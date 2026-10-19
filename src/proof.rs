//! Proof certificate generation.
//!
//! Emits `.guardcert` JSON artifacts containing:
//!   - Source and bytecode hashes (tamper detection)
//!   - Per-obligation verification conditions in SMT-LIB format
//!   - Solver results, counterexamples, and a Merkle root

use crate::cir::{CirModule, ConstValue, Expr};
use crate::error::{GuardError, Result};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::HashMap;

// ---------------------------------------------------------------------------
// Certificate Types
// ---------------------------------------------------------------------------

/// Top-level certificate structure.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct ProofCertificate {
    pub certificate_format: String,
    pub module: String,
    pub version: String,
    pub compiler: CompilerInfo,
    pub source_hash: String,
    pub bytecode_hash: String,
    pub proofs: Vec<ProofBlock>,
    pub metadata: CertMetadata,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct CompilerInfo {
    pub name: String,
    pub version: String,
    pub target: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct ProofBlock {
    pub proof_id: String,
    pub tactics: Vec<String>,
    pub status: ProofStatus,
    pub verification_time_ms: u64,
    pub obligations: Vec<Obligation>,
    pub merkle_root: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub enum ProofStatus {
    Verified,
    Bounded,
    Runtime,
    Failed,
    /// The obligations were GENERATED but not sealed: the compiler does not
    /// run the solver, so there is no execution trace to hash and nothing was
    /// proved. A certificate that says `verified` here is a claim the code
    /// cannot support.
    ///
    /// **The absence of a backend is a REFUSAL, not a pass.**
    NotSealed,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Obligation {
    pub obligation_id: String,
    pub kind: ObligationKind,
    pub name: String,
    pub source_span: String,
    pub vc: VerificationCondition,
    pub trace_digest: String,
    pub counterexample: Option<Counterexample>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub enum ObligationKind {
    InvariantPreservation,
    InvariantInitiation,
    DerivedRuleSanity,
    TemporalLiveness,
    TemporalSafety,
    UnitConsistency,
    DomainMembership,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct VerificationCondition {
    pub logic: String,
    pub formula: String,
    pub status: VcStatus,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub enum VcStatus {
    Sat,
    Unsat,
    Unknown,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Counterexample {
    pub model: HashMap<String, serde_json::Value>,
    pub time_step: usize,
    pub violated_invariant: String,
    pub explanation: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct CertMetadata {
    pub generated_at: String,
    pub host_os: String,
    #[serde(rename = " deterministic")]
    pub deterministic: bool,
}

// ---------------------------------------------------------------------------
// Generator
// ---------------------------------------------------------------------------

pub struct ProofGen<'a> {
    module: &'a CirModule,
    source_text: &'a str,
    bytecode_bytes: &'a [u8],
}

impl<'a> ProofGen<'a> {
    pub fn new(module: &'a CirModule, source_text: &'a str, bytecode_bytes: &'a [u8]) -> Self {
        Self {
            module,
            source_text,
            bytecode_bytes,
        }
    }

    pub fn generate(&self) -> Result<ProofCertificate> {
        let source_hash = sha256_hex(self.source_text.as_bytes());
        let bytecode_hash = sha256_hex(self.bytecode_bytes);

        let mut proofs = vec![];
        for proof_cfg in &self.module.proof_config {
            let obligations = self.generate_obligations()?;
            let merkle_root = compute_merkle_root(&obligations);
            proofs.push(ProofBlock {
                proof_id: proof_cfg.name.clone(),
                tactics: proof_cfg.tactics.clone(),
                // The solver is not run, so nothing was proved. Saying
                // `Verified` here was a claim the code could not support.
                status: ProofStatus::NotSealed,
                verification_time_ms: 0,
                obligations,
                merkle_root,
            });
        }

        Ok(ProofCertificate {
            certificate_format: "guard-native-v1".to_string(),
            module: self.module.name.clone(),
            version: self.module.version.clone(),
            compiler: CompilerInfo {
                name: "guardc".to_string(),
                version: env!("CARGO_PKG_VERSION").to_string(),
                target: "flux-isa-43".to_string(),
            },
            source_hash: format!("sha256:{}", source_hash),
            bytecode_hash: format!("sha256:{}", bytecode_hash),
            proofs,
            metadata: CertMetadata {
                generated_at: format_iso_now(),
                host_os: format!("{}-{}", std::env::consts::OS, std::env::consts::ARCH),
                deterministic: true,
            },
        })
    }

    fn generate_obligations(&self) -> Result<Vec<Obligation>> {
        let mut obligations = vec![];
        let mut id = 0u32;

        for inv in &self.module.invariants {
            id += 1;
            let formula = expr_to_smt(&inv.ensure, &self.module.symbol_table)?;
            let obligation_id = format!("inv-{id:02}");
            let name = inv.name.clone();
            let source_span = format!("{}", inv.source_span);
            let vc = VerificationCondition {
                logic: select_logic(&inv.ensure),
                formula,
                // The solver is not run, so the VC's satisfiability is
                // UNKNOWN, not Sat. `Sat` is the opposite of what a safety
                // proof wants.
                status: VcStatus::Unknown,
            };
            // The seal is computed FROM this obligation and then carried on
            // it, so the two cannot drift apart.
            let mut obligation = Obligation {
                obligation_id,
                kind: ObligationKind::InvariantPreservation,
                name,
                source_span,
                vc,
                trace_digest: String::new(),
                counterexample: None,
            };
            obligation.trace_digest = obligation_digest(&obligation);
            obligations.push(obligation);
        }

        for der in &self.module.derived {
            id += 1;
            let formula = expr_to_smt(&der.conclude, &self.module.symbol_table)?;
            let obligation_id = format!("der-{id:02}");
            let name = der.name.clone();
            let source_span = format!("{}", der.source_span);
            let vc = VerificationCondition {
                logic: select_logic(&der.conclude),
                formula,
                status: VcStatus::Unknown,
            };
            let mut obligation = Obligation {
                obligation_id,
                kind: ObligationKind::DerivedRuleSanity,
                name,
                source_span,
                vc,
                trace_digest: String::new(),
                counterexample: None,
            };
            obligation.trace_digest = obligation_digest(&obligation);
            obligations.push(obligation);
        }

        Ok(obligations)
    }
}

// ---------------------------------------------------------------------------
// SMT-LIB emission
// ---------------------------------------------------------------------------

fn select_logic(expr: &Expr) -> String {
    // Simple heuristic based on expression structure.
    if has_reals(expr) {
        "QF_LRA".to_string() // Quantifier-Free Linear Real Arithmetic
    } else if has_integers(expr) {
        "QF_LIA".to_string()
    } else {
        "QF_BV".to_string() // Bit-vectors as fallback
    }
}

fn has_reals(expr: &Expr) -> bool {
    match expr {
        Expr::Const(ConstValue::Real(_)) => true,
        Expr::Unary { operand, .. } => has_reals(operand),
        Expr::Binary { left, right, .. } => has_reals(left) || has_reals(right),
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => has_reals(cond) || has_reals(then_branch) || has_reals(else_branch),
        Expr::Forall { body, .. } | Expr::Exists { body, .. } => has_reals(body),
        _ => false,
    }
}

fn has_integers(expr: &Expr) -> bool {
    match expr {
        Expr::Const(ConstValue::Integer(_)) => true,
        Expr::Unary { operand, .. } => has_integers(operand),
        Expr::Binary { left, right, .. } => has_integers(left) || has_integers(right),
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => has_integers(cond) || has_integers(then_branch) || has_integers(else_branch),
        Expr::Forall { body, .. } | Expr::Exists { body, .. } => has_integers(body),
        _ => false,
    }
}

fn expr_to_smt(expr: &Expr, _symtab: &crate::cir::SymbolTable) -> Result<String> {
    fn go(expr: &Expr, out: &mut String) -> Result<()> {
        match expr {
            Expr::Const(c) => match c {
                ConstValue::Real(v) => out.push_str(&format!("{:.6}", v)),
                ConstValue::Integer(v) => out.push_str(&v.to_string()),
                ConstValue::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            },
            Expr::Var(v) => out.push_str(&format!("v{}", v.0)),
            Expr::Unary { op, operand, .. } => {
                let sop = match op {
                    crate::cir::UnOp::Neg => "-",
                    crate::cir::UnOp::Abs => "abs",
                    crate::cir::UnOp::Not => "not",
                };
                out.push_str(&format!("({} ", sop));
                go(operand, out)?;
                out.push(')');
            }
            Expr::Binary {
                op, left, right, ..
            } => {
                let sop = match op {
                    crate::cir::BinOp::Add => "+",
                    crate::cir::BinOp::Sub => "-",
                    crate::cir::BinOp::Mul => "*",
                    crate::cir::BinOp::Div => "/",
                    crate::cir::BinOp::Mod => "mod",
                    crate::cir::BinOp::Eq => "=",
                    crate::cir::BinOp::Neq => "distinct",
                    crate::cir::BinOp::Lt => "<",
                    crate::cir::BinOp::Gt => ">",
                    crate::cir::BinOp::Lte => "<=",
                    crate::cir::BinOp::Gte => ">=",
                    crate::cir::BinOp::And => "and",
                    crate::cir::BinOp::Or => "or",
                    crate::cir::BinOp::Implies => "=>",
                };
                out.push_str(&format!("({} ", sop));
                go(left, out)?;
                out.push(' ');
                go(right, out)?;
                out.push(')');
            }
            Expr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                out.push_str("(ite ");
                go(cond, out)?;
                out.push(' ');
                go(then_branch, out)?;
                out.push(' ');
                go(else_branch, out)?;
                out.push(')');
            }
            Expr::Forall { var, body, .. } => {
                out.push_str(&format!("(forall ((v{} Int)) ", var.0));
                go(body, out)?;
                out.push(')');
            }
            Expr::Exists { var, body, .. } => {
                out.push_str(&format!("(exists ((v{} Int)) ", var.0));
                go(body, out)?;
                out.push(')');
            }
            _ => {
                return Err(GuardError::ProofFailed {
                    obligation: "smt".into(),
                    reason: format!("unsupported expr variant for SMT: {:?}", expr),
                })
            }
        }
        Ok(())
    }

    let mut s = String::new();
    go(expr, &mut s)?;
    Ok(s)
}

// ---------------------------------------------------------------------------
// Merkle Tree
// ---------------------------------------------------------------------------

/// The digest an obligation carries.
///
/// **IT BINDS THE OBLIGATION.** The previous implementation hashed the
/// literal bytes `placeholder` for EVERY obligation, so two different
/// obligations sealed identically, the merkle root over them was a
/// constant, and the seal certified nothing at all.
///
/// The parts are LENGTH-PREFIXED, so a field boundary cannot be moved:
/// ("ab", "c") and ("a", "bc") must not produce the same preimage.
///
/// **WHAT IT DOES NOT BIND: the execution trace.** The compiler does not run
/// the solver, so there IS no trace to hash -- and a digest that claimed to
/// cover one would be a claim rather than a measurement. That is what
/// `ProofStatus::NotSealed` says.
fn obligation_digest(o: &Obligation) -> String {
    // A STABLE rendering of the kind, not a Debug one: `{:?}` would change
    // with the shape of the enum and silently re-seal every obligation.
    let kind = serde_json::to_string(&o.kind).unwrap_or_default();
    let mut hasher = Sha256::new();
    for part in [
        o.obligation_id.as_str(),
        kind.as_str(),
        o.name.as_str(),
        o.source_span.as_str(),
        o.vc.logic.as_str(),
        o.vc.formula.as_str(),
    ] {
        hasher.update((part.len() as u64).to_le_bytes());
        hasher.update(part.as_bytes());
    }
    bytes_to_hex(&hasher.finalize())
}

fn compute_merkle_root(obligations: &[Obligation]) -> String {
    let leaves: Vec<Vec<u8>> = obligations
        .iter()
        .map(|o| {
            let mut hasher = Sha256::new();
            hasher.update(o.obligation_id.as_bytes());
            // RECOMPUTE the digest from the obligation; do NOT trust the
            // stored field. The stored `trace_digest` is a RECEIPT of what
            // was sealed -- the root has to be bound to the OBLIGATION.
            // Trusting the field means a stale or empty digest yields a
            // root that ignores the obligation's content entirely, which
            // is exactly what the `placeholder` digest did.
            hasher.update(obligation_digest(o).as_bytes());
            hasher.finalize().to_vec()
        })
        .collect();

    if leaves.is_empty() {
        return format!("sha256:{}", sha256_hex(b""));
    }

    let mut current = leaves;
    while current.len() > 1 {
        let mut next = vec![];
        for pair in current.chunks(2) {
            let mut hasher = Sha256::new();
            hasher.update(&pair[0]);
            hasher.update(pair.get(1).unwrap_or(&pair[0]));
            next.push(hasher.finalize().to_vec());
        }
        current = next;
    }

    format!("sha256:{}", bytes_to_hex(&current[0]))
}

fn sha256_hex(data: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(data);
    bytes_to_hex(&hasher.finalize())
}

fn bytes_to_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

fn format_iso_now() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs();
    // Simple RFC 3339-ish format
    let days = now / 86400;
    let rem = now % 86400;
    let hours = rem / 3600;
    let mins = (rem % 3600) / 60;
    let secs = rem % 60;
    format!(
        "1970-01-{:02}T{:02}:{:02}:{:02}Z",
        days + 1,
        hours,
        mins,
        secs
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn obligation(id: &str, name: &str, span: &str) -> Obligation {
        Obligation {
            obligation_id: id.to_string(),
            kind: ObligationKind::InvariantPreservation,
            name: name.to_string(),
            source_span: span.to_string(),
            vc: VerificationCondition {
                logic: "QF_LIA".to_string(),
                formula: "(> (+ (abs_height) 0) (+ (abs_height) 0))".to_string(),
                status: VcStatus::Unknown,
            },
            trace_digest: String::new(),
            counterexample: None,
        }
    }

    /// **THE SEAL MUST BIND THE OBLIGATION.** The previous implementation
    /// returned `sha256_hex(b"placeholder")` for every obligation, so this
    /// property was FALSE: two different obligations sealed identically, and
    /// the merkle root over them was a constant.
    #[test]
    fn two_different_obligations_seal_differently() {
        let a = obligation("inv-01", "abs_height_nonneg", "sheets/a.yaml:1:1");
        let b = obligation("inv-02", "abs_height_nonneg", "sheets/a.yaml:2:1");
        assert_ne!(
            obligation_digest(&a),
            obligation_digest(&b),
            "two different obligations produced the same seal -- the seal binds nothing"
        );
    }

    #[test]
    fn the_same_obligation_seals_the_same() {
        let a = obligation("inv-01", "abs_height_nonneg", "sheets/a.yaml:1:1");
        let b = obligation("inv-01", "abs_height_nonneg", "sheets/a.yaml:1:1");
        assert_eq!(
            obligation_digest(&a),
            obligation_digest(&b),
            "the seal is not deterministic"
        );
    }

    /// **THE LENGTH PREFIX MATTERS.** Without it, ("ab", "c") and ("a", "bc")
    /// produce the same preimage, and a field boundary can be moved.
    #[test]
    fn a_field_boundary_cannot_be_moved() {
        let a = obligation("ab", "c", "x");
        let b = obligation("a", "bc", "x");
        assert_ne!(
            obligation_digest(&a),
            obligation_digest(&b),
            "a field boundary was not encoded"
        );
    }

    /// THE ROOT FOLLOWS THE OBLIGATION, NOT THE STORED DIGEST. The stored
    /// `trace_digest` is a RECEIPT of what was sealed; the root must be
    /// bound to the content. A stale or empty digest must not change it.
    #[test]
    fn the_root_follows_the_obligation_not_the_stored_digest() {
        let mut o = obligation("inv-01", "a", "s1");
        o.trace_digest = "deadbeef".to_string();
        let a = compute_merkle_root(&[o.clone()]);
        o.trace_digest = String::new();
        let b = compute_merkle_root(&[o]);
        assert_eq!(
            a, b,
            "the merkle root trusted the stored digest instead of the obligation"
        );
    }

    /// EVERY FIELD IS BOUND. Change one and the seal changes.
    #[test]
    fn every_part_of_the_obligation_is_bound() {
        let base = obligation("inv-01", "n", "s");
        let mut other = base.clone();
        other.name = "n2".to_string();
        assert_ne!(obligation_digest(&base), obligation_digest(&other));
        let mut other = base.clone();
        other.source_span = "t".to_string();
        assert_ne!(obligation_digest(&base), obligation_digest(&other));
        let mut other = base.clone();
        other.vc.formula = "different".to_string();
        assert_ne!(obligation_digest(&base), obligation_digest(&other));
        let mut other = base.clone();
        other.vc.logic = "QF_NIA".to_string();
        assert_ne!(obligation_digest(&base), obligation_digest(&other));
        let mut other = base.clone();
        other.kind = ObligationKind::DerivedRuleSanity;
        assert_ne!(obligation_digest(&base), obligation_digest(&other));
    }

    /// THE MERKLE ROOT OVER THE OBLIGATIONS IS NOT A CONSTANT.
    #[test]
    fn the_merkle_root_over_distinct_obligations_is_not_constant() {
        let obs = vec![
            obligation("inv-01", "a", "s1"),
            obligation("inv-02", "b", "s2"),
        ];
        let one = compute_merkle_root(&obs);
        let two = compute_merkle_root(&[
            obligation("inv-01", "a", "s1"),
            obligation("inv-02", "B", "s2"),
        ]);
        assert_ne!(one, two, "the merkle root ignored its leaves");
    }
}
