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
    /// Nothing was verified, because nothing ran.
    ///
    /// `guardc` compiles GUARD to FLUX bytecode. It runs no SMT solver and it
    /// never runs the FLUX VM, so there is no execution trace to seal against
    /// and no VC to discharge. This is the only status any block can honestly
    /// carry today, so it is what `generate` emits.
    NotSealed,
    Verified,
    Bounded,
    Runtime,
    Failed,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Obligation {
    pub obligation_id: String,
    pub kind: ObligationKind,
    pub name: String,
    pub source_span: String,
    pub vc: VerificationCondition,
    /// Named `trace_digest` for historical reasons. It is **not** a trace
    /// digest: `guardc` compiles and does not execute, so there is no trace.
    /// It carries `obligation:<sha256>` over this obligation -- see
    /// [`obligation_digest`].
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

impl ObligationKind {
    /// The stable tag hashed into the obligation digest.
    ///
    /// This must stay byte-identical to the name serde emits, because an
    /// independent verifier re-derives the digest from the certificate's JSON.
    /// The match is exhaustive on purpose: adding a variant has to be a
    /// deliberate decision about its tag rather than a silent default, and the
    /// `kind_tag_matches_the_serialized_kind` test checks the two agree.
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::InvariantPreservation => "invariant_preservation",
            Self::InvariantInitiation => "invariant_initiation",
            Self::DerivedRuleSanity => "derived_rule_sanity",
            Self::TemporalLiveness => "temporal_liveness",
            Self::TemporalSafety => "temporal_safety",
            Self::UnitConsistency => "unit_consistency",
            Self::DomainMembership => "domain_membership",
        }
    }
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
                // No solver ran and no VM executed, so nothing was verified and
                // there is no trace to seal against. `Verified` would be a lie
                // the moment it was serialized.
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
            let obligation_id = format!("inv-{id:02}");
            let kind = ObligationKind::InvariantPreservation;
            let name = inv.name.clone();
            let source_span = format!("{}", inv.source_span);
            let logic = select_logic(&inv.ensure);
            let formula = expr_to_smt(&inv.ensure, &self.module.symbol_table)?;
            let trace_digest =
                obligation_digest(&obligation_id, &kind, &name, &source_span, &logic, &formula);
            obligations.push(Obligation {
                obligation_id,
                kind,
                name,
                source_span,
                vc: VerificationCondition {
                    logic,
                    formula,
                    status: VcStatus::Sat, // Placeholder
                },
                trace_digest,
                counterexample: None,
            });
        }

        for der in &self.module.derived {
            id += 1;
            let obligation_id = format!("der-{id:02}");
            let kind = ObligationKind::DerivedRuleSanity;
            let name = der.name.clone();
            let source_span = format!("{}", der.source_span);
            let logic = select_logic(&der.conclude);
            let formula = expr_to_smt(&der.conclude, &self.module.symbol_table)?;
            let trace_digest =
                obligation_digest(&obligation_id, &kind, &name, &source_span, &logic, &formula);
            obligations.push(Obligation {
                obligation_id,
                kind,
                name,
                source_span,
                vc: VerificationCondition {
                    logic,
                    formula,
                    status: VcStatus::Sat,
                },
                trace_digest,
                counterexample: None,
            });
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

fn compute_merkle_root(obligations: &[Obligation]) -> String {
    let leaves: Vec<Vec<u8>> = obligations
        .iter()
        .map(|o| {
            let mut hasher = Sha256::new();
            hasher.update(o.obligation_id.as_bytes());
            hasher.update(o.trace_digest.as_bytes());
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

/// The digest an obligation is sealed with: `obligation:<sha256>` over the
/// fields this VC was actually built from.
///
/// This binds the obligation, so two different obligations seal differently.
/// It used to be `sha256_hex(b"placeholder")` -- a constant -- so every
/// obligation in every certificate ever emitted carried the same value.
///
/// Each field is written length-prefixed (8-byte big-endian length, then the
/// bytes). The prefixes are load-bearing: without them `("ab", "c")` and
/// `("a", "bc")` concatenate to identical bytes, so two genuinely different
/// field splits would still seal identically.
///
/// The `obligation:` prefix is deliberate. `guardc` compiles and does not
/// execute, so there is no trace to digest; the tag stops a reader mistaking
/// this for a trace digest. The field name is historical.
///
/// This is public because it is the certificate's re-derivable commitment: a
/// verifier that does not trust `guardc` has to be able to recompute it.
pub fn obligation_digest(
    obligation_id: &str,
    kind: &ObligationKind,
    name: &str,
    source_span: &str,
    logic: &str,
    formula: &str,
) -> String {
    let mut hasher = Sha256::new();
    for field in [
        obligation_id,
        kind.as_str(),
        name,
        source_span,
        logic,
        formula,
    ] {
        hasher.update((field.len() as u64).to_be_bytes());
        hasher.update(field.as_bytes());
    }
    format!("obligation:{}", bytes_to_hex(&hasher.finalize()))
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
