//! The certificate's seal must bind the obligation it describes, and the
//! certificate must not claim a verification that never happened.
//!
//! Regression cover for the state where `trace_digest` was the digest of the
//! literal bytes `placeholder` -- a constant -- so every obligation in every
//! certificate ever emitted hashed to the same value, and `proofs[].status`
//! was `ProofStatus::Verified` on a compiler that runs no solver and never runs
//! the FLUX VM.

use guardc::cir::{
    BinOp, CirDerived, CirInvariant, CirModule, CirType, ConstValue, Expr, Priority, ProofConfig,
    ViolationAction,
};
use guardc::error::Span;
use guardc::proof::{obligation_digest, ProofGen, ProofStatus};

/// SHA-256 of the literal bytes `placeholder` -- the value the seal carried for
/// every obligation before the fix.
const PLACEHOLDER_DIGEST: &str = "4097889236a2af26c293033feb964c4cf118c0224e0d063fec0a89e9d0569ef2";

fn span(line: u32) -> Span {
    Span {
        file: "t.guard".to_string(),
        start_line: line,
        start_col: 0,
        end_line: line + 1,
        end_col: 9,
    }
}

fn bool_ty() -> CirType {
    CirType {
        kind: guardc::cir::TypeKind::Boolean,
        unit: guardc::cir::Unit::Dimensionless,
    }
}

fn inv(name: &str, line: u32, op: BinOp, bound: f64) -> CirInvariant {
    CirInvariant {
        name: name.to_string(),
        priority: Priority::Critical,
        when: None,
        ensure: Expr::Binary {
            op,
            left: Box::new(Expr::Var(guardc::cir::VarId(0))),
            right: Box::new(Expr::Const(ConstValue::Real(bound))),
            ty: bool_ty(),
        },
        on_violation: ViolationAction::Halt,
        source_span: span(line),
    }
}

fn derived(name: &str, line: u32) -> CirDerived {
    CirDerived {
        name: name.to_string(),
        premises: vec![],
        when: None,
        conclude: Expr::Binary {
            op: BinOp::Implies,
            left: Box::new(Expr::Const(ConstValue::Integer(1))),
            right: Box::new(Expr::Const(ConstValue::Bool(true))),
            ty: bool_ty(),
        },
        source_span: span(line),
    }
}

/// A module with three obligations that genuinely differ from one another:
/// two invariants with different bounds and different source spans, and one
/// derived rule of a different kind.
fn module_with_three_obligations() -> CirModule {
    CirModule {
        name: "Throttle".to_string(),
        version: "1.0.0".to_string(),
        sample_period_ms: 10.0,
        symbol_table: Default::default(),
        invariants: vec![
            inv("ThrottleMustNotExceedMax", 13, BinOp::Lte, 1.0),
            inv("ThrottleMustNotReverse", 18, BinOp::Gte, 0.0),
        ],
        derived: vec![derived("PositiveImpliesEnabled", 24)],
        proof_config: vec![ProofConfig {
            name: "ThrottleSafetyProof".to_string(),
            tactics: vec!["interval_arithmetic".to_string()],
            cert_format: guardc::cir::CertFormat::Native,
            include_trace: false,
            include_counterexample: false,
            hash_algo: guardc::cir::HashAlgo::Sha256,
        }],
    }
}

fn generate(module: &CirModule) -> guardc::proof::ProofCertificate {
    ProofGen::new(module, "module Throttle {}", b"\x00bytecode")
        .generate()
        .expect("certificate generation succeeds")
}

#[test]
fn seal_differs_between_different_obligations() {
    let cert = generate(&module_with_three_obligations());
    let obligations = &cert.proofs[0].obligations;
    assert_eq!(
        obligations.len(),
        3,
        "fixture should produce three distinct obligations"
    );

    // The point of the fix: a seal over a constant produces the same value for
    // every input. These three obligations differ in kind, name, span and
    // formula, so their seals must differ.
    for (i, a) in obligations.iter().enumerate() {
        for b in obligations.iter().skip(i + 1) {
            assert_ne!(
                a.trace_digest, b.trace_digest,
                "{} and {} are different obligations but sealed identically",
                a.name, b.name
            );
        }
    }
}

#[test]
fn seal_is_not_the_digest_of_a_constant() {
    let cert = generate(&module_with_three_obligations());
    for o in &cert.proofs[0].obligations {
        assert_ne!(
            o.trace_digest, PLACEHOLDER_DIGEST,
            "{} was sealed with the constant placeholder digest",
            o.name
        );
        assert!(
            o.trace_digest.starts_with("obligation:"),
            "{} digest must be tagged `obligation:` so it cannot be mistaken \
             for a trace digest, got {}",
            o.name,
            o.trace_digest
        );
    }
}

#[test]
fn seal_changes_when_any_bound_field_changes() {
    let base = inv("ThrottleMustNotExceedMax", 13, BinOp::Lte, 1.0);

    let mut wider = base.clone();
    wider.ensure = Expr::Binary {
        op: BinOp::Lte,
        left: Box::new(Expr::Var(guardc::cir::VarId(0))),
        right: Box::new(Expr::Const(ConstValue::Real(2.0))),
        ty: bool_ty(),
    };

    let mut moved = base.clone();
    moved.source_span = span(99);

    let mut renamed = base.clone();
    renamed.name = "SomethingElseEntirely".to_string();

    let digests = [base, wider, moved, renamed]
        .iter()
        .map(|i| {
            let cert = generate(&module_with_three_obligations_with(std::slice::from_ref(i)));
            cert.proofs[0].obligations[0].trace_digest.clone()
        })
        .collect::<Vec<_>>();

    for (i, a) in digests.iter().enumerate() {
        for b in digests.iter().skip(i + 1) {
            assert_ne!(a, b, "changing a bound field must change the seal");
        }
    }
}

fn module_with_three_obligations_with(invariants: &[CirInvariant]) -> CirModule {
    CirModule {
        name: "Throttle".to_string(),
        version: "1.0.0".to_string(),
        sample_period_ms: 10.0,
        symbol_table: Default::default(),
        invariants: invariants.to_vec(),
        derived: vec![],
        proof_config: vec![ProofConfig {
            name: "ThrottleSafetyProof".to_string(),
            tactics: vec!["interval_arithmetic".to_string()],
            cert_format: guardc::cir::CertFormat::Native,
            include_trace: false,
            include_counterexample: false,
            hash_algo: guardc::cir::HashAlgo::Sha256,
        }],
    }
}

#[test]
fn length_prefix_stops_field_split_collisions() {
    // Without length prefixes, ("ab", "c") and ("a", "bc") concatenate to the
    // same bytes and so would seal identically. The prefixes are what keep
    // those two apart.
    let a = obligation_digest(
        "ob-1",
        &guardc::proof::ObligationKind::InvariantPreservation,
        "ab",
        "c",
        "QF_LRA",
        "(<= v0 1.000000)",
    );
    let b = obligation_digest(
        "ob-1",
        &guardc::proof::ObligationKind::InvariantPreservation,
        "a",
        "bc",
        "QF_LRA",
        "(<= v0 1.000000)",
    );
    assert_ne!(a, b, "length prefixes must prevent a field-split collision");

    // And the naive concatenation the prefixes replace really would collide.
    assert_eq!(
        format!("ab{}", "c"),
        format!("a{}", "bc"),
        "fixture no longer demonstrates the collision it is guarding against"
    );
}

#[test]
fn kind_tag_matches_the_serialized_kind() {
    // An independent verifier re-derives the digest from the JSON. If the tag
    // used here ever drifts from the name serde emits, every previously issued
    // certificate stops re-deriving and nobody would notice.
    let cases = [
        (
            guardc::proof::ObligationKind::InvariantPreservation,
            "invariant_preservation",
        ),
        (
            guardc::proof::ObligationKind::InvariantInitiation,
            "invariant_initiation",
        ),
        (
            guardc::proof::ObligationKind::DerivedRuleSanity,
            "derived_rule_sanity",
        ),
        (
            guardc::proof::ObligationKind::TemporalLiveness,
            "temporal_liveness",
        ),
        (
            guardc::proof::ObligationKind::TemporalSafety,
            "temporal_safety",
        ),
        (
            guardc::proof::ObligationKind::UnitConsistency,
            "unit_consistency",
        ),
        (
            guardc::proof::ObligationKind::DomainMembership,
            "domain_membership",
        ),
    ];
    for (kind, expected) in cases {
        assert_eq!(
            serde_json::to_string(&kind).unwrap(),
            format!("\"{}\"", expected),
            "kind tag drifted from the serialized form"
        );
    }
}

#[test]
fn block_status_does_not_claim_verified() {
    let cert = generate(&module_with_three_obligations());
    let block = &cert.proofs[0];
    assert_eq!(
        block.status,
        ProofStatus::NotSealed,
        "no solver ran and no VM executed, so nothing is verified"
    );

    let json = serde_json::to_string(&cert).unwrap();
    assert!(
        json.contains("\"status\":\"not_sealed\""),
        "serialized certificate must say not_sealed, got: {}",
        json
    );
    assert!(
        !json.contains("\"status\":\"verified\""),
        "serialized certificate must not claim verified, got: {}",
        json
    );
}

#[test]
fn identical_input_still_seals_identically() {
    // The seal must still be a function of the obligation: certificate
    // determinism is a documented property and this guards against "fixing"
    // the collision by hashing something that varies per run.
    let module = module_with_three_obligations();
    let first = generate(&module);
    let second = generate(&module);
    assert_eq!(first.proofs[0].obligations, second.proofs[0].obligations);
}
