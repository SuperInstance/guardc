//! An un-discharged VC must not report a solver verdict.
//!
//! `guardc` emitted `VcStatus::Sat` on every generated VC. `sat` means the
//! constraint is SATISFIABLE -- a counterexample exists, i.e. the property
//! FAILED -- which is the opposite of what a safety proof wants. A consumer
//! reading `sat` would conclude the opposite of the truth.
//!
//! These tests deliberately avoid naming the obligations. They walk whatever
//! the generator produced, so adding, removing or renaming an invariant cannot
//! quietly turn this suite into a no-op.

use guardc::cir::{
    BinOp, CirDerived, CirInvariant, CirModule, CirType, ConstValue, Expr, Priority, ProofConfig,
    ViolationAction,
};
use guardc::error::Span;
use guardc::proof::{ProofGen, VcStatus};

fn spn(line: u32) -> Span {
    Span {
        file: "t.guard".to_string(),
        start_line: line,
        start_col: 0,
        end_line: line + 1,
        end_col: 9,
    }
}

fn bt() -> CirType {
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
            ty: bt(),
        },
        on_violation: ViolationAction::Halt,
        source_span: spn(line),
    }
}

fn module(invariants: Vec<CirInvariant>) -> CirModule {
    CirModule {
        name: "Throttle".to_string(),
        version: "1.0.0".to_string(),
        sample_period_ms: 10.0,
        symbol_table: Default::default(),
        derived: vec![CirDerived {
            name: "PositiveImpliesEnabled".to_string(),
            premises: vec![],
            when: None,
            conclude: Expr::Binary {
                op: BinOp::Implies,
                left: Box::new(Expr::Var(guardc::cir::VarId(0))),
                right: Box::new(Expr::Const(ConstValue::Bool(true))),
                ty: bt(),
            },
            source_span: spn(24),
        }],
        invariants,
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

fn obligations() -> Vec<guardc::proof::Obligation> {
    let m = module(vec![
        inv("ThrottleMustNotExceedMax", 13, BinOp::Lte, 1.0),
        inv("ThrottleMustNotReverse", 18, BinOp::Gte, 0.0),
    ]);
    let cert = ProofGen::new(&m, "module Throttle {}", b"\x00bc")
        .generate()
        .expect("certificate generation succeeds");
    let obs: Vec<_> = cert
        .proofs
        .iter()
        .flat_map(|p| p.obligations.clone())
        .collect();
    assert!(
        !obs.is_empty(),
        "fixture produced no obligations, so these tests would vacuously pass"
    );
    obs
}

#[test]
fn every_generated_vc_is_unknown() {
    for o in obligations() {
        assert_eq!(
            o.vc.status,
            VcStatus::Unknown,
            "{} carries a solver verdict, but no solver ran",
            o.name
        );
    }
}

#[test]
fn no_generated_vc_claims_sat() {
    for o in obligations() {
        assert_ne!(
            o.vc.status,
            VcStatus::Sat,
            "{} says `sat`, i.e. satisfiable, i.e. a counterexample exists",
            o.name
        );
    }
}

#[test]
fn no_generated_vc_claims_unsat() {
    // `unsat` is the one variant that would legitimately mean "proven", so it
    // must not appear either -- asserting it keeps this test honest if the
    // placeholder is ever swapped from `sat` to `unsat` by mistake.
    for o in obligations() {
        assert_ne!(
            o.vc.status,
            VcStatus::Unsat,
            "{} claims the property was proven",
            o.name
        );
    }
}

#[test]
fn serialized_certificate_says_unknown() {
    let m = module(vec![inv("ThrottleMustNotExceedMax", 13, BinOp::Lte, 1.0)]);
    let json = serde_json::to_string(&ProofGen::new(&m, "s", b"b").generate().unwrap()).unwrap();

    assert!(
        json.contains("\"status\":\"unknown\""),
        "serialized certificate never says unknown: {}",
        json
    );
    assert!(
        !json.contains("\"status\":\"sat\""),
        "serialized certificate still claims sat: {}",
        json
    );
    assert!(
        !json.contains("\"status\":\"unsat\""),
        "serialized certificate claims unsat: {}",
        json
    );
}

#[test]
fn a_module_with_no_obligations_does_not_panic() {
    // A module with nothing to check should still produce a certificate; it
    // just has no VCs to misreport.
    let m = module(vec![]);
    let cert = ProofGen::new(&m, "s", b"b").generate().unwrap();
    let total: usize = cert.proofs.iter().map(|p| p.obligations.len()).sum();
    assert_eq!(total, 1, "only the derived rule remains");
    assert!(cert.proofs.iter().all(|p| p
        .obligations
        .iter()
        .all(|o| o.vc.status == VcStatus::Unknown)));
}
