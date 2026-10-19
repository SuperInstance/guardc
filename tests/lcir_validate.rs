//! `LcirProgram::validate` — CFG target bounds checks.
//!
//! Every terminator that names a block must name a block that exists.
//! `validate` is the only guard for a hand-built `LcirProgram`: `codegen`
//! resolves targets through a side table and only notices the problem later,
//! and with a different error.
//!
//! NOTE ON THE CORPUS: the lowerer cannot lower a bare `Expr::Var` —
//! `lower_expr_to_var` calls `expr.ty()` on entry and `Expr::ty()` panics for
//! `Expr::Var` (`src/cir.rs`, "Var type must be looked up in symbol table").
//! That is a pre-existing lowerer limitation, out of scope here, so the corpus
//! below is built from constants. That still reaches every `Terminator::Branch`
//! the lowerer mints: both branch sites (`when` guard, `Expr::If`) are covered.

use guardc::cir::{
    self, BinOp, CirInvariant, CirModule, CirType, ConstValue, Domain, Expr, Priority, SymbolTable,
    TypeKind, Unit, VarId, VarKind, ViolationAction,
};
use guardc::error::Span;
use guardc::lcir::{BlockId, LcirBuilder, LcirProgram, Terminator};
use guardc::lower::lower_module;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn span() -> Span {
    Span::new("<test>", 0, 0)
}

fn real_ty() -> CirType {
    CirType {
        kind: TypeKind::Real,
        unit: Unit::Dimensionless,
    }
}

fn bool_ty() -> CirType {
    CirType {
        kind: TypeKind::Boolean,
        unit: Unit::Dimensionless,
    }
}

fn cmp(op: BinOp, left: Expr, right: Expr) -> Expr {
    Expr::Binary {
        op,
        left: Box::new(left),
        right: Box::new(right),
        ty: bool_ty(),
    }
}

fn one() -> Expr {
    Expr::Const(ConstValue::Real(1.0))
}

fn two() -> Expr {
    Expr::Const(ConstValue::Real(2.0))
}

fn truth() -> Expr {
    Expr::Const(ConstValue::Bool(true))
}

/// A three-block program (`entry`, `a`, `c`) whose block 1 branches on
/// `then_target`/`else_target` as given. Built through the real `LcirBuilder`,
/// so only the terminator is under the test's control.
fn branching_program(then_target: BlockId, else_target: BlockId) -> LcirProgram {
    let mut b = LcirBuilder::new("branch_probe", "0.1.0");
    let a = b.fresh_block("a");
    b.fresh_block("c");
    b.switch_block(a);
    b.set_terminator(Terminator::Branch {
        cond: VarId(1),
        then_target,
        else_target,
    });
    b.build()
}

/// A three-block program whose block 1 jumps to `target`.
fn jumping_program(target: BlockId) -> LcirProgram {
    let mut b = LcirBuilder::new("jump_probe", "0.1.0");
    let a = b.fresh_block("a");
    b.fresh_block("c");
    b.switch_block(a);
    b.set_terminator(Terminator::Jump(target));
    b.build()
}

// ---------------------------------------------------------------------------
// The defect: `else_target` is not bounds-checked.
// ---------------------------------------------------------------------------

/// THE REPRODUCTION.
///
/// `branching_program` has `blocks.len() == 3`, so valid targets are
/// `BlockId(0..=2)`. `then_target` is in range; `else_target` is
/// `BlockId(9999)`, far out. `validate` must reject it.
///
/// Before the fix this assertion fails: the `then_target` arm matches every
/// `Branch` value, so the `else_target` check never runs and `validate`
/// returns `Ok(())` for a program whose else-edge points nowhere.
#[test]
fn validate_rejects_out_of_range_else_target() {
    let prog = branching_program(BlockId(2), BlockId(9999));
    assert_eq!(prog.blocks.len(), 3, "fixture shape changed");

    let err = prog
        .validate()
        .expect_err("out-of-range else_target must be rejected");

    match err {
        guardc::GuardError::Validation(msg) => {
            assert!(
                msg.contains("9999"),
                "error should name the offending target, got: {}",
                msg
            );
        }
        other => panic!("expected GuardError::Validation, got {:?}", other),
    }
}

/// The first out-of-range value above the last valid index is the boundary:
/// `blocks.len()` itself must be rejected, and `blocks.len() - 1` accepted.
#[test]
fn validate_else_target_boundary_is_blocks_len() {
    let first_bad = branching_program(BlockId(2), BlockId(3));
    assert!(
        first_bad.validate().is_err(),
        "else_target == blocks.len() must be rejected"
    );

    let last_good = branching_program(BlockId(2), BlockId(2));
    assert!(
        last_good.validate().is_ok(),
        "else_target == blocks.len() - 1 must be accepted"
    );
}

// ---------------------------------------------------------------------------
// The other direction: in-range targets are still accepted.
// ---------------------------------------------------------------------------

/// The tightening must not reject a program that was valid before. A branch
/// with both targets in range stays accepted.
#[test]
fn validate_accepts_in_range_else_target() {
    let prog = branching_program(BlockId(2), BlockId(0));
    assert_eq!(prog.blocks.len(), 3);
    assert!(
        prog.validate().is_ok(),
        "in-range else_target must be accepted: {:?}",
        prog.validate().err()
    );
}

/// Self-branch: `else_target == self` is in range and must be accepted.
#[test]
fn validate_accepts_self_branch() {
    let prog = branching_program(BlockId(1), BlockId(1));
    assert!(prog.validate().is_ok());
}

/// The checks that already worked must keep working. `Jump` out of range and
/// `then_target` out of range were rejected before this change and must still
/// be rejected.
#[test]
fn validate_still_rejects_out_of_range_jump_and_then_target() {
    assert!(jumping_program(BlockId(9999)).validate().is_err());
    assert!(branching_program(BlockId(9999), BlockId(0))
        .validate()
        .is_err());
}

/// And in-range `Jump`/`then_target` stay accepted.
#[test]
fn validate_still_accepts_in_range_jump_and_then_target() {
    assert!(jumping_program(BlockId(2)).validate().is_ok());
    assert!(branching_program(BlockId(0), BlockId(1)).validate().is_ok());
}

// ---------------------------------------------------------------------------
// Compatibility: everything the lowerer produces must still validate.
// ---------------------------------------------------------------------------

fn module_with(invariants: Vec<CirInvariant>) -> CirModule {
    let mut st = SymbolTable::new();
    st.vars.insert(
        VarId(0),
        cir::VarInfo {
            name: "altitude".into(),
            ty: real_ty(),
            kind: VarKind::State,
            source_span: span(),
        },
    );
    st.vars.insert(
        VarId(1),
        cir::VarInfo {
            name: "armed".into(),
            ty: bool_ty(),
            kind: VarKind::State,
            source_span: span(),
        },
    );
    CirModule {
        name: "compat".into(),
        version: "0.1.0".into(),
        sample_period_ms: 20.0,
        symbol_table: st,
        invariants,
        derived: vec![],
        proof_config: vec![],
    }
}

fn inv(name: &str, when: Option<Expr>, ensure: Expr) -> CirInvariant {
    CirInvariant {
        name: name.into(),
        priority: Priority::Critical,
        when,
        ensure,
        on_violation: ViolationAction::Halt,
        source_span: span(),
    }
}

/// The corpus of CIR modules used as the compatibility witness. Between them
/// these cover both sites that mint a `Terminator::Branch`:
///
///  * `lower_invariant` — a `when` guard mints `Branch { else_target: next_block }`
///  * `lower_expr_to_var` on `Expr::If` — mints `Branch { else_target: else_block }`
fn corpus() -> Vec<(&'static str, CirModule)> {
    vec![
        // 1. Bare invariant, no guard: no Branch at all.
        (
            "bare",
            module_with(vec![inv("bare", None, cmp(BinOp::Lt, one(), two()))]),
        ),
        // 2. `when` guard -> the `lower_invariant` Branch.
        (
            "when_guard",
            module_with(vec![inv(
                "guarded",
                Some(truth()),
                cmp(BinOp::Lt, one(), two()),
            )]),
        ),
        // 3. Five `when`-guarded invariants chained: five Branches, each with a
        //    distinct `else_target`.
        (
            "many_when_guards",
            module_with(vec![
                inv("g1", Some(truth()), cmp(BinOp::Lt, one(), two())),
                inv("g2", Some(truth()), cmp(BinOp::Gt, two(), one())),
                inv("g3", Some(truth()), cmp(BinOp::Eq, one(), two())),
                inv("g4", Some(truth()), cmp(BinOp::Lte, one(), two())),
                inv("g5", Some(truth()), cmp(BinOp::Gte, one(), two())),
            ]),
        ),
        // 4. `Expr::If` -> the `lower_expr_to_var` Branch.
        (
            "expr_if",
            module_with(vec![inv(
                "if_inv",
                None,
                cmp(
                    BinOp::Eq,
                    one(),
                    Expr::If {
                        cond: Box::new(truth()),
                        then_branch: Box::new(one()),
                        else_branch: Box::new(two()),
                        ty: real_ty(),
                    },
                ),
            )]),
        ),
        // 5. `Expr::If` inside a `when` guard: both Branch sites at once.
        (
            "if_inside_when",
            module_with(vec![inv(
                "nested",
                Some(Expr::If {
                    cond: Box::new(truth()),
                    then_branch: Box::new(truth()),
                    else_branch: Box::new(truth()),
                    ty: bool_ty(),
                }),
                cmp(BinOp::Lt, one(), two()),
            )]),
        ),
        // 6. Quantifier expansion over an interval domain (unrolled body).
        (
            "forall_interval",
            module_with(vec![inv(
                "quantified",
                Some(truth()),
                Expr::Forall {
                    var: VarId(1),
                    domain: Domain::Interval { low: 0, high: 7 },
                    body: Box::new(cmp(BinOp::Lt, one(), two())),
                    ty: bool_ty(),
                },
            )]),
        ),
        // 7. Quantifier expansion over an enum domain, unguarded.
        (
            "exists_enum",
            module_with(vec![inv(
                "enum_quantified",
                None,
                Expr::Exists {
                    var: VarId(1),
                    domain: Domain::Enum(vec!["a".into(), "b".into(), "c".into()]),
                    body: Box::new(cmp(BinOp::Gt, two(), one())),
                    ty: bool_ty(),
                },
            )]),
        ),
        // 8. Temporal lowering: `RateOf` / `Delta` (no buffer declared, so the
        //    lowerer falls back to the variable's own slot).
        (
            "temporal",
            module_with(vec![inv(
                "temporal_inv",
                Some(truth()),
                cmp(
                    BinOp::Lt,
                    Expr::RateOf(VarId(0), real_ty()),
                    Expr::Delta(VarId(0), real_ty()),
                ),
            )]),
        ),
        // 9. Guard, quantifier, `Expr::If` and a bare invariant all at once.
        (
            "kitchen_sink",
            module_with(vec![
                inv("a", Some(truth()), cmp(BinOp::Lt, one(), two())),
                inv(
                    "b",
                    Some(truth()),
                    Expr::Binary {
                        op: BinOp::And,
                        left: Box::new(cmp(BinOp::Eq, one(), two())),
                        right: Box::new(Expr::Exists {
                            var: VarId(1),
                            domain: Domain::Array { size: 4 },
                            body: Box::new(Expr::If {
                                cond: Box::new(truth()),
                                then_branch: Box::new(truth()),
                                else_branch: Box::new(truth()),
                                ty: bool_ty(),
                            }),
                            ty: bool_ty(),
                        }),
                        ty: bool_ty(),
                    },
                ),
                inv("c", None, cmp(BinOp::Lt, one(), two())),
            ]),
        ),
        // 10. An empty module: `blocks` is just the loop skeleton.
        ("empty", module_with(vec![])),
    ]
}

/// Every program the lowerer emits must still validate after the tightening,
/// and every `else_target` it mints must be in range. The counts are printed
/// so a regression in CFG shape is visible, not just an `Ok`.
#[test]
fn every_lowered_program_still_validates() {
    let corpus = corpus();
    let mut total_blocks = 0usize;
    let mut total_branches = 0usize;
    let mut total_else_targets = 0usize;
    let mut max_else_target = 0u32;

    for (name, module) in &corpus {
        let prog =
            lower_module(module).unwrap_or_else(|e| panic!("{}: lower failed: {:?}", name, e));
        let block_count = prog.blocks.len();

        // Collect every else_target the lowerer minted, before validating.
        let else_targets: Vec<BlockId> = prog
            .blocks
            .iter()
            .filter_map(|b| match &b.terminator {
                Terminator::Branch { else_target, .. } => Some(*else_target),
                _ => None,
            })
            .collect();
        for t in &else_targets {
            assert!(
                (t.0 as usize) < block_count,
                "{}: lowerer minted out-of-range else_target {:?} ({} blocks)",
                name,
                t,
                block_count
            );
        }

        prog.validate()
            .unwrap_or_else(|e| panic!("{}: validate rejected a lowered program: {:?}", name, e));

        total_blocks += block_count;
        total_branches += else_targets.len();
        total_else_targets += else_targets.len();
        max_else_target = max_else_target.max(else_targets.iter().map(|t| t.0).max().unwrap_or(0));
    }

    println!(
        "compat: {} modules, {} blocks, {} branches, {} else_targets, max else_target = {}",
        corpus.len(),
        total_blocks,
        total_branches,
        total_else_targets,
        max_else_target
    );

    // Sanity: the corpus must actually exercise the else_target path, else
    // this test proves nothing.
    assert!(
        total_else_targets > 0,
        "corpus produced no else_targets — the compatibility witness is vacuous"
    );
}

/// The strongest compatibility statement available: the tightened `validate`
/// must not newly reject anything the lowerer produces. Every lowered program
/// validates, AND every else_target is genuinely in range, so the new check
/// has nothing to fire on.
#[test]
fn tightening_fires_on_nothing_the_lowerer_produces() {
    let corpus = corpus();
    let mut checked = 0usize;

    for (name, module) in &corpus {
        let prog = lower_module(module).unwrap();
        let block_count = prog.blocks.len();
        let rejections: Vec<String> = prog
            .blocks
            .iter()
            .filter_map(|b| match &b.terminator {
                Terminator::Branch { else_target, .. }
                    if (else_target.0 as usize) >= block_count =>
                {
                    Some(format!("block {} else_target {:?}", b.id.0, else_target))
                }
                _ => None,
            })
            .collect();
        assert!(
            rejections.is_empty(),
            "{}: tightening would reject lowered program: {:?}",
            name,
            rejections
        );
        checked += prog.blocks.len();
    }

    println!("tightening fires on 0 of {} lowered blocks", checked);
}
