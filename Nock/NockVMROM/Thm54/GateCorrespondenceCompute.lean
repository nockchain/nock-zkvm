import Nock.AIR

/-!
# Gate-level correspondence receipts for the COMPUTE table

Only claims that are cheap to compile live here.  Three groups:

1. **Where `(a, b, c)` are read.**  The paper's three equality coins enter
   the compute AIR at challenge indices `2, 3, 4` (`Nock/AIR.lean:550-552`).  A census shows
   they are read by exactly one of the eleven per-opcode evaluation blocks — OP5 — and by no
   memory-record block, no SV gate, no formula gate, no `mem_record_1` gate, and not the
   `z·zinv` witness gate.

2. **What their soundness costs.**  The OP5 evaluation block pins `e.leaf` to the paper's `=`
   operator with **no hypothesis whatsoever on `(a, b, c)`**
   (`op5_evaluation_is_equality_without_abc`).  What `(a, b, c)` buy is
   *completeness*, and that is genuinely random-dependent
   (`op5_rlc_completeness_needs_abc`).

3. **The `ln` recurrence and the `cons` row.**  The paper's `ln` recurrence
   sums over `j ∈ {1,3,4} ∪ {0,2,5,7,8} ∪ {6,9}` and so omits `op_11` entirely; this tree puts
   the `cons` row in the `α¹` branch (`cons_row_uses_alpha_one_branch`), following `V_comp`'s
   `state ≠ OP_0` else-if rather than the appendix display.

Everything here is `K`-generic and reuses the tight biconditionals of `Nock/AIR.lean`.
-/

namespace Nock
namespace Reified
namespace GateCorrespondenceCompute

open ComputeTable

set_option maxRecDepth 100000

/-! ## 1. Challenge census: which gates read `a`, `b`, `c` -/

/-- Does the expression read challenge slot `i`? -/
def usesChal (i : ℕ) : Expr → Bool
  | .Var .challenge j => j == i
  | .Var _ _ => false
  | .Const _ => false
  | .Add a b => usesChal i a || usesChal i b
  | .Sub a b => usesChal i a || usesChal i b
  | .Mul a b => usesChal i a || usesChal i b
  | .Neg a => usesChal i a
  | .Pow a _ => usesChal i a

/-- Reads any of the three equality coins `a = chal 2`, `b = chal 3`, `c = chal 4`
(`Nock/AIR.lean:550-552`). -/
def usesEqCoins (e : Expr) : Bool :=
  usesChal 2 e || usesChal 3 e || usesChal 4 e

/-- **The OP5 evaluation block reads all three equality coins** — the paper's `EC.5.5`. -/
theorem op5_block_reads_all_three_eq_coins :
    ((evalRExprs .s5).any (usesChal 2)) = true ∧
      ((evalRExprs .s5).any (usesChal 3)) = true ∧
      ((evalRExprs .s5).any (usesChal 4)) = true := by
  decide

/-- **No other per-opcode evaluation block reads them.** -/
theorem eq_coins_absent_from_other_eval_blocks :
    ∀ st ∈ [State.s0, .s1, .s2, .s3, .s4, .s6, .s7, .s8, .s9, .cons],
      ((evalRExprs st).all (fun e => !usesEqCoins e)) = true := by
  decide

/-- **No memory-record block reads them, including OP5's.** -/
theorem eq_coins_absent_from_all_memory_blocks :
    ∀ st ∈ [State.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .cons],
      ((memBlkExprs st).all (fun e => !usesEqCoins e)) = true := by
  decide

/-- **No always-on gate reads them.**  The State-Variables block, the formula-decomposition
block, the `mem_record_1` block and the `z·zinv` witness gate are all equality-coin-free. -/
theorem eq_coins_absent_from_always_on_gates :
    (svExprs.all (fun e => !usesEqCoins e)) = true ∧
      (formulaExprs.all (fun e => !usesEqCoins e)) = true ∧
      (mr1Exprs.all (fun e => !usesEqCoins e)) = true ∧
      (!usesEqCoins zZinvExpr) = true := by
  decide

/-! ## 2. `(a, b, c)` are a completeness device, not a soundness assumption -/

/-- **The OP5 evaluation block pins `e.leaf` to the paper's `=` operator, with no hypothesis
on `(a, b, c)`.**

`Vcomp` requires `evaluation = =(sf_evaluation_1, sf_evaluation_2)`, and the
`Lem:equiv_compute` proof sketch explains `EC.5.1-5.5` as exactly that
correlation.  The soundness direction needs nothing from the coins: `EC.5.2-5.4` force equality outright when `e.leaf = 0`, and when `e.leaf = 1` the
existence of the inverse witness in `EC.5.5` forces the difference triple to
be nonzero whatever `(a, b, c)` are. -/
theorem op5_evaluation_is_equality_without_abc
    {K : Type*} [Field K]
    (inp : ComputeTable.Inputs K) (op : State → K) (pub : ComputeTable.Pub K)
    (dec : ComputeTable.Dec K) (ex : ComputeTable.Extra K)
    (h : ∀ e ∈ evalRExprs .s5, e.eval (computeEnvFull inp op pub dec ex) = 0) :
    pub.e.leaf = FP.eqOp pub.sf1_e pub.sf2_e := by
  obtain ⟨-, -, -, -, -, -, -, hbool, hs, hd, hl, hinv⟩ :=
    (evalRExprs_s5_sound inp op pub dec ex).mp h
  rcases mul_eq_zero.mp hbool with h0 | h1'
  · have h0' : (1 : K) - pub.e.leaf = 1 := by rw [h0]; ring
    rw [h0', one_mul] at hs hd hl
    have heq : pub.sf1_e = pub.sf2_e :=
      FP.ext (sub_eq_zero.mp hs) (sub_eq_zero.mp hd) (sub_eq_zero.mp hl)
    simp [h0, FP.eqOp, heq]
  · have h1 : pub.e.leaf = 1 := (sub_eq_zero.mp h1').symm
    have hne : pub.sf1_e ≠ pub.sf2_e := by
      intro heq
      rw [heq, h1] at hinv
      simp at hinv
    simp [h1, FP.eqOp, hne]

/-- **Completeness genuinely needs the coins.**  For the nonzero difference triple `(1, -1, 0)`
there are coin values at which no inverse witness `inv_gen` exists, so `EC.5.5` is unsatisfiable and the honest prover of an unequal OP5 row is stuck.  This
is why the coins may not be deleted, and it is a *completeness* event (probability `≤ 1/|K|`
per row by Schwartz-Zippel on a linear form), not a soundness one. -/
theorem op5_rlc_completeness_needs_abc {K : Type*} [Field K] :
    ∃ a b c ds dd dl : K,
      (ds ≠ 0 ∨ dd ≠ 0 ∨ dl ≠ 0) ∧
        ∀ g : K, g * (a * ds + b * dd + c * dl + (1 - 1)) ≠ 1 := by
  refine ⟨1, 1, 1, 1, -1, 0, Or.inl one_ne_zero, ?_⟩
  intro g
  simp

/-! ## 3. The `ln` recurrence and the `cons` row -/

variable {K : Type*} [Field K]
  (inp : ComputeTable.Inputs K) (op : State → K) (pub : ComputeTable.Pub K)
  (dec : ComputeTable.Dec K) (ex : ComputeTable.Extra K)

/-- **This tree puts the `cons` row in the `α¹` branch of the `ln` recurrence.**  The paper's
displayed identity sums only over `j ∈ {1,3,4} ∪ {0,2,5,7,8} ∪ {6,9}` — the
`cons` selector `op_11` appears nowhere in it, so read literally it forces `ln(i) = 0` on a
`cons` row.  `V_comp` does cover it: a cell head fails the outer test and the `state ≠ OP_0`
else-if gives `ln = ln_prev · z`.  This tree follows `1741` and groups
`.cons` with `.s1/.s3/.s4`. -/
theorem cons_row_uses_alpha_one_branch
    (h : ∀ e ∈ memBlkExprs .cons, e.eval (computeEnvFull inp op pub dec ex) = 0) :
    pub.ln = pub.ln_prev * inp.α :=
  ((memBlkExprs_cons_sound inp op pub dec ex).mp h).2.2

/-- The same `α¹` branch is what `.s1`, `.s3` and `.s4` carry — the three opcodes the paper
does put in the `α` group. -/
theorem alpha_one_branch_states
    (h1 : ∀ e ∈ memBlkExprs .s1, e.eval (computeEnvFull inp op pub dec ex) = 0)
    (h3 : ∀ e ∈ memBlkExprs .s3, e.eval (computeEnvFull inp op pub dec ex) = 0)
    (h4 : ∀ e ∈ memBlkExprs .s4, e.eval (computeEnvFull inp op pub dec ex) = 0) :
    pub.ln = pub.ln_prev * inp.α ∧ pub.ln = pub.ln_prev * inp.α
      ∧ pub.ln = pub.ln_prev * inp.α :=
  ⟨((memBlkExprs_s1_sound inp op pub dec ex).mp h1).2.2,
   ((memBlkExprs_s3_sound inp op pub dec ex).mp h3).2.2,
   ((memBlkExprs_s4_sound inp op pub dec ex).mp h4).2.2⟩

/-- The `α²` group is `{OP0, OP2, OP5, OP7, OP8}` and the `α³` group is `{OP6, OP9}`, exactly
as the paper states them. -/
theorem alpha_two_group
    (h0 : ∀ e ∈ memBlkExprs .s0, e.eval (computeEnvFull inp op pub dec ex) = 0)
    (h2 : ∀ e ∈ memBlkExprs .s2, e.eval (computeEnvFull inp op pub dec ex) = 0)
    (h5 : ∀ e ∈ memBlkExprs .s5, e.eval (computeEnvFull inp op pub dec ex) = 0)
    (h7 : ∀ e ∈ memBlkExprs .s7, e.eval (computeEnvFull inp op pub dec ex) = 0)
    (h8 : ∀ e ∈ memBlkExprs .s8, e.eval (computeEnvFull inp op pub dec ex) = 0) :
    pub.ln = pub.ln_prev * inp.α ^ 2 ∧ pub.ln = pub.ln_prev * inp.α ^ 2
      ∧ pub.ln = pub.ln_prev * inp.α ^ 2 ∧ pub.ln = pub.ln_prev * inp.α ^ 2
      ∧ pub.ln = pub.ln_prev * inp.α ^ 2 :=
  ⟨((memBlkExprs_s0_sound inp op pub dec ex).mp h0).2.2.1,
   ((memBlkExprs_s2_sound inp op pub dec ex).mp h2).2.2.2,
   ((memBlkExprs_s5_sound inp op pub dec ex).mp h5).2.2.2,
   ((memBlkExprs_s7_sound inp op pub dec ex).mp h7).2.2.2,
   ((memBlkExprs_s8_sound inp op pub dec ex).mp h8).2.2.2⟩

theorem alpha_three_group
    (h6 : ∀ e ∈ memBlkExprs .s6, e.eval (computeEnvFull inp op pub dec ex) = 0)
    (h9 : ∀ e ∈ memBlkExprs .s9, e.eval (computeEnvFull inp op pub dec ex) = 0) :
    pub.ln = pub.ln_prev * inp.α ^ 3 ∧ pub.ln = pub.ln_prev * inp.α ^ 3 :=
  ⟨((memBlkExprs_s6_sound inp op pub dec ex).mp h6).2.2.2.2,
   ((memBlkExprs_s9_sound inp op pub dec ex).mp h9).2.2.2⟩

#print axioms op5_block_reads_all_three_eq_coins
#print axioms eq_coins_absent_from_other_eval_blocks
#print axioms eq_coins_absent_from_all_memory_blocks
#print axioms eq_coins_absent_from_always_on_gates
#print axioms op5_evaluation_is_equality_without_abc
#print axioms op5_rlc_completeness_needs_abc
#print axioms cons_row_uses_alpha_one_branch
#print axioms alpha_one_branch_states
#print axioms alpha_two_group
#print axioms alpha_three_group

end GateCorrespondenceCompute
end Reified
end Nock
