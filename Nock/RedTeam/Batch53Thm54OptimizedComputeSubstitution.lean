import Nock.RedTeam.Batch52Thm54SampledComputeIO
import Nock.NockVMROM.Thm54.OptimizedComputeSubstitution

/-!
Assertions outside that section continue to test the current production substitution.
-/

namespace Nock.RedTeam.Batch53

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.StrictPackage

/-! ## 1. Independent generic substitution attacks -/

/-- A substitution exercising every variable kind and replacing trace variables by degree-two
expressions. -/
def attackSubst : VarKind → ℕ → Expr
  | .traceCur, i => .Mul (.Var .traceCur (100 + i)) (.Var .traceNext (200 + i))
  | .traceNext, i => .Pow (.Var .traceNext (300 + i)) 2
  | .challenge, i => .Neg (.Var .challenge (400 + i))
  | .publicVal, i => .Add (.Var .publicVal (500 + i)) (.Const 7)

/-- Constants, all four variable kinds, nested multiplication, negation, and power are traversed
structurally rather than treated as projections. -/
def allConstructorExpr : Expr :=
  .Add (.Const 9)
    (.Mul (.Var .traceCur 1)
      (.Pow (.Sub (.Var .traceNext 2)
        (.Neg (.Add (.Var .challenge 3) (.Var .publicVal 4)))) 3))

def allConstructorExpected : Expr :=
  .Add (.Const 9)
    (.Mul
      (.Mul (.Var .traceCur 101) (.Var .traceNext 201))
      (.Pow
        (.Sub (.Pow (.Var .traceNext 302) 2)
          (.Neg (.Add (.Neg (.Var .challenge 403))
            (.Add (.Var .publicVal 504) (.Const 7))))) 3))

theorem subst_all_constructors :
    Expr.subst attackSubst allConstructorExpr = allConstructorExpected := by
  rfl

/-- The generic evaluation theorem is exercised on the nested all-kind expression. -/
def nestedAllKindExpr : Expr :=
  .Mul (.Var .traceCur 1)
    (.Pow (.Add (.Var .traceNext 2) (.Var .challenge 3)) 4)

theorem subst_nested_eval {K : Type*} [Field K] (env : Env K) :
    (Expr.subst attackSubst nestedAllKindExpr).eval env =
      nestedAllKindExpr.eval (Env.ofSubst attackSubst env) :=
  Expr.eval_subst _ _ _

/-- The support theorem applies to the same nested all-kind expression. -/
theorem subst_nested_support :
    (Expr.subst attackSubst
      (.Mul (.Var .traceCur 1)
        (.Pow (.Add (.Var .traceNext 2) (.Var .challenge 3)) 4))).vars ⊆
      (Expr.substSupport attackSubst
        (.Mul (.Var .traceCur 1)
          (.Pow (.Add (.Var .traceNext 2) (.Var .challenge 3)) 4))) :=
  Expr.vars_subst_subset _ _

/-- The multiplicative degree bound is sharp: a source quartic can become degree eight.  Thus the
generic theorem alone cannot certify future degree-at-most-four gates. -/
theorem degree_bound_sharp :
    let e : Expr := .Pow (.Mul (.Var .traceCur 0) (.Var .traceNext 0)) 2
    e.degree = 4 ∧ (e.subst attackSubst).degree = 8 := by
  decide

/-! ## 2. Every erased memory-record field is decoder-forced -/

/-- The induced source environment has no independent `mr2` witness: all eight fields are exactly
the selected decoder expressions. -/
theorem mr2_has_no_independent_witness {K : Type*} [Field K]
    (env : Env K) (j : Fin 8) :
    (Env.ofSubst computeSubst env).trace (75 + j) =
      (mr2Field .traceCur j).eval env := by
  fin_cases j <;>
    simp [Env.ofSubst, computeSubst, computeTraceSubst]

/-- Likewise for all eight fields of `mr3`. -/
theorem mr3_has_no_independent_witness {K : Type*} [Field K]
    (env : Env K) (j : Fin 8) :
    (Env.ofSubst computeSubst env).trace (83 + j) =
      (mr3Field .traceCur j).eval env := by
  fin_cases j <;>
    simp [Env.ofSubst, computeSubst, computeTraceSubst]

/-- Concrete one-hot physical environment with distinct stored coordinates. -/
def selectorEnv (st : State) : Env ℚ where
  trace i :=
    if i < 11 then
      if i = Nock.Reified.opCol st then 1 else 0
    else i
  traceNext i :=
    if i < 11 then
      if i = Nock.Reified.opCol st then 1 else 0
    else 1000 + i
  chal i := i + 2
  pub i := i + 3

/-- All eleven selector cases independently evaluate to the exact `mr2` row:
OP0 uses `(s,e,f_t.leaf)`, OP2/5/6/7/8/9 use `(f_t,f_th,2)`, and all other states erase it. -/
theorem mr2_roundtrip_all_states (st : State) :
    List.ofFn (fun j : Fin 8 => (mr2Field .traceCur j).eval (selectorEnv st)) =
      match st with
      | .s0 => [13, 14, 15, 19, 20, 21, 54, 268]
      | .s2 | .s5 | .s6 | .s7 | .s8 | .s9 =>
          [52, 53, 54, 55, 56, 57, 2, 268]
      | _ => [0, 0, 0, 0, 0, 0, 0, 0] := by
  cases st <;>
    norm_num [mr2Field, mr2Group, selectorEnv, pubFP, decFP, lnPrev, ext0,
      Nock.Reified.opCol, Expr.eval]

/-- All eleven selector cases independently evaluate to the exact `mr3` row. -/
theorem mr3_roundtrip_all_states (st : State) :
    List.ofFn (fun j : Fin 8 => (mr3Field .traceCur j).eval (selectorEnv st)) =
      match st with
      | .s6 => [58, 59, 60, 61, 62, 63, 2, 536]
      | .s9 => [28, 29, 30, 34, 35, 36, 57, 536]
      | _ => [0, 0, 0, 0, 0, 0, 0, 0] := by
  cases st <;>
    norm_num [mr3Field, mr3Group, selectorEnv, pubFP, decFP, lnPrev, ext0,
      Nock.Reified.opCol, Expr.eval]

/-- OP1 and OP6 are genuinely different, so replaying the OP6 decoder under the OP1 selector does
not preserve the record. -/
theorem wrong_selector_replay_rejected :
    List.ofFn (fun j : Fin 8 => (mr2Field .traceCur j).eval (selectorEnv .s1)) ≠
      List.ofFn (fun j : Fin 8 => (mr2Field .traceCur j).eval (selectorEnv .s6)) := by
  rw [mr2_roundtrip_all_states, mr2_roundtrip_all_states]
  decide

/-! ## 3. Source-column coverage -/

def computeSourceBlock : List Expr :=
  Nock.Reified.svExprs ++ Nock.Reified.formulaExprs ++ Nock.Reified.mr1Exprs ++
    [Nock.Reified.zZinvExpr] ++ Nock.Reified.perStateGated ++
    [Nock.Reified.Trans.lnChainExpr]

theorem source_interface_is_94_columns :
    Nock.Reified.computeAIR.numTraceCols = 94 := rfl

/-- Every one of the 94 source trace columns has a decoder expression supported only on physical
13/58 slots `0..70` and derived challenges `0..5`; no source column reaches the fallback branch. -/
theorem all_94_source_columns_have_physical_decoders
    (kind : VarKind) (i : Fin 94)
    (hkind : kind = .traceCur ∨ kind = .traceNext) :
    ∀ x ∈ (computeTraceSubst kind i).vars,
      match x.1 with
      | .traceCur | .traceNext => x.2 < 71
      | .challenge => x.2 < 6
      | .publicVal => True := by
  rcases hkind with rfl | rfl <;> fin_cases i <;>
    simp [computeTraceSubst, semanticPub, restoredPub, sourcePubAt, restoredAField,
      restoredBField, restoredIOHostField, restoredDenomHostField,
      mr2Field, mr2Group, mr3Field, mr3Group, Nock.Reified.allStates,
      overlayANat, overlayBNat, pubFP, decFP, lnPrev, lnCur, consInv, invGen, ext0,
      Nock.Reified.opCol, Expr.vars]

theorem zinv_substitution_is_pinned :
    Nock.Reified.zZinvExpr.subst computeSubst =
      .Sub (.Mul (.Var .challenge 1) (.Var .challenge 5)) (.Const 1) ∧
      (Nock.Reified.zZinvExpr.subst computeSubst).degree = 0 := by
  constructor <;> rfl

/-! ## 4. -/

def historicalOverlayCoord (kind : VarKind) (coord : ℕ) : Expr :=
  Nock.Reified.allStates.foldr
    (fun st acc =>
      let role := if coord < 3 then overlayANat st else overlayBNat st
      let c := if coord < 3 then coord else coord - 3
      .Add (.Mul (.Var kind (Nock.Reified.opCol st)) (pubFP kind role c)) acc)
    (.Const 0)

def historicalWalkSubst : VarKind → ℕ → Expr
  | .traceCur, 0 => lnCur .traceCur
  | .traceCur, i => historicalOverlayCoord .traceCur i
  | .traceNext, 0 => lnCur .traceNext
  | .traceNext, i => historicalOverlayCoord .traceNext i
  | .challenge, i => .Var .challenge i
  | .publicVal, i => .Var .publicVal i

def historicalSampledIOSubst : VarKind → ℕ → Expr
  | .traceCur, 0 => historicalOverlayCoord .traceCur 5
  | .traceNext, 0 => historicalOverlayCoord .traceNext 5
  | .traceCur, i => .Var .traceCur i
  | .traceNext, i => .Var .traceNext i
  | .challenge, i => .Var .challenge i
  | .publicVal, i => .Var .publicVal i

/-- **Finding B53-F1.** The current walk map is off by one: source walk column five
(`walkMultiplier`) and source sampled-IO column zero (`ioAcc`) are definitionally the same
state-selected physical expression.  No phase/state guard separates them. -/
theorem walk_multiplier_collides_with_sampled_io :
    historicalWalkSubst .traceCur 5 = historicalSampledIOSubst .traceCur 0 := by
  rfl

/-- The same collision exists on the next-row side. -/
theorem walk_multiplier_collides_with_sampled_io_next :
    historicalWalkSubst .traceNext 5 = historicalSampledIOSubst .traceNext 0 := by
  rfl

/-- The first walk overlay column is shifted too: source `count` maps to overlay coordinate one,
not coordinate zero. -/
theorem walk_count_is_shifted :
    historicalWalkSubst .traceCur 1 = historicalOverlayCoord .traceCur 1 := by
  rfl

/-- An OP1 physical row making the intended six coordinates pairwise visible. -/
def op1OverlayEnv : Env ℚ where
  trace i :=
    if i = 1 then 1
    else if i < 11 then 0
    else if i = 19 then 7
    else if i = 20 then 11
    else if i = 24 then 17
    else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

/-- Concrete evaluation of the off-by-one: the intended OP1 overlay-A size is `7`, while source
walk-count substitution reads overlay-A dyck `11`. -/
theorem walk_count_shift_is_observable :
    (historicalOverlayCoord .traceCur 0).eval op1OverlayEnv = 7 ∧
      (Expr.subst historicalWalkSubst (tc 1)).eval op1OverlayEnv = 11 := by
  constructor
  · norm_num [historicalOverlayCoord, op1OverlayEnv, Nock.Reified.allStates,
      overlayANat, overlayBNat, pubFP, ext0, Nock.Reified.opCol, Expr.eval]
  · change (historicalOverlayCoord .traceCur 1).eval op1OverlayEnv = 11
    norm_num [historicalOverlayCoord, op1OverlayEnv, Nock.Reified.allStates,
      overlayANat, overlayBNat, pubFP, ext0, Nock.Reified.opCol, Expr.eval]

/-- Concrete cross-role replay: both source roles read the same OP1 overlay-B leaf `17`. -/
theorem cross_role_replay_is_observable :
    (Expr.subst historicalWalkSubst (tc 5)).eval op1OverlayEnv = 17 ∧
      (Expr.subst historicalSampledIOSubst (tc 0)).eval op1OverlayEnv = 17 := by
  rw [show Expr.subst historicalWalkSubst (tc 5) =
      historicalWalkSubst .traceCur 5 by rfl,
    show Expr.subst historicalSampledIOSubst (tc 0) =
      historicalSampledIOSubst .traceCur 0 by rfl,
    walk_multiplier_collides_with_sampled_io]
  norm_num [historicalSampledIOSubst, historicalOverlayCoord, op1OverlayEnv,
    Nock.Reified.allStates,
    overlayANat, overlayBNat, pubFP, ext0, Nock.Reified.opCol, Expr.eval]

/-! ## 5. Sampled-IO source columns still hit selector slots -/

/-- Except for its accumulator, the current sampled-IO map is still the identity on source trace
columns. -/
theorem sampled_io_nonaccumulator_columns_are_direct :
    historicalSampledIOSubst .traceCur 1 = .Var .traceCur 1 ∧
      historicalSampledIOSubst .traceCur 2 = .Var .traceCur 2 ∧
      historicalSampledIOSubst .traceCur 3 = .Var .traceCur 3 ∧
      historicalSampledIOSubst .traceCur 4 = .Var .traceCur 4 ∧
      historicalSampledIOSubst .traceCur 5 = .Var .traceCur 5 ∧
      historicalSampledIOSubst .traceCur 6 = .Var .traceCur 6 := by
  repeat' apply And.intro
  all_goals rfl

/-- Therefore the substituted degree-four finite-IO fold reads physical columns `1..6`, which in
the normalized 13/58 row are opcode selectors, not denominator/active-slot decoder expressions. -/
theorem sampled_fold_reads_selector_slots :
    ({(.traceCur, 1), (.traceCur, 2), (.traceCur, 3), (.traceCur, 4),
        (.traceCur, 5), (.traceCur, 6)} : Finset (VarKind × ℕ)) ⊆
      (Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates.foldedProgStep3.subst
        historicalSampledIOSubst).vars := by
  decide

/-! ## 6. Block commutation is all-environment, but only substitution-generic -/

def actualWalkBlock : List Expr :=
  [Trans.walkLnStep, Trans.walkCountStep, Trans.walkAccStep,
    Trans.walkLn1, Trans.walkCount1, Trans.walkAccInit, Trans.walkOut]

def actualFiniteIOBlock : List Expr :=
  [Nock.NockVMROM.Thm54.FiniteIO.ioAccInit,
    Nock.NockVMROM.Thm54.FiniteIO.ioInvPin 8 4,
    Nock.NockVMROM.Thm54.FiniteIO.ioProgAccStep,
    Nock.NockVMROM.Thm54.FiniteIO.ioTerm]

/-- The real 352-expression per-state block commutes in both directions on every physical
environment; the theorem is not restricted to rows produced by the codec. -/
theorem actual_per_state_block_commutes {K : Type*} [Field K] (env : Env K) :
    (∀ e ∈ Nock.Reified.perStateGated, (e.subst computeSubst).eval env = 0) ↔
      (∀ e ∈ Nock.Reified.perStateGated,
        e.eval (Env.ofSubst computeSubst env) = 0) :=
  perStateGated_subst_iff _

/-- The actual cross-row line-nonce gate commutes in both directions on every environment. -/
theorem actual_ln_chain_commutes {K : Type*} [Field K] (env : Env K) :
    (Nock.Reified.Trans.lnChainExpr.subst computeSubst).eval env = 0 ↔
      Nock.Reified.Trans.lnChainExpr.eval (Env.ofSubst computeSubst env) = 0 := by
  rw [Expr.eval_subst]

/-- The walk theorem is a genuine biconditional for arbitrary physical environments when
instantiated at the real walk block. -/
theorem actual_walk_block_commutes {K : Type*} [Field K] (env : Env K) :
    (∀ e ∈ actualWalkBlock, (e.subst walkSubst).eval env = 0) ↔
      (∀ e ∈ actualWalkBlock, e.eval (Env.ofSubst walkSubst env) = 0) :=
  walk_block_subst_iff _ _

/-- Likewise for the actual unfurled finite-IO request block.  This is algebraically correct but
does not validate the semantic choice of replacement expressions exposed above. -/
theorem actual_finite_io_block_commutes {K : Type*} [Field K] (env : Env K) :
    (∀ e ∈ actualFiniteIOBlock, (e.subst sampledIOSubst).eval env = 0) ↔
      (∀ e ∈ actualFiniteIOBlock,
        e.eval (Env.ofSubst sampledIOSubst env) = 0) :=
  sampledIO_block_subst_iff _ _

/-- The displayed degree-four finite-IO fold also commutes on all environments.  This algebraic
fact does not make the current direct projections of source columns `1..6` semantic decoders. -/
theorem actual_folded_io_gate_commutes {K : Type*} [Field K] (env : Env K) :
    (Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates.foldedProgStep3.subst
        sampledIOSubst).eval env = 0 ↔
      Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates.foldedProgStep3.eval
        (Env.ofSubst sampledIOSubst env) = 0 := by
  rw [Expr.eval_subst]

/-! ### The paper's displayed four-way nonlinear fold -/

/-- Independent symbolic transcription of `ComputeTable.combinedGate = 1`. -/
def combinedSourceExpr : Expr :=
  .Sub
    (.Add
      (.Add
        (.Add
          (.Mul (tc 3)
            (.Add (.Mul (tc 92) (.Sub (chl 1) Nock.Reified.cSf1e.size))
              Nock.Reified.cE.leaf))
          (.Mul (tc 5)
            (.Mul (tc 92)
              (.Add
                (.Add
                  (.Add (.Mul (chl 2)
                    (.Sub Nock.Reified.cSf1e.size Nock.Reified.cSf2e.size))
                    (.Mul (chl 3)
                      (.Sub Nock.Reified.cSf1e.dyck Nock.Reified.cSf2e.dyck)))
                  (.Mul (chl 4)
                    (.Sub Nock.Reified.cSf1e.leaf Nock.Reified.cSf2e.leaf)))
                (.Sub (.Const 1) Nock.Reified.cE.leaf)))))
        (.Mul (tc 8)
          (.Mul (.Mul Nock.Reified.cSf2e.size Nock.Reified.cS.size) (tc 92))))
      (.Mul (tc 10)
        (.Mul (.Mul Nock.Reified.cSf1e.size Nock.Reified.cSf2e.size) (tc 92))))
    (.Const 1)

/-- The independent expression evaluates to the existing combined gate on every source row, not
only an encoded honest row. -/
theorem combinedSourceExpr_eval {K : Type*} [Field K]
    (inp : Inputs K) (op : State → K) (pub : Pub K) (dec : Dec K) (ex : Extra K) :
    combinedSourceExpr.eval (Nock.Reified.computeEnvFull inp op pub dec ex) =
      ComputeTable.combinedGate inp pub op ex.invGen - 1 := by
  simp only [combinedSourceExpr, Expr.eval, Nock.Reified.eval_op3,
    Nock.Reified.eval_op5, Nock.Reified.eval_op8, Nock.Reified.eval_op10,
    Nock.Reified.eval_invGen, Nock.Reified.eval_chZ, Nock.Reified.eval_chA,
    Nock.Reified.eval_chB, Nock.Reified.eval_chC, Nock.Reified.eval_cSf1e,
    Nock.Reified.eval_cSf2e, Nock.Reified.eval_cE, Nock.Reified.eval_cS,
    FPExpr.eval_size, FPExpr.eval_dyck, FPExpr.eval_leaf,
    ComputeTable.combinedGate, Int.cast_one]

/-- Combined-gate substitution commutes in both directions over an arbitrary physical
environment. -/
theorem combinedSourceExpr_subst_eval {K : Type*} [Field K] (env : Env K) :
    (combinedSourceExpr.subst computeSubst).eval env =
      combinedSourceExpr.eval (Env.ofSubst computeSubst env) :=
  Expr.eval_subst _ _ _

/-! ## 7. -/

/-- Degree-two substitutions can double a source quartic to eight; each concrete source block
therefore needs its own refold proof. -/
theorem source_quartic_not_automatically_degree_four (e : Expr)
    (h : e.degree = 4) :
    (e.subst computeSubst).degree ≤ 8 := by
  simpa [h] using degree_computeSubst_le e

/-- Exact source-block degree census after substitution. -/
theorem substituted_block_max_degrees :
    (Nock.Reified.svExprs.map (fun e => (e.subst computeSubst).degree)).foldr Nat.max 0 = 3 ∧
      (Nock.Reified.formulaExprs.map
        (fun e => (e.subst computeSubst).degree)).foldr Nat.max 0 = 3 ∧
      (Nock.Reified.perStateGated.map
        (fun e => (e.subst computeSubst).degree)).foldr Nat.max 0 = 5 ∧
      (actualWalkBlock.map (fun e => (e.subst walkSubst).degree)).foldr Nat.max 0 = 4 ∧
      (actualFiniteIOBlock.map
        (fun e => (e.subst sampledIOSubst).degree)).foldr Nat.max 0 = 2 := by
  decide

/-- The remaining source blocks and the displayed sampled-IO fold complete the exact degree
census.  In particular the source degree-four IO fold becomes degree five because its accumulator
is a selector-times-overlay expression; its current substitution is not a degree-four fold. -/
theorem remaining_block_degree_census :
    (Nock.Reified.mr1Exprs.map
      (fun e => (e.subst computeSubst).degree)).foldr Nat.max 0 = 1 ∧
      (Nock.Reified.zZinvExpr.subst computeSubst).degree = 0 ∧
      (Nock.Reified.Trans.lnChainExpr.subst computeSubst).degree = 1 ∧
      (Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates.foldedProgStep3.subst
        historicalSampledIOSubst).degree = 5 := by
  decide

/-- The only current substituted per-state gates over degree four are indices 177 and 270,
the selector-gated `e.leaf` booleanity constraints in OP3 and OP5. -/
theorem exact_over_degree_four_indices :
    ((List.range Nock.Reified.perStateGated.length).zip
      (Nock.Reified.perStateGated.map (fun e => (e.subst computeSubst).degree))).filter
        (fun x => 4 < x.2) = [(177, 5), (270, 5)] := by
  decide

def op3ELeafBool : Expr :=
  Nock.Reified.gateBy .s3
    (.Mul Nock.Reified.cE.leaf (.Sub (.Const 1) Nock.Reified.cE.leaf))

def op5ELeafBool : Expr :=
  Nock.Reified.gateBy .s5
    (.Mul Nock.Reified.cE.leaf (.Sub (.Const 1) Nock.Reified.cE.leaf))

/-- The two exact high-degree positions are the OP3/OP5 output-bit booleanity gates. -/
theorem exact_high_degree_gate_bodies :
    Nock.Reified.perStateGated.get ⟨177, by decide⟩ = op3ELeafBool ∧
      Nock.Reified.perStateGated.get ⟨270, by decide⟩ = op5ELeafBool ∧
      (op3ELeafBool.subst computeSubst).degree = 5 ∧
      (op5ELeafBool.subst computeSubst).degree = 5 := by
  constructor
  · rfl
  constructor
  · rfl
  decide

/-- The paper's displayed four-way combined gate remains at degree four after substitution; it is
not one of the two degree-five obligations. -/
theorem combined_gate_degree_audit :
    combinedSourceExpr.degree = 4 ∧
      (combinedSourceExpr.subst computeSubst).degree = 4 := by
  decide

/-! ## 8. Consumed-scope guards -/

theorem scope_guard_alias :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch52.scope_guard

def strict_package_still_requires_B29
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :=
  Nock.RedTeam.Batch51.strict_package_still_consumes_B29 P

end Nock.RedTeam.Batch53

#print axioms Nock.RedTeam.Batch53.subst_all_constructors
#print axioms Nock.RedTeam.Batch53.subst_nested_eval
#print axioms Nock.RedTeam.Batch53.degree_bound_sharp
#print axioms Nock.RedTeam.Batch53.mr2_roundtrip_all_states
#print axioms Nock.RedTeam.Batch53.mr3_roundtrip_all_states
#print axioms Nock.RedTeam.Batch53.walk_multiplier_collides_with_sampled_io
#print axioms Nock.RedTeam.Batch53.walk_count_shift_is_observable
#print axioms Nock.RedTeam.Batch53.cross_role_replay_is_observable
#print axioms Nock.RedTeam.Batch53.sampled_fold_reads_selector_slots
#print axioms Nock.RedTeam.Batch53.actual_per_state_block_commutes
#print axioms Nock.RedTeam.Batch53.actual_ln_chain_commutes
#print axioms Nock.RedTeam.Batch53.actual_walk_block_commutes
#print axioms Nock.RedTeam.Batch53.actual_finite_io_block_commutes
#print axioms Nock.RedTeam.Batch53.actual_folded_io_gate_commutes
#print axioms Nock.RedTeam.Batch53.remaining_block_degree_census
#print axioms Nock.RedTeam.Batch53.scope_guard_alias
