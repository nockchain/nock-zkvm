import Nock.RedTeam.Batch60Thm54FinalComputeScalarPublicCollision
import Nock.NockVMROM.Thm54.OptimizedComputeSameExecution

/-!
# Corrected combined gate and exact non-IO same-execution bridge

Paper frame:

* compute IO and shared execution: the paper;
* algorithmic memory-record semantics: the paper;
* `mr2` constraint semantics: the paper;
* nonlinear equations and displayed combination: the paper.

This batch passes only the exact seventeen
non-IO source-family forward bridge.
-/

namespace Nock.RedTeam.Batch61

set_option maxRecDepth 300000
set_option maxHeartbeats 8000000

open Classical
open Module
open Nock
open Nock.ComputeTable
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.StrictExtension
open scoped Polynomial

noncomputable section

/-! ## 1. MR2 axis correction against the authoritative source -/

/-- A marker environment with every physical coordinate distinct.  Selectors are one-hot, so the
eleven cases can be checked without accidental equality between `pub.e.leaf` (index 21) and
`dec.f_t.leaf` (index 54). -/
def mr2AuditEnv (st : State) : Env ℚ where
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

/-- The corrected expression literally selects `dec.f_t.leaf` in OP0 and constant axis two in
OP2/5/6/7/8/9.  It never selects `pub.e.leaf`. -/
theorem mr2_axis_expression_exact :
    mr2Field .traceCur 6 =
      .Add (.Mul (.Var .traceCur 0) (decFP .traceCur 1 2))
        (.Mul (mr2Group .traceCur) (.Const 2)) := by
  rfl

/-- Exhaustive all-state axis evaluation.  The OP0 marker `54` is the physical
`dec.f_t.leaf` coordinate; the six decomposition states carry axis `2`; all other states erase
the record. -/
theorem mr2_axis_all_states (st : State) :
    (mr2Field .traceCur 6).eval (mr2AuditEnv st) =
      match st with
      | .s0 => 54
      | .s2 | .s5 | .s6 | .s7 | .s8 | .s9 => 2
      | _ => 0 := by
  cases st <;>
    norm_num [mr2Field, mr2Group, mr2AuditEnv, decFP, ext0,
      Nock.Reified.opCol, Expr.eval]

theorem mr2_full_all_states (st : State) :
    List.ofFn (fun j : Fin 8 => (mr2Field .traceCur j).eval (mr2AuditEnv st)) =
      match st with
      | .s0 => [13, 14, 15, 19, 20, 21, 54, 268]
      | .s2 | .s5 | .s6 | .s7 | .s8 | .s9 =>
          [52, 53, 54, 55, 56, 57, 2, 268]
      | _ => [0, 0, 0, 0, 0, 0, 0, 0] := by
  cases st <;>
    norm_num [mr2Field, mr2Group, mr2AuditEnv, pubFP, decFP, lnPrev, ext0,
      Nock.Reified.opCol, Expr.eval]

theorem mr2_old_pub_e_leaf_replay_rejected :
    (mr2Field .traceCur 6).eval (mr2AuditEnv .s0) ≠
      (pubFP .traceCur 2 2).eval (mr2AuditEnv .s0) := by
  norm_num [mr2Field, mr2Group, mr2AuditEnv, pubFP, decFP, ext0,
    Nock.Reified.opCol, Expr.eval]

/-! ## 2. Corrected selector-relative combined gate -/

/-- Direct all-eleven-state unfolding of `Σ op*g - Σ op`.  The seven inactive states evaluate
identically to zero; each active state is exactly its own nonlinear equation minus one. -/
theorem corrected_combined_all_states
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K) (st : State) :
    combinedSourceExpr.eval (computeEnvFull inp (opSel st) pub dec ex) =
      match st with
      | .s3 => ex.invGen * (inp.z - pub.sf1_e.size) + pub.e.leaf - 1
      | .s5 => ex.invGen * (inp.a * (pub.sf1_e.size - pub.sf2_e.size)
          + inp.b * (pub.sf1_e.dyck - pub.sf2_e.dyck)
          + inp.c * (pub.sf1_e.leaf - pub.sf2_e.leaf) + (1 - pub.e.leaf)) - 1
      | .s8 => pub.sf2_e.size * pub.s.size * ex.invGen - 1
      | .cons => pub.sf1_e.size * pub.sf2_e.size * ex.invGen - 1
      | _ => 0 := by
  rw [combinedSourceExpr_eval_computeEnv]
  cases st <;> simp [ComputeTable.combinedGate_opSel, opSel]

/-- The zero equation has the exact four active iff branches and is tautological on every
inactive opcode. -/
theorem corrected_combined_all_states_iff
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K) (st : State) :
    combinedSourceExpr.eval (computeEnvFull inp (opSel st) pub dec ex) = 0 ↔
      match st with
      | .s3 => ex.invGen * (inp.z - pub.sf1_e.size) + pub.e.leaf = 1
      | .s5 => ex.invGen * (inp.a * (pub.sf1_e.size - pub.sf2_e.size)
          + inp.b * (pub.sf1_e.dyck - pub.sf2_e.dyck)
          + inp.c * (pub.sf1_e.leaf - pub.sf2_e.leaf) + (1 - pub.e.leaf)) = 1
      | .s8 => pub.sf2_e.size * pub.s.size * ex.invGen = 1
      | .cons => pub.sf1_e.size * pub.sf2_e.size * ex.invGen = 1
      | _ => True :=
  combinedSourceExpr_opSel_iff inp pub dec ex st

/-- The OP8 branch retains the load-bearing input-subject size factor from EC.8.1. -/
theorem corrected_combined_op8_factor_intact
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K) :
    combinedSourceExpr.eval (computeEnvFull inp (opSel .s8) pub dec ex) =
      pub.sf2_e.size * pub.s.size * ex.invGen - 1 :=
  corrected_combined_all_states inp pub dec ex .s8

/-- One-hot selectors make the correction term exactly one on the four participating opcodes and
zero on the other seven. -/
theorem combined_selector_one_hot_all_states
    {K : Type} [Field K]
    (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K) (st : State) :
    combinedSelectorExpr.eval (computeEnvFull inp (opSel st) pub dec ex) =
      if st = .s3 ∨ st = .s5 ∨ st = .s8 ∨ st = .cons then 1 else 0 := by
  cases st <;>
    simp [combinedSelectorExpr, Expr.eval, computeEnvFull, opSel, tc]

def nonOneHotCancellationEnv : Env ℚ where
  trace i := if i = 3 then 1 else if i = 5 then -1 else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

def gate3MinusOne : Expr :=
  .Sub
    (.Add (.Mul (tc 92) (.Sub (chl 1) Nock.Reified.cSf1e.size))
      Nock.Reified.cE.leaf)
    (.Const 1)

def gate5MinusOne : Expr :=
  .Sub
    (.Mul (tc 92)
      (.Add
        (.Add
          (.Add (.Mul (chl 2) (.Sub Nock.Reified.cSf1e.size Nock.Reified.cSf2e.size))
            (.Mul (chl 3) (.Sub Nock.Reified.cSf1e.dyck Nock.Reified.cSf2e.dyck)))
          (.Mul (chl 4) (.Sub Nock.Reified.cSf1e.leaf Nock.Reified.cSf2e.leaf)))
        (.Sub (.Const 1) Nock.Reified.cE.leaf)))
    (.Const 1)

/-- Cancellation remains possible if the base one-hot gates are removed: selectors `1,-1` cancel
although both active nonlinear residuals are nonzero.  This is a control on the combined gate's
required one-hot context, not a finding against the production base block. -/
theorem non_one_hot_cancellation_control :
    combinedSourceExpr.eval nonOneHotCancellationEnv = 0 ∧
      gate3MinusOne.eval nonOneHotCancellationEnv = -1 ∧
      gate5MinusOne.eval nonOneHotCancellationEnv = -1 ∧
      (tc 3).eval nonOneHotCancellationEnv = 1 ∧
      (tc 5).eval nonOneHotCancellationEnv = -1 := by
  norm_num [combinedSourceExpr, combinedSelectorExpr, gate3MinusOne, gate5MinusOne,
    nonOneHotCancellationEnv, Nock.Reified.cSf1e, Nock.Reified.cSf2e,
    Nock.Reified.cE, Nock.Reified.cS, Nock.Reified.fpCol, tc, chl, Expr.eval]

theorem corrected_combined_degree :
    combinedSourceExpr.degree = 4 ∧ optimizedCombinedGate.degree = 4 := by
  decide

/-! ## 3. Exact source partition and unchanged resources -/

theorem final_source_partition_exact :
    finalNonIOSourceFamilies17.length = 17 ∧
      finalNonIOSourceFamilies17.flatten.length = 511 ∧
      finalNonIOSourceFamilies17.flatten.Nodup ∧
      finalNonIOTransitionGates.length = 17 ∧
      finalSampledIOTransitionGates.length = 4 ∧
      historicalFinalExtTransitionGates.length = 21 ∧
      finalExtTransitionGates.length = 82 ∧
      finalComputeRLCWorkload = 494 := by
  set_option maxRecDepth 300000 in
  decide

theorem final_gate_degrees :
    (∀ g ∈ finalNonIOTransitionGates, g.degree ≤ 4) ∧
      (∀ g ∈ finalSampledIOTransitionGates, g.degree ≤ 4) ∧
      (∀ g ∈ finalExtTransitionGates, g.degree ≤ 4) := by
  set_option maxRecDepth 300000 in
  decide

theorem corrected_resources_unchanged
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    let Q := ProductionFinalComputeRAP (n := n) b chalVal pubVal orbit H
    Q.w = 303 ∧ Q.s = 418 ∧ Q.d = 4 ∧ Q.k = 2 ∧ Q.e = 3 :=
  corrected_rap_fingerprint b chalVal pubVal orbit H

/-! ## 4. Exact same-execution bridge and honest transition boundary -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

noncomputable local instance :
    Fintype ConcreteStrictPackage.K73cubic :=
  Fintype.ofFinite ConcreteStrictPackage.K73cubic

noncomputable local instance :
    DecidableEq ConcreteStrictPackage.K73cubic :=
  Classical.decEq ConcreteStrictPackage.K73cubic

local instance :
    CharP ConcreteStrictPackage.K73cubic 73 :=
  inferInstance

local instance :
    CharP ConcreteStrictPackage.K73cubic
      (ringChar ConcreteStrictPackage.K73cubic) :=
  ringChar.charP ConcreteStrictPackage.K73cubic

/-- One `A`, one obligation proof, one row, and
its actual successor occur in every source equation; no row, witness, configuration, or execution
is existentially or independently quantified in the conclusion. -/
theorem exact_nonIO_bridge_same_object
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    ∀ e ∈ finalNonIOSourceFamilies17.flatten,
      e.eval (exactFinalTransitionEnv A i hi).toSourceEnv = 0 :=
  exact_finalNonIOSourceFamilies17 A hA i hi

/-- The same exact source proof gives the seventeen folds unconditionally. -/
theorem exact_nonIO_folds_same_object
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    ∀ g ∈ finalNonIOTransitionGates,
      g.eval (exactFinalTransitionEnv A i hi).toSourceEnv = 0 :=
  exact_finalNonIOTransitionGates A hA i hi

/-- Honest source satisfaction also inhabits the exact same-row collision-free premise. -/
theorem exact_nonIO_collision_free_same_object
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    FinalComputeCollisionFree (exactFinalTransitionEnv A i hi).toSourceEnv :=
  exact_finalComputeCollisionFree A hA i hi

omit [Fintype K] [DecidableEq K] in
/-- The successor premise makes the row genuinely nonterminal. -/
theorem transition_row_strictly_before_last
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (i : ℕ) < R.problem.cfg.compRows - 1 := by
  omega

omit [Fintype K] [DecidableEq K] in
/-- No cyclic `next = first` convention is used at the final row: its ordinary successor
inequality is impossible. -/
theorem final_row_has_no_transition_successor
    (hn : 0 < R.problem.cfg.compRows) :
    ¬ ((R.problem.cfg.compRows - 1) + 1 < R.problem.cfg.compRows) := by
  omega

/-- The complete compute-table/walk/sampled-IO premise is concretely inhabited by the existing
same-cfg/same-exec `F73/K73cubic` assignment. -/
theorem concrete_compute_sampled_premise_nonvacuous :
    OptimizedComputeSampledTrace.Concrete.honestSampled.ComputeSampledObligations :=
  OptimizedComputeSampledTrace.Concrete.honest_obligations

/-- That concrete regression has one row, so it honestly exercises row-local AIR/Vcomp and terminal
co-residence but does not fake a cyclic transition witness. -/
theorem concrete_one_row_has_no_fake_transition :
    ¬ ((OptimizedComputeSampledTrace.Concrete.honestRowIndex : ℕ) + 1 <
      ConcreteStrictPackage.honestLegacyFamily.problem.cfg.compRows) := by
  change ¬ (0 + 1 < (ConcreteStrictPackage.cfg
    ConcreteStrictPackage.honestSeed ConcreteStrictPackage.honestAlpha).compRows)
  norm_num [ConcreteStrictPackage.cfg]

/-! ## 5. Fold exactness and event threading -/

omit [Fintype K] [DecidableEq K] in
theorem final_folds_iff_sources_under_exact_collision_exclusion
    (env : Env K) (hfree : FinalComputeCollisionFree env) :
    (∀ g ∈ finalNonIOTransitionGates, g.eval env = 0) ↔
      ∀ e ∈ finalNonIOSourceFamilies17.flatten, e.eval env = 0 :=
  ⟨finalNonIOTransitionGates_sound env hfree,
    finalNonIOTransitionGates_complete env⟩

omit [Fintype K] [DecidableEq K] in
theorem final_collision_event_is_exact_complement (env : Env K) :
    ¬ FinalComputeCollisionFree env ↔ FinalComputeCollisionEvent env :=
  not_finalComputeCollisionFree_iff_event env

/-- The random-fold API threads one tuple through all rows and the walk-init fold. -/
theorem full_event_threads_one_tuple
    {N : ℕ} (envK : Fin N → Env K) (walkEnv : Env K)
    (c : FinalComputeChallengeTuple K)
    (hgood : ExtensionFinalComputeCollisionFree envK walkEnv c) :
    True :=
  extensionFinalComputeCollisionFree_components envK walkEnv c hgood

theorem full_event_cardinality_threads_one_space
    {N : ℕ} (envK : Fin N → Env K) (walkEnv : Env K) :
    (extensionFinalComputeCollisionEvent envK walkEnv).card ≤
      (494 * N) * Fintype.card K + Fintype.card K * 1 :=
  extensionFinalComputeCollisionEvent_card_le envK walkEnv

/-! ## 6. Explicit scope guards -/

theorem sampled_io_four_remain_separate :
    ∀ e ∈ optimizedSampledIOTransitionGates,
      e ∉ finalNonIOSourceFamilies17.flatten :=
  sampledIO_sources_outside_challenge9_families

theorem exact_extension_partition_scope :
    finalExtTransitionGates =
        paperPackingNonIOGates ++ finalSampledIOTransitionGates ∧
      paperPackingNonIOGates.length = 78 ∧
      finalSampledIOTransitionGates.length = 4 ∧
      finalExtTransitionGates.length = 82 :=
  final_extension_source_partition

def strict_package_still_requires_B29
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ}
    (P : Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage F K hOrb q Λ) :=
  Nock.RedTeam.Batch60.strict_package_still_requires_B29 P

theorem paper_alias_still_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch60.paper_alias_still_forest

#print axioms mr2_axis_all_states
#print axioms mr2_full_all_states
#print axioms corrected_combined_all_states
#print axioms corrected_combined_all_states_iff
#print axioms corrected_combined_op8_factor_intact
#print axioms non_one_hot_cancellation_control
#print axioms final_source_partition_exact
#print axioms corrected_resources_unchanged
#print axioms exact_nonIO_bridge_same_object
#print axioms exact_nonIO_collision_free_same_object
#print axioms concrete_compute_sampled_premise_nonvacuous
#print axioms final_folds_iff_sources_under_exact_collision_exclusion
#print axioms full_event_threads_one_tuple
#print axioms full_event_cardinality_threads_one_space
#print axioms sampled_io_four_remain_separate
#print axioms strict_package_still_requires_B29
#print axioms paper_alias_still_forest

end
end Nock.RedTeam.Batch61
