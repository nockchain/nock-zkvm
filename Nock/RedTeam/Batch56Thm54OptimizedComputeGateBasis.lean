import Nock.RedTeam.Batch55Thm54InactiveSafeSampledIO
import Nock.NockVMROM.Thm54.OptimizedComputeTemplate

/-!
Its two findings apply to
the retired untyped `ChipTemplate` assembly and incomplete 510-equation source partition:

* In particular the
  first non-IO gate reads index 68, which coordinate-expands from column 217 while the cubic
  template width is only 187.

Production now uses typed `Fin 13` / `Fin 58` lowering, a dedicated coordinate compiler, a
511-equation source partition, and a restored terminal endpoint.
-/

namespace Nock.RedTeam.Batch56

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedComputeRowSemantics
open Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates

deriving instance DecidableEq for Expr
deriving instance DecidableEq for CoeffExpr

/-! ## 1. Exact IDs, lists, cardinalities, duplicate bodies, and degrees -/

theorem exact_base13_ext21_census :
    allBaseGateIds.length = 13 ∧
      allBaseGateIds.Nodup ∧
      allExtGateIds.length = 21 ∧
      allExtGateIds.Nodup ∧
      (baseTransitionGates (F := ℚ)).length = 13 ∧
      extTransitionGates.length = 21 ∧
      nonIOTransitionGates.length = 17 ∧
      optimizedSampledIOTransitionGates.length = 4 :=
  ⟨allBaseGateIds_length, allBaseGateIds_nodup,
    allExtGateIds_length, allExtGateIds_nodup,
    baseTransitionGates_length, extTransitionGates_length,
    nonIOTransitionGates_length, optimizedSampledIOTransitionGates_length⟩

theorem no_duplicate_gate_bodies :
    (baseTransitionGates (F := ℚ)).Nodup ∧ extTransitionGates.Nodup := by
  decide

theorem every_gate_body_syntactically_nonzero :
    (∀ g ∈ (baseTransitionGates (F := ℚ)), g ≠ .const 0) ∧
      (∀ g ∈ extTransitionGates, g ≠ (.Const 0 : Expr)) :=
  ⟨baseTransitionGates_nonzero, extTransitionGates_nonzero⟩

theorem every_gate_body_has_degree_at_most_four :
    (∀ g ∈ (baseTransitionGates (F := ℚ)), g.degree ≤ 4) ∧
      (∀ g ∈ extTransitionGates, g.degree ≤ 4) :=
  ⟨baseTransitionGates_degree, extTransitionGates_degree⟩

/-! ## 2. Exact source partition and RLC cancellation control -/

def stateBlocks : List Expr :=
  [stateBlock .s0, stateBlock .s1, stateBlock .s2, stateBlock .s3,
    stateBlock .s4, stateBlock .s5, stateBlock .s6, stateBlock .s7,
    stateBlock .s8, stateBlock .s9, stateBlock .cons].flatten

def historicalSourceFamilies20 : List (List Expr) :=
  [[sv4Expr.subst computeSubst],
   [sv5Expr.subst computeSubst],
   [sv6Expr.subst computeSubst],
   formulaExprs.map (fun e => e.subst computeSubst),
   [zZinvExpr.subst computeSubst],
   [Trans.lnChainExpr.subst computeSubst],
   [Trans.walkLnStep.subst walkSubst],
   [Trans.walkCountStep.subst walkSubst],
   [Trans.walkAccStep.subst walkSubst],
   stateBlock .s0, stateBlock .s1, stateBlock .s2, stateBlock .s3,
   stateBlock .s4, stateBlock .s5, stateBlock .s6, stateBlock .s7,
   stateBlock .s8, stateBlock .s9, stateBlock .cons]

def historicalNonIOSourceFamilies17 : List (List Expr) :=
  [(stateBlock .s0 ++ stateBlock .s1),
   (stateBlock .s2 ++ stateBlock .s3),
   (stateBlock .s4 ++ stateBlock .s5),
   [sv4Expr.subst computeSubst],
   [sv5Expr.subst computeSubst],
   [sv6Expr.subst computeSubst],
   formulaExprs.map (fun e => e.subst computeSubst),
   [zZinvExpr.subst computeSubst],
   [Trans.lnChainExpr.subst computeSubst],
   [Trans.walkLnStep.subst walkSubst],
   [Trans.walkCountStep.subst walkSubst],
   [Trans.walkAccStep.subst walkSubst],
   stateBlock .s6, stateBlock .s7, stateBlock .s8, stateBlock .s9,
   stateBlock .cons]

def historicalNonIOTransitionGates : List Expr :=
  historicalNonIOSourceFamilies17.map rlcFold

def historicalExtTransitionGates : List Expr :=
  historicalNonIOTransitionGates ++ optimizedSampledIOTransitionGates

theorem exact_source_partition :
    Nock.Reified.perStateGated.length = 499 ∧
      refoldedPerStateGates.length = 499 ∧
      stateBlocks = refoldedPerStateGates ∧
      historicalSourceFamilies20.flatten.length = 510 ∧
      historicalNonIOSourceFamilies17.flatten.length = 510 ∧
      historicalSourceFamilies20.flatten.Nodup ∧
      historicalNonIOSourceFamilies17.flatten.Nodup := by
  decide

theorem pair_folds_preserve_declared_membership (e : Expr) :
    e ∈ historicalNonIOSourceFamilies17.flatten ↔
      e ∈ historicalSourceFamilies20.flatten := by
  simp [historicalNonIOSourceFamilies17, historicalSourceFamilies20]
  aesop

theorem cancellation_is_a_real_required_premise :
    (rlcFold [.Const 1, .Const (-1)]).eval cancellationEnv = 0 ∧
      ¬ (∀ e ∈ ([.Const 1, .Const (-1)] : List Expr),
        e.eval cancellationEnv = 0) :=
  cancellation_counterexample

/-! ## 3. Finding B56-F1: the mixed 13/58 support does not fit `ChipTemplate.col0` -/

def ExtensionSupportFits58 (e : Expr) : Prop :=
  ∀ x ∈ e.vars,
    match x.1 with
    | .traceCur | .traceNext => x.2 < 58
    | .challenge | .publicVal => True

theorem first_nonIO_gate_reads_mixed_index_68 :
    (.traceCur, 68) ∈
      (historicalNonIOTransitionGates.get ⟨0, by decide⟩).vars := by
  decide

theorem first_nonIO_gate_does_not_fit_58_extension_columns :
    ¬ ExtensionSupportFits58
      (historicalNonIOTransitionGates.get ⟨0, by decide⟩) := by
  intro h
  have h68 := h (.traceCur, 68) first_nonIO_gate_reads_mixed_index_68
  norm_num at h68

def index68MutationEnv (v : ZMod 73) : Env (ZMod 73) where
  trace i := if i = 0 then 1 else if i = 68 then v else 0
  traceNext := fun _ => 0
  chal i := if i = 8 then 2 else 0
  pub := fun _ => 0

theorem index68_is_semantically_load_bearing_in_first_gate :
    (historicalNonIOTransitionGates.get ⟨0, by decide⟩).eval
        (index68MutationEnv 0) = 0 ∧
      (historicalNonIOTransitionGates.get ⟨0, by decide⟩).eval
        (index68MutationEnv 1) = 55 := by
  decide

def historicalCol0 (e : ℕ) (kind : VarKind) (i : ℕ) : ℕ :=
  match kind with
  | .traceCur | .traceNext => 13 + e * i
  | .challenge | .publicVal => 0

theorem concrete_compiler_index_exceeds_cubic_width :
    historicalCol0 3 .traceCur 68 = 217 ∧
      13 + 58 * 3 = 187 ∧
      ¬ historicalCol0 3 .traceCur 68 < 13 + 58 * 3 := by
  decide

theorem out_of_width_compiled_projection_reifies_to_zero :
    coeffToMv (w := 187) (fun _ => (0 : ℚ)) (fun _ => 0)
      (.var .traceCur 217 : CoeffExpr ℚ) = 0 := by
  simp [coeffToMv]

/-! ## 4. Finding B56-F2: the complete-row/template lists omit `walkOut` -/

def historicalOptimizedWalkLn1 : Expr := Trans.walkLn1.subst walkSubst
def historicalOptimizedWalkCount1 : Expr := Trans.walkCount1.subst walkSubst
def historicalOptimizedWalkAccInit : Expr := Trans.walkAccInit.subst walkSubst
def historicalOptimizedWalkOut : Expr := Trans.walkOut.subst walkSubst

theorem walkOut_is_a_real_walk_source_gate :
    Trans.walkOut ∈
      [Trans.walkLnStep, Trans.walkCountStep, Trans.walkAccStep,
        Trans.walkLn1, Trans.walkCount1, Trans.walkAccInit, Trans.walkOut] := by
  simp

theorem completeSourceRow_declared_nonIO_list_omits_walkOut :
    historicalOptimizedWalkOut ∉ historicalSourceFamilies20.flatten := by
  decide

theorem declared_nonIO_list_omits_named_combined_equation :
    Nock.RedTeam.Batch53.combinedSourceExpr.subst computeSubst ∉
      historicalSourceFamilies20.flatten := by
  decide

theorem concrete_template_omits_walkOut :
    historicalOptimizedWalkOut ∉ historicalExtTransitionGates ∧
      historicalOptimizedWalkOut ∉
        [historicalOptimizedWalkLn1, historicalOptimizedWalkCount1] ∧
      historicalOptimizedWalkOut ∉ [historicalOptimizedWalkAccInit] := by
  decide

theorem row_semantics_is_row_local_not_independently_quantified :
    ∀ (envF envF' : Env ℚ) (envK envK' : Env ℚ),
      envF = envF' → envK = envK' →
      (RowTransitionSat envF envK ↔ RowTransitionSat envF' envK') := by
  rintro envF envF' envK envK' rfl rfl
  exact Iff.rfl

/-! ## 5. Structural summary and actual template/padding counts -/

theorem base_summary_is_exactly_load_bearing_under_its_premise
    (env : Env ℚ) (hfree : SummaryCollisionFree env) :
    summaryFold.eval env = 0 ↔
      fanoutPin.eval env = 0 ∧ recordCountPin.eval env = 0 :=
  summaryFold_zero_iff env hfree

def baseWitnessEnv : Env ℚ where
  trace i := if i = 1 then 1 else if i = 12 then 1 else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

private theorem range11 :
    List.range 11 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  decide

theorem base13_collision_premise_nonvacuous :
    SummaryCollisionFree baseWitnessEnv ∧
      ∀ g ∈ (baseTransitionGates (F := ℚ)), g.eval baseWitnessEnv = 0 := by
  constructor
  · intro h
    norm_num [fanoutPin, recordCountPin, expectedSummary, Nock.Reified.allStates,
      Nock.Reified.opCol, Nock.ComputeTable.fanoutComp, Nock.Framework.recordCount,
      CoeffExpr.sumList, bv, baseWitnessEnv, CoeffExpr.eval]
  · intro g hg
    simp only [baseTransitionGates, List.mem_append, List.mem_map, List.mem_range,
      List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with ⟨i, hi, rfl⟩ | rfl | rfl
    · interval_cases i <;>
        norm_num [selectorBool, bv, baseWitnessEnv, CoeffExpr.eval]
    · simp only [selectorOneHot, CoeffExpr.eval, sub_eq_zero]
      unfold selectorSum
      rw [CoeffExpr.eval_sumList, range11]
      norm_num [bv, baseWitnessEnv, CoeffExpr.eval]
    · norm_num [summaryFold, fanoutPin, recordCountPin, expectedSummary,
        Nock.Reified.allStates, Nock.Reified.opCol, Nock.ComputeTable.fanoutComp,
        Nock.Framework.recordCount, CoeffExpr.sumList, bv, baseWitnessEnv,
        CoeffExpr.eval]

theorem actual_template_and_padding_counts :
    (compOptimizedTemplate ℚ).rounds = 2 ∧
      (compOptimizedTemplate ℚ).baseCols = 13 ∧
      (compOptimizedTemplate ℚ).extCols = 58 ∧
      (compOptimizedTemplate ℚ).baseTransition.length = 13 ∧
      (compOptimizedTemplate ℚ).extTransition.length = 21 ∧
      (compOptimizedTemplate ℚ).extDeg1.length = 2 ∧
      (compOptimizedTemplate ℚ).extDeg3.length = 1 ∧
      (compOptimizedTemplate ℚ).equalityChecks.length = 2 ∧
      (compOptimizedTemplate ℚ).width 3 = 187 ∧
      (compOptimizedTemplate ℚ).baseTransition.length +
          (compOptimizedTemplate ℚ).extTransition.length * 3 = 76 ∧
      (compOptimizedTemplate ℚ).baseTransition.length +
          (compOptimizedTemplate ℚ).extTransition.length * 3 +
          (compOptimizedTemplate ℚ).extDeg1.length * 3 +
          (compOptimizedTemplate ℚ).extDeg3.length * 3 +
          (compOptimizedTemplate ℚ).equalityChecks.length = 87 := by
  exact ⟨compOptimizedTemplate_shape.1,
    compOptimizedTemplate_shape.2.1,
    compOptimizedTemplate_shape.2.2.1,
    compOptimizedTemplate_shape.2.2.2.1,
    compOptimizedTemplate_shape.2.2.2.2.1,
    compOptimizedTemplate_shape.2.2.2.2.2.1,
    compOptimizedTemplate_shape.2.2.2.2.2.2.1,
    compOptimizedTemplate_shape.2.2.2.2.2.2.2,
    compOptimizedTemplate_cubic_counts.1,
    compOptimizedTemplate_cubic_counts.2.1,
    compOptimizedTemplate_cubic_counts.2.2⟩

#print axioms exact_base13_ext21_census
#print axioms no_duplicate_gate_bodies
#print axioms exact_source_partition
#print axioms first_nonIO_gate_does_not_fit_58_extension_columns
#print axioms index68_is_semantically_load_bearing_in_first_gate
#print axioms concrete_compiler_index_exceeds_cubic_width
#print axioms out_of_width_compiled_projection_reifies_to_zero
#print axioms completeSourceRow_declared_nonIO_list_omits_walkOut
#print axioms declared_nonIO_list_omits_named_combined_equation
#print axioms concrete_template_omits_walkOut
#print axioms base13_collision_premise_nonvacuous
#print axioms actual_template_and_padding_counts

end Nock.RedTeam.Batch56
