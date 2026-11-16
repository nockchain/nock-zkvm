import Nock.NockVMROM.Thm54.OptimizedStrictFullPackageConcrete
import Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
import Nock.RedTeam.Batch66Thm54OptimizedStrictPackage

/-!
Receipts for the optimized strict full NockVMROM package: the full statement is determined by its fields and is built from one package, all components share the same package objects, resources and row budgets are projections of the package, and false acceptance is exactly acceptance with failure of the genuine target. Attack lemmas show trace and challenge substitution cannot detach acceptance, and concrete F73 and F97 fixtures (including a nonterminal OP4/OP1 execution) exercise the statements.
-/
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54


namespace Nock.RedTeam.Batch67

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage

noncomputable section

open Nock.NockVMROM.Thm54.ConcreteStrictPackage

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-! ## Full statement shape and same-object threading -/

/-- The full statement is determined by its fourteen fields. -/
theorem full_capstone_reconstructs_from_fourteen_fields
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} {P : OptimizedFullStrictNockVMROMPackage F K hOrb}
    (S : OptimizedFullStrictThm54Statement P) :
    S =
      { structural := S.structural
        optimized_chips := S.optimized_chips
        shared_io := S.shared_io
        perfect_completeness := S.perfect_completeness
        containment := S.containment
        walk_bounds := S.walk_bounds
        p8_fixed_field_soundness := S.p8_fixed_field_soundness
        p8_fixed_field_bits := S.p8_fixed_field_bits
        acceptance_to_target := S.acceptance_to_target
        complete_false_acceptance_bound := S.complete_false_acceptance_bound
        complete_false_acceptance_bits := S.complete_false_acceptance_bits
        staged_false_acceptance_bound := S.staged_false_acceptance_bound
        exact_resources := S.exact_resources
        row_budgets := S.row_budgets
        shared_forest_axis := S.shared_forest_axis } := by
  cases S
  rfl

/-- The field-map surface is obtained from a single package. -/
theorem historical_nonB29_surface_is_one_package
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    HistoricalNonB29FieldMap P :=
  full_statement_field_map (optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth)

/-- Configuration, dependent execution, walk family, sampled records, and exported IO meet at the
same package objects; no independently quantified execution is introduced. -/
theorem package_object_identity_receipt
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    P.optimized.family.problem.cfg = P.objects.cfg ∧
      HEq P.optimized.family.problem.exec P.objects.exec ∧
      P.walkFamily.problem = ⟨P.objects.cfg, P.objects.exec⟩ ∧
      P.ioStrategy.records.requests = P.objects.reqRecs ∧
      P.ioStrategy.records.responses = P.objects.respRecs ∧
      IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs :=
  ⟨P.optimized.family_cfg, P.optimized.family_exec, P.walkFamily_problem,
    P.io_requests, P.io_responses, P.shared_io⟩

/-- Exact optimized widths, constraints, degrees, rounds, fingerprints, and raw RAP-domain row
budgets are all projections of the same package. -/
theorem exact_resource_and_raw_budget_receipt
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    P.computeChip.rap.w = 303 ∧ P.computeChip.rap.s = 418 ∧
      P.computeChip.rap.d = 4 ∧ P.computeChip.rap.k = 2 ∧
      P.memoryChip.rap.w = 205 ∧ P.memoryChip.rap.s = 156 ∧
      P.memoryChip.rap.d = 4 ∧ P.memoryChip.rap.k = 1 ∧
      P.computeChip.rap.s - 44 = 374 ∧ P.memoryChip.rap.s - 0 = 156 ∧
      P.computeChip.rap.H.card = P.objects.cfg.compRows ∧
      P.memoryChip.rap.H.card =
        RowLayout.memoryM P.objects.exec + 2 * RowLayout.memoryL P.objects.exec := by
  have h := P.optimizedFullCostRealization
  -- `OptimizedFullCostRealization` states the counts as affine functions of the chip's recorded
  -- extension degree `e`; `cost_realization_deployed_numerals` reads the deployed `e = 3` numerals off it.
  have hnum := P.cost_realization_deployed_numerals h
  exact ⟨hnum.1.1, hnum.1.2.1, hnum.1.2.2.1, hnum.1.2.2.2,
    hnum.2.1.1, hnum.2.1.2.1, hnum.2.1.2.2.1, hnum.2.1.2.2.2,
    hnum.2.2.1, hnum.2.2.2, h.compute_row_budget, h.memory_row_budget⟩

/-! ## Event completeness and parameter-substitution attacks -/

/-- The false-acceptance set is definitionally acceptance and failure of the genuine target for
the same traces and challenge tuple. -/
theorem false_acceptance_membership_exact
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    c ∈ P.OptimizedFalseAcceptanceSet Qc Qm ↔
      P.OptimizedProductionAcceptanceAt Qc Qm c ∧
        ¬ P.OptimizedProductionGenuineTargetAt Qc Qm c := by
  simp [OptimizedFullStrictNockVMROMPackage.OptimizedFalseAcceptanceSet]

/-- Outside the declared lifted union means all four components are good on the exact environments
derived from the accepted traces.

It used to be
`c.2.2.1 ∉ FullFinalComputeCollisionEvent …`; since stage 3e the failure union's compute summand
is `extensionFinalComputeCollisionEvent` — the two `𝕂` lifts alone — because the de-compressed
endpoint equality checks determine the column-vs-public equalities with no coin
(`OptimizedComputeFinal.endpointEqualityChecks_determine_public`).  The bridge in the other
direction is `extensionFinalComputeCollisionEvent_subset_full`.

It used to be
`c.2.2.2 ∉ fullMemoryCollisionEvent …`.  Since stage 3c the failure union's memory summand is
`extensionMemoryCollisionEvent` — the extension-fold lift alone — so being outside the union no
longer excludes the four base-field mask/chain/selector collisions, and the old statement is not
a corollary of the new one.

**Stage 3d closed the question**: `MemoryChallengeTuple` no longer has those four
coordinates, so `fullMemoryCollisionEvent` and the `extensionMemoryCollisionEvent_subset_full`
bridge are both gone, and there is nothing left for the old reading to be a statement about. -/
theorem outside_union_exports_all_four_components
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : c ∉ P.optimizedFailureEvent Qc Qm) :
    c.1 ∉ FailureUnion P.strategy P.optimized.census P.objects.cfg.challenges.lam ∧
      c ∉ P.famIOEventOf Qc Qm ∧
      c.2.2.1 ∉ extensionFinalComputeCollisionEvent
        (P.computeSourceEnv Qc) (P.computeWalkEnv Qc) ∧
      c.2.2.2 ∉ extensionMemoryCollisionEvent (P.memorySourceEnv Qm) := by
  -- The IO component is the family IO event.
  have hc := P.optimizedFailureEvent_good_components Qc Qm c h
  exact ⟨hc.1, hc.2.1,
    (by simp [extensionFinalComputeCollisionEvent] :
      c.2.2.1 ∉ extensionFinalComputeCollisionEvent
        (P.computeSourceEnv Qc) (P.computeWalkEnv Qc)),
    (by simp [extensionMemoryCollisionEvent] :
      c.2.2.2 ∉ extensionMemoryCollisionEvent (P.memorySourceEnv Qm))⟩

theorem acceptance_pins_exact_traces
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : P.OptimizedProductionAcceptanceAt Qc Qm c) :
    RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (P.familyQc c Qc) ∧
      RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (P.familyQm c Qm) :=
  ⟨h.compute_satisfies, h.memory_satisfies⟩

/-- Challenge substitution cannot detach the tuple from sampled IO or the compute coordinates. -/
theorem acceptance_pins_exact_challenges
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    c.2.1 =
        (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole) :=
  h.sampled_io_coins

/-- The normalized mixed-denominator expression is exactly the recorded
`K`, `K²`, and `F` workload formula. -/
theorem mixed_denominator_formula_exact
    (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedProductionFailureProbabilityBound cardK cardF p8Work ioWork N M =
      (p8Work + 494 * N + 1 + 61 * M : ℚ) / cardK +
        (ioWork : ℚ) / cardK ^ 2 +
        (20 + 14 * M : ℚ) / cardF :=
  rfl

/-! ## Concrete F73 non-vacuity on the exact production connective -/

open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.Concrete

/-! ## F97 nonterminal decode and substitution resistance -/

namespace Nonterminal

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.Framework Nock.Framework.Thm54 Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.Reified
open Module
open CoordinateBasis
open StrictExtension
open OptimizedComputeCanonicalSatisfaction
open OptimizedComputeCollisionBound
open OptimizedComputeCorrectedFinal
open OptimizedComputeFinalTrace
open OptimizedComputeGateBasis
open OptimizedComputeSameExecution
open OptimizedComputeSemanticRealization
open OptimizedComputeSampledTrace

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-- The row/config/trace substitution attack fails at the concrete fixture: row zero and its
successor are distinct indices and use distinct orbit nodes. -/
theorem row_index_substitution_rejected :
    row0 ≠ row0Next ∧ computeNodes97 row0 ≠ computeNodes97 row0Next := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp [row0, row0Next] at hv
  · change (1 : F97) ≠ 6
    decide

/-- Full same-execution nonterminal receipt: accepted OP4/s4 is linked to accepted OP1/s1; exact
distinct requests equal exact memory responses; finite sampled IO uses that same execution; the
corrected 199/98 fixed-preprocessing trace accepts; and actual row zero decodes only after the full
collision-good premise. -/
theorem nonterminal_same_execution_decode_receipt
    (hbasis : OptimizedComputeFinalTrace.FormRBasis basis97) :
    family97.problem.cfg.compRows = 2 ∧
      parentPub.state = .s4 ∧ childPub.state = .s1 ∧
      ComputeTable.fanoutComp parentPub.state = 1 ∧
      parentOut 0 = some childLabel ∧
      Vcomp computeInputs97 parentPub parentDec ∧
      Vcomp computeInputs97 childPub childDec ∧
      RVT (ComputeTable.Fcomp (K := K97cubic)) computeTree ∧
      exec97.derivedRequestIO =
        [NockVM.encRecFormR parentRequest MemoryTable.formRDefault,
            NockVM.encRecFormR childRequest MemoryTable.formRDefault] ∧
      exec97.derivedResponseIO =
        [NockVM.encRecFormR parentRequest MemoryTable.formRDefault,
            NockVM.encRecFormR childRequest MemoryTable.formRDefault] ∧
      exec97.derivedRequestIO.Nodup ∧ exec97.MemoryRowsAccepted ∧
      sampledAssignment97.sampled.records.requests =
        family97.problem.exec.derivedRequestIO ∧
      sampledAssignment97.sampled.records.responses =
        family97.problem.exec.derivedResponseIO ∧
      sampledAssignment97.ComputeSampledObligations ∧
      RAP.SatisfiesWithPreprocessing
        (ProductionNamedComputeRAP family97.problem.cfg.compRows_pos computeNodes97 basis97
          challengeCoordinates97 publicCoordinates97 strictOrbit97)
        correctedTrace97 ∧
      (let env := gatherCorrectedFinalTypedEnv basis97
        (envOfTrace correctedTrace97 strictOrbit97.ω
          (computeNodes97 row0) challengeCoordinates97 publicCoordinates97)
       env.baseTrace 12 = 0 ∧ FinalComputeCollisionFree env.toSourceEnv ∧
        CorrectedDecodedTransitionSources env) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, parent_accepts, child_accepts, computeTree_rvt,
    derived_requests, derived_responses, derived_requests_nodup, memory_rows_accepted,
    sampledAssignment97.requests_eq, sampledAssignment97.responses_eq, sampled_obligations97,
    corrected_trace97_satisfies hbasis, ?_⟩
  exact ⟨row0_not_last, row0_full_collision_good, row0_decoded_via_conditional_row_decode hbasis⟩

end Nonterminal


/-- The six-field optimized statement is determined by its fields. -/
theorem batch66_six_field_control_still_compiles
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} {P : OptimizedStrictNockVMROMPackage F K hOrb}
    (S : OptimizedStrictThm54Statement P) :
    S =
      { sameExecution := S.sameExecution
        structuralResiduals := S.structuralResiduals
        optimizedChips := S.optimizedChips
        exactResources := S.exactResources
        sharedForestAxis := S.sharedForestAxis
        completeS7 := S.completeS7 } :=
  Nock.RedTeam.Batch66.optimized_capstone_reconstructs_from_six_fields S

/-- The paper alias `Thm:NockVMROM` is `optimizedFullStrictNockVMROM_of_package`. -/
theorem paper_alias_targets_optimized_full_strict :
    @«Thm:NockVMROM» =
      @Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  rfl

#print axioms full_capstone_reconstructs_from_fourteen_fields
#print axioms historical_nonB29_surface_is_one_package
#print axioms package_object_identity_receipt
#print axioms exact_resource_and_raw_budget_receipt
#print axioms false_acceptance_membership_exact
#print axioms outside_union_exports_all_four_components
#print axioms acceptance_pins_exact_traces
#print axioms acceptance_pins_exact_challenges
#print axioms mixed_denominator_formula_exact
#print axioms Nonterminal.row_index_substitution_rejected
#print axioms Nonterminal.nonterminal_same_execution_decode_receipt
#print axioms batch66_six_field_control_still_compiles
#print axioms paper_alias_targets_optimized_full_strict

#print axioms OptimizedFullStrictNockVMROMPackage.structural
#print axioms OptimizedFullStrictNockVMROMPackage.acceptance_outside_failure_implies_target
#print axioms OptimizedFullStrictNockVMROMPackage.optimizedFalseAcceptance_probability_le
#print axioms OptimizedFullStrictNockVMROMPackage.optimizedFalseAcceptance_probability_le_two_pow_neg
#print axioms optimizedFullStrictNockVMROM_of_package
#print axioms production_surface_is_full_and_optimized
#print axioms concreteOptimizedFullStrictPackage
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete.strict_release_nonterminal_fixture

end
end Nock.RedTeam.Batch67
