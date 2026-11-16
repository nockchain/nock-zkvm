import Nock.NockVMROM.Thm54.CompilerFoldCorrespondence
import Nock.RedTeam.Batch87Thm54CollisionFreeSelector
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed Lean objects:
`exactFinalChallenge`, `BuildableChips.computeChallenge`,
`DistinctCensusFold2.packageR`, `combinedSourceExpr`, and
`OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageR hfirstD)`.

Result: scoped PASS.  The current paper has no sampled challenge corresponding
to compiler folds `9`, `11`, or `36`.  The `3 * 12 = 36` fact is a Lean
physical-layout fact, not a statement of the paper; those paper lines
name the five semantic compute RAP inputs.  Slot `36` is nevertheless used by
Lean to compress the paper's two endpoint selector/public equality checks, so
the precise absence statement is “no paper-sampled challenge corresponding to
slot 36”, not “no paper object has any Lean image involving slot 36”.
-/

set_option autoImplicit false

namespace Nock.RedTeam.Batch88

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.ComputeTable Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment
open Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
open Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
open Nock.NockVMROM.Thm54.DistinctCensusFold2
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-! ## A. Paper RAP inputs and OP_5 are not overwritten -/

/-- Direct expansion of the consumed semantic challenge map.  These are the five
inputs fixed in the paper. -/
theorem slots_0_to_4_are_exactly_alpha_z_a_b_c
    (A : SampledIOSameExecutionAssignment R p) :
    exactFinalChallenge A 0 = R.problem.cfg.challenges.computeInputs.α ∧
      exactFinalChallenge A 1 = R.problem.cfg.challenges.computeInputs.z ∧
      exactFinalChallenge A 2 = R.problem.cfg.challenges.computeInputs.a ∧
      exactFinalChallenge A 3 = R.problem.cfg.challenges.computeInputs.b ∧
      exactFinalChallenge A 4 = R.problem.cfg.challenges.computeInputs.c :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Varying the complete compiler tuple, including its base-field slot `36`,
cannot overwrite OP_5's paper `(a,b,c)` inputs at slots `2/3/4`. -/
theorem op5_inputs_survive_every_compiler_tuple
    (A : SampledIOSameExecutionAssignment R p)
    (c : FinalComputeChallengeTuple K) :
    exactFinalChallengeWith A c 2 = R.problem.cfg.challenges.computeInputs.a ∧
      exactFinalChallengeWith A c 3 = R.problem.cfg.challenges.computeInputs.b ∧
      exactFinalChallengeWith A c 4 = R.problem.cfg.challenges.computeInputs.c :=
  ⟨rfl, rfl, rfl⟩

/-! ## B. The four-way paper expression has no compiler-fold input -/

/-- Direct syntactic check of the expression transcribing -/
theorem combinedSourceExpr_has_no_compiler_input :
    CompilerInputFree combinedSourceExpr := by
  rw [← compilerInputFreeB_iff]
  decide

/-- Strong evaluation form: changing any of `challenge9`, `challenge11`, or
`challenge36` leaves the paper four-way source expression unchanged. -/
theorem combinedSourceExpr_ignores_9_11_36
    (A : SampledIOSameExecutionAssignment R p)
    (env : CorrectedFinalTypedEnv F K)
    (c d : FinalComputeChallengeTuple K) :
    combinedSourceExpr.eval (withFinalComputeChallenges A env c).toSourceEnv =
      combinedSourceExpr.eval (withFinalComputeChallenges A env d).toSourceEnv := by
  calc
    _ = combinedSourceExpr.eval env.toSourceEnv :=
      eval_withFinalComputeChallenges_of_free A env c combinedSourceExpr
        combinedSourceExpr_has_no_compiler_input
    _ = _ :=
      (eval_withFinalComputeChallenges_of_free A env d combinedSourceExpr
        combinedSourceExpr_has_no_compiler_input).symm

/-- The two paper walk-init equations are independently
compiler-free before Lean folds them together. -/
theorem walk_init_equations_have_no_compiler_input :
    CompilerInputFree optimizedWalkLn1 ∧
      CompilerInputFree optimizedWalkCount1 := by
  constructor <;> rw [← compilerInputFreeB_iff] <;> decide

/-- Negative control: the optimized combined walk-init equation does read the
Lean-only slot `11`. -/
theorem walk_init_compiler_fold_really_reads_slot11 :
    optimizedWalkInitFold =
        .Add optimizedWalkLn1
          (.Mul (.Var .challenge 11) optimizedWalkCount1) ∧
      ¬ CompilerInputFree optimizedWalkInitFold := by
  constructor
  · rfl
  · rw [← compilerInputFreeB_iff]
    decide

/-! ## C. Slot 36 is a Lean physical-layout fact -/

/-- This theorem is deliberately uncited: it is the current Lean compiler
allocation, not a claim made by the paper. -/
theorem raw_slot36_is_lean_layout :
    tableChallengeBase = 0 ∧ tableChallengeCount = 6 ∧
      walkChallengeBase = 6 ∧ walkChallengeCount = 1 ∧
      sampledChallengeBase = 7 ∧ sampledChallengeCount = 2 ∧
      compilerChallengeBase = 9 ∧ compilerChallengeCount = 3 ∧
      compilerChallengeBase + compilerChallengeCount = 12 ∧
      finalScalarChallengeBase =
        3 * (compilerChallengeBase + compilerChallengeCount) := by
  decide

/-- Every cubic coordinate is strictly below raw scalar slot `36`. -/
theorem every_cubic_coordinate_precedes_slot36
    (q : Fin 12) (k : Fin 3) :
    3 * (q : ℕ) + (k : ℕ) < finalScalarChallengeBase := by
  simp only [finalScalarChallengeBase]
  omega

def perturbSlot36 (chalVal : ℕ → F) (j : ℕ) : F :=
  if j = finalScalarChallengeBase then chalVal j + 1 else chalVal j

/-- Negative control: the perturbation genuinely changes raw slot `36`. -/
theorem perturbSlot36_changes_slot36 (chalVal : ℕ → F) :
    perturbSlot36 chalVal finalScalarChallengeBase ≠
      chalVal finalScalarChallengeBase := by
  simp [perturbSlot36]

theorem frozen_pin_is_blind_to_slot36
    [FiniteDimensional F K]
    (b : Basis (Fin 3) F K)
    (A : SampledIOSameExecutionAssignment R p)
    (chalVal : ℕ → F) :
    ExactFinalChallengeCoordinates b A (perturbSlot36 chalVal) ↔
      ExactFinalChallengeCoordinates b A chalVal := by
  constructor
  · intro h q k
    simpa [perturbSlot36,
      ne_of_lt (every_cubic_coordinate_precedes_slot36 q k)] using h q k
  · intro h q k
    simpa [perturbSlot36,
      ne_of_lt (every_cubic_coordinate_precedes_slot36 q k)] using h q k

/-! ## D. Reproduce the result at `(packageR hfirstD)` and the consumed statement -/

local instance prime97b88 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97b88 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
variable (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
variable (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
variable (hwidthR : FormRWidth F97)
include haxR hbasisR hwidthR
include hfirstD

theorem packageR_op5_inputs_are_the_paper_inputs :
    (inputsR hfirstD).computeChallenges =
        (default : FinalComputeChallengeTuple K97cubic) ∧
      exactFinalChallengeWith
          (sampledAssignment (distinctCensusExecution hfirstD) (inputsR hfirstD))
          (inputsR hfirstD).computeChallenges 2 =
        cfgD.challenges.computeInputs.a ∧
      exactFinalChallengeWith
          (sampledAssignment (distinctCensusExecution hfirstD) (inputsR hfirstD))
          (inputsR hfirstD).computeChallenges 3 =
        cfgD.challenges.computeInputs.b ∧
      exactFinalChallengeWith
          (sampledAssignment (distinctCensusExecution hfirstD) (inputsR hfirstD))
          (inputsR hfirstD).computeChallenges 4 =
        cfgD.challenges.computeInputs.c :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem packageR_raw36_is_the_compiler_tuple :
    computeChallenge (distinctCensusExecution hfirstD) (inputsR hfirstD)
        finalScalarChallengeBase = 0 :=
  computeChallenge_slot36 (distinctCensusExecution hfirstD) (inputsR hfirstD)

theorem packageR_is_the_existing_With_package :
    (packageR hfirstD) =
      buildFullPackageWith (distinctCensusExecution hfirstD) (inputsR hfirstD) (residualHonestQ hfirstD)
        (computeChallenge_pins (distinctCensusExecution hfirstD) (inputsR hfirstD))
        DistinctCensusC1.pairedRecordLayout_distinctCensus
        (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD)
          (by change 1 ≤ 1; trivial))
        (DistinctCensusPhaseCorrect.phase_walkOrder hfirstD)
        (DistinctCensusCommitment.walkOrderMemD hfirstD)
        (DistinctCensusCommitment.rowsBoundD hfirstD)
        (DistinctCensusCommitment.residualD_generated hfirstD) DistinctCensusCommitment.f97_primeFieldD :=
  rfl

theorem packageR_frozen_pin_and_consumed_statement :
    ExactFinalChallengeCoordinates (inputsR hfirstD).basis
        (sampledAssignment (distinctCensusExecution hfirstD) (inputsR hfirstD))
        (computeChallenge (distinctCensusExecution hfirstD) (inputsR hfirstD)) ∧
      OptimizedFullStrictThm54Statement (packageR hfirstD) :=
  ⟨(packageR hfirstD).optimized.computeChallengePins, (statementR hfirstD haxR hbasisR hwidthR)⟩

theorem packageR_endpoint_checks_use_internal_raw36 :
    (finalMaskedEndpointEqualityChecks (F := F97)).length = 2 ∧
      finalScalarChallengeBase = 36 ∧
      computeChallenge (distinctCensusExecution hfirstD) (inputsR hfirstD) finalScalarChallengeBase = 0 :=
  ⟨rfl, rfl, computeChallenge_slot36 (distinctCensusExecution hfirstD) (inputsR hfirstD)⟩

#print axioms slots_0_to_4_are_exactly_alpha_z_a_b_c
#print axioms op5_inputs_survive_every_compiler_tuple
#print axioms combinedSourceExpr_has_no_compiler_input
#print axioms combinedSourceExpr_ignores_9_11_36
#print axioms walk_init_equations_have_no_compiler_input
#print axioms walk_init_compiler_fold_really_reads_slot11
#print axioms raw_slot36_is_lean_layout
#print axioms every_cubic_coordinate_precedes_slot36
#print axioms perturbSlot36_changes_slot36
#print axioms frozen_pin_is_blind_to_slot36
#print axioms packageR_op5_inputs_are_the_paper_inputs
#print axioms packageR_raw36_is_the_compiler_tuple
#print axioms packageR_is_the_existing_With_package
#print axioms packageR_frozen_pin_and_consumed_statement
#print axioms packageR_endpoint_checks_use_internal_raw36

#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch88
