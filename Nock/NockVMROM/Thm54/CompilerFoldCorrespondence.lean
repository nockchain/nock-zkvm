import Nock.ComputeTable
import Nock.NockVMROM.Thm54.BuildableChips
import Nock.NockVMROM.Thm54.DistinctCensusFold2
import Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
import Nock.NockVMROM.Thm54.OptimizedComputeFinal
import Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
import Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
import Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
import Nock.NockVMROM.Thm54.OptimizedComputeTemplate

/-!
# Slot ↔ paper correspondence for compiler folds `9`, `11`, and `36`

Inventory of what Lean slots `9`, `11`, and `36` implement, against the paper objects that
actually exist.  This module does not inhabit a paper challenge at slot `36`, does not
restate the released capstone, and does not rewrite `packageR`.

Paper objects that *are* sampled compute / walk / IO randomness:

* compute RAP inputs `(α, z, a, b, c)` — the paper
* OP_5 RLC over that same `(a, b, c)` — the paper
* walk verifier coins `(α, γ)` — the paper
* RAP adaptive column randomness `ρ_i`, with preprocessing *selector polynomials*
  (not a sampled selector challenge) — the paper
* one-hot opcode *trace* selectors `op_j` — the paper
* displayed four-way nonlinear gate combination, using existing `op_s` and `(a,b,c,z)` —
* compute RAP “two equality checks” at the endpoints — the paper
* formula-tail decomposition — the paper (not a challenge)

Lean compiler-internal folds, with no paper-sampled preimage:

* slot `9` — production extension family RLC (`finalFoldChallenge`)
* slot `11` — walk-init pair fold (`optimizedWalkInitFold`)
* slot `36` — raw scalar selector/public RLC (`finalSelectorPublicCheck`)
-/

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54
namespace CompilerFoldCorrespondence

open Module
open Nock
open Nock.ComputeTable
open Nock.Reified
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.DistinctCensusFold2
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-! ## A. Lean slot indices -/

/-- Slot `9` is the production compiler-challenge base. -/
theorem slot9_index : compilerChallengeBase = 9 := rfl

/-- Slot `11` is the walk-init compiler challenge (`compilerChallengeBase + 2`). -/
theorem slot11_index : compilerChallengeBase + 2 = 11 := rfl

/-- Slot `36` is the first raw base-field index after cubic expansion of twelve `K` challenges. -/
theorem slot36_index : finalScalarChallengeBase = 36 := rfl

/-- Cubic expansion of the twelve `K` challenges occupies raw indices `0..35` -/
theorem cubic_block_occupies_0_to_35 : 3 * (compilerChallengeBase + compilerChallengeCount) = 36 :=
  rfl

/-- Slot `36` is outside that cubic block, so it is not a coordinate of any `K`-valued paper input. -/
theorem slot36_outside_cubic_block : ¬ (36 < 3 * 12) := by
  decide

/-! ## B. Paper-sampled compute inputs occupy slots `0..4` -/

/-- The paper RAP inputs are exactly the five fields of `ComputeTable.Inputs` -/
theorem paper_rap_inputs_eta {K' : Type*} (I : ComputeTable.Inputs K') :
    I = { α := I.α, z := I.z, a := I.a, b := I.b, c := I.c } := by
  cases I
  rfl

/-- Lean slots `0..4` are the paper compute RAP inputs `(α, z, a, b, c)` -/
theorem paper_rap_inputs_are_slots_0_to_4
    (A : SampledIOSameExecutionAssignment R p) :
    exactFinalChallenge A 0 = R.problem.cfg.challenges.computeInputs.α ∧
      exactFinalChallenge A 1 = R.problem.cfg.challenges.computeInputs.z ∧
      exactFinalChallenge A 2 = R.problem.cfg.challenges.computeInputs.a ∧
      exactFinalChallenge A 3 = R.problem.cfg.challenges.computeInputs.b ∧
      exactFinalChallenge A 4 = R.problem.cfg.challenges.computeInputs.c :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- OP_5's `(a, b, c)` is slots `2, 3, 4`, not the compiler triple -/
theorem op5_abc_are_slots_2_3_4
    (A : SampledIOSameExecutionAssignment R p) :
    exactFinalChallenge A 2 = R.problem.cfg.challenges.computeInputs.a ∧
      exactFinalChallenge A 3 = R.problem.cfg.challenges.computeInputs.b ∧
      exactFinalChallenge A 4 = R.problem.cfg.challenges.computeInputs.c :=
  ⟨rfl, rfl, rfl⟩

/-- Those OP_5 slots are disjoint from the compiler-fold indices -/
theorem op5_slots_disjoint_compiler_folds :
    (2 : ℕ) ≠ 9 ∧ 3 ≠ 11 ∧ 4 ≠ 36 ∧ 2 ≠ 11 ∧ 3 ≠ 9 ∧ 4 ≠ 9 := by
  decide

/-! ## C. Slot `9` is the Form R `λ` coin, slot `10` the walk `γ`; slot `11` has no paper object -/

theorem paper_semantic_map_vanishes_on_compiler_slots
    (A : SampledIOSameExecutionAssignment R p) :
    exactFinalChallenge A 9 = R.problem.cfg.challenges.lam ∧
      exactFinalChallenge A 10 = R.walkGamma ∧
      exactFinalChallenge A 11 = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- Overlaying a compiler tuple leaves paper slots `0..8` unchanged -/
theorem with_preserves_paper_and_io_slots
    (A : SampledIOSameExecutionAssignment R p)
    (c : FinalComputeChallengeTuple K) :
    (∀ q : Fin 9, exactFinalChallengeWith A c q = exactFinalChallenge A q) := by
  intro q
  fin_cases q <;> rfl

theorem with_reads_compiler_tuple
    (A : SampledIOSameExecutionAssignment R p)
    (c : FinalComputeChallengeTuple K) :
    exactFinalChallengeWith A c 9 = R.problem.cfg.challenges.lam ∧
      exactFinalChallengeWith A c 10 = R.walkGamma ∧
      exactFinalChallengeWith A c 11 = 0 :=
  ⟨rfl, rfl, rfl⟩

theorem frozen_cubic_pin_ignores_slot36
    [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (A : SampledIOSameExecutionAssignment R p)
    (chalVal chalVal' : ℕ → F)
    (h : ∀ q : Fin 12, ∀ k : Fin 3,
      chalVal (3 * (q : ℕ) + (k : ℕ)) = chalVal' (3 * (q : ℕ) + (k : ℕ))) :
    ExactFinalChallengeCoordinates b A chalVal ↔
      ExactFinalChallengeCoordinates b A chalVal' := by
  constructor
  · intro hp q k
    rw [← h q k]
    exact hp q k
  · intro hp q k
    rw [h q k]
    exact hp q k

theorem parameterized_pin_slot36
    [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (A : SampledIOSameExecutionAssignment R p)
    (c : FinalComputeChallengeTuple K) (chalVal chalVal' : ℕ → F)
    (h : ExactFinalChallengeCoordinatesWith b A c chalVal)
    (hagree : ∀ q : Fin 12, ∀ k : Fin 3, chalVal' (3 * (q : ℕ) + (k : ℕ)) = chalVal (3 * q + k)) :
    ExactFinalChallengeCoordinatesWith b A c chalVal' := by
  intro q k
  rw [hagree q k]
  exact h q k

/-! ## D. Nearby paper objects that are *not* slots `9/11/36` -/

/-- The paper's displayed four-way combination uses only challenges `< 9` -/
theorem paper_four_way_fold_is_compilerInputFree :
    CompilerInputFree combinedSourceExpr := by
  rw [← compilerInputFreeB_iff]
  decide

/-- Production family compression is a Horner RLC at slot `9`, not the paper four-way fold. -/
theorem slot9_is_production_family_rlc :
    finalFoldChallenge = .Var .challenge 9 ∧
      (∀ e es, finalRlcFold (e :: es) =
        .Add e (.Mul (.Var .challenge 9) (finalRlcFold es))) :=
  ⟨rfl, fun _ _ => rfl⟩

/-- Paper walk-init equations `ln(1)=α` and `count(1)=…` mention no compiler fold -/
theorem paper_walk_init_summands_are_compilerInputFree :
    CompilerInputFree optimizedWalkLn1 ∧ CompilerInputFree optimizedWalkCount1 := by
  constructor
  · rw [← compilerInputFreeB_iff]; decide
  · rw [← compilerInputFreeB_iff]; decide

/-- Lean slot `11` is the extra factor that folds those two paper equations -/
theorem slot11_is_walk_init_compiler_fold :
    optimizedWalkInitFold =
      .Add optimizedWalkLn1 (.Mul (.Var .challenge 11) optimizedWalkCount1) :=
  rfl

/-- The fold itself is therefore *not* a paper-semantic challenge expression -/
theorem walk_init_fold_is_not_compilerInputFree :
    ¬ CompilerInputFree optimizedWalkInitFold := by
  rw [← compilerInputFreeB_iff]
  decide

/-- Theorem 5.4 names two endpoint equality checks, not a sampled selector challenge -/
theorem paper_terminal_equality_checks_are_two :
    (finalMaskedEndpointEqualityChecks (F := F)).length = 2 :=
  finalMaskedEndpointEqualityChecks_length

/-- Lean implements those checks by an RLC at raw slot `36` -/
theorem slot36_is_selector_public_rlc :
    finalScalarChallengeBase = 36 ∧
      finalMaskedEndpointEqualityChecks (F := F) =
        [.mul isFirstVar (finalSelectorPublicCheck (F := F) .traceCur 20),
          .mul isLastVar (finalSelectorPublicCheck (F := F) .traceCur 31)] :=
  ⟨rfl, rfl⟩

/-- Preprocessing selector polynomials are the first `w_RAP` block, not slot `36` -/
theorem preprocessing_selector_is_round_zero_not_slot36 :
    tableChallengeBase = 0 ∧ finalScalarChallengeBase = 36 ∧ tableChallengeBase ≠ 36 :=
  ⟨rfl, rfl, by decide⟩

/-- One-hot opcode selectors occupy the fifteen base transition gates, not challenge slots -/
theorem one_hot_selectors_are_base_gates_not_challenge :
    (finalBaseTransitionGates (F := F) 2).length = 15 :=
  finalBaseTransitionGates_length 2

/-! ## E. `packageR` still uses the compiler tuple; paper slots are not that tuple -/

noncomputable section

local instance prime97corr : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97corr : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
include hfirstD

theorem packageR_tuple_is_compiler_fold_not_paper_rap_inputs :
    fold2Challenges = (default : FinalComputeChallengeTuple K97cubic) ∧
      (inputsR hfirstD).computeChallenges = (default : FinalComputeChallengeTuple K97cubic) :=
  ⟨rfl, rfl⟩

/-- On `packageR`, the paper-semantic map gives `λ = formRDefault` at slot `9` and still vanishes at
 slot `11` (the compiler cubic slots) -/
theorem packageR_paper_semantic_map_vanishes_on_compiler_slots :
    exactFinalChallenge (sampledAssignment (distinctCensusExecution hfirstD) (inputsR hfirstD)) 9 =
        (MemoryTable.formRDefault : K97cubic) ∧
      exactFinalChallenge (sampledAssignment (distinctCensusExecution hfirstD) (inputsR hfirstD)) 11 = 0 :=
  ⟨rfl, rfl⟩

theorem packageR_overlay_reads_compiler_tuple :
    exactFinalChallengeWith (sampledAssignment (distinctCensusExecution hfirstD) (inputsR hfirstD))
        (inputsR hfirstD).computeChallenges 9 = (MemoryTable.formRDefault : K97cubic) ∧
      exactFinalChallengeWith (sampledAssignment (distinctCensusExecution hfirstD) (inputsR hfirstD))
        (inputsR hfirstD).computeChallenges 11 = 0 ∧
      computeChallenge (distinctCensusExecution hfirstD) (inputsR hfirstD) finalScalarChallengeBase = 0 :=
  ⟨rfl, rfl, computeChallenge_slot36 (distinctCensusExecution hfirstD) (inputsR hfirstD)⟩

end

end CompilerFoldCorrespondence
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.CompilerFoldCorrespondence.paper_rap_inputs_are_slots_0_to_4
#print axioms Nock.NockVMROM.Thm54.CompilerFoldCorrespondence.paper_semantic_map_vanishes_on_compiler_slots
#print axioms Nock.NockVMROM.Thm54.CompilerFoldCorrespondence.paper_four_way_fold_is_compilerInputFree
#print axioms Nock.NockVMROM.Thm54.CompilerFoldCorrespondence.slot11_is_walk_init_compiler_fold
#print axioms Nock.NockVMROM.Thm54.CompilerFoldCorrespondence.slot36_is_selector_public_rlc
#print axioms Nock.NockVMROM.Thm54.CompilerFoldCorrespondence.packageR_tuple_is_compiler_fold_not_paper_rap_inputs
#print axioms Nock.NockVMROM.Thm54.CompilerFoldCorrespondence.packageR_overlay_reads_compiler_tuple
#print axioms Nock.NockVMROM.Thm54.CompilerFoldCorrespondence.walk_init_fold_is_not_compilerInputFree
#print axioms Nock.NockVMROM.Thm54.CompilerFoldCorrespondence.with_preserves_paper_and_io_slots
