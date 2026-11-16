import Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
import Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
import Nock.NockVMROM.Thm54.MultiRootServedFixture
import Nock.RedTeam.Batch84Thm54DistinctCensusPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# honest arrays over the consumed distinct census

Paper frame:
the paper,
1697-1716,1813-1848,1864-1868`.

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

The qualification is partial: the exact table
rows and symbolic IO relation remain inhabited, and a duplicated response list
is rejected.

The collision exclusion is independently substantive at its own layer.  The
actual census consumed by `statementH` contains the unequal OP5 operands, those
operands are `PairFaithful` at seed `8`, and the same package census's collision
event is inhabited at seed `-1`.  Neither `alphaC` nor `gamma` occurs in that
event predicate.

The earlier `8 + 1 + 5` count is correct but its optimized-tail rationale is not:
the generic canonical bridge already exhibits optimized acceptance at
`packageH`.  That accepted tuple lies inside the optimized compute failure event
because the fixed scalar challenge is zero while the OP5/OP1 terminal selector
comparison has zero constant coefficient and a nonzero later coefficient.
Thus the `acceptance_to_target` outside-event antecedent is still not discharged.
-/

set_option autoImplicit false

namespace Nock.RedTeam.Batch85

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Noun Nock.Walk Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.EqualityOperandCensus
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment
open Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
include hfirstD
variable (hrootAt : (packageH hfirstD).strategy.RootAxisBoundaryAt
  (nprSeed coinH) seedH_ne (alphaM coinH))

/-! ## A. -/

theorem coinH_is_zero_walk_coin :
    alphaC coinH = 0 ∧ gamma coinH = 0 ∧ alphaM coinH = alphaD ∧
      nprSeed coinH = seedD :=
  coinH_coordinates hfirstD

theorem walkArraysD_is_coin_constant
    (ω₁ ω₂ : JointCoins K97cubic) (lmb₁ lmb₂ : K97cubic)
    (hz₁ : nprSeed ω₁ ≠ 0) (hz₂ : nprSeed ω₂ ≠ 0) :
    walkArraysD hfirstD ω₁ lmb₁ hz₁ = walkArraysD hfirstD ω₂ lmb₂ hz₂ :=
  rfl

/-- A fixed `walkArraysD` response can only accept coins whose compute-walk
challenge is the response's specialized value, zero. -/
theorem rawStrategyD_accepts_only_zero_alphaC
    (ω : JointCoins K97cubic) (hz : nprSeed ω ≠ 0)
    (hacc : (rawStrategyD hfirstD).Accepts ω cfgD.challenges.lam) :
    alphaC ω = 0 := by
  have hsixω := ((rawStrategyD hfirstD).accepts_iff_six_families ω cfgD.challenges.lam hz).1 hacc
  have hcertω :=
    (((rawStrategyD hfirstD).messageAt ω cfgD.challenges.lam hz).computeWalkRAP_wholeTrace_iff).1
      hsixω.2.2.2.1
  have hsixH :=
    ((rawStrategyD hfirstD).accepts_iff_six_families coinH cfgD.challenges.lam seedH_ne).1
      (rawStrategyD_accepts_coinH hfirstD)
  have hcertH :=
    (((rawStrategyD hfirstD).messageAt coinH cfgD.challenges.lam seedH_ne).computeWalkRAP_wholeTrace_iff).1
      hsixH.2.2.2.1
  have hω := hcertω.1.ln1
  have hH := hcertH.1.ln1
  change (honestAssignmentD hfirstD).computeWalk.ln 1 = alphaC ω at hω
  change (honestAssignmentD hfirstD).computeWalk.ln 1 = 0 at hH
  exact hω.symm.trans hH

def duplicatedResponsesD : List (Fin 9 → K97cubic) :=
  [NockVM.encRec recF, NockVM.encRec recF,
    NockVM.encRec recL, NockVM.encRec recR]

/-- The symbolic IO relation remains discriminating at the zero walk coin. -/
theorem duplicated_response_multiset_rejected :
    ¬ IO.LIO 4 (rawLegacyD hfirstD).exec.derivedRequestIO duplicatedResponsesD := by
  intro h
  have hnd := h.2.1
  simp [duplicatedResponsesD] at hnd

theorem accepted_nonwalk_layers_remain_exact :
    (rawLegacyD hfirstD).exec.ComputeRowsAccepted ∧
      (rawLegacyD hfirstD).exec.MemoryRowsAccepted ∧
      IO.LIO (rawLegacyD hfirstD).cfg.Ksz (rawLegacyD hfirstD).exec.derivedRequestIO
        (rawLegacyD hfirstD).exec.derivedResponseIO := by
  refine ⟨rawLegacyD_computeRowsAccepted hfirstD, rawLegacyD_memoryRowsAccepted hfirstD, ?_⟩
  have hraw :
      (RawMessage.ofLegacy (honestAssignmentD hfirstD)).Accepts skelD.publicClaim coinH := by
    exact ⟨honestVerifierGatesD hfirstD,
      RawMessage.sixRAPSatisfy_of_legacy (honestAssignmentD hfirstD)
        (honestCompletionD hfirstD).assignment.sixFamilies⟩
  apply (RawMessage.ofLegacy (honestAssignmentD hfirstD)).lio_of_accepts
    (legacyZeroFamilyD_KszBound hfirstD)
  · change
      (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.derivedRequestIO.length + 1 ≤
        2 ^ (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).cfg.orbit.h
    rw [specializedProblemD_honest hfirstD, derived_requestsD]
    norm_num [cfgD, orbitD]
  · change
      (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.derivedResponseIO.length + 1 ≤
        2 ^ (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).cfg.orbit.h
    rw [specializedProblemD_honest hfirstD, derived_responsesD]
    norm_num [cfgD, orbitD]
  · exact hraw


theorem packageH_acceptance_is_partially_degenerate :
    alphaC coinH = 0 ∧ gamma coinH = 0 ∧
      (∃ ln count acc : ℕ → K97cubic,
        WalkSat Nock.RedTeam.Batch79.alteredCur
          Nock.RedTeam.Batch79.alteredChild Nock.RedTeam.Batch79.alteredFanout
          ln count acc 0 0 0 2 ∧ acc 2 = 0) ∧
      ¬ IsFullBFT Nock.RedTeam.Batch79.alteredCur
        Nock.RedTeam.Batch79.alteredChild Nock.RedTeam.Batch79.alteredFanout 2 ∧
      (rawLegacyD hfirstD).exec.ComputeRowsAccepted ∧
      (rawLegacyD hfirstD).exec.MemoryRowsAccepted ∧
      IO.LIO (rawLegacyD hfirstD).cfg.Ksz (rawLegacyD hfirstD).exec.derivedRequestIO
        (rawLegacyD hfirstD).exec.derivedResponseIO ∧
      ¬ IO.LIO 4 (rawLegacyD hfirstD).exec.derivedRequestIO duplicatedResponsesD := by
  refine ⟨rfl, rfl,
    Nock.RedTeam.Batch79.altered_non_bft_walk_accepts_at_zero.1,
    Nock.RedTeam.Batch79.altered_non_bft_walk_accepts_at_zero.2,
    (accepted_nonwalk_layers_remain_exact hfirstD).1,
    (accepted_nonwalk_layers_remain_exact hfirstD).2.1,
    (accepted_nonwalk_layers_remain_exact hfirstD).2.2,
    duplicated_response_multiset_rejected hfirstD⟩

/-! ## B. Same consumed census, and a non-vacuous collision exclusion -/

def badCollisionCoinH : JointCoins K97cubic :=
  ((0, 0), (alphaD, -1))

theorem badCollisionCoinH_mem_consumed_collision_event :
    badCollisionCoinH ∈
      collisionFailureEvent (packageH hfirstD).optimized.census.census := by
  rw [mem_collisionFailureEvent_iff]
  obtain ⟨i, hi, _⟩ := packageH_consumed_census_has_genuine_distinct_pair hfirstD
  refine ⟨i, ?_⟩
  rw [hi]
  exact operands_not_sepSeed_at_neg_one

theorem collision_exclusion_is_pair_substantive :
    (∃ i : Fin (packageH hfirstD).optimized.census.census.count,
      (packageH hfirstD).optimized.census.census.pair i =
          (operandLeft, operandRight) ∧
        ((packageH hfirstD).optimized.census.census.pair i).1 ≠
          ((packageH hfirstD).optimized.census.census.pair i).2) ∧
      OpcodeSemantics.PairFaithful (nprSeed coinH) 97
        operandLeft operandRight ∧
      coinH ∉ collisionFailureEvent (packageH hfirstD).optimized.census.census ∧
      badCollisionCoinH ∈
        collisionFailureEvent (packageH hfirstD).optimized.census.census := by
  refine ⟨packageH_consumed_census_has_genuine_distinct_pair hfirstD, ?_,
    coinH_not_collisionFailureEvent hfirstD,
    badCollisionCoinH_mem_consumed_collision_event hfirstD⟩
  change OpcodeSemantics.PairFaithful seedD 97 operandLeft operandRight
  exact operands_pairFaithful

/-- `collisionFailureEvent` reads only `nprSeed`; zero `alphaC`/`gamma` cannot
make this class empty. -/
theorem collision_event_ignores_walk_coordinates
    (a₁ g₁ a₂ g₂ m z : K97cubic) :
    (((a₁, g₁), (m, z)) : JointCoins K97cubic) ∈
        collisionFailureEvent (packageH hfirstD).optimized.census.census ↔
      (((a₂, g₂), (m, z)) : JointCoins K97cubic) ∈
        collisionFailureEvent (packageH hfirstD).optimized.census.census := by
  simp only [mem_collisionFailureEvent_iff, nprSeed]

/-! ## C. The new residual preserves the whole forest/execution shape -/

def rootIndexH : Fin (packageH hfirstD).objects.cfg.kMem :=
  ⟨0, by
    change 0 < cfgD.kMem
    norm_num [cfgD]⟩

theorem honest_residual_preserves_forest_and_four_records :
    (packageH hfirstD).objects.cfg = cfgD ∧
      (packageH hfirstD).objects.exec = execD ∧
      (packageH hfirstD).objects.exec.memoryRows.length = 21 ∧
      (packageH hfirstD).objects.exec.rawRequests = [recF, recT, recL, recR] ∧
      -- 28th: the served forest is the a-bearing view `execA` (its executed rows are encodes).
      ServedMemoryTrace.rootResponseRecords (distinctCensusExecution hfirstD).execA
          (rootIndexH hfirstD) = [recF, recT, recL, recR] ∧
      ((distinctCensusExecution hfirstD).memoryTrace.roots
        ⟨0, by
          change 0 < cfgD.kMem
          norm_num [cfgD]⟩).services.map (fun s => s.record) =
          [recF, recT, recL, recR] := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · change execD.memoryRows.length = 21
    rw [execution_rowsD.2]
    rfl
  · exact rawRequestsD
  · exact rootResponseRecordsD
  · rfl

/-! ## D. `GenuineTargetAt` is the production witness at the consumed capstone -/

theorem genuineTargetH_is_production_genuineWitness
    (hrootAt : (packageH hfirstD).strategy.RootAxisBoundaryAt
      (nprSeed coinH) seedH_ne (alphaM coinH)) :
    ProductionP8Containment.GenuineTargetAt (packageH hfirstD).strategy 97 7 coinH cfgD.challenges.lam ∧
      ∃ hz : nprSeed coinH ≠ 0,
        Nonempty
          (ProductionP8Containment.GenuineWitness (packageH hfirstD).strategy 97 7
            (nprSeed coinH) hz (alphaM coinH) cfgD.challenges.lam) := by
  refine ⟨genuineTargetH hfirstD hrootAt, ?_⟩
  simpa [ProductionP8Containment.GenuineTargetAt] using genuineTargetH hfirstD hrootAt

/-! ## E. Exact statement accounting and the optimized-tail correction -/

theorem containment_is_the_exact_moved_conjunct
    (hrootAt : (packageH hfirstD).strategy.RootAxisBoundaryAt
      (nprSeed coinH) seedH_ne (alphaM coinH))
    (haxH : FormRAxisBound (packageH hfirstD).optimized.sampled
      (packageH hfirstD).optimized.basis)
    (hbasisH : FormRBasis (packageH hfirstD).optimized.basis)
    (hwidthH : FormRWidth F97) :
    (packageH hfirstD).strategy.Accepts coinH cfgD.challenges.lam ∧
      coinH ∉ FailureUnion (packageH hfirstD).strategy (packageH hfirstD).optimized.census cfgD.challenges.lam ∧
      ProductionP8Containment.GenuineTargetAt (packageH hfirstD).strategy 97 7 coinH cfgD.challenges.lam ∧
      (∀ ω : JointCoins K97cubic, ¬ (packageD hfirstD).strategy.Accepts ω cfgD.challenges.lam) :=
  ⟨packageH_accepts hfirstD hrootAt, coinH_not_failureUnion hfirstD,
    (statementH hfirstD haxH hbasisH hwidthH).containment coinH cfgD.challenges.lam (packageH_accepts hfirstD hrootAt)
      (coinH_not_failureUnion hfirstD),
    fun ω => Nock.RedTeam.Batch84.packageD_accepts_none hfirstD ω _⟩

theorem package_relative_arithmetic_is_correct
    (hmoreM : LaterSeedZeros (F := F97) (K := K97cubic) multiRootExecution)
    (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
      (packageP hmoreM).optimized.basis)
    (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
    (hwidthP : FormRWidth F97)
    (haxH : FormRAxisBound (packageH hfirstD).optimized.sampled
      (packageH hfirstD).optimized.basis)
    (hbasisH : FormRBasis (packageH hfirstD).optimized.basis)
    (hwidthH : FormRWidth F97)
    (haxD : FormRAxisBound (packageD hfirstD).optimized.sampled
      (packageD hfirstD).optimized.basis)
    (hbasisD : FormRBasis (packageD hfirstD).optimized.basis)
    (hwidthD : FormRWidth F97) :
    (8 + 1 + 5 = 14) ∧
      Nonempty (OptimizedFullStrictThm54Statement (packageH hfirstD)) ∧
      (7 + 1 + 6 = 14) ∧
      Nonempty (OptimizedFullStrictThm54Statement (packageD hfirstD)) ∧
      (9 + 1 + 4 = 14) ∧
      Nonempty (OptimizedFullStrictThm54Statement (packageP hmoreM)) :=
  ⟨by norm_num, ⟨statementH hfirstD haxH hbasisH hwidthH⟩, by norm_num, ⟨statementD hfirstD haxD hbasisD hwidthD⟩,
    by norm_num, ⟨statementP hmoreM haxP hbasisP hwidthP⟩⟩

abbrev computeTraceH := canonicalComputeTrace (packageH hfirstD)
abbrev memoryTraceH := canonicalMemoryTrace (packageH hfirstD)
abbrev optimizedTupleH := canonicalProductionTuple (packageH hfirstD) coinH

/-- The earlier analysis said no accepted optimized tuple was exhibited.  The generic bridge
already applies to `packageH`, so that rationale is false even though the final
`8 + 1 + 5` count remains correct. -/
theorem packageH_optimized_acceptance
    (hrootAt : (packageH hfirstD).strategy.RootAxisBoundaryAt
      (nprSeed coinH) seedH_ne (alphaM coinH))
    (hax : FormRAxisBound (packageH hfirstD).optimized.sampled
      (packageH hfirstD).optimized.basis)
    (hbasis : FormRBasis (packageH hfirstD).optimized.basis)
    (hwidth : FormRWidth F97) :
    (packageH hfirstD).OptimizedHistoricalAcceptanceAt (computeTraceH hfirstD)
      (memoryTraceH hfirstD) (optimizedTupleH hfirstD) :=
  canonicalProductionAcceptance (packageH hfirstD) coinH (packageH_accepts hfirstD hrootAt) rfl rfl
    (hmore := BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD)
      (by change 1 ≤ 1; trivial))
    DistinctCensusExecution.execD_cprimeCoherent hax hbasis hwidth

theorem packageH_first_state :
    ((packageH hfirstD).optimized.family.problem.exec.computePubAt
      ⟨0, (packageH hfirstD).optimized.family.problem.cfg.compRows_pos⟩).state = .s5 := by
  change (execD.computePubAt ⟨0, _⟩).state = _
  rw [computePubAtD_zero]
  rfl

theorem packageH_last_state :
    ((packageH hfirstD).optimized.family.problem.exec.computePubAt
      ⟨(packageH hfirstD).optimized.family.problem.cfg.compRows - 1,
        Nat.sub_lt (packageH hfirstD).optimized.family.problem.cfg.compRows_pos Nat.one_pos⟩).state =
      .s1 := by
  change (execD.computePubAt ⟨2, _⟩).state = _
  rw [computePubAtD_two]
  rfl

theorem packageH_selector31_head_zero :
    ((packageH hfirstD).computeScalarEnv (computeTraceH hfirstD)).trace 0 -
      ((packageH hfirstD).computeScalarEnv (computeTraceH hfirstD)).pub 31 = 0 := by
  rw [canonical_selector31_head (packageH hfirstD), packageH_first_state, packageH_last_state]
  norm_num [OptimizedComputeCodec.stateIndex]
  try decide

theorem packageH_selector31_second_nonzero :
    ((packageH hfirstD).computeScalarEnv (computeTraceH hfirstD)).trace 1 -
      ((packageH hfirstD).computeScalarEnv (computeTraceH hfirstD)).pub 32 = -1 := by
  have ht := canonical_scalarEnv_trace (packageH hfirstD) (1 : Fin 11)
  have hp := (packageH hfirstD).optimized.computePublicPins.2.2 (1 : Fin 11)
  change ((packageH hfirstD).computeScalarEnv (computeTraceH hfirstD)).trace 1 = _ at ht
  have hp' :
      ((packageH hfirstD).computeScalarEnv (computeTraceH hfirstD)).pub 32 =
        (if (1 : Fin 11) = OptimizedComputeCodec.stateIndex
            ((packageH hfirstD).optimized.family.problem.exec.computePubAt
              ⟨(packageH hfirstD).optimized.family.problem.cfg.compRows - 1,
                Nat.sub_lt (packageH hfirstD).optimized.family.problem.cfg.compRows_pos
                  Nat.one_pos⟩).state then 1 else 0) := by
    change (packageH hfirstD).optimized.computePublic 32 = _
    simpa using hp
  rw [ht, hp', packageH_first_state, packageH_last_state]
  norm_num [OptimizedComputeCodec.stateIndex]
  try decide

/-- W1 deleted the coordinate, so the fact is stated at the
value level (the tuple-level statement is not restated). -/
theorem packageH_zero_was_a_bad_selector_challenge :
    (0 : F97) ∈
      finalSelectorBadChallenges ((packageH hfirstD).computeScalarEnv (computeTraceH hfirstD)) := by
  apply Finset.mem_union_right
  unfold selectorBadChallenges valueBadChallenges
  have hnonzero :
      ∃ a ∈ selectorErrors ((packageH hfirstD).computeScalarEnv (computeTraceH hfirstD)) 31, a ≠ 0 := by
    refine ⟨-1, ?_, neg_ne_zero.mpr one_ne_zero⟩
    simp [selectorErrors, packageH_selector31_second_nonzero]
  rw [if_pos hnonzero]
  simp [selectorErrors, valueRlcPolynomial, packageH_selector31_head_zero]

/--

There is no legacy reading, the same way `KX` §7 had none for
`outside_union_exports_all_four_components`; the tuple-level statement is not restated. -/
theorem accepted_optimized_tuple_is_inside_historical_compute_failure
    (hrootAt : (packageH hfirstD).strategy.RootAxisBoundaryAt
      (nprSeed coinH) seedH_ne (alphaM coinH))
    (hax : FormRAxisBound (packageH hfirstD).optimized.sampled
      (packageH hfirstD).optimized.basis)
    (hbasis : FormRBasis (packageH hfirstD).optimized.basis)
    (hwidth : FormRWidth F97) :
    (packageH hfirstD).OptimizedHistoricalAcceptanceAt (computeTraceH hfirstD)
        (memoryTraceH hfirstD) (optimizedTupleH hfirstD) ∧
      (0 : F97) ∈
        finalSelectorBadChallenges ((packageH hfirstD).computeScalarEnv (computeTraceH hfirstD)) :=
  ⟨packageH_optimized_acceptance hfirstD hrootAt hax hbasis hwidth, packageH_zero_was_a_bad_selector_challenge hfirstD⟩

/-! ## F. Gate, axiom, and release regression -/

theorem verifier_gates_and_six_families_are_inhabited :
    Nonempty
        ((RawMessage.ofLegacy (honestAssignmentD hfirstD)).VerifierGates skelD.publicClaim coinH) ∧
      Nonempty ((RawMessage.ofLegacy (honestAssignmentD hfirstD)).SixRAPSatisfy) :=
  ⟨⟨honestVerifierGatesD hfirstD⟩,
    ⟨RawMessage.sixRAPSatisfy_of_legacy (honestAssignmentD hfirstD)
      (honestCompletionD hfirstD).assignment.sixFamilies⟩⟩

omit hfirstD in
theorem released_aliases_and_control_unchanged :
    @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package ∧
      @«Thm:NockVMROM:forest-control» =
        @Nock.NockVM.V_NockVMROM_forest :=
  ⟨rfl, rfl⟩

#print axioms coinH_is_zero_walk_coin
#print axioms walkArraysD_is_coin_constant
#print axioms rawStrategyD_accepts_only_zero_alphaC
#print axioms duplicated_response_multiset_rejected
#print axioms accepted_nonwalk_layers_remain_exact
#print axioms packageH_acceptance_is_partially_degenerate
#print axioms badCollisionCoinH_mem_consumed_collision_event
#print axioms collision_exclusion_is_pair_substantive
#print axioms collision_event_ignores_walk_coordinates
#print axioms honest_residual_preserves_forest_and_four_records
#print axioms genuineTargetH_is_production_genuineWitness
#print axioms containment_is_the_exact_moved_conjunct
#print axioms package_relative_arithmetic_is_correct
#print axioms packageH_optimized_acceptance
#print axioms packageH_zero_was_a_bad_selector_challenge
#print axioms accepted_optimized_tuple_is_inside_historical_compute_failure
#print axioms verifier_gates_and_six_families_are_inhabited
#print axioms released_aliases_and_control_unchanged

#print axioms DistinctCensusHonestArrays.honestCompletionD_nonempty
#print axioms DistinctCensusHonestArrays.honestVerifierGatesD
#print axioms DistinctCensusHonestArrays.packageH_accepts
#print axioms DistinctCensusHonestArrays.packageH_consumed_census_has_genuine_distinct_pair
#print axioms DistinctCensusHonestArrays.coinH_not_collisionFailureEvent
#print axioms DistinctCensusHonestArrays.coinH_not_failureUnion
#print axioms DistinctCensusHonestArrays.genuineTargetH
#print axioms DistinctCensusHonestArrays.statementH

#print axioms «Thm:IO_result»
#print axioms «Thm:Walk_IOP»
#print axioms «Corr:forest»
#print axioms «Thm:deterministic_Trace»
#print axioms «Lem:NPR_decomp»
#print axioms «Thm:Noun_Validation»
#print axioms «Thm:comp_38»
#print axioms «Thm:mem_38»
#print axioms «Thm:NockVMROM»
#print axioms «Lem:equiv_compute»
#print axioms «Lem:equiv_mem»
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVM.V_NockVMROM_forest

end
end Nock.RedTeam.Batch85
