import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
import Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
import Nock.NockVMROM.Thm54.MultiRootServedFixture
import Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Collision-free selector fold over the distinct-pair `OP_5` census

`DistinctCensusPhaseCorrect` constructed `packageQ` over `dataD` / `residualHonestQ` /
`walkArraysQ` at compiler-fold `⟨0,0⟩`.  The accepted canonical optimized tuple sits inside
the compute collision event because scalar challenge `36` is `0`, a root of the `s5`/`s1`
selector RLC.

Seed stays `8`.  `packageQ` is
untouched.
-/

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.DistinctCensusFold2

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Noun Nock.Walk Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.EqualityOperandCensus
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment
open Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
open Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeCodec
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97r : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97r : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
include hfirstD

/-! ## A. Collision-free Inputs and the reconstructed package -/

def fold2Challenges : FinalComputeChallengeTuple K97cubic := default

def inputsR : Inputs (distinctCensusExecution hfirstD) :=
  (inputsD hfirstD).withComputeChallenges fold2Challenges

theorem inputsR_zero_cubic :
    (inputsR hfirstD).computeChallenges = (default : FinalComputeChallengeTuple K97cubic) :=
  rfl

theorem inputsR_changes_only_compute_challenges :
    (inputsR hfirstD).computeChallenges = fold2Challenges ∧
      (inputsR hfirstD).computeWalkAlpha = (inputsD hfirstD).computeWalkAlpha ∧
      (inputsR hfirstD).memoryWalkAlpha = (inputsD hfirstD).memoryWalkAlpha ∧
      (inputsR hfirstD).walkGamma = (inputsD hfirstD).walkGamma ∧
      (inputsR hfirstD).hOrb = (inputsD hfirstD).hOrb ∧
      (inputsR hfirstD).ioCoins = (inputsD hfirstD).ioCoins ∧
      (inputsR hfirstD).memoryScalarChallenge = (inputsD hfirstD).memoryScalarChallenge ∧
      (inputsR hfirstD).memoryExtensionFold = (inputsD hfirstD).memoryExtensionFold :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The reconstructed package.**  Same `dataD` census, same phase-correct residual
`residualHonestQ`, selector fold `2`. -/
def packageR :
    OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F97 K97cubic 5 :=
  buildFullPackageWith (distinctCensusExecution hfirstD) (inputsR hfirstD)
    (residualHonestQ hfirstD)
    (computeChallenge_pins (distinctCensusExecution hfirstD) (inputsR hfirstD))
    DistinctCensusC1.pairedRecordLayout_distinctCensus
    (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD)
      (by change 1 ≤ 1; trivial))
    (DistinctCensusPhaseCorrect.phase_walkOrder hfirstD)
    (DistinctCensusCommitment.walkOrderMemD hfirstD)
    (DistinctCensusCommitment.rowsBoundD hfirstD)
    (DistinctCensusCommitment.residualD_generated hfirstD) DistinctCensusCommitment.f97_primeFieldD

variable (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
variable (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
variable (hwidthR : FormRWidth F97)

theorem statementR
    (hax : FormRAxisBound
      (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasis : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidth : FormRWidth F97) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageR hfirstD) :=
  universalOptimizedFullStrictThm54With (distinctCensusExecution hfirstD) (inputsR hfirstD)
    (residualHonestQ hfirstD)
    (computeChallenge_pins (distinctCensusExecution hfirstD) (inputsR hfirstD))
    DistinctCensusC1.pairedRecordLayout_distinctCensus
    (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD)
      (by change 1 ≤ 1; trivial))
    (DistinctCensusPhaseCorrect.phase_walkOrder hfirstD)
    (DistinctCensusCommitment.walkOrderMemD hfirstD)
    (DistinctCensusCommitment.rowsBoundD hfirstD)
    (DistinctCensusCommitment.residualD_generated hfirstD) DistinctCensusCommitment.f97_primeFieldD
    hax hbasis hwidth

theorem packageR_verifier : (packageR hfirstD).strategy.verifier = verifierQ hfirstD := rfl

theorem packageR_seed : (packageR hfirstD).honestSeed = seedD := rfl

theorem packageR_census : (packageR hfirstD).optimized.census = censusD := rfl

variable (hrootAt : ∀ a g : K97cubic,
  (packageR hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
include hrootAt
variable (hrootAtQ : ∀ a g : K97cubic,
  (packageQ hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
include hrootAtQ

/-- The released constructor requires `hzero`. -/
theorem released_hzero_still_required :
    (∀ (I : Inputs (distinctCensusExecution hfirstD))
      (_R : BuildablePackage.CommitmentResidual (distinctCensusExecution hfirstD)),
      I.computeChallenges = default →
        (2 ≤ (distinctCensusExecution hfirstD).cfg.compRows →
          (distinctCensusExecution hfirstD).cfg.compRows ≤ orderOf I.computeWalkAlpha) →
        (2 ≤ (distinctCensusExecution hfirstD).cfg.memRows →
          (distinctCensusExecution hfirstD).cfg.memRows ≤ orderOf I.memoryWalkAlpha) →
        GeneratedField.ClaimGenerated K97cubic _R.verifier.raw.claim _R.Λ →
        Nonempty
          (OptimizedFullStrictNockVMROMPackage F97 K97cubic I.hOrb)) ∧
      (inputsR hfirstD).computeChallenges = default := by
  constructor
  · intro I _R hzero hord hordM hgenF
    exact ⟨buildFullPackage (distinctCensusExecution hfirstD) I _R hzero
      DistinctCensusC1.pairedRecordLayout_distinctCensus
      (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD)
        (by change 1 ≤ 1; trivial))
      hord hordM (DistinctCensusCommitment.rowsBoundD hfirstD)⟩
  · rfl

/-- **The one package accepts the coin at every sampled walk-challenge pair.** -/
theorem packageR_accepts (a g : K97cubic) : (packageR hfirstD).strategy.Accepts (coinQ a g) cfgD.challenges.lam := by
  apply ((packageR hfirstD).strategy.accepts_iff (coinQ a g) cfgD.challenges.lam seedH_ne).2
  constructor
  · apply (ProductionAxisStructureVerifier.accepts_iff (verifierQ hfirstD) (coinQ a g) cfgD.challenges.lam seedH_ne).2
    exact ⟨((verifierQ hfirstD).accepts_iff_production (coinQ a g) cfgD.challenges.lam seedH_ne).1
      (verifierQ_accepts hfirstD a g), structuralChecksQ hfirstD⟩
  · exact hrootAt a g

theorem coinR_not_guardedAxisFailureEvent (a g : K97cubic) :
    coinQ a g ∉ ProductionP8Containment.guardedAxisFailureEvent (packageR hfirstD).strategy
      cfgD.challenges.lam := by
  rw [ProductionP8Containment.mem_guardedAxisFailureEvent_iff]
  rintro ⟨hz, hbad⟩
  change alphaD ∈
    ProductionAxisStructureVerifier.verifierGuardedRootUnion (templateD hfirstD)
      cfgD.challenges.lam at hbad
  obtain ⟨i, -, hmem⟩ := Finset.mem_biUnion.1 hbad
  simp only [ProductionAxisStructureVerifier.verifierGuardedRootAlphas,
    Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  obtain ⟨-, -, ⟨e, hread, hverify, hne⟩, -, -⟩ := hmem
  exact hne
    (axis_eq_relaxis_transportedD hfirstD _ (dataD hfirstD).honest_execA i e hread hverify)

theorem coinR_not_failureUnion (a g : K97cubic) :
    coinQ a g ∉ ProductionP8Containment.FailureUnion (packageR hfirstD).strategy
      (packageR hfirstD).optimized.census cfgD.challenges.lam := by
  intro hbad
  simp only [ProductionP8Containment.FailureUnion, Finset.mem_union] at hbad
  rcases hbad with hbad | hbad
  · rcases hbad with hbad | hbad
    · rcases hbad with hbad | hbad
      · rcases hbad with hbad | hbad
        · exact coinQ_not_zeroSeedFailureEvent hfirstD hrootAtQ a g hbad
        · rw [packageR_census] at hbad
          exact coinQ_not_collisionFailureEvent hfirstD hrootAtQ a g hbad
      · exact coinQ_not_specializedTopologyFailureEvent hfirstD hrootAtQ a g hbad
    · exact coinR_not_guardedAxisFailureEvent hfirstD hrootAt hrootAtQ a g hbad
  · exact coinQ_not_sizeWindowFailure hfirstD hrootAtQ a g hbad

theorem genuineTargetR (a g : K97cubic) :
    ProductionP8Containment.GenuineTargetAt (packageR hfirstD).strategy 97 7 (coinQ a g) cfgD.challenges.lam :=
  (packageR hfirstD).containment (coinQ a g) cfgD.challenges.lam
    (packageR_accepts hfirstD hrootAt hrootAtQ a g) (coinR_not_failureUnion hfirstD hrootAt hrootAtQ a g)

theorem packageR_consumed_census_has_genuine_distinct_pair :
    ∃ i : Fin (packageR hfirstD).optimized.census.census.count,
      (packageR hfirstD).optimized.census.census.pair i =
          (operandLeft, operandRight) ∧
        ((packageR hfirstD).optimized.census.census.pair i).1 ≠
          ((packageR hfirstD).optimized.census.census.pair i).2 :=
  censusD_has_distinct_pair

theorem packageR_regression :
    (packageR hfirstD).objects.cfg = cfgD ∧
      (packageR hfirstD).objects.exec = execD ∧
      (packageR hfirstD).computeChip.rap.w = 303 ∧ (packageR hfirstD).computeChip.rap.s = 418 ∧
      (packageR hfirstD).memoryChip.rap.w = 205 ∧ (packageR hfirstD).memoryChip.rap.s = 156 ∧
      (packageR hfirstD).computeChip.rap.H.card = 3 ∧
      (inputsR hfirstD).computeChallenges = fold2Challenges ∧
      (inputsR hfirstD).hOrb = 5 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · exact (chip_resources (distinctCensusExecution hfirstD) (inputsR hfirstD)).1
  · exact (chip_resources (distinctCensusExecution hfirstD) (inputsR hfirstD)).2.1
  · exact (chip_resources (distinctCensusExecution hfirstD) (inputsR hfirstD)).2.2.1
  · exact (chip_resources (distinctCensusExecution hfirstD) (inputsR hfirstD)).2.2.2
  · exact (raw_row_cards (distinctCensusExecution hfirstD) (inputsR hfirstD)).1

/-! ## B. Optimized traces, selector fold `2`, outside-event acceptance -/

omit hrootAt hrootAtQ in
abbrev computeTraceR := canonicalComputeTrace (packageR hfirstD)
omit hrootAt hrootAtQ in
abbrev memoryTraceR := canonicalMemoryTrace (packageR hfirstD)
omit hrootAt hrootAtQ in
abbrev tupleR (a g : K97cubic) := canonicalProductionTuple (packageR hfirstD) (coinQ a g)

theorem packageR_optimized_acceptance (a g : K97cubic)
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled
      (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97) :
    (packageR hfirstD).OptimizedHistoricalAcceptanceAt (computeTraceR hfirstD)
      (memoryTraceR hfirstD) (tupleR hfirstD a g) :=
  canonicalProductionAcceptance (packageR hfirstD) (coinQ a g)
    (packageR_accepts hfirstD hrootAt hrootAtQ a g) rfl rfl
    (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD)
      (by change 1 ≤ 1; trivial))
    DistinctCensusExecution.execD_cprimeCoherent haxR hbasisR hwidthR

omit hrootAt hrootAtQ in
theorem packageR_first_state :
    ((packageR hfirstD).optimized.family.problem.exec.computePubAt
      ⟨0, (packageR hfirstD).optimized.family.problem.cfg.compRows_pos⟩).state = .s5 := by
  change (execD.computePubAt ⟨0, _⟩).state = _
  rw [computePubAtD_zero]
  rfl

omit hrootAt hrootAtQ in
theorem packageR_last_state :
    ((packageR hfirstD).optimized.family.problem.exec.computePubAt
      ⟨(packageR hfirstD).optimized.family.problem.cfg.compRows - 1,
        Nat.sub_lt (packageR hfirstD).optimized.family.problem.cfg.compRows_pos Nat.one_pos⟩).state =
      .s1 := by
  change (execD.computePubAt ⟨2, _⟩).state = _
  rw [computePubAtD_two]
  rfl

omit hrootAt hrootAtQ in
theorem packageR_selector31_error_value (j : Fin 11) :
    ((packageR hfirstD).computeScalarEnv (computeTraceR hfirstD)).trace (j : ℕ) -
        ((packageR hfirstD).computeScalarEnv (computeTraceR hfirstD)).pub (31 + (j : ℕ)) =
      (if j = 1 then -1 else if j = 5 then 1 else 0) := by
  rw [canonical_scalarEnv_trace (packageR hfirstD) j]
  have hp := (packageR hfirstD).optimized.computePublicPins.2.2 j
  have hp' :
      ((packageR hfirstD).computeScalarEnv (computeTraceR hfirstD)).pub (31 + (j : ℕ)) =
        (if j = OptimizedComputeCodec.stateIndex
            ((packageR hfirstD).optimized.family.problem.exec.computePubAt
              ⟨(packageR hfirstD).optimized.family.problem.cfg.compRows - 1,
                Nat.sub_lt (packageR hfirstD).optimized.family.problem.cfg.compRows_pos
                  Nat.one_pos⟩).state then 1 else 0) := by
    change (packageR hfirstD).optimized.computePublic (31 + (j : ℕ)) = _
    simpa using hp
  rw [hp', packageR_first_state, packageR_last_state]
  fin_cases j <;> norm_num [OptimizedComputeCodec.stateIndex] <;> decide

omit hrootAt hrootAtQ in
theorem two_is_not_packageR_selector_bad :
    (2 : F97) ∉ finalSelectorBadChallenges
      ((packageR hfirstD).computeScalarEnv (computeTraceR hfirstD)) := by
  have h20 :
      selectorBadChallenges ((packageR hfirstD).computeScalarEnv (computeTraceR hfirstD)) 20 = ∅ := by
    unfold selectorBadChallenges
    exact valueBadChallenges_eq_empty_of_all_zero _
      (canonical_selector20_zero (packageR hfirstD))
  rw [finalSelectorBadChallenges, h20, Finset.empty_union]
  unfold selectorBadChallenges valueBadChallenges
  split
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hroot
    rw [show selectorErrors ((packageR hfirstD).computeScalarEnv (computeTraceR hfirstD)) 31 =
      [0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0] by
        simp only [selectorErrors]
        congr 1
        · simpa using packageR_selector31_error_value hfirstD 0
        · congr 1
          · simpa using packageR_selector31_error_value hfirstD 1
          · congr 1
            · simpa using packageR_selector31_error_value hfirstD 2
            · congr 1
              · simpa using packageR_selector31_error_value hfirstD 3
              · congr 1
                · simpa using packageR_selector31_error_value hfirstD 4
                · congr 1
                  · simpa using packageR_selector31_error_value hfirstD 5
                  · congr 1
                    · simpa using packageR_selector31_error_value hfirstD 6
                    · congr 1
                      · simpa using packageR_selector31_error_value hfirstD 7
                      · congr 1
                        · simpa using packageR_selector31_error_value hfirstD 8
                        · congr 1
                          · simpa using packageR_selector31_error_value hfirstD 9
                          · congr 1
                            · simpa using packageR_selector31_error_value hfirstD 10] at hroot
    norm_num [valueRlcPolynomial] at hroot
    exact (by decide : (30 : F97) ≠ 0) hroot
  · simp

omit hrootAt hrootAtQ in
/-- The canonical compute tuple is outside the consumed two-lift compute collision event. -/
theorem packageR_compute_outside_failure :
    canonicalComputeChallengeTuple (packageR hfirstD) ∉
      extensionFinalComputeCollisionEvent ((packageR hfirstD).computeSourceEnv (computeTraceR hfirstD))
        ((packageR hfirstD).computeWalkEnv (computeTraceR hfirstD)) := by
  simp [extensionFinalComputeCollisionEvent]

end

end Nock.NockVMROM.Thm54.DistinctCensusFold2

#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.fold2Challenges
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.inputsR
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.packageR
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.statementR
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.released_hzero_still_required
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.packageR_accepts
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.coinR_not_failureUnion
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.genuineTargetR
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.two_is_not_packageR_selector_bad
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.packageR_compute_outside_failure
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.packageR_optimized_acceptance
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.buildFullPackage
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.buildFullPackageWith
