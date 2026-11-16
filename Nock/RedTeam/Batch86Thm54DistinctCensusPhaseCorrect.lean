import Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
import Nock.RedTeam.Batch85Thm54DistinctCensusHonestArrays
import Nock.NockVMROM.Thm54.MultiRootServedFixture
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Phase-correct distinct-census package

Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

* `packageQ` is one closed package outside `∀ a g`; its pre-coin message is fixed and its
  post-coin walk columns read `(alphaC,gamma)`.
* This is not paper-forced randomness: arbitrary `Inputs.computeChallenges`
  still build satisfying chips and traces.  The released package constructor nevertheless requires
  the already-recorded `hzero` restriction, so no alternate full package is claimed here.
-/

set_option autoImplicit false

namespace Nock.RedTeam.Batch86

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
open Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.BuildableChips
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
variable (hrootAt : ∀ a g : K97cubic,
  (packageQ hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
include hrootAt
variable (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)

variable (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
    (packageP hmoreM).optimized.basis)
variable (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
variable (hwidthP : FormRWidth F97)

/-! ## A. Quantifier order and fixed commitment -/

/-- The witness is one literal `packageQ`, not a package rebuilt under `(a,g)`. -/
theorem one_fixed_package_outside_the_pair_quantifier :
    (∀ a g : K97cubic, (packageQ hfirstD).strategy.Accepts (coinQ a g) cfgD.challenges.lam) ∧
      (∃ P : OptimizedFullStrictNockVMROMPackage F97 K97cubic 5,
        ∀ a g : K97cubic, P.strategy.Accepts (coinQ a g) cfgD.challenges.lam) ∧
      (packageQ hfirstD).strategy.Accepts (coinQ 0 0) cfgD.challenges.lam ∧
      (packageQ hfirstD).strategy.Accepts (coinQ alphaCN gammaN) cfgD.challenges.lam :=
  ⟨packageQ_accepts hfirstD hrootAt, ⟨packageQ hfirstD, packageQ_accepts hfirstD hrootAt⟩,
    packageQ_accepts hfirstD hrootAt 0 0, packageQ_accepts hfirstD hrootAt alphaCN gammaN⟩

/-- A direct identity control at two distinct pairs. -/
theorem packageQ_identity_across_distinct_pairs :
    (fun _ _ : K97cubic => packageQ hfirstD) 0 0 =
      (fun _ _ : K97cubic => packageQ hfirstD) alphaCN gammaN ∧
    alphaCN ≠ 0 ∧ gammaN ≠ 0 :=
  ⟨rfl, alphaCN_ne_zero, gammaN_ne_zero⟩

/-- The pre-coin commitment is definitionally identical at arbitrary walk coins. -/
theorem precoin_commitment_is_fixed
    (a g a' g' : K97cubic) :
    (rawStrategyQ hfirstD).alphaMCommitment (coinQ a g) cfgD.challenges.lam seedH_ne =
      (rawStrategyQ hfirstD).alphaMCommitment (coinQ a' g') cfgD.challenges.lam seedH_ne :=
  rfl

/-! ## B. Mixed-assignment provenance and a verifier-read moving column -/

/-- Exact provenance of all six assignment families: table/IO data are the `(0,0)` reference
terms, while both walk traces are the sampled pair's terms. -/
theorem mixed_assignment_exact_provenance (a g : K97cubic) :
    (mixedAssignmentQ hfirstD a g).computeTableTrace =
        (assignmentQ hfirstD 0 0).computeTableTrace ∧
      (mixedAssignmentQ hfirstD a g).memoryTableTrace =
        (assignmentQ hfirstD 0 0).memoryTableTrace ∧
      (mixedAssignmentQ hfirstD a g).computeIOTrace =
        (assignmentQ hfirstD 0 0).computeIOTrace ∧
      (mixedAssignmentQ hfirstD a g).memoryIOTrace =
        (assignmentQ hfirstD 0 0).memoryIOTrace ∧
      (mixedAssignmentQ hfirstD a g).computeWalkTrace =
        (assignmentQ hfirstD a g).computeWalkTrace ∧
      (mixedAssignmentQ hfirstD a g).memoryWalkTrace =
        (assignmentQ hfirstD a g).memoryWalkTrace ∧
      (mixedAssignmentQ hfirstD a g).Satisfies :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, mixedAssignmentQ_satisfies hfirstD a g⟩

/-- `computeLn 1` is read by `WalkSat.ln1` through the accepted compute-walk RAP.  It is zero at
the zero coin and `2` at the nonzero coin, so the moving output is not a dead record field. -/
theorem verifier_read_walk_column_moves :
    (walkArraysQ hfirstD (coinQ 0 0) cfgD.challenges.lam seedH_ne).computeLn 1 = 0 ∧
      (walkArraysQ hfirstD (coinQ alphaCN gammaN) cfgD.challenges.lam seedH_ne).computeLn 1 = alphaCN ∧
      (walkArraysQ hfirstD (coinQ 0 0) cfgD.challenges.lam seedH_ne).computeLn 1 ≠
        (walkArraysQ hfirstD (coinQ alphaCN gammaN) cfgD.challenges.lam seedH_ne).computeLn 1 := by
  have hsix0 :=
    ((rawStrategyQ hfirstD).accepts_iff_six_families (coinQ 0 0) cfgD.challenges.lam seedH_ne).1
      (rawStrategyQ_accepts hfirstD 0 0)
  have hsixN :=
    ((rawStrategyQ hfirstD).accepts_iff_six_families (coinQ alphaCN gammaN) cfgD.challenges.lam seedH_ne).1
      (rawStrategyQ_accepts hfirstD alphaCN gammaN)
  have hcert0 :=
    (((rawStrategyQ hfirstD).messageAt (coinQ 0 0) cfgD.challenges.lam seedH_ne).computeWalkRAP_wholeTrace_iff).1
      hsix0.2.2.2.1
  have hcertN :=
    (((rawStrategyQ hfirstD).messageAt (coinQ alphaCN gammaN) cfgD.challenges.lam seedH_ne).computeWalkRAP_wholeTrace_iff).1
      hsixN.2.2.2.1
  have h0 := hcert0.1.ln1
  have hN := hcertN.1.ln1
  change (walkArraysQ hfirstD (coinQ 0 0) cfgD.challenges.lam seedH_ne).computeLn 1 = 0 at h0
  change
    (walkArraysQ hfirstD (coinQ alphaCN gammaN) cfgD.challenges.lam seedH_ne).computeLn 1 = alphaCN at hN
  refine ⟨h0, hN, ?_⟩
  intro heq
  exact alphaCN_ne_zero (hN.symm.trans (heq.symm.trans h0))

/-! ## C. -/

/-- Thus the isolated walk predicate is discriminating at the accepted `(2,5)` coin. -/
theorem nonzero_pair_leaves_zero_walk_degeneracy :
    alphaC (coinQ alphaCN gammaN) = alphaCN ∧
      gamma (coinQ alphaCN gammaN) = gammaN ∧
      alphaCN ≠ 0 ∧ gammaN ≠ 0 ∧
      (∃ ln count acc : ℕ → K97cubic,
        WalkSat alteredCurN alteredChildN alteredFanoutN ln count acc 0
          (alteredCurN 1 * 0) 0 2 ∧ acc 2 = 0) ∧
      ¬ ∃ ln count acc : ℕ → K97cubic,
        WalkSat alteredCurN alteredChildN alteredFanoutN ln count acc
          (alphaC (coinQ alphaCN gammaN))
          (alteredCurN 1 * alphaC (coinQ alphaCN gammaN))
          (alphaC (coinQ alphaCN gammaN)) 2 ∧ acc 2 = 0 :=
  ⟨rfl, rfl, alphaCN_ne_zero, gammaN_ne_zero,
    altered_non_bft_walk_accepts_at_zero.2,
    altered_non_bft_walk_rejected_at_alphaCN.2⟩

/-! ## D. Exact committed fibre, census, and collision exclusion -/

/-- The `coinQ` image is exactly the committed seed/`alphaM` fibre.  The production theorem is
therefore walk-challenge completeness, not completeness over the full joint coin space. -/
theorem coinQ_image_iff_committed_fibre (ω : JointCoins K97cubic) :
    ω ∈ Finset.univ.image
        (fun pair : K97cubic × K97cubic => coinQ pair.1 pair.2) ↔
      nprSeed ω = seedD ∧ alphaM ω = alphaD := by
  constructor
  · intro h
    obtain ⟨pair, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨rfl, rfl⟩
  · rintro ⟨hz, hα⟩
    apply Finset.mem_image.mpr
    refine ⟨(alphaC ω, gamma ω), Finset.mem_univ _, ?_⟩
    rcases ω with ⟨⟨a, g⟩, ⟨m, z⟩⟩
    simp only [nprSeed, alphaM] at hz hα
    subst z
    subst m
    rfl

/-- The same consumed package, statement, and production target retain the genuinely unequal
`([7 9],[8 10])` pair; no residual phase diagonalizes it. -/
theorem consumed_census_and_target_are_same_object (a g : K97cubic) :
    (packageQ hfirstD).optimized.census = censusD ∧
      (∃ i : Fin (packageQ hfirstD).optimized.census.census.count,
        (packageQ hfirstD).optimized.census.census.pair i =
            (operandLeft, operandRight) ∧
          ((packageQ hfirstD).optimized.census.census.pair i).1 ≠
            ((packageQ hfirstD).optimized.census.census.pair i).2) ∧
      ProductionP8Containment.GenuineTargetAt (packageQ hfirstD).strategy 97 7
        (coinQ a g) cfgD.challenges.lam :=
  ⟨rfl, packageQ_consumed_census_has_genuine_distinct_pair hfirstD hrootAt, genuineTargetQ hfirstD hrootAt a g⟩

/-- Seed-8 collision exclusion is pair-substantive and independent of the walk coordinates;
the same consumed census enters the event at its unique bad seed `-1`. -/
theorem collision_exclusion_is_pair_substantive_and_walk_independent
    (a g a' g' : K97cubic) :
    OpcodeSemantics.PairFaithful seedD 97 operandLeft operandRight ∧
      coinQ a g ∉ collisionFailureEvent (packageQ hfirstD).optimized.census.census ∧
      ((((a, g), (alphaD, -1)) : JointCoins K97cubic) ∈
          collisionFailureEvent (packageQ hfirstD).optimized.census.census) ∧
      ((((a, g), (alphaD, -1)) : JointCoins K97cubic) ∈
          collisionFailureEvent (packageQ hfirstD).optimized.census.census ↔
        (((a', g'), (alphaD, -1)) : JointCoins K97cubic) ∈
          collisionFailureEvent (packageQ hfirstD).optimized.census.census) := by
  refine ⟨operands_pairFaithful, coinQ_not_collisionFailureEvent hfirstD hrootAt a g, ?_, ?_⟩
  · rw [mem_collisionFailureEvent_iff]
    obtain ⟨i, hi, _⟩ := packageQ_consumed_census_has_genuine_distinct_pair hfirstD hrootAt
    exact ⟨i, by rw [hi]; exact operands_not_sepSeed_at_neg_one⟩
  · simp only [mem_collisionFailureEvent_iff, nprSeed]

/-! ## E. Package-relative accounting and capstone scope -/

/-- The new universal walk-pair quantifier changes no field of the fourteen-field statement.
At `packageQ`, production containment is inhabited while the accepted canonical optimized tuple
is inside its failure event.  The earlier package-relative counts remain unchanged. -/
theorem package_relative_accounting_is_unchanged
    (haxQ : FormRAxisBound (packageQ hfirstD).optimized.sampled (packageQ hfirstD).optimized.basis)
    (hbasisQ : FormRBasis (packageQ hfirstD).optimized.basis)
    (hwidthQ : FormRWidth F97)
    (haxD : FormRAxisBound (packageD hfirstD).optimized.sampled (packageD hfirstD).optimized.basis)
    (hbasisD : FormRBasis (packageD hfirstD).optimized.basis)
    (hwidthD : FormRWidth F97)
    (haxH : FormRAxisBound (packageH hfirstD).optimized.sampled (packageH hfirstD).optimized.basis)
    (hbasisH : FormRBasis (packageH hfirstD).optimized.basis)
    (hwidthH : FormRWidth F97)
    (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled (packageP hmoreM).optimized.basis)
    (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
    (hwidthP : FormRWidth F97) :
    (8 + 1 + 5 = 14) ∧
      Nonempty (OptimizedFullStrictThm54Statement (packageQ hfirstD)) ∧
      (∀ a g : K97cubic,
        (packageQ hfirstD).strategy.Accepts (coinQ a g) cfgD.challenges.lam ∧
          coinQ a g ∉ FailureUnion (packageQ hfirstD).strategy (packageQ hfirstD).optimized.census cfgD.challenges.lam ∧
          GenuineTargetAt (packageQ hfirstD).strategy 97 7 (coinQ a g) cfgD.challenges.lam) ∧
      (7 + 1 + 6 = 14) ∧
      Nonempty (OptimizedFullStrictThm54Statement (packageD hfirstD)) ∧
      (8 + 1 + 5 = 14) ∧
      Nonempty (OptimizedFullStrictThm54Statement (packageH hfirstD)) ∧
      (9 + 1 + 4 = 14) ∧
      Nonempty (OptimizedFullStrictThm54Statement (packageP hmoreM)) :=
  ⟨by norm_num, ⟨statementQ hfirstD haxQ hbasisQ hwidthQ⟩,
    fun a g => ⟨packageQ_accepts hfirstD hrootAt a g, coinQ_not_failureUnion hfirstD hrootAt a g, genuineTargetQ hfirstD hrootAt a g⟩,
    by norm_num, ⟨statementD hfirstD haxD hbasisD hwidthD⟩, by norm_num,
    ⟨statementH hfirstD haxH hbasisH hwidthH⟩,
    by norm_num, ⟨statementP hmoreM haxP hbasisP hwidthP⟩⟩

/-- Wrong-layer control: the negative optimized fact is reproduced on the exact package consumed
by `OptimizedFullStrictThm54Statement (packageQ hfirstD)`, not only on a walk or idealized tree.

The control's point — that
the negative fact is reproduced at the consumed package rather than at an idealized object — is
unchanged, and the first two conjuncts are untouched. -/
theorem consumed_capstone_has_accepted_tuple_inside_historical_compute_failure
    (haxQ : FormRAxisBound (packageQ hfirstD).optimized.sampled (packageQ hfirstD).optimized.basis)
    (hbasisQ : FormRBasis (packageQ hfirstD).optimized.basis)
    (hwidthQ : FormRWidth F97)
    (a g : K97cubic) :
    OptimizedFullStrictThm54Statement (packageQ hfirstD) ∧
      (packageQ hfirstD).OptimizedHistoricalAcceptanceAt (computeTraceQ hfirstD) (memoryTraceQ hfirstD) (tupleQ hfirstD a g) ∧
      (0 : F97) ∈
        finalSelectorBadChallenges ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)) :=
  ⟨statementQ hfirstD haxQ hbasisQ hwidthQ,
    accepted_optimized_tuple_is_inside_historical_compute_failure hfirstD hrootAt a g haxQ hbasisQ hwidthQ⟩

/-! ## F. Zero-fold obstruction versus arbitrary chip input -/

theorem zero_fold_obstruction_is_real_at_packageQ
    (haxQ : FormRAxisBound (packageQ hfirstD).optimized.sampled (packageQ hfirstD).optimized.basis)
    (hbasisQ : FormRBasis (packageQ hfirstD).optimized.basis)
    (hwidthQ : FormRWidth F97)
    (a g : K97cubic) :
    computeChallenge (distinctCensusExecution hfirstD) (inputsD hfirstD)
        OptimizedComputeSubstitution.finalScalarChallengeBase = 0 ∧
      (0 : F97) ∈
        finalSelectorBadChallenges ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)) ∧
      (packageQ hfirstD).OptimizedHistoricalAcceptanceAt (computeTraceQ hfirstD) (memoryTraceQ hfirstD) (tupleQ hfirstD a g) :=
  ⟨computeChallenge_slot36 (distinctCensusExecution hfirstD) (inputsD hfirstD),
    (accepted_optimized_tuple_is_inside_historical_compute_failure hfirstD hrootAt a g haxQ hbasisQ hwidthQ).2,
    (accepted_optimized_tuple_is_inside_historical_compute_failure hfirstD hrootAt a g haxQ hbasisQ hwidthQ).1⟩

/-- Every terminal-selector error is the difference between the first `s5` one-hot vector and
the last `s1` one-hot vector. -/
theorem packageQ_selector31_error_value (j : Fin 11) :
    ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)).trace (j : ℕ) -
        ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)).pub (31 + (j : ℕ)) =
      (if j = 1 then -1 else if j = 5 then 1 else 0) := by
  rw [canonical_scalarEnv_trace (packageQ hfirstD)]
  have hp := (packageQ hfirstD).optimized.computePublicPins.2.2 j
  have hp' :
      ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)).pub (31 + (j : ℕ)) =
        (if j = OptimizedComputeCodec.stateIndex
            ((packageQ hfirstD).optimized.family.problem.exec.computePubAt
              ⟨(packageQ hfirstD).optimized.family.problem.cfg.compRows - 1,
                Nat.sub_lt (packageQ hfirstD).optimized.family.problem.cfg.compRows_pos
                  Nat.one_pos⟩).state then 1 else 0) := by
    change (packageQ hfirstD).optimized.computePublic (31 + (j : ℕ)) = _
    simpa using hp
  rw [hp', packageQ_first_state hfirstD hrootAt, packageQ_last_state hfirstD hrootAt]
  fin_cases j <;> norm_num [OptimizedComputeCodec.stateIndex] <;> decide

/-- Scalar challenge `2` is not a root of the `s5` versus `s1` selector polynomial
`-X + X^5`.  Hence the zero root is avoidable at the chip-input layer. -/
theorem two_is_not_packageQ_selector_bad :
    (2 : F97) ∉ finalSelectorBadChallenges
      ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)) := by
  have h20 :
      selectorBadChallenges ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)) 20 = ∅ := by
    unfold selectorBadChallenges
    exact valueBadChallenges_eq_empty_of_all_zero _
      (canonical_selector20_zero (packageQ hfirstD))
  rw [finalSelectorBadChallenges, h20, Finset.empty_union]
  unfold selectorBadChallenges valueBadChallenges
  split
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hroot
    rw [show selectorErrors ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)) 31 =
      [0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0] by
        simp only [selectorErrors]
        congr 1
        · simpa using packageQ_selector31_error_value hfirstD hrootAt 0
        · congr 1
          · simpa using packageQ_selector31_error_value hfirstD hrootAt 1
          · congr 1
            · simpa using packageQ_selector31_error_value hfirstD hrootAt 2
            · congr 1
              · simpa using packageQ_selector31_error_value hfirstD hrootAt 3
              · congr 1
                · simpa using packageQ_selector31_error_value hfirstD hrootAt 4
                · congr 1
                  · simpa using packageQ_selector31_error_value hfirstD hrootAt 5
                  · congr 1
                    · simpa using packageQ_selector31_error_value hfirstD hrootAt 6
                    · congr 1
                      · simpa using packageQ_selector31_error_value hfirstD hrootAt 7
                      · congr 1
                        · simpa using packageQ_selector31_error_value hfirstD hrootAt 8
                        · congr 1
                          · simpa using packageQ_selector31_error_value hfirstD hrootAt 9
                          · congr 1
                            · simpa using packageQ_selector31_error_value hfirstD hrootAt 10] at hroot
    norm_num [valueRlcPolynomial] at hroot
    exact (by decide : (30 : F97) ≠ 0) hroot
  · simp

/-- Keep challenges 9 and 11 canonical. -/
def alternateComputeChallengesQ : FinalComputeChallengeTuple K97cubic := default

/-- At the fixed `packageQ` environments this tuple is outside the consumed two-lift compute
collision event: challenges 9 and 11 keep their generic canonical exclusions (the third
component, `two_is_not_packageQ_selector_bad`, is kept above as the value-level history of the
deleted coordinate).  This is a chip-input fact, not alternate package acceptance. -/
theorem alternate_compute_tuple_outside_current_compute_event :
    alternateComputeChallengesQ ∉
      extensionFinalComputeCollisionEvent
        ((packageQ hfirstD).computeSourceEnv (computeTraceQ hfirstD))
        ((packageQ hfirstD).computeWalkEnv (computeTraceQ hfirstD)) := by
  simp [extensionFinalComputeCollisionEvent]

def alternateInputsQ : Inputs (distinctCensusExecution hfirstD) :=
  (inputsD hfirstD).withComputeChallenges alternateComputeChallengesQ

/-- `Inputs` accepts the alternate tuple without changing any semantic execution, walk, orbit,
IO, memory, or basis datum. -/
theorem alternate_input_changes_only_compute_challenges :
    (alternateInputsQ hfirstD).computeChallenges = alternateComputeChallengesQ ∧
      (alternateInputsQ hfirstD).computeWalkAlpha = (inputsD hfirstD).computeWalkAlpha ∧
      (alternateInputsQ hfirstD).memoryWalkAlpha = (inputsD hfirstD).memoryWalkAlpha ∧
      (alternateInputsQ hfirstD).walkGamma = (inputsD hfirstD).walkGamma ∧
      (alternateInputsQ hfirstD).hOrb = (inputsD hfirstD).hOrb ∧
      (alternateInputsQ hfirstD).ioCoins = (inputsD hfirstD).ioCoins ∧
      (alternateInputsQ hfirstD).memoryScalarChallenge = (inputsD hfirstD).memoryScalarChallenge ∧
      (alternateInputsQ hfirstD).memoryExtensionFold = (inputsD hfirstD).memoryExtensionFold :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem alternate_chip_input_is_satisfying_and_writes_two
    (hax : FormRAxisBound
      (sampledAssignment (distinctCensusExecution hfirstD) (alternateInputsQ hfirstD))
      (alternateInputsQ hfirstD).basis)
    (hbasis : FormRBasis (alternateInputsQ hfirstD).basis)
    (hwidth : FormRWidth F97)
    (hhalt : MemoryHaltLeavesHonest.HaltRowsBase (F := F97)
      (distinctCensusExecution hfirstD).exec) :
    BuildableTraceSatisfaction
        (buildTopology (distinctCensusExecution hfirstD) (alternateInputsQ hfirstD))
        (buildTraces (distinctCensusExecution hfirstD) (alternateInputsQ hfirstD)) ∧
      computeChallenge (distinctCensusExecution hfirstD) (alternateInputsQ hfirstD)
        OptimizedComputeSubstitution.finalScalarChallengeBase = 0 :=
  ⟨buildTraceSatisfaction (distinctCensusExecution hfirstD) (alternateInputsQ hfirstD)
      (by
        change (DistinctCensusExecution.execD.computePubAt
          ⟨0, DistinctCensusExecution.cfgD.compRows_pos⟩).ln_prev = 1
        rw [DistinctCensusExecution.computePubAtD_zero]
        rfl)
      DistinctCensusC1.pairedRecordLayout_distinctCensus
      (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD)
        (by simp [distinctCensusExecution]; decide))
      (hord := fun _ => by
        have hα : (alternateInputsQ hfirstD).computeWalkAlpha = (2 : K97cubic) := rfl
        have hrows : (distinctCensusExecution hfirstD).cfg.compRows = 3 := rfl
        rw [hα, omega2_order, hrows]
        norm_num)
      (hordM := fun _ => by
        have hα : (alternateInputsQ hfirstD).memoryWalkAlpha = (3 : K97cubic) := rfl
        have hrows : (distinctCensusExecution hfirstD).cfg.memRows = 21 := rfl
        rw [hα, omega3_order, hrows]
        norm_num)
      DistinctCensusExecution.execD_cprimeCoherent
      hax hbasis hwidth hhalt,
    computeChallenge_slot36 (distinctCensusExecution hfirstD) (alternateInputsQ hfirstD)⟩

theorem current_full_package_builder_requires_zero :
    (∀ (I : Inputs (distinctCensusExecution hfirstD))
      (R : BuildablePackage.CommitmentResidual (distinctCensusExecution hfirstD)),
      I.computeChallenges = default →
        (2 ≤ (distinctCensusExecution hfirstD).cfg.compRows →
          (distinctCensusExecution hfirstD).cfg.compRows ≤ orderOf I.computeWalkAlpha) →
        (2 ≤ (distinctCensusExecution hfirstD).cfg.memRows →
          (distinctCensusExecution hfirstD).cfg.memRows ≤ orderOf I.memoryWalkAlpha) →
        GeneratedField.ClaimGenerated K97cubic R.verifier.raw.claim R.Λ →
        Nonempty
          (OptimizedFullStrictNockVMROMPackage F97 K97cubic I.hOrb)) ∧
      (alternateInputsQ hfirstD).computeChallenges = default ∧
        canonicalComputeChallengeTuple (packageQ hfirstD) =
          ⟨(packageQ hfirstD).objects.cfg.challenges.a,
            (packageQ hfirstD).objects.cfg.challenges.b,
            (packageQ hfirstD).objects.cfg.challenges.c⟩ := by
  constructor
  · intro I R hzero hord hordM hgenF
    exact ⟨BuildablePackage.buildFullPackage (distinctCensusExecution hfirstD) I R hzero
      DistinctCensusC1.pairedRecordLayout_distinctCensus
      (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD)
        (by simp [distinctCensusExecution]; decide))
      hord hordM (DistinctCensusCommitment.rowsBoundD hfirstD)⟩
  · constructor
    · rfl
    · rfl

/-! ## G. -/

theorem released_aliases_and_control_unchanged :
    @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package ∧
      @«Thm:NockVMROM:forest-control» =
        @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch85.released_aliases_and_control_unchanged

#print axioms one_fixed_package_outside_the_pair_quantifier
#print axioms packageQ_identity_across_distinct_pairs
#print axioms precoin_commitment_is_fixed
#print axioms mixed_assignment_exact_provenance
#print axioms verifier_read_walk_column_moves
#print axioms nonzero_pair_leaves_zero_walk_degeneracy
#print axioms coinQ_image_iff_committed_fibre
#print axioms consumed_census_and_target_are_same_object
#print axioms collision_exclusion_is_pair_substantive_and_walk_independent
#print axioms package_relative_accounting_is_unchanged
#print axioms consumed_capstone_has_accepted_tuple_inside_historical_compute_failure
#print axioms zero_fold_obstruction_is_real_at_packageQ
#print axioms packageQ_selector31_error_value
#print axioms two_is_not_packageQ_selector_bad
#print axioms alternate_compute_tuple_outside_current_compute_event
#print axioms alternate_input_changes_only_compute_challenges
#print axioms alternate_chip_input_is_satisfying_and_writes_two
#print axioms current_full_package_builder_requires_zero
#print axioms released_aliases_and_control_unchanged

#print axioms DistinctCensusPhaseCorrect.packageQ
#print axioms DistinctCensusPhaseCorrect.statementQ
#print axioms DistinctCensusPhaseCorrect.commit_then_sample_completeness
#print axioms DistinctCensusPhaseCorrect.walkArraysQ_is_nonconstant_on_accepted_coins
#print axioms DistinctCensusPhaseCorrect.packageQ_zero_was_a_bad_selector_challenge
#print axioms DistinctCensusPhaseCorrect.accepted_optimized_tuple_is_inside_historical_compute_failure
#print axioms BuildableChips.challenge_substitution_traces_satisfy
#print axioms BuildablePackage.buildFullPackage

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
end Nock.RedTeam.Batch86
