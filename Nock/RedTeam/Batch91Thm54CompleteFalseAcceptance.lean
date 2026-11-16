import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance
import Nock.NockVMROM.Thm54.WalkTilingEvents
import Nock.RedTeam.Batch90Thm54P8Absorption
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Complete false-acceptance bound at the concrete `F97` package R

Checks on the complete false-acceptance bound and its bit projection at the concrete
package `DistinctCensusFold2.packageR` over `F97` / `K97cubic`, together with the
fourteen-field partition of the full strict Theorem 5.4 statement.

Consumed Lean objects:
`DistinctCensusFold2.packageR`,
`OptimizedFullStrictThm54Statement (packageR hfirstD)`, and
`optimizedFullStrictNockVMROM_of_package (packageR hfirstD) hax hbasis hwidth`.

One vacuity qualification is load-bearing: at this concrete
`F97` package the support premise of `complete_false_acceptance_bits` is false
for every `b`, already because `(20 + 14 * memRows) / |F| = 314/97 > 1`.
Thus the two fields classify together only as statements about the same event;
the bit projection has no non-vacuous package-R instance.  The ordinary bound
projection is unconditional.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch91

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Noun Nock.Walk
open Framework Framework.Reify Framework.Thm54
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment
open Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
open Nock.NockVMROM.Thm54.DistinctCensusFold2
open Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
open Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
open Nock.NockVMROM.Thm54.DistinctCensusP8FixedField
open Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97b91 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97b91 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
variable (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
variable (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
variable (hwidthR : FormRWidth F97)
include haxR hbasisR hwidthR
variable (hrootAt : ∀ a g : K97cubic,
  (packageR hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
variable (hrootAtQ : ∀ a g : K97cubic,
  (packageQ hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
include hfirstD
include hrootAt
include hrootAtQ

/-! ## A. Exact event and the conditional bit corollary -/

/-- Both landed projections use the identical package-relative
`OptimizedFalseAcceptanceSet Qc Qm`.  The bit result is obtained from the
ordinary bound by support arithmetic and introduces no second event. -/
theorem same_event_and_bits_derived_from_bound :
    (∀ (Qc : Fin (packageR hfirstD).computeChip.rap.w → F97[X])
        (Qm : Fin (packageR hfirstD).memoryChip.rap.w → F97[X]),
      (((packageR hfirstD).OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
          Fintype.card (OptimizedProductionChallengeTuple K97cubic F97) ≤
        optimizedProductionFailureProbabilityBound
          (Fintype.card K97cubic) (Fintype.card F97)
          (OptimizedFailureEventEv.workloadEv (packageR hfirstD) (packageR hfirstD).optimized.Λ +
            OptimizedHostileTimestamps.timestampCollisionBound
              (3 * (packageR hfirstD).optimized.family.problem.cfg.compRows) +
              pricedWalkWork (packageR hfirstD).optimized.family.problem.cfg.compRows
              (packageR hfirstD).optimized.family.problem.cfg.memRows)
          ((packageR hfirstD).hostileIOWork + (packageR hfirstD).hostileInterWork)
          (packageR hfirstD).optimized.family.problem.cfg.compRows
          (packageR hfirstD).optimized.family.problem.cfg.memRows) ∧
      (∀ (Qc : Fin (packageR hfirstD).computeChip.rap.w → F97[X])
          (Qm : Fin (packageR hfirstD).memoryChip.rap.w → F97[X]) (b : ℕ),
        optimizedProductionFailureProbabilityBound
            (Fintype.card K97cubic) (Fintype.card F97)
            (OptimizedFailureEventEv.workloadEv (packageR hfirstD) (packageR hfirstD).optimized.Λ +
              OptimizedHostileTimestamps.timestampCollisionBound
                (3 * (packageR hfirstD).optimized.family.problem.cfg.compRows) +
                pricedWalkWork (packageR hfirstD).optimized.family.problem.cfg.compRows
              (packageR hfirstD).optimized.family.problem.cfg.memRows)
            ((packageR hfirstD).hostileIOWork + (packageR hfirstD).hostileInterWork)
            (packageR hfirstD).optimized.family.problem.cfg.compRows
            (packageR hfirstD).optimized.family.problem.cfg.memRows * 2 ^ b ≤ 1 →
          (((packageR hfirstD).OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
              Fintype.card (OptimizedProductionChallengeTuple K97cubic F97) ≤
            1 / 2 ^ b) := by
  refine ⟨(packageR hfirstD).optimizedFalseAcceptance_probability_le_legacy haxR hbasisR hwidthR, ?_⟩
  intro Qc Qm b hsupport
  refine ((packageR hfirstD).optimizedFalseAcceptance_probability_le_legacy haxR hbasisR hwidthR Qc Qm).trans ?_
  have hpow : (0 : ℚ) < 2 ^ b := by positivity
  apply (le_div_iff₀ hpow).2
  simpa [mul_comm, OptimizedFullStrictNockVMROMPackage.hostileIOWork] using hsupport

/-! ## B. -/

/-! ## C. Independent consumed-trace replay -/

/-- The acceptance fields themselves pin the complete trace-side challenge
block. -/
theorem independent_acceptance_pins_trace_challenges
    (Qc : Fin (packageR hfirstD).computeChip.rap.w → F97[X])
    (Qm : Fin (packageR hfirstD).memoryChip.rap.w → F97[X])
    (c : OptimizedProductionChallengeTuple K97cubic F97)
    (hacc : (packageR hfirstD).OptimizedHistoricalAcceptanceAt Qc Qm c) :
    c.2 =
      (((packageR hfirstD).optimized.sampled.sampled.coins.gamma,
          (packageR hfirstD).optimized.sampled.sampled.coins.pole),
        (c.2.2.1, ⟨(canonicalMemoryChallengeTuple (packageR hfirstD)).interPole,
          c.2.2.2.lambda⟩)) := by
  refine Prod.ext hacc.sampled_io_coins (Prod.ext rfl ?_)
  exact memoryChallengeTuple_ext (by
    have h := hacc.memory_intermediate_pole ⟨0, (packageR hfirstD).optimized.family.problem.cfg.memRows_pos⟩
    have hcan := (canonicalTraceAcceptance (packageR hfirstD) (hmoreR hfirstD)
        DistinctCensusExecution.execD_cprimeCoherent
      haxR hbasisR hwidthR).memory_intermediate_pole
      ⟨0, (packageR hfirstD).optimized.family.problem.cfg.memRows_pos⟩
    exact ⟨h.symm.trans hcan, rfl⟩)

/-- Same-problem pins the coin and the acceptance fields pin the tail, so an
accepted tuple at arbitrary candidate traces is the package-R canonical tuple. -/
theorem independent_accepted_tuple_is_tupleR
    (Qc : Fin (packageR hfirstD).computeChip.rap.w → F97[X])
    (Qm : Fin (packageR hfirstD).memoryChip.rap.w → F97[X])
    (c : OptimizedProductionChallengeTuple K97cubic F97)
    (hacc : (packageR hfirstD).OptimizedHistoricalAcceptanceAt Qc Qm c) :
    c = (coinQ (alphaC c.1) (gamma c.1),
      (((packageR hfirstD).optimized.sampled.sampled.coins.gamma,
          (packageR hfirstD).optimized.sampled.sampled.coins.pole),
        (c.2.2.1, ⟨(canonicalMemoryChallengeTuple (packageR hfirstD)).interPole,
          c.2.2.2.lambda⟩))) := by
  obtain ⟨hz, hα⟩ := packageR_sameProblem_pins_fibre hfirstD hrootAt hrootAtQ c.1 c.2.2.2.lambda hacc.same_problem
  have hcoin : c.1 = coinQ (alphaC c.1) (gamma c.1) :=
    coin_eq_coinQ_of_fibre hfirstD hrootAt hrootAtQ c.1 hz hα
  exact Prod.ext hcoin (independent_acceptance_pins_trace_challenges
    hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ Qc Qm c hacc)

/-! ## D. The universal stop and package-Q negative control -/

abbrev preprocessingR :=
  compFixedPreprocessingCoreRAP
    (F := F97) (K := K97cubic)
    (packageR hfirstD).optimized.family.problem.cfg.compRows_pos
    (packageR hfirstD).optimized.computeNodes (packageR hfirstD).optimized.basis
    (packageR hfirstD).optimized.computeChallenge (packageR hfirstD).optimized.computePublic
    (packageR hfirstD).optimized.orbit

/-- Fixed preprocessing has exactly two columns, the first/last masks at
physical base columns 11 and 12.  In particular no selector column `0..10` is
in the fixed-preprocessing image. -/
theorem fixed_preprocessing_is_exactly_the_two_masks :
    (preprocessingR hfirstD).fixedCount = 2 ∧
      (((preprocessingR hfirstD).preprocessingColumn
        (compFixedFirstIndex
          (packageR hfirstD).optimized.family.problem.cfg.compRows_pos
          (packageR hfirstD).optimized.computeNodes (packageR hfirstD).optimized.basis
          (packageR hfirstD).optimized.computeChallenge (packageR hfirstD).optimized.computePublic
          (packageR hfirstD).optimized.orbit) : ℕ) = 11) ∧
      (((preprocessingR hfirstD).preprocessingColumn
        (compFixedLastIndex
          (packageR hfirstD).optimized.family.problem.cfg.compRows_pos
          (packageR hfirstD).optimized.computeNodes (packageR hfirstD).optimized.basis
          (packageR hfirstD).optimized.computeChallenge (packageR hfirstD).optimized.computePublic
          (packageR hfirstD).optimized.orbit) : ℕ) = 12) ∧
      ∀ i : Fin (preprocessingR hfirstD).fixedCount,
        11 ≤ ((preprocessingR hfirstD).preprocessingColumn i : ℕ) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i
  change Fin 2 at i
  fin_cases i
  · change 11 ≤ 11
    norm_num
  · change 11 ≤ 12
    norm_num

/-- At package Q, the tuple at coin `(0, 0)` is accepted
(`OptimizedHistoricalAcceptanceAt`), and the scalar coin `0` lies in
`finalSelectorBadChallenges` of the compute scalar environment.

This does not exhibit a nonempty `OptimizedFalseAcceptanceSet` at `packageQ hfirstD`: whether that
set is nonempty is not decided here, and nothing is proved empty. -/
theorem independent_packageQ_accepted_tuple_has_a_bad_scalar_coin
    (haxQ : FormRAxisBound (packageQ hfirstD).optimized.sampled (packageQ hfirstD).optimized.basis)
    (hbasisQ : FormRBasis (packageQ hfirstD).optimized.basis)
    (hwidthQ : FormRWidth F97) :
    (packageQ hfirstD).OptimizedHistoricalAcceptanceAt (computeTraceQ hfirstD) (memoryTraceQ hfirstD) ((tupleQ hfirstD) 0 0) ∧
      (0 : F97) ∈
        finalSelectorBadChallenges ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)) :=
  ⟨packageQ_optimized_acceptance hfirstD hrootAtQ 0 0 haxQ hbasisQ hwidthQ,
    packageQ_zero_was_a_bad_selector_challenge hfirstD hrootAtQ⟩

omit haxR hbasisR hwidthR hrootAt hrootAtQ in
/-- The bit-support premise is impossible for every `b` at package R.  The
memory term alone is `314/97 > 1`, and `2^b ≥ 1`.  This does not affect the
unconditional ordinary bound, but it prevents a non-vacuity PASS for the bit
projection at this concrete package. -/
theorem packageR_complete_bits_support_is_impossible (b : ℕ) :
    ¬ (optimizedProductionFailureProbabilityBound
          (Fintype.card K97cubic) (Fintype.card F97)
          (OptimizedFailureEventEv.workloadEv (packageR hfirstD) (packageR hfirstD).optimized.Λ +
            OptimizedHostileTimestamps.timestampCollisionBound
              (3 * (packageR hfirstD).optimized.family.problem.cfg.compRows) +
              pricedWalkWork (packageR hfirstD).optimized.family.problem.cfg.compRows
              (packageR hfirstD).optimized.family.problem.cfg.memRows)
          ((packageR hfirstD).hostileIOWork + (packageR hfirstD).hostileInterWork)
          (packageR hfirstD).optimized.family.problem.cfg.compRows
          (packageR hfirstD).optimized.family.problem.cfg.memRows * 2 ^ b ≤ 1) := by
  intro h
  have hF : Fintype.card F97 = 97 := by simp [F97]
  have hM : (packageR hfirstD).optimized.family.problem.cfg.memRows = 21 := rfl
  have hthird : (1 : ℚ) < (20 + 14 * 21 : ℚ) / 97 := by norm_num
  have hle :
      (20 + 14 * 21 : ℚ) / 97 ≤
        optimizedProductionFailureProbabilityBound
          (Fintype.card K97cubic) (Fintype.card F97)
          (OptimizedFailureEventEv.workloadEv (packageR hfirstD) (packageR hfirstD).optimized.Λ +
            OptimizedHostileTimestamps.timestampCollisionBound
              (3 * (packageR hfirstD).optimized.family.problem.cfg.compRows) +
              pricedWalkWork (packageR hfirstD).optimized.family.problem.cfg.compRows
              (packageR hfirstD).optimized.family.problem.cfg.memRows)
          ((packageR hfirstD).hostileIOWork + (packageR hfirstD).hostileInterWork)
          (packageR hfirstD).optimized.family.problem.cfg.compRows
          (packageR hfirstD).optimized.family.problem.cfg.memRows := by
    generalize OptimizedFailureEventEv.workloadEv (packageR hfirstD) (packageR hfirstD).optimized.Λ = w
    rw [optimizedProductionFailureProbabilityBound, hF, hM]
    exact le_add_of_nonneg_left (by positivity)
  have hbound :
      (1 : ℚ) <
        optimizedProductionFailureProbabilityBound
          (Fintype.card K97cubic) (Fintype.card F97)
          (OptimizedFailureEventEv.workloadEv (packageR hfirstD) (packageR hfirstD).optimized.Λ +
            OptimizedHostileTimestamps.timestampCollisionBound
              (3 * (packageR hfirstD).optimized.family.problem.cfg.compRows) +
              pricedWalkWork (packageR hfirstD).optimized.family.problem.cfg.compRows
              (packageR hfirstD).optimized.family.problem.cfg.memRows)
          ((packageR hfirstD).hostileIOWork + (packageR hfirstD).hostileInterWork)
          (packageR hfirstD).optimized.family.problem.cfg.compRows
          (packageR hfirstD).optimized.family.problem.cfg.memRows :=
    lt_of_lt_of_le hthird hle
  have hpow : (1 : ℚ) ≤ 2 ^ b := one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2)
  exact not_le_of_gt (one_lt_mul_of_lt_of_le hbound hpow) h

theorem packageR_complete_bits_projection_has_no_applicable_b :
    ¬ ∃ b : ℕ,
      optimizedProductionFailureProbabilityBound
          (Fintype.card K97cubic) (Fintype.card F97)
          (OptimizedFailureEventEv.workloadEv (packageR hfirstD) (packageR hfirstD).optimized.Λ +
            OptimizedHostileTimestamps.timestampCollisionBound
              (3 * (packageR hfirstD).optimized.family.problem.cfg.compRows) +
              pricedWalkWork (packageR hfirstD).optimized.family.problem.cfg.compRows
              (packageR hfirstD).optimized.family.problem.cfg.memRows)
          ((packageR hfirstD).hostileIOWork + (packageR hfirstD).hostileInterWork)
          (packageR hfirstD).optimized.family.problem.cfg.compRows
          (packageR hfirstD).optimized.family.problem.cfg.memRows * 2 ^ b ≤ 1 := by
  rintro ⟨b, hb⟩
  exact packageR_complete_bits_support_is_impossible hfirstD b hb

/-! ## F. -/

inductive ReviewedField
  | structural
  | optimized_chips
  | shared_io
  | perfect_completeness
  | containment
  | walk_bounds
  | p8_fixed_field_soundness
  | p8_fixed_field_bits
  | acceptance_to_target
  | complete_false_acceptance_bound
  | complete_false_acceptance_bits
  | staged_false_acceptance_bound
  | exact_resources
  | row_budgets
  | shared_forest_axis
  deriving DecidableEq

def reviewedSubstantiveFields : List ReviewedField :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets, .shared_forest_axis]

def reviewedTypeSummaryFields : List ReviewedField := [.structural]

def reviewedResidualFields : List ReviewedField :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

omit hfirstD hrootAt hrootAtQ haxR hbasisR hwidthR in
theorem exact_eleven_one_two_partition :
    reviewedSubstantiveFields.length = 11 ∧
      reviewedTypeSummaryFields.length = 1 ∧
      reviewedResidualFields =
        [.complete_false_acceptance_bound, .complete_false_acceptance_bits] ∧
      reviewedResidualFields.length = 2 ∧
      (reviewedSubstantiveFields ++ reviewedTypeSummaryFields ++
        reviewedResidualFields).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

/-! ## G. The three-residual partition -/

/-- The residual fields including the staged false-acceptance bound. -/
def reviewedResidualFields37 : List ReviewedField :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits, .staged_false_acceptance_bound]

omit hrootAt hrootAtQ in
theorem exact_eleven_one_three_partition :
    (reviewedSubstantiveFields.length = 11 ∧
      reviewedTypeSummaryFields.length = 1 ∧
      reviewedResidualFields37 =
        [.complete_false_acceptance_bound, .complete_false_acceptance_bits,
          .staged_false_acceptance_bound] ∧
      reviewedResidualFields37.length = 3 ∧
      (reviewedSubstantiveFields ++ reviewedTypeSummaryFields ++
        reviewedResidualFields37).Nodup ∧
      11 + 1 + 3 = 15) ∧
    (∀ (Qc : PartA12.OptimizedProductionChallengeTuple12 K97cubic F97 → Fin 309 → F97[X])
        (Qm : PartA12.OptimizedProductionChallengeTuple12 K97cubic F97 → Fin (packageR hfirstD).memoryChip.rap.w → F97[X]),
        PartAStaged.StagedTraces12 (packageR hfirstD) Qc Qm →
        ((Finset.univ.filter fun c =>
            PartAStaged.AcceptanceAt309 (packageR hfirstD) (Qc c) (Qm c) c ∧
              ¬ (packageR hfirstD).OptimizedProductionGenuineTargetAt309 (Qc c) (Qm c) c).card : ℚ) /
            Fintype.card (PartA12.OptimizedProductionChallengeTuple12 K97cubic F97) ≤
          PartA12.optimizedHostileProductionFailureProbabilityBound15 (Fintype.card K97cubic) (Fintype.card F97)
            (OptimizedFailureEventEv.workloadEv (packageR hfirstD) (packageR hfirstD).optimized.Λ)
            (FiniteIO.ioFailureUnionBound 10 (3 * (packageR hfirstD).optimized.family.problem.cfg.compRows)
              (packageR hfirstD).optimized.family.problem.cfg.memRows (Fintype.card K97cubic))
            (packageR hfirstD).optimized.family.problem.cfg.compRows (packageR hfirstD).optimized.family.problem.cfg.memRows) ∧
    (∀ (qc : Fin 309 → F97[X]) (qm : Fin (packageR hfirstD).memoryChip.rap.w → F97[X]),
        ((Finset.univ.filter fun c =>
            PartAStaged.AcceptanceAt309 (packageR hfirstD) qc qm c ∧
              ¬ (packageR hfirstD).OptimizedProductionGenuineTargetAt309 qc qm c).card : ℚ) /
            Fintype.card (PartA12.OptimizedProductionChallengeTuple12 K97cubic F97) ≤
          PartA12.optimizedHostileProductionFailureProbabilityBound15 (Fintype.card K97cubic) (Fintype.card F97)
            (OptimizedFailureEventEv.workloadEv (packageR hfirstD) (packageR hfirstD).optimized.Λ)
            (FiniteIO.ioFailureUnionBound 10 (3 * (packageR hfirstD).optimized.family.problem.cfg.compRows)
              (packageR hfirstD).optimized.family.problem.cfg.memRows (Fintype.card K97cubic))
            (packageR hfirstD).optimized.family.problem.cfg.compRows (packageR hfirstD).optimized.family.problem.cfg.memRows) :=
  ⟨by decide,
    fun Qc Qm hst => PartAStaged.staged_false_acceptance_bound12 (packageR hfirstD)
      (packageR hfirstD).OptimizedProductionGenuineTargetAt309
      (statementR hfirstD haxR hbasisR hwidthR).acceptance_to_target Qc Qm hst,
    fun qc qm => PartAStaged.complete_false_acceptance_bound_of_staged12 (packageR hfirstD)
      (packageR hfirstD).OptimizedProductionGenuineTargetAt309
      (statementR hfirstD haxR hbasisR hwidthR).acceptance_to_target qc qm⟩

theorem statementR_fourteen_field_eta :
    statementR hfirstD haxR hbasisR hwidthR =
      { structural := (statementR hfirstD haxR hbasisR hwidthR).structural
        optimized_chips := (statementR hfirstD haxR hbasisR hwidthR).optimized_chips
        shared_io := (statementR hfirstD haxR hbasisR hwidthR).shared_io
        perfect_completeness := (statementR hfirstD haxR hbasisR hwidthR).perfect_completeness
        containment := (statementR hfirstD haxR hbasisR hwidthR).containment
        walk_bounds := (statementR hfirstD haxR hbasisR hwidthR).walk_bounds
        p8_fixed_field_soundness := (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_soundness
        p8_fixed_field_bits := (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_bits
        acceptance_to_target := (statementR hfirstD haxR hbasisR hwidthR).acceptance_to_target
        complete_false_acceptance_bound :=
          (statementR hfirstD haxR hbasisR hwidthR).complete_false_acceptance_bound
        complete_false_acceptance_bits :=
          (statementR hfirstD haxR hbasisR hwidthR).complete_false_acceptance_bits
        staged_false_acceptance_bound :=
          (statementR hfirstD haxR hbasisR hwidthR).staged_false_acceptance_bound
        exact_resources := (statementR hfirstD haxR hbasisR hwidthR).exact_resources
        row_budgets := (statementR hfirstD haxR hbasisR hwidthR).row_budgets
        shared_forest_axis := (statementR hfirstD haxR hbasisR hwidthR).shared_forest_axis } := by
  cases (statementR hfirstD haxR hbasisR hwidthR)
  rfl

theorem frozen_capstone_and_alias :
    OptimizedFullStrictThm54Statement (packageR hfirstD) ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  ⟨optimizedFullStrictNockVMROM_of_package (packageR hfirstD) haxR hbasisR hwidthR, rfl⟩


#print axioms same_event_and_bits_derived_from_bound
#print axioms exact_eleven_one_three_partition
#print axioms independent_acceptance_pins_trace_challenges
#print axioms independent_accepted_tuple_is_tupleR
#print axioms fixed_preprocessing_is_exactly_the_two_masks
#print axioms independent_packageQ_accepted_tuple_has_a_bad_scalar_coin
#print axioms packageR_complete_bits_support_is_impossible
#print axioms packageR_complete_bits_projection_has_no_applicable_b
#print axioms exact_eleven_one_two_partition
#print axioms statementR_fourteen_field_eta
#print axioms frozen_capstone_and_alias

#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.packageR
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.statementR

end
end Nock.RedTeam.Batch91
