import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.DistinctCensusP8FixedField
import Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
import Nock.NockVMROM.Thm54.MultiRootServedFixture
import Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
import Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Complete optimized false-acceptance classification at `(packageR hfirstD)`

The
theorems below are phrased at the `61·M` bound and obtained
through `complete_false_acceptance_bound_legacy` / `_bits_legacy`.
The vacuity argument at F97 turns on the base-field `(20 + 14M)/97` term.
The question is whether the optimized false-acceptance set is
empty at the field's actual quantification `∀ Qc Qm`.

The bit-support statement is
the Goldilocks 121-bit claim, not a non-vacuous
`1/2^b` instance at `|F|=97`.  This module records that qualification
without editing `OptimizedFullStrictThm54Statement` and without taking
`q` to be Goldilocks.

What this module compiles:
* the two fields quantify the same set; bound is contentful, bits is
  vacuous at `(packageR hfirstD).q = 97`;
* challenge maps are independent of the candidate traces, so optimized
  acceptance at *any* `(Qc, Qm)` pins the tuple to `tupleR`;
* at the exhibited canonical traces the optimized set is empty;
* `∀ Qc Qm` emptiness is **not** established here: compute/memory collision
  events still read the candidate traces, and preprocessing binds only the
  two mask columns `11/12`.

The accounting is `11 + 1 + 2` conjuncts, with the residual pair
(contentful bound, vacuous-at-F97 bits rewrite).  Whole-joint completeness,
generic `CommitmentResidual`, and any
selector challenge are out of scope.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Noun Nock.Walk
open Framework Framework.Reify Framework.Thm54
open Nock.Reified
open SemanticStrategy SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment
open Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
open Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
open Nock.NockVMROM.Thm54.DistinctCensusFold2
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.DistinctCensusP8FixedField
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97cfa : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97cfa : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
variable (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
variable (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
variable (hwidthR : FormRWidth F97)
include hfirstD
variable (hrootAt : ∀ a g : K97cubic,
  (packageR hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
include hrootAt
variable (hrootAtQ : ∀ a g : K97cubic,
  (packageQ hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
include hrootAtQ

variable (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)

variable (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
    (packageP hmoreM).optimized.basis)
variable (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
variable (hwidthP : FormRWidth F97)

def hmoreR :
    ∀ i : Fin (packageR hfirstD).optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < (packageR hfirstD).optimized.family.problem.cfg.kMem →
        ((packageR hfirstD).optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          ((packageR hfirstD).optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0 :=
  BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD)
    (by change 1 ≤ 1; trivial)

/-! ## A. The two statement fields name the same set

Both quantify over `OptimizedFalseAcceptanceSet Qc Qm`.  The bit field adds only the support
arithmetic.  They share the event, but do not
have equal non-vacuous content at this fixture. -/

theorem statementR_complete_false_acceptance_bound
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97)
    (Qc : Fin (packageR hfirstD).computeChip.rap.w → F97[X])
    (Qm : Fin (packageR hfirstD).memoryChip.rap.w → F97[X]) :
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
        (packageR hfirstD).optimized.family.problem.cfg.memRows :=
  (packageR hfirstD).optimizedFalseAcceptance_probability_le_legacy haxR hbasisR hwidthR Qc Qm

theorem statementR_complete_false_acceptance_bits
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97)
    (Qc : Fin (packageR hfirstD).computeChip.rap.w → F97[X])
    (Qm : Fin (packageR hfirstD).memoryChip.rap.w → F97[X]) (b : ℕ)
    (hsupport :
      optimizedProductionFailureProbabilityBound
          (Fintype.card K97cubic) (Fintype.card F97)
          (OptimizedFailureEventEv.workloadEv (packageR hfirstD) (packageR hfirstD).optimized.Λ +
            OptimizedHostileTimestamps.timestampCollisionBound
              (3 * (packageR hfirstD).optimized.family.problem.cfg.compRows) +
              pricedWalkWork (packageR hfirstD).optimized.family.problem.cfg.compRows
              (packageR hfirstD).optimized.family.problem.cfg.memRows)
          ((packageR hfirstD).hostileIOWork + (packageR hfirstD).hostileInterWork)
          (packageR hfirstD).optimized.family.problem.cfg.compRows
          (packageR hfirstD).optimized.family.problem.cfg.memRows * 2 ^ b ≤ 1) :
    (((packageR hfirstD).OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple K97cubic F97) ≤
      1 / 2 ^ b :=
  (packageR hfirstD).optimizedFalseAcceptance_probability_le_two_pow_neg_legacy haxR hbasisR hwidthR Qc Qm b hsupport

theorem complete_fields_share_the_exact_false_acceptance_set
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97) :
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
            1 / 2 ^ b) :=
  ⟨(packageR hfirstD).optimizedFalseAcceptance_probability_le_legacy haxR hbasisR hwidthR,
    (packageR hfirstD).optimizedFalseAcceptance_probability_le_two_pow_neg_legacy haxR hbasisR hwidthR⟩

/-! ## B. Challenge maps ignore the candidate traces

`envOfTrace` stores `chalVal` / `pubVal` from the package, not from `Qc`.  Gathered environments read only the challenge
field. -/

theorem computeSourceEnv_chal_independent
    (Qc Qc' : Fin (packageR hfirstD).computeChip.rap.w → F97[X])
    (i : Fin (packageR hfirstD).optimized.family.problem.cfg.compRows) :
    ((packageR hfirstD).computeSourceEnv Qc i).chal =
      ((packageR hfirstD).computeSourceEnv Qc' i).chal :=
  rfl

theorem computeScalarEnv_chal_independent
    (Qc Qc' : Fin (packageR hfirstD).computeChip.rap.w → F97[X]) :
    ((packageR hfirstD).computeScalarEnv Qc).chal =
      ((packageR hfirstD).computeScalarEnv Qc').chal :=
  rfl

theorem memoryBaseEnv_chal_independent
    (Qm Qm' : Fin (packageR hfirstD).memoryChip.rap.w → F97[X])
    (i : Fin (packageR hfirstD).optimized.family.problem.cfg.memRows) :
    ((packageR hfirstD).memoryBaseEnv Qm i).chal =
      ((packageR hfirstD).memoryBaseEnv Qm' i).chal :=
  rfl

theorem memorySourceEnv_chal_independent
    (Qm Qm' : Fin (packageR hfirstD).memoryChip.rap.w → F97[X])
    (i : Fin (packageR hfirstD).optimized.family.problem.cfg.memRows) :
    ((packageR hfirstD).memorySourceEnv Qm i).chal =
      ((packageR hfirstD).memorySourceEnv Qm' i).chal :=
  rfl

/-- Optimized acceptance at an arbitrary trace pair pins the whole
trace-side challenge block to the package's canonical tuple. -/
theorem packageR_optimized_acceptance_pins_tuple
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97)
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

/-- Every optimized-accepted tuple, at any traces, is the fibre-canonical
`tupleR`.  Same-problem pins the coin; the challenge fields pin the tail. -/
theorem packageR_accepted_tuple_is_canonical
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97)
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
  have htail := packageR_optimized_acceptance_pins_tuple hfirstD hrootAt hrootAtQ haxR hbasisR hwidthR Qc Qm c hacc
  have hcoin : c.1 = coinQ (alphaC c.1) (gamma c.1) :=
    coin_eq_coinQ_of_fibre hfirstD hrootAt hrootAtQ c.1 hz hα
  exact Prod.ext hcoin htail

/-! ## C.

Those two events ignore the candidate traces.  The remaining compute and
memory collision events do not. -/

theorem packageR_accepted_excludes_p8_and_io
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97)
    (Qc : Fin (packageR hfirstD).computeChip.rap.w → F97[X])
    (Qm : Fin (packageR hfirstD).memoryChip.rap.w → F97[X])
    (c : OptimizedProductionChallengeTuple K97cubic F97)
    (hacc : (packageR hfirstD).OptimizedHistoricalAcceptanceAt Qc Qm c) :
    c.1 ∉ ProductionP8Containment.FailureUnion (packageR hfirstD).strategy
        (packageR hfirstD).optimized.census c.2.2.2.lambda ∧
      c.2.1 ∉ FiniteIO.IOFailureEvent (packageR hfirstD).optimized.sampled.sampled.records := by
  have hc := packageR_accepted_tuple_is_canonical hfirstD hrootAt hrootAtQ haxR hbasisR hwidthR Qc Qm c hacc
  have hl : c.2.2.2.lambda = MemoryTable.formRDefault := hacc.same_problem.lam_eq
  constructor
  · rw [hc]
    simpa [tupleR, canonicalProductionTuple, hl] using
      coinR_not_failureUnion hfirstD hrootAt hrootAtQ (alphaC c.1) (gamma c.1)
  · rw [show c.2.1 = ((packageR hfirstD).optimized.sampled.sampled.coins.gamma,
        (packageR hfirstD).optimized.sampled.sampled.coins.pole) from
      congrArg (fun t => t.1) (packageR_optimized_acceptance_pins_tuple hfirstD hrootAt hrootAtQ haxR hbasisR hwidthR Qc Qm c hacc)]
    exact FiniteIO.FiniteIOStrategy.coins_not_failure
      (packageR hfirstD).optimized.sampled.sampled

/-! ## D. Emptiness at the exhibited canonical traces

Emptiness at the canonical traces does not settle
the fields' `∀ Qc Qm` quantifier. -/

/-! ## E. Why `∀ Qc Qm` emptiness is not a 1-1 discharge

Theorem 5.4 claims negligible soundness error, i.e. the union bound carried by the field
types, not uniqueness of satisfying traces.
Fixed preprocessing binds only the two mask columns `11/12`.  Selector columns `0..10` remain free in the
round-zero prefix, so compute/memory collision events still depend on
the candidate traces.

See `packageQ_accepted_with_a_bad_scalar_coin` for the `packageQ` fixture. -/

theorem compute_preprocessing_binds_only_two_masks :
    (compFixedPreprocessingCoreRAP
        (F := F97) (K := K97cubic)
        (packageR hfirstD).optimized.family.problem.cfg.compRows_pos
        (packageR hfirstD).optimized.computeNodes (packageR hfirstD).optimized.basis
        (packageR hfirstD).optimized.computeChallenge (packageR hfirstD).optimized.computePublic
        (packageR hfirstD).optimized.orbit).fixedCount = 2 ∧
      ((compFixedPreprocessingCoreRAP
          (F := F97) (K := K97cubic)
          (packageR hfirstD).optimized.family.problem.cfg.compRows_pos
          (packageR hfirstD).optimized.computeNodes (packageR hfirstD).optimized.basis
          (packageR hfirstD).optimized.computeChallenge (packageR hfirstD).optimized.computePublic
          (packageR hfirstD).optimized.orbit).preprocessingColumn
          (compFixedFirstIndex
            (packageR hfirstD).optimized.family.problem.cfg.compRows_pos
            (packageR hfirstD).optimized.computeNodes (packageR hfirstD).optimized.basis
            (packageR hfirstD).optimized.computeChallenge (packageR hfirstD).optimized.computePublic
            (packageR hfirstD).optimized.orbit) : ℕ) = 11 ∧
      ((compFixedPreprocessingCoreRAP
          (F := F97) (K := K97cubic)
          (packageR hfirstD).optimized.family.problem.cfg.compRows_pos
          (packageR hfirstD).optimized.computeNodes (packageR hfirstD).optimized.basis
          (packageR hfirstD).optimized.computeChallenge (packageR hfirstD).optimized.computePublic
          (packageR hfirstD).optimized.orbit).preprocessingColumn
          (compFixedLastIndex
            (packageR hfirstD).optimized.family.problem.cfg.compRows_pos
            (packageR hfirstD).optimized.computeNodes (packageR hfirstD).optimized.basis
            (packageR hfirstD).optimized.computeChallenge (packageR hfirstD).optimized.computePublic
            (packageR hfirstD).optimized.orbit) : ℕ) = 12 :=
  ⟨rfl, rfl, rfl⟩

/-- At `packageQ`'s canonical traces, the tuple `tupleQ a g` is optimized-accepted, and `0` is a
bad final-selector challenge of the compute scalar environment.

This does not exhibit a nonempty optimized false-acceptance set at `packageQ`, nor prove it
empty: `challenge36` lies in no lift of `OptimizedProductionFailureEvent`, so the
`compute_collision_good` conjunct of `OptimizedProductionGenuineTargetAt` does not see it.
That conjunct is an endpoint payload that nothing consumes as a premise. -/
theorem packageQ_accepted_with_a_bad_scalar_coin (a g : K97cubic)
    (haxQ : FormRAxisBound (packageQ hfirstD).optimized.sampled (packageQ hfirstD).optimized.basis)
    (hbasisQ : FormRBasis (packageQ hfirstD).optimized.basis)
    (hwidthQ : FormRWidth F97) :
    (packageQ hfirstD).OptimizedHistoricalAcceptanceAt (computeTraceQ hfirstD) (memoryTraceQ hfirstD) (tupleQ hfirstD a g) ∧
      (0 : F97) ∈
        finalSelectorBadChallenges ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)) :=
  ⟨packageQ_optimized_acceptance hfirstD hrootAtQ a g haxQ hbasisQ hwidthQ,
    packageQ_zero_was_a_bad_selector_challenge hfirstD hrootAtQ⟩

/-! ## F. Bits support is uninhabited at this F97 fixture

The bits field's exact premise is
`optimizedProductionFailureProbabilityBound * 2^b ≤ 1`
(`complete_false_acceptance_bits`).  At `(packageR hfirstD).q = 97` the base
field is `F97`, so `|F| = 97` and `memRows = 21`.  The memory summand
alone is `(20 + 14·21)/97 = 314/97 > 1`.  The bit-support statement is the
Goldilocks 121-bit claim, not a non-vacuous
instance of this rewrite at `|F|=97`.  The ordinary bound remains
unconditional. -/

/-- Fixture cardinalities used by the bits premise.  `(packageR hfirstD).q`
equals `|F97|` here because `q = ringChar K` and `F = ZMod 97`; the
bits denominator is `|F|`, not a second copy of `q`. -/
theorem packageR_complete_bits_numeric_hypothesis :
    (packageR hfirstD).q = 97 ∧
      Fintype.card F97 = 97 ∧
      (packageR hfirstD).q = Fintype.card F97 ∧
      (packageR hfirstD).optimized.family.problem.cfg.memRows = 21 ∧
      ((20 + 14 * (packageR hfirstD).optimized.family.problem.cfg.memRows : ℚ) /
        Fintype.card F97 = (314 / 97 : ℚ)) ∧
      (314 / 97 : ℚ) > 1 := by
  have hF : Fintype.card F97 = 97 := by simp [F97]
  have hq : (packageR hfirstD).q = 97 := (packageR_q_Λ hfirstD hrootAt hrootAtQ).1
  have hM : (packageR hfirstD).optimized.family.problem.cfg.memRows = 21 := rfl
  refine ⟨hq, hF, ?_, hM, ?_, ?_⟩
  · rw [hq, hF]
  · rw [hF, hM]
    norm_num
  · norm_num

/-- The bit-support premise is impossible for every `b` at package R.
The memory term alone is `314/97 > 1`, and `2^b ≥ 1`.  This does not
affect the unconditional ordinary bound. -/
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
  have hmem :
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
    simp only [optimizedProductionFailureProbabilityBound, hF, hM]
    exact le_add_of_nonneg_left (add_nonneg (by positivity) (by positivity))
  have hpow : (1 : ℚ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  have hthird : (1 : ℚ) < (20 + 14 * 21 : ℚ) / 97 := by norm_num
  have hx : (20 + 14 * 21 : ℚ) / 97 ≤ ((20 + 14 * 21 : ℚ) / 97) * 2 ^ b :=
    le_mul_of_one_le_right (by positivity) hpow
  have hle : ((20 + 14 * 21 : ℚ) / 97) * 2 ^ b ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right hmem (by positivity)) h
  linarith [hx, hle, hthird]

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
  exact packageR_complete_bits_support_is_impossible hfirstD hrootAt hrootAtQ b hb

/-- Bound and bits quantify the same set.  The bound is the inhabited
union bound.  The bits rewrite is a vacuous implication at this field
cardinality.  The accounting is `11+1+2`. -/
theorem bound_contentful_bits_vacuous_at_F97
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97) :
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
      (¬ ∃ b : ℕ,
        optimizedProductionFailureProbabilityBound
            (Fintype.card K97cubic) (Fintype.card F97)
            (OptimizedFailureEventEv.workloadEv (packageR hfirstD) (packageR hfirstD).optimized.Λ +
              OptimizedHostileTimestamps.timestampCollisionBound
                (3 * (packageR hfirstD).optimized.family.problem.cfg.compRows) +
                pricedWalkWork (packageR hfirstD).optimized.family.problem.cfg.compRows
              (packageR hfirstD).optimized.family.problem.cfg.memRows)
            ((packageR hfirstD).hostileIOWork + (packageR hfirstD).hostileInterWork)
            (packageR hfirstD).optimized.family.problem.cfg.compRows
            (packageR hfirstD).optimized.family.problem.cfg.memRows * 2 ^ b ≤ 1) ∧
      (11 + 1 + 2 = 14) :=
  ⟨(packageR hfirstD).optimizedFalseAcceptance_probability_le_legacy haxR hbasisR hwidthR,
    packageR_complete_bits_projection_has_no_applicable_b hfirstD hrootAt hrootAtQ,
    by norm_num⟩

/-! ## G. Accounting `11 + 1 + 2`

The predicate `OptimizedFullStrictThm54Statement`
is that bound, not emptiness of every fibre.
The residual pair is (contentful bound, vacuous-at-F97 bits
rewrite). -/

/-- The capstone `optimizedFullStrictNockVMROM_of_package` consumes the package statement `OptimizedFullStrictThm54Statement (packageR hfirstD)`. -/
theorem consumed_capstone_is_inhabited 
    (hax : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasis : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidth : FormRWidth F97):
    OptimizedFullStrictThm54Statement (packageR hfirstD) :=
  optimizedFullStrictNockVMROM_of_package (packageR hfirstD) hax hbasis hwidth

end

end Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance

#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance.statementR_complete_false_acceptance_bound
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance.statementR_complete_false_acceptance_bits
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance.complete_fields_share_the_exact_false_acceptance_set
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance.packageR_complete_bits_numeric_hypothesis
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance.packageR_complete_bits_support_is_impossible
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance.packageR_complete_bits_projection_has_no_applicable_b
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance.bound_contentful_bits_vacuous_at_F97
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance.computeSourceEnv_chal_independent
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance.packageR_optimized_acceptance_pins_tuple
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance.packageR_accepted_tuple_is_canonical
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance.packageR_accepted_excludes_p8_and_io
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance.compute_preprocessing_binds_only_two_masks
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance.packageQ_accepted_with_a_bad_scalar_coin
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance.consumed_capstone_is_inhabited
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.packageR
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.statementR
