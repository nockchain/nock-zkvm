import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.DistinctCensusFold2
import Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
import Nock.NockVMROM.Thm54.WalkTilingEvents

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# P8 fixed-field classification at `packageR`

The earlier analysis localized the two `p8_fixed_field_*` conjuncts of
`OptimizedFullStrictThm54Statement packageR` as far as the `OP_5` fixture
honestly went, and stopped with fibre pinning as a hypothesis. This module
absorbs that FINDING on the production side: the pin and emptiness are
re-proved here, without depending on `Nock/RedTeam`.

Paper objects:
* Theorem 5.4's negligible soundness error, instantiated at one finite field as
  the P8 union-bound `FixedFieldSoundnessClaim`;
* `Lem:ion_univariate_sec` collision probability for `n_1 ≠ n_2`;
* the bit-security rewrite of that bound;
* OP_5 EC.5 inverse;
* OP_3/OP_4/OP_6 size windows, which this skeleton does not consume
.

Cite repair.

The two statement *fields* remain the released union bound
(`p8_fixedField_falseAcceptance_le` / `_two_pow_neg`); their Lean types do not
change.  Classification is the extra fixture fact that
`FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam = ∅`.
The two `complete_false_acceptance_*` fields are a different 1-1 obligation
and are left untouched.

Whole-joint completeness and generic `CommitmentResidual` are out of scope.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.DistinctCensusP8FixedField

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Noun Nock.Walk
open Framework Framework.Reify Framework.Thm54
open Nock.Reified
open SemanticStrategy SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.ProductionRawVerifier
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.EqualityOperandCensus
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment
open Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
open Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
open Nock.NockVMROM.Thm54.DistinctCensusFold2
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97p8 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97p8 : CharP K97cubic 97 := inferInstance
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

/-! ## A. The two statement fields, named exactly -/

theorem packageR_q_Λ :
    (packageR hfirstD).q = 97 ∧ (packageR hfirstD).optimized.Λ = 7 :=
  ⟨rfl, rfl⟩

theorem packageR_skeleton : (packageR hfirstD).strategy.skeleton = skelD :=
  rfl

/-- The inhabited `p8_fixed_field_soundness` field is the released P8 union bound
, not an empty-set classification. -/
theorem statementR_p8_fixed_field_soundness
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled
      (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97) :
    |jointProbability
        (FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam)| ≤
      (workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
          (fixedTopologyWorkload (packageR hfirstD).strategy)
          (fixedAxisWorkload (packageR hfirstD).strategy) : ℝ) /
        (Fintype.card K97cubic : ℝ) :=
  (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_soundness cfgD.challenges.lam

/-- The inhabited `p8_fixed_field_bits` field is the bit-support rewrite of that
same bound.  It classifies with soundness, because both
name the same `FalseAcceptanceSet`. -/
theorem statementR_p8_fixed_field_bits
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled
      (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97)
    (b : ℕ)
    (hsupport :
      workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
          (fixedTopologyWorkload (packageR hfirstD).strategy)
          (fixedAxisWorkload (packageR hfirstD).strategy) * 2 ^ b ≤
        Fintype.card K97cubic) :
    |jointProbability
        (FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam)| ≤
      1 / 2 ^ b :=
  (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_bits cfgD.challenges.lam b hsupport

/-! ## B. Size-window event is empty: OP_5 / OP_1 consume none

`requiredSizeWindowNouns` is nonempty only at `.s3`, `.s4`, `.s6`
 -- those are exactly the
three algorithm blocks that read a subformula evaluation's *type*: `OP_3`'s
`evaluation = ?(sf_evaluation_1)` at `1764`, `OP_4`'s `evaluation = +(sf_evaluation_1)`
at `1768`, and `OP_6`'s `type(sf_evaluation_2) = atom` at `1777`.  This skeleton,
whose rows are `OP_5`/`OP_1`, has none. -/

theorem sizeWindowFailureR_empty :
    SizeWindowFailure (K := K97cubic) (packageR hfirstD).strategy.skeleton = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro ω hω
  rw [mem_SizeWindowFailure_iff] at hω
  obtain ⟨_, n, hn, _⟩ := hω
  rw [packageR_skeleton hfirstD hrootAt hrootAtQ, sizeWindowNounsD hfirstD] at hn
  exact List.not_mem_nil hn

/-! ## C. Collision event is nonempty: the distinct OP_5 pair

This is the paper's `n_1 ≠ n_2` hypothesis of `Lem:ion_univariate_sec`
, carried by the consumed census.  P8 is present. -/

theorem collisionFailureEventR_nonempty :
    (collisionFailureEvent (K := K97cubic)
      (packageR hfirstD).optimized.census.census).Nonempty := by
  obtain ⟨i, hi, _hne⟩ := packageR_consumed_census_has_genuine_distinct_pair hfirstD hrootAt hrootAtQ
  refine ⟨((0, 0), (0, -1)), ?_⟩
  rw [mem_collisionFailureEvent_iff]
  refine ⟨i, ?_⟩
  simpa [hi, nprSeed] using operands_not_sepSeed_at_neg_one

theorem collisionFailureEventR_ne_empty :
    collisionFailureEvent (K := K97cubic) (packageR hfirstD).optimized.census.census ≠ ∅ :=
  Finset.nonempty_iff_ne_empty.mp (collisionFailureEventR_nonempty hfirstD hrootAt hrootAtQ)

/-- The P8 object of `Lem:ion_univariate_sec` is the consumed census pair, not an
absent opcode.  Completeness delta would require the pair to be missing; it is
not. -- the paper -/
theorem p8_collision_object_is_present :
    (∃ i : Fin (packageR hfirstD).optimized.census.census.count,
      (packageR hfirstD).optimized.census.census.pair i = (operandLeft, operandRight) ∧
        ((packageR hfirstD).optimized.census.census.pair i).1 ≠
          ((packageR hfirstD).optimized.census.census.pair i).2) ∧
      (collisionFailureEvent (K := K97cubic)
        (packageR hfirstD).optimized.census.census).Nonempty ∧
      SizeWindowFailure (K := K97cubic) (packageR hfirstD).strategy.skeleton = ∅ :=
  ⟨packageR_consumed_census_has_genuine_distinct_pair hfirstD hrootAt hrootAtQ,
    collisionFailureEventR_nonempty hfirstD hrootAt hrootAtQ,
    sizeWindowFailureR_empty hfirstD hrootAt hrootAtQ⟩

/-! ## D. Emptiness reduced to three accepted-coin exclusions

Zero-seed is removed by `Accepts`.  Size-window is empty.  Collision does
**not** drop out, unlike `packageP`.  Remaining: specialized topology, guarded
axis, and collision at accepted coins. -/

theorem falseAcceptanceR_empty_of_three_events
    (htopology : ∀ ω : JointCoins K97cubic, (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam →
      ω ∉ specializedTopologyFailureEvent (packageR hfirstD).strategy.verifier.raw cfgD.challenges.lam)
    (haxis : ∀ ω : JointCoins K97cubic, (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam →
      ω ∉ guardedAxisFailureEvent (packageR hfirstD).strategy cfgD.challenges.lam)
    (hcoll : ∀ ω : JointCoins K97cubic, (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam →
      ω ∉ collisionFailureEvent (packageR hfirstD).optimized.census.census) :
    FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro ω hω
  have hacc := (mem_falseAcceptanceSet_iff _ _ _ _ ω).1 hω
  refine hacc.2 ((packageR hfirstD).containment ω cfgD.challenges.lam hacc.1 ?_)
  intro hbad
  simp only [ProductionP8Containment.FailureUnion, Finset.mem_union] at hbad
  rcases hbad with hbad | hbad
  · rcases hbad with hbad | hbad
    · rcases hbad with hbad | hbad
      · rcases hbad with hbad | hbad
        · exact accepts_seed_ne_zero hacc.1
            ((mem_zeroSeedFailureEvent_iff ω).1 hbad)
        · exact hcoll ω hacc.1 hbad
      · exact htopology ω hacc.1 hbad
    · exact haxis ω hacc.1 hbad
  · rw [sizeWindowFailureR_empty hfirstD hrootAt hrootAtQ] at hbad
    exact absurd hbad (Finset.notMem_empty _)

/-- Fibre pinning still implies emptiness, as at `packageP`.  It is a strictly
stronger hypothesis than the three exclusions, and is not discharged. -/
theorem coin_eq_coinQ_of_fibre (ω : JointCoins K97cubic)
    (hz : nprSeed ω = seedD) (hα : alphaM ω = alphaD) :
    ω = coinQ (alphaC ω) (gamma ω) := by
  rcases ω with ⟨⟨a, g⟩, ⟨α, z⟩⟩
  change ((a, g), (α, z)) = ((a, g), (alphaD, seedD))
  exact Prod.ext rfl (Prod.ext hα hz)

theorem falseAcceptanceR_empty_of_fibre_pinned
    (h : ∀ ω : JointCoins K97cubic, (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam →
      nprSeed ω = seedD ∧ alphaM ω = alphaD) :
    FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam = ∅ := by
  apply falseAcceptanceR_empty_of_three_events hfirstD hrootAt hrootAtQ
  · intro ω hacc hbad
    obtain ⟨hseed, halpha⟩ := h ω hacc
    rw [coin_eq_coinQ_of_fibre hfirstD hrootAt hrootAtQ ω hseed halpha] at hbad
    exact coinQ_not_specializedTopologyFailureEvent hfirstD hrootAtQ (alphaC ω) (gamma ω) hbad
  · intro ω hacc hbad
    obtain ⟨hseed, halpha⟩ := h ω hacc
    rw [coin_eq_coinQ_of_fibre hfirstD hrootAt hrootAtQ ω hseed halpha] at hbad
    exact coinR_not_guardedAxisFailureEvent hfirstD hrootAt hrootAtQ (alphaC ω) (gamma ω) hbad
  · intro ω hacc hbad
    obtain ⟨hseed, halpha⟩ := h ω hacc
    rw [coin_eq_coinQ_of_fibre hfirstD hrootAt hrootAtQ ω hseed halpha] at hbad
    apply coinQ_not_collisionFailureEvent hfirstD hrootAtQ (alphaC ω) (gamma ω)
    rw [← packageR_census hfirstD]
    exact hbad

/-! ## E. Optimized layer pins the fibre; P8 `Accepts` does not

The earlier sub-goal is discharged at the optimized layer because
`OptimizedSameProblemAt` is a field of optimized acceptance.
`ProductionStrategy.Accepts` has no such field. -/

theorem packageR_sameProblem_pins_fibre (ω : JointCoins K97cubic) (lmb : K97cubic)
    (hsame : (packageR hfirstD).OptimizedSameProblemAt ω lmb) :
    nprSeed ω = seedD ∧ alphaM ω = alphaD := by
  have hcfg := congrArg RawProblem.cfg hsame.specialized_eq_objects
  constructor
  · have hz : nprSeed ω = (packageR hfirstD).objects.cfg.challenges.z := by
      calc
        nprSeed ω =
            (specializedProblem (packageR hfirstD).optimized.verifier.raw.timestamp
              (nprSeed ω) hsame.nprSeed_ne (alphaM ω) lmb).cfg.challenges.z :=
          (specializedProblem_seed _ _ _ _ _).symm
        _ = (packageR hfirstD).objects.cfg.challenges.z :=
          congrArg (fun cfg : ExactConfig F97 K97cubic => cfg.challenges.z) hcfg
    rw [hz, (packageR_regression hfirstD hrootAt hrootAtQ).1, seedD_cfg]
  · have hα : alphaM ω = (packageR hfirstD).objects.cfg.challenges.α := by
      calc
        alphaM ω =
            (specializedProblem (packageR hfirstD).optimized.verifier.raw.timestamp
              (nprSeed ω) hsame.nprSeed_ne (alphaM ω) lmb).cfg.challenges.α :=
          (specializedProblem_tableAlpha _ _ _ _ _).symm
        _ = (packageR hfirstD).objects.cfg.challenges.α :=
          congrArg (fun cfg : ExactConfig F97 K97cubic => cfg.challenges.α) hcfg
    rw [hα, (packageR_regression hfirstD hrootAt hrootAtQ).1]
    rfl

theorem packageR_optimized_acceptance_pins_fibre
    (c : OptimizedProductionChallengeTuple K97cubic F97)
    (hacc : (packageR hfirstD).OptimizedHistoricalAcceptanceAt (computeTraceR hfirstD) (memoryTraceR hfirstD) c) :
    nprSeed c.1 = seedD ∧ alphaM c.1 = alphaD :=
  packageR_sameProblem_pins_fibre hfirstD hrootAt hrootAtQ c.1 c.2.2.2.lambda hacc.same_problem

/-- P8 acceptance on the committed fibre, and the optimized pin, side by side.
The missing implication is `Accepts ω → nprSeed ω = seedD ∧ alphaM ω = alphaD`. -/
theorem fibre_pinning_is_carried_by_same_problem_only :
    (∀ c : OptimizedProductionChallengeTuple K97cubic F97,
        (packageR hfirstD).OptimizedHistoricalAcceptanceAt (computeTraceR hfirstD) (memoryTraceR hfirstD) c →
        nprSeed c.1 = seedD ∧ alphaM c.1 = alphaD) ∧
      (∀ (ω : JointCoins K97cubic) (lmb : K97cubic),
        (packageR hfirstD).OptimizedSameProblemAt ω lmb →
        nprSeed ω = seedD ∧ alphaM ω = alphaD) ∧
      (∀ a g : K97cubic, (packageR hfirstD).strategy.Accepts (coinQ a g) cfgD.challenges.lam) :=
  ⟨packageR_optimized_acceptance_pins_fibre hfirstD hrootAt hrootAtQ,
    packageR_sameProblem_pins_fibre hfirstD hrootAt hrootAtQ,
    packageR_accepts hfirstD hrootAt hrootAtQ⟩

/-! ## F. Why VerifierGates do not pin the NPR seed

`alphaMCommitmentQ` reuses one table/IO assignment at every `(z, α)`, but
`familyData.base.problem` is still the specialization at that pair.  The
public-claim `enc` gates therefore compare `enc(z, claim)` against the
*specialized* first row, which is tautological for a skeleton-binding
execution, and the six RAPs are the RAP of the specialized family against
the seed-`8` traces.  Showing those RAPs fail off-fibre is the per-seed
argument recorded earlier; the paper does not supply it
. -/

theorem alphaMCommitmentQ_problem
    (z : K97cubic) (hz : z ≠ 0) (α : K97cubic) :
    (alphaMCommitmentQ hfirstD z hz α cfgD.challenges.lam).familyData.base.problem =
      specializedProblem (timestampD hfirstD) z hz α cfgD.challenges.lam :=
  rfl

theorem alphaMCommitmentQ_tables_are_the_seed8_assignment
    (z : K97cubic) (hz : z ≠ 0) (α : K97cubic) :
    (alphaMCommitmentQ hfirstD z hz α cfgD.challenges.lam).tables.compute =
      (assignmentQ hfirstD 0 0).computeTableAux ∧
      (alphaMCommitmentQ hfirstD z hz α cfgD.challenges.lam).tables.memory =
        (assignmentQ hfirstD 0 0).memoryTableAux :=
  ⟨rfl, rfl⟩

theorem packageR_afterAlphaM_is_alphaMCommitmentQ :
    (packageR hfirstD).strategy.verifier.raw.afterAlphaM = alphaMCommitmentQ hfirstD :=
  rfl

/-! ## G. Snapshot: emptiness reduced to fibre pinning

This section is the compiled localization.  Section H discharges the
remaining production fibre-pin premise. -/

/-- Size-window empty, collision nonempty, emptiness waiting on three named
exclusions (or on fibre pinning).  The two `complete_false_acceptance_*`
fields are a different 1-1 obligation and are left untouched. -/
theorem p8_fixed_field_status_R
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled
      (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97) :
    SizeWindowFailure (K := K97cubic) (packageR hfirstD).strategy.skeleton = ∅ ∧
      (collisionFailureEvent (K := K97cubic)
        (packageR hfirstD).optimized.census.census).Nonempty ∧
      ((∀ ω : JointCoins K97cubic, (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam →
          ω ∉ specializedTopologyFailureEvent (packageR hfirstD).strategy.verifier.raw cfgD.challenges.lam) →
        (∀ ω : JointCoins K97cubic, (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam →
          ω ∉ guardedAxisFailureEvent (packageR hfirstD).strategy cfgD.challenges.lam) →
        (∀ ω : JointCoins K97cubic, (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam →
          ω ∉ collisionFailureEvent (packageR hfirstD).optimized.census.census) →
        FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam = ∅) ∧
      ((∀ ω : JointCoins K97cubic, (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam →
          nprSeed ω = seedD ∧ alphaM ω = alphaD) →
        FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam = ∅) ∧
      |jointProbability
          (FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam)| ≤
        (workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
            (fixedTopologyWorkload (packageR hfirstD).strategy)
            (fixedAxisWorkload (packageR hfirstD).strategy) : ℝ) /
          (Fintype.card K97cubic : ℝ) :=
  ⟨sizeWindowFailureR_empty hfirstD hrootAt hrootAtQ,
    collisionFailureEventR_nonempty hfirstD hrootAt hrootAtQ,
    falseAcceptanceR_empty_of_three_events hfirstD hrootAt hrootAtQ,
    falseAcceptanceR_empty_of_fibre_pinned hfirstD hrootAt hrootAtQ,
    statementR_p8_fixed_field_soundness hfirstD hrootAt hrootAtQ haxR hbasisR hwidthR⟩

/-- Arithmetic snapshot `9+1+4 = 14`.  The equation remains true; the
class split is updated in `accounting_after_p8_empty`. -/
theorem accounting_unchanged
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled
      (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97) :
    (9 + 1 + 4 = 14) ∧
      Nonempty (OptimizedFullStrictThm54Statement (packageR hfirstD)) ∧
      (∀ a g : K97cubic,
        (packageR hfirstD).strategy.Accepts (coinQ a g) cfgD.challenges.lam ∧
          coinQ a g ∉ ProductionP8Containment.FailureUnion (packageR hfirstD).strategy
            (packageR hfirstD).optimized.census cfgD.challenges.lam ∧
          ProductionP8Containment.GenuineTargetAt (packageR hfirstD).strategy 97 7
            (coinQ a g) cfgD.challenges.lam) :=
  ⟨by norm_num, ⟨statementR hfirstD haxR hbasisR hwidthR⟩,
    fun a g => ⟨packageR_accepts hfirstD hrootAt hrootAtQ a g,
      coinR_not_failureUnion hfirstD hrootAt hrootAtQ a g,
      genuineTargetR hfirstD hrootAt hrootAtQ a g⟩⟩

/-! ## H. Production fibre pin and empty false-acceptance set

Production `Accepts` has no
`OptimizedSameProblemAt` field, but the consumed OP_5 EC.5 inverse and the
memory-walk initial line still pin `(nprSeed, alphaM) = (8, 4)`
. -/

omit hfirstD hrootAt hrootAtQ

/-- Row-level extraction retaining the prover's actual auxiliary columns. -/
theorem compute_rapcomp_at_of_satisfies
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K]
    {p : ℕ} [CharP K p]
    {R : RawPlusIOSegmentedFamily F K}
    (M : RawMessage R p)
    (hchar : NodeEncoding.StateTagChar K)
    (hrap : ∀ kind, (R.computeTableRAP kind).Satisfies M.computeTableTrace)
    (i : Fin R.cfg.compRows) :
    ComputeTable.RAPcomp R.cfg.challenges.computeInputs
      (R.exec.computePubAt i) (R.exec.computeDecAt i) (M.tables.compute i) := by
  let env := fun i : Fin R.cfg.compRows =>
    computeEnvFull R.cfg.challenges.computeInputs
      (ComputeTable.opSel (R.exec.computePubAt i).state)
      (R.exec.computePubAt i) (R.exec.computeDecAt i) (M.tables.compute i)
  have hrowRAP :=
    (computeRowSegment_iff R.cfg M.computeTableTrace).1 (hrap .row)
  have hrows :
      ∀ i, ∀ c ∈ computeAIR.constraints, c.expr.eval (env i) = 0 := by
    apply (satisfies_iff_perRow_env env R.cfg.compNodes R.cfg.compNodes_injective
      R.cfg.challenges.computeValuation R.cfg.eDeg R.cfg.orbit.h
      R.cfg.orbit.ω R.cfg.orbit.βcoset R.cfg.orbit.βcoset_ne_zero
      R.cfg.orbit_h_pos (fun _ => rfl) (fun _ => rfl)).1
    simpa [env, RawMessage.computeTableTrace] using hrowRAP
  obtain ⟨s, hs, hlocal, _⟩ :=
    computeAIR_sound_free R.cfg.challenges.computeInputs
      (ComputeTable.opSel (R.exec.computePubAt i).state)
      (R.exec.computePubAt i) (R.exec.computeDecAt i) (M.tables.compute i)
      (RawMessage.freeSelectorChar_of_stateTagChar hchar) (hrows i)
  have hstate : s = (R.exec.computePubAt i).state := by
    by_contra hne
    have he := congrFun hs (R.exec.computePubAt i).state
    simp [ComputeTable.opSel, Ne.symm hne] at he
  subst s
  simpa using hlocal

include hfirstD hrootAt hrootAtQ

/-- Production acceptance pins `alphaM` through the memory-walk initial-line
equation. -/
theorem production_acceptance_pins_alphaM
    (ω : JointCoins K97cubic) (hacc : (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam) :
    alphaM ω = alphaD := by
  have hz : nprSeed ω ≠ 0 :=
    MultiRootNonzeroChallenges.accepts_seed_ne_zero hacc
  have hverifier : (verifierQ hfirstD).Accepts ω cfgD.challenges.lam := by
    change (packageR hfirstD).strategy.verifier.Accepts ω cfgD.challenges.lam
    exact (packageR hfirstD).strategy.productionRawAccepts_of_accepts ω cfgD.challenges.lam hz hacc
  have hsixω :=
    ((verifierQ hfirstD).accepts_iff_eight_segmented_families ω cfgD.challenges.lam hz).1 hverifier
  have hcertω :=
    (((verifierQ hfirstD).messageAt ω cfgD.challenges.lam hz).raw.memoryWalkRAP_wholeTrace_iff).1
      hsixω.2.2.2.2.1
  have hω := hcertω.1.ln1
  have hsixTarget :=
    (PlusIOSameExecutionAssignment.satisfies_iff_six_families
      (assignmentQ hfirstD (alphaC ω) (gamma ω))).1
      ((completionQ hfirstD).assignment (alphaC ω) (gamma ω)).sixFamilies
  have hcertTarget :=
    (PlusIOSameExecutionAssignment.memoryWalkRAP_wholeTrace_iff
      (assignmentQ hfirstD (alphaC ω) (gamma ω))).1 hsixTarget.2.2.2.1
  have ht := hcertTarget.1.ln1
  change (assignmentQ hfirstD (alphaC ω) (gamma ω)).memoryWalk.ln 1 = alphaM ω at hω
  change (assignmentQ hfirstD (alphaC ω) (gamma ω)).memoryWalk.ln 1 = alphaD at ht
  exact hω.symm.trans ht

/-- The same committed OP_5 inverse witness appears in the accepted row at
`nprSeed ω` and in the known accepted row at seed `8`; subtracting the two
EC.5 RLC equations pins the seed. -/
theorem production_acceptance_pins_seed
    (ω : JointCoins K97cubic) (hacc : (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam) :
    nprSeed ω = seedD := by
  have hz : nprSeed ω ≠ 0 :=
    MultiRootNonzeroChallenges.accepts_seed_ne_zero hacc
  have hverifier : (verifierQ hfirstD).Accepts ω cfgD.challenges.lam := by
    change (packageR hfirstD).strategy.verifier.Accepts ω cfgD.challenges.lam
    exact (packageR hfirstD).strategy.productionRawAccepts_of_accepts ω cfgD.challenges.lam hz hacc
  have hsixω :=
    ((verifierQ hfirstD).accepts_iff_eight_segmented_families ω cfgD.challenges.lam hz).1 hverifier
  let iω : Fin ((verifierQ hfirstD).familyAt ω cfgD.challenges.lam hz).cfg.compRows :=
    ⟨0, ((verifierQ hfirstD).familyAt ω cfgD.challenges.lam hz).cfg.compRows_pos⟩
  have hcur := compute_rapcomp_at_of_satisfies
    ((verifierQ hfirstD).messageAt ω cfgD.challenges.lam hz).raw stateTagChar97 hsixω.2.1 iω
  have htargetVerifier := verifierQ_accepts hfirstD (alphaC ω) (gamma ω)
  have hsixTarget :=
    ((verifierQ hfirstD).accepts_iff_eight_segmented_families
      (coinQ (alphaC ω) (gamma ω)) cfgD.challenges.lam seedH_ne).1 htargetVerifier
  let it : Fin
      ((verifierQ hfirstD).familyAt (coinQ (alphaC ω) (gamma ω)) cfgD.challenges.lam seedH_ne).cfg.compRows :=
    ⟨0, ((verifierQ hfirstD).familyAt
      (coinQ (alphaC ω) (gamma ω)) cfgD.challenges.lam seedH_ne).cfg.compRows_pos⟩
  have htarget := compute_rapcomp_at_of_satisfies
    ((verifierQ hfirstD).messageAt (coinQ (alphaC ω) (gamma ω)) cfgD.challenges.lam seedH_ne).raw
    stateTagChar97 hsixTarget.2.1 it
  have hstateCur :
      (((verifierQ hfirstD).familyAt ω cfgD.challenges.lam hz).exec.computePubAt iω).state = .s5 := by
    simp [iω, verifierQ, HonestCommitment.verifierOf,
      ProductionRawVerifier.TemplateAdapter.Strategy.honest,
      acceptedFamilyDataQ, alphaMCommitmentQ,
      TemplateRawJointSoundness.Strategy.alphaMCommitment,
      TemplateRawJointSoundness.Strategy.familyAt,
      AlphaMFamilyData.atCoins,
      ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      specializedProblem, HonestCommitment.Data.timestampStrategy,
      HonestCommitment.Data.executionTemplate,
      DataOnlyTemplateFixedStagedTimestampStrategy.ofRawData,
      ExactExecutionTemplate.specialize, ComputeRowTemplate.specialize,
      specializeMemRecScaled, computeLineOrigin,
      ExactExecution.computePubAt, ExactExecution.computeRowAt,
      ExactExecution.computeRows, bfsForest,
      HonestCommitment.renderComputeTemplate, HonestCommitment.renderComputeRow,
      dataD, skelD, HonestCommitment.skeletonOfNodes, computeNodesD, op5Node,
      op5Stamp, op5SkelD, op5Row]
    rfl
  have hstateTarget :
      (((verifierQ hfirstD).familyAt
        (coinQ (alphaC ω) (gamma ω)) cfgD.challenges.lam seedH_ne).exec.computePubAt it).state = .s5 := by
    simp [it, verifierQ, HonestCommitment.verifierOf,
      ProductionRawVerifier.TemplateAdapter.Strategy.honest,
      acceptedFamilyDataQ, alphaMCommitmentQ, coinQ,
      TemplateRawJointSoundness.Strategy.alphaMCommitment,
      TemplateRawJointSoundness.Strategy.familyAt,
      AlphaMFamilyData.atCoins,
      ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      specializedProblem, HonestCommitment.Data.timestampStrategy,
      HonestCommitment.Data.executionTemplate,
      DataOnlyTemplateFixedStagedTimestampStrategy.ofRawData,
      ExactExecutionTemplate.specialize, ComputeRowTemplate.specialize,
      specializeMemRecScaled, computeLineOrigin,
      ExactExecution.computePubAt, ExactExecution.computeRowAt,
      ExactExecution.computeRows, bfsForest,
      HonestCommitment.renderComputeTemplate, HonestCommitment.renderComputeRow,
      dataD, skelD, HonestCommitment.skeletonOfNodes, computeNodesD, op5Node,
      op5Stamp, op5SkelD, op5Row]
    rfl
  have hecur := hcur.2.2.2.2
  have hetarget := htarget.2.2.2.2
  rw [show ((verifierQ hfirstD).familyAt ω cfgD.challenges.lam hz).cfg.challenges.computeInputs =
      ((verifierQ hfirstD).familyAt ω cfgD.challenges.lam hz).cfg.challenges.computeInputs from rfl] at hecur
  simp only [ComputeTable.evalR, hstateCur] at hecur
  simp only [ComputeTable.evalR, hstateTarget] at hetarget
  rcases hecur with ⟨_, _, _, _, _, _, _, _, _, _, _, hcurInv⟩
  rcases hetarget with ⟨_, _, _, _, _, _, _, _, _, _, _, htargetInv⟩
  dsimp [iω, it] at hcurInv htargetInv
  simp [verifierQ, HonestCommitment.verifierOf,
    ProductionRawVerifier.TemplateAdapter.Strategy.honest,
    acceptedFamilyDataQ, alphaMCommitmentQ, rawStrategyQ,
    TemplateRawJointSoundness.Strategy.alphaMCommitment,
    TemplateRawJointSoundness.Strategy.familyAt,
    TemplateRawJointSoundness.Strategy.messageAt,
    AlphaMFamilyData.atCoins, AlphaMCommitment.tablesAt,
    ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
    ProductionRawVerifier.TemplateAdapter.Strategy.messageAt,
    specializedProblem, HonestCommitment.Data.timestampStrategy,
    HonestCommitment.Data.executionTemplate, HonestCommitment.configTemplateOf,
    DataOnlyTemplateFixedStagedTimestampStrategy.ofRawData,
    ExactExecutionTemplate.specialize, ComputeRowTemplate.specialize,
    specializeMemRecScaled, computeLineOrigin,
    ExactExecution.computePubAt, ExactExecution.computeRowAt,
    ExactExecution.computeRows, bfsForest,
    HonestCommitment.renderComputeTemplate, HonestCommitment.renderComputeRow,
    HonestCommitment.renderInputs, HonestCommitment.renderPub,
    HonestCommitment.renderDec,
    dataD, skelD, HonestCommitment.skeletonOfNodes, computeNodesD, op5Node,
    op5SkelD, op5Row, op5PubD, op5Dec, compInputs] at hcurInv htargetInv
  let i0 : Fin (legacyFamilyQ hfirstD 0 0).problem.cfg.compRows :=
    ⟨0, (legacyFamilyQ hfirstD 0 0).problem.cfg.compRows_pos⟩
  let g : K97cubic := ((assignmentQ hfirstD 0 0).computeTableAux i0).invGen
  have hresult (z : K97cubic) :
      (GlobalCarryRecognizer.enc z op5Result).leaf = 1 := by
    rw [GlobalCarryRecognizer.enc_leaf]
    change (NPR.listPoly [(1 : K97cubic)]).eval z = 1
    rw [NPR.listPoly_cons, NPR.listPoly_nil]
    simp
  have hresultPoly (z : K97cubic) :
      (NPR.listPoly (NPR.leafF (K := K97cubic) op5Result)).eval z = 1 := by
    rw [← GlobalCarryRecognizer.enc_leaf]
    exact hresult z
  have hcurSimple : g * (-(1 + nprSeed ω)) = 1 := by
    dsimp only [Fin.cast, Fin.val_zero, List.getElem_cons_zero] at hcurInv
    simp [g, i0, acceptedFamilyDataQ, AlphaMFamilyData.atCoins, specializedProblem,
      HonestCommitment.configTemplateOf, ExactConfigTemplate.specialize,
      ChallengeVectorTemplate.specialize, distinctCensusExecution, cfgD, compInputs,
      ChallengeVector.computeInputs, ComputeTable.fanoutComp,
      HonestCommitment.renderSubFP, op5SkelD, op5Row,
      leafPoly_eval_left, leafPoly_eval_right, hresultPoly] at hcurInv
    change g * (7 + 9 * nprSeed ω - (8 + 10 * nprSeed ω)) = 1 at hcurInv
    calc
      g * (-(1 + nprSeed ω)) =
          g * (7 + 9 * nprSeed ω - (8 + 10 * nprSeed ω)) := by ring
      _ = 1 := hcurInv
  have htargetSimple : g * (-(1 + seedD)) = 1 := by
    dsimp only [Fin.cast, Fin.val_zero, List.getElem_cons_zero] at htargetInv
    simp [g, i0, coinQ, acceptedFamilyDataQ, AlphaMFamilyData.atCoins, specializedProblem,
      HonestCommitment.configTemplateOf, ExactConfigTemplate.specialize,
      ChallengeVectorTemplate.specialize, distinctCensusExecution, cfgD, compInputs,
      ChallengeVector.computeInputs, ComputeTable.fanoutComp,
      HonestCommitment.renderSubFP, op5SkelD, op5Row,
      leafPoly_eval_left, leafPoly_eval_right, hresultPoly] at htargetInv
    change g * (7 + 9 * seedD - (8 + 10 * seedD)) = 1 at htargetInv
    calc
      g * (-(1 + seedD)) =
          g * (7 + 9 * seedD - (8 + 10 * seedD)) := by ring
      _ = 1 := htargetInv
  have hg : g ≠ 0 := by
    intro hg
    rw [hg, zero_mul] at htargetSimple
    exact zero_ne_one htargetSimple
  have hprod : g * (nprSeed ω - seedD) = 0 := by
    linear_combination -hcurSimple + htargetSimple
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hg)

/-- Production acceptance pins the complete committed fibre
. -/
theorem production_acceptance_pins_fibre
    (ω : JointCoins K97cubic) (hacc : (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam) :
    nprSeed ω = 8 ∧ alphaM ω = 4 := by
  refine ⟨?_, ?_⟩
  · exact (production_acceptance_pins_seed hfirstD hrootAt hrootAtQ ω hacc).trans
      (show seedD = (8 : K97cubic) from rfl)
  · exact (production_acceptance_pins_alphaM hfirstD hrootAt hrootAtQ ω hacc).trans
      (show alphaD = (4 : K97cubic) from rfl)

theorem production_acceptance_pins_fibre_named
    (ω : JointCoins K97cubic) (hacc : (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam) :
    nprSeed ω = seedD ∧ alphaM ω = alphaD :=
  ⟨production_acceptance_pins_seed hfirstD hrootAt hrootAtQ ω hacc,
    production_acceptance_pins_alphaM hfirstD hrootAt hrootAtQ ω hacc⟩

/-- FINDING absorbed: the production false-acceptance set is empty at this
fixture. -/
theorem falseAcceptanceR_empty :
    FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam = ∅ :=
  falseAcceptanceR_empty_of_fibre_pinned hfirstD hrootAt hrootAtQ
    (production_acceptance_pins_fibre_named hfirstD hrootAt hrootAtQ)

/-- Both statement fields remain the paper's probabilistic bound; at this
fixture they classify together as bounds on the empty set.  Field *types* are
unchanged. -- the paper -/
theorem both_p8_fields_classify_empty
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled
      (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97) :
    FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam = ∅ ∧
      |jointProbability
          (FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam)| ≤
        (workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
            (fixedTopologyWorkload (packageR hfirstD).strategy)
            (fixedAxisWorkload (packageR hfirstD).strategy) : ℝ) /
          (Fintype.card K97cubic : ℝ) ∧
      ∀ b : ℕ,
        workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
            (fixedTopologyWorkload (packageR hfirstD).strategy)
            (fixedAxisWorkload (packageR hfirstD).strategy) * 2 ^ b ≤
          Fintype.card K97cubic →
        |jointProbability
            (FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam)| ≤
          1 / 2 ^ b :=
  ⟨falseAcceptanceR_empty hfirstD hrootAt hrootAtQ,
    (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_soundness cfgD.challenges.lam,
    fun b hs => (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_bits cfgD.challenges.lam b hs⟩

/-- The two P8 fields move uninformative → substantive.  Remaining tail is the
two complete optimized false-acceptance bounds.  Field types are still the
inhabited union bound. -/
theorem accounting_after_p8_empty
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled
      (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97) :
    (11 + 1 + 2 = 14) ∧
      FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam = ∅ ∧
      |jointProbability
          (FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam)| ≤
        (workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
            (fixedTopologyWorkload (packageR hfirstD).strategy)
            (fixedAxisWorkload (packageR hfirstD).strategy) : ℝ) /
          (Fintype.card K97cubic : ℝ) ∧
      (∀ b : ℕ,
        workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
            (fixedTopologyWorkload (packageR hfirstD).strategy)
            (fixedAxisWorkload (packageR hfirstD).strategy) * 2 ^ b ≤
          Fintype.card K97cubic →
        |jointProbability
            (FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam)| ≤
          1 / 2 ^ b) ∧
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
          1 / 2 ^ b) ∧
      Nonempty (OptimizedFullStrictThm54Statement (packageR hfirstD)) :=
  ⟨by norm_num, falseAcceptanceR_empty hfirstD hrootAt hrootAtQ,
    (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_soundness cfgD.challenges.lam, fun b hs => (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_bits cfgD.challenges.lam b hs,
    (packageR hfirstD).optimizedFalseAcceptance_probability_le_legacy haxR hbasisR hwidthR,
    (packageR hfirstD).optimizedFalseAcceptance_probability_le_two_pow_neg_legacy haxR hbasisR hwidthR, ⟨statementR hfirstD haxR hbasisR hwidthR⟩⟩

/-- The live released capstone still consumes the exact same package statement. -/
theorem consumed_capstone_is_inhabited 
    (hax : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasis : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidth : FormRWidth F97):
    OptimizedFullStrictThm54Statement (packageR hfirstD) :=
  optimizedFullStrictNockVMROM_of_package (packageR hfirstD) hax hbasis hwidth

end

end Nock.NockVMROM.Thm54.DistinctCensusP8FixedField

#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.statementR_p8_fixed_field_soundness
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.statementR_p8_fixed_field_bits
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.sizeWindowFailureR_empty
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.collisionFailureEventR_nonempty
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.p8_collision_object_is_present
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.falseAcceptanceR_empty_of_three_events
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.coin_eq_coinQ_of_fibre
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.falseAcceptanceR_empty_of_fibre_pinned
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.packageR_sameProblem_pins_fibre
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.fibre_pinning_is_carried_by_same_problem_only
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.alphaMCommitmentQ_tables_are_the_seed8_assignment
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.p8_fixed_field_status_R
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.accounting_unchanged
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.compute_rapcomp_at_of_satisfies
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.production_acceptance_pins_alphaM
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.production_acceptance_pins_seed
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.production_acceptance_pins_fibre
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.production_acceptance_pins_fibre_named
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.falseAcceptanceR_empty
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.both_p8_fields_classify_empty
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.accounting_after_p8_empty
#print axioms Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.consumed_capstone_is_inhabited
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.packageR
#print axioms Nock.NockVMROM.Thm54.DistinctCensusFold2.statementR
