/-
  Nock/NockVMROM/Thm54/StrictAsymptoticSecurity.lean

  `ProductionAsymptotic.production_hasExactAsymptoticSoundness` proves negligible false acceptance
  over the varying cubic-extension family `p9ExactSecurityFamily`.  It consumes an twelve-field
  `FamilyPointwiseHypotheses` bundle.

  Those twelve fields are of two genuinely different kinds:

  * **Field-side facts.**  `q_gt_one`, `q_le_characteristic`, the `hchar` state-tag separation, the
    bounded natural-cast injectivity `hcast`, and the `Ksz n < char` comparison are facts about the
    *selected prime*, not about any prover strategy.  This module proves each of them
    unconditionally for the varying cubic family at the canonical atom range `q = p n`, so no caller
    ever supplies them.  This is the family-level analogue of Packet 2B's `hcast` discharge
    (`StrictContainment.production_falseAcceptance_le_at_char`).

  * **Strategy-side obligations.**  `skeleton_bounded`, `combined_bounded`, `operational`,
    `size_window_nouns_bounded`, `specialized_Ksz_le`, `program_capacity`, `memory_capacity`,
    `topology_bound`, `axis_bound` all quantify over a *given* `ProductionStrategy` family's
    skeleton and specialized executions.  They are isolated verbatim in `StrategyFamilyData`.

  `familyPointwiseHypotheses_iff_strategyData` proves that at `q = p n` the two bundles are
  equivalent: nothing is weakened by the split, and the field-side fields are exactly the redundant
  ones.  `strict_asymptotic_soundness_of_strategyData` is then the conditional capstone with
  strictly fewer premises than the raw theorem.

  This module deliberately constructs **no** `ProductionStrategy` inhabitant.  `StrategyFamilyData`
  is the precise, named residual that a concrete production strategy family must discharge; that
  assembly is a separate packet.
-/

import Nock.NockVMROM.Thm54.ProductionAsymptotic
import Nock.NockVMROM.Thm54.StrictRawReconstruction

namespace Nock.NockVMROM.Thm54
namespace StrictAsymptoticSecurity

open scoped Topology
open Filter
open Nock.Framework
open Nock.NockVMROM
open ExactPrimeFamily
open ProductionAsymptotic
open ProductionP8Containment
open SizeWindowCounting
open TemplateRawJointSoundness

noncomputable section

variable (Ksz h : ℕ → ℕ) (kroots : ℕ)

/-! ## Field-side facts, proved unconditionally at every selected prime

Everything in this section is a theorem about the prime selection and the cubic extension it
carries.  No `ProductionStrategy` appears. -/

/-- **The strict denominator is the cubic cardinality.**  The soundness denominator of the varying
family is exactly `(p n)³`, the paper's `e = 3` Goldilocks cubic shape. -/
theorem strict_cardAt_eq_prime_cube (n : ℕ) :
    (p9ExactSecurityFamily Ksz h kroots).cardAt n = p Ksz h kroots n ^ 3 :=
  p9_exactSecurityFamily_card Ksz h kroots n

/-- **Super-polynomial growth of the actual denominator.**  This is the growth side of the paper's
`negl(𝕂)` requirement. -/
theorem strict_cardAt_superpolynomial (e : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) + 1) ^ e ≤ ((p9ExactSecurityFamily Ksz h kroots).cardAt n : ℝ) :=
  p9_card_superpolynomial Ksz h kroots e

/-- The same growth statement written directly in the cubic form `(p n)³`, i.e. the strengthened
denominator-explicit version of `strict_cardAt_superpolynomial`. -/
theorem strict_prime_cube_superpolynomial (e : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) + 1) ^ e ≤ (p Ksz h kroots n : ℝ) ^ 3 := by
  filter_upwards [strict_cardAt_superpolynomial Ksz h kroots e] with n hn
  rw [strict_cardAt_eq_prime_cube] at hn
  push_cast at hn
  exact hn

/-- **The family really varies.**  No single characteristic works at every security parameter, so
the growth above is not a fixed-field statement in disguise. -/
theorem strict_family_not_fixed_characteristic :
    ¬ ∃ q : ℕ, ∀ n : ℕ, CharP (FieldAt Ksz h kroots n) q :=
  p9_family_not_fixed_characteristic Ksz h kroots

/-- Field-side discharge of `FamilyPointwiseHypotheses.q_gt_one` at the canonical atom range
`q = p n`, from `11 < p n`. -/
theorem strict_q_gt_one (n : ℕ) : 1 < p Ksz h kroots n := by
  have hp := p9_char_gt_11 Ksz h kroots n
  omega

/-- Field-side discharge of `FamilyPointwiseHypotheses.q_le_characteristic`: at the canonical atom
range the bound is the characteristic itself. -/
theorem strict_q_le_characteristic (n : ℕ) :
    p Ksz h kroots n ≤ p Ksz h kroots n :=
  le_rfl

/-- Field-side discharge of the `hchar` state-tag separation premise. -/
theorem strict_hchar (n : ℕ) :
    NodeEncoding.StateTagChar (FieldAt Ksz h kroots n) :=
  p9_hchar Ksz h kroots n

/-- The `ringChar` of the pointwise field is the selected prime, so the canonical atom range and
the characteristic agree. -/
theorem strict_ringChar_eq (n : ℕ) :
    ringChar (FieldAt Ksz h kroots n) = p Ksz h kroots n :=
  @ringChar.eq (FieldAt Ksz h kroots n) _ (p Ksz h kroots n)
    (p9_FieldAt_charP Ksz h kroots n)

/-- Field-side discharge of the bounded natural-cast injectivity premise `hcast`, via Packet 2A's
`StrictRawReconstruction.charCast_injOn`. -/
theorem strict_charCast_injOn (n : ℕ) :
    Set.InjOn (fun k : ℕ => (k : FieldAt Ksz h kroots n))
      (Set.Iio (p Ksz h kroots n)) :=
  @StrictRawReconstruction.charCast_injOn (FieldAt Ksz h kroots n) _
    (p Ksz h kroots n) (p9_FieldAt_charP Ksz h kroots n)

/-- Field-side discharge of `(2 : K) ≠ 0`, from `11 < p n`. -/
theorem strict_two_ne_zero (n : ℕ) :
    (2 : FieldAt Ksz h kroots n) ≠ 0 := by
  intro hzero
  have hnat : (2 : ℕ) = 0 :=
    (strict_hchar Ksz h kroots n)
      (show (2 : ℕ) ∈ Set.Iic 11 by simp)
      (show (0 : ℕ) ∈ Set.Iic 11 by simp)
      (by simpa using hzero)
  omega

/-- **The field-side half of the `Ksz` comparison.**  The IO/K-size budget is below the pointwise
characteristic unconditionally; only the strategy-side inequality
`specializedProblem ….cfg.Ksz ≤ Ksz n` remains. -/
theorem strict_Ksz_lt_ringChar (n : ℕ) :
    Ksz n < ringChar (FieldAt Ksz h kroots n) := by
  rw [strict_ringChar_eq]
  exact p9_Ksz_lt Ksz h kroots n

/-! ## The strategy-dependent residual, isolated

Every field below quantifies over the supplied `ProductionStrategy` family.  None of them is a
consequence of the prime selection, so none is discharged here.  `StrategyFamilyData` is therefore
the exact residual obligation of a concrete production-strategy family. -/

/-- **The strategy-inhabitant residual.**  Exactly the fields of
`ProductionAsymptotic.FamilyPointwiseHypotheses` that genuinely depend on the supplied
`ProductionStrategy` family, taken verbatim at the canonical atom range `q = p n`.

The field-side fields `q_gt_one` and `q_le_characteristic` are absent because they are proved
above; the `Ksz`-vs-characteristic comparison is absent because `strict_Ksz_lt_ringChar` supplies
it, leaving only the strategy-side inequality `specialized_Ksz_le`.

Note that the combined census `C` is *not* a parameter: no strategy-side field mentions it. -/
structure StrategyFamilyData
    (Ksz h : ℕ → ℕ) (kroots : ℕ)
    (T : ∀ n, ProductionStrategy
      (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))
    (Λ topologyBound axisWorkload : ℕ → ℕ) : Prop where
  /-- Every skeleton atom is a canonical residue below the pointwise characteristic. -/
  skeleton_bounded : ∀ n, (T n).skeleton.BoundedBy (p Ksz h kroots n)
  /-- Every combined-census occurrence is likewise bounded. -/
  combined_bounded : ∀ n, FixedCombinedBoundedBy (p Ksz h kroots n) (T n)
  /-- Each committed compute row satisfies the operational core at that bound. -/
  operational :
    ∀ n, ∀ s ∈ SemanticStrategy.computeSkeletonRows (T n).skeleton,
      BoundSemanticTrace.SkeletonOperationalCore s
  /-- The noun-leaf size window bounds the skeleton's nouns. -/
  size_window_nouns_bounded :
    ∀ n, SizeWindowNounsBoundedBy (T n).skeleton (Λ n)
  /-- The specialized problem's IO/K-size stays inside the declared budget.  The remaining
  comparison with the characteristic is `strict_Ksz_lt_ringChar`, a field-side fact. -/
  specialized_Ksz_le :
    ∀ n (z : FieldAt Ksz h kroots n) (hz : z ≠ 0) α lmb,
      (specializedProblem (T n).verifier.raw.timestamp z hz α lmb).cfg.Ksz ≤
        Ksz n
  /-- Program-IO capacity at the orbit exponent. -/
  program_capacity :
    ∀ n (z : FieldAt Ksz h kroots n) (hz : z ≠ 0) α lmb,
      (specializedProblem (T n).verifier.raw.timestamp z hz α lmb).exec.derivedRequestIO.length + 1 ≤
        2 ^ (specializedProblem (T n).verifier.raw.timestamp z hz α lmb).cfg.orbit.h
  /-- Memory-IO capacity at the orbit exponent. -/
  memory_capacity :
    ∀ n (z : FieldAt Ksz h kroots n) (hz : z ≠ 0) α lmb,
      (specializedProblem (T n).verifier.raw.timestamp z hz α lmb).exec.derivedResponseIO.length + 1 ≤
        2 ^ (specializedProblem (T n).verifier.raw.timestamp z hz α lmb).cfg.orbit.h
  /-- The actual topology workload majorant. -/
  topology_bound :
    ∀ n (z : FieldAt Ksz h kroots n) (hz : z ≠ 0) α lmb,
      topologyWorkload
          ((T n).verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤
        topologyBound n
  binds : ∀ n, (T n).BindsAll
  /-- The actual template-axis workload majorant. -/
  axis_bound :
    ∀ n (z : FieldAt Ksz h kroots n) (hz : z ≠ 0),
      TemplateAxisCounting.templateAxisWorkload
          (ProductionAxisStructureVerifier.committedTemplate
            (T n).verifier z hz) ≤
        axisWorkload n

/-! ## The split is exact: field facts are free, strategy facts are the residual -/

/-- **Field-side discharge.**  A strategy family carrying only `StrategyFamilyData` already
satisfies the full twelve-field `FamilyPointwiseHypotheses` bundle at `q = p n`: the missing fields
are supplied by the prime selection. -/
theorem familyPointwiseHypotheses_of_strategyData
    (T : ∀ n, ProductionStrategy
      (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))
    (Λ topologyBound axisWorkload : ℕ → ℕ)
    (C : ∀ n, EdgeComparisonCensus.CombinedSkeletonCensus
      (FieldAt Ksz h kroots n) (T n).skeleton (Λ n))
    (S : StrategyFamilyData Ksz h kroots T Λ topologyBound axisWorkload) :
    FamilyPointwiseHypotheses Ksz h kroots T (p Ksz h kroots) Λ
      topologyBound axisWorkload C where
  q_gt_one := strict_q_gt_one Ksz h kroots
  q_eq_characteristic := fun _ => rfl
  skeleton_bounded := S.skeleton_bounded
  combined_bounded := S.combined_bounded
  operational := S.operational
  size_window_nouns_bounded := S.size_window_nouns_bounded
  specialized_Ksz_le := S.specialized_Ksz_le
  program_capacity := S.program_capacity
  memory_capacity := S.memory_capacity
  topology_bound := S.topology_bound
  binds := S.binds
  axis_bound := S.axis_bound

/-- **No weakening.**  Conversely the raw bundle at `q = p n` contains the residual verbatim, so
the split loses nothing. -/
theorem strategyData_of_familyPointwiseHypotheses
    (T : ∀ n, ProductionStrategy
      (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))
    (Λ topologyBound axisWorkload : ℕ → ℕ)
    (C : ∀ n, EdgeComparisonCensus.CombinedSkeletonCensus
      (FieldAt Ksz h kroots n) (T n).skeleton (Λ n))
    (H : FamilyPointwiseHypotheses Ksz h kroots T (p Ksz h kroots) Λ
      topologyBound axisWorkload C) :
    StrategyFamilyData Ksz h kroots T Λ topologyBound axisWorkload where
  skeleton_bounded := H.skeleton_bounded
  combined_bounded := H.combined_bounded
  operational := H.operational
  size_window_nouns_bounded := H.size_window_nouns_bounded
  specialized_Ksz_le := H.specialized_Ksz_le
  program_capacity := H.program_capacity
  memory_capacity := H.memory_capacity
  topology_bound := H.topology_bound
  binds := H.binds
  axis_bound := H.axis_bound

/-- **The split is exact.**  At the canonical atom range `q = p n` the raw pointwise bundle and the
strategy-side residual are equivalent propositions.  Read left-to-right this says the residual is
no stronger; read right-to-left it says the field-side fields are free. -/
theorem familyPointwiseHypotheses_iff_strategyData
    (T : ∀ n, ProductionStrategy
      (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))
    (Λ topologyBound axisWorkload : ℕ → ℕ)
    (C : ∀ n, EdgeComparisonCensus.CombinedSkeletonCensus
      (FieldAt Ksz h kroots n) (T n).skeleton (Λ n)) :
    FamilyPointwiseHypotheses Ksz h kroots T (p Ksz h kroots) Λ
        topologyBound axisWorkload C ↔
      StrategyFamilyData Ksz h kroots T Λ topologyBound axisWorkload :=
  ⟨strategyData_of_familyPointwiseHypotheses Ksz h kroots T Λ topologyBound
      axisWorkload C,
    familyPointwiseHypotheses_of_strategyData Ksz h kroots T Λ topologyBound
      axisWorkload C⟩

/-- The composed `Ksz` comparison the containment theorem actually consumes: the strategy-side
inequality composed with the field-side `strict_Ksz_lt_ringChar`. -/
theorem strict_specialized_Ksz_lt_ringChar
    (T : ∀ n, ProductionStrategy
      (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))
    (Λ topologyBound axisWorkload : ℕ → ℕ)
    (S : StrategyFamilyData Ksz h kroots T Λ topologyBound axisWorkload)
    (n : ℕ) (z : FieldAt Ksz h kroots n) (hz : z ≠ 0) (α lmb) :
    (specializedProblem (T n).verifier.raw.timestamp z hz α lmb).cfg.Ksz <
      ringChar (FieldAt Ksz h kroots n) :=
  (S.specialized_Ksz_le n z hz α lmb).trans_lt
    (strict_Ksz_lt_ringChar Ksz h kroots n)

/-! ## The strict conditional capstones -/

/-- Same conclusion as
`ProductionAsymptotic.production_pointwiseP8Bound`, but the caller supplies only
`StrategyFamilyData`: the atom range is fixed to the canonical `q = p n` and the field-side
premises are discharged internally. -/
theorem strict_pointwiseP8Bound_of_strategyData
    (T : ∀ n, ProductionStrategy
      (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))
    (lmb : ∀ n, FieldAt Ksz h kroots n)
    (Λ topologyBound axisWorkload : ℕ → ℕ)
    (C : ∀ n, EdgeComparisonCensus.CombinedSkeletonCensus
      (FieldAt Ksz h kroots n) (T n).skeleton (Λ n))
    (S : StrategyFamilyData Ksz h kroots T Λ topologyBound axisWorkload)
    (hlam : ∀ n ω (hz : nprSeed ω ≠ 0) i,
      (((T n).verifier.familyAt ω (lmb n) hz).exec.memoryPubAt i).lambda = ((T n).verifier.familyAt ω (lmb n) hz).cfg.challenges.lam) :
    PointwiseP8Bound
      (p9ExactSecurityFamily Ksz h kroots)
      (fun n => (productionWorkloadFamily
        Ksz h kroots T Λ topologyBound axisWorkload n : ℝ))
      (productionBadFamily Ksz h kroots T lmb (p Ksz h kroots) Λ) :=
  production_pointwiseP8Bound Ksz h kroots T lmb (p Ksz h kroots) Λ
    topologyBound axisWorkload C
    (familyPointwiseHypotheses_of_strategyData Ksz h kroots T Λ topologyBound
      axisWorkload C S) hlam

/-- Given a varying `e = 3`
cubic family, a combined census, the strategy-side residual `StrategyFamilyData`, and the four
componentwise `PolynomialGrowth` receipts, false acceptance over the actual varying cubic field
cardinalities has its verified pointwise bound and is negligible.

The caller supplies strictly fewer premises than
`ProductionAsymptotic.production_hasExactAsymptoticSoundness`: the atom-range function `q` is no
longer a parameter, and `q_gt_one`, `q_le_characteristic`, `hchar`, `hcast`, `(2 : K) ≠ 0` and the
`Ksz`-vs-characteristic comparison are all discharged from the prime selection. -/
theorem strict_asymptotic_soundness_of_strategyData
    (T : ∀ n, ProductionStrategy
      (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))
    (lmb : ∀ n, FieldAt Ksz h kroots n)
    (Λ topologyBound axisWorkload : ℕ → ℕ)
    (C : ∀ n, EdgeComparisonCensus.CombinedSkeletonCensus
      (FieldAt Ksz h kroots n) (T n).skeleton (Λ n))
    (S : StrategyFamilyData Ksz h kroots T Λ topologyBound axisWorkload)
    (hrows : PolynomialGrowth fun n =>
      (SemanticStrategy.computeSkeletonRows (T n).skeleton).length)
    (hcensus : PolynomialGrowth Λ)
    (htopology : PolynomialGrowth topologyBound)
    (haxis : PolynomialGrowth axisWorkload)
    (hformR : PolynomialGrowth fun n => ProductionP8Containment.formRUniformWorkload (T n))
    (hpair : PolynomialGrowth fun n => ProductionP8Containment.reqPairWorkload (T n) (Λ n))
    (hlam : ∀ n ω (hz : nprSeed ω ≠ 0) i,
      (((T n).verifier.familyAt ω (lmb n) hz).exec.memoryPubAt i).lambda = ((T n).verifier.familyAt ω (lmb n) hz).cfg.challenges.lam) :
    HasExactAsymptoticSoundness
      (p9ExactSecurityFamily Ksz h kroots)
      (fun n => (productionWorkloadFamily
        Ksz h kroots T Λ topologyBound axisWorkload n : ℝ))
      (productionBadFamily Ksz h kroots T lmb (p Ksz h kroots) Λ) :=
  production_hasExactAsymptoticSoundness Ksz h kroots T lmb (p Ksz h kroots) Λ
    topologyBound axisWorkload C
    (familyPointwiseHypotheses_of_strategyData Ksz h kroots T Λ topologyBound
      axisWorkload C S)
    hrows hcensus htopology haxis hformR hpair hlam

/-- **Negligibility, extracted.**  The bad-event family of the strict capstone is negligible. -/
theorem strict_negligible_of_strategyData
    (T : ∀ n, ProductionStrategy
      (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))
    (lmb : ∀ n, FieldAt Ksz h kroots n)
    (Λ topologyBound axisWorkload : ℕ → ℕ)
    (C : ∀ n, EdgeComparisonCensus.CombinedSkeletonCensus
      (FieldAt Ksz h kroots n) (T n).skeleton (Λ n))
    (S : StrategyFamilyData Ksz h kroots T Λ topologyBound axisWorkload)
    (hrows : PolynomialGrowth fun n =>
      (SemanticStrategy.computeSkeletonRows (T n).skeleton).length)
    (hcensus : PolynomialGrowth Λ)
    (htopology : PolynomialGrowth topologyBound)
    (haxis : PolynomialGrowth axisWorkload)
    (hformR : PolynomialGrowth fun n => ProductionP8Containment.formRUniformWorkload (T n))
    (hpair : PolynomialGrowth fun n => ProductionP8Containment.reqPairWorkload (T n) (Λ n))
    (hlam : ∀ n ω (hz : nprSeed ω ≠ 0) i,
      (((T n).verifier.familyAt ω (lmb n) hz).exec.memoryPubAt i).lambda = ((T n).verifier.familyAt ω (lmb n) hz).cfg.challenges.lam) :
    Negligible (productionBadFamily Ksz h kroots T lmb (p Ksz h kroots) Λ) :=
  (strict_asymptotic_soundness_of_strategyData Ksz h kroots T lmb Λ topologyBound
    axisWorkload C S hrows hcensus htopology haxis hformR hpair hlam).negligible

/-- **The workload/cardinality ratio vanishes.**  The exact five-class production workload divided
by the actual varying cubic cardinality tends to zero.  This needs only the four growth receipts:
it is a statement about the numerator's growth against `(p n)³`, so not even the strategy-side
residual is required. -/
theorem strict_workload_div_card_tendsto_zero
    (T : ∀ n, ProductionStrategy
      (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))
    (Λ topologyBound axisWorkload : ℕ → ℕ)
    (hrows : PolynomialGrowth fun n =>
      (SemanticStrategy.computeSkeletonRows (T n).skeleton).length)
    (hcensus : PolynomialGrowth Λ)
    (htopology : PolynomialGrowth topologyBound)
    (haxis : PolynomialGrowth axisWorkload)
    (hformR : PolynomialGrowth fun n => ProductionP8Containment.formRUniformWorkload (T n))
    (hpair : PolynomialGrowth fun n => ProductionP8Containment.reqPairWorkload (T n) (Λ n)) :
    Tendsto
      (fun n =>
        (productionWorkloadFamily
            Ksz h kroots T Λ topologyBound axisWorkload n : ℝ) /
          ((p9ExactSecurityFamily Ksz h kroots).cardAt n : ℝ))
      atTop (𝓝 0) :=
  production_workload_div_card_tendsto_zero Ksz h kroots T Λ topologyBound
    axisWorkload hrows hcensus htopology haxis hformR hpair

/-- The same limit with the denominator written explicitly as the cubic `(p n)³`. -/
theorem strict_workload_div_prime_cube_tendsto_zero
    (T : ∀ n, ProductionStrategy
      (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))
    (Λ topologyBound axisWorkload : ℕ → ℕ)
    (hrows : PolynomialGrowth fun n =>
      (SemanticStrategy.computeSkeletonRows (T n).skeleton).length)
    (hcensus : PolynomialGrowth Λ)
    (htopology : PolynomialGrowth topologyBound)
    (haxis : PolynomialGrowth axisWorkload)
    (hformR : PolynomialGrowth fun n => ProductionP8Containment.formRUniformWorkload (T n))
    (hpair : PolynomialGrowth fun n => ProductionP8Containment.reqPairWorkload (T n) (Λ n)) :
    Tendsto
      (fun n =>
        (productionWorkloadFamily
            Ksz h kroots T Λ topologyBound axisWorkload n : ℝ) /
          (p Ksz h kroots n : ℝ) ^ 3)
      atTop (𝓝 0) := by
  have hbase :=
    strict_workload_div_card_tendsto_zero Ksz h kroots T Λ topologyBound
      axisWorkload hrows hcensus htopology haxis hformR hpair
  refine hbase.congr fun n => ?_
  rw [strict_cardAt_eq_prime_cube]
  push_cast
  ring

end

end StrictAsymptoticSecurity
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.strict_cardAt_eq_prime_cube
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.strict_cardAt_superpolynomial
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.strict_prime_cube_superpolynomial
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.strict_family_not_fixed_characteristic
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.strict_q_gt_one
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.strict_q_le_characteristic
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.strict_hchar
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.strict_ringChar_eq
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.strict_charCast_injOn
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.strict_two_ne_zero
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.strict_Ksz_lt_ringChar
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.familyPointwiseHypotheses_of_strategyData
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.strategyData_of_familyPointwiseHypotheses
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.familyPointwiseHypotheses_iff_strategyData
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.strict_specialized_Ksz_lt_ringChar
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.strict_pointwiseP8Bound_of_strategyData
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.strict_asymptotic_soundness_of_strategyData
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.strict_negligible_of_strategyData
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.strict_workload_div_card_tendsto_zero
#print axioms Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.strict_workload_div_prime_cube_tendsto_zero
