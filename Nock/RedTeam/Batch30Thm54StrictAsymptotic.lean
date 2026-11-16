/-
  Nock/RedTeam/Batch30Thm54StrictAsymptotic.lean

  1. **The field-side hypotheses of `ProductionAsymptotic.FamilyPointwiseHypotheses` are
     unconditional** for the varying cubic family.  `b30_field_facts_unconditional` states the
     denominator shape, `11 < char`, `Ksz n < char`, the state-tag separation `hchar`, the bounded
     natural-cast injectivity `hcast`, and `(2 : K) ≠ 0` in a single proposition whose statement
     contains **no** `ProductionStrategy` at all.  There is nothing for a caller to supply.

  2. **The strict capstone needs strictly fewer premises.**
     `b30_field_side_premises_are_free` compiles the raw eleven-field bundle out of the nine-field
     `StrategyFamilyData`, and `b30_strategyData_is_exact_residual` shows the two are *equivalent*
     at the canonical atom range `q = p n` — so the reduction is not a weakening.

  The residual is named, not hidden: `StrategyFamilyData` is exactly the obligation of a concrete
  `ProductionStrategy` family, which this repository does not yet construct.  That assembly is the
  coupled downstream packet.  `b30_residual_obligations_are_strategy_shaped` shows the residual is
  not a vacuous `True`-shaped placeholder (its projections are real statements about `T`), and
  `b30_residual_majorant_fields_satisfiable` gives a genuine partial nonvacuity: for *every*
  strategy family, two of the nine residual fields — the topology and template-axis workload
  majorants — are satisfiable by an explicit definable choice of majorant.

  Scope discipline.  `b30_residual_majorant_fields_satisfiable` is a partial nonvacuity only.  It
  does **not** claim the remaining seven fields are satisfiable, and the constructed maxima carry no
  `PolynomialGrowth` receipt, which the capstone separately requires.  No `ProductionStrategy`
  inhabitant is constructed anywhere in this file.
-/

import Nock.NockVMROM.Thm54.StrictAsymptoticSecurity

namespace Nock.RedTeam.Batch30

open Filter
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExactPrimeFamily
open Nock.NockVMROM.Thm54.ProductionAsymptotic
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.StrictAsymptoticSecurity
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness

noncomputable section

/-! ## Receipts: the field-side facts hold with no strategy in sight -/

section FieldSide

variable (Ksz h : ℕ → ℕ) (kroots : ℕ)

/-- The soundness denominator of the varying family is the cubic `(p n)³`. -/
theorem b30_field_cardAt_eq_prime_cube (n : ℕ) :
    (p9ExactSecurityFamily Ksz h kroots).cardAt n = p Ksz h kroots n ^ 3 :=
  strict_cardAt_eq_prime_cube Ksz h kroots n

/-- The denominator grows faster than every polynomial. -/
theorem b30_field_card_superpolynomial (e : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) + 1) ^ e ≤ ((p9ExactSecurityFamily Ksz h kroots).cardAt n : ℝ) :=
  strict_cardAt_superpolynomial Ksz h kroots e

/-- The same growth in the explicitly cubic form. -/
theorem b30_field_prime_cube_superpolynomial (e : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) + 1) ^ e ≤ (p Ksz h kroots n : ℝ) ^ 3 :=
  strict_prime_cube_superpolynomial Ksz h kroots e

/-- The pointwise characteristic exceeds eleven, which discharges `q_gt_one` at `q = p n`. -/
theorem b30_field_char_gt_eleven (n : ℕ) : 11 < p Ksz h kroots n :=
  p9_char_gt_11 Ksz h kroots n

/-- The `Ksz`-versus-characteristic comparison consumed by the containment theorem. -/
theorem b30_field_Ksz_lt_char (n : ℕ) :
    Ksz n < ringChar (FieldAt Ksz h kroots n) :=
  strict_Ksz_lt_ringChar Ksz h kroots n

/-- `hchar` is free at the selected prime. -/
theorem b30_field_hchar_free (n : ℕ) :
    NodeEncoding.StateTagChar (FieldAt Ksz h kroots n) :=
  strict_hchar Ksz h kroots n

/-- `hcast` is free at the selected prime (Packet 2A's `charCast_injOn`). -/
theorem b30_field_hcast_free (n : ℕ) :
    Set.InjOn (fun k : ℕ => (k : FieldAt Ksz h kroots n))
      (Set.Iio (p Ksz h kroots n)) :=
  strict_charCast_injOn Ksz h kroots n

/-- `(2 : K) ≠ 0` is free at the selected prime. -/
theorem b30_field_two_ne_zero (n : ℕ) :
    (2 : FieldAt Ksz h kroots n) ≠ 0 :=
  strict_two_ne_zero Ksz h kroots n

/-- The family genuinely varies: no single characteristic works at every security parameter, so the
super-polynomial growth above is not a fixed-field statement in disguise. -/
theorem b30_family_really_varies :
    ¬ ∃ q : ℕ, ∀ n : ℕ, CharP (FieldAt Ksz h kroots n) q :=
  strict_family_not_fixed_characteristic Ksz h kroots

/-- **The field-side facts are unconditional.**  This statement mentions no `ProductionStrategy`,
no verifier, no skeleton, and no census: every conjunct is a theorem about the prime selection and
the cubic extension it carries. -/
theorem b30_field_facts_unconditional (n : ℕ) :
    (p9ExactSecurityFamily Ksz h kroots).cardAt n = p Ksz h kroots n ^ 3 ∧
      11 < p Ksz h kroots n ∧
      Ksz n < ringChar (FieldAt Ksz h kroots n) ∧
      NodeEncoding.StateTagChar (FieldAt Ksz h kroots n) ∧
      Set.InjOn (fun k : ℕ => (k : FieldAt Ksz h kroots n))
        (Set.Iio (p Ksz h kroots n)) ∧
      (2 : FieldAt Ksz h kroots n) ≠ 0 :=
  ⟨b30_field_cardAt_eq_prime_cube Ksz h kroots n,
    b30_field_char_gt_eleven Ksz h kroots n,
    b30_field_Ksz_lt_char Ksz h kroots n,
    b30_field_hchar_free Ksz h kroots n,
    b30_field_hcast_free Ksz h kroots n,
    b30_field_two_ne_zero Ksz h kroots n⟩

end FieldSide

/-! ## Receipts: strictly fewer premises, with no weakening -/

section Reduction

variable (Ksz h : ℕ → ℕ) (kroots : ℕ)
variable (T : ∀ n, ProductionStrategy
  (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))
variable (Λ topologyBound axisWorkload : ℕ → ℕ)

/-- **The field-side premises are gone.**  The raw eleven-field bundle that
`production_hasExactAsymptoticSoundness` consumes is manufactured from the nine-field
`StrategyFamilyData` alone: the caller never supplies `q`, `q_gt_one`, or
`q_le_characteristic`. -/
theorem b30_field_side_premises_are_free
    (C : ∀ n, EdgeComparisonCensus.CombinedSkeletonCensus
      (FieldAt Ksz h kroots n) (T n).skeleton (Λ n))
    (S : StrategyFamilyData Ksz h kroots T Λ topologyBound axisWorkload) :
    FamilyPointwiseHypotheses Ksz h kroots T (p Ksz h kroots) Λ
      topologyBound axisWorkload C :=
  familyPointwiseHypotheses_of_strategyData Ksz h kroots T Λ topologyBound
    axisWorkload C S

/-- **The reduction is not a weakening.**  At the canonical atom range `q = p n` the raw bundle and
the residual are equivalent propositions, so removing the field-side fields removed exactly the
redundant ones. -/
theorem b30_strategyData_is_exact_residual
    (C : ∀ n, EdgeComparisonCensus.CombinedSkeletonCensus
      (FieldAt Ksz h kroots n) (T n).skeleton (Λ n)) :
    FamilyPointwiseHypotheses Ksz h kroots T (p Ksz h kroots) Λ
        topologyBound axisWorkload C ↔
      StrategyFamilyData Ksz h kroots T Λ topologyBound axisWorkload :=
  familyPointwiseHypotheses_iff_strategyData Ksz h kroots T Λ topologyBound
    axisWorkload C

/-- **The strict capstone fires.**  Supplying only the residual and the four componentwise
polynomial-growth receipts yields the full exact asymptotic soundness class over the actual varying
cubic cardinalities. -/
theorem b30_strict_capstone_fires
    (C : ∀ n, EdgeComparisonCensus.CombinedSkeletonCensus
      (FieldAt Ksz h kroots n) (T n).skeleton (Λ n))
    (S : StrategyFamilyData Ksz h kroots T Λ topologyBound axisWorkload)
    (lmb : ∀ n, FieldAt Ksz h kroots n)
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
  strict_asymptotic_soundness_of_strategyData Ksz h kroots T lmb Λ topologyBound
    axisWorkload C S hrows hcensus htopology haxis hformR hpair hlam

/-- **The capstone factors through exactly the residual.**  Curried form: once a strategy family
carries `StrategyFamilyData`, the only remaining inputs are the four growth receipts. -/
theorem b30_capstone_factors_through_residual
    (C : ∀ n, EdgeComparisonCensus.CombinedSkeletonCensus
      (FieldAt Ksz h kroots n) (T n).skeleton (Λ n))
    (lmb : ∀ n, FieldAt Ksz h kroots n) :
    StrategyFamilyData Ksz h kroots T Λ topologyBound axisWorkload →
      (PolynomialGrowth fun n =>
          (SemanticStrategy.computeSkeletonRows (T n).skeleton).length) →
        PolynomialGrowth Λ →
          PolynomialGrowth topologyBound →
            PolynomialGrowth axisWorkload →
              (PolynomialGrowth fun n => ProductionP8Containment.formRUniformWorkload (T n)) →
              (PolynomialGrowth fun n => ProductionP8Containment.reqPairWorkload (T n) (Λ n)) →
              (∀ n ω (hz : nprSeed ω ≠ 0) i,
                (((T n).verifier.familyAt ω (lmb n) hz).exec.memoryPubAt i).lambda = ((T n).verifier.familyAt ω (lmb n) hz).cfg.challenges.lam) →
              HasExactAsymptoticSoundness
                (p9ExactSecurityFamily Ksz h kroots)
                (fun n => (productionWorkloadFamily
                  Ksz h kroots T Λ topologyBound axisWorkload n : ℝ))
                (productionBadFamily Ksz h kroots T lmb (p Ksz h kroots) Λ) :=
  fun S hrows hcensus htopology haxis hformR hpair hlam =>
    b30_strict_capstone_fires Ksz h kroots T Λ topologyBound axisWorkload C S lmb
      hrows hcensus htopology haxis hformR hpair hlam

/-- The `Ksz` comparison the containment theorem consumes really is the composition of the
strategy-side inequality with the field-side one; no independent premise is smuggled in. -/
theorem b30_specialized_Ksz_comparison_is_composed
    (S : StrategyFamilyData Ksz h kroots T Λ topologyBound axisWorkload)
    (n : ℕ) (z : FieldAt Ksz h kroots n) (hz : z ≠ 0) (α lmb) :
    (specializedProblem (T n).verifier.raw.timestamp z hz α lmb).cfg.Ksz <
      ringChar (FieldAt Ksz h kroots n) :=
  strict_specialized_Ksz_lt_ringChar Ksz h kroots T Λ topologyBound
    axisWorkload S n z hz α lmb

/-! ## Receipts: the residual is not a vacuous placeholder -/

/-- **The residual carries real content.**  Every projection is a genuine statement about the
supplied strategy family's skeleton and specialized executions, so `StrategyFamilyData` is not a
`True`-shaped placeholder. -/
theorem b30_residual_obligations_are_strategy_shaped
    (S : StrategyFamilyData Ksz h kroots T Λ topologyBound axisWorkload)
    (n : ℕ) :
    (T n).skeleton.BoundedBy (p Ksz h kroots n) ∧
      FixedCombinedBoundedBy (p Ksz h kroots n) (T n) ∧
      SizeWindowNounsBoundedBy (T n).skeleton (Λ n) ∧
      (∀ s ∈ SemanticStrategy.computeSkeletonRows (T n).skeleton,
        BoundSemanticTrace.SkeletonOperationalCore s) ∧
      (∀ (z : FieldAt Ksz h kroots n) (hz : z ≠ 0) α lmb,
        (specializedProblem (T n).verifier.raw.timestamp z hz α lmb).cfg.Ksz ≤
          Ksz n) :=
  ⟨S.skeleton_bounded n, S.combined_bounded n,
    S.size_window_nouns_bounded n, S.operational n,
    fun z hz α lmb => S.specialized_Ksz_le n z hz α lmb⟩

end Reduction

/-! ## Partial nonvacuity: the two workload majorants are satisfiable for every family

The pointwise field is finite, so the two majorant fields of the residual can be met by an explicit
definable choice: the maximum of the workload over all seed/challenge pairs.  This is a *partial*
nonvacuity receipt.  It says nothing about the seven remaining fields, and it supplies no
`PolynomialGrowth` receipt for the constructed maxima. -/

section Majorants

variable (Ksz h : ℕ → ℕ) (kroots : ℕ)
variable (T : ∀ n, ProductionStrategy
  (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))

/-- The pointwise maximum of the raw topology workload over all seed/challenge pairs. -/
def maxTopologyBound (n : ℕ) : ℕ :=
  Finset.univ.sup fun
    zα : FieldAt Ksz h kroots n × FieldAt Ksz h kroots n × FieldAt Ksz h kroots n =>
      if hz : zα.1 ≠ 0 then
        topologyWorkload
          ((T n).verifier.raw.afterAlphaM zα.1 hz zα.2.1 zα.2.2).familyData.base
      else 0

/-- The pointwise maximum of the template-axis workload over all seeds. -/
def maxAxisWorkload (n : ℕ) : ℕ :=
  Finset.univ.sup fun z : FieldAt Ksz h kroots n =>
    if hz : z ≠ 0 then
      TemplateAxisCounting.templateAxisWorkload
        (ProductionAxisStructureVerifier.committedTemplate
          (T n).verifier z hz)
    else 0

/-- The constructed topology majorant really majorizes. -/
theorem b30_maxTopologyBound_majorizes
    (n : ℕ) (z : FieldAt Ksz h kroots n) (hz : z ≠ 0) (α lmb) :
    topologyWorkload
        ((T n).verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤
      maxTopologyBound Ksz h kroots T n := by
  have hmem :
      ((z, α, lmb) : FieldAt Ksz h kroots n × FieldAt Ksz h kroots n × FieldAt Ksz h kroots n) ∈
        (Finset.univ :
          Finset (FieldAt Ksz h kroots n × FieldAt Ksz h kroots n × FieldAt Ksz h kroots n)) :=
    Finset.mem_univ _
  have hle :=
    Finset.le_sup
      (f := fun zα : FieldAt Ksz h kroots n × FieldAt Ksz h kroots n × FieldAt Ksz h kroots n =>
        if hz : zα.1 ≠ 0 then
          topologyWorkload
            ((T n).verifier.raw.afterAlphaM zα.1 hz zα.2.1 zα.2.2).familyData.base
        else 0)
      hmem
  simpa only [maxTopologyBound, dif_pos hz] using hle

/-- The constructed template-axis majorant really majorizes. -/
theorem b30_maxAxisWorkload_majorizes
    (n : ℕ) (z : FieldAt Ksz h kroots n) (hz : z ≠ 0) :
    TemplateAxisCounting.templateAxisWorkload
        (ProductionAxisStructureVerifier.committedTemplate
          (T n).verifier z hz) ≤
      maxAxisWorkload Ksz h kroots T n := by
  have hle :=
    Finset.le_sup
      (f := fun z : FieldAt Ksz h kroots n =>
        if hz : z ≠ 0 then
          TemplateAxisCounting.templateAxisWorkload
            (ProductionAxisStructureVerifier.committedTemplate
              (T n).verifier z hz)
        else 0)
      (Finset.mem_univ z)
  simpa only [maxAxisWorkload, dif_pos hz] using hle

/-- **Partial nonvacuity of the residual.**  For every strategy family the `topology_bound` and
`axis_bound` fields of `StrategyFamilyData` are satisfiable, witnessed by the explicit definable
majorants above.  The remaining seven fields, and polynomial growth of these two majorants, are not
claimed here. -/
theorem b30_residual_majorant_fields_satisfiable :
    (∀ n (z : FieldAt Ksz h kroots n) (hz : z ≠ 0) α lmb,
        topologyWorkload
            ((T n).verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤
          maxTopologyBound Ksz h kroots T n) ∧
      ∀ n (z : FieldAt Ksz h kroots n) (hz : z ≠ 0),
        TemplateAxisCounting.templateAxisWorkload
            (ProductionAxisStructureVerifier.committedTemplate
              (T n).verifier z hz) ≤
          maxAxisWorkload Ksz h kroots T n :=
  ⟨fun n z hz α lmb => b30_maxTopologyBound_majorizes Ksz h kroots T n z hz α lmb,
    fun n z hz => b30_maxAxisWorkload_majorizes Ksz h kroots T n z hz⟩

end Majorants

end

end Nock.RedTeam.Batch30

#print axioms Nock.RedTeam.Batch30.b30_field_cardAt_eq_prime_cube
#print axioms Nock.RedTeam.Batch30.b30_field_card_superpolynomial
#print axioms Nock.RedTeam.Batch30.b30_field_prime_cube_superpolynomial
#print axioms Nock.RedTeam.Batch30.b30_field_char_gt_eleven
#print axioms Nock.RedTeam.Batch30.b30_field_Ksz_lt_char
#print axioms Nock.RedTeam.Batch30.b30_field_hchar_free
#print axioms Nock.RedTeam.Batch30.b30_field_hcast_free
#print axioms Nock.RedTeam.Batch30.b30_field_two_ne_zero
#print axioms Nock.RedTeam.Batch30.b30_family_really_varies
#print axioms Nock.RedTeam.Batch30.b30_field_facts_unconditional
#print axioms Nock.RedTeam.Batch30.b30_field_side_premises_are_free
#print axioms Nock.RedTeam.Batch30.b30_strategyData_is_exact_residual
#print axioms Nock.RedTeam.Batch30.b30_strict_capstone_fires
#print axioms Nock.RedTeam.Batch30.b30_capstone_factors_through_residual
#print axioms Nock.RedTeam.Batch30.b30_specialized_Ksz_comparison_is_composed
#print axioms Nock.RedTeam.Batch30.b30_residual_obligations_are_strategy_shaped
#print axioms Nock.RedTeam.Batch30.b30_maxTopologyBound_majorizes
#print axioms Nock.RedTeam.Batch30.b30_maxAxisWorkload_majorizes
#print axioms Nock.RedTeam.Batch30.b30_residual_majorant_fields_satisfiable
