import Nock.NockVMROM.Thm54.ProductionP8Containment

/-!
# Production P8 to varying cubic-extension asymptotics

This module assembles the production pointwise false-acceptance theorem over the exact varying
cubic-extension family.  The strategy remains the phase-correct production strategy: no semantic
witness, accepting response, or target is added to a prover message.

The asymptotic input is deliberately componentwise. Their product in the NPR term is retained; no field-size-independent uniform bound is
asserted. -/

namespace Nock.NockVMROM.Thm54.ProductionAsymptotic

open scoped Topology

open Filter
open Nock.Framework
open Nock.NockVMROM
open ExactPrimeFamily
open ProductionP8Containment
open SizeWindowCounting
open TemplateRawJointSoundness

noncomputable section

/-- Expose the canonical characteristic instance needed by the production strategy at each
varying cubic-extension field. -/
instance primeFieldAt_charRing
    (Ksz h : ℕ → ℕ) (kroots n : ℕ) :
    CharP (FieldAt Ksz h kroots n) (ringChar (FieldAt Ksz h kroots n)) :=
  ringChar.charP _

/-! ## Polynomial growth with an honest leading coefficient -/

/-- A natural-valued family is bounded by one polynomial monomial with an explicit coefficient.
Keeping the coefficient avoids the impossible requirement that every nontrivial workload be at
most `(n + 1)^d` at `n = 0`. -/
structure PolynomialGrowth (f : ℕ → ℕ) where
  coefficient : ℕ
  degree : ℕ
  bound : ∀ n, f n ≤ coefficient * (n + 1) ^ degree

namespace PolynomialGrowth

def const (c : ℕ) : PolynomialGrowth (fun _ => c) where
  coefficient := c
  degree := 0
  bound := by simp

def add {f g : ℕ → ℕ} (hf : PolynomialGrowth f) (hg : PolynomialGrowth g) :
    PolynomialGrowth (fun n => f n + g n) where
  coefficient := hf.coefficient + hg.coefficient
  degree := max hf.degree hg.degree
  bound := by
    intro n
    have hx : 1 ≤ n + 1 := by omega
    have hfpow :
        (n + 1) ^ hf.degree ≤ (n + 1) ^ max hf.degree hg.degree :=
      Nat.pow_le_pow_right hx (le_max_left _ _)
    have hgpow :
        (n + 1) ^ hg.degree ≤ (n + 1) ^ max hf.degree hg.degree :=
      Nat.pow_le_pow_right hx (le_max_right _ _)
    calc
      f n + g n
          ≤ hf.coefficient * (n + 1) ^ hf.degree +
              hg.coefficient * (n + 1) ^ hg.degree :=
        Nat.add_le_add (hf.bound n) (hg.bound n)
      _ ≤ hf.coefficient * (n + 1) ^ max hf.degree hg.degree +
            hg.coefficient * (n + 1) ^ max hf.degree hg.degree :=
        Nat.add_le_add
          (Nat.mul_le_mul_left hf.coefficient hfpow)
          (Nat.mul_le_mul_left hg.coefficient hgpow)
      _ = (hf.coefficient + hg.coefficient) *
            (n + 1) ^ max hf.degree hg.degree := by ring

def mul {f g : ℕ → ℕ} (hf : PolynomialGrowth f) (hg : PolynomialGrowth g) :
    PolynomialGrowth (fun n => f n * g n) where
  coefficient := hf.coefficient * hg.coefficient
  degree := hf.degree + hg.degree
  bound := by
    intro n
    calc
      f n * g n
          ≤ (hf.coefficient * (n + 1) ^ hf.degree) *
              (hg.coefficient * (n + 1) ^ hg.degree) :=
        Nat.mul_le_mul (hf.bound n) (hg.bound n)
      _ = (hf.coefficient * hg.coefficient) *
            (n + 1) ^ (hf.degree + hg.degree) := by
        rw [pow_add]
        ring

def scale (c : ℕ) {f : ℕ → ℕ} (hf : PolynomialGrowth f) :
    PolynomialGrowth (fun n => c * f n) :=
  mul (const c) hf

def sub {f g : ℕ → ℕ} (hf : PolynomialGrowth f) :
    PolynomialGrowth (fun n => f n - g n) where
  coefficient := hf.coefficient
  degree := hf.degree
  bound := fun n => (Nat.sub_le _ _).trans (hf.bound n)

/-- A coefficient-bearing polynomial bound can be absorbed into one extra degree eventually.
This is the only finite-prefix step used by the asymptotic assembly. -/
theorem eventually_bound_by_monic {f : ℕ → ℕ} (hf : PolynomialGrowth f) :
    ∀ᶠ n : ℕ in atTop, f n ≤ (n + 1) ^ (hf.degree + 1) := by
  filter_upwards [eventually_ge_atTop hf.coefficient] with n hn
  have hcoeff : hf.coefficient ≤ n + 1 := hn.trans (Nat.le_succ n)
  calc
    f n ≤ hf.coefficient * (n + 1) ^ hf.degree := hf.bound n
    _ ≤ (n + 1) * (n + 1) ^ hf.degree :=
      Nat.mul_le_mul_right ((n + 1) ^ hf.degree) hcoeff
    _ = (n + 1) ^ (hf.degree + 1) := by
      rw [pow_succ]
      ring

end PolynomialGrowth



/-- The triangular low-order root numerator grows polynomially with the noun-window bound. -/
def sizeWindowRootBoundGrowth
    {Λ : ℕ → ℕ} (hΛ : PolynomialGrowth Λ) :
    PolynomialGrowth fun n => sizeWindowRootBound (Λ n) where
  coefficient := hΛ.coefficient * hΛ.coefficient
  degree := hΛ.degree + hΛ.degree
  bound := by
    intro n
    calc
      sizeWindowRootBound (Λ n) ≤ Λ n * Λ n :=
        sizeWindowRootBound_le_square (Λ n)
      _ ≤ (hΛ.coefficient * (n + 1) ^ hΛ.degree) *
            (hΛ.coefficient * (n + 1) ^ hΛ.degree) :=
        Nat.mul_le_mul (hΛ.bound n) (hΛ.bound n)
      _ = (hΛ.coefficient * hΛ.coefficient) *
            (n + 1) ^ (hΛ.degree + hΛ.degree) := by
        rw [pow_add]
        ring

/-- Componentwise polynomial data give polynomial growth of the exact five-class production
workload.  In particular the row/census product is proved polynomial rather than assumed
uniformly bounded. -/
def productionWorkloadGrowth
    (Ksz h : ℕ → ℕ) (kroots : ℕ)
    (T : ∀ n, ProductionStrategy
      (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))
    (Λ topologyBound axisWorkload : ℕ → ℕ)
    (hrows : PolynomialGrowth fun n =>
      (SemanticStrategy.computeSkeletonRows (T n).skeleton).length)
    (hcensus : PolynomialGrowth Λ)
    (htopology : PolynomialGrowth topologyBound)
    (haxis : PolynomialGrowth axisWorkload)
    (hformR : PolynomialGrowth fun n => formRUniformWorkload (T n))
    (hpair : PolynomialGrowth fun n => reqPairWorkload (T n) (Λ n)) :
    PolynomialGrowth fun n =>
      workload (T n) (Λ n) (topologyBound n) (axisWorkload n) := by
  let hcollision :=
    PolynomialGrowth.mul
      (PolynomialGrowth.add (PolynomialGrowth.const 3)
        (PolynomialGrowth.scale 19 hrows))
      (PolynomialGrowth.sub (g := fun _ => 1)
        (PolynomialGrowth.scale 2 hcensus))
  simpa only [workload] using
    PolynomialGrowth.add
      (PolynomialGrowth.add
        (PolynomialGrowth.add
          (PolynomialGrowth.add
            (PolynomialGrowth.add
              (PolynomialGrowth.add (PolynomialGrowth.const 1) hcollision)
              htopology)
            haxis)
          hformR)
        hpair)
      (sizeWindowRootBoundGrowth hcensus)

/-! ## Coefficient-aware exact-family asymptotics -/

/-- The existing exact-family pointwise interface remains sufficient when the natural workload has
an explicit polynomial coefficient.  The coefficient is absorbed only eventually, so no condition
on the finite prefix is fabricated. -/
theorem hasExactAsymptoticSoundness_of_polynomialGrowth
    (Fam : ExactSecurityFamily)
    (workload : ℕ → ℕ) (bad : ℕ → ℝ)
    (hwork : PolynomialGrowth workload)
    (hcard_growth :
      ∀ e : ℕ, ∀ᶠ n : ℕ in atTop,
        ((n : ℝ) + 1) ^ e ≤ (Fam.cardAt n : ℝ))
    (hpointwise :
      PointwiseP8Bound Fam (fun n => (workload n : ℝ)) bad) :
    HasExactAsymptoticSoundness Fam (fun n => (workload n : ℝ)) bad := by
  have hmajor :
      Negligible (fun n =>
        ((n : ℝ) + 1) ^ (hwork.degree + 1) / (Fam.cardAt n : ℝ)) :=
    negligible_workload_div_field
      (fun n => ((n : ℝ) + 1) ^ (hwork.degree + 1))
      (fun n => (Fam.cardAt n : ℝ))
      (hwork.degree + 1)
      (fun n => by
        rw [abs_of_nonneg]
        positivity)
      (fun n => by exact_mod_cast Fam.cardAt_pos n)
      hcard_growth
  refine ⟨hpointwise, ?_⟩
  intro c
  filter_upwards [hmajor c, hwork.eventually_bound_by_monic] with n hn hmono
  have hcard_pos : 0 < (Fam.cardAt n : ℝ) := by
    exact_mod_cast Fam.cardAt_pos n
  have hmonoReal :
      (workload n : ℝ) ≤ ((n : ℝ) + 1) ^ (hwork.degree + 1) := by
    exact_mod_cast hmono
  calc
    |bad n| ≤ (workload n : ℝ) / (Fam.cardAt n : ℝ) :=
      hpointwise n
    _ ≤ ((n : ℝ) + 1) ^ (hwork.degree + 1) /
          (Fam.cardAt n : ℝ) :=
      div_le_div_of_nonneg_right hmonoReal hcard_pos.le
    _ = |((n : ℝ) + 1) ^ (hwork.degree + 1) /
          (Fam.cardAt n : ℝ)| := by
      rw [abs_of_nonneg]
      positivity
    _ ≤ ((n : ℝ) + 1) ^ (-(c : ℤ)) := hn

/-- Negligibility implies ordinary convergence to zero. -/
theorem Negligible.tendsto_zero {f : ℕ → ℝ} (hf : Negligible f) :
    Tendsto f atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => norm_nonneg (f n)
  · filter_upwards [hf 1] with n hn
    simpa [Real.norm_eq_abs, zpow_neg_one] using hn
  · simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-! ## Production theorem over the varying cubic-extension family -/

/-- The exact natural numerator from the production five-class failure union. -/
def productionWorkloadFamily
    (Ksz h : ℕ → ℕ) (kroots : ℕ)
    (T : ∀ n, ProductionStrategy
      (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))
    (Λ topologyBound axisWorkload : ℕ → ℕ) (n : ℕ) : ℕ :=
  workload (T n) (Λ n) (topologyBound n) (axisWorkload n)

/-- The actual normalized production false-acceptance event at each varying cubic field. -/
def productionBadFamily
    (Ksz h : ℕ → ℕ) (kroots : ℕ)
    (T : ∀ n, ProductionStrategy
      (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))
    (lmb : ∀ n, FieldAt Ksz h kroots n)
    (q Λ : ℕ → ℕ) (n : ℕ) : ℝ :=
  jointProbability
    (FalseAcceptanceSet (T n) (q n) (Λ n) (lmb n))

/-- External, pointwise premises needed by `production_jointProbability_falseAcceptance_le`.

This proposition is not part of `ProductionStrategy` and is not available to the verifier.  It
contains no response, acceptance proof, evaluator, genuine witness, or target.  The selected prime
itself discharges state-tag separation, `(2 : K) ≠ 0`, and bounded natural-cast injectivity; only
the semantic/capacity facts and the actual topology/axis majorants remain here. -/
structure FamilyPointwiseHypotheses
    (Ksz h : ℕ → ℕ) (kroots : ℕ)
    (T : ∀ n, ProductionStrategy
      (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))
    (q Λ topologyBound axisWorkload : ℕ → ℕ)
    (C : ∀ n, EdgeComparisonCensus.CombinedSkeletonCensus
      (FieldAt Ksz h kroots n) (T n).skeleton (Λ n)) : Prop where
  q_gt_one : ∀ n, 1 < q n
  q_eq_characteristic : ∀ n, q n = p Ksz h kroots n
  skeleton_bounded : ∀ n, (T n).skeleton.BoundedBy (q n)
  combined_bounded : ∀ n, FixedCombinedBoundedBy (q n) (T n)
  operational :
    ∀ n, ∀ s ∈ SemanticStrategy.computeSkeletonRows (T n).skeleton,
      BoundSemanticTrace.SkeletonOperationalCore s
  size_window_nouns_bounded :
    ∀ n, SizeWindowNounsBoundedBy (T n).skeleton (Λ n)
  specialized_Ksz_le :
    ∀ n (z : FieldAt Ksz h kroots n) (hz : z ≠ 0) α lmb,
      (specializedProblem (T n).verifier.raw.timestamp z hz α lmb).cfg.Ksz ≤
        Ksz n
  program_capacity :
    ∀ n (z : FieldAt Ksz h kroots n) (hz : z ≠ 0) α lmb,
      (specializedProblem (T n).verifier.raw.timestamp z hz α lmb).exec.derivedRequestIO.length + 1 ≤
        2 ^ (specializedProblem (T n).verifier.raw.timestamp z hz α lmb).cfg.orbit.h
  memory_capacity :
    ∀ n (z : FieldAt Ksz h kroots n) (hz : z ≠ 0) α lmb,
      (specializedProblem (T n).verifier.raw.timestamp z hz α lmb).exec.derivedResponseIO.length + 1 ≤
        2 ^ (specializedProblem (T n).verifier.raw.timestamp z hz α lmb).cfg.orbit.h
  topology_bound :
    ∀ n (z : FieldAt Ksz h kroots n) (hz : z ≠ 0) α lmb,
      topologyWorkload
          ((T n).verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤
        topologyBound n
  /-- Binding at every specialization (before H1.5b Part 1, the field `semantics.binds` of the
  strategy; honest strategies satisfy it by `ProductionStrategy.ofBare_bindsAll`). -/
  binds : ∀ n, (T n).BindsAll
  axis_bound :
    ∀ n (z : FieldAt Ksz h kroots n) (hz : z ≠ 0),
      TemplateAxisCounting.templateAxisWorkload
          (ProductionAxisStructureVerifier.committedTemplate
            (T n).verifier z hz) ≤
        axisWorkload n

/-- The verified production containment theorem supplies the exact P8 pointwise interface at every
chosen prime.  No independent challenge-coordinate assumption is used. -/
theorem production_pointwiseP8Bound
    (Ksz h : ℕ → ℕ) (kroots : ℕ)
    (T : ∀ n, ProductionStrategy
      (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))
    (lmb : ∀ n, FieldAt Ksz h kroots n)
    (q Λ topologyBound axisWorkload : ℕ → ℕ)
    (C : ∀ n, EdgeComparisonCensus.CombinedSkeletonCensus
      (FieldAt Ksz h kroots n) (T n).skeleton (Λ n))
    (H : FamilyPointwiseHypotheses
      Ksz h kroots T q Λ topologyBound axisWorkload C)
    (hlam : ∀ n ω (hz : nprSeed ω ≠ 0) i,
      (((T n).verifier.familyAt ω (lmb n) hz).exec.memoryPubAt i).lambda = ((T n).verifier.familyAt ω (lmb n) hz).cfg.challenges.lam) :
    PointwiseP8Bound
      (p9ExactSecurityFamily Ksz h kroots)
      (fun n => (productionWorkloadFamily
        Ksz h kroots T Λ topologyBound axisWorkload n : ℝ))
      (productionBadFamily Ksz h kroots T lmb q Λ) := by
  intro n
  letI charPPrime : CharP
      (FieldAt Ksz h kroots n) (p Ksz h kroots n) :=
    p9_FieldAt_charP Ksz h kroots n
  letI charPRing : CharP (FieldAt Ksz h kroots n)
      (ringChar (FieldAt Ksz h kroots n)) :=
    ringChar.charP _
  have htwo : (2 : FieldAt Ksz h kroots n) ≠ 0 := by
    intro hzero
    have hnat : (2 : ℕ) = 0 :=
      (p9_hchar Ksz h kroots n)
        (show (2 : ℕ) ∈ Set.Iic 11 by simp)
        (show (0 : ℕ) ∈ Set.Iic 11 by simp)
        (by simpa using hzero)
    omega
  have hcast :
      Set.InjOn
        (fun k : ℕ => (k : FieldAt Ksz h kroots n))
        (Set.Iio (q n)) := by
    intro a ha b hb hab
    exact (@CharP.natCast_injOn_Iio
      (FieldAt Ksz h kroots n) _ (p Ksz h kroots n) charPPrime _)
        (ha.trans_le (le_of_eq (H.q_eq_characteristic n)))
        (hb.trans_le (le_of_eq (H.q_eq_characteristic n)))
        hab
  have hKsz :
      ∀ z (hz : z ≠ 0) α lmb,
        (specializedProblem (T n).verifier.raw.timestamp z hz α lmb).cfg.Ksz <
          ringChar (FieldAt Ksz h kroots n) := by
    intro z hz α lmb
    have hring :
        ringChar (FieldAt Ksz h kroots n) = p Ksz h kroots n :=
      @ringChar.eq (FieldAt Ksz h kroots n) _ (p Ksz h kroots n) charPPrime
    have hKszRing :
        Ksz n < ringChar (FieldAt Ksz h kroots n) := by
      have hp := p9_Ksz_lt Ksz h kroots n
      omega
    exact (H.specialized_Ksz_le n z hz α lmb).trans_lt hKszRing
  have hqRing :
      q n = ringChar (FieldAt Ksz h kroots n) := by
    rw [H.q_eq_characteristic n]
    exact (@ringChar.eq (FieldAt Ksz h kroots n) _
      (p Ksz h kroots n) charPPrime).symm
  have key :=
    (production_jointProbability_falseAcceptance_le
      htwo (T n) (lmb n) (C n) (q n) (topologyBound n) (axisWorkload n)
      (p9_hchar Ksz h kroots n) (H.q_gt_one n) hqRing hcast
      (H.skeleton_bounded n) (H.combined_bounded n)
      (H.operational n) (H.size_window_nouns_bounded n)
      hKsz (H.program_capacity n) (H.memory_capacity n)
      (H.topology_bound n) (H.axis_bound n) (hlam n) (H.binds n))
  simp only [productionBadFamily, productionWorkloadFamily,
      ExactSecurityFamily.cardAt, p9ExactSecurityFamily,
      abs_jointProbability] at key ⊢
  convert key using 3
  exact Fintype.card_congr' rfl

/-- End-to-end family-level assembly: production false acceptance over the exact varying cubic
fields has its verified pointwise bound and is negligible. -/
theorem production_hasExactAsymptoticSoundness
    (Ksz h : ℕ → ℕ) (kroots : ℕ)
    (T : ∀ n, ProductionStrategy
      (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))
    (lmb : ∀ n, FieldAt Ksz h kroots n)
    (q Λ topologyBound axisWorkload : ℕ → ℕ)
    (C : ∀ n, EdgeComparisonCensus.CombinedSkeletonCensus
      (FieldAt Ksz h kroots n) (T n).skeleton (Λ n))
    (H : FamilyPointwiseHypotheses
      Ksz h kroots T q Λ topologyBound axisWorkload C)
    (hrows : PolynomialGrowth fun n =>
      (SemanticStrategy.computeSkeletonRows (T n).skeleton).length)
    (hcensus : PolynomialGrowth Λ)
    (htopology : PolynomialGrowth topologyBound)
    (haxis : PolynomialGrowth axisWorkload)
    (hformR : PolynomialGrowth fun n => formRUniformWorkload (T n))
    (hpair : PolynomialGrowth fun n => reqPairWorkload (T n) (Λ n))
    (hlam : ∀ n ω (hz : nprSeed ω ≠ 0) i,
      (((T n).verifier.familyAt ω (lmb n) hz).exec.memoryPubAt i).lambda = ((T n).verifier.familyAt ω (lmb n) hz).cfg.challenges.lam) :
    HasExactAsymptoticSoundness
      (p9ExactSecurityFamily Ksz h kroots)
      (fun n => (productionWorkloadFamily
        Ksz h kroots T Λ topologyBound axisWorkload n : ℝ))
      (productionBadFamily Ksz h kroots T lmb q Λ) := by
  apply hasExactAsymptoticSoundness_of_polynomialGrowth
    (p9ExactSecurityFamily Ksz h kroots)
    (productionWorkloadFamily Ksz h kroots T Λ topologyBound axisWorkload)
    (productionBadFamily Ksz h kroots T lmb q Λ)
    (productionWorkloadGrowth Ksz h kroots T Λ topologyBound axisWorkload
      hrows hcensus htopology haxis hformR hpair)
    (p9_card_superpolynomial Ksz h kroots)
  exact production_pointwiseP8Bound Ksz h kroots T lmb q Λ
    topologyBound axisWorkload C H hlam

/-- The exact production workload divided by the actual varying cubic cardinality tends to zero. -/
theorem production_workload_div_card_tendsto_zero
    (Ksz h : ℕ → ℕ) (kroots : ℕ)
    (T : ∀ n, ProductionStrategy
      (FieldAt Ksz h kroots n) (FieldAt Ksz h kroots n))
    (Λ topologyBound axisWorkload : ℕ → ℕ)
    (hrows : PolynomialGrowth fun n =>
      (SemanticStrategy.computeSkeletonRows (T n).skeleton).length)
    (hcensus : PolynomialGrowth Λ)
    (htopology : PolynomialGrowth topologyBound)
    (haxis : PolynomialGrowth axisWorkload)
    (hformR : PolynomialGrowth fun n => formRUniformWorkload (T n))
    (hpair : PolynomialGrowth fun n => reqPairWorkload (T n) (Λ n)) :
    Tendsto
      (fun n =>
        (productionWorkloadFamily
            Ksz h kroots T Λ topologyBound axisWorkload n : ℝ) /
          ((p9ExactSecurityFamily Ksz h kroots).cardAt n : ℝ))
      atTop (𝓝 0) := by
  let hwork :=
    productionWorkloadGrowth Ksz h kroots T Λ topologyBound axisWorkload
      hrows hcensus htopology haxis hformR hpair
  have hpointwise :
      PointwiseP8Bound
        (p9ExactSecurityFamily Ksz h kroots)
        (fun n => (productionWorkloadFamily
          Ksz h kroots T Λ topologyBound axisWorkload n : ℝ))
        (fun n =>
          (productionWorkloadFamily
              Ksz h kroots T Λ topologyBound axisWorkload n : ℝ) /
            ((p9ExactSecurityFamily Ksz h kroots).cardAt n : ℝ)) := by
    intro n
    rw [abs_of_nonneg]
    positivity
  have hs :=
    hasExactAsymptoticSoundness_of_polynomialGrowth
      (p9ExactSecurityFamily Ksz h kroots)
      (productionWorkloadFamily Ksz h kroots T Λ topologyBound axisWorkload)
      (fun n =>
        (productionWorkloadFamily
            Ksz h kroots T Λ topologyBound axisWorkload n : ℝ) /
          ((p9ExactSecurityFamily Ksz h kroots).cardAt n : ℝ))
      hwork (p9_card_superpolynomial Ksz h kroots) hpointwise
  exact Negligible.tendsto_zero hs.negligible

end

end Nock.NockVMROM.Thm54.ProductionAsymptotic

#print axioms Nock.NockVMROM.Thm54.ProductionAsymptotic.productionWorkloadGrowth
#print axioms Nock.NockVMROM.Thm54.ProductionAsymptotic.hasExactAsymptoticSoundness_of_polynomialGrowth
#print axioms Nock.NockVMROM.Thm54.ProductionAsymptotic.production_pointwiseP8Bound
#print axioms Nock.NockVMROM.Thm54.ProductionAsymptotic.production_hasExactAsymptoticSoundness
#print axioms Nock.NockVMROM.Thm54.ProductionAsymptotic.production_workload_div_card_tendsto_zero
