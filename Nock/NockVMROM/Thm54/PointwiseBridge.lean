import Nock.NockVMROM.Thm54.JointCoins
import Nock.NockVMROM.Thm54.ExactAsymptotic
import Nock.NockVMROM.Thm54.AxisSoundness

/-!
# Finite-cardinality to pointwise P8 probability bridge

This module normalizes an event in the exact four-coordinate joint challenge space and turns the
cardinality estimate `|E| ≤ workload * |K|³` into the pointwise estimate
`Pr[E] ≤ workload / |K|`.  No independence hypothesis is used.
-/

open scoped Classical

namespace Nock.NockVMROM.Thm54

noncomputable section

/-! ## Exact finite probability and denominator facts -/

/-- Uniform probability of a finite event in the exact joint challenge space. -/
def jointProbability {K : Type*} [Fintype K]
    (E : Finset (JointCoins K)) : ℝ :=
  (E.card : ℝ) / (Fintype.card (JointCoins K) : ℝ)

/-- A nonempty finite carrier has nonzero cardinality. -/
theorem carrier_card_ne_zero {K : Type*} [Fintype K] [Nonempty K] :
    Fintype.card K ≠ 0 :=
  Fintype.card_ne_zero

/-- The exact four-coordinate joint challenge space has positive cardinality. -/
theorem jointCoins_card_pos {K : Type*} [Fintype K] [Nonempty K] :
    0 < Fintype.card (JointCoins K) := by
  rw [card_jointCoins]
  exact pow_pos (Fintype.card_pos_iff.mpr ‹Nonempty K›) _

/-- The exact four-coordinate joint challenge space has nonzero cardinality. -/
theorem jointCoins_card_ne_zero {K : Type*} [Fintype K] [Nonempty K] :
    Fintype.card (JointCoins K) ≠ 0 :=
  Nat.ne_of_gt jointCoins_card_pos

/-- A normalized finite-event probability is nonnegative. -/
theorem jointProbability_nonneg {K : Type*} [Fintype K] [Nonempty K]
    (E : Finset (JointCoins K)) :
    0 ≤ jointProbability E := by
  exact div_nonneg (by positivity)
    (by exact_mod_cast (Nat.zero_le (Fintype.card (JointCoins K))))

/-- Absolute value does not alter a normalized finite-event probability. -/
@[simp]
theorem abs_jointProbability {K : Type*} [Fintype K] [Nonempty K]
    (E : Finset (JointCoins K)) :
    |jointProbability E| = jointProbability E :=
  abs_of_nonneg (jointProbability_nonneg E)

/-! ## The generic `|K|⁴` to `1 / |K|` bridge -/

/-- A cardinality bound in the exact `JointCoins K = K⁴` space gives the desired pointwise
probability estimate.  The proof is purely finite counting and uses no independence assumption. -/
theorem jointProbability_le_workload_div_card
    {K : Type*} [Fintype K] [Nonempty K]
    (E : Finset (JointCoins K)) (workload : ℕ)
    (hcard : E.card ≤ workload * Fintype.card K ^ 3) :
    |jointProbability E| ≤ (workload : ℝ) / (Fintype.card K : ℝ) := by
  rw [abs_jointProbability, jointProbability, card_jointCoins]
  have hK : 0 < (Fintype.card K : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty K›)
  have hcardReal :
      (E.card : ℝ) ≤ (workload : ℝ) * (Fintype.card K : ℝ) ^ 3 := by
    exact_mod_cast hcard
  push_cast
  rw [div_le_div_iff₀ (pow_pos hK 4) hK]
  nlinarith [mul_le_mul_of_nonneg_right hcardReal hK.le]

/-! ## Exact-security-family bridge -/

/-- Pointwise cardinal bounds over an exact family supply P8's named real-valued pointwise
interface.  The family's stored field and finite instances are installed at each parameter. -/
theorem pointwiseP8Bound_of_joint_card_le
    (Fam : ExactSecurityFamily)
    (E : ∀ n, Finset (JointCoins (Fam.FieldAt n)))
    (workload : ℕ → ℕ)
    (hcard :
      ∀ n, (E n).card ≤ workload n * Fam.cardAt n ^ 3) :
    PointwiseP8Bound Fam
      (fun n => (workload n : ℝ))
      (fun n =>
        @jointProbability (Fam.FieldAt n) (Fam.fintypeAt n) (E n)) := by
  intro n
  letI : Field (Fam.FieldAt n) := Fam.fieldAt n
  letI : Fintype (Fam.FieldAt n) := Fam.fintypeAt n
  apply jointProbability_le_workload_div_card
  simpa [ExactSecurityFamily.cardAt] using hcard n

namespace ExactPrimeFamily

/-- The finite-cardinality bridge specialized to P9's exact varying cubic-extension family, producing its
named `P8PointwiseBridge` interface. -/
theorem P8PointwiseBridge_of_joint_card_le
    (Ksz h : ℕ → ℕ) (kroots : ℕ)
    (E : ∀ n, Finset (JointCoins (FieldAt Ksz h kroots n)))
    (workload : ℕ → ℕ)
    (hcard :
      ∀ n, (E n).card ≤
        workload n * Fintype.card (FieldAt Ksz h kroots n) ^ 3) :
    P8PointwiseBridge Ksz h kroots
      (fun n => (workload n : ℝ))
      (fun n => jointProbability (E n)) := by
  apply pointwiseP8Bound_of_joint_card_le
  intro n
  have h := hcard n
  simp only [ExactSecurityFamily.cardAt, p9ExactSecurityFamily]
  convert h using 4
  exact Fintype.card_congr (Equiv.refl _)

/-- A polynomial natural workload and its exact joint-event cardinality bound directly supply P9's
full exact asymptotic-soundness class.  The actual bad family remains the normalized probability
of the supplied joint events. -/
theorem p9_hasExactAsymptoticSoundness_of_joint_card_le
    (Ksz h : ℕ → ℕ) (kroots : ℕ)
    (E : ∀ n, Finset (JointCoins (FieldAt Ksz h kroots n)))
    (workload : ℕ → ℕ) (dw : ℕ)
    (hcard :
      ∀ n, (E n).card ≤
        workload n * Fintype.card (FieldAt Ksz h kroots n) ^ 3)
    (hwork_poly :
      ∀ n, |(workload n : ℝ)| ≤ ((n : ℝ) + 1) ^ dw) :
    HasExactAsymptoticSoundness
      (p9ExactSecurityFamily Ksz h kroots)
      (fun n => (workload n : ℝ))
      (fun n => jointProbability (E n)) := by
  apply p9_hasExactAsymptoticSoundness Ksz h kroots
  · intro n
    positivity
  · exact hwork_poly
  · exact P8PointwiseBridge_of_joint_card_le Ksz h kroots E workload hcard

end ExactPrimeFamily

/-! ## Direct adapter for the axis-corrected failure union -/

/-- The generic axis-corrected union cardinality theorem immediately yields its normalized
pointwise probability estimate.  This adapter depends only on `AxisSoundness`, not on any
`JointSoundness` module. -/
theorem failureUnionWithAxis_jointProbability_le
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K]
    {p : ℕ} [CharP K p]
    (h2 : (2 : K) ≠ 0)
    (base : Finset (JointCoins K)) (baseWorkload : ℕ)
    (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (hbase : base.card ≤ baseWorkload * Fintype.card K ^ 3)
    (R : ExactAxisRefinement cfg exec) :
    |jointProbability (FailureUnionWithAxis base cfg exec)| ≤
      (jointWorkloadWithAxis baseWorkload cfg exec : ℝ) /
        (Fintype.card K : ℝ) :=
  jointProbability_le_workload_div_card _ _
    (failureUnionWithAxis_card_le h2 base baseWorkload cfg exec hbase R)

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.carrier_card_ne_zero
#print axioms Nock.NockVMROM.Thm54.jointCoins_card_pos
#print axioms Nock.NockVMROM.Thm54.jointCoins_card_ne_zero
#print axioms Nock.NockVMROM.Thm54.jointProbability_nonneg
#print axioms Nock.NockVMROM.Thm54.abs_jointProbability
#print axioms Nock.NockVMROM.Thm54.jointProbability_le_workload_div_card
#print axioms Nock.NockVMROM.Thm54.pointwiseP8Bound_of_joint_card_le
#print axioms Nock.NockVMROM.Thm54.ExactPrimeFamily.P8PointwiseBridge_of_joint_card_le
#print axioms Nock.NockVMROM.Thm54.ExactPrimeFamily.p9_hasExactAsymptoticSoundness_of_joint_card_le
#print axioms Nock.NockVMROM.Thm54.failureUnionWithAxis_jointProbability_le
