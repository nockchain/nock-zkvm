import Nock.NockVMROM.Thm54.PlusIOSegmentedRAP
import Nock.NockVMROM.Thm54.ExactAsymptotic
import Nock.NockVM

/-!
# Varying cubic-denominator repair packet

The paper's Theorem 5.4 uses the Goldilocks cubic extension `𝕂 = 𝔽_{p³}`, with
`|𝕂| = p³ ≈ 2¹⁹²`. The production exact-security family now instantiates
each pointwise field as `GaloisField (p n) 3`, so its actual `Fintype.card` denominator is
`(p n)³`. This module records that varying-family denominator repair. It does not instantiate the
paper's one fixed Goldilocks prime.

Two distinct notions must not be conflated:

1. `RAP.e` remains reifier metadata: changing it does not expand the RAP trace width, and
   `ExactConfig.eDeg = 1`.
2. The soundness denominator is independently determined by the actual finite field stored in
   `ExactSecurityFamily`. That field is now cubic, regardless of RAP-width/coordinate expansion.

The arithmetic receipts below establish the denominator and scale facts used by the paper's
121-bit discussion. They do not claim a complete exact concrete false-acceptance formula: such a
claim additionally needs the concrete workload/event bridge, not merely field cardinality and
scale arithmetic.
-/

namespace Nock.RedTeam.Batch16

open Nock Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExactPrimeFamily
open Nock.NockVMROM.Thm54.PlusIOSegmentedFamily
open Nock.Framework Nock.Framework.Reify

/-! ## RAP coordinates remain separate from the soundness denominator -/

/-- **The declared extension order does not affect the RAP width.** For any AIR, reifying at
extension order `e₁` and at `e₂` produces the same column count, equal to the AIR's own
`numTraceCols`. This coordinate-width fact is separate from the soundness denominator, which is
the cardinality of the field stored in the exact security family. -/
theorem b16_rap_width_independent_of_extension_order
    {K : Type} [Field K]
    (air : Nock.Reified.AIR) (chalVal pubVal : ℕ → K)
    (e₁ e₂ h : ℕ) (ω β : K) (H : Finset K) (hβ : β ≠ 0) (hh : 1 ≤ h) :
    (airToRAP air chalVal pubVal e₁ h ω β H hβ hh).w =
        (airToRAP air chalVal pubVal e₂ h ω β H hβ hh).w ∧
      (airToRAP air chalVal pubVal e₁ h ω β H hβ hh).w = air.numTraceCols :=
  airToRAP_width_is_e_independent air chalVal pubVal e₁ e₂ h ω β H hβ hh

/-- **The exact configuration records extension-degree one.** This says that RAP coordinates are
not expanded by the reifier. It does not force the independently supplied exact-family field to
have prime cardinality; production now supplies a cubic `GaloisField`. -/
theorem b16_exactConfig_eDeg_is_one
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (cfg : ExactConfig F K) :
    cfg.eDeg = 1 :=
  cfg.eDeg_eq_one

/-! ## Regression receipt — the explicitly local old base-field family -/

section Family

variable (Ksz h : ℕ → ℕ) (kroots : ℕ)

/-- The field used by the pre-closure implementation, retained locally for regression only. This
is not the current production `ExactPrimeFamily.FieldAt`. -/
abbrev OldBaseFieldAt (n : ℕ) : Type :=
  ZMod (p Ksz h kroots n)

/-- An explicit exact-security family reproducing the old prime-field denominator. Its name and
scope prevent this regression fixture from being mistaken for current production. -/
noncomputable def oldBaseExactSecurityFamily : ExactSecurityFamily where
  FieldAt := OldBaseFieldAt Ksz h kroots
  fieldAt := fun _ => inferInstance
  fintypeAt := fun _ => inferInstance

/-- The old local regression family has base-field cardinality `p n`. -/
@[simp]
theorem b16_old_base_family_card (n : ℕ) :
    (oldBaseExactSecurityFamily Ksz h kroots).cardAt n = p Ksz h kroots n := by
  change Fintype.card (ZMod (p Ksz h kroots n)) = p Ksz h kroots n
  exact ZMod.card _

/-- The old local regression denominator is prime. This theorem says nothing about the current
production family, whose denominator is cubic. -/
theorem b16_old_base_denominator_is_prime (n : ℕ) :
    Nat.Prime ((oldBaseExactSecurityFamily Ksz h kroots).cardAt n) := by
  rw [b16_old_base_family_card]
  exact (p9_p_spec Ksz h kroots n).1

/-- A prime is never the cube of an integer exceeding one. -/
theorem b16_prime_not_cube {pp : ℕ} (hpp : Nat.Prime pp) :
    ¬ ∃ q : ℕ, 1 < q ∧ q ^ 3 = pp := by
  rintro ⟨q, hq1, hq3⟩
  have hdvd : q ∣ pp := ⟨q ^ 2, by rw [← hq3]; ring⟩
  rcases (hpp.eq_one_or_self_of_dvd q hdvd) with h | h
  · omega
  · rw [h] at hq3
    have hinj : Function.Injective (fun k => pp ^ k) :=
      Nat.pow_right_injective hpp.two_le
    have h31 : (3 : ℕ) = 1 := hinj (by simpa [pow_one] using hq3)
    omega

/-- The old local regression field is not cubic. -/
theorem b16_old_base_field_not_cubic_extension (n : ℕ) :
    ¬ ∃ q : ℕ, 1 < q ∧
      q ^ 3 = (oldBaseExactSecurityFamily Ksz h kroots).cardAt n :=
  b16_prime_not_cube (b16_old_base_denominator_is_prime Ksz h kroots n)

/-- A pointwise bound over the old local regression family divides by its prime cardinality. -/
theorem b16_old_base_pointwise_bound_divides_by_prime
    (workload bad : ℕ → ℝ)
    (H : PointwiseP8Bound
      (oldBaseExactSecurityFamily Ksz h kroots) workload bad) (n : ℕ) :
    |bad n| ≤ workload n / ((p Ksz h kroots n : ℝ)) := by
  have := H n
  rwa [b16_old_base_family_card] at this

/-! ## Current production — cubic field and denominator closure -/

/-- **Current production cardinality.** The actual pointwise soundness denominator is the
cardinality of `GaloisField (p n) 3`, namely `(p n)³`. -/
theorem b16_production_cardAt_eq_prime_cube (n : ℕ) :
    (p9ExactSecurityFamily Ksz h kroots).cardAt n =
      p Ksz h kroots n ^ 3 :=
  p9_exactSecurityFamily_card Ksz h kroots n

/-- The current production denominator is a cube of the selected prime, and that prime is greater
than one. -/
theorem b16_production_denominator_is_prime_cube (n : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ 1 < q ∧
      (p9ExactSecurityFamily Ksz h kroots).cardAt n = q ^ 3 := by
  refine ⟨p Ksz h kroots n, (p9_p_spec Ksz h kroots n).1,
    (p9_p_spec Ksz h kroots n).1.one_lt, ?_⟩
  exact b16_production_cardAt_eq_prime_cube Ksz h kroots n

/-- **The production pointwise bound divides by the cubic cardinality.** This is exactly the
denominator substitution supplied by `PointwiseP8Bound`; it does not by itself prove a concrete
121-bit false-acceptance formula. -/
theorem b16_production_pointwise_bound_divides_by_cubic_cardinality
    (workload bad : ℕ → ℝ)
    (H : PointwiseP8Bound (p9ExactSecurityFamily Ksz h kroots) workload bad) (n : ℕ) :
    |bad n| ≤ workload n / ((p Ksz h kroots n ^ 3 : ℕ) : ℝ) := by
  have hbound := H n
  rwa [b16_production_cardAt_eq_prime_cube] at hbound

end Family

/-! ## Goldilocks-scale arithmetic -/

/-- The paper-scale soundness numerator `k²·Λ` at the paper's own parameters (`k = 2³¹`,
`Λ = 2⁹`), equal to `2⁷¹`. -/
def numeratorScale : ℕ := Nock.NockVM.kbound ^ 2 * Nock.NockVM.Λ

/-- A base-field capacity of Goldilocks scale, `≈ 2⁶⁴`. -/
def baseFieldCap : ℕ := 2 ^ 64

/-- The cubic-extension capacity the paper actually uses, `(2⁶⁴)³ = 2¹⁹²`. -/
def cubicFieldCap : ℕ := baseFieldCap ^ Nock.NockVM.extOrder

/-- The concrete Goldilocks prime `2⁶⁴ − 2³² + 1`. -/
def goldilocksPrime : ℕ := 2 ^ 64 - 2 ^ 32 + 1

/-- The numerator scale is exactly `2⁷¹`. -/
theorem b16_numeratorScale_eq : numeratorScale = 2 ^ 71 := by
  unfold numeratorScale Nock.NockVM.kbound Nock.NockVM.Λ
  norm_num

/-- The actual Goldilocks prime sits below the base-field capacity `2⁶⁴`. -/
theorem b16_goldilocks_below_base_cap : goldilocksPrime < baseFieldCap := by
  unfold goldilocksPrime baseFieldCap
  norm_num

/-- **Base-field divisor is too small.** At a base-field capacity the paper-scale numerator `2⁷¹`
exceeds the divisor `2⁶⁴`, so the illustrated ratio is `> 1`. -/
theorem b16_base_divisor_too_small : baseFieldCap < numeratorScale := by
  rw [b16_numeratorScale_eq]
  unfold baseFieldCap
  norm_num

/-- **Cubic divisor is large enough.** The same numerator `2⁷¹` is far below the cubic capacity
`2¹⁹²`, so the illustrated ratio is `< 1`. -/
theorem b16_cubic_divisor_large_enough : numeratorScale < cubicFieldCap := by
  rw [b16_numeratorScale_eq]
  unfold cubicFieldCap baseFieldCap Nock.NockVM.extOrder
  norm_num

/-- **The base-field bound is vacuous** (exceeds `1`), as reals. -/
theorem b16_base_bound_vacuous :
    (1 : ℝ) < (numeratorScale : ℝ) / (baseFieldCap : ℝ) := by
  have hb : (0 : ℝ) < (baseFieldCap : ℝ) := by unfold baseFieldCap; norm_num
  rw [one_lt_div hb]
  exact_mod_cast b16_base_divisor_too_small

/-- **The cubic-extension bound is meaningful** (below `1`), as reals. -/
theorem b16_cubic_bound_meaningful :
    (numeratorScale : ℝ) / (cubicFieldCap : ℝ) < 1 := by
  have hc : (0 : ℝ) < (cubicFieldCap : ℝ) := by
    unfold cubicFieldCap baseFieldCap Nock.NockVM.extOrder; norm_num
  rw [div_lt_one hc]
  exact_mod_cast b16_cubic_divisor_large_enough

/-- **Varying cubic-denominator capstone.** Current production has cubic cardinality at each varying
prime, the paper-scale cubic ratio is arithmetically meaningful, and the configured security
parameter is `121`. This neither instantiates the fixed Goldilocks prime nor proves a complete exact
concrete 121-bit probability theorem: it packages denominator shape and scale arithmetic only. -/
theorem b16_varying_cubic_denominator_closed
    (Ksz h : ℕ → ℕ) (kroots : ℕ) (n : ℕ) :
    (p9ExactSecurityFamily Ksz h kroots).cardAt n =
        p Ksz h kroots n ^ 3 ∧
      (numeratorScale : ℝ) / (cubicFieldCap : ℝ) < 1 ∧
      Nock.NockVM.security_bits = 121 :=
  ⟨b16_production_cardAt_eq_prime_cube Ksz h kroots n,
    b16_cubic_bound_meaningful, rfl⟩

/-! ## Exact asymptotic soundness over the varying cubic family

The theorem retains that bridge as an explicit hypothesis.
-/

/-- **Exact asymptotic soundness over current production fields.** -/
theorem b16_exact_asymptotic_security_claim
    (Ksz h : ℕ → ℕ) (kroots : ℕ)
    (workload bad : ℕ → ℝ) (dw : ℕ)
    (hwork_nonneg : ∀ n, 0 ≤ workload n)
    (hwork_poly : ∀ n, |workload n| ≤ ((n : ℝ) + 1) ^ dw)
    (hP8 : ExactPrimeFamily.P8PointwiseBridge Ksz h kroots workload bad) :
    HasExactAsymptoticSoundness
      (ExactPrimeFamily.p9ExactSecurityFamily Ksz h kroots) workload bad :=
  ExactPrimeFamily.p9_hasExactAsymptoticSoundness Ksz h kroots
    workload bad dw hwork_nonneg hwork_poly hP8

end Nock.RedTeam.Batch16

#print axioms Nock.RedTeam.Batch16.b16_rap_width_independent_of_extension_order
#print axioms Nock.RedTeam.Batch16.b16_exactConfig_eDeg_is_one
#print axioms Nock.RedTeam.Batch16.b16_old_base_family_card
#print axioms Nock.RedTeam.Batch16.b16_old_base_denominator_is_prime
#print axioms Nock.RedTeam.Batch16.b16_old_base_field_not_cubic_extension
#print axioms Nock.RedTeam.Batch16.b16_old_base_pointwise_bound_divides_by_prime
#print axioms Nock.RedTeam.Batch16.b16_production_cardAt_eq_prime_cube
#print axioms Nock.RedTeam.Batch16.b16_production_denominator_is_prime_cube
#print axioms Nock.RedTeam.Batch16.b16_production_pointwise_bound_divides_by_cubic_cardinality
#print axioms Nock.RedTeam.Batch16.b16_varying_cubic_denominator_closed
#print axioms Nock.RedTeam.Batch16.b16_exact_asymptotic_security_claim
