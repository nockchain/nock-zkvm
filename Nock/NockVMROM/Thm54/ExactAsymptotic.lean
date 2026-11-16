import Nock.NockVMROM.Asymptotic
import Nock.NockVMROM.Thm54.NodeEncoding
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Exact Theorem 5.4 asymptotics over varying cubic extension fields

It leaves `SecurityFamily` and `HasAsymptoticSoundness` unchanged.

`max (Ksz n + 2)
  (max (3 * 2 ^ h n + 2) (kroots + 2 * 2 ^ h n + 12))`.

That compatibility bound does not by itself imply asymptotic growth when `h` and `Ksz` are
constant.  The actual selection bound therefore takes its maximum with `13^(n+1)`.  This preserves
all AIR/IO/domain inequalities and gives an unconditional super-polynomial cardinality theorem.
-/

namespace Nock.NockVMROM.Thm54

open Filter
open Nock.Framework
open Nock.Framework.Thm54

noncomputable section

/-! ## Additive exact security-family interface -/

/-- A security family whose pointwise carriers really are finite fields. -/
structure ExactSecurityFamily where
  /-- Field at security parameter `n`. -/
  FieldAt : ℕ → Type*
  /-- Pointwise field structure. -/
  fieldAt : ∀ n, Field (FieldAt n)
  /-- Pointwise finite structure. -/
  fintypeAt : ∀ n, Fintype (FieldAt n)

namespace ExactSecurityFamily

/-- The actual cardinality of the field stored at parameter `n`. -/
def cardAt (Fam : ExactSecurityFamily) (n : ℕ) : ℕ :=
  @Fintype.card (Fam.FieldAt n) (Fam.fintypeAt n)

/-- Every stored field has positive cardinality. -/
theorem cardAt_pos (Fam : ExactSecurityFamily) (n : ℕ) :
    0 < Fam.cardAt n := by
  letI : Field (Fam.FieldAt n) := Fam.fieldAt n
  letI : Fintype (Fam.FieldAt n) := Fam.fintypeAt n
  simpa [cardAt] using
    (Fintype.card_pos_iff.mpr ⟨(0 : Fam.FieldAt n)⟩)

end ExactSecurityFamily

def PointwiseP8Bound (Fam : ExactSecurityFamily)
    (workload bad : ℕ → ℝ) : Prop :=
  ∀ n, |bad n| ≤ workload n / (Fam.cardAt n : ℝ)

/-- Additive exact asymptotic soundness. -/
class HasExactAsymptoticSoundness (Fam : ExactSecurityFamily)
    (workload bad : ℕ → ℝ) : Prop where
  pointwise_bound : PointwiseP8Bound Fam workload bad
  /-- The resulting bad-event family is negligible. -/
  negligible : Negligible bad

/-- Downward closure from a polynomial-over-cardinality estimate to negligibility. -/
theorem negligible_of_pointwiseP8Bound
    (Fam : ExactSecurityFamily) (workload bad : ℕ → ℝ) (dw : ℕ)
    (hwork_nonneg : ∀ n, 0 ≤ workload n)
    (hwork_poly : ∀ n, |workload n| ≤ ((n : ℝ) + 1) ^ dw)
    (hcard_growth :
      ∀ e : ℕ, ∀ᶠ n : ℕ in atTop,
        ((n : ℝ) + 1) ^ e ≤ (Fam.cardAt n : ℝ))
    (hP8 : PointwiseP8Bound Fam workload bad) :
    Negligible bad := by
  have hratio :
      Negligible (fun n => workload n / (Fam.cardAt n : ℝ)) :=
    Nock.NockVMROM.negligible_workload_div_field
      workload (fun n => (Fam.cardAt n : ℝ)) dw hwork_poly
      (fun n => by exact_mod_cast Fam.cardAt_pos n) hcard_growth
  intro c
  filter_upwards [hratio c] with n hn
  have hratio_nonneg :
      0 ≤ workload n / (Fam.cardAt n : ℝ) := by
    exact div_nonneg (hwork_nonneg n)
      (by exact_mod_cast (Nat.zero_le (Fam.cardAt n)))
  exact (hP8 n).trans (by simpa [abs_of_nonneg hratio_nonneg] using hn)

/-! ## The varying cubic-extension family -/

namespace ExactPrimeFamily

variable (Ksz h : ℕ → ℕ) (kroots : ℕ)

def compatibilityBound (n : ℕ) : ℕ :=
  max (Ksz n + 2)
    (max (3 * 2 ^ h n + 2) (kroots + 2 * 2 ^ h n + 12))

/-- The prime-selection bound.  Its left branch is the canonical compatibility bound; its right
branch supplies unconditional super-polynomial growth even when `h` and `Ksz` are constant. -/
def selectionBound (n : ℕ) : ℕ :=
  max (compatibilityBound Ksz h kroots n) (13 ^ (n + 1))

/-- The special congruent-prime theorem needed here.  This is
`Nat.exists_prime_gt_modEq_one` from `Mathlib.NumberTheory.PrimesCongruentOne`, not a Dirichlet
claim. -/
theorem p9_exists_good_prime (n : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ selectionBound Ksz h kroots n < p ∧
      p ≡ 1 [MOD 2 ^ h n] :=
  Nat.exists_prime_gt_modEq_one (selectionBound Ksz h kroots n) (by positivity)

/-- The chosen prime at security parameter `n`. -/
def p (n : ℕ) : ℕ :=
  Nat.find
    (p := fun q =>
      Nat.Prime q ∧ selectionBound Ksz h kroots n < q ∧
        q ≡ 1 [MOD 2 ^ h n])
    (p9_exists_good_prime Ksz h kroots n)

/-- All three defining facts about the `Nat.find` choice. -/
theorem p9_p_spec (n : ℕ) :
    Nat.Prime (p Ksz h kroots n) ∧
      selectionBound Ksz h kroots n < p Ksz h kroots n ∧
      p Ksz h kroots n ≡ 1 [MOD 2 ^ h n] :=
  Nat.find_spec (p9_exists_good_prime Ksz h kroots n)

/-- The chosen modulus is prime, exposed as the instance required by `ZMod`. -/
instance p9_fact_prime (n : ℕ) : Fact (Nat.Prime (p Ksz h kroots n)) :=
  ⟨(p9_p_spec Ksz h kroots n).1⟩

/-- The exact pointwise field, a cubic extension of the chosen prime field. -/
abbrev FieldAt (n : ℕ) : Type :=
  GaloisField (p Ksz h kroots n) 3

noncomputable instance p9_fieldAt_field (n : ℕ) :
    Field (FieldAt Ksz h kroots n) :=
  inferInstance

noncomputable instance p9_fieldAt_fintype (n : ℕ) :
    Fintype (FieldAt Ksz h kroots n) :=
  Fintype.ofFinite _

noncomputable instance p9_fieldAt_decidableEq (n : ℕ) :
    DecidableEq (FieldAt Ksz h kroots n) :=
  Classical.decEq _

/-- Exact pointwise cardinality of the varying cubic extension field. -/
@[simp]
theorem p9_FieldAt_card (n : ℕ) :
    Fintype.card (FieldAt Ksz h kroots n) = p Ksz h kroots n ^ 3 := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card _ 3 (by norm_num)

/-- The field has exactly the chosen prime as its characteristic. -/
theorem p9_FieldAt_charP (n : ℕ) :
    CharP (FieldAt Ksz h kroots n) (p Ksz h kroots n) :=
  inferInstance

/-- The canonical compatibility bound is below the chosen prime. -/
theorem p9_compatibilityBound_lt (n : ℕ) :
    compatibilityBound Ksz h kroots n < p Ksz h kroots n :=
  (le_max_left _ _).trans_lt (p9_p_spec Ksz h kroots n).2.1

/-- The chosen characteristic is strictly greater than eleven. -/
theorem p9_char_gt_11 (n : ℕ) :
    11 < p Ksz h kroots n := by
  have hcompat := p9_compatibilityBound_lt Ksz h kroots n
  have hmem :
      kroots + 2 * 2 ^ h n + 12 ≤ compatibilityBound Ksz h kroots n :=
    (le_max_right _ _).trans (le_max_right _ _)
  omega

/-- The exact `hchar ≤ 11` state-tag condition consumed by the compute AIR and concrete node
encoders. -/
theorem p9_hchar (n : ℕ) :
    NodeEncoding.StateTagChar (FieldAt Ksz h kroots n) :=
  NodeEncoding.stateTagChar_of_charP
    (p Ksz h kroots n) (p9_char_gt_11 Ksz h kroots n)

/-- The IO/K-size condition `Ksz n < char(FieldAt n)`. -/
theorem p9_Ksz_lt (n : ℕ) :
    Ksz n < p Ksz h kroots n := by
  have hcompat := p9_compatibilityBound_lt Ksz h kroots n
  have hK :
      Ksz n + 2 ≤ compatibilityBound Ksz h kroots n :=
    le_max_left _ _
  omega

/-- Any natural workload pointwise bounded by `Ksz` is also below the varying
characteristic. -/
theorem p9_workload_lt_of_le_Ksz (workload : ℕ → ℕ) (n : ℕ)
    (hwork : workload n ≤ Ksz n) :
    workload n < p Ksz h kroots n :=
  hwork.trans_lt (p9_Ksz_lt Ksz h kroots n)

/-- The compute-walk no-wrap condition at the full `2^h` node capacity. -/
theorem p9_wrapc (n : ℕ) :
    1 + 2 ^ h n * 3 < p Ksz h kroots n := by
  have hcompat := p9_compatibilityBound_lt Ksz h kroots n
  have hcomp :
      3 * 2 ^ h n + 2 ≤ compatibilityBound Ksz h kroots n :=
    (le_max_left _ _).trans (le_max_right _ _)
  omega

/-- The memory-forest no-wrap condition at the full `2^h` node capacity. -/
theorem p9_wrapm (n : ℕ) :
    kroots + 2 ^ h n * 2 < p Ksz h kroots n := by
  have hcompat := p9_compatibilityBound_lt Ksz h kroots n
  have hmem :
      kroots + 2 * 2 ^ h n + 12 ≤ compatibilityBound Ksz h kroots n :=
    (le_max_right _ _).trans (le_max_right _ _)
  omega

/-- The congruence certificate in the divisibility form needed for a subgroup of order `2^h`. -/
theorem p9_two_pow_dvd (n : ℕ) :
    2 ^ h n ∣ p Ksz h kroots n - 1 := by
  have hmod := (p9_p_spec Ksz h kroots n).2.2
  have hp : 0 < p Ksz h kroots n :=
    (p9_p_spec Ksz h kroots n).1.pos
  exact (Nat.modEq_iff_dvd' hp).mp hmod.symm

/-- A field element of exact order `2^(h n)`, obtained by taking the appropriate power of a
generator of the cyclic unit group. -/
theorem p9_exists_orbit_generator (n : ℕ) :
    ∃ ω : FieldAt Ksz h kroots n, orderOf ω = 2 ^ h n := by
  classical
  obtain ⟨g, hg⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard
      (α := (ZMod (p Ksz h kroots n))ˣ)
  have hcard :
      Nat.card (ZMod (p Ksz h kroots n))ˣ =
        p Ksz h kroots n - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime (p9_p_spec Ksz h kroots n).1]
  rw [hcard] at hg
  have hne : orderOf g ≠ 0 := by
    rw [hg]
    have hp_one : 1 < p Ksz h kroots n :=
      (p9_p_spec Ksz h kroots n).1.one_lt
    omega
  have hdvd : 2 ^ h n ∣ orderOf g := by
    rw [hg]
    exact p9_two_pow_dvd Ksz h kroots n
  let ζ : ZMod (p Ksz h kroots n) :=
    ((g ^ (orderOf g / 2 ^ h n) :
      (ZMod (p Ksz h kroots n))ˣ) :
      ZMod (p Ksz h kroots n))
  have hζ : orderOf ζ = 2 ^ h n := by
    change
      orderOf
        (((g ^ (orderOf g / 2 ^ h n) :
          (ZMod (p Ksz h kroots n))ˣ) :
          ZMod (p Ksz h kroots n))) =
        2 ^ h n
    rw [orderOf_units]
    exact orderOf_pow_orderOf_div hne hdvd
  refine
    ⟨algebraMap (ZMod (p Ksz h kroots n))
      (FieldAt Ksz h kroots n) ζ, ?_⟩
  exact
    (orderOf_injective
      (algebraMap (ZMod (p Ksz h kroots n))
        (FieldAt Ksz h kroots n)).toMonoidHom
      (algebraMap (ZMod (p Ksz h kroots n))
        (FieldAt Ksz h kroots n)).injective ζ).trans hζ

/-- A fixed chosen order-`2^h` generator. -/
def p9_orbitGenerator (n : ℕ) : FieldAt Ksz h kroots n :=
  Classical.choose (p9_exists_orbit_generator Ksz h kroots n)

@[simp]
theorem p9_orbitGenerator_order (n : ℕ) :
    orderOf (p9_orbitGenerator Ksz h kroots n) = 2 ^ h n :=
  Classical.choose_spec (p9_exists_orbit_generator Ksz h kroots n)

/-- The production `OrbitDomain` over the varying cubic extension field. -/
def p9_orbitDomain (n : ℕ) : OrbitDomain (FieldAt Ksz h kroots n) where
  h := h n
  ω := p9_orbitGenerator Ksz h kroots n
  βcoset := 1
  βcoset_ne_zero := one_ne_zero
  order_ω := p9_orbitGenerator_order Ksz h kroots n

theorem p9_fieldFamily_hasOrbit (n : ℕ) :
    ∃ D : OrbitDomain (FieldAt Ksz h kroots n), D.h = h n :=
  ⟨p9_orbitDomain Ksz h kroots n, rfl⟩

/-- Any requested compute and memory prefixes fitting `2^(h n)` fit the constructed domain. -/
theorem p9_required_node_capacity (n : ℕ) {compRows memRows : ℕ}
    (hcomp : compRows ≤ 2 ^ h n) (hmem : memRows ≤ 2 ^ h n) :
    compRows ≤ 2 ^ (p9_orbitDomain Ksz h kroots n).h ∧
      memRows ≤ 2 ^ (p9_orbitDomain Ksz h kroots n).h := by
  simpa [p9_orbitDomain] using And.intro hcomp hmem

/-- The additive exact family built from varying cubic extensions of the selected prime fields. -/
def p9ExactSecurityFamily : ExactSecurityFamily where
  FieldAt := FieldAt Ksz h kroots
  fieldAt := p9_fieldAt_field Ksz h kroots
  fintypeAt := p9_fieldAt_fintype Ksz h kroots

/-- The exact-family denominator is definitionally backed by the chosen cubic extension's actual
`Fintype.card`. -/
@[simp]
theorem p9_exactSecurityFamily_card (n : ℕ) :
    (p9ExactSecurityFamily Ksz h kroots).cardAt n =
      p Ksz h kroots n ^ 3 := by
  change Fintype.card (FieldAt Ksz h kroots n) = p Ksz h kroots n ^ 3
  exact p9_FieldAt_card Ksz h kroots n

/-- The chosen primes grow faster than every polynomial. -/
theorem p9_prime_superpolynomial (e : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) + 1) ^ e ≤ (p Ksz h kroots n : ℝ) := by
  filter_upwards [Nock.NockVMROM.poly_le_exp_eventually e] with n hn
  have hnat :
      13 ^ (n + 1) ≤ p Ksz h kroots n :=
    (le_max_right _ _).trans
      (Nat.le_of_lt (p9_p_spec Ksz h kroots n).2.1)
  have hreal :
      (13 : ℝ) ^ (n + 1) ≤ (p Ksz h kroots n : ℝ) := by
    exact_mod_cast hnat
  exact hn.trans hreal

/-- The actual field cardinalities, not an unrelated denominator, grow super-polynomially. -/
theorem p9_card_superpolynomial (e : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) + 1) ^ e ≤
        ((p9ExactSecurityFamily Ksz h kroots).cardAt n : ℝ) := by
  filter_upwards [p9_prime_superpolynomial Ksz h kroots e] with n hn
  rw [p9_exactSecurityFamily_card]
  have hp :
      (1 : ℝ) ≤ (p Ksz h kroots n : ℝ) := by
    exact_mod_cast (p9_p_spec Ksz h kroots n).1.one_lt.le
  have hp_le_cube :
      (p Ksz h kroots n : ℝ) ≤ (p Ksz h kroots n : ℝ) ^ 3 := by
    have hp_nonneg :
        (0 : ℝ) ≤ (p Ksz h kroots n : ℝ) :=
      (show (0 : ℝ) ≤ 1 by norm_num).trans hp
    have hp_le_sq :
        (p Ksz h kroots n : ℝ) ≤
          (p Ksz h kroots n : ℝ) * (p Ksz h kroots n : ℝ) := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hp hp_nonneg)
    calc
      (p Ksz h kroots n : ℝ) ≤
          (p Ksz h kroots n : ℝ) * (p Ksz h kroots n : ℝ) :=
        hp_le_sq
      _ ≤ (p Ksz h kroots n : ℝ) *
          ((p Ksz h kroots n : ℝ) * (p Ksz h kroots n : ℝ)) :=
        mul_le_mul_of_nonneg_left hp_le_sq hp_nonneg
      _ = (p Ksz h kroots n : ℝ) ^ 3 := by ring
  exact hn.trans (by simpa using hp_le_cube)

/-- Each selected prime exceeds its own security-parameter index. -/
theorem p9_index_lt_prime (n : ℕ) :
    n < p Ksz h kroots n := by
  have hpow : n < 13 ^ (n + 1) := by
    exact (Nat.lt_succ_self n).trans
      ((n + 1).lt_pow_self (by norm_num : 1 < 13))
  have hgrowth :
      13 ^ (n + 1) ≤ selectionBound Ksz h kroots n :=
    le_max_right _ _
  exact (hpow.trans_le hgrowth).trans
    (p9_p_spec Ksz h kroots n).2.1

/-- The exact family cannot have one fixed characteristic at every security parameter. -/
theorem p9_family_not_fixed_characteristic :
    ¬ ∃ q : ℕ, ∀ n : ℕ, CharP (FieldAt Ksz h kroots n) q := by
  rintro ⟨q, hq⟩
  have hpchar :
      CharP (FieldAt Ksz h kroots q) (p Ksz h kroots q) :=
    p9_FieldAt_charP Ksz h kroots q
  have heq : q = p Ksz h kroots q :=
    CharP.eq _ (hq q) hpchar
  exact (Nat.ne_of_lt (p9_index_lt_prime Ksz h kroots q)) heq


abbrev P8PointwiseBridge (workload bad : ℕ → ℝ) : Prop :=
  PointwiseP8Bound (p9ExactSecurityFamily Ksz h kroots) workload bad

theorem p9_negligible_of_P8_bound
    (workload bad : ℕ → ℝ) (dw : ℕ)
    (hwork_nonneg : ∀ n, 0 ≤ workload n)
    (hwork_poly : ∀ n, |workload n| ≤ ((n : ℝ) + 1) ^ dw)
    (hP8 : P8PointwiseBridge Ksz h kroots workload bad) :
    Negligible bad :=
  negligible_of_pointwiseP8Bound
    (p9ExactSecurityFamily Ksz h kroots) workload bad dw
    hwork_nonneg hwork_poly (p9_card_superpolynomial Ksz h kroots) hP8

theorem p9_hasExactAsymptoticSoundness
    (workload bad : ℕ → ℝ) (dw : ℕ)
    (hwork_nonneg : ∀ n, 0 ≤ workload n)
    (hwork_poly : ∀ n, |workload n| ≤ ((n : ℝ) + 1) ^ dw)
    (hP8 : P8PointwiseBridge Ksz h kroots workload bad) :
    HasExactAsymptoticSoundness
      (p9ExactSecurityFamily Ksz h kroots) workload bad :=
  ⟨hP8,
    p9_negligible_of_P8_bound Ksz h kroots workload bad dw
      hwork_nonneg hwork_poly hP8⟩

end ExactPrimeFamily

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.negligible_of_pointwiseP8Bound
#print axioms Nock.NockVMROM.Thm54.ExactPrimeFamily.p9_p_spec
#print axioms Nock.NockVMROM.Thm54.ExactPrimeFamily.p9_FieldAt_card
#print axioms Nock.NockVMROM.Thm54.ExactPrimeFamily.p9_FieldAt_charP
#print axioms Nock.NockVMROM.Thm54.ExactPrimeFamily.p9_hchar
#print axioms Nock.NockVMROM.Thm54.ExactPrimeFamily.p9_Ksz_lt
#print axioms Nock.NockVMROM.Thm54.ExactPrimeFamily.p9_workload_lt_of_le_Ksz
#print axioms Nock.NockVMROM.Thm54.ExactPrimeFamily.p9_wrapc
#print axioms Nock.NockVMROM.Thm54.ExactPrimeFamily.p9_wrapm
#print axioms Nock.NockVMROM.Thm54.ExactPrimeFamily.p9_fieldFamily_hasOrbit
#print axioms Nock.NockVMROM.Thm54.ExactPrimeFamily.p9_required_node_capacity
#print axioms Nock.NockVMROM.Thm54.ExactPrimeFamily.p9_card_superpolynomial
#print axioms Nock.NockVMROM.Thm54.ExactPrimeFamily.p9_family_not_fixed_characteristic
#print axioms Nock.NockVMROM.Thm54.ExactPrimeFamily.p9_negligible_of_P8_bound
#print axioms Nock.NockVMROM.Thm54.ExactPrimeFamily.p9_hasExactAsymptoticSoundness
