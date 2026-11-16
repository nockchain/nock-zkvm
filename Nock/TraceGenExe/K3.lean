/-
  Nock/TraceGenExe/K3.lean

The honest theorems (`honest_accepted_VSQ_of_run_chosen`, `nockCompiles_*`) are GENERIC in the cubic:
  they take `[Field K] [Algebra F K] [FiniteDimensional F K]` with `Module.finrank F K = 3` and
  `Fintype K` (the figures use `Fintype.card K = cK = p^3`, which follows from `finrank = 3`; it is not
  special to `GaloisField p 3`).  So any concrete cubic extension of `F = ZMod p` is admissible.

  **The concrete 𝕂**: `KC = (ZMod p)[X] / (X^3 - 7)`, `x^3 = 7`.  `7` is not a cube in `ZMod p`
  (`7^((p-1)/3) ≠ 1`, a kernel-evaluated certificate through `Gold.pow`), so `X^3 - 7` is irreducible
  (`X_pow_sub_C_irreducible_of_prime`), `KC` is a field, `finrank = 3`, `card = p^3`.
  The executable `K3` is the triple `(c0, c1, c2)` of `Gold`, standing for `c0 + c1 x + c2 x^2`;
  `K3.toK : K3 → KC` is proved to commute with add / sub / neg / mul / inv and to hit every element.
-/
import Nock.TraceGenExe.GL
import Nock.NockVMROM.Thm54.P8Core.Batch1541Thm54T0Tower
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.AdjoinRoot

set_option autoImplicit false

namespace Nock.TraceGenExe

open Nock.Field Polynomial

/-! ## The constant 7 and its certificates -/

namespace Gold

/-- The constant `7` (a generator of `(ZMod p)ˣ`). -/
def seven : Gold := ofU64 7

theorem toZ_seven : seven.toZ = 7 := by
  unfold seven
  rw [ofU64_toZ]
  show (((7 : UInt64).toNat : ℕ) : ZMod p) = 7
  have : (7 : UInt64).toNat = 7 := by decide
  rw [this]; rfl

/-- Kernel-evaluated certificate: `7^((p-1)/3) ≠ 1`. -/
theorem seven_pow_third_ne : (pow seven ((p - 1) / 3)).val.toNat ≠ 1 := by decide +kernel

/-- Kernel-evaluated certificate: `7^((p-1)/2) ≠ 1`. -/
theorem seven_pow_half_ne : (pow seven (p / 2)).val.toNat ≠ 1 := by decide +kernel

theorem seven_pow_third : (7 : ZMod p) ^ ((p - 1) / 3) ≠ 1 := by
  intro h
  apply seven_pow_third_ne
  have := toZ_pow ((p - 1) / 3) seven
  rw [toZ_seven, h] at this
  have h1 : (pow seven ((p - 1) / 3)).toZ = (1 : Gold).toZ := by rw [this, toZ_one]
  have h2 := congrArg (fun x : Gold => x.val.toNat) (toZ_injective h1)
  have e : ((1 : Gold)).val.toNat = 1 := rfl
  simp only [e] at h2
  exact h2

theorem seven_pow_half : (7 : ZMod p) ^ (p / 2) ≠ 1 := by
  intro h
  apply seven_pow_half_ne
  have := toZ_pow (p / 2) seven
  rw [toZ_seven, h] at this
  have h1 : (pow seven (p / 2)).toZ = (1 : Gold).toZ := by rw [this, toZ_one]
  have h2 := congrArg (fun x : Gold => x.val.toNat) (toZ_injective h1)
  have e : ((1 : Gold)).val.toNat = 1 := rfl
  simp only [e] at h2
  exact h2

end Gold

/-- `7` is not a cube in `ZMod p`. -/
theorem seven_not_cube : ∀ b : ZMod p, b ^ 3 ≠ 7 := by
  intro b hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hb
    exact absurd hb.symm (by
      intro h
      have := congrArg ZMod.val h
      rw [ZMod.val_zero, ZMod.val_ofNat_of_lt] at this <;> [omega; (rw [p_eq]; norm_num)])
  apply Gold.seven_pow_third
  have h3 : 3 * ((p - 1) / 3) = p - 1 := by rw [p_eq]
  rw [← hb, ← pow_mul, h3]
  exact ZMod.pow_card_sub_one_eq_one hb0

/-- `7` is not a square in `ZMod p`. -/
theorem seven_not_square : ¬ IsSquare (7 : ZMod p) := by
  intro h
  have h7 : (7 : ZMod p) ≠ 0 := by
    intro h0
    have := congrArg ZMod.val h0
    rw [ZMod.val_zero, ZMod.val_ofNat_of_lt (by rw [p_eq]; norm_num)] at this
    omega
  have hc : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n, p_eq]; norm_num
  have := (FiniteField.isSquare_iff hc h7).mp h
  rw [ZMod.card] at this
  exact Gold.seven_pow_half this

/-! ## The concrete field `KC` -/

/-- The cubic `X^3 - 7` over `ZMod p`. -/
noncomputable def cubicPoly : (ZMod p)[X] := X ^ 3 - C 7

theorem cubic_irreducible : Irreducible cubicPoly :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_three seven_not_cube

instance cubicFact : Fact (Irreducible cubicPoly) := ⟨cubic_irreducible⟩

/-- **The concrete 𝕂**: `(ZMod p)[X]/(X^3 - 7)`. -/
abbrev KC : Type := AdjoinRoot cubicPoly

theorem cubicPoly_ne_zero : cubicPoly ≠ 0 := cubic_irreducible.ne_zero

theorem cubicPoly_natDegree : cubicPoly.natDegree = 3 := by
  unfold cubicPoly; exact natDegree_X_pow_sub_C

theorem KC_finrank : Module.finrank (ZMod p) KC = 3 := by
  rw [(AdjoinRoot.powerBasis cubicPoly_ne_zero).finrank, AdjoinRoot.powerBasis_dim,
    cubicPoly_natDegree]

noncomputable instance KC_fintype : Fintype KC :=
  Module.fintypeOfFintype (AdjoinRoot.powerBasis cubicPoly_ne_zero).basis

noncomputable instance KC_decEq : DecidableEq KC := Classical.decEq _

instance KC_finiteDim : FiniteDimensional (ZMod p) KC :=
  Module.finite_of_finrank_pos (by rw [KC_finrank]; norm_num)

/-- `|𝕂| = p^3`, hence `cK` (`VclL.Events.cK_eq`). -/
theorem KC_card : Fintype.card KC = 18446744069414584321 ^ 3 := by
  -- 4.35: go through `Nat.card` (instance-agnostic); the `Fintype` form unified
  -- instances by evaluating the card and OOMed.
  rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod p) (V := KC), KC_finrank,
    Nat.card_zmod, p_eq]

/-- The adjoined root `x`. -/
noncomputable def xr : KC := AdjoinRoot.root cubicPoly

/-- `x^3 = 7`. -/
theorem xr_cube : xr ^ 3 = algebraMap (ZMod p) KC 7 := by
  have h := AdjoinRoot.eval₂_root cubicPoly
  unfold cubicPoly at h
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

/-! ## The executable cubic extension -/

/-- `c0 + c1 x + c2 x^2`, `x^3 = 7`. -/
structure K3 where
  c0 : Gold
  c1 : Gold
  c2 : Gold

namespace K3

instance : Inhabited K3 := ⟨⟨0, 0, 0⟩⟩

def zero : K3 := ⟨0, 0, 0⟩
def one : K3 := ⟨1, 0, 0⟩
instance : Zero K3 := ⟨zero⟩
instance : One K3 := ⟨one⟩

def add (a b : K3) : K3 := ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩
def sub (a b : K3) : K3 := ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2⟩
def neg (a : K3) : K3 := ⟨-a.c0, -a.c1, -a.c2⟩
/-- Multiplication in `F[x]/(x^3 - 7)`. -/
def mul (a b : K3) : K3 :=
  ⟨a.c0 * b.c0 + Gold.seven * (a.c1 * b.c2 + a.c2 * b.c1),
   a.c0 * b.c1 + a.c1 * b.c0 + Gold.seven * (a.c2 * b.c2),
   a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0⟩
/-- Scalar multiplication by a base-field element. -/
def smul (s : Gold) (a : K3) : K3 := ⟨s * a.c0, s * a.c1, s * a.c2⟩
/-- The norm `N(a) = a0³ + 7 a1³ + 49 a2³ - 21 a0 a1 a2 ∈ F` and the adjugate. -/
def adj (a : K3) : K3 :=
  ⟨a.c0 * a.c0 - Gold.seven * (a.c1 * a.c2),
   Gold.seven * (a.c2 * a.c2) - a.c0 * a.c1,
   a.c1 * a.c1 - a.c0 * a.c2⟩
def norm (a : K3) : Gold :=
  let A := adj a
  a.c0 * A.c0 + Gold.seven * (a.c1 * A.c2 + a.c2 * A.c1)
/-- Inverse (`0⁻¹ = 0`): `adj a · N(a)⁻¹`. -/
def inv (a : K3) : K3 := smul (norm a)⁻¹ (adj a)

instance : Add K3 := ⟨add⟩
instance : Sub K3 := ⟨sub⟩
instance : Neg K3 := ⟨neg⟩
instance : Mul K3 := ⟨mul⟩
instance : Inv K3 := ⟨inv⟩

/-- The semantic value in `KC`. -/
noncomputable def toK (a : K3) : KC :=
  algebraMap (ZMod p) KC a.c0.toZ + algebraMap (ZMod p) KC a.c1.toZ * xr +
    algebraMap (ZMod p) KC a.c2.toZ * xr ^ 2

section
variable (a b : K3)

private theorem seven_map : algebraMap (ZMod p) KC Gold.seven.toZ = xr ^ 3 := by
  rw [Gold.toZ_seven, xr_cube]

theorem toK_zero : toK 0 = 0 := by
  show toK zero = 0
  simp [toK, zero, Gold.toZ_zero]

theorem toK_one : toK 1 = 1 := by
  show toK one = 1
  simp [toK, one, zero, Gold.toZ_zero, Gold.toZ_one]

theorem toK_add : toK (a + b) = toK a + toK b := by
  show toK (add a b) = _
  simp only [toK, add, Gold.toZ_add, map_add]; ring

theorem toK_sub : toK (a - b) = toK a - toK b := by
  show toK (sub a b) = _
  simp only [toK, sub, Gold.toZ_sub, map_sub]; ring

theorem toK_neg : toK (-a) = -toK a := by
  show toK (neg a) = _
  simp only [toK, neg, Gold.toZ_neg, map_neg]; ring

theorem toK_mul : toK (a * b) = toK a * toK b := by
  show toK (mul a b) = _
  simp only [toK, mul, Gold.toZ_add, Gold.toZ_mul, map_add, map_mul, seven_map]
  ring

theorem toK_smul (s : Gold) : toK (smul s a) = algebraMap (ZMod p) KC s.toZ * toK a := by
  simp only [toK, smul, Gold.toZ_mul, map_mul]; ring

/-- `a · adj a = N(a)` (embedded). -/
theorem toK_mul_adj : toK a * toK (adj a) = algebraMap (ZMod p) KC (norm a).toZ := by
  simp only [toK, adj, norm, Gold.toZ_add, Gold.toZ_sub, Gold.toZ_mul, map_add, map_sub, map_mul,
    seven_map]
  ring

/-- Coordinates: `c0 + c1 x + c2 x^2 = 0` in `KC` forces `c0 = c1 = c2 = 0` (`X^3 - 7` has degree 3). -/
theorem coords_eq_zero (c0 c1 c2 : ZMod p)
    (h : algebraMap (ZMod p) KC c0 + algebraMap (ZMod p) KC c1 * xr + algebraMap (ZMod p) KC c2 * xr ^ 2 = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
  set g : (ZMod p)[X] := C c0 + C c1 * X + C c2 * X ^ 2 with hg
  have hmk : AdjoinRoot.mk cubicPoly g = 0 := by
    rw [← h]
    simp only [hg, map_add, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    rfl
  have hdvd : cubicPoly ∣ g := AdjoinRoot.mk_eq_zero.mp hmk
  have hdeg : g.degree < cubicPoly.degree := by
    rw [degree_eq_natDegree cubicPoly_ne_zero, cubicPoly_natDegree]
    have : g.degree ≤ 2 := by
      rw [hg]; compute_degree
    exact lt_of_le_of_lt this (by norm_num)
  have h0 : g = 0 := eq_zero_of_dvd_of_degree_lt hdvd hdeg
  have c0' : g.coeff 0 = c0 := by simp [hg, coeff_C]
  have c1' : g.coeff 1 = c1 := by simp [hg, coeff_X, coeff_C]
  have c2' : g.coeff 2 = c2 := by simp [hg, coeff_X, coeff_C, coeff_X_pow]
  rw [h0] at c0' c1' c2'
  simp at c0' c1' c2'
  exact ⟨c0'.symm, c1'.symm, c2'.symm⟩

theorem toK_injective : Function.Injective toK := by
  intro a b h
  have h' : toK (a - b) = 0 := by rw [toK_sub, h, sub_self]
  change toK (sub a b) = 0 at h'
  simp only [toK, sub, Gold.toZ_sub, map_sub] at h'
  obtain ⟨e0, e1, e2⟩ := coords_eq_zero (a.c0.toZ - b.c0.toZ) (a.c1.toZ - b.c1.toZ) (a.c2.toZ - b.c2.toZ)
    (by simp only [map_sub]; linear_combination h')
  have := fun (x y : Gold) (e : x.toZ - y.toZ = 0) => Gold.toZ_injective (sub_eq_zero.mp e)
  cases a; cases b
  simp only [mk.injEq]
  exact ⟨this _ _ e0, this _ _ e1, this _ _ e2⟩

theorem monic_cubic : cubicPoly.Monic := monic_X_pow_sub_C _ (by norm_num)

theorem toK_surjective : Function.Surjective toK := by
  intro y
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective (g := cubicPoly) y
  set r := g %ₘ cubicPoly with hr
  have hmod : AdjoinRoot.mk cubicPoly g = AdjoinRoot.mk cubicPoly r := by
    rw [AdjoinRoot.mk_eq_mk]
    refine ⟨g /ₘ cubicPoly, ?_⟩
    have := modByMonic_add_div g cubicPoly
    rw [hr]; linear_combination -this
  have hdeg : r.natDegree < 3 := by
    have h1 := degree_modByMonic_lt g monic_cubic
    by_cases h0 : r = 0
    · rw [h0]; simp
    · rw [degree_eq_natDegree h0, degree_eq_natDegree cubicPoly_ne_zero, cubicPoly_natDegree] at h1
      exact_mod_cast h1
  have hsum := as_sum_range' r 3 hdeg
  refine ⟨⟨Gold.ofZ (r.coeff 0), Gold.ofZ (r.coeff 1), Gold.ofZ (r.coeff 2)⟩, ?_⟩
  have key : AdjoinRoot.mk cubicPoly r = AdjoinRoot.mk cubicPoly
      (∑ i ∈ Finset.range 3, monomial i (r.coeff i)) := congrArg _ hsum
  rw [hmod, key]
  simp only [toK, Gold.toZ_ofZ, Finset.sum_range_succ, Finset.sum_range_zero, map_add, map_mul, map_pow,
    ← C_mul_X_pow_eq_monomial, AdjoinRoot.mk_C, AdjoinRoot.mk_X, zero_add, pow_zero, pow_one, mul_one]
  rfl

/-- The adjugate coordinates vanish only at `0` (`7` is not a cube). -/
theorem adj_zero_imp (x0 x1 x2 : ZMod p) (h0 : x0 * x0 - 7 * (x1 * x2) = 0)
    (h1 : 7 * (x2 * x2) - x0 * x1 = 0) (h2 : x1 * x1 - x0 * x2 = 0) :
    x0 = 0 ∧ x1 = 0 ∧ x2 = 0 := by
  by_cases hx2 : x2 = 0
  · subst hx2
    have e0 : x0 = 0 := by
      have : x0 * x0 = 0 := by linear_combination h0
      exact mul_self_eq_zero.mp this
    have e1 : x1 = 0 := by
      have : x1 * x1 = 0 := by linear_combination h2
      exact mul_self_eq_zero.mp this
    exact ⟨e0, e1, rfl⟩
  · exfalso
    apply seven_not_cube (x1 / x2)
    have hx0 : x0 = x1 * x1 / x2 := by field_simp; linear_combination -h2
    rw [div_pow]
    field_simp
    have : x1 ^ 3 = x0 * x1 * x2 := by rw [hx0]; field_simp
    rw [this]
    linear_combination (-x2) * h1 * 1

theorem toK_ne_zero_norm (a : K3) (h : toK a ≠ 0) : (norm a).toZ ≠ 0 := by
  intro hN
  have hm := toK_mul_adj a
  rw [hN, map_zero] at hm
  have hadj : toK (adj a) = 0 := by
    rcases mul_eq_zero.mp hm with h' | h'
    · exact absurd h' h
    · exact h'
  have hadj' : adj a = 0 := toK_injective (by rw [hadj, toK_zero])
  have e0 : (adj a).c0 = 0 := by rw [hadj']; rfl
  have e1 : (adj a).c1 = 0 := by rw [hadj']; rfl
  have e2 : (adj a).c2 = 0 := by rw [hadj']; rfl
  have z0 := congrArg Gold.toZ e0
  have z1 := congrArg Gold.toZ e1
  have z2 := congrArg Gold.toZ e2
  simp only [adj, Gold.toZ_sub, Gold.toZ_mul, Gold.toZ_seven, Gold.toZ_zero] at z0 z1 z2
  obtain ⟨y0, y1, y2⟩ := adj_zero_imp _ _ _ z0 z1 z2
  apply h
  simp only [toK, y0, y1, y2, map_zero, zero_mul, add_zero]

/-- **The executable inverse is the field inverse** (including `0⁻¹ = 0`). -/
theorem toK_inv (a : K3) : toK (a⁻¹) = (toK a)⁻¹ := by
  show toK (inv a) = _
  unfold inv
  rw [toK_smul, Gold.toZ_inv]
  by_cases h : toK a = 0
  · have hN : (norm a).toZ = 0 := by
      have ha : a = 0 := toK_injective (by rw [h, toK_zero])
      subst ha
      have z0 : ((0 : K3).c0).toZ = 0 := Gold.toZ_zero
      have z1 : ((0 : K3).c1).toZ = 0 := Gold.toZ_zero
      have z2 : ((0 : K3).c2).toZ = 0 := Gold.toZ_zero
      simp only [norm, adj, Gold.toZ_add, Gold.toZ_mul, Gold.toZ_sub, z0, z1, z2]
      ring
    rw [hN, inv_zero, map_zero, zero_mul, h, inv_zero]
  · have hN := toK_ne_zero_norm a h
    have hm := toK_mul_adj a
    have hφ : algebraMap (ZMod p) KC (norm a).toZ ≠ 0 := by
      intro h0; exact hN ((map_eq_zero _).mp h0)
    rw [map_inv₀]
    field_simp
    rw [mul_comm, hm]

end

end K3

end Nock.TraceGenExe
