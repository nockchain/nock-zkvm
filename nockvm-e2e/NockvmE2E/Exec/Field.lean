/-
  NockvmE2E/Exec/Field.lean

  Sources (read only, ported to Lean 4.35 / Mathlib 4.35): the nockvm library,
    Nock/TraceGenExe/GL.lean  (executable Goldilocks `Gold`, `toZ` agreement lemmas for + - * neg pow inv),
    Nock/TraceGenExe/K3.lean  (executable cubic extension `K3` over `x^3 = 7`, `toK` agreement lemmas),
    Nock/Field.lean           (the Goldilocks prime).
  Added here: `NonBinaryField KC`, a `SmoothCosetFftDomain n KC` (n ≤ 32), a 2-adic NTT.
-/
import NockvmE2E.Exec.Pratt
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.GetD
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.AdjoinRoot
import CompPoly.Fields.Basic
import ArkLib.Data.Domain.CosetFftDomain.Defs

set_option autoImplicit false

namespace NockvmE2E.Exec

/-- The Goldilocks prime `2^64 - 2^32 + 1`. -/
def p : ℕ := 2 ^ 64 - 2 ^ 32 + 1

theorem p_eq : p = 18446744069414584321 := by norm_num [p]

theorem goldilocks_prime : Nat.Prime p := by
  have := Primality.goldilocks_prime_nat
  exact this

instance : Fact (Nat.Prime p) := ⟨goldilocks_prime⟩

/-- The Goldilocks modulus as a `UInt64`. -/
def pU : UInt64 := 0xFFFFFFFF00000001

theorem pU_toNat : pU.toNat = 18446744069414584321 := by decide

theorem p_lit : p = 18446744069414584321 := p_eq

theorem toNat_add' (a b : UInt64) :
    (a + b).toNat = (a.toNat + b.toNat) % 18446744073709551616 := by
  rw [UInt64.toNat_add]

theorem toNat_sub' (a b : UInt64) :
    (a - b).toNat = (18446744073709551616 - b.toNat + a.toNat) % 18446744073709551616 := by
  rw [UInt64.toNat_sub]

theorem toNat_lt' (a : UInt64) : a.toNat < 18446744073709551616 := by
  have := UInt64.toNat_lt a; norm_num at this; exact this

theorem toNat_ofNat'' (n : ℕ) : (UInt64.ofNat n).toNat = n % 18446744073709551616 := by
  rw [UInt64.toNat_ofNat']

theorem lt_iff' {a b : UInt64} : a < b ↔ a.toNat < b.toNat := UInt64.lt_iff_toNat_lt
theorem le_iff' {a b : UInt64} : a ≤ b ↔ a.toNat ≤ b.toNat := UInt64.le_iff_toNat_le

theorem mod2 (x M : ℕ) (h : x < 2 * M) :
    (x < M ∧ x % M = x) ∨ (M ≤ x ∧ x % M = x - M) := by
  rcases Nat.lt_or_ge x M with h1 | h1
  · exact Or.inl ⟨h1, Nat.mod_eq_of_lt h1⟩
  · refine Or.inr ⟨h1, ?_⟩
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]

/-! ### Raw operations with their `ℕ` specifications -/

/-- Wrap-around add, then subtract `p` once if the sum overflowed or reached `p`. -/
def addRaw (a b : UInt64) : UInt64 :=
  let s := a + b
  if s < a ∨ pU ≤ s then s - pU else s

theorem addRaw_toNat (a b : UInt64) (ha : a.toNat < p) (hb : b.toNat < p) :
    (addRaw a b).toNat = (a.toNat + b.toNat) % p := by
  rw [p_lit] at *
  have hs := toNat_add' a b
  have hP := pU_toNat
  have h1 := toNat_lt' a
  have h2 := toNat_lt' b
  have m1 := mod2 (a.toNat + b.toNat) 18446744073709551616 (by omega)
  have m2 := mod2 (a.toNat + b.toNat) 18446744069414584321 (by omega)
  unfold addRaw
  simp only
  split_ifs with h
  · rw [toNat_sub']
    have m3 := mod2 (18446744073709551616 - pU.toNat + (a + b).toNat) 18446744073709551616 (by omega)
    rcases h with h | h
    · have := lt_iff'.mp h
      omega
    · have := le_iff'.mp h
      omega
  · rw [not_or] at h
    have h3 : a.toNat ≤ (a + b).toNat := by
      by_contra hc; exact h.1 (lt_iff'.mpr (by omega))
    have h4 : (a + b).toNat < pU.toNat := by
      by_contra hc; exact h.2 (le_iff'.mpr (by omega))
    omega

/-- Subtraction: wrap-around subtract, add `p` back when `a < b`. -/
def subRaw (a b : UInt64) : UInt64 := if a < b then a - b + pU else a - b

theorem subRaw_toNat (a b : UInt64) (ha : a.toNat < p) (hb : b.toNat < p) :
    (subRaw a b).toNat = (a.toNat + p - b.toNat) % p := by
  rw [p_lit] at *
  have hP := pU_toNat
  have h1 := toNat_lt' a
  have h2 := toNat_lt' b
  have m0 := mod2 (a.toNat + 18446744069414584321 - b.toNat) 18446744069414584321 (by omega)
  unfold subRaw
  split_ifs with h
  · have h3 := lt_iff'.mp h
    rw [toNat_add', toNat_sub', hP]
    have m3 := mod2 (18446744073709551616 - b.toNat + a.toNat) 18446744073709551616 (by omega)
    have m4 := mod2 ((18446744073709551616 - b.toNat + a.toNat) % 18446744073709551616 + 18446744069414584321)
      18446744073709551616 (by omega)
    omega
  · have h4 : b.toNat ≤ a.toNat := by
      by_contra hc; exact h (lt_iff'.mpr (by omega))
    rw [toNat_sub']
    have m3 := mod2 (18446744073709551616 - b.toNat + a.toNat) 18446744073709551616 (by omega)
    omega

/-- Negation. -/
def negRaw (a : UInt64) : UInt64 := if a = 0 then 0 else pU - a

theorem negRaw_toNat (a : UInt64) (ha : a.toNat < p) :
    (negRaw a).toNat = (p - a.toNat) % p := by
  rw [p_lit] at *
  have hP := pU_toNat
  have h1 := toNat_lt' a
  unfold negRaw
  split_ifs with h
  · subst h
    have : (0 : UInt64).toNat = 0 := rfl
    rw [this]
  · have h3 : a.toNat ≠ 0 := fun h0 => h (UInt64.toNat_inj.mp (by rw [h0]; rfl))
    rw [toNat_sub']
    omega

/-- Multiplication: product in `ℕ`, reduced mod `p`. -/
def mulRaw (a b : UInt64) : UInt64 := UInt64.ofNat (a.toNat * b.toNat % p)

theorem mulRaw_toNat (a b : UInt64) :
    (mulRaw a b).toNat = a.toNat * b.toNat % p := by
  unfold mulRaw
  rw [toNat_ofNat'']
  have : a.toNat * b.toNat % p < p := Nat.mod_lt _ (by rw [p_lit]; norm_num)
  rw [p_lit] at *
  omega

/-! ### The type -/

/-- A canonical Goldilocks element. -/
structure Gold where
  val : UInt64
  lt : val.toNat < p

namespace Gold

theorem p_pos : 0 < p := by rw [p_lit]; norm_num

theorem zero_lt : (0 : UInt64).toNat < p := by
  have : (0 : UInt64).toNat = 0 := rfl
  rw [this]; exact p_pos

theorem one_lt : (1 : UInt64).toNat < p := by
  have : (1 : UInt64).toNat = 1 := rfl
  rw [this, p_lit]; norm_num

def zero : Gold := ⟨0, zero_lt⟩
def one : Gold := ⟨1, one_lt⟩

instance : Inhabited Gold := ⟨zero⟩
instance : Zero Gold := ⟨zero⟩
instance : One Gold := ⟨one⟩

@[ext] theorem ext {a b : Gold} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

theorem ext_iff' {a b : Gold} : a = b ↔ a.val.toNat = b.val.toNat :=
  ⟨fun h => by rw [h], fun h => ext (UInt64.toNat_inj.mp h)⟩

/-- The semantic value in `ZMod p`. -/
def toZ (a : Gold) : ZMod p := (a.val.toNat : ZMod p)

theorem toZ_val (a : Gold) : (a.toZ).val = a.val.toNat := by
  unfold toZ
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt a.lt]

theorem toZ_injective : Function.Injective toZ := by
  intro a b h
  have := congrArg ZMod.val h
  rw [toZ_val, toZ_val] at this
  exact ext_iff'.mpr this

theorem ofNat_lt (n : ℕ) : (UInt64.ofNat (n % p)).toNat < p := by
  rw [toNat_ofNat'']
  have := Nat.mod_lt n p_pos
  rw [p_lit] at *
  omega

/-- The element of `Gold` with a given `ZMod p` value. -/
def ofZ (x : ZMod p) : Gold := ⟨UInt64.ofNat (x.val % p), ofNat_lt _⟩

theorem ofZ_val (x : ZMod p) : (ofZ x).val.toNat = x.val := by
  show (UInt64.ofNat (x.val % p)).toNat = _
  have h := ZMod.val_lt x
  rw [toNat_ofNat'', Nat.mod_eq_of_lt h]
  have h' : x.val < 18446744073709551616 := by have := p_lit; omega
  exact Nat.mod_eq_of_lt h'

theorem toZ_ofZ (x : ZMod p) : (ofZ x).toZ = x := by
  unfold toZ
  rw [ofZ_val, ZMod.natCast_zmod_val]

theorem ofZ_toZ (a : Gold) : ofZ a.toZ = a := toZ_injective (toZ_ofZ _)

/-- Reduce an arbitrary raw limb (as read from a file) to a canonical element. -/
def ofU64 (x : UInt64) : Gold := ⟨UInt64.ofNat (x.toNat % p), ofNat_lt _⟩

theorem ofU64_toZ (x : UInt64) : (ofU64 x).toZ = (x.toNat : ZMod p) := by
  unfold toZ ofU64
  show ((UInt64.ofNat (x.toNat % p)).toNat : ZMod p) = _
  rw [toNat_ofNat'']
  have := Nat.mod_lt x.toNat p_pos
  have h2 : x.toNat % p % 18446744073709551616 = x.toNat % p := by
    rw [p_lit] at *; omega
  rw [h2, ZMod.natCast_mod]

/-! ### The operations and their equalities with `ZMod p` -/

def add (a b : Gold) : Gold :=
  ⟨addRaw a.val b.val, by rw [addRaw_toNat _ _ a.lt b.lt]; exact Nat.mod_lt _ p_pos⟩
def sub (a b : Gold) : Gold :=
  ⟨subRaw a.val b.val, by rw [subRaw_toNat _ _ a.lt b.lt]; exact Nat.mod_lt _ p_pos⟩
def neg (a : Gold) : Gold :=
  ⟨negRaw a.val, by rw [negRaw_toNat _ a.lt]; exact Nat.mod_lt _ p_pos⟩
def mul (a b : Gold) : Gold :=
  ⟨mulRaw a.val b.val, by rw [mulRaw_toNat]; exact Nat.mod_lt _ p_pos⟩

instance : Add Gold := ⟨add⟩
instance : Sub Gold := ⟨sub⟩
instance : Neg Gold := ⟨neg⟩
instance : Mul Gold := ⟨mul⟩

theorem toZ_zero : (0 : Gold).toZ = 0 := by
  show ((((0 : UInt64)).toNat : ℕ) : ZMod p) = 0
  rfl
theorem toZ_one : (1 : Gold).toZ = 1 := by
  show ((((1 : UInt64)).toNat : ℕ) : ZMod p) = 1
  rfl

theorem toZ_add (a b : Gold) : (a + b).toZ = a.toZ + b.toZ := by
  show (((addRaw a.val b.val).toNat : ℕ) : ZMod p) = _
  rw [addRaw_toNat _ _ a.lt b.lt, ZMod.natCast_mod, Nat.cast_add]; rfl

theorem toZ_sub (a b : Gold) : (a - b).toZ = a.toZ - b.toZ := by
  show (((subRaw a.val b.val).toNat : ℕ) : ZMod p) = _
  rw [subRaw_toNat _ _ a.lt b.lt, ZMod.natCast_mod]
  have hb : b.val.toNat ≤ a.val.toNat + p := by have := b.lt; omega
  rw [Nat.cast_sub hb, Nat.cast_add, ZMod.natCast_self, add_zero]; rfl

theorem toZ_neg (a : Gold) : (-a).toZ = -a.toZ := by
  show (((negRaw a.val).toNat : ℕ) : ZMod p) = _
  rw [negRaw_toNat _ a.lt, ZMod.natCast_mod, Nat.cast_sub a.lt.le, ZMod.natCast_self, zero_sub]; rfl

theorem toZ_mul (a b : Gold) : (a * b).toZ = a.toZ * b.toZ := by
  show (((mulRaw a.val b.val).toNat : ℕ) : ZMod p) = _
  rw [mulRaw_toNat, ZMod.natCast_mod, Nat.cast_mul]; rfl

/-- Exponentiation by squaring with explicit fuel (structural, so the kernel can evaluate it). -/
def powF : ℕ → Gold → ℕ → Gold
  | 0, _, _ => 1
  | f + 1, a, n =>
    if n = 0 then 1 else
      let r := powF f (a * a) (n / 2)
      if n % 2 = 1 then a * r else r

theorem toZ_powF : ∀ (f : ℕ) (a : Gold) (n : ℕ), n < 2 ^ f → (powF f a n).toZ = a.toZ ^ n := by
  intro f
  induction f with
  | zero =>
    intro a n hn
    have : n = 0 := by simpa using hn
    subst this; exact toZ_one
  | succ f ih =>
    intro a n hn
    unfold powF
    by_cases h0 : n = 0
    · subst h0; simp [toZ_one]
    · simp only [h0, if_false]
      have h := ih (a * a) (n / 2) (by rw [pow_succ] at hn; omega)
      have hn2 : n = 2 * (n / 2) + n % 2 := by omega
      split_ifs with hc
      · rw [toZ_mul, h, toZ_mul]
        conv_rhs => rw [hn2, hc]
        ring
      · rw [h, toZ_mul]
        have : n % 2 = 0 := by omega
        conv_rhs => rw [hn2, this]
        ring

/-- Exponentiation (`ℕ` exponent). -/
def pow (a : Gold) (n : ℕ) : Gold := powF (n + 1) a n

theorem toZ_pow (n : ℕ) (a : Gold) : (pow a n).toZ = a.toZ ^ n :=
  toZ_powF _ _ _ (by
    have := Nat.lt_two_pow_self (n := n + 1)
    omega)

/-- Inverse: `a^(p-2)`; `0⁻¹ = 0`, as in `ZMod p`. -/
def inv (a : Gold) : Gold := pow a (p - 2)

instance : Inv Gold := ⟨inv⟩

theorem toZ_inv (a : Gold) : (a⁻¹).toZ = (a.toZ)⁻¹ := by
  show (pow a (p - 2)).toZ = _
  rw [toZ_pow]
  by_cases h : a.toZ = 0
  · rw [h, inv_zero, zero_pow]; rw [p_lit]; norm_num
  · have h1 : a.toZ ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h
    have h2 : p - 1 = (p - 2) + 1 := by rw [p_lit]
    rw [h2, pow_succ] at h1
    exact (eq_inv_of_mul_eq_one_left h1)

end Gold

open Polynomial

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
  rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := ZMod p) (V := KC), KC_finrank, Nat.card_zmod, p_eq]

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


/-! ## `NonBinaryField KC` and the smooth coset FFT domains (n ≤ 32) -/

theorem zmod_ne_zero (k : ℕ) (hk : 0 < k) (hk' : k < 18446744069414584321) : (k : ZMod p) ≠ 0 := by
  intro h
  have := congrArg ZMod.val h
  rw [ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt (by rw [p_eq]; exact hk')] at this
  omega

/-- `char KC ≠ 2`: `KC` is a `NonBinaryField`, as ArkLib's FRI needs. -/
noncomputable instance : NonBinaryField KC :=
  { (inferInstance : Field KC) with
    char_neq_2 := by
      intro h
      have h2 : (2 : ZMod p) = 0 := (algebraMap (ZMod p) KC).injective (by rw [map_ofNat, map_zero]; exact h)
      exact zmod_ne_zero 2 (by norm_num) (by norm_num) (by simpa using h2) }

/-- A generator of the 2-Sylow subgroup of `(ZMod p)ˣ`: `7^((p-1)/2^32) = 7^(2^32-1)`. -/
def gZ : ZMod p := 7 ^ (2 ^ 32 - 1)

theorem seven_ne_zero : (7 : ZMod p) ≠ 0 := zmod_ne_zero 7 (by norm_num) (by norm_num)

theorem gZ_ne_zero : gZ ≠ 0 := pow_ne_zero _ seven_ne_zero

theorem gZ_pow_2_32 : gZ ^ (2 ^ 32) = 1 := by
  have := ZMod.pow_card_sub_one_eq_one seven_ne_zero
  unfold gZ
  rw [← pow_mul, show (2 ^ 32 - 1) * 2 ^ 32 = p - 1 by rw [p_eq]; norm_num]
  exact this

/-- `gZ^(2^31) = 7^((p-1)/2) ≠ 1`. -/
theorem gZ_pow_2_31 : gZ ^ (2 ^ 31) ≠ 1 := by
  have := Gold.seven_pow_half
  unfold gZ
  rw [← pow_mul, show (2 ^ 32 - 1) * 2 ^ 31 = p / 2 by rw [p_eq]; norm_num]
  exact this

/-- `gZ` as a unit of order exactly `2^32`. -/
noncomputable def gU : (ZMod p)ˣ := Units.mk0 gZ gZ_ne_zero

theorem orderOf_gU : orderOf gU = 2 ^ 32 :=
  orderOf_eq_prime_pow (p := 2) (n := 31) (x := gU)
    (fun h => gZ_pow_2_31 (by simpa [gU] using congrArg Units.val h))
    (Units.ext (by simpa [gU] using gZ_pow_2_32))

/-- `zeta n = g^(2^(32-n))` embedded in `KCˣ`: a primitive `2^n`-th root of unity. -/
noncomputable def zeta (n : ℕ) : KCˣ :=
  Units.map (algebraMap (ZMod p) KC : ZMod p →* KC) (gU ^ 2 ^ (32 - n))

theorem orderOf_zeta {n : ℕ} (hn : n ≤ 32) : orderOf (zeta n) = 2 ^ n := by
  have hi := orderOf_injective (Units.map (algebraMap (ZMod p) KC : ZMod p →* KC))
    (Units.map_injective (algebraMap (ZMod p) KC).injective) (gU ^ 2 ^ (32 - n))
  unfold zeta
  rw [hi,
    orderOf_pow_of_dvd (by positivity) (by rw [orderOf_gU]; exact pow_dvd_pow 2 (by omega)),
    orderOf_gU, Nat.pow_div (Nat.sub_le _ _) (by norm_num), Nat.sub_sub_self hn]

/-- A unit of order exactly `2^n` gives a smooth coset FFT domain `c · ⟨z⟩` (index `i ↦ c z^i`). -/
def domainOfUnit {F : Type} [Field F] (n : ℕ) (z c : Fˣ) (hz : orderOf z = 2 ^ n) :
    Domain.SmoothCosetFftDomain n F where
  subgroupDomain :=
    { toFun := fun i => z ^ (Multiplicative.toAdd i : Fin (2 ^ n)).val
      map_one' := by simp
      map_mul' := fun a b => by
        show z ^ ((Multiplicative.toAdd a + Multiplicative.toAdd b : Fin (2 ^ n)).val) = _
        rw [Fin.val_add, ← pow_eq_pow_mod _ (hz ▸ pow_orderOf_eq_one z), pow_add] }
  subgroupDomain_inj := fun a b h => by
    have h' : z ^ (Multiplicative.toAdd a : Fin (2 ^ n)).val = z ^ (Multiplicative.toAdd b : Fin (2 ^ n)).val := h
    have := pow_injOn_Iio_orderOf (x := z)
      (show (Multiplicative.toAdd a : Fin (2 ^ n)).val < orderOf z by rw [hz]; exact (Multiplicative.toAdd a).isLt)
      (show (Multiplicative.toAdd b : Fin (2 ^ n)).val < orderOf z by rw [hz]; exact (Multiplicative.toAdd b).isLt) h'
    exact Multiplicative.toAdd.injective (Fin.ext this)
  cosetGenerator := c

/-- **The `SmoothCosetFftDomain n KC` for every `n ≤ 32`**: coset `7 · ⟨ω_n⟩`, `ω_n` of order `2^n`. -/
noncomputable def smoothDomain (n : ℕ) (hn : n ≤ 32) : Domain.SmoothCosetFftDomain n KC :=
  domainOfUnit n (zeta n) (Units.map (algebraMap (ZMod p) KC : ZMod p →* KC) (Units.mk0 7 seven_ne_zero))
    (orderOf_zeta hn)


/-! ## A 2-adic NTT over `Gold` -/

namespace NTT

/-- Even-indexed entries. -/
def evens {α : Type} : List α → List α
  | [] => []
  | [a] => [a]
  | a :: _ :: t => a :: evens t

/-- Odd-indexed entries. -/
def odds {α : Type} : List α → List α
  | [] => []
  | [_] => []
  | _ :: b :: t => b :: odds t

/-- Radix-2 decimation-in-time NTT of a list of length `2^k` with a root `ω` of order `2^k`:
`ntt k ω a [j] = Σ_i a[i] ω^(i j)`. -/
def ntt : ℕ → Gold → List Gold → List Gold
  | 0, _, a => a
  | k + 1, ω, a =>
    let e := ntt k (ω * ω) (evens a)
    let t := (List.range (2 ^ k)).map fun j => Gold.pow ω j * (ntt k (ω * ω) (odds a)).getD j 0
    List.zipWith (· + ·) e t ++ List.zipWith (· - ·) e t

/-- The naive DFT (the specification): `Σ_{i<len} a[i] ω^(i j)`. -/
def dft (ω : Gold) (a : List Gold) (j : ℕ) : Gold :=
  (List.range a.length).foldl (fun acc i => acc + a.getD i 0 * Gold.pow ω (i * j)) 0

/-- A primitive `2^k`-th root of unity of `Gold`: `(7^(2^32-1))^(2^(32-k))`. -/
def root (k : ℕ) : Gold := Gold.pow (Gold.pow (Gold.seven) (2 ^ 32 - 1)) (2 ^ (32 - k))

instance : DecidableEq Gold := fun a b =>
  decidable_of_iff (a.val = b.val) ⟨Gold.ext, fun h => h ▸ rfl⟩

def sample (n : ℕ) : List Gold := (List.range n).map fun i => Gold.ofU64 (UInt64.ofNat (i * i * 977 + 3 * i + 5))

/-- Executed check, size 8 and size 16, against the naive DFT (kernel evaluation, no `native_decide`). -/
theorem ntt_check8 : ntt 3 (root 3) (sample 8) = (List.range 8).map (dft (root 3) (sample 8)) := by decide +kernel
theorem ntt_check16 : ntt 4 (root 4) (sample 16) = (List.range 16).map (dft (root 4) (sample 16)) := by decide +kernel


section Correct

theorem getD_evens {α : Type} (d : α) : ∀ (a : List α) (i : ℕ), (evens a).getD i d = a.getD (2 * i) d
  | [], i => by simp [evens]
  | [x], 0 => by simp [evens]
  | [x], i + 1 => by simp [evens, show 2 * (i + 1) = 2 * i + 1 + 1 by ring]
  | x :: y :: t, 0 => by simp [evens]
  | x :: y :: t, i + 1 => by
    simp only [evens, List.getD_cons_succ, show 2 * (i + 1) = 2 * i + 1 + 1 by ring]
    exact getD_evens d t i

theorem getD_odds {α : Type} (d : α) : ∀ (a : List α) (i : ℕ), (odds a).getD i d = a.getD (2 * i + 1) d
  | [], i => by simp [odds]
  | [x], i => by simp [odds]
  | x :: y :: t, 0 => by simp [odds]
  | x :: y :: t, i + 1 => by
    simp only [odds, List.getD_cons_succ, show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by ring]
    exact getD_odds d t i

theorem length_evens {α : Type} : ∀ (a : List α), (evens a).length = (a.length + 1) / 2
  | [] => by simp [evens]
  | [x] => by simp [evens]
  | x :: y :: t => by simp only [evens, List.length_cons, length_evens t]; omega

theorem length_odds {α : Type} : ∀ (a : List α), (odds a).length = a.length / 2
  | [] => by simp [odds]
  | [x] => by simp [odds]
  | x :: y :: t => by simp only [odds, List.length_cons, length_odds t]; omega

theorem length_ntt : ∀ (k : ℕ) (ω : Gold) (a : List Gold), a.length = 2 ^ k → (ntt k ω a).length = 2 ^ k
  | 0, _, a, h => by simpa [ntt] using h
  | k + 1, ω, a, h => by
    have he : (evens a).length = 2 ^ k := by rw [length_evens, h, pow_succ]; omega
    have ho : (odds a).length = 2 ^ k := by rw [length_odds, h, pow_succ]; omega
    have h1 := length_ntt k (ω * ω) _ he
    simp only [ntt, List.length_append, List.length_zipWith, List.length_map, List.length_range, h1]
    rw [pow_succ]; omega

/-- Sum over `range (2N)` splits into even and odd indices. -/
theorem sum_range_two_mul {M : Type} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ m ∈ Finset.range (2 * N), f m = ∑ i ∈ Finset.range N, (f (2 * i) + f (2 * i + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    abel

theorem dft_toZ (ω : Gold) (a : List Gold) (j : ℕ) :
    (dft ω a j).toZ = ∑ i ∈ Finset.range a.length, (a.getD i 0).toZ * ω.toZ ^ (i * j) := by
  unfold dft
  have key : ∀ (n : ℕ) (acc : Gold), n ≤ a.length →
      ((List.range n).foldl (fun acc i => acc + a.getD i 0 * Gold.pow ω (i * j)) acc).toZ
        = acc.toZ + ∑ i ∈ Finset.range n, (a.getD i 0).toZ * ω.toZ ^ (i * j) := by
    intro n
    induction n with
    | zero => intro acc _; simp
    | succ n ih =>
      intro acc hn
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Finset.sum_range_succ]
      show (_ + _ * Gold.pow ω (n * j)).toZ = _
      rw [Gold.toZ_add, Gold.toZ_mul, Gold.toZ_pow, ih acc (by omega)]
      ring
  rw [key a.length 0 le_rfl, Gold.toZ_zero, zero_add]


theorem getD_zipWith (f : Gold → Gold → Gold) (e t : List Gold) (j : ℕ) (he : j < e.length)
    (ht : j < t.length) : (List.zipWith f e t).getD j 0 = f (e.getD j 0) (t.getD j 0) := by
  simp [List.getD_eq_getElem?_getD, he, ht]

/-- **NTT correctness**: for `a` of length `2^k` and `ω` with `ω^(2^(k-1)) = -1` (a primitive `2^k`-th root),
entry `j` of `ntt k ω a` is the evaluation `Σ_i a_i (ω^j)^i` of the polynomial `Σ a_i X^i` at `ω^j`, in `ZMod p`. -/
theorem ntt_spec : ∀ (k : ℕ) (ω : Gold) (a : List Gold), a.length = 2 ^ k →
    (k = 0 ∨ ω.toZ ^ 2 ^ (k - 1) = -1) → ∀ j < 2 ^ k,
    ((ntt k ω a).getD j 0).toZ = ∑ i ∈ Finset.range (2 ^ k), (a.getD i 0).toZ * ω.toZ ^ (i * j)
  | 0, ω, a, h, _, j, hj => by
    have : j = 0 := by simpa using hj
    subst this
    have : a.length = 1 := by simpa using h
    obtain ⟨x, rfl⟩ : ∃ x, a = [x] := by
      match a, this with
      | [x], _ => exact ⟨x, rfl⟩
    simp [ntt]
  | k + 1, ω, a, h, hk, j, hj => by
    have hw : ω.toZ ^ 2 ^ k = -1 := by simpa using hk.resolve_left (by omega)
    have he : (evens a).length = 2 ^ k := by rw [length_evens, h, pow_succ]; omega
    have ho : (odds a).length = 2 ^ k := by rw [length_odds, h, pow_succ]; omega
    have hk' : k = 0 ∨ (ω * ω).toZ ^ 2 ^ (k - 1) = -1 := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exact Or.inl h0
      · right
        rw [Gold.toZ_mul, ← sq, ← pow_mul, show 2 * 2 ^ (k - 1) = 2 ^ k by rw [← pow_succ']; congr 1; omega]
        exact hw
    have IHe := ntt_spec k (ω * ω) (evens a) he hk'
    have IHo := ntt_spec k (ω * ω) (odds a) ho hk'
    have le : (ntt k (ω * ω) (evens a)).length = 2 ^ k := length_ntt k _ _ he
    have lo : (ntt k (ω * ω) (odds a)).length = 2 ^ k := length_ntt k _ _ ho
    set e := ntt k (ω * ω) (evens a) with he_def
    set o := ntt k (ω * ω) (odds a) with ho_def
    set t := (List.range (2 ^ k)).map fun j => Gold.pow ω j * o.getD j 0 with ht_def
    have tlen : t.length = 2 ^ k := by simp [ht_def]
    have tget : ∀ j' < 2 ^ k, t.getD j' 0 = Gold.pow ω j' * o.getD j' 0 := by
      intro j' hj'; simp [ht_def, List.getD_eq_getElem?_getD, hj']
    have hlen1 : (List.zipWith (· + ·) e t).length = 2 ^ k := by simp [le, tlen]
    have hE : ∀ j' < 2 ^ k, (e.getD j' 0).toZ =
        ∑ i ∈ Finset.range (2 ^ k), (a.getD (2 * i) 0).toZ * (ω.toZ * ω.toZ) ^ (i * j') := by
      intro j' hj'; rw [IHe j' hj']
      exact Finset.sum_congr rfl fun i _ => by rw [getD_evens, Gold.toZ_mul]
    have hO : ∀ j' < 2 ^ k, (o.getD j' 0).toZ =
        ∑ i ∈ Finset.range (2 ^ k), (a.getD (2 * i + 1) 0).toZ * (ω.toZ * ω.toZ) ^ (i * j') := by
      intro j' hj'; rw [IHo j' hj']
      exact Finset.sum_congr rfl fun i _ => by rw [getD_odds, Gold.toZ_mul]
    have hn : ntt (k + 1) ω a = List.zipWith (· + ·) e t ++ List.zipWith (· - ·) e t := rfl
    rw [hn, show 2 ^ (k + 1) = 2 * 2 ^ k by ring, sum_range_two_mul]
    rw [show 2 ^ (k + 1) = 2 * 2 ^ k by ring] at hj
    rcases lt_or_ge j (2 ^ k) with hjk | hjk
    · rw [List.getD_append _ _ _ _ (by rw [hlen1]; exact hjk),
        getD_zipWith _ _ _ _ (by omega) (by omega), tget j hjk, Gold.toZ_add, Gold.toZ_mul, Gold.toZ_pow,
        hE j hjk, hO j hjk, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · obtain ⟨j', rfl⟩ : ∃ j', j = 2 ^ k + j' := ⟨j - 2 ^ k, by omega⟩
      have hj' : j' < 2 ^ k := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [hlen1]; omega), hlen1, Nat.add_sub_cancel_left,
        getD_zipWith _ _ _ _ (by omega) (by omega), tget j' hj', Gold.toZ_sub, Gold.toZ_mul, Gold.toZ_pow,
        hE j' hj', hO j' hj', Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e1 : ω.toZ ^ (2 * i * (2 ^ k + j')) = ω.toZ ^ (2 * i * j') := by
        have : ω.toZ ^ (2 * i * (2 ^ k + j')) = (ω.toZ ^ 2 ^ k) ^ (2 * i) * ω.toZ ^ (2 * i * j') := by ring
        rw [this, hw, Even.neg_one_pow ⟨i, by ring⟩, one_mul]
      have e2 : ω.toZ ^ ((2 * i + 1) * (2 ^ k + j')) = -ω.toZ ^ ((2 * i + 1) * j') := by
        have : ω.toZ ^ ((2 * i + 1) * (2 ^ k + j')) =
            (ω.toZ ^ 2 ^ k) ^ (2 * i + 1) * ω.toZ ^ ((2 * i + 1) * j') := by ring
        rw [this, hw, Odd.neg_one_pow ⟨i, rfl⟩, neg_one_mul]
      rw [e1, e2]
      ring

end Correct

end NTT

theorem gZ_pow_2_31_eq : gZ ^ 2 ^ 31 = -1 := by
  have h : gZ ^ 2 ^ 31 * gZ ^ 2 ^ 31 = 1 := by rw [← pow_add, ← two_mul, ← pow_succ']; exact gZ_pow_2_32
  exact (mul_self_eq_one_iff.mp h).resolve_left gZ_pow_2_31

theorem root_toZ (k : ℕ) : (NTT.root k).toZ = gZ ^ 2 ^ (32 - k) := by
  simp [NTT.root, Gold.toZ_pow, ← Gold.toZ_seven, Gold.seven, gZ]

/-- `root k` is a primitive `2^k`-th root of unity in `ZMod p` (`ω^(2^(k-1)) = -1`), for `1 ≤ k ≤ 32`. -/
theorem root_primitive {k : ℕ} (hk : k ≤ 32) : k = 0 ∨ (NTT.root k).toZ ^ 2 ^ (k - 1) = -1 := by
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · exact Or.inl h0
  · right
    rw [root_toZ, ← pow_mul, ← pow_add, show 32 - k + (k - 1) = 31 by omega]
    exact gZ_pow_2_31_eq

/-- **NTT evaluates the polynomial at the domain**: for `a` of length `2^k`, `k ≤ 32`, entry `j` of `ntt k (root k) a`
is `Σ_i a_i (ω_k^j)^i`, i.e. the polynomial `Σ a_i X^i` evaluated at the `j`-th point of the subgroup `⟨ω_k⟩`. -/
theorem ntt_root_spec {k : ℕ} (hk : k ≤ 32) (a : List Gold) (h : a.length = 2 ^ k) {j : ℕ} (hj : j < 2 ^ k) :
    ((NTT.ntt k (NTT.root k) a).getD j 0).toZ =
      ∑ i ∈ Finset.range (2 ^ k), (a.getD i 0).toZ * ((NTT.root k).toZ ^ j) ^ i := by
  rw [NTT.ntt_spec k _ a h (root_primitive hk) j hj]
  exact Finset.sum_congr rfl fun i _ => by rw [← pow_mul]; ring

/-- The NTT root is the embedded generator of the `SmoothCosetFftDomain` of `smoothDomain`. -/
theorem zeta_val (n : ℕ) : ((zeta n : KCˣ) : KC) = algebraMap (ZMod p) KC (NTT.root n).toZ := by
  simp [zeta, gU, root_toZ]

end NockvmE2E.Exec
