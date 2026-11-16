/-
  Nock/TraceGenExe/GL.lean

  **Executable Goldilocks.**  New module; additive.

  `Gold` is a canonical residue `x < p = 2^64 - 2^32 + 1` held in a `UInt64` (a one-field structure
  plus a proof, so it is compiled as the bare `UInt64`).  The operations `add / sub / neg / mul /
  pow / inv` are executable (`UInt64` wrap-around arithmetic) and each is proved equal to the
  corresponding `ZMod p` operation through `Gold.toZ : Gold → ZMod p`; `Gold.toZ` is a bijection
  with inverse `Gold.ofZ`.  `Gold.ofU64` reduces an arbitrary raw limb (used when reading a file).
-/
import Nock.Field
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false

namespace Nock.TraceGenExe

open Nock.Field

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

end Nock.TraceGenExe
