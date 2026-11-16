/-
  Nock/TraceGenExe/GoldFast.lean

  **Register Goldilocks multiplication.**  `Gold.mul` is `UInt64.ofNat (a.toNat * b.toNat % p)`:
  a bignum product and a bignum remainder per multiplication.  `mulU` multiplies in 32-bit limbs on `UInt64`
  registers (`2^64 = 2^32 - 1`, `2^96 = -1` mod `p`) and `mulU_toNat` proves it equal to `Gold.mulRaw`.
  `Gold.mulF` is the register version, `Gold.mulF_eq : mulF a b = a * b`; the fast checker calls it explicitly (no csimp); no
  proved definition changes.
-/
import Nock.TraceGenExe.GL

set_option autoImplicit false

namespace Nock.TraceGenExe

open Nock.Field

/-- Canonical reduction of a raw 64-bit value (`x < 2^64 < 2p`). -/
def redU (x : UInt64) : UInt64 := if pU ≤ x then x - pU else x

theorem redU_toNat (x : UInt64) : (redU x).toNat = x.toNat % p := by
  have hP := pU_toNat
  have h1 := toNat_lt' x
  have hp := p_lit
  unfold redU
  split_ifs with h
  · have := le_iff'.mp h
    rw [toNat_sub']
    rw [hp] at *
    omega
  · have := lt_iff'.mp (UInt64.not_le.mp h)
    rw [hp]; omega

/-- Register multiplication mod `p`. -/
def mulU (a b : UInt64) : UInt64 :=
  let a0 := a % 4294967296
  let a1 := a / 4294967296
  let b0 := b % 4294967296
  let b1 := b / 4294967296
  let ll := a0 * b0
  let lh := a0 * b1
  let hl := a1 * b0
  let hh := a1 * b1
  let t0 := redU ll
  let t1 := redU ((lh / 4294967296) * 4294967295)
  let t2 := redU ((lh % 4294967296) * 4294967296)
  let t3 := redU ((hl / 4294967296) * 4294967295)
  let t4 := redU ((hl % 4294967296) * 4294967296)
  let t5 := redU ((hh % 4294967296) * 4294967295)
  let t6 := hh / 4294967296
  subRaw (addRaw (addRaw (addRaw (addRaw (addRaw t0 t1) t2) t3) t4) t5) t6

theorem lt_p_of_mod (x : ℕ) : x % p < p := Nat.mod_lt _ Gold.p_pos

theorem chain_toNat (t0 t1 t2 t3 t4 t5 t6 : UInt64) (h0 : t0.toNat < p) (h1 : t1.toNat < p) (h2 : t2.toNat < p)
    (h3 : t3.toNat < p) (h4 : t4.toNat < p) (h5 : t5.toNat < p) (h6 : t6.toNat < p) :
    (subRaw (addRaw (addRaw (addRaw (addRaw (addRaw t0 t1) t2) t3) t4) t5) t6).toNat =
      (((((((t0.toNat + t1.toNat) % p + t2.toNat) % p + t3.toNat) % p + t4.toNat) % p + t5.toNat) % p) + p
        - t6.toNat) % p := by
  have L : ∀ x y : UInt64, x.toNat < p → y.toNat < p → (addRaw x y).toNat < p := fun x y hx hy => by
    rw [addRaw_toNat _ _ hx hy]; exact lt_p_of_mod _
  have e1 := L _ _ h0 h1
  have e2 := L _ _ e1 h2
  have e3 := L _ _ e2 h3
  have e4 := L _ _ e3 h4
  have e5 := L _ _ e4 h5
  rw [subRaw_toNat _ _ e5 h6, addRaw_toNat _ _ e4 h5, addRaw_toNat _ _ e3 h4, addRaw_toNat _ _ e2 h3,
    addRaw_toNat _ _ e1 h2, addRaw_toNat _ _ h0 h1]

theorem fin_aux (S P f K : ℕ) (hf : f < 18446744069414584321) (h : P + f = S + 18446744069414584321 * K) :
    (S % 18446744069414584321 + 18446744069414584321 - f) % 18446744069414584321 = P % 18446744069414584321 := by
  omega

theorem core_mod (LL LH HL HH : ℕ) (hHH : HH < 18446744073709551616) :
    (((((((LL % p + LH / 4294967296 * 4294967295 % p) % p + LH % 4294967296 * 4294967296 % p) % p +
      HL / 4294967296 * 4294967295 % p) % p + HL % 4294967296 * 4294967296 % p) % p +
      HH % 4294967296 * 4294967295 % p) % p) + p - HH / 4294967296) % p =
    (HH * 18446744073709551616 + (LH + HL) * 4294967296 + LL) % p := by
  have hp := p_lit
  rw [hp]
  -- strip the inner reductions
  have step : ∀ x y : ℕ, (x % 18446744069414584321 + y) % 18446744069414584321 = (x + y) % 18446744069414584321 := by
    intro x y; omega
  have step2 : ∀ x y : ℕ, (x + y % 18446744069414584321) % 18446744069414584321 = (x + y) % 18446744069414584321 := by
    intro x y; omega
  simp only [step, step2]
  have key : HH * 18446744073709551616 + (LH + HL) * 4294967296 + LL + HH / 4294967296 =
      (LL + LH / 4294967296 * 4294967295 + LH % 4294967296 * 4294967296 + HL / 4294967296 * 4294967295 +
        HL % 4294967296 * 4294967296 + HH % 4294967296 * 4294967295) +
        18446744069414584321 * (HH + HH / 4294967296 + LH / 4294967296 + HL / 4294967296) := by
    omega
  have hf : HH / 4294967296 < 18446744069414584321 := by omega
  exact fin_aux _ _ _ _ hf key

theorem mulU_toNat (a b : UInt64) (ha : a.toNat < p) (hb : b.toNat < p) :
    (mulU a b).toNat = a.toNat * b.toNat % p := by
  have hp := p_lit
  have hM : (4294967296 : UInt64).toNat = 4294967296 := by decide
  have hM1 : (4294967295 : UInt64).toNat = 4294967295 := by decide
  have ha' := toNat_lt' a
  have hb' := toNat_lt' b
  have mod_ : ∀ x : UInt64, (x % 4294967296).toNat = x.toNat % 4294967296 := by
    intro x; rw [UInt64.toNat_mod, hM]
  have div_ : ∀ x : UInt64, (x / 4294967296).toNat = x.toNat / 4294967296 := by
    intro x; rw [UInt64.toNat_div, hM]
  have mulnw : ∀ x y : UInt64, x.toNat < 4294967296 → y.toNat < 4294967296 → (x * y).toNat = x.toNat * y.toNat := by
    intro x y hx hy
    rw [UInt64.toNat_mul]
    apply Nat.mod_eq_of_lt
    calc x.toNat * y.toNat < 4294967296 * 4294967296 := Nat.mul_lt_mul'' hx hy
      _ = 18446744073709551616 := by norm_num
  have lim0 : ∀ x : UInt64, (x % 4294967296).toNat < 4294967296 := by
    intro x; rw [mod_]; exact Nat.mod_lt _ (by norm_num)
  have lim1 : ∀ x : UInt64, (x / 4294967296).toNat < 4294967296 := by
    intro x; rw [div_]; have := toNat_lt' x; omega
  have T1 : ∀ x : UInt64, (redU ((x / 4294967296) * 4294967295)).toNat = (x.toNat / 4294967296 * 4294967295) % p := by
    intro x; rw [redU_toNat, mulnw _ _ (lim1 x) (by rw [hM1]; norm_num), div_, hM1]
  have T5 : ∀ x : UInt64, (redU ((x % 4294967296) * 4294967295)).toNat = (x.toNat % 4294967296 * 4294967295) % p := by
    intro x; rw [redU_toNat, mulnw _ _ (lim0 x) (by rw [hM1]; norm_num), mod_, hM1]
  have T2 : ∀ x : UInt64, (redU ((x % 4294967296) * 4294967296)).toNat = (x.toNat % 4294967296 * 4294967296) % p := by
    intro x; rw [redU_toNat]
    have : ((x % 4294967296) * 4294967296 : UInt64).toNat = x.toNat % 4294967296 * 4294967296 := by
      rw [UInt64.toNat_mul, mod_, hM]
      apply Nat.mod_eq_of_lt
      have := Nat.mod_lt x.toNat (show 0 < 4294967296 by norm_num)
      omega
    rw [this]
  have hp6 : ∀ x : UInt64, (x / 4294967296).toNat < p := fun x => by have := lim1 x; omega
  have ll := mulnw (a % 4294967296) (b % 4294967296) (lim0 a) (lim0 b)
  have lh := mulnw (a % 4294967296) (b / 4294967296) (lim0 a) (lim1 b)
  have hl := mulnw (a / 4294967296) (b % 4294967296) (lim1 a) (lim0 b)
  have hh := mulnw (a / 4294967296) (b / 4294967296) (lim1 a) (lim1 b)
  rw [mod_, mod_] at ll
  rw [mod_, div_] at lh
  rw [div_, mod_] at hl
  rw [div_, div_] at hh
  unfold mulU
  simp only []
  rw [chain_toNat _ _ _ _ _ _ _ (by rw [redU_toNat]; exact lt_p_of_mod _) (by rw [T1]; exact lt_p_of_mod _)
    (by rw [T2]; exact lt_p_of_mod _) (by rw [T1]; exact lt_p_of_mod _) (by rw [T2]; exact lt_p_of_mod _)
    (by rw [T5]; exact lt_p_of_mod _) (hp6 _)]
  rw [redU_toNat, T1, T2, T1, T2, T5, div_, lh, hl, hh, ll]
  have hHHb0 : a.toNat / 4294967296 * (b.toNat / 4294967296) < 18446744073709551616 := by
    have := toNat_lt' (a / 4294967296 * (b / 4294967296)); rw [hh] at this; exact this
  generalize hLL : a.toNat % 4294967296 * (b.toNat % 4294967296) = LL
  generalize hLH : a.toNat % 4294967296 * (b.toNat / 4294967296) = LH
  generalize hHL : a.toNat / 4294967296 * (b.toNat % 4294967296) = HL
  generalize hHH : a.toNat / 4294967296 * (b.toNat / 4294967296) = HH
  have hHHb : HH < 18446744073709551616 := hHH ▸ hHHb0
  have hprod : a.toNat * b.toNat = HH * 18446744073709551616 + (LH + HL) * 4294967296 + LL := by
    rw [← hLL, ← hLH, ← hHL, ← hHH]
    have ea := (Nat.div_add_mod a.toNat 4294967296).symm
    have eb := (Nat.div_add_mod b.toNat 4294967296).symm
    generalize a.toNat / 4294967296 = A1 at *
    generalize a.toNat % 4294967296 = A0 at *
    generalize b.toNat / 4294967296 = B1 at *
    generalize b.toNat % 4294967296 = B0 at *
    rw [ea, eb]; ring
  rw [hprod]
  exact core_mod LL LH HL HH hHHb

namespace Gold

/-- Register multiplication of canonical elements. -/
def mulF (a b : Gold) : Gold :=
  ⟨mulU a.val b.val, by rw [mulU_toNat _ _ a.lt b.lt]; exact Nat.mod_lt _ p_pos⟩

theorem mulF_eq (a b : Gold) : mulF a b = a * b := by
  apply Gold.ext
  apply UInt64.toNat_inj.mp
  show (mulU a.val b.val).toNat = (mulRaw a.val b.val).toNat
  rw [mulU_toNat _ _ a.lt b.lt, mulRaw_toNat]

/-- Exponentiation by squaring on the register multiplication. -/
def powFF : ℕ → Gold → ℕ → Gold
  | 0, _, _ => 1
  | f + 1, a, n =>
    if n = 0 then 1 else
      let r := powFF f (mulF a a) (n / 2)
      if n % 2 = 1 then mulF a r else r

theorem powFF_eq : ∀ (f : ℕ) (a : Gold) (n : ℕ), powFF f a n = powF f a n
  | 0, _, _ => rfl
  | f + 1, a, n => by
    unfold powFF powF
    simp only [mulF_eq, powFF_eq f]

def powF' (a : Gold) (n : ℕ) : Gold := powFF (n + 1) a n

theorem powF'_eq (a : Gold) (n : ℕ) : powF' a n = pow a n := powFF_eq _ _ _

end Gold

end Nock.TraceGenExe
