/-
  NockvmE2E/Exec/VLink.lean   (proof-only)

  Link of the verifier's field `Exec/VField.lean` (`VF`, `UInt64`) to the kernel-checked `Exec/Field.lean`:
  `VF.add/sub/neg` have the `ℕ`-specification of `Gold`'s (canonical inputs).  `VF.mul` / `VF.pow` / `VF.inv` are NOT linked:
  (`pow` is a `while` loop = `partial`; `mul` is the 32-bit-limb schedule, proof not done here).
-/
import NockvmE2E.Exec.Field
import NockvmE2E.Exec.VField

set_option autoImplicit false

namespace NockvmE2E.Exec.VL

open NockvmE2E.Exec

theorem P_toNat : VF.P.toNat = 18446744069414584321 := by decide
theorem EPS_toNat : VF.EPS.toNat = 4294967295 := by decide

theorem add_toNat (a b : UInt64) (ha : a.toNat < p) (hb : b.toNat < p) :
    (VF.add a b).toNat = (a.toNat + b.toNat) % p := by
  rw [p_lit] at *
  have hP := P_toNat
  have hE := EPS_toNat
  have h1 := toNat_lt' a
  have h2 := toNat_lt' b
  have hs := toNat_add' a b
  have m1 := mod2 (a.toNat + b.toNat) 18446744073709551616 (by omega)
  unfold VF.add
  simp only
  by_cases hov : a + b < a
  · have h3 := lt_iff'.mp hov
    have hs2 := toNat_add' (a + b) VF.EPS
    simp only [hov, ite_true]
    by_cases hge : VF.P ≤ a + b + VF.EPS
    · have := le_iff'.mp hge
      omega
    · have h4 : ¬ (VF.P.toNat ≤ (a + b + VF.EPS).toNat) := fun h => hge (le_iff'.mpr h)
      simp only [ge_iff_le, hge, ite_false]
      omega
  · have h3 : a.toNat ≤ (a + b).toNat := by
      by_contra hc; exact hov (lt_iff'.mpr (by omega))
    simp only [hov, ite_false]
    by_cases hge : VF.P ≤ a + b
    · have := le_iff'.mp hge
      simp only [ge_iff_le, hge, ite_true]
      rw [toNat_sub']
      omega
    · have : ¬ (VF.P.toNat ≤ (a + b).toNat) := fun h => hge (le_iff'.mpr h)
      simp only [ge_iff_le, hge, ite_false]
      omega

theorem sub_toNat (a b : UInt64) (ha : a.toNat < p) (hb : b.toNat < p) :
    (VF.sub a b).toNat = (a.toNat + p - b.toNat) % p := by
  rw [p_lit] at *
  have hE := EPS_toNat
  have h1 := toNat_lt' a
  have h2 := toNat_lt' b
  have m0 := mod2 (a.toNat + 18446744069414584321 - b.toNat) 18446744069414584321 (by omega)
  unfold VF.sub
  by_cases h : a ≥ b
  · have h3 := le_iff'.mp h
    simp only [h, ite_true]
    rw [toNat_sub']
    have m3 := mod2 (18446744073709551616 - b.toNat + a.toNat) 18446744073709551616 (by omega)
    omega
  · have h3 : a.toNat < b.toNat := by
      by_contra hc; exact h (le_iff'.mpr (by omega))
    simp only [h, ite_false]
    rw [toNat_sub', toNat_sub']
    have m3 := mod2 (18446744073709551616 - b.toNat + a.toNat) 18446744073709551616 (by omega)
    have m4 := mod2 ((18446744073709551616 - b.toNat + a.toNat) % 18446744073709551616 + 0)
      18446744073709551616 (by omega)
    omega

theorem neg_toNat (a : UInt64) (ha : a.toNat < p) :
    (VF.neg a).toNat = (p - a.toNat) % p := by
  rw [p_lit] at *
  have hP := P_toNat
  have h1 := toNat_lt' a
  unfold VF.neg
  by_cases h : a = 0
  · subst h
    have : (0 : UInt64).toNat = 0 := rfl
    simp [this]
  · have h3 : a.toNat ≠ 0 := fun h0 => h (UInt64.toNat_inj.mp (by rw [h0]; rfl))
    have hb : (a == 0) = false := by simpa using h
    simp only [hb]
    simp only [Bool.false_eq_true, ite_false]
    rw [toNat_sub']
    omega

theorem shr32 (x : UInt64) : (x >>> 32).toNat = x.toNat / 4294967296 := by
  rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
theorem shl32 (x : UInt64) : (x <<< 32).toNat = x.toNat * 4294967296 % 18446744073709551616 := by
  rw [UInt64.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]
theorem and32 (x : UInt64) : (x &&& VF.EPS).toNat = x.toNat % 4294967296 := by
  rw [UInt64.toNat_and, EPS_toNat]
  have := @Nat.and_two_pow_sub_one_eq_mod x.toNat 32
  simpa using this
theorem mulsmall (x y : UInt64) (hx : x.toNat < 4294967296) (hy : y.toNat < 4294967296) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [UInt64.toNat_mul]
  apply Nat.mod_eq_of_lt
  calc x.toNat * y.toNat ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
    _ < 2 ^ 64 := by norm_num

theorem mod_of (T res K : ℕ) (h : T = res + 18446744069414584321 * K) (hr : res < 18446744069414584321) :
    res = T % 18446744069414584321 := by
  subst h; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

theorem final_aux (lo hi hh hl t0 t1 r0 r1 T : ℕ) (hTT : T = hi * 18446744073709551616 + lo)
    (hlo : lo < 18446744073709551616) (hhi : hi < 18446744073709551616)
    (nhh : hh = hi / 4294967296) (nhl : hl = hi % 4294967296) (nt1 : t1 = hl * 4294967295)
    (nt0 : t0 = if lo < hh then lo + 18446744069414584321 - hh else lo - hh)
    (nr0 : r0 = (t0 + t1) % 18446744073709551616)
    (nr1 : r1 = if r0 < t0 then (r0 + 4294967295) % 18446744073709551616 else r0) :
    (if 18446744069414584321 ≤ r1 then r1 - 18446744069414584321 else r1) = T % 18446744069414584321 := by
  have hhi' : hi = hh * 4294967296 + hl := by omega
  have hlt : hl < 4294967296 := by omega
  by_cases h1 : lo < hh <;> by_cases h2 : r0 < t0 <;> by_cases h3 : 18446744069414584321 ≤ r1 <;>
    simp only [h1, h2, h3, ite_true, ite_false] at nt0 nr1 ⊢ <;>
    first
    | exact mod_of _ _ (hh * 4294967297 + hl - 1) (by omega) (by omega)
    | exact mod_of _ _ (hh * 4294967297 + hl) (by omega) (by omega)
    | exact mod_of _ _ (hh * 4294967297 + hl + 1) (by omega) (by omega)

set_option maxRecDepth 100000 in
theorem hi_aux (T P00 P01 P10 P11 mid midc lo loc hi : ℕ)
    (hab : T = P11 * 18446744073709551616 + (P01 + P10) * 4294967296 + P00)
    (b00 : P00 < 18446744073709551616) (b01 : P01 < 18446744073709551616) (b10 : P10 < 18446744073709551616)
    (b11 : P11 < 18446744073709551616)
    (bound : T < 18446744073709551616 * 18446744073709551616)
    (nmid : mid = (P01 + P10) % 18446744073709551616)
    (nmidc : midc = if mid < P01 then 1 else 0)
    (nlo : lo = (P00 + mid * 4294967296 % 18446744073709551616) % 18446744073709551616)
    (nloc : loc = if lo < P00 then 1 else 0)
    (nhi : hi = ((((P11 + mid / 4294967296) % 18446744073709551616 +
      midc * 4294967296 % 18446744073709551616) % 18446744073709551616) + loc) % 18446744073709551616) :
    T = hi * 18446744073709551616 + lo := by
  have hmc : midc * 18446744073709551616 + mid = P01 + P10 := by
    clear nhi nlo nloc hab bound
    by_cases h : mid < P01 <;> simp only [h, ite_true, ite_false] at nmidc <;> omega
  have hlc : loc * 18446744073709551616 + lo = P00 + mid % 4294967296 * 4294967296 := by
    clear nhi hab bound hmc nmidc
    by_cases h : lo < P00 <;> simp only [h, ite_true, ite_false] at nloc <;> omega
  have hmc1 : midc ≤ 1 := by
    by_cases h : mid < P01 <;> simp only [h, ite_true, ite_false] at nmidc <;> omega
  have hlc1 : loc ≤ 1 := by
    by_cases h : lo < P00 <;> simp only [h, ite_true, ite_false] at nloc <;> omega
  have e1 : T = (P11 + midc * 4294967296 + mid / 4294967296 + loc) * 18446744073709551616 + lo := by
    clear nhi nlo nloc nmid nmidc bound
    have hd : mid = mid / 4294967296 * 4294967296 + mid % 4294967296 := (Nat.div_add_mod' mid 4294967296).symm
    generalize mid / 4294967296 = m1 at *
    generalize mid % 4294967296 = m0 at *
    subst hd
    linarith
  have e2 : P11 + midc * 4294967296 + mid / 4294967296 + loc < 18446744073709551616 := by
    clear nhi nlo nloc nmid nmidc
    omega
  have e3 : hi = P11 + midc * 4294967296 + mid / 4294967296 + loc := by
    clear nlo nloc nmid nmidc hab bound e1 hmc hlc
    omega
  rw [e3]; exact e1

theorem ite_lt (x y : UInt64) : (if x < y then (1 : UInt64) else 0).toNat = if x.toNat < y.toNat then 1 else 0 := by
  by_cases h : x < y
  · simp only [h, lt_iff'.mp h, ite_true]; rfl
  · have h' : ¬ x.toNat < y.toNat := fun z => h (lt_iff'.mpr z)
    simp only [h, h', ite_false]; rfl

theorem mul_toNat (a b : UInt64) : (VF.mul a b).toNat = a.toNat * b.toNat % p := by
  rw [p_lit]
  unfold VF.mul
  simp only []
  generalize ha0 : a &&& VF.EPS = a0
  generalize ha1 : a >>> 32 = a1
  generalize hb0 : b &&& VF.EPS = b0
  generalize hb1 : b >>> 32 = b1
  have na0 : a0.toNat = a.toNat % 4294967296 := by rw [← ha0, and32]
  have na1 : a1.toNat = a.toNat / 4294967296 := by rw [← ha1, shr32]
  have nb0 : b0.toNat = b.toNat % 4294967296 := by rw [← hb0, and32]
  have nb1 : b1.toNat = b.toNat / 4294967296 := by rw [← hb1, shr32]
  have la := toNat_lt' a
  have lb := toNat_lt' b
  have la0 : a0.toNat < 4294967296 := by omega
  have lb0 : b0.toNat < 4294967296 := by omega
  have la1 : a1.toNat < 4294967296 := by omega
  have lb1 : b1.toNat < 4294967296 := by omega
  generalize hp00 : a0 * b0 = p00
  generalize hp01 : a0 * b1 = p01
  generalize hp10 : a1 * b0 = p10
  generalize hp11 : a1 * b1 = p11
  have n00 : p00.toNat = a0.toNat * b0.toNat := by rw [← hp00, mulsmall _ _ la0 lb0]
  have n01 : p01.toNat = a0.toNat * b1.toNat := by rw [← hp01, mulsmall _ _ la0 lb1]
  have n10 : p10.toNat = a1.toNat * b0.toNat := by rw [← hp10, mulsmall _ _ la1 lb0]
  have n11 : p11.toNat = a1.toNat * b1.toNat := by rw [← hp11, mulsmall _ _ la1 lb1]
  have hab : a.toNat * b.toNat = p11.toNat * 18446744073709551616 + (p01.toNat + p10.toNat) * 4294967296 + p00.toNat := by
    rw [n00, n01, n10, n11]
    have ea : a.toNat = a1.toNat * 4294967296 + a0.toNat := by omega
    have eb : b.toNat = b1.toNat * 4294967296 + b0.toNat := by omega
    rw [ea, eb]; ring
  have bound : a.toNat * b.toNat < 18446744073709551616 * 18446744073709551616 :=
    Nat.mul_lt_mul'' la lb
  generalize hT : a.toNat * b.toNat = T at *
  clear n00 n01 n10 n11 na0 na1 nb0 nb1 hp00 hp01 hp10 hp11 ha0 ha1 hb0 hb1 la0 lb0 la1 lb1 la lb
  generalize hmid : p01 + p10 = mid
  generalize hmidc : (if mid < p01 then (1 : UInt64) else 0) = midc
  generalize hlo : p00 + (mid <<< 32) = lo
  generalize hloc : (if lo < p00 then (1 : UInt64) else 0) = loc
  generalize hhi : p11 + mid >>> 32 + midc <<< 32 + loc = hi
  generalize hhh : hi >>> 32 = hh
  generalize hhl : hi &&& VF.EPS = hl
  have nmid : mid.toNat = (p01.toNat + p10.toNat) % 18446744073709551616 := by rw [← hmid, toNat_add']
  have nmidc : midc.toNat = if mid.toNat < p01.toNat then 1 else 0 := by
    rw [← hmidc, ite_lt]
  have nlo : lo.toNat = (p00.toNat + mid.toNat * 4294967296 % 18446744073709551616) % 18446744073709551616 := by
    rw [← hlo, toNat_add', shl32]
  have nloc : loc.toNat = if lo.toNat < p00.toNat then 1 else 0 := by
    rw [← hloc, ite_lt]
  have nhi : hi.toNat = ((((p11.toNat + mid.toNat / 4294967296) % 18446744073709551616 +
      midc.toNat * 4294967296 % 18446744073709551616) % 18446744073709551616) + loc.toNat) % 18446744073709551616 := by
    rw [← hhi, toNat_add', toNat_add', toNat_add', shr32, shl32]
  have nhh : hh.toNat = hi.toNat / 4294967296 := by rw [← hhh, shr32]
  have nhl : hl.toNat = hi.toNat % 4294967296 := by rw [← hhl, and32]
  have lhl : hl.toNat < 4294967296 := by omega
  have hE := EPS_toNat
  have hP := P_toNat
  have lE : VF.EPS.toNat < 4294967296 := by omega
  have nt1 : (hl * VF.EPS).toNat = hl.toNat * 4294967295 := by rw [mulsmall _ _ lhl lE, hE]
  generalize ht1 : hl * VF.EPS = t1 at *
  generalize ht0 : (if lo < hh then lo - hh - VF.EPS else lo - hh) = t0
  have nt0 : t0.toNat = if lo.toNat < hh.toNat then lo.toNat + 18446744069414584321 - hh.toNat else lo.toNat - hh.toNat := by
    rw [← ht0]
    by_cases h : lo < hh
    · have h' := lt_iff'.mp h
      simp only [h, ite_true, h']
      rw [toNat_sub', toNat_sub']
      have := toNat_lt' lo; have := toNat_lt' hh
      omega
    · have h' : ¬ lo.toNat < hh.toNat := fun x => h (lt_iff'.mpr x)
      simp only [h, ite_false, h']
      rw [toNat_sub']
      have := toNat_lt' lo; have := toNat_lt' hh
      omega
  generalize hr0 : t0 + t1 = r0
  have nr0 : r0.toNat = (t0.toNat + t1.toNat) % 18446744073709551616 := by rw [← hr0, toNat_add']
  generalize hr1 : (if r0 < t0 then r0 + VF.EPS else r0) = r1
  have nr1 : r1.toNat = if r0.toNat < t0.toNat then (r0.toNat + 4294967295) % 18446744073709551616 else r0.toNat := by
    rw [← hr1]
    by_cases h : r0 < t0
    · simp only [h, ite_true, lt_iff'.mp h]; rw [toNat_add', hE]
    · have h' : ¬ r0.toNat < t0.toNat := fun x => h (lt_iff'.mpr x)
      simp only [h, ite_false, h']
  have fin : (if r1 ≥ VF.P then r1 - VF.P else r1).toNat = if VF.P.toNat ≤ r1.toNat then r1.toNat - VF.P.toNat else r1.toNat := by
    by_cases hc : r1 ≥ VF.P
    · have hc' := le_iff'.mp hc
      simp only [ge_iff_le, hc, hc', ite_true]
      rw [toNat_sub']; have := toNat_lt' r1; omega
    · have hc' : ¬ VF.P.toNat ≤ r1.toNat := fun x => hc (le_iff'.mpr x)
      simp only [ge_iff_le, hc, hc', ite_false]
  rw [fin, hP]
  have hTT := hi_aux T p00.toNat p01.toNat p10.toNat p11.toNat mid.toNat midc.toNat lo.toNat loc.toNat hi.toNat hab
    (toNat_lt' _) (toNat_lt' _) (toNat_lt' _) (toNat_lt' _) bound nmid nmidc nlo nloc nhi
  exact final_aux lo.toNat hi.toNat hh.toNat hl.toNat t0.toNat t1.toNat r0.toNat r1.toNat T hTT (toNat_lt' _) (toNat_lt' _)
    nhh nhl nt1 nt0 nr0 nr1

/-- the derived `BEq` of `VF.K3` is equality (the verifier's `lhs == zh * qsum` test reads as `=`) -/
theorem K3_beq_iff (x y : VF.K3) : (x == y) = true ↔ x = y := by
  obtain ⟨a0, a1, a2⟩ := x
  obtain ⟨b0, b1, b2⟩ := y
  simp [BEq.beq, VF.K3.mk.injEq]
  change (a0 == b0 && (a1 == b1 && a2 == b2)) = true ↔ _
  simp

/-! ### Into `Gold` / `K3` of `Exec/Field.lean` -/

def canon (a : UInt64) : Prop := a.toNat < p

theorem ofU64_vadd (a b : UInt64) (ha : canon a) (hb : canon b) :
    Gold.ofU64 (VF.add a b) = Gold.ofU64 a + Gold.ofU64 b := by
  apply Gold.toZ_injective
  rw [Gold.toZ_add, Gold.ofU64_toZ, Gold.ofU64_toZ, Gold.ofU64_toZ, add_toNat a b ha hb]
  rw [ZMod.natCast_mod, Nat.cast_add]

theorem ofU64_vsub (a b : UInt64) (ha : canon a) (hb : canon b) :
    Gold.ofU64 (VF.sub a b) = Gold.ofU64 a - Gold.ofU64 b := by
  apply Gold.toZ_injective
  rw [Gold.toZ_sub, Gold.ofU64_toZ, Gold.ofU64_toZ, Gold.ofU64_toZ, sub_toNat a b ha hb, ZMod.natCast_mod]
  have : ((a.toNat + p - b.toNat : ℕ) : ZMod p) = (a.toNat : ZMod p) + (p : ZMod p) - (b.toNat : ZMod p) := by
    rw [Nat.cast_sub (by have := hb; unfold canon at *; omega), Nat.cast_add]
  rw [this, ZMod.natCast_self]; ring

theorem ofU64_vneg (a : UInt64) (ha : canon a) : Gold.ofU64 (VF.neg a) = - Gold.ofU64 a := by
  apply Gold.toZ_injective
  rw [Gold.toZ_neg, Gold.ofU64_toZ, Gold.ofU64_toZ, neg_toNat a ha, ZMod.natCast_mod]
  rw [Nat.cast_sub (by unfold canon at ha; omega), ZMod.natCast_self]; ring

/-! ### The residue map `zv`, multiplication / power / inverse into `ZMod p`, and the cubic extension -/

/-- the residue of a raw limb in `ZMod p` -/
def zv (a : UInt64) : ZMod p := (a.toNat : ZMod p)

theorem mul_lt (a b : UInt64) : canon (VF.mul a b) := by
  unfold canon; rw [mul_toNat]; exact Nat.mod_lt _ Gold.p_pos

/-- `VF.mul` is multiplication of residues, for ARBITRARY limbs -/
theorem zv_mul (a b : UInt64) : zv (VF.mul a b) = zv a * zv b := by
  unfold zv; rw [mul_toNat, ZMod.natCast_mod, Nat.cast_mul]

theorem add_lt (a b : UInt64) (ha : canon a) (hb : canon b) : canon (VF.add a b) := by
  unfold canon at *; rw [add_toNat a b ha hb]; exact Nat.mod_lt _ Gold.p_pos
theorem sub_lt (a b : UInt64) (ha : canon a) (hb : canon b) : canon (VF.sub a b) := by
  unfold canon at *; rw [sub_toNat a b ha hb]; exact Nat.mod_lt _ Gold.p_pos
theorem neg_lt (a : UInt64) (ha : canon a) : canon (VF.neg a) := by
  unfold canon at *; rw [neg_toNat a ha]; exact Nat.mod_lt _ Gold.p_pos

theorem zv_add (a b : UInt64) (ha : canon a) (hb : canon b) : zv (VF.add a b) = zv a + zv b := by
  unfold zv; rw [add_toNat a b ha hb, ZMod.natCast_mod, Nat.cast_add]
theorem zv_sub (a b : UInt64) (ha : canon a) (hb : canon b) : zv (VF.sub a b) = zv a - zv b := by
  have := ofU64_vsub a b ha hb
  have h := congrArg Gold.toZ this
  rwa [Gold.toZ_sub, Gold.ofU64_toZ, Gold.ofU64_toZ, Gold.ofU64_toZ] at h
theorem zv_neg (a : UInt64) (ha : canon a) : zv (VF.neg a) = - zv a := by
  have h := congrArg Gold.toZ (ofU64_vneg a ha)
  rwa [Gold.toZ_neg, Gold.ofU64_toZ, Gold.ofU64_toZ] at h

theorem zv_zero : zv 0 = 0 := rfl
theorem zv_one : zv 1 = 1 := rfl
theorem zv_two : zv 2 = 2 := rfl
theorem zv_seven : zv VF.seven = 7 := rfl

/-- `VF.powAux` with fuel `f ≥ k` computes `r * b ^ k` (residues), for ARBITRARY limbs -/
theorem zv_powAux : ∀ (f : ℕ) (b : UInt64) (k : ℕ) (r : UInt64), k ≤ f →
    zv (VF.powAux f b k r) = zv r * zv b ^ k := by
  intro f
  induction f with
  | zero =>
    intro b k r hk
    have : k = 0 := by omega
    subst this; simp [VF.powAux]
  | succ f ih =>
    intro b k r hk
    unfold VF.powAux
    by_cases h0 : k = 0
    · subst h0; simp
    · have h0' : (k == 0) = false := by simpa using h0
      simp only [h0', Bool.false_eq_true, ite_false]
      have hk2 : k / 2 ≤ f := by omega
      have hn2 : k = 2 * (k / 2) + k % 2 := by omega
      by_cases hc : k % 2 = 1
      · have hc' : (k % 2 == 1) = true := by simpa using hc
        simp only [hc', ite_true]
        rw [ih _ _ _ hk2, zv_mul, zv_mul]
        conv_rhs => rw [hn2, hc]
        ring
      · have hc' : (k % 2 == 1) = false := by simpa using hc
        simp only [hc', Bool.false_eq_true, ite_false]
        rw [ih _ _ _ hk2, zv_mul]
        have : k % 2 = 0 := by omega
        conv_rhs => rw [hn2, this]
        ring

theorem zv_pow (a : UInt64) (e : ℕ) : zv (VF.pow a e) = zv a ^ e := by
  unfold VF.pow; rw [zv_powAux _ _ _ _ (by omega), zv_one, one_mul]

theorem zv_inv (a : UInt64) : zv (VF.inv a) = (zv a)⁻¹ := by
  unfold VF.inv
  have hPN : VF.PN = p := by rw [p_lit]; rfl
  rw [zv_pow, hPN]
  by_cases h : zv a = 0
  · rw [h, inv_zero, zero_pow]; rw [p_lit]; norm_num
  · have h1 : zv a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h
    have h2 : p - 1 = (p - 2) + 1 := by rw [p_lit]
    rw [h2, pow_succ] at h1
    exact (eq_inv_of_mul_eq_one_left h1)

/-! #### `VF.K3` into `KC` -/

open Polynomial in
/-- the value in `KC` of a verifier `K3` (limbs read as residues) -/
noncomputable def toKV (x : VF.K3) : KC :=
  algebraMap (ZMod p) KC (zv x.c0) + algebraMap (ZMod p) KC (zv x.c1) * xr +
    algebraMap (ZMod p) KC (zv x.c2) * xr ^ 2

/-- the residue map on the base-field values -/
noncomputable def psiV (g : UInt64) : KC := algebraMap (ZMod p) KC (zv g)

/-- the same element as an `Exec.K3` (reduced limbs) -/
def t3 (x : VF.K3) : Exec.K3 := ⟨Gold.ofU64 x.c0, Gold.ofU64 x.c1, Gold.ofU64 x.c2⟩

theorem toKV_eq_toK (x : VF.K3) : toKV x = Exec.K3.toK (t3 x) := by
  simp only [toKV, Exec.K3.toK, t3, Gold.ofU64_toZ, zv]

def canon3 (x : VF.K3) : Prop := canon x.c0 ∧ canon x.c1 ∧ canon x.c2

private theorem seven_map : algebraMap (ZMod p) KC (7 : ZMod p) = xr ^ 3 := by
  rw [xr_cube]

theorem zv_addMM (a b c d : UInt64) : zv (VF.add (VF.mul a b) (VF.mul c d)) = zv a * zv b + zv c * zv d := by
  rw [zv_add _ _ (mul_lt _ _) (mul_lt _ _), zv_mul, zv_mul]
theorem zv_addAM (a b c d e f : UInt64) :
    zv (VF.add (VF.add (VF.mul a b) (VF.mul c d)) (VF.mul e f)) = zv a * zv b + zv c * zv d + zv e * zv f := by
  rw [zv_add _ _ (add_lt _ _ (mul_lt _ _) (mul_lt _ _)) (mul_lt _ _), zv_addMM, zv_mul]
theorem zv_subMM (a b c d : UInt64) : zv (VF.sub (VF.mul a b) (VF.mul c d)) = zv a * zv b - zv c * zv d := by
  rw [zv_sub _ _ (mul_lt _ _) (mul_lt _ _), zv_mul, zv_mul]

theorem toKV_mul (x y : VF.K3) : toKV (VF.K3.mul x y) = toKV x * toKV y := by
  unfold VF.K3.mul toKV
  simp only [zv_addMM, zv_addAM, zv_mul, zv_seven, map_add, map_mul, seven_map]
  ring

theorem toKV_smul (s : UInt64) (x : VF.K3) : toKV (VF.K3.smul s x) = psiV s * toKV x := by
  unfold VF.K3.smul toKV psiV
  simp only [zv_mul, map_mul]; ring

theorem toKV_ofG (g : UInt64) : toKV (VF.K3.ofG g) = psiV g := by
  simp [VF.K3.ofG, toKV, psiV, zv_zero]

theorem toKV_zero : toKV VF.K3.zero = 0 := by
  simp [VF.K3.zero, toKV, zv_zero]

theorem toKV_one : toKV VF.K3.one = 1 := by
  simp [VF.K3.one, toKV, zv_zero]; rfl

theorem toKV_add (x y : VF.K3) (hx : canon3 x) (hy : canon3 y) : toKV (VF.K3.add x y) = toKV x + toKV y := by
  obtain ⟨a0, a1, a2⟩ := hx; obtain ⟨b0, b1, b2⟩ := hy
  unfold VF.K3.add toKV
  simp only [zv_add _ _ a0 b0, zv_add _ _ a1 b1, zv_add _ _ a2 b2, map_add]; ring

theorem toKV_sub (x y : VF.K3) (hx : canon3 x) (hy : canon3 y) : toKV (VF.K3.sub x y) = toKV x - toKV y := by
  obtain ⟨a0, a1, a2⟩ := hx; obtain ⟨b0, b1, b2⟩ := hy
  unfold VF.K3.sub toKV
  simp only [zv_sub _ _ a0 b0, zv_sub _ _ a1 b1, zv_sub _ _ a2 b2, map_sub]; ring

theorem toKV_neg (x : VF.K3) (hx : canon3 x) : toKV (VF.K3.neg x) = - toKV x := by
  obtain ⟨a0, a1, a2⟩ := hx
  unfold VF.K3.neg toKV
  simp only [zv_neg _ a0, zv_neg _ a1, zv_neg _ a2, map_neg]; ring

/-- `VF.K3.powAux` with fuel `f ≥ k` computes `r * b ^ k`, for ARBITRARY limbs (all adds sit on `mul` outputs) -/
theorem toKV_powAux : ∀ (f : ℕ) (b : VF.K3) (k : ℕ) (r : VF.K3), k ≤ f →
    toKV (VF.K3.powAux f b k r) = toKV r * toKV b ^ k := by
  intro f
  induction f with
  | zero =>
    intro b k r hk
    have : k = 0 := by omega
    subst this; simp [VF.K3.powAux]
  | succ f ih =>
    intro b k r hk
    unfold VF.K3.powAux
    by_cases h0 : k = 0
    · subst h0; simp
    · have h0' : (k == 0) = false := by simpa using h0
      simp only [h0', Bool.false_eq_true, ite_false]
      have hk2 : k / 2 ≤ f := by omega
      have hn2 : k = 2 * (k / 2) + k % 2 := by omega
      by_cases hc : k % 2 = 1
      · have hc' : (k % 2 == 1) = true := by simpa using hc
        simp only [hc', ite_true]
        rw [ih _ _ _ hk2, toKV_mul, toKV_mul]
        conv_rhs => rw [hn2, hc]
        ring
      · have hc' : (k % 2 == 1) = false := by simpa using hc
        simp only [hc', Bool.false_eq_true, ite_false]
        rw [ih _ _ _ hk2, toKV_mul]
        have : k % 2 = 0 := by omega
        conv_rhs => rw [hn2, this]
        ring

theorem toKV_pow (x : VF.K3) (e : ℕ) : toKV (VF.K3.pow x e) = toKV x ^ e := by
  unfold VF.K3.pow; rw [toKV_powAux _ _ _ _ (by omega), toKV_one, one_mul]

theorem toKV_adj (x : VF.K3) : toKV (VF.K3.adj x) = Exec.K3.toK (Exec.K3.adj (t3 x)) := by
  unfold VF.K3.adj Exec.K3.adj toKV Exec.K3.toK t3
  simp only [zv_subMM, zv_mul, zv_seven]
  simp only [Gold.toZ_sub, Gold.toZ_mul, Gold.ofU64_toZ, Gold.toZ_seven, zv, map_sub, map_mul]

theorem zv_norm (x : VF.K3) : zv (VF.K3.norm x) = (Exec.K3.norm (t3 x)).toZ := by
  unfold VF.K3.norm Exec.K3.norm VF.K3.adj Exec.K3.adj t3
  simp only [zv_addMM, zv_subMM, zv_mul, zv_seven]
  simp only [Gold.toZ_add, Gold.toZ_sub, Gold.toZ_mul, Gold.ofU64_toZ, Gold.toZ_seven, zv]

/-- the executable inverse (including `0⁻¹ = 0`) is the field inverse, for ARBITRARY limbs -/
theorem toKV_inv (x : VF.K3) : toKV (VF.K3.inv x) = (toKV x)⁻¹ := by
  have h1 : toKV (VF.K3.inv x) = psiV (VF.inv (VF.K3.norm x)) * toKV (VF.K3.adj x) := by
    unfold VF.K3.inv; rw [toKV_smul]
  rw [h1, toKV_adj, toKV_eq_toK x, ← Exec.K3.toK_inv]
  unfold psiV
  rw [zv_inv, zv_norm]
  show _ = Exec.K3.toK (Exec.K3.smul (Exec.K3.norm (t3 x))⁻¹ (Exec.K3.adj (t3 x)))
  rw [Exec.K3.toK_smul, Gold.toZ_inv]


/-! #### canonical limbs are closed under the verifier's `K3` operations -/

theorem canon3_zero : canon3 VF.K3.zero := ⟨Gold.zero_lt, Gold.zero_lt, Gold.zero_lt⟩
theorem canon3_one : canon3 VF.K3.one := ⟨Gold.one_lt, Gold.zero_lt, Gold.zero_lt⟩
theorem canon3_ofG (g : UInt64) (h : canon g) : canon3 (VF.K3.ofG g) := ⟨h, Gold.zero_lt, Gold.zero_lt⟩
theorem canon3_add (x y : VF.K3) (hx : canon3 x) (hy : canon3 y) : canon3 (VF.K3.add x y) :=
  ⟨add_lt _ _ hx.1 hy.1, add_lt _ _ hx.2.1 hy.2.1, add_lt _ _ hx.2.2 hy.2.2⟩
theorem canon3_sub (x y : VF.K3) (hx : canon3 x) (hy : canon3 y) : canon3 (VF.K3.sub x y) :=
  ⟨sub_lt _ _ hx.1 hy.1, sub_lt _ _ hx.2.1 hy.2.1, sub_lt _ _ hx.2.2 hy.2.2⟩
theorem canon3_neg (x : VF.K3) (hx : canon3 x) : canon3 (VF.K3.neg x) :=
  ⟨neg_lt _ hx.1, neg_lt _ hx.2.1, neg_lt _ hx.2.2⟩
theorem canon3_smul (s : UInt64) (x : VF.K3) : canon3 (VF.K3.smul s x) := ⟨mul_lt _ _, mul_lt _ _, mul_lt _ _⟩
theorem canon_addMM (a b c d : UInt64) : canon (VF.add (VF.mul a b) (VF.mul c d)) :=
  add_lt _ _ (mul_lt _ _) (mul_lt _ _)
theorem canon_addAM (a b c d e f : UInt64) : canon (VF.add (VF.add (VF.mul a b) (VF.mul c d)) (VF.mul e f)) :=
  add_lt _ _ (canon_addMM a b c d) (mul_lt _ _)
theorem canon3_mul (x y : VF.K3) : canon3 (VF.K3.mul x y) := by
  unfold canon3 VF.K3.mul
  simp only []
  exact ⟨canon_addMM _ _ _ _, canon_addAM _ _ _ _ _ _, canon_addAM _ _ _ _ _ _⟩
theorem canon3_powAux : ∀ (f : ℕ) (b : VF.K3) (k : ℕ) (r : VF.K3), canon3 r → canon3 (VF.K3.powAux f b k r) := by
  intro f
  induction f with
  | zero => intro b k r hr; simpa [VF.K3.powAux] using hr
  | succ f ih =>
    intro b k r hr
    unfold VF.K3.powAux
    by_cases h0 : (k == 0) = true
    · simpa [h0] using hr
    · simp only [h0, Bool.false_eq_true, ite_false]
      apply ih
      split
      · exact canon3_mul _ _
      · exact hr
theorem canon3_pow (x : VF.K3) (e : ℕ) : canon3 (VF.K3.pow x e) := canon3_powAux _ _ _ _ canon3_one
theorem canon3_inv (x : VF.K3) : canon3 (VF.K3.inv x) := canon3_smul _ _

theorem psiV_mul (a b : UInt64) : psiV (VF.mul a b) = psiV a * psiV b := by
  unfold psiV; rw [zv_mul, map_mul]
theorem psiV_pow (a : UInt64) (e : ℕ) : psiV (VF.pow a e) = psiV a ^ e := by
  unfold psiV; rw [zv_pow, map_pow]
theorem psiV_inv (a : UInt64) : psiV (VF.inv a) = (psiV a)⁻¹ := by
  unfold psiV; rw [zv_inv, map_inv₀]
theorem psiV_two : psiV 2 = 2 := by
  unfold psiV; rw [zv_two]; exact map_ofNat (algebraMap (ZMod p) KC) 2

end NockvmE2E.Exec.VL
