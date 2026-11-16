/-
  Nock/TraceGenExe/K6.lean

  **Executable 𝕂′ = Quad δ over 𝕂.**

  `δ = 7 ∈ F_p` (the same `7` as the cubic `X^3 - 7`).  `7` is a non-square in `ZMod p`
  (`7^((p-1)/2) ≠ 1`, kernel-evaluated through `Gold.pow`), hence a non-square in the cubic extension
  `KC` (`T0Tower.nonsquare_lift`, odd degree), so `Fact (¬ IsSquare (algebraMap (ZMod p) KC 7))` holds and
  `Quad (algebraMap (ZMod p) KC 7)` is exactly the `𝕂′` of the honest theorems at
  `F := ZMod p`, `K := KC`, `δF := 7`.  `K6` is a pair of `K3` (`re + im·√δ`), six limbs.
-/
import Nock.TraceGenExe.K3

set_option autoImplicit false

namespace Nock.TraceGenExe

open Nock.Field Nock.NockVMROM.Thm54.T0Tower

/-- The chosen base non-square `δ = 7 ∈ F_p`. -/
def deltaF : ZMod p := 7

theorem deltaF_ne_zero : deltaF ≠ 0 := by
  intro h0
  have := congrArg ZMod.val h0
  unfold deltaF at this
  rw [ZMod.val_zero, ZMod.val_ofNat_of_lt (by rw [p_eq]; norm_num)] at this
  omega

theorem KC_char_ne_two : ringChar KC ≠ 2 := by
  rw [← Algebra.ringChar_eq (ZMod p) KC, ZMod.ringChar_zmod_n, p_eq]; norm_num

/-- **`δ = 7` is a non-square in `𝕂`.** -/
theorem delta_nonsquare_KC : ¬ IsSquare (algebraMap (ZMod p) KC deltaF) :=
  nonsquare_lift (F := ZMod p) (K := KC)
    (by rw [ZMod.ringChar_zmod_n, p_eq]; norm_num) KC_char_ne_two KC_finrank deltaF
    deltaF_ne_zero seven_not_square

instance deltaFact : Fact (¬ IsSquare (algebraMap (ZMod p) KC deltaF)) := ⟨delta_nonsquare_KC⟩

noncomputable instance : DecidableEq (Quad (algebraMap (ZMod p) KC deltaF)) := Classical.decEq _

/-- **The concrete 𝕂′**. -/
abbrev KQ : Type := Quad (algebraMap (ZMod p) KC deltaF)

/-- `re + im · √δ`, six limbs. -/
structure K6 where
  re : K3
  im : K3

namespace K6

/-- The embedded `δ` as an element of `K3`. -/
def dK : K3 := ⟨Gold.seven, 0, 0⟩

theorem toK_dK : K3.toK dK = algebraMap (ZMod p) KC deltaF := by
  simp [K3.toK, dK, Gold.toZ_seven, Gold.toZ_zero, deltaF]

/-- `δ · x`. -/
def mulD (x : K3) : K3 := K3.smul Gold.seven x

theorem toK_mulD (x : K3) : K3.toK (mulD x) = algebraMap (ZMod p) KC deltaF * K3.toK x := by
  unfold mulD; rw [K3.toK_smul, Gold.toZ_seven]; rfl

def zero : K6 := ⟨0, 0⟩
def one : K6 := ⟨1, 0⟩
instance : Zero K6 := ⟨zero⟩
instance : One K6 := ⟨one⟩
def add (a b : K6) : K6 := ⟨a.re + b.re, a.im + b.im⟩
def sub (a b : K6) : K6 := ⟨a.re - b.re, a.im - b.im⟩
def neg (a : K6) : K6 := ⟨-a.re, -a.im⟩
def mul (a b : K6) : K6 :=
  ⟨a.re * b.re + mulD (a.im * b.im), a.re * b.im + a.im * b.re⟩
def conjN (a : K6) : K3 := a.re * a.re - mulD (a.im * a.im)
def inv (a : K6) : K6 := let n := (conjN a)⁻¹; ⟨a.re * n, -(a.im * n)⟩

instance : Add K6 := ⟨add⟩
instance : Sub K6 := ⟨sub⟩
instance : Neg K6 := ⟨neg⟩
instance : Mul K6 := ⟨mul⟩
instance : Inv K6 := ⟨inv⟩

/-- The semantic value in `𝕂′`. -/
noncomputable def toQ (a : K6) : KQ := Quad.mk _ (K3.toK a.re) (K3.toK a.im)

theorem toQ_zero : toQ 0 = 0 := by
  show toQ zero = 0
  simp [toQ, zero, K3.toK_zero, Quad.mk_zero'] <;> rfl

theorem toQ_one : toQ 1 = 1 := by
  show toQ one = 1
  simp [toQ, one, K3.toK_one, K3.toK_zero, Quad.mk_one'] <;> rfl

theorem toQ_add (a b : K6) : toQ (a + b) = toQ a + toQ b := by
  show toQ (add a b) = _
  simp only [toQ, add, K3.toK_add, Quad.mk_add]

theorem toQ_sub (a b : K6) : toQ (a - b) = toQ a - toQ b := by
  show toQ (sub a b) = _
  simp only [toQ, sub, K3.toK_sub, Quad.mk_sub]

theorem toQ_neg (a : K6) : toQ (-a) = -toQ a := by
  show toQ (neg a) = _
  have h := Quad.mk_sub (algebraMap (ZMod p) KC deltaF) 0 0 (K3.toK a.re) (K3.toK a.im)
  rw [Quad.mk_zero', zero_sub, zero_sub, zero_sub] at h
  simp only [toQ, neg, K3.toK_neg]
  exact h.symm

theorem toQ_mul (a b : K6) : toQ (a * b) = toQ a * toQ b := by
  show toQ (mul a b) = _
  simp only [toQ, mul, K3.toK_add, K3.toK_mul, toK_mulD, Quad.mk_mul]

theorem toQ_eq_zero_iff (a : K6) : toQ a = 0 ↔ K3.toK a.re = 0 ∧ K3.toK a.im = 0 :=
  Quad.mk_eq_zero_iff _ _ _

/-- **The executable inverse is the field inverse of `𝕂′`** (including `0⁻¹ = 0`). -/
theorem toQ_inv (a : K6) : toQ (a⁻¹) = (toQ a)⁻¹ := by
  show toQ (inv a) = _
  by_cases h : K3.toK a.re = 0 ∧ K3.toK a.im = 0
  · have h0 : toQ a = 0 := (toQ_eq_zero_iff a).mpr h
    rw [h0, inv_zero]
    unfold inv
    simp only [toQ, K3.toK_mul, K3.toK_neg, h.1, h.2, zero_mul, neg_zero, Quad.mk_zero']
  · unfold toQ
    rw [Quad.mk_inv _ _ _ h]
    unfold inv
    simp only [K3.toK_mul, K3.toK_neg, K3.toK_inv, conjN, K3.toK_sub, K3.toK_mul, toK_mulD, div_eq_mul_inv,
      neg_mul]

end K6

end Nock.TraceGenExe
