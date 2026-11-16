/-
  Nock/RedTeam/Batch577Thm54FormRCompleteness.lean

  **Form R completeness at the `MTree` level.**

  C1. `ReadVerifyNested` + unique exponents + honest certificates
      (`m = |bits|`, `c` the relative path) imply `formRCounts = 0` and
      `formRPw = 0`.  Nested/RVN is a *completeness premise* here (C1), not
      an S2 soundness premise.
  C2.
-/
import Nock.AxisBatching
import Nock.AxisBridge
import Nock.RedTeam.Batch554Thm54PwFunctional
import Nock.RedTeam.Batch575Thm54FormRMtree
import Nock.RedTeam.Batch576Thm54FormRNegatives

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch577

open Nock
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.RedTeam.Batch554 (vpaths rpaths bitsOf bitsOf_length)
open Nock.RedTeam.Batch575
open Nock.RedTeam.Batch576
open Polynomial

variable {K : Type*} [Field K]

/-! ## Path certificates for `/[2]` and `/[3]` -/

def leftBit : ℕ → Bool := fun _ => false

theorem leftBit_bitsOf : bitsOf 1 leftBit = [false] := by
  decide

theorem leftBit_padding (n : ℕ) (_hn : 1 ≤ n) : Padding n 1 leftBit := by
  intro j hj hjn
  rfl

def rightBit : ℕ → Bool := fun j => decide (j = 1)

theorem rightBit_bitsOf : bitsOf 1 rightBit = [true] := by
  decide

theorem rightBit_padding (n : ℕ) (_hn : 1 ≤ n) : Padding n 1 rightBit := by
  intro j hj hjn
  simp [rightBit]
  omega

/-! ## C1 — single honest record (`read` at the root, verify at the left child) -/

def c1Tree (e : ℕ) (a : K) : MTree K :=
  .read e (.decompose (.verify e a .halt) .halt)

theorem c1_rvn (e : ℕ) (a : K) :
    AxisBridge.ReadVerifyNested (c1Tree e a) := by
  simp [c1Tree, AxisBridge.ReadVerifyNested, verifyCount]

theorem c1_unique (e : ℕ) (a : K) : UniqueExponents (c1Tree e a) := by
  intro e'
  constructor <;> simp [c1Tree, readCount, verifyCount] <;> split_ifs <;> simp

theorem c1_vpaths (e : ℕ) (a : K) : vpaths e (c1Tree e a) = [[false]] := by
  simp [c1Tree, vpaths]

theorem c1_rpaths (e : ℕ) (a : K) : rpaths e (c1Tree e a) = [[]] := by
  simp [c1Tree, rpaths]

theorem c1_read_eq (e e' : ℕ) (a : K) :
    readCount e' (c1Tree e a) = if e = e' then 1 else 0 := by
  simp [c1Tree, readCount]

theorem c1_verify_eq (e e' : ℕ) (a : K) :
    verifyCount e' (c1Tree e a) = if e = e' then 1 else 0 := by
  simp [c1Tree, verifyCount]

/-- **C1.** Honest `/[2]` certificate (`m = 1`, `c_1 = false`) is exact, and the
tree is `ReadVerifyNested`. -/
theorem c1_honest (n e : ℕ) (a : K) (hn : 2 ≤ n) :
    AxisBridge.ReadVerifyNested (c1Tree e a)
    ∧ formRCounts n (fun _ => 1) (fun _ => leftBit) (c1Tree e a) = 0
    ∧ formRPw n (fun _ => 1) (c1Tree e a) = 0 := by
  refine ⟨c1_rvn e a, ?_, ?_⟩
  · refine (formR_counts_zero_iff n (fun _ => 1) (fun _ => leftBit)
        (c1Tree e a) (c1_unique e a) (fun _ => by omega)).mpr ?_
    constructor
    · intro e'
      rw [c1_read_eq, c1_verify_eq]
    · intro e' ⟨hr, _hv⟩
      have heq : e' = e := by
        rw [c1_read_eq] at hr
        by_cases h : e = e'
        · exact h.symm
        · simp [h] at hr
      refine ⟨leftBit_padding n (by omega), [], ?_, ?_⟩
      · rw [heq]; exact c1_rpaths e a
      · rw [heq, c1_vpaths, leftBit_bitsOf]; rfl
  · simp only [c1Tree, formRPw, Tpoly, scale, Y, pow_one, add_zero, zero_add]
    rw [← mul_assoc, ← C_mul, mul_comm (X : Polynomial K) (X ^ (n - 1))]
    simp


/-- Left child holds an honest `/[2]` record; right child holds an honest `/[3]`. -/
def twoReadForest (e₁ e₂ : ℕ) (a₁ a₂ : K) : MTree K :=
  .decompose
    (.read e₁ (.decompose (.verify e₁ a₁ .halt) .halt))
    (.read e₂ (.decompose .halt (.verify e₂ a₂ .halt)))

def twoRead_m (_ : ℕ) : ℕ := 1
def twoRead_c (e₁ : ℕ) : ℕ → ℕ → Bool :=
  fun e => if e = e₁ then leftBit else rightBit

theorem twoRead_unique (e₁ e₂ : ℕ) (a₁ a₂ : K) (hne : e₁ ≠ e₂) :
    UniqueExponents (twoReadForest e₁ e₂ a₁ a₂) := by
  intro e
  constructor
  · simp [twoReadForest, readCount]
    by_cases h1 : e₁ = e
    · by_cases h2 : e₂ = e
      · exact absurd (h1.trans h2.symm) hne
      · simp [h1, h2]
    · by_cases h2 : e₂ = e
      · simp [h1, h2]
      · simp [h1, h2]
  · simp [twoReadForest, verifyCount]
    by_cases h1 : e₁ = e
    · by_cases h2 : e₂ = e
      · exact absurd (h1.trans h2.symm) hne
      · simp [h1, h2]
    · by_cases h2 : e₂ = e
      · simp [h1, h2]
      · simp [h1, h2]

theorem twoRead_rpaths_left (e₁ e₂ : ℕ) (a₁ a₂ : K) (hne : e₁ ≠ e₂) :
    rpaths e₁ (twoReadForest e₁ e₂ a₁ a₂) = [[false]] := by
  simp [twoReadForest, rpaths, Ne.symm hne]

theorem twoRead_vpaths_left (e₁ e₂ : ℕ) (a₁ a₂ : K) (hne : e₁ ≠ e₂) :
    vpaths e₁ (twoReadForest e₁ e₂ a₁ a₂) = [[false, false]] := by
  simp [twoReadForest, vpaths, Ne.symm hne]

theorem twoRead_rpaths_right (e₁ e₂ : ℕ) (a₁ a₂ : K) (hne : e₁ ≠ e₂) :
    rpaths e₂ (twoReadForest e₁ e₂ a₁ a₂) = [[true]] := by
  simp [twoReadForest, rpaths, hne, Ne.symm hne]

theorem twoRead_vpaths_right (e₁ e₂ : ℕ) (a₁ a₂ : K) (hne : e₁ ≠ e₂) :
    vpaths e₂ (twoReadForest e₁ e₂ a₁ a₂) = [[true, true]] := by
  simp [twoReadForest, vpaths, hne, Ne.symm hne]

theorem twoRead_read_eq (e₁ e₂ e : ℕ) (a₁ a₂ : K) :
    readCount e (twoReadForest e₁ e₂ a₁ a₂)
      = (if e₁ = e then 1 else 0) + if e₂ = e then 1 else 0 := by
  simp [twoReadForest, readCount]

theorem twoRead_verify_eq (e₁ e₂ e : ℕ) (a₁ a₂ : K) :
    verifyCount e (twoReadForest e₁ e₂ a₁ a₂)
      = (if e₁ = e then 1 else 0) + if e₂ = e then 1 else 0 := by
  simp [twoReadForest, verifyCount]

/-- **C2.** The two-read forest with honest path certificates is exact. -/
theorem c2_two_read (n e₁ e₂ : ℕ) (a₁ a₂ : K) (hne : e₁ ≠ e₂) (hn : 2 ≤ n) :
    formRCounts n twoRead_m (twoRead_c e₁) (twoReadForest e₁ e₂ a₁ a₂) = 0 := by
  have hU := twoRead_unique e₁ e₂ a₁ a₂ hne
  have hm : ∀ e, twoRead_m e ≤ n - 1 := fun _ => by simp [twoRead_m]; omega
  refine (formR_counts_zero_iff n twoRead_m (twoRead_c e₁)
      (twoReadForest e₁ e₂ a₁ a₂) hU hm).mpr ?_
  constructor
  · intro e
    rw [twoRead_read_eq, twoRead_verify_eq]
  · intro e ⟨hr, _hv⟩
    by_cases h1 : e₁ = e
    · rw [h1]
      have hne' : e ≠ e₂ := fun h => hne (h1.trans h)
      refine ⟨by simpa [twoRead_m, twoRead_c] using leftBit_padding n (by omega),
        [false], twoRead_rpaths_left e e₂ a₁ a₂ hne', ?_⟩
      rw [twoRead_vpaths_left e e₂ a₁ a₂ hne']
      simp [twoRead_c, twoRead_m, leftBit_bitsOf]
    · have h2 : e₂ = e := by
        rw [twoRead_read_eq] at hr
        by_cases h : e₂ = e
        · exact h
        · simp [h1, h] at hr
      rw [h2]
      have hne' : e₁ ≠ e := fun h => hne (h.trans h2.symm)
      have hne'' : e ≠ e₁ := Ne.symm hne'
      refine ⟨by simpa [twoRead_m, twoRead_c, hne''] using
          rightBit_padding n (by omega),
        [true], twoRead_rpaths_right e₁ e a₁ a₂ hne', ?_⟩
      rw [twoRead_vpaths_right e₁ e a₁ a₂ hne']
      simp [twoRead_c, twoRead_m, hne'', rightBit_bitsOf]

/-- **C2 companion.** -/
theorem c2_crossing_beside (n e : ℕ) :
    (formRCounts n (fun _ => 0) (fun _ => fun _ => false)
      (crossingTree e (2 : K))).coeff e ≠ 0 :=
  n1_crossing_rejected n e (2 : K) 0 (fun _ => false) (Nat.zero_le _)


end Nock.RedTeam.Batch577

#print axioms Nock.RedTeam.Batch577.c1_honest
#print axioms Nock.RedTeam.Batch577.c2_two_read
#print axioms Nock.RedTeam.Batch577.c2_crossing_beside
