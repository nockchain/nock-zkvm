/-
  Nock/RedTeam/Batch862Thm54ReviewU1Sound.lean

  Notes only; no production edit.

  `Batch806.formR_cert_lt_p` assumes the row's columns ARE the bits of some `a`.  The adversary
  does not owe us that shape, so this file closes the gap: from acceptance alone (all 97 gates),
  at every `25 ≤ p < 2^64`,

  * `accepted_shift_le`: the decoded 6-bit shift is `≤ n − 1` (no shift `> n − 1`);
  * `accepted_junk_zero`: every certificate column `j ≥ n − 1` is `0` (no junk above `n − 1`);
  * `accepted_bits_boolean`: every column `j < n − 1` is `0`/`1`;
  * `accepted_top_lt_p`: on a shift-`(n−1)` row, the MSB-first integer `horner` of the record-visible
    columns (implicit leading `1`) is `< p` (no certificate `≥ p`).

  The constructed `a` is `horner b (n−1)`, so `Batch806.formR_cert_lt_p` applies to EVERY accepted
  row, not only to rows built from an `a`.  Instances at `p = 31`, `769` and Goldilocks follow.
  `formR_cert_lt_p_zero`: the `0 < a` premise is harmless — the columns of `a = 0` are those of `a = 1`.
-/
import Nock.RedTeam.Batch806Thm54FormRRepairSound
import Nock.RedTeam.Batch784Thm54FormRAliasesSurviveU1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Nock.RedTeam.Batch862

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.CoordinateCompiler

/-- MSB-first integer with implicit leading `1`: `horner b k = 2^k + Σ_{i<k} b_i 2^{k−1−i}`. -/
def horner (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 * horner b k + (if b k then 1 else 0)

theorem horner_bounds (b : ℕ → Bool) (k : ℕ) : 2 ^ k ≤ horner b k ∧ horner b k < 2 ^ (k + 1) := by
  induction k with
  | zero => simp [horner]
  | succ k ih =>
      simp only [horner, pow_succ]
      split_ifs <;> omega

theorem horner_testBit (b : ℕ → Bool) (k : ℕ) :
    ∀ i, i < k → (horner b k).testBit i = b (k - 1 - i) := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
      intro i hi
      cases i with
      | zero =>
          rw [Nat.testBit_zero]
          simp only [horner, Nat.add_sub_cancel, Nat.sub_zero]
          rcases Bool.eq_false_or_eq_true (b k) with hb | hb <;> simp [hb]
      | succ i =>
          rw [Nat.testBit_succ]
          have hdiv : (2 * horner b k + (if b k then 1 else 0)) / 2 = horner b k := by
            split_ifs <;> omega
          simp only [horner, hdiv]
          rw [ih i (by omega)]
          congr 1
          omega

theorem horner_size (b : ℕ → Bool) (k : ℕ) : Nat.size (horner b k) = k + 1 := by
  obtain ⟨h1, h2⟩ := horner_bounds b k
  exact le_antisymm (Nat.size_le.mpr h2) (Nat.lt_size.mpr h1)

section Generic

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F]

/-- The column-`j` booleanity/pin gate of the deployed `booleanGates`. -/
theorem boolGate_mem (j : ℕ) (hj : j < 63) :
    (if formRN F - 1 < j + 1 then colC (F := F) j else bbool (colC j)) ∈
      formRCertificateGates (F := F) := by
  simp only [formRCertificateGates, booleanGates, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨j, hj, rfl⟩))))

theorem shiftGate_mem (k : ℕ) (hk : k < 6) : bbool (colM (F := F) k) ∈ formRCertificateGates (F := F) := by
  simp only [formRCertificateGates, booleanGates, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk, rfl⟩))))

variable (env : Env F) (hacc : ∀ g ∈ formRCertificateGates (F := F), g.eval env = 0)
include hacc

/-- **C2 at acceptance:** no junk above `n − 1`. -/
theorem accepted_junk_zero (j : ℕ) (hj : j < 63) (hjn : formRN F - 1 ≤ j) :
    env.trace (col0 + j) = 0 := by
  have h := hacc _ (boolGate_mem j hj)
  rw [if_pos (by omega)] at h
  simpa [colC, bcur, CoeffExpr.eval] using h

/-- Record-visible columns are boolean at acceptance (the C2-stable shape `Batch823` needs). -/
theorem accepted_bits_boolean (j : ℕ) (hj : j < 63) :
    env.trace (col0 + j) = 0 ∨ env.trace (col0 + j) = 1 := by
  have h := hacc _ (boolGate_mem j hj)
  split_ifs at h
  · left; simpa [colC, bcur, CoeffExpr.eval] using h
  · simp only [bbool, colC, bcur, CoeffExpr.eval] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)

/-- **U1 at acceptance:** no shift `> n − 1`. -/
theorem accepted_shift_le : Nock.RedTeam.Batch782.rowShift env ≤ formRN F - 1 := by
  have hmem : ∀ g, g ∈ booleanGates (F := F) ++ powerPins ++ formRPins ++ helperPins ++
      formRNamed → g ∈ formRCertificateGates (F := F) := fun g hg => by
    simpa [formRCertificateGates] using hg
  exact Batch806.shift_le_formRN_pred env (fun k hk => hacc _ (shiftGate_mem k hk))
    (hacc _ (hmem _ (by simp [formRPins]))) (hacc _ (hmem _ (by simp [formRPins])))
    (hacc _ (hmem _ (by simp [formRNamed])))

/-- **C1 at acceptance, from acceptance alone:** on a shift-`(n−1)` row the record-visible
integer is `< p`.  No assumption that the columns come from an `a`. -/
theorem accepted_top_lt_p (hp25 : 25 ≤ ringChar F) (hp64 : ringChar F < 2 ^ 64)
    (hm : Nock.RedTeam.Batch782.rowShift env = formRN F - 1) :
    horner (fun j => decide (env.trace (col0 + j) = 1)) (formRN F - 1) < ringChar F := by
  have hn64 : formRN F ≤ 64 := by unfold formRN; exact Nat.size_le.mpr hp64
  have hn5 : 5 ≤ formRN F := by
    unfold formRN; exact (Nat.lt_size).mpr (le_trans (by norm_num) hp25)
  set b : ℕ → Bool := fun j => decide (env.trace (col0 + j) = 1) with hbdef
  set a := horner b (formRN F - 1) with hadef
  have hsz : Nat.size a = formRN F := by rw [hadef, horner_size]; omega
  have hsh : certShift a = formRN F - 1 := by simp [certShift, hsz]
  obtain ⟨hlo, hhi⟩ := horner_bounds b (formRN F - 1)
  have ha0 : 0 < a := lt_of_lt_of_le (Nat.two_pow_pos _) hlo
  have ha64 : a < 2 ^ 64 :=
    lt_of_lt_of_le hhi (Nat.pow_le_pow_right (by decide) (by omega))
  refine Batch806.formR_cert_lt_p env a hp25 hp64 ha0 ha64 (fun j hj => ?_) (fun k hk => ?_) hacc
  · unfold certCBit
    rw [hsh]
    by_cases hjn : j < formRN F - 1
    · rw [if_pos hjn, hadef, horner_testBit b _ _ (by omega)]
      have hidx : formRN F - 1 - 1 - (formRN F - 1 - 1 - j) = j := by omega
      rw [hidx]
      rcases accepted_bits_boolean env hacc j hj with h | h
      · simp [hbdef, h, bit01]
      · simp [hbdef, h, bit01]
    · rw [if_neg hjn, accepted_junk_zero env hacc j hj (by omega)]; rfl
  · obtain ⟨_, hR⟩ := Nock.RedTeam.Batch782.shift_cols_of_boolean env
      (fun k hk => hacc _ (shiftGate_mem k hk))
    rw [hR k hk, hm, hsh]

end Generic

/-- `0 < a` in `Batch806.formR_cert_lt_p` is harmless: `a = 0` writes the columns of `a = 1`
(shift `0`, no bits), whose value `1` is `< p` anyway. -/
theorem formR_cert_lt_p_zero : certShift 0 = certShift 1 ∧ ∀ j, certCBit 0 j = certCBit 1 j := by
  refine ⟨by decide, fun j => ?_⟩
  simp [certCBit, certShift]

/-! ## Instances: `p = 31`, `769`, Goldilocks -/

attribute [local instance] Classical.propDecidable

theorem at31 (env : Env Batch781.F31)
    (hacc : ∀ g ∈ formRCertificateGates (F := Batch781.F31), g.eval env = 0)
    (hm : Nock.RedTeam.Batch782.rowShift env = 4) :
    horner (fun j => decide (env.trace (col0 + j) = 1)) 4 < 31 := by
  have h := accepted_top_lt_p env hacc (by rw [Batch781.ringChar_31]; norm_num)
    (by rw [Batch781.ringChar_31]; norm_num) (by rw [hm, Batch781.formRN_31])
  rw [Batch781.formRN_31, Batch781.ringChar_31, show (5 : ℕ) - 1 = 4 from rfl] at h; convert h

theorem at769 (env : Env Batch781.F769)
    (hacc : ∀ g ∈ formRCertificateGates (F := Batch781.F769), g.eval env = 0)
    (hm : Nock.RedTeam.Batch782.rowShift env = 9) :
    horner (fun j => decide (env.trace (col0 + j) = 1)) 9 < 769 := by
  have h := accepted_top_lt_p env hacc (by rw [Batch781.ringChar_769]; norm_num)
    (by rw [Batch781.ringChar_769]; norm_num) (by rw [hm, Batch781.formRN_769])
  rw [Batch781.formRN_769, Batch781.ringChar_769, show (10 : ℕ) - 1 = 9 from rfl] at h; convert h

theorem atGoldilocks (env : Env Batch784.GF)
    (hacc : ∀ g ∈ formRCertificateGates (F := Batch784.GF), g.eval env = 0)
    (hm : Nock.RedTeam.Batch782.rowShift env = 63) :
    horner (fun j => decide (env.trace (col0 + j) = 1)) 63 < Nock.Field.p := by
  have h := accepted_top_lt_p env hacc (by rw [Batch784.ringChar_GF]; unfold Nock.Field.p; norm_num)
    (by rw [Batch784.ringChar_GF]; unfold Nock.Field.p; norm_num) (by rw [hm, Batch784.formRN_GF])
  rw [Batch784.formRN_GF, Batch784.ringChar_GF, show (64 : ℕ) - 1 = 63 from rfl] at h; convert h

end Nock.RedTeam.Batch862

#print axioms Nock.RedTeam.Batch862.accepted_top_lt_p
#print axioms Nock.RedTeam.Batch862.accepted_junk_zero
#print axioms Nock.RedTeam.Batch862.atGoldilocks
