/-
  Nock/RedTeam/Batch808Thm54FormRRepairComplete.lean

  **U1+C1+C2 honest completeness at the repaired gates, lane `u1-formr-repair`.**
  The generic statement is `canonical_formR99` (`OptimizedComputeCanonicalSatisfaction`), which
  builds at this move; these are the two concrete width receipts through `Batch781`'s builder, on
  the hardest honest rows (`top = 1`, shift `n − 1`, where the realigned comparison is consulted):

  * `honest_768_at_769`: `p = 769`, leaf `768 = p − 1` (shift `9 = n − 1`), all 97 gates vanish;
  * `honest_pred_at_goldilocks`: Goldilocks, leaf `p − 1` (shift `63`), all 97 gates vanish.
-/
import Nock.RedTeam.Batch784Thm54FormRAliasesSurviveU1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch808

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.RedTeam.Batch781
open Nock.RedTeam.Batch784

section At769

theorem size_768 : Nat.size 768 = 10 :=
  le_antisymm (Nat.size_le.mpr (by norm_num)) (Nat.lt_size.mpr (by norm_num))
theorem certShift_768 : certShift 768 = 9 := by simp [certShift, size_768]

/-- The honest row of the leaf `768 = p − 1` at `p = 769`. -/
noncomputable def row768 : Env F769 :=
  rowEnv ((768 : ℕ) : F769) (certCBit 768) (nMinus1Low F769) (matchedP F769 (nMinus1Low F769)) 1
    (fun k => 1 * certEqRun 768 (3 * (k + 1)))

/-- **Honest completeness at `p = 769`, `top = 1`:** all 97 repaired gates vanish. -/
theorem honest_768_at_769 : ∀ g ∈ formRCertificateGates (F := F769), g.eval row768 = 0 := by
  have h2 : (2 : F769) ≠ 0 := by decide
  have hc : ringChar F769 ≠ 0 := by rw [ringChar_769]; norm_num
  refine deployed_row_accepts _ _ _ _ _ 768 (Or.inr rfl) matchedTop_nMinus1.symm rfl
    (fun j hj => ?_) (fun _ _ => rfl) ?_ (fun _ => ?_) ?_
  · unfold certCBit; rw [certShift_768, if_neg (by rw [formRN_769] at hj; omega)]
  · refine rangeGate_eval_of_eq_nMinus1 _ (fun k hk => ?_) ?_ (rowEnv_top _ _ _ _ _ _)
    · rw [rowEnv_m _ _ _ _ _ _ k hk, nMinus1Low_testBit k hk]
    · rw [rowEnv_P]; exact matchedP_nMinus1
  · exact certLt_one_of_window (F := F769) 768 hc (by rw [formRN_769]; norm_num)
      (by rw [certShift_768, formRN_769]) (by norm_num) (by rw [ringChar_769]; norm_num)
  · have h := pow_csum_cert (F := F769) row768 768 (by norm_num) (by norm_num) h2
      (fun j hj => by rw [row768, rowEnv_c _ _ _ _ _ _ j hj]; rfl)
    rw [certShift_768] at h
    have hpb : powBits (2 : F769) (nMinus1Low F769) 6 = 2 ^ 9 := by
      rw [nMinus1Low_769, powBits_six_eq _ _ (by norm_num)]
    rw [hpb]; exact h.symm

end At769

section Goldilocks

/-- The honest certificate value `a = p − 1`. -/
def aP : ℕ := Nock.Field.p - 1

theorem size_aP : Nat.size aP = 64 :=
  le_antisymm (Nat.size_le.mpr (by norm_num [aP, Nock.Field.p]))
    (Nat.lt_size.mpr (by norm_num [aP, Nock.Field.p]))
theorem certShift_aP : certShift aP = 63 := by simp [certShift, size_aP]

/-- The honest row of the leaf `p − 1` at Goldilocks. -/
noncomputable def rowP : Env GF :=
  rowEnv ((aP : ℕ) : GF) (certCBit aP) (nMinus1Low GF) (matchedP GF (nMinus1Low GF)) 1
    (fun k => 1 * certEqRun aP (3 * (k + 1)))

/-- **Honest completeness at Goldilocks, `top = 1`:** all 97 repaired gates vanish. -/
theorem honest_pred_at_goldilocks : ∀ g ∈ formRCertificateGates (F := GF), g.eval rowP = 0 := by
  have hc : ringChar GF ≠ 0 := by rw [ringChar_GF]; norm_num [Nock.Field.p]
  refine deployed_row_accepts _ _ _ _ _ aP (Or.inr rfl) matchedTop_nMinus1.symm rfl
    (fun j hj => ?_) (fun _ _ => rfl) ?_ (fun _ => ?_) ?_
  · unfold certCBit; rw [certShift_aP, if_neg (by rw [formRN_GF] at hj; omega)]
  · refine rangeGate_eval_of_eq_nMinus1 _ (fun k hk => ?_) ?_ (rowEnv_top _ _ _ _ _ _)
    · rw [rowEnv_m _ _ _ _ _ _ k hk, nMinus1Low_testBit k hk]
    · rw [rowEnv_P]; exact matchedP_nMinus1
  · exact certLt_one_of_window (F := GF) aP hc (by rw [formRN_GF])
      (by rw [certShift_aP, formRN_GF]) (by norm_num [aP, Nock.Field.p])
      (by rw [ringChar_GF]; norm_num [aP, Nock.Field.p])
  · have hle : 2 ^ 63 ≤ aP := by norm_num [aP, Nock.Field.p]
    have hr : aP - 2 ^ 63 < 2 ^ 63 := by norm_num [aP, Nock.Field.p]
    have h := twoPow_csum_bits (F := GF) rowP (aP - 2 ^ 63) hr two_ne_zero_GF
      (fun j hj => by
        rw [rowP, rowEnv_c _ _ _ _ _ _ j hj]
        unfold certCBit
        rw [certShift_aP, if_pos hj, ← testBit_sub_pow aP 63 (62 - j) hle (by omega),
          show 63 - 1 - j = 62 - j by omega]
        rfl)
    have hpb : powBits (2 : GF) (nMinus1Low GF) 6 = 2 ^ 63 := by
      rw [nMinus1Low_GF, powBits_six_eq _ _ (by norm_num)]
    have h' : (2 : GF) ^ 63 * (csum (F := GF)).eval rowP = ((aP : ℕ) : GF) := by
      rw [h, ← Nat.cast_ofNat, ← Nat.cast_pow, ← Nat.cast_add, Nat.add_sub_cancel' hle]
    rw [hpb]; exact h'.symm

end Goldilocks

end Nock.RedTeam.Batch808

#print axioms Nock.RedTeam.Batch808.honest_768_at_769
#print axioms Nock.RedTeam.Batch808.honest_pred_at_goldilocks
