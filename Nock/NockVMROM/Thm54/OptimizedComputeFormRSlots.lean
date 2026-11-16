import Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

/-!
# Form R compute record slots: honest values

This module evaluates those in-gate slot expressions on a typed row environment
whose certificate columns hold the leftover certificate of a natural axis `a < 2^64`, and
identifies them with the Form R encode `MemoryTable.formRT λ a` / `formRC λ a` the compute IO
(`NockVM.encRecFormR`) reads.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeFormRSlots

open Nock
open Nock.Reified
open OptimizedComputeSubstitution
open OptimizedComputeCorrectedFinal
open OptimizedComputeRangeCertificate
open OptimizedComputeFinalTrace

noncomputable section

/-! ## The `C'` sum -/

theorem foldr_cprime_eval {K : Type*} [Field K] (env : Env K) :
    ∀ l : List ℕ,
      (l.foldr (fun j acc => Expr.Add (.Mul (certCVar .traceCur j) (lamPowVar (j + 1))) acc)
          (lamPowVar 0)).eval env =
        env.chal 100 + (l.map fun j => env.trace (202 + j) * env.chal (100 + (j + 1))).sum
  | [] => by simp [lamPowVar, Expr.eval]
  | j :: l => by
      have ih := foldr_cprime_eval env l
      simp only [List.foldr_cons, List.map_cons, List.sum_cons, Expr.eval, certCVar,
        lamPowVar] at ih ⊢
      rw [ih]
      ring

theorem sampledCprime_eval {K : Type*} [Field K] (env : Env K) :
    (sampledCprime .traceCur).eval env =
      env.chal 100 +
        ∑ j ∈ Finset.range 63, env.trace (202 + j) * env.chal (100 + (j + 1)) := by
  rw [sampledCprime, foldr_cprime_eval, MemoryTable.list_range_map_sum]

/-! ## Typed-environment readings -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem toSource_chal9 (env : CorrectedFinalTypedEnv F K) :
    env.toSourceEnv.chal 9 = env.chal 9 := by
  simp [CorrectedFinalTypedEnv.toSourceEnv]

theorem toSource_lamPow (env : CorrectedFinalTypedEnv F K) (d : ℕ) (hd : d < 64) :
    env.toSourceEnv.chal (100 + d) = lamPowVal (env.chal 9) d := by
  simp [CorrectedFinalTypedEnv.toSourceEnv, show ¬ 100 + d < 12 by omega,
    show 100 + d < 164 by omega]

theorem toSource_certBase (env : CorrectedFinalTypedEnv F K) (j : ℕ) (hj : j < 94) :
    env.toSourceEnv.trace (202 + j) = algebraMap F K (env.certBase ⟨j, hj⟩) := by
  simp [CorrectedFinalTypedEnv.toSourceEnv, show ¬ 202 + j < 13 by omega,
    show ¬ 202 + j < 76 by omega, show 202 + j < 296 by omega]

theorem toSource_certT (env : CorrectedFinalTypedEnv F K) :
    env.toSourceEnv.trace 299 = env.certExt 1 := by
  simp [CorrectedFinalTypedEnv.toSourceEnv]

/-! ## Form R algebra -/

theorem formRCertShift_two : MemoryTable.formRCertShift 2 = 1 := by decide
theorem formRCertShift_three : MemoryTable.formRCertShift 3 = 1 := by decide

theorem formRT_two (lam : K) : MemoryTable.formRT lam 2 = lam := by
  simp [MemoryTable.formRT, formRCertShift_two]

theorem formRT_three (lam : K) : MemoryTable.formRT lam 3 = lam := by
  simp [MemoryTable.formRT, formRCertShift_three]

theorem formRCertBit_two (j : ℕ) : MemoryTable.formRCertBit 2 j = false := by
  unfold MemoryTable.formRCertBit
  rw [formRCertShift_two]
  split_ifs with hj
  · have : j = 0 := by omega
    subst this; decide
  · rfl

theorem formRCertBit_three (j : ℕ) :
    MemoryTable.formRCertBit 3 j = decide (j = 0) := by
  unfold MemoryTable.formRCertBit
  rw [formRCertShift_three]
  split_ifs with hj
  · have : j = 0 := by omega
    subst this; decide
  · simp; omega

theorem formRC_two (lam : K) :
    MemoryTable.formRC lam 2 = lam ^ MemoryTable.pwScaleExp K := by
  simp [MemoryTable.formRC, formRCertBit_two]

theorem formRC_three (lam : K) (hN : 1 ≤ MemoryTable.pwScaleExp K) :
    MemoryTable.formRC lam 3 =
      lam ^ MemoryTable.pwScaleExp K + lam ^ (MemoryTable.pwScaleExp K - 1) := by
  simp only [MemoryTable.formRC, formRCertBit_three, MemoryTable.list_range_map_sum]
  congr 1
  obtain ⟨M, hM⟩ : ∃ M, MemoryTable.pwScaleExp K = M + 1 := ⟨_, (Nat.sub_add_cancel hN).symm⟩
  rw [hM, Finset.sum_range_succ']
  simp

theorem lamPowVal_zero (lam : K) :
    lamPowVal lam 0 = lam ^ MemoryTable.pwScaleExp K := by
  simp [lamPowVal]

theorem lamPowVal_one (lam : K) (hN : 1 ≤ MemoryTable.pwScaleExp K) :
    lamPowVal lam 1 = lam ^ (MemoryTable.pwScaleExp K - 1) := by
  simp [lamPowVal, hN]

theorem certCBit_eq_formRCertBit (a j : ℕ) :
    certCBit a j = MemoryTable.formRCertBit a j := rfl

/-- The in-gate `C'` with the leftover certificate bits of `a` is the Form R `C'` of `a`. -/
theorem slot_cprime_eq_formRC (lam : K) (a : ℕ) (hN : MemoryTable.pwScaleExp K ≤ 63) :
    lamPowVal lam 0 +
        ∑ j ∈ Finset.range 63,
          algebraMap F K (bit01 (certCBit a j)) * lamPowVal lam (j + 1) =
      MemoryTable.formRC lam a := by
  set N := MemoryTable.pwScaleExp K with hNdef
  simp only [MemoryTable.formRC, ← hNdef, MemoryTable.list_range_map_sum, lamPowVal_zero]
  congr 1
  rw [show (63 : ℕ) = N + (63 - N) by omega, Finset.sum_range_add]
  have htail : ∑ x ∈ Finset.range (63 - N),
      algebraMap F K (bit01 (certCBit a (N + x))) * lamPowVal lam (N + x + 1) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    simp [lamPowVal, ← hNdef, show ¬ N + x + 1 ≤ N by omega]
  rw [htail, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j + 1 ≤ N := Finset.mem_range.mp hj
  simp only [lamPowVal, ← hNdef, if_pos hj', certCBit_eq_formRCertBit]
  cases MemoryTable.formRCertBit a j <;> simp [bit01]

/-- The leftover `T` helper of a bounded axis is the Form R `T`. -/
theorem formRLamTNat_eq_formRT (lam : K) (a : ℕ) (ha : a < 2 ^ 64) :
    formRLamTNat (F := F) a lam = MemoryTable.formRT lam a := by
  have hs : Nat.size a ≤ 64 := Nat.size_le.mpr ha
  have hm : axisCertM a < 64 := by
    simp only [axisCertM, certShift]; omega
  unfold formRLamTNat
  rw [rangeShiftExp_of_lt64 (F := F) hm, leftoverHornerExp_of_lt (F := F) hm,
    powBits_six_eq lam _ hm]
  rfl

/-! ## Width and residue side conditions -/

theorem ringChar_K_eq (F K : Type) [Field F] [Field K] [Algebra F K] :
    ringChar K = ringChar F := (Algebra.ringChar_eq F K).symm

theorem pwScaleExp_le_63 (hwidth : FormRWidth F) :
    MemoryTable.pwScaleExp K ≤ 63 := by
  have h := hwidth.1
  simp only [formRN] at h
  simp only [MemoryTable.pwScaleExp, ringChar_K_eq F K]
  omega

theorem one_le_pwScaleExp (hwidth : FormRWidth F) :
    1 ≤ MemoryTable.pwScaleExp K := by
  have h3 : 3 < ringChar F := hwidth.2.2
  have hs : Nat.size 3 ≤ Nat.size (ringChar F) := Nat.size_le_size (by omega)
  have h3s : Nat.size 3 = 2 := by decide
  simp only [MemoryTable.pwScaleExp, ringChar_K_eq F K]
  omega

theorem nockAxisOf_two (hwidth : FormRWidth F) :
    MemoryTable.nockAxisOf (2 : K) = 2 := by
  have h : 2 < ringChar K := by rw [ringChar_K_eq F K]; have := hwidth.2.2; omega
  simpa using MemoryTable.nockAxisOf_natCast (K := K) (a := 2) h

theorem nockAxisOf_three (hwidth : FormRWidth F) :
    MemoryTable.nockAxisOf (3 : K) = 3 := by
  have h : 3 < ringChar K := by rw [ringChar_K_eq F K]; exact hwidth.2.2
  simpa using MemoryTable.nockAxisOf_natCast (K := K) (a := 3) h

/-! ## Slot values on a row environment -/

/-- The three request records' Form R slots on a row environment whose certificate columns hold
the leftover certificate of the natural axis `a` and whose `T` helper is `λ^{m}`.  The record
axis is `3` (`mr₁`), `a` (`mr₂` on `s0`, `mr₃` on `s9`) or `2` (`mr₂` on `G`, `mr₃` on `s6`). -/
theorem formR_slots
    (E : Env K) (lam : K) (st : ComputeTable.State)
    (hsel : ∀ s : ComputeTable.State,
      E.trace (Nock.Reified.opCol s) = if s = st then 1 else 0)
    (a : ℕ) (ha : a < 2 ^ 64)
    (hN1 : 1 ≤ MemoryTable.pwScaleExp K) (hN : MemoryTable.pwScaleExp K ≤ 63)
    (h9 : E.chal 9 = lam)
    (hlp : ∀ d, d < 64 → E.chal (100 + d) = lamPowVal lam d)
    (hcb : ∀ j, j < 63 → E.trace (202 + j) = algebraMap F K (formROffNat (F := F) a j))
    (hT : E.trace 299 = formRLamTNat (F := F) a lam) :
    ((sampledSlotT .traceCur 67).eval E = MemoryTable.formRT lam 3 ∧
      (sampledSlotC .traceCur 67).eval E = MemoryTable.formRC lam 3) ∧
    (st = .s0 →
      (sampledSlotT .traceCur 75).eval E = MemoryTable.formRT lam a ∧
      (sampledSlotC .traceCur 75).eval E = MemoryTable.formRC lam a) ∧
    (st = .s2 ∨ st = .s5 ∨ st = .s6 ∨ st = .s7 ∨ st = .s8 ∨ st = .s9 →
      (sampledSlotT .traceCur 75).eval E = MemoryTable.formRT lam 2 ∧
      (sampledSlotC .traceCur 75).eval E = MemoryTable.formRC lam 2) ∧
    (st = .s6 →
      (sampledSlotT .traceCur 83).eval E = MemoryTable.formRT lam 2 ∧
      (sampledSlotC .traceCur 83).eval E = MemoryTable.formRC lam 2) ∧
    (st = .s9 →
      (sampledSlotT .traceCur 83).eval E = MemoryTable.formRT lam a ∧
      (sampledSlotC .traceCur 83).eval E = MemoryTable.formRC lam a) := by
  have hl0 : E.chal 100 = lam ^ MemoryTable.pwScaleExp K := by
    simpa [lamPowVal_zero] using hlp 0 (by decide)
  have hl1 : E.chal 101 = lam ^ (MemoryTable.pwScaleExp K - 1) := by
    simpa [lamPowVal_one lam hN1] using hlp 1 (by decide)
  have hTv : E.trace 299 = MemoryTable.formRT lam a := by
    rw [hT, formRLamTNat_eq_formRT _ _ ha]
  have hCv : (sampledCprime .traceCur).eval E = MemoryTable.formRC lam a := by
    rw [sampledCprime_eval, ← slot_cprime_eq_formRC (F := F) lam a hN]
    have h100 : E.chal 100 = lamPowVal lam 0 := hlp 0 (by decide)
    rw [h100]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < 63 := Finset.mem_range.mp hj
    rw [hcb j hj', hlp (j + 1) (by omega)]
    simp [formROffNat, hj']
  have s0 := hsel .s0
  have s2 := hsel .s2
  have s5 := hsel .s5
  have s6 := hsel .s6
  have s7 := hsel .s7
  have s8 := hsel .s8
  have s9 := hsel .s9
  simp only [Nock.Reified.opCol] at s0 s2 s5 s6 s7 s8 s9
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp [sampledSlotT, sampledLam, Expr.eval, h9, formRT_three]
  · simp [sampledSlotC, lamPowVar, Expr.eval, hl0, hl1, formRC_three lam hN1]
  · rintro rfl
    simp at s0 s2 s5 s6 s7 s8 s9
    refine ⟨?_, ?_⟩
    · simp only [sampledSlotT, sampledGSel, certTVar, sampledLam, Expr.eval, s0, s2, s5, s6,
        s7, s8, s9, hTv]
      ring
    · simp only [sampledSlotC, sampledGSel, lamPowVar, Expr.eval, s0, s2, s5, s6, s7, s8, s9,
        hCv]
      ring
  · intro hst
    rcases hst with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp at s0 s2 s5 s6 s7 s8 s9 <;>
      refine ⟨?_, ?_⟩ <;>
      simp [sampledSlotT, sampledSlotC, sampledGSel, certTVar, sampledLam, lamPowVar,
        Expr.eval, s0, s2, s5, s6, s7, s8, s9, h9, hl0, formRT_two, formRC_two]
  · rintro rfl
    simp at s0 s2 s5 s6 s7 s8 s9
    refine ⟨?_, ?_⟩ <;>
      simp [sampledSlotT, sampledSlotC, certTVar, sampledLam, lamPowVar, Expr.eval, s6, s9,
        h9, hl0, formRT_two, formRC_two]
  · rintro rfl
    simp at s0 s2 s5 s6 s7 s8 s9
    refine ⟨?_, ?_⟩
    · simp [sampledSlotT, certTVar, sampledLam, Expr.eval, s6, s9, hTv]
    · simp [sampledSlotC, lamPowVar, Expr.eval, s6, s9, hCv]

end

end OptimizedComputeFormRSlots
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedComputeFormRSlots.slot_cprime_eq_formRC
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeFormRSlots.formR_slots
