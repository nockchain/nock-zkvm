/-
  Nock/NockVMROM/Thm54/P8Core/Batch972Thm54Round0WrapCertAxis.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch972Thm54Round0WrapCertAxis`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch972Thm54Round0WrapCertAxis.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch806Thm54FormRRepairSound
import Nock.NockVMROM.Thm54.StrategyOfTracesR0

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch972

open scoped Polynomial BigOperators
open Polynomial
open Nock
open Nock.Reified
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.RedTeam.Batch575
open Nock.RedTeam.Batch554 (Cpoly bit)

noncomputable section

section Encode

variable {K : Type} [Field K]

theorem formRT_certAxis (lmb : K) (m : ℕ) (c : ℕ → Bool) :
    formRT lmb (certAxis m c) = lmb ^ m := by
  unfold formRT; rw [formRCertShift_certAxis]

private theorem finset_sum_range_eq_list (n : ℕ) (f : ℕ → K) :
    ∑ j ∈ Finset.range n, f j = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
      simp

/-- **`C'` of the recovered axis is the certificate's `C'`**, given the padding. -/
theorem formRC_certAxis (lmb : K) (m : ℕ) (c : ℕ → Bool)
    (hpad : Padding (FormRAxisEvent.formRN K) m c) :
    formRC lmb (certAxis m c) = (C'poly (K := K) (FormRAxisEvent.formRN K) c).eval lmb := by
  simp only [MemoryTable.formRC, C'poly, Cpoly, ← FormRAxisEvent.formRN_sub_one]
  rw [eval_add, eval_pow, eval_X, eval_finsetSum, finset_sum_range_eq_list]
  congr 1
  congr 1
  apply List.map_congr_left
  intro j hj
  have hj' : j < FormRAxisEvent.formRN K - 1 := List.mem_range.mp hj
  rw [formRCertBit_certAxis]
  simp only [eval_mul, eval_C, eval_pow, eval_X, bit]
  by_cases hjm : j < m
  · simp [hjm]
  · have hc : c (j + 1) = false := hpad (j + 1) (by omega) (by omega)
    simp [hjm, hc]

end Encode

section Bound

open scoped Classical
variable {F : Type} [Field F]

theorem rowShift_eq_782 (env : Env F) :
    DecodedLambdaEvent.rowShift env = Nock.RedTeam.Batch782.rowShift env := rfl

theorem certShift_eq_formRCertShift (a : ℕ) : certShift a = formRCertShift a := rfl

theorem certCBit_eq_formRCertBit (a j : ℕ) : certCBit a j = formRCertBit a j := rfl

/-- Proof verbatim otherwise. -/
theorem formR_cert_lt_p_p4 (env : Env F) (a : ℕ)
    (hp4 : 3 < ringChar F) (hp64 : ringChar F < 2 ^ 64)
    (ha0 : 0 < a) (ha64 : a < 2 ^ 64)
    (hC : ∀ j, j < 63 → env.trace (col0 + j) = bit01 (certCBit a j))
    (hM : ∀ k, k < 6 → env.trace (col0 + 63 + k) = bit01 ((certShift a).testBit k))
    (hacc : ∀ g ∈ formRCertificateGates (F := F), g.eval env = 0) :
    a < ringChar F := by
  have hchar : ringChar F ≠ 0 := by omega
  have hmem : ∀ g, g ∈ booleanGates (F := F) ++ powerPins ++ formRPins ++ helperPins ++
      formRNamed → g ∈ formRCertificateGates (F := F) := fun g hg => by
    simpa [formRCertificateGates] using hg
  have hpP : (pPin (F := F)).eval env = 0 := hacc _ (hmem _ (by simp [formRPins]))
  have htP : (topPin (F := F)).eval env = 0 := hacc _ (hmem _ (by simp [formRPins]))
  have hrG : (rangeGate (F := F)).eval env = 0 := hacc _ (hmem _ (by simp [formRNamed]))
  have hcG : (comparisonGate (F := F)).eval env = 0 := hacc _ (hmem _ (by simp [formRNamed]))
  have hH : ∀ k, k < 21 → (helperPinAt (F := F) k).eval env = 0 := fun k hk =>
    hacc _ (hmem _ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
      (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))))))
  have hn64 : formRN F ≤ 64 := by
    unfold formRN; exact Nat.size_le.mpr hp64
  have hm64 : certShift a < 64 := Nat.lt_succ_of_le (certShift_le_63_of_lt_64 a ha64)
  have hb : ∀ k, k < 6 → (bbool (colM (F := F) k)).eval env = 0 := fun k hk => by
    simp only [bbool, colM, bcur, CoeffExpr.eval]; rw [hM k hk]; exact bit01_mul_sub _
  have hsh : certShift a ≤ formRN F - 1 := by
    have := Batch806.shift_le_formRN_pred env hb hpP htP hrG
    rwa [Batch806.rowShift_eq env (certShift a) hm64 hM] at this
  rcases Nat.lt_or_eq_of_le hsh with hlt | heq
  · -- below `n − 1`: `a < 2^{m+1} ≤ 2^{n−1} ≤ p`
    have hsz : certShift a + 1 = Nat.size a := certShift_of_pos a ha0
    have h1 : a < 2 ^ (certShift a + 1) := by rw [hsz]; exact Nat.lt_size_self a
    have h2 : 2 ^ (certShift a + 1) ≤ 2 ^ (formRN F - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have h3 : 2 ^ (formRN F - 1) ≤ ringChar F := by
      have := Nat.lt_size.mp (show formRN F - 1 < Nat.size (ringChar F) by
        unfold formRN at *; omega)
      exact this
    omega
  · -- at `n − 1`: U1 forces `top = 1`, the helpers are the eq-chain, the comparison is `certLt`
    have hN : nMinus1Low F = formRN F - 1 := Nat.mod_eq_of_lt (by omega)
    have hlm : ∀ k, k < 6 → (lm (F := F) k).eval env = 1 := fun k hk => by
      rw [lm_eval, hM k hk, heq, ← hN]
      have := matchedLm_nMinus1 (F := F) k hk
      unfold matchedLm at this
      split_ifs at this ⊢ <;> simpa using this
    have hP : env.trace (col0 + 71) = 1 := by
      have h := hpP
      simp only [pPin, colP, bcur, CoeffExpr.eval] at h
      rw [hlm 5 (by decide), hlm 4 (by decide), hlm 3 (by decide)] at h
      simpa [sub_eq_zero] using h
    have hTop : env.trace (col0 + 72) = 1 := by
      have h := htP
      rw [topPin_eval, hlm 2 (by decide), hlm 1 (by decide), hlm 0 (by decide), hP] at h
      simpa [sub_eq_zero] using h
    have hE := Batch806.helpers_eq_certEqRun env a hTop hC hH
    have hcmp := Batch806.comparisonGate_eval_eq env a hTop hC hE
    rw [hcG] at hcmp
    have hlt1 : certLt (F := F) a 63 = 1 := (sub_eq_zero.mp hcmp.symm)
    exact Batch806.certLt_one_imp_lt (F := F) a hchar heq ha0 hlt1

/-- **The padded certificate of an accepted compute row is below `p`.** -/
theorem certAxis_lt_ringChar (env : Env F)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F)
    (hacc : ∀ g ∈ formRCertificateGates (F := F), g.eval env = 0)
    (hpad : Padding (OptimizedComputeRangeCertificate.formRN F) (DecodedLambdaEvent.rowShift env)
      (DecodedLambdaEvent.rowBits env)) :
    certAxis (DecodedLambdaEvent.rowShift env) (DecodedLambdaEvent.rowBits env) < ringChar F := by
  have hp64 : ringChar F < 2 ^ 64 := Nat.size_le.mp hwidth.1
  have hp4 : 3 < ringChar F := hwidth.2.2
  set m := DecodedLambdaEvent.rowShift env with hm
  set cb := DecodedLambdaEvent.rowBits env with hcb
  have hmem : ∀ g, g ∈ booleanGates (F := F) ++ powerPins ++ formRPins ++ helperPins ++
      formRNamed → g ∈ formRCertificateGates (F := F) := fun g hg => by
    simpa [formRCertificateGates] using hg
  have hb : ∀ k, k < 6 → (bbool (colM (F := F) k)).eval env = 0 := by
    intro k hk
    refine hacc _ (hmem _ ?_)
    simp only [booleanGates, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk, rfl⟩))))
  have hpP : (pPin (F := F)).eval env = 0 := hacc _ (hmem _ (by simp [formRPins]))
  have htP : (topPin (F := F)).eval env = 0 := hacc _ (hmem _ (by simp [formRPins]))
  have hrG : (rangeGate (F := F)).eval env = 0 := hacc _ (hmem _ (by simp [formRNamed]))
  have hsh : m ≤ OptimizedComputeRangeCertificate.formRN F - 1 := by
    rw [hm, rowShift_eq_782]
    exact Batch806.shift_le_formRN_pred env hb hpP htP hrG
  have hm63 : m ≤ 63 := DecodedLambdaEvent.rowShift_le env
  obtain ⟨_, hR⟩ := Nock.RedTeam.Batch782.shift_cols_of_boolean env hb
  have hpos := certAxis_pos m cb
  have hlt := certAxis_lt m cb
  have hsz : certShift (certAxis m cb) = m := by
    rw [certShift_eq_formRCertShift, formRCertShift_certAxis]
  refine formR_cert_lt_p_p4 env (certAxis m cb) hp4 hp64 hpos ?_ ?_ ?_ hacc
  · calc certAxis m cb < 2 ^ (m + 1) := hlt
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  · intro j hj
    rw [certCBit_eq_formRCertBit, formRCertBit_certAxis]
    have hg := hacc
      (if OptimizedComputeRangeCertificate.formRN F - 1 < j + 1 then colC j else bbool (colC j))
      (hmem _ (by
        simp only [booleanGates, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨j, hj, rfl⟩))))))
    have hcbj : cb (j + 1) = decide (env.trace (202 + j) = 1) := by
      rw [hcb]
      unfold DecodedLambdaEvent.rowBits
      simp only [Nat.add_sub_cancel]
      congr 1
      apply propext
      constructor
      · intro h; exact h.2.2
      · intro h; exact ⟨by omega, by omega, h⟩
    split_ifs at hg with hbig
    · -- beyond `n − 1`: the C2 pin zeroes the column, and `j ≥ m`
      have hz : env.trace (col0 + j) = 0 := by simpa [colC, bcur, CoeffExpr.eval] using hg
      have hjm : ¬ j < m := by omega
      simp [hz, hjm]
    · have h01 : env.trace (col0 + j) = 0 ∨ env.trace (col0 + j) = 1 := by
        have h' : env.trace (col0 + j) * (env.trace (col0 + j) - 1) = 0 := by
          simpa [bbool, colC, bcur, CoeffExpr.eval] using hg
        rcases mul_eq_zero.mp h' with h | h
        · exact Or.inl h
        · exact Or.inr (sub_eq_zero.mp h)
      have hcol : col0 + j = 202 + j := rfl
      by_cases hjm : j < m
      · rw [hcbj, ← hcol]
        rcases h01 with h | h <;> simp [h, hjm]
      · have hc : cb (j + 1) = false := hpad (j + 1) (by omega) (by omega)
        rw [hcbj, ← hcol] at hc
        rcases h01 with h | h
        · simp [h, hjm]
        · simp [h] at hc
  · intro k hk
    rw [hsz]
    have := hR k hk
    rw [← rowShift_eq_782] at this
    exact this

end Bound

end

end Nock.RedTeam.Batch972
