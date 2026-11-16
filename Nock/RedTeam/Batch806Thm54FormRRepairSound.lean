/-
  Nock/RedTeam/Batch806Thm54FormRRepairSound.lean

  * `topPin_eq_U1`: the deployed `topPin` is the pre-greenlight's U1 replica (`Batch782.topPinU1`),
    definitionally.
  * `shift_le_formRN_pred`: boolean shift bits + `pPin` + the production `topPin` + `rangeGate`
    ⇒ the row's 6-bit shift is `≤ n − 1`, every width, no field hypothesis.
  * `certLt_one_imp_lt`: the repaired (C1) comparison witness is `1` only below `p` — every
    shift-`(n−1)` certificate `a` with `certLt a 63 = 1` has `a < p` (`n ≤ 64`).
  * `comparisonGate_eval_eq`: on a `top = 1` row whose certificate columns are the bits of `a`
    and whose helpers are the eq-chain, the comparison gate is `certLt a 63 − 1`.
  * `helpers_eq_certEqRun`: the 21 helper pins with `top = 1` force the helpers to the eq-chain.
  * **`formR_cert_lt_p` (the `Batch557.gadget_sound` shape, generic):** for every field with
    `25 ≤ p < 2^64`, a row passing all 97 deployed gates whose certificate / shift columns carry
    `0 < a < 2^64` has `a < p`.
-/
import Nock.RedTeam.Batch782Thm54U1Sound
import Nock.NockVMROM.Thm54.DecodedLambdaEvent
import Nock.NockVMROM.Thm54.P8Core.Batch806Thm54FormRRepairSound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Nock.RedTeam.Batch806

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.CoordinateCompiler

section Generic

variable {F : Type*} [Field F]

/-- The deployed `topPin` IS the U1 pin of the pre-greenlight (`Batch782.topPinU1`). -/
theorem topPin_eq_U1 : (topPin (F := F)) = Nock.RedTeam.Batch782.topPinU1 := rfl

/-- **Generic `cert < p` from the repaired gates (the `Batch557.gadget_sound` shape).**  For every
base field with `25 ≤ p < 2^64`: a row passing all 97 deployed Form R gates whose certificate
columns are the bits of `0 < a < 2^64` and whose shift columns are `certShift a` has `a < p`. -/
theorem formR_cert_lt_p (env : Env F) (a : ℕ)
    (hp25 : 25 ≤ ringChar F) (hp64 : ringChar F < 2 ^ 64)
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
  have hn5 : 5 ≤ formRN F := by
    unfold formRN
    exact (Nat.lt_size).mpr (le_trans (by norm_num) hp25)
  have hm64 : certShift a < 64 := Nat.lt_succ_of_le (certShift_le_63_of_lt_64 a ha64)
  have hb : ∀ k, k < 6 → (bbool (colM (F := F) k)).eval env = 0 := fun k hk => by
    simp only [bbool, colM, bcur, CoeffExpr.eval]; rw [hM k hk]; exact bit01_mul_sub _
  have hsh : certShift a ≤ formRN F - 1 := by
    have := shift_le_formRN_pred env hb hpP htP hrG
    rwa [rowShift_eq env (certShift a) hm64 hM] at this
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
    have hE := helpers_eq_certEqRun env a hTop hC hH
    have hcmp := comparisonGate_eval_eq env a hTop hC hE
    rw [hcG] at hcmp
    have hlt1 : certLt (F := F) a 63 = 1 := (sub_eq_zero.mp hcmp.symm)
    exact certLt_one_imp_lt (F := F) a hchar heq ha0 hlt1

end Generic

/-! ## The `CertInRange` source for Part 2, at the production decoder -/

section Decoded

variable {K : Type} [Field K] {N : ℕ}

end Decoded

end Nock.RedTeam.Batch806

#print axioms Nock.RedTeam.Batch806.shift_le_formRN_pred
#print axioms Nock.RedTeam.Batch806.decodedShift_in_range_of_U1
#print axioms Nock.RedTeam.Batch806.certLt_one_imp_lt
#print axioms Nock.RedTeam.Batch806.formR_cert_lt_p
