/-
  Nock/RedTeam/Batch863Thm54ReviewU1Shapes.lean

  Notes only; no production edit.

  * `old_window_false_at_p`: the deleted `a ≤ p` form of `certLt_one_of_window` is FALSE under C1
    at `a = p` (`p = 769`, `a = 769`: `certLt = 0`).  The tightening is forced, not a weakening.
  * `linCol_msb_eval_false_at_17`: the deleted `linCol_msb_eval` (`c₀ = 0 ⇒ lin₀ = 0`) is FALSE
    under C1 at `p = 17` (`p_{n−2} = p_3 = 0`, so `lin₀ = 1 − c₀ = 1`).
-/
import Nock.RedTeam.Batch806Thm54FormRRepairSound
import Nock.RedTeam.Batch781Thm54U1Reproduce
import Nock.NockVMROM.Thm54.FormRTemplatePolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch863

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.CoordinateCompiler

theorem formRN_copies_agree (K : Type) [Field K] :
    FormRAxisEvent.formRN K = OptimizedComputeRangeCertificate.formRN K := rfl

/-- The `hA` of `Batch824.r4_path_valid_at`, verbatim in its `FormRAxisEvent.formRN` form. -/
theorem r4_hA_of_U1 {K : Type} [Field K] {N : ℕ} (envsC : Fin N → Env K)
    (hn : 2 ≤ formRN K)
    (hb : ∀ i, ∀ k, k < 6 → (bbool (colM (F := K) k)).eval (envsC i) = 0)
    (hp : ∀ i, (pPin (F := K)).eval (envsC i) = 0)
    (ht : ∀ i, (topPin (F := K)).eval (envsC i) = 0)
    (hr : ∀ i, (rangeGate (F := K)).eval (envsC i) = 0) :
    ∀ e, DecodedLambdaEvent.decodedShift envsC e ≤ FormRAxisEvent.formRN K - 1 :=
  Batch806.decodedShift_in_range_of_U1 envsC hn hb hp ht hr

open Batch781 in
theorem size_769 : Nat.size 769 = 10 :=
  le_antisymm (Nat.size_le.mpr (by norm_num)) (Nat.lt_size.mpr (by norm_num))

open Batch781 in
/-- At `a = p` the C1 comparison witness is `0`: the old `a ≤ p` statement is false. -/
theorem old_window_false_at_p : certLt (F := F769) 769 63 = 0 := by
  have hc : ringChar F769 ≠ 0 := by rw [ringChar_769]; norm_num
  refine Batch806.certLt_zero_of_ge (F := F769) 769 hc ?_ (by norm_num) (by rw [ringChar_769])
  rw [formRN_769]; simp [certShift, size_769]

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩
abbrev F17 := ZMod 17

theorem formRN_17 : formRN F17 = 5 := by
  rw [formRN, ZMod.ringChar_zmod_n]
  exact le_antisymm (Nat.size_le.mpr (by norm_num)) (Nat.lt_size.mpr (by norm_num))

/-- The deleted `linCol_msb_eval` fails under C1 at `p = 17`. -/
theorem linCol_msb_eval_false_at_17 :
    ¬ ∀ env : Env F17, env.trace col0 = 0 → (linCol (F := F17) 0).eval env = 0 := by
  intro h
  have hbit : pBit F17 (formRN F17 - 2 - 0) = false := by
    rw [formRN_17]; simp [pBit, ZMod.ringChar_zmod_n]; decide
  let env : Env F17 := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩
  have := h env rfl
  simp only [linCol, hbit] at this
  simp [colC, bcur, CoeffExpr.eval, env] at this

end Nock.RedTeam.Batch863

#print axioms Nock.RedTeam.Batch863.r4_hA_of_U1
#print axioms Nock.RedTeam.Batch863.old_window_false_at_p
#print axioms Nock.RedTeam.Batch863.linCol_msb_eval_false_at_17
