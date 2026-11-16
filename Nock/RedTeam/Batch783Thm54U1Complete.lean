/-
  Nock/RedTeam/Batch783Thm54U1Complete.lean

  **U1 pre-greenlight, Q3: is U1
  complete?  YES on the live fill, with NO fill change.**

  The live honest fill (`OptimizedComputeFinalTrace.formROff`, `preliminaryCell` columns
  `202..301`) writes, on every row, the certificate of `axisNat leaf` (`0` on non-axis rows and
  padding: shift `0`, `top = 0`).  Under `FormRWidth` and the axis bound (`FormRAxisBound`'s
  first conjuncts, which `canonical`'s Form R branch already has in scope as `hax` / `hwidth`),
  the written shift is `≤ n − 1`, so the deployed `leftoverBitMatchedTop` IS the bit-matched
  `matchedTop` of the written shift and the U1 pin holds (`honest_fill_topPinU1`).  The scope's "honest fill writes shift `n − 1` on non-axis rows" is therefore NOT needed and
  would change `T = λ^m` on every non-axis row for nothing.

  Instances: `p = 769` (leaves `5`, `768`, none) and Goldilocks (leaves `1`, `p − 1`, none).
  `TraceGen/Gen.lean` is not involved (the fill is `OptimizedComputeFinalTrace`).
-/
import Nock.RedTeam.Batch784Thm54FormRAliasesSurviveU1
import Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Nock.RedTeam.Batch783

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.RedTeam.Batch782

section Generic

variable {F : Type} [Field F]

/-- **The completeness obligation of U1 at one row:** if the written shift `m` is `≤ n − 1`, the
live fill's `top` (`leftoverBitMatchedTop m`), `P` and shift bits satisfy the U1 pin. -/
theorem topPinU1_of_fill (env : Env F) (m : ℕ) (hm : m ≤ nMinus1Low F)
    (hM : ∀ k, k < 6 →
      env.trace (col0 + 63 + k) = bit01 ((rangeShiftExp (F := F) m).testBit k))
    (hP : env.trace (col0 + 71) = matchedP F (rangeShiftExp (F := F) m))
    (hTop : env.trace (col0 + 72) = leftoverBitMatchedTop (F := F) m) :
    (topPinU1 (F := F)).eval env = 0 := by
  have hN : nMinus1Low F < 64 := Nat.mod_lt _ (by decide)
  have hm64 : m < 64 := lt_of_le_of_lt hm hN
  have he : rangeShiftExp (F := F) m = m := by
    rw [rangeShiftExp_of_lt64 (F := F) hm64, leftoverHornerExp_of_lt (F := F) hm64]
  rw [he] at hM hP
  have hlm : ∀ k, k < 6 → (lm (F := F) k).eval env = matchedLm F m k := by
    intro k hk; rw [lm_eval, hM k hk]; unfold matchedLm; split_ifs <;> rfl
  rw [topPinU1_eval, hlm 2 (by decide), hlm 1 (by decide), hlm 0 (by decide), hP, hTop]
  rcases Nat.lt_or_eq_of_le hm with hlt | heq
  · have hne : ¬ leftoverMatch (F := F) m := fun h =>
      by have := (leftoverMatch_of_lt (F := F) hm64).mp h; omega
    have hng : ¬ leftoverGtTop (F := F) m := fun h => by
      have := h.2; rw [leftoverHornerExp_of_lt (F := F) hm64] at this; omega
    have h0 : matchedTop F m = 0 := matchedTop_eq_zero_of_ne m fun hall => by
      have : m = nMinus1Low F := eq_of_low6_testBit hm64 hN fun k hk => by
        rw [hall k hk, nMinus1Low_testBit k hk]
      omega
    rw [leftoverBitMatchedTop_of_lt (F := F) hne hng hm64]
    unfold matchedTop at h0; rw [h0]; ring
  · subst heq
    rw [leftoverBitMatchedTop_nMinus1]
    have h1 := matchedTop_nMinus1 (F := F)
    unfold matchedTop at h1; rw [h1]; ring

/-- The non-axis / padding fill writes shift `0` (not `n − 1`). -/
theorem nonaxis_fill_shift_zero : axisCertM (axisNat (none : Option F)) = 0 := by
  simp [axisCertM, axisNat_none, certShift]

/-- **The live fill's shift is in range** under `FormRWidth` and the axis bound. -/
theorem fill_shift_le (leaf : Option F) (hw : FormRWidth F)
    (hleaf : ∀ L, leaf = some L → ∃ a : ℕ, 0 < a ∧ a < ringChar F ∧ (a : F) = L) :
    axisCertM (axisNat leaf) ≤ nMinus1Low F := by
  have hN : nMinus1Low F = formRN F - 1 := Nat.mod_eq_of_lt (by have := hw.1; omega)
  rw [hN]
  cases leaf with
  | none => rw [nonaxis_fill_shift_zero]; omega
  | some L =>
      obtain ⟨a, ha0, hap, haL⟩ := hleaf L rfl
      have hmem := axisNat_of_mem L ha0 haL
      have hsz : Nat.size (axisNat (some L)) ≤ Nat.size (ringChar F) :=
        Nat.size_le_size (le_trans hmem.2.1 (le_of_lt hap))
      simp only [axisCertM, certShift, formRN]
      omega

/-- **U1 is complete on the live fill:** every row whose Form R columns are `formROff leaf`
satisfies the U1 pin, under `FormRWidth` and the axis bound. -/
theorem honest_fill_topPinU1 (env : Env F) (leaf : Option F) (hw : FormRWidth F)
    (hleaf : ∀ L, leaf = some L → ∃ a : ℕ, 0 < a ∧ a < ringChar F ∧ (a : F) = L)
    (hfill : ∀ j, j < 100 → env.trace (col0 + j) = formROff leaf j) :
    (topPinU1 (F := F)).eval env = 0 := by
  refine topPinU1_of_fill env (axisCertM (axisNat leaf)) (fill_shift_le leaf hw hleaf)
    (fun k hk => ?_) ?_ ?_
  · rw [show col0 + 63 + k = col0 + (63 + k) by omega, hfill _ (by omega), formROff_m leaf k hk]
  · rw [hfill 71 (by omega), formROff_p]
  · rw [hfill 72 (by omega), formROff_top]

/-- A row carrying the live fill of `leaf` in columns `202..301`. -/
noncomputable def fillEnv (leaf : Option F) : Env F :=
  ⟨fun i => if 202 ≤ i ∧ i < 302 then formROff leaf (i - 202) else 0,
    fun _ => 0, fun _ => 0, fun _ => 0⟩

theorem fillEnv_trace (leaf : Option F) (j : ℕ) (hj : j < 100) :
    (fillEnv leaf).trace (col0 + j) = formROff leaf j := by
  have e : 202 + j - 202 = j := by omega
  simp only [fillEnv, col0, e]
  rw [if_pos (by omega)]

end Generic

/-! ## Instances: `p = 769` and Goldilocks -/

open Nock.RedTeam.Batch781 Nock.RedTeam.Batch784

theorem width_769 : FormRWidth F769 := by
  refine ⟨by rw [formRN_769]; norm_num, by rw [formRN_769]; norm_num, by rw [ringChar_769]; norm_num⟩

theorem width_GF : FormRWidth GF :=
  ⟨by rw [formRN_GF], by rw [formRN_GF]; norm_num,
    by rw [ringChar_GF]; norm_num [Nock.Field.p]⟩

theorem leaf_769 (a : ℕ) (ha0 : 0 < a) (ha : a < 769) :
    ∀ L, (some ((a : ℕ) : F769)) = some L → ∃ b : ℕ, 0 < b ∧ b < ringChar F769 ∧ (b : F769) = L :=
  fun L h => ⟨a, ha0, by rw [ringChar_769]; exact ha, Option.some.inj h⟩

theorem leaf_GF (a : ℕ) (ha0 : 0 < a) (ha : a < Nock.Field.p) :
    ∀ L, (some ((a : ℕ) : GF)) = some L → ∃ b : ℕ, 0 < b ∧ b < ringChar GF ∧ (b : GF) = L :=
  fun L h => ⟨a, ha0, by rw [ringChar_GF]; exact ha, Option.some.inj h⟩

theorem none_ok {F : Type} [Field F] :
    ∀ L, (none : Option F) = some L → ∃ b : ℕ, 0 < b ∧ b < ringChar F ∧ (b : F) = L :=
  fun _ h => by cases h

/-- **Honest instances, Tier A prime (`p = 769`):** axis leaves `5`, `768` and a non-axis row. -/
theorem honest_u1_at_769 :
    (topPinU1 (F := F769)).eval (fillEnv (some ((5 : ℕ) : F769))) = 0 ∧
      (topPinU1 (F := F769)).eval (fillEnv (some ((768 : ℕ) : F769))) = 0 ∧
      (topPinU1 (F := F769)).eval (fillEnv (none : Option F769)) = 0 :=
  ⟨honest_fill_topPinU1 _ _ width_769 (leaf_769 5 (by norm_num) (by norm_num))
      (fillEnv_trace _),
    honest_fill_topPinU1 _ _ width_769 (leaf_769 768 (by norm_num) (by norm_num))
      (fillEnv_trace _),
    honest_fill_topPinU1 _ _ width_769 none_ok (fillEnv_trace _)⟩

/-- **Honest instances, Goldilocks:** axis leaves `1`, `p − 1` and a non-axis row. -/
theorem honest_u1_at_goldilocks :
    (topPinU1 (F := GF)).eval (fillEnv (some ((1 : ℕ) : GF))) = 0 ∧
      (topPinU1 (F := GF)).eval (fillEnv (some ((Nock.Field.p - 1 : ℕ) : GF))) = 0 ∧
      (topPinU1 (F := GF)).eval (fillEnv (none : Option GF)) = 0 :=
  ⟨honest_fill_topPinU1 _ _ width_GF (leaf_GF 1 (by norm_num) (by norm_num [Nock.Field.p]))
      (fillEnv_trace _),
    honest_fill_topPinU1 _ _ width_GF
      (leaf_GF _ (by norm_num [Nock.Field.p]) (by norm_num [Nock.Field.p])) (fillEnv_trace _),
    honest_fill_topPinU1 _ _ width_GF none_ok (fillEnv_trace _)⟩

end Nock.RedTeam.Batch783

#print axioms Nock.RedTeam.Batch783.topPinU1_of_fill
#print axioms Nock.RedTeam.Batch783.honest_fill_topPinU1
#print axioms Nock.RedTeam.Batch783.honest_u1_at_769
#print axioms Nock.RedTeam.Batch783.honest_u1_at_goldilocks
