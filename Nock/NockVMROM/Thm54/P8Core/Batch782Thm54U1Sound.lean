/-
  Nock/NockVMROM/Thm54/P8Core/Batch782Thm54U1Sound.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch782Thm54U1Sound`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch782Thm54U1Sound.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackageDefs
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Nock.RedTeam.Batch782

open scoped Classical
open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.CoordinateCompiler
variable {F : Type*} [Field F]

noncomputable def topPinU1 : CoeffExpr F :=
  .sub colTop (.mul (.mul (.mul colP (lm 2)) (lm 1)) (lm 0))

theorem topPinU1_eval (env : Env F) :
    (topPinU1 (F := F)).eval env =
      env.trace (col0 + 72) - env.trace (col0 + 71) * (lm (F := F) 2).eval env *
        (lm (F := F) 1).eval env * (lm (F := F) 0).eval env := by
  simp [topPinU1, colTop, colP, bcur, CoeffExpr.eval]

noncomputable def rowShift (env : Env F) : ℕ :=
  ∑ k ∈ Finset.range 6, if env.trace (265 + k) = 1 then 2 ^ k else 0

theorem testBit_sum6 (c : ℕ → Bool) (k : ℕ) (hk : k < 6) :
    (∑ i ∈ Finset.range 6, if c i then 2 ^ i else 0).testBit k = c k := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  cases h0 : c 0 <;> cases h1 : c 1 <;> cases h2 : c 2 <;> cases h3 : c 3 <;>
    cases h4 : c 4 <;> cases h5 : c 5 <;>
    interval_cases k <;> simp_all <;> decide

theorem sum6_lt (c : ℕ → Bool) : (∑ i ∈ Finset.range 6, if c i then 2 ^ i else 0) < 64 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  cases c 0 <;> cases c 1 <;> cases c 2 <;> cases c 3 <;> cases c 4 <;> cases c 5 <;> decide

/-- Shift columns of a row where every `m_k` is boolean, as `bit01` of the shift's bits. -/
theorem shift_cols_of_boolean (env : Env F)
    (hb : ∀ k, k < 6 → (bbool (colM (F := F) k)).eval env = 0) :
    rowShift env < 64 ∧
      ∀ k, k < 6 → env.trace (col0 + 63 + k) = bit01 ((rowShift env).testBit k) := by
  have hrw : rowShift env =
      ∑ i ∈ Finset.range 6, if decide (env.trace (265 + i) = 1) then 2 ^ i else 0 := by
    unfold rowShift
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : env.trace (265 + i) = 1 <;> simp [h]
  refine ⟨hrw ▸ sum6_lt _, fun k hk => ?_⟩
  rw [hrw, testBit_sum6 _ k hk]
  have h := hb k hk
  simp only [bbool, colM, bcur, CoeffExpr.eval, col0] at h
  have h' : env.trace (202 + 63 + k) = 0 ∨ env.trace (202 + 63 + k) = 1 := by
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have e : 202 + 63 + k = 265 + k := by omega
  simp only [col0, e] at h' ⊢
  rcases h' with h0 | h1
  · rw [h0]; simp [bit01]
  · rw [h1]; simp [bit01]

/-- The range terms read no `top` column: they agree on two rows that agree off column `274`. -/
theorem rangeSum_congr (env env' : Env F)
    (h : ∀ i, i ≠ col0 + 72 → env'.trace i = env.trace i) :
    (sumExpr (rangeTerms (F := F))).eval env' = (sumExpr (rangeTerms (F := F))).eval env := by
  have hm : ∀ k, k < 6 → env'.trace (col0 + 63 + k) = env.trace (col0 + 63 + k) :=
    fun k hk => h _ (by simp only [col0]; omega)
  have hP : env'.trace (col0 + 71) = env.trace (col0 + 71) := h _ (by simp only [col0]; omega)
  have hlm : ∀ k, k < 6 → (lm (F := F) k).eval env' = (lm (F := F) k).eval env := by
    intro k hk; rw [lm_eval, lm_eval, hm k hk]
  have hc : ∀ b : Bool, (if b = true then CoeffExpr.const 1 else CoeffExpr.const 0 :
      CoeffExpr F).eval env' = (if b = true then CoeffExpr.const 1 else CoeffExpr.const 0 :
      CoeffExpr F).eval env := by
    intro b; cases b <;> rfl
  simp only [rangeTerms, List.range, List.range.loop, List.map, sumExpr, rangeTerm, eqmAt,
    CoeffExpr.eval, colP, colM, bcur]
  rw [hlm 1 (by decide), hlm 2 (by decide), hlm 4 (by decide), hlm 5 (by decide), hP,
    hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide), hm 4 (by decide),
    hm 5 (by decide), hc, hc, hc, hc, hc, hc]

theorem rangeGate_eval_split (env : Env F) :
    (rangeGate (F := F)).eval env =
      (sumExpr (rangeTerms (F := F))).eval env + env.trace (col0 + 72) - 1 := by
  simp [rangeGate, colTop, bcur, CoeffExpr.eval]

/-- **U1 IS SOUND FOR THE SHIFT, at every width, no hypothesis on the field.**  On any row where
the six shift bits are boolean, `pPin` and the U1 `topPin` hold and the deployed `rangeGate`
holds, the decoded 6-bit shift is `≤ (n − 1) mod 64`. -/
theorem shift_le_nMinus1Low (env : Env F)
    (hb : ∀ k, k < 6 → (bbool (colM (F := F) k)).eval env = 0)
    (hp : (pPin (F := F)).eval env = 0)
    (ht : (topPinU1 (F := F)).eval env = 0)
    (hr : (rangeGate (F := F)).eval env = 0) :
    rowShift env ≤ nMinus1Low F := by
  obtain ⟨hm64, hM⟩ := shift_cols_of_boolean env hb
  set m := rowShift env with hmdef
  have hlm : ∀ k, k < 6 → (lm (F := F) k).eval env = matchedLm F m k := by
    intro k hk; rw [lm_eval, hM k hk]; unfold matchedLm; split_ifs <;> rfl
  have hP : env.trace (col0 + 71) = matchedP F m := by
    have h := hp
    simp only [pPin, colP, bcur, CoeffExpr.eval] at h
    rw [hlm 5 (by decide), hlm 4 (by decide), hlm 3 (by decide)] at h
    unfold matchedP; exact sub_eq_zero.mp h
  have hTop : env.trace (col0 + 72) = matchedTop F m := by
    have h := ht
    rw [topPinU1_eval, hlm 2 (by decide), hlm 1 (by decide), hlm 0 (by decide), hP] at h
    unfold matchedTop; exact sub_eq_zero.mp h
  have hN : nMinus1Low F < 64 := Nat.mod_lt _ (by decide)
  by_contra hgt
  have hgt : nMinus1Low F < m := Nat.lt_of_not_ge hgt
  have h0 : matchedTop F m = 0 := by
    refine matchedTop_eq_zero_of_ne m fun hall => ?_
    have : m = nMinus1Low F := eq_of_low6_testBit hm64 hN fun k hk => by
      rw [hall k hk, nMinus1Low_testBit k hk]
    omega
  let env' : Env F :=
    ⟨fun i => if i = col0 + 72 then 1 else env.trace i, env.traceNext, env.chal, env.pub⟩
  have hagree : ∀ i, i ≠ col0 + 72 → env'.trace i = env.trace i := fun i hi => by
    simp [env', hi]
  have hR' : (rangeGate (F := F)).eval env' = 0 :=
    rangeGate_eval_of_gt_top1 env' m hm64 hN hgt
      (fun k hk => by rw [hagree _ (by simp [col0]; omega)]; exact hM k hk)
      (by rw [hagree _ (by simp [col0])]; exact hP) (by simp [env'])
  rw [rangeGate_eval_split, rangeSum_congr env env' hagree] at hR'
  rw [rangeGate_eval_split, hTop, h0] at hr
  have h1 : env'.trace (col0 + 72) = 1 := by simp [env']
  rw [h1] at hR'
  have : (sumExpr (rangeTerms (F := F))).eval env = 0 := by linear_combination hR'
  rw [this] at hr
  norm_num at hr

/-- With `nMinus1Low ≤ formRN − 1` (unconditional): the shift is in range. -/
theorem shift_le_formRN_pred (env : Env F)
    (hb : ∀ k, k < 6 → (bbool (colM (F := F) k)).eval env = 0)
    (hp : (pPin (F := F)).eval env = 0)
    (ht : (topPinU1 (F := F)).eval env = 0)
    (hr : (rangeGate (F := F)).eval env = 0) :
    rowShift env ≤ formRN F - 1 :=
  (shift_le_nMinus1Low env hb hp ht hr).trans nMinus1Low_le_pred_formRN

end Nock.RedTeam.Batch782
