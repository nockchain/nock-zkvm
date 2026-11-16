/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHStaticJ.lean

  `StaticHypJ I m` is `GenPortJ9AHStatic.StaticHyp` with `g = regs.length` and `J.n ≤ m` in place of
  `g = 0`, `J.n = 0`, `regs = []`. Proves
  * `budJ9A_staticJ : BudJ9A (mkPbA I hv) I.toRows (I.g + max 10 (2m))` (the `jCount` terms are `≤ J.n ≤ m`:
    every kind occurs at most once in each slot list);
  * `hbudV_staticJ`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStatic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStaticJ

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Check Nock.V1J8.Gen Nock.V1J9A
open Nock.V1J9A.CheckJ9AIff Nock.V1J9A.CheckJ9A
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8 (jCount)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A (BudJ9A)
open Nock.Jet.ChipJ8 (keysOf entsX ents0T ents1T ents2T ents3 Kd KE PRow)

/-- Every kind occurs at most once in each slot list. -/
theorem ents0T_one : ∀ kd : Kd, (ents0T.filter fun e => e.1 == kd).length ≤ 1 := by
  intro kd; cases kd <;> decide
theorem ents1T_one : ∀ kd : Kd, (ents1T.filter fun e => e.1 == kd).length ≤ 1 := by
  intro kd; cases kd <;> decide
theorem ents2T_one : ∀ kd : Kd, (ents2T.filter fun e => e.1 == kd).length ≤ 1 := by
  intro kd; cases kd <;> decide
theorem ents3_one : ∀ kd : Kd, (ents3.filter fun e => e.1 == kd).length ≤ 1 := by
  intro kd; cases kd <;> decide
theorem entsX_one : ∀ kd : Kd, (entsX.filter fun e => e.1 == kd).length ≤ 1 := by
  intro kd; cases kd <;> decide

theorem jCount_le (es : List (Kd × List KE)) (hes : ∀ kd : Kd, (es.filter fun e => e.1 == kd).length ≤ 1)
    {n : ℕ} (lay : Fin n → PRow) : jCount es lay ≤ n := by
  unfold jCount
  have := List.sum_le_card_nsmul ((List.finRange n).map fun i => (es.filter fun e => e.1 == (lay i).kd).length) 1
    (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact hes _)
  simpa using this

/-- The static block hypotheses at jets: the budget shape and the size bounds. -/
structure StaticHypJ (I : InJ9A) (m : ℕ) : Prop where
  hr : I.r = budget m
  hg : I.g = I.regs.length
  hAX : I.rAX = max 10 (2 * m)
  hSP : I.rSP = max 10 (2 * m)
  hJ : I.J.n ≤ m
  sX : I.X.n ≤ m
  sC : I.C.n ≤ m
  sW : I.W.n ≤ m
  sA : I.A.n ≤ m
  sV : I.V.n ≤ m
  sAX : I.AX.n ≤ m
  sSP : I.SP.n ≤ m

/-- **`BudJ9A` at `g + B`** for the jet record. -/
theorem budJ9A_staticJ (I : InJ9A) (hv : ValidJ9A I) (m : ℕ) (H : StaticHypJ I m) :
    BudJ9A (mkPbA I hv) I.toRows (I.g + (max 10 (2 * m))) := by
  have fnJ : (mkPbA I hv).nJ = I.J.n := rfl
  have hj : ∀ es : List (Kd × List KE), (∀ kd : Kd, (es.filter fun e => e.1 == kd).length ≤ 1) →
      jCount es (mkPbA I hv).lay ≤ m := fun es hes =>
    (jCount_le es hes (mkPbA I hv).lay).trans (by rw [fnJ]; exact H.hJ)
  have jX := hj entsX entsX_one
  have j0 := hj ents0T ents0T_one
  have j1 := hj ents1T ents1T_one
  have j2 := hj ents2T ents2T_one
  have j3 := hj ents3 ents3_one
  have hN : I.toRows.N = max 10 (2 * m) := by
    show I.r.N = _; rw [H.hr]; rfl
  have e1 : I.toRows.W = max 10 (2 * m) := by show I.r.W = _; rw [H.hr]; rfl
  have e2 : I.toRows.rd = max 10 (2 * m) := by show I.r.rd = _; rw [H.hr]; rfl
  have e3 : I.toRows.D = max 10 (2 * m) := by show I.r.D = _; rw [H.hr]; rfl
  have e4 : I.toRows.J = max 10 (2 * m) := by show I.r.J = _; rw [H.hr]; rfl
  have e5 : I.toRows.calls = max 10 (2 * m) := by show I.r.calls = _; rw [H.hr]; rfl
  have e6 : I.toRows.heads = max 10 (2 * m) := by show I.r.heads = _; rw [H.hr]; rfl
  have e7 : I.toRows.blocks = max 10 (2 * m) := by show I.r.blocks = _; rw [H.hr]; rfl
  have e8 : I.toRows.AX = max 10 (2 * m) := H.hAX
  have e9 : I.toRows.SP = max 10 (2 * m) := H.hSP
  have hreg : (mkPbA I hv).regs.length = I.g := by
    show I.regs.length = I.g; exact H.hg.symm
  have fn : (mkPbA I hv).n = I.X.n := rfl
  have fnC : (mkPbA I hv).nC = I.C.n := rfl
  have fnW : (mkPbA I hv).nW = I.W.n := rfl
  have fnA : (mkPbA I hv).nA = I.A.n := rfl
  have fnV : (mkPbA I hv).nV = I.V.n := rfl
  have fnX : (mkPbA I hv).nX = I.AX.n := rfl
  have fnS : (mkPbA I hv).nS = I.SP.n := rfl
  have sX := H.sX; have sC := H.sC; have sW := H.sW; have sA := H.sA
  have sV := H.sV; have sAX := H.sAX; have sSP := H.sSP
  have hB1 : 10 ≤ max 10 (2 * m) := le_max_left _ _
  have hB2 : 2 * m ≤ max 10 (2 * m) := le_max_right _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hN, e1, e2, fn, fnW]; omega
  · rw [e3, fnC]; omega
  · rw [hN, fn, fnX]; omega
  · rw [e1, fnW]; omega
  · rw [hN, e4, e8, hreg, fn, fnX]; omega
  · rw [e5, e6, e7, e4, e8, e9, fnA, fnV, fnX, fnS]; omega

/-- **`hbudV` at jets** (`g = regs.length`, `r = I.toRows`). -/
theorem hbudV_staticJ (I : InJ9A) (hv : ValidJ9A I) (m : ℕ) (H : StaticHypJ I m) :
    (mkPbA I hv).regs.length ≤ I.g ∧ (mkPbA I hv).nA ≤ I.toRows.mb ∧ (mkPbA I hv).nA ≤ I.toRows.A ∧
      (mkPbA I hv).nV ≤ I.toRows.AW ∧ (mkPbA I hv).nX ≤ I.toRows.AX ∧ (mkPbA I hv).nS ≤ I.toRows.SP := by
  have hreg : (mkPbA I hv).regs.length = I.g := by
    show I.regs.length = I.g; exact H.hg.symm
  have e1 : I.toRows.mb = max 10 (2 * m) := by show I.r.mb = _; rw [H.hr]; rfl
  have e2 : I.toRows.A = max 10 (2 * m) := by show I.r.A = _; rw [H.hr]; rfl
  have e3 : I.toRows.AW = max 10 (2 * m) := by show I.r.AW = _; rw [H.hr]; rfl
  have e8 : I.toRows.AX = max 10 (2 * m) := H.hAX
  have e9 : I.toRows.SP = max 10 (2 * m) := H.hSP
  have fnA : (mkPbA I hv).nA = I.A.n := rfl
  have fnV : (mkPbA I hv).nV = I.V.n := rfl
  have fnX : (mkPbA I hv).nX = I.AX.n := rfl
  have fnS : (mkPbA I hv).nS = I.SP.n := rfl
  have sA := H.sA; have sV := H.sV; have sAX := H.sAX; have sSP := H.sSP
  have hB2 : 2 * m ≤ max 10 (2 * m) := le_max_right _ _
  have hB1 : 10 ≤ max 10 (2 * m) := le_max_left _ _
  refine ⟨hreg.le, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, fnA]; omega
  · rw [e2, fnA]; omega
  · rw [e3, fnV]; omega
  · rw [e8, fnX]; omega
  · rw [e9, fnS]; omega

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStaticJ

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStaticJ.ents0T_one
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStaticJ.ents1T_one
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStaticJ.ents2T_one
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStaticJ.ents3_one
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStaticJ.entsX_one
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStaticJ.jCount_le
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStaticJ.budJ9A_staticJ
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStaticJ.hbudV_staticJ
