/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHStatic.lean

  For an input `I` with `I.r = budget m`, `I.g = 0`, `I.rAX = I.rSP = max 10 (2m)`, J absent,
  `I.regs = []` and every chip table of size `≤ m`, proves directly (no transport from `canonRows`):
  * `budJ9A_static : BudJ9A (mkPbA I hv) I.toRows (0 + B)`;
  * `hbudV_static : (mkPbA I hv).regs.length ≤ 0 ∧ nA ≤ mb ∧ nA ≤ A ∧ nV ≤ AW ∧ nX ≤ AX ∧ nS ≤ SP`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStatic

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Check Nock.V1J8.Gen Nock.V1J9A
open Nock.V1J9A.CheckJ9AIff Nock.V1J9A.CheckJ9A
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8 (jCount)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A (BudJ9A)
open Nock.Jet.ChipJ8 (keysOf entsX ents0T ents1T ents2T ents3 Kd KE PRow)

/-- `jCount` over an empty layout vanishes. -/
theorem jCount_nil (es : List (Kd × List KE)) {n : ℕ} (lay : Fin n → PRow) (h : n = 0) :
    jCount es lay = 0 := by
  subst h; rfl

/-- The static block hypotheses: the budget shape and the size bounds. -/
structure StaticHyp (I : InJ9A) (m : ℕ) : Prop where
  hr : I.r = budget m
  hg : I.g = 0
  hAX : I.rAX = max 10 (2 * m)
  hSP : I.rSP = max 10 (2 * m)
  hJ : I.J.n = 0
  hregs : I.regs = []
  sX : I.X.n ≤ m
  sC : I.C.n ≤ m
  sW : I.W.n ≤ m
  sA : I.A.n ≤ m
  sV : I.V.n ≤ m
  sAX : I.AX.n ≤ m
  sSP : I.SP.n ≤ m

/-- **E1a: `BudJ9A` at `0 + B`.** -/
theorem budJ9A_static (I : InJ9A) (hv : ValidJ9A I) (m : ℕ) (H : StaticHyp I m) :
    BudJ9A (mkPbA I hv) I.toRows (0 + (max 10 (2 * m))) := by
  have hj : ∀ es, jCount es (mkPbA I hv).lay = 0 := fun es => jCount_nil es _ H.hJ
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
  have hreg : (mkPbA I hv).regs.length = 0 := by
    show I.regs.length = 0; rw [H.hregs]; rfl
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
  · rw [hj, hN, e1, e2, fn, fnW]; omega
  · rw [e3, fnC]; omega
  · rw [hN, fn, fnX]; omega
  · rw [e1, fnW]; omega
  · rw [hj, hj, hN, e4, e8, hreg, fn, fnX]; omega
  · rw [hj, hj, e5, e6, e7, e4, e8, e9, fnA, fnV, fnX, fnS]; omega

/-- **E1b: `hbudV`** (`g = 0`, `r = I.toRows`). -/
theorem hbudV_static (I : InJ9A) (hv : ValidJ9A I) (m : ℕ) (H : StaticHyp I m) :
    (mkPbA I hv).regs.length ≤ 0 ∧ (mkPbA I hv).nA ≤ I.toRows.mb ∧ (mkPbA I hv).nA ≤ I.toRows.A ∧
      (mkPbA I hv).nV ≤ I.toRows.AW ∧ (mkPbA I hv).nX ≤ I.toRows.AX ∧ (mkPbA I hv).nS ≤ I.toRows.SP := by
  have hreg : (mkPbA I hv).regs.length = 0 := by
    show I.regs.length = 0; rw [H.hregs]; rfl
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
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, fnA]; omega
  · rw [e2, fnA]; omega
  · rw [e3, fnV]; omega
  · rw [e8, fnX]; omega
  · rw [e9, fnS]; omega

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStatic

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStatic.jCount_nil
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStatic.budJ9A_static
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStatic.hbudV_static
