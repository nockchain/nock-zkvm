/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHStaticJ.lean

  **the static budget block of the J9AL generator record** (twin of `GenPortJ9AHStaticJ`). NOT a rfl transfer: `StaticHypJL I m` states, abstractly over the field shapes the
  generator `GenJ9ALXJ` produces (`r = budget m`, `rAX = rSP = rAL = B := max 10 (2m)`, `g = regs.length`, every
  chip's row count `≤ m`, where `m` is the max over all nine row counts INCLUDING `lR.size`), and proves
  * `budJ9AL_staticJ : BudJ9AL (mkPbAL I hv) I.toRowsL (I.g + max 10 (2m))` (the `g + r.N` argument, `r.N = B`);
  * `hbudV_staticJL` (the `hbudV` conjunct of `AcceptsJ9AL`, with `nL ≤ r.AL`).
  Nothing here names the generator record.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStaticJ
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL
import Nock.V1J9AL.CheckJ9ALIff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaticJ

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Check Nock.V1J8.Gen Nock.V1J9A
open Nock.V1J9A.CheckJ9AIff Nock.V1J9A.CheckJ9A
open Nock.V1J9AL.CheckJ9AL Nock.V1J9AL.CheckJ9ALIff
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8 (jCount)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL (BudJ9AL)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStaticJ
open Nock.Jet.ChipJ8 (keysOf entsX ents0T ents1T ents2T ents3 Kd KE PRow)

/-- The J9A static hypotheses (budget shape, `g = regs.length`, row-count bounds) plus the ALU's: `rAL = B` and
`AL.n ≤ m`. -/
structure StaticHypJL (I : InJ9AL) (m : ℕ) : Prop extends StaticHypJ I.toInJ9A m where
  hAL : I.rAL = max 10 (2 * m)
  sAL : I.AL.n ≤ m

/-- **`BudJ9AL` at `g + B`** for the J9AL record. -/
theorem budJ9AL_staticJ (I : InJ9AL) (hv : ValidJ9AL I) (m : ℕ) (H : StaticHypJL I m) :
    BudJ9AL (mkPbAL I hv) I.toRowsL (I.g + (max 10 (2 * m))) := by
  have fnJ : (mkPbAL I hv).nJ = I.J.n := rfl
  have hj : ∀ es : List (Kd × List KE), (∀ kd : Kd, (es.filter fun e => e.1 == kd).length ≤ 1) →
      jCount es (mkPbAL I hv).lay ≤ m := fun es hes =>
    (jCount_le es hes (mkPbAL I hv).lay).trans (by rw [fnJ]; exact H.hJ)
  have jX := hj entsX entsX_one
  have j0 := hj ents0T ents0T_one
  have j1 := hj ents1T ents1T_one
  have j2 := hj ents2T ents2T_one
  have j3 := hj ents3 ents3_one
  have e0 : I.toRowsL.N = max 10 (2 * m) := by
    show I.r.N = _; rw [H.hr]; rfl
  have e1 : I.toRowsL.W = max 10 (2 * m) := by show I.r.W = _; rw [H.hr]; rfl
  have e2 : I.toRowsL.rd = max 10 (2 * m) := by show I.r.rd = _; rw [H.hr]; rfl
  have e3 : I.toRowsL.D = max 10 (2 * m) := by show I.r.D = _; rw [H.hr]; rfl
  have e4 : I.toRowsL.J = max 10 (2 * m) := by show I.r.J = _; rw [H.hr]; rfl
  have e5 : I.toRowsL.calls = max 10 (2 * m) := by show I.r.calls = _; rw [H.hr]; rfl
  have e6 : I.toRowsL.heads = max 10 (2 * m) := by show I.r.heads = _; rw [H.hr]; rfl
  have e7 : I.toRowsL.blocks = max 10 (2 * m) := by show I.r.blocks = _; rw [H.hr]; rfl
  have e8 : I.toRowsL.AX = max 10 (2 * m) := H.hAX
  have e9 : I.toRowsL.SP = max 10 (2 * m) := H.hSP
  have e10 : I.toRowsL.AL = max 10 (2 * m) := H.hAL
  have hreg : (mkPbAL I hv).regs.length = I.g := by
    show I.regs.length = I.g; exact H.hg.symm
  have fn : (mkPbAL I hv).n = I.X.n := rfl
  have fnC : (mkPbAL I hv).nC = I.C.n := rfl
  have fnW : (mkPbAL I hv).nW = I.W.n := rfl
  have fnA : (mkPbAL I hv).nA = I.A.n := rfl
  have fnV : (mkPbAL I hv).nV = I.V.n := rfl
  have fnX : (mkPbAL I hv).nX = I.AX.n := rfl
  have fnS : (mkPbAL I hv).nS = I.SP.n := rfl
  have fnL : (mkPbAL I hv).nL = I.AL.n := rfl
  have sX := H.sX; have sC := H.sC; have sW := H.sW; have sA := H.sA
  have sV := H.sV; have sAX := H.sAX; have sSP := H.sSP; have sAL := H.sAL
  have hB1 : 10 ≤ max 10 (2 * m) := le_max_left _ _
  have hB2 : 2 * m ≤ max 10 (2 * m) := le_max_right _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0, e1, e2, e10, fn, fnW, fnL]; omega
  · rw [e3, fnC]; omega
  · rw [e0, fn, fnX]; omega
  · rw [e1, fnW]; omega
  · rw [e0, e4, e8, e10, hreg, fn, fnX, fnL]; omega
  · rw [e5, e6, e7, e4, e8, e9, e10, fnA, fnV, fnX, fnS, fnL]; omega

/-- **`hbudV` at J9AL** (`g = regs.length`, `r = I.toRowsL`, with `nL ≤ r.AL`). -/
theorem hbudV_staticJL (I : InJ9AL) (hv : ValidJ9AL I) (m : ℕ) (H : StaticHypJL I m) :
    (mkPbAL I hv).regs.length ≤ I.g ∧ (mkPbAL I hv).nA ≤ I.toRowsL.mb ∧ (mkPbAL I hv).nA ≤ I.toRowsL.A ∧
      (mkPbAL I hv).nV ≤ I.toRowsL.AW ∧ (mkPbAL I hv).nX ≤ I.toRowsL.AX ∧ (mkPbAL I hv).nS ≤ I.toRowsL.SP ∧
      (mkPbAL I hv).nL ≤ I.toRowsL.AL := by
  have hreg : (mkPbAL I hv).regs.length = I.g := by
    show I.regs.length = I.g; exact H.hg.symm
  have e1 : I.toRowsL.mb = max 10 (2 * m) := by show I.r.mb = _; rw [H.hr]; rfl
  have e2 : I.toRowsL.A = max 10 (2 * m) := by show I.r.A = _; rw [H.hr]; rfl
  have e3 : I.toRowsL.AW = max 10 (2 * m) := by show I.r.AW = _; rw [H.hr]; rfl
  have e8 : I.toRowsL.AX = max 10 (2 * m) := H.hAX
  have e9 : I.toRowsL.SP = max 10 (2 * m) := H.hSP
  have e10 : I.toRowsL.AL = max 10 (2 * m) := H.hAL
  have fnA : (mkPbAL I hv).nA = I.A.n := rfl
  have fnV : (mkPbAL I hv).nV = I.V.n := rfl
  have fnX : (mkPbAL I hv).nX = I.AX.n := rfl
  have fnS : (mkPbAL I hv).nS = I.SP.n := rfl
  have fnL : (mkPbAL I hv).nL = I.AL.n := rfl
  have sA := H.sA; have sV := H.sV; have sAX := H.sAX; have sSP := H.sSP; have sAL := H.sAL
  have hB2 : 2 * m ≤ max 10 (2 * m) := le_max_right _ _
  have hB1 : 10 ≤ max 10 (2 * m) := le_max_left _ _
  refine ⟨hreg.le, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, fnA]; omega
  · rw [e2, fnA]; omega
  · rw [e3, fnV]; omega
  · rw [e8, fnX]; omega
  · rw [e9, fnS]; omega
  · rw [e10, fnL]; omega

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaticJ

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaticJ.budJ9AL_staticJ
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaticJ.hbudV_staticJL
