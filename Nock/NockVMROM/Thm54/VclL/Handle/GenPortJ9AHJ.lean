/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHJ.lean

  For `I = recJ9AX s f χe t r` (the explicit record of `genJ9AX_some`):
  * `recJ9AX_nJ`: `I.J.n = 0`;  `recJ9AX_pubsJ`: `I.M.pubsJ i = 0`, `recJ9AX_toMsg_pubsJ`: `I.toMsg.pubsJ i = 0`;
  * `recJ9AX_jchip`: `JChipOK` (absent branch) at `mkPbA I hv`, at the exec message/trace;
  * `recJ9AX_lay`: `List.ofFn (mkPbA I hv).lay = []` and `= layoutJ8 Rt regs ids`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRun
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Static

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJ

open Nock Nock.Field Nock.TraceGenExe Nock.Edit Nock.Edit.GenX Nock.Walk Nock.V1J8 Nock.V1J8.Gen Nock.V1J8.Exe
open Nock.V1J8.Check Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff Nock.V1J9A.GenJ9AX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRun

theorem recJ9AX_nJ (s f : Noun) (χe : CoinsE) (t : NTree SkelX) (r : Noun) :
    (recJ9AX s f χe t r).J.n = 0 := rfl

theorem recJ9AX_pubsJ (s f : Noun) (χe : CoinsE) (t : NTree SkelX) (r : Noun) (i : ℕ) :
    (recJ9AX s f χe t r).M.pubsJ i = 0 := rfl

theorem recJ9AX_toMsg_pubsJ (s f : Noun) (χe : CoinsE) (t : NTree SkelX) (r : Noun) (i : ℕ) :
    (recJ9AX s f χe t r).toMsg.pubsJ i = 0 := by
  have h : (recJ9AX s f χe t r).M.pubsJ i = 0 := rfl
  simp [InJ9A.toMsg, MsgE.toMsg, h, K3.toK_zero]

theorem recJ9AX_jchip (s f : Noun) (χe : CoinsE) (t : NTree SkelX) (r : Noun)
    (hv : ValidJ9A (recJ9AX s f χe t r)) :
    JGenJ8.JChipOK deltaF powerBasis3 (mkPbA (recJ9AX s f χe t r) hv).nodesJ
      (mkPbA (recJ9AX s f χe t r) hv).orbitJ (chalsJJ8 (toχ (recJ9AX s f χe t r).χ))
      (recJ9AX s f χe t r).toMsg.pubsJ (mkPbA (recJ9AX s f χe t r) hv).lay
      (qJ deltaF powerBasis3 (mkPbA (recJ9AX s f χe t r) hv).toPubJ8 (recJ9AX s f χe t r).toTr.toJ8
        (chalsJJ8 (toχ (recJ9AX s f χe t r).χ)) (recJ9AX s f χe t r).toMsg.pubsJ) :=
  Or.inr ⟨rfl, recJ9AX_toMsg_pubsJ .., recJ9AX_toMsg_pubsJ .., recJ9AX_toMsg_pubsJ .., recJ9AX_toMsg_pubsJ ..⟩

theorem recJ9AX_lay (s f : Noun) (χe : CoinsE) (t : NTree SkelX) (r : Noun)
    (hv : ValidJ9A (recJ9AX s f χe t r)) :
    List.ofFn (mkPbA (recJ9AX s f χe t r) hv).lay = [] ∧
    List.ofFn (mkPbA (recJ9AX s f χe t r) hv).lay =
      Nock.Jet.ChipJ8.layoutJ8 (mkPbA (recJ9AX s f χe t r) hv).Rt (mkPbA (recJ9AX s f χe t r) hv).regs
        (mkPbA (recJ9AX s f χe t r) hv).ids := by
  have h0 : List.ofFn (mkPbA (recJ9AX s f χe t r) hv).lay = [] :=
    List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn]; rfl)
  refine ⟨h0, h0.trans ?_⟩
  exact (InhabJ8Static.layout_nil _).symm.trans (by rfl)

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJ

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJ.recJ9AX_nJ
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJ.recJ9AX_pubsJ
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJ.recJ9AX_toMsg_pubsJ
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJ.recJ9AX_jchip
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJ.recJ9AX_lay
