/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHLinkJ.lean

  The link for the jet-calling record: `ExecLinkJ` bundles the field-shape equations that the generic chip ports take as
  hypotheses, and `execLink_recJ9AXJ` discharges them at `recJ9AXJ`.  No `hnc`. -/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsgJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStaticJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHLinkJ

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 rowsOfT9 genX9T)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf cellsA_pos acsA_pos)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
  (BRun9A W9 N9 idOfA axOnA spOnA Rows31A)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj (RnOf)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (OrbJ9A withOrb)
open Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.GenJ9AX Nock.V1J9A.GenCompX9

variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]

/-- The link: every field-shape equation the chip ports take, for the record `I`. -/
structure ExecLinkJ {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ}
    {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
    (hpG : P = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf P Rg Rt hgen)) (χe : CoinsE) (I : InJ9A) : Prop where
  hC : I.C = chipOf (cellGenB (coOf χe) (yE χe) (hdlB (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs)
      (bigIdOf (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells
      (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx
      (Array.replicate (j9aDataOf P Rg Rt hgen).cells.length 0) (j9aDataOf P Rg Rt hgen).mh).1
  hpC : I.M.pubsC = (cellGenB (coOf χe) (yE χe) (hdlB (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs)
      (bigIdOf (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells
      (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx
      (Array.replicate (j9aDataOf P Rg Rt hgen).cells.length 0) (j9aDataOf P Rg Rt hgen).mh).2
  hW : I.W = chipOf (walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1)
      (GenPortJ9AHWalkRun.regD (j9aDataOf P Rg Rt hgen)).H (idxN (GenPortJ9AHWalkRun.regD (j9aDataOf P Rg Rt hgen)).cells)
      HonestK8.certB8 (GenPortJ9AHWalkRun.regD (j9aDataOf P Rg Rt hgen)).cells
      ((walkRows (GenPortJ9AHWalkRun.regD (j9aDataOf P Rg Rt hgen)).cells
        (GenPortJ9AHWalkRun.regD (j9aDataOf P Rg Rt hgen)).reads).map GenPortJ9AHWalkRow.wrowOf)
      (krW (GenPortJ9AHWalkRun.regD (j9aDataOf P Rg Rt hgen)).cells
        (GenPortJ9AHWalkRun.regD (j9aDataOf P Rg Rt hgen)).reads)).1
  hpW : I.M.pubsW = (walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1)
      (GenPortJ9AHWalkRun.regD (j9aDataOf P Rg Rt hgen)).H (idxN (GenPortJ9AHWalkRun.regD (j9aDataOf P Rg Rt hgen)).cells)
      HonestK8.certB8 (GenPortJ9AHWalkRun.regD (j9aDataOf P Rg Rt hgen)).cells
      ((walkRows (GenPortJ9AHWalkRun.regD (j9aDataOf P Rg Rt hgen)).cells
        (GenPortJ9AHWalkRun.regD (j9aDataOf P Rg Rt hgen)).reads).map GenPortJ9AHWalkRow.wrowOf)
      (krW (GenPortJ9AHWalkRun.regD (j9aDataOf P Rg Rt hgen)).cells
        (GenPortJ9AHWalkRun.regD (j9aDataOf P Rg Rt hgen)).reads)).2
  hkr : I.kroots = krW (GenPortJ9AHWalkRun.regD (j9aDataOf P Rg Rt hgen)).cells
        (GenPortJ9AHWalkRun.regD (j9aDataOf P Rg Rt hgen)).reads
  hA : I.A = chipOf (atomGenE (ComplJ8Data.ptrP P (j9aDataOf P Rg Rt hgen).acs (j9aDataOf P Rg Rt hgen).rows) χe
      (j9aDataOf P Rg Rt hgen).acs (j9aDataOf P Rg Rt hgen).info (j9aDataOf P Rg Rt hgen).mb
      (j9aDataOf P Rg Rt hgen).mxA (j9aDataOf P Rg Rt hgen).mhA).1
  hpA : I.M.pubsA = (atomGenE (ComplJ8Data.ptrP P (j9aDataOf P Rg Rt hgen).acs (j9aDataOf P Rg Rt hgen).rows) χe
      (j9aDataOf P Rg Rt hgen).acs (j9aDataOf P Rg Rt hgen).info (j9aDataOf P Rg Rt hgen).mb
      (j9aDataOf P Rg Rt hgen).mxA (j9aDataOf P Rg Rt hgen).mhA).2
  hVon : (j9aDataOf P Rg Rt hgen).preads ≠ [] →
      I.V = chipOf (GenPortJ9AHAW.awE χe (GenPortJ9AHAWOrd.regV (j9aDataOf P Rg Rt hgen))).1 ∧
        I.M.pubsV = (GenPortJ9AHAW.awE χe (GenPortJ9AHAWOrd.regV (j9aDataOf P Rg Rt hgen))).2
  hVoff : (j9aDataOf P Rg Rt hgen).preads = [] →
      I.V = chipOf #[Array.replicate 166 0] ∧ I.M.pubsV = fun _ => 0
  hkrV : I.krootsV = ComplJ8Of.krVOf (j9aDataOf P Rg Rt hgen)
  hc : I.c = ⟨s, f, r⟩
  hχI : I.χ = χe
  hX : I.X = chipOf (GenCompX9.compGenX9 ⟨s, f, r⟩ (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
      (idOfA (p := P) Rt hgen) (W9 t) χe).rows
  hm : I.toMsg.m = ((BRun9A deltaF powerBasis3 Rt hgen hpG h31A).M (toχ χe)).m
  hρ : I.toMsg.ρ = ((BRun9A deltaF powerBasis3 Rt hgen hpG h31A).M (toχ χe)).ρ
  hρS : I.toMsg.ρS = ((BRun9A deltaF powerBasis3 Rt hgen hpG h31A).M (toχ χe)).ρS
  hAX : I.AX = chipOf (GenAxE.axGenOf χe (j9aDataOf P Rg Rt hgen).acs.length (j9aDataOf P Rg Rt hgen).H
      (rowsOfT9 t) (axOnA t)).1
  hpX : I.pubsX = (GenAxE.axGenOf χe (j9aDataOf P Rg Rt hgen).acs.length (j9aDataOf P Rg Rt hgen).H
      (rowsOfT9 t) (axOnA t)).2
  haxOn : I.axOn = axOnA t
  hszAX : I.AX.n = (BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Pb.nX
  hSPon : spOnA P t = true →
      I.SP = chipOf (GenSpE.spGenE χe (j9aDataOf P Rg Rt hgen).acs.length (GenSpE.vSE (rowsOfT9 t))
        (GenSpE.mSE (rowsOfT9 t) (GenSpE.vSE (rowsOfT9 t)))).1 ∧
      I.pubsS = (GenSpE.spGenE χe (j9aDataOf P Rg Rt hgen).acs.length (GenSpE.vSE (rowsOfT9 t))
        (GenSpE.mSE (rowsOfT9 t) (GenSpE.vSE (rowsOfT9 t)))).2
  hSPoff : ¬ spOnA P t = true → I.pubsS = fun _ => (0 : K3)
  hspOn : I.spOn = spOnA P t
  hszSP : I.SP.n = (BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Pb.nS
  hszA : I.A.n = (BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Pb.nA

section Run
variable {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hpG : P = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf P Rg Rt hgen))

theorem execLink_recJ9AXJ (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads) (χe : CoinsE) :
    ExecLinkJ Rt hgen hpG h31A χe (recJ9AXJ Rt s f χe t r) where
  hC := by
    show chipOf (cRPK Rt s f χe (RnOf t r)).1 = _
    rw [GenPortJ9AHMsgJ.cRPK_eqJ Rt hgen χe]
  hpC := by
    show (cRPK Rt s f χe (RnOf t r)).2 = _
    rw [GenPortJ9AHMsgJ.cRPK_eqJ Rt hgen χe]
  hW := by
    show chipOf (wRPK Rt s f χe (RnOf t r)).1 = _
    rw [GenPortJ9AHMsgJ.wRPK_eqJ Rt hgen hwalk9 χe]
  hpW := by
    show (wRPK Rt s f χe (RnOf t r)).2 = _
    rw [GenPortJ9AHMsgJ.wRPK_eqJ Rt hgen hwalk9 χe]
  hkr := by
    show (wsKrK Rt s f χe (RnOf t r)).2 = _
    rw [GenPortJ9AHMsgJ.wsKr_eqJ Rt hgen hwalk9 χe]
  hA := by
    show chipOf (aRPK Rt s f χe (RnOf t r)).1 = _
    rw [GenPortJ9AHMsgJ.aRPK_eqJ Rt hgen χe]
  hpA := by
    show (aRPK Rt s f χe (RnOf t r)).2 = _
    rw [GenPortJ9AHMsgJ.aRPK_eqJ Rt hgen χe]
  hVon := fun hne => by
    refine ⟨?_, ?_⟩
    · show chipOf (vRPK Rt s f χe (RnOf t r)).1 = _
      rw [GenPortJ9AHMsgJ.vRPK_eq_awEJ Rt hgen hax9 hwalkA χe hne]
    · show (vRPK Rt s f χe (RnOf t r)).2 = _
      rw [GenPortJ9AHMsgJ.vRPK_eq_awEJ Rt hgen hax9 hwalkA χe hne]
  hVoff := fun h => by
    refine ⟨?_, ?_⟩
    · show chipOf (vRPK Rt s f χe (RnOf t r)).1 = _
      rw [GenPortJ9AHMsgJ.vRPK_absent Rt hgen χe h]
    · show (vRPK Rt s f χe (RnOf t r)).2 = _
      rw [GenPortJ9AHMsgJ.vRPK_absent Rt hgen χe h]
  hkrV := GenPortJ9AHMsgJ.size_krootsV Rt hgen hpG h31A χe hax9 hwalkA
  hc := rfl
  hχI := rfl
  hX := by
    show chipOf (compK Rt s f χe (RnOf t r)).rows = _
    unfold compK
    rw [HJ_eqJ Rt hgen χe, pd_eqJ Rt hgen χe, idOf_eqJ Rt hgen χe]
    rfl
  hm := GenPortJ9AHMsgJ.msg_m Rt hgen hpG h31A χe
  hρ := GenPortJ9AHMsgJ.msg_ρ Rt hgen hpG h31A χe
  hρS := GenPortJ9AHMsgJ.msg_ρS Rt hgen hpG h31A χe
  hAX := by
    show chipOf (xRPK Rt s f χe (RnOf t r)).1 = _
    rw [GenPortJ9AHMsgJ.xRPK_eqJ Rt hgen χe]
  hpX := by
    show (xRPK Rt s f χe (RnOf t r)).2 = _
    rw [GenPortJ9AHMsgJ.xRPK_eqJ Rt hgen χe]
  haxOn := rfl
  hszAX := GenPortJ9AHMsgJ.size_AX Rt hgen hpG h31A χe
  hSPon := fun h => by
    have e : sRPK Rt s f χe (RnOf t r) = _ := GenPortJ9AHMsgJ.sRPK_of_spOn Rt χe h
    refine ⟨?_, ?_⟩
    · show chipOf (sRPK Rt s f χe (RnOf t r)).1 = _
      rw [e, acs_eqJ Rt hgen χe]
      rfl
    · show (sRPK Rt s f χe (RnOf t r)).2 = _
      rw [e, acs_eqJ Rt hgen χe]
      rfl
  hSPoff := fun h => by
    show (sRPK Rt s f χe (RnOf t r)).2 = _
    rw [GenPortJ9AHMsgJ.sRPK_of_not_spOn Rt χe h]
  hspOn := rfl
  hszSP := GenPortJ9AHMsgJ.size_SP Rt hgen hpG h31A χe
  hszA := GenPortJ9AHMsgJ.size_A Rt hgen hpG h31A χe

theorem staticHypJ_recJ9AXJ (χe : CoinsE) :
    GenPortJ9AHStaticJ.StaticHypJ (recJ9AXJ Rt s f χe t r) (mK Rt s f χe (RnOf t r)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (layK Rt s f χe (RnOf t r)).length ≤ _
    unfold mK
    omega
  · show (compK Rt s f χe (RnOf t r)).rows.size ≤ _
    exact le_max_left _ _
  · show (cRPK Rt s f χe (RnOf t r)).1.size ≤ _
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  · show (wRPK Rt s f χe (RnOf t r)).1.size ≤ _
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  · show (aRPK Rt s f χe (RnOf t r)).1.size ≤ _
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  · show (vRPK Rt s f χe (RnOf t r)).1.size ≤ _
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  · show (xRPK Rt s f χe (RnOf t r)).1.size ≤ _
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _)))))
  · show (sRPK Rt s f χe (RnOf t r)).1.size ≤ _
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))))

end Run

theorem staticHypJ_withOrb {I : InJ9A} {m : ℕ} (o : OrbJ9A)
    (H : GenPortJ9AHStaticJ.StaticHypJ I m) : GenPortJ9AHStaticJ.StaticHypJ (withOrb I o) m :=
  ⟨H.hr, H.hg, H.hAX, H.hSP, H.hJ, H.sX, H.sC, H.sW, H.sA, H.sV, H.sAX, H.sSP⟩

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHLinkJ

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHLinkJ.execLink_recJ9AXJ
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHLinkJ.staticHypJ_recJ9AXJ
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHLinkJ.staticHypJ_withOrb
