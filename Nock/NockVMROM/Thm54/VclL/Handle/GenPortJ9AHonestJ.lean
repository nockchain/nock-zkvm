/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHonestJ.lean

  Honest acceptance of `genJ9AXJ` (jet-calling runs), assembled from the chip ports
  `GenPortJ9AH{CellE,WalkE,AtomE,AWE,XASE,LinkJ,GoodCoinJ}` after `GenPortJ9AHonest`, with `recJ9AXJ` for `recJ9AX` and
  `hC : CompiledBy P Rg Rt`.

  * `honest_rec_atJ`        : core, no `Algebra Fp 𝕂′` binder;
  * `genJ9AXJ_honest_at`    : every `genJ9AXJ` output, at any admissible orbit, is valid and accepted;
  * `genJ9AXJ_honest`       : the same at the output's own orbit;
  * `checkJ9AX_genJ9AXJ`    : the wired checker accepts it.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellE
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkE
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomE
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWE
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHXASE
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHLinkJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoinJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsgJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStaticJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHNonChip
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA
import Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry
import Nock.NockVMROM.Thm54.VclL.Handle.ComplClosedChecked
import Nock.V1J9A.CheckJ9AIffComp

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonestJ

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.V1J9A Nock.V1J9A.GenJ9AX Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb OrbJ9A OrbAdm reorb withOrb orbOf)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun (recJ9AXJ)

noncomputable section

/-! ## 1. The core, at the global `Algebra Fp 𝕂′` instance -/

section Core
variable [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **Honest acceptance of `recJ9AXJ` at any admissible orbit** (global instance; jet-calling run). -/
theorem honest_rec_atJ (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Rt hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf P Rg Rt hgen))
    (hC : CheckedRegistry.CompiledBy P Rg Rt)
    (χe : CoinsE)
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe))
    (o : OrbJ9A) (ho : OrbAdm (recJ9AXJ Rt s f χe t r) o) :
    ∃ hv : ValidJ9A (withOrb (recJ9AXJ Rt s f χe t r) o),
      AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 (mkPbA (withOrb (recJ9AXJ Rt s f χe t r) o) hv) Rg.R
        (withOrb (recJ9AXJ Rt s f χe t r) o).c (toχ (withOrb (recJ9AXJ Rt s f χe t r) o).χ)
        (withOrb (recJ9AXJ Rt s f χe t r) o).toMsg (withOrb (recJ9AXJ Rt s f χe t r) o).toTr
        (withOrb (recJ9AXJ Rt s f χe t r) o).toRows (withOrb (recJ9AXJ Rt s f χe t r) o).g := by
  have hcl := ComplClosedChecked.complJ9A_closed_of deltaF powerBasis3 Rt hgen hpG hax9 hop5 hleaf hwalk9
    hwalkA hC h31A
  obtain ⟨hacc, -⟩ := hcl
  have AH := hacc (toχ χe) hχ
  have NC0 := GenPortJ9AHNonChip.nonChip_of_accepts deltaF powerBasis3 AH
  have L := GenPortJ9AHLinkJ.execLink_recJ9AXJ Rt hgen hpG h31A hax9 hwalk9 hwalkA χe
  have hv' : ValidJ9A (withOrb (recJ9AXJ Rt s f χe t r) o) :=
    GenPortJ9AHOrbA.validJ9A_withOrb
      (GenPortJ9AHMsgJ.validJ9A_recJ9AXJ Rt hgen hpG h31A χe hwalk9 hax9 hwalkA) ho
  refine ⟨hv', ?_⟩
  have NC : GenPortJ9AHNonChip.NonChipJ9A deltaF powerBasis3 (mkPbA (withOrb (recJ9AXJ Rt s f χe t r) o) hv') Rg.R
      (withOrb (recJ9AXJ Rt s f χe t r) o).c (toχ (withOrb (recJ9AXJ Rt s f χe t r) o).χ)
      (withOrb (recJ9AXJ Rt s f χe t r) o).toMsg := by
    show GenPortJ9AHNonChip.NonChipJ9A deltaF powerBasis3 (mkPbA (withOrb (recJ9AXJ Rt s f χe t r) o) hv') Rg.R
      (ComplJ8.cJ s f r) (toχ χe) (withOrb (recJ9AXJ Rt s f χe t r) o).toMsg
    have hr := GenPortJ9AHMsgJ.regs_B' Rt hgen hpG h31A χe
    exact GenPortJ9AHMsgJ.nonChip_transportJ deltaF powerBasis3 NC0
      (GenPortJ9AHMsgJ.size_X Rt hgen hpG h31A χe)
      (GenPortJ9AHMsgJ.size_C Rt hgen hpG h31A χe)
      (GenPortJ9AHMsgJ.size_W Rt hgen hpG h31A χe hwalk9)
      (GenPortJ9AHMsgJ.size_kroots Rt hgen hpG h31A χe hwalk9)
      (GenPortJ9AHMsgJ.size_A Rt hgen hpG h31A χe)
      (GenPortJ9AHMsgJ.size_V Rt hgen hpG h31A χe hax9 hwalkA)
      (GenPortJ9AHMsgJ.size_AX Rt hgen hpG h31A χe)
      (GenPortJ9AHMsgJ.size_SP Rt hgen hpG h31A χe)
      hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 (hr.2.2.2.2.2.trans NC0.hlay.symm)
      (GenPortJ9AHMsgJ.msg_m Rt hgen hpG h31A χe)
      (GenPortJ9AHMsgJ.msg_ρ Rt hgen hpG h31A χe)
      (GenPortJ9AHMsgJ.msg_ρS Rt hgen hpG h31A χe)
      (GenPortJ9AHMsgJ.msg_pubsC Rt hgen hpG h31A χe)
      (GenPortJ9AHMsgJ.msg_pubsW Rt hgen hpG h31A χe hwalk9)
      (GenPortJ9AHMsgJ.msg_pubsJ Rt hgen hpG h31A χe)
      (GenPortJ9AHMsgJ.msg_pubsA Rt hgen hpG h31A χe)
      (GenPortJ9AHMsgJ.msg_pubsV Rt hgen hpG h31A χe hax9 hwalkA)
      (GenPortJ9AHMsgJ.msg_pubsX Rt hgen hpG h31A χe)
      (GenPortJ9AHMsgJ.msg_pubsS Rt hgen hpG h31A χe)
  obtain ⟨⟨hinjX, hadjX⟩, ⟨hinjC, hadjC⟩, ⟨hinjW, hadjW⟩, ⟨hinjA, hadjA⟩⟩ :=
    GenPortJ9AHOrbA.nodes_withOrb ho hv'
  -- budgets
  have H := GenPortJ9AHLinkJ.staticHypJ_withOrb o (GenPortJ9AHLinkJ.staticHypJ_recJ9AXJ Rt (s := s) (f := f) (t := t) (r := r) χe)
  have hb := GenPortJ9AHStaticJ.budJ9A_staticJ (withOrb (recJ9AXJ Rt s f χe t r) o) hv' _ H
  have hbV := GenPortJ9AHStaticJ.hbudV_staticJ (withOrb (recJ9AXJ Rt s f χe t r) o) hv' _ H
  have eB : (withOrb (recJ9AXJ Rt s f χe t r) o).g + (withOrb (recJ9AXJ Rt s f χe t r) o).toRows.N =
      (withOrb (recJ9AXJ Rt s f χe t r) o).g +
        max 10 (2 * GenPortJ9AHJRun.mK Rt s f χe (GenPortJ9AHProj.RnOf t r)) := by
    show (withOrb (recJ9AXJ Rt s f χe t r) o).g + (withOrb (recJ9AXJ Rt s f χe t r) o).r.N = _
    rw [H.hr]
    rfl
  -- chips
  have cell := GenPortJ9AHCellE.cellE_at Rt hgen hpG h31A hleaf χe _ L.hC L.hpC o ho hv' hχ
  have walk := GenPortJ9AHWalkE.walkE_at Rt hgen hwalk9 hpG h31A χe _ L.hW L.hpW L.hkr o ho hv' hχ
  have atom := GenPortJ9AHAtomE.atomE_at Rt hgen hpG h31A χe _ L.hA L.hpA o ho hv' hχ
  have hRt := (CheckedRegistry.hRt_hregAx_of hC hgen).1
  exact
    { hsatX := GenPortJ9AHXASE.hsatXE_at Rt hgen hpG h31A hax9 hop5 χe _ L.hc L.hχI L.hX L.hm L.hρ L.hρS
        o ho hv' hχ
      hinjX := hinjX
      hadjX := hadjX
      hsatC := cell.1
      hbindC := cell.2
      hinjC := hinjC
      hadjC := hadjC
      hnpC := NC.hnpC
      hsatW := walk.1
      hbindW := walk.2
      hinjW := hinjW
      hadjW := hadjW
      hkW := NC.hkW
      hknW := NC.hknW
      hkpW := NC.hkpW
      hJk := GenPortJ9AHOrbJ.j_at Rt hgen hpG h31A hRt χe o ho hv' hχ
      hsatA := atom.1.1
      hbindA := atom.1.2
      hinjA := hinjA
      hadjA := hadjA
      hnpA := NC.hnpA
      hVk := GenPortJ9AHAWE.awE_at Rt hgen hax9 hwalkA hpG h31A χe _ L.hχI L.hVon L.hVoff L.hkrV o ho hv' hχ
      hGx := NC.hGx
      hGp := NC.hGp
      hGS := NC.hGS
      hlay := NC.hlay
      hsmall := NC.hsmall
      huniq := NC.huniq
      hTpl := NC.hTpl
      hnd := NC.hnd
      hidx := NC.hidx
      hrk := NC.hrk
      hlt := NC.hlt
      hsumC' := NC.hsumC'
      hbalA' := NC.hbalA'
      hvalA0 := NC.hvalA0
      hfxC := NC.hfxC
      hfxA := NC.hfxA
      hclI := NC.hclI
      hclR := NC.hclR
      hcen' := NC.hcen'
      hlenC := NC.hlenC
      hlenA := NC.hlenA
      hcellF := NC.hcellF
      hnAS := NC.hnAS
      hbud := by rw [eB]; exact hb
      hbudV := hbV
      hsatL := atom.2.1
      hbindL := atom.2.2
      hAXk := GenPortJ9AHXASE.hAXkE_at Rt hgen hpG h31A χe _ L.hχI L.hAX L.hpX L.haxOn L.hszAX o ho hv' hχ
      hSPk := GenPortJ9AHXASE.hSPkE_at Rt hgen hpG h31A hax9 χe _ L.hχI L.hSPon L.hSPoff L.hspOn L.hszSP
        L.hszA o ho hv' hχ
      hlenX := NC.hlenX }

end Core

/-! ## 2. The deliverables -/

section Final
variable [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  [iA : Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod P) KC deltaF))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
  (hgen : genX Rg.R fuel s f = some (t, r))

/-- **`genJ9AXJ_honest_at`**: every `genJ9AXJ` output, at every admissible per-chip orbit, is valid and accepted. -/
theorem genJ9AXJ_honest_at (hpG : P = Nock.Atoms.p) {Rt : ℕ → Nock.Jet.Autogen.Tpl}
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Rt hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf P Rg Rt hgen))
    (hC : CheckedRegistry.CompiledBy P Rg Rt)
    {χe : CoinsE} {I : InJ9A} (hI : Nock.V1J9A.GenJ9AXJ.genJ9AXJ Rg.R Rt fuel s f χe = some I)
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe))
    (o : OrbJ9A) (ho : OrbAdm I o) :
    ∃ hv : ValidJ9A (withOrb I o),
      AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 (mkPbA (withOrb I o) hv) Rg.R (withOrb I o).c
        (toχ (withOrb I o).χ) (withOrb I o).toMsg (withOrb I o).toTr (withOrb I o).toRows (withOrb I o).g := by
  obtain ⟨t', r', hgen', rfl⟩ := GenPortJ9AHJRun.genJ9AXJ_some hI
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hgen'.symm.trans hgen))
  obtain rfl : iA = GenPortJ9AHonest.algG := Subsingleton.elim _ _
  exact honest_rec_atJ Rt hgen hpG hax9 hop5 hleaf hwalk9 hwalkA h31A hC χe hχ o ho

/-- **`genJ9AXJ_honest`**: every `genJ9AXJ` output is valid and accepted (at its own orbit). -/
theorem genJ9AXJ_honest (hpG : P = Nock.Atoms.p) {Rt : ℕ → Nock.Jet.Autogen.Tpl}
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Rt hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf P Rg Rt hgen))
    (hC : CheckedRegistry.CompiledBy P Rg Rt)
    {χe : CoinsE} {I : InJ9A} (hI : Nock.V1J9A.GenJ9AXJ.genJ9AXJ Rg.R Rt fuel s f χe = some I)
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    ∃ hv : ValidJ9A I,
      AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 (mkPbA I hv) Rg.R I.c (toχ I.χ) I.toMsg I.toTr I.toRows I.g := by
  obtain ⟨t', r', hgen', rfl⟩ := GenPortJ9AHJRun.genJ9AXJ_some hI
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hgen'.symm.trans hgen))
  obtain rfl : iA = GenPortJ9AHonest.algG := Subsingleton.elim _ _
  have h := honest_rec_atJ Rt hgen hpG hax9 hop5 hleaf hwalk9 hwalkA h31A hC χe hχ _
    (GenPortJ9AHMsgJ.orbAdm_recJ9AXJ Rt hgen hpG h31A χe hwalk9 hax9 hwalkA)
  rw [GenPortJ9AHOrbA.withOrb_self] at h
  exact h

/-- **`checkJ9AX_genJ9AXJ`**: the wired J-9 A checker accepts every `genJ9AXJ` output. -/
theorem checkJ9AX_genJ9AXJ (hpG : P = Nock.Atoms.p) {Rt : ℕ → Nock.Jet.Autogen.Tpl}
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Rt hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf P Rg Rt hgen))
    (hC : CheckedRegistry.CompiledBy P Rg Rt)
    {χe : CoinsE} {I : InJ9A} (hI : Nock.V1J9A.GenJ9AXJ.genJ9AXJ Rg.R Rt fuel s f χe = some I)
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    GenJ9AX.checkJ9AX I = true :=
  (CheckJ9AIffComp.checkJ9AX_iff I Rg.R (GenPortJ9AHJRun.regOK_genJ9AXJ hC hI)).mpr
    (genJ9AXJ_honest hgen hpG hax9 hop5 hleaf hwalk9 hwalkA h31A hC hI hχ)

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonestJ

section Axioms
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonestJ.honest_rec_atJ
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonestJ.genJ9AXJ_honest_at
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonestJ.genJ9AXJ_honest
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonestJ.checkJ9AX_genJ9AXJ
end Axioms
