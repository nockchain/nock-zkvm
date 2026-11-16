/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHonest.lean

* `genJ9AX_honest_at`  : every `genJ9AX` output, re-oriented to any admissible per-chip orbit `o`, is valid and
                           accepted by `AcceptsJ9A` at every good coin of the honest run `BRun9A`;
  * `genJ9AX_honest`     : the same at the output's own orbit (`o := orbOf I`);
  * `checkJ9AX_genJ9AX`  : hence the wired checker accepts it.

  Assembly only.  The core `honest_rec_at` is stated in a section WITHOUT the
  `[Algebra Nock.Atoms.Fp 𝕂′]` binder, so every piece (with or without that binder) meets it at the global
  instance; the three targets keep the binder and reduce to the core by `Subsingleton` (algebra structures over
  `ZMod p` are unique) and `subst`.  Never compares `mkPbA` with `B.Pb` (R1): every field enters through its own
  lemma.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbXAS
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbCell
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbAtom
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbWalk
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbAW
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsg
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHNonChip
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStatic
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AClosed
import Nock.V1J9A.CheckJ9AIffComp

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.V1J9A Nock.V1J9A.GenJ9AX Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb OrbJ9A OrbAdm reorb withOrb orbOf)

noncomputable section

/-- The global `Algebra Fp 𝕂′` instance (`AdjoinRoot.instAlgebra`), named. -/
abbrev algG : Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod P) KC deltaF)) := inferInstance

/-! ## 1. The core, at the global `Algebra Fp 𝕂′` instance -/

section Core
variable [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
  (hgen : genX Rg.R fuel s f = some (t, r))

/-- **Honest acceptance of `recJ9AX` at any admissible orbit** (global instance; jet-free run). -/
theorem honest_rec_at (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Example.RtG hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Example.RtG hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf P Rg Example.RtG hgen))
    (hnc : callsOf (ComplJ8Data.rowsOfT t) = []) (hcid : ComplJ8Jet.CalledIds t = ∅)
    (χe : CoinsE)
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Example.RtG hgen hpG h31A).Good (toχ χe))
    (o : OrbJ9A) (ho : OrbAdm (recJ9AX s f χe t r) o) :
    ∃ hv : ValidJ9A (withOrb (recJ9AX s f χe t r) o),
      AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv) Rg.R
        (withOrb (recJ9AX s f χe t r) o).c (toχ (withOrb (recJ9AX s f χe t r) o).χ)
        (withOrb (recJ9AX s f χe t r) o).toMsg (withOrb (recJ9AX s f χe t r) o).toTr
        (withOrb (recJ9AX s f χe t r) o).toRows (withOrb (recJ9AX s f χe t r) o).g := by
  -- the honest acceptance at `BRun9A` (`hRt`, `hregAx` vacuous: no called ids)
  have hcl := ComplJ9AClosed.complJ9A_closed deltaF powerBasis3 Example.RtG hgen hpG hax9 hop5 hleaf hwalk9
    hwalkA (fun id hid => by rw [hcid] at hid; simp at hid) (fun id hid => by rw [hcid] at hid; simp at hid) h31A
  obtain ⟨hacc, -⟩ := hcl
  have AH := hacc (toχ χe) hχ
  have NC0 := GenPortJ9AHNonChip.nonChip_of_accepts deltaF powerBasis3 AH
  -- validity at the new orbit
  have hv' : ValidJ9A (withOrb (recJ9AX s f χe t r) o) :=
    GenPortJ9AHOrbA.validJ9A_withOrb
      (GenPortJ9AHMsg.validJ9A_recJ9AX Example.RtG hgen hnc hpG h31A χe hwalk9 hax9 hwalkA) ho
  refine ⟨hv', ?_⟩
  -- the 29 non-chip fields, transported from `B` field by field
  have NC : GenPortJ9AHNonChip.NonChipJ9A deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv') Rg.R
      (withOrb (recJ9AX s f χe t r) o).c (toχ (withOrb (recJ9AX s f χe t r) o).χ)
      (withOrb (recJ9AX s f χe t r) o).toMsg := by
    show GenPortJ9AHNonChip.NonChipJ9A deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv') Rg.R
      (ComplJ8.cJ s f r) (toχ χe) (withOrb (recJ9AX s f χe t r) o).toMsg
    exact GenPortJ9AHNonChip.nonChip_transport deltaF powerBasis3 NC0
      (GenPortJ9AHMsg.size_X Example.RtG hgen hnc hpG h31A χe)
      (GenPortJ9AHMsg.size_C Example.RtG hgen hnc hpG h31A χe)
      (GenPortJ9AHMsg.size_W Example.RtG hgen hnc hpG h31A χe hwalk9)
      (GenPortJ9AHMsg.size_kroots Example.RtG hgen hnc hpG h31A χe hwalk9)
      (GenPortJ9AHMsg.size_A Example.RtG hgen hnc hpG h31A χe)
      (GenPortJ9AHMsg.size_V Example.RtG hgen hnc hpG h31A χe hax9 hwalkA)
      (GenPortJ9AHMsg.size_AX Example.RtG hgen hnc hpG h31A χe)
      (GenPortJ9AHMsg.size_SP Example.RtG hgen hnc hpG h31A χe)
      (GenPortJ9AHProj.recX_regs s f χe t r)
      (GenPortJ9AHMsg.regs_B Example.RtG hgen hnc hpG h31A)
      rfl
      (GenPortJ9AHProj.recX_J_n s f χe t r)
      (GenPortJ9AHMsg.msg_m Example.RtG hgen hnc hpG h31A χe)
      (GenPortJ9AHMsg.msg_ρ Example.RtG hgen hnc hpG h31A χe)
      (GenPortJ9AHMsg.msg_ρS Example.RtG hgen hnc hpG h31A χe)
      (GenPortJ9AHMsg.msg_pubsC Example.RtG hgen hnc hpG h31A χe)
      (GenPortJ9AHMsg.msg_pubsW Example.RtG hgen hnc hpG h31A χe hwalk9)
      (GenPortJ9AHMsg.msg_pubsJ Example.RtG hgen hnc hpG h31A χe)
      (GenPortJ9AHMsg.msg_pubsA Example.RtG hgen hnc hpG h31A χe)
      (GenPortJ9AHMsg.msg_pubsV Example.RtG hgen hnc hpG h31A χe hax9 hwalkA)
      (GenPortJ9AHMsg.msg_pubsX Example.RtG hgen hnc hpG h31A χe)
      (GenPortJ9AHMsg.msg_pubsS Example.RtG hgen hnc hpG h31A χe)
  -- nodes
  obtain ⟨⟨hinjX, hadjX⟩, ⟨hinjC, hadjC⟩, ⟨hinjW, hadjW⟩, ⟨hinjA, hadjA⟩⟩ :=
    GenPortJ9AHOrbA.nodes_withOrb ho hv'
  -- budgets
  have H := GenPortJ9AHOrbA.staticHyp_withOrb o (GenPortJ9AHProj.staticHyp_recX s f χe t r)
  have hb := GenPortJ9AHStatic.budJ9A_static (withOrb (recJ9AX s f χe t r) o) hv' _ H
  have hbV := GenPortJ9AHStatic.hbudV_static (withOrb (recJ9AX s f χe t r) o) hv' _ H
  have eB : (withOrb (recJ9AX s f χe t r) o).g + (withOrb (recJ9AX s f χe t r) o).toRows.N =
      0 + max 10 (2 * GenPortJ9AHProj.mJ s f χe (GenPortJ9AHProj.RnOf t r)) := by
    rw [H.hg]
    show 0 + (withOrb (recJ9AX s f χe t r) o).r.N = _
    rw [H.hr]
    rfl
  -- chips
  have cell := GenPortJ9AHOrbCell.cell_at Example.RtG hgen hnc hpG h31A hleaf χe o ho hv' hχ
  have walk := GenPortJ9AHOrbWalk.walk_at Example.RtG hgen hnc hwalk9 hpG h31A χe (recJ9AX s f χe t r) rfl
    o ho hv' hχ
  have atom := GenPortJ9AHOrbAtom.atom_at Example.RtG hgen hnc hpG h31A χe o ho hv' hχ
  exact
    { hsatX := GenPortJ9AHOrbXAS.hsatX_at Example.RtG hgen hpG h31A hax9 hop5 hnc χe o ho hv' hχ
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
      hJk := GenPortJ9AHOrbXAS.hJk_at s f χe t r o hv'
      hsatA := atom.1.1
      hbindA := atom.1.2
      hinjA := hinjA
      hadjA := hadjA
      hnpA := NC.hnpA
      hVk := GenPortJ9AHOrbAW.aw_at Example.RtG hgen hnc hax9 hwalkA hpG h31A χe o ho hv' hχ
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
      hbudV := by rw [H.hg]; exact hbV
      hsatL := atom.2.1
      hbindL := atom.2.2
      hAXk := GenPortJ9AHOrbXAS.hAXk_at Example.RtG hgen hpG h31A hnc χe o ho hv' hχ
      hSPk := GenPortJ9AHOrbXAS.hSPk_at Example.RtG hgen hpG h31A hax9 hnc χe o ho hv' hχ
      hlenX := NC.hlenX }

end Core

/-! ## 2. The deliverables -/

section Final
variable [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  [iA : Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod P) KC deltaF))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
  (hgen : genX Rg.R fuel s f = some (t, r))

/-- **`genJ9AX_honest_at`**: every `genJ9AX` output, at every admissible per-chip orbit, is valid and accepted. -/
theorem genJ9AX_honest_at (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Example.RtG hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Example.RtG hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf P Rg Example.RtG hgen))
    {χe : CoinsE} {I : InJ9A} (hI : GenJ9AX.genJ9AX Rg.R fuel s f χe = some I)
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Example.RtG hgen hpG h31A).Good (toχ χe))
    (o : OrbJ9A) (ho : OrbAdm I o) :
    ∃ hv : ValidJ9A (withOrb I o),
      AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 (mkPbA (withOrb I o) hv) Rg.R (withOrb I o).c
        (toχ (withOrb I o).χ) (withOrb I o).toMsg (withOrb I o).toTr (withOrb I o).toRows (withOrb I o).g := by
  obtain ⟨t', r', hgen', hnc, hcid, rfl⟩ := GenPortJ9AHRun.genJ9AX_some hI
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hgen'.symm.trans hgen))
  obtain rfl : iA = algG := Subsingleton.elim _ _
  exact honest_rec_at hgen hpG hax9 hop5 hleaf hwalk9 hwalkA h31A hnc hcid χe hχ o ho

/-- **`genJ9AX_honest`**: every `genJ9AX` output is valid and accepted (at its own orbit). -/
theorem genJ9AX_honest (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Example.RtG hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Example.RtG hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf P Rg Example.RtG hgen))
    {χe : CoinsE} {I : InJ9A} (hI : GenJ9AX.genJ9AX Rg.R fuel s f χe = some I)
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Example.RtG hgen hpG h31A).Good (toχ χe)) :
    ∃ hv : ValidJ9A I,
      AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 (mkPbA I hv) Rg.R I.c (toχ I.χ) I.toMsg I.toTr I.toRows I.g := by
  obtain ⟨t', r', hgen', hnc, hcid, rfl⟩ := GenPortJ9AHRun.genJ9AX_some hI
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hgen'.symm.trans hgen))
  obtain rfl : iA = algG := Subsingleton.elim _ _
  have h := honest_rec_at hgen hpG hax9 hop5 hleaf hwalk9 hwalkA h31A hnc hcid χe hχ _
    (GenPortJ9AHMsg.orbAdm_recJ9AX Example.RtG hgen hnc hpG h31A χe hwalk9 hax9 hwalkA)
  rw [GenPortJ9AHOrbA.withOrb_self] at h
  exact h

/-- **`checkJ9AX_genJ9AX`**: the wired J-9 A checker accepts every `genJ9AX` output. -/
theorem checkJ9AX_genJ9AX (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Example.RtG hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Example.RtG hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf P Rg Example.RtG hgen))
    {χe : CoinsE} {I : InJ9A} (hI : GenJ9AX.genJ9AX Rg.R fuel s f χe = some I)
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Example.RtG hgen hpG h31A).Good (toχ χe)) :
    GenJ9AX.checkJ9AX I = true :=
  (CheckJ9AIffComp.checkJ9AX_iff I Rg.R (GenPortJ9AHRun.genJ9AX_some' hI).2).mpr
    (genJ9AX_honest hgen hpG hax9 hop5 hleaf hwalk9 hwalkA h31A hI hχ)

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest

section Axioms
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest.honest_rec_at
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest.genJ9AX_honest_at
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest.genJ9AX_honest
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest.checkJ9AX_genJ9AX
end Axioms
