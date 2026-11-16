/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHOrbCellG.lean

  `cell_at'` is `GenPortJ9AHOrbCell.cell_at` proved through the generic `GenPortJ9AHChipPort.chipAt_of_cols_pubs`;
  same statement and binders as `cell_at`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipPort
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbCell

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbCellG

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellRow
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCell
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf cellsA_pos)
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.V1J9A Nock.V1J9A.GenJ9AX Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (qM)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipPort
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbCell (genJ9AX_cell_pubs_at cell_interp_at)

section Run
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hnc : callsOf (ComplJ8Data.rowsOfT t) = [])
include hnc

/-- **`hsatC ∧ hbindC` of `AcceptsJ9A` at `withOrb I o`**, through `chipAt_of_cols_pubs`. -/
theorem cell_at' (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Rt hgen).roots)
    (χe : CoinsE) (o : OrbJ9A) (ho : OrbAdm (recJ9AX s f χe t r) o)
    (hv' : ValidJ9A (withOrb (recJ9AX s f χe t r) o))
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    (CellTwinKW.cellChipHQKW deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').hnC
        (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').nodesC (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').orbitC
        (chalsMJ8 deltaF (toχ χe)) (withOrb (recJ9AX s f χe t r) o).toMsg.pubsC).rap.Satisfies
      (qM deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').toPubJ8
        (withOrb (recJ9AX s f χe t r) o).toTr.toJ8 (chalsMJ8 deltaF (toχ χe))
        (withOrb (recJ9AX s f χe t r) o).toMsg.pubsC) ∧
    (CellTwinKW.cellChipHQKW deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').hnC
        (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').nodesC (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').orbitC
        (chalsMJ8 deltaF (toχ χe)) (withOrb (recJ9AX s f χe t r) o).toMsg.pubsC).BindsPreprocessing
      (qM deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').toPubJ8
        (withOrb (recJ9AX s f χe t r) o).toTr.toJ8 (chalsMJ8 deltaF (toχ χe))
        (withOrb (recJ9AX s f χe t r) o).toMsg.pubsC) := by
  have hn := GenPortJ9AHCellRun.genJ9AX_cell_n Rt hgen hnc χe
  have hC : 0 < (j9aDataOf P Rg Rt hgen).cells.length := cellsA_pos Rt hgen
  have hoC : OrbOK (reorb (recJ9AX s f χe t r).C o.C) := hv'.oC
  have hinj0 : Function.Injective (nodesOf (reorb (recJ9AX s f χe t r).C o.C)) :=
    GenPortJ9AHOrb.nodesOf_inj _ hoC ho.C.2
  have hF := ComplJ9ARun.hF_run Rt hgen hpG h31A
  have hmem : (j9aDataOf P Rg Rt hgen).cells.length ∈ ComplJ8Of.sizesJ8 (j9aDataOf P Rg Rt hgen) := by
    simp [ComplJ8Of.sizesJ8]
  have hinjJ : Function.Injective (ComplJ8Of.powN (ComplJ8Of.orbJ8 (j9aDataOf P Rg Rt hgen) hF)
      (j9aDataOf P Rg Rt hgen).cells.length) :=
    (ComplJ8Of.powN_ok _ (ComplJ8Of.le_two_pow_ht _ hmem)).1
  have hV : ∀ e ∈ ComplJ8Of.famCellV deltaF (j9aDataOf P Rg Rt hgen) (K := KC), toχ χe ∉ e.ev :=
    fun e he => ComplJ9AOfMem.goodJA deltaF powerBasis3 Rt hgen hpG h31A hχ _
      (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)) e he
  let S : ChipPort KC 242 :=
    ⟨fun {n} hn ν {h} O chals pubs T =>
      (CellTwinKW.cellChipHQKW deltaF powerBasis3 hn ν O chals pubs).rap.Satisfies T ∧
      (CellTwinKW.cellChipHQKW deltaF powerBasis3 hn ν O chals pubs).BindsPreprocessing T⟩
  have key := chipAt_of_cols_pubs S (reorb (recJ9AX s f χe t r).C o.C) hoC hv'.nC hinj0
    (m := (j9aDataOf P Rg Rt hgen).cells.length) hC hn (chalsMJ8 deltaF (toχ χe))
    (fun {h} O => ComplJ8Of.pubsCOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hC O (toχ χe))
    (fun {h} O j => ComplJ8Enc.cellTrME deltaF powerBasis3 hC
        (ComplJ8Of.powN O (j9aDataOf P Rg Rt hgen).cells.length)
        O (chalsMJ8 deltaF)
        (ComplJ8Of.pubsCOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hC O)
        (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.zJ deltaF)
        (ComplJ8Of.encR deltaF) (ComplJ8Of.bigOf (j9aDataOf P Rg Rt hgen)) (j9aDataOf P Rg Rt hgen).cells
        (ComplJ8Of.mvF (j9aDataOf P Rg Rt hgen)) (ComplJ8Of.mxF (j9aDataOf P Rg Rt hgen)) (fun _ => 0)
        (ComplJ8Of.mhF (j9aDataOf P Rg Rt hgen)) (toχ χe) j)
    (by
      intro h O hinjN hadjN
      have hH : ∀ e ∈ ComplJ8Of.famCellH deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hC O (K := KC),
          toχ χe ∉ e.ev := by
        refine (GenPortJ9AHGood.famCellH_ev_orb deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hC
          (ComplJ8Of.orbJ8 (j9aDataOf P Rg Rt hgen) hF) _ hinjJ hinjN (toχ χe)).mp ?_
        exact fun e he => ComplJ9AOfMem.goodJA deltaF powerBasis3 Rt hgen hpG h31A hχ _
          (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) e he
      exact GenPortJ9AHMemSat.cellOK_run_at deltaF powerBasis3 Rt hgen hC hpG
        (ComplJ9AChains.hp63_of_G hpG) hleaf O hinjN hadjN (toχ χe) hV hH)
    (withOrb (recJ9AX s f χe t r) o).toMsg.pubsC
    (funext fun j => genJ9AX_cell_pubs_at Rt hgen hnc χe _
      (by
        have hnodes := GenPortJ9AHOrbA.nodesOf_powN _ hoC
        have hpow : ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC)
            (j9aDataOf P Rg Rt hgen).cells.length =
            nodesOf (reorb (recJ9AX s f χe t r).C o.C) ∘ Fin.cast hn.symm := by
          rw [hnodes]; rfl
        rw [hpow]; exact hinj0.comp (Fin.cast_injective _)) j)
    (qM deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').toPubJ8
        (withOrb (recJ9AX s f χe t r) o).toTr.toJ8 (chalsMJ8 deltaF (toχ χe))
        (withOrb (recJ9AX s f χe t r) o).toMsg.pubsC)
    (by
      have hnodes := GenPortJ9AHOrbA.nodesOf_powN _ hoC
      have hpow : ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC)
          (j9aDataOf P Rg Rt hgen).cells.length =
          nodesOf (reorb (recJ9AX s f χe t r).C o.C) ∘ Fin.cast hn.symm := by
        rw [hnodes]; rfl
      funext j
      have hfun : (fun i => nodesOf (reorb (recJ9AX s f χe t r).C o.C) (Fin.cast hn.symm i)) =
          ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC)
            (j9aDataOf P Rg Rt hgen).cells.length := hpow.symm
      have := cell_interp_at Rt hgen hnc χe (nodesOf (reorb (recJ9AX s f χe t r).C o.C)) hinj0
        (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC)
        (ComplJ8Of.pubsCOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hC
          (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC)) j j.2
      rw [hfun] at this
      exact this)
  exact key

end Run

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbCellG

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbCellG in
#print axioms cell_at'
