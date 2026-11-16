/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHOrbCell.lean

* `genJ9AX_cell_pubs_at` : `genJ9AX_cell_pubs` at an arbitrary injective orbit `O`;
  * `cell_interp_at`       : `genJ9AX_cell_interp` at arbitrary injective nodes `ν`;
  * `cell_at`              : `hsatC ∧ hbindC` at `mkPbA (withOrb I o) hv'`, `I.toMsg`/`toTr`, coin `toχ χe`.
  Never compares `mkPbA` with `B.Pb`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipCast
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMemSat
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGood
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfMem

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbCell

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

section Run
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hnc : callsOf (ComplJ8Data.rowsOfT t) = [])
include hnc

/-- `genJ9AX_cell_pubs` at an arbitrary injective orbit `O`. -/
theorem genJ9AX_cell_pubs_at (χe : CoinsE) {h : ℕ} (O : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN O (j9aDataOf P Rg Rt hgen).cells.length)) (j : ℕ) :
    K3.toK ((recJ9AX s f χe t r).M.pubsC j) =
      ComplJ8Of.pubsCOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) (cellsA_pos Rt hgen) O (toχ χe) j := by
  rw [GenPortJ9AHCellRun.recJ9AX_pubsC Rt hgen hnc χe]
  exact cellGenB_pubs χe (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs
    (GenPortJ9AHCellRun.hcs_DA Rt hgen hnc χe) (GenPortJ9AHCellRun.hcl_DA Rt hgen hnc χe)
    (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx
    (j9aDataOf P Rg Rt hgen).mh (j9aDataOf P Rg Rt hgen) rfl rfl rfl rfl rfl (cellsA_pos Rt hgen)
    O hinj j

/-- `genJ9AX_cell_interp` at arbitrary injective nodes `ν`. -/
theorem cell_interp_at (χe : CoinsE) (ν : Fin (recJ9AX s f χe t r).C.n → ZMod P)
    (hinj : Function.Injective ν) {h : ℕ}
    (O : StrictOrbitDomain (ZMod P) 3 h)
    (pubsF : Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC → ℕ → KC)
    (j : ℕ) (hj : j < 242) :
    Lagrange.interpolate Finset.univ ν (fun i => (recJ9AX s f χe t r).C.cols j i) =
      ComplJ8Enc.cellTrME deltaF powerBasis3 (cellsA_pos Rt hgen)
        (fun i => ν (Fin.cast (GenPortJ9AHCellRun.genJ9AX_cell_n Rt hgen hnc χe).symm i))
        O (chalsMJ8 deltaF) pubsF (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.zJ deltaF)
        (ComplJ8Of.encR deltaF) (ComplJ8Of.bigOf (j9aDataOf P Rg Rt hgen)) (j9aDataOf P Rg Rt hgen).cells
        (ComplJ8Of.mvF (j9aDataOf P Rg Rt hgen)) (ComplJ8Of.mxF (j9aDataOf P Rg Rt hgen)) (fun _ => 0)
        (ComplJ8Of.mhF (j9aDataOf P Rg Rt hgen)) (toχ χe) ⟨j, hj⟩ := by
  have hn := GenPortJ9AHCellRun.genJ9AX_cell_n Rt hgen hnc χe
  rw [interp_cast hn]
  unfold ComplJ8Enc.cellTrME honestQ
  refine congrArg (Lagrange.interpolate Finset.univ (ν ∘ Fin.cast hn.symm)) ?_
  funext i'
  exact GenPortJ9AHCellRun.genJ9AX_cell_cols Rt hgen hnc χe (Fin.cast hn.symm i') j hj
    (fun i => ν (Fin.cast hn.symm i))
    (hinj.comp (Fin.cast_injective _)) O (pubsF (toχ χe))

/-- **`hsatC ∧ hbindC` of `AcceptsJ9A` at `withOrb I o`.** -/
theorem cell_at (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
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
  -- the exec chip at the new orbit
  have hoC : OrbOK (reorb (recJ9AX s f χe t r).C o.C) := hv'.oC
  have hinj0 : Function.Injective (nodesOf (reorb (recJ9AX s f χe t r).C o.C)) :=
    GenPortJ9AHOrb.nodesOf_inj _ hoC ho.C.2
  have hnodes : nodesOf (reorb (recJ9AX s f χe t r).C o.C) =
      ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC) (recJ9AX s f χe t r).C.n :=
    GenPortJ9AHOrbA.nodesOf_powN _ hoC
  have hpow : ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC)
        (j9aDataOf P Rg Rt hgen).cells.length =
      nodesOf (reorb (recJ9AX s f χe t r).C o.C) ∘ Fin.cast hn.symm := by
    rw [hnodes]; rfl
  have hinjN : Function.Injective (ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC)
      (j9aDataOf P Rg Rt hgen).cells.length) := by
    rw [hpow]; exact hinj0.comp (Fin.cast_injective _)
  have hadjN : ∀ (i : Fin (j9aDataOf P Rg Rt hgen).cells.length)
      (hi : (i : ℕ) + 1 < (j9aDataOf P Rg Rt hgen).cells.length),
      ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC)
          (j9aDataOf P Rg Rt hgen).cells.length ⟨(i : ℕ) + 1, hi⟩ =
        ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC)
          (j9aDataOf P Rg Rt hgen).cells.length i * (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC).ω :=
    fun i hi => pow_succ _ _
  -- the J-8 orbit
  have hF := ComplJ9ARun.hF_run Rt hgen hpG h31A
  have hmem : (j9aDataOf P Rg Rt hgen).cells.length ∈ ComplJ8Of.sizesJ8 (j9aDataOf P Rg Rt hgen) := by
    simp [ComplJ8Of.sizesJ8]
  have hinjJ : Function.Injective (ComplJ8Of.powN (ComplJ8Of.orbJ8 (j9aDataOf P Rg Rt hgen) hF)
      (j9aDataOf P Rg Rt hgen).cells.length) :=
    (ComplJ8Of.powN_ok _ (ComplJ8Of.le_two_pow_ht _ hmem)).1
  -- coin events
  have hV : ∀ e ∈ ComplJ8Of.famCellV deltaF (j9aDataOf P Rg Rt hgen) (K := KC), toχ χe ∉ e.ev :=
    fun e he => ComplJ9AOfMem.goodJA deltaF powerBasis3 Rt hgen hpG h31A hχ _
      (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)) e he
  have hH : ∀ e ∈ ComplJ8Of.famCellH deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hC
      (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC) (K := KC), toχ χe ∉ e.ev := by
    refine (GenPortJ9AHGood.famCellH_ev_orb deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hC
      (ComplJ8Of.orbJ8 (j9aDataOf P Rg Rt hgen) hF) _ hinjJ hinjN (toχ χe)).mp ?_
    exact fun e he => ComplJ9AOfMem.goodJA deltaF powerBasis3 Rt hgen hpG h31A hχ _
      (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) e he
  have H := GenPortJ9AHMemSat.cellOK_run_at deltaF powerBasis3 Rt hgen hC hpG
    (ComplJ9AChains.hp63_of_G hpG) hleaf (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC)
    hinjN hadjN (toχ χe) hV hH
  -- publics
  have hpubs : (withOrb (recJ9AX s f χe t r) o).toMsg.pubsC =
      ComplJ8Of.pubsCOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hC
        (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC) (toχ χe) :=
    funext fun j => genJ9AX_cell_pubs_at Rt hgen hnc χe _ hinjN j
  -- trace
  have hT : ∀ j : Fin 242, interpOf (reorb (recJ9AX s f χe t r).C o.C) j =
      ComplJ8Enc.cellTrME deltaF powerBasis3 hC
        (ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC)
          (j9aDataOf P Rg Rt hgen).cells.length)
        (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC) (chalsMJ8 deltaF)
        (ComplJ8Of.pubsCOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hC
          (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC))
        (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.zJ deltaF)
        (ComplJ8Of.encR deltaF) (ComplJ8Of.bigOf (j9aDataOf P Rg Rt hgen)) (j9aDataOf P Rg Rt hgen).cells
        (ComplJ8Of.mvF (j9aDataOf P Rg Rt hgen)) (ComplJ8Of.mxF (j9aDataOf P Rg Rt hgen)) (fun _ => 0)
        (ComplJ8Of.mhF (j9aDataOf P Rg Rt hgen)) (toχ χe) j := by
    intro j
    have hfun : (fun i => nodesOf (reorb (recJ9AX s f χe t r).C o.C) (Fin.cast hn.symm i)) =
        ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC)
          (j9aDataOf P Rg Rt hgen).cells.length := hpow.symm
    have := cell_interp_at Rt hgen hnc χe (nodesOf (reorb (recJ9AX s f χe t r).C o.C)) hinj0
      (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC)
      (ComplJ8Of.pubsCOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hC
        (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC)) j j.2
    rw [hfun] at this
    exact this
  have hνμ : ∀ i : Fin (reorb (recJ9AX s f χe t r).C o.C).n,
      nodesOf (reorb (recJ9AX s f χe t r).C o.C) i =
        ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC)
          (j9aDataOf P Rg Rt hgen).cells.length (Fin.cast hn i) :=
    fun i => congrFun hnodes i
  generalize (withOrb (recJ9AX s f χe t r) o).toMsg.pubsC = pubs at hpubs ⊢
  subst hpubs
  have hq : qM deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').toPubJ8
      (withOrb (recJ9AX s f χe t r) o).toTr.toJ8 (chalsMJ8 deltaF (toχ χe))
      (ComplJ8Of.pubsCOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hC
        (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC) (toχ χe)) =
      ComplJ8Enc.cellTrME deltaF powerBasis3 hC
        (ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC)
          (j9aDataOf P Rg Rt hgen).cells.length)
        (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC) (chalsMJ8 deltaF)
        (ComplJ8Of.pubsCOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hC
          (mkOrbit (reorb (recJ9AX s f χe t r).C o.C) hoC))
        (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.zJ deltaF)
        (ComplJ8Of.encR deltaF) (ComplJ8Of.bigOf (j9aDataOf P Rg Rt hgen)) (j9aDataOf P Rg Rt hgen).cells
        (ComplJ8Of.mvF (j9aDataOf P Rg Rt hgen)) (ComplJ8Of.mxF (j9aDataOf P Rg Rt hgen)) (fun _ => 0)
        (ComplJ8Of.mhF (j9aDataOf P Rg Rt hgen)) (toχ χe) :=
    funext hT
  rw [hq]
  exact GenPortJ9AHChipCast.cellOK_reidx deltaF powerBasis3 hn hv'.nC hC _ _ hνμ _ _ _ _ H

end Run

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbCell

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbCell in
#print axioms genJ9AX_cell_pubs_at
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbCell in
#print axioms cell_interp_at
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbCell in
#print axioms cell_at
