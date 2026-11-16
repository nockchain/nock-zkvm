/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHCellE.lean

  **The cell chip over an abstract record `I : InJ9A`.**  `hnc` is replaced by the field-shape hypotheses `hC`, `hpC` (RHS of `GenPortJ9AHCellRun.cRPJ_eq` /
  `GenPortJ9AHMsgJ.cRPK_eqJ`, copied verbatim). `cellE_n/_cols/_pubs_at/_interp_at/_at`. -/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipPort
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbCellG
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsgJ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellE

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

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsgJ (hcs_DAJ hcl_DAJ)

section Run
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- Columns of a chip equal to `chipOf tbl` (local copy of `WalkRun.cols_of_eq`). -/
theorem cols_of_eqE (C : ChipIn) (tbl : Array (Array (ZMod P))) (h : C = chipOf tbl) (i : Fin C.n) (c : ℕ) :
    C.cols c i = (tbl.getD (i : ℕ) #[]).getD c 0 := by
  subst h
  rfl

theorem cellE_n (χe : CoinsE) (I : InJ9A)
    (hC : I.C = chipOf (cellGenB (coOf χe) (yE χe) (hdlB (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs)
        (bigIdOf (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells
        (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx
        (Array.replicate (j9aDataOf P Rg Rt hgen).cells.length 0) (j9aDataOf P Rg Rt hgen).mh).1) :
    I.C.n = (j9aDataOf P Rg Rt hgen).cells.length := by
  rw [hC]
  exact cellGenB_size _ _ _ _ _ _ _ _ _

theorem cellE_cols (χe : CoinsE) (I : InJ9A)
    (hC : I.C = chipOf (cellGenB (coOf χe) (yE χe) (hdlB (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs)
        (bigIdOf (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells
        (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx
        (Array.replicate (j9aDataOf P Rg Rt hgen).cells.length 0) (j9aDataOf P Rg Rt hgen).mh).1)
    (i : Fin I.C.n) (c : ℕ) (hc : c < 242)
    (nodes : Fin (j9aDataOf P Rg Rt hgen).cells.length → ZMod P) (hinj : Function.Injective nodes) {h : ℕ}
    (orbit : StrictOrbitDomain (ZMod P) 3 h) (pubs : ℕ → KC) :
    I.C.cols c i =
      fullCol (cellsA_pos Rt hgen)
        (HonestKW.colW deltaF powerBasis3
          (cellCol deltaF powerBasis3 (VB χe (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs
            (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx))
          (mhv (j9aDataOf P Rg Rt hgen).mh)
          (ComplJ8Cell.kbLB (ComplJ8Data.bigIdOfP P (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells)
          (ComplJ8Cell.kbRB (ComplJ8Data.bigIdOfP P (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells)
          (HonestKW.ivW deltaF powerBasis3 (cellsA_pos Rt hgen) nodes orbit (chalsMJ8 deltaF (toχ χe)) pubs
            (cellCol deltaF powerBasis3 (VB χe (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs
              (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx))
            (mhv (j9aDataOf P Rg Rt hgen).mh)
            (ComplJ8Cell.kbLB (ComplJ8Data.bigIdOfP P (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells)
            (ComplJ8Cell.kbRB (ComplJ8Data.bigIdOfP P (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells))
          (HonestKW.avW deltaF powerBasis3 (cellsA_pos Rt hgen) nodes orbit (chalsMJ8 deltaF (toχ χe)) pubs
            (cellCol deltaF powerBasis3 (VB χe (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs
              (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx))
            (mhv (j9aDataOf P Rg Rt hgen).mh)
            (ComplJ8Cell.kbLB (ComplJ8Data.bigIdOfP P (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells)
            (ComplJ8Cell.kbRB (ComplJ8Data.bigIdOfP P (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells)))
        c (Fin.cast (cellE_n Rt hgen χe I hC) i) := by
  have hcg := cellGenB_cols χe (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs
    (hcs_DAJ Rt hgen χe) (hcl_DAJ Rt hgen χe) (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx
    (j9aDataOf P Rg Rt hgen).mh (cellsA_pos Rt hgen) rfl nodes hinj orbit pubs
    (Fin.cast (cellE_n Rt hgen χe I hC) i) c hc
  rw [← hcg]
  rw [cols_of_eqE I.C _ hC i c]
  rfl

theorem cellE_pubs_at (χe : CoinsE) (I : InJ9A)
    (hpC : I.M.pubsC = (cellGenB (coOf χe) (yE χe) (hdlB (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs)
        (bigIdOf (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells
        (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx
        (Array.replicate (j9aDataOf P Rg Rt hgen).cells.length 0) (j9aDataOf P Rg Rt hgen).mh).2) {h : ℕ} (O : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN O (j9aDataOf P Rg Rt hgen).cells.length)) (j : ℕ) :
    K3.toK (I.M.pubsC j) =
      ComplJ8Of.pubsCOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) (cellsA_pos Rt hgen) O (toχ χe) j := by
  rw [hpC]
  exact cellGenB_pubs χe (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs
    (hcs_DAJ Rt hgen χe) (hcl_DAJ Rt hgen χe)
    (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx
    (j9aDataOf P Rg Rt hgen).mh (j9aDataOf P Rg Rt hgen) rfl rfl rfl rfl rfl (cellsA_pos Rt hgen)
    O hinj j

theorem cellE_interp_at (χe : CoinsE) (I : InJ9A)
    (hC0 : I.C = chipOf (cellGenB (coOf χe) (yE χe) (hdlB (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs)
        (bigIdOf (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells
        (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx
        (Array.replicate (j9aDataOf P Rg Rt hgen).cells.length 0) (j9aDataOf P Rg Rt hgen).mh).1) (ν : Fin I.C.n → ZMod P)
    (hinj : Function.Injective ν) {h : ℕ}
    (O : StrictOrbitDomain (ZMod P) 3 h)
    (pubsF : Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC → ℕ → KC)
    (j : ℕ) (hj : j < 242) :
    Lagrange.interpolate Finset.univ ν (fun i => I.C.cols j i) =
      ComplJ8Enc.cellTrME deltaF powerBasis3 (cellsA_pos Rt hgen)
        (fun i => ν (Fin.cast (cellE_n Rt hgen χe I hC0).symm i))
        O (chalsMJ8 deltaF) pubsF (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.zJ deltaF)
        (ComplJ8Of.encR deltaF) (ComplJ8Of.bigOf (j9aDataOf P Rg Rt hgen)) (j9aDataOf P Rg Rt hgen).cells
        (ComplJ8Of.mvF (j9aDataOf P Rg Rt hgen)) (ComplJ8Of.mxF (j9aDataOf P Rg Rt hgen)) (fun _ => 0)
        (ComplJ8Of.mhF (j9aDataOf P Rg Rt hgen)) (toχ χe) ⟨j, hj⟩ := by
  have hn := cellE_n Rt hgen χe I hC0
  rw [interp_cast hn]
  unfold ComplJ8Enc.cellTrME honestQ
  refine congrArg (Lagrange.interpolate Finset.univ (ν ∘ Fin.cast hn.symm)) ?_
  funext i'
  exact cellE_cols Rt hgen χe I hC0 (Fin.cast hn.symm i') j hj
    (fun i => ν (Fin.cast hn.symm i))
    (hinj.comp (Fin.cast_injective _)) O (pubsF (toχ χe))

theorem cellE_at (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Rt hgen).roots)
    (χe : CoinsE) (I : InJ9A)
    (hC0 : I.C = chipOf (cellGenB (coOf χe) (yE χe) (hdlB (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs)
        (bigIdOf (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells
        (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx
        (Array.replicate (j9aDataOf P Rg Rt hgen).cells.length 0) (j9aDataOf P Rg Rt hgen).mh).1)
    (hpC : I.M.pubsC = (cellGenB (coOf χe) (yE χe) (hdlB (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs)
        (bigIdOf (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells
        (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx
        (Array.replicate (j9aDataOf P Rg Rt hgen).cells.length 0) (j9aDataOf P Rg Rt hgen).mh).2)
    (o : OrbJ9A) (ho : OrbAdm I o)
        (hv' : ValidJ9A (withOrb I o))
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    (CellTwinKW.cellChipHQKW deltaF powerBasis3 (mkPbA (withOrb I o) hv').hnC
        (mkPbA (withOrb I o) hv').nodesC (mkPbA (withOrb I o) hv').orbitC
        (chalsMJ8 deltaF (toχ χe)) (withOrb I o).toMsg.pubsC).rap.Satisfies
      (qM deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8 (chalsMJ8 deltaF (toχ χe))
        (withOrb I o).toMsg.pubsC) ∧
    (CellTwinKW.cellChipHQKW deltaF powerBasis3 (mkPbA (withOrb I o) hv').hnC
        (mkPbA (withOrb I o) hv').nodesC (mkPbA (withOrb I o) hv').orbitC
        (chalsMJ8 deltaF (toχ χe)) (withOrb I o).toMsg.pubsC).BindsPreprocessing
      (qM deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8 (chalsMJ8 deltaF (toχ χe))
        (withOrb I o).toMsg.pubsC) := by
  have hn := cellE_n Rt hgen χe I hC0
  have hC : 0 < (j9aDataOf P Rg Rt hgen).cells.length := cellsA_pos Rt hgen
  have hoC : OrbOK (reorb I.C o.C) := hv'.oC
  have hinj0 : Function.Injective (nodesOf (reorb I.C o.C)) :=
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
  have key := chipAt_of_cols_pubs S (reorb I.C o.C) hoC hv'.nC hinj0
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
    (withOrb I o).toMsg.pubsC
    (funext fun j => cellE_pubs_at Rt hgen χe I hpC _
      (by
        have hnodes := GenPortJ9AHOrbA.nodesOf_powN _ hoC
        have hpow : ComplJ8Of.powN (mkOrbit (reorb I.C o.C) hoC)
            (j9aDataOf P Rg Rt hgen).cells.length =
            nodesOf (reorb I.C o.C) ∘ Fin.cast hn.symm := by
          rw [hnodes]; rfl
        rw [hpow]; exact hinj0.comp (Fin.cast_injective _)) j)
    (qM deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8 (chalsMJ8 deltaF (toχ χe))
        (withOrb I o).toMsg.pubsC)
    (by
      have hnodes := GenPortJ9AHOrbA.nodesOf_powN _ hoC
      have hpow : ComplJ8Of.powN (mkOrbit (reorb I.C o.C) hoC)
          (j9aDataOf P Rg Rt hgen).cells.length =
          nodesOf (reorb I.C o.C) ∘ Fin.cast hn.symm := by
        rw [hnodes]; rfl
      funext j
      have hfun : (fun i => nodesOf (reorb I.C o.C) (Fin.cast hn.symm i)) =
          ComplJ8Of.powN (mkOrbit (reorb I.C o.C) hoC)
            (j9aDataOf P Rg Rt hgen).cells.length := hpow.symm
      have := cellE_interp_at Rt hgen χe I hC0 (nodesOf (reorb I.C o.C)) hinj0
        (mkOrbit (reorb I.C o.C) hoC)
        (ComplJ8Of.pubsCOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hC
          (mkOrbit (reorb I.C o.C) hoC)) j j.2
      rw [hfun] at this
      exact this)
  exact key

end Run

#print axioms cellE_n
#print axioms cellE_cols
#print axioms cellE_pubs_at
#print axioms cellE_interp_at
#print axioms cellE_at

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellE
