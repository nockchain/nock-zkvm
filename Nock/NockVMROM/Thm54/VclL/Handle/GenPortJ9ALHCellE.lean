/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHCellE.lean

  **Honest link, file 2: the cell chip over an abstract record `I : InJ9A` at the J-9 AL data `DL`.**
  Twin of `GenPortJ9AHCellE` (`j9aDataOf` replaced by `j9alDataOf`; the cell generator's
  `mv`/`mh` are DL's bumped counts, its `cells`/`acs`/`mx` are DA's by `rfl`).  `hC`/`hpC` (the link equations at DL) are
  the RHS of the DL twins of `cRPK_eqJ`, copied verbatim.  The coin hypothesis is `B8L.Good` (`ComplJ9ALClosed.gL_of`
  gives it from `BRun9AL.Good`); the table fact is `GenPortJ9ALHMemSat.cellOK_run_atL`.  The conclusion is stated at
  `withOrb I o` of the J9A projection `I : InJ9A`, exactly as in `cellE_at`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipPort
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbCellG
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsgJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHMemSat

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHCellE

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellRow
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCell
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.V1J9A Nock.V1J9A.GenJ9AX Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (qM)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipPort

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsgJ (hcs_DAJ hcl_DAJ)

section Run
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × Nock.Jet.Prim.PrimOp))
  {fuel : ℕ} {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DL" => ComplJ9ALData.j9alDataOf P Rg Rt prims hgen

/-- Columns of a chip equal to `chipOf tbl` (local copy of `WalkRun.cols_of_eq`). -/
theorem cols_of_eqE (C : ChipIn) (tbl : Array (Array (ZMod P))) (h : C = chipOf tbl) (i : Fin C.n) (c : ℕ) :
    C.cols c i = (tbl.getD (i : ℕ) #[]).getD c 0 := by
  subst h
  rfl

theorem hcs_DL (χe : CoinsE) : ∀ c ∈ (DL).cells, c.isCell = true := hcs_DAJ Rt hgen χe

theorem hcl_DL (χe : CoinsE) : ComplJ8Data.ClP (DL).cells [] := hcl_DAJ Rt hgen χe

theorem cellE_nL (χe : CoinsE) (I : InJ9A)
    (hC : I.C = chipOf (cellGenB (coOf χe) (yE χe) (hdlB (DL).cells (DL).acs)
        (bigIdOf (DL).acs) (DL).cells
        (DL).mv (DL).mx
        (Array.replicate (DL).cells.length 0) (DL).mh).1) :
    I.C.n = (DL).cells.length := by
  rw [hC]
  exact cellGenB_size _ _ _ _ _ _ _ _ _

theorem cellE_colsL (χe : CoinsE) (I : InJ9A)
    (hC : I.C = chipOf (cellGenB (coOf χe) (yE χe) (hdlB (DL).cells (DL).acs)
        (bigIdOf (DL).acs) (DL).cells
        (DL).mv (DL).mx
        (Array.replicate (DL).cells.length 0) (DL).mh).1)
    (i : Fin I.C.n) (c : ℕ) (hc : c < 242)
    (nodes : Fin (DL).cells.length → ZMod P) (hinj : Function.Injective nodes) {h : ℕ}
    (orbit : StrictOrbitDomain (ZMod P) 3 h) (pubs : ℕ → KC) :
    I.C.cols c i =
      fullCol (ComplJ9ALData.cellsL_pos Rt prims hgen)
        (HonestKW.colW deltaF powerBasis3
          (cellCol deltaF powerBasis3 (VB χe (DL).cells (DL).acs
            (DL).mv (DL).mx))
          (mhv (DL).mh)
          (ComplJ8Cell.kbLB (ComplJ8Data.bigIdOfP P (DL).acs) (DL).cells)
          (ComplJ8Cell.kbRB (ComplJ8Data.bigIdOfP P (DL).acs) (DL).cells)
          (HonestKW.ivW deltaF powerBasis3 (ComplJ9ALData.cellsL_pos Rt prims hgen) nodes orbit (chalsMJ8 deltaF (toχ χe)) pubs
            (cellCol deltaF powerBasis3 (VB χe (DL).cells (DL).acs
              (DL).mv (DL).mx))
            (mhv (DL).mh)
            (ComplJ8Cell.kbLB (ComplJ8Data.bigIdOfP P (DL).acs) (DL).cells)
            (ComplJ8Cell.kbRB (ComplJ8Data.bigIdOfP P (DL).acs) (DL).cells))
          (HonestKW.avW deltaF powerBasis3 (ComplJ9ALData.cellsL_pos Rt prims hgen) nodes orbit (chalsMJ8 deltaF (toχ χe)) pubs
            (cellCol deltaF powerBasis3 (VB χe (DL).cells (DL).acs
              (DL).mv (DL).mx))
            (mhv (DL).mh)
            (ComplJ8Cell.kbLB (ComplJ8Data.bigIdOfP P (DL).acs) (DL).cells)
            (ComplJ8Cell.kbRB (ComplJ8Data.bigIdOfP P (DL).acs) (DL).cells)))
        c (Fin.cast (cellE_nL Rt prims hgen χe I hC) i) := by
  have hcg := cellGenB_cols χe (DL).cells (DL).acs
    (hcs_DL Rt prims hgen χe) (hcl_DL Rt prims hgen χe) (DL).mv (DL).mx
    (DL).mh (ComplJ9ALData.cellsL_pos Rt prims hgen) rfl nodes hinj orbit pubs
    (Fin.cast (cellE_nL Rt prims hgen χe I hC) i) c hc
  rw [← hcg]
  rw [cols_of_eqE I.C _ hC i c]
  rfl

theorem cellE_pubs_atL (χe : CoinsE) (I : InJ9A)
    (hpC : I.M.pubsC = (cellGenB (coOf χe) (yE χe) (hdlB (DL).cells (DL).acs)
        (bigIdOf (DL).acs) (DL).cells
        (DL).mv (DL).mx
        (Array.replicate (DL).cells.length 0) (DL).mh).2) {h : ℕ} (O : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN O (DL).cells.length)) (j : ℕ) :
    K3.toK (I.M.pubsC j) =
      ComplJ8Of.pubsCOf deltaF powerBasis3 (DL) (ComplJ9ALData.cellsL_pos Rt prims hgen) O (toχ χe) j := by
  rw [hpC]
  exact cellGenB_pubs χe (DL).cells (DL).acs
    (hcs_DL Rt prims hgen χe) (hcl_DL Rt prims hgen χe)
    (DL).mv (DL).mx
    (DL).mh (DL) rfl rfl rfl rfl rfl (ComplJ9ALData.cellsL_pos Rt prims hgen)
    O hinj j

theorem cellE_interp_atL (χe : CoinsE) (I : InJ9A)
    (hC0 : I.C = chipOf (cellGenB (coOf χe) (yE χe) (hdlB (DL).cells (DL).acs)
        (bigIdOf (DL).acs) (DL).cells
        (DL).mv (DL).mx
        (Array.replicate (DL).cells.length 0) (DL).mh).1) (ν : Fin I.C.n → ZMod P)
    (hinj : Function.Injective ν) {h : ℕ}
    (O : StrictOrbitDomain (ZMod P) 3 h)
    (pubsF : Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC → ℕ → KC)
    (j : ℕ) (hj : j < 242) :
    Lagrange.interpolate Finset.univ ν (fun i => I.C.cols j i) =
      ComplJ8Enc.cellTrME deltaF powerBasis3 (ComplJ9ALData.cellsL_pos Rt prims hgen)
        (fun i => ν (Fin.cast (cellE_nL Rt prims hgen χe I hC0).symm i))
        O (chalsMJ8 deltaF) pubsF (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.zJ deltaF)
        (ComplJ8Of.encR deltaF) (ComplJ8Of.bigOf (DL)) (DL).cells
        (ComplJ8Of.mvF (DL)) (ComplJ8Of.mxF (DL)) (fun _ => 0)
        (ComplJ8Of.mhF (DL)) (toχ χe) ⟨j, hj⟩ := by
  have hn := cellE_nL Rt prims hgen χe I hC0
  rw [interp_cast hn]
  unfold ComplJ8Enc.cellTrME honestQ
  refine congrArg (Lagrange.interpolate Finset.univ (ν ∘ Fin.cast hn.symm)) ?_
  funext i'
  exact cellE_colsL Rt prims hgen χe I hC0 (Fin.cast hn.symm i') j hj
    (fun i => ν (Fin.cast hn.symm i))
    (hinj.comp (Fin.cast_injective _)) O (pubsF (toχ χe))

theorem cellE_atL (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Rt hgen).roots)
    (χe : CoinsE) (I : InJ9A)
    (hC0 : I.C = chipOf (cellGenB (coOf χe) (yE χe) (hdlB (DL).cells (DL).acs)
        (bigIdOf (DL).acs) (DL).cells
        (DL).mv (DL).mx
        (Array.replicate (DL).cells.length 0) (DL).mh).1)
    (hpC : I.M.pubsC = (cellGenB (coOf χe) (yE χe) (hdlB (DL).cells (DL).acs)
        (bigIdOf (DL).acs) (DL).cells
        (DL).mv (DL).mx
        (Array.replicate (DL).cells.length 0) (DL).mh).2)
    (o : OrbJ9A) (ho : OrbAdm I o)
        (hv' : ValidJ9A (withOrb I o))
    (hχ : (ComplJ9ALRun.B8L deltaF powerBasis3 Rt hgen prims hpG
      (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).Good (toχ χe)) :
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
  have hn := cellE_nL Rt prims hgen χe I hC0
  have hC : 0 < (DL).cells.length := ComplJ9ALData.cellsL_pos Rt prims hgen
  have hoC : OrbOK (reorb I.C o.C) := hv'.oC
  have hinj0 : Function.Injective (nodesOf (reorb I.C o.C)) :=
    GenPortJ9AHOrb.nodesOf_inj _ hoC ho.C.2
  have h31 := ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A
  have hF := ComplJ9ALRun.hFL Rt hgen prims hpG h31
  have hin := GenPortJ9ALHMemSat.hin_B8L deltaF powerBasis3 Rt prims hgen hpG h31 (toχ χe) hχ
  have hmem : (DL).cells.length ∈ ComplJ8Of.sizesJ8 (DL) := by
    simp [ComplJ8Of.sizesJ8]
  have hinjJ : Function.Injective (ComplJ8Of.powN (ComplJ8Of.orbJ8 (DL) hF)
      (DL).cells.length) :=
    (ComplJ8Of.powN_ok _ (ComplJ8Of.le_two_pow_ht _ hmem)).1
  have hV : ∀ e ∈ ComplJ8Of.famCellV deltaF (DL) (K := KC), toχ χe ∉ e.ev :=
    fun e he => hin _
      (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)) e he
  let S : ChipPort KC 242 :=
    ⟨fun {n} hn ν {h} O chals pubs T =>
      (CellTwinKW.cellChipHQKW deltaF powerBasis3 hn ν O chals pubs).rap.Satisfies T ∧
      (CellTwinKW.cellChipHQKW deltaF powerBasis3 hn ν O chals pubs).BindsPreprocessing T⟩
  have key := chipAt_of_cols_pubs S (reorb I.C o.C) hoC hv'.nC hinj0
    (m := (DL).cells.length) hC hn (chalsMJ8 deltaF (toχ χe))
    (fun {h} O => ComplJ8Of.pubsCOf deltaF powerBasis3 (DL) hC O (toχ χe))
    (fun {h} O j => ComplJ8Enc.cellTrME deltaF powerBasis3 hC
        (ComplJ8Of.powN O (DL).cells.length)
        O (chalsMJ8 deltaF)
        (ComplJ8Of.pubsCOf deltaF powerBasis3 (DL) hC O)
        (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.zJ deltaF)
        (ComplJ8Of.encR deltaF) (ComplJ8Of.bigOf (DL)) (DL).cells
        (ComplJ8Of.mvF (DL)) (ComplJ8Of.mxF (DL)) (fun _ => 0)
        (ComplJ8Of.mhF (DL)) (toχ χe) j)
    (by
      intro h O hinjN hadjN
      have hH : ∀ e ∈ ComplJ8Of.famCellH deltaF powerBasis3 (DL) hC O (K := KC),
          toχ χe ∉ e.ev := by
        refine (GenPortJ9AHGood.famCellH_ev_orb deltaF powerBasis3 (DL) hC
          (ComplJ8Of.orbJ8 (DL) hF) _ hinjJ hinjN (toχ χe)).mp ?_
        exact fun e he => hin _
          (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) e he
      exact GenPortJ9ALHMemSat.cellOK_run_atL deltaF powerBasis3 Rt prims hgen hC hpG
        (ComplJ9AChains.hp63_of_G hpG) hleaf O hinjN hadjN (toχ χe) hV hH)
    (withOrb I o).toMsg.pubsC
    (funext fun j => cellE_pubs_atL Rt prims hgen χe I hpC _
      (by
        have hnodes := GenPortJ9AHOrbA.nodesOf_powN _ hoC
        have hpow : ComplJ8Of.powN (mkOrbit (reorb I.C o.C) hoC)
            (DL).cells.length =
            nodesOf (reorb I.C o.C) ∘ Fin.cast hn.symm := by
          rw [hnodes]; rfl
        rw [hpow]; exact hinj0.comp (Fin.cast_injective _)) j)
    (qM deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8 (chalsMJ8 deltaF (toχ χe))
        (withOrb I o).toMsg.pubsC)
    (by
      have hnodes := GenPortJ9AHOrbA.nodesOf_powN _ hoC
      have hpow : ComplJ8Of.powN (mkOrbit (reorb I.C o.C) hoC)
          (DL).cells.length =
          nodesOf (reorb I.C o.C) ∘ Fin.cast hn.symm := by
        rw [hnodes]; rfl
      funext j
      have hfun : (fun i => nodesOf (reorb I.C o.C) (Fin.cast hn.symm i)) =
          ComplJ8Of.powN (mkOrbit (reorb I.C o.C) hoC)
            (DL).cells.length := hpow.symm
      have := cellE_interp_atL Rt prims hgen χe I hC0 (nodesOf (reorb I.C o.C)) hinj0
        (mkOrbit (reorb I.C o.C) hoC)
        (ComplJ8Of.pubsCOf deltaF powerBasis3 (DL) hC
          (mkOrbit (reorb I.C o.C) hoC)) j j.2
      rw [hfun] at this
      exact this)
  exact key

end Run

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHCellE
