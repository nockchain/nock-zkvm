/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHMsgJ.lean

  Sizes and the ten message fields of the jet-calling exec record `recJ9AXJ` agree with `BRun9A`'s (no `hnc`).
  Twins of `GenPortJ9AHMsg` at `recJ9AXJ Rt s f χe t r` with the data
  equalities of `GenPortJ9AHJRun` (`cs_eqJ … jrows_eqJ`, all `rfl`/short) in place of `hnc`. -/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsg
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStatic
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHNonChip

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsgJ

section Run

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 rowsOfT9 genX9T)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData (fieldAx9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChains (idOf9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf cellsA_pos acsA_pos)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
  (BRun9A MA W9 N9 N9_def idOfA nXA nAA nXOf nSOf nSOf_eq nSOf_pos axOnA spOnA ρA ρSA pubsXA pubsSA vSA mSA
   Rows31A hF_run sizesA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of (DvdOK orbJ8 pubsCOf pubsWOf pubsAOf pubsJOf)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj (RnOf)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (OrbAdm orbOf orbAdm_self)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb (chipOf_n_le validJ9A_of_chips)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp (chipOf_n compGenX9_size)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCoin (hchi_toχ mOf_eq_mCOf)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot (compGenX9_rho compGenX9_rhoS)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAx (pubsXA_eq axn_eq)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHSp (spGenE_size)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips (pubsSE_eq)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun
open Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff Nock.V1J9A.GenJ9AX Nock.V1J9A.GenCompX9

variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hpG : P = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf P Rg Rt hgen)) (χe : CoinsE)

local notation "DA" => j9aDataOf P Rg Rt hgen
local notation "BR" => BRun9A deltaF powerBasis3 Rt hgen hpG h31A
local notation "IJ" => recJ9AXJ Rt s f χe t r

/-! ## 1. Field-level `rfl` lemmas -/

theorem Pb_n : (BR).Pb.n = N9 t := rfl
theorem Pb_nC : (BR).Pb.nC = (DA).cells.length := rfl
theorem Pb_nW : (BR).Pb.nW = (walkRows (DA).cells (DA).reads).length := rfl
theorem Pb_kroots : (BR).Pb.kroots = krW (DA).cells (DA).reads := rfl
theorem Pb_nA : (BR).Pb.nA = (DA).acs.length := rfl
theorem Pb_nV : (BR).Pb.nV = ComplJ8Of.nVOf (DA) := rfl
theorem Pb_krootsV : (BR).Pb.krootsV = ComplJ8Of.krVOf (DA) := rfl
theorem Pb_nX : (BR).Pb.nX = nXA (p := P) Rt hgen := rfl
theorem Pb_nS : (BR).Pb.nS = nSOf P t := rfl
theorem Pb_nJ : (BR).Pb.nJ = (DA).jrows.length := rfl

/-- **`regs_B'`**: the jet record's registry fields are the honest verifier's. -/
theorem regs_B' : (IJ).regs = (BR).Pb.regs ∧ (IJ).ids = (BR).Pb.ids ∧ (IJ).idx = (BR).Pb.idx ∧
    (IJ).rk = (BR).Pb.rk ∧ (IJ).Rt = (BR).Pb.Rt ∧
    List.ofFn (IJ).lay = Nock.Jet.ChipJ8.layoutJ8 (BR).Pb.Rt (BR).Pb.regs (BR).Pb.ids :=
  ⟨regs_eqJ Rt hgen χe, ids_eqJ Rt hgen χe, idx_eqJ Rt hgen χe, rk_eqJ Rt hgen χe, Rt_eqJ Rt hgen χe,
    (lay_eqJ Rt hgen χe).trans rfl⟩

theorem g_B' : (IJ).g = (BR).Pb.regs.length := rfl

/-! ## 2. Data (jets) -/

theorem hcs_DAJ (χe : CoinsE) : ∀ c ∈ (DA).cells, c.isCell = true := by
  rw [← cs_eqJ Rt hgen χe]
  exact fun c hc => (ComplJ8Walk.cellsOfRoots_mem _ c hc).1

theorem hcl_DAJ (χe : CoinsE) : ComplJ8Data.ClP (DA).cells [] := by
  rw [← cs_eqJ Rt hgen χe]
  exact ComplJ8Data.cells_closed _

/-! ## 3. Sizes: X, C, AX, SP, J -/

theorem size_X : (IJ).X.n = (BR).Pb.n := by
  have e : (IJ).X.n = N9 t := by
    show (chipOf (compK Rt s f χe (RnOf t r)).rows).n = N9 t
    unfold compK
    rw [chipOf_n, compGenX9_size, N9_def]
    try rfl
  exact e

theorem cRPK_eqJ :
    cRPK Rt s f χe (RnOf t r) =
      cellGenB (coOf χe) (yE χe) (hdlB (DA).cells (DA).acs) (bigIdOf (DA).acs) (DA).cells
        (DA).mv (DA).mx (Array.replicate (DA).cells.length 0) (DA).mh := by
  unfold cRPK mx1K HK
  rw [cs_eqJ Rt hgen χe, acs_eqJ Rt hgen χe, mv_eqJ Rt hgen χe, mx_eqJ Rt hgen χe, mh_eqJ Rt hgen χe]

theorem size_C : (IJ).C.n = (BR).Pb.nC := by
  have e : (IJ).C.n = (DA).cells.length := by
    show (chipOf (cRPK Rt s f χe (RnOf t r)).1).n = _
    rw [cRPK_eqJ Rt hgen χe]
    exact GenPortJ9AHCell.cellGenB_size _ _ _ _ _ _ _ _ _
  exact e

theorem xRPK_eqJ :
    xRPK Rt s f χe (RnOf t r) =
      GenAxE.axGenOf χe (DA).acs.length (DA).H (rowsOfT9 t) (axOnA t) := by
  show GenAxE.axGenOf χe (acsK Rt s f χe (RnOf t r)).length (HK Rt s f χe (RnOf t r)) (rowsOfT9 t)
    (axOnA t) = _
  rw [HJ_eqJ Rt hgen χe, acs_eqJ Rt hgen χe]

theorem size_AX : (IJ).AX.n = (BR).Pb.nX := by
  have e : (IJ).AX.n = nXA (p := P) Rt hgen := by
    show (chipOf (xRPK Rt s f χe (RnOf t r)).1).n = _
    rw [xRPK_eqJ Rt hgen χe]
    exact axn_eq Rt hgen χe
  exact e

theorem sRPK_of_spOn (h : spOnA P t = true) :
    sRPK Rt s f χe (RnOf t r) =
      GenSpE.spGenE χe (acsK Rt s f χe (RnOf t r)).length (GenSpE.vSE (GenPortJ9AHProj.rows9J s f χe (RnOf t r)))
        (GenSpE.mSE (GenPortJ9AHProj.rows9J s f χe (RnOf t r))
          (GenSpE.vSE (GenPortJ9AHProj.rows9J s f χe (RnOf t r)))) := by
  have hh : GenPortJ9AHProj.spOnJ s f χe (RnOf t r) = true := h
  unfold sRPK
  rw [if_pos hh]

theorem sRPK_of_not_spOn (h : ¬ spOnA P t = true) :
    sRPK Rt s f χe (RnOf t r) = (#[Array.replicate 90 0], fun _ => (0 : K3)) := by
  have hh : GenPortJ9AHProj.spOnJ s f χe (RnOf t r) = false := Bool.eq_false_iff.mpr h
  unfold sRPK
  rw [hh]
  rfl

theorem size_SP : (IJ).SP.n = (BR).Pb.nS := by
  rw [Pb_nS Rt hgen hpG h31A]
  by_cases h : spOnA P t = true
  · show (chipOf (sRPK Rt s f χe (RnOf t r)).1).n = _
    rw [sRPK_of_spOn Rt χe h]
    exact (spGenE_size χe _ _ _).trans (nSOf_eq h).symm
  · show (chipOf (sRPK Rt s f χe (RnOf t r)).1).n = _
    rw [sRPK_of_not_spOn Rt χe h]
    have h1 : nSOf P t = 1 := by unfold nSOf; rw [if_neg h]
    rw [h1]
    rfl

theorem jrows_len_layK : (DA).jrows.length = (layK Rt s f χe (RnOf t r)).length := by
  have h := ComplJ8Jet.jrows_pre_run (p := P) Rt hgen
  have h2 := congrArg List.length h
  rw [List.length_map] at h2
  exact h2

theorem size_J : (IJ).J.n = (BR).Pb.nJ :=
  (jrows_len_layK Rt hgen χe).symm

/-! ## 4. Messages: m, ρ, ρS, pubsC, pubsX, pubsS -/

theorem msg_m : (IJ).toMsg.m = ((BR).M (toχ χe)).m :=
  ((rfl : (IJ).toMsg.m = mOf (cK Rt s f χe (RnOf t r)) (HK Rt s f χe (RnOf t r))).trans
    ((congrArg (mOf (cK Rt s f χe (RnOf t r))) (HJ_eqJ Rt hgen χe)).trans (mOf_eq_mCOf _ _)))

theorem msg_ρ : (IJ).toMsg.ρ = ((BR).M (toχ χe)).ρ := by
  funext i
  have e := (GenPortJ9AHMsg.rho_aux ⟨s, f, r⟩ (DA).H (HK Rt s f χe (RnOf t r)) (DA).pd
    (pdK Rt s f χe (RnOf t r)) (idOfA (p := P) Rt hgen) (idOfK Rt s f χe (RnOf t r)) (W9 t) χe
    (HJ_eqJ Rt hgen χe) (pd_eqJ Rt hgen χe) (idOf_eqJ Rt hgen χe) (IJ).M.ρ (IJ).M.ρS ⟨rfl, rfl⟩).1
  show K6.toQ ((IJ).M.ρ i) = ρA deltaF powerBasis3 Rt hgen (toχ χe) i
  rw [e]
  exact compGenX9_rho Rt hgen (toχ χe) χe (hchi_toχ χe) _ i

theorem msg_ρS : (IJ).toMsg.ρS = ((BR).M (toχ χe)).ρS := by
  have e := (GenPortJ9AHMsg.rho_aux ⟨s, f, r⟩ (DA).H (HK Rt s f χe (RnOf t r)) (DA).pd
    (pdK Rt s f χe (RnOf t r)) (idOfA (p := P) Rt hgen) (idOfK Rt s f χe (RnOf t r)) (W9 t) χe
    (HJ_eqJ Rt hgen χe) (pd_eqJ Rt hgen χe) (idOf_eqJ Rt hgen χe) (IJ).M.ρ (IJ).M.ρS ⟨rfl, rfl⟩).2
  show K6.toQ ((IJ).M.ρS) = ρSA deltaF powerBasis3 Rt hgen (toχ χe)
  rw [e]
  exact compGenX9_rhoS Rt hgen (toχ χe) χe (hchi_toχ χe) _

theorem msg_pubsC : (IJ).toMsg.pubsC = ((BR).M (toχ χe)).pubsC := by
  funext j
  have hF := hF_run Rt hgen hpG h31A
  show K3.toK ((cRPK Rt s f χe (RnOf t r)).2 j) =
    pubsCOf deltaF powerBasis3 (DA) (cellsA_pos Rt hgen) (orbJ8 (DA) hF) (toχ χe) j
  have hmem : (DA).cells.length ∈ ComplJ8Of.sizesJ8 (DA) := by
    simp [ComplJ8Of.sizesJ8]
  have hinj : Function.Injective (ComplJ8Of.powN (orbJ8 (DA) hF) (DA).cells.length) :=
    (ComplJ8Of.powN_ok _ (ComplJ8Of.le_two_pow_ht _ hmem)).1
  rw [cRPK_eqJ Rt hgen χe]
  exact GenPortJ9AHCell.cellGenB_pubs χe (DA).cells (DA).acs
    (hcs_DAJ Rt hgen χe) (hcl_DAJ Rt hgen χe) (DA).mv (DA).mx
    (DA).mh (DA) rfl rfl rfl rfl rfl (cellsA_pos Rt hgen)
    (orbJ8 (DA) hF) hinj j

theorem msg_pubsX : (IJ).toMsg.pubsX = ((BR).M (toχ χe)).pubsX := by
  funext j
  show K3.toK ((xRPK Rt s f χe (RnOf t r)).2 j) = pubsXA deltaF Rt hgen (toχ χe) j
  rw [pubsXA_eq Rt hgen χe j, xRPK_eqJ Rt hgen χe]

theorem getD_map_ltJ (g : ℕ → ℕ) (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    (l.map g).getD i 0 = g (l.getD i 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem msg_pubsS : (IJ).toMsg.pubsS = ((BR).M (toχ χe)).pubsS := by
  funext j
  show K3.toK ((sRPK Rt s f χe (RnOf t r)).2 j) = pubsSA deltaF Rt hgen (toχ χe) j
  unfold pubsSA
  by_cases h : spOnA P t = true
  · rw [if_pos h, sRPK_of_spOn Rt χe h, acs_eqJ Rt hgen χe]
    have hn : nSOf P t = (GenSpE.vSE (GenPortJ9AHProj.rows9J s f χe (RnOf t r))).length := nSOf_eq h
    have key := pubsSE_eq χe (DA).acs.length (GenSpE.vSE (GenPortJ9AHProj.rows9J s f χe (RnOf t r)))
      (GenSpE.mSE (GenPortJ9AHProj.rows9J s f χe (RnOf t r))
        (GenSpE.vSE (GenPortJ9AHProj.rows9J s f χe (RnOf t r)))) hn (nSOf_pos P t) j
    have hm : (fun i : Fin (nSOf P t) =>
        (GenSpE.mSE (GenPortJ9AHProj.rows9J s f χe (RnOf t r))
          (GenSpE.vSE (GenPortJ9AHProj.rows9J s f χe (RnOf t r)))).getD i 0) =
        mSA (p := P) (t := t) := by
      funext i
      have hi : (i : ℕ) < (GenSpE.vSE (GenPortJ9AHProj.rows9J s f χe (RnOf t r))).length := hn ▸ i.2
      show (List.map _ (GenSpE.vSE (GenPortJ9AHProj.rows9J s f χe (RnOf t r)))).getD i 0 = _
      rw [getD_map_ltJ _ _ _ hi]
      rfl
    rw [hm] at key
    exact key
  · rw [if_neg h, sRPK_of_not_spOn Rt χe h]
    exact K3.toK_zero


/-! ## 5. The walk (W, kroots, pubsW) -/

local notation "DR" => GenPortJ9AHWalkRun.regD (j9aDataOf P Rg Rt hgen)

theorem hall_DAJ : ∀ x ∈ (DA).reads, VclL.isPathAx x.2 = true := by
  intro x hx
  have hx' : x ∈ ComplJ9ADataRec.readsA t := hx
  simp only [ComplJ9ADataRec.readsA, List.mem_append] at hx'
  refine ComplJ8OfBal.isPathAx_of_two_le ?_
  rcases hx' with hx' | hx'
  · unfold ComplJ9AReads.walkReadsX9 at hx'
    simpa using (List.mem_filter.mp hx').2
  · unfold ComplJ9AChainsRun.axChainReadsK9 at hx'
    simpa using (List.mem_filter.mp hx').2

theorem hwalk_DAJ (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t)) :
    ComplJ8Walk.WalkDepthOK (DA).reads :=
  ComplJ9ADataRec.walkDepthOK_readsA Rt hgen hwalk9

theorem hp_DRJ : (walkRows (DR).cells (DR).reads).Perm (walkRows (DA).cells (DA).reads) :=
  GenPortJ9AHWalkOrd.walkRows_regroup_perm _ _ (hall_DAJ Rt hgen)

theorem hwcell_DAJ : ∀ u ∈ walkRows (DA).cells (DA).reads, u.label.node ∈ (DA).cells :=
  ComplJ9ABalGen.walkRows_node_cells_gen _ _ (ComplJ8Data.cells_closed _)
    (ComplJ9ADataRec.cellsA_pos Rt hgen) (ComplJ9ABalW.hslotA hgen) (ComplJ9ABalW.hrootA hgen)

theorem hwcell_DRJ : ∀ u ∈ walkRows (DR).cells (DR).reads, u.label.node ∈ (DR).cells :=
  GenPortJ9AHWalkGlue.hwcell_reg _ _ (hall_DAJ Rt hgen) (hwcell_DAJ Rt hgen)

theorem hwroot_DRJ : ∀ u ∈ walkRows (DR).cells (DR).reads,
    u.label.root ∈ (DR).cells ∨ u.label.root.isCell = false :=
  GenPortJ9AHWalkGlue.hwroot_reg _ _ (hall_DAJ Rt hgen) (hwcell_DAJ Rt hgen)

theorem wsKr_eqJ (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t)) (χe : CoinsE) :
    wsKrK Rt s f χe (RnOf t r) =
      ((walkRows (DR).cells (DR).reads).map GenPortJ9AHWalkRow.wrowOf, krW (DR).cells (DR).reads) := by
  have h := GenPortJ9AHWalkBfs.walkGen_eq_map (DA).cells (ComplJ9ADataRec.readsA t) (hall_DAJ Rt hgen)
    (hwalk_DAJ Rt hgen hwalk9)
  show walkGen ((DA).cells.headD (.atom 0)) (ComplJ9ADataRec.readsA t) = _
  exact Prod.ext h.1 h.2

theorem wRPK_eqJ (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t)) (χe : CoinsE) :
    wRPK Rt s f χe (RnOf t r) =
      walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) (DR).H (idxN (DR).cells)
        HonestK8.certB8 (DR).cells ((walkRows (DR).cells (DR).reads).map GenPortJ9AHWalkRow.wrowOf)
        (krW (DR).cells (DR).reads) := by
  unfold wRPK
  rw [HJ_eqJ Rt hgen χe, wsKr_eqJ Rt hgen hwalk9 χe, cs_eqJ Rt hgen χe]

theorem size_W (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t)) :
    (IJ).W.n = (BR).Pb.nW := by
  have e : (IJ).W.n = (walkRows (DR).cells (DR).reads).length := by
    show (chipOf (wRPK Rt s f χe (RnOf t r)).1).n = _
    rw [wRPK_eqJ Rt hgen hwalk9 χe]
    show (walkGenRowsB _ _ _ _ _ _ _ _ _ _).1.size = _
    rw [GenPortJ9AHWalkGlue.walkGenRowsB_size, List.length_map]
  exact e.trans (hp_DRJ Rt hgen).length_eq

theorem size_kroots (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t)) :
    (IJ).kroots = (BR).Pb.kroots := by
  have e : (IJ).kroots = krW (DR).cells (DR).reads := by
    show (wsKrK Rt s f χe (RnOf t r)).2 = _
    rw [wsKr_eqJ Rt hgen hwalk9 χe]
  exact e.trans (GenPortJ9AHWalkOrd.krW_regroup _ _ (hall_DAJ Rt hgen))

theorem powN_inj_DRJ (hF : DvdOK (DA)) :
    Function.Injective (ComplJ8Of.powN (orbJ8 (DA) hF) (walkRows (DR).cells (DR).reads).length) := by
  have hmem : (walkRows (DA).cells (DA).reads).length ∈ ComplJ8Of.sizesJ8 (DA) := by
    simp [ComplJ8Of.sizesJ8]
  have hle : (walkRows (DR).cells (DR).reads).length ≤ 2 ^ ComplJ8Of.htJ8 (DA) :=
    (hp_DRJ Rt hgen).length_eq.le.trans (ComplJ8Of.le_two_pow_ht (DA) hmem)
  exact (ComplJ8Of.powN_ok _ hle).1

theorem pubs_DR_DAJ (hF : DvdOK (DA)) (j : ℕ) :
    pubsWOf deltaF powerBasis3 (DR) (orbJ8 (DA) hF) (toχ χe) j =
      pubsWOf deltaF powerBasis3 (DA) (orbJ8 (DA) hF) (toχ χe) j := by
  have hmem : (walkRows (DA).cells (DA).reads).length ∈ ComplJ8Of.sizesJ8 (DA) := by
    simp [ComplJ8Of.sizesJ8]
  have hinj : Function.Injective (ComplJ8Of.powN (orbJ8 (DA) hF)
      (walkRows (DA).cells (DA).reads).length) :=
    (ComplJ8Of.powN_ok _ (ComplJ8Of.le_two_pow_ht _ hmem)).1
  exact congrFun (GenPortJ9AHWalkPub.pubsWOf_perm deltaF powerBasis3 (DA) (DR) rfl rfl (hp_DRJ Rt hgen)
      (orbJ8 (DA) hF) (orbJ8 (DA) hF) hinj (powN_inj_DRJ Rt hgen hF) (toχ χe)) j

theorem msg_pubsW (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t)) :
    (IJ).toMsg.pubsW = ((BR).M (toχ χe)).pubsW := by
  funext j
  have hF := hF_run Rt hgen hpG h31A
  have a : ∀ c ∈ (DR).cells, c.isCell = true := hcs_DAJ Rt hgen χe
  have b := hwcell_DRJ Rt hgen
  have c := hwroot_DRJ Rt hgen
  have hI := powN_inj_DRJ Rt hgen hF
  have e1 := GenPortJ9AHWalkPubs.walkGenRowsB_pubs χe (DR) a b c (orbJ8 (DA) hF) hI j
  have e2 : K3.toK ((IJ).M.pubsW j) = pubsWOf deltaF powerBasis3 (DR) (orbJ8 (DA) hF) (toχ χe) j := by
    show K3.toK ((wRPK Rt s f χe (RnOf t r)).2 j) = _
    rw [wRPK_eqJ Rt hgen hwalk9 χe]
    exact e1
  exact e2.trans (pubs_DR_DAJ Rt hgen χe hF j)

/-! ## 6. The atom table (A, pubsA) -/

theorem ptK_eqJ (χe : CoinsE) :
    ptK Rt s f χe (RnOf t r) = ComplJ8Data.ptrP P (DA).acs (DA).rows :=
  GenPortJ9.ptrE_eq' (acsK Rt s f χe (RnOf t r)) (RnOf t r).rows

theorem readsK_eqJ (χe : CoinsE) : readsK Rt s f χe (RnOf t r) = (DA).preads := by
  have hpd' : pdK Rt s f χe (RnOf t r) = (ComplJ8Data.j8DataOf P Rg Rt hgen).pd := pd_eqJ Rt hgen χe
  have hH : HK Rt s f χe (RnOf t r) = (ComplJ8Data.j8DataOf P Rg Rt hgen).H := HJ_eqJ Rt hgen χe
  rw [ComplJ9ADataRec.j9aDataOf_preads]
  unfold readsK
  rw [hH, hpd']
  rfl

theorem vsKrVK_eqJ (χe : CoinsE) : vsKrVK Rt s f χe (RnOf t r) = ((DA).vs, (DA).krV) := by
  unfold vsKrVK
  rw [readsK_eqJ Rt hgen χe]
  exact Prod.ext rfl rfl

theorem aRPK_eqJ (χe : CoinsE) :
    aRPK Rt s f χe (RnOf t r) =
      atomGenE (ComplJ8Data.ptrP P (DA).acs (DA).rows) χe (DA).acs (DA).info (DA).mb (DA).mxA (DA).mhA := by
  have hinfo : infoOfE (acsK Rt s f χe (RnOf t r)) (ptK Rt s f χe (RnOf t r)) (RnOf t r).rows =
      (DA).info := GenPortJ9.infoOfE_eq _ _
  have hmb : Nock.V1J9.Gen9.mbCounts9 (acsK Rt s f χe (RnOf t r)) (csK Rt s f χe (RnOf t r))
      (cK Rt s f χe (RnOf t r)) = (DA).mb := by
    show Nock.V1J9.Gen9.mbCounts9 (DA).acs (DA).cells ⟨s, f, r⟩ = (DA).mb
    rw [← ComplJ9BOf.mbCountsP9_gen]
    exact (ComplJ9BOf.j9_mb_eq Rg Rt hgen).symm
  have hv : (vsKrVK Rt s f χe (RnOf t r)).1 = (DA).vs := congrArg Prod.fst (vsKrVK_eqJ Rt hgen χe)
  have hmx : wCounts (rIAK Rt s f χe (RnOf t r)) (acsK Rt s f χe (RnOf t r)) (vsKrVK Rt s f χe (RnOf t r)).1 =
      (DA).mxA := by
    rw [hv]; rfl
  unfold aRPK
  rw [hinfo, hmb, hmx, ptK_eqJ Rt hgen χe, acs_eqJ Rt hgen χe]
  try rfl

theorem size_A : (IJ).A.n = (BR).Pb.nA := by
  have e : (IJ).A.n = (DA).acs.length := by
    show (chipOf (aRPK Rt s f χe (RnOf t r)).1).n = _
    rw [aRPK_eqJ Rt hgen χe]
    exact GenPortJ9AHAtomCols2.atomGenE_size (ComplJ8Data.ptrP P (DA).acs (DA).rows) χe (DA).acs (DA).info
      (DA).mb (DA).mxA (DA).mhA
  exact e

theorem hN_runJ (h31A : Rows31A (DA)) : (ComplJ8Data.j8DataOf P Rg Rt hgen).rows.size ≤ 2 ^ 31 := by
  have h : (bfsForest [t]).length ≤ 2 ^ 31 := h31A _ (ComplJ9AOfStatic.mem_bfs Rt hgen)
  have e : (ComplJ8Data.rowsOfT t).size = (bfsForest [t]).length := by simp [ComplJ8Data.rowsOfT]
  show (ComplJ8Data.rowsOfT t).size ≤ 2 ^ 31
  rw [e]
  exact h

theorem msg_pubsA : (IJ).toMsg.pubsA = ((BR).M (toχ χe)).pubsA := by
  funext j
  have hF := hF_run Rt hgen hpG h31A
  have hmem : (DA).acs.length ∈ ComplJ8Of.sizesJ8 (DA) := by simp [ComplJ8Of.sizesJ8]
  have hinj : Function.Injective (ComplJ8Of.powN (orbJ8 (DA) hF) (DA).acs.length) :=
    (ComplJ8Of.powN_ok _ (ComplJ8Of.le_two_pow_ht _ hmem)).1
  show K3.toK ((aRPK Rt s f χe (RnOf t r)).2 j) =
    pubsAOf deltaF powerBasis3 (DA) (acsA_pos Rt hgen) (orbJ8 (DA) hF) (toχ χe) j
  rw [aRPK_eqJ Rt hgen χe]
  have hacs : (DA).acs = ComplJ8Data.acsP P (DA).bigs (DA).dupP := rfl
  have hinfo : (DA).info = ComplJ8Data.infoOfP P (DA).acs (DA).rows := rfl
  have hg : ComplJ8Atom.GenHyp (DA).bigs (DA).dupP (DA).rows (DA).mb :=
    ComplJ9ATables.genHyp_mbXA Rg Rt hgen (hN_runJ Rt hgen h31A)
  exact GenPortJ9AHAtom.atomGenE_pubs (DA) hacs hinfo hg χe (acsA_pos Rt hgen) (orbJ8 (DA) hF) hinj j

/-! ## 7. The atom walk (V, krootsV, pubsV) -/

local notation "DV" => GenPortJ9AHAWOrd.regV (j9aDataOf P Rg Rt hgen)

theorem HAK_eqJ (χe : CoinsE) : HAK Rt s f χe (RnOf t r) = Nock.V1J8.Gen.hdl (DA).acs := by
  unfold HAK
  rw [acs_eqJ Rt hgen χe]

theorem rIAK_eqJ (χe : CoinsE) : rIAK Rt s f χe (RnOf t r) = ComplJ8Data.rIAP P (DA).acs := by
  unfold rIAK
  rw [acs_eqJ Rt hgen χe]
  rfl

theorem vsKrVK_neJ (χe : CoinsE) (hne : (DA).preads ≠ []) :
    walkGen padN (DA).preads = ((DA).vs, (DA).krV) := by
  have e := vsKrVK_eqJ Rt hgen χe
  unfold vsKrVK at e
  rw [readsK_eqJ Rt hgen χe] at e
  have hie : (DA).preads.isEmpty = false := by
    cases hh : (DA).preads.isEmpty
    · rfl
    · exact absurd (List.isEmpty_iff.mp hh) hne
  simp only [hie, Bool.false_eq_true, if_false] at e
  exact e

theorem krV_zero_iffJ (χe : CoinsE) :
    (vsKrVK Rt s f χe (RnOf t r)).2 = 0 ↔ (DA).preads = [] := by
  by_cases h : (DA).preads = []
  · unfold vsKrVK
    rw [readsK_eqJ Rt hgen χe, h]
    simp
  · refine ⟨fun hz => ?_, fun hh => absurd hh h⟩
    have e := vsKrVK_neJ Rt hgen χe h
    rw [vsKrVK_eqJ Rt hgen χe] at hz
    have := GenPortJ9AHAWOrd.walkGen_snd_ne_zero padN h
    rw [e] at this
    exact absurd hz this

theorem hallV_DAJ : ∀ x ∈ (DA).preads, VclL.isPathAx x.2 = true :=
  ComplJ9ABalFA.hallA_A Rt hgen (rfl : P = Nock.Atoms.p)

theorem hwA_DAJ : ∀ u ∈ walkRows (DA).acs (DA).preads, u.label.node ∈ (DA).acs :=
  ComplJ9ABalFA.hwA_A Rt hgen (rfl : P = Nock.Atoms.p)

theorem hwalkV_DAJ (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads) :
    ComplJ8Walk.WalkDepthOK (DA).preads :=
  ComplJ9ADataRec.walkDepthOK_preadsA Rt hgen hax9 hwalkA

theorem hwA_DRJ : ∀ u ∈ walkRows (DV).acs (DV).preads, u.label.node ∈ (DV).acs :=
  GenPortJ9AHAWOrd.hwA_regV (DA) (hallV_DAJ Rt hgen) (hwA_DAJ Rt hgen)

theorem hcl_DRJ : ∀ y ∈ (DV).acs, y.isCell = true :=
  fun y hy => ComplJ8OfBal.acs_cell Rt hgen (rfl : P = Nock.Atoms.p) y hy

theorem hsm_DRJ : ∀ y ∈ (DV).acs, GenPortJ9AHAtomRow.Small y := by
  intro y hy
  have hbigs : ∀ a ∈ (DA).bigs, P ≤ a := fun a ha =>
    ((ComplJ8Atom.mem_bigsP P (ComplJ8Data.j8DataOf P Rg Rt hgen).roots
      (ComplJ8Data.j8DataOf P Rg Rt hgen).rows a).mp ha).2
  exact GenPortJ9AHAtomRow.small_of_acs (DA).bigs (DA).dupP hbigs y hy

theorem vs_krV_presentJ (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads)
    (χe : CoinsE) (hne : (DA).preads ≠ []) :
    (DA).vs = ((walkRows (DV).acs (DV).preads).map GenPortJ9AHWalkBfs.wrowOf) ∧
      (DA).krV = krW (DV).acs (DV).preads := by
  have e := vsKrVK_neJ Rt hgen χe hne
  obtain ⟨a, b⟩ := GenPortJ9AHAWOrd.walkGen_padN_eq_map (DA).acs (DA).preads hne
    (hallV_DAJ Rt hgen) (hwalkV_DAJ Rt hgen hax9 hwalkA)
  rw [e] at a b
  exact ⟨a, b⟩

theorem vRPK_eq_awEJ (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads)
    (χe : CoinsE) (hne : (DA).preads ≠ []) :
    vRPK Rt s f χe (RnOf t r) = GenPortJ9AHAW.awE χe (DV) := by
  have hz : (vsKrVK Rt s f χe (RnOf t r)).2 ≠ 0 :=
    fun hh => hne ((krV_zero_iffJ Rt hgen χe).mp hh)
  obtain ⟨h1, h2⟩ := vs_krV_presentJ Rt hgen hax9 hwalkA χe hne
  unfold vRPK
  rw [if_neg hz, ptK_eqJ Rt hgen χe, HAK_eqJ Rt hgen χe, rIAK_eqJ Rt hgen χe, acs_eqJ Rt hgen χe,
    vsKrVK_eqJ Rt hgen χe]
  show walkGenRowsBE _ _ _ _ _ _ _ _ _ (DA).vs (DA).krV = _
  rw [h1, h2]

theorem vRPK_absent (χe : CoinsE) (h : (DA).preads = []) :
    vRPK Rt s f χe (RnOf t r) = (#[Array.replicate 166 0], fun _ => (0 : K3)) := by
  unfold vRPK
  rw [if_pos ((krV_zero_iffJ Rt hgen χe).mpr h)]

theorem size_V (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads) :
    (IJ).V.n = (BR).Pb.nV := by
  have h : (IJ).V.n = ComplJ8Of.nVOf (DV) := by
    show (chipOf (vRPK Rt s f χe (RnOf t r)).1).n = _
    by_cases h : (DA).preads = []
    · rw [vRPK_absent Rt hgen χe h]
      have h' : (DV).preads = [] := GenPortJ9AHAWOrd.regroup_eq_nil_iff.mpr h
      unfold ComplJ8Of.nVOf
      rw [if_pos h']
      rfl
    · have h' : (DV).preads ≠ [] := fun e => h (GenPortJ9AHAWOrd.regroup_eq_nil_iff.mp e)
      rw [vRPK_eq_awEJ Rt hgen hax9 hwalkA χe h]
      exact GenPortJ9AHAW.walkGenRowsBE_size χe (DV) h'
  exact h.trans (GenPortJ9AHAWOrd.nVOf_regV (DA) (hallV_DAJ Rt hgen))

theorem size_krootsV (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads) :
    (IJ).krootsV = (BR).Pb.krootsV := by
  show (vsKrVK Rt s f χe (RnOf t r)).2 = ComplJ8Of.krVOf (DA)
  by_cases h : (DA).preads = []
  · rw [(krV_zero_iffJ Rt hgen χe).mpr h]
    unfold ComplJ8Of.krVOf
    rw [if_pos h]
  · have hh := vs_krV_presentJ Rt hgen hax9 hwalkA χe h
    rw [vsKrVK_eqJ Rt hgen χe]
    show (DA).krV = _
    rw [hh.2]
    unfold ComplJ8Of.krVOf
    rw [if_neg h]
    exact GenPortJ9AHWalkOrd.krW_regroup (DA).acs (DA).preads (hallV_DAJ Rt hgen)

theorem msg_pubsV (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads) :
    (IJ).toMsg.pubsV = ((BR).M (toχ χe)).pubsV := by
  funext j
  have hF := hF_run Rt hgen hpG h31A
  have hmem : ComplJ8Of.nVOf (DA) ∈ ComplJ8Of.sizesJ8 (DA) := by simp [ComplJ8Of.sizesJ8]
  have hinj : Function.Injective (ComplJ8Of.powN (orbJ8 (DA) hF) (ComplJ8Of.nVOf (DA))) :=
    (ComplJ8Of.powN_ok _ (ComplJ8Of.le_two_pow_ht _ hmem)).1
  show K3.toK ((IJ).M.pubsV j) =
    (ComplJ9BBalF.avOf9 deltaF powerBasis3 (DA) hF
      (ComplJ8Of.avOf deltaF powerBasis3 (DA) hF (acsA_pos Rt hgen))).pubsV (toχ χe) j
  show K3.toK ((vRPK Rt s f χe (RnOf t r)).2 j) = ComplJ9BBalF.pubsVOf9 deltaF powerBasis3 (DA) (orbJ8 (DA) hF) (toχ χe) j
  by_cases h0 : (DA).preads = []
  · rw [vRPK_absent Rt hgen χe h0]
    show K3.toK (0 : K3) = _
    unfold ComplJ9BBalF.pubsVOf9
    rw [if_pos h0, K3.toK_zero]
  · have h' : (DV).preads ≠ [] := fun e => h0 (GenPortJ9AHAWOrd.regroup_eq_nil_iff.mp e)
    have hall := hallV_DAJ Rt hgen
    have hinj' : Function.Injective (ComplJ8Of.powN (orbJ8 (DA) hF) (ComplJ8Of.nVOf (DV))) := by
      rw [GenPortJ9AHAWOrd.nVOf_regV (DA) hall]
      exact hinj
    rw [vRPK_eq_awEJ Rt hgen hax9 hwalkA χe h0]
    rw [GenPortJ9AHAWPubs.walkGenRowsBE_pubs χe (DV) (hwA_DRJ Rt hgen) (hsm_DRJ Rt hgen)
      (hcl_DRJ Rt hgen) h' (orbJ8 (DA) hF) hinj' j]
    exact GenPortJ9AHAWPub.pubsVOf9_perm deltaF powerBasis3 (D := DA) (D' := DV) rfl rfl
      (GenPortJ9AHAWOrd.regroup_eq_nil_iff) (GenPortJ9AHAWOrd.walkRows_regV_perm (DA) hall)
      (orbJ8 (DA) hF) (orbJ8 (DA) hF) hinj hinj' (toχ χe) ▸ rfl

/-! ## 8. The J chip's publics: `jGen_pubs` -/

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (liftQ)

theorem toQ_fqJ (x : ZMod P) : K6.toQ (fq x) = liftQ (K := KC) deltaF x := by
  unfold fq
  rw [toQ_g6, Gold.toZ_ofZ]
  exact IsScalarTower.algebraMap_apply (ZMod P) KC KQ _

theorem coinsJ_eqJ (χe : CoinsE) :
    Nock.Jet.RapJetJ8.coinsJ deltaF (VerJ8.chalsJJ8 (toχ χe)) =
      (⟨ComplJ8Bad.γH deltaF (toχ χe), ComplJ8Bad.ρH deltaF (toχ χe)⟩ : FiniteIO.IOCoins KQ) := by
  first
  | rfl
  | simp [Nock.Jet.RapJetJ8.coinsJ, VerJ8.chalsJJ8, ComplJ8Bad.γH, ComplJ8Bad.ρH, toVSQ, cGamHi, cRhoHi]

theorem coinsJX_eqJ (χe : CoinsE) :
    Nock.Jet.RapJetJ8.coinsJX deltaF (VerJ8.chalsJJ8 (toχ χe)) =
      (⟨ComplJ8Bad.γH deltaF (toχ χe), ComplJ8Bad.ρH deltaF (toχ χe)⟩ : FiniteIO.IOCoins KQ) := by
  first
  | rfl
  | simp [Nock.Jet.RapJetJ8.coinsJX, VerJ8.chalsJJ8, ComplJ8Bad.γH, ComplJ8Bad.ρH, toVSQ, cGamHi, cRhoHi]

theorem toQ_dKeyJ (χe : CoinsE) (m : ℕ) (κ : List (ZMod P)) (cs : FiniteIO.IOCoins KQ)
    (hc : cs = ⟨ComplJ8Bad.γH deltaF (toχ χe), ComplJ8Bad.ρH deltaF (toχ χe)⟩) :
    K6.toQ (dKey χe m κ) =
      (FiniteIO.compress cs (BalanceQ.liftRec (L := KQ) (Nock.Jet.RapJetJ8.keyK (K := KC) m κ)))⁻¹ := by
  have hv : (fun c : Fin m => K6.toQ (fq (κ.getD c 0))) =
      BalanceQ.liftRec (L := KQ) (Nock.Jet.RapJetJ8.keyK (K := KC) m κ) := funext fun c => toQ_fqJ _
  have h := toQ_compressE (γHE χe) (ρHE χe) (fun c : Fin m => fq (κ.getD c 0))
  unfold dKey
  rw [K6.toQ_inv, h, GenPortJ9AChips.toQ_γHE, GenPortJ9AChips.toQ_ρHE, hc]
  show (FiniteIO.compress _ (fun c : Fin m => K6.toQ (fq (κ.getD c 0))))⁻¹ = _
  rw [hv]

theorem toQ_foldrJ (l : List K6) : K6.toQ (l.foldr (· + ·) 0) = (l.map K6.toQ).sum := by
  induction l with
  | nil => simp [K6.toQ_zero]
  | cons a l ih => simp [K6.toQ_add, ih]

theorem toQ_sTEJ (χe : CoinsE) (es : List (Nock.Jet.ChipJ8.Kd × List Nock.Jet.ChipJ8.KE))
    (r : Nock.Jet.ChipJ8.CRow (ZMod P)) :
    K6.toQ (sTE χe es r) = Nock.Jet.ChipJ8T.HonestRAP.sT deltaF (VerJ8.chalsJJ8 (toχ χe)) es r := by
  unfold sTE Nock.Jet.ChipJ8T.HonestRAP.sT
  rw [toQ_foldrJ, List.map_map]
  congr 1
  refine List.map_congr_left fun κ _ => ?_
  exact toQ_dKeyJ χe 8 κ _ (coinsJ_eqJ χe)

theorem toQ_sXEJ (χe : CoinsE) (r : Nock.Jet.ChipJ8.CRow (ZMod P)) :
    K6.toQ (sXE χe r) = Nock.Jet.ChipJ8T.HonestRAP.sX deltaF (VerJ8.chalsJJ8 (toχ χe)) r := by
  unfold sXE Nock.Jet.ChipJ8T.HonestRAP.sX
  rw [toQ_foldrJ, List.map_map]
  congr 1
  refine List.map_congr_left fun κ _ => ?_
  exact toQ_dKeyJ χe 5 κ _ (coinsJX_eqJ χe)

theorem toQ_termEJ (χe : CoinsE) (r : Nock.Jet.ChipJ8.CRow (ZMod P)) :
    K6.toQ (termE χe r) = Nock.Jet.ChipJ8T.HonestRAP.termJ deltaF (VerJ8.chalsJJ8 (toχ χe)) r := by
  unfold termE Nock.Jet.ChipJ8T.HonestRAP.termJ
  simp only [K6.toQ_sub, K6.toQ_add, K6.toQ_mul, toQ_sTEJ, toQ_fqJ]

theorem toQ_lastScanJ (l : List K6) :
    K6.toQ (lastK6 (scanK6 l)) = ∑ j ∈ Finset.range l.length, K6.toQ (l.getD j 0) := by
  rcases Nat.eq_zero_or_pos l.length with h0 | hpos
  · have : l = [] := List.length_eq_zero_iff.mp h0
    subst this
    simp [lastK6, scanK6, K6.toQ_zero]
  · have hlen := GenPortJ9AChips.scanK6_length l
    have hl : lastK6 (scanK6 l) = (scanK6 l).getD (l.length - 1) 0 := by
      unfold lastK6
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hlen]
      simp [List.getD_eq_getElem?_getD]
    rw [hl, GenPortJ9AChips.toQ_scanK6_getD l (l.length - 1) (by omega), Nat.sub_add_cancel hpos]

theorem toQ_lastScanMapJ (rows : List (Nock.Jet.ChipJ8.CRow (ZMod P))) (g : Nock.Jet.ChipJ8.CRow (ZMod P) → K6)
    (g' : Nock.Jet.ChipJ8.CRow (ZMod P) → KQ) (hg : ∀ r, K6.toQ (g r) = g' r) :
    K6.toQ (lastK6 (scanK6 (rows.map g))) = ∑ k : Fin rows.length, g' (rows.get k) := by
  rw [toQ_lastScanJ, List.length_map, ← Fin.sum_univ_eq_sum_range
    (fun j => K6.toQ ((rows.map g).getD j 0)) rows.length]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (rows.map g).getD k 0 = g (rows.get k) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem k.2]
  rw [this, hg]

theorem jGen_snd (rows : List (Nock.Jet.ChipJ8.CRow (ZMod P))) (j : ℕ) :
    (jGen χe rows).2 j =
      if j = 0 then (lastK6 (scanK6 (rows.map (termE χe)))).re
      else if j = 1 then (lastK6 (scanK6 (rows.map (termE χe)))).im
      else if j = 2 then (lastK6 (scanK6 (rows.map (sXE χe)))).re
      else if j = 3 then (lastK6 (scanK6 (rows.map (sXE χe)))).im else 0 := rfl

/-- **`jGen_pubs`**: the J chip's four publics are `pubsJOf` at the honest data. -/
theorem jGen_pubs (i : ℕ) :
    K3.toK ((jGen χe (DA).jrows).2 i) = pubsJOf deltaF (DA) (toχ χe) i := by
  have hT := toQ_lastScanMapJ (DA).jrows (termE χe)
    (Nock.Jet.ChipJ8T.HonestRAP.termJ deltaF (VerJ8.chalsJJ8 (toχ χe))) (toQ_termEJ χe)
  have hX := toQ_lastScanMapJ (DA).jrows (sXE χe)
    (Nock.Jet.ChipJ8T.HonestRAP.sX deltaF (VerJ8.chalsJJ8 (toχ χe))) (toQ_sXEJ χe)
  have hR0 : pubsJOf deltaF (DA) (toχ χe) 0 = Quad.re _ (∑ k : Fin (DA).jrows.length,
      Nock.Jet.ChipJ8T.HonestRAP.termJ deltaF (VerJ8.chalsJJ8 (toχ χe)) ((DA).jrows.get k)) := rfl
  have hR1 : pubsJOf deltaF (DA) (toχ χe) 1 = Quad.im _ (∑ k : Fin (DA).jrows.length,
      Nock.Jet.ChipJ8T.HonestRAP.termJ deltaF (VerJ8.chalsJJ8 (toχ χe)) ((DA).jrows.get k)) := rfl
  have hR2 : pubsJOf deltaF (DA) (toχ χe) 2 = Quad.re _ (∑ k : Fin (DA).jrows.length,
      Nock.Jet.ChipJ8T.HonestRAP.sX deltaF (VerJ8.chalsJJ8 (toχ χe)) ((DA).jrows.get k)) := rfl
  have hR3 : pubsJOf deltaF (DA) (toχ χe) 3 = Quad.im _ (∑ k : Fin (DA).jrows.length,
      Nock.Jet.ChipJ8T.HonestRAP.sX deltaF (VerJ8.chalsJJ8 (toχ χe)) ((DA).jrows.get k)) := rfl
  have L0 : (jGen χe (DA).jrows).2 0 = (lastK6 (scanK6 ((DA).jrows.map (termE χe)))).re := rfl
  have L1 : (jGen χe (DA).jrows).2 1 = (lastK6 (scanK6 ((DA).jrows.map (termE χe)))).im := rfl
  have L2 : (jGen χe (DA).jrows).2 2 = (lastK6 (scanK6 ((DA).jrows.map (sXE χe)))).re := rfl
  have L3 : (jGen χe (DA).jrows).2 3 = (lastK6 (scanK6 ((DA).jrows.map (sXE χe)))).im := rfl
  by_cases h0 : i = 0
  · subst h0
    rw [L0, hR0, ← hT, re_toQ]
  by_cases h1 : i = 1
  · subst h1
    rw [L1, hR1, ← hT, im_toQ]
  by_cases h2 : i = 2
  · subst h2
    rw [L2, hR2, ← hX, re_toQ]
  by_cases h3 : i = 3
  · subst h3
    rw [L3, hR3, ← hX, im_toQ]
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 4 := ⟨i - 4, by omega⟩
  have hR4 : pubsJOf deltaF (DA) (toχ χe) (i' + 4) = 0 := by
    simp [pubsJOf]
  have hL4 : (jGen χe (DA).jrows).2 (i' + 4) = 0 := by
    simp [jGen_snd]
  rw [hL4, hR4]
  exact K3.toK_zero

theorem msg_pubsJ : (IJ).toMsg.pubsJ = ((BR).M (toχ χe)).pubsJ := by
  funext i
  exact jGen_pubs Rt hgen χe i

/-! ## 9. Validity and orbit admissibility -/

theorem orbOK_J (n : ℕ) (hs : n ≤ 2 ^ 31) (g : ℕ → Fin n → ZMod P) :
    OrbOK (⟨hOf n, n, ωOf (hOf n), g⟩ : ChipIn) := by
  obtain ⟨h1, -, h32⟩ := GenPortJ9AHOrb.hOf_spec n hs
  rw [← orbB_iff]
  unfold orbB
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true h1, GenPortJ9AHOrb.ordOK_ωOf _ h1 h32⟩

theorem orb_of_size {q : ChipIn} (tbl : Array (Array (ZMod P))) (h : q = chipOf tbl) (hs : q.n ≤ 2 ^ 31) :
    OrbOK q := by
  subst h
  exact GenPortJ9AHOrb.orbOK_chipOf tbl hs

theorem fits_of_size {q : ChipIn} (tbl : Array (Array (ZMod P))) (h : q = chipOf tbl) (hs : q.n ≤ 2 ^ 31) :
    q.n ≤ 3 * 2 ^ q.h := by
  subst h
  exact GenPortJ9AHOrb.chipOf_n_le tbl hs

include hpG h31A in
theorem sizes31J (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads) :
    (IJ).X.n ≤ 2 ^ 31 ∧ (IJ).C.n ≤ 2 ^ 31 ∧ (IJ).W.n ≤ 2 ^ 31 ∧ (IJ).J.n ≤ 2 ^ 31 ∧ (IJ).A.n ≤ 2 ^ 31 ∧
      (IJ).V.n ≤ 2 ^ 31 ∧ (IJ).AX.n ≤ 2 ^ 31 ∧ (IJ).SP.n ≤ 2 ^ 31 := by
  have hW : (walkRows (DA).cells (DA).reads).length ∈ sizesA (DA) :=
    List.mem_append_left _ (by simp [ComplJ8Of.sizesJ8])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (size_X Rt hgen hpG h31A χe).le.trans (h31A _ (ComplJ9AOfStatic.mem_N9 Rt hgen))
  · exact (size_C Rt hgen hpG h31A χe).le.trans (h31A _ (ComplJ9AOfStatic.mem_cells Rt hgen))
  · exact (size_W Rt hgen hpG h31A χe hwalk9).le.trans (h31A _ hW)
  · exact (size_J Rt hgen hpG h31A χe).le.trans (h31A _ (ComplJ9AOfStatic.mem_jrows Rt hgen))
  · exact (size_A Rt hgen hpG h31A χe).le.trans (h31A _ (ComplJ9AOfStatic.mem_acs Rt hgen))
  · exact (size_V Rt hgen hpG h31A χe hax9 hwalkA).le.trans (h31A _ (ComplJ9AOfStatic.mem_nV Rt hgen))
  · exact (size_AX Rt hgen hpG h31A χe).le.trans (h31A _ (ComplJ9AOfStatic.mem_nX Rt hgen))
  · exact (size_SP Rt hgen hpG h31A χe).le.trans (h31A _ (ComplJ9AOfStatic.mem_nS Rt hgen))

include hpG h31A in
theorem validJ9A_recJ9AXJ (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads) :
    ValidJ9A (IJ) := by
  obtain ⟨sX, sC, sW, sJ, sA, sV, sAX, sSP⟩ := sizes31J Rt hgen hpG h31A χe hwalk9 hax9 hwalkA
  refine ValidJ9A.mk' (IJ) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩
  · rw [size_X Rt hgen hpG h31A χe]; exact (BR).Pb.hn
  · rw [size_C Rt hgen hpG h31A χe]; exact (BR).Pb.hnC
  · rw [size_W Rt hgen hpG h31A χe hwalk9]; exact (BR).Pb.hnW
  · rw [size_A Rt hgen hpG h31A χe]; exact (BR).Pb.hnA
  · rw [size_V Rt hgen hpG h31A χe hax9 hwalkA]; exact (BR).Pb.hnV
  · exact orb_of_size _ rfl sX
  · exact orb_of_size _ rfl sC
  · exact orb_of_size _ rfl sW
  · exact orbOK_J (layK Rt s f χe (RnOf t r)).length sJ _
  · exact orb_of_size _ rfl sA
  · exact orb_of_size _ rfl sV
  · rw [size_AX Rt hgen hpG h31A χe]; exact (BR).Pb.hnX
  · exact orb_of_size _ rfl sAX
  · rw [size_SP Rt hgen hpG h31A χe]; exact (BR).Pb.hnS
  · exact orb_of_size _ rfl sSP

include hpG h31A in
theorem orbAdm_recJ9AXJ (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads) :
    OrbAdm (IJ) (orbOf (IJ)) := by
  obtain ⟨sX, sC, sW, sJ, sA, sV, sAX, sSP⟩ := sizes31J Rt hgen hpG h31A χe hwalk9 hax9 hwalkA
  exact orbAdm_self (validJ9A_recJ9AXJ Rt hgen hpG h31A χe hwalk9 hax9 hwalkA)
    (fits_of_size _ rfl sX) (fits_of_size _ rfl sC) (fits_of_size _ rfl sW)
    (GenPortJ9AHOrb.hOf_spec (layK Rt s f χe (RnOf t r)).length sJ).2.1
    (fits_of_size _ rfl sA) (fits_of_size _ rfl sV) (fits_of_size _ rfl sAX) (fits_of_size _ rfl sSP)

end Run

/-! ## 10. The non-chip transport at jets (`nonChip_transport` hard-codes `regs = []`) -/

section NonChipTwin

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB)
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.Jet.PinJ8 (pinCons)
open Nock.Atoms (lenL)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHNonChip (NonChipJ9A)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **Transport of the non-chip conjuncts at jets**: `(Pb, M)` from `(Pb', M')` when the sizes and the message
fields agree and the registry fields (`regs ids idx rk Rt`, and the layout list) agree. -/
theorem nonChip_transportJ {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {Pb Pb' : PubJ9A p} {M M' : MsgJ9A' p K δ} (H : NonChipJ9A δ b Pb' Rg c χ M')
    (hn : Pb.n = Pb'.n) (hnC : Pb.nC = Pb'.nC) (hnW : Pb.nW = Pb'.nW) (hkr : Pb.kroots = Pb'.kroots)
    (hnA : Pb.nA = Pb'.nA) (hnV : Pb.nV = Pb'.nV) (hnX : Pb.nX = Pb'.nX) (hnS : Pb.nS = Pb'.nS)
    (hreg : Pb.regs = Pb'.regs) (hids : Pb.ids = Pb'.ids) (hidxE : Pb.idx = Pb'.idx)
    (hrkE : Pb.rk = Pb'.rk) (hRtE : Pb.Rt = Pb'.Rt) (hlayE : List.ofFn Pb.lay = List.ofFn Pb'.lay)
    (hm : M.m = M'.m) (hρ : M.ρ = M'.ρ) (hρS : M.ρS = M'.ρS) (hC : M.pubsC = M'.pubsC) (hW : M.pubsW = M'.pubsW)
    (hJ : M.pubsJ = M'.pubsJ) (hA : M.pubsA = M'.pubsA) (hV : M.pubsV = M'.pubsV) (hX : M.pubsX = M'.pubsX)
    (hS : M.pubsS = M'.pubsS) : NonChipJ9A δ b Pb Rg c χ M := by
  have hpr : pinRecsJ8 δ Pb.toPubJ8 χ = pinRecsJ8 δ Pb'.toPubJ8 χ := by
    unfold pinRecsJ8; rw [hreg, hidxE, hrkE, hRtE]
  have hcen : censusGJ9 Pb.toPubJ8 c = censusGJ9 Pb'.toPubJ8 c := by
    unfold censusGJ9 censusG; rw [hreg, hRtE]
  exact
    { hnpC := by rw [hnC]; exact H.hnpC
      hkW := by rw [hkr]; exact H.hkW
      hknW := by rw [hkr, hnW]; exact H.hknW
      hkpW := by rw [hkr, hnW]; exact H.hkpW
      hnpA := by rw [hnA]; exact H.hnpA
      hGx := by rw [hρ, hW, hJ, hC]; exact H.hGx
      hGp := by rw [hρ, hX, hW]; exact H.hGp
      hGS := by rw [hreg, hidxE, hρS, hJ, hX, hA, hV, hS]; exact H.hGS
      hlay := by rw [hlayE, hRtE, hreg, hids]; exact H.hlay
      hsmall := by rw [hRtE, hreg, hids]; exact H.hsmall
      huniq := by rw [hRtE, hreg, hids]; exact H.huniq
      hTpl := by rw [hreg, hRtE]; exact H.hTpl
      hnd := by rw [hreg]; exact H.hnd
      hidx := by rw [hreg, hidxE]; exact H.hidx
      hrk := by rw [hreg, hrkE]; exact H.hrk
      hlt := by rw [hreg, hrkE, hidxE]; exact H.hlt
      hsumC' := by rw [hpr, hm, hC, hA]; exact H.hsumC'
      hbalA' := by rw [hA, hV]; exact H.hbalA'
      hvalA0 := by rw [hA]; exact H.hvalA0
      hfxC := by rw [hC, hW]; exact H.hfxC
      hfxA := by rw [hA, hV]; exact H.hfxA
      hclI := by rw [hm]; exact H.hclI
      hclR := H.hclR
      hcen' := by rw [hcen, hnA]; exact H.hcen'
      hlenC := by rw [hreg, hnC]; exact H.hlenC
      hlenA := by rw [hnA, hnV]; exact H.hlenA
      hcellF := H.hcellF
      hnAS := by rw [hnA, hnS]; exact H.hnAS
      hlenX := by rw [hnX, hn, hnS]; exact H.hlenX }

end NonChipTwin

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsgJ

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsgJ
#print axioms Pb_n
#print axioms Pb_nC
#print axioms Pb_nW
#print axioms Pb_kroots
#print axioms Pb_nA
#print axioms Pb_nV
#print axioms Pb_krootsV
#print axioms Pb_nX
#print axioms Pb_nS
#print axioms Pb_nJ
#print axioms regs_B'
#print axioms g_B'
#print axioms hcs_DAJ
#print axioms hcl_DAJ
#print axioms size_X
#print axioms cRPK_eqJ
#print axioms size_C
#print axioms xRPK_eqJ
#print axioms size_AX
#print axioms sRPK_of_spOn
#print axioms sRPK_of_not_spOn
#print axioms size_SP
#print axioms jrows_len_layK
#print axioms size_J
#print axioms msg_m
#print axioms msg_ρ
#print axioms msg_ρS
#print axioms msg_pubsC
#print axioms msg_pubsX
#print axioms getD_map_ltJ
#print axioms msg_pubsS
#print axioms hall_DAJ
#print axioms hwalk_DAJ
#print axioms hp_DRJ
#print axioms hwcell_DAJ
#print axioms hwcell_DRJ
#print axioms hwroot_DRJ
#print axioms wsKr_eqJ
#print axioms wRPK_eqJ
#print axioms size_W
#print axioms size_kroots
#print axioms powN_inj_DRJ
#print axioms pubs_DR_DAJ
#print axioms msg_pubsW
#print axioms ptK_eqJ
#print axioms readsK_eqJ
#print axioms vsKrVK_eqJ
#print axioms aRPK_eqJ
#print axioms size_A
#print axioms hN_runJ
#print axioms msg_pubsA
#print axioms HAK_eqJ
#print axioms rIAK_eqJ
#print axioms vsKrVK_neJ
#print axioms krV_zero_iffJ
#print axioms hallV_DAJ
#print axioms hwA_DAJ
#print axioms hwalkV_DAJ
#print axioms hwA_DRJ
#print axioms hcl_DRJ
#print axioms hsm_DRJ
#print axioms vs_krV_presentJ
#print axioms vRPK_eq_awEJ
#print axioms vRPK_absent
#print axioms size_V
#print axioms size_krootsV
#print axioms msg_pubsV
#print axioms toQ_fqJ
#print axioms coinsJ_eqJ
#print axioms coinsJX_eqJ
#print axioms toQ_dKeyJ
#print axioms toQ_foldrJ
#print axioms toQ_sTEJ
#print axioms toQ_sXEJ
#print axioms toQ_termEJ
#print axioms toQ_lastScanJ
#print axioms toQ_lastScanMapJ
#print axioms jGen_snd
#print axioms jGen_pubs
#print axioms msg_pubsJ
#print axioms orbOK_J
#print axioms orb_of_size
#print axioms fits_of_size
#print axioms sizes31J
#print axioms validJ9A_recJ9AXJ
#print axioms orbAdm_recJ9AXJ
#print axioms nonChip_transportJ
end Axioms
