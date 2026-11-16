/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHMsg.lean

  Context: `hgen hnc hpG h31A χe`, `I := recJ9AX s f χe t r`,
  `B := BRun9A deltaF powerBasis3 Rt hgen hpG h31A`.

  * field-level `rfl` lemmas for `B.Pb` (`Pb_n … Pb_nS`), `regs_B ids_B nJ_B`;
  * sizes `size_X size_C size_W size_kroots size_A size_V size_krootsV size_AX size_SP`;
  * messages `msg_m msg_ρ msg_ρS msg_pubsC msg_pubsW msg_pubsJ msg_pubsA msg_pubsV msg_pubsX msg_pubsS`;
  * `sizes31`, `validJ9A_recJ9AX`, `orbAdm_recJ9AX`.

  Extra binders: `hwalk9`, `hax9`, `hwalkA` (those of the walk and atom-walk interpolant lemmas) on every lemma
  that uses the walk / atom-walk run lemmas.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCoin
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAx
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHSp
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ARun
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfStatic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsg

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
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj
  (RnOf HJ csJ acsLJ rows9J xRPJ sRPJ spOnJ recX_X recX_C recX_W recX_A recX_V recX_AX recX_SP recX_J_n
   recX_pubsX recX_pubsS recX_M_m sRPJ_of_spOn sRPJ_of_not_spOn)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (OrbAdm orbOf orbAdm_self)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb (chipOf_n_le validJ9A_of_chips)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp (recJ9AX_X_n recJ9AX_hdp)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCoin (hchi_toχ mOf_eq_mCOf)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot (compGenX9_rho compGenX9_rhoS)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAx (pubsXA_eq axn_eq)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHSp (spGenE_size)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips (pubsSE_eq)
open Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff Nock.V1J9A.GenJ9AX Nock.V1J9A.GenCompX9

section Run
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hnc : callsOf (ComplJ8Data.rowsOfT t) = [])
  (hpG : P = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf P Rg Rt hgen)) (χe : CoinsE)
include hnc

local notation "DA" => j9aDataOf P Rg Rt hgen
local notation "BR" => BRun9A deltaF powerBasis3 Rt hgen hpG h31A
local notation "II" => recJ9AX s f χe t r

/-! ## 1. Field-level `rfl` lemmas for `B.Pb` -/

theorem Pb_n : (BR).Pb.n = N9 t := rfl
theorem Pb_nC : (BR).Pb.nC = (DA).cells.length := rfl
theorem Pb_nW : (BR).Pb.nW = (walkRows (DA).cells (DA).reads).length := rfl
theorem Pb_kroots : (BR).Pb.kroots = krW (DA).cells (DA).reads := rfl
theorem Pb_nA : (BR).Pb.nA = (DA).acs.length := rfl
theorem Pb_nV : (BR).Pb.nV = ComplJ8Of.nVOf (DA) := rfl
theorem Pb_krootsV : (BR).Pb.krootsV = ComplJ8Of.krVOf (DA) := rfl
theorem Pb_nX : (BR).Pb.nX = nXA (p := P) Rt hgen := rfl
theorem Pb_nS : (BR).Pb.nS = nSOf P t := rfl
theorem Pb_regs : (BR).Pb.regs = (DA).regs := rfl
theorem Pb_ids : (BR).Pb.ids = (DA).ids := rfl
theorem Pb_nJ : (BR).Pb.nJ = (DA).jrows.length := rfl

/-- The honest data has no registry, no ids, no jet rows (`hnc`). -/
theorem regs_DA : (DA).regs = [] := by
  show ((callsOf (ComplJ8Data.rowsOfT t)).map Prod.fst).dedup = []
  simp [hnc]

theorem ids_DA : (DA).ids = [] := by
  show (callsOf (ComplJ8Data.rowsOfT t)).map Prod.fst = []
  simp [hnc]

theorem jrows_DA : (DA).jrows = [] := by
  have hjr : (ComplJ8Data.j8DataOf P Rg Rt hgen).jrows = [] := by
    show ComplJ8Data.mvFixP _ (Nock.Jet.ChipJ8.honestJ8G _ _ (List.map Prod.fst (Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t))).dedup
      (Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t))) _ = []
    rw [hnc]; rfl
  exact hjr

theorem regs_B : (BR).Pb.regs = [] := (Pb_regs Rt hgen hnc hpG h31A).trans (regs_DA Rt hgen hnc)
theorem ids_B : (BR).Pb.ids = [] := (Pb_ids Rt hgen hnc hpG h31A).trans (ids_DA Rt hgen hnc)
theorem nJ_B : (BR).Pb.nJ = 0 := by
  rw [Pb_nJ Rt hgen hnc hpG h31A, jrows_DA Rt hgen hnc]; rfl

/-! ## 2. Data equalities (re-proved without the walk binders) -/

theorem HJ_eq : HJ s f χe (RnOf t r) = (DA).H := by
  show hdlB (csJ s f χe (RnOf t r)) (acsLJ s f χe (RnOf t r)) = _
  rw [GenPortJ9AHCellRun.cs_eq Rt hgen hnc χe, GenPortJ9AHCellRun.acs_eq Rt hgen hnc χe,
    GenPortJ9A.hdlB_eq_hdlP]
  rfl

theorem xRPJ_eq : xRPJ s f χe (RnOf t r) =
    GenAxE.axGenOf χe (DA).acs.length (DA).H (rowsOfT9 t) (axOnA t) := by
  show GenAxE.axGenOf χe (acsLJ s f χe (RnOf t r)).length (HJ s f χe (RnOf t r)) (rowsOfT9 t) (axOnA t) = _
  rw [HJ_eq Rt hgen hnc χe, GenPortJ9AHCellRun.acs_eq Rt hgen hnc χe]

/-! ## 3. Sizes -/

theorem size_X : (II).X.n = (BR).Pb.n :=
  (recJ9AX_X_n s f χe t r).trans (Pb_n Rt hgen hnc hpG h31A).symm

theorem size_C : (II).C.n = (BR).Pb.nC :=
  (GenPortJ9AHCellRun.genJ9AX_cell_n Rt hgen hnc χe).trans (Pb_nC Rt hgen hnc hpG h31A).symm

theorem size_W (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t)) :
    (II).W.n = (BR).Pb.nW :=
  (GenPortJ9AHWalkRun.genJ9AX_walk_n Rt hgen hnc hwalk9 χe).trans (Pb_nW Rt hgen hnc hpG h31A).symm

theorem size_kroots (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t)) :
    (II).kroots = (BR).Pb.kroots :=
  (GenPortJ9AHWalkRun.genJ9AX_walk_kroots Rt hgen hnc hwalk9 χe).trans (Pb_kroots Rt hgen hnc hpG h31A).symm

theorem size_A : (II).A.n = (BR).Pb.nA :=
  (GenPortJ9AHAtomRun.genJ9AX_atom_n Rt hgen hnc χe).trans (Pb_nA Rt hgen hnc hpG h31A).symm

theorem size_V (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads) :
    (II).V.n = (BR).Pb.nV :=
  (GenPortJ9AHAWRun.genJ9AX_aw_n Rt hgen hnc hax9 hwalkA χe).trans (Pb_nV Rt hgen hnc hpG h31A).symm

theorem size_krootsV (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads) :
    (II).krootsV = (BR).Pb.krootsV :=
  (GenPortJ9AHAWRun.genJ9AX_aw_krootsV Rt hgen hnc hax9 hwalkA χe).trans
    (Pb_krootsV Rt hgen hnc hpG h31A).symm

theorem size_AX : (II).AX.n = (BR).Pb.nX := by
  rw [recX_AX, xRPJ_eq Rt hgen hnc χe]
  exact (axn_eq Rt hgen χe).trans (Pb_nX Rt hgen hnc hpG h31A).symm

theorem size_SP : (II).SP.n = (BR).Pb.nS := by
  rw [Pb_nS Rt hgen hnc hpG h31A]
  by_cases h : spOnA P t = true
  · rw [recX_SP, sRPJ_of_spOn s f χe (RnOf t r) h]
    refine (spGenE_size χe _ _ _).trans ?_
    exact (nSOf_eq h).symm
  · have h' : spOnJ s f χe (RnOf t r) = false := Bool.eq_false_iff.mpr h
    rw [recX_SP, sRPJ_of_not_spOn s f χe (RnOf t r) h']
    have h1 : nSOf P t = 1 := by unfold nSOf; rw [if_neg h]
    rw [h1]
    rfl

/-! ## 4. Messages -/

theorem msg_m : (II).toMsg.m = ((BR).M (toχ χe)).m :=
  (recX_M_m s f χe t r).trans
    ((congrArg (mOf (GenPortJ9AHProj.cJ s f χe (RnOf t r))) (HJ_eq Rt hgen hnc χe)).trans
      (mOf_eq_mCOf _ _))

omit hnc in
/-- The compute message's `ρ, ρS` of the record, in the shape of `recJ9AX_hdp`'s let-terms. -/
theorem recX_ρ_let (s f : Noun) (χe : CoinsE) (t : NTree SkelX) (r : Noun) :
    let c : P8PublicClaim := ⟨s, f, r⟩
    let acsL := GenPortJ9.acsRun s f r t
    let cs := cellsOfRoots (rootsOf c (ComplJ8Data.rowsOfT t))
    let H := hdlB cs acsL
    let pt := ptrE acsL (stopEdges (ComplJ8Data.rowsOfT t))
    let pd := HonestPairX.pdX (sxE pt)
    let fx := fieldAx9 P (rowsOfT9 t)
    let idOf := idOf9 P acsL.length H fx
    (recJ9AX s f χe t r).M.ρ = (compGenX9 c H pd idOf (W9 t) χe).ρ ∧
      (recJ9AX s f χe t r).M.ρS = (compGenX9 c H pd idOf (W9 t) χe).ρS := by
  intros
  exact ⟨rfl, rfl⟩

omit hnc in
theorem rho_aux (c : P8PublicClaim) (DH H : Noun → ℕ × ℕ) (Dpd pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
    (idA idOf : ℕ → ℕ) (W : List (NTree LX9)) (χe : CoinsE) (hH : H = DH) (hpd : pd = Dpd) (hid : idOf = idA)
    (ρ' : Fin 5 → K6) (ρS' : K6) (hI : ρ' = (compGenX9 c H pd idOf W χe).ρ ∧ ρS' = (compGenX9 c H pd idOf W χe).ρS) :
    ρ' = (compGenX9 c DH Dpd idA W χe).ρ ∧ ρS' = (compGenX9 c DH Dpd idA W χe).ρS := by
  subst hH hpd hid
  exact hI

theorem msg_ρ : (II).toMsg.ρ = ((BR).M (toχ χe)).ρ := by
  funext i
  obtain ⟨hH, hpd, hid⟩ := recJ9AX_hdp Rt hgen hnc
  have e := (rho_aux ⟨s, f, r⟩ (DA).H _ (DA).pd _ (idOfA (p := P) Rt hgen) _ (W9 t) χe hH hpd hid _ _
    (recX_ρ_let s f χe t r)).1
  show K6.toQ ((II).M.ρ i) = ρA deltaF powerBasis3 Rt hgen (toχ χe) i
  rw [e]
  exact compGenX9_rho Rt hgen (toχ χe) χe (hchi_toχ χe) _ i

theorem msg_ρS : (II).toMsg.ρS = ((BR).M (toχ χe)).ρS := by
  obtain ⟨hH, hpd, hid⟩ := recJ9AX_hdp Rt hgen hnc
  have e := (rho_aux ⟨s, f, r⟩ (DA).H _ (DA).pd _ (idOfA (p := P) Rt hgen) _ (W9 t) χe hH hpd hid _ _
    (recX_ρ_let s f χe t r)).2
  show K6.toQ ((II).M.ρS) = ρSA deltaF powerBasis3 Rt hgen (toχ χe)
  rw [e]
  exact compGenX9_rhoS Rt hgen (toχ χe) χe (hchi_toχ χe) _

theorem msg_pubsC : (II).toMsg.pubsC = ((BR).M (toχ χe)).pubsC := by
  funext j
  show K3.toK ((II).M.pubsC j) =
    pubsCOf deltaF powerBasis3 (DA) (cellsA_pos Rt hgen) (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) (toχ χe) j
  exact GenPortJ9AHCellRun.genJ9AX_cell_pubs Rt hgen hnc χe (hF_run Rt hgen hpG h31A) j

theorem Mw_eq :
    ((BR).M (toχ χe)).pubsW =
      pubsWOf deltaF powerBasis3 (DA) (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) (toχ χe) := rfl

theorem Wl_pubs (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t)) (j : ℕ) :
    K3.toK ((II).M.pubsW j) =
      pubsWOf deltaF powerBasis3 (DA) (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) (toχ χe) j :=
  by
    have h := GenPortJ9AHWalkRun.genJ9AX_walk_pubs Rt hgen hnc hwalk9 χe (hF_run Rt hgen hpG h31A) j
    convert h using 4
    all_goals exact Subsingleton.elim _ _

theorem msg_pubsW (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t)) :
    (II).toMsg.pubsW = ((BR).M (toχ χe)).pubsW :=
  funext fun j => (Wl_pubs Rt hgen hnc hpG h31A χe hwalk9 j).trans
    (congrFun (Mw_eq Rt hgen hnc hpG h31A χe) j).symm

omit hnc in
theorem pubsJOf_zero (D : ComplJ8Data.J8Data P Rg fuel s f r) (χ : Nock.NockVMROM.Thm54.SVFrame.Coins
    Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC) (h0 : D.jrows.length = 0) (i : ℕ) :
    pubsJOf deltaF D χ i = 0 := by
  have hs : ∀ (g : Fin D.jrows.length → Quad (algebraMap (ZMod P) KC deltaF)), ∑ k, g k = 0 := by
    intro g; exact Finset.sum_eq_zero fun k _ => absurd k.isLt (by omega)
  have hz : Quad.re _ (0 : Quad (algebraMap (ZMod P) KC deltaF)) = 0 ∧
      Quad.im _ (0 : Quad (algebraMap (ZMod P) KC deltaF)) = 0 :=
    (Quad.mk_eq_zero_iff _ _ _).mp (Quad.mk_re_im _ 0)
  have hp2 : ∀ i, ComplJ8Of.pub2 deltaF (0 : Quad (algebraMap (ZMod P) KC deltaF)) i = 0 := by
    intro i
    unfold ComplJ8Of.pub2
    split_ifs
    · exact hz.1
    · exact hz.2
  unfold pubsJOf
  rw [hs, hs]
  split_ifs
  · exact hp2 i
  · exact hp2 i
  · rfl

theorem msg_pubsJ : (II).toMsg.pubsJ = ((BR).M (toχ χe)).pubsJ := by
  funext i
  rw [GenPortJ9AHJ.recJ9AX_toMsg_pubsJ]
  show (0 : KC) = pubsJOf deltaF (DA) (toχ χe) i
  exact (pubsJOf_zero (DA) (toχ χe) (by rw [jrows_DA Rt hgen hnc]; rfl) i).symm

theorem hN_run (h31A : Rows31A (j9aDataOf P Rg Rt hgen)) :
    (ComplJ8Data.j8DataOf P Rg Rt hgen).rows.size ≤ 2 ^ 31 := by
  have h : (bfsForest [t]).length ≤ 2 ^ 31 := h31A _ (ComplJ9AOfStatic.mem_bfs Rt hgen)
  have e : (ComplJ8Data.rowsOfT t).size = (bfsForest [t]).length := by simp [ComplJ8Data.rowsOfT]
  show (ComplJ8Data.rowsOfT t).size ≤ 2 ^ 31
  rw [e]
  exact h

theorem msg_pubsA : (II).toMsg.pubsA = ((BR).M (toχ χe)).pubsA := by
  funext j
  have hF := hF_run Rt hgen hpG h31A
  have hmem : (DA).acs.length ∈ ComplJ8Of.sizesJ8 (DA) := by simp [ComplJ8Of.sizesJ8]
  have hinj : Function.Injective (ComplJ8Of.powN (orbJ8 (DA) hF) (DA).acs.length) :=
    (ComplJ8Of.powN_ok _ (ComplJ8Of.le_two_pow_ht _ hmem)).1
  show K3.toK ((II).M.pubsA j) = pubsAOf deltaF powerBasis3 (DA) (acsA_pos Rt hgen) (orbJ8 (DA) hF) (toχ χe) j
  exact GenPortJ9AHAtomRun.genJ9AX_atom_pubs Rt hgen hnc χe (hN_run Rt hgen hnc h31A) (acsA_pos Rt hgen)
    (orbJ8 (DA) hF) hinj j

theorem msg_pubsV (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads) :
    (II).toMsg.pubsV = ((BR).M (toχ χe)).pubsV := by
  funext j
  have hF := hF_run Rt hgen hpG h31A
  show K3.toK ((II).M.pubsV j) =
    (ComplJ9BBalF.avOf9 deltaF powerBasis3 (DA) hF
      (ComplJ8Of.avOf deltaF powerBasis3 (DA) hF (acsA_pos Rt hgen))).pubsV (toχ χe) j
  exact GenPortJ9AHAWRun.genJ9AX_aw_pubs_avOf9 Rt hgen hnc hax9 hwalkA χe hF _ j

theorem msg_pubsX : (II).toMsg.pubsX = ((BR).M (toχ χe)).pubsX := by
  funext j
  show K3.toK ((II).pubsX j) = pubsXA deltaF Rt hgen (toχ χe) j
  rw [pubsXA_eq Rt hgen χe j, recX_pubsX, xRPJ_eq Rt hgen hnc χe]

omit hnc in
theorem getD_map_lt (g : ℕ → ℕ) (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    (l.map g).getD i 0 = g (l.getD i 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem msg_pubsS : (II).toMsg.pubsS = ((BR).M (toχ χe)).pubsS := by
  funext j
  show K3.toK ((II).pubsS j) = pubsSA deltaF Rt hgen (toχ χe) j
  unfold pubsSA
  by_cases h : spOnA P t = true
  · rw [if_pos h, recX_pubsS, sRPJ_of_spOn s f χe (RnOf t r) h, GenPortJ9AHCellRun.acs_eq Rt hgen hnc χe]
    have hn : nSOf P t = (GenSpE.vSE (rows9J s f χe (RnOf t r))).length := nSOf_eq h
    have key := pubsSE_eq χe (DA).acs.length (GenSpE.vSE (rows9J s f χe (RnOf t r)))
      (GenSpE.mSE (rows9J s f χe (RnOf t r)) (GenSpE.vSE (rows9J s f χe (RnOf t r)))) hn (nSOf_pos P t) j
    have hm : (fun i : Fin (nSOf P t) =>
        (GenSpE.mSE (rows9J s f χe (RnOf t r)) (GenSpE.vSE (rows9J s f χe (RnOf t r)))).getD i 0) =
        mSA (p := P) (t := t) := by
      funext i
      have hi : (i : ℕ) < (GenSpE.vSE (rows9J s f χe (RnOf t r))).length := hn ▸ i.2
      show (List.map _ (GenSpE.vSE (rows9J s f χe (RnOf t r)))).getD i 0 = _
      rw [getD_map_lt _ _ _ hi]
      rfl
    rw [hm] at key
    exact key
  · rw [if_neg h]
    have h' : spOnJ s f χe (RnOf t r) = false := Bool.eq_false_iff.mpr h
    rw [recX_pubsS, sRPJ_of_not_spOn s f χe (RnOf t r) h']
    exact K3.toK_zero

/-! ## 5. Orbit-side facts -/

include hpG h31A

theorem sizes31 (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads) :
    (II).X.n ≤ 2 ^ 31 ∧ (II).C.n ≤ 2 ^ 31 ∧ (II).W.n ≤ 2 ^ 31 ∧ (II).A.n ≤ 2 ^ 31 ∧
      (II).V.n ≤ 2 ^ 31 ∧ (II).AX.n ≤ 2 ^ 31 ∧ (II).SP.n ≤ 2 ^ 31 := by
  have hW : (walkRows (DA).cells (DA).reads).length ∈ sizesA (DA) :=
    List.mem_append_left _ (by simp [ComplJ8Of.sizesJ8])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (size_X Rt hgen hnc hpG h31A χe).le.trans (h31A _ (ComplJ9AOfStatic.mem_N9 Rt hgen))
  · exact (size_C Rt hgen hnc hpG h31A χe).le.trans (h31A _ (ComplJ9AOfStatic.mem_cells Rt hgen))
  · exact (size_W Rt hgen hnc hpG h31A χe hwalk9).le.trans (h31A _ hW)
  · exact (size_A Rt hgen hnc hpG h31A χe).le.trans (h31A _ (ComplJ9AOfStatic.mem_acs Rt hgen))
  · exact (size_V Rt hgen hnc hpG h31A χe hax9 hwalkA).le.trans (h31A _ (ComplJ9AOfStatic.mem_nV Rt hgen))
  · exact (size_AX Rt hgen hnc hpG h31A χe).le.trans (h31A _ (ComplJ9AOfStatic.mem_nX Rt hgen))
  · exact (size_SP Rt hgen hnc hpG h31A χe).le.trans (h31A _ (ComplJ9AOfStatic.mem_nS Rt hgen))

omit hnc hpG h31A in
theorem pos_tbl (q : ChipIn) (tbl : Array (Array (ZMod P))) (h : q = chipOf tbl) (hp : 0 < q.n) :
    0 < tbl.size := by
  subst h; exact hp

omit hnc hpG h31A in
theorem le_tbl (q : ChipIn) (tbl : Array (Array (ZMod P))) (h : q = chipOf tbl) (hp : q.n ≤ 2 ^ 31) :
    tbl.size ≤ 2 ^ 31 := by
  subst h; exact hp

omit hnc hpG h31A in
theorem fits_tbl (q : ChipIn) (tbl : Array (Array (ZMod P))) (h : q = chipOf tbl) (hs : tbl.size ≤ 2 ^ 31) :
    q.n ≤ 3 * 2 ^ q.h := by
  subst h; exact chipOf_n_le tbl hs

theorem validJ9A_recJ9AX (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads) :
    ValidJ9A (II) := by
  obtain ⟨sX, sC, sW, sA, sV, sAX, sSP⟩ := sizes31 Rt hgen hnc hpG h31A χe hwalk9 hax9 hwalkA
  have hX := recX_X s f χe t r
  have hC := recX_C s f χe t r
  have hW := recX_W s f χe t r
  have hA := recX_A s f χe t r
  have hV := recX_V s f χe t r
  have hAX := recX_AX s f χe t r
  have hSP := recX_SP s f χe t r
  refine validJ9A_of_chips (II) _ _ _ _ _ _ _ hX hC hW hA hV hAX hSP rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (le_tbl _ _ hX sX) (le_tbl _ _ hC sC) (le_tbl _ _ hW sW) (le_tbl _ _ hA sA) (le_tbl _ _ hV sV)
    (le_tbl _ _ hAX sAX) (le_tbl _ _ hSP sSP)
  · refine pos_tbl _ _ hX ?_
    rw [size_X Rt hgen hnc hpG h31A χe]; exact (BR).Pb.hn
  · refine pos_tbl _ _ hC ?_
    rw [size_C Rt hgen hnc hpG h31A χe]; exact (BR).Pb.hnC
  · refine pos_tbl _ _ hW ?_
    rw [size_W Rt hgen hnc hpG h31A χe hwalk9]; exact (BR).Pb.hnW
  · refine pos_tbl _ _ hA ?_
    rw [size_A Rt hgen hnc hpG h31A χe]; exact (BR).Pb.hnA
  · refine pos_tbl _ _ hV ?_
    rw [size_V Rt hgen hnc hpG h31A χe hax9 hwalkA]; exact (BR).Pb.hnV
  · refine pos_tbl _ _ hAX ?_
    rw [size_AX Rt hgen hnc hpG h31A χe]; exact (BR).Pb.hnX
  · refine pos_tbl _ _ hSP ?_
    rw [size_SP Rt hgen hnc hpG h31A χe]; exact (BR).Pb.hnS

theorem orbAdm_recJ9AX (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads) :
    OrbAdm (II) (orbOf (II)) := by
  obtain ⟨sX, sC, sW, sA, sV, sAX, sSP⟩ := sizes31 Rt hgen hnc hpG h31A χe hwalk9 hax9 hwalkA
  have hX := recX_X s f χe t r
  have hC := recX_C s f χe t r
  have hW := recX_W s f χe t r
  have hA := recX_A s f χe t r
  have hV := recX_V s f χe t r
  have hAX := recX_AX s f χe t r
  have hSP := recX_SP s f χe t r
  refine orbAdm_self (validJ9A_recJ9AX Rt hgen hnc hpG h31A χe hwalk9 hax9 hwalkA)
    (fits_tbl _ _ hX (le_tbl _ _ hX sX)) (fits_tbl _ _ hC (le_tbl _ _ hC sC))
    (fits_tbl _ _ hW (le_tbl _ _ hW sW)) ?_ (fits_tbl _ _ hA (le_tbl _ _ hA sA))
    (fits_tbl _ _ hV (le_tbl _ _ hV sV)) (fits_tbl _ _ hAX (le_tbl _ _ hAX sAX))
    (fits_tbl _ _ hSP (le_tbl _ _ hSP sSP))
  rw [recX_J_n]
  exact Nat.zero_le _

end Run

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsg

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsg
#print axioms Pb_n
#print axioms Pb_nC
#print axioms Pb_nW
#print axioms Pb_kroots
#print axioms Pb_nA
#print axioms Pb_nV
#print axioms Pb_krootsV
#print axioms Pb_nX
#print axioms Pb_nS
#print axioms Pb_regs
#print axioms Pb_ids
#print axioms Pb_nJ
#print axioms regs_DA
#print axioms ids_DA
#print axioms jrows_DA
#print axioms regs_B
#print axioms ids_B
#print axioms nJ_B
#print axioms HJ_eq
#print axioms xRPJ_eq
#print axioms size_X
#print axioms size_C
#print axioms size_W
#print axioms size_kroots
#print axioms size_A
#print axioms size_V
#print axioms size_krootsV
#print axioms size_AX
#print axioms size_SP
#print axioms msg_m
#print axioms recX_ρ_let
#print axioms rho_aux
#print axioms msg_ρ
#print axioms msg_ρS
#print axioms msg_pubsC
#print axioms msg_pubsW
#print axioms pubsJOf_zero
#print axioms msg_pubsJ
#print axioms hN_run
#print axioms msg_pubsA
#print axioms msg_pubsV
#print axioms msg_pubsX
#print axioms getD_map_lt
#print axioms msg_pubsS
#print axioms sizes31
#print axioms pos_tbl
#print axioms le_tbl
#print axioms fits_tbl
#print axioms validJ9A_recJ9AX
#print axioms orbAdm_recJ9AX
end Axioms
