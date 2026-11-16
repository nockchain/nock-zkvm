/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHWalkRun.lean

  Uses the R-card projections (`GenPortJ9AHProj.recX_W/recX_kroots/recX_M_pubsW`), never unfolds `recJ9AX`.

  The exec walk is the honest J-8 walk of `regD DA` (`DA` with its reads regrouped), not of `DA` itself.

  * `regD`, data equalities (`wsKr_eq`, `wRPJ_eq`);
  * `recJ9AX_W`, `recJ9AX_pubsW`, `recJ9AX_kroots`;
  * **`genJ9AX_walk_n`**, **`genJ9AX_walk_kroots`**, **`genJ9AX_walk_cols`**, **`genJ9AX_walk_pubs`**,
    **`genJ9AX_walk_interp`** (corrected form: `walkTrWE` at `regD DA`), **`genJ9AX_walk_ok`**.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkPubs
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkPub
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkBfs
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkGlue
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalGen
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkRun

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellRun (cs_eq acs_eq hcs_DA)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCell (interp_cast)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkOrd
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkBfs
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkGlue
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkPubs
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalk
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf cellsA_pos readsA)
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.V1J9A Nock.V1J9A.GenJ9AX

/-- **The regrouped record**: `D` with its reads regrouped so each root's reads are contiguous. -/
abbrev regD {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
    (D : ComplJ8Data.J8Data p Rg fuel s f r) : ComplJ8Data.J8Data p Rg fuel s f r :=
  { D with reads := regroup D.reads }

/-- The nodes of an admissible chip, cast to any equal row count, are `powN` at the chip's orbit. -/
theorem nodes_cast (q : ChipIn) (ho : OrbOK q) {n : ℕ} (e : q.n = n) :
    (nodesOf q ∘ Fin.cast e.symm) = ComplJ8Of.powN (mkOrbit q ho) n := by
  subst e
  exact funext fun i => nodesOf_eq q i

/-- Columns of a chip equal to `chipOf tbl`. -/
theorem cols_of_eq (C : ChipIn) (tbl : Array (Array (ZMod P))) (h : C = chipOf tbl) (i : Fin C.n) (c : ℕ) :
    C.cols c i = (tbl.getD (i : ℕ) #[]).getD c 0 := by
  subst h
  rfl

theorem cols_via (C : ChipIn) (tbl : Array (Array (ZMod P))) (h : C = chipOf tbl) (i : Fin C.n) (c : ℕ)
    (v : ZMod P) (hv : (tbl.getD (i : ℕ) #[]).getD c 0 = v) : C.cols c i = v :=
  (cols_of_eq C tbl h i c).trans hv

section Run
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hnc : callsOf (ComplJ8Data.rowsOfT t) = [])
  (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
include hnc hwalk9

local notation "DA" => j9aDataOf P Rg Rt hgen
local notation "DR" => regD (j9aDataOf P Rg Rt hgen)

/-! ## 1. Data equalities -/

theorem hall_DA : ∀ x ∈ (DA).reads, VclL.isPathAx x.2 = true := by
  intro x hx
  have hx' : x ∈ readsA t := hx
  simp only [readsA, List.mem_append] at hx'
  refine ComplJ8OfBal.isPathAx_of_two_le ?_
  rcases hx' with hx' | hx'
  · unfold ComplJ9AReads.walkReadsX9 at hx'
    simpa using (List.mem_filter.mp hx').2
  · unfold ComplJ9AChainsRun.axChainReadsK9 at hx'
    simpa using (List.mem_filter.mp hx').2

theorem hwalk_DA : ComplJ8Walk.WalkDepthOK (DA).reads :=
  ComplJ9ADataRec.walkDepthOK_readsA Rt hgen hwalk9

theorem hall_DR : ∀ x ∈ (DR).reads, VclL.isPathAx x.2 = true :=
  fun x hx => hall_DA Rt hgen hnc hwalk9 x ((mem_regroup _ x).mp hx)

theorem hwalk_DR : ComplJ8Walk.WalkDepthOK (DR).reads :=
  walkDepthOK_regroup _ (hwalk_DA Rt hgen hnc hwalk9)

theorem hp_DR : (walkRows (DR).cells (DR).reads).Perm (walkRows (DA).cells (DA).reads) :=
  walkRows_regroup_perm _ _ (hall_DA Rt hgen hnc hwalk9)

theorem hwcell_DA : ∀ u ∈ walkRows (DA).cells (DA).reads, u.label.node ∈ (DA).cells :=
  ComplJ9ABalGen.walkRows_node_cells_gen _ _ (ComplJ8Data.cells_closed _)
    (ComplJ9ADataRec.cellsA_pos Rt hgen) (ComplJ9ABalW.hslotA hgen) (ComplJ9ABalW.hrootA hgen)

theorem hwcell_DR : ∀ u ∈ walkRows (DR).cells (DR).reads, u.label.node ∈ (DR).cells :=
  hwcell_reg _ _ (hall_DA Rt hgen hnc hwalk9) (hwcell_DA Rt hgen hnc hwalk9)

theorem hwroot_DR : ∀ u ∈ walkRows (DR).cells (DR).reads,
    u.label.root ∈ (DR).cells ∨ u.label.root.isCell = false :=
  hwroot_reg _ _ (hall_DA Rt hgen hnc hwalk9) (hwcell_DA Rt hgen hnc hwalk9)

theorem hH_eq (χe : CoinsE) : HJ s f χe (RnOf t r) = (DA).H := by
  show hdlB (csJ s f χe (RnOf t r)) (acsLJ s f χe (RnOf t r)) = _
  rw [cs_eq Rt hgen hnc χe, acs_eq Rt hgen hnc χe, GenPortJ9A.hdlB_eq_hdlP]
  rfl

/-- The executable `(ws, kr)` is the honest walk rows of `regD DA` (via `wrowOf`) and its root count. -/
theorem wsKr_eq (χe : CoinsE) :
    wsKrJ s f χe (RnOf t r) =
      ((walkRows (DR).cells (DR).reads).map GenPortJ9AHWalkRow.wrowOf, krW (DR).cells (DR).reads) := by
  have h := walkGen_eq_map (DA).cells (readsA t) (hall_DA Rt hgen hnc hwalk9) (hwalk_DA Rt hgen hnc hwalk9)
  show walkGen ((csJ s f χe (RnOf t r)).headD (.atom 0)) (readsA t) = _
  rw [cs_eq Rt hgen hnc χe]
  exact Prod.ext h.1 h.2

/-- The executable walk table and publics are `walkGenRowsB` at `regD DA`'s data. -/
theorem wRPJ_eq (χe : CoinsE) :
    wRPJ s f χe (RnOf t r) =
      walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) (DR).H (idxN (DR).cells)
        HonestK8.certB8 (DR).cells ((walkRows (DR).cells (DR).reads).map GenPortJ9AHWalkRow.wrowOf)
        (krW (DR).cells (DR).reads) := by
  unfold wRPJ kJ alphaJ gammaJ
  rw [hH_eq Rt hgen hnc hwalk9 χe, wsKr_eq Rt hgen hnc hwalk9 χe, cs_eq Rt hgen hnc χe]

theorem recJ9AX_W (χe : CoinsE) :
    (recJ9AX s f χe t r).W =
      chipOf (walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) (DR).H (idxN (DR).cells)
        HonestK8.certB8 (DR).cells ((walkRows (DR).cells (DR).reads).map GenPortJ9AHWalkRow.wrowOf)
        (krW (DR).cells (DR).reads)).1 := by
  rw [recX_W, wRPJ_eq Rt hgen hnc hwalk9 χe]

theorem recJ9AX_pubsW (χe : CoinsE) :
    (recJ9AX s f χe t r).M.pubsW =
      (walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) (DR).H (idxN (DR).cells)
        HonestK8.certB8 (DR).cells ((walkRows (DR).cells (DR).reads).map GenPortJ9AHWalkRow.wrowOf)
        (krW (DR).cells (DR).reads)).2 := by
  rw [recX_M_pubsW, wRPJ_eq Rt hgen hnc hwalk9 χe]

theorem recJ9AX_kroots' (χe : CoinsE) :
    (recJ9AX s f χe t r).kroots = krW (DR).cells (DR).reads := by
  rw [recX_kroots, wsKr_eq Rt hgen hnc hwalk9 χe]

/-! ## 2. The final statements -/

theorem genJ9AX_walk_n' (χe : CoinsE) :
    (recJ9AX s f χe t r).W.n = (walkRows (DR).cells (DR).reads).length := by
  rw [recJ9AX_W Rt hgen hnc hwalk9 χe]
  show (walkGenRowsB _ _ _ _ _ _ _ _ _ _).1.size = _
  rw [walkGenRowsB_size, List.length_map]

theorem genJ9AX_walk_n (χe : CoinsE) :
    (recJ9AX s f χe t r).W.n = (walkRows (DA).cells (DA).reads).length :=
  (genJ9AX_walk_n' Rt hgen hnc hwalk9 χe).trans (hp_DR Rt hgen hnc hwalk9).length_eq

theorem genJ9AX_walk_kroots (χe : CoinsE) :
    (recJ9AX s f χe t r).kroots = krW (DA).cells (DA).reads :=
  (recJ9AX_kroots' Rt hgen hnc hwalk9 χe).trans (krW_regroup _ _ (hall_DA Rt hgen hnc hwalk9))

theorem genJ9AX_walk_cols (χe : CoinsE) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length))
    (i : Fin (recJ9AX s f χe t r).W.n) (c : ℕ) (hc : c < 166) :
    (recJ9AX s f χe t r).W.cols c i =
      fullCol (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (HonestK8.certUp
          (ComplJ8Enc.wColHQBE deltaF powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
            (ComplJ8Of.powN o _) o (VerJ8.chalsMJ8 deltaF (toχ χe))
            (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) o (toχ χe)) (ComplJ8Of.encR deltaF (toχ χe))
            (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe)) (DR).cells (DR).reads
            (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR)) (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR)))
          (ComplJ8Walk.lenB (DR).cells (DR).reads)) c
        (Fin.cast (genJ9AX_walk_n' Rt hgen hnc hwalk9 χe) i) := by
  have hcg := walkGenRowsB_cols χe (DR) (hcs_DA Rt hgen hnc χe) (hwcell_DR Rt hgen hnc hwalk9)
    (hwroot_DR Rt hgen hnc hwalk9) (hall_DR Rt hgen hnc hwalk9) (hwalk_DR Rt hgen hnc hwalk9) o hinj
    (Fin.cast (genJ9AX_walk_n' Rt hgen hnc hwalk9 χe) i) c hc
  rw [Fin.val_cast] at hcg
  exact cols_via _ _ (recJ9AX_W Rt hgen hnc hwalk9 χe) i c _ hcg

/-- Injectivity of the `powN` nodes at `DR`'s row count, for any orbit, from the sizes. -/
theorem powN_inj_DR (hF : ComplJ8Of.DvdOK (DA)) :
    Function.Injective (ComplJ8Of.powN (ComplJ8Of.orbJ8 (DA) hF) (walkRows (DR).cells (DR).reads).length) := by
  have hmem : (walkRows (DA).cells (DA).reads).length ∈ ComplJ8Of.sizesJ8 (DA) := by
    simp [ComplJ8Of.sizesJ8]
  have hle : (walkRows (DR).cells (DR).reads).length ≤ 2 ^ ComplJ8Of.htJ8 (DA) := by
    exact (hp_DR Rt hgen hnc hwalk9).length_eq.le.trans (ComplJ8Of.le_two_pow_ht (DA) hmem)
  exact (ComplJ8Of.powN_ok _ hle).1

theorem pubs_exec_DR (χe : CoinsE) (hF : ComplJ8Of.DvdOK (DA)) (j : ℕ) :
    K3.toK ((recJ9AX s f χe t r).M.pubsW j) =
      ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) (ComplJ8Of.orbJ8 (DA) hF) (toχ χe) j := by
  have a : ∀ c ∈ (DR).cells, c.isCell = true := hcs_DA Rt hgen hnc χe
  have b := hwcell_DR Rt hgen hnc hwalk9
  have c := hwroot_DR Rt hgen hnc hwalk9
  have hI := powN_inj_DR Rt hgen hnc hwalk9 hF
  have e1 := walkGenRowsB_pubs χe (DR) a b c (ComplJ8Of.orbJ8 (DA) hF) hI j
  rw [recJ9AX_pubsW Rt hgen hnc hwalk9 χe]
  exact e1

theorem pubs_DR_DA (χe : CoinsE) (hF : ComplJ8Of.DvdOK (DA)) (j : ℕ) :
    ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) (ComplJ8Of.orbJ8 (DA) hF) (toχ χe) j =
      ComplJ8Of.pubsWOf deltaF powerBasis3 (DA) (ComplJ8Of.orbJ8 (DA) hF) (toχ χe) j := by
  have hmem : (walkRows (DA).cells (DA).reads).length ∈ ComplJ8Of.sizesJ8 (DA) := by
    simp [ComplJ8Of.sizesJ8]
  have hinj : Function.Injective (ComplJ8Of.powN (ComplJ8Of.orbJ8 (DA) hF)
      (walkRows (DA).cells (DA).reads).length) :=
    (ComplJ8Of.powN_ok _ (ComplJ8Of.le_two_pow_ht _ hmem)).1
  exact congrFun (GenPortJ9AHWalkPub.pubsWOf_perm deltaF powerBasis3 (DA) (DR) rfl rfl (hp_DR Rt hgen hnc hwalk9)
      (ComplJ8Of.orbJ8 (DA) hF) (ComplJ8Of.orbJ8 (DA) hF) hinj (powN_inj_DR Rt hgen hnc hwalk9 hF)
      (toχ χe)) j

theorem genJ9AX_walk_pubs (χe : CoinsE) (hF : ComplJ8Of.DvdOK (DA)) (j : ℕ) :
    K3.toK ((recJ9AX s f χe t r).M.pubsW j) =
      ComplJ8Of.pubsWOf deltaF powerBasis3 (DA) (ComplJ8Of.orbJ8 (DA) hF) (toχ χe) j :=
  (pubs_exec_DR Rt hgen hnc hwalk9 χe hF j).trans (pubs_DR_DA Rt hgen hnc hwalk9 χe hF j)

/-- `nodesOf I.W` at `DR`'s row count is `powN` at the chip's own orbit, and injectivity transfers. -/
theorem powN_inj_chip (χe : CoinsE) (ho : OrbOK (recJ9AX s f χe t r).W)
    (hinj : Function.Injective (nodesOf (recJ9AX s f χe t r).W)) :
    Function.Injective (ComplJ8Of.powN (mkOrbit (recJ9AX s f χe t r).W ho)
      (walkRows (DR).cells (DR).reads).length) := by
  have hI : Function.Injective
      (nodesOf (recJ9AX s f χe t r).W ∘ Fin.cast (genJ9AX_walk_n' Rt hgen hnc hwalk9 χe).symm) :=
    hinj.comp (Fin.cast_injective _)
  rw [nodes_cast _ ho (genJ9AX_walk_n' Rt hgen hnc hwalk9 χe)] at hI
  exact hI

theorem genJ9AX_walk_interp (χe : CoinsE) (ho : OrbOK (recJ9AX s f χe t r).W)
    (hinj : Function.Injective (nodesOf (recJ9AX s f χe t r).W)) (j : ℕ) (hj : j < 166) :
    interpOf (recJ9AX s f χe t r).W j =
      ComplJ8Enc.walkTrWE deltaF powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN (mkOrbit (recJ9AX s f χe t r).W ho) (walkRows (DR).cells (DR).reads).length)
        (mkOrbit (recJ9AX s f χe t r).W ho) (VerJ8.chalsMJ8 deltaF)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) (mkOrbit (recJ9AX s f χe t r).W ho))
        (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.encR deltaF) (DR).cells (DR).reads
        (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR)) (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR))
        (toχ χe) ⟨j, hj⟩ := by
  have hn := genJ9AX_walk_n' Rt hgen hnc hwalk9 χe
  have hinj' := powN_inj_chip Rt hgen hnc hwalk9 χe ho hinj
  unfold interpOf
  rw [interp_cast hn, nodes_cast _ ho hn]
  unfold ComplJ8Enc.walkTrWE honestQ
  refine congrArg (Lagrange.interpolate Finset.univ
    (ComplJ8Of.powN (mkOrbit (recJ9AX s f χe t r).W ho) (walkRows (DR).cells (DR).reads).length)) ?_
  funext i'
  exact genJ9AX_walk_cols Rt hgen hnc hwalk9 χe (mkOrbit (recJ9AX s f χe t r).W ho) hinj'
    (Fin.cast hn.symm i') j hj

/-- **The walk chip obligation at `regD DA`**, any admissible orbit `o` (instantiate at `mkOrbit I.W ho` with
`powN_inj_chip`), families taken at `DA` (`BRun9A`'s good event). -/
theorem genJ9AX_walk_ok (hp63 : 2 ^ 63 < P) (h31A : ComplJ9ARun.Rows31A (DA))
    {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length))
    (χ : Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC)
    (hV : ∀ e ∈ ComplJ8Of.famWalkV deltaF (DA) (K := KC), χ ∉ e.ev)
    (hH : ∀ e ∈ ComplJ8Of.famWalkH deltaF (DA) (K := KC), χ ∉ e.ev) :
    (WalkJ8.walkChipJ8 deltaF (krW (DR).cells (DR).reads) powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length) o (chalsMJ8 deltaF χ)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) o χ)).rap.Satisfies
      (fun j => ComplJ8Enc.walkTrWE deltaF powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length) o (chalsMJ8 deltaF)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) o) (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF)
        (ComplJ8Of.encR deltaF) (DR).cells (DR).reads (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR))
        (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR)) χ
        (Fin.cast (WalkJ8.walkChipJ8_width deltaF (krW (DR).cells (DR).reads) powerBasis3
          (ComplJ8Of.walk_pos (DR).cells (DR).reads)
          (ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length) o (chalsMJ8 deltaF χ)
          (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) o χ)) j)) ∧
    (WalkJ8.walkChipJ8 deltaF (krW (DR).cells (DR).reads) powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length) o (chalsMJ8 deltaF χ)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) o χ)).BindsPreprocessing
      (fun j => ComplJ8Enc.walkTrWE deltaF powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length) o (chalsMJ8 deltaF)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) o) (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF)
        (ComplJ8Of.encR deltaF) (DR).cells (DR).reads (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR))
        (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR)) χ
        (Fin.cast (WalkJ8.walkChipJ8_width deltaF (krW (DR).cells (DR).reads) powerBasis3
          (ComplJ8Of.walk_pos (DR).cells (DR).reads)
          (ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length) o (chalsMJ8 deltaF χ)
          (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) o χ)) j)) := by
  have h31 := ComplJ9ARun.rows31_of_A h31A
  have hmC : (DA).cells.length ∈ ComplJ8Of.sizesJ8 (DA) := by simp [ComplJ8Of.sizesJ8]
  have hmW : (walkRows (DA).cells (DA).reads).length ∈ ComplJ8Of.sizesJ8 (DA) := by
    simp [ComplJ8Of.sizesJ8]
  have h1 := h31 _ hmC
  have h2 := h31 _ hmW
  have h3 := krW_le_rows (DA).cells (DA).reads
  have h64 : (2 : ℕ) ^ 31 + 2 ^ 31 < 2 ^ 63 := by norm_num
  have hlenW := (hp_DR Rt hgen hnc hwalk9).length_eq
  have hkrW := krW_regroup (DA).cells (DA).reads (hall_DA Rt hgen hnc hwalk9)
  have hlenW' : (walkRows (DA).cells (regroup (DA).reads)).length =
      (walkRows (DA).cells (DA).reads).length := hlenW
  have hcl : (DR).cells.length < P := by
    show (DA).cells.length < P
    omega
  have hkp : krW (DR).cells (DR).reads + (walkRows (DR).cells (DR).reads).length < P := by
    show krW (DA).cells (regroup (DA).reads) + (walkRows (DA).cells (regroup (DA).reads)).length < P
    omega
  have hadj : ∀ (i : Fin (walkRows (DR).cells (DR).reads).length)
      (hi : (i : ℕ) + 1 < (walkRows (DR).cells (DR).reads).length),
      ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length ⟨(i : ℕ) + 1, hi⟩ =
        ComplJ8Of.powN o (walkRows (DR).cells (DR).reads).length i * o.ω :=
    fun i hi => pow_succ _ _
  exact GenPortJ9AHWalkPub.walkOK_at deltaF powerBasis3 (DR) hp63 hcl hkp (hwalk_DR Rt hgen hnc hwalk9)
    (fun x => ComplJ8Of.hdl_kind (DA).cells (DA).acs x) o hinj hadj χ
    (GenPortJ9AHWalkFam.famWalkV_good_of_perm deltaF (DA) (DR) rfl (hp_DR Rt hgen hnc hwalk9) χ hV)
    (GenPortJ9AHWalkFam.famWalkH_good_of_perm deltaF (DA) (DR) rfl rfl (hp_DR Rt hgen hnc hwalk9) χ hH)

end Run

#print axioms nodes_cast
#print axioms hall_DA
#print axioms hwalk_DA
#print axioms hall_DR
#print axioms hwalk_DR
#print axioms hp_DR
#print axioms hwcell_DA
#print axioms hwcell_DR
#print axioms hwroot_DR
#print axioms hH_eq
#print axioms wsKr_eq
#print axioms wRPJ_eq
#print axioms recJ9AX_W
#print axioms recJ9AX_pubsW
#print axioms recJ9AX_kroots'
#print axioms genJ9AX_walk_n'
#print axioms genJ9AX_walk_n
#print axioms genJ9AX_walk_kroots
#print axioms genJ9AX_walk_cols
#print axioms powN_inj_DR
#print axioms cols_via
#print axioms pubs_exec_DR
#print axioms pubs_DR_DA
#print axioms genJ9AX_walk_pubs
#print axioms powN_inj_chip
#print axioms genJ9AX_walk_interp
#print axioms genJ9AX_walk_ok

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkRun
