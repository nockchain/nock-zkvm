/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/J8GenOfBalG.lean

 **J-8 completeness over any admissible `J8Data`, continued**: the balance `balG` of `ComplJ8OfBalG`; `reads_eqG` / `preads_eqG` state the reads as a PERMUTATION of the
 row-ordered read lists (the source theorems state an equality), and the sums over the reads go through `Perm.sum_eq`.
 Every declaration is the corresponding statement and proof over `j8DataGen … O` (suffix `G`), except where the
 free list orders need a membership or permutation step.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.J8GenOfBal
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.V1J8.Gen (cellsOfRoots addCells rootsOf idxOf idxD combOf spineOf padN linkOrder addNew lastIdxOf
  sxOf incChain AInfo atomV hdN' tlN' idxN pathReads walkGen mvCounts mxCounts mvPins wCounts bump callsOf
  WRow budget)
open Nock.Jet.Autogen (Tpl compile)
open Nock.Jet.ChipJ8 (CRow PRow layoutJ8 keysOf entsX)
open Nock.Jet.RapJetJ8 (consKT provKT tlF)

noncomputable section

/-! ### Twins of `ComplJ8OfBalG` -/

section ComplJ8OfBalGG_1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG
open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
noncomputable section
section TermsRun
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
/-- The run's cells are cells, and their cell children are in the list. -/
theorem cells_kidsG (c : Noun) (hc : c ∈ (j8DataGen p Rg Rt hgen O).cells) :
    ∃ x y, c = Noun.cell x y ∧ (x.isCell = true → x ∈ (j8DataGen p Rg Rt hgen O).cells) ∧
      (y.isCell = true → y ∈ (j8DataGen p Rg Rt hgen O).cells) := by
  have hcc := (ComplJ8Walk.cellsOfRoots_mem _ c ((O.permC _).mem_iff.mp hc)).1
  cases c with
  | atom v => simp [Noun.isCell] at hcc
  | cell x y =>
    have hcl := cells_closedG p Rg Rt hgen O x y hc (by simp)
    refine ⟨x, y, rfl, fun hx => ?_, fun hy => ?_⟩
    · cases x with
      | atom v => simp [Noun.isCell] at hx
      | cell x1 x2 => exact hcl.1 x1 x2 rfl
    · cases y with
      | atom v => simp [Noun.isCell] at hy
      | cell y1 y2 => exact hcl.2 y1 y2 rfl

/-- **The J-8 walk handle import is the walk-row sum of the cell handle weights.** -/
theorem whX_eqG {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjC : Function.Injective (powN o (j8DataGen p Rg Rt hgen O).cells.length))
    (hinjW : Function.Injective (powN o (walkRows (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).reads).length))
    (χ : Coins frameJ8 K) :
    whX δ b (j8DataGen p Rg Rt hgen O) o χ =
      ((walkRows (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).reads).map fun u =>
        GC δ b (j8DataGen p Rg Rt hgen O) (cells_posG Rt hgen O) o χ
          ((j8DataGen p Rg Rt hgen O).cells.idxOf u.label.node)).sum := by
  set D := j8DataGen p Rg Rt hgen O with hD
  have hwcell := walkRows_node_cellsG (p := p) Rt hgen O
  have hterm : ∀ k ∈ Finset.range (walkRows D.cells D.reads).length, (wdN δ b D o χ WalkHC.xKeyH k)⁻¹ =
      GC δ b D (cells_posG Rt hgen O) o χ (D.cells.idxOf (wTrie D.cells D.reads k).label.node) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hmem : (wTrie D.cells D.reads k).label.node ∈ D.cells := hwcell _ (wTrie_mem _ _ hk')
    obtain ⟨x, y, hxy, hx, hy⟩ := cells_kidsG Rt hgen O _ hmem
    have hjl := List.idxOf_lt_length_of_mem hmem
    have hyj : D.cells[D.cells.idxOf (wTrie D.cells D.reads k).label.node] = Noun.cell x y := by
      rw [List.getElem_idxOf hjl]; exact hxy
    have hd : wdN δ b D o χ WalkHC.xKeyH k = ComplJ8Bad.ρH δ χ + recDen 0 (ComplJ8Bad.γH δ χ)
        ((wValsC δ D χ ⟨k, hk'⟩).idx, (kLW D ⟨k, hk'⟩, vLW D ⟨k, hk'⟩), (kRW D ⟨k, hk'⟩, vRW D ⟨k, hk'⟩)) := by
      simp only [wdN, WalkTraceHQ.dN, dif_pos hk']
      exact (walk_dRow_split δ b D o hinjW χ (pubsW0 δ D χ) ⟨k, hk'⟩).1
    have hv : (wValsC δ D χ ⟨k, hk'⟩).idx = ((D.cells.idxOf (wTrie D.cells D.reads k).label.node : ℕ) : ZMod p) := rfl
    have hkl : kLW D ⟨k, hk'⟩ = (((D.H x).1 : ℕ) : ZMod p) ∧ vLW D ⟨k, hk'⟩ = (((D.H x).2 : ℕ) : ZMod p) ∧
        kRW D ⟨k, hk'⟩ = (((D.H y).1 : ℕ) : ZMod p) ∧ vRW D ⟨k, hk'⟩ = (((D.H y).2 : ℕ) : ZMod p) := by
      simp only [kLW, vLW, kRW, vRW, wNode, hxy]
      exact ⟨rfl, rfl, rfl, rfl⟩
    simp only [GC]
    rw [hd, hv, hkl.1, hkl.2.1, hkl.2.2.1, hkl.2.2.2,
      cellHx_eq δ b D (cells_posG Rt hgen O) o hinjC χ rfl _ hjl hyj hx hy]
  unfold whX
  rw [Finset.sum_congr rfl hterm]
  exact ComplJ8OfBal.sum_range_getD' (trie (.atom 0) (.atom 0) [] [])
    (fun u => GC δ b D (cells_posG Rt hgen O) o χ (D.cells.idxOf u.label.node)) _

end TermsRun
section Export
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
set_option maxHeartbeats 1000000 in
/-- **`balG`'s export clause at the run, at every coin**, with the compute export total `hC` and the J export
key identity `hJ` carried (exact statements below); the J-8 walk import, the cell handle-export terminal and the
counts are discharged (`whX_eqG`, `chT_eq`, `mh_eq_cnt`). -/
theorem balG1_ofG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataGen p Rg Rt hgen O).reads)
    (hrange : ∀ q ∈ (ComplJ8Data.xRecs (j8DataGen p Rg Rt hgen O)).flatMap ComplJ8Data.NamedRecs.recs, 0 < q.2 →
      q.1 < (j8DataGen p Rg Rt hgen O).cells.length)
    (χ : Coins frameJ8 K)
    (hC : ((BRunG δ b Rt hgen O o).M χ).ρ 3 =
      wsum (GC δ b (j8DataGen p Rg Rt hgen O) (cells_posG Rt hgen O) o χ)
        ((j8DataGen p Rg Rt hgen O).bases.flatMap fun bs =>
          ComplJ8Data.xConsumesP p (⟨bs, bs, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))))
    (hJ : ∀ row ∈ (j8DataGen p Rg Rt hgen O).jrows, ∀ κ ∈ Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.entsX row,
      ComplJ8OfBal.fH δ b χ (Nock.Jet.RapJetJ8.keyK 5 κ) =
        GC δ b (j8DataGen p Rg Rt hgen O) (cells_posG Rt hgen O) o χ (κ.headD 0).val) :
    ((BRunG δ b Rt hgen O o).M χ).ρ 3 +
        (Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsW WalkHQ.pubXQ)
          (((BRunG δ b Rt hgen O o).M χ).pubsW (WalkHQ.pubXQ + 1)) +
        Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsJ 2) (((BRunG δ b Rt hgen O o).M χ).pubsJ 3)) =
      Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsC CellHQ.pubHQ)
        (((BRunG δ b Rt hgen O o).M χ).pubsC (CellHQ.pubHQ + 1)) := by
  revert o
  set D := j8DataGen p Rg Rt hgen O with hD
  intro o hC hJ
  have hCp : 0 < D.cells.length := cells_posG Rt hgen O
  set G := GC δ b D hCp o χ with hG
  have hmC : D.cells.length ∈ sizesJ8 D := by simp [sizesJ8]
  have hmW : (walkRows D.cells D.reads).length ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjC := (powN_ok o (le_two_pow_ht D hmC)).1
  have hinjW := (powN_ok o (le_two_pow_ht D hmW)).1
  have eJ := h1J_runG δ b Rt hgen O o hpG h31 χ
  have eW : Quad.mk (algebraMap (ZMod p) K δ) (((BRunG δ b Rt hgen O o).M χ).pubsW WalkHQ.pubXQ)
      (((BRunG δ b Rt hgen O o).M χ).pubsW (WalkHQ.pubXQ + 1)) = whX δ b D o χ := by
    show Quad.mk _ (pubsWOf δ b D o χ WalkHQ.pubXQ) (pubsWOf δ b D o χ (WalkHQ.pubXQ + 1)) = _
    have h4 : pubsWOf δ b D o χ WalkHQ.pubXQ = pub2 δ (whX δ b D o χ) 4 := by simp [pubsWOf, WalkHQ.pubXQ]
    have h5 : pubsWOf δ b D o χ (WalkHQ.pubXQ + 1) = pub2 δ (whX δ b D o χ) 5 := by simp [pubsWOf, WalkHQ.pubXQ]
    rw [h4, h5, pub2_mk2 δ _ 4 rfl]
  have eC : Quad.mk (algebraMap (ZMod p) K δ) (((BRunG δ b Rt hgen O o).M χ).pubsC CellHQ.pubHQ)
      (((BRunG δ b Rt hgen O o).M χ).pubsC (CellHQ.pubHQ + 1)) = chT δ b D hCp o χ := by
    show Quad.mk _ (pubsCOf δ b D hCp o χ CellHQ.pubHQ) (pubsCOf δ b D hCp o χ (CellHQ.pubHQ + 1)) = _
    have h4 : pubsCOf δ b D hCp o χ CellHQ.pubHQ = pub2 δ (chT δ b D hCp o χ) 4 := by
      simp [pubsCOf, CellHQ.pubHQ]
    have h5 : pubsCOf δ b D hCp o χ (CellHQ.pubHQ + 1) = pub2 δ (chT δ b D hCp o χ) 5 := by
      simp [pubsCOf, CellHQ.pubHQ]
    rw [h4, h5, pub2_mk2 δ _ 4 rfl]
  rw [eW, eC, eJ, hC, whX_eqG δ b Rt hgen O o hinjC hinjW χ, chT_eq δ b D hCp o χ]
  -- the cell side: counts
  have hcnt : ∑ j ∈ Finset.range D.cells.length, ((D.mh.getD j 0 : ℕ) : 𝕂′) * G j =
      ∑ j ∈ Finset.range D.cells.length, ((ComplJ8Data.cnt (ComplJ8Data.xRecs D) j : ℕ) : 𝕂′) * G j :=
    Finset.sum_congr rfl fun j hj => by rw [mh_eq_cntG p Rg Rt hgen O j (Finset.mem_range.mp hj)]
  rw [hcnt, sum_cnt_eq G _ _ hrange]
  simp only [ComplJ8Data.xRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil, wsum_append]
  congr 1
  congr 1
  · -- the walk
    rw [wsum_cellPairs]
    have hall : ∀ x ∈ D.reads, VclL.isPathAx x.2 = true := by
      intro x hx
      have hx := (O.permR _ _).mem_iff.mp hx
      unfold Nock.V1J8.Gen.pathReads at hx
      exact ComplJ8OfBal.isPathAx_of_two_le (by simpa using (List.mem_filter.mp hx).2)
    have h62 : ∀ r ∈ VclL.pathReads D.reads, VclL.depthOf r.2 ≤ 62 :=
      fun r hr => (hwalk r hr).trans (by norm_num)
    have hperm := ComplJ8OfBal.walkGen_nodes_perm D.cells _ hall h62
    have hws : D.ws = (Nock.V1J8.Gen.walkGen (D.cells.headD (.atom 0)) D.reads).1 := rfl
    have hwcell := walkRows_node_cellsG (p := p) Rt hgen O
    rw [hws, ((hperm.map fun n => if n.isCell then G (Nock.V1J8.Gen.idxOf D.cells n) else 0).sum_eq),
      List.map_map]
    congr 1
    refine List.map_congr_left fun u hu => ?_
    have hm := hwcell u hu
    have hc := (ComplJ8Walk.cellsOfRoots_mem _ _ ((O.permC _).mem_iff.mp hm)).1
    simp only [Function.comp_apply, hc, if_true]
    rw [ComplJ8OfBal.genIdxOf_eq _ _ hm]
  · -- the J reads
    rw [wsum_keys δ G (Nock.Jet.ChipJ8.keysOf (F := ZMod p) Nock.Jet.ChipJ8.entsX) (fun κ : List (ZMod p) => (κ.headD 0).val)]
    simp only [ComplJ8Bal.tots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      ComplJ8OfBal.tabJX, ComplJ8OfBal.mapTab, ComplJ8Bal.tot, ComplJ8Bal.tabOfRows, List.ofFn_get]
    have hp : ∀ L : List (Nock.Jet.ChipJ8.CRow (ZMod p)),
        (L.flatMap fun _ => ([] : List (List (ZMod p) × 𝕂′))) = [] := fun L => by simp
    rw [hp]
    simp only [List.map_nil, List.sum_nil, sub_zero, List.map_map]
    congr 1
    refine List.map_congr_left fun κ hκ => ?_
    obtain ⟨row, hrow, hk⟩ := List.mem_flatMap.mp hκ
    simp only [Function.comp_apply]
    exact hJ row hrow κ hk

end Export
section HJ
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
set_option maxHeartbeats 1000000 in
/-- **`hJ`**: with the J rows at the cell table's handle `hJd`, no sibling binder: the calls' typing facts (`calls_of_hregC`), the base-gate
fact `kN = 1` on export reads and `|cells| < p`, every J export key's weight is the cell handle weight of its
node serial. -/
theorem hJ_exportG {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjC : Function.Injective (powN o (j8DataGen p Rg Rt hgen O).cells.length)) (χ : Coins frameJ8 K)
    (hcalls : ∀ cl ∈ (j8DataGen p Rg Rt hgen O).calls,
      (Rt cl.1).WellTyped p ∧ ∃ r, (Rt cl.1).sem p cl.2 = some r)
    (hlen : (j8DataGen p Rg Rt hgen O).cells.length < p)
    (hkN : ∀ x ∈ (j8DataGen p Rg Rt hgen O).jrows,
      (x.pre.kd = .rp ∨ x.pre.kd = .sl ∨ x.pre.kd = .sr) → x.w.kN = 1) :
    ∀ row ∈ (j8DataGen p Rg Rt hgen O).jrows, ∀ κ ∈ Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.entsX row,
      ComplJ8OfBal.fH δ b χ (Nock.Jet.RapJetJ8.keyK 5 κ) =
        GC δ b (j8DataGen p Rg Rt hgen O) (cells_posG Rt hgen O) o χ (κ.headD 0).val := by
  set D := j8DataGen p Rg Rt hgen O with hD
  intro x hx κ hκ
  have hκ' : κ = [x.w.vN, x.w.kL, x.w.vL, x.w.kR, x.w.vR] := by
    simp only [Nock.Jet.ChipJ8.keysOf, Nock.Jet.ChipJ8.entsX, List.mem_map, List.mem_filter, List.mem_cons,
      List.not_mem_nil, or_false] at hκ
    obtain ⟨e, ⟨he, hk⟩, rfl⟩ := hκ
    rcases he with rfl | rfl | rfl <;>
      simp [Nock.Jet.ChipJ8.keyX, Nock.Jet.ChipJ8.KE.ev, Nock.Jet.ChipJ8.colOf, Nock.Jet.ChipJ8.Col.vN,
        Nock.Jet.ChipJ8.Col.kL, Nock.Jet.ChipJ8.Col.vL, Nock.Jet.ChipJ8.Col.kR, Nock.Jet.ChipJ8.Col.vR]
  obtain ⟨hkd, -⟩ := ComplJ8Data.keysOf_entsX_head x κ hκ
  have hk1 := hkN x hx hkd
  obtain ⟨r0, hr0, hpre, e1, e2, e3, e4, e5, e6⟩ := mvFixP_mem' _ _ x hx
  have hcl : ComplJ8Data.ClP D.cells [] := cells_closedG p Rg Rt hgen O
  have hjn := jn_goodG p Rg Rt hgen O
  have hk := honestJ8_kids (p := p) (hd := ComplJ8Data.hJd p D.cells D.acs) hcl Rt D.regs D.calls (by
      intro cl hcl'
      have hc1 := List.fst_mem_of_mem_zipIdx hcl'
      have hc := hcalls cl.1 hc1
      refine ⟨hjn _ ?_, fun y hy => hjn _ ?_, hc.1, hc.2⟩
      · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨cl, hcl', List.mem_cons_self⟩)
      · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨cl, hcl', List.mem_cons_of_mem _ hy⟩))
    r0 hr0 (by rw [← hpre]; exact hkd)
  obtain ⟨y, hy, k1, k2, k3, k4, k5, k6⟩ := hk
  cases y with
  | atom v => rw [e1, k1] at hk1; exact absurd hk1 (ComplJ8Data.hJd_atom_ne p _ _ v)
  | cell yl yr =>
    have hm := hy yl yr rfl
    have hkids := hcl yl yr hm (by simp)
    have hxl : yl.isCell = true → yl ∈ D.cells := fun h => by
      cases yl with
      | atom _ => simp [Noun.isCell] at h
      | cell a b => exact hkids.1 a b rfl
    have hxr : yr.isCell = true → yr ∈ D.cells := fun h => by
      cases yr with
      | atom _ => simp [Noun.isCell] at h
      | cell a b => exact hkids.2 a b rfl
    have hjl := List.idxOf_lt_length_of_mem hm
    have hv : x.w.vN = ((D.cells.idxOf (Noun.cell yl yr) : ℕ) : ZMod p) := by
      rw [e2, k2]
      simp only [ComplJ8Data.hJd, ComplJ8Data.hdlP]
      rw [ComplJ8OfBal.genIdxOf_eq _ _ hm]
    have hval : (κ.headD 0).val = D.cells.idxOf (.cell yl yr) := by
      rw [hκ']
      simp only [List.headD_cons]
      rw [hv, ZMod.val_natCast, Nat.mod_eq_of_lt (hjl.trans hlen)]
    rw [hval]
    simp only [GC]
    rw [cellHx_eq δ b D (cells_posG Rt hgen O) o hinjC χ rfl _ hjl (List.getElem_idxOf hjl) hxl hxr, hκ', fH_key]
    have hkl : x.w.kL = (((D.H yl).1 : ℕ) : ZMod p) ∧ x.w.vL = (((D.H yl).2 : ℕ) : ZMod p) ∧
        x.w.kR = (((D.H yr).1 : ℕ) : ZMod p) ∧ x.w.vR = (((D.H yr).2 : ℕ) : ZMod p) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [e3, k3]; rfl
      · rw [e4, k4]; rfl
      · rw [e5, k5]; rfl
      · rw [e6, k6]; rfl
    rw [hv, hkl.1, hkl.2.1, hkl.2.2.1, hkl.2.2.2]

end HJ
section XRun
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (SlotX EntX Bal cellRecX hdX)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (castSlotX castEntX DX invQX)
set_option maxHeartbeats 1000000 in
/-- **The `.x` reciprocal sum of run row `j` is the weighted total of the row's export consumes.** -/
theorem xSum_runG (hsm : ∀ u, InTree t u → HonestRowX.SmallX p (rowOfSkelX u.label))
    (hlen : (j8DataGen p Rg Rt hgen O).cells.length < p) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjC : Function.Injective (powN o (j8DataGen p Rg Rt hgen O).cells.length)) (χ : Coins frameJ8 K)
    (pubVal : ℕ → ZMod p) (j : ℕ) (hj : j < (bfsForest [t]).length) :
    xSum δ b (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      wsum (GC δ b (j8DataGen p Rg Rt hgen O) (cells_posG Rt hgen O) o χ)
        (ComplJ8Data.xConsumesP p (⟨Nock.V1J8.FillX.colXE (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd
          (HonestWalkX.rowAtWX (bfsForest [t]) (j + 1)) (HonestTraceX.flX j) (HonestTraceX.llX (bfsForest [t]) j),
          Nock.V1J8.FillX.colXE (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd
          (HonestWalkX.rowAtWX (bfsForest [t]) (j + 1)) (HonestTraceX.flX j) (HonestTraceX.llX (bfsForest [t]) j),
          fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))) := by
  set D := j8DataGen p Rg Rt hgen O with hD
  set W := bfsForest [t] with hW
  set rr := HonestWalkX.rowAtWX W (j + 1) with hrr
  set e0 := HonestTraceX.env0 D.H D.pd W (VerJ8.chalVJ8 b χ) pubVal j with he0
  set e' : Nock.Reified.Env (ZMod p) := ⟨Nock.V1J8.FillX.colXE D.H D.pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j),
    Nock.V1J8.FillX.colXE D.H D.pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j), fun _ => 0, fun _ => 0⟩ with he'
  have hT : e0.trace = e'.trace := by
    funext c
    show HonestTraceX.baseT D.H D.pd W j c =
      Nock.V1J8.FillX.colXE D.H D.pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j) c
    rw [Nock.V1J8.FillX.colXE_eq]; rfl
  have hin : InTree t (W[j]'hj) :=
    Nock.NockVMROM.Thm54.TraceGen.inTree_of_mem_bfsForest_singleton (List.getElem_mem hj)
  have hrow : rr = rowOfSkelX (W[j]'hj).label := by
    simp [hrr, HonestWalkX.rowAtWX, List.getElem?_eq_getElem hj]
  have hok : HonestCompX.RowOKX p rr := by rw [hrow]; exact HonestRowX.rowOKX_of_genX hgen hin (hsm _ hin)
  have hs3 : rr.st = .s3 → rr.sf1.isCell = true → rr.sf1 = .cell rr.ftth rr.fttt := by
    rw [hrow]; exact rowOfSkelX_s3 _
  have hrowm : rr ∈ D.rows.toList := by
    rw [hrow]
    simp only [hD, j8DataGen, ComplJ8Data.rowsOfT, List.toList_toArray]
    exact List.mem_map_of_mem (List.getElem_mem hj)
  have hH := ComplJ8Data.hdlOK_hdlP p D.cells D.acs
  unfold xSum ComplJ8Data.xConsumesP
  rw [wsum_flatMap, ← TeleCQX.slotsX_cast (F := ZMod p), List.map_map]
  refine congrArg List.sum (List.map_congr_left fun S hS => ?_)
  have hS' : castSlotX (F := ZMod p) S ∈ ChipHX.slotsX (F := ZMod p) := by
    rw [← TeleCQX.slotsX_cast]; exact List.mem_map_of_mem hS
  simp only [Function.comp_apply]
  rw [show (castSlotX (F := ZMod p) S).ents = S.ents.map castEntX from rfl, List.filter_map, List.filterMap_map,
    wsum_filterMap]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  obtain ⟨hxS, hb⟩ := List.mem_filter.mp hx
  have hb' : x.bal = Bal.x := by simpa using hb
  have hmem : castEntX (F := ZMod p) x ∈ (castSlotX (F := ZMod p) S).ents := List.mem_map_of_mem hxS
  have hae : (castEntX (F := ZMod p) x).act.eval e' = ChipHX.evalQX x.act e0 := by
    rw [← TeleCQX.castEntX_act]
    refine HonestTraceX.eval_okC HonestTraceX.okFs _ (ComplJ8CompPole.hacts_slots _ hS' _ hmem) e' e0
      fun k i hk => ?_
    cases k <;> simp [HonestTraceX.okFs] at hk
    show e'.trace i = e0.trace i
    rw [hT]
  simp only [Function.comp_apply]
  rw [hae]
  by_cases ha : ChipHX.evalQX x.act e0 = 0
  · rw [ha]; simp
  have hne' : (castEntX (F := ZMod p) x).act.eval e' ≠ 0 := by rwa [hae]
  have hv0 : (ChipHX.evalQX x.act e0).val ≠ 0 := fun h => ha ((ZMod.val_eq_zero _).mp h)
  rw [if_neg hv0]
  obtain ⟨kP, kL, kR, hrc, hpar, h1, h2, h3⟩ :=
    xEnt_par D.H D.pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j) hok hH hs3 _ hS' _ hmem hb' hne'
  obtain ⟨k', tail, hr', hcell, hk, n, hn, hsub⟩ :=
    ComplJ8Data.xEnt_cell D.H D.pd rr _ _ hok hH _ hS' _ hmem hb' hne'
  have hrcd : (castEntX (F := ZMod p) x).rcd = x.rcd := rfl
  try rw [hrcd] at hr'
  try rw [hrcd] at hrc
  rw [hrc] at hr'
  have hkk : k' = kP := by
    simp [cellRecX, ChipHX.recOf, ChipH.cellRec, hdX] at hr'; omega
  subst hkk
  have hcm : HonestCompX.hN rr k' ∈ D.cells :=
    mem_cells_of_subsG p Rg Rt hgen O (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, hrowm, hn⟩))) _ hsub
  rw [hpar] at hcm
  set L := HonestCompX.hN rr kL with hL
  set R := HonestCompX.hN rr kR with hR
  have hjl := List.idxOf_lt_length_of_mem hcm
  obtain ⟨x1, y1, hxy, hxL, hxR⟩ := cells_kidsG Rt hgen O _ hcm
  simp only [Noun.cell.injEq] at hxy
  obtain ⟨rfl, rfl⟩ := hxy
  have tr : ∀ c, e0.trace c = HonestCompX.colX D.H D.pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j) c :=
    fun c => rfl
  have tP : e0.trace (hdX k').v = ((D.cells.idxOf (Noun.cell L R) : ℕ) : ZMod p) := by
    rw [tr, show (hdX k').v = 26 + 2 * k' from rfl, HonestCompX.colX_v _ _ _ _ _ _ h1, hpar]
    show (((ComplJ8Data.hdlP p D.cells D.acs (Noun.cell L R)).2 : ℕ) : ZMod p) = _
    simp only [ComplJ8Data.hdlP]
    rw [ComplJ8OfBal.genIdxOf_eq _ _ hcm]
  have tP' : e'.trace (hdX k').v = ((D.cells.idxOf (Noun.cell L R) : ℕ) : ZMod p) := by rw [← hT]; exact tP
  have hval : (e'.trace (hdX k').v).val = D.cells.idxOf (Noun.cell L R) := by
    rw [tP', ZMod.val_natCast, Nat.mod_eq_of_lt (hjl.trans hlen)]
  rw [hrcd, hrc]
  simp only [cellRecX, ChipHX.recOf, ChipH.cellRec, List.map_cons]
  rw [hval]
  simp only [GC]
  rw [cellHx_eq δ b D (cells_posG Rt hgen O) o hinjC χ rfl _ hjl (List.getElem_idxOf hjl) hxL hxR,
    ComplJ8CompPole.den_split δ b e0 χ rfl _ (by simp),
    ← map_natCast (algebraMap (ZMod p) 𝕂′), ZMod.natCast_zmod_val]
  congr 2
  have t1 : e0.trace (hdX kL).k = (((D.H L).1 : ℕ) : ZMod p) := by
    rw [tr, show (hdX kL).k = 25 + 2 * kL from rfl, HonestCompX.colX_k _ _ _ _ _ _ h2]; rfl
  have t2 : e0.trace (hdX kL).v = (((D.H L).2 : ℕ) : ZMod p) := by
    rw [tr, show (hdX kL).v = 26 + 2 * kL from rfl, HonestCompX.colX_v _ _ _ _ _ _ h2]; rfl
  have t3 : e0.trace (hdX kR).k = (((D.H R).1 : ℕ) : ZMod p) := by
    rw [tr, show (hdX kR).k = 25 + 2 * kR from rfl, HonestCompX.colX_k _ _ _ _ _ _ h3]; rfl
  have t4 : e0.trace (hdX kR).v = (((D.H R).2 : ℕ) : ZMod p) := by
    rw [tr, show (hdX kR).v = 26 + 2 * kR from rfl, HonestCompX.colX_v _ _ _ _ _ _ h3]; rfl
  simp only [FiniteIO.compress, Walk.rlc, Fin.sum_univ_eight, BalanceQ.liftRec, DenXJ8.keyX, DenXJ8.keyXN, recDen]
  simp [ChipHX.RE.ev, tP, t1, t2, t3, t4, IsScalarTower.algebraMap_apply (ZMod p) K 𝕂′]

end XRun
section HC
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
/-- The run's compute base columns are the honest stage-1 columns of the BFS rows. -/
theorem bases_getDG (j : ℕ) (hj : j < (bfsForest [t]).length) :
    (j8DataGen p Rg Rt hgen O).bases.getD j (fun _ => 0) =
      Nock.V1J8.FillX.colXE (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd
        (HonestWalkX.rowAtWX (bfsForest [t]) (j + 1)) (HonestTraceX.flX j) (HonestTraceX.llX (bfsForest [t]) j) := by
  have hl : j < (j8DataGen p Rg Rt hgen O).bases.length := by
    simp [j8DataGen, ComplJ8Data.basesP, ComplJ8Data.rowsOfT, hj]
  rw [List.getD_eq_getElem _ _ hl]
  simp only [j8DataGen, ComplJ8Data.basesP, List.getElem_map, List.getElem_zipIdx]
  funext c
  have hrow : HonestWalkX.rowAtWX (bfsForest [t]) (j + 1) = rowOfSkelX ((bfsForest [t])[j]'hj).label := by
    simp [HonestWalkX.rowAtWX, List.getElem?_eq_getElem hj]
  rw [hrow]
  simp only [ComplJ8Data.rowsOfT, List.toList_toArray, List.getElem_map, zero_add, List.size_toArray,
    List.length_map]
  congr 1
  · by_cases h0 : j = 0 <;> simp [ComplJ8Data.flagP, HonestTraceX.flX, h0]
  · by_cases h0 : j + 1 = (bfsForest [t]).length <;> simp [ComplJ8Data.flagP, HonestTraceX.llX, h0]

set_option maxHeartbeats 1000000 in
/-- **`hC`**: `ρ 3 = Σ_{compute export consumes} mult · 1/(ρH + cellHx serial)` at the run, at every coin, under the
run's small-atom bounds `hsm` (`smallX_of_binders`) and `|cells| < p`. -/
theorem hC_runG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hsm : ∀ u, InTree t u → HonestRowX.SmallX p (rowOfSkelX u.label))
    (hlen : (j8DataGen p Rg Rt hgen O).cells.length < p) (χ : Coins frameJ8 K) :
    ((BRunG δ b Rt hgen O o).M χ).ρ 3 =
      wsum (GC δ b (j8DataGen p Rg Rt hgen O) (cells_posG Rt hgen O) o χ)
        ((j8DataGen p Rg Rt hgen O).bases.flatMap fun bs =>
          ComplJ8Data.xConsumesP p (⟨bs, bs, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))) := by
  revert o
  set D := j8DataGen p Rg Rt hgen O with hD
  intro o
  have hmC : D.cells.length ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjC := (powN_ok o (le_two_pow_ht D hmC)).1
  show ComplJ8Comp.ρCOf δ b D.H D.pd (bfsForest [t]) (ComplJ8.cJ s f r) χ 3 = _
  rw [rhoC3_rows, wsum_flatMap, ← ComplJ8OfBal.sum_range_getD' (fun _ => 0)]
  have hlb : D.bases.length = (bfsForest [t]).length := by
    simp [hD, j8DataGen, ComplJ8Data.basesP, ComplJ8Data.rowsOfT]
  rw [hlb]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [termQX_x, xSum_runG δ b Rt hgen O hsm hlen o hinjC χ _ j hj', bases_getDG Rt hgen O j hj']

end HC
section Clause1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK ProgOp5OK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
set_option maxHeartbeats 1000000 in
/-- **`balG` clause 1 at the run, at every coin**, from the run binders `hax hop5`, the registry binder `hRt`,
the row binder `h31`, the walk-depth binder `hwalk` and the J sibling binder `hsib` (`JSibOK`). -/
theorem balG1_runG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataGen p Rg Rt hgen O).reads)
    (χ : Coins frameJ8 K) :
    ((BRunG δ b Rt hgen O o).M χ).ρ 3 +
        (Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsW WalkHQ.pubXQ)
          (((BRunG δ b Rt hgen O o).M χ).pubsW (WalkHQ.pubXQ + 1)) +
        Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsJ 2) (((BRunG δ b Rt hgen O o).M χ).pubsJ 3)) =
      Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsC CellHQ.pubHQ)
        (((BRunG δ b Rt hgen O o).M χ).pubsC (CellHQ.pubHQ + 1)) := by
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have hlen : (j8DataGen p Rg Rt hgen O).cells.length < p := size_lt_pG Rt hgen O hp63 h31 (by simp [sizesJ8])
  revert o
  set D := j8DataGen p Rg Rt hgen O with hD
  intro o
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hsm := ComplJ8.smallX_of_binders hax hop5
  have hkN : ∀ x ∈ D.jrows, (x.pre.kd = .rp ∨ x.pre.kd = .sl ∨ x.pre.kd = .sr) → x.w.kN = 1 :=
    fun x hx => (Nock.Jet.ChipJ8.gate_facts x (jrows_gate_runG Rt hgen O hp0 hRt x hx)).2.2.2
  have hcalls : ∀ cl ∈ D.calls, (Rt cl.1).WellTyped p ∧ ∃ r, (Rt cl.1).sem p cl.2 = some r :=
    ComplJ8Jet.calls_of_hregC hgen Rt hRt
  have hmC : D.cells.length ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjC := (powN_ok o (le_two_pow_ht D hmC)).1
  exact balG1_ofG δ b Rt hgen O o hpG h31 hwalk
    (xRecs_rangeG p Rg Rt hgen O hsm hlen (jReads_rangeG p Rg Rt hgen O hlen hkN)) χ
    (hC_runG δ b Rt hgen O o hpG h31 hsm hlen χ) (hJ_exportG δ b Rt hgen O o hinjC χ hcalls hlen hkN)

end Clause1
section WalkP
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
section WalkRun
variable [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
set_option maxHeartbeats 1000000 in
/-- **The J-8 walk handle provide is the walk rows' provided total at the path weight `Wp`.** -/
theorem whP_eqG {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjW : Function.Injective (powN o (walkRows (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).reads).length))
    (χ : Coins frameJ8 K) (hlen : (j8DataGen p Rg Rt hgen O).cells.length < p)
    (hpre : ∀ u ∈ walkRows (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).reads,
      2 * axisFold u.label.bits + 1 < p) :
    whP δ b (j8DataGen p Rg Rt hgen O) o χ =
      ((walkRows (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).reads).map fun u =>
        provH (Wp δ (j8DataGen p Rg Rt hgen O) χ) (j8DataGen p Rg Rt hgen O).cells u.label).sum := by
  set D := j8DataGen p Rg Rt hgen O with hD
  have hwcell := walkRows_node_cellsG (p := p) Rt hgen O
  unfold whP
  rw [← ComplJ8OfBal.sum_range_getD' (trie (.atom 0) (.atom 0) [] [])
    (fun u => provH (Wp δ D χ) D.cells u.label)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [show (walkRows D.cells D.reads).getD k (trie (.atom 0) (.atom 0) [] []) = wTrie D.cells D.reads k from rfl]
  obtain ⟨-, eL, eR⟩ := walk_dRow_split δ b D o hinjW χ (pubsW0 δ D χ) ⟨k, hk'⟩
  simp only [wdN, WalkTraceHQ.dN, WalkTraceH.cN, dif_pos hk', eL, eR]
  have hu : wTrie D.cells D.reads k ∈ walkRows D.cells D.reads := wTrie_mem _ _ hk'
  obtain ⟨hch, hroot⟩ := walk_row_chain D.cells D.reads hwcell _ hu
  obtain ⟨l, rr, hlr, -, -⟩ := cells_kidsG Rt hgen O _ (hwcell _ hu)
  have hp2 := hpre _ hu
  set w := (wTrie D.cells D.reads k).label with hw
  have hgw : (D.reads.length = D.reads.length) := rfl
  have hmL : wCol δ b D χ WChip.mL ⟨k, hk'⟩ = ((w.mL : ℕ) : ZMod p) := rfl
  have hmR : wCol δ b D χ WChip.mR ⟨k, hk'⟩ = ((w.mR : ℕ) : ZMod p) := rfl
  rw [hmL, hmR]
  have hsL : Noun.slot (2 * axisFold w.bits) w.root = some l := by
    rw [show 2 * axisFold w.bits = axisFold (w.bits ++ [false]) by rw [axisFold_append]; simp, chain_slot,
      chainWalk_append, hch, hlr]
    rfl
  have hsR : Noun.slot (2 * axisFold w.bits + 1) w.root = some rr := by
    rw [show 2 * axisFold w.bits + 1 = axisFold (w.bits ++ [true]) by rw [axisFold_append]; simp, chain_slot,
      chainWalk_append, hch, hlr]
    rfl
  have eWL : Wp δ D χ (recLH D.cells w) = (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ)
      (((D.cells.idxOf w.root : ℕ) : ZMod p), ((2 * axisFold w.bits : ℕ) : ZMod p),
        ((((D.H l).1 : ℕ) : ZMod p), (((D.H l).2 : ℕ) : ZMod p))))⁻¹ := by
    rw [recLH, Wp_third δ D χ _ _ _ (0, 0)]
    exact Wp_eq δ D χ w.root l _ _ hroot rfl hlen (by omega) hsL
  have eWR : Wp δ D χ (recRH D.cells w) = (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ)
      (((D.cells.idxOf w.root : ℕ) : ZMod p), ((2 * axisFold w.bits + 1 : ℕ) : ZMod p),
        ((((D.H rr).1 : ℕ) : ZMod p), (((D.H rr).2 : ℕ) : ZMod p))))⁻¹ := by
    rw [recRH, Wp_third δ D χ _ _ _ (0, 0)]
    exact Wp_eq δ D χ w.root rr _ _ hroot rfl hlen hp2 hsR
  rw [provH, nsmul_eq_mul, nsmul_eq_mul, eWL, eWR]
  have hkl : kLW D ⟨k, hk'⟩ = (((D.H l).1 : ℕ) : ZMod p) ∧ vLW D ⟨k, hk'⟩ = (((D.H l).2 : ℕ) : ZMod p) ∧
      kRW D ⟨k, hk'⟩ = (((D.H rr).1 : ℕ) : ZMod p) ∧ vRW D ⟨k, hk'⟩ = (((D.H rr).2 : ℕ) : ZMod p) := by
    simp only [kLW, vLW, kRW, vRW, wNode, ← hw, hlr]
    exact ⟨rfl, rfl, rfl, rfl⟩
  rw [hkl.1, hkl.2.1, hkl.2.2.1, hkl.2.2.2]
  have hri : (wValsC δ D χ ⟨k, hk'⟩).ridx = ((D.cells.idxOf w.root : ℕ) : ZMod p) := rfl
  have hpr : (wValsC δ D χ ⟨k, hk'⟩).pre = ((axisFold w.bits : ℕ) : ZMod p) := rfl
  rw [hri, hpr]
  push_cast
  simp [liftQ, map_natCast]

end WalkRun
section PRun
variable [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
/-- The run's reads are its rows' walk entries (the `2 ≤ axis` filter is vacuous). -/
theorem reads_eqG :
    (j8DataGen p Rg Rt hgen O).reads.Perm
      ((bfsForest [t]).flatMap fun u => (consEntriesX (rowOfSkelX u.label)).map fun x => (x.1, x.2.1)) := by
  refine (O.permR _ _).trans (List.Perm.of_eq ?_)
  have hrows : (j8DataGen p Rg Rt hgen O).rows.toList = (bfsForest [t]).map fun u => rowOfSkelX u.label := by
    show (ComplJ8Data.rowsOfT t).toList = _
    simp [ComplJ8Data.rowsOfT]
  show Nock.V1J8.Gen.pathReads (j8DataGen p Rg Rt hgen O).rows = _
  unfold Nock.V1J8.Gen.pathReads
  rw [hrows, List.flatMap_map]
  refine List.filter_eq_self.mpr fun x hx => ?_
  obtain ⟨u, hu, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp hu
  rw [List.mem_singleton] at hc; subst hc
  simpa using (consEntriesX_sound u.label (inTree_rowSem hgen hin) e he).1

set_option maxHeartbeats 2000000 in
/-- **The `.p` reciprocal sum of run row `j` is the path weight total of the row's walk entries.** -/
theorem pSum_runG (hsm : ∀ u, InTree t u → HonestRowX.SmallX p (rowOfSkelX u.label))
    (hlen : (j8DataGen p Rg Rt hgen O).cells.length < p) (hp62 : 2 ^ 62 < p)
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataGen p Rg Rt hgen O).reads) (χ : Coins frameJ8 K)
    (pubVal : ℕ → ZMod p) (j : ℕ) (hj : j < (bfsForest [t]).length) :
    pSum δ b (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      ((consEntriesX (rowOfSkelX ((bfsForest [t])[j]'hj).label)).map fun x =>
        Wp δ (j8DataGen p Rg Rt hgen O) χ (readRecH (j8DataGen p Rg Rt hgen O).cells (x.1, x.2.1))).sum := by
  set D := j8DataGen p Rg Rt hgen O with hD
  set W := bfsForest [t] with hW
  have hin : InTree t (W[j]'hj) :=
    Nock.NockVMROM.Thm54.TraceGen.inTree_of_mem_bfsForest_singleton (List.getElem_mem hj)
  have hrow : HonestWalkX.rowAtWX W (j + 1) = rowOfSkelX (W[j]'hj).label := by
    simp [HonestWalkX.rowAtWX, List.getElem?_eq_getElem hj]
  have hok : HonestCompX.RowOKX p (rowOfSkelX (W[j]'hj).label) := HonestRowX.rowOKX_of_genX hgen hin (hsm _ hin)
  have hrowm : rowOfSkelX (W[j]'hj).label ∈ D.rows.toList := by
    simp only [hD, j8DataGen, ComplJ8Data.rowsOfT, List.toList_toArray]
    exact List.mem_map_of_mem (List.getElem_mem hj)
  have hH := ComplJ8Data.hdlOK_hdlP p D.cells D.acs
  rw [pSum_expand]
  have htr : (HonestTraceX.env0 D.H D.pd W (VerJ8.chalVJ8 b χ) pubVal j).trace =
      HonestCompX.colX D.H D.pd (rowOfSkelX (W[j]'hj).label) (HonestTraceX.flX j) (HonestTraceX.llX W j) := by
    funext c
    show HonestTraceX.baseT D.H D.pd W j c = _
    unfold HonestTraceX.baseT; rw [hrow]
  rw [htr, pRow_row δ D.H D.pd χ _ _ _ hok hH]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  obtain ⟨h2, hsl⟩ := consEntriesX_sound _ (inTree_rowSem hgen hin) x hx
  have hroot := consEntriesX_root _ x hx
  have hcell : x.1 ∈ D.cells ∧ ∃ a c, x.1 = .cell a c := by
    rcases handle_noun_casesG p Rg Rt hgen O hrowm hroot with ⟨⟨a, c, hac⟩, hm⟩ | ⟨v, ev, _⟩ | ⟨v, ev, _⟩
    · exact ⟨hm, a, c, hac⟩
    · rw [ev, slot_atom_two h2] at hsl; cases hsl
    · rw [ev, slot_atom_two h2] at hsl; cases hsl
  obtain ⟨hmem, a, c, hac⟩ := hcell
  have hread : (x.1, x.2.1) ∈ D.reads := by
    apply (reads_eqG Rt hgen O).mem_iff.mpr
    exact List.mem_flatMap.mpr ⟨_, List.getElem_mem hj, List.mem_map_of_mem hx⟩
  have hpr : (x.1, x.2.1) ∈ VclL.pathReads D.reads := by
    unfold VclL.pathReads
    exact List.mem_dedup.mpr (List.mem_filter.mpr ⟨hread, ComplJ8OfBal.isPathAx_of_two_le h2⟩)
  have hax : x.2.1 < p := (ax_lt_of_depth (by omega) (hwalk _ hpr)).trans hp62
  have hidx : ((D.H x.1).2 : ℕ) = D.cells.idxOf x.1 := by
    show (ComplJ8Data.hdlP p D.cells D.acs x.1).2 = _
    rw [hac]
    simp only [ComplJ8Data.hdlP]
    rw [← hac, ComplJ8OfBal.genIdxOf_eq _ _ hmem]
  unfold Tc readRecH
  rw [Wp_third δ D χ _ _ _ (0, 0), Wp_eq δ D χ x.1 x.2.2 _ _ hmem rfl hlen hax hsl, hidx]

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK ProgOp5OK) in
set_option maxHeartbeats 2000000 in
/-- **`balG` clause 2 at the run, at every good coin**: the compute path public `ρ 4` is the J-8 walk's handle
provide `whP`, from the run binders `hax hop5`, the row binder `h31` and the walk-depth binder `hwalk`. -/
theorem balG2_runG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataGen p Rg Rt hgen O).reads) (χ : Coins frameJ8 K)
    (hχ : (BRunG δ b Rt hgen O o).Good χ) :
    ((BRunG δ b Rt hgen O o).M χ).ρ 4 =
      Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsW WalkHQ.pubPQ)
        (((BRunG δ b Rt hgen O o).M χ).pubsW (WalkHQ.pubPQ + 1)) := by
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have hp62 : 2 ^ 62 < p := lt_trans (by norm_num) hp63
  have hlen : (j8DataGen p Rg Rt hgen O).cells.length < p := size_lt_pG Rt hgen O hp63 h31 (by simp [sizesJ8])
  have hg0 : ∀ e ∈ ComplJ8Bad.badOf (ComplJ8Bad.badList [(⟨13, by decide⟩, (bfsForest [(j8DataGen p Rg Rt hgen O).t]).length)]
      (famsOfO δ b (j8DataGen p Rg Rt hgen O) o (cells_posG Rt hgen O))), χ ∉ e.1 := hχ
  revert o
  set D := j8DataGen p Rg Rt hgen O with hD
  intro o hχ hg0
  have hsm := ComplJ8.smallX_of_binders hax hop5
  have hmW : (walkRows D.cells D.reads).length ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjW := (powN_ok o (le_two_pow_ht D hmW)).1
  have hg : ∀ e ∈ ComplJ8CompPole.compPoles (K := K) δ D.H D.pd (bfsForest [t]) (bfsForest [t]).length,
      χ ∉ e.ev := fun e he =>
    ComplJ8Bad.good_spec hg0 (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_cons_self, he⟩))
  -- the walk side
  have eW : Quad.mk (algebraMap (ZMod p) K δ) (((BRunG δ b Rt hgen O o).M χ).pubsW WalkHQ.pubPQ)
      (((BRunG δ b Rt hgen O o).M χ).pubsW (WalkHQ.pubPQ + 1)) = whP δ b D o χ := by
    show Quad.mk _ (pubsWOf δ b D o χ WalkHQ.pubPQ) (pubsWOf δ b D o χ (WalkHQ.pubPQ + 1)) = _
    have h6 : pubsWOf δ b D o χ WalkHQ.pubPQ = pub2 δ (whP δ b D o χ) 6 := by simp [pubsWOf, WalkHQ.pubPQ]
    have h7 : pubsWOf δ b D o χ (WalkHQ.pubPQ + 1) = pub2 δ (whP δ b D o χ) 7 := by simp [pubsWOf, WalkHQ.pubPQ]
    rw [h6, h7, pub2_mk2 δ _ 6 rfl]
  rw [eW]
  have hpre : ∀ u ∈ walkRows D.cells D.reads, 2 * axisFold u.label.bits + 1 < p := by
    intro u hu
    have h60 := ComplJ8Walk.walkRows_len_le60 hwalk hu
    have h1 := axisFold_lt u.label.bits
    have h2 : 2 ^ (u.label.bits.length + 1) ≤ 2 ^ 61 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 62 = 2 * 2 ^ 61 := by norm_num
    omega
  have hall : ∀ x ∈ D.reads, VclL.isPathAx x.2 = true := by
    intro x hx
    have hx := (O.permR _ _).mem_iff.mp hx
    unfold Nock.V1J8.Gen.pathReads at hx
    exact ComplJ8OfBal.isPathAx_of_two_le (by simpa using (List.mem_filter.mp hx).2)
  have hslot : ∀ x ∈ VclL.pathReads D.reads, (Noun.slot x.2 x.1).isSome := fun x hx =>
    reads_slotG Rt hgen O x (List.mem_filter.mp (List.mem_dedup.mp hx)).1
  rw [whP_eqG δ b Rt hgen O o hinjW χ hlen hpre, walk_provide_total (Wp δ D χ) D.cells D.reads hslot (fun _ => rfl),
    ComplJ8OfBal.pathKind_of_all hall]
  -- the compute side
  show ComplJ8Comp.ρCOf δ b D.H D.pd (bfsForest [t]) (ComplJ8.cJ s f r) χ 4 = _
  rw [rhoC4_rows]
  set g : NTree SkelX → 𝕂′ := fun u => ((consEntriesX (rowOfSkelX u.label)).map fun x =>
    Wp δ D χ (readRecH D.cells (x.1, x.2.1))).sum with hgdef
  have hrow : ∀ j ∈ Finset.range (bfsForest [t]).length,
      TeleCQX.termQX δ b (envC δ b D.H D.pd (bfsForest [t]) (ComplJ8.cJ s f r) χ j) .p =
        g ((bfsForest [t]).getD j t) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [termQX_p δ b _ _ _ _ _ j (hpair_good δ b _ _ _ _ _ χ hg j hj'), pSum_runG δ b Rt hgen O hsm hlen hp62 hwalk χ _ j hj',
      List.getD_eq_getElem _ _ hj']
  rw [Finset.sum_congr rfl hrow, ComplJ8OfBal.sum_range_getD' t g,
    (List.Perm.map _ (reads_eqG Rt hgen O)).sum_eq, ComplJ8OfBalG.sum_flatMap_map]
  simp only [hgdef, List.map_map, Function.comp_def]

end PRun
end WalkP
section Clause3
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK ProgOp5OK)
open Nock.Jet.PinJ8 (pinCons)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.FiniteIO (compress)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
/-- The compute row environment's publics at the run (as `envC`). -/
abbrev pubCG (χ : Coins frameJ8 K) : ℕ → ZMod p :=
  VerJ8.pubVJ8 δ b (ComplJ8.cJ s f r) (ComplJ8Comp.mCOf (j8DataGen p Rg Rt hgen O).H (ComplJ8.cJ s f r)) 0 0 χ

set_option maxHeartbeats 2000000 in
/-- **`balG` clause 3 at the run, at every good coin, from its three sub-balances**: the compute service public
`ρS` splits row by row into the inc consumes (`incT`), the jet consumes (`jetT`) and the atom-walk pair consumes
(`awT`); the clause holds once the inc consumes total the atom MI terminal (`hI`), the pair consumes total the atom
walk's handle provide (`hA`), and the jet consumes, the registry pins and the J terminal sum to zero (`hJ`). -/
theorem balG3_ofG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) (χ : Coins frameJ8 K)
    (hχ : (BRunG δ b Rt hgen O o).Good χ)
    (hI : ∑ j ∈ Finset.range (bfsForest [t]).length, incT δ b (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubCG δ b Rt hgen O χ) j =
      Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsA AtomChipHQ.pubMI)
        (((BRunG δ b Rt hgen O o).M χ).pubsA (AtomChipHQ.pubMI + 1)))
    (hA : ∑ j ∈ Finset.range (bfsForest [t]).length, awT δ b (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubCG δ b Rt hgen O χ) j =
      Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsV WalkHQ.pubPQ)
        (((BRunG δ b Rt hgen O o).M χ).pubsV (WalkHQ.pubPQ + 1)))
    (hJ : ∑ j ∈ Finset.range (bfsForest [t]).length, jetT δ b (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubCG δ b Rt hgen O χ) j +
      ((pinCons (p := p) (K := K) (BRunG δ b Rt hgen O o).Pb.regs (BRunG δ b Rt hgen O o).Pb.idx).map fun x =>
        (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsJ 0) (((BRunG δ b Rt hgen O o).M χ).pubsJ 1) = 0) :
    ((BRunG δ b Rt hgen O o).M χ).ρS +
        ((pinCons (p := p) (K := K) (BRunG δ b Rt hgen O o).Pb.regs (BRunG δ b Rt hgen O o).Pb.idx).map fun x =>
          (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
        Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsJ 0) (((BRunG δ b Rt hgen O o).M χ).pubsJ 1) =
      Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsA AtomChipHQ.pubMI)
          (((BRunG δ b Rt hgen O o).M χ).pubsA (AtomChipHQ.pubMI + 1)) +
        Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsV WalkHQ.pubPQ)
          (((BRunG δ b Rt hgen O o).M χ).pubsV (WalkHQ.pubPQ + 1)) := by
  have hg0 : ∀ e ∈ ComplJ8Bad.badOf (ComplJ8Bad.badList [(⟨13, by decide⟩, (bfsForest [(j8DataGen p Rg Rt hgen O).t]).length)]
      (famsOfO δ b (j8DataGen p Rg Rt hgen O) o (cells_posG Rt hgen O))), χ ∉ e.1 := hχ
  revert o
  set D := j8DataGen p Rg Rt hgen O with hD
  intro o hχ hI hA hJ hg0
  have hg : ∀ e ∈ ComplJ8CompPole.compPoles (K := K) δ D.H D.pd (bfsForest [t]) (bfsForest [t]).length,
      χ ∉ e.ev := fun e he =>
    ComplJ8Bad.good_spec hg0 (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_cons_self, he⟩))
  have hS : ((BRunG δ b Rt hgen O o).M χ).ρS =
      ∑ j ∈ Finset.range (bfsForest [t]).length, (incT δ b D.H D.pd (bfsForest [t]) (VerJ8.chalVJ8 b χ)
        (pubCG δ b Rt hgen O χ) j + jetT δ b D.H D.pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubCG δ b Rt hgen O χ) j +
        awT δ b D.H D.pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubCG δ b Rt hgen O χ) j) := by
    show ComplJ8Comp.ρSCOf δ b D.H D.pd (bfsForest [t]) (ComplJ8.cJ s f r) χ = _
    rw [rhoCS_rows]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [termQX_s δ b _ _ _ _ _ j (hpair_good δ b _ _ _ _ _ χ hg j (Finset.mem_range.mp hj)), sSum_expand]
  rw [hS, Finset.sum_add_distrib, Finset.sum_add_distrib]
  linear_combination hI + hA + hJ

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds) in
set_option maxHeartbeats 2000000 in
/-- **`OpenJ8.balG` at the run**: clauses 1 and 2 from the binders `hax hop5 hRt h31 hwalk`; clause 3 from
its three sub-balances `hI hA hJ` (carried, exact statements as in `balG3_ofG`). -/
theorem balG_closedG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataGen p Rg Rt hgen O).reads)
    (hI : ∀ χ, (BRunG δ b Rt hgen O o).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, incT δ b (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubCG δ b Rt hgen O χ) j =
      Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsA AtomChipHQ.pubMI)
        (((BRunG δ b Rt hgen O o).M χ).pubsA (AtomChipHQ.pubMI + 1)))
    (hA : ∀ χ, (BRunG δ b Rt hgen O o).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, awT δ b (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubCG δ b Rt hgen O χ) j =
      Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsV WalkHQ.pubPQ)
        (((BRunG δ b Rt hgen O o).M χ).pubsV (WalkHQ.pubPQ + 1)))
    (hJ : ∀ χ, (BRunG δ b Rt hgen O o).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, jetT δ b (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubCG δ b Rt hgen O χ) j +
      ((pinCons (p := p) (K := K) (BRunG δ b Rt hgen O o).Pb.regs (BRunG δ b Rt hgen O o).Pb.idx).map fun x =>
        (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsJ 0) (((BRunG δ b Rt hgen O o).M χ).pubsJ 1) = 0) :
    ∀ χ, (BRunG δ b Rt hgen O o).Good χ →
      ((BRunG δ b Rt hgen O o).M χ).ρ 3 +
          (Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsW WalkHQ.pubXQ)
            (((BRunG δ b Rt hgen O o).M χ).pubsW (WalkHQ.pubXQ + 1)) +
          Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsJ 2) (((BRunG δ b Rt hgen O o).M χ).pubsJ 3)) =
        Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsC CellHQ.pubHQ)
          (((BRunG δ b Rt hgen O o).M χ).pubsC (CellHQ.pubHQ + 1)) ∧
      ((BRunG δ b Rt hgen O o).M χ).ρ 4 =
        Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsW WalkHQ.pubPQ)
          (((BRunG δ b Rt hgen O o).M χ).pubsW (WalkHQ.pubPQ + 1)) ∧
      ((BRunG δ b Rt hgen O o).M χ).ρS +
          ((pinCons (p := p) (K := K) (BRunG δ b Rt hgen O o).Pb.regs (BRunG δ b Rt hgen O o).Pb.idx).map
            fun x => (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
          Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsJ 0) (((BRunG δ b Rt hgen O o).M χ).pubsJ 1) =
        Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsA AtomChipHQ.pubMI)
            (((BRunG δ b Rt hgen O o).M χ).pubsA (AtomChipHQ.pubMI + 1)) +
          Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsV WalkHQ.pubPQ)
            (((BRunG δ b Rt hgen O o).M χ).pubsV (WalkHQ.pubPQ + 1)) := fun χ hχ =>
  ⟨balG1_runG δ b Rt hgen O o hpG hax hop5 hRt h31 hwalk χ,
   balG2_runG δ b Rt hgen O o hpG hax hop5 h31 hwalk χ hχ,
   balG3_ofG δ b Rt hgen O o hpG h31 χ hχ (hI χ hχ) (hA χ hχ) (hJ χ hχ)⟩

end Clause3
section AW
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
section AWRun
variable [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
set_option maxHeartbeats 1000000 in
/-- **The atom walk's handle provide is its rows' provided total at `WvA`** (a read present). -/
theorem vhP_eqG {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (hne : (j8DataGen p Rg Rt hgen O).preads ≠ [])
    (hinjV : Function.Injective (powN o (nVOf (j8DataGen p Rg Rt hgen O))))
    (χ : Coins frameJ8 K) (hlen : (j8DataGen p Rg Rt hgen O).acs.length < p)
    (hwn : ∀ u ∈ walkRows (j8DataGen p Rg Rt hgen O).acs (j8DataGen p Rg Rt hgen O).preads,
      u.label.node ∈ (j8DataGen p Rg Rt hgen O).acs)
    (hcl : ∀ c ∈ (j8DataGen p Rg Rt hgen O).acs, c.isCell = true)
    (hpre : ∀ u ∈ walkRows (j8DataGen p Rg Rt hgen O).acs (j8DataGen p Rg Rt hgen O).preads,
      2 * axisFold u.label.bits + 1 < p) :
    vhP δ b (j8DataGen p Rg Rt hgen O) o χ =
      ((walkRows (j8DataGen p Rg Rt hgen O).acs (j8DataGen p Rg Rt hgen O).preads).map fun u =>
        provH (WvA δ (j8DataGen p Rg Rt hgen O) χ) (j8DataGen p Rg Rt hgen O).acs u.label).sum := by
  set D := j8DataGen p Rg Rt hgen O with hD
  have hn : nVOf D = (walkRows D.acs D.preads).length := by simp [nVOf, hne]
  unfold vhP
  rw [show Finset.range (nVOf D) = Finset.range (walkRows D.acs D.preads).length by rw [hn],
    ← ComplJ8OfBal.sum_range_getD' (trie (.atom 0) (.atom 0) [] [])
    (fun u => provH (WvA δ D χ) D.acs u.label)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have hkV : k < nVOf D := hn ▸ hk'
  rw [show (walkRows D.acs D.preads).getD k (trie (.atom 0) (.atom 0) [] []) = wTrie D.acs D.preads k from rfl]
  obtain ⟨-, eL, eR⟩ := ComplJ8OfAtom.aw_dRow_split δ b D o hinjV χ (pubsV0 δ D χ) ⟨k, hkV⟩
  simp only [vdN, WalkTraceHQ.dN, WalkTraceH.cN, dif_pos hkV]
  rw [show krVOf D = krW D.acs D.preads by simp [krVOf, hne], eL, eR]
  have hu : wTrie D.acs D.preads k ∈ walkRows D.acs D.preads := wTrie_mem _ _ hk'
  obtain ⟨hch, hroot⟩ := walk_row_chain D.acs D.preads hwn _ hu
  have hc := hcl _ (hwn _ hu)
  obtain ⟨l, rr, hlr⟩ : ∃ l rr, (wTrie D.acs D.preads k).label.node = .cell l rr := by
    cases h : (wTrie D.acs D.preads k).label.node with
    | atom v => rw [h] at hc; simp [Noun.isCell] at hc
    | cell l rr => exact ⟨l, rr, rfl⟩
  have hp2 := hpre _ hu
  set w := (wTrie D.acs D.preads k).label with hw
  have hmL : vCol δ b D χ WChip.mL ⟨k, hkV⟩ = ((w.mL : ℕ) : ZMod p) := rfl
  have hmR : vCol δ b D χ WChip.mR ⟨k, hkV⟩ = ((w.mR : ℕ) : ZMod p) := rfl
  rw [hmL, hmR]
  have hsL : Noun.slot (2 * axisFold w.bits) w.root = some l := by
    rw [show 2 * axisFold w.bits = axisFold (w.bits ++ [false]) by rw [axisFold_append]; simp, chain_slot,
      chainWalk_append, hch, hlr]
    rfl
  have hsR : Noun.slot (2 * axisFold w.bits + 1) w.root = some rr := by
    rw [show 2 * axisFold w.bits + 1 = axisFold (w.bits ++ [true]) by rw [axisFold_append]; simp, chain_slot,
      chainWalk_append, hch, hlr]
    rfl
  have eWL := WvA_eq δ D χ w.root l _ (2 * axisFold w.bits) hroot rfl hlen (by omega) hsL
    (hdl D.acs (hdN w.node))
  have eWR := WvA_eq δ D χ w.root rr _ (2 * axisFold w.bits + 1) hroot rfl hlen hp2 hsR
    (hdl D.acs (tlN w.node))
  rw [provH, nsmul_eq_mul, nsmul_eq_mul, recLH, recRH, eWL, eWR]
  have hkl : kLV D ⟨k, hkV⟩ = (((D.H l).1 : ℕ) : ZMod p) ∧ vLV D ⟨k, hkV⟩ = (((D.H l).2 : ℕ) : ZMod p) ∧
      kRV D ⟨k, hkV⟩ = (((D.H rr).1 : ℕ) : ZMod p) ∧ vRV D ⟨k, hkV⟩ = (((D.H rr).2 : ℕ) : ZMod p) := by
    simp only [kLV, vLV, kRV, vRV, vNode, ← hw, hlr]
    exact ⟨rfl, rfl, rfl, rfl⟩
  rw [hkl.1, hkl.2.1, hkl.2.2.1, hkl.2.2.2]
  have hri : (ComplJ8OfAtom.vValsC δ D χ ⟨k, hkV⟩).ridx = ((D.acs.idxOf w.root : ℕ) : ZMod p) := rfl
  have hpr : (ComplJ8OfAtom.vValsC δ D χ ⟨k, hkV⟩).pre = ((axisFold w.bits : ℕ) : ZMod p) := rfl
  rw [hri, hpr]
  push_cast
  simp [liftQ, map_natCast]

/-- **An honest op-5 pair row's two atom-walk reads**: both leaves are big atoms of the run with the two-limb
comb in `acs`, the first-difference axis is `2` or `3`, and the comb's slot there is the recorded small limb. -/
theorem pair_factsG (hpG : p = Nock.Atoms.p)
    (hbig : ∀ a ∈ (j8DataGen p Rg Rt hgen O).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1])
    {row : RowNX} (hrow : row ∈ (j8DataGen p Rg Rt hgen O).rows.toList)
    (hpair : HonestCompX.isPair (j8DataGen p Rg Rt hgen O).H row) :
    ∃ a c, row.ftth = .atom a ∧ row.fttt = .atom c ∧ a ∈ (j8DataGen p Rg Rt hgen O).bigs ∧
      c ∈ (j8DataGen p Rg Rt hgen O).bigs ∧
      ((j8DataGen p Rg Rt hgen O).pd row).1 < p ∧ ((j8DataGen p Rg Rt hgen O).pd row).2.1.1 = 0 ∧
      ((j8DataGen p Rg Rt hgen O).pd row).2.2.1 = 0 ∧ ((j8DataGen p Rg Rt hgen O).pd row).2.1.2 < p ∧
      ((j8DataGen p Rg Rt hgen O).pd row).2.2.2 < p ∧
      Noun.slot ((j8DataGen p Rg Rt hgen O).pd row).1 (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)) =
        some (.atom ((j8DataGen p Rg Rt hgen O).pd row).2.1.2) ∧
      Noun.slot ((j8DataGen p Rg Rt hgen O).pd row).1 (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs c)) =
        some (.atom ((j8DataGen p Rg Rt hgen O).pd row).2.2.2) := by
  set D := j8DataGen p Rg Rt hgen O with hD
  obtain ⟨-, -, h1, h2⟩ := hpair
  have hkind : ∀ n : Noun, n ∈ rowHandleNounsX row → (D.H n).1 = 2 →
      ∃ a, n = .atom a ∧ a ∈ D.bigs := by
    intro n hn hk
    have hH : D.H = ComplJ8Data.hdlP p D.cells D.acs := rfl
    rw [hH] at hk
    cases n with
    | cell l r' => simp [ComplJ8Data.hdlP] at hk
    | atom a =>
      have hpa : p ≤ a := by
        by_contra hlt
        simp [ComplJ8Data.hdlP, show a < p by omega] at hk
      refine ⟨a, rfl, ?_⟩
      show a ∈ ComplJ8Data.bigsP p D.roots D.rows
      refine (ComplJ8Atom.mem_bigsP p _ _ a).mpr ⟨?_, hpa⟩
      refine List.mem_flatMap.mpr ⟨.atom a, List.mem_append_right _ (List.mem_flatMap.mpr ⟨row, hrow, hn⟩), ?_⟩
      simp [leavesOf]
  obtain ⟨a, ha', ha⟩ := hkind row.ftth (by simp [rowHandleNounsX]) h1
  obtain ⟨c, hc', hc⟩ := hkind row.fttt (by simp [rowHandleNounsX]) h2
  have hB : Nock.Atoms.B - 1 < p := by rw [hpG]; simp [Nock.Atoms.B, Nock.Atoms.p, Nock.Field.p]
  have hp3 : 3 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have hxa : a + 1 - p < p := by
    have := HonestPairX.limbs_lt a (a + 1 - p) (by rw [(hbig a ha).2]; simp)
    omega
  have hxc : c + 1 - p < p := by
    have := HonestPairX.limbs_lt c (c + 1 - p) (by rw [(hbig c hc).2]; simp)
    omega
  have e : D.pd row = HonestPairX.pdX (ComplJ8Data.sxPP p D.acs D.rows) row := rfl
  refine ⟨a, c, ha', hc', ha, hc, ?_⟩
  rw [e]
  unfold HonestPairX.pdX
  rw [ha', hc']
  simp only [(hbig a ha).2, (hbig c hc).2, HonestPairX.combFD, Nock.V1J8.Gen.combOf]
  split_ifs <;> simp [Noun.slot]
  all_goals refine ⟨by omega, ?_⟩ <;> omega

set_option maxHeartbeats 2000000 in
/-- **Run row `j`'s atom-walk pair consume** is the `WvA` total of the row's atom-walk reads (`pairReadsP`). -/
theorem awT_runG (hpG : p = Nock.Atoms.p)
    (hbig : ∀ a ∈ (j8DataGen p Rg Rt hgen O).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1])
    (hrt : ∀ a, ComplJ8Data.rootIdxP p (j8DataGen p Rg Rt hgen O).acs a =
      Nock.V1J8.Gen.idxOf (j8DataGen p Rg Rt hgen O).acs (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)))
    (hix : ∀ n ∈ (j8DataGen p Rg Rt hgen O).acs, Nock.V1J8.Gen.idxOf (j8DataGen p Rg Rt hgen O).acs n =
      List.idxOf n (j8DataGen p Rg Rt hgen O).acs)
    (hlen : (j8DataGen p Rg Rt hgen O).acs.length < p) (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) (j : ℕ)
    (hj : j < (bfsForest [t]).length) :
    awT δ b (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      ((if Nock.V1J8.FillX.isPairB (j8DataGen p Rg Rt hgen O).H (rowOfSkelX ((bfsForest [t])[j]'hj).label) then
          [(Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (Nock.V1J8.Gen.atomV (rowOfSkelX ((bfsForest [t])[j]'hj).label).ftth)),
              ((j8DataGen p Rg Rt hgen O).pd (rowOfSkelX ((bfsForest [t])[j]'hj).label)).1),
           (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (Nock.V1J8.Gen.atomV (rowOfSkelX ((bfsForest [t])[j]'hj).label).fttt)),
              ((j8DataGen p Rg Rt hgen O).pd (rowOfSkelX ((bfsForest [t])[j]'hj).label)).1)]
        else []).map fun x => WvA δ (j8DataGen p Rg Rt hgen O) χ (readRecH (j8DataGen p Rg Rt hgen O).acs x)).sum := by
  set D := j8DataGen p Rg Rt hgen O with hD
  set W := bfsForest [t] with hW
  set rr := rowOfSkelX (W[j]'hj).label with hrr
  have hrow : HonestWalkX.rowAtWX W (j + 1) = rr := by
    simp [hrr, HonestWalkX.rowAtWX, List.getElem?_eq_getElem hj]
  have hrowm : rr ∈ D.rows.toList := by
    simp only [hrr, hD, j8DataGen, ComplJ8Data.rowsOfT, List.toList_toArray]
    exact List.mem_map_of_mem (List.getElem_mem hj)
  have hH : HonestCompX.HdlOK p D.H := ComplJ8Data.hdlOK_hdlP p D.cells D.acs
  have htr : (HonestTraceX.env0 D.H D.pd W (VerJ8.chalVJ8 b χ) pubVal j).trace =
      HonestCompX.colX D.H D.pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j) := by
    funext c
    show HonestTraceX.baseT D.H D.pd W j c = _
    unfold HonestTraceX.baseT; rw [hrow]
  unfold awT
  rw [DX_walkA δ b _ χ rfl, DX_walkA δ b _ χ rfl, htr]
  simp only [ChipHX.xFtth, ChipHX.xFttt, ChipHX.xL1, ChipHX.xL2, ChipHX.hdX, HonestCompX.cx64, HonestCompX.cx63,
    HonestCompX.cx65, HonestCompX.cx66, HonestCompX.cx67, HonestCompX.cx68]
  rw [show (26 + 2 * 9 : ℕ) = 44 from rfl, show (26 + 2 * 10 : ℕ) = 46 from rfl, HonestCompX.cxFtth_v,
    HonestCompX.cxFttt_v]
  by_cases hp : HonestCompX.isPair D.H rr
  · have hpB : Nock.V1J8.FillX.isPairB D.H rr = true := (Nock.V1J8.FillX.isPairB_iff D.H rr).mpr hp
    rw [if_pos hpB]
    obtain ⟨a, c, ha', hc', ha, hc, hax, hk1, hk2, hv1, hv2, hs1, hs2⟩ := pair_factsG Rt hgen O hpG hbig hrowm hp
    have hst : rr.st = .s5 := hp.1
    have hma := comb_mem_acsG Rt hgen O hpG ha (by rw [(hbig a ha).2]; simp)
    have hmc := comb_mem_acsG Rt hgen O hpG hc (by rw [(hbig c hc).2]; simp)
    have hra : ((D.H (.atom a)).2 : ℕ) = D.acs.idxOf (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)) := by
      show (ComplJ8Data.hdlP p D.cells D.acs (.atom a)).2 = _
      have : ¬ a < p := Nat.not_lt.mpr (hbig a ha).1
      simp only [ComplJ8Data.hdlP, this, if_false]
      rw [hrt, hix _ hma]
    have hrc : ((D.H (.atom c)).2 : ℕ) = D.acs.idxOf (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs c)) := by
      show (ComplJ8Data.hdlP p D.cells D.acs (.atom c)).2 = _
      have : ¬ c < p := Nat.not_lt.mpr (hbig c hc).1
      simp only [ComplJ8Data.hdlP, this, if_false]
      rw [hrt, hix _ hmc]
    have e1 := WvA_eq δ D χ _ _ _ _ hma rfl hlen hax hs1 (hdl D.acs ((Noun.slot (D.pd rr).1
      (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a))).getD (.atom 0)))
    have e2 := WvA_eq δ D χ _ _ _ _ hmc rfl hlen hax hs2 (hdl D.acs ((Noun.slot (D.pd rr).1
      (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs c))).getD (.atom 0)))
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, readRecH, ha', hc',
      Nock.V1J8.Gen.atomV]
    rw [e1, e2, hH.small _ hv1, hH.small _ hv2]
    simp only [HonestCompX.cPr2, HonestCompX.cAx2, HonestCompX.cL, hst, if_pos hp, HonestCompX.hv, hra, hrc,
      map_one, one_mul]
    simp only [show (D.pd rr).2.1.1 = 0 from hk1, show (D.pd rr).2.2.1 = 0 from hk2, Nat.cast_zero]
    rfl
  · have hpB : Nock.V1J8.FillX.isPairB D.H rr = false := by
      cases h : Nock.V1J8.FillX.isPairB D.H rr
      · rfl
      · exact absurd ((Nock.V1J8.FillX.isPairB_iff D.H rr).mp h) hp
    rw [if_neg (by simp [hpB])]
    simp [HonestCompX.cPr2, hp]

/-- The run's atom-walk reads are its rows' pair reads. -/
theorem preads_eqG :
    (j8DataGen p Rg Rt hgen O).preads.Perm <| (bfsForest [t]).flatMap fun u =>
      if Nock.V1J8.FillX.isPairB (j8DataGen p Rg Rt hgen O).H (rowOfSkelX u.label) then
        [(Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (Nock.V1J8.Gen.atomV (rowOfSkelX u.label).ftth)),
            ((j8DataGen p Rg Rt hgen O).pd (rowOfSkelX u.label)).1),
         (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (Nock.V1J8.Gen.atomV (rowOfSkelX u.label).fttt)),
            ((j8DataGen p Rg Rt hgen O).pd (rowOfSkelX u.label)).1)]
      else [] := by
  refine (O.permR _ _).trans (List.Perm.of_eq ?_)
  have hrows : (j8DataGen p Rg Rt hgen O).rows.toList = (bfsForest [t]).map fun u => rowOfSkelX u.label := by
    show (ComplJ8Data.rowsOfT t).toList = _
    simp [ComplJ8Data.rowsOfT]
  show ComplJ8Data.pairReadsP (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd (j8DataGen p Rg Rt hgen O).rows = _
  unfold ComplJ8Data.pairReadsP
  rw [hrows, List.flatMap_map]

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds) in
set_option maxHeartbeats 2000000 in
/-- **`hA`: the compute's atom-walk pair consumes total the atom walk's handle provide**, at every coin, from
`complJ8`'s binders `hpG hop5 hclA hRt h31` (`bigBound_singleG`). -/
theorem hA_runG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (hop5 : ComplJ8.ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) (χ : Coins frameJ8 K) :
    ∑ j ∈ Finset.range (bfsForest [t]).length, awT δ b (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubCG δ b Rt hgen O χ) j =
      Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsV WalkHQ.pubPQ)
        (((BRunG δ b Rt hgen O o).M χ).pubsV (WalkHQ.pubPQ + 1)) := by
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have hN : (j8DataGen p Rg Rt hgen O).rows.size ≤ 2 ^ 31 := by
    have h := h31 (bfsForest [(j8DataGen p Rg Rt hgen O).t]).length (by simp [sizesJ8])
    rw [data_rowsG hgen O]
    simpa [ComplJ8Data.rowsOfT, j8DataGen] using h
  obtain ⟨hb, -, -, -, -, -, -, hix, hrt⟩ := bigBound_singleG hgen O hpG (hclA 0) (hclA 1) hRt hop5 hN
  have hbig : ∀ a ∈ (j8DataGen p Rg Rt hgen O).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1] :=
    fun a ha => ⟨(hb a ha).1, (hb a ha).2.2⟩
  have hlenA : (j8DataGen p Rg Rt hgen O).acs.length < p := size_lt_pG Rt hgen O hp63 h31 (by simp [sizesJ8])
  revert o
  set D := j8DataGen p Rg Rt hgen O with hD
  intro o
  set W := bfsForest [t] with hW
  set g : NTree SkelX → 𝕂′ := fun u => ((if Nock.V1J8.FillX.isPairB D.H (rowOfSkelX u.label) then
        [(Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (Nock.V1J8.Gen.atomV (rowOfSkelX u.label).ftth)),
            (D.pd (rowOfSkelX u.label)).1),
         (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (Nock.V1J8.Gen.atomV (rowOfSkelX u.label).fttt)),
            (D.pd (rowOfSkelX u.label)).1)]
      else []).map fun x => WvA δ D χ (readRecH D.acs x)).sum with hgdef
  have hrow : ∀ j ∈ Finset.range W.length,
      awT δ b D.H D.pd W (VerJ8.chalVJ8 b χ) (pubCG δ b Rt hgen O χ) j = g (W.getD j t) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [awT_runG δ b Rt hgen O hpG hbig hrt hix hlenA χ _ j hj', List.getD_eq_getElem _ _ hj']
  rw [Finset.sum_congr rfl hrow, ComplJ8OfBal.sum_range_getD' t g]
  have hsum : (W.map g).sum = (D.preads.map fun x => WvA δ D χ (readRecH D.acs x)).sum := by
    rw [(List.Perm.map _ (preads_eqG Rt hgen O)).sum_eq, ComplJ8OfBalG.sum_flatMap_map]
  rw [hsum]
  show _ = Quad.mk _ (pubsVOf δ b D o χ WalkHQ.pubPQ) (pubsVOf δ b D o χ (WalkHQ.pubPQ + 1))
  by_cases h0 : D.preads = []
  · rw [h0]
    have hz : (0 : 𝕂′) = Quad.mk _ 0 0 := ((Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩).symm
    simp [pubsVOf, h0, hz]
  have hsh := preads_shapeG Rt hgen O hbig
  have h6 : pubsVOf δ b D o χ WalkHQ.pubPQ = pub2 δ (vhP δ b D o χ) 6 := by simp [pubsVOf, h0, WalkHQ.pubPQ]
  have h7 : pubsVOf δ b D o χ (WalkHQ.pubPQ + 1) = pub2 δ (vhP δ b D o χ) 7 := by
    simp [pubsVOf, h0, WalkHQ.pubPQ]
  rw [h6, h7, pub2_mk2 δ _ 6 rfl]
  have hall : ∀ x ∈ D.preads, VclL.isPathAx x.2 = true := by
    intro x hx
    obtain ⟨a, -, -, h⟩ := hsh x hx
    exact ComplJ8OfBal.isPathAx_of_two_le (by omega)
  have hmem : ∀ x ∈ VclL.pathReads D.preads, x ∈ D.preads := fun x hx =>
    (List.mem_filter.mp (List.mem_dedup.mp hx)).1
  have hslot : ∀ x ∈ VclL.pathReads D.preads, (Noun.slot x.2 x.1).isSome := by
    intro x hx
    obtain ⟨a, ha, h1, h2⟩ := hsh x (hmem x hx)
    rw [h1, (hbig a ha).2]
    rcases h2 with h | h <;> rw [h, VclL.slot_eq_chainWalk _ (by norm_num)] <;> rfl
  have hd61 : ComplJ8Walk.WalkDepthOK D.preads := by
    intro x hx
    obtain ⟨a, -, -, h⟩ := hsh x (hmem x hx)
    rcases h with h | h <;> rw [h] <;> decide
  have hpre : ∀ u ∈ walkRows D.acs D.preads, 2 * axisFold u.label.bits + 1 < p := by
    intro u hu
    have h60 := ComplJ8Walk.walkRows_len_le60 hd61 hu
    have h1 := axisFold_lt u.label.bits
    have h2 : 2 ^ (u.label.bits.length + 1) ≤ 2 ^ 61 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 63 = 4 * 2 ^ 61 := by norm_num
    omega
  have hwn : ∀ u ∈ walkRows D.acs D.preads, u.label.node ∈ D.acs := by
    refine ComplJ8OfBal.walkRows_nodes_mem _ _ (List.ne_nil_of_length_pos (acs_posG (p := p) Rt hgen O))
      (acs_closed_runG Rt hgen O hpG) ?_
    intro x hx _
    obtain ⟨a, ha, h1, h2⟩ := hsh x hx
    have hl := (hbig a ha).2
    refine ⟨h1 ▸ comb_mem_acsG Rt hgen O hpG ha (by rw [hl]; simp), ?_⟩
    rw [h1, hl]
    rcases h2 with h | h <;> rw [h, VclL.slot_eq_chainWalk _ (by norm_num)] <;> rfl
  have hmV : nVOf D ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjV := (powN_ok o (le_two_pow_ht D hmV)).1
  rw [vhP_eqG δ b Rt hgen O o h0 hinjV χ hlenA hwn (acs_cellG Rt hgen O hpG) hpre,
    walk_provide_total (WvA δ D χ) D.acs D.preads hslot (fun _ => rfl), ComplJ8OfBal.pathKind_of_all hall]

end AWRun
end AW
section IncComp
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
section IncRun
variable [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
set_option maxHeartbeats 1000000 in
/-- **Run row `j`'s inc consume** is the inc weight of its slow-OP4 operand (zero on every other row). -/
theorem incT_run2G (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) (j : ℕ) (hj : j < (bfsForest [t]).length) :
    incT δ b (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      (optI p (rowOfSkelX ((bfsForest [t])[j]'hj).label)).elim 0 (FI δ (j8DataGen p Rg Rt hgen O) χ) := by
  set D := j8DataGen p Rg Rt hgen O with hD
  set W := bfsForest [t] with hW
  set rr := rowOfSkelX (W[j]'hj).label with hrr
  have hrow : HonestWalkX.rowAtWX W (j + 1) = rr := by
    simp [hrr, HonestWalkX.rowAtWX, List.getElem?_eq_getElem hj]
  have hrowm : rr ∈ (ComplJ8Data.rowsOfT t).toList := by
    simp only [hrr, ComplJ8Data.rowsOfT, List.toList_toArray]
    exact List.mem_map_of_mem (List.getElem_mem hj)
  have hH : HonestCompX.HdlOK p D.H := ComplJ8Data.hdlOK_hdlP p D.cells D.acs
  have htr : (HonestTraceX.env0 D.H D.pd W (VerJ8.chalVJ8 b χ) pubVal j).trace =
      HonestCompX.colX D.H D.pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j) := by
    funext c
    show HonestTraceX.baseT D.H D.pd W j c = _
    unfold HonestTraceX.baseT; rw [hrow]
  unfold incT
  rw [DX_inc δ b _ χ rfl, htr, HonestCompX.colX_st _ _ _ _ _ 4 (by decide)]
  simp only [HonestCompX.cx61, HonestCompX.cxSf1_k, HonestCompX.cxSf1_v, HonestCompX.cxE_k, HonestCompX.cxE_v]
  by_cases hst : rr.st = .s4
  · obtain ⟨n, h1, h2⟩ := ComplJ8Atom.s4_row hgen hax hop5 hrowm hst
    have ho : optI p rr = if p ≤ n + 1 then some n else none := by
      unfold optI; rw [hst, h1]
    rw [ho]
    simp only [HonestCompX.cFast, hst, h2, RowDecodeVSX.stIdx, if_true]
    by_cases hp : p ≤ n + 1
    · have hb := hH.big (n + 1) hp
      rw [if_pos hp, if_neg (by omega)]
      simp only [Option.elim, FI, h1, HonestCompX.hk, HonestCompX.hv, hb, sub_zero, mul_one, map_one, one_mul]
    · have hs := hH.small (n + 1) (by omega)
      rw [if_neg hp, if_pos (by rw [hs])]
      simp
  · have ho : optI p rr = none := by
      unfold optI
      cases h : rr.st <;> simp_all
    rw [ho, if_neg]
    · simp
    · cases h : rr.st <;> simp_all [RowDecodeVSX.stIdx]

end IncRun
end IncComp
section IncClose
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
/-- **The compute's inc consumes, by operand**: the slow-OP4 rows' inc weights total `Σ_{(v, c) ∈ incOps} c · FI v`. -/
theorem incT_totalG (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t) (χ : Coins frameJ8 K)
    (pubVal : ℕ → ZMod p) :
    ∑ j ∈ Finset.range (bfsForest [t]).length, incT δ b (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      ((ComplJ8Data.incOpsP p (j8DataGen p Rg Rt hgen O).rows).map fun vc =>
        (vc.2 : 𝕂′) * FI δ (j8DataGen p Rg Rt hgen O) χ vc.1).sum := by
  set D := j8DataGen p Rg Rt hgen O with hD
  set W := bfsForest [t] with hW
  set g : NTree SkelX → 𝕂′ := fun u => (optI p (rowOfSkelX u.label)).elim 0 (FI δ D χ) with hg
  have hrow : ∀ j ∈ Finset.range W.length,
      incT δ b D.H D.pd W (VerJ8.chalVJ8 b χ) pubVal j = g (W.getD j t) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [incT_run2G δ b Rt hgen O hax hop5 χ _ j hj', List.getD_eq_getElem _ _ hj']
  rw [Finset.sum_congr rfl hrow, ComplJ8OfBal.sum_range_getD' t g, hg,
    sum_filterMap_elim (fun u => optI p (rowOfSkelX u.label)) (FI δ D χ) W, sum_count_dedup]
  have hrows : D.rows.toList = W.map fun u => rowOfSkelX u.label := by
    show (ComplJ8Data.rowsOfT t).toList = _
    simp [ComplJ8Data.rowsOfT, hW]
  have hvs : D.rows.toList.filterMap (optI p) = W.filterMap fun u => optI p (rowOfSkelX u.label) := by
    rw [hrows, List.filterMap_map]; rfl
  show _ = (((D.rows.toList.filterMap (optI p)).dedup.map fun v =>
    (v, (D.rows.toList.filterMap (optI p)).count v)).map fun vc => (vc.2 : 𝕂′) * FI δ D χ vc.1).sum
  rw [hvs]

end IncClose
section IncAtomSum
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
set_option maxHeartbeats 2000000 in
/-- **The atom table's inc terminal, by operand** (two limbs per big atom): the `mi`-weighted inc-key LogUp total is
`Σ_{(v, c) ∈ incOps} c · FI v` — the row `rootIdx (v + 1)` carries `mi = c` and the inc key of `v`'s compute record
(old handle `(0, p − 1)` on the conversion row, `(2, rootIdx v)` on the inc row of `v`'s two-limb comb). -/
theorem incSum_eqG (hpG : p = Nock.Atoms.p) (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (hbig : ∀ a ∈ (j8DataGen p Rg Rt hgen O).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1])
    (hrt : ∀ a, ComplJ8Data.rootIdxP p (j8DataGen p Rg Rt hgen O).acs a =
      Nock.V1J8.Gen.idxOf (j8DataGen p Rg Rt hgen O).acs (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)))
    (hN : (j8DataGen p Rg Rt hgen O).rows.size ≤ 2 ^ 31)
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (j8DataGen p Rg Rt hgen O).acs.length)) (χ : Coins frameJ8 K) (pubs : ℕ → K) :
    ∑ j ∈ Finset.range (j8DataGen p Rg Rt hgen O).acs.length,
        liftQ δ (HonestA8.cNat j (newBA (j8DataGen p Rg Rt hgen O) AtomChipHQ.mi)) *
          (HonestA8.dNat δ (HonestA8.dMI δ b (acs_posG Rt hgen O) (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) pubs
            (colAH δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) o χ pubs) (newBA (j8DataGen p Rg Rt hgen O))) j)⁻¹ =
      ((ComplJ8Data.incOpsP p (j8DataGen p Rg Rt hgen O).rows).map fun vc =>
        (vc.2 : 𝕂′) * FI δ (j8DataGen p Rg Rt hgen O) χ vc.1).sum := by
  subst hpG
  set D := j8DataGen Nock.Atoms.p Rg Rt hgen O with hD
  have hA : 0 < D.acs.length := acs_posG Rt hgen O
  have hg := genHyp_j8G Rg Rt hgen O hax hop5 hN
  set ops := ComplJ8Data.incOpsP Nock.Atoms.p D.rows with hops
  have hl2 : ∀ a ∈ D.bigs, Nock.Atoms.limbs a = [a + 1 - Nock.Atoms.p, Nock.Atoms.B - 1] := fun a ha => (hbig a ha).2
  have hopB : ∀ vc ∈ ops, vc.1 + 1 ≠ Nock.Atoms.p → vc.1 ∈ D.bigs ∧ vc.1 + 1 ∈ D.bigs :=
    fun vc hvc hp => (hg.ops vc hvc).2 hp
  have hopT : ∀ vc ∈ ops, vc.1 + 1 ∈ D.bigs := by
    intro vc hvc
    by_cases hp : vc.1 + 1 = Nock.Atoms.p
    · rw [hp]; exact (hg.ops vc hvc).1 hp
    · exact (hopB vc hvc hp).2
  have hlen : ∀ vc ∈ ops, vc.1 + 1 ≠ Nock.Atoms.p →
      (Nock.Atoms.limbs vc.1).length = 2 ∧ (Nock.Atoms.limbs (vc.1 + 1)).length = 2 := by
    intro vc hvc hp
    obtain ⟨h1, h2⟩ := hopB vc hvc hp
    rw [hl2 _ h1, hl2 _ h2]; simp
  obtain ⟨-, hfold⟩ := fold_mi Nock.Atoms.p D.acs D.rows ops (Array.replicate D.acs.length Nock.V1J8.Gen.AInfo.z) hlen
  have hinfo : D.info = ComplJ8Data.infoOfP Nock.Atoms.p D.acs D.rows := rfl
  have hF0 : ComplJ8Atom.infoFold Nock.Atoms.p D.acs D.rows =
      ops.foldl (ComplJ8Atom.stepF Nock.Atoms.p D.acs D.rows) (Array.replicate D.acs.length Nock.V1J8.Gen.AInfo.z) := rfl
  have hz : ∀ k < D.acs.length, (Array.replicate D.acs.length Nock.V1J8.Gen.AInfo.z).getD k Nock.V1J8.Gen.AInfo.z =
      Nock.V1J8.Gen.AInfo.z := by
    intro k hk; simp [Array.getD_eq_getD_getElem?, hk]
  set tgt : ℕ × ℕ → ℕ := fun vc => ComplJ8Data.rootIdxP Nock.Atoms.p D.acs (vc.1 + 1) with htgt
  have hmi : ∀ k < D.acs.length, (D.info.getD k Nock.V1J8.Gen.AInfo.z).mi = ((ops.filter fun vc => tgt vc = k).map Prod.snd).sum := by
    intro k hk
    rw [hinfo, (ComplJ8Atom.info_fields _ _ _ k).2.2.2.2.2.2, hF0, (hfold k (by simpa using hk)).1, hz k hk]
    simp [Nock.V1J8.Gen.AInfo.z, htgt]
  have hconv : ∀ k < D.acs.length, ((D.info.getD k Nock.V1J8.Gen.AInfo.z).conv = true ↔
      ∃ vc ∈ ops, vc.1 + 1 = Nock.Atoms.p ∧ ComplJ8Data.rootIdxP Nock.Atoms.p D.acs Nock.Atoms.p = k) := by
    intro k hk
    rw [hinfo, (ComplJ8Atom.info_fields _ _ _ k).2.1, hF0, (hfold k (by simpa using hk)).2.1, hz k hk]
    simp [Nock.V1J8.Gen.AInfo.z]
  have hinc : ∀ k < D.acs.length, ((D.info.getD k Nock.V1J8.Gen.AInfo.z).inc = true ↔
      ∃ vc ∈ ops, vc.1 + 1 ≠ Nock.Atoms.p ∧
        k = Nock.V1J8.Gen.idxOf D.acs (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (vc.1 + 1)))) := by
    intro k hk
    rw [hinfo, (ComplJ8Atom.info_fields _ _ _ k).1, hF0, (hfold k (by simpa using hk)).2.2, hz k hk]
    simp [Nock.V1J8.Gen.AInfo.z]
  have hmem : ∀ a ∈ D.bigs, Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a) ∈ D.acs :=
    fun a ha => comb_mem_acsG Rt hgen O rfl ha (by rw [hl2 a ha]; simp)
  have hlt : ∀ c ∈ D.acs, Nock.V1J8.Gen.idxOf D.acs c < D.acs.length := by
    intro c hc; rw [ComplJ8OfBal.genIdxOf_eq _ _ hc]; exact List.idxOf_lt_length_of_mem hc
  have hgetE : ∀ c (hc : c ∈ D.acs), D.acs[Nock.V1J8.Gen.idxOf D.acs c]'(hlt c hc) = c := by
    intro c hc
    simp only [ComplJ8OfBal.genIdxOf_eq _ _ hc]
    exact List.getElem_idxOf _
  have hgetD : ∀ c ∈ D.acs, ∀ d, D.acs.getD (Nock.V1J8.Gen.idxOf D.acs c) d = c := by
    intro c hc d
    rw [List.getD_eq_getElem _ _ (hlt c hc)]; exact hgetE c hc
  have htl : ∀ vc ∈ ops, tgt vc < D.acs.length := by
    intro vc hvc
    simp only [htgt, hrt]
    exact hlt _ (hmem _ (hopT vc hvc))
  -- the atom rows' weight
  have hterm : ∀ j ∈ Finset.range D.acs.length,
      liftQ δ (HonestA8.cNat j (newBA D AtomChipHQ.mi)) *
        (HonestA8.dNat δ (HonestA8.dMI δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) pubs (colAH δ b D hA o χ pubs)
          (newBA D)) j)⁻¹ =
      ((((ops.filter fun vc => tgt vc = j).map Prod.snd).sum : ℕ) : Quad (algebraMap (ZMod Nock.Atoms.p) K δ)) * GAt δ b D hA o χ pubs j := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [HonestA8.cNat, HonestA8.dNat, dif_pos hj', GAt, newBA_mi, hmi j hj', liftQ, map_natCast]
  rw [Finset.sum_congr rfl hterm, ← sum_serialW D.acs.length tgt Prod.snd (GAt δ b D hA o χ pubs) ops htl]
  refine congrArg List.sum (List.map_congr_left fun vc hvc => ?_)
  congr 1
  -- the matching: the target row's inc key is `vc.1`'s compute record
  rcases vc with ⟨v, c⟩
  dsimp only
  have hk := htl (v, c) hvc
  have hkt : tgt (v, c) = Nock.V1J8.Gen.idxOf D.acs (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (v + 1))) := by
    simp only [htgt, hrt]
  have hH : HonestCompX.HdlOK Nock.Atoms.p D.H := ComplJ8Data.hdlOK_hdlP Nock.Atoms.p D.cells D.acs
  have hHb : ∀ a, Nock.Atoms.p ≤ a → D.H (.atom a) = (2, ComplJ8Data.rootIdxP Nock.Atoms.p D.acs a) := by
    intro a ha
    show ComplJ8Data.hdlP Nock.Atoms.p D.cells D.acs (.atom a) = _
    simp [ComplJ8Data.hdlP, Nat.not_lt.mpr ha]
  obtain ⟨x, hx, -, -, hle⟩ := ComplJ8Atom.mem_incOpsP _ _ (v, c) hvc
  simp only [GAt, dif_pos hk, FI, ← hD]
  rw [dMI_key δ b D hA o hinj χ pubs ⟨tgt (v, c), hk⟩, newBA_conv, newBA_idxO]
  refine congrArg (fun x => (ComplJ8Bad.ρH δ χ + x)⁻¹) ?_
  by_cases hp : v + 1 = Nock.Atoms.p
  · have hc : (D.info.getD (tgt (v, c)) Nock.V1J8.Gen.AInfo.z).conv = true :=
      (hconv _ hk).mpr ⟨(v, c), hvc, hp, by simp only [htgt, hp]⟩
    have hsm : D.H (.atom v) = (0, v) := hH.small v (by omega)
    have hv1 : ((v : ℕ) : ZMod Nock.Atoms.p) = -1 := by
      have : ((v + 1 : ℕ) : ZMod Nock.Atoms.p) = 0 := by rw [hp, ZMod.natCast_self]
      push_cast at this; linear_combination this
    simp only [hc, if_true, hsm, hHb (v + 1) (by omega), hv1]
    simp only [htgt]
    norm_num
  · have hpv : Nock.Atoms.p ≤ v := by omega
    have hc : (D.info.getD (tgt (v, c)) Nock.V1J8.Gen.AInfo.z).conv = false := by
      cases hcc : (D.info.getD (tgt (v, c)) Nock.V1J8.Gen.AInfo.z).conv
      · rfl
      · exfalso
        obtain ⟨wc, hwc, hwp, hwk⟩ := (hconv _ hk).mp hcc
        have m1 := hmem _ ((hg.ops wc hwc).1 hwp)
        have m2 := hmem _ (hopT (v, c) hvc)
        rw [hrt, hkt] at hwk
        have e1 : Nock.V1J8.Gen.combOf (Nock.Atoms.limbs Nock.Atoms.p) =
            Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (v + 1)) := by
          rw [← hgetD _ m1 Nock.V1J8.Gen.padN, ← hgetD _ m2 Nock.V1J8.Gen.padN, hwk]
        have e2 : Nock.Atoms.limbs Nock.Atoms.p = Nock.Atoms.limbs (v + 1) := by
          rw [← ComplJ8Atom.unComb_combOf (Nock.Atoms.limbs Nock.Atoms.p) (by rw [Nock.Atoms.limbs_p]; simp),
            ← ComplJ8Atom.unComb_combOf (Nock.Atoms.limbs (v + 1)) (by rw [(hlen (v, c) hvc hp).2]), e1]
        have e3 : Nock.Atoms.p = v + 1 := by
          rw [← Nock.Atoms.val_limbs Nock.Atoms.p, ← Nock.Atoms.val_limbs (v + 1), e2]
        exact hp e3.symm
    have hi : (D.info.getD (tgt (v, c)) Nock.V1J8.Gen.AInfo.z).inc = true := (hinc _ hk).mpr ⟨(v, c), hvc, hp, hkt⟩
    set T := ComplJ8Atom.tabOf D.acs D.info D.mb D.rows with hT
    have hsp : T.sp (tgt (v, c)) = Nock.Atoms.limbs (v + 1) := by
      show ComplJ8Atom.unComb (D.acs.getD (tgt (v, c)) Nock.V1J8.Gen.padN) = _
      rw [hkt, hgetD _ (hmem _ (hopT (v, c) hvc)), ComplJ8Atom.unComb_combOf _ (by rw [(hlen (v, c) hvc hp).2])]
    have hidx : (T.row (tgt (v, c))).idxO = ComplJ8Data.rootIdxP Nock.Atoms.p D.acs v := by
      rw [hkt]; exact ComplJ8Atom.idxO_root _ _ _ _ hg (v, c) hvc hp
    simp only [hc, Bool.false_eq_true, if_false, hidx, hHb v hpv, hHb (v + 1) (by omega)]
    simp only [htgt]
    norm_num

end IncAtomSum
section IncFinal
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK ProgOp5OK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.Jet.PinJ8 (pinCons)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.FiniteIO (compress)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
set_option maxHeartbeats 2000000 in
/-- **`hI`: the compute's inc consumes total the atom table's inc terminal**, at every coin, from `complJ8`'s
binders `hpG hax hop5 hclA hRt h31` (`bigBound_singleG`): both sides are `Σ_{(v, c) ∈ incOps} c · FI v`
(`incT_totalG`, `incSum_eqG`). -/
theorem hI_runG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) :
    ∀ χ, (BRunG δ b Rt hgen O o).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, incT δ b (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubCG δ b Rt hgen O χ) j =
      Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsA AtomChipHQ.pubMI)
        (((BRunG δ b Rt hgen O o).M χ).pubsA (AtomChipHQ.pubMI + 1)) := by
  intro χ _
  have hN : (j8DataGen p Rg Rt hgen O).rows.size ≤ 2 ^ 31 := by
    have h := h31 (bfsForest [(j8DataGen p Rg Rt hgen O).t]).length (by simp [sizesJ8])
    rw [data_rowsG hgen O]
    simpa [ComplJ8Data.rowsOfT, j8DataGen] using h
  obtain ⟨hb, -, -, -, -, -, -, -, hrt⟩ := bigBound_singleG hgen O hpG (hclA 0) (hclA 1) hRt hop5 hN
  have hbig : ∀ a ∈ (j8DataGen p Rg Rt hgen O).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1] :=
    fun a ha => ⟨(hb a ha).1, (hb a ha).2.2⟩
  revert o
  set D := j8DataGen p Rg Rt hgen O with hD
  intro o _
  have hA : 0 < D.acs.length := acs_posG Rt hgen O
  have hmA : D.acs.length ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjA := (powN_ok o (le_two_pow_ht D hmA)).1
  obtain ⟨-, -, -, -, -, tMI⟩ := ComplJ8OfAtom.atomTerms δ b D hA o χ
  show _ = Quad.mk _ (pubsAOf δ b D hA o χ AtomChipHQ.pubMI) (pubsAOf δ b D hA o χ (AtomChipHQ.pubMI + 1))
  rw [tMI, incT_totalG δ b Rt hgen O hax hop5 χ _, incSum_eqG δ b Rt hgen O hpG hax hop5 hbig hrt hN o hinjA χ _]

end IncFinal
end
end ComplJ8OfBalGG_1

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen
