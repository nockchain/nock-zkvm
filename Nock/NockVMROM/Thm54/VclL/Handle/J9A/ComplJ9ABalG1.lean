/-
J-9 A L7 balance, the export clause `hGx`.

  * §1 generic in the data record (`J8Data`), any orbit:
    - `whX_eq_gen`: the J-8 walk's handle import is the walk-row sum of the cell handle weights (J-8's `whX_eq`
      with `j8DataOf` replaced by a record whose `H` is `hdlP`, whose cells are closed and whose walk nodes are
      cells).
    - `h1J_gen`: the J export publics `2/3` are the J export table's total (J-8's `h1J_run`, any record).
    - `balG1_gen`: **the export clause over a record** from (i) the compute export total `hρ` (`ρ 3` = the weighted
      total of a compute consume list `cs`), (ii) the J export key identity `hJ`, (iii) the count identity `hmh`
      (`mh` = the count of `cs`, the walk rows at cells, the J export reads), (iv) the range `hrange`.
  * §2 at `BRun9A`: `hGx_A_of` (the `hGx` field of `ComplJ9AObligations`, verbatim) from the walk-node fact
    `hwcellA` and three carried run facts.
    The count identity is `ComplJ9ABalX.mh_eq_cntA`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalX
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalGen
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalG1

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG (GC wsum wsum_append sum_cnt_eq wsum_cellPairs wsum_keys
  cellHx_eq chT_eq)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.Jet.RapJetJ8 (dJX)
open Nock.Jet.ChipJ8T.HonestRAP (sX)

noncomputable section

/-! ## 1. Generic in the data record -/

section Gen
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- Cells of a closed cell list are cells whose cell children are in the list. -/
theorem cells_kids_gen (cs : List Noun) (hcl : ComplJ8Data.ClP cs []) (hcellsC : ∀ c ∈ cs, c.isCell = true)
    (c : Noun) (hc : c ∈ cs) :
    ∃ x y, c = Noun.cell x y ∧ (x.isCell = true → x ∈ cs) ∧ (y.isCell = true → y ∈ cs) := by
  have hcc := hcellsC c hc
  cases c with
  | atom v => simp [Noun.isCell] at hcc
  | cell x y =>
    have hc2 := hcl x y hc (by simp)
    refine ⟨x, y, rfl, fun hx => ?_, fun hy => ?_⟩
    · cases x with
      | atom v => simp [Noun.isCell] at hx
      | cell x1 x2 => exact hc2.1 x1 x2 rfl
    · cases y with
      | atom v => simp [Noun.isCell] at hy
      | cell y1 y2 => exact hc2.2 y1 y2 rfl

/-- **The J-8 walk handle import over a record** (J-8's `whX_eq`, any record with `H = hdlP`, closed cells and
walk nodes at cells). -/
theorem whX_eq_gen (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjC : Function.Injective (powN o D.cells.length))
    (hinjW : Function.Injective (powN o (walkRows D.cells D.reads).length))
    (hH : D.H = ComplJ8Data.hdlP p D.cells D.acs) (hcl : ComplJ8Data.ClP D.cells [])
    (hcellsC : ∀ c ∈ D.cells, c.isCell = true)
    (hwcell : ∀ u ∈ walkRows D.cells D.reads, u.label.node ∈ D.cells) (χ : Coins frameJ8 K) :
    whX δ b D o χ =
      ((walkRows D.cells D.reads).map fun u => GC δ b D hC o χ (D.cells.idxOf u.label.node)).sum := by
  have hterm : ∀ k ∈ Finset.range (walkRows D.cells D.reads).length, (wdN δ b D o χ WalkHC.xKeyH k)⁻¹ =
      GC δ b D hC o χ (D.cells.idxOf (wTrie D.cells D.reads k).label.node) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hmem : (wTrie D.cells D.reads k).label.node ∈ D.cells := hwcell _ (wTrie_mem _ _ hk')
    obtain ⟨x, y, hxy, hx, hy⟩ := cells_kids_gen D.cells hcl hcellsC _ hmem
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
    rw [hd, hv, hkl.1, hkl.2.1, hkl.2.2.1, hkl.2.2.2, cellHx_eq δ b D hC o hinjC χ hH _ hjl hyj hx hy]
  unfold whX
  rw [Finset.sum_congr rfl hterm]
  exact ComplJ8OfBal.sum_range_getD' (trie (.atom 0) (.atom 0) [] [])
    (fun u => GC δ b D hC o χ (D.cells.idxOf u.label.node)) _

/-- **`h1J` over a record**: the J export publics `2/3` are the J export table's total. -/
theorem h1J_gen (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (pubsJOf δ D χ 2) (pubsJOf δ D χ 3) =
      ComplJ8Bal.tots δ (fH δ b χ) [tabJX δ D] := by
  have e0 : pubsJOf δ D χ 2 = pub2 δ (∑ k, sX δ (chalsJJ8 χ) (D.jrows.get k)) 2 := by simp [pubsJOf]
  have e1 : pubsJOf δ D χ 3 = pub2 δ (∑ k, sX δ (chalsJJ8 χ) (D.jrows.get k)) 3 := by simp [pubsJOf]
  have h2 := pub2_mk2 δ (∑ k, sX δ (chalsJJ8 χ) (D.jrows.get k)) 2 rfl
  rw [show (2 : ℕ) + 1 = 3 from rfl] at h2
  rw [e0, e1, h2]
  simp only [ComplJ8Bal.tots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, tabJX, tot_mapTab,
    ← dJX_eq]
  have := ComplJ8Bal.tot_tabOfRows_fin (R := 𝕂′) (dJX δ (chalsJJ8 χ)) D.jrows.get
    (Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.entsX) (fun _ => ([] : List (List (ZMod p) × 𝕂′)))
  simp only [List.map_nil, List.sum_nil, sub_zero] at this
  rw [← this]
  rfl

/-- The J export reads of a record (serial, multiplicity `1`). -/
abbrev jReadsOf (D : J8Data p Rg fuel s f r) : List (ℕ × ℕ) :=
  D.jrows.flatMap fun row => (Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.entsX row).map fun κ => ((κ.headD 0).val, 1)

/-- The export consumers of a record, the compute part `cs` given. -/
abbrev xRecsOf (D : J8Data p Rg fuel s f r) (cs : List (ℕ × ℕ)) : List ComplJ8Data.NamedRecs :=
  [⟨"compute", cs⟩, ⟨"walk", ComplJ8Data.cellPairs D.cells (D.ws.map Nock.V1J8.Gen.WRow.node)⟩, ⟨"J", jReadsOf D⟩]

set_option maxHeartbeats 1000000 in
/-- **`balG`'s export clause over a record** (any orbit `o`): the compute export total `ρ3` plus the walk and J
export imports equals the cell handle-export terminal, from `hρ` (compute total), `hJ` (J key identity), `hmh`
(counts) and `hrange` (serial range). -/
theorem balG1_gen (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjC : Function.Injective (powN o D.cells.length))
    (hinjW : Function.Injective (powN o (walkRows D.cells D.reads).length))
    (hH : D.H = ComplJ8Data.hdlP p D.cells D.acs) (hcl : ComplJ8Data.ClP D.cells [])
    (hcellsC : ∀ c ∈ D.cells, c.isCell = true)
    (hwcell : ∀ u ∈ walkRows D.cells D.reads, u.label.node ∈ D.cells)
    (hws : D.ws = (Nock.V1J8.Gen.walkGen (D.cells.headD (.atom 0)) D.reads).1)
    (hall : ∀ x ∈ D.reads, VclL.isPathAx x.2 = true) (hwalk : ComplJ8Walk.WalkDepthOK D.reads)
    (cs : List (ℕ × ℕ))
    (hmh : ∀ j < D.cells.length, D.mh.getD j 0 = ComplJ8Data.cnt (xRecsOf D cs) j)
    (hrange : ∀ q ∈ (xRecsOf D cs).flatMap ComplJ8Data.NamedRecs.recs, 0 < q.2 → q.1 < D.cells.length)
    (χ : Coins frameJ8 K) (ρ3 : 𝕂′) (hρ : ρ3 = wsum (GC δ b D hC o χ) cs)
    (hJ : ∀ row ∈ D.jrows, ∀ κ ∈ Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.entsX row,
      fH δ b χ (Nock.Jet.RapJetJ8.keyK 5 κ) = GC δ b D hC o χ (κ.headD 0).val) :
    ρ3 + (Quad.mk _ (pubsWOf δ b D o χ WalkHQ.pubXQ) (pubsWOf δ b D o χ (WalkHQ.pubXQ + 1)) +
        Quad.mk _ (pubsJOf δ D χ 2) (pubsJOf δ D χ 3)) =
      Quad.mk _ (pubsCOf δ b D hC o χ CellHQ.pubHQ) (pubsCOf δ b D hC o χ (CellHQ.pubHQ + 1)) := by
  set G := GC δ b D hC o χ with hG
  have eW : Quad.mk (algebraMap (ZMod p) K δ) (pubsWOf δ b D o χ WalkHQ.pubXQ)
      (pubsWOf δ b D o χ (WalkHQ.pubXQ + 1)) = whX δ b D o χ := by
    have h4 : pubsWOf δ b D o χ WalkHQ.pubXQ = pub2 δ (whX δ b D o χ) 4 := by simp [pubsWOf, WalkHQ.pubXQ]
    have h5 : pubsWOf δ b D o χ (WalkHQ.pubXQ + 1) = pub2 δ (whX δ b D o χ) 5 := by simp [pubsWOf, WalkHQ.pubXQ]
    rw [h4, h5, pub2_mk2 δ _ 4 rfl]
  have eC : Quad.mk (algebraMap (ZMod p) K δ) (pubsCOf δ b D hC o χ CellHQ.pubHQ)
      (pubsCOf δ b D hC o χ (CellHQ.pubHQ + 1)) = chT δ b D hC o χ := by
    have h4 : pubsCOf δ b D hC o χ CellHQ.pubHQ = pub2 δ (chT δ b D hC o χ) 4 := by simp [pubsCOf, CellHQ.pubHQ]
    have h5 : pubsCOf δ b D hC o χ (CellHQ.pubHQ + 1) = pub2 δ (chT δ b D hC o χ) 5 := by
      simp [pubsCOf, CellHQ.pubHQ]
    rw [h4, h5, pub2_mk2 δ _ 4 rfl]
  rw [eW, eC, h1J_gen δ b D χ, hρ, whX_eq_gen δ b D hC o hinjC hinjW hH hcl hcellsC hwcell χ, chT_eq δ b D hC o χ]
  have hcnt : ∑ j ∈ Finset.range D.cells.length, ((D.mh.getD j 0 : ℕ) : 𝕂′) * G j =
      ∑ j ∈ Finset.range D.cells.length, ((ComplJ8Data.cnt (xRecsOf D cs) j : ℕ) : 𝕂′) * G j :=
    Finset.sum_congr rfl fun j hj => by rw [hmh j (Finset.mem_range.mp hj)]
  rw [hcnt, sum_cnt_eq G _ _ hrange]
  simp only [xRecsOf, List.flatMap_cons, List.flatMap_nil, List.append_nil, wsum_append]
  congr 1
  congr 1
  · -- the walk
    rw [wsum_cellPairs]
    have h62 : ∀ r ∈ VclL.pathReads D.reads, VclL.depthOf r.2 ≤ 62 :=
      fun r hr => (hwalk r hr).trans (by norm_num)
    have hperm := ComplJ8OfBal.walkGen_nodes_perm D.cells _ hall h62
    rw [hws, ((hperm.map fun n => if n.isCell then G (Nock.V1J8.Gen.idxOf D.cells n) else 0).sum_eq),
      List.map_map]
    congr 1
    refine List.map_congr_left fun u hu => ?_
    have hm := hwcell u hu
    have hc := hcellsC _ hm
    simp only [Function.comp_apply, hc, if_true]
    rw [ComplJ8OfBal.genIdxOf_eq _ _ hm]
  · -- the J reads
    rw [wsum_keys δ G (Nock.Jet.ChipJ8.keysOf (F := ZMod p) Nock.Jet.ChipJ8.entsX)
      (fun κ : List (ZMod p) => (κ.headD 0).val)]
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

end Gen

/-! ## 2. `hGx` at `BRun9A` -/

section J9A
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf readsA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (WalkDepthOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalX (xRecsA basesA mh_eq_cntA)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen))

local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "BA" => BRun9A δ b Rt hgen hpG h31A
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The cell handle weight at `BRun9A`'s cell-table orbit. -/
abbrev GA (χ : Coins frameJ8 K) : ℕ → 𝕂′ :=
  GC δ b (DA) (ComplJ9ADataRec.cellsA_pos Rt hgen) (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ

/-- The twin compute's export consume list at the run. -/
abbrev csA : List (ℕ × ℕ) :=
  (basesA p Rg Rt hgen).flatMap fun bs =>
    ComplJ9ADataRec.xConsumesX9 p (⟨bs, bs, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))

set_option maxHeartbeats 1000000 in
/-- **`hGx` at `BRun9A`** (the `hGx` field of `ComplJ9AObligations`, verbatim), from the J-9 A walk-node fact
`hwcellA` and the three carried run facts: `hρA` (the twin compute export total), `hJA` (the J export
key identity at `DA`), `hrangeA` (the consumers' serial range).  Binder `hwalk9`. -/
theorem hGx_A_of (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwcellA : ∀ u ∈ walkRows (DA).cells (DA).reads, u.label.node ∈ (DA).cells)
    (hρA : ∀ χ, (BA).Good χ → ((BA).M χ).ρ 3 = wsum (GA δ b Rt hgen hpG h31A χ) (csA (p := p) Rt hgen))
    (hJA : ∀ χ, (BA).Good χ → ∀ row ∈ (DA).jrows, ∀ κ ∈ Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.entsX row,
      fH δ b χ (Nock.Jet.RapJetJ8.keyK 5 κ) = GA δ b Rt hgen hpG h31A χ (κ.headD 0).val)
    (hrangeA : ∀ q ∈ (xRecsA (DA) (basesA p Rg Rt hgen)).flatMap ComplJ8Data.NamedRecs.recs, 0 < q.2 →
      q.1 < (DA).cells.length) :
    ∀ χ, (BA).Good χ → ((BA).M χ).ρ 3 + (Quad.mk _ (((BA).M χ).pubsW WalkHQ.pubXQ)
        (((BA).M χ).pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (((BA).M χ).pubsJ 2) (((BA).M χ).pubsJ 3)) =
      Quad.mk _ (((BA).M χ).pubsC CellHQ.pubHQ) (((BA).M χ).pubsC (CellHQ.pubHQ + 1)) := by
  intro χ hχ
  set D := DA with hD
  set o := orbJ8 D (hF_run Rt hgen hpG h31A) with ho
  have hmC : D.cells.length ∈ sizesJ8 D := by simp [sizesJ8]
  have hmW : (walkRows D.cells D.reads).length ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjC := (powN_ok o (le_two_pow_ht D hmC)).1
  have hinjW := (powN_ok o (le_two_pow_ht D hmW)).1
  rw [ComplJ9AOfMem.pubsC_eq, ComplJ9AOfMem.pubsW_eq, ComplJ9AOfMem.pubsJ_eq]
  exact balG1_gen δ b D (ComplJ9ADataRec.cellsA_pos Rt hgen) o hinjC hinjW rfl (ComplJ8Data.cells_closed _)
    (fun c hc => (ComplJ8Walk.cellsOfRoots_mem _ c hc).1) hwcellA rfl (ComplJ9ABalGen.hall_readsA Rt hgen)
    (ComplJ9ADataRec.walkDepthOK_readsA Rt hgen hwalk9) (csA (p := p) Rt hgen)
    (fun j hj => mh_eq_cntA p Rg Rt hgen j hj) hrangeA χ _ (hρA χ hχ) (hJA χ hχ)

end J9A

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalG1

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalG1
#print axioms cells_kids_gen
#print axioms whX_eq_gen
#print axioms h1J_gen
#print axioms balG1_gen
#print axioms hGx_A_of
end Axioms
