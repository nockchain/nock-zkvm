/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalGen.lean

J-8's `ComplJ8OfBal.mx_spec`, `cxT_eq_wxT`, `walkRows_node_cells`, `balF1_run` are stated at `j8DataOf`.  Their
  proofs read the data only through five facts, which are the hypotheses here:
  * `hmx : D.mx = mxCounts D.cells D.ws` and `hws : D.ws = (walkGen (D.cells.headD 0) D.reads).1` (the shape of the
    walk data: true by `rfl` at `j8DataOf` and at `j9aDataOf`);
  * `hall : ∀ x ∈ D.reads, isPathAx x.2` and `hwalk : WalkDepthOK D.reads` (the read list's shape);
  * `hcellsC : ∀ c ∈ D.cells, c.isCell` and, for the walk nodes, `hwcell` (every spec walk node is a cell of the
    table), itself from `hclosed` (the cell list is child-closed), `hslot` (every read is a defined slot) and
    `hroot` (every cell read root is in the table) by `walkRows_node_cells_gen`.
  * §1 `mx_spec_gen`, `cxT_eq_wxT_gen`, `walkRows_node_cells_gen`; §2 the J-8 instances are recovered
    (`walkRows_node_cells_j8`, `cxT_eq_wxT_j8` = J-8's `cxT_eq_wxT`); §3 the J-9 A instance's data shape
    (`hall_readsA`, `hmx_A`, `hws_A`) and the `hfxC` / `hvalA0` fields at `BRun9A` (`hfxC_A`, `hvalA0_A`), with the
    walk-node fact `hwcellA` (every node of the J-9 A walk is a cell of the table) as the one remaining input of
    `hfxC_A`, reduced by `walkRows_node_cells_gen` to `hslot`/`hroot` on `readsA` (`hfxC_A_of`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfMem
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalGen

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of

noncomputable section

/-! ## 1. The generic lemmas -/

section Gen
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- `mxCounts` as a bump of the cell-pair list (the body of J-8's `mx_eq_cnt`). -/
theorem mxCounts_eq (cs : List Noun) (ws : List Nock.V1J8.Gen.WRow) : Nock.V1J8.Gen.mxCounts cs ws =
    ComplJ8Data.bumpAll (Array.replicate cs.length 0) (ComplJ8Data.cellPairs cs (ws.map Nock.V1J8.Gen.WRow.node)) := by
  unfold Nock.V1J8.Gen.mxCounts
  generalize Array.replicate cs.length 0 = a
  induction ws generalizing a with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.foldl_cons, List.map_cons]
    rcases hw : w.node with v | ⟨x, y⟩
    · rw [ih]; simp [ComplJ8Data.cellPairs]
    · rw [ih]; simp only [ComplJ8Data.cellPairs, List.filterMap_cons]; rfl

/-- **`mx_spec` over a general record**: the cell export multiplicity counts the spec walk rows at the serial. -/
theorem mx_spec_gen (D : J8Data p Rg fuel s f r) (hmx : D.mx = Nock.V1J8.Gen.mxCounts D.cells D.ws)
    (hws : D.ws = (Nock.V1J8.Gen.walkGen (D.cells.headD (.atom 0)) D.reads).1)
    (hall : ∀ x ∈ D.reads, VclL.isPathAx x.2 = true) (hwalk : ComplJ8Walk.WalkDepthOK D.reads)
    (j : ℕ) (hj : j < D.cells.length) :
    D.mx.getD j 0 = ((walkRows D.cells D.reads).filter fun t =>
      t.label.node.isCell && decide (Nock.V1J8.Gen.idxOf D.cells t.label.node = j)).length := by
  rw [hmx, mxCounts_eq, ComplJ8Data.bumpAll0_getD _ _ _ hj, ComplJ8OfBal.sumAt_cellPairs]
  have h62 : ∀ r ∈ VclL.pathReads D.reads, VclL.depthOf r.2 ≤ 62 :=
    fun r hr => (hwalk r hr).trans (by norm_num)
  have hperm := ComplJ8OfBal.walkGen_nodes_perm D.cells _ hall h62
  rw [hws, (hperm.filter _).length_eq, List.filter_map, List.length_map]
  rfl

/-- **`cxT_eq_wxT` over a general record**: the cell export terminal equals the walk import terminal. -/
theorem cxT_eq_wxT_gen (D : J8Data p Rg fuel s f r) (hmx : D.mx = Nock.V1J8.Gen.mxCounts D.cells D.ws)
    (hws : D.ws = (Nock.V1J8.Gen.walkGen (D.cells.headD (.atom 0)) D.reads).1)
    (hall : ∀ x ∈ D.reads, VclL.isPathAx x.2 = true) (hwalk : ComplJ8Walk.WalkDepthOK D.reads)
    (hcellsC : ∀ c ∈ D.cells, c.isCell = true)
    (hwcell : ∀ u ∈ walkRows D.cells D.reads, u.label.node ∈ D.cells) (χ : Coins frameJ8 K) :
    cxT δ D χ = wxT δ D χ := by
  set n := D.cells.length
  set XG : ℕ → 𝕂′ := fun j => (FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩
    (xKeyOf δ (cRows δ D χ j) 0))⁻¹ with hXG
  have hW : wxT δ D χ = ((walkRows D.cells D.reads).map fun u => XG (D.cells.idxOf u.label.node)).sum := by
    unfold wxT
    rw [← ComplJ8OfBal.sum_range_getD' (trie (.atom 0) (.atom 0) [] []) _ (walkRows D.cells D.reads)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hmem : (wTrie D.cells D.reads k).label.node ∈ D.cells :=
      hwcell _ (wTrie_mem _ _ (Finset.mem_range.mp hk))
    show (FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (wxKeyV δ (wR δ D χ k)))⁻¹ = _
    rw [show wR δ D χ k = ComplJ8Enc.walkRow0E δ (encR δ χ) D.cells D.reads (VerJ8.chalsMJ8 δ χ 0)
        (VerJ8.chalsMJ8 δ χ 1) k from rfl,
      ComplJ8OfBal.wxKey_eq δ (encR δ χ) (zJ δ χ) (bigOf D) D.cells D.reads (mvF D) (mxF D) (fun _ => 0) _ _ k hmem]
    rfl
  have hS := ComplJ8OfBal.sum_serial n (fun u : NTree WN => D.cells.idxOf u.label.node) XG (walkRows D.cells D.reads)
    (fun u hu => List.idxOf_lt_length_of_mem (hwcell u hu))
  have hC : cxT δ D χ = ∑ j ∈ Finset.range n, ((mxF D j : ℕ) : 𝕂′) * XG j := by
    unfold cxT
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [xTermOf, cellFillInv, hXG, ComplJ8Enc.cellRowsBE, ComplJ8Enc.cellRowBE, ComplJ8Cell.cellRowB, liftQ,
      map_natCast, Nat.cast_zero, map_zero, zero_mul, add_zero]
  rw [hC, hW, hS]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 2
  show D.mx.getD j 0 = _
  rw [mx_spec_gen D hmx hws hall hwalk j (Finset.mem_range.mp hj)]
  congr 1
  refine List.filter_congr fun u hu => ?_
  have hm := hwcell u hu
  rw [hcellsC _ hm, ComplJ8OfBal.genIdxOf_eq _ _ hm]
  simp

/-- **`walkRows_node_cells` over a general read list**: on a child-closed non-empty cell list, if every read is a
defined slot and every cell read root is in the list, every spec walk node is in the list. -/
theorem walkRows_node_cells_gen (cs : List Noun) (reads : List (Noun × ℕ)) (hclosed : ComplJ8Data.ClP cs [])
    (hpos : 0 < cs.length) (hslot : ∀ x ∈ reads, (Noun.slot x.2 x.1).isSome)
    (hroot : ∀ x ∈ reads, x.1.isCell = true → x.1 ∈ cs) :
    ∀ u ∈ walkRows cs reads, u.label.node ∈ cs := by
  have htok : ∀ r, ∀ s ∈ targetsOf reads r, s ≠ [] ∧ (chainWalk r s).isSome := by
    intro r s hs
    refine ⟨targetsOf_ne _ r s hs, ?_⟩
    unfold targetsOf at hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hxk, hxr⟩ := List.mem_filter.mp hx
    have hxr : x.1 = r := of_decide_eq_true hxr
    have hpk := mem_pathKind.mp hxk
    have hsl := hslot x hpk.1
    rw [slot_eq_chainWalk _ (by have := two_le_of_path hpk.2; omega), hxr] at hsl
    exact hsl
  intro u hu
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp hu
  let Q : Noun → List Bool → List (List Bool) → Prop := fun n _ T =>
    n ∈ cs ∧ ∀ s ∈ T, s ≠ [] ∧ (chainWalk n s).isSome
  have hQ : ∀ l r bs T (b : Bool), Q (.cell l r) bs T → cont b T = true →
      Q (if b then r else l) (bs ++ [b]) (contT b T) := by
    intro l r bs T b hq hcont
    obtain ⟨hmem, hT⟩ := hq
    have hT' : ∀ s ∈ contT b T, s ≠ [] ∧ (chainWalk (if b then r else l) s).isSome := by
      intro s hs
      obtain ⟨hbs, hne⟩ := mem_contT hs
      exact ⟨hne, by simpa [chainWalk] using (hT _ hbs).2⟩
    refine ⟨?_, hT'⟩
    obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ (contT_ne_nil hcont)
    obtain ⟨hne, hsome⟩ := hT' s hs
    obtain ⟨b', s', rfl⟩ : ∃ b' s', s = b' :: s' := by
      cases s with
      | nil => exact absurd rfl hne
      | cons b' s' => exact ⟨b', s', rfl⟩
    obtain ⟨x, y, hxy⟩ := ComplJ8OfBal.chainWalk_cons_cell hsome
    have hcl := hclosed l r hmem (by simp)
    cases b
    · simp only [Bool.false_eq_true, if_false] at hxy ⊢; exact hcl.1 x y hxy
    · simp only [if_true] at hxy ⊢; exact hcl.2 x y hxy
  rcases mem_walkForest hc with ⟨-, rfl⟩ | ⟨r, hr, rfl⟩
  · have hq : Q (cs.headD (.atom 0)) [] [] := by
      refine ⟨?_, by simp⟩
      cases h : cs with
      | nil => rw [h] at hpos; simp at hpos
      | cons a l => simp
    obtain ⟨n', bs', T', rfl, hq'⟩ := inTree_trie_inv _ Q hQ hin _ _ _ rfl hq
    rw [(trie_label _ _ _ _).1]; exact hq'.1
  · have hrc : r ∈ cs := by
      obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ (targetsOf_ne_nil hr)
      obtain ⟨hsne, hsome⟩ := htok r s hs
      obtain ⟨b', s', rfl⟩ : ∃ b' s', s = b' :: s' := by
        cases s with
        | nil => exact absurd rfl hsne
        | cons b' s' => exact ⟨b', s', rfl⟩
      obtain ⟨x, y, hxy⟩ := ComplJ8OfBal.chainWalk_cons_cell hsome
      unfold walkRoots at hr
      obtain ⟨z0, hz0, hz0r⟩ := List.mem_map.mp (List.mem_dedup.mp hr)
      have hz := (mem_pathKind.mp hz0).1
      exact hz0r ▸ hroot z0 hz (by rw [hz0r, hxy]; rfl)
    have hq : Q r [] (targetsOf reads r) := ⟨hrc, htok r⟩
    obtain ⟨n', bs', T', rfl, hq'⟩ := inTree_trie_inv _ Q hQ hin _ _ _ rfl hq
    rw [(trie_label _ _ _ _).1]; exact hq'.1

/-- **`balF`'s cell / walk clause over a general record**: the cell fingerprint-export publics are the walk's
fingerprint-import publics. -/
theorem balF1_gen (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hmx : D.mx = Nock.V1J8.Gen.mxCounts D.cells D.ws)
    (hws : D.ws = (Nock.V1J8.Gen.walkGen (D.cells.headD (.atom 0)) D.reads).1)
    (hall : ∀ x ∈ D.reads, VclL.isPathAx x.2 = true) (hwalk : ComplJ8Walk.WalkDepthOK D.reads)
    (hcellsC : ∀ c ∈ D.cells, c.isCell = true)
    (hwcell : ∀ u ∈ walkRows D.cells D.reads, u.label.node ∈ D.cells) (χ : Coins frameJ8 K) :
    pubsCOf δ b D hC o χ 2 = pubsWOf δ b D o' χ 0 ∧ pubsCOf δ b D hC o χ 3 = pubsWOf δ b D o' χ 1 := by
  have he := cxT_eq_wxT_gen δ D hmx hws hall hwalk hcellsC hwcell χ
  exact ⟨by simp [pubsCOf, pubsC0, pubsWOf, pubsW0, pub2, he], by simp [pubsCOf, pubsC0, pubsWOf, pubsW0, pub2, he]⟩

/-- **`balV`'s third clause over a general record**: the atom table's validity publics are zero on a closed atom
cell list. -/
theorem balV3_gen (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hcl : ∀ y ∈ D.acs, ((hdN y).isCell = true → hdN y ∈ D.acs) ∧ ((tlN y).isCell = true → tlN y ∈ D.acs))
    (χ : Coins frameJ8 K) : pubsAOf δ b D hA o χ 0 = 0 ∧ pubsAOf δ b D hA o χ 1 = 0 := by
  have h0 := ComplJ8OfBal.avT_zero_of δ D hcl χ
  have hz : (0 : Quad (algebraMap (ZMod p) K δ)) = Quad.mk _ 0 0 :=
    ((Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩).symm
  exact ⟨by simp [pubsAOf, pubsA1, pubsA0, pub2, h0, hz, Quad.re_mk, Quad.im_mk],
    by simp [pubsAOf, pubsA1, pubsA0, pub2, h0, hz, Quad.re_mk, Quad.im_mk]⟩

end Gen

/-! ## 2. The J-8 instances are recovered -/

section J8
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DD" => j8DataOf p Rg Rt hgen

/-- The J-8 reads are path reads (axis `≥ 2`). -/
theorem hall_j8 : ∀ x ∈ (DD).reads, VclL.isPathAx x.2 = true := by
  intro x hx
  have : (DD).reads = Nock.V1J8.Gen.pathReads (DD).rows := rfl
  rw [this] at hx
  unfold Nock.V1J8.Gen.pathReads at hx
  exact ComplJ8OfBal.isPathAx_of_two_le (by simpa using (List.mem_filter.mp hx).2)

/-- The J-8 cell read roots are in the table. -/
theorem hroot_j8 : ∀ x ∈ (DD).reads, x.1.isCell = true → x.1 ∈ (DD).cells := by
  intro x hx hc
  obtain ⟨row, hrow, hroot⟩ := ComplJ8Data.pathReads_root _ x hx
  rcases ComplJ8Data.handle_noun_cases p Rg Rt hgen hrow hroot with ⟨_, hm⟩ | ⟨v, ev, _⟩ | ⟨v, ev, _⟩
  · exact hm
  · simp [ev, Noun.isCell] at hc
  · simp [ev, Noun.isCell] at hc

/-- **J-8's `walkRows_node_cells` from the generic lemma.** -/
theorem walkRows_node_cells_j8 : ∀ u ∈ walkRows (DD).cells (DD).reads, u.label.node ∈ (DD).cells :=
  walkRows_node_cells_gen _ _ (ComplJ8Data.cells_closed _) (cells_pos Rt hgen) (ComplJ8OfBal.reads_slot Rt hgen)
    (hroot_j8 Rt hgen)

/-- **J-8's `cxT_eq_wxT` from the generic lemma** (same binder `hwalk`, no `hwcell`). -/
theorem cxT_eq_wxT_j8 (hwalk : ComplJ8Walk.WalkDepthOK (DD).reads) (χ : Coins frameJ8 K) :
    cxT δ (DD) χ = wxT δ (DD) χ :=
  cxT_eq_wxT_gen δ (DD) rfl rfl (hall_j8 Rt hgen) hwalk
    (fun c hc => (ComplJ8Walk.cellsOfRoots_mem _ c hc).1) (walkRows_node_cells_j8 Rt hgen) χ

end J8

/-! ## 3. The J-9 A instance -/

section J9A
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf readsA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (WalkDepthOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AObl (HonestJ9A)
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

/-- The J-9 A cell-walk reads are path reads (both parts are filtered at axis `≥ 2`). -/
theorem hall_readsA : ∀ x ∈ (DA).reads, VclL.isPathAx x.2 = true := by
  intro x hx
  have hx' : x ∈ readsA t := hx
  simp only [readsA, List.mem_append] at hx'
  refine ComplJ8OfBal.isPathAx_of_two_le ?_
  rcases hx' with hx' | hx'
  · unfold ComplJ9AReads.walkReadsX9 at hx'
    simpa using (List.mem_filter.mp hx').2
  · unfold ComplJ9AChainsRun.axChainReadsK9 at hx'
    simpa using (List.mem_filter.mp hx').2

/-- **`hfxC` at `BRun9A`**, given the J-9 A walk-node fact `hwcellA` (every node of the J-9 A cell walk is a cell
of the table).  Binder `hwalk9`. -/
theorem hfxC_A (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwcellA : ∀ u ∈ walkRows (DA).cells (DA).reads, u.label.node ∈ (DA).cells) :
    ∀ χ, (BA).Good χ → ((BA).M χ).pubsC 2 = ((BA).M χ).pubsW 0 ∧ ((BA).M χ).pubsC 3 = ((BA).M χ).pubsW 1 := by
  intro χ _
  rw [ComplJ9AOfMem.pubsC_eq, ComplJ9AOfMem.pubsW_eq]
  exact balF1_gen δ b (DA) (ComplJ9ADataRec.cellsA_pos Rt hgen) (orbJ8 (DA) (hF_run Rt hgen hpG h31A))
    (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) rfl rfl (hall_readsA Rt hgen)
    (ComplJ9ADataRec.walkDepthOK_readsA Rt hgen hwalk9)
    (fun c hc => (ComplJ8Walk.cellsOfRoots_mem _ c hc).1) hwcellA χ

/-- **`hfxC` at `BRun9A` from the read facts** (`walkRows_node_cells_gen`): every J-9 A cell-walk read is a defined
slot, and its root, when a cell, is in the table. -/
theorem hfxC_A_of (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hslotA : ∀ x ∈ readsA t, (Noun.slot x.2 x.1).isSome)
    (hrootA : ∀ x ∈ readsA t, x.1.isCell = true → x.1 ∈ (j8DataOf p Rg Rt hgen).cells) :
    ∀ χ, (BA).Good χ → ((BA).M χ).pubsC 2 = ((BA).M χ).pubsW 0 ∧ ((BA).M χ).pubsC 3 = ((BA).M χ).pubsW 1 :=
  hfxC_A δ b Rt hgen hpG h31A hwalk9
    (walkRows_node_cells_gen _ _ (ComplJ8Data.cells_closed _) (ComplJ9ADataRec.cellsA_pos Rt hgen) hslotA hrootA)

/-- **`hvalA0` at `BRun9A`** (every coin; the atom table's validity publics are zero). -/
theorem hvalA0_A : ∀ χ, (BA).Good χ → ((BA).M χ).pubsA 0 = 0 ∧ ((BA).M χ).pubsA 1 = 0 := by
  intro χ _
  rw [ComplJ9AOfMem.pubsA_eq]
  exact balV3_gen δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) (orbJ8 (DA) (hF_run Rt hgen hpG h31A))
    (ComplJ8OfBal.acs_closed_run Rt hgen hpG) χ

end J9A

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalGen

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalGen
#print axioms mx_spec_gen
#print axioms cxT_eq_wxT_gen
#print axioms walkRows_node_cells_gen
#print axioms balF1_gen
#print axioms balV3_gen
#print axioms walkRows_node_cells_j8
#print axioms cxT_eq_wxT_j8
#print axioms hall_readsA
#print axioms hfxC_A
#print axioms hfxC_A_of
#print axioms hvalA0_A
end Axioms
