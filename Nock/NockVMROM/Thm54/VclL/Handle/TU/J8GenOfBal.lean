/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/J8GenOfBal.lean

 **J-8 completeness over any admissible `J8Data`, continued**: the balances `balF`, `balV` of `ComplJ8OfBal`; the J-8 walk and atom-walk reads enter only through membership
 (`O.permR`) and the walk-node permutation `walkGen_nodes_perm`.
 Every declaration is the corresponding statement and proof over `j8DataGen … O` (suffix `G`), except where the
 free list orders need a membership or permutation step.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.J8GenOf
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal

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

/-! ### Twins of `ComplJ8OfBal` -/

section ComplJ8OfBalG_1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data)
noncomputable section
section AtomRunJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.Edit Nock.Edit.GenX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
/-- **The run's atom cell list is closed under cell children** (Goldilocks). -/
theorem acs_closed_runG (hpG : p = Nock.Atoms.p) :
    ∀ y ∈ (j8DataGen p Rg Rt hgen O).acs, ((hdN y).isCell = true → hdN y ∈ (j8DataGen p Rg Rt hgen O).acs) ∧
      ((tlN y).isCell = true → tlN y ∈ (j8DataGen p Rg Rt hgen O).acs) := by
  subst hpG
  exact acsP_closed _ _ fun a ha => ((ComplJ8Atom.mem_bigsP _ _ _ a).mp ha).2

/-- **`balV`'s third clause at the run**: the atom table's validity publics are zero (at every coin). -/
theorem balV3_runG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) (χ : Coins frameJ8 K) :
    ((BRunG δ b Rt hgen O o).M χ).pubsA 0 = 0 ∧ ((BRunG δ b Rt hgen O o).M χ).pubsA 1 = 0 := by
  have h0 := avT_zero_of δ (j8DataGen p Rg Rt hgen O) (acs_closed_runG Rt hgen O hpG) χ
  have hz : (0 : Quad (algebraMap (ZMod p) K δ)) = Quad.mk _ 0 0 :=
    ((Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩).symm
  refine ⟨?_, ?_⟩
  · show pubsAOf δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) o χ 0 = 0
    simp [pubsAOf, pubsA1, pubsA0, pub2, h0, hz, Quad.re_mk, Quad.im_mk]
  · show pubsAOf δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) o χ 1 = 0
    simp [pubsAOf, pubsA1, pubsA0, pub2, h0, hz, Quad.re_mk, Quad.im_mk]

end AtomRunJ8
section JRun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bal (Tab tot tots tabOfRows tot_tabOfRows_fin fS)
open Nock.Jet.RapJetJ8 (dJX dJ coinsJ coinsJX consKT keyK)
open Nock.Jet.ChipJ8T.HonestRAP (termJ sX)
open Nock.NockVMROM.Thm54.FiniteIO (compress)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Edit Nock.Edit.GenX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
/-- **`h1J`: the J export public is the J export table's total** (at every coin). -/
theorem h1J_runG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) (χ : Coins frameJ8 K) :
    Quad.mk _ (((BRunG δ b Rt hgen O o).M χ).pubsJ 2) (((BRunG δ b Rt hgen O o).M χ).pubsJ 3) =
      tots δ (fH δ b χ) [tabJX δ (j8DataGen p Rg Rt hgen O)] := by
  show Quad.mk _ (pubsJOf δ (j8DataGen p Rg Rt hgen O) χ 2) (pubsJOf δ (j8DataGen p Rg Rt hgen O) χ 3) = _
  have e0 : pubsJOf δ (j8DataGen p Rg Rt hgen O) χ 2 = pub2 δ (∑ k, sX δ (chalsJJ8 χ) ((j8DataGen p Rg Rt hgen O).jrows.get k)) 2 := by
    simp [pubsJOf]
  have e1 : pubsJOf δ (j8DataGen p Rg Rt hgen O) χ 3 = pub2 δ (∑ k, sX δ (chalsJJ8 χ) ((j8DataGen p Rg Rt hgen O).jrows.get k)) 3 := by
    simp [pubsJOf]
  have h2 := pub2_mk2 δ (∑ k, sX δ (chalsJJ8 χ) ((j8DataGen p Rg Rt hgen O).jrows.get k)) 2 rfl
  rw [show (2 : ℕ) + 1 = 3 from rfl] at h2
  rw [e0, e1, h2]
  simp only [tots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, tabJX, tot_mapTab, ← dJX_eq]
  have := tot_tabOfRows_fin (R := 𝕂′) (dJX δ (chalsJJ8 χ)) (j8DataGen p Rg Rt hgen O).jrows.get
    (Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.entsX) (fun _ => ([] : List (List (ZMod p) × 𝕂′)))
  simp only [List.map_nil, List.sum_nil, sub_zero] at this
  rw [← this]
  rfl

end JRun
section BalF
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.Edit Nock.Edit.GenX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
/-- **The cell export multiplicity counts the spec walk rows at the serial** (cell nodes). -/
theorem mx_specG (hwalk : ComplJ8Walk.WalkDepthOK (j8DataGen p Rg Rt hgen O).reads) (j : ℕ)
    (hj : j < (j8DataGen p Rg Rt hgen O).cells.length) :
    (j8DataGen p Rg Rt hgen O).mx.getD j 0 =
      ((walkRows (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).reads).filter fun t =>
        t.label.node.isCell && decide (Nock.V1J8.Gen.idxOf (j8DataGen p Rg Rt hgen O).cells t.label.node = j)).length := by
  rw [mx_eq_cntG p Rg Rt hgen O j hj, ComplJ8Data.cnt_eq_sumAt]
  simp only [ComplJ8Data.wRecs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [sumAt_cellPairs]
  have hall : ∀ x ∈ (j8DataGen p Rg Rt hgen O).reads, VclL.isPathAx x.2 = true := by
    intro x hx
    have hx := (O.permR _ _).mem_iff.mp hx
    unfold Nock.V1J8.Gen.pathReads at hx
    exact isPathAx_of_two_le (by simpa using (List.mem_filter.mp hx).2)
  have h62 : ∀ r ∈ VclL.pathReads (j8DataGen p Rg Rt hgen O).reads, VclL.depthOf r.2 ≤ 62 :=
    fun r hr => (hwalk r hr).trans (by norm_num)
  have hperm := walkGen_nodes_perm (j8DataGen p Rg Rt hgen O).cells _ hall h62
  have hws : (j8DataGen p Rg Rt hgen O).ws =
      (Nock.V1J8.Gen.walkGen ((j8DataGen p Rg Rt hgen O).cells.headD (.atom 0)) (j8DataGen p Rg Rt hgen O).reads).1 := rfl
  rw [hws, (hperm.filter _).length_eq, List.filter_map, List.length_map]
  rfl

/-- **The cell export terminal equals the walk import terminal** (every spec walk node a cell of the table). -/
theorem cxT_eq_wxTG (hwalk : ComplJ8Walk.WalkDepthOK (j8DataGen p Rg Rt hgen O).reads)
    (hwcell : ∀ u ∈ walkRows (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).reads,
      u.label.node ∈ (j8DataGen p Rg Rt hgen O).cells) (χ : Coins frameJ8 K) :
    cxT δ (j8DataGen p Rg Rt hgen O) χ = wxT δ (j8DataGen p Rg Rt hgen O) χ := by
  set D := j8DataGen p Rg Rt hgen O with hD
  set n := D.cells.length
  set XG : ℕ → 𝕂′ := fun j => (FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩
    (xKeyOf δ (cRows δ D χ j) 0))⁻¹ with hXG
  have hcellsC : ∀ c ∈ D.cells, c.isCell = true := fun c hc => (ComplJ8Walk.cellsOfRoots_mem _ c ((O.permC _).mem_iff.mp hc)).1
  -- the walk side
  have hW : wxT δ D χ = ((walkRows D.cells D.reads).map fun u => XG (D.cells.idxOf u.label.node)).sum := by
    unfold wxT
    rw [← sum_range_getD' (trie (.atom 0) (.atom 0) [] []) _ (walkRows D.cells D.reads)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hmem : (wTrie D.cells D.reads k).label.node ∈ D.cells :=
      hwcell _ (wTrie_mem _ _ (Finset.mem_range.mp hk))
    show (FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (wxKeyV δ (wR δ D χ k)))⁻¹ = _
    rw [show wR δ D χ k = ComplJ8Enc.walkRow0E δ (encR δ χ) D.cells D.reads (VerJ8.chalsMJ8 δ χ 0)
        (VerJ8.chalsMJ8 δ χ 1) k from rfl,
      wxKey_eq δ (encR δ χ) (zJ δ χ) (bigOf D) D.cells D.reads (mvF D) (mxF D) (fun _ => 0) _ _ k hmem]
    rfl
  have hS := sum_serial n (fun u : NTree WN => D.cells.idxOf u.label.node) XG (walkRows D.cells D.reads)
    (fun u hu => List.idxOf_lt_length_of_mem (hwcell u hu))
  -- the cell side
  have hC : cxT δ D χ = ∑ j ∈ Finset.range n, ((mxF D j : ℕ) : 𝕂′) * XG j := by
    unfold cxT
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [xTermOf, cellFillInv, hXG, ComplJ8Enc.cellRowsBE, ComplJ8Enc.cellRowBE, ComplJ8Cell.cellRowB, liftQ,
      map_natCast, Nat.cast_zero, map_zero, zero_mul, add_zero]
  rw [hC, hW, hS]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 2
  show D.mx.getD j 0 = _
  rw [mx_specG Rt hgen O hwalk j (Finset.mem_range.mp hj)]
  congr 1
  refine List.filter_congr fun u hu => ?_
  have hm := hwcell u hu
  rw [hcellsC _ hm, ComplJ8OfBal.genIdxOf_eq _ _ hm]
  simp

/-- Every read of the run is a defined slot (`consEntriesX_sound` at the run's rows). -/
theorem reads_slotG : ∀ x ∈ (j8DataGen p Rg Rt hgen O).reads, (Noun.slot x.2 x.1).isSome := by
  intro x hx
  have hx' : x ∈ Nock.V1J8.Gen.pathReads (j8DataGen p Rg Rt hgen O).rows := (O.permR _ _).mem_iff.mp hx
  unfold Nock.V1J8.Gen.pathReads at hx'
  obtain ⟨hx', -⟩ := List.mem_filter.mp hx'
  obtain ⟨row, hrow, hx'⟩ := List.mem_flatMap.mp hx'
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx'
  have hrow' : row ∈ ((bfsForest [t]).map fun u => rowOfSkelX u.label) := by
    have : (j8DataGen p Rg Rt hgen O).rows.toList = (bfsForest [t]).map fun u => rowOfSkelX u.label := by
      show (ComplJ8Data.rowsOfT t).toList = _
      simp [ComplJ8Data.rowsOfT]
    rwa [this] at hrow
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hrow'
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp hu
  rw [List.mem_singleton] at hc; subst hc
  have := (consEntriesX_sound u.label (inTree_rowSem hgen hin) e he).2
  simp [this]

/-- **Every spec J-8 walk node is a cell of the table** (the run's reads are defined slots; the cell list is
child-closed and contains every cell read root). -/
theorem walkRows_node_cellsG : ∀ u ∈ walkRows (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).reads,
    u.label.node ∈ (j8DataGen p Rg Rt hgen O).cells := by
  set D := j8DataGen p Rg Rt hgen O with hD
  have hclosed : ComplJ8Data.ClP D.cells [] := cells_closedG p Rg Rt hgen O
  have htok : ∀ r, ∀ s ∈ targetsOf D.reads r, s ≠ [] ∧ (chainWalk r s).isSome := by
    intro r s hs
    refine ⟨targetsOf_ne _ r s hs, ?_⟩
    unfold targetsOf at hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hxk, hxr⟩ := List.mem_filter.mp hx
    have hxr : x.1 = r := of_decide_eq_true hxr
    have hpk := mem_pathKind.mp hxk
    have hsl := reads_slotG Rt hgen O x hpk.1
    rw [slot_eq_chainWalk _ (by have := two_le_of_path hpk.2; omega), hxr] at hsl
    exact hsl
  intro u hu
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp hu
  let Q : Noun → List Bool → List (List Bool) → Prop := fun n _ T =>
    n ∈ D.cells ∧ ∀ s ∈ T, s ≠ [] ∧ (chainWalk n s).isSome
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
    obtain ⟨x, y, hxy⟩ := chainWalk_cons_cell hsome
    have hcl := hclosed l r hmem (by simp)
    cases b
    · simp only [Bool.false_eq_true, if_false] at hxy ⊢; exact hcl.1 x y hxy
    · simp only [if_true] at hxy ⊢; exact hcl.2 x y hxy
  rcases mem_walkForest hc with ⟨-, rfl⟩ | ⟨r, hr, rfl⟩
  · have hq : Q (D.cells.headD (.atom 0)) [] [] := by
      refine ⟨?_, by simp⟩
      have : 0 < D.cells.length := cells_posG (p := p) Rt hgen O
      cases h : D.cells with
      | nil => rw [h] at this; simp at this
      | cons a l => simp
    obtain ⟨n', bs', T', rfl, hq'⟩ := inTree_trie_inv _ Q hQ hin _ _ _ rfl hq
    rw [(trie_label _ _ _ _).1]; exact hq'.1
  · have hrc : r ∈ D.cells := by
      obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ (targetsOf_ne_nil hr)
      obtain ⟨hsne, hsome⟩ := htok r s hs
      obtain ⟨b', s', rfl⟩ : ∃ b' s', s = b' :: s' := by
        cases s with
        | nil => exact absurd rfl hsne
        | cons b' s' => exact ⟨b', s', rfl⟩
      obtain ⟨x, y, hxy⟩ := chainWalk_cons_cell hsome
      unfold walkRoots at hr
      obtain ⟨z0, hz0, hz0r⟩ := List.mem_map.mp (List.mem_dedup.mp hr)
      obtain ⟨row, hrow, hroot⟩ := ComplJ8Data.pathReads_root _ z0 ((O.permR _ _).mem_iff.mp (mem_pathKind.mp hz0).1)
      rw [hz0r] at hroot
      rcases handle_noun_casesG p Rg Rt hgen O hrow hroot with ⟨_, hm⟩ | ⟨v, ev, _⟩ | ⟨v, ev, _⟩
      · exact hm
      · rw [hxy] at ev; cases ev
      · rw [hxy] at ev; cases ev
    have hq : Q r [] (targetsOf D.reads r) := ⟨hrc, htok r⟩
    obtain ⟨n', bs', T', rfl, hq'⟩ := inTree_trie_inv _ Q hQ hin _ _ _ rfl hq
    rw [(trie_label _ _ _ _).1]; exact hq'.1

/-- **`balF`'s first clause at the run** (every coin): the cell fingerprint-export publics are the J-8 walk's
fingerprint-import publics. -/
theorem balF1_runG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataGen p Rg Rt hgen O).reads)
 (χ : Coins frameJ8 K) :
    ((BRunG δ b Rt hgen O o).M χ).pubsC 2 = ((BRunG δ b Rt hgen O o).M χ).pubsW 0 ∧
    ((BRunG δ b Rt hgen O o).M χ).pubsC 3 = ((BRunG δ b Rt hgen O o).M χ).pubsW 1 := by
  have he := cxT_eq_wxTG δ Rt hgen O hwalk (walkRows_node_cellsG Rt hgen O) χ
  refine ⟨?_, ?_⟩
  · show pubsCOf δ b (j8DataGen p Rg Rt hgen O) (cells_posG Rt hgen O) o χ 2 =
      pubsWOf δ b (j8DataGen p Rg Rt hgen O) o χ 0
    simp [pubsCOf, pubsC0, pubsWOf, pubsW0, pub2, he]
  · show pubsCOf δ b (j8DataGen p Rg Rt hgen O) (cells_posG Rt hgen O) o χ 3 =
      pubsWOf δ b (j8DataGen p Rg Rt hgen O) o χ 1
    simp [pubsCOf, pubsC0, pubsWOf, pubsW0, pub2, he]

/-- **`balF` at the run**, in `OpenJ8`'s form, with the atom / atom-walk clause carried (`hAV`). -/
theorem balF_runG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataGen p Rg Rt hgen O).reads)
    (hAV : ∀ χ, (BRunG δ b Rt hgen O o).Good χ →
      ((BRunG δ b Rt hgen O o).M χ).pubsA 2 = ((BRunG δ b Rt hgen O o).M χ).pubsV 0 ∧
      ((BRunG δ b Rt hgen O o).M χ).pubsA 3 = ((BRunG δ b Rt hgen O o).M χ).pubsV 1) :
    ∀ χ, (BRunG δ b Rt hgen O o).Good χ →
      (((BRunG δ b Rt hgen O o).M χ).pubsC 2 = ((BRunG δ b Rt hgen O o).M χ).pubsW 0 ∧
        ((BRunG δ b Rt hgen O o).M χ).pubsC 3 = ((BRunG δ b Rt hgen O o).M χ).pubsW 1) ∧
      (((BRunG δ b Rt hgen O o).M χ).pubsA 2 = ((BRunG δ b Rt hgen O o).M χ).pubsV 0 ∧
        ((BRunG δ b Rt hgen O o).M χ).pubsA 3 = ((BRunG δ b Rt hgen O o).M χ).pubsV 1) :=
  fun χ hχ => ⟨balF1_runG δ b Rt hgen O o hpG h31 hwalk χ, hAV χ hχ⟩

end BalF
section BalFA
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.Edit Nock.Edit.GenX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
/-- The atom-walk reads: a two-limb big atom's comb at axis `2` or `3`. -/
theorem preads_shapeG
    (hbig : ∀ a ∈ (j8DataGen p Rg Rt hgen O).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1]) :
    ∀ x ∈ (j8DataGen p Rg Rt hgen O).preads, ∃ a ∈ (j8DataGen p Rg Rt hgen O).bigs,
      x.1 = Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a) ∧ (x.2 = 2 ∨ x.2 = 3) := by
  set D := j8DataGen p Rg Rt hgen O with hD
  intro x hx
  have hx' : x ∈ ComplJ8Data.pairReadsP D.H D.pd D.rows := (O.permR _ _).mem_iff.mp hx
  unfold ComplJ8Data.pairReadsP at hx'
  obtain ⟨row, hrow, hx'⟩ := List.mem_flatMap.mp hx'
  split_ifs at hx' with hpair
  swap
  · simp at hx'
  simp only [Nock.V1J8.FillX.isPairB, Bool.and_eq_true, decide_eq_true_eq] at hpair
  obtain ⟨⟨⟨-, -⟩, h1⟩, h2⟩ := hpair
  -- the two leaves are big atoms of the run
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
  have hpd : (D.pd row).1 = 2 ∨ (D.pd row).1 = 3 := by
    have e : D.pd row = HonestPairX.pdX (ComplJ8Data.sxPP p D.acs D.rows) row := rfl
    rw [e]
    unfold HonestPairX.pdX
    rw [ha', hc']
    simp only [(hbig a ha).2, (hbig c hc).2, HonestPairX.combFD]
    split_ifs <;> simp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
  rcases hx' with rfl | rfl
  · exact ⟨a, ha, by rw [ha']; rfl, hpd⟩
  · exact ⟨c, hc, by rw [hc']; rfl, hpd⟩

end BalFA
section BalFA2
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.Edit Nock.Edit.GenX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
theorem vs_eqG (hne : (j8DataGen p Rg Rt hgen O).preads ≠ []) :
    (j8DataGen p Rg Rt hgen O).vs =
      (Nock.V1J8.Gen.walkGen ((j8DataGen p Rg Rt hgen O).acs.headD (.atom 0)) (j8DataGen p Rg Rt hgen O).preads).1 := by
  have h : (j8DataGen p Rg Rt hgen O).vs = (if (j8DataGen p Rg Rt hgen O).preads.isEmpty then
      (([], 0) : List Nock.V1J8.Gen.WRow × ℕ)
      else Nock.V1J8.Gen.walkGen Nock.V1J8.Gen.padN (j8DataGen p Rg Rt hgen O).preads).1 := rfl
  rw [h, if_neg (by simpa using hne)]
  exact walkGen_dummy _ _ _ hne

theorem vs_nilG (h0 : (j8DataGen p Rg Rt hgen O).preads = []) : (j8DataGen p Rg Rt hgen O).vs = [] := by
  have h : (j8DataGen p Rg Rt hgen O).vs = (if (j8DataGen p Rg Rt hgen O).preads.isEmpty then
      (([], 0) : List Nock.V1J8.Gen.WRow × ℕ)
      else Nock.V1J8.Gen.walkGen Nock.V1J8.Gen.padN (j8DataGen p Rg Rt hgen O).preads).1 := rfl
  rw [h, if_pos (by rw [h0]; rfl)]

/-- **The atom export multiplicity counts the spec atom-walk rows at the serial** (`rIAP = idxN`). -/
theorem mxA_specG (hrI : ComplJ8Data.rIAP p (j8DataGen p Rg Rt hgen O).acs = Nock.V1J8.Gen.idxN (j8DataGen p Rg Rt hgen O).acs)
    (hne : (j8DataGen p Rg Rt hgen O).preads ≠ [])
    (hall : ∀ x ∈ (j8DataGen p Rg Rt hgen O).preads, VclL.isPathAx x.2 = true)
    (h62 : ∀ r ∈ VclL.pathReads (j8DataGen p Rg Rt hgen O).preads, VclL.depthOf r.2 ≤ 62) (j : ℕ)
    (hj : j < (j8DataGen p Rg Rt hgen O).acs.length) :
    (j8DataGen p Rg Rt hgen O).mxA.getD j 0 =
      ((walkRows (j8DataGen p Rg Rt hgen O).acs (j8DataGen p Rg Rt hgen O).preads).filter fun t =>
        t.label.node.isCell && decide (Nock.V1J8.Gen.idxOf (j8DataGen p Rg Rt hgen O).acs t.label.node = j)).length := by
  rw [mxA_eq_cntG p Rg Rt hgen O j hj, ComplJ8Data.cnt_eq_sumAt]
  simp only [ComplJ8Data.awRecs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [hrI, wPairs_idxN, sumAt_cellPairs, vs_eqG Rt hgen O hne]
  have hperm := walkGen_nodes_perm (j8DataGen p Rg Rt hgen O).acs _ hall h62
  rw [(hperm.filter _).length_eq, List.filter_map, List.length_map]
  rfl

theorem acs_cellG (hpG : p = Nock.Atoms.p) : ∀ c ∈ (j8DataGen p Rg Rt hgen O).acs, c.isCell = true := by
  subst hpG
  intro c hc
  obtain ⟨l, h2, -, rfl, -⟩ := ComplJ8Atom.shape_acsP _ _
    (fun a ha => ((ComplJ8Atom.mem_bigsP _ _ _ a).mp ha).2) c hc
  exact combOf_isCell l h2

/-- **The atom export terminal equals the atom-walk import terminal** (atom walk present). -/
theorem axT_eq_vxTG (hpG : p = Nock.Atoms.p)
    (hrI : ComplJ8Data.rIAP p (j8DataGen p Rg Rt hgen O).acs = Nock.V1J8.Gen.idxN (j8DataGen p Rg Rt hgen O).acs)
    (hne : (j8DataGen p Rg Rt hgen O).preads ≠ [])
    (hall : ∀ x ∈ (j8DataGen p Rg Rt hgen O).preads, VclL.isPathAx x.2 = true)
    (h62 : ∀ r ∈ VclL.pathReads (j8DataGen p Rg Rt hgen O).preads, VclL.depthOf r.2 ≤ 62)
    (hwcell : ∀ u ∈ walkRows (j8DataGen p Rg Rt hgen O).acs (j8DataGen p Rg Rt hgen O).preads,
      u.label.node ∈ (j8DataGen p Rg Rt hgen O).acs) (χ : Coins frameJ8 K) :
    axT δ (j8DataGen p Rg Rt hgen O) χ = vxT δ (j8DataGen p Rg Rt hgen O) χ := by
  have hcellsC := acs_cellG Rt hgen O hpG
  have hspec := mxA_specG Rt hgen O hrI hne hall h62
  set D := j8DataGen p Rg Rt hgen O with hD
  set n := D.acs.length
  set XG : ℕ → 𝕂′ := fun j => (FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩
    (xKeyOf δ (aRows δ D χ j) 0))⁻¹ with hXG
  have hnV : nVOf D = (walkRows D.acs D.preads).length := by unfold nVOf; rw [if_neg hne]
  have hW : vxT δ D χ = ((walkRows D.acs D.preads).map fun u => XG (D.acs.idxOf u.label.node)).sum := by
    unfold vxT
    rw [hnV, ← sum_range_getD' (trie (.atom 0) (.atom 0) [] []) _ (walkRows D.acs D.preads)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hmem : (wTrie D.acs D.preads k).label.node ∈ D.acs :=
      hwcell _ (wTrie_mem _ _ (Finset.mem_range.mp hk))
    show (FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (wxKeyV δ (vR δ D χ k)))⁻¹ = _
    rw [show vR δ D χ k = walkRow0 δ (zA δ χ) D.acs D.preads (ChalsAZJ8.chalsAJ8Z δ χ 0)
        (ChalsAZJ8.chalsAJ8Z δ χ 1) k from rfl,
      wxKey_eq0 δ (zA δ χ) (fun _ => none) D.acs D.preads (mvA D) (mxAF D) (fun _ => 0) _ _ k hmem]
    rfl
  have hS := sum_serial n (fun u : NTree WN => D.acs.idxOf u.label.node) XG (walkRows D.acs D.preads)
    (fun u hu => List.idxOf_lt_length_of_mem (hwcell u hu))
  have hC : axT δ D χ = ∑ j ∈ Finset.range n, ((mxAF D j : ℕ) : 𝕂′) * XG j := by
    unfold axT
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [xTermOf, cellFillInv, hXG, ComplJ8Cell.cellRowsBP, ComplJ8Cell.cellRowBP, ComplJ8Cell.cellRowsB,
      ComplJ8Cell.cellRowB, liftQ, map_natCast,
      Nat.cast_zero, map_zero, zero_mul, add_zero]
  rw [hC, hW, hS]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 2
  show D.mxA.getD j 0 = _
  rw [hspec j (Finset.mem_range.mp hj)]
  congr 1
  refine List.filter_congr fun u hu => ?_
  have hm := hwcell u hu
  rw [hcellsC _ hm, ComplJ8OfBal.genIdxOf_eq _ _ hm]
  simp

/-- With no atom-walk read the atom export terminal is zero. -/
theorem axT_zeroG (h0 : (j8DataGen p Rg Rt hgen O).preads = []) (χ : Coins frameJ8 K) :
    axT δ (j8DataGen p Rg Rt hgen O) χ = 0 := by
  unfold axT
  refine Finset.sum_eq_zero fun j hj => ?_
  have hm : (j8DataGen p Rg Rt hgen O).mxA.getD j 0 = 0 := by
    rw [mxA_eq_cntG p Rg Rt hgen O j (Finset.mem_range.mp hj), ComplJ8Data.cnt_eq_sumAt]
    simp [ComplJ8Data.awRecs, vs_nilG Rt hgen O h0, ComplJ8Data.wPairs, ComplJ8Data.sumAt]
  simp only [xTermOf, cellFillInv, ComplJ8Cell.cellRowsBP, ComplJ8Cell.cellRowBP, ComplJ8Cell.cellRowsB,
    ComplJ8Cell.cellRowB, liftQ, mxAF, hm,
    Nat.cast_zero, map_zero, zero_mul, add_zero]

theorem comb_mem_acsG (hpG : p = Nock.Atoms.p) {a : ℕ} (ha : a ∈ (j8DataGen p Rg Rt hgen O).bigs)
    (h2 : 2 ≤ (Nock.Atoms.limbs a).length) :
    Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a) ∈ (j8DataGen p Rg Rt hgen O).acs := by
  subst hpG
  rw [data_acsG hgen O]
  exact (ComplJ8Atom.mem_acsP _ _ _).mpr (Or.inl ((ComplJ8Atom.mem_spineL _ _).mpr
    ⟨a, ha, (ComplJ8Atom.mem_spineOf _ _).mpr ⟨0, by simpa using h2, by simp⟩⟩))

/-- **`balF`'s atom / atom-walk clause at the run** (every coin), from two facts: every big atom has
the two limbs `[a + 1 − p, B − 1]`, and the atom walk's root serial map is `idxN`. -/
theorem balF2_runG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hbig : ∀ a ∈ (j8DataGen p Rg Rt hgen O).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1])
    (hrI : ComplJ8Data.rIAP p (j8DataGen p Rg Rt hgen O).acs = Nock.V1J8.Gen.idxN (j8DataGen p Rg Rt hgen O).acs)
    (χ : Coins frameJ8 K) :
    ((BRunG δ b Rt hgen O o).M χ).pubsA 2 = ((BRunG δ b Rt hgen O o).M χ).pubsV 0 ∧
    ((BRunG δ b Rt hgen O o).M χ).pubsA 3 = ((BRunG δ b Rt hgen O o).M χ).pubsV 1 := by
  have hsh := preads_shapeG Rt hgen O hbig
  have hall : ∀ x ∈ (j8DataGen p Rg Rt hgen O).preads, VclL.isPathAx x.2 = true := by
    intro x hx
    obtain ⟨a, -, -, h⟩ := hsh x hx
    exact isPathAx_of_two_le (by omega)
  have h62 : ∀ r ∈ VclL.pathReads (j8DataGen p Rg Rt hgen O).preads, VclL.depthOf r.2 ≤ 62 := by
    intro x hx
    have hx' : x ∈ (j8DataGen p Rg Rt hgen O).preads := by
      unfold VclL.pathReads at hx
      exact (List.mem_filter.mp (List.mem_dedup.mp hx)).1
    obtain ⟨a, -, -, h⟩ := hsh x hx'
    exact depthOf_le_of h
  have hwcell : ∀ u ∈ walkRows (j8DataGen p Rg Rt hgen O).acs (j8DataGen p Rg Rt hgen O).preads,
      u.label.node ∈ (j8DataGen p Rg Rt hgen O).acs := by
    refine walkRows_nodes_mem _ _ (List.ne_nil_of_length_pos (acs_posG (p := p) Rt hgen O))
      (acs_closed_runG Rt hgen O hpG) ?_
    intro x hx _
    obtain ⟨a, ha, h1, h2⟩ := hsh x hx
    have hl := (hbig a ha).2
    refine ⟨h1 ▸ comb_mem_acsG Rt hgen O hpG ha (by rw [hl]; simp), ?_⟩
    rw [h1, hl]
    rcases h2 with h | h <;> rw [h, slot_eq_chainWalk _ (by norm_num)] <;> rfl
  have hz : (0 : Quad (algebraMap (ZMod p) K δ)) = Quad.mk _ 0 0 :=
    ((Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩).symm
  refine ⟨?_, ?_⟩
  · show pubsAOf δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) o χ 2 =
      pubsVOf δ b (j8DataGen p Rg Rt hgen O) o χ 0
    by_cases h0 : (j8DataGen p Rg Rt hgen O).preads = []
    · simp [pubsAOf, pubsA1, pubsA0, pubsVOf, pub2, h0, axT_zeroG δ Rt hgen O h0, hz, Quad.re_mk]
    · simp [pubsAOf, pubsA1, pubsA0, pubsVOf, pubsV0, pub2, h0,
        axT_eq_vxTG δ Rt hgen O hpG hrI h0 hall h62 hwcell χ]
  · show pubsAOf δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) o χ 3 =
      pubsVOf δ b (j8DataGen p Rg Rt hgen O) o χ 1
    by_cases h0 : (j8DataGen p Rg Rt hgen O).preads = []
    · simp [pubsAOf, pubsA1, pubsA0, pubsVOf, pub2, h0, axT_zeroG δ Rt hgen O h0, hz, Quad.im_mk]
    · simp [pubsAOf, pubsA1, pubsA0, pubsVOf, pubsV0, pub2, h0,
        axT_eq_vxTG δ Rt hgen O hpG hrI h0 hall h62 hwcell χ]

/-- **`balF` at the run, closed** (`OpenJ8`'s form, nothing carried): at `complJ8`'s binders `hpG hop5 hclA hRt
h31` (`bigBound_singleG`) and the walk binder `hwalk`. -/
theorem balF_closedG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (hop5 : ComplJ8.ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataGen p Rg Rt hgen O).reads) :
    ∀ χ, (BRunG δ b Rt hgen O o).Good χ →
      (((BRunG δ b Rt hgen O o).M χ).pubsC 2 = ((BRunG δ b Rt hgen O o).M χ).pubsW 0 ∧
        ((BRunG δ b Rt hgen O o).M χ).pubsC 3 = ((BRunG δ b Rt hgen O o).M χ).pubsW 1) ∧
      (((BRunG δ b Rt hgen O o).M χ).pubsA 2 = ((BRunG δ b Rt hgen O o).M χ).pubsV 0 ∧
        ((BRunG δ b Rt hgen O o).M χ).pubsA 3 = ((BRunG δ b Rt hgen O o).M χ).pubsV 1) := by
  have hN : (j8DataGen p Rg Rt hgen O).rows.size ≤ 2 ^ 31 := by
    have h := h31 (bfsForest [(j8DataGen p Rg Rt hgen O).t]).length (by simp [sizesJ8])
    rw [data_rowsG hgen O]
    simpa [ComplJ8Data.rowsOfT, j8DataGen] using h
  obtain ⟨hb, -, -, -, -, -, hrI, -, -⟩ := bigBound_singleG hgen O hpG (hclA 0) (hclA 1) hRt hop5 hN
  exact balF_runG δ b Rt hgen O o hpG h31 hwalk fun χ _ =>
    balF2_runG δ b Rt hgen O o hpG h31 (fun a ha => ⟨(hb a ha).1, (hb a ha).2.2⟩) hrI χ

end BalFA2
section BalV2
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.Edit Nock.Edit.GenX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
/-- The atom cell list's rows are cells of two small atoms (every big atom has two limbs). -/
theorem acs_twoG (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
    (hpG : p = Nock.Atoms.p)
    (hb : ∀ a ∈ (j8DataGen p Rg Rt hgen O).bigs, p ≤ a ∧ a < p + 2 ^ 31) :
    ∀ y ∈ (j8DataGen p Rg Rt hgen O).acs, ∃ x z, y = Noun.cell (.atom x) (.atom z) ∧ x < p ∧ z < p := by
  subst hpG
  have hp : Nock.Atoms.p = 18446744069414584321 := by simp [Nock.Atoms.p, Nock.Field.p]
  have hB := Nock.Atoms.B_eq
  intro y hy
  rw [data_acsG hgen O, (ComplJ8BigBound.acsP_two _ hb).2] at hy
  rcases List.mem_append.mp hy with hy | hy
  · have hy' := ((ComplJ8Atom.linkOrder_spec _ (ComplJ8Atom.spineL_cells _)).2.1 y).1 hy
    obtain ⟨a, ha, hy'⟩ := (ComplJ8Atom.mem_spineL _ y).1 hy'
    rw [ComplJ8BigBound.limbs_two (hb a ha).1 (hb a ha).2] at hy'
    simp only [Nock.V1J8.Gen.spineOf, Nock.V1J8.Gen.combOf, List.mem_singleton] at hy'
    have := (hb a ha).2
    exact ⟨_, _, hy', by omega, by omega⟩
  · rw [List.mem_singleton] at hy
    exact ⟨0, 1, hy, by omega, by omega⟩

/-- **The atom-walk handle import is the atom-walk-weighted atom cell handle sum** (atom walk present). -/
theorem vhX_eqG (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
    (hpG : p = Nock.Atoms.p)
    (h2 : ∀ y ∈ (j8DataGen p Rg Rt hgen O).acs, ∃ x z, y = Noun.cell (.atom x) (.atom z) ∧ x < p ∧ z < p)
    (hrI : ComplJ8Data.rIAP p (j8DataGen p Rg Rt hgen O).acs = Nock.V1J8.Gen.idxN (j8DataGen p Rg Rt hgen O).acs)
    (hne : (j8DataGen p Rg Rt hgen O).preads ≠ [])
    (hall : ∀ x ∈ (j8DataGen p Rg Rt hgen O).preads, VclL.isPathAx x.2 = true)
    (h62 : ∀ r ∈ VclL.pathReads (j8DataGen p Rg Rt hgen O).preads, VclL.depthOf r.2 ≤ 62)
    (hwcell : ∀ u ∈ walkRows (j8DataGen p Rg Rt hgen O).acs (j8DataGen p Rg Rt hgen O).preads,
      u.label.node ∈ (j8DataGen p Rg Rt hgen O).acs)
    (hA : 0 < (j8DataGen p Rg Rt hgen O).acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjA : Function.Injective (powN o (j8DataGen p Rg Rt hgen O).acs.length))
    (hinjV : Function.Injective (powN o (nVOf (j8DataGen p Rg Rt hgen O)))) (χ : Coins frameJ8 K) :
    vhX δ b (j8DataGen p Rg Rt hgen O) o χ = ∑ j ∈ Finset.range (j8DataGen p Rg Rt hgen O).acs.length,
      (((j8DataGen p Rg Rt hgen O).mhA.getD j 0 : ℕ) : 𝕂′) *
        (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b (j8DataGen p Rg Rt hgen O) hA o j χ)⁻¹ := by
  have hcellsC := acs_cellG Rt hgen O hpG
  have hspec := mxA_specG Rt hgen O hrI hne hall h62
  set D := j8DataGen p Rg Rt hgen O with hD
  set n := D.acs.length
  set G : ℕ → 𝕂′ := fun j => (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b D hA o j χ)⁻¹ with hG
  have hnV : nVOf D = (walkRows D.acs D.preads).length := by unfold nVOf; rw [if_neg hne]
  have hterm : ∀ k ∈ Finset.range (nVOf D), (vdN δ b D o χ WalkHC.xKeyH k)⁻¹ =
      G (D.acs.idxOf (wTrie D.acs D.preads k).label.node) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hmem : (wTrie D.acs D.preads k).label.node ∈ D.acs :=
      hwcell _ (wTrie_mem _ _ (hnV ▸ hk'))
    obtain ⟨x, z, hxz, hx, hz⟩ := h2 _ hmem
    have hjl := List.idxOf_lt_length_of_mem hmem
    have hyj : D.acs[D.acs.idxOf (wTrie D.acs D.preads k).label.node] = Noun.cell (.atom x) (.atom z) := by
      rw [List.getElem_idxOf hjl]; exact hxz
    have hd : vdN δ b D o χ WalkHC.xKeyH k = ComplJ8Bad.ρH δ χ + recDen 0 (ComplJ8Bad.γH δ χ)
        ((ComplJ8OfAtom.vValsC δ D χ ⟨k, hk'⟩).idx, (kLV D ⟨k, hk'⟩, vLV D ⟨k, hk'⟩), (kRV D ⟨k, hk'⟩, vRV D ⟨k, hk'⟩)) := by
      simp only [vdN, WalkTraceHQ.dN, dif_pos hk']
      exact (ComplJ8OfAtom.aw_dRow_split δ b D o hinjV χ (pubsV0 δ D χ) ⟨k, hk'⟩).1
    have hH : D.H = ComplJ8Data.hdlP p D.cells D.acs := rfl
    have hv : (ComplJ8OfAtom.vValsC δ D χ ⟨k, hk'⟩).idx = ((D.acs.idxOf (wTrie D.acs D.preads k).label.node : ℕ) : ZMod p) := rfl
    have hkl : kLV D ⟨k, hk'⟩ = 0 ∧ vLV D ⟨k, hk'⟩ = ((x : ℕ) : ZMod p) ∧ kRV D ⟨k, hk'⟩ = 0 ∧
        vRV D ⟨k, hk'⟩ = ((z : ℕ) : ZMod p) := by
      simp only [kLV, vLV, kRV, vRV, vNode, hxz, hH]
      simp [VclL.hdN, VclL.tlN, ComplJ8Data.hdlP, hx, hz]
    simp only [hG]
    rw [hd, hv, hkl.1, hkl.2.1, hkl.2.2.1, hkl.2.2.2, aHx_two δ b D hA o hinjA χ _ hjl hyj]
  have hW : vhX δ b D o χ = ((walkRows D.acs D.preads).map fun u => G (D.acs.idxOf u.label.node)).sum := by
    unfold vhX
    rw [Finset.sum_congr rfl hterm, hnV]
    exact sum_range_getD' (trie (.atom 0) (.atom 0) [] []) (fun u => G (D.acs.idxOf u.label.node)) _
  have hS := sum_serial n (fun u : NTree WN => D.acs.idxOf u.label.node) G (walkRows D.acs D.preads)
    (fun u hu => List.idxOf_lt_length_of_mem (hwcell u hu))
  rw [hW, hS]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 2
  show _ = D.mxA.getD j 0
  rw [hspec j (Finset.mem_range.mp hj)]
  congr 1
  refine List.filter_congr fun u hu => ?_
  have hm := hwcell u hu
  rw [hcellsC _ hm, ComplJ8OfBal.genIdxOf_eq _ _ hm]
  simp

/-- **`balV`'s second clause at the run, with the inc part carried** (`hI`: the atom inc terminal is the
`mhx`-weighted atom cell handle sum; every coin). -/
theorem balV2_of_incG (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O)))
    (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hbig : ∀ a ∈ (j8DataGen p Rg Rt hgen O).bigs, p ≤ a ∧ a < p + 2 ^ 31 ∧
      Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1])
    (hrI : ComplJ8Data.rIAP p (j8DataGen p Rg Rt hgen O).acs = Nock.V1J8.Gen.idxN (j8DataGen p Rg Rt hgen O).acs)
    (hI : ∀ χ : Coins frameJ8 K,
      ∑ j ∈ Finset.range (j8DataGen p Rg Rt hgen O).acs.length,
        liftQ δ (HonestA8.cNat j (newBA (j8DataGen p Rg Rt hgen O) AtomChipHQ.inc)) *
          (HonestA8.dNat δ (HonestA8.dC δ b (acs_posG Rt hgen O) (powN o _)
            o (ChalsAZJ8.chalsAJ8Z δ χ)
            (pubsAOf δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) o χ)
            (colAH δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) o χ
              (pubsAOf δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) o χ))
            (newBA (j8DataGen p Rg Rt hgen O))) j)⁻¹ =
        ∑ j ∈ Finset.range (j8DataGen p Rg Rt hgen O).acs.length,
          ((((j8DataGen p Rg Rt hgen O).info.getD j Nock.V1J8.Gen.AInfo.z).mhx : ℕ) : 𝕂′) *
            (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O)
              o j χ)⁻¹)
    (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (((BRunG δ b Rt hgen O o).M χ).pubsA CellHQ.pubHQ)
        (((BRunG δ b Rt hgen O o).M χ).pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) (((BRunG δ b Rt hgen O o).M χ).pubsA AtomChipHQ.pubC)
          (((BRunG δ b Rt hgen O o).M χ).pubsA (AtomChipHQ.pubC + 1)) +
        Quad.mk (algebraMap (ZMod p) K δ) (((BRunG δ b Rt hgen O o).M χ).pubsV WalkHQ.pubXQ)
          (((BRunG δ b Rt hgen O o).M χ).pubsV (WalkHQ.pubXQ + 1)) := by
  revert o
  set D := j8DataGen p Rg Rt hgen O with hD
  intro o hI
  have hA : 0 < D.acs.length := acs_posG Rt hgen O
  have hmA : D.acs.length ∈ sizesJ8 D := by simp [sizesJ8]
  have hmV : nVOf D ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjA := (powN_ok o (le_two_pow_ht D hmA)).1
  have hinjV := (powN_ok o (le_two_pow_ht D hmV)).1
  set G : ℕ → 𝕂′ := fun j => (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b D hA o j χ)⁻¹ with hG
  obtain ⟨-, -, tHQ, -, tC, -⟩ := ComplJ8OfAtom.atomTerms δ b D hA o χ
  show Quad.mk _ (pubsAOf δ b D hA o χ CellHQ.pubHQ) (pubsAOf δ b D hA o χ (CellHQ.pubHQ + 1)) =
    Quad.mk _ (pubsAOf δ b D hA o χ AtomChipHQ.pubC) (pubsAOf δ b D hA o χ (AtomChipHQ.pubC + 1)) +
      Quad.mk _ (pubsVOf δ b D o χ WalkHQ.pubXQ) (pubsVOf δ b D o χ (WalkHQ.pubXQ + 1))
  rw [tHQ, tC, hI χ]
  -- the cell part's handle provide, row by row
  have hL : ∑ j ∈ Finset.range D.acs.length, liftQ δ (CellTraceH.mN (mhvA D) j) *
      (CellTraceHQ.dN δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) (pubsAOf δ b D hA o χ) (aCol δ b D χ) (mhvA D) j)⁻¹ =
      ∑ j ∈ Finset.range D.acs.length, (((D.info.getD j Nock.V1J8.Gen.AInfo.z).mhx : ℕ) : 𝕂′) * G j +
      ∑ j ∈ Finset.range D.acs.length, ((D.mhA.getD j 0 : ℕ) : 𝕂′) * G j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    simp only [CellTraceH.mN, CellTraceHQ.dN, dif_pos hj', hG]
    rw [ComplJ8OfAtom.aRow_split δ b D hA o χ _ ⟨j, hj'⟩]
    simp only [mhvA, mhAF, liftQ, Nat.cast_add, map_add, map_natCast]
    ring
  rw [hL]
  congr 1
  by_cases h0 : D.preads = []
  · have hz : (0 : 𝕂′) = Quad.mk _ 0 0 := ((Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩).symm
    have hv : ∀ i, pubsVOf δ b D o χ i = 0 := fun i => by simp [pubsVOf, h0]
    rw [hv, hv, ← hz]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hm : D.mhA.getD j 0 = 0 := by
      show D.mxA.getD j 0 = 0
      rw [mxA_eq_cntG p Rg Rt hgen O j (Finset.mem_range.mp hj), ComplJ8Data.cnt_eq_sumAt]
      simp [ComplJ8Data.awRecs, vs_nilG Rt hgen O h0, ComplJ8Data.wPairs, ComplJ8Data.sumAt]
    simp [hm]
  · have hsh := preads_shapeG Rt hgen O fun a ha => ⟨(hbig a ha).1, (hbig a ha).2.2⟩
    have hall : ∀ x ∈ D.preads, VclL.isPathAx x.2 = true := by
      intro x hx
      obtain ⟨a, -, -, h⟩ := hsh x hx
      exact isPathAx_of_two_le (by omega)
    have h62 : ∀ r ∈ VclL.pathReads D.preads, VclL.depthOf r.2 ≤ 62 := by
      intro x hx
      have hx' : x ∈ D.preads := by
        unfold VclL.pathReads at hx
        exact (List.mem_filter.mp (List.mem_dedup.mp hx)).1
      obtain ⟨a, -, -, h⟩ := hsh x hx'
      exact depthOf_le_of h
    have hwcell : ∀ u ∈ walkRows D.acs D.preads, u.label.node ∈ D.acs := by
      refine walkRows_nodes_mem _ _ (List.ne_nil_of_length_pos hA) (acs_closed_runG Rt hgen O hpG) ?_
      intro x hx _
      obtain ⟨a, ha, h1, h2⟩ := hsh x hx
      have hl := (hbig a ha).2.2
      refine ⟨h1 ▸ comb_mem_acsG Rt hgen O hpG ha (by rw [hl]; simp), ?_⟩
      rw [h1, hl]
      rcases h2 with h | h <;> rw [h, slot_eq_chainWalk _ (by norm_num)] <;> rfl
    have h4 : pubsVOf δ b D o χ WalkHQ.pubXQ = pub2 δ (vhX δ b D o χ) 4 := by
      simp [pubsVOf, h0, WalkHQ.pubXQ]
    have h5 : pubsVOf δ b D o χ (WalkHQ.pubXQ + 1) = pub2 δ (vhX δ b D o χ) 5 := by
      simp [pubsVOf, h0, WalkHQ.pubXQ]
    rw [h4, h5, pub2_mk2 δ _ 4 rfl,
      vhX_eqG δ b Rt hgen O hpG (acs_twoG Rt hgen O hpG fun a ha => ⟨(hbig a ha).1, (hbig a ha).2.1⟩) hrI h0 hall h62
        hwcell hA o hinjA hinjV χ]

end BalV2
section BalVI
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.Edit Nock.Edit.GenX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
/-- **`balV`'s atom inc terminal at the run, at GENERAL limbs** (GLA): with the recounted `mhx` (`mhxOf`: the inc
rows whose old row is `j`), the inc-weighted old-key LogUp total is the `mhx`-weighted atom cell handle sum. Every
inc row's old key is the handle key of its old row (`inc_old`, `dC_key`, `aHx_gen`), and `mhx` counts the inc rows
by old row (`sum_serial`). No limb count, no injectivity. -/
theorem incT_genG (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O)))
    (hpG : p = Nock.Atoms.p) (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hlast : Nock.V1J8.Gen.lastIdxOf (j8DataGen p Rg Rt hgen O).acs (ComplJ8Data.combPP p) =
      Nock.V1J8.Gen.idxOf (j8DataGen p Rg Rt hgen O).acs (ComplJ8Data.combPP p)) (χ : Coins frameJ8 K) :
      ∑ j ∈ Finset.range (j8DataGen p Rg Rt hgen O).acs.length,
        liftQ δ (HonestA8.cNat j (newBA (j8DataGen p Rg Rt hgen O) AtomChipHQ.inc)) *
          (HonestA8.dNat δ (HonestA8.dC δ b (acs_posG Rt hgen O) (powN o _)
            o (ChalsAZJ8.chalsAJ8Z δ χ)
            (pubsAOf δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) o χ)
            (colAH δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) o χ
              (pubsAOf δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) o χ))
            (newBA (j8DataGen p Rg Rt hgen O))) j)⁻¹ =
        ∑ j ∈ Finset.range (j8DataGen p Rg Rt hgen O).acs.length,
          ((((j8DataGen p Rg Rt hgen O).info.getD j Nock.V1J8.Gen.AInfo.z).mhx : ℕ) : 𝕂′) *
            (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O)
              o j χ)⁻¹ := by
  subst hpG
  revert o
  set D := j8DataGen Nock.Atoms.p Rg Rt hgen O with hD
  intro o
  have hA : 0 < D.acs.length := acs_posG Rt hgen O
  have hmA : D.acs.length ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjA := (powN_ok o (le_two_pow_ht D hmA)).1
  have hg := genHyp_j8G Rg Rt hgen O hax hop5 (rows_le_of_rows31G Rt hgen O h31)
  obtain ⟨-, -, htl⟩ := acs_okG Rg Rt hgen O hax hop5 h31
  set T := ComplJ8Atom.tabOf D.acs D.info D.mb D.rows with hT
  set G : ℕ → Quad (algebraMap (ZMod Nock.Atoms.p) K δ) := fun j =>
    (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b D hA o j χ)⁻¹ with hG
  set J : ℕ → ℕ := fun m => (T.row m).idxO with hJ
  set C := (List.range D.acs.length).filter fun m => T.inc m with hCdef
  have hlt : ∀ c ∈ D.acs, Nock.V1J8.Gen.idxOf D.acs c < D.acs.length := by
    intro c hc; rw [genIdxOf_eq _ _ hc]; exact List.idxOf_lt_length_of_mem hc
  -- an inc row's old index and fields
  have hold : ∀ m, T.inc m = true → D.acs[J m]? = some (Nock.V1J8.Gen.combOf (T.lo m)) ∧
      J m < D.acs.length ∧ 2 ≤ (T.lo m).length ∧ Nock.V1J8.Gen.combOf (T.lo m) ∈ D.acs := by
    intro m hm
    obtain ⟨-, h2, hmem⟩ := ComplJ8Atom.inc_old _ _ _ _ hg m hm
    obtain ⟨hl, he⟩ := ComplJ8Atom.idxO_copy _ _ _ _ hg m hm
    exact ⟨he, hl, h2, hmem⟩
  -- the inc rows' terms
  have hterm : ∀ j ∈ Finset.range D.acs.length,
      liftQ δ (HonestA8.cNat j (newBA D AtomChipHQ.inc)) *
        (HonestA8.dNat δ (HonestA8.dC δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) (pubsAOf δ b D hA o χ)
          (colAH δ b D hA o χ (pubsAOf δ b D hA o χ)) (newBA D)) j)⁻¹ =
      if T.inc j = true then G (J j) else 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [HonestA8.cNat, HonestA8.dNat, dif_pos hj']
    rw [newBA_inc]
    by_cases hi : T.inc j = true
    · have hi' : (D.info.getD j Nock.V1J8.Gen.AInfo.z).inc = true := hi
      rw [if_pos hi', if_pos hi]
      obtain ⟨eJ, hJn, h2, hmem⟩ := hold j hi
      set l := T.lo j with hl
      rw [dC_key δ b D hA o hinjA χ _ ⟨j, hj'⟩]
      simp only [Fin.val_mk, liftQ, map_one, one_mul, hG]
      have hget : D.acs[J j]'hJn = Nock.V1J8.Gen.combOf l := by
        rw [List.getElem?_eq_getElem hJn] at eJ; exact Option.some.inj eJ
      have hhd : Nock.V1J8.Gen.hdN' D.acs[J j] = .atom (l.headD 0) := by rw [hget, ComplJ8Atom.hd_combOf l h2]
      rw [aHx_gen δ b D hA o hinjA χ (J j) hJn (by rw [hhd]; rfl), hhd]
      have hrow : (T.row j).idxO = J j ∧ (T.row j).lO = l.headD 0 ∧
          (T.row j).kRO = (if 3 ≤ l.length then 1 else 0) ∧
          (T.row j).vRO = (if 3 ≤ l.length then T.ip l else l.getD 1 0) := by
        refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp [ComplJ8Atom.AtomTab.row, hi, hl]
      rw [hrow.1, hrow.2.1, hrow.2.2.1, hrow.2.2.2]
      have htl' := ComplJ8Atom.tl_combOf l h2
      by_cases h3 : 3 ≤ l.length
      · have e2 : Nock.V1J8.Gen.tlN' D.acs[J j] = Nock.V1J8.Gen.combOf l.tail := by rw [hget, htl', if_pos h3]
        have hc : (Nock.V1J8.Gen.tlN' D.acs[J j]).isCell = true := by
          rw [e2]; exact ComplJ8Atom.combOf_isCell _ (by rw [List.length_tail]; omega)
        have hm2 : Nock.V1J8.Gen.combOf l.tail ∈ D.acs := e2 ▸ htl _ (List.getElem_mem _) hc
        have hix : T.ip l = ComplJ8Data.ptrP Nock.Atoms.p D.acs D.rows D.acs[J j] := by
          show ComplJ8Data.ptrP Nock.Atoms.p D.acs D.rows (Nock.V1J8.Gen.combOf l) = _
          rw [hget]
        have hc' : (Nock.V1J8.Gen.combOf l.tail).isCell = true := e2 ▸ hc
        simp only [if_pos h3, hc', if_true, hix, e2, Nock.V1J8.Gen.atomV]
      · have e2 : Nock.V1J8.Gen.tlN' D.acs[J j] = .atom (l.getD 1 0) := by rw [hget, htl', if_neg h3]
        simp only [if_neg h3, e2, Noun.isCell, Bool.false_eq_true, if_false, Nock.V1J8.Gen.atomV]
    · have hi' : ¬ (D.info.getD j Nock.V1J8.Gen.AInfo.z).inc = true := hi
      rw [if_neg hi', if_neg hi]
      simp only [liftQ, map_zero, zero_mul]
  rw [Finset.sum_congr rfl hterm, sum_range_ite_list (fun m => T.inc m) (fun m => G (J m)) D.acs.length]
  have hss := sum_serial D.acs.length J G C (fun m hm => (hold m (List.mem_filter.mp hm).2).2.1)
  rw [hss]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  congr 1
  -- the recounted mhx is the number of inc rows whose old row is `j`
  set Fd := ComplJ8Atom.infoFold Nock.Atoms.p D.acs D.rows with hFd
  have hinfo : D.info = Nock.V1J8.Gen.recountMhx Fd := ComplJ8Atom.infoOfP_eq _ _ _
  have hsz : Fd.size = D.acs.length := by
    have := ComplJ8Atom.recountMhx_size Fd
    rw [← hinfo] at this
    rw [← this]
    exact (ComplJ8Atom.stInv_gen _ _ _ _ hg).size
  have hm : (D.info.getD j Nock.V1J8.Gen.AInfo.z).mhx = Nock.V1J8.Gen.mhxOf Fd j := by
    rw [hinfo, ComplJ8Atom.getD_recountMhx, if_pos (by rw [hsz]; exact hj')]
  rw [hm]
  unfold Nock.V1J8.Gen.mhxOf
  rw [toList_eq_range, hsz, List.filter_map, List.length_map, hCdef, List.filter_filter]
  congr 2
  refine List.filter_congr fun m hmr => ?_
  have hR := ComplJ8Atom.recountMhx_fields Fd m
  have e1 : (Fd.getD m Nock.V1J8.Gen.AInfo.z).inc = T.inc m := by
    show _ = (D.info.getD m Nock.V1J8.Gen.AInfo.z).inc; rw [hinfo, hR.1]
  have e2 : (Fd.getD m Nock.V1J8.Gen.AInfo.z).idxO = (D.info.getD m Nock.V1J8.Gen.AInfo.z).idxO := by
    rw [hinfo, hR.2.2.2.1]
  have e3 : (T.row m).idxO = (D.info.getD m Nock.V1J8.Gen.AInfo.z).idxO :=
    (ComplJ8Atom.row_info _ _ _ _ hg m).2.2.2.1
  simp only [Function.comp, e1, e2, hJ, e3]
  cases T.inc m <;> simp <;> exact Bool.eq_iff_iff.mpr (by simp)

/-- **`balV`'s atom inc terminal at the run** (`hI` of `balV2_of_incG`, every coin): the inc-weighted old-key
LogUp total is the `mhx`-weighted atom cell handle sum. The two limbs of `bigBound_single` make every slow increment one `wrA`
(`fold_two`): inc row `jn v` (the comb of `v + 1`) carries the old key of row `jo v` (the comb of `v`), whose cell
handle key it is (`dC_key`, `aHx_two`), and `mhx` counts the `jo v` (`sum_serial`). -/
theorem incT_runG (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O)))
    (hpG : p = Nock.Atoms.p) (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hlast : Nock.V1J8.Gen.lastIdxOf (j8DataGen p Rg Rt hgen O).acs (ComplJ8Data.combPP p) =
      Nock.V1J8.Gen.idxOf (j8DataGen p Rg Rt hgen O).acs (ComplJ8Data.combPP p))
    (hbig : ∀ a ∈ (j8DataGen p Rg Rt hgen O).bigs, p ≤ a ∧ a < p + 2 ^ 31 ∧
      Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1]) (χ : Coins frameJ8 K) :
      ∑ j ∈ Finset.range (j8DataGen p Rg Rt hgen O).acs.length,
        liftQ δ (HonestA8.cNat j (newBA (j8DataGen p Rg Rt hgen O) AtomChipHQ.inc)) *
          (HonestA8.dNat δ (HonestA8.dC δ b (acs_posG Rt hgen O) (powN o _)
            o (ChalsAZJ8.chalsAJ8Z δ χ)
            (pubsAOf δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) o χ)
            (colAH δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) o χ
              (pubsAOf δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) o χ))
            (newBA (j8DataGen p Rg Rt hgen O))) j)⁻¹ =
        ∑ j ∈ Finset.range (j8DataGen p Rg Rt hgen O).acs.length,
          ((((j8DataGen p Rg Rt hgen O).info.getD j Nock.V1J8.Gen.AInfo.z).mhx : ℕ) : 𝕂′) *
            (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O)
              o j χ)⁻¹ := by
  exact incT_genG δ b Rt hgen O o hpG hax hop5 h31 hlast χ

/-- **`balV`'s second clause at the run, closed** (every coin; `complJ8`'s binders `hpG hax hop5 hclA hRt h31`):
`balV2_of_incG` with the two big-atom facts and `hI := incT_runG`. -/
theorem balV2_runG (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O)))
    (hpG : p = Nock.Atoms.p) (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (((BRunG δ b Rt hgen O o).M χ).pubsA CellHQ.pubHQ)
        (((BRunG δ b Rt hgen O o).M χ).pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) (((BRunG δ b Rt hgen O o).M χ).pubsA AtomChipHQ.pubC)
          (((BRunG δ b Rt hgen O o).M χ).pubsA (AtomChipHQ.pubC + 1)) +
        Quad.mk (algebraMap (ZMod p) K δ) (((BRunG δ b Rt hgen O o).M χ).pubsV WalkHQ.pubXQ)
          (((BRunG δ b Rt hgen O o).M χ).pubsV (WalkHQ.pubXQ + 1)) := by
  have hN : (j8DataGen p Rg Rt hgen O).rows.size ≤ 2 ^ 31 := by
    have h := h31 (bfsForest [(j8DataGen p Rg Rt hgen O).t]).length (by simp [sizesJ8])
    rw [data_rowsG hgen O]
    simpa [ComplJ8Data.rowsOfT, j8DataGen] using h
  obtain ⟨hb, -, -, -, -, -, hrI, -, -⟩ := bigBound_singleG hgen O hpG (hclA 0) (hclA 1) hRt hop5 hN
  have hbig : ∀ a ∈ (j8DataGen p Rg Rt hgen O).bigs, p ≤ a ∧ a < p + 2 ^ 31 ∧
      Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1] :=
    fun a ha => ⟨(hb a ha).1, by have := (hb a ha).2.1; omega, (hb a ha).2.2⟩
  exact balV2_of_incG δ b Rt hgen O o hpG h31 hbig hrI
    (fun χ => incT_runG δ b Rt hgen O o hpG hax hop5 h31
      (last_eq_of_j8G Rt hgen O hpG hop5 hclA hRt h31) hbig χ) χ

end BalVI
section BalV1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.Edit Nock.Edit.GenX
open Nock.V1J8.Gen (hdN' tlN')
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
/-- The run's cell list is closed under cell children (`hdN` / `tlN` form). -/
theorem cells_cl_runG : ∀ y ∈ (j8DataGen p Rg Rt hgen O).cells,
    ((hdN y).isCell = true → hdN y ∈ (j8DataGen p Rg Rt hgen O).cells) ∧
      ((tlN y).isCell = true → tlN y ∈ (j8DataGen p Rg Rt hgen O).cells) := by
  have hclosed : ComplJ8Data.ClP (j8DataGen p Rg Rt hgen O).cells [] := cells_closedG p Rg Rt hgen O
  intro y hy
  cases y with
  | atom v => simp [hdN_eq, tlN_eq, hdN', tlN', Noun.isCell]
  | cell u v =>
    obtain ⟨h1, h2⟩ := hclosed u v hy (by simp)
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rw [hdN_eq] at hc ⊢
      simp only [hdN'] at hc ⊢
      cases u with
      | atom _ => simp [Noun.isCell] at hc
      | cell x y => exact h1 x y rfl
    · rw [tlN_eq] at hc ⊢
      simp only [tlN'] at hc ⊢
      cases v with
      | atom _ => simp [Noun.isCell] at hc
      | cell x y => exact h2 x y rfl

/-- The claim / cell-reference term at the generator's serial. -/
abbrev ccGG (χ : Coins frameJ8 K) (n : Noun) : 𝕂′ :=
  if n.isCell then cG δ (γV δ χ) (ρV δ χ) (encR δ χ) (j8DataGen p Rg Rt hgen O).cells
    (Nock.V1J8.Gen.idxOf (j8DataGen p Rg Rt hgen O).cells n) else 0

theorem ccT_eqG (χ : Coins frameJ8 K) (n : Noun) (hn : n.isCell = true → n ∈ (j8DataGen p Rg Rt hgen O).cells) :
    ccT δ (γV δ χ) (ρV δ χ) (encR δ χ) (j8DataGen p Rg Rt hgen O).cells n = ccGG δ Rt hgen O χ n := by
  by_cases hc : n.isCell = true
  · simp only [ccT, ccGG, hc, if_true, genIdxOf_eq _ _ (hn hc)]
  · simp [ccT, ccGG, hc]

/-- **The cell validity terminal at the run**: claim terms plus pin terms minus the big-child terms. -/
theorem cvT_runG (χ : Coins frameJ8 K) :
    cvT δ (j8DataGen p Rg Rt hgen O) χ =
      ([s, f, r].map fun x => ccGG δ Rt hgen O χ x).sum +
      ((j8DataGen p Rg Rt hgen O).regs.map fun id => cG δ (γV δ χ) (ρV δ χ) (encR δ χ) (j8DataGen p Rg Rt hgen O).cells
        ((j8DataGen p Rg Rt hgen O).idx id)).sum -
      ((j8DataGen p Rg Rt hgen O).cells.map fun y =>
        btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (j8DataGen p Rg Rt hgen O)) (hdN y) +
          btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (j8DataGen p Rg Rt hgen O)) (tlN y)).sum := by
  have hcl := cells_cl_runG (p := p) Rt hgen O
  set D := j8DataGen p Rg Rt hgen O with hD
  set G := cG δ (γV δ χ) (ρV δ χ) (encR δ χ) D.cells with hG
  set L1 := ComplJ8Data.cellPairs D.cells (D.cells.flatMap fun n => [hdN' n, tlN' n]) with hL1
  set L2 := ComplJ8Data.cellPairs D.cells [s, f, r] with hL2
  set L3 := D.regs.map fun id => (D.idx id, 1) with hL3
  have hr : ∀ L ∈ [L1, L2, L3], ∀ q ∈ L, 0 < q.2 → q.1 < D.cells.length := by
    intro L hL q hq
    refine vRecs_rangeG p Rg Rt hgen O q ?_
    simp only [ComplJ8Data.vRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl
    · exact Or.inl hq
    · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr hq)
  have hcnt : ∀ k < D.cells.length, mvF D k = ComplJ8Data.sumAt L1 k + ComplJ8Data.sumAt L2 k +
      ComplJ8Data.sumAt L3 k := by
    intro k hk
    show D.mv.getD k 0 = _
    rw [mv_eq_cntG p Rg Rt hgen O k hk, ComplJ8Data.cnt_eq_sumAt]
    simp only [ComplJ8Data.vRecs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [add_assoc]
  have h1 : ∑ k ∈ Finset.range D.cells.length, liftQ δ ((mvF D k : ℕ) : ZMod p) * G k =
      (L1.map fun q => (q.2 : 𝕂′) * G q.1).sum + (L2.map fun q => (q.2 : 𝕂′) * G q.1).sum +
        (L3.map fun q => (q.2 : 𝕂′) * G q.1).sum := by
    rw [Finset.sum_congr rfl (fun k hk => by rw [hcnt k (Finset.mem_range.mp hk)])]
    simp only [liftQ, Nat.cast_add, map_add, map_natCast, add_mul, Finset.sum_add_distrib]
    rw [sum_sumAt _ _ L1 (hr L1 (by simp)), sum_sumAt _ _ L2 (hr L2 (by simp)),
      sum_sumAt _ _ L3 (hr L3 (by simp))]
  have hS1 : (L1.map fun q => (q.2 : 𝕂′) * G q.1).sum =
      (D.cells.map fun y => ccGG δ Rt hgen O χ (hdN' y) + ccGG δ Rt hgen O χ (tlN' y)).sum := by
    rw [hL1, cellPairs_sum, sum_flatMap_two]
  have hS2 : (L2.map fun q => (q.2 : 𝕂′) * G q.1).sum = ([s, f, r].map fun x => ccGG δ Rt hgen O χ x).sum := by
    rw [hL2, cellPairs_sum]
  have hS3 : (L3.map fun q => (q.2 : 𝕂′) * G q.1).sum = (D.regs.map fun id => G (D.idx id)).sum := by
    simp [hL3, List.map_map, Function.comp_def]
  have h2 : (D.cells.map fun y => ccT δ (γV δ χ) (ρV δ χ) (encR δ χ) D.cells (hdN y) +
        ccT δ (γV δ χ) (ρV δ χ) (encR δ χ) D.cells (tlN y) +
        (btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf D) (hdN y) +
          btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf D) (tlN y))).sum =
      (D.cells.map fun y => ccGG δ Rt hgen O χ (hdN' y) + ccGG δ Rt hgen O χ (tlN' y)).sum +
        (D.cells.map fun y => btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf D) (hdN y) +
          btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf D) (tlN y)).sum := by
    rw [← List.sum_map_add]
    refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
    rw [ccT_eqG δ Rt hgen O χ _ (hcl y hy).1, ccT_eqG δ Rt hgen O χ _ (hcl y hy).2, hdN_eq, tlN_eq]
  unfold cvT
  rw [cvSum_gen δ _ _ _ _ _ _ _ _ _ hcl, ← hG, h1, h2, hS1, hS2, hS3]
  ring

/-- The atom-root provider inverse of atom row `j` at the run. -/
abbrev HBG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) (χ : Coins frameJ8 K) (j : ℕ) : 𝕂′ :=
  (HonestA8.dNat δ (HonestA8.dMB δ b (acs_posG Rt hgen O) (powN (o) _) (o)
    (ChalsAZJ8.chalsAJ8Z δ χ) (pubsAOf δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) (o) χ)
    (colAH δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) (o) χ
      (pubsAOf δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) (o) χ))
    (newBA (j8DataGen p Rg Rt hgen O))) j)⁻¹

/-- A child's atom-root term (the atom table's `mb` consumer). -/
abbrev bhTG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) (χ : Coins frameJ8 K) (n : Noun) : 𝕂′ :=
  ((ComplJ8Data.bigIdOfP p (j8DataGen p Rg Rt hgen O).acs n).map (HBG δ b Rt hgen O o hpG h31 χ)).getD 0

/-- **The atom table's `mb` terminal at the run** is the sum of the big-child atom-root terms. -/
theorem mbT_runG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (((BRunG δ b Rt hgen O o).M χ).pubsA AtomChipHQ.pubMB)
        (((BRunG δ b Rt hgen O o).M χ).pubsA (AtomChipHQ.pubMB + 1)) =
      ((j8DataGen p Rg Rt hgen O).cells.map fun y =>
        bhTG δ b Rt hgen O o hpG h31 χ (hdN' y) + bhTG δ b Rt hgen O o hpG h31 χ (tlN' y)).sum := by
  refine ((ComplJ8OfAtom.atomTerms δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) (o) χ).2.2.2.1).trans ?_
  obtain ⟨LB, hLB⟩ : ∃ LB, LB = ((j8DataGen p Rg Rt hgen O).cells.flatMap fun n => [hdN' n, tlN' n]).filterMap
      fun n => (ComplJ8Data.bigIdOfP p (j8DataGen p Rg Rt hgen O).acs n).map fun i => (i, 1) := ⟨_, rfl⟩
  refine (Finset.sum_congr rfl (g := fun j => ((ComplJ8Data.sumAt LB j : ℕ) : 𝕂′) * HBG δ b Rt hgen O o hpG h31 χ j)
    fun j hj => ?_).trans ?_
  · have hj' := Finset.mem_range.mp hj
    have e : HonestA8.cNat j (newBA (j8DataGen p Rg Rt hgen O) AtomChipHQ.mb) = ((ComplJ8Data.sumAt LB j : ℕ) : ZMod p) := by
      rw [HonestA8.cNat, dif_pos hj', newBA_mb]
      rw [mb_eq_cntG p Rg Rt hgen O j hj', ComplJ8Data.cnt_eq_sumAt]
      simp only [ComplJ8Data.mbRecs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hLB]
    rw [e]
    simp only [liftQ, map_natCast]
  · rw [sum_sumAt _ _ LB (fun q hq => mbRecs_rangeG p Rg Rt hgen O q (by
      simp only [ComplJ8Data.mbRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil]; rw [← hLB]; exact hq)),
      hLB, bigPairs_sum (ComplJ8Data.bigIdOfP p (j8DataGen p Rg Rt hgen O).acs) (HBG δ b Rt hgen O o hpG h31 χ),
      sum_flatMap_two]

/-- **The big-atom key identity**: a big child's validity consumer key `(zJ, 0, leafVal zY a, 0, root)` is the atom
table's `mb` provider key of its root row `(zAt, 0, leaf, 0, idx)` (`zAt = zJ`, `zA = zY`, two limbs). -/
theorem big_keyG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hl2 : ∀ a ∈ (j8DataGen p Rg Rt hgen O).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1])
    (hroot : ∀ a, ComplJ8Data.rootIdxP p (j8DataGen p Rg Rt hgen O).acs a =
      Nock.V1J8.Gen.idxOf (j8DataGen p Rg Rt hgen O).acs (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)))
    (χ : Coins frameJ8 K) (a : ℕ) (ha : a ∈ (j8DataGen p Rg Rt hgen O).bigs) :
    gOf δ (γV δ χ) (ρV δ χ) (encR δ χ) (.atom a)
        ((ComplJ8Data.rootIdxP p (j8DataGen p Rg Rt hgen O).acs a : ℕ) : ZMod p) =
      HBG δ b Rt hgen O o hpG h31 χ (ComplJ8Data.rootIdxP p (j8DataGen p Rg Rt hgen O).acs a) := by
  have hmem : Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a) ∈ (j8DataGen p Rg Rt hgen O).acs :=
    comb_mem_acsG Rt hgen O hpG ha (by rw [(hl2 a ha).2]; simp)
  have hjE : ComplJ8Data.rootIdxP p (j8DataGen p Rg Rt hgen O).acs a =
      List.idxOf (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)) (j8DataGen p Rg Rt hgen O).acs := by
    rw [hroot, genIdxOf_eq _ _ hmem]
  have hj : ComplJ8Data.rootIdxP p (j8DataGen p Rg Rt hgen O).acs a < (j8DataGen p Rg Rt hgen O).acs.length := by
    rw [hjE]; exact List.idxOf_lt_length_of_mem hmem
  have hget : (j8DataGen p Rg Rt hgen O).acs[ComplJ8Data.rootIdxP p (j8DataGen p Rg Rt hgen O).acs a]'hj =
      Noun.cell (.atom (a + 1 - p)) (.atom (Nock.Atoms.B - 1)) := by
    have key : ∀ (j : ℕ) (hj' : j < (j8DataGen p Rg Rt hgen O).acs.length),
        j = List.idxOf (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)) (j8DataGen p Rg Rt hgen O).acs →
        (j8DataGen p Rg Rt hgen O).acs[j]'hj' = Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a) := by
      intro j hj' e; subst e; exact List.getElem_idxOf _
    rw [key _ hj hjE, (hl2 a ha).2, combOf_two]
  have hmA : (j8DataGen p Rg Rt hgen O).acs.length ∈ sizesJ8 (j8DataGen p Rg Rt hgen O) := by simp [sizesJ8]
  have hinj := (powN_ok (o) (le_two_pow_ht (j8DataGen p Rg Rt hgen O) hmA)).1
  set i : Fin (j8DataGen p Rg Rt hgen O).acs.length := ⟨_, hj⟩ with hi
  have hleaf := ekA_leaf δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) (o) hinj χ
    (pubsAOf δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) (o) χ) i
  have hidx : (ComplJ8OfAtom.ezA δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) (o) χ
      (pubsAOf δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) (o) χ) i).trace 2 =
      ((ComplJ8Data.rootIdxP p (j8DataGen p Rg Rt hgen O).acs a : ℕ) : ZMod p) := by
    rw [ComplJ8Atom.EZ_trace (δF := δ) (b := b) (hinj := hinj) (i := i) (j := 2) (h2 := le_rfl) (h3 := by norm_num),
      if_pos (by norm_num)]
    exact (ComplJ8OfAtom.colAH_fields δ b _ (acs_posG Rt hgen O) (o) χ _ i).1
  have hchal := ComplJ8OfAtom.ekA_chal δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) (o) χ
    (pubsAOf δ b (j8DataGen p Rg Rt hgen O) (acs_posG Rt hgen O) (o) χ) i
  -- the leaf values
  have hlimbs : ∀ x ∈ Nock.Atoms.limbs a, x < Nock.Atoms.B := fun x hx => (Nock.Atoms.limbs_canonical a).1 x hx
  have hlv := G5J8.leafVal_val (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2)) hlimbs
    (by rw [Nock.Atoms.val_limbs, ← hpG]; exact (hl2 a ha).1)
  rw [Nock.Atoms.val_limbs, (hl2 a ha).2, horner_two] at hlv
  rw [hget, enc_leaf2, ComplJ8OfAtom.zA_eq] at hleaf
  unfold HBG gOf
  rw [HonestA8.dNat, dif_pos hj, ComplJ8OfAtom.dMB_eq, InhabJ8Good.compress_split, keyVec_mb, hchal,
    ChalsAZJ8.chalsAJ8Z_zAt, hleaf, hidx]
  refine congrArg (fun x => (ρV δ χ + FiniteIO.compress ⟨γV δ χ, 0⟩ x)⁻¹) ?_
  funext c
  fin_cases c
  · rfl
  · rfl
  · show Nock.Atoms.leafVal (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2)) a = _
    rw [hlv]
    rfl
  · show Quad.mk _ (algebraMap (ZMod p) K ((0 % 2 ^ 62 : ℕ) : ZMod p))
      (algebraMap (ZMod p) K ((0 / 2 ^ 62 : ℕ) : ZMod p)) = 0
    simp only [Nat.zero_mod, Nat.zero_div, Nat.cast_zero, map_zero]
    exact (Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩
  · rfl

/-- The atom children of the run's cells that are big are big atoms of the run. -/
theorem child_bigG (y : Noun) (hy : y ∈ (j8DataGen p Rg Rt hgen O).cells) (n : Noun) (hn : n = hdN y ∨ n = tlN y)
    (a : ℕ) (ha : n = .atom a) (hp : p ≤ a) : a ∈ (j8DataGen p Rg Rt hgen O).bigs := by
  obtain ⟨hc, hl⟩ := cellsOfRoots_inv (j8DataGen p Rg Rt hgen O).roots y ((O.permC _).mem_iff.mp hy)
  cases y with
  | atom _ => simp [Noun.isCell] at hc
  | cell u v =>
    have hal : a ∈ Nock.Edit.GenX.leavesOf (.cell u v) := by
      rcases hn with h | h
      · rw [h, hdN_eq] at ha; simp only [hdN'] at ha; subst ha; simp [Nock.Edit.GenX.leavesOf]
      · rw [h, tlN_eq] at ha; simp only [tlN'] at ha; subst ha; simp [Nock.Edit.GenX.leavesOf]
    have hr := hl a hal
    show a ∈ ComplJ8Data.bigsP p (j8DataGen p Rg Rt hgen O).roots (j8DataGen p Rg Rt hgen O).rows
    refine (ComplJ8Atom.mem_bigsP p _ _ a).mpr ⟨?_, hp⟩
    rw [List.flatMap_append]
    exact List.mem_append_left _ hr

/-- **A child's big-atom consumer term is its atom-root provider term.** -/
theorem bt_bhG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hl2 : ∀ a ∈ (j8DataGen p Rg Rt hgen O).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1])
    (hroot : ∀ a, ComplJ8Data.rootIdxP p (j8DataGen p Rg Rt hgen O).acs a =
      Nock.V1J8.Gen.idxOf (j8DataGen p Rg Rt hgen O).acs (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)))
    (χ : Coins frameJ8 K) (n : Noun) (hn : ∀ a, n = .atom a → p ≤ a → a ∈ (j8DataGen p Rg Rt hgen O).bigs) :
    btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (j8DataGen p Rg Rt hgen O)) n = bhTG δ b Rt hgen O o hpG h31 χ n := by
  cases n with
  | cell u v => simp [btT, bhTG, ComplJ8Cell.isBig, Noun.isCell, ComplJ8Data.bigIdOfP]
  | atom v =>
    by_cases hv : v < p
    · simp [btT, bhTG, ComplJ8Cell.isBig, Noun.isCell, ComplJ8Data.bigIdOfP, hv]
    · have hb : ComplJ8Cell.isBig (bigOf (j8DataGen p Rg Rt hgen O)) (.atom v) = true := by
        simp [ComplJ8Cell.isBig, Noun.isCell, ComplJ8Data.bigIdOfP, hv]
      simp only [btT, hb, if_true, bhTG, bigOf, ComplJ8Data.bigIdOfP, hv, if_false, Option.getD_some,
        Option.map_some]
      exact big_keyG δ b Rt hgen O o hpG h31 hl2 hroot χ v (hn v rfl (by omega))

/-- **The claim records' inverse sum** is the claim cell-reference sum. -/
theorem claim_sumG (χ : Coins frameJ8 K) :
    ((AcceptsJ8P.claimRecsJ8 δ χ (ComplJ8.cJ s f r)
        (ComplJ8Comp.mCOf (j8DataGen p Rg Rt hgen O).H (ComplJ8.cJ s f r))).map fun x =>
      (FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6),
        Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      ([s, f, r].map fun x => ccGG δ Rt hgen O χ x).sum := by
  have hterm : ∀ x ∈ [s, f, r], (if FrameVS.isCellN x = true then
      (FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩ (ClaimVS.claimVec δ (AcceptsJ8.encJ8 δ χ x)
        (((j8DataGen p Rg Rt hgen O).H x).2 : ZMod p) ((AcceptsJ8P.rkC x).1 : ZMod p)
        ((AcceptsJ8P.rkC x).2 : ZMod p)))⁻¹ else 0) = ccGG δ Rt hgen O χ x := by
    intro x hx
    cases x with
    | atom v => simp [FrameVS.isCellN, ccGG, Noun.isCell]
    | cell u v =>
      have hmem := claim_mem_cellsG p Rg Rt hgen O hx (.cell u v) (by simp [Nock.Jet.ChipJ8.subs])
      simp only [FrameVS.isCellN, if_true, ccGG, Noun.isCell]
      rw [show ((j8DataGen p Rg Rt hgen O).H (.cell u v)).2 =
          Nock.V1J8.Gen.idxOf (j8DataGen p Rg Rt hgen O).cells (.cell u v) from rfl, genIdxOf_eq _ _ hmem]
      unfold cG
      rw [getD_idxOf _ _ hmem, AcceptsJ8P.rkC, claimVec_kOf]
  unfold AcceptsJ8P.claimRecsJ8 AcceptsJ8P.claimCells
  rw [List.map_map, sum_map_ite']
  have h3 : List.finRange 3 = [0, 1, 2] := by decide
  rw [h3]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp_def]
  rw [← hterm s (by simp), ← hterm f (by simp), ← hterm r (by simp)]
  rfl

/-- **The registry pin records' inverse sum** is the pin provider sum. -/
theorem pin_sumG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) (χ : Coins frameJ8 K) :
    ((AcceptsJ8P.pinRecsJ8 δ (BRunG δ b Rt hgen O o).Pb χ).map fun x =>
      (FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6),
        Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      ((j8DataGen p Rg Rt hgen O).regs.map fun id => cG δ (γV δ χ) (ρV δ χ) (encR δ χ) (j8DataGen p Rg Rt hgen O).cells
        ((j8DataGen p Rg Rt hgen O).idx id)).sum := by
  unfold AcceptsJ8P.pinRecsJ8
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left (l := (j8DataGen p Rg Rt hgen O).regs) fun id hid => ?_)
  have hmem : Nock.Jet.Autogen.compile p (Rt id) ∈ (j8DataGen p Rg Rt hgen O).cells := by
    have hm : Nock.Jet.Autogen.compile p (Rt id) ∈ (j8DataGen p Rg Rt hgen O).roots :=
      List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨id, hid, rfl⟩))
    obtain ⟨a, c, hab⟩ := ComplJ8Data.compile_isCell p (Rt id)
    rw [hab] at hm ⊢
    exact root_mem_cellsG p Rg Rt hgen O hm
  show (FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩ (ClaimVS.claimVec δ
      (encR δ χ (Nock.Jet.Autogen.compile p (Rt id)))
      (((j8DataGen p Rg Rt hgen O).idx id : ℕ) : ZMod p)
      ((AcceptsJ8P.rkC (Nock.Jet.Autogen.compile p (Rt id))).1 : ZMod p)
      ((AcceptsJ8P.rkC (Nock.Jet.Autogen.compile p (Rt id))).2 : ZMod p)))⁻¹ = _
  rw [show (j8DataGen p Rg Rt hgen O).idx id =
      Nock.V1J8.Gen.idxOf (j8DataGen p Rg Rt hgen O).cells (Nock.Jet.Autogen.compile p (Rt id)) from rfl,
    genIdxOf_eq _ _ hmem]
  unfold cG
  rw [getD_idxOf _ _ hmem, AcceptsJ8P.rkC, claimVec_kOf]

/-- **`balV`'s first clause at the run** (every coin): the claim and registry pin records' validity inverses sum to
the cell validity terminal plus the atom table's `mb` terminal. The two limbs of `bigBound_single` (`bigBound_single`) give the
big-atom keys. -/
theorem balV1_runG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (hop5 : ComplJ8.ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) (χ : Coins frameJ8 K) :
    ((AcceptsJ8P.claimRecsJ8 δ χ (ComplJ8.cJ s f r) ((BRunG δ b Rt hgen O o).M χ).m ++
        AcceptsJ8P.pinRecsJ8 δ (BRunG δ b Rt hgen O o).Pb χ).map fun x => (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6), Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      Quad.mk (algebraMap (ZMod p) K δ) (((BRunG δ b Rt hgen O o).M χ).pubsC 0)
          (((BRunG δ b Rt hgen O o).M χ).pubsC 1) +
        Quad.mk (algebraMap (ZMod p) K δ) (((BRunG δ b Rt hgen O o).M χ).pubsA AtomChipHQ.pubMB)
          (((BRunG δ b Rt hgen O o).M χ).pubsA (AtomChipHQ.pubMB + 1)) := by
  have hN : (j8DataGen p Rg Rt hgen O).rows.size ≤ 2 ^ 31 := by
    have h := h31 (bfsForest [(j8DataGen p Rg Rt hgen O).t]).length (by simp [sizesJ8])
    rw [data_rowsG hgen O]
    simpa [ComplJ8Data.rowsOfT, j8DataGen] using h
  obtain ⟨hb, -, -, -, -, -, -, -, hroot⟩ :=
    bigBound_singleG hgen O hpG (hclA 0) (hclA 1) hRt hop5 hN
  have hl2 : ∀ a ∈ (j8DataGen p Rg Rt hgen O).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1] :=
    fun a ha => ⟨(hb a ha).1, (hb a ha).2.2⟩
  have hcv : Quad.mk (algebraMap (ZMod p) K δ) (((BRunG δ b Rt hgen O o).M χ).pubsC 0)
      (((BRunG δ b Rt hgen O o).M χ).pubsC 1) = cvT δ (j8DataGen p Rg Rt hgen O) χ := by
    show Quad.mk _ (pubsCOf δ b _ (cells_posG Rt hgen O) (o) χ 0)
      (pubsCOf δ b _ (cells_posG Rt hgen O) (o) χ 1) = _
    have e0 : pubsCOf δ b _ (cells_posG Rt hgen O) (o) χ 0 = pub2 δ (cvT δ (j8DataGen p Rg Rt hgen O) χ) 0 := by
      simp [pubsCOf, pubsC0]
    have e1 : pubsCOf δ b _ (cells_posG Rt hgen O) (o) χ 1 = pub2 δ (cvT δ (j8DataGen p Rg Rt hgen O) χ) 1 := by
      simp [pubsCOf, pubsC0]
    rw [e0, e1]
    exact pub2_mk2 δ _ 0 rfl
  have hbb : ((j8DataGen p Rg Rt hgen O).cells.map fun y =>
      btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (j8DataGen p Rg Rt hgen O)) (hdN y) +
        btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (j8DataGen p Rg Rt hgen O)) (tlN y)).sum =
      ((j8DataGen p Rg Rt hgen O).cells.map fun y =>
        bhTG δ b Rt hgen O o hpG h31 χ (hdN' y) + bhTG δ b Rt hgen O o hpG h31 χ (tlN' y)).sum := by
    refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
    rw [bt_bhG δ b Rt hgen O o hpG h31 hl2 hroot χ _ fun a ha hp => child_bigG Rt hgen O y hy _ (Or.inl rfl) a ha hp,
      bt_bhG δ b Rt hgen O o hpG h31 hl2 hroot χ _ fun a ha hp => child_bigG Rt hgen O y hy _ (Or.inr rfl) a ha hp,
      hdN_eq, tlN_eq]
  rw [show ((BRunG δ b Rt hgen O o).M χ).m = ComplJ8Comp.mCOf (j8DataGen p Rg Rt hgen O).H (ComplJ8.cJ s f r) from rfl,
    List.map_append, List.sum_append, claim_sumG δ Rt hgen O χ, pin_sumG δ b Rt hgen O o hpG h31 χ, hcv,
    cvT_runG δ Rt hgen O χ, mbT_runG δ b Rt hgen O o hpG h31 χ, hbb]
  ring

/-- **`balV` at the run, closed** (`OpenJ8.balV`'s form, nothing carried): clause 1 (`balV1_runG`), clause 2
(`balV2_runG`), clause 3 (`balV3_runG`), at `complJ8`'s binders `hpG hax hop5 hclA hRt h31`. -/
theorem balV_closedG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hpG : p = Nock.Atoms.p) (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) :
    ∀ χ, (BRunG δ b Rt hgen O o).Good χ →
      ((AcceptsJ8P.claimRecsJ8 δ χ (ComplJ8.cJ s f r) ((BRunG δ b Rt hgen O o).M χ).m ++
          AcceptsJ8P.pinRecsJ8 δ (BRunG δ b Rt hgen O o).Pb χ).map fun x => (FiniteIO.compress (m := 5)
          ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6), Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
        Quad.mk (algebraMap (ZMod p) K δ) (((BRunG δ b Rt hgen O o).M χ).pubsC 0)
            (((BRunG δ b Rt hgen O o).M χ).pubsC 1) +
          Quad.mk (algebraMap (ZMod p) K δ) (((BRunG δ b Rt hgen O o).M χ).pubsA AtomChipHQ.pubMB)
            (((BRunG δ b Rt hgen O o).M χ).pubsA (AtomChipHQ.pubMB + 1)) ∧
      Quad.mk (algebraMap (ZMod p) K δ) (((BRunG δ b Rt hgen O o).M χ).pubsA CellHQ.pubHQ)
          (((BRunG δ b Rt hgen O o).M χ).pubsA (CellHQ.pubHQ + 1)) =
        Quad.mk (algebraMap (ZMod p) K δ) (((BRunG δ b Rt hgen O o).M χ).pubsA AtomChipHQ.pubC)
            (((BRunG δ b Rt hgen O o).M χ).pubsA (AtomChipHQ.pubC + 1)) +
          Quad.mk (algebraMap (ZMod p) K δ) (((BRunG δ b Rt hgen O o).M χ).pubsV WalkHQ.pubXQ)
            (((BRunG δ b Rt hgen O o).M χ).pubsV (WalkHQ.pubXQ + 1)) ∧
      (((BRunG δ b Rt hgen O o).M χ).pubsA 0 = 0 ∧ ((BRunG δ b Rt hgen O o).M χ).pubsA 1 = 0) :=
  fun χ _ => ⟨balV1_runG δ b Rt hgen O o hpG hop5 hclA hRt h31 χ,
    balV2_runG δ b Rt hgen O o hpG hax hop5 hclA hRt h31 χ, balV3_runG δ b Rt hgen O o hpG h31 χ⟩

end BalV1
end
end ComplJ8OfBalG_1

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen
