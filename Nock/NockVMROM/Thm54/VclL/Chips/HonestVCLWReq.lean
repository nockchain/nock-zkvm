/-
  Nock/NockVMROM/Thm54/VclL/Chips/HonestVCLWReq.lean

  **The walk family's honest requests are the
  path family's** (twin of `HonestMemReq.req_eq`).

  `HonestVCLW.req` is DEFINED as the three accumulator terminals of the cell table and the walk
  table.  Here, given `hslot` (every deep read is a defined slot), they are shown to be EXACTLY the
  right-hand sides of `HonestVCL.req_eq` (so the compute side's closed form `honestReqCF` is
  unchanged):
  * validity: `vTot = 0` (the cell rows are the path family's, `vcsOf cells []`);
  * export: `xTot − yTot = Σ_{shallowSided reads} den⁻¹` — every walk node is a cell of `d.cells`
    (`walkRows_node_mem`) and a walk row's consume key is that cell's side-0 export record, so the
    walk consumers in `xs0W` cancel against `yTot`;
  * path-provide: `pTot = Σ_{x ∈ pathKind preads} den⁻¹(pReq x)` — the TRIE MULTISET IDENTITY
    (`trie_pSum`): over the DFS nodes of `trie root n bs T`, `Σ mL·inv recL + mR·inv recR` is
    `Σ_{s ∈ T} inv pReq(root, axisFold (bs ++ s))`, by structural induction on the noun; the forest
    regroups by root (`sum_regroup_fst`), and BFS is a permutation of DFS (`bfsForest_perm_dfsForest`).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestVCLW
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemReq
import Nock.NockVMROM.Thm54.VclL.Walk.GenWalkCount

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock
open Nock.Walk
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Noun- and list-level facts -/

section NounLevel

theorem one_le_axisFold (bs : List Bool) : 1 ≤ axisFold bs := by
  induction bs using List.reverseRecOn with
  | nil => simp [axisFold]
  | append_singleton bs b ih => rw [axisFold_append]; omega

/-- `axisBits` inverts `axisFold` on every bit list. -/
theorem axisBits_axisFold (bs : List Bool) : axisBits (axisFold bs) = bs := by
  induction bs using List.reverseRecOn with
  | nil => exact axisBits_of_lt_two (by simp [axisFold])
  | append_singleton bs b ih =>
    have h1 := one_le_axisFold bs
    rw [axisFold_append, axisBits_of_two_le (by split <;> omega)]
    have hdiv : (2 * axisFold bs + (if b then 1 else 0)) / 2 = axisFold bs := by split <;> omega
    have hmod : decide ((2 * axisFold bs + (if b then 1 else 0)) % 2 = 1) = b := by
      cases b <;> simp <;> omega
    rw [hdiv, ih, hmod]

theorem chainWalk_isSome_cons {n : Noun} {b : Bool} {s : List Bool} (h : (chainWalk n (b :: s)).isSome) :
    ∃ l r, n = .cell l r := by
  cases n with
  | atom a => simp [chainWalk] at h
  | cell l r => exact ⟨l, r, rfl⟩

/-- Splitting a target list (all non-empty) by its first bit. -/
theorem sum_sideTails {M : Type*} [AddCommMonoid M] (g : List Bool → M) :
    ∀ (T : List (List Bool)), (∀ s ∈ T, s ≠ []) →
      (T.map g).sum = ((sideTails false T).map fun s => g (false :: s)).sum +
        ((sideTails true T).map fun s => g (true :: s)).sum
  | [], _ => by simp [sideTails]
  | s :: T, h => by
    have ih := sum_sideTails g T (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases s with
    | nil => exact absurd rfl (h [] (List.mem_cons_self))
    | cons c s =>
      cases c <;> simp [sideTails, List.filterMap_cons] at ih ⊢ <;> rw [ih] <;> abel

/-- Splitting off the empty suffixes. -/
theorem sum_count_nil {M : Type*} [AddCommMonoid M] (h : List Bool → M) :
    ∀ (L : List (List Bool)), (L.map h).sum = L.count [] • h [] + ((L.filter fun s => !s.isEmpty).map h).sum
  | [] => by simp
  | s :: L => by
    have ih := sum_count_nil h L
    cases s with
    | nil => simp [ih, List.count_cons, add_smul]; abel
    | cons c s => simp [ih, List.count_cons]; abel

theorem contT_of_not_cont {b : Bool} {T : List (List Bool)} (h : cont b T = false) : contT b T = [] := by
  unfold cont at h
  simpa using h

theorem dfsForest_sum {LT M : Type*} [AddCommMonoid M] (f : NTree LT → M) :
    ∀ l : List (NTree LT), ((dfsForest l).map f).sum = (l.map fun c => ((dfsTree c).map f).sum).sum
  | [] => by simp
  | c :: l => by rw [dfsForest_cons, List.map_append, List.sum_append, dfsForest_sum f l]; simp

/-- Regrouping a sum by the first coordinate. -/
theorem sum_regroup_fst_aux {α M : Type*} [DecidableEq α] [AddCommMonoid M] {β : Type*} (φ : α × β → M) :
    ∀ (L : List (α × β)) (S : List α), S.Nodup → (∀ x ∈ L, x.1 ∈ S) →
      (S.map fun r => ((L.filter fun x => decide (x.1 = r)).map φ).sum).sum = (L.map φ).sum
  | [], S, _, _ => by simp
  | a :: L, S, hS, hL => by
    have ih := sum_regroup_fst_aux φ L S hS (fun x hx => hL x (List.mem_cons_of_mem _ hx))
    have ha : a.1 ∈ S := hL a List.mem_cons_self
    have e : ∀ r, ((((a :: L).filter fun x => decide (x.1 = r))).map φ).sum =
        (if a.1 = r then φ a else 0) + ((L.filter fun x => decide (x.1 = r)).map φ).sum := by
      intro r
      by_cases h : a.1 = r <;> simp [List.filter_cons, h]
    simp only [e, List.sum_map_add, ih, List.map_cons, List.sum_cons]
    congr 1
    rw [← List.sum_toFinset _ hS, Finset.sum_ite_eq]
    simp [ha]

theorem sum_regroup_fst {α M : Type*} [DecidableEq α] [AddCommMonoid M] {β : Type*} (φ : α × β → M)
    (L : List (α × β)) :
    (((L.map Prod.fst).dedup).map fun r => ((L.filter fun x => decide (x.1 = r)).map φ).sum).sum =
      (L.map φ).sum :=
  sum_regroup_fst_aux φ L _ (List.nodup_dedup _)
    (fun x hx => List.mem_dedup.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩))

end NounLevel

/-! ## 2. The trie multiset identity -/

section Trie
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] {δF : F}
  [Fact (¬ IsSquare (algebraMap F K δF))]
variable (γ ρ z : Quad (algebraMap F K δF)) (cells : List Noun)

/-- The left path record of a trie node, in the walk row's form `(root, hd, 2·prefix, rootIdx)`. -/
def recLN (w : WN) : Fin 8 → Quad (algebraMap F K δF) :=
  ![(GlobalCarryRecognizer.enc z w.root).size, (GlobalCarryRecognizer.enc z w.root).dyck,
    (GlobalCarryRecognizer.enc z w.root).leaf,
    (GlobalCarryRecognizer.enc z (hdN w.node)).size, (GlobalCarryRecognizer.enc z (hdN w.node)).dyck,
    (GlobalCarryRecognizer.enc z (hdN w.node)).leaf,
    liftQ δF (2 * ((axisFold w.bits : ℕ) : F)), liftQ δF ((cells.idxOf w.root : ℕ) : F)]

/-- The right path record `(root, tl, 2·prefix + 1, rootIdx)`. -/
def recRN (w : WN) : Fin 8 → Quad (algebraMap F K δF) :=
  ![(GlobalCarryRecognizer.enc z w.root).size, (GlobalCarryRecognizer.enc z w.root).dyck,
    (GlobalCarryRecognizer.enc z w.root).leaf,
    (GlobalCarryRecognizer.enc z (tlN w.node)).size, (GlobalCarryRecognizer.enc z (tlN w.node)).dyck,
    (GlobalCarryRecognizer.enc z (tlN w.node)).leaf,
    liftQ δF (2 * ((axisFold w.bits : ℕ) : F) + 1), liftQ δF ((cells.idxOf w.root : ℕ) : F)]

/-- A trie node's path-provide term `mL·inv(recL) + mR·inv(recR)`. -/
def pTermN (t : NTree WN) : Quad (algebraMap F K δF) :=
  liftQ δF ((t.label.mL : ℕ) : F) * cinv δF γ ρ (recLN z cells t.label) +
    liftQ δF ((t.label.mR : ℕ) : F) * cinv δF γ ρ (recRN z cells t.label)

/-- The record of the read of `root` along `bits`. -/
def gRec (root : Noun) (bits : List Bool) : Quad (algebraMap F K δF) :=
  cinv δF γ ρ (pReq δF z cells (root, axisFold bits))

theorem liftQ_nat (m : ℕ) : liftQ δF ((m : ℕ) : F) = ((m : ℕ) : Quad (algebraMap F K δF)) := by
  induction m with
  | zero => simp [liftQ]
  | succ m ih => push_cast; simp [liftQ] at ih ⊢

theorem recLN_eq (w : WN) (l r : Noun) (hn : w.node = .cell l r)
    (hw : chainWalk w.root w.bits = some (.cell l r)) :
    recLN (δF := δF) z cells w = pReq δF z cells (w.root, axisFold (w.bits ++ [false])) := by
  have hs : (Noun.slot (axisFold (w.bits ++ [false])) w.root).getD (.atom 0) = l := by
    rw [slot_eq_chainWalk _ (one_le_axisFold _), axisBits_axisFold, chainWalk_append, hw]; rfl
  unfold recLN pReq
  rw [hs, axisFold_append, hn]
  simp only [hdN, Bool.false_eq_true, if_false, add_zero]
  push_cast
  rfl

theorem recRN_eq (w : WN) (l r : Noun) (hn : w.node = .cell l r)
    (hw : chainWalk w.root w.bits = some (.cell l r)) :
    recRN (δF := δF) z cells w = pReq δF z cells (w.root, axisFold (w.bits ++ [true])) := by
  have hs : (Noun.slot (axisFold (w.bits ++ [true])) w.root).getD (.atom 0) = r := by
    rw [slot_eq_chainWalk _ (one_le_axisFold _), axisBits_axisFold, chainWalk_append, hw]; rfl
  unfold recRN pReq
  rw [hs, axisFold_append, hn]
  simp only [tlN, if_true]
  push_cast
  rfl

/-- **The trie multiset identity.** -/
theorem trie_pSum (root : Noun) :
    ∀ (n : Noun) (bs : List Bool) (T : List (List Bool)), chainWalk root bs = some n →
      (∀ s ∈ T, s ≠ [] ∧ (chainWalk n s).isSome) →
      ((dfsTree (trie root n bs T)).map (pTermN γ ρ z cells)).sum =
        (T.map fun s => gRec γ ρ z cells root (bs ++ s)).sum := by
  intro n
  induction n with
  | atom a =>
    intro bs T _ hT
    have hT0 : T = [] := by
      cases T with
      | nil => rfl
      | cons s T =>
        obtain ⟨hne, hs⟩ := hT s List.mem_cons_self
        cases s with
        | nil => exact absurd rfl hne
        | cons c s => simp [chainWalk] at hs
    subst hT0
    rw [dfsTree_eq]
    simp only [trie, NTree.children, dfsForest_nil, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    unfold pTermN
    simp [NTree.label, multT, sideTails, liftQ]
  | cell l r ihl ihr =>
    intro bs T hw hT
    have hTne : ∀ s ∈ T, s ≠ [] := fun s hs => (hT s hs).1
    -- the child step
    have hchild : ∀ b : Bool,
        (if cont b T then ((dfsTree (trie root (if b then r else l) (bs ++ [b]) (contT b T))).map
          (pTermN γ ρ z cells)).sum else 0) =
        ((contT b T).map fun s => gRec γ ρ z cells root (bs ++ b :: s)).sum := by
      intro b
      by_cases hc : cont b T = true
      · rw [if_pos hc]
        have hw' : chainWalk root (bs ++ [b]) = some (if b then r else l) := by
          rw [chainWalk_append, hw]
        have hT' : ∀ s ∈ contT b T, s ≠ [] ∧ (chainWalk (if b then r else l) s).isSome := by
          intro s hs
          obtain ⟨hbs, hne⟩ := mem_contT hs
          refine ⟨hne, ?_⟩
          have := (hT _ hbs).2
          simpa [chainWalk] using this
        have e : (fun s => gRec γ ρ z cells root (bs ++ b :: s)) =
            fun s => gRec γ ρ z cells root ((bs ++ [b]) ++ s) := funext fun s => by simp
        rw [e]
        cases b
        · exact ihl _ _ hw' hT'
        · exact ihr _ _ hw' hT'
      · have hc' : cont b T = false := by simpa using hc
        rw [if_neg hc, contT_of_not_cont hc']
        simp
    have hdfs : ((dfsTree (trie root (.cell l r) bs T)).map (pTermN γ ρ z cells)).sum =
        pTermN γ ρ z cells (trie root (.cell l r) bs T) +
          ((if cont false T then ((dfsTree (trie root l (bs ++ [false]) (contT false T))).map
            (pTermN γ ρ z cells)).sum else 0) +
          (if cont true T then ((dfsTree (trie root r (bs ++ [true]) (contT true T))).map
            (pTermN γ ρ z cells)).sum else 0)) := by
      rw [dfsTree_eq, trie_children_cell, List.map_cons, List.sum_cons, dfsForest_append]
      congr 1
      rw [List.map_append, List.sum_append]
      congr 1 <;> split_ifs <;> simp [dfsForest_cons]
    have h0 := hchild false
    have h1 := hchild true
    simp only [Bool.false_eq_true, if_false, if_true] at h0 h1
    rw [hdfs, h0, h1, sum_sideTails _ T hTne, sum_count_nil _ (sideTails false T),
      sum_count_nil _ (sideTails true T)]
    have hL : pTermN γ ρ z cells (trie root (.cell l r) bs T) =
        (sideTails false T).count [] • gRec γ ρ z cells root (bs ++ [false]) +
          (sideTails true T).count [] • gRec γ ρ z cells root (bs ++ [true]) := by
      unfold pTermN gRec
      rw [recLN_eq z cells _ l r rfl hw, recRN_eq z cells _ l r rfl hw, liftQ_nat, liftQ_nat,
        nsmul_eq_mul, nsmul_eq_mul]
      rfl
    rw [hL]
    simp only [contT]
    abel

end Trie

/-! ## 3. The honest datum's terminals -/

section Honest
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] {hT hP hC kr : ℕ}

namespace HonestVCLW
variable (H : HonestVCLW (K := K) δF hT hP hC kr)

theorem cells_pos : 0 < H.d.cells.length := H.hC0 ▸ H.V.hM (tCW hT hP)

theorem cells_hyps :
    H.d.cells.Nodup ∧ (∀ n ∈ H.d.cells, n.isCell = true) ∧
    (∀ n ∈ H.d.cells, ∀ c ∈ childCells n, c ∈ H.d.cells) :=
  ⟨closureOf_nodup _, fun n hn => closureOf_isCell hn, fun n hn c hc => closureOf_closed hn hc⟩

/-- A defined-slot path read's targets from its root. -/
theorem targets_ok (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome) (r : Noun) :
    ∀ s ∈ targetsOf H.d.preads r, s ≠ [] ∧ (chainWalk r s).isSome := by
  intro s hs
  refine ⟨targetsOf_ne _ r s hs, ?_⟩
  unfold targetsOf at hs
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
  obtain ⟨hxk, hxr⟩ := List.mem_filter.mp hx
  have hxr : x.1 = r := of_decide_eq_true hxr
  have hpk := mem_pathKind.mp hxk
  have hsl := hslot x (by unfold pathReads; exact List.mem_dedup.mpr (List.mem_filter.mpr hpk))
  rw [slot_eq_chainWalk _ (by have := two_le_of_path hpk.2; omega), hxr] at hsl
  exact hsl

/-- **Every walk node is a cell of the table** (`hslot`: a target never passes an atom). -/
theorem walkRows_node_mem (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome) :
    ∀ t ∈ walkRows H.d.cells H.d.preads, t.label.node ∈ H.d.cells := by
  obtain ⟨-, -, hclosed⟩ := H.cells_hyps
  intro t ht
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp ht
  let Q : Noun → List Bool → List (List Bool) → Prop := fun n _ T =>
    n ∈ H.d.cells ∧ ∀ s ∈ T, s ≠ [] ∧ (chainWalk n s).isSome
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
    obtain ⟨x, y, hxy⟩ := chainWalk_isSome_cons hsome
    apply hclosed _ hmem
    rw [hxy]
    cases b <;> simp_all [childCells, selfCell]
  rcases mem_walkForest hc with ⟨-, rfl⟩ | ⟨r, hr, rfl⟩
  · have hq : Q (H.d.cells.headD (.atom 0)) [] [] := by
      refine ⟨?_, by simp⟩
      have := H.cells_pos
      cases h : H.d.cells with
      | nil => rw [h] at this; simp at this
      | cons a l => simp
    obtain ⟨n', bs', T', rfl, hq'⟩ := inTree_trie_inv _ Q hQ hin _ _ _ rfl hq
    rw [(trie_label _ _ _ _).1]; exact hq'.1
  · have hrc : r ∈ H.d.cells := by
      have hne := targetsOf_ne_nil hr
      obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨hsne, hsome⟩ := H.targets_ok hslot r s hs
      obtain ⟨b, s', rfl⟩ : ∃ b s', s = b :: s' := by
        cases s with
        | nil => exact absurd rfl hsne
        | cons b s' => exact ⟨b, s', rfl⟩
      obtain ⟨x, y, rfl⟩ := chainWalk_isSome_cons hsome
      unfold walkRoots at hr
      obtain ⟨z0, hz0, hz0r⟩ := List.mem_map.mp (List.mem_dedup.mp hr)
      have hroot : z0.1 ∈ H.d.roots := pread_root_mem H.d (mem_pathKind.mp hz0).1
      rw [hz0r] at hroot
      exact selfCell_subset_closureOf hroot (by simp [selfCell])
    have hq : Q r [] (targetsOf H.d.preads r) := ⟨hrc, H.targets_ok hslot r⟩
    obtain ⟨n', bs', T', rfl, hq'⟩ := inTree_trie_inv _ Q hQ hin _ _ _ rfl hq
    rw [(trie_label _ _ _ _).1]; exact hq'.1

theorem xs0W_subset (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome) :
    ∀ c ∈ xs0W H.d, c ∈ H.d.cells := by
  intro c hc
  simp only [xs0W, List.mem_append, List.mem_map] at hc
  rcases hc with ⟨t, ht, rfl⟩ | ⟨x, hx, rfl⟩
  · exact H.walkRows_node_mem hslot t ht
  · apply exportConsumers_subset H.d
    rw [← sidedConsumers_fst]
    exact List.mem_map.mpr ⟨x, by simp only [sidedConsumers, List.mem_append]; exact Or.inr (List.mem_filter.mp hx).1, rfl⟩

theorem xs1W_subset : ∀ c ∈ xs1W H.d, c ∈ H.d.cells := by
  intro c hc
  simp only [xs1W, List.mem_map] at hc
  obtain ⟨x, hx, rfl⟩ := hc
  apply exportConsumers_subset H.d
  rw [← sidedConsumers_fst]
  exact List.mem_map.mpr ⟨x, by simp only [sidedConsumers, List.mem_append]; exact Or.inr (List.mem_filter.mp hx).1, rfl⟩

variable (χ : Coins frameVCL K)

/-- **Validity (accumulator 0)**: `vTot = 0`. -/
theorem vTot_eq_zero : H.vTot χ = 0 := by
  obtain ⟨hnd, hcell, hclosed⟩ := H.cells_hyps
  unfold vTot cellRows
  rw [H.hC0]
  have := cell_vTotal (δF := δF) (γC χ) (ρC χ) (zC χ) H.d.cells [] (xs0W H.d) (xs1W H.d)
    hnd hcell hclosed (fun b hb => by simp at hb)
  simpa using this

/-- A walk row's consume key is its node's side-0 export record. -/
theorem wxKey_eq (j : ℕ) :
    wxKeyV δF (walkFillInv δF (γC χ) (ρC χ) (H.wRows χ j)) =
      xReq δF (zC χ) H.d.cells (wTrie H.d.cells H.d.preads j).label.node false := rfl

/-- The walk's export-consume total: `Σ_{walk nodes} den⁻¹(xReq · false)`. -/
theorem yTot_eq : H.yTot χ =
    (((walkRows H.d.cells H.d.preads).map fun t => t.label.node).map fun n =>
      cinv δF (γC χ) (ρC χ) (xReq δF (zC χ) H.d.cells n false)).sum := by
  unfold yTot
  rw [H.hW0, List.map_map]
  refine Eq.trans ?_ (sum_range_getD (walkRows H.d.cells H.d.preads) (trie (.atom 0) (.atom 0) [] [])
    ((fun n => cinv δF (γC χ) (ρC χ) (xReq δF (zC χ) H.d.cells n false)) ∘ fun t => t.label.node))
  rfl

/-- **Export (accumulator 1)**: `xTot − yTot = Σ_{shallow lookups} den⁻¹`. -/
theorem xTot_sub_yTot_eq (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome) :
    H.xTot χ - H.yTot χ = ((shallowSided H.d.reads).map fun c =>
      (FiniteIO.compress (m := 11) ⟨γC χ, ρC χ⟩ (xReq δF (zC χ) H.d.cells c.1 c.2))⁻¹).sum := by
  obtain ⟨hnd, -, -⟩ := H.cells_hyps
  have hx : H.xTot χ = ((xs0W H.d).map fun c => cinv δF (γC χ) (ρC χ) (xReq δF (zC χ) H.d.cells c false)).sum +
      ((xs1W H.d).map fun c => cinv δF (γC χ) (ρC χ) (xReq δF (zC χ) H.d.cells c true)).sum := by
    unfold xTot cellRows
    rw [H.hC0]
    exact cell_xTotal (δF := δF) (γC χ) (ρC χ) (zC χ) H.d.cells (vcsOf H.d.cells []) (xs0W H.d) (xs1W H.d)
      hnd (H.xs0W_subset hslot) H.xs1W_subset
  rw [hx, H.yTot_eq, sum_sided_split (shallowSided H.d.reads)
    fun n b => (FiniteIO.compress (m := 11) ⟨γC χ, ρC χ⟩ (xReq δF (zC χ) H.d.cells n b))⁻¹]
  simp only [xs0W, xs1W, List.map_append, List.sum_append, cinv]
  abel

/-- A walk row's path-provide term is its trie node's `pTermN`. -/
theorem wpTerm_eq (j : ℕ) :
    wpTermV δF (walkFillInv δF (γC χ) (ρC χ) (H.wRows χ j)) =
      pTermN (γC χ) (ρC χ) (zC χ) H.d.cells (wTrie H.d.cells H.d.preads j) := rfl

/-- **Path-provide (accumulator 2)**: `pTot = Σ_{deep reads} den⁻¹(pReq)`. -/
theorem pTot_eq (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome) :
    H.pTot χ = ((H.d.preads.filter fun r => isPathAx r.2).map fun r =>
      (FiniteIO.compress (m := 8) ⟨γC χ, ρC χ⟩ (pReq δF (zC χ) H.d.cells r))⁻¹).sum := by
  set Φ := pTermN (δF := δF) (γC χ) (ρC χ) (zC χ) H.d.cells with hΦ
  have h1 : H.pTot χ = ((walkRows H.d.cells H.d.preads).map Φ).sum := by
    unfold pTot
    rw [H.hW0]
    exact (Finset.sum_congr rfl fun j _ => H.wpTerm_eq χ j).trans
      (sum_range_getD (walkRows H.d.cells H.d.preads) (trie (.atom 0) (.atom 0) [] []) Φ)
  have h2 : ((walkRows H.d.cells H.d.preads).map Φ).sum = ((dfsForest (walkForest H.d.cells H.d.preads)).map Φ).sum :=
    ((bfsForest_perm_dfsForest _).map Φ).sum_eq
  rw [h1, h2, dfsForest_sum]
  change _ = ((pathKind H.d.preads).map _).sum
  unfold walkForest
  split_ifs with hroots
  · -- no path read: the dummy trie has no targets
    have hpk : pathKind H.d.preads = [] := by
      by_contra hne
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
      have : x.1 ∈ walkRoots H.d.preads := List.mem_dedup.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩)
      rw [hroots] at this; simp at this
    rw [hpk]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have := trie_pSum (δF := δF) (γC χ) (ρC χ) (zC χ) H.d.cells (H.d.cells.headD (.atom 0)) (H.d.cells.headD (.atom 0)) [] []
      rfl (by simp)
    simpa using this
  · rw [List.map_map]
    have hper : ∀ r ∈ walkRoots H.d.preads,
        (Function.comp (fun c => ((dfsTree c).map Φ).sum) (fun r => trie r r [] (targetsOf H.d.preads r))) r =
        (((pathKind H.d.preads).filter fun x => decide (x.1 = r)).map fun x =>
          (FiniteIO.compress (m := 8) ⟨γC χ, ρC χ⟩ (pReq δF (zC χ) H.d.cells x))⁻¹).sum := by
      intro r _
      simp only [Function.comp]
      rw [trie_pSum (δF := δF) (γC χ) (ρC χ) (zC χ) H.d.cells r r [] _ rfl (H.targets_ok hslot r)]
      unfold targetsOf
      rw [List.map_map]
      congr 1
      refine List.map_congr_left fun x hx => ?_
      obtain ⟨hxk, hxr⟩ := List.mem_filter.mp hx
      have hxr : x.1 = r := of_decide_eq_true hxr
      have h2x := two_le_of_path (mem_pathKind.mp hxk).2
      simp only [Function.comp, List.nil_append, gRec, cinv]
      rw [axisFold_axisBits _ (by omega), ← hxr]
    rw [List.map_congr_left hper]
    exact sum_regroup_fst _ _

/-- **`honestReq` is `Σ den⁻¹` over the path family's honest requests, per accumulator**
(the right-hand sides of `HonestVCL.req_eq`). -/
theorem req_eq (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome) :
    H.req χ 0 = 0 ∧
    H.req χ 1 = ((shallowSided H.d.reads).map fun c =>
      (FiniteIO.compress (m := 11) ⟨γC χ, ρC χ⟩ (xReq δF (zC χ) H.d.cells c.1 c.2))⁻¹).sum ∧
    H.req χ 2 = ((H.d.preads.filter fun r => isPathAx r.2).map fun r =>
      (FiniteIO.compress (m := 8) ⟨γC χ, ρC χ⟩ (pReq δF (zC χ) H.d.cells r))⁻¹).sum :=
  ⟨H.vTot_eq_zero χ, H.xTot_sub_yTot_eq χ hslot, H.pTot_eq χ hslot⟩

end HonestVCLW

end Honest

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
