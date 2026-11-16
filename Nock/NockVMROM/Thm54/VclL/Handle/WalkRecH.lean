/-
  Nock/NockVMROM/Thm54/VclL/Handle/WalkRecH.lean

  Each row provides the two handle walk records
  `(rootIdx, 2·prefix + b, kind_b, val_b)` with multiplicities `mL`, `mR`.

  * `readRecH cells (root, ax)`: the handle walk record of a read: `(idx root, ax, hdl (slot ax root))`;
  * `trie_hSum`: the TRIE MULTISET IDENTITY at handle records, for an ARBITRARY weight `W` into any
    additive monoid: over the DFS nodes of `trie root n bs T`, `mL•W(recL) + mR•W(recR)` sums to
    `Σ_{s ∈ T} W (readRecH root (axisFold (bs ++ s)))`;
  * `walk_provide_total`: over the BFS walk rows of a demand, the provided total equals
    `Σ_{r ∈ pathKind preads} W (readRecH cells r)` (hypothesis `hslot`: every deep read is a defined
    slot, as `HonestVCLW`);
  * `walkRowH_kids`: the honest `kL vL kR vR` of a row are the handles of the node's children.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkH
import Nock.NockVMROM.Thm54.VclL.Handle.HonestRows
import Nock.NockVMROM.Thm54.VclL.Chips.HonestVCLWReq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

noncomputable section

section Rec
variable {F : Type} [Field F]

/-- **The handle walk record of a read `(root, ax)`**: `(rootIdx, axis, handle of the slot)` (the
shape `ChipH.walkRec` consumes). -/
def readRecH (cells : List Noun) (r : Noun × ℕ) : F × F × (F × F) :=
  ((cells.idxOf r.1 : ℕ), (r.2 : F), hdl cells ((Noun.slot r.2 r.1).getD (.atom 0)))

/-- The left handle record a walk row provides: `(rootIdx, 2·prefix, handle of hd node)`. -/
def recLH (cells : List Noun) (w : WN) : F × F × (F × F) :=
  ((cells.idxOf w.root : ℕ), ((2 * axisFold w.bits : ℕ) : F), hdl cells (hdN w.node))

/-- The right handle record: `(rootIdx, 2·prefix + 1, handle of tl node)`. -/
def recRH (cells : List Noun) (w : WN) : F × F × (F × F) :=
  ((cells.idxOf w.root : ℕ), ((2 * axisFold w.bits + 1 : ℕ) : F), hdl cells (tlN w.node))

variable {M : Type} [AddCommMonoid M]

/-- A trie node's provided total at weight `W`: `mL•W(recL) + mR•W(recR)`. -/
def provH (W : F × F × (F × F) → M) (cells : List Noun) (w : WN) : M :=
  w.mL • W (recLH cells w) + w.mR • W (recRH cells w)

theorem recLH_eq (cells : List Noun) (w : WN) (l r : Noun) (hn : w.node = .cell l r)
    (hw : chainWalk w.root w.bits = some (.cell l r)) :
    (recLH cells w : F × F × (F × F)) = readRecH cells (w.root, axisFold (w.bits ++ [false])) := by
  have hs : (Noun.slot (axisFold (w.bits ++ [false])) w.root).getD (.atom 0) = l := by
    rw [slot_eq_chainWalk _ (one_le_axisFold _), axisBits_axisFold, chainWalk_append, hw]; rfl
  unfold recLH readRecH
  rw [hs, axisFold_append, hn]
  simp [hdN]

theorem recRH_eq (cells : List Noun) (w : WN) (l r : Noun) (hn : w.node = .cell l r)
    (hw : chainWalk w.root w.bits = some (.cell l r)) :
    (recRH cells w : F × F × (F × F)) = readRecH cells (w.root, axisFold (w.bits ++ [true])) := by
  have hs : (Noun.slot (axisFold (w.bits ++ [true])) w.root).getD (.atom 0) = r := by
    rw [slot_eq_chainWalk _ (one_le_axisFold _), axisBits_axisFold, chainWalk_append, hw]; rfl
  unfold recRH readRecH
  rw [hs, axisFold_append, hn]
  simp [tlN]

/-- **The trie multiset identity at handle records** (any weight `W`). -/
theorem trie_hSum (W : F × F × (F × F) → M) (cells : List Noun) (root : Noun) :
    ∀ (n : Noun) (bs : List Bool) (T : List (List Bool)), chainWalk root bs = some n →
      (∀ s ∈ T, s ≠ [] ∧ (chainWalk n s).isSome) →
      ((dfsTree (trie root n bs T)).map (fun t => provH W cells t.label)).sum =
        (T.map fun s => W (readRecH cells (root, axisFold (bs ++ s)))).sum := by
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
    unfold provH
    simp [NTree.label, multT, sideTails]
  | cell l r ihl ihr =>
    intro bs T hw hT
    have hTne : ∀ s ∈ T, s ≠ [] := fun s hs => (hT s hs).1
    have hchild : ∀ b : Bool,
        (if cont b T then ((dfsTree (trie root (if b then r else l) (bs ++ [b]) (contT b T))).map
          (fun t => provH W cells t.label)).sum else 0) =
        ((contT b T).map fun s => W (readRecH cells (root, axisFold (bs ++ b :: s)))).sum := by
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
        have e : (fun s => W (readRecH cells (root, axisFold (bs ++ b :: s)))) =
            fun s => W (readRecH cells (root, axisFold ((bs ++ [b]) ++ s))) := funext fun s => by simp
        rw [e]
        cases b
        · exact ihl _ _ hw' hT'
        · exact ihr _ _ hw' hT'
      · have hc' : cont b T = false := by simpa using hc
        rw [if_neg hc, contT_of_not_cont hc']
        simp
    have hdfs : ((dfsTree (trie root (.cell l r) bs T)).map (fun t => provH W cells t.label)).sum =
        provH W cells (trie root (.cell l r) bs T).label +
          ((if cont false T then ((dfsTree (trie root l (bs ++ [false]) (contT false T))).map
            (fun t => provH W cells t.label)).sum else 0) +
          (if cont true T then ((dfsTree (trie root r (bs ++ [true]) (contT true T))).map
            (fun t => provH W cells t.label)).sum else 0)) := by
      rw [dfsTree_eq, trie_children_cell, List.map_cons, List.sum_cons, dfsForest_append]
      congr 1
      rw [List.map_append, List.sum_append]
      congr 1 <;> split_ifs <;> simp [dfsForest_cons]
    have h0 := hchild false
    have h1 := hchild true
    simp only [Bool.false_eq_true, if_false, if_true] at h0 h1
    rw [hdfs, h0, h1, sum_sideTails _ T hTne, sum_count_nil _ (sideTails false T),
      sum_count_nil _ (sideTails true T)]
    have hL : provH W cells (trie root (.cell l r) bs T).label =
        (sideTails false T).count [] • W (readRecH cells (root, axisFold (bs ++ [false]))) +
          (sideTails true T).count [] • W (readRecH cells (root, axisFold (bs ++ [true]))) := by
      unfold provH
      rw [recLH_eq cells _ l r rfl hw, recRH_eq cells _ l r rfl hw]
      rfl
    rw [hL]
    simp only [contT]
    abel

end Rec

/-! ## The walk rows' provided total -/

section Walk
variable {F : Type} [Field F] {M : Type} [AddCommMonoid M]

/-- A defined-slot path read's targets from its root (as `HonestVCLW.targets_ok`). -/
theorem targets_ok_of (preads : List (Noun × ℕ))
    (hslot : ∀ r ∈ pathReads preads, (Noun.slot r.2 r.1).isSome) (r : Noun) :
    ∀ s ∈ targetsOf preads r, s ≠ [] ∧ (chainWalk r s).isSome := by
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

/-- **The walk rows' provided handle-record total.**  Over the BFS walk rows of `(cells, preads)`,
`Σ mL•W(recL) + mR•W(recR) = Σ_{r ∈ pathKind preads} W (readRecH cells r)`, for any weight `W`
(in particular `1 / (ρ + RLC_γ)`), given that every deep read is a defined slot. -/
theorem walk_provide_total (W : F × F × (F × F) → M) (cells : List Noun) (preads : List (Noun × ℕ))
    (hslot : ∀ r ∈ pathReads preads, (Noun.slot r.2 r.1).isSome)
    (hdummy : walkRoots preads = [] → chainWalk (cells.headD (.atom 0)) [] = some (cells.headD (.atom 0))) :
    (((walkRows cells preads).map fun t => provH W cells t.label)).sum =
      ((pathKind preads).map fun r => W (readRecH cells r)).sum := by
  have h2 : (((walkRows cells preads).map fun t => provH W cells t.label)).sum =
      (((dfsForest (walkForest cells preads)).map fun t => provH W cells t.label)).sum :=
    ((bfsForest_perm_dfsForest _).map _).sum_eq
  rw [h2, dfsForest_sum]
  unfold walkForest
  split_ifs with hroots
  · have hpk : pathKind preads = [] := by
      by_contra hne
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
      have : x.1 ∈ walkRoots preads := List.mem_dedup.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩)
      rw [hroots] at this; simp at this
    rw [hpk]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have := trie_hSum W cells (cells.headD (.atom 0)) (cells.headD (.atom 0)) [] []
      (hdummy hroots) (by simp)
    simpa using this
  · rw [List.map_map]
    have hper : ∀ r ∈ walkRoots preads,
        (Function.comp (fun c => ((dfsTree c).map fun t => provH W cells t.label).sum)
          (fun r => trie r r [] (targetsOf preads r))) r =
        (((pathKind preads).filter fun x => decide (x.1 = r)).map fun x =>
          W (readRecH cells x)).sum := by
      intro r _
      simp only [Function.comp]
      rw [trie_hSum W cells r r [] _ rfl (targets_ok_of preads hslot r)]
      unfold targetsOf
      rw [List.map_map]
      congr 1
      refine List.map_congr_left fun x hx => ?_
      obtain ⟨hxk, hxr⟩ := List.mem_filter.mp hx
      have hxr : x.1 = r := of_decide_eq_true hxr
      have h2x := two_le_of_path (mem_pathKind.mp hxk).2
      simp only [Function.comp, List.nil_append]
      rw [axisFold_axisBits _ (by omega), ← hxr]
    rw [List.map_congr_left hper]
    exact sum_regroup_fst _ _

end Walk

end

end Nock.NockVMROM.Thm54.VclL.Handle
