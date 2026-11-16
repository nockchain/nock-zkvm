/-
  Nock/NockVMROM/Thm54/VclL/Walk/GenWalkCount.lean

  `trie_size_le`: a read trie has at most `Σ_{distinct targets} |target|` nodes (every node is a
  proper prefix of some distinct target; at a node, the side-`b` subtries are paid by the
  targets through `b`, and the node itself by the first edge of one target).
  `walkRows_length_le`: `|walkRows| ≤ Σ_{distinct path reads} depth` (+ 1 for the dummy row
  when there is no path read) — the walk table is at most as long as the path table's
  edge count (`pathTable` has one row per edge of each distinct deep read when the reads are
  defined), so the path table's orbit height also fits the walk.
-/
import Nock.NockVMROM.Thm54.VclL.Walk.GenWalkRows

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.GenWalk

open Nock Nock.Walk Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.TraceGen

/-- The total length of the DISTINCT targets. -/
def costT (T : List (List Bool)) : ℕ := ∑ s ∈ T.toFinset, s.length

theorem mem_sideTails_iff {b : Bool} {T : List (List Bool)} {s : List Bool} :
    s ∈ sideTails b T ↔ b :: s ∈ T := by
  refine ⟨mem_sideTails, fun h => ?_⟩
  unfold sideTails
  exact List.mem_filterMap.mpr ⟨b :: s, h, by simp⟩

/-- Removing the empty suffix does not change the cost. -/
theorem costT_contT (b : Bool) (T : List (List Bool)) : costT (contT b T) = costT (sideTails b T) := by
  unfold costT contT
  rw [List.toFinset_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  cases s <;> simp

/-- **Head split** of a target set with no empty target. -/
theorem toFinset_split (T : List (List Bool)) (hT : ∀ s ∈ T, s ≠ []) :
    T.toFinset = ((sideTails false T).toFinset.image (List.cons false)) ∪
      ((sideTails true T).toFinset.image (List.cons true)) := by
  ext s
  simp only [List.mem_toFinset, Finset.mem_union, Finset.mem_image, mem_sideTails_iff]
  constructor
  · intro hs
    match s, hT s hs with
    | c :: s', _ =>
      cases c
      · exact Or.inl ⟨s', hs, rfl⟩
      · exact Or.inr ⟨s', hs, rfl⟩
  · rintro (⟨s', h, rfl⟩ | ⟨s', h, rfl⟩) <;> exact h

theorem costT_split (T : List (List Bool)) (hT : ∀ s ∈ T, s ≠ []) :
    costT T = ((sideTails false T).toFinset.card + costT (sideTails false T)) +
      ((sideTails true T).toFinset.card + costT (sideTails true T)) := by
  unfold costT
  rw [toFinset_split T hT, Finset.sum_union, Finset.sum_image (fun _ _ _ _ h => List.cons_injective h),
    Finset.sum_image (fun _ _ _ _ h => List.cons_injective h)]
  · simp only [List.length_cons, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    ring
  · rw [Finset.disjoint_left]
    simp only [Finset.mem_image]
    rintro _ ⟨a, _, rfl⟩ ⟨b, _, hb⟩
    simp at hb

theorem costT_pos (T : List (List Bool)) (hT : ∀ s ∈ T, s ≠ []) (hne : T ≠ []) : 1 ≤ costT T := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil T hne
  unfold costT
  have h1 : 1 ≤ s.length := List.length_pos_of_ne_nil (hT s hs)
  exact h1.trans (Finset.single_le_sum (f := List.length) (fun _ _ => Nat.zero_le _)
    (List.mem_toFinset.mpr hs))

theorem contT_ne (b : Bool) (T : List (List Bool)) : ∀ s ∈ contT b T, s ≠ [] :=
  fun _ h => (mem_contT h).2

theorem contT_ne_nil {b : Bool} {T : List (List Bool)} (h : cont b T = true) : contT b T ≠ [] := by
  unfold cont at h
  intro h'; rw [h'] at h; simp at h

theorem costT_contT_le_card (b : Bool) (T : List (List Bool)) (h : cont b T = true) :
    1 ≤ (sideTails b T).toFinset.card := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ (contT_ne_nil h)
  have := (List.mem_filter.mp hs).1
  exact Finset.card_pos.mpr ⟨s, List.mem_toFinset.mpr this⟩

theorem sideTails_ne_of_ne (T : List (List Bool)) (hT : ∀ s ∈ T, s ≠ []) (hne : T ≠ []) :
    1 ≤ (sideTails false T).toFinset.card + (sideTails true T).toFinset.card := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil T hne
  match s, hT s hs, hs with
  | c :: s', _, hs =>
    have hm : s' ∈ sideTails c T := mem_sideTails_iff.mpr hs
    have : 1 ≤ (sideTails c T).toFinset.card := Finset.card_pos.mpr ⟨s', List.mem_toFinset.mpr hm⟩
    cases c
    · exact this.trans (Nat.le_add_right _ _)
    · exact this.trans (Nat.le_add_left _ _)

theorem size_node' {LT : Type} (x : LT) (c : List (NTree LT)) :
    (NTree.node x c).size = 1 + (c.map NTree.size).sum := by
  simp [NTree.size]

/-- **A read trie has at most `costT T` nodes.** -/
theorem trie_size_le (root : Noun) :
    ∀ (n : Noun) (bs : List Bool) (T : List (List Bool)), (∀ s ∈ T, s ≠ []) → T ≠ [] →
      (trie root n bs T).size ≤ costT T := by
  intro n
  induction n with
  | atom a =>
    intro bs T hT hne
    rw [show trie root (.atom a) bs T = NTree.node _ [] from rfl, size_node']
    simpa using costT_pos T hT hne
  | cell l r ihl ihr =>
    intro bs T hT hne
    have hsplit := costT_split T hT
    have hcard := sideTails_ne_of_ne T hT hne
    rw [show trie root (.cell l r) bs T = NTree.node _
        ((if cont false T then [trie root l (bs ++ [false]) (contT false T)] else []) ++
          (if cont true T then [trie root r (bs ++ [true]) (contT true T)] else [])) from rfl, size_node']
    have hL : (if cont false T = true then (trie root l (bs ++ [false]) (contT false T)).size else 0) ≤
        (if cont false T = true then costT (sideTails false T) else 0) := by
      split_ifs with h
      · rw [← costT_contT]; exact ihl _ _ (contT_ne _ _) (contT_ne_nil h)
      · exact le_rfl
    have hR : (if cont true T = true then (trie root r (bs ++ [true]) (contT true T)).size else 0) ≤
        (if cont true T = true then costT (sideTails true T) else 0) := by
      split_ifs with h
      · rw [← costT_contT]; exact ihr _ _ (contT_ne _ _) (contT_ne_nil h)
      · exact le_rfl
    have e : (((if cont false T then [trie root l (bs ++ [false]) (contT false T)] else []) ++
        (if cont true T then [trie root r (bs ++ [true]) (contT true T)] else [])).map NTree.size).sum =
        (if cont false T = true then (trie root l (bs ++ [false]) (contT false T)).size else 0) +
        (if cont true T = true then (trie root r (bs ++ [true]) (contT true T)).size else 0) := by
      split_ifs <;> simp
    rw [e, hsplit]
    have c1 : (if cont false T = true then costT (sideTails false T) else 0) ≤ costT (sideTails false T) := by
      split_ifs <;> omega
    have c2 : (if cont true T = true then costT (sideTails true T) else 0) ≤ costT (sideTails true T) := by
      split_ifs <;> omega
    omega

/-! ## The forest -/

theorem axisBits_ne_of_path {a : ℕ} (h : isPathAx a = true) : axisBits a ≠ [] := by
  unfold isPathAx at h
  have := of_decide_eq_true h
  intro h'; rw [depthOf, h'] at this; simp at this

theorem two_le_of_path {a : ℕ} (h : isPathAx a = true) : 2 ≤ a := by
  by_contra hc
  exact axisBits_ne_of_path h (axisBits_of_lt_two (by omega))

theorem mem_pathKind {preads : List (Noun × ℕ)} {x : Noun × ℕ} :
    x ∈ pathKind preads ↔ x ∈ preads ∧ isPathAx x.2 = true := by
  unfold pathKind; simp

theorem targetsOf_ne (preads : List (Noun × ℕ)) (r : Noun) : ∀ s ∈ targetsOf preads r, s ≠ [] := by
  intro s hs
  unfold targetsOf at hs
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
  exact axisBits_ne_of_path (mem_pathKind.mp (List.mem_filter.mp hx).1).2

theorem targetsOf_ne_nil {preads : List (Noun × ℕ)} {r : Noun} (hr : r ∈ walkRoots preads) :
    targetsOf preads r ≠ [] := by
  unfold walkRoots at hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hr)
  unfold targetsOf
  intro h
  have : axisBits x.2 ∈ ((pathKind preads).filter fun y => decide (y.1 = x.1)).map fun y => axisBits y.2 :=
    List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hx, by simp⟩, rfl⟩
  rw [h] at this; simp at this

/-- `costT` of a root's targets is the depth sum over its distinct path reads. -/
theorem costT_targetsOf (preads : List (Noun × ℕ)) (r : Noun) :
    costT (targetsOf preads r) =
      ∑ x ∈ (pathKind preads).toFinset with x.1 = r, depthOf x.2 := by
  unfold costT targetsOf
  have hm : ((List.filter (fun x => decide (x.1 = r)) (pathKind preads)).map fun x => axisBits x.2).toFinset
      = ((pathKind preads).toFinset.filter fun x => x.1 = r).image fun x => axisBits x.2 := by
    ext s; simp
  rw [hm, Finset.sum_image]
  intro x hx y hy hxy
  simp only [Finset.coe_filter, Set.mem_setOf_eq, List.mem_toFinset] at hx hy
  have ax := axisFold_axisBits x.2 (by have := two_le_of_path (mem_pathKind.mp hx.1).2; omega)
  have ay := axisFold_axisBits y.2 (by have := two_le_of_path (mem_pathKind.mp hy.1).2; omega)
  have h2 : x.2 = y.2 := by rw [← ax, ← ay]; exact congrArg axisFold hxy
  exact Prod.ext (hx.2.trans hy.2.symm) h2

theorem walkRows_length_le (cells : List Noun) (preads : List (Noun × ℕ)) :
    (walkRows cells preads).length ≤
      ((pathReads preads).map fun r => depthOf r.2).sum + (if pathReads preads = [] then 1 else 0) := by
  unfold walkRows
  rw [bfsForest_length]
  unfold walkForest totalSize
  have hpr : pathReads preads = (pathKind preads).dedup := rfl
  split_ifs with h1 h2 h2
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have : (trie (cells.headD (.atom 0)) (cells.headD (.atom 0)) [] []).size = 1 := by
      cases hc : cells.headD (.atom 0) with
      | atom a => simp [trie, size_node']
      | cell l r => simp [trie, cont, contT, sideTails, size_node']
    omega
  · exfalso
    apply h2
    rw [hpr]
    unfold walkRoots at h1
    rw [List.dedup_eq_nil, List.map_eq_nil_iff] at h1
    rw [h1]; rfl
  · exfalso
    apply h1
    rw [hpr, List.dedup_eq_nil] at h2
    unfold walkRoots
    rw [h2]; rfl
  · rw [add_zero, List.map_map]
    have hnd : (walkRoots preads).Nodup := List.nodup_dedup _
    rw [← List.sum_toFinset _ hnd]
    have hnd2 : (pathReads preads).Nodup := List.nodup_dedup _
    rw [← List.sum_toFinset (fun r : Noun × ℕ => depthOf r.2) hnd2]
    have hts : (pathReads preads).toFinset = (pathKind preads).toFinset := by
      rw [hpr]; ext x; simp
    rw [hts, ← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := (walkRoots preads).toFinset)]
    · refine Finset.sum_le_sum fun r hr => ?_
      rw [Function.comp_apply, ← costT_targetsOf]
      exact trie_size_le r r [] _ (targetsOf_ne preads r) (targetsOf_ne_nil (List.mem_toFinset.mp hr))
    · intro x hx
      unfold walkRoots
      simp only [List.mem_toFinset, List.mem_dedup, List.mem_map] at hx ⊢
      exact ⟨x, hx, rfl⟩

end Nock.NockVMROM.Thm54.VclL.GenWalk
