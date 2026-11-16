/-
  Nock/NockVMROM/Thm54/ReconTreeSize.lean

  `Walk.reconTree fo lbl h` is the
  tree the round-0 built strategies read off `h` committed compute rows
  (`StrategyOfTracesR0AC2.c2TreeOfTraces`).  The bound holds unconditionally because
  `Walk.childIdxs` tiles the child ranges contiguously (`Walk.firstC_succ`): a child index
  determines its parent, so the indices of the reconstructed nodes are pairwise distinct and all
  lie in `[1, h]`.
-/
import Nock.NockVMROM.Thm54.ExactTraversal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.ReconTreeSize

open Nock.Walk

/-! ## §A  Relabelling keeps the size; relabelling commutes with reconstruction -/

theorem size_eq_bfs_length {α : Type*} (t : NTree α) : t.size = (bfsForest [t]).length := by
  rw [bfsForest_length]
  simp [totalSize]

theorem size_mapNTree {α β : Type*} (f : α → β) (t : NTree α) :
    (mapNTree f t).size = t.size := by
  rw [size_eq_bfs_length, size_eq_bfs_length t,
    show [mapNTree f t] = [t].map (mapNTree f) from rfl, bfsForest_mapNTree, List.length_map]

/-- Relabelling composes (owned here: `ForestExponentWindow.mapNTree_comp` sits above the pin). -/
theorem mapNTree_comp {α β γ : Type*} (f : α → β) (g : β → γ) :
    ∀ t : NTree α, mapNTree g (mapNTree f t) = mapNTree (fun a => g (f a)) t := by
  intro t
  let P := fun t : NTree α => mapNTree g (mapNTree f t) = mapNTree (fun a => g (f a)) t
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro l ch ih
    simp only [P, mapNTree, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact ih c hc
  · intro c hc
    simp at hc
  · intro head tail ihHead ihTail c hc
    simp only [List.mem_cons] at hc
    exact hc.elim (fun h => h ▸ ihHead) (ihTail c)

theorem mapNTree_buildTF {α β : Type*} (f : α → β)
    (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → α) (h i : ℕ) :
    mapNTree f (buildTF kroots fo lbl h i) =
      buildTF kroots fo (fun j => f (lbl j)) h i := by
  suffices ∀ d i, h - i = d →
      mapNTree f (buildTF kroots fo lbl h i) =
        buildTF kroots fo (fun j => f (lbl j)) h i from this (h - i) i rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro i hi
    rw [buildTF, mapNTree, buildTF]
    refine congrArg (NTree.node (f (lbl i))) ?_
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    have hmem : j.1 ∈ childIdxsF kroots fo h i := j.property
    have hlt : h - j.1 < d := by
      simp only [childIdxsF, List.mem_filter, decide_eq_true_eq, List.mem_range'] at hmem
      omega
    exact ih (h - j.1) hlt j.1 rfl

theorem mapNTree_reconForest {α β : Type*} (f : α → β)
    (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → α) (h : ℕ) :
    (reconForest kroots fo lbl h).map (mapNTree f) =
      reconForest kroots fo (fun j => f (lbl j)) h := by
  simp only [reconForest, List.map_map]
  apply List.map_congr_left
  intro _ _
  exact mapNTree_buildTF f kroots fo lbl h _

theorem mapNTree_buildT {α β : Type*} (f : α → β) (fo : ℕ → ℕ) (lbl : ℕ → α) (h : ℕ) :
    ∀ i, mapNTree f (buildT fo lbl h i) = buildT fo (fun j => f (lbl j)) h i := by
  intro i
  suffices ∀ d i, h - i = d →
      mapNTree f (buildT fo lbl h i) = buildT fo (fun j => f (lbl j)) h i from this (h - i) i rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i hi
    rw [buildT, mapNTree, buildT]
    refine congrArg (NTree.node (f (lbl i))) ?_
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    have hmem : j.1 ∈ childIdxs fo h i := j.property
    have hlt : h - j.1 < d := by
      simp only [childIdxs, List.mem_filter, decide_eq_true_eq] at hmem
      omega
    exact ih (h - j.1) hlt j.1 rfl

theorem mapNTree_reconTree {α β : Type*} (f : α → β) (fo : ℕ → ℕ) (lbl : ℕ → α) (h : ℕ) :
    mapNTree f (reconTree fo lbl h) = reconTree fo (fun j => f (lbl j)) h :=
  mapNTree_buildT f fo lbl h 1

/-! ## §B  The preorder index list and the tiling of child ranges -/

/-- The preorder label list of a tree; its length is the tree's size. -/
def pre {α : Type*} : NTree α → List α
  | .node l ch => l :: (ch.map pre).flatten

theorem pre_length {α : Type*} : ∀ t : NTree α, (pre t).length = t.size := by
  intro t
  let P := fun t : NTree α => (pre t).length = t.size
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro l ch ih
    simp only [P, pre, NTree.size, List.length_cons, List.length_flatten, List.map_map]
    rw [Nat.add_comm]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro c hc
    exact ih c hc
  · intro c hc
    simp at hc
  · intro head tail ihHead ihTail c hc
    simp only [List.mem_cons] at hc
    exact hc.elim (fun h => h ▸ ihHead) (ihTail c)

theorem mem_childIdxs {fo : ℕ → ℕ} {h i j : ℕ} (hj : j ∈ childIdxs fo h i) :
    i < j ∧ j ≤ h ∧ firstC fo i ≤ j ∧ j < firstC fo i + fo i := by
  simp only [childIdxs, List.mem_filter, List.mem_range', decide_eq_true_eq] at hj
  obtain ⟨⟨k, hk, rfl⟩, h1, h2⟩ := hj
  omega

theorem firstC_mono (fo : ℕ → ℕ) {a b : ℕ} (hab : a ≤ b) : firstC fo a ≤ firstC fo b := by
  unfold firstC
  have := Sf_mono fo (show a - 1 ≤ b - 1 by omega)
  omega

/-- **A child index determines its parent**: the child ranges of distinct parents are disjoint
(`Walk.firstC_succ`, the contiguous tiling). -/
theorem childIdxs_parent_unique {fo : ℕ → ℕ} {h p p' j : ℕ} (hp : 1 ≤ p) (hp' : 1 ≤ p')
    (h1 : j ∈ childIdxs fo h p) (h2 : j ∈ childIdxs fo h p') : p = p' := by
  obtain ⟨_, _, hlo, hhi⟩ := mem_childIdxs h1
  obtain ⟨_, _, hlo', hhi'⟩ := mem_childIdxs h2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hs := firstC_succ fo hp
    have hm := firstC_mono fo (show p + 1 ≤ p' by omega)
    omega
  · have hs := firstC_succ fo hp'
    have hm := firstC_mono fo (show p' + 1 ≤ p by omega)
    omega

/-- The children of a reconstructed node, as a plain `map` over its child indices. -/
theorem buildT_eq_node (fo : ℕ → ℕ) {α : Type*} (lbl : ℕ → α) (h i : ℕ) :
    buildT fo lbl h i = .node (lbl i) ((childIdxs fo h i).map (buildT fo lbl h)) := by
  have hl := buildT_label fo lbl h i
  have hc := buildT_children fo lbl h i
  cases hb : buildT fo lbl h i with
  | node l ch =>
    rw [hb] at hl hc
    simp only [NTree.label_node, NTree.children_node] at hl hc
    rw [hl, hc]

theorem self_mem_pre_buildT (fo : ℕ → ℕ) (h i : ℕ) : i ∈ pre (buildT fo id h i) := by
  rw [buildT_eq_node]
  simp [pre]

/-- Every reconstructed index below `i` descends from `i` through a child range. -/
theorem pre_buildT_parent (fo : ℕ → ℕ) (h : ℕ) :
    ∀ i x, x ∈ pre (buildT fo id h i) → x ≠ i →
      ∃ p ∈ pre (buildT fo id h i), x ∈ childIdxs fo h p := by
  intro i
  suffices ∀ d i, h - i = d → ∀ x, x ∈ pre (buildT fo id h i) → x ≠ i →
      ∃ p ∈ pre (buildT fo id h i), x ∈ childIdxs fo h p from this (h - i) i rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i hi x hx hne
    rw [buildT_eq_node] at hx ⊢
    simp only [pre, id, List.mem_cons, List.mem_flatten, List.mem_map] at hx
    rcases hx with hx | ⟨l, ⟨t, ⟨j, hj, rfl⟩, rfl⟩, hxl⟩
    · exact absurd hx hne
    · obtain ⟨hij, hjh, -, -⟩ := mem_childIdxs hj
      by_cases hxj : x = j
      · subst hxj
        exact ⟨i, by simp [pre], hj⟩
      · obtain ⟨p, hp, hxp⟩ := ih (h - j) (by omega) j rfl x hxl hxj
        refine ⟨p, ?_, hxp⟩
        simp only [pre, id, List.mem_cons, List.mem_flatten, List.mem_map]
        exact Or.inr ⟨pre (buildT fo id h j), ⟨buildT fo id h j, ⟨j, hj, rfl⟩, rfl⟩, hp⟩

theorem pre_buildT_ge (fo : ℕ → ℕ) (h : ℕ) :
    ∀ i x, x ∈ pre (buildT fo id h i) → i ≤ x := by
  intro i
  suffices ∀ d i, h - i = d → ∀ x, x ∈ pre (buildT fo id h i) → i ≤ x from this (h - i) i rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i hi x hx
    rw [buildT_eq_node] at hx
    simp only [pre, id, List.mem_cons, List.mem_flatten, List.mem_map] at hx
    rcases hx with rfl | ⟨l, ⟨t, ⟨j, hj, rfl⟩, rfl⟩, hxl⟩
    · exact le_rfl
    · obtain ⟨hij, hjh, -, -⟩ := mem_childIdxs hj
      have := ih (h - j) (by omega) j rfl x hxl
      omega

theorem pre_buildT_le (fo : ℕ → ℕ) (h : ℕ) :
    ∀ i x, i ≤ h → x ∈ pre (buildT fo id h i) → x ≤ h := by
  intro i x hih hx
  by_cases hxi : x = i
  · omega
  · obtain ⟨p, -, hxp⟩ := pre_buildT_parent fo h i x hx hxi
    exact (mem_childIdxs hxp).2.1

/-- **Incomparable subtrees are disjoint** (the pattern of `DecodedLambdaEvent.reach_disjoint`). -/
theorem pre_buildT_disjoint (fo : ℕ → ℕ) (h : ℕ) (j₁ j₂ : ℕ) (hj₁ : 1 ≤ j₁) (hj₂ : 1 ≤ j₂)
    (h12 : j₁ ∉ pre (buildT fo id h j₂)) (h21 : j₂ ∉ pre (buildT fo id h j₁)) :
    ∀ x, x ∈ pre (buildT fo id h j₁) → x ∈ pre (buildT fo id h j₂) → False := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx1 hx2
    have hne1 : x ≠ j₁ := fun hx => h12 (hx ▸ hx2)
    have hne2 : x ≠ j₂ := fun hx => h21 (hx ▸ hx1)
    obtain ⟨p₁, hp₁, hxp₁⟩ := pre_buildT_parent fo h j₁ x hx1 hne1
    obtain ⟨p₂, hp₂, hxp₂⟩ := pre_buildT_parent fo h j₂ x hx2 hne2
    have hp₁ge := pre_buildT_ge fo h j₁ p₁ hp₁
    have hp₂ge := pre_buildT_ge fo h j₂ p₂ hp₂
    have heq := childIdxs_parent_unique (fo := fo) (h := h) (by omega) (by omega) hxp₁ hxp₂
    subst heq
    have hlt : p₁ < x := (mem_childIdxs hxp₁).1
    exact ih p₁ hlt hp₁ hp₂

/-- Two distinct children of one node root disjoint subtrees. -/
theorem pre_buildT_siblings_disjoint (fo : ℕ → ℕ) (h i : ℕ) (hi : 1 ≤ i) {j₁ j₂ : ℕ}
    (hj₁ : j₁ ∈ childIdxs fo h i) (hj₂ : j₂ ∈ childIdxs fo h i) (hne : j₁ ≠ j₂) :
    List.Disjoint (pre (buildT fo id h j₁)) (pre (buildT fo id h j₂)) := by
  have hnot : ∀ a b, a ∈ childIdxs fo h i → b ∈ childIdxs fo h i → a ≠ b →
      b ∉ pre (buildT fo id h a) := by
    intro a b ha hb hab hmem
    obtain ⟨p, hp, hbp⟩ := pre_buildT_parent fo h a b hmem (Ne.symm hab)
    have hpa := pre_buildT_ge fo h a p hp
    have hia := (mem_childIdxs ha).1
    have := childIdxs_parent_unique (fo := fo) (h := h) hi (by omega) hb hbp
    omega
  intro x hx1 hx2
  exact pre_buildT_disjoint fo h j₁ j₂ (by have := (mem_childIdxs hj₁).1; omega)
    (by have := (mem_childIdxs hj₂).1; omega)
    (hnot j₂ j₁ hj₂ hj₁ (Ne.symm hne)) (hnot j₁ j₂ hj₁ hj₂ hne) x hx1 hx2

theorem childIdxs_nodup (fo : ℕ → ℕ) (h i : ℕ) : (childIdxs fo h i).Nodup :=
  List.Nodup.filter _ (List.nodup_range' 1)

/-- **The reconstructed indices are pairwise distinct.** -/
theorem pre_buildT_nodup (fo : ℕ → ℕ) (h : ℕ) :
    ∀ i, 1 ≤ i → (pre (buildT fo id h i)).Nodup := by
  intro i
  suffices ∀ d i, h - i = d → 1 ≤ i → (pre (buildT fo id h i)).Nodup from this (h - i) i rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i hi hi1
    rw [buildT_eq_node]
    simp only [pre, id, List.map_map]
    refine List.nodup_cons.2 ⟨?_, ?_⟩
    · intro hmem
      simp only [List.mem_flatten, List.mem_map, Function.comp] at hmem
      obtain ⟨l, ⟨j, hj, rfl⟩, hil⟩ := hmem
      have hij := (mem_childIdxs hj).1
      have := pre_buildT_ge fo h j i hil
      omega
    · rw [List.nodup_flatten]
      refine ⟨?_, ?_⟩
      · intro l hl
        simp only [List.mem_map, Function.comp] at hl
        obtain ⟨j, hj, rfl⟩ := hl
        obtain ⟨hij, hjh, -, -⟩ := mem_childIdxs hj
        exact ih (h - j) (by omega) j rfl (by omega)
      · rw [List.pairwise_map]
        refine List.Pairwise.imp_of_mem ?_ (childIdxs_nodup fo h i)
        intro a b ha hb hab
        exact pre_buildT_siblings_disjoint fo h i hi1 ha hb hab

/-- **THE BOUND: the reconstruction of `h ≥ 1` committed rows has at most `h` nodes**, at every
fanout map and every labelling (no `BFSValid`, no `Sf` equation). -/
theorem reconTree_size_le {α : Type*} (fo : ℕ → ℕ) (lbl : ℕ → α) (h : ℕ) (hh : 1 ≤ h) :
    (reconTree fo lbl h).size ≤ h := by
  have hmap : reconTree fo lbl h = mapNTree lbl (reconTree fo id h) := by
    rw [mapNTree_reconTree]; rfl
  rw [hmap, size_mapNTree, ← pre_length]
  have hnodup := pre_buildT_nodup fo h 1 le_rfl
  have hsub : pre (buildT fo id h 1) ⊆ List.range' 1 h := by
    intro x hx
    rw [List.mem_range']
    have h1 := pre_buildT_ge fo h 1 x hx
    have h2 := pre_buildT_le fo h 1 x hh hx
    exact ⟨x - 1, by omega, by omega⟩
  have := (List.subperm_of_subset hnodup hsub).length_le
  rw [List.length_range'] at this
  exact this

end Nock.NockVMROM.Thm54.ReconTreeSize
