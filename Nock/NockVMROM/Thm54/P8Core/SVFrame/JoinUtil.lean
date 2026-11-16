/-
  Nock/NockVMROM/Thm54/P8Core/SVFrame/JoinUtil.lean

* `size_mapNTree'`: `mapNTree` preserves `size`.
  * `c2JoinFuelF_factor`: the field C2 join reads the label tree only through `(st, Sof)`, so the
    join at the full exec tree IS the join at its B0 shape (`StrategyOfTracesEv.c2JoinFuel_factor`'s
    field twin, same proof).
  * `c2JoinFuelF_size_le`: the join never has more nodes than the label tree (the Nat twin's proof).
  * `zipLabels`: positional pairing of two trees' labels; `pr_mem_zipLabels`: positionally reached
    nodes (`Batch1171.PR`) pair their labels in it; `zipLabels_length_le`; `pr_map`: `PR` survives a
    label map of the first tree; `inTree_of_pr` / `inTree_of_pr_right`.
-/
import Nock.NockVMROM.Thm54.P8Core.SVFrame.LeafBoundF

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.SVFrame

open Nock Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54.SVJoinF

theorem size_node {α : Type*} (a : α) (cs : List (NTree α)) :
    (NTree.node a cs).size = 1 + (cs.map NTree.size).sum := by
  rw [NTree.size]

/-- `mapNTree` preserves `size`. -/
theorem size_mapNTree' {α β : Type*} (g : α → β) : ∀ t : NTree α, (mapNTree g t).size = t.size := by
  intro t
  induction ht : t.size using Nat.strongRecOn generalizing t with
  | _ n ih =>
    cases t with
    | node a cs =>
      have hcs : ∀ c ∈ cs, (mapNTree g c).size = c.size := by
        intro c hc
        have : c.size < n := by
          rw [← ht, size_node]
          have := List.le_sum_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩ : c.size ∈ cs.map NTree.size)
          omega
        exact ih _ this c rfl
      rw [← ht]
      simp only [mapNTree, size_node, List.map_map]
      congr 2
      exact List.map_congr_left (fun c hc => hcs c hc)

theorem mapNTree_children {α β : Type*} (g : α → β) (t : NTree α) :
    (mapNTree g t).children = t.children.map (mapNTree g) := by
  cases t; simp [mapNTree, NTree.children]

variable {β : Type}

/-- **The field join factors through `(st, Sof)`.** -/
theorem c2JoinFuelF_factor (q : ℕ) (st : β → State) (Sof : β → ℕ) (sv : MState → ℕ → Noun)
    (ax : ℕ → ℕ) :
    ∀ (n : ℕ) (t : NTree β) (subj formula : Noun),
      c2JoinFuelF q st Sof sv ax n t subj formula =
        c2JoinFuelF q Prod.fst Prod.snd sv ax n (mapNTree (fun l => (st l, Sof l)) t) subj formula := by
  intro n
  induction n with
  | zero =>
      intro t subj formula
      cases t with
      | node row ch => simp [c2JoinFuelF, mapNTree]
  | succ n ih =>
      intro t subj formula
      cases t with
      | node row ch =>
          simp only [c2JoinFuelF, c2JoinKidsF, mapNTree]
          generalize hs : st row = s
          cases s <;> rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, ch'⟩⟩⟩⟩ <;>
            (simp only [List.map_cons, List.map_nil, List.map_map, Function.comp_def, ih]
             try rfl)

/-- The field join never has more nodes than the label tree. -/
theorem c2JoinFuelF_size_le (q : ℕ) (st : β → State) (Sof : β → ℕ) (sv : MState → ℕ → Noun)
    (ax : ℕ → ℕ) :
    ∀ (n : ℕ) (t : NTree β) (subj formula : Noun),
      (c2JoinFuelF q st Sof sv ax n t subj formula).size ≤ t.size := by
  intro n
  induction n with
  | zero =>
      intro t subj formula
      cases t with
      | node row ch =>
          simp only [c2JoinFuelF, NTree.size, List.map_nil, List.sum_nil]
          omega
  | succ n ih =>
      intro t subj formula
      cases t with
      | node row ch =>
          have H : ∀ (c : NTree β) (s f : Noun),
              (c2JoinFuelF q st Sof sv ax n c s f).size ≤ c.size := ih
          have hsum : ∀ (kids : List (NTree SemanticStrategy.ComputeRowSkeleton)) (ch : List (NTree β)),
              List.Forall₂ (fun k c => k.size ≤ c.size) kids ch →
              (kids.map NTree.size).sum ≤ (ch.map NTree.size).sum := by
            intro kids ch hf
            induction hf with
            | nil => simp
            | cons h _ ih' => simp only [List.map_cons, List.sum_cons]; omega
          simp only [c2JoinFuelF, c2JoinKidsF]
          generalize hs : st row = s
          cases s <;> rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, ch'⟩⟩⟩⟩ <;>
            (simp only [NTree.size]
             apply Nat.add_le_add_left
             apply hsum
             simp [List.forall₂_cons, List.forall₂_map_left_iff, List.forall₂_same, H])

/-! ## Positional label pairing -/

section Zip

variable {α γ : Type}

mutual
/-- The labels of two trees paired positionally (pre-order, children by index). -/
def zipLabels : NTree α → NTree γ → List (α × γ)
  | .node a cs, .node b ds => (a, b) :: zipLabelsL cs ds
/-- `zipLabels` over two child lists, index by index. -/
def zipLabelsL : List (NTree α) → List (NTree γ) → List (α × γ)
  | c :: cs, d :: ds => zipLabels c d ++ zipLabelsL cs ds
  | _, _ => []
end

theorem label_mem_zipLabels (t : NTree α) (T : NTree γ) : (t.label, T.label) ∈ zipLabels t T := by
  cases t; cases T; simp [zipLabels, NTree.label]

theorem zipLabelsL_sub {cs : List (NTree α)} {ds : List (NTree γ)} {i : ℕ} {c : NTree α}
    {d : NTree γ} (hc : cs[i]? = some c) (hd : ds[i]? = some d) :
    zipLabels c d ⊆ zipLabelsL cs ds := by
  induction cs generalizing ds i with
  | nil => simp at hc
  | cons c0 cs ih =>
      cases ds with
      | nil => simp at hd
      | cons d0 ds =>
          cases i with
          | zero =>
              simp at hc hd
              subst hc; subst hd
              intro p hp; simp [zipLabelsL, hp]
          | succ i =>
              simp at hc hd
              intro p hp
              simp only [zipLabelsL, List.mem_append]
              exact Or.inr (ih hc hd hp)

theorem zipLabels_child_sub {u : NTree α} {w : NTree γ} {i : ℕ} {uc : NTree α} {wc : NTree γ}
    (hu : u.children[i]? = some uc) (hw : w.children[i]? = some wc) :
    zipLabels uc wc ⊆ zipLabels u w := by
  cases u with
  | node a cs =>
    cases w with
    | node b ds =>
      intro p hp
      simp only [zipLabels, List.mem_cons]
      exact Or.inr (zipLabelsL_sub hu hw hp)

theorem zipLabels_sub_of_pr {t u : NTree α} {T w : NTree γ}
    (h : Nock.RedTeam.Batch1171.PR t T u w) : zipLabels u w ⊆ zipLabels t T := by
  induction h with
  | root => exact fun _ hp => hp
  | child i _ hu hw ih => exact List.Subset.trans (zipLabels_child_sub hu hw) ih

/-- **Positionally reached nodes pair their labels.** -/
theorem pr_mem_zipLabels {t u : NTree α} {T w : NTree γ}
    (h : Nock.RedTeam.Batch1171.PR t T u w) : (u.label, w.label) ∈ zipLabels t T :=
  zipLabels_sub_of_pr h (label_mem_zipLabels u w)

mutual
theorem zipLabels_length_le : ∀ (t : NTree α) (T : NTree γ), (zipLabels t T).length ≤ t.size
  | .node a cs, .node b ds => by
      have := zipLabelsL_length_le cs ds
      simp only [zipLabels, List.length_cons, size_node]
      omega
theorem zipLabelsL_length_le : ∀ (cs : List (NTree α)) (ds : List (NTree γ)),
    (zipLabelsL cs ds).length ≤ (cs.map NTree.size).sum
  | c :: cs, d :: ds => by
      have h1 := zipLabels_length_le c d
      have h2 := zipLabelsL_length_le cs ds
      simp only [zipLabelsL, List.length_append, List.map_cons, List.sum_cons]
      omega
  | [], _ => by simp [zipLabelsL]
  | _ :: _, [] => by simp [zipLabelsL]
end

/-- `PR` survives a label map of the first tree. -/
theorem pr_map {δ : Type} (g : α → δ) {t u : NTree α} {T w : NTree γ}
    (h : Nock.RedTeam.Batch1171.PR t T u w) :
    Nock.RedTeam.Batch1171.PR (mapNTree g t) T (mapNTree g u) w := by
  induction h with
  | root => exact .root
  | child i _ hu hw ih =>
      refine .child i ih ?_ hw
      rw [mapNTree_children, List.getElem?_map, hu]; rfl

theorem inTree_child {α : Type} {u uc : NTree α} {i : ℕ} (hu : u.children[i]? = some uc) :
    InTree u uc := by
  cases u with
  | node a cs => exact InTree.sub (List.mem_of_getElem? hu) (InTree.here _)

theorem inTree_of_pr {t u : NTree α} {T w : NTree γ}
    (h : Nock.RedTeam.Batch1171.PR t T u w) : InTree t u := by
  induction h with
  | root => exact InTree.here _
  | child i _ hu _ ih => exact InTree_trans ih (inTree_child hu)

theorem inTree_of_pr_right {t u : NTree α} {T w : NTree γ}
    (h : Nock.RedTeam.Batch1171.PR t T u w) : InTree T w := by
  induction h with
  | root => exact InTree.here _
  | child i _ _ hw ih => exact InTree_trans ih (inTree_child hw)

end Zip

end Nock.NockVMROM.Thm54.SVFrame
