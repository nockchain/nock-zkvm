/-
  Nock.WalkForest — forest analogues of the single-walk BFS/completeness lemmas.

  `bfsForest_isForestFullBFT` is the forest analogue of `Walk.bfs_isFullBFT`, and
  `forest_completeness_RVT` the forest analogue of `Walk.walk_completeness_RVT`;
  the latter has no counterpart anywhere else in the tree.
  `Thm54.PlusIOTraceEncoding.bfsForest_isForestFullBFT_exact` is the exact-column
  variant of the former and is proved independently.
-/
import Nock.NockVM

namespace Nock
namespace Walk

open Polynomial

variable {LT : Type*} {K : Type*} [Field K]

section
variable (nodeVal : NTree LT → K)

theorem flatBlks_chldCol (W : List (NTree LT)) (n : ℕ) :
    flatBlks (chldCol nodeVal W) (foCol W) n
      = ((W.take n).flatMap NTree.children).map nodeVal := by
  apply lpoly_inj 2
  · rw [flatBlks_length, List.length_map, Sf_foCol]
  · rw [← queueSum_eq_gen, queueSum_eq]

theorem curVals_curCol_full (W : List (NTree LT)) :
    curVals (curCol nodeVal W) W.length = W.map nodeVal := by
  apply lpoly_inj 1
  · rw [curVals_length, List.length_map]
  · rw [← nodeListP_eq_lpoly_gen, ← nodeListP_eq_lpoly]

theorem curVals_curCol_prefix (l rest : List (NTree LT)) :
    curVals (curCol nodeVal (l ++ rest)) l.length = l.map nodeVal := by
  apply List.ext_getElem (by simp)
  intro j hj hj2
  simp only [curVals, List.getElem_map, List.getElem_range]
  have hjl : j < l.length := by simpa [curVals] using hj
  unfold curCol
  rw [Nat.add_sub_cancel, List.getElem?_append_left hjl,
    List.getElem?_eq_getElem hjl]
  rfl

/-- **The missing forest analogue of `bfs_isFullBFT`.** -/
theorem bfsForest_isForestFullBFT (l : List (NTree LT)) (hne : l ≠ []) :
    IsForestFullBFT (curCol nodeVal (bfsForest l)) (chldCol nodeVal (bfsForest l))
      (foCol (bfsForest l)) l.length (bfsForest l).length := by
  have hsplit : bfsForest l = l ++ (bfsForest l).flatMap NTree.children :=
    bfsForest_eq_append_flatMap l hne
  have hpre : curVals (curCol nodeVal (bfsForest l)) l.length = l.map nodeVal := by
    conv_lhs => rw [hsplit]
    exact curVals_curCol_prefix nodeVal l _
  unfold IsForestFullBFT
  rw [nodeListP_eq_lpoly_gen, forestQueueP_eq_lpoly, curVals_curCol_full,
    flatBlks_chldCol, List.take_length, hpre]
  congr 1
  conv_lhs => rw [hsplit]
  rw [List.map_append]

end

section
variable {S DT : Type*} {n : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}

/-- **`forest_completeness_RVT` — the forest analogue of `walk_completeness_RVT`.** -/
theorem forest_completeness_RVT (nodeVal : NTree (S × DT) → K) (l : List (NTree (S × DT)))
    (hne : l ≠ []) (α : K) (hrvt : ∀ t ∈ l, RVT F t) :
    ∃ ln count acc : ℕ → K,
      WalkSat (curCol nodeVal (bfsForest l)) (chldCol nodeVal (bfsForest l))
        (foCol (bfsForest l)) ln count acc α
        (∑ i ∈ Finset.Icc 1 l.length, curCol nodeVal (bfsForest l) i * α ^ i)
        (α ^ l.length) (bfsForest l).length
      ∧ (∀ t ∈ bfsForest l, Fcon F t)
      ∧ acc (bfsForest l).length = 0 := by
  have hh : 1 ≤ (bfsForest l).length := by
    have := bfsForest_length l
    have := nonempty_totalSize l hne
    omega
  obtain ⟨ln, count, acc, hw⟩ :=
    walkSat_exists (curCol nodeVal (bfsForest l)) (chldCol nodeVal (bfsForest l))
      (foCol (bfsForest l)) α
      (∑ i ∈ Finset.Icc 1 l.length, curCol nodeVal (bfsForest l) i * α ^ i)
      (α ^ l.length) hh
  have hseed : (∑ i ∈ Finset.Icc 1 l.length, curCol nodeVal (bfsForest l) i * α ^ i)
      = (nodeListP (curCol nodeVal (bfsForest l)) l.length).eval α := by
    unfold nodeListP
    rw [eval_finsetSum]
    exact Finset.sum_congr rfl (fun i _ => by simp)
  refine ⟨ln, count, acc, hw, ?_, ?_⟩
  · intro t ht
    obtain ⟨r, hr, hrt⟩ := (mem_bfsForest l t).mp ht
    exact (RVT_iff_walk_Fcon r).mp (hrvt r hr) t
      ((mem_bfsForest [r] t).mpr ⟨r, List.mem_singleton_self r, hrt⟩)
  · rw [forest_out_zero_iff hw hseed rfl]
    exact congrArg (Polynomial.eval α) (bfsForest_isForestFullBFT nodeVal l hne)

end

end Walk
end Nock

#print axioms Nock.Walk.bfsForest_isForestFullBFT
#print axioms Nock.Walk.forest_completeness_RVT
