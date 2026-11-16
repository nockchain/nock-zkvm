/-
  Nock/RedTeam/Batch186Thm54BfsDfsPermutation.lean

  **The two absent `bfsForest` permutation lemmas.**

  Two were genuinely absent and are now in `Nock/Walk.lean`:
  `bfsForest_append_perm` and `bfsForest_perm_dfsForest`.  The generator needs them because
  request exponents are distinct in **BFS row order** (`genSemanticRequests_exponent_nodup`)
  while `genMemForestFromTree` builds the memory forest in **DFS pre-order**.

  This artifact pins that neither lemma is vacuous.  A permutation statement says nothing if the
  two sides are equal, so both directions are exhibited on concrete trees:

  * `b186_bfs_ne_dfs` — BFS and DFS of the same tree are DIFFERENT lists, and
    `b186_bfs_perm_dfs` — they are nonetheless permutations.
  * `b186_append_ne` — `bfsForest` does NOT commute with `++` on the nose, and
    `b186_append_perm` — it does up to permutation.

  `b186_dfs_append_is_equality` records the asymmetry: DFS pre-order *does* split over `++`
  definitionally, which is why the permutation lives on the BFS side.

  -- uniqueness, the property that has to cross between the two orders)
-/
import Nock.Walk

namespace Nock.RedTeam.Batch186

open Nock Nock.Walk

/-! ### A. The witness tree: BFS and DFS genuinely disagree -/

def w3 : NTree ℕ := .node 3 []
def w2 : NTree ℕ := .node 2 []
def w1 : NTree ℕ := .node 1 [w3]
def w0 : NTree ℕ := .node 0 [w1, w2]

theorem b186_bfsForest_w0 : bfsForest [w0] = [w0, w1, w2, w3] := by
  have h3 : bfsForest [w3] = [w3] := by
    rw [bfsForest_cons_eq _ (List.cons_ne_nil _ _)]
    show [w3] ++ bfsForest ([] : List (NTree ℕ)) = [w3]
    rw [bfsForest_nil, List.append_nil]
  have h2 : bfsForest [w1, w2] = [w1, w2, w3] := by
    rw [bfsForest_cons_eq _ (List.cons_ne_nil _ _)]
    show [w1, w2] ++ bfsForest [w3] = [w1, w2, w3]
    rw [h3]; rfl
  rw [bfsForest_cons_eq _ (List.cons_ne_nil _ _)]
  show [w0] ++ bfsForest [w1, w2] = [w0, w1, w2, w3]
  rw [h2]; rfl

theorem b186_dfsTree_w0 : dfsTree w0 = [w0, w1, w3, w2] := rfl

/-- **Not vacuous.**  The two enumerations are different lists. -/
theorem b186_bfs_ne_dfs : bfsForest [w0] ≠ dfsTree w0 := by
  rw [b186_bfsForest_w0, b186_dfsTree_w0]
  intro h
  have := congrArg (fun l => l.map NTree.label) h
  simp [w0, w1, w2, w3] at this

/-- … and they are nonetheless permutations. -/
theorem b186_bfs_perm_dfs : (bfsForest [w0]).Perm (dfsTree w0) :=
  bfsForest_perm_dfsForest [w0]

/-! ### B. `bfsForest` over `++` is a permutation and not an equality -/

def v1 : NTree ℕ := .node 1 []
def v0 : NTree ℕ := .node 0 [v1]
def u2 : NTree ℕ := .node 2 []

theorem b186_bfsForest_append : bfsForest [v0, u2] = [v0, u2, v1] := by
  have h1 : bfsForest [v1] = [v1] := by
    rw [bfsForest_cons_eq _ (List.cons_ne_nil _ _)]
    show [v1] ++ bfsForest ([] : List (NTree ℕ)) = [v1]
    rw [bfsForest_nil, List.append_nil]
  rw [bfsForest_cons_eq _ (List.cons_ne_nil _ _)]
  show [v0, u2] ++ bfsForest [v1] = [v0, u2, v1]
  rw [h1]; rfl

theorem b186_bfsForest_v0 : bfsForest [v0] = [v0, v1] := by
  have h1 : bfsForest [v1] = [v1] := by
    rw [bfsForest_cons_eq _ (List.cons_ne_nil _ _)]
    show [v1] ++ bfsForest ([] : List (NTree ℕ)) = [v1]
    rw [bfsForest_nil, List.append_nil]
  rw [bfsForest_cons_eq _ (List.cons_ne_nil _ _)]
  show [v0] ++ bfsForest [v1] = [v0, v1]
  rw [h1]; rfl

theorem b186_bfsForest_u2 : bfsForest [u2] = [u2] := by
  rw [bfsForest_cons_eq _ (List.cons_ne_nil _ _)]
  show [u2] ++ bfsForest ([] : List (NTree ℕ)) = [u2]
  rw [bfsForest_nil, List.append_nil]

/-- **Not vacuous.**  `bfsForest` does not commute with `++` on the nose. -/
theorem b186_append_ne :
    bfsForest ([v0] ++ [u2]) ≠ bfsForest [v0] ++ bfsForest [u2] := by
  rw [show ([v0] ++ [u2]) = [v0, u2] from rfl, b186_bfsForest_append,
    b186_bfsForest_v0, b186_bfsForest_u2]
  intro h
  have := congrArg (fun l => l.map NTree.label) h
  simp [v0, v1, u2] at this

/-- … and it does commute up to permutation. -/
theorem b186_append_perm :
    (bfsForest ([v0] ++ [u2])).Perm (bfsForest [v0] ++ bfsForest [u2]) :=
  bfsForest_append_perm [v0] [u2]

/-! ### C. DFS pre-order, unlike BFS, splits over `++` on the nose -/

theorem b186_dfs_append_is_equality (l₁ l₂ : List (NTree ℕ)) :
    dfsForest (l₁ ++ l₂) = dfsForest l₁ ++ dfsForest l₂ :=
  dfsForest_append l₁ l₂

/-! ### D. The transported corollaries -/

theorem b186_dfs_length (l : List (NTree ℕ)) : (dfsForest l).length = totalSize l :=
  dfsForest_length l

theorem b186_mem_dfs (cs : List (NTree ℕ)) (t : NTree ℕ) :
    t ∈ dfsForest cs ↔ ∃ c ∈ cs, InTree c t :=
  mem_dfsForest cs t

#print axioms Nock.Walk.bfsForest_append_perm
#print axioms Nock.Walk.bfsForest_perm_dfsForest
#print axioms Nock.Walk.dfsForest_append
#print axioms Nock.RedTeam.Batch186.b186_bfs_ne_dfs
#print axioms Nock.RedTeam.Batch186.b186_append_ne

end Nock.RedTeam.Batch186
