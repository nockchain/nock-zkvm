/-
  Nock/NockVMROM/Thm54/P8Core/Batch772Thm54RequestIndex.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch772Thm54RequestIndex`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch772Thm54RequestIndex.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch530Thm54ComputeTreeBindsDeployed

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch772

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.PreSeedCensus
variable {K : Type} [Field K] [DecidableEq K]

theorem filterMap_finRange_three {β : Type} (c : ℕ) (hc : c ≤ 3)
    (F : ∀ i : Fin 3, (i : ℕ) < c → β) :
    ((List.finRange 3).filterMap
        (fun i : Fin 3 => if h : (i : ℕ) < c then some (F i h) else none)).length = c ∧
      ∀ j (hj : j < c),
        ((List.finRange 3).filterMap
          (fun i : Fin 3 => if h : (i : ℕ) < c then some (F i h) else none))[j]? =
            some (F ⟨j, by omega⟩ hj) := by
  interval_cases c
  · simp
  · refine ⟨by simp [List.finRange_succ], ?_⟩
    intro j hj
    have : j = 0 := by omega
    subst this
    simp [List.finRange_succ]
  · refine ⟨by simp [List.finRange_succ], ?_⟩
    intro j hj
    interval_cases j <;> simp [List.finRange_succ]
  · refine ⟨by simp [List.finRange_succ], ?_⟩
    intro j hj
    interval_cases j <;> simp [List.finRange_succ]

/-- The records one skeleton row requests, in slot order (`requestList`'s inner list). -/
def recs (r : ComputeRowSkeleton) : List MemRecSkeleton :=
  (List.finRange 3).filterMap fun (i : Fin 3) =>
    if h : (i : ℕ) < Nock.Framework.recordCount r.state then some (r.memoryRecord i h) else none

theorem requestList_eq (S : SemanticSkeleton) :
    requestList S = (computeSkeletonRows S).flatMap recs := rfl

theorem recs_length (r : ComputeRowSkeleton) : (recs r).length = Nock.Framework.recordCount r.state :=
  (filterMap_finRange_three _ (Nock.Framework.recordCount_le r.state) r.memoryRecord).1

theorem recs_getElem? (r : ComputeRowSkeleton) (j : ℕ) (hj : j < Nock.Framework.recordCount r.state) :
    (recs r)[j]? = some (r.memoryRecord ⟨j, lt_of_lt_of_le hj (Nock.Framework.recordCount_le r.state)⟩ hj) :=
  (filterMap_finRange_three _ (Nock.Framework.recordCount_le r.state) r.memoryRecord).2 j hj

theorem flatMap_getElem?_prefix {β γ : Type} (R : List β) (f : β → List γ) (a : ℕ)
    (ha : a < R.length) (j : ℕ) (hj : j < (f R[a]).length) :
    (R.flatMap f)[((R.take a).map (fun r => (f r).length)).sum + j]? = (f R[a])[j]? := by
  have hsplit : R.flatMap f =
      (R.take a).flatMap f ++ (f R[a] ++ (R.drop (a + 1)).flatMap f) := by
    conv_lhs => rw [← List.take_append_drop a R]
    rw [List.flatMap_append, List.drop_eq_getElem_cons ha, List.flatMap_cons]
  have hlen : ((R.take a).flatMap f).length = ((R.take a).map (fun r => (f r).length)).sum := by
    rw [List.length_flatMap]
  rw [hsplit, List.getElem?_append_right (by omega), ← hlen]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hj]

/-- **`requestList` is indexed by the exponent prefix**: slot `j` of BFS row `a` sits at
`Σ_{a' < a} recordCount(state a') + j` (0-based). -/
theorem requestList_getElem? (S : SemanticSkeleton) (a : ℕ)
    (ha : a < (computeSkeletonRows S).length) (j : ℕ)
    (hj : j < Nock.Framework.recordCount (computeSkeletonRows S)[a].state) :
    (requestList S)[(((computeSkeletonRows S).take a).map
        (fun r => Nock.Framework.recordCount r.state)).sum + j]? =
      some ((computeSkeletonRows S)[a].memoryRecord
        ⟨j, lt_of_lt_of_le hj (Nock.Framework.recordCount_le _)⟩ hj) := by
  have h := flatMap_getElem?_prefix (computeSkeletonRows S) recs a ha j
    (by rw [recs_length]; exact hj)
  simp only [recs_length] at h
  rw [requestList_eq, h, recs_getElem? _ j hj]

end Nock.RedTeam.Batch772
