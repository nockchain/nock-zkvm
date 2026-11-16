/-
  Nock/NockVMROM/Thm54/TraceGen/GenBalance.lean

  **`hbal` — `RecordCountBalanced` for any generated execution.**

  This module is that composition, and it has exactly two
  steps neither of which was written down:

  1. **Threading does not move a row's public state.**  `genMemoryForest` is
     `threadGenForest inp 0 (genMemForestFromTree …)` (`GenSemanticDataParts.lean:45`), and
     `genMemForestFromTree_balanced` is about the *unthreaded* forest.  `threadGenRow` rewrites only
     the two accumulator columns via `setAcc`, so `memPubSt` survives it — but `ForestCountBalanced`
     is defined by structural recursion over the forest, not over the BFS row list, so the transport
     goes through `fibreCount_bfsForest` in both directions rather than by rewriting in place.

  2. **`ExactExecution.memoryRows` is the forest mapped through `GenMemoryRow.row`**, which
     `fibreCount_bfsForest_mapNTree_row` (`GenTierABalance.lean:511`) already handles.

  `DotConfig257.recordCountBalance` does exactly this at one configuration; the two theorems below
  are the same argument with the configuration removed.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenForestIndexRange

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.RowLayout
open Nock.Framework.Thm54
open MemoryTable

variable {F K : Type} [Field F] [Field K] [Algebra F K]

variable {lmb : K}

/-! ## Threading preserves the public-state fibre -/

/-- Setting the accumulator columns does not touch the public state. -/
@[simp] theorem memPubSt_setGenAcc (g : GenMemoryRow K) (ipre icur : K) :
    memPubSt (setGenAcc g ipre icur) = memPubSt g := rfl

/-- `threadGenRow` rewrites only the accumulator columns. -/
@[simp] theorem memPubSt_threadGenRow (inp : Inputs K) (acc : K) (g : GenMemoryRow K) :
    memPubSt (threadGenRow inp acc g).2 = memPubSt g := rfl

/-- **Threading the whole BFS row list leaves every fibre count unchanged.** -/
theorem fibreCount_threadGenRows (inp : Inputs K) (s : MState) (l : List (GenMemoryRow K)) :
    ∀ acc : K, fibreCount memPubSt (threadGenRows inp acc l) s = fibreCount memPubSt l s := by
  induction l with
  | nil => intro acc; rfl
  | cons g gs ih =>
      intro acc
      rw [threadGenRows, fibreCount_cons, fibreCount_cons, ih, memPubSt_threadGenRow]

/-- **`ForestCountBalanced` survives threading.**

Stated as fibre equality rather than as the balance predicate so that both sides of the balance
transport in one step. -/
theorem forestFibre_threadGenForest (inp : Inputs K) (acc : K) (s : MState)
    (forest : List (NTree (GenMemoryRow K))) :
    forestFibre s (threadGenForest inp acc forest) = forestFibre s forest := by
  rw [← fibreCount_bfsForest s (threadGenForest inp acc forest),
    ← fibreCount_bfsForest s forest, threadGenForest_bfs_labels,
    fibreCount_threadGenRows]

/-- **The generated memory forest is balanced, for any accepted program.**

`genMemForestFromTree_balanced` holds at an arbitrary compute tree; threading preserves it. -/
theorem genMemoryForest_balanced (z α : K) (inp : Inputs K) (t : NTree (GenComputeRow K)) :
    ForestCountBalanced (genMemoryForest z α lmb inp t) := by
  unfold genMemoryForest ForestCountBalanced
  rw [forestFibre_threadGenForest, forestFibre_threadGenForest]
  exact genMemForestFromTree_balanced (encC z) z α (bfsAssign (airReorder t))

/-! ## `hbal` at the generic carrier -/

/-- **`RecordCountBalanced` for `genExactExecution`, from a balanced forest.**

Quantified over an arbitrary `mf`, matching `genExactExecution`'s own generality. -/
theorem genExactExecution_recordCountBalance
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (hbal : ForestCountBalanced mf) :
    RecordCountBalanced
      (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem) := by
  have hst : ∀ s : MState,
      memoryStateCount
        (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem) s =
        forestFibre s mf := by
    intro s
    -- the row encode keeps every row's state
    have hA : memoryStateCount
        (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem) s =
        memoryStateCount
          (genExactExecutionA (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem) s := by
      unfold memoryStateCount fibreCount
      rw [genExactExecution_eq_encodeMem, ExactExecution.encodeMem_memoryRows, List.countP_map]
      simp [Function.comp_def]
    rw [hA]
    unfold memoryStateCount ExactExecution.memoryRows
    show fibreCount (fun row : MState × DTmem K => row.2.2.st)
      ((bfsForest (mf.map (mapNTree GenMemoryRow.row))).map NTree.label) s = _
    rw [fibreCount_bfsForest_mapNTree_row, fibreCount_bfsForest]
  unfold RecordCountBalanced
  rw [hst, hst]
  exact hbal

/-- **`hbal` for any accepted program** — the form `genBuildable` consumes. -/
theorem genBuildable_hbal
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α : K) (a b c : K) (inp : Inputs K)
    (ct : NTree (GenComputeRow K)) (t : NTree (GenComputeRow K))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h) :
    RecordCountBalanced
      (genExactExecution (F := F) chal Ksz orbit horb a b c ct
        (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem) :=
  genExactExecution_recordCountBalance chal Ksz orbit horb a b c ct _ hmempos hcomp hmem
    (genMemoryForest_balanced z α inp t)

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.fibreCount_threadGenRows
#print axioms Nock.NockVMROM.Thm54.TraceGen.forestFibre_threadGenForest
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemoryForest_balanced
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecution_recordCountBalance
#print axioms Nock.NockVMROM.Thm54.TraceGen.genBuildable_hbal
