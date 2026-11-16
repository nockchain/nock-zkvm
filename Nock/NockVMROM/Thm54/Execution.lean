import Nock.NockVMROM.Thm54.Config
import Nock.NockVM

/-!
# Forest-first exact execution carriers

Flat rows are derived by BFS.
-/

namespace Nock.NockVMROM.Thm54

open Nock.Walk

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- One configured forest-first execution.

The compute carrier is exactly one tree.  The memory carrier is a nonempty forest whose root count
is the configured `kMem`.  The two active lengths are definitionally tied, by proof fields, to the
BFS lengths of these carriers.  There are deliberately no independent flat rows or IO lists.
-/
structure ExactExecution (cfg : ExactConfig F K) where
  /-- The single authoritative compute tree, labeled by actual compute-table rows. -/
  computeTree : NTree (ComputeTable.State × ComputeTable.DTcomp K)
  /-- The authoritative memory forest, labeled by actual memory-table rows. -/
  memoryForest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))
  /-- The memory carrier really has at least one root. -/
  memoryForest_nonempty : memoryForest ≠ []
  /-- The configured memory-root count is the forest's actual number of roots. -/
  memory_root_count : memoryForest.length = cfg.kMem
  /-- The configured compute active length is the single tree's actual BFS length. -/
  compute_bfs_length : (bfsForest [computeTree]).length = cfg.compRows
  /-- The configured memory active length is the forest's actual BFS length. -/
  memory_bfs_length : (bfsForest memoryForest).length = cfg.memRows

namespace ExactExecution

/-- Flat compute rows are a derived BFS projection, never authoritative stored data. -/
def computeRows {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    List (ComputeTable.State × ComputeTable.DTcomp K) :=
  (bfsForest [exec.computeTree]).map NTree.label

/-- Flat memory rows are a derived BFS projection, never authoritative stored data. -/
def memoryRows {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    List (MemoryTable.MState × MemoryTable.DTmem K) :=
  (bfsForest exec.memoryForest).map NTree.label

/-- The derived compute row list has exactly the configured active length. -/
@[simp]
theorem computeRows_length {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.computeRows.length = cfg.compRows := by
  simp [computeRows, exec.compute_bfs_length]

/-- The derived memory row list has exactly the configured active length. -/
@[simp]
theorem memoryRows_length {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.memoryRows.length = cfg.memRows := by
  simp [memoryRows, exec.memory_bfs_length]

/-- A nonempty authoritative memory forest forces the configured root count to be positive. -/
theorem memoryRootCount_pos {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    0 < cfg.kMem := by
  have hlen : 0 < exec.memoryForest.length :=
    List.length_pos_of_ne_nil exec.memoryForest_nonempty
  simpa [exec.memory_root_count] using hlen

/-- Forest roots occupy the BFS prefix, so `kMem ≤ memRows`. -/
theorem kMem_le_memRows {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    cfg.kMem ≤ cfg.memRows := by
  have hbfs := bfsForest_eq_append_flatMap exec.memoryForest exec.memoryForest_nonempty
  rw [← exec.memory_bfs_length, hbfs, List.length_append, exec.memory_root_count]
  exact Nat.le_add_right _ _

/-- Executions with the same authoritative tree and forest are equal.

In particular, there is no hidden free IO payload by which two executions with identical
forest-first carriers could differ.
-/
@[ext]
theorem ext {cfg : ExactConfig F K} (x y : ExactExecution cfg)
    (hcompute : x.computeTree = y.computeTree)
    (hmemory : x.memoryForest = y.memoryForest) :
    x = y := by
  cases x
  cases y
  cases hcompute
  cases hmemory
  rfl

theorem carrierProjection_injective {cfg : ExactConfig F K} :
    Function.Injective
      (fun exec : ExactExecution cfg => (exec.computeTree, exec.memoryForest)) := by
  intro x y h
  exact ext x y (congrArg Prod.fst h) (congrArg Prod.snd h)

end ExactExecution

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.ExactExecution.computeRows_length
#print axioms Nock.NockVMROM.Thm54.ExactExecution.memoryRows_length
#print axioms Nock.NockVMROM.Thm54.ExactExecution.memoryRootCount_pos
#print axioms Nock.NockVMROM.Thm54.ExactExecution.ext
#print axioms Nock.NockVMROM.Thm54.ExactExecution.carrierProjection_injective
