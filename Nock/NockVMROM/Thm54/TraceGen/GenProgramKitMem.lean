/-
  Nock/NockVMROM/Thm54/TraceGen/GenProgramKitMem.lean

  **The served-memory size/length lemmas for the three arms `GenMatmulMemSize` was missing.**

  `genSemanticData` takes three row-count measurements — `hmempos`, `hcomp`, `hmem` — and `hmem`
  needs the memory forest's BFS row count against `2 ^ orbit.h`.  There is no generic bound on that
  count in the tree (and there cannot be a cheap one: `nounWalkSize` grows with the *nouns*, not the
  row count), so it is measured per program.

  `GenMatmulMemSize.lean` already carries the measurement kit — a per-arm
  `(length, totalSize)` pair for `OP_0`, `OP_1`/`quote`, `OP_4`, `OP_5`, `OP_6`, `OP_7`, `OP_9` and
  autocons, plus the generic reductions that make the whole forest a sum over BFS rows
  (`treeMemSize_eq`, `bfsAssign_rowForest_sum`, `airReorder_treeMemSize`).  It is missing exactly the
  three arms `GenProgramKit` had to add — `OP_2`, `OP_3`, `OP_8` — for the same reason: the matmul
  program does not use them.  This module adds two of them, `OP_3` and `OP_8`, in the same shape.

  `OP_3`'s record structure is `OP_4`'s (one formula-open record at axis `3`) and `OP_8`'s is
  `OP_7`'s (the chained pair `⟨formula, f_t, 3⟩`, `⟨f_t, f_th, 2⟩`), so both are read off the
  existing chain lemmas with no new memory theory.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenProgramKit
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulMemSize

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K]

variable {lmb : K}

/-- `OP_3`'s served memory: one formula-open record, like `OP_4`. -/
theorem gen_op3_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ) {subject tail callResult : Noun}
    {callTree t : NTree (GenComputeRow K)} {r : Noun}
    (hc : genComputeSkeleton (K := K) n subject tail = .ok (callTree, callResult))
    (h : genComputeSkeleton (K := K) (n + 1) subject (.cell (.atom 3) tail) = .ok (t, r)) :
    (genMemForestFromTree E z α lmb t).length =
      1 + (genMemForestFromTree E z α lmb callTree).length ∧
    totalSize (genMemForestFromTree E z α lmb t) =
      4 + nounWalkSize tail + totalSize (genMemForestFromTree E z α lmb callTree) := by
  refine gen_ok_mem E z α h (gen_op3 (K := K) n hc) ?_ ?_
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_one,
      genMemForestFromList_cons, genMemForestFromList_nil,
      List.length_append, List.length_append, List.length_nil]
    simp [genRowMemForest_singleton]
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_one,
      genMemForestFromList_cons, genMemForestFromList_nil,
      totalSize_append]
    rw [genRowMemForest_singleton_axis3_size]
    simp [nounWalkSize, totalSize]
    try omega

/-- `OP_8`'s served memory: the chained pair, like `OP_7`. -/
theorem gen_op8_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ) {subject b c sb result : Noun}
    {bTree cTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (bTree, sb))
    (hc : genComputeSkeleton (K := K) n (.cell sb subject) c = .ok (cTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) subject (.cell (.atom 8) (.cell b c))
      = .ok (t, r)) :
    (genMemForestFromTree E z α lmb t).length =
      1 + (genMemForestFromTree E z α lmb bTree).length +
        (genMemForestFromTree E z α lmb cTree).length ∧
    totalSize (genMemForestFromTree E z α lmb t) =
      7 + nounWalkSize b + nounWalkSize c +
        totalSize (genMemForestFromTree E z α lmb bTree) +
        totalSize (genMemForestFromTree E z α lmb cTree) := by
  refine gen_ok_mem E z α h (gen_op8 (K := K) n hb hc) ?_ ?_
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_two,
      genMemForestFromList_two, List.length_append, List.length_append]
    simp [ServiceReq.root, ServiceReq.child, ServiceReq.axis]
    rw [genRowMemForest_chain_length (lmb := lmb) (hc := rfl)]
    omega
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_two,
      genMemForestFromList_two, totalSize_append, totalSize_append]
    simp [ServiceReq.root, ServiceReq.child, ServiceReq.axis]
    rw [genRowMemForest_chain32_size]
    simp [nounWalkSize]
    omega

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_op3_mem
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_op8_mem
