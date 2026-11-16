/-
  Nock/NockVMROM/Thm54/TraceGen/GenBroadMem.lean

  **The served-memory row count of the broad program: 19 roots, 227 rows.**

  `genSemanticData` takes `hmempos`, `hcomp` and `hmem` — the two capacity measurements against
  `2 ^ orbit.h` and the non-emptiness.  `hcomp` is the compute row count (`bp_compRowsLen`, 17);
  `hmem` needs the memory forest's BFS row count, which is `totalSize` of the served forest and has
  no generic bound (`nounWalkSize` grows with the *nouns*, not with the row count).

  It is therefore measured, and the measurement is compositional: `GenMatmulMemSize`'s
  `treeMemSize_eq` / `bfsAssign_rowForest_sum` / `airReorder_treeMemSize` make the whole forest a
  sum over BFS rows and are invariant under both `bfsAssign` and `airReorder`, so the sum can be
  taken on the DFS tree the generator emits, arm by arm.  Nothing here is a bespoke reduction of the
  kind `GenTierASizeAir.lean` needed (444 lines for eight rows): with the per-arm lemmas the whole
  measurement is seventeen applications.

  At `q = 769` the orbit caps at `h = 8` (`2 ^ h ∣ 768` forces `h ≤ 8`), so the numbers that matter
  are `17 ≤ 256` and `227 ≤ 256`.  Tier A's are `8` and `184`; the broad program is a little over
  twice as heavy and still inside the same orbit.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenProgramKitMem
import Nock.NockVMROM.Thm54.TraceGen.GenBroadProgram
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticDataParts
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMemWeb
import Nock.NockVMROM.Thm54.TraceGen.GenCommitmentBridge

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## Noun-walk sizes of the program's nouns -/

theorem bp_nws_7 : nounWalkSize bp7 = 9 := by
  simp [bp7, bp7Tail, bp7B, bp7C, nounWalkSize]
theorem bp_nws_8 : nounWalkSize bp8 = 9 := by
  simp [bp8, bp8Tail, bp8B, bp8C, nounWalkSize]
theorem bp_nws_5 : nounWalkSize bp5 = 9 := by
  simp [bp5, bp5Tail, bp5B, bp5C, nounWalkSize]
theorem bp_nws_4 : nounWalkSize bp4 = 5 := by
  simp [bp4, bp4Tail, nounWalkSize]
theorem bp_nws_3 : nounWalkSize bp3 = 7 := by
  simp [bp3, bp3Tail, bp3Call, nounWalkSize]
theorem bp_nws_R3 : nounWalkSize bpR3 = 13 := by
  simp [bpR3, bp4, bp4Tail, bp3, bp3Tail, bp3Call, nounWalkSize]
theorem bp_nws_R2 : nounWalkSize bpR2 = 23 := by
  simp [bpR2, bpR3, bp5, bp5Tail, bp5B, bp5C, bp4, bp4Tail, bp3, bp3Tail, bp3Call,
    nounWalkSize]

/-! ## The two `OP_0` record trees -/

/-- `OP_7`'s axis-`1` read against the helper `5`: read, then one verify. -/
theorem bp_recordTreeSize_7C : recordTreeSize bp7Sb bp7Sb 1 = 3 := by
  rw [recordTreeSize, descentForestSize_of_lt2 _ _ (by omega)]
  simp [bp7Sb, nounWalkSize]

/-- `OP_8`'s axis-`3` read against the pushed subject `[3 [5 7]]`: read, decompose, walk the
head, verify the tail. -/
theorem bp_recordTreeSize_8C : recordTreeSize bp8Pushed bpSubject 3 = 7 := by
  rw [recordTreeSize,
    descentForestSize_of_tail _ _ (by omega) axisTopBit_three, axisRest_three,
    descentForestSize_of_lt2 _ _ (by omega)]
  simp [bp8Pushed, bp8Sb, bpSubject, formulaHead, nounWalkSize]

/-! ## Per-subtree measurements, innermost outwards -/

theorem bp_mem_op1 (E : Noun → ComputeTable.FP K) (z α : K) (subject tail : Noun) :
    (genMemForestFromTree E z α lmb (bpOp1Tree (K := K) subject tail)).length = 1 ∧
      totalSize (genMemForestFromTree E z α lmb (bpOp1Tree (K := K) subject tail))
        = 4 + nounWalkSize tail :=
  gen_quote_mem E z α 0 subject tail (bp_gen_op1 0 subject tail)

theorem bp_mem_7C (E : Noun → ComputeTable.FP K) (z α : K) :
    (genMemForestFromTree E z α lmb (bp7CTree (K := K))).length = 2 ∧
      totalSize (genMemForestFromTree E z α lmb (bp7CTree (K := K))) = 8 := by
  obtain ⟨hl, hs⟩ := gen_op0_mem E z α 0 bp7_slot (bp_gen_7C 0) (by decide)
  exact ⟨hl, by rw [hs, bp_recordTreeSize_7C]⟩

theorem bp_mem_8C (E : Noun → ComputeTable.FP K) (z α : K) :
    (genMemForestFromTree E z α lmb (bp8CTree (K := K))).length = 2 ∧
      totalSize (genMemForestFromTree E z α lmb (bp8CTree (K := K))) = 12 := by
  obtain ⟨hl, hs⟩ := gen_op0_mem E z α 0 bp8_slot (bp_gen_8C 0)
    (by simp [bp8Pushed])
  exact ⟨hl, by rw [hs, bp_recordTreeSize_8C]⟩

theorem bp_mem_7 (E : Noun → ComputeTable.FP K) (z α : K) :
    (genMemForestFromTree E z α lmb (bp7Tree (K := K))).length = 4 ∧
      totalSize (genMemForestFromTree E z α lmb (bp7Tree (K := K))) = 26 := by
  obtain ⟨hl, hs⟩ := gen_op7_mem E z α 1 (bp_gen_op1 0 bpSubject (.atom 5))
    (bp_gen_7C 0) (bp_gen_7 0)
  obtain ⟨hl1, hs1⟩ := bp_mem_op1 E z α bpSubject (.atom 5)
  obtain ⟨hl2, hs2⟩ := bp_mem_7C E z α
  refine ⟨by rw [hl, hl1, hl2], ?_⟩
  rw [hs, hs1, hs2]
  simp [bp7B, bp7C, nounWalkSize]

theorem bp_mem_8 (E : Noun → ComputeTable.FP K) (z α : K) :
    (genMemForestFromTree E z α lmb (bp8Tree (K := K))).length = 4 ∧
      totalSize (genMemForestFromTree E z α lmb (bp8Tree (K := K))) = 30 := by
  obtain ⟨hl, hs⟩ := gen_op8_mem E z α 1 (bp_gen_op1 0 bpSubject (.atom 3))
    (bp_gen_8C 0) (bp_gen_8 0)
  obtain ⟨hl1, hs1⟩ := bp_mem_op1 E z α bpSubject (.atom 3)
  obtain ⟨hl2, hs2⟩ := bp_mem_8C E z α
  refine ⟨by rw [hl, hl1, hl2], ?_⟩
  rw [hs, hs1, hs2]
  simp [bp8B, bp8C, nounWalkSize]

theorem bp_mem_5 (E : Noun → ComputeTable.FP K) (z α : K) :
    (genMemForestFromTree E z α lmb (bp5Tree (K := K))).length = 3 ∧
      totalSize (genMemForestFromTree E z α lmb (bp5Tree (K := K))) = 23 := by
  obtain ⟨hl, hs⟩ := gen_op5_mem E z α 1 (bp_gen_op1 0 bpSubject (.atom 1))
    (bp_gen_op1 0 bpSubject (.atom 2)) (bp_gen_5 0)
  obtain ⟨hl1, hs1⟩ := bp_mem_op1 E z α bpSubject (.atom 1)
  obtain ⟨hl2, hs2⟩ := bp_mem_op1 E z α bpSubject (.atom 2)
  refine ⟨by rw [hl, hl1, hl2], ?_⟩
  rw [hs, hs1, hs2]
  simp [bp5B, bp5C, nounWalkSize]

theorem bp_mem_4 (E : Noun → ComputeTable.FP K) (z α : K) :
    (genMemForestFromTree E z α lmb (bp4Tree (K := K))).length = 2 ∧
      totalSize (genMemForestFromTree E z α lmb (bp4Tree (K := K))) = 12 := by
  obtain ⟨hl, hs⟩ := gen_op4_mem E z α 1 (bp_gen_op1 0 bpSubject (.atom 1))
    bp_lus (bp_gen_4 0)
  obtain ⟨hl1, hs1⟩ := bp_mem_op1 E z α bpSubject (.atom 1)
  refine ⟨by rw [hl, hl1], ?_⟩
  rw [hs, hs1]
  simp [bp4Tail, nounWalkSize]

theorem bp_mem_3 (E : Noun → ComputeTable.FP K) (z α : K) :
    (genMemForestFromTree E z α lmb (bp3Tree (K := K))).length = 2 ∧
      totalSize (genMemForestFromTree E z α lmb (bp3Tree (K := K))) = 16 := by
  obtain ⟨hl, hs⟩ := gen_op3_mem E z α 1 (bp_gen_op1 0 bpSubject bp3Call) (bp_gen_3 0)
  obtain ⟨hl1, hs1⟩ := bp_mem_op1 E z α bpSubject bp3Call
  refine ⟨by rw [hl, hl1], ?_⟩
  rw [hs, hs1]
  simp [bp3Tail, bp3Call, nounWalkSize]

theorem bp_mem_R3 (E : Noun → ComputeTable.FP K) (z α : K) :
    (genMemForestFromTree E z α lmb (bpR3Tree (K := K))).length = 5 ∧
      totalSize (genMemForestFromTree E z α lmb (bpR3Tree (K := K))) = 43 := by
  obtain ⟨hl, hs⟩ := gen_cons_mem E z α 2 (bp_gen_4 0) (bp_gen_3 0) (bp_gen_R3 0)
  obtain ⟨hl1, hs1⟩ := bp_mem_4 E z α
  obtain ⟨hl2, hs2⟩ := bp_mem_3 E z α
  refine ⟨by rw [hl, hl1, hl2], ?_⟩
  rw [hs, hs1, hs2]
  rw [show (Noun.cell (.atom 4) bp4Tail) = bp4 from rfl, bp_nws_4, bp_nws_3]

theorem bp_mem_R2 (E : Noun → ComputeTable.FP K) (z α : K) :
    (genMemForestFromTree E z α lmb (bpR2Tree (K := K))).length = 9 ∧
      totalSize (genMemForestFromTree E z α lmb (bpR2Tree (K := K))) = 91 := by
  obtain ⟨hl, hs⟩ := gen_cons_mem E z α 3 (bp_gen_5 1) (bp_gen_R3 0) (bp_gen_R2 0)
  obtain ⟨hl1, hs1⟩ := bp_mem_5 E z α
  obtain ⟨hl2, hs2⟩ := bp_mem_R3 E z α
  refine ⟨by rw [hl, hl1, hl2], ?_⟩
  rw [hs, hs1, hs2]
  rw [show (Noun.cell (.atom 5) bp5Tail) = bp5 from rfl, bp_nws_5, bp_nws_R3]

theorem bp_mem_R1 (E : Noun → ComputeTable.FP K) (z α : K) :
    (genMemForestFromTree E z α lmb (bpR1Tree (K := K))).length = 14 ∧
      totalSize (genMemForestFromTree E z α lmb (bpR1Tree (K := K))) = 156 := by
  obtain ⟨hl, hs⟩ := gen_cons_mem E z α 4 (bp_gen_8 2) (bp_gen_R2 0) (bp_gen_R1 0)
  obtain ⟨hl1, hs1⟩ := bp_mem_8 E z α
  obtain ⟨hl2, hs2⟩ := bp_mem_R2 E z α
  refine ⟨by rw [hl, hl1, hl2], ?_⟩
  rw [hs, hs1, hs2]
  rw [show (Noun.cell (.atom 8) bp8Tail) = bp8 from rfl, bp_nws_8, bp_nws_R2]

/-- **The broad program's served memory forest: 19 roots, 227 rows.** -/
theorem bp_mem (E : Noun → ComputeTable.FP K) (z α : K) :
    (genMemForestFromTree E z α lmb (bpTree (K := K))).length = 19 ∧
      totalSize (genMemForestFromTree E z α lmb (bpTree (K := K))) = 227 := by
  obtain ⟨hl, hs⟩ := gen_cons_mem E z α 5 (bp_gen_7 3) (bp_gen_R1 0)
    (genComputeSkeleton_bp 0)
  obtain ⟨hl1, hs1⟩ := bp_mem_7 E z α
  obtain ⟨hl2, hs2⟩ := bp_mem_R1 E z α
  refine ⟨by rw [hl, hl1, hl2], ?_⟩
  rw [hs, hs1, hs2]
  rw [show (Noun.cell (.atom 7) bp7Tail) = bp7 from rfl, bp_nws_7]
  rw [show nounWalkSize bpR1 = 33 from by
    simp [bpR1, bp8, bp8Tail, bp8B, bp8C, bpR2, bpR3, bp5, bp5Tail, bp5B, bp5C,
      bp4, bp4Tail, bp3, bp3Tail, bp3Call, nounWalkSize]]

/-! ## Transport to the assigned, AIR-ordered, threaded forest

`bfsAssign` rewrites only stamps and `airReorder` only permutes children, and the memory-forest
size is invariant under both (`bfsAssign_rowForest_sum`, `airReorder_treeMemSize`).  The LogUp
threading preserves both counts (`threadGenForest_length`, `threadGenForest_totalSize`). -/

theorem bp_assigned_memLen (E : Noun → ComputeTable.FP K) (z α : K) :
    (genMemForestFromTree E z α lmb (bfsAssign (airReorder (bpTree (K := K))))).length = 19 := by
  rw [genMemForestFromTree_eq_bfsLen, (bfsAssign_rowForest_sum E z α _).2,
    ← genMemForestFromTree_eq_bfsLen, ← treeMemLen_eq, airReorder_treeMemLen,
    treeMemLen_eq]
  exact (bp_mem E z α).1

theorem bp_assigned_memSize (E : Noun → ComputeTable.FP K) (z α : K) :
    totalSize (genMemForestFromTree E z α lmb (bfsAssign (airReorder (bpTree (K := K)))))
      = 227 := by
  rw [genMemForestFromTree_eq_bfsSum, (bfsAssign_rowForest_sum E z α _).1,
    ← genMemForestFromTree_eq_bfsSum, ← treeMemSize_eq, airReorder_treeMemSize,
    treeMemSize_eq]
  exact (bp_mem E z α).2

/-- `kMem = 19` at the threaded forest `genSemanticData` actually consumes. -/
theorem bp_memoryForest_length (z α : K) (inp : MemoryTable.Inputs K) :
    (genMemoryForest z α lmb inp (bpTree (K := K))).length = 19 := by
  rw [genMemoryForest, threadGenForest_length]
  exact bp_assigned_memLen (encC z) z α

/-- **`memRows = 227`.**  This is `hmem`'s left-hand side. -/
theorem bp_memRowsLen (z α : K) (inp : MemoryTable.Inputs K) :
    (bfsForest (genMemoryForest z α lmb inp (bpTree (K := K)))).length = 227 := by
  rw [bfsForest_length, genMemoryForest, threadGenForest_totalSize]
  exact bp_assigned_memSize (encC z) z α

theorem bp_memRows_pos (z α : K) (inp : MemoryTable.Inputs K) :
    0 < (bfsForest (genMemoryForest z α lmb inp (bpTree (K := K)))).length := by
  rw [bp_memRowsLen]; omega

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.bp_mem
#print axioms Nock.NockVMROM.Thm54.TraceGen.bp_memRowsLen
#print axioms Nock.NockVMROM.Thm54.TraceGen.bp_memoryForest_length
#print axioms Nock.NockVMROM.Thm54.TraceGen.bp_memRows_pos
