/-
  Nock/NockVMROM/Thm54/TraceGen/Op1Data.lean

  The assembled
  `Op1Execution : BuildableNockExecution (ZMod 97) (ZMod 97)` — all fourteen fields — and the
  directly-built literal-node commitment `HonestCommitment.Data Op1Execution` for the slice
  `*[0 [1 5]] = 5` over `K = ZMod 97`, `Λ = 3`, seed `z = 8`, `α = 4`.

  `Op1Execution` bundles the two semantic-CORE fields (`semanticData` from `Op1SemanticData.lean`,
  `memoryTrace` from `Op1MemoryTrace.lean`) with the twelve non-semantic fields of
  `Op1BuildableParts.lean`.

  The commitment supplies `computeNodes`/`memoryNodes` as literal node trees (NEVER via
  `dataOf`/`computeNodesOf`): one `OP_1` compute node and the five-row memory reconstruction
  `read -> dec -> (halt, verify -> halt)`.  Their `skeletonOfNodes` is definitionally
  `Op1Skeleton.semanticSkeleton`, so the six census-closure obligations already discharged there
  (`slotSemantics`, `recordEquations`, `census`, `sizeWindowBound`, `skeletonBounded`,
  `combinedBounded`) are reused by `▸`-transport.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op1MemoryTrace
import Nock.NockVMROM.Thm54.BelowDefs.HonestCommitment
import Nock.NockVMROM.Thm54.ConcreteStrictPackage

namespace Nock.NockVMROM.Thm54.TraceGen.Op1Config

open Nock Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
  (ComputeTimestampSpecializesAt MemoryTimestampSpecializesAt)

/-! ## The assembled buildable execution -/

/-- The OP1 slice's complete `BuildableNockExecution` — all fourteen fields explicitly named. -/
noncomputable def Op1Execution
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    BuildableNockExecution F F where
  q := 97
  q_gt_one := by norm_num
  Λ := 3
  cfg := cfg seedZ alphaA
  execA := execA seedZ alphaA
  exec := exec seedZ alphaA
  exec_encode := exec_encode seedZ alphaA
  semanticData := semanticData hread hdec hver
  memoryTrace := memoryTrace hread hdec hver
  requestNodup := requestNodup seedZ alphaA
  recordCountBalance := recordCountBalance seedZ alphaA
  q_le_ringChar := q_le_ringChar
  two_ne_zero := two_ne_zero
  Ksz_lt_ringChar := Ksz_lt_ringChar seedZ alphaA
  programIOCapacity := programIOCapacity seedZ alphaA
  memoryIOCapacity := memoryIOCapacity seedZ alphaA

/-! ## Row-skeleton bindings of the concrete rows -/

theorem bind_computeRow (z α : F) :
    BindComputeRow z computeSkeletonRow (computeRow z α) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP,
        computeSkeletonRow, computeRow, computeDec, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp computeSkeletonRow.state) := by
      simp [computeSkeletonRow, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, computeRow, computePub]
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, rfl⟩
    · rfl
    · rfl

theorem bind_readRow (z α : F) :
    BindMemoryRowA z readSkeletonRow (readRowA z α) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [readSkeletonRow, MemoryTable.fanoutMem, memoryChildCell, readRowA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decomposeRow (z α : F) :
    BindMemoryRowA z decomposeSkeletonRow (decomposeRowA z α) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_headRow (z : F) :
    BindMemoryRowA z headSkeletonRow (headRowA z) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem headSkeletonRow.state) := by
      simp [headSkeletonRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyRow (z α : F) :
    BindMemoryRowA z verifySkeletonRow (verifyRowA z α) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [verifySkeletonRow, MemoryTable.fanoutMem, memoryChildCell, verifyRowA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_tailRow (z : F) :
    BindMemoryRowA z tailSkeletonRow (tailRowA z) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem tailSkeletonRow.state) := by
      simp [tailSkeletonRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_dummyHaltRow (z : F) :
    BindMemoryRowA z dummyHaltSkeletonRow (dummyHaltRowA z) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem dummyHaltSkeletonRow.state) := by
      simp [dummyHaltSkeletonRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

/-! ## The literal committed node trees -/

/-- The `OP_1` compute node: skeleton row, α-free timestamp `(ln_prev, ln, rec) = (0, 1, 1)`, and
concrete row. -/
noncomputable def op1ComputeNode : ComputeNode F where
  skel := computeSkeletonRow
  stamp := { state := .s1, lnPrevExponent := 0, lnExponent := 1, recordExponent := fun _ => 1 }
  row := computeRow seedZ alphaA

noncomputable def op1ComputeTree : NTree (ComputeNode F) := .node op1ComputeNode []

noncomputable def dummyHaltNode : MemoryNode F where
  skel := dummyHaltSkeletonRow
  stamp := { state := .halt, recordExponent := 0 }
  row := dummyHaltRowA seedZ

noncomputable def dummyHaltMemTree : NTree (MemoryNode F) := .node dummyHaltNode []

noncomputable def op1ReadNode : MemoryNode F where
  skel := readSkeletonRow
  stamp := { state := .read_root, recordExponent := 1 }
  row := readRowA seedZ alphaA

noncomputable def op1DecomposeNode : MemoryNode F where
  skel := decomposeSkeletonRow
  stamp := { state := .decompose, recordExponent := 0 }
  row := decomposeRowA seedZ alphaA

noncomputable def op1HeadNode : MemoryNode F where
  skel := headSkeletonRow
  stamp := { state := .halt, recordExponent := 0 }
  row := headRowA seedZ

noncomputable def op1VerifyNode : MemoryNode F where
  skel := verifySkeletonRow
  stamp := { state := .verify_child, recordExponent := 1 }
  row := verifyRowA seedZ alphaA

noncomputable def op1TailNode : MemoryNode F where
  skel := tailSkeletonRow
  stamp := { state := .halt, recordExponent := 0 }
  row := tailRowA seedZ

noncomputable def op1MemTree : NTree (MemoryNode F) :=
  .node op1ReadNode
    [.node op1DecomposeNode
      [.node op1HeadNode [], .node op1VerifyNode [.node op1TailNode []]]]

/-! ## Timestamp specialization of each concrete row -/

theorem op1_compute_specializes :
    ComputeTimestampSpecializesAt alphaA op1ComputeNode.stamp (computeRow seedZ alphaA) := by
  refine ComputeTimestampSpecializesAt.of_absolute rfl rfl rfl ?_ ?_ ?_ ?_
    (by decide) (fun i => by fin_cases i <;> decide)
  · show (computePub seedZ alphaA).ln_prev = alphaA ^ 0
    simp [computePub]
  · show (computePub seedZ alphaA).ln = alphaA ^ 1
    simp [computePub, pow_one]
  · intro i
    fin_cases i <;>
      simp [op1ComputeNode, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        computeRow, computePub, requestRecord, MemRec.zero, pow_one]
  · intro i hi
    fin_cases i <;>
      simp_all [op1ComputeNode, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        computeRow, computePub, MemRec.zero]

theorem op1_dummyHalt_specializes :
    MemoryTimestampSpecializesAt alphaA dummyHaltNode.stamp (dummyHaltRowA seedZ) :=
  ⟨rfl, rfl, by simp [dummyHaltNode, memoryMemRecKind, dummyHaltRowA, dummyHaltPub, MemRec.zero],
    by simp [dummyHaltNode, memoryMemRecKind, dummyHaltRowA, dummyHaltPub, MemRec.zero]⟩

theorem op1_read_specializes :
    MemoryTimestampSpecializesAt alphaA op1ReadNode.stamp (readRowA seedZ alphaA) :=
  ⟨rfl, rfl, by simp [op1ReadNode, memoryMemRecKind, readRowA, readPub, requestRecord, pow_one],
    by simp [op1ReadNode, memoryMemRecKind]⟩

theorem op1_decompose_specializes :
    MemoryTimestampSpecializesAt alphaA op1DecomposeNode.stamp (decomposeRowA seedZ alphaA) :=
  ⟨rfl, rfl, by simp [op1DecomposeNode, memoryMemRecKind, decomposeRowA, decomposePub, MemRec.zero],
    by simp [op1DecomposeNode, memoryMemRecKind, decomposeRowA, decomposePub, MemRec.zero]⟩

theorem op1_head_specializes :
    MemoryTimestampSpecializesAt alphaA op1HeadNode.stamp (headRowA seedZ) :=
  ⟨rfl, rfl, by simp [op1HeadNode, memoryMemRecKind, headRowA, headPub, MemRec.zero],
    by simp [op1HeadNode, memoryMemRecKind, headRowA, headPub, MemRec.zero]⟩

theorem op1_verify_specializes :
    MemoryTimestampSpecializesAt alphaA op1VerifyNode.stamp (verifyRowA seedZ alphaA) :=
  ⟨rfl, rfl, by simp [op1VerifyNode, memoryMemRecKind, verifyRowA, verifyPub, requestRecord,
      pow_one],
    by simp [op1VerifyNode, memoryMemRecKind]⟩

theorem op1_tail_specializes :
    MemoryTimestampSpecializesAt alphaA op1TailNode.stamp (tailRowA seedZ) :=
  ⟨rfl, rfl, by simp [op1TailNode, memoryMemRecKind, tailRowA, tailPub, MemRec.zero],
    by simp [op1TailNode, memoryMemRecKind, tailRowA, tailPub, MemRec.zero]⟩

/-! ## Local node validity -/

theorem op1ComputeTree_OK :
    ComputeNodesOK seedZ alphaA op1ComputeTree := by
  refine ComputeNodesOK.mk' ⟨?_, rfl, bind_computeRow _ _, op1_compute_specializes⟩ (by simp)
  simp [op1ComputeNode, computeSkeletonRow, ComputeTable.fanoutComp]

theorem dummyHaltMemTree_OK :
    MemoryNodesOK seedZ alphaA dummyHaltMemTree := by
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_dummyHaltRow _, op1_dummyHalt_specializes⟩ (by simp)

theorem op1MemTree_OK :
    MemoryNodesOK seedZ alphaA op1MemTree := by
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readRow _ _, op1_read_specializes⟩ ?_
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decomposeRow _ _, op1_decompose_specializes⟩ ?_
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_headRow _, op1_head_specializes⟩ (by simp)
  · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyRow _ _, op1_verify_specializes⟩ ?_
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_tailRow _, op1_tail_specializes⟩ (by simp)

/-! ## The committed skeleton is exactly `Op1Skeleton.semanticSkeleton` -/

theorem skeletonOfNodes_eq :
    skeletonOfNodes op1ComputeTree [dummyHaltMemTree, op1MemTree] = semanticSkeleton := by
  simp [skeletonOfNodes, op1ComputeTree, dummyHaltMemTree, op1MemTree, mapNTree, semanticSkeleton,
    op1ComputeNode, dummyHaltNode, op1ReadNode, op1DecomposeNode, op1HeadNode, op1VerifyNode, op1TailNode,
    dummyHaltSkeletonTree, readSkeletonTree, decomposeSkeletonTree, headSkeletonTree, verifySkeletonTree,
    tailSkeletonTree]

/-! ## The honest commitment -/

/-- The directly-built honest commitment of the OP1 slice: literal `OP_1` compute node and the
five memory nodes, with all six census obligations transported from `Op1Skeleton`. -/
noncomputable def data
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    Data (Op1Execution hread hdec hver) where
  computeNodes := op1ComputeTree
  memoryNodes := [dummyHaltMemTree, op1MemTree]
  compute_rows := by
    show mapNTree ComputeNode.row op1ComputeTree = (exec seedZ alphaA).computeTree
    simp [op1ComputeTree, op1ComputeNode, mapNTree, exec]
  memory_rows := by
    show [dummyHaltMemTree, op1MemTree].map (mapNTree MemoryNode.row) =
      (execA seedZ alphaA).memoryForest
    simp [dummyHaltMemTree, dummyHaltNode, op1MemTree, op1ReadNode, op1DecomposeNode, op1HeadNode,
      op1VerifyNode, op1TailNode, mapNTree, exec, execA, dummyHaltTreeA, readTreeA,
          decomposeTreeA, headTreeA,
      verifyTreeA, tailTreeA]
  computeOK := op1ComputeTree_OK
  memoryOK := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact dummyHaltMemTree_OK
    · exact op1MemTree_OK
  root_line_exponent := rfl
  root_line_origin := rfl
  nounSizeBound := 5
  Λ := 3
  slotSemantics := skeletonOfNodes_eq ▸ slotSemantics
  recordEquations := skeletonOfNodes_eq ▸ recordEquations
  census := skeletonOfNodes_eq ▸ census
  sizeWindowBound := skeletonOfNodes_eq ▸ sizeWindowBound
  q_eq_ringChar := by show (97 : ℕ) = ringChar F; rw [ZMod.ringChar_zmod_n]
  skeletonBounded := skeletonOfNodes_eq ▸ skeletonBounded
  combinedBounded := skeletonOfNodes_eq ▸ combinedBounded

/-- The committed skeleton this commitment derives is exactly the OP1 committed skeleton. -/
theorem data_skeleton
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    (data hread hdec hver).skeleton = semanticSkeleton :=
  skeletonOfNodes_eq

end Nock.NockVMROM.Thm54.TraceGen.Op1Config

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1Config.Op1Execution
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1Config.data
