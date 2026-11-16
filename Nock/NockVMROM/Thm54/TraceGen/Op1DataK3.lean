/-
  Nock/NockVMROM/Thm54/TraceGen/Op1DataK3.lean

  The assembled `Op1Execution_K3 : BuildableNockExecution (ZMod 97)
  K3` — all fourteen fields — and the directly-built literal-node commitment
  `HonestCommitment.Data Op1Execution_K3` for the slice `*[0 [1 5]] = 5` over base `F = ZMod 97`,
  table field `K = K3` (`finrank F K = 3`), seed `z = 8`, `α = 4`.

  A re-basing of `Op1Data.lean`.  The two semantic-CORE fields come from `Op1SemanticDataK3.lean` /
  `Op1MemoryTraceK3.lean`; the twelve non-semantic fields from `Op1BuildablePartsK3.lean`.  The
  literal committed node trees are exactly the F73/degree-1 shape (nodes are field-polymorphic).  The
  only field-touching deltas are:

  * `q_eq_ringChar : E.q = ringChar K` is now `97 = ringChar K3` (via `ringChar_K3`), not
    `ringChar (ZMod 97)`;
  * the two `K`-parametrized census fields `census : CombinedSkeletonCensus K …` and
    `combinedBounded : CombinedBoundedBy K …` are re-derived over `K3` — their proofs are
    field-agnostic (they inspect nouns and leaf counts), so they port verbatim with `K` in the type.

  The four field-free skeleton obligations (`slotSemantics`, `recordEquations`, `sizeWindowBound`,
  `skeletonBounded`) are reused unchanged from `Op1Skeleton`, transported by `skeletonOfNodes_eq`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op1SemanticDataK3
import Nock.NockVMROM.Thm54.TraceGen.Op1MemoryTraceK3
import Nock.NockVMROM.Thm54.TraceGen.Op1BuildablePartsK3
import Nock.NockVMROM.Thm54.HonestCommitment

namespace Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3

open Nock Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
  (ComputeTimestampSpecializesAt MemoryTimestampSpecializesAt)

/-! ## The assembled buildable execution -/

/-- The OP1/K3 slice's complete `BuildableNockExecution` — all fourteen fields explicitly named. -/
noncomputable def Op1Execution_K3
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    BuildableNockExecution F K where
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

theorem bind_computeRow (z α : K) :
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

theorem bind_readRow (z α : K) :
    BindMemoryRowA z readSkeletonRow (readRowA z α) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [readSkeletonRow, MemoryTable.fanoutMem, memoryChildCell, readRowA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decomposeRow (z α : K) :
    BindMemoryRowA z decomposeSkeletonRow (decomposeRowA z α) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_headRow (z : K) :
    BindMemoryRowA z headSkeletonRow (headRowA z) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem headSkeletonRow.state) := by
      simp [headSkeletonRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyRow (z α : K) :
    BindMemoryRowA z verifySkeletonRow (verifyRowA z α) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [verifySkeletonRow, MemoryTable.fanoutMem, memoryChildCell, verifyRowA, verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_tailRow (z : K) :
    BindMemoryRowA z tailSkeletonRow (tailRowA z) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem tailSkeletonRow.state) := by
      simp [tailSkeletonRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_dummyHaltRow (z : K) :
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
noncomputable def op1ComputeNode : ComputeNode K where
  skel := computeSkeletonRow
  stamp := { state := .s1, lnPrevExponent := 0, lnExponent := 1, recordExponent := fun _ => 1 }
  row := computeRow seedZ alphaA

noncomputable def op1ComputeTree : NTree (ComputeNode K) := .node op1ComputeNode []

noncomputable def dummyHaltNode : MemoryNode K where
  skel := dummyHaltSkeletonRow
  stamp := { state := .halt, recordExponent := 0 }
  row := dummyHaltRowA seedZ

noncomputable def dummyHaltMemTree : NTree (MemoryNode K) := .node dummyHaltNode []

noncomputable def op1ReadNode : MemoryNode K where
  skel := readSkeletonRow
  stamp := { state := .read_root, recordExponent := 1 }
  row := readRowA seedZ alphaA

noncomputable def op1DecomposeNode : MemoryNode K where
  skel := decomposeSkeletonRow
  stamp := { state := .decompose, recordExponent := 0 }
  row := decomposeRowA seedZ alphaA

noncomputable def op1HeadNode : MemoryNode K where
  skel := headSkeletonRow
  stamp := { state := .halt, recordExponent := 0 }
  row := headRowA seedZ

noncomputable def op1VerifyNode : MemoryNode K where
  skel := verifySkeletonRow
  stamp := { state := .verify_child, recordExponent := 1 }
  row := verifyRowA seedZ alphaA

noncomputable def op1TailNode : MemoryNode K where
  skel := tailSkeletonRow
  stamp := { state := .halt, recordExponent := 0 }
  row := tailRowA seedZ

noncomputable def op1MemTree : NTree (MemoryNode K) :=
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

/-! ## The two `K`-parametrized census fields, re-derived over `K3`

These re-derive `Op1Skeleton.census` / `Op1Skeleton.combinedBounded` with the table field `K = K3`
in the type.  The proofs inspect only nouns and leaf counts, so they are identical to the degree-1
versions modulo the type parameter. -/

/-- `combinedBounded` over `K3`: every comparison-census noun pair is `q = 97`-bounded on both
sides. -/
theorem combinedBounded_K3 :
    ProductionP8Containment.CombinedBoundedBy K 97 semanticSkeleton := by
  intro pair hp
  simp [EdgeComparisonCensus.combinedSkeletonPairs,
    BoundSemanticTrace.skeletonPairs, EdgeComparisonCensus.edgePairs,
    EdgeComparisonCensus.rowEdgePairs, P8Census.skeletonComparisonCensus,
    P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
    semanticSkeleton, computeSkeletonRow, NTree.childOpt,
    subjectNoun, formulaNoun, headNoun, resultNoun, requestSkeleton,
    SemanticStrategy.SemanticSkeleton.publicClaim, SemanticTrace.ComparisonUse.pair,
    decActive, computeSkeletonRows, bfsForest] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [FieldEmbedding.BoundedBy]

/-- `census` over `K3`: the comparison census of the skeleton lies inside the paper's leaf window
`Λ = 3`. -/
def census_K3 : EdgeComparisonCensus.CombinedSkeletonCensus K semanticSkeleton 3 where
  p8 :=
    { leaves_bounded := by
        intro pair hp
        simp [BoundSemanticTrace.skeletonPairs, semanticSkeleton, computeSkeletonRow,
          P8Census.skeletonComparisonCensus, P8Census.skeletonComparisons,
          P8Census.skeletonUse, P8Census.skeletonDec,
          subjectNoun, formulaNoun, headNoun, resultNoun, requestSkeleton,
          SemanticStrategy.SemanticSkeleton.publicClaim,
          SemanticTrace.ComparisonUse.pair, decActive,
          computeSkeletonRows, bfsForest] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [Noun.leaves] }
  edges :=
    { leaves_bounded := by
        intro pair hp
        simp [EdgeComparisonCensus.edgePairs, EdgeComparisonCensus.rowEdgePairs,
          semanticSkeleton, computeSkeletonRow, NTree.childOpt, bfsForest] at hp }

/-! ## The honest commitment -/

/-- The directly-built honest commitment of the OP1/K3 slice: literal `OP_1` compute node and the
five memory nodes.  The four field-free census obligations are transported from `Op1Skeleton`; the
two `K`-parametrized ones are the local `K3` re-derivations. -/
noncomputable def data
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    Data (Op1Execution_K3 hread hdec hver) where
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
  slotSemantics := skeletonOfNodes_eq ▸ Op1Skeleton.slotSemantics
  recordEquations := skeletonOfNodes_eq ▸ Op1Skeleton.recordEquations
  census := skeletonOfNodes_eq ▸ census_K3
  sizeWindowBound := skeletonOfNodes_eq ▸ Op1Skeleton.sizeWindowBound
  q_eq_ringChar := by show (97 : ℕ) = ringChar K; exact ringChar_K3.symm
  skeletonBounded := skeletonOfNodes_eq ▸ Op1Skeleton.skeletonBounded
  combinedBounded := skeletonOfNodes_eq ▸ combinedBounded_K3

/-- The committed skeleton this commitment derives is exactly the OP1 committed skeleton. -/
theorem data_skeleton
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    (data hread hdec hver).skeleton = semanticSkeleton :=
  skeletonOfNodes_eq

end Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3.Op1Execution_K3
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3.data
