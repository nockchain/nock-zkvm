/-
  Nock/NockVMROM/Thm54/TraceGen/Op1GenData.lean

  The generator's `genTrace`, run on the fresh ROM
  program `*[0 [1 5]] = 5`, produces — *through its three passes plus the served-memory pass* — the
  exact honest commitment `HonestCommitment.Data Op1Execution` of the verified OP1 slice.

  Three things are proved, all `#print axioms`-clean:

  * `gen_computeNodes_eq` / `gen_memForest_eq` — the `.node`-projection of the generated compute
    tree is exactly `Op1Config.op1ComputeTree`, and the `.node`-projection of the generated served
    forest is exactly `[Op1Config.op1MemTree]`.  The generated skeleton/timestamp rows are
    definitionally the verified nodes; the `K`-columns collapse via `Encode.encC_eq`.

  * `GenTraceOK` / `genTrace_spec` — a predicate bundling those two node-tree equalities, proved for
    every successfully generated `G` of the OP1 program.

  * `dataOfGenerated` — from `GenTraceOK G`, the honest commitment `Data Op1Execution` whose
    committed `computeNodes`/`memoryNodes` are *the generator's own nodes* (never `dataOf`), with the
    six census obligations, the binds, and the timestamp specializations transported from the
    verified `Op1Config.data` across the two node-tree equalities.  This is the generated analogue of
    `Op1Config.data`.

  Scope note (honest): `execOf G` for the OP1 program is the verified `Op1Execution`; a `genTrace →
  BuildableNockExecution` map in general needs the semantic CORE (`ExactExecutionSemanticData` /
  `ExactServedMemoryTrace`), which is the heavier still-open obligation — not PR-2.  What PR-2 lands
  is that the *committed node trees* the honest commitment consumes are produced by the generator.
-/
import Nock.NockVMROM.Thm54.TraceGen.Gen
import Nock.NockVMROM.Thm54.TraceGen.Op1Gen
import Nock.NockVMROM.Thm54.TraceGen.Op1Data

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.TraceGen.Op1Config
open Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton

/-! ## The served-memory rows collapse to the verified `Op1Config` rows -/

theorem memReadRow_eq (z α : Op1Config.F) :
    (MemoryTable.MState.read_root, memInputs z,
        memReadPub z α (.cell (.atom 1) (.atom 5)) (.atom 5))
      = readRowA z α := by
  simp only [readRowA, readPubA, memReadPub, memInputs, memPoleInv, memReqRec, readRow,
      memoryInputs, readPub,
    seedCell, decomposeCell, requestRecord, reqPoleInv, fp, encC_eq, formulaNoun, headNoun,
    resultNoun]

theorem memDecomposeRow_eq (z : Op1Config.F) :
    (MemoryTable.MState.decompose, memInputs z,
        memDecomposePub z (.cell (.atom 1) (.atom 5)) (.atom 1) (.atom 5))
      = decomposeRowA z alphaA := by
  simp only [decomposeRowA, decomposePubA, memDecomposePub, memInputs, memPoleInv, decomposeRow,
      memoryInputs, decomposePub,
    decomposeCell, headCell, verifyCell, reqPoleInv, fp, encC_eq, formulaNoun, headNoun,
    resultNoun]

theorem memHeadRow_eq (z : Op1Config.F) :
    (MemoryTable.MState.halt, memInputs z, memHeadPub z (.cell (.atom 1) (.atom 5)) (.atom 1))
      = headRowA z := by
  simp only [headRowA, headPubA, memHeadPub, memInputs, memPoleInv, headRow, memoryInputs,
      headPub, headCell,
    reqPoleInv, fp, encC_eq, formulaNoun, headNoun, resultNoun]

theorem memVerifyRow_eq (z α : Op1Config.F) :
    (MemoryTable.MState.verify_child, memInputs z,
        memVerifyPub z α (.cell (.atom 1) (.atom 5)) (.atom 5))
      = verifyRowA z α := by
  simp only [verifyRowA, verifyPubA, memVerifyPub, memInputs, memPoleInv, memReqRec, verifyRow,
      memoryInputs, verifyPub,
    verifyCell, tailCell, requestRecord, reqPoleInv, fp, encC_eq, formulaNoun, headNoun,
    resultNoun]

theorem memTailRow_eq (z : Op1Config.F) :
    (MemoryTable.MState.halt, memInputs z, memTailPub z (.atom 5)) = tailRowA z := by
  simp only [tailRowA, tailPubA,
    memTailPub, memInputs, tailRow, memoryInputs, tailPub, tailCell, fp, encC_eq,
    resultNoun]

/-! ## The generated node trees are the verified committed node trees -/

/-- The generated compute tree's `.node` projection is exactly the verified `op1ComputeTree`. -/
theorem gen_computeNodes_eq :
    mapNTree GenComputeRow.node
        (renderRows seedZ alphaA (assignExponents
          (.node (skelNode (genSkelOp1 subjectNoun formulaNoun resultNoun (.atom 1))
            [⟨formulaNoun, resultNoun, 3, 0⟩]) [])))
      = op1ComputeTree := by
  have hstate : (genSkelOp1 subjectNoun formulaNoun resultNoun (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  simp only [assignExponents, assignTree, assignList, renderRows, renderNode, skelNode, hstate,
    List.map_nil, mapNTree]
  show NTree.node (GenComputeRow.node _) [] = op1ComputeTree
  simp only [GenComputeRow.node, op1ComputeTree, op1ComputeNode]
  rw [renderOp1Row_eq]
  rfl

/-- The generated served forest's `.node` projection is exactly the verified `[op1MemTree]`. -/
theorem gen_memForest_eq :
    (genOp1MemForest seedZ alphaA 5).map (mapNTree GenMemoryRow.node) = [op1MemTree] := by
  simp only [genOp1MemForest, List.map_cons, List.map_nil, mapNTree, GenMemoryRow.node,
    op1MemTree, op1ReadNode, op1DecomposeNode, op1HeadNode, op1VerifyNode, op1TailNode]
  rw [memReadRow_eq, memDecomposeRow_eq, memHeadRow_eq, memVerifyRow_eq, memTailRow_eq]
  rfl

/-! ## `GenTraceOK` and the generator specification -/

/-- The generator succeeded and committed exactly the verified OP1 node trees: the compute tree and
    the served memory forest that the honest commitment `Op1Config.data` consumes.  (This is the
    OP1-family specialization; the general predicate over an arbitrary ROM program bundles the same
    fields against that program's committed skeleton.) -/
structure GenTraceOK (G : GenTrace Op1Config.F Op1Config.F) : Prop where
  computeNodes_eq : mapNTree GenComputeRow.node G.computeNodes = op1ComputeTree
  memoryForest_eq : G.memoryNodes.map (mapNTree GenMemoryRow.node) = [op1MemTree]

/-- **`genTrace_spec` (PR-2 gate).**  Every successful run of the generator on the OP1 program
    commits exactly the verified honest node trees. -/
theorem genTrace_spec (n : ℕ) (G : GenTrace Op1Config.F Op1Config.F)
    (h : genTrace 97 3 seedZ alphaA (n + 1) subjectNoun formulaNoun = .ok G) :
    GenTraceOK G := by
  have hG : G =
      { subject := subjectNoun, formula := formulaNoun, result := resultNoun, fuel := n + 1
        computeNodes := renderRows seedZ alphaA (bfsAssign
          (.node (skelNode (genSkelOp1 subjectNoun formulaNoun resultNoun (.atom 1))
            [⟨formulaNoun, resultNoun, 3, 0⟩]) []))
        memoryNodes := genOp1MemForest seedZ alphaA 5 } :=
    Except.ok.inj h.symm
  subst hG
  refine ⟨?cmp, gen_memForest_eq⟩
  rw [bfsAssign_node_nil_eq_assignExponents]
  exact gen_computeNodes_eq

/-! ## The generated honest commitment (the generated analogue of `Op1Config.data`) -/

/-- **`dataOfGenerated`.**  The honest commitment of the OP1 slice whose committed compute/memory
    node trees are *the generator's own emitted nodes*, with every census / bind / specialization
    obligation transported from the verified `Op1Config.data` across the two node-tree equalities of
    `GenTraceOK`. -/
noncomputable def dataOfGenerated (G : GenTrace Op1Config.F Op1Config.F) (h : GenTraceOK G)
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    Data (Op1Execution hread hdec hver) where
  computeNodes := mapNTree GenComputeRow.node G.computeNodes
  memoryNodes := dummyHaltMemTree :: G.memoryNodes.map (mapNTree GenMemoryRow.node)
  compute_rows := by rw [h.computeNodes_eq]; exact (Op1Config.data hread hdec hver).compute_rows
  memory_rows := by rw [h.memoryForest_eq]; exact (Op1Config.data hread hdec hver).memory_rows
  computeOK := by rw [h.computeNodes_eq]; exact (Op1Config.data hread hdec hver).computeOK
  memoryOK := by rw [h.memoryForest_eq]; exact (Op1Config.data hread hdec hver).memoryOK
  root_line_exponent := by
    rw [h.computeNodes_eq]; exact (Op1Config.data hread hdec hver).root_line_exponent
  root_line_origin := by
    rw [h.computeNodes_eq]; exact (Op1Config.data hread hdec hver).root_line_origin
  nounSizeBound := 5
  Λ := 3
  slotSemantics := by
    rw [h.computeNodes_eq, h.memoryForest_eq]
    exact (Op1Config.data hread hdec hver).slotSemantics
  recordEquations := by
    rw [h.computeNodes_eq, h.memoryForest_eq]
    exact (Op1Config.data hread hdec hver).recordEquations
  census := by
    rw [h.computeNodes_eq, h.memoryForest_eq]; exact (Op1Config.data hread hdec hver).census
  sizeWindowBound := by
    rw [h.computeNodes_eq, h.memoryForest_eq]
    exact (Op1Config.data hread hdec hver).sizeWindowBound
  q_eq_ringChar := (Op1Config.data hread hdec hver).q_eq_ringChar
  skeletonBounded := by
    rw [h.computeNodes_eq, h.memoryForest_eq]
    exact (Op1Config.data hread hdec hver).skeletonBounded
  combinedBounded := by
    rw [h.computeNodes_eq, h.memoryForest_eq]
    exact (Op1Config.data hread hdec hver).combinedBounded

/-- The generated commitment's committed skeleton is exactly the OP1 committed skeleton. -/
theorem dataOfGenerated_skeleton (G : GenTrace Op1Config.F Op1Config.F) (h : GenTraceOK G)
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    (dataOfGenerated G h hread hdec hver).skeleton = semanticSkeleton := by
  show skeletonOfNodes (mapNTree GenComputeRow.node G.computeNodes)
      (dummyHaltMemTree :: G.memoryNodes.map (mapNTree GenMemoryRow.node)) = semanticSkeleton
  rw [h.computeNodes_eq, h.memoryForest_eq]
  exact Op1Config.skeletonOfNodes_eq

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genTrace_spec
#print axioms Nock.NockVMROM.Thm54.TraceGen.dataOfGenerated
