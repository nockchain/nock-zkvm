/-
  Nock/NockVMROM/Thm54/TraceGen/Op1GenDataK3.lean

  The K3 mirror of `Op1GenData.lean`: the generator's `genTrace`, run over the computable cubic table
  field `K = K3` on the fresh ROM program `*[0 [1 5]] = 5`, produces — through its three passes plus
  the served-memory pass — the exact honest commitment `HonestCommitment.Data Op1Execution_K3` of the
  re-based OP1 slice.  This is the K3 analogue of `Op1GenData` (which lives over `ZMod 97`), so the
  committed node trees that the released Theorem-5.4 capstone consumes over `K3` are the GENERATOR's
  own output, not the hand-built literal `Op1ConfigK3.data`.

  Three things are proved, all `#print axioms`-clean:

  * `gen_computeNodesK3_eq` / `gen_memForestK3_eq` — the `.node`-projection of the generated compute
    tree over `K3` is exactly `Op1ConfigK3.op1ComputeTree`, and the `.node`-projection of the
    generated served forest is exactly `[Op1ConfigK3.op1MemTree]`.  The generated skeleton/timestamp
    rows are definitionally the verified nodes; the `K3`-columns collapse via `Encode.encC_eq`.

  * `GenTraceOK_K3` / `genTraceK3_spec` — a predicate bundling those two node-tree equalities, proved
    for every successfully generated `G` of the OP1 program over `K3`.

  * `dataOfGeneratedK3` — from `GenTraceOK_K3 G`, the honest commitment `Data Op1Execution_K3` whose
    committed `computeNodes`/`memoryNodes` are *the generator's own nodes* (never `dataOf`), with the
    census / bind / timestamp obligations transported from the verified `Op1ConfigK3.data` across the
    two node-tree equalities.  This is the generated analogue of `Op1ConfigK3.data`.

  The field-generic passes (`renderRows`, `assignExponents`, `genOp1MemForest`, `encC`) are reused
  verbatim from `Gen.lean`; only the row-collapse lemmas are re-derived against `Op1ConfigK3`'s row
  definitions (its `fp = enc`, `computeRow`, `readRow`, …).  No `K3`-specific `simp`/`decide` over
  `Finset (K3 × K3)` is used — every proof is a symbolic reduction that never enumerates `K3`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Gen
import Nock.NockVMROM.Thm54.TraceGen.BFSAssign
import Nock.NockVMROM.Thm54.TraceGen.Op1DataK3

namespace Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3

open Nock Nock.Walk Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton

set_option maxRecDepth 10000

/-! ## The rendered `OP_1` compute row collapses to the verified `Op1ConfigK3` row -/

/-- The generator's `renderOp1Row`, run on the `OP_1` skeleton at exponents `(0, 1, 1)`, reproduces
    the verified `Op1ConfigK3.computeRow`: the `encC` fingerprint columns collapse to the `enc`
    columns (`Encode.encC_eq`), `ln_prev = α⁰ = 1`, `ln = α¹ = α`, and the single record's timestamp
    is `α¹ = α`.  The K3 analogue of `Op1Gen.renderOp1Row_eq`. -/
theorem renderOp1RowK3_eq (z α : K) :
    renderOp1Row z α (stampOfAcc ComputeTable.State.s1 0)
        (genSkelOp1 subjectNoun formulaNoun resultNoun (Noun.atom 1))
      = computeRow z α := by
  simp only [renderOp1Row, genSkelOp1, stampOfAcc, formulaHead, formulaNoun,
    Nock.Framework.recordCount, computeRow, computeInputs, computePub, computeDec,
    requestRecord, fp, encC_eq, pow_zero, pow_one, Nat.zero_add]

/-! ## The served-memory rows collapse to the verified `Op1ConfigK3` rows -/

theorem memReadRowK3_eq (z α : K) :
    (MemoryTable.MState.read_root, memInputs z,
        memReadPub z α (.cell (.atom 1) (.atom 5)) (.atom 5))
      = readRowA z α := by
  simp only [readRowA, readPubA, memReadPub, memInputs, memPoleInv, memReqRec, readRow,
      memoryInputs, readPub,
    seedCell, decomposeCell, requestRecord, reqPoleInv, fp, encC_eq, formulaNoun, headNoun,
    resultNoun]

theorem memDecomposeRowK3_eq (z : K) :
    (MemoryTable.MState.decompose, memInputs z,
        memDecomposePub z (.cell (.atom 1) (.atom 5)) (.atom 1) (.atom 5))
      = decomposeRowA z alphaA := by
  simp only [decomposeRowA, decomposePubA, memDecomposePub, memInputs, memPoleInv, decomposeRow,
      memoryInputs, decomposePub,
    decomposeCell, headCell, verifyCell, reqPoleInv, fp, encC_eq, formulaNoun, headNoun,
    resultNoun]

theorem memHeadRowK3_eq (z : K) :
    (MemoryTable.MState.halt, memInputs z, memHeadPub z (.cell (.atom 1) (.atom 5)) (.atom 1))
      = headRowA z := by
  simp only [headRowA, headPubA, memHeadPub, memInputs, memPoleInv, headRow, memoryInputs,
      headPub, headCell,
    reqPoleInv, fp, encC_eq, formulaNoun, headNoun, resultNoun]

theorem memVerifyRowK3_eq (z α : K) :
    (MemoryTable.MState.verify_child, memInputs z,
        memVerifyPub z α (.cell (.atom 1) (.atom 5)) (.atom 5))
      = verifyRowA z α := by
  simp only [verifyRowA, verifyPubA, memVerifyPub, memInputs, memPoleInv, memReqRec, verifyRow,
      memoryInputs, verifyPub,
    verifyCell, tailCell, requestRecord, reqPoleInv, fp, encC_eq, formulaNoun, headNoun,
    resultNoun]

theorem memTailRowK3_eq (z : K) :
    (MemoryTable.MState.halt, memInputs z, memTailPub z (.atom 5)) = tailRowA z := by
  simp only [tailRowA, tailPubA,
    memTailPub, memInputs, tailRow, memoryInputs, tailPub, tailCell, fp, encC_eq,
    resultNoun]

/-! ## The generated node trees are the verified committed node trees over `K3` -/

/-- The generated compute tree's `.node` projection over `K3` is exactly `op1ComputeTree`. -/
theorem gen_computeNodesK3_eq :
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
  rw [renderOp1RowK3_eq]
  rfl

/-- The generated served forest's `.node` projection over `K3` is exactly `[op1MemTree]`. -/
theorem gen_memForestK3_eq :
    (genOp1MemForest seedZ alphaA 5).map (mapNTree GenMemoryRow.node) = [op1MemTree] := by
  simp only [genOp1MemForest, List.map_cons, List.map_nil, mapNTree, GenMemoryRow.node,
    op1MemTree, op1ReadNode, op1DecomposeNode, op1HeadNode, op1VerifyNode, op1TailNode]
  rw [memReadRowK3_eq, memDecomposeRowK3_eq, memHeadRowK3_eq, memVerifyRowK3_eq, memTailRowK3_eq]
  rfl

/-! ## `GenTraceOK_K3` and the generator specification over `K3` -/

/-- The generator succeeded and committed exactly the verified OP1/K3 node trees: the compute tree
    and the served memory forest that the honest commitment `Op1ConfigK3.data` consumes. -/
structure GenTraceOK_K3 (G : GenTrace K K) : Prop where
  computeNodes_eq : mapNTree GenComputeRow.node G.computeNodes = op1ComputeTree
  memoryForest_eq : G.memoryNodes.map (mapNTree GenMemoryRow.node) = [op1MemTree]

/-- A successful OP1 generator run over `K3` exists (the generator is deterministic, so this reduces
    by `rfl`) — the concrete witness `dataOfGeneratedK3` routes through. -/
theorem genTrace_op1_existsK3 (n : ℕ) :
    ∃ G : GenTrace K K,
      genTrace 97 3 seedZ alphaA (n + 1) subjectNoun formulaNoun = .ok G :=
  ⟨_, rfl⟩

/-- **`genTraceK3_spec`.**  Every successful run of the generator on the OP1 program over `K3`
    commits exactly the verified honest node trees. -/
theorem genTraceK3_spec (n : ℕ) (G : GenTrace K K)
    (h : genTrace 97 3 seedZ alphaA (n + 1) subjectNoun formulaNoun = .ok G) :
    GenTraceOK_K3 G := by
  have hG : G =
      { subject := subjectNoun, formula := formulaNoun, result := resultNoun, fuel := n + 1
        computeNodes := renderRows seedZ alphaA (bfsAssign
          (.node (skelNode (genSkelOp1 subjectNoun formulaNoun resultNoun (.atom 1))
            [⟨formulaNoun, resultNoun, 3, 0⟩]) []))
        memoryNodes := genOp1MemForest seedZ alphaA 5 } :=
    Except.ok.inj h.symm
  subst hG
  refine ⟨?cmp, gen_memForestK3_eq⟩
  rw [bfsAssign_node_nil_eq_assignExponents]
  exact gen_computeNodesK3_eq

/-! ## The generated honest commitment over `K3` (the generated analogue of `Op1ConfigK3.data`) -/

/-- **`dataOfGeneratedK3`.**  The honest commitment of the OP1/K3 slice whose committed
    compute/memory node trees are *the generator's own emitted nodes*, with every census / bind /
    specialization obligation transported from the verified `Op1ConfigK3.data` across the two
    node-tree equalities of `GenTraceOK_K3`. -/
noncomputable def dataOfGeneratedK3 (G : GenTrace K K) (h : GenTraceOK_K3 G)
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    Data (Op1Execution_K3 hread hdec hver) where
  computeNodes := mapNTree GenComputeRow.node G.computeNodes
  memoryNodes := dummyHaltMemTree :: G.memoryNodes.map (mapNTree GenMemoryRow.node)
  compute_rows := by rw [h.computeNodes_eq]; exact (data hread hdec hver).compute_rows
  memory_rows := by rw [h.memoryForest_eq]; exact (data hread hdec hver).memory_rows
  computeOK := by rw [h.computeNodes_eq]; exact (data hread hdec hver).computeOK
  memoryOK := by rw [h.memoryForest_eq]; exact (data hread hdec hver).memoryOK
  root_line_exponent := by rw [h.computeNodes_eq]; exact (data hread hdec hver).root_line_exponent
  root_line_origin := by rw [h.computeNodes_eq]; exact (data hread hdec hver).root_line_origin
  nounSizeBound := 5
  Λ := 3
  slotSemantics := by
    rw [h.computeNodes_eq, h.memoryForest_eq]; exact (data hread hdec hver).slotSemantics
  recordEquations := by
    rw [h.computeNodes_eq, h.memoryForest_eq]; exact (data hread hdec hver).recordEquations
  census := by rw [h.computeNodes_eq, h.memoryForest_eq]; exact (data hread hdec hver).census
  sizeWindowBound := by
    rw [h.computeNodes_eq, h.memoryForest_eq]; exact (data hread hdec hver).sizeWindowBound
  q_eq_ringChar := (data hread hdec hver).q_eq_ringChar
  skeletonBounded := by
    rw [h.computeNodes_eq, h.memoryForest_eq]; exact (data hread hdec hver).skeletonBounded
  combinedBounded := by
    rw [h.computeNodes_eq, h.memoryForest_eq]; exact (data hread hdec hver).combinedBounded

/-- A concrete successful OP1 generator run over `K3`. -/
noncomputable def op1GenTraceK3 : GenTrace K K := (genTrace_op1_existsK3 0).choose

/-- The concrete OP1/K3 run commits exactly the verified honest OP1 node trees. -/
theorem op1GenTraceK3OK : GenTraceOK_K3 op1GenTraceK3 :=
  genTraceK3_spec 0 op1GenTraceK3 (genTrace_op1_existsK3 0).choose_spec

/-- **The generated OP1/K3 honest commitment** — `dataOfGeneratedK3` applied to the generator's own
    output, i.e. the `Data (Op1Execution_K3 …)` whose committed node trees are produced end-to-end by
    the executable generator on the fresh program `*[0 [1 5]] = 5` over the cubic field `K3`. -/
noncomputable def dataK3Generated
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    Data (Op1Execution_K3 hread hdec hver) :=
  dataOfGeneratedK3 op1GenTraceK3 op1GenTraceK3OK hread hdec hver

/-- The generated commitment's committed skeleton over `K3` is exactly the OP1 committed skeleton. -/
theorem dataOfGeneratedK3_skeleton (G : GenTrace K K) (h : GenTraceOK_K3 G)
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    (dataOfGeneratedK3 G h hread hdec hver).skeleton = semanticSkeleton := by
  show skeletonOfNodes (mapNTree GenComputeRow.node G.computeNodes)
      (dummyHaltMemTree :: G.memoryNodes.map (mapNTree GenMemoryRow.node)) = semanticSkeleton
  rw [h.computeNodes_eq, h.memoryForest_eq]
  exact skeletonOfNodes_eq

end Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3.genTraceK3_spec
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3.dataOfGeneratedK3
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3.dataK3Generated
