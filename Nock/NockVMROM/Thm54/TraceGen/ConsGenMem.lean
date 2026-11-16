/-
  Nock/NockVMROM/Thm54/TraceGen/ConsGenMem.lean

  The trace generator's
  `genConsMemForest`, run on the fresh branching ROM program `*[0 [[1 5] [1 6]]] = [5 6]` over
  `F = ZMod 97`, produces — through its `encC` fingerprints and the BFS-threaded LogUp accumulator —
  the exact thirteen-row served memory forest that the verified honest commitment `ConsData`
  consumes: the `.node`-projection of the generated forest is precisely `[ConsConfig.consMemTree]`,
  and its row-projection is precisely `ConsConfig.exec.memoryForest`.

  This is the branching analogue of `Op1GenData.gen_memForest_eq`.  Where OP1 served a single
  request through a five-row reconstruction, the cons forest interleaves THREE
  `read_root`/`verify_child` pairs — the cons request `recCons` read at the root and verified deep
  in the right branch, and the two `OP_1` requests `recL`/`recR` each read and verified in their own
  branches — every pairing matched by the SHARED committed record's fingerprint VALUE, never by a
  committed-line index (memoryless, positionless).  The field-valued LogUp accumulator threads in BFS
  order, `+q` at each read and `-q` at each matching verify, telescoping to zero.

  Everything collapses to the hand-built `ConsConfig`/`ConsData` rows via `Encode.encC_eq`
  (`encC = enc`); the three LogUp poles collapse via `β = γ = 0`.

  * `gen_consMemForest_eq` — `(genConsMemForest seedZ alphaA 5 6).map (mapNTree GenMemoryRow.node)`
    is exactly `[consMemTree]`.

  * `ConsGenTraceOK` / `consGenTrace_spec` — every successful run of the generator on the cons
    program commits exactly the verified honest compute tree AND served memory forest.

  * `consDataOfGenerated` — the honest commitment `Data ConsExecution` whose committed
    compute/memory node trees are the generator's own emitted nodes, transported from `ConsData`.
-/
import Nock.NockVMROM.Thm54.TraceGen.ConsGen
import Nock.NockVMROM.Thm54.TraceGen.ConsData
import Nock.NockVMROM.Thm54.P8Core.ForestExponentWindow

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.TraceGen.ConsConfig
open Nock.NockVMROM.Thm54.TraceGen.ConsSkeleton

/-! ## The three LogUp poles collapse -/

/-- The generated cons-root pole reciprocal is the verified `qCons`. -/
theorem consQCons_eq : consQCons seedZ 5 6 = ConsConfig.qCons := by
  simp only [consQCons, ConsConfig.qCons, MemoryTable.pole, NockVM.formRRow, MemoryTable.recRLC,
    ConsConfig.memInputs, ConsConfig.recCons, ConsConfig.enc, encC_eq,
    consForm, consLeftF, consRightF, formulaNoun, leftFormula, rightFormula, op1Head,
    leftResult, rightResult]
  ring_nf

/-- The generated left-child pole reciprocal is the verified `qL`. -/
theorem consQL_eq : consQL seedZ 5 = ConsConfig.qL := by
  simp only [consQL, ConsConfig.qL, MemoryTable.pole, NockVM.formRRow, MemoryTable.recRLC,
    ConsConfig.memInputs, ConsConfig.recL, ConsConfig.enc, encC_eq,
    consLeftF, leftFormula, op1Head, leftResult]
  ring_nf

/-- The generated right-child pole reciprocal is the verified `qR`. -/
theorem consQR_eq : consQR seedZ 6 = ConsConfig.qR := by
  simp only [consQR, ConsConfig.qR, MemoryTable.pole, NockVM.formRRow, MemoryTable.recRLC,
    ConsConfig.memInputs, ConsConfig.recR, ConsConfig.enc, encC_eq,
    consRightF, rightFormula, op1Head, rightResult]
  ring_nf

/-! ## The three committed records collapse via `encC_eq` -/

theorem consRecCons_eq : consRecCons seedZ alphaA 5 6 = ConsConfig.recCons := by
  simp only [consRecCons, ConsConfig.recCons, ConsConfig.enc, encC_eq,
    consForm, consLeftF, consRightF, formulaNoun, leftFormula, rightFormula, op1Head,
    leftResult, rightResult]

theorem consRecL_eq : consRecL seedZ alphaA 5 = ConsConfig.recL := by
  simp only [consRecL, ConsConfig.recL, ConsConfig.enc, encC_eq,
    consLeftF, leftFormula, op1Head, leftResult]

theorem consRecR_eq : consRecR seedZ alphaA 6 = ConsConfig.recR := by
  simp only [consRecR, ConsConfig.recR, ConsConfig.enc, encC_eq,
    consRightF, rightFormula, op1Head, rightResult]

/-! ## The thirteen served pubs collapse to the verified `ConsConfig` pubs -/

theorem consPReadF_eq : consPReadF seedZ alphaA 5 6 = ConsConfig.pReadFA := by
  simp only [consPReadF, servReadPub, ConsConfig.pReadFA, ConsConfig.readPubA, ConsConfig.readPub,
    ConsConfig.cReadF, ConsConfig.cDecF, consRecCons_eq, consQCons_eq, ConsConfig.enc, encC_eq,
    consForm, consLeftF, consRightF, formulaNoun, leftFormula, rightFormula, op1Head,
    leftResult, rightResult]

theorem consPDecF_eq : consPDecF seedZ alphaA 5 6 = ConsConfig.pDecFA := by
  simp only [consPDecF, servDecPub, ConsConfig.pDecFA, ConsConfig.decPubA, ConsConfig.decPub,
    ConsConfig.cDecF, ConsConfig.cReadL, ConsConfig.cReadR, consQCons_eq, ConsConfig.enc, encC_eq,
    consForm, consLeftF, consRightF, formulaNoun, leftFormula, rightFormula, op1Head,
    leftResult, rightResult]

theorem consPReadL_eq : consPReadL seedZ alphaA 5 6 = ConsConfig.pReadLA := by
  simp only [consPReadL, servReadPub, ConsConfig.pReadLA, ConsConfig.readPubA, ConsConfig.readPub,
    ConsConfig.cReadL, ConsConfig.cDecL, consRecL_eq, consQCons_eq, consQL_eq, ConsConfig.enc,
    encC_eq, consLeftF, leftFormula, op1Head, leftResult]

theorem consPReadR_eq : consPReadR seedZ alphaA 5 6 = ConsConfig.pReadRA := by
  simp only [consPReadR, servReadPub, ConsConfig.pReadRA, ConsConfig.readPubA, ConsConfig.readPub,
    ConsConfig.cReadR, ConsConfig.cVerifyF, consRecR_eq, consQCons_eq, consQL_eq, consQR_eq,
    ConsConfig.enc, encC_eq, consRightF, rightFormula, op1Head, rightResult]

theorem consPDecL_eq : consPDecL seedZ alphaA 5 6 = ConsConfig.pDecLA := by
  simp only [consPDecL, servDecPub, ConsConfig.pDecLA, ConsConfig.decPubA, ConsConfig.decPub,
    ConsConfig.cDecL, ConsConfig.cHaltL1, ConsConfig.cVerifyL, consQCons_eq, consQL_eq, consQR_eq,
    ConsConfig.enc, encC_eq, consLeftF, leftFormula, op1Head, leftResult]

theorem consPVerifyF_eq : consPVerifyF seedZ alphaA 5 6 = ConsConfig.pVerifyFA := by
  simp only [consPVerifyF, servVerifyPub, ConsConfig.pVerifyFA, ConsConfig.verifyPubA,
      ConsConfig.verifyPub,
    ConsConfig.cVerifyF, ConsConfig.cDecR, consRecCons_eq, consQCons_eq, consQL_eq, consQR_eq,
    ConsConfig.enc, encC_eq, consForm, consLeftF, consRightF, formulaNoun, leftFormula,
    rightFormula, op1Head, leftResult, rightResult]

theorem consPHaltL1_eq : consPHaltL1 seedZ 5 6 = ConsConfig.pHaltL1A := by
  simp only [consPHaltL1, servHaltPub, ConsConfig.pHaltL1A, ConsConfig.haltPubA, ConsConfig.haltPub,
    consQL_eq, consQR_eq, ConsConfig.enc, encC_eq, op1Head]

theorem consPVerifyL_eq : consPVerifyL seedZ alphaA 5 6 = ConsConfig.pVerifyLA := by
  simp only [consPVerifyL, servVerifyPub, ConsConfig.pVerifyLA, ConsConfig.verifyPubA,
      ConsConfig.verifyPub,
    ConsConfig.cVerifyL, ConsConfig.cHaltL5, consRecL_eq, consQL_eq, consQR_eq, ConsConfig.enc,
    encC_eq, consLeftF, leftFormula, op1Head, leftResult]

theorem consPDecR_eq : consPDecR seedZ alphaA 5 6 = ConsConfig.pDecRA := by
  simp only [consPDecR, servDecPub, ConsConfig.pDecRA, ConsConfig.decPubA, ConsConfig.decPub,
    ConsConfig.cDecR, ConsConfig.cHaltR1, ConsConfig.cVerifyR, consQR_eq, ConsConfig.enc, encC_eq,
    consRightF, rightFormula, op1Head, rightResult]

theorem consPHaltL5_eq : consPHaltL5 seedZ 5 6 = ConsConfig.pHaltL5A := by
  simp only [consPHaltL5, servHaltPub, ConsConfig.pHaltL5A, ConsConfig.haltPubA, ConsConfig.haltPub,
    consQR_eq, ConsConfig.enc, encC_eq, leftResult]

theorem consPHaltR1_eq : consPHaltR1 seedZ 6 = ConsConfig.pHaltR1A := by
  simp only [consPHaltR1, servHaltPub, ConsConfig.pHaltR1A, ConsConfig.haltPubA, ConsConfig.haltPub,
    consQR_eq, ConsConfig.enc, encC_eq, op1Head]

theorem consPVerifyR_eq : consPVerifyR seedZ alphaA 6 = ConsConfig.pVerifyRA := by
  simp only [consPVerifyR, servVerifyPub, ConsConfig.pVerifyRA, ConsConfig.verifyPubA,
      ConsConfig.verifyPub,
    ConsConfig.cVerifyR, ConsConfig.cHaltR6, consRecR_eq, consQR_eq, ConsConfig.enc, encC_eq,
    consRightF, rightFormula, op1Head, rightResult]

theorem consPHaltR6_eq : consPHaltR6 seedZ 6 = ConsConfig.pHaltR6A := by
  simp only [consPHaltR6, servHaltPub, ConsConfig.pHaltR6A, ConsConfig.haltPubA, ConsConfig.haltPub,
    ConsConfig.enc, encC_eq, rightResult]

/-! ## The generated served forest equals the verified committed forest -/

/-- **The generated served forest's `.node` projection is exactly `[consMemTree]`.**  Each of the
    thirteen rows collapses (via `encC_eq` and the pole/record lemmas) to the verified `ConsConfig`
    row; the memoryless matcher's read/verify pairing is by shared record fingerprint value. -/
theorem gen_consMemForest_eq :
    (genConsMemForest seedZ alphaA 5 6).map (mapNTree GenMemoryRow.node)
      = [ConsConfig.consMemTree] := by
  simp only [genConsMemForest, List.map_cons, List.map_nil, mapNTree, GenMemoryRow.node,
    servRow, consMemRowReadF, consMemRowDecF, consMemRowReadL, consMemRowReadR, consMemRowDecL,
    consMemRowVerifyF, consMemRowHaltL1, consMemRowVerifyL, consMemRowDecR, consMemRowHaltL5,
    consMemRowHaltR1, consMemRowVerifyR, consMemRowHaltR6,
    consMemTree, readFNode, decFNode, readLNode, readRNode, decLNode, verifyFNode, haltL1Node,
    verifyLNode, decRNode, haltL5Node, haltR1Node, verifyRNode, haltR6Node,
    consPReadF_eq, consPDecF_eq, consPReadL_eq, consPReadR_eq, consPDecL_eq, consPVerifyF_eq,
    consPHaltL1_eq, consPVerifyL_eq, consPDecR_eq, consPHaltL5_eq, consPHaltR1_eq,
    consPVerifyR_eq, consPHaltR6_eq]
  rfl

/-- **The generated served forest's row projection is exactly `exec.memoryForest`.**  Composes the
    node equality with the honest commitment's own `memory_rows`. -/
theorem gen_consMemForest_rows :
    (genConsMemForest seedZ alphaA 5 6).map (mapNTree (fun g => (GenMemoryRow.node g).row))
      = [mapNTree MemoryNode.row ConsConfig.consMemTree] := by
  have hcompose :
      (genConsMemForest seedZ alphaA 5 6).map (mapNTree (fun g => (GenMemoryRow.node g).row))
        = ((genConsMemForest seedZ alphaA 5 6).map (mapNTree GenMemoryRow.node)).map
            (mapNTree MemoryNode.row) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro t _
    exact (Nock.NockVMROM.Thm54.ForestExponentWindow.mapNTree_comp
      GenMemoryRow.node MemoryNode.row t).symm
  rw [hcompose, gen_consMemForest_eq]
  rfl

/-! ## The generated compute node tree equals the verified committed compute tree -/

/-- **The generated compute tree's `.node` projection is exactly `consComputeTree`.**  Each rendered
    row collapses (via `Encode.encC_eq`) to the verified `ConsConfig` compute row at its BFS-assigned
    exponent; the branching analogue of `Op1GenData.gen_computeNodes_eq`. -/
theorem gen_consComputeNodes_eq :
    mapNTree GenComputeRow.node
      (renderRows seedZ alphaA (assignExponents
        (.node (skelNode (genSkelCons subjectNoun leftFormula rightFormula leftResult rightResult)
            [⟨formulaNoun, rightFormula, 3, 0⟩])
          [.node (skelNode (genSkelOp1 subjectNoun leftFormula leftResult (.atom 1))
              [⟨leftFormula, leftResult, 3, 0⟩]) [],
           .node (skelNode (genSkelOp1 subjectNoun rightFormula rightResult (.atom 1))
              [⟨rightFormula, rightResult, 3, 0⟩]) []])))
      = ConsConfig.consComputeTree := by
  have hcons : (genSkelCons subjectNoun leftFormula rightFormula leftResult rightResult).state
      = ComputeTable.State.cons := rfl
  have hop1 : (genSkelOp1 subjectNoun leftFormula leftResult (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  have hop1' : (genSkelOp1 subjectNoun rightFormula rightResult (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  simp only [assignExponents, assignTree, assignList, subtreeRecordCount, stampOfAcc, renderRows,
    renderNode, skelNode, hcons, hop1, hop1', Nock.Framework.recordCount, List.map_nil,
    List.map_cons, List.sum_nil, List.sum_cons, mapNTree, Nat.zero_add, Nat.add_zero]
  simp only [GenComputeRow.node, ConsConfig.consComputeTree, ConsConfig.consComputeNode,
    ConsConfig.op1LComputeNode, ConsConfig.op1RComputeNode]
  rw [renderConsRow_eq, renderOp1LRow_eq, renderOp1RRow_eq]
  rfl

/-! ## `ConsGenTraceOK` and the generator specification (compute AND memory) -/

/-- The generator succeeded and committed exactly the verified cons node trees: the branching
    compute tree and the thirteen-row served memory forest that the honest commitment `ConsData`
    consumes.  The branching analogue of `Op1GenData.GenTraceOK`. -/
structure ConsGenTraceOK (G : GenTrace ConsConfig.F ConsConfig.F) : Prop where
  computeNodes_eq : mapNTree GenComputeRow.node G.computeNodes = ConsConfig.consComputeTree
  memoryForest_eq : G.memoryNodes.map (mapNTree GenMemoryRow.node) = [ConsConfig.consMemTree]

/-- **`consGenTrace_spec` (PR-3 memory gate).**  Every successful run of the generator on the cons
    program `*[0 [[1 5] [1 6]]] = [5 6]` commits exactly the verified honest compute tree AND the
    thirteen-row served memory forest. -/
theorem consGenTrace_spec (n : ℕ) (G : GenTrace ConsConfig.F ConsConfig.F)
    (h : genTrace 97 4 seedZ alphaA (n + 2) subjectNoun formulaNoun = .ok G) :
    ConsGenTraceOK G := by
  have hG : G =
      { subject := subjectNoun, formula := formulaNoun, result := resultNoun, fuel := n + 2
        computeNodes := renderRows seedZ alphaA (bfsAssign
          (.node (skelNode (genSkelCons subjectNoun leftFormula rightFormula leftResult rightResult)
              [⟨formulaNoun, rightFormula, 3, 0⟩])
            [.node (skelNode (genSkelOp1 subjectNoun leftFormula leftResult (.atom 1))
                [⟨leftFormula, leftResult, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 subjectNoun rightFormula rightResult (.atom 1))
                [⟨rightFormula, rightResult, 3, 0⟩]) []]))
        memoryNodes := genMemForest seedZ alphaA formulaNoun } :=
    Except.ok.inj h.symm
  subst hG
  refine ⟨?cmp, gen_consMemForest_eq⟩
  rw [bfsAssign_eq_assignExponents_two_leaves]
  exact gen_consComputeNodes_eq

/-! ## The generated honest commitment (the generated analogue of `ConsConfig.ConsData`) -/

/-- **`consDataOfGenerated`.**  The honest commitment `Data ConsExecution` whose committed
    compute/memory node trees are *the generator's own emitted nodes*, with every census / bind /
    specialization obligation transported from the verified `ConsConfig.ConsData` across the two
    node-tree equalities of `ConsGenTraceOK`. -/
noncomputable def consDataOfGenerated (G : GenTrace ConsConfig.F ConsConfig.F)
    (h : ConsGenTraceOK G)
    (hReadF : Vmem ConsConfig.memInputs ConsConfig.pReadF)
    (hDecF : Vmem ConsConfig.memInputs ConsConfig.pDecF)
    (hReadL : Vmem ConsConfig.memInputs ConsConfig.pReadL)
    (hReadR : Vmem ConsConfig.memInputs ConsConfig.pReadR)
    (hDecL : Vmem ConsConfig.memInputs ConsConfig.pDecL)
    (hVerifyF : Vmem ConsConfig.memInputs ConsConfig.pVerifyF)
    (hVerifyL : Vmem ConsConfig.memInputs ConsConfig.pVerifyL)
    (hDecR : Vmem ConsConfig.memInputs ConsConfig.pDecR)
    (hVerifyR : Vmem ConsConfig.memInputs ConsConfig.pVerifyR) :
    Data (ConsConfig.ConsExecution hReadF hDecF hReadL hReadR hDecL
      hVerifyF hVerifyL hDecR hVerifyR) where
  computeNodes := mapNTree GenComputeRow.node G.computeNodes
  memoryNodes := ConsConfig.dummyHaltMemTree :: G.memoryNodes.map (mapNTree GenMemoryRow.node)
  compute_rows := by
    rw [h.computeNodes_eq]
    exact (ConsConfig.ConsData hReadF hDecF hReadL hReadR hDecL
      hVerifyF hVerifyL hDecR hVerifyR).compute_rows
  memory_rows := by
    rw [h.memoryForest_eq]
    exact (ConsConfig.ConsData hReadF hDecF hReadL hReadR hDecL
      hVerifyF hVerifyL hDecR hVerifyR).memory_rows
  computeOK := by
    rw [h.computeNodes_eq]
    exact (ConsConfig.ConsData hReadF hDecF hReadL hReadR hDecL
      hVerifyF hVerifyL hDecR hVerifyR).computeOK
  memoryOK := by
    rw [h.memoryForest_eq]
    exact (ConsConfig.ConsData hReadF hDecF hReadL hReadR hDecL
      hVerifyF hVerifyL hDecR hVerifyR).memoryOK
  root_line_exponent := by
    rw [h.computeNodes_eq]
    exact (ConsConfig.ConsData hReadF hDecF hReadL hReadR hDecL
      hVerifyF hVerifyL hDecR hVerifyR).root_line_exponent
  root_line_origin := by
    rw [h.computeNodes_eq]
    exact (ConsConfig.ConsData hReadF hDecF hReadL hReadR hDecL
      hVerifyF hVerifyL hDecR hVerifyR).root_line_origin
  nounSizeBound := 7
  Λ := 4
  slotSemantics := by
    rw [h.computeNodes_eq, h.memoryForest_eq]
    exact (ConsConfig.ConsData hReadF hDecF hReadL hReadR hDecL
      hVerifyF hVerifyL hDecR hVerifyR).slotSemantics
  recordEquations := by
    rw [h.computeNodes_eq, h.memoryForest_eq]
    exact (ConsConfig.ConsData hReadF hDecF hReadL hReadR hDecL
      hVerifyF hVerifyL hDecR hVerifyR).recordEquations
  census := by
    rw [h.computeNodes_eq, h.memoryForest_eq]
    exact (ConsConfig.ConsData hReadF hDecF hReadL hReadR hDecL
      hVerifyF hVerifyL hDecR hVerifyR).census
  sizeWindowBound := by
    rw [h.computeNodes_eq, h.memoryForest_eq]
    exact (ConsConfig.ConsData hReadF hDecF hReadL hReadR hDecL
      hVerifyF hVerifyL hDecR hVerifyR).sizeWindowBound
  q_eq_ringChar :=
    (ConsConfig.ConsData hReadF hDecF hReadL hReadR hDecL
      hVerifyF hVerifyL hDecR hVerifyR).q_eq_ringChar
  skeletonBounded := by
    rw [h.computeNodes_eq, h.memoryForest_eq]
    exact (ConsConfig.ConsData hReadF hDecF hReadL hReadR hDecL
      hVerifyF hVerifyL hDecR hVerifyR).skeletonBounded
  combinedBounded := by
    rw [h.computeNodes_eq, h.memoryForest_eq]
    exact (ConsConfig.ConsData hReadF hDecF hReadL hReadR hDecL
      hVerifyF hVerifyL hDecR hVerifyR).combinedBounded

/-- The generated cons commitment's committed skeleton is exactly the cons committed skeleton. -/
theorem consDataOfGenerated_skeleton (G : GenTrace ConsConfig.F ConsConfig.F) (h : ConsGenTraceOK G)
    (hReadF : Vmem ConsConfig.memInputs ConsConfig.pReadF)
    (hDecF : Vmem ConsConfig.memInputs ConsConfig.pDecF)
    (hReadL : Vmem ConsConfig.memInputs ConsConfig.pReadL)
    (hReadR : Vmem ConsConfig.memInputs ConsConfig.pReadR)
    (hDecL : Vmem ConsConfig.memInputs ConsConfig.pDecL)
    (hVerifyF : Vmem ConsConfig.memInputs ConsConfig.pVerifyF)
    (hVerifyL : Vmem ConsConfig.memInputs ConsConfig.pVerifyL)
    (hDecR : Vmem ConsConfig.memInputs ConsConfig.pDecR)
    (hVerifyR : Vmem ConsConfig.memInputs ConsConfig.pVerifyR) :
    (consDataOfGenerated G h hReadF hDecF hReadL hReadR hDecL
      hVerifyF hVerifyL hDecR hVerifyR).skeleton = ConsSkeleton.semanticSkeleton := by
  show skeletonOfNodes (mapNTree GenComputeRow.node G.computeNodes)
      (ConsConfig.dummyHaltMemTree :: G.memoryNodes.map (mapNTree GenMemoryRow.node))
      = ConsSkeleton.semanticSkeleton
  rw [h.computeNodes_eq, h.memoryForest_eq]
  exact ConsConfig.skeletonOfNodes_eq

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_consComputeNodes_eq
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_consMemForest_eq
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_consMemForest_rows
#print axioms Nock.NockVMROM.Thm54.TraceGen.consGenTrace_spec
#print axioms Nock.NockVMROM.Thm54.TraceGen.consDataOfGenerated
#print axioms Nock.NockVMROM.Thm54.TraceGen.consDataOfGenerated_skeleton
