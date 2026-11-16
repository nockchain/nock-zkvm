import Nock.NockVMROM.Thm54.ServedForestModule
import Nock.NockVMROM.Thm54.BuildableChips

/-!
# `ServedForestExecution` — the generic served-forest execution / semantic / buildable chain

This module continues the generic port begun in `ServedForestModule`: it lifts the
*opcode-invariant* reassembly chain of `MultiRootServedFixture` (the `cfgS` / `execS`,
`semanticDataS` / `servedMemoryTraceS`, and `multiRootExecution` blocks) to be generic over a
`ServedForestExec` — a `ServedForestParams` bundled with the per-opcode **compute parent-row seam**
(the `.s4`/`.s3` produced-result gate row and its acceptance/well-formedness data).

Root `B` and the inner shared child rows are opcode-invariant and are reused verbatim from
`MultiRootServedFixture`; the parent-touching root-`A` objects come from `ServedForestModule`
(`rootATreeG`, `aReadOuter_acceptsG`, …).

## What lands here (all additive, kernel-clean)

Generic over `P : ServedForestExec`:

* **Stage 4** — the generic config/execution `execSG` over `cfgS`, its BFS row order
  `execution_rowsSG`, the derived request/response IO, their `Nodup`, and the row-indexed
  `pubAt` / well-formedness / chained-accumulator facts.

* **Stage 5a** — the generic compute-side semantic core: the semantic preimage
  `semanticPreimageSG`, the chained/traversable/noun-realized `languageSG`, and the
  `semanticDataSG` bundle (`SemanticTrace.ExactExecutionSemanticData`).

* **Stage 5b** — the generic served memory trace `servedMemoryTraceSG`
  (`ServedMemoryTrace.ExactServedMemoryTrace`): the two serviced root traces `rootTraceAG` /
  `rootTraceBG`, their head-generic services (`serviceA1G`/`serviceA2G`/`serviceBG`), the exact
  axis trees, and the cross-root timestamp-power multiset.  Root `A`'s subject `P.parentFormula`
  and head `P.parentHead` are opened to their `cell`/`atom` shapes via `P.hcons` / `P.hhead` at the
  `ServiceWalk`, so the traversal is head-generic.

The compute parent-row objects are supplied as interface fields (`parentAccepts`, `parentWf`,
`parentActiveReq`, `parentLineHandoff`, `parentRowData`, `parentRowNoun`, `semParentRec`,
`semParentBridge`, `parentRowFcomp`, …), discharged per-opcode when the module is instantiated at
`op4Params` / `op3Params`.
-/

namespace Nock.NockVMROM.Thm54.ServedForestModule

open scoped Classical
open Nock Nock.Noun Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.ServedForest
open Nock.NockVMROM.Thm54.BuildableChips

noncomputable section

local instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-! ## The extended served-forest interface: params + compute parent-row seam -/

/-- A `ServedForestParams` bundled with the per-opcode **compute parent-row seam**: the produced
result gate row's public/dec columns, its `Vcomp` acceptance and `WF`, its single emitted request
record (the parent memory record), and the compute-line handoff to the served `OP_0` child. -/
structure ServedForestExec extends ServedForestParams where
  /-- The parent compute row's public columns (its `.state` field is the parent gate state
  `.s4` for OP₄, `.s3` for OP₃, and is used as the BFS label state of the parent row). -/
  parentPub : ComputeTable.Pub K97cubic
  /-- The parent compute row's decomposition columns. -/
  parentDec : ComputeTable.Dec K97cubic
  /-- The parent row is an accepted compute row. -/
  parentAccepts : Vcomp servedInputs parentPub parentDec
  /-- The parent row is table-well-formed. -/
  parentWf : ComputeTable.WF servedInputs parentPub
  /-- The parent row emits exactly the parent memory record as its one active request
  (opcode-invariant: both `.s3` and `.s4` request a single `mr1`). -/
  parentActiveReq :
    NockVM.activeRequestRecords parentPub = [parentRecordG toServedForestParams]
  /-- The compute-line handoff: the parent's `ln` is the served row's `ln_prev`. -/
  parentLineHandoff : parentPub.ln = servedPub.ln_prev
  /-- The compute line's origin: the parent (first) row's `ln_prev` is `1` — `Data.root_line_origin` for this fixture family (W6.1 stage 2A). -/
  parentLineOrigin : parentPub.ln_prev = 1
  /-- The parent compute row's full row-level semantic data (opcode-specific: OP₄ carries an
  increment window, OP₃ a `wut` gate).  Its `needs.served` list is empty — the parent performs no
  slot lookup. -/
  parentRowData :
    SemanticTrace.ComputeRowSemanticData 97 3 (parentPub.state, (servedInputs, parentPub, parentDec))
  /-- The parent needs no served slot lookup. -/
  parentRowServed : parentRowData.needs.served = []
  /-- Bounded-noun realization of the parent public row (its subject / formula / evaluation and
  sf-slots are opcode-specific). -/
  parentRowNoun :
    ComputePublicRowNounRealization 97
      (computePublicLabel (parentPub.state, (servedInputs, parentPub, parentDec)))
  /-- The parent's semantic record preimage (an `nmr` record). -/
  semParentRec : (nmrMEF F97 K97cubic).Rec
  /-- The parent semantic record's timestamp exponent is `1` (`< 4`, the certified window). -/
  semParentTs : semParentRec.2.2 = 1
  /-- The parent semantic record bridges to the encoded parent memory record. -/
  semParentBridge :
    bridge F97 K97cubic cfgS.challenges.α cfgS.challenges.lam semParentRec =
      NockVM.encRecFormR (parentRecordG toServedForestParams) MemoryTable.formRDefault
  /-- The parent compute row is an accepted nonterminal `Fcomp` row whose single active child is
  the served `OP_0` row (via the shared fanout `parentOutS`). -/
  parentRowFcomp :
    ComputeTable.Fcomp (parentPub.state, (servedInputs, parentPub, parentDec)) parentOutS
  /-- The parent gate state is genuinely nonterminal with a single active child. -/
  parentFanout : ComputeTable.fanoutComp parentPub.state = 1

variable (P : ServedForestExec)

/-- The generic parent compute row.  The BFS label state is the pub's own `.state`, so the
`ComputeRowAccepted` label-agreement obligation holds definitionally. -/
def parentRowG : ComputeTable.State × ComputeTable.DTcomp K97cubic :=
  (P.parentPub.state, (servedInputs, P.parentPub, P.parentDec))

/-- The generic two-row nonterminal compute tree: the parent gate row with the served `OP_0`
row as its one child. -/
def computeTreeSG : NTree (ComputeTable.State × ComputeTable.DTcomp K97cubic) :=
  .node (parentRowG P) [.node servedRow []]

/-! ## Stage 4. The exact configuration and execution (generic).

`cfgS` is opcode-invariant and is reused verbatim; the execution threads the generic compute tree
and the generic root-`A` memory tree from `ServedForestModule`. -/

/-- Fifteen memory rows (dummy halt + two serviced roots), two nonterminal compute rows. -/
def execSG : ExactExecution cfgS where
  computeTree := computeTreeSG P
  memoryForest := [dummyHaltTreeS, rootATreeG P.toServedForestParams, rootBTree]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTreeSG, bfsForest, NTree.size, totalSize, cfgS]
  memory_bfs_length := by
    norm_num [dummyHaltTreeS, rootATreeG, aDecomposeOuterTreeG, aHeadHaltTreeG, aReadInnerTreeG,
      aVerifyOuterTreeG, aDecomposeInnerTree, aInnerHeadHaltTree, aVerifyInnerTree,
      aTailHaltTree, rootBTree, bDecomposeTree, bVerifyTree, bResultHaltTree, bTailHaltTree,
      bfsForest, NTree.size, totalSize, cfgS]

/-- The aggregate BFS row order genuinely interleaves the two serviced roots. -/
theorem execution_rowsSG :
    (execSG P).computeRows = [parentRowG P, servedRow] ∧
      (execSG P).memoryRows =
        [dummyHaltLabelS, aReadOuterLabelG P.toServedForestParams, bReadLabel,
          aDecomposeOuterLabelG P.toServedForestParams, bDecomposeLabel,
          aHeadHaltLabelG P.toServedForestParams, aReadInnerLabel, bVerifyLabel, bTailHaltLabel,
          aVerifyOuterLabelG P.toServedForestParams, bResultHaltLabel, aDecomposeInnerLabel,
          aInnerHeadHaltLabel, aVerifyInnerLabel, aTailHaltLabel] := by
  constructor <;>
    norm_num [ExactExecution.computeRows, ExactExecution.memoryRows, execSG, computeTreeSG,
      dummyHaltTreeS, rootATreeG, aDecomposeOuterTreeG, aHeadHaltTreeG, aReadInnerTreeG, aVerifyOuterTreeG,
      aDecomposeInnerTree, aInnerHeadHaltTree, aVerifyInnerTree, aTailHaltTree,
      rootBTree, bDecomposeTree, bVerifyTree, bResultHaltTree, bTailHaltTree,
      bfsForest, NTree.size, totalSize]

/-! ### The a-bearing view of `execSG` (28th: the paper; the active rows hold the
address, and `execSG` is their Form R row encode, as for `MultiRootServedFixture.execSA`). -/

@[simp] def aReadOuterPubGA (Q : ServedForestParams) : MemoryTable.Pub K97cubic :=
  { aReadOuterPubG Q with mem := parentRecordG Q, cprime? := none }
@[simp] def aVerifyOuterPubGA (Q : ServedForestParams) : MemoryTable.Pub K97cubic :=
  { aVerifyOuterPubG Q with mem := parentRecordG Q, cprime? := none }

abbrev aReadOuterLabelGA (Q : ServedForestParams) := memLabelS .read_root (aReadOuterPubGA Q)
abbrev aVerifyOuterLabelGA (Q : ServedForestParams) :=
  memLabelS .verify_child (aVerifyOuterPubGA Q)

def aVerifyOuterTreeGA (Q : ServedForestParams) : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node (aVerifyOuterLabelGA Q) [aDecomposeInnerTreeA]
def aReadInnerTreeGA (Q : ServedForestParams) : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node aReadInnerLabelA [aVerifyOuterTreeGA Q]
def aDecomposeOuterTreeGA (Q : ServedForestParams) :
    NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node (aDecomposeOuterLabelG Q) [aHeadHaltTreeG Q, aReadInnerTreeGA Q]
def rootATreeGA (Q : ServedForestParams) : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node (aReadOuterLabelGA Q) [aDecomposeOuterTreeGA Q]

/-- The a-bearing view of `execSG`: the served memory trace and axis accounting live here. -/
def execSGA : ExactExecution cfgS where
  computeTree := computeTreeSG P
  memoryForest := [dummyHaltTreeS, rootATreeGA P.toServedForestParams, rootBTreeA]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTreeSG, bfsForest, NTree.size, totalSize, cfgS]
  memory_bfs_length := by
    norm_num [dummyHaltTreeS, rootATreeGA, aDecomposeOuterTreeGA, aHeadHaltTreeG,
      aReadInnerTreeGA, aVerifyOuterTreeGA, aDecomposeInnerTreeA, aInnerHeadHaltTree,
      aVerifyInnerTreeA, aTailHaltTree, rootBTreeA, bDecomposeTreeA, bVerifyTreeA,
      bResultHaltTree, bTailHaltTree, bfsForest, NTree.size, totalSize, cfgS]

/-- `execSG` is the Form R row encode of `execSGA` (`BuildableNockExecution.exec_encode`). -/
theorem execSG_encode : execSG P = (execSGA P).encodeMem :=
  TraceGen.RowEncode.eq_encodeMem_of rfl (by
    simp [execSG, execSGA, mapNTree, dummyHaltTreeS, rootATreeG, rootATreeGA,
      aDecomposeOuterTreeG, aDecomposeOuterTreeGA, aHeadHaltTreeG, aReadInnerTreeG,
      aReadInnerTreeGA, aVerifyOuterTreeG, aVerifyOuterTreeGA, aDecomposeInnerTree,
      aDecomposeInnerTreeA, aInnerHeadHaltTree, aVerifyInnerTree, aVerifyInnerTreeA,
      aTailHaltTree, rootBTree, rootBTreeA, bDecomposeTree, bDecomposeTreeA, bVerifyTree,
      bVerifyTreeA, bResultHaltTree, bTailHaltTree, memLabelS, dummyHaltPubS, aReadOuterPubG,
      bReadPub, aDecomposeOuterPubG, bDecomposePub, aHeadHaltPubG, aReadInnerPub, bVerifyPub,
      bTailHaltPub, aVerifyOuterPubG, bResultHaltPub, aDecomposeInnerPub, aInnerHeadHaltPub,
      aVerifyInnerPub, aTailHaltPub])

/-! ## Derived IO: three requests, three responses, genuinely permuted -/

theorem derived_requestsSG :
    (execSG P).derivedRequestIO =
      [NockVM.encRecFormR (parentRecordG P.toServedForestParams) MemoryTable.formRDefault,
        NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault,
        NockVM.encRecFormR servedRecord MemoryTable.formRDefault] := by
  rw [ExactExecution.derivedRequestIO_eq_computeRows, (execution_rowsSG P).1]
  have hp : NockVM.activeRequestRecords (parentRowG P).2.2.1 =
      [parentRecordG P.toServedForestParams] := P.parentActiveReq
  have hs : NockVM.activeRequestRecords servedRow.2.2.1 = [servedFormulaRecord, servedRecord] := by
    simp [NockVM.activeRequestRecords, servedRow, servedPub]
  simp [List.flatMap_cons, List.flatMap_nil, hp, hs]

theorem derived_responsesSG :
    (execSG P).derivedResponseIO =
      [NockVM.encRecFormR (parentRecordG P.toServedForestParams) MemoryTable.formRDefault,
        NockVM.encRecFormR servedRecord MemoryTable.formRDefault,
        NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault] := by
  rw [ExactExecution.derivedResponseIO_eq_memoryRows, (execution_rowsSG P).2]
  rfl

theorem rawRequestsSG :
    (execSG P).rawRequests =
      [parentRecordG P.toServedForestParams, servedFormulaRecord, servedRecord] := by
  rw [ExactExecution.rawRequests_eq_computeRows, (execution_rowsSG P).1]
  have hp : NockVM.activeRequestRecords (parentRowG P).2.2.1 =
      [parentRecordG P.toServedForestParams] := P.parentActiveReq
  have hs : NockVM.activeRequestRecords servedRow.2.2.1 = [servedFormulaRecord, servedRecord] := by
    simp [NockVM.activeRequestRecords, servedRow, servedPub]
  simp [List.flatMap_cons, List.flatMap_nil, hp, hs]

/-- The a-bearing view has the same compute rows, hence the same raw requests. -/
theorem rawRequestsSGA :
    (execSGA P).rawRequests =
      [parentRecordG P.toServedForestParams, servedFormulaRecord, servedRecord] := by
  rw [show (execSGA P).rawRequests = (execSG P).rawRequests from rfl, rawRequestsSG]

theorem requestsSG_nodup : (execSG P).derivedRequestIO.Nodup := by
  rw [derived_requestsSG]
  have h12 : NockVM.encRecFormR (parentRecordG P.toServedForestParams) MemoryTable.formRDefault ≠
      NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_parentRecordG, ts_servedFormulaRecord]; exact ts_4_ne_16)
  have h13 : NockVM.encRecFormR (parentRecordG P.toServedForestParams) MemoryTable.formRDefault
      ≠ NockVM.encRecFormR servedRecord MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_parentRecordG, ts_servedRecord]; exact ts_4_ne_64)
  have h23 : NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault
      ≠ NockVM.encRecFormR servedRecord MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_servedFormulaRecord, ts_servedRecord]; exact ts_16_ne_64)
  simp [h12, h13, h23]

theorem responsesSG_nodup : (execSG P).derivedResponseIO.Nodup := by
  rw [derived_responsesSG]
  have h12 : NockVM.encRecFormR (parentRecordG P.toServedForestParams) MemoryTable.formRDefault
      ≠ NockVM.encRecFormR servedRecord MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_parentRecordG, ts_servedRecord]; exact ts_4_ne_64)
  have h13 : NockVM.encRecFormR (parentRecordG P.toServedForestParams) MemoryTable.formRDefault ≠
      NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_parentRecordG, ts_servedFormulaRecord]; exact ts_4_ne_16)
  have h23 : NockVM.encRecFormR servedRecord MemoryTable.formRDefault ≠ NockVM.encRecFormR
      servedFormulaRecord MemoryTable.formRDefault :=
    fun h => (encRec_ne_of_ts_ne
      (r := servedFormulaRecord) (s := servedRecord)
      (by rw [ts_servedFormulaRecord, ts_servedRecord]; exact ts_16_ne_64)) h.symm
  simp [h12, h13, h23]

/-! ## Row acceptance, `pubAt`, well-formedness, and the chained boundaries -/

theorem compute_rows_acceptedSG : (execSG P).ComputeRowsAccepted := by
  rw [ExactExecution.computeRowsAccepted_iff, (execution_rowsSG P).1]
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl
  · exact ⟨rfl, rfl, P.parentAccepts⟩
  · exact ⟨rfl, rfl, served_accepts⟩

theorem memory_rows_acceptedSG : (execSG P).MemoryRowsAccepted := by
  rw [ExactExecution.memoryRowsAccepted_iff, (execution_rowsSG P).2]
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl, dummyHaltS_accepts, rfl⟩
  · exact ⟨rfl, rfl, aReadOuter_acceptsG _, rfl⟩
  · exact ⟨rfl, rfl, bRead_accepts, rfl⟩
  · exact ⟨rfl, rfl, aDecomposeOuter_acceptsG _, rfl⟩
  · exact ⟨rfl, rfl, bDecompose_accepts, rfl⟩
  · exact ⟨rfl, rfl, aHeadHalt_acceptsG _, rfl⟩
  · exact ⟨rfl, rfl, aReadInner_accepts, rfl⟩
  · exact ⟨rfl, rfl, bVerify_accepts, rfl⟩
  · exact ⟨rfl, rfl, bTailHalt_accepts, rfl⟩
  · exact ⟨rfl, rfl, aVerifyOuter_acceptsG _, rfl⟩
  · exact ⟨rfl, rfl, bResultHalt_accepts, rfl⟩
  · exact ⟨rfl, rfl, aDecomposeInner_accepts, rfl⟩
  · exact ⟨rfl, rfl, aInnerHeadHalt_accepts, rfl⟩
  · exact ⟨rfl, rfl, aVerifyInner_accepts, rfl⟩
  · exact ⟨rfl, rfl, aTailHalt_accepts, rfl⟩

theorem computePubAtSG_zero : (execSG P).computePubAt ⟨0, by norm_num [cfgS]⟩ = P.parentPub := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt,
    (execution_rowsSG P).1, cfgS, parentRowG]

theorem computePubAtSG_one : (execSG P).computePubAt ⟨1, by norm_num [cfgS]⟩ = servedPub := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt,
    (execution_rowsSG P).1, cfgS, servedRow]

theorem compute_wf_allSG :
    ∀ i, ComputeTable.WF cfgS.challenges.computeInputs ((execSG P).computePubAt i) := by
  rw [challenge_alignmentS.1]
  intro i
  fin_cases i
  · rw [computePubAtSG_zero]; exact P.parentWf
  · rw [computePubAtSG_one]; exact served_wf

theorem memoryPubAtSG_0 :
    (execSG P).memoryPubAt ⟨0, by norm_num [cfgS]⟩ = dummyHaltPubS := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rowsSG P).2,
    cfgS, memLabelS]

theorem memoryPubAtSG_1 :
    (execSG P).memoryPubAt ⟨1, by norm_num [cfgS]⟩ = aReadOuterPubG P.toServedForestParams := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rowsSG P).2,
    cfgS, memLabelS]

theorem memoryPubAtSG_2 : (execSG P).memoryPubAt ⟨2, by norm_num [cfgS]⟩ = bReadPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rowsSG P).2,
    cfgS, memLabelS]

theorem memoryPubAtSG_3 :
    (execSG P).memoryPubAt ⟨3, by norm_num [cfgS]⟩ =
      aDecomposeOuterPubG P.toServedForestParams := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rowsSG P).2,
    cfgS, memLabelS]

theorem memoryPubAtSG_4 : (execSG P).memoryPubAt ⟨4, by norm_num [cfgS]⟩ = bDecomposePub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rowsSG P).2,
    cfgS, memLabelS]

theorem memoryPubAtSG_5 :
    (execSG P).memoryPubAt ⟨5, by norm_num [cfgS]⟩ = aHeadHaltPubG P.toServedForestParams := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rowsSG P).2,
    cfgS, memLabelS]

theorem memoryPubAtSG_6 : (execSG P).memoryPubAt ⟨6, by norm_num [cfgS]⟩ = aReadInnerPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rowsSG P).2,
    cfgS, memLabelS]

theorem memoryPubAtSG_7 : (execSG P).memoryPubAt ⟨7, by norm_num [cfgS]⟩ = bVerifyPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rowsSG P).2,
    cfgS, memLabelS]

theorem memoryPubAtSG_8 : (execSG P).memoryPubAt ⟨8, by norm_num [cfgS]⟩ = bTailHaltPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rowsSG P).2,
    cfgS, memLabelS]

theorem memoryPubAtSG_9 :
    (execSG P).memoryPubAt ⟨9, by norm_num [cfgS]⟩ = aVerifyOuterPubG P.toServedForestParams := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rowsSG P).2,
    cfgS, memLabelS]

theorem memoryPubAtSG_10 : (execSG P).memoryPubAt ⟨10, by norm_num [cfgS]⟩ = bResultHaltPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rowsSG P).2,
    cfgS, memLabelS]

theorem memoryPubAtSG_11 :
    (execSG P).memoryPubAt ⟨11, by norm_num [cfgS]⟩ = aDecomposeInnerPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rowsSG P).2,
    cfgS, memLabelS]

theorem memoryPubAtSG_12 :
    (execSG P).memoryPubAt ⟨12, by norm_num [cfgS]⟩ = aInnerHeadHaltPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rowsSG P).2,
    cfgS, memLabelS]

theorem memoryPubAtSG_13 : (execSG P).memoryPubAt ⟨13, by norm_num [cfgS]⟩ = aVerifyInnerPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rowsSG P).2,
    cfgS, memLabelS]

theorem memoryPubAtSG_14 : (execSG P).memoryPubAt ⟨14, by norm_num [cfgS]⟩ = aTailHaltPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rowsSG P).2,
    cfgS, memLabelS]

theorem memory_wf_allSG :
    ∀ i, MemoryTable.WF cfgS.challenges.memoryInputs ((execSG P).memoryPubAt i) := by
  rw [challenge_alignmentS.2]
  intro i
  fin_cases i
  · rw [memoryPubAtSG_0]; exact dummyHaltS_wf
  · rw [memoryPubAtSG_1]; exact aReadOuter_wfG _
  · rw [memoryPubAtSG_2]; exact bRead_wf
  · rw [memoryPubAtSG_3]; exact aDecomposeOuter_wfG _
  · rw [memoryPubAtSG_4]; exact bDecompose_wf
  · rw [memoryPubAtSG_5]; exact aHeadHalt_wfG _
  · rw [memoryPubAtSG_6]; exact aReadInner_wf
  · rw [memoryPubAtSG_7]; exact bVerify_wf
  · rw [memoryPubAtSG_8]; exact bTailHalt_wf
  · rw [memoryPubAtSG_9]; exact aVerifyOuter_wfG _
  · rw [memoryPubAtSG_10]; exact bResultHalt_wf
  · rw [memoryPubAtSG_11]; exact aDecomposeInner_wf
  · rw [memoryPubAtSG_12]; exact aInnerHeadHalt_wf
  · rw [memoryPubAtSG_13]; exact aVerifyInner_wf
  · rw [memoryPubAtSG_14]; exact aTailHalt_wf

theorem compute_chainSG :
    ∀ i : Fin cfgS.compRows, ∀ _ : (i : ℕ) + 1 < cfgS.compRows,
      ((execSG P).computePubAt i).ln =
        ((execSG P).computePubAt ⟨(i : ℕ) + 1, by omega⟩).ln_prev := by
  intro i hi
  fin_cases i
  · rw [computePubAtSG_zero, computePubAtSG_one]
    exact P.parentLineHandoff
  · simp [cfgS] at hi

theorem memory_chainSG :
    ∀ i : Fin cfgS.memRows, ∀ _ : (i : ℕ) + 1 < cfgS.memRows,
      ((execSG P).memoryPubAt i).icur =
        ((execSG P).memoryPubAt ⟨(i : ℕ) + 1, by omega⟩).ipre := by
  intro i hi
  fin_cases i
  · rw [memoryPubAtSG_0, memoryPubAtSG_1]; rfl
  · rw [memoryPubAtSG_1, memoryPubAtSG_2]; rfl
  · rw [memoryPubAtSG_2, memoryPubAtSG_3]; rfl
  · rw [memoryPubAtSG_3, memoryPubAtSG_4]; rfl
  · rw [memoryPubAtSG_4, memoryPubAtSG_5]; rfl
  · rw [memoryPubAtSG_5, memoryPubAtSG_6]; rfl
  · rw [memoryPubAtSG_6, memoryPubAtSG_7]; rfl
  · rw [memoryPubAtSG_7, memoryPubAtSG_8]; rfl
  · rw [memoryPubAtSG_8, memoryPubAtSG_9]; rfl
  · rw [memoryPubAtSG_9, memoryPubAtSG_10]; rfl
  · rw [memoryPubAtSG_10, memoryPubAtSG_11]; rfl
  · rw [memoryPubAtSG_11, memoryPubAtSG_12]; rfl
  · rw [memoryPubAtSG_12, memoryPubAtSG_13]; rfl
  · rw [memoryPubAtSG_13, memoryPubAtSG_14]; rfl
  · simp [cfgS] at hi

/-! ## Stage 5. The generic semantic CORE.

The shared inner semantic records `semInnerRec`/`semServedRec` and their bridges, and the shared
child compute-row realization `servedRow_nounRealization`, are opcode-invariant and reused verbatim.
The parent-touching pieces come from the interface fields (`semParentRec`/`semParentBridge`,
`parentRowData`, `parentRowNoun`, `parentRowFcomp`). -/

/-- The generic compute tree is an accepted `RVT` (the parent `Fcomp` is `P.parentRowFcomp`; the
served child is the shared `servedRow_accepts`). -/
theorem computeTreeSG_rvt : RVT (ComputeTable.Fcomp (K := K97cubic)) (computeTreeSG P) := by
  unfold computeTreeSG RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 3 =>
        (NTree.node (parentRowG P) [.node servedRow []]).childLabel i) = parentOutS by
      funext i; fin_cases i <;> rfl]
    exact P.parentRowFcomp
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    unfold RVT
    exact ⟨servedRow_accepts, by simp, ⟨fun _ => servedRow_accepts, fun _ => rfl⟩⟩
  · refine ⟨fun h => ?_, fun hF => ?_⟩
    · simp [NTree.isLeaf] at h
    · have hfan := hF.2.2.1 ⟨0, by norm_num⟩
      simp only [parentRowG, P.parentFanout] at hfan
      simp at hfan

/-! ### Semantic IO preimage -/

theorem semRecsG_nodup : [P.semParentRec, semInnerRec, semServedRec].Nodup := by
  have h12 : P.semParentRec ≠ semInnerRec := by
    intro h
    have := congrArg (fun r : (nmrMEF F97 K97cubic).Rec => r.2.2) h
    rw [P.semParentTs] at this; norm_num [semInnerRec] at this
  have h13 : P.semParentRec ≠ semServedRec := by
    intro h
    have := congrArg (fun r : (nmrMEF F97 K97cubic).Rec => r.2.2) h
    rw [P.semParentTs] at this; norm_num [semServedRec] at this
  have h23 : semInnerRec ≠ semServedRec := by
    intro h
    have := congrArg (fun r : (nmrMEF F97 K97cubic).Rec => r.2.2) h
    norm_num [semInnerRec, semServedRec] at this
  simp [h12, h13, h23]

def semanticPreimageSG : SemanticIOPreimage cfgS (execSG P) where
  timestampBound := 4
  timestampBound_le_order := by
    change 4 ≤ orderOf fixtureAlpha
    rw [fixtureAlpha_order]
    norm_num
  semanticRequests := [P.semParentRec, semInnerRec, semServedRec]
  semanticResponses := [P.semParentRec, semServedRec, semInnerRec]
  requestTimestampBound := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [P.semParentTs]; norm_num
    · norm_num [semInnerRec]
    · norm_num [semServedRec]
  responseTimestampBound := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [P.semParentTs]; norm_num
    · norm_num [semServedRec]
    · norm_num [semInnerRec]
  semantic_lmio := by
    refine ⟨by norm_num [IO.InRange, cfgS], [P.semParentRec, semInnerRec, semServedRec],
      le_refl _, semRecsG_nodup P, fun x => Iff.rfl, ?_⟩
    exact List.Perm.cons P.semParentRec (List.Perm.swap semInnerRec semServedRec [])
  requestTimestamp_determines := by
    intro x hx y hy h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
        | rfl
        | (simp only [P.semParentTs] at h; norm_num [semInnerRec, semServedRec] at h)
        | (norm_num [semInnerRec, semServedRec] at h)
  requests_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_cons, List.map_singleton,
      P.semParentBridge, semInnerRec_bridge, semServedRec_bridge, derived_requestsSG]
  responses_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_cons, List.map_singleton,
      P.semParentBridge, semServedRec_bridge, semInnerRec_bridge, derived_responsesSG]

theorem semantic_exactSG : SemanticExactLanguage cfgS (execSG P) :=
  ⟨compute_rows_acceptedSG P, memory_rows_acceptedSG P, ⟨semanticPreimageSG P⟩⟩

/-- Every served-forest memory row carries the package `λ = formRDefault` (row encode). -/
theorem execSG_lambda_unset :
    ∀ i, ((execSG P).memoryPubAt i).lambda? = some MemoryTable.formRDefault := by
  intro i
  fin_cases i
  · rw [memoryPubAtSG_0]; rfl
  · rw [memoryPubAtSG_1]; rfl
  · rw [memoryPubAtSG_2]; rfl
  · rw [memoryPubAtSG_3]; rfl
  · rw [memoryPubAtSG_4]; rfl
  · rw [memoryPubAtSG_5]; rfl
  · rw [memoryPubAtSG_6]; rfl
  · rw [memoryPubAtSG_7]; rfl
  · rw [memoryPubAtSG_8]; rfl
  · rw [memoryPubAtSG_9]; rfl
  · rw [memoryPubAtSG_10]; rfl
  · rw [memoryPubAtSG_11]; rfl
  · rw [memoryPubAtSG_12]; rfl
  · rw [memoryPubAtSG_13]; rfl
  · rw [memoryPubAtSG_14]; rfl

theorem chainedSG : ChainedSemanticExactLanguage cfgS (execSG P) where
  semantic := semantic_exactSG P
  z_ne_zero := servedSeed_ne
  compute_wf := compute_wf_allSG P
  memory_wf := memory_wf_allSG P
  compute_chain := compute_chainSG P
  memory_chain := memory_chainSG P
  memory_same_lambda :=
    ExactExecution.memory_same_lambda_of_const _ (some MemoryTable.formRDefault)
      (execSG_lambda_unset P)
  memory_first_counts := by rw [memoryPubAtSG_0]; rfl
  memory_first_indicator := by rw [memoryPubAtSG_0]; rfl
  memory_first_ipre := by rw [memoryPubAtSG_0]; rfl
  memory_last_icur := by
    have hlast :
        cfgS.orbit.lastIndex cfgS.memRows cfgS.memRows_pos =
          ⟨14, by norm_num [cfgS]⟩ := rfl
    rw [hlast, memoryPubAtSG_14]
    rfl

/-! ### Exact topology -/

theorem compute_topologySG : ComputeExactTopology (execSG P) := by
  refine ⟨computeTreeSG_rvt P, ?_⟩
  show ProperArity 3 (computeTreeSG P)
  simp [computeTreeSG]

theorem memory_topologySG : MemoryExactTopology (execSG P) := by
  intro t ht
  simp only [execSG, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · refine ⟨dummyHaltTreeS_rvt, ?_⟩
    simp [dummyHaltTreeS]
  · refine ⟨rootATreeG_rvt _, ?_⟩
    simp [rootATreeG, aDecomposeOuterTreeG, aHeadHaltTreeG, aReadInnerTreeG, aVerifyOuterTreeG,
      aDecomposeInnerTree, aInnerHeadHaltTree, aVerifyInnerTree, aTailHaltTree]
  · refine ⟨rootBTree_rvt, ?_⟩
    simp [rootBTree, bDecomposeTree, bVerifyTree, bResultHaltTree, bTailHaltTree]

theorem traversableSG : TraversableChainedSemanticExactLanguage cfgS (execSG P) where
  chained := chainedSG P
  compute_topology := compute_topologySG P
  memory_topology := memory_topologySG P

/-! ### Bounded noun realization of every public row -/

theorem computeTreeNounRealizationSG :
    ComputePublicTreeNounRealization 97 (execSG P).computePublicTree := by
  have h : (bfsForest [(execSG P).computePublicTree]).map NTree.label
      = [computePublicLabel (parentRowG P), computePublicLabel servedRow] := by
    rw [ExactExecution.computePublicTree_bfs, ExactExecution.computePublicRows,
      (execution_rowsSG P).1]
    rfl
  unfold ComputePublicTreeNounRealization ComputePublicRowsNounRealization
  rw [h]
  refine List.forall_iff_forall_mem.mpr ?_
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl
  · exact P.parentRowNoun
  · exact servedRow_nounRealization

theorem memoryForestNounRealizationSG :
    MemoryPublicForestNounRealization 97 (execSG P).memoryForest := by
  unfold MemoryPublicForestNounRealization MemoryPublicRowsNounRealization
  rw [show (bfsForest (execSG P).memoryForest).map NTree.label = (execSG P).memoryRows from rfl,
    (execution_rowsSG P).2]
  refine List.forall_iff_forall_mem.mpr ?_
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact dummyHalt_realization
  · exact aReadOuter_realizationG _
  · exact bRead_realization
  · exact aDecomposeOuter_realizationG _
  · exact bDecompose_realization
  · exact aHeadHalt_realizationG _
  · exact aReadInner_realization
  · exact bVerify_realization
  · exact bTailHalt_realization
  · exact aVerifyOuter_realizationG _
  · exact bResultHalt_realization
  · exact aDecomposeInner_realization
  · exact aInnerHeadHalt_realization
  · exact aVerifyInner_realization
  · exact aTailHalt_realization

theorem nounRealizationSG : ExactExecutionNounRealization 97 cfgS (execSG P) where
  computeTree := computeTreeNounRealizationSG P
  memoryForest := memoryForestNounRealizationSG P
  memoryLeaves := by
    intro tree htree
    simp only [execSG, List.mem_cons, List.not_mem_nil, or_false] at htree
    rcases htree with rfl | rfl | rfl
    · exact leafAtoms_dummyHaltTreeS
    · exact leafAtoms_rootATreeG _
    · exact leafAtoms_rootBTree

theorem languageSG :
    NounRealizedTraversableChainedSemanticExactLanguage 97 cfgS (execSG P) where
  traversable := traversableSG P
  nounRealization := nounRealizationSG P

/-! ### Exact row-level semantic data on both compute rows -/

theorem computeRowAtSG_zero :
    (execSG P).computeRowAt ⟨0, by norm_num [cfgS]⟩ = parentRowG P := by
  norm_num [ExactExecution.computeRowAt, (execution_rowsSG P).1, cfgS]

theorem computeRowAtSG_one :
    (execSG P).computeRowAt ⟨1, by norm_num [cfgS]⟩ = servedRow := by
  norm_num [ExactExecution.computeRowAt, (execution_rowsSG P).1, cfgS]

def rowDataSG : ∀ i : Fin cfgS.compRows,
    SemanticTrace.ComputeRowSemanticData 97 3 ((execSG P).computeRowAt i)
  | ⟨0, _⟩ => castRowData (computeRowAtSG_zero P) P.parentRowData
  | ⟨1, _⟩ => castRowData (computeRowAtSG_one P) servedRowData
  | ⟨n + 2, h⟩ =>
      absurd (show n + 2 < 2 from by simpa [cfgS] using h) (by omega)

theorem rowDataSG_zero_servedTuples :
    (rowDataSG P ⟨0, by norm_num [cfgS]⟩).needs.served.map lookupTuple = [] := by
  refine (castRowData_servedTuples (computeRowAtSG_zero P) P.parentRowData).trans ?_
  rw [P.parentRowServed]
  rfl

theorem rowDataSG_one_servedTuples :
    (rowDataSG P ⟨1, by norm_num [cfgS]⟩).needs.served.map lookupTuple =
      [(servedRecord, subjectS, 2, resultS)] :=
  (castRowData_servedTuples (computeRowAtSG_one P) servedRowData).trans rfl

/-- The exact semantic CORE of the whole generic execution. -/
def semanticDataSG : SemanticTrace.ExactExecutionSemanticData 97 3 cfgS (execSG P) where
  language := languageSG P
  rowAccepted := fun i =>
    ExactExecution.computeRowAt_accepted (compute_rows_acceptedSG P) i
  rows := rowDataSG P

/-! ## Stage 5b. The generic served memory trace.

Root `B` is opcode-invariant (reused verbatim).  Root `A`'s axis tree and response records are
head-independent (`ts_parentRecordG = 4`, so the walked timestamps are the concrete
`expParent`/`expInner`), so they port over the generic `rootATreeG`. -/

theorem memoryTreeAtSG_zero :
    (execSGA P).memoryTreeAt ⟨0, by norm_num [cfgS]⟩ = dummyHaltTreeS := rfl

theorem memoryTreeAtSG_one :
    (execSGA P).memoryTreeAt ⟨1, by norm_num [cfgS]⟩ = rootATreeGA P.toServedForestParams := rfl

theorem memoryTreeAtSG_two :
    (execSGA P).memoryTreeAt ⟨2, by norm_num [cfgS]⟩ = rootBTreeA := rfl

set_option maxRecDepth 400000 in
theorem axisTreeDummySG :
    exactAxisTree cfgS (execSGA P) ⟨0, by norm_num [cfgS]⟩ = MTree.halt := by
  rw [exactAxisTree, memoryTreeAtSG_zero]
  simp [dummyHaltTreeS, Nock.AxisBridge.ofNTree, Nock.AxisBridge.MemWalk.toMTree,
    memLabelS, dummyHaltPubS]

set_option maxRecDepth 400000 in
/-- Root `A`'s exact axis tree — identical to the OP₄ concrete tree, since every walked timestamp
is head-independent. -/
theorem axisTreeASG :
    exactAxisTree cfgS (execSGA P) ⟨1, by norm_num [cfgS]⟩ =
      MTree.read expParent
        (MTree.decompose MTree.halt
          (MTree.read expInner
            (MTree.verify expParent 3
              (MTree.decompose MTree.halt
                (MTree.verify expInner 3 MTree.halt))))) := by
  rw [exactAxisTree, memoryTreeAtSG_one]
  simp [rootATreeGA, aDecomposeOuterTreeGA, aHeadHaltTreeG, aReadInnerTreeGA, aVerifyOuterTreeGA,
    aDecomposeInnerTreeA, aInnerHeadHaltTree, aVerifyInnerTreeA, aTailHaltTree,
    Nock.AxisBridge.ofNTree, Nock.AxisBridge.MemWalk.toMTree, memLabelS, timestampExpAt,
    expParent, expInner, aReadOuterPubG, aReadInnerPubA, aReadInnerPub, aVerifyOuterPubG,
    aVerifyInnerPubA, aVerifyInnerPub, parentRecordG, parentRecordS, servedFormulaRecord]

set_option maxRecDepth 400000 in
/-- Root `B`'s exact axis tree (opcode-invariant). -/
theorem axisTreeBSG :
    exactAxisTree cfgS (execSGA P) ⟨2, by norm_num [cfgS]⟩ =
      MTree.read expServed
        (MTree.decompose (MTree.verify expServed 2 MTree.halt) MTree.halt) := by
  rw [exactAxisTree, memoryTreeAtSG_two]
  simp [rootBTreeA, bDecomposeTreeA, bVerifyTreeA, bResultHaltTree, bTailHaltTree,
    Nock.AxisBridge.ofNTree, Nock.AxisBridge.MemWalk.toMTree, memLabelS, timestampExpAt,
    expServed, bReadPubA, bReadPub, bVerifyPubA, bVerifyPub, servedRecord]

/-! ### Raw requests and the three services (root `A` parent service is head-generic) -/

/-- Root `A`'s response records (head-independent: `parentRecordG`'s encoded coordinates differ but
its position in the BFS is fixed). -/
theorem rootResponseRecordsDummySG :
    ServedMemoryTrace.rootResponseRecords (execSGA P) ⟨0, by norm_num [cfgS]⟩ = [] := by
  simp [ServedMemoryTrace.rootResponseRecords, memoryTreeAtSG_zero, dummyHaltTreeS,
    bfsForest, MemoryTable.responseRecords, memLabelS, dummyHaltPubS]

theorem rootResponseRecordsAG :
    ServedMemoryTrace.rootResponseRecords (execSGA P) ⟨1, by norm_num [cfgS]⟩ =
      [parentRecordG P.toServedForestParams, servedFormulaRecord] := by
  simp [ServedMemoryTrace.rootResponseRecords, memoryTreeAtSG_one, rootATreeGA,
    aDecomposeOuterTreeGA, aHeadHaltTreeG, aReadInnerTreeGA, aVerifyOuterTreeGA,
    aDecomposeInnerTreeA, aInnerHeadHaltTree, aVerifyInnerTreeA, aTailHaltTree,
    bfsForest, MemoryTable.responseRecords, memLabelS, aReadOuterPubG, aDecomposeOuterPubG,
    aHeadHaltPubG, aReadInnerPubA, aReadInnerPub, aVerifyOuterPubG, aDecomposeInnerPub,
    aInnerHeadHaltPub, aVerifyInnerPubA, aVerifyInnerPub, aTailHaltPub]

theorem rootResponseRecordsBG :
    ServedMemoryTrace.rootResponseRecords (execSGA P) ⟨2, by norm_num [cfgS]⟩ = [servedRecord] := by
  simp [ServedMemoryTrace.rootResponseRecords, memoryTreeAtSG_two, rootBTreeA,
    bDecomposeTreeA, bVerifyTreeA, bResultHaltTree, bTailHaltTree,
    bfsForest, MemoryTable.responseRecords, memLabelS, bReadPubA, bReadPub, bDecomposePub,
    bVerifyPubA, bVerifyPub, bResultHaltPub, bTailHaltPub]

theorem parentRecordG_ts_eq : (parentRecordG P.toServedForestParams).ts = parentRecordS.ts := by
  rw [ts_parentRecordG, ts_parentRecordS]

/-- Root `A`'s outer service — the only genuinely parent-specific service, but every obligation is
head-generic (the served slot is `slot 3 (cell parentHead formulaS) = formulaS`). -/
def serviceA1G : ServedMemoryTrace.Service cfgS (execSGA P) where
  exponent := expParent
  record := parentRecordG P.toServedForestParams
  root := P.parentFormula
  child := formulaS
  axis := 3
  request_mem := by rw [rawRequestsSGA]; simp
  timestamp := by rw [parentRecordG_ts_eq]; exact ts_eq_parent
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [parentRecordG] }
  served := by rw [P.hcons]; simp [Noun.slot]

def serviceA2G : ServedMemoryTrace.Service cfgS (execSGA P) where
  exponent := expInner
  record := servedFormulaRecord
  root := formulaS
  child := tailS
  axis := 3
  request_mem := by rw [rawRequestsSGA]; simp
  timestamp := ts_eq_inner
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [servedFormulaRecord] }
  served := by simp [formulaS, Noun.slot]

def serviceBG : ServedMemoryTrace.Service cfgS (execSGA P) where
  exponent := expServed
  record := servedRecord
  root := subjectS
  child := resultS
  axis := 2
  request_mem := by rw [rawRequestsSGA]; simp
  timestamp := ts_eq_served
  realization := servedRecord_realizes
  served := slot_subjectS

/-! ### The two generic root traces -/

def rootTraceDummySG :
    ServedMemoryTrace.RootTrace cfgS (execSGA P) ⟨0, by norm_num [cfgS]⟩ where
  subject := .atom 0
  services := []
  recordPartition := by rw [rootResponseRecordsDummySG]; rfl
  readPartition := by rw [axisTreeDummySG]; simp [readExps]
  verifyPartition := by rw [axisTreeDummySG]; simp [verifyExps]
  traversal := by
    rw [axisTreeDummySG]
    exact ServedMemoryTrace.ServiceWalk.halt

def rootTraceAG :
    ServedMemoryTrace.RootTrace cfgS (execSGA P) ⟨1, by norm_num [cfgS]⟩ where
  subject := P.parentFormula
  services := [serviceA1G P, serviceA2G P]
  recordPartition := by rw [rootResponseRecordsAG]; rfl
  readPartition := by rw [axisTreeASG]; simp [serviceA1G, serviceA2G, readExps]
  verifyPartition := by rw [axisTreeASG]; simp [serviceA1G, serviceA2G, verifyExps]
  traversal := by
    rw [axisTreeASG, P.hcons]
    refine ServedMemoryTrace.ServiceWalk.read (serviceA1G P) (by simp) rfl P.hcons ?_ ?_
    · rw [show (serviceA1G P).axis = 3 from rfl, axisPath_three]
      refine ServedMemoryTrace.VerifyRoute.right (by simp [readCount])
        (by simp [verifyCount]) ?_
      refine ServedMemoryTrace.VerifyRoute.read_other expInner_ne_expParent ?_
      exact ServedMemoryTrace.VerifyRoute.here rfl rfl (by simp [readCount])
        (by simp [verifyCount, expInner_ne_expParent])
    · refine ServedMemoryTrace.ServiceWalk.decompose
        (by rw [P.hhead]; exact ServedMemoryTrace.ServiceWalk.halt) ?_
      refine ServedMemoryTrace.ServiceWalk.read (serviceA2G P) (by simp) rfl rfl ?_ ?_
      · rw [show (serviceA2G P).axis = 3 from rfl, axisPath_three]
        refine ServedMemoryTrace.VerifyRoute.verify_other expParent_ne_expInner ?_
        refine ServedMemoryTrace.VerifyRoute.right (by simp [readCount])
          (by simp [verifyCount]) ?_
        exact ServedMemoryTrace.VerifyRoute.here rfl rfl (by simp [readCount])
          (by simp [verifyCount])
      · exact ServedMemoryTrace.ServiceWalk.verify
          (ServedMemoryTrace.ServiceWalk.decompose ServedMemoryTrace.ServiceWalk.halt
            (ServedMemoryTrace.ServiceWalk.verify ServedMemoryTrace.ServiceWalk.halt))

def rootTraceBG :
    ServedMemoryTrace.RootTrace cfgS (execSGA P) ⟨2, by norm_num [cfgS]⟩ where
  subject := subjectS
  services := [serviceBG P]
  recordPartition := by rw [rootResponseRecordsBG]; rfl
  readPartition := by rw [axisTreeBSG]; simp [serviceBG, readExps]
  verifyPartition := by rw [axisTreeBSG]; simp [serviceBG, verifyExps]
  traversal := by
    rw [axisTreeBSG]
    refine ServedMemoryTrace.ServiceWalk.read (serviceBG P) (by simp) rfl rfl ?_ ?_
    · rw [show (serviceBG P).axis = 2 from rfl, axisPath_two]
      refine ServedMemoryTrace.VerifyRoute.left ?_ (by simp [readCount])
        (by simp [verifyCount])
      exact ServedMemoryTrace.VerifyRoute.here rfl rfl (by simp [readCount])
        (by simp [verifyCount])
    · exact ServedMemoryTrace.ServiceWalk.decompose
        (ServedMemoryTrace.ServiceWalk.verify ServedMemoryTrace.ServiceWalk.halt)
        ServedMemoryTrace.ServiceWalk.halt

def rootTracesSG : ∀ i : Fin cfgS.kMem, ServedMemoryTrace.RootTrace cfgS (execSGA P) i
  | ⟨0, _⟩ => rootTraceDummySG P
  | ⟨1, _⟩ => rootTraceAG P
  | ⟨2, _⟩ => rootTraceBG P
  | ⟨n + 3, h⟩ =>
      absurd (show n + 3 < 3 from by simpa [cfgS] using h) (by omega)

theorem rootTracesSG_zero : rootTracesSG P ⟨0, by norm_num [cfgS]⟩ = rootTraceDummySG P := rfl

theorem rootTracesSG_one : rootTracesSG P ⟨1, by norm_num [cfgS]⟩ = rootTraceAG P := rfl

theorem rootTracesSG_two : rootTracesSG P ⟨2, by norm_num [cfgS]⟩ = rootTraceBG P := rfl

/-! ### The aggregate cross-root timestamp multiset -/

theorem forestTimestampPowersSG :
    (List.finRange cfgS.kMem).flatMap
        (fun i => (rootTracesSG P i).timestampPowers) = [(4 : K97cubic), 16, 64] := by
  rw [finRange_kMemS]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    rootTracesSG_zero, rootTracesSG_one, rootTracesSG_two]
  simp only [ServedMemoryTrace.RootTrace.timestampPowers,
    ServedMemoryTrace.RootTrace.exponents, rootTraceDummySG, rootTraceAG, rootTraceBG,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  rw [show ((serviceA1G P).exponent : ℕ) = expParent from rfl,
    show ((serviceA2G P).exponent : ℕ) = expInner from rfl,
    show ((serviceBG P).exponent : ℕ) = expServed from rfl,
    ← ts_eq_parent, ← ts_eq_inner, ← ts_eq_served,
    ts_parentRecordS, ts_servedFormulaRecord, ts_servedRecord]

theorem forestTimestampPowers_nodupSG :
    ((List.finRange cfgS.kMem).flatMap
      (fun i => (rootTracesSG P i).timestampPowers)).Nodup := by
  rw [forestTimestampPowersSG]
  have h1 : (4 : K97cubic) ≠ 16 := ts_4_ne_16
  have h2 : (4 : K97cubic) ≠ 64 := ts_4_ne_64
  have h3 : (16 : K97cubic) ≠ 64 := ts_16_ne_64
  simp [h1, h2, h3]

/-- The generic served memory trace: two serviced roots covering the single `OP_0` slot lookup. -/
def servedMemoryTraceSG :
    ServedMemoryTrace.ExactServedMemoryTrace 97 3 cfgS (execSG P) (semanticDataSG P)
      (execSGA P) where
  roots := rootTracesSG P
  timestampPowersNodup := forestTimestampPowers_nodupSG P
  forestIndexRange := by
    rw [forestTimestampPowersSG]
    norm_num [IO.InRange, cfgS]
  semanticCoverage := by
    intro row lookup hlookup
    have hl : lookup ∈ (rowDataSG P row).needs.served := hlookup
    rcases row with ⟨v, hv⟩
    match v, hv with
    | 0, hv =>
        exfalso
        have hmem : lookupTuple lookup ∈
            (rowDataSG P ⟨0, hv⟩).needs.served.map lookupTuple :=
          List.mem_map_of_mem hl
        rw [rowDataSG_zero_servedTuples] at hmem
        simp at hmem
    | 1, hv =>
        have hmem : lookupTuple lookup ∈
            (rowDataSG P ⟨1, hv⟩).needs.served.map lookupTuple :=
          List.mem_map_of_mem hl
        rw [rowDataSG_one_servedTuples] at hmem
        simp only [List.mem_singleton] at hmem
        have htuple : (lookup.record, lookup.root, lookup.axis, lookup.child) =
            (servedRecord, subjectS, 2, resultS) := hmem
        refine ⟨⟨2, by norm_num [cfgS]⟩, serviceBG P, ?_, ?_, ?_, ?_, ?_⟩
        · rw [rootTracesSG_two]
          simp [rootTraceBG]
        · have hc := congrArg Prod.fst htuple
          simpa [serviceBG] using hc.symm
        · have hc := congrArg (fun p => p.2.1) htuple
          simpa [serviceBG] using hc.symm
        · have hc := congrArg (fun p => p.2.2.2) htuple
          simpa [serviceBG] using hc.symm
        · have hc := congrArg (fun p => p.2.2.1) htuple
          simpa [serviceBG] using hc.symm
    | (n + 2), hv =>
        exact absurd (show n + 2 < 2 from by simpa [cfgS] using hv) (by omega)

/-! ## Stage 6a. The generic buildable execution bundle.

The memory-state counts and record-count balance are head-independent (they count row *states*, not
record coordinates), so they port from the concrete `memoryStateCountsS` proof by swapping the four
parent-touching pubs to their `…G` forms. -/

theorem memoryStateCountsSG :
    RowLayout.memoryStateCount (execSG P) .read_root = 3 ∧
      RowLayout.memoryStateCount (execSG P) .verify_child = 3 ∧
      RowLayout.memoryStateCount (execSG P) .decompose = 3 ∧
      RowLayout.memoryStateCount (execSG P) .halt = 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [RowLayout.memoryStateCount, RowLayout.fibreCount, (execution_rowsSG P).2, memLabelS,
      dummyHaltPubS, aReadOuterPubG, bReadPub, aDecomposeOuterPubG, bDecomposePub, aHeadHaltPubG,
      aReadInnerPub, bVerifyPub, bTailHaltPub, aVerifyOuterPubG, bResultHaltPub,
      aDecomposeInnerPub, aInnerHeadHaltPub, aVerifyInnerPub, aTailHaltPub]

theorem recordCountBalanceSG : RowLayout.RecordCountBalanced (execSG P) := by
  rw [RowLayout.RecordCountBalanced, (memoryStateCountsSG P).1, (memoryStateCountsSG P).2.1]

theorem addedRecordListSG :
    RowLayout.addedRecordList (execSG P) =
      [NockVM.formRRow (parentRecordG P.toServedForestParams) MemoryTable.formRDefault,
        NockVM.formRRow servedRecord MemoryTable.formRDefault,
        NockVM.formRRow servedFormulaRecord MemoryTable.formRDefault] := by
  rw [RowLayout.addedRecordList, (execution_rowsSG P).2]
  simp [MemoryTable.responseRecords, memLabelS, dummyHaltPubS,
    aReadOuterPubG, bReadPub, aDecomposeOuterPubG, bDecomposePub, aHeadHaltPubG,
    aReadInnerPub, bVerifyPub, bTailHaltPub, aVerifyOuterPubG, bResultHaltPub,
    aDecomposeInnerPub, aInnerHeadHaltPub, aVerifyInnerPub, aTailHaltPub]

theorem consumedRecordListSG :
    RowLayout.consumedRecordList (execSG P) =
      [NockVM.formRRow servedRecord MemoryTable.formRDefault,
        NockVM.formRRow (parentRecordG P.toServedForestParams) MemoryTable.formRDefault,
        NockVM.formRRow servedFormulaRecord MemoryTable.formRDefault] := by
  rw [RowLayout.consumedRecordList, (execution_rowsSG P).2]
  simp [RowLayout.consumedRecords, memLabelS, dummyHaltPubS,
    aReadOuterPubG, bReadPub, aDecomposeOuterPubG, bDecomposePub, aHeadHaltPubG,
    aReadInnerPub, bVerifyPub, bTailHaltPub, aVerifyOuterPubG, bResultHaltPub,
    aDecomposeInnerPub, aInnerHeadHaltPub, aVerifyInnerPub, aTailHaltPub]

theorem pairedRecordLayoutSG : RowLayout.PairedRecordLayout (execSG P) := by
  rw [RowLayout.PairedRecordLayout, addedRecordListSG, consumedRecordListSG]
  exact (List.Perm.swap (NockVM.formRRow servedRecord MemoryTable.formRDefault)
    (NockVM.formRRow (parentRecordG P.toServedForestParams) MemoryTable.formRDefault)
    [NockVM.formRRow servedFormulaRecord MemoryTable.formRDefault]).symm

theorem honestVerSG : ∀ row ∈ (execSG P).memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  simp [(execution_rowsSG P).2, memLabelS, dummyHaltPubS,
    aReadOuterPubG, bReadPub, aDecomposeOuterPubG, bDecomposePub, aHeadHaltPubG,
    aReadInnerPub, bVerifyPub, bTailHaltPub, aVerifyOuterPubG, bResultHaltPub,
    aDecomposeInnerPub, aInnerHeadHaltPub, aVerifyInnerPub, aTailHaltPub]


theorem memoryBudgetSG :
    RowLayout.memoryM (execSG P) = 9 ∧ RowLayout.memoryL (execSG P) = 3 ∧
      cfgS.memRows = RowLayout.memoryM (execSG P) + 2 * RowLayout.memoryL (execSG P) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [RowLayout.memoryM, (memoryStateCountsSG P).2.2.1, (memoryStateCountsSG P).2.2.2]
  · exact (memoryStateCountsSG P).1
  · rw [RowLayout.memoryM, RowLayout.memoryL, (memoryStateCountsSG P).2.2.1,
      (memoryStateCountsSG P).2.2.2, (memoryStateCountsSG P).1]
    norm_num [cfgS]

/-- **The generic buildable execution** over `P : ServedForestExec`.  All fourteen input fields are
named explicitly; `memoryTrace` is the generic two-serviced-root `servedMemoryTraceSG` and
`two_ne_zero` / the trace are supplied without defaults. -/
def servedForestModule : BuildableNockExecution F97 K97cubic where
  q := 97
  q_gt_one := by norm_num
  Λ := 3
  cfg := cfgS
  execA := execSGA P
  exec := execSG P
  exec_encode := execSG_encode P
  semanticData := semanticDataSG P
  memoryTrace := servedMemoryTraceSG P
  requestNodup := requestsSG_nodup P
  recordCountBalance := recordCountBalanceSG P
  q_le_ringChar := by rw [ringChar_K97]
  two_ne_zero := two_ne_zero_K97
  Ksz_lt_ringChar := by rw [ringChar_K97]; norm_num [cfgS]
  programIOCapacity := by
    rw [derived_requestsSG]
    norm_num [cfgS, executionOrbit97]
  memoryIOCapacity := by
    rw [derived_responsesSG]
    norm_num [cfgS, executionOrbit97]

/-! ## Stage 6b. The generic pre-compilation backend inputs.

`strictOrbitM`, `basis97`, `stateTagChar97`, and `cardK97cubic` are opcode-invariant and reused
verbatim.  The IO-failure bound and the good-coins existence argument are head-independent (they are
cardinality bounds on the three-record sample, whose *length* is fixed), so the whole `Inputs`
constructor ports from `inputsM` by swapping `multiRootExecution → servedForestModule P`. -/

/-- The pre-challenge record sample of the generic fixture. -/
def sampledRecordsMG : FiniteIO.PreChallengeRecords K97cubic 9 :=
  BuildableChips.executionRecords (servedForestModule P)

theorem sampledRecordsMG_lengths :
    (sampledRecordsMG P).requests.length = 3 ∧ (sampledRecordsMG P).responses.length = 3 := by
  constructor
  · change (execSG P).derivedRequestIO.length = 3
    rw [derived_requestsSG]; rfl
  · change (execSG P).derivedResponseIO.length = 3
    rw [derived_responsesSG]; rfl

theorem ioFailureBoundMG :
    (FiniteIO.IOFailureEvent (sampledRecordsMG P)).card <
      Fintype.card (K97cubic × K97cubic) := by
  refine lt_of_le_of_lt (FiniteIO.IOFailureEvent_card_le (sampledRecordsMG P)) ?_
  rw [(sampledRecordsMG_lengths P).1, (sampledRecordsMG_lengths P).2]
  simp only [FiniteIO.ioFailureUnionBound, Fintype.card_prod]
  rw [cardK97cubic]
  norm_num

theorem goodIOCoinsMG_exists :
    ∃ coins : FiniteIO.IOCoins K97cubic,
      (coins.gamma, coins.pole) ∉ FiniteIO.IOFailureEvent (sampledRecordsMG P) ∧
      (coins.gamma, coins.pole) ∉ FiniteIO.IOFailureEvent (BuildableChips.executionRecords10 (servedForestModule P)) :=
  RecordCarrier.exists_io_coins_ext _ (sampledRecordsMG P)
    (sampledRecordsMG_lengths P).1.le (sampledRecordsMG_lengths P).2.le
    (by
      rw [RecordCarrier.honestIOBound_eq, Fintype.card_prod, cardK97cubic]
      norm_num)

def ioCoinsMG : FiniteIO.IOCoins K97cubic := Classical.choose (goodIOCoinsMG_exists P)

theorem ioCoinsMG_good :
    ((ioCoinsMG P).gamma, (ioCoinsMG P).pole) ∉ FiniteIO.IOFailureEvent (sampledRecordsMG P) :=
  (Classical.choose_spec (goodIOCoinsMG_exists P)).1

theorem ioCoinsMG_good10 :
    ((ioCoinsMG P).gamma, (ioCoinsMG P).pole) ∉
      FiniteIO.IOFailureEvent (BuildableChips.executionRecords10 (servedForestModule P)) :=
  (Classical.choose_spec (goodIOCoinsMG_exists P)).2

theorem inputsMG_interCard :
    2 * ((executionInterRecords (servedForestModule P)).requests.length +
      (executionInterRecords (servedForestModule P)).responses.length) + 1 < Fintype.card K97cubic :=
  executionInterRecords_card_lt_of_memRows (servedForestModule P) (by
    have hmem : (servedForestModule P).cfg.memRows = 15 := rfl
    have hq : Fintype.card K97cubic = 97 ^ 3 := by
      rw [Fintype.card_eq_nat_card]
      exact GaloisField.card 97 3 (by norm_num)
    rw [hmem, hq]
    norm_num)


def inputsMG : BuildableChips.Inputs (servedForestModule P) where
  stateTagChar := stateTagChar97
  computeWalkAlpha := 2
  memoryWalkAlpha := 3
  walkGamma := 5
  hOrb := 4
  basis := basis97
  orbit := strictOrbitM
  activeDomains :=
    { computeCapacity := by norm_num [servedForestModule, cfgS]
      memoryCapacity := by
        rw [show RowLayout.memoryM (servedForestModule P).exec = 9 from (memoryBudgetSG P).1,
          show RowLayout.memoryL (servedForestModule P).exec = 3 from (memoryBudgetSG P).2.1]
        norm_num }
  ioCoins := ioCoinsMG P
  ioPoleHitGood := by
    intro h
    apply ioCoinsMG_good P
    simp [FiniteIO.IOFailureEvent, sampledRecordsMG, h]
    <;> (refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩; exact Or.inr (Or.inl h))
  ioGammaGood := by
    intro h
    apply ioCoinsMG_good P
    simp [FiniteIO.IOFailureEvent, sampledRecordsMG, h]
    <;> (refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩; exact Or.inl h)
  ioLogDerivGood := by
    intro h
    apply ioCoinsMG_good P
    simp [FiniteIO.IOFailureEvent, sampledRecordsMG, h]
    <;> (refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩; exact Or.inr (Or.inr h))
  computeChallenges := default
  memoryScalarChallenge := fun j => (j : F97) + 1
  memoryExtensionFold :=
    interPoleOfE (servedForestModule P) (ioCoinsMG P).gamma (inputsMG_interCard P)
  interPoleHitGood :=
    interPoleOfE_good (servedForestModule P) (ioCoinsMG P).gamma (inputsMG_interCard P)
  honestVer := honestVerSG P
  ioGood10 := ioCoinsMG_good10 P
  interPoleHitGood10 :=
    interPoleOfE_good10 (servedForestModule P) (ioCoinsMG P).gamma (inputsMG_interCard P)

theorem inputsMG_challenges : (inputsMG P).computeChallenges = default := rfl

end

end Nock.NockVMROM.Thm54.ServedForestModule

#print axioms Nock.NockVMROM.Thm54.ServedForestModule.execSG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.execution_rowsSG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.derived_requestsSG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.derived_responsesSG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.requestsSG_nodup
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.responsesSG_nodup
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.memory_chainSG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.semanticPreimageSG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.languageSG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.semanticDataSG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.servedMemoryTraceSG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.recordCountBalanceSG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.servedForestModule
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.inputsMG
