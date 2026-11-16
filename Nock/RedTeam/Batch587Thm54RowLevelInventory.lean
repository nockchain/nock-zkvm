/-
  Nock/RedTeam/Batch587Thm54RowLevelInventory.lean

  Instruments (all run at elaboration time; a false assertion FAILS THE BUILD):
  * `axisReadersIn root` — every constant in the transitive type+value closure of `root`
    (theorem bodies included, `value? (allowOpaque := true)`) whose own type or value mentions the
    projection `ComputeTable.MemRec.axis` (as a constant or as `Expr.proj _ 2`).
  * `closureOf root` — that closure as a `NameSet`.
  Positive controls: `MemoryTable.eqBlk` reads the axis (its `verify_child` clause); `BindMemRec`
  is in the capstone closure.

  What is compiled here:
  * §1 **The hostile decode pipeline is NOT in the proof closure of `nockCompiles_zmod`.**
    The capstone's `ExactExecution` is the honest
    `P.objects.exec`; `derivedResponseIO`, `tableRecordAt`, `BindMemRec`, `BindMemoryRow`,
    `MemoryRowFrame` are present.
  * §2 the inventory (`inventory`), each entry certified to read `MemRec.axis` directly, with its
    layer, its use, and what R1–R3 supply.
  * §3 composition on live: decoded memory rows hold the chip's role 25 in the axis slot with no
    encode (`decodeMemPub_axis_is_role25`); decoded compute records are V_comp-semantic
    (`expectedMr2_s0_axis`); the hostile memory skeleton DECODES that slot as the Nock axis
    (`decodeMemoryRowIn_readRoot_axis`), which under R1 is `T`, not `a`
    (`r1_skeleton_reads_T_not_a`); `BindMemRec` then fails for an honest R1 row
    (`r1_bindMemRec_fails`).
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
import Nock.NockVMROM.Thm54.ExecOfTracesPrefix
import Nock.NockVMROM.Thm54.HostileSkeletonDecoding
import Nock.NockVMROM.Thm54.StrategyOfTraces
import Nock.NockVMROM.Thm54.WrapFixesVcomp
import Nock.NockVMROM.Thm54.WrapMemoryConjuncts
import Nock.NockVMROM.Thm54.MemoryWalkRoots
import Nock.NockVMROM.Thm54.FamilyMemoryRows
import Nock.NockVMROM.Thm54.RemainingIoObstructions
import Nock.RedTeam.Batch588Thm54RowLevelHonest
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch587

open Lean Meta Elab Command

/-! ## §0 Instruments -/

/-- Does `e` mention the `MemRec.axis` projection? -/
def mentionsAxis (e : Expr) : Bool :=
  (e.find? fun x => match x with
    | .const n _ => n == ``Nock.ComputeTable.MemRec.axis
    | .proj s i _ => s == ``Nock.ComputeTable.MemRec && i == 2
    | _ => false).isSome

/-- Does the constant `n` itself (type or value, proofs included) read `MemRec.axis`? -/
def readsAxis (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | none => false
  | some ci =>
      mentionsAxis ci.type ||
        mentionsAxis ((ci.value? (allowOpaque := true)).getD (.sort .zero))

/-- Transitive type+value closure (proof terms included). -/
partial def closureOf (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := #[root]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let v := (ci.value? (allowOpaque := true)).getD (.sort .zero)
    for c in ci.type.getUsedConstants ++ v.getUsedConstants do
      if !seen.contains c then stack := stack.push c
  return seen

def capstoneName : Name := `Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
def statement : Name := `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement

/-- Hostile decode pipeline names (all exist; asserted below). -/
def hostilePipeline : List Name :=
  [``Nock.NockVMROM.Thm54.StrategyOfTracesCore.strategyOfTraces,
   ``Nock.NockVMROM.Thm54.StrategyOfTracesCore.strategyOfTraces_bindsAtCoin,
   ``Nock.NockVMROM.Thm54.ExecOfTraces.execOfTraces,
   ``Nock.NockVMROM.Thm54.ExecOfTraces.decodeMemPub,
   ``Nock.NockVMROM.Thm54.ExecOfTracesPrefix.execOfTracesPrefix,
   ``Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill.specializedExec_eq,
   ``Nock.NockVMROM.Thm54.HostileSkeletonDecoding.decodedSkeleton,
   ``Nock.NockVMROM.Thm54.HostileSkeletonDecoding.decodeMemoryRowIn,
   ``Nock.NockVMROM.Thm54.StrategyOfTraces.memRecJoin]

/-- Honest objects the capstone does read (positive controls for the closure walk). -/
def honestInCapstone : List Name :=
  [``Nock.NockVMROM.Thm54.ExactExecution.derivedResponseIO,
   ``Nock.NockVMROM.Thm54.ExactExecution.derivedRequestIO,
   ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.SemanticTimestampSkeleton.tableRecordAt,
   ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.ExactExecutionTemplate,
   ``Nock.NockVMROM.Thm54.SemanticStrategy.BindMemRec,
   ``Nock.NockVMROM.Thm54.SemanticStrategy.BindMemoryRow,
   ``Nock.NockVMROM.Thm54.RawSemanticAssembly.MemoryRowFrame]

/-! ## §1 The hostile pipeline is off the capstone; the honest objects are on it -/

run_cmd do
  let env ← getEnv
  let cap := closureOf env capstoneName
  let stmt := closureOf env statement
  -- positive controls: the walk finds things
  unless cap.contains ``Nock.MemoryTable.eqBlk do throwError "control: eqBlk not in capstone"
  unless readsAxis env ``Nock.MemoryTable.eqBlk do throwError "control: eqBlk reads no axis"
  for n in honestInCapstone do
    unless cap.contains n do throwError m!"honest object {n} NOT in capstone closure"
  unless cap.contains ``Nock.NockVMROM.Thm54.ExecOfTraces.execOfTraces do
    throwError "the 36th move: execOfTraces expected in the capstone closure"
  for n in hostilePipeline do
    unless env.contains n do throwError m!"{n} does not exist"
    -- It stays out of the STATEMENT closure.
    logInfo m!"hostile {n}: in capstone closure = {cap.contains n}"
    if stmt.contains n then throwError m!"hostile {n} IS in the statement closure"

/-! ## §2 The dependence inventory -/

/-- Where a reader sits. -/
inductive Layer
  /-- in the proof closure of `nockCompiles_zmod`; reads honest / template / column objects -/
  | capstone
  /-- off the capstone: the hostile decode track (`StrategyOfTraces*`, `ExecOfTraces*`, …) -/
  | hostileOff
deriving DecidableEq, Repr

/-- What the reader uses `MemRec.axis` for. -/
inductive Use
  /-- the axis slot as a table column / RLC coordinate / encoded vector / record equality -/
  | column
  | computeVcomp
  /-- memory row axis bound to the skeleton's `ℕ` address (`BindMemRec`, frames, templates) -/
  | memoryBinding
  /-- paper `verify_child` accounting `counts += axis·ts` (`MTree.verify _ a _`) -/
  | paperAccounting
  /-- hostile: read the decoded memory row's axis slot AS the Nock axis -/
  | hostileDecode
deriving DecidableEq, Repr

/-- What R1–R3 do with it. -/
inductive Supply
  /-- unchanged: reads a column; under R1 the column holds `T`, which is what the chip reads -/
  | unchanged
  /-- unchanged: compute records stay a-bearing (R1 amended: memory-only) -/
  | computeStays
  /-- restate as `row (T, C') = (formRT λ s.axis, formRC λ s.axis)` — encode the SKELETON at bind -/
  | encodeSkeletonAtBind
  /-- retyped by Form R itself (verify adds `λ^{n−1}·ts`; no axis read), independent of R1 -/
  | formRRetype
  /-- BROKEN under R1 as written: must take the axis from the compute join (R3), not decode it -/
  | joinNotDecode
deriving DecidableEq, Repr

structure Reader where
  name : Name
  layer : Layer
  use : Use
  supply : Supply

open Layer Use Supply in
/-- **The inventory.**  Every `MemRec.axis` reader reached from `nockCompiles_zmod` (capstone) or
from the hostile-track modules (`hostileOff`), modulo auxiliary `eq_n` / `_simp` / `_proof`
constants. -/
def inventory : List Reader := [
  -- column / RLC / record equality (row-neutral)
  ⟨``Nock.ComputeTable.MemRec.ext, capstone, column, unchanged⟩,
  ⟨``Nock.MemoryTable.recRLC, capstone, column, unchanged⟩,
  ⟨``Nock.NockVM.encRec, capstone, column, unchanged⟩,
  ⟨``Nock.Reified.computeEnvFull, capstone, column, unchanged⟩,
  ⟨``Nock.Reified.memoryEnvFull, capstone, column, unchanged⟩,
  ⟨``Nock.Reified.memEqC_sound, capstone, column, unchanged⟩,
  ⟨``Nock.Reified.memZeroC_sound, capstone, column, unchanged⟩,
  ⟨``Nock.Reified.mem_perState_sound, capstone, column, unchanged⟩,
  ⟨``Nock.Reified.poleExpr_eval, capstone, column, unchanged⟩,
  ⟨``Nock.Reified.memPacked_zero, capstone, column, unchanged⟩,
  ⟨``Nock.Reified.packMR_zero_opSel, capstone, column, unchanged⟩,
  ⟨``Nock.NockVMROM.Thm54.MemoryPaperFactorization.poleSource_eval_eq_compress,
    capstone, column, unchanged⟩,
  ⟨``Nock.NockVMROM.Thm54.MemoryPaperFactorization.canonical_paperAggregator,
    capstone, column, unchanged⟩,
  ⟨``Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.canonical_denominatorPinMixed,
    capstone, column, unchanged⟩,
  ⟨``Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.exactMemoryRowEnv_trace_ge35,
    capstone, column, unchanged⟩,
  -- paper accounting (retyped by Form R regardless of R1)
  ⟨``Nock.MemoryTable.eqBlk, capstone, paperAccounting, formRRetype⟩,
  ⟨``Nock.Reified.memEqBlkExprs_verify_child_sound, capstone, paperAccounting, formRRetype⟩,
  ⟨``Nock.NockVMROM.Thm54.TemplateAxisCounting.templateAxisTree,
    capstone, paperAccounting, formRRetype⟩,
  ⟨``Nock.NockVMROM.Thm54.TemplateAxisCounting.recoveredAxisTree,
    capstone, paperAccounting, formRRetype⟩,
  ⟨``Nock.NockVMROM.Thm54.TemplateAxisStructure.recoveredAxisTree_eq_reindexAxisTree,
    capstone, paperAccounting, formRRetype⟩,
  ⟨``Nock.NockVMROM.Thm54.ServedMemoryTrace.ServiceWalk.axisValidity,
    capstone, paperAccounting, formRRetype⟩,
  ⟨``Nock.NockVMROM.Thm54.TraceGen.axisMTree_verify_node, capstone, paperAccounting, formRRetype⟩,
  ⟨``Nock.NockVMROM.Thm54.TraceGen.gMemRow9_verify_bind, capstone, paperAccounting, formRRetype⟩,
  ⟨``Nock.NockVMROM.Thm54.TraceGen.annotatedVerifyPub_eqBlk,
    capstone, paperAccounting, formRRetype⟩,
  ⟨``Nock.NockVMROM.Thm54.TraceGen.genAssignedMemory_WF, capstone, paperAccounting, formRRetype⟩,
  -- compute records: a-bearing by V_comp (stay semantic)
  ⟨``Nock.NockVMROM.Thm54.OpcodeSemantics.RealizesMemRec.axis_realizes,
    capstone, computeVcomp, computeStays⟩,
  ⟨``Nock.NockVMROM.Thm54.OpcodeSemantics.s0_vcomp_semantics, capstone, computeVcomp, computeStays⟩,
  ⟨``Nock.NockVMROM.Thm54.OpcodeSemantics.s9_vcomp_semantics, capstone, computeVcomp, computeStays⟩,
  ⟨``Nock.NockVMROM.Thm54.OptimizedComputeSameExecution.exactFinalCurrentEnv_table_mr2,
    capstone, computeVcomp, computeStays⟩,
  ⟨``Nock.NockVMROM.Thm54.TraceGen.renderOp0Row_Vcomp, capstone, computeVcomp, computeStays⟩,
  ⟨``Nock.NockVMROM.Thm54.TraceGen.genSkelOp0_bindCompute, capstone, computeVcomp, computeStays⟩,
  ⟨``Nock.NockVMROM.Thm54.RawSemanticAssembly.ComputeRowFrame.memoryRecordAxis,
    capstone, computeVcomp, computeStays⟩,
  ⟨``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.activeComputeRecord_eq_tableRecordAt,
    capstone, computeVcomp, computeStays⟩,
  ⟨``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.ComputeRowTemplate.bindMemRec_specialize_active,
    capstone, computeVcomp, computeStays⟩,
  ⟨``Nock.NockVMROM.Thm54.TraceGen.realizesMemRec_of_bindMemRec,
    capstone, computeVcomp, computeStays⟩,
  -- memory binding: the honest R2 annotation already exists as the skeleton's ℕ axis
  ⟨``Nock.NockVMROM.Thm54.SemanticStrategy.BindMemRec, capstone, memoryBinding, encodeSkeletonAtBind⟩,
  ⟨``Nock.NockVMROM.Thm54.RawSemanticAssembly.MemoryRowFrame.memoryRecordAxis,
    capstone, memoryBinding, encodeSkeletonAtBind⟩,
  ⟨``Nock.NockVMROM.Thm54.RawSemanticAssembly.bindMemoryRow_of_slots,
    capstone, memoryBinding, encodeSkeletonAtBind⟩,
  ⟨``Nock.NockVMROM.Thm54.ActiveFingerprintScan.bindMemoryRow_slots,
    capstone, memoryBinding, encodeSkeletonAtBind⟩,
  ⟨``Nock.NockVMROM.Thm54.HonestCommitment.bindMemoryRow_render,
    capstone, memoryBinding, encodeSkeletonAtBind⟩,
  ⟨``Nock.NockVMROM.Thm54.HonestCommitment.memory_specialize_placeholder_eq,
    capstone, memoryBinding, encodeSkeletonAtBind⟩,
  ⟨``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate.bindsRow_specialize,
    capstone, memoryBinding, encodeSkeletonAtBind⟩,
  ⟨``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.SemanticTimestampSkeleton.tableRecordAt_eq_of_bind,
    capstone, memoryBinding, encodeSkeletonAtBind⟩,
  ⟨``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.SemanticTimestampSkeleton.bridge_semanticRecordAt,
    capstone, memoryBinding, encodeSkeletonAtBind⟩,
  ⟨``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.specializeMemRec,
    capstone, memoryBinding, encodeSkeletonAtBind⟩,
  ⟨``Nock.NockVMROM.Thm54.TemplateAxisCounting.specialize_memory_axis_of_active,
    capstone, memoryBinding, encodeSkeletonAtBind⟩,
  -- hostile track (off the capstone)
  ⟨``Nock.NockVMROM.Thm54.HostileSkeletonDecoding.decodeMemoryRowIn,
    hostileOff, hostileDecode, joinNotDecode⟩,
  ⟨``Nock.NockVMROM.Thm54.HostileSkeletonDecoding.decodeMemoryRowIn_bounded,
    hostileOff, hostileDecode, joinNotDecode⟩,
  ⟨``Nock.NockVMROM.Thm54.StrategyOfTraces.memRecJoin, hostileOff, computeVcomp, computeStays⟩,
  ⟨``Nock.NockVMROM.Thm54.WrapFixesVcomp.wrap_fixes_vcomp_row, hostileOff, computeVcomp, computeStays⟩,
  ⟨``Nock.NockVMROM.Thm54.MemoryWalkRoots.read_root_noun_eq_record_root,
    hostileOff, paperAccounting, formRRetype⟩,
  ⟨``Nock.NockVMROM.Thm54.FamilyMemoryRows.eqBlk_verify_child_of_paper,
    hostileOff, paperAccounting, formRRetype⟩,
  ⟨``Nock.NockVMROM.Thm54.FamilyMemoryRows.eqBlk_read_root_of_paper,
    hostileOff, paperAccounting, formRRetype⟩,
  ⟨``Nock.NockVMROM.Thm54.WrapMemoryConjuncts.wrap_preserves_mem_ts, hostileOff, column, unchanged⟩,
  ⟨``Nock.NockVMROM.Thm54.RemainingIoObstructions.specializeMemRec_active_zero_ts,
    hostileOff, column, unchanged⟩]

/-- The only BROKEN-under-R1 entries are the two hostile decoders. -/
theorem broken_entries :
    (inventory.filter (fun r => r.supply == .joinNotDecode)).map Reader.name =
      [``Nock.NockVMROM.Thm54.HostileSkeletonDecoding.decodeMemoryRowIn,
       ``Nock.NockVMROM.Thm54.HostileSkeletonDecoding.decodeMemoryRowIn_bounded] := by
  decide

/-- No capstone entry needs a hostile decode. -/
theorem capstone_entries_need_no_decode :
    (inventory.filter (fun r => r.layer == .capstone && r.supply == .joinNotDecode)) = [] := by
  decide

def post28thOffCapstone : List Name :=
  [``Nock.NockVMROM.Thm54.MemoryPaperFactorization.poleSource_eval_eq_compress,
   ``Nock.NockVMROM.Thm54.MemoryPaperFactorization.canonical_paperAggregator,
   ``Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.canonical_denominatorPinMixed,
   ``Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.exactMemoryRowEnv_trace_ge35,
   ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.ComputeRowTemplate.bindMemRec_specialize_active,
   ``Nock.NockVMROM.Thm54.HonestCommitment.memory_specialize_placeholder_eq,
   ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.SemanticTimestampSkeleton.tableRecordAt_eq_of_bind]

/-- Asserted below as the new truth. -/
def post28thNoAxisRead : List Name :=
  [``Nock.Reified.memEqBlkExprs_verify_child_sound,
   ``Nock.NockVMROM.Thm54.TraceGen.annotatedVerifyPub_eqBlk,
   ``Nock.NockVMROM.Thm54.HonestCommitment.memory_specialize_placeholder_eq,
   ``Nock.NockVMROM.Thm54.MemoryWalkRoots.read_root_noun_eq_record_root,
   ``Nock.NockVMROM.Thm54.MemoryPaperFactorization.poleSource_eval_eq_compress,
   ``Nock.NockVMROM.Thm54.MemoryPaperFactorization.canonical_paperAggregator]

-- Certify every inventory entry: it exists, it reads `MemRec.axis` directly, and its layer is
-- right (capstone entries in the capstone closure, hostile entries not).
run_cmd do
  let env ← getEnv
  let cap := closureOf env capstoneName
  for n in post28thOffCapstone do
    unless inventory.any (fun r => r.name == n && r.layer == .capstone) do
      throwError m!"drift list: {n} is not a capstone inventory entry"
  for n in post28thNoAxisRead do
    unless inventory.any (fun r => r.name == n) do
      throwError m!"drift list: {n} is not an inventory entry"
  for r in inventory do
    unless env.contains r.name do throwError m!"{r.name} does not exist"
    if post28thNoAxisRead.contains r.name then
      if readsAxis env r.name then throwError m!"{r.name} reads MemRec.axis again (post-28th drift)"
    else
      unless readsAxis env r.name do throwError m!"{r.name} does not read MemRec.axis"
    match r.layer with
    | .capstone =>
      if post28thOffCapstone.contains r.name then
        if cap.contains r.name then
          throwError m!"{r.name} is back in capstone closure (post-28th drift)"
      else
        unless cap.contains r.name do throwError m!"{r.name} not in capstone closure"
    | .hostileOff => pure ()

/-! ## §3 Composition on live -/

section Composition

open Polynomial
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.FamilyComputeRows

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The decoded memory row's axis slot is the memory chip's role 25 — no encode in the decoder.
Under Form R that role is `T` (lane `MemoryTable.eqBlk` reads `p.mem.axis` as `T`; lane
`ExecOfTraces.decodeMemPub` adds `cprime? := some (trace 57)`, `lambda? := some (chal 8)`). -/
theorem decodeMemPub_axis_is_role25
    (Qm : Fin P.memoryChip.rap.w → F[X]) (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (ExecOfTraces.decodeMemPub P Qm c i).mem.axis = (memorySourceEnvAt P c Qm i).trace 25 :=
  rfl

example (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : ExecOfTraces.TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0) :
    (StrategyOfTracesCore.strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda =
      (StrategyOfTracesCore.execTemplateOfTraces P Qc Qm c h (nprSeed c.1)).specialize (alphaM c.1)
        c.2.2.2.lambda :=
  AcceptedContentOfTracesFill.specializedExec_eq P Qc Qm c h hz

end Composition

section Skeleton

open Nock.NockVMROM.Thm54
open Nock.Walk
variable {K : Type} [Field K]

/-- Decoded compute records are `V_comp`-semantic: OP0's second request carries `f_t.leaf`, the
Nock-axis atom. -/
theorem expectedMr2_s0_axis (inp : ComputeTable.Inputs K) (pub : ComputeTable.Pub K)
    (dec : ComputeTable.Dec K) (h : pub.state = .s0) :
    (OptimizedComputeCodec.expectedMr2 inp pub dec).axis = dec.f_t.leaf := by
  simp [OptimizedComputeCodec.expectedMr2, h]

/-- The hostile memory skeleton decodes the row's axis slot as the Nock axis
(`HostileSkeletonDecoding.lean:269`). -/
theorem decodeMemoryRowIn_readRoot_axis (q : ℕ)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K)))
    (data : MemoryTable.DTmem K) (child : NTree (MemoryTable.MState × MemoryTable.DTmem K))
    (h : memoryMemRecKind MemoryTable.MState.read_root = .active) :
    ((HostileSkeletonDecoding.decodeMemoryRowIn q forest
        (.node (.read_root, data) [child])).memoryRecord h).axis =
      HostileSkeletonDecoding.leafAtomOf q data.2.mem.axis :=
  rfl

/-- `leafAtomOf` recovers a cast below the window. -/
theorem leafAtomOf_natCast {q a : ℕ} (hq : q ≤ ringChar K) (ha : a < q) :
    HostileSkeletonDecoding.leafAtomOf q (a : K) = a := by
  have hex : ∃ k : ℕ, k < q ∧ (k : K) = (a : K) := ⟨a, ha, rfl⟩
  have hspec := HostileSkeletonDecoding.leafAtomOf_cast (K := K) hex
  have hlt := HostileSkeletonDecoding.leafAtomOf_lt (K := K) hex
  have hmod : HostileSkeletonDecoding.leafAtomOf q (a : K) ≡ a [MOD ringChar K] :=
    (CharP.natCast_eq_natCast (R := K) (p := ringChar K)).mp hspec
  exact Nat.ModEq.eq_of_lt_of_lt hmod (lt_of_lt_of_le hlt hq) (lt_of_lt_of_le ha hq)

end Skeleton

section Concrete

open Nock.NockVMROM.Thm54
open Nock.RedTeam.Batch588

/-- **Under R1 the decoded skeleton reads `T`, not `a`.**  Honest axis `5` at `λ = 2` in `𝔽_7`:
the R1 row holds `T = 4` in the axis slot; `decodeMemoryRowIn` would put `leafAtomOf 7 4 = 4`
into the skeleton's `MemRecSkeleton.axis`, while the compute request (V_comp) says `5`. -/
theorem r1_skeleton_reads_T_not_a :
    HostileSkeletonDecoding.leafAtomOf 7 (LformRT (2 : Z7) 5) = 4 ∧ (4 : ℕ) ≠ 5 := by
  have hT : LformRT (2 : Z7) 5 = ((4 : ℕ) : Z7) := by
    simp only [LformRT]; decide
  refine ⟨?_, by decide⟩
  rw [hT]
  exact leafAtomOf_natCast (K := Z7) (by simp [ZMod.ringChar_zmod_n]) (by decide)

/-- **`BindMemRec` fails for an honest R1 row** bound to its true skeleton (axis `5`): the row's
axis slot is `T = 4`.  So `SemanticStrategy.BindMemRec`'s memory use (via `BindMemoryRow`,
`SemanticStrategy.lean:156-166`) must be restated as an encode of the skeleton at bind time. -/
theorem r1_bindMemRec_fails (z : Z7) (s : SemanticStrategy.MemRecSkeleton)
    (hs : s.axis = 5) (r : ComputeTable.MemRec Z7) (hr : r.axis = LformRT (2 : Z7) 5) :
    ¬ SemanticStrategy.BindMemRec z s r := by
  rintro ⟨-, -, hax⟩
  rw [hr, hs] at hax
  revert hax
  simp only [LformRT]
  decide

end Concrete

/-! ## §4 The lane's double encode, reproduced -/

section DoubleEncode

open Nock.RedTeam.Batch588

/-- A semantic compute request with Nock axis `5` (any fingerprints, `ts = 3`), `𝔽_7`. -/
def semRec : ComputeTable.MemRec Z7 := ⟨0, 0, 5, 3⟩

/-- The R1 memory row the deployed chip holds for it at `λ = 2` (`T = 4`, `C' = 5`). -/
noncomputable def rowR1 : MemRow Z7 := buildRow 2 5 semRec

theorem rowR1_values : rowR1.record.axis = 4 ∧ rowR1.cprime = 5 := by
  simp only [rowR1, buildRow, semRec, LformRT, LformRC, pwScale_Z7]
  decide

/-- **R1 composes.**  Reading the row gives exactly the compute side's single encode. -/
theorem row_read_agrees : rowR1.io = LencRecFormR semRec 2 :=
  build_encode_eq_io_encode (K := Z7) 2 (by simp [ZMod.ringChar_zmod_n]) semRec rfl

/-- **The lane's `derivedResponseIO` on a decoded row double-encodes.**  Lane
`Language.lean:54-56` maps `encRecFormR · formRDefault` over `rawResponses`, i.e. over the row's
`mem` (axis slot `T = 4`) and ignores the row's `C'`.  It recomputes `C'` from `nockAxisOf T = 4`:
`C'(4) = 4`, not the row's `5`.  So response IO ≠ the row and ≠ the matching compute request. -/
theorem double_encode_breaks :
    LencRecFormR rowR1.record 2 ≠ rowR1.io ∧ LencRecFormR rowR1.record 2 ≠ LencRecFormR semRec 2 := by
  have h4 : rowR1.record.axis = ((4 : ℕ) : Z7) := by
    rw [rowR1_values.1]; rfl
  have hn : LnockAxisOf rowR1.record.axis = 4 := by
    rw [h4]; exact LnockAxisOf_natCast (K := Z7) (a := 4) (by simp [ZMod.ringChar_zmod_n])
  have hslot : LencRecFormR rowR1.record (2 : Z7) 8 = LformRC (2 : Z7) 4 := by
    simp only [LencRecFormR, LencRecC, hn]
    rfl
  have hC4 : LformRC (2 : Z7) 4 = 4 := by
    simp only [LformRC, pwScale_Z7]; decide
  have hrow : rowR1.io 8 = 5 := by
    simp [MemRow.io, LencRecC, rowR1_values.2]
  have hne : LencRecFormR rowR1.record 2 ≠ rowR1.io := by
    intro h
    have := congrFun h 8
    rw [hslot, hC4, hrow] at this
    exact absurd this (by decide)
  exact ⟨hne, by rw [← row_read_agrees]; exact hne⟩

end DoubleEncode

end Nock.RedTeam.Batch587

#print axioms Nock.RedTeam.Batch587.broken_entries
#print axioms Nock.RedTeam.Batch587.capstone_entries_need_no_decode
#print axioms Nock.RedTeam.Batch587.decodeMemPub_axis_is_role25
#print axioms Nock.RedTeam.Batch587.expectedMr2_s0_axis
#print axioms Nock.RedTeam.Batch587.decodeMemoryRowIn_readRoot_axis
#print axioms Nock.RedTeam.Batch587.leafAtomOf_natCast
#print axioms Nock.RedTeam.Batch587.r1_skeleton_reads_T_not_a
#print axioms Nock.RedTeam.Batch587.r1_bindMemRec_fails
#print axioms Nock.RedTeam.Batch587.rowR1_values
#print axioms Nock.RedTeam.Batch587.row_read_agrees
#print axioms Nock.RedTeam.Batch587.double_encode_breaks
