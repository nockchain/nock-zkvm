/-
  Nock/NockVMROM/Thm54/TraceGen/Row.lean

  The pure-data records the
  three-phase worker emits, carrying NO proof fields so the generator stays computable.

  A `GenComputeRow`/`GenMemoryRow` is exactly the seed-free data of a committed
  `HonestCommitment.ComputeNode`/`MemoryNode` (skeleton row, committed Nat timestamp exponents,
  and the rendered execution row) plus, on the compute side, the value-keyed service requests the
  memoryless matcher will discharge.  Projecting `GenComputeRow.node`
  drops the requests and yields the honest-commitment node verbatim, so a generated trace can feed
  the existing `HonestCommitment.Data` machinery unchanged.

  `GenError` is the failure alphabet of the generator (`Except GenError`, never `Option`): the
  evaluator `evalFBy` succeeds on `OP_11`, but `ComputeTable.State` carries no `s10`/`s11`
  (`ComputeTable.lean:142`), so out-of-ROM opcodes are `.error notROM` rather than a silent `none`.

  `ServiceReq` is the value-keyed (memoryless, positionless) request record:
  a committed request is matched against the served memory forest by fingerprint VALUE at seed `z`,
  never by a committed-line index.
-/
import Nock.NockVMROM.Thm54.HonestCommitmentNodes

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

/-- The generator's failure alphabet.  `notROM` is the `OP_10`/`OP_11`
    out-of-ROM decline; `outOfFuel` the fuel-`0` stop; `atomOutOfRange` an atom `≥ q`; `crash`
    a Nock evaluation crash; `malformed` an opcode this stage does not yet emit. -/
inductive GenError
  | outOfFuel | notROM | atomOutOfRange | crash | malformed
deriving DecidableEq, Repr

/-- A value-keyed memory service request.  It records the committed nouns
    (`root`, `child`) opened at Nat `axis`.  The matcher keys on the seed-`z` fingerprint VALUE of
    `root`/`child`, never on any committed-line pointer (memoryless/positionless, §0).

    ⚠️ **`ts` is dead, and for slots 1 and 2 it is WRONG.**  This docstring used to describe `ts`
    as "the honest timestamp `ts = ln_prev · α` at which the compute row emitted it".  It is not:
    `renderNode` (`Gen.lean:2884`) sets `requests := g.requests.map (fun r => { r with
    ts := α ^ g.stamp.recordExponent 0 })` — index `0`, **uniformly for all eleven states**, so a
    row emitting two or three records stamps every request with the *first* slot's exponent.  The
    per-record timestamps live in `mr1/mr2/mr3.ts`, written inside `renderOp*Row z α g.stamp
    g.skel`, and the committed memory forest reads `getRecordExp g.stamp i` via `extractNodeReqs`,
    never this field.  So nothing depends on it and nothing is broken — but do not read `ts` as a
    timestamp. -/
structure ServiceReq (K : Type) [Field K] where
  root : Noun
  child : Noun
  axis : ℕ
  ts : K

/-- One emitted compute row: its pre-seed skeleton, committed Nat timestamp exponents, the rendered
    execution row, and the value-keyed requests it issued.  A pure-data record — no proof field. -/
structure GenComputeRow (K : Type) [Field K] where
  skel : ComputeRowSkeleton
  stamp : ComputeTimestampRow
  row : ComputeTable.State × ComputeTable.DTcomp K
  requests : List (ServiceReq K)

/-- Forget the requests: the honest-commitment compute node this generated row commits. -/
def GenComputeRow.node {K : Type} [Field K] (g : GenComputeRow K) :
    HonestCommitment.ComputeNode K :=
  ⟨g.skel, g.stamp, g.row⟩

@[simp] theorem GenComputeRow.node_skel {K : Type} [Field K] (g : GenComputeRow K) :
    g.node.skel = g.skel := rfl
@[simp] theorem GenComputeRow.node_stamp {K : Type} [Field K] (g : GenComputeRow K) :
    g.node.stamp = g.stamp := rfl
@[simp] theorem GenComputeRow.node_row {K : Type} [Field K] (g : GenComputeRow K) :
    g.node.row = g.row := rfl

/-- One emitted memory row: its pre-seed skeleton, committed Nat timestamp exponent, and the
    rendered execution row.  A pure-data record — no proof field. -/
structure GenMemoryRow (K : Type) [Field K] where
  skel : MemoryRowSkeleton
  stamp : MemoryTimestampRow
  row : MemoryTable.MState × MemoryTable.DTmem K

/-- Forget nothing: the honest-commitment memory node this generated row commits. -/
def GenMemoryRow.node {K : Type} [Field K] (g : GenMemoryRow K) :
    HonestCommitment.MemoryNode K :=
  ⟨g.skel, g.stamp, g.row⟩

@[simp] theorem GenMemoryRow.node_skel {K : Type} [Field K] (g : GenMemoryRow K) :
    g.node.skel = g.skel := rfl
@[simp] theorem GenMemoryRow.node_stamp {K : Type} [Field K] (g : GenMemoryRow K) :
    g.node.stamp = g.stamp := rfl
@[simp] theorem GenMemoryRow.node_row {K : Type} [Field K] (g : GenMemoryRow K) :
    g.node.row = g.row := rfl

/-- A fully generated trace of a ROM program: the semantic nouns, the fuel it ran under, the
    committed compute node tree, and the committed memory node forest.  Projecting the two node
    fields through `GenComputeRow.node`/`GenMemoryRow.node` yields exactly the trees a
    `HonestCommitment.Data` commits. -/
structure GenTrace (F K : Type) [Field F] [Field K] [Algebra F K] where
  subject : Noun
  formula : Noun
  result : Noun
  fuel : ℕ
  computeNodes : NTree (GenComputeRow K)
  memoryNodes : List (NTree (GenMemoryRow K))

end Nock.NockVMROM.Thm54.TraceGen
