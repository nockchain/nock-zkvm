/-
  Nock/NockVMROM/Thm54/TraceGen/Op0Gen.lean

  Phase 3, the OP0 (axis) vertical slice: the trace generator's compute skeletons and the
  **two-serviced-root axis-descent served memory forest** for the nonterminal program
  `*[subjectS [4 [0 2]]]` — the `OP_4` parent whose single recursive call is the
  genuine `OP_0` axis read `/[2 subjectS] = resultS`.

  The load-bearing new piece (design spec §5, §7) is `genOp0MemForest`: unlike OP1/cons — whose
  served forests are single-rooted — the OP0 forest has TWO serviced roots:

  * root `A`, rooted at `parentFormulaS`, serves the `OP_4` record `parentRecordS` and the `OP_0`
    formula-open record `servedFormulaRecord` through nested `read_root`/`verify_child` pairs
    (nine rows);
  * root `B`, rooted at the SUBJECT `subjectS`, serves the actual slot record `servedRecord` on a
    genuine **left** axis descent `axisPath 2 = [false]` (five rows).

  Everything is reproduced against the proven `MultiRootHonestCommitment` committed node trees.  The
  skeletons and committed records are the positionless commitment (shared verbatim); the generated
  content is the field-valued served-cell fingerprints, emitted through the computable `encC`
  (`= enc`, `Encode.encC_eq`) at the repaired seed `servedSeed = -1` (never the F97 default seed `1`,
  which admits no size window — `NonterminalServedRow.no_sizeWindow_at_fixtureSeed`).

  * `genSkelOp0_eq` / `genSkelOp4_eq` — the generic skeleton emitters reproduce the committed
    `servedSkeletonRow` / `parentSkeletonRow`.

  * `gen_op0MemForest_eq` — the `.node`-projection of the generated two-root forest is exactly the
    committed `memoryNodesM = [rootANodeTree, rootBNodeTree]`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Gen
import Nock.NockVMROM.Thm54.MultiRootHonestCommitment

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.TraceGen

open scoped Classical
open Nock Nock.Noun Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)

/-! ## A. The compute skeletons

    `genSkelOp0` (the `OP_0` emitter) lives in `Gen.lean` beside `genSkelOp1`/`genSkelCons`, since
    `genComputeSkeleton`'s new `OP_0` DFS arm consumes it; `genSkelOp0_eq` below shows it reproduces
    the committed served skeleton. -/

/-- The generic `OP_0` emitter, instantiated at the fixture nouns, is the committed served
    skeleton. -/
theorem genSkelOp0_eq :
    genSkelOp0 subjectS formulaS headS tailS resultS 2 = servedSkeletonRow := by
  rfl

/-- The generic `OP_4` emitter, instantiated at the fixture nouns, is the committed parent
    skeleton. -/
theorem genSkelOp4_eq :
    genSkelOp4 subjectS parentFormulaS parentHeadS formulaS subjectS formulaS resultS parentResultS
      = parentSkeletonRow := by
  rfl

/-! ## B. The generated served-forest cells via `encC` -/

/-- Root `A` served cells: the formula-opening descent on `parentFormulaS`. -/
-- Form R row-level cells at `λ = formRDefault`, written from their children exactly as the
-- committed `MultiRootServedFixture` cells.
def gATailCell (z : K97cubic) : MemoryTable.Cell K97cubic := ⟨encC z tailS, 0, 0⟩
def gAInnerVerifyCell (z : K97cubic) : MemoryTable.Cell K97cubic :=
  rowVerifyCell (encC z tailS) (gATailCell z) servedFormulaRecord.ts
def gAInnerHeadCell (z : K97cubic) : MemoryTable.Cell K97cubic := ⟨encC z headS, 0, 0⟩
def gAInnerLiftCell (z : K97cubic) : MemoryTable.Cell K97cubic :=
  rowDecCell (encC z formulaS) (gAInnerHeadCell z) (gAInnerVerifyCell z)
def gAOuterVerifyCell (z : K97cubic) : MemoryTable.Cell K97cubic :=
  rowVerifyCell (encC z formulaS) (gAInnerLiftCell z) parentRecordS.ts
def gAInnerRootCell (z : K97cubic) : MemoryTable.Cell K97cubic :=
  rowReadCell (encC z formulaS) (gAOuterVerifyCell z) servedFormulaRecord
def gAHeadCell (z : K97cubic) : MemoryTable.Cell K97cubic := ⟨encC z parentHeadS, 0, 0⟩
def gALiftCell (z : K97cubic) : MemoryTable.Cell K97cubic :=
  rowDecCell (encC z parentFormulaS) (gAHeadCell z) (gAInnerRootCell z)
def gARootCell (z : K97cubic) : MemoryTable.Cell K97cubic :=
  rowReadCell (encC z parentFormulaS) (gALiftCell z) parentRecordS

/-- Root `B` served cells: the left axis descent on `subjectS`. -/
def gBResultHaltCell (z : K97cubic) : MemoryTable.Cell K97cubic := ⟨encC z resultS, 0, 0⟩
def gBTailHaltCell (z : K97cubic) : MemoryTable.Cell K97cubic := ⟨encC z bTailNoun, 0, 0⟩
def gBVerifyCell (z : K97cubic) : MemoryTable.Cell K97cubic :=
  rowVerifyCell (encC z resultS) (gBResultHaltCell z) servedRecord.ts
def gBLiftCell (z : K97cubic) : MemoryTable.Cell K97cubic :=
  rowDecCell (encC z subjectS) (gBVerifyCell z) (gBTailHaltCell z)
def gBRootCell (z : K97cubic) : MemoryTable.Cell K97cubic :=
  rowReadCell (encC z subjectS) (gBLiftCell z) servedRecord

/-! ## C. The fourteen generated served pubs -/

def gAReadOuterPub (z : K97cubic) : MemoryTable.Pub K97cubic where
  st := .read_root
  pt := gARootCell z
  lc := gALiftCell z
  rc := MemoryTable.Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := parentRecordS
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := -1

def gADecomposeOuterPub (z : K97cubic) : MemoryTable.Pub K97cubic where
  st := .decompose
  pt := gALiftCell z
  lc := gAHeadCell z
  rc := gAInnerRootCell z
  lcSt := .halt
  rcSt := .read_root
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 0

def gAHeadHaltPub (z : K97cubic) : MemoryTable.Pub K97cubic where
  st := .halt
  pt := gAHeadCell z
  lc := MemoryTable.Cell.zero
  rc := MemoryTable.Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 0

def gAReadInnerPub (z : K97cubic) : MemoryTable.Pub K97cubic where
  st := .read_root
  pt := gAInnerRootCell z
  lc := gAOuterVerifyCell z
  rc := MemoryTable.Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := servedFormulaRecord
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 1

def gAVerifyOuterPub (z : K97cubic) : MemoryTable.Pub K97cubic where
  st := .verify_child
  pt := gAOuterVerifyCell z
  lc := gAInnerLiftCell z
  rc := MemoryTable.Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := parentRecordS
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 1

def gADecomposeInnerPub (z : K97cubic) : MemoryTable.Pub K97cubic where
  st := .decompose
  pt := gAInnerLiftCell z
  lc := gAInnerHeadCell z
  rc := gAInnerVerifyCell z
  lcSt := .halt
  rcSt := .verify_child
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 1
  icur := 1

def gAInnerHeadHaltPub (z : K97cubic) : MemoryTable.Pub K97cubic where
  st := .halt
  pt := gAInnerHeadCell z
  lc := MemoryTable.Cell.zero
  rc := MemoryTable.Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 1
  icur := 1

def gAVerifyInnerPub (z : K97cubic) : MemoryTable.Pub K97cubic where
  st := .verify_child
  pt := gAInnerVerifyCell z
  lc := gATailCell z
  rc := MemoryTable.Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := servedFormulaRecord
  lambda? := some MemoryTable.formRDefault
  ipre := 1
  icur := 0

def gATailHaltPub (z : K97cubic) : MemoryTable.Pub K97cubic where
  st := .halt
  pt := gATailCell z
  lc := MemoryTable.Cell.zero
  rc := MemoryTable.Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 0

def gBReadPub (z : K97cubic) : MemoryTable.Pub K97cubic where
  st := .read_root
  pt := gBRootCell z
  lc := gBLiftCell z
  rc := MemoryTable.Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := servedRecord
  lambda? := some MemoryTable.formRDefault
  ipre := -1
  icur := 0

def gBDecomposePub (z : K97cubic) : MemoryTable.Pub K97cubic where
  st := .decompose
  pt := gBLiftCell z
  lc := gBVerifyCell z
  rc := gBTailHaltCell z
  lcSt := .verify_child
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 0

def gBVerifyPub (z : K97cubic) : MemoryTable.Pub K97cubic where
  st := .verify_child
  pt := gBVerifyCell z
  lc := gBResultHaltCell z
  rc := MemoryTable.Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := servedRecord
  lambda? := some MemoryTable.formRDefault
  ipre := 1
  icur := 0

def gBResultHaltPub (z : K97cubic) : MemoryTable.Pub K97cubic where
  st := .halt
  pt := gBResultHaltCell z
  lc := MemoryTable.Cell.zero
  rc := MemoryTable.Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 1
  icur := 1

def gBTailHaltPub (z : K97cubic) : MemoryTable.Pub K97cubic where
  st := .halt
  pt := gBTailHaltCell z
  lc := MemoryTable.Cell.zero
  rc := MemoryTable.Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 0

/-! ## D. Each generated pub collapses to the committed pub via `encC_eq` -/

theorem gAReadOuterPub_eq : gAReadOuterPub servedSeed = aReadOuterPubA := by
  simp only [gAReadOuterPub, aReadOuterPubA, aReadOuterPub,
    gATailCell, gAInnerVerifyCell, gAInnerHeadCell, gAInnerLiftCell, gAOuterVerifyCell,
    gAInnerRootCell, gAHeadCell, gALiftCell, gARootCell, gBResultHaltCell, gBTailHaltCell,
    gBVerifyCell, gBLiftCell, gBRootCell, aTailCell, aInnerVerifyCell, aInnerHeadCell,
    aInnerLiftCell, aOuterVerifyCell, aInnerRootCell, aHeadCell, aLiftCell, aRootCell,
    bResultHaltCell, bTailHaltCell, bVerifyCell, bLiftCell, bRootCell,
     gARootCell, gALiftCell, aRootCell, aLiftCell,
    encS, encC_eq]

theorem gADecomposeOuterPub_eq : gADecomposeOuterPub servedSeed = aDecomposeOuterPub := by
  simp only [gADecomposeOuterPub, aDecomposeOuterPub,
    gATailCell, gAInnerVerifyCell, gAInnerHeadCell, gAInnerLiftCell, gAOuterVerifyCell,
    gAInnerRootCell, gAHeadCell, gALiftCell, gARootCell, gBResultHaltCell, gBTailHaltCell,
    gBVerifyCell, gBLiftCell, gBRootCell, aTailCell, aInnerVerifyCell, aInnerHeadCell,
    aInnerLiftCell, aOuterVerifyCell, aInnerRootCell, aHeadCell, aLiftCell, aRootCell,
    bResultHaltCell, bTailHaltCell, bVerifyCell, bLiftCell, bRootCell,
     gALiftCell, gAHeadCell, gAInnerRootCell,
    aLiftCell, aHeadCell, aInnerRootCell, encS, encC_eq]

theorem gAHeadHaltPub_eq : gAHeadHaltPub servedSeed = aHeadHaltPub := by
  simp only [gAHeadHaltPub, aHeadHaltPub,
    gATailCell, gAInnerVerifyCell, gAInnerHeadCell, gAInnerLiftCell, gAOuterVerifyCell,
    gAInnerRootCell, gAHeadCell, gALiftCell, gARootCell, gBResultHaltCell, gBTailHaltCell,
    gBVerifyCell, gBLiftCell, gBRootCell, aTailCell, aInnerVerifyCell, aInnerHeadCell,
    aInnerLiftCell, aOuterVerifyCell, aInnerRootCell, aHeadCell, aLiftCell, aRootCell,
    bResultHaltCell, bTailHaltCell, bVerifyCell, bLiftCell, bRootCell,
     gAHeadCell, aHeadCell, encS, encC_eq]

theorem gAReadInnerPub_eq : gAReadInnerPub servedSeed = aReadInnerPubA := by
  simp only [gAReadInnerPub, aReadInnerPubA, aReadInnerPub,
    gATailCell, gAInnerVerifyCell, gAInnerHeadCell, gAInnerLiftCell, gAOuterVerifyCell,
    gAInnerRootCell, gAHeadCell, gALiftCell, gARootCell, gBResultHaltCell, gBTailHaltCell,
    gBVerifyCell, gBLiftCell, gBRootCell, aTailCell, aInnerVerifyCell, aInnerHeadCell,
    aInnerLiftCell, aOuterVerifyCell, aInnerRootCell, aHeadCell, aLiftCell, aRootCell,
    bResultHaltCell, bTailHaltCell, bVerifyCell, bLiftCell, bRootCell,
     gAInnerRootCell, gAOuterVerifyCell,
    aInnerRootCell, aOuterVerifyCell, encS, encC_eq]

theorem gAVerifyOuterPub_eq : gAVerifyOuterPub servedSeed = aVerifyOuterPubA := by
  simp only [gAVerifyOuterPub, aVerifyOuterPubA, aVerifyOuterPub,
    gATailCell, gAInnerVerifyCell, gAInnerHeadCell, gAInnerLiftCell, gAOuterVerifyCell,
    gAInnerRootCell, gAHeadCell, gALiftCell, gARootCell, gBResultHaltCell, gBTailHaltCell,
    gBVerifyCell, gBLiftCell, gBRootCell, aTailCell, aInnerVerifyCell, aInnerHeadCell,
    aInnerLiftCell, aOuterVerifyCell, aInnerRootCell, aHeadCell, aLiftCell, aRootCell,
    bResultHaltCell, bTailHaltCell, bVerifyCell, bLiftCell, bRootCell,
     gAOuterVerifyCell, gAInnerLiftCell,
    aOuterVerifyCell, aInnerLiftCell, encS, encC_eq]

theorem gADecomposeInnerPub_eq : gADecomposeInnerPub servedSeed = aDecomposeInnerPub := by
  simp only [gADecomposeInnerPub, aDecomposeInnerPub,
    gATailCell, gAInnerVerifyCell, gAInnerHeadCell, gAInnerLiftCell, gAOuterVerifyCell,
    gAInnerRootCell, gAHeadCell, gALiftCell, gARootCell, gBResultHaltCell, gBTailHaltCell,
    gBVerifyCell, gBLiftCell, gBRootCell, aTailCell, aInnerVerifyCell, aInnerHeadCell,
    aInnerLiftCell, aOuterVerifyCell, aInnerRootCell, aHeadCell, aLiftCell, aRootCell,
    bResultHaltCell, bTailHaltCell, bVerifyCell, bLiftCell, bRootCell,
     gAInnerLiftCell, gAInnerHeadCell,
    gAInnerVerifyCell, aInnerLiftCell, aInnerHeadCell, aInnerVerifyCell, encS, encC_eq]

theorem gAInnerHeadHaltPub_eq : gAInnerHeadHaltPub servedSeed = aInnerHeadHaltPub := by
  simp only [gAInnerHeadHaltPub, aInnerHeadHaltPub,
    gATailCell, gAInnerVerifyCell, gAInnerHeadCell, gAInnerLiftCell, gAOuterVerifyCell,
    gAInnerRootCell, gAHeadCell, gALiftCell, gARootCell, gBResultHaltCell, gBTailHaltCell,
    gBVerifyCell, gBLiftCell, gBRootCell, aTailCell, aInnerVerifyCell, aInnerHeadCell,
    aInnerLiftCell, aOuterVerifyCell, aInnerRootCell, aHeadCell, aLiftCell, aRootCell,
    bResultHaltCell, bTailHaltCell, bVerifyCell, bLiftCell, bRootCell,
     gAInnerHeadCell, aInnerHeadCell, encS, encC_eq]

theorem gAVerifyInnerPub_eq : gAVerifyInnerPub servedSeed = aVerifyInnerPubA := by
  simp only [gAVerifyInnerPub, aVerifyInnerPubA, aVerifyInnerPub,
    gATailCell, gAInnerVerifyCell, gAInnerHeadCell, gAInnerLiftCell, gAOuterVerifyCell,
    gAInnerRootCell, gAHeadCell, gALiftCell, gARootCell, gBResultHaltCell, gBTailHaltCell,
    gBVerifyCell, gBLiftCell, gBRootCell, aTailCell, aInnerVerifyCell, aInnerHeadCell,
    aInnerLiftCell, aOuterVerifyCell, aInnerRootCell, aHeadCell, aLiftCell, aRootCell,
    bResultHaltCell, bTailHaltCell, bVerifyCell, bLiftCell, bRootCell,
     gAInnerVerifyCell, gATailCell,
    aInnerVerifyCell, aTailCell, encS, encC_eq]

theorem gATailHaltPub_eq : gATailHaltPub servedSeed = aTailHaltPub := by
  simp only [gATailHaltPub, aTailHaltPub,
    gATailCell, gAInnerVerifyCell, gAInnerHeadCell, gAInnerLiftCell, gAOuterVerifyCell,
    gAInnerRootCell, gAHeadCell, gALiftCell, gARootCell, gBResultHaltCell, gBTailHaltCell,
    gBVerifyCell, gBLiftCell, gBRootCell, aTailCell, aInnerVerifyCell, aInnerHeadCell,
    aInnerLiftCell, aOuterVerifyCell, aInnerRootCell, aHeadCell, aLiftCell, aRootCell,
    bResultHaltCell, bTailHaltCell, bVerifyCell, bLiftCell, bRootCell,
     gATailCell, aTailCell, encS, encC_eq]

theorem gBReadPub_eq : gBReadPub servedSeed = bReadPubA := by
  simp only [gBReadPub, bReadPubA, bReadPub,
    gATailCell, gAInnerVerifyCell, gAInnerHeadCell, gAInnerLiftCell, gAOuterVerifyCell,
    gAInnerRootCell, gAHeadCell, gALiftCell, gARootCell, gBResultHaltCell, gBTailHaltCell,
    gBVerifyCell, gBLiftCell, gBRootCell, aTailCell, aInnerVerifyCell, aInnerHeadCell,
    aInnerLiftCell, aOuterVerifyCell, aInnerRootCell, aHeadCell, aLiftCell, aRootCell,
    bResultHaltCell, bTailHaltCell, bVerifyCell, bLiftCell, bRootCell,
     gBRootCell, gBLiftCell, bRootCell, bLiftCell, encS, encC_eq]

theorem gBDecomposePub_eq : gBDecomposePub servedSeed = bDecomposePub := by
  simp only [gBDecomposePub, bDecomposePub,
    gATailCell, gAInnerVerifyCell, gAInnerHeadCell, gAInnerLiftCell, gAOuterVerifyCell,
    gAInnerRootCell, gAHeadCell, gALiftCell, gARootCell, gBResultHaltCell, gBTailHaltCell,
    gBVerifyCell, gBLiftCell, gBRootCell, aTailCell, aInnerVerifyCell, aInnerHeadCell,
    aInnerLiftCell, aOuterVerifyCell, aInnerRootCell, aHeadCell, aLiftCell, aRootCell,
    bResultHaltCell, bTailHaltCell, bVerifyCell, bLiftCell, bRootCell,
     gBLiftCell, gBVerifyCell, gBTailHaltCell,
    bLiftCell, bVerifyCell, bTailHaltCell, encS, encC_eq]

theorem gBVerifyPub_eq : gBVerifyPub servedSeed = bVerifyPubA := by
  simp only [gBVerifyPub, bVerifyPubA, bVerifyPub,
    gATailCell, gAInnerVerifyCell, gAInnerHeadCell, gAInnerLiftCell, gAOuterVerifyCell,
    gAInnerRootCell, gAHeadCell, gALiftCell, gARootCell, gBResultHaltCell, gBTailHaltCell,
    gBVerifyCell, gBLiftCell, gBRootCell, aTailCell, aInnerVerifyCell, aInnerHeadCell,
    aInnerLiftCell, aOuterVerifyCell, aInnerRootCell, aHeadCell, aLiftCell, aRootCell,
    bResultHaltCell, bTailHaltCell, bVerifyCell, bLiftCell, bRootCell,
     gBVerifyCell, gBResultHaltCell, bVerifyCell, bResultHaltCell,
    encS, encC_eq]

theorem gBResultHaltPub_eq : gBResultHaltPub servedSeed = bResultHaltPub := by
  simp only [gBResultHaltPub, bResultHaltPub,
    gATailCell, gAInnerVerifyCell, gAInnerHeadCell, gAInnerLiftCell, gAOuterVerifyCell,
    gAInnerRootCell, gAHeadCell, gALiftCell, gARootCell, gBResultHaltCell, gBTailHaltCell,
    gBVerifyCell, gBLiftCell, gBRootCell, aTailCell, aInnerVerifyCell, aInnerHeadCell,
    aInnerLiftCell, aOuterVerifyCell, aInnerRootCell, aHeadCell, aLiftCell, aRootCell,
    bResultHaltCell, bTailHaltCell, bVerifyCell, bLiftCell, bRootCell,
     gBResultHaltCell, bResultHaltCell, encS, encC_eq]

theorem gBTailHaltPub_eq : gBTailHaltPub servedSeed = bTailHaltPub := by
  simp only [gBTailHaltPub, bTailHaltPub,
    gATailCell, gAInnerVerifyCell, gAInnerHeadCell, gAInnerLiftCell, gAOuterVerifyCell,
    gAInnerRootCell, gAHeadCell, gALiftCell, gARootCell, gBResultHaltCell, gBTailHaltCell,
    gBVerifyCell, gBLiftCell, gBRootCell, aTailCell, aInnerVerifyCell, aInnerHeadCell,
    aInnerLiftCell, aOuterVerifyCell, aInnerRootCell, aHeadCell, aLiftCell, aRootCell,
    bResultHaltCell, bTailHaltCell, bVerifyCell, bLiftCell, bRootCell,
     gBTailHaltCell, bTailHaltCell, encS, encC_eq]

/-! ## E. The generated two-root served forest -/

/-- Package a served pub with its committed skeleton and Nat exponent into a `GenMemoryRow`. -/
def gMemRow (sk : MemoryRowSkeleton) (e : ℕ) (z : K97cubic) (pub : MemoryTable.Pub K97cubic) :
    GenMemoryRow K97cubic where
  skel := sk
  stamp := { state := sk.state, recordExponent := e }
  row := (sk.state, (memInputs z, pub))

/-- **`genOp0MemForest`.**  The fourteen-row, two-serviced-root axis-descent served memory forest of
    the program `*[subjectS [4 [0 2]]]`, emitted as pure data with `encC` fingerprints
.  Root `A` (nine rows) serves the `OP_4`/`OP_0` formula records on
    `parentFormulaS`; root `B` (five rows) serves the slot record on the SUBJECT `subjectS` via the
    left axis descent `axisPath 2 = [false]`.  This is the shared multi-root served-forest generator
    OP9 reuses. -/
def genOp0MemForest (z : K97cubic) : List (NTree (GenMemoryRow K97cubic)) :=
  [ .node (gMemRow dummyHaltSkel 0 z dummyHaltPubS) [],
    .node (gMemRow aReadOuterSkel 1 z (gAReadOuterPub z))
      [.node (gMemRow aDecomposeOuterSkel 0 z (gADecomposeOuterPub z))
        [.node (gMemRow aHeadHaltSkel 0 z (gAHeadHaltPub z)) [],
         .node (gMemRow aReadInnerSkel 2 z (gAReadInnerPub z))
          [.node (gMemRow aVerifyOuterSkel 1 z (gAVerifyOuterPub z))
            [.node (gMemRow aDecomposeInnerSkel 0 z (gADecomposeInnerPub z))
              [.node (gMemRow aInnerHeadHaltSkel 0 z (gAInnerHeadHaltPub z)) [],
               .node (gMemRow aVerifyInnerSkel 2 z (gAVerifyInnerPub z))
                [.node (gMemRow aTailHaltSkel 0 z (gATailHaltPub z)) []]]]]]],
    .node (gMemRow bReadSkel 3 z (gBReadPub z))
      [.node (gMemRow bDecomposeSkel 0 z (gBDecomposePub z))
        [.node (gMemRow bVerifySkel 3 z (gBVerifyPub z))
          [.node (gMemRow bResultHaltSkel 0 z (gBResultHaltPub z)) []],
         .node (gMemRow bTailHaltSkel 0 z (gBTailHaltPub z)) []]] ]

/-- **The generated served forest's `.node` projection is exactly `memoryNodesM`.**  Each of the
    fourteen generated rows collapses (via `encC_eq`) to the committed `MultiRootHonestCommitment`
    memory node; the two-root topology and the axis-`2` left descent of root `B` are reproduced
    verbatim. -/
theorem gen_op0MemForest_eq :
    (genOp0MemForest servedSeed).map (mapNTree GenMemoryRow.node) = memoryNodesM := by
  simp only [genOp0MemForest, List.map_cons, List.map_nil, mapNTree, GenMemoryRow.node, gMemRow,
    memInputs,
    memoryNodesM, dummyHaltNodeTree, rootANodeTree, aDecomposeOuterNodeTree, aHeadHaltNodeTree, aReadInnerNodeTree,
    aVerifyOuterNodeTree, aDecomposeInnerNodeTree, aInnerHeadHaltNodeTree, aVerifyInnerNodeTree,
    aTailHaltNodeTree, rootBNodeTree, bDecomposeNodeTree, bVerifyNodeTree, bResultHaltNodeTree,
    bTailHaltNodeTree, memNode, memStamp, memLabelS, memInputsS,
    gAReadOuterPub_eq, gADecomposeOuterPub_eq, gAHeadHaltPub_eq, gAReadInnerPub_eq,
    gAVerifyOuterPub_eq, gADecomposeInnerPub_eq, gAInnerHeadHaltPub_eq, gAVerifyInnerPub_eq,
    gATailHaltPub_eq, gBReadPub_eq, gBDecomposePub_eq, gBVerifyPub_eq, gBResultHaltPub_eq,
    gBTailHaltPub_eq]

/-- **Non-vacuity of the served coverage.**  The generated forest has TWO serviced roots — the
    second (`root B`) rooted at the subject `subjectS`, serving the real slot record `servedRecord`
    (`[subject result] @ axis 2`) on the genuine left descent `axisPath 2 = [false]` — so its
    `semanticCoverage` is genuinely inhabited, unlike the (vacuous) OP1/cons served coverage. -/
theorem genOp0MemForest_two_roots :
    (genOp0MemForest servedSeed).length = 3 ∧
      (gBReadPub servedSeed).mem = servedRecord ∧
      servedRecord.axis = (2 : K97cubic) :=
  ⟨rfl, rfl, rfl⟩

/-! ## F. The generator's `OP_0` DFS arm fires on the axis formula `[0 2]` -/

/-- **The `OP_0` DFS arm of `genComputeSkeleton` classifies the axis read `[0 2]`** on `subjectS`,
    resolves its served slot value `/[2 subjectS] = resultS`, and emits the leaf `.s0` skeleton with
    the two committed requests (formula-open `[0 2] @3`, slot `[subjectS resultS] @2`).  This is the
    generator-side of the OP0 slice; `genSkelOp0_eq` connects the emitted skeleton to the committed
    served row. -/
theorem genComputeSkeleton_op0 (n : ℕ) :
    genComputeSkeleton (K := K97cubic) (n + 1) subjectS formulaS
      = .ok (.node (skelNode (genSkelOp0 subjectS formulaS (.atom 0) tailS resultS 2)
          [⟨formulaS, tailS, 3, 0⟩, ⟨subjectS, resultS, 2, 0⟩]) [], resultS) := by
  simp only [genComputeSkeleton, formulaS, headS, tailS, slot_subjectS]

/-- **The `OP_4` DFS arm of `genComputeSkeleton` classifies the increment `[4 [0 2]]`** on
    `subjectS`: it recurses on the axis read `[0 2]` (the `OP_0` arm above), increments the
    call's result `resultS = /[2 subjectS]` to `parentResultS = +resultS`, and emits the `.s4`
    parent skeleton over the served `.s0` child. -/
theorem genComputeSkeleton_op4 (n : ℕ) :
    genComputeSkeleton (K := K97cubic) (n + 2) subjectS parentFormulaS
      = .ok (.node (skelNode
            (genSkelOp4 subjectS parentFormulaS (.atom 4) formulaS subjectS formulaS resultS
              parentResultS)
            [⟨parentFormulaS, formulaS, 3, 0⟩])
            [.node (skelNode (genSkelOp0 subjectS formulaS (.atom 0) tailS resultS 2)
                [⟨formulaS, tailS, 3, 0⟩, ⟨subjectS, resultS, 2, 0⟩]) []],
          parentResultS) := by
  show genComputeSkeleton ((n + 1) + 1) subjectS parentFormulaS = _
  simp only [genComputeSkeleton, parentFormulaS, parentHeadS, formulaS, headS, tailS,
    slot_subjectS, Nock.Noun.lus, resultS, parentResultS]

/-! ## G. The compute render rows collapse to the committed rows via `encC` -/

/-- The generated `OP_4` render row, at the repaired seed and the assigned root exponents, is the
    committed parent row `parentRowS`.  Every fingerprint column collapses `encC → enc = encS`
    (`Encode.encC_eq`); `ln_prev = α⁰ = 1`, `ln = α¹`, and the single record is `parentRecordS`. -/
theorem renderOp4Row_eq :
    renderOp4Row servedSeed fixtureAlpha (stampOfAcc .s4 0)
        (genSkelOp4 subjectS parentFormulaS (.atom 4) formulaS subjectS formulaS resultS
          parentResultS)
      = parentRowS := by
  simp only [renderOp4Row, genSkelOp4, stampOfAcc, formulaHead, formulaTail, parentFormulaS,
    P8Census.skeletonSubformula, ComputeTable.fanoutComp, Nock.Framework.recordCount,
    parentRowS, servedInputs, parentPubS, parentDecS, parentRecordS, encS, encC_eq,
    Fin.isValue, Fin.val_zero, pow_zero, pow_one, Nat.zero_add,
    dif_pos, Nat.zero_lt_one] <;> rfl

/-- The generated `OP_0` render row, at the repaired seed and the assigned served exponents
    (`stampOfAcc .s0 1`), is the committed served row `servedRow`.  The two records are the
    formula-open `servedFormulaRecord` (`α²`) and the slot read `servedRecord` (`@2`, `α³`), the
    piecewise exponents `2`,`3` supplied by the `.s0` branch of `stampOfAcc`. -/
theorem renderOp0Row_eq :
    renderOp0Row servedSeed fixtureAlpha (stampOfAcc .s0 1)
        (genSkelOp0 subjectS formulaS (.atom 0) tailS resultS 2)
      = servedRow := by
  simp only [renderOp0Row, genSkelOp0, stampOfAcc, formulaHead, formulaTail,
    P8Census.skeletonMemoryAxis, Nock.Framework.recordCount,
    servedRow, servedInputs, servedPub, servedDec, servedFormulaRecord, servedRecord,
    encS, encC_eq, formulaS, Fin.isValue, Fin.val_zero, Fin.val_one, pow_one,
    Nat.reduceLT, reduceDIte, Nat.cast_ofNat, Nat.reduceAdd, if_true, if_false, Nat.reduceEqDiff]

/-! ## H. The generated compute tree's `.node` projection is exactly `computeNodesM` -/

/-- **The generator's emitted `OP_4[OP_0]` compute tree, rendered, is the committed `computeNodesM`.**
    The DFS pass (`genComputeSkeleton_op4`) emits the `.s4` parent over the `.s0` child; the exponent
    pass stamps the root at `stampOfAcc .s4 0` and the child at `stampOfAcc .s0 1` (the piecewise
    `OP_0` exponents); the render pass fills each row to `parentRowS`/`servedRow`.  This is the
    compute-side analogue of `gen_op0MemForest_eq`. -/
theorem gen_op0ComputeNodes_eq :
    mapNTree GenComputeRow.node
        (renderRows servedSeed fixtureAlpha (assignExponents
          (.node (skelNode
            (genSkelOp4 subjectS parentFormulaS (.atom 4) formulaS subjectS formulaS resultS
              parentResultS)
            [⟨parentFormulaS, formulaS, 3, 0⟩])
            [.node (skelNode (genSkelOp0 subjectS formulaS (.atom 0) tailS resultS 2)
                [⟨formulaS, tailS, 3, 0⟩, ⟨subjectS, resultS, 2, 0⟩]) []])))
      = computeNodesM := by
  have hparent : (genSkelOp4 subjectS parentFormulaS (.atom 4) formulaS subjectS formulaS resultS
      parentResultS).state = ComputeTable.State.s4 := rfl
  have hserved : (genSkelOp0 subjectS formulaS (.atom 0) tailS resultS 2).state
      = ComputeTable.State.s0 := rfl
  simp only [assignExponents, assignTree, assignList, subtreeRecordCount, renderRows,
    renderNode, skelNode, hparent, hserved, Nock.Framework.recordCount, List.map_nil,
    List.map_cons, List.sum_nil, List.sum_cons, mapNTree, Nat.zero_add, Nat.add_zero]
  simp only [GenComputeRow.node, computeNodesM, parentNode, servedNode]
  rw [renderOp4Row_eq, renderOp0Row_eq]
  rfl

/-! ## I. The generator-routed honest commitment `Data multiRootExecution` -/

/-- The generator's own emitted `OP_4[OP_0]` trace: the DFS/exponent/render compute tree of
    `genComputeSkeleton_op4` paired with the fourteen-row two-serviced-root served memory forest
    `genOp0MemForest`.  Its `computeNodes` are literally the generator's rendered nodes (see
    `genOp0Trace_is_generated`). -/
def genOp0Trace : GenTrace K97cubic K97cubic where
  subject := subjectS
  formula := parentFormulaS
  result := parentResultS
  fuel := 2
  computeNodes := renderRows servedSeed fixtureAlpha (assignExponents
    (.node (skelNode
      (genSkelOp4 subjectS parentFormulaS (.atom 4) formulaS subjectS formulaS resultS
        parentResultS) [⟨parentFormulaS, formulaS, 3, 0⟩])
      [.node (skelNode (genSkelOp0 subjectS formulaS (.atom 0) tailS resultS 2)
          [⟨formulaS, tailS, 3, 0⟩, ⟨subjectS, resultS, 2, 0⟩]) []]))
  memoryNodes := genOp0MemForest servedSeed

/-- **The trace's compute nodes really are the generator's output.**  Running the DFS pass
    `genComputeSkeleton 2 subjectS parentFormulaS` and rendering its tree yields exactly
    `genOp0Trace.computeNodes` — nothing is hand-substituted for the generator. -/
theorem genOp0Trace_is_generated :
    (genComputeSkeleton (K := K97cubic) 2 subjectS parentFormulaS).map
        (fun p => renderRows servedSeed fixtureAlpha (assignExponents p.1))
      = .ok genOp0Trace.computeNodes := by
  rw [genComputeSkeleton_op4 0]
  rfl

/-- The generator committed exactly the two verified `MultiRootHonestCommitment` node trees: the
    compute tree `computeNodesM` and the fourteen-row served forest `memoryNodesM`. -/
structure Op0GenTraceOK (G : GenTrace K97cubic K97cubic) : Prop where
  computeNodes_eq : mapNTree GenComputeRow.node G.computeNodes = computeNodesM
  memoryForest_eq : G.memoryNodes.map (mapNTree GenMemoryRow.node) = memoryNodesM

theorem genOp0Trace_OK : Op0GenTraceOK genOp0Trace :=
  ⟨gen_op0ComputeNodes_eq, gen_op0MemForest_eq⟩

/-- **`op0DataOfGenerated`.**  The honest commitment `Data multiRootExecution` whose committed
    compute/memory node trees are *the generator's own emitted nodes*, with every census / bind /
    specialization obligation transported from the verified `MultiRootHonestCommitment.dataM` across
    the two node-tree equalities of `Op0GenTraceOK`.  This is the generated analogue of `dataM` and
    closes the OP0 slice's deferred compute-side transport (mirrors `Op1GenData.dataOfGenerated`). -/
noncomputable def op0DataOfGenerated (G : GenTrace K97cubic K97cubic) (h : Op0GenTraceOK G) :
    HonestCommitment.Data multiRootExecution where
  computeNodes := mapNTree GenComputeRow.node G.computeNodes
  memoryNodes := G.memoryNodes.map (mapNTree GenMemoryRow.node)
  compute_rows := by rw [h.computeNodes_eq]; exact dataM.compute_rows
  memory_rows := by rw [h.memoryForest_eq]; exact dataM.memory_rows
  computeOK := by rw [h.computeNodes_eq]; exact dataM.computeOK
  memoryOK := by rw [h.memoryForest_eq]; exact dataM.memoryOK
  root_line_exponent := by rw [h.computeNodes_eq]; exact dataM.root_line_exponent
  root_line_origin := by rw [h.computeNodes_eq]; exact dataM.root_line_origin
  nounSizeBound := 3
  Λ := 3
  slotSemantics := by rw [h.computeNodes_eq, h.memoryForest_eq]; exact dataM.slotSemantics
  recordEquations := by rw [h.computeNodes_eq, h.memoryForest_eq]; exact dataM.recordEquations
  census := by rw [h.computeNodes_eq, h.memoryForest_eq]; exact dataM.census
  sizeWindowBound := by rw [h.computeNodes_eq, h.memoryForest_eq]; exact dataM.sizeWindowBound
  q_eq_ringChar := dataM.q_eq_ringChar
  skeletonBounded := by rw [h.computeNodes_eq, h.memoryForest_eq]; exact dataM.skeletonBounded
  combinedBounded := by rw [h.computeNodes_eq, h.memoryForest_eq]; exact dataM.combinedBounded

/-- **The generator-routed honest commitment of the OP4[OP0] execution.** -/
noncomputable def op0Data : HonestCommitment.Data multiRootExecution :=
  op0DataOfGenerated genOp0Trace genOp0Trace_OK

/-- The generated commitment's committed skeleton is exactly the committed `skelM`. -/
theorem op0Data_skeleton : op0Data.skeleton = skelM := by
  show skeletonOfNodes (mapNTree GenComputeRow.node genOp0Trace.computeNodes)
      (genOp0Trace.memoryNodes.map (mapNTree GenMemoryRow.node)) = skelM
  rw [genOp0Trace_OK.computeNodes_eq, genOp0Trace_OK.memoryForest_eq]
  rfl

/-! ## J. The generator-routed committed residual, package, and released statement -/

/-- The committed residual over the generator-routed data (all-zero later-round message). -/
noncomputable def op0Residual : BuildablePackage.CommitmentResidual multiRootExecution :=
  HonestCommitment.commitmentResidualOfZero op0Data

theorem op0Residual_nonvacuous :
    Nonempty (BuildablePackage.CommitmentResidual multiRootExecution) :=
  ⟨op0Residual⟩


theorem op0Residual_generated :
    GeneratedField.ClaimGenerated K97cubic op0Residual.verifier.raw.claim op0Residual.Λ := by
  show GeneratedField.ClaimGenerated K97cubic op0Data.skeleton.publicClaim 3
  rw [op0Data_skeleton]
  exact residualM_generated

/-- **The released fourteen-conjunct Theorem-5.4 statement over the generator-routed package.** -/
theorem op0Statement
    (hax : FormRAxisBound
      (BuildablePackage.buildFullPackage multiRootExecution inputsM op0Residual
        inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
        op0Residual_generated f97_primeField).optimized.sampled
      (BuildablePackage.buildFullPackage multiRootExecution inputsM op0Residual
        inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
        op0Residual_generated f97_primeField).optimized.basis)
    (hbasis : FormRBasis
      (BuildablePackage.buildFullPackage multiRootExecution inputsM op0Residual
        inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
        op0Residual_generated f97_primeField).optimized.basis)
    (hwidth : FormRWidth F97) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
      (BuildablePackage.buildFullPackage multiRootExecution inputsM op0Residual
        inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
        op0Residual_generated f97_primeField) :=
  universalStatement_of_residualM hmoreM op0Residual op0Residual_generated hax hbasis hwidth

/-! ## K. Non-vacuity of the OP4 size window and the OP0 served coverage -/

/-- The `OP_4` parent's required size window is genuinely inhabited: exactly one bounded power
    window, the atom `resultS` (`requiredSizeWindows .s4 = 1`). -/
theorem op4_sizeWindow_inhabited :
    SizeWindowCounting.requiredSizeWindowNouns parentSkeletonRow = [resultS] := rfl

/-- The `OP_4` produced-result gate: `+resultS = parentResultS` (`incMod`). -/
theorem op4_incMod_gate :
    OpcodeSemantics.incMod (ringChar K97cubic) resultS = parentResultS :=
  incMod_resultS

/-- Joint non-vacuity: the served forest genuinely has two serviced roots serving the real slot
    record on axis `2`, and the OP4 size window is inhabited by `resultS`. -/
theorem op0_op4_nonvacuous :
    (genOp0MemForest servedSeed).length = 3 ∧
      (gBReadPub servedSeed).mem = servedRecord ∧
      servedRecord.axis = (2 : K97cubic) ∧
      SizeWindowCounting.requiredSizeWindowNouns parentSkeletonRow = [resultS] ∧
      OpcodeSemantics.incMod (ringChar K97cubic) resultS = parentResultS :=
  ⟨rfl, rfl, rfl, rfl, incMod_resultS⟩

end



#print axioms genSkelOp0_eq
#print axioms genSkelOp4_eq
#print axioms gen_op0MemForest_eq
#print axioms genOp0MemForest_two_roots
#print axioms genComputeSkeleton_op0
#print axioms genComputeSkeleton_op4
#print axioms renderOp4Row_eq
#print axioms renderOp0Row_eq
#print axioms gen_op0ComputeNodes_eq
#print axioms genOp0Trace_is_generated
#print axioms op0DataOfGenerated
#print axioms op0Data
#print axioms op0Data_skeleton
#print axioms op0Statement
#print axioms op0_op4_nonvacuous

end Nock.NockVMROM.Thm54.TraceGen
