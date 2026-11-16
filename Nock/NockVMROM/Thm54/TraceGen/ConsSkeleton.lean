/-
  Nock/NockVMROM/Thm54/TraceGen/ConsSkeleton.lean

  The field-free semantic skeleton of the fresh BRANCHING
  ROM program `*[0 [[1 5] [1 6]]] = [5 6]`, together with the six seed-free census-closure
  obligations an honest `HonestCommitment.Data` over that skeleton must discharge.

  This is the first VERIFIED BRANCHING reference skeleton in-tree.  Its compute tree is a `.cons`
  (autocons) root of fanout 2 (`Nock/NockVM.lean:159`) with two `OP_1` child rows:
  the left child evaluates to `5`, the right to `6`, and the root autocons combines them into the
  pair `[5 6]`.

  Because the compute tree branches, the seed-independent census here is genuinely multi-row for the
  first time: `EdgeComparisonCensus.edgePairs` is NON-EMPTY (two parent→child edges, three
  comparisons each), and `P8Census.skeletonComparisonCensus` flat-maps the `.cons` row's six
  comparisons together with each `OP_1` child's three.  Every comparison is DIAGONAL — the autocons
  program is a constant map whose decomposition/subformula projections reproduce their targets
  exactly — so the `PairFaithful` obligations reduce to the trivial self case, isolating the
  branching + BFS-order + census-closure work without the OP5 non-diagonal (`z ∉ badSeeds`)
  complication.

  Leaf window: the formula `[[1 5] [1 6]]` has `Noun.leaves = 4` (four atoms), the largest noun the
  census inspects, so `Λ = 4`.  (`OP_1`'s slice took `Λ = 3` for `[1 5]`.)
-/
import Nock.NockVMROM.Thm54.EdgeComparisonCensus
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.ServedLookupBridge
import Mathlib.Tactic.NormNum.Prime

namespace Nock.NockVMROM.Thm54.TraceGen.ConsSkeleton

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open SemanticStrategy ServedLookupBridge

/-- `ZMod 97` is a field. -/
instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- The Phase-2 slice field: the paper's `ExactConfig` uses `eDeg = 1`, so a prime field suffices. -/
abbrev F : Type := ZMod 97

/-! ## The seed-independent nouns of `*[0 [[1 5] [1 6]]] = [5 6]` -/

/-- Subject `0`. -/
def subjectNoun : Noun := .atom 0
/-- The `OP_1` formula head `1`, shared by both children. -/
def op1Head : Noun := .atom 1
/-- The left child's constant result `5`. -/
def leftResult : Noun := .atom 5
/-- The right child's constant result `6`. -/
def rightResult : Noun := .atom 6
/-- Left child formula `[1 5]`. -/
def leftFormula : Noun := .cell op1Head leftResult
/-- Right child formula `[1 6]`. -/
def rightFormula : Noun := .cell op1Head rightResult
/-- Root formula `[[1 5] [1 6]]` (the autocons of the two child formulae). -/
def formulaNoun : Noun := .cell leftFormula rightFormula
/-- Result `[5 6]` — the autocons of the two child results. -/
def resultNoun : Noun := .cell leftResult rightResult

/-- The `.cons` root's single live memory record: opening the formula at axis `3`. -/
def recCons : MemRecSkeleton where
  root := formulaNoun
  child := rightFormula
  axis := 3
/-- The left `OP_1` child's live memory record: opening `[1 5]` at axis `3`. -/
def recL : MemRecSkeleton where
  root := leftFormula
  child := leftResult
  axis := 3
/-- The right `OP_1` child's live memory record: opening `[1 6]` at axis `3`. -/
def recR : MemRecSkeleton where
  root := rightFormula
  child := rightResult
  axis := 3

/-! ## The three compute rows (`.cons` root + two `OP_1` children), in BFS order -/

/-- The `.cons` autocons compute-row skeleton.  Fanout 2: two subformula
branches (left → `[1 5]`, right → `[1 6]`); one live memory record opening the formula. -/
def consRow : ComputeRowSkeleton where
  state := .cons
  subject := subjectNoun
  formula := formulaNoun
  evaluation := resultNoun
  decomposition := fun slot _ =>
    match slot with
    | .f_h => leftFormula
    | .f_t => rightFormula
    | _ => .atom 0
  subformula := fun i _ slot =>
    if (i : ℕ) = 0 then
      match slot with
      | .subject => subjectNoun
      | .formula => leftFormula
      | .result => leftResult
    else
      match slot with
      | .subject => subjectNoun
      | .formula => rightFormula
      | .result => rightResult
  memoryRecord := fun i _ =>
    if (i : ℕ) = 0 then recCons else ⟨.atom 0, .atom 0, 0⟩

/-- The left `OP_1` child compute-row skeleton: `*[0 [1 5]] = 5`. -/
def op1LRow : ComputeRowSkeleton where
  state := .s1
  subject := subjectNoun
  formula := leftFormula
  evaluation := leftResult
  decomposition := fun slot _ =>
    match slot with
    | .f_h => op1Head
    | .f_t => leftResult
    | _ => .atom 0
  subformula := fun i hi _ => absurd hi (by
    simpa [ComputeTable.fanoutComp] using hi)
  memoryRecord := fun i _ =>
    if (i : ℕ) = 0 then recL else ⟨.atom 0, .atom 0, 0⟩

/-- The right `OP_1` child compute-row skeleton: `*[0 [1 6]] = 6`. -/
def op1RRow : ComputeRowSkeleton where
  state := .s1
  subject := subjectNoun
  formula := rightFormula
  evaluation := rightResult
  decomposition := fun slot _ =>
    match slot with
    | .f_h => op1Head
    | .f_t => rightResult
    | _ => .atom 0
  subformula := fun i hi _ => absurd hi (by
    simpa [ComputeTable.fanoutComp] using hi)
  memoryRecord := fun i _ =>
    if (i : ℕ) = 0 then recR else ⟨.atom 0, .atom 0, 0⟩

/-- The branching compute tree: `.cons` root over its two `OP_1` children (BFS order:
root, left, right). -/
def computeTree : NTree ComputeRowSkeleton :=
  .node consRow [.node op1LRow [], .node op1RRow []]

/-! ## The memory forest: the reconstruction servicing the three committed records

The `.cons` row commits `recCons` (formula @3), and each `OP_1` child commits `recL`/`recR`
(its formula @3).  The forest is a single tree rooted at the formula: read the formula (serving
`recCons`), decompose it into its head `[1 5]` and tail `[1 6]`; the head roots the left child's
own read/decompose/verify reconstruction (serving `recL`), while the tail is both read for the
right child (`recR`) and verified as `recCons`'s committed child, then decomposed for `recR`.

Only `skeletonBounded` inspects this forest, and only for `q = 97`-boundedness of every committed
noun; the exact servicing correctness is the memory-CORE obligation of a later module.  Every noun
here (`[[1 5] [1 6]]`, `[1 5]`, `[1 6]`, and atoms `1,5,6`) is atom- and leaf-bounded below `97`. -/

/-- `read_root` of the formula, serving `recCons`. -/
def readFRow : MemoryRowSkeleton where
  state := .read_root
  parent := formulaNoun
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if (i : ℕ) = 0 then formulaNoun else .atom 0
  memoryRecord := fun _ => recCons

/-- `decompose` of the formula into head `[1 5]` and tail `[1 6]`. -/
def decFRow : MemoryRowSkeleton where
  state := .decompose
  parent := formulaNoun
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if (i : ℕ) = 0 then leftFormula else rightFormula
  memoryRecord := fun h => nomatch h

/-- `read_root` of the left formula `[1 5]`, serving `recL`. -/
def readLRow : MemoryRowSkeleton where
  state := .read_root
  parent := leftFormula
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if (i : ℕ) = 0 then leftFormula else .atom 0
  memoryRecord := fun _ => recL

/-- `decompose` of the left formula into head `1` and tail `5`. -/
def decLRow : MemoryRowSkeleton where
  state := .decompose
  parent := leftFormula
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if (i : ℕ) = 0 then op1Head else leftResult
  memoryRecord := fun h => nomatch h

/-- Terminal `halt` seed (atom `0`) prepended so form-R remaining is zero at BFS row 0. -/
def dummyHaltRow : MemoryRowSkeleton where
  state := .halt
  parent := .atom 0
  haltAtom := fun _ => 0
  haltParent := by intro h; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

/-- Terminal `halt` for the left head `1`. -/
def haltL1Row : MemoryRowSkeleton where
  state := .halt
  parent := op1Head
  haltAtom := fun _ => 1
  haltParent := by intro h; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

/-- `verify_child` pairing read/verify for the left served result `5` (`recL`). -/
def verifyLRow : MemoryRowSkeleton where
  state := .verify_child
  parent := leftResult
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => leftResult
  memoryRecord := fun _ => recL

/-- Terminal `halt` for the left result `5`. -/
def haltL5Row : MemoryRowSkeleton where
  state := .halt
  parent := leftResult
  haltAtom := fun _ => 5
  haltParent := by intro h; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

/-- `read_root` of the right formula `[1 6]`, serving `recR`. -/
def readRRow : MemoryRowSkeleton where
  state := .read_root
  parent := rightFormula
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if (i : ℕ) = 0 then rightFormula else .atom 0
  memoryRecord := fun _ => recR

/-- `verify_child` of the right formula `[1 6]` as `recCons`'s committed child. -/
def verifyFRow : MemoryRowSkeleton where
  state := .verify_child
  parent := rightFormula
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => rightFormula
  memoryRecord := fun _ => recCons

/-- `decompose` of the right formula into head `1` and tail `6`. -/
def decRRow : MemoryRowSkeleton where
  state := .decompose
  parent := rightFormula
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if (i : ℕ) = 0 then op1Head else rightResult
  memoryRecord := fun h => nomatch h

/-- Terminal `halt` for the right head `1`. -/
def haltR1Row : MemoryRowSkeleton where
  state := .halt
  parent := op1Head
  haltAtom := fun _ => 1
  haltParent := by intro h; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

/-- `verify_child` pairing read/verify for the right served result `6` (`recR`). -/
def verifyRRow : MemoryRowSkeleton where
  state := .verify_child
  parent := rightResult
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => rightResult
  memoryRecord := fun _ => recR

/-- Terminal `halt` for the right result `6`. -/
def haltR6Row : MemoryRowSkeleton where
  state := .halt
  parent := rightResult
  haltAtom := fun _ => 6
  haltParent := by intro h; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

def dummyHaltTree : NTree MemoryRowSkeleton := .node dummyHaltRow []
def haltL1Tree : NTree MemoryRowSkeleton := .node haltL1Row []
def haltL5Tree : NTree MemoryRowSkeleton := .node haltL5Row []
def verifyLTree : NTree MemoryRowSkeleton := .node verifyLRow [haltL5Tree]
def decLTree : NTree MemoryRowSkeleton := .node decLRow [haltL1Tree, verifyLTree]
def readLTree : NTree MemoryRowSkeleton := .node readLRow [decLTree]
def haltR1Tree : NTree MemoryRowSkeleton := .node haltR1Row []
def haltR6Tree : NTree MemoryRowSkeleton := .node haltR6Row []
def verifyRTree : NTree MemoryRowSkeleton := .node verifyRRow [haltR6Tree]
def decRTree : NTree MemoryRowSkeleton := .node decRRow [haltR1Tree, verifyRTree]
def verifyFTree : NTree MemoryRowSkeleton := .node verifyFRow [decRTree]
def readRTree : NTree MemoryRowSkeleton := .node readRRow [verifyFTree]
def decFTree : NTree MemoryRowSkeleton := .node decFRow [readLTree, readRTree]
def readFTree : NTree MemoryRowSkeleton := .node readFRow [decFTree]

/-- The complete field-free semantic skeleton of `*[0 [[1 5] [1 6]]] = [5 6]`. -/
def semanticSkeleton : SemanticSkeleton where
  computeTree := computeTree
  memoryForest := [dummyHaltTree, readFTree]

/-! ## Row-list reductions used by every obligation below -/

theorem computeRows_eq :
    computeSkeletonRows semanticSkeleton = [consRow, op1LRow, op1RRow] := by
  norm_num [computeSkeletonRows, semanticSkeleton, computeTree, bfsForest,
    NTree.size, totalSize]

theorem memoryRows_eq :
    memorySkeletonRows semanticSkeleton =
      [dummyHaltRow, readFRow, decFRow, readLRow, readRRow, decLRow, verifyFRow,
        haltL1Row, verifyLRow, decRRow, haltL5Row, haltR1Row, verifyRRow, haltR6Row] := by
  norm_num [memorySkeletonRows, semanticSkeleton, dummyHaltTree, readFTree, decFTree, readLTree,
    decLTree, haltL1Tree, verifyLTree, haltL5Tree, readRTree, verifyFTree, decRTree,
    haltR1Tree, verifyRTree, haltR6Tree, bfsForest, NTree.size, totalSize]

/-! ## The six seed-free census-closure obligations (the concrete branching Phase-2 slice)

Every obligation below is exactly a field of `HonestCommitment.Data` on this skeleton, stated over
the concrete slice's `K = ZMod 97` and `Λ = 4`, so a future `HonestCommitment.Data` can consume
them once the heavier `BuildableNockExecution` is supplied. -/

/-- `slotSemantics`. -/
theorem slotSemantics :
    ∀ s ∈ computeSkeletonRows semanticSkeleton, SkeletonSlotSemantics s := by
  intro s hs
  rw [computeRows_eq] at hs
  fin_cases hs <;>
    exact
      { s0_slot := fun h => absurd h (by simp [consRow, op1LRow, op1RRow])
        s9_slot := fun h => absurd h (by simp [consRow, op1LRow, op1RRow]) }

/-- `recordEquations` (free by the same `OP_1`/`.cons` state discrimination). -/
theorem recordEquations :
    ∀ s ∈ computeSkeletonRows semanticSkeleton, SkeletonRecordEquations s := by
  intro s hs
  rw [computeRows_eq] at hs
  fin_cases hs <;>
    exact
      { s0_record := fun h => absurd h (by simp [consRow, op1LRow, op1RRow])
        s9_record := fun h => absurd h (by simp [consRow, op1LRow, op1RRow]) }

/-- `sizeWindowBound` (free: neither `.cons` nor `OP_1` triggers any OP3/OP4/OP6 size window;
`Λ = 4`). -/
theorem sizeWindowBound :
    SizeWindowCounting.SizeWindowNounsBoundedBy semanticSkeleton 4 := by
  intro n hn
  rw [SizeWindowCounting.skeletonSizeWindowNouns, computeRows_eq] at hn
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hn
  simp [SizeWindowCounting.requiredSizeWindowNouns, consRow, op1LRow, op1RRow] at hn

/-! ### `skeletonBounded`: every committed noun's atoms/leaves lie below `q = 97` -/

theorem consRow_bounded : consRow.BoundedBy 97 := by
  refine ⟨by simp [consRow, subjectNoun, FieldEmbedding.BoundedBy],
    by simp [consRow, formulaNoun, leftFormula, rightFormula, op1Head, leftResult, rightResult,
      FieldEmbedding.BoundedBy],
    by simp [consRow, resultNoun, leftResult, rightResult, FieldEmbedding.BoundedBy], ?_, ?_, ?_⟩
  · intro slot h
    cases slot <;>
      simp [consRow, leftFormula, rightFormula, op1Head, leftResult, rightResult,
        FieldEmbedding.BoundedBy]
  · intro i h slot
    rcases slot with _ | _ | _ <;>
      (by_cases hi : i = 0 <;>
        simp [consRow, subjectNoun, leftFormula, rightFormula, op1Head, leftResult, rightResult,
          FieldEmbedding.BoundedBy, hi])
  · intro i h
    by_cases hi : i = 0 <;>
      simp [consRow, recCons, formulaNoun, leftFormula, rightFormula, op1Head, leftResult,
        rightResult, SemanticStrategy.MemRecSkeleton.BoundedBy, FieldEmbedding.BoundedBy, hi]

theorem op1LRow_bounded : op1LRow.BoundedBy 97 := by
  refine ⟨by simp [op1LRow, subjectNoun, FieldEmbedding.BoundedBy],
    by simp [op1LRow, leftFormula, op1Head, leftResult, FieldEmbedding.BoundedBy],
    by simp [op1LRow, leftResult, FieldEmbedding.BoundedBy], ?_, ?_, ?_⟩
  · intro slot h
    cases slot <;>
      simp [op1LRow, op1Head, leftResult, FieldEmbedding.BoundedBy]
  · intro i h slot
    simp [op1LRow, ComputeTable.fanoutComp] at h
  · intro i h
    by_cases hi : i = 0 <;>
      simp [op1LRow, recL, leftFormula, op1Head, leftResult,
        SemanticStrategy.MemRecSkeleton.BoundedBy, FieldEmbedding.BoundedBy, hi]

theorem op1RRow_bounded : op1RRow.BoundedBy 97 := by
  refine ⟨by simp [op1RRow, subjectNoun, FieldEmbedding.BoundedBy],
    by simp [op1RRow, rightFormula, op1Head, rightResult, FieldEmbedding.BoundedBy],
    by simp [op1RRow, rightResult, FieldEmbedding.BoundedBy], ?_, ?_, ?_⟩
  · intro slot h
    cases slot <;>
      simp [op1RRow, op1Head, rightResult, FieldEmbedding.BoundedBy]
  · intro i h slot
    simp [op1RRow, ComputeTable.fanoutComp] at h
  · intro i h
    by_cases hi : i = 0 <;>
      simp [op1RRow, recR, rightFormula, op1Head, rightResult,
        SemanticStrategy.MemRecSkeleton.BoundedBy, FieldEmbedding.BoundedBy, hi]

theorem readFRow_bounded : readFRow.BoundedBy 97 := by
  refine ⟨by simp [readFRow, formulaNoun, leftFormula, rightFormula, op1Head, leftResult,
    rightResult, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    by_cases hi : i = 0 <;>
      simp [readFRow, formulaNoun, leftFormula, rightFormula, op1Head, leftResult, rightResult,
        FieldEmbedding.BoundedBy, hi]
  · intro _
    simp [readFRow, recCons, formulaNoun, leftFormula, rightFormula, op1Head, leftResult,
      rightResult, SemanticStrategy.MemRecSkeleton.BoundedBy, FieldEmbedding.BoundedBy]

theorem decFRow_bounded : decFRow.BoundedBy 97 := by
  refine ⟨by simp [decFRow, formulaNoun, leftFormula, rightFormula, op1Head, leftResult,
    rightResult, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    by_cases hi : i = 0 <;>
      simp [decFRow, leftFormula, rightFormula, op1Head, leftResult, rightResult,
        FieldEmbedding.BoundedBy, hi]
  · intro h
    simp [decFRow, memoryMemRecKind] at h

theorem readLRow_bounded : readLRow.BoundedBy 97 := by
  refine ⟨by simp [readLRow, leftFormula, op1Head, leftResult, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    by_cases hi : i = 0 <;>
      simp [readLRow, leftFormula, op1Head, leftResult, FieldEmbedding.BoundedBy, hi]
  · intro _
    simp [readLRow, recL, leftFormula, op1Head, leftResult,
      SemanticStrategy.MemRecSkeleton.BoundedBy, FieldEmbedding.BoundedBy]

theorem decLRow_bounded : decLRow.BoundedBy 97 := by
  refine ⟨by simp [decLRow, leftFormula, op1Head, leftResult, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    by_cases hi : i = 0 <;>
      simp [decLRow, op1Head, leftResult, FieldEmbedding.BoundedBy, hi]
  · intro h
    simp [decLRow, memoryMemRecKind] at h

theorem dummyHaltRow_bounded : dummyHaltRow.BoundedBy 97 := by
  refine ⟨by simp [dummyHaltRow, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    simp [dummyHaltRow, MemoryTable.fanoutMem] at h
  · intro h
    simp [dummyHaltRow, memoryMemRecKind] at h

theorem haltL1Row_bounded : haltL1Row.BoundedBy 97 := by
  refine ⟨by simp [haltL1Row, op1Head, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    simp [haltL1Row, MemoryTable.fanoutMem] at h
  · intro h
    simp [haltL1Row, memoryMemRecKind] at h

theorem verifyLRow_bounded : verifyLRow.BoundedBy 97 := by
  refine ⟨by simp [verifyLRow, leftResult, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    simp [verifyLRow, leftResult, FieldEmbedding.BoundedBy]
  · intro _
    simp [verifyLRow, recL, leftFormula, op1Head, leftResult,
      SemanticStrategy.MemRecSkeleton.BoundedBy, FieldEmbedding.BoundedBy]

theorem haltL5Row_bounded : haltL5Row.BoundedBy 97 := by
  refine ⟨by simp [haltL5Row, leftResult, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    simp [haltL5Row, MemoryTable.fanoutMem] at h
  · intro h
    simp [haltL5Row, memoryMemRecKind] at h

theorem readRRow_bounded : readRRow.BoundedBy 97 := by
  refine ⟨by simp [readRRow, rightFormula, op1Head, rightResult, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    by_cases hi : i = 0 <;>
      simp [readRRow, rightFormula, op1Head, rightResult, FieldEmbedding.BoundedBy, hi]
  · intro _
    simp [readRRow, recR, rightFormula, op1Head, rightResult,
      SemanticStrategy.MemRecSkeleton.BoundedBy, FieldEmbedding.BoundedBy]

theorem verifyFRow_bounded : verifyFRow.BoundedBy 97 := by
  refine ⟨by simp [verifyFRow, rightFormula, op1Head, rightResult, FieldEmbedding.BoundedBy],
    ?_, ?_⟩
  · intro i h
    simp [verifyFRow, rightFormula, op1Head, rightResult, FieldEmbedding.BoundedBy]
  · intro _
    simp [verifyFRow, recCons, formulaNoun, leftFormula, rightFormula, op1Head, leftResult,
      rightResult, SemanticStrategy.MemRecSkeleton.BoundedBy, FieldEmbedding.BoundedBy]

theorem decRRow_bounded : decRRow.BoundedBy 97 := by
  refine ⟨by simp [decRRow, rightFormula, op1Head, rightResult, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    by_cases hi : i = 0 <;>
      simp [decRRow, op1Head, rightResult, FieldEmbedding.BoundedBy, hi]
  · intro h
    simp [decRRow, memoryMemRecKind] at h

theorem haltR1Row_bounded : haltR1Row.BoundedBy 97 := by
  refine ⟨by simp [haltR1Row, op1Head, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    simp [haltR1Row, MemoryTable.fanoutMem] at h
  · intro h
    simp [haltR1Row, memoryMemRecKind] at h

theorem verifyRRow_bounded : verifyRRow.BoundedBy 97 := by
  refine ⟨by simp [verifyRRow, rightResult, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    simp [verifyRRow, rightResult, FieldEmbedding.BoundedBy]
  · intro _
    simp [verifyRRow, recR, rightFormula, op1Head, rightResult,
      SemanticStrategy.MemRecSkeleton.BoundedBy, FieldEmbedding.BoundedBy]

theorem haltR6Row_bounded : haltR6Row.BoundedBy 97 := by
  refine ⟨by simp [haltR6Row, rightResult, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    simp [haltR6Row, MemoryTable.fanoutMem] at h
  · intro h
    simp [haltR6Row, memoryMemRecKind] at h

/-- `skeletonBounded`: the whole branching skeleton's committed nouns are `q = 97`-bounded. -/
theorem skeletonBounded : semanticSkeleton.BoundedBy 97 := by
  refine
    { computeRows := ?_
      memoryRows := ?_
      memoryTrees := ?_ }
  · rw [computeRows_eq]
    exact ⟨consRow_bounded, op1LRow_bounded, op1RRow_bounded⟩
  · rw [memoryRows_eq]
    exact ⟨dummyHaltRow_bounded, readFRow_bounded, decFRow_bounded, readLRow_bounded,
      readRRow_bounded, decLRow_bounded, verifyFRow_bounded, haltL1Row_bounded, verifyLRow_bounded,
      decRRow_bounded, haltL5Row_bounded, haltR1Row_bounded, verifyRRow_bounded,
      haltR6Row_bounded⟩
  · intro tree htree node hnode
    change tree ∈ [dummyHaltTree, readFTree] at htree
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htree
    rcases htree with rfl | rfl
    · have hm : node ∈ bfsForest [dummyHaltTree] :=
        (mem_bfsForest [dummyHaltTree] node).2 ⟨dummyHaltTree, by simp, hnode⟩
      simp [dummyHaltTree, bfsForest] at hm
      subst hm
      exact dummyHaltRow_bounded
    · have hm : node ∈ bfsForest [readFTree] :=
        (mem_bfsForest [readFTree] node).2 ⟨readFTree, by simp, hnode⟩
      simp [readFTree, decFTree, readLTree, decLTree, haltL1Tree, verifyLTree, haltL5Tree,
        readRTree, verifyFTree, decRTree, haltR1Tree, verifyRTree, haltR6Tree, bfsForest] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact readFRow_bounded
      · exact decFRow_bounded
      · exact readLRow_bounded
      · exact readRRow_bounded
      · exact decLRow_bounded
      · exact verifyFRow_bounded
      · exact haltL1Row_bounded
      · exact verifyLRow_bounded
      · exact decRRow_bounded
      · exact haltL5Row_bounded
      · exact haltR1Row_bounded
      · exact verifyRRow_bounded
      · exact haltR6Row_bounded

/-! `combinedSkeletonPairs = skeletonPairs ++ edgePairs computeTree`.  For this autocons slice:
`skeletonPairs` is the three public-claim self-pairs followed by the `.cons` row's six comparisons
and each `OP_1` child's three (15 total), and `edgePairs` is the two parent→child edges' three
comparisons each (6 total).  Every pair is diagonal by construction of the autocons projections. -/

/-- `combinedBounded`: every comparison-census noun pair is `q = 97`-bounded on both sides.

This is the OP1 `combinedBounded` reduction generalized to the multi-row skeleton
(NOT `decide`: `P8Census` is `noncomputable`). -/
theorem combinedBounded :
    ProductionP8Containment.CombinedBoundedBy F 97 semanticSkeleton := by
  intro pair hp
  simp [EdgeComparisonCensus.combinedSkeletonPairs, BoundSemanticTrace.skeletonPairs,
    EdgeComparisonCensus.edgePairs, EdgeComparisonCensus.rowEdgePairs,
    EdgeComparisonCensus.edgeTriple, P8Census.skeletonComparisonCensus,
    P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
    P8Census.skeletonSubformula, SemanticStrategy.SemanticSkeleton.publicClaim,
    SemanticTrace.ComparisonUse.pair, semanticSkeleton, computeTree, computeSkeletonRows,
    consRow, op1LRow, op1RRow, subjectNoun, formulaNoun, leftFormula, rightFormula, op1Head,
    leftResult, rightResult, resultNoun, recCons, recL, recR, decActive, ComputeTable.fanoutComp,
    NTree.childOpt, NTree.label, bfsForest, NTree.size, totalSize, List.flatMap_cons,
    List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil, List.cons_append,
    List.nil_append, List.ofFn_succ, List.ofFn_zero, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.getElem?_nil, Option.map_some, Option.map_none] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [FieldEmbedding.BoundedBy, subjectNoun, formulaNoun, leftFormula, rightFormula,
      op1Head, leftResult, rightResult, resultNoun]

/-- `census`: the branching comparison census of the skeleton lies inside the paper's leaf window
`Λ = 4`. -/
def census : EdgeComparisonCensus.CombinedSkeletonCensus F semanticSkeleton 4 where
  p8 :=
    { leaves_bounded := by
        intro pair hp
        simp [BoundSemanticTrace.skeletonPairs, P8Census.skeletonComparisonCensus,
          P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
          P8Census.skeletonSubformula, SemanticStrategy.SemanticSkeleton.publicClaim,
          SemanticTrace.ComparisonUse.pair, semanticSkeleton, computeTree, computeSkeletonRows,
          consRow, op1LRow, op1RRow, subjectNoun, formulaNoun, leftFormula, rightFormula, op1Head,
          leftResult, rightResult, resultNoun, decActive, ComputeTable.fanoutComp, NTree.label,
          bfsForest, NTree.size, totalSize, List.flatMap_cons, List.flatMap_nil, List.map_cons,
          List.map_nil, List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl <;>
          simp [subjectNoun, formulaNoun, leftFormula, rightFormula, op1Head, leftResult,
            rightResult, resultNoun, Noun.leaves] }
  edges :=
    { leaves_bounded := by
        intro pair hp
        simp [EdgeComparisonCensus.edgePairs, EdgeComparisonCensus.rowEdgePairs,
          EdgeComparisonCensus.edgeTriple, P8Census.skeletonSubformula, semanticSkeleton,
          computeTree, consRow, op1LRow, op1RRow, subjectNoun, leftFormula, rightFormula, op1Head,
          leftResult, rightResult, ComputeTable.fanoutComp, NTree.childOpt, NTree.label, bfsForest,
          NTree.size, totalSize, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.ofFn_succ, List.ofFn_zero, List.cons_append, List.nil_append, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false, List.getElem?_cons_zero,
          List.getElem?_cons_succ, List.getElem?_nil, Option.map_some, Option.map_none] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [subjectNoun, leftFormula, rightFormula, op1Head, leftResult, rightResult,
            Noun.leaves] }

end Nock.NockVMROM.Thm54.TraceGen.ConsSkeleton

#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsSkeleton.slotSemantics
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsSkeleton.recordEquations
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsSkeleton.sizeWindowBound
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsSkeleton.skeletonBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsSkeleton.combinedBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsSkeleton.census
