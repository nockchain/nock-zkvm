/-
  Nock/NockVMROM/Thm54/TraceGen/Op1Skeleton.lean

  The field-free semantic skeleton of the fresh ROM
  program `*[0 [1 5]] = 5`, together with the six seed-free census-closure obligations an honest
  `HonestCommitment.Data` over that skeleton must discharge.

  The skeleton is a `SemanticStrategy.SemanticSkeleton`: nouns, Nat axes, and tree topology, all
  fixed before the sampled seed.  It is one `OP_1` compute row over the five-row memory reconstruction of its single live request,
  `read_root -> decompose -> (halt, verify_child -> halt)`, in BFS order
  `read, dec, halt_1, verify, halt_r`.

  Because `OP_1` is a constant, the OP0/OP9
  slot/record obligations and the OP3/OP4/OP6 size-window census are genuinely empty by state
  discrimination, so `slotSemantics`/`recordEquations`/`sizeWindowBound` hold
  by vacuity — the load-bearing gate being exactly that the row is `OP_1`, carried explicitly below.
-/
import Nock.NockVMROM.Thm54.EdgeComparisonCensus
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.ServedLookupBridge
import Mathlib.Tactic.NormNum.Prime

namespace Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open SemanticStrategy ServedLookupBridge

/-- `ZMod 97` is a field. -/
instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- The Phase-1 slice field: the paper's `ExactConfig` uses `eDeg = 1`, so a prime field suffices. -/
abbrev F : Type := ZMod 97

/-! ## The seed-independent nouns of `*[0 [1 5]] = 5` -/

/-- Subject `0`. -/
def subjectNoun : Noun := .atom 0
/-- The `OP_1` formula head `1`. -/
def headNoun : Noun := .atom 1
/-- Result `5` — the constant returned by `OP_1`. -/
def resultNoun : Noun := .atom 5
/-- Formula `[1 5]`. -/
def formulaNoun : Noun := .cell headNoun resultNoun

/-- The single live memory record of the `OP_1` row: opening the formula at axis `3`. -/
def requestSkeleton : MemRecSkeleton where
  root := formulaNoun
  child := resultNoun
  axis := 3

/-! ## The one compute row and the five memory rows -/

/-- The `OP_1` compute-row skeleton. -/
def computeSkeletonRow : ComputeRowSkeleton where
  state := .s1
  subject := subjectNoun
  formula := formulaNoun
  evaluation := resultNoun
  decomposition := fun slot _ =>
    match slot with
    | .f_h => headNoun
    | .f_t => resultNoun
    | _ => .atom 0
  subformula := fun i hi _ => absurd hi (by
    simpa [ComputeTable.fanoutComp] using hi)
  memoryRecord := fun i _ =>
    if (i : ℕ) = 0 then requestSkeleton else ⟨.atom 0, .atom 0, 0⟩

/-- The `read_root` memory row serving the single request. -/
def readSkeletonRow : MemoryRowSkeleton where
  state := .read_root
  parent := formulaNoun
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ =>
    if (i : ℕ) = 0 then formulaNoun else .atom 0
  memoryRecord := fun _ => requestSkeleton

/-- The `decompose` memory row splitting `[1 5]` into head `1` and tail `5`. -/
def decomposeSkeletonRow : MemoryRowSkeleton where
  state := .decompose
  parent := formulaNoun
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if (i : ℕ) = 0 then headNoun else resultNoun
  memoryRecord := fun h => nomatch h

def headSkeletonRow : MemoryRowSkeleton where
  state := .halt
  parent := headNoun
  haltAtom := fun _ => 1
  haltParent := by intro h; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

/-- The `verify_child` memory row that pairs read/verify for the served result. -/
def verifySkeletonRow : MemoryRowSkeleton where
  state := .verify_child
  parent := resultNoun
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => resultNoun
  memoryRecord := fun _ => requestSkeleton

def tailSkeletonRow : MemoryRowSkeleton where
  state := .halt
  parent := resultNoun
  haltAtom := fun _ => 5
  haltParent := by intro h; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

/-- Terminal `halt` seed (atom `0`) prepended so form-R remaining is zero at BFS row 0. -/
def dummyHaltSkeletonRow : MemoryRowSkeleton where
  state := .halt
  parent := .atom 0
  haltAtom := fun _ => 0
  haltParent := by intro h; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

def dummyHaltSkeletonTree : NTree MemoryRowSkeleton :=
  .node dummyHaltSkeletonRow []

def tailSkeletonTree : NTree MemoryRowSkeleton :=
  .node tailSkeletonRow []

def verifySkeletonTree : NTree MemoryRowSkeleton :=
  .node verifySkeletonRow [tailSkeletonTree]

def headSkeletonTree : NTree MemoryRowSkeleton :=
  .node headSkeletonRow []

def decomposeSkeletonTree : NTree MemoryRowSkeleton :=
  .node decomposeSkeletonRow [headSkeletonTree, verifySkeletonTree]

def readSkeletonTree : NTree MemoryRowSkeleton :=
  .node readSkeletonRow [decomposeSkeletonTree]

/-- The complete field-free semantic skeleton of `*[0 [1 5]] = 5`. -/
def semanticSkeleton : SemanticSkeleton where
  computeTree := .node computeSkeletonRow []
  memoryForest := [dummyHaltSkeletonTree, readSkeletonTree]

/-! ## The six seed-free census-closure obligations (the concrete Phase-2 slice)

Every obligation below is exactly a field of `HonestCommitment.Data` on this skeleton.  They are
stated once here, over the concrete slice's `K = ZMod 97` and `Λ = 3`, so that a future
`HonestCommitment.Data (execOf …)` can consume them by `rfl`-transport once the heavier
`BuildableNockExecution` is supplied. -/

/-- `slotSemantics`. -/
theorem slotSemantics :
    ∀ s ∈ computeSkeletonRows semanticSkeleton, SkeletonSlotSemantics s := by
  intro s hs
  have hrows : computeSkeletonRows semanticSkeleton = [computeSkeletonRow] := by
    norm_num [computeSkeletonRows, semanticSkeleton, bfsForest, NTree.size, totalSize]
  rw [hrows] at hs
  simp only [List.mem_singleton] at hs
  subst s
  exact
    { s0_slot := fun h => absurd h (by simp [computeSkeletonRow])
      s9_slot := fun h => absurd h (by simp [computeSkeletonRow]) }

/-- `recordEquations` (free by the same `OP_1` state discrimination). -/
theorem recordEquations :
    ∀ s ∈ computeSkeletonRows semanticSkeleton, SkeletonRecordEquations s := by
  intro s hs
  have hrows : computeSkeletonRows semanticSkeleton = [computeSkeletonRow] := by
    norm_num [computeSkeletonRows, semanticSkeleton, bfsForest, NTree.size, totalSize]
  rw [hrows] at hs
  simp only [List.mem_singleton] at hs
  subst s
  exact
    { s0_record := fun h => absurd h (by simp [computeSkeletonRow])
      s9_record := fun h => absurd h (by simp [computeSkeletonRow]) }

/-- `sizeWindowBound` (free: `OP_1` triggers no OP3/OP4/OP6 size window; `Λ = 3`). -/
theorem sizeWindowBound :
    SizeWindowCounting.SizeWindowNounsBoundedBy semanticSkeleton 3 := by
  intro n hn
  simp [SizeWindowCounting.skeletonSizeWindowNouns,
    SizeWindowCounting.requiredSizeWindowNouns, semanticSkeleton,
    computeSkeletonRows, computeSkeletonRow, bfsForest, NTree.size, totalSize] at hn

/-! ### `skeletonBounded`: every committed noun's atoms/leaves lie below `q = 97` -/

theorem computeSkeletonRow_bounded : computeSkeletonRow.BoundedBy 97 := by
  refine ⟨by simp [computeSkeletonRow, subjectNoun, FieldEmbedding.BoundedBy],
    by simp [computeSkeletonRow, formulaNoun, headNoun, resultNoun,
      FieldEmbedding.BoundedBy],
    by simp [computeSkeletonRow, resultNoun, FieldEmbedding.BoundedBy], ?_, ?_, ?_⟩
  · intro slot h
    cases slot <;>
      simp [computeSkeletonRow, headNoun, resultNoun, FieldEmbedding.BoundedBy]
  · intro i h
    simp [computeSkeletonRow, ComputeTable.fanoutComp] at h
  · intro i h
    fin_cases i <;>
      simp [computeSkeletonRow, requestSkeleton, formulaNoun, headNoun, resultNoun,
        SemanticStrategy.MemRecSkeleton.BoundedBy, FieldEmbedding.BoundedBy] at h ⊢

theorem readSkeletonRow_bounded : readSkeletonRow.BoundedBy 97 := by
  refine ⟨by simp [readSkeletonRow, formulaNoun, headNoun, resultNoun,
    FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    fin_cases i <;>
      simp [readSkeletonRow, MemoryTable.fanoutMem, formulaNoun, headNoun, resultNoun,
        FieldEmbedding.BoundedBy] at h ⊢
  · intro h
    simp [readSkeletonRow, requestSkeleton, formulaNoun, headNoun, resultNoun,
      SemanticStrategy.MemRecSkeleton.BoundedBy, FieldEmbedding.BoundedBy]

theorem decomposeSkeletonRow_bounded : decomposeSkeletonRow.BoundedBy 97 := by
  refine ⟨by simp [decomposeSkeletonRow, formulaNoun, headNoun, resultNoun,
    FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    fin_cases i <;>
      simp [decomposeSkeletonRow, MemoryTable.fanoutMem, headNoun, resultNoun,
        FieldEmbedding.BoundedBy] at h ⊢
  · intro h
    simp [decomposeSkeletonRow, memoryMemRecKind] at h

theorem headSkeletonRow_bounded : headSkeletonRow.BoundedBy 97 := by
  refine ⟨by simp [headSkeletonRow, headNoun, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    simp [headSkeletonRow, MemoryTable.fanoutMem] at h
  · intro h
    simp [headSkeletonRow, memoryMemRecKind] at h

theorem verifySkeletonRow_bounded : verifySkeletonRow.BoundedBy 97 := by
  refine ⟨by simp [verifySkeletonRow, resultNoun, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    fin_cases i <;>
      simp [verifySkeletonRow, resultNoun, FieldEmbedding.BoundedBy]
  · intro h
    simp [verifySkeletonRow, requestSkeleton, formulaNoun, headNoun, resultNoun,
      SemanticStrategy.MemRecSkeleton.BoundedBy, FieldEmbedding.BoundedBy]

theorem tailSkeletonRow_bounded : tailSkeletonRow.BoundedBy 97 := by
  refine ⟨by simp [tailSkeletonRow, resultNoun, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    simp [tailSkeletonRow, MemoryTable.fanoutMem] at h
  · intro h
    simp [tailSkeletonRow, memoryMemRecKind] at h

theorem dummyHaltSkeletonRow_bounded : dummyHaltSkeletonRow.BoundedBy 97 := by
  refine ⟨by simp [dummyHaltSkeletonRow, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    simp [dummyHaltSkeletonRow, MemoryTable.fanoutMem] at h
  · intro h
    simp [dummyHaltSkeletonRow, memoryMemRecKind] at h

/-- `skeletonBounded`: the whole skeleton's committed nouns are `q = 97`-bounded. -/
theorem skeletonBounded : semanticSkeleton.BoundedBy 97 := by
  refine
    { computeRows := ?_
      memoryRows := ?_
      memoryTrees := ?_ }
  · have hrows : computeSkeletonRows semanticSkeleton = [computeSkeletonRow] := by
      norm_num [computeSkeletonRows, semanticSkeleton, bfsForest, NTree.size, totalSize]
    rw [hrows]
    simpa using computeSkeletonRow_bounded
  · have hrows :
        memorySkeletonRows semanticSkeleton =
          [dummyHaltSkeletonRow, readSkeletonRow, decomposeSkeletonRow, headSkeletonRow,
            verifySkeletonRow, tailSkeletonRow] := by
      norm_num [memorySkeletonRows, semanticSkeleton, dummyHaltSkeletonTree, readSkeletonTree,
        decomposeSkeletonTree, headSkeletonTree, verifySkeletonTree, tailSkeletonTree,
        bfsForest, NTree.size, totalSize]
    rw [hrows]
    exact ⟨dummyHaltSkeletonRow_bounded, readSkeletonRow_bounded, decomposeSkeletonRow_bounded,
      headSkeletonRow_bounded, verifySkeletonRow_bounded, tailSkeletonRow_bounded⟩
  · intro tree htree node hnode
    change tree ∈ [dummyHaltSkeletonTree, readSkeletonTree] at htree
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htree
    rcases htree with rfl | rfl
    · have hm : node ∈ bfsForest [dummyHaltSkeletonTree] :=
        (mem_bfsForest [dummyHaltSkeletonTree] node).2 ⟨dummyHaltSkeletonTree, by simp, hnode⟩
      simp [dummyHaltSkeletonTree, bfsForest] at hm
      subst hm
      exact dummyHaltSkeletonRow_bounded
    · have hm : node ∈ bfsForest [readSkeletonTree] :=
        (mem_bfsForest [readSkeletonTree] node).2 ⟨readSkeletonTree, by simp, hnode⟩
      simp [readSkeletonTree, decomposeSkeletonTree, headSkeletonTree,
        verifySkeletonTree, tailSkeletonTree, bfsForest] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl
      · exact readSkeletonRow_bounded
      · exact decomposeSkeletonRow_bounded
      · exact headSkeletonRow_bounded
      · exact verifySkeletonRow_bounded
      · exact tailSkeletonRow_bounded

/-- `combinedBounded`: every comparison-census noun pair is `q = 97`-bounded on both sides. -/
theorem combinedBounded :
    ProductionP8Containment.CombinedBoundedBy F 97 semanticSkeleton := by
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
    simp [FieldEmbedding.BoundedBy, subjectNoun, formulaNoun, headNoun, resultNoun,
      SemanticStrategy.SemanticSkeleton.publicClaim, SemanticTrace.ComparisonUse.pair,
      decActive]

/-- `census`: the comparison census of the skeleton lies inside the paper's leaf window `Λ = 3`. -/
def census : EdgeComparisonCensus.CombinedSkeletonCensus F semanticSkeleton 3 where
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
          simp [subjectNoun, formulaNoun, headNoun, resultNoun,
            SemanticStrategy.SemanticSkeleton.publicClaim,
            SemanticTrace.ComparisonUse.pair, decActive, Noun.leaves] }
  edges :=
    { leaves_bounded := by
        intro pair hp
        simp [EdgeComparisonCensus.edgePairs, EdgeComparisonCensus.rowEdgePairs,
          semanticSkeleton, computeSkeletonRow, NTree.childOpt, bfsForest] at hp }

end Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton.slotSemantics
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton.recordEquations
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton.sizeWindowBound
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton.skeletonBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton.combinedBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton.census
