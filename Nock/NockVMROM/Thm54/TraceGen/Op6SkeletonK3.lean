/-
  Nock/NockVMROM/Thm54/TraceGen/Op6SkeletonK3.lean

  Field-free semantic skeleton of the fan-out-2 branch (if) program

      `*[0 [6 [[1 0] [[1 5] [1 6]]]]] = 5`

  plus the census-closure obligations.  The `.s6` root has fan-out 2 and three live records
  (formula@3, formula-tail@2, branch-pair@2); each `.s1` child has one record (child-formula@3).
  The memory forest is the 23-row single-root reconstruction of all five records.  Leaf window
  `Λ = 7` (the parent formula has seven atoms).  Census/`combinedBounded` are stated over
  the table field `K3`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op6Gen
import Nock.NockVMROM.Thm54.TraceGen.CubicField97
import Nock.NockVMROM.Thm54.EdgeComparisonCensus
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.ServedLookupBridge
import Mathlib.Tactic.NormNum.Prime

namespace Nock.NockVMROM.Thm54.TraceGen.Op6Skeleton

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open SemanticStrategy ServedLookupBridge
open Nock.NockVMROM.Thm54.TraceGen

set_option linter.unusedSimpArgs false

def op1Head : Noun := .atom 1
def op6Head : Noun := .atom 6

instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

abbrev F : Type := ZMod 97
abbrev K : Type := CubicField97.K3

/-! ## Committed records (nouns + Nat axes, no timestamps) -/

def recF : MemRecSkeleton where
  root := op6ParentFormula
  child := op6ParentTail
  axis := 3
def recT : MemRecSkeleton where
  root := op6ParentTail
  child := op6CondFormula
  axis := 2
def recP : MemRecSkeleton where
  root := op6BranchPair
  child := op6BranchC
  axis := 2
def recC1 : MemRecSkeleton where
  root := op6BranchC
  child := op6Result
  axis := 3
def recC2 : MemRecSkeleton where
  root := op6CondFormula
  child := op6CondResult
  axis := 3

/-! ## Compute rows (`.s6` root + two `OP_1` children) -/

def parentRow : ComputeRowSkeleton where
  state := .s6
  subject := op6Subject
  formula := op6ParentFormula
  evaluation := op6Result
  decomposition := fun slot _ =>
    match slot with
    | .f_h => op6Head
    | .f_t => op6ParentTail
    | .f_th => op6CondFormula
    | .f_tt => op6BranchPair
    | .f_tth => op6BranchC
    | .f_ttt => op6BranchD
  subformula := fun i _ slot =>
    match (i : ℕ), slot with
    | 0, .subject => op6Subject
    | 0, .formula => op6BranchC
    | 0, .result => op6Result
    | 1, .subject => op6Subject
    | 1, .formula => op6CondFormula
    | 1, .result => op6CondResult
    | _, _ => .atom 0
  memoryRecord := fun i _ =>
    match (i : ℕ) with
    | 0 => recF
    | 1 => recT
    | _ => recP

def op1Row (subject formula result : Noun) (rec : MemRecSkeleton) :
    ComputeRowSkeleton where
  state := .s1
  subject := subject
  formula := formula
  evaluation := result
  decomposition := fun slot _ =>
    match slot with
    | .f_h => op1Head
    | .f_t => result
    | _ => .atom 0
  subformula := fun i hi _ => absurd hi (by
    simp [ComputeTable.fanoutComp] at hi)
  memoryRecord := fun i _ =>
    if i = 0 then rec else ⟨.atom 0, .atom 0, 0⟩

def child1Row : ComputeRowSkeleton := op1Row op6Subject op6BranchC op6Result recC1
def child2Row : ComputeRowSkeleton := op1Row op6Subject op6CondFormula op6CondResult recC2

def computeTree : NTree ComputeRowSkeleton :=
  .node parentRow [.node child1Row [], .node child2Row []]

/-! ## Memory-row helpers -/

def haltRow (n : ℕ) : MemoryRowSkeleton where
  state := .halt
  parent := .atom n
  haltAtom := fun _ => n
  haltParent := by intro h; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

def readRow (parent : Noun) (rec : MemRecSkeleton) : MemoryRowSkeleton where
  state := .read_root
  parent := parent
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if i = 0 then parent else .atom 0
  memoryRecord := fun _ => rec

def verifyRow (parent : Noun) (rec : MemRecSkeleton) : MemoryRowSkeleton where
  state := .verify_child
  parent := parent
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => parent
  memoryRecord := fun _ => rec

def decRow (parent left right : Noun) : MemoryRowSkeleton where
  state := .decompose
  parent := parent
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if i = 0 then left else right
  memoryRecord := fun h => nomatch h

/-! ## The 23 skeleton memory rows -/

def skReadF : MemoryRowSkeleton := readRow op6ParentFormula recF
def skDecF : MemoryRowSkeleton := decRow op6ParentFormula op6Head op6ParentTail
def skHalt6 : MemoryRowSkeleton := haltRow 6
def skVerifyF : MemoryRowSkeleton := verifyRow op6ParentTail recF

def skReadT : MemoryRowSkeleton := readRow op6ParentTail recT
def skDecT : MemoryRowSkeleton := decRow op6ParentTail op6CondFormula op6BranchPair
def skVerifyT : MemoryRowSkeleton := verifyRow op6CondFormula recT

def skReadC2 : MemoryRowSkeleton := readRow op6CondFormula recC2
def skDecC2 : MemoryRowSkeleton := decRow op6CondFormula op1Head (.atom 0)
def skHalt1_c2 : MemoryRowSkeleton := haltRow 1
def skVerifyC2 : MemoryRowSkeleton := verifyRow op6CondResult recC2
def skHalt0 : MemoryRowSkeleton := haltRow 0

def skReadP : MemoryRowSkeleton := readRow op6BranchPair recP
def skDecP : MemoryRowSkeleton := decRow op6BranchPair op6BranchC op6BranchD
def skVerifyP : MemoryRowSkeleton := verifyRow op6BranchC recP

def skReadC1 : MemoryRowSkeleton := readRow op6BranchC recC1
def skDecC1 : MemoryRowSkeleton := decRow op6BranchC op1Head (.atom 5)
def skHalt1_c1 : MemoryRowSkeleton := haltRow 1
def skVerifyC1 : MemoryRowSkeleton := verifyRow op6Result recC1
def skHalt5 : MemoryRowSkeleton := haltRow 5

def skDecBranchD : MemoryRowSkeleton := decRow op6BranchD op1Head (.atom 6)
def skHalt1_d : MemoryRowSkeleton := haltRow 1
def skHalt6_d : MemoryRowSkeleton := haltRow 6

/-! ## Memory forest tree assembly -/

def mLeaf (r : MemoryRowSkeleton) : NTree MemoryRowSkeleton := .node r []
def mOne (r : MemoryRowSkeleton) (c : NTree MemoryRowSkeleton) : NTree MemoryRowSkeleton :=
  .node r [c]
def mTwo (r : MemoryRowSkeleton) (l s : NTree MemoryRowSkeleton) : NTree MemoryRowSkeleton :=
  .node r [l, s]

def tHalt6 : NTree MemoryRowSkeleton := mLeaf skHalt6
def tHalt0 : NTree MemoryRowSkeleton := mLeaf skHalt0
def tHalt5 : NTree MemoryRowSkeleton := mLeaf skHalt5
def tHalt1_c2 : NTree MemoryRowSkeleton := mLeaf skHalt1_c2
def tHalt1_c1 : NTree MemoryRowSkeleton := mLeaf skHalt1_c1
def tHalt1_d : NTree MemoryRowSkeleton := mLeaf skHalt1_d
def tHalt6_d : NTree MemoryRowSkeleton := mLeaf skHalt6_d

def tVerifyC2 : NTree MemoryRowSkeleton := mOne skVerifyC2 tHalt0
def tDecC2 : NTree MemoryRowSkeleton := mTwo skDecC2 tHalt1_c2 tVerifyC2
def tReadC2 : NTree MemoryRowSkeleton := mOne skReadC2 tDecC2
def tVerifyT : NTree MemoryRowSkeleton := mOne skVerifyT tReadC2

def tVerifyC1 : NTree MemoryRowSkeleton := mOne skVerifyC1 tHalt5
def tDecC1 : NTree MemoryRowSkeleton := mTwo skDecC1 tHalt1_c1 tVerifyC1
def tReadC1 : NTree MemoryRowSkeleton := mOne skReadC1 tDecC1
def tVerifyP : NTree MemoryRowSkeleton := mOne skVerifyP tReadC1

def tDecBranchD : NTree MemoryRowSkeleton := mTwo skDecBranchD tHalt1_d tHalt6_d
def tDecP : NTree MemoryRowSkeleton := mTwo skDecP tVerifyP tDecBranchD
def tReadP : NTree MemoryRowSkeleton := mOne skReadP tDecP

def tDecT : NTree MemoryRowSkeleton := mTwo skDecT tVerifyT tReadP
def tReadT : NTree MemoryRowSkeleton := mOne skReadT tDecT

def tVerifyF : NTree MemoryRowSkeleton := mOne skVerifyF tReadT
def tDecF : NTree MemoryRowSkeleton := mTwo skDecF tHalt6 tVerifyF
def readFTree : NTree MemoryRowSkeleton := mOne skReadF tDecF

def semanticSkeleton : SemanticSkeleton where
  computeTree := computeTree
  memoryForest := [readFTree]

theorem computeRows_eq :
    computeSkeletonRows semanticSkeleton = [parentRow, child1Row, child2Row] := by
  norm_num [computeSkeletonRows, semanticSkeleton, computeTree, bfsForest,
    NTree.size, totalSize]

theorem memoryRows_eq :
    memorySkeletonRows semanticSkeleton =
      [skReadF, skDecF, skHalt6, skVerifyF, skReadT, skDecT, skVerifyT, skReadP,
       skReadC2, skDecP, skDecC2, skVerifyP, skDecBranchD,
       skHalt1_c2, skVerifyC2, skReadC1, skHalt1_d, skHalt6_d,
       skHalt0, skDecC1, skHalt1_c1, skVerifyC1, skHalt5] := by
  norm_num [memorySkeletonRows, semanticSkeleton, readFTree, tDecF, tHalt6, tVerifyF,
    tReadT, tDecT, tVerifyT, tReadC2, tDecC2, tHalt1_c2, tVerifyC2, tHalt0,
    tReadP, tDecP, tVerifyP, tReadC1, tDecC1, tHalt1_c1, tVerifyC1, tHalt5,
    tDecBranchD, tHalt1_d, tHalt6_d,
    mLeaf, mOne, mTwo, bfsForest, NTree.size, totalSize]

/-! ## The seed-free census-closure obligations -/

theorem slotSemantics :
    ∀ s ∈ computeSkeletonRows semanticSkeleton, SkeletonSlotSemantics s := by
  intro s hs
  rw [computeRows_eq] at hs
  fin_cases hs <;>
    exact
      { s0_slot := fun h => absurd h (by simp [parentRow, child1Row, child2Row, op1Row])
        s9_slot := fun h => absurd h (by simp [parentRow, child1Row, child2Row, op1Row]) }

theorem recordEquations :
    ∀ s ∈ computeSkeletonRows semanticSkeleton, SkeletonRecordEquations s := by
  intro s hs
  rw [computeRows_eq] at hs
  fin_cases hs <;>
    exact
      { s0_record := fun h => absurd h (by simp [parentRow, child1Row, child2Row, op1Row])
        s9_record := fun h => absurd h (by simp [parentRow, child1Row, child2Row, op1Row]) }

theorem sizeWindowBound :
    SizeWindowCounting.SizeWindowNounsBoundedBy semanticSkeleton 7 := by
  intro n hn
  rw [SizeWindowCounting.skeletonSizeWindowNouns, computeRows_eq] at hn
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hn
  simp only [SizeWindowCounting.requiredSizeWindowNouns, parentRow, child1Row, child2Row,
    op1Row, op6CondResult, ComputeTable.fanoutComp, FieldEmbedding.BoundedBy,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, List.mem_nil_iff, or_false, false_or] at hn
  subst hn
  decide

/-! ### Boundedness -/

private theorem atom_bounded {n : ℕ} (hn : n < 97) :
    FieldEmbedding.BoundedBy 97 (.atom n) := by
  simp [FieldEmbedding.BoundedBy]; exact hn

theorem haltRow_bounded {n : ℕ} (hn : n < 97) : (haltRow n).BoundedBy 97 := by
  refine ⟨atom_bounded hn, ?_, ?_⟩
  · intro i h
    simp [haltRow, MemoryTable.fanoutMem] at h
  · intro h
    simp [haltRow, memoryMemRecKind] at h

theorem readRow_bounded {parent : Noun} {rec : MemRecSkeleton}
    (hp : FieldEmbedding.BoundedBy 97 parent) (hr : rec.BoundedBy 97) :
    (readRow parent rec).BoundedBy 97 := by
  refine ⟨hp, ?_, fun _ => hr⟩
  intro i h
  simp [readRow]
  split_ifs <;> simp [hp, FieldEmbedding.BoundedBy]

theorem verifyRow_bounded {parent : Noun} {rec : MemRecSkeleton}
    (hp : FieldEmbedding.BoundedBy 97 parent) (hr : rec.BoundedBy 97) :
    (verifyRow parent rec).BoundedBy 97 := by
  refine ⟨hp, ?_, fun _ => hr⟩
  intro i h
  simp [verifyRow, hp]

theorem decRow_bounded {parent left right : Noun}
    (hp : FieldEmbedding.BoundedBy 97 parent)
    (hl : FieldEmbedding.BoundedBy 97 left) (hr : FieldEmbedding.BoundedBy 97 right) :
    (decRow parent left right).BoundedBy 97 := by
  refine ⟨hp, ?_, ?_⟩
  · intro i h
    simp [decRow]
    split_ifs <;> simp [hl, hr]
  · intro h
    simp [decRow, memoryMemRecKind] at h

theorem recF_bounded : recF.BoundedBy 97 := by
  simp [recF, MemRecSkeleton.BoundedBy, op6ParentFormula, op6ParentTail, op6CondFormula,
    op6BranchPair, op6BranchC, op6BranchD, FieldEmbedding.BoundedBy]
theorem recT_bounded : recT.BoundedBy 97 := by
  simp [recT, MemRecSkeleton.BoundedBy, op6ParentTail, op6CondFormula, op6BranchPair,
    op6BranchC, op6BranchD, FieldEmbedding.BoundedBy]
theorem recP_bounded : recP.BoundedBy 97 := by
  simp [recP, MemRecSkeleton.BoundedBy, op6BranchPair, op6BranchC, op6BranchD,
    FieldEmbedding.BoundedBy]

theorem recC1_bounded : recC1.BoundedBy 97 := by
  simp [recC1, MemRecSkeleton.BoundedBy, op6BranchC, op6Result, FieldEmbedding.BoundedBy]
theorem recC2_bounded : recC2.BoundedBy 97 := by
  simp [recC2, MemRecSkeleton.BoundedBy, op6CondFormula, op6CondResult, FieldEmbedding.BoundedBy]

theorem parentRow_bounded : parentRow.BoundedBy 97 := by
  refine ⟨by simp [parentRow, op6Subject, FieldEmbedding.BoundedBy],
    by simp [parentRow, op6ParentFormula, op6ParentTail, op6CondFormula, op6BranchPair,
      op6BranchC, op6BranchD, op6Head, op1Head, FieldEmbedding.BoundedBy],
    by simp [parentRow, op6Result, FieldEmbedding.BoundedBy], ?_, ?_, ?_⟩
  · intro slot h
    cases slot <;>
      simp [parentRow, op6Head, op6ParentTail, op6CondFormula, op6BranchPair, op6BranchC,
        op6BranchD, op1Head, FieldEmbedding.BoundedBy]
  · intro i h slot
    fin_cases i <;> cases slot <;>
      simp [parentRow, op6Subject, op6CondFormula, op6BranchPair, op6BranchC, op6BranchD,
        op6Result, op6CondResult, op1Head, FieldEmbedding.BoundedBy]
  · intro i h
    simp only [parentRow]
    fin_cases i <;> simp [recF_bounded, recT_bounded, recP_bounded]

theorem op1Row_bounded {subject formula result : Noun} {rec : MemRecSkeleton}
    (hs : FieldEmbedding.BoundedBy 97 subject)
    (hf : FieldEmbedding.BoundedBy 97 formula)
    (he : FieldEmbedding.BoundedBy 97 result)
    (hr : rec.BoundedBy 97) :
    (op1Row subject formula result rec).BoundedBy 97 := by
  refine ⟨hs, hf, he, ?_, ?_, ?_⟩
  · intro slot h
    cases slot <;> simp [op1Row, op1Head, FieldEmbedding.BoundedBy, he]
  · intro i h
    simp [op1Row, ComputeTable.fanoutComp] at h
  · intro i h
    simp [op1Row]
    split_ifs
    · exact hr
    · simp [MemRecSkeleton.BoundedBy, FieldEmbedding.BoundedBy]

theorem child1Row_bounded : child1Row.BoundedBy 97 :=
  op1Row_bounded (by simp [op6Subject, FieldEmbedding.BoundedBy])
    (by simp [op6BranchC, FieldEmbedding.BoundedBy])
    (by simp [op6Result, FieldEmbedding.BoundedBy]) recC1_bounded
theorem child2Row_bounded : child2Row.BoundedBy 97 :=
  op1Row_bounded (by simp [op6Subject, FieldEmbedding.BoundedBy])
    (by simp [op6CondFormula, FieldEmbedding.BoundedBy])
    (by simp [op6CondResult, FieldEmbedding.BoundedBy]) recC2_bounded

private theorem b_formula : FieldEmbedding.BoundedBy 97 op6ParentFormula := by
  simp [op6ParentFormula, op6ParentTail, op6CondFormula, op6BranchPair, op6BranchC, op6BranchD,
    op6Head, op1Head, FieldEmbedding.BoundedBy]
private theorem b_tail : FieldEmbedding.BoundedBy 97 op6ParentTail := by
  simp [op6ParentTail, op6CondFormula, op6BranchPair, op6BranchC, op6BranchD, op1Head,
    FieldEmbedding.BoundedBy]
private theorem b_condFormula : FieldEmbedding.BoundedBy 97 op6CondFormula := by
  simp [op6CondFormula, FieldEmbedding.BoundedBy]
private theorem b_branchPair : FieldEmbedding.BoundedBy 97 op6BranchPair := by
  simp [op6BranchPair, op6BranchC, op6BranchD, FieldEmbedding.BoundedBy]
private theorem b_branchC : FieldEmbedding.BoundedBy 97 op6BranchC := by
  simp [op6BranchC, FieldEmbedding.BoundedBy]
private theorem b_branchD : FieldEmbedding.BoundedBy 97 op6BranchD := by
  simp [op6BranchD, FieldEmbedding.BoundedBy]
private theorem b_result : FieldEmbedding.BoundedBy 97 op6Result := by
  simp [op6Result, FieldEmbedding.BoundedBy]
private theorem b_condResult : FieldEmbedding.BoundedBy 97 op6CondResult := by
  simp [op6CondResult, FieldEmbedding.BoundedBy]
private theorem b_head6 : FieldEmbedding.BoundedBy 97 op6Head := by
  simp [op6Head, FieldEmbedding.BoundedBy]
private theorem b_head1 : FieldEmbedding.BoundedBy 97 op1Head := by
  simp [op1Head, FieldEmbedding.BoundedBy]

theorem skeletonBounded : semanticSkeleton.BoundedBy 97 := by
  refine { computeRows := ?_, memoryRows := ?_, memoryTrees := ?_ }
  · rw [computeRows_eq]
    exact ⟨parentRow_bounded, child1Row_bounded, child2Row_bounded⟩
  · rw [memoryRows_eq]
    exact ⟨readRow_bounded b_formula recF_bounded, decRow_bounded b_formula b_head6 b_tail,
      haltRow_bounded (by norm_num), verifyRow_bounded b_tail recF_bounded,
      readRow_bounded b_tail recT_bounded, decRow_bounded b_tail b_condFormula b_branchPair,
      verifyRow_bounded b_condFormula recT_bounded,
      readRow_bounded b_branchPair recP_bounded,
      readRow_bounded b_condFormula recC2_bounded,
      decRow_bounded b_branchPair b_branchC b_branchD,
      decRow_bounded b_condFormula b_head1 (atom_bounded (by norm_num)),
      verifyRow_bounded b_branchC recP_bounded,
      decRow_bounded b_branchD b_head1 (atom_bounded (by norm_num)),
      haltRow_bounded (by norm_num),
      verifyRow_bounded b_condResult recC2_bounded,
      readRow_bounded b_branchC recC1_bounded,
      haltRow_bounded (by norm_num), haltRow_bounded (by norm_num),
      haltRow_bounded (by norm_num),
      decRow_bounded b_branchC b_head1 (atom_bounded (by norm_num)),
      haltRow_bounded (by norm_num),
      verifyRow_bounded b_result recC1_bounded,
      haltRow_bounded (by norm_num)⟩
  · intro tree htree node hnode
    simp only [semanticSkeleton, List.mem_singleton] at htree
    subst tree
    have hm : node ∈ bfsForest [readFTree] :=
      (mem_bfsForest [readFTree] node).2 ⟨readFTree, by simp, hnode⟩
    simp [readFTree, tDecF, tHalt6, tVerifyF, tReadT, tDecT, tVerifyT, tReadC2, tDecC2,
      tHalt1_c2, tVerifyC2, tHalt0, tReadP, tDecP, tVerifyP, tReadC1, tDecC1,
      tHalt1_c1, tVerifyC1, tHalt5, tDecBranchD, tHalt1_d, tHalt6_d,
      mLeaf, mOne, mTwo, bfsForest] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact readRow_bounded b_formula recF_bounded
    · exact decRow_bounded b_formula b_head6 b_tail
    · exact haltRow_bounded (by norm_num)
    · exact verifyRow_bounded b_tail recF_bounded
    · exact readRow_bounded b_tail recT_bounded
    · exact decRow_bounded b_tail b_condFormula b_branchPair
    · exact verifyRow_bounded b_condFormula recT_bounded
    · exact readRow_bounded b_branchPair recP_bounded
    · exact readRow_bounded b_condFormula recC2_bounded
    · exact decRow_bounded b_branchPair b_branchC b_branchD
    · exact decRow_bounded b_condFormula b_head1 (atom_bounded (by norm_num))
    · exact verifyRow_bounded b_branchC recP_bounded
    · exact decRow_bounded b_branchD b_head1 (atom_bounded (by norm_num))
    · exact haltRow_bounded (by norm_num)
    · exact verifyRow_bounded b_condResult recC2_bounded
    · exact readRow_bounded b_branchC recC1_bounded
    · exact haltRow_bounded (by norm_num)
    · exact haltRow_bounded (by norm_num)
    · exact haltRow_bounded (by norm_num)
    · exact decRow_bounded b_branchC b_head1 (atom_bounded (by norm_num))
    · exact haltRow_bounded (by norm_num)
    · exact verifyRow_bounded b_result recC1_bounded
    · exact haltRow_bounded (by norm_num)

/-! ### Comparison census over `K3` (`Λ = 7`) -/

theorem combinedBounded :
    ProductionP8Containment.CombinedBoundedBy K 97 semanticSkeleton := by
  intro pair hp
  simp [EdgeComparisonCensus.combinedSkeletonPairs, BoundSemanticTrace.skeletonPairs,
    EdgeComparisonCensus.edgePairs, EdgeComparisonCensus.rowEdgePairs,
    EdgeComparisonCensus.edgeTriple, P8Census.skeletonComparisonCensus,
    P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
    P8Census.skeletonSubformula, SemanticStrategy.SemanticSkeleton.publicClaim,
    SemanticTrace.ComparisonUse.pair, semanticSkeleton, computeTree, computeSkeletonRows,
    parentRow, child1Row, child2Row, op1Row, op6Subject, op6ParentFormula,
    op6ParentTail, op6CondFormula, op6BranchPair, op6BranchC, op6BranchD, op6Result,
    op6CondResult, op6Head, op1Head, recF, recT, recP, recC1, recC2,
    decActive, ComputeTable.fanoutComp,
    NTree.childOpt, NTree.label, bfsForest, NTree.size, totalSize, List.flatMap_cons,
    List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil, List.cons_append,
    List.nil_append, List.ofFn_succ, List.ofFn_zero, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.getElem?_nil, Option.map_some, Option.map_none] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [FieldEmbedding.BoundedBy, hasTailDecomposition, decActive, ComputeTable.fanoutComp,
      op6Subject, op6ParentFormula, op6ParentTail, op6CondFormula, op6BranchPair, op6BranchC,
      op6BranchD, op6Result, op6CondResult, op6Head, op1Head, Noun.tis]

def census : EdgeComparisonCensus.CombinedSkeletonCensus K semanticSkeleton 7 where
  p8 :=
    { leaves_bounded := by
        intro pair hp
        simp [BoundSemanticTrace.skeletonPairs, P8Census.skeletonComparisonCensus,
          P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
          P8Census.skeletonSubformula, SemanticStrategy.SemanticSkeleton.publicClaim,
          SemanticTrace.ComparisonUse.pair, semanticSkeleton, computeTree, computeSkeletonRows,
          parentRow, child1Row, child2Row, op1Row, op6Subject, op6ParentFormula,
          op6ParentTail, op6CondFormula, op6BranchPair, op6BranchC, op6BranchD, op6Result,
          op6CondResult, op6Head, op1Head, recF, recT, recP, recC1, recC2,
          decActive, ComputeTable.fanoutComp, NTree.label, bfsForest, NTree.size,
          totalSize, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
          List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [hasTailDecomposition, decActive, ComputeTable.fanoutComp, op6Subject,
            op6ParentFormula, op6ParentTail, op6CondFormula, op6BranchPair, op6BranchC,
            op6BranchD, op6Result, op6CondResult, op6Head, op1Head, Noun.tis, Noun.leaves] }
  edges :=
    { leaves_bounded := by
        intro pair hp
        simp [EdgeComparisonCensus.edgePairs, EdgeComparisonCensus.rowEdgePairs,
          EdgeComparisonCensus.edgeTriple, P8Census.skeletonSubformula, semanticSkeleton,
          computeTree, parentRow, child1Row, child2Row, op1Row, op6Subject,
          op6CondFormula, op6BranchPair, op6BranchC, op6BranchD, op6Result, op6CondResult,
          op6Head, op1Head,
          ComputeTable.fanoutComp, NTree.childOpt, NTree.label, bfsForest, NTree.size,
          totalSize, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
          List.append_nil, List.cons_append, List.nil_append, List.ofFn_succ, List.ofFn_zero,
          List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
          List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
          Option.map_some, Option.map_none] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [hasTailDecomposition, decActive, ComputeTable.fanoutComp, op6Subject,
            op6ParentFormula, op6ParentTail, op6CondFormula, op6BranchPair, op6BranchC,
            op6BranchD, op6Result, op6CondResult, op6Head, op1Head, Noun.tis, Noun.leaves] }

end Nock.NockVMROM.Thm54.TraceGen.Op6Skeleton

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6Skeleton.slotSemantics
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6Skeleton.recordEquations
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6Skeleton.sizeWindowBound
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6Skeleton.skeletonBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6Skeleton.combinedBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6Skeleton.census
