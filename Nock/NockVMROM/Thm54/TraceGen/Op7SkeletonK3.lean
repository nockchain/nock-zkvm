/-
  Nock/NockVMROM/Thm54/TraceGen/Op7SkeletonK3.lean

  Field-free semantic skeleton of the fan-out-2 compose program

      `*[0 [7 [[1 3] [1 5]]]] = 5`

  plus the six seed-free census-closure obligations an honest `HonestCommitment.Data` over
  that skeleton must discharge.  The `.s7` root has fan-out 2 and two live records
  (formula@3, formula-tail@2); each `.s1` child has one record (formula@3).  The memory
  forest is the 17-row single-root reconstruction of those four records.  Leaf window
  `Λ = 5` (the parent formula has five atoms).  Census/`combinedBounded` are stated over
  the table field `K3`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op7Gen
import Nock.NockVMROM.Thm54.TraceGen.CubicField97
import Nock.NockVMROM.Thm54.EdgeComparisonCensus
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.ServedLookupBridge
import Mathlib.Tactic.NormNum.Prime

namespace Nock.NockVMROM.Thm54.TraceGen.Op7Skeleton

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open SemanticStrategy ServedLookupBridge
open Nock.NockVMROM.Thm54.TraceGen

set_option linter.unusedSimpArgs false

def op1Head : Noun := .atom 1
def op7Head : Noun := .atom 7

instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

abbrev F : Type := ZMod 97
abbrev K : Type := CubicField97.K3

/-! ## Committed records (nouns + Nat axes, no timestamps) -/

def recF : MemRecSkeleton where
  root := op7ParentFormula
  child := op7ParentTail
  axis := 3
def recT : MemRecSkeleton where
  root := op7ParentTail
  child := op7ChildFormulaB
  axis := 2
def recB : MemRecSkeleton where
  root := op7ChildFormulaB
  child := op7Sb
  axis := 3
def recC : MemRecSkeleton where
  root := op7ChildFormulaC
  child := op7Result
  axis := 3

/-! ## Compute rows (`.s7` root + two `OP_1` children) -/

def parentRow : ComputeRowSkeleton where
  state := .s7
  subject := op7Subject
  formula := op7ParentFormula
  evaluation := op7Result
  decomposition := fun slot _ =>
    match slot with
    | .f_h => op7Head
    | .f_t => op7ParentTail
    | .f_th => op7ChildFormulaB
    | .f_tt => op7ChildFormulaC
    | _ => .atom 0
  subformula := fun i _ slot =>
    match (i : ℕ), slot with
    | 0, .subject => op7Sb
    | 0, .formula => op7ChildFormulaC
    | 0, .result => op7Result
    | 1, .subject => op7Subject
    | 1, .formula => op7ChildFormulaB
    | 1, .result => op7Sb
    | _, _ => .atom 0
  memoryRecord := fun i _ =>
    if i = 0 then recF else recT

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

def child1Row : ComputeRowSkeleton := op1Row op7Subject op7ChildFormulaB op7Sb recB
def child2Row : ComputeRowSkeleton := op1Row op7Sb op7ChildFormulaC op7Result recC

def computeTree : NTree ComputeRowSkeleton :=
  .node parentRow [.node child2Row [], .node child1Row []]

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

def skReadF : MemoryRowSkeleton := readRow op7ParentFormula recF
def skDecF : MemoryRowSkeleton := decRow op7ParentFormula op7Head op7ParentTail
def skHalt7 : MemoryRowSkeleton := haltRow 7
def skVerifyF : MemoryRowSkeleton := verifyRow op7ParentTail recF
def skReadT : MemoryRowSkeleton := readRow op7ParentTail recT
def skDecT : MemoryRowSkeleton := decRow op7ParentTail op7ChildFormulaB op7ChildFormulaC
def skVerifyT : MemoryRowSkeleton := verifyRow op7ChildFormulaB recT
def skReadB : MemoryRowSkeleton := readRow op7ChildFormulaB recB
def skDecB : MemoryRowSkeleton := decRow op7ChildFormulaB op1Head op7Sb
def skHaltB1 : MemoryRowSkeleton := haltRow 1
def skVerifyB : MemoryRowSkeleton := verifyRow op7Sb recB
def skHalt3 : MemoryRowSkeleton := haltRow 3
def skReadC : MemoryRowSkeleton := readRow op7ChildFormulaC recC
def skDecC : MemoryRowSkeleton := decRow op7ChildFormulaC op1Head op7Result
def skHaltC1 : MemoryRowSkeleton := haltRow 1
def skVerifyC : MemoryRowSkeleton := verifyRow op7Result recC
def skHalt5 : MemoryRowSkeleton := haltRow 5

def mLeaf (r : MemoryRowSkeleton) : NTree MemoryRowSkeleton := .node r []
def mOne (r : MemoryRowSkeleton) (c : NTree MemoryRowSkeleton) : NTree MemoryRowSkeleton :=
  .node r [c]
def mTwo (r : MemoryRowSkeleton) (l s : NTree MemoryRowSkeleton) : NTree MemoryRowSkeleton :=
  .node r [l, s]

def tHalt7 : NTree MemoryRowSkeleton := mLeaf skHalt7
def tHalt3 : NTree MemoryRowSkeleton := mLeaf skHalt3
def tHalt5 : NTree MemoryRowSkeleton := mLeaf skHalt5
def tHaltB1 : NTree MemoryRowSkeleton := mLeaf skHaltB1
def tHaltC1 : NTree MemoryRowSkeleton := mLeaf skHaltC1
def tVerifyB : NTree MemoryRowSkeleton := mOne skVerifyB tHalt3
def tDecB : NTree MemoryRowSkeleton := mTwo skDecB tHaltB1 tVerifyB
def tReadB : NTree MemoryRowSkeleton := mOne skReadB tDecB
def tVerifyT : NTree MemoryRowSkeleton := mOne skVerifyT tReadB
def tVerifyC : NTree MemoryRowSkeleton := mOne skVerifyC tHalt5
def tDecC : NTree MemoryRowSkeleton := mTwo skDecC tHaltC1 tVerifyC
def tReadC : NTree MemoryRowSkeleton := mOne skReadC tDecC
def tDecT : NTree MemoryRowSkeleton := mTwo skDecT tVerifyT tReadC
def tReadT : NTree MemoryRowSkeleton := mOne skReadT tDecT
def tVerifyF : NTree MemoryRowSkeleton := mOne skVerifyF tReadT
def tDecF : NTree MemoryRowSkeleton := mTwo skDecF tHalt7 tVerifyF
def readFTree : NTree MemoryRowSkeleton := mOne skReadF tDecF

def semanticSkeleton : SemanticSkeleton where
  computeTree := computeTree
  memoryForest := [readFTree]

theorem computeRows_eq :
    computeSkeletonRows semanticSkeleton = [parentRow, child2Row, child1Row] := by
  norm_num [computeSkeletonRows, semanticSkeleton, computeTree, bfsForest,
    NTree.size, totalSize]

theorem memoryRows_eq :
    memorySkeletonRows semanticSkeleton =
      [skReadF, skDecF, skHalt7, skVerifyF, skReadT, skDecT, skVerifyT, skReadC,
        skReadB, skDecC, skDecB, skHaltC1, skVerifyC, skHaltB1, skVerifyB, skHalt5, skHalt3] := by
  norm_num [memorySkeletonRows, semanticSkeleton, readFTree, tDecF, tHalt7, tVerifyF,
    tReadT, tDecT, tVerifyT, tReadB, tDecB, tHaltB1, tVerifyB, tHalt3,
    tReadC, tDecC, tHaltC1, tVerifyC, tHalt5,
    mLeaf, mOne, mTwo, bfsForest, NTree.size, totalSize]

/-! ## The six seed-free census-closure obligations -/

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
    SizeWindowCounting.SizeWindowNounsBoundedBy semanticSkeleton 5 := by
  intro n hn
  rw [SizeWindowCounting.skeletonSizeWindowNouns, computeRows_eq] at hn
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hn
  simp [SizeWindowCounting.requiredSizeWindowNouns, parentRow, child1Row, child2Row,
    op1Row] at hn

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
  simp [recF, MemRecSkeleton.BoundedBy, op7ParentFormula, op7ParentTail, op7ChildFormulaB,
    op7ChildFormulaC, op7Sb, op7Result, op7Head, op1Head,
    FieldEmbedding.BoundedBy]
theorem recT_bounded : recT.BoundedBy 97 := by
  simp [recT, MemRecSkeleton.BoundedBy, op7ParentTail, op7ChildFormulaB, op7ChildFormulaC,
    op7Sb, op7Result, op1Head, FieldEmbedding.BoundedBy]
theorem recB_bounded : recB.BoundedBy 97 := by
  simp [recB, MemRecSkeleton.BoundedBy, op7ChildFormulaB, op7Sb, op1Head, FieldEmbedding.BoundedBy]
theorem recC_bounded : recC.BoundedBy 97 := by
  simp [recC, MemRecSkeleton.BoundedBy, op7ChildFormulaC, op7Result, op1Head, FieldEmbedding.BoundedBy]

theorem parentRow_bounded : parentRow.BoundedBy 97 := by
  refine ⟨by simp [parentRow, op7Subject, FieldEmbedding.BoundedBy],
    by simp [parentRow, op7ParentFormula, op7ParentTail, op7ChildFormulaB, op7ChildFormulaC,
      op7Sb, op7Result, op7Head, op1Head, FieldEmbedding.BoundedBy],
    by simp [parentRow, op7Result, FieldEmbedding.BoundedBy], ?_, ?_, ?_⟩
  · intro slot h
    cases slot <;>
      simp [parentRow, op7Head, op7ParentTail, op7ChildFormulaB, op7ChildFormulaC, op7Sb,
        op7Result, op1Head, FieldEmbedding.BoundedBy]
  · intro i h slot
    fin_cases i <;> cases slot <;>
      simp [parentRow, op7Subject, op7ChildFormulaB, op7ChildFormulaC, op7Sb, op7Result,
        op1Head, FieldEmbedding.BoundedBy]
  · intro i h
    simp [parentRow]
    split_ifs <;> simp [recF_bounded, recT_bounded]

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
  op1Row_bounded (by simp [op7Subject, FieldEmbedding.BoundedBy])
    (by simp [op7ChildFormulaB, op7Sb, op1Head, FieldEmbedding.BoundedBy])
    (by simp [op7Sb, FieldEmbedding.BoundedBy]) recB_bounded
theorem child2Row_bounded : child2Row.BoundedBy 97 :=
  op1Row_bounded (by simp [op7Sb, FieldEmbedding.BoundedBy])
    (by simp [op7ChildFormulaC, op7Result, op1Head, FieldEmbedding.BoundedBy])
    (by simp [op7Result, FieldEmbedding.BoundedBy]) recC_bounded

private theorem b_formula : FieldEmbedding.BoundedBy 97 op7ParentFormula := by
  simp [op7ParentFormula, op7ParentTail, op7ChildFormulaB, op7ChildFormulaC, op7Sb, op7Result,
    op7Head, op1Head, FieldEmbedding.BoundedBy]
private theorem b_tail : FieldEmbedding.BoundedBy 97 op7ParentTail := by
  simp [op7ParentTail, op7ChildFormulaB, op7ChildFormulaC, op7Sb, op7Result, op1Head,
    FieldEmbedding.BoundedBy]
private theorem b_c1 : FieldEmbedding.BoundedBy 97 op7ChildFormulaB := by
  simp [op7ChildFormulaB, op7Sb, op1Head, FieldEmbedding.BoundedBy]
private theorem b_c2 : FieldEmbedding.BoundedBy 97 op7ChildFormulaC := by
  simp [op7ChildFormulaC, op7Result, op1Head, FieldEmbedding.BoundedBy]
private theorem b_sb : FieldEmbedding.BoundedBy 97 op7Sb := by
  simp [op7Sb, FieldEmbedding.BoundedBy]
private theorem b_result : FieldEmbedding.BoundedBy 97 op7Result := by
  simp [op7Result, FieldEmbedding.BoundedBy]
private theorem b_head7 : FieldEmbedding.BoundedBy 97 op7Head := by
  simp [op7Head, FieldEmbedding.BoundedBy]
private theorem b_head1 : FieldEmbedding.BoundedBy 97 op1Head := by
  simp [op1Head, FieldEmbedding.BoundedBy]

theorem skeletonBounded : semanticSkeleton.BoundedBy 97 := by
  refine { computeRows := ?_, memoryRows := ?_, memoryTrees := ?_ }
  · rw [computeRows_eq]
    exact ⟨parentRow_bounded, child2Row_bounded, child1Row_bounded⟩
  · rw [memoryRows_eq]
    exact ⟨readRow_bounded b_formula recF_bounded, decRow_bounded b_formula b_head7 b_tail,
      haltRow_bounded (by norm_num), verifyRow_bounded b_tail recF_bounded,
      readRow_bounded b_tail recT_bounded, decRow_bounded b_tail b_c1 b_c2,
      verifyRow_bounded b_c1 recT_bounded, readRow_bounded b_c2 recC_bounded,
      readRow_bounded b_c1 recB_bounded, decRow_bounded b_c2 b_head1 b_result,
      decRow_bounded b_c1 b_head1 b_sb, haltRow_bounded (by norm_num),
      verifyRow_bounded b_result recC_bounded, haltRow_bounded (by norm_num),
      verifyRow_bounded b_sb recB_bounded, haltRow_bounded (by norm_num),
      haltRow_bounded (by norm_num)⟩
  · intro tree htree node hnode
    simp only [semanticSkeleton, List.mem_singleton] at htree
    subst tree
    have hm : node ∈ bfsForest [readFTree] :=
      (mem_bfsForest [readFTree] node).2 ⟨readFTree, by simp, hnode⟩
    simp [readFTree, tDecF, tHalt7, tVerifyF, tReadT, tDecT, tVerifyT, tReadB, tDecB,
      tHaltB1, tVerifyB, tHalt3, tReadC, tDecC, tHaltC1, tVerifyC, tHalt5,
      mLeaf, mOne, mTwo, bfsForest] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl
    · exact readRow_bounded b_formula recF_bounded
    · exact decRow_bounded b_formula b_head7 b_tail
    · exact haltRow_bounded (by norm_num)
    · exact verifyRow_bounded b_tail recF_bounded
    · exact readRow_bounded b_tail recT_bounded
    · exact decRow_bounded b_tail b_c1 b_c2
    · exact verifyRow_bounded b_c1 recT_bounded
    · exact readRow_bounded b_c2 recC_bounded
    · exact readRow_bounded b_c1 recB_bounded
    · exact decRow_bounded b_c2 b_head1 b_result
    · exact decRow_bounded b_c1 b_head1 b_sb
    · exact haltRow_bounded (by norm_num)
    · exact verifyRow_bounded b_result recC_bounded
    · exact haltRow_bounded (by norm_num)
    · exact verifyRow_bounded b_sb recB_bounded
    · exact haltRow_bounded (by norm_num)
    · exact haltRow_bounded (by norm_num)

/-! ### Comparison census over `K3` (`Λ = 5`) -/

theorem combinedBounded :
    ProductionP8Containment.CombinedBoundedBy K 97 semanticSkeleton := by
  intro pair hp
  simp [EdgeComparisonCensus.combinedSkeletonPairs, BoundSemanticTrace.skeletonPairs,
    EdgeComparisonCensus.edgePairs, EdgeComparisonCensus.rowEdgePairs,
    EdgeComparisonCensus.edgeTriple, P8Census.skeletonComparisonCensus,
    P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
    P8Census.skeletonSubformula, SemanticStrategy.SemanticSkeleton.publicClaim,
    SemanticTrace.ComparisonUse.pair, semanticSkeleton, computeTree, computeSkeletonRows,
    parentRow, child1Row, child2Row, op1Row, op7Subject, op7ParentFormula,
    op7ParentTail, op7ChildFormulaB, op7ChildFormulaC, op7Sb, op7Result, op7Head, op1Head,
    recF, recT, recB, recC, decActive, ComputeTable.fanoutComp,
    NTree.childOpt, NTree.label, bfsForest, NTree.size, totalSize, List.flatMap_cons,
    List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil, List.cons_append,
    List.nil_append, List.ofFn_succ, List.ofFn_zero, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.getElem?_nil, Option.map_some, Option.map_none] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [FieldEmbedding.BoundedBy, hasTailDecomposition, decActive, ComputeTable.fanoutComp,
      op7Subject, op7ParentFormula, op7ParentTail, op7ChildFormulaB, op7ChildFormulaC,
      op7Sb, op7Result, op7Head, op1Head, Noun.tis]

def census : EdgeComparisonCensus.CombinedSkeletonCensus K semanticSkeleton 5 where
  p8 :=
    { leaves_bounded := by
        intro pair hp
        simp [BoundSemanticTrace.skeletonPairs, P8Census.skeletonComparisonCensus,
          P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
          P8Census.skeletonSubformula, SemanticStrategy.SemanticSkeleton.publicClaim,
          SemanticTrace.ComparisonUse.pair, semanticSkeleton, computeTree, computeSkeletonRows,
          parentRow, child1Row, child2Row, op1Row, op7Subject, op7ParentFormula,
          op7ParentTail, op7ChildFormulaB, op7ChildFormulaC, op7Sb, op7Result, op7Head, op1Head,
          decActive, ComputeTable.fanoutComp, NTree.label, bfsForest, NTree.size,
          totalSize, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
          List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [hasTailDecomposition, decActive, ComputeTable.fanoutComp, op7Subject,
            op7ParentFormula, op7ParentTail, op7ChildFormulaB, op7ChildFormulaC, op7Sb,
            op7Result, op7Head, op1Head, Noun.tis, Noun.leaves] }
  edges :=
    { leaves_bounded := by
        intro pair hp
        simp [EdgeComparisonCensus.edgePairs, EdgeComparisonCensus.rowEdgePairs,
          EdgeComparisonCensus.edgeTriple, P8Census.skeletonSubformula, semanticSkeleton,
          computeTree, parentRow, child1Row, child2Row, op1Row, op7Subject,
          op7ChildFormulaB, op7ChildFormulaC, op7Sb, op7Result, op7Head, op1Head,
          ComputeTable.fanoutComp, NTree.childOpt, NTree.label, bfsForest, NTree.size,
          totalSize, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
          List.append_nil, List.cons_append, List.nil_append, List.ofFn_succ, List.ofFn_zero,
          List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
          List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
          Option.map_some, Option.map_none] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [hasTailDecomposition, decActive, ComputeTable.fanoutComp, op7Subject,
            op7ParentFormula, op7ParentTail, op7ChildFormulaB, op7ChildFormulaC, op7Sb,
            op7Result, op7Head, op1Head, Noun.tis, Noun.leaves] }

end Nock.NockVMROM.Thm54.TraceGen.Op7Skeleton

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op7Skeleton.slotSemantics
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op7Skeleton.recordEquations
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op7Skeleton.sizeWindowBound
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op7Skeleton.skeletonBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op7Skeleton.combinedBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op7Skeleton.census
