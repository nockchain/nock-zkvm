/-
  Nock/NockVMROM/Thm54/TraceGen/Op5SkeletonK3.lean

  Field-free semantic skeleton of the fan-out-2 equality program

      `*[0 [5 [1 3] [1 4]]] = 1`

  plus the six seed-free census-closure obligations an honest `HonestCommitment.Data` over
  that skeleton must discharge.  The `.s5` root has fan-out 2 and two live records
  (formula@3, formula-tail@2); each `.s1` child has one record (formula@3).  The memory
  forest is the 17-row single-root reconstruction of those four records.  Leaf window
  `Λ = 5` (the parent formula has five atoms).  Census/`combinedBounded` are stated over
  the table field `K3`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op5Gen
import Nock.NockVMROM.Thm54.TraceGen.CubicField97
import Nock.NockVMROM.Thm54.EdgeComparisonCensus
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.ServedLookupBridge
import Mathlib.Tactic.NormNum.Prime

namespace Nock.NockVMROM.Thm54.TraceGen.Op5Skeleton

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open SemanticStrategy ServedLookupBridge
open Nock.NockVMROM.Thm54.TraceGen

set_option linter.unusedSimpArgs false

def op1Head : Noun := .atom 1
def op5Head : Noun := .atom 5

instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

abbrev F : Type := ZMod 97
abbrev K : Type := CubicField97.K3

/-! ## Committed records (nouns + Nat axes, no timestamps) -/

def recF : MemRecSkeleton where
  root := op5ParentFormula
  child := op5ParentTail
  axis := 3
def recT : MemRecSkeleton where
  root := op5ParentTail
  child := op5ChildFormulaB
  axis := 2
def recB : MemRecSkeleton where
  root := op5ChildFormulaB
  child := op5Sf1
  axis := 3
def recC : MemRecSkeleton where
  root := op5ChildFormulaC
  child := op5Sf2
  axis := 3

/-! ## Compute rows (`.s5` root + two `OP_1` children) -/

def parentRow : ComputeRowSkeleton where
  state := .s5
  subject := op5Subject
  formula := op5ParentFormula
  evaluation := op5Result
  decomposition := fun slot _ =>
    match slot with
    | .f_h => op5Head
    | .f_t => op5ParentTail
    | .f_th => op5ChildFormulaB
    | .f_tt => op5ChildFormulaC
    | _ => .atom 0
  subformula := fun i _ slot =>
    match (i : ℕ), slot with
    | 0, .subject => op5Subject
    | 0, .formula => op5ChildFormulaB
    | 0, .result => op5Sf1
    | 1, .subject => op5Subject
    | 1, .formula => op5ChildFormulaC
    | 1, .result => op5Sf2
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

def child1Row : ComputeRowSkeleton := op1Row op5Subject op5ChildFormulaB op5Sf1 recB
def child2Row : ComputeRowSkeleton := op1Row op5Subject op5ChildFormulaC op5Sf2 recC

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

def skReadF : MemoryRowSkeleton := readRow op5ParentFormula recF
def skDecF : MemoryRowSkeleton := decRow op5ParentFormula op5Head op5ParentTail
def skHalt5 : MemoryRowSkeleton := haltRow 5
def skVerifyF : MemoryRowSkeleton := verifyRow op5ParentTail recF
def skReadT : MemoryRowSkeleton := readRow op5ParentTail recT
def skDecT : MemoryRowSkeleton := decRow op5ParentTail op5ChildFormulaB op5ChildFormulaC
def skVerifyT : MemoryRowSkeleton := verifyRow op5ChildFormulaB recT
def skReadB : MemoryRowSkeleton := readRow op5ChildFormulaB recB
def skDecB : MemoryRowSkeleton := decRow op5ChildFormulaB op1Head op5Sf1
def skHaltB1 : MemoryRowSkeleton := haltRow 1
def skVerifyB : MemoryRowSkeleton := verifyRow op5Sf1 recB
def skHalt3 : MemoryRowSkeleton := haltRow 3
def skReadC : MemoryRowSkeleton := readRow op5ChildFormulaC recC
def skDecC : MemoryRowSkeleton := decRow op5ChildFormulaC op1Head op5Sf2
def skHaltC1 : MemoryRowSkeleton := haltRow 1
def skVerifyC : MemoryRowSkeleton := verifyRow op5Sf2 recC
def skHalt4 : MemoryRowSkeleton := haltRow 4

def mLeaf (r : MemoryRowSkeleton) : NTree MemoryRowSkeleton := .node r []
def mOne (r : MemoryRowSkeleton) (c : NTree MemoryRowSkeleton) : NTree MemoryRowSkeleton :=
  .node r [c]
def mTwo (r : MemoryRowSkeleton) (l s : NTree MemoryRowSkeleton) : NTree MemoryRowSkeleton :=
  .node r [l, s]

def tHalt5 : NTree MemoryRowSkeleton := mLeaf skHalt5
def tHalt3 : NTree MemoryRowSkeleton := mLeaf skHalt3
def tHalt4 : NTree MemoryRowSkeleton := mLeaf skHalt4
def tHaltB1 : NTree MemoryRowSkeleton := mLeaf skHaltB1
def tHaltC1 : NTree MemoryRowSkeleton := mLeaf skHaltC1
def tVerifyB : NTree MemoryRowSkeleton := mOne skVerifyB tHalt3
def tDecB : NTree MemoryRowSkeleton := mTwo skDecB tHaltB1 tVerifyB
def tReadB : NTree MemoryRowSkeleton := mOne skReadB tDecB
def tVerifyT : NTree MemoryRowSkeleton := mOne skVerifyT tReadB
def tVerifyC : NTree MemoryRowSkeleton := mOne skVerifyC tHalt4
def tDecC : NTree MemoryRowSkeleton := mTwo skDecC tHaltC1 tVerifyC
def tReadC : NTree MemoryRowSkeleton := mOne skReadC tDecC
def tDecT : NTree MemoryRowSkeleton := mTwo skDecT tVerifyT tReadC
def tReadT : NTree MemoryRowSkeleton := mOne skReadT tDecT
def tVerifyF : NTree MemoryRowSkeleton := mOne skVerifyF tReadT
def tDecF : NTree MemoryRowSkeleton := mTwo skDecF tHalt5 tVerifyF
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
      [skReadF, skDecF, skHalt5, skVerifyF, skReadT, skDecT, skVerifyT, skReadC,
        skReadB, skDecC, skDecB, skHaltC1, skVerifyC, skHaltB1, skVerifyB, skHalt4, skHalt3] := by
  norm_num [memorySkeletonRows, semanticSkeleton, readFTree, tDecF, tHalt5, tVerifyF,
    tReadT, tDecT, tVerifyT, tReadB, tDecB, tHaltB1, tVerifyB, tHalt3,
    tReadC, tDecC, tHaltC1, tVerifyC, tHalt4,
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
  simp [recF, MemRecSkeleton.BoundedBy, op5ParentFormula, op5ParentTail, op5ChildFormulaB,
    op5ChildFormulaC, op5Sf1, op5Sf2, op5Head, op1Head,
    FieldEmbedding.BoundedBy]
theorem recT_bounded : recT.BoundedBy 97 := by
  simp [recT, MemRecSkeleton.BoundedBy, op5ParentTail, op5ChildFormulaB, op5ChildFormulaC,
    op5Sf1, op5Sf2, op1Head, FieldEmbedding.BoundedBy]
theorem recB_bounded : recB.BoundedBy 97 := by
  simp [recB, MemRecSkeleton.BoundedBy, op5ChildFormulaB, op5Sf1, op1Head, FieldEmbedding.BoundedBy]
theorem recC_bounded : recC.BoundedBy 97 := by
  simp [recC, MemRecSkeleton.BoundedBy, op5ChildFormulaC, op5Sf2, op1Head, FieldEmbedding.BoundedBy]

theorem parentRow_bounded : parentRow.BoundedBy 97 := by
  refine ⟨by simp [parentRow, op5Subject, FieldEmbedding.BoundedBy],
    by simp [parentRow, op5ParentFormula, op5ParentTail, op5ChildFormulaB, op5ChildFormulaC,
      op5Sf1, op5Sf2, op5Head, op1Head, FieldEmbedding.BoundedBy],
    by simp [parentRow, op5Result_is_one, FieldEmbedding.BoundedBy], ?_, ?_, ?_⟩
  · intro slot h
    cases slot <;>
      simp [parentRow, op5Head, op5ParentTail, op5ChildFormulaB, op5ChildFormulaC, op5Sf1,
        op5Sf2, op1Head, FieldEmbedding.BoundedBy]
  · intro i h slot
    fin_cases i <;> cases slot <;>
      simp [parentRow, op5Subject, op5ChildFormulaB, op5ChildFormulaC, op5Sf1, op5Sf2,
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
  op1Row_bounded (by simp [op5Subject, FieldEmbedding.BoundedBy])
    (by simp [op5ChildFormulaB, op5Sf1, op1Head, FieldEmbedding.BoundedBy])
    (by simp [op5Sf1, FieldEmbedding.BoundedBy]) recB_bounded
theorem child2Row_bounded : child2Row.BoundedBy 97 :=
  op1Row_bounded (by simp [op5Subject, FieldEmbedding.BoundedBy])
    (by simp [op5ChildFormulaC, op5Sf2, op1Head, FieldEmbedding.BoundedBy])
    (by simp [op5Sf2, FieldEmbedding.BoundedBy]) recC_bounded

private theorem b_formula : FieldEmbedding.BoundedBy 97 op5ParentFormula := by
  simp [op5ParentFormula, op5ParentTail, op5ChildFormulaB, op5ChildFormulaC, op5Sf1, op5Sf2,
    op5Head, op1Head, FieldEmbedding.BoundedBy]
private theorem b_tail : FieldEmbedding.BoundedBy 97 op5ParentTail := by
  simp [op5ParentTail, op5ChildFormulaB, op5ChildFormulaC, op5Sf1, op5Sf2, op1Head,
    FieldEmbedding.BoundedBy]
private theorem b_c1 : FieldEmbedding.BoundedBy 97 op5ChildFormulaB := by
  simp [op5ChildFormulaB, op5Sf1, op1Head, FieldEmbedding.BoundedBy]
private theorem b_c2 : FieldEmbedding.BoundedBy 97 op5ChildFormulaC := by
  simp [op5ChildFormulaC, op5Sf2, op1Head, FieldEmbedding.BoundedBy]
private theorem b_sf1 : FieldEmbedding.BoundedBy 97 op5Sf1 := by
  simp [op5Sf1, FieldEmbedding.BoundedBy]
private theorem b_sf2 : FieldEmbedding.BoundedBy 97 op5Sf2 := by
  simp [op5Sf2, FieldEmbedding.BoundedBy]
private theorem b_head5 : FieldEmbedding.BoundedBy 97 op5Head := by
  simp [op5Head, FieldEmbedding.BoundedBy]
private theorem b_head1 : FieldEmbedding.BoundedBy 97 op1Head := by
  simp [op1Head, FieldEmbedding.BoundedBy]

theorem skeletonBounded : semanticSkeleton.BoundedBy 97 := by
  refine { computeRows := ?_, memoryRows := ?_, memoryTrees := ?_ }
  · rw [computeRows_eq]
    exact ⟨parentRow_bounded, child1Row_bounded, child2Row_bounded⟩
  · rw [memoryRows_eq]
    exact ⟨readRow_bounded b_formula recF_bounded, decRow_bounded b_formula b_head5 b_tail,
      haltRow_bounded (by norm_num), verifyRow_bounded b_tail recF_bounded,
      readRow_bounded b_tail recT_bounded, decRow_bounded b_tail b_c1 b_c2,
      verifyRow_bounded b_c1 recT_bounded, readRow_bounded b_c2 recC_bounded,
      readRow_bounded b_c1 recB_bounded, decRow_bounded b_c2 b_head1 b_sf2,
      decRow_bounded b_c1 b_head1 b_sf1, haltRow_bounded (by norm_num),
      verifyRow_bounded b_sf2 recC_bounded, haltRow_bounded (by norm_num),
      verifyRow_bounded b_sf1 recB_bounded, haltRow_bounded (by norm_num),
      haltRow_bounded (by norm_num)⟩
  · intro tree htree node hnode
    simp only [semanticSkeleton, List.mem_singleton] at htree
    subst tree
    have hm : node ∈ bfsForest [readFTree] :=
      (mem_bfsForest [readFTree] node).2 ⟨readFTree, by simp, hnode⟩
    simp [readFTree, tDecF, tHalt5, tVerifyF, tReadT, tDecT, tVerifyT, tReadB, tDecB,
      tHaltB1, tVerifyB, tHalt3, tReadC, tDecC, tHaltC1, tVerifyC, tHalt4,
      mLeaf, mOne, mTwo, bfsForest] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl
    · exact readRow_bounded b_formula recF_bounded
    · exact decRow_bounded b_formula b_head5 b_tail
    · exact haltRow_bounded (by norm_num)
    · exact verifyRow_bounded b_tail recF_bounded
    · exact readRow_bounded b_tail recT_bounded
    · exact decRow_bounded b_tail b_c1 b_c2
    · exact verifyRow_bounded b_c1 recT_bounded
    · exact readRow_bounded b_c2 recC_bounded
    · exact readRow_bounded b_c1 recB_bounded
    · exact decRow_bounded b_c2 b_head1 b_sf2
    · exact decRow_bounded b_c1 b_head1 b_sf1
    · exact haltRow_bounded (by norm_num)
    · exact verifyRow_bounded b_sf2 recC_bounded
    · exact haltRow_bounded (by norm_num)
    · exact verifyRow_bounded b_sf1 recB_bounded
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
    parentRow, child1Row, child2Row, op1Row, op5Subject, op5ParentFormula,
    op5ParentTail, op5ChildFormulaB, op5ChildFormulaC, op5Sf1, op5Sf2, op5Head, op1Head,
    op5Result, recF, recT, recB, recC, decActive, ComputeTable.fanoutComp,
    NTree.childOpt, NTree.label, bfsForest, NTree.size, totalSize, List.flatMap_cons,
    List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil, List.cons_append,
    List.nil_append, List.ofFn_succ, List.ofFn_zero, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.getElem?_nil, Option.map_some, Option.map_none] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [FieldEmbedding.BoundedBy, hasTailDecomposition, decActive, ComputeTable.fanoutComp,
      op5Subject, op5ParentFormula, op5ParentTail, op5ChildFormulaB, op5ChildFormulaC,
      op5Sf1, op5Sf2, op5Head, op1Head, op5Result, Noun.tis]

def census : EdgeComparisonCensus.CombinedSkeletonCensus K semanticSkeleton 5 where
  p8 :=
    { leaves_bounded := by
        intro pair hp
        simp [BoundSemanticTrace.skeletonPairs, P8Census.skeletonComparisonCensus,
          P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
          P8Census.skeletonSubformula, SemanticStrategy.SemanticSkeleton.publicClaim,
          SemanticTrace.ComparisonUse.pair, semanticSkeleton, computeTree, computeSkeletonRows,
          parentRow, child1Row, child2Row, op1Row, op5Subject, op5ParentFormula,
          op5ParentTail, op5ChildFormulaB, op5ChildFormulaC, op5Sf1, op5Sf2, op5Head, op1Head,
          op5Result, decActive, ComputeTable.fanoutComp, NTree.label, bfsForest, NTree.size,
          totalSize, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
          List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [hasTailDecomposition, decActive, ComputeTable.fanoutComp, op5Subject,
            op5ParentFormula, op5ParentTail, op5ChildFormulaB, op5ChildFormulaC, op5Sf1,
            op5Sf2, op5Head, op1Head, op5Result, Noun.tis, Noun.leaves] }
  edges :=
    { leaves_bounded := by
        intro pair hp
        simp [EdgeComparisonCensus.edgePairs, EdgeComparisonCensus.rowEdgePairs,
          EdgeComparisonCensus.edgeTriple, P8Census.skeletonSubformula, semanticSkeleton,
          computeTree, parentRow, child1Row, child2Row, op1Row, op5Subject,
          op5ChildFormulaB, op5ChildFormulaC, op5Sf1, op5Sf2, op5Head, op1Head, op5Result,
          ComputeTable.fanoutComp, NTree.childOpt, NTree.label, bfsForest, NTree.size,
          totalSize, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
          List.append_nil, List.cons_append, List.nil_append, List.ofFn_succ, List.ofFn_zero,
          List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
          List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
          Option.map_some, Option.map_none] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [hasTailDecomposition, decActive, ComputeTable.fanoutComp, op5Subject,
            op5ParentFormula, op5ParentTail, op5ChildFormulaB, op5ChildFormulaC, op5Sf1,
            op5Sf2, op5Head, op1Head, op5Result, Noun.tis, Noun.leaves] }

end Nock.NockVMROM.Thm54.TraceGen.Op5Skeleton

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op5Skeleton.slotSemantics
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op5Skeleton.recordEquations
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op5Skeleton.sizeWindowBound
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op5Skeleton.skeletonBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op5Skeleton.combinedBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op5Skeleton.census
