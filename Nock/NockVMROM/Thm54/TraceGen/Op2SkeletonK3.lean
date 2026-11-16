/-
  Nock/NockVMROM/Thm54/TraceGen/Op2SkeletonK3.lean

  Field-free semantic skeleton of the fan-out-3 eval program

      `*[0 [2 [1 [0 1]] [1 [1 5]]]] = 5`

  plus the six seed-free census-closure obligations an honest `HonestCommitment.Data` over
  that skeleton must discharge.  The `.s2` root has fan-out 3 and two live records
  (formula@3, formula-tail@2); the memory forest is the 23-row single-root reconstruction
  of those five records, including the axis-2 left descent.  Leaf window `Λ = 7` (the parent formula has seven atoms).
  Census/`combinedBounded` are stated over the table field `K3`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op2Gen
import Nock.NockVMROM.Thm54.TraceGen.CubicField97
import Nock.NockVMROM.Thm54.EdgeComparisonCensus
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.ServedLookupBridge
import Mathlib.Tactic.NormNum.Prime

namespace Nock.NockVMROM.Thm54.TraceGen.Op2Skeleton

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open SemanticStrategy ServedLookupBridge
open Nock.NockVMROM.Thm54.TraceGen

set_option linter.unusedSimpArgs false

def op1Head : Noun := .atom 1
def op2Head : Noun := .atom 2

instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

abbrev F : Type := ZMod 97
abbrev K : Type := CubicField97.K3

/-! ## Committed records (nouns + Nat axes, no timestamps) -/

def recF : MemRecSkeleton where
  root := op2ParentFormula
  child := op2ParentTail
  axis := 3
def recT : MemRecSkeleton where
  root := op2ParentTail
  child := op2ChildFormula1
  axis := 2
def recB : MemRecSkeleton where
  root := op2ChildFormula1
  child := op2Sf1
  axis := 3
def recC : MemRecSkeleton where
  root := op2ChildFormula2
  child := op2Sf2
  axis := 3
def recS : MemRecSkeleton where
  root := op2Sf2
  child := op2Result
  axis := 3

/-! ## Compute rows (`.s2` root + three `OP_1` children) -/

/-- The `.s2` parent: fan-out 3, active tail `f_th`/`f_tt`, two live records. -/
def parentRow : ComputeRowSkeleton where
  state := .s2
  subject := op2Subject
  formula := op2ParentFormula
  evaluation := op2Result
  decomposition := fun slot _ =>
    match slot with
    | .f_h => op2Head
    | .f_t => op2ParentTail
    | .f_th => op2ChildFormula1
    | .f_tt => op2ChildFormula2
    | _ => .atom 0
  subformula := fun i _ slot =>
    match (i : ℕ), slot with
    | 0, .subject => op2Subject
    | 0, .formula => op2ChildFormula1
    | 0, .result => op2Sf1
    | 1, .subject => op2Subject
    | 1, .formula => op2ChildFormula2
    | 1, .result => op2Sf2
    | _, .subject => op2Sf1
    | _, .formula => op2Sf2
    | _, .result => op2Result
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

def child1Row : ComputeRowSkeleton := op1Row op2Subject op2ChildFormula1 op2Sf1 recB
def child2Row : ComputeRowSkeleton := op1Row op2Subject op2ChildFormula2 op2Sf2 recC
def child3Row : ComputeRowSkeleton := op1Row op2Sf1 op2Sf2 op2Result recS

def computeTree : NTree ComputeRowSkeleton :=
  .node parentRow [.node child1Row [], .node child2Row [], .node child3Row []]

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

def skReadF : MemoryRowSkeleton := readRow op2ParentFormula recF
def skDecF : MemoryRowSkeleton := decRow op2ParentFormula op2Head op2ParentTail
def skHalt2 : MemoryRowSkeleton := haltRow 2
def skVerifyF : MemoryRowSkeleton := verifyRow op2ParentTail recF
def skReadT : MemoryRowSkeleton := readRow op2ParentTail recT
def skDecT : MemoryRowSkeleton := decRow op2ParentTail op2ChildFormula1 op2ChildFormula2
def skVerifyT : MemoryRowSkeleton := verifyRow op2ChildFormula1 recT
def skReadC : MemoryRowSkeleton := readRow op2ChildFormula2 recC
def skReadB : MemoryRowSkeleton := readRow op2ChildFormula1 recB
def skDecC : MemoryRowSkeleton := decRow op2ChildFormula2 op1Head op2Sf2
def skDecB : MemoryRowSkeleton := decRow op2ChildFormula1 op1Head op2Sf1
def skHaltC1 : MemoryRowSkeleton := haltRow 1
def skVerifyC : MemoryRowSkeleton := verifyRow op2Sf2 recC
def skHaltB1 : MemoryRowSkeleton := haltRow 1
def skVerifyB : MemoryRowSkeleton := verifyRow op2Sf1 recB
def skReadS : MemoryRowSkeleton := readRow op2Sf2 recS
def skDecSf1 : MemoryRowSkeleton := decRow op2Sf1 (.atom 0) (.atom 1)
def skDecS : MemoryRowSkeleton := decRow op2Sf2 op1Head op2Result
def skHalt0 : MemoryRowSkeleton := haltRow 0
def skHalt1s : MemoryRowSkeleton := haltRow 1
def skHaltS1 : MemoryRowSkeleton := haltRow 1
def skVerifyS : MemoryRowSkeleton := verifyRow op2Result recS
def skHalt5 : MemoryRowSkeleton := haltRow 5

def mLeaf (r : MemoryRowSkeleton) : NTree MemoryRowSkeleton := .node r []
def mOne (r : MemoryRowSkeleton) (c : NTree MemoryRowSkeleton) : NTree MemoryRowSkeleton :=
  .node r [c]
def mTwo (r : MemoryRowSkeleton) (l s : NTree MemoryRowSkeleton) : NTree MemoryRowSkeleton :=
  .node r [l, s]

def tHalt5 : NTree MemoryRowSkeleton := mLeaf skHalt5
def tVerifyS : NTree MemoryRowSkeleton := mOne skVerifyS tHalt5
def tHaltS1 : NTree MemoryRowSkeleton := mLeaf skHaltS1
def tDecS : NTree MemoryRowSkeleton := mTwo skDecS tHaltS1 tVerifyS
def tReadS : NTree MemoryRowSkeleton := mOne skReadS tDecS
def tHalt0 : NTree MemoryRowSkeleton := mLeaf skHalt0
def tHalt1s : NTree MemoryRowSkeleton := mLeaf skHalt1s
def tDecSf1 : NTree MemoryRowSkeleton := mTwo skDecSf1 tHalt0 tHalt1s
def tVerifyB : NTree MemoryRowSkeleton := mOne skVerifyB tDecSf1
def tHaltB1 : NTree MemoryRowSkeleton := mLeaf skHaltB1
def tDecB : NTree MemoryRowSkeleton := mTwo skDecB tHaltB1 tVerifyB
def tReadB : NTree MemoryRowSkeleton := mOne skReadB tDecB
def tVerifyC : NTree MemoryRowSkeleton := mOne skVerifyC tReadS
def tHaltC1 : NTree MemoryRowSkeleton := mLeaf skHaltC1
def tDecC : NTree MemoryRowSkeleton := mTwo skDecC tHaltC1 tVerifyC
def tReadC : NTree MemoryRowSkeleton := mOne skReadC tDecC
def tVerifyT : NTree MemoryRowSkeleton := mOne skVerifyT tReadB
def tDecT : NTree MemoryRowSkeleton := mTwo skDecT tVerifyT tReadC
def tReadT : NTree MemoryRowSkeleton := mOne skReadT tDecT
def tVerifyF : NTree MemoryRowSkeleton := mOne skVerifyF tReadT
def tHalt2 : NTree MemoryRowSkeleton := mLeaf skHalt2
def tDecF : NTree MemoryRowSkeleton := mTwo skDecF tHalt2 tVerifyF
def readFTree : NTree MemoryRowSkeleton := mOne skReadF tDecF

def semanticSkeleton : SemanticSkeleton where
  computeTree := computeTree
  memoryForest := [readFTree]

theorem computeRows_eq :
    computeSkeletonRows semanticSkeleton = [parentRow, child1Row, child2Row, child3Row] := by
  norm_num [computeSkeletonRows, semanticSkeleton, computeTree, bfsForest,
    NTree.size, totalSize]

theorem memoryRows_eq :
    memorySkeletonRows semanticSkeleton =
      [skReadF, skDecF, skHalt2, skVerifyF, skReadT, skDecT, skVerifyT, skReadC, skReadB,
        skDecC, skDecB, skHaltC1, skVerifyC, skHaltB1, skVerifyB, skReadS, skDecSf1, skDecS,
        skHalt0, skHalt1s, skHaltS1, skVerifyS, skHalt5] := by
  norm_num [memorySkeletonRows, semanticSkeleton, readFTree, tDecF, tHalt2, tVerifyF,
    tReadT, tDecT, tVerifyT, tReadC, tReadB, tDecC, tDecB, tHaltC1, tVerifyC, tHaltB1,
    tVerifyB, tReadS, tDecSf1, tDecS, tHalt0, tHalt1s, tHaltS1, tVerifyS, tHalt5,
    mLeaf, mOne, mTwo, bfsForest, NTree.size, totalSize]

/-! ## The six seed-free census-closure obligations -/

theorem slotSemantics :
    ∀ s ∈ computeSkeletonRows semanticSkeleton, SkeletonSlotSemantics s := by
  intro s hs
  rw [computeRows_eq] at hs
  fin_cases hs <;>
    exact
      { s0_slot := fun h => absurd h (by simp [parentRow, child1Row, child2Row, child3Row, op1Row])
        s9_slot := fun h => absurd h (by simp [parentRow, child1Row, child2Row, child3Row, op1Row]) }

theorem recordEquations :
    ∀ s ∈ computeSkeletonRows semanticSkeleton, SkeletonRecordEquations s := by
  intro s hs
  rw [computeRows_eq] at hs
  fin_cases hs <;>
    exact
      { s0_record := fun h => absurd h (by simp [parentRow, child1Row, child2Row, child3Row, op1Row])
        s9_record := fun h => absurd h (by simp [parentRow, child1Row, child2Row, child3Row, op1Row]) }

theorem sizeWindowBound :
    SizeWindowCounting.SizeWindowNounsBoundedBy semanticSkeleton 7 := by
  intro n hn
  rw [SizeWindowCounting.skeletonSizeWindowNouns, computeRows_eq] at hn
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hn
  simp [SizeWindowCounting.requiredSizeWindowNouns, parentRow, child1Row, child2Row, child3Row,
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
  simp [recF, MemRecSkeleton.BoundedBy, op2ParentFormula, op2ParentTail, op2ChildFormula1,
    op2ChildFormula2, op2Sf1, op2Sf2, op2Head, op1Head, op2Result, op2Subject,
    FieldEmbedding.BoundedBy]
theorem recT_bounded : recT.BoundedBy 97 := by
  simp [recT, MemRecSkeleton.BoundedBy, op2ParentTail, op2ChildFormula1, op2ChildFormula2,
    op2Sf1, op2Sf2, op1Head, op2Result, FieldEmbedding.BoundedBy]
theorem recB_bounded : recB.BoundedBy 97 := by
  simp [recB, MemRecSkeleton.BoundedBy, op2ChildFormula1, op2Sf1, op1Head, FieldEmbedding.BoundedBy]
theorem recC_bounded : recC.BoundedBy 97 := by
  simp [recC, MemRecSkeleton.BoundedBy, op2ChildFormula2, op2Sf2, op1Head, op2Result,
    FieldEmbedding.BoundedBy]
theorem recS_bounded : recS.BoundedBy 97 := by
  simp [recS, MemRecSkeleton.BoundedBy, op2Sf2, op2Result, op1Head, FieldEmbedding.BoundedBy]

theorem parentRow_bounded : parentRow.BoundedBy 97 := by
  refine ⟨by simp [parentRow, op2Subject, FieldEmbedding.BoundedBy],
    by simp [parentRow, op2ParentFormula, op2ParentTail, op2ChildFormula1, op2ChildFormula2,
      op2Sf1, op2Sf2, op2Head, op1Head, op2Result, FieldEmbedding.BoundedBy],
    by simp [parentRow, op2Result, FieldEmbedding.BoundedBy], ?_, ?_, ?_⟩
  · intro slot h
    cases slot <;>
      simp [parentRow, op2Head, op2ParentTail, op2ChildFormula1, op2ChildFormula2, op2Sf1,
        op2Sf2, op1Head, op2Result, FieldEmbedding.BoundedBy]
  · intro i h slot
    fin_cases i <;> cases slot <;>
      simp [parentRow, op2Subject, op2ChildFormula1, op2ChildFormula2, op2Sf1, op2Sf2,
        op2Result, op1Head, FieldEmbedding.BoundedBy]
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
  op1Row_bounded (by simp [op2Subject, FieldEmbedding.BoundedBy])
    (by simp [op2ChildFormula1, op2Sf1, op1Head, FieldEmbedding.BoundedBy])
    (by simp [op2Sf1, FieldEmbedding.BoundedBy]) recB_bounded
theorem child2Row_bounded : child2Row.BoundedBy 97 :=
  op1Row_bounded (by simp [op2Subject, FieldEmbedding.BoundedBy])
    (by simp [op2ChildFormula2, op2Sf2, op1Head, op2Result, FieldEmbedding.BoundedBy])
    (by simp [op2Sf2, op1Head, op2Result, FieldEmbedding.BoundedBy]) recC_bounded
theorem child3Row_bounded : child3Row.BoundedBy 97 :=
  op1Row_bounded (by simp [op2Sf1, FieldEmbedding.BoundedBy])
    (by simp [op2Sf2, op1Head, op2Result, FieldEmbedding.BoundedBy])
    (by simp [op2Result, FieldEmbedding.BoundedBy]) recS_bounded

private theorem b_formula : FieldEmbedding.BoundedBy 97 op2ParentFormula := by
  simp [op2ParentFormula, op2ParentTail, op2ChildFormula1, op2ChildFormula2, op2Sf1, op2Sf2,
    op2Head, op1Head, op2Result, FieldEmbedding.BoundedBy]
private theorem b_tail : FieldEmbedding.BoundedBy 97 op2ParentTail := by
  simp [op2ParentTail, op2ChildFormula1, op2ChildFormula2, op2Sf1, op2Sf2, op1Head, op2Result,
    FieldEmbedding.BoundedBy]
private theorem b_c1 : FieldEmbedding.BoundedBy 97 op2ChildFormula1 := by
  simp [op2ChildFormula1, op2Sf1, op1Head, FieldEmbedding.BoundedBy]
private theorem b_c2 : FieldEmbedding.BoundedBy 97 op2ChildFormula2 := by
  simp [op2ChildFormula2, op2Sf2, op1Head, op2Result, FieldEmbedding.BoundedBy]
private theorem b_sf1 : FieldEmbedding.BoundedBy 97 op2Sf1 := by
  simp [op2Sf1, FieldEmbedding.BoundedBy]
private theorem b_sf2 : FieldEmbedding.BoundedBy 97 op2Sf2 := by
  simp [op2Sf2, op1Head, op2Result, FieldEmbedding.BoundedBy]
private theorem b_head2 : FieldEmbedding.BoundedBy 97 op2Head := by
  simp [op2Head, FieldEmbedding.BoundedBy]
private theorem b_head1 : FieldEmbedding.BoundedBy 97 op1Head := by
  simp [op1Head, FieldEmbedding.BoundedBy]
private theorem b_res : FieldEmbedding.BoundedBy 97 op2Result := by
  simp [op2Result, FieldEmbedding.BoundedBy]

theorem skeletonBounded : semanticSkeleton.BoundedBy 97 := by
  refine { computeRows := ?_, memoryRows := ?_, memoryTrees := ?_ }
  · rw [computeRows_eq]
    exact ⟨parentRow_bounded, child1Row_bounded, child2Row_bounded, child3Row_bounded⟩
  · rw [memoryRows_eq]
    exact ⟨readRow_bounded b_formula recF_bounded, decRow_bounded b_formula b_head2 b_tail,
      haltRow_bounded (by norm_num), verifyRow_bounded b_tail recF_bounded,
      readRow_bounded b_tail recT_bounded, decRow_bounded b_tail b_c1 b_c2,
      verifyRow_bounded b_c1 recT_bounded, readRow_bounded b_c2 recC_bounded,
      readRow_bounded b_c1 recB_bounded, decRow_bounded b_c2 b_head1 b_sf2,
      decRow_bounded b_c1 b_head1 b_sf1, haltRow_bounded (by norm_num),
      verifyRow_bounded b_sf2 recC_bounded, haltRow_bounded (by norm_num),
      verifyRow_bounded b_sf1 recB_bounded, readRow_bounded b_sf2 recS_bounded,
      decRow_bounded b_sf1 (atom_bounded (by norm_num)) (atom_bounded (by norm_num)),
      decRow_bounded b_sf2 b_head1 b_res, haltRow_bounded (by norm_num),
      haltRow_bounded (by norm_num), haltRow_bounded (by norm_num),
      verifyRow_bounded b_res recS_bounded, haltRow_bounded (by norm_num)⟩
  · intro tree htree node hnode
    simp only [semanticSkeleton, List.mem_singleton] at htree
    subst tree
    have hm : node ∈ bfsForest [readFTree] :=
      (mem_bfsForest [readFTree] node).2 ⟨readFTree, by simp, hnode⟩
    simp [readFTree, tDecF, tHalt2, tVerifyF, tReadT, tDecT, tVerifyT, tReadC, tReadB,
      tDecC, tDecB, tHaltC1, tVerifyC, tHaltB1, tVerifyB, tReadS, tDecSf1, tDecS, tHalt0,
      tHalt1s, tHaltS1, tVerifyS, tHalt5, mLeaf, mOne, mTwo, bfsForest] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact readRow_bounded b_formula recF_bounded
    · exact decRow_bounded b_formula b_head2 b_tail
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
    · exact readRow_bounded b_sf2 recS_bounded
    · exact decRow_bounded b_sf1 (atom_bounded (by norm_num)) (atom_bounded (by norm_num))
    · exact decRow_bounded b_sf2 b_head1 b_res
    · exact haltRow_bounded (by norm_num)
    · exact haltRow_bounded (by norm_num)
    · exact haltRow_bounded (by norm_num)
    · exact verifyRow_bounded b_res recS_bounded
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
    parentRow, child1Row, child2Row, child3Row, op1Row, op2Subject, op2ParentFormula,
    op2ParentTail, op2ChildFormula1, op2ChildFormula2, op2Sf1, op2Sf2, op2Head, op1Head,
    op2Result, recF, recT, recB, recC, recS, decActive, ComputeTable.fanoutComp,
    NTree.childOpt, NTree.label, bfsForest, NTree.size, totalSize, List.flatMap_cons,
    List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil, List.cons_append,
    List.nil_append, List.ofFn_succ, List.ofFn_zero, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.getElem?_nil, Option.map_some, Option.map_none] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [FieldEmbedding.BoundedBy, hasTailDecomposition, decActive, ComputeTable.fanoutComp,
      op2Subject, op2ParentFormula, op2ParentTail, op2ChildFormula1, op2ChildFormula2,
      op2Sf1, op2Sf2, op2Head, op1Head, op2Result]

def census : EdgeComparisonCensus.CombinedSkeletonCensus K semanticSkeleton 7 where
  p8 :=
    { leaves_bounded := by
        intro pair hp
        simp [BoundSemanticTrace.skeletonPairs, P8Census.skeletonComparisonCensus,
          P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
          P8Census.skeletonSubformula, SemanticStrategy.SemanticSkeleton.publicClaim,
          SemanticTrace.ComparisonUse.pair, semanticSkeleton, computeTree, computeSkeletonRows,
          parentRow, child1Row, child2Row, child3Row, op1Row, op2Subject, op2ParentFormula,
          op2ParentTail, op2ChildFormula1, op2ChildFormula2, op2Sf1, op2Sf2, op2Head, op1Head,
          op2Result, decActive, ComputeTable.fanoutComp, NTree.label, bfsForest, NTree.size,
          totalSize, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
          List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [hasTailDecomposition, decActive, ComputeTable.fanoutComp, op2Subject,
            op2ParentFormula, op2ParentTail, op2ChildFormula1, op2ChildFormula2, op2Sf1,
            op2Sf2, op2Head, op1Head, op2Result, Noun.leaves] }
  edges :=
    { leaves_bounded := by
        intro pair hp
        simp [EdgeComparisonCensus.edgePairs, EdgeComparisonCensus.rowEdgePairs,
          EdgeComparisonCensus.edgeTriple, P8Census.skeletonSubformula, semanticSkeleton,
          computeTree, parentRow, child1Row, child2Row, child3Row, op1Row, op2Subject,
          op2ChildFormula1, op2ChildFormula2, op2Sf1, op2Sf2, op2Head, op1Head, op2Result,
          ComputeTable.fanoutComp, NTree.childOpt, NTree.label, bfsForest, NTree.size,
          totalSize, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
          List.append_nil, List.cons_append, List.nil_append, List.ofFn_succ, List.ofFn_zero,
          List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
          List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
          Option.map_some, Option.map_none] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [hasTailDecomposition, decActive, ComputeTable.fanoutComp, op2Subject,
            op2ParentFormula, op2ParentTail, op2ChildFormula1, op2ChildFormula2, op2Sf1,
            op2Sf2, op2Head, op1Head, op2Result, Noun.leaves] }

end Nock.NockVMROM.Thm54.TraceGen.Op2Skeleton

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2Skeleton.slotSemantics
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2Skeleton.recordEquations
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2Skeleton.sizeWindowBound
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2Skeleton.skeletonBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2Skeleton.combinedBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2Skeleton.census
