/-
  Nock/NockVMROM/Thm54/TraceGen/Op9SkeletonK3.lean

  Field-free semantic skeleton of the fan-out-2 invoke program

      `*[0 [9 [2 [1 [[1 7] [1 9]]]]]] = 7`

  plus the six seed-free census-closure obligations an honest `HonestCommitment.Data` over
  that skeleton must discharge.  The `.s9` root has fan-out 2 and three live records
  (formula@3, formula-tail@2, arm-fetch@2); each `.s1` child has one record (formula@3).
  The memory forest is the TWO-ROOT reconstruction: root A (19 rows) for the formula
  records, root B (11 rows) for the arm-fetch records rooted at the computed core.  Leaf
  window `Λ = 7` (the parent formula has seven atoms).  Census/`combinedBounded` are
  stated over the table field `K3`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op9Gen
import Nock.NockVMROM.Thm54.TraceGen.CubicField97
import Nock.NockVMROM.Thm54.EdgeComparisonCensus
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.ServedLookupBridge
import Mathlib.Tactic.NormNum.Prime

namespace Nock.NockVMROM.Thm54.TraceGen.Op9Skeleton

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open SemanticStrategy ServedLookupBridge
open Nock.NockVMROM.Thm54.TraceGen

set_option linter.unusedSimpArgs false

def op1Head : Noun := .atom 1
def op9Head : Noun := .atom 9

instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

abbrev F : Type := ZMod 97
abbrev K : Type := CubicField97.K3

/-! ## Committed records (nouns + Nat axes, no timestamps) -/

def recF : MemRecSkeleton where
  root := op9ParentFormula
  child := op9ParentTail
  axis := 3
def recT : MemRecSkeleton where
  root := op9ParentTail
  child := op9AxisAtom
  axis := 2
def recArm : MemRecSkeleton where
  root := op9CoreNoun
  child := op9Arm
  axis := 2
def recCoreF : MemRecSkeleton where
  root := op9CoreFormula
  child := op9CoreNoun
  axis := 3
def recArmF : MemRecSkeleton where
  root := op9Arm
  child := op9Result
  axis := 3

/-! ## Compute rows (`.s9` root + two `OP_1` children) -/

def parentRow : ComputeRowSkeleton where
  state := .s9
  subject := op9Subject
  formula := op9ParentFormula
  evaluation := op9Result
  decomposition := fun slot _ =>
    match slot with
    | .f_h => op9Head
    | .f_t => op9ParentTail
    | .f_th => op9AxisAtom
    | .f_tt => op9CoreFormula
    | _ => .atom 0
  subformula := fun i _ slot =>
    match (i : ℕ), slot with
    | 0, .subject => op9Subject
    | 0, .formula => op9CoreFormula
    | 0, .result => op9CoreNoun
    | 1, .subject => op9CoreNoun
    | 1, .formula => op9Arm
    | 1, .result => op9Result
    | _, _ => .atom 0
  memoryRecord := fun i _ =>
    match (i : ℕ) with
    | 0 => recF
    | 1 => recT
    | _ => recArm

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

def child1Row : ComputeRowSkeleton := op1Row op9Subject op9CoreFormula op9CoreNoun recCoreF
def child2Row : ComputeRowSkeleton := op1Row op9CoreNoun op9Arm op9Result recArmF

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

/-! ### Root A — formula tree (19 nodes: 3 read, 3 verify, 6 decompose, 7 halt) -/

def skReadF : MemoryRowSkeleton := readRow op9ParentFormula recF
def skDecPF : MemoryRowSkeleton := decRow op9ParentFormula op9Head op9ParentTail
def skHalt9 : MemoryRowSkeleton := haltRow 9
def skVerifyF : MemoryRowSkeleton := verifyRow op9ParentTail recF
def skReadT : MemoryRowSkeleton := readRow op9ParentTail recT
def skDecPT : MemoryRowSkeleton := decRow op9ParentTail op9AxisAtom op9CoreFormula
def skVerifyT : MemoryRowSkeleton := verifyRow op9AxisAtom recT
def skHaltA2 : MemoryRowSkeleton := haltRow 2
def skReadCoreF : MemoryRowSkeleton := readRow op9CoreFormula recCoreF
def skDecCF : MemoryRowSkeleton := decRow op9CoreFormula op1Head op9CoreNoun
def skHaltH1a : MemoryRowSkeleton := haltRow 1
def skVerifyCoreF : MemoryRowSkeleton := verifyRow op9CoreNoun recCoreF
def skDecCN : MemoryRowSkeleton := decRow op9CoreNoun op9Arm op9CoreTail
def skDecArmA : MemoryRowSkeleton := decRow op9Arm op1Head op9Result
def skHaltH1b : MemoryRowSkeleton := haltRow 1
def skHaltA7 : MemoryRowSkeleton := haltRow 7
def skDecCTA : MemoryRowSkeleton := decRow op9CoreTail op1Head op9Head
def skHaltH1c : MemoryRowSkeleton := haltRow 1
def skHaltA9 : MemoryRowSkeleton := haltRow 9

/-! ### Root B — core tree (11 nodes: 2 read, 2 verify, 3 decompose, 4 halt) -/

def skReadArm : MemoryRowSkeleton := readRow op9CoreNoun recArm
def skDecCN_B : MemoryRowSkeleton := decRow op9CoreNoun op9Arm op9CoreTail
def skVerifyArm : MemoryRowSkeleton := verifyRow op9Arm recArm
def skReadArmF : MemoryRowSkeleton := readRow op9Arm recArmF
def skDecArmB : MemoryRowSkeleton := decRow op9Arm op1Head op9Result
def skHaltH1_B1 : MemoryRowSkeleton := haltRow 1
def skVerifyArmF : MemoryRowSkeleton := verifyRow op9Result recArmF
def skHaltA7_B : MemoryRowSkeleton := haltRow 7
def skDecCT_B : MemoryRowSkeleton := decRow op9CoreTail op1Head op9Head
def skHaltH1_B2 : MemoryRowSkeleton := haltRow 1
def skHaltA9_B : MemoryRowSkeleton := haltRow 9

/-! ### Memory forest assembly -/

def mLeaf (r : MemoryRowSkeleton) : NTree MemoryRowSkeleton := .node r []
def mOne (r : MemoryRowSkeleton) (c : NTree MemoryRowSkeleton) : NTree MemoryRowSkeleton :=
  .node r [c]
def mTwo (r : MemoryRowSkeleton) (l s : NTree MemoryRowSkeleton) : NTree MemoryRowSkeleton :=
  .node r [l, s]

def rootATree : NTree MemoryRowSkeleton :=
  mOne skReadF
    (mTwo skDecPF
      (mLeaf skHalt9)
      (mOne skVerifyF
        (mOne skReadT
          (mTwo skDecPT
            (mOne skVerifyT (mLeaf skHaltA2))
            (mOne skReadCoreF
              (mTwo skDecCF
                (mLeaf skHaltH1a)
                (mOne skVerifyCoreF
                  (mTwo skDecCN
                    (mTwo skDecArmA (mLeaf skHaltH1b) (mLeaf skHaltA7))
                    (mTwo skDecCTA (mLeaf skHaltH1c) (mLeaf skHaltA9))))))))))

def rootBTree : NTree MemoryRowSkeleton :=
  mOne skReadArm
    (mTwo skDecCN_B
      (mOne skVerifyArm
        (mOne skReadArmF
          (mTwo skDecArmB
            (mLeaf skHaltH1_B1)
            (mOne skVerifyArmF (mLeaf skHaltA7_B)))))
      (mTwo skDecCT_B
        (mLeaf skHaltH1_B2)
        (mLeaf skHaltA9_B)))

def semanticSkeleton : SemanticSkeleton where
  computeTree := computeTree
  memoryForest := [rootATree, rootBTree]

theorem computeRows_eq :
    computeSkeletonRows semanticSkeleton = [parentRow, child1Row, child2Row] := by
  norm_num [computeSkeletonRows, semanticSkeleton, computeTree, bfsForest,
    NTree.size, totalSize]

theorem memoryRows_eq :
    (memorySkeletonRows semanticSkeleton).length = 30 := by
  norm_num [memorySkeletonRows, semanticSkeleton, rootATree, rootBTree,
    mLeaf, mOne, mTwo, bfsForest, NTree.size, totalSize]

/-! ## The six seed-free census-closure obligations -/

theorem slotSemantics :
    ∀ s ∈ computeSkeletonRows semanticSkeleton, SkeletonSlotSemantics s := by
  intro s hs
  rw [computeRows_eq] at hs
  fin_cases hs <;>
    exact
      { s0_slot := fun h => absurd h (by simp [parentRow, child1Row, child2Row, op1Row])
        s9_slot := fun h => by
          simp only [parentRow, child1Row, child2Row, op1Row,
            P8Census.skeletonMemoryAxis, P8Census.skeletonSubformula,
            ComputeTable.fanoutComp, Nock.Framework.recordCount] at h ⊢
          first
          | exact op9_slot
          | exact absurd h (by decide) }

theorem recordEquations :
    ∀ s ∈ computeSkeletonRows semanticSkeleton, SkeletonRecordEquations s := by
  intro s hs
  rw [computeRows_eq] at hs
  fin_cases hs <;>
    exact
      { s0_record := fun h => absurd h (by simp [parentRow, child1Row, child2Row, op1Row])
        s9_record := fun h => by
          simp only [parentRow, child1Row, child2Row, op1Row,
            P8Census.skeletonSubformula, ComputeTable.fanoutComp,
            Nock.Framework.recordCount] at h ⊢
          exact ⟨rfl, rfl⟩ }

theorem sizeWindowBound :
    SizeWindowCounting.SizeWindowNounsBoundedBy semanticSkeleton 7 := by
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
  simp [recF, MemRecSkeleton.BoundedBy, op9ParentFormula, op9ParentTail, op9AxisAtom,
    op9CoreFormula, op9CoreNoun, op9Arm, op9Result, op9Head, op1Head,
    FieldEmbedding.BoundedBy]
theorem recT_bounded : recT.BoundedBy 97 := by
  simp [recT, MemRecSkeleton.BoundedBy, op9ParentTail, op9AxisAtom, op9CoreFormula,
    op9CoreNoun, op9Arm, op9Result, op1Head, FieldEmbedding.BoundedBy]
theorem recArm_bounded : recArm.BoundedBy 97 := by
  simp [recArm, MemRecSkeleton.BoundedBy, op9CoreNoun, op9Arm, FieldEmbedding.BoundedBy]
theorem recCoreF_bounded : recCoreF.BoundedBy 97 := by
  simp [recCoreF, MemRecSkeleton.BoundedBy, op9CoreFormula, op9CoreNoun, op9Arm,
    FieldEmbedding.BoundedBy]
theorem recArmF_bounded : recArmF.BoundedBy 97 := by
  simp [recArmF, MemRecSkeleton.BoundedBy, op9Arm, op9Result, FieldEmbedding.BoundedBy]

theorem parentRow_bounded : parentRow.BoundedBy 97 := by
  refine ⟨by simp [parentRow, op9Subject, FieldEmbedding.BoundedBy],
    by simp [parentRow, op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula,
      op9CoreNoun, op9Arm, op9Result, op9Head, op1Head, FieldEmbedding.BoundedBy],
    by simp [parentRow, op9Result, FieldEmbedding.BoundedBy], ?_, ?_, ?_⟩
  · intro slot h
    cases slot <;>
      simp [parentRow, op9Head, op9ParentTail, op9AxisAtom, op9CoreFormula, op9CoreNoun,
        op9Arm, op9Result, op1Head, FieldEmbedding.BoundedBy]
  · intro i h slot
    fin_cases i <;> cases slot <;>
      simp [parentRow, op9Subject, op9CoreFormula, op9CoreNoun, op9Arm, op9Result,
        op1Head, FieldEmbedding.BoundedBy]
  · intro i h
    simp only [parentRow]
    match i with
    | ⟨0, _⟩ => exact recF_bounded
    | ⟨1, _⟩ => exact recT_bounded
    | ⟨2, _⟩ => exact recArm_bounded

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
  op1Row_bounded (by simp [op9Subject, FieldEmbedding.BoundedBy])
    (by simp [op9CoreFormula, op9CoreNoun, op9Arm, op1Head, FieldEmbedding.BoundedBy])
    (by simp [op9CoreNoun, op9Arm, FieldEmbedding.BoundedBy]) recCoreF_bounded
theorem child2Row_bounded : child2Row.BoundedBy 97 :=
  op1Row_bounded (by simp [op9CoreNoun, op9Arm, FieldEmbedding.BoundedBy])
    (by simp [op9Arm, op9Result, op1Head, FieldEmbedding.BoundedBy])
    (by simp [op9Result, FieldEmbedding.BoundedBy]) recArmF_bounded

private theorem b_formula : FieldEmbedding.BoundedBy 97 op9ParentFormula := by
  simp [op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula, op9CoreNoun, op9Arm,
    op9Result, op9Head, op1Head, FieldEmbedding.BoundedBy]
private theorem b_tail : FieldEmbedding.BoundedBy 97 op9ParentTail := by
  simp [op9ParentTail, op9AxisAtom, op9CoreFormula, op9CoreNoun, op9Arm, op9Result, op1Head,
    FieldEmbedding.BoundedBy]
private theorem b_axisAtom : FieldEmbedding.BoundedBy 97 op9AxisAtom := by
  simp [op9AxisAtom, FieldEmbedding.BoundedBy]
private theorem b_coreFormula : FieldEmbedding.BoundedBy 97 op9CoreFormula := by
  simp [op9CoreFormula, op9CoreNoun, op9Arm, FieldEmbedding.BoundedBy]
private theorem b_coreNoun : FieldEmbedding.BoundedBy 97 op9CoreNoun := by
  simp [op9CoreNoun, op9Arm, FieldEmbedding.BoundedBy]
private theorem b_arm : FieldEmbedding.BoundedBy 97 op9Arm := by
  simp [op9Arm, FieldEmbedding.BoundedBy]
private theorem b_coreTail : FieldEmbedding.BoundedBy 97 op9CoreTail := by
  simp [op9CoreTail, FieldEmbedding.BoundedBy]
private theorem b_result : FieldEmbedding.BoundedBy 97 op9Result := by
  simp [op9Result, FieldEmbedding.BoundedBy]
private theorem b_head9 : FieldEmbedding.BoundedBy 97 op9Head := by
  simp [op9Head, FieldEmbedding.BoundedBy]
private theorem b_head1 : FieldEmbedding.BoundedBy 97 op1Head := by
  simp [op1Head, FieldEmbedding.BoundedBy]

theorem skeletonBounded : semanticSkeleton.BoundedBy 97 := by
  refine { computeRows := ?_, memoryRows := ?_, memoryTrees := ?_ }
  · rw [computeRows_eq]
    exact ⟨parentRow_bounded, child1Row_bounded, child2Row_bounded⟩
  · rw [List.forall_iff_forall_mem]
    intro s hs
    simp [memorySkeletonRows, semanticSkeleton, rootATree, rootBTree,
      mLeaf, mOne, mTwo, bfsForest, NTree.size, totalSize] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact readRow_bounded b_formula recF_bounded
      | exact readRow_bounded b_coreNoun recArm_bounded
      | exact readRow_bounded b_arm recArmF_bounded
      | exact readRow_bounded b_tail recT_bounded
      | exact readRow_bounded b_coreFormula recCoreF_bounded
      | exact decRow_bounded b_formula b_head9 b_tail
      | exact decRow_bounded b_coreNoun b_arm b_coreTail
      | exact decRow_bounded b_tail b_axisAtom b_coreFormula
      | exact decRow_bounded b_coreFormula b_head1 b_coreNoun
      | exact decRow_bounded b_arm b_head1 b_result
      | exact decRow_bounded b_coreTail b_head1 b_head9
      | exact verifyRow_bounded b_tail recF_bounded
      | exact verifyRow_bounded b_axisAtom recT_bounded
      | exact verifyRow_bounded b_coreNoun recCoreF_bounded
      | exact verifyRow_bounded b_arm recArm_bounded
      | exact verifyRow_bounded b_result recArmF_bounded
      | exact haltRow_bounded (by norm_num)
  · intro tree htree node hnode
    have hm : node ∈ bfsForest semanticSkeleton.memoryForest :=
      (mem_bfsForest semanticSkeleton.memoryForest node).2 ⟨tree, htree, hnode⟩
    simp [semanticSkeleton, rootATree, rootBTree,
      mLeaf, mOne, mTwo, bfsForest, NTree.size, totalSize] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact readRow_bounded b_formula recF_bounded
      | exact readRow_bounded b_coreNoun recArm_bounded
      | exact readRow_bounded b_arm recArmF_bounded
      | exact readRow_bounded b_tail recT_bounded
      | exact readRow_bounded b_coreFormula recCoreF_bounded
      | exact decRow_bounded b_formula b_head9 b_tail
      | exact decRow_bounded b_coreNoun b_arm b_coreTail
      | exact decRow_bounded b_tail b_axisAtom b_coreFormula
      | exact decRow_bounded b_coreFormula b_head1 b_coreNoun
      | exact decRow_bounded b_arm b_head1 b_result
      | exact decRow_bounded b_coreTail b_head1 b_head9
      | exact verifyRow_bounded b_tail recF_bounded
      | exact verifyRow_bounded b_axisAtom recT_bounded
      | exact verifyRow_bounded b_coreNoun recCoreF_bounded
      | exact verifyRow_bounded b_arm recArm_bounded
      | exact verifyRow_bounded b_result recArmF_bounded
      | exact haltRow_bounded (by norm_num)

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
    parentRow, child1Row, child2Row, op1Row, op9Subject, op9ParentFormula,
    op9ParentTail, op9AxisAtom, op9CoreFormula, op9CoreNoun, op9Arm, op9Result,
    op9Head, op1Head,
    recF, recT, recArm, recCoreF, recArmF, decActive, ComputeTable.fanoutComp,
    NTree.childOpt, NTree.label, bfsForest, NTree.size, totalSize, List.flatMap_cons,
    List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil, List.cons_append,
    List.nil_append, List.ofFn_succ, List.ofFn_zero, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.getElem?_nil, Option.map_some, Option.map_none] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) [FieldEmbedding.BoundedBy, hasTailDecomposition,
      decActive, ComputeTable.fanoutComp,
      op9Subject, op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula, op9CoreNoun,
      op9Arm, op9Result, op9Head, op1Head, Noun.tis]

def census : EdgeComparisonCensus.CombinedSkeletonCensus K semanticSkeleton 7 where
  p8 :=
    { leaves_bounded := by
        intro pair hp
        simp [BoundSemanticTrace.skeletonPairs, P8Census.skeletonComparisonCensus,
          P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
          P8Census.skeletonSubformula, SemanticStrategy.SemanticSkeleton.publicClaim,
          SemanticTrace.ComparisonUse.pair, semanticSkeleton, computeTree, computeSkeletonRows,
          parentRow, child1Row, child2Row, op1Row, op9Subject, op9ParentFormula,
          op9ParentTail, op9AxisAtom, op9CoreFormula, op9CoreNoun, op9Arm, op9Result,
          op9Head, op1Head,
          decActive, ComputeTable.fanoutComp, NTree.label, bfsForest, NTree.size,
          totalSize, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
          List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [hasTailDecomposition, decActive, ComputeTable.fanoutComp, op9Subject,
            op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula, op9CoreNoun,
            op9Arm, op9Result, op9Head, op1Head, Noun.tis, Noun.leaves] }
  edges :=
    { leaves_bounded := by
        intro pair hp
        simp [EdgeComparisonCensus.edgePairs, EdgeComparisonCensus.rowEdgePairs,
          EdgeComparisonCensus.edgeTriple, P8Census.skeletonSubformula, semanticSkeleton,
          computeTree, parentRow, child1Row, child2Row, op1Row, op9Subject,
          op9CoreFormula, op9CoreNoun, op9Arm, op9Result, op9Head, op1Head,
          ComputeTable.fanoutComp, NTree.childOpt, NTree.label, bfsForest, NTree.size,
          totalSize, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
          List.append_nil, List.cons_append, List.nil_append, List.ofFn_succ, List.ofFn_zero,
          List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
          List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
          Option.map_some, Option.map_none] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [hasTailDecomposition, decActive, ComputeTable.fanoutComp, op9Subject,
            op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula, op9CoreNoun,
            op9Arm, op9Result, op9Head, op1Head, Noun.tis, Noun.leaves] }

end Nock.NockVMROM.Thm54.TraceGen.Op9Skeleton

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9Skeleton.slotSemantics
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9Skeleton.recordEquations
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9Skeleton.sizeWindowBound
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9Skeleton.skeletonBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9Skeleton.combinedBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9Skeleton.census
