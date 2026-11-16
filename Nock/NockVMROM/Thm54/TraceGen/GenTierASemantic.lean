/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierASemantic.lean

  Semantic IO preimage and chained language for the threaded F769
  carrier `execThreaded`.  Thirteen live NMR records (exponents 1..13)
  bridge to the BFS-derived request list; memory responses are the same
  records in forest-BFS order: the ten tree roots, then the three inner
  chained reads.

  -- the paper
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMemAccept
import Nock.NockVMROM.Thm54.TraceGen.GenTierANodup
import Nock.NockVMROM.Thm54.Language
import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.NockVMROM.Thm54.RecordBridge
import Mathlib.Tactic.IntervalCases

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun Nock.NockVM
open Nock.MemoryTable
open Nock.ComputeTable (MemRec State)
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy

variable {K : Type} [Field K]

-- Form R `λ` (generic lemmas; 28th λ-fix).
variable {lmb : K}

theorem gMemRow9_pub (sk : MemoryRowSkeleton) (e : ℕ) (z : K) (pub : Pub K) :
    (gMemRow9 sk e z pub).row.2.2 = pub :=
  rfl

theorem gMemRow9_mem (sk : MemoryRowSkeleton) (e : ℕ) (z : K) (pub : Pub K) :
    (gMemRow9 sk e z pub).row.2.2.mem = pub.mem :=
  rfl

theorem gMemRow9_st (sk : MemoryRowSkeleton) (e : ℕ) (z : K) (pub : Pub K) :
    (gMemRow9 sk e z pub).row.2.2.st = pub.st :=
  rfl

theorem responseRecords_setAcc (p : Pub K) (a b : K) :
    responseRecords (setAcc p a b) = responseRecords p := by
  simp [responseRecords, setAcc]
  rfl

theorem setGenAcc_mem (g : GenMemoryRow K) (a b : K) :
    (setGenAcc g a b).row.2.2.mem = g.row.2.2.mem :=
  rfl

theorem threadGenRow_pub_mem (inp : MemoryTable.Inputs K) (acc : K) (g : GenMemoryRow K) :
    (threadGenRow inp acc g).2.row.2.2.mem = g.row.2.2.mem := by
  rw [threadGenRow_snd, setGenAcc_mem]

theorem threadGenRow_responseRecords (inp : MemoryTable.Inputs K) (acc : K) (g : GenMemoryRow K) :
    responseRecords (threadGenRow inp acc g).2.row.2.2 =
      responseRecords g.row.2.2 := by
  rw [threadGenRow_snd]
  exact responseRecords_setAcc g.row.2.2 acc _

theorem threadGenRows_flatMap_responseRecords (inp : MemoryTable.Inputs K) :
    ∀ acc gs,
      (threadGenRows inp acc gs).flatMap
          (fun g : GenMemoryRow K => responseRecords g.row.2.2) =
        gs.flatMap (fun g => responseRecords g.row.2.2)
  | _, [] => rfl
  | acc, g :: gs => by
      simp [threadGenRows, threadGenRow_responseRecords]
      exact threadGenRows_flatMap_responseRecords inp
        (threadGenRow inp acc g).1 gs

theorem threadGenRows_map_mem (inp : MemoryTable.Inputs K) :
    ∀ acc gs,
      (threadGenRows inp acc gs).map (fun g : GenMemoryRow K => g.row.2.2.mem) =
        gs.map (fun g => g.row.2.2.mem)
  | _, [] => rfl
  | acc, g :: gs => by
      simp [threadGenRows, threadGenRow_pub_mem]
      exact threadGenRows_map_mem inp (threadGenRow inp acc g).1 gs

/-- BFS-order served `read_root` memories of a generated forest. -/
def servedGen (forest : List (NTree (GenMemoryRow K))) : List (MemRec K) :=
  (bfsForest forest).flatMap (fun t => responseRecords t.label.row.2.2)

theorem servedGen_eq_labels (forest : List (NTree (GenMemoryRow K))) :
    servedGen forest =
      ((bfsForest forest).map NTree.label).flatMap
        (fun g : GenMemoryRow K => responseRecords g.row.2.2) := by
  simp [servedGen, List.flatMap_map]

theorem servedGen_of_ne_nil (l : List (NTree (GenMemoryRow K))) (hl : l ≠ []) :
    servedGen l =
      l.flatMap (fun t => responseRecords t.label.row.2.2) ++
        servedGen (l.flatMap NTree.children) := by
  unfold servedGen
  rw [bfsForest_cons_eq l hl, List.flatMap_append]

theorem genAnnotatedNounWalk_st (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n, (genAnnotatedNounWalk E z lmb n).1.label.row.2.2.st = nounWalkRootState n
  | .atom a => rfl
  | .cell h t => rfl

theorem genAnnotatedNounWalk_not_read (E : Noun → ComputeTable.FP K) (z : K)
    (n : Noun) :
    (genAnnotatedNounWalk E z lmb n).1.label.row.2.2.st ≠ .read_root := by
  rw [genAnnotatedNounWalk_st]
  cases n <;> simp [nounWalkRootState]

theorem annotatedReadPub_mem (E : Noun → ComputeTable.FP K)
    (root child : Noun) (ax : ℕ) (ts : K) (lcCell : Cell K) (ipre icur lmb : K) :
    (annotatedReadPub E root child ax ts lcCell ipre icur lmb).mem =
      ⟨E root, E child, (ax : K), ts⟩ :=
  rfl

theorem annotatedReadPub_ver (E : Noun → ComputeTable.FP K)
    (root child : Noun) (ax : ℕ) (ts : K) (lcCell : Cell K) (ipre icur lmb : K) :
    (annotatedReadPub E root child ax ts lcCell ipre icur lmb).ver = true :=
  rfl

theorem annotatedDecPub_ver (E : Noun → ComputeTable.FP K) (parent hd tl : Noun)
    (lcCell rcCell : Cell K) (lcSt rcSt : MState) (ipre icur : K) :
    (annotatedDecPub E parent hd tl lcCell rcCell lcSt rcSt ipre icur lmb).ver = false :=
  rfl

theorem annotatedVerifyPub_ver (E : Noun → ComputeTable.FP K)
    (root child : Noun) (ax : ℕ) (ts : K) (lcCell : Cell K) (ipre icur : K) :
    (annotatedVerifyPub E root child ax ts lcCell ipre icur lmb).ver = false :=
  rfl

theorem gMemRow9_ver (sk : MemoryRowSkeleton) (e : ℕ) (z : K) (pub : Pub K) :
    (gMemRow9 sk e z pub).row.2.2.ver = pub.ver :=
  rfl

theorem row_s6 :
    (bfsLabelAt (dotTree (K := K)) 1).skel.state = State.s6 := by
  rw [bfsLabelAt_dot_skel1]; rfl

theorem row_s1_2 :
    (bfsLabelAt (dotTree (K := K)) 2).skel.state = State.s1 := by
  rw [bfsLabelAt_dot_skel2]; rfl

theorem row_s2 :
    (bfsLabelAt (dotTree (K := K)) 3).skel.state = State.s2 := by
  rw [bfsLabelAt_dot_skel3]; rfl

theorem row_s1_4 :
    (bfsLabelAt (dotTree (K := K)) 4).skel.state = State.s1 := by
  rw [bfsLabelAt_dot_skel4]; rfl

theorem row_s1_5 :
    (bfsLabelAt (dotTree (K := K)) 5).skel.state = State.s1 := by
  rw [bfsLabelAt_dot_skel5]; rfl

theorem row_s9 :
    (bfsLabelAt (dotTree (K := K)) 6).skel.state = State.s9 := by
  rw [bfsLabelAt_dot_skel6]; rfl

theorem row_s1_7 :
    (bfsLabelAt (dotTree (K := K)) 7).skel.state = State.s1 := by
  rw [bfsLabelAt_dot_skel7]; rfl

theorem row_s1_8 :
    (bfsLabelAt (dotTree (K := K)) 8).skel.state = State.s1 := by
  rw [bfsLabelAt_dot_skel8]; rfl

theorem formulaTail_dotFormula : formulaTail dotFormula = dotParentTail := rfl
theorem formulaHead_dotParentTail : formulaHead dotParentTail = dotCondFormula := rfl
theorem formulaTail_dotParentTail : formulaTail dotParentTail = dotBranchPair := rfl
theorem formulaHead_dotBranchPair : formulaHead dotBranchPair = dotThenFormula := rfl
theorem formulaTail_dotThenFormula : formulaTail dotThenFormula = dotThenTail := rfl
theorem formulaHead_dotThenTail : formulaHead dotThenTail = dotOp2B := rfl
theorem formulaTail_dotOp9Formula : formulaTail dotOp9Formula = dotOp9Tail := rfl
theorem formulaHead_dotOp9Tail : formulaHead dotOp9Tail = .atom 2 := rfl

theorem rendered_row1_recs (z α : K) :
    activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTree (K := K)) 1)).row.2.2.1 =
      [⟨encC z dotFormula, encC z dotParentTail, 3, α ^ 1⟩,
       ⟨encC z dotParentTail, encC z dotCondFormula, 2, α ^ 2⟩,
       ⟨encC z dotBranchPair, encC z dotThenFormula, 2, α ^ 3⟩] := by
  rw [renderNode_op6_row z α _ row_s6, bfsLabelAt_dot_skel1]
  simp only [activeRequestRecords, renderOp6Row, recExp_eq_getRecordExp,
    liveRecordExps_named, pow_one, dotOp6Skel, genSkelOp6]
  rw [formulaTail_dotFormula, formulaHead_dotParentTail, formulaTail_dotParentTail,
    formulaHead_dotBranchPair]
  have h := liveRecordExps_named (K := K)
  simp [h, pow_one]

theorem rendered_row2_recs (z α : K) :
    activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTree (K := K)) 2)).row.2.2.1 =
      [⟨encC z dotCondFormula, encC z dotCondResult, 3, α ^ 4⟩] := by
  rw [renderNode_op1_row z α _ row_s1_2, bfsLabelAt_dot_skel2]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_named, pow_one, dotCondTree, skelNode, genSkelOp1]

theorem rendered_row3_recs (z α : K) :
    activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTree (K := K)) 3)).row.2.2.1 =
      [⟨encC z dotThenFormula, encC z dotThenTail, 3, α ^ 5⟩,
       ⟨encC z dotThenTail, encC z dotOp2B, 2, α ^ 6⟩] := by
  rw [renderNode_op2_row z α _ row_s2, bfsLabelAt_dot_skel3]
  simp only [activeRequestRecords, renderOp2Row, recExp_eq_getRecordExp,
    liveRecordExps_named, pow_one, dotOp2Skel, genSkelOp2]
  rw [formulaTail_dotThenFormula, formulaHead_dotThenTail]
  have h := liveRecordExps_named (K := K)
  simp [h]

theorem rendered_row4_recs (z α : K) :
    activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTree (K := K)) 4)).row.2.2.1 =
      [⟨encC z dotOp2B, encC z dotOp2Sf1, 3, α ^ 7⟩] := by
  rw [renderNode_op1_row z α _ row_s1_4, bfsLabelAt_dot_skel4]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_named, pow_one, dotOp1BTree, skelNode, genSkelOp1]

theorem rendered_row5_recs (z α : K) :
    activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTree (K := K)) 5)).row.2.2.1 =
      [⟨encC z dotOp2C, encC z dotOp2Sf2, 3, α ^ 8⟩] := by
  rw [renderNode_op1_row z α _ row_s1_5, bfsLabelAt_dot_skel5]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_named, pow_one, dotOp1CTree, skelNode, genSkelOp1]

theorem skeletonSubformula_dotOp9_core :
    P8Census.skeletonSubformula dotOp9Skel 0 .result = dotCore := by
  simp [P8Census.skeletonSubformula, dotOp9Skel, genSkelOp9, ComputeTable.fanoutComp]

theorem skeletonSubformula_dotOp9_arm :
    P8Census.skeletonSubformula dotOp9Skel 1 .formula = dotArm := by
  simp [P8Census.skeletonSubformula, dotOp9Skel, genSkelOp9, ComputeTable.fanoutComp]

theorem skeletonMemoryAxis_dotOp9 :
    P8Census.skeletonMemoryAxis dotOp9Skel 2 = 2 :=
  genSkelOp9_memoryAxis _ _ _ _ _ _ _ _ _ _

theorem rendered_row6_recs (z α : K) :
    activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTree (K := K)) 6)).row.2.2.1 =
      [⟨encC z dotOp9Formula, encC z dotOp9Tail, 3, α ^ 9⟩,
       ⟨encC z dotOp9Tail, encC z (.atom 2), 2, α ^ 10⟩,
       ⟨encC z dotCore, encC z dotArm, 2, α ^ 11⟩] := by
  rw [renderNode_op9_row z α _ row_s9, bfsLabelAt_dot_skel6]
  simp only [activeRequestRecords, renderOp9Row, recExp_eq_getRecordExp,
    liveRecordExps_named, pow_one]
  rw [skeletonSubformula_dotOp9_core, skeletonSubformula_dotOp9_arm,
    skeletonMemoryAxis_dotOp9]
  simp only [dotOp9Skel, genSkelOp9]
  rw [formulaTail_dotOp9Formula, formulaHead_dotOp9Tail]
  have h := liveRecordExps_named (K := K)
  simp [h]

theorem rendered_row7_recs (z α : K) :
    activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTree (K := K)) 7)).row.2.2.1 =
      [⟨encC z dotCoreFormula, encC z dotCore, 3, α ^ 12⟩] := by
  rw [renderNode_op1_row z α _ row_s1_7, bfsLabelAt_dot_skel7]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_named, pow_one, dotOp9CoreTree, skelNode, genSkelOp1]

theorem rendered_row8_recs (z α : K) :
    activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTree (K := K)) 8)).row.2.2.1 =
      [⟨encC z dotArm, encC z dotResult, 3, α ^ 13⟩] := by
  rw [renderNode_op1_row z α _ row_s1_8, bfsLabelAt_dot_skel8]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_named, pow_one, dotOp9InvokeTree, skelNode, genSkelOp1]

theorem air_row_s6 :
    (bfsLabelAt (dotTreeAir (K := K)) 1).skel.state = State.s6 := by
  rw [bfsLabelAt_air_skel1]; rfl

theorem air_row_s2 :
    (bfsLabelAt (dotTreeAir (K := K)) 2).skel.state = State.s2 := by
  rw [bfsLabelAt_air_skel2]; rfl

theorem air_row_s1_3 :
    (bfsLabelAt (dotTreeAir (K := K)) 3).skel.state = State.s1 := by
  rw [bfsLabelAt_air_skel3]; rfl

theorem air_row_s1_4 :
    (bfsLabelAt (dotTreeAir (K := K)) 4).skel.state = State.s1 := by
  rw [bfsLabelAt_air_skel4]; rfl

theorem air_row_s1_5 :
    (bfsLabelAt (dotTreeAir (K := K)) 5).skel.state = State.s1 := by
  rw [bfsLabelAt_air_skel5]; rfl

theorem air_row_s9 :
    (bfsLabelAt (dotTreeAir (K := K)) 6).skel.state = State.s9 := by
  rw [bfsLabelAt_air_skel6]; rfl

theorem air_row_s1_7 :
    (bfsLabelAt (dotTreeAir (K := K)) 7).skel.state = State.s1 := by
  rw [bfsLabelAt_air_skel7]; rfl

theorem air_row_s1_8 :
    (bfsLabelAt (dotTreeAir (K := K)) 8).skel.state = State.s1 := by
  rw [bfsLabelAt_air_skel8]; rfl

theorem rendered_air_row1_recs (z α : K) :
    activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 1)).row.2.2.1 =
      [⟨encC z dotFormula, encC z dotParentTail, 3, α ^ 1⟩,
       ⟨encC z dotParentTail, encC z dotCondFormula, 2, α ^ 2⟩,
       ⟨encC z dotBranchPair, encC z dotThenFormula, 2, α ^ 3⟩] := by
  rw [renderNode_op6_row z α _ air_row_s6, bfsLabelAt_air_skel1]
  simp only [activeRequestRecords, renderOp6Row, recExp_eq_getRecordExp,
    liveRecordExps_air_named, pow_one, dotOp6Skel, genSkelOp6]
  rw [formulaTail_dotFormula, formulaHead_dotParentTail, formulaTail_dotParentTail,
    formulaHead_dotBranchPair]
  have h := liveRecordExps_air_named (K := K)
  simp [h, pow_one]

theorem rendered_air_row2_recs (z α : K) :
    activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 2)).row.2.2.1 =
      [⟨encC z dotThenFormula, encC z dotThenTail, 3, α ^ 4⟩,
       ⟨encC z dotThenTail, encC z dotOp2B, 2, α ^ 5⟩] := by
  rw [renderNode_op2_row z α _ air_row_s2, bfsLabelAt_air_skel2]
  have hskel : (dotOp2Tree (K := K)).label.skel = dotOp2Skel := rfl
  rw [hskel]
  simp only [activeRequestRecords, renderOp2Row, recExp_eq_getRecordExp,
    liveRecordExps_air_named, pow_one, dotOp2Skel, genSkelOp2]
  rw [formulaTail_dotThenFormula, formulaHead_dotThenTail]
  have h := liveRecordExps_air_named (K := K)
  simp [h]

theorem rendered_air_row3_recs (z α : K) :
    activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 3)).row.2.2.1 =
      [⟨encC z dotCondFormula, encC z dotCondResult, 3, α ^ 6⟩] := by
  rw [renderNode_op1_row z α _ air_row_s1_3, bfsLabelAt_air_skel3]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_air_named, pow_one, dotCondTree, skelNode, genSkelOp1]

theorem rendered_air_row4_recs (z α : K) :
    activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 4)).row.2.2.1 =
      [⟨encC z dotOp2B, encC z dotOp2Sf1, 3, α ^ 7⟩] := by
  rw [renderNode_op1_row z α _ air_row_s1_4, bfsLabelAt_air_skel4]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_air_named, pow_one, dotOp1BTree, skelNode, genSkelOp1]

theorem rendered_air_row5_recs (z α : K) :
    activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 5)).row.2.2.1 =
      [⟨encC z dotOp2C, encC z dotOp2Sf2, 3, α ^ 8⟩] := by
  rw [renderNode_op1_row z α _ air_row_s1_5, bfsLabelAt_air_skel5]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_air_named, pow_one, dotOp1CTree, skelNode, genSkelOp1]

theorem rendered_air_row6_recs (z α : K) :
    activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 6)).row.2.2.1 =
      [⟨encC z dotOp9Formula, encC z dotOp9Tail, 3, α ^ 9⟩,
       ⟨encC z dotOp9Tail, encC z (.atom 2), 2, α ^ 10⟩,
       ⟨encC z dotCore, encC z dotArm, 2, α ^ 11⟩] := by
  rw [renderNode_op9_row z α _ air_row_s9, bfsLabelAt_air_skel6]
  simp only [activeRequestRecords, renderOp9Row, recExp_eq_getRecordExp,
    liveRecordExps_air_named, pow_one]
  rw [skeletonSubformula_dotOp9_core, skeletonSubformula_dotOp9_arm,
    skeletonMemoryAxis_dotOp9]
  simp only [dotOp9Skel, genSkelOp9]
  rw [formulaTail_dotOp9Formula, formulaHead_dotOp9Tail]
  have h := liveRecordExps_air_named (K := K)
  simp [h]

theorem rendered_air_row7_recs (z α : K) :
    activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 7)).row.2.2.1 =
      [⟨encC z dotCoreFormula, encC z dotCore, 3, α ^ 12⟩] := by
  rw [renderNode_op1_row z α _ air_row_s1_7, bfsLabelAt_air_skel7]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_air_named, pow_one, dotOp9CoreTree, skelNode, genSkelOp1]

theorem rendered_air_row8_recs (z α : K) :
    activeRequestRecords
        (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 8)).row.2.2.1 =
      [⟨encC z dotArm, encC z dotResult, 3, α ^ 13⟩] := by
  rw [renderNode_op1_row z α _ air_row_s1_8, bfsLabelAt_air_skel8]
  simp [activeRequestRecords, renderOp1Row, recExp_eq_getRecordExp,
    liveRecordExps_air_named, pow_one, dotOp9InvokeTree, skelNode, genSkelOp1]

theorem genAnnotatedRecordTree_eq (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (axis recordExp : ℕ) :
    genAnnotatedRecordTree E z α lmb root child axis recordExp =
      .node (gMemRow9 (memReadSkelAx root child axis) recordExp z
        (annotatedReadPub E root child axis (α ^ recordExp)
          (genAnnotatedDescent E z lmb root child axis (α ^ recordExp)
            recordExp root axis).2 0 0 lmb))
        (genAnnotatedDescent E z lmb root child axis (α ^ recordExp)
          recordExp root axis).1 := by
  simp only [genAnnotatedRecordTree]

theorem genAnnotatedDescent_axis3 (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ts : K) (recordExp : ℕ) (hd tl : Noun) :
    genAnnotatedDescent E z lmb root child 3 ts recordExp (.cell hd tl) 3 =
      ([.node (gMemRow9 (memDecomposeSkel (.cell hd tl) hd tl) 0 z
          (annotatedDecPub E (.cell hd tl) hd tl
            (genAnnotatedNounWalk E z lmb hd).2
            (genAnnotatedVerify E z lmb root child 3 ts recordExp).2
            (nounWalkRootState hd) (descentRootState 1) 0 0 lmb))
          [(genAnnotatedNounWalk E z lmb hd).1,
           (genAnnotatedVerify E z lmb root child 3 ts recordExp).1]],
        (annotatedDecPub E (.cell hd tl) hd tl
          (genAnnotatedNounWalk E z lmb hd).2
          (genAnnotatedVerify E z lmb root child 3 ts recordExp).2
          (nounWalkRootState hd) (descentRootState 1) 0 0 lmb).pt) := by
  unfold genAnnotatedDescent
  simp only [show ¬((3 : ℕ) < 2) from by omega, formulaHead, formulaTail,
    axisTopBit_three, axisRest_three, ↓reduceIte]
  unfold genAnnotatedDescent
  simp only [show (1 : ℕ) < 2 from by omega, ↓reduceIte, ite_true,
    genAnnotatedVerify, List.cons_append, List.nil_append]

theorem genAnnotatedDescent_axis2 (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ts : K) (recordExp : ℕ) (hd tl : Noun) :
    genAnnotatedDescent E z lmb root child 2 ts recordExp (.cell hd tl) 2 =
      ([.node (gMemRow9 (memDecomposeSkel (.cell hd tl) hd tl) 0 z
          (annotatedDecPub E (.cell hd tl) hd tl
            (genAnnotatedVerify E z lmb root child 2 ts recordExp).2
            (genAnnotatedNounWalk E z lmb tl).2
            (descentRootState 1) (nounWalkRootState tl) 0 0 lmb))
          [(genAnnotatedVerify E z lmb root child 2 ts recordExp).1,
           (genAnnotatedNounWalk E z lmb tl).1]],
        (annotatedDecPub E (.cell hd tl) hd tl
          (genAnnotatedVerify E z lmb root child 2 ts recordExp).2
          (genAnnotatedNounWalk E z lmb tl).2
          (descentRootState 1) (nounWalkRootState tl) 0 0 lmb).pt) := by
  unfold genAnnotatedDescent
  simp only [show ¬((2 : ℕ) < 2) from by omega, formulaHead, formulaTail,
    axisTopBit_two, axisRest_two, Bool.false_eq_true, ↓reduceIte]
  unfold genAnnotatedDescent
  simp only [show (1 : ℕ) < 2 from by omega, ↓reduceIte, ite_true,
    genAnnotatedVerify, List.cons_append, List.nil_append]

theorem genAnnotatedChainedTree_pair (E : Noun → ComputeTable.FP K) (z α : K)
    (r1 r2 : MemRecordReq) :
    genAnnotatedChainedTree E z α lmb [r1, r2] =
      some (.node (gMemRow9 (memReadSkelAx r1.root r1.child r1.axis) r1.recordExp z
          (annotatedReadPub E r1.root r1.child r1.axis (α ^ r1.recordExp)
            (genAnnotatedDescentCont E z lmb
              (genAnnotatedChainedInner E z α lmb r1 [r2]).1
              (genAnnotatedChainedInner E z α lmb r1 [r2]).2
              (chainedInnerRootState [r2]) r1.root r1.axis).2 0 0 lmb))
        (genAnnotatedDescentCont E z lmb
          (genAnnotatedChainedInner E z α lmb r1 [r2]).1
          (genAnnotatedChainedInner E z α lmb r1 [r2]).2
          (chainedInnerRootState [r2]) r1.root r1.axis).1) :=
  rfl

theorem genMemForestFromTree_as_node (E : Noun → ComputeTable.FP K) (z α : K)
    (t : NTree (GenComputeRow K)) :
    genMemForestFromTree E z α lmb t =
      genRowMemForest E z α lmb (extractNodeReqs t.label) ++
        genMemForestFromList E z α lmb t.children := by
  cases t with
  | node _ _ => rfl

theorem genRowMemForest_chain32_head (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    ∃ t, genRowMemForest E z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩] =
      [t] ∧
      genAnnotatedChainedTree E z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩] = some t := by
  unfold genRowMemForest
  cases h : genAnnotatedChainedTree E z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] with
  | none =>
    simp [genAnnotatedChainedTree] at h
  | some t =>
    simp [h]

/-- Every node of an annotated noun walk has `ver = false`. -/
theorem genAnnotatedNounWalk_inTree_ver_false (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n t, InTree (genAnnotatedNounWalk E z lmb n).1 t →
      t.label.row.2.2.ver = false
  | .atom a, t, ht => by
      cases ht with
      | here => simp [genAnnotatedNounWalk, gMemRow9, op9HaltPub]
      | sub hs _ =>
          simp [genAnnotatedNounWalk, NTree.children_node] at hs
  | .cell h tl, t, ht => by
      cases ht with
      | here => simp [genAnnotatedNounWalk, gMemRow9, annotatedDecPub]
      | sub hs hsub =>
          simp only [genAnnotatedNounWalk, NTree.children_node, List.mem_cons,
            List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · exact genAnnotatedNounWalk_inTree_ver_false E z h _ hsub
          · exact genAnnotatedNounWalk_inTree_ver_false E z tl _ hsub

theorem genAnnotatedNounWalk_ver_false (E : Noun → ComputeTable.FP K) (z : K) (n : Noun) :
    (genAnnotatedNounWalk E z lmb n).1.label.row.2.2.ver = false :=
  genAnnotatedNounWalk_inTree_ver_false E z n _ (InTree.here _)



/-- BFS nodes under the axis-2 descent-cont used by a chained inner read are non-response. -/
theorem genAnnotatedDescentCont_axis2_bfs_ver_false
    (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) (hd tl : Noun)
    (hcont : ∀ t ∈ bfsForest cont, t.label.row.2.2.ver = false) :
    ∀ t ∈ bfsForest (genAnnotatedDescentCont E z lmb cont contCell contState (.cell hd tl) 2).1,
      t.label.row.2.2.ver = false := by
  rw [genAnnotatedDescentCont_axis2]
  intro t ht
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp ht
  simp only [List.mem_singleton] at hc
  subst c
  cases hin with
  | here =>
      simp [NTree.label, gMemRow9, annotatedDecPub]
  | sub hs hsub =>
      simp only [NTree.children_node] at hs
      rw [List.mem_append] at hs
      rcases hs with hC | hW
      · exact hcont t ((mem_bfsForest _ _).mpr ⟨_, hC, hsub⟩)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hW
        subst hW
        exact genAnnotatedNounWalk_inTree_ver_false E z tl t hsub

theorem genAnnotatedVerify_ver_false (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ) :
    (genAnnotatedVerify E z lmb root child ax ts recordExp).1.label.row.2.2.ver = false := by
  simp [genAnnotatedVerify, gMemRow9, annotatedVerifyPub]

theorem genAnnotatedVerify_bfs_ver_false (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ) :
    ∀ t ∈ bfsForest [(genAnnotatedVerify E z lmb root child ax ts recordExp).1],
      t.label.row.2.2.ver = false := by
  intro t ht
  obtain ⟨_, hmem, hin⟩ := (mem_bfsForest _ _).mp ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  cases hin with
  | here => exact genAnnotatedVerify_ver_false E z root child ax ts recordExp
  | sub hs hsub =>
      simp only [genAnnotatedVerify, NTree.children_node, List.mem_cons,
        List.not_mem_nil, or_false] at hs
      subst hs
      exact genAnnotatedNounWalk_inTree_ver_false E z child _ hsub

theorem genAnnotatedChainedTree_axis3_axis2_shape
    (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ)
    (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩] = some t) :
    ∃ dec walk inner,
      t.children = [dec] ∧
      dec.label.row.2.2.st = .decompose ∧
      dec.label.row.2.2.ver = false ∧
      dec.children = [walk, inner] ∧
      walk.label.row.2.2.st ≠ .read_root ∧
      walk.label.row.2.2.ver = false ∧
      (∀ u, InTree walk u → u.label.row.2.2.ver = false) ∧
      treeFibre (.read_root : MemoryTable.MState) walk = 0 ∧
      inner.label.row.2.2.st = .read_root ∧
      inner.label.row.2.2.ver = true ∧
      inner.label.row.2.2.mem =
        ⟨E (.cell hd2 tl2), E hd2, (2 : K), α ^ e2⟩ ∧
      forestFibre (.read_root : MemoryTable.MState) inner.children = 0 ∧
      (∀ u ∈ bfsForest inner.children, u.label.row.2.2.ver = false) := by
  rw [genAnnotatedChainedTree_pair] at ht
  injection ht with ht
  subst t
  simp only [NTree.children_node]
  rw [genAnnotatedDescentCont_axis3]
  simp only [NTree.children_node]
  unfold genAnnotatedChainedInner
  simp only [genAnnotatedChainedInner_nil, chainedInnerRootState]
  rw [genAnnotatedDescentCont_axis2]
  simp only [List.cons_append, List.nil_append, NTree.children_node]
  refine ⟨_, _, _, rfl, ?hstDec, ?hverDec, rfl, ?hstWalk, ?hverWalk, ?hAllWalk, ?hfWalk,
    ?hstInner, ?hverInner, ?hmemInner, ?hfInner, ?hChInner⟩
  · simp [NTree.label, gMemRow9_st, annotatedDecPub_st]
  · simp [NTree.label, gMemRow9, annotatedDecPub]
  · exact genAnnotatedNounWalk_not_read E z hd1
  · simpa [NTree.label] using genAnnotatedNounWalk_ver_false E z hd1
  · intro u hu
    exact genAnnotatedNounWalk_inTree_ver_false E z hd1 u hu
  · exact genAnnotatedNounWalk_fibre_read E z hd1
  · simp [NTree.label, gMemRow9_st, annotatedReadPub_st]
  · simp [NTree.label, gMemRow9, annotatedReadPub]
  · simp [NTree.label, gMemRow9_mem, annotatedReadPub_mem]
  · simp [NTree.children_node, forestFibre_cons, forestFibre_nil, treeFibre_gMemRow9,
      annotatedVerifyPub_st, annotatedDecPub_st, genAnnotatedVerify_fibre_read,
      genAnnotatedNounWalk_fibre_read]
  · intro u hu
    obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp hu
    simp only [NTree.children_node, List.mem_singleton] at hc
    subst c
    cases hin with
    | here =>
        simp [NTree.label, gMemRow9, annotatedVerifyPub]
    | sub hs hsub =>
        simp only [NTree.children_node, List.mem_singleton] at hs
        subst hs
        cases hsub with
        | here =>
            simp [NTree.label, gMemRow9, annotatedDecPub]
        | sub hs2 hsub2 =>
            simp only [NTree.children_node, List.mem_cons, List.not_mem_nil,
              or_false] at hs2
            rcases hs2 with rfl | rfl
            · cases hsub2 with
              | here =>
                  simp [genAnnotatedVerify, NTree.label, gMemRow9, annotatedVerifyPub]
              | sub hs3 hsub3 =>
                  simp only [genAnnotatedVerify, NTree.children_node,
                    List.mem_singleton] at hs3
                  subst hs3
                  exact genAnnotatedNounWalk_inTree_ver_false E z hd2 _ hsub3
            · exact genAnnotatedNounWalk_inTree_ver_false E z tl2 _ hsub2

theorem genAnnotatedNounWalk_bfs_ver_false (E : Noun → ComputeTable.FP K) (z : K) (n : Noun) :
    ∀ t ∈ bfsForest [(genAnnotatedNounWalk E z lmb n).1],
      t.label.row.2.2.ver = false := by
  intro t ht
  obtain ⟨_, hmem, hin⟩ := (mem_bfsForest _ _).mp ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  exact genAnnotatedNounWalk_inTree_ver_false E z n t hin

/-- Every BFS node of an annotated descent has `ver = false`. -/
theorem genAnnotatedDescent_bfs_ver_false (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (currentNoun : Noun) (remainingAxis : ℕ) :
    ∀ t ∈ bfsForest (genAnnotatedDescent E z lmb root child recAxis ts recordExp
        currentNoun remainingAxis).1,
      t.label.row.2.2.ver = false := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    unfold genAnnotatedDescent
    split
    · exact genAnnotatedVerify_bfs_ver_false E z root child recAxis ts recordExp
    · split
      · intro t ht
        obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp ht
        simp only [List.mem_singleton] at hc
        subst c
        cases hin with
        | here =>
            simp [NTree.label, gMemRow9, annotatedDecPub]
        | sub hs hsub =>
            simp only [NTree.children] at hs
            rw [List.mem_append] at hs
            rcases hs with hW | hC
            · simp only [List.mem_singleton] at hW
              subst hW
              exact genAnnotatedNounWalk_inTree_ver_false E z
                (formulaHead currentNoun) t hsub
            · exact ih (axisRest n) (axisRest_lt (by omega)) (formulaTail currentNoun) t
                ((mem_bfsForest _ _).mpr ⟨_, hC, hsub⟩)
      · intro t ht
        obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp ht
        simp only [List.mem_singleton] at hc
        subst c
        cases hin with
        | here =>
            simp [NTree.label, gMemRow9, annotatedDecPub]
        | sub hs hsub =>
            simp only [NTree.children] at hs
            rw [List.mem_append] at hs
            rcases hs with hC | hW
            · exact ih (axisRest n) (axisRest_lt (by omega)) (formulaHead currentNoun) t
                ((mem_bfsForest _ _).mpr ⟨_, hC, hsub⟩)
            · simp only [List.mem_singleton] at hW
              subst hW
              exact genAnnotatedNounWalk_inTree_ver_false E z
                (formulaTail currentNoun) t hsub

theorem genAnnotatedRecordTree_children_bfs_ver_false
    (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (axis recordExp : ℕ) :
    ∀ t ∈ bfsForest (genAnnotatedRecordTree E z α lmb root child axis recordExp).children,
      t.label.row.2.2.ver = false := by
  intro t ht
  unfold genAnnotatedRecordTree at ht
  exact genAnnotatedDescent_bfs_ver_false E z root child axis (α ^ recordExp) recordExp
    root axis t ht

theorem genAnnotatedRecordTree_axis3_shape (E : Noun → ComputeTable.FP K)
    (z α : K) (hd tl : Noun) (e : ℕ) :
    ∃ dec,
      (genAnnotatedRecordTree E z α lmb (.cell hd tl) tl 3 e).children = [dec] ∧
      dec.label.row.2.2.st = .decompose ∧
      dec.label.row.2.2.ver = false ∧
      (∀ u ∈ dec.children, u.label.row.2.2.st ≠ .read_root) ∧
      (∀ c ∈ dec.children, ∀ u, InTree c u → u.label.row.2.2.ver = false) ∧
      forestFibre (.read_root : MemoryTable.MState) dec.children = 0 := by
  rw [genAnnotatedRecordTree_eq, genAnnotatedDescent_axis3]
  simp only [NTree.children_node]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [NTree.label, gMemRow9_st, annotatedDecPub_st]
  · simp [NTree.label, gMemRow9, annotatedDecPub]
  · intro u hu
    simp only [NTree.children_node, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact genAnnotatedNounWalk_not_read E z hd
    · simp [genAnnotatedVerify, NTree.label, gMemRow9_st, annotatedVerifyPub_st]
  · intro c hc u hu
    simp only [NTree.children_node, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact genAnnotatedNounWalk_inTree_ver_false E z hd u hu
    · cases hu with
      | here => simp [genAnnotatedVerify, NTree.label, gMemRow9, annotatedVerifyPub]
      | sub hs hsub =>
          simp only [genAnnotatedVerify, NTree.children_node, List.mem_singleton] at hs
          subst hs
          exact genAnnotatedNounWalk_inTree_ver_false E z tl _ hsub
  · simp only [NTree.children_node]
    rw [forestFibre_cons, forestFibre_cons, forestFibre_nil]
    rw [genAnnotatedNounWalk_fibre_read, genAnnotatedVerify_fibre_read]

theorem genAnnotatedRecordTree_axis2_shape (E : Noun → ComputeTable.FP K)
    (z α : K) (hd tl : Noun) (e : ℕ) :
    ∃ dec,
      (genAnnotatedRecordTree E z α lmb (.cell hd tl) hd 2 e).children = [dec] ∧
      dec.label.row.2.2.st = .decompose ∧
      dec.label.row.2.2.ver = false ∧
      (∀ u ∈ dec.children, u.label.row.2.2.st ≠ .read_root) ∧
      (∀ c ∈ dec.children, ∀ u, InTree c u → u.label.row.2.2.ver = false) ∧
      forestFibre (.read_root : MemoryTable.MState) dec.children = 0 := by
  rw [genAnnotatedRecordTree_eq, genAnnotatedDescent_axis2]
  simp only [NTree.children_node]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [NTree.label, gMemRow9_st, annotatedDecPub_st]
  · simp [NTree.label, gMemRow9, annotatedDecPub]
  · intro u hu
    simp only [NTree.children_node, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · simp [genAnnotatedVerify, NTree.label, gMemRow9_st, annotatedVerifyPub_st]
    · exact genAnnotatedNounWalk_not_read E z tl
  · intro c hc u hu
    simp only [NTree.children_node, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases hu with
      | here => simp [genAnnotatedVerify, NTree.label, gMemRow9, annotatedVerifyPub]
      | sub hs hsub =>
          simp only [genAnnotatedVerify, NTree.children_node, List.mem_singleton] at hs
          subst hs
          exact genAnnotatedNounWalk_inTree_ver_false E z hd _ hsub
    · exact genAnnotatedNounWalk_inTree_ver_false E z tl u hu
  · simp only [NTree.children_node]
    rw [forestFibre_cons, forestFibre_cons, forestFibre_nil]
    rw [genAnnotatedVerify_fibre_read, genAnnotatedNounWalk_fibre_read]

theorem servedGen_flatMap_reads (l : List (NTree (GenMemoryRow K)))
    (h : ∀ t ∈ l, t.label.row.2.2.st = .read_root)
    (hver : ∀ t ∈ l, t.label.row.2.2.ver = true) :
    l.flatMap (fun t => responseRecords t.label.row.2.2) =
      l.map (fun t => t.label.row.2.2.mem) := by
  induction l with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.flatMap_cons, List.map_cons]
    rw [responseRecords_eq_singleton_of_read_root _ (h t (by simp)) (hver t (by simp)),
      ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
        (fun t' ht' => hver t' (List.mem_cons_of_mem _ ht'))]
    rfl

theorem servedGen_reads_prefix (l : List (NTree (GenMemoryRow K))) (hl : l ≠ [])
    (h : ∀ t ∈ l, t.label.row.2.2.st = .read_root)
    (hver : ∀ t ∈ l, t.label.row.2.2.ver = true) :
    servedGen l =
      l.map (fun t => t.label.row.2.2.mem) ++
        servedGen (l.flatMap NTree.children) := by
  rw [servedGen_of_ne_nil l hl, servedGen_flatMap_reads l h hver]

theorem responseRecords_eq_nil_of_ne_read (pub : MemoryTable.Pub K)
    (h : pub.st ≠ .read_root) (hver : pub.ver = false) :
    responseRecords pub = [] :=
  responseRecords_eq_nil_of_not_ver pub hver

theorem responseRecords_flatMap_not_read (l : List (NTree (GenMemoryRow K)))
    (h : ∀ t ∈ l, t.label.row.2.2.st ≠ .read_root)
    (hver : ∀ t ∈ l, t.label.row.2.2.ver = false) :
    l.flatMap (fun t => responseRecords t.label.row.2.2) = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  obtain ⟨t, ht, hx'⟩ := List.mem_flatMap.mp hx
  rw [responseRecords_eq_nil_of_ne_read _ (h t ht) (hver t ht)] at hx'
  cases hx'

theorem forestFibre_children_of_zero (l : List (NTree (GenMemoryRow K)))
    (h : forestFibre (.read_root : MemoryTable.MState) l = 0) :
    forestFibre (.read_root : MemoryTable.MState) (l.flatMap NTree.children) = 0 := by
  have := forestFibre_eq_roots_add_children (.read_root : MemoryTable.MState) l
  omega

theorem forestFibre_flatMap_append (s : MemoryTable.MState)
    (l₁ l₂ : List (NTree (GenMemoryRow K))) :
    forestFibre s ((l₁ ++ l₂).flatMap NTree.children) =
      forestFibre s (l₁.flatMap NTree.children) +
        forestFibre s (l₂.flatMap NTree.children) := by
  rw [List.flatMap_append, forestFibre_append]

theorem treeFibre_zero_children (w : NTree (GenMemoryRow K))
    (h : treeFibre (.read_root : MemoryTable.MState) w = 0) :
    forestFibre (.read_root : MemoryTable.MState) w.children = 0 := by
  cases w with
  | node g cs =>
    rw [NTree.children_node]
    simp [treeFibre_node] at h
    omega

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig769

open Nock Nock.Walk Nock.Noun Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.RowLayout

noncomputable section

theorem execThreaded_computeTree (z α : K) :
    (execThreaded z α).computeTree = (exec z α).computeTree :=
  rfl

theorem execThreaded_computeRows (z α : K) :
    (execThreaded z α).computeRows = (exec z α).computeRows :=
  rfl

theorem computeRows_eq_threaded (z α : K) :
    (execThreaded z α).computeRows =
      [(renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 1)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 2)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 3)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 4)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 5)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 6)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 7)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 8)).row] := by
  rw [execThreaded_computeRows, computeRows_eq]

theorem computeRowsAccepted_threaded (z α : K) (hz : z ≠ 0) :
    (execThreaded z α).ComputeRowsAccepted := by
  have h := computeRowsAccepted z α hz
  rw [ExactExecution.computeRowsAccepted_iff] at h ⊢
  rw [execThreaded_computeRows]
  exact h

theorem computeRowAt_eq_threaded (z α : K) (i : Fin (cfg z α).compRows) :
    (execThreaded z α).computeRowAt i =
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) ((i : ℕ) + 1))).row := by
  have h8 : (cfg z α).compRows = 8 := by simp [cfg]
  have hi : (i : ℕ) < 8 := by
    have := i.isLt
    simp [h8] at this
    exact this
  have hrows := computeRows_eq_threaded z α
  have hlt : (i : ℕ) < (execThreaded z α).computeRows.length := by
    have hlen := (execThreaded z α).computeRows_length
    have hltcfg := i.isLt
    omega
  have hget :
      (execThreaded z α).computeRowAt i =
        (execThreaded z α).computeRows[(i : ℕ)]'hlt := by
    simp [ExactExecution.computeRowAt, List.get_eq_getElem]
  rw [hget]
  have hlt' : (i : ℕ) <
      [(renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 1)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 2)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 3)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 4)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 5)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 6)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 7)).row,
       (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 8)).row].length := by
    simp; omega
  have hidx := congrArg (fun l : List _ => l[(i : ℕ)]?) hrows
  simp only [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hlt'] at hidx
  have heq := Option.some.inj hidx
  rw [heq]
  interval_cases (i : ℕ) <;> simp

theorem computePubAt_eq_threaded (z α : K) (i : Fin (cfg z α).compRows) :
    (execThreaded z α).computePubAt i =
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) ((i : ℕ) + 1))).row.2.2.1 := by
  rw [ExactExecution.computePubAt, computeRowAt_eq_threaded]

theorem compute_chain_threaded (z α : K) :
    ∀ i : Fin (cfg z α).compRows,
      ∀ hi : (i : ℕ) + 1 < (cfg z α).compRows,
        ((execThreaded z α).computePubAt i).ln =
          ((execThreaded z α).computePubAt ⟨(i : ℕ) + 1, hi⟩).ln_prev := by
  intro i hi
  rw [computePubAt_eq_threaded, computePubAt_eq_threaded]
  exact adjacent_ln_air z α (i : ℕ) (by
    have h8 : (cfg z α).compRows = 8 := by simp [cfg]
    omega)

theorem compute_wf_threaded (z α : K) :
    ∀ i, ComputeTable.WF (cfg z α).challenges.computeInputs
      ((execThreaded z α).computePubAt i) := by
  intro i
  have hch : (cfg z α).challenges.computeInputs = ⟨α, z, 0, 0, 0⟩ := by
    simp [cfg, ChallengeVector.computeInputs]
  rw [computePubAt_eq_threaded, hch]
  have hi : ((i : ℕ) + 1) ∈
      List.range' 1 (bfsForest [dotTreeAir (K := K)]).length := by
    have hlen : (bfsForest [dotTreeAir (K := K)]).length = 8 := by
      simp [dot_air_bfsForest]
    have h8 : (cfg z α).compRows = 8 := by simp [cfg]
    have hlt : (i : ℕ) < 8 := by
      have := i.isLt
      simp [h8] at this
      exact this
    rw [hlen]
    exact List.mem_range'.mpr ⟨(i : ℕ), hlt, by omega⟩
  exact renderNode_wf z α _ (bfsLabelAt_air_live_state _ hi)

theorem rawRequests_eq (z α : K) :
    (exec z α).rawRequests =
      [⟨encC z dotFormula, encC z dotParentTail, 3, α ^ 1⟩,
       ⟨encC z dotParentTail, encC z dotCondFormula, 2, α ^ 2⟩,
       ⟨encC z dotBranchPair, encC z dotThenFormula, 2, α ^ 3⟩,
       ⟨encC z dotThenFormula, encC z dotThenTail, 3, α ^ 4⟩,
       ⟨encC z dotThenTail, encC z dotOp2B, 2, α ^ 5⟩,
       ⟨encC z dotCondFormula, encC z dotCondResult, 3, α ^ 6⟩,
       ⟨encC z dotOp2B, encC z dotOp2Sf1, 3, α ^ 7⟩,
       ⟨encC z dotOp2C, encC z dotOp2Sf2, 3, α ^ 8⟩,
       ⟨encC z dotOp9Formula, encC z dotOp9Tail, 3, α ^ 9⟩,
       ⟨encC z dotOp9Tail, encC z (.atom 2), 2, α ^ 10⟩,
       ⟨encC z dotCore, encC z dotArm, 2, α ^ 11⟩,
       ⟨encC z dotCoreFormula, encC z dotCore, 3, α ^ 12⟩,
       ⟨encC z dotArm, encC z dotResult, 3, α ^ 13⟩] := by
  rw [ExactExecution.rawRequests_eq_computeRows, computeRows_eq]
  simp [List.flatMap_cons, rendered_air_row1_recs, rendered_air_row2_recs,
    rendered_air_row3_recs, rendered_air_row4_recs, rendered_air_row5_recs,
    rendered_air_row6_recs, rendered_air_row7_recs, rendered_air_row8_recs]

theorem execThreaded_rawRequests (z α : K) :
    (execThreaded z α).rawRequests = (exec z α).rawRequests :=
  rfl

theorem execThreadedA_rawRequests (z α : K) :
    (execThreadedA z α).rawRequests = (exec z α).rawRequests :=
  rfl

def recOf (z α : K) (root child : Noun) (ax exp : ℕ) : MemRec K :=
  ⟨encC z root, encC z child, (ax : K), α ^ exp⟩

def semOf (z : K) (axis : F) (root child : Noun) (exp : ℕ) :
    (nmrMEF F K).Rec :=
  (axis,
    ((((encC z root).size, (encC z root).dyck, (encC z root).leaf),
      ((encC z child).size, (encC z child).dyck, (encC z child).leaf)),
     exp))

theorem semOf_preimage (z α : K) (axis : F) (root child : Noun) (exp : ℕ) :
    memRecOfNMR F K ((nmrEncoding F K α).encode (semOf z axis root child exp)) =
      ⟨encC z root, encC z child, algebraMap F K axis, α ^ exp⟩ := by
  ext <;> simp [semOf, memRecOfNMR, nmrEncoding]

theorem semOf_bridge (z α lmb : K) (axis : F) (root child : Noun) (exp ax : ℕ)
    (hax : algebraMap F K axis = (ax : K)) :
    bridge F K α lmb (semOf z axis root child exp) =
      encRecFormR ⟨encC z root, encC z child, (ax : K), α ^ exp⟩ lmb := by
  rw [← d2_record_bridge_agrees, semOf_preimage, hax]

theorem algebraMap_two : algebraMap F K (2 : F) = (2 : K) := by
  simp [map_ofNat]

theorem algebraMap_three : algebraMap F K (3 : F) = (3 : K) := by
  simp [map_ofNat]

theorem four_pow_2 : (4 : F) ^ 2 = 16 := by decide
theorem four_pow_4 : (4 : F) ^ 4 = 256 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, four_pow_2]; decide
theorem four_pow_8 : (4 : F) ^ 8 = 171 := by
  rw [show 8 = 4 * 2 from rfl, pow_mul, four_pow_4]; decide
theorem four_pow_16 : (4 : F) ^ 16 = 19 := by
  rw [show 16 = 8 * 2 from rfl, pow_mul, four_pow_8]; decide
theorem four_pow_32 : (4 : F) ^ 32 = 361 := by
  rw [show 32 = 16 * 2 from rfl, pow_mul, four_pow_16]; decide
theorem four_pow_64 : (4 : F) ^ 64 = 360 := by
  rw [show 64 = 32 * 2 from rfl, pow_mul, four_pow_32]; decide
theorem four_pow_96 : (4 : F) ^ 96 = 768 := by
  rw [show 96 = 64 + 32 from rfl, pow_add, four_pow_64, four_pow_32]; decide
theorem four_pow_192 : (4 : F) ^ 192 = 1 := by
  have h768 : (768 : F) = -1 := by decide
  rw [show 192 = 96 * 2 from rfl, pow_mul, four_pow_96, h768, neg_one_pow_two]

theorem four_pows_ne_one :
    (4 : F) ^ 1 ≠ 1 ∧ (4 : F) ^ 2 ≠ 1 ∧ (4 : F) ^ 3 ≠ 1 ∧ (4 : F) ^ 4 ≠ 1 ∧
    (4 : F) ^ 5 ≠ 1 ∧ (4 : F) ^ 6 ≠ 1 ∧ (4 : F) ^ 7 ≠ 1 ∧ (4 : F) ^ 8 ≠ 1 ∧
    (4 : F) ^ 9 ≠ 1 ∧ (4 : F) ^ 10 ≠ 1 ∧ (4 : F) ^ 11 ≠ 1 ∧ (4 : F) ^ 12 ≠ 1 ∧
    (4 : F) ^ 13 ≠ 1 := by
  decide

theorem four_pow_ne_one {k : ℕ} (hpos : 0 < k) (hlt : k < 14) :
    (4 : F) ^ k ≠ 1 := by
  have h := four_pows_ne_one
  interval_cases k <;> simp_all

theorem four_order_ge_14 : 14 ≤ orderOf (4 : F) := by
  have hfin : IsOfFinOrder (4 : F) :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨192, by norm_num, four_pow_192⟩
  have hpos : 0 < orderOf (4 : F) := orderOf_pos_iff.2 hfin
  refine le_of_not_gt ?_
  intro hlt
  exact four_pow_ne_one hpos hlt (pow_orderOf_eq_one _)

theorem alphaA_order_ge_14 : 14 ≤ orderOf alphaA := by
  have h := orderOf_injective φ.toMonoidHom φ_injective (4 : F)
  simpa [alphaA] using (h ▸ four_order_ge_14)

def sem1 : (nmrMEF F K).Rec := semOf seedZ (3 : F) dotFormula dotParentTail 1
def sem2 : (nmrMEF F K).Rec := semOf seedZ (2 : F) dotParentTail dotCondFormula 2
def sem3 : (nmrMEF F K).Rec := semOf seedZ (2 : F) dotBranchPair dotThenFormula 3
def sem4 : (nmrMEF F K).Rec := semOf seedZ (3 : F) dotThenFormula dotThenTail 4
def sem5 : (nmrMEF F K).Rec := semOf seedZ (2 : F) dotThenTail dotOp2B 5
def sem6 : (nmrMEF F K).Rec := semOf seedZ (3 : F) dotCondFormula dotCondResult 6
def sem7 : (nmrMEF F K).Rec := semOf seedZ (3 : F) dotOp2B dotOp2Sf1 7
def sem8 : (nmrMEF F K).Rec := semOf seedZ (3 : F) dotOp2C dotOp2Sf2 8
def sem9 : (nmrMEF F K).Rec := semOf seedZ (3 : F) dotOp9Formula dotOp9Tail 9
def sem10 : (nmrMEF F K).Rec := semOf seedZ (2 : F) dotOp9Tail (.atom 2) 10
def sem11 : (nmrMEF F K).Rec := semOf seedZ (2 : F) dotCore dotArm 11
def sem12 : (nmrMEF F K).Rec := semOf seedZ (3 : F) dotCoreFormula dotCore 12
def sem13 : (nmrMEF F K).Rec := semOf seedZ (3 : F) dotArm dotResult 13

def semanticRequestList : List ((nmrMEF F K).Rec) :=
  [sem1, sem2, sem3, sem4, sem5, sem6, sem7, sem8, sem9, sem10, sem11, sem12, sem13]

/-- Forest-BFS response order: ten tree-root reads, then the three inner
    chained reads (`2`, `6`, `10`). -/
def semanticResponseList : List ((nmrMEF F K).Rec) :=
  [sem1, sem3, sem4, sem7, sem8, sem9, sem11, sem12, sem13, sem6, sem2, sem5, sem10]

theorem sem_bridge (r : (nmrMEF F K).Rec)
    (root child : Noun) (axis : F) (exp ax : ℕ)
    (hr : r = semOf seedZ axis root child exp)
    (hax : algebraMap F K axis = (ax : K)) :
    bridge F K alphaA formRDefault r =
      encRecFormR ⟨encC seedZ root, encC seedZ child, (ax : K), alphaA ^ exp⟩ formRDefault := by
  subst hr
  exact semOf_bridge seedZ alphaA formRDefault axis root child exp ax hax

theorem derived_requests :
    (execThreaded seedZ alphaA).derivedRequestIO =
      [encRecFormR ⟨encC seedZ dotFormula, encC seedZ dotParentTail, 3, alphaA ^ 1⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotParentTail, encC seedZ dotCondFormula, 2,
           alphaA ^ 2⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotBranchPair, encC seedZ dotThenFormula, 2,
           alphaA ^ 3⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotThenFormula, encC seedZ dotThenTail, 3, alphaA ^ 4⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotThenTail, encC seedZ dotOp2B, 2, alphaA ^ 5⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotCondFormula, encC seedZ dotCondResult, 3,
           alphaA ^ 6⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotOp2B, encC seedZ dotOp2Sf1, 3, alphaA ^ 7⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotOp2C, encC seedZ dotOp2Sf2, 3, alphaA ^ 8⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotOp9Formula, encC seedZ dotOp9Tail, 3, alphaA ^ 9⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotOp9Tail, encC seedZ (.atom 2), 2, alphaA ^ 10⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotCore, encC seedZ dotArm, 2, alphaA ^ 11⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotCoreFormula, encC seedZ dotCore, 3, alphaA ^ 12⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotArm, encC seedZ dotResult, 3, alphaA ^ 13⟩ formRDefault] := by
  rw [ExactExecution.derivedRequestIO, execThreaded_rawRequests, rawRequests_eq]
  rfl

theorem sem1_bridge :
    bridge F K alphaA formRDefault sem1 =
      encRecFormR ⟨encC seedZ dotFormula, encC seedZ dotParentTail, 3, alphaA ^ 1⟩ formRDefault :=
  semOf_bridge seedZ alphaA formRDefault (3 : F) dotFormula dotParentTail 1 3 algebraMap_three

theorem sem2_bridge :
    bridge F K alphaA formRDefault sem2 =
      encRecFormR ⟨encC seedZ dotParentTail, encC seedZ dotCondFormula, 2,
          alphaA ^ 2⟩ formRDefault :=
  semOf_bridge seedZ alphaA formRDefault (2 : F) dotParentTail dotCondFormula 2 2 algebraMap_two

theorem sem3_bridge :
    bridge F K alphaA formRDefault sem3 =
      encRecFormR ⟨encC seedZ dotBranchPair, encC seedZ dotThenFormula, 2,
          alphaA ^ 3⟩ formRDefault :=
  semOf_bridge seedZ alphaA formRDefault (2 : F) dotBranchPair dotThenFormula 3 2 algebraMap_two

theorem sem4_bridge :
    bridge F K alphaA formRDefault sem4 =
      encRecFormR ⟨encC seedZ dotThenFormula, encC seedZ dotThenTail, 3, alphaA ^ 4⟩ formRDefault :=
  semOf_bridge seedZ alphaA formRDefault (3 : F) dotThenFormula dotThenTail 4 3 algebraMap_three

theorem sem5_bridge :
    bridge F K alphaA formRDefault sem5 =
      encRecFormR ⟨encC seedZ dotThenTail, encC seedZ dotOp2B, 2, alphaA ^ 5⟩ formRDefault :=
  semOf_bridge seedZ alphaA formRDefault (2 : F) dotThenTail dotOp2B 5 2 algebraMap_two

theorem sem6_bridge :
    bridge F K alphaA formRDefault sem6 =
      encRecFormR ⟨encC seedZ dotCondFormula, encC seedZ dotCondResult, 3,
          alphaA ^ 6⟩ formRDefault :=
  semOf_bridge seedZ alphaA formRDefault (3 : F) dotCondFormula dotCondResult 6 3 algebraMap_three

theorem sem7_bridge :
    bridge F K alphaA formRDefault sem7 =
      encRecFormR ⟨encC seedZ dotOp2B, encC seedZ dotOp2Sf1, 3, alphaA ^ 7⟩ formRDefault :=
  semOf_bridge seedZ alphaA formRDefault (3 : F) dotOp2B dotOp2Sf1 7 3 algebraMap_three

theorem sem8_bridge :
    bridge F K alphaA formRDefault sem8 =
      encRecFormR ⟨encC seedZ dotOp2C, encC seedZ dotOp2Sf2, 3, alphaA ^ 8⟩ formRDefault :=
  semOf_bridge seedZ alphaA formRDefault (3 : F) dotOp2C dotOp2Sf2 8 3 algebraMap_three

theorem sem9_bridge :
    bridge F K alphaA formRDefault sem9 =
      encRecFormR ⟨encC seedZ dotOp9Formula, encC seedZ dotOp9Tail, 3, alphaA ^ 9⟩ formRDefault :=
  semOf_bridge seedZ alphaA formRDefault (3 : F) dotOp9Formula dotOp9Tail 9 3 algebraMap_three

theorem sem10_bridge :
    bridge F K alphaA formRDefault sem10 =
      encRecFormR ⟨encC seedZ dotOp9Tail, encC seedZ (.atom 2), 2, alphaA ^ 10⟩ formRDefault :=
  semOf_bridge seedZ alphaA formRDefault (2 : F) dotOp9Tail (.atom 2) 10 2 algebraMap_two

theorem sem11_bridge :
    bridge F K alphaA formRDefault sem11 =
      encRecFormR ⟨encC seedZ dotCore, encC seedZ dotArm, 2, alphaA ^ 11⟩ formRDefault :=
  semOf_bridge seedZ alphaA formRDefault (2 : F) dotCore dotArm 11 2 algebraMap_two

theorem sem12_bridge :
    bridge F K alphaA formRDefault sem12 =
      encRecFormR ⟨encC seedZ dotCoreFormula, encC seedZ dotCore, 3, alphaA ^ 12⟩ formRDefault :=
  semOf_bridge seedZ alphaA formRDefault (3 : F) dotCoreFormula dotCore 12 3 algebraMap_three

theorem sem13_bridge :
    bridge F K alphaA formRDefault sem13 =
      encRecFormR ⟨encC seedZ dotArm, encC seedZ dotResult, 3, alphaA ^ 13⟩ formRDefault :=
  semOf_bridge seedZ alphaA formRDefault (3 : F) dotArm dotResult 13 3 algebraMap_three

theorem requests_bridge :
    bridgeRecords F K (cfg seedZ alphaA).challenges.α (cfg seedZ alphaA).challenges.lam semanticRequestList =
      (execThreaded seedZ alphaA).derivedRequestIO := by
  change bridgeRecords F K alphaA formRDefault semanticRequestList =
    (execThreaded seedZ alphaA).derivedRequestIO
  rw [bridgeRecords, semanticRequestList, List.map_cons, List.map_cons, List.map_cons,
    List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
    List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
    List.map_nil, sem1_bridge, sem2_bridge, sem3_bridge, sem4_bridge, sem5_bridge,
    sem6_bridge, sem7_bridge, sem8_bridge, sem9_bridge, sem10_bridge, sem11_bridge,
    sem12_bridge, sem13_bridge, derived_requests]

theorem semanticRequests_nodup : semanticRequestList.Nodup := by
  simp [semanticRequestList, sem1, sem2, sem3, sem4, sem5, sem6, sem7, sem8,
    sem9, sem10, sem11, sem12, sem13, semOf]

theorem semanticResponses_nodup : semanticResponseList.Nodup := by
  simp [semanticResponseList, sem1, sem2, sem3, sem4, sem5, sem6, sem7, sem8,
    sem9, sem10, sem11, sem12, sem13, semOf]

theorem semantic_mem_iff (x : (nmrMEF F K).Rec) :
    x ∈ semanticRequestList ↔ x ∈ semanticResponseList := by
  simp only [semanticRequestList, semanticResponseList, List.mem_cons, List.not_mem_nil, or_false]
  constructor <;> intro h <;>
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]

theorem semantic_lmio :
    IO.LmIO (cfg seedZ alphaA).Ksz semanticRequestList semanticResponseList := by
  refine ⟨⟨by decide, by decide⟩, semanticResponseList, by decide,
    semanticResponses_nodup, semantic_mem_iff, List.Perm.refl _⟩

/-- The a-bearing view's raw responses (row-level memory: the executed `execThreaded` carries
    `(T, C')` instead of the axis; see `derivedResponseIO_threaded`). -/
theorem execThreadedA_rawResponses (z α : K) :
    (execThreadedA z α).rawResponses =
      servedGen (assignedForest z α) := by
  rw [ExactExecution.rawResponses_eq_memoryRows]
  unfold ExactExecution.memoryRows servedGen
  change ((bfsForest (memoryForestThreaded z α)).map NTree.label).flatMap
      (fun row => responseRecords row.2.2) = _
  unfold memoryForestThreaded
  rw [bfsForest_mapNTree, List.map_map]
  have hcomp :
      NTree.label ∘ mapNTree (fun g : GenMemoryRow K => g.row) =
        (fun g : GenMemoryRow K => g.row) ∘ NTree.label := by
    funext n
    simp [Function.comp, mapNTree_label]
  rw [hcomp, ← List.map_map]
  unfold threadedForest
  rw [threadGenForest_bfs_labels, List.flatMap_map]
  have hflat := threadGenRows_flatMap_responseRecords (memInputs z) 0
    ((bfsForest (assignedForest z α)).map NTree.label)
  rw [hflat, List.flatMap_map]


theorem assigned_bfs_ver (z α : K) :
    ∀ t ∈ bfsForest (assignedForest z α),
      t.label.row.2.2.ver = decide (t.label.row.2.2.st = .read_root) := by
  intro t ht
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ t).mp ht
  have hOK := assignedMemForest_OK_air z α u hu
      (mapNTree GenMemoryRow.node t) (mapNTree_inTree _ hin)
  have hb := hOK.2.2.1
  have hsteq : t.label.skel.state = t.label.row.2.2.st := by
    simpa [mapNTree_label, GenMemoryRow.node_skel, GenMemoryRow.node_row] using
      hb.2.2.1.symm
  have hv : t.label.row.2.2.ver = decide (t.label.skel.state = .read_root) := by
    simpa [mapNTree_label, GenMemoryRow.node_skel, GenMemoryRow.node_row] using
      hb.2.2.2.2.2.2
  rw [hv, hsteq]

theorem threadGenRows_ver_honest (inp : MemoryTable.Inputs K) :
    ∀ acc gs, (∀ g ∈ gs, g.row.2.2.ver = decide (g.row.2.2.st = .read_root)) →
      ∀ g ∈ threadGenRows inp acc gs,
        g.row.2.2.ver = decide (g.row.2.2.st = .read_root)
  | _, [] => by intro _ g hg; cases hg
  | acc, q :: qs => by
      intro hall g hg
      simp only [threadGenRows_cons, List.mem_cons] at hg
      rcases hg with rfl | hg
      · have := hall q (List.mem_cons.mpr (Or.inl rfl))
        rw [threadGenRow_snd]
        exact this
      · exact threadGenRows_ver_honest inp (threadGenRow inp acc q).1 qs
          (fun r hr => hall r (List.mem_cons_of_mem _ hr)) g hg

theorem threaded_bfs_ver (z α : K) :
    ∀ t ∈ bfsForest (threadedForest z α),
      t.label.row.2.2.ver = decide (t.label.row.2.2.st = .read_root) := by
  intro t ht
  have hlab : t.label ∈ (bfsForest (threadedForest z α)).map NTree.label :=
    List.mem_map.mpr ⟨t, ht, rfl⟩
  unfold threadedForest at hlab
  rw [threadGenForest_bfs_labels] at hlab
  exact threadGenRows_ver_honest (memInputs z) 0 _
    (fun g hg => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      exact assigned_bfs_ver z α u hu)
    t.label hlab

/-- Row-level memory: the executed responses are the single Form R encode of the a-bearing
    responses. -/
theorem derivedResponseIO_threaded (z α : K) :
    (execThreaded z α).derivedResponseIO =
      (execThreadedA z α).rawResponses.map
        (fun r => NockVM.encRecFormR r MemoryTable.formRDefault) := by
  unfold ExactExecution.derivedResponseIO ExactExecution.rawResponses
  rw [memoryRows_eq_threaded, memoryRowsA_eq_threaded, List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr ?_
  intro x hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  have hst := threaded_bfs_state z α t ht
  have hv := threaded_bfs_ver z α t ht
  have hpub := encodeRow_pub (lmb := MemoryTable.formRDefault) t.label.row hst
  simp only [Function.comp, hpub]
  by_cases hver : t.label.row.2.2.ver = true
  · have hread : t.label.row.2.2.st = .read_root := by
      rw [hver] at hv
      exact of_decide_eq_true hv.symm
    have hact : memoryMemRecKind t.label.row.2.2.st = .active := by rw [hread]; rfl
    simp [responseRecords, hver, encPub_ver, encPub_mem_active _ hact,
      encPub_cprime_active _ hact]
  · simp [responseRecords, hver, encPub_ver]

theorem genAnnotatedRecordTree_root_mem
    (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (axis recordExp : ℕ) :
    (genAnnotatedRecordTree E z α lmb root child axis recordExp).label.row.2.2.st =
        .read_root ∧
      (genAnnotatedRecordTree E z α lmb root child axis recordExp).label.row.2.2.mem =
        ⟨E root, E child, (axis : K), α ^ recordExp⟩ ∧
      (genAnnotatedRecordTree E z α lmb root child axis recordExp).label.row.2.2.ver = true := by
  simp only [genAnnotatedRecordTree, NTree.label]
  refine ⟨?_, ?_, ?_⟩
  · rw [gMemRow9_st, annotatedReadPub_st]
  · rw [gMemRow9_mem, annotatedReadPub_mem]
  · simp [gMemRow9, annotatedReadPub]

theorem genAnnotatedChainedTree_pair_root_mem
    (E : Noun → ComputeTable.FP K) (z α : K)
    (r restHead : MemRecordReq) (restTail : List MemRecordReq)
    (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z α lmb (r :: restHead :: restTail) = some t) :
    t.label.row.2.2.st = .read_root ∧
      t.label.row.2.2.mem =
        ⟨E r.root, E r.child, (r.axis : K), α ^ r.recordExp⟩ ∧
      t.label.row.2.2.ver = true := by
  simp only [genAnnotatedChainedTree] at ht
  injection ht with ht
  subst t
  simp only [NTree.label]
  refine ⟨?_, ?_, ?_⟩
  · rw [gMemRow9_st, annotatedReadPub_st]
  · rw [gMemRow9_mem, annotatedReadPub_mem]
  · simp [gMemRow9, annotatedReadPub]

theorem responseRecords_of_read_mem (pub : MemoryTable.Pub K)
    (h : pub.st = .read_root) (hver : pub.ver = true) :
    responseRecords pub = [pub.mem] :=
  responseRecords_eq_singleton_of_read_root pub h hver

theorem responseRecords_of_not_read (pub : MemoryTable.Pub K)
    (h : pub.st ≠ .read_root) (hver : pub.ver = false) :
    responseRecords pub = [] :=
  responseRecords_eq_nil_of_ne_read pub h hver

theorem served_root_read (t : NTree (GenMemoryRow K))
    (h : t.label.row.2.2.st = .read_root) (hver : t.label.row.2.2.ver = true) :
    responseRecords t.label.row.2.2 = [t.label.row.2.2.mem] :=
  responseRecords_of_read_mem _ h hver

theorem servedGen_fibre_zero (forest : List (NTree (GenMemoryRow K)))
    (h : forestFibre (.read_root : MemoryTable.MState) forest = 0)
    (hver : ∀ t ∈ bfsForest forest, t.label.row.2.2.ver = false) :
    servedGen forest = [] := by
  have hnil : ∀ t ∈ bfsForest forest, responseRecords t.label.row.2.2 = [] := by
    intro t ht
    have hst : t.label.row.2.2.st ≠ .read_root := by
      intro hst
      have hcount := fibreCount_bfsForest (.read_root : MemoryTable.MState) forest
      rw [h] at hcount
      have hpos :
          0 < fibreCount memPubSt ((bfsForest forest).map NTree.label)
            (.read_root : MemoryTable.MState) := by
        unfold fibreCount
        refine List.countP_pos_iff.mpr ⟨t.label, List.mem_map.mpr ⟨t, ht, rfl⟩, ?_⟩
        simp [memPubSt, hst]
      omega
    exact responseRecords_of_not_read _ hst (hver t ht)
  unfold servedGen
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  obtain ⟨t, ht, hx'⟩ := List.mem_flatMap.mp hx
  rw [hnil t ht] at hx'
  cases hx'


theorem servedGen_recordTree (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (axis recordExp : ℕ) :
    servedGen [genAnnotatedRecordTree E z α lmb root child axis recordExp] =
      [⟨E root, E child, (axis : K), α ^ recordExp⟩] := by
  have hne :
      ([genAnnotatedRecordTree E z α lmb root child axis recordExp] :
        List (NTree (GenMemoryRow K))) ≠ [] :=
    List.cons_ne_nil _ _
  rw [servedGen_of_ne_nil _ hne]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append]
  have hroot := genAnnotatedRecordTree_root_mem (lmb := lmb) E z α root child axis recordExp
  rw [served_root_read _ hroot.1 hroot.2.2, hroot.2.1]
  have hch :
      forestFibre (.read_root : MemoryTable.MState)
        (genAnnotatedRecordTree E z α lmb root child axis recordExp).children = 0 := by
    have hf := genAnnotatedRecordTree_fibre (lmb := lmb) E z α root child axis recordExp
    unfold genAnnotatedRecordTree at hf ⊢
    simp [treeFibre_gMemRow9, annotatedReadPub_st] at hf ⊢
    omega
  have hchVer :
      ∀ t ∈ bfsForest (genAnnotatedRecordTree E z α lmb root child axis recordExp).children,
        t.label.row.2.2.ver = false :=
    genAnnotatedRecordTree_children_bfs_ver_false E z α root child axis recordExp
  rw [servedGen_fibre_zero _ hch hchVer]
  rfl

theorem servedGen_skip_roots (l : List (NTree (GenMemoryRow K))) (hl : l ≠ [])
    (h : ∀ t ∈ l, t.label.row.2.2.st ≠ .read_root)
    (hver : ∀ t ∈ l, t.label.row.2.2.ver = false) :
    servedGen l = servedGen (l.flatMap NTree.children) := by
  rw [servedGen_of_ne_nil l hl]
  have : l.flatMap (fun t => responseRecords t.label.row.2.2) = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro x hx
    obtain ⟨t, ht, hx'⟩ := List.mem_flatMap.mp hx
    rw [responseRecords_of_not_read _ (h t ht) (hver t ht)] at hx'
    cases hx'
  rw [this, List.nil_append]


theorem semanticRequest_timestamps :
    ∀ r ∈ semanticRequestList, r.2.2 < 14 := by
  intro r hr
  simp only [semanticRequestList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    <;> simp [sem1, sem2, sem3, sem4, sem5, sem6, sem7, sem8, sem9, sem10,
      sem11, sem12, sem13, semOf]

theorem semanticRequest_determines :
    ∀ x ∈ semanticRequestList, ∀ y ∈ semanticRequestList, x.2.2 = y.2.2 → x = y := by
  intro x hx y hy h
  simp only [semanticRequestList, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | (exfalso
       simp [sem1, sem2, sem3, sem4, sem5, sem6, sem7, sem8, sem9, sem10,
         sem11, sem12, sem13, semOf] at h
       done)
    | rfl

theorem semanticResponse_timestamps :
    ∀ r ∈ semanticResponseList, r.2.2 < 14 := by
  intro r hr
  simp only [semanticResponseList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    <;> simp [sem1, sem2, sem3, sem4, sem5, sem6, sem7, sem8, sem9, sem10,
      sem11, sem12, sem13, semOf]

theorem timestampBound_le_order_seed :
    14 ≤ orderOf (cfg seedZ alphaA).challenges.α := by
  change 14 ≤ orderOf alphaA
  exact alphaA_order_ge_14

theorem assignedForest_eq (z α : K) :
    ∃ t12 t45 t910,
      assignedForest z α =
        [t12,
         genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotBranchPair dotThenFormula 2 3,
         t45,
         genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotOp2B dotOp2Sf1 3 7,
         genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotOp2C dotOp2Sf2 3 8,
         t910,
         genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotCore dotArm 2 11,
         genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotCoreFormula dotCore 3 12,
         genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotArm dotResult 3 13,
         genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotCondFormula dotCondResult 3 6] ∧
      genAnnotatedChainedTree (encC z) z α MemoryTable.formRDefault
        [⟨dotFormula, dotParentTail, 3, 1⟩,
         ⟨dotParentTail, dotCondFormula, 2, 2⟩] = some t12 ∧
      genAnnotatedChainedTree (encC z) z α MemoryTable.formRDefault
        [⟨dotThenFormula, dotThenTail, 3, 4⟩,
         ⟨dotThenTail, dotOp2B, 2, 5⟩] = some t45 ∧
      genAnnotatedChainedTree (encC z) z α MemoryTable.formRDefault
        [⟨dotOp9Formula, dotOp9Tail, 3, 9⟩,
         ⟨dotOp9Tail, .atom 2, 2, 10⟩] = some t910 := by
  have hexp := liveRecordExps_air_named (K := K)
  unfold assignedForest
  rw [bfsAssign_air_eq_node, genMemForestFromTree_node, bfsAssign_air_children]
  rw [genMemForestFromList_cons, genMemForestFromList_cons, genMemForestFromList_nil]
  rw [extractNodeReqs_air_root, bfsAssign_label]
  simp only [dotFormula, dotParentTail, dotBranchPair]
  simp [hexp]
  obtain ⟨t12, hroot, h12⟩ :=
    genRowMemForest_three_chain32_head (encC z) z α
      (.atom 6) dotCondFormula dotBranchPair dotThenFormula dotElseFormula 1 2 3
  simp only [dotBranchPair] at hroot h12
  rw [hroot]
  rw [genMemForestFromTree_as_node, genMemForestFromTree_as_node]
  rw [airBuild_2_children]
  rw [genMemForestFromList_cons, genMemForestFromList_cons, genMemForestFromList_cons,
    genMemForestFromList_nil]
  rw [airBuild_label, extractNodeReqs_bfsLabelAt_air_op2]
  simp only [dotThenFormula, dotThenTail]
  simp [hexp]
  obtain ⟨t45, hop2, h45⟩ :=
    genRowMemForest_chain32_head (encC z) z α (.atom 2) dotOp2B dotOp2C 4 5
  rw [hop2]
  rw [genMemForestFromTree_as_node, genMemForestFromTree_as_node,
    genMemForestFromTree_as_node]
  rw [airBuild_4_children, airBuild_5_children]
  simp only [genMemForestFromList_nil, List.append_nil]
  rw [airBuild_label, extractNodeReqs_bfsLabelAt_air_op1b, genRowMemForest_singleton]
  rw [airBuild_label, extractNodeReqs_bfsLabelAt_air_op1c, genRowMemForest_singleton]
  simp [hexp]
  rw [airBuild_6_children]
  rw [genMemForestFromList_cons, genMemForestFromList_cons, genMemForestFromList_nil]
  rw [airBuild_label, extractNodeReqs_bfsLabelAt_air_op9]
  simp only [dotOp9Formula, dotOp9Tail, dotCore, dotArm]
  simp [hexp]
  obtain ⟨t910, hop9, h910⟩ :=
    genRowMemForest_three_chain32_head (encC z) z α
      (.atom 9) (.atom 2) dotCoreFormula dotElem0 dotElem1 9 10 11
  rw [hop9]
  rw [genMemForestFromTree_as_node, genMemForestFromTree_as_node]
  rw [airBuild_7_children, airBuild_8_children]
  simp only [genMemForestFromList_nil, List.append_nil]
  rw [airBuild_label, extractNodeReqs_bfsLabelAt_air_core, genRowMemForest_singleton]
  rw [airBuild_label, extractNodeReqs_bfsLabelAt_air_invoke, genRowMemForest_singleton]
  simp [hexp]
  rw [airBuild_3_children, genMemForestFromList_nil, List.append_nil]
  rw [airBuild_label, extractNodeReqs_bfsLabelAt_air_cond, genRowMemForest_singleton]
  simp [hexp]
  simp only [dotThenFormula, dotThenTail, dotCore, dotArm] at h12 h45 h910
  simp [h12, h45, h910, dotCore, dotArm]



theorem servedGen_assignedForest (z α : K) :
    servedGen (assignedForest z α) =
      [recOf z α dotFormula dotParentTail 3 1,
       recOf z α dotBranchPair dotThenFormula 2 3,
       recOf z α dotThenFormula dotThenTail 3 4,
       recOf z α dotOp2B dotOp2Sf1 3 7,
       recOf z α dotOp2C dotOp2Sf2 3 8,
       recOf z α dotOp9Formula dotOp9Tail 3 9,
       recOf z α dotCore dotArm 2 11,
       recOf z α dotCoreFormula dotCore 3 12,
       recOf z α dotArm dotResult 3 13,
       recOf z α dotCondFormula dotCondResult 3 6,
       recOf z α dotParentTail dotCondFormula 2 2,
       recOf z α dotThenTail dotOp2B 2 5,
       recOf z α dotOp9Tail (.atom 2) 2 10] := by
  obtain ⟨t12, t45, t910, hF, h12, h45, h910⟩ := assignedForest_eq z α
  have h12' :
      genAnnotatedChainedTree (encC z) z α MemoryTable.formRDefault
        [⟨.cell (.atom 6) (.cell dotCondFormula dotBranchPair),
          .cell dotCondFormula dotBranchPair, 3, 1⟩,
         ⟨.cell dotCondFormula dotBranchPair, dotCondFormula, 2, 2⟩] = some t12 := by
    simpa [dotFormula, dotParentTail] using h12
  have h45' :
      genAnnotatedChainedTree (encC z) z α MemoryTable.formRDefault
        [⟨.cell (.atom 2) (.cell dotOp2B dotOp2C), .cell dotOp2B dotOp2C, 3, 4⟩,
         ⟨.cell dotOp2B dotOp2C, dotOp2B, 2, 5⟩] = some t45 := by
    simpa [dotThenFormula, dotThenTail] using h45
  have h910' :
      genAnnotatedChainedTree (encC z) z α MemoryTable.formRDefault
        [⟨.cell (.atom 9) (.cell (.atom 2) dotCoreFormula),
          .cell (.atom 2) dotCoreFormula, 3, 9⟩,
         ⟨.cell (.atom 2) dotCoreFormula, .atom 2, 2, 10⟩] = some t910 := by
    simpa [dotOp9Formula, dotOp9Tail] using h910
  obtain ⟨dec12, walk12, inner12, hch12, hdec12, hdecver12, hL2_12, hwalk12, hwalkver12, hwalkAll12, hwalkf12, hinr12, hinrver12, hmem12, hf12, hinnerChVer12⟩ :=
    genAnnotatedChainedTree_axis3_axis2_shape (encC z) z α
      (.atom 6) dotCondFormula dotBranchPair 1 2 t12 h12'
  obtain ⟨dec45, walk45, inner45, hch45, hdec45, hdecver45, hL2_45, hwalk45, hwalkver45, hwalkAll45, hwalkf45, hinr45, hinrver45, hmem45, hf45, hinnerChVer45⟩ :=
    genAnnotatedChainedTree_axis3_axis2_shape (encC z) z α
      (.atom 2) dotOp2B dotOp2C 4 5 t45 h45'
  obtain ⟨dec910, walk910, inner910, hch910, hdec910, hdecver910, hL2_910, hwalk910, hwalkver910, hwalkAll910, hwalkf910, hinr910, hinrver910, hmem910, hf910, hinnerChVer910⟩ :=
    genAnnotatedChainedTree_axis3_axis2_shape (encC z) z α
      (.atom 9) (.atom 2) dotCoreFormula 9 10 t910 h910'
  obtain ⟨dec3, hch3, hdec3, hdecver3, hnr3, hnrver3, hf3⟩ :=
    genAnnotatedRecordTree_axis2_shape (encC z) z α dotThenFormula dotElseFormula 3
  obtain ⟨dec6, hch6, hdec6, hdecver6, hnr6, hnrver6, hf6⟩ :=
    genAnnotatedRecordTree_axis3_shape (encC z) z α (.atom 1) (.atom 0) 6
  obtain ⟨dec7, hch7, hdec7, hdecver7, hnr7, hnrver7, hf7⟩ :=
    genAnnotatedRecordTree_axis3_shape (encC z) z α (.atom 1) (.cell (.atom 0) (.atom 1)) 7
  obtain ⟨dec8, hch8, hdec8, hdecver8, hnr8, hnrver8, hf8⟩ :=
    genAnnotatedRecordTree_axis3_shape (encC z) z α (.atom 1) dotOp9Formula 8
  obtain ⟨dec11, hch11, hdec11, hdecver11, hnr11, hnrver11, hf11⟩ :=
    genAnnotatedRecordTree_axis2_shape (encC z) z α dotArm dotElem1 11
  obtain ⟨dec12r, hch12r, hdec12r, hdecver12r, hnr12r, hnrver12r, hf12r⟩ :=
    genAnnotatedRecordTree_axis3_shape (encC z) z α (.atom 1) dotCore 12
  obtain ⟨dec13, hch13, hdec13, hdecver13, hnr13, hnrver13, hf13⟩ :=
    genAnnotatedRecordTree_axis3_shape (encC z) z α (.atom 1) (.atom 3) 13
  have hch3' :
      (genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotBranchPair dotThenFormula 2 3).children =
        [dec3] := by
    simpa [dotBranchPair] using hch3
  have hch6' :
      (genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotCondFormula dotCondResult 3 6).children =
        [dec6] := by
    simpa [dotCondFormula, dotCondResult] using hch6
  have hch7' :
      (genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotOp2B dotOp2Sf1 3 7).children =
        [dec7] := by
    simpa [dotOp2B, dotOp2Sf1] using hch7
  have hch8' :
      (genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotOp2C dotOp2Sf2 3 8).children =
        [dec8] := by
    simpa [dotOp2C, dotOp2Sf2] using hch8
  have hch11' :
      (genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotCore dotArm 2 11).children =
        [dec11] := by
    simpa [dotCore, dotArm] using hch11
  have hch12r' :
      (genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotCoreFormula dotCore 3 12).children =
        [dec12r] := by
    simpa [dotCoreFormula] using hch12r
  have hch13' :
      (genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotArm dotResult 3 13).children =
        [dec13] := by
    simpa [dotArm, dotElem0, dotResult] using hch13
  have hroot12 :=
    genAnnotatedChainedTree_pair_root_mem (encC z) z α _ _ [] t12 h12'
  have hroot45 :=
    genAnnotatedChainedTree_pair_root_mem (encC z) z α _ _ [] t45 h45'
  have hroot910 :=
    genAnnotatedChainedTree_pair_root_mem (encC z) z α _ _ [] t910 h910'
  have hroot3 := genAnnotatedRecordTree_root_mem (lmb := MemoryTable.formRDefault) (encC z) z α
    dotBranchPair dotThenFormula 2 3
  have hroot6 := genAnnotatedRecordTree_root_mem (lmb := MemoryTable.formRDefault) (encC z) z α
    dotCondFormula dotCondResult 3 6
  have hroot7 := genAnnotatedRecordTree_root_mem (lmb := MemoryTable.formRDefault) (encC z) z α
    dotOp2B dotOp2Sf1 3 7
  have hroot8 := genAnnotatedRecordTree_root_mem (lmb := MemoryTable.formRDefault) (encC z) z α
    dotOp2C dotOp2Sf2 3 8
  have hroot11 := genAnnotatedRecordTree_root_mem (lmb := MemoryTable.formRDefault) (encC z) z α
    dotCore dotArm 2 11
  have hroot12r := genAnnotatedRecordTree_root_mem (lmb := MemoryTable.formRDefault) (encC z) z α
    dotCoreFormula dotCore 3 12
  have hroot13 := genAnnotatedRecordTree_root_mem (lmb := MemoryTable.formRDefault) (encC z) z α
    dotArm dotResult 3 13
  rw [hF]
  have hreads :
      ∀ t ∈ ([t12,
          genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotBranchPair dotThenFormula 2 3,
          t45,
          genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotOp2B dotOp2Sf1 3 7,
          genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotOp2C dotOp2Sf2 3 8,
          t910,
          genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotCore dotArm 2 11,
          genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotCoreFormula dotCore 3 12,
          genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotArm dotResult 3 13,
          genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotCondFormula dotCondResult 3 6] :
        List (NTree (GenMemoryRow K))),
        t.label.row.2.2.st = .read_root := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hroot12.1
    · exact hroot3.1
    · exact hroot45.1
    · exact hroot7.1
    · exact hroot8.1
    · exact hroot910.1
    · exact hroot11.1
    · exact hroot12r.1
    · exact hroot13.1
    · exact hroot6.1
  have hreadsVer :
      ∀ t ∈ ([t12,
          genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotBranchPair dotThenFormula 2 3,
          t45,
          genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotOp2B dotOp2Sf1 3 7,
          genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotOp2C dotOp2Sf2 3 8,
          t910,
          genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotCore dotArm 2 11,
          genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotCoreFormula dotCore 3 12,
          genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotArm dotResult 3 13,
          genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault dotCondFormula dotCondResult 3 6] :
        List (NTree (GenMemoryRow K))),
        t.label.row.2.2.ver = true := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hroot12.2.2
    · exact hroot3.2.2
    · exact hroot45.2.2
    · exact hroot7.2.2
    · exact hroot8.2.2
    · exact hroot910.2.2
    · exact hroot11.2.2
    · exact hroot12r.2.2
    · exact hroot13.2.2
    · exact hroot6.2.2
  rw [servedGen_reads_prefix _ (List.cons_ne_nil _ _) hreads hreadsVer]
  simp only [List.map_cons, List.map_nil]
  rw [hroot12.2.1, hroot3.2.1, hroot45.2.1, hroot7.2.1, hroot8.2.1, hroot910.2.1,
    hroot11.2.1, hroot12r.2.1, hroot13.2.1, hroot6.2.1]
  simp only [List.flatMap_cons, List.flatMap_nil, hch12, hch3', hch45, hch7',
    hch8', hch910, hch11', hch12r', hch13', hch6', List.cons_append, List.nil_append]
  have hL1ne :
      ([dec12, dec3, dec45, dec7, dec8, dec910, dec11, dec12r, dec13, dec6] :
        List (NTree (GenMemoryRow K))) ≠ [] :=
    List.cons_ne_nil _ _
  have hL1 :
      ∀ t ∈ ([dec12, dec3, dec45, dec7, dec8, dec910, dec11, dec12r, dec13, dec6] :
        List (NTree (GenMemoryRow K))),
        t.label.row.2.2.st ≠ .read_root := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hdec12]; simp
    · rw [hdec3]; simp
    · rw [hdec45]; simp
    · rw [hdec7]; simp
    · rw [hdec8]; simp
    · rw [hdec910]; simp
    · rw [hdec11]; simp
    · rw [hdec12r]; simp
    · rw [hdec13]; simp
    · rw [hdec6]; simp
  have hL1ver :
      ∀ t ∈ ([dec12, dec3, dec45, dec7, dec8, dec910, dec11, dec12r, dec13, dec6] :
        List (NTree (GenMemoryRow K))),
        t.label.row.2.2.ver = false := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hdecver12
    · exact hdecver3
    · exact hdecver45
    · exact hdecver7
    · exact hdecver8
    · exact hdecver910
    · exact hdecver11
    · exact hdecver12r
    · exact hdecver13
    · exact hdecver6
  rw [servedGen_skip_roots _ hL1ne hL1 hL1ver]
  simp only [List.flatMap_cons, List.flatMap_nil, hL2_12, hL2_45, hL2_910]
  simp only [List.append_nil, ← List.append_assoc]
  have hL2ne :
      ([walk12, inner12] ++ dec3.children ++
        [walk45, inner45] ++ dec7.children ++ dec8.children ++
        [walk910, inner910] ++ dec11.children ++ dec12r.children ++
        dec13.children ++ dec6.children) ≠ [] := by
    simp
  rw [servedGen_of_ne_nil _ hL2ne]
  have hflat :
      ([walk12, inner12] ++ dec3.children ++
        [walk45, inner45] ++ dec7.children ++ dec8.children ++
        [walk910, inner910] ++ dec11.children ++ dec12r.children ++
        dec13.children ++ dec6.children).flatMap
          (fun t => responseRecords t.label.row.2.2) =
        [inner12.label.row.2.2.mem, inner45.label.row.2.2.mem,
          inner910.label.row.2.2.mem] := by
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil]
    rw [responseRecords_eq_nil_of_ne_read _ hwalk12 hwalkver12,
      responseRecords_eq_singleton_of_read_root _ hinr12 hinrver12]
    rw [responseRecords_flatMap_not_read _ hnr3 (fun t ht => hnrver3 t ht t (InTree.here _))]
    rw [responseRecords_eq_nil_of_ne_read _ hwalk45 hwalkver45,
      responseRecords_eq_singleton_of_read_root _ hinr45 hinrver45]
    rw [responseRecords_flatMap_not_read _ hnr7 (fun t ht => hnrver7 t ht t (InTree.here _)),
      responseRecords_flatMap_not_read _ hnr8 (fun t ht => hnrver8 t ht t (InTree.here _))]
    rw [responseRecords_eq_nil_of_ne_read _ hwalk910 hwalkver910,
      responseRecords_eq_singleton_of_read_root _ hinr910 hinrver910]
    rw [responseRecords_flatMap_not_read _ hnr11 (fun t ht => hnrver11 t ht t (InTree.here _)),
      responseRecords_flatMap_not_read _ hnr12r (fun t ht => hnrver12r t ht t (InTree.here _)),
      responseRecords_flatMap_not_read _ hnr13 (fun t ht => hnrver13 t ht t (InTree.here _)),
      responseRecords_flatMap_not_read _ hnr6 (fun t ht => hnrver6 t ht t (InTree.here _))]
    simp
  rw [hflat, hmem12, hmem45, hmem910]
  have hL3 :
      forestFibre (.read_root : MemoryTable.MState)
        (([walk12, inner12] ++ dec3.children ++
          [walk45, inner45] ++ dec7.children ++ dec8.children ++
          [walk910, inner910] ++ dec11.children ++ dec12r.children ++
          dec13.children ++ dec6.children).flatMap NTree.children) = 0 := by
    rw [forestFibre_flatMap_append, forestFibre_flatMap_append,
      forestFibre_flatMap_append, forestFibre_flatMap_append,
      forestFibre_flatMap_append, forestFibre_flatMap_append,
      forestFibre_flatMap_append, forestFibre_flatMap_append,
      forestFibre_flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [forestFibre_append, forestFibre_append, forestFibre_append]
    rw [treeFibre_zero_children _ hwalkf12, hf12]
    rw [forestFibre_children_of_zero _ hf3]
    rw [treeFibre_zero_children _ hwalkf45, hf45]
    rw [forestFibre_children_of_zero _ hf7, forestFibre_children_of_zero _ hf8]
    rw [treeFibre_zero_children _ hwalkf910, hf910]
    rw [forestFibre_children_of_zero _ hf11, forestFibre_children_of_zero _ hf12r,
      forestFibre_children_of_zero _ hf13, forestFibre_children_of_zero _ hf6]
  have hL3ver :
      ∀ t ∈ bfsForest
        (([walk12, inner12] ++ dec3.children ++
          [walk45, inner45] ++ dec7.children ++ dec8.children ++
          [walk910, inner910] ++ dec11.children ++ dec12r.children ++
          dec13.children ++ dec6.children).flatMap NTree.children),
        t.label.row.2.2.ver = false := by
    intro t ht
    obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp ht
    obtain ⟨parent, hp, hchild⟩ := List.mem_flatMap.mp hc
    have hp' :
        parent = walk12 ∨ parent = inner12 ∨ parent ∈ dec3.children ∨
          parent = walk45 ∨ parent = inner45 ∨ parent ∈ dec7.children ∨
          parent ∈ dec8.children ∨ parent = walk910 ∨ parent = inner910 ∨
          parent ∈ dec11.children ∨ parent ∈ dec12r.children ∨
          parent ∈ dec13.children ∨ parent ∈ dec6.children := by
      simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm]
        using hp
    rcases hp' with rfl | rfl | hp | rfl | rfl | hp | hp | rfl | rfl | hp | hp | hp | hp
    · exact hwalkAll12 t (InTree.sub hchild hin)
    · exact hinnerChVer12 t ((mem_bfsForest _ _).mpr ⟨c, hchild, hin⟩)
    · exact hnrver3 parent hp t (InTree.sub hchild hin)
    · exact hwalkAll45 t (InTree.sub hchild hin)
    · exact hinnerChVer45 t ((mem_bfsForest _ _).mpr ⟨c, hchild, hin⟩)
    · exact hnrver7 parent hp t (InTree.sub hchild hin)
    · exact hnrver8 parent hp t (InTree.sub hchild hin)
    · exact hwalkAll910 t (InTree.sub hchild hin)
    · exact hinnerChVer910 t ((mem_bfsForest _ _).mpr ⟨c, hchild, hin⟩)
    · exact hnrver11 parent hp t (InTree.sub hchild hin)
    · exact hnrver12r parent hp t (InTree.sub hchild hin)
    · exact hnrver13 parent hp t (InTree.sub hchild hin)
    · exact hnrver6 parent hp t (InTree.sub hchild hin)
  rw [servedGen_fibre_zero _ hL3 hL3ver]
  simp [recOf, dotFormula, dotParentTail, dotThenFormula, dotThenTail,
    dotOp9Formula, dotOp9Tail]

theorem derived_responses :
    (execThreaded seedZ alphaA).derivedResponseIO =
      [encRecFormR ⟨encC seedZ dotFormula, encC seedZ dotParentTail, 3, alphaA ^ 1⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotBranchPair, encC seedZ dotThenFormula, 2,
           alphaA ^ 3⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotThenFormula, encC seedZ dotThenTail, 3, alphaA ^ 4⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotOp2B, encC seedZ dotOp2Sf1, 3, alphaA ^ 7⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotOp2C, encC seedZ dotOp2Sf2, 3, alphaA ^ 8⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotOp9Formula, encC seedZ dotOp9Tail, 3, alphaA ^ 9⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotCore, encC seedZ dotArm, 2, alphaA ^ 11⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotCoreFormula, encC seedZ dotCore, 3, alphaA ^ 12⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotArm, encC seedZ dotResult, 3, alphaA ^ 13⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotCondFormula, encC seedZ dotCondResult, 3,
           alphaA ^ 6⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotParentTail, encC seedZ dotCondFormula, 2,
           alphaA ^ 2⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotThenTail, encC seedZ dotOp2B, 2, alphaA ^ 5⟩ formRDefault,
       encRecFormR ⟨encC seedZ dotOp9Tail, encC seedZ (.atom 2), 2, alphaA ^ 10⟩ formRDefault] := by
  rw [derivedResponseIO_threaded, execThreadedA_rawResponses,
    servedGen_assignedForest]
  simp [recOf]

theorem responses_bridge :
    bridgeRecords F K (cfg seedZ alphaA).challenges.α (cfg seedZ alphaA).challenges.lam semanticResponseList =
      (execThreaded seedZ alphaA).derivedResponseIO := by
  change bridgeRecords F K alphaA formRDefault semanticResponseList =
    (execThreaded seedZ alphaA).derivedResponseIO
  rw [bridgeRecords, semanticResponseList, List.map_cons, List.map_cons, List.map_cons,
    List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
    List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
    List.map_nil, sem1_bridge, sem3_bridge, sem4_bridge, sem7_bridge,
    sem8_bridge, sem9_bridge, sem11_bridge, sem12_bridge, sem13_bridge, sem6_bridge,
    sem2_bridge, sem5_bridge, sem10_bridge, derived_responses]

def semanticPreimage :
    SemanticIOPreimage (cfg seedZ alphaA) (execThreaded seedZ alphaA) where
  timestampBound := 14
  timestampBound_le_order := timestampBound_le_order_seed
  semanticRequests := semanticRequestList
  semanticResponses := semanticResponseList
  requestTimestampBound := semanticRequest_timestamps
  responseTimestampBound := semanticResponse_timestamps
  requestTimestamp_determines := semanticRequest_determines
  semantic_lmio := semantic_lmio
  requests_bridge := requests_bridge
  responses_bridge := responses_bridge

theorem semanticExactLanguage :
    SemanticExactLanguage (cfg seedZ alphaA) (execThreaded seedZ alphaA) :=
  ⟨computeRowsAccepted_threaded seedZ alphaA seedZ_ne_zero,
    memoryRowsAccepted_seed, ⟨semanticPreimage⟩⟩

theorem chained
    (hfirst : ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.counts = 0) :
    ChainedSemanticExactLanguage (cfg seedZ alphaA) (execThreaded seedZ alphaA) where
  semantic := semanticExactLanguage
  z_ne_zero := seedZ_ne_zero
  compute_wf := compute_wf_threaded seedZ alphaA
  memory_wf := memory_wf_seed
  compute_chain := compute_chain_threaded seedZ alphaA
  memory_chain := memory_chain seedZ alphaA
  memory_first_counts := memory_first_counts seedZ alphaA two_ne_zero hfirst
  memory_first_indicator := memory_first_indicator seedZ alphaA two_ne_zero hfirst
  memory_first_ipre := memory_first_ipre seedZ alphaA
  memory_last_icur := memory_last_icur seedZ alphaA

  memory_same_lambda :=
    ExactExecution.memory_same_lambda_of_const _ (some MemoryTable.formRDefault)
      (execThreaded_lambda? seedZ alphaA)

theorem requestNodup_threaded :
    (execThreaded seedZ alphaA).derivedRequestIO.Nodup := by
  rw [ExactExecution.derivedRequestIO, execThreaded_rawRequests]
  simpa [ExactExecution.derivedRequestIO] using requestNodup

theorem derivedResponseIO_length :
    (execThreaded seedZ alphaA).derivedResponseIO.length = 13 := by
  rw [derived_responses]
  rfl

theorem derivedRequestIO_length :
    (execThreaded seedZ alphaA).derivedRequestIO.length = 13 := by
  rw [derived_requests]
  rfl

theorem programIOCapacity_threaded :
    (execThreaded seedZ alphaA).derivedRequestIO.length + 1 ≤
      2 ^ (cfg seedZ alphaA).orbit.h := by
  rw [derivedRequestIO_length]
  simp [cfg, executionOrbit]

theorem memoryIOCapacity_threaded :
    (execThreaded seedZ alphaA).derivedResponseIO.length + 1 ≤
      2 ^ (cfg seedZ alphaA).orbit.h := by
  rw [derivedResponseIO_length]
  simp [cfg, executionOrbit]

end

end Nock.NockVMROM.Thm54.TraceGen.DotConfig769

#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.servedGen_assignedForest
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.derived_responses
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.responses_bridge
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.semanticExactLanguage
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.chained
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.requestNodup_threaded
