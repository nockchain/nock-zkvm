/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierASizeAir.lean

  Assigned-forest counts for the AIR-ordered Tier A tree `dotTreeAir`
  (children `[taken, condition]`).  Root count 10 and total size 184 are
  the same as the DFS `dotTree` forest: `++` is commutative on length
  and `totalSize`.  `Gen.lean` is not edited.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierASize
import Nock.NockVMROM.Thm54.TraceGen.GenTierAComputeLink

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## AIR `extractNodeReqs` -/

theorem bfsAssign_air_root_requests :
    (bfsAssign (dotTreeAir (K := K))).label.requests =
      (dotTreeAir (K := K)).label.requests := by
  rw [bfsAssign_label]
  have hi : 1 - 1 < (bfsRows (dotTreeAir (K := K))).length := by
    simp [dot_air_bfsRows]
  rw [bfsLabelAt_eq _ 1 hi]
  simp [dot_air_bfsRows]

theorem extractNodeReqs_air_root :
    extractNodeReqs (bfsAssign (dotTreeAir (K := K))).label =
      [⟨dotFormula, dotParentTail, 3,
          getRecordExp (bfsAssign (dotTreeAir (K := K))).label.stamp 0⟩,
       ⟨dotParentTail, dotCondFormula, 2,
          getRecordExp (bfsAssign (dotTreeAir (K := K))).label.stamp 1⟩,
       ⟨dotBranchPair, dotThenFormula, 2,
          getRecordExp (bfsAssign (dotTreeAir (K := K))).label.stamp 2⟩] := by
  rw [extractNodeReqs, bfsAssign_air_root_requests]
  simp [dotTreeAir, skelNode, extractNodeReqsAux_cons3]

theorem extractNodeReqs_bfsLabelAt_air_op2 :
    extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 2) =
      [⟨dotThenFormula, dotThenTail, 3,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 0⟩,
       ⟨dotThenTail, dotOp2B, 2,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 1⟩] := by
  have hi : 2 - 1 < (bfsRows (dotTreeAir (K := K))).length := by
    simp [dot_air_bfsRows]
  rw [extractNodeReqs, bfsLabelAt_requests (dotTreeAir (K := K)) 2 hi]
  have hget : (bfsRows (dotTreeAir (K := K)))[1] = (dotOp2Tree (K := K)).label := by
    simp [dot_air_bfsRows]
  rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 0 g.requests) hget]
  simp [dotOp2Tree, skelNode, extractNodeReqsAux_cons2]

theorem extractNodeReqs_bfsLabelAt_air_cond :
    extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 3) =
      [⟨dotCondFormula, dotCondResult, 3,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 3).stamp 0⟩] := by
  have hi : 3 - 1 < (bfsRows (dotTreeAir (K := K))).length := by
    simp [dot_air_bfsRows]
  rw [extractNodeReqs, bfsLabelAt_requests (dotTreeAir (K := K)) 3 hi]
  have hget : (bfsRows (dotTreeAir (K := K)))[2] = (dotCondTree (K := K)).label := by
    simp [dot_air_bfsRows]
  rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 3).stamp 0 g.requests) hget]
  simp [dotCondTree, skelNode, extractNodeReqsAux_cons1]

theorem extractNodeReqs_bfsLabelAt_air_op1b :
    extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 4) =
      [⟨dotOp2B, dotOp2Sf1, 3,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 4).stamp 0⟩] := by
  have hi : 4 - 1 < (bfsRows (dotTreeAir (K := K))).length := by
    simp [dot_air_bfsRows]
  rw [extractNodeReqs, bfsLabelAt_requests (dotTreeAir (K := K)) 4 hi]
  have hget : (bfsRows (dotTreeAir (K := K)))[3] = (dotOp1BTree (K := K)).label := by
    simp [dot_air_bfsRows]
  rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 4).stamp 0 g.requests) hget]
  simp [dotOp1BTree, skelNode, extractNodeReqsAux_cons1]

theorem extractNodeReqs_bfsLabelAt_air_op1c :
    extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 5) =
      [⟨dotOp2C, dotOp2Sf2, 3,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 5).stamp 0⟩] := by
  have hi : 5 - 1 < (bfsRows (dotTreeAir (K := K))).length := by
    simp [dot_air_bfsRows]
  rw [extractNodeReqs, bfsLabelAt_requests (dotTreeAir (K := K)) 5 hi]
  have hget : (bfsRows (dotTreeAir (K := K)))[4] = (dotOp1CTree (K := K)).label := by
    simp [dot_air_bfsRows]
  rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 5).stamp 0 g.requests) hget]
  simp [dotOp1CTree, skelNode, extractNodeReqsAux_cons1]

theorem extractNodeReqs_bfsLabelAt_air_op9 :
    extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 6) =
      [⟨dotOp9Formula, dotOp9Tail, 3,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 0⟩,
       ⟨dotOp9Tail, .atom 2, 2,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 1⟩,
       ⟨dotCore, dotArm, 2,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 2⟩] := by
  have hi : 6 - 1 < (bfsRows (dotTreeAir (K := K))).length := by
    simp [dot_air_bfsRows]
  rw [extractNodeReqs, bfsLabelAt_requests (dotTreeAir (K := K)) 6 hi]
  have hget : (bfsRows (dotTreeAir (K := K)))[5] = (dotOp9Tree (K := K)).label := by
    simp [dot_air_bfsRows]
  rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 0 g.requests) hget]
  simp [dotOp9Tree, skelNode, extractNodeReqsAux_cons3]

theorem extractNodeReqs_bfsLabelAt_air_core :
    extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 7) =
      [⟨dotCoreFormula, dotCore, 3,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 7).stamp 0⟩] := by
  have hi : 7 - 1 < (bfsRows (dotTreeAir (K := K))).length := by
    simp [dot_air_bfsRows]
  rw [extractNodeReqs, bfsLabelAt_requests (dotTreeAir (K := K)) 7 hi]
  have hget : (bfsRows (dotTreeAir (K := K)))[6] = (dotOp9CoreTree (K := K)).label := by
    simp [dot_air_bfsRows]
  rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 7).stamp 0 g.requests) hget]
  simp [dotOp9CoreTree, skelNode, extractNodeReqsAux_cons1]

theorem extractNodeReqs_bfsLabelAt_air_invoke :
    extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 8) =
      [⟨dotArm, dotResult, 3,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 8).stamp 0⟩] := by
  have hi : 8 - 1 < (bfsRows (dotTreeAir (K := K))).length := by
    simp [dot_air_bfsRows]
  rw [extractNodeReqs, bfsLabelAt_requests (dotTreeAir (K := K)) 8 hi]
  have hget : (bfsRows (dotTreeAir (K := K)))[7] = (dotOp9InvokeTree (K := K)).label := by
    simp [dot_air_bfsRows]
  rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 8).stamp 0 g.requests) hget]
  simp [dotOp9InvokeTree, skelNode, extractNodeReqsAux_cons1]

/-! ## AIR row-forest sizes -/

theorem genRowMemForest_air_root_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsAssign (dotTreeAir (K := K))).label)) = 86 := by
  rw [extractNodeReqs_air_root]
  simp [dotFormula, dotParentTail, dotBranchPair]
  rw [genRowMemForest_three_chain32_size]
  simp [nounWalkSize, nounWalkSize_dotCondFormula,
    nounWalkSize_dotThenFormula, nounWalkSize_dotElseFormula]

theorem genRowMemForest_air_root_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsAssign (dotTreeAir (K := K))).label)).length = 2 := by
  rw [extractNodeReqs_air_root]
  simp [dotFormula, dotParentTail, dotBranchPair]
  exact genRowMemForest_three_chain32_length (encC z) z α
    (.atom 6) dotCondFormula dotBranchPair dotThenFormula dotElseFormula
    _ _ _

theorem genRowMemForest_bfsLabelAt_air_cond_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 3))) = 5 := by
  rw [extractNodeReqs_bfsLabelAt_air_cond]
  simp [dotCondFormula, dotCondResult]
  rw [genRowMemForest_singleton_axis3_size]
  simp [nounWalkSize]

theorem genRowMemForest_bfsLabelAt_air_op1b_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 4))) = 7 := by
  rw [extractNodeReqs_bfsLabelAt_air_op1b]
  simp [dotOp2B, dotOp2Sf1]
  rw [genRowMemForest_singleton_axis3_size]
  simp [nounWalkSize]

theorem genRowMemForest_bfsLabelAt_air_op1c_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 5))) = 17 := by
  rw [extractNodeReqs_bfsLabelAt_air_op1c]
  simp [dotOp2C, dotOp2Sf2]
  rw [genRowMemForest_singleton_axis3_size]
  simp [nounWalkSize, nounWalkSize_dotOp9Formula]

theorem genRowMemForest_bfsLabelAt_air_core_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 7))) = 11 := by
  rw [extractNodeReqs_bfsLabelAt_air_core]
  simp [dotCoreFormula]
  rw [genRowMemForest_singleton_axis3_size]
  simp [nounWalkSize, nounWalkSize_dotCore]

theorem genRowMemForest_bfsLabelAt_air_invoke_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 8))) = 5 := by
  rw [extractNodeReqs_bfsLabelAt_air_invoke]
  simp [dotArm, dotElem0, dotResult]
  rw [genRowMemForest_singleton_axis3_size]
  simp [nounWalkSize]

theorem genRowMemForest_bfsLabelAt_air_op2_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 2))) = 27 := by
  rw [extractNodeReqs_bfsLabelAt_air_op2]
  simp [dotThenFormula, dotThenTail]
  rw [genRowMemForest_chain32_size]
  simp [nounWalkSize, nounWalkSize_dotOp2B, nounWalkSize_dotOp2C]

theorem genRowMemForest_bfsLabelAt_air_op9_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 6))) = 26 := by
  rw [extractNodeReqs_bfsLabelAt_air_op9]
  simp [dotOp9Formula, dotOp9Tail, dotCore, dotArm]
  rw [genRowMemForest_three_chain32_size]
  simp [nounWalkSize, nounWalkSize_dotCoreFormula, nounWalkSize_dotElem0,
    nounWalkSize_dotElem1]

theorem genRowMemForest_bfsLabelAt_air_cond_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 3))).length = 1 := by
  rw [extractNodeReqs_bfsLabelAt_air_cond, genRowMemForest_singleton]
  simp

theorem genRowMemForest_bfsLabelAt_air_op1b_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 4))).length = 1 := by
  rw [extractNodeReqs_bfsLabelAt_air_op1b, genRowMemForest_singleton]
  simp

theorem genRowMemForest_bfsLabelAt_air_op1c_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 5))).length = 1 := by
  rw [extractNodeReqs_bfsLabelAt_air_op1c, genRowMemForest_singleton]
  simp

theorem genRowMemForest_bfsLabelAt_air_core_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 7))).length = 1 := by
  rw [extractNodeReqs_bfsLabelAt_air_core, genRowMemForest_singleton]
  simp

theorem genRowMemForest_bfsLabelAt_air_invoke_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 8))).length = 1 := by
  rw [extractNodeReqs_bfsLabelAt_air_invoke, genRowMemForest_singleton]
  simp

theorem genRowMemForest_bfsLabelAt_air_op2_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 2))).length = 1 := by
  rw [extractNodeReqs_bfsLabelAt_air_op2]
  exact genRowMemForest_chain_length (encC z) z α _ _ rfl

theorem genRowMemForest_bfsLabelAt_air_op9_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTreeAir (K := K)) 6))).length = 2 := by
  rw [extractNodeReqs_bfsLabelAt_air_op9]
  simp [dotOp9Formula, dotOp9Tail, dotCore, dotArm]
  exact genRowMemForest_three_chain32_length (encC z) z α
    (.atom 9) (.atom 2) dotCoreFormula dotElem0 dotElem1 _ _ _

/-! ## AIR `airBuild` forests -/

theorem genMemForestFromTree_airBuild_leaf_length (z α : K) (i : ℕ)
    (hch : (airBuild (K := K) i).children = [])
    (r : MemRecordReq)
    (h : extractNodeReqs (airBuild (K := K) i).label = [r]) :
    (genMemForestFromTree (encC z) z α lmb (airBuild (K := K) i)).length = 1 := by
  rw [show airBuild (K := K) i = .node (airBuild (K := K) i).label
        (airBuild (K := K) i).children from by cases airBuild (K := K) i; rfl,
    hch, genMemForestFromTree_leaf, h, genRowMemForest_singleton]
  simp

theorem genMemForestFromTree_airBuild_leaf_size (z α : K) (i : ℕ)
    (hch : (airBuild (K := K) i).children = [])
    (hd tl : Noun) (e : ℕ)
    (h : extractNodeReqs (airBuild (K := K) i).label = [⟨.cell hd tl, tl, 3, e⟩]) :
    totalSize (genMemForestFromTree (encC z) z α lmb (airBuild (K := K) i)) =
      3 + nounWalkSize hd + nounWalkSize tl := by
  rw [show airBuild (K := K) i = .node (airBuild (K := K) i).label
        (airBuild (K := K) i).children from by cases airBuild (K := K) i; rfl,
    hch, genMemForestFromTree_leaf_axis3_size (encC z) z α _ hd tl e h]

theorem genMemForestFromTree_airBuild_3_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (airBuild (K := K) 3)).length = 1 := by
  have h : extractNodeReqs (airBuild (K := K) 3).label =
      [⟨dotCondFormula, dotCondResult, 3,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 3).stamp 0⟩] := by
    rw [airBuild_label, extractNodeReqs_bfsLabelAt_air_cond]
  exact genMemForestFromTree_airBuild_leaf_length z α 3 airBuild_3_children _ h

theorem genMemForestFromTree_airBuild_4_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (airBuild (K := K) 4)).length = 1 := by
  have h : extractNodeReqs (airBuild (K := K) 4).label =
      [⟨dotOp2B, dotOp2Sf1, 3,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 4).stamp 0⟩] := by
    rw [airBuild_label, extractNodeReqs_bfsLabelAt_air_op1b]
  exact genMemForestFromTree_airBuild_leaf_length z α 4 airBuild_4_children _ h

theorem genMemForestFromTree_airBuild_5_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (airBuild (K := K) 5)).length = 1 := by
  have h : extractNodeReqs (airBuild (K := K) 5).label =
      [⟨dotOp2C, dotOp2Sf2, 3,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 5).stamp 0⟩] := by
    rw [airBuild_label, extractNodeReqs_bfsLabelAt_air_op1c]
  exact genMemForestFromTree_airBuild_leaf_length z α 5 airBuild_5_children _ h

theorem genMemForestFromTree_airBuild_7_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (airBuild (K := K) 7)).length = 1 := by
  have h : extractNodeReqs (airBuild (K := K) 7).label =
      [⟨dotCoreFormula, dotCore, 3,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 7).stamp 0⟩] := by
    rw [airBuild_label, extractNodeReqs_bfsLabelAt_air_core]
  exact genMemForestFromTree_airBuild_leaf_length z α 7 airBuild_7_children _ h

theorem genMemForestFromTree_airBuild_8_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (airBuild (K := K) 8)).length = 1 := by
  have h : extractNodeReqs (airBuild (K := K) 8).label =
      [⟨dotArm, dotResult, 3,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 8).stamp 0⟩] := by
    rw [airBuild_label, extractNodeReqs_bfsLabelAt_air_invoke]
  exact genMemForestFromTree_airBuild_leaf_length z α 8 airBuild_8_children _ h

theorem genMemForestFromTree_airBuild_6_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (airBuild (K := K) 6)).length = 4 := by
  rw [show airBuild (K := K) 6 = .node (airBuild (K := K) 6).label
        (airBuild (K := K) 6).children from by cases airBuild (K := K) 6; rfl,
    genMemForestFromTree_node, airBuild_6_children, List.length_append,
    genMemForestFromList_cons, genMemForestFromList_cons, genMemForestFromList_nil,
    List.length_append, List.length_append, List.length_nil, airBuild_label,
    genRowMemForest_bfsLabelAt_air_op9_length, genMemForestFromTree_airBuild_7_length,
    genMemForestFromTree_airBuild_8_length]

theorem genMemForestFromTree_airBuild_2_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (airBuild (K := K) 2)).length = 7 := by
  rw [show airBuild (K := K) 2 = .node (airBuild (K := K) 2).label
        (airBuild (K := K) 2).children from by cases airBuild (K := K) 2; rfl,
    genMemForestFromTree_node, airBuild_2_children, List.length_append,
    genMemForestFromList_cons, genMemForestFromList_cons, genMemForestFromList_cons,
    genMemForestFromList_nil, List.length_append, List.length_append,
    List.length_append, List.length_nil, airBuild_label,
    genRowMemForest_bfsLabelAt_air_op2_length, genMemForestFromTree_airBuild_4_length,
    genMemForestFromTree_airBuild_5_length, genMemForestFromTree_airBuild_6_length]

theorem genMemForestFromTree_airBuild_3_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (airBuild (K := K) 3)) = 5 := by
  have hreq : extractNodeReqs (airBuild (K := K) 3).label =
      [⟨.cell (.atom 1) (.atom 0), .atom 0, 3,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 3).stamp 0⟩] := by
    rw [airBuild_label, extractNodeReqs_bfsLabelAt_air_cond]
    simp [dotCondFormula, dotCondResult]
  rw [genMemForestFromTree_airBuild_leaf_size z α 3 airBuild_3_children _ _ _ hreq]
  simp [nounWalkSize]

theorem genMemForestFromTree_airBuild_4_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (airBuild (K := K) 4)) = 7 := by
  have hreq : extractNodeReqs (airBuild (K := K) 4).label =
      [⟨.cell (.atom 1) (.cell (.atom 0) (.atom 1)), .cell (.atom 0) (.atom 1), 3,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 4).stamp 0⟩] := by
    rw [airBuild_label, extractNodeReqs_bfsLabelAt_air_op1b]
    simp [dotOp2B, dotOp2Sf1]
  rw [genMemForestFromTree_airBuild_leaf_size z α 4 airBuild_4_children _ _ _ hreq]
  simp [nounWalkSize]

theorem genMemForestFromTree_airBuild_5_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (airBuild (K := K) 5)) = 17 := by
  have hreq : extractNodeReqs (airBuild (K := K) 5).label =
      [⟨.cell (.atom 1) dotOp9Formula, dotOp9Formula, 3,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 5).stamp 0⟩] := by
    rw [airBuild_label, extractNodeReqs_bfsLabelAt_air_op1c]
    simp [dotOp2C, dotOp2Sf2]
  rw [genMemForestFromTree_airBuild_leaf_size z α 5 airBuild_5_children _ _ _ hreq]
  simp [nounWalkSize, nounWalkSize_dotOp9Formula]

theorem genMemForestFromTree_airBuild_7_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (airBuild (K := K) 7)) = 11 := by
  have hreq : extractNodeReqs (airBuild (K := K) 7).label =
      [⟨.cell (.atom 1) dotCore, dotCore, 3,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 7).stamp 0⟩] := by
    rw [airBuild_label, extractNodeReqs_bfsLabelAt_air_core]
    simp [dotCoreFormula]
  rw [genMemForestFromTree_airBuild_leaf_size z α 7 airBuild_7_children _ _ _ hreq]
  simp [nounWalkSize, nounWalkSize_dotCore]

theorem genMemForestFromTree_airBuild_8_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (airBuild (K := K) 8)) = 5 := by
  have hreq : extractNodeReqs (airBuild (K := K) 8).label =
      [⟨.cell (.atom 1) (.atom 3), .atom 3, 3,
          getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 8).stamp 0⟩] := by
    rw [airBuild_label, extractNodeReqs_bfsLabelAt_air_invoke]
    simp [dotArm, dotElem0, dotResult]
  rw [genMemForestFromTree_airBuild_leaf_size z α 8 airBuild_8_children _ _ _ hreq]
  simp [nounWalkSize]

theorem genMemForestFromTree_airBuild_6_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (airBuild (K := K) 6)) = 42 := by
  rw [show airBuild (K := K) 6 = .node (airBuild (K := K) 6).label
        (airBuild (K := K) 6).children from by cases airBuild (K := K) 6; rfl,
    genMemForestFromTree_node, totalSize_append, airBuild_6_children,
    genMemForestFromList_cons, genMemForestFromList_cons, genMemForestFromList_nil,
    totalSize_append, totalSize_append, airBuild_label]
  have hnil : totalSize ([] : List (NTree (GenMemoryRow K))) = 0 := rfl
  rw [genRowMemForest_bfsLabelAt_air_op9_size, genMemForestFromTree_airBuild_7_size,
    genMemForestFromTree_airBuild_8_size, hnil]

theorem genMemForestFromTree_airBuild_2_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (airBuild (K := K) 2)) = 93 := by
  rw [show airBuild (K := K) 2 = .node (airBuild (K := K) 2).label
        (airBuild (K := K) 2).children from by cases airBuild (K := K) 2; rfl,
    genMemForestFromTree_node, totalSize_append, airBuild_2_children,
    genMemForestFromList_cons, genMemForestFromList_cons, genMemForestFromList_cons,
    genMemForestFromList_nil, totalSize_append, totalSize_append, totalSize_append,
    airBuild_label]
  have hnil : totalSize ([] : List (NTree (GenMemoryRow K))) = 0 := rfl
  rw [genRowMemForest_bfsLabelAt_air_op2_size, genMemForestFromTree_airBuild_4_size,
    genMemForestFromTree_airBuild_5_size, genMemForestFromTree_airBuild_6_size, hnil]

/-! ## Assigned AIR forest counts -/

theorem dotMemForest_assigned_air_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTreeAir (K := K)))).length =
      10 := by
  rw [bfsAssign_air_eq_node, genMemForestFromTree_node, List.length_append,
    bfsAssign_air_children, genMemForestFromList_cons, genMemForestFromList_cons,
    genMemForestFromList_nil, List.length_append, List.length_append, List.length_nil,
    genRowMemForest_air_root_length, genMemForestFromTree_airBuild_2_length,
    genMemForestFromTree_airBuild_3_length]

theorem dotMemForest_assigned_air_totalSize (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb
      (bfsAssign (dotTreeAir (K := K)))) = 184 := by
  rw [bfsAssign_air_eq_node, genMemForestFromTree_node, totalSize_append,
    bfsAssign_air_children, genMemForestFromList_cons, genMemForestFromList_cons,
    genMemForestFromList_nil, totalSize_append, totalSize_append]
  have hnil : totalSize ([] : List (NTree (GenMemoryRow K))) = 0 := rfl
  rw [genRowMemForest_air_root_size, genMemForestFromTree_airBuild_2_size,
    genMemForestFromTree_airBuild_3_size, hnil]

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.dotMemForest_assigned_air_length
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotMemForest_assigned_air_totalSize
