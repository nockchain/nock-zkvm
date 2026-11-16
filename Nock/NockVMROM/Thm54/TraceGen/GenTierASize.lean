/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierASize.lean

  Exact served-forest counts for the Tier A OP6/OP2/OP9 program.  The OP6 branch-pair record is already
  39 nodes (`dotBranchPairRecord_size`); this module names the remaining
  walks and shows the full unassigned forest has 184 nodes / 10 roots,
  which fits an orbit of `2^8 = 256` and not F97's `2^5 = 32`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMem

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54

variable {K : Type} [Field K]

variable {lmb : K}

theorem nounWalkSize_dotCondFormula : nounWalkSize dotCondFormula = 3 := by
  simp [nounWalkSize, dotCondFormula]

theorem nounWalkSize_dotOp2B : nounWalkSize dotOp2B = 5 := by
  simp [nounWalkSize, dotOp2B]

theorem nounWalkSize_dotOp9Formula : nounWalkSize dotOp9Formula = 13 := by
  simp [nounWalkSize, dotOp9Formula, dotOp9Tail, dotCoreFormula, dotCore, dotElem0, dotElem1]

theorem nounWalkSize_dotOp2C : nounWalkSize dotOp2C = 15 := by
  simp [nounWalkSize, dotOp2C, nounWalkSize_dotOp9Formula]

theorem nounWalkSize_dotCore : nounWalkSize dotCore = 7 := by
  simp [nounWalkSize, dotCore, dotElem0, dotElem1]

theorem nounWalkSize_dotCoreFormula : nounWalkSize dotCoreFormula = 9 := by
  simp [nounWalkSize, dotCoreFormula, nounWalkSize_dotCore]

theorem nounWalkSize_dotBranchPair : nounWalkSize dotBranchPair = 37 := by
  simp [nounWalkSize, dotBranchPair, nounWalkSize_dotThenFormula, nounWalkSize_dotElseFormula]

theorem nounWalkSize_dotElem0 : nounWalkSize dotElem0 = 3 := by
  simp [nounWalkSize, dotElem0]

theorem nounWalkSize_dotElem1 : nounWalkSize dotElem1 = 3 := by
  simp [nounWalkSize, dotElem1]

theorem totalSize_append {α} (l₁ l₂ : List (NTree α)) :
    totalSize (l₁ ++ l₂) = totalSize l₁ + totalSize l₂ := by
  simp [totalSize, List.map_append, List.sum_append]

theorem mapNTree_size {α β} (f : α → β) (t : NTree α) :
    (mapNTree f t).size = t.size := by
  induction ht : t.size using Nat.strongRecOn generalizing t with
  | _ n ih =>
    cases t with
    | node _ cs =>
      simp [mapNTree, NTree.size] at ht ⊢
      have hcs : ∀ c ∈ cs, (mapNTree f c).size = c.size := by
        intro c hc
        have hin : c.size ∈ cs.map NTree.size := List.mem_map.mpr ⟨c, hc, rfl⟩
        have hle : c.size ≤ (cs.map NTree.size).sum := List.le_sum_of_mem hin
        refine ih c.size (by omega) c rfl
      have hmap : cs.map (NTree.size ∘ mapNTree f) = cs.map NTree.size := by
        apply List.map_congr_left
        intro c hc
        exact hcs c hc
      rw [hmap]
      exact ht

theorem totalSize_map {α β} (f : α → β) (ts : List (NTree α)) :
    totalSize (ts.map (mapNTree f)) = totalSize ts := by
  simp [totalSize, List.map_map]
  refine congrArg List.sum ?_
  apply List.map_congr_left
  intro t _
  exact mapNTree_size f t

theorem genAnnotatedChainedTree_axis3_axis2_size
    (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ)
    (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩] = some t) :
    t.size = 6 + nounWalkSize hd1 + nounWalkSize hd2 + nounWalkSize tl2 := by
  unfold genAnnotatedChainedTree at ht
  simp only [chainedInnerRootState] at ht
  injection ht with ht
  subst t
  have hinner :
      ((genAnnotatedChainedInner E z α lmb
          ⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩
          [⟨.cell hd2 tl2, hd2, 2, e2⟩]).1.map NTree.size).sum
        = 4 + nounWalkSize hd2 + nounWalkSize tl2 := by
    unfold genAnnotatedChainedInner
    simp only [genAnnotatedChainedInner_nil, chainedInnerRootState]
    rw [genAnnotatedDescentCont_axis2]
    simp [NTree.size, genAnnotatedNounWalk_size, genAnnotatedVerify_size]
    omega
  rw [genAnnotatedDescentCont_axis3]
  simp [NTree.size, genAnnotatedNounWalk_size]
  omega

theorem genRowMemForest_chain32_size (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    totalSize (genRowMemForest E z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩])
      = 6 + nounWalkSize hd1 + nounWalkSize hd2 + nounWalkSize tl2 := by
  unfold genRowMemForest
  cases h : genAnnotatedChainedTree E z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] with
  | none => simp [genAnnotatedChainedTree] at h
  | some t =>
    simp [h, totalSize,
      genAnnotatedChainedTree_axis3_axis2_size E z α hd1 hd2 tl2 e1 e2 t h]

theorem genRowMemForest_three_chain32_size (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 hd3 tl3 : Noun) (e1 e2 e3 : ℕ) :
    totalSize (genRowMemForest E z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩,
         ⟨.cell hd3 tl3, hd3, 2, e3⟩])
      = 9 + nounWalkSize hd1 + nounWalkSize hd2 + nounWalkSize tl2
          + nounWalkSize hd3 + nounWalkSize tl3 := by
  unfold genRowMemForest
  cases h : genAnnotatedChainedTree E z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] with
  | none => simp [genAnnotatedChainedTree] at h
  | some t =>
    simp [h, totalSize,
      genAnnotatedChainedTree_axis3_axis2_size E z α hd1 hd2 tl2 e1 e2 t h,
      genAnnotatedRecordTree_axis2_size]
    omega

theorem genRowMemForest_singleton_axis3_size (E : Noun → ComputeTable.FP K) (z α : K)
    (hd tl : Noun) (e : ℕ) :
    totalSize (genRowMemForest E z α lmb [⟨.cell hd tl, tl, 3, e⟩])
      = 3 + nounWalkSize hd + nounWalkSize tl := by
  simp [genRowMemForest_singleton, totalSize, genAnnotatedRecordTree_axis3_size]

theorem genRowMemForest_singleton_axis2_size (E : Noun → ComputeTable.FP K) (z α : K)
    (hd tl : Noun) (e : ℕ) :
    totalSize (genRowMemForest E z α lmb [⟨.cell hd tl, hd, 2, e⟩])
      = 3 + nounWalkSize hd + nounWalkSize tl := by
  simp [genRowMemForest_singleton, totalSize, genAnnotatedRecordTree_axis2_size]

theorem genRowMemForest_three_chain32_length (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 hd3 tl3 : Noun) (e1 e2 e3 : ℕ) :
    (genRowMemForest E z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩,
         ⟨.cell hd3 tl3, hd3, 2, e3⟩]).length = 2 := by
  unfold genRowMemForest
  cases h : genAnnotatedChainedTree E z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] with
  | none => simp [genAnnotatedChainedTree] at h
  | some t => simp [h]

theorem extractNodeReqs_unassigned (g : GenComputeRow K) :
    extractNodeReqs g =
      extractNodeReqsAux g.stamp 0 g.requests := rfl

theorem extractNodeReqs_dotTree :
    extractNodeReqs (dotTree (K := K)).label =
      [⟨dotFormula, dotParentTail, 3, 0⟩,
       ⟨dotParentTail, dotCondFormula, 2, 0⟩,
       ⟨dotBranchPair, dotThenFormula, 2, 0⟩] := by
  simp [dotTree, skelNode, extractNodeReqs, extractNodeReqsAux, getRecordExp, zeroStamp]

theorem extractNodeReqs_dotCondTree :
    extractNodeReqs (dotCondTree (K := K)).label =
      [⟨dotCondFormula, dotCondResult, 3, 0⟩] := by
  simp [dotCondTree, skelNode, extractNodeReqs, extractNodeReqsAux, getRecordExp, zeroStamp]

theorem extractNodeReqs_dotOp2Tree :
    extractNodeReqs (dotOp2Tree (K := K)).label =
      [⟨dotThenFormula, dotThenTail, 3, 0⟩,
       ⟨dotThenTail, dotOp2B, 2, 0⟩] := by
  simp [dotOp2Tree, skelNode, extractNodeReqs, extractNodeReqsAux, getRecordExp, zeroStamp]

theorem extractNodeReqs_dotOp1BTree :
    extractNodeReqs (dotOp1BTree (K := K)).label =
      [⟨dotOp2B, dotOp2Sf1, 3, 0⟩] := by
  simp [dotOp1BTree, skelNode, extractNodeReqs, extractNodeReqsAux, getRecordExp, zeroStamp]

theorem extractNodeReqs_dotOp1CTree :
    extractNodeReqs (dotOp1CTree (K := K)).label =
      [⟨dotOp2C, dotOp2Sf2, 3, 0⟩] := by
  simp [dotOp1CTree, skelNode, extractNodeReqs, extractNodeReqsAux, getRecordExp, zeroStamp]

theorem extractNodeReqs_dotOp9Tree :
    extractNodeReqs (dotOp9Tree (K := K)).label =
      [⟨dotOp9Formula, dotOp9Tail, 3, 0⟩,
       ⟨dotOp9Tail, .atom 2, 2, 0⟩,
       ⟨dotCore, dotArm, 2, 0⟩] := by
  simp [dotOp9Tree, skelNode, extractNodeReqs, extractNodeReqsAux, getRecordExp, zeroStamp]

theorem extractNodeReqs_dotOp9CoreTree :
    extractNodeReqs (dotOp9CoreTree (K := K)).label =
      [⟨dotCoreFormula, dotCore, 3, 0⟩] := by
  simp [dotOp9CoreTree, skelNode, extractNodeReqs, extractNodeReqsAux, getRecordExp, zeroStamp]

theorem extractNodeReqs_dotOp9InvokeTree :
    extractNodeReqs (dotOp9InvokeTree (K := K)).label =
      [⟨dotArm, dotResult, 3, 0⟩] := by
  simp [dotOp9InvokeTree, skelNode, extractNodeReqs, extractNodeReqsAux, getRecordExp, zeroStamp]

theorem genMemForestFromTree_node (E : Noun → ComputeTable.FP K) (z α : K)
    (g : GenComputeRow K) (cs : List (NTree (GenComputeRow K))) :
    genMemForestFromTree E z α lmb (.node g cs) =
      genRowMemForest E z α lmb (extractNodeReqs g) ++ genMemForestFromList E z α lmb cs :=
  rfl

theorem genMemForestFromList_nil (E : Noun → ComputeTable.FP K) (z α : K) :
    genMemForestFromList E z α lmb [] = [] := rfl

theorem genMemForestFromList_cons (E : Noun → ComputeTable.FP K) (z α : K)
    (t : NTree (GenComputeRow K)) (ts : List (NTree (GenComputeRow K))) :
    genMemForestFromList E z α lmb (t :: ts) =
      genMemForestFromTree E z α lmb t ++ genMemForestFromList E z α lmb ts :=
  rfl

theorem genMemForestFromTree_leaf_length (E : Noun → ComputeTable.FP K) (z α : K)
    (g : GenComputeRow K) (r : MemRecordReq)
    (h : extractNodeReqs g = [r]) :
    (genMemForestFromTree E z α lmb (.node g [])).length = 1 := by
  rw [genMemForestFromTree_leaf, h, genRowMemForest_singleton]
  simp

theorem genMemForestFromTree_leaf_axis3_size (E : Noun → ComputeTable.FP K) (z α : K)
    (g : GenComputeRow K) (hd tl : Noun) (e : ℕ)
    (h : extractNodeReqs g = [⟨.cell hd tl, tl, 3, e⟩]) :
    totalSize (genMemForestFromTree E z α lmb (.node g [])) =
      3 + nounWalkSize hd + nounWalkSize tl := by
  rw [genMemForestFromTree_leaf, h, genRowMemForest_singleton_axis3_size]

theorem dotTree_eq_node :
    dotTree (K := K) = .node (dotTree (K := K)).label
      [dotCondTree (K := K), dotOp2Tree (K := K)] := rfl

theorem dotOp2Tree_eq_node :
    dotOp2Tree (K := K) = .node (dotOp2Tree (K := K)).label
      [dotOp1BTree (K := K), dotOp1CTree (K := K), dotOp9Tree (K := K)] := rfl

theorem dotOp9Tree_eq_node :
    dotOp9Tree (K := K) = .node (dotOp9Tree (K := K)).label
      [dotOp9CoreTree (K := K), dotOp9InvokeTree (K := K)] := rfl

theorem genRowMemForest_dotTree_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (dotTree (K := K)).label)).length = 2 := by
  rw [extractNodeReqs_dotTree]
  simp [dotFormula, dotParentTail, dotBranchPair]
  exact genRowMemForest_three_chain32_length (encC z) z α
    (.atom 6) dotCondFormula dotBranchPair dotThenFormula dotElseFormula 0 0 0

theorem genRowMemForest_dotOp9_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (dotOp9Tree (K := K)).label)).length = 2 := by
  rw [extractNodeReqs_dotOp9Tree]
  simp [dotOp9Formula, dotOp9Tail, dotCore, dotArm]
  exact genRowMemForest_three_chain32_length (encC z) z α
    (.atom 9) (.atom 2) dotCoreFormula dotElem0 dotElem1 0 0 0

theorem genRowMemForest_dotOp2_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (dotOp2Tree (K := K)).label)).length = 1 := by
  rw [extractNodeReqs_dotOp2Tree]
  exact genRowMemForest_chain_length (encC z) z α
    ⟨dotThenFormula, dotThenTail, 3, 0⟩ ⟨dotThenTail, dotOp2B, 2, 0⟩ rfl

theorem genRowMemForest_dotTree_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (dotTree (K := K)).label)) = 86 := by
  rw [extractNodeReqs_dotTree]
  simp [dotFormula, dotParentTail, dotBranchPair]
  rw [genRowMemForest_three_chain32_size]
  simp [nounWalkSize, nounWalkSize_dotCondFormula,
    nounWalkSize_dotThenFormula, nounWalkSize_dotElseFormula]

theorem genRowMemForest_dotOp9_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (dotOp9Tree (K := K)).label)) = 26 := by
  rw [extractNodeReqs_dotOp9Tree]
  simp [dotOp9Formula, dotOp9Tail, dotCore, dotArm]
  rw [genRowMemForest_three_chain32_size]
  simp [nounWalkSize, nounWalkSize_dotCoreFormula, nounWalkSize_dotElem0,
    nounWalkSize_dotElem1]

theorem genRowMemForest_dotOp2_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (dotOp2Tree (K := K)).label)) = 27 := by
  rw [extractNodeReqs_dotOp2Tree]
  simp [dotThenFormula, dotThenTail]
  rw [genRowMemForest_chain32_size]
  simp [nounWalkSize, nounWalkSize_dotOp2B, nounWalkSize_dotOp2C]

theorem genMemForestFromTree_dotCond_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (dotCondTree (K := K))).length = 1 := by
  rw [show dotCondTree (K := K) = .node (dotCondTree (K := K)).label [] from rfl]
  exact genMemForestFromTree_leaf_length (encC z) z α _
    ⟨dotCondFormula, dotCondResult, 3, 0⟩ extractNodeReqs_dotCondTree

theorem genMemForestFromTree_dotOp1B_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (dotOp1BTree (K := K))).length = 1 := by
  rw [show dotOp1BTree (K := K) = .node (dotOp1BTree (K := K)).label [] from rfl]
  exact genMemForestFromTree_leaf_length (encC z) z α _
    ⟨dotOp2B, dotOp2Sf1, 3, 0⟩ extractNodeReqs_dotOp1BTree

theorem genMemForestFromTree_dotOp1C_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (dotOp1CTree (K := K))).length = 1 := by
  rw [show dotOp1CTree (K := K) = .node (dotOp1CTree (K := K)).label [] from rfl]
  exact genMemForestFromTree_leaf_length (encC z) z α _
    ⟨dotOp2C, dotOp2Sf2, 3, 0⟩ extractNodeReqs_dotOp1CTree

theorem genMemForestFromTree_dotOp9Core_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (dotOp9CoreTree (K := K))).length = 1 := by
  rw [show dotOp9CoreTree (K := K) = .node (dotOp9CoreTree (K := K)).label [] from rfl]
  exact genMemForestFromTree_leaf_length (encC z) z α _
    ⟨dotCoreFormula, dotCore, 3, 0⟩ extractNodeReqs_dotOp9CoreTree

theorem genMemForestFromTree_dotOp9Invoke_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (dotOp9InvokeTree (K := K))).length = 1 := by
  rw [show dotOp9InvokeTree (K := K) = .node (dotOp9InvokeTree (K := K)).label [] from rfl]
  exact genMemForestFromTree_leaf_length (encC z) z α _
    ⟨dotArm, dotResult, 3, 0⟩ extractNodeReqs_dotOp9InvokeTree

theorem genMemForestFromTree_dotCond_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (dotCondTree (K := K))) = 5 := by
  rw [show dotCondTree (K := K) = .node (dotCondTree (K := K)).label [] from rfl]
  have hreq : extractNodeReqs (dotCondTree (K := K)).label =
      [⟨.cell (.atom 1) (.atom 0), .atom 0, 3, 0⟩] := by
    simp [extractNodeReqs_dotCondTree, dotCondFormula, dotCondResult]
  rw [genMemForestFromTree_leaf_axis3_size (encC z) z α _ (.atom 1) (.atom 0) 0 hreq]
  simp [nounWalkSize]

theorem genMemForestFromTree_dotOp1B_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (dotOp1BTree (K := K))) = 7 := by
  rw [show dotOp1BTree (K := K) = .node (dotOp1BTree (K := K)).label [] from rfl]
  have hreq : extractNodeReqs (dotOp1BTree (K := K)).label =
      [⟨.cell (.atom 1) (.cell (.atom 0) (.atom 1)), .cell (.atom 0) (.atom 1), 3, 0⟩] := by
    simp [extractNodeReqs_dotOp1BTree, dotOp2B, dotOp2Sf1]
  rw [genMemForestFromTree_leaf_axis3_size (encC z) z α _
      (.atom 1) (.cell (.atom 0) (.atom 1)) 0 hreq]
  simp [nounWalkSize]

theorem genMemForestFromTree_dotOp1C_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (dotOp1CTree (K := K))) = 17 := by
  rw [show dotOp1CTree (K := K) = .node (dotOp1CTree (K := K)).label [] from rfl]
  have hreq : extractNodeReqs (dotOp1CTree (K := K)).label =
      [⟨.cell (.atom 1) dotOp9Formula, dotOp9Formula, 3, 0⟩] := by
    simp [extractNodeReqs_dotOp1CTree, dotOp2C, dotOp2Sf2]
  rw [genMemForestFromTree_leaf_axis3_size (encC z) z α _
      (.atom 1) dotOp9Formula 0 hreq]
  simp [nounWalkSize, nounWalkSize_dotOp9Formula]

theorem genMemForestFromTree_dotOp9Core_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (dotOp9CoreTree (K := K))) = 11 := by
  rw [show dotOp9CoreTree (K := K) = .node (dotOp9CoreTree (K := K)).label [] from rfl]
  have hreq : extractNodeReqs (dotOp9CoreTree (K := K)).label =
      [⟨.cell (.atom 1) dotCore, dotCore, 3, 0⟩] := by
    simp [extractNodeReqs_dotOp9CoreTree, dotCoreFormula]
  rw [genMemForestFromTree_leaf_axis3_size (encC z) z α _ (.atom 1) dotCore 0 hreq]
  simp [nounWalkSize, nounWalkSize_dotCore]

theorem genMemForestFromTree_dotOp9Invoke_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (dotOp9InvokeTree (K := K))) = 5 := by
  rw [show dotOp9InvokeTree (K := K) = .node (dotOp9InvokeTree (K := K)).label [] from rfl]
  have hreq : extractNodeReqs (dotOp9InvokeTree (K := K)).label =
      [⟨.cell (.atom 1) (.atom 3), .atom 3, 3, 0⟩] := by
    simp [extractNodeReqs_dotOp9InvokeTree, dotArm, dotElem0, dotResult]
  rw [genMemForestFromTree_leaf_axis3_size (encC z) z α _
      (.atom 1) (.atom 3) 0 hreq]
  simp [nounWalkSize]

theorem genMemForestFromTree_dotOp9_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (dotOp9Tree (K := K))).length = 4 := by
  rw [dotOp9Tree_eq_node, genMemForestFromTree_node, List.length_append,
    genMemForestFromList_cons, genMemForestFromList_cons, genMemForestFromList_nil,
    List.length_append, List.length_append, List.length_nil]
  rw [genRowMemForest_dotOp9_length, genMemForestFromTree_dotOp9Core_length,
    genMemForestFromTree_dotOp9Invoke_length]

theorem genMemForestFromTree_dotOp9_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (dotOp9Tree (K := K))) = 42 := by
  rw [dotOp9Tree_eq_node, genMemForestFromTree_node, totalSize_append,
    genMemForestFromList_cons, genMemForestFromList_cons, genMemForestFromList_nil,
    totalSize_append, totalSize_append]
  have hnil : totalSize ([] : List (NTree (GenMemoryRow K))) = 0 := rfl
  rw [genRowMemForest_dotOp9_size, genMemForestFromTree_dotOp9Core_size,
    genMemForestFromTree_dotOp9Invoke_size, hnil]

theorem genMemForestFromTree_dotOp2_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (dotOp2Tree (K := K))).length = 7 := by
  rw [dotOp2Tree_eq_node, genMemForestFromTree_node, List.length_append,
    genMemForestFromList_cons, genMemForestFromList_cons, genMemForestFromList_cons,
    genMemForestFromList_nil, List.length_append, List.length_append, List.length_append,
    List.length_nil]
  rw [genRowMemForest_dotOp2_length, genMemForestFromTree_dotOp1B_length,
    genMemForestFromTree_dotOp1C_length, genMemForestFromTree_dotOp9_length]

theorem genMemForestFromTree_dotOp2_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (dotOp2Tree (K := K))) = 93 := by
  rw [dotOp2Tree_eq_node, genMemForestFromTree_node, totalSize_append,
    genMemForestFromList_cons, genMemForestFromList_cons, genMemForestFromList_cons,
    genMemForestFromList_nil, totalSize_append, totalSize_append, totalSize_append]
  have hnil : totalSize ([] : List (NTree (GenMemoryRow K))) = 0 := rfl
  rw [genRowMemForest_dotOp2_size, genMemForestFromTree_dotOp1B_size,
    genMemForestFromTree_dotOp1C_size, genMemForestFromTree_dotOp9_size, hnil]

theorem dotMemForest_unassigned_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (dotTree (K := K))).length = 10 := by
  rw [dotTree_eq_node, genMemForestFromTree_node, List.length_append,
    genMemForestFromList_cons, genMemForestFromList_cons, genMemForestFromList_nil,
    List.length_append, List.length_append, List.length_nil]
  rw [genRowMemForest_dotTree_length, genMemForestFromTree_dotCond_length,
    genMemForestFromTree_dotOp2_length]

theorem dotMemForest_unassigned_totalSize (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (dotTree (K := K))) = 184 := by
  rw [dotTree_eq_node, genMemForestFromTree_node, totalSize_append,
    genMemForestFromList_cons, genMemForestFromList_cons, genMemForestFromList_nil,
    totalSize_append, totalSize_append]
  have hnil : totalSize ([] : List (NTree (GenMemoryRow K))) = 0 := rfl
  rw [genRowMemForest_dotTree_size, genMemForestFromTree_dotCond_size,
    genMemForestFromTree_dotOp2_size, hnil]

/-! ## Assigned forest counts

`bfsAssign` restamps; request `(root, child, axis)` lists are unchanged
and the size lemmas ignore `recordExp`.  Children of `bfsAssign t` are
`buildTF` nodes at global BFS indices, not `bfsAssign` of the original
subtrees. -/

theorem foCol_dot_1 : foCol (bfsForest [dotTree (K := K)]) 1 = 2 := by
  rw [foCol, dot_bfsForest]
  rfl

theorem foCol_dot_2 : foCol (bfsForest [dotTree (K := K)]) 2 = 0 := by
  rw [foCol, dot_bfsForest]
  rfl

theorem foCol_dot_3 : foCol (bfsForest [dotTree (K := K)]) 3 = 3 := by
  rw [foCol, dot_bfsForest]
  rfl

theorem foCol_dot_4 : foCol (bfsForest [dotTree (K := K)]) 4 = 0 := by
  rw [foCol, dot_bfsForest]
  rfl

theorem foCol_dot_5 : foCol (bfsForest [dotTree (K := K)]) 5 = 0 := by
  rw [foCol, dot_bfsForest]
  rfl

theorem foCol_dot_6 : foCol (bfsForest [dotTree (K := K)]) 6 = 2 := by
  rw [foCol, dot_bfsForest]
  rfl

theorem foCol_dot_7 : foCol (bfsForest [dotTree (K := K)]) 7 = 0 := by
  rw [foCol, dot_bfsForest]
  rfl

theorem foCol_dot_8 : foCol (bfsForest [dotTree (K := K)]) 8 = 0 := by
  rw [foCol, dot_bfsForest]
  rfl

theorem Sf_foCol_dot :
    Sf (foCol (bfsForest [dotTree (K := K)])) 1 = 2 ∧
    Sf (foCol (bfsForest [dotTree (K := K)])) 2 = 2 ∧
    Sf (foCol (bfsForest [dotTree (K := K)])) 5 = 5 := by
  have h1 : Sf (foCol (bfsForest [dotTree (K := K)])) 1 = 2 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, Sf_succ, Sf_zero, foCol_dot_1]
  have h2 : Sf (foCol (bfsForest [dotTree (K := K)])) 2 = 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Sf_succ, h1, foCol_dot_2]
  have h3 : Sf (foCol (bfsForest [dotTree (K := K)])) 3 = 5 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Sf_succ, h2, foCol_dot_3]
  have h4 : Sf (foCol (bfsForest [dotTree (K := K)])) 4 = 5 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, Sf_succ, h3, foCol_dot_4]
  have h5 : Sf (foCol (bfsForest [dotTree (K := K)])) 5 = 5 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, Sf_succ, h4, foCol_dot_5]
  exact ⟨h1, h2, h5⟩

private def dotBuild (i : ℕ) : NTree (GenComputeRow K) :=
  buildTF 1 (foCol (bfsForest [dotTree (K := K)]))
    (bfsLabelAt (dotTree (K := K))) (bfsForest [dotTree (K := K)]).length i

theorem dotBuild_label (i : ℕ) :
    (dotBuild (K := K) i).label = bfsLabelAt (dotTree (K := K)) i :=
  buildTF_label _ _ _ _ _

theorem dot_hne : [dotTree (K := K)] ≠ [] := List.cons_ne_nil _ _

theorem dotBuild_children (i : ℕ) (hi1 : 1 ≤ i)
    (hih : i ≤ (bfsForest [dotTree (K := K)]).length) :
    (dotBuild (K := K) i).children =
      (List.range' (firstCF 1 (foCol (bfsForest [dotTree (K := K)])) i)
        (foCol (bfsForest [dotTree (K := K)]) i)).map dotBuild := by
  unfold dotBuild
  rw [buildTF_children,
    childIdxsF_eq (kroots := 1) (fo := foCol (bfsForest [dotTree (K := K)]))
      (h := (bfsForest [dotTree (K := K)]).length)
      (foCol_Sf_tilingF _ dot_hne) (foCol_BFSValidF _ dot_hne) hi1 hih]

theorem firstCF_dot_1 :
    firstCF 1 (foCol (bfsForest [dotTree (K := K)])) 1 = 2 := by
  dsimp only [firstCF]
  rw [Sf_zero]

theorem firstCF_dot_3 :
    firstCF 1 (foCol (bfsForest [dotTree (K := K)])) 3 = 4 := by
  dsimp only [firstCF]
  change 1 + 1 + Sf (foCol (bfsForest [dotTree (K := K)])) 2 = 4
  rw [Sf_foCol_dot.2.1]

theorem firstCF_dot_6 :
    firstCF 1 (foCol (bfsForest [dotTree (K := K)])) 6 = 7 := by
  dsimp only [firstCF]
  change 1 + 1 + Sf (foCol (bfsForest [dotTree (K := K)])) 5 = 7
  rw [Sf_foCol_dot.2.2]

theorem bfsAssign_dot_eq_node :
    bfsAssign (dotTree (K := K)) =
      .node (bfsAssign (dotTree (K := K))).label
        (bfsAssign (dotTree (K := K))).children := by
  cases bfsAssign (dotTree (K := K)); rfl

theorem bfsAssign_dot_children :
    (bfsAssign (dotTree (K := K))).children =
      [dotBuild (K := K) 2, dotBuild (K := K) 3] := by
  rw [bfsAssign]
  change (dotBuild (K := K) 1).children = _
  rw [dotBuild_children 1 (by omega) (by simp [dot_bfsForest]),
    firstCF_dot_1, foCol_dot_1]
  rfl

theorem dotBuild_2_children : (dotBuild (K := K) 2).children = [] := by
  rw [dotBuild_children 2 (by omega) (by simp [dot_bfsForest]), foCol_dot_2]
  rfl

theorem dotBuild_3_children :
    (dotBuild (K := K) 3).children =
      [dotBuild (K := K) 4, dotBuild (K := K) 5, dotBuild (K := K) 6] := by
  rw [dotBuild_children 3 (by omega) (by simp [dot_bfsForest]),
    firstCF_dot_3, foCol_dot_3]
  rfl

theorem dotBuild_4_children : (dotBuild (K := K) 4).children = [] := by
  rw [dotBuild_children 4 (by omega) (by simp [dot_bfsForest]), foCol_dot_4]
  rfl

theorem dotBuild_5_children : (dotBuild (K := K) 5).children = [] := by
  rw [dotBuild_children 5 (by omega) (by simp [dot_bfsForest]), foCol_dot_5]
  rfl

theorem dotBuild_6_children :
    (dotBuild (K := K) 6).children =
      [dotBuild (K := K) 7, dotBuild (K := K) 8] := by
  rw [dotBuild_children 6 (by omega) (by simp [dot_bfsForest]),
    firstCF_dot_6, foCol_dot_6]
  rfl

theorem dotBuild_7_children : (dotBuild (K := K) 7).children = [] := by
  rw [dotBuild_children 7 (by omega) (by simp [dot_bfsForest]), foCol_dot_7]
  rfl

theorem dotBuild_8_children : (dotBuild (K := K) 8).children = [] := by
  rw [dotBuild_children 8 (by omega) (by simp [dot_bfsForest]), foCol_dot_8]
  rfl

theorem extractNodeReqs_bfsLabelAt_cond :
    extractNodeReqs (bfsLabelAt (dotTree (K := K)) 2) =
      [⟨dotCondFormula, dotCondResult, 3,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 2).stamp 0⟩] := by
  have hi : 2 - 1 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  rw [extractNodeReqs, bfsLabelAt_requests (dotTree (K := K)) 2 hi]
  have hget : (bfsRows (dotTree (K := K)))[1] = (dotCondTree (K := K)).label := by
    simp [dot_bfsRows]
  rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 2).stamp 0 g.requests) hget]
  simp [dotCondTree, skelNode, extractNodeReqsAux_cons1]

theorem extractNodeReqs_bfsLabelAt_op2 :
    extractNodeReqs (bfsLabelAt (dotTree (K := K)) 3) =
      [⟨dotThenFormula, dotThenTail, 3,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 3).stamp 0⟩,
       ⟨dotThenTail, dotOp2B, 2,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 3).stamp 1⟩] := by
  have hi : 3 - 1 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  rw [extractNodeReqs, bfsLabelAt_requests (dotTree (K := K)) 3 hi]
  have hget : (bfsRows (dotTree (K := K)))[2] = (dotOp2Tree (K := K)).label := by
    simp [dot_bfsRows]
  rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 3).stamp 0 g.requests) hget]
  simp [dotOp2Tree, skelNode, extractNodeReqsAux_cons2]

theorem extractNodeReqs_bfsLabelAt_op1b :
    extractNodeReqs (bfsLabelAt (dotTree (K := K)) 4) =
      [⟨dotOp2B, dotOp2Sf1, 3,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 4).stamp 0⟩] := by
  have hi : 4 - 1 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  rw [extractNodeReqs, bfsLabelAt_requests (dotTree (K := K)) 4 hi]
  have hget : (bfsRows (dotTree (K := K)))[3] = (dotOp1BTree (K := K)).label := by
    simp [dot_bfsRows]
  rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 4).stamp 0 g.requests) hget]
  simp [dotOp1BTree, skelNode, extractNodeReqsAux_cons1]

theorem extractNodeReqs_bfsLabelAt_op1c :
    extractNodeReqs (bfsLabelAt (dotTree (K := K)) 5) =
      [⟨dotOp2C, dotOp2Sf2, 3,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 5).stamp 0⟩] := by
  have hi : 5 - 1 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  rw [extractNodeReqs, bfsLabelAt_requests (dotTree (K := K)) 5 hi]
  have hget : (bfsRows (dotTree (K := K)))[4] = (dotOp1CTree (K := K)).label := by
    simp [dot_bfsRows]
  rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 5).stamp 0 g.requests) hget]
  simp [dotOp1CTree, skelNode, extractNodeReqsAux_cons1]

theorem extractNodeReqs_bfsLabelAt_op9 :
    extractNodeReqs (bfsLabelAt (dotTree (K := K)) 6) =
      [⟨dotOp9Formula, dotOp9Tail, 3,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 0⟩,
       ⟨dotOp9Tail, .atom 2, 2,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 1⟩,
       ⟨dotCore, dotArm, 2,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 2⟩] := by
  have hi : 6 - 1 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  rw [extractNodeReqs, bfsLabelAt_requests (dotTree (K := K)) 6 hi]
  have hget : (bfsRows (dotTree (K := K)))[5] = (dotOp9Tree (K := K)).label := by
    simp [dot_bfsRows]
  rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 6).stamp 0 g.requests) hget]
  simp [dotOp9Tree, skelNode, extractNodeReqsAux_cons3]

theorem extractNodeReqs_bfsLabelAt_core :
    extractNodeReqs (bfsLabelAt (dotTree (K := K)) 7) =
      [⟨dotCoreFormula, dotCore, 3,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 7).stamp 0⟩] := by
  have hi : 7 - 1 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  rw [extractNodeReqs, bfsLabelAt_requests (dotTree (K := K)) 7 hi]
  have hget : (bfsRows (dotTree (K := K)))[6] = (dotOp9CoreTree (K := K)).label := by
    simp [dot_bfsRows]
  rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 7).stamp 0 g.requests) hget]
  simp [dotOp9CoreTree, skelNode, extractNodeReqsAux_cons1]

theorem extractNodeReqs_bfsLabelAt_invoke :
    extractNodeReqs (bfsLabelAt (dotTree (K := K)) 8) =
      [⟨dotArm, dotResult, 3,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 8).stamp 0⟩] := by
  have hi : 8 - 1 < (bfsRows (dotTree (K := K))).length := by simp [dot_bfsRows]
  rw [extractNodeReqs, bfsLabelAt_requests (dotTree (K := K)) 8 hi]
  have hget : (bfsRows (dotTree (K := K)))[7] = (dotOp9InvokeTree (K := K)).label := by
    simp [dot_bfsRows]
  rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 8).stamp 0 g.requests) hget]
  simp [dotOp9InvokeTree, skelNode, extractNodeReqsAux_cons1]

theorem genRowMemForest_dotTree_assigned_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsAssign (dotTree (K := K))).label)) = 86 := by
  rw [extractNodeReqs_dot_root]
  simp [dotFormula, dotParentTail, dotBranchPair]
  rw [genRowMemForest_three_chain32_size]
  simp [nounWalkSize, nounWalkSize_dotCondFormula,
    nounWalkSize_dotThenFormula, nounWalkSize_dotElseFormula]

theorem genRowMemForest_dotTree_assigned_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsAssign (dotTree (K := K))).label)).length = 2 := by
  rw [extractNodeReqs_dot_root]
  simp [dotFormula, dotParentTail, dotBranchPair]
  exact genRowMemForest_three_chain32_length (encC z) z α
    (.atom 6) dotCondFormula dotBranchPair dotThenFormula dotElseFormula
    _ _ _

theorem genRowMemForest_bfsLabelAt_cond_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTree (K := K)) 2))) = 5 := by
  rw [extractNodeReqs_bfsLabelAt_cond]
  simp [dotCondFormula, dotCondResult]
  rw [genRowMemForest_singleton_axis3_size]
  simp [nounWalkSize]

theorem genRowMemForest_bfsLabelAt_op1b_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTree (K := K)) 4))) = 7 := by
  rw [extractNodeReqs_bfsLabelAt_op1b]
  simp [dotOp2B, dotOp2Sf1]
  rw [genRowMemForest_singleton_axis3_size]
  simp [nounWalkSize]

theorem genRowMemForest_bfsLabelAt_op1c_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTree (K := K)) 5))) = 17 := by
  rw [extractNodeReqs_bfsLabelAt_op1c]
  simp [dotOp2C, dotOp2Sf2]
  rw [genRowMemForest_singleton_axis3_size]
  simp [nounWalkSize, nounWalkSize_dotOp9Formula]

theorem genRowMemForest_bfsLabelAt_core_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTree (K := K)) 7))) = 11 := by
  rw [extractNodeReqs_bfsLabelAt_core]
  simp [dotCoreFormula]
  rw [genRowMemForest_singleton_axis3_size]
  simp [nounWalkSize, nounWalkSize_dotCore]

theorem genRowMemForest_bfsLabelAt_invoke_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTree (K := K)) 8))) = 5 := by
  rw [extractNodeReqs_bfsLabelAt_invoke]
  simp [dotArm, dotElem0, dotResult]
  rw [genRowMemForest_singleton_axis3_size]
  simp [nounWalkSize]

theorem genRowMemForest_bfsLabelAt_op2_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTree (K := K)) 3))) = 27 := by
  rw [extractNodeReqs_bfsLabelAt_op2]
  simp [dotThenFormula, dotThenTail]
  rw [genRowMemForest_chain32_size]
  simp [nounWalkSize, nounWalkSize_dotOp2B, nounWalkSize_dotOp2C]

theorem genRowMemForest_bfsLabelAt_op9_size (z α : K) :
    totalSize (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTree (K := K)) 6))) = 26 := by
  rw [extractNodeReqs_bfsLabelAt_op9]
  simp [dotOp9Formula, dotOp9Tail, dotCore, dotArm]
  rw [genRowMemForest_three_chain32_size]
  simp [nounWalkSize, nounWalkSize_dotCoreFormula, nounWalkSize_dotElem0,
    nounWalkSize_dotElem1]

theorem genRowMemForest_bfsLabelAt_cond_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTree (K := K)) 2))).length = 1 := by
  rw [extractNodeReqs_bfsLabelAt_cond, genRowMemForest_singleton]
  simp

theorem genRowMemForest_bfsLabelAt_op1b_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTree (K := K)) 4))).length = 1 := by
  rw [extractNodeReqs_bfsLabelAt_op1b, genRowMemForest_singleton]
  simp

theorem genRowMemForest_bfsLabelAt_op1c_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTree (K := K)) 5))).length = 1 := by
  rw [extractNodeReqs_bfsLabelAt_op1c, genRowMemForest_singleton]
  simp

theorem genRowMemForest_bfsLabelAt_core_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTree (K := K)) 7))).length = 1 := by
  rw [extractNodeReqs_bfsLabelAt_core, genRowMemForest_singleton]
  simp

theorem genRowMemForest_bfsLabelAt_invoke_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTree (K := K)) 8))).length = 1 := by
  rw [extractNodeReqs_bfsLabelAt_invoke, genRowMemForest_singleton]
  simp

theorem genRowMemForest_bfsLabelAt_op2_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTree (K := K)) 3))).length = 1 := by
  rw [extractNodeReqs_bfsLabelAt_op2]
  exact genRowMemForest_chain_length (encC z) z α _ _ rfl

theorem genRowMemForest_bfsLabelAt_op9_length (z α : K) :
    (genRowMemForest (encC z) z α lmb
      (extractNodeReqs (bfsLabelAt (dotTree (K := K)) 6))).length = 2 := by
  rw [extractNodeReqs_bfsLabelAt_op9]
  simp [dotOp9Formula, dotOp9Tail, dotCore, dotArm]
  exact genRowMemForest_three_chain32_length (encC z) z α
    (.atom 9) (.atom 2) dotCoreFormula dotElem0 dotElem1 _ _ _

theorem genMemForestFromTree_dotBuild_leaf_length (z α : K) (i : ℕ)
    (hch : (dotBuild (K := K) i).children = [])
    (r : MemRecordReq)
    (h : extractNodeReqs (dotBuild (K := K) i).label = [r]) :
    (genMemForestFromTree (encC z) z α lmb (dotBuild (K := K) i)).length = 1 := by
  rw [show dotBuild (K := K) i = .node (dotBuild (K := K) i).label
        (dotBuild (K := K) i).children from by cases dotBuild (K := K) i; rfl,
    hch, genMemForestFromTree_leaf, h, genRowMemForest_singleton]
  simp

theorem genMemForestFromTree_dotBuild_2_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (dotBuild (K := K) 2)).length = 1 := by
  have h : extractNodeReqs (dotBuild (K := K) 2).label =
      [⟨dotCondFormula, dotCondResult, 3,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 2).stamp 0⟩] := by
    rw [dotBuild_label, extractNodeReqs_bfsLabelAt_cond]
  exact genMemForestFromTree_dotBuild_leaf_length z α 2 dotBuild_2_children _ h

theorem genMemForestFromTree_dotBuild_4_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (dotBuild (K := K) 4)).length = 1 := by
  have h : extractNodeReqs (dotBuild (K := K) 4).label =
      [⟨dotOp2B, dotOp2Sf1, 3,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 4).stamp 0⟩] := by
    rw [dotBuild_label, extractNodeReqs_bfsLabelAt_op1b]
  exact genMemForestFromTree_dotBuild_leaf_length z α 4 dotBuild_4_children _ h

theorem genMemForestFromTree_dotBuild_5_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (dotBuild (K := K) 5)).length = 1 := by
  have h : extractNodeReqs (dotBuild (K := K) 5).label =
      [⟨dotOp2C, dotOp2Sf2, 3,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 5).stamp 0⟩] := by
    rw [dotBuild_label, extractNodeReqs_bfsLabelAt_op1c]
  exact genMemForestFromTree_dotBuild_leaf_length z α 5 dotBuild_5_children _ h

theorem genMemForestFromTree_dotBuild_7_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (dotBuild (K := K) 7)).length = 1 := by
  have h : extractNodeReqs (dotBuild (K := K) 7).label =
      [⟨dotCoreFormula, dotCore, 3,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 7).stamp 0⟩] := by
    rw [dotBuild_label, extractNodeReqs_bfsLabelAt_core]
  exact genMemForestFromTree_dotBuild_leaf_length z α 7 dotBuild_7_children _ h

theorem genMemForestFromTree_dotBuild_8_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (dotBuild (K := K) 8)).length = 1 := by
  have h : extractNodeReqs (dotBuild (K := K) 8).label =
      [⟨dotArm, dotResult, 3,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 8).stamp 0⟩] := by
    rw [dotBuild_label, extractNodeReqs_bfsLabelAt_invoke]
  exact genMemForestFromTree_dotBuild_leaf_length z α 8 dotBuild_8_children _ h

theorem genMemForestFromTree_dotBuild_6_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (dotBuild (K := K) 6)).length = 4 := by
  rw [show dotBuild (K := K) 6 = .node (dotBuild (K := K) 6).label
        (dotBuild (K := K) 6).children from by cases dotBuild (K := K) 6; rfl,
    genMemForestFromTree_node, dotBuild_6_children, List.length_append,
    genMemForestFromList_cons, genMemForestFromList_cons, genMemForestFromList_nil,
    List.length_append, List.length_append, List.length_nil, dotBuild_label,
    genRowMemForest_bfsLabelAt_op9_length, genMemForestFromTree_dotBuild_7_length,
    genMemForestFromTree_dotBuild_8_length]

theorem genMemForestFromTree_dotBuild_3_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (dotBuild (K := K) 3)).length = 7 := by
  rw [show dotBuild (K := K) 3 = .node (dotBuild (K := K) 3).label
        (dotBuild (K := K) 3).children from by cases dotBuild (K := K) 3; rfl,
    genMemForestFromTree_node, dotBuild_3_children, List.length_append,
    genMemForestFromList_cons, genMemForestFromList_cons, genMemForestFromList_cons,
    genMemForestFromList_nil, List.length_append, List.length_append,
    List.length_append, List.length_nil, dotBuild_label,
    genRowMemForest_bfsLabelAt_op2_length, genMemForestFromTree_dotBuild_4_length,
    genMemForestFromTree_dotBuild_5_length, genMemForestFromTree_dotBuild_6_length]

theorem dotMemForest_assigned_length (z α : K) :
    (genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTree (K := K)))).length = 10 := by
  rw [bfsAssign_dot_eq_node, genMemForestFromTree_node, List.length_append,
    bfsAssign_dot_children, genMemForestFromList_cons, genMemForestFromList_cons,
    genMemForestFromList_nil, List.length_append, List.length_append, List.length_nil,
    genRowMemForest_dotTree_assigned_length, genMemForestFromTree_dotBuild_2_length,
    genMemForestFromTree_dotBuild_3_length]

theorem genMemForestFromTree_dotBuild_leaf_size (z α : K) (i : ℕ)
    (hch : (dotBuild (K := K) i).children = [])
    (hd tl : Noun) (e : ℕ)
    (h : extractNodeReqs (dotBuild (K := K) i).label = [⟨.cell hd tl, tl, 3, e⟩]) :
    totalSize (genMemForestFromTree (encC z) z α lmb (dotBuild (K := K) i)) =
      3 + nounWalkSize hd + nounWalkSize tl := by
  rw [show dotBuild (K := K) i = .node (dotBuild (K := K) i).label
        (dotBuild (K := K) i).children from by cases dotBuild (K := K) i; rfl,
    hch, genMemForestFromTree_leaf_axis3_size (encC z) z α _ hd tl e h]

theorem genMemForestFromTree_dotBuild_2_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (dotBuild (K := K) 2)) = 5 := by
  have hreq : extractNodeReqs (dotBuild (K := K) 2).label =
      [⟨.cell (.atom 1) (.atom 0), .atom 0, 3,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 2).stamp 0⟩] := by
    rw [dotBuild_label, extractNodeReqs_bfsLabelAt_cond]
    simp [dotCondFormula, dotCondResult]
  rw [genMemForestFromTree_dotBuild_leaf_size z α 2 dotBuild_2_children _ _ _ hreq]
  simp [nounWalkSize]

theorem genMemForestFromTree_dotBuild_4_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (dotBuild (K := K) 4)) = 7 := by
  have hreq : extractNodeReqs (dotBuild (K := K) 4).label =
      [⟨.cell (.atom 1) (.cell (.atom 0) (.atom 1)), .cell (.atom 0) (.atom 1), 3,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 4).stamp 0⟩] := by
    rw [dotBuild_label, extractNodeReqs_bfsLabelAt_op1b]
    simp [dotOp2B, dotOp2Sf1]
  rw [genMemForestFromTree_dotBuild_leaf_size z α 4 dotBuild_4_children _ _ _ hreq]
  simp [nounWalkSize]

theorem genMemForestFromTree_dotBuild_5_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (dotBuild (K := K) 5)) = 17 := by
  have hreq : extractNodeReqs (dotBuild (K := K) 5).label =
      [⟨.cell (.atom 1) dotOp9Formula, dotOp9Formula, 3,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 5).stamp 0⟩] := by
    rw [dotBuild_label, extractNodeReqs_bfsLabelAt_op1c]
    simp [dotOp2C, dotOp2Sf2]
  rw [genMemForestFromTree_dotBuild_leaf_size z α 5 dotBuild_5_children _ _ _ hreq]
  simp [nounWalkSize, nounWalkSize_dotOp9Formula]

theorem genMemForestFromTree_dotBuild_7_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (dotBuild (K := K) 7)) = 11 := by
  have hreq : extractNodeReqs (dotBuild (K := K) 7).label =
      [⟨.cell (.atom 1) dotCore, dotCore, 3,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 7).stamp 0⟩] := by
    rw [dotBuild_label, extractNodeReqs_bfsLabelAt_core]
    simp [dotCoreFormula]
  rw [genMemForestFromTree_dotBuild_leaf_size z α 7 dotBuild_7_children _ _ _ hreq]
  simp [nounWalkSize, nounWalkSize_dotCore]

theorem genMemForestFromTree_dotBuild_8_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (dotBuild (K := K) 8)) = 5 := by
  have hreq : extractNodeReqs (dotBuild (K := K) 8).label =
      [⟨.cell (.atom 1) (.atom 3), .atom 3, 3,
          getRecordExp (bfsLabelAt (dotTree (K := K)) 8).stamp 0⟩] := by
    rw [dotBuild_label, extractNodeReqs_bfsLabelAt_invoke]
    simp [dotArm, dotElem0, dotResult]
  rw [genMemForestFromTree_dotBuild_leaf_size z α 8 dotBuild_8_children _ _ _ hreq]
  simp [nounWalkSize]

theorem genMemForestFromTree_dotBuild_6_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (dotBuild (K := K) 6)) = 42 := by
  rw [show dotBuild (K := K) 6 = .node (dotBuild (K := K) 6).label
        (dotBuild (K := K) 6).children from by cases dotBuild (K := K) 6; rfl,
    genMemForestFromTree_node, totalSize_append, dotBuild_6_children,
    genMemForestFromList_cons, genMemForestFromList_cons, genMemForestFromList_nil,
    totalSize_append, totalSize_append, dotBuild_label]
  have hnil : totalSize ([] : List (NTree (GenMemoryRow K))) = 0 := rfl
  rw [genRowMemForest_bfsLabelAt_op9_size, genMemForestFromTree_dotBuild_7_size,
    genMemForestFromTree_dotBuild_8_size, hnil]

theorem genMemForestFromTree_dotBuild_3_size (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (dotBuild (K := K) 3)) = 93 := by
  rw [show dotBuild (K := K) 3 = .node (dotBuild (K := K) 3).label
        (dotBuild (K := K) 3).children from by cases dotBuild (K := K) 3; rfl,
    genMemForestFromTree_node, totalSize_append, dotBuild_3_children,
    genMemForestFromList_cons, genMemForestFromList_cons, genMemForestFromList_cons,
    genMemForestFromList_nil, totalSize_append, totalSize_append, totalSize_append,
    dotBuild_label]
  have hnil : totalSize ([] : List (NTree (GenMemoryRow K))) = 0 := rfl
  rw [genRowMemForest_bfsLabelAt_op2_size, genMemForestFromTree_dotBuild_4_size,
    genMemForestFromTree_dotBuild_5_size, genMemForestFromTree_dotBuild_6_size, hnil]

theorem dotMemForest_assigned_totalSize (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTree (K := K)))) = 184 := by
  rw [bfsAssign_dot_eq_node, genMemForestFromTree_node, totalSize_append,
    bfsAssign_dot_children, genMemForestFromList_cons, genMemForestFromList_cons,
    genMemForestFromList_nil, totalSize_append, totalSize_append]
  have hnil : totalSize ([] : List (NTree (GenMemoryRow K))) = 0 := rfl
  rw [genRowMemForest_dotTree_assigned_size, genMemForestFromTree_dotBuild_2_size,
    genMemForestFromTree_dotBuild_3_size, hnil]

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genRowMemForest_three_chain32_size
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotMemForest_unassigned_length
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotMemForest_unassigned_totalSize
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotMemForest_assigned_length
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotMemForest_assigned_totalSize
