import Nock.RedTeam.Batch1571Thm54ZeroBinderShapes
import Nock.NockVMROM.Thm54.TraceGen.Op2Gen
import Nock.NockVMROM.Thm54.TraceGen.Op5Gen
import Nock.NockVMROM.Thm54.TraceGen.Op6Gen
import Nock.NockVMROM.Thm54.TraceGen.Op7Gen
import Nock.NockVMROM.Thm54.TraceGen.Op8Gen
import Nock.NockVMROM.Thm54.TraceGen.Op9Gen

/-
  Nock/RedTeam/Batch1572Thm54ZeroBinderRows97.lean

  Tree facts are computed from the generator's
  own `genComputeSkeleton` output (`romTree_spec`); nothing is a premise.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Nock.RedTeam.Batch1572

open Nock Nock.Walk Nock.MemoryTable
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam.Batch1571

local instance fact97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype (GaloisField 97 3) := Fintype.ofFinite _
noncomputable local instance : DecidableEq (GaloisField 97 3) := Classical.decEq _
local instance : CharP (GaloisField 97 3) (ringChar (GaloisField 97 3)) := ringChar.charP _

theorem orderOf_five97 : orderOf (5 : ZMod 97) = 96 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  decide

section
variable {K : Type} [Field K]

/-! ### OP1: `*[0 [1 5]] = 5` -/
abbrev s1 : Noun := .atom 0
abbrev f1 : Noun := .cell (.atom 1) (.atom 5)
abbrev T1 : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp1 s1 f1 (.atom 5) (.atom 1)) [⟨f1, .atom 5, 3, 0⟩]) []

theorem gen1 : genComputeSkeleton (K := K) 1 s1 f1 = .ok (T1, .atom 5) := by
  simp [genComputeSkeleton]

theorem evalRom1 : evalRom 1 s1 f1 = some (.atom 5) := by simp [evalRom]

theorem romTree1 (h : evalRom 1 s1 f1 = some (.atom 5)) : romTree (K := K) h = T1 := by
  have hs := romTree_spec (K := K) h
  rw [gen1] at hs
  injection hs with hs
  exact (Prod.mk.inj hs).1.symm

theorem air1 : airReorder (T1 (K := K)) = T1 := by
  simp [airReorder, skelNode, genSkelOp1, airNeedsSwap]

theorem bfsRows1 : bfsRows (T1 (K := K)) =
    [skelNode (genSkelOp1 s1 f1 (.atom 5) (.atom 1)) [⟨f1, .atom 5, 3, 0⟩]] := by
  simp [bfsRows, bfsForest_node_nil]
theorem acc1 : programAcc (T1 (K := K)) = 1 := by
  rw [programAcc, air1, bfsRows1]; simp [accAt, bfsRows1, skelNode, genSkelOp1, Framework.recordCount]
theorem comp1 : programCompRows (T1 (K := K)) = 1 := by
  rw [programCompRows, air1, bfsRows1]; rfl
theorem leaf1 : programLeafBound (airReorder (T1 (K := K))) = 2 := by
  rw [air1, programLeafBound, bfsRows1]; simp [rowNounsBound, skelNode, genSkelOp1, Noun.leaves]

theorem memRows1 (lmb z α : K) : programMemRowsL lmb z α (T1 (K := K)) = 5 := by
  simp only [programMemRowsL, genMemoryForest]
  rw [bfsForest_length, threadGenForest_totalSize, air1]
  rw [show (T1 : NTree (GenComputeRow K)) = NTree.node _ [] from rfl, bfsAssign_node_nil]
  simp only [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux, skelNode,
    Walk.totalSize_append, List.append_nil, f1]
  simp only [genRowMemForest_singleton_axis3_size]
  simp [nounWalkSize]

theorem memRoots1 (lmb z α : K) : programMemRootsL lmb z α (T1 (K := K)) = 1 := by
  simp only [programMemRootsL, genMemoryForest]
  rw [threadGenForest_length, air1]
  rw [show (T1 : NTree (GenComputeRow K)) = NTree.node _ [] from rfl, bfsAssign_node_nil]
  simp [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux, skelNode,
    genRowMemForest]

/-! ### OP0 and OP4/OP3 over an OP0 child, subject `[7 9]` -/
abbrev sB : Noun := .cell (.atom 7) (.atom 9)
abbrev f0B : Noun := .cell (.atom 0) (.atom 2)
abbrev T0 : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp0 sB f0B (.atom 0) (.atom 2) (.atom 7) 2)
     [⟨f0B, .atom 2, 3, 0⟩, ⟨sB, .atom 7, 2, 0⟩]) []

theorem gen0 : genComputeSkeleton (K := K) 1 sB f0B = .ok (T0, .atom 7) := by
  simp [genComputeSkeleton, Nock.Noun.slot]
theorem evalRom0 : evalRom 1 sB f0B = some (.atom 7) := by
  simp [evalRom, Nock.Noun.slot]
theorem romTree0 (h : evalRom 1 sB f0B = some (.atom 7)) : romTree (K := K) h = T0 := by
  have hs := romTree_spec (K := K) h
  rw [gen0] at hs
  injection hs with hs
  exact (Prod.mk.inj hs).1.symm
theorem air0 : airReorder (T0 (K := K)) = T0 := by
  simp [airReorder, skelNode, genSkelOp0, airNeedsSwap]
theorem acc0 : programAcc (T0 (K := K)) = 2 := by
  rw [programAcc, air0]; simp [accAt, bfsRows, bfsForest_node_nil, skelNode, genSkelOp0, Framework.recordCount]
theorem comp0 : programCompRows (T0 (K := K)) = 1 := by
  rw [programCompRows, air0]; simp [bfsRows, bfsForest_node_nil]
theorem leaf0 : programLeafBound (airReorder (T0 (K := K))) = 2 := by
  rw [air0, programLeafBound]; simp [bfsRows, bfsForest_node_nil, rowNounsBound, skelNode, genSkelOp0, Noun.leaves]
theorem memRows0 (lmb z α : K) : programMemRowsL lmb z α (T0 (K := K)) = 10 := by
  simp only [programMemRowsL, genMemoryForest]
  rw [bfsForest_length, threadGenForest_totalSize, air0]
  rw [show (T0 : NTree (GenComputeRow K)) = NTree.node _ [] from rfl, bfsAssign_node_nil]
  simp [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux,
    genRowMemForest, skelNode, genSkelOp0, Walk.totalSize_append]
  simp [totalSize, genAnnotatedRecordTree_size, recordTreeSize_axis3, recordTreeSize_axis2, nounWalkSize]
theorem memRoots0 (lmb z α : K) : programMemRootsL lmb z α (T0 (K := K)) = 2 := by
  simp only [programMemRootsL, genMemoryForest]
  rw [threadGenForest_length, air0]
  rw [show (T0 : NTree (GenComputeRow K)) = NTree.node _ [] from rfl, bfsAssign_node_nil]
  simp [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux,
    genRowMemForest, skelNode, genSkelOp0]

/-! ### OP4[OP0]: `*[[7 9] [4 [0 2]]] = 8` -/
abbrev fB : Noun := .cell (.atom 4) f0B
abbrev TB : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp4 sB fB (.atom 4) f0B sB f0B (.atom 7) (.atom 8)) [⟨fB, f0B, 3, 0⟩]) [T0]

theorem genB : genComputeSkeleton (K := K) 2 sB fB = .ok (TB, .atom 8) := by
  simp [genComputeSkeleton, Nock.Noun.slot, Nock.Noun.lus, Noun.wut]

theorem evalRomB : evalRom 2 sB fB = some (.atom 8) := by
  simp [evalRom, Nock.Noun.slot, Nock.Noun.lus, Noun.wut]

theorem romTreeB (h : evalRom 2 sB fB = some (.atom 8)) : romTree (K := K) h = TB := by
  have hs := romTree_spec (K := K) h
  rw [genB] at hs
  injection hs with hs
  exact (Prod.mk.inj hs).1.symm

theorem airB : airReorder (TB (K := K)) = TB := by
  simp [airReorder, skelNode, genSkelOp0, genSkelOp4, airNeedsSwap, swapPair]

theorem accB : programAcc (TB (K := K)) = 3 := by
  rw [programAcc, airB]; simp [accAt, bfsRows_one_leaf, skelNode, genSkelOp0, genSkelOp4, Framework.recordCount]
theorem compB : programCompRows (TB (K := K)) = 2 := by
  rw [programCompRows, airB]; simp [bfsRows_one_leaf]
theorem leafB : programLeafBound (airReorder (TB (K := K))) = 3 := by
  rw [airB, programLeafBound]; simp [bfsRows_one_leaf, rowNounsBound, skelNode, genSkelOp0, genSkelOp4, Noun.leaves]

theorem memRowsB (lmb z α : K) : programMemRowsL lmb z α (TB (K := K)) = 17 := by
  simp only [programMemRowsL, genMemoryForest]
  rw [bfsForest_length, threadGenForest_totalSize, airB]
  rw [show (TB : NTree (GenComputeRow K)) = NTree.node _ [T0] from rfl, bfsAssign_one_leaf]
  simp [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux,
    genRowMemForest, skelNode, genSkelOp0, genSkelOp4, Walk.totalSize_append]
  simp [totalSize, genAnnotatedRecordTree_size, recordTreeSize_axis3, recordTreeSize_axis2, nounWalkSize]

theorem memRootsB (lmb z α : K) : programMemRootsL lmb z α (TB (K := K)) = 3 := by
  simp only [programMemRootsL, genMemoryForest]
  rw [threadGenForest_length, airB]
  rw [show (TB : NTree (GenComputeRow K)) = NTree.node _ [T0] from rfl, bfsAssign_one_leaf]
  simp [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux,
    genRowMemForest, skelNode, genSkelOp0, genSkelOp4]

/-! ### OP3[OP0]: `*[[7 9] [3 [0 2]]] = 1` -/
abbrev fC : Noun := .cell (.atom 3) f0B
abbrev TC : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp3 sB fC (.atom 3) f0B sB f0B (.atom 7) (.atom 1)) [⟨fC, f0B, 3, 0⟩]) [T0]

theorem genC : genComputeSkeleton (K := K) 2 sB fC = .ok (TC, .atom 1) := by
  simp [genComputeSkeleton, Nock.Noun.slot, Nock.Noun.lus, Noun.wut]

theorem evalRomC : evalRom 2 sB fC = some (.atom 1) := by
  simp [evalRom, Nock.Noun.slot, Nock.Noun.lus, Noun.wut]

theorem romTreeC (h : evalRom 2 sB fC = some (.atom 1)) : romTree (K := K) h = TC := by
  have hs := romTree_spec (K := K) h
  rw [genC] at hs
  injection hs with hs
  exact (Prod.mk.inj hs).1.symm

theorem airC : airReorder (TC (K := K)) = TC := by
  simp [airReorder, skelNode, genSkelOp0, genSkelOp3, airNeedsSwap, swapPair]

theorem accC : programAcc (TC (K := K)) = 3 := by
  rw [programAcc, airC]; simp [accAt, bfsRows_one_leaf, skelNode, genSkelOp0, genSkelOp3, Framework.recordCount]
theorem compC : programCompRows (TC (K := K)) = 2 := by
  rw [programCompRows, airC]; simp [bfsRows_one_leaf]
theorem leafC : programLeafBound (airReorder (TC (K := K))) = 3 := by
  rw [airC, programLeafBound]; simp [bfsRows_one_leaf, rowNounsBound, skelNode, genSkelOp0, genSkelOp3, Noun.leaves]

theorem memRowsC (lmb z α : K) : programMemRowsL lmb z α (TC (K := K)) = 17 := by
  simp only [programMemRowsL, genMemoryForest]
  rw [bfsForest_length, threadGenForest_totalSize, airC]
  rw [show (TC : NTree (GenComputeRow K)) = NTree.node _ [T0] from rfl, bfsAssign_one_leaf]
  simp [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux,
    genRowMemForest, skelNode, genSkelOp0, genSkelOp3, Walk.totalSize_append]
  simp [totalSize, genAnnotatedRecordTree_size, recordTreeSize_axis3, recordTreeSize_axis2, nounWalkSize]

theorem memRootsC (lmb z α : K) : programMemRootsL lmb z α (TC (K := K)) = 3 := by
  simp only [programMemRootsL, genMemoryForest]
  rw [threadGenForest_length, airC]
  rw [show (TC : NTree (GenComputeRow K)) = NTree.node _ [T0] from rfl, bfsAssign_one_leaf]
  simp [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux,
    genRowMemForest, skelNode, genSkelOp0, genSkelOp3]

/-! ### OP5 -/
abbrev T5 : NTree (GenComputeRow K) := .node (skelNode
            (genSkelOp5 op5Subject op5ParentFormula (.atom 5) op5ParentTail op5ChildFormulaB
              op5ChildFormulaC op5Sf1 op5Sf2 op5Result)
            [⟨op5ParentFormula, op5ParentTail, 3, 0⟩, ⟨op5ParentTail, op5ChildFormulaB, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op5Subject op5ChildFormulaB op5Sf1 (.atom 1))
                [⟨op5ChildFormulaB, op5Sf1, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op5Subject op5ChildFormulaC op5Sf2 (.atom 1))
                [⟨op5ChildFormulaC, op5Sf2, 3, 0⟩]) []]

theorem gen5 : genComputeSkeleton (K := K) 2 op5Subject op5ParentFormula = .ok (T5, op5Result) :=
  genComputeSkeleton_op5 0

theorem evalRom5 : evalRom 2 op5Subject op5ParentFormula = some op5Result := by
  simp [evalRom, op5Subject, op5ParentFormula, op5ParentTail, op5ChildFormulaB, op5ChildFormulaC, op5Sf1, op5Sf2, op5Result, Nock.Noun.slot, Nock.Noun.lus, Noun.tis]

theorem romTree5 (h : evalRom 2 op5Subject op5ParentFormula = some op5Result) : romTree (K := K) h = T5 := by
  have hs := romTree_spec (K := K) h
  rw [gen5] at hs
  injection hs with hs
  exact (Prod.mk.inj hs).1.symm

theorem air5 : airReorder (T5 (K := K)) = T5 := by
  simp [airReorder, skelNode, genSkelOp1, genSkelOp5, airNeedsSwap]

theorem acc5 : programAcc (T5 (K := K)) = 4 := by
  rw [programAcc, air5]; simp [accAt, bfsRows_two_leaves, skelNode, genSkelOp1, genSkelOp5, Framework.recordCount]
theorem comp5 : programCompRows (T5 (K := K)) = 3 := by
  rw [programCompRows, air5]; simp [bfsRows_two_leaves]
theorem leaf5 : programLeafBound (airReorder (T5 (K := K))) = 5 := by
  rw [air5, programLeafBound]
  simp [bfsRows_two_leaves, rowNounsBound, skelNode, genSkelOp1, genSkelOp5, Noun.leaves, op5Subject, op5ParentFormula, op5ParentTail, op5ChildFormulaB, op5ChildFormulaC, op5Sf1, op5Sf2, op5Result]

theorem memRows5 (lmb z α : K) : programMemRowsL lmb z α (T5 (K := K)) = 23 := by
  simp only [programMemRowsL, genMemoryForest]
  rw [bfsForest_length, threadGenForest_totalSize, air5]
  rw [show (T5 : NTree (GenComputeRow K)) = NTree.node _ [_, _] from rfl, bfsAssign_two_leaves]
  simp only [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux, skelNode,
    Walk.totalSize_append, List.append_nil, op5Subject, op5ParentFormula, op5ParentTail, op5ChildFormulaB, op5ChildFormulaC, op5Sf1, op5Sf2, op5Result]
  simp only [genRowMemForest_chain32_size, genRowMemForest_singleton_axis3_size]
  simp [nounWalkSize]

theorem memRoots5 (lmb z α : K) : programMemRootsL lmb z α (T5 (K := K)) = 3 := by
  simp only [programMemRootsL, genMemoryForest]
  rw [threadGenForest_length, air5]
  rw [show (T5 : NTree (GenComputeRow K)) = NTree.node _ [_, _] from rfl, bfsAssign_two_leaves]
  simp only [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux, skelNode,
    List.length_append, List.append_nil, op5Subject, op5ParentFormula, op5ParentTail, op5ChildFormulaB, op5ChildFormulaC, op5Sf1, op5Sf2, op5Result]
  simp only [chain32_length, genRowMemForest_singleton, List.length_singleton]

/-! ### OP7 -/
abbrev T7 : NTree (GenComputeRow K) := .node (skelNode
            (genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail op7ChildFormulaB
              op7ChildFormulaC op7Sb op7Result)
            [⟨op7ParentFormula, op7ParentTail, 3, 0⟩, ⟨op7ParentTail, op7ChildFormulaB, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op7Subject op7ChildFormulaB op7Sb (.atom 1))
                [⟨op7ChildFormulaB, op7Sb, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op7Sb op7ChildFormulaC op7Result (.atom 1))
                [⟨op7ChildFormulaC, op7Result, 3, 0⟩]) []]
abbrev U7 : NTree (GenComputeRow K) := .node (skelNode
            (genSkelOp7 op7Subject op7ParentFormula (.atom 7) op7ParentTail op7ChildFormulaB
              op7ChildFormulaC op7Sb op7Result)
            [⟨op7ParentFormula, op7ParentTail, 3, 0⟩, ⟨op7ParentTail, op7ChildFormulaB, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op7Sb op7ChildFormulaC op7Result (.atom 1))
                [⟨op7ChildFormulaC, op7Result, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op7Subject op7ChildFormulaB op7Sb (.atom 1))
                [⟨op7ChildFormulaB, op7Sb, 3, 0⟩]) []]

theorem gen7 : genComputeSkeleton (K := K) 2 op7Subject op7ParentFormula = .ok (T7, op7Result) :=
  genComputeSkeleton_op7 0

theorem evalRom7 : evalRom 2 op7Subject op7ParentFormula = some op7Result := by
  simp [evalRom, op7Subject, op7ParentFormula, op7ParentTail, op7ChildFormulaB, op7ChildFormulaC, op7Sb, op7Result, Nock.Noun.slot, Nock.Noun.lus, Noun.tis]

theorem romTree7 (h : evalRom 2 op7Subject op7ParentFormula = some op7Result) : romTree (K := K) h = T7 := by
  have hs := romTree_spec (K := K) h
  rw [gen7] at hs
  injection hs with hs
  exact (Prod.mk.inj hs).1.symm

theorem air7 : airReorder (T7 (K := K)) = U7 := by
  simp [airReorder, skelNode, genSkelOp1, genSkelOp7, airNeedsSwap, swapPair, T7, U7]

theorem acc7 : programAcc (T7 (K := K)) = 4 := by
  rw [programAcc, air7]; simp [accAt, bfsRows_two_leaves, skelNode, genSkelOp1, genSkelOp7, Framework.recordCount]
theorem comp7 : programCompRows (T7 (K := K)) = 3 := by
  rw [programCompRows, air7]; simp [bfsRows_two_leaves]
theorem leaf7 : programLeafBound (airReorder (T7 (K := K))) = 5 := by
  rw [air7, programLeafBound]
  simp [bfsRows_two_leaves, rowNounsBound, skelNode, genSkelOp1, genSkelOp7, Noun.leaves, op7Subject, op7ParentFormula, op7ParentTail, op7ChildFormulaB, op7ChildFormulaC, op7Sb, op7Result]

theorem memRows7 (lmb z α : K) : programMemRowsL lmb z α (T7 (K := K)) = 23 := by
  simp only [programMemRowsL, genMemoryForest]
  rw [bfsForest_length, threadGenForest_totalSize, air7]
  rw [show (U7 : NTree (GenComputeRow K)) = NTree.node _ [_, _] from rfl, bfsAssign_two_leaves]
  simp only [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux, skelNode,
    Walk.totalSize_append, List.append_nil, op7Subject, op7ParentFormula, op7ParentTail, op7ChildFormulaB, op7ChildFormulaC, op7Sb, op7Result]
  simp only [genRowMemForest_chain32_size, genRowMemForest_singleton_axis3_size]
  simp [nounWalkSize]

theorem memRoots7 (lmb z α : K) : programMemRootsL lmb z α (T7 (K := K)) = 3 := by
  simp only [programMemRootsL, genMemoryForest]
  rw [threadGenForest_length, air7]
  rw [show (U7 : NTree (GenComputeRow K)) = NTree.node _ [_, _] from rfl, bfsAssign_two_leaves]
  simp only [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux, skelNode,
    List.length_append, List.append_nil, op7Subject, op7ParentFormula, op7ParentTail, op7ChildFormulaB, op7ChildFormulaC, op7Sb, op7Result]
  simp only [chain32_length, genRowMemForest_singleton, List.length_singleton]

/-! ### OP8 -/
abbrev T8 : NTree (GenComputeRow K) := .node (skelNode
            (genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail op8ChildFormulaB
              op8ChildFormulaC op8Sb op8Result)
            [⟨op8ParentFormula, op8ParentTail, 3, 0⟩, ⟨op8ParentTail, op8ChildFormulaB, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op8Subject op8ChildFormulaB op8Sb (.atom 1))
                [⟨op8ChildFormulaB, op8Sb, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op8PushedSubject op8ChildFormulaC op8Result (.atom 1))
                [⟨op8ChildFormulaC, op8Result, 3, 0⟩]) []]
abbrev U8 : NTree (GenComputeRow K) := .node (skelNode
            (genSkelOp8 op8Subject op8ParentFormula (.atom 8) op8ParentTail op8ChildFormulaB
              op8ChildFormulaC op8Sb op8Result)
            [⟨op8ParentFormula, op8ParentTail, 3, 0⟩, ⟨op8ParentTail, op8ChildFormulaB, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op8PushedSubject op8ChildFormulaC op8Result (.atom 1))
                [⟨op8ChildFormulaC, op8Result, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op8Subject op8ChildFormulaB op8Sb (.atom 1))
                [⟨op8ChildFormulaB, op8Sb, 3, 0⟩]) []]

theorem gen8 : genComputeSkeleton (K := K) 2 op8Subject op8ParentFormula = .ok (T8, op8Result) :=
  genComputeSkeleton_op8 0

theorem evalRom8 : evalRom 2 op8Subject op8ParentFormula = some op8Result := by
  simp [evalRom, op8Subject, op8ParentFormula, op8ParentTail, op8ChildFormulaB, op8ChildFormulaC, op8Sb, op8Result, op8PushedSubject, Nock.Noun.slot, Nock.Noun.lus, Noun.tis]

theorem romTree8 (h : evalRom 2 op8Subject op8ParentFormula = some op8Result) : romTree (K := K) h = T8 := by
  have hs := romTree_spec (K := K) h
  rw [gen8] at hs
  injection hs with hs
  exact (Prod.mk.inj hs).1.symm

theorem air8 : airReorder (T8 (K := K)) = U8 := by
  simp [airReorder, skelNode, genSkelOp1, genSkelOp8, airNeedsSwap, swapPair, T8, U8]

theorem acc8 : programAcc (T8 (K := K)) = 4 := by
  rw [programAcc, air8]; simp [accAt, bfsRows_two_leaves, skelNode, genSkelOp1, genSkelOp8, Framework.recordCount]
theorem comp8 : programCompRows (T8 (K := K)) = 3 := by
  rw [programCompRows, air8]; simp [bfsRows_two_leaves]
theorem leaf8 : programLeafBound (airReorder (T8 (K := K))) = 5 := by
  rw [air8, programLeafBound]
  simp [bfsRows_two_leaves, rowNounsBound, skelNode, genSkelOp1, genSkelOp8, Noun.leaves, op8Subject, op8ParentFormula, op8ParentTail, op8ChildFormulaB, op8ChildFormulaC, op8Sb, op8Result, op8PushedSubject]

theorem memRows8 (lmb z α : K) : programMemRowsL lmb z α (T8 (K := K)) = 23 := by
  simp only [programMemRowsL, genMemoryForest]
  rw [bfsForest_length, threadGenForest_totalSize, air8]
  rw [show (U8 : NTree (GenComputeRow K)) = NTree.node _ [_, _] from rfl, bfsAssign_two_leaves]
  simp only [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux, skelNode,
    Walk.totalSize_append, List.append_nil, op8Subject, op8ParentFormula, op8ParentTail, op8ChildFormulaB, op8ChildFormulaC, op8Sb, op8Result, op8PushedSubject]
  simp only [genRowMemForest_chain32_size, genRowMemForest_singleton_axis3_size]
  simp [nounWalkSize]

theorem memRoots8 (lmb z α : K) : programMemRootsL lmb z α (T8 (K := K)) = 3 := by
  simp only [programMemRootsL, genMemoryForest]
  rw [threadGenForest_length, air8]
  rw [show (U8 : NTree (GenComputeRow K)) = NTree.node _ [_, _] from rfl, bfsAssign_two_leaves]
  simp only [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux, skelNode,
    List.length_append, List.append_nil, op8Subject, op8ParentFormula, op8ParentTail, op8ChildFormulaB, op8ChildFormulaC, op8Sb, op8Result, op8PushedSubject]
  simp only [chain32_length, genRowMemForest_singleton, List.length_singleton]

/-! #### field part of `op1`: `p = 97`, `α = 5`, `h = 3` -/

theorem hrun1 : Nock.evalN 1 s1 f1 = some (.atom 5) := by
  simp [Nock.evalN, s1, f1, Nock.Noun.slot, Nock.Noun.lus, Noun.tis]

theorem hgrom1 : evalGRom 97 1 s1 f1 = some (.atom 5) := by
  simp [evalGRom, s1, f1, Nock.Noun.slot, FieldEmbedding.lusGBy, Noun.tis]

theorem hbound1 : RunBoundedBy 97 1 s1 f1 := ⟨_, hgrom1⟩
theorem hs1 : FieldEmbedding.BoundedBy 97 s1 := by
  simp [FieldEmbedding.BoundedBy, s1, f1]
theorem hf1 : FieldEmbedding.BoundedBy 97 f1 := by
  simp [FieldEmbedding.BoundedBy, s1, f1]

theorem programMemShape1 (α : K) : programMemShape α (T1 (K := K)) = 5 := by
  unfold programMemShape programMemRows; exact memRows1 0 0 α

theorem hΛp1 (h : evalRom 1 s1 f1 = some (.atom 5)) :
    programLeafBound (airReorder (romTree (K := GaloisField 97 3) h)) < 97 := by
  rw [romTree1, leaf1]; norm_num

theorem hF1 (h : evalRom 1 s1 f1 = some (.atom 5)) :
    3 * 2 ^ orbitHeight (programFit (αP 97 5) (romTree (K := GaloisField 97 3) h)) ∣ 97 - 1 := by
  rw [romTree1]
  refine dvd_of_fit_le 97 (H := 3) (by norm_num) ?_ (by norm_num)
  simp only [programFit, comp1, programMemShape1, acc1]; norm_num

theorem hwin1 (h : evalRom 1 s1 f1 = some (.atom 5)) :
    programAcc (romTree (K := GaloisField 97 3) h) + 3 < orderOf (αP 97 5) ∧
      programMemShape (αP 97 5) (romTree (K := GaloisField 97 3) h) ≤ orderOf (αP 97 5) := by
  rw [romTree1, acc1, programMemShape1, orderOf_αP, orderOf_five97]; norm_num

theorem hKsz1 (h : evalRom 1 s1 f1 = some (.atom 5)) :
    compilerKszOf (0 : GaloisField 97 3) (αP 97 5) (romTree (K := GaloisField 97 3) h) < 97 := by
  rw [romTree1]
  simp only [compilerKszOf, compilerKsz, programMemRoots, memRoots1, acc1]
  norm_num

/-- `nockCompilesHostile` at `op1` over `ZMod 97` (zero explicit binders). -/
noncomputable def b1572_op1_hostile :=
  GoodSeed.nockCompilesHostile (p := 97) (K := GaloisField 97 3) (αP 97 5) (αP 97 5) (0 : GaloisField 97 3)
    hrun1 hbound1 hs1 hf1 (hΛp1 _) (by norm_num) (by norm_num) (hK_P 97) (hF1 _)
    (hwin1 _) (hKsz1 _)

/-! #### field part of `op0`: `p = 97`, `α = 5`, `h = 4` -/

theorem hrun0 : Nock.evalN 1 sB f0B = some (.atom 7) := by
  simp [Nock.evalN, sB, f0B, Nock.Noun.slot, Nock.Noun.lus, Noun.tis]

theorem hgrom0 : evalGRom 97 1 sB f0B = some (.atom 7) := by
  simp [evalGRom, sB, f0B, Nock.Noun.slot, FieldEmbedding.lusGBy, Noun.tis]

theorem hbound0 : RunBoundedBy 97 1 sB f0B := ⟨_, hgrom0⟩
theorem hs0 : FieldEmbedding.BoundedBy 97 sB := by
  simp [FieldEmbedding.BoundedBy, sB, f0B]
theorem hf0 : FieldEmbedding.BoundedBy 97 f0B := by
  simp [FieldEmbedding.BoundedBy, sB, f0B]

theorem programMemShape0 (α : K) : programMemShape α (T0 (K := K)) = 10 := by
  unfold programMemShape programMemRows; exact memRows0 0 0 α

theorem hΛp0 (h : evalRom 1 sB f0B = some (.atom 7)) :
    programLeafBound (airReorder (romTree (K := GaloisField 97 3) h)) < 97 := by
  rw [romTree0, leaf0]; norm_num

theorem hF0 (h : evalRom 1 sB f0B = some (.atom 7)) :
    3 * 2 ^ orbitHeight (programFit (αP 97 5) (romTree (K := GaloisField 97 3) h)) ∣ 97 - 1 := by
  rw [romTree0]
  refine dvd_of_fit_le 97 (H := 4) (by norm_num) ?_ (by norm_num)
  simp only [programFit, comp0, programMemShape0, acc0]; norm_num

theorem hwin0 (h : evalRom 1 sB f0B = some (.atom 7)) :
    programAcc (romTree (K := GaloisField 97 3) h) + 3 < orderOf (αP 97 5) ∧
      programMemShape (αP 97 5) (romTree (K := GaloisField 97 3) h) ≤ orderOf (αP 97 5) := by
  rw [romTree0, acc0, programMemShape0, orderOf_αP, orderOf_five97]; norm_num

theorem hKsz0 (h : evalRom 1 sB f0B = some (.atom 7)) :
    compilerKszOf (0 : GaloisField 97 3) (αP 97 5) (romTree (K := GaloisField 97 3) h) < 97 := by
  rw [romTree0]
  simp only [compilerKszOf, compilerKsz, programMemRoots, memRoots0, acc0]
  norm_num

/-- `nockCompilesHostile` at `op0` over `ZMod 97` (zero explicit binders). -/
noncomputable def b1572_op0_hostile :=
  GoodSeed.nockCompilesHostile (p := 97) (K := GaloisField 97 3) (αP 97 5) (αP 97 5) (0 : GaloisField 97 3)
    hrun0 hbound0 hs0 hf0 (hΛp0 _) (by norm_num) (by norm_num) (hK_P 97) (hF0 _)
    (hwin0 _) (hKsz0 _)

/-! #### field part of `op4`: `p = 97`, `α = 5`, `h = 5` -/

theorem hrunB : Nock.evalN 2 sB fB = some (.atom 8) := by
  simp [Nock.evalN, sB, fB, f0B, Nock.Noun.slot, Nock.Noun.lus, Noun.tis]

theorem hgromB : evalGRom 97 2 sB fB = some (.atom 8) := by
  simp [evalGRom, sB, fB, f0B, Nock.Noun.slot, FieldEmbedding.lusGBy, Noun.tis]

theorem hboundB : RunBoundedBy 97 2 sB fB := ⟨_, hgromB⟩
theorem hsB : FieldEmbedding.BoundedBy 97 sB := by
  simp [FieldEmbedding.BoundedBy, sB, fB, f0B]
theorem hfB : FieldEmbedding.BoundedBy 97 fB := by
  simp [FieldEmbedding.BoundedBy, sB, fB, f0B]

theorem programMemShapeB (α : K) : programMemShape α (TB (K := K)) = 17 := by
  unfold programMemShape programMemRows; exact memRowsB 0 0 α

theorem hΛpB (h : evalRom 2 sB fB = some (.atom 8)) :
    programLeafBound (airReorder (romTree (K := GaloisField 97 3) h)) < 97 := by
  rw [romTreeB, leafB]; norm_num

theorem hFB (h : evalRom 2 sB fB = some (.atom 8)) :
    3 * 2 ^ orbitHeight (programFit (αP 97 5) (romTree (K := GaloisField 97 3) h)) ∣ 97 - 1 := by
  rw [romTreeB]
  refine dvd_of_fit_le 97 (H := 5) (by norm_num) ?_ (by norm_num)
  simp only [programFit, compB, programMemShapeB, accB]; norm_num

theorem hwinB (h : evalRom 2 sB fB = some (.atom 8)) :
    programAcc (romTree (K := GaloisField 97 3) h) + 3 < orderOf (αP 97 5) ∧
      programMemShape (αP 97 5) (romTree (K := GaloisField 97 3) h) ≤ orderOf (αP 97 5) := by
  rw [romTreeB, accB, programMemShapeB, orderOf_αP, orderOf_five97]; norm_num

theorem hKszB (h : evalRom 2 sB fB = some (.atom 8)) :
    compilerKszOf (0 : GaloisField 97 3) (αP 97 5) (romTree (K := GaloisField 97 3) h) < 97 := by
  rw [romTreeB]
  simp only [compilerKszOf, compilerKsz, programMemRoots, memRootsB, accB]
  norm_num

/-- `nockCompilesHostile` at `op4` over `ZMod 97` (zero explicit binders). -/
noncomputable def b1572_op4_hostile :=
  GoodSeed.nockCompilesHostile (p := 97) (K := GaloisField 97 3) (αP 97 5) (αP 97 5) (0 : GaloisField 97 3)
    hrunB hboundB hsB hfB (hΛpB _) (by norm_num) (by norm_num) (hK_P 97) (hFB _)
    (hwinB _) (hKszB _)

/-! #### field part of `op3`: `p = 97`, `α = 5`, `h = 5` -/

theorem hrunC : Nock.evalN 2 sB fC = some (.atom 1) := by
  simp [Nock.evalN, sB, fC, f0B, Nock.Noun.slot, Nock.Noun.lus, Noun.tis, Nock.Noun.wut]

theorem hgromC : evalGRom 97 2 sB fC = some (.atom 1) := by
  simp [evalGRom, sB, fC, f0B, Nock.Noun.slot, FieldEmbedding.lusGBy, Noun.tis, Nock.Noun.wut]

theorem hboundC : RunBoundedBy 97 2 sB fC := ⟨_, hgromC⟩
theorem hsC : FieldEmbedding.BoundedBy 97 sB := by
  simp [FieldEmbedding.BoundedBy, sB, fC, f0B]
theorem hfC : FieldEmbedding.BoundedBy 97 fC := by
  simp [FieldEmbedding.BoundedBy, sB, fC, f0B]

theorem programMemShapeC (α : K) : programMemShape α (TC (K := K)) = 17 := by
  unfold programMemShape programMemRows; exact memRowsC 0 0 α

theorem hΛpC (h : evalRom 2 sB fC = some (.atom 1)) :
    programLeafBound (airReorder (romTree (K := GaloisField 97 3) h)) < 97 := by
  rw [romTreeC, leafC]; norm_num

theorem hFC (h : evalRom 2 sB fC = some (.atom 1)) :
    3 * 2 ^ orbitHeight (programFit (αP 97 5) (romTree (K := GaloisField 97 3) h)) ∣ 97 - 1 := by
  rw [romTreeC]
  refine dvd_of_fit_le 97 (H := 5) (by norm_num) ?_ (by norm_num)
  simp only [programFit, compC, programMemShapeC, accC]; norm_num

theorem hwinC (h : evalRom 2 sB fC = some (.atom 1)) :
    programAcc (romTree (K := GaloisField 97 3) h) + 3 < orderOf (αP 97 5) ∧
      programMemShape (αP 97 5) (romTree (K := GaloisField 97 3) h) ≤ orderOf (αP 97 5) := by
  rw [romTreeC, accC, programMemShapeC, orderOf_αP, orderOf_five97]; norm_num

theorem hKszC (h : evalRom 2 sB fC = some (.atom 1)) :
    compilerKszOf (0 : GaloisField 97 3) (αP 97 5) (romTree (K := GaloisField 97 3) h) < 97 := by
  rw [romTreeC]
  simp only [compilerKszOf, compilerKsz, programMemRoots, memRootsC, accC]
  norm_num

/-- `nockCompilesHostile` at `op3` over `ZMod 97` (zero explicit binders). -/
noncomputable def b1572_op3_hostile :=
  GoodSeed.nockCompilesHostile (p := 97) (K := GaloisField 97 3) (αP 97 5) (αP 97 5) (0 : GaloisField 97 3)
    hrunC hboundC hsC hfC (hΛpC _) (by norm_num) (by norm_num) (hK_P 97) (hFC _)
    (hwinC _) (hKszC _)

/-! #### field part of `op5`: `p = 97`, `α = 5`, `h = 5` -/

theorem hrun5 : Nock.evalN 2 op5Subject op5ParentFormula = some op5Result := by
  simp [Nock.evalN, op5Subject, op5ParentFormula, op5ParentTail, op5ChildFormulaB, op5ChildFormulaC, op5Sf1, op5Sf2, op5Result, Nock.Noun.slot, Nock.Noun.lus, Noun.tis]

theorem hgrom5 : evalGRom 97 2 op5Subject op5ParentFormula = some op5Result := by
  simp [evalGRom, op5Subject, op5ParentFormula, op5ParentTail, op5ChildFormulaB, op5ChildFormulaC, op5Sf1, op5Sf2, op5Result, Nock.Noun.slot, FieldEmbedding.lusGBy, Noun.tis]

theorem hbound5 : RunBoundedBy 97 2 op5Subject op5ParentFormula := ⟨_, hgrom5⟩
theorem hs5 : FieldEmbedding.BoundedBy 97 op5Subject := by
  simp [FieldEmbedding.BoundedBy, op5Subject, op5ParentFormula, op5ParentTail, op5ChildFormulaB, op5ChildFormulaC, op5Sf1, op5Sf2, op5Result]
theorem hf5 : FieldEmbedding.BoundedBy 97 op5ParentFormula := by
  simp [FieldEmbedding.BoundedBy, op5Subject, op5ParentFormula, op5ParentTail, op5ChildFormulaB, op5ChildFormulaC, op5Sf1, op5Sf2, op5Result]

theorem programMemShape5 (α : K) : programMemShape α (T5 (K := K)) = 23 := by
  unfold programMemShape programMemRows; exact memRows5 0 0 α

theorem hΛp5 (h : evalRom 2 op5Subject op5ParentFormula = some op5Result) :
    programLeafBound (airReorder (romTree (K := GaloisField 97 3) h)) < 97 := by
  rw [romTree5, leaf5]; norm_num

theorem hF5 (h : evalRom 2 op5Subject op5ParentFormula = some op5Result) :
    3 * 2 ^ orbitHeight (programFit (αP 97 5) (romTree (K := GaloisField 97 3) h)) ∣ 97 - 1 := by
  rw [romTree5]
  refine dvd_of_fit_le 97 (H := 5) (by norm_num) ?_ (by norm_num)
  simp only [programFit, comp5, programMemShape5, acc5]; norm_num

theorem hwin5 (h : evalRom 2 op5Subject op5ParentFormula = some op5Result) :
    programAcc (romTree (K := GaloisField 97 3) h) + 3 < orderOf (αP 97 5) ∧
      programMemShape (αP 97 5) (romTree (K := GaloisField 97 3) h) ≤ orderOf (αP 97 5) := by
  rw [romTree5, acc5, programMemShape5, orderOf_αP, orderOf_five97]; norm_num

theorem hKsz5 (h : evalRom 2 op5Subject op5ParentFormula = some op5Result) :
    compilerKszOf (0 : GaloisField 97 3) (αP 97 5) (romTree (K := GaloisField 97 3) h) < 97 := by
  rw [romTree5]
  simp only [compilerKszOf, compilerKsz, programMemRoots, memRoots5, acc5]
  norm_num

/-- `nockCompilesHostile` at `op5` over `ZMod 97` (zero explicit binders). -/
noncomputable def b1572_op5_hostile :=
  GoodSeed.nockCompilesHostile (p := 97) (K := GaloisField 97 3) (αP 97 5) (αP 97 5) (0 : GaloisField 97 3)
    hrun5 hbound5 hs5 hf5 (hΛp5 _) (by norm_num) (by norm_num) (hK_P 97) (hF5 _)
    (hwin5 _) (hKsz5 _)

/-! #### field part of `op7`: `p = 97`, `α = 5`, `h = 5` -/

theorem hrun7 : Nock.evalN 2 op7Subject op7ParentFormula = some op7Result := by
  simp [Nock.evalN, op7Subject, op7ParentFormula, op7ParentTail, op7ChildFormulaB, op7ChildFormulaC, op7Sb, op7Result, Nock.Noun.slot, Nock.Noun.lus, Noun.tis]

theorem hgrom7 : evalGRom 97 2 op7Subject op7ParentFormula = some op7Result := by
  simp [evalGRom, op7Subject, op7ParentFormula, op7ParentTail, op7ChildFormulaB, op7ChildFormulaC, op7Sb, op7Result, Nock.Noun.slot, FieldEmbedding.lusGBy, Noun.tis]

theorem hbound7 : RunBoundedBy 97 2 op7Subject op7ParentFormula := ⟨_, hgrom7⟩
theorem hs7 : FieldEmbedding.BoundedBy 97 op7Subject := by
  simp [FieldEmbedding.BoundedBy, op7Subject, op7ParentFormula, op7ParentTail, op7ChildFormulaB, op7ChildFormulaC, op7Sb, op7Result]
theorem hf7 : FieldEmbedding.BoundedBy 97 op7ParentFormula := by
  simp [FieldEmbedding.BoundedBy, op7Subject, op7ParentFormula, op7ParentTail, op7ChildFormulaB, op7ChildFormulaC, op7Sb, op7Result]

theorem programMemShape7 (α : K) : programMemShape α (T7 (K := K)) = 23 := by
  unfold programMemShape programMemRows; exact memRows7 0 0 α

theorem hΛp7 (h : evalRom 2 op7Subject op7ParentFormula = some op7Result) :
    programLeafBound (airReorder (romTree (K := GaloisField 97 3) h)) < 97 := by
  rw [romTree7, leaf7]; norm_num

theorem hF7 (h : evalRom 2 op7Subject op7ParentFormula = some op7Result) :
    3 * 2 ^ orbitHeight (programFit (αP 97 5) (romTree (K := GaloisField 97 3) h)) ∣ 97 - 1 := by
  rw [romTree7]
  refine dvd_of_fit_le 97 (H := 5) (by norm_num) ?_ (by norm_num)
  simp only [programFit, comp7, programMemShape7, acc7]; norm_num

theorem hwin7 (h : evalRom 2 op7Subject op7ParentFormula = some op7Result) :
    programAcc (romTree (K := GaloisField 97 3) h) + 3 < orderOf (αP 97 5) ∧
      programMemShape (αP 97 5) (romTree (K := GaloisField 97 3) h) ≤ orderOf (αP 97 5) := by
  rw [romTree7, acc7, programMemShape7, orderOf_αP, orderOf_five97]; norm_num

theorem hKsz7 (h : evalRom 2 op7Subject op7ParentFormula = some op7Result) :
    compilerKszOf (0 : GaloisField 97 3) (αP 97 5) (romTree (K := GaloisField 97 3) h) < 97 := by
  rw [romTree7]
  simp only [compilerKszOf, compilerKsz, programMemRoots, memRoots7, acc7]
  norm_num

/-- `nockCompilesHostile` at `op7` over `ZMod 97` (zero explicit binders). -/
noncomputable def b1572_op7_hostile :=
  GoodSeed.nockCompilesHostile (p := 97) (K := GaloisField 97 3) (αP 97 5) (αP 97 5) (0 : GaloisField 97 3)
    hrun7 hbound7 hs7 hf7 (hΛp7 _) (by norm_num) (by norm_num) (hK_P 97) (hF7 _)
    (hwin7 _) (hKsz7 _)

/-! #### field part of `op8`: `p = 97`, `α = 5`, `h = 5` -/

theorem hrun8 : Nock.evalN 2 op8Subject op8ParentFormula = some op8Result := by
  simp [Nock.evalN, op8Subject, op8ParentFormula, op8ParentTail, op8ChildFormulaB, op8ChildFormulaC, op8Sb, op8Result, op8PushedSubject, Nock.Noun.slot, Nock.Noun.lus, Noun.tis]

theorem hgrom8 : evalGRom 97 2 op8Subject op8ParentFormula = some op8Result := by
  simp [evalGRom, op8Subject, op8ParentFormula, op8ParentTail, op8ChildFormulaB, op8ChildFormulaC, op8Sb, op8Result, op8PushedSubject, Nock.Noun.slot, FieldEmbedding.lusGBy, Noun.tis]

theorem hbound8 : RunBoundedBy 97 2 op8Subject op8ParentFormula := ⟨_, hgrom8⟩
theorem hs8 : FieldEmbedding.BoundedBy 97 op8Subject := by
  simp [FieldEmbedding.BoundedBy, op8Subject, op8ParentFormula, op8ParentTail, op8ChildFormulaB, op8ChildFormulaC, op8Sb, op8Result, op8PushedSubject]
theorem hf8 : FieldEmbedding.BoundedBy 97 op8ParentFormula := by
  simp [FieldEmbedding.BoundedBy, op8Subject, op8ParentFormula, op8ParentTail, op8ChildFormulaB, op8ChildFormulaC, op8Sb, op8Result, op8PushedSubject]

theorem programMemShape8 (α : K) : programMemShape α (T8 (K := K)) = 23 := by
  unfold programMemShape programMemRows; exact memRows8 0 0 α

theorem hΛp8 (h : evalRom 2 op8Subject op8ParentFormula = some op8Result) :
    programLeafBound (airReorder (romTree (K := GaloisField 97 3) h)) < 97 := by
  rw [romTree8, leaf8]; norm_num

theorem hF8 (h : evalRom 2 op8Subject op8ParentFormula = some op8Result) :
    3 * 2 ^ orbitHeight (programFit (αP 97 5) (romTree (K := GaloisField 97 3) h)) ∣ 97 - 1 := by
  rw [romTree8]
  refine dvd_of_fit_le 97 (H := 5) (by norm_num) ?_ (by norm_num)
  simp only [programFit, comp8, programMemShape8, acc8]; norm_num

theorem hwin8 (h : evalRom 2 op8Subject op8ParentFormula = some op8Result) :
    programAcc (romTree (K := GaloisField 97 3) h) + 3 < orderOf (αP 97 5) ∧
      programMemShape (αP 97 5) (romTree (K := GaloisField 97 3) h) ≤ orderOf (αP 97 5) := by
  rw [romTree8, acc8, programMemShape8, orderOf_αP, orderOf_five97]; norm_num

theorem hKsz8 (h : evalRom 2 op8Subject op8ParentFormula = some op8Result) :
    compilerKszOf (0 : GaloisField 97 3) (αP 97 5) (romTree (K := GaloisField 97 3) h) < 97 := by
  rw [romTree8]
  simp only [compilerKszOf, compilerKsz, programMemRoots, memRoots8, acc8]
  norm_num

/-- `nockCompilesHostile` at `op8` over `ZMod 97` (zero explicit binders). -/
noncomputable def b1572_op8_hostile :=
  GoodSeed.nockCompilesHostile (p := 97) (K := GaloisField 97 3) (αP 97 5) (αP 97 5) (0 : GaloisField 97 3)
    hrun8 hbound8 hs8 hf8 (hΛp8 _) (by norm_num) (by norm_num) (hK_P 97) (hF8 _)
    (hwin8 _) (hKsz8 _)

end

end Nock.RedTeam.Batch1572
