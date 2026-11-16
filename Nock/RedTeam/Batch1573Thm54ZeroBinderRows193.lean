import Nock.RedTeam.Batch1571Thm54ZeroBinderShapes
import Nock.NockVMROM.Thm54.TraceGen.Op2Gen
import Nock.NockVMROM.Thm54.TraceGen.Op5Gen
import Nock.NockVMROM.Thm54.TraceGen.Op6Gen
import Nock.NockVMROM.Thm54.TraceGen.Op7Gen
import Nock.NockVMROM.Thm54.TraceGen.Op8Gen
import Nock.NockVMROM.Thm54.TraceGen.Op9Gen

/-
  Nock/RedTeam/Batch1573Thm54ZeroBinderRows193.lean

  OP2, OP6, OP9: the memory forest has 36 / 36 / 42 rows, so `programFit = 37 / 37 / 43 > 32` and `ZMod 97`
  (`96 = 3 * 2^5`) cannot carry `hF`; moved to the next prime `193` (`192 = 3 * 2^6`), `α = 5` (order 192),
  `K = GaloisField 193 3`.  `αW := α`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Nock.RedTeam.Batch1573

open Nock Nock.Walk Nock.MemoryTable
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam.Batch1571

local instance fact193 : Fact (Nat.Prime 193) := ⟨by norm_num⟩
noncomputable local instance : Fintype (GaloisField 193 3) := Fintype.ofFinite _
noncomputable local instance : DecidableEq (GaloisField 193 3) := Classical.decEq _
local instance : CharP (GaloisField 193 3) (ringChar (GaloisField 193 3)) := ringChar.charP _

theorem orderOf_five193 : orderOf (5 : ZMod 193) = 192 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  decide

section
variable {K : Type} [Field K]

/-! ### OP2 -/
abbrev T2 : NTree (GenComputeRow K) := .node (skelNode
            (genSkelOp2 op2Subject op2ParentFormula (.atom 2) op2ParentTail op2ChildFormula1
              op2ChildFormula2 op2Sf1 op2Sf2 op2Result)
            [⟨op2ParentFormula, op2ParentTail, 3, 0⟩, ⟨op2ParentTail, op2ChildFormula1, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op2Subject op2ChildFormula1 op2Sf1 (.atom 1))
                [⟨op2ChildFormula1, op2Sf1, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op2Subject op2ChildFormula2 op2Sf2 (.atom 1))
                [⟨op2ChildFormula2, op2Sf2, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op2Sf1 op2Sf2 op2Result (.atom 1))
                [⟨op2Sf2, op2Result, 3, 0⟩]) []]

theorem gen2 : genComputeSkeleton (K := K) 2 op2Subject op2ParentFormula = .ok (T2, op2Result) :=
  genComputeSkeleton_op2 0

theorem evalRom2 : evalRom 2 op2Subject op2ParentFormula = some op2Result := by
  simp [evalRom, op2Subject, op2ParentFormula, op2ParentTail, op2ChildFormula1, op2ChildFormula2, op2Result, op2Sf1, op2Sf2, Nock.Noun.slot, Nock.Noun.lus, Noun.tis]

theorem romTree2 (h : evalRom 2 op2Subject op2ParentFormula = some op2Result) : romTree (K := K) h = T2 := by
  have hs := romTree_spec (K := K) h
  rw [gen2] at hs
  injection hs with hs
  exact (Prod.mk.inj hs).1.symm

theorem air2 : airReorder (T2 (K := K)) = T2 := by
  simp [airReorder, skelNode, genSkelOp1, genSkelOp2, airNeedsSwap]

theorem acc2 : programAcc (T2 (K := K)) = 5 := by
  rw [programAcc, air2]; simp [accAt, bfsRows_three_leaves, skelNode, genSkelOp1, genSkelOp2, Framework.recordCount]
theorem comp2 : programCompRows (T2 (K := K)) = 4 := by
  rw [programCompRows, air2]; simp [bfsRows_three_leaves]
theorem leaf2 : programLeafBound (airReorder (T2 (K := K))) = 7 := by
  rw [air2, programLeafBound]
  simp [bfsRows_three_leaves, rowNounsBound, skelNode, genSkelOp1, genSkelOp2, Noun.leaves, op2Subject, op2ParentFormula, op2ParentTail, op2ChildFormula1, op2ChildFormula2, op2Result, op2Sf1, op2Sf2]

theorem memRows2 (lmb z α : K) : programMemRowsL lmb z α (T2 (K := K)) = 36 := by
  simp only [programMemRowsL, genMemoryForest]
  rw [bfsForest_length, threadGenForest_totalSize, air2]
  rw [show (T2 : NTree (GenComputeRow K)) = NTree.node _ [_, _, _] from rfl, bfsAssign_three_leaves]
  simp only [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux, skelNode,
    Walk.totalSize_append, List.append_nil, op2Subject, op2ParentFormula, op2ParentTail, op2ChildFormula1, op2ChildFormula2, op2Result, op2Sf1, op2Sf2]
  simp only [genRowMemForest_chain32_size, genRowMemForest_singleton_axis3_size]
  simp [nounWalkSize]

theorem memRoots2 (lmb z α : K) : programMemRootsL lmb z α (T2 (K := K)) = 4 := by
  simp only [programMemRootsL, genMemoryForest]
  rw [threadGenForest_length, air2]
  rw [show (T2 : NTree (GenComputeRow K)) = NTree.node _ [_, _, _] from rfl, bfsAssign_three_leaves]
  simp only [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux, skelNode,
    List.length_append, List.append_nil, op2Subject, op2ParentFormula, op2ParentTail, op2ChildFormula1, op2ChildFormula2, op2Result, op2Sf1, op2Sf2]
  simp only [chain32_length, genRowMemForest_singleton, List.length_singleton]

/-! ### OP6 -/
abbrev T6 : NTree (GenComputeRow K) := .node (skelNode
            (genSkelOp6 op6Subject op6ParentFormula (.atom 6) op6ParentTail op6CondFormula
              op6BranchPair op6BranchC op6BranchD op6CondResult op6BranchC op6Result)
            [⟨op6ParentFormula, op6ParentTail, 3, 0⟩, ⟨op6ParentTail, op6CondFormula, 2, 0⟩,
             ⟨op6BranchPair, op6BranchC, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op6Subject op6CondFormula op6CondResult (.atom 1))
                [⟨op6CondFormula, op6CondResult, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op6Subject op6BranchC op6Result (.atom 1))
                [⟨op6BranchC, op6Result, 3, 0⟩]) []]
abbrev U6 : NTree (GenComputeRow K) := .node (skelNode
            (genSkelOp6 op6Subject op6ParentFormula (.atom 6) op6ParentTail op6CondFormula
              op6BranchPair op6BranchC op6BranchD op6CondResult op6BranchC op6Result)
            [⟨op6ParentFormula, op6ParentTail, 3, 0⟩, ⟨op6ParentTail, op6CondFormula, 2, 0⟩,
             ⟨op6BranchPair, op6BranchC, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op6Subject op6BranchC op6Result (.atom 1))
                [⟨op6BranchC, op6Result, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op6Subject op6CondFormula op6CondResult (.atom 1))
                [⟨op6CondFormula, op6CondResult, 3, 0⟩]) []]

theorem gen6 : genComputeSkeleton (K := K) 2 op6Subject op6ParentFormula = .ok (T6, op6Result) :=
  genComputeSkeleton_op6 0

theorem evalRom6 : evalRom 2 op6Subject op6ParentFormula = some op6Result := by
  simp [evalRom, op6Subject, op6ParentFormula, op6ParentTail, op6CondFormula, op6CondResult, op6BranchC, op6BranchD, op6BranchPair, op6Result, Nock.Noun.slot, Nock.Noun.lus, Noun.tis]

theorem romTree6 (h : evalRom 2 op6Subject op6ParentFormula = some op6Result) : romTree (K := K) h = T6 := by
  have hs := romTree_spec (K := K) h
  rw [gen6] at hs
  injection hs with hs
  exact (Prod.mk.inj hs).1.symm

theorem air6 : airReorder (T6 (K := K)) = U6 := by
  simp [airReorder, skelNode, genSkelOp1, genSkelOp6, airNeedsSwap, swapPair, T6, U6]

theorem acc6 : programAcc (T6 (K := K)) = 5 := by
  rw [programAcc, air6]; simp [accAt, bfsRows_two_leaves, skelNode, genSkelOp1, genSkelOp6, Framework.recordCount]
theorem comp6 : programCompRows (T6 (K := K)) = 3 := by
  rw [programCompRows, air6]; simp [bfsRows_two_leaves]
theorem leaf6 : programLeafBound (airReorder (T6 (K := K))) = 7 := by
  rw [air6, programLeafBound]
  simp [bfsRows_two_leaves, rowNounsBound, skelNode, genSkelOp1, genSkelOp6, Noun.leaves, op6Subject, op6ParentFormula, op6ParentTail, op6CondFormula, op6CondResult, op6BranchC, op6BranchD, op6BranchPair, op6Result]

theorem memRows6 (lmb z α : K) : programMemRowsL lmb z α (T6 (K := K)) = 36 := by
  simp only [programMemRowsL, genMemoryForest]
  rw [bfsForest_length, threadGenForest_totalSize, air6]
  rw [show (U6 : NTree (GenComputeRow K)) = NTree.node _ [_, _] from rfl, bfsAssign_two_leaves]
  simp only [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux, skelNode,
    Walk.totalSize_append, List.append_nil, op6Subject, op6ParentFormula, op6ParentTail, op6CondFormula, op6CondResult, op6BranchC, op6BranchD, op6BranchPair, op6Result]
  simp only [genRowMemForest_three_chain32_size, genRowMemForest_singleton_axis3_size]
  simp [nounWalkSize]

theorem memRoots6 (lmb z α : K) : programMemRootsL lmb z α (T6 (K := K)) = 4 := by
  simp only [programMemRootsL, genMemoryForest]
  rw [threadGenForest_length, air6]
  rw [show (U6 : NTree (GenComputeRow K)) = NTree.node _ [_, _] from rfl, bfsAssign_two_leaves]
  simp only [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux, skelNode,
    List.length_append, List.append_nil, op6Subject, op6ParentFormula, op6ParentTail, op6CondFormula, op6CondResult, op6BranchC, op6BranchD, op6BranchPair, op6Result]
  simp only [genRowMemForest_three_chain32_length, genRowMemForest_singleton, List.length_singleton]

/-! ### OP9 -/
abbrev T9 : NTree (GenComputeRow K) := .node (skelNode
            (genSkelOp9 op9Subject op9ParentFormula (.atom 9) op9ParentTail op9AxisAtom
              op9CoreFormula op9CoreNoun op9Arm op9Result 2)
            [⟨op9ParentFormula, op9ParentTail, 3, 0⟩, ⟨op9ParentTail, op9AxisAtom, 2, 0⟩,
             ⟨op9CoreNoun, op9Arm, 2, 0⟩])
            [.node (skelNode (genSkelOp1 op9Subject op9CoreFormula op9CoreNoun (.atom 1))
                [⟨op9CoreFormula, op9CoreNoun, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 op9CoreNoun op9Arm op9Result (.atom 1))
                [⟨op9Arm, op9Result, 3, 0⟩]) []]

theorem gen9 : genComputeSkeleton (K := K) 2 op9Subject op9ParentFormula = .ok (T9, op9Result) :=
  genComputeSkeleton_op9 0

theorem evalRom9 : evalRom 2 op9Subject op9ParentFormula = some op9Result := by
  simp [evalRom, op9Subject, op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula, op9CoreNoun, op9Arm, op9Result, Nock.Noun.slot, Nock.Noun.lus, Noun.tis]

theorem romTree9 (h : evalRom 2 op9Subject op9ParentFormula = some op9Result) : romTree (K := K) h = T9 := by
  have hs := romTree_spec (K := K) h
  rw [gen9] at hs
  injection hs with hs
  exact (Prod.mk.inj hs).1.symm

theorem air9 : airReorder (T9 (K := K)) = T9 := by
  simp [airReorder, skelNode, genSkelOp1, genSkelOp9, airNeedsSwap]

theorem acc9 : programAcc (T9 (K := K)) = 5 := by
  rw [programAcc, air9]; simp [accAt, bfsRows_two_leaves, skelNode, genSkelOp1, genSkelOp9, Framework.recordCount]
theorem comp9 : programCompRows (T9 (K := K)) = 3 := by
  rw [programCompRows, air9]; simp [bfsRows_two_leaves]
theorem leaf9 : programLeafBound (airReorder (T9 (K := K))) = 7 := by
  rw [air9, programLeafBound]
  simp [bfsRows_two_leaves, rowNounsBound, skelNode, genSkelOp1, genSkelOp9, Noun.leaves, op9Subject, op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula, op9CoreNoun, op9Arm, op9Result]

theorem memRows9 (lmb z α : K) : programMemRowsL lmb z α (T9 (K := K)) = 42 := by
  simp only [programMemRowsL, genMemoryForest]
  rw [bfsForest_length, threadGenForest_totalSize, air9]
  rw [show (T9 : NTree (GenComputeRow K)) = NTree.node _ [_, _] from rfl, bfsAssign_two_leaves]
  simp only [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux, skelNode,
    Walk.totalSize_append, List.append_nil, op9Subject, op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula, op9CoreNoun, op9Arm, op9Result]
  simp only [genRowMemForest_three_chain32_size, genRowMemForest_singleton_axis3_size]
  simp [nounWalkSize]

theorem memRoots9 (lmb z α : K) : programMemRootsL lmb z α (T9 (K := K)) = 4 := by
  simp only [programMemRootsL, genMemoryForest]
  rw [threadGenForest_length, air9]
  rw [show (T9 : NTree (GenComputeRow K)) = NTree.node _ [_, _] from rfl, bfsAssign_two_leaves]
  simp only [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux, skelNode,
    List.length_append, List.append_nil, op9Subject, op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula, op9CoreNoun, op9Arm, op9Result]
  simp only [genRowMemForest_three_chain32_length, genRowMemForest_singleton, List.length_singleton]

/-! #### field part of `op2`: `p = 193`, `α = 5`, `h = 6` -/

theorem hrun2 : Nock.evalN 2 op2Subject op2ParentFormula = some op2Result := by
  simp [Nock.evalN, op2Subject, op2ParentFormula, op2ParentTail, op2ChildFormula1, op2ChildFormula2, op2Result, op2Sf1, op2Sf2, Nock.Noun.slot, Nock.Noun.lus, Noun.tis]

theorem hgrom2 : evalGRom 193 2 op2Subject op2ParentFormula = some op2Result := by
  simp [evalGRom, op2Subject, op2ParentFormula, op2ParentTail, op2ChildFormula1, op2ChildFormula2, op2Result, op2Sf1, op2Sf2, Nock.Noun.slot, FieldEmbedding.lusGBy, Noun.tis]

theorem hbound2 : RunBoundedBy 193 2 op2Subject op2ParentFormula := ⟨_, hgrom2⟩
theorem hs2 : FieldEmbedding.BoundedBy 193 op2Subject := by
  simp [FieldEmbedding.BoundedBy, op2Subject, op2ParentFormula, op2ParentTail, op2ChildFormula1, op2ChildFormula2, op2Result, op2Sf1, op2Sf2]
theorem hf2 : FieldEmbedding.BoundedBy 193 op2ParentFormula := by
  simp [FieldEmbedding.BoundedBy, op2Subject, op2ParentFormula, op2ParentTail, op2ChildFormula1, op2ChildFormula2, op2Result, op2Sf1, op2Sf2]

theorem programMemShape2 (α : K) : programMemShape α (T2 (K := K)) = 36 := by
  unfold programMemShape programMemRows; exact memRows2 0 0 α

theorem hΛp2 (h : evalRom 2 op2Subject op2ParentFormula = some op2Result) :
    programLeafBound (airReorder (romTree (K := GaloisField 193 3) h)) < 193 := by
  rw [romTree2, leaf2]; norm_num

theorem hF2 (h : evalRom 2 op2Subject op2ParentFormula = some op2Result) :
    3 * 2 ^ orbitHeight (programFit (αP 193 5) (romTree (K := GaloisField 193 3) h)) ∣ 193 - 1 := by
  rw [romTree2]
  refine dvd_of_fit_le 193 (H := 6) (by norm_num) ?_ (by norm_num)
  simp only [programFit, comp2, programMemShape2, acc2]; norm_num

theorem hwin2 (h : evalRom 2 op2Subject op2ParentFormula = some op2Result) :
    programAcc (romTree (K := GaloisField 193 3) h) + 3 < orderOf (αP 193 5) ∧
      programMemShape (αP 193 5) (romTree (K := GaloisField 193 3) h) ≤ orderOf (αP 193 5) := by
  rw [romTree2, acc2, programMemShape2, orderOf_αP, orderOf_five193]; norm_num

theorem hKsz2 (h : evalRom 2 op2Subject op2ParentFormula = some op2Result) :
    compilerKszOf (0 : GaloisField 193 3) (αP 193 5) (romTree (K := GaloisField 193 3) h) < 193 := by
  rw [romTree2]
  simp only [compilerKszOf, compilerKsz, programMemRoots, memRoots2, acc2]
  norm_num

/-- `nockCompilesHostile` at `op2` over `ZMod 193` (zero explicit binders). -/
noncomputable def b1573_op2_hostile :=
  GoodSeed.nockCompilesHostile (p := 193) (K := GaloisField 193 3) (αP 193 5) (αP 193 5) (0 : GaloisField 193 3)
    hrun2 hbound2 hs2 hf2 (hΛp2 _) (by norm_num) (by norm_num) (hK_P 193) (hF2 _)
    (hwin2 _) (hKsz2 _)

/-! #### field part of `op6`: `p = 193`, `α = 5`, `h = 6` -/

theorem hrun6 : Nock.evalN 2 op6Subject op6ParentFormula = some op6Result := by
  simp [Nock.evalN, op6Subject, op6ParentFormula, op6ParentTail, op6CondFormula, op6CondResult, op6BranchC, op6BranchD, op6BranchPair, op6Result, Nock.Noun.slot, Nock.Noun.lus, Noun.tis]

theorem hgrom6 : evalGRom 193 2 op6Subject op6ParentFormula = some op6Result := by
  simp [evalGRom, op6Subject, op6ParentFormula, op6ParentTail, op6CondFormula, op6CondResult, op6BranchC, op6BranchD, op6BranchPair, op6Result, Nock.Noun.slot, FieldEmbedding.lusGBy, Noun.tis]

theorem hbound6 : RunBoundedBy 193 2 op6Subject op6ParentFormula := ⟨_, hgrom6⟩
theorem hs6 : FieldEmbedding.BoundedBy 193 op6Subject := by
  simp [FieldEmbedding.BoundedBy, op6Subject, op6ParentFormula, op6ParentTail, op6CondFormula, op6CondResult, op6BranchC, op6BranchD, op6BranchPair, op6Result]
theorem hf6 : FieldEmbedding.BoundedBy 193 op6ParentFormula := by
  simp [FieldEmbedding.BoundedBy, op6Subject, op6ParentFormula, op6ParentTail, op6CondFormula, op6CondResult, op6BranchC, op6BranchD, op6BranchPair, op6Result]

theorem programMemShape6 (α : K) : programMemShape α (T6 (K := K)) = 36 := by
  unfold programMemShape programMemRows; exact memRows6 0 0 α

theorem hΛp6 (h : evalRom 2 op6Subject op6ParentFormula = some op6Result) :
    programLeafBound (airReorder (romTree (K := GaloisField 193 3) h)) < 193 := by
  rw [romTree6, leaf6]; norm_num

theorem hF6 (h : evalRom 2 op6Subject op6ParentFormula = some op6Result) :
    3 * 2 ^ orbitHeight (programFit (αP 193 5) (romTree (K := GaloisField 193 3) h)) ∣ 193 - 1 := by
  rw [romTree6]
  refine dvd_of_fit_le 193 (H := 6) (by norm_num) ?_ (by norm_num)
  simp only [programFit, comp6, programMemShape6, acc6]; norm_num

theorem hwin6 (h : evalRom 2 op6Subject op6ParentFormula = some op6Result) :
    programAcc (romTree (K := GaloisField 193 3) h) + 3 < orderOf (αP 193 5) ∧
      programMemShape (αP 193 5) (romTree (K := GaloisField 193 3) h) ≤ orderOf (αP 193 5) := by
  rw [romTree6, acc6, programMemShape6, orderOf_αP, orderOf_five193]; norm_num

theorem hKsz6 (h : evalRom 2 op6Subject op6ParentFormula = some op6Result) :
    compilerKszOf (0 : GaloisField 193 3) (αP 193 5) (romTree (K := GaloisField 193 3) h) < 193 := by
  rw [romTree6]
  simp only [compilerKszOf, compilerKsz, programMemRoots, memRoots6, acc6]
  norm_num

/-- `nockCompilesHostile` at `op6` over `ZMod 193` (zero explicit binders). -/
noncomputable def b1573_op6_hostile :=
  GoodSeed.nockCompilesHostile (p := 193) (K := GaloisField 193 3) (αP 193 5) (αP 193 5) (0 : GaloisField 193 3)
    hrun6 hbound6 hs6 hf6 (hΛp6 _) (by norm_num) (by norm_num) (hK_P 193) (hF6 _)
    (hwin6 _) (hKsz6 _)

/-! #### field part of `op9`: `p = 193`, `α = 5`, `h = 6` -/

theorem hrun9 : Nock.evalN 2 op9Subject op9ParentFormula = some op9Result := by
  simp [Nock.evalN, op9Subject, op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula, op9CoreNoun, op9Arm, op9Result, Nock.Noun.slot, Nock.Noun.lus, Noun.tis]

theorem hgrom9 : evalGRom 193 2 op9Subject op9ParentFormula = some op9Result := by
  simp [evalGRom, op9Subject, op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula, op9CoreNoun, op9Arm, op9Result, Nock.Noun.slot, FieldEmbedding.lusGBy, Noun.tis]

theorem hbound9 : RunBoundedBy 193 2 op9Subject op9ParentFormula := ⟨_, hgrom9⟩
theorem hs9 : FieldEmbedding.BoundedBy 193 op9Subject := by
  simp [FieldEmbedding.BoundedBy, op9Subject, op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula, op9CoreNoun, op9Arm, op9Result]
theorem hf9 : FieldEmbedding.BoundedBy 193 op9ParentFormula := by
  simp [FieldEmbedding.BoundedBy, op9Subject, op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula, op9CoreNoun, op9Arm, op9Result]

theorem programMemShape9 (α : K) : programMemShape α (T9 (K := K)) = 42 := by
  unfold programMemShape programMemRows; exact memRows9 0 0 α

theorem hΛp9 (h : evalRom 2 op9Subject op9ParentFormula = some op9Result) :
    programLeafBound (airReorder (romTree (K := GaloisField 193 3) h)) < 193 := by
  rw [romTree9, leaf9]; norm_num

theorem hF9 (h : evalRom 2 op9Subject op9ParentFormula = some op9Result) :
    3 * 2 ^ orbitHeight (programFit (αP 193 5) (romTree (K := GaloisField 193 3) h)) ∣ 193 - 1 := by
  rw [romTree9]
  refine dvd_of_fit_le 193 (H := 6) (by norm_num) ?_ (by norm_num)
  simp only [programFit, comp9, programMemShape9, acc9]; norm_num

theorem hwin9 (h : evalRom 2 op9Subject op9ParentFormula = some op9Result) :
    programAcc (romTree (K := GaloisField 193 3) h) + 3 < orderOf (αP 193 5) ∧
      programMemShape (αP 193 5) (romTree (K := GaloisField 193 3) h) ≤ orderOf (αP 193 5) := by
  rw [romTree9, acc9, programMemShape9, orderOf_αP, orderOf_five193]; norm_num

theorem hKsz9 (h : evalRom 2 op9Subject op9ParentFormula = some op9Result) :
    compilerKszOf (0 : GaloisField 193 3) (αP 193 5) (romTree (K := GaloisField 193 3) h) < 193 := by
  rw [romTree9]
  simp only [compilerKszOf, compilerKsz, programMemRoots, memRoots9, acc9]
  norm_num

/-- `nockCompilesHostile` at `op9` over `ZMod 193` (zero explicit binders). -/
noncomputable def b1573_op9_hostile :=
  GoodSeed.nockCompilesHostile (p := 193) (K := GaloisField 193 3) (αP 193 5) (αP 193 5) (0 : GaloisField 193 3)
    hrun9 hbound9 hs9 hf9 (hΛp9 _) (by norm_num) (by norm_num) (hK_P 193) (hF9 _)
    (hwin9 _) (hKsz9 _)

end

end Nock.RedTeam.Batch1573
