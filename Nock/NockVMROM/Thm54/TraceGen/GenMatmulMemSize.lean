/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulMemSize.lean

  Exact served-forest counts for the generated 2×2 matmul program.
  Constructor lemmas (`gen_op*_mem`, `gen_slam_mem`) add request-walk
  sizes along the same `gen_*` tree as `mmTree_size`.  The unassigned
  forest of `mmTree` is 618 roots / 30936 rows, obtained by
  summing constructor walks along C00..C11 and three autocons wrappers.
  Assigned counts match via stamp-independent row forests and BFS-sum
  transport through `bfsAssign`.

  Kernel `#eval` / `rfl` of the 28k-node forest is not a proof.

  `Gen.lean` is not edited.  `mapNTree_size` / `totalSize_append` /
  `genMemForestFromTree_node` live in `GenTierASize` and are not redeclared.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulSize
import Nock.NockVMROM.Thm54.TraceGen.GenMem

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy

variable {K : Type} [Field K]

variable {lmb : K}

noncomputable section

set_option maxHeartbeats 800000

/-! ## Noun-walk sizes of formula fragments -/

theorem nounWalkSize_atom (n : ℕ) : nounWalkSize (.atom n) = 1 := rfl

theorem nounWalkSize_cell (h t : Noun) :
    nounWalkSize (.cell h t) = 1 + nounWalkSize h + nounWalkSize t := rfl

theorem nounWalkSize_op0 (ax : ℕ) : nounWalkSize (op0 ax) = 3 := by
  simp [op0, nounWalkSize]

theorem nounWalkSize_op1 (k : ℕ) : nounWalkSize (op1 k) = 3 := by
  simp [op1, nounWalkSize]

theorem nounWalkSize_quote (n : Noun) :
    nounWalkSize (quote n) = 2 + nounWalkSize n := by
  simp [quote, nounWalkSize]

theorem nounWalkSize_op4 (b : Noun) :
    nounWalkSize (op4 b) = 2 + nounWalkSize b := by
  simp [op4, nounWalkSize]

theorem nounWalkSize_op5 (b c : Noun) :
    nounWalkSize (op5 b c) = 3 + nounWalkSize b + nounWalkSize c := by
  simp [op5, nounWalkSize]
  omega

theorem nounWalkSize_op7 (b c : Noun) :
    nounWalkSize (op7 b c) = 3 + nounWalkSize b + nounWalkSize c := by
  simp [op7, nounWalkSize]
  omega

theorem nounWalkSize_op6 (b c d : Noun) :
    nounWalkSize (op6 b c d) =
      4 + nounWalkSize b + nounWalkSize c + nounWalkSize d := by
  simp [op6, nounWalkSize]
  omega

theorem nounWalkSize_invokeAxis (axis : ℕ) : nounWalkSize (invokeAxis axis) = 7 := by
  simp [invokeAxis, nounWalkSize]

theorem nounWalkSize_slam (batt samp : Noun) (axis : ℕ) :
    nounWalkSize (slam batt samp axis) =
      11 + nounWalkSize batt + nounWalkSize samp := by
  simp [slam, nounWalkSize_op7, nounWalkSize, nounWalkSize_invokeAxis]
  omega

theorem nounWalkSize_addNewSample : nounWalkSize addNewSample = 15 := by
  simp [addNewSample, nounWalkSize_cell, nounWalkSize_op4, nounWalkSize_op0]

theorem nounWalkSize_addArm : nounWalkSize addArm = 45 := by
  simp [addArm, nounWalkSize_op6, nounWalkSize_op5, nounWalkSize_op0,
    nounWalkSize_slam, nounWalkSize_addNewSample]

theorem nounWalkSize_addFromMac : nounWalkSize addFromMac = 25 := by
  simp [addFromMac, nounWalkSize_slam, nounWalkSize_op0, nounWalkSize_cell,
    nounWalkSize_op1]

theorem nounWalkSize_macNewSample : nounWalkSize macNewSample = 39 := by
  simp [macNewSample, nounWalkSize_cell, nounWalkSize_addFromMac,
    nounWalkSize_op4, nounWalkSize_op0]

theorem nounWalkSize_macArm : nounWalkSize macArm = 69 := by
  simp [macArm, nounWalkSize_op6, nounWalkSize_op5, nounWalkSize_op0,
    nounWalkSize_slam, nounWalkSize_macNewSample]

theorem nounWalkSize_mmBattery : nounWalkSize mmBattery = 115 := by
  simp [mmBattery, nounWalkSize_cell, nounWalkSize_macArm, nounWalkSize_addArm]

theorem nounWalkSize_addSample (acc m : Noun) :
    nounWalkSize (addSample acc m) = 3 + nounWalkSize acc + nounWalkSize m := by
  simp [addSample, nounWalkSize]
  omega

theorem nounWalkSize_addCore (acc i m : Noun) :
    nounWalkSize (addCore acc i m) =
      48 + nounWalkSize acc + nounWalkSize i + nounWalkSize m := by
  simp [addCore, nounWalkSize, nounWalkSize_addArm]
  omega

theorem nounWalkSize_macSample (acc n m : Noun) :
    nounWalkSize (macSample acc n m) =
      4 + nounWalkSize acc + nounWalkSize n + nounWalkSize m := by
  simp [macSample, nounWalkSize]
  omega

theorem nounWalkSize_macCoreAt (acc i n m : Noun) :
    nounWalkSize (macCoreAt acc i n m) =
      119 + nounWalkSize acc + nounWalkSize i + nounWalkSize n +
        nounWalkSize m := by
  simp [macCoreAt, nounWalkSize, nounWalkSize_mmBattery]
  omega

theorem nounWalkSize_macCore (acc n m : Noun) :
    nounWalkSize (macCore acc n m) =
      120 + nounWalkSize acc + nounWalkSize n + nounWalkSize m := by
  simp [macCore, nounWalkSize_macCoreAt, nounWalkSize_atom]
  omega

theorem nounWalkSize_mmA : nounWalkSize mmA = 7 := by
  simp [mmA, nounWalkSize]

theorem nounWalkSize_mmB : nounWalkSize mmB = 7 := by
  simp [mmB, nounWalkSize]

theorem nounWalkSize_mmSubject : nounWalkSize mmSubject = 15 := by
  simp [mmSubject, nounWalkSize, nounWalkSize_mmA, nounWalkSize_mmB]

theorem nounWalkSize_invokeMac (accF nF mF : Noun) :
    nounWalkSize (invokeMac accF nF mF) =
      134 + nounWalkSize accF + nounWalkSize nF + nounWalkSize mF := by
  simp [invokeMac, nounWalkSize_slam, nounWalkSize_quote, nounWalkSize_mmBattery,
    nounWalkSize, nounWalkSize_op1]
  omega

theorem nounWalkSize_mac2 (accF nF mF nF' mF' : Noun) :
    nounWalkSize (mac2 accF nF mF nF' mF') =
      268 + nounWalkSize accF + nounWalkSize nF + nounWalkSize mF +
        nounWalkSize nF' + nounWalkSize mF' := by
  simp [mac2, nounWalkSize_invokeMac]
  omega

theorem nounWalkSize_mmC00 : nounWalkSize mmC00 = 283 := by
  simp [mmC00, nounWalkSize_mac2, nounWalkSize_op1, nounWalkSize_op0]

theorem nounWalkSize_mmC01 : nounWalkSize mmC01 = 283 := by
  simp [mmC01, nounWalkSize_mac2, nounWalkSize_op1, nounWalkSize_op0]

theorem nounWalkSize_mmC10 : nounWalkSize mmC10 = 283 := by
  simp [mmC10, nounWalkSize_mac2, nounWalkSize_op1, nounWalkSize_op0]

theorem nounWalkSize_mmC11 : nounWalkSize mmC11 = 283 := by
  simp [mmC11, nounWalkSize_mac2, nounWalkSize_op1, nounWalkSize_op0]

/-! ## Record-tree size -/

/-- Size of the descent forest under a read node: one verify (remaining `< 2`)
    or one decompose whose on-path child continues the axis. -/
def descentForestSize (child current : Noun) (remaining : ℕ) : ℕ :=
  if remaining < 2 then
    1 + nounWalkSize child
  else if axisTopBit remaining then
    1 + nounWalkSize (formulaHead current)
      + descentForestSize child (formulaTail current) (axisRest remaining)
  else
    1 + descentForestSize child (formulaHead current) (axisRest remaining)
      + nounWalkSize (formulaTail current)
termination_by remaining
decreasing_by
  all_goals
    apply axisRest_lt
    omega

def recordTreeSize (root child : Noun) (axis : ℕ) : ℕ :=
  1 + descentForestSize child root axis

theorem descentForestSize_of_lt2 (child current : Noun) {remaining : ℕ}
    (h : remaining < 2) :
    descentForestSize child current remaining = 1 + nounWalkSize child := by
  conv => lhs; unfold descentForestSize
  rw [if_pos h]

theorem descentForestSize_of_tail (child current : Noun) {remaining : ℕ}
    (h2 : ¬ remaining < 2) (ht : axisTopBit remaining = true) :
    descentForestSize child current remaining =
      1 + nounWalkSize (formulaHead current)
        + descentForestSize child (formulaTail current) (axisRest remaining) := by
  conv => lhs; unfold descentForestSize
  rw [if_neg h2, if_pos ht]

theorem descentForestSize_of_head (child current : Noun) {remaining : ℕ}
    (h2 : ¬ remaining < 2) (hh : axisTopBit remaining = false) :
    descentForestSize child current remaining =
      1 + descentForestSize child (formulaHead current) (axisRest remaining)
        + nounWalkSize (formulaTail current) := by
  conv => lhs; unfold descentForestSize
  rw [if_neg h2, if_neg (by simp [hh])]

theorem genAnnotatedDescent_totalSize (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (currentNoun : Noun) (remainingAxis : ℕ) :
    totalSize (genAnnotatedDescent E z lmb root child recAxis ts recordExp
        currentNoun remainingAxis).1 =
      descentForestSize child currentNoun remainingAxis := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    unfold genAnnotatedDescent
    split
    · rename_i hlt
      simp [genAnnotatedVerify, totalSize, NTree.size, genAnnotatedNounWalk_size]
      rw [descentForestSize_of_lt2 _ _ hlt]
    · rename_i hge
      split
      · rename_i ht
        rw [descentForestSize_of_tail _ _ hge ht]
        have hih := ih (axisRest n) (axisRest_lt (by omega)) (formulaTail currentNoun)
        simp [totalSize, NTree.size, genAnnotatedNounWalk_size] at hih ⊢
        rw [hih]
        omega
      · rename_i hh
        have hh' : axisTopBit n = false := Bool.eq_false_iff.mpr hh
        rw [descentForestSize_of_head _ _ hge hh']
        have hih := ih (axisRest n) (axisRest_lt (by omega)) (formulaHead currentNoun)
        simp [totalSize, NTree.size, genAnnotatedNounWalk_size] at hih ⊢
        rw [hih]
        omega

theorem genAnnotatedRecordTree_size (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (axis e : ℕ) :
    (genAnnotatedRecordTree E z α lmb root child axis e).size =
      recordTreeSize root child axis := by
  simp [genAnnotatedRecordTree, recordTreeSize, NTree.size, totalSize]
  exact genAnnotatedDescent_totalSize E z root child axis (α ^ e) e root axis

theorem genRowMemForest_singleton_size (E : Noun → ComputeTable.FP K) (z α : K)
    (r : MemRecordReq) :
    totalSize (genRowMemForest E z α lmb [r]) =
      recordTreeSize r.root r.child r.axis := by
  simp [genRowMemForest_singleton, totalSize, genAnnotatedRecordTree_size]

/-! ## Axis specializations used by 1-record opcodes -/

theorem recordTreeSize_axis3 (hd tl : Noun) :
    recordTreeSize (.cell hd tl) tl 3 = 3 + nounWalkSize hd + nounWalkSize tl := by
  unfold recordTreeSize
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_three)]
  simp [axisRest_three]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [formulaHead, formulaTail]
  omega

theorem recordTreeSize_axis2 (hd tl : Noun) :
    recordTreeSize (.cell hd tl) hd 2 = 3 + nounWalkSize hd + nounWalkSize tl := by
  unfold recordTreeSize
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_two)]
  simp [axisRest_two]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [formulaHead, formulaTail]
  omega

theorem recordTreeSize_axis1 (root child : Noun) :
    recordTreeSize root child 1 = 2 + nounWalkSize child := by
  unfold recordTreeSize
  rw [descentForestSize_of_lt2 (h := by omega)]
  omega

/-! ## Extraction from unassigned `skelNode`s -/

theorem getRecordExp_zeroStamp (st : ComputeTable.State) (i : ℕ) :
    getRecordExp (zeroStamp st) i = 0 := by
  unfold getRecordExp zeroStamp
  split_ifs <;> rfl

theorem extractNodeReqs_skelNode (skel : ComputeRowSkeleton)
    (reqs : List (ServiceReq K)) :
    extractNodeReqs (skelNode skel reqs) =
      extractNodeReqsAux (zeroStamp skel.state) 0 reqs :=
  rfl

theorem extractNodeReqs_skel_one (skel : ComputeRowSkeleton) (r : ServiceReq K) :
    extractNodeReqs (skelNode skel [r]) =
      [⟨r.root, r.child, r.axis, 0⟩] := by
  rw [extractNodeReqs_skelNode, extractNodeReqsAux_cons1, getRecordExp_zeroStamp]

theorem extractNodeReqs_skel_two (skel : ComputeRowSkeleton)
    (r1 r2 : ServiceReq K) :
    extractNodeReqs (skelNode skel [r1, r2]) =
      [⟨r1.root, r1.child, r1.axis, 0⟩,
       ⟨r2.root, r2.child, r2.axis, 0⟩] := by
  rw [extractNodeReqs_skelNode, extractNodeReqsAux_cons2, getRecordExp_zeroStamp,
    getRecordExp_zeroStamp]

theorem extractNodeReqs_skel_three (skel : ComputeRowSkeleton)
    (r1 r2 r3 : ServiceReq K) :
    extractNodeReqs (skelNode skel [r1, r2, r3]) =
      [⟨r1.root, r1.child, r1.axis, 0⟩,
       ⟨r2.root, r2.child, r2.axis, 0⟩,
       ⟨r3.root, r3.child, r3.axis, 0⟩] := by
  rw [extractNodeReqs_skelNode, extractNodeReqsAux_cons3, getRecordExp_zeroStamp,
    getRecordExp_zeroStamp, getRecordExp_zeroStamp]

/-! ## Forest list arithmetic -/

theorem genMemForestFromList_two (E : Noun → ComputeTable.FP K) (z α : K)
    (a b : NTree (GenComputeRow K)) :
    genMemForestFromList E z α lmb [a, b] =
      genMemForestFromTree E z α lmb a ++ genMemForestFromTree E z α lmb b := by
  simp [genMemForestFromList_cons, genMemForestFromList_nil]

theorem gen_ok_mem (E : Noun → ComputeTable.FP K) (z α : K)
    {fuel : ℕ} {s f : Noun}
    {t t' : NTree (GenComputeRow K)} {r r' : Noun} {n m : ℕ}
    (h : genComputeSkeleton (K := K) fuel s f = .ok (t, r))
    (h' : genComputeSkeleton (K := K) fuel s f = .ok (t', r'))
    (hlen : (genMemForestFromTree E z α lmb t').length = n)
    (hsz : totalSize (genMemForestFromTree E z α lmb t') = m) :
    (genMemForestFromTree E z α lmb t).length = n ∧
      totalSize (genMemForestFromTree E z α lmb t) = m := by
  rw [(gen_ok_unique h h').1]
  exact ⟨hlen, hsz⟩

/-! ## Three-record row with a generic third tree (`OP_9`) -/

theorem genRowMemForest_three_chain32_gen_length (E : Noun → ComputeTable.FP K)
    (z α : K) (hd1 hd2 tl2 : Noun) (root3 child3 : Noun) (ax3 e1 e2 e3 : ℕ) :
    (genRowMemForest E z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩,
         ⟨root3, child3, ax3, e3⟩]).length = 2 := by
  unfold genRowMemForest
  cases h : genAnnotatedChainedTree E z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] with
  | none => simp [genAnnotatedChainedTree] at h
  | some t => simp [h]

theorem genRowMemForest_three_chain32_gen_size (E : Noun → ComputeTable.FP K)
    (z α : K) (hd1 hd2 tl2 : Noun) (root3 child3 : Noun) (ax3 e1 e2 e3 : ℕ) :
    totalSize (genRowMemForest E z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩,
         ⟨root3, child3, ax3, e3⟩])
      = 6 + nounWalkSize hd1 + nounWalkSize hd2 + nounWalkSize tl2
          + recordTreeSize root3 child3 ax3 := by
  unfold genRowMemForest
  cases h : genAnnotatedChainedTree E z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] with
  | none => simp [genAnnotatedChainedTree] at h
  | some t =>
    simp [h, totalSize,
      genAnnotatedChainedTree_axis3_axis2_size E z α hd1 hd2 tl2 e1 e2 t h,
      genAnnotatedRecordTree_size]
    try omega

/-! ## OP0: two independent records (formula-open `@3` and slot read) -/

theorem atom_ne_cell (n : ℕ) (h t : Noun) : Noun.atom n ≠ Noun.cell h t := by
  intro h'; cases h'

theorem genRowMemForest_op0_length (E : Noun → ComputeTable.FP K) (z α : K)
    (ax : ℕ) (subject result : Noun) (e1 e2 : ℕ)
    (hne : .atom ax ≠ subject) :
    (genRowMemForest E z α lmb
        [⟨op0 ax, .atom ax, 3, e1⟩, ⟨subject, result, ax, e2⟩]).length = 2 := by
  unfold genRowMemForest op0
  simp [hne]

theorem genRowMemForest_op0_size (E : Noun → ComputeTable.FP K) (z α : K)
    (ax : ℕ) (subject result : Noun) (e1 e2 : ℕ)
    (hne : .atom ax ≠ subject) :
    totalSize (genRowMemForest E z α lmb
        [⟨op0 ax, .atom ax, 3, e1⟩, ⟨subject, result, ax, e2⟩])
      = 5 + recordTreeSize subject result ax := by
  unfold genRowMemForest op0
  simp [hne, totalSize, genAnnotatedRecordTree_size, recordTreeSize_axis3,
    nounWalkSize]
  try omega

/-! ## Constructor forests from `gen_*` -/

theorem gen_op1_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ) (subject : Noun) (k : ℕ)
    {t : NTree (GenComputeRow K)} {r : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) subject (op1 k) = .ok (t, r)) :
    (genMemForestFromTree E z α lmb t).length = 1 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 5 := by
  refine gen_ok_mem (lmb := lmb) E z α h (gen_op1 (K := K) n subject k) ?_ ?_
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_one,
      genMemForestFromList_nil, List.length_append, List.length_nil]
    simp [genRowMemForest_singleton]
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_one,
      genMemForestFromList_nil, List.append_nil]
    have hop : op1 k = .cell (.atom 1) (.atom k) := rfl
    rw [hop, genRowMemForest_singleton_axis3_size]
    simp [nounWalkSize]

theorem gen_quote_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ) (subject result : Noun)
    {t : NTree (GenComputeRow K)} {r : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) subject (quote result) = .ok (t, r)) :
    (genMemForestFromTree E z α lmb t).length = 1 ∧
      totalSize (genMemForestFromTree E z α lmb t) =
        4 + nounWalkSize result := by
  refine gen_ok_mem (lmb := lmb) E z α h (gen_quote (K := K) n subject result) ?_ ?_
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_one,
      genMemForestFromList_nil, List.length_append, List.length_nil]
    simp [genRowMemForest_singleton]
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_one,
      genMemForestFromList_nil, List.append_nil]
    have hq : quote result = .cell (.atom 1) result := rfl
    rw [hq, genRowMemForest_singleton_axis3_size]
    simp [nounWalkSize]

theorem gen_cons_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ)
    {subject leftHead leftTail tail lRes rRes : Noun}
    {lTree rTree t : NTree (GenComputeRow K)} {r : Noun}
    (hl : genComputeSkeleton (K := K) n subject (.cell leftHead leftTail) =
      .ok (lTree, lRes))
    (hr : genComputeSkeleton (K := K) n subject tail = .ok (rTree, rRes))
    (h : genComputeSkeleton (K := K) (n + 1) subject
      (.cell (.cell leftHead leftTail) tail) = .ok (t, r)) :
    (genMemForestFromTree E z α lmb t).length =
      1 + (genMemForestFromTree E z α lmb lTree).length +
        (genMemForestFromTree E z α lmb rTree).length ∧
    totalSize (genMemForestFromTree E z α lmb t) =
      3 + nounWalkSize (.cell leftHead leftTail) + nounWalkSize tail +
        totalSize (genMemForestFromTree E z α lmb lTree) +
        totalSize (genMemForestFromTree E z α lmb rTree) := by
  refine gen_ok_mem (lmb := lmb) E z α h (gen_cons (K := K) n hl hr) ?_ ?_
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_one,
      genMemForestFromList_two, List.length_append, List.length_append]
    simp [genRowMemForest_singleton]
    omega
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_one,
      genMemForestFromList_two, totalSize_append, totalSize_append]
    rw [genRowMemForest_singleton_axis3_size]
    omega

theorem gen_op4_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ) {subject tail callResult result : Noun}
    {callTree t : NTree (GenComputeRow K)} {r : Noun}
    (hc : genComputeSkeleton (K := K) n subject tail = .ok (callTree, callResult))
    (hinc : Noun.lus callResult = some result)
    (h : genComputeSkeleton (K := K) (n + 1) subject (op4 tail) = .ok (t, r)) :
    (genMemForestFromTree E z α lmb t).length =
      1 + (genMemForestFromTree E z α lmb callTree).length ∧
    totalSize (genMemForestFromTree E z α lmb t) =
      4 + nounWalkSize tail + totalSize (genMemForestFromTree E z α lmb callTree) := by
  refine gen_ok_mem (lmb := lmb) E z α h (gen_op4 (K := K) n hc hinc) ?_ ?_
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_one,
      genMemForestFromList_cons, genMemForestFromList_nil,
      List.length_append, List.length_append, List.length_nil]
    simp [genRowMemForest_singleton]
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_one,
      genMemForestFromList_cons, genMemForestFromList_nil,
      totalSize_append]
    have hop : op4 tail = .cell (.atom 4) tail := rfl
    rw [hop, genRowMemForest_singleton_axis3_size]
    simp [nounWalkSize, totalSize]
    try omega

theorem gen_op5_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ) {subject b c sf1 sf2 : Noun}
    {bTree cTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (bTree, sf1))
    (hc : genComputeSkeleton (K := K) n subject c = .ok (cTree, sf2))
    (h : genComputeSkeleton (K := K) (n + 1) subject (op5 b c) = .ok (t, r)) :
    (genMemForestFromTree E z α lmb t).length =
      1 + (genMemForestFromTree E z α lmb bTree).length +
        (genMemForestFromTree E z α lmb cTree).length ∧
    totalSize (genMemForestFromTree E z α lmb t) =
      7 + nounWalkSize b + nounWalkSize c +
        totalSize (genMemForestFromTree E z α lmb bTree) +
        totalSize (genMemForestFromTree E z α lmb cTree) := by
  refine gen_ok_mem (lmb := lmb) E z α h (gen_op5 (K := K) n hb hc) ?_ ?_
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_two,
      genMemForestFromList_two, List.length_append, List.length_append]
    have hop : op5 b c = .cell (.atom 5) (.cell b c) := rfl
    rw [hop]
    simp [ServiceReq.root, ServiceReq.child, ServiceReq.axis]
    rw [genRowMemForest_chain_length (hc := rfl)]
    omega
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_two,
      genMemForestFromList_two, totalSize_append, totalSize_append]
    have hop : op5 b c = .cell (.atom 5) (.cell b c) := rfl
    rw [hop]
    simp [ServiceReq.root, ServiceReq.child, ServiceReq.axis]
    rw [genRowMemForest_chain32_size]
    simp [nounWalkSize]
    omega

theorem gen_op7_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ) {subject b c sb result : Noun}
    {bTree cTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (bTree, sb))
    (hc : genComputeSkeleton (K := K) n sb c = .ok (cTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) subject (op7 b c) = .ok (t, r)) :
    (genMemForestFromTree E z α lmb t).length =
      1 + (genMemForestFromTree E z α lmb bTree).length +
        (genMemForestFromTree E z α lmb cTree).length ∧
    totalSize (genMemForestFromTree E z α lmb t) =
      7 + nounWalkSize b + nounWalkSize c +
        totalSize (genMemForestFromTree E z α lmb bTree) +
        totalSize (genMemForestFromTree E z α lmb cTree) := by
  refine gen_ok_mem (lmb := lmb) E z α h (gen_op7 (K := K) n hb hc) ?_ ?_
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_two,
      genMemForestFromList_two, List.length_append, List.length_append]
    have hop : op7 b c = .cell (.atom 7) (.cell b c) := rfl
    rw [hop]
    simp [ServiceReq.root, ServiceReq.child, ServiceReq.axis]
    rw [genRowMemForest_chain_length (hc := rfl)]
    omega
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_two,
      genMemForestFromList_two, totalSize_append, totalSize_append]
    have hop : op7 b c = .cell (.atom 7) (.cell b c) := rfl
    rw [hop]
    simp [ServiceReq.root, ServiceReq.child, ServiceReq.axis]
    rw [genRowMemForest_chain32_size]
    simp [nounWalkSize]
    omega

theorem gen_op6_zero_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ) {subject b c d result : Noun}
    {condTree takenTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (condTree, .atom 0))
    (hc : genComputeSkeleton (K := K) n subject c = .ok (takenTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) subject (op6 b c d) = .ok (t, r)) :
    (genMemForestFromTree E z α lmb t).length =
      2 + (genMemForestFromTree E z α lmb condTree).length +
        (genMemForestFromTree E z α lmb takenTree).length ∧
    totalSize (genMemForestFromTree E z α lmb t) =
      11 + nounWalkSize b + 2 * nounWalkSize c + 2 * nounWalkSize d +
        totalSize (genMemForestFromTree E z α lmb condTree) +
        totalSize (genMemForestFromTree E z α lmb takenTree) := by
  refine gen_ok_mem (lmb := lmb) E z α h (gen_op6_zero (K := K) n hb hc) ?_ ?_
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_three,
      genMemForestFromList_two, List.length_append, List.length_append]
    have hop : op6 b c d = .cell (.atom 6) (.cell b (.cell c d)) := rfl
    rw [hop]
    simp [ServiceReq.root, ServiceReq.child, ServiceReq.axis]
    rw [genRowMemForest_three_chain32_length]
    omega
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_three,
      genMemForestFromList_two, totalSize_append, totalSize_append]
    have hop : op6 b c d = .cell (.atom 6) (.cell b (.cell c d)) := rfl
    rw [hop]
    simp [ServiceReq.root, ServiceReq.child, ServiceReq.axis]
    rw [genRowMemForest_three_chain32_size]
    simp [nounWalkSize]
    omega

theorem gen_op6_one_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ) {subject b c d result : Noun}
    {condTree takenTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (condTree, .atom 1))
    (hd : genComputeSkeleton (K := K) n subject d = .ok (takenTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) subject (op6 b c d) = .ok (t, r)) :
    (genMemForestFromTree E z α lmb t).length =
      2 + (genMemForestFromTree E z α lmb condTree).length +
        (genMemForestFromTree E z α lmb takenTree).length ∧
    totalSize (genMemForestFromTree E z α lmb t) =
      11 + nounWalkSize b + 2 * nounWalkSize c + 2 * nounWalkSize d +
        totalSize (genMemForestFromTree E z α lmb condTree) +
        totalSize (genMemForestFromTree E z α lmb takenTree) := by
  refine gen_ok_mem (lmb := lmb) E z α h (gen_op6_one (K := K) n hb hd) ?_ ?_
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_three,
      genMemForestFromList_two, List.length_append, List.length_append]
    have hop : op6 b c d = .cell (.atom 6) (.cell b (.cell c d)) := rfl
    rw [hop]
    simp [ServiceReq.root, ServiceReq.child, ServiceReq.axis]
    rw [genRowMemForest_three_chain32_length]
    omega
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_three,
      genMemForestFromList_two, totalSize_append, totalSize_append]
    have hop : op6 b c d = .cell (.atom 6) (.cell b (.cell c d)) := rfl
    rw [hop]
    simp [ServiceReq.root, ServiceReq.child, ServiceReq.axis]
    rw [genRowMemForest_three_chain32_size]
    simp [nounWalkSize]
    omega

theorem gen_op0_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ) {subject : Noun} {axis : ℕ} {result : Noun}
    (hs : Noun.slot axis subject = some result)
    {t : NTree (GenComputeRow K)} {r : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) subject (op0 axis) = .ok (t, r))
    (hne : .atom axis ≠ subject) :
    (genMemForestFromTree E z α lmb t).length = 2 ∧
      totalSize (genMemForestFromTree E z α lmb t) =
        5 + recordTreeSize subject result axis := by
  refine gen_ok_mem (lmb := lmb) E z α h (gen_op0 (K := K) n hs) ?_ ?_
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_two,
      genMemForestFromList_nil, List.append_nil]
    exact genRowMemForest_op0_length E z α axis subject result 0 0 hne
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_two,
      genMemForestFromList_nil, List.append_nil]
    exact genRowMemForest_op0_size E z α axis subject result 0 0 hne

theorem gen_op9_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ) {subject c core arm result : Noun} {axis : ℕ}
    {coreTree invokeTree t : NTree (GenComputeRow K)} {r : Noun}
    (hc : genComputeSkeleton (K := K) n subject c = .ok (coreTree, core))
    (hslot : Noun.slot axis core = some arm)
    (harm : genComputeSkeleton (K := K) n core arm = .ok (invokeTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) subject
      (.cell (.atom 9) (.cell (.atom axis) c)) = .ok (t, r)) :
    (genMemForestFromTree E z α lmb t).length =
      2 + (genMemForestFromTree E z α lmb coreTree).length +
        (genMemForestFromTree E z α lmb invokeTree).length ∧
    totalSize (genMemForestFromTree E z α lmb t) =
      8 + nounWalkSize c + recordTreeSize core arm axis +
        totalSize (genMemForestFromTree E z α lmb coreTree) +
        totalSize (genMemForestFromTree E z α lmb invokeTree) := by
  refine gen_ok_mem (lmb := lmb) E z α h (gen_op9 (K := K) n hc hslot harm) ?_ ?_
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_three,
      genMemForestFromList_two, List.length_append, List.length_append]
    simp [ServiceReq.root, ServiceReq.child, ServiceReq.axis]
    rw [genRowMemForest_three_chain32_gen_length]
    omega
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_three,
      genMemForestFromList_two, totalSize_append, totalSize_append]
    simp [ServiceReq.root, ServiceReq.child, ServiceReq.axis]
    rw [genRowMemForest_three_chain32_gen_size]
    simp [nounWalkSize]
    omega

theorem gen_invokeAxis_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ) {subject core arm result : Noun} {axis : ℕ}
    {coreTree invokeTree t : NTree (GenComputeRow K)} {r : Noun}
    (hcore : genComputeSkeleton (K := K) (n + 2) subject (op0 1) =
      .ok (coreTree, core))
    (hslotA : Noun.slot axis core = some arm)
    (harm : genComputeSkeleton (K := K) (n + 2) core arm = .ok (invokeTree, result))
    (h : genComputeSkeleton (K := K) (n + 3) subject (invokeAxis axis) = .ok (t, r)) :
    (genMemForestFromTree E z α lmb t).length =
      2 + (genMemForestFromTree E z α lmb coreTree).length +
        (genMemForestFromTree E z α lmb invokeTree).length ∧
    totalSize (genMemForestFromTree E z α lmb t) =
      11 + recordTreeSize core arm axis +
        totalSize (genMemForestFromTree E z α lmb coreTree) +
        totalSize (genMemForestFromTree E z α lmb invokeTree) := by
  have hop9 :
      genComputeSkeleton (K := K) (n + 3) subject
        (.cell (.atom 9) (.cell (.atom axis) (op0 1))) = .ok (t, r) := by
    simpa [invokeAxis, op0] using h
  have hmem := gen_op9_mem (lmb := lmb) E z α (n + 2) hcore hslotA harm hop9
  have hwalk : nounWalkSize (op0 1) = 3 := nounWalkSize_op0 1
  constructor
  · exact hmem.1
  · have := hmem.2
    omega

theorem atom_ne_addCore (n : ℕ) (acc i m : Noun) :
    Noun.atom n ≠ addCore acc i m := by
  simp [addCore]

theorem atom_ne_macCoreAt (n : ℕ) (acc i k m : Noun) :
    Noun.atom n ≠ macCoreAt acc i k m := by
  simp [macCoreAt]

theorem atom_ne_macCore (n : ℕ) (acc k m : Noun) :
    Noun.atom n ≠ macCore acc k m :=
  atom_ne_macCoreAt n acc (Noun.atom 0) k m

theorem atom_ne_cell_battery_sample (n : ℕ) (batt samp : Noun) :
    Noun.atom n ≠ Noun.cell batt samp :=
  atom_ne_cell n batt samp

theorem atom_ne_mmSubject (n : ℕ) : Noun.atom n ≠ mmSubject := by
  simp [mmSubject, mmA, mmB]

/-! ## Record sizes on `addCore` / `macCoreAt` slot reads -/

theorem recordTreeSize_axis4 (hd tl child : Noun) :
    recordTreeSize (.cell hd tl) child 4 =
      2 + descentForestSize child hd 2 + nounWalkSize tl := by
  unfold recordTreeSize
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_four)]
  simp [formulaHead, formulaTail, axisRest_four]
  omega

theorem recordTreeSize_axis5 (hd tl child : Noun) :
    recordTreeSize (.cell hd tl) child 5 =
      2 + descentForestSize child hd 3 + nounWalkSize tl := by
  unfold recordTreeSize
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_five)]
  simp [formulaHead, formulaTail, axisRest_five]
  omega

theorem recordTreeSize_axis6 (hd tl child : Noun) :
    recordTreeSize (.cell hd tl) child 6 =
      2 + nounWalkSize hd + descentForestSize child tl 2 := by
  unfold recordTreeSize
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_six)]
  simp [formulaHead, formulaTail, axisRest_six]
  omega

theorem recordTreeSize_axis14 (root child : Noun) :
    recordTreeSize root child 14 =
      2 + nounWalkSize (formulaHead root)
        + descentForestSize child (formulaTail root) 6 := by
  unfold recordTreeSize
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_fourteen)]
  simp [axisRest_fourteen]
  omega

theorem recordTreeSize_axis15 (root child : Noun) :
    recordTreeSize root child 15 =
      2 + nounWalkSize (formulaHead root)
        + descentForestSize child (formulaTail root) 7 := by
  unfold recordTreeSize
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_fifteen)]
  simp [axisRest_fifteen]
  omega

theorem recordTreeSize_axis30 (root child : Noun) :
    recordTreeSize root child 30 =
      2 + nounWalkSize (formulaHead root)
        + descentForestSize child (formulaTail root) 14 := by
  unfold recordTreeSize
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_thirty)]
  simp [axisRest_thirty]
  omega

theorem recordTreeSize_axis31 (root child : Noun) :
    recordTreeSize root child 31 =
      2 + nounWalkSize (formulaHead root)
        + descentForestSize child (formulaTail root) 15 := by
  unfold recordTreeSize
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_thirtyone)]
  simp [axisRest_thirtyone]
  omega

theorem formulaHead_addArm : formulaHead addArm = .atom 6 := by
  simp [addArm, op6, formulaHead]

theorem formulaTail_addArm :
    formulaTail addArm =
      .cell (op5 (op0 14) (op0 15))
        (.cell (op0 6) (slam (op0 2) addNewSample 2)) := by
  simp [addArm, op6, formulaTail]

theorem formulaHead_mmBattery : formulaHead mmBattery = macArm := by
  simp [mmBattery, formulaHead]

theorem formulaTail_mmBattery : formulaTail mmBattery = addArm := by
  simp [mmBattery, formulaTail]

theorem nounWalkSize_addCore_sample (acc i m : Noun) :
    nounWalkSize (.cell acc (.cell i m)) =
      2 + nounWalkSize acc + nounWalkSize i + nounWalkSize m := by
  simp [nounWalkSize]
  omega

theorem nounWalkSize_macCoreAt_sample (acc i n m : Noun) :
    nounWalkSize (.cell acc (.cell i (.cell n m))) =
      3 + nounWalkSize acc + nounWalkSize i + nounWalkSize n +
        nounWalkSize m := by
  simp [nounWalkSize]
  omega

theorem descentForestSize_addArm_3 (child : Noun) :
    descentForestSize child addArm 3 = 3 + nounWalkSize child := by
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_three)]
  simp [axisRest_three]
  rw [formulaHead_addArm, descentForestSize_of_lt2 (h := by omega)]
  simp [nounWalkSize]
  omega

theorem descentForestSize_addArm_7 (child : Noun) :
    descentForestSize child addArm 7 = 13 + nounWalkSize child := by
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_seven)]
  simp [axisRest_seven]
  rw [formulaHead_addArm, formulaTail_addArm]
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_three)]
  simp [axisRest_three]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [formulaHead, formulaTail, nounWalkSize, nounWalkSize_op5, nounWalkSize_op0]
  omega

theorem descentForestSize_mmBattery_2 (child : Noun) :
    descentForestSize child mmBattery 2 = 47 + nounWalkSize child := by
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_two)]
  simp [axisRest_two]
  rw [formulaHead_mmBattery, formulaTail_mmBattery]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [nounWalkSize_addArm]
  omega

theorem descentForestSize_mmBattery_3 (child : Noun) :
    descentForestSize child mmBattery 3 = 71 + nounWalkSize child := by
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_three)]
  simp [axisRest_three]
  rw [formulaHead_mmBattery, formulaTail_mmBattery]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [nounWalkSize_macArm]
  omega

theorem descentForestSize_mmBattery_7 (child : Noun) :
    descentForestSize child mmBattery 7 = 73 + nounWalkSize child := by
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_seven)]
  simp [axisRest_seven]
  rw [formulaHead_mmBattery, formulaTail_mmBattery]
  rw [descentForestSize_addArm_3]
  simp [nounWalkSize_macArm]
  omega

theorem descentForestSize_mmBattery_15 (child : Noun) :
    descentForestSize child mmBattery 15 = 83 + nounWalkSize child := by
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_fifteen)]
  simp [axisRest_fifteen]
  rw [formulaHead_mmBattery, formulaTail_mmBattery]
  rw [descentForestSize_addArm_7]
  simp [nounWalkSize_macArm]
  omega

theorem recordTreeSize_addCore_atoms_axis2 (acc i m : ℕ) :
    recordTreeSize (addCore (.atom acc) (.atom i) (.atom m)) addArm 2 = 53 := by
  simp [addCore]
  rw [recordTreeSize_axis2]
  simp [nounWalkSize_addArm, nounWalkSize]

theorem recordTreeSize_addCore_atoms_axis6 (acc i m x : ℕ) :
    recordTreeSize (addCore (.atom acc) (.atom i) (.atom m)) (.atom x) 6 = 53 := by
  simp [addCore]
  rw [recordTreeSize_axis6]
  simp [nounWalkSize_addArm]
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_two)]
  simp [axisRest_two]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [formulaHead, formulaTail, nounWalkSize]

theorem recordTreeSize_addCore_atoms_axis14 (acc i m x : ℕ) :
    recordTreeSize (addCore (.atom acc) (.atom i) (.atom m)) (.atom x) 14 = 53 := by
  simp [addCore]
  rw [recordTreeSize_axis14]
  simp [formulaHead, formulaTail, nounWalkSize_addArm]
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_six)]
  simp [axisRest_six]
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_two)]
  simp [axisRest_two]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [formulaHead, formulaTail, nounWalkSize]

theorem recordTreeSize_addCore_atoms_axis15 (acc i m x : ℕ) :
    recordTreeSize (addCore (.atom acc) (.atom i) (.atom m)) (.atom x) 15 = 53 := by
  simp [addCore]
  rw [recordTreeSize_axis15]
  simp [formulaHead, formulaTail, nounWalkSize_addArm, nounWalkSize]
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_seven)]
  simp [axisRest_seven]
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_three)]
  simp [axisRest_three]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [formulaHead, formulaTail, nounWalkSize]

theorem recordTreeSize_macCoreAt_atoms_axis2 (acc i n m : ℕ) :
    recordTreeSize (macCoreAt (.atom acc) (.atom i) (.atom n) (.atom m))
      mmBattery 2 = 125 := by
  simp [macCoreAt]
  rw [recordTreeSize_axis2]
  simp [nounWalkSize_mmBattery, nounWalkSize]

theorem recordTreeSize_macCoreAt_atoms_axis4 (acc i n m : ℕ) :
    recordTreeSize (macCoreAt (.atom acc) (.atom i) (.atom n) (.atom m))
      macArm 4 = 125 := by
  simp [macCoreAt]
  rw [recordTreeSize_axis4, descentForestSize_mmBattery_2]
  simp [nounWalkSize_macArm, nounWalkSize]

theorem recordTreeSize_macCoreAt_atoms_axis5 (acc i n m : ℕ) :
    recordTreeSize (macCoreAt (.atom acc) (.atom i) (.atom n) (.atom m))
      addArm 5 = 125 := by
  simp [macCoreAt]
  rw [recordTreeSize_axis5, descentForestSize_mmBattery_3]
  simp [nounWalkSize_addArm, nounWalkSize]

theorem recordTreeSize_macCoreAt_atoms_axis6 (acc i n m x : ℕ) :
    recordTreeSize (macCoreAt (.atom acc) (.atom i) (.atom n) (.atom m))
      (.atom x) 6 = 125 := by
  simp [macCoreAt]
  rw [recordTreeSize_axis6]
  simp [nounWalkSize_mmBattery]
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_two)]
  simp [axisRest_two]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [formulaHead, formulaTail, nounWalkSize]

theorem recordTreeSize_macCoreAt_atoms_axis14 (acc i n m x : ℕ) :
    recordTreeSize (macCoreAt (.atom acc) (.atom i) (.atom n) (.atom m))
      (.atom x) 14 = 125 := by
  simp [macCoreAt]
  rw [recordTreeSize_axis14]
  simp [formulaHead, formulaTail, nounWalkSize_mmBattery]
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_six)]
  simp [axisRest_six]
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_two)]
  simp [axisRest_two]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [formulaHead, formulaTail, nounWalkSize]

theorem recordTreeSize_macCoreAt_atoms_axis30 (acc i n m x : ℕ) :
    recordTreeSize (macCoreAt (.atom acc) (.atom i) (.atom n) (.atom m))
      (.atom x) 30 = 125 := by
  simp [macCoreAt]
  rw [recordTreeSize_axis30]
  simp [formulaHead, formulaTail, nounWalkSize_mmBattery]
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_fourteen)]
  simp [axisRest_fourteen]
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_six)]
  simp [axisRest_six]
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_two)]
  simp [axisRest_two]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [formulaHead, formulaTail, nounWalkSize]

theorem recordTreeSize_macCoreAt_atoms_axis31 (acc i n m x : ℕ) :
    recordTreeSize (macCoreAt (.atom acc) (.atom i) (.atom n) (.atom m))
      (.atom x) 31 = 125 := by
  simp [macCoreAt]
  rw [recordTreeSize_axis31]
  simp [formulaHead, formulaTail, nounWalkSize_mmBattery]
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_fifteen)]
  simp [axisRest_fifteen]
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_seven)]
  simp [axisRest_seven]
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_three)]
  simp [axisRest_three]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [formulaHead, formulaTail, nounWalkSize]

theorem recordTreeSize_macCore_atoms_axis4 (acc n m : ℕ) :
    recordTreeSize (macCore (.atom acc) (.atom n) (.atom m)) macArm 4 = 125 := by
  simpa [macCore] using recordTreeSize_macCoreAt_atoms_axis4 acc 0 n m

theorem recordTreeSize_mmSubject_atom8 (x : ℕ) :
    recordTreeSize mmSubject (.atom x) 8 = 17 := by
  unfold recordTreeSize
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_eight)]
  simp [mmSubject, formulaHead, formulaTail, nounWalkSize_mmB, axisRest_eight]
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_four)]
  simp [mmA, formulaHead, formulaTail, nounWalkSize, axisRest_four]
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_two)]
  simp [axisRest_two]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [formulaHead, formulaTail, nounWalkSize]

theorem recordTreeSize_mmSubject_atom9 (x : ℕ) :
    recordTreeSize mmSubject (.atom x) 9 = 17 := by
  unfold recordTreeSize
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_nine)]
  simp [mmSubject, formulaHead, formulaTail, nounWalkSize_mmB, axisRest_nine]
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_five)]
  simp [mmA, formulaHead, formulaTail, nounWalkSize, axisRest_five]
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_three)]
  simp [axisRest_three]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [formulaHead, formulaTail, nounWalkSize]

theorem recordTreeSize_mmSubject_atom10 (x : ℕ) :
    recordTreeSize mmSubject (.atom x) 10 = 17 := by
  unfold recordTreeSize
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_ten)]
  simp [mmSubject, formulaHead, formulaTail, nounWalkSize_mmB, axisRest_ten]
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_six)]
  simp [mmA, formulaHead, formulaTail, nounWalkSize, axisRest_six]
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_two)]
  simp [axisRest_two]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [formulaHead, formulaTail, nounWalkSize]

theorem recordTreeSize_mmSubject_atom11 (x : ℕ) :
    recordTreeSize mmSubject (.atom x) 11 = 17 := by
  unfold recordTreeSize
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_eleven)]
  simp [mmSubject, formulaHead, formulaTail, nounWalkSize_mmB, axisRest_eleven]
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_seven)]
  simp [mmA, formulaHead, formulaTail, nounWalkSize, axisRest_seven]
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_three)]
  simp [axisRest_three]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [formulaHead, formulaTail, nounWalkSize]

theorem recordTreeSize_mmSubject_atom12 (x : ℕ) :
    recordTreeSize mmSubject (.atom x) 12 = 17 := by
  unfold recordTreeSize
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_twelve)]
  simp [mmSubject, formulaHead, formulaTail, nounWalkSize_mmA, axisRest_twelve]
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_four)]
  simp [mmB, formulaHead, formulaTail, nounWalkSize, axisRest_four]
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_two)]
  simp [axisRest_two]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [formulaHead, formulaTail, nounWalkSize]

theorem recordTreeSize_mmSubject_atom13 (x : ℕ) :
    recordTreeSize mmSubject (.atom x) 13 = 17 := by
  unfold recordTreeSize
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_thirteen)]
  simp [mmSubject, formulaHead, formulaTail, nounWalkSize_mmA, axisRest_thirteen]
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_five)]
  simp [mmB, formulaHead, formulaTail, nounWalkSize, axisRest_five]
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_three)]
  simp [axisRest_three]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [formulaHead, formulaTail, nounWalkSize]

theorem recordTreeSize_mmSubject_atom14 (x : ℕ) :
    recordTreeSize mmSubject (.atom x) 14 = 17 := by
  unfold recordTreeSize
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_fourteen)]
  simp [mmSubject, formulaHead, formulaTail, nounWalkSize_mmA, axisRest_fourteen]
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_six)]
  simp [mmB, formulaHead, formulaTail, nounWalkSize, axisRest_six]
  rw [descentForestSize_of_head (h2 := by omega) (hh := axisTopBit_two)]
  simp [axisRest_two]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [formulaHead, formulaTail, nounWalkSize]

theorem recordTreeSize_mmSubject_atom15 (x : ℕ) :
    recordTreeSize mmSubject (.atom x) 15 = 17 := by
  unfold recordTreeSize
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_fifteen)]
  simp [mmSubject, formulaHead, formulaTail, nounWalkSize_mmA, axisRest_fifteen]
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_seven)]
  simp [mmB, formulaHead, formulaTail, nounWalkSize, axisRest_seven]
  rw [descentForestSize_of_tail (h2 := by omega) (ht := axisTopBit_three)]
  simp [axisRest_three]
  rw [descentForestSize_of_lt2 (h := by omega)]
  simp [formulaHead, formulaTail, nounWalkSize]

theorem gen_slam_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ) {axis : ℕ}
    {subject bHead bTail sampleF battery sample arm result : Noun}
    {battTree sampTree invokeTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) (n + 3) subject (.cell bHead bTail) =
      .ok (battTree, battery))
    (hs : genComputeSkeleton (K := K) (n + 3) subject sampleF =
      .ok (sampTree, sample))
    (hslot : Noun.slot axis (.cell battery sample) = some arm)
    (harm : genComputeSkeleton (K := K) (n + 3) (.cell battery sample) arm =
      .ok (invokeTree, result))
    (h : genComputeSkeleton (K := K) (n + 5) subject
        (slam (.cell bHead bTail) sampleF axis) = .ok (t, r)) :
    (genMemForestFromTree E z α lmb t).length =
      6 + (genMemForestFromTree E z α lmb battTree).length +
        (genMemForestFromTree E z α lmb sampTree).length +
        (genMemForestFromTree E z α lmb invokeTree).length ∧
    totalSize (genMemForestFromTree E z α lmb t) =
      37 + 2 * nounWalkSize (.cell bHead bTail) + 2 * nounWalkSize sampleF +
        nounWalkSize battery + nounWalkSize sample +
        recordTreeSize (.cell battery sample) arm axis +
        totalSize (genMemForestFromTree E z α lmb battTree) +
        totalSize (genMemForestFromTree E z α lmb sampTree) +
        totalSize (genMemForestFromTree E z α lmb invokeTree) := by
  have hpair :=
    gen_cons (K := K) (n + 3) (lTree := battTree) (rTree := sampTree) hb hs
  have hcore :=
    gen_op0 (K := K) (n + 2) (slot_1 (.cell battery sample))
  have hax := gen_invokeAxis (K := K) (n + 1) hcore hslot harm
  simp only [slam] at h
  have h7 := gen_op7_mem (lmb := lmb) E z α (n + 4) hpair hax h
  have hp := gen_cons_mem (lmb := lmb) E z α (n + 3) hb hs hpair
  have hx := gen_invokeAxis_mem (lmb := lmb) E z α (n + 1) hcore hslot harm hax
  have hc0 := gen_op0_mem (lmb := lmb) E z α (n + 2) (slot_1 (.cell battery sample)) hcore
    (atom_ne_cell_battery_sample 1 battery sample)
  have hwalk7 : nounWalkSize (invokeAxis axis) = 7 := nounWalkSize_invokeAxis axis
  have hwalkC : nounWalkSize (.cell (.cell bHead bTail) sampleF) =
      1 + nounWalkSize (.cell bHead bTail) + nounWalkSize sampleF :=
    nounWalkSize_cell _ _
  have hwalkCore : nounWalkSize (.cell battery sample) =
      1 + nounWalkSize battery + nounWalkSize sample :=
    nounWalkSize_cell _ _
  have hax1 : recordTreeSize (.cell battery sample) (.cell battery sample) 1 =
      2 + nounWalkSize (.cell battery sample) :=
    recordTreeSize_axis1 _ _
  obtain ⟨h7l, h7s⟩ := h7
  obtain ⟨hpl, hps⟩ := hp
  obtain ⟨hxl, hxs⟩ := hx
  obtain ⟨hc0l, hc0s⟩ := hc0
  constructor
  · omega
  · omega

theorem gen_addArm_done_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ) (acc m : Noun) :
    ∃ t, genComputeSkeleton (K := K) (n + 6) (addCore acc m m) addArm =
      .ok (t, acc) ∧
      (genMemForestFromTree E z α lmb t).length = 9 ∧
      totalSize (genMemForestFromTree E z α lmb t) =
        112 + recordTreeSize (addCore acc m m) m 14 +
          recordTreeSize (addCore acc m m) m 15 +
          recordTreeSize (addCore acc m m) acc 6 := by
  have h14 := gen_op0 (K := K) (n + 3) (addCore_slot14 acc m m)
  have h15 := gen_op0 (K := K) (n + 3) (addCore_slot15 acc m m)
  have hcond := gen_op5 (K := K) (n + 4) h14 h15
  rw [tis_self m] at hcond
  have hthen := gen_op0 (K := K) (n + 4) (addCore_slot6 acc m m)
  have hop := gen_op6_zero (K := K) (n + 5)
    (d := slam (op0 2) addNewSample 2) hcond hthen
  refine ⟨_, by simpa [addArm] using hop, ?_⟩
  have h6 := gen_op6_zero_mem (lmb := lmb) E z α (n + 5) hcond hthen
    (by simpa [addArm] using hop)
  have hc := gen_op5_mem (lmb := lmb) E z α (n + 4) h14 h15 hcond
  have hs14 := gen_op0_mem (lmb := lmb) E z α (n + 3) (addCore_slot14 acc m m) h14
    (atom_ne_addCore 14 acc m m)
  have hs15 := gen_op0_mem (lmb := lmb) E z α (n + 3) (addCore_slot15 acc m m) h15
    (atom_ne_addCore 15 acc m m)
  have hs6 := gen_op0_mem (lmb := lmb) E z α (n + 4) (addCore_slot6 acc m m) hthen
    (atom_ne_addCore 6 acc m m)
  have hb : nounWalkSize (op5 (op0 14) (op0 15)) = 9 := by
    simp [nounWalkSize_op5, nounWalkSize_op0]
  have w14 : nounWalkSize (op0 14) = 3 := nounWalkSize_op0 14
  have w15 : nounWalkSize (op0 15) = 3 := nounWalkSize_op0 15
  have hc0 : nounWalkSize (op0 6) = 3 := nounWalkSize_op0 6
  have hd : nounWalkSize (slam (op0 2) addNewSample 2) = 29 := by
    simp [nounWalkSize_slam, nounWalkSize_op0, nounWalkSize_addNewSample]
  obtain ⟨h6l, h6s⟩ := h6
  obtain ⟨hcl, hcs⟩ := hc
  obtain ⟨hs14l, hs14s⟩ := hs14
  obtain ⟨hs15l, hs15s⟩ := hs15
  obtain ⟨hs6l, hs6s⟩ := hs6
  constructor
  · omega
  · omega

theorem gen_addNewSample_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n acc i m : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 5)
      (addCore (.atom acc) (.atom i) (.atom m)) addNewSample =
      .ok (t, .cell (.atom (acc + 1)) (.cell (.atom (i + 1)) (.atom m))) ∧
      (genMemForestFromTree E z α lmb t).length = 10 ∧
      totalSize (genMemForestFromTree E z α lmb t) =
        57 + recordTreeSize (addCore (.atom acc) (.atom i) (.atom m)) (.atom acc) 6 +
          recordTreeSize (addCore (.atom acc) (.atom i) (.atom m)) (.atom i) 14 +
          recordTreeSize (addCore (.atom acc) (.atom i) (.atom m)) (.atom m) 15 := by
  have h6 := gen_op0 (K := K) (n + 2)
    (addCore_slot6 (.atom acc) (.atom i) (.atom m))
  have h14 := gen_op0 (K := K) (n + 1)
    (addCore_slot14 (.atom acc) (.atom i) (.atom m))
  have h15 := gen_op0 (K := K) (n + 2)
    (addCore_slot15 (.atom acc) (.atom i) (.atom m))
  have hincA := gen_op4 (K := K) (n + 3) h6 (lus_nat acc)
  have hincI := gen_op4 (K := K) (n + 2) h14 (lus_nat i)
  have hinner := gen_cons (K := K) (n + 3) hincI h15
  have houter := gen_cons (K := K) (n + 4) hincA hinner
  refine ⟨_, houter, ?_⟩
  have ho := gen_cons_mem (lmb := lmb) E z α (n + 4) hincA hinner houter
  have hi := gen_cons_mem (lmb := lmb) E z α (n + 3) hincI h15 hinner
  have hA := gen_op4_mem (lmb := lmb) E z α (n + 3) h6 (lus_nat acc) hincA
  have hI := gen_op4_mem (lmb := lmb) E z α (n + 2) h14 (lus_nat i) hincI
  have hs6 := gen_op0_mem (lmb := lmb) E z α (n + 2)
    (addCore_slot6 (.atom acc) (.atom i) (.atom m)) h6
    (atom_ne_addCore 6 (.atom acc) (.atom i) (.atom m))
  have hs14 := gen_op0_mem (lmb := lmb) E z α (n + 1)
    (addCore_slot14 (.atom acc) (.atom i) (.atom m)) h14
    (atom_ne_addCore 14 (.atom acc) (.atom i) (.atom m))
  have hs15 := gen_op0_mem (lmb := lmb) E z α (n + 2)
    (addCore_slot15 (.atom acc) (.atom i) (.atom m)) h15
    (atom_ne_addCore 15 (.atom acc) (.atom i) (.atom m))
  have w6 : nounWalkSize (op0 6) = 3 := nounWalkSize_op0 6
  have w14 : nounWalkSize (op0 14) = 3 := nounWalkSize_op0 14
  have w15 : nounWalkSize (op0 15) = 3 := nounWalkSize_op0 15
  have w4_6 : nounWalkSize (.cell (.atom 4) (op0 6)) = 5 := by
    simp [nounWalkSize, op0]
  have w4_14 : nounWalkSize (.cell (.atom 4) (op0 14)) = 5 := by
    simp [nounWalkSize, op0]
  have winner : nounWalkSize (.cell (.cell (.atom 4) (op0 14)) (op0 15)) = 9 := by
    simp [nounWalkSize, op0]
  obtain ⟨hol, hos⟩ := ho
  obtain ⟨hil, his⟩ := hi
  obtain ⟨hAl, hAs⟩ := hA
  obtain ⟨hIl, hIs⟩ := hI
  obtain ⟨hs6l, hs6s⟩ := hs6
  obtain ⟨hs14l, hs14s⟩ := hs14
  obtain ⟨hs15l, hs15s⟩ := hs15
  constructor
  · omega
  · omega

theorem gen_macArm_done_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ) (acc k m : Noun) :
    ∃ t, genComputeSkeleton (K := K) (n + 6) (macCoreAt acc k k m) macArm =
      .ok (t, acc) ∧
      (genMemForestFromTree E z α lmb t).length = 9 ∧
      totalSize (genMemForestFromTree E z α lmb t) =
        160 + recordTreeSize (macCoreAt acc k k m) k 14 +
          recordTreeSize (macCoreAt acc k k m) k 30 +
          recordTreeSize (macCoreAt acc k k m) acc 6 := by
  have h14 := gen_op0 (K := K) (n + 3) (macCoreAt_slot14 acc k k m)
  have h30 := gen_op0 (K := K) (n + 3) (macCoreAt_slot30 acc k k m)
  have hcond := gen_op5 (K := K) (n + 4) h14 h30
  rw [tis_self k] at hcond
  have hthen := gen_op0 (K := K) (n + 4) (macCoreAt_slot6 acc k k m)
  have hop := gen_op6_zero (K := K) (n + 5)
    (d := slam (op0 2) macNewSample 4) hcond hthen
  refine ⟨_, by simpa [macArm] using hop, ?_⟩
  have h6 := gen_op6_zero_mem (lmb := lmb) E z α (n + 5) hcond hthen
    (by simpa [macArm] using hop)
  have hc := gen_op5_mem (lmb := lmb) E z α (n + 4) h14 h30 hcond
  have hs14 := gen_op0_mem (lmb := lmb) E z α (n + 3) (macCoreAt_slot14 acc k k m) h14
    (atom_ne_macCoreAt 14 acc k k m)
  have hs30 := gen_op0_mem (lmb := lmb) E z α (n + 3) (macCoreAt_slot30 acc k k m) h30
    (atom_ne_macCoreAt 30 acc k k m)
  have hs6 := gen_op0_mem (lmb := lmb) E z α (n + 4) (macCoreAt_slot6 acc k k m) hthen
    (atom_ne_macCoreAt 6 acc k k m)
  have hb : nounWalkSize (op5 (op0 14) (op0 30)) = 9 := by
    simp [nounWalkSize_op5, nounWalkSize_op0]
  have w14 : nounWalkSize (op0 14) = 3 := nounWalkSize_op0 14
  have w30 : nounWalkSize (op0 30) = 3 := nounWalkSize_op0 30
  have hc0 : nounWalkSize (op0 6) = 3 := nounWalkSize_op0 6
  have hd : nounWalkSize (slam (op0 2) macNewSample 4) = 53 := by
    simp [nounWalkSize_slam, nounWalkSize_op0, nounWalkSize_macNewSample]
  obtain ⟨h6l, h6s⟩ := h6
  obtain ⟨hcl, hcs⟩ := hc
  obtain ⟨hs14l, hs14s⟩ := hs14
  obtain ⟨hs30l, hs30s⟩ := hs30
  obtain ⟨hs6l, hs6s⟩ := hs6
  constructor
  · omega
  · omega

theorem gen_addArm_one_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 16)
      (addCore (.atom acc) (.atom 0) (.atom 1)) addArm =
      .ok (t, .atom (acc + 1)) ∧
      (genMemForestFromTree E z α lmb t).length = 34 ∧
      totalSize (genMemForestFromTree E z α lmb t) =
        404 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom 0) 14 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom 1) 15 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) addArm 2 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom acc) 6 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom 0) 14 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom 1) 15 +
          recordTreeSize (addCore (.atom (acc + 1)) (.atom 1) (.atom 1)) (.atom 1) 14 +
          recordTreeSize (addCore (.atom (acc + 1)) (.atom 1) (.atom 1)) (.atom 1) 15 +
          recordTreeSize (addCore (.atom (acc + 1)) (.atom 1) (.atom 1))
            (.atom (acc + 1)) 6 +
          recordTreeSize
            (.cell addArm (.cell (.atom (acc + 1)) (.cell (.atom 1) (.atom 1))))
            addArm 2 := by
  have h14 := gen_op0 (K := K) (n + 13)
    (addCore_slot14 (.atom acc) (.atom 0) (.atom 1))
  have h15 := gen_op0 (K := K) (n + 13)
    (addCore_slot15 (.atom acc) (.atom 0) (.atom 1))
  have hcond := gen_op5 (K := K) (n + 14) h14 h15
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  obtain ⟨nsTree, hns, hns_len, hns_sz⟩ :=
    gen_addNewSample_mem (lmb := lmb) E z α (n + 8) acc 0 1
  have hbatt := gen_op0 (K := K) (n + 12)
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1))
  obtain ⟨doneTree, hdone, hdone_len, hdone_sz⟩ :=
    gen_addArm_done_mem (lmb := lmb) E z α (n + 7) (.atom (acc + 1)) (.atom 1)
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 10) (axis := 2)
    (bHead := .atom 0) (bTail := .atom 2) hbatt hns
    (addCore_slot2 (.atom (acc + 1)) (.atom 1) (.atom 1)) hdone
  have hop6 := gen_op6_one (K := K) (n + 15) (c := op0 6) hcond hslam
  refine ⟨_, by simpa [addArm, slam, op0] using hop6, ?_⟩
  have h6 := gen_op6_one_mem (lmb := lmb) E z α (n + 15) hcond hslam
    (by simpa [addArm, slam, op0] using hop6)
  have hc := gen_op5_mem (lmb := lmb) E z α (n + 14) h14 h15 hcond
  have hs14 := gen_op0_mem (lmb := lmb) E z α (n + 13)
    (addCore_slot14 (.atom acc) (.atom 0) (.atom 1)) h14
    (atom_ne_addCore 14 (.atom acc) (.atom 0) (.atom 1))
  have hs15 := gen_op0_mem (lmb := lmb) E z α (n + 13)
    (addCore_slot15 (.atom acc) (.atom 0) (.atom 1)) h15
    (atom_ne_addCore 15 (.atom acc) (.atom 0) (.atom 1))
  have hss := gen_slam_mem (lmb := lmb) E z α (n + 10) hbatt hns
    (addCore_slot2 (.atom (acc + 1)) (.atom 1) (.atom 1)) hdone hslam
  have hbatt_m := gen_op0_mem (lmb := lmb) E z α (n + 12)
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1)) hbatt
    (atom_ne_addCore 2 (.atom acc) (.atom 0) (.atom 1))
  have hb : nounWalkSize (op5 (op0 14) (op0 15)) = 9 := by
    simp [nounWalkSize_op5, nounWalkSize_op0]
  have w14 : nounWalkSize (op0 14) = 3 := nounWalkSize_op0 14
  have w15 : nounWalkSize (op0 15) = 3 := nounWalkSize_op0 15
  have wd : nounWalkSize (slam (.cell (.atom 0) (.atom 2)) addNewSample 2) = 29 := by
    simp [nounWalkSize_slam, nounWalkSize, nounWalkSize_addNewSample]
  have wbattF : nounWalkSize (.cell (.atom 0) (.atom 2)) = 3 := by simp [nounWalkSize]
  have wsampF : nounWalkSize addNewSample = 15 := nounWalkSize_addNewSample
  have wbatt : nounWalkSize addArm = 45 := nounWalkSize_addArm
  have wsamp : nounWalkSize
      (.cell (.atom (acc + 1)) (.cell (.atom (0 + 1)) (.atom 1))) = 5 := by
    simp [nounWalkSize]
  have wc' : nounWalkSize (.cell (.atom 0) (.atom 6)) = 3 := by simp [nounWalkSize]
  have hcoreEq :
      Noun.cell addArm (.cell (.atom (acc + 1)) (.cell (.atom (0 + 1)) (.atom 1))) =
        .cell addArm (.cell (.atom (acc + 1)) (.cell (.atom 1) (.atom 1))) := by
    simp
  obtain ⟨h6l, h6s⟩ := h6
  obtain ⟨hcl, hcs⟩ := hc
  obtain ⟨hs14l, hs14s⟩ := hs14
  obtain ⟨hs15l, hs15s⟩ := hs15
  obtain ⟨hssl, hsss⟩ := hss
  obtain ⟨hbattl, hbatts⟩ := hbatt_m
  rw [hcoreEq] at hsss
  constructor
  · omega
  · rw [h6s]
    rw [hcs]
    rw [hsss]
    rw [hs14s]
    rw [hs15s]
    rw [hns_sz]
    rw [hdone_sz]
    rw [hbatts]
    simp only [hb, w14, w15, wd, wbattF, wsampF, wbatt, wsamp, wc']
    omega

theorem gen_macSampleF_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ) {subject aH aT nH nT mF acc k m : Noun}
    {aTree nTree mTree t : NTree (GenComputeRow K)} {r : Noun}
    (ha : genComputeSkeleton (K := K) (n + 2) subject (.cell aH aT) = .ok (aTree, acc))
    (hn : genComputeSkeleton (K := K) n subject (.cell nH nT) = .ok (nTree, k))
    (hm : genComputeSkeleton (K := K) n subject mF = .ok (mTree, m))
    (h : genComputeSkeleton (K := K) (n + 3) subject
      (.cell (.cell aH aT) (.cell (op1 0) (.cell (.cell nH nT) mF))) = .ok (t, r)) :
    (genMemForestFromTree E z α lmb t).length =
      4 + (genMemForestFromTree E z α lmb aTree).length +
        (genMemForestFromTree E z α lmb nTree).length +
        (genMemForestFromTree E z α lmb mTree).length ∧
    totalSize (genMemForestFromTree E z α lmb t) =
      23 + nounWalkSize (.cell aH aT) +
        3 * nounWalkSize (.cell nH nT) + 3 * nounWalkSize mF +
        totalSize (genMemForestFromTree E z α lmb aTree) +
        totalSize (genMemForestFromTree E z α lmb nTree) +
        totalSize (genMemForestFromTree E z α lmb mTree) := by
  have hnm := gen_cons (K := K) n hn hm
  have hz := gen_op1 (K := K) n subject 0
  have hinner := gen_cons (K := K) (n + 1) hz hnm
  have ho := gen_cons_mem (lmb := lmb) E z α (n + 2) ha hinner h
  have hi := gen_cons_mem (lmb := lmb) E z α (n + 1) hz hnm hinner
  have hnm_m := gen_cons_mem (lmb := lmb) E z α n hn hm hnm
  have hz_m := gen_op1_mem (lmb := lmb) E z α n subject 0 hz
  have wZ : nounWalkSize (.cell (.atom 1) (.atom 0)) = 3 := by simp [nounWalkSize]
  obtain ⟨hol, hos⟩ := ho
  obtain ⟨hil, his⟩ := hi
  obtain ⟨hnml, hnms⟩ := hnm_m
  obtain ⟨hzl, hzs⟩ := hz_m
  constructor
  · omega
  · rw [hos]
    rw [his]
    rw [hnms]
    rw [hzs]
    simp only [wZ, nounWalkSize, op1]
    omega

theorem gen_invokeMac_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ) {subject aH aT nH nT mF acc k m result : Noun}
    {aTree nTree mTree armTree t : NTree (GenComputeRow K)} {r : Noun}
    (ha : genComputeSkeleton (K := K) (n + 2) subject (.cell aH aT) = .ok (aTree, acc))
    (hn : genComputeSkeleton (K := K) n subject (.cell nH nT) = .ok (nTree, k))
    (hm : genComputeSkeleton (K := K) n subject mF = .ok (mTree, m))
    (harm : genComputeSkeleton (K := K) (n + 3) (macCore acc k m) macArm =
      .ok (armTree, result))
    (h : genComputeSkeleton (K := K) (n + 5) subject
        (invokeMac (.cell aH aT) (.cell nH nT) mF) = .ok (t, r)) :
    (genMemForestFromTree E z α lmb t).length =
      11 + (genMemForestFromTree E z α lmb aTree).length +
        (genMemForestFromTree E z α lmb nTree).length +
        (genMemForestFromTree E z α lmb mTree).length +
        (genMemForestFromTree E z α lmb armTree).length ∧
    totalSize (genMemForestFromTree E z α lmb t) =
      37 + 2 * nounWalkSize (.cell (.atom 1) mmBattery) +
        2 * nounWalkSize
          (.cell (.cell aH aT) (.cell (op1 0) (.cell (.cell nH nT) mF))) +
        nounWalkSize mmBattery +
        nounWalkSize (.cell acc (.cell (.atom 0) (.cell k m))) +
        recordTreeSize (macCore acc k m) macArm 4 +
        (4 + nounWalkSize mmBattery) +
        (23 + nounWalkSize (.cell aH aT) +
          3 * nounWalkSize (.cell nH nT) + 3 * nounWalkSize mF +
          totalSize (genMemForestFromTree E z α lmb aTree) +
          totalSize (genMemForestFromTree E z α lmb nTree) +
          totalSize (genMemForestFromTree E z α lmb mTree)) +
        totalSize (genMemForestFromTree E z α lmb armTree) := by
  have hqB := gen_quote (K := K) (n + 2) subject mmBattery
  obtain ⟨sfTree, hsf⟩ := gen_macSampleF (K := K) n ha hn hm
  simp only [invokeMac, slam, quote] at h
  have hss := gen_slam_mem (lmb := lmb) E z α n hqB hsf
    (macCoreAt_slot4 acc (.atom 0) k m) harm h
  have hq := gen_quote_mem (lmb := lmb) E z α (n + 2) subject mmBattery hqB
  have hsf_m := gen_macSampleF_mem (lmb := lmb) E z α n ha hn hm hsf
  have wQ : nounWalkSize (.cell (.atom 1) mmBattery) = 2 + nounWalkSize mmBattery := by
    simp [nounWalkSize]
  have hmac :
      Noun.cell mmBattery (.cell acc (.cell (.atom 0) (.cell k m))) =
        macCore acc k m := by
    simp [macCore, macCoreAt]
  obtain ⟨hssl, hsss⟩ := hss
  obtain ⟨hql, hqs⟩ := hq
  obtain ⟨hsfl, hsfs⟩ := hsf_m
  rw [hmac] at hsss
  constructor
  · omega
  · rw [hqs] at hsss
    rw [hsfs] at hsss
    simpa only [wQ] using hsss

theorem gen_addFromMac_m0_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 12)
      (macCore (.atom acc) (.atom 1) (.atom 0)) addFromMac = .ok (t, .atom acc) ∧
      (genMemForestFromTree E z α lmb t).length = 24 ∧
      totalSize (genMemForestFromTree E z α lmb t) =
        269 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0)) addArm 5 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0)) (.atom acc) 6 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0)) (.atom 0) 31 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 0)) addArm 2 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 0)) (.atom 0) 14 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 0)) (.atom 0) 15 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 0)) (.atom acc) 6 := by
  have h5 := gen_op0 (K := K) (n + 9)
    (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hacc := gen_op0 (K := K) (n + 8)
    (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hz := gen_op1 (K := K) (n + 7)
    (macCore (.atom acc) (.atom 1) (.atom 0)) 0
  have hm := gen_op0 (K := K) (n + 7)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hinner := gen_cons (K := K) (n + 8) hz hm
  have hsmpl := gen_cons (K := K) (n + 9) hacc hinner
  obtain ⟨doneTree, hdone, hdone_len, hdone_sz⟩ :=
    gen_addArm_done_mem (lmb := lmb) E z α (n + 4) (.atom acc) (.atom 0)
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 7) (axis := 2)
    (bHead := .atom 0) (bTail := .atom 5) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 0)) hdone
  refine ⟨_, by simpa [addFromMac, slam, op0, op1, macCore] using hslam, ?_⟩
  have hss := gen_slam_mem (lmb := lmb) E z α (n + 7) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 0)) hdone
    (by simpa [addFromMac, slam, op0, op1, macCore] using hslam)
  have hs5 := gen_op0_mem (lmb := lmb) E z α (n + 9)
    (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h5
    (atom_ne_macCoreAt 5 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hsmpl_m := gen_cons_mem (lmb := lmb) E z α (n + 9) hacc hinner hsmpl
  have hinner_m := gen_cons_mem (lmb := lmb) E z α (n + 8) hz hm hinner
  have hsacc := gen_op0_mem (lmb := lmb) E z α (n + 8)
    (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hacc
    (atom_ne_macCoreAt 6 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hsz := gen_op1_mem (lmb := lmb) E z α (n + 7)
    (macCore (.atom acc) (.atom 1) (.atom 0)) 0 hz
  have hsm := gen_op0_mem (lmb := lmb) E z α (n + 7)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hm
    (atom_ne_macCoreAt 31 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have wbattF : nounWalkSize (.cell (.atom 0) (.atom 5)) = 3 := by simp [nounWalkSize]
  have wsampF : nounWalkSize
      (.cell (.cell (.atom 0) (.atom 6))
        (.cell (.cell (.atom 1) (.atom 0)) (op0 31))) = 11 := by
    simp [nounWalkSize, op0]
  have wbatt : nounWalkSize addArm = 45 := nounWalkSize_addArm
  have wsamp : nounWalkSize
      (.cell (.atom acc) (.cell (.atom 0) (.atom 0))) = 5 := by
    simp [nounWalkSize]
  have w6 : nounWalkSize (.cell (.atom 0) (.atom 6)) = 3 := by simp [nounWalkSize]
  have wZ : nounWalkSize (.cell (.atom 1) (.atom 0)) = 3 := by simp [nounWalkSize]
  have w31 : nounWalkSize (op0 31) = 3 := nounWalkSize_op0 31
  have wInner : nounWalkSize
      (.cell (.cell (.atom 1) (.atom 0)) (op0 31)) = 7 := by
    simp [nounWalkSize, op0]
  have hcoreEq :
      Noun.cell addArm (.cell (.atom acc) (.cell (.atom 0) (.atom 0))) =
        addCore (.atom acc) (.atom 0) (.atom 0) := by
    simp [addCore]
  obtain ⟨hssl, hsss⟩ := hss
  obtain ⟨hs5l, hs5s⟩ := hs5
  obtain ⟨hsmpl_l, hsmpl_s⟩ := hsmpl_m
  obtain ⟨hinner_l, hinner_s⟩ := hinner_m
  obtain ⟨hsaccl, hsaccs⟩ := hsacc
  obtain ⟨hszl, hszs⟩ := hsz
  obtain ⟨hsml, hsms⟩ := hsm
  rw [hcoreEq] at hsss
  constructor
  · omega
  · rw [hs5s] at hsss
    rw [hsmpl_s] at hsss
    rw [hinner_s] at hsss
    rw [hsaccs] at hsss
    rw [hszs] at hsss
    rw [hsms] at hsss
    rw [hdone_sz] at hsss
    rw [hsss]
    simp only [wbattF, wsampF, wbatt, wsamp, w6, wZ, w31, wInner]
    omega

theorem gen_addFromMac_m1_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 21)
      (macCore (.atom acc) (.atom 1) (.atom 1)) addFromMac =
      .ok (t, .atom (acc + 1)) ∧
      (genMemForestFromTree E z α lmb t).length = 49 ∧
      totalSize (genMemForestFromTree E z α lmb t) =
        561 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1)) addArm 5 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1)) (.atom acc) 6 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1)) (.atom 1) 31 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) addArm 2 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom 0) 14 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom 1) 15 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) addArm 2 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom acc) 6 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom 0) 14 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom 1) 15 +
          recordTreeSize (addCore (.atom (acc + 1)) (.atom 1) (.atom 1)) (.atom 1) 14 +
          recordTreeSize (addCore (.atom (acc + 1)) (.atom 1) (.atom 1)) (.atom 1) 15 +
          recordTreeSize (addCore (.atom (acc + 1)) (.atom 1) (.atom 1))
            (.atom (acc + 1)) 6 +
          recordTreeSize
            (.cell addArm (.cell (.atom (acc + 1)) (.cell (.atom 1) (.atom 1))))
            addArm 2 := by
  have h5 := gen_op0 (K := K) (n + 18)
    (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have haccS := gen_op0 (K := K) (n + 17)
    (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hz := gen_op1 (K := K) (n + 16)
    (macCore (.atom acc) (.atom 1) (.atom 1)) 0
  have hm := gen_op0 (K := K) (n + 16)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hinner := gen_cons (K := K) (n + 17) hz hm
  have hsmpl := gen_cons (K := K) (n + 18) haccS hinner
  obtain ⟨doneTree, hdone, hdone_len, hdone_sz⟩ :=
    gen_addArm_one_mem (lmb := lmb) E z α (n + 3) acc
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 16) (axis := 2)
    (bHead := .atom 0) (bTail := .atom 5) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1)) hdone
  refine ⟨_, by simpa [addFromMac, slam, op0, op1, macCore] using hslam, ?_⟩
  have hss := gen_slam_mem (lmb := lmb) E z α (n + 16) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1)) hdone
    (by simpa [addFromMac, slam, op0, op1, macCore] using hslam)
  have hs5 := gen_op0_mem (lmb := lmb) E z α (n + 18)
    (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h5
    (atom_ne_macCoreAt 5 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hsmpl_m := gen_cons_mem (lmb := lmb) E z α (n + 18) haccS hinner hsmpl
  have hinner_m := gen_cons_mem (lmb := lmb) E z α (n + 17) hz hm hinner
  have hsacc := gen_op0_mem (lmb := lmb) E z α (n + 17)
    (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) haccS
    (atom_ne_macCoreAt 6 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hsz := gen_op1_mem (lmb := lmb) E z α (n + 16)
    (macCore (.atom acc) (.atom 1) (.atom 1)) 0 hz
  have hsm := gen_op0_mem (lmb := lmb) E z α (n + 16)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hm
    (atom_ne_macCoreAt 31 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have wbattF : nounWalkSize (.cell (.atom 0) (.atom 5)) = 3 := by simp [nounWalkSize]
  have wsampF : nounWalkSize
      (.cell (.cell (.atom 0) (.atom 6))
        (.cell (.cell (.atom 1) (.atom 0)) (op0 31))) = 11 := by
    simp [nounWalkSize, op0]
  have wbatt : nounWalkSize addArm = 45 := nounWalkSize_addArm
  have wsamp : nounWalkSize
      (.cell (.atom acc) (.cell (.atom 0) (.atom 1))) = 5 := by
    simp [nounWalkSize]
  have w6 : nounWalkSize (.cell (.atom 0) (.atom 6)) = 3 := by simp [nounWalkSize]
  have wZ : nounWalkSize (.cell (.atom 1) (.atom 0)) = 3 := by simp [nounWalkSize]
  have w31 : nounWalkSize (op0 31) = 3 := nounWalkSize_op0 31
  have wInner : nounWalkSize
      (.cell (.cell (.atom 1) (.atom 0)) (op0 31)) = 7 := by
    simp [nounWalkSize, op0]
  have hcoreEq :
      Noun.cell addArm (.cell (.atom acc) (.cell (.atom 0) (.atom 1))) =
        addCore (.atom acc) (.atom 0) (.atom 1) := by
    simp [addCore]
  obtain ⟨hssl, hsss⟩ := hss
  obtain ⟨hs5l, hs5s⟩ := hs5
  obtain ⟨hsmpl_l, hsmpl_s⟩ := hsmpl_m
  obtain ⟨hinner_l, hinner_s⟩ := hinner_m
  obtain ⟨hsaccl, hsaccs⟩ := hsacc
  obtain ⟨hszl, hszs⟩ := hsz
  obtain ⟨hsml, hsms⟩ := hsm
  rw [hcoreEq] at hsss
  constructor
  · omega
  · rw [hs5s] at hsss
    rw [hsmpl_s] at hsss
    rw [hinner_s] at hsss
    rw [hsaccs] at hsss
    rw [hszs] at hsss
    rw [hsms] at hsss
    rw [hdone_sz] at hsss
    rw [hsss]
    simp only [wbattF, wsampF, wbatt, wsamp, w6, wZ, w31, wInner]
    omega

theorem gen_macNewSample_m0_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 14)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macNewSample =
      .ok (t, .cell (.atom acc) (.cell (.atom 1) (.cell (.atom 1) (.atom 0)))) ∧
      (genMemForestFromTree E z α lmb t).length = 34 ∧
      totalSize (genMemForestFromTree E z α lmb t) =
        356 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0)) addArm 5 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0)) (.atom acc) 6 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0)) (.atom 0) 31 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 0)) addArm 2 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 0)) (.atom 0) 14 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 0)) (.atom 0) 15 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 0)) (.atom acc) 6 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0)) (.atom 0) 14 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0)) (.atom 1) 30 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0)) (.atom 0) 31 := by
  obtain ⟨addT, hadd, hadd_len, hadd_sz⟩ :=
    gen_addFromMac_m0_mem (lmb := lmb) E z α (n + 1) acc
  have h14 := gen_op0 (K := K) (n + 10)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hinc := gen_op4 (K := K) (n + 11) h14 (lus_nat 0)
  have hn := gen_op0 (K := K) (n + 10)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hm := gen_op0 (K := K) (n + 10)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hnm := gen_cons (K := K) (n + 11) hn hm
  have hrest := gen_cons (K := K) (n + 12) hinc hnm
  have hadd' :
      genComputeSkeleton (K := K) (n + 13)
        (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0))
        (.cell (.atom 7)
          (.cell (.cell (op0 5)
            (.cell (op0 6) (.cell (op1 0) (op0 31))))
            (invokeAxis 2))) = .ok (addT, .atom acc) := by
    simpa [addFromMac, slam, op7, op0, op1, invokeAxis, macCore] using hadd
  have hcell := gen_cons (K := K) (n + 13) hadd' hrest
  obtain ⟨t, ht⟩ := gen_macNewSample_m0 (K := K) n acc
  refine ⟨t, ht, ?_⟩
  simp only [macNewSample, macCore, addFromMac, slam, op7, op0, op1, invokeAxis] at ht
  refine gen_ok_mem (lmb := lmb) E z α ht hcell ?_ ?_
  · have ho := (gen_cons_mem (lmb := lmb) E z α (n + 13) hadd' hrest hcell).1
    have hr := (gen_cons_mem (lmb := lmb) E z α (n + 12) hinc hnm hrest).1
    have hnm_m := (gen_cons_mem (lmb := lmb) E z α (n + 11) hn hm hnm).1
    have hinc_m := (gen_op4_mem (lmb := lmb) E z α (n + 11) h14 (lus_nat 0) hinc).1
    have hs14 := (gen_op0_mem (lmb := lmb) E z α (n + 10)
      (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h14
      (atom_ne_macCoreAt 14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))).1
    have hsn := (gen_op0_mem (lmb := lmb) E z α (n + 10)
      (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hn
      (atom_ne_macCoreAt 30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))).1
    have hsm := (gen_op0_mem (lmb := lmb) E z α (n + 10)
      (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hm
      (atom_ne_macCoreAt 31 (.atom acc) (.atom 0) (.atom 1) (.atom 0))).1
    omega
  · have ho := gen_cons_mem (lmb := lmb) E z α (n + 13) hadd' hrest hcell
    have hr := gen_cons_mem (lmb := lmb) E z α (n + 12) hinc hnm hrest
    have hnm_m := gen_cons_mem (lmb := lmb) E z α (n + 11) hn hm hnm
    have hinc_m := gen_op4_mem (lmb := lmb) E z α (n + 11) h14 (lus_nat 0) hinc
    have hs14 := gen_op0_mem (lmb := lmb) E z α (n + 10)
      (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h14
      (atom_ne_macCoreAt 14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
    have hsn := gen_op0_mem (lmb := lmb) E z α (n + 10)
      (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hn
      (atom_ne_macCoreAt 30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
    have hsm := gen_op0_mem (lmb := lmb) E z α (n + 10)
      (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hm
      (atom_ne_macCoreAt 31 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
    have wAdd : nounWalkSize
        (.cell (.atom 7)
          (.cell (.cell (op0 5)
            (.cell (op0 6) (.cell (op1 0) (op0 31))))
            (invokeAxis 2))) = 25 := by
      simp [nounWalkSize, op0, op1, invokeAxis]
    have wRest : nounWalkSize
        (.cell (.cell (.atom 4) (op0 14))
          (.cell (.cell (.atom 0) (.atom 30)) (op0 31))) = 13 := by
      simp [nounWalkSize, op0]
    have w4 : nounWalkSize (.cell (.atom 4) (op0 14)) = 5 := by
      simp [nounWalkSize, op0]
    have wNM : nounWalkSize
        (.cell (.cell (.atom 0) (.atom 30)) (op0 31)) = 7 := by
      simp [nounWalkSize, op0]
    have w14 : nounWalkSize (op0 14) = 3 := nounWalkSize_op0 14
    have w30 : nounWalkSize (.cell (.atom 0) (.atom 30)) = 3 := by simp [nounWalkSize]
    have w31 : nounWalkSize (op0 31) = 3 := nounWalkSize_op0 31
    obtain ⟨hol, hos⟩ := ho
    obtain ⟨hrl, hrs⟩ := hr
    obtain ⟨hnml, hnms⟩ := hnm_m
    obtain ⟨hincl, hincs⟩ := hinc_m
    obtain ⟨hs14l, hs14s⟩ := hs14
    obtain ⟨hsnl, hsns⟩ := hsn
    obtain ⟨hsml, hsms⟩ := hsm
    rw [hrs] at hos
    rw [hnms] at hos
    rw [hincs] at hos
    rw [hs14s] at hos
    rw [hsns] at hos
    rw [hsms] at hos
    rw [hadd_sz] at hos
    rw [hos]
    simp only [wAdd, wRest, w4, wNM, w14, w30, w31]
    omega

theorem gen_macNewSample_m1_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 23)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macNewSample =
      .ok (t, .cell (.atom (acc + 1)) (.cell (.atom 1) (.cell (.atom 1) (.atom 1)))) ∧
      (genMemForestFromTree E z α lmb t).length = 59 ∧
      totalSize (genMemForestFromTree E z α lmb t) =
        648 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1)) addArm 5 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1)) (.atom acc) 6 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1)) (.atom 1) 31 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) addArm 2 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom 0) 14 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom 1) 15 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) addArm 2 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom acc) 6 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom 0) 14 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom 1) 15 +
          recordTreeSize (addCore (.atom (acc + 1)) (.atom 1) (.atom 1)) (.atom 1) 14 +
          recordTreeSize (addCore (.atom (acc + 1)) (.atom 1) (.atom 1)) (.atom 1) 15 +
          recordTreeSize (addCore (.atom (acc + 1)) (.atom 1) (.atom 1))
            (.atom (acc + 1)) 6 +
          recordTreeSize
            (.cell addArm (.cell (.atom (acc + 1)) (.cell (.atom 1) (.atom 1))))
            addArm 2 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1)) (.atom 0) 14 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1)) (.atom 1) 30 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1)) (.atom 1) 31 := by
  obtain ⟨addT, hadd, hadd_len, hadd_sz⟩ :=
    gen_addFromMac_m1_mem (lmb := lmb) E z α (n + 1) acc
  have h14 := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hinc := gen_op4 (K := K) (n + 20) h14 (lus_nat 0)
  have hn := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hm := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hnm := gen_cons (K := K) (n + 20) hn hm
  have hrest := gen_cons (K := K) (n + 21) hinc hnm
  have hadd' :
      genComputeSkeleton (K := K) (n + 22)
        (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1))
        (.cell (.atom 7)
          (.cell (.cell (op0 5)
            (.cell (op0 6) (.cell (op1 0) (op0 31))))
            (invokeAxis 2))) = .ok (addT, .atom (acc + 1)) := by
    simpa [addFromMac, slam, op7, op0, op1, invokeAxis, macCore] using hadd
  have hcell := gen_cons (K := K) (n + 22) hadd' hrest
  obtain ⟨t, ht⟩ := gen_macNewSample_m1 (K := K) n acc
  refine ⟨t, ht, ?_⟩
  simp only [macNewSample, macCore, addFromMac, slam, op7, op0, op1, invokeAxis] at ht
  refine gen_ok_mem (lmb := lmb) E z α ht hcell ?_ ?_
  · have ho := (gen_cons_mem (lmb := lmb) E z α (n + 22) hadd' hrest hcell).1
    have hr := (gen_cons_mem (lmb := lmb) E z α (n + 21) hinc hnm hrest).1
    have hnm_m := (gen_cons_mem (lmb := lmb) E z α (n + 20) hn hm hnm).1
    have hinc_m := (gen_op4_mem (lmb := lmb) E z α (n + 20) h14 (lus_nat 0) hinc).1
    have hs14 := (gen_op0_mem (lmb := lmb) E z α (n + 19)
      (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h14
      (atom_ne_macCoreAt 14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))).1
    have hsn := (gen_op0_mem (lmb := lmb) E z α (n + 19)
      (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hn
      (atom_ne_macCoreAt 30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))).1
    have hsm := (gen_op0_mem (lmb := lmb) E z α (n + 19)
      (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hm
      (atom_ne_macCoreAt 31 (.atom acc) (.atom 0) (.atom 1) (.atom 1))).1
    omega
  · have ho := gen_cons_mem (lmb := lmb) E z α (n + 22) hadd' hrest hcell
    have hr := gen_cons_mem (lmb := lmb) E z α (n + 21) hinc hnm hrest
    have hnm_m := gen_cons_mem (lmb := lmb) E z α (n + 20) hn hm hnm
    have hinc_m := gen_op4_mem (lmb := lmb) E z α (n + 20) h14 (lus_nat 0) hinc
    have hs14 := gen_op0_mem (lmb := lmb) E z α (n + 19)
      (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h14
      (atom_ne_macCoreAt 14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
    have hsn := gen_op0_mem (lmb := lmb) E z α (n + 19)
      (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hn
      (atom_ne_macCoreAt 30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
    have hsm := gen_op0_mem (lmb := lmb) E z α (n + 19)
      (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hm
      (atom_ne_macCoreAt 31 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
    have wAdd : nounWalkSize
        (.cell (.atom 7)
          (.cell (.cell (op0 5)
            (.cell (op0 6) (.cell (op1 0) (op0 31))))
            (invokeAxis 2))) = 25 := by
      simp [nounWalkSize, op0, op1, invokeAxis]
    have wRest : nounWalkSize
        (.cell (.cell (.atom 4) (op0 14))
          (.cell (.cell (.atom 0) (.atom 30)) (op0 31))) = 13 := by
      simp [nounWalkSize, op0]
    have w4 : nounWalkSize (.cell (.atom 4) (op0 14)) = 5 := by
      simp [nounWalkSize, op0]
    have wNM : nounWalkSize
        (.cell (.cell (.atom 0) (.atom 30)) (op0 31)) = 7 := by
      simp [nounWalkSize, op0]
    have w14 : nounWalkSize (op0 14) = 3 := nounWalkSize_op0 14
    have w30 : nounWalkSize (.cell (.atom 0) (.atom 30)) = 3 := by simp [nounWalkSize]
    have w31 : nounWalkSize (op0 31) = 3 := nounWalkSize_op0 31
    obtain ⟨hol, hos⟩ := ho
    obtain ⟨hrl, hrs⟩ := hr
    obtain ⟨hnml, hnms⟩ := hnm_m
    obtain ⟨hincl, hincs⟩ := hinc_m
    obtain ⟨hs14l, hs14s⟩ := hs14
    obtain ⟨hsnl, hsns⟩ := hsn
    obtain ⟨hsml, hsms⟩ := hsm
    rw [hrs] at hos
    rw [hnms] at hos
    rw [hincs] at hos
    rw [hs14s] at hos
    rw [hsns] at hos
    rw [hsms] at hos
    rw [hadd_sz] at hos
    rw [hos]
    simp only [wAdd, wRest, w4, wNM, w14, w30, w31]
    omega

theorem gen_macArm_one_m0_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 22)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macArm = .ok (t, .atom acc) ∧
      (genMemForestFromTree E z α lmb t).length = 58 ∧
      totalSize (genMemForestFromTree E z α lmb t) =
        919 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0)) (.atom 0) 14 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0)) (.atom 1) 30 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0)) mmBattery 2 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0)) addArm 5 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0)) (.atom acc) 6 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0)) (.atom 0) 31 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 0)) addArm 2 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 0)) (.atom 0) 14 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 0)) (.atom 0) 15 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 0)) (.atom acc) 6 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0)) (.atom 0) 14 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0)) (.atom 1) 30 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0)) (.atom 0) 31 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 1) (.atom 1) (.atom 0)) (.atom 1) 14 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 1) (.atom 1) (.atom 0)) (.atom 1) 30 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 1) (.atom 1) (.atom 0)) (.atom acc) 6 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 1) (.atom 1) (.atom 0)) macArm 4 := by
  have h14 := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have h30 := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hcond := gen_op5 (K := K) (n + 20) h14 h30
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  obtain ⟨nsTree, hns, hns_len, hns_sz⟩ :=
    gen_macNewSample_m0_mem (lmb := lmb) E z α (n + 5) acc
  have hbatt := gen_op0 (K := K) (n + 18)
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  obtain ⟨doneTree, hdone, hdone_len, hdone_sz⟩ :=
    gen_macArm_done_mem (lmb := lmb) E z α (n + 13) (.atom acc) (.atom 1) (.atom 0)
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 16) (axis := 4)
    (bHead := .atom 0) (bTail := .atom 2) hbatt hns
    (macCoreAt_slot4 (.atom acc) (.atom 1) (.atom 1) (.atom 0)) hdone
  have hop6 := gen_op6_one (K := K) (n + 21) (c := op0 6) hcond hslam
  refine ⟨_, by simpa [macArm, slam, op0, macNewSample, macCore] using hop6, ?_⟩
  have h6 := gen_op6_one_mem (lmb := lmb) E z α (n + 21) hcond hslam
    (by simpa [macArm, slam, op0, macNewSample, macCore] using hop6)
  have hc := gen_op5_mem (lmb := lmb) E z α (n + 20) h14 h30 hcond
  have hs14 := gen_op0_mem (lmb := lmb) E z α (n + 19)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h14
    (atom_ne_macCoreAt 14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hs30 := gen_op0_mem (lmb := lmb) E z α (n + 19)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h30
    (atom_ne_macCoreAt 30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hss := gen_slam_mem (lmb := lmb) E z α (n + 16) hbatt hns
    (macCoreAt_slot4 (.atom acc) (.atom 1) (.atom 1) (.atom 0)) hdone hslam
  have hbatt_m := gen_op0_mem (lmb := lmb) E z α (n + 18)
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hbatt
    (atom_ne_macCoreAt 2 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hb : nounWalkSize (op5 (op0 14) (op0 30)) = 9 := by
    simp [nounWalkSize_op5, nounWalkSize_op0]
  have w14 : nounWalkSize (op0 14) = 3 := nounWalkSize_op0 14
  have w30 : nounWalkSize (op0 30) = 3 := nounWalkSize_op0 30
  have wd : nounWalkSize (slam (.cell (.atom 0) (.atom 2)) macNewSample 4) = 53 := by
    simp [nounWalkSize_slam, nounWalkSize, nounWalkSize_macNewSample]
  have wc' : nounWalkSize (.cell (.atom 0) (.atom 6)) = 3 := by simp [nounWalkSize]
  have wbattF : nounWalkSize (.cell (.atom 0) (.atom 2)) = 3 := by simp [nounWalkSize]
  have wsampF : nounWalkSize macNewSample = 39 := nounWalkSize_macNewSample
  have wbatt : nounWalkSize mmBattery = 115 := nounWalkSize_mmBattery
  have wsamp : nounWalkSize
      (.cell (.atom acc) (.cell (.atom 1) (.cell (.atom 1) (.atom 0)))) = 7 := by
    simp [nounWalkSize]
  have hcoreEq :
      Noun.cell mmBattery
          (.cell (.atom acc) (.cell (.atom (0 + 1)) (.cell (.atom 1) (.atom 0)))) =
        macCoreAt (.atom acc) (.atom 1) (.atom 1) (.atom 0) := by
    simp [macCoreAt]
  obtain ⟨h6l, h6s⟩ := h6
  obtain ⟨hcl, hcs⟩ := hc
  obtain ⟨hs14l, hs14s⟩ := hs14
  obtain ⟨hs30l, hs30s⟩ := hs30
  obtain ⟨hssl, hsss⟩ := hss
  obtain ⟨hbattl, hbatts⟩ := hbatt_m
  rw [hcoreEq] at hsss
  constructor
  · omega
  · rw [hs14s] at hcs
    rw [hs30s] at hcs
    rw [hns_sz] at hsss
    rw [hdone_sz] at hsss
    rw [hbatts] at hsss
    rw [hcs] at h6s
    rw [hsss] at h6s
    rw [h6s]
    simp only [hb, w14, w30, wd, wc', wbattF, wsampF, wbatt, wsamp]
    omega

theorem gen_macArm_one_m1_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 31)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macArm =
      .ok (t, .atom (acc + 1)) ∧
      (genMemForestFromTree E z α lmb t).length = 83 ∧
      totalSize (genMemForestFromTree E z α lmb t) =
        1211 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1)) (.atom 0) 14 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1)) (.atom 1) 30 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1)) mmBattery 2 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1)) addArm 5 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1)) (.atom acc) 6 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1)) (.atom 1) 31 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) addArm 2 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom 0) 14 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom 1) 15 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) addArm 2 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom acc) 6 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom 0) 14 +
          recordTreeSize (addCore (.atom acc) (.atom 0) (.atom 1)) (.atom 1) 15 +
          recordTreeSize (addCore (.atom (acc + 1)) (.atom 1) (.atom 1)) (.atom 1) 14 +
          recordTreeSize (addCore (.atom (acc + 1)) (.atom 1) (.atom 1)) (.atom 1) 15 +
          recordTreeSize (addCore (.atom (acc + 1)) (.atom 1) (.atom 1))
            (.atom (acc + 1)) 6 +
          recordTreeSize
            (.cell addArm (.cell (.atom (acc + 1)) (.cell (.atom 1) (.atom 1))))
            addArm 2 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1)) (.atom 0) 14 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1)) (.atom 1) 30 +
          recordTreeSize
            (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1)) (.atom 1) 31 +
          recordTreeSize
            (macCoreAt (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1)) (.atom 1) 14 +
          recordTreeSize
            (macCoreAt (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1)) (.atom 1) 30 +
          recordTreeSize
            (macCoreAt (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1))
            (.atom (acc + 1)) 6 +
          recordTreeSize
            (macCoreAt (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1)) macArm 4 := by
  have h14 := gen_op0 (K := K) (n + 28)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have h30 := gen_op0 (K := K) (n + 28)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hcond := gen_op5 (K := K) (n + 29) h14 h30
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  obtain ⟨nsTree, hns, hns_len, hns_sz⟩ :=
    gen_macNewSample_m1_mem (lmb := lmb) E z α (n + 5) acc
  have hbatt := gen_op0 (K := K) (n + 27)
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  obtain ⟨doneTree, hdone, hdone_len, hdone_sz⟩ :=
    gen_macArm_done_mem (lmb := lmb) E z α (n + 22) (.atom (acc + 1)) (.atom 1) (.atom 1)
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 25) (axis := 4)
    (bHead := .atom 0) (bTail := .atom 2) hbatt hns
    (macCoreAt_slot4 (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1)) hdone
  have hop6 := gen_op6_one (K := K) (n + 30) (c := op0 6) hcond hslam
  refine ⟨_, by simpa [macArm, slam, op0, macNewSample, macCore] using hop6, ?_⟩
  have h6 := gen_op6_one_mem (lmb := lmb) E z α (n + 30) hcond hslam
    (by simpa [macArm, slam, op0, macNewSample, macCore] using hop6)
  have hc := gen_op5_mem (lmb := lmb) E z α (n + 29) h14 h30 hcond
  have hs14 := gen_op0_mem (lmb := lmb) E z α (n + 28)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h14
    (atom_ne_macCoreAt 14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hs30 := gen_op0_mem (lmb := lmb) E z α (n + 28)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h30
    (atom_ne_macCoreAt 30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hss := gen_slam_mem (lmb := lmb) E z α (n + 25) hbatt hns
    (macCoreAt_slot4 (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1)) hdone hslam
  have hbatt_m := gen_op0_mem (lmb := lmb) E z α (n + 27)
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hbatt
    (atom_ne_macCoreAt 2 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hb : nounWalkSize (op5 (op0 14) (op0 30)) = 9 := by
    simp [nounWalkSize_op5, nounWalkSize_op0]
  have w14 : nounWalkSize (op0 14) = 3 := nounWalkSize_op0 14
  have w30 : nounWalkSize (op0 30) = 3 := nounWalkSize_op0 30
  have wd : nounWalkSize (slam (.cell (.atom 0) (.atom 2)) macNewSample 4) = 53 := by
    simp [nounWalkSize_slam, nounWalkSize, nounWalkSize_macNewSample]
  have wc' : nounWalkSize (.cell (.atom 0) (.atom 6)) = 3 := by simp [nounWalkSize]
  have wbattF : nounWalkSize (.cell (.atom 0) (.atom 2)) = 3 := by simp [nounWalkSize]
  have wsampF : nounWalkSize macNewSample = 39 := nounWalkSize_macNewSample
  have wbatt : nounWalkSize mmBattery = 115 := nounWalkSize_mmBattery
  have wsamp : nounWalkSize
      (.cell (.atom (acc + 1)) (.cell (.atom 1) (.cell (.atom 1) (.atom 1)))) = 7 := by
    simp [nounWalkSize]
  have hcoreEq :
      Noun.cell mmBattery
          (.cell (.atom (acc + 1))
            (.cell (.atom (0 + 1)) (.cell (.atom 1) (.atom 1)))) =
        macCoreAt (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1) := by
    simp [macCoreAt]
  obtain ⟨h6l, h6s⟩ := h6
  obtain ⟨hcl, hcs⟩ := hc
  obtain ⟨hs14l, hs14s⟩ := hs14
  obtain ⟨hs30l, hs30s⟩ := hs30
  obtain ⟨hssl, hsss⟩ := hss
  obtain ⟨hbattl, hbatts⟩ := hbatt_m
  rw [hcoreEq] at hsss
  constructor
  · omega
  · rw [hs14s] at hcs
    rw [hs30s] at hcs
    rw [hns_sz] at hsss
    rw [hdone_sz] at hsss
    rw [hbatts] at hsss
    rw [hcs] at h6s
    rw [hsss] at h6s
    rw [h6s]
    simp only [hb, w14, w30, wd, wc', wbattF, wsampF, wbatt, wsamp]
    omega

theorem gen_macArm_done_mem_atoms (E : Noun → ComputeTable.FP K) (z α : K)
    (n acc k m : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 6)
      (macCoreAt (.atom acc) (.atom k) (.atom k) (.atom m)) macArm =
      .ok (t, .atom acc) ∧
      (genMemForestFromTree E z α lmb t).length = 9 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 535 := by
  obtain ⟨t, ht, hlen, hsz⟩ :=
    gen_macArm_done_mem (lmb := lmb) E z α n (.atom acc) (.atom k) (.atom m)
  refine ⟨t, ht, hlen, ?_⟩
  rw [hsz, recordTreeSize_macCoreAt_atoms_axis14,
    recordTreeSize_macCoreAt_atoms_axis30, recordTreeSize_macCoreAt_atoms_axis6]

theorem gen_macArm_one_m0_mem_closed (E : Noun → ComputeTable.FP K) (z α : K)
    (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 22)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macArm = .ok (t, .atom acc) ∧
      (genMemForestFromTree E z α lmb t).length = 58 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 2756 := by
  obtain ⟨t, ht, hlen, hsz⟩ := gen_macArm_one_m0_mem (lmb := lmb) E z α n acc
  refine ⟨t, ht, hlen, ?_⟩
  rw [hsz]
  simp only [recordTreeSize_macCoreAt_atoms_axis14,
    recordTreeSize_macCoreAt_atoms_axis30, recordTreeSize_macCoreAt_atoms_axis2,
    recordTreeSize_macCoreAt_atoms_axis5, recordTreeSize_macCoreAt_atoms_axis6,
    recordTreeSize_macCoreAt_atoms_axis31, recordTreeSize_addCore_atoms_axis2,
    recordTreeSize_addCore_atoms_axis14, recordTreeSize_addCore_atoms_axis15,
    recordTreeSize_addCore_atoms_axis6, recordTreeSize_macCoreAt_atoms_axis4]

theorem gen_macArm_one_m1_mem_closed (E : Noun → ComputeTable.FP K) (z α : K)
    (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 31)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macArm =
      .ok (t, .atom (acc + 1)) ∧
      (genMemForestFromTree E z α lmb t).length = 83 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 3419 := by
  obtain ⟨t, ht, hlen, hsz⟩ := gen_macArm_one_m1_mem (lmb := lmb) E z α n acc
  refine ⟨t, ht, hlen, ?_⟩
  rw [hsz]
  have hcell :
      recordTreeSize
        (.cell addArm (.cell (.atom (acc + 1)) (.cell (.atom 1) (.atom 1))))
        addArm 2 = 53 :=
    recordTreeSize_addCore_atoms_axis2 (acc + 1) 1 1
  rw [hcell]
  simp only [recordTreeSize_macCoreAt_atoms_axis14,
    recordTreeSize_macCoreAt_atoms_axis30, recordTreeSize_macCoreAt_atoms_axis2,
    recordTreeSize_macCoreAt_atoms_axis5, recordTreeSize_macCoreAt_atoms_axis6,
    recordTreeSize_macCoreAt_atoms_axis31, recordTreeSize_addCore_atoms_axis2,
    recordTreeSize_addCore_atoms_axis14, recordTreeSize_addCore_atoms_axis15,
    recordTreeSize_addCore_atoms_axis6, recordTreeSize_macCoreAt_atoms_axis4]

theorem gen_mmC00_mem (E : Noun → ComputeTable.FP K) (z α : K) (n : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 56) mmSubject mmC00 =
      .ok (t, .atom 2) ∧
      (genMemForestFromTree E z α lmb t).length = 197 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 8773 := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a00 := gen_op0 (K := K) (n + 47) mmSubject_slot8
  have b00 := gen_op0 (K := K) (n + 47) mmSubject_slot12
  obtain ⟨innerArm, innerA, inner_len, inner_sz⟩ :=
    gen_macArm_one_m1_mem_closed (lmb := lmb) E z α (n + 20) 0
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 12) ha0 a00 b00 innerA
  have a01 := gen_op0 (K := K) (n + 50) mmSubject_slot9
  have b10 := gen_op0 (K := K) (n + 50) mmSubject_slot14
  obtain ⟨outerArm, outerA, outer_len, outer_sz⟩ :=
    gen_macArm_one_m1_mem_closed (lmb := lmb) E z α (n + 23) 1
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 8)) (op0 12)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 9) (mF := op0 14)
    (by simpa [invokeMac, slam, op7, quote, op1] using hinner) a01 b10 outerA
  obtain ⟨t, ht⟩ := gen_mmC00 (K := K) n
  refine ⟨t, ht, ?_⟩
  simp only [mmC00, mac2, invokeMac, slam, op7, quote, op1, op0] at ht
  have houter' :
      genComputeSkeleton (K := K) (n + 56) mmSubject
        (invokeMac
          (.cell (.atom 7)
            (.cell (.cell (quote mmBattery)
                (.cell (op1 0) (.cell (op1 0)
                  (.cell (.cell (.atom 0) (.atom 8)) (op0 12)))))
              (invokeAxis 4)))
          (.cell (.atom 0) (.atom 9)) (op0 14)) = .ok (houterT, .atom 2) := by
    simpa [invokeMac, slam, op7, quote, op1, op0] using houter
  rw [(gen_ok_unique ht houter').1]
  have hout := gen_invokeMac_mem (lmb := lmb) E z α (n + 51)
      (by simpa [invokeMac, slam, op7, quote, op1] using hinner) a01 b10 outerA
      houter'
  have hin := gen_invokeMac_mem (lmb := lmb) E z α (n + 48) ha0 a00 b00 innerA hinner
  have ha0m := gen_op1_mem (lmb := lmb) E z α (n + 49) mmSubject 0 ha0
  have a00m := gen_op0_mem (lmb := lmb) E z α (n + 47) mmSubject_slot8 a00
    (atom_ne_mmSubject 8)
  have b00m := gen_op0_mem (lmb := lmb) E z α (n + 47) mmSubject_slot12 b00
    (atom_ne_mmSubject 12)
  have a01m := gen_op0_mem (lmb := lmb) E z α (n + 50) mmSubject_slot9 a01
    (atom_ne_mmSubject 9)
  have b10m := gen_op0_mem (lmb := lmb) E z α (n + 50) mmSubject_slot14 b10
    (atom_ne_mmSubject 14)
  constructor
  · omega
  · rw [hout.2, hin.2, inner_sz, outer_sz, ha0m.2, a00m.2, b00m.2, a01m.2, b10m.2]
    simp only [nounWalkSize, nounWalkSize_mmBattery, quote, op1, op0, invokeAxis,
      recordTreeSize_macCore_atoms_axis4, recordTreeSize_mmSubject_atom8,
      recordTreeSize_mmSubject_atom12, recordTreeSize_mmSubject_atom9,
      recordTreeSize_mmSubject_atom14]

theorem gen_mmC01_mem (E : Noun → ComputeTable.FP K) (z α : K) (n : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 56) mmSubject mmC01 =
      .ok (t, .atom 1) ∧
      (genMemForestFromTree E z α lmb t).length = 172 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 8110 := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a00 := gen_op0 (K := K) (n + 47) mmSubject_slot8
  have b01 := gen_op0 (K := K) (n + 47) mmSubject_slot13
  obtain ⟨innerArm, innerA, inner_len, inner_sz⟩ :=
    gen_macArm_one_m0_mem_closed (lmb := lmb) E z α (n + 29) 0
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 13) ha0 a00 b01 innerA
  have a01 := gen_op0 (K := K) (n + 50) mmSubject_slot9
  have b11 := gen_op0 (K := K) (n + 50) mmSubject_slot15
  obtain ⟨outerArm, outerA, outer_len, outer_sz⟩ :=
    gen_macArm_one_m1_mem_closed (lmb := lmb) E z α (n + 23) 0
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 8)) (op0 13)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 9) (mF := op0 15)
    (by simpa [invokeMac, slam, op7, quote, op1] using hinner) a01 b11 outerA
  obtain ⟨t, ht⟩ := gen_mmC01 (K := K) n
  refine ⟨t, ht, ?_⟩
  simp only [mmC01, mac2, invokeMac, slam, op7, quote, op1, op0] at ht
  have houter' :
      genComputeSkeleton (K := K) (n + 56) mmSubject
        (invokeMac
          (.cell (.atom 7)
            (.cell (.cell (quote mmBattery)
                (.cell (op1 0) (.cell (op1 0)
                  (.cell (.cell (.atom 0) (.atom 8)) (op0 13)))))
              (invokeAxis 4)))
          (.cell (.atom 0) (.atom 9)) (op0 15)) = .ok (houterT, .atom 1) := by
    simpa [invokeMac, slam, op7, quote, op1, op0] using houter
  rw [(gen_ok_unique ht houter').1]
  have hout := gen_invokeMac_mem (lmb := lmb) E z α (n + 51)
      (by simpa [invokeMac, slam, op7, quote, op1] using hinner) a01 b11 outerA
      houter'
  have hin := gen_invokeMac_mem (lmb := lmb) E z α (n + 48) ha0 a00 b01 innerA hinner
  have ha0m := gen_op1_mem (lmb := lmb) E z α (n + 49) mmSubject 0 ha0
  have a00m := gen_op0_mem (lmb := lmb) E z α (n + 47) mmSubject_slot8 a00
    (atom_ne_mmSubject 8)
  have b01m := gen_op0_mem (lmb := lmb) E z α (n + 47) mmSubject_slot13 b01
    (atom_ne_mmSubject 13)
  have a01m := gen_op0_mem (lmb := lmb) E z α (n + 50) mmSubject_slot9 a01
    (atom_ne_mmSubject 9)
  have b11m := gen_op0_mem (lmb := lmb) E z α (n + 50) mmSubject_slot15 b11
    (atom_ne_mmSubject 15)
  constructor
  · omega
  · rw [hout.2, hin.2, inner_sz, outer_sz, ha0m.2, a00m.2, b01m.2, a01m.2, b11m.2]
    simp only [nounWalkSize, nounWalkSize_mmBattery, quote, op1, op0, invokeAxis,
      recordTreeSize_macCore_atoms_axis4, recordTreeSize_mmSubject_atom8,
      recordTreeSize_mmSubject_atom13, recordTreeSize_mmSubject_atom9,
      recordTreeSize_mmSubject_atom15]

theorem gen_mmC10_mem (E : Noun → ComputeTable.FP K) (z α : K) (n : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 56) mmSubject mmC10 =
      .ok (t, .atom 1) ∧
      (genMemForestFromTree E z α lmb t).length = 123 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 5889 := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a10 := gen_op0 (K := K) (n + 47) mmSubject_slot10
  have b00 := gen_op0 (K := K) (n + 47) mmSubject_slot12
  obtain ⟨innerArm, innerA, inner_len, inner_sz⟩ :=
    gen_macArm_done_mem_atoms (lmb := lmb) E z α (n + 45) 0 0 1
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 12) ha0 a10 b00 innerA
  have a11 := gen_op0 (K := K) (n + 50) mmSubject_slot11
  have b10 := gen_op0 (K := K) (n + 50) mmSubject_slot14
  obtain ⟨outerArm, outerA, outer_len, outer_sz⟩ :=
    gen_macArm_one_m1_mem_closed (lmb := lmb) E z α (n + 23) 0
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 10)) (op0 12)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 11) (mF := op0 14)
    (by simpa [invokeMac, slam, op7, quote, op1] using hinner) a11 b10 outerA
  obtain ⟨t, ht⟩ := gen_mmC10 (K := K) n
  refine ⟨t, ht, ?_⟩
  simp only [mmC10, mac2, invokeMac, slam, op7, quote, op1, op0] at ht
  have houter' :
      genComputeSkeleton (K := K) (n + 56) mmSubject
        (invokeMac
          (.cell (.atom 7)
            (.cell (.cell (quote mmBattery)
                (.cell (op1 0) (.cell (op1 0)
                  (.cell (.cell (.atom 0) (.atom 10)) (op0 12)))))
              (invokeAxis 4)))
          (.cell (.atom 0) (.atom 11)) (op0 14)) = .ok (houterT, .atom 1) := by
    simpa [invokeMac, slam, op7, quote, op1, op0] using houter
  rw [(gen_ok_unique ht houter').1]
  have hout := gen_invokeMac_mem (lmb := lmb) E z α (n + 51)
      (by simpa [invokeMac, slam, op7, quote, op1] using hinner) a11 b10 outerA
      houter'
  have hin := gen_invokeMac_mem (lmb := lmb) E z α (n + 48) ha0 a10 b00 innerA hinner
  have ha0m := gen_op1_mem (lmb := lmb) E z α (n + 49) mmSubject 0 ha0
  have a10m := gen_op0_mem (lmb := lmb) E z α (n + 47) mmSubject_slot10 a10
    (atom_ne_mmSubject 10)
  have b00m := gen_op0_mem (lmb := lmb) E z α (n + 47) mmSubject_slot12 b00
    (atom_ne_mmSubject 12)
  have a11m := gen_op0_mem (lmb := lmb) E z α (n + 50) mmSubject_slot11 a11
    (atom_ne_mmSubject 11)
  have b10m := gen_op0_mem (lmb := lmb) E z α (n + 50) mmSubject_slot14 b10
    (atom_ne_mmSubject 14)
  constructor
  · omega
  · rw [hout.2, hin.2, inner_sz, outer_sz, ha0m.2, a10m.2, b00m.2, a11m.2, b10m.2]
    simp only [nounWalkSize, nounWalkSize_mmBattery, quote, op1, op0, invokeAxis,
      recordTreeSize_macCore_atoms_axis4, recordTreeSize_mmSubject_atom10,
      recordTreeSize_mmSubject_atom12, recordTreeSize_mmSubject_atom11,
      recordTreeSize_mmSubject_atom14]

theorem gen_mmC11_mem (E : Noun → ComputeTable.FP K) (z α : K) (n : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 56) mmSubject mmC11 =
      .ok (t, .atom 1) ∧
      (genMemForestFromTree E z α lmb t).length = 123 ∧
      totalSize (genMemForestFromTree E z α lmb t) = 5889 := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a10 := gen_op0 (K := K) (n + 47) mmSubject_slot10
  have b01 := gen_op0 (K := K) (n + 47) mmSubject_slot13
  obtain ⟨innerArm, innerA, inner_len, inner_sz⟩ :=
    gen_macArm_done_mem_atoms (lmb := lmb) E z α (n + 45) 0 0 0
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 13) ha0 a10 b01 innerA
  have a11 := gen_op0 (K := K) (n + 50) mmSubject_slot11
  have b11 := gen_op0 (K := K) (n + 50) mmSubject_slot15
  obtain ⟨outerArm, outerA, outer_len, outer_sz⟩ :=
    gen_macArm_one_m1_mem_closed (lmb := lmb) E z α (n + 23) 0
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 10)) (op0 13)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 11) (mF := op0 15)
    (by simpa [invokeMac, slam, op7, quote, op1] using hinner) a11 b11 outerA
  obtain ⟨t, ht⟩ := gen_mmC11 (K := K) n
  refine ⟨t, ht, ?_⟩
  simp only [mmC11, mac2, invokeMac, slam, op7, quote, op1, op0] at ht
  have houter' :
      genComputeSkeleton (K := K) (n + 56) mmSubject
        (invokeMac
          (.cell (.atom 7)
            (.cell (.cell (quote mmBattery)
                (.cell (op1 0) (.cell (op1 0)
                  (.cell (.cell (.atom 0) (.atom 10)) (op0 13)))))
              (invokeAxis 4)))
          (.cell (.atom 0) (.atom 11)) (op0 15)) = .ok (houterT, .atom 1) := by
    simpa [invokeMac, slam, op7, quote, op1, op0] using houter
  rw [(gen_ok_unique ht houter').1]
  have hout := gen_invokeMac_mem (lmb := lmb) E z α (n + 51)
      (by simpa [invokeMac, slam, op7, quote, op1] using hinner) a11 b11 outerA
      houter'
  have hin := gen_invokeMac_mem (lmb := lmb) E z α (n + 48) ha0 a10 b01 innerA hinner
  have ha0m := gen_op1_mem (lmb := lmb) E z α (n + 49) mmSubject 0 ha0
  have a10m := gen_op0_mem (lmb := lmb) E z α (n + 47) mmSubject_slot10 a10
    (atom_ne_mmSubject 10)
  have b01m := gen_op0_mem (lmb := lmb) E z α (n + 47) mmSubject_slot13 b01
    (atom_ne_mmSubject 13)
  have a11m := gen_op0_mem (lmb := lmb) E z α (n + 50) mmSubject_slot11 a11
    (atom_ne_mmSubject 11)
  have b11m := gen_op0_mem (lmb := lmb) E z α (n + 50) mmSubject_slot15 b11
    (atom_ne_mmSubject 15)
  constructor
  · omega
  · rw [hout.2, hin.2, inner_sz, outer_sz, ha0m.2, a10m.2, b01m.2, a11m.2, b11m.2]
    simp only [nounWalkSize, nounWalkSize_mmBattery, quote, op1, op0, invokeAxis,
      recordTreeSize_macCore_atoms_axis4, recordTreeSize_mmSubject_atom10,
      recordTreeSize_mmSubject_atom13, recordTreeSize_mmSubject_atom11,
      recordTreeSize_mmSubject_atom15]

theorem mmMemForest_unassigned_length (E : Noun → ComputeTable.FP K) (z α : K) :
    (genMemForestFromTree E z α lmb (mmTree (K := K))).length = 618 := by
  obtain ⟨t00, h00, s00, _⟩ := gen_mmC00_mem (lmb := lmb) E z α 6
  obtain ⟨t01, h01, s01, _⟩ := gen_mmC01_mem (lmb := lmb) E z α 6
  obtain ⟨t10, h10, s10, _⟩ := gen_mmC10_mem (lmb := lmb) E z α 6
  obtain ⟨t11, h11, s11, _⟩ := gen_mmC11_mem (lmb := lmb) E z α 6
  have h00c :
      genComputeSkeleton (K := K) 62 mmSubject
        (.cell (.atom 7)
          (.cell (.cell (quote mmBattery)
            (.cell (invokeMac (op1 0) (op0 8) (op0 12))
              (.cell (op1 0) (.cell (op0 9) (op0 14)))))
            (invokeAxis 4))) = .ok (t00, .atom 2) := by
    simpa [mmC00, mac2, invokeMac, slam, op7, quote, op1] using h00
  have h01c :
      genComputeSkeleton (K := K) 62 mmSubject
        (.cell (.atom 7)
          (.cell (.cell (quote mmBattery)
            (.cell (invokeMac (op1 0) (op0 8) (op0 13))
              (.cell (op1 0) (.cell (op0 9) (op0 15)))))
            (invokeAxis 4))) = .ok (t01, .atom 1) := by
    simpa [mmC01, mac2, invokeMac, slam, op7, quote, op1] using h01
  have h10c :
      genComputeSkeleton (K := K) 62 mmSubject
        (.cell (.atom 7)
          (.cell (.cell (quote mmBattery)
            (.cell (invokeMac (op1 0) (op0 10) (op0 12))
              (.cell (op1 0) (.cell (op0 11) (op0 14)))))
            (invokeAxis 4))) = .ok (t10, .atom 1) := by
    simpa [mmC10, mac2, invokeMac, slam, op7, quote, op1] using h10
  have h11c :
      genComputeSkeleton (K := K) 62 mmSubject
        (.cell (.atom 7)
          (.cell (.cell (quote mmBattery)
            (.cell (invokeMac (op1 0) (op0 10) (op0 13))
              (.cell (op1 0) (.cell (op0 11) (op0 15)))))
            (invokeAxis 4))) = .ok (t11, .atom 1) := by
    simpa [mmC11, mac2, invokeMac, slam, op7, quote, op1] using h11
  have hL := gen_cons (K := K) 62 h00c h01c
  have hR := gen_cons (K := K) 62 h10c h11c
  have hop := gen_cons (K := K) 63 hL hR
  have ht := mmTree_gen (K := K)
  simp only [mmFormula, mmC00, mmC01, mmC10, mmC11, mac2, invokeMac, slam, op7,
    quote, op1, op0] at ht
  rw [(gen_ok_unique ht hop).1]
  have hsL := (gen_cons_mem (lmb := lmb) E z α 62 h00c h01c hL).1
  have hsR := (gen_cons_mem (lmb := lmb) E z α 62 h10c h11c hR).1
  have hsO := (gen_cons_mem (lmb := lmb) E z α 63 hL hR hop).1
  omega

theorem mmMemForest_unassigned_totalSize (E : Noun → ComputeTable.FP K) (z α : K) :
    totalSize (genMemForestFromTree E z α lmb (mmTree (K := K))) = 30936 := by
  obtain ⟨t00, h00, _, sz00⟩ := gen_mmC00_mem (lmb := lmb) E z α 6
  obtain ⟨t01, h01, _, sz01⟩ := gen_mmC01_mem (lmb := lmb) E z α 6
  obtain ⟨t10, h10, _, sz10⟩ := gen_mmC10_mem (lmb := lmb) E z α 6
  obtain ⟨t11, h11, _, sz11⟩ := gen_mmC11_mem (lmb := lmb) E z α 6
  have h00c :
      genComputeSkeleton (K := K) 62 mmSubject
        (.cell (.atom 7)
          (.cell (.cell (quote mmBattery)
            (.cell (invokeMac (op1 0) (op0 8) (op0 12))
              (.cell (op1 0) (.cell (op0 9) (op0 14)))))
            (invokeAxis 4))) = .ok (t00, .atom 2) := by
    simpa [mmC00, mac2, invokeMac, slam, op7, quote, op1] using h00
  have h01c :
      genComputeSkeleton (K := K) 62 mmSubject
        (.cell (.atom 7)
          (.cell (.cell (quote mmBattery)
            (.cell (invokeMac (op1 0) (op0 8) (op0 13))
              (.cell (op1 0) (.cell (op0 9) (op0 15)))))
            (invokeAxis 4))) = .ok (t01, .atom 1) := by
    simpa [mmC01, mac2, invokeMac, slam, op7, quote, op1] using h01
  have h10c :
      genComputeSkeleton (K := K) 62 mmSubject
        (.cell (.atom 7)
          (.cell (.cell (quote mmBattery)
            (.cell (invokeMac (op1 0) (op0 10) (op0 12))
              (.cell (op1 0) (.cell (op0 11) (op0 14)))))
            (invokeAxis 4))) = .ok (t10, .atom 1) := by
    simpa [mmC10, mac2, invokeMac, slam, op7, quote, op1] using h10
  have h11c :
      genComputeSkeleton (K := K) 62 mmSubject
        (.cell (.atom 7)
          (.cell (.cell (quote mmBattery)
            (.cell (invokeMac (op1 0) (op0 10) (op0 13))
              (.cell (op1 0) (.cell (op0 11) (op0 15)))))
            (invokeAxis 4))) = .ok (t11, .atom 1) := by
    simpa [mmC11, mac2, invokeMac, slam, op7, quote, op1] using h11
  have hL := gen_cons (K := K) 62 h00c h01c
  have hR := gen_cons (K := K) 62 h10c h11c
  have hop := gen_cons (K := K) 63 hL hR
  have ht := mmTree_gen (K := K)
  simp only [mmFormula, mmC00, mmC01, mmC10, mmC11, mac2, invokeMac, slam, op7,
    quote, op1, op0] at ht
  rw [(gen_ok_unique ht hop).1]
  have hsL := gen_cons_mem (lmb := lmb) E z α 62 h00c h01c hL
  have hsR := gen_cons_mem (lmb := lmb) E z α 62 h10c h11c hR
  have hsO := gen_cons_mem (lmb := lmb) E z α 63 hL hR hop
  have w00 : nounWalkSize
      (.cell (.atom 7)
        (.cell (.cell (quote mmBattery)
          (.cell (invokeMac (op1 0) (op0 8) (op0 12))
            (.cell (op1 0) (.cell (op0 9) (op0 14)))))
          (invokeAxis 4))) = 283 := by
    simpa [mmC00, mac2, invokeMac, slam, op7, quote, op1] using nounWalkSize_mmC00
  have w01 : nounWalkSize
      (.cell (.atom 7)
        (.cell (.cell (quote mmBattery)
          (.cell (invokeMac (op1 0) (op0 8) (op0 13))
            (.cell (op1 0) (.cell (op0 9) (op0 15)))))
          (invokeAxis 4))) = 283 := by
    simpa [mmC01, mac2, invokeMac, slam, op7, quote, op1] using nounWalkSize_mmC01
  have w10 : nounWalkSize
      (.cell (.atom 7)
        (.cell (.cell (quote mmBattery)
          (.cell (invokeMac (op1 0) (op0 10) (op0 12))
            (.cell (op1 0) (.cell (op0 11) (op0 14)))))
          (invokeAxis 4))) = 283 := by
    simpa [mmC10, mac2, invokeMac, slam, op7, quote, op1] using nounWalkSize_mmC10
  have w11 : nounWalkSize
      (.cell (.atom 7)
        (.cell (.cell (quote mmBattery)
          (.cell (invokeMac (op1 0) (op0 10) (op0 13))
            (.cell (op1 0) (.cell (op0 11) (op0 15)))))
          (invokeAxis 4))) = 283 := by
    simpa [mmC11, mac2, invokeMac, slam, op7, quote, op1] using nounWalkSize_mmC11
  rw [hsO.2, hsL.2, hsR.2, sz00, sz01, sz10, sz11]
  rw [w00, w01, w10, w11]
  simp only [nounWalkSize_cell, w00, w01, w10, w11]

/-! ## Stamp-independent row forests and `bfsAssign` transport -/

def descentContForestSize (current : Noun) (remaining : ℕ) (contSize : ℕ) : ℕ :=
  if remaining < 2 then contSize
  else if axisTopBit remaining then
    1 + nounWalkSize (formulaHead current)
      + descentContForestSize (formulaTail current) (axisRest remaining) contSize
  else
    1 + descentContForestSize (formulaHead current) (axisRest remaining) contSize
      + nounWalkSize (formulaTail current)
termination_by remaining
decreasing_by
  all_goals
    apply axisRest_lt
    omega

theorem descentContForestSize_of_lt2 (current : Noun) {remaining : ℕ} (contSize : ℕ)
    (h : remaining < 2) :
    descentContForestSize current remaining contSize = contSize := by
  conv => lhs; unfold descentContForestSize
  rw [if_pos h]

theorem descentContForestSize_of_tail (current : Noun) {remaining : ℕ} (contSize : ℕ)
    (h2 : ¬ remaining < 2) (ht : axisTopBit remaining = true) :
    descentContForestSize current remaining contSize =
      1 + nounWalkSize (formulaHead current)
        + descentContForestSize (formulaTail current) (axisRest remaining) contSize := by
  conv => lhs; unfold descentContForestSize
  rw [if_neg h2, if_pos ht]

theorem descentContForestSize_of_head (current : Noun) {remaining : ℕ} (contSize : ℕ)
    (h2 : ¬ remaining < 2) (hh : axisTopBit remaining = false) :
    descentContForestSize current remaining contSize =
      1 + descentContForestSize (formulaHead current) (axisRest remaining) contSize
        + nounWalkSize (formulaTail current) := by
  conv => lhs; unfold descentContForestSize
  rw [if_neg h2, if_neg (by simp [hh])]

theorem genAnnotatedDescentCont_totalSize (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) (currentNoun : Noun) (remainingAxis : ℕ) :
    totalSize (genAnnotatedDescentCont E z lmb cont contCell contState
        currentNoun remainingAxis).1 =
      descentContForestSize currentNoun remainingAxis (totalSize cont) := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    unfold genAnnotatedDescentCont
    split
    · rename_i hlt
      rw [descentContForestSize_of_lt2 _ _ hlt]
    · rename_i hge
      split
      · rename_i ht
        rw [descentContForestSize_of_tail _ _ hge ht]
        have hih := ih (axisRest n) (axisRest_lt (by omega)) (formulaTail currentNoun)
        simp [totalSize, NTree.size, genAnnotatedNounWalk_size] at hih ⊢
        rw [hih]
        omega
      · rename_i hh
        have hh' : axisTopBit n = false := Bool.eq_false_iff.mpr hh
        rw [descentContForestSize_of_head _ _ hge hh']
        have hih := ih (axisRest n) (axisRest_lt (by omega)) (formulaHead currentNoun)
        simp [totalSize, NTree.size, genAnnotatedNounWalk_size] at hih ⊢
        rw [hih]
        omega

theorem genAnnotatedChainedInner_nil_totalSize (E : Noun → ComputeTable.FP K)
    (z α : K) (prev : MemRecordReq) :
    totalSize (genAnnotatedChainedInner E z α lmb prev []).1 =
      1 + nounWalkSize prev.child := by
  rw [genAnnotatedChainedInner_nil]
  simp [totalSize, genAnnotatedVerify_size]

theorem genAnnotatedChainedInner_cons_totalSize (E : Noun → ComputeTable.FP K)
    (z α : K) (prev r : MemRecordReq) (more : List MemRecordReq) :
    totalSize (genAnnotatedChainedInner E z α lmb prev (r :: more)).1 =
      2 + descentContForestSize r.root r.axis
        (totalSize (genAnnotatedChainedInner E z α lmb r more).1) := by
  conv => lhs; unfold genAnnotatedChainedInner
  simp only [totalSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    NTree.size, add_zero]
  change 1 + (1 + totalSize (genAnnotatedDescentCont E z lmb
      (genAnnotatedChainedInner E z α lmb r more).1
      (genAnnotatedChainedInner E z α lmb r more).2
      (chainedInnerRootState more) r.root r.axis).1) =
    2 + descentContForestSize r.root r.axis
      (totalSize (genAnnotatedChainedInner E z α lmb r more).1)
  rw [genAnnotatedDescentCont_totalSize]
  omega

theorem genAnnotatedChainedTree_two_size (E : Noun → ComputeTable.FP K)
    (z α : K) (r1 r2 : MemRecordReq) (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z α lmb [r1, r2] = some t) :
    t.size = 1 + descentContForestSize r1.root r1.axis
      (totalSize (genAnnotatedChainedInner E z α lmb r1 [r2]).1) := by
  have hopen :
      genAnnotatedChainedTree E z α lmb [r1, r2] =
        some
          (.node
            (gMemRow9 (memReadSkelAx r1.root r1.child r1.axis) r1.recordExp z
              (annotatedReadPub E r1.root r1.child r1.axis (α ^ r1.recordExp)
                (genAnnotatedDescentCont E z lmb
                    (genAnnotatedChainedInner E z α lmb r1 [r2]).1
                    (genAnnotatedChainedInner E z α lmb r1 [r2]).2
                    (chainedInnerRootState [r2]) r1.root r1.axis).2
                0 0 lmb))
            (genAnnotatedDescentCont E z lmb
              (genAnnotatedChainedInner E z α lmb r1 [r2]).1
              (genAnnotatedChainedInner E z α lmb r1 [r2]).2
              (chainedInnerRootState [r2]) r1.root r1.axis).1) :=
    rfl
  rw [hopen] at ht
  injection ht with ht
  subst t
  simp only [NTree.size]
  change 1 + totalSize (genAnnotatedDescentCont E z lmb
      (genAnnotatedChainedInner E z α lmb r1 [r2]).1
      (genAnnotatedChainedInner E z α lmb r1 [r2]).2
      (chainedInnerRootState [r2]) r1.root r1.axis).1 =
    1 + descentContForestSize r1.root r1.axis
      (totalSize (genAnnotatedChainedInner E z α lmb r1 [r2]).1)
  rw [genAnnotatedDescentCont_totalSize]

theorem genAnnotatedChainedInner_one_totalSize (E : Noun → ComputeTable.FP K)
    (z α : K) (prev r : MemRecordReq) :
    totalSize (genAnnotatedChainedInner E z α lmb prev [r]).1 =
      2 + descentContForestSize r.root r.axis (1 + nounWalkSize r.child) := by
  rw [genAnnotatedChainedInner_cons_totalSize, genAnnotatedChainedInner_nil_totalSize]

theorem extractNodeReqsAux_shape (stamp) (i : ℕ) :
    ∀ rs : List (ServiceReq K),
      (extractNodeReqsAux stamp i rs).map (fun r => (r.root, r.child, r.axis)) =
        rs.map (fun r => (r.root, r.child, r.axis))
  | [] => rfl
  | _ :: rs => by
      simp [extractNodeReqsAux]
      exact extractNodeReqsAux_shape stamp (i + 1) rs

theorem extractNodeReqsAux_len (stamp) (i : ℕ) :
    ∀ rs : List (ServiceReq K),
      (extractNodeReqsAux stamp i rs).length = rs.length
  | [] => rfl
  | _ :: rs => by
      simp [extractNodeReqsAux, extractNodeReqsAux_len stamp (i + 1) rs]

theorem genRowMemForest_two_eq (E : Noun → ComputeTable.FP K) (z α : K)
    (r1 r2 : MemRecordReq) :
    genRowMemForest E z α lmb [r1, r2] =
      if r1.child = r2.root then
        match genAnnotatedChainedTree E z α lmb [r1, r2] with
        | some t => [t]
        | none =>
          [genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
           genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]
      else
        [genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
         genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp] :=
  rfl

theorem genRowMemForest_three_eq (E : Noun → ComputeTable.FP K) (z α : K)
    (r1 r2 r3 : MemRecordReq) :
    genRowMemForest E z α lmb [r1, r2, r3] =
      genRowMemForest E z α lmb [r1, r2] ++
        [genAnnotatedRecordTree E z α lmb r3.root r3.child r3.axis r3.recordExp] :=
  rfl

theorem genRowMemForest_two_chain_size (E : Noun → ComputeTable.FP K)
    (z α : K) (r1 r2 : MemRecordReq) (hc : r1.child = r2.root) :
    totalSize (genRowMemForest E z α lmb [r1, r2]) =
      1 + descentContForestSize r1.root r1.axis
        (2 + descentContForestSize r2.root r2.axis (1 + nounWalkSize r2.child)) ∧
    (genRowMemForest E z α lmb [r1, r2]).length = 1 := by
  rw [genRowMemForest_two_eq, if_pos hc]
  cases hch : genAnnotatedChainedTree E z α lmb [r1, r2] with
  | none =>
      have hsome :
          genAnnotatedChainedTree E z α lmb [r1, r2] =
            some
              (.node
                (gMemRow9 (memReadSkelAx r1.root r1.child r1.axis) r1.recordExp z
                  (annotatedReadPub E r1.root r1.child r1.axis (α ^ r1.recordExp)
                    (genAnnotatedDescentCont E z lmb
                        (genAnnotatedChainedInner E z α lmb r1 [r2]).1
                        (genAnnotatedChainedInner E z α lmb r1 [r2]).2
                        (chainedInnerRootState [r2]) r1.root r1.axis).2
                    0 0 lmb))
                (genAnnotatedDescentCont E z lmb
                  (genAnnotatedChainedInner E z α lmb r1 [r2]).1
                  (genAnnotatedChainedInner E z α lmb r1 [r2]).2
                  (chainedInnerRootState [r2]) r1.root r1.axis).1) :=
        rfl
      simp [hsome] at hch
  | some t =>
      simp [totalSize]
      rw [genAnnotatedChainedTree_two_size E z α r1 r2 t hch,
        genAnnotatedChainedInner_one_totalSize]

theorem genRowMemForest_two_indep_size (E : Noun → ComputeTable.FP K)
    (z α : K) (r1 r2 : MemRecordReq) (hne : r1.child ≠ r2.root) :
    totalSize (genRowMemForest E z α lmb [r1, r2]) =
      recordTreeSize r1.root r1.child r1.axis +
        recordTreeSize r2.root r2.child r2.axis ∧
    (genRowMemForest E z α lmb [r1, r2]).length = 2 := by
  rw [genRowMemForest_two_eq, if_neg hne]
  simp [totalSize, genAnnotatedRecordTree_size]

theorem genRowMemForest_two_congr (E : Noun → ComputeTable.FP K) (z α : K)
    (r1 r2 s1 s2 : MemRecordReq)
    (h1 : r1.root = s1.root ∧ r1.child = s1.child ∧ r1.axis = s1.axis)
    (h2 : r2.root = s2.root ∧ r2.child = s2.child ∧ r2.axis = s2.axis) :
    totalSize (genRowMemForest E z α lmb [r1, r2]) =
      totalSize (genRowMemForest E z α lmb [s1, s2]) ∧
    (genRowMemForest E z α lmb [r1, r2]).length =
      (genRowMemForest E z α lmb [s1, s2]).length := by
  have hiff : r1.child = r2.root ↔ s1.child = s2.root := by
    rw [h1.2.1, h2.1]
  by_cases hc : r1.child = r2.root
  · have hc' : s1.child = s2.root := hiff.mp hc
    have hL := genRowMemForest_two_chain_size (lmb := lmb) E z α r1 r2 hc
    have hR := genRowMemForest_two_chain_size (lmb := lmb) E z α s1 s2 hc'
    rw [hL.1, hR.1, hL.2, hR.2]
    simp [h1, h2]
  · have hc' : s1.child ≠ s2.root := fun h => hc (hiff.mpr h)
    have hL := genRowMemForest_two_indep_size (lmb := lmb) E z α r1 r2 hc
    have hR := genRowMemForest_two_indep_size (lmb := lmb) E z α s1 s2 hc'
    rw [hL.1, hR.1, hL.2, hR.2]
    simp [h1, h2]

theorem genRowMemForest_extract_stamp (E : Noun → ComputeTable.FP K) (z α : K)
    (s1 s2) (i : ℕ) :
    ∀ rs : List (ServiceReq K),
      totalSize (genRowMemForest E z α lmb (extractNodeReqsAux s1 i rs)) =
        totalSize (genRowMemForest E z α lmb (extractNodeReqsAux s2 i rs)) ∧
      (genRowMemForest E z α lmb (extractNodeReqsAux s1 i rs)).length =
        (genRowMemForest E z α lmb (extractNodeReqsAux s2 i rs)).length
  | [] => by simp [extractNodeReqsAux, genRowMemForest, totalSize]
  | [r] => by
      simp [extractNodeReqsAux, genRowMemForest, totalSize, genAnnotatedRecordTree_size]
  | [r1, r2] => by
      simp only [extractNodeReqsAux_cons2]
      exact genRowMemForest_two_congr E z α _ _ _ _
        ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  | [r1, r2, r3] => by
      simp only [extractNodeReqsAux_cons3]
      rw [genRowMemForest_three_eq, genRowMemForest_three_eq]
      have htwo := genRowMemForest_two_congr (lmb := lmb) E z α
        ⟨r1.root, r1.child, r1.axis, getRecordExp s1 i⟩
        ⟨r2.root, r2.child, r2.axis, getRecordExp s1 (i + 1)⟩
        ⟨r1.root, r1.child, r1.axis, getRecordExp s2 i⟩
        ⟨r2.root, r2.child, r2.axis, getRecordExp s2 (i + 1)⟩
        ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
      constructor
      · rw [totalSize_append, totalSize_append, htwo.1]
        simp [totalSize, genAnnotatedRecordTree_size]
      · rw [List.length_append, List.length_append, htwo.2]
        simp
  | r1 :: r2 :: r3 :: r4 :: rest => by
      have hmap (s) :
          genRowMemForest E z α lmb (extractNodeReqsAux s i (r1 :: r2 :: r3 :: r4 :: rest)) =
            (extractNodeReqsAux s i (r1 :: r2 :: r3 :: r4 :: rest)).map
              (fun r => genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) :=
        rfl
      have hrec :
          ∀ rs1 rs2 : List MemRecordReq,
            rs1.map (fun r => (r.root, r.child, r.axis)) =
              rs2.map (fun r => (r.root, r.child, r.axis)) →
            rs1.map (fun r => recordTreeSize r.root r.child r.axis) =
              rs2.map (fun r => recordTreeSize r.root r.child r.axis) := by
        intro rs1
        induction rs1 with
        | nil =>
            intro rs2 h
            cases rs2 <;> simp at h ⊢
        | cons r1 rs1 ih =>
            intro rs2 h
            cases rs2 with
            | nil => simp at h
            | cons r2 rs2 =>
                simp at h
                simp [h.1, ih rs2 h.2]
      constructor
      · rw [hmap s1, hmap s2]
        unfold totalSize
        simp only [List.map_map]
        have hfun1 :
            ((extractNodeReqsAux s1 i (r1 :: r2 :: r3 :: r4 :: rest)).map
              (NTree.size ∘ fun r =>
                genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp)) =
              (extractNodeReqsAux s1 i (r1 :: r2 :: r3 :: r4 :: rest)).map
                (fun r => recordTreeSize r.root r.child r.axis) := by
          apply List.map_congr_left
          intro r _
          exact genAnnotatedRecordTree_size E z α r.root r.child r.axis r.recordExp
        have hfun2 :
            ((extractNodeReqsAux s2 i (r1 :: r2 :: r3 :: r4 :: rest)).map
              (NTree.size ∘ fun r =>
                genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp)) =
              (extractNodeReqsAux s2 i (r1 :: r2 :: r3 :: r4 :: rest)).map
                (fun r => recordTreeSize r.root r.child r.axis) := by
          apply List.map_congr_left
          intro r _
          exact genAnnotatedRecordTree_size E z α r.root r.child r.axis r.recordExp
        rw [hfun1, hfun2]
        exact congrArg List.sum (hrec _ _ (by
          rw [extractNodeReqsAux_shape s1 i, extractNodeReqsAux_shape s2 i]))
      · rw [hmap s1, hmap s2, List.length_map, List.length_map,
          extractNodeReqsAux_len, extractNodeReqsAux_len]

def rowForestSize (E : Noun → ComputeTable.FP K) (z α : K)
    (g : GenComputeRow K) : ℕ :=
  totalSize (genRowMemForest E z α lmb (extractNodeReqs g))

def rowForestLen (E : Noun → ComputeTable.FP K) (z α : K)
    (g : GenComputeRow K) : ℕ :=
  (genRowMemForest E z α lmb (extractNodeReqs g)).length

theorem rowForest_stamp (E : Noun → ComputeTable.FP K) (z α : K)
    (g : GenComputeRow K) (st) :
    rowForestSize (lmb := lmb) E z α { g with stamp := st } = rowForestSize (lmb := lmb) E z α g ∧
      rowForestLen (lmb := lmb) E z α { g with stamp := st } = rowForestLen (lmb := lmb) E z α g := by
  simp [rowForestSize, rowForestLen, extractNodeReqs]
  exact genRowMemForest_extract_stamp E z α st g.stamp 0 g.requests

theorem rowForestSize_bfsLabelAt (E : Noun → ComputeTable.FP K) (z α : K)
    (t : NTree (GenComputeRow K)) (i : ℕ)
    (hi : i - 1 < (bfsRows t).length) :
    rowForestSize (lmb := lmb) E z α (bfsLabelAt t i) =
      rowForestSize (lmb := lmb) E z α (bfsRows t)[i - 1] ∧
    rowForestLen (lmb := lmb) E z α (bfsLabelAt t i) =
      rowForestLen (lmb := lmb) E z α (bfsRows t)[i - 1] := by
  rw [bfsLabelAt_eq t i hi]
  exact rowForest_stamp E z α (bfsRows t)[i - 1] _

theorem genMemForestFromList_totalSize_sum (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ cs, totalSize (genMemForestFromList E z α lmb cs) =
      (cs.map (fun t => totalSize (genMemForestFromTree E z α lmb t))).sum
  | [] => rfl
  | c :: cs => by
      rw [genMemForestFromList_cons, totalSize_append]
      simp [genMemForestFromList_totalSize_sum E z α cs]

theorem genMemForestFromList_length_sum (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ cs, (genMemForestFromList E z α lmb cs).length =
      (cs.map (fun t => (genMemForestFromTree E z α lmb t).length)).sum
  | [] => rfl
  | c :: cs => by
      rw [genMemForestFromList_cons, List.length_append]
      simp [genMemForestFromList_length_sum E z α cs]

def treeMemSize (E : Noun → ComputeTable.FP K) (z α : K) :
    NTree (GenComputeRow K) → ℕ
  | .node g cs =>
      rowForestSize (lmb := lmb) E z α g + (cs.map (treeMemSize E z α)).sum

def treeMemLen (E : Noun → ComputeTable.FP K) (z α : K) :
    NTree (GenComputeRow K) → ℕ
  | .node g cs =>
      rowForestLen (lmb := lmb) E z α g + (cs.map (treeMemLen E z α)).sum

theorem treeMemSize_eq (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ t, treeMemSize (lmb := lmb) E z α t = totalSize (genMemForestFromTree E z α lmb t) := by
  intro t
  induction ht : t.size using Nat.strongRecOn generalizing t with
  | _ n ih =>
    cases t with
    | node g cs =>
      unfold treeMemSize
      rw [genMemForestFromTree_node, totalSize_append, genMemForestFromList_totalSize_sum]
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro c hc
      have hin : c.size ∈ cs.map NTree.size := List.mem_map.mpr ⟨c, hc, rfl⟩
      have hle : c.size ≤ (cs.map NTree.size).sum := List.le_sum_of_mem hin
      exact ih c.size (by simp [NTree.size] at ht; omega) c rfl

theorem treeMemLen_eq (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ t, treeMemLen (lmb := lmb) E z α t = (genMemForestFromTree E z α lmb t).length := by
  intro t
  induction ht : t.size using Nat.strongRecOn generalizing t with
  | _ n ih =>
    cases t with
    | node g cs =>
      unfold treeMemLen
      rw [genMemForestFromTree_node, List.length_append, genMemForestFromList_length_sum]
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro c hc
      have hin : c.size ∈ cs.map NTree.size := List.mem_map.mpr ⟨c, hc, rfl⟩
      have hle : c.size ≤ (cs.map NTree.size).sum := List.le_sum_of_mem hin
      exact ih c.size (by simp [NTree.size] at ht; omega) c rfl

theorem bfsForest_treeMemSize_sum (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ n ts, totalSize ts ≤ n →
      ((bfsForest ts).map (fun t => rowForestSize (lmb := lmb) E z α t.label)).sum =
        (ts.map (treeMemSize (lmb := lmb) E z α)).sum := by
  intro n
  induction n with
  | zero =>
      intro ts hts
      have : ts = [] := by
        cases ts with
        | nil => rfl
        | cons t rest =>
            have : 1 ≤ t.size := by cases t; simp [NTree.size]
            rw [totalSize_cons] at hts; omega
      subst ts
      simp [bfsForest_nil]
  | succ m ih =>
      intro ts hts
      by_cases hne : ts = []
      · subst hne; simp [bfsForest_nil]
      · rw [bfsForest_cons_eq ts hne, List.map_append, List.sum_append]
        have hch : totalSize (ts.flatMap NTree.children) ≤ m := by
          have := totalSize_flatMap_children (LT := GenComputeRow K) ts
          have hlen : 1 ≤ ts.length := List.length_pos_iff.mpr hne
          omega
        rw [ih _ hch]
        match ts with
        | [] => exact absurd rfl hne
        | t :: rest =>
            cases t with
            | node g cs =>
                simp [treeMemSize, List.flatMap_cons, List.map_append, List.sum_append]
                have hrest :
                    ((rest.map (fun t => rowForestSize (lmb := lmb) E z α t.label)).sum +
                      ((rest.flatMap NTree.children).map (treeMemSize (lmb := lmb) E z α)).sum) =
                      (rest.map (treeMemSize (lmb := lmb) E z α)).sum := by
                  by_cases hr : rest = []
                  · subst hr; simp
                  · have hsz : totalSize rest ≤ m := by
                      have : 1 ≤ NTree.size (.node g cs) := by simp [NTree.size]
                      rw [totalSize_cons] at hts; omega
                    have hch' : totalSize (rest.flatMap NTree.children) ≤ m := by
                      have := totalSize_flatMap_children (LT := GenComputeRow K) rest
                      omega
                    have hbfs := ih rest hsz
                    rw [bfsForest_cons_eq rest hr, List.map_append, List.sum_append] at hbfs
                    rw [ih _ hch'] at hbfs
                    exact hbfs
                omega

theorem bfsForest_treeMemLen_sum (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ n ts, totalSize ts ≤ n →
      ((bfsForest ts).map (fun t => rowForestLen (lmb := lmb) E z α t.label)).sum =
        (ts.map (treeMemLen (lmb := lmb) E z α)).sum := by
  intro n
  induction n with
  | zero =>
      intro ts hts
      have : ts = [] := by
        cases ts with
        | nil => rfl
        | cons t rest =>
            have : 1 ≤ t.size := by cases t; simp [NTree.size]
            rw [totalSize_cons] at hts; omega
      subst ts
      simp [bfsForest_nil]
  | succ m ih =>
      intro ts hts
      by_cases hne : ts = []
      · subst hne; simp [bfsForest_nil]
      · rw [bfsForest_cons_eq ts hne, List.map_append, List.sum_append]
        have hch : totalSize (ts.flatMap NTree.children) ≤ m := by
          have := totalSize_flatMap_children (LT := GenComputeRow K) ts
          have hlen : 1 ≤ ts.length := List.length_pos_iff.mpr hne
          omega
        rw [ih _ hch]
        match ts with
        | [] => exact absurd rfl hne
        | t :: rest =>
            cases t with
            | node g cs =>
                simp [treeMemLen, List.flatMap_cons, List.map_append, List.sum_append]
                have hrest :
                    ((rest.map (fun t => rowForestLen (lmb := lmb) E z α t.label)).sum +
                      ((rest.flatMap NTree.children).map (treeMemLen (lmb := lmb) E z α)).sum) =
                      (rest.map (treeMemLen (lmb := lmb) E z α)).sum := by
                  by_cases hr : rest = []
                  · subst hr; simp
                  · have hsz : totalSize rest ≤ m := by
                      have : 1 ≤ NTree.size (.node g cs) := by simp [NTree.size]
                      rw [totalSize_cons] at hts; omega
                    have hch' : totalSize (rest.flatMap NTree.children) ≤ m := by
                      have := totalSize_flatMap_children (LT := GenComputeRow K) rest
                      omega
                    have hbfs := ih rest hsz
                    rw [bfsForest_cons_eq rest hr, List.map_append, List.sum_append] at hbfs
                    rw [ih _ hch'] at hbfs
                    exact hbfs
                omega

theorem genMemForestFromTree_eq_bfsSum (E : Noun → ComputeTable.FP K) (z α : K)
    (t : NTree (GenComputeRow K)) :
    totalSize (genMemForestFromTree E z α lmb t) =
      ((bfsForest [t]).map (fun n => rowForestSize (lmb := lmb) E z α n.label)).sum := by
  have h := bfsForest_treeMemSize_sum (lmb := lmb) E z α (totalSize [t]) [t] le_rfl
  simpa [treeMemSize_eq] using h.symm

theorem genMemForestFromTree_eq_bfsLen (E : Noun → ComputeTable.FP K) (z α : K)
    (t : NTree (GenComputeRow K)) :
    (genMemForestFromTree E z α lmb t).length =
      ((bfsForest [t]).map (fun n => rowForestLen (lmb := lmb) E z α n.label)).sum := by
  have h := bfsForest_treeMemLen_sum (lmb := lmb) E z α (totalSize [t]) [t] le_rfl
  simpa [treeMemLen_eq] using h.symm

theorem range'_map_bfsLabelAt_eq (t : NTree (GenComputeRow K))
    (f : GenComputeRow K → ℕ)
    (hf : ∀ i, (hi : i - 1 < (bfsRows t).length) →
      f (bfsLabelAt t i) = f (bfsRows t)[i - 1]) :
    (List.range' 1 (bfsForest [t]).length).map (fun i => f (bfsLabelAt t i)) =
      (bfsForest [t]).map (fun n => f n.label) := by
  apply List.ext_getElem
  · simp [List.length_map, List.length_range']
  · intro j hj
    have hj' : j < (bfsForest [t]).length := by
      simpa [List.length_map, List.length_range'] using hj
    have hi : 1 + j - 1 < (bfsRows t).length := by
      simpa [bfsRows_length] using hj'
    simp [List.getElem_map, List.getElem_range']
    rw [hf (1 + j) hi]
    simp [bfsRows, List.getElem_map]

theorem bfsAssign_rowForest_sum (E : Noun → ComputeTable.FP K) (z α : K)
    (t : NTree (GenComputeRow K)) :
    ((bfsForest [bfsAssign t]).map (fun n => rowForestSize (lmb := lmb) E z α n.label)).sum =
      ((bfsForest [t]).map (fun n => rowForestSize (lmb := lmb) E z α n.label)).sum ∧
    ((bfsForest [bfsAssign t]).map (fun n => rowForestLen (lmb := lmb) E z α n.label)).sum =
      ((bfsForest [t]).map (fun n => rowForestLen (lmb := lmb) E z α n.label)).sum := by
  rw [bfsForest_bfsAssign]
  simp [List.map_map, Function.comp_def, buildTF_label]
  constructor
  · rw [range'_map_bfsLabelAt_eq t (rowForestSize E z α)
        (fun i hi => (rowForestSize_bfsLabelAt E z α t i hi).1)]
  · rw [range'_map_bfsLabelAt_eq t (rowForestLen E z α)
        (fun i hi => (rowForestSize_bfsLabelAt E z α t i hi).2)]

theorem airReorder_treeMemSize (E : Noun → ComputeTable.FP K) (z α : K)
    (t : NTree (GenComputeRow K)) :
    treeMemSize (lmb := lmb) E z α (airReorder t) = treeMemSize (lmb := lmb) E z α t := by
  let P := fun t : NTree (GenComputeRow K) =>
    treeMemSize (lmb := lmb) E z α (airReorder t) = treeMemSize (lmb := lmb) E z α t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro g cs ih
    change treeMemSize E z α (airReorder (NTree.node g cs)) =
      treeMemSize E z α (NTree.node g cs)
    simp [airReorder]
    split_ifs
    · unfold treeMemSize
      simp [List.map_map]
      rw [swapPair_map_sum, List.map_map]
      congr 1
      exact List.map_congr_left fun c hc => ih c hc
    · unfold treeMemSize
      simp [List.map_map]
      congr 1
      exact List.map_congr_left fun c hc => ih c hc
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

theorem airReorder_treeMemLen (E : Noun → ComputeTable.FP K) (z α : K)
    (t : NTree (GenComputeRow K)) :
    treeMemLen (lmb := lmb) E z α (airReorder t) = treeMemLen (lmb := lmb) E z α t := by
  let P := fun t : NTree (GenComputeRow K) =>
    treeMemLen (lmb := lmb) E z α (airReorder t) = treeMemLen (lmb := lmb) E z α t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro g cs ih
    change treeMemLen E z α (airReorder (NTree.node g cs)) =
      treeMemLen E z α (NTree.node g cs)
    simp [airReorder]
    split_ifs
    · unfold treeMemLen
      simp [List.map_map]
      rw [swapPair_map_sum, List.map_map]
      congr 1
      exact List.map_congr_left fun c hc => ih c hc
    · unfold treeMemLen
      simp [List.map_map]
      congr 1
      exact List.map_congr_left fun c hc => ih c hc
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

theorem mmMemForest_assigned_length (E : Noun → ComputeTable.FP K) (z α : K) :
    (genMemForestFromTree E z α lmb (bfsAssign (mmTreeAir (K := K)))).length = 618 := by
  rw [genMemForestFromTree_eq_bfsLen, (bfsAssign_rowForest_sum E z α _).2,
    ← genMemForestFromTree_eq_bfsLen, ← treeMemLen_eq]
  unfold mmTreeAir
  rw [airReorder_treeMemLen, treeMemLen_eq]
  exact mmMemForest_unassigned_length E z α

theorem mmMemForest_assigned_totalSize (E : Noun → ComputeTable.FP K) (z α : K) :
    totalSize (genMemForestFromTree E z α lmb (bfsAssign (mmTreeAir (K := K)))) =
      30936 := by
  rw [genMemForestFromTree_eq_bfsSum, (bfsAssign_rowForest_sum E z α _).1,
    ← genMemForestFromTree_eq_bfsSum, ← treeMemSize_eq]
  unfold mmTreeAir
  rw [airReorder_treeMemSize, treeMemSize_eq]
  exact mmMemForest_unassigned_totalSize E z α

#print axioms genAnnotatedRecordTree_size
#print axioms gen_op1_mem
#print axioms gen_op0_mem
#print axioms gen_op6_zero_mem
#print axioms gen_op9_mem
#print axioms gen_slam_mem
#print axioms gen_addArm_done_mem
#print axioms gen_addNewSample_mem
#print axioms gen_macArm_done_mem
#print axioms gen_addArm_one_mem
#print axioms gen_macSampleF_mem
#print axioms gen_invokeMac_mem
#print axioms gen_addFromMac_m0_mem
#print axioms gen_addFromMac_m1_mem
#print axioms gen_macNewSample_m0_mem
#print axioms gen_macNewSample_m1_mem
#print axioms gen_macArm_one_m0_mem
#print axioms gen_macArm_one_m1_mem
#print axioms gen_mmC00_mem
#print axioms gen_mmC01_mem
#print axioms gen_mmC10_mem
#print axioms gen_mmC11_mem
#print axioms mmMemForest_unassigned_length
#print axioms mmMemForest_unassigned_totalSize
#print axioms mmMemForest_assigned_length
#print axioms mmMemForest_assigned_totalSize

end

end Nock.NockVMROM.Thm54.TraceGen
