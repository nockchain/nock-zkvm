/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierA.lean

  Tier A milestone (generic-matmul plan): a two-element core with one
  conditional, exercising OP6 (branch), OP2 (eval) and OP9 (invoke) on
  one generated tree — the first program outside every DFS=BFS shape
  gate (`isPathTree`, `childrenAreLeaves`).

  The subject is `0`.  The two elements are the arms of a core
  `[[1 3] [1 5]]`.  OP6's condition `[1 0]` selects the THEN arm; that
  arm is an OP2 whose computed-subject third child is an OP9 fetch of
  axis 2 (first element `3`).  The ELSE arm `[9 [3 …]]` (second element)
  is present only structurally, as every OP6 else-formula is.

  Phases 1–4 apply without a path/star hypothesis: `bfsAssign` stamps,
  `genComputeTimestampSkeleton`, `Vcomp` on the live OP6/OP2/OP9 rows,
  slot/record census on those skeletons.  `Gen.lean` is not edited.
-/
import Nock.NockVMROM.Thm54.TraceGen.BFSAssign
import Nock.NockVMROM.Thm54.TraceGen.GenSound
import Nock.NockVMROM.Thm54.TraceGen.GenCensus
import Nock.NockVMROM.Thm54.TraceGen.GenRowSemantic
import Nock.FieldEmbedding

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.ServedLookupBridge
open ComputeTable

variable {K : Type} [Field K]

/-! ## Program nouns -- two-element core, OP6 then-arm is OP2(OP9) -/

/-- Row subject `0`. -/
def dotSubject : Noun := .atom 0
/-- First core arm `[1 3]`. -/
def dotElem0 : Noun := .cell (.atom 1) (.atom 3)
/-- Second core arm `[1 5]` (ELSE, structural only). -/
def dotElem1 : Noun := .cell (.atom 1) (.atom 5)
/-- Two-element core `[[1 3] [1 5]]`.  Kept folded so `slot` matches. -/
def dotCore : Noun := .cell dotElem0 dotElem1
/-- Core formula `[1 core]`. -/
def dotCoreFormula : Noun := .cell (.atom 1) dotCore
/-- Condition `[1 0]` → `0` → THEN. -/
def dotCondFormula : Noun := .cell (.atom 1) (.atom 0)
def dotCondResult : Noun := .atom 0
/-- OP9 formula `[9 [2 [1 core]]]` — fetch axis 2. -/
def dotOp9Tail : Noun := .cell (.atom 2) dotCoreFormula
def dotOp9Formula : Noun := .cell (.atom 9) dotOp9Tail
/-- OP2 children: `[1 [0 1]]` and `[1 op9Formula]`. -/
def dotOp2B : Noun := .cell (.atom 1) (.cell (.atom 0) (.atom 1))
def dotOp2C : Noun := .cell (.atom 1) dotOp9Formula
def dotOp2Sf1 : Noun := .cell (.atom 0) (.atom 1)
def dotOp2Sf2 : Noun := dotOp9Formula
def dotThenTail : Noun := .cell dotOp2B dotOp2C
/-- THEN formula `[2 [b c]]`. -/
def dotThenFormula : Noun := .cell (.atom 2) dotThenTail
/-- ELSE formula `[9 [3 [1 core]]]` — second element, not a compute child. -/
def dotElseFormula : Noun :=
  .cell (.atom 9) (.cell (.atom 3) dotCoreFormula)
def dotBranchPair : Noun := .cell dotThenFormula dotElseFormula
def dotParentTail : Noun := .cell dotCondFormula dotBranchPair
/-- Full formula `[6 [b [c d]]]`. -/
def dotFormula : Noun := .cell (.atom 6) dotParentTail
/-- Result: first element `3`. -/
def dotResult : Noun := .atom 3
def dotArm : Noun := dotElem0

theorem dot_slot : Noun.slot 2 dotCore = some dotArm := by
  simp [dotCore, dotElem0, dotElem1, dotArm, Noun.slot]

/-! ## Named compute subtrees (pre-stamp) -/

def dotOp6Skel : ComputeRowSkeleton :=
  genSkelOp6 dotSubject dotFormula (.atom 6) dotParentTail
    dotCondFormula dotBranchPair dotThenFormula dotElseFormula
    dotCondResult dotThenFormula dotResult

def dotOp2Skel : ComputeRowSkeleton :=
  genSkelOp2 dotSubject dotThenFormula (.atom 2) dotThenTail
    dotOp2B dotOp2C dotOp2Sf1 dotOp2Sf2 dotResult

def dotOp9Skel : ComputeRowSkeleton :=
  genSkelOp9 dotOp2Sf1 dotOp9Formula (.atom 9) dotOp9Tail
    (.atom 2) dotCoreFormula dotCore dotArm dotResult 2

def dotCondTree : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp1 dotSubject dotCondFormula dotCondResult (.atom 1))
    [⟨dotCondFormula, dotCondResult, 3, 0⟩]) []

def dotOp1BTree : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp1 dotSubject dotOp2B dotOp2Sf1 (.atom 1))
    [⟨dotOp2B, dotOp2Sf1, 3, 0⟩]) []

def dotOp1CTree : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp1 dotSubject dotOp2C dotOp2Sf2 (.atom 1))
    [⟨dotOp2C, dotOp2Sf2, 3, 0⟩]) []

def dotOp9CoreTree : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp1 dotOp2Sf1 dotCoreFormula dotCore (.atom 1))
    [⟨dotCoreFormula, dotCore, 3, 0⟩]) []

def dotOp9InvokeTree : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp1 dotCore dotArm dotResult (.atom 1))
    [⟨dotArm, dotResult, 3, 0⟩]) []

def dotOp9Tree : NTree (GenComputeRow K) :=
  .node (skelNode dotOp9Skel
    [⟨dotOp9Formula, dotOp9Tail, 3, 0⟩,
     ⟨dotOp9Tail, .atom 2, 2, 0⟩,
     ⟨dotCore, dotArm, 2, 0⟩])
    [dotOp9CoreTree, dotOp9InvokeTree]

def dotOp2Tree : NTree (GenComputeRow K) :=
  .node (skelNode dotOp2Skel
    [⟨dotThenFormula, dotThenTail, 3, 0⟩,
     ⟨dotThenTail, dotOp2B, 2, 0⟩])
    [dotOp1BTree, dotOp1CTree, dotOp9Tree]

/-- The OP6/OP2/OP9 tree the DFS arm emits. -/
def dotTree : NTree (GenComputeRow K) :=
  .node (skelNode dotOp6Skel
    [⟨dotFormula, dotParentTail, 3, 0⟩,
     ⟨dotParentTail, dotCondFormula, 2, 0⟩,
     ⟨dotBranchPair, dotThenFormula, 2, 0⟩])
    [dotCondTree, dotOp2Tree]

/-- AIR-ordered OP6 tree: children `[taken, condition]` matching `sf1`/`sf2`
    (`evalV` / `Op6ConfigK3`), not the generator's DFS `[condition, taken]`.
    `dotTree` is unchanged so `genComputeSkeleton_dot` stays. -/
def dotTreeAir : NTree (GenComputeRow K) :=
  .node (skelNode dotOp6Skel
    [⟨dotFormula, dotParentTail, 3, 0⟩,
     ⟨dotParentTail, dotCondFormula, 2, 0⟩,
     ⟨dotBranchPair, dotThenFormula, 2, 0⟩])
    [dotOp2Tree, dotCondTree]

/-! ## Generator emission -/

/-- Fuel `n+4` covers OP1, OP9 (2) and OP2 (3) under the OP6 wrapper. -/
theorem genComputeSkeleton_dot (n : ℕ) :
    genComputeSkeleton (K := K) (n + 4) dotSubject dotFormula
      = .ok (dotTree, dotResult) := by
  show genComputeSkeleton ((n + 3) + 1) dotSubject dotFormula = _
  simp only [genComputeSkeleton, dotFormula, dotParentTail, dotBranchPair,
    dotCondFormula, dotThenFormula, dotElseFormula, dotThenTail, dotOp2B,
    dotOp2C, dotOp9Formula, dotOp9Tail, dotCoreFormula, dotSubject,
    dotArm, dotResult, dot_slot]
  rfl

/-! ## Semantics -/

theorem dot_evalFBy :
    FieldEmbedding.evalFBy 97 8 dotSubject dotFormula = some dotResult := by
  simp [FieldEmbedding.evalFBy, dotSubject, dotFormula, dotParentTail,
    dotBranchPair, dotCondFormula, dotThenFormula, dotElseFormula,
    dotThenTail, dotOp2B, dotOp2C, dotOp9Formula, dotOp9Tail, dotCoreFormula,
    dotCore, dotElem0, dotElem1, dotResult, Noun.slot]

/-! ## Outside every DFS=BFS shape gate -/

theorem dotTree_not_isPathTree :
    ¬ isPathTree (dotTree (K := K)) := by
  intro h
  simp [dotTree, isPathTree] at h

theorem dotTree_not_childrenAreLeaves :
    ¬ childrenAreLeaves (dotTree (K := K)) := by
  intro h
  have hop2 : dotOp2Tree (K := K) ∈ (dotTree (K := K)).children := by
    simp [dotTree]
  have := h _ hop2
  simp [NTree.isLeaf, dotOp2Tree] at this

theorem dotTree_root_s6 :
    (dotTree (K := K)).label.skel.state = State.s6 :=
  rfl

theorem dotTree_has_s2 :
    ∃ u ∈ (dotTree (K := K)).children, u.label.skel.state = State.s2 :=
  ⟨dotOp2Tree, by simp [dotTree], rfl⟩

/-! ## BFS flatten -/

theorem dot_bfsForest :
    bfsForest [dotTree (K := K)] =
      [dotTree, dotCondTree, dotOp2Tree, dotOp1BTree, dotOp1CTree,
       dotOp9Tree, dotOp9CoreTree, dotOp9InvokeTree] := by
  have hne {α : Type} {a : α} {l : List α} : a :: l ≠ [] := List.cons_ne_nil _ _
  rw [bfsForest_cons_eq _ (List.cons_ne_nil _ _)]
  have hc : (dotTree (K := K)).children = [dotCondTree, dotOp2Tree] := rfl
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, hc]
  have hc0 : (dotCondTree (K := K)).children = [] := rfl
  have hc1 : (dotOp2Tree (K := K)).children =
      [dotOp1BTree, dotOp1CTree, dotOp9Tree] := rfl
  rw [bfsForest_cons_eq (_ :: _) hne]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hc0]
  rw [List.nil_append, hc1]
  rw [bfsForest_cons_eq (_ :: _) hne]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hb : (dotOp1BTree (K := K)).children = [] := rfl
  have hc' : (dotOp1CTree (K := K)).children = [] := rfl
  have h9 : (dotOp9Tree (K := K)).children =
      [dotOp9CoreTree, dotOp9InvokeTree] := rfl
  rw [hb, hc', h9, List.nil_append, List.nil_append]
  rw [bfsForest_cons_eq (_ :: _) hne]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hr : (dotOp9CoreTree (K := K)).children = [] := rfl
  have hi : (dotOp9InvokeTree (K := K)).children = [] := rfl
  rw [hr, hi]
  simp [bfsForest_nil]

theorem dot_bfsRows :
    bfsRows (dotTree (K := K)) =
      [dotTree.label, dotCondTree.label, dotOp2Tree.label,
       dotOp1BTree.label, dotOp1CTree.label, dotOp9Tree.label,
       dotOp9CoreTree.label, dotOp9InvokeTree.label] := by
  simp [bfsRows, dot_bfsForest]

theorem dot_air_bfsForest :
    bfsForest [dotTreeAir (K := K)] =
      [dotTreeAir, dotOp2Tree, dotCondTree, dotOp1BTree, dotOp1CTree,
       dotOp9Tree, dotOp9CoreTree, dotOp9InvokeTree] := by
  have hne {α : Type} {a : α} {l : List α} : a :: l ≠ [] := List.cons_ne_nil _ _
  rw [bfsForest_cons_eq _ (List.cons_ne_nil _ _)]
  have hc : (dotTreeAir (K := K)).children = [dotOp2Tree, dotCondTree] := rfl
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, hc]
  have hc0 : (dotOp2Tree (K := K)).children =
      [dotOp1BTree, dotOp1CTree, dotOp9Tree] := rfl
  have hc1 : (dotCondTree (K := K)).children = [] := rfl
  rw [bfsForest_cons_eq (_ :: _) hne]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hc0, hc1]
  rw [bfsForest_cons_eq (_ :: _) hne]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hb : (dotOp1BTree (K := K)).children = [] := rfl
  have hc' : (dotOp1CTree (K := K)).children = [] := rfl
  have h9 : (dotOp9Tree (K := K)).children =
      [dotOp9CoreTree, dotOp9InvokeTree] := rfl
  rw [hb, hc', h9, List.nil_append, List.nil_append]
  rw [bfsForest_cons_eq (_ :: _) hne]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hr : (dotOp9CoreTree (K := K)).children = [] := rfl
  have hi : (dotOp9InvokeTree (K := K)).children = [] := rfl
  rw [hr, hi]
  simp [bfsForest_nil]

theorem dot_air_bfsRows :
    bfsRows (dotTreeAir (K := K)) =
      [dotTreeAir.label, dotOp2Tree.label, dotCondTree.label,
       dotOp1BTree.label, dotOp1CTree.label, dotOp9Tree.label,
       dotOp9CoreTree.label, dotOp9InvokeTree.label] := by
  simp [bfsRows, dot_air_bfsForest]

theorem dotTree_has_s9 :
    ∃ u ∈ bfsForest [dotTree (K := K)], u.label.skel.state = State.s9 :=
  ⟨dotOp9Tree, by simp [dot_bfsForest], rfl⟩

/-! ## BFS stamps on a genuine branch -/

theorem bfsAssign_root_mem (t : NTree (GenComputeRow K)) :
    bfsAssign t ∈ bfsForest [bfsAssign t] := by
  rw [bfsForest_cons_eq _ (List.cons_ne_nil _ _)]
  exact List.mem_cons.mpr (Or.inl rfl)

theorem bfsRows_head? (t : NTree (GenComputeRow K)) :
    (bfsRows t).head? = some t.label := by
  unfold bfsRows
  rw [bfsForest_cons_eq _ (List.cons_ne_nil _ _)]
  rfl

theorem bfsAssign_root_skel (t : NTree (GenComputeRow K)) :
    (bfsAssign t).label.skel = t.label.skel := by
  rw [bfsAssign_label]
  unfold bfsLabelAt
  have h0 : (1 - 1 : ℕ) = 0 := rfl
  rw [h0]
  have hhead : (bfsRows t)[0]? = (bfsRows t).head? := by
    cases (bfsRows t) <;> rfl
  rw [hhead, bfsRows_head?]

theorem mem_bfsAssign_stampOfAcc (t : NTree (GenComputeRow K))
    {n : NTree (GenComputeRow K)} (hn : n ∈ bfsForest [bfsAssign t]) :
    n.label.stamp =
      stampOfAcc n.label.skel.state n.label.stamp.lnPrevExponent := by
  have hmem : n.label ∈ (bfsForest [bfsAssign t]).map NTree.label :=
    List.mem_map.mpr ⟨n, hn, rfl⟩
  rw [bfsAssign_bfsForest_labels, List.mem_map] at hmem
  obtain ⟨i, hi, hni⟩ := hmem
  have hi' := lt_bfsRows_of_mem_range' hi
  rw [← hni, bfsLabelAt_eq t i hi']
  simp [stampOfAcc_lnPrevExponent]

theorem exists_assigned_label (t : NTree (GenComputeRow K)) (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [t]).length) :
    ∃ n ∈ bfsForest [bfsAssign t], n.label = bfsLabelAt t i := by
  have : bfsLabelAt t i ∈ (bfsForest [bfsAssign t]).map NTree.label := by
    rw [bfsAssign_bfsForest_labels]
    exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact List.mem_map.mp this

theorem bfsLabelAt_stampOfAcc (t : NTree (GenComputeRow K)) (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [t]).length) :
    (bfsLabelAt t i).stamp =
      stampOfAcc (bfsLabelAt t i).skel.state
        (bfsLabelAt t i).stamp.lnPrevExponent := by
  obtain ⟨n, hn, hlab⟩ := exists_assigned_label t i hi
  have := mem_bfsAssign_stampOfAcc t hn
  simpa [hlab] using this

/-- Unconditional timestamp skeleton: no `isPathTree` / `childrenAreLeaves`. -/
noncomputable def dotTimestampSkeleton :
    SemanticTimestampSkeleton K K
      (genComputeSemanticSkeleton (bfsAssign (dotTree (K := K)))) :=
  genComputeTimestampSkeleton K dotTree

theorem dotTimestampSkeleton_nonvacuous :
    Nonempty (SemanticTimestampSkeleton K K
      (genComputeSemanticSkeleton (bfsAssign (dotTree (K := K))))) :=
  ⟨dotTimestampSkeleton⟩

/-! ## Census on the three live opcode skeletons -/

theorem dot_op6_slotSemantics :
    SkeletonSlotSemantics (dotOp6Skel) :=
  genSkelOp6_slotSemantics _ _ _ _ _ _ _ _ _ _ _

theorem dot_op2_slotSemantics :
    SkeletonSlotSemantics (dotOp2Skel) :=
  genSkelOp2_slotSemantics _ _ _ _ _ _ _ _ _

theorem dot_op9_slotSemantics :
    SkeletonSlotSemantics (dotOp9Skel) :=
  genSkelOp9_slotSemantics _ _ _ _ _ _ _ _ _ _ dot_slot

theorem dot_op6_recordEquations :
    SkeletonRecordEquations (dotOp6Skel) :=
  genSkelOp6_recordEquations _ _ _ _ _ _ _ _ _ _ _

theorem dot_op2_recordEquations :
    SkeletonRecordEquations (dotOp2Skel) :=
  genSkelOp2_recordEquations _ _ _ _ _ _ _ _ _

theorem dot_op9_recordEquations :
    SkeletonRecordEquations (dotOp9Skel) :=
  genSkelOp9_recordEquations _ _ _ _ _ _ _ _ _ _

/-! ## `BindComputeRow` on the three opcode skeletons -/

theorem dot_op6_bindCompute (z α : K) :
    BindComputeRow z dotOp6Skel
      (renderOp6Row z α (stampOfAcc State.s6 0) dotOp6Skel) := by
  refine genSkelOp6_bindCompute z α _ _ _ _ _ _ _ _ _ _ _ (stampOfAcc State.s6 0)
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [formulaHead, formulaTail, dotFormula, dotParentTail,
    dotBranchPair, dotCondFormula, dotThenFormula, dotElseFormula]

theorem dot_op2_bindCompute (z α : K) :
    BindComputeRow z dotOp2Skel
      (renderOp2Row z α (stampOfAcc State.s2 0) dotOp2Skel) := by
  refine genSkelOp2_bindCompute z α _ _ _ _ _ _ _ _ _ (stampOfAcc State.s2 0)
    ?_ ?_ ?_ ?_
  all_goals simp [formulaHead, formulaTail, dotThenFormula, dotThenTail,
    dotOp2B, dotOp2C]

theorem dot_op9_bindCompute (z α : K) :
    BindComputeRow z dotOp9Skel
      (renderOp9Row z α (stampOfAcc State.s9 0) dotOp9Skel) := by
  refine genSkelOp9_bindCompute z α _ _ _ _ _ _ _ _ _ _ (stampOfAcc State.s9 0)
    ?_ ?_ ?_ ?_
  all_goals simp [formulaHead, formulaTail, dotOp9Formula, dotOp9Tail,
    dotCoreFormula]

/-! ## Condition fingerprint (1-leaf atom 0) -/

theorem encC_atom0 (z : K) :
    encC z (.atom 0) = FP.atomFP z 0 := by
  rw [encC_eq, GlobalCarryRecognizer.enc_atom, Nat.cast_zero]

theorem encC_atom0_leaf (z : K) : (encC z (.atom 0)).leaf = 0 := by
  simp [encC_atom0 z, FP.atomFP]

theorem encC_atom0_size_dyck (z : K) :
    (encC z (.atom 0)).size = z ∧ (encC z (.atom 0)).dyck = 0 := by
  simp [encC_atom0 z, FP.atomFP]

/-! ## `Vcomp` after BFS assign -/

theorem dot_range3 :
    3 ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length := by
  simp [dot_bfsForest]

theorem dot_range6 :
    6 ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length := by
  simp [dot_bfsForest]

private lemma dot_op6_skel :
    (dotTree (K := K)).label.skel = dotOp6Skel :=
  rfl

theorem render_bfsAssign_dot_root_Vcomp (z α : K) (hz : z ≠ 0) :
    let g := (bfsAssign (dotTree (K := K))).label
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  let g := (bfsAssign (dotTree (K := K))).label
  have hskel : g.skel = dotOp6Skel := by
    rw [bfsAssign_root_skel, dot_op6_skel]
  have hstate : g.skel.state = State.s6 := by
    rw [hskel]; rfl
  have hstamp :
      g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent :=
    mem_bfsAssign_stampOfAcc _ (bfsAssign_root_mem _)
  refine renderNode_op6_Vcomp_of_assigned z α g
    dotThenFormula dotElseFormula hz hstate ?hform ?hsf1s ?hsf2s
    ?hsf1f ?heval ?hsf2e hstamp
  · rw [hskel]
    simp [dotOp6Skel, genSkelOp6, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp, dotFormula, dotParentTail, dotBranchPair,
      dotCondFormula]
  · rw [hskel]
    simp [dotOp6Skel, genSkelOp6, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · rw [hskel]
    simp [dotOp6Skel, genSkelOp6, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · rw [hskel]
    refine Or.inl ⟨?_, ?_⟩
    · simp only [dotOp6Skel, genSkelOp6, P8Census.skeletonSubformula,
        ComputeTable.fanoutComp, dotCondResult]
      exact encC_atom0_leaf z
    · simp [dotOp6Skel, genSkelOp6, P8Census.skeletonSubformula,
        ComputeTable.fanoutComp]
  · rw [hskel]
    simp [dotOp6Skel, genSkelOp6, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · rw [hskel]
    refine ⟨?_, ?_, Or.inl ?_⟩
    · simp only [dotOp6Skel, genSkelOp6, P8Census.skeletonSubformula,
        ComputeTable.fanoutComp, dotCondResult]
      exact (encC_atom0_size_dyck z).1
    · simp only [dotOp6Skel, genSkelOp6, P8Census.skeletonSubformula,
        ComputeTable.fanoutComp, dotCondResult]
      exact (encC_atom0_size_dyck z).2
    · simp only [dotOp6Skel, genSkelOp6, P8Census.skeletonSubformula,
        ComputeTable.fanoutComp, dotCondResult]
      exact encC_atom0_leaf z

theorem render_bfsAssign_dot_op2_Vcomp (z α : K) (hz : z ≠ 0) :
    let g := bfsLabelAt (dotTree (K := K)) 3
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  let g := bfsLabelAt (dotTree (K := K)) 3
  have hi := lt_bfsRows_of_mem_range' (t := (dotTree (K := K))) dot_range3
  have hskel : g.skel = dotOp2Skel := by
    rw [bfsLabelAt_skel (dotTree (K := K)) 3 hi]
    simp [dot_bfsRows, dotOp2Tree, skelNode]
  have hstate : g.skel.state = State.s2 := by
    rw [hskel]; rfl
  have hstamp := bfsLabelAt_stampOfAcc (dotTree (K := K)) 3 dot_range3
  refine renderNode_op2_Vcomp_of_assigned z α g hz hstate ?hform
    ?hsf1s ?hsf2s ?hsf3s ?hsf3f ?heval hstamp
  · rw [hskel]
    simp [dotOp2Skel, genSkelOp2, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp, dotThenFormula, dotThenTail, dotOp2B, dotOp2C]
  · rw [hskel]
    simp [dotOp2Skel, genSkelOp2, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · rw [hskel]
    simp [dotOp2Skel, genSkelOp2, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · rw [hskel]
    simp [dotOp2Skel, genSkelOp2, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · rw [hskel]
    simp [dotOp2Skel, genSkelOp2, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · rw [hskel]
    simp [dotOp2Skel, genSkelOp2, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]

theorem render_bfsAssign_dot_op9_Vcomp (z α : K) (hz : z ≠ 0) :
    let g := bfsLabelAt (dotTree (K := K)) 6
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  let g := bfsLabelAt (dotTree (K := K)) 6
  have hi := lt_bfsRows_of_mem_range' (t := (dotTree (K := K))) dot_range6
  have hskel : g.skel = dotOp9Skel := by
    rw [bfsLabelAt_skel (dotTree (K := K)) 6 hi]
    simp [dot_bfsRows, dotOp9Tree, skelNode]
  have hstate : g.skel.state = State.s9 := by
    rw [hskel]; rfl
  have hstamp := bfsLabelAt_stampOfAcc (dotTree (K := K)) 6 dot_range6
  refine renderNode_op9_Vcomp_of_assigned z α g hz hstate ?hform
    ?hsf1s ?hsf2s ?heval hstamp
  · rw [hskel]
    simp [dotOp9Skel, genSkelOp9, P8Census.skeletonSubformula,
      P8Census.skeletonMemoryAxis, ComputeTable.fanoutComp,
      Nock.Framework.recordCount, dotOp9Formula, dotOp9Tail, dotCoreFormula]
  · rw [hskel]
    simp [dotOp9Skel, genSkelOp9, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · rw [hskel]
    simp [dotOp9Skel, genSkelOp9, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · rw [hskel]
    simp [dotOp9Skel, genSkelOp9, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_dot
#print axioms Nock.NockVMROM.Thm54.TraceGen.dot_evalFBy
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotTree_not_isPathTree
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotTree_not_childrenAreLeaves
#print axioms Nock.NockVMROM.Thm54.TraceGen.mem_bfsAssign_stampOfAcc
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotTimestampSkeleton_nonvacuous
#print axioms Nock.NockVMROM.Thm54.TraceGen.render_bfsAssign_dot_root_Vcomp
#print axioms Nock.NockVMROM.Thm54.TraceGen.render_bfsAssign_dot_op2_Vcomp
#print axioms Nock.NockVMROM.Thm54.TraceGen.render_bfsAssign_dot_op9_Vcomp
#print axioms Nock.NockVMROM.Thm54.TraceGen.dot_op6_bindCompute
