/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierAAccept.lean

  Compute-row acceptance of the generated eight-row BFS render: each
  `renderNode (bfsLabelAt dotTree i)` satisfies `Vcomp`, agrees on the
  outer/public state, and carries the configuration challenge vector, so
  `ComputeRowsAccepted` holds for `DotConfig257.exec` and
  `DotConfig769.exec`.

  OP6 / OP2 / OP9 `Vcomp` is `render_bfsAssign_dot_*_Vcomp`.  The five
  `.s1` leaves use `renderNode_op1_Vcomp_of_assigned` on the OP1 shape
  `[1 result]`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierANodup
import Nock.NockVMROM.Thm54.Language
import Mathlib.Tactic.IntervalCases

set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

variable {K : Type} [Field K]

theorem renderNode_state_agree (z α : K) (g : GenComputeRow K) :
    (renderNode z α g).row.1 = (renderNode z α g).row.2.2.1.state := by
  unfold renderNode
  cases g.skel.state <;> rfl

theorem renderNode_inputs (z α : K) (g : GenComputeRow K) :
    (renderNode z α g).row.2.1 = ⟨α, z, 0, 0, 0⟩ := by
  unfold renderNode
  cases g.skel.state <;> rfl

theorem dot_range2 :
    2 ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length := by
  simp [dot_bfsForest]

theorem dot_range4 :
    4 ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length := by
  simp [dot_bfsForest]

theorem dot_range5 :
    5 ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length := by
  simp [dot_bfsForest]

theorem dot_range7 :
    7 ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length := by
  simp [dot_bfsForest]

theorem dot_range8 :
    8 ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length := by
  simp [dot_bfsForest]

theorem dot_air_range1 :
    1 ∈ List.range' 1 (bfsForest [dotTreeAir (K := K)]).length := by
  simp [dot_air_bfsForest]

theorem dot_air_range2 :
    2 ∈ List.range' 1 (bfsForest [dotTreeAir (K := K)]).length := by
  simp [dot_air_bfsForest]

theorem dot_air_range3 :
    3 ∈ List.range' 1 (bfsForest [dotTreeAir (K := K)]).length := by
  simp [dot_air_bfsForest]

theorem dot_air_range4 :
    4 ∈ List.range' 1 (bfsForest [dotTreeAir (K := K)]).length := by
  simp [dot_air_bfsForest]

theorem dot_air_range5 :
    5 ∈ List.range' 1 (bfsForest [dotTreeAir (K := K)]).length := by
  simp [dot_air_bfsForest]

theorem dot_air_range6 :
    6 ∈ List.range' 1 (bfsForest [dotTreeAir (K := K)]).length := by
  simp [dot_air_bfsForest]

theorem dot_air_range7 :
    7 ∈ List.range' 1 (bfsForest [dotTreeAir (K := K)]).length := by
  simp [dot_air_bfsForest]

theorem dot_air_range8 :
    8 ∈ List.range' 1 (bfsForest [dotTreeAir (K := K)]).length := by
  simp [dot_air_bfsForest]

theorem render_dot_op1_Vcomp (z α : K) (hz : z ≠ 0) (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length)
    (hstate : (bfsLabelAt (dotTree (K := K)) i).skel.state = State.s1)
    (hform :
      (bfsLabelAt (dotTree (K := K)) i).skel.formula =
        Noun.cell (Noun.atom 1)
          (bfsLabelAt (dotTree (K := K)) i).skel.evaluation) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTree (K := K)) i)).row.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) i)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) i)).row.2.2.2 :=
  renderNode_op1_Vcomp_of_assigned z α (bfsLabelAt (dotTree (K := K)) i) hz
    hstate hform (bfsLabelAt_stampOfAcc (dotTree (K := K)) i hi)

theorem render_dot_op1_2_Vcomp (z α : K) (hz : z ≠ 0) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 2)).row.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 2)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 2)).row.2.2.2 := by
  have hskel := bfsLabelAt_dot_skel2 (K := K)
  have hstate : (bfsLabelAt (dotTree (K := K)) 2).skel.state = State.s1 := by
    rw [hskel]; rfl
  refine render_dot_op1_Vcomp z α hz 2 dot_range2 hstate ?_
  rw [hskel]
  simp [dotCondTree, skelNode, genSkelOp1, dotCondFormula, dotCondResult]

theorem render_dot_op1_4_Vcomp (z α : K) (hz : z ≠ 0) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 4)).row.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 4)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 4)).row.2.2.2 := by
  have hskel := bfsLabelAt_dot_skel4 (K := K)
  have hstate : (bfsLabelAt (dotTree (K := K)) 4).skel.state = State.s1 := by
    rw [hskel]; rfl
  refine render_dot_op1_Vcomp z α hz 4 dot_range4 hstate ?_
  rw [hskel]
  simp [dotOp1BTree, skelNode, genSkelOp1, dotOp2B, dotOp2Sf1]

theorem render_dot_op1_5_Vcomp (z α : K) (hz : z ≠ 0) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 5)).row.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 5)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 5)).row.2.2.2 := by
  have hskel := bfsLabelAt_dot_skel5 (K := K)
  have hstate : (bfsLabelAt (dotTree (K := K)) 5).skel.state = State.s1 := by
    rw [hskel]; rfl
  refine render_dot_op1_Vcomp z α hz 5 dot_range5 hstate ?_
  rw [hskel]
  simp [dotOp1CTree, skelNode, genSkelOp1, dotOp2C, dotOp2Sf2]

theorem render_dot_op1_7_Vcomp (z α : K) (hz : z ≠ 0) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 7)).row.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 7)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 7)).row.2.2.2 := by
  have hskel := bfsLabelAt_dot_skel7 (K := K)
  have hstate : (bfsLabelAt (dotTree (K := K)) 7).skel.state = State.s1 := by
    rw [hskel]; rfl
  refine render_dot_op1_Vcomp z α hz 7 dot_range7 hstate ?_
  rw [hskel]
  simp [dotOp9CoreTree, skelNode, genSkelOp1, dotCoreFormula]

theorem render_dot_op1_8_Vcomp (z α : K) (hz : z ≠ 0) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 8)).row.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 8)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 8)).row.2.2.2 := by
  have hskel := bfsLabelAt_dot_skel8 (K := K)
  have hstate : (bfsLabelAt (dotTree (K := K)) 8).skel.state = State.s1 := by
    rw [hskel]; rfl
  refine render_dot_op1_Vcomp z α hz 8 dot_range8 hstate ?_
  rw [hskel]
  simp [dotOp9InvokeTree, skelNode, genSkelOp1, dotArm, dotElem0, dotResult]

theorem render_dot_root_Vcomp (z α : K) (hz : z ≠ 0) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 1)).row.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 1)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 1)).row.2.2.2 := by
  simpa [bfsAssign_label] using render_bfsAssign_dot_root_Vcomp z α hz

theorem render_dot_op2_Vcomp (z α : K) (hz : z ≠ 0) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 3)).row.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 3)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 3)).row.2.2.2 :=
  render_bfsAssign_dot_op2_Vcomp z α hz

theorem render_dot_op9_Vcomp (z α : K) (hz : z ≠ 0) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 6)).row.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 6)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) 6)).row.2.2.2 :=
  render_bfsAssign_dot_op9_Vcomp z α hz

theorem bfsLabelAt_dot_Vcomp (z α : K) (hz : z ≠ 0) (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTree (K := K)) i)).row.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) i)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTree (K := K)) i)).row.2.2.2 := by
  rcases dot_bfs_index i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact render_dot_root_Vcomp z α hz
  · exact render_dot_op1_2_Vcomp z α hz
  · exact render_dot_op2_Vcomp z α hz
  · exact render_dot_op1_4_Vcomp z α hz
  · exact render_dot_op1_5_Vcomp z α hz
  · exact render_dot_op9_Vcomp z α hz
  · exact render_dot_op1_7_Vcomp z α hz
  · exact render_dot_op1_8_Vcomp z α hz

/-! ## AIR-ordered `Vcomp` -/

theorem render_air_op1_Vcomp (z α : K) (hz : z ≠ 0) (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [dotTreeAir (K := K)]).length)
    (hstate : (bfsLabelAt (dotTreeAir (K := K)) i).skel.state = State.s1)
    (hform :
      (bfsLabelAt (dotTreeAir (K := K)) i).skel.formula =
        Noun.cell (Noun.atom 1)
          (bfsLabelAt (dotTreeAir (K := K)) i).skel.evaluation) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) i)).row.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) i)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) i)).row.2.2.2 :=
  renderNode_op1_Vcomp_of_assigned z α (bfsLabelAt (dotTreeAir (K := K)) i) hz
    hstate hform (bfsLabelAt_stampOfAcc (dotTreeAir (K := K)) i hi)

theorem render_air_op1_3_Vcomp (z α : K) (hz : z ≠ 0) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 3)).row.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 3)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 3)).row.2.2.2 := by
  have hskel := bfsLabelAt_air_skel3 (K := K)
  have hstate : (bfsLabelAt (dotTreeAir (K := K)) 3).skel.state = State.s1 := by
    rw [hskel]; rfl
  refine render_air_op1_Vcomp z α hz 3 dot_air_range3 hstate ?_
  rw [hskel]
  simp [dotCondTree, skelNode, genSkelOp1, dotCondFormula, dotCondResult]

theorem render_air_op1_4_Vcomp (z α : K) (hz : z ≠ 0) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 4)).row.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 4)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 4)).row.2.2.2 := by
  have hskel := bfsLabelAt_air_skel4 (K := K)
  have hstate : (bfsLabelAt (dotTreeAir (K := K)) 4).skel.state = State.s1 := by
    rw [hskel]; rfl
  refine render_air_op1_Vcomp z α hz 4 dot_air_range4 hstate ?_
  rw [hskel]
  simp [dotOp1BTree, skelNode, genSkelOp1, dotOp2B, dotOp2Sf1]

theorem render_air_op1_5_Vcomp (z α : K) (hz : z ≠ 0) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 5)).row.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 5)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 5)).row.2.2.2 := by
  have hskel := bfsLabelAt_air_skel5 (K := K)
  have hstate : (bfsLabelAt (dotTreeAir (K := K)) 5).skel.state = State.s1 := by
    rw [hskel]; rfl
  refine render_air_op1_Vcomp z α hz 5 dot_air_range5 hstate ?_
  rw [hskel]
  simp [dotOp1CTree, skelNode, genSkelOp1, dotOp2C, dotOp2Sf2]

theorem render_air_op1_7_Vcomp (z α : K) (hz : z ≠ 0) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 7)).row.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 7)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 7)).row.2.2.2 := by
  have hskel := bfsLabelAt_air_skel7 (K := K)
  have hstate : (bfsLabelAt (dotTreeAir (K := K)) 7).skel.state = State.s1 := by
    rw [hskel]; rfl
  refine render_air_op1_Vcomp z α hz 7 dot_air_range7 hstate ?_
  rw [hskel]
  simp [dotOp9CoreTree, skelNode, genSkelOp1, dotCoreFormula]

theorem render_air_op1_8_Vcomp (z α : K) (hz : z ≠ 0) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 8)).row.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 8)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 8)).row.2.2.2 := by
  have hskel := bfsLabelAt_air_skel8 (K := K)
  have hstate : (bfsLabelAt (dotTreeAir (K := K)) 8).skel.state = State.s1 := by
    rw [hskel]; rfl
  refine render_air_op1_Vcomp z α hz 8 dot_air_range8 hstate ?_
  rw [hskel]
  simp [dotOp9InvokeTree, skelNode, genSkelOp1, dotArm, dotElem0, dotResult]

theorem render_bfsAssign_air_root_Vcomp (z α : K) (hz : z ≠ 0) :
    let g := (bfsAssign (dotTreeAir (K := K))).label
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  let g := (bfsAssign (dotTreeAir (K := K))).label
  have hskel : g.skel = dotOp6Skel := by
    rw [bfsAssign_root_skel]
    rfl
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

theorem render_air_root_Vcomp (z α : K) (hz : z ≠ 0) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 1)).row.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 1)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 1)).row.2.2.2 := by
  simpa [bfsAssign_label] using render_bfsAssign_air_root_Vcomp z α hz

theorem render_bfsAssign_air_op2_Vcomp (z α : K) (hz : z ≠ 0) :
    let g := bfsLabelAt (dotTreeAir (K := K)) 2
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  let g := bfsLabelAt (dotTreeAir (K := K)) 2
  have hi := lt_bfsRows_of_mem_range' (t := (dotTreeAir (K := K))) dot_air_range2
  have hskel : g.skel = dotOp2Skel := by
    rw [bfsLabelAt_skel (dotTreeAir (K := K)) 2 hi]
    simp [dot_air_bfsRows, dotOp2Tree, skelNode]
  have hstate : g.skel.state = State.s2 := by
    rw [hskel]; rfl
  have hstamp := bfsLabelAt_stampOfAcc (dotTreeAir (K := K)) 2 dot_air_range2
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

theorem render_air_op2_Vcomp (z α : K) (hz : z ≠ 0) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 2)).row.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 2)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 2)).row.2.2.2 :=
  render_bfsAssign_air_op2_Vcomp z α hz

theorem render_bfsAssign_air_op9_Vcomp (z α : K) (hz : z ≠ 0) :
    let g := bfsLabelAt (dotTreeAir (K := K)) 6
    let row := (renderNode z α g).row
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  let g := bfsLabelAt (dotTreeAir (K := K)) 6
  have hi := lt_bfsRows_of_mem_range' (t := (dotTreeAir (K := K))) dot_air_range6
  have hskel : g.skel = dotOp9Skel := by
    rw [bfsLabelAt_skel (dotTreeAir (K := K)) 6 hi]
    simp [dot_air_bfsRows, dotOp9Tree, skelNode]
  have hstate : g.skel.state = State.s9 := by
    rw [hskel]; rfl
  have hstamp := bfsLabelAt_stampOfAcc (dotTreeAir (K := K)) 6 dot_air_range6
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

theorem render_air_op9_Vcomp (z α : K) (hz : z ≠ 0) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 6)).row.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 6)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) 6)).row.2.2.2 :=
  render_bfsAssign_air_op9_Vcomp z α hz

theorem bfsLabelAt_air_Vcomp (z α : K) (hz : z ≠ 0) (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [dotTreeAir (K := K)]).length) :
    Vcomp
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) i)).row.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) i)).row.2.2.1
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) i)).row.2.2.2 := by
  rcases dot_air_bfs_index i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact render_air_root_Vcomp z α hz
  · exact render_air_op2_Vcomp z α hz
  · exact render_air_op1_3_Vcomp z α hz
  · exact render_air_op1_4_Vcomp z α hz
  · exact render_air_op1_5_Vcomp z α hz
  · exact render_air_op9_Vcomp z α hz
  · exact render_air_op1_7_Vcomp z α hz
  · exact render_air_op1_8_Vcomp z α hz

theorem renderNode_ln (z α : K) (g : GenComputeRow K) :
    (renderNode z α g).row.2.2.1.ln = α ^ g.stamp.lnExponent ∧
      (renderNode z α g).row.2.2.1.ln_prev = α ^ g.stamp.lnPrevExponent := by
  unfold renderNode
  cases g.skel.state <;>
    simp [renderOp0Row, renderOp1Row, renderOp2Row, renderOp3Row, renderOp4Row,
      renderOp5Row, renderOp6Row, renderOp7Row, renderOp8Row, renderOp9Row,
      renderConsRow]

theorem adjacent_ln (z α : K) (k : ℕ) (hk : k + 1 < 8) :
    (renderNode z α (bfsLabelAt (dotTree (K := K)) (k + 1))).row.2.2.1.ln =
      (renderNode z α (bfsLabelAt (dotTree (K := K)) (k + 2))).row.2.2.1.ln_prev := by
  have hlen : (bfsRows (dotTree (K := K))).length = 8 := by simp [dot_bfsRows]
  have hk0 : (k + 1) - 1 < (bfsRows (dotTree (K := K))).length := by omega
  have hk1 : (k + 2) - 1 < (bfsRows (dotTree (K := K))).length := by omega
  have hkacc : k < (bfsRows (dotTree (K := K))).length := by omega
  rw [(renderNode_ln z α _).1, (renderNode_ln z α _).2]
  rw [bfsLabelAt_lnExponent (dotTree (K := K)) (k + 1) hk0,
    bfsLabelAt_lnPrev (dotTree (K := K)) (k + 2) hk1]
  have hsucc := accAt_succ_of_lt (dotTree (K := K)) k hkacc
  have hskel := bfsLabelAt_skel (dotTree (K := K)) (k + 1) hk0
  have hk1' : k + 1 - 1 = k := Nat.add_sub_cancel k 1
  have hk2' : k + 2 - 1 = k + 1 := by omega
  simp [hk1', hk2', hskel, hsucc]

theorem adjacent_ln_air (z α : K) (k : ℕ) (hk : k + 1 < 8) :
    (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) (k + 1))).row.2.2.1.ln =
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) (k + 2))).row.2.2.1.ln_prev := by
  have hlen : (bfsRows (dotTreeAir (K := K))).length = 8 := by simp [dot_air_bfsRows]
  have hk0 : (k + 1) - 1 < (bfsRows (dotTreeAir (K := K))).length := by omega
  have hk1 : (k + 2) - 1 < (bfsRows (dotTreeAir (K := K))).length := by omega
  have hkacc : k < (bfsRows (dotTreeAir (K := K))).length := by omega
  rw [(renderNode_ln z α _).1, (renderNode_ln z α _).2]
  rw [bfsLabelAt_lnExponent (dotTreeAir (K := K)) (k + 1) hk0,
    bfsLabelAt_lnPrev (dotTreeAir (K := K)) (k + 2) hk1]
  have hsucc := accAt_succ_of_lt (dotTreeAir (K := K)) k hkacc
  have hskel := bfsLabelAt_skel (dotTreeAir (K := K)) (k + 1) hk0
  have hk1' : k + 1 - 1 = k := Nat.add_sub_cancel k 1
  have hk2' : k + 2 - 1 = k + 1 := by omega
  simp [hk1', hk2', hskel, hsucc]

theorem renderNode_state_eq (z α : K) (g : GenComputeRow K) :
    (renderNode z α g).row.2.2.1.state = g.skel.state := by
  unfold renderNode
  cases g.skel.state <;> rfl

theorem renderNode_wf (z α : K) (g : GenComputeRow K)
    (h : g.skel.state = State.s1 ∨ g.skel.state = State.s2 ∨
      g.skel.state = State.s6 ∨ g.skel.state = State.s9) :
    WF ⟨α, z, 0, 0, 0⟩ (renderNode z α g).row.2.2.1 where
  rlc5 := by
    intro hst _
    rw [renderNode_state_eq] at hst
    rcases h with h | h | h | h <;> rw [h] at hst <;> cases hst
  size8 := by
    intro hst
    rw [renderNode_state_eq] at hst
    rcases h with h | h | h | h <;> rw [h] at hst <;> cases hst
  size11 := by
    intro hst
    rw [renderNode_state_eq] at hst
    rcases h with h | h | h | h <;> rw [h] at hst <;> cases hst

theorem bfsLabelAt_dot_live_state (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length) :
    (bfsLabelAt (dotTree (K := K)) i).skel.state = State.s1 ∨
      (bfsLabelAt (dotTree (K := K)) i).skel.state = State.s2 ∨
      (bfsLabelAt (dotTree (K := K)) i).skel.state = State.s6 ∨
      (bfsLabelAt (dotTree (K := K)) i).skel.state = State.s9 := by
  rcases dot_bfs_index i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [bfsLabelAt_dot_skel1]; rfl
  · refine Or.inl ?_
    rw [bfsLabelAt_dot_skel2]; rfl
  · refine Or.inr (Or.inl ?_)
    rw [bfsLabelAt_dot_skel3]; rfl
  · refine Or.inl ?_
    rw [bfsLabelAt_dot_skel4]; rfl
  · refine Or.inl ?_
    rw [bfsLabelAt_dot_skel5]; rfl
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [bfsLabelAt_dot_skel6]; rfl
  · refine Or.inl ?_
    rw [bfsLabelAt_dot_skel7]; rfl
  · refine Or.inl ?_
    rw [bfsLabelAt_dot_skel8]; rfl

theorem bfsLabelAt_air_live_state (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [dotTreeAir (K := K)]).length) :
    (bfsLabelAt (dotTreeAir (K := K)) i).skel.state = State.s1 ∨
      (bfsLabelAt (dotTreeAir (K := K)) i).skel.state = State.s2 ∨
      (bfsLabelAt (dotTreeAir (K := K)) i).skel.state = State.s6 ∨
      (bfsLabelAt (dotTreeAir (K := K)) i).skel.state = State.s9 := by
  rcases dot_air_bfs_index i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [bfsLabelAt_air_skel1]; rfl
  · refine Or.inr (Or.inl ?_)
    rw [bfsLabelAt_air_skel2]; rfl
  · refine Or.inl ?_
    rw [bfsLabelAt_air_skel3]; rfl
  · refine Or.inl ?_
    rw [bfsLabelAt_air_skel4]; rfl
  · refine Or.inl ?_
    rw [bfsLabelAt_air_skel5]; rfl
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [bfsLabelAt_air_skel6]; rfl
  · refine Or.inl ?_
    rw [bfsLabelAt_air_skel7]; rfl
  · refine Or.inl ?_
    rw [bfsLabelAt_air_skel8]; rfl

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig257

open Nock Nock.Walk Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

theorem rendered_accepted (z α : K) (hz : z ≠ 0) (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length) :
    ExactExecution.ComputeRowAccepted (cfg z α)
      (renderNode z α (bfsLabelAt (dotTree (K := K)) i)).row := by
  refine ⟨renderNode_state_agree z α _, ?_, bfsLabelAt_dot_Vcomp z α hz i hi⟩
  rw [renderNode_inputs]
  simp [cfg, ChallengeVector.computeInputs]

theorem computeRowsAccepted (z α : K) (hz : z ≠ 0) :
    (exec z α).ComputeRowsAccepted := by
  rw [ExactExecution.computeRowsAccepted_iff, computeRows_eq]
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  have h1 : 1 ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length := by
    simp [dot_bfsForest]
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rendered_accepted z α hz 1 h1
  · exact rendered_accepted z α hz 2 dot_range2
  · exact rendered_accepted z α hz 3 dot_range3
  · exact rendered_accepted z α hz 4 dot_range4
  · exact rendered_accepted z α hz 5 dot_range5
  · exact rendered_accepted z α hz 6 dot_range6
  · exact rendered_accepted z α hz 7 dot_range7
  · exact rendered_accepted z α hz 8 dot_range8

theorem computeRowAt_eq (z α : K) (i : Fin (cfg z α).compRows) :
    (exec z α).computeRowAt i =
      (renderNode z α (bfsLabelAt (dotTree (K := K)) ((i : ℕ) + 1))).row := by
  have h8 : (cfg z α).compRows = 8 := by simp [cfg]
  have hi : (i : ℕ) < 8 := by
    have := i.isLt
    simp [h8] at this
    exact this
  have hrows := computeRows_eq z α
  have hlt : (i : ℕ) < (exec z α).computeRows.length := by
    have hlen := (exec z α).computeRows_length
    have hltcfg := i.isLt
    omega
  have hget :
      (exec z α).computeRowAt i = (exec z α).computeRows[(i : ℕ)]'hlt := by
    simp [ExactExecution.computeRowAt, List.get_eq_getElem]
  rw [hget]
  have hlt' : (i : ℕ) <
      [(renderNode z α (bfsLabelAt (dotTree (K := K)) 1)).row,
       (renderNode z α (bfsLabelAt (dotTree (K := K)) 2)).row,
       (renderNode z α (bfsLabelAt (dotTree (K := K)) 3)).row,
       (renderNode z α (bfsLabelAt (dotTree (K := K)) 4)).row,
       (renderNode z α (bfsLabelAt (dotTree (K := K)) 5)).row,
       (renderNode z α (bfsLabelAt (dotTree (K := K)) 6)).row,
       (renderNode z α (bfsLabelAt (dotTree (K := K)) 7)).row,
       (renderNode z α (bfsLabelAt (dotTree (K := K)) 8)).row].length := by
    simp; omega
  have hidx := congrArg (fun l : List _ => l[(i : ℕ)]?) hrows
  simp only [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hlt'] at hidx
  have heq := Option.some.inj hidx
  rw [heq]
  interval_cases (i : ℕ) <;> simp

theorem computePubAt_eq (z α : K) (i : Fin (cfg z α).compRows) :
    (exec z α).computePubAt i =
      (renderNode z α (bfsLabelAt (dotTree (K := K)) ((i : ℕ) + 1))).row.2.2.1 := by
  rw [ExactExecution.computePubAt, computeRowAt_eq]

theorem compute_chain (z α : K) :
    ∀ i : Fin (cfg z α).compRows,
      ∀ hi : (i : ℕ) + 1 < (cfg z α).compRows,
        ((exec z α).computePubAt i).ln =
          ((exec z α).computePubAt ⟨(i : ℕ) + 1, hi⟩).ln_prev := by
  intro i hi
  rw [computePubAt_eq, computePubAt_eq]
  exact adjacent_ln z α (i : ℕ) (by
    have h8 : (cfg z α).compRows = 8 := by simp [cfg]
    omega)

theorem compute_wf (z α : K) :
    ∀ i, WF (cfg z α).challenges.computeInputs ((exec z α).computePubAt i) := by
  intro i
  have hch : (cfg z α).challenges.computeInputs = ⟨α, z, 0, 0, 0⟩ := by
    simp [cfg, ChallengeVector.computeInputs]
  rw [computePubAt_eq, hch]
  have hi : ((i : ℕ) + 1) ∈
      List.range' 1 (bfsForest [dotTree (K := K)]).length := by
    have hlen : (bfsForest [dotTree (K := K)]).length = 8 := by
      simp [dot_bfsForest]
    have h8 : (cfg z α).compRows = 8 := by simp [cfg]
    have hlt : (i : ℕ) < 8 := by
      have := i.isLt
      simp [h8] at this
      exact this
    rw [hlen]
    exact List.mem_range'.mpr ⟨(i : ℕ), hlt, by omega⟩
  exact renderNode_wf z α _ (bfsLabelAt_dot_live_state _ hi)

end Nock.NockVMROM.Thm54.TraceGen.DotConfig257

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig769

open Nock Nock.Walk Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

theorem rendered_accepted (z α : K) (hz : z ≠ 0) (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [dotTreeAir (K := K)]).length) :
    ExactExecution.ComputeRowAccepted (cfg z α)
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) i)).row := by
  refine ⟨renderNode_state_agree z α _, ?_, bfsLabelAt_air_Vcomp z α hz i hi⟩
  rw [renderNode_inputs]
  simp [cfg, ChallengeVector.computeInputs]

theorem computeRowsAccepted (z α : K) (hz : z ≠ 0) :
    (exec z α).ComputeRowsAccepted := by
  rw [ExactExecution.computeRowsAccepted_iff, computeRows_eq]
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  have h1 : 1 ∈ List.range' 1 (bfsForest [dotTreeAir (K := K)]).length := by
    simp [dot_air_bfsForest]
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rendered_accepted z α hz 1 h1
  · exact rendered_accepted z α hz 2 dot_air_range2
  · exact rendered_accepted z α hz 3 dot_air_range3
  · exact rendered_accepted z α hz 4 dot_air_range4
  · exact rendered_accepted z α hz 5 dot_air_range5
  · exact rendered_accepted z α hz 6 dot_air_range6
  · exact rendered_accepted z α hz 7 dot_air_range7
  · exact rendered_accepted z α hz 8 dot_air_range8

theorem computeRowAt_eq (z α : K) (i : Fin (cfg z α).compRows) :
    (exec z α).computeRowAt i =
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) ((i : ℕ) + 1))).row := by
  have h8 : (cfg z α).compRows = 8 := by simp [cfg]
  have hi : (i : ℕ) < 8 := by
    have := i.isLt
    simp [h8] at this
    exact this
  have hrows := computeRows_eq z α
  have hlt : (i : ℕ) < (exec z α).computeRows.length := by
    have hlen := (exec z α).computeRows_length
    have hltcfg := i.isLt
    omega
  have hget :
      (exec z α).computeRowAt i = (exec z α).computeRows[(i : ℕ)]'hlt := by
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

theorem computePubAt_eq (z α : K) (i : Fin (cfg z α).compRows) :
    (exec z α).computePubAt i =
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) ((i : ℕ) + 1))).row.2.2.1 := by
  rw [ExactExecution.computePubAt, computeRowAt_eq]

theorem compute_chain (z α : K) :
    ∀ i : Fin (cfg z α).compRows,
      ∀ hi : (i : ℕ) + 1 < (cfg z α).compRows,
        ((exec z α).computePubAt i).ln =
          ((exec z α).computePubAt ⟨(i : ℕ) + 1, hi⟩).ln_prev := by
  intro i hi
  rw [computePubAt_eq, computePubAt_eq]
  exact adjacent_ln_air z α (i : ℕ) (by
    have h8 : (cfg z α).compRows = 8 := by simp [cfg]
    omega)

theorem compute_wf (z α : K) :
    ∀ i, WF (cfg z α).challenges.computeInputs ((exec z α).computePubAt i) := by
  intro i
  have hch : (cfg z α).challenges.computeInputs = ⟨α, z, 0, 0, 0⟩ := by
    simp [cfg, ChallengeVector.computeInputs]
  rw [computePubAt_eq, hch]
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

end Nock.NockVMROM.Thm54.TraceGen.DotConfig769

#print axioms Nock.NockVMROM.Thm54.TraceGen.bfsLabelAt_dot_Vcomp
#print axioms Nock.NockVMROM.Thm54.TraceGen.bfsLabelAt_air_Vcomp
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig257.computeRowsAccepted
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.computeRowsAccepted
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.compute_chain
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.compute_wf
