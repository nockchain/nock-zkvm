/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierAData.lean

  Lift the Tier A OP6/OP2/OP9 program through production `genTraceGeneric`
  (BFS stamps on compute *and* memory) toward an honest commitment.

  Production `genTrace` still builds memory with `genMemForest`, which only
  classifies OP1-arm stars.  This formula is `[6 [ [1 0] [ [2 …] [9 …] ] ]]`,
  so that worker emits the empty forest.  `genTraceGeneric` is the worker
  that inhabits a nonempty served forest from the assigned tree's requests.

  What this module inhabits:

  * `genTraceGeneric` succeeds, and its compute nodes are
    `renderRows (bfsAssign dotTree)`.
  * The committed compute node tree is locally valid:
    `ComputeNodesOK` on `mapNTree GenComputeRow.node` of that render
    (fan-out, stamp/state, `BindComputeRow`, `ComputeTimestampSpecializesAt`).
  * The committed root line-number exponent is `0`.
  * The generated memory forest is nonempty.

  Deferred, and why (not faked): `Data E` requires a
  `BuildableNockExecution` whose `semanticData` /
  `ExactServedMemoryTrace` CORE is not yet assembled for this
  eight-row branch.  `statement_of_generated_residual` further needs
  `Inputs E` with `finrank F K = 3`.  The F97 orbit is at most `2^5 = 32`
  rows (`orderOf` divides `96`); `dotMemForest_exceeds_F97_orbit` shows
  the generated forest is larger (the OP6 branch-pair record alone has
  39 nodes), so `ExactConfig`/`ExactExecution`/`Data` over `ZMod 97` /
  `K3` are not claimed.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierA
import Nock.NockVMROM.Thm54.TraceGen.GenMem

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open ComputeTable

variable {K : Type} [Field K]

variable {lmb : K}

instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-! ## Production `genTrace` misses this formula -/

/-- `genMemForest` has no arm for nested OP6/OP2/OP9, so production `genTrace`
    would commit an empty memory forest. -/
theorem genMemForest_dot (z α : K) :
    genMemForest z α dotFormula dotSubject = [] := by
  simp [genMemForest, dotFormula, dotParentTail, dotBranchPair, dotCondFormula,
    dotThenFormula, dotElseFormula, dotThenTail, dotOp2B, dotOp2C, dotSubject]

/-! ## `genTraceGeneric` on Tier A -/

theorem genTraceGeneric_dot (q Λ : ℕ) (z α : K) (n : ℕ) :
    genTraceGeneric q Λ z α lmb (n + 4) dotSubject dotFormula =
      .ok
        { subject := dotSubject
          formula := dotFormula
          result := dotResult
          fuel := n + 4
          computeNodes := renderRows z α (bfsAssign (dotTree (K := K)))
          memoryNodes :=
            genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTree (K := K))) } := by
  unfold genTraceGeneric
  rw [genComputeSkeleton_dot]

theorem genTraceGeneric_dot_isOk (q Λ : ℕ) (z α : K) (n : ℕ) :
    (genTraceGeneric q Λ z α lmb (n + 4) dotSubject dotFormula).isOk = true := by
  rw [genTraceGeneric_isOk_iff, genComputeSkeleton_dot]
  rfl

/-! ## Committed compute nodes -/

/-- `renderRows` is `mapNTree renderNode`. -/
theorem renderRows_eq_mapNTree (z α : K) :
    ∀ t, renderRows z α t = mapNTree (renderNode z α) t
  | .node _ cs => by
      simp only [renderRows, mapNTree]
      refine congrArg _ ?_
      apply List.map_congr_left
      intro c _
      exact renderRows_eq_mapNTree z α c

theorem mapNTree_comp {α β γ : Type*} (f : β → γ) (g : α → β) :
    ∀ t, mapNTree f (mapNTree g t) = mapNTree (f ∘ g) t
  | .node _ cs => by
      simp only [mapNTree, List.map_map]
      refine congrArg _ ?_
      apply List.map_congr_left
      intro c _
      exact mapNTree_comp f g c

/-- The honest-commitment compute tree of a generated generic trace. -/
def dotComputeNodes (z α : K) : NTree (ComputeNode K) :=
  mapNTree GenComputeRow.node (renderRows z α (bfsAssign (dotTree (K := K))))

theorem genTraceGeneric_dot_computeNodes (q Λ : ℕ) (z α : K) (n : ℕ)
    {G : GenTrace K K}
    (h : genTraceGeneric q Λ z α lmb (n + 4) dotSubject dotFormula = .ok G) :
    mapNTree GenComputeRow.node G.computeNodes = dotComputeNodes z α := by
  rw [genTraceGeneric_dot] at h
  cases h
  rfl

/-! ## Origin ordering of generator stamps -/

/-- Every `stampOfAcc` stamp is ordered from its own line origin: `lnPrevExponent = acc` while
    `lnExponent = acc + recordCount st`.

    The RAP-faithful (relative) `ComputeTimestampSpecializesAt` states
    `ln = ln_prev * α^(lnExponent - lnPrevExponent)`, and `Nat` subtraction truncates, so it needs
    this bound to follow from the absolute `α^e` rendering.  It is not an assumption about
    arbitrary stamps: it is a property of the generator's own assignment. -/
theorem stampOfAcc_lnPrev_le_lnExponent (st : ComputeTable.State) (acc : ℕ) :
    (stampOfAcc st acc).lnPrevExponent ≤ (stampOfAcc st acc).lnExponent := by
  rw [stampOfAcc_lnPrevExponent, stampOfAcc_lnExponent]
  exact Nat.le_add_right _ _

/-- Companion of `stampOfAcc_lnPrev_le_lnExponent` for the record offsets, which `stampOfAcc`
    places at `acc + i + 1` (`stampOfAcc_recordExponent`), hence at or above the line origin for
    every slot -- including the padding slots, where no liveness hypothesis is available. -/
theorem stampOfAcc_lnPrev_le_recordExponent (st : ComputeTable.State) (acc : ℕ) (i : Fin 3) :
    (stampOfAcc st acc).lnPrevExponent ≤ (stampOfAcc st acc).recordExponent i := by
  rw [stampOfAcc_lnPrevExponent]
  cases st <;> simp [stampOfAcc] <;> split_ifs <;> omega

/-! ## Timestamp specialization of rendered rows -/

theorem renderOp1Row_specializes (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) (hstate : stamp.state = State.s1)
    (hln : stamp.lnPrevExponent ≤ stamp.lnExponent)
    (hrec : ∀ i : Fin 3, stamp.lnPrevExponent ≤ stamp.recordExponent i) :
    ComputeTimestampSpecializesAt α stamp (renderOp1Row z α stamp skel) := by
  refine ComputeTimestampSpecializesAt.of_absolute
    ?_ rfl ?_ rfl rfl ?_ ?_ hln hrec
  · simp [renderOp1Row, hstate]
  · simp [renderOp1Row, hstate]
  · intro i
    fin_cases i <;>
      simp [renderOp1Row, computeMemRec, computeMemRecKind, hstate,
        Nock.Framework.recordCount, MemRec.zero]
  · intro i hi
    simp [computeMemRecKind, hstate, Nock.Framework.recordCount] at hi
    fin_cases i <;> simp_all [renderOp1Row, computeMemRec, MemRec.zero]

theorem renderOp2Row_specializes (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) (hstate : stamp.state = State.s2)
    (hln : stamp.lnPrevExponent ≤ stamp.lnExponent)
    (hrec : ∀ i : Fin 3, stamp.lnPrevExponent ≤ stamp.recordExponent i) :
    ComputeTimestampSpecializesAt α stamp (renderOp2Row z α stamp skel) := by
  refine ComputeTimestampSpecializesAt.of_absolute
    ?_ rfl ?_ rfl rfl ?_ ?_ hln hrec
  · simp [renderOp2Row, hstate]
  · simp [renderOp2Row, hstate]
  · intro i
    fin_cases i <;>
      simp [renderOp2Row, computeMemRec, computeMemRecKind, hstate,
        Nock.Framework.recordCount, MemRec.zero]
  · intro i hi
    simp [computeMemRecKind, hstate, Nock.Framework.recordCount] at hi
    fin_cases i <;> simp_all [renderOp2Row, computeMemRec, MemRec.zero]

theorem renderOp6Row_specializes (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) (hstate : stamp.state = State.s6)
    (hln : stamp.lnPrevExponent ≤ stamp.lnExponent)
    (hrec : ∀ i : Fin 3, stamp.lnPrevExponent ≤ stamp.recordExponent i) :
    ComputeTimestampSpecializesAt α stamp (renderOp6Row z α stamp skel) := by
  refine ComputeTimestampSpecializesAt.of_absolute
    ?_ rfl ?_ rfl rfl ?_ ?_ hln hrec
  · simp [renderOp6Row, hstate]
  · simp [renderOp6Row, hstate]
  · intro i
    fin_cases i <;>
      simp [renderOp6Row, computeMemRec, computeMemRecKind, hstate,
        Nock.Framework.recordCount]
  · intro i hi
    simp [computeMemRecKind, hstate, Nock.Framework.recordCount] at hi

theorem renderOp9Row_specializes (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) (hstate : stamp.state = State.s9)
    (hln : stamp.lnPrevExponent ≤ stamp.lnExponent)
    (hrec : ∀ i : Fin 3, stamp.lnPrevExponent ≤ stamp.recordExponent i) :
    ComputeTimestampSpecializesAt α stamp (renderOp9Row z α stamp skel) := by
  refine ComputeTimestampSpecializesAt.of_absolute
    ?_ rfl ?_ rfl rfl ?_ ?_ hln hrec
  · simp [renderOp9Row, hstate]
  · simp [renderOp9Row, hstate]
  · intro i
    fin_cases i <;>
      simp [renderOp9Row, computeMemRec, computeMemRecKind, hstate,
        Nock.Framework.recordCount]
  · intro i hi
    simp [computeMemRecKind, hstate, Nock.Framework.recordCount] at hi

/-! ## Original BFS fan-out equals `fanoutComp` -/

theorem dotTree_bfs_fanout {n : NTree (GenComputeRow K)}
    (hn : n ∈ bfsForest [dotTree (K := K)]) :
    n.children.length = fanoutComp n.label.skel.state := by
  simp [dot_bfsForest] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-! ## Assigned-tree children match `fanoutComp` -/

theorem bfsAssign_dot_recon :
    reconForest 1 (foCol (bfsForest [dotTree (K := K)]))
        (bfsLabelAt (dotTree (K := K))) (bfsForest [dotTree (K := K)]).length =
      [bfsAssign (dotTree (K := K))] := by
  rw [reconForest_one, bfsAssign]

theorem bfsForest_bfsAssign_dot :
    bfsForest [bfsAssign (dotTree (K := K))] =
      (List.range' 1 (bfsForest [dotTree (K := K)]).length).map
        (buildTF 1 (foCol (bfsForest [dotTree (K := K)]))
          (bfsLabelAt (dotTree (K := K)))
          (bfsForest [dotTree (K := K)]).length) := by
  have hne : [dotTree (K := K)] ≠ [] := List.cons_ne_nil _ _
  rw [← bfsAssign_dot_recon, bfsForest_reconForest]
  · exact Nat.le_refl 1
  · exact foCol_Sf_tilingF [dotTree (K := K)] hne
  · exact foCol_BFSValidF [dotTree (K := K)] hne

theorem bfsAssign_dot_children_len {n : NTree (GenComputeRow K)}
    (hn : n ∈ bfsForest [bfsAssign (dotTree (K := K))]) :
    n.children.length = fanoutComp n.label.skel.state := by
  have hne : [dotTree (K := K)] ≠ [] := List.cons_ne_nil _ _
  have hSf := foCol_Sf_tilingF [dotTree (K := K)] hne
  have hvalid := foCol_BFSValidF [dotTree (K := K)] hne
  rw [bfsForest_bfsAssign_dot, List.mem_map] at hn
  obtain ⟨i, hi, rfl⟩ := hn
  obtain ⟨k, hk, hik⟩ := List.mem_range'.mp hi
  have hi1 : 1 ≤ i := by omega
  have hih : i ≤ (bfsForest [dotTree (K := K)]).length := by omega
  have hch :
      (buildTF 1 (foCol (bfsForest [dotTree (K := K)]))
          (bfsLabelAt (dotTree (K := K)))
          (bfsForest [dotTree (K := K)]).length i).children.length =
        foCol (bfsForest [dotTree (K := K)]) i := by
    rw [buildTF_children, childIdxsF_eq (kroots := 1) _ _ hSf hvalid hi1 hih,
      List.length_map, List.length_range']
  rw [hch, buildTF_label]
  have hi' : i - 1 < (bfsForest [dotTree (K := K)]).length := by omega
  have hfo :
      foCol (bfsForest [dotTree (K := K)]) i =
        (bfsForest [dotTree (K := K)])[i - 1].children.length := by
    simp [foCol, List.getElem?_eq_getElem hi']
  rw [hfo]
  have horig : (bfsForest [dotTree (K := K)])[i - 1] ∈
      bfsForest [dotTree (K := K)] := List.getElem_mem hi'
  have hfan := dotTree_bfs_fanout horig
  have hskel :
      (bfsLabelAt (dotTree (K := K)) i).skel =
        (bfsForest [dotTree (K := K)])[i - 1].label.skel := by
    have hr : i - 1 < (bfsRows (dotTree (K := K))).length := by
      simpa [bfsRows_length] using hi'
    rw [bfsLabelAt_skel _ i hr]
    simp [bfsRows]
  rw [hskel]
  exact hfan

/-! ## Bind + specialize on assigned labels -/

theorem bfsLabelAt_dot_state (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length) :
    (bfsLabelAt (dotTree (K := K)) i).stamp.state =
      (bfsLabelAt (dotTree (K := K)) i).skel.state :=
  bfsLabelAt_state _ i (lt_bfsRows_of_mem_range' hi)

theorem renderNode_preserves_skel_stamp (z α : K) (g : GenComputeRow K) :
    (renderNode z α g).skel = g.skel ∧ (renderNode z α g).stamp = g.stamp :=
  ⟨renderNode_op1_skel z α g, renderNode_op1_stamp z α g⟩

theorem dot_bfs_index (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length) :
    i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by
  simp [dot_bfsForest, List.mem_range'] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  interval_cases k <;> simp

theorem bfsLabelAt_dot_skel1 :
    (bfsLabelAt (dotTree (K := K)) 1).skel = dotOp6Skel := by
  have hi : 1 ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length := by
    simp [dot_bfsForest]
  have hi' := lt_bfsRows_of_mem_range' (t := (dotTree (K := K))) hi
  rw [bfsLabelAt_skel (dotTree (K := K)) 1 hi']
  simp [dot_bfsRows]
  rfl

theorem bfsLabelAt_dot_skel2 :
    (bfsLabelAt (dotTree (K := K)) 2).skel = (dotCondTree (K := K)).label.skel := by
  have hi : 2 ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length := by
    simp [dot_bfsForest]
  have hi' := lt_bfsRows_of_mem_range' (t := (dotTree (K := K))) hi
  rw [bfsLabelAt_skel (dotTree (K := K)) 2 hi']
  simp [dot_bfsRows]

theorem bfsLabelAt_dot_skel3 :
    (bfsLabelAt (dotTree (K := K)) 3).skel = dotOp2Skel := by
  have hi : 3 ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length := by
    simp [dot_bfsForest]
  have hi' := lt_bfsRows_of_mem_range' (t := (dotTree (K := K))) hi
  rw [bfsLabelAt_skel (dotTree (K := K)) 3 hi']
  simp [dot_bfsRows]
  rfl

theorem bfsLabelAt_dot_skel4 :
    (bfsLabelAt (dotTree (K := K)) 4).skel = (dotOp1BTree (K := K)).label.skel := by
  have hi : 4 ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length := by
    simp [dot_bfsForest]
  have hi' := lt_bfsRows_of_mem_range' (t := (dotTree (K := K))) hi
  rw [bfsLabelAt_skel (dotTree (K := K)) 4 hi']
  simp [dot_bfsRows]

theorem bfsLabelAt_dot_skel5 :
    (bfsLabelAt (dotTree (K := K)) 5).skel = (dotOp1CTree (K := K)).label.skel := by
  have hi : 5 ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length := by
    simp [dot_bfsForest]
  have hi' := lt_bfsRows_of_mem_range' (t := (dotTree (K := K))) hi
  rw [bfsLabelAt_skel (dotTree (K := K)) 5 hi']
  simp [dot_bfsRows]

theorem bfsLabelAt_dot_skel6 :
    (bfsLabelAt (dotTree (K := K)) 6).skel = dotOp9Skel := by
  have hi : 6 ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length := by
    simp [dot_bfsForest]
  have hi' := lt_bfsRows_of_mem_range' (t := (dotTree (K := K))) hi
  rw [bfsLabelAt_skel (dotTree (K := K)) 6 hi']
  simp [dot_bfsRows]
  rfl

theorem bfsLabelAt_dot_skel7 :
    (bfsLabelAt (dotTree (K := K)) 7).skel = (dotOp9CoreTree (K := K)).label.skel := by
  have hi : 7 ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length := by
    simp [dot_bfsForest]
  have hi' := lt_bfsRows_of_mem_range' (t := (dotTree (K := K))) hi
  rw [bfsLabelAt_skel (dotTree (K := K)) 7 hi']
  simp [dot_bfsRows]

theorem bfsLabelAt_dot_skel8 :
    (bfsLabelAt (dotTree (K := K)) 8).skel = (dotOp9InvokeTree (K := K)).label.skel := by
  have hi : 8 ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length := by
    simp [dot_bfsForest]
  have hi' := lt_bfsRows_of_mem_range' (t := (dotTree (K := K))) hi
  rw [bfsLabelAt_skel (dotTree (K := K)) 8 hi']
  simp [dot_bfsRows]

theorem dot_op1_leaf_bind (z α : K) (subject formula result : Noun)
    (stamp : ComputeTimestampRow)
    (hhead : formulaHead formula = .atom 1) :
    BindComputeRow z (genSkelOp1 subject formula result (.atom 1))
      (renderOp1Row z α stamp (genSkelOp1 subject formula result (.atom 1))) :=
  genSkelOp1_bindCompute z α subject formula result (.atom 1) stamp hhead

theorem bfsLabelAt_dot_bind (z α : K) (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length) :
    BindComputeRow z (bfsLabelAt (dotTree (K := K)) i).skel
      (renderNode z α (bfsLabelAt (dotTree (K := K)) i)).row := by
  rcases dot_bfs_index i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hskel := bfsLabelAt_dot_skel1 (K := K)
    have hstate : (bfsLabelAt (dotTree (K := K)) 1).skel.state = State.s6 := by
      rw [hskel]; rfl
    rw [renderNode_op6_row z α _ hstate, hskel]
    refine genSkelOp6_bindCompute z α _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp [formulaHead, formulaTail, dotFormula, dotParentTail,
      dotBranchPair, dotCondFormula, dotThenFormula, dotElseFormula]
  · have hskel := bfsLabelAt_dot_skel2 (K := K)
    have hstate : (bfsLabelAt (dotTree (K := K)) 2).skel.state = State.s1 := by
      rw [hskel]; rfl
    rw [renderNode_op1_row z α _ hstate, hskel]
    simp [dotCondTree, skelNode]
    exact dot_op1_leaf_bind z α _ _ _ _ (by simp [formulaHead, dotCondFormula])
  · have hskel := bfsLabelAt_dot_skel3 (K := K)
    have hstate : (bfsLabelAt (dotTree (K := K)) 3).skel.state = State.s2 := by
      rw [hskel]; rfl
    rw [renderNode_op2_row z α _ hstate, hskel]
    refine genSkelOp2_bindCompute z α _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
    all_goals simp [formulaHead, formulaTail, dotThenFormula, dotThenTail,
      dotOp2B, dotOp2C]
  · have hskel := bfsLabelAt_dot_skel4 (K := K)
    have hstate : (bfsLabelAt (dotTree (K := K)) 4).skel.state = State.s1 := by
      rw [hskel]; rfl
    rw [renderNode_op1_row z α _ hstate, hskel]
    simp [dotOp1BTree, skelNode]
    exact dot_op1_leaf_bind z α _ _ _ _ (by simp [formulaHead, dotOp2B])
  · have hskel := bfsLabelAt_dot_skel5 (K := K)
    have hstate : (bfsLabelAt (dotTree (K := K)) 5).skel.state = State.s1 := by
      rw [hskel]; rfl
    rw [renderNode_op1_row z α _ hstate, hskel]
    simp [dotOp1CTree, skelNode]
    exact dot_op1_leaf_bind z α _ _ _ _ (by simp [formulaHead, dotOp2C])
  · have hskel := bfsLabelAt_dot_skel6 (K := K)
    have hstate : (bfsLabelAt (dotTree (K := K)) 6).skel.state = State.s9 := by
      rw [hskel]; rfl
    rw [renderNode_op9_row z α _ hstate, hskel]
    refine genSkelOp9_bindCompute z α _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
    all_goals simp [formulaHead, formulaTail, dotOp9Formula, dotOp9Tail,
      dotCoreFormula]
  · have hskel := bfsLabelAt_dot_skel7 (K := K)
    have hstate : (bfsLabelAt (dotTree (K := K)) 7).skel.state = State.s1 := by
      rw [hskel]; rfl
    rw [renderNode_op1_row z α _ hstate, hskel]
    simp [dotOp9CoreTree, skelNode]
    exact dot_op1_leaf_bind z α _ _ _ _ (by simp [formulaHead, dotCoreFormula])
  · have hskel := bfsLabelAt_dot_skel8 (K := K)
    have hstate : (bfsLabelAt (dotTree (K := K)) 8).skel.state = State.s1 := by
      rw [hskel]; rfl
    rw [renderNode_op1_row z α _ hstate, hskel]
    simp [dotOp9InvokeTree, skelNode]
    exact dot_op1_leaf_bind z α _ _ _ _ (by simp [formulaHead, dotArm, dotElem0])

theorem bfsLabelAt_dot_specializes (z α : K) (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length) :
    ComputeTimestampSpecializesAt α (bfsLabelAt (dotTree (K := K)) i).stamp
      (renderNode z α (bfsLabelAt (dotTree (K := K)) i)).row := by
  have hst := bfsLabelAt_dot_state i hi
  have hln : (bfsLabelAt (dotTree (K := K)) i).stamp.lnPrevExponent ≤
      (bfsLabelAt (dotTree (K := K)) i).stamp.lnExponent := by
    rw [bfsLabelAt_stamp (dotTree (K := K)) i (lt_bfsRows_of_mem_range' hi)]
    exact stampOfAcc_lnPrev_le_lnExponent _ _
  have hrec : ∀ j : Fin 3,
      (bfsLabelAt (dotTree (K := K)) i).stamp.lnPrevExponent ≤
        (bfsLabelAt (dotTree (K := K)) i).stamp.recordExponent j := fun j => by
    rw [bfsLabelAt_stamp (dotTree (K := K)) i (lt_bfsRows_of_mem_range' hi)]
    exact stampOfAcc_lnPrev_le_recordExponent _ _ j
  rcases dot_bfs_index i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hstate : (bfsLabelAt (dotTree (K := K)) 1).skel.state = State.s6 := by
      rw [bfsLabelAt_dot_skel1]; rfl
    rw [renderNode_op6_row z α _ hstate]
    exact renderOp6Row_specializes z α _ _ (hst.trans hstate) hln hrec
  · have hstate : (bfsLabelAt (dotTree (K := K)) 2).skel.state = State.s1 := by
      rw [bfsLabelAt_dot_skel2]; rfl
    rw [renderNode_op1_row z α _ hstate]
    exact renderOp1Row_specializes z α _ _ (hst.trans hstate) hln hrec
  · have hstate : (bfsLabelAt (dotTree (K := K)) 3).skel.state = State.s2 := by
      rw [bfsLabelAt_dot_skel3]; rfl
    rw [renderNode_op2_row z α _ hstate]
    exact renderOp2Row_specializes z α _ _ (hst.trans hstate) hln hrec
  · have hstate : (bfsLabelAt (dotTree (K := K)) 4).skel.state = State.s1 := by
      rw [bfsLabelAt_dot_skel4]; rfl
    rw [renderNode_op1_row z α _ hstate]
    exact renderOp1Row_specializes z α _ _ (hst.trans hstate) hln hrec
  · have hstate : (bfsLabelAt (dotTree (K := K)) 5).skel.state = State.s1 := by
      rw [bfsLabelAt_dot_skel5]; rfl
    rw [renderNode_op1_row z α _ hstate]
    exact renderOp1Row_specializes z α _ _ (hst.trans hstate) hln hrec
  · have hstate : (bfsLabelAt (dotTree (K := K)) 6).skel.state = State.s9 := by
      rw [bfsLabelAt_dot_skel6]; rfl
    rw [renderNode_op9_row z α _ hstate]
    exact renderOp9Row_specializes z α _ _ (hst.trans hstate) hln hrec
  · have hstate : (bfsLabelAt (dotTree (K := K)) 7).skel.state = State.s1 := by
      rw [bfsLabelAt_dot_skel7]; rfl
    rw [renderNode_op1_row z α _ hstate]
    exact renderOp1Row_specializes z α _ _ (hst.trans hstate) hln hrec
  · have hstate : (bfsLabelAt (dotTree (K := K)) 8).skel.state = State.s1 := by
      rw [bfsLabelAt_dot_skel8]; rfl
    rw [renderNode_op1_row z α _ hstate]
    exact renderOp1Row_specializes z α _ _ (hst.trans hstate) hln hrec

/-! ## `ComputeNodesOK` -/

theorem dotComputeNodes_bfsForest (z α : K) :
    bfsForest [dotComputeNodes z α] =
      (bfsForest [bfsAssign (dotTree (K := K))]).map
        (fun n => mapNTree GenComputeRow.node (renderRows z α n)) := by
  simp only [dotComputeNodes, renderRows_eq_mapNTree, mapNTree_comp]
  rw [show [mapNTree (GenComputeRow.node ∘ renderNode z α)
        (bfsAssign (dotTree (K := K)))] =
      [bfsAssign (dotTree (K := K))].map
        (mapNTree (GenComputeRow.node ∘ renderNode z α)) from rfl]
  rw [bfsForest_mapNTree]

theorem dotComputeNodes_OK (z α : K) :
    ComputeNodesOK z α (dotComputeNodes z α) := by
  intro t ht
  have hmem : t ∈ bfsForest [dotComputeNodes z α] :=
    (mem_bfsForest [dotComputeNodes z α] t).mpr
      ⟨dotComputeNodes z α, List.mem_singleton.mpr rfl, ht⟩
  rw [dotComputeNodes_bfsForest, bfsForest_bfsAssign_dot, List.mem_map] at hmem
  obtain ⟨n, hn, rfl⟩ := hmem
  rw [List.mem_map] at hn
  obtain ⟨j, hj, rfl⟩ := hn
  have hnmem :
      buildTF 1 (foCol (bfsForest [dotTree (K := K)]))
          (bfsLabelAt (dotTree (K := K)))
          (bfsForest [dotTree (K := K)]).length j ∈
        bfsForest [bfsAssign (dotTree (K := K))] := by
    rw [bfsForest_bfsAssign_dot]
    exact List.mem_map.mpr ⟨j, hj, rfl⟩
  have hch := bfsAssign_dot_children_len hnmem
  have hnode :
      (mapNTree GenComputeRow.node
          (renderRows z α
            (buildTF 1 (foCol (bfsForest [dotTree (K := K)]))
              (bfsLabelAt (dotTree (K := K)))
              (bfsForest [dotTree (K := K)]).length j))).label =
        (renderNode z α (bfsLabelAt (dotTree (K := K)) j)).node := by
    simp [renderRows_eq_mapNTree, mapNTree_label, buildTF_label, GenComputeRow.node]
  refine ⟨?flen, ?fstamp, ?fbind, ?ftime⟩
  · rw [mapNTree_children, renderRows_eq_mapNTree, mapNTree_children,
      List.length_map, List.length_map, hch]
    simp [buildTF_label, mapNTree_label,
      GenComputeRow.node, renderNode_op1_skel]
  · rw [hnode]
    simp [GenComputeRow.node, renderNode_op1_skel, renderNode_op1_stamp]
    exact bfsLabelAt_dot_state j hj
  · rw [hnode]
    simp [GenComputeRow.node, renderNode_op1_skel]
    exact bfsLabelAt_dot_bind z α j hj
  · rw [hnode]
    simp [GenComputeRow.node, renderNode_op1_stamp]
    exact bfsLabelAt_dot_specializes z α j hj

/-! ## Root line exponent -/

theorem accAt_zero (t : NTree (GenComputeRow K)) : accAt t 0 = 0 :=
  rfl

theorem dotComputeNodes_root_line_exponent (z α : K) :
    (dotComputeNodes z α).label.stamp.lnPrevExponent = 0 := by
  simp [dotComputeNodes, renderRows_eq_mapNTree, mapNTree_label,
    renderNode_op1_stamp, GenComputeRow.node, bfsAssign_label]
  have hi : 1 ∈ List.range' 1 (bfsForest [dotTree (K := K)]).length := by
    simp [dot_bfsForest]
  rw [bfsLabelAt_lnPrev (dotTree (K := K)) 1 (lt_bfsRows_of_mem_range' hi)]
  exact accAt_zero _

/-! ## Generated memory forest is nonempty -/
theorem bfsAssign_dot_root_requests :
    (bfsAssign (dotTree (K := K))).label.requests =
      (dotTree (K := K)).label.requests := by
  rw [bfsAssign_label]
  have hi : 1 - 1 < (bfsRows (dotTree (K := K))).length := by
    simp [dot_bfsRows]
  rw [bfsLabelAt_eq _ 1 hi]
  simp [dot_bfsRows]

theorem extractNodeReqs_dot_root_length :
    (extractNodeReqs (bfsAssign (dotTree (K := K))).label).length = 3 := by
  rw [extractNodeReqs, bfsAssign_dot_root_requests]
  simp [dotTree, skelNode, extractNodeReqsAux]

theorem append_eq_nil {α} {l₁ l₂ : List α} : l₁ ++ l₂ = [] ↔ l₁ = [] ∧ l₂ = [] := by
  cases l₁ <;> cases l₂ <;> simp

theorem genRowMemForest_three_ne (E : Noun → ComputeTable.FP K) (z α : K)
    (r1 r2 r3 : MemRecordReq) :
    genRowMemForest E z α lmb [r1, r2, r3] ≠ [] := by
  simp only [genRowMemForest]
  intro h
  exact List.cons_ne_nil _ _ (append_eq_nil.mp h).2

theorem genRowMemForest_dot_root_ne (E : Noun → ComputeTable.FP K) (z α : K) :
    genRowMemForest E z α lmb
        (extractNodeReqs (bfsAssign (dotTree (K := K))).label) ≠ [] := by
  have hlen := extractNodeReqs_dot_root_length (K := K)
  cases hreqs : extractNodeReqs (bfsAssign (dotTree (K := K))).label with
  | nil => simp [hreqs] at hlen
  | cons r1 rs1 =>
    cases rs1 with
    | nil => simp [hreqs] at hlen
    | cons r2 rs2 =>
      cases rs2 with
      | nil => simp [hreqs] at hlen
      | cons r3 rs3 =>
        cases rs3 with
        | nil =>
          exact genRowMemForest_three_ne E z α r1 r2 r3
        | cons _ _ => simp [hreqs, List.length_cons] at hlen

theorem dotMemForest_nonempty (z α : K) :
    genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTree (K := K))) ≠ [] := by
  have hshape :
      bfsAssign (dotTree (K := K)) =
        NTree.node (bfsAssign (dotTree (K := K))).label
          (bfsAssign (dotTree (K := K))).children := by
    cases bfsAssign (dotTree (K := K)); rfl
  rw [hshape, genMemForestFromTree]
  intro h
  exact genRowMemForest_dot_root_ne (encC z) z α (append_eq_nil.mp h).1

/-! ## Concrete F97 inhabitant -/

def seedZ : ZMod 97 := 8
def alphaA : ZMod 97 := 4

theorem seedZ_ne_zero : seedZ ≠ 0 := by decide

/-- The generator's own emitted Tier A trace at the OP1 slice's sample. -/
noncomputable def dotGenTrace : GenTrace (ZMod 97) (ZMod 97) :=
  { subject := dotSubject
    formula := dotFormula
    result := dotResult
    fuel := 4
    computeNodes := renderRows seedZ alphaA (bfsAssign (dotTree (K := ZMod 97)))
    memoryNodes :=
      genMemForestFromTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault
        (bfsAssign (dotTree (K := ZMod 97))) }

theorem dotGenTrace_is_generated :
    genTraceGeneric 97 3 seedZ alphaA MemoryTable.formRDefault 4 dotSubject dotFormula = .ok dotGenTrace :=
  genTraceGeneric_dot 97 3 seedZ alphaA 0

theorem dotGenTrace_computeOK :
    ComputeNodesOK seedZ alphaA
      (mapNTree GenComputeRow.node dotGenTrace.computeNodes) := by
  simpa [dotGenTrace, dotComputeNodes] using
    (dotComputeNodes_OK (K := ZMod 97) seedZ alphaA)

theorem dotGenTrace_root_line_exponent :
    (mapNTree GenComputeRow.node dotGenTrace.computeNodes).label.stamp.lnPrevExponent
      = 0 := by
  simpa [dotGenTrace, dotComputeNodes] using
    (dotComputeNodes_root_line_exponent (K := ZMod 97) seedZ alphaA)

theorem dotGenTrace_memory_nonempty : dotGenTrace.memoryNodes ≠ [] :=
  dotMemForest_nonempty (K := ZMod 97) seedZ alphaA

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genTraceGeneric_dot
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotComputeNodes_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotComputeNodes_root_line_exponent
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotMemForest_nonempty
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotGenTrace_is_generated
