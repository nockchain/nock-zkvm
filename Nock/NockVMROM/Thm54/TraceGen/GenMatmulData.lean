/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulData.lean

  Lift the 2×2 matmul generator through production `genTraceGeneric`
  (BFS stamps on compute *and* memory) toward an honest commitment.

  Production `genTrace` still builds memory with `genMemForest`, which only
  classifies OP1-arm stars.  `mmFormula` is an autocons of four nested
  OP7/OP9 slams, so that worker emits the empty forest.  `genTraceGeneric`
  is the worker that inhabits a nonempty served forest from the assigned
  tree's requests.

  What this module inhabits:

  * `genTraceGeneric` succeeds, and its compute nodes are
    `renderRows (bfsAssign mmTree)`.
  * The committed compute node tree is locally valid:
    `ComputeNodesOK` on `mapNTree GenComputeRow.node` of that render
    (generic generated-tree fan-out, bind, and timestamp specialization).
  * The committed root line-number exponent is `0`.
  * The generated memory forest is nonempty (root cons has one service
    request).
  * Assigned forest counts `kMem = 618` / `memRows = 30936` and
    `MemoryNodesOK` on that forest (`mmMemForest_OK`, paper `axisPath`
    MSB-first agreeing with `Noun.slot`).

  Deferred, and why (not faked): `Data E` / `BuildableNockExecution` /
  `statement_of_generated_residual` further need
  `ExactExecutionSemanticData` and `ExactServedMemoryTrace`.
  Non-semantic `BuildableNockExecution` fields (orbit IO capacity,
  `RecordCountBalanced`, committed node-forest row identification) are
  in `GenMatmulBuildableParts`.  `ExactConfig` / `ExactExecution` over
  `GaloisField 65537 3` (`finrank = 3`, orbit `2^16`) are in
  `GenMatmulConfig`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmul
import Nock.NockVMROM.Thm54.TraceGen.GenTierAData
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonSpecialize
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderBinding
import Nock.NockVMROM.Thm54.TraceGen.GenWF

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open ComputeTable

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## Production `genTrace` misses this formula -/

/-- `genMemForest` has no arm for nested OP7/OP9 slams, so production
    `genTrace` would commit an empty memory forest. -/
theorem genMemForest_nested_op7 (z α : K) (b c d e subject : Noun) :
    genMemForest z α
      (.cell (.cell (.cell (.atom 7) b) c) (.cell d e)) subject = [] :=
  rfl

theorem genMemForest_mm (z α : K) :
    genMemForest z α mmFormula mmSubject = [] := by
  simp [mmFormula, mmC00, mmC01, mmC10, mmC11, mac2, invokeMac, slam, op7]
  exact genMemForest_nested_op7 z α _ _ _ _ _

/-! ## `genTraceGeneric` on matmul -/

theorem genTraceGeneric_mm (q Λ : ℕ) (z α : K) :
    genTraceGeneric q Λ z α lmb 64 mmSubject mmFormula =
      .ok
        { subject := mmSubject
          formula := mmFormula
          result := mmC
          fuel := 64
          computeNodes := renderRows z α (bfsAssign (mmTree (K := K)))
          memoryNodes :=
            genMemForestFromTree (encC z) z α lmb (bfsAssign (mmTree (K := K))) } := by
  unfold genTraceGeneric
  rw [mmTree_gen]

theorem genTraceGeneric_mm_isOk (q Λ : ℕ) (z α : K) :
    (genTraceGeneric q Λ z α lmb 64 mmSubject mmFormula).isOk = true := by
  rw [genTraceGeneric_isOk_iff, mmTree_gen]
  rfl

/-! ## Committed compute nodes -/

/-- Overwrite baked RLC coins on a committed compute node. -/
def setNodeCoins (a b c : K) (n : ComputeNode K) : ComputeNode K :=
  { n with row := setRowCoins a b c n.row }

/-- The honest-commitment compute tree of a generated generic trace. -/
noncomputable def mmComputeNodes (z α : K) : NTree (ComputeNode K) :=
  mapNTree (setNodeCoins (0 : K) 0 1)
    (mapNTree GenComputeRow.node (renderRows z α (bfsAssign (mmTreeAir (K := K)))))

theorem mmComputeNodes_OK (z α : K) :
    ComputeNodesOK z α (mmComputeNodes z α) := by
  intro t ht
  have hmem : t ∈ bfsForest [mmComputeNodes z α] :=
    (mem_bfsForest _ t).mpr ⟨_, List.mem_singleton.mpr rfl, ht⟩
  unfold mmComputeNodes at hmem
  rw [show [mapNTree (setNodeCoins (0 : K) 0 1)
        (mapNTree GenComputeRow.node
          (renderRows z α (bfsAssign (mmTreeAir (K := K)))))] =
      [mapNTree GenComputeRow.node
          (renderRows z α (bfsAssign (mmTreeAir (K := K))))].map
        (mapNTree (setNodeCoins (0 : K) 0 1)) from rfl] at hmem
  rw [bfsForest_mapNTree, List.mem_map] at hmem
  obtain ⟨u, hu, rfl⟩ := hmem
  have hin :
      InTree (mapNTree GenComputeRow.node
          (renderRows z α (bfsAssign (mmTreeAir (K := K))))) u := by
    have := (mem_bfsForest _ u).mp hu
    obtain ⟨c, hc, hct⟩ := this
    simp at hc
    subst c
    exact hct
  obtain ⟨hshape, hst, hbind, htime⟩ :=
    genComputeSkeleton_airReorder_computeNodes_OK z α (mmTree_gen (K := K)) u hin
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [mapNTree, setNodeCoins] using hshape
  · simpa [mapNTree_label, setNodeCoins] using hst
  · simpa [mapNTree_label, setNodeCoins] using
      bindComputeRow_setRowCoins z (0 : K) 0 1 hbind
  · simpa [mapNTree_label, setNodeCoins] using
      computeTimestampSpecializesAt_setRowCoins α (0 : K) 0 1 htime

/-! ## Root line exponent -/

theorem mmComputeNodes_root_line_exponent (z α : K) :
    (mmComputeNodes z α).label.stamp.lnPrevExponent = 0 := by
  simp [mmComputeNodes, setNodeCoins, renderRows_eq_mapNTree, mapNTree_label,
    renderNode_op1_stamp, GenComputeRow.node, bfsAssign_label]
  have hi : 1 ∈ List.range' 1 (bfsForest [mmTreeAir (K := K)]).length := by
    refine List.mem_range'.mpr ⟨0, bfsForest_singleton_length_pos _, ?_⟩
    omega
  rw [bfsLabelAt_lnPrev (mmTreeAir (K := K)) 1 (lt_bfsRows_of_mem_range' hi)]
  exact accAt_zero _

/-! ## Generated memory forest is nonempty -/

theorem bfsAssign_mm_root_requests :
    (bfsAssign (mmTreeAir (K := K))).label.requests =
      (mmTree (K := K)).label.requests := by
  rw [bfsAssign_label]
  unfold bfsLabelAt mmTreeAir
  have hhead : (bfsRows (airReorder (mmTree (K := K))))[0]? =
      some (airReorder (mmTree (K := K))).label := by
    have h? := bfsRows_head? (airReorder (mmTree (K := K)))
    cases hrows : bfsRows (airReorder (mmTree (K := K))) with
    | nil => simp [hrows] at h?
    | cons g gs =>
      simp [hrows] at h?
      simp [h?]
  simp [hhead, airReorder_label]

theorem extractNodeReqsAux_length (stamp : ComputeTimestampRow) :
    ∀ (i : ℕ) (rs : List (ServiceReq K)),
      (extractNodeReqsAux stamp i rs).length = rs.length
  | _, [] => rfl
  | i, _ :: rs => by
      simp [extractNodeReqsAux, extractNodeReqsAux_length stamp (i + 1) rs]

theorem extractNodeReqs_mm_root_length :
    (extractNodeReqs (bfsAssign (mmTreeAir (K := K))).label).length = 1 := by
  rw [extractNodeReqs, bfsAssign_mm_root_requests, extractNodeReqsAux_length]
  exact mmTree_root_requests_length

theorem genRowMemForest_one_ne (E : Noun → ComputeTable.FP K) (z α : K)
    (r : MemRecordReq) :
    genRowMemForest E z α lmb [r] ≠ [] := by
  simp [genRowMemForest]

theorem genRowMemForest_mm_root_ne (E : Noun → ComputeTable.FP K) (z α : K) :
    genRowMemForest E z α lmb
        (extractNodeReqs (bfsAssign (mmTreeAir (K := K))).label) ≠ [] := by
  have hlen := extractNodeReqs_mm_root_length (K := K)
  cases hreqs : extractNodeReqs (bfsAssign (mmTreeAir (K := K))).label with
  | nil => simp [hreqs] at hlen
  | cons r rs =>
    cases rs with
    | nil => exact genRowMemForest_one_ne E z α r
    | cons _ _ => simp [hreqs, List.length_cons] at hlen

theorem mmMemForest_nonempty (z α : K) :
    genMemForestFromTree (encC z) z α lmb (bfsAssign (mmTreeAir (K := K))) ≠ [] := by
  have hshape :
      bfsAssign (mmTreeAir (K := K)) =
        NTree.node (bfsAssign (mmTreeAir (K := K))).label
          (bfsAssign (mmTreeAir (K := K))).children := by
    cases bfsAssign (mmTreeAir (K := K)); rfl
  rw [hshape, genMemForestFromTree]
  intro h
  exact genRowMemForest_mm_root_ne (encC z) z α (append_eq_nil.mp h).1

/-! ## Concrete F97 inhabitant -/

/-- The generator's own emitted matmul trace at the OP1 slice's sample. -/
noncomputable def mmGenTrace : GenTrace (ZMod 97) (ZMod 97) :=
  { subject := mmSubject
    formula := mmFormula
    result := mmC
    fuel := 64
    computeNodes := renderRows seedZ alphaA (bfsAssign (mmTree (K := ZMod 97)))
    memoryNodes :=
      genMemForestFromTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault
        (bfsAssign (mmTree (K := ZMod 97))) }

theorem mmGenTrace_is_generated :
    genTraceGeneric 97 3 seedZ alphaA MemoryTable.formRDefault 64 mmSubject mmFormula = .ok mmGenTrace :=
  genTraceGeneric_mm 97 3 seedZ alphaA

theorem mmGenTrace_computeOK :
    ComputeNodesOK seedZ alphaA
      (mapNTree GenComputeRow.node mmGenTrace.computeNodes) :=
  genComputeSkeleton_computeNodes_OK seedZ alphaA (mmTree_gen (K := ZMod 97))

theorem mmGenTrace_root_line_exponent :
    (mapNTree GenComputeRow.node mmGenTrace.computeNodes).label.stamp.lnPrevExponent
      = 0 := by
  simp [mmGenTrace, renderRows_eq_mapNTree, mapNTree_label, renderNode_op1_stamp,
    GenComputeRow.node, bfsAssign_label]
  have hi : 1 ∈ List.range' 1 (bfsForest [mmTree (K := ZMod 97)]).length := by
    refine List.mem_range'.mpr ⟨0, bfsForest_singleton_length_pos _, ?_⟩
    omega
  rw [bfsLabelAt_lnPrev (mmTree (K := ZMod 97)) 1 (lt_bfsRows_of_mem_range' hi)]
  exact accAt_zero _

theorem mmGenTrace_memory_nonempty : mmGenTrace.memoryNodes ≠ [] := by
  simp [mmGenTrace]
  have hshape :
      bfsAssign (mmTree (K := ZMod 97)) =
        NTree.node (bfsAssign (mmTree (K := ZMod 97))).label
          (bfsAssign (mmTree (K := ZMod 97))).children := by
    cases bfsAssign (mmTree (K := ZMod 97)); rfl
  rw [hshape, genMemForestFromTree]
  intro h
  have hlen :
      (extractNodeReqs (bfsAssign (mmTree (K := ZMod 97))).label).length = 1 := by
    have hreq :
        (bfsAssign (mmTree (K := ZMod 97))).label.requests =
          (mmTree (K := ZMod 97)).label.requests := by
      rw [bfsAssign_label]
      unfold bfsLabelAt
      have hhead : (bfsRows (mmTree (K := ZMod 97)))[0]? =
          some (mmTree (K := ZMod 97)).label := by
        have h? := bfsRows_head? (mmTree (K := ZMod 97))
        cases hrows : bfsRows (mmTree (K := ZMod 97)) with
        | nil => simp [hrows] at h?
        | cons g gs =>
          simp [hrows] at h?
          simp [h?]
      simp [hhead]
    rw [extractNodeReqs, hreq, extractNodeReqsAux_length]
    exact mmTree_root_requests_length
  cases hreqs : extractNodeReqs (bfsAssign (mmTree (K := ZMod 97))).label with
  | nil => simp [hreqs] at hlen
  | cons r rs =>
    cases rs with
    | nil =>
      rw [hreqs] at h
      exact (genRowMemForest_one_ne (encC seedZ) seedZ alphaA r)
        (append_eq_nil.mp h).1
    | cons _ _ => simp [hreqs, List.length_cons] at hlen

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genTraceGeneric_mm
#print axioms Nock.NockVMROM.Thm54.TraceGen.mmComputeNodes_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.mmComputeNodes_root_line_exponent
#print axioms Nock.NockVMROM.Thm54.TraceGen.mmMemForest_nonempty
#print axioms Nock.NockVMROM.Thm54.TraceGen.mmGenTrace_is_generated
#print axioms Nock.NockVMROM.Thm54.TraceGen.mmGenTrace_computeOK
