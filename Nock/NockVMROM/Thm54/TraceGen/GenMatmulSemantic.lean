/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulSemantic.lean

  Timestamp skeleton and `TimestampSpecializesAt` for the threaded F65537
  matmul carrier.  Memory stamp/state agreement is `MemoryNodesOK`; compute
  and memory timestamp equations are the BFS stamps of `bfsAssign mmTree`
  against the overwritten compute rows and LogUp-threaded memory rows.
  Bridge equations are the generic semantic-slot theorems.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulBinds
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulNodup
import Nock.NockVMROM.Thm54.TraceGen.BFSAssign
import Nock.NockVMROM.Thm54.SemanticTimestampStrategy
import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticLmIO

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

open Nock Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.RowLayout

noncomputable section

theorem assignedForest_memoryStampsWellFormed (z α : K) :
    ∀ root ∈ assignedForest z α, memoryStampsWellFormed root := by
  intro root hroot
  exact memoryStampsWellFormed_of_nodesOK root (mmMemForest_OK z α root hroot)

noncomputable def timestampSkeleton (z α : K) :
    SemanticTimestampSkeleton F K (semanticSkeleton z α) :=
  genTimestampSkeleton F (mmTreeAir (K := K)) (assignedForest z α)
    (assignedForest_memoryStampsWellFormed z α)

theorem timestampSkeleton_computeRows (z α : K) :
    (timestampSkeleton z α).computeRows =
      bfsStamps (bfsAssign (mmTreeAir (K := K))) :=
  rfl

theorem timestampSkeleton_memoryRows (z α : K) :
    (timestampSkeleton z α).memoryRows =
      genMemoryStamps (assignedForest z α) :=
  rfl

theorem assigned_bfs_memoryTimestamp (z α : K) :
    ∀ t ∈ bfsForest (assignedForest z α),
      MemoryTimestampSpecializesAt α t.label.stamp t.label.row := by
  intro t ht
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ t).mp ht
  exact inTree_memoryTimestamp z α (mmMemForest_OK z α u hu) hin

theorem computeRows_eq_overwritten (z α : K) :
    (execThreaded z α).computeRows =
      (bfsForest [bfsAssign (mmTreeAir (K := K))]).map
        (fun n => setRowCoins (0 : K) 0 1
          (renderNode z α n.label).row) := by
  change (bfsForest [(execThreaded z α).computeTree]).map NTree.label = _
  have htree : (execThreaded z α).computeTree = computeTree z α := rfl
  rw [htree]
  unfold computeTree
  rw [renderRows_eq_mapNTree, mapNTree_comp]
  rw [show [mapNTree ((fun g : GenComputeRow K =>
        setRowCoins (0 : K) 0 1 g.row) ∘ renderNode z α)
      (bfsAssign (mmTreeAir (K := K)))] =
      [bfsAssign (mmTreeAir (K := K))].map
        (mapNTree ((fun g => setRowCoins (0 : K) 0 1 g.row) ∘ renderNode z α))
    from rfl]
  rw [bfsForest_mapNTree, List.map_map]
  refine List.map_congr_left fun n _ => ?_
  simp [Function.comp, mapNTree_label]

theorem compute_timestamps (z α : K) :
    List.Forall₂ (ComputeTimestampSpecializesAt α)
      (timestampSkeleton z α).computeRows
      (execThreaded z α).computeRows := by
  rw [timestampSkeleton_computeRows, computeRows_eq_overwritten]
  unfold bfsStamps
  rw [forall2_map_map_iff]
  intro n hn
  have hmem : n.label ∈
      (bfsForest [bfsAssign (mmTreeAir (K := K))]).map NTree.label :=
    List.mem_map.mpr ⟨n, hn, rfl⟩
  rw [bfsAssign_bfsForest_labels, List.mem_map] at hmem
  obtain ⟨i, hi, hni⟩ := hmem
  have hi' := lt_bfsRows_of_mem_range' hi
  have hst : n.label.stamp.state = n.label.skel.state := by
    rw [← hni]
    exact bfsLabelAt_state (mmTreeAir (K := K)) i hi'
  have hln : n.label.stamp.lnPrevExponent ≤ n.label.stamp.lnExponent := by
    rw [← hni, bfsLabelAt_stamp (mmTreeAir (K := K)) i hi']
    exact stampOfAcc_lnPrev_le_lnExponent _ _
  have hrec : ∀ j : Fin 3,
      n.label.stamp.lnPrevExponent ≤ n.label.stamp.recordExponent j := fun j => by
    rw [← hni, bfsLabelAt_stamp (mmTreeAir (K := K)) i hi']
    exact stampOfAcc_lnPrev_le_recordExponent _ _ j
  exact computeTimestampSpecializesAt_setRowCoins α 0 0 1
    (renderNode_specializes z α n.label hst hln hrec)

theorem memoryRowsA_eq_threadGenRows (z α : K) :
    (execThreadedA z α).memoryRows =
      (threadGenRows (memInputs z) 0
        ((bfsForest (assignedForest z α)).map NTree.label)).map
        GenMemoryRow.row := by
  rw [memoryRowsA_eq_threaded]
  unfold threadedForest
  rw [threadGenForest_bfs_labels]

/-- The executed rows are the row encode of the generated threaded rows. -/
theorem memoryRows_eq_threadGenRows (z α : K) :
    (execThreaded z α).memoryRows =
      ((threadGenRows (memInputs z) 0
        ((bfsForest (assignedForest z α)).map NTree.label)).map
        GenMemoryRow.row).map (MemoryRowTemplate.encodeRow MemoryTable.formRDefault) := by
  rw [execThreaded, ExactExecution.encodeMem_memoryRows, memoryRowsA_eq_threadGenRows]
  rfl

theorem memory_timestampsA (z α : K) :
    List.Forall₂ (MemoryTimestampSpecializesAt α)
      (timestampSkeleton z α).memoryRows
      ((threadGenRows (memInputs z) 0
        ((bfsForest (assignedForest z α)).map NTree.label)).map
        GenMemoryRow.row) := by
  rw [timestampSkeleton_memoryRows]
  unfold genMemoryStamps
  have hstamps :
      (bfsForest (assignedForest z α)).map (fun n => n.label.stamp) =
        ((bfsForest (assignedForest z α)).map NTree.label).map
          GenMemoryRow.stamp := by
    rw [List.map_map]
    rfl
  rw [hstamps]
  refine threadGenRows_timestamp α (memInputs z) 0
      ((bfsForest (assignedForest z α)).map NTree.label) ?_
  intro g hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  exact assigned_bfs_memoryTimestamp z α t ht

theorem memory_timestamps (z α : K) :
    List.Forall₂ (MemoryTimestampSpecializesAt α)
      (timestampSkeleton z α).memoryRows
      (execThreaded z α).memoryRows := by
  rw [memoryRows_eq_threadGenRows, List.forall₂_map_right_iff]
  exact (memory_timestampsA z α).imp
    (fun _ _ h => memoryTimestampSpecializesAt_encodeRow h)

/-- The absolute line-number origin on the threaded compute rows, which the semantic request
    bridge takes separately now that `ComputeTimestampSpecializesAt` is the relative RAP form.
    Discharged from `renderNode_ln_prev`; `setRowCoins` leaves `row.2.2` untouched. -/
theorem compute_origins (z α : K) :
    List.Forall₂ (fun stamp row => row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
      (timestampSkeleton z α).computeRows
      (execThreaded z α).computeRows := by
  rw [timestampSkeleton_computeRows, computeRows_eq_overwritten]
  unfold bfsStamps
  rw [forall2_map_map_iff]
  intro n _
  exact renderNode_ln_prev z α n.label

theorem challenge_α (z α : K) : (cfg z α).challenges.α = α := by
  simp [cfg]

theorem specializes_threaded (z α : K) (hz : z ≠ 0) :
    TimestampSpecializesAt z α (timestampSkeleton z α)
      (cfg z α) (execThreaded z α) where
  challengeEquation := challenge_α z α
  semanticBinding := bindsAt_threaded z α
  computeTimestampEquations := compute_timestamps z α
  memoryTimestampEquations := memory_timestamps z α
  requestBridgeEquation :=
    semanticRequestBridgeEquation hz (bindsAt_threaded z α)
      (compute_timestamps z α) (compute_origins z α)
  responseBridgeEquation :=
    semanticResponseBridgeEquation (bindsAt_threaded z α)
      (memory_timestamps z α)
      (by
        intro row hrow
        rw [memoryRows_eq_threaded] at hrow
        obtain ⟨r0, _, rfl⟩ := List.mem_map.mp hrow
        rw [MemoryTable.Pub.lambda_some _ _ (encodeRow_pub_lambda? (lmb := MemoryTable.formRDefault) r0)]
        rfl)

theorem specializes_seed :
    TimestampSpecializesAt seedZ alphaA (timestampSkeleton seedZ alphaA)
      (cfg seedZ alphaA) (execThreaded seedZ alphaA) :=
  specializes_threaded seedZ alphaA seedZ_ne_zero

theorem accAt_mm_lt : accAt (mmTreeAir (K := K))
    (bfsRows (mmTreeAir (K := K))).length + 3 < 65536 := by
  have := accAt_mm_le
  omega

theorem requestTimestampBound_threaded (z α : K) :
    ∀ r ∈ (timestampSkeleton z α).semanticRequestsAt z, r.2.2 < 65536 :=
  genSemanticRequestsAt_timestampBound (F := F) 65536 z
    (mmTreeAir (K := K)) (assignedForest z α) accAt_mm_lt

theorem requestTimestampBound_seed :
    ∀ r ∈ (timestampSkeleton seedZ alphaA).semanticRequestsAt seedZ,
      r.2.2 < 65536 :=
  requestTimestampBound_threaded seedZ alphaA

theorem timestampBound_le_order_seed :
    (65536 : ℕ) ≤ orderOf (cfg seedZ alphaA).challenges.α := by
  rw [challenge_α, alphaA_order]

theorem responseTimestampBound_threaded (z α : K) :
    ∀ r ∈ (timestampSkeleton z α).semanticResponsesAt z, r.2.2 < 65536 :=
  genSemanticResponsesAt_timestampBound (F := F) 65536 z α
    (mmTreeAir (K := K)) accAt_mm_lt

theorem responseTimestampBound_seed :
    ∀ r ∈ (timestampSkeleton seedZ alphaA).semanticResponsesAt seedZ,
      r.2.2 < 65536 :=
  responseTimestampBound_threaded seedZ alphaA

theorem mmTree_requests_match : treeRequestsMatch (mmTree (K := K)) :=
  genComputeSkeleton_tree_requests_match (mmTree_gen (K := K))

/-! ## `L_mIO` at this configuration

`semantic_lmio` was ~230 lines here.  It is now `genTimestampSkeleton_lmio`
(`GenSemanticLmIO.lean`) applied at this configuration: `t := mmTree`, `h := mmTree_gen`, and the
`[Ksz]` window from `accAt_mm_le`.  Nothing about `65537`, the 401-row trace, the seed or `α`
enters the derivation — the generic theorem supplies the `Nodup`, the `Perm` and the range in one
step, and the types match by elaboration. -/

theorem accAt_mm_le_Ksz (z α : K) :
    accAt (airReorder (mmTree (K := K)))
        (bfsRows (airReorder (mmTree (K := K)))).length ≤ (cfg z α).Ksz :=
  le_trans accAt_mm_le (by norm_num [cfg])

theorem semantic_lmio (z α : K) :
    IO.LmIO (cfg z α).Ksz
      ((timestampSkeleton z α).semanticRequestsAt z)
      ((timestampSkeleton z α).semanticResponsesAt z) :=
  genTimestampSkeleton_lmio (F := F) (cfg z α).Ksz z α (mmTree_gen (K := K))
    (assignedForest_memoryStampsWellFormed z α) (accAt_mm_le_Ksz z α)

def semanticPreimage :
    SemanticIOPreimage (cfg seedZ alphaA) (execThreaded seedZ alphaA) :=
  specializes_seed.toSemanticIOPreimage 65536
    (by simpa [challenge_α] using timestampBound_le_order_seed)
    requestTimestampBound_seed
    responseTimestampBound_seed
    (semantic_lmio seedZ alphaA)
    (genSemanticRequests_exponent_nodup (mmTreeAir (K := K)) (assignedForest seedZ alphaA))

theorem semanticExactLanguage :
    SemanticExactLanguage (cfg seedZ alphaA) (execThreaded seedZ alphaA) :=
  ⟨computeRowsAccepted_threaded, memoryRowsAccepted_seed, ⟨semanticPreimage⟩⟩

theorem chained
    (hfirst : ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.counts = 0) :
    ChainedSemanticExactLanguage (cfg seedZ alphaA)
      (execThreaded seedZ alphaA) where
  semantic := semanticExactLanguage
  z_ne_zero := seedZ_ne_zero
  compute_wf := compute_wf_seed
  memory_wf := memory_wf_seed
  compute_chain := compute_chain seedZ alphaA
  memory_chain := memory_chain seedZ alphaA
  memory_first_counts := memory_first_counts seedZ alphaA two_ne_zero hfirst
  memory_first_indicator := memory_first_indicator seedZ alphaA two_ne_zero hfirst
  memory_first_ipre := memory_first_ipre seedZ alphaA
  memory_last_icur := memory_last_icur seedZ alphaA

  memory_same_lambda :=
    ExactExecution.memory_same_lambda_of_const _ (some MemoryTable.formRDefault)
      (execThreaded_lambda? seedZ alphaA)

end

end Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.specializes_seed
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.requestTimestampBound_seed
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.responseTimestampBound_seed
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.mmTree_requests_match
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.accAt_mm_le_Ksz
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.semantic_lmio
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.semanticExactLanguage
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.chained
