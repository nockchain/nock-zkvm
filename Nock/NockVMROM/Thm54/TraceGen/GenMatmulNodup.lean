/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulNodup.lean

  Opcode-active request timestamps on the generated assigned matmul BFS
  render are the consecutive powers `α^1.. α^L` with `L = accAt mmTree 401
  ≤ 3 * 401 = 1203`.  `requestNodup` inhabits because the honest `α` is
  the orbit generator (`orderOf = 2^16 > 1203`).  The OP1-slice sample
  `φ(4)` has order `16` and is not used.

  **The `∀`-generic facts that used to be here now live in `GenGenericRowFacts.lean`** —
  `map_getRecordExp_one/_two/_three`, `renderNode_active_timestamps` (all eleven states, no
  hypotheses) and `accAt_le_three_mul`.  Names and statements are unchanged and the namespace
  is the same, so uses here resolve exactly as before.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenericRowFacts
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfig
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulBuildableParts
import Nock.NockVMROM.Thm54.TraceGen.GenSound
import Nock.NockVMROM.Thm54.TraceGen.GenTierANodup
import Nock.NockVMROM.Thm54.Language

set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.NockVM
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy

variable {K : Type} [Field K]

/-! ## BFS-indexed request timestamps

The per-row readout these build on (`renderNode_active_timestamps` and the
`map_getRecordExp_*` helpers) is `∀`-generic and lives in `GenGenericRowFacts.lean`; these two
put it at a BFS index and then over a prefix. -/

theorem bfsLabelAt_active_timestamps (z α : K)
    (t : NTree (GenComputeRow K)) (i : ℕ)
    (hi : i - 1 < (bfsRows t).length) :
    (activeRequestRecords
        (renderNode z α (bfsLabelAt t i)).row.2.2.1).map (fun r => r.ts) =
      (List.range (Nock.Framework.recordCount (bfsRows t)[i - 1].skel.state)).map
        (fun j => α ^ (accAt t (i - 1) + j + 1)) := by
  rw [renderNode_active_timestamps]
  rw [bfsLabelAt_skel t i hi, bfsLabelAt_stamp t i hi]
  refine List.map_congr_left fun j hj => ?_
  have hj' : j < Nock.Framework.recordCount (bfsRows t)[i - 1].skel.state :=
    List.mem_range.mp hj
  have hj3 : j < 3 :=
    Nat.lt_of_lt_of_le hj' (by simpa [mem_record_arity] using
      Nock.Framework.recordCount_le (bfsRows t)[i - 1].skel.state)
  rw [getRecordExp_stampOfAcc _ _ _ hj3 hj']

theorem range_add (n m : ℕ) :
    List.range (n + m) = List.range n ++ (List.range m).map (n + ·) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.add_succ, List.range_succ, ih, List.range_succ, List.map_append,
        List.append_assoc]
      simp [Nat.add_succ]

theorem range_map_pow_append (α : K) (n m : ℕ) :
    (List.range n).map (fun i => α ^ (i + 1)) ++
      (List.range m).map (fun j => α ^ (n + j + 1)) =
      (List.range (n + m)).map (fun i => α ^ (i + 1)) := by
  rw [range_add, List.map_append]
  congr 1
  simp [List.map_map, Function.comp, Nat.add_assoc]

theorem prefix_request_timestamps (z α : K) (t : NTree (GenComputeRow K)) :
    ∀ k, k ≤ (bfsRows t).length →
      (((List.range k).map
          (fun i => (renderNode z α (bfsLabelAt t (i + 1))).row)).flatMap
        (fun row => activeRequestRecords row.2.2.1)).map (fun r => r.ts) =
        (List.range (accAt t k)).map (fun i => α ^ (i + 1))
  | 0, _ => by
      simp [accAt, List.range_zero]
  | k + 1, hk => by
      have hk' : k < (bfsRows t).length := Nat.lt_of_succ_le hk
      have hle : k ≤ (bfsRows t).length := Nat.le_of_lt hk'
      rw [List.range_succ, List.map_append, List.flatMap_append, List.map_append,
        prefix_request_timestamps z α t k hle]
      have hrow := bfsLabelAt_active_timestamps z α t (k + 1)
        (by simpa using hk')
      simp only [Nat.add_sub_cancel] at hrow
      simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, hrow]
      have hacc := accAt_succ_of_lt t k hk'
      rw [hacc, range_map_pow_append]

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

open Nock Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy

theorem mm_bfsForest_length :
    (bfsForest [mmTree (K := K)]).length = 401 := by
  have h := mmTree_size (K := K)
  simpa [bfsForest_length, totalSize] using h

theorem mmTreeAir_bfsForest_length :
    (bfsForest [mmTreeAir (K := K)]).length = 401 := by
  have h : (mmTreeAir (K := K)).size = 401 := by
    unfold mmTreeAir
    rw [airReorder_size, mmTree_size]
  simpa [bfsForest_length, totalSize] using h

theorem computeRows_eq (z α : K) :
    (exec z α).computeRows =
      (List.range' 1 (bfsForest [mmTreeAir (K := K)]).length).map
        (fun i => setRowCoins (0 : K) 0 1
          (renderNode z α (bfsLabelAt (mmTreeAir (K := K)) i)).row) := by
  unfold ExactExecution.computeRows
  change (bfsForest [computeTree z α]).map NTree.label = _
  unfold computeTree
  rw [renderRows_eq_mapNTree, mapNTree_comp]
  rw [show [mapNTree ((fun g => setRowCoins (0 : K) 0 1 g.row) ∘ renderNode z α)
        (bfsAssign (mmTreeAir (K := K)))] =
      [bfsAssign (mmTreeAir (K := K))].map
        (mapNTree ((fun g => setRowCoins (0 : K) 0 1 g.row) ∘ renderNode z α)) from rfl]
  rw [bfsForest_mapNTree, List.map_map]
  have hcomp :
      NTree.label ∘ mapNTree ((fun g => setRowCoins (0 : K) 0 1 g.row) ∘ renderNode z α) =
        (fun g => setRowCoins (0 : K) 0 1 (renderNode z α g).row) ∘ NTree.label := by
    funext n
    change (mapNTree ((fun g => setRowCoins (0 : K) 0 1 g.row) ∘ renderNode z α) n).label =
      setRowCoins (0 : K) 0 1 (renderNode z α n.label).row
    rw [mapNTree_label]
    rfl
  rw [hcomp, ← List.map_map, bfsAssign_bfsForest_labels, List.map_map]
  rfl

theorem range'_one_eq_map_succ (n : ℕ) :
    List.range' 1 n = (List.range n).map (· + 1) := by
  simp [List.range'_eq_map_range, Nat.add_comm]

theorem rawRequest_timestamps (z α : K) :
    (exec z α).rawRequests.map (fun r => r.ts) =
      (List.range (accAt (mmTreeAir (K := K))
          (bfsRows (mmTreeAir (K := K))).length)).map
        (fun i => α ^ (i + 1)) := by
  rw [ExactExecution.rawRequests_eq_computeRows, computeRows_eq]
  rw [range'_one_eq_map_succ, List.map_map]
  change (((List.range (bfsForest [mmTreeAir (K := K)]).length).map
      (fun i => setRowCoins (0 : K) 0 1
        (renderNode z α (bfsLabelAt (mmTreeAir (K := K)) (i + 1))).row)).flatMap
        (fun row => activeRequestRecords row.2.2.1)).map (fun r => r.ts) = _
  have hlen : (bfsForest [mmTreeAir (K := K)]).length =
      (bfsRows (mmTreeAir (K := K))).length := by
    simp [bfsRows]
  rw [hlen]
  have hsame :
      (((List.range (bfsRows (mmTreeAir (K := K))).length).map
          (fun i => setRowCoins (0 : K) 0 1
            (renderNode z α (bfsLabelAt (mmTreeAir (K := K)) (i + 1))).row)).flatMap
        (fun row => activeRequestRecords row.2.2.1)) =
      (((List.range (bfsRows (mmTreeAir (K := K))).length).map
          (fun i => (renderNode z α
            (bfsLabelAt (mmTreeAir (K := K)) (i + 1))).row)).flatMap
        (fun row => activeRequestRecords row.2.2.1)) := by
    simp [List.flatMap_map]
  rw [hsame]
  exact prefix_request_timestamps z α (mmTreeAir (K := K)) _
    (le_refl _)

theorem accAt_mm_le :
    accAt (mmTreeAir (K := K)) (bfsRows (mmTreeAir (K := K))).length ≤ 1203 := by
  have hlen : (bfsRows (mmTreeAir (K := K))).length = 401 := by
    simp [bfsRows, mmTreeAir_bfsForest_length]
  have h := accAt_le_three_mul (mmTreeAir (K := K))
    (bfsRows (mmTreeAir (K := K))).length
  simpa [hlen] using h

theorem alpha_pows_nodup (n : ℕ) (hn : n < 65536) :
    ((List.range n).map (fun i => alphaA ^ (i + 1))).Nodup := by
  refine (List.nodup_iff_injective_getElem
      (l := (List.range n).map (fun i => alphaA ^ (i + 1)))).2 ?_
  intro i j hij
  have hi : i.1 < n := by
    simpa [List.length_map, List.length_range] using i.2
  have hj : j.1 < n := by
    simpa [List.length_map, List.length_range] using j.2
  have hpow :
      alphaA ^ (i.1 + 1) = alphaA ^ (j.1 + 1) := by
    simpa [List.getElem_map, List.getElem_range] using hij
  have hi' : i.1 + 1 < orderOf alphaA := by
    rw [alphaA_order]; omega
  have hj' : j.1 + 1 < orderOf alphaA := by
    rw [alphaA_order]; omega
  have hidx : i.1 + 1 = j.1 + 1 :=
    (pow_injOn_Iio_orderOf (x := alphaA)) hi' hj' hpow
  exact Fin.eq_of_val_eq (Nat.succ_injective hidx)

theorem requestNodup :
    (exec seedZ alphaA).derivedRequestIO.Nodup := by
  -- The Form R request encode keeps `ts` at coordinate `7` (it no longer reads `encRecC · 1`).
  unfold ExactExecution.derivedRequestIO
  refine List.Nodup.of_map (fun f => f 7) ?_
  rw [List.map_map]
  show ((exec seedZ alphaA).rawRequests.map (fun r => r.ts)).Nodup
  rw [rawRequest_timestamps]
  refine alpha_pows_nodup _ ?_
  have hle := accAt_mm_le
  omega

end Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

#print axioms Nock.NockVMROM.Thm54.TraceGen.renderNode_active_timestamps
#print axioms Nock.NockVMROM.Thm54.TraceGen.prefix_request_timestamps
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.requestNodup
