/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulBuildableParts.lean

  Non-semantic `BuildableNockExecution` side-obligations for the generated
  2×2 matmul program hosted on `MatmulConfig65537` (`F = ZMod 65537`,
  `K = GaloisField 65537 3`).  Atom bound `q = 65537 = ringChar K`.
  Orbit `2^16 = 65536` covers 401 compute rows and 30936 memory rows.

  The committed node forests project onto `exec`'s row carriers, and
  `RecordCountBalanced` holds by the generic generated-forest fibre
  identity (`genMemForestFromTree_balanced`).  `requestNodup` is in
  `GenMatmulNodup` (honest `α` is the orbit generator of order `2^16`).

  `semanticData` / `memoryTrace` are not claimed here: those need the
  per-row language and the served forest walk.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfig
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulMem
import Nock.NockVMROM.Thm54.TraceGen.GenTierABalance
import Nock.NockVMROM.Thm54.Language
import Nock.NockVMROM.Thm54.MemoryMplus2L

namespace Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

open Nock Nock.Walk Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.RowLayout

/-! ## Characteristic of the table field -/

instance : CharP K 65537 := inferInstance

theorem ringChar_K : ringChar K = 65537 :=
  CharP.eq K (ringChar.charP K) (inferInstanceAs (CharP K 65537))

/-! ## Opcode-active request / response lengths -/

theorem activeRequestRecords_length_le (pub : ComputeTable.Pub K) :
    (activeRequestRecords pub).length ≤ 3 := by
  unfold activeRequestRecords
  split <;> simp

theorem responseRecords_length_le (pub : MemoryTable.Pub K) :
    (responseRecords pub).length ≤ 1 := by
  unfold responseRecords
  split <;> simp

theorem length_flatMap_le {α β} (l : List α) (f : α → List β) (n : ℕ)
    (h : ∀ x ∈ l, (f x).length ≤ n) :
    (l.flatMap f).length ≤ n * l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    have hx : (f x).length ≤ n := h x (List.mem_cons.mpr (Or.inl rfl))
    have hxs : ∀ y ∈ xs, (f y).length ≤ n := fun y hy =>
      h y (List.mem_cons.mpr (Or.inr hy))
    have := ih hxs
    omega

/-! ## The non-semantic fields that do not need the row web -/

theorem q_gt_one : 1 < (65537 : ℕ) := by norm_num

theorem q_le_ringChar : (65537 : ℕ) ≤ ringChar K := by
  rw [ringChar_K]

theorem two_ne_zero : (2 : K) ≠ 0 := by
  intro h
  have : 65537 ∣ 2 := (CharP.cast_eq_zero_iff K 65537 2).mp h
  omega

theorem Ksz_lt_ringChar (z α : K) : (cfg z α).Ksz < ringChar K := by
  rw [ringChar_K]
  norm_num [cfg]

theorem derivedRequestIO_length_le (z α : K) :
    (exec z α).derivedRequestIO.length ≤ 1203 := by
  rw [ExactExecution.derivedRequestIO, List.length_map,
    ExactExecution.rawRequests_eq_computeRows]
  have hrows : (exec z α).computeRows.length = 401 :=
    (exec z α).computeRows_length
  have hle := length_flatMap_le (exec z α).computeRows
    (fun row => activeRequestRecords row.2.2.1) 3
    (fun _ _ => activeRequestRecords_length_le _)
  omega

theorem derivedResponseIO_length_le (z α : K) :
    (exec z α).derivedResponseIO.length ≤ 30936 := by
  -- Row-level memory: each `ver` row emits one record whatever its `C'` (no `C' = 1`).
  have hrows : (exec z α).memoryRows.length = 30936 :=
    (exec z α).memoryRows_length
  have hle := ExactExecution.derivedResponseIO_length_le (exec z α)
  omega

theorem programIOCapacity (z α : K) :
    (exec z α).derivedRequestIO.length + 1 ≤ 2 ^ (cfg z α).orbit.h := by
  have hlen := derivedRequestIO_length_le z α
  have hpow : 2 ^ (cfg z α).orbit.h = 65536 := by
    simp [cfg, executionOrbit]
  omega

theorem memoryIOCapacity (z α : K) :
    (exec z α).derivedResponseIO.length + 1 ≤ 2 ^ (cfg z α).orbit.h := by
  have hlen := derivedResponseIO_length_le z α
  have hpow : 2 ^ (cfg z α).orbit.h = 65536 := by
    simp [cfg, executionOrbit]
  omega

/-! ## Committed node forests project onto `exec` -/

theorem computeNodes_rows (z α : K) :
    mapNTree ComputeNode.row (mmComputeNodes z α) = computeTree z α := by
  unfold mmComputeNodes computeTree
  rw [mapNTree_comp, mapNTree_comp]
  rfl

theorem memoryNodes_rows (z α : K) :
    (mmMemoryNodes z α).map (mapNTree MemoryNode.row) = memoryForest z α := by
  unfold mmMemoryNodes memoryForest
  rw [List.map_map]
  refine List.map_congr_left fun t _ => ?_
  change mapNTree MemoryNode.row (mapNTree GenMemoryRow.node t) =
    mapNTree GenMemoryRow.row t
  rw [mapNTree_comp]
  rfl

/-! ## Record-count balance -/

theorem memoryStateCount_eq_forestFibre (z α : K) (s : MState) :
    memoryStateCount (exec z α) s =
      forestFibre s
        (genMemForestFromTree (encC z) z α MemoryTable.formRDefault (bfsAssign (mmTreeAir (K := K)))) := by
  unfold memoryStateCount ExactExecution.memoryRows
  have hmf : (exec z α).memoryForest = memoryForest z α := rfl
  rw [hmf, memoryForest, fibreCount_bfsForest_mapNTree_row, fibreCount_bfsForest]

theorem recordCountBalance (z α : K) :
    RecordCountBalanced (exec z α) := by
  unfold RecordCountBalanced
  rw [memoryStateCount_eq_forestFibre, memoryStateCount_eq_forestFibre]
  exact genMemForestFromTree_balanced (encC z) z α
    (bfsAssign (mmTreeAir (K := K)))

end Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.ringChar_K
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.two_ne_zero
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.programIOCapacity
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.memoryIOCapacity
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.computeNodes_rows
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.memoryNodes_rows
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.recordCountBalance
