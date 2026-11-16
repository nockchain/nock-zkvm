/-
  Nock/NockVMROM/Thm54/TraceGen/GenExactExecution.lean

  Until the carrier itself is built once and for all, "the
  premises are generic" and "the theorem is generic" stay different statements.

  This module builds the carrier.  It is deliberately mechanical: every field of `ExactConfig` and
  `ExactExecution` is either

  * **defined as** the generated trace's own measurement — `kMem` is the forest's root count,
    `compRows`/`memRows` are the BFS lengths, so `memory_root_count`, `compute_bfs_length` and
    `memory_bfs_length` follow from the general `bfsForest_mapNTree` rewrites rather than from a
    per-fixture `norm_num` at literals (they are `rfl` only *after* those rewrites); or

  Nothing is discovered here and nothing is assumed that a configuration was not already assuming:
  `DotConfig769.cfg` hard-codes `compRows := 8`, `memRows := 184`, `kMem := 10` and proves the three
  length obligations by `norm_num` at those literals.  `genExactConfig` replaces the literals with
  the measurements, so the obligations become definitional and the literals disappear.

  `compRows_pos` needs no hypothesis: a compute tree always has its root
  (`bfsForest_singleton_length_pos`).

  **Scope.**  This is the carrier only.

  Note also that `genExactConfig` / `genExactExecution` / `genBuildable` quantify over an
  **arbitrary** `ct` and `mf`, with no hypothesis tying either to `genComputeSkeleton`.  They are
  therefore more general than "for any generated trace" suggests; `Batch167` is what ties the carrier
  to an actual generated program.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenericCensusWindow
import Nock.NockVMROM.Thm54.TraceGen.GenTierAComputeLink

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.Framework.Thm54

variable {F K : Type} [Field F] [Field K] [Algebra F K]

variable {lmb : K}

/-! ## A compute tree always has a row

`bfsForest_singleton_length_pos` (`BFSAssign.lean:77`) already says the root is there. -/

/-- A forest with a nonempty BFS is itself nonempty. -/
theorem ne_nil_of_bfsForest_length_pos {α : Type} {l : List (NTree α)}
    (h : 0 < (bfsForest l).length) : l ≠ [] := by
  rintro rfl
  simp [bfsForest_nil] at h

/-! ## The configuration -/

/-- **`ExactConfig` measured off a generated trace.**

`kMem`, `compRows` and `memRows` are the trace's own counts rather than literals, so the three
`ExactExecution` length obligations become definitional. -/
noncomputable def genExactConfig
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    ExactConfig F K where
  challenges := chal
  Ksz := Ksz
  kMem := mf.length
  orbit := orbit
  orbit_h_pos := horb
  compRows := (bfsForest [ct]).length
  memRows := (bfsForest mf).length
  compRows_pos := bfsForest_singleton_length_pos ct
  memRows_pos := hmempos
  compRows_le := hcomp
  memRows_le := hmem
  eDeg := 1
  eDeg_eq_one := rfl
  compNodes := fun i => orbit.βcoset * orbit.ω ^ (i : ℕ)
  compNodes_spec := fun _ => rfl
  memNodes := fun i => orbit.βcoset * orbit.ω ^ (i : ℕ)
  memNodes_spec := fun _ => rfl

/-! ## The execution -/

/-- **`ExactExecution` for any generated trace.**

The compute tree is the rendered generated tree with the rows projected out — exactly what
`DotConfig769.computeTree` (`GenTierAConfig769.lean:81`) and `GenMatmulConfig.computeTree`
(`GenMatmulConfig.lean:102`) build by hand — and the memory forest likewise.  All three length
fields are `bfsForest_mapNTree` plus `rfl`.
The generated memory rows are a-bearing, so this projection is the **a-bearing view**
`genExactExecutionA`, on which all axis accounting and the served trace live.  The executed trace
`genExactExecution` is its row encode `ExactExecution.encodeMem` (`MemoryRowTemplate.encodeRow`,
the single memory encode site), which writes `(T, C', λ)` on active rows. -/
noncomputable def genExactExecutionA
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    ExactExecution (genExactConfig (F := F) chal Ksz orbit horb ct mf hmempos hcomp hmem) where
  computeTree := mapNTree (fun g : GenComputeRow K => setRowCoins a b c g.row) ct
  memoryForest := mf.map (mapNTree GenMemoryRow.row)
  memoryForest_nonempty := by
    simpa using ne_nil_of_bfsForest_length_pos hmempos
  memory_root_count := by
    simp [genExactConfig]
  compute_bfs_length := by
    rw [bfsForest_mapNTree_singleton]
    simp [genExactConfig]
  memory_bfs_length := by
    rw [bfsForest_mapNTree]
    simp [genExactConfig]

/-- **The executed trace of a generated program**: the row encode of the a-bearing view. -/
noncomputable def genExactExecution
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    ExactExecution (genExactConfig (F := F) chal Ksz orbit horb ct mf hmempos hcomp hmem) :=
  (genExactExecutionA chal Ksz orbit horb a b c ct mf hmempos hcomp hmem).encodeMem

theorem genExactExecution_eq_encodeMem
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    genExactExecution (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem =
      (genExactExecutionA (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem).encodeMem :=
  rfl

/-! ## The rows are the generated rows

Stated so downstream work never has to re-derive the projection. -/

theorem genExactExecution_computeRows
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem).computeRows =
      (bfsRows ct).map (fun g => setRowCoins a b c g.row) := by
  rw [genExactExecution, ExactExecution.encodeMem_computeRows]
  show ((bfsForest [mapNTree (fun g : GenComputeRow K => setRowCoins a b c g.row) ct]).map
    NTree.label) = _
  rw [bfsForest_mapNTree_singleton, List.map_map]
  unfold bfsRows
  rw [List.map_map]
  exact List.map_congr_left fun t _ => mapNTree_label _ t

/-- The two views share their compute rows. -/
theorem genExactExecutionA_computeRows_eq
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    (genExactExecutionA (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem).computeRows =
      (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem).computeRows :=
  rfl

theorem genExactExecutionA_computeRows
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    (genExactExecutionA (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem).computeRows =
      (bfsRows ct).map (fun g => setRowCoins a b c g.row) := by
  rw [genExactExecutionA_computeRows_eq]
  exact genExactExecution_computeRows chal Ksz orbit horb a b c ct mf hmempos hcomp hmem

/-- The a-bearing view's memory rows are the generated rows. -/
theorem genExactExecutionA_memoryRows
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    (genExactExecutionA (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem).memoryRows =
      (bfsForest mf).map (fun n => GenMemoryRow.row n.label) := by
  show ((bfsForest (mf.map (mapNTree GenMemoryRow.row))).map NTree.label) = _
  rw [bfsForest_mapNTree, List.map_map]
  exact List.map_congr_left fun t _ => mapNTree_label GenMemoryRow.row t


/-- The executed memory rows are the row encode of the generated rows. -/
theorem genExactExecution_memoryRows
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem).memoryRows =
      (bfsForest mf).map (fun n => MemoryRowTemplate.encodeRow chal.lam (GenMemoryRow.row n.label)) := by
  rw [genExactExecution, ExactExecution.encodeMem_memoryRows, genExactExecutionA_memoryRows,
    List.map_map]
  rfl

/-- Every executed memory row carries the configuration's `λ` (`encodeRow chal.lam`; the core
`MemoryRowAccepted` λ pin and the `hlam` premise of `semanticResponseBridgeEquation`). -/
theorem genExactExecution_memoryRows_lambda
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    ∀ row ∈ (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem).memoryRows,
      row.2.2.lambda = chal.lam := by
  intro row hrow
  rw [genExactExecution_memoryRows] at hrow
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp hrow
  unfold MemoryRowTemplate.encodeRow
  split <;> simp [MemoryTable.Pub.lambda]

/-! ## The carrier, assembled

`genBuildable` is the generic `BuildableNockExecution`.

A configuration that today writes fourteen fields by hand writes these arguments instead. -/
noncomputable def genBuildable
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (q : ℕ) (hq : 1 < q) (Λ : ℕ)
    (sd : SemanticTrace.ExactExecutionSemanticData q Λ
      (genExactConfig (F := F) chal Ksz orbit horb ct mf hmempos hcomp hmem)
      (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem))
    (mt : ServedMemoryTrace.ExactServedMemoryTrace q Λ
      (genExactConfig (F := F) chal Ksz orbit horb ct mf hmempos hcomp hmem)
      (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem) sd
      (genExactExecutionA (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem))
    (hnodup :
      (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem).derivedRequestIO.Nodup)
    (hbal : RowLayout.RecordCountBalanced
      (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem))
    (hqrc : q ≤ ringChar K) (h2 : (2 : K) ≠ 0) (hKsz : Ksz < ringChar K)
    (hprog :
      (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem).derivedRequestIO.length
        + 1 ≤ 2 ^ orbit.h)
    (hresp :
      (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem).derivedResponseIO.length
        + 1 ≤ 2 ^ orbit.h) :
    BuildableNockExecution F K where
  q := q
  q_gt_one := hq
  Λ := Λ
  cfg := genExactConfig chal Ksz orbit horb ct mf hmempos hcomp hmem
  execA := genExactExecutionA chal Ksz orbit horb a b c ct mf hmempos hcomp hmem
  exec := genExactExecution chal Ksz orbit horb a b c ct mf hmempos hcomp hmem
  exec_encode := rfl
  semanticData := sd
  memoryTrace := mt
  requestNodup := hnodup
  recordCountBalance := hbal
  q_le_ringChar := hqrc
  two_ne_zero := h2
  Ksz_lt_ringChar := hKsz
  programIOCapacity := hprog
  memoryIOCapacity := hresp

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.ne_nil_of_bfsForest_length_pos
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactConfig
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecutionA
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecution
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecutionA_memoryRows
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecution_computeRows
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecution_memoryRows
#print axioms Nock.NockVMROM.Thm54.TraceGen.genBuildable
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecution_memoryRows_lambda
