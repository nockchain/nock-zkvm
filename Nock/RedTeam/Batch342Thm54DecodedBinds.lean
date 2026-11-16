/-
  Nock/RedTeam/Batch342Thm54DecodedBinds.lean

  `BindsAt` (`SemanticStrategy.BindsAt`) needs both a compute tree and a memory
  forest.  This lane decodes the memory forest.

  ```
  theorem decoded_binds
      {z : K} (hz : z ≠ 0) {q : ℕ} {α : K}
      (join : ComputeJoin)
      (forest : List (NTree (MState × DTmem K)))
      {cfg : ExactConfig F K} {exec : ExactExecution cfg}
      (hjoin : ComputeJoinSound z join cfg exec)
      (hforest : exec.memoryForest = forest)
      (hstruct : ∀ t ∈ forest, MemoryFingerprintStructure z t)
      (hleaves : ∀ t ∈ forest, MemoryLeafAtomsRealized q t)
      (hbound : ∀ n ∈ decodedNodes q forest, n.leaves ≤ q)
      (hgood : z ∉ (hostileCensus q q forest hbound).badSeeds) :
      BindsAt z (decodedSkeleton q join forest) cfg exec
  ```

  * `ComputeJoin.computeTree` — nouns for each compute row's subject / formula /
    evaluation / active decompositions / active records, read off the served
    memory-forest nodes by matching `hostileRecords`.
  * `ComputeJoinSound` — `cfg.challenges.z = z` and
    `ComputeTreeBinds z join.computeTree exec.computeTree`.
  * Until then `decodeMemoryRow` writes `atom 0`.

  This batch proves the compute half (`decoded_binds_compute`) and the forest
  length identity.  Full `MemoryTreeBinds` waits on `RecordHalfJoin`.
-/
import Nock.NockVMROM.Thm54.HostileSkeletonDecoding

namespace Nock.RedTeam.Batch342

open Nock
open Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.SemanticStrategy

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem binds_compute
    {z : K} {join : ComputeJoin}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hjoin : ComputeJoinSound z join cfg exec) :
    ComputeTreeBinds z
        (decodedSkeleton (K := K) (q := 0) join []).computeTree
      exec.computeTree :=
  decoded_binds_compute hjoin

theorem forest_length (q : ℕ)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))) :
    (decodedMemoryForest q forest).length = forest.length :=
  decodedMemoryForest_length q forest

theorem skeleton_computeTree (q : ℕ) (join : ComputeJoin)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))) :
    (decodedSkeleton q join forest).computeTree = join.computeTree :=
  rfl

end

#print axioms Nock.RedTeam.Batch342.binds_compute
#print axioms Nock.RedTeam.Batch342.forest_length

end Nock.RedTeam.Batch342
