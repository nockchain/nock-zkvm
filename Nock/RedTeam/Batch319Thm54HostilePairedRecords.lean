/-
  Nock/RedTeam/Batch319Thm54HostilePairedRecords.lean

  Any accepted
  `(Qc, Qm, c)` outside the consumed failure event has
  `(hostileReads P Qm).Perm (hostileVerifies P Qm)` — `hpole` derived from
  the all-row pole-hit half of `interFailurePairs`.  Not a field of `E`.

  Paper at source: the paper.
-/
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.MemoryInternalPole
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.RedTeam.Batch319

open Nock.NockVMROM.Thm54.MemoryInternalPole
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open scoped Polynomial

/-- Hostile `read_root` records permute `verify_child` records off the
consumed event -/
theorem hostile_paired_records
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (S : OptimizedFullStrictThm54Statement P)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hK : rows P < ringChar K) :
    (hostileReads P Qm).Perm (hostileVerifies P Qm) :=
  optimizedFullStrict_paired_records (P := P) Qc Qm c S hacc hgood hK

end Nock.RedTeam.Batch319

#print axioms Nock.RedTeam.Batch319.hostile_paired_records
