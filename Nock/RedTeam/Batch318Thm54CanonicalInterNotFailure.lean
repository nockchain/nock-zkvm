/-
  Nock/RedTeam/Batch318Thm54CanonicalInterNotFailure.lean

  Twin of `canonical_coins_not_hostile_failure`.

  Paper at source: the paper.
-/
import Nock.NockVMROM.Thm54.OptimizedCanonicalHostileLists
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.RedTeam.Batch318

open Nock.NockVMROM.Thm54.OptimizedCanonicalHostileLists
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

/-- Honest canonical pair is not in the priced internal-pole event. -/
theorem canonical_inter_outside_failure
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (h0 : P.optimized.sampled.interPole ≠ 0)
    (hγ8 : P.optimized.sampled.interPole +
      P.optimized.sampled.sampled.coins.gamma ^ 8 ≠ 0)
    (hz : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .read_root →
      (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .verify_child →
      (P.optimized.family.problem.exec.memoryPubAt i).mem =
        ComputeTable.MemRec.zero)
    (hzc : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .read_root →
      (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .verify_child →
      (P.optimized.family.problem.exec.memoryPubAt i).cprime = 1)
    (hC : P.optimized.family.problem.exec.CprimeCoherent) :
    (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.interPole) ∉
      interFailurePairs
        (P.hostileInterRecords (honestMemoryTrace P))
        (P.memorySourceEnv (honestMemoryTrace P))
        (P.memoryBaseEnv (honestMemoryTrace P)) :=
  canonical_inter_not_hostile_failure (P := P) h0 hγ8 hz hzc hC

end Nock.RedTeam.Batch318

#print axioms Nock.RedTeam.Batch318.canonical_inter_outside_failure
