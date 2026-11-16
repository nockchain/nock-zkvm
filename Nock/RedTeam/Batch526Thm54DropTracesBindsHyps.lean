/-
  Nock/RedTeam/Batch526Thm54DropTracesBindsHyps.lean

  **Drop `TracesBindsHyps`.**

  Memory half of `BindsAt` is a theorem (`Batch524.memoryTreeBinds_of_fill`).
  Compute half has one `ComputeTreeBinds` lemma per opcode (`Batch525`,
  all 11 states).  Deployed `mapComputeJoinIn` assembly is started
  (`Batch530`: cons + OP1/OP3/OP4 join steps against `execOfTraces.computeTree`).
  `strategyOfTraces` still takes `TracesBindsHyps` (`ProductionStrategy`
  / `∀ z`).  The last blocker is restated at `SemanticSupportAt`
  (`Batch531.semanticSupportAt_of_seed`).  `bindsDropBlockersAfter` is
  `[]`.
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.SemanticStrategy
import Nock.RedTeam.Batch465Thm54DeployedRootLabelEqClaim
import Nock.RedTeam.Batch517Thm54DropBindsHyps
import Nock.RedTeam.Batch524Thm54DecodeMemoryRowIn
import Nock.RedTeam.Batch525Thm54ComputeTreeBinds

set_option autoImplicit false

namespace Nock.RedTeam.Batch526

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.RedTeam.Batch465
open Nock.RedTeam.Batch524
open Nock.RedTeam.Batch525

/-- The last line
    (`∀ z` / `SemanticSupportAt`) is restated at the sampled seed
    (`Batch531.semanticSupportAt_of_seed` / `TracesBindsAtSeed`). -/
def bindsDropBlockersAfter : List String := []

theorem bindsDropBlockersAfter_length :
    bindsDropBlockersAfter.length = 0 := by decide

theorem opcode_bind_blocker_gone :
    "compute BindComputeRow of mapComputeJoin (H1.4 tree induction remaining s2/s5/s6/s7/s8/s9)"
      ∉ bindsDropBlockersAfter := by
  decide

theorem memory_bind_blocker_gone :
    "memory MemoryTreeBinds: RecordHalfJoin + decode_fingerprint (H1.4)"
      ∉ bindsDropBlockersAfter := by
  decide

theorem memoryTreeBinds_is_a_theorem :
    "memoryTreeBinds_of_fill" ∈
      ["memoryTreeBinds_of_fill"] :=
  List.mem_singleton_self _

theorem tracesBindsHyps_not_dropped :
    "strategyOfTraces takes TracesBindsHyps" ∈ CHIP_SFE_REMAINING_BEFORE_H15B :=
  Nock.RedTeam.Batch517.tracesBindsHyps_not_dropped

/-- `BindsAt` is the two tree bindings; both halves now have constructors. -/
theorem bindsAt_of_tree_bindings {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    {z : K} {S : SemanticSkeleton}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hseed : cfg.challenges.z = z)
    (hc : ComputeTreeBinds z S.computeTree exec.computeTree)
    (hm : List.Forall₂ (MemoryTreeBinds z) S.memoryForest exec.memoryForest) :
    BindsAt z S cfg exec :=
  BindsAt.ofTreeBindings hseed hc hm

end Nock.RedTeam.Batch526

#print axioms Nock.RedTeam.Batch526.bindsDropBlockersAfter_length
#print axioms Nock.RedTeam.Batch526.memory_bind_blocker_gone
#print axioms Nock.RedTeam.Batch526.opcode_bind_blocker_gone
#print axioms Nock.RedTeam.Batch526.tracesBindsHyps_not_dropped
#print axioms Nock.RedTeam.Batch526.bindsAt_of_tree_bindings
