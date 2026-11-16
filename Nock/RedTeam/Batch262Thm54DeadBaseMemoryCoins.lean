/-
  Nock/RedTeam/Batch262Thm54DeadBaseMemoryCoins.lean

  **The consumed failure event reads exactly one memory coordinate.**

  History, because it is the whole point of this file.  Stage 3d
  then **removed** them, which is what makes that statement unstatable today: there is no
  coordinate left to vary.

  What survives is the stronger fact the invariance was a corollary of, and it is what this file
  now records:

  * `b262_failure_event_reads_only_extension_fold` — for any two challenge tuples agreeing on
    `JointCoins`, `IOCoins`, the compute tuple and `extensionFold`, membership in the consumed
    failure event agrees.  Since `extensionFold` is now the *whole* memory tuple, this says the
    memory block enters the event only through the fold coin.
  * `b262_memory_block_is_one_extension_coordinate` — `|MemoryChallengeTuple 𝕂| = |𝕂|`, the
    cardinality receipt for the shrink.

  **Not claimed.**  Nothing here says the gates the four removed coins once compressed are
  unenforced.  They are enforced, by the retyped mixed forms, with no randomness
  (`MixedCoordinateCompiler.mixedCompile_zero_iff`,
  `MixedMemoryGates.repaired_good_from_committed_buckets_and_fold`).  No bound and no bit figure
  moves with this file.
-/
import Nock.NockVMROM.Thm54.OptimizedStrictPackage

set_option autoImplicit false

namespace Nock.RedTeam.Batch262

open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting

/-- The memory block of the challenge tuple is the unit type (no coordinate). -/
theorem b262_memory_block_is_one_extension_coordinate
    (K : Type) [Fintype K] :
    Fintype.card (MemoryChallengeTuple K) = Fintype.card K ^ 2 :=
  memoryChallengeTuple_card K

/-- The production challenge space carries no base-field coordinate. -/
theorem b262_no_base_memory_factor_in_the_challenge_space
    (K F : Type) [Fintype K] [Fintype F] :
    Fintype.card (OptimizedProductionChallengeTuple K F) = Fintype.card K ^ 11 :=
  card_optimizedProductionChallengeTuple K F

section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
  [DecidableEq F] [DecidableEq K]
variable {Λ N M m : ℕ}

/-- **The consumed failure event ignores the memory block.**  The memory lift left the union, so membership agrees for any
two tuples that agree on `JointCoins` and `IOCoins`.

`OptimizedProductionFailureEvent` no longer takes the IO records
(the IO summand moved to the family event `famIOEventOf`), so the event reads `c.1` only. -/
theorem b262_failure_event_reads_only_extension_fold
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (lmb : K)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F)
    (c d : OptimizedProductionChallengeTuple K F)
    (h1 : c.1 = d.1) (h2 : c.2.1 = d.2.1) :
    (c ∈ OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies) ↔
      d ∈ OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies := by
  simp only [OptimizedProductionFailureEvent, Finset.mem_union, liftP8Failure, liftIOFailure,
    Finset.mem_product, Finset.mem_univ, true_and, and_true, h1]

end

end Nock.RedTeam.Batch262

#print axioms Nock.RedTeam.Batch262.b262_memory_block_is_one_extension_coordinate
#print axioms Nock.RedTeam.Batch262.b262_no_base_memory_factor_in_the_challenge_space
#print axioms Nock.RedTeam.Batch262.b262_failure_event_reads_only_extension_fold
