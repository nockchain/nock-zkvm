/-
  Nock/RedTeam/Batch358Thm54TupleWiden.lean

  **Widen `OptimizedProductionChallengeTuple` `|𝕂|⁷ → |𝕂|¹⁰`.**
  `(a, b, c)` sit in `FinalComputeChallengeTuple` at `c.2.2.1` as `eqA, eqB, eqC`.
  They are compute RAP inputs and belong with the compute
  block; JointCoins / IO / `MemoryChallengeTuple` projections stay put.  The
  product proof of `card_optimizedProductionChallengeTuple` becomes `|K|^10`.

  Soundness does not read them (`op5_evaluation_is_equality_without_abc`); the
  consumed probability bound is byte-identical
  (`optimizedHostileProductionFailureProbabilityBound_byte_identical`).  Every
  existing event lifts as a cylinder; densities are unchanged.

  `chalValOfTuple` / `computeKOfTuple` now carry slots `2,3,4`.
  `chalValOfTuple_honest` closes on the cubic read set without a `0`.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.GateCorrespondenceCompute
import Nock.NockVMROM.Thm54.ComputeStagedTable
import Nock.RedTeam.Batch357Thm54DeployedReadSet
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch358

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.GigaChips
open Nock.ComputeTable
open Module

/-! ## Where `(a, b, c)` sit, and why -/

/-- `(a, b, c)` are the three fields of `FinalComputeChallengeTuple`, which is
the first factor of the inner chip pair `c.2.2`.  Product:
`JointCoins × ((K×K) × (FinalComputeChallengeTuple × MemoryChallengeTuple))`. -/
theorem abc_sit_at_c_2_2_1 {K F : Type} [Fintype K] [Fintype F]
    (c : OptimizedProductionChallengeTuple K F) :
    c.2.2.1 = ⟨c.2.2.1.eqA, c.2.2.1.eqB, c.2.2.1.eqC⟩ :=
  FinalComputeChallengeTuple.eta c.2.2.1

/-- Challenge space is `|𝕂|¹⁰`. -/
theorem card_is_ten (K F : Type) [Fintype K] [Fintype F] :
    Fintype.card (OptimizedProductionChallengeTuple K F) = Fintype.card K ^ 11 :=
  card_optimizedProductionChallengeTuple K F

/-- The compute block is `|𝕂|³`, not the unit. -/
theorem compute_block_card (K : Type) [Fintype K] :
    Fintype.card (FinalComputeChallengeTuple K) = Fintype.card K ^ 3 :=
  card_finalComputeChallengeTuple K

/-! ## Probability bound is byte-identical; densities unchanged -/

theorem bound_byte_identical (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedHostileProductionFailureProbabilityBound cardK cardF p8Work ioWork N M =
      (p8Work +
        OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
        pricedWalkWork N M : ℚ) / cardK +
      (ioWork : ℚ) / cardK ^ 2 +
      ((FiniteIO.ioFailureUnionBound 10 M M cardK + cardK * M : ℕ) : ℚ) / cardK ^ 2 :=
  optimizedHostileProductionFailureProbabilityBound_byte_identical
    cardK cardF p8Work ioWork N M

theorem p8_density {K F : Type} [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F]
    [Nonempty K]
    (bad : Finset (JointCoins K)) :
    ((liftP8Failure (K := K) (F := F) bad).card : ℚ) /
        (Fintype.card (OptimizedProductionChallengeTuple K F) : ℚ) =
      (bad.card : ℚ) / (Fintype.card (JointCoins K) : ℚ) :=
  liftP8Failure_density (K := K) (F := F) bad

theorem io_density {K F : Type} [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F]
    [Nonempty K]
    (bad : Finset (K × K)) :
    ((liftIOFailure (K := K) (F := F) bad).card : ℚ) /
        (Fintype.card (OptimizedProductionChallengeTuple K F) : ℚ) =
      (bad.card : ℚ) / (Fintype.card (K × K) : ℚ) :=
  liftIOFailure_density (K := K) (F := F) bad

theorem timestamp_density {K F : Type} [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F]
    [Nonempty K]
    (bad : Finset K) :
    ((liftTimestampFailure (K := K) (F := F) bad).card : ℚ) /
        (Fintype.card (OptimizedProductionChallengeTuple K F) : ℚ) =
      (bad.card : ℚ) / (Fintype.card K : ℚ) :=
  liftTimestampFailure_density (K := K) (F := F) bad

/-! ## `computeKOfTuple` / `chalValOfTuple` cover all ten coordinates -/

theorem slots_234_are_abc {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [Fintype F] [DecidableEq K] [FiniteDimensional F K]
    (c : OptimizedProductionChallengeTuple K F) :
    computeKOfTuple c 2 = c.2.2.1.eqA ∧
      computeKOfTuple c 3 = c.2.2.1.eqB ∧
      computeKOfTuple c 4 = c.2.2.1.eqC :=
  ⟨computeKOfTuple_eqA c, computeKOfTuple_eqB c, computeKOfTuple_eqC c⟩

theorem abc_live_and_carried :
    Batch357.listReads 2 OptimizedComputeGateBasis.finalExtTransitionGates = true ∧
      Batch357.listReads 3 OptimizedComputeGateBasis.finalExtTransitionGates = true ∧
      Batch357.listReads 4 OptimizedComputeGateBasis.finalExtTransitionGates = true ∧
      Batch357.computeTupleCarried 2 = true ∧
      Batch357.computeTupleCarried 3 = true ∧
      Batch357.computeTupleCarried 4 = true :=
  Batch357.finding_abc_live_and_carried

/-- Soundness still does not price `(a, b, c)`.  Quoted, not restated. -/
def no_soundness_event_over_abc :=
  @Nock.Reified.GateCorrespondenceCompute.op5_evaluation_is_equality_without_abc

/-! ## Round schedule: `(a, b, c)` already share `z`'s round

`nockSampledAfter = ![1,0,0,0,0,1,1,1]`: slots `1,2,3,4` are message `0`.
`inv_gen` is a prover column (role 18 / AIR 92), not a coin —
it is computed after the seed is known, so no column moves rounds. -/

theorem abc_same_round_as_z :
    nockSampledAfter ⟨1, by decide⟩ = 0 ∧
      nockSampledAfter ⟨2, by decide⟩ = 0 ∧
      nockSampledAfter ⟨3, by decide⟩ = 0 ∧
      nockSampledAfter ⟨4, by decide⟩ = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

end Nock.RedTeam.Batch358

#print axioms Nock.RedTeam.Batch358.card_is_ten
#print axioms Nock.RedTeam.Batch358.bound_byte_identical
#print axioms Nock.RedTeam.Batch358.slots_234_are_abc
#print axioms Nock.RedTeam.Batch358.abc_live_and_carried
#print axioms Nock.RedTeam.Batch358.abc_same_round_as_z
#print axioms Nock.RedTeam.Batch358.no_soundness_event_over_abc
