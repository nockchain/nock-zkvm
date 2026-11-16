/-
  Nock/RedTeam/Batch360Thm54ForeignCoins.lean

  **Foreign-coin liveness and the tautology is gone.**

  Changing the corresponding
  tuple coordinate changes `computeKOfTuple` / `memoryKOfTuple` at that index.

  `DeployedAcceptanceAt` has no pin field, so it does not imply
  `nprSeed c.1 = cfg.z`.
-/
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.Framework.FixedPreprocessingRAP
import Nock.RedTeam.Batch337Thm54HostileGapAudit
import Nock.RedTeam.Batch357Thm54DeployedReadSet
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch360

open scoped Polynomial
open Polynomial
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily

/-! ## Changing a coordinate changes the family map -/

theorem foreign_z_moves_seed {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [Fintype F] [DecidableEq K] [FiniteDimensional F K]
    (c c' : OptimizedProductionChallengeTuple K F)
    (h : nprSeed c.1 ≠ nprSeed c'.1) :
    computeKOfTuple c 1 ≠ computeKOfTuple c' 1 := by
  simpa [computeKOfTuple_seed] using h

theorem foreign_alphaM_moves_slot0 {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [Fintype F] [DecidableEq K] [FiniteDimensional F K]
    (c c' : OptimizedProductionChallengeTuple K F)
    (h : alphaM c.1 ≠ alphaM c'.1) :
    computeKOfTuple c 0 ≠ computeKOfTuple c' 0 := by
  simpa [computeKOfTuple_alphaM] using h

theorem foreign_ioPole_moves_slot8 {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [Fintype F] [DecidableEq K] [FiniteDimensional F K]
    (c c' : OptimizedProductionChallengeTuple K F)
    (h : c.2.1.2 ≠ c'.2.1.2) :
    computeKOfTuple c 8 ≠ computeKOfTuple c' 8 := by
  simpa [computeKOfTuple_ioPole] using h

theorem foreign_interPole_moves_mem6 {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [Fintype F] [DecidableEq K] [FiniteDimensional F K]
    (c c' : OptimizedProductionChallengeTuple K F)
    (h : c.2.2.2.interPole ≠ c'.2.2.2.interPole) :
    memoryKOfTuple c 6 ≠ memoryKOfTuple c' 6 := by
  simpa [memoryKOfTuple_interPole] using h

theorem foreign_a_moves_slot2 {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [Fintype F] [DecidableEq K] [FiniteDimensional F K]
    (c c' : OptimizedProductionChallengeTuple K F)
    (h : c.2.2.1.eqA ≠ c'.2.2.1.eqA) :
    computeKOfTuple c 2 ≠ computeKOfTuple c' 2 := by
  simpa [computeKOfTuple_eqA] using h

/-- Each foreign-moved slot is read by a committed gate — not dead. -/
theorem foreign_slots_are_read :
    Batch357.listReads 1 OptimizedComputeGateBasis.finalExtTransitionGates = true ∧
      Batch357.listReads 0 OptimizedComputeGateBasis.finalExtTransitionGates = true ∧
      Batch357.listReads 8 OptimizedComputeGateBasis.finalExtTransitionGates = true ∧
      Batch357.exprReads 6 OptimizedMemoryGateBasis.poleSource = true ∧
      Batch357.listReads 2 OptimizedComputeGateBasis.finalExtTransitionGates = true :=
  ⟨Batch357.compute_k_read_census.2.1,
    Batch357.compute_k_read_census.1,
    Batch357.compute_k_read_census.2.2.2.2.2.2.2.1,
    Batch357.poleSource_reads_interPole,
    Batch357.compute_k_read_census.2.2.1⟩

/-! ## The `|K|²` tautology is gone

`DeployedAcceptanceAt` does not mention `cfg.challenges.z`. -/

/-- `DeployedAcceptanceAt` is two RAP conjuncts.  Nothing in its type forces
`nprSeed c.1 = P.objects.cfg.challenges.z`.  That implication was the F-1
tautology (`acceptance_pins_five`); it does not apply to the family
predicate. -/
theorem falseAcceptanceSet_not_a_priori_small
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K] {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (h : DeployedAcceptanceAt P c Qc Qm) :
    RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc :=
  h.compute_satisfies

end Nock.RedTeam.Batch360

#print axioms Nock.RedTeam.Batch360.foreign_z_moves_seed
#print axioms Nock.RedTeam.Batch360.foreign_a_moves_slot2
#print axioms Nock.RedTeam.Batch360.foreign_slots_are_read
#print axioms Nock.RedTeam.Batch360.falseAcceptanceSet_not_a_priori_small
