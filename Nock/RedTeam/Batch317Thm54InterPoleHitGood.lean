/-
  Nock/RedTeam/Batch317Thm54InterPoleHitGood.lean

  Acceptance pins `(ioGamma, interPole)` to the package's sampled coins, and
  `sampled_inter_event_good_of_historical` keeps that pair out of
  `IOFailureEvent` on the intermediate lists.  `Inputs.interPoleHitGood` is
  the assignment-level twin of `ioPoleHitGood`.

  Paper at source: the paper.
-/
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.BuildableChips
import Nock.NockVMROM.Thm54.BuildablePackage
import Nock.NockVMROM.Thm54.FiniteFieldIOSoundness
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.RedTeam.Batch317

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open scoped Polynomial

/-- `Inputs` carries the honest internal pole-hit, twin of `ioPoleHitGood`. -/
theorem inputs_carry_interPoleHitGood
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    {E : BuildableNockExecution F K} (I : Inputs E) :
    I.memoryExtensionFold ∉
      FiniteIO.IOPoleHitEvent (executionInterRecords E) I.ioCoins.gamma :=
  I.interPoleHitGood

/-- Honest acceptance implies the tuple's `(γ, interPole)` is outside the
intermediate `IOFailureEvent`.  Not a capstone hypothesis. -/
theorem sampled_inter_good_of_acceptance
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hC : P.optimized.family.problem.exec.CprimeCoherent) :
    (c.2.1.1, c.2.2.2.interPole) ∉
      FiniteIO.IOFailureEvent P.optimized.sampled.interRecords :=
  P.sampled_inter_event_good_of_historical Qc Qm c hacc hC

end Nock.RedTeam.Batch317

#print axioms Nock.RedTeam.Batch317.inputs_carry_interPoleHitGood
#print axioms Nock.RedTeam.Batch317.sampled_inter_good_of_acceptance
