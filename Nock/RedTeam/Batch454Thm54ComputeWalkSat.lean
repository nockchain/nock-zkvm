/-
  Nock/RedTeam/Batch454Thm54ComputeWalkSat.lean

  **`DeployedAcceptanceAt ⇒` walk gates vanish.**

  The in-gate walk endpoints (`finalMaskedWalkAccInit`, `finalMaskedWalkLn1`,
  `finalMaskedWalkCount1`, `finalMaskedWalkOut`) and the packed walk
  transitions sit in `CorrectedComputeSourceObligations`.  Family-chip
  acceptance supplies them at every row (`FamilyComputeRows.row_obligations_at`).
  `Batch438.label_rlc_is_decoded_label` is the hostile `cur(i+1)` identity
  at the decoded successor label.

  The K-side compute topology RAP is **not** retired.
-/
import Nock.Walk
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
import Nock.NockVMROM.Thm54.ComputeWalkLabel
import Nock.RedTeam.Batch438Thm54InGateWalkReceipts
import Nock.RedTeam.Batch453Thm54SeedWiring
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch454

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.RedTeam.Batch438
open Nock.RedTeam.Batch453
open Nock.Framework
open OptimizedComputeHostileAccumulator
open MonolithicRAP

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Chip acceptance implies the degree-4 walk-init gate vanishes. -/
theorem deployed_walkAccInit_zero
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hAcc : DeployedAcceptanceAt P c Qc Qm)
    (i : Fin (rows P)) :
    ∀ t ∈ correctedEndpoint4, t.eval (rowEnvAt P c Qc i) = 0 :=
  walkAccInit_vanishes_from_chip P c Qc hAcc.compute_satisfies i

/-- Chip acceptance implies the degree-2 walk endpoints vanish
    (`ln1`, `count1`, `out`, `accInit`, `accTerminal`, `lnInit`). -/
theorem deployed_endpoint2_zero
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hAcc : DeployedAcceptanceAt P c Qc Qm)
    (i : Fin (rows P)) :
    ∀ t ∈ correctedEndpoint2, t.eval (rowEnvAt P c Qc i) = 0 :=
  endpoint2_vanishes_from_chip P c Qc hAcc.compute_satisfies i

/-- Hostile successor-row identity, reused: `cur(i+1)` is `RLC^γ` of the
    decoded label (`Batch438.label_rlc_is_decoded_label`). -/
theorem successor_cur_is_decoded_label (env : Env K) (st : ComputeTable.State)
    (hsel : ∀ st', env.traceNext (Nock.Reified.opCol st') =
      if st' = st then 1 else 0) :
    (ComputeWalkLabel.labelRLC ComputeWalkLabel.nextReader).eval env =
      Walk.rlc (env.chal 10)
        (ComputeTable.labelVecOfPub
          (Nock.Reified.pubOfState
            (Env.ofSubst OptimizedComputeSubstitution.computeSubst
              (ComputeWalkLabel.shiftNext env)) st)) :=
  label_rlc_is_decoded_label env st hsel

def WALKSAT_ASSEMBLY : List String :=
  ["WalkSat.ln1 from finalMaskedWalkLn1",
    "WalkSat.count1 from finalMaskedWalkCount1",
    "WalkSat.accInit from finalMaskedWalkAccInit + seedOfClaim",
    "WalkSat.accStep from walkAccStep + label_rlc_is_decoded_label"]

theorem walkSat_assembly_length : WALKSAT_ASSEMBLY.length = 4 := by decide

end

end Nock.RedTeam.Batch454

#print axioms Nock.RedTeam.Batch454.deployed_walkAccInit_zero
#print axioms Nock.RedTeam.Batch454.successor_cur_is_decoded_label
