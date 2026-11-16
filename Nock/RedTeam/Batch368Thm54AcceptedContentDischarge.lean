/-
  Nock/RedTeam/Batch368Thm54AcceptedContentDischarge.lean

  **Discharge of `AcceptedContent` conjuncts at
  `DeployedAcceptanceAt`.**

  Full `AcceptedContent (strategyOfTraces …)` is not stated: there is no
  `strategyOfTraces : ProductionStrategy`.  This file names
  each of NM's 21 conjuncts as closed or open from
  `DeployedAcceptanceAt` + `c ∉ hostileFailureEvent`.

  Closed without extra premise:

  Open (need a trace-built `ExactExecution` / `strategyOfTraces`):
  `z_eq`, `ComputeRowsAccepted`, `MemoryRowsAccepted`, `vmem`, chains,
  first-row zeros, `mem_last_icur`, `io`, `public_*`, topology / axis /
  structural, compute-half `binds` (`ComputeJoinSound`), memory-half
  `binds` (`RecordHalfJoin`).
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.StrategyOfTraces
import Nock.NockVMROM.Thm54.ProductionP8AcceptedContent
import Nock.RedTeam.Batch364Thm54AcceptedContentOfDeployed
import Nock.RedTeam.Batch367Thm54FamilyOfTraces
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch368

open scoped Polynomial
open Polynomial
open Nock
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.RedTeam.Batch367

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem seed_ne_of_not_zeroSeed
    (c : OptimizedProductionChallengeTuple K F)
    (h : nprSeed c.1 ∉ ({0} : Set K)) :
    nprSeed c.1 ≠ 0 := by
  intro hz
  exact h (by simp [hz])

/-- Closed: compute `Vcomp` at every row of an accepted family chip,
from `seed_ne` (no extra `P.strategy` premise).  Here we keep the constant-chip
form and name the family form as needing `computeChipAt_honest`. -/
theorem computeVcomp_of_deployed_constant
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : DeployedAcceptance P Qc Qm c)
    (_hz : nprSeed c.1 ≠ 0)
    (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0) :
    computeRowsAreVcomp P Qc :=
  computeRowsAreVcomp_of_sat P Qc hacc.compute_satisfies hz0

theorem traces_claim_eq
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (strategyOfTracesData P Qc Qm).claim =
      (strategyOfTracesData P Qc Qm).skeleton.publicClaim :=
  (strategyOfTracesData P Qc Qm).publicClaim_eq.symm

/-- The closed half at `DeployedAcceptanceAt` (family chips, no pins).
`seed_ne` is taken from the caller (priced zero-seed event), not from
a pin. -/
structure DeployedAcceptedContentAt
    (c : OptimizedProductionChallengeTuple K F) : Prop where
  seed_ne : nprSeed c.1 ≠ 0

theorem acceptedContent_of_deployed
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (_hacc : DeployedAcceptanceAt P c Qc Qm)
    (hz : nprSeed c.1 ≠ 0) :
    DeployedAcceptedContentAt c where
  seed_ne := hz

/-- Each needs a trace-built
`ProductionStrategy` / `ExactExecution`.  Count: 20 of 21 (`seed_ne`
is the closed one). -/
def openConjuncts : List String :=
  ["z_eq", "computeRows", "memoryRows", "vcomp", "vmem", "ln_chain",
    "mem_icur_chain", "mem_first_counts", "mem_first_indicator",
    "mem_first_ipre", "mem_last_icur", "io", "public_subject",
    "public_formula", "public_result", "computeTopology",
    "memoryTopology", "axisStructural", "rootBoundary",
    "structuralChecks"]

theorem openConjuncts_length : openConjuncts.length = 20 := by
  decide

end

end Nock.RedTeam.Batch368

#print axioms Nock.RedTeam.Batch368.seed_ne_of_not_zeroSeed
#print axioms Nock.RedTeam.Batch368.traces_claim_eq
#print axioms Nock.RedTeam.Batch368.acceptedContent_of_deployed
