/-
  Nock/RedTeam/Batch377Thm54AcceptedContentOfTraces.lean

  **`AcceptedContent` conjuncts at the
  trace-built strategy.**

  Closed without extra honest-package data:
  * `seed_ne` — from `c ∉ hostileFailureEvent` (`nprSeed_ne_of_good`)
  * `z_eq` — `strategyOfTraces_z_eq` (`rfl` of `ofRawData`)

  Count: **2 of 21**.  The other 19 are named in `openConjuncts`.
  `closedAcceptedContent_of_seed` (extra `hz`) is kept; the fill
  successor is `closedAcceptedContent_of_good`.
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.NockVMROM.Thm54.ProductionP8AcceptedContent
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch377

open scoped Polynomial
open Polynomial
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Closed half: `seed_ne` and `z_eq` of `AcceptedContent`. -/
structure ClosedAcceptedContent
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) : Prop where
  seed_ne : nprSeed c.1 ≠ 0
  z_eq :
    ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) seed_ne (alphaM c.1) c.2.2.2.lambda).challenges.z =
      nprSeed c.1

theorem closedAcceptedContent_of_seed
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0) :
    ClosedAcceptedContent P Qc Qm c h where
  seed_ne := hz
  z_eq := strategyOfTraces_z_eq P Qc Qm c h hz

/-- Fill successor: `seed_ne` from the priced zero-seed lift. -/
theorem closedAcceptedContent_of_good
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hgood : c ∉ hostileFailureEvent P Qc Qm) :
    ClosedAcceptedContent P Qc Qm c h :=
  closedAcceptedContent_of_seed P Qc Qm c h
    (seed_ne_of_not_hostile P Qc Qm c hgood)

/-- Open `AcceptedContent` conjuncts at the built strategy.  Count 19. -/
def openConjuncts : List String :=
  ["computeRows", "memoryRows", "vcomp", "vmem", "ln_chain",
    "mem_icur_chain", "mem_first_counts", "mem_first_indicator",
    "mem_first_ipre", "mem_last_icur", "io", "public_subject",
    "public_formula", "public_result", "computeTopology",
    "memoryTopology", "axisStructural", "rootBoundary",
    "structuralChecks"]

theorem openConjuncts_length : openConjuncts.length = 19 := by
  decide

theorem closed_count : 21 - openConjuncts.length = 2 := by
  decide

end

end Nock.RedTeam.Batch377

#print axioms Nock.RedTeam.Batch377.closedAcceptedContent_of_seed
#print axioms Nock.RedTeam.Batch377.closedAcceptedContent_of_good
#print axioms Nock.RedTeam.Batch377.openConjuncts_length
