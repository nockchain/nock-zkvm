/-
  Nock/RedTeam/Batch388Thm54OpenConjunctsTransfer.lean

  **Assembly, honest count 8/21.**

  `openConjuncts` shrinks by the six names actually closed in this
  lane (`vcomp`, `ln_chain`, `computeRows`, `mem_first_ipre`,
  `mem_last_icur`, `mem_icur_chain`).  Starting 2/21 + 6 = **8/21**.
  Target ≥12/21 after step 3 was missed: `vmem` / `memoryRows` are
  wrap-blocked (Vmem case (b), live `recordExponent := 0` writes
  `ts := 1`); `mem_first_counts` / `mem_first_indicator` have no
  deployed first-row pin on roles 3/4.

  Eight-field sister (not twelve).
-/
import Lean
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.RedTeam.Batch377Thm54AcceptedContentOfTraces
import Nock.RedTeam.Batch386Thm54ComputeConjuncts
import Nock.RedTeam.Batch387Thm54MemoryConjuncts
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch388

open Lean Meta Elab Command
open scoped Polynomial
open Polynomial
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.Framework
open MonolithicRAP
open Nock.RedTeam.Batch377
open Nock.RedTeam.Batch386
open Nock.RedTeam.Batch387

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Count 13. -/
def openConjuncts : List String :=
  ["memoryRows", "vmem", "mem_first_counts", "mem_first_indicator",
    "io", "public_subject", "public_formula", "public_result",
    "computeTopology", "memoryTopology", "axisStructural", "rootBoundary",
    "structuralChecks"]

theorem openConjuncts_length : openConjuncts.length = 13 := by decide

theorem closed_count : 21 - openConjuncts.length = 8 := by decide

def closedNames : List String :=
  ["seed_ne", "z_eq", "vcomp", "ln_chain", "computeRows",
    "mem_first_ipre", "mem_last_icur", "mem_icur_chain"]

theorem closedNames_length : closedNames.length = 8 := by decide

/-- Eight-field sister: the two fill closes plus the six transfer closes. -/
structure ClosedAcceptedContentTransfer
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc))
    (hsatM : RAP.SatisfiesWithPreprocessing P.memoryChip Qm) : Prop where
  seed_z : ClosedAcceptedContent P Qc Qm c h
  compute : ClosedComputeConjuncts P Qc Qm c h hz hsatC
  memory : ClosedMemoryScalarConjuncts P Qc Qm c h hz hsatM

theorem closedAcceptedContentTransfer_of_accepted
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc))
    (hsatM : RAP.SatisfiesWithPreprocessing P.memoryChip Qm) :
    ClosedAcceptedContentTransfer P Qc Qm c h hz hsatC hsatM where
  seed_z := closedAcceptedContent_of_seed P Qc Qm c h hz
  compute := closedComputeConjuncts_of_accepted P Qc Qm c h hz hsatC
  memory := closedMemoryScalarConjuncts_of_accepted P Qc Qm c h hz hsatM

end

/-- Constant-walk: `strategyOfTraces` / `execOfTraces` reach the
trace-built labels and do not reach the package strategy. -/
def valueDirect (env : Environment) (root : Name) : Array Name :=
  match env.find? root with
  | some ci =>
    match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants
    | none => #[]
  | none => #[]

def STRATEGY : Name :=
  ``Nock.NockVMROM.Thm54.StrategyOfTracesCore.strategyOfTraces

def EXEC : Name :=
  ``Nock.NockVMROM.Thm54.ExecOfTraces.execOfTraces

def LBLC : Name :=
  ``Nock.NockVMROM.Thm54.ExecOfTraces.lblC

def LBLM : Name :=
  ``Nock.NockVMROM.Thm54.ExecOfTraces.lblM

def VERIFIER : Name :=
  ``Nock.NockVMROM.Thm54.StrategyOfTracesCore.verifierOfTraces

run_cmd do
  let env ← getEnv
  let s := valueDirect env STRATEGY
  let e := valueDirect env EXEC
  unless e.contains LBLC do
    throwError "execOfTraces value does not reach lblC"
  unless e.contains LBLM do
    throwError "execOfTraces value does not reach lblM"
  unless s.contains VERIFIER do
    throwError "strategyOfTraces value does not reach verifierOfTraces"
  logInfo m!"Batch388 walk: strategyOfTraces → verifierOfTraces; execOfTraces → lblC/lblM"

end Nock.RedTeam.Batch388

#print axioms Nock.RedTeam.Batch388.closedAcceptedContentTransfer_of_accepted
#print axioms Nock.RedTeam.Batch388.closed_count
#print axioms Nock.RedTeam.Batch388.openConjuncts_length
