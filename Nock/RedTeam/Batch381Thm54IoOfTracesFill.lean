/-
  Nock/RedTeam/Batch381Thm54IoOfTracesFill.lean

  **Fill `ioOfTraces` / `familyDataOfTraces`.**

  Both defs mention `Qc`/`Qm` in their **bodies** (F1).  `io` of
  `AcceptedContent` stays open: `optimizedFullStrict_hostile_LIO` is
  about `hostileRequests`/`hostileResponses`, while `AcceptedContent.io`
  is `IO.LIO` of `specializedExec.derivedRequestIO` /
  `derivedResponseIO`.  Remaining named hyps of the hostile-LIO
  theorem (`hchar`, `hKp`, `hKreq`, `hKresp`) plus the identification
  of derived IO with the hostile lists.
-/
import Lean
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch381

open Lean Meta Elab Command
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps

def valueDirect (env : Environment) (root : Name) : Array Name :=
  match env.find? root with
  | some ci =>
    match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants
    | none => #[]
  | none => #[]

def FAMILY : Name :=
  ``Nock.NockVMROM.Thm54.StrategyOfTracesCore.familyDataOfTraces

def IO : Name :=
  ``Nock.NockVMROM.Thm54.StrategyOfTracesCore.ioOfTraces

def ROW : Name :=
  ``Nock.NockVMROM.Thm54.FamilyComputeRows.rowEnvAt

def MEM : Name :=
  ``Nock.NockVMROM.Thm54.FamilyComputeRows.memorySourceEnvAt

/-- `io` remaining hyps: the four `optimizedFullStrict_hostile_LIO`
range/char premises, plus derived-list identification. -/
def ioRemainingHyps : List String :=
  ["hchar", "hKp", "hKreq", "hKresp",
    "derivedRequestIO_eq_hostileRequests",
    "derivedResponseIO_eq_hostileResponses"]

theorem ioRemainingHyps_length : ioRemainingHyps.length = 6 := by
  decide

run_cmd do
  let env ← getEnv
  let f := valueDirect env FAMILY
  let io := valueDirect env IO
  unless f.contains MEM do
    throwError "familyDataOfTraces value does not reach memorySourceEnvAt (Qm column)"
  unless io.contains ROW do
    throwError "ioOfTraces value does not reach rowEnvAt (Qc)"
  unless io.contains MEM do
    throwError "ioOfTraces value does not reach memorySourceEnvAt (Qm)"
  logInfo m!"Batch381 walk: familyDataOfTraces → memorySourceEnvAt; ioOfTraces → rowEnvAt/memorySourceEnvAt"

#check optimizedFullStrict_hostile_LIO_historical

end Nock.RedTeam.Batch381

#print axioms Nock.RedTeam.Batch381.ioRemainingHyps_length
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.optimizedFullStrict_hostile_LIO_historical
