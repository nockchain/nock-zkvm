/-
  Nock/RedTeam/Batch376Thm54StrategyOfTraces.lean

  **`strategyOfTraces : ProductionStrategy`.**

  Inhabited from `Qc`/`Qm` via `ofRawData` / `execOfTraces`.  Not
  `P.strategy`.  One named hyp `TracesBindsHyps` (NL reason 1 `∀ z`
  binds).  `z_eq` is `rfl`.

  Step-6 walk: `strategyOfTraces` / `execOfTraces` values reach `lblC`
  / `rowEnv` (hence `Qc`); NO's `familyOfTraces` value does not.
-/
import Lean
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.RedTeam.Batch367Thm54FamilyOfTraces

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch376

open Lean Meta Elab Command
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.ProductionP8Containment

noncomputable abbrev strategyOfTraces :=
  @Nock.NockVMROM.Thm54.StrategyOfTracesCore.strategyOfTraces

#check strategyOfTraces
#check Nock.NockVMROM.Thm54.StrategyOfTracesCore.strategyOfTraces_z_eq

def valueDirect (env : Environment) (root : Name) : Array Name :=
  match env.find? root with
  | some ci =>
    match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants
    | none => #[]
  | none => #[]

def STRATEGY : Name :=
  ``Nock.NockVMROM.Thm54.StrategyOfTracesCore.strategyOfTraces

def TEMPLATE : Name :=
  ``Nock.NockVMROM.Thm54.StrategyOfTracesCore.execTemplateOfTraces

def WALKS : Name :=
  ``Nock.NockVMROM.Thm54.StrategyOfTracesCore.walksOfTraces

def EXEC : Name :=
  ``Nock.NockVMROM.Thm54.ExecOfTraces.execOfTraces

def LBLC : Name :=
  ``Nock.NockVMROM.Thm54.ExecOfTraces.lblC

def FAMILY : Name :=
  ``Nock.RedTeam.Batch367.familyOfTraces

run_cmd do
  let env ← getEnv
  let t := valueDirect env TEMPLATE
  let w := valueDirect env WALKS
  let e := valueDirect env EXEC
  let f := valueDirect env FAMILY
  unless t.contains EXEC do
    throwError "execTemplateOfTraces value does not reach execOfTraces"
  unless w.contains LBLC do
    throwError "walksOfTraces value does not reach lblC (Qc)"
  unless e.contains LBLC do
    throwError "execOfTraces value does not reach lblC (Qc)"
  if f.contains EXEC || f.contains LBLC then
    throwError "positive control failed: familyOfTraces unexpectedly reaches execOfTraces/lblC"
  logInfo m!"Batch376 walk: execTemplateOfTraces → execOfTraces → lblC; walksOfTraces → lblC; familyOfTraces does not (NO control)"

end Nock.RedTeam.Batch376

#print axioms Nock.NockVMROM.Thm54.StrategyOfTracesCore.strategyOfTraces_z_eq
#print axioms Nock.NockVMROM.Thm54.StrategyOfTracesCore.strategyOfTraces_claim
