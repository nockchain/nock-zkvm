/-
  Nock/RedTeam/Batch384Thm54HostileClaimFill.lean

  **Semantic conclusion, not 21/21.**

  `acceptedContent_of_deployed` is **not** inhabited (`openConjuncts`
  still 19).  Constant walk: `strategyOfTraces` / `execOfTraces` reach
  `Qc`/`Qm` and do **not** reach `P.strategy`, `P.objects`,
  `P.optimized.census`, `P.walkFamily`.
-/
import Lean
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.RedTeam.Batch377Thm54AcceptedContentOfTraces
import Nock.RedTeam.Batch378Thm54HostileClaimOfTraces
import Nock.RedTeam.Batch380Thm54OpenConjunctsFill

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch384

open Lean Meta Elab Command
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.RedTeam.Batch378

theorem still_open_19 : Nock.RedTeam.Batch380.openConjuncts.length = 19 :=
  Nock.RedTeam.Batch380.openConjuncts_length

theorem still_closed_2 : 21 - Nock.RedTeam.Batch380.openConjuncts.length = 2 :=
  Nock.RedTeam.Batch380.closed_count

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
  logInfo m!"Batch384 walk: strategyOfTraces → verifierOfTraces; execOfTraces → lblC/lblM"

#check HostileClaimHoldsOfDeployed

end Nock.RedTeam.Batch384

#print axioms Nock.RedTeam.Batch384.still_open_19
#print axioms Nock.RedTeam.Batch384.still_closed_2
