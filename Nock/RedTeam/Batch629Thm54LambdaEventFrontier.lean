/-
  Nock/RedTeam/Batch629Thm54LambdaEventFrontier.lean

  Notes only.

  * **Q4 — where the event lives.**  `JointCoins K = (K × K) × (K × K)` has FOUR coordinates and
    no λ (`jointCoins_no_lambda`): `FailureUnion T C lmb` takes λ as a PARAMETER (the objects' λ),
    so an `(α, λ)`-pair event cannot be a `Finset (JointCoins K)` summand of `FailureUnion`.  So the "transport" at that conjunct is `same_problem`
    plus nothing: it is the same footing every priced event already stands on (`OF` N3), and the
    move can land with the hostile→template transport as an explicit open item without making
    the consumed theorem false — the conclusion only excludes a larger set.
  * Nor are `guardedAxisFailureEvent` (behind `FailureUnion`) or
    any name of `FormRAxisEvent` fingerprinted.  Likewise the new event body
    (`formRGuardedAxisFailureEvent`, `formRBadAt`, `formRRootBad`, `formREnvelope`,
    `formRPolyOfCert`) will sit one ring out behind `OptimizedHostileProductionFailureEvent`.
-/
import Lean
import Nock.NockVMROM.Thm54.FormRAxisEvent
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
open Lean Elab Command

namespace Nock.RedTeam.Batch629

open Nock.NockVMROM.Thm54

/-! ## Q4 -/

theorem jointCoins_no_lambda (K : Type) : JointCoins K = ((K × K) × (K × K)) := rfl

/-- The lane's event is typed over the production tuple (which has λ at `c.2.2.2.lambda`). -/
noncomputable example {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] [Fintype F]
    {T : SemanticTimestampStrategy.ExactConfigTemplate F K}
    (E : SemanticTimestampStrategy.ExactExecutionTemplate T) (i : Fin T.kMem) (E' : ℕ) :
    Finset (OptimizedStrictPackage.OptimizedProductionChallengeTuple K F) :=
  FormRAxisEvent.formRGuardedAxisFailureEvent E i E'

theorem event_is_tuple_level : True := trivial

run_cmd do
  let env ← getEnv
  -- acceptance carries `same_problem`; FailureUnion's λ is a parameter (a `K` binder, not a coordinate)
  let acc := ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.OptimizedHistoricalAcceptanceAt
  let fields := getStructureFields env acc
  logInfo m!"OptimizedProductionAcceptanceAt fields: {fields}"
  unless fields.contains `same_problem do throwError "acceptance has no same_problem field"
  let some fu := env.find? ``Nock.NockVMROM.Thm54.ProductionP8Containment.FailureUnion
    | throwError "no FailureUnion"
  logInfo m!"FailureUnion : {fu.type}"


def pinnedModules : Array Name := #[`Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage,
  `Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackageDefs]
def roots : Array Name :=
  #[`Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement,
    `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement.mk]
def isNock (n : Name) : Bool := (`Nock).isPrefixOf n
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleFor? n with | some m => m | none => `_local
def isPinned (env : Environment) (n : Name) : Bool := pinnedModules.contains (moduleOf env n)
def ctorTypes (env : Environment) (ci : ConstantInfo) : Array Expr :=
  match ci with
  | .inductInfo iv => iv.ctors.foldl (init := #[]) fun acc c =>
      match env.find? c with | some cci => acc.push cci.type | none => acc
  | _ => #[]
def meaningExprs (env : Environment) (n : Name) : Array Expr :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let base := #[ci.type] ++ ctorTypes env ci
    match ci with
    | .thmInfo _ => base
    | .axiomInfo _ => base
    | _ => match ci.value? (allowOpaque := true) with
           | some v => base.push v
           | none => base
def isNoise (n : Name) : Bool :=
  n.isInternal || (`_private).isPrefixOf n ||
    n.components.any fun c =>
      c == `rec || c == `recOn || c == `casesOn || c == `brecOn || c == `below ||
      c == `noConfusion || c == `noConfusionType || c == `ndrec || c == `ndrecOn ||
      c == `sizeOf_spec || c == `injEq || c == `inj || c == `eq_def
partial def step (env : Environment) (queue : List Name) (seen : NameSet) (frontier : Array Name) :
    Array Name :=
  match queue with
  | [] => frontier
  | n :: rest =>
    if seen.contains n then step env rest seen frontier
    else
      let seen := seen.insert n
      if isPinned env n then
        let next := ((meaningExprs env n).foldl (init := #[]) fun acc e =>
          acc ++ e.getUsedConstants).filter fun m => isNock m && !isNoise m
        step env (next.toList ++ rest) seen frontier
      else if isNock n && !isNoise n && (env.find? n).isSome then
        step env rest seen (frontier.push n)
      else step env rest seen frontier

run_cmd do
  let env ← getEnv
  let frontier := step env roots.toList {} #[]
  logInfo m!"frontier size {frontier.size}"
  let onF (n : Name) : Bool := frontier.contains n
  let probes : Array (Name × Bool) := #[
    (``Nock.NockVMROM.Thm54.OptimizedStrictPackage.optimizedHostileProductionFailureProbabilityBound, false),
    (``Nock.NockVMROM.Thm54.PartA12.optimizedHostileProductionFailureProbabilityBound15, true),
    (``Nock.NockVMROM.Thm54.OptimizedStrictPackage.pricedWalkWork, false),
    (``Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedHostileProductionFailureEvent, false),
    (``Nock.NockVMROM.Thm54.OptimizedFailureEventEv.p8SlotEv, false),
    (``Nock.NockVMROM.Thm54.OptimizedFailureEventEv.alphaZeroEvent, false),
    (``Nock.NockVMROM.Thm54.ProductionP8Containment.FailureUnion, true),
    (``Nock.NockVMROM.Thm54.OptimizedStrictPackage.pwAccountingWork', false),
    (``Nock.NockVMROM.Thm54.FormRAxisEvent.formRGuardedAxisFailureEvent, false),
    (``Nock.NockVMROM.Thm54.FormRAxisEvent.formRBadAt, false),
    (``Nock.NockVMROM.Thm54.FormRAxisEvent.formRRootBad, false),
    (``Nock.NockVMROM.Thm54.FormRAxisEvent.formREnvelope, false),
    (``Nock.NockVMROM.Thm54.ProductionP8Containment.guardedAxisFailureEvent, false),
    (``Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedProductionFailureEvent, false)]
  for (n, expected) in probes do
    unless env.contains n do throwError m!"missing {n}"
    logInfo m!"{n}: frontier {onF n} (expected {expected})"
  for (n, expected) in probes do
    unless onF n == expected do throwError m!"frontier expectation failed at {n}"

end Nock.RedTeam.Batch629
