/-
  Nock/RedTeam/Batch941Thm54LiftStrategyReach.lean

  Nothing consumes this.

  * **(A) import walk.**  The transitive import closure of `StrategyOfTracesLift` (read off the
    environment's module headers) does not contain `OptimizedStrictFullPackage`, nor any module that
    imports it.  Positive control: the closures of the originals' modules `ExecOfTraces` and
    `StrategyOfTracesCore` do contain it.
  * **(B) constant walk.**  The transitive constant reach (types, values with `allowOpaque := true`,
    constructor types) of the lifted `strategyOfTraces`, `TracesWalkHyps`, `verifierOfTraces`,
    `decodedSkeletonOf` reaches no constant of a module at or above the pin, and in particular not
    `OptimizedFullStrictNockVMROMPackage`.  Positive control: the same walk from the originals
    reaches the package type and a nonempty above-pin set.
  * **(C) the vacuity check of `Batch940` §Z, re-run on a deliberately vacuous receipt.**  The
    statement `lifted = lifted` is flagged (the original is absent), and a genuine receipt passes.
  Every check throws on failure, so the module builds only if all hold.
-/
import Lean
import Nock.NockVMROM.Thm54.StrategyOfTracesLift
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.RedTeam.Batch940Thm54LiftStrategyReceipts
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

open Lean

namespace Nock.RedTeam.Batch941

def PIN : Name := `Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
def PKG : Name := `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage
def LIFTMOD : Name := `Nock.NockVMROM.Thm54.StrategyOfTracesLift

def aboveSet (env : Environment) : NameSet := Id.run do
  let names := env.header.moduleNames
  let data := env.header.moduleData
  let mut above : NameSet := {}
  for i in [0:names.size] do
    let m := names[i]!
    if m == PIN || data[i]!.imports.any (fun imp => above.contains imp.module) then
      above := above.insert m
  return above

/-- The transitive import closure of module `m`, read off the module headers. -/
partial def importClosure (env : Environment) (queue : List Name) (seen : NameSet) : NameSet :=
  match queue with
  | [] => seen
  | m :: rest =>
    if seen.contains m then importClosure env rest seen
    else
      match env.header.moduleNames.idxOf? m with
      | none => importClosure env rest (seen.insert m)
      | some i =>
        let imps := (env.header.moduleData[i]!.imports.map (·.module)).toList
        importClosure env (imps ++ rest) (seen.insert m)

def isNock (n : Name) : Bool :=
  (`Nock).isPrefixOf n || ((`_private).isPrefixOf n && (n.toString.splitOn ".Nock.").length > 1)

partial def constReach (env : Environment) (queue : List Name) (seen : NameSet) : NameSet :=
  match queue with
  | [] => seen
  | n :: rest =>
    if seen.contains n then constReach env rest seen
    else
      match env.find? n with
      | none => constReach env rest seen
      | some ci =>
        let es := #[ci.type] ++ (match ci.value? (allowOpaque := true) with
          | some v => #[v] | none => #[])
        let es := es ++ (match ci with
          | .inductInfo iv => iv.ctors.foldl (init := #[]) fun acc c =>
              match env.find? c with | some cc => acc.push cc.type | none => acc
          | _ => #[])
        let next := (es.foldl (init := #[]) fun acc e => acc ++ e.getUsedConstants).filter isNock
        constReach env (next.toList ++ rest) (seen.insert n)

def aboveConsts (env : Environment) (above : NameSet) (s : NameSet) : List Name :=
  s.toList.filter fun n => match env.getModuleFor? n with
    | some m => above.contains m | none => false

/-- `Batch940` §Z's per-receipt test: the statement names the lifted and the original constant, the
two differ and the original is not in the lifted module.  `none` = passes. -/
def receiptFlaw (env : Environment) (receipt lifted original : Name) : Option String :=
  match env.find? receipt with
  | none => some "missing"
  | some ci =>
    let used := ci.type.getUsedConstants
    if !used.contains lifted then some "lifted absent"
    else if !used.contains original then some "original absent (vacuous)"
    else if lifted == original then some "lifted = original"
    else if env.getModuleFor? original == some LIFTMOD then some "original in the lifted module"
    else none

end Nock.RedTeam.Batch941

namespace Nock.RedTeam.Batch941.Control

open scoped Polynomial
open Polynomial
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-- It is true, and it is NOT a receipt; (C) must flag it. -/
theorem vacuous_strategyOfTraces_eq (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized Qc Qm c) :
    StrategyOfTracesLift.strategyOfTraces P.optimized P.stateTagChar Qc Qm c h =
      StrategyOfTracesLift.strategyOfTraces P.optimized P.stateTagChar Qc Qm c h := rfl

end Nock.RedTeam.Batch941.Control

open Nock.RedTeam.Batch941 in
run_cmd do
  let env ← getEnv
  let above := aboveSet env
  -- (A) import walk + positive control
  let liftClosure := importClosure env [LIFTMOD] {}
  let bad := liftClosure.toList.filter above.contains
  unless bad.isEmpty do throwError s!"(A) the lift's import closure meets the pin: {bad}"
  if liftClosure.contains PIN then throwError "(A) the lift imports the pinned file"
  logInfo s!"(A) import closure of {LIFTMOD}: {liftClosure.size} modules; pinned file absent; modules at/above the pin in it: 0"
  for m in [`Nock.NockVMROM.Thm54.ExecOfTraces, `Nock.NockVMROM.Thm54.StrategyOfTracesCore] do
    let cl := importClosure env [m] {}
    unless cl.contains PIN do throwError s!"(A) positive control FAILED: {m}'s closure lacks the pin"
    logInfo s!"(A) positive control: import closure of {m}: {cl.size} modules; pinned file PRESENT"
  -- (B) constant walk + positive control
  let lifted : List Name := [
    `Nock.NockVMROM.Thm54.StrategyOfTracesLift.strategyOfTraces,
    `Nock.NockVMROM.Thm54.StrategyOfTracesLift.TracesWalkHyps,
    `Nock.NockVMROM.Thm54.StrategyOfTracesLift.verifierOfTraces,
    `Nock.NockVMROM.Thm54.StrategyOfTracesLift.decodedSkeletonOf]
  let r := constReach env lifted {}
  let ab := aboveConsts env above r
  unless ab.isEmpty do throwError s!"(B) the lift reaches above-pin constants: {ab}"
  if r.contains PKG then throwError "(B) the lift reaches OptimizedFullStrictNockVMROMPackage"
  logInfo s!"(B) constant reach of the lifted roots: {r.size} constants; at/above the pin: 0; OptimizedFullStrictNockVMROMPackage: absent"
  let originals : List Name := [
    `Nock.NockVMROM.Thm54.StrategyOfTracesCore.strategyOfTraces,
    `Nock.NockVMROM.Thm54.ExecOfTraces.TracesWalkHyps,
    `Nock.NockVMROM.Thm54.StrategyOfTracesCore.verifierOfTraces,
    `Nock.NockVMROM.Thm54.StrategyOfTraces.decodedSkeletonOf]
  let r0 := constReach env originals {}
  let ab0 := aboveConsts env above r0
  if ab0.isEmpty || !r0.contains PKG then
    throwError "(B) positive control FAILED: the originals' reach shows nothing above the pin"
  logInfo s!"(B) positive control: constant reach of the originals: {r0.size} constants; at/above the pin: {ab0.length}; OptimizedFullStrictNockVMROMPackage: PRESENT"
  -- (C) the vacuity check fires on a vacuous receipt and passes a genuine one
  let lift : Name := `Nock.NockVMROM.Thm54.StrategyOfTracesLift.strategyOfTraces
  let orig : Name := `Nock.NockVMROM.Thm54.StrategyOfTracesCore.strategyOfTraces
  match receiptFlaw env `Nock.RedTeam.Batch941.Control.vacuous_strategyOfTraces_eq lift lift with
  | none => throwError "(C) the vacuity check did NOT flag lifted = lifted"
  | some why => logInfo s!"(C) vacuous receipt (lifted vs lifted) flagged: {why}"
  match receiptFlaw env `Nock.RedTeam.Batch941.Control.vacuous_strategyOfTraces_eq lift orig with
  | none => throwError "(C) the vacuity check passed a receipt that does not name the original"
  | some why => logInfo s!"(C) vacuous receipt (claimed against the original) flagged: {why}"
  match receiptFlaw env `Nock.RedTeam.Batch940.strategyOfTraces_eq lift orig with
  | some why => throwError s!"(C) the genuine receipt Batch940.strategyOfTraces_eq was flagged: {why}"
  | none => logInfo "(C) genuine receipt Batch940.strategyOfTraces_eq passes"
