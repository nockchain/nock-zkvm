/-
  Nock/RedTeam/Batch920Thm54Part2bLiftMeasure.lean

  Nothing consumes this.

  For each statement ingredient of the restored `p8` the transitive `Nock.*` constant reach (types and values,
  `allowOpaque := true`) is printed by MODULE, with the DIRECT package projections it reads.
-/
import Lean
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.StrategyOfTraces
import Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

open Lean

namespace Nock.RedTeam.Batch920

def isNock (n : Name) : Bool := (`Nock).isPrefixOf n

partial def reach (env : Environment) (queue : List Name) (seen : NameSet) : NameSet :=
  match queue with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reach env rest seen
    else
      match env.find? n with
      | none => reach env rest seen
      | some ci =>
        let es := #[ci.type] ++ (match ci.value? (allowOpaque := true) with
          | some v => #[v] | none => #[])
        let next := (es.foldl (init := #[]) fun acc e => acc ++ e.getUsedConstants).filter isNock
        reach env (next.toList ++ rest) (seen.insert n)

def PKG : Name := `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage

def ingredients : List Name := [
  `Nock.NockVMROM.Thm54.StrategyOfTracesCore.strategyOfTraces,
  `Nock.NockVMROM.Thm54.StrategyOfTracesCore.verifierOfTraces,
  `Nock.NockVMROM.Thm54.StrategyOfTracesCore.wrapMemoryLabel,
  `Nock.NockVMROM.Thm54.ExecOfTraces.TracesWalkHyps,
  `Nock.NockVMROM.Thm54.ExecOfTraces.execOfTraces,
  `Nock.NockVMROM.Thm54.StrategyOfTraces.decodedSkeletonOf,
  `Nock.NockVMROM.Thm54.StrategyOfTraces.publicClaimOf,
  `Nock.NockVMROM.Thm54.StrategyOfTraces.computeJoinOf,
  `Nock.NockVMROM.Thm54.StrategyOfTraces.typedMemoryForest]

end Nock.RedTeam.Batch920

open Nock.RedTeam.Batch920 in
run_cmd do
  let env ← Lean.getEnv
  for ing in ingredients do
    unless (env.find? ing).isSome do
      Lean.logInfo s!"MISSING {ing}"
      continue
    let r := reach env [ing] {}
    let mut mods : NameSet := {}
    let mut pkgProj : Array Name := #[]
    let mut count := 0
    for n in r.toList do
      count := count + 1
      match env.getModuleFor? n with
      | some m => mods := mods.insert m
      | none => pure ()
      if PKG.isPrefixOf n then pkgProj := pkgProj.push n
    Lean.logInfo s!"INGREDIENT {ing}: reach {count} constants over {mods.size} modules; package projections {pkgProj.size}"
    for m in mods.toList do
      Lean.logInfo s!"  MOD {ing} {m}"
    for p in pkgProj.qsort (fun a b => a.toString < b.toString) do
      Lean.logInfo s!"  PKGPROJ {ing} {p}"
