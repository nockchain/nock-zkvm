/-
  Nock/RedTeam/Batch657Thm54FormRCoreLiftGraph.lean

  Notes only.

  Both recorded in the report.

* **Check 1, downstream:** per-module digests of the public constants (`name, type hash, def value
    hash`) of the 14 direct importers of the five moved modules that are not themselves moved, at `PL`
    (embedded) — equal here.

  -- the paper
-/
import Lean
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.FormRAxisEvent
import Nock.RedTeam.Batch558Thm54FormRJoin
import Nock.RedTeam.Batch555Thm54PwCertificate
import Nock.RedTeam.Batch576Thm54FormRNegatives
import Nock.RedTeam.Batch577Thm54FormRCompleteness
import Nock.RedTeam.Batch581Thm54FormREvent
import Nock.RedTeam.Batch582Thm54FormRCompletenessHazard
import Nock.NockVMROM.Thm54.DeployedStaging
import Nock.RedTeam.Batch619Thm54FormRReadSet
import Nock.RedTeam.Batch624Thm54FormREventA4
import Nock.RedTeam.Batch626Thm54FormREventNested
import Nock.RedTeam.Batch628Thm54LambdaEventLift
import Nock.RedTeam.Batch629Thm54LambdaEventFrontier
import Nock.RedTeam.Batch633Thm54LambdaEventUnguarded
import Nock.RedTeam.Batch641Thm54LambdaEventGuarded

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
open Lean Elab Command

namespace Nock.RedTeam.Batch657

/-- Transitive import set of a module, from the loaded header. -/
def importsOf (env : Environment) (root : Name) : Array Name := Id.run do
  let mods := env.header.moduleNames
  let data := env.header.moduleData
  let mut idx : Std.HashMap Name Nat := {}
  for i in [0:mods.size] do idx := idx.insert mods[i]! i
  let mut seen : Std.HashSet Name := {}
  let mut work := [root]
  while true do
    match work with
    | [] => break
    | m :: rest =>
      work := rest
      if seen.contains m then continue
      seen := seen.insert m
      match idx[m]? with
      | some i => for imp in data[i]!.imports do work := imp.module :: work
      | none => pure ()
  return seen.toArray

def forbidden : Array Name := #[
  `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage,
  `Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier,
  `Nock.RedTeam.Batch554Thm54PwFunctional, `Nock.RedTeam.Batch555Thm54PwCertificate,
  `Nock.RedTeam.Batch556Thm54PwEvent, `Nock.RedTeam.Batch557Thm54RangeGadget,
  `Nock.RedTeam.Batch575Thm54FormRMtree]

run_cmd do
  let env ← getEnv
  let fre := importsOf env `Nock.NockVMROM.Thm54.FormRAxisEvent
  logInfo m!"FormRAxisEvent transitive imports: {fre.size}"
  for f in forbidden do
    if fre.contains f then throwError m!"FormRAxisEvent still reaches {f}"
  for p in [`Nock.NockVMROM.Thm54.ProductionP8Containment, `Nock.NockVMROM.Thm54.OptimizedStrictPackage,
      `Nock.NockVMROM.Thm54.FormRCore, `Nock.NockVMROM.Thm54.FormRTemplatePolynomial] do
    unless fre.contains p do throwError m!"positive control: FormRAxisEvent does not reach {p}"
  let ftp := importsOf env `Nock.NockVMROM.Thm54.FormRTemplatePolynomial
  logInfo m!"FormRTemplatePolynomial transitive imports: {ftp.size}"
  for f in forbidden ++ #[`Nock.NockVMROM.Thm54.ProductionP8Containment,
      `Nock.NockVMROM.Thm54.OptimizedStrictPackage] do
    if ftp.contains f then throwError m!"FormRTemplatePolynomial reaches {f}"
  let rt := ftp.filter fun m => (`Nock.RedTeam).isPrefixOf m
  unless rt.isEmpty do throwError m!"FormRTemplatePolynomial reaches red-team modules {rt}"
  -- check 5: the pinned file's closure, vs PL
  let pin := (importsOf env `Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage).qsort (·.toString < ·.toString)
  let h := pin.foldl (init := (17 : UInt64)) fun acc m => mixHash acc m.hash
  logInfo m!"pinned closure {pin.size} digest {h}"

  -- authorized `import …FormRAxisEvent` to the pinned file: 5432 / 6061067108338835133 (the nine
  -- added modules are `FormRAxisEvent`, `FormRTemplatePolynomial`, `FormRCore` and its four

  -- The thirty-first move adds one module below the pinned file,
  -- `Nock.NockVMROM.Thm54.RecordCarrier` (the ten-slot record facts): 5433 / 8144757428698741296.
  -- The thirty-second move adds the authorized
  -- `import …DecodedLambdaEvent` to the pinned file, one module whose own imports are already below
  -- it: 5434 / 5323874675720104979.
  -- The thirty-third move adds the authorized `import …PreZCensusCore` to the


  -- H1.5b Part 2a adds the authorized `import …FamilyEnvCore`: one module, whose
  -- own imports are already below the pin: 5437 / 6955681637188793633.

  -- `P8Core.PlacementAEvOnly` / `PlacementABridge`; Defs imports `P8Core.TraceGen.GenAirOrder` /
  -- `GenTraceConfined`).

  -- `P8Core.PartATarget309`: the parallel Part A modules, 24 more, all below the pin).
  -- 5608 / 1969708446570793877 since S0: the 15 `Thm54.BelowDefs.*` modules that
  -- sources in the pinned closure now import (declarations moved verbatim out of them); none removed.
  -- 5611 / 8993326757497721873 since GOLDI: `Nock.Field` now imports
  -- `Nock.Primality.GoldilocksCore` (goldilocks_prime is a kernel theorem), adding 3 modules below the pin.

  -- modules left and 457 entered (4.35 module splits: Init.Data.Float*, BVDecide.*, ImportGraph.*, Std.WP, Mathlib.Tactic.* ...).
  unless pin.size == 5904 ∧ h == 11310547186410272848 do
    throwError "pinned file import closure moved since the 37th move"
  let rtp := pin.filter fun m => (`Nock.RedTeam).isPrefixOf m
  logInfo m!"red-team modules below the pinned file: {rtp.size} {rtp}"
  unless rtp.size == 10 do throwError "red-team modules below the pinned file moved"

  unless pin.contains `Nock.NockVMROM.Thm54.FormRAxisEvent ∧ pin.contains `Nock.NockVMROM.Thm54.FormRCore do
    throwError "the pinned file does not import the Form R core (the thirtieth move's import)"

/-- `(module, public-constant count, digest)` at `PL`, for the 14 unmoved direct importers. -/
def downstream : Array (Name × Nat × UInt64) := #[
  (`Nock.RedTeam.Batch558Thm54FormRJoin, 28, 10929801027193533180),
  (`Nock.RedTeam.Batch555Thm54PwCertificate, 88, 15608016781822503180),
  (`Nock.RedTeam.Batch576Thm54FormRNegatives, 14, 15178441768356065434),
  (`Nock.RedTeam.Batch577Thm54FormRCompleteness, 33, 17876764954570557009),
  (`Nock.RedTeam.Batch581Thm54FormREvent, 11, 390694958112141781),
  (`Nock.RedTeam.Batch582Thm54FormRCompletenessHazard, 14, 13287843258636749369),
  -- 31st: `DeployedStaging` gained `carrier_columns_round_zero` and the 303/205 maps.
  -- reloc-3: re-measured after 12 reached declarations moved to `P8Core.DeployedStaging` (was 162, 380307722421375517).
  (`Nock.NockVMROM.Thm54.DeployedStaging, 134, 16125734761382977808),
  (`Nock.RedTeam.Batch619Thm54FormRReadSet, 7, 10965986880250755650),
  (`Nock.RedTeam.Batch624Thm54FormREventA4, 16, 10163614689980940196),
  -- 31st: `numerals` restated at 303/418, 205/156.
  (`Nock.RedTeam.Batch626Thm54FormREventNested, 11, 144360756636718433),
  (`Nock.RedTeam.Batch628Thm54LambdaEventLift, 15, 2631653302765281150),
  (`Nock.RedTeam.Batch629Thm54LambdaEventFrontier, 18, 5685662537241409991),
  (`Nock.RedTeam.Batch633Thm54LambdaEventUnguarded, 20, 6072127720082532529),
  (`Nock.RedTeam.Batch641Thm54LambdaEventGuarded, 20, 8279656894819904271)
]

run_cmd do
  let env ← getEnv
  let mut table : Std.HashMap Name (Array (Name × UInt64 × UInt64)) := {}
  let targets := downstream.map (·.1)
  for (name, ci) in env.constants.map₁.toList do
    if name.isInternal || (`_private).isPrefixOf name then continue
    match env.getModuleFor? name with
    | some m =>
      if targets.contains m then
        let vh : UInt64 := match ci with
          | .thmInfo _ => 0
          | _ => match ci.value? (allowOpaque := true) with | some v => v.hash | none => 0
        table := table.insert m ((table.getD m #[]).push (name, ci.type.hash, vh))
    | none => pure ()
  for (m, c, h) in downstream do
    let rows := (table.getD m #[]).qsort (fun a b => a.1.toString < b.1.toString)
    let h' := rows.foldl (init := (17 : UInt64)) fun acc (n, t, v) => mixHash (mixHash (mixHash acc n.hash) t) v
    unless rows.size == c ∧ h' == h do
      throwError m!"downstream module {m} changed: {rows.size} / {h'} vs {c} / {h}"
  logInfo m!"downstream digests equal for {downstream.size} modules"

end Nock.RedTeam.Batch657
