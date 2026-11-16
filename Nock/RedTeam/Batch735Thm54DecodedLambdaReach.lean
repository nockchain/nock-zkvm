/-
  Nock/RedTeam/Batch735Thm54DecodedLambdaReach.lean

  **The thirty-second move's import walk (4a) and proof-term reach (4g-(i)), lane
  `lambda-consumer-32nd`.**  Instruments with positive controls; no production edit.

  * **4a.**
  * **4g-(i), toward the paper mirror.**
-/
import Lean
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.FamilyMemoryRows
import Nock.RedTeam.Batch489Thm54FoOfEqFoW
import Nock.RedTeam.Batch501Thm54MemoryTopology
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch735

open Lean Elab Command

partial def reachSet (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut work := roots
  while true do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        match ci.value? (allowOpaque := true) with
        | some v => cs := cs ++ v.getUsedConstants
        | none => pure ()
        if let .inductInfo iv := ci then cs := cs ++ iv.ctors.toArray
        work := cs.toList ++ work
  return seen

partial def importsOf (env : Environment) (root : Name) : Std.HashSet Name := Id.run do
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
  return seen

run_cmd do
  let env ← getEnv
  let T := `Nock.NockVMROM.Thm54
  let ev := T ++ `DecodedLambdaEvent
  -- 4a: the direct imports are exactly the five
  let mods := env.header.moduleNames
  let some i := mods.findIdx? (· == ev) | throwError "event module missing"
  let direct := (env.header.moduleData[i]!.imports.map (·.module)).filter (· != `Init)
  let five := #[T ++ `WalkForestPrefixAlphaEvents, T ++ `FormRAxisEvent, T ++ `FormRCore,
    T ++ `RecordCarrier, T ++ `HostileRecordLists]
  unless direct.size == 5 ∧ five.all direct.contains do
    throwError m!"event module imports {direct}, expected exactly {five}"
  let cl := importsOf env ev
  for m in [T ++ `Walk37.OptimizedStrictFullPackage, T ++ `HostileSkeletonDecoding, T ++ `ExecOfTraces,
      T ++ `MemoryHaltAtomDecode, T ++ `OptimizedHostileTimestamps] do
    if cl.contains m then throwError m!"event module reaches {m}"
  unless (importsOf env (T ++ `Walk37.OptimizedStrictFullPackage)).contains ev do
    throwError "positive control: the pinned file does not import the event module"
  logInfo m!"4a: DecodedLambdaEvent imports exactly the five ({cl.size} modules), none of the five forbidden"
  -- 4g-(i)
  let mirror := [`Nock.MemoryTable.Vmem, `Nock.MemoryTable.interV, `Nock.MemoryTable.pole,
    `Nock.MemoryTable.interR, `Nock.MemoryTable.Fmem, T ++ `FamilyMemoryRows.deployed_row_vmem_at,
    `Nock.RedTeam.Batch489.tracesWalkHyps_of_deployed,
    `Nock.RedTeam.Batch501.memoryTopology_of_deployed,
    `Nock.RedTeam.Batch501.memoryTopology_of_deployed_of_good]
  for t in mirror do
    unless (env.find? t).isSome do throwError m!"target missing: {t}"
  let hits (r : Name) : List Name := let s := reachSet env [r]; mirror.filter s.contains
  for r in [ev ++ `decodedLambdaEventOfEnvs, ev ++ `decodedLambdaEventOfEnvs_card_le,
      ev ++ `decodedLambdaEventOfEnvs_card_le_numeral, T ++ `ProductionP8Containment.formRUniformWorkload] do
    unless (hits r).isEmpty do throwError m!"{r} reaches the mirror: {hits r}"
  let pkg := `Nock.Walk37 ++ T ++ `OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage
  let base := hits (pkg ++ `memoryForestAlphaEventOf_card_le)
  for r in [pkg ++ `decodedLambdaEventOf, pkg ++ `decodedLambdaEventOf_card_le] do
    unless hits r == base do throwError m!"{r} reaches {hits r}, baseline {base}"
  let pc := hits `Nock.RedTeam.Batch489.tracesWalkHyps_of_deployed
  unless pc.contains `Nock.MemoryTable.Vmem ∧ pc.contains `Nock.MemoryTable.interR do
    throwError "positive control failed"
  logInfo m!"4g-(i): the event, its card theorems and formRUniformWorkload reach none of the mirror; \
    the pinned wrappers reach exactly the package-type baseline {base}"

end Nock.RedTeam.Batch735
