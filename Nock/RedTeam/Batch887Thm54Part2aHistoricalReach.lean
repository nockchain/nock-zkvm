/-
  Nock/RedTeam/Batch887Thm54Part2aHistoricalReach.lean

  The pre-2a acceptance survives as a production object
  (`OptimizedHistoricalAcceptanceAt` and friends, `DeployedAcceptance.lean`) so fixture receipts
  restate rather than vanish.  This instrument shows none of it is reached — through types AND proof
  terms (`value?
-/
import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.RealProgramSoundness
import Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch887

open Lean Elab Command

partial def reachSet (env : Environment) (roots : Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut work := roots.toList
  while true do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      if !(`Nock).isPrefixOf n then continue
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
        for c in cs do
          unless seen.contains c do work := c :: work
  return seen

def PKG : Name := `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage

def historical : Array Name := #[
  PKG ++ `OptimizedHistoricalAcceptanceAt,
  PKG ++ `OptimizedHistoricalTraceAcceptanceAt,
  PKG ++ `optimizedHistoricalAcceptanceAt_iff,
  PKG ++ `sampled_io_event_good_of_historical,
  PKG ++ `sampled_inter_event_good_of_historical,
  `Nock.Walk37.Nock.NockVMROM.Thm54.deployedAcceptance_of_historical,
  `Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.optimizedFullStrict_hostile_LIO_historical]

def roots : Array Name := #[
  ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod,
  ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76,
  ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package,
  ``Nock.NockVMROM.Thm54.RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_31,
  ``Nock.NockVMROM.Thm54.RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_32,
  ``Nock.NockVMROM.Thm54.GoldilocksParameters.hostile_soundness_at_paper_configuration]

run_cmd do
  let env ← getEnv
  for n in historical ++ roots do
    unless env.contains n do throwError m!"name missing: {n}"
  for r in [``Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.hz0_of_good,
      ``Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.optimizedFullStrict_hostile_LIO_historical] do
    unless (reachSet env #[r]).contains (PKG ++ `OptimizedHistoricalAcceptanceAt) do
      throwError m!"positive control failed: {r} does not reach OptimizedHistoricalAcceptanceAt"
  -- and finds the live family IO event from the capstone
  unless (reachSet env #[``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package]).contains
      (PKG ++ `famIOEventOf) do
    throwError "positive control failed: of_package does not reach famIOEventOf"
  for r in roots do
    let cl := reachSet env #[r]
    let hits := historical.filter cl.contains
    logInfo m!"{r}: closure {cl.size}; historical names reached: {hits}"
    unless hits.isEmpty do throwError m!"{r} reaches the historical acceptance: {hits}"
  logInfo "Batch887: no historical-acceptance name is reached from the three capstones or the three figure theorems"

end Nock.RedTeam.Batch887
