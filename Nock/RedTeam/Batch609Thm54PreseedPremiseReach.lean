/-
  Nock/RedTeam/Batch609Thm54PreseedPremiseReach.lean

  Notes only.

  Instrument: a worklist walk of the transitive constant closure through TYPES AND PROOF TERMS
  (`ConstantInfo.value? Positive controls: the deployed gate `haltAtomMixed` and the column `atomCol` must be FOUND
  (they sit in the chip every package carries); the new honest-side premises
  (`HaltRowsBase`, `HaltLeavesBase`, `canonical_haltAtomMixed`, `buildTraceSatisfaction`) are
  then reported present/absent.  Every expectation is asserted with `throwError`, so the file
  only compiles if the reading below holds.
-/
import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.MemoryHaltLeavesHonest
import Nock.NockVMROM.Thm54.MemoryHaltAtomDecode
import Nock.NockVMROM.Thm54.BuildableChips
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

open Lean Elab Command Meta

namespace Nock.RedTeam.Batch609

/-- Transitive constant reach through types and (opaque-inclusive) values. -/
partial def reachWalk (env : Environment) (roots : Array Name) (stopAt : Name → Bool) :
    Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut work := roots.toList
  while !work.isEmpty do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      if stopAt n then continue
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        match ci.value? (allowOpaque := true) with
        | some v => cs := cs ++ v.getUsedConstants
        | none => pure ()
        for c in cs do
          unless seen.contains c do work := c :: work
  return seen

def typeMentions (env : Environment) (root : Name) : Array Name :=
  match env.find? root with
  | none => #[]
  | some ci => ci.type.getUsedConstants

def zmod : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
def p76 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76
def ofPkg : Name :=
  ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

def positive : Array Name := #[
  ``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.haltAtomMixed,
  ``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.atomCol]

def probes : Array Name := #[
  ``Nock.NockVMROM.Thm54.MemoryHaltLeavesHonest.HaltRowsBase,
  ``Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.HaltLeavesBase,
  ``Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.canonical_haltAtomMixed,
  ``Nock.NockVMROM.Thm54.BuildableChips.buildTraceSatisfaction,
  ``Nock.NockVMROM.Thm54.MemoryHaltLeavesHonest.package_haltLeavesBase,
  ``Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace.honestAtomOf]

run_cmd do
  let env ← getEnv
  -- do not descend into Mathlib / core: their closure cannot contain project names
  let stop : Name → Bool := fun n => !(`Nock).isPrefixOf n
  for root in #[zmod, p76, ofPkg] do
    unless env.contains root do throwError m!"missing root {root}"
    let r := reachWalk env #[root] stop
    let tys := typeMentions env root
    for n in positive ++ probes do
      unless env.contains n do throwError m!"missing probe {n}"
    let posHits := positive.filter r.contains
    let probeHits := probes.filter r.contains
    let typeHits := (positive ++ probes).filter tys.contains
    logInfo m!"{root}: closure size {r.size}; positive found {posHits}; \
      new-premise names reached {probeHits}; named in TYPE {typeHits}"
    unless posHits.size == positive.size do throwError m!"positive control failed at {root}"
    unless probeHits.isEmpty do throwError m!"new premise reached from {root}: {probeHits}"
    unless typeHits.isEmpty do throwError m!"new name in the TYPE of {root}: {typeHits}"
  -- positive control for the probes themselves: the same walker finds `HaltRowsBase` /
  -- `canonical_haltAtomMixed` from the fixture receipt that does consume them.
  let rFix := reachWalk env #[``Nock.NockVMROM.Thm54.BuildableChips.Concrete.traceSatisfaction73] stop
  let fixHits := probes.filter rFix.contains
  logInfo m!"traceSatisfaction73 (positive control): reaches {fixHits}"
  unless fixHits.contains ``Nock.NockVMROM.Thm54.MemoryHaltLeavesHonest.HaltRowsBase &&
      fixHits.contains
        ``Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.canonical_haltAtomMixed do
    throwError "probe positive control failed"
