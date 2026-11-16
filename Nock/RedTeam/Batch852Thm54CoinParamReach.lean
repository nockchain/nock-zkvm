/-
  Nock/RedTeam/Batch852Thm54CoinParamReach.lean

  This is the `Batch845` instrument, unchanged.

  * **(A) Reach** (`value? No constant of
    `CoinParamCompleteness` or `Batch851` reaches `OptimizedProductionAcceptanceAt.same_problem`
    or `.p8`, `OptimizedSameProblemAt`, the target's `same_problem` or `p8`, or the capstone
    statement `OptimizedFullStrictThm54Statement` (`S`).  Positive controls: the instrument
    finds each probe where it is known to be.
-/
import Lean
import Nock.RedTeam.Batch851Thm54CoinParamCompletenessStop
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch852

open Lean Elab Command
open Nock.NockVMROM.Thm54

partial def reachNames (env : Environment) (roots : Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut work := roots.toList
  while true do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      if !((`Nock).isPrefixOf n) then continue
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
        for c in cs do
          unless seen.contains c do work := c :: work
  return seen

def PKG : Name := `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage

def probes : Array Name := #[
  PKG ++ `OptimizedHistoricalAcceptanceAt.same_problem,
  PKG ++ `OptimizedHistoricalAcceptanceAt.p8,
  PKG ++ `OptimizedSameProblemAt,
  `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement]

def reported : Array Name := #[`Nock.MemoryTable.interV, `Nock.MemoryTable.Vmem]

def lanes : List Name := [`Nock.NockVMROM.Thm54.CoinParamCompleteness, `Nock.RedTeam.Batch851]

def delivered (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for (n, _) in env.constants.toList do
    if lanes.any (fun ns => ns.isPrefixOf n) && !n.isInternal then out := out.push n
  return out

run_cmd do
  let env ← getEnv
  for p in probes ++ reported do
    unless env.contains p do throwError m!"probe name missing: {p}"
  let ctl : List (Name × Name) := [
    -- The pre-2a acceptance is `OptimizedHistoricalAcceptanceAt` (same fields).
    (``OptimizedHostileTimestamps.optimizedFullStrict_hostile_LIO_historical,
      PKG ++ `OptimizedHistoricalAcceptanceAt),
    (``OptimizedHostileTimestamps.hz0_of_good, PKG ++ `OptimizedHistoricalAcceptanceAt.same_problem),
    (``OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.optimizedHistoricalAcceptanceAt_iff,
      PKG ++ `OptimizedHistoricalAcceptanceAt.p8),
    (``OptimizedHostileTimestamps.hz0_of_good, PKG ++ `OptimizedSameProblemAt),
    (`Nock.MemoryTable.Fmem, `Nock.MemoryTable.Vmem),
    (`Nock.MemoryTable.Fmem, `Nock.MemoryTable.interV)]
  for (r, p) in ctl do
    unless (reachNames env #[r]).contains p do
      throwError m!"positive control failed: {r} does not reach {p}"
  logInfo m!"Batch852 (A): {ctl.length} positive controls pass"
  let ds := delivered env
  let keys : List Name := [
    `Nock.NockVMROM.Thm54.CoinParamCompleteness.logup_fibre_card_le,
    `Nock.NockVMROM.Thm54.CoinParamCompleteness.requests_forced_at,
    `Nock.NockVMROM.Thm54.CoinParamCompleteness.accepted_poles_card_le,
    `Nock.NockVMROM.Thm54.CoinParamCompleteness.exists_good_pole_rejected,
    `Nock.NockVMROM.Thm54.CoinParamCompleteness.exists_good_pole_not_deployed,
    `Nock.NockVMROM.Thm54.CoinParamCompleteness.rejected_of_response_poleHit_at,
    `Nock.NockVMROM.Thm54.CoinParamCompleteness.familyComputePublic_coin_free,
    `Nock.NockVMROM.Thm54.CoinParamCompleteness.familyMemoryPublic_coin_free,
    `Nock.RedTeam.Batch851.existing_instance_at_honestTuple,
    `Nock.RedTeam.Batch851.honest_fibre_has_rejected_good_pole,
    `Nock.RedTeam.Batch851.negative_control,
    `Nock.RedTeam.Batch851.concrete_sum_moves]
  for k in keys do
    unless ds.contains k do throwError m!"key name missing from the delivered set: {k}"
  let mut bad : Array (Name × Name) := #[]
  let mut rep : Array (Name × Name) := #[]
  for d in ds do
    let r := reachNames env #[d]
    for p in probes do
      if r.contains p then bad := bad.push (d, p)
    for p in reported do
      if r.contains p then rep := rep.push (d, p)
  unless bad.isEmpty do throwError m!"Batch852 (A): a delivered constant reaches a probe: {bad}"
  logInfo m!"Batch852 (A): {ds.size} delivered constants reach none of {probes.size} probes; paper-mirror reaches (reported): {rep.size}"
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut axBad : Array (Name × Name) := #[]
  for d in ds do
    let axs ← liftCoreM (Lean.collectAxioms d)
    for a in axs do
      unless allowed.contains a do axBad := axBad.push (d, a)
  unless axBad.isEmpty do throwError m!"Batch852 (B): non-standard axiom: {axBad}"
  logInfo m!"Batch852 (B): {ds.size} constants use only propext / Classical.choice / Quot.sound"

end Nock.RedTeam.Batch852
