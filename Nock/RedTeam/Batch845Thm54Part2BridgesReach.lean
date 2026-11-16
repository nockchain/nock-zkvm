/-
  Nock/RedTeam/Batch845Thm54Part2BridgesReach.lean

  * **(A) Reach** (`value? Positive controls: the instrument finds each probe where it is known to be.
-/
import Lean
import Nock.RedTeam.Batch843Thm54HonestAlignment
import Nock.RedTeam.Batch844Thm54HpowHW
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch845

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
  `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement,
  `Nock.MemoryTable.interV,
  `Nock.MemoryTable.Vmem]

/-- Each reaches `Vmem` (and possibly `interV`) and
nothing else among the probes: `tiles_queued_of_deployed` through
`WalkQueueDeployed.tracesWalkHyps_compute → deployed_tiling → count_eq_ln_last →
Batch459.isLast_source_last → Batch457.masks_at_row_at → computeRealization →
correctedCanonicalFinalTrace_satisfies → … → exactMemoryChainedAccepts → Vmem`;
`expOf_requestList_honest` through `canonicalComputeTrace_satisfies` (the same honest canonical
satisfaction chain); `tiles_queued_built` through the carrier's `MemoryExactTopology` (`Fmem`), the
type of `E.traversal`. -/
def exempt : List Name := [`Nock.RedTeam.Batch842.tiles_queued_of_deployed,
  `Nock.RedTeam.Batch843.expOf_requestList_honest, `Nock.RedTeam.Batch843.tiles_queued_built]

def paperMirror : List Name := [`Nock.MemoryTable.interV, `Nock.MemoryTable.Vmem]

def lanes : List Name := [`Nock.NockVMROM.Thm54.UniqueExponentsBridge, `Nock.RedTeam.Batch842,
  `Nock.RedTeam.Batch843, `Nock.RedTeam.Batch844]

def delivered (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for (n, _) in env.constants.toList do
    let inP8Core := match env.getModuleIdxFor? n with
      | some i => (`Nock.NockVMROM.Thm54.P8Core.EvOnly).isPrefixOf (env.header.moduleNames[i.toNat]!)
      | none => false
    if lanes.any (fun ns => ns.isPrefixOf n) && !n.isInternal && !inP8Core then out := out.push n
  return out

run_cmd do
  let env ← getEnv
  for p in probes do
    unless env.contains p do throwError m!"probe name missing: {p}"
  let ctl : List (Name × Name) := [
    -- The pre-2a acceptance is `OptimizedHistoricalAcceptanceAt`.
    (``OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package,
      `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement),
    (``OptimizedHostileTimestamps.hz0_of_good, PKG ++ `OptimizedHistoricalAcceptanceAt.same_problem),
    (``OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.optimizedHistoricalAcceptanceAt_iff,
      PKG ++ `OptimizedHistoricalAcceptanceAt.p8),
    (``OptimizedHostileTimestamps.hz0_of_good, PKG ++ `OptimizedSameProblemAt),
    (`Nock.MemoryTable.Fmem, `Nock.MemoryTable.Vmem),
    (`Nock.MemoryTable.Fmem, `Nock.MemoryTable.interV)]
  for (r, p) in ctl do
    unless (reachNames env #[r]).contains p do
      throwError m!"positive control failed: {r} does not reach {p}"
  logInfo m!"Batch845 (A): {ctl.length} positive controls pass"
  let ds := delivered env
  unless ds.size ≥ 40 do throwError m!"delivered set too small: {ds.size}"
  let keys : List Name := [
    `Nock.NockVMROM.Thm54.UniqueExponentsBridge.uniqueExponents_decoded_at,
    `Nock.NockVMROM.Thm54.UniqueExponentsBridge.uniqueExponents_decoded_pkg,
    `Nock.RedTeam.Batch842.lblCAt_state_eq_typed,
    `Nock.RedTeam.Batch842.tiles_queued_of_tracesWalkHyps,
    `Nock.RedTeam.Batch842.tiles_queued_of_deployed,
    `Nock.RedTeam.Batch843.typed_state_eq_exec,
    `Nock.RedTeam.Batch843.expOf_requestList_honest,
    `Nock.RedTeam.Batch843.tiles_queued_built,
    `Nock.RedTeam.Batch844.hpow_of_family_acceptance,
    `Nock.RedTeam.Batch844.hpow_of_family_acceptance_two,
    `Nock.RedTeam.Batch844.hW_forces_axis_fixed,
    `Nock.RedTeam.Batch844.formRT_nockAxisOf_not_idempotent]
  for k in keys do
    unless ds.contains k do throwError m!"key name missing from the delivered set: {k}"
  let mut bad : Array (Name × Name) := #[]
  let mut exHits : Array (Name × Name) := #[]
  for d in ds do
    let r := reachNames env #[d]
    for p in probes do
      if r.contains p then
        if exempt.contains d && paperMirror.contains p then exHits := exHits.push (d, p)
        else bad := bad.push (d, p)
  unless bad.isEmpty do throwError m!"Batch845 (A): a delivered constant reaches a probe: {bad}"
  -- the named honest-side reaches really are reaches (negative of the exemption)
  for e in exempt do
    unless exHits.any (fun x => x.1 == e) do
      throwError m!"exempt name does not reach the paper mirror (drop the exemption): {e}"
  logInfo m!"Batch845 (A): {ds.size} delivered constants; all but {exempt.length} reach none of {probes.size} probes; the named STOP-class reaches: {exHits}"
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut axBad : Array (Name × Name) := #[]
  for d in ds do
    let axs ← liftCoreM (Lean.collectAxioms d)
    for a in axs do
      unless allowed.contains a do axBad := axBad.push (d, a)
  unless axBad.isEmpty do throwError m!"Batch845 (B): non-standard axiom: {axBad}"
  logInfo m!"Batch845 (B): {ds.size} constants use only propext / Classical.choice / Quot.sound"

end Nock.RedTeam.Batch845
