/-
  Nock/RedTeam/Batch825Thm54R4BridgeReach.lean

  * **(A) Reach.**  The instrument of `Batch786` (`ConstantInfo.value? Positive controls: `deployed_row_vmem_at` reaches `Vmem` and `interV`;
    `optimizedFullStrict_hostile_LIO` reaches `S` and `same_problem`;
    `optimizedProductionAcceptanceAt_iff` reaches `p8`; `cfg_z_eq_nprSeed` reaches
    `OptimizedSameProblemAt`.
  * **(B) Axioms.**  Every delivered constant uses only `propext`, `Classical.choice`,
    `Quot.sound`.
-/
import Lean
import Nock.RedTeam.Batch824Thm54R4Bridge
import Nock.RedTeam.Batch786Thm54FamilyIOChain
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch825

open Lean Elab Command

def PKG : Name := `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage

def probes : Array Name := #[
  -- The pre-2a acceptance is `OptimizedHistoricalAcceptanceAt`; the target's
  -- `same_problem` / `p8` were deleted (no longer probes).
  PKG ++ `OptimizedHistoricalAcceptanceAt,
  PKG ++ `OptimizedHistoricalAcceptanceAt.same_problem,
  PKG ++ `OptimizedHistoricalAcceptanceAt.p8,
  PKG ++ `OptimizedSameProblemAt,
  `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement,
  `Nock.MemoryTable.interV,
  `Nock.MemoryTable.Vmem]

def lanes : Array Name := #[`Nock.NockVMROM.Thm54.FormRBridge, `Nock.RedTeam.Batch822,
  `Nock.RedTeam.Batch823, `Nock.RedTeam.Batch824]

def delivered (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for (n, _) in env.constants.toList do
    let inP8Core := match env.getModuleIdxFor? n with
      | some i => (`Nock.NockVMROM.Thm54.P8Core.EvOnly).isPrefixOf (env.header.moduleNames[i.toNat]!)
      | none => false
    if lanes.any (·.isPrefixOf n) && !n.isInternal && !inP8Core then out := out.push n
  return out

run_cmd do
  let env ← getEnv
  for p in probes do
    unless env.contains p do throwError m!"probe name missing: {p}"
  let ctl : List (Name × Name) := [
    (`Nock.NockVMROM.Thm54.FamilyMemoryRows.deployed_row_vmem_at, `Nock.MemoryTable.Vmem),
    (`Nock.NockVMROM.Thm54.FamilyMemoryRows.deployed_row_vmem_at, `Nock.MemoryTable.interV),
    (`Nock.RedTeam.Batch742.row_record_is_request,
      `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement),
    (`Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.optimizedFullStrict_hostile_LIO_historical,
      PKG ++ `OptimizedHistoricalAcceptanceAt.same_problem),
    (PKG ++ `optimizedHistoricalAcceptanceAt_iff, PKG ++ `OptimizedHistoricalAcceptanceAt.p8),
    (`Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.hz0_of_good, PKG ++ `OptimizedSameProblemAt)]
  for (r, p) in ctl do
    unless env.contains r do throwError m!"control root missing: {r}"
    unless (Nock.RedTeam.Batch786.reachNames env #[r]).contains p do
      throwError m!"positive control failed: {r} does not reach {p}"
  logInfo m!"Batch825 (A): {ctl.length} positive controls pass"
  let ds := delivered env
  unless ds.size ≥ 60 do throwError m!"delivered set too small: {ds.size}"
  let keys : List Name := [`Nock.RedTeam.Batch824.r4_bridge_at, `Nock.RedTeam.Batch824.r4_path_valid_at,
    `Nock.RedTeam.Batch824.r4_bridge_at_current, `Nock.NockVMROM.Thm54.FormRBridge.telescope,
    `Nock.RedTeam.Batch822.telescopeRows_of_memory, `Nock.RedTeam.Batch823.slot_values,
    `Nock.RedTeam.Batch823.locateExp_expOfAt]
  for k in keys do
    unless ds.contains k do throwError m!"key theorem missing from the delivered set: {k}"
  let mut bad : Array (Name × Name) := #[]
  for d in ds do
    let r := Nock.RedTeam.Batch786.reachNames env #[d]
    for p in probes do
      if r.contains p then bad := bad.push (d, p)
  unless bad.isEmpty do throwError m!"Batch825 (A): a delivered constant reaches a probe: {bad}"
  logInfo m!"Batch825 (A): {ds.size} delivered constants reach none of {probes.size} probes"
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut axBad : Array (Name × Name) := #[]
  for d in ds do
    let axs ← liftCoreM (Lean.collectAxioms d)
    for a in axs do
      unless allowed.contains a do axBad := axBad.push (d, a)
  unless axBad.isEmpty do throwError m!"Batch825 (B): non-standard axiom: {axBad}"
  logInfo m!"Batch825 (B): {ds.size} constants use only propext / Classical.choice / Quot.sound"

end Nock.RedTeam.Batch825
