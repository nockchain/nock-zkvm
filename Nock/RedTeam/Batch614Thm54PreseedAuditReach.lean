/-
  Nock/RedTeam/Batch614Thm54PreseedAuditReach.lean

  Notes only; not a pass.

  Q1.  From `nockCompiles_zmod`, `nockCompiles_p76`, `of_package`: the deployed gate and column
  (`haltAtomMixed`, `atomCol`, `expandChipTail`) are REACHED; `haltAtomGateCoord` is NOT (it is a
  watchlist-only name; the letter's "five newly reached" over-counts by one) (positive
  control: they sit in the chip every package carries) and the new honest-side premises
  (`HaltRowsBase`, `HaltLeavesBase`, `canonical_haltAtomMixed`, `buildTraceSatisfaction`,
  `package_haltLeavesBase`, `honestAtomOf`) are NOT.  Second positive control for the walker:
  from `BuildableChips.Concrete.traceSatisfaction73` the premises ARE found.
  Third: `GenMemAtomFill` (the generator's honest fill) is a LEAF module — none of its names is
  reached from any capstone.

  Q2.  The decoder (`decodeMemPub`, `HostileSkeletonDecoding.decodeNoun`, `memoryAtomAt`,
  `MemoryHaltAtomDecode`) is NOT reached from the TYPE of `OptimizedProductionGenuineTargetAt`
  nor from the TYPE of `OptimizedProductionAcceptanceAt`, nor from the consumed failure event
  `optimizedFailureEvent`'s closure; and `NPR.collision_card_le_tight`'s event is not in the
  failure event's closure.  Positive controls: the target's type reaches `mixedTransitionGates`
  (the `memory` conjunct) and `GenuineTargetAt`; `GenuineWitness` reaches
  `OpcodeSemantics.PairFaithful` (the strategy-skeleton census that IS priced).
-/
import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.MemoryHaltLeavesHonest
import Nock.NockVMROM.Thm54.MemoryHaltAtomDecode
import Nock.NockVMROM.Thm54.BuildableChips
import Nock.NockVMROM.Thm54.TraceGen.GenMemAtomFill
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
open Lean Elab Command Meta

namespace Nock.RedTeam.Batch614

partial def reach (env : Environment) (roots : Array Name) (stop : Name → Bool) :
    Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut work := roots.toList
  while true do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      if stop n then continue
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
        for c in cs do
          unless seen.contains c do work := c :: work
  return seen

/-- Constants used by the TYPE of `n` and, for a structure, by its constructor's type. -/
def typeReach (env : Environment) (n : Name) (stop : Name → Bool) : Std.HashSet Name := Id.run do
  let mut roots : Array Name := #[]
  match env.find? n with
  | some (.inductInfo iv) =>
      for c in iv.ctors do
        if let some cci := env.find? c then roots := roots ++ cci.type.getUsedConstants
      roots := roots ++ iv.type.getUsedConstants
  | some ci => roots := ci.type.getUsedConstants
  | none => pure ()
  -- one level only: the names the statement mentions, and what those names unfold to
  return reach env roots stop

def zmod : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
def p76 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76
def ofPkg : Name :=
  ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

def positive : Array Name := #[
  ``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.haltAtomMixed,
  ``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.atomCol,
  ``Nock.NockVMROM.Thm54.MonolithicRAP.expandChipTail]

/-- The letter lists `haltAtomGateCoord` among "five definitions newly reached by the statement".
It is NOT reached by any capstone: the chip compiles `mixedTransitionGates` generically
(`ChipTemplate.allGates` / `mixedCompile`), and `haltAtomGateCoord` is a named abbreviation used
only by the shape lemmas.  It is in the closure listing because it is on the WATCHLIST.  Asserted
below (finding, documentation-level). -/
def watchOnly : Name := ``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.haltAtomGateCoord

def premises : Array Name := #[
  ``Nock.NockVMROM.Thm54.MemoryHaltLeavesHonest.HaltRowsBase,
  ``Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.HaltLeavesBase,
  ``Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.canonical_haltAtomMixed,
  ``Nock.NockVMROM.Thm54.BuildableChips.buildTraceSatisfaction,
  ``Nock.NockVMROM.Thm54.MemoryHaltLeavesHonest.package_haltLeavesBase,
  ``Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace.honestAtomOf]

def decoder : Array Name := #[
  ``Nock.NockVMROM.Thm54.ExecOfTraces.decodeMemPub,
  ``Nock.NockVMROM.Thm54.HostileSkeletonDecoding.decodeNoun,
  ``Nock.NockVMROM.Thm54.MemoryHaltAtomDecode.memoryAtomAt,
  ``Nock.NockVMROM.Thm54.MemoryHaltAtomDecode.decodeMemPub_halt_leaf_eq_atom,
  ``Nock.NockVMROM.Thm54.MemoryHaltAtomDecode.decodeNoun_halt_eq_atom_zmod]

def genFill : Array Name := #[
  ``Nock.NockVMROM.Thm54.TraceGen.genMemForestFromTree_bfs_halt,
  ``Nock.NockVMROM.Thm54.TraceGen.honest_halt_gate,
  ``Nock.NockVMROM.Thm54.TraceGen.AllH]

def stop : Name → Bool := fun n => !(`Nock).isPrefixOf n

run_cmd do
  let env ← getEnv
  for n in positive ++ premises ++ decoder ++ genFill ++ #[watchOnly] do
    unless env.contains n do throwError m!"missing name {n}"
  for root in #[zmod, p76, ofPkg] do
    let r := reach env #[root] stop
    let pos := positive.filter r.contains
    let pre := premises.filter r.contains
    let dec := decoder.filter r.contains
    let gen := genFill.filter r.contains
    logInfo m!"{root}: closure {r.size}; gate/column reached {pos.size}/{positive.size}; \
      new premises reached {pre}; decoder reached {dec}; generator fill reached {gen}"
    unless pos.size == positive.size do throwError m!"positive control failed at {root}: {pos}"
    if r.contains watchOnly then
      throwError m!"{watchOnly} IS reached from {root} (the audit note below would be wrong)"
    unless pre.isEmpty do throwError m!"new premise reached from {root}: {pre}"
    unless gen.isEmpty do throwError m!"generator fill reached from {root}: {gen}"
  -- walker positive control: the fixture receipt that does consume the premises
  let rFix := reach env #[``Nock.NockVMROM.Thm54.BuildableChips.Concrete.traceSatisfaction73] stop
  let hits := premises.filter rFix.contains
  logInfo m!"traceSatisfaction73 reaches {hits}"
  unless hits.contains ``Nock.NockVMROM.Thm54.MemoryHaltLeavesHonest.HaltRowsBase &&
      hits.contains
        ``Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.canonical_haltAtomMixed do
    throwError "walker positive control failed"

/-! ## Q2 — the consumed target and event never look at the decoder -/

def target : Name :=
  ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.OptimizedProductionGenuineTargetAt
def acceptance : Name :=
  ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.OptimizedProductionAcceptanceAt
def event : Name := ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.optimizedFailureEvent
def witness : Name := ``Nock.NockVMROM.Thm54.ProductionP8Containment.GenuineWitness

run_cmd do
  let env ← getEnv
  for n in #[target, acceptance, event, witness, ``Nock.NPR.collision_card_le_tight,
      ``Nock.NockVMROM.Thm54.OpcodeSemantics.PairFaithful,
      ``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.mixedTransitionGates,
      ``Nock.NockVMROM.Thm54.ProductionP8Containment.GenuineTargetAt] do
    unless env.contains n do throwError m!"missing {n}"
  -- the TYPE closures of the target and of acceptance (what the conjuncts can say)
  for s in #[target, acceptance] do
    let r := typeReach env s stop
    let dec := decoder.filter r.contains
    logInfo m!"{s}: type closure {r.size}; decoder names {dec}; \
      mentions mixedTransitionGates \
      {r.contains ``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.mixedTransitionGates}"
    unless dec.isEmpty do throwError m!"decoder reached from the type of {s}: {dec}"
  let rT := typeReach env target stop
  unless rT.contains ``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.mixedTransitionGates do
    throwError "target positive control (mixedTransitionGates) failed"
  -- The target lost `p8` (disclosed gap), so it no longer reaches `GenuineTargetAt`.
  if rT.contains ``Nock.NockVMROM.Thm54.ProductionP8Containment.GenuineTargetAt then
    throwError "target still reaches GenuineTargetAt (2a dropped p8)"
  -- the consumed event: full closure
  let rE := reach env #[event] stop
  let decE := decoder.filter rE.contains
  logInfo m!"optimizedFailureEvent: closure {rE.size}; decoder names {decE}; \
    collision_card_le_tight {rE.contains ``Nock.NPR.collision_card_le_tight}; \
    NPR namespace reached {(rE.toArray.filter fun n => (`Nock.NPR).isPrefixOf n).size}"
  unless decE.isEmpty do throwError m!"decoder reached from the event: {decE}"
  if rE.contains ``Nock.NPR.collision_card_le_tight then
    throwError "fixed-pair collision event IS in the consumed event (letter says it is not)"
  -- GenuineWitness: the skeleton census is where pair faithfulness lives
  let rW := typeReach env witness stop
  logInfo m!"GenuineWitness: type closure {rW.size}; PairFaithful \
    {rW.contains ``Nock.NockVMROM.Thm54.OpcodeSemantics.PairFaithful}; decoder \
    {decoder.filter rW.contains}"
  unless rW.contains ``Nock.NockVMROM.Thm54.OpcodeSemantics.PairFaithful do
    throwError "witness positive control failed"

end Nock.RedTeam.Batch614
