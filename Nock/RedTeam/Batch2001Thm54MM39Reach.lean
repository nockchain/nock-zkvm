/-
  Nock/RedTeam/Batch2001Thm54MM39Reach.lean

  Asserted:
  * positive controls (≥ 3): the walk reaches `walkChip`, `memSoundnessVCLW`, `boundVCLW''`,
    `vclWalkSummandW`, `HonestVCLW`, `HonestVCLJW`, `computeChipVCLQ7T`, `cellChip`, `frameVCL`, and NO
    `Nock.Walk37.*` and NO `Nock.VCL38.*` constant;
  * the remaining two, `shapeV` and `Path.colRoundT`, left the one-ring frontier but ARE still reached by
    the transitive walk; neither was on the watchlist.  Shortest chains (BFS with parent pointers, printed
    below): `Statement.mk → Package.MF → StandaloneW.MFvW → memSoundnessVCLW → vcl_response_soundW →
    round_cell0 → shapeV (→ Path.colRoundT)`.  No chain passes
    through `pathChip` or `memSoundnessVCL` (asserted).
-/
import Nock.NockVMROM.Thm54.Walk39.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.VCL38.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedStrictFullPackageConcrete
import Nock.RedTeam.Batch1761Thm54MM38Reach
open Lean

namespace Nock.RedTeam.Batch2001
open Nock.RedTeam.Batch1761
/-- The `Batch1761` walk, breadth-first, with parent pointers (for shortest chains). -/
def reachP (env : Environment) (roots : List Name) : Std.HashMap Name Name := Id.run do
  let mut par : Std.HashMap Name Name := {}
  for r in roots do par := par.insert r r
  let mut q : Array Name := roots.toArray
  let mut i := 0
  while i < q.size do
    let n := q[i]!
    i := i + 1
    match env.find? n with
    | none => pure ()
    | some ci =>
      let mut nxt := consts ci
      match ci with
      | .inductInfo iv => nxt := nxt ++ iv.ctors.toArray
      | .ctorInfo c => nxt := nxt.push c.induct
      | _ => pure ()
      for m in nxt do
        if tracked m && !par.contains m then
          par := par.insert m n
          q := q.push m
  return par
partial def chainTo (par : Std.HashMap Name Name) (n : Name) (acc : List Name := []) : List Name :=
  match par.get? n with
  | none => n :: acc
  | some p => if p == n then n :: acc else chainTo par p (n :: acc)
end Nock.RedTeam.Batch2001

open Nock.RedTeam.Batch1761 Nock.RedTeam.Batch2001 in
run_cmd do
  let env ← getEnv
  let SF := `Nock.Walk39.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
  let roots : List Name := [SF ++ `OptimizedFullStrictThm54Statement, SF ++ `OptimizedFullStrictThm54Statement.mk,
    SF ++ `OptimizedFullStrictNockVMROMPackage]
  for r in roots do
    unless (env.find? r).isSome do throwError "root missing {r}"
  let R := reach env roots
  let tw := R.toList.filter fun n => (`Nock.Walk37).isPrefixOf n || (`Nock.VCL38).isPrefixOf n
  unless tw.isEmpty do throwError "the 39th statement reaches twin constants: {tw}"
  let pos : List Name := [`Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.walkChip,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.memSoundnessVCLW,
    `Nock.NockVMROM.Thm54.VclL.Events.«boundVCLW''»,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.vclWalkSummandW,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.HonestVCLW,
    `Nock.NockVMROM.Thm54.VclL.Compute.TowerD.HonestVCLJW,
    `Nock.NockVMROM.Thm54.VclL.Compute.TowerD.computeChipVCLQ7T,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cellChip,
    `Nock.NockVMROM.Thm54.SVFrame.frameVCL]
  for n in pos do
    unless R.contains n do throwError "positive control: {n} not reached (instrument suspect)"
  let dropped : List Name := [
    `Nock.NockVMROM.Thm54.SVCompute.ChipData,
    `Nock.NockVMROM.Thm54.SVCompute.layoutVCL,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.acc,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.baseGates,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.bit0,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.cellIdx,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.child,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.pathChip,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.first,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.isF,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.isL,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.last,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.len,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.lR,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.m,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.mixedGates,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.pAcc,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.pProvInv,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.pR,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.pRec,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.qEqs,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.rootIdx,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.rootR,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.rR,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.side,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.pathTemplate,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.xAcc,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.xConsInv,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.Path.xKey,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.QFP.add,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.QFP.next,
    `Nock.NockVMROM.Thm54.VclL.Events.boundVCL'',
    `Nock.NockVMROM.Thm54.VclL.Events.ioWorkKpS]
  let extras : List Name := [
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.memSoundnessVCL,
    `Nock.RedTeam.Batch1880.MFv,
    `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.HonestVCL,
    `Nock.NockVMROM.Thm54.VclL.Compute.TowerD.HonestVCLJ.toHonestVCLT,
    `Nock.NockVMROM.Thm54.VclL.Compute.TowerD.JointMemFacts,
    `Nock.NockVMROM.Thm54.VclL.Compute.TowerD.jointMemFacts_of,
    `Nock.RedTeam.Batch1880.CFv,
    `Nock.NockVMROM.Thm54.VclL.Compute.TowerD.HonestVCLJ,
    `Nock.NockVMROM.Thm54.VclL.Compute.TowerD.jointMem,
    `Nock.NockVMROM.Thm54.VclL.Compute.TowerD.CFvW4,
    `Nock.NockVMROM.Thm54.VclL.Compute.TowerD.MFvW4,
    `Nock.NockVMROM.Thm54.VclL.Compute.TowerD.extraPremises_vclW4,
    `Nock.NockVMROM.Thm54.VclL.Compute.TowerD.rowFactsAt_CFvW4,
    `Nock.NockVMROM.Thm54.PlusIOSegmentedFamily,
    `Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedStrictNockVMROMPackage,
    `Nock.NockVMROM.Thm54.PlusIOSegmentedFamily.memoryWalkAlpha,
    `Nock.NockVMROM.Thm54.ExactConfig.kMem,
    `Nock.NockVMROM.Thm54.ExactConfig.memRows,
    `Nock.NockVMROM.Thm54.ChallengeVector.lam,
    `Nock.NockVMROM.Thm54.PartA12.walkAccStepInGate12]
  let mut bad : Array Name := #[]
  for n in dropped ++ extras do
    unless (env.find? n).isSome do throwError "name does not resolve: {n}"
    if R.contains n then bad := bad.push n
  unless bad.isEmpty do throwError "reached (must not be): {bad}"
  let par := reachP env roots
  for n in [`Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.shapeV, `Nock.NockVMROM.Thm54.VclL.Chips.Path.colRoundT] do
    unless R.contains n do throwError "expected still reached (transitively): {n}"
    let ch := chainTo par n
    logInfo s!"B2001 CHAIN to {n} ({ch.length - 1} steps): {" -> ".intercalate (ch.map toString)}"
    for pb in [`Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.pathChip, `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.memSoundnessVCL] do
      if ch.contains pb then throwError "chain to {n} routes through {pb}"
  logInfo s!"B2001 reach size {R.size}; Walk37/VCL38 reached 0; dropped {dropped.length} + extras {extras.length}: all reach = false; positive controls {pos.length} reached"
