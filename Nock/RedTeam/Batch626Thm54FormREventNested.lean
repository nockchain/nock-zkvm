/-
  Nock/RedTeam/Batch626Thm54FormREventNested.lean

  Notes only; not a pass.  Own walker (types AND values,
  `value?

  * Check 8: direct users of `AxisBridge.ReadVerifyNested` / `AxisBatching.MTree.Nested` in the
    closure of `nockCompiles_zmod` and of `of_package`, counted and listed; positive controls: the
    two targets are in both closures, and `alphaFreeAxisStructureCheck_eq_true_iff` is flagged.
  * Check 9: compute `302 / 416`, memory `204 / 156` (the deployed numeral theorems);
    `nockCompiles_zmod` 26/13, `p76` 28/13; `#print axioms` on A2, A4, B2 (`compute_core_classes`,
    `memory_mixed_classes`), `of_package`, `nockCompiles_zmod`.
-/
import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.FormRAxisEvent
import Nock.NockVMROM.Thm54.DeployedStaging
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
open Lean Elab Command Meta

namespace Nock.RedTeam.Batch626

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

def targets : Array Name := #[``Nock.AxisBridge.ReadVerifyNested, ``Nock.AxisBatching.MTree.Nested]

def mentionsTarget (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | none => false
  | some ci =>
    let cs := ci.type.getUsedConstants ++
      ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
    targets.any cs.contains

def zmod : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
def ofPkg : Name :=
  ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

run_cmd do
  let env ← getEnv
  let stop : Name → Bool := fun n => !(`Nock).isPrefixOf n
  let rz := reach env #[zmod] stop
  let rp := reach env #[ofPkg] stop
  for t in targets do
    unless rz.contains t ∧ rp.contains t do throwError m!"positive control: {t} not in a closure"
  let hz := (rz.toArray.filter (mentionsTarget env)).qsort (·.toString < ·.toString)
  let hp := (rp.toArray.filter (mentionsTarget env)).qsort (·.toString < ·.toString)
  logInfo m!"nockCompiles_zmod: {hz.size} direct Nested consumers: {hz}"
  logInfo m!"of_package: {hp.size} direct Nested consumers: {hp}"
  unless hz.size == 28 do throwError m!"zmod consumer count moved: {hz.size}"
  unless hp.size == 22 do throwError m!"of_package consumer count moved: {hp.size}"
  unless hp.all hz.contains do throwError "of_package consumers are not a subset"
  -- positive controls
  let ctrl := ``Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck_eq_true_iff
  unless hz.contains ctrl ∧ hp.contains ctrl do throwError "control theorem not flagged"
  let bodyOnly := ``Nock.NockVMROM.Thm54.ServedMemoryTrace.ServiceWalk.axisValidity
  unless hz.contains bodyOnly ∧ !hp.contains bodyOnly do
    throwError "body-walk control failed (ServiceWalk.axisValidity)"
  -- a type-only walk would miss theorem-body consumers: count how many flagged names are
  -- reached from zmod ONLY through some theorem's value (never named in any type on the path)
  let typeOnly : Std.HashSet Name := Id.run do
    let mut seen : Std.HashSet Name := {}
    let mut work := [zmod]
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
          -- descend into values of DEFINITIONS only, never theorem proofs
          match ci with
          | .thmInfo _ => pure ()
          | _ => if let some v := ci.value? then cs := cs ++ v.getUsedConstants
          for c in cs do
            unless seen.contains c do work := c :: work
    return seen
  let missed := hz.filter fun n => !typeOnly.contains n
  logInfo m!"consumers a type-only walk would miss from zmod: {missed.size}: {missed}"

/-! ## Check 9 — numerals, binders -/

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.Thm54Resources in
theorem numerals :
    computeColumns deployedExtensionDegree = 303 ∧ computeConstraints deployedExtensionDegree = 418 ∧
      memoryColumns deployedExtensionDegree = 205 ∧ memoryConstraints deployedExtensionDegree = 156 :=
  ⟨computeColumns_deployed, computeConstraints_deployed, memoryColumns_deployed,
    memoryConstraints_deployed⟩

def binders (n : Name) : MetaM (ℕ × ℕ) := do
  let some ci := (← getEnv).find? n | throwError m!"missing {n}"
  Meta.forallTelescope ci.type fun xs _ => do
    let mut explicit := 0
    for x in xs do
      if (← x.fvarId!.getDecl).binderInfo.isExplicit then explicit := explicit + 1
    return (xs.size, explicit)

run_cmd do
  let (tz, ez) ← liftTermElabM <| binders zmod
  let (tp, ep) ← liftTermElabM <| binders ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76
  logInfo m!"nockCompiles_zmod {tz}/{ez}; nockCompiles_p76 {tp}/{ep}"
  unless tz == 27 ∧ ez == 14 ∧ tp == 31 ∧ ep == 16 do throwError "binders moved"

#print axioms Nock.NockVMROM.Thm54.FormRAxisEvent.formR_identity_iff_path
#print axioms Nock.NockVMROM.Thm54.FormRAxisEvent.formRBadAt_readsOn
#print axioms Nock.NockVMROM.Thm54.FormRAxisEvent.encodedTBad_not_readsOn
#print axioms Nock.NockVMROM.Thm54.FormRAxisEvent.formRGuardedAxisFailureEvent_card_le
#print axioms Nock.NockVMROM.Thm54.DeployedStaging.compute_core_classes
#print axioms Nock.NockVMROM.Thm54.DeployedStaging.memory_mixed_classes
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod

end Nock.RedTeam.Batch626
