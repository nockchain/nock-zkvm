/-
  Nock/RedTeam/Batch930Thm54Part2aReview.lean

  * `Batch887`
    checks seven names.
  * **(B) Binder counts (check 8).**  `nockCompiles_zmod` 26/13 (unchanged); `nockCompiles_p76`
    29/14 (`+hrows`), measured on the elaborated types.
  * **(C) Figures (check 7).**  Axioms of the three figure theorems printed below.
-/
import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.MemoryWalkRoots
import Nock.NockVMROM.Thm54.RealProgramSoundness
import Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch930

open Lean Elab Command Meta

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
def DA : Name := `Nock.NockVMROM.Thm54.DeployedAcceptance

def roots : Array Name := #[
  ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod,
  ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76,
  ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package,
  ``Nock.NockVMROM.Thm54.RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_31,
  ``Nock.NockVMROM.Thm54.RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_32,
  ``Nock.NockVMROM.Thm54.GoldilocksParameters.hostile_soundness_at_paper_configuration]

/-! ## (A) -/
run_cmd do
  let env ← getEnv
  let mut hist : Array Name := #[`Nock.Walk37.Nock.NockVMROM.Thm54.deployedAcceptance_of_historical,
    ``Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.optimizedFullStrict_hostile_LIO_historical]
  hist := env.constants.fold (init := hist) fun acc n _ =>
    if PKG.isPrefixOf n && env.getModuleFor? n == some DA then acc.push n else acc
  unless hist.size ≥ 10 do throwError m!"historical section too small to be the right set: {hist}"
  logInfo m!"historical section ({hist.size} names): {hist.qsort (·.toString < ·.toString)}"
  let pc1 := reachSet env #[``Nock.NockVMROM.Thm54.MemoryWalkRoots.memory_roots_bound_by_LIO]
  unless pc1.contains (PKG ++ `OptimizedHistoricalAcceptanceAt) do
    throwError "positive control 1 failed: memory_roots_bound_by_LIO does not reach the historical acceptance"
  let pc2 := reachSet env #[``Nock.NockVMROM.Thm54.DeployedAcceptanceAt.of_acceptance]
  unless pc2.contains (PKG ++ `OptimizedProductionAcceptanceAt) do
    throwError "positive control 2 failed: of_acceptance does not reach the live acceptance"
  if pc2.contains (PKG ++ `OptimizedHistoricalAcceptanceAt) then
    throwError "of_acceptance reaches the historical acceptance (alias?)"
  for r in roots do
    let cl := reachSet env #[r]
    let hits := hist.filter cl.contains
    logInfo m!"{r}: closure {cl.size}; historical-section names reached: {hits.size}"
    unless hits.isEmpty do throwError m!"{r} reaches the historical section: {hits}"
  logInfo "Batch930 (A): no constant of the historical section is reached from the six roots"

/-- (B) binder counts on the elaborated types: (total, explicit). -/
def binderCounts (env : Environment) (n : Name) : MetaM (Nat × Nat) := do
  let some ci := env.find? n | throwError m!"missing {n}"
  Meta.forallTelescope ci.type fun xs _ => do
    let mut ex := 0
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then ex := ex + 1
    pure (xs.size, ex)

run_cmd do
  let env ← getEnv
  let (z, zx) ← liftTermElabM (binderCounts env ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod)
  let (p, px) ← liftTermElabM (binderCounts env ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76)
  logInfo m!"nockCompiles_zmod {z}/{zx}; nockCompiles_p76 {p}/{px}"
  unless (z, zx) == (27, 14) do throwError m!"nockCompiles_zmod moved: {z}/{zx} (expected 27/14)"
  unless (p, px) == (31, 16) do throwError m!"nockCompiles_p76 is {p}/{px} (expected 31/16: the 36th + hFprime, S2 + αW)"

end Nock.RedTeam.Batch930

/-! ## (C) the figures at the corrected tip -/
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_31
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_32
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.hostile_soundness_at_paper_configuration
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.acceptance_outside_failure_implies_target
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.famIOEventOf_card_le
