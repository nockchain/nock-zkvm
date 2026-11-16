/-
  Nock/RedTeam/Batch2002Thm54MM39Accounting.lean

  * The families are asserted: the
    `standalone` field's type names `memSoundnessVCLW` and not `memSoundnessVCL`.
  * Binders (`forallTelescope`, total / Prop): `nockCompiles_zmod` 25/15, `nockCompilesHostile` 25/15,
    `nockCompiles_p76` 28/15 — unchanged; the binder list contains `hmemW` and no `hmemP` (item 5: the one
    swap in place).
  * The capstone `optimizedFullStrictNockVMROM_of_package` binds only the package (13/2, unchanged).
-/
import Nock.NockVMROM.Thm54.Walk39.GenNockCompilesVCL
import Nock.PaperNames

set_option autoImplicit false

namespace Nock.RedTeam.Batch2002

open Lean Meta

theorem exact_walk_one_one_three_one : (1 + 1 + 3 + 1 : ℕ) = 6 := rfl

run_cmd do
  let env ← getEnv
  let S := `Nock.Walk39.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
  let fs := getStructureFields env S
  let want : Array Name := #[`standalone, `bound, `figure_155, `figure_154, `figure_164, `completeness]
  unless fs == want do throwError "39th statement fields are not exactly {want}: {fs}"
  let some ci := env.find? (S ++ `standalone) | throwError "no standalone projection"
  let PK := `Nock.Walk39.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage
  let used := ci.type.getUsedConstants
  unless used.contains (PK ++ `CF) && used.contains (PK ++ `MF) do throwError "standalone not at P.CF / P.MF"
  let some mf := env.find? (PK ++ `MF) | throwError "no MF"
  let some cf := env.find? (PK ++ `CF) | throwError "no CF"
  let mfu := (mf.value? (allowOpaque := true)).get!.getUsedConstants
  let cfu := (cf.value? (allowOpaque := true)).get!.getUsedConstants
  let w := `Nock.NockVMROM.Thm54.VclL.StandaloneW.MFvW
  let c := `Nock.NockVMROM.Thm54.VclL.StandaloneW.CFvW
  unless mfu.contains w && cfu.contains c do throwError "P.MF / P.CF are not MFvW / CFvW: {mfu} {cfu}"
  let some mfw := env.find? w | throwError "no MFvW"
  unless (mfw.value? (allowOpaque := true)).get!.getUsedConstants.contains
      `Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.memSoundnessVCLW do throwError "MFvW is not memSoundnessVCLW"
  logInfo m!"STATEMENT-FIELDS {fs.size} {fs}; standalone at MFvW (memSoundnessVCLW)"

-- Binder census, asserted.
run_cmd do
  let env ← getEnv
  let rows : List (Name × Nat × Nat) := [
    (`Nock.Walk39.Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompiles_zmod, 25, 15),
    (`Nock.Walk39.Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompilesHostile, 25, 15),
    (`Nock.Walk39.Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompiles_p76, 28, 15)]
  for (c, tot, pr) in rows do
    let some ci := env.find? c | throwError "missing {c}"
    let (n, p, names) : Nat × Nat × Array String ← Lean.Elab.Command.liftTermElabM <|
      forallTelescope ci.type fun xs body => do
        let mut props : Nat := 0
        let mut nm : Array String := #[]
        for x in xs do
          let d ← x.fvarId!.getDecl
          let isP ← isProp d.type
          if isP then props := props + 1
          nm := nm.push s!"{d.userName.eraseMacroScopes}{if isP then "*" else ""}"
        -- the `∀ hF hrowsC hmemC hmemW hleaf haxis` block sits under a `haveI` in the body
        let inner ← forallTelescope (← whnfR body) fun ys _ => do
          let mut m : Array String := #[]
          for y in ys do m := m.push s!"{(← y.fvarId!.getDecl).userName.eraseMacroScopes}"
          pure m
        pure (xs.size, props, nm ++ inner)
    logInfo m!"BINDERS {c}: {n}/{p} {names}"
    unless n == tot && p == pr do throwError "binder count of {c} is {n}/{p}, authorized {tot}/{pr}"
    unless names.contains "hmemW" || names.contains "hmemW*" do throwError "{c}: no hmemW binder"
    if names.contains "hmemP" || names.contains "hmemP*" then throwError "{c}: hmemP still a binder"
  let some ci := env.find? `Nock.Walk39.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
    | throwError "capstone missing"
  let (n, p) : Nat × Nat ← Lean.Elab.Command.liftTermElabM <| forallTelescope ci.type fun xs _ => do
    let mut props : Nat := 0
    for x in xs do
      if (← isProp (← x.fvarId!.getDecl).type) then props := props + 1
    pure (xs.size, props)
  logInfo m!"CAPSTONE-BINDERS {n}/{p}"
  unless n == 13 && p == 2 do throwError "capstone binders {n}/{p}, expected 13/2"

end Nock.RedTeam.Batch2002

#check @Nock.Walk39.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#check @Nock.Walk39.Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompiles_zmod
#print axioms Nock.Walk39.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms «Thm:NockVMROM»
#print axioms Nock.Walk39.Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompiles_zmod
#print axioms Nock.Walk39.Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompilesHostile
#print axioms Nock.Walk39.Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompiles_p76
#print axioms Nock.NockVMROM.Thm54.VclL.StandaloneW.vcl_standaloneW_155'
#print axioms Nock.NockVMROM.Thm54.VclL.StandaloneW.vcl_standaloneW_154'
#print axioms Nock.NockVMROM.Thm54.VclL.StandaloneW.vcl_standaloneW_164'
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.vcl_completenessW5'
#print axioms Nock.RedTeam.Batch2002.exact_walk_one_one_three_one
