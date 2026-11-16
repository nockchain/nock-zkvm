/-
  Nock/RedTeam/Batch1762Thm54MM38Accounting.lean

  * Compiled: `exact_vcl_one_one_three_one`.
-/
import Nock.NockVMROM.Thm54.VCL38.GenNockCompilesVCL
import Nock.PaperNames

set_option autoImplicit false

namespace Nock.RedTeam.Batch1762

open Lean Meta

theorem exact_vcl_one_one_three_one : (1 + 1 + 3 + 1 : ℕ) = 6 := rfl

run_cmd do
  let env ← getEnv
  let S := `Nock.VCL38.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
  let fs := getStructureFields env S
  let want : Array Name := #[`standalone, `bound, `figure_155, `figure_154, `figure_164, `completeness]
  unless fs == want do throwError "38th statement fields are not exactly {want}: {fs}"
  logInfo m!"STATEMENT-FIELDS {fs.size} {fs}"

-- Binder census, asserted.
run_cmd do
  let env ← getEnv
  let rows : List (Name × Nat × Nat) := [
    (`Nock.VCL38.Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompiles_zmod, 25, 15),
    (`Nock.VCL38.Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompilesHostile, 25, 15),
    (`Nock.VCL38.Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompiles_p76, 28, 15)]
  for (c, tot, pr) in rows do
    let some ci := env.find? c | throwError "missing {c}"
    let (n, p, names) : Nat × Nat × Array String ← Lean.Elab.Command.liftTermElabM <| forallTelescope ci.type fun xs _ => do
      let mut props : Nat := 0
      let mut nm : Array String := #[]
      for x in xs do
        let d ← x.fvarId!.getDecl
        let isP ← isProp d.type
        if isP then props := props + 1
        nm := nm.push s!"{d.userName.eraseMacroScopes}{if isP then "*" else ""}"
      pure (xs.size, props, nm)
    logInfo m!"BINDERS {c}: {n}/{p} {names}"
    unless n == tot && p == pr do throwError "binder count of {c} is {n}/{p}, authorized {tot}/{pr}"
  -- the capstone: only `F K` + 8 instances + `hOrb` + `P`
  let some ci := env.find? `Nock.VCL38.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
    | throwError "capstone missing"
  let (n, p) : Nat × Nat ← Lean.Elab.Command.liftTermElabM <| forallTelescope ci.type fun xs _ => do
    let mut props : Nat := 0
    for x in xs do
      let d ← x.fvarId!.getDecl
      if (← isProp d.type) then props := props + 1
    pure (xs.size, props)
  logInfo m!"CAPSTONE-BINDERS {n}/{p}"
  unless p == 2 do throwError "capstone has Prop binders beyond the two instance Props: {n}/{p}"

#check @Nock.VCL38.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#check @Nock.VCL38.Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompiles_zmod
#print axioms Nock.VCL38.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms «Thm:NockVMROM»
#print axioms Nock.VCL38.Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompiles_zmod
#print axioms Nock.VCL38.Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompilesHostile
#print axioms Nock.VCL38.Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompiles_p76
#print axioms Nock.RedTeam.Batch1882.vcl_standalone_155'
#print axioms Nock.RedTeam.Batch1882.vcl_standalone_154'
#print axioms Nock.RedTeam.Batch1882.vcl_standalone_164'
#print axioms Nock.RedTeam.Batch1938.vcl_completeness'
#print axioms exact_vcl_one_one_three_one

end Nock.RedTeam.Batch1762
