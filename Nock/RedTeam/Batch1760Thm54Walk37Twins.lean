/-
  Nock/RedTeam/Batch1760Thm54Walk37Twins.lean

  Every other reader changed only `import` / `open` lines (one header comment, one
  `open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54`).
-/
import Nock.NockVMROM.Thm54.Walk37.PaperNames
import Nock.NockVMROM.Thm54.OptimizedStrictFullPackageConcrete

set_option autoImplicit false

namespace Nock.RedTeam.Batch1760

open Lean

run_cmd do
  let env ← getEnv
  let S := `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
  let some _ := env.find? S | throwError "Walk37 statement missing"
  let fs := getStructureFields env S
  unless fs.contains `staged_false_acceptance_bound && fs.contains `acceptance_to_target do
    throwError "Walk37 statement is not the 37th's: {fs}"
  logInfo m!"WALK37-STATEMENT-FIELDS {fs.size} {fs}"
  let some ci := env.find? `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
    | throwError "Walk37 capstone missing"
  let n : Nat ← Lean.Elab.Command.liftTermElabM (Lean.Meta.forallTelescope ci.type fun xs _ => pure xs.size)
  logInfo m!"WALK37-CAPSTONE-BINDERS {n}"

#check @Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.Walk37.«Thm:NockVMROM»

end Nock.RedTeam.Batch1760
