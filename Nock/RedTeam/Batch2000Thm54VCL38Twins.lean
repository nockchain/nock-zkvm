/-
  Nock/RedTeam/Batch2000Thm54VCL38Twins.lean

  * **Twins (item 4).**
  * **Reconciliation (item 3).**
  * The derived walk-family instances: `algZModW (ZMod p) K` is `Batch1996.algRC p K` (`rfl`), so the
    package's honest datum at `F = ZMod p` is W4d's.
-/
import Nock.NockVMROM.Thm54.VCL38.GenNockCompilesVCL
import Nock.NockVMROM.Thm54.Walk39.GenNockCompilesVCL
import Nock.RedTeam.Batch1996Thm54WalkW4dCompletenessChosen

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch2000

open Lean Meta
open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD

run_cmd do
  let env ← getEnv
  let want : Array Name := #[`standalone, `bound, `figure_155, `figure_154, `figure_164, `completeness]
  let S38 := `Nock.VCL38.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
  let S39 := `Nock.Walk39.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
  for S in [S38, S39] do
    let fs := getStructureFields env S
    unless fs == want do throwError "{S}: fields {fs}"
  let boundOf (S : Name) : MetaM (Array Name) := do
    let some ci := env.find? (S ++ `bound) | throwError "no bound projection {S}"
    pure ci.type.getUsedConstants
  let b38 ← Lean.Elab.Command.liftTermElabM (boundOf S38)
  let b39 ← Lean.Elab.Command.liftTermElabM (boundOf S39)
  let v := `Nock.NockVMROM.Thm54.VclL.Events.«boundVCL''»
  let w := `Nock.NockVMROM.Thm54.VclL.Events.«boundVCLW''»
  unless b38.contains v && !b38.contains w do throwError "the 38th twin's bound is not boundVCL''"
  unless b39.contains w && !b39.contains v do throwError "the 39th bound is not boundVCLW''"
  let some ci := env.find? `Nock.VCL38.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
    | throwError "38th twin capstone missing"
  let (n, p) : Nat × Nat ← Lean.Elab.Command.liftTermElabM <| forallTelescope ci.type fun xs _ => do
    let mut props : Nat := 0
    for x in xs do
      if (← isProp (← x.fvarId!.getDecl).type) then props := props + 1
    pure (xs.size, props)
  unless n == 13 && p == 2 do throwError "38th twin capstone binders {n}/{p}"
  logInfo m!"B2000 38th twin: six fields, bound = boundVCL'', capstone 13/2; live 39th: six fields, bound = boundVCLW''"

noncomputable section
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (hT hP hC kr : ℕ)

theorem CFvW4_eq_CFvW : CFvW4 (K := K) δF hT hP hC = VclL.StandaloneW.CFvW (K := K) δF hT hP hC := rfl

theorem MFvW4_eq_MFvW :
    MFvW4 (K := K) δF hT hP hC kr = VclL.StandaloneW.MFvW (K := K) δF hT hP hC kr := rfl

theorem extraPremises_vclW4_eq :
    extraPremises_vclW4 (K := K) δF hT hP hC kr = VclL.StandaloneW.extraPremises_vclW δF hT hP hC kr := rfl

theorem rowFactsAt_CFvW4_eq :
    rowFactsAt_CFvW4 (K := K) δF hT hP hC = VclL.StandaloneW.rowFactsAt_CFvW δF hT hP hC := rfl

end

/-- The derived walk-family algebra at `F = ZMod p` is W4d's `algRC` (both are `ZMod.algebra`). -/
theorem algZModW_zmod (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [CharP K p] :
    algZModW (ZMod p) K = Batch1996.algRC p K := rfl

end Nock.RedTeam.Batch2000

#print axioms Nock.RedTeam.Batch2000.CFvW4_eq_CFvW
#print axioms Nock.RedTeam.Batch2000.MFvW4_eq_MFvW
#print axioms Nock.RedTeam.Batch2000.extraPremises_vclW4_eq
#print axioms Nock.RedTeam.Batch2000.rowFactsAt_CFvW4_eq
#print axioms Nock.RedTeam.Batch2000.algZModW_zmod
