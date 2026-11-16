/-
  Nock/RedTeam/Batch611Thm54PreseedNothingElseMoved.lean

  Notes only; not a pass.

  * Compute `w / s = 302 / 416`, `d = 4` on both chips, memory `k = 1`, memory `204 / 156`.
  * Challenge space `|𝕂|¹¹` (`card_optimizedProductionChallengeTuple`, no coin).
  * `#print axioms` on `optimizedFullStrictNockVMROM_of_package`, `nockCompiles_zmod`,
    `nockCompiles_p76` at the end of the file.
-/
import Lean
import Nock.RedTeam.Batch601Thm54PreseedAtomMemoryGate
import Nock.NockVMROM.Thm54.GoldilocksParameters
import Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

open Lean Elab Command Meta

namespace Nock.RedTeam.Batch611

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.Thm54Resources

theorem numerals_after :
    memoryColumns deployedExtensionDegree = 205 ∧
      memoryConstraints deployedExtensionDegree = 156 ∧
      computeColumns deployedExtensionDegree = 303 ∧
      computeConstraints deployedExtensionDegree = 418 ∧
      maxConstraintDegree = 4 ∧ memoryCommittedRounds = 1 :=
  ⟨memoryColumns_deployed, memoryConstraints_deployed, computeColumns_deployed,
    computeConstraints_deployed, rfl, rfl⟩

theorem challenge_space_unmoved (K F : Type) [Fintype K] [Fintype F] :
    Fintype.card (OptimizedStrictPackage.OptimizedProductionChallengeTuple K F) =
      Fintype.card K ^ 11 :=
  OptimizedStrictPackage.card_optimizedProductionChallengeTuple K F

theorem consumed_bound_unmoved (cardK cardF p8Work ioWork N M : ℕ) :
    OptimizedStrictPackage.optimizedHostileProductionFailureProbabilityBound
        cardK cardF p8Work ioWork N M =
      OptimizedStrictPackage.optimizedHostileProductionFailureProbabilityBound
        cardK cardF p8Work ioWork N M := rfl

#check @OptimizedStrictPackage.optimizedHostileProductionFailureProbabilityBound_byte_identical
#check @GoldilocksParameters.hostile_soundness_at_paper_configuration
#check @RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_31
#check @RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_32

def binderTelescope (n : Name) : MetaM (Array (Name × BinderInfo)) := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs _ =>
    xs.mapM fun x => do
      let l ← x.fvarId!.getDecl
      pure (l.userName, l.binderInfo)

run_cmd liftTermElabM do
  let nZ : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
  let n76 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76
  for (n, tot, ex) in [(nZ, 27, 14), (n76, 31, 16)] do
    let tel ← binderTelescope n
    let expl := tel.filter (fun (_, bi) => bi == .default)
    logInfo m!"{n}: total {tel.size}, explicit {expl.size}: {expl.map (·.1)}"
    unless tel.size == tot && expl.size == ex do
      throwError m!"{n}: expected {tot}/{ex}, got {tel.size}/{expl.size}"

end Nock.RedTeam.Batch611

#print axioms Nock.RedTeam.Batch611.numerals_after
#print axioms Nock.RedTeam.Batch611.challenge_space_unmoved
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76
