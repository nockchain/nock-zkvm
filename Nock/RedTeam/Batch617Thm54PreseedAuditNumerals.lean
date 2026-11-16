/-
  Nock/RedTeam/Batch617Thm54PreseedAuditNumerals.lean

  Notes only; not a pass.

  Q5: the restated receipts.  Numerals-only restatements keep their strength.  Names that now
  misdescribe their content (asserted against the live statements so the list is checked):
  `Batch274.memory_s_unmoved` (docstring "`M.rap.s = 113`", statement `156 ∧ 204`; it has moved at
  every memory move since), `Batch408.memory_s_is_146` (`= 156`), `Batch408.memory_s_still_140`
  (`= 156`), `Batch580.memory_width_delta` (name says delta, statement says equality — the F4
  meaning change), `Batch580.compute_width_delta` (documents a withdrawn proposal: `303 = 302 + 1`
  is arithmetic about a column that does not exist).  No restated receipt's conclusion
  was weakened other than by that premise.
-/
import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.RedTeam.Batch274Thm54AnchorsAndAssemblyReview
import Nock.RedTeam.Batch408Thm54SeedBoundaryGates
import Nock.RedTeam.Batch580Thm54PreseedChronology
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Lean Elab Command Meta

namespace Nock.RedTeam.Batch617

open scoped Polynomial
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.Thm54Resources

noncomputable section

/-! ## Q6 — numerals -/

theorem resource_numerals :
    computeColumns deployedExtensionDegree = 303 ∧
      computeConstraints deployedExtensionDegree = 418 ∧
      memoryColumns deployedExtensionDegree = 205 ∧
      memoryConstraints deployedExtensionDegree = 156 :=
  ⟨computeColumns_deployed, computeConstraints_deployed, memoryColumns_deployed,
    memoryConstraints_deployed⟩

section Pkg
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem package_numerals (R : P.OptimizedFullCostRealization) :
    (P.computeChip.rap.w = 303 ∧ P.computeChip.rap.s = 418 ∧
        P.computeChip.rap.d = 4 ∧ P.computeChip.rap.k = 2) ∧
      (P.memoryChip.rap.w = 205 ∧ P.memoryChip.rap.s = 156 ∧
        P.memoryChip.rap.d = 4 ∧ P.memoryChip.rap.k = 1) :=
  ⟨(P.cost_realization_deployed_numerals R).1, (P.cost_realization_deployed_numerals R).2.1⟩

end Pkg

theorem challenge_space (K F : Type) [Fintype K] [Fintype F] :
    Fintype.card (OptimizedProductionChallengeTuple K F) = Fintype.card K ^ 11 :=
  card_optimizedProductionChallengeTuple K F

theorem consumed_bound_body (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedHostileProductionFailureProbabilityBound cardK cardF p8Work ioWork N M =
      (p8Work +
        OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
        pricedWalkWork N M : ℚ) / cardK +
      (ioWork : ℚ) / cardK ^ 2 +
      ((FiniteIO.ioFailureUnionBound 10 M M cardK + cardK * M : ℕ) : ℚ) / cardK ^ 2 := rfl

/-! ## Q6 — binders -/

def binders (n : Name) : MetaM (ℕ × ℕ × Array Name) := do
  let some ci := (← getEnv).find? n | throwError m!"missing {n}"
  Meta.forallTelescope ci.type fun xs _ => do
    let mut explicit := 0
    let mut names : Array Name := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      names := names.push d.userName
      if d.binderInfo.isExplicit then explicit := explicit + 1
    return (xs.size, explicit, names)

run_cmd do
  let (tz, ez, nz) ← liftTermElabM <| binders ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
  let (tp, ep, _) ← liftTermElabM <| binders ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76
  logInfo m!"nockCompiles_zmod {tz}/{ez}; nockCompiles_p76 {tp}/{ep}; zmod binder names {nz}"
  unless tz == 27 ∧ ez == 14 do throwError m!"nockCompiles_zmod binders moved: {tz}/{ez}"
  unless tp == 31 ∧ ep == 16 do
  unless nz.contains `αW ∧ nz.contains `lmb ∧ nz.contains `hp64 ∧ nz.contains `hp do
    throwError "expected lmb / hp64 / hp among the binders"

/-! ## Q5 — restated receipts: names vs content (checked against the live statements) -/

section Names
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

example : P.memoryChip.rap.s = 156 ∧ P.memoryChip.rap.w = 205 := Batch274.memory_s_unmoved P
example : Thm54Resources.memoryConstraints 3 = 156 := Batch408.memory_s_is_146
example : Thm54Resources.memoryConstraints 3 = 156 := Batch408.memory_s_still_140
example : Batch580.memoryWidthAfterAtom + 1 = memoryColumns deployedExtensionDegree :=
  Batch580.memory_width_delta
example : Batch580.computeWidthAfterAtom = computeColumns deployedExtensionDegree :=
  Batch580.compute_width_delta

end Names

#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.RedTeam.Batch617.package_numerals

end

end Nock.RedTeam.Batch617
