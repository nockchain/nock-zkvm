/-
  Nock/RedTeam/Batch636Thm54FormRGuardedBelowPinned.lean

  So `OptimizedStrictFullPackage` could import this
  module (or `FormRAxisEvent`) without a cycle — the reverse direction of `Batch635`'s `import_ok`,
  which before the lift failed with `build cycle detected`.  The `example`s name
  `formRGuardedUnion`, `formRGuardedBad` and `formRTemplatePolynomial` at the production tuple
  type, with no scratch definitions.
-/
import Nock.NockVMROM.Thm54.FormRAxisEvent

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch636

open Lean

/-! Positive control: `FormRAxisEvent`, `FormRCore.Mtree` and `ProductionP8Containment` are
loaded. -/

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  for bad in #[`Nock.NockVMROM.Thm54.OptimizedStrictFullPackage,
      `Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier] do
    if mods.contains bad then throwError "Batch636 loads {bad}"
  for bad in #[`Nock.RedTeam.Batch554Thm54PwFunctional, `Nock.RedTeam.Batch555Thm54PwCertificate,
      `Nock.RedTeam.Batch556Thm54PwEvent, `Nock.RedTeam.Batch557Thm54RangeGadget,
      `Nock.RedTeam.Batch575Thm54FormRMtree] do
    if mods.contains bad then throwError "Batch636 loads the Form R batch {bad}"
  let rt := mods.toList.filter fun m => (`Nock.RedTeam).isPrefixOf m
  for want in #[`Nock.NockVMROM.Thm54.FormRAxisEvent, `Nock.NockVMROM.Thm54.FormRCore.Mtree,
      `Nock.NockVMROM.Thm54.ProductionP8Containment] do
    unless mods.contains want do throwError "positive control failed: {want} not loaded"
  logInfo m!"Batch636 loads {mods.size} modules: no OptimizedStrictFullPackage, no \
    GenNockCompilesCarrier, no Form R batch; {rt.length} red-team modules (production's own); \
    FormRAxisEvent, FormRCore.Mtree and ProductionP8Containment loaded"

end Nock.RedTeam.Batch636

namespace Nock.RedTeam.Batch636

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FormRAxisEvent
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.OptimizedStrictPackage

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] [Fintype F]

noncomputable example {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (E' : ℕ) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  formRGuardedUnion E E'

/-- Each guarded tree event is inside the union (`Finset.mem_biUnion`). -/
theorem guardedBad_subset_union {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (i : Fin T.kMem) (E' : ℕ) :
    formRGuardedBad E i E' ⊆ formRGuardedUnion E E' := by
  intro c hc
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hc⟩

noncomputable example {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (i : Fin T.kMem) :
    Polynomial (Polynomial K) :=
  formRTemplatePolynomial E i

end Nock.RedTeam.Batch636

#print axioms Nock.RedTeam.Batch636.guardedBad_subset_union
