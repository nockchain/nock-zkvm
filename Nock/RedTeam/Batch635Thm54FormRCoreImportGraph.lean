/-
  Nock/RedTeam/Batch635Thm54FormRCoreImportGraph.lean

  **Lane `formR-core-lift`: the import-graph receipts of the Form R core lift.**
.

  What moved (verbatim, same fully qualified names; `Batch637` checks the types):
  * `Batch554` §§A–C → `Thm54/FormRCore/PwFunctional.lean`; `Batch556` §§A–C →
    `FormRCore/PwEvent.lean`; `Batch557.pwAccountingWork'` (+ `_majorises`) →
    `FormRCore/Majorant.lean`; `Batch575`'s accumulators, S1, S2's identity and S3 →
    `FormRCore/Mtree.lean`; `FormRCore.lean` re-exports the four.
  * `FormRAxisEvent`'s A1 (`formRN` … `formRTemplatePolynomial`) →
    `Thm54/FormRTemplatePolynomial.lean` (imports `FormRCore` and `TemplateAxisCounting` only).
  * `FormRAxisEvent.lean` now imports `FormRTemplatePolynomial` instead of `Batch575` / `Batch556` /
    `Batch557`.

  Receipts (this file):
  * **`import_ok`.**
  * **The import-graph fact, as a `run_cmd`.**  They contain
    none of the Form R batches (`Batch554`/`555`/`556`/`557`/`575`).
  * **Positive controls, same instrument.**  Over the NEW `FormRAxisEvent` it finds
    `ProductionP8Containment` and `OptimizedStrictPackage` (reached through
    `RoundFibredSoundness`): the walk does see transitive production modules.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.FormRAxisEvent
import Nock.NockVMROM.Thm54.FormRCore
import Nock.NockVMROM.Thm54.FormRTemplatePolynomial
import Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
import Nock.NockVMROM.Thm54.TemplateAxisCounting
import Nock.NockVMROM.Thm54.RoundFibredSoundness
import Nock.NockVMROM.Thm54.SemanticTimestampStrategy
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.RedTeam.Batch575Thm54FormRMtree
import Nock.RedTeam.Batch556Thm54PwEvent
import Nock.RedTeam.Batch557Thm54RangeGadget
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch635

open Lean

/-! ## The instrument: transitive imports of a set of modules, read off the environment header -/

/-- The modules transitively imported by `roots` (the roots included), walking
`env.header.moduleData[i].imports`.  Every root must be a module of the current environment. -/
partial def importReach (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : List Name := roots.toList
  while !todo.isEmpty do
    let m := todo.head!
    todo := todo.tail!
    if seen.contains m then continue
    seen := seen.insert m
    if let some i := env.getModuleIdx? m then
      for imp in env.header.moduleData[i.toNat]!.imports do
        if !seen.contains imp.module then todo := imp.module :: todo
  return seen

/-- The `Nock.RedTeam.*` modules in a reach set. -/
def redTeamIn (s : NameSet) : List Name :=
  s.toList.filter fun m => (`Nock.RedTeam).isPrefixOf m

def pinnedMod : Name := `Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
def carrierMod : Name := `Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
def strictPkgMod : Name := `Nock.NockVMROM.Thm54.OptimizedStrictPackage
def p8Mod : Name := `Nock.NockVMROM.Thm54.ProductionP8Containment
def formRBatchMods : Array Name :=
  #[`Nock.RedTeam.Batch554Thm54PwFunctional, `Nock.RedTeam.Batch555Thm54PwCertificate,
    `Nock.RedTeam.Batch556Thm54PwEvent, `Nock.RedTeam.Batch557Thm54RangeGadget,
    `Nock.RedTeam.Batch575Thm54FormRMtree]

def eventMod : Name := `Nock.NockVMROM.Thm54.FormRAxisEvent
def coreMod : Name := `Nock.NockVMROM.Thm54.FormRCore
def templateMod : Name := `Nock.NockVMROM.Thm54.FormRTemplatePolynomial

def oldEventImports : Array Name :=
  #[`Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier,
    `Nock.NockVMROM.Thm54.TemplateAxisCounting,
    `Nock.NockVMROM.Thm54.RoundFibredSoundness,
    `Nock.NockVMROM.Thm54.SemanticTimestampStrategy,
    `Nock.NockVMROM.Thm54.DeployedChipFamily,
    `Nock.RedTeam.Batch575Thm54FormRMtree,
    `Nock.RedTeam.Batch556Thm54PwEvent,
    `Nock.RedTeam.Batch557Thm54RangeGadget]


run_cmd do
  let env ← getEnv
  let s := importReach env #[eventMod]
  unless (env.getModuleIdx? eventMod).isSome do throwError "FormRAxisEvent is not loaded"
  if s.contains pinnedMod then throwError "FormRAxisEvent reaches the pinned file"
  if s.contains carrierMod then throwError "FormRAxisEvent reaches GenNockCompilesCarrier"
  unless s.contains coreMod && s.contains templateMod do
    throwError "FormRAxisEvent does not reach the new core"
  let formRBatches := (redTeamIn s).filter fun m => formRBatchMods.contains m
  unless formRBatches.isEmpty do throwError "FormRAxisEvent reaches Form R batches: {formRBatches}"
  let pin := importReach env #[pinnedMod]
  let extra := (redTeamIn s).filter fun m => !pin.contains m
  unless extra.isEmpty do
    throwError "FormRAxisEvent reaches red-team modules the pinned file does not: {extra}"
  logInfo m!"R1: FormRAxisEvent reaches {s.size} modules; OptimizedStrictFullPackage: absent; \
    GenNockCompilesCarrier: absent; Batch554/555/556/557/575: absent; its \
    {(redTeamIn s).length} red-team modules are all reached by the pinned file itself \
    ({(redTeamIn pin).length}): {(redTeamIn s).toArray.qsort (·.toString < ·.toString)}; \
    FormRCore, FormRTemplatePolynomial: present"

/-! ## R2: the core and the template polynomial sit below `OptimizedStrictPackage` and
`ProductionP8Containment` -/

run_cmd do
  let env ← getEnv
  for root in #[coreMod, templateMod] do
    let s := importReach env #[root]
    let rt := redTeamIn s
    unless rt.isEmpty do throwError "{root} reaches red-team modules: {rt}"
    for bad in #[pinnedMod, carrierMod, strictPkgMod, p8Mod] do
      if s.contains bad then throwError "{root} reaches {bad}"
    logInfo m!"R2: {root} reaches {s.size} modules; none of Nock.RedTeam.*, \
      OptimizedStrictFullPackage, GenNockCompilesCarrier, OptimizedStrictPackage, \
      ProductionP8Containment"

/-! ## Positive controls (same instrument) -/

/-! **PC1.** -/

run_cmd do
  let env ← getEnv
  let s := importReach env oldEventImports
  for want in #[`Nock.RedTeam.Batch575Thm54FormRMtree, pinnedMod, carrierMod] do
    unless s.contains want do throwError "positive control failed: {want} not found"
  logInfo m!"PC1: the bb42fcc1 FormRAxisEvent import set reaches Batch575Thm54FormRMtree, \
    OptimizedStrictFullPackage and GenNockCompilesCarrier ({(redTeamIn s).length} red-team \
    modules)"

/-! **PC2.** -/

run_cmd do
  let env ← getEnv
  let s := importReach env #[eventMod]
  for want in #[p8Mod, strictPkgMod] do
    unless s.contains want do throwError "positive control failed: {want} not found"
  logInfo m!"PC2: FormRAxisEvent reaches ProductionP8Containment and OptimizedStrictPackage"

/-! **PC3.** -/

run_cmd do
  let env ← getEnv
  let s := importReach env #[pinnedMod]
  unless s.contains eventMod do throwError "the pinned file does not import FormRAxisEvent"
  logInfo m!"PC3 (30th): OptimizedStrictFullPackage imports FormRAxisEvent"

end Nock.RedTeam.Batch635


namespace Nock.RedTeam.Batch635

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FormRAxisEvent
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open scoped Classical Polynomial

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

/-- **`import_ok`.** -/
theorem pinned_event_union_guarded {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (E' : ℕ) :
    (P.optimizedFailureEvent Qc Qm ∪ formRGuardedUnion E E').card
      ≤ (P.optimizedFailureEvent Qc Qm).card + (formRGuardedUnion E E').card :=
  Finset.card_union_le _ _

end Nock.RedTeam.Batch635

#print axioms Nock.RedTeam.Batch635.pinned_event_union_guarded
