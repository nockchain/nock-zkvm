/-
  Nock/RedTeam/Batch615Thm54PreseedAuditRound.lean

  Notes only; not a pass.

  Two models exist at the consumed capstone, and the atom column is "pre-`z`" in neither in a way
  that distinguishes it from the leaf it pins:

  1. **Chip model** (`of_package`'s `acceptance_to_target`, `complete_false_acceptance_bound`):
     `OptimizedFalseAcceptanceSet Qc Qm` filters the coin tuple with the trace pair `(Qc, Qm)`
     FIXED (`falseAcceptanceSet_def`, by `rfl`).  Every column of `Qm` — the selectors, the `𝕂`
     roles (size columns `6..8`, which hold `z` on honest `halt` rows; the leaf columns `12..14`),
     and the `atom` column `180` — is a parameter there.  The memory RAP has ONE round
     (`memory_single_round`: `rap.k = 1`) whose width is the whole source `181` (`round0_width`);
     the Lean round structure cannot place `atom` before `leaf`.  So this is the same basis every
     prior move used, and on it the 29th is soundness-neutral: the leaf was already "fixed before
     the coins" there.
  2. **Strategy model** (`containment`, `p8`): `TemplateRawJointSoundness.Strategy` carries NO chip
     trace at all, and its pre-seed data is exactly the public claim: the structure
     `DataOnlyTemplateFixedStagedTimestampStrategy` has fields `[claim, afterSeed]` and
     `afterSeed` is a Pi over the seed (`preseed_fields`, run_cmd), i.e. the whole execution —
     every `halt` leaf included — is chosen AFTER `z`.  The names `atomCol` / `haltAtomMixed` are
     not in that structure's type closure (`strategy_blind`).

  Consequence for H1.3 (not for this move): to let the gate carry soundness weight, the census
  must live in a model with a pre-`z` commitment stage for the memory base columns that the
  post-`z` `𝕂` columns are then checked against — a model element neither (1) nor (2) has today.
  The letter's phrase "rests on `OptimizedFalseAcceptanceSet`" is accurate about WHERE the claim is
  stated and silent about this.

  -- the paper
-/
import Lean
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.MemoryHaltAtomDecode

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Lean Elab Command Meta

namespace Nock.RedTeam.Batch615

open scoped Polynomial
open Nock
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension

noncomputable section

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- (1) The consumed false-acceptance set fixes the trace pair and filters coins. -/
theorem falseAcceptanceSet_def
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    c ∈ P.OptimizedFalseAcceptanceSet Qc Qm ↔
      P.OptimizedProductionAcceptanceAt Qc Qm c ∧
        ¬ P.OptimizedProductionGenuineTargetAt Qc Qm c := by
  unfold OptimizedFullStrictNockVMROMPackage.OptimizedFalseAcceptanceSet
  simp [Finset.mem_filter]

/-- The memory RAP has one commitment round at every package with the deployed numerals. -/
theorem memory_single_round (R : P.OptimizedFullCostRealization) : P.memoryChip.rap.k = 1 :=
  (P.cost_realization_deployed_numerals R).2.1.2.2.2

/-- The source memory RAP's single round holds the whole source width, `atom` included:
`wRAP 0 = 182 = 6 + 3·58 + 2` (`181` until the 31st's `reqIdx`). -/
theorem round0_width {h : ℕ} (b : Module.Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    (sourceMemoryRAP b chalVal pubVal orbit H).k = 1 ∧
      ∀ r : Fin (sourceMemoryRAP b chalVal pubVal orbit H).k,
        (sourceMemoryRAP b chalVal pubVal orbit H).wRAP r = 182 := by
  refine ⟨rfl, fun r => ?_⟩
  have hr : (r : ℕ) = 0 := by
    have hk : (sourceMemoryRAP b chalVal pubVal orbit H).k = 1 := rfl
    have h1 := r.isLt
    omega
  simp [sourceMemoryRAP, expandChipTail, ChipTemplate.roundWidthTail, memorySourceTemplate,
    ChipTemplate.roundWidth, hr]

/-- The leaf (`12..14`), the seed-valued size columns (`6..8`) and the atom column (`180`) are all
below the single round's width — the round structure orders none of them before another. -/
theorem all_in_round0 {h : ℕ} (b : Module.Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    ∀ (r : Fin (sourceMemoryRAP b chalVal pubVal orbit H).k) (col : ℕ),
      col ∈ ({6, 12, atomCol} : Finset ℕ) →
      col < (sourceMemoryRAP b chalVal pubVal orbit H).wRAP r := by
  intro r col hcol
  rw [(round0_width b chalVal pubVal orbit H).2 r]
  simp only [Finset.mem_insert, Finset.mem_singleton, atomCol] at hcol
  omega

end Chip

/-! ## (2) Strategy model: pre-seed data is the claim only -/

run_cmd do
  let env ← getEnv
  let s := ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.DataOnlyTemplateFixedStagedTimestampStrategy
  let some (.inductInfo iv) := env.find? s | throwError m!"not a structure: {s}"
  let some ctor := iv.ctors[0]? | throwError "no ctor"
  let some cci := env.find? ctor | throwError "no ctor info"
  -- field names and whether each field's type is a Pi over the seed
  let fields := getStructureFields env s
  logInfo m!"preseed_fields: {fields}"
  unless fields == #[`claim, `afterSeed] do
    throwError m!"pre-seed structure has fields {fields}, expected [claim, afterSeed]"
  let ty : Array (Name × Bool) ← liftTermElabM <| Meta.forallTelescopeReducing cci.type fun xs _ => do
    let mut out : Array (Name × Bool) := #[]
    for x in xs do
      let d ← Meta.inferType x
      let n := (← x.fvarId!.getDecl).userName
      out := out.push (n, d.isForall)
    return out
  logInfo m!"ctor binders (name, isPi): {ty}"
  match ty.find? (·.1 == `afterSeed) with
  | some (_, true) => pure ()
  | _ => throwError "afterSeed is not a Pi over the seed"

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

-- `strategy_blind`: the production strategy type (fields and everything they unfold to) never
-- mentions the atom column or its gate; the chip trace `Qm` is not a strategy datum.
run_cmd do
  let env ← getEnv
  let stop : Name → Bool := fun n => !(`Nock).isPrefixOf n
  for s in #[``Nock.NockVMROM.Thm54.TemplateRawJointSoundness.Strategy,
      ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.DataOnlyTemplateFixedStagedTimestampStrategy] do
    let some (.inductInfo iv) := env.find? s | throwError m!"not a structure: {s}"
    let mut roots : Array Name := iv.type.getUsedConstants
    for c in iv.ctors do
      if let some cci := env.find? c then roots := roots ++ cci.type.getUsedConstants
    let r := reach env roots stop
    let probes : Array Name := #[``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.atomCol,
      ``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.haltAtomMixed,
      ``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.memorySourceTemplate]
    let hits := probes.filter r.contains
    logInfo m!"{s}: closure {r.size}; atom/gate/template names reached {hits}"
    unless hits.isEmpty do throwError m!"strategy type reaches {hits}"

#print axioms Nock.RedTeam.Batch615.all_in_round0
#print axioms Nock.RedTeam.Batch615.falseAcceptanceSet_def

end

end Nock.RedTeam.Batch615
