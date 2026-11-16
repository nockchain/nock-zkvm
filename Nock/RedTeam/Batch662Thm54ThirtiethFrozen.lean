/-
  Nock/RedTeam/Batch662Thm54ThirtiethFrozen.lean

* The live fingerprints of the three new names — `formRGuardedBad` `16140021487105387138`,
    `formRLambdaEvent` `12626547842621218738`, `fixedFormRWorkload` `1341184952722653365`
 — are recomputed here by the dumper's own procedure
    (type ++ value `Expr.hash`, `allowOpaque`) and match (`pins_match`).
  * **Negative control, signature-preserving, without touching production:** two replicas of
    `formRGuardedBad` with identical binders — `guardedA` the verbatim body, `guardedB` with the
    `else ∅` branch replaced by `else (… ).filter (fun _ => False)` (same type, same extension,
    different term). The replicated fingerprints differ (`control_fires`) while the types agree
    (`control_types_equal`), so the guard would fire on exactly that body change and on nothing
    else.

-- the paper
-/
import Lean
import Nock.NockVMROM.Thm54.FormRAxisEvent
import Nock.NockVMROM.Thm54.ProductionP8Containment

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Lean Elab Command

namespace Nock.RedTeam.Batch662

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FormRAxisEvent
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open scoped Classical

section Replicas
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] [Fintype F]

noncomputable def guardedA {T : SemanticTimestampStrategy.ExactConfigTemplate F K}
    (E : SemanticTimestampStrategy.ExactExecutionTemplate T) (i : Fin T.kMem) (E' : ℕ) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  if formRGuard (formRTemplatePolynomial E i) E' then formRGuardedAxisFailureEvent E i E' else ∅

noncomputable def guardedB {T : SemanticTimestampStrategy.ExactConfigTemplate F K}
    (E : SemanticTimestampStrategy.ExactExecutionTemplate T) (i : Fin T.kMem) (E' : ℕ) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  if formRGuard (formRTemplatePolynomial E i) E' then formRGuardedAxisFailureEvent E i E'
  else (formRGuardedAxisFailureEvent E i E').filter (fun _ => False)

/-- The perturbation is extensionally invisible (same set), so only the guard can tell. -/
theorem guardedB_eq_guardedA {T : SemanticTimestampStrategy.ExactConfigTemplate F K}
    (E : SemanticTimestampStrategy.ExactExecutionTemplate T) (i : Fin T.kMem) (E' : ℕ) :
    guardedB E i E' = guardedA E i E' := by
  unfold guardedA guardedB
  split_ifs <;> simp

end Replicas

/-- `FrozenClosure.meaningExprs` / `fingerprint`, replicated (the dumper is not a module). -/
def meaningExprs (env : Environment) (n : Name) : Array Expr :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let base := #[ci.type]
    match ci with
    | .thmInfo _ => base
    | .axiomInfo _ => base
    | _ => match ci.value? (allowOpaque := true) with
           | some v => base.push v
           | none => base

def fp (env : Environment) (n : Name) : UInt64 :=
  (meaningExprs env n).foldl (init := (17 : UInt64)) fun acc e => mixHash acc e.hash

run_cmd do
  let env ← getEnv
  let pins : Array (Name × UInt64) := #[
    (``Nock.NockVMROM.Thm54.FormRAxisEvent.formRGuardedBad, 16140021487105387138),
    (``Nock.NockVMROM.Thm54.FormRAxisEvent.formRLambdaEvent, 12626547842621218738),
    (``Nock.NockVMROM.Thm54.ProductionP8Containment.fixedFormRWorkload, 1341184952722653365)]
  for (n, h) in pins do
    let h' := fp env n
    logInfo m!"pins_match {n}: {h'} (pinned {h})"
    unless h' == h do throwError m!"live fingerprint of {n} is {h'}, pinned {h}"
  let a := fp env ``Nock.RedTeam.Batch662.guardedA
  let b := fp env ``Nock.RedTeam.Batch662.guardedB
  logInfo m!"control: guardedA {a}, guardedB {b}"
  unless a != b do throwError "control_fires failed: the perturbed body has the same fingerprint"
  -- types equal (signature-preserving)
  let some ca := env.find? ``Nock.RedTeam.Batch662.guardedA | throwError "no guardedA"
  let some cb := env.find? ``Nock.RedTeam.Batch662.guardedB | throwError "no guardedB"
  unless ca.type.hash == cb.type.hash do throwError "control_types_equal failed"
  logInfo "control_types_equal: the two replicas have the same type hash"

end Nock.RedTeam.Batch662
