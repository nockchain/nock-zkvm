/-
  Nock/RedTeam/Batch736Thm54DecodedLambdaNegativeControls.lean

  **The thirty-second move's negative controls by replica (lane `lambda-consumer-32nd`).**
  * (i) the guard `∃ k ≤ E'` → `∃ k ≤ E' + 1` in `decodedRootBad`: `6988877621924139331 →
    10455602239368963338`.
  * (ii) the exponent locator `e ≤ S + arity` → `e < S + arity` in `locateExp`:
    `3183022933929141274 → 623535235917067256`.
-/
import Nock.NockVMROM.Thm54.DecodedLambdaEvent
set_option autoImplicit false
namespace Nock.RedTeam.Batch736
open scoped Classical BigOperators Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.FormRAxisEvent
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.RedTeam.Batch575
open Nock.NockVMROM.Thm54.DecodedLambdaEvent (computePrefix computeArity decodedRootPoly decodedEnvelopeDeg)
open Polynomial
noncomputable section
section Compute
variable {K : Type} [Field K] {N : ℕ}
def locateExpA (envsC : Fin N → Env K) (e : ℕ) : Option (Fin N × ℕ) :=
  ((List.finRange N).find? fun i =>
      decide (computePrefix envsC i < e ∧ e ≤ computePrefix envsC i + computeArity (envsC i))).map
    fun i => (i, e - computePrefix envsC i - 1)
def locateExpB (envsC : Fin N → Env K) (e : ℕ) : Option (Fin N × ℕ) :=
  ((List.finRange N).find? fun i =>
      decide (computePrefix envsC i < e ∧ e < computePrefix envsC i + computeArity (envsC i))).map
    fun i => (i, e - computePrefix envsC i - 1)
end Compute
section Event
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
variable [Fintype F] [DecidableEq F] {N M : ℕ}
def decodedRootBadA (envsC : Fin N → Env K) (envsK : Fin M → Env K) (envsF : Fin M → Env F)
    (kroots r : ℕ) : Finset (K × K) :=
  if formRGuard (decodedRootPoly envsC envsK envsF kroots r) (decodedEnvelopeDeg N) then
    formRRootBad (decodedRootPoly envsC envsK envsF kroots r) (decodedEnvelopeDeg N)
  else ∅
def decodedRootBadB (envsC : Fin N → Env K) (envsK : Fin M → Env K) (envsF : Fin M → Env F)
    (kroots r : ℕ) : Finset (K × K) :=
  if formRGuard (decodedRootPoly envsC envsK envsF kroots r) (decodedEnvelopeDeg N + 1) then
    formRRootBad (decodedRootPoly envsC envsK envsF kroots r) (decodedEnvelopeDeg N)
  else ∅
end Event
end
end Nock.RedTeam.Batch736

def fpOf (env : Lean.Environment) (n : Lean.Name) : String :=
  match env.find? n with
  | none => "missing"
  | some ci =>
    let es : Array Lean.Expr := match ci.value? (allowOpaque := true) with
      | some v => #[ci.type, v]
      | none => #[ci.type]
    toString (es.foldl (init := (17 : UInt64)) fun acc e => mixHash acc e.hash)

open Lean in
run_cmd do
  let env ← getEnv
  let D := `Nock.NockVMROM.Thm54.DecodedLambdaEvent
  let R := `Nock.RedTeam.Batch736
  let h (n : Name) : String := fpOf env n
  for (live, a, b) in [(D ++ `locateExp, R ++ `locateExpA, R ++ `locateExpB),
                       (D ++ `decodedRootBad, R ++ `decodedRootBadA, R ++ `decodedRootBadB)] do
    logInfo m!"{live}: live {h live}; verbatim replica {h a} (reproduces: {h live == h a}); perturbed {h b} (fires: {h b != h live})"
    unless h live == h a ∧ h b != h live do throwError "control failed"
  unless h (D ++ `decodedRootBad) == "6988877621924139331" ∧ h (D ++ `locateExp) == "3183022933929141274" ∧
      h (D ++ `slotCert) == "13282248033372792418" do
    throwError "live fingerprints differ from the 32nd re-pin"
