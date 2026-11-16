/-
  Nock/RedTeam/Batch616Thm54PreseedAuditFingerprint.lean

  Notes only; not a pass.  Cause established here.

  A user's value mentions `haltSel` as a constant application
  `@haltSel F …`, whose hash does not change when `haltSel`'s BODY changes.  The mutation used at the merge
  was NOT body-only: `.const 0 : CoeffExpr F` needs `(0 : F)`, i.e. an `OfNat F 0` instance, so
  Lean's section-variable inclusion adds the `[Field F]` binder to `haltSel`'s SIGNATURE (the
  live `haltSel` has none: `haltSel_type` below — `fun {F} => bcur 1` needs no instance).  Every
  user's value then becomes `@haltSel F inst` instead of `@haltSel F`, so the users' value hashes
  move too: `haltAtomMixed` (direct), `haltAtomGateCoord` and `mixedTransitionGates` (through
  `haltAtomMixed`), exactly the four that fired.  The guard hashed what it should — a signature
  change in a frontier definition IS a change of meaning of its users' terms — and nothing
  unintended.  `Expr.hash : Expr → UInt64` takes no environment, so a referent's BODY cannot
  reach a user's hash; only its name, levels and the arguments applied to it can — and the
  mutation changed the arguments (one more, the instance).

  Replicas: `selA := bcur 1` (no `[Field F]`), `selB :=.add (bcur 1) (.const 0)` (gains
  `[Field F]`); `gateX := Scale selX (…)`.
-/
import Lean
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis

set_option autoImplicit false
open Lean Elab Command

namespace Nock.RedTeam.Batch616

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis

section Replicas
variable {F : Type} [Field F]

def selA : CoeffExpr F := bcur 1
def selB : CoeffExpr F := .add (bcur 1) (.const 0)

def gateA : MixedExpr F := .Scale selA (.Sub (.Var .traceCur 2) (.Lift (bcur atomCol)))
def gateB : MixedExpr F := .Scale selB (.Sub (.Var .traceCur 2) (.Lift (bcur atomCol)))

end Replicas

/-- The live selector's signature has no instance binder. -/
theorem haltSel_type : (@haltSel : ∀ {F : Type}, CoeffExpr F) = @haltSel := rfl

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

def binderCount (env : Environment) (n : Name) : ℕ :=
  match env.find? n with
  | some ci => ci.type.getForallBinderNames.length
  | none => 0

/-- The largest number of arguments `c` is applied to anywhere inside the value of `n`. -/
partial def arityWalk (c : Name) : Expr → ℕ → ℕ
  | e@(.app ..), best =>
      let f := e.getAppFn
      let best := if f.isConstOf c then max best e.getAppNumArgs else best
      e.getAppArgs.foldl (fun b a => arityWalk c a b) (arityWalk c f best)
  | .lam _ d b _, best => arityWalk c b (arityWalk c d best)
  | .forallE _ d b _, best => arityWalk c b (arityWalk c d best)
  | .letE _ t v b _, best => arityWalk c b (arityWalk c v (arityWalk c t best))
  | .mdata _ b, best => arityWalk c b best
  | .proj _ _ b, best => arityWalk c b best
  | _, best => best

def maxArity (env : Environment) (n c : Name) : ℕ :=
  match env.find? n with
  | some ci =>
      match ci.value? (allowOpaque := true) with
      | some v => arityWalk c v 0
      | none => 0
  | none => 0

run_cmd do
  let env ← getEnv
  let live := ``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.haltSel
  let a := ``Nock.RedTeam.Batch616.selA
  let b := ``Nock.RedTeam.Batch616.selB
  logInfo m!"binders: live haltSel {binderCount env live}, selA {binderCount env a}, \
    selB {binderCount env b}"
  unless binderCount env live == 1 ∧ binderCount env a == 1 do
    throwError "expected a single implicit binder on haltSel and selA"
  unless binderCount env b == 2 do throwError "expected selB to gain [Field F]"
  logInfo m!"fp live haltSel {fp env live}; fp selA {fp env a}; fp selB {fp env b}"
  unless fp env live == fp env a do throwError "selA does not replicate the live haltSel fingerprint"
  let gA := ``Nock.RedTeam.Batch616.gateA
  let gB := ``Nock.RedTeam.Batch616.gateB
  let arA := maxArity env gA a
  let arB := maxArity env gB b
  logInfo m!"arity of the selector inside the gate value: gateA/selA {arA}, gateB/selB {arB}"
  unless arA == 1 ∧ arB == 2 do throwError "expected selA applied to 1 arg, selB to 2"
  let ga := fp env gA
  let gb := fp env gB
  logInfo m!"fp gateA {ga}; gateB {gb}"
  unless ga != gb do throwError "gateB should differ from gateA (signature change propagates)"
  -- the same mechanism, one ring further: the live users of haltSel apply it to exactly one arg
  for u in [``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.haltAtomMixed] do
    logInfo m!"{u}: haltSel arity {maxArity env u live}"
    unless maxArity env u live == 1 do throwError m!"{u} applies haltSel to ≠ 1 args"

end Nock.RedTeam.Batch616
