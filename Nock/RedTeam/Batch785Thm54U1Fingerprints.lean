/-
  Nock/RedTeam/Batch785Thm54U1Fingerprints.lean

  * **U1 fires:** `Batch782.topPinU1` (signature-preserving) hashes differently.

  The ring-two read-set facts
  are unchanged; the names they list are on the watchlist since this move.
-/
import Lean
import Nock.RedTeam.Batch782Thm54U1Sound

set_option autoImplicit false

namespace Nock.RedTeam.Batch785

open Lean
open Nock.Reified
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.CoordinateCompiler

variable {F : Type*} [Field F]

noncomputable def topPinVerbatim : CoeffExpr F :=
  .mul colTop (.sub colTop (.const 1))


def ctorTypes (env : Environment) (ci : ConstantInfo) : Array Lean.Expr :=
  match ci with
  | .inductInfo iv =>
      iv.ctors.foldl (init := #[]) fun acc c =>
        match env.find? c with
        | some cci => acc.push cci.type
        | none => acc
  | _ => #[]

def meaningExprs (env : Environment) (n : Name) : Array Lean.Expr :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let base := #[ci.type] ++ ctorTypes env ci
    match ci with
    | .thmInfo _ => base
    | .axiomInfo _ => base
    | _ => match ci.value? (allowOpaque := true) with
           | some v => base.push v
           | none => base

def fpHash (env : Environment) (n : Name) : UInt64 :=
  (meaningExprs env n).foldl (init := (17 : UInt64)) fun acc e => mixHash acc e.hash

def usesConst (env : Environment) (n c : Name) : Bool :=
  match env.find? n with
  | some ci => match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstants.contains c
      | none => false
  | none => false

run_cmd do
  let env ← getEnv
  let ns := `Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
  let prod := fpHash env (ns ++ `topPin)
  let verb := fpHash env `Nock.RedTeam.Batch785.topPinVerbatim
  let u1 := fpHash env `Nock.RedTeam.Batch782.topPinU1
  logInfo m!"topPin (deployed) {prod}; pre-repair verbatim replica {verb}; U1 replica {u1}"
  unless prod == 17115654872064556545 do throwError "deployed topPin moved off its re-pin"
  unless verb == 7881170531472581138 do
    throwError "pre-repair verbatim replica does not reproduce the old pin"
  unless u1 == prod do throwError "deployed topPin is not the U1 body"
  if verb == prod then throwError "the U1 move does not fire"
  -- the ring-two shape of the comparison / csum repairs
  let checks : List (Name × Name × Bool) := [
    (ns ++ `comparisonGate, ns ++ `comparisonTerms, true),
    (ns ++ `comparisonGate, ns ++ `linCol, false),
    (ns ++ `comparisonGate, ns ++ `pBit, false),
    (ns ++ `helperPins, ns ++ `helperPinAt, true),
    (ns ++ `helperPins, ns ++ `linCol, false),
    (ns ++ `axisEquation, ns ++ `csum, true),
    (ns ++ `axisEquation, ns ++ `csumAcc, false),
    (ns ++ `booleanGates, ns ++ `bbool, true),
    (ns ++ `topPin, ns ++ `colTop, true),
    (ns ++ `rangeGate, ns ++ `rangeTerms, true),
    (ns ++ `rangeGate, ns ++ `lm, false)]
  for (n, c, expect) in checks do
    unless usesConst env n c == expect do
      throwError m!"read-set expectation failed: {n} uses {c} = {!expect}"
  logInfo m!"ring-two shape confirmed: comparisonGate/helperPins/axisEquation/rangeGate name \
    comparisonTerms/helperPinAt/csum/rangeTerms, not linCol/pBit/csumAcc/lm"

end Nock.RedTeam.Batch785
