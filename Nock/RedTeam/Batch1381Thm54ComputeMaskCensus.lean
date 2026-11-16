import Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
/-!
  Nock/RedTeam/Batch1381Thm54ComputeMaskCensus.lean

  **Compute gate census (masked gate counts and degrees by kind)** -- lane `d3d4-adopt`.
-/
open Nock Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.CoordinateCompiler

namespace Nock.RedTeam.Batch1381
abbrev T := CorrectedFinalTypedExpr

def maskOf : T → Option String
  | .baseCur i => if i.val = 11 then some "first" else if i.val = 12 then some "last" else none
  | .sub (.const 1) (.baseCur i) => if i.val = 12 then some "notLast" else if i.val = 11 then some "notFirst" else none
  | _ => none

partial def readsMask : T → Bool
  | .baseCur i => i.val = 11 || i.val = 12
  | .add a b | .sub a b | .mul a b => readsMask a || readsMask b
  | .neg a | .pow a _ => readsMask a
  | _ => false

partial def readsNext : T → Bool
  | .baseNext _ | .extNext _ => true
  | .add a b | .sub a b | .mul a b => readsNext a || readsNext b
  | .neg a | .pow a _ => readsNext a
  | _ => false

def classify (t : T) : String × ℕ × ℕ × Bool × Bool :=
  match t with
  | .mul m g => match maskOf m with
      | some k => (k, t.degree, g.degree, readsMask g, readsNext t)
      | none => match maskOf g with
        | some k => (k, t.degree, m.degree, readsMask m, readsNext t)
        | none => ("none", t.degree, t.degree, readsMask t, readsNext t)
  | _ => ("none", t.degree, t.degree, readsMask t, readsNext t)

def core : List T := (List.range 82).map fun i =>
  if h : i < 82 then
    let g := correctedFinalExtGate ⟨i, h⟩
    if i = 74 then .mul (.sub (.const 1) (.baseCur 12)) (.extCur 58)
    else if i = 75 then .mul (.sub (.const 1) (.baseCur 12)) (.extCur 59)
    else if i = 81 then accAfterChain
    else if i = 72 ∨ i = 73 then .mul (.sub (.const 1) (.baseCur 12)) g
    else g
  else .const 0

def aux : List T := [correctedFinalExtGate ⟨74, by omega⟩, correctedFinalExtGate ⟨75, by omega⟩, correctedAccAfterStep]

def report (name : String) (l : List T) : List String :=
  (l.zipIdx).map fun (t, i) =>
    let (k, d, d0, rm, rn) := classify t
    s!"{name}[{i}] mask={k} deg={d} degNoMask={d0} innerReadsMask={rm} readsNext={rn}"
end Nock.RedTeam.Batch1381
open Nock.RedTeam.Batch1381
#eval (report "core" core ++ report "aux" aux ++ report "ep2" correctedEndpoint2 ++ report "ep4" correctedEndpoint4 ++ report "lam" formRLamPins).foldl (fun a b => a ++ "\n" ++ b) ""
