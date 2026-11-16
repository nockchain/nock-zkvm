import Nock.NockVMROM.Thm54.OptimizedMemoryRAP
/-!
  Nock/RedTeam/Batch1382Thm54MemoryMaskCensus.lean

  **Memory gate census (masked gate counts and degrees by kind)** -- lane `d3d4-adopt`.
-/
open Nock Nock.Framework Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler

namespace Nock.RedTeam.Batch1382
abbrev C := CoeffExpr ℚ
abbrev M := MixedExpr ℚ

def cMask : C → Option String
  | .var .traceCur 4 => some "first"
  | .var .traceCur 5 => some "last"
  | .var .traceCur 153 => some "rootMask"
  | .var .traceCur 154 => some "dequeueMask"
  | .sub (.const _) (.var .traceCur 5) => some "notLast"
  | .sub (.const _) (.var .traceCur 4) => some "notFirst"
  | .pow (.var .traceCur 4) _ => some "first^k"
  | _ => none

def cReads : C → Bool
  | .var .traceCur i => i = 4 || i = 5 || i = 153 || i = 154
  | .var .traceNext i => i = 4 || i = 5 || i = 153 || i = 154
  | .add a b | .sub a b | .mul a b => cReads a || cReads b
  | .neg a | .pow a _ => cReads a
  | _ => false
def cNext : C → Bool
  | .var .traceNext _ => true
  | .add a b | .sub a b | .mul a b => cNext a || cNext b
  | .neg a | .pow a _ => cNext a
  | _ => false

def mMaskLeaf : M → Option String
  | .Lift c => cMask c
  | .Var .traceCur 56 => some "dequeueMirror56"
  | .Var .traceCur 47 => some "firstMirror47"
  | .Var .traceCur 48 => some "lastMirror48"
  | .Sub (.Const 1) (.Var .traceCur 48) => some "notLastMirror"
  | _ => none

def mReads : M → Bool
  | .Var .traceCur i => i = 56 || i = 47 || i = 48
  | .Var .traceNext i => i = 56 || i = 47 || i = 48
  | .Lift c => cReads c
  | .Scale c u => cReads c || mReads u
  | .Add a b | .Sub a b | .Mul a b => mReads a || mReads b
  | .Neg a | .Pow a _ => mReads a
  | _ => false
def mNext : M → Bool
  | .Var .traceNext _ => true
  | .Lift c => cNext c
  | .Scale c u => cNext c || mNext u
  | .Add a b | .Sub a b | .Mul a b => mNext a || mNext b
  | .Neg a | .Pow a _ => mNext a
  | _ => false

def mClass (t : M) : String × ℕ × ℕ × Bool × Bool :=
  match t with
  | .Scale m g => match cMask m with
      | some k => (k, t.degree, g.degree, mReads g, mNext t)
      | none => ("none", t.degree, t.degree, mReads t, mNext t)
  | .Mul a g => match mMaskLeaf a with
      | some k => (k, t.degree, g.degree, mReads g, mNext t)
      | none => match mMaskLeaf g with
        | some k => (k, t.degree, a.degree, mReads a, mNext t)
        | none => ("none", t.degree, t.degree, mReads t, mNext t)
  | _ => ("none", t.degree, t.degree, mReads t, mNext t)

def cClass (t : C) : String × ℕ × ℕ × Bool × Bool :=
  match t with
  | .mul m g => match cMask m with
      | some k => (k, t.degree, g.degree, cReads g, cNext t)
      | none => ("none", t.degree, t.degree, cReads t, cNext t)
  | _ => ("none", t.degree, t.degree, cReads t, cNext t)

def rep {α} (name : String) (f : α → String × ℕ × ℕ × Bool × Bool) (l : List α) : List String :=
  (l.zipIdx).map fun (t, i) =>
    let (k, d, d0, rm, rn) := f t
    s!"{name}[{i}] mask={k} deg={d} degNoMask={d0} innerReadsMask={rm} readsNext={rn}"
end Nock.RedTeam.Batch1382
open Nock.RedTeam.Batch1382

noncomputable def allK := (paperKGates (K := ℚ) (F := ℚ)).map (fun t => let (k,d,d0,rm,rn) := mClass t; (k,d,d0,rm,rn))
set_option maxRecDepth 100000
set_option maxHeartbeats 0
#reduce (proofs := false) (types := false) (paperBaseGates (F := ℚ)).map cClass
#reduce (proofs := false) (types := false) [haltAtomMixed (F := ℚ)].map mClass
#reduce (proofs := false) (types := false) allK
