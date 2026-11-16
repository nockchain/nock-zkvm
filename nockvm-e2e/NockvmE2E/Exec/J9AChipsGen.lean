/-
  NockvmE2E/Exec/J9AChipsGen.lean

  Generator of the J-9 A expected verifier chips (`Tr.Chip` literals) from the emitter specs.

  The J-8 literals were produced from the Lean-emitted JSON documents (`lean-emit/Nock/Emit/Json.lean`) loaded by `Tr.loadChip`
  and passed through `verifierChipT`.  There are no emitted J-9 A documents yet, so the same pipeline is replayed in Lean:
  `litChipOf id spec` = `verifierChipT` of the chip the DAG of `emitDag spec` parses to, with the per-constraint
  `kind` (transition iff the gate reads `trace_next`, else row), `round` (max column round / coin `sampled_after` read), `deg`
  (trace degree) and the `colRound` array computed by the SAME rules as `Json.lean` (`summ`, ported verbatim).
  `litChipOf` is validated against the existing J-8 literals (`chipEqB (litChipOf …) chipAtom` etc.; see `GEN-A3-REPORT.md`).
  The kernel tie `tieB spec lit` (J8ChipsK) then ties the literal's `shared`/`cons.e` to the emitter; kind/round/deg/colRound are
  NOT tied (the verifier never reads them), they are checked by the exe against the loaded document only.
-/
import NockvmE2E.Exec.J8ChipsK
import NockvmE2E.Emit.ChipsJ9A
import NockvmE2E.Emit.ComputeX9

set_option autoImplicit false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.J9AChips
open NockvmE2E.Exec NockvmE2E.Exec.Tr NockvmE2E.Exec.VC NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J8ChipsK NockvmE2E.Emit Nock.Emit
open Nock.Reified Nock.NockVMROM.Thm54.MonolithicRAP

def sampledAfterJ8 : List ℕ := [1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def coinAfter (i : ℕ) : ℕ := sampledAfterJ8.getD i 0

structure Summ where
  deg : ℕ := 0
  rnd : ℕ := 0
  next : Bool := false

def Summ.join (a b : Summ) (d : ℕ) : Summ := { deg := d, rnd := max a.rnd b.rnd, next := a.next || b.next }

def slotRound (i : ℕ) : ℕ := if i < 19 then coinAfter i else max (coinAfter 4) (coinAfter 6)

def baseRounds (s : TSpec) : List ℕ := (s.baseCols.zipIdx).flatMap fun ((n, r) : ℕ × ℕ) => List.replicate n r
def extRounds (s : TSpec) : List ℕ := (s.extCols.zipIdx).flatMap fun ((n, r) : ℕ × ℕ) => List.replicate n r

def summ (br er : List ℕ) (tab : Array Summ) : JExpr → Summ
  | .ref i => tab.getD i {}
  | .var .traceCur i => { deg := 1, rnd := br.getD i 0 }
  | .var .traceNext i => { deg := 1, rnd := br.getD i 0, next := true }
  | .var .challenge i | .extChal i | .extVar i .challenge => { rnd := slotRound i }
  | .var .publicVal _ => {}
  | .extVar _ .publicVal => {}
  | .constF _ | .constZ _ => {}
  | .extVar i .traceCur => { deg := 1, rnd := er.getD i 0 }
  | .extVar i .traceNext => { deg := 1, rnd := er.getD i 0, next := true }
  | .neg a | .extNeg a | .extLift a => summ br er tab a
  | .pow a n => let x := summ br er tab a; { x with deg := if x.deg = 0 then 0 else x.deg * n }
  | .add a b | .sub a b | .extAdd a b | .extSub a b =>
      let x := summ br er tab a; let y := summ br er tab b; x.join y (max x.deg y.deg)
  | .mul a b | .extMul a b =>
      let x := summ br er tab a; let y := summ br er tab b; x.join y (x.deg + y.deg)

/-- the loaded chip (`Tr.loadChip`) of the document of `emitDag s`, with the `Json.lean` constraint metadata -/
def loadedOf (id : String) (s : TSpec) : Option Chip := do
  let d := emitDag s
  let br := baseRounds s
  let er := extRounds s
  let tab := d.defs.foldl (fun (t : Array Summ) j => t.push (summ br er t j)) #[]
  let sh ← d.defs.mapM toEx
  let roots := d.base ++ d.ext ++ d.mixed ++ d.ext1 ++ d.ext3 ++ d.eqc
  let cs ← roots.mapM fun j => do
    let m := summ br er tab j
    let e ← toEx j
    pure ({ kind := if m.next then 1 else 0, round := m.rnd, deg := m.deg, e := e } : Con)
  pure { id := id, shared := sh.toArray, cons := cs.toArray,
         colRound := (br ++ (er.flatMap fun r => [r, r, r])).toArray, sharedK := #[], consK := #[],
         baseCols := s.baseCols.sum, width := s.baseCols.sum + 3 * s.extCols.sum }

/-- the expected VERIFIER chip -/
def litChipOf (id : String) (s : TSpec) : Option Chip := (loadedOf id s).map fun c => (verifierChipT c jDers jMeta).1

/-! ### rendering as Lean source -/

partial def renderEx : Tr.Ex → String
  | .var k i => s!"(.var {k} {i})"
  | .cF v => s!"(.cF {v})"
  | .add a b => s!"(.add {renderEx a} {renderEx b})"
  | .sub a b => s!"(.sub {renderEx a} {renderEx b})"
  | .mul a b => s!"(.mul {renderEx a} {renderEx b})"
  | .neg a => s!"(.neg {renderEx a})"
  | .pow a n => s!"(.pow {renderEx a} {n})"
  | .extVar k e => s!"(.extVar {k} {e})"
  | .chal i => s!"(.chal {i})"
  | .ref i => s!"(.ref {i})"

def renderChip (name : String) (c : Chip) : String :=
  let sh := ",\n  ".intercalate (c.shared.toList.map renderEx)
  let cs := ",\n  ".intercalate (c.cons.toList.map fun k => s!"⟨{k.kind}, {k.round}, {k.deg}, {renderEx k.e}⟩")
  s!"def {name} : Chip where\n  id := \"{c.id}\"\n  shared := #[{sh}]\n  cons := #[{cs}]\n  colRound := {repr c.colRound}\n  sharedK := #[]\n  consK := #[]\n  baseCols := {c.baseCols}\n  width := {c.width}\n"

def genChip (id name : String) (s : TSpec) : String :=
  match litChipOf id s with
  | some c => renderChip name c
  | none => "-- gen failed"

/-- validation against the existing J-8 literals (executed `#eval`, true = the replayed pipeline reproduces the literal, incl. kind/round/deg/colRound) -/
def valid (id : String) (s : TSpec) (lit : Chip) : Bool := match litChipOf id s with | some c => chipEqB c lit | none => false
#eval (valid "atomChipHQL" atomSpec chipAtom, valid "jetChipJ8" jetSpec chipJet, valid "cellChipHQKW" cellKWSpec chipCell,
  valid "walkChipJ8" (walkJ8SpecAt 1) chipWalkJ8_1, valid "computeChipVCLHX" computeSpec chipCompute)

end NockvmE2E.Exec.J9AChips
