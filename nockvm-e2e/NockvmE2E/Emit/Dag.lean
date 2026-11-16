/-
  NockvmE2E/Emit/Dag.lean

  **Shared-subterm (DAG) emission.**  The J-8 gate trees are exponentially redundant as trees
  (`jetChipJ8`: 333 k nodes for 26 gates, because `QE.mul` duplicates its operands), but are small DAGs.  A
  document therefore carries, per chip, a `shared : [Expr]` table; a composite node is a table entry whose
  children are leaves or `{"ref": i}` to EARLIER entries; a gate is a leaf or a `ref`.  Every JSON subtree
  then has depth ≤ 3.

  `emitDag` interns nodes with a digest map and a `BEq` check, so correctness does NOT depend on the map; it
  uses only `Nat` / `List` / `RBMap` (kernel-reducible, no `HashMap`/`mixHash`).  The kernel-checked
  statement per chip (`Chips.lean`) is `decodeDag (emitDag spec) = some (specGates spec)`, by `decide +kernel`:
  the table is decoded entry by entry (tree values rebuilt) and compared with the chip's gate lists in the
  `norm` normal form (`Schema.lean`; `eval_norm` shows `norm` preserves values).
-/
import NockvmE2E.Emit.Schema
import Lean.Data.RBMap

set_option autoImplicit false

namespace Nock.Emit

open Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler

deriving instance DecidableEq for CoeffExpr
deriving instance DecidableEq for MixedExpr

/-- A chip's gate lists, `𝕂`-valued buckets already read as mixed expressions. -/
structure TSpec where
  rounds : ℕ
  baseCols : List ℕ
  extCols : List ℕ
  base : List (CoeffExpr Gl)
  ext : List (MixedExpr Gl)
  mixed : List (MixedExpr Gl)
  ext1 : List (MixedExpr Gl)
  ext3 : List (MixedExpr Gl)
  eqc : List (CoeffExpr Gl)

def TSpec.ofTemplate (T : ChipTemplate Gl) : TSpec where
  rounds := T.rounds
  baseCols := List.ofFn T.baseColsOf
  extCols := List.ofFn T.extColsOf
  base := T.baseTransition
  ext := T.extTransition.map MixedExpr.ofExpr
  mixed := T.mixedTransition
  ext1 := T.extDeg1.map MixedExpr.ofExpr
  ext3 := T.extDeg3.map MixedExpr.ofExpr
  eqc := T.equalityChecks

structure DGatesDec where
  base : List (CoeffExpr Gl)
  ext : List (MixedExpr Gl)
  mixed : List (MixedExpr Gl)
  ext1 : List (MixedExpr Gl)
  ext3 : List (MixedExpr Gl)
  eqc : List (CoeffExpr Gl)
deriving DecidableEq

def TSpec.gates (s : TSpec) : DGatesDec where
  base := s.base
  ext := s.ext.map norm
  mixed := s.mixed.map norm
  ext1 := s.ext1.map norm
  ext3 := s.ext3.map norm
  eqc := s.eqc

/-! ## Interning -/

structure Tab where
  defsRev : List JExpr := []
  size : ℕ := 0
  map : Lean.RBMap ℕ (List (JExpr × ℕ)) compare := {}

/-- A digest of a SHALLOW node (children are leaves or refs); any value is sound, collisions only cost a scan. -/
def digest : JExpr → ℕ
  | .var k i => 3 + 7 * i + (match k with | .traceCur => 0 | .traceNext => 1 | .challenge => 2 | .publicVal => 5)
  | .constF n => 11 + 13 * n
  | .constZ z => 17 + 19 * z.natAbs
  | .add a b => 23 + 29 * digest a + 31 * digest b
  | .sub a b => 37 + 41 * digest a + 43 * digest b
  | .mul a b => 47 + 53 * digest a + 59 * digest b
  | .neg a => 61 + 67 * digest a
  | .pow a n => 71 + 73 * digest a + 79 * n
  | .extVar i k => 83 + 89 * i + (match k with | .traceCur => 0 | .traceNext => 1 | .challenge => 2 | .publicVal => 5)
  | .extChal i => 97 + 101 * i
  | .extLift a => 103 + 107 * digest a
  | .extAdd a b => 109 + 113 * digest a + 127 * digest b
  | .extSub a b => 131 + 137 * digest a + 139 * digest b
  | .extMul a b => 149 + 151 * digest a + 157 * digest b
  | .extNeg a => 163 + 167 * digest a
  | .ref i => 173 + 179 * i

/-- Intern a composite node: returns `ref i`. -/
def intern (j : JExpr) : StateM Tab JExpr := fun t =>
  let d := digest j % 1000000007
  let cands := (t.map.find? d).getD []
  match cands.find? (fun c => c.1 == j) with
  | some c => (.ref c.2, t)
  | none => (.ref t.size, { defsRev := j :: t.defsRev, size := t.size + 1, map := t.map.insert d ((j, t.size) :: cands) })

def dagBase : CoeffExpr Gl → StateM Tab JExpr
  | .const c => pure (.constF c.val)
  | .var k i => pure (.var k i)
  | .add a b => do let x ← dagBase a; let y ← dagBase b; intern (.add x y)
  | .sub a b => do let x ← dagBase a; let y ← dagBase b; intern (.sub x y)
  | .mul a b => do let x ← dagBase a; let y ← dagBase b; intern (.mul x y)
  | .neg a => do let x ← dagBase a; intern (.neg x)
  | .pow a n => do let x ← dagBase a; intern (.pow x n)

def dagPow (x : JExpr) : ℕ → StateM Tab JExpr
  | 0 => intern (.extLift (.constZ 1))
  | n + 1 => do let p ← dagPow x n; intern (.extMul p x)

def dagMixed : MixedExpr Gl → StateM Tab JExpr
  | .Var .traceCur i => pure (.extVar i .traceCur)
  | .Var .traceNext i => pure (.extVar i .traceNext)
  | .Var .challenge i => pure (.extChal i)
  | .Var .publicVal i => pure (.extVar i .publicVal)
  | .Lift g => do let x ← dagBase g; intern (.extLift x)
  | .Scale g u => do
      let x ← dagBase g; let l ← intern (.extLift x); let y ← dagMixed u; intern (.extMul l y)
  | .Const c => intern (.extLift (.constZ c))
  | .Add x y => do let a ← dagMixed x; let b ← dagMixed y; intern (.extAdd a b)
  | .Sub x y => do let a ← dagMixed x; let b ← dagMixed y; intern (.extSub a b)
  | .Neg x => do let a ← dagMixed x; intern (.extNeg a)
  | .Mul x y => do let a ← dagMixed x; let b ← dagMixed y; intern (.extMul a b)
  | .Pow x n => do let a ← dagMixed x; dagPow a n

/-- The emitted DAG for a chip: the shared table (in order) and the gate lists as leaves / refs. -/
structure DagGates where
  defs : List JExpr
  base : List JExpr
  ext : List JExpr
  mixed : List JExpr
  ext1 : List JExpr
  ext3 : List JExpr
  eqc : List JExpr

def emitDag (s : TSpec) : DagGates :=
  let m : StateM Tab (List JExpr × List JExpr × List JExpr × List JExpr × List JExpr × List JExpr) := do
    let a ← s.base.mapM dagBase
    let b ← s.ext.mapM dagMixed
    let c ← s.mixed.mapM dagMixed
    let d ← s.ext1.mapM dagMixed
    let e ← s.ext3.mapM dagMixed
    let f ← s.eqc.mapM dagBase
    pure (a, b, c, d, e, f)
  let (r, t) := m.run {}
  { defs := t.defsRev.reverse, base := r.1, ext := r.2.1, mixed := r.2.2.1, ext1 := r.2.2.2.1,
    ext3 := r.2.2.2.2.1, eqc := r.2.2.2.2.2 }

/-! ## Decoding -/

inductive Val where
  | b (c : CoeffExpr Gl)
  | m (e : MixedExpr Gl)

abbrev VTab := Lean.RBMap ℕ Val compare

def decStep (tab : VTab) : JExpr → Option Val
  | .ref i => tab.find? i
  | .var k i => some (.b (.var k i))
  | .constF n => some (.b (.const (n : Gl)))
  | .add a b => match decStep tab a, decStep tab b with
      | some (.b x), some (.b y) => some (.b (.add x y)) | _, _ => none
  | .sub a b => match decStep tab a, decStep tab b with
      | some (.b x), some (.b y) => some (.b (.sub x y)) | _, _ => none
  | .mul a b => match decStep tab a, decStep tab b with
      | some (.b x), some (.b y) => some (.b (.mul x y)) | _, _ => none
  | .neg a => match decStep tab a with | some (.b x) => some (.b (.neg x)) | _ => none
  | .pow a n => match decStep tab a with | some (.b x) => some (.b (.pow x n)) | _ => none
  | .extVar i k => some (.m (.Var k i))
  | .extChal i => some (.m (.Var .challenge i))
  | .extLift (.constZ c) => some (.m (.Const c))
  | .extLift a => match decStep tab a with | some (.b g) => some (.m (.Lift g)) | _ => none
  | .extAdd a b => match decStep tab a, decStep tab b with
      | some (.m x), some (.m y) => some (.m (.Add x y)) | _, _ => none
  | .extSub a b => match decStep tab a, decStep tab b with
      | some (.m x), some (.m y) => some (.m (.Sub x y)) | _, _ => none
  | .extMul a b => match decStep tab a, decStep tab b with
      | some (.m x), some (.m y) => some (.m (.Mul x y)) | _, _ => none
  | .extNeg a => match decStep tab a with | some (.m x) => some (.m (.Neg x)) | _ => none
  | _ => none

/-- Decode the shared table in order (entry `i` may only use entries `< i`; the table is a `List`, newest last). -/
def decTable (defs : List JExpr) : Option VTab :=
  (defs.foldlM (fun (st : VTab × ℕ) j => (decStep st.1 j).map fun v => (st.1.insert st.2 v, st.2 + 1)) ({}, 0)).map (·.1)

def decB (tab : VTab) (j : JExpr) : Option (CoeffExpr Gl) :=
  match decStep tab j with | some (.b g) => some g | _ => none
def decM (tab : VTab) (j : JExpr) : Option (MixedExpr Gl) :=
  match decStep tab j with | some (.m g) => some g | _ => none

def decodeDag (d : DagGates) : Option DGatesDec :=
  match decTable d.defs with
  | none => none
  | some tab =>
    match d.base.mapM (decB tab), d.ext.mapM (decM tab), d.mixed.mapM (decM tab),
          d.ext1.mapM (decM tab), d.ext3.mapM (decM tab), d.eqc.mapM (decB tab) with
    | some a, some b, some c, some e, some f, some g => some ⟨a, b, c, e, f, g⟩
    | _, _, _, _, _, _ => none

/-! ## Leaf renaming (chip-family leaf conventions → document conventions) -/

/-- Rename the `𝕂`-leaves of a mixed expression: challenge slots by `fc`, trace-column roles by `fe`, publics by `fp`. -/
def renameM (fc fe fp : ℕ → ℕ) : MixedExpr Gl → MixedExpr Gl
  | .Var .challenge i => .Var .challenge (fc i)
  | .Var .publicVal i => .Var .publicVal (fp i)
  | .Var .traceCur i => .Var .traceCur (fe i)
  | .Var .traceNext i => .Var .traceNext (fe i)
  | .Lift g => .Lift g
  | .Scale g u => .Scale g (renameM fc fe fp u)
  | .Const c => .Const c
  | .Add x y => .Add (renameM fc fe fp x) (renameM fc fe fp y)
  | .Sub x y => .Sub (renameM fc fe fp x) (renameM fc fe fp y)
  | .Neg x => .Neg (renameM fc fe fp x)
  | .Mul x y => .Mul (renameM fc fe fp x) (renameM fc fe fp y)
  | .Pow x n => .Pow (renameM fc fe fp x) n

def TSpec.rename (fc fe fp : ℕ → ℕ) (s : TSpec) : TSpec :=
  { s with ext := s.ext.map (renameM fc fe fp), mixed := s.mixed.map (renameM fc fe fp),
           ext1 := s.ext1.map (renameM fc fe fp), ext3 := s.ext3.map (renameM fc fe fp) }

end Nock.Emit
