/-
  Nock/NockVMROM/Thm54/VclL/Handle/ChipH.lean

  **Layout** (MEASURED `widthH = 70` by `rfl`; VERDICT §3 target ≈ 76 hosted):

  | cols | group | note |
  |---|---|---|
  | `0..10`  | op one-hot (`OP_0 … OP_9`, `cons` at 10) | B0 |
  | `11, 12` | `isFirst`, `isLast` (verifier preprocessing) | B0 |
  | `13`     | `z1` (axis-1 local read on OP0 / OP9; local first difference on OP5) | B0 |
  | `14..18` | atom value `v`, output bit `β`, second atom value `v2`, OP5 inverse `w`, OP5 read-pair flag `pr` | B0, atom-only |
  | `19..42` | 12 handles `(kind, val)`: `s f e sf1_e sf2_e`, decode `f_h f_t f_th f_tt f_tth f_ttt`, hosted `m` | B0 |
  | `43..51` | 3 slot inverses (`𝕂`, 3 limbs each) | B2 |
  | `52..57` | 2 accumulators (export / path, `𝕂`) | B2 |
  | `58..69` | compute walk `ln, count, acc, walk_inv` (`𝕂`) | B2 |

  The instrument `serialFreeB` / `keyOK` checks
  this over the whole gate list, with positive controls that it flags forbidden shapes.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerLookup

namespace Nock.NockVMROM.Thm54
namespace VclL.Handle
namespace ChipH

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.Framework

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. Layout -/

/-- Op selector column: `OP_j` at `j` (`j ≤ 9`), `cons` at `10`. -/
def consCol : ℕ := 10
def firstCol : ℕ := 11
def lastCol : ℕ := 12
def z1C : ℕ := 13
def vC : ℕ := 14
def betaC : ℕ := 15
def v2C : ℕ := 16
def wC : ℕ := 17
def prC : ℕ := 18

/-- A handle: its kind-bit column and its value column (atom value or round-0 serial). -/
structure Hd where
  k : ℕ
  v : ℕ
deriving DecidableEq, Repr

def hd (j : ℕ) : Hd := ⟨19 + 2 * j, 20 + 2 * j⟩

def hS : Hd := hd 0
def hF : Hd := hd 1
def hE : Hd := hd 2
def hSf1 : Hd := hd 3
def hSf2 : Hd := hd 4
def hFh : Hd := hd 5
def hFt : Hd := hd 6
def hFth : Hd := hd 7
def hFtt : Hd := hd 8
def hFtth : Hd := hd 9
def hFttt : Hd := hd 10
/-- The hosted multipurpose handle: OP6 branch formula, OP8 subject `[sf2_e s]`, OP9 arm,
OP5 first-difference axis (as an atom handle). -/
def hM : Hd := hd 11

def allHandles : List Hd := (List.range 12).map hd

/-- **The serial-capable columns**: every handle value column (an atom value when the kind bit is
`0`, a round-0 serial when it is `1`). -/
def serialCols : List ℕ := allHandles.map Hd.v
def kindCols : List ℕ := allHandles.map Hd.k

def round0W : ℕ := 43

/-- Round-2 (`𝕂`, 3 limbs each) column bases. -/
def inv0 : ℕ := 43
def inv1 : ℕ := 46
def inv2 : ℕ := 49
def accX : ℕ := 52
def accP : ℕ := 55
def wLn : ℕ := 58
def wCnt : ℕ := 61
def wAcc : ℕ := 64
def wInv : ℕ := 67

/-- **The handle chip's width.** -/
def widthH : ℕ := 70

/-- **Width breakdown** (VERDICT §3 groups): control 14, atom/flags 5, handles 12 × 2,
lookup inverses 3 × 3, accumulators 2 × 3, walk 4 × 3. -/
theorem widthH_eq : widthH = 14 + 5 + 12 * 2 + 3 * 3 + 2 * 3 + 4 * 3 := rfl

theorem widthH_le_cap : widthH ≤ 91 := by decide

/-- The layout is a partition of `0.. 70`: handles tile `19.. 42`, round-2 blocks are adjacent. -/
theorem layout_tiles :
    (allHandles.map Hd.k ++ allHandles.map Hd.v).length = 24 ∧
    hd 0 = ⟨19, 20⟩ ∧ hd 11 = ⟨41, 42⟩ ∧ 42 + 1 = round0W ∧ round0W = inv0 ∧
    inv0 + 3 = inv1 ∧ inv1 + 3 = inv2 ∧ inv2 + 3 = accX ∧ accX + 3 = accP ∧ accP + 3 = wLn ∧
    wLn + 3 = wCnt ∧ wCnt + 3 = wAcc ∧ wAcc + 3 = wInv ∧ wInv + 3 = widthH ∧
    (List.range 43).Nodup ∧
    (allHandles.map Hd.k ++ allHandles.map Hd.v).Nodup ∧
    ∀ c ∈ allHandles.map Hd.k ++ allHandles.map Hd.v, 19 ≤ c ∧ c < 43 := by
  decide

/-- Coin / public slots of the twin (`𝕂` bases, limbs `i.. i+2`; base-field claim publics `0..5`). -/
def chalGammaL : ℕ := 0
def chalRhoL : ℕ := 3
def chalAlphaW : ℕ := 6
def chalGammaW : ℕ := 9
def pubIC : ℕ := 6
def pubSeed : ℕ := 9
def pubOut : ℕ := 12
def pubRhoX : ℕ := 15
def pubRhoP : ℕ := 18

/-! ## 2. Base-field building blocks -/

section Base
variable {F : Type} [Field F]

def cc (i : ℕ) : CoeffExpr F := .var .traceCur i
def notC (i : ℕ) : CoeffExpr F := .sub (.const 1) (cc i)
def selS (l : List ℕ) : CoeffExpr F := CoeffExpr.sumList l cc
def prodL (l : List (CoeffExpr F)) : CoeffExpr F := l.foldr .mul (.const 1)

/-- An equality-test operand: a column, a constant, or a public. -/
inductive Opnd (F : Type) where
  | col (i : ℕ)
  | cst (x : F)
  | pub (i : ℕ)

def Opnd.expr : Opnd F → CoeffExpr F
  | .col i => cc i
  | .cst x => .const x
  | .pub i => .var .publicVal i

/-- **An equality test** `σ · (x − y)`. -/
structure EqG (F : Type) where
  σ : CoeffExpr F
  x : ℕ
  y : Opnd F

def EqG.gate (g : EqG F) : CoeffExpr F := .mul g.σ (.sub (cc g.x) g.y.expr)

/-- Handle equality under `σ`: kind and value. -/
def heq (σ : CoeffExpr F) (a b : Hd) : List (EqG F) := [⟨σ, a.k, .col b.k⟩, ⟨σ, a.v, .col b.v⟩]

def hpub (σ : CoeffExpr F) (a : Hd) (pk pv : ℕ) : List (EqG F) := [⟨σ, a.k, .pub pk⟩, ⟨σ, a.v, .pub pv⟩]

end Base

/-! ## 3. The base gates: `V_comp` on handles -/

section Gates
variable {F : Type} [Field F]

/-- `OP_j` selectors that decode `f_t` (L2): `2, 5, 6, 7, 8, 9`. -/
def l2States : List ℕ := [2, 5, 6, 7, 8, 9]

/-- **The read-pair flag gate** `pr − s5 · β · (1 − z1)`: `pr` is `1` exactly on OP5 "≠" rows whose
first difference is read through the walk (so `pr = 0` off `s5`). -/
def prGate : CoeffExpr F := .sub (cc prC) (prodL [cc 5, cc betaC, notC z1C])

/-- **The OP5 "≠" witness gate** `s5·β·((x1.k − x2.k)² + (v − v2)·w − 1)`: kinds differ, or both atoms
with an invertible ATOM-VALUE difference (`v`, `v2` are atom-only columns). -/
def neGate : CoeffExpr F :=
  .mul (prodL [cc 5, cc betaC])
    (.sub (.add (.pow (.sub (cc hFtth.k) (cc hFttt.k)) 2)
      (.mul (.sub (cc vC) (cc v2C)) (cc wC))) (.const 1))

/-- **Serial-free arithmetic gates** (selectors, kind bits, atom-only columns, masks). -/
def arithGates : List (CoeffExpr F) :=
  -- one-hot selectors, `z1`, `β` booleanity
  ((List.range 11).map fun j => .mul (cc j) (.sub (cc j) (.const 1))) ++
  [.sub (selS (List.range 11)) (.const 1),
   .mul (cc z1C) (.sub (cc z1C) (.const 1)),
   .mul (cc betaC) (.sub (cc betaC) (.const 1))] ++
  -- booleanity on every kind bit
  (allHandles.map fun h => .mul (cc h.k) (.sub (cc h.k) (.const 1))) ++
  -- SV: `cons` iff the head is a cell; every formula is a cell (L1)
  [.sub (cc consCol) (cc hFh.k),
   .sub (cc hF.k) (.const 1),
   -- L2 / L3 parents are cells
   .mul (selS l2States) (notC hFt.k),
   .mul (cc 6) (notC hFtt.k),
   -- OP0: axis atom; a read needs a cell root; axis 1 is local
   .mul (cc 0) (cc hFt.k),
   prodL [cc 0, notC z1C, notC hS.k],
   prodL [cc 0, cc z1C, .sub (cc vC) (.const 1)],
   -- OP3: `e = atom β`, `β = 1 − sf1_e.kind` (Nock `?`: 0 on a cell)
   .mul (cc 3) (cc hE.k),
   .mul (cc 3) (.add (.sub (cc betaC) (.const 1)) (cc hSf1.k)),
   -- OP4: atom in, atom out, successor on ATOM values only
   .mul (cc 4) (cc hSf1.k),
   .mul (cc 4) (cc hE.k),
   .mul (cc 4) (.sub (.sub (cc v2C) (cc vC)) (.const 1)),
   -- OP5
   .mul (cc 5) (cc hE.k),
   prodL [cc 5, cc betaC, cc hFtth.k, cc hFttt.k],
   neGate,
   prGate,
   .mul (cc prC) (cc hM.k),
   .mul (cc prC) (notC hSf1.k),
   .mul (cc prC) (notC hSf2.k),
   -- OP6: test atom in {0,1} (copied to `v`)
   .mul (cc 6) (cc hSf2.k),
   prodL [cc 6, cc vC, .sub (cc vC) (.const 1)],
   -- OP8: the built subject is a cell
   .mul (cc 8) (notC hM.k),
   -- OP9: axis atom; a read needs a cell core; axis 1 is local
   .mul (cc 9) (cc hFth.k),
   prodL [cc 9, notC z1C, notC hSf1.k],
   prodL [cc 9, cc z1C, .sub (cc vC) (.const 1)],
   -- cons: the result is a cell
   .mul (cc consCol) (notC hE.k)]

/-- **Equality tests** (the only base gates that read a handle value). -/
def eqGates : List (EqG F) :=
  -- SV: atom head `= j` on `OP_j`
  ((List.range 10).map fun j => ⟨cc j, hFh.v, .cst (j : F)⟩) ++
  -- OP0: axis copy; axis-1 local `e = s`
  [⟨cc 0, vC, .col hFt.v⟩] ++ heq (.mul (cc 0) (cc z1C)) hE hS ++
  -- OP1: `e = f_t`
  heq (cc 1) hE hFt ++
  -- OP3: `e.val = β`
  [⟨cc 3, hE.v, .col betaC⟩] ++
  -- OP4: `v = sf1_e.val`, `e.val = v2`
  [⟨cc 4, vC, .col hSf1.v⟩, ⟨cc 4, hE.v, .col v2C⟩] ++
  -- OP5: `e.val = β`; "=": handle equality; "≠": first-difference leaves `x1 = f_tth`, `x2 = f_ttt`
  [⟨cc 5, hE.v, .col betaC⟩] ++ heq (prodL [cc 5, notC betaC]) hSf1 hSf2 ++
  heq (prodL [cc 5, cc betaC, cc z1C]) hFtth hSf1 ++ heq (prodL [cc 5, cc betaC, cc z1C]) hFttt hSf2 ++
  [⟨prodL [cc 5, cc betaC, notC hFtth.k], vC, .col hFtth.v⟩,
   ⟨prodL [cc 5, cc betaC, notC hFttt.k], v2C, .col hFttt.v⟩] ++
  -- OP6: test copy; hosted branch `m = (1−v)·f_tth + v·f_ttt` as two selected equalities; `e = sf1_e`
  [⟨cc 6, vC, .col hSf2.v⟩] ++ heq (.mul (cc 6) (notC vC)) hM hFtth ++ heq (.mul (cc 6) (cc vC)) hM hFttt ++
  heq (cc 6) hE hSf1 ++
  -- OP7 / OP8: `e = sf1_e`
  heq (cc 7) hE hSf1 ++ heq (cc 8) hE hSf1 ++
  -- OP9: axis copy; axis-1 local arm `m = sf1_e`; `e = sf2_e`
  [⟨cc 9, vC, .col hFth.v⟩] ++ heq (.mul (cc 9) (cc z1C)) hM hSf1 ++ heq (cc 9) hE hSf2 ++
  -- claim binding: the root row's `s f e` are the claim handles (publics `0..5`; their meaning is
  -- the validity-key record with the verifier-computed fingerprint, provided memory-side)
  hpub (cc firstCol) hS 0 1 ++ hpub (cc firstCol) hF 2 3 ++ hpub (cc firstCol) hE 4 5

end Gates

/-! ## 4. Lookups: records keyed by serial (L1–L5), slots, accumulators -/

section Lookups
variable {F : Type} [Field F]

/-- Cell-table export record `(idx, l.kind, l.val, r.kind, r.val)` of parent `p`. -/
def cellRec (p l r : Hd) : List ℕ := [p.v, l.k, l.v, r.k, r.v]
/-- Walk read record `(root, axis, child.kind, child.val)`. -/
def walkRec (root : Hd) (axis : ℕ) (ch : Hd) : List ℕ := [root.v, axis, ch.k, ch.v]

/-- A slot entry: active on `states` (times `extra`), consuming `rec` from the export table
(`path = false`) or the walk records (`path = true`). -/
structure Ent (F : Type) where
  states : List ℕ
  extra : CoeffExpr F
  rcd : List ℕ
  path : Bool

def Ent.act (x : Ent F) : CoeffExpr F := .mul (selS x.states) x.extra

/-- A slot: one `𝕂` inverse; optionally a batched walk-read PAIR under the flag column. -/
structure SlotSpec (F : Type) where
  inv : ℕ
  ents : List (Ent F)
  pair : Option (ℕ × List ℕ × List ℕ)
  pairStates : List ℕ

def allStates : List ℕ := List.range 11

/-- **S0** (L1): decode `f = [f_h f_t]`, every row. -/
def slot0 : SlotSpec F := ⟨inv0, [⟨allStates, .const 1, cellRec hF hFh hFt, false⟩], none, []⟩

/-- **S1** (L2 / L4): decode `f_t = [f_th f_tt]` on `2,5..9`; OP0 read `(s, axis f_t, e)` off `z1`. -/
def slot1 : SlotSpec F :=
  ⟨inv1, [⟨l2States, .const 1, cellRec hFt hFth hFtt, false⟩,
           ⟨[0], notC z1C, walkRec hS hFt.v hE, true⟩], none, []⟩

/-- **S2** (L3 / L4 / L5): OP6 decode `f_tt`; OP9 read `(sf1_e, axis f_th, m)` off `z1`; cons
`e = [sf1_e sf2_e]`; OP8 subject `m = [sf2_e s]`; OP3 cell witness of `sf1_e` when its kind is `1`;
and the OP5 first-difference read PAIR `(sf1_e, m.val, f_tth)`, `(sf2_e, m.val, f_ttt)` under `pr`. -/
def slot2 : SlotSpec F :=
  ⟨inv2, [⟨[6], .const 1, cellRec hFtt hFtth hFttt, false⟩,
           ⟨[9], notC z1C, walkRec hSf1 hFth.v hM, true⟩,
           ⟨[consCol], .const 1, cellRec hE hSf1 hSf2, false⟩,
           ⟨[8], .const 1, cellRec hM hSf2 hS, false⟩,
           ⟨[3], cc hSf1.k, cellRec hSf1 hFtth hFttt, false⟩],
    some (prC, walkRec hSf1 hM.v hFtth, walkRec hSf2 hM.v hFttt), [5]⟩

def slots : List (SlotSpec F) := [slot0, slot1, slot2]

/-- Export / path activity of a slot. -/
def SlotSpec.actX (S : SlotSpec F) : CoeffExpr F :=
  CoeffExpr.sumList (S.ents.filter (fun x => !x.path)) Ent.act
def SlotSpec.actP (S : SlotSpec F) : CoeffExpr F :=
  .add (CoeffExpr.sumList (S.ents.filter (fun x => x.path)) Ent.act)
    (match S.pair with | some (fl, _, _) => cc fl | none => .const 0)

/-- **The accumulators** (export / path), `LogUp.accGates` at `e = 3`. -/
def accGatesH : List (CoeffExpr F) :=
  accGates 3 (slots.map fun S => ⟨S.actX, S.inv⟩) accX pubRhoX ++
    accGates 3 (slots.map fun S => ⟨S.actP, S.inv⟩) accP pubRhoP

/-- RLC of a record by a coin: `Σ_k γ^k · lift(col_k)` (the ONLY form in which a `𝕂` gate reads a
handle value). -/
def rlcKey (kind : VarKind) (γ : ℕ) : ℕ → List ℕ → MixedExpr F
  | _, [] => .Const 0
  | n, i :: r => .Add (.Mul (.Pow (.Var .challenge γ) n) (.Lift (.var kind i))) (rlcKey kind γ (n + 1) r)

def den (r : List ℕ) : MixedExpr F := .Add (.Var .challenge chalRhoL) (rlcKey .traceCur chalGammaL 0 r)

def sumM (l : List (MixedExpr F)) : MixedExpr F := l.foldr .Add (.Const 0)

/-- **The slot gate** `inv · (Σ act·den [+ pr·den_a·den_b]) − (Σ act [+ pr·(den_a + den_b)])`. -/
def slotGate (S : SlotSpec F) : MixedExpr F :=
  .Sub (.Mul (.Var .traceCur S.inv)
      (.Add (sumM (S.ents.map fun x => .Scale x.act (den x.rcd)))
        (match S.pair with
         | some (fl, a, b) => .Scale (cc fl) (.Mul (den a) (den b))
         | none => .Const 0)))
    (.Add (.Lift (CoeffExpr.sumList S.ents Ent.act))
      (match S.pair with
       | some (fl, a, b) => .Scale (cc fl) (.Add (den a) (den b))
       | none => .Const 0))

end Lookups

/-! ## 5. The compute walk over handle labels -/

section Walk
variable {F : Type} [Field F]

/-- The row label `(s, f, e)` as handles (6 base coordinates).  The state tag is NOT in the label:
a row's state is fixed by its own `f_h` decode (SV gates).  UNCONFIRMED soundness of that choice. -/
def labelCols : List ℕ := [hS.k, hS.v, hF.k, hF.v, hE.k, hE.v]

def hcols (s f e : Hd) : List ℕ := [s.k, s.v, f.k, f.v, e.k, e.v]

/-- Child labels `(subject, formula, evaluation)` per state (EC table `:1895-1990`, OP7 per the table). -/
def children : ℕ → List (List ℕ)
  | 2 => [hcols hS hFth hSf1, hcols hS hFtt hSf2, hcols hSf1 hSf2 hE]
  | 3 => [hcols hS hFt hSf1]
  | 4 => [hcols hS hFt hSf1]
  | 5 => [hcols hS hFth hSf1, hcols hS hFtt hSf2]
  | 6 => [hcols hS hM hSf1, hcols hS hFth hSf2]
  | 7 => [hcols hSf2 hFtt hSf1, hcols hS hFth hSf2]
  | 8 => [hcols hM hFtt hSf1, hcols hS hFth hSf2]
  | 9 => [hcols hS hFtt hSf1, hcols hSf1 hM hSf2]
  | 10 => [hcols hS hFh hSf1, hcols hS hFt hSf2]
  | _ => []

def wv (kind : VarKind) (i : ℕ) : MixedExpr F := .Var kind i
def kv (kind : VarKind) (i : ℕ) : CoeffExpr F := .var kind i

def curL (kind : VarKind) : MixedExpr F := rlcKey kind chalGammaW 0 labelCols

def childSum (kind : VarKind) (st : ℕ) : MixedExpr F :=
  sumM (((children st).zipIdx).map fun p =>
    .Mul (.Pow (.Var .challenge chalAlphaW) (p.2 + 1)) (rlcKey kind chalGammaW 0 p.1))

def ccL (kind : VarKind) : MixedExpr F :=
  sumM (allStates.map fun st => .Scale (kv kind st) (childSum kind st))

def cmL (kind : VarKind) : MixedExpr F :=
  sumM (allStates.map fun st => .Scale (kv kind st) (.Pow (.Var .challenge chalAlphaW) (children st).length))

def notLast : CoeffExpr F := notC lastCol

/-- **The walk gates**: line, count, accumulator (step + boundary), queue witness, terminal. -/
def walkGates : List (MixedExpr F) :=
  let αW : MixedExpr F := .Var .challenge chalAlphaW
  let lnC := wv .traceCur wLn; let lnN := wv .traceNext wLn
  let cnC := wv .traceCur wCnt; let cnN := wv .traceNext wCnt
  let acC := wv .traceCur wAcc; let acN := wv .traceNext wAcc
  [.Scale notLast (.Sub lnN (.Mul αW lnC)),
   .Scale notLast (.Sub cnN (.Mul cnC (cmL .traceNext))),
   .Scale notLast (.Sub (.Sub (.Add (.Mul lnN (curL .traceNext)) acN) acC) (.Mul cnC (ccL .traceNext))),
   .Scale (cc firstCol) (.Sub lnC αW),
   .Scale (cc firstCol) (.Sub cnC (.Mul (.Var .publicVal pubIC) (cmL .traceCur))),
   .Scale (cc firstCol) (.Sub (.Add (.Mul lnC (curL .traceCur)) acC)
      (.Add (.Mul (.Var .publicVal pubIC) (ccL .traceCur)) (.Var .publicVal pubSeed))),
   .Scale notLast (.Sub (.Mul (wv .traceCur wInv) (.Sub cnC lnC)) (.Const 1)),
   .Scale (cc lastCol) (.Sub cnC lnC),
   .Scale (cc lastCol) (.Sub acC (.Var .publicVal pubOut))]

end Walk

/-! ## 6. The gate list and the read-set instrument -/

section Assemble
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Base (`𝔽`) gates (generic builder). -/
def baseGatesH : List (CoeffExpr F) := arithGates ++ accGatesH ++ eqGates.map EqG.gate

/-- `𝕂` gates (slots, walk), generic builder. -/
def kGatesH : List (MixedExpr F) := (slots.map slotGate) ++ walkGates

/-- Constant transport `CoeffExpr G → CoeffExpr F` (columns, kinds and shape unchanged). -/
def mapC {G : Type} (φ : G → F) : CoeffExpr G → CoeffExpr F
  | .const c => .const (φ c)
  | .var k i => .var k i
  | .add a b => .add (mapC φ a) (mapC φ b)
  | .sub a b => .sub (mapC φ a) (mapC φ b)
  | .mul a b => .mul (mapC φ a) (mapC φ b)
  | .neg a => .neg (mapC φ a)
  | .pow a n => .pow (mapC φ a) n

def mapM {G : Type} (φ : G → F) : MixedExpr G → MixedExpr F
  | .Var k i => .Var k i
  | .Lift g => .Lift (mapC φ g)
  | .Scale g u => .Scale (mapC φ g) (mapM φ u)
  | .Const c => .Const c
  | .Add x y => .Add (mapM φ x) (mapM φ y)
  | .Sub x y => .Sub (mapM φ x) (mapM φ y)
  | .Neg x => .Neg (mapM φ x)
  | .Mul x y => .Mul (mapM φ x) (mapM φ y)
  | .Pow x n => .Pow (mapM φ x) n

theorem degree_mapC {G : Type} (φ : G → F) (g : CoeffExpr G) : (mapC φ g).degree = g.degree := by
  induction g with
  | const c => rfl
  | var k i => cases k <;> rfl
  | add a b iha ihb => simp only [mapC, CoeffExpr.degree, iha, ihb]
  | sub a b iha ihb => simp only [mapC, CoeffExpr.degree, iha, ihb]
  | mul a b iha ihb => simp only [mapC, CoeffExpr.degree, iha, ihb]
  | neg a iha => simp only [mapC, CoeffExpr.degree, iha]
  | pow a n iha => simp only [mapC, CoeffExpr.degree, iha]

theorem degree_mapM {G : Type} (φ : G → F) (g : MixedExpr G) : (mapM φ g).degree = g.degree := by
  induction g with
  | Var k i => cases k <;> rfl
  | Lift g => simp only [mapM, MixedExpr.degree, degree_mapC]
  | Scale g u ih => simp only [mapM, MixedExpr.degree, degree_mapC, ih]
  | Const c => rfl
  | Add x y ihx ihy => simp only [mapM, MixedExpr.degree, ihx, ihy]
  | Sub x y ihx ihy => simp only [mapM, MixedExpr.degree, ihx, ihy]
  | Neg x ih => simp only [mapM, MixedExpr.degree, ih]
  | Mul x y ihx ihy => simp only [mapM, MixedExpr.degree, ihx, ihy]
  | Pow x n ih => simp only [mapM, MixedExpr.degree, ih]

/-- **The chip's base gates over `F`**: the `ℚ`-template transported along `Rat.cast` (the only
constants are `0, 1, …, 9`, whose casts are the field's `0, 1, …, 9`).  The template is a closed
term, so every syntactic receipt is a kernel `decide`. -/
def baseGatesF : List (CoeffExpr F) := (baseGatesH (F := ℚ)).map (mapC (fun q : ℚ => (q : F)))

def kGatesF : List (MixedExpr F) := (kGatesH (F := ℚ)).map (mapM (fun q : ℚ => (q : F)))

/-- **The gates of `computeChipVCLH`.** -/
def gatesH (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  baseGatesF ++ (kGatesF (F := F)).flatMap fun g => List.ofFn (mixedCompile b VclL.Compute.TowerD.col0Id g)

end Assemble

section Instrument
variable {F : Type} [Field F]

/-- Trace columns read by a base expression. -/
def colsOf : CoeffExpr F → List ℕ
  | .const _ => []
  | .var .traceCur i => [i]
  | .var .traceNext i => [i]
  | .var _ _ => []
  | .add a b => colsOf a ++ colsOf b
  | .sub a b => colsOf a ++ colsOf b
  | .mul a b => colsOf a ++ colsOf b
  | .neg a => colsOf a
  | .pow a _ => colsOf a

/-- **No serial-capable column is read.** -/
def serialFreeB (g : CoeffExpr F) : Bool := (colsOf g).all fun i => !serialCols.contains i

/-- **`𝕂` gate discipline**: a serial-capable column may be read only as an RLC key entry
`γ^n · lift(col)`; every other base leaf is serial-free. -/
def keyOK : MixedExpr F → Bool
  | .Mul (.Pow (.Var .challenge _) _) (.Lift (.var _ _)) => true
  | .Var _ _ => true
  | .Lift g => serialFreeB g
  | .Scale g u => serialFreeB g && keyOK u
  | .Const _ => true
  | .Add x y => keyOK x && keyOK y
  | .Sub x y => keyOK x && keyOK y
  | .Mul x y => keyOK x && keyOK y
  | .Neg x => keyOK x
  | .Pow x _ => keyOK x

/-- An equality test is well-formed when its selector is serial-free (the difference `x − y` is
the only place a serial may sit). -/
def EqG.okB (g : EqG F) : Bool := serialFreeB g.σ

end Instrument

/-! ## 7. The chip -/

section Chip
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem baseTemplate_degree :
    ((baseGatesH (F := ℚ)).all fun g => decide (g.degree ≤ 4)) = true := by decide +kernel

theorem kTemplate_degree :
    ((kGatesH (F := ℚ)).all fun g => decide (g.degree ≤ 4)) = true := by decide +kernel

theorem baseGatesF_degree : ∀ g ∈ (baseGatesF : List (CoeffExpr F)), g.degree ≤ 4 := by
  intro g hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  rw [degree_mapC]
  simpa using List.all_eq_true.mp baseTemplate_degree t ht

theorem kGatesF_degree : ∀ g ∈ (kGatesF : List (MixedExpr F)), g.degree ≤ 4 := by
  intro g hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  rw [degree_mapM]
  simpa using List.all_eq_true.mp kTemplate_degree t ht

/-- **Degree `≤ 4` for every gate of the chip.** -/
theorem gatesH_degree (b : Basis (Fin 3) F K) : ∀ g ∈ gatesH b, g.degree ≤ 4 := by
  intro g hg
  simp only [gatesH, List.mem_append, List.mem_flatMap, List.mem_ofFn] at hg
  rcases hg with hg | ⟨m, hm, k, rfl⟩
  · exact baseGatesF_degree g hg
  · exact (mixedCompile_degree_le b _ m k).trans (kGatesF_degree m hm)

/-- **The handle compute RAP** (`wRAP = ![43, 27]`: B0 columns, then the coin-dependent block —
UNCONFIRMED round placement against `frameVCL`). -/
def vclRAPH [FiniteDimensional F K] {h : ℕ} (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) : RAP F :=
  { e := 3
    k := 2
    wRAP := ![round0W, 27]
    w := widthH
    w_eq := by simp [Fin.sum_univ_two, round0W, widthH]
    h := h
    d := 4
    s := (gatesH b).length
    ω := orbit.ω
    β := orbit.βcoset
    I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
    C := fun i => coeffToMv chalV pubVal ((gatesH b).get i)
    C_vars := fun _i => coeffToMv_vars chalV pubVal _
    C_deg := fun _i => (coeffToMv_totalDegree_le chalV pubVal _).trans
      (gatesH_degree b _ (List.get_mem _ _))
    H := H
    β_ne_zero := orbit.βcoset_ne_zero
    I_bound := by
      intro q hq
      have hq2 : q.2 = 0 ∨ q.2 = 1 := by
        have h2 := (Finset.mem_product.mp hq).2
        simpa [Finset.mem_insert, Finset.mem_singleton] using h2
      have hge : 2 ≤ 2 ^ h := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) orbit.h_pos
      rcases hq2 with hq' | hq' <;> rw [hq'] <;> omega }

/-- **`computeChipVCLH`**: the VS handle compute chip (preprocessing `isFirst` / `isLast` at
`11` / `12`, as `computeChipVCLQ7T`). -/
def computeChipVCLH [FiniteDimensional F K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) : FixedPreprocessingRAP F where
  rap := vclRAPH b chalV pubVal orbit (rowNodeSet nodes)
  rounds_pos := Nat.two_pos
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨11 + (j : ℕ), by
          have := j.isLt
          change 11 + (j : ℕ) < round0W
          simp only [round0W]
          omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

end Chip

end

end ChipH
end VclL.Handle
end Nock.NockVMROM.Thm54
