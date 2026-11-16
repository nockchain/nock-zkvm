/-
  Nock/Jet/ChipJ8.lean

  **The J chip `jetChipJ8`.**

  ONE straight-line interpreter: one block of rows per call; the rows of a
  block are generated from J-3a's canonical numbering `nodesOf T`.

  **Row kinds** (one selector column each): `reg` (registry entry: PROVIDES `(TAG_reg, id, h_c)`),
  `call` (CONSUMES `(TAG_reg, id, h_c)` and the output `(TAG_val, cid, 0, h_E)`, PROVIDES the subject
  `(TAG_val, cid, S, h_S)` and the SERVICE record `(id, h_c, h_S, h_E, TAG_jet)` to compute, tag LAST), `cst`,
  `add`, `mul` (the gates `val = n1`, `val = v1 + v2`, `val = v1·v2` on field values), `rp` (pair:
  ONE export read binds `h_N = [h_L h_R]`), `sl` / `sr` (one step of a read chain: ONE export read,
  the cursor `h_N` moves to `h_L` / `h_R`), `cp` (end of a read chain: copy), `isf` / `nil` (the shape
  guards).  Every node-value key is `(TAG_val, cid, nid, k, v)` (a handle `(k, v)`; a field atom is
  `k = 0`, its value on the wire).  `var i` is the chain along `T.ax i` from the subject, `nth j` the
  chain `tail^j; head`, `tlN n` the chain `tail^n`; chain cursors carry virtual node ids `> N`.

  **Columns** (`29` base + `14` `𝕂`-roles = `7` `𝕂′` pairs; width `29 + 14·3 = 71`, MEASURED by `rfl`):
  selectors `0..10`, masks `isFirst / isLast` `11, 12`, `id cid nid n1 n2` `13..17` (preprocessed),
  `m mv val v1 v2` `18..22`, handles `kN vN kL vL kR vR` `23..28`; `𝕂′` roles: four tagged slot
  inverses, the export-read inverse, the tagged accumulator (in-chip balances + the service
  provide) and the export accumulator.

  **Theorems.**  Honest acceptance at
  matmul `n = 2` (`p = 101`) by the kernel.
-/
import Nock.Jet.Interp
import Nock.NockVMROM.Thm54.VclL.Handle.MemHQ
import Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.Jet.ChipJ8

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen Nock.Jet.Interp
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.Reified Nock.NockVMROM.Thm54.MonolithicRAP

/-! ## §1 Rows: kinds, preprocessed part, witness part -/

inductive Kd where
  | reg | call | cst | add | mul | rp | sl | sr | cp | isf | nil
  deriving DecidableEq, Repr

/-- The selector column of a kind. -/
def Kd.sel : Kd → ℕ
  | .reg => 0 | .call => 1 | .cst => 2 | .add => 3 | .mul => 4 | .rp => 5 | .sl => 6 | .sr => 7
  | .cp => 8 | .isf => 9 | .nil => 10

namespace Col
def isFirst : ℕ := 11
def isLast : ℕ := 12
def id : ℕ := 13
def cid : ℕ := 14
def nid : ℕ := 15
def n1 : ℕ := 16
def n2 : ℕ := 17
def m : ℕ := 18
def mv : ℕ := 19
def val : ℕ := 20
def v1 : ℕ := 21
def v2 : ℕ := 22
def kN : ℕ := 23
def vN : ℕ := 24
def kL : ℕ := 25
def vL : ℕ := 26
def kR : ℕ := 27
def vR : ℕ := 28
/-- Base width. -/
def baseW : ℕ := 29
-- `𝕂′` pairs (`𝕂`-roles Re, Im)
def inv0 : ℕ := 0
def inv1 : ℕ := 2
def inv2 : ℕ := 4
def inv3 : ℕ := 6
def invX : ℕ := 8
def accT : ℕ := 10
def accX : ℕ := 12
/-- `𝕂`-roles. -/
def extW : ℕ := 14
end Col

/-- **Preprocessed part of a row** (the verifier's layout): kind, registry id, call id, node id,
operand ids / parameter. -/
structure PRow where
  kd : Kd
  id : ℕ
  cid : ℕ
  nid : ℕ
  n1 : ℕ
  n2 : ℕ
  deriving DecidableEq, Repr

/-- **Witness part of a row.** -/
structure WRow (F : Type) where
  m : F
  mv : F
  val : F
  v1 : F
  v2 : F
  kN : F
  vN : F
  kL : F
  vL : F
  kR : F
  vR : F
  deriving DecidableEq, Repr

structure CRow (F : Type) where
  pre : PRow
  w : WRow F
  deriving DecidableEq, Repr

/-- The base columns of a row (masks read as `0`: they enter only the accumulator gates). -/
def colOf {F : Type} [Field F] (r : CRow F) (j : ℕ) : F :=
  if j < 11 then (if r.pre.kd.sel = j then 1 else 0) else
  match j with
  | 13 => (r.pre.id : F) | 14 => (r.pre.cid : F) | 15 => (r.pre.nid : F) | 16 => (r.pre.n1 : F)
  | 17 => (r.pre.n2 : F) | 18 => r.w.m | 19 => r.w.mv | 20 => r.w.val | 21 => r.w.v1
  | 22 => r.w.v2 | 23 => r.w.kN | 24 => r.w.vN | 25 => r.w.kL | 26 => r.w.vL | 27 => r.w.kR
  | 28 => r.w.vR | _ => 0

/-- The row's current-row environment. -/
def envOf {F : Type} [Field F] (r : CRow F) : Env F := ⟨colOf r, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-! ## §2 Balance keys: ONE table drives both the gates and the semantics -/

/-- A key entry: a base column or a constant. -/
inductive KE where
  | col (j : ℕ)
  | k (c : ℕ)
  deriving DecidableEq, Repr

def KE.ev {F : Type} [Field F] (f : ℕ → F) : KE → F
  | .col j => f j
  | .k c => (c : F)

/-- Tags: `TAG_val = 1`, `TAG_reg = 2`, `TAG_jet = 3`. -/
def keyV (n k v : KE) : List KE := [.k 1, .col Col.cid, n, k, v]
def keyRg : List KE := [.k 2, .col Col.id, .col Col.kN, .col Col.vN]
/-- The SERVICE key `(id, h_c, h_S, h_E, TAG_jet)`: `TAG_jet` is the LAST (8th) entry (C-2 step 0, the
fix of C-1's finding `jetKey_collides_walkRecA`: with the tag first, a zero-handle jet key equalled a
4-entry `walkRecA` key as a polynomial in `γ`; with the tag in position 7 it never does). -/
def keyJet : List KE :=
  [.col Col.id, .col Col.kN, .col Col.vN, .col Col.kL, .col Col.vL, .col Col.kR, .col Col.vR, .k 3]
/-- The export record `(hN.v, hL.k, hL.v, hR.k, hR.v)` (`keyH` shape). -/
def keyX : List KE := [.col Col.vN, .col Col.kL, .col Col.vL, .col Col.kR, .col Col.vR]

open Col in
/-- Slot 0 (consume): first operand / the registry entry. -/
def ents0 : List (Kd × List KE) :=
  [(.add, keyV (.col n1) (.k 0) (.col v1)), (.mul, keyV (.col n1) (.k 0) (.col v1)),
   (.rp, keyV (.col n1) (.col kL) (.col vL)), (.sl, keyV (.col n1) (.col kN) (.col vN)),
   (.sr, keyV (.col n1) (.col kN) (.col vN)), (.cp, keyV (.col n1) (.col kL) (.col vL)),
   (.isf, keyV (.col n1) (.k 0) (.col v1)), (.nil, keyV (.col n1) (.k 0) (.k 0)),
   (.call, keyRg)]

open Col in
/-- Slot 1 (consume): second operand / the output node `0`. -/
def ents1 : List (Kd × List KE) :=
  [(.add, keyV (.col n2) (.k 0) (.col v2)), (.mul, keyV (.col n2) (.k 0) (.col v2)),
   (.rp, keyV (.col n2) (.col kR) (.col vR)), (.call, keyV (.k 0) (.col kR) (.col vR))]

open Col in
/-- Slot 2 (provide, multiplicity `mv`): the row's node value / the registry entry / the subject. -/
def ents2 : List (Kd × List KE) :=
  [(.cst, keyV (.col nid) (.k 0) (.col val)), (.add, keyV (.col nid) (.k 0) (.col val)),
   (.mul, keyV (.col nid) (.k 0) (.col val)), (.rp, keyV (.col nid) (.col kN) (.col vN)),
   (.sl, keyV (.col nid) (.col kL) (.col vL)), (.sr, keyV (.col nid) (.col kR) (.col vR)),
   (.cp, keyV (.col nid) (.col kL) (.col vL)), (.isf, keyV (.col nid) (.k 0) (.col v1)),
   (.nil, keyV (.col nid) (.k 0) (.k 0)), (.reg, keyRg), (.call, keyV (.col n2) (.col kL) (.col vL))]

/-- Slot 3 (the SERVICE provide to compute, multiplicity `m`). -/
def ents3 : List (Kd × List KE) := [(.call, keyJet)]

/-- The export-read slot (consume; third consumer of the cell export balance). -/
def entsX : List (Kd × List KE) := [(.rp, keyX), (.sl, keyX), (.sr, keyX)]

/-- The keys a row puts in the slots `es`. -/
def keysOf {F : Type} [Field F] (es : List (Kd × List KE)) (r : CRow F) : List (List F) :=
  (es.filter fun e => e.1 == r.pre.kd).map fun e => e.2.map (KE.ev (colOf r))

/-- In-chip consumes / provides. -/
def consK {F : Type} [Field F] (r : CRow F) : List (List F) := keysOf ents0 r ++ keysOf ents1 r
def provK {F : Type} [Field F] (r : CRow F) : List (List F) := keysOf ents2 r

/-! ## §3 Gates -/

section Gates
variable {F : Type} [Field F]

def KE.expr : KE → CoeffExpr F
  | .col j => cv j
  | .k c => .const (c : F)

/-- **Base gates**: the const / add / mul gates on field values, and `kN = 1` on export reads. -/
def baseGatesJ : List (CoeffExpr F) :=
  [ .mul (cv (Kd.sel .cst)) (.sub (cv Col.val) (cv Col.n1)),
    .mul (cv (Kd.sel .add)) (.sub (cv Col.val) (.add (cv Col.v1) (cv Col.v2))),
    .mul (cv (Kd.sel .mul)) (.sub (cv Col.val) (.mul (cv Col.v1) (cv Col.v2))),
    .mul (.add (.add (cv (Kd.sel .rp)) (cv (Kd.sel .sl))) (cv (Kd.sel .sr)))
      (.sub (cv Col.kN) (.const 1)) ]

/-- Coins: tagged `γ = (χ0, χ2)`, `ρ = (χ1, χ3)`; export `γ = (χ4, χ6)`, `ρ = (χ5, χ7)`. -/
def gamT : QE F := QE.chal 0 2
def rhoT : QE F := QE.chal 1 3
def gamX : QE F := QE.chal 4 6
def rhoX : QE F := QE.chal 5 7

def gpowJ (δ : F) (g : QE F) : ℕ → QE F
  | 0 => QE.one
  | n + 1 => QE.mul δ g (gpowJ δ g n)

/-- `Σ_k γ^k · lift(key_k)`. -/
def rlcJ (δ : F) (g : QE F) : ℕ → List KE → QE F
  | _, [] => QE.zero
  | n, e :: r => QE.add (QE.mul δ (gpowJ δ g n) (QE.base e.expr)) (rlcJ δ g (n + 1) r)

def denJ (δ : F) (g ρ : QE F) (l : List KE) : QE F := QE.add ρ (rlcJ δ g 0 l)

def sumQE (l : List (QE F)) : QE F := l.foldr QE.add QE.zero

/-- `Σ` of the slot's selectors, read through `rd` (current or next row). -/
def selSum (rd : ℕ → CoeffExpr F) (es : List (Kd × List KE)) : CoeffExpr F :=
  CoeffExpr.sumList es fun e => rd e.1.sel

/-- **The slot gate**: `inv · Σ sel·den(key) − Σ sel` (the selectors of a slot are exclusive). -/
def slotGate (δ : F) (g ρ : QE F) (inv : ℕ) (es : List (Kd × List KE)) : QE F :=
  QE.sub (QE.mul δ (QE.var inv) (sumQE (es.map fun e => QE.scale (cv e.1.sel) (denJ δ g ρ e.2))))
    (QE.base (selSum cv es))

def slotGates (δ : F) : List (QE F) :=
  [ slotGate δ gamT rhoT Col.inv0 ents0, slotGate δ gamT rhoT Col.inv1 ents1,
    slotGate δ gamT rhoT Col.inv2 ents2, slotGate δ gamT rhoT Col.inv3 ents3,
    slotGate δ gamX rhoX Col.invX entsX ]

/-- The tagged accumulator's row contribution: consumes `+1`, in-chip provides `−mv`, the service
provide `−m`. -/
def contribT (rd : ℕ → CoeffExpr F) (iv : ℕ → QE F) : QE F :=
  sumQE [ QE.scale (selSum rd ents0) (iv Col.inv0), QE.scale (selSum rd ents1) (iv Col.inv1),
    QE.scale (.neg (.mul (selSum rd ents2) (rd Col.mv))) (iv Col.inv2),
    QE.scale (.neg (.mul (rd (Kd.sel .call)) (rd Col.m))) (iv Col.inv3) ]

def contribX (rd : ℕ → CoeffExpr F) (iv : ℕ → QE F) : QE F :=
  QE.scale (selSum rd entsX) (iv Col.invX)

/-- **Accumulators** (init / step / terminal; tagged terminal = public `0/1`, export `2/3`). -/
def accGates : List (QE F) :=
  [ QE.scale (cv Col.isFirst) (QE.sub (QE.var Col.accT) (contribT cv QE.var)),
    QE.scale (notE (cv Col.isLast))
      (QE.sub (QE.sub (QE.next Col.accT) (QE.var Col.accT)) (contribT nv QE.next)),
    QE.scale (cv Col.isLast) (QE.sub (QE.var Col.accT) (QE.pub 0)),
    QE.scale (cv Col.isFirst) (QE.sub (QE.var Col.accX) (contribX cv QE.var)),
    QE.scale (notE (cv Col.isLast))
      (QE.sub (QE.sub (QE.next Col.accX) (QE.var Col.accX)) (contribX nv QE.next)),
    QE.scale (cv Col.isLast) (QE.sub (QE.var Col.accX) (QE.pub 2)) ]

/-- **The `𝕂`-valued gates** (each `𝕂′` equation is two `𝕂` gates). -/
def gatesJ (δ : F) : List (MixedExpr F) := (slotGates δ ++ accGates).flatMap QE.gates

end Gates

/-! ## §4 Degree, template, width -/

section Template
variable {F : Type} [Field F]

theorem baseGatesJ_deg : ∀ g ∈ (baseGatesJ : List (CoeffExpr F)), g.degree ≤ 4 := by
  intro g hg
  simp only [baseGatesJ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp [CoeffExpr.degree]

theorem gatesJ_deg_all (δ : F) : (gatesJ δ).all (fun g => decide (g.degree ≤ 4)) = true := by
  simp [gatesJ, slotGates, accGates, slotGate, contribT, contribX, denJ, rlcJ, gpowJ, sumQE, selSum,
    CoeffExpr.sumList, ents0, ents1, ents2, ents3, entsX, keyV, keyRg, keyJet, keyX, KE.expr,
    gamT, rhoT, gamX, rhoX, Kd.sel, QE.gates, QE.var, QE.next, QE.chal, QE.pub, QE.base, QE.zero,
    QE.one, QE.add, QE.sub, QE.mul, QE.scale, MixedExpr.degree, CoeffExpr.degree]

theorem gatesJ_degree (δ : F) : ∀ g ∈ gatesJ δ, g.degree ≤ 4 := by
  intro g hg
  simpa using List.all_eq_true.mp (gatesJ_deg_all δ) g hg

/-- **The J chip template**: base `29`, `𝕂`-roles `0 / 14` (round 1: the coin-dependent block). -/
def jetTemplateJ8 (δ : F) : ChipTemplate F where
  rounds := 2
  rounds_pos := by decide
  baseColsOf := ![29, 0]
  extColsOf := ![0, 14]
  baseTransition := baseGatesJ
  extTransition := []
  mixedTransition := gatesJ δ
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := baseGatesJ_deg
  extTransition_deg := by simp
  mixedTransition_deg := gatesJ_degree δ
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

/-- **Width, MEASURED: `71`** (`29` base + `14` `𝕂`-roles × `3`). -/
theorem jetTemplateJ8_width (δ : F) : (jetTemplateJ8 δ).width 3 = 71 := rfl

end Template


section Instrument
variable {F : Type} [Field F]

/-- The serial-capable columns: the handle values. -/
def serialJ : List ℕ := [Col.vN, Col.vL, Col.vR]

def serialFreeJ (g : CoeffExpr F) : Bool :=
  (VclL.Handle.ChipH.colsOf g).all fun i => !serialJ.contains i

/-- `keyOKQe` (ChipHQ) with the J chip's serial columns. -/
def keyOKJe : MixedExpr F → Bool
  | .Mul x (.Lift (.var _ _)) => VclL.Handle.ChipHQ.coinOnly x
  | .Var _ _ => true
  | .Lift g => serialFreeJ g
  | .Scale g u => serialFreeJ g && keyOKJe u
  | .Const _ => true
  | .Add x y => keyOKJe x && keyOKJe y
  | .Sub x y => keyOKJe x && keyOKJe y
  | .Mul x y => keyOKJe x && keyOKJe y
  | .Neg x => keyOKJe x
  | .Pow x _ => keyOKJe x

theorem gatesJ_keyOK : (gatesJ (F := ℚ) 7).all keyOKJe = true := by decide +kernel

/-- The base gates read no serial column. -/
theorem baseGatesJ_serialFree : (baseGatesJ (F := ℚ)).all serialFreeJ = true := by decide +kernel

/-- **Positive controls**: the instrument flags a serial times a trace column, and a base gate on
a serial. -/
theorem keyOKJ_flags :
    keyOKJe (F := ℚ) (.Mul (.Var .traceCur 0) (.Lift (cv Col.vN))) = false ∧
      serialFreeJ (F := ℚ) (.sub (cv Col.vL) (.const 1)) = false := by decide +kernel

end Instrument

/-! ## §6 The verifier's layout (public: the registry and the call sequence) -/

/-- A read path (`true` = tail / right, `false` = head / left). -/
def followPath : List Bool → Noun → Option Noun
  | [], x => some x
  | b :: bs, .cell l r => followPath bs (if b then r else l)
  | _ :: _, .atom _ => none

def axPathF : ℕ → ℕ → List Bool
  | 0, _ => []
  | f + 1, a => if a < 2 then [] else axPathF f (a / 2) ++ [a % 2 == 1]

/-- The path of an axis (`1 ↦ []`, `2a ↦ path a ++ [head]`, `2a+1 ↦ path a ++ [tail]`). -/
def axPath (a : ℕ) : List Bool := axPathF a a

/-- A read chain from node `src` to node `dst`: one `sl`/`sr` row per step (cursor ids `ctr, ctr+1, …`),
then a `cp` row. -/
def chainPre (c dst : ℕ) : ℕ → ℕ → List Bool → List PRow
  | src, _, [] => [⟨.cp, 0, c, dst, src, 0⟩]
  | src, ctr, b :: bs => ⟨if b then .sr else .sl, 0, c, ctr, src, 0⟩ :: chainPre c dst ctr (ctr + 1) bs

/-- The rows of one J-3a node (`S` = the subject's node id, `ctr` = the next free cursor id). -/
def nodePre (c S ctr : ℕ) (nd : JNode) : List PRow :=
  match nd.op with
  | .var _ ax => chainPre c nd.id S ctr (axPath ax)
  | .nth j => chainPre c nd.id nd.a ctr (List.replicate j true ++ [false])
  | .tlN n => chainPre c nd.id nd.a ctr (List.replicate n true)
  | .const k => [⟨.cst, 0, c, nd.id, k, 0⟩]
  | .add => [⟨.add, 0, c, nd.id, nd.a, nd.b⟩]
  | .mul => [⟨.mul, 0, c, nd.id, nd.a, nd.b⟩]
  | .pair => [⟨.rp, 0, c, nd.id, nd.a, nd.b⟩]
  | .isF => [⟨.isf, 0, c, nd.id, nd.a, 0⟩]
  | .isNil => [⟨.nil, 0, c, nd.id, nd.a, 0⟩]

def nodeVirt (nd : JNode) : ℕ :=
  match nd.op with
  | .var _ ax => (axPath ax).length
  | .nth j => j + 1
  | .tlN n => n
  | _ => 0

def nodesPre (c S : ℕ) : ℕ → List JNode → List PRow
  | _, [] => []
  | ctr, nd :: nds => nodePre c S ctr nd ++ nodesPre c S (ctr + nodeVirt nd) nds

/-- The call row of block `c` (template id `i`; the subject is node `N = |nodesOf T|`). -/
def callPre (R : ℕ → Tpl) (c i : ℕ) : PRow := ⟨.call, i, c, 0, 0, (nodesOf (R i)).length⟩

def blockPre (R : ℕ → Tpl) (c i : ℕ) : List PRow :=
  callPre R c i :: nodesPre c (nodesOf (R i)).length ((nodesOf (R i)).length + 1) (nodesOf (R i))

def blocks (R : ℕ → Tpl) : ℕ → List ℕ → List PRow
  | _, [] => []
  | c, i :: is => blockPre R c i ++ blocks R (c + 1) is

def regPre (i : ℕ) : PRow := ⟨.reg, i, 0, 0, 0, 0⟩

/-- **The layout**: the registry rows, then one block per call. -/
def layoutJ8 (R : ℕ → Tpl) (regs ids : List ℕ) : List PRow := regs.map regPre ++ blocks R 0 ids

/-- The node id a row provides (the subject's for the call row). -/
def PRow.pn (q : PRow) : ℕ := if q.kd = .call then q.n2 else q.nid

/-- The `(call, node)` a row provides under `TAG_val`. -/
def tvKey (q : PRow) : Option (ℕ × ℕ) := if q.kd = .reg then none else some (q.cid, q.pn)

/-- Every `var` axis of the template is `≥ 1` (a public check on the registry). -/
def axPosB (T : Tpl) : Bool :=
  (nodesOf T).all fun nd => match nd.op with
    | .var _ a => decide (0 < a)
    | _ => true

theorem mem_blocks (R : ℕ → Tpl) : ∀ (ids : List ℕ) (c0 c i : ℕ), ids[c]? = some i →
    ∀ q ∈ blockPre R (c0 + c) i, q ∈ blocks R c0 ids
  | [], _, _, _, h => by simp at h
  | j :: is, c0, 0, i, h => by
    intro q hq
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [Nat.add_zero] at hq
    simp [blocks, hq]
  | j :: is, c0, c + 1, i, h => by
    intro q hq
    have := mem_blocks R is (c0 + 1) c i (by simpa using h) q
      (by rwa [show c0 + 1 + c = c0 + (c + 1) by omega])
    simp [blocks, this]

theorem mem_nodesPre (c S : ℕ) : ∀ (nds : List JNode) (ctr : ℕ) (nd : JNode), nd ∈ nds →
    ∃ ctr', ∀ q ∈ nodePre c S ctr' nd, q ∈ nodesPre c S ctr nds
  | [], _, _, h => by simp at h
  | x :: xs, ctr, nd, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨ctr, fun q hq => by simp [nodesPre, hq]⟩
    · obtain ⟨c', hc'⟩ := mem_nodesPre c S xs (ctr + nodeVirt x) nd h
      exact ⟨c', fun q hq => by simp only [nodesPre, List.mem_append]; exact Or.inr (hc' q hq)⟩

/-! ### Paths -/

theorem followPath_append : ∀ (l1 l2 : List Bool) (x : Noun),
    followPath (l1 ++ l2) x = (followPath l1 x).bind (followPath l2)
  | [], _, _ => rfl
  | _ :: bs, l2, .cell _ _ => followPath_append bs l2 _
  | _ :: _, _, .atom _ => rfl

theorem tailO_path : ∀ (n : ℕ) (x : Noun), tailO n x = followPath (List.replicate n true) x
  | 0, _ => rfl
  | _ + 1, .atom _ => rfl
  | n + 1, .cell _ t => by
    simp only [tailO, List.replicate_succ, followPath, if_true]
    exact tailO_path n t

theorem nthO_path (j : ℕ) (x : Noun) :
    nthO j x = followPath (List.replicate j true ++ [false]) x := by
  rw [followPath_append, ← tailO_path]
  unfold nthO
  rcases tailO j x with _ | y
  · rfl
  · cases y <;> rfl

theorem slot_path : ∀ (f a : ℕ) (x : Noun), 1 ≤ a → a ≤ f →
    Noun.slot a x = followPath (axPathF f a) x
  | 0, _, _, h1, h2 => by omega
  | f + 1, a, x, h1, h2 => by
    by_cases ha : a < 2
    · obtain rfl : a = 1 := by omega
      simp [axPathF, followPath, Noun.slot]
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
      rw [axPathF, if_neg ha, followPath_append,
        ← slot_path f ((a' + 2) / 2) x (by omega) (by omega), Noun.slot]
      rcases Noun.slot ((a' + 2) / 2) x with _ | (_ | ⟨l, r⟩)
      · rfl
      · rfl
      · rcases Nat.mod_two_eq_zero_or_one (a' + 2) with h | h <;> simp [h, followPath]

theorem slot_axPath {a : ℕ} (x : Noun) (h : 0 < a) : Noun.slot a x = followPath (axPath a) x :=
  slot_path a a x h le_rfl

/-! ## §7 Soundness -/

section Sound
variable {F : Type} [Field F]

@[simp] theorem colOf_sel (r : CRow F) (kd : Kd) : colOf r kd.sel = if r.pre.kd = kd then 1 else 0 := by
  cases kd <;> cases h : r.pre.kd <;> simp [colOf, Kd.sel, h]

@[simp] theorem colOf_val (r : CRow F) : colOf r Col.val = r.w.val := rfl
@[simp] theorem colOf_v1 (r : CRow F) : colOf r Col.v1 = r.w.v1 := rfl
@[simp] theorem colOf_v2 (r : CRow F) : colOf r Col.v2 = r.w.v2 := rfl
@[simp] theorem colOf_n1 (r : CRow F) : colOf r Col.n1 = r.pre.n1 := rfl
@[simp] theorem colOf_kN (r : CRow F) : colOf r Col.kN = r.w.kN := rfl

/-- What the base gates say on a row. -/
theorem gate_facts (r : CRow F) (h : ∀ g ∈ (baseGatesJ : List (CoeffExpr F)), g.eval (envOf r) = 0) :
    (r.pre.kd = .cst → r.w.val = r.pre.n1) ∧ (r.pre.kd = .add → r.w.val = r.w.v1 + r.w.v2) ∧
      (r.pre.kd = .mul → r.w.val = r.w.v1 * r.w.v2) ∧
      (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr → r.w.kN = 1) := by
  simp only [baseGatesJ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [CoeffExpr.eval, envOf, colOf_sel, colOf_val, colOf_v1, colOf_v2, colOf_n1,
    colOf_kN] at h1 h2 h3 h4
  refine ⟨fun hk => ?_, fun hk => ?_, fun hk => ?_, fun hk => ?_⟩
  · simp only [hk, if_true, one_mul] at h1; exact sub_eq_zero.1 h1
  · simp only [hk, if_true, one_mul] at h2; exact sub_eq_zero.1 h2
  · simp only [hk, if_true, one_mul] at h3; exact sub_eq_zero.1 h3
  · rcases hk with hk | hk | hk <;> simp [hk] at h4 <;> exact sub_eq_zero.1 h4

/-- The handle a non-`reg` row provides under `TAG_val`. -/
def provHW (r : CRow F) : F × F :=
  match r.pre.kd with
  | .cst | .add | .mul => (((0 : ℕ) : F), r.w.val)
  | .rp => (r.w.kN, r.w.vN)
  | .sl | .cp | .call => (r.w.kL, r.w.vL)
  | .sr => (r.w.kR, r.w.vR)
  | .isf => (((0 : ℕ) : F), r.w.v1)
  | .nil => (((0 : ℕ) : F), ((0 : ℕ) : F))
  | .reg => (r.w.kN, r.w.vN)

theorem provK_eq (r : CRow F) (h : r.pre.kd ≠ .reg) :
    provK r = [[((1 : ℕ) : F), (r.pre.cid : F), (r.pre.pn : F), (provHW r).1, (provHW r).2]] := by
  obtain ⟨⟨kd, id, cid, nid, n1, n2⟩, w⟩ := r
  cases kd <;> first | exact absurd rfl h | rfl

theorem provK_reg (r : CRow F) (h : r.pre.kd = .reg) :
    provK r = [[((2 : ℕ) : F), (r.pre.id : F), r.w.kN, r.w.vN]] := by
  obtain ⟨⟨kd, id, cid, nid, n1, n2⟩, w⟩ := r
  cases h; rfl

theorem consK_call (id c n2 : ℕ) (w : WRow F) :
    consK (⟨⟨.call, id, c, 0, 0, n2⟩, w⟩ : CRow F) =
      [[((2 : ℕ) : F), (id : F), w.kN, w.vN], [((1 : ℕ) : F), (c : F), ((0 : ℕ) : F), w.kR, w.vR]] := rfl

end Sound

section SoundP
variable {p : ℕ} [Fact p.Prime]

instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

theorem natCast_inj_lt {a b : ℕ} (ha : a < p) (hb : b < p) (h : (a : ZMod p) = b) : a = b := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- The genuine-record check of an export read (black box: memory's served records). -/
def recB (den : ZMod p × ZMod p → Option Noun) (r : CRow (ZMod p)) : Bool :=
  match den (r.w.kL, r.w.vL), den (r.w.kR, r.w.vR) with
  | some a, some b => decide (den (1, r.w.vN) = some (.cell a b))
  | _, _ => false

theorem recB_true {den : ZMod p × ZMod p → Option Noun} {r : CRow (ZMod p)} (h : recB den r = true) :
    ∃ a b, den (r.w.kL, r.w.vL) = some a ∧ den (r.w.kR, r.w.vR) = some b ∧
      den (1, r.w.vN) = some (.cell a b) := by
  unfold recB at h
  split at h
  · rename_i a b ha hb
    exact ⟨a, b, ha, hb, of_decide_eq_true h⟩
  · simp at h

/-- **Chip-accepted, outside the balance events**: the rows realize the public layout, the
preprocessed numbers are below `p`, the layout provides each `(call, node)` once, every base gate
vanishes on every row, and the in-chip tagged balance holds in existence form (every consumed key is
provided by some row — the LogUp conclusion outside its bad event). -/
structure Accepted (R : ℕ → Tpl) (regs ids : List ℕ) (rows : List (CRow (ZMod p))) : Prop where
  lay : rows.map CRow.pre = layoutJ8 R regs ids
  small : ∀ q ∈ layoutJ8 R regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p
  uniq : ((layoutJ8 R regs ids).filterMap tvKey).Nodup
  gate : ∀ r ∈ rows, ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod p))), g.eval (envOf r) = 0
  bal : ∀ r ∈ rows, ∀ κ ∈ consK r, ∃ r' ∈ rows, κ ∈ provK r'

/-- **Memory as a black box**: a kind-`0` handle is its field atom (the wire convention); every export
record an `rp/sl/sr` row consumes is genuine (`exportH_genuine`'s class); every registry row's root
handle denotes `compile p (R id)` (the public-side `FP_id` claim binding, `claimH_genuine`'s class). -/
structure MemoryBB (R : ℕ → Tpl) (rows : List (CRow (ZMod p)))
    (den : ZMod p × ZMod p → Option Noun) : Prop where
  den0 : ∀ v : ZMod p, den (0, v) = some (.atom v.val)
  gen : ∀ r ∈ rows, (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) → recB den r = true
  reg : ∀ r ∈ rows, r.pre.kd = .reg → den (r.w.kN, r.w.vN) = some (compile p (R r.pre.id))

theorem eq_of_filterMap_nodup {α β : Type} (f : α → Option β) : ∀ (l : List α), (l.filterMap f).Nodup →
    ∀ a ∈ l, ∀ b ∈ l, ∀ k, f a = some k → f b = some k → a = b
  | [], _, a, ha, _, _, _, _, _ => by simp at ha
  | x :: xs, hnd, a, ha, b, hb, k, hfa, hfb => by
    have ih := eq_of_filterMap_nodup f xs
    cases hx : f x with
    | none =>
      rw [List.filterMap_cons_none hx] at hnd
      rcases List.mem_cons.1 ha with rfl | ha <;> rcases List.mem_cons.1 hb with rfl | hb
      · rfl
      · simp [hx] at hfa
      · simp [hx] at hfb
      · exact ih hnd a ha b hb k hfa hfb
    | some k0 =>
      rw [List.filterMap_cons_some hx, List.nodup_cons] at hnd
      rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
      · rfl
      · rw [hx] at hfa; obtain rfl := Option.some.inj hfa
        exact absurd (List.mem_filterMap.2 ⟨b, hb', hfb⟩) hnd.1
      · rw [hx] at hfb; obtain rfl := Option.some.inj hfb
        exact absurd (List.mem_filterMap.2 ⟨a, ha', hfa⟩) hnd.1
      · exact ih hnd.2 a ha' b hb' k hfa hfb

variable {R : ℕ → Tpl} {regs ids : List ℕ} {rows : List (CRow (ZMod p))}

open Classical in
/-- The handle served for `(call c, node n)`: the providing row's (unique, by the layout). -/
noncomputable def Hn (rows : List (CRow (ZMod p))) (c n : ℕ) : ZMod p × ZMod p :=
  if h : ∃ r ∈ rows, tvKey r.pre = some (c, n) then provHW (Classical.choose h) else (0, 0)

theorem pre_mem (hA : Accepted R regs ids rows) {r : CRow (ZMod p)} (hr : r ∈ rows) :
    r.pre ∈ layoutJ8 R regs ids := hA.lay ▸ List.mem_map_of_mem hr

theorem real (hA : Accepted R regs ids rows) {q : PRow} (hq : q ∈ layoutJ8 R regs ids) :
    ∃ r ∈ rows, r.pre = q := by
  rw [← hA.lay] at hq; exact List.mem_map.1 hq

theorem Hn_prov (hA : Accepted R regs ids rows) {r : CRow (ZMod p)} (hr : r ∈ rows) {c n : ℕ}
    (h : tvKey r.pre = some (c, n)) : Hn rows c n = provHW r := by
  have hex : ∃ r ∈ rows, tvKey r.pre = some (c, n) := ⟨r, hr, h⟩
  unfold Hn; rw [dif_pos hex]
  have hs := Classical.choose_spec hex
  have hnd : (rows.filterMap (tvKey ∘ CRow.pre)).Nodup := by
    rw [← List.filterMap_map, hA.lay]; exact hA.uniq
  rw [eq_of_filterMap_nodup (tvKey ∘ CRow.pre) rows hnd _ hs.1 r hr (c, n) hs.2 h]

theorem tvKey_of {q : PRow} (h : q.kd ≠ .reg) : tvKey q = some (q.cid, q.pn) := by
  simp [tvKey, h]

/-- **A consumed `TAG_val` key is the served handle.** -/
theorem served (hA : Accepted R regs ids rows) {r : CRow (ZMod p)} (hr : r ∈ rows) {c n : ℕ}
    (hc : c < p) (hn : n < p) {k v : ZMod p}
    (hκ : [((1 : ℕ) : ZMod p), (c : ZMod p), (n : ZMod p), k, v] ∈ consK r) : Hn rows c n = (k, v) := by
  obtain ⟨r', hr', hκ'⟩ := hA.bal r hr _ hκ
  by_cases hreg : r'.pre.kd = .reg
  · rw [provK_reg r' hreg] at hκ'; simp at hκ'
  · rw [provK_eq r' hreg] at hκ'
    simp only [List.mem_singleton, List.cons.injEq] at hκ'
    obtain ⟨-, h1, h2, h3, h4, -⟩ := hκ'
    obtain ⟨-, hcid, hnid, -, hn2⟩ := hA.small _ (pre_mem hA hr')
    have hpn : r'.pre.pn < p := by unfold PRow.pn; split <;> assumption
    have e1 := natCast_inj_lt hc hcid h1
    have e2 := natCast_inj_lt hn hpn h2
    rw [Hn_prov hA hr' (by rw [tvKey_of hreg, e1, e2]), h3, h4]

/-- The value the chip serves for node `n` of call `c`. -/
noncomputable def lookC (den : ZMod p × ZMod p → Option Noun) (rows : List (CRow (ZMod p))) (c n : ℕ) :
    Noun := (den (Hn rows c n)).getD z0

/-- An export-read row: `kN = 1` and the record is genuine. -/
theorem rd_facts (hA : Accepted R regs ids rows) {den : ZMod p × ZMod p → Option Noun}
    (hM : MemoryBB R rows den) {r : CRow (ZMod p)} (hr : r ∈ rows)
    (hk : r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) :
    ∃ a b, den (r.w.kL, r.w.vL) = some a ∧ den (r.w.kR, r.w.vR) = some b ∧
      den (r.w.kN, r.w.vN) = some (.cell a b) := by
  have h1 := (gate_facts r (hA.gate r hr)).2.2.2 hk
  obtain ⟨a, b, ha, hb, hc⟩ := recB_true (hM.gen r hr hk)
  exact ⟨a, b, ha, hb, by rw [h1]; exact hc⟩

theorem chain_ok (hA : Accepted R regs ids rows) {den : ZMod p × ZMod p → Option Noun}
    (hM : MemoryBB R rows den) {c dst : ℕ} (hcp : c < p) :
    ∀ (bs : List Bool) (src ctr : ℕ), (∀ q ∈ chainPre c dst src ctr bs, q ∈ layoutJ8 R regs ids) →
      followPath bs (lookC den rows c src) = some (lookC den rows c dst) ∧
      (bs = [] → Hn rows c dst = Hn rows c src) ∧
      (bs ≠ [] → ∃ y, den (Hn rows c dst) = some y)
  | [], src, ctr, hsub => by
    obtain ⟨r, hr, hpre⟩ := real hA (hsub ⟨.cp, 0, c, dst, src, 0⟩ (by simp [chainPre]))
    obtain ⟨-, -, hnid, hn1, -⟩ := hA.small _ (pre_mem hA hr)
    rw [hpre] at hnid hn1
    have hc : consK r = [[((1 : ℕ) : ZMod p), (c : ZMod p), (src : ZMod p), r.w.kL, r.w.vL]] := by
      obtain ⟨pre, w⟩ := r; simp only at hpre; subst hpre; rfl
    have h1 := served hA hr hcp hn1 (by rw [hc]; exact List.mem_singleton_self _)
    have h2 := Hn_prov hA hr (c := c) (n := dst) (by rw [hpre]; rfl)
    have hp : provHW r = (r.w.kL, r.w.vL) := by
      obtain ⟨pre, w⟩ := r; simp only at hpre; subst hpre; rfl
    have heq : Hn rows c dst = Hn rows c src := by rw [h2, hp, h1]
    exact ⟨by simp [followPath, lookC, heq], fun _ => heq, fun h => absurd rfl h⟩
  | b :: bs, src, ctr, hsub => by
    obtain ⟨r, hr, hpre⟩ :=
      real hA (hsub ⟨if b then .sr else .sl, 0, c, ctr, src, 0⟩ (by simp [chainPre]))
    obtain ⟨-, -, hnid, hn1, -⟩ := hA.small _ (pre_mem hA hr)
    rw [hpre] at hnid hn1
    have ih := chain_ok (dst := dst) hA hM hcp bs ctr (ctr + 1)
      (fun q hq => hsub q (by simp only [chainPre, List.mem_cons]; exact Or.inr hq))
    have hk : r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr := by
      rw [hpre]; cases b <;> simp
    obtain ⟨A, B, hA', hB', hN⟩ := rd_facts hA hM hr hk
    have hc : consK r = [[((1 : ℕ) : ZMod p), (c : ZMod p), (src : ZMod p), r.w.kN, r.w.vN]] := by
      obtain ⟨pre, w⟩ := r; simp only at hpre; subst hpre; cases b <;> rfl
    have h1 := served hA hr hcp hn1 (by rw [hc]; exact List.mem_singleton_self _)
    have h2 := Hn_prov hA hr (c := c) (n := ctr) (by rw [hpre]; cases b <;> rfl)
    have hp : provHW r = if b then (r.w.kR, r.w.vR) else (r.w.kL, r.w.vL) := by
      obtain ⟨pre, w⟩ := r; simp only at hpre; subst hpre; cases b <;> rfl
    have hsrc : lookC den rows c src = .cell A B := by simp [lookC, h1, hN]
    have hctr : den (Hn rows c ctr) = some (if b then B else A) := by
      rw [h2, hp]; cases b <;> simp [hA', hB']
    have hlc : lookC den rows c ctr = if b then B else A := by simp [lookC, hctr]
    refine ⟨?_, fun h => absurd h (List.cons_ne_nil _ _), fun _ => ?_⟩
    · rw [hsrc]; simp only [followPath]; rw [← hlc]; exact ih.1
    · by_cases hbs : bs = []
      · exact ⟨_, by rw [ih.2.1 hbs, hctr]⟩
      · exact ih.2.2 hbs

/-- Ops that can be a body root (`Ex`'s constructors). -/
def opBody : JOp → Bool
  | .var _ _ | .const _ | .add | .mul | .pair | .nth _ => true
  | _ => false

theorem root_node (T : Tpl) : ∃ nd ∈ nodesOf T, nd.id = 0 ∧ opBody nd.op = true := by
  obtain ⟨k, ax, inTy, outTy, body⟩ := T
  cases body <;> exact ⟨_, List.mem_append_left _ (List.mem_cons_self ..), rfl, rfl⟩

theorem look_atom {den : ZMod p × ZMod p → Option Noun} (hM : MemoryBB R rows den) {c n : ℕ}
    {v : ZMod p} (h : Hn rows c n = (((0 : ℕ) : ZMod p), v)) : lookC den rows c n = .atom v.val := by
  simp [lookC, h, hM.den0]

/-- **One node**: its rows force J-3a's local constraint and genuine read on the served values. -/
theorem node_ok (hA : Accepted R regs ids rows) {den : ZMod p × ZMod p → Option Noun}
    (hM : MemoryBB R rows den) {c S : ℕ} (hcp : c < p) {s : Noun}
    (hs : den (Hn rows c S) = some s) (nd : JNode)
    (hax : (match nd.op with | .var _ a => decide (0 < a) | _ => true) = true)
    (ctr : ℕ) (hsub : ∀ q ∈ nodePre c S ctr nd, q ∈ layoutJ8 R regs ids) :
    localOK p nd.op (lookC den rows c nd.id) (lookC den rows c nd.a) (lookC den rows c nd.b) = true ∧
    readOK s nd.op (lookC den rows c nd.id) (lookC den rows c nd.a) (lookC den rows c nd.b) = true ∧
    (opBody nd.op = true → ∃ y, den (Hn rows c nd.id) = some y) := by
  have hlS : lookC den rows c S = s := by simp [lookC, hs]
  obtain ⟨id, op, a, b⟩ := nd
  cases op with
  | var j ax =>
    have hax' : 0 < ax := of_decide_eq_true hax
    obtain ⟨h1, h2, h3⟩ := chain_ok (dst := id) hA hM hcp (axPath ax) S ctr hsub
    refine ⟨rfl, ?_, fun _ => ?_⟩
    · simp only [readOK, decide_eq_true_eq]; rw [slot_axPath s hax', ← hlS]; exact h1
    · by_cases he : axPath ax = []
      · exact ⟨s, by rw [h2 he, hs]⟩
      · exact h3 he
  | nth j =>
    obtain ⟨h1, -, h3⟩ := chain_ok (dst := id) hA hM hcp _ a ctr hsub
    refine ⟨rfl, ?_, fun _ => h3 (by simp)⟩
    simp only [readOK, decide_eq_true_eq]; rw [nthO_path]; exact h1
  | tlN n =>
    obtain ⟨h1, -, -⟩ := chain_ok (dst := id) hA hM hcp _ a ctr hsub
    refine ⟨rfl, ?_, fun h => by simp [opBody] at h⟩
    simp only [readOK, decide_eq_true_eq]; rw [tailO_path]; exact h1
  | const k =>
    obtain ⟨r, hr, hpre⟩ := real hA (hsub ⟨.cst, 0, c, id, k, 0⟩ (by simp [nodePre]))
    obtain ⟨-, -, hid, hk, -⟩ := hA.small _ (pre_mem hA hr)
    rw [hpre] at hid hk
    have hv := (gate_facts r (hA.gate r hr)).1 (by rw [hpre])
    have h2 := Hn_prov hA hr (c := c) (n := id) (by rw [hpre]; rfl)
    have hp : provHW r = (((0 : ℕ) : ZMod p), r.w.val) := by
      obtain ⟨pre, w⟩ := r; simp only at hpre; subst hpre; rfl
    have hl := look_atom hM (h2.trans hp)
    refine ⟨?_, rfl, fun _ => ⟨_, by rw [h2, hp, Nat.cast_zero, hM.den0]⟩⟩
    simp only [localOK, decide_eq_true_eq, hl, hv, hpre, ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  | add =>
    obtain ⟨r, hr, hpre⟩ := real hA (hsub ⟨.add, 0, c, id, a, b⟩ (by simp [nodePre]))
    obtain ⟨-, -, hid, ha, hb⟩ := hA.small _ (pre_mem hA hr)
    rw [hpre] at hid ha hb
    have hv := (gate_facts r (hA.gate r hr)).2.1 (by rw [hpre])
    have hc : consK r = [[((1 : ℕ) : ZMod p), (c : ZMod p), (a : ZMod p), ((0 : ℕ) : ZMod p), r.w.v1],
        [((1 : ℕ) : ZMod p), (c : ZMod p), (b : ZMod p), ((0 : ℕ) : ZMod p), r.w.v2]] := by
      obtain ⟨pre, w⟩ := r; simp only at hpre; subst hpre; rfl
    have ha' := served (k := ((0 : ℕ) : ZMod p)) (v := r.w.v1) hA hr hcp ha (by rw [hc]; simp)
    have hb' := served (k := ((0 : ℕ) : ZMod p)) (v := r.w.v2) hA hr hcp hb (by rw [hc]; simp)
    have h2 := Hn_prov hA hr (c := c) (n := id) (by rw [hpre]; rfl)
    have hp : provHW r = (((0 : ℕ) : ZMod p), r.w.val) := by
      obtain ⟨pre, w⟩ := r; simp only at hpre; subst hpre; rfl
    refine ⟨?_, rfl, fun _ => ⟨_, by rw [h2, hp, Nat.cast_zero, hM.den0]⟩⟩
    simp only [localOK, decide_eq_true_eq, look_atom hM (h2.trans hp), look_atom hM ha',
      look_atom hM hb', hv, atomVal, ZMod.val_add]
  | mul =>
    obtain ⟨r, hr, hpre⟩ := real hA (hsub ⟨.mul, 0, c, id, a, b⟩ (by simp [nodePre]))
    obtain ⟨-, -, hid, ha, hb⟩ := hA.small _ (pre_mem hA hr)
    rw [hpre] at hid ha hb
    have hv := (gate_facts r (hA.gate r hr)).2.2.1 (by rw [hpre])
    have hc : consK r = [[((1 : ℕ) : ZMod p), (c : ZMod p), (a : ZMod p), ((0 : ℕ) : ZMod p), r.w.v1],
        [((1 : ℕ) : ZMod p), (c : ZMod p), (b : ZMod p), ((0 : ℕ) : ZMod p), r.w.v2]] := by
      obtain ⟨pre, w⟩ := r; simp only at hpre; subst hpre; rfl
    have ha' := served (k := ((0 : ℕ) : ZMod p)) (v := r.w.v1) hA hr hcp ha (by rw [hc]; simp)
    have hb' := served (k := ((0 : ℕ) : ZMod p)) (v := r.w.v2) hA hr hcp hb (by rw [hc]; simp)
    have h2 := Hn_prov hA hr (c := c) (n := id) (by rw [hpre]; rfl)
    have hp : provHW r = (((0 : ℕ) : ZMod p), r.w.val) := by
      obtain ⟨pre, w⟩ := r; simp only at hpre; subst hpre; rfl
    refine ⟨?_, rfl, fun _ => ⟨_, by rw [h2, hp, Nat.cast_zero, hM.den0]⟩⟩
    simp only [localOK, decide_eq_true_eq, look_atom hM (h2.trans hp), look_atom hM ha',
      look_atom hM hb', hv, atomVal, ZMod.val_mul]
  | pair =>
    obtain ⟨r, hr, hpre⟩ := real hA (hsub ⟨.rp, 0, c, id, a, b⟩ (by simp [nodePre]))
    obtain ⟨-, -, hid, ha, hb⟩ := hA.small _ (pre_mem hA hr)
    rw [hpre] at hid ha hb
    obtain ⟨A, B, hA', hB', hN⟩ := rd_facts hA hM hr (by rw [hpre]; simp)
    have hc : consK r = [[((1 : ℕ) : ZMod p), (c : ZMod p), (a : ZMod p), r.w.kL, r.w.vL],
        [((1 : ℕ) : ZMod p), (c : ZMod p), (b : ZMod p), r.w.kR, r.w.vR]] := by
      obtain ⟨pre, w⟩ := r; simp only at hpre; subst hpre; rfl
    have ha' := served (k := r.w.kL) (v := r.w.vL) hA hr hcp ha (by rw [hc]; simp)
    have hb' := served (k := r.w.kR) (v := r.w.vR) hA hr hcp hb (by rw [hc]; simp)
    have h2 := Hn_prov hA hr (c := c) (n := id) (by rw [hpre]; rfl)
    have hp : provHW r = (r.w.kN, r.w.vN) := by
      obtain ⟨pre, w⟩ := r; simp only at hpre; subst hpre; rfl
    refine ⟨rfl, ?_, fun _ => ⟨_, by rw [h2, hp, hN]⟩⟩
    simp [readOK, lookC, h2, hp, hN, ha', hb', hA', hB']
  | isF =>
    obtain ⟨r, hr, hpre⟩ := real hA (hsub ⟨.isf, 0, c, id, a, 0⟩ (by simp [nodePre]))
    obtain ⟨-, -, hid, ha, -⟩ := hA.small _ (pre_mem hA hr)
    rw [hpre] at hid ha
    have hc : consK r = [[((1 : ℕ) : ZMod p), (c : ZMod p), (a : ZMod p), ((0 : ℕ) : ZMod p), r.w.v1]] := by
      obtain ⟨pre, w⟩ := r; simp only at hpre; subst hpre; rfl
    have ha' := served (k := ((0 : ℕ) : ZMod p)) (v := r.w.v1) hA hr hcp ha (by rw [hc]; simp)
    have h2 := Hn_prov hA hr (c := c) (n := id) (by rw [hpre]; rfl)
    have hp : provHW r = (((0 : ℕ) : ZMod p), r.w.v1) := by
      obtain ⟨pre, w⟩ := r; simp only at hpre; subst hpre; rfl
    refine ⟨?_, rfl, fun h => by simp [opBody] at h⟩
    simp [localOK, isFieldAtom, look_atom hM (h2.trans hp), look_atom hM ha', ZMod.val_lt]
  | isNil =>
    obtain ⟨r, hr, hpre⟩ := real hA (hsub ⟨.nil, 0, c, id, a, 0⟩ (by simp [nodePre]))
    obtain ⟨-, -, hid, ha, -⟩ := hA.small _ (pre_mem hA hr)
    rw [hpre] at hid ha
    have hc : consK r =
        [[((1 : ℕ) : ZMod p), (c : ZMod p), (a : ZMod p), ((0 : ℕ) : ZMod p), ((0 : ℕ) : ZMod p)]] := by
      obtain ⟨pre, w⟩ := r; simp only at hpre; subst hpre; rfl
    have ha' := served (k := ((0 : ℕ) : ZMod p)) (v := ((0 : ℕ) : ZMod p)) hA hr hcp ha (by rw [hc]; simp)
    have h2 := Hn_prov hA hr (c := c) (n := id) (by rw [hpre]; rfl)
    have hp : provHW r = (((0 : ℕ) : ZMod p), ((0 : ℕ) : ZMod p)) := by
      obtain ⟨pre, w⟩ := r; simp only at hpre; subst hpre; rfl
    refine ⟨?_, rfl, fun h => by simp [opBody] at h⟩
    simp [localOK, look_atom hM (h2.trans hp), look_atom hM ha']

/-- **`jetChip_sound`** (J-3b).  On rows accepted by the J chip (`Accepted`: layout, base gates, the
in-chip balance in existence form) with memory as a black box (`MemoryBB`), for call `c` of template
`R i` whose call row carries the handles `h_c = (kN, vN)`, `h_S = (kL, vL)`, `h_E = (kR, vR)` with
`h_S` denoting `s`: `h_c` denotes `compile p (R i)`, and there is a J-3a table for call `c` with the
canonical skeleton (`nodesOf`), `LocalOK`, `NodeLookupSound`, `ReadsGenuine s`, whose output row's
value is what `h_E` denotes. -/
theorem jetChip_sound (R : ℕ → Tpl) (regs ids : List ℕ) (rows : List (CRow (ZMod p)))
    (den : ZMod p × ZMod p → Option Noun) (hA : Accepted R regs ids rows) (hM : MemoryBB R rows den)
    (c i : ℕ) (hc : ids[c]? = some i) (hax : axPosB (R i) = true)
    (rc : CRow (ZMod p)) (hrc : rc ∈ rows) (hpre : rc.pre = callPre R c i)
    (s : Noun) (hs : den (rc.w.kL, rc.w.vL) = some s) :
    den (rc.w.kN, rc.w.vN) = some (compile p (R i)) ∧
    ∃ t : JTable, callRows t c = t ∧ t.map JRow.node = nodesOf (R i) ∧ (∀ r ∈ t, LocalOK p r) ∧
      NodeLookupSound t ∧ ReadsGenuine s t ∧
      ∃ out ∈ t, out.node.id = 0 ∧ den (rc.w.kR, rc.w.vR) = some out.val := by
  have hblk : ∀ q ∈ blockPre R c i, q ∈ layoutJ8 R regs ids := fun q hq =>
    List.mem_append_right _ (mem_blocks R ids 0 c i hc q (by simpa using hq))
  obtain ⟨hip, hcp, -, -, hNp⟩ := hA.small _ (pre_mem hA hrc)
  obtain ⟨pre, w⟩ := rc
  simp only at hpre hs hip hcp hNp ⊢
  subst hpre
  simp only [callPre] at hip hcp hNp
  have hcons : consK (⟨callPre R c i, w⟩ : CRow (ZMod p)) =
      [[((2 : ℕ) : ZMod p), (i : ZMod p), w.kN, w.vN],
        [((1 : ℕ) : ZMod p), (c : ZMod p), ((0 : ℕ) : ZMod p), w.kR, w.vR]] :=
    consK_call (F := ZMod p) i c (nodesOf (R i)).length w
  -- the registry claim binding
  have hreg : den (w.kN, w.vN) = some (compile p (R i)) := by
    obtain ⟨r', hr', hκ⟩ := hA.bal _ hrc [((2 : ℕ) : ZMod p), (i : ZMod p), w.kN, w.vN]
      (by rw [hcons]; exact List.mem_cons_self ..)
    by_cases hk : r'.pre.kd = .reg
    · rw [provK_reg r' hk] at hκ
      simp only [List.mem_singleton, List.cons.injEq] at hκ
      obtain ⟨-, h1, h2, h3, -⟩ := hκ
      have hid := (hA.small _ (pre_mem hA hr')).1
      have e := natCast_inj_lt hip hid h1
      have := hM.reg r' hr' hk
      rw [← e, ← h2, ← h3] at this; exact this
    · rw [provK_eq r' hk] at hκ; simp at hκ
  refine ⟨hreg, ?_⟩
  set N := (nodesOf (R i)).length
  have hS : Hn rows c N = (w.kL, w.vL) := Hn_prov hA hrc (by rfl)
  have hsS : den (Hn rows c N) = some s := by rw [hS]; exact hs
  have hout : Hn rows c 0 = (w.kR, w.vR) :=
    served (k := w.kR) (v := w.vR) hA hrc hcp (Fact.out : p.Prime).pos (by rw [hcons]; simp)
  have hnode : ∀ nd ∈ nodesOf (R i),
      localOK p nd.op (lookC den rows c nd.id) (lookC den rows c nd.a) (lookC den rows c nd.b) = true ∧
      readOK s nd.op (lookC den rows c nd.id) (lookC den rows c nd.a) (lookC den rows c nd.b) = true ∧
      (opBody nd.op = true → ∃ y, den (Hn rows c nd.id) = some y) := by
    intro nd hnd
    obtain ⟨ctr, hctr⟩ := mem_nodesPre c N (nodesOf (R i)) (N + 1) nd hnd
    exact node_ok hA hM hcp hsS nd (List.all_eq_true.1 hax nd hnd) ctr
      (fun q hq => hblk q (List.mem_cons_of_mem _ (hctr q hq)))
  let look := lookC den rows c
  refine ⟨(nodesOf (R i)).map fun nd => ⟨nd, c, look nd.id, look nd.a, look nd.b⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.filter_eq_self.2 fun r hr => by obtain ⟨nd, -, rfl⟩ := List.mem_map.1 hr; simp
  · rw [List.map_map]; exact List.map_id'' (fun _ => rfl) _
  · intro r hr; obtain ⟨nd, hnd, rfl⟩ := List.mem_map.1 hr; exact (hnode nd hnd).1
  · refine ⟨look, fun r hr => ?_, fun r hr => ?_⟩
    · obtain ⟨nd, -, rfl⟩ := List.mem_map.1 hr; rfl
    · obtain ⟨nd, -, rfl⟩ := List.mem_map.1 hr; exact ⟨fun _ => rfl, fun _ => rfl⟩
  · intro r hr; obtain ⟨nd, hnd, rfl⟩ := List.mem_map.1 hr; exact (hnode nd hnd).2.1
  · obtain ⟨nd0, hnd0, hid0, hb0⟩ := root_node (R i)
    obtain ⟨y, hy⟩ := (hnode nd0 hnd0).2.2 hb0
    refine ⟨_, List.mem_map_of_mem hnd0, hid0, ?_⟩
    rw [hid0, hout] at hy
    show _ = some (lookC den rows c nd0.id)
    rw [hy]; simp [lookC, hid0, hout, hy]

/-- **`jetChip_holds`**: the call's output handle denotes `T.sem p s`, and `HoldsN ⟨s, compile p T, e⟩`
(J-3a's `interp_sound`, then J-2's `compile_rel_iff_holdsN`). -/
theorem jetChip_holds (R : ℕ → Tpl) (regs ids : List ℕ) (rows : List (CRow (ZMod p)))
    (den : ZMod p × ZMod p → Option Noun) (hA : Accepted R regs ids rows) (hM : MemoryBB R rows den)
    (c i : ℕ) (hc : ids[c]? = some i) (hax : axPosB (R i) = true) (hT : (R i).WellTyped p)
    (rc : CRow (ZMod p)) (hrc : rc ∈ rows) (hpre : rc.pre = callPre R c i)
    (s : Noun) (hs : den (rc.w.kL, rc.w.vL) = some s) :
    den (rc.w.kN, rc.w.vN) = some (compile p (R i)) ∧
    ∃ e, den (rc.w.kR, rc.w.vR) = some e ∧ (R i).sem p s = some e ∧
      HoldsN ⟨s, compile p (R i), e⟩ := by
  obtain ⟨hreg, t, hct, hsk, hloc, hlk, hrd, out, hout, hid, hE⟩ :=
    jetChip_sound R regs ids rows den hA hM c i hc hax rc hrc hpre s hs
  rw [← hct] at hsk hloc hlk hrd hout
  exact ⟨hreg, out.val, hE, interp_sound (Fact.out : p.Prime).pos (R i) hT s t c hsk hloc hlk hrd out
    hout hid⟩

end SoundP

end Nock.Jet.ChipJ8
