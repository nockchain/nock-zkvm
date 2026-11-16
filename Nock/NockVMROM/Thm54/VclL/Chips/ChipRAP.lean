/-
  Nock/NockVMROM/Thm54/VclL/Chips/ChipRAP.lean

  Built through `MonolithicRAP.expandChip` (the deployed chips' constructor), so the
  `Def:RAP` degree field `C_deg` (every coordinate constraint has total degree `≤ 4`) is a THEOREM
  discharged from the template's per-gate degree proofs, which are checked here by evaluation
  (`cellBase_deg`, `cellMixed_deg`, `pathBase_deg`, `pathMixed_deg`).

  **𝕂′ in gates.**  `𝕂′ = 𝕂(√δ)` with `δ = algebraMap 𝔽 𝕂 δF` (a base non-square; it stays a
  non-square in the odd-degree `𝕂`, `T0Tower.nonsquare_lift`).  A `𝕂′` quantity is a pair of `𝕂`-valued
  `MixedExpr`s (`QE`, Re/Im on two consecutive `𝕂`-roles); `QE.mul` is `Quad.mk_mul`'s formula
  (`(a₀b₀ + δ a₁b₁, a₀b₁ + a₁b₀)`); a `𝕂′` equation is two `𝕂`-gates, each expanded to `e = 3`
  base gates by the coordinate compiler.  Coins are `MixedExpr` challenge leaves at the `frameVCL`
  index (`z′ = (χ₂, χ₃)`, `γ′ = (χ₄, χ₆)`, `ρ′ = (χ₅, χ₇)`); `slotVal` supplies their
  coordinates at the compiler's slots.

  **Cell table** (memory table 0; columns as `Layout.Cell` / `IOField.Cell.widthT`): base
  `128` (round 0), `18` `𝕂`-roles (round 1: `p l r`, role `6k + 2c + ri`), `12` `𝕂`-roles (round 2:
  validity provide / consume-L / consume-R / export provide inverses, validity and export
  accumulators).  Base gates (`123`): serial `isFirst·idx`, `(1−isLast)(idx′ − idx − 1)`; rank limbs
  `lo + 2^62 carry − loL − loR − 1`, `hi − hiL − hiR − carry`; booleanity of `carry wL wR` and the
  `110` rank bits; the two bit decompositions; the atom-limb pins `(1−wX)·loX`, `(1−wX)·hiX`.  Mixed
  gates (`38` `𝕂`-gates = `19` `𝕂′` equations): cons size / leaf / `z`-cleared dyck
  (`Table.RowOK.cons` times `z`); the two atom gates `(1 − wX)(X − atomFP z′ aX)`; the four LogUp
  inverse gates `inv·den − 1` (providers) / `inv·den − wX` (consumers), `den = ρ′ + RLC′(key)` at
  the `𝕂′`-entry keys `(fp′ p, lo + hi√δ, idx)` (`5`) and `(fp′ p, fp′ l, fp′ r, idx)` (`10`); the
  two accumulators' init / step / terminal, the weighted provider terms `mv·inv`, `mx·inv` (`mv`,
  `mx` unbounded `𝔽` B0 columns), terminals at the publics (validity: `ρ_V`; export: `ρ_X + y`, the
  path chip's export terminal `y` sent after the coins).  `s = 123 + 3·38 = 237`.
  Base `129`, `𝕂`-roles `0 / 18 / 14`: `w = 129 + 32·3 = 225`, `22` `𝕂′` equations,
  `s = 123 + 3·44 = 255`, `d = 4`.  The γ′ powers read leaves `11 … 32` (`i < 11`).

  **Path chip** (memory table 1): base `16`, `24` `𝕂`-roles (round 1: `root p l r`), `8` (round 2:
  export consume inverse, path provide inverse, export and path accumulators).  Mixed (`34`): `first·(root − p)`,
  `(1 − last)(root′ − root)`, `(1 − last)(p′ − l − side(r − l))` (`Chain.childOf`); the export consume
  inverse `inv·den(p, l, r, cellIdx) − 1`, the path provide inverse `last·(inv·den(root, child, acc,
  rootIdx) − 1)`; the two accumulators (export consumption terminal `y`; path terminal `ρ_P`).

  What is NOT here: the bridge from chip satisfaction to `Table.TableAccepts` / `Chain` (the
  instance's `response_sound`), honest acceptance, `vclMemFamily`.
-/
import Nock.NockVMROM.Thm54.CoordinateRAPCore
import Nock.Framework.EndpointMasks
import Nock.NockVMROM.Thm54.VclL.Chips.IOField

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Module
open scoped Polynomial

noncomputable section

variable {F : Type} [Field F]

/-! ## 1. Expression helpers -/

/-- Current-row base column. -/
abbrev cv (j : ℕ) : CoeffExpr F := .var .traceCur j
/-- Next-row base column. -/
abbrev nv (j : ℕ) : CoeffExpr F := .var .traceNext j
abbrev cst (c : F) : CoeffExpr F := .const c
/-- `1 − g`. -/
abbrev notE (g : CoeffExpr F) : CoeffExpr F := .sub (.const 1) g
/-- Booleanity `g·(g − 1)`. -/
abbrev boolE (g : CoeffExpr F) : CoeffExpr F := .mul g (.sub g (.const 1))
/-- `Σ_{i<n} 2^i · col (base + i)`. -/
def bitSum (base n : ℕ) : CoeffExpr F :=
  CoeffExpr.sumList (List.range n) fun i => .mul (.const ((2 : F) ^ i)) (cv (base + i))

/-- A `𝕂′` expression: Re/Im as two `𝕂`-valued mixed expressions. -/
structure QE (F : Type) where
  re : MixedExpr F
  im : MixedExpr F

namespace QE
/-- A `𝕂′` column: `𝕂`-roles `r` (Re) and `r + 1` (Im), current row. -/
def var (r : ℕ) : QE F := ⟨.Var .traceCur r, .Var .traceCur (r + 1)⟩
def next (r : ℕ) : QE F := ⟨.Var .traceNext r, .Var .traceNext (r + 1)⟩
/-- A `𝕂′` coin `χ i + χ j·√δ`. -/
def chal (i j : ℕ) : QE F := ⟨.Var .challenge i, .Var .challenge j⟩
/-- A `𝕂′` public at `𝕂`-public slots `i`, `i + 1`. -/
def pub (i : ℕ) : QE F := ⟨.Var .publicVal i, .Var .publicVal (i + 1)⟩
/-- A lifted base-field expression. -/
def base (g : CoeffExpr F) : QE F := ⟨.Lift g, .Const 0⟩
/-- `g + h·√δ` from two base-field expressions. -/
def mk2 (g h : CoeffExpr F) : QE F := ⟨.Lift g, .Lift h⟩
def zero : QE F := ⟨.Const 0, .Const 0⟩
def one : QE F := ⟨.Const 1, .Const 0⟩
def add (a b : QE F) : QE F := ⟨.Add a.re b.re, .Add a.im b.im⟩
def sub (a b : QE F) : QE F := ⟨.Sub a.re b.re, .Sub a.im b.im⟩
/-- `Quad.mk_mul`: `(a₀b₀ + δ a₁b₁, a₀b₁ + a₁b₀)`, `δ = algebraMap δF`. -/
def mul (δF : F) (a b : QE F) : QE F :=
  ⟨.Add (.Mul a.re b.re) (.Scale (.const δF) (.Mul a.im b.im)), .Add (.Mul a.re b.im) (.Mul a.im b.re)⟩
/-- A base-field scalar times a `𝕂′` expression. -/
def scale (g : CoeffExpr F) (a : QE F) : QE F := ⟨.Scale g a.re, .Scale g a.im⟩
/-- The two `𝕂`-gates of a `𝕂′` equation `a = 0`. -/
def gates (a : QE F) : List (MixedExpr F) := [a.re, a.im]
/-- The verifier-computed power `γ′^i`, read at the challenge leaves `11 + 2i` (Re), `12 + 2i` (Im)
(the chip's challenge vector carries the powers of the coin, as the deployed chips' `chalVal` does). -/
def gpow (i : ℕ) : QE F := ⟨.Var .challenge (11 + 2 * i), .Var .challenge (12 + 2 * i)⟩
/-- `RLC′ = Σ γ′^i e_i`, flat (each term degree `deg e_i`). -/
def rlc (δF : F) (es : List (QE F)) : QE F :=
  (es.zipIdx).foldr (fun ei acc => add (mul δF (gpow ei.2) ei.1) acc) zero
end QE

/-- A `𝕂′` fingerprint at `𝕂`-roles `r.. r + 5` (size, dyck, leaf; Re/Im). -/
structure QFP (F : Type) where
  size : QE F
  dyck : QE F
  leaf : QE F

namespace QFP
def var (r : ℕ) : QFP F := ⟨QE.var r, QE.var (r + 2), QE.var (r + 4)⟩
def next (r : ℕ) : QFP F := ⟨QE.next r, QE.next (r + 2), QE.next (r + 4)⟩
def entries (x : QFP F) : List (QE F) := [x.size, x.dyck, x.leaf]
def sub (x y : QFP F) : QFP F := ⟨QE.sub x.size y.size, QE.sub x.dyck y.dyck, QE.sub x.leaf y.leaf⟩
def add (x y : QFP F) : QFP F := ⟨QE.add x.size y.size, QE.add x.dyck y.dyck, QE.add x.leaf y.leaf⟩
def scale (g : CoeffExpr F) (x : QFP F) : QFP F := ⟨QE.scale g x.size, QE.scale g x.dyck, QE.scale g x.leaf⟩
def gates (x : QFP F) : List (MixedExpr F) := x.size.gates ++ x.dyck.gates ++ x.leaf.gates
end QFP

/-- The seed `z′ = χ₂ + χ₃√δ`. -/
def zQ : QE F := QE.chal 2 3
/-- The LogUp pole `ρ′ = χ₅ + χ₇√δ` (`ioSpecVCL`); `γ′ = χ₄ + χ₆√δ` enters through its powers
`QE.gpow`. -/
def rQ : QE F := QE.chal 5 7

/-- `den = ρ′ + RLC′(entries)` (`FiniteIO.compress`). -/
def den (δF : F) (es : List (QE F)) : QE F := QE.add rQ (QE.rlc δF es)

/-! ## 2. The cell table -/

namespace Cell

-- base columns (`Layout.Cell.b0Pos`)
def isF : ℕ := 0
def isL : ℕ := 1
def idx : ℕ := 2
def idL : ℕ := 3
def idR : ℕ := 4
def wL : ℕ := 5
def wR : ℕ := 6
def aL : ℕ := 7
def aR : ℕ := 8
def lo : ℕ := 9
def hi : ℕ := 10
def loL : ℕ := 11
def hiL : ℕ := 12
def loR : ℕ := 13
def hiR : ℕ := 14
def carry : ℕ := 15
def mv : ℕ := 16
def mx : ℕ := 17
def bit0 : ℕ := 18
/-- The side-1 export multiplicity, appended after the
`110` rank bits. -/
def mx1 : ℕ := 128

-- `𝕂`-roles: `p l r` at `0 / 6 / 12`; B2 at `18 …`
def pR : ℕ := 0
def lR : ℕ := 6
def rR : ℕ := 12
def vProvInv : ℕ := 18
def consLInv : ℕ := 20
def consRInv : ℕ := 22
def xProvInv : ℕ := 24
def vAcc : ℕ := 26
def xAcc : ℕ := 28
/-- R-V2c : the side-1 export provider inverse. -/
def xProvInv1 : ℕ := 30

/-- **The cell table's base-field gates** (`123`). -/
def baseGates : List (CoeffExpr F) :=
  [ .mul (cv isF) (cv idx),
    .mul (notE (cv isL)) (.sub (.sub (nv idx) (cv idx)) (.const 1)),
    .sub (.add (cv lo) (.mul (.const ((2 : F) ^ 62)) (cv carry)))
      (.add (.add (cv loL) (cv loR)) (.const 1)),
    .sub (cv hi) (.add (.add (cv hiL) (cv hiR)) (cv carry)),
    boolE (cv carry), boolE (cv wL), boolE (cv wR),
    .sub (cv lo) (bitSum bit0 62),
    .sub (cv hi) (bitSum (bit0 + 62) 48),
    .mul (notE (cv wL)) (cv loL), .mul (notE (cv wL)) (cv hiL),
    .mul (notE (cv wR)) (cv loR), .mul (notE (cv wR)) (cv hiR) ] ++
  (List.range 110).map fun i => boolE (cv (bit0 + i))

/-- The validity key `(fp′ p, lo + hi√δ, idx)` of the row (`5` entries). -/
def vKeyP : List (QE F) := (QFP.var pR).entries ++ [QE.mk2 (cv lo) (cv hi), QE.base (cv idx)]
/-- The consumed child keys. -/
def vKeyL : List (QE F) := (QFP.var lR).entries ++ [QE.mk2 (cv loL) (cv hiL), QE.base (cv idL)]
def vKeyR : List (QE F) := (QFP.var rR).entries ++ [QE.mk2 (cv loR) (cv hiR), QE.base (cv idR)]
/-- The export key `(fp′ p, fp′ l, fp′ r, idx)` (`10` entries). -/
def xKey : List (QE F) :=
  (QFP.var pR).entries ++ (QFP.var lR).entries ++ (QFP.var rR).entries ++ [QE.base (cv idx)]

/-- **** the export record of side `s`
`(fp′ p, fp′ l, fp′ r, idx, s)` (`11` entries); side `0` exports the left child (axis `2`), side `1`
the right child (axis `3`). -/
def xKeyS (s : F) : List (QE F) := xKey ++ [QE.base (cst s)]

/-- The validity accumulator's row term `mv·inv_v − inv_L − inv_R` (current or next row). -/
def vTerm (cur : Bool) : QE F :=
  let col : ℕ → CoeffExpr F := if cur then cv else nv
  let q : ℕ → QE F := if cur then QE.var else QE.next
  QE.sub (QE.sub (QE.scale (col mv) (q vProvInv)) (q consLInv)) (q consRInv)
def xTerm (cur : Bool) : QE F :=
  if cur then QE.add (QE.scale (cv mx) (QE.var xProvInv)) (QE.scale (cv mx1) (QE.var xProvInv1))
  else QE.add (QE.scale (nv mx) (QE.next xProvInv)) (QE.scale (nv mx1) (QE.next xProvInv1))

/-- The `𝕂′` cons, `z`-cleared (`FP.cons` times `z`): size, leaf, dyck. -/
def consEqs (δF : F) : List (QE F) :=
  let p := QFP.var pR; let l := QFP.var lR; let r := QFP.var rR
  let m := QE.mul δF
  [ QE.sub p.size (m l.size r.size),
    QE.sub p.leaf (QE.add l.leaf (m l.size r.leaf)),
    QE.sub (m zQ p.dyck)
      (QE.add (QE.add (m (m zQ zQ) l.dyck) (m l.size l.size)) (m (m zQ (m l.size l.size)) r.dyck)) ]

/-- The atom gate `(1 − w)(X − atomFP z′ a)` coordinatewise. -/
def atomEqs (w a xr : ℕ) : List (QE F) :=
  let x := QFP.var xr
  [ QE.scale (notE (cv w)) (QE.sub x.size zQ),
    QE.scale (notE (cv w)) x.dyck,
    QE.scale (notE (cv w)) (QE.sub x.leaf (QE.base (cv a))) ]

def qEqs (δF : F) : List (QE F) :=
  consEqs δF ++ atomEqs wL aL lR ++ atomEqs wR aR rR ++
  [ QE.sub (QE.mul δF (QE.var vProvInv) (den δF vKeyP)) QE.one,
    QE.sub (QE.mul δF (QE.var consLInv) (den δF vKeyL)) (QE.base (cv wL)),
    QE.sub (QE.mul δF (QE.var consRInv) (den δF vKeyR)) (QE.base (cv wR)),
    -- A zero-weight child's inverse is `0` even when its
    -- key hits the pole (`Batch1795.consumer_gate_free_inv`)
    QE.scale (notE (cv wL)) (QE.var consLInv),
    QE.scale (notE (cv wR)) (QE.var consRInv),
    QE.sub (QE.mul δF (QE.var xProvInv) (den δF (xKeyS 0))) QE.one,
    QE.sub (QE.mul δF (QE.var xProvInv1) (den δF (xKeyS 1))) QE.one,
    -- validity accumulator: init, step, terminal (public `0`)
    QE.scale (cv isF) (QE.sub (QE.var vAcc) (vTerm true)),
    QE.scale (notE (cv isL)) (QE.sub (QE.sub (QE.next vAcc) (QE.var vAcc)) (vTerm false)),
    QE.scale (cv isL) (QE.sub (QE.var vAcc) (QE.pub 0)),
    -- export accumulator (public `2`)
    QE.scale (cv isF) (QE.sub (QE.var xAcc) (xTerm true)),
    QE.scale (notE (cv isL)) (QE.sub (QE.sub (QE.next xAcc) (QE.var xAcc)) (xTerm false)),
    QE.scale (cv isL) (QE.sub (QE.var xAcc) (QE.pub 2)) ]

def mixedGates (δF : F) : List (MixedExpr F) := (qEqs δF).flatMap QE.gates

end Cell

/-! ## 3. The path chip -/

namespace Path

def isF : ℕ := 0
def isL : ℕ := 1
def side : ℕ := 2
def first : ℕ := 3
def last : ℕ := 4
def len : ℕ := 5
def acc : ℕ := 6
def m : ℕ := 7
def cellIdx : ℕ := 8
def rootIdx : ℕ := 9
def bit0 : ℕ := 10

def rootR : ℕ := 0
def pR : ℕ := 6
def lR : ℕ := 12
def rR : ℕ := 18
def xConsInv : ℕ := 24
def pProvInv : ℕ := 26
def xAcc : ℕ := 28
def pAcc : ℕ := 30

/-- **The path chip's base-field gates** (`20`). -/
def baseGates : List (CoeffExpr F) :=
  [ boolE (cv side), boolE (cv first), boolE (cv last),
    .mul (cv isF) (.sub (cv first) (.const 1)),
    .mul (cv isL) (.sub (cv last) (.const 1)),
    .mul (notE (cv isL)) (.sub (nv first) (cv last)),
    .mul (cv first) (.sub (cv len) (.const 1)),
    .mul (notE (cv last)) (.sub (.sub (nv len) (cv len)) (.const 1)),
    .mul (cv first) (.sub (.sub (cv acc) (.const 2)) (cv side)),
    .mul (notE (cv last)) (.sub (.sub (nv acc) (.mul (.const 2) (cv acc))) (nv side)),
    .mul (cv first) (.sub (cv rootIdx) (cv cellIdx)),
    .mul (notE (cv last)) (.sub (nv rootIdx) (cv rootIdx)),
    .mul (cv last) (.sub (.add (cv len) (bitSum bit0 6)) (.const 62)),
    .mul (notE (cv last)) (cv m) ] ++
  (List.range 6).map fun i => boolE (cv (bit0 + i))

/-- The edge's child `l + side·(r − l)`. -/
def child : QFP F := QFP.add (QFP.var lR) (QFP.scale (cv side) (QFP.sub (QFP.var rR) (QFP.var lR)))

def xKey : List (QE F) :=
  (QFP.var pR).entries ++ (QFP.var lR).entries ++ (QFP.var rR).entries ++ [QE.base (cv cellIdx)] ++
    [QE.base (cv side)]
/-- The provided path record `(root, child, acc, rootIdx)` (`8` entries). -/
def pRec : List (QE F) :=
  (QFP.var rootR).entries ++ (child (F := F)).entries ++ [QE.base (cv acc), QE.base (cv rootIdx)]

/-- **The path chip's `𝕂′` equations** (`17`). -/
def qEqs (δF : F) : List (QE F) :=
  let root := QFP.var rootR; let p := QFP.var pR
  let fpEq (x : QFP F) : List (QE F) := x.entries
  fpEq (QFP.scale (cv first) (QFP.sub root p)) ++
  fpEq (QFP.scale (notE (cv last)) (QFP.sub (QFP.next rootR) root)) ++
  fpEq (QFP.scale (notE (cv last)) (QFP.sub (QFP.next pR) child)) ++
  [ QE.sub (QE.mul δF (QE.var xConsInv) (den δF xKey)) QE.one,
    QE.scale (cv last) (QE.sub (QE.mul δF (QE.var pProvInv) (den δF pRec)) QE.one),
    QE.scale (cv isF) (QE.sub (QE.var xAcc) (QE.var xConsInv)),
    QE.scale (notE (cv isL)) (QE.sub (QE.sub (QE.next xAcc) (QE.var xAcc)) (QE.next xConsInv)),
    QE.scale (cv isL) (QE.sub (QE.var xAcc) (QE.pub 0)),
    QE.scale (cv isF) (QE.sub (QE.var pAcc) (QE.scale (cv m) (QE.var pProvInv))),
    QE.scale (notE (cv isL))
      (QE.sub (QE.sub (QE.next pAcc) (QE.var pAcc)) (QE.scale (nv m) (QE.next pProvInv))),
    QE.scale (cv isL) (QE.sub (QE.var pAcc) (QE.pub 2)) ]

def mixedGates (δF : F) : List (MixedExpr F) := (qEqs δF).flatMap QE.gates

end Path

/-! ## 4. Degrees, checked by evaluation -/

theorem sumList_degree_le (l : List ℕ) (f : ℕ → CoeffExpr F) (d : ℕ)
    (h : ∀ i ∈ l, (f i).degree ≤ d) : (CoeffExpr.sumList l f).degree ≤ d := by
  induction l with
  | nil => simp [CoeffExpr.sumList, CoeffExpr.degree]
  | cons a t ih =>
    simp only [CoeffExpr.sumList, List.foldr_cons, CoeffExpr.degree] at ih ⊢
    exact max_le (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

theorem bitSum_degree_le1 (base n : ℕ) : (bitSum (F := F) base n).degree ≤ 1 :=
  sumList_degree_le _ _ _ fun i _ => by simp [CoeffExpr.degree]

theorem bitSum_degree_le4 (base n : ℕ) : (bitSum (F := F) base n).degree ≤ 4 :=
  (bitSum_degree_le1 base n).trans (by norm_num)

theorem forall_le_of_all {α : Type*} (f : α → ℕ) (l : List α) (d : ℕ)
    (h : (l.map f).all (fun n => decide (n ≤ d)) = true) : ∀ g ∈ l, f g ≤ d := by
  intro g hg
  have := List.all_eq_true.mp h (f g) (List.mem_map_of_mem hg)
  simpa using this

theorem cellBase_deg_all : ((Cell.baseGates (F := F)).map CoeffExpr.degree).all (fun n => decide (n ≤ 4)) = true := by
  simp [Cell.baseGates, Cell.mixedGates, Cell.qEqs, Cell.consEqs, Cell.atomEqs, Cell.vKeyP, Cell.vKeyL, Cell.vKeyR, Cell.xKey, Cell.xKeyS, Cell.vTerm, Cell.xTerm, QE.gates, QE.var, QE.next, QE.chal, QE.pub, QE.base, QE.mk2, QE.zero, QE.one, QE.add, QE.sub, QE.mul, QE.scale, QE.rlc, QE.gpow, QFP.var, QFP.next, QFP.entries, QFP.sub, QFP.add, QFP.scale, QFP.gates, den, zQ, rQ, bitSum_degree_le4, MixedExpr.degree, CoeffExpr.degree, List.zipIdx]
theorem cellMixed_deg_all (δF : F) :
    ((Cell.mixedGates δF).map MixedExpr.degree).all (fun n => decide (n ≤ 4)) = true := by
  simp [Cell.baseGates, Cell.mixedGates, Cell.qEqs, Cell.consEqs, Cell.atomEqs, Cell.vKeyP, Cell.vKeyL, Cell.vKeyR, Cell.xKey, Cell.xKeyS, Cell.vTerm, Cell.xTerm, QE.gates, QE.var, QE.next, QE.chal, QE.pub, QE.base, QE.mk2, QE.zero, QE.one, QE.add, QE.sub, QE.mul, QE.scale, QE.rlc, QE.gpow, QFP.var, QFP.next, QFP.entries, QFP.sub, QFP.add, QFP.scale, QFP.gates, den, zQ, rQ, bitSum_degree_le4, MixedExpr.degree, CoeffExpr.degree, List.zipIdx]
theorem pathBase_deg_all : ((Path.baseGates (F := F)).map CoeffExpr.degree).all (fun n => decide (n ≤ 4)) = true := by
  simp [Path.baseGates, Path.mixedGates, Path.qEqs, Path.xKey, Path.pRec, Path.child, QE.gates, QE.var, QE.next, QE.chal, QE.pub, QE.base, QE.mk2, QE.zero, QE.one, QE.add, QE.sub, QE.mul, QE.scale, QE.rlc, QE.gpow, QFP.var, QFP.next, QFP.entries, QFP.sub, QFP.add, QFP.scale, QFP.gates, den, zQ, rQ, bitSum_degree_le4, MixedExpr.degree, CoeffExpr.degree, List.zipIdx]
  have := bitSum_degree_le1 (F := F) Path.bit0 6
  omega
theorem pathMixed_deg_all (δF : F) :
    ((Path.mixedGates δF).map MixedExpr.degree).all (fun n => decide (n ≤ 4)) = true := by
  simp [Path.baseGates, Path.mixedGates, Path.qEqs, Path.xKey, Path.pRec, Path.child, QE.gates, QE.var, QE.next, QE.chal, QE.pub, QE.base, QE.mk2, QE.zero, QE.one, QE.add, QE.sub, QE.mul, QE.scale, QE.rlc, QE.gpow, QFP.var, QFP.next, QFP.entries, QFP.sub, QFP.add, QFP.scale, QFP.gates, den, zQ, rQ, bitSum_degree_le4, MixedExpr.degree, CoeffExpr.degree, List.zipIdx]

theorem cellBase_deg : ∀ g ∈ Cell.baseGates (F := F), g.degree ≤ 4 :=
  forall_le_of_all _ _ _ cellBase_deg_all
theorem cellMixed_deg (δF : F) : ∀ g ∈ Cell.mixedGates δF, g.degree ≤ 4 :=
  forall_le_of_all _ _ _ (cellMixed_deg_all δF)
theorem pathBase_deg : ∀ g ∈ Path.baseGates (F := F), g.degree ≤ 4 :=
  forall_le_of_all _ _ _ pathBase_deg_all
theorem pathMixed_deg (δF : F) : ∀ g ∈ Path.mixedGates δF, g.degree ≤ 4 :=
  forall_le_of_all _ _ _ (pathMixed_deg_all δF)

theorem cellBase_length : (Cell.baseGates (F := F)).length = 123 := by
  simp [Cell.baseGates]
theorem cellMixed_length (δF : F) : (Cell.mixedGates δF).length = 44 := by
  simp [Cell.mixedGates, Cell.qEqs, Cell.consEqs, Cell.atomEqs, QE.gates]
theorem pathBase_length : (Path.baseGates (F := F)).length = 20 := by
  simp [Path.baseGates]
theorem pathMixed_length (δF : F) : (Path.mixedGates δF).length = 34 := by
  simp [Path.mixedGates, Path.qEqs, QFP.entries, QE.gates]

/-! ## 5. The templates and the chips -/

/-- **The cell table template**: three rounds, base `128 / 0 / 0`, `𝕂`-roles `0 / 18 / 12`. -/
def cellTemplate (δF : F) : ChipTemplate F where
  rounds := 3
  rounds_pos := by decide
  baseColsOf := ![129, 0, 0]
  extColsOf := ![0, 18, 14]
  baseTransition := Cell.baseGates
  extTransition := []
  mixedTransition := Cell.mixedGates δF
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := cellBase_deg
  extTransition_deg := by simp
  mixedTransition_deg := cellMixed_deg δF
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

/-- **The path chip template**: base `17 / 0 / 0`, `𝕂`-roles `0 / 24 / 8`. -/
def pathTemplate (δF : F) : ChipTemplate F where
  rounds := 3
  rounds_pos := by decide
  baseColsOf := ![16, 0, 0]
  extColsOf := ![0, 24, 8]
  baseTransition := Path.baseGates
  extTransition := []
  mixedTransition := Path.mixedGates δF
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := pathBase_deg
  extTransition_deg := by simp
  mixedTransition_deg := pathMixed_deg δF
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

theorem cellTemplate_baseCols (δF : F) : (cellTemplate δF).baseCols = 129 := by
  show (∑ r : Fin 3, (![129, 0, 0] : Fin 3 → ℕ) r) = 129
  decide
theorem cellTemplate_extCols (δF : F) : (cellTemplate δF).extCols = 32 := by
  show (∑ r : Fin 3, (![0, 18, 14] : Fin 3 → ℕ) r) = 32
  decide
theorem pathTemplate_baseCols (δF : F) : (pathTemplate δF).baseCols = 16 := by
  show (∑ r : Fin 3, (![16, 0, 0] : Fin 3 → ℕ) r) = 16
  decide
theorem pathTemplate_extCols (δF : F) : (pathTemplate δF).extCols = 32 := by
  show (∑ r : Fin 3, (![0, 24, 8] : Fin 3 → ℕ) r) = 32
  decide

section Chips
variable {K : Type} [Field K] [Algebra F K] [FiniteDimensional F K]

/-- The compiler's coordinate slots for `𝕂`-valued leaves: leaf `i`, coordinate `k`, at slot
`baseCols + 3 i + k` (`ChipTemplate.col0` ignores the kind).  `chals i` is coin `i` of `frameVCL`
for `i < 11` and the Re/Im of `γ′^j` at `11 + 2j`, `12 + 2j`; `pubs` are the terminal publics. -/
def slotVal (b : Basis (Fin 3) F K) (baseCols : ℕ) (v : ℕ → K) (n : ℕ) : F :=
  if baseCols ≤ n then
    coord b (v ((n - baseCols) / 3)) ⟨(n - baseCols) % 3, Nat.mod_lt _ (by norm_num)⟩
  else 0

/-- **The cell table as a `FixedPreprocessingRAP`**: `expandChip` of `cellTemplate`, the endpoint
masks `isFirst`, `isLast` fixed at columns `0`, `1` (round 0). -/
def cellChip (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) : FixedPreprocessingRAP F where
  rap := expandChip (cellTemplate δF) b (slotVal b 129 chals) (slotVal b 129 pubs) orbit (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 129 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

/-- **The path chip as a `FixedPreprocessingRAP`.** -/
def pathChip (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) : FixedPreprocessingRAP F where
  rap := expandChip (pathTemplate δF) b (slotVal b 16 chals) (slotVal b 16 pubs) orbit (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 16 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

variable (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

theorem cellChip_fingerprint :
    (cellChip δF b hn nodes orbit chals pubs).rap.w = 225 ∧
      (cellChip δF b hn nodes orbit chals pubs).rap.s = 255 ∧
      (cellChip δF b hn nodes orbit chals pubs).rap.d = 4 ∧
      (cellChip δF b hn nodes orbit chals pubs).rap.k = 3 := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · show (cellTemplate δF).baseCols + (cellTemplate δF).extCols * 3 = 225
    rw [cellTemplate_baseCols, cellTemplate_extCols]
  · rw [show (cellChip δF b hn nodes orbit chals pubs).rap = expandChip (cellTemplate δF) b _ _ orbit _ from rfl,
      expandChip_s]
    simp only [cellTemplate, cellBase_length, cellMixed_length, List.length_nil]

/-- **Path chip fingerprint**: `w = 112` (`IOField.Path.widthT`), `s = 122`, `d = 4`, `k = 3`. -/
theorem pathChip_fingerprint :
    (pathChip δF b hn nodes orbit chals pubs).rap.w = 112 ∧
      (pathChip δF b hn nodes orbit chals pubs).rap.s = 122 ∧
      (pathChip δF b hn nodes orbit chals pubs).rap.d = 4 ∧
      (pathChip δF b hn nodes orbit chals pubs).rap.k = 3 := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · show (pathTemplate δF).baseCols + (pathTemplate δF).extCols * 3 = 112
    rw [pathTemplate_baseCols, pathTemplate_extCols]
  · rw [show (pathChip δF b hn nodes orbit chals pubs).rap = expandChip (pathTemplate δF) b _ _ orbit _ from rfl,
      expandChip_s]
    simp only [pathTemplate, pathBase_length, pathMixed_length, List.length_nil]

/-- **Degree `≤ 4` at the chips**: every constraint polynomial of either chip has total degree
`≤ 4` (the `Def:RAP` field `C_deg`, discharged by `expandChip` from the per-gate checks above). -/
theorem cellChip_deg (i : Fin (cellChip δF b hn nodes orbit chals pubs).rap.s) :
    ((cellChip δF b hn nodes orbit chals pubs).rap.C i).totalDegree ≤ 4 := by
  have hd := (cellChip δF b hn nodes orbit chals pubs).rap.C_deg i
  rwa [(cellChip_fingerprint δF b hn nodes orbit chals pubs).2.2.1] at hd

theorem pathChip_deg (i : Fin (pathChip δF b hn nodes orbit chals pubs).rap.s) :
    ((pathChip δF b hn nodes orbit chals pubs).rap.C i).totalDegree ≤ 4 := by
  have hd := (pathChip δF b hn nodes orbit chals pubs).rap.C_deg i
  rwa [(pathChip_fingerprint δF b hn nodes orbit chals pubs).2.2.1] at hd

end Chips

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
