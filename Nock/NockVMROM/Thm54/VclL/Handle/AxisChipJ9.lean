/-
  Nock/NockVMROM/Thm54/VclL/Handle/AxisChipJ9.lean

  A NEW template beside the memory-side twins (`walkChipHQK`, `atomChipHQ`); no existing module is edited.

  **Layout** (MEASURED `w = 52` by `rfl`): base round 0, columns `0 .. 21`:

  | col | name | col | name |
  |---|---|---|---|
  | 0 | `isFirstT` (preprocessing) | 11 | `hr.v` |
  | 1 | `isLastT` (preprocessing)  | 12 | `hin.k` |
  | 2 | `head` | 13 | `hin.v` |
  | 3 | `cl` (chain last) | 14 | `hout.k` |
  | 4 | `z1a` | 15 | `hout.v` |
  | 5 | `route0` | 16 | `v` |
  | 6 | `R` (provider id) | 17 | `inv_g4` |
  | 7 | `pw` | 18 | `r0h` |
  | 8 | `l` | 19 | `ftk` |
  | 9 | `axK` | 20 | `ftv` |
  | 10 | `axS` | 21 | `mu` |

  `𝕂`-roles (round 2, as the handle-coin inverses of `cellTemplateHQ` / `atomTemplateHQ`), each a `𝕂′` pair:
  `invL 0/1` (limb consume), `invP 2/3` (path consume), `invT 4/5` (`TAG_ax` provide), `accS 6/7` (net service),
  `accP 8/9` (path).  `22 + 10·3 = 52`, the design's `≈ 52`.

  **Gates** = §2.1 G1–G8 verbatim (`g1 … g8` below, one list per design group, each gate the design's polynomial).
  **Design choice (binding):** the four gates no S1–S4 step consumes are KEPT (gate ledger `unconsumedGates`); of
  `(1 − cl)·mu` and the provide activity `cl·mu` exactly ONE is kept: the GATE `(1 − cl)·mu` stays (it is G8) and the
  `TAG_ax` provide activity is `mu` (not `cl·mu`).  Then the gate is consumed by S4 (a provided row has `mu ≠ 0`, so
  `cl = 1`), and three gates stay unconsumed.
  **Provider list.** The provider list `axTagProvs` keeps rows with `mu ≠ 0`, the path consumer list `axPathReqs` rows with
  `1 − z1a ≠ 0` (the `atomIncProvs` precedent, `ServiceJ8.lean`).

  **Records / coins.** Every `𝕂′` denominator is `HQ.denKeyQ` (the handle coins `γH′ = (33,35)`, `ρH′ = (34,36)`,
  the service and path classes' coins on the memory side).  Consumed (service, every row): `(R, axK, 0, l)`;
  consumed (path, activity `1 − z1a`): `(hin.v, axS, hout.k, hout.v)`; provided (service, activity `mu`):
  `(hr.v, ftk, ftv, hout.k, hout.v, R, 0, 5)`, `TAG_ax = 5` last.  Terminals: service `pubAXs = 0/1` (consumes −
  provides, the LHS of the J-9 A `hGS`), path `pubAXp = 2/3` (the LHS of `hGp`).

  **Instrument.** Serial-capable columns: `R, hr.v, hin.v, hout.v, ftv` (row indices /
  ids). Every base gate is serial-free EXCEPT the copy gates (`CopyG`, `σ·(X − Y)` with `σ` serial-free, the
  `ChipHX` `EqG` pattern extended to next-row operands) and ONE select-copy (`SelG`, G8's
  `ftv − R − route0·(v − R)`, the two-branch copy `x = a` / `x = b` under a serial-free selector). The `𝕂′` gates
  read a serial only as an RLC key entry.

  **NC (§5 (c), chip level):** `nc_drop_headCl` — on the 1-row table (`isFirstT = isLastT = 1`), the row
  `head = cl = 1`, `pw = 4`, `axK = 3` (the top-limb axis `2^2 − 1` of a 2-limb comb, so the chain drops `l_0`)
  satisfies EVERY base gate except `head·cl`, which evaluates to `1`.  LABEL: base-gate (row) level, not a full
  `rap.Satisfies` trace (the `𝕂′` LogUp gates are not exhibited).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.NounAx

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Columns -/

def isFT : ℕ := 0
def isLT : ℕ := 1
def head : ℕ := 2
def cl : ℕ := 3
def z1a : ℕ := 4
def route0 : ℕ := 5
def R : ℕ := 6
def pw : ℕ := 7
def l : ℕ := 8
def axK : ℕ := 9
def axS : ℕ := 10
def hrv : ℕ := 11
def hink : ℕ := 12
def hinv : ℕ := 13
def houtk : ℕ := 14
def houtv : ℕ := 15
def v : ℕ := 16
def invg4 : ℕ := 17
def r0h : ℕ := 18
def ftk : ℕ := 19
def ftv : ℕ := 20
def mu : ℕ := 21

/-- Base width (round 0). -/
def baseW : ℕ := 22

/-- `𝕂′` roles (Re at `r`, Im at `r + 1`). -/
def invL : ℕ := 0
def invP : ℕ := 2
def invT : ℕ := 4
def accS : ℕ := 6
def accP : ℕ := 8

/-- Terminal publics (`𝕂′`): net service `0 / 1`, path `2 / 3`. -/
def pubAXs : ℕ := 0
def pubAXp : ℕ := 2

/-- `TAG_ax`. -/
def tagAx : ℕ := 5

/-- The serial-capable columns (row indices / ids). -/
def serialColsAx : List ℕ := [R, hrv, hinv, houtv, ftv]

theorem layout_tiles :
    [isFT, isLT, head, cl, z1a, route0, R, pw, l, axK, axS, hrv, hink, hinv, houtk, houtv, v, invg4, r0h,
      ftk, ftv, mu] = List.range baseW ∧
    [invL, invP, invT, accS, accP] = [0, 2, 4, 6, 8] := by decide

/-! ## 2. Copy gates (the `EqG` pattern with next-row operands) -/

section Copy
variable {F : Type} [Field F]

/-- An operand: a current-row column, a next-row column, or a constant. -/
inductive Op (F : Type) where
  | cur (i : ℕ)
  | nxt (i : ℕ)
  | cst (x : F)

def Op.expr : Op F → CoeffExpr F
  | .cur i => cv i
  | .nxt i => nv i
  | .cst x => .const x

/-- **A copy gate** `σ · (X − Y)`. -/
structure CopyG (F : Type) where
  σ : CoeffExpr F
  x : Op F
  y : Op F

def CopyG.gate (g : CopyG F) : CoeffExpr F := .mul g.σ (.sub g.x.expr g.y.expr)

/-- **A select-copy gate** `x − a − σ·(b − a)` (`x = a` at `σ = 0`, `x = b` at `σ = 1`). -/
structure SelG where
  σ : ℕ
  x : ℕ
  a : ℕ
  b : ℕ

def SelG.gate (g : SelG) : CoeffExpr F := .sub (.sub (cv g.x) (cv g.a)) (.mul (cv g.σ) (.sub (cv g.b) (cv g.a)))

end Copy

/-! ## 3. The gates, by design group -/

section Gates
variable {F : Type} [Field F]

/-- `B = 2^32` in the field. -/
def Bf : F := (2 : F) ^ 32


/-- A base gate of the axis chip: an arithmetic gate, a copy gate, or a select gate. -/
inductive AG (F : Type) where
  | ar (g : CoeffExpr F)
  | cp (c : CopyG F)
  | sel (s : SelG)

def AG.gate : AG F → CoeffExpr F
  | .ar g => g
  | .cp c => c.gate
  | .sel s => s.gate

/-- **G1** booleans. -/
def g1 : List (AG F) := [.ar (boolE (cv head)), .ar (boolE (cv cl)), .ar (boolE (cv z1a)), .ar (boolE (cv route0))]

/-- **G2** limb axis: `head·(axK − pw + 1)`, `(1 − head)·(axK − pw + 2)`. -/
def g2 : List (AG F) :=
  [ .ar (.mul (cv head) (.add (.sub (cv axK) (cv pw)) (.const 1))),
    .ar (.mul (notE (cv head)) (.add (.sub (cv axK) (cv pw)) (.const 2))) ]

/-- **G3** segment axis: `head·(axS − l)`, `(1 − head)·(axS − B − l)`. -/
def g3 : List (AG F) :=
  [ .ar (.mul (cv head) (.sub (cv axS) (cv l))),
    .ar (.mul (notE (cv head)) (.sub (.sub (cv axS) (.const Bf)) (cv l))) ]

/-- **G4** top limb `= 1`: `z1a·(1 − head)`, `z1a·(l − 1)`, `z1a·(hout.k − hin.k)`, `z1a·(hout.v − hin.v)`. -/
def g4 : List (AG F) :=
  [ .ar (.mul (cv z1a) (notE (cv head))),
    .ar (.mul (cv z1a) (.sub (cv l) (.const 1))),
    .ar (.mul (cv z1a) (.sub (cv houtk) (cv hink))),
    .cp ⟨cv z1a, .cur houtv, .cur hinv⟩ ]

/-- **G5** roots: `head·(hin.v − hr.v)`, `head·(hin.k − 1)`, `(1 − z1a)·(hin.k − 1)`. -/
def g5 : List (AG F) :=
  [ .cp ⟨cv head, .cur hinv, .cur hrv⟩,
    .ar (.mul (cv head) (.sub (cv hink) (.const 1))),
    .ar (.mul (notE (cv z1a)) (.sub (cv hink) (.const 1))) ]

/-- **G6 continuity** (`(1 − cl)·(next.x − x')`, six gates in the design's order). -/
def g6c : List (AG F) :=
  [ .ar (.mul (notE (cv cl)) (.sub (nv hink) (cv houtk))),
    .cp ⟨notE (cv cl), .nxt hinv, .cur houtv⟩,
    .cp ⟨notE (cv cl), .nxt R, .cur R⟩,
    .cp ⟨notE (cv cl), .nxt hrv, .cur hrv⟩,
    .ar (.mul (notE (cv cl)) (.sub (nv route0) (cv route0))),
    .ar (.mul (notE (cv cl)) (.sub (nv v) (cv v))) ]

/-- **G6 `pw` schedule**: `(1 − cl)·(2·next.pw − pw·(1 + head))`, `cl·(pw − 4)`. -/
def g6p : List (AG F) :=
  [ .ar (.mul (notE (cv cl)) (.sub (.mul (.const 2) (nv pw)) (.mul (cv pw) (.add (.const 1) (cv head))))),
    .ar (.mul (cv cl) (.sub (cv pw) (.const 4))) ]

/-- **G6 `head·isLast = 0`** (cond. 2 verbatim; `isLast` is the chain-last column `cl`). -/
def gHeadCl : CoeffExpr F := .mul (cv head) (cv cl)

/-- **G6 chain boundaries**: `(1 − isLastT)·cl·(1 − next.head)`, `(1 − isLastT)·(1 − cl)·next.head`,
`isLastT·(1 − cl)`, `isFirstT·(1 − head)`. -/
def g6b : List (AG F) :=
  [ .ar (.mul (.mul (notE (cv isLT)) (cv cl)) (notE (nv head))),
    .ar (.mul (.mul (notE (cv isLT)) (notE (cv cl))) (nv head)),
    .ar (.mul (cv isLT) (notE (cv cl))),
    .ar (.mul (cv isFT) (notE (cv head))) ]

/-- **G6** (`head·cl` sits between the schedule and the boundaries, as in §2.1). -/
def g6 : List (AG F) := g6c ++ g6p ++ [.ar gHeadCl] ++ g6b

/-- **G7** the `(0, v)` emission: `r0h − route0·head`, `r0h·(1 − next.cl)`,
`r0h·next.l·((l − (B − 1))·inv_g4 − 1)`, `r0h·(v − l·B − next.l)`. -/
def g7 : List (AG F) :=
  [ .ar (.sub (cv r0h) (.mul (cv route0) (cv head))),
    .ar (.mul (cv r0h) (notE (nv cl))),
    .ar (.mul (.mul (cv r0h) (nv l)) (.sub (.mul (.sub (cv l) (.const (Bf - 1))) (cv invg4)) (.const 1))),
    .ar (.mul (cv r0h) (.sub (.sub (cv v) (.mul (cv l) (.const Bf))) (nv l))) ]

/-- G8's select-copy `ftv − R − route0·(v − R)`. -/
def selG8 : SelG := ⟨route0, ftv, R, v⟩

/-- **G8** emission columns: `ftk − 2·(1 − route0)`, `ftv − R − route0·(v − R)`, `(1 − cl)·mu`. -/
def g8 : List (AG F) :=
  [ .ar (.sub (cv ftk) (.mul (.const 2) (notE (cv route0)))),
    .sel selG8,
    .ar (.mul (notE (cv cl)) (cv mu)) ]

/-- The tagged gate list, in design order. -/
def baseAG : List (AG F) := g1 ++ g2 ++ g3 ++ g4 ++ g5 ++ g6 ++ g7 ++ g8

/-- **The axis chip's base gates** (`4 + 2 + 2 + 4 + 3 + 13 + 4 + 3 = 35`). -/
def baseGates : List (CoeffExpr F) := baseAG.map AG.gate

/-- **Gate ledger**: the three gates no step of S1–S4 consumes (kept). `(1 − cl)·mu` is consumed by S4 since
the provide activity is `mu`. -/
def unconsumedGates : List (CoeffExpr F) :=
  [ .mul (cv head) (.sub (cv hink) (.const 1)),
    .mul (.mul (notE (cv isLT)) (notE (cv cl))) (nv head),
    .mul (cv isLT) (notE (cv cl)) ]

theorem unconsumed_kept : ∀ g ∈ (unconsumedGates : List (CoeffExpr F)), g ∈ baseGates := by
  intro g hg
  simp only [unconsumedGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact List.mem_map.mpr ⟨.ar _, by simp [baseAG, g5], rfl⟩
  · exact List.mem_map.mpr ⟨.ar _, by simp [baseAG, g6, g6b], rfl⟩
  · exact List.mem_map.mpr ⟨.ar _, by simp [baseAG, g6, g6b], rfl⟩

/-! ### The `𝕂′` LogUp gates -/

/-- The consumed limb record `(R, axK, 0, l)` (`walkRecA`'s 4-entry shape). -/
def limbKey : List (CoeffExpr F) := [cv R, cv axK, .const 0, cv l]
/-- The consumed path record `(hin.v, axS, hout.k, hout.v)` (`walkRec`). -/
def pathKey : List (CoeffExpr F) := [cv hinv, cv axS, cv houtk, cv houtv]
/-- The provided `TAG_ax` record `(hr.v, ftk, ftv, hout.k, hout.v, R, 0, 5)`. -/
def tagKey : List (CoeffExpr F) :=
  [cv hrv, cv ftk, cv ftv, cv houtk, cv houtv, cv R, .const 0, .const (tagAx : F)]

/-- The service term `invL − mu·invT` (consume minus provide, activity `mu`). -/
def sTerm (cur : Bool) : QE F :=
  if cur then QE.sub (QE.var invL) (QE.scale (cv mu) (QE.var invT))
  else QE.sub (QE.next invL) (QE.scale (nv mu) (QE.next invT))

/-- The path term `(1 − z1a)·invP`. -/
def pTerm (cur : Bool) : QE F :=
  if cur then QE.scale (notE (cv z1a)) (QE.var invP) else QE.scale (notE (nv z1a)) (QE.next invP)

/-- **The axis chip's `𝕂′` equations** (three inverses, two accumulators). -/
def axQ (δF : F) : List (QE F) :=
  [ QE.sub (QE.mul δF (QE.var invL) (HQ.denKeyQ δF limbKey)) QE.one,
    QE.sub (QE.mul δF (QE.var invP) (HQ.denKeyQ δF pathKey)) QE.one,
    QE.sub (QE.mul δF (QE.var invT) (HQ.denKeyQ δF tagKey)) QE.one,
    QE.scale (cv isFT) (QE.sub (QE.var accS) (sTerm true)),
    QE.scale (notE (cv isLT)) (QE.sub (QE.sub (QE.next accS) (QE.var accS)) (sTerm false)),
    QE.scale (cv isLT) (QE.sub (QE.var accS) (QE.pub pubAXs)),
    QE.scale (cv isFT) (QE.sub (QE.var accP) (pTerm true)),
    QE.scale (notE (cv isLT)) (QE.sub (QE.sub (QE.next accP) (QE.var accP)) (pTerm false)),
    QE.scale (cv isLT) (QE.sub (QE.var accP) (QE.pub pubAXp)) ]

def axMixed (δF : F) : List (MixedExpr F) := (axQ δF).flatMap QE.gates

/-! ### Degree -/

theorem baseGates_deg_all : (baseGates (F := F)).all (fun g => decide (g.degree ≤ 4)) = true := by
  simp [baseGates, baseAG, AG.gate, g1, g2, g3, g4, g5, g6, g6c, g6p, gHeadCl, g6b, g7, g8, selG8, CopyG.gate,
    SelG.gate, Op.expr, CoeffExpr.degree]

theorem baseGates_deg : ∀ g ∈ (baseGates (F := F)), g.degree ≤ 4 := by
  intro g hg; simpa using List.all_eq_true.mp baseGates_deg_all g hg

theorem axMixed_deg_all (δF : F) : (axMixed δF).all (fun g => decide (g.degree ≤ 4)) = true := by
  simp [axMixed, axQ, sTerm, pTerm, limbKey, pathKey, tagKey, HQ.denKeyQ, HQ.rlcQ, HQ.gpowQ, HQ.gamQ,
    HQ.rhoQ, QE.gates, QE.var, QE.next, QE.chal, QE.pub, QE.base, QE.zero, QE.one, QE.add, QE.sub,
    QE.mul, QE.scale, MixedExpr.degree, CoeffExpr.degree]

theorem axMixed_deg (δF : F) : ∀ g ∈ axMixed δF, g.degree ≤ 4 := by
  intro g hg; simpa using List.all_eq_true.mp (axMixed_deg_all δF) g hg

theorem baseGates_length : (baseGates (F := F)).length = 35 := by
  simp [baseGates, baseAG, g1, g2, g3, g4, g5, g6, g6c, g6p, g6b, g7, g8]

theorem axMixed_length (δF : F) : (axMixed δF).length = 18 := by
  simp [axMixed, axQ, QE.gates]

/-! ## 4. The template and the chip -/

/-- **The axis chip template**: three rounds (as the handle-coin twins), base `22 / 0 / 0`,
`𝕂`-roles `0 / 0 / 10`. -/
def axisTemplateJ9 (δF : F) : ChipTemplate F where
  rounds := 3
  rounds_pos := by decide
  baseColsOf := ![22, 0, 0]
  extColsOf := ![0, 0, 10]
  baseTransition := baseGates
  extTransition := []
  mixedTransition := axMixed δF
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := baseGates_deg
  extTransition_deg := by simp
  mixedTransition_deg := axMixed_deg δF
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

theorem axisTemplateJ9_baseCols (δF : F) : (axisTemplateJ9 δF).baseCols = 22 := by
  show (∑ r : Fin 3, (![22, 0, 0] : Fin 3 → ℕ) r) = 22
  decide
theorem axisTemplateJ9_extCols (δF : F) : (axisTemplateJ9 δF).extCols = 10 := by
  show (∑ r : Fin 3, (![0, 0, 10] : Fin 3 → ℕ) r) = 10
  decide

/-- **`gates_degree ≤ 4`**: every base and every mixed gate of the template. -/
theorem gates_degree (δF : F) :
    (∀ g ∈ (axisTemplateJ9 δF).baseTransition, g.degree ≤ 4) ∧
      (∀ g ∈ (axisTemplateJ9 δF).mixedTransition, g.degree ≤ 4) :=
  ⟨baseGates_deg, axMixed_deg δF⟩

end Gates

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **`axisChipJ9`** (masks `isFirstT`, `isLastT` at columns `0`, `1`). -/
noncomputable def axisChipJ9 (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    FixedPreprocessingRAP F where
  rap := expandChip (axisTemplateJ9 δF) b (slotVal b 22 chals) (slotVal b 22 pubs) orbit (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 22 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

variable (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- **`width_eq`: `w = 52`** (`22 + 10·3`), by `rfl`. -/
theorem width_eq : (axisChipJ9 δF b hn nodes orbit chals pubs).rap.w = 52 := rfl

/-- **Fingerprint**: `w = 52`, `s = 35 + 18·3 = 89`, `d = 4`, `k = 3`. -/
theorem axisChipJ9_fingerprint :
    (axisChipJ9 δF b hn nodes orbit chals pubs).rap.w = 52 ∧
      (axisChipJ9 δF b hn nodes orbit chals pubs).rap.s = 89 ∧
      (axisChipJ9 δF b hn nodes orbit chals pubs).rap.d = 4 ∧
      (axisChipJ9 δF b hn nodes orbit chals pubs).rap.k = 3 := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  rw [show (axisChipJ9 δF b hn nodes orbit chals pubs).rap = expandChip (axisTemplateJ9 δF) b _ _ orbit _ from rfl,
    expandChip_s]
  simp only [axisTemplateJ9, baseGates_length, axMixed_length, List.length_nil]

end Chip

/-! ## 5. -/

section Instrument
variable {F : Type} [Field F]

/-- **No serial-capable column is read** (at the axis layout). -/
def serialFreeAx (g : CoeffExpr F) : Bool := (colsOfB g).all fun i => !serialColsAx.contains i

def CopyG.okB (g : CopyG F) : Bool := serialFreeAx g.σ
def SelG.okB (g : SelG) : Bool := !serialColsAx.contains g.σ

/-- **The instrument on a tagged gate**: arithmetic gates read no serial; copies and selects have a
serial-free selector (the difference / selection is the only serial read). -/
def AG.okB : AG F → Bool
  | .ar g => serialFreeAx g
  | .cp c => c.okB
  | .sel s => s.okB

def AG.isAr : AG F → Bool
  | .ar _ => true
  | _ => false

/-- `𝕂′` discipline at the axis serial set (`ChipHQ.keyOKQe`'s rule): a serial is read only as an RLC key entry
`c · lift(col)` with a coin-only coefficient. -/
def coinOnlyA : MixedExpr F → Bool
  | .Var .challenge _ => true
  | .Const _ => true
  | .Scale (.const _) u => coinOnlyA u
  | .Add x y => coinOnlyA x && coinOnlyA y
  | .Sub x y => coinOnlyA x && coinOnlyA y
  | .Mul x y => coinOnlyA x && coinOnlyA y
  | .Neg x => coinOnlyA x
  | .Pow x _ => coinOnlyA x
  | _ => false

def keyOKAx : MixedExpr F → Bool
  | .Mul x (.Lift (.var _ _)) => coinOnlyA x
  | .Var _ _ => true
  | .Lift g => serialFreeAx g
  | .Scale g u => serialFreeAx g && keyOKAx u
  | .Const _ => true
  | .Add x y => keyOKAx x && keyOKAx y
  | .Sub x y => keyOKAx x && keyOKAx y
  | .Mul x y => keyOKAx x && keyOKAx y
  | .Neg x => keyOKAx x
  | .Pow x _ => keyOKAx x


/-- Every base gate of the axis chip passes the serial-free check `AG.okB`. -/
theorem baseGates_serialFree : (baseAG (F := ℚ)).all AG.okB = true := by decide +kernel

/-- The non-arithmetic (serial-reading) gates are exactly six: five copies and the G8 select. -/
theorem serial_readers_count : ((baseAG (F := ℚ)).filter fun g => !g.isAr).length = 6 := by decide +kernel

/-- Every arithmetic gate reads no serial. -/
theorem arith_serialFree : ((baseAG (F := ℚ)).filter AG.isAr).all (fun g => serialFreeAx g.gate) = true := by
  decide +kernel


/-- Every mixed gate of the axis chip passes the key check `keyOKAx`. -/
theorem axMixed_keyOK : (axMixed (F := ℚ) 7).all keyOKAx = true := by decide +kernel


/-- The mixed gates of the axis chip read only the listed columns (`R, axK, l, hinv, …, z1a`). -/
theorem axMixed_reads :
    (axMixed (F := ℚ) 7).all (fun g => (liftCols g).all fun c =>
      [R, axK, l, hinv, axS, houtk, houtv, hrv, ftk, ftv, isFT, isLT, mu, z1a].contains c) = true := by
  decide +kernel

/-- **Positive control 1**: `serialFreeAx` flags the G6 continuity copy of `R`. -/
theorem serialFreeAx_flags : serialFreeAx (F := ℚ) (.mul (notE (cv cl)) (.sub (nv R) (cv R))) = false := by
  decide +kernel

/-- **Positive control 2**: G8's select, mis-tagged as plain arithmetic, is flagged (so the select class is
what admits it), and a copy with a serial selector is flagged. -/
theorem flags_naive_arith :
    AG.okB (F := ℚ) (.ar selG8.gate) = false ∧
      AG.okB (F := ℚ) (.cp ⟨cv R, .nxt hrv, .cur hrv⟩) = false := by decide +kernel

/-- **Positive control 3**: the `𝕂′` instrument flags a denominator multiplied by a serial. -/
theorem keyOKAx_flags :
    ((QE.mul (7 : ℚ) (HQ.denKeyQ 7 limbKey) (QE.base (cv R))).gates).all keyOKAx = false := by
  decide +kernel

/-- **Positive control 4**: the read-set instrument sees a column outside the set (`pw`). -/
theorem axMixed_reads_control :
    ((axMixed (F := ℚ) 7 ++ (QE.mul (7 : ℚ) (QE.var invL) (QE.base (cv pw))).gates).all
      (fun g => (liftCols g).all fun c =>
        [R, axK, l, hinv, axS, houtk, houtv, hrv, ftk, ftv, isFT, isLT, mu, z1a].contains c)) = false := by
  decide +kernel

end Instrument

/-! ## 6. Row environments and gate readers -/

section Rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (axisChipJ9 δF b hn nodes orbit chals pubs).rap.w → F[X])

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- Row `i`'s base environment on the axis chip (twin of `AtomServedQ.aEF`). -/
abbrev axEF {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : Env F :=
  Reify.envOfTrace Q' orbit.ω (nodes i) (slotVal b 22 chals) (slotVal b 22 pubs)

/-- Row `i`'s gathered `𝕂` environment. -/
abbrev axEK {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : Env K :=
  gatherEnv b ((axisTemplateJ9 δF).col0 3) (axEF b nodes orbit chals pubs Q' i)

theorem ax_base (hsat : (axisChipJ9 δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    ∀ g ∈ (baseGates : List (CoeffExpr F)), g.eval (axEF b nodes orbit chals pubs Q i) = 0 := by
  have hl := (expandChip_satisfies_iff_language (axisTemplateJ9 δF) b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)
  exact hl.1

theorem ax_qgates (hsat : (axisChipJ9 δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    ∀ e ∈ axQ δF, e.ev δF (axEK δF b nodes orbit chals pubs Q i) (axEF b nodes orbit chals pubs Q i) = 0 := by
  have hl := (expandChip_satisfies_iff_language (axisTemplateJ9 δF) b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)
  intro e he
  exact ev_eq_zero_of_gates δF _ _ e fun g hg => hl.2.2.2 g (List.mem_flatMap.mpr ⟨e, he, hg⟩)

theorem ax_masks (hbind : (axisChipJ9 δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (axEF b nodes orbit chals pubs Q i).trace isFT = (if (i : ℕ) = 0 then 1 else 0) ∧
      (axEF b nodes orbit chals pubs Q i).trace isLT = (if (i : ℕ) = n - 1 then 1 else 0) := by
  have hw : (axisChipJ9 δF b hn nodes orbit chals pubs).rap.w = 52 := width_eq δF b hn nodes orbit chals pubs
  have h0 : Q ⟨0, by rw [hw]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 2; omega⟩
  have h1 : Q ⟨1, by rw [hw]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 2; omega⟩
  exact TeleH.masks_of hn nodes orbit Q _ _ h0 h1 hinj _ _ i

theorem axEF_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (j : ℕ) :
    (axEF b nodes orbit chals pubs Q i).traceNext j = (axEF b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace j :=
  traceNext_eq nodes orbit Q _ _ hadj i hi j

theorem axEK_pub (i : Fin n) (idx : ℕ) : (axEK δF b nodes orbit chals pubs Q i).pub idx = pubs idx :=
  TeleH.gather_pub_T b (axisTemplateJ9 δF) 22 (axisTemplateJ9_baseCols δF) _ pubs rfl idx

theorem axEK_chal (i : Fin n) (idx : ℕ) : (axEK δF b nodes orbit chals pubs Q i).chal idx = chals idx :=
  TeleH.gather_chal_T b (axisTemplateJ9 δF) 22 (axisTemplateJ9_baseCols δF) _ chals rfl idx

/-! ### The record lists, filtered on nonzero activity -/

/-- A key read off a base environment, lifted to `𝕂`, zero-padded to width `m`. -/
def keyVecL (m : ℕ) (key : List (CoeffExpr F)) (eF : Env F) : Fin m → K :=
  fun c => algebraMap F K ((key.getD c (.const 0)).eval eF)

/-- **The limb consumes** (service, every row; weight `1`). -/
def axLimbReqs {w : ℕ} (Q' : Fin w → F[X]) : List (Fin 8 → K) :=
  (List.finRange n).map fun i => keyVecL 8 limbKey (axEF b nodes orbit chals pubs Q' i)

/-- **The path consumes** (rows with activity `1 − z1a ≠ 0`). -/
def axPathReqs [DecidableEq F] {w : ℕ} (Q' : Fin w → F[X]) : List (Fin 5 → K) :=
  (List.finRange n).flatMap fun i =>
    if 1 - (axEF b nodes orbit chals pubs Q' i).trace z1a = 0 then [] else
      [keyVecL 5 pathKey (axEF b nodes orbit chals pubs Q' i)]

/-- **The `TAG_ax` providers** (rows with activity `mu ≠ 0`, weight `mu`). -/
def axTagProvs [DecidableEq F] {w : ℕ} (Q' : Fin w → F[X]) : List ((Fin 8 → K) × K) :=
  (List.finRange n).flatMap fun i =>
    if (axEF b nodes orbit chals pubs Q' i).trace mu = 0 then [] else
      [(keyVecL 8 tagKey (axEF b nodes orbit chals pubs Q' i),
        algebraMap F K ((axEF b nodes orbit chals pubs Q' i).trace mu))]

theorem axTagProvs_mu [DecidableEq F] {w : ℕ} (Q' : Fin w → F[X]) :
    ∀ q ∈ axTagProvs b nodes orbit chals pubs Q', ∃ i : Fin n,
      (axEF b nodes orbit chals pubs Q' i).trace mu ≠ 0 ∧
      q = (keyVecL 8 tagKey (axEF b nodes orbit chals pubs Q' i),
        algebraMap F K ((axEF b nodes orbit chals pubs Q' i).trace mu)) := by
  intro q hq
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hq
  by_cases h0 : (axEF b nodes orbit chals pubs Q' i).trace mu = 0
  · simp [h0] at hi
  · rw [if_neg h0, List.mem_singleton] at hi
    exact ⟨i, h0, hi⟩

end Rows

/-! ## 7. NC: drop `head·isLast` ⇒ the padding trace satisfies -/

section NC
variable {F : Type} [Field F]

/-- **The padding row** (§5 (c), a 1-row chain on a 2-limb atom): on the 1-row table (`isFirstT = isLastT = 1`),
`head = cl = 1`, `pw = 4`, `axK = 3` (the top-limb axis `2^2 − 1` of a 2-limb comb: the chain drops `l_0`),
`axS = l = hi`, `hin = (1, hr)`, `route0 = z1a = r0h = 0`, `ftk = 2`, `ftv = R`; next-row values arbitrary. -/
def padEnv (rr hr hi hk hv : F) (nxt : ℕ → F) : Env F where
  trace := fun j =>
    if j = isFT then 1 else if j = isLT then 1 else if j = head then 1 else if j = cl then 1
    else if j = pw then 4 else if j = axK then 3 else if j = R then rr else if j = l then hi
    else if j = axS then hi else if j = hrv then hr else if j = hink then 1 else if j = hinv then hr
    else if j = houtk then hk else if j = houtv then hv else if j = ftk then 2 else if j = ftv then rr else 0
  traceNext := nxt
  chal := fun _ => 0
  pub := fun _ => 0

/-- **NC `nc_drop_headCl`**: the padding row satisfies every axis base gate EXCEPT `head·cl`, which evaluates
to `1`.  So dropping `head·isLast` admits it; with the gate, the row is rejected.  LABEL: row (base-gate)
level. -/
theorem nc_drop_headCl (rr hr hi hk hv : F) (nxt : ℕ → F) :
    (∀ g ∈ (baseGates : List (CoeffExpr F)), g ≠ gHeadCl → g.eval (padEnv rr hr hi hk hv nxt) = 0) ∧
      (gHeadCl : CoeffExpr F).eval (padEnv rr hr hi hk hv nxt) = 1 ∧ (gHeadCl : CoeffExpr F) ∈ baseGates := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg hne
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    simp only [baseAG, g1, g2, g3, g4, g5, g6, g6c, g6p, g6b, g7, g8, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at ha
    rcases ha with ((((((((ha | ha | ha | ha) | ha | ha) | ha | ha) | ha | ha | ha | ha) | ha | ha | ha) |
      (((ha | ha | ha | ha | ha | ha) | ha | ha) | ha) | ha | ha | ha | ha) | ha | ha | ha | ha) | ha | ha | ha) <;>
      subst ha <;>
      first
      | exact absurd rfl hne
      | (simp [AG.gate, gHeadCl, selG8, CopyG.gate, SelG.gate, Op.expr, padEnv, CoeffExpr.eval, isFT, isLT, head,
           cl, z1a, route0, R, pw, l, axK, axS, hrv, hink, hinv, houtk, houtv, v, invg4, r0h, ftk, ftv, mu]
         try norm_num)
  · simp [gHeadCl, padEnv, CoeffExpr.eval, isFT, isLT, head, cl]
  · exact List.mem_map.mpr ⟨.ar gHeadCl, by simp [baseAG, g6], rfl⟩

/-- The same row under the FULL gate list is rejected (by exactly `head·cl`). -/
theorem padding_rejected (rr hr hi hk hv : F) (nxt : ℕ → F) :
    ∃ g ∈ (baseGates : List (CoeffExpr F)), g.eval (padEnv rr hr hi hk hv nxt) ≠ 0 :=
  ⟨gHeadCl, (nc_drop_headCl rr hr hi hk hv nxt).2.2, by
    rw [(nc_drop_headCl rr hr hi hk hv nxt).2.1]; exact one_ne_zero⟩

/-- The padding row consumes the limb record `(R, 3, 0, hi)`: axis `3 = 2^2 − 1`, the top limb of a 2-limb comb
(so a served chain of length 1 would certify `hi` alone, dropping `l_0`). -/
theorem padEnv_limbKey (rr hr hi hk hv : F) (nxt : ℕ → F) :
    (limbKey : List (CoeffExpr F)).map (fun g => g.eval (padEnv rr hr hi hk hv nxt)) = [rr, 3, 0, hi] := by
  simp [limbKey, padEnv, CoeffExpr.eval, isFT, isLT, head, cl, R, axK, l, pw]

end NC


/-! ## 8. Row lemmas G1–G8 (gate level, any field) -/

section RowLemmas
variable {F : Type} [Field F]

/-- **Every base gate of the axis chip, as a field equation at one row** (`t` = current row, `n` = next row). -/
structure AxRowEqs (e : Env F) : Prop where
  b_head : e.trace head * (e.trace head - 1) = 0
  b_cl : e.trace cl * (e.trace cl - 1) = 0
  b_z1a : e.trace z1a * (e.trace z1a - 1) = 0
  b_route0 : e.trace route0 * (e.trace route0 - 1) = 0
  g2h : e.trace head * (e.trace axK - e.trace pw + 1) = 0
  g2n : (1 - e.trace head) * (e.trace axK - e.trace pw + 2) = 0
  g3h : e.trace head * (e.trace axS - e.trace l) = 0
  g3n : (1 - e.trace head) * (e.trace axS - Bf - e.trace l) = 0
  g4a : e.trace z1a * (1 - e.trace head) = 0
  g4b : e.trace z1a * (e.trace l - 1) = 0
  g4c : e.trace z1a * (e.trace houtk - e.trace hink) = 0
  g4d : e.trace z1a * (e.trace houtv - e.trace hinv) = 0
  g5a : e.trace head * (e.trace hinv - e.trace hrv) = 0
  g5b : e.trace head * (e.trace hink - 1) = 0
  g5c : (1 - e.trace z1a) * (e.trace hink - 1) = 0
  g6k : (1 - e.trace cl) * (e.traceNext hink - e.trace houtk) = 0
  g6v : (1 - e.trace cl) * (e.traceNext hinv - e.trace houtv) = 0
  g6R : (1 - e.trace cl) * (e.traceNext R - e.trace R) = 0
  g6hr : (1 - e.trace cl) * (e.traceNext hrv - e.trace hrv) = 0
  g6r0 : (1 - e.trace cl) * (e.traceNext route0 - e.trace route0) = 0
  g6vv : (1 - e.trace cl) * (e.traceNext v - e.trace v) = 0
  g6pw : (1 - e.trace cl) * (2 * e.traceNext pw - e.trace pw * (1 + e.trace head)) = 0
  g6p4 : e.trace cl * (e.trace pw - 4) = 0
  g6hc : e.trace head * e.trace cl = 0
  g6b1 : (1 - e.trace isLT) * e.trace cl * (1 - e.traceNext head) = 0
  g6b2 : (1 - e.trace isLT) * (1 - e.trace cl) * e.traceNext head = 0
  g6b3 : e.trace isLT * (1 - e.trace cl) = 0
  g6b4 : e.trace isFT * (1 - e.trace head) = 0
  g7a : e.trace r0h - e.trace route0 * e.trace head = 0
  g7b : e.trace r0h * (1 - e.traceNext cl) = 0
  g7c : e.trace r0h * e.traceNext l * ((e.trace l - (Bf - 1)) * e.trace invg4 - 1) = 0
  g7d : e.trace r0h * (e.trace v - e.trace l * Bf - e.traceNext l) = 0
  g8a : e.trace ftk - 2 * (1 - e.trace route0) = 0
  g8b : e.trace ftv - e.trace R - e.trace route0 * (e.trace v - e.trace R) = 0
  g8c : (1 - e.trace cl) * e.trace mu = 0

/-- **Reader**: every base gate vanishing at `e` gives `AxRowEqs e`. -/
theorem axRowEqs_of {e : Env F} (hg : ∀ g ∈ (baseGates : List (CoeffExpr F)), g.eval e = 0) : AxRowEqs e := by
  have hm : ∀ a ∈ (baseAG : List (AG F)), a.gate.eval e = 0 := fun a ha => hg _ (List.mem_map_of_mem ha)
  simp only [baseAG, g1, g2, g3, g4, g5, g6, g6c, g6p, g6b, g7, g8, selG8, List.forall_mem_append,
    List.forall_mem_cons, List.forall_mem_nil, AG.gate, CopyG.gate, SelG.gate, Op.expr, gHeadCl, CoeffExpr.eval,
    cv, nv, notE, boolE, List.mem_nil_iff, false_implies, implies_true, and_true] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2, h3, h4⟩, h5, h6⟩, h7, h8⟩, h9, h10, h11, h12⟩, h13, h14, h15⟩,
    ⟨⟨⟨h16, h17, h18, h19, h20, h21⟩, h22, h23⟩, h24⟩, h25, h26, h27, h28⟩, h29, h30, h31, h32⟩, h33, h34, h35⟩ := hm
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35⟩

variable {e : Env F} (H : AxRowEqs e)
include H

/-- **G1**: the four flags are boolean. -/
theorem G1 : (e.trace head = 0 ∨ e.trace head = 1) ∧ (e.trace cl = 0 ∨ e.trace cl = 1) ∧
    (e.trace z1a = 0 ∨ e.trace z1a = 1) ∧ (e.trace route0 = 0 ∨ e.trace route0 = 1) := by
  have b : ∀ x : F, x * (x - 1) = 0 → x = 0 ∨ x = 1 := fun x hx => by
    rcases mul_eq_zero.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  exact ⟨b _ H.b_head, b _ H.b_cl, b _ H.b_z1a, b _ H.b_route0⟩

/-- **G2**: the limb axis: `axK = pw − 1` on the head, `axK = pw − 2` off it. -/
theorem G2 : (e.trace head = 1 → e.trace axK = e.trace pw - 1) ∧
    (e.trace head = 0 → e.trace axK = e.trace pw - 2) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := H.g2h; rw [h, one_mul] at this; linear_combination this
  · have := H.g2n; rw [h, sub_zero, one_mul] at this; linear_combination this

/-- **G3**: the segment axis: `axS = l` on the head, `axS = B + l` off it. -/
theorem G3 : (e.trace head = 1 → e.trace axS = e.trace l) ∧
    (e.trace head = 0 → e.trace axS = Bf + e.trace l) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := H.g3h; rw [h, one_mul] at this; linear_combination this
  · have := H.g3n; rw [h, sub_zero, one_mul] at this; linear_combination this

/-- **G4**: a `z1a` row is the head, its top limb is `1`, and `hout = hin`. -/
theorem G4 (hz : e.trace z1a = 1) : e.trace head = 1 ∧ e.trace l = 1 ∧ e.trace houtk = e.trace hink ∧
    e.trace houtv = e.trace hinv := by
  have a := H.g4a; have b := H.g4b; have c := H.g4c; have d := H.g4d
  rw [hz, one_mul] at a b c d
  exact ⟨by linear_combination -a, by linear_combination b, by linear_combination c, by linear_combination d⟩

/-- **G5**: the head's root is `(1, hr)`; every non-`z1a` row's root handle has kind `1`. -/
theorem G5 : (e.trace head = 1 → e.trace hinv = e.trace hrv ∧ e.trace hink = 1) ∧
    (e.trace z1a = 0 → e.trace hink = 1) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have a := H.g5a; have b := H.g5b; rw [h, one_mul] at a b
    exact ⟨by linear_combination a, by linear_combination b⟩
  · have c := H.g5c; rw [h, sub_zero, one_mul] at c; linear_combination c

/-- **G6 continuity** (off `cl`): `hin ← hout`, and `R`, `hr`, `route0`, `v` carry to the next row. -/
theorem G6c (hc : e.trace cl = 0) : e.traceNext hink = e.trace houtk ∧ e.traceNext hinv = e.trace houtv ∧
    e.traceNext R = e.trace R ∧ e.traceNext hrv = e.trace hrv ∧ e.traceNext route0 = e.trace route0 ∧
    e.traceNext v = e.trace v := by
  have a := H.g6k; have b := H.g6v; have c := H.g6R; have d := H.g6hr; have f := H.g6r0; have g := H.g6vv
  rw [hc, sub_zero, one_mul] at a b c d f g
  exact ⟨by linear_combination a, by linear_combination b, by linear_combination c, by linear_combination d,
    by linear_combination f, by linear_combination g⟩

/-- **G6 `pw` schedule**: off `cl`, `2·next.pw = pw·(1 + head)` (non-head: `pw = 2·next.pw`; head:
`next.pw = pw` when `2 ≠ 0`); on `cl`, `pw = 4`. -/
theorem G6p : (e.trace cl = 0 → 2 * e.traceNext pw = e.trace pw * (1 + e.trace head)) ∧
    (e.trace cl = 1 → e.trace pw = 4) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have a := H.g6pw; rw [h, sub_zero, one_mul] at a; linear_combination a
  · have a := H.g6p4; rw [h, one_mul] at a; linear_combination a

theorem G6p_nonhead (hc : e.trace cl = 0) (hh : e.trace head = 0) : e.trace pw = 2 * e.traceNext pw := by
  have := (G6p H).1 hc; rw [hh, add_zero, mul_one] at this; exact this.symm

theorem G6p_head (h2 : (2 : F) ≠ 0) (hc : e.trace cl = 0) (hh : e.trace head = 1) :
    e.trace pw = e.traceNext pw := by
  have := (G6p H).1 hc; rw [hh] at this
  have h' : (2 : F) * (e.traceNext pw - e.trace pw) = 0 := by linear_combination this
  exact (sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left h2)).symm

/-- **G6 `head·isLast = 0`** (cond. 2): a head is never the chain's last row. -/
theorem G6hc (hh : e.trace head = 1) : e.trace cl = 0 := by
  have := H.g6hc; rw [hh, one_mul] at this; exact this

/-- **G6 chain boundaries.** -/
theorem G6b : (e.trace isLT = 0 → e.trace cl = 1 → e.traceNext head = 1) ∧
    (e.trace isLT = 0 → e.trace cl = 0 → e.traceNext head = 0) ∧
    (e.trace isLT = 1 → e.trace cl = 1) ∧ (e.trace isFT = 1 → e.trace head = 1) := by
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h => ?_, fun h => ?_⟩
  · have a := H.g6b1; rw [h1, h2, sub_zero, one_mul, one_mul] at a; linear_combination -a
  · have a := H.g6b2; rw [h1, h2] at a; simpa using a
  · have a := H.g6b3; rw [h, one_mul] at a; linear_combination -a
  · have a := H.g6b4; rw [h, one_mul] at a; linear_combination -a

/-- **G7** the `(0, v)` emission: `r0h = route0·head`; on `r0h`, the next row closes the chain, the g4 form
`next.l ≠ 0 → l ≠ B − 1`, and `v = l·B + next.l`. -/
theorem G7 : e.trace r0h = e.trace route0 * e.trace head ∧
    (e.trace r0h = 1 → e.traceNext cl = 1 ∧ (e.traceNext l ≠ 0 → e.trace l ≠ Bf - 1) ∧
      e.trace v = e.trace l * Bf + e.traceNext l) := by
  refine ⟨by linear_combination H.g7a, fun h => ⟨?_, fun hl hb => ?_, ?_⟩⟩
  · have a := H.g7b; rw [h, one_mul] at a; linear_combination -a
  · have c := H.g7c; rw [h, one_mul, hb, sub_self, zero_mul, zero_sub, mul_neg, mul_one, neg_eq_zero] at c
    exact hl c
  · have d := H.g7d; rw [h, one_mul] at d; linear_combination d

/-- **G8** the emission columns: `ftk = 2·(1 − route0)`, `ftv = R + route0·(v − R)`, `(1 − cl)·mu = 0`. -/
theorem G8 : e.trace ftk = 2 * (1 - e.trace route0) ∧
    e.trace ftv = e.trace R + e.trace route0 * (e.trace v - e.trace R) ∧
    (e.trace cl = 0 → e.trace mu = 0) := by
  refine ⟨by linear_combination H.g8a, by linear_combination H.g8b, fun h => ?_⟩
  have a := H.g8c; rw [h, sub_zero, one_mul] at a; exact a

/-- G8 by route: `route0 = 1 ⇒ (ftk, ftv) = (0, v)`; `route0 = 0 ⇒ (ftk, ftv) = (2, R)`. -/
theorem G8_route : (e.trace route0 = 1 → e.trace ftk = 0 ∧ e.trace ftv = e.trace v) ∧
    (e.trace route0 = 0 → e.trace ftk = 2 ∧ e.trace ftv = e.trace R) := by
  obtain ⟨a, b, -⟩ := G8 H
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩ <;> rw [h] at a b <;>
    first | linear_combination a | linear_combination b

/-- A provided row (`mu ≠ 0`) closes its chain (the gate `(1 − cl)·mu` with activity `mu`). -/
theorem cl_of_mu (hmu : e.trace mu ≠ 0) : e.trace cl = 1 := by
  rcases (G1 H).2.1 with h | h
  · exact absurd ((G8 H).2.2 h) hmu
  · exact h

omit H in
/-- **Every row of an accepted axis trace satisfies `AxRowEqs`.** -/
theorem ax_rowEqs {K : Type} [Field K] [Algebra F K] [FiniteDimensional F K] (δF : F) (b : Basis (Fin 3) F K)
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
    (Q : Fin (axisChipJ9 δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (axisChipJ9 δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    AxRowEqs (axEF b nodes orbit chals pubs Q i) := by
  have hl := (expandChip_satisfies_iff_language (axisTemplateJ9 δF) b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)
  exact axRowEqs_of hl.1

end RowLemmas

/-! ## 9. ℕ-level step lemmas at `ZMod p` -/

section Steps
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (combL)
variable {p : ℕ} [Fact p.Prime]

theorem two_pow_sub_two_ne (d L : ℕ) (hL : 1 ≤ L) : 2 ^ (d + 2) - 2 ≠ 2 ^ L - 1 := by
  have h1 : 2 ^ (d + 2) = 2 * 2 ^ (d + 1) := by ring
  have h2 : 2 ^ L = 2 * 2 ^ (L - 1) := by rw [← pow_succ']; congr 1; omega
  have h3 : 1 ≤ 2 ^ (d + 1) := Nat.one_le_two_pow
  have h4 : 1 ≤ 2 ^ (L - 1) := Nat.one_le_two_pow
  omega

/-- Cast injectivity below `p`. -/
theorem val_of_cast {x : ZMod p} {a : ℕ} (ha : a < p) (h : x = (a : ZMod p)) : x.val = a := by
  rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt ha]

/-- **S3 step P (a non-head row at distance `d` from `cl`)**: with `pw = 2^(d+2)` (`d + 2 ≤ 63`, `2^63 < p`) and the
served limb fact `slot axK (combL L) = atom l`, the axis is the exact even comb axis `2^(d+2) − 2` and the limb is
`L[d]`. -/
theorem step_nonhead (hp : 2 ^ 63 < p) {e : Env (ZMod p)} (H : AxRowEqs e) (hh : e.trace head = 0) (d : ℕ)
    (hd : d + 2 ≤ 63) (hpw : e.trace pw = (2 : ZMod p) ^ (d + 2)) {L : List ℕ}
    (hS : Noun.slot (e.trace axK).val (combL L) = some (.atom (e.trace l).val)) :
    (e.trace axK).val = 2 ^ (d + 2) - 2 ∧ d + 2 ≤ L.length ∧ (e.trace l).val = L[d]! := by
  have hle : 2 ^ (d + 2) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) hd
  have h2 : 2 ≤ 2 ^ (d + 2) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (d + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hax : (e.trace axK).val = 2 ^ (d + 2) - 2 := by
    refine val_of_cast (by omega) ?_
    rw [(G2 H).2 hh, hpw, Nat.cast_sub h2]; push_cast; ring
  refine ⟨hax, ?_⟩
  rw [hax] at hS
  rcases Nock.J9A.NounAx.slot_combL_atom hS with ⟨j, hj, ha, hx⟩ | ⟨h1, ha, -⟩ | ⟨-, ha, -⟩
  · have hj2 : 2 ≤ 2 ^ (j + 2) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ (d + 2) = 2 ^ (j + 2) := by omega
    have hdj : d + 2 = j + 2 := Nat.pow_right_injective (le_refl 2) this
    have : d = j := by omega
    subst this
    exact ⟨hj, hx⟩
  · exact absurd ha (two_pow_sub_two_ne d L.length h1)
  · have : 4 ≤ 2 ^ (d + 2) := by
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ (d + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- **S3 step H (the head)**: with `pw = 2^k` (`2 ≤ k ≤ 63`) and the served limb fact, the head reads the TOP limb
of a `k`-limb comb: `k = L.length`, `axK = 2^k − 1`, `l = L.getLast!`. -/
theorem step_head (hp : 2 ^ 63 < p) {e : Env (ZMod p)} (H : AxRowEqs e) (hh : e.trace head = 1) (k : ℕ)
    (hk2 : 2 ≤ k) (hk : k ≤ 63) (hpw : e.trace pw = (2 : ZMod p) ^ k) {L : List ℕ}
    (hS : Noun.slot (e.trace axK).val (combL L) = some (.atom (e.trace l).val)) :
    (e.trace axK).val = 2 ^ k - 1 ∧ k = L.length ∧ (e.trace l).val = L.getLast! := by
  have hle : 2 ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) hk
  have h4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  have hax : (e.trace axK).val = 2 ^ k - 1 := by
    refine val_of_cast (by omega) ?_
    rw [(G2 H).1 hh, hpw, Nat.cast_sub (by omega)]; push_cast; ring
  refine ⟨hax, ?_⟩
  rw [hax] at hS
  rcases Nock.J9A.NounAx.slot_combL_atom hS with ⟨j, -, ha, -⟩ | ⟨h1, ha, hx⟩ | ⟨-, ha, -⟩
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact absurd ha.symm (by
      have := two_pow_sub_two_ne j (k' + 1) (by omega)
      exact this)
  · have h2 : 1 ≤ 2 ^ L.length := Nat.one_le_two_pow
    have : 2 ^ k = 2 ^ L.length := by omega
    exact ⟨Nat.pow_right_injective (le_refl 2) this, hx⟩
  · omega

/-- **The g4 form in ℕ** (`hpG`): two limbs `hi, lo < B` with `lo ≠ 0 → hi ≠ B − 1` have `hi·B + lo < p`. -/
theorem g4_lt_p {hi lo : ℕ} (hhi : hi < Nock.Atoms.B) (hlo : lo < Nock.Atoms.B)
    (hg : lo ≠ 0 → hi ≠ Nock.Atoms.B - 1) : hi * Nock.Atoms.B + lo < Nock.Atoms.p := by
  rw [Nock.Atoms.p_eq_limbs]
  have hB : Nock.Atoms.B = 4294967296 := Nock.Atoms.B_eq
  rw [hB] at hhi hlo hg ⊢
  by_cases h0 : lo = 0
  · subst h0; omega
  · have := hg h0; omega

/-- **S3 step R (route0)**: on an `r0h` row whose limbs `hi = l`, `lo = next.l` are below `B`, at Goldilocks the
emitted value is exact: `v.val = hi·B + lo < p`. -/
theorem step_route0 (hpG : p = Nock.Atoms.p) {e : Env (ZMod p)} (H : AxRowEqs e) (hr : e.trace r0h = 1)
    (hhi : (e.trace l).val < Nock.Atoms.B) (hlo : (e.traceNext l).val < Nock.Atoms.B) :
    e.traceNext cl = 1 ∧ (e.trace v).val = (e.trace l).val * Nock.Atoms.B + (e.traceNext l).val ∧
      (e.trace l).val * Nock.Atoms.B + (e.traceNext l).val < p := by
  obtain ⟨-, h7⟩ := G7 H
  obtain ⟨hc, hg, hv⟩ := h7 hr
  have hBp : Nock.Atoms.B < p := by rw [hpG]; have := Nock.Atoms.two_B_lt_p; omega
  have hBf : (Bf : ZMod p) = ((Nock.Atoms.B : ℕ) : ZMod p) := by norm_num [Bf, Nock.Atoms.B]
  have hg' : (e.traceNext l).val ≠ 0 → (e.trace l).val ≠ Nock.Atoms.B - 1 := by
    intro h0 hb
    refine hg (fun hz => h0 (by rw [hz, ZMod.val_zero])) ?_
    rw [hBf, ← ZMod.natCast_zmod_val (e.trace l), hb, Nat.cast_sub (by norm_num [Nock.Atoms.B] : 1 ≤ Nock.Atoms.B),
      Nat.cast_one]
  have hlt : (e.trace l).val * Nock.Atoms.B + (e.traceNext l).val < p := by
    exact lt_of_lt_of_eq (g4_lt_p hhi hlo hg') hpG.symm
  refine ⟨hc, val_of_cast hlt ?_, hlt⟩
  rw [hv, hBf]; push_cast; simp [ZMod.natCast_zmod_val]

/-- **S3 step F (a non-head segment axis)**: `axS = B + l` exactly, `< 2B < p`. -/
theorem step_axS_nonhead (hpG : p = Nock.Atoms.p) {e : Env (ZMod p)} (H : AxRowEqs e) (hh : e.trace head = 0)
    (hl : (e.trace l).val < Nock.Atoms.B) : (e.trace axS).val = Nock.Atoms.B + (e.trace l).val := by
  have h2B : 2 * Nock.Atoms.B < p := by rw [hpG]; exact Nock.Atoms.two_B_lt_p
  refine val_of_cast (by omega) ?_
  rw [(G3 H).2 hh, Nat.cast_add, ZMod.natCast_zmod_val]
  congr 1
  norm_num [Bf, Nock.Atoms.B]

/-- **S3 step F (the head's segment axis)**: `axS = l`. -/
theorem step_axS_head {e : Env (ZMod p)} (H : AxRowEqs e) (hh : e.trace head = 1) :
    (e.trace axS).val = (e.trace l).val := by rw [(G3 H).1 hh]

end Steps

end

end Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9
