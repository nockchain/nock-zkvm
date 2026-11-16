/-
  Nock/NockVMROM/Thm54/VclL/Chips/WalkChip.lean

  Columns: `LayoutW.lean` (`21 / 72 / 39`, width `132`).  Row `i` (0-based) is walk row `i + 1`.

  * **`F` gates**: the children are in-gate (`prefix 2p + b`, `len + 1`, root / rootIdx carried,
    child fp `= l | r`), so `F` holds by construction except the depth guard: the six certificate
    bits of `61 − len` (`len + Σ 2^i bᵢ − 61`) and the exclusion of `62, 63` (`u = b₁ b₂`,
    `u b₃ b₄ b₅ = 0`), on EVERY row.
  * **Root gate** on the preprocessed `rootMask` rows `0..kroots−1`: `prefix = 1`, `len = 0`,
    `rootIdx = idx`, `root = p` (`𝕂′`).
  * **Queue counter** (base field): `q₁ = kroots + fo₁ − 1`, `q′ = q + fo′ − 1`,
    `(1 − isLast)(q · qinv − 1)`, `isLast · q` — BFS queue validity and the forest tiling, with no
    coin event (`RowBridgeW`).
  * **IO**: ONE export consume per row, key `(p, l, r, idx, 0)` (the cell table's side-0 record,
    `Cell.xKeyS 0`), and two path records per row, `(root, l, 2·prefix, rootIdx)` and
    `(root, r, 2·prefix + 1, rootIdx)` (`Path.pRec`'s shape), with multiplicities `mL mR`; the export
    and path accumulators terminate at publics `0` and `2` (as the path chip).

  `s = 19 + 3 · 31 = 112`, `d = 4` (per-gate degrees checked by evaluation).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
import Nock.NockVMROM.Thm54.VclL.Chips.LayoutW

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

namespace WChip

/-! ## 1. Columns (`LayoutW`) -/

def isF : ℕ := 0
def isL : ℕ := 1
def rM : ℕ := 2
def idx : ℕ := 3
def pre : ℕ := 4
def ridx : ℕ := 5
def len : ℕ := 6
def cL : ℕ := 7
def cR : ℕ := 8
def e : ℕ := 9
def mL : ℕ := 10
def mR : ℕ := 11
def q : ℕ := 12
def qinv : ℕ := 13
def u : ℕ := 14
def bit0 : ℕ := 15

def pR : ℕ := 0
def lR : ℕ := 6
def rR : ℕ := 12
def rootR : ℕ := 18
def lnR : ℕ := 24
def cntR : ℕ := 25
def accR : ℕ := 26
def xInv : ℕ := 27
def pInvL : ℕ := 29
def pInvR : ℕ := 31
def xAcc : ℕ := 33
def pAcc : ℕ := 35

/-- Certificate bit `i`. -/
abbrev bt (i : ℕ) : CoeffExpr F := cv (bit0 + i)

/-! ## 2. The walk's `𝕂` expressions -/

/-- The walk coins: `α = χ₀` (`αC`), `γ = χ₁`. -/
def αE : MixedExpr F := .Var .challenge 0
def γE : MixedExpr F := .Var .challenge 1

/-- A listed sum of mixed expressions. -/
def sumME : List (MixedExpr F) → MixedExpr F
  | [] => .Const 0
  | x :: xs => .Add x (sumME xs)

/-- `RLC^γ(v) = Σ_c γ^c v_c` (trunk `Walk.rlc`), in-gate. -/
def rlcW (v : Fin 15 → MixedExpr F) : MixedExpr F :=
  sumME (List.ofFn fun c : Fin 15 => .Mul (.Pow γE (c : ℕ)) (v c))

def vecAt (k : VarKind) (bc : ℕ → CoeffExpr F) (nodeR : ℕ) (preE lenE : CoeffExpr F) :
    Fin 15 → MixedExpr F :=
  ![.Var k nodeR, .Var k (nodeR + 1), .Var k (nodeR + 2), .Var k (nodeR + 3), .Var k (nodeR + 4),
    .Var k (nodeR + 5), .Lift preE,
    .Var k rootR, .Var k (rootR + 1), .Var k (rootR + 2), .Var k (rootR + 3), .Var k (rootR + 4),
    .Var k (rootR + 5), .Lift (bc ridx), .Lift lenE]

/-- `RLC^γ(current)` of the row. -/
def curW (k : VarKind) (bc : ℕ → CoeffExpr F) : MixedExpr F :=
  rlcW (vecAt k bc pR (bc pre) (bc len))
/-- `RLC^γ` of the left child label `(l, 2p, root, rootIdx, len + 1)`. -/
def childLW (k : VarKind) (bc : ℕ → CoeffExpr F) : MixedExpr F :=
  rlcW (vecAt k bc lR (.mul (.const 2) (bc pre)) (.add (bc len) (.const 1)))
/-- `RLC^γ` of the right child label `(r, 2p + 1, root, rootIdx, len + 1)`. -/
def childRW (k : VarKind) (bc : ℕ → CoeffExpr F) : MixedExpr F :=
  rlcW (vecAt k bc rR (.add (.mul (.const 2) (bc pre)) (.const 1)) (.add (bc len) (.const 1)))

/-- `α^{fanout} = 1 + (cL + cR)(α − 1) + e(α − 1)²` (`e = cL cR`). -/
def afoW (bc : ℕ → CoeffExpr F) : MixedExpr F :=
  .Add (.Const 1) (.Add (.Scale (.add (bc cL) (bc cR)) (.Sub αE (.Const 1)))
    (.Scale (bc e) (.Mul (.Sub αE (.Const 1)) (.Sub αE (.Const 1)))))

/-- `cc = Σ_{l ≤ fo} α^l · child_l = cL α L + cR α R + e α(α − 1) R`. -/
def ccW (k : VarKind) (bc : ℕ → CoeffExpr F) : MixedExpr F :=
  .Add (.Scale (bc cL) (.Mul αE (childLW k bc)))
    (.Add (.Scale (bc cR) (.Mul αE (childRW k bc)))
      (.Scale (bc e) (.Mul (.Mul αE (.Sub αE (.Const 1))) (childRW k bc))))

/-- `initial_count = α^kroots`. -/
def αk (kroots : ℕ) : MixedExpr F := .Pow αE kroots

abbrev vC (r : ℕ) : MixedExpr F := .Var .traceCur r
abbrev vN (r : ℕ) : MixedExpr F := .Var .traceNext r

/-- **The walk gates** (`7` `𝕂`-gates, `WalkSatInGate`'s fields). -/
def walkGates (kroots : ℕ) : List (MixedExpr F) :=
  [ .Scale (cv isF) (.Sub (vC lnR) αE),
    .Scale (notE (cv isL)) (.Sub (vN lnR) (.Mul αE (vC lnR))),
    .Scale (cv isF) (.Sub (vC cntR) (.Mul (αk kroots) (afoW cv))),
    .Scale (notE (cv isL)) (.Sub (vN cntR) (.Mul (vC cntR) (afoW nv))),
    .Scale (cv isF) (.Sub (vC accR) (.Mul (αk kroots) (ccW .traceCur cv))),
    .Scale (notE (cv isL))
      (.Sub (.Add (.Scale (notE (nv rM)) (.Mul (vN lnR) (curW .traceNext nv)))
          (.Sub (vN accR) (vC accR)))
        (.Mul (vC cntR) (ccW .traceNext nv))),
    .Scale (cv isL) (vC accR) ]

/-! ## 3. Base gates -/

/-- **The walk chip's base-field gates** (`19`). -/
def baseGates (kroots : ℕ) : List (CoeffExpr F) :=
  [ boolE (cv cL), boolE (cv cR), .sub (cv e) (.mul (cv cL) (cv cR)),
    .sub (cv u) (.mul (bt 1) (bt 2)),
    .mul (.mul (cv u) (bt 3)) (.mul (bt 4) (bt 5)),
    .sub (.add (cv len) (bitSum bit0 6)) (.const 61),
    .mul (cv rM) (.sub (cv pre) (.const 1)),
    .mul (cv rM) (cv len),
    .mul (cv rM) (.sub (cv ridx) (cv idx)),
    .mul (cv isF) (.add (.sub (.sub (.sub (cv q) (.const (kroots : F))) (cv cL)) (cv cR)) (.const 1)),
    .mul (notE (cv isL)) (.add (.sub (.sub (.sub (nv q) (cv q)) (nv cL)) (nv cR)) (.const 1)),
    .mul (notE (cv isL)) (.sub (.mul (cv q) (cv qinv)) (.const 1)),
    .mul (cv isL) (cv q) ] ++
  (List.range 6).map fun i => boolE (bt i)

/-! ## 4. The `𝕂′` equations (IO) -/

/-- The consumed export key `(p, l, r, idx, 0)` (`Cell.xKeyS 0`'s shape). -/
def xKey : List (QE F) :=
  (QFP.var pR).entries ++ (QFP.var lR).entries ++ (QFP.var rR).entries ++
    [QE.base (cv idx), QE.base (cst 0)]
/-- The left record `(root, l, 2·prefix, rootIdx)` (`Path.pRec`'s shape). -/
def recL : List (QE F) :=
  (QFP.var rootR).entries ++ (QFP.var lR).entries ++
    [QE.base (.mul (cst 2) (cv pre)), QE.base (cv ridx)]
/-- The right record `(root, r, 2·prefix + 1, rootIdx)`. -/
def recR : List (QE F) :=
  (QFP.var rootR).entries ++ (QFP.var rR).entries ++
    [QE.base (.add (.mul (cst 2) (cv pre)) (cst 1)), QE.base (cv ridx)]

/-- The path accumulator's row term `mL·invL + mR·invR`. -/
def pTerm (cur : Bool) : QE F :=
  if cur then QE.add (QE.scale (cv mL) (QE.var pInvL)) (QE.scale (cv mR) (QE.var pInvR))
  else QE.add (QE.scale (nv mL) (QE.next pInvL)) (QE.scale (nv mR) (QE.next pInvR))

/-- **The walk chip's `𝕂′` equations** (`12`). -/
def qEqs (δF : F) : List (QE F) :=
  (QFP.scale (cv rM) (QFP.sub (QFP.var rootR) (QFP.var pR))).entries ++
  [ QE.sub (QE.mul δF (QE.var xInv) (den δF xKey)) QE.one,
    QE.sub (QE.mul δF (QE.var pInvL) (den δF recL)) QE.one,
    QE.sub (QE.mul δF (QE.var pInvR) (den δF recR)) QE.one,
    QE.scale (cv isF) (QE.sub (QE.var xAcc) (QE.var xInv)),
    QE.scale (notE (cv isL)) (QE.sub (QE.sub (QE.next xAcc) (QE.var xAcc)) (QE.next xInv)),
    QE.scale (cv isL) (QE.sub (QE.var xAcc) (QE.pub 0)),
    QE.scale (cv isF) (QE.sub (QE.var pAcc) (pTerm true)),
    QE.scale (notE (cv isL)) (QE.sub (QE.sub (QE.next pAcc) (QE.var pAcc)) (pTerm false)),
    QE.scale (cv isL) (QE.sub (QE.var pAcc) (QE.pub 2)) ]

/-- **All mixed gates** (`31`): the walk's `7` and the `2 · 12` IO coordinates. -/
def mixedGates (δF : F) (kroots : ℕ) : List (MixedExpr F) :=
  walkGates kroots ++ (qEqs δF).flatMap QE.gates

end WChip

/-! ## 5. Degrees, checked by evaluation -/

open WChip in
theorem walkBase_deg_all (kroots : ℕ) :
    ((WChip.baseGates (F := F) kroots).map CoeffExpr.degree).all (fun n => decide (n ≤ 4)) = true := by
  simp [WChip.baseGates, bitSum_degree_le4, CoeffExpr.degree]

open WChip in
theorem walkMixed_deg_all (δF : F) (kroots : ℕ) :
    ((WChip.mixedGates δF kroots).map MixedExpr.degree).all (fun n => decide (n ≤ 4)) = true := by
  simp [WChip.mixedGates, WChip.walkGates, WChip.qEqs, WChip.xKey, WChip.recL, WChip.recR,
    WChip.pTerm, WChip.curW, WChip.childLW, WChip.childRW, WChip.afoW, WChip.ccW, WChip.αk,
    WChip.αE, WChip.γE, WChip.rlcW, WChip.sumME, WChip.vecAt, List.ofFn_succ, QE.gates, QE.var,
    QE.next, QE.chal, QE.pub, QE.base, QE.zero, QE.one, QE.add, QE.sub, QE.mul, QE.scale,
    QE.rlc, QE.gpow, QFP.var, QFP.next, QFP.entries, QFP.sub, QFP.add, QFP.scale, QFP.gates, den,
    rQ, MixedExpr.degree, CoeffExpr.degree, List.zipIdx]

theorem walkBase_deg (kroots : ℕ) : ∀ g ∈ WChip.baseGates (F := F) kroots, g.degree ≤ 4 :=
  forall_le_of_all _ _ _ (walkBase_deg_all kroots)
theorem walkMixed_deg (δF : F) (kroots : ℕ) :
    ∀ g ∈ WChip.mixedGates δF kroots, g.degree ≤ 4 :=
  forall_le_of_all _ _ _ (walkMixed_deg_all δF kroots)

theorem walkBase_length (kroots : ℕ) : (WChip.baseGates (F := F) kroots).length = 19 := by
  simp [WChip.baseGates]
theorem walkMixed_length (δF : F) (kroots : ℕ) : (WChip.mixedGates δF kroots).length = 31 := by
  simp [WChip.mixedGates, WChip.walkGates, WChip.qEqs, QFP.entries, QFP.scale, QE.gates]

/-! ## 6. The template and the chip -/

/-- **The walk chip template**: three rounds, base `21 / 0 / 0`, `𝕂`-roles `0 / 24 / 13`. -/
def walkTemplate (δF : F) (kroots : ℕ) : ChipTemplate F where
  rounds := 3
  rounds_pos := by decide
  baseColsOf := ![21, 0, 0]
  extColsOf := ![0, 24, 13]
  baseTransition := WChip.baseGates kroots
  extTransition := []
  mixedTransition := WChip.mixedGates δF kroots
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := walkBase_deg kroots
  extTransition_deg := by simp
  mixedTransition_deg := walkMixed_deg δF kroots
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

theorem walkTemplate_baseCols (δF : F) (kroots : ℕ) : (walkTemplate δF kroots).baseCols = 21 := by
  show (∑ r : Fin 3, (![21, 0, 0] : Fin 3 → ℕ) r) = 21
  decide
theorem walkTemplate_extCols (δF : F) (kroots : ℕ) : (walkTemplate δF kroots).extCols = 37 := by
  show (∑ r : Fin 3, (![0, 24, 13] : Fin 3 → ℕ) r) = 37
  decide

/-- Forest root mask: `1` on rows `0..kroots−1`, `0` after
(trunk `rootRowMask`, restated here so the VCL objects keep their import split). -/
def rootRowMaskW {n : ℕ} (nodes : Fin n → F) (kroots : ℕ) : F[X] :=
  Lagrange.interpolate Finset.univ nodes (fun i => if (i : ℕ) < kroots then 1 else 0)

theorem rootRowMaskW_eval {n : ℕ} (nodes : Fin n → F) (kroots : ℕ)
    (hnodes : Function.Injective nodes) (i : Fin n) :
    (rootRowMaskW nodes kroots).eval (nodes i) = (if (i : ℕ) < kroots then 1 else 0) :=
  Lagrange.eval_interpolate_at_node _ hnodes.injOn (Finset.mem_univ i)

section Chip
variable {K : Type} [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **The walk chip as a `FixedPreprocessingRAP`**: `expandChip` of `walkTemplate`, with the three
fixed columns `isFirst`, `isLast`, `rootMask` (round 0). -/
def walkChip (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    FixedPreprocessingRAP F where
  rap := expandChip (walkTemplate δF kroots) b (slotVal b 21 chals) (slotVal b 21 pubs) orbit
    (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 3
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 21 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes
    | 2 => rootRowMaskW nodes kroots

variable (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- **Walk chip fingerprint, MEASURED**: `w = 132` (`LayoutW.width`), `s = 112`, `d = 4`, `k = 3`. -/
theorem walkChip_fingerprint :
    (walkChip δF kroots b hn nodes orbit chals pubs).rap.w = 132 ∧
      (walkChip δF kroots b hn nodes orbit chals pubs).rap.s = 112 ∧
      (walkChip δF kroots b hn nodes orbit chals pubs).rap.d = 4 ∧
      (walkChip δF kroots b hn nodes orbit chals pubs).rap.k = 3 := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · show (walkTemplate δF kroots).baseCols + (walkTemplate δF kroots).extCols * 3 = 132
    rw [walkTemplate_baseCols, walkTemplate_extCols]
  · rw [show (walkChip δF kroots b hn nodes orbit chals pubs).rap =
        expandChip (walkTemplate δF kroots) b _ _ orbit _ from rfl, expandChip_s]
    simp only [walkTemplate, walkBase_length, walkMixed_length, List.length_nil]

/-- The chip's width is `LayoutW`'s. -/
theorem walkChip_width_layout :
    (walkChip δF kroots b hn nodes orbit chals pubs).rap.w = WalkW.width :=
  (walkChip_fingerprint δF kroots b hn nodes orbit chals pubs).1.trans WalkW.width_eq.symm

theorem walkChip_deg (i : Fin (walkChip δF kroots b hn nodes orbit chals pubs).rap.s) :
    ((walkChip δF kroots b hn nodes orbit chals pubs).rap.C i).totalDegree ≤ 4 := by
  have hd := (walkChip δF kroots b hn nodes orbit chals pubs).rap.C_deg i
  rwa [(walkChip_fingerprint δF kroots b hn nodes orbit chals pubs).2.2.1] at hd

end Chip

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
