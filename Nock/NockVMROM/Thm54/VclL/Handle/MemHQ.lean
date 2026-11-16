/-
  Nock/NockVMROM/Thm54/VclL/Handle/MemHQ.lean

  New chips beside `cellChipH` / `walkChipH`; no existing
  module is edited.

  * **`cellTemplateHQ`** = `cellTemplate` + the B0 multiplicity `mh` (column `129`, as `cellTemplateH`)
    + four `𝕂`-roles: the provide inverse `invHQ = (32, 33)` and the accumulator `accHQ = (34, 35)` as
    `𝕂′` pairs (`ChipRAP.QE`, Re at the first role, Im at the next), and four `𝕂′` gates (8 `𝕂`-gates):
    `invH′ · (ρH′ + Σ_k γH′^k · key_k) − 1` and the accumulator's init / step / terminal.  The key is
    `CellH.keyH` (unchanged).  Coins: `γH′ = χ₃₃ + χ₃₅√δ`, `ρH′ = χ₃₄ + χ₃₆√δ` (challenge leaves); the
    terminal is the `𝕂′` public at `4 / 5`.  **MEASURED `w = 238`.**
  * **`walkTemplateHQ`** = `walkTemplate` + the child handle columns `kL vL kR vR` (`21..24`, as
    `walkTemplateH`) + ten `𝕂`-roles: three provide/consume inverses and two accumulators as `𝕂′` pairs
    (`37..46`), the nine `walkTemplateH` gates over `𝕂′` (18 `𝕂`-gates).  Terminals: export `4 / 5`,
    path `6 / 7`.  **MEASURED `w = 166`.**
  * degree `≤ 4` for every gate; the read-set receipt that the original gates read only the original
    columns (reused: `cellBase_below`, `cellMixed_below`, `walkBase_below`, `walkMixed_below`) and the
    **restrictions** `cellChipHQ_restrict_sat` / `walkChipHQ_restrict_sat`: a `𝕂′`-twin-accepted trace,
    restricted to the original's columns, is accepted by `cellChip` / `walkChip` — so every theorem about
    the original chips applies unchanged (as for `cellChipH` / `walkChipH`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkH

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The `𝕂′` handle LogUp pieces (memory side) -/

namespace HQ

section Gates
variable {F : Type} [Field F]

/-- `𝕂′` handle coins at the memory challenge leaves: `γH′ = (33, 35)`, `ρH′ = (34, 36)`. -/
def gamQ : QE F := QE.chal 33 35
def rhoQ : QE F := QE.chal 34 36

/-- `γH′^m` (a product of coins, degree `0`). -/
def gpowQ (δF : F) : ℕ → QE F
  | 0 => QE.one
  | m + 1 => QE.mul δF gamQ (gpowQ δF m)

/-- `Σ_k γH′^k · lift(key_k)`. -/
def rlcQ (δF : F) : ℕ → List (CoeffExpr F) → QE F
  | _, [] => QE.zero
  | m, g :: r => QE.add (QE.mul δF (gpowQ δF m) (QE.base g)) (rlcQ δF (m + 1) r)

/-- The `𝕂′` denominator `ρH′ + Σ_k γH′^k · key_k`. -/
def denKeyQ (δF : F) (l : List (CoeffExpr F)) : QE F := QE.add rhoQ (rlcQ δF 0 l)

end Gates

end HQ

namespace CellHQ

section Gates
variable {F : Type} [Field F]

def invHQ : ℕ := 32
def accHQ : ℕ := 34
/-- The `𝕂′` terminal public `4 / 5`. -/
def pubHQ : ℕ := 4

/-- **The four `𝕂′` handle-export gates** (8 `𝕂`-gates). -/
def gatesQ (δF : F) : List (QE F) :=
  [ QE.sub (QE.mul δF (QE.var invHQ) (HQ.denKeyQ δF CellH.keyH)) QE.one,
    QE.scale (cv Cell.isF) (QE.sub (QE.var accHQ) (QE.scale (cv CellH.mh) (QE.var invHQ))),
    QE.scale (notE (cv Cell.isL)) (QE.sub (QE.sub (QE.next accHQ) (QE.var accHQ))
      (QE.scale (nv CellH.mh) (QE.next invHQ))),
    QE.scale (cv Cell.isL) (QE.sub (QE.var accHQ) (QE.pub pubHQ)) ]

def gates (δF : F) : List (MixedExpr F) := (gatesQ δF).flatMap QE.gates

theorem gates_deg_all (δF : F) : (gates δF).all (fun g => decide (g.degree ≤ 4)) = true := by
  simp [gates, gatesQ, HQ.denKeyQ, HQ.rlcQ, HQ.gpowQ, HQ.gamQ, HQ.rhoQ, CellH.keyH, CellH.valE,
    QE.gates, QE.var, QE.next, QE.chal, QE.pub, QE.base, QE.zero, QE.one, QE.add, QE.sub, QE.mul,
    QE.scale, MixedExpr.degree, CoeffExpr.degree]

theorem mixed_deg (δF : F) : ∀ g ∈ Cell.mixedGates δF ++ gates δF, g.degree ≤ 4 := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact cellMixed_deg δF g hg
  · simpa using List.all_eq_true.mp (gates_deg_all δF) g hg

end Gates

end CellHQ

namespace WalkHQ

section Gates
variable {F : Type} [Field F]

/-- `𝕂′` roles after the original's `37`: inverses `37 / 39 / 41`, accumulators `43 / 45`. -/
def hxInvQ : ℕ := 37
def hpInvLQ : ℕ := 39
def hpInvRQ : ℕ := 41
def hxAccQ : ℕ := 43
def hpAccQ : ℕ := 45
/-- `𝕂′` terminal publics: export `4 / 5`, path `6 / 7`. -/
def pubXQ : ℕ := 4
def pubPQ : ℕ := 6

def pTermQ (cur : Bool) : QE F :=
  if cur then QE.add (QE.scale (cv WChip.mL) (QE.var hpInvLQ)) (QE.scale (cv WChip.mR) (QE.var hpInvRQ))
  else QE.add (QE.scale (nv WChip.mL) (QE.next hpInvLQ)) (QE.scale (nv WChip.mR) (QE.next hpInvRQ))

/-- **The nine `𝕂′` handle gates** (18 `𝕂`-gates): three inverses, two accumulators. -/
def gatesQ (δF : F) : List (QE F) :=
  [ QE.sub (QE.mul δF (QE.var hxInvQ) (HQ.denKeyQ δF WalkHC.xKeyH)) QE.one,
    QE.sub (QE.mul δF (QE.var hpInvLQ) (HQ.denKeyQ δF WalkHC.recLH)) QE.one,
    QE.sub (QE.mul δF (QE.var hpInvRQ) (HQ.denKeyQ δF WalkHC.recRH)) QE.one,
    QE.scale (cv WChip.isF) (QE.sub (QE.var hxAccQ) (QE.var hxInvQ)),
    QE.scale (notE (cv WChip.isL)) (QE.sub (QE.sub (QE.next hxAccQ) (QE.var hxAccQ)) (QE.next hxInvQ)),
    QE.scale (cv WChip.isL) (QE.sub (QE.var hxAccQ) (QE.pub pubXQ)),
    QE.scale (cv WChip.isF) (QE.sub (QE.var hpAccQ) (pTermQ true)),
    QE.scale (notE (cv WChip.isL)) (QE.sub (QE.sub (QE.next hpAccQ) (QE.var hpAccQ)) (pTermQ false)),
    QE.scale (cv WChip.isL) (QE.sub (QE.var hpAccQ) (QE.pub pubPQ)) ]

def gates (δF : F) : List (MixedExpr F) := (gatesQ δF).flatMap QE.gates

theorem gates_deg_all (δF : F) : (gates δF).all (fun g => decide (g.degree ≤ 4)) = true := by
  simp [gates, gatesQ, pTermQ, HQ.denKeyQ, HQ.rlcQ, HQ.gpowQ, HQ.gamQ, HQ.rhoQ, WalkHC.xKeyH,
    WalkHC.recLH, WalkHC.recRH, QE.gates, QE.var, QE.next, QE.chal, QE.pub, QE.base, QE.zero, QE.one,
    QE.add, QE.sub, QE.mul, QE.scale, MixedExpr.degree, CoeffExpr.degree]

theorem mixed_deg (δF : F) (kroots : ℕ) :
    ∀ g ∈ WChip.mixedGates δF kroots ++ gates δF, g.degree ≤ 4 := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact walkMixed_deg δF kroots g hg
  · simpa using List.all_eq_true.mp (gates_deg_all δF) g hg

end Gates

end WalkHQ

/-! ## 2. The templates -/

section Template
variable {F : Type} [Field F]

/-- **The `𝕂′` cell twin template**: base `130`, `𝕂`-roles `0 / 18 / 18`. -/
def cellTemplateHQ (δF : F) : ChipTemplate F where
  rounds := 3
  rounds_pos := by decide
  baseColsOf := ![130, 0, 0]
  extColsOf := ![0, 18, 18]
  baseTransition := Cell.baseGates
  extTransition := []
  mixedTransition := Cell.mixedGates δF ++ CellHQ.gates δF
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := cellBase_deg
  extTransition_deg := by simp
  mixedTransition_deg := CellHQ.mixed_deg δF
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

theorem cellTemplateHQ_baseCols (δF : F) : (cellTemplateHQ δF).baseCols = 130 := by
  show (∑ r : Fin 3, (![130, 0, 0] : Fin 3 → ℕ) r) = 130
  decide
theorem cellTemplateHQ_extCols (δF : F) : (cellTemplateHQ δF).extCols = 36 := by
  show (∑ r : Fin 3, (![0, 18, 18] : Fin 3 → ℕ) r) = 36
  decide

/-- **The `𝕂′` walk twin template**: base `25 / 0 / 0`, `𝕂`-roles `0 / 24 / 23`. -/
def walkTemplateHQ (δF : F) (kroots : ℕ) : ChipTemplate F where
  rounds := 3
  rounds_pos := by decide
  baseColsOf := ![25, 0, 0]
  extColsOf := ![0, 24, 23]
  baseTransition := WChip.baseGates kroots ++ WalkHC.baseH
  extTransition := []
  mixedTransition := WChip.mixedGates δF kroots ++ WalkHQ.gates δF
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := WalkHC.base_deg kroots
  extTransition_deg := by simp
  mixedTransition_deg := WalkHQ.mixed_deg δF kroots
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

theorem walkTemplateHQ_baseCols (δF : F) (kroots : ℕ) : (walkTemplateHQ δF kroots).baseCols = 25 := by
  show (∑ r : Fin 3, (![25, 0, 0] : Fin 3 → ℕ) r) = 25
  decide
theorem walkTemplateHQ_extCols (δF : F) (kroots : ℕ) : (walkTemplateHQ δF kroots).extCols = 47 := by
  show (∑ r : Fin 3, (![0, 24, 23] : Fin 3 → ℕ) r) = 47
  decide

end Template

/-! ## 3. The chips, widths and restrictions -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **The `𝕂′` cell twin chip** (masks at `0`, `1`). -/
def cellChipHQ (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) : FixedPreprocessingRAP F where
  rap := expandChip (cellTemplateHQ δF) b (slotVal b 130 chals) (slotVal b 130 pubs) orbit
    (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 130 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

/-- **The `𝕂′` walk twin chip** (masks `isFirst isLast rootMask` at `0..2`). -/
def walkChipHQ (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    FixedPreprocessingRAP F where
  rap := expandChip (walkTemplateHQ δF kroots) b (slotVal b 25 chals) (slotVal b 25 pubs) orbit
    (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 3
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 25 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes
    | 2 => rootRowMaskW nodes kroots

variable (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- **The `𝕂′` cell twin's width, MEASURED: `238`** (`232 + 2` more `𝕂`-roles: the Im halves). -/
theorem cellChipHQ_width : (cellChipHQ δF b hn nodes orbit chals pubs).rap.w = 238 := by
  show (cellTemplateHQ δF).baseCols + (cellTemplateHQ δF).extCols * 3 = 238
  rw [cellTemplateHQ_baseCols, cellTemplateHQ_extCols]

/-- **The `𝕂′` walk twin's width, MEASURED: `166`** (`151 + 5` more `𝕂`-roles: the Im halves). -/
theorem walkChipHQ_width : (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.w = 166 := by
  show (walkTemplateHQ δF kroots).baseCols + (walkTemplateHQ δF kroots).extCols * 3 = 166
  rw [walkTemplateHQ_baseCols, walkTemplateHQ_extCols]

theorem cellHQ_shift : ∀ j < (cellTemplate δF).width 3,
    shiftCol 129 130 j < (cellTemplateHQ δF).width 3 :=
  shift_lt _ _ 129 130 (cellTemplate_baseCols δF) (cellTemplateHQ_baseCols δF) (by omega)
    (by rw [cellTemplate_extCols, cellTemplateHQ_extCols]; omega)

theorem walkHQ_shift : ∀ j < (walkTemplate δF kroots).width 3,
    shiftCol 21 25 j < (walkTemplateHQ δF kroots).width 3 :=
  shift_lt _ _ 21 25 (walkTemplate_baseCols δF kroots) (walkTemplateHQ_baseCols δF kroots) (by omega)
    (by rw [walkTemplate_extCols, walkTemplateHQ_extCols]; omega)

/-- The restriction of a `𝕂′` cell twin trace to the original cell chip's `225` columns. -/
def restrictCellQ (Q : Fin (cellChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X]) :
    Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X] :=
  restrictQ 129 130 (cellHQ_shift δF) Q

/-- The restriction of a `𝕂′` walk twin trace to the original walk chip's `132` columns. -/
def restrictWalkQ (Q : Fin (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.w → F[X]) :
    Fin (walkChip δF kroots b hn nodes orbit chals pubs).rap.w → F[X] :=
  restrictQ 21 25 (walkHQ_shift δF kroots) Q

/-- **`𝕂′` cell twin acceptance ⇒ original cell acceptance** of the restriction. -/
theorem cellChipHQ_restrict_sat (Q : Fin (cellChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies
      (restrictCellQ δF b hn nodes orbit chals pubs Q) := by
  have hR : (cellTemplate δF).extCols = 32 := cellTemplate_extCols δF
  exact expandChip_restrict b orbit (rowNodeSet nodes) chals pubs (cellTemplate δF)
    (cellTemplateHQ δF) 129 130 (cellTemplate_baseCols δF) (cellTemplateHQ_baseCols δF) (by omega)
    (by rw [hR, cellTemplateHQ_extCols]; omega)
    (fun g hg => ⟨hg, cellBase_below g hg⟩)
    (fun g hg => ⟨List.mem_append_left _ hg, by rw [hR]; exact cellMixed_below δF g hg⟩)
    rfl rfl Q hsat

/-- **`𝕂′` walk twin acceptance ⇒ original walk acceptance** of the restriction. -/
theorem walkChipHQ_restrict_sat (Q : Fin (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) :
    (walkChip δF kroots b hn nodes orbit chals pubs).rap.Satisfies
      (restrictWalkQ δF kroots b hn nodes orbit chals pubs Q) := by
  have hR : (walkTemplate δF kroots).extCols = 37 := walkTemplate_extCols δF kroots
  exact expandChip_restrict b orbit (rowNodeSet nodes) chals pubs (walkTemplate δF kroots)
    (walkTemplateHQ δF kroots) 21 25 (walkTemplate_baseCols δF kroots)
    (walkTemplateHQ_baseCols δF kroots) (by omega)
    (by rw [hR, walkTemplateHQ_extCols]; omega)
    (fun g hg => ⟨List.mem_append_left _ hg, walkBase_below kroots g hg⟩)
    (fun g hg => ⟨List.mem_append_left _ hg, by rw [hR]; exact walkMixed_below δF kroots g hg⟩)
    rfl rfl Q hsat

end Chip

/-! ## 4. -/

section Instrument
variable {F : Type} [Field F]

/-- Trace columns read by a base expression. -/
def colsOfB : CoeffExpr F → List ℕ
  | .const _ => []
  | .var .traceCur i => [i]
  | .var .traceNext i => [i]
  | .var _ _ => []
  | .add a b => colsOfB a ++ colsOfB b
  | .sub a b => colsOfB a ++ colsOfB b
  | .mul a b => colsOfB a ++ colsOfB b
  | .neg a => colsOfB a
  | .pow a _ => colsOfB a

/-- Base columns read by a mixed gate (through `Lift` leaves and scales). -/
def liftCols : MixedExpr F → List ℕ
  | .Lift g => colsOfB g
  | .Scale g u => colsOfB g ++ liftCols u
  | .Add x y => liftCols x ++ liftCols y
  | .Sub x y => liftCols x ++ liftCols y
  | .Mul x y => liftCols x ++ liftCols y
  | .Neg x => liftCols x
  | .Pow x _ => liftCols x
  | _ => []

/-- (Checked by the kernel on the closed instance `F = ℚ`, `δF = 7`; `δF` enters only as a `qmul`
constant, which the instrument does not read.) -/
theorem cellHQ_reads :
    (CellHQ.gates (F := ℚ) 7).all (fun g => (liftCols g).all fun c =>
      [Cell.idx, Cell.wL, Cell.idL, Cell.aL, Cell.wR, Cell.idR, Cell.aR, Cell.isF, Cell.isL,
        CellH.mh].contains c) = true := by decide +kernel

theorem walkHQ_reads :
    (WalkHQ.gates (F := ℚ) 7).all (fun g => (liftCols g).all fun c =>
      [WChip.idx, WalkHC.kL, WalkHC.vL, WalkHC.kR, WalkHC.vR, WChip.ridx, WChip.pre, WChip.isF,
        WChip.isL, WChip.mL, WChip.mR].contains c) = true := by decide +kernel

/-- **Positive control**: the instrument sees a column outside the allowed set (`Cell.lo`). -/
theorem cellHQ_reads_control :
    ((CellHQ.gates (F := ℚ) 7 ++ [QE.mul (7 : ℚ) (QE.var CellHQ.invHQ) (QE.base (cv Cell.lo))].flatMap QE.gates).all
      (fun g => (liftCols g).all fun c =>
        [Cell.idx, Cell.wL, Cell.idL, Cell.aL, Cell.wR, Cell.idR, Cell.aR, Cell.isF, Cell.isL,
          CellH.mh].contains c)) = false := by decide +kernel

end Instrument

end

end Nock.NockVMROM.Thm54.VclL.Handle
