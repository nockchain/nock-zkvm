/-
  Nock/NockVMROM/Thm54/VclL/Handle/AtomChipHQ.lean

* `atomTemplateHQ` = `cellTemplateHQ` (every original base and mixed gate verbatim) + base columns
    `130 .. 204` and `𝕂`-roles `36 .. 47`, with the §2.3 gates g1–g5, g7.0–g7.5, g8 and the consume
    accumulator `cAcc`.
    **Width `349` by `rfl`**,
    degree `≤ 4` by structural `simp` (`atomGates_deg`, `atomMixed_deg`).
  * `atomChipHQ_restrict_sat` / `atomChipHQ_restrict_cell_sat`: twin-accepted ⇒ `cellChipHQ`- and
    `cellChip`-accepted on the restricted trace (`expandChip_restrict`); `atomTable_accepts` is the
    cell table's T1 (`cellTable_accepts`, `TableAccepts` at the chip's coin `χ₂ + χ₃√δ`) VERBATIM on the
    restriction.  "At `y`": the atom table's challenge vector carries the limb coin `y` at `χ₂, χ₃`
    (frame wiring, U — `frameJ8` is card J-8a).
  * §2 (`inc_chain_sound`): the ℕ chain model; an inc row whose OLD node copy is genuine denotes the
    `+1` of the old limb list (`Carry 1`, A-1), so `val new = val old + 1` (A-1 `carry_val`), with the
    adjacent-row links.  §3: the field gates ⇒ the ℕ chain relations (`2B < char`).  §4: the honest
    two-row chain `2^64 + B − 1 ↦ 2^64 + B` at gate level.

  DEVIATIONS from §2.3 (gates only, no column; each is needed for `inc_chain_sound` or the degree
  bound and is labelled at its definition): `kR_o` booleanity, `(1 − inc)·c_out`, `inc·conv`,
  `mi·(1 − inc − conv)`; g7.3′ gains `c_out·kR_o·(1 − wR)` and `c_out·kR_o·(1 − next.inc)`; g7.4 drops
  the `inc` factor (degree 5 otherwise; `c_out ⇒ inc` by `(1 − inc)·c_out`) and its `t = B − 1`
  branch reads the two-limb row `(0, 1)` at the ADJACENT row `idx + 1` (no second consume, which
  §2.3 has no column for); the inc-record key puts `TAG_inc` LAST (§3.4: tag beyond the 4th entry). `OldGenuine` is
  discharged from the consume's served form `ConsumeServedQ` (§2b), the named hypothesis the atom
  export balance soundness (A-3s class) must supply. -/
import Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK
import Nock.Atoms.Carry

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.RangeHQ
open Module
open scoped Polynomial

/-! ## 1. Columns, gates, template, chip -/

/-- Added base columns (after `cellTemplateHQ`'s `130`). -/
def bitA : ℕ := 130   -- `aL` bits `130 .. 161`
def bitR : ℕ := 162   -- `aR` bits `162 .. 193`
def invT : ℕ := 194
def invB : ℕ := 195
def mb : ℕ := 196
def inc : ℕ := 197
def conv : ℕ := 198
def cout : ℕ := 199
def idxO : ℕ := 200
def lO : ℕ := 201
def kRO : ℕ := 202
def vRO : ℕ := 203
def mi : ℕ := 204

/-- Added `𝕂`-roles (after `cellTemplateHQ`'s `36`), as `𝕂′` pairs. -/
def mbInv : ℕ := 36
def mbAcc : ℕ := 38
def cInv : ℕ := 40
def miInv : ℕ := 42
def miAcc : ℕ := 44
/-- The old-export consume accumulator. -/
def cAcc : ℕ := 46
/-- Terminal publics (`𝕂′`): the external validity provide `6 / 7`, the inc-record provide `8 / 9`. -/
def pubMB : ℕ := 6
def pubMI : ℕ := 8
/-- The consume accumulator's terminal (`𝕂′`, `10 / 11`): the atom table's inc rows as a consumer of the
atom export balance (summand #4), beside the atom-walk instance. -/
def pubC : ℕ := 10
/-- The cell table's coin `z` as the atom chip reads it (its `χ₂, χ₃` carry `y`; frame wiring U). -/
def zAt {F : Type} : QE F := QE.chal 37 38

section Gates
variable {F : Type} [Field F]

/-- `B = 2^32` in the field. -/
def Bf : F := (2 : F) ^ 32

/-- `valR = wR·idR + (1 − wR)·aR`. -/
def valR : CoeffExpr F := CellH.valE Cell.wR Cell.idR Cell.aR

/-- **g1** limb bits: `aL = Σ 2^i b_i`, `aR = Σ 2^i b_{32+i}`, 64 booleanities. -/
def g1 : List (CoeffExpr F) :=
  [ .sub (cv Cell.aL) (bitSum bitA 32), .sub (cv Cell.aR) (bitSum bitR 32) ] ++
  (List.range 64).map fun i => boolE (cv (bitA + i))

/-- **g2** `wL = 0`; **g3** `(1 − wR)(aR·inv_t − 1)`. -/
def g23 : List (CoeffExpr F) :=
  [ cv Cell.wL, .mul (notE (cv Cell.wR)) (.sub (.mul (cv Cell.aR) (cv invT)) (.const 1)) ]

/-- The boundary condition of an exported two-limb row, selected by `m` (`mb`, or `mi`). -/
def bnd (m : ℕ) : List (CoeffExpr F) :=
  [ .mul (.mul (cv m) (notE (cv Cell.wR))) (.sub (cv Cell.aR) (.const (Bf - 1))),
    .mul (.mul (cv m) (notE (cv Cell.wR))) (.sub (.mul (cv Cell.aL) (cv invB)) (.const 1)) ]

/-- **g7.0** booleanity of `inc conv c_out`; DEVIATION (gates, no column): `kR_o` boolean,
`(1 − inc)·c_out` (`c_out ⇒ inc`), `inc·conv`, `mi·(1 − inc − conv)` (a chain head is an inc or a
conversion row). -/
def g70 : List (CoeffExpr F) :=
  [ boolE (cv inc), boolE (cv conv), boolE (cv cout), boolE (cv kRO),
    .mul (notE (cv inc)) (cv cout), .mul (cv inc) (cv conv),
    .mul (cv mi) (.sub (notE (cv inc)) (cv conv)) ]

/-- **g7.1** `inc·(aL − l_o − 1 + B·c_out)`. -/
def g71 : List (CoeffExpr F) :=
  [ .mul (cv inc) (.add (.sub (.sub (cv Cell.aL) (cv lO)) (.const 1)) (.mul (.const Bf) (cv cout))) ]

/-- **g7.2** stop: `inc·(1 − c_out)·(wR − kR_o)`, `inc·(1 − c_out)·(valR − vR_o)`. -/
def g72 : List (CoeffExpr F) :=
  [ .mul (.mul (cv inc) (notE (cv cout))) (.sub (cv Cell.wR) (cv kRO)),
    .mul (.mul (cv inc) (notE (cv cout))) (.sub valR (cv vRO)) ]

/-- **g7.3′** link (`c_out = 1`, `kR_o = 1`), adjacent rows: `idR = idx + 1`, `next.idx_o = vR_o`;
DEVIATION (gates): `wR = 1` and `next.inc = 1` (else the suffix is unconstrained). -/
def g73 : List (CoeffExpr F) :=
  [ .mul (.mul (.mul (cv inc) (cv cout)) (cv kRO)) (.sub (.sub (cv Cell.idR) (cv Cell.idx)) (.const 1)),
    .mul (.mul (.mul (cv inc) (cv cout)) (cv kRO)) (.sub (nv idxO) (cv vRO)),
    .mul (.mul (cv cout) (cv kRO)) (notE (cv Cell.wR)),
    .mul (.mul (cv cout) (cv kRO)) (notE (nv inc)) ]

/-- `c_out·(1 − kR_o)`: the overflow selector (the `inc` factor is implied by `(1 − inc)·c_out`). -/
def ovf : CoeffExpr F := .mul (cv cout) (notE (cv kRO))

/-- **g7.4** overflow (`c_out = 1`, `kR_o = 0`, `t = vR_o`): `wR = 0 ⇒ aR = t + 1`;
`wR = 1 ⇒ t = B − 1` and the ADJACENT row `idx + 1 = idR` is the two-limb row `(0, 1)`. -/
def g74 : List (CoeffExpr F) :=
  [ .mul (.mul ovf (notE (cv Cell.wR))) (.sub (.sub (cv Cell.aR) (cv vRO)) (.const 1)),
    .mul (.mul ovf (cv Cell.wR)) (.sub (cv vRO) (.const (Bf - 1))),
    .mul (.mul ovf (cv Cell.wR)) (.sub (.sub (cv Cell.idR) (cv Cell.idx)) (.const 1)),
    .mul (.mul ovf (cv Cell.wR)) (nv Cell.aL),
    .mul (.mul ovf (cv Cell.wR)) (nv Cell.wR),
    .mul (.mul ovf (cv Cell.wR)) (.sub (nv Cell.aR) (.const 1)) ]

/-- **g8** conversion: the row is `p = [1, B − 1]`. -/
def g8 : List (CoeffExpr F) :=
  [ .mul (cv conv) (.sub (cv Cell.aL) (.const 1)), .mul (cv conv) (.sub (cv Cell.aR) (.const (Bf - 1))),
    .mul (cv conv) (cv Cell.wR), .mul (cv conv) (cv Cell.wL) ]

/-- **The added base gates.** -/
def atomGates : List (CoeffExpr F) := g1 ++ g23 ++ bnd mb ++ bnd mi ++ g70 ++ g71 ++ g72 ++ g73 ++ g74 ++ g8

/-- The external validity-shaped key (g5): `(⟨z, 0, leaf_y⟩, 0 + 0√δ, idx)`. -/
def mbKey : List (QE F) := [zAt, QE.zero, QE.var (Cell.pR + 4), QE.zero, QE.base (cv Cell.idx)]

/-- The consumed old export record `(idx_o, 0, l_o, kR_o, vR_o)` (the shape of `CellH.keyH`). -/
def oldKey : List (CoeffExpr F) := [cv idxO, .const 0, cv lO, cv kRO, cv vRO]

/-- The `TAG_inc` constant. -/
def tagInc : F := 4

/-- The inc record `(h_old.k, h_old.v, h_new.k, h_new.v, TAG_inc)`: old `(2, idx_o)` on an inc row,
`(0, p − 1) = (0, −1)` on a conversion row; new `(2, idx)`. -/
def incKey : List (CoeffExpr F) :=
  [ .mul (.const 2) (notE (cv conv)),
    .sub (.mul (notE (cv conv)) (cv idxO)) (cv conv),
    .const 2, cv Cell.idx, .const tagInc ]

/-- **The added `𝕂′` gates**: g5 (inverse + accumulator, cell validity coins `γ′ρ′`), the old-export
consume inverse (handle coins), g7.5 (inverse + accumulator, handle coins). -/
def atomQ (δF : F) : List (QE F) :=
  [ QE.sub (QE.mul δF (QE.var mbInv) (den δF mbKey)) QE.one,
    QE.scale (cv Cell.isF) (QE.sub (QE.var mbAcc) (QE.scale (cv mb) (QE.var mbInv))),
    QE.scale (notE (cv Cell.isL)) (QE.sub (QE.sub (QE.next mbAcc) (QE.var mbAcc))
      (QE.scale (nv mb) (QE.next mbInv))),
    QE.scale (cv Cell.isL) (QE.sub (QE.var mbAcc) (QE.pub pubMB)),
    QE.sub (QE.mul δF (QE.var cInv) (HQ.denKeyQ δF oldKey)) QE.one,
    QE.scale (cv Cell.isF) (QE.sub (QE.var cAcc) (QE.scale (cv inc) (QE.var cInv))),
    QE.scale (notE (cv Cell.isL)) (QE.sub (QE.sub (QE.next cAcc) (QE.var cAcc))
      (QE.scale (nv inc) (QE.next cInv))),
    QE.scale (cv Cell.isL) (QE.sub (QE.var cAcc) (QE.pub pubC)),
    QE.sub (QE.mul δF (QE.var miInv) (HQ.denKeyQ δF incKey)) QE.one,
    QE.scale (cv Cell.isF) (QE.sub (QE.var miAcc) (QE.scale (cv mi) (QE.var miInv))),
    QE.scale (notE (cv Cell.isL)) (QE.sub (QE.sub (QE.next miAcc) (QE.var miAcc))
      (QE.scale (nv mi) (QE.next miInv))),
    QE.scale (cv Cell.isL) (QE.sub (QE.var miAcc) (QE.pub pubMI)) ]

def atomMixed (δF : F) : List (MixedExpr F) := (atomQ δF).flatMap QE.gates

theorem bitSum_deg (base n : ℕ) : (bitSum base n : CoeffExpr F).degree ≤ 1 :=
  CoeffExpr.degree_sumList_le _ _ 1 fun i _ => by simp [CoeffExpr.degree]

/-- **Degree `≤ 4`** for every added base gate (`simp` on the structural degree). -/
theorem atomGates_deg_all : (atomGates (F := F)).all (fun g => decide (g.degree ≤ 4)) = true := by
  have h1 := bitSum_deg (F := F) bitA 32
  have h2 := bitSum_deg (F := F) bitR 32
  simp [atomGates, g1, g23, bnd, g70, g71, g72, g73, ovf, g74, g8, CoeffExpr.degree, valR,
    CellH.valE, List.all_eq_true]
  omega

theorem atomGates_deg : ∀ g ∈ (atomGates (F := F)), g.degree ≤ 4 := by
  intro g hg; simpa using List.all_eq_true.mp atomGates_deg_all g hg

theorem atomMixed_deg_all (δF : F) : (atomMixed δF).all (fun g => decide (g.degree ≤ 4)) = true := by
  simp [atomMixed, atomQ, mbKey, oldKey, incKey, zAt, den, rQ, QE.rlc, QE.gpow, HQ.denKeyQ, HQ.rlcQ,
    HQ.gpowQ, HQ.gamQ, HQ.rhoQ, QE.gates, QE.var, QE.next, QE.chal, QE.pub, QE.base, QE.zero, QE.one,
    QE.add, QE.sub, QE.mul, QE.scale, MixedExpr.degree, CoeffExpr.degree]

theorem atomMixed_deg (δF : F) : ∀ g ∈ atomMixed δF, g.degree ≤ 4 := by
  intro g hg; simpa using List.all_eq_true.mp (atomMixed_deg_all δF) g hg

/-- **The atom table template**: `cellTemplateHQ` + 75 base columns + 12 `𝕂`-roles (round 2). -/
def atomTemplateHQ (δF : F) : ChipTemplate F where
  rounds := 3
  rounds_pos := by decide
  baseColsOf := ![205, 0, 0]
  extColsOf := ![0, 18, 30]
  baseTransition := Cell.baseGates ++ atomGates
  extTransition := []
  mixedTransition := Cell.mixedGates δF ++ CellHQ.gates δF ++ atomMixed δF
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact cellBase_deg g h
    · exact atomGates_deg g h
  extTransition_deg := by simp
  mixedTransition_deg := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact CellHQ.mixed_deg δF g h
    · exact atomMixed_deg δF g h
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

theorem atomTemplateHQ_baseCols (δF : F) : (atomTemplateHQ δF).baseCols = 205 := by
  show (∑ r : Fin 3, (![205, 0, 0] : Fin 3 → ℕ) r) = 205
  decide
theorem atomTemplateHQ_extCols (δF : F) : (atomTemplateHQ δF).extCols = 48 := by
  show (∑ r : Fin 3, (![0, 18, 30] : Fin 3 → ℕ) r) = 48
  decide

end Gates

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **`atomChipHQ`** (masks at `0`, `1`, as `cellChipHQ`). -/
noncomputable def atomChipHQ (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    FixedPreprocessingRAP F where
  rap := expandChip (atomTemplateHQ δF) b (slotVal b 205 chals) (slotVal b 205 pubs) orbit
    (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 205 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

variable (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

set_option maxRecDepth 20000 in
/-- **Width `349`** (`205 + 48·3`), by `rfl`. -/
theorem atomChipHQ_width : (atomChipHQ δF b hn nodes orbit chals pubs).rap.w = 349 := rfl

theorem atomGates_below_all : (atomGates (F := F)).all (colsBelow 205) = true := by
  simp [atomGates, g1, g23, bnd, g70, g71, g72, g73, ovf, g74, g8, colsBelow, bitSum,
    CoeffExpr.sumList, List.range_succ, valR, CellH.valE, Cell.wL, Cell.wR, Cell.aL, Cell.aR,
    Cell.idR, Cell.idx, bitA, bitR, invT, invB, mb, mi, inc, conv, cout, idxO, lO, kRO, vRO,
    List.all_eq_true]

theorem atomGates_below : ∀ g ∈ (atomGates (F := F)), colsBelow 205 g = true := by
  intro g hg; exact List.all_eq_true.mp atomGates_below_all g hg

theorem atomHQ_shift : ∀ j < (cellTemplateHQ δF).width 3,
    shiftCol 130 205 j < (atomTemplateHQ δF).width 3 :=
  shift_lt _ _ 130 205 (cellTemplateHQ_baseCols δF) (atomTemplateHQ_baseCols δF) (by omega)
    (by rw [cellTemplateHQ_extCols, atomTemplateHQ_extCols]; omega)

theorem atomCell_shift : ∀ j < (cellTemplate δF).width 3,
    shiftCol 129 205 j < (atomTemplateHQ δF).width 3 :=
  shift_lt _ _ 129 205 (cellTemplate_baseCols δF) (atomTemplateHQ_baseCols δF) (by omega)
    (by rw [cellTemplate_extCols, atomTemplateHQ_extCols]; omega)

/-- Restriction of an atom trace to `cellChipHQ`'s `238` columns. -/
noncomputable def restrictAtomQ (Q : Fin (atomChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X]) :
    Fin (cellChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X] :=
  restrictQ 130 205 (atomHQ_shift δF) Q

/-- Restriction of an atom trace to `cellChip`'s `225` columns. -/
noncomputable def restrictAtomCell
    (Q : Fin (atomChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X]) :
    Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X] :=
  restrictQ 129 205 (atomCell_shift δF) Q

/-- **`restrict`** (`expandChip_restrict`): atom-accepted ⇒ `cellChipHQ`-accepted on the restriction —
every ORIGINAL gate is the twin's, reading columns `< 130` and roles `< 36`. -/
theorem atomChipHQ_restrict_sat
    (Q : Fin (atomChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies
      (restrictAtomQ δF b hn nodes orbit chals pubs Q) := by
  obtain ⟨hB, hM, -, -⟩ := cellHQ_range δF
  exact expandChip_restrict b orbit (rowNodeSet nodes) chals pubs (cellTemplateHQ δF)
    (atomTemplateHQ δF) 130 205 (cellTemplateHQ_baseCols δF) (atomTemplateHQ_baseCols δF)
    (by omega) (by rw [cellTemplateHQ_extCols, atomTemplateHQ_extCols]; omega)
    (fun g hg => ⟨List.mem_append_left _ hg, by
      have := hB g hg; rwa [cellTemplateHQ_baseCols] at this⟩)
    (fun g hg => ⟨List.mem_append_left _ hg, by
      have := hM g hg; rwa [cellTemplateHQ_baseCols, cellTemplateHQ_extCols] at this⟩)
    rfl rfl Q hsat

/-- **`restrict` to the original cell chip** (`225` columns), the chip T1 is stated on. -/
theorem atomChipHQ_restrict_cell_sat
    (Q : Fin (atomChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies
      (restrictAtomCell δF b hn nodes orbit chals pubs Q) := by
  have hR : (cellTemplate δF).extCols = 32 := cellTemplate_extCols δF
  exact expandChip_restrict b orbit (rowNodeSet nodes) chals pubs (cellTemplate δF)
    (atomTemplateHQ δF) 129 205 (cellTemplate_baseCols δF) (atomTemplateHQ_baseCols δF)
    (by omega) (by rw [hR, atomTemplateHQ_extCols]; omega)
    (fun g hg => ⟨List.mem_append_left _ hg, cellBase_below g hg⟩)
    (fun g hg => ⟨List.mem_append_left _ (List.mem_append_left _ hg), by
      rw [hR]; exact cellMixed_below δF g hg⟩)
    rfl rfl Q hsat

/-- The preprocessing transfers (columns `0`, `1` are not shifted). -/
theorem atomChipHQ_restrict_bind
    (Q : Fin (atomChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hbind : (atomChipHQ δF b hn nodes orbit chals pubs).BindsPreprocessing Q) :
    (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing
      (restrictAtomCell δF b hn nodes orbit chals pubs Q) := by
  intro j
  have hj := hbind j
  fin_cases j
  · exact hj
  · exact hj

end Chip

/-! ### T1 verbatim on the restriction -/

section T1
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- **T1 at `y`, verbatim**: on an atom-accepted trace, the cell table read off the restriction
satisfies `TableAccepts` at the chip's coin `χ₂ + χ₃√δ` — which, in the atom table's challenge vector,
is the limb coin `y` (frame wiring U).  This is `cellTable_accepts` applied unchanged. -/
theorem atomTable_accepts (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hz : Quad.mk (algebraMap F K δF) (chals 2) (chals 3) ≠ 0)
    (Q : Fin (atomChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (atomChipHQ δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hnp : n < ringChar F)
    (hserved : ValidityServed (cellTableOf δF b nodes orbit chals pubs
      (restrictAtomCell δF b hn nodes orbit chals pubs Q)))
    (vl : List (VKey (Quad (algebraMap F K δF)))) :
    TableAccepts (Quad.mk (algebraMap F K δF) (chals 2) (chals 3))
      (cellTableOf δF b nodes orbit chals pubs (restrictAtomCell δF b hn nodes orbit chals pubs Q)) vl :=
  cellTable_accepts δF b hn nodes orbit chals pubs _
    (atomChipHQ_restrict_cell_sat δF b hn nodes orbit chals pubs Q hsat) hF hq hz
    (atomChipHQ_restrict_bind δF b hn nodes orbit chals pubs Q hbind) hinj hadj hnp hserved vl

end T1

/-! ## 2. The ℕ chain model and `inc_chain_sound` -/

open Nock.Atoms

/-- One atom-table row read in ℕ (the columns the chain touches; `idx` is the row's serial). -/
structure ARow where
  idx : ℕ
  aL : ℕ
  wR : ℕ
  idR : ℕ
  aR : ℕ
  inc : ℕ
  cout : ℕ
  idxO : ℕ
  lO : ℕ
  kRO : ℕ
  vRO : ℕ

/-- `valR` in ℕ: the suffix serial if weighted, the top limb otherwise. -/
def ARow.valR (a : ARow) : ℕ := if a.wR = 1 then a.idR else a.aR

/-- **The limb list a row denotes** (right comb; `[aL, aR]` at the deepest node). -/
inductive Denotes (r : ℕ → ARow) : ℕ → List ℕ → Prop
  | top {i : ℕ} : (r i).wR = 0 → Denotes r i [(r i).aL, (r i).aR]
  | step {i : ℕ} {l : List ℕ} : (r i).wR = 1 → Denotes r (r i).idR l → Denotes r i ((r i).aL :: l)

/-- Every row's limbs are `< B` (g1). -/
def LimbsBounded (r : ℕ → ARow) : Prop := ∀ j, (r j).aL < B ∧ (r j).aR < B

theorem Denotes.bounded {r : ℕ → ARow} (hB : LimbsBounded r) {i : ℕ} {l : List ℕ}
    (h : Denotes r i l) : ∀ x ∈ l, x < B := by
  induction h with
  | @top j _ => intro x hx; simp at hx; rcases hx with rfl | rfl; exact (hB j).1; exact (hB j).2
  | step _ _ ih => intro x hx; simp at hx; rcases hx with rfl | hx; exact (hB _).1; exact ih x hx

/-- **The ℕ chain relations at an inc row `i`** (what g7.0–g7.4 say over bit-certified limbs,
§3 `chainOK_of_gates`). -/
structure ChainOK (r : ℕ → ARow) (i : ℕ) : Prop where
  cout_le : (r i).cout ≤ 1
  kRO_le : (r i).kRO ≤ 1
  limb : (r i).aL + B * (r i).cout = (r i).lO + 1
  stop : (r i).cout = 0 → (r i).wR = (r i).kRO ∧ (r i).valR = (r i).vRO
  link : (r i).cout = 1 → (r i).kRO = 1 →
    (r i).wR = 1 ∧ (r i).idR = i + 1 ∧ (r (i + 1)).idxO = (r i).vRO ∧ (r (i + 1)).inc = 1
  ovf0 : (r i).cout = 1 → (r i).kRO = 0 → (r i).wR = 0 → (r i).aR = (r i).vRO + 1
  ovf1 : (r i).cout = 1 → (r i).kRO = 0 → (r i).wR = 1 →
    (r i).vRO = B - 1 ∧ (r i).idR = i + 1 ∧ (r (i + 1)).aL = 0 ∧ (r (i + 1)).wR = 0 ∧
      (r (i + 1)).aR = 1

/-- **The old-node copy is genuine**: `(l_o, kR_o, vR_o)` is row `idx_o`'s `(aL, wR, valR)` — what
the consumed export record `(idx_o, 0, l_o, kR_o, vR_o)` says once the atom export balance is
sound. -/
def OldGenuine (r : ℕ → ARow) (i : ℕ) : Prop :=
  (r (r i).idxO).aL = (r i).lO ∧ (r (r i).idxO).wR = (r i).kRO ∧ (r (r i).idxO).valR = (r i).vRO

/-- **`inc_chain_sound`**: on rows whose inc rows satisfy the chain relations and whose old-node
copies are genuine, an inc row `i` whose old handle denotes `l_old` itself denotes some `l_new` with
`Carry 1 l_old l_new` (A-1) — the adjacent-row link carries the chain down the suffix. -/
theorem inc_chain_carry {r : ℕ → ARow} (hB : LimbsBounded r) (hw : ∀ j, (r j).wR ≤ 1)
    (hok : ∀ j, (r j).inc = 1 → ChainOK r j) (hgen : ∀ j, (r j).inc = 1 → OldGenuine r j)
    {i : ℕ} {lold : List ℕ} (hinc : (r i).inc = 1) (hold : Denotes r (r i).idxO lold) :
    ∃ lnew, Denotes r i lnew ∧ Carry 1 lold lnew := by
  generalize ho : (r i).idxO = o at hold
  induction hold generalizing i with
  | @top o hwo =>
    obtain ⟨hl, hk, hv⟩ := hgen i hinc
    rw [ho] at hl hk hv
    have c := hok i hinc
    have hkR : (r i).kRO = 0 := by omega
    have hvR : (r i).vRO = (r o).aR := by rw [← hv]; simp [ARow.valR, hwo]
    have hBo := hB o
    have hBi := hB i
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp c.cout_le with h0 | h1
    · obtain ⟨hwR, hval⟩ := c.stop h0
      have hwi : (r i).wR = 0 := by omega
      have haR : (r i).aR = (r o).aR := by rw [← hvR, ← hval]; simp [ARow.valR, hwi]
      refine ⟨[(r i).aL, (r i).aR], Denotes.top hwi, ?_⟩
      rw [haR]
      refine Carry.cons le_rfl (Nat.zero_le _) hBi.1 ?_ ?_
      · have := c.limb; rw [h0] at this; omega
      · exact Carry.cons (Nat.zero_le _) (Nat.zero_le _) hBo.2 (by simp) Carry.nil0
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hw i) with hw0 | hw1
      · have haR := c.ovf0 h1 hkR hw0
        refine ⟨[(r i).aL, (r i).aR], Denotes.top hw0, ?_⟩
        refine Carry.cons le_rfl le_rfl hBi.1 ?_ ?_
        · have := c.limb; rw [h1] at this; omega
        · exact Carry.cons le_rfl (Nat.zero_le _) hBi.2 (by omega) Carry.nil0
      · obtain ⟨ht, hid, h0', hw0', h1'⟩ := c.ovf1 h1 hkR hw1
        have hd : Denotes r (r i).idR [0, 1] := by
          rw [hid]; have := Denotes.top (r := r) (i := i + 1) hw0'; rwa [h0', h1'] at this
        refine ⟨(r i).aL :: [0, 1], Denotes.step hw1 hd, ?_⟩
        refine Carry.cons le_rfl le_rfl hBi.1 ?_ ?_
        · have := c.limb; rw [h1] at this; omega
        · refine Carry.cons le_rfl le_rfl (by norm_num [B]) ?_ Carry.nil1
          have : (r o).aR = B - 1 := by omega
          rw [this]; norm_num [B]
  | @step o lrest hwo hrest ih =>
    obtain ⟨hl, hk, hv⟩ := hgen i hinc
    rw [ho] at hl hk hv
    have c := hok i hinc
    have hkR : (r i).kRO = 1 := by omega
    have hvR : (r i).vRO = (r o).idR := by rw [← hv]; simp [ARow.valR, hwo]
    have hBi := hB i
    have hbr := hrest.bounded hB
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp c.cout_le with h0 | h1
    · obtain ⟨hwR, hval⟩ := c.stop h0
      have hwi : (r i).wR = 1 := by omega
      have hid : (r i).idR = (r o).idR := by rw [← hvR, ← hval]; simp [ARow.valR, hwi]
      refine ⟨(r i).aL :: lrest, Denotes.step hwi (by rw [hid]; exact hrest), ?_⟩
      exact Carry.stop hbr le_rfl hBi.1 (by have := c.limb; rw [h0] at this; omega)
    · obtain ⟨hwi, hid, hnx, hninc⟩ := c.link h1 hkR
      obtain ⟨lnew, hd, hc⟩ := ih hninc (by rw [hnx, hvR])
      refine ⟨(r i).aL :: lnew, Denotes.step hwi (by rw [hid]; exact hd), ?_⟩
      exact Carry.cons le_rfl le_rfl hBi.1 (by have := c.limb; rw [h1] at this; omega) hc

/-- **`inc_chain_sound`**: `val new = val old + 1` (A-1 `carry_val`). -/
theorem inc_chain_sound {r : ℕ → ARow} (hB : LimbsBounded r) (hw : ∀ j, (r j).wR ≤ 1)
    (hok : ∀ j, (r j).inc = 1 → ChainOK r j) (hgen : ∀ j, (r j).inc = 1 → OldGenuine r j)
    {i : ℕ} {lold : List ℕ} (hinc : (r i).inc = 1) (hold : Denotes r (r i).idxO lold) :
    ∃ lnew, Denotes r i lnew ∧ val lnew = val lold + 1 := by
  obtain ⟨lnew, hd, hc⟩ := inc_chain_carry hB hw hok hgen hinc hold
  exact ⟨lnew, hd, carry_val hc⟩

/-- **g8, the conversion row**: a row with `aL = 1`, `wR = 0`, `aR = B − 1` denotes `p = [1, B − 1]`,
the `+1` of the small atom `p − 1` (A-1 `crossing`). -/
theorem conv_sound {r : ℕ → ARow} {i : ℕ} (h1 : (r i).aL = 1) (hw : (r i).wR = 0)
    (ht : (r i).aR = B - 1) :
    Denotes r i (limbs p) ∧ Carry 1 (limbs (p - 1)) (limbs p) ∧ val (limbs p) = (p - 1) + 1 := by
  refine ⟨?_, crossing, carry_val crossing⟩
  rw [limbs_p]; have := Denotes.top (r := r) hw; rwa [h1, ht] at this

/-! ## 3. Field gates ⇒ the ℕ chain relations -/

section Bridge
variable {F : Type} [Field F]

/-- Row `a`'s chain columns, read at the current row of `e`. -/
structure Reads (e : Env F) (a : ARow) : Prop where
  idx : e.trace Cell.idx = a.idx
  aL : e.trace Cell.aL = a.aL
  wR : e.trace Cell.wR = a.wR
  idR : e.trace Cell.idR = a.idR
  aR : e.trace Cell.aR = a.aR
  inc : e.trace inc = a.inc
  cout : e.trace cout = a.cout
  idxO : e.trace idxO = a.idxO
  lO : e.trace lO = a.lO
  kRO : e.trace kRO = a.kRO
  vRO : e.trace vRO = a.vRO

/-- The next row's columns the link gates read. -/
structure ReadsNext (e : Env F) (a : ARow) : Prop where
  idxO : e.traceNext idxO = a.idxO
  inc : e.traceNext inc = a.inc
  aL : e.traceNext Cell.aL = a.aL
  wR : e.traceNext Cell.wR = a.wR
  aR : e.traceNext Cell.aR = a.aR

/-- Every ℕ value a row carries is `< 2^62` (serials `< n`, limbs `< B`). -/
def ARow.Small (a : ARow) : Prop :=
  a.idx < 2 ^ 62 ∧ a.aL < 2 ^ 62 ∧ a.wR < 2 ^ 62 ∧ a.idR < 2 ^ 62 ∧ a.aR < 2 ^ 62 ∧ a.inc < 2 ^ 62 ∧
    a.cout < 2 ^ 62 ∧ a.idxO < 2 ^ 62 ∧ a.lO < 2 ^ 62 ∧ a.kRO < 2 ^ 62 ∧ a.vRO < 2 ^ 62

theorem cast_inj (hq : 2 ^ 63 < ringChar F) {x y : ℕ} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63)
    (h : (x : F) = y) : x = y :=
  CharP.natCast_injOn_Iio F (ringChar F) (show x < ringChar F by omega)
    (show y < ringChar F by omega) h

theorem cast_bool (hq : 2 ^ 63 < ringChar F) {x : ℕ} (hx : x < 2 ^ 63)
    (h : (x : F) * ((x : F) - 1) = 0) : x ≤ 1 := by
  rcases mul_eq_zero.mp h with h | h
  · have := cast_inj hq hx (by norm_num) (h.trans Nat.cast_zero.symm); omega
  · have := cast_inj hq hx (by norm_num) ((sub_eq_zero.mp h).trans Nat.cast_one.symm); omega

theorem Bf_eq : (Bf : F) = ((B : ℕ) : F) := by simp [Bf, B]; norm_num

/-- **The bridge**: at an inc row `i` whose current and next rows are read by `e` (`Reads`,
`ReadsNext`), every added base gate vanishing gives the ℕ relations `ChainOK r i`, provided the row
values are small (`< 2^62`; serials `< n`), the limbs `aL`, `l_o` are `< B` (g1 here, g1 at the old row), `wR` is boolean (the cell
base gate) and the serial is `i`; `2^63 < char F`. -/
theorem chainOK_of_gates (hq : 2 ^ 63 < ringChar F) {e : Env F} {r : ℕ → ARow} {i : ℕ}
    (hg : ∀ g ∈ (atomGates (F := F)), g.eval e = 0) (hr : Reads e (r i))
    (hn : ReadsNext e (r (i + 1))) (hs : (r i).Small) (hs' : (r (i + 1)).Small)
    (hidx : (r i).idx = i) (hwR : (r i).wR ≤ 1) (hinc : (r i).inc = 1)
    (hlimb : (r i).aL < B ∧ (r i).lO < B) :
    ChainOK r i := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := hs
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11⟩ := hs'
  have sub : ∀ (l : List (CoeffExpr F)), (∀ g ∈ l, g ∈ (atomGates (F := F))) →
      ∀ g ∈ l, g.eval e = 0 := fun l hl g h => hg g (hl g h)
  have h70 := sub g70 (fun g h => by simp [atomGates, h])
  have h71 := sub g71 (fun g h => by simp [atomGates, h])
  have h72 := sub g72 (fun g h => by simp [atomGates, h])
  have h73 := sub g73 (fun g h => by simp [atomGates, h])
  have h74 := sub g74 (fun g h => by simp [atomGates, h])
  simp only [g70, g71, g72, g73, g74, ovf, valR, CellH.valE, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, forall_const, implies_true, and_true, CoeffExpr.eval, hr.idx, hr.aL, hr.wR, hr.idR,
    hr.aR, hr.inc, hr.cout, hr.idxO, hr.lO, hr.kRO, hr.vRO, hn.idxO, hn.inc, hn.aL, hn.wR, hn.aR,
    hinc, hidx, Nat.cast_one, one_mul, mul_one] at h70 h71 h72 h73 h74
  obtain ⟨-, -, bc, bk, -, -, -⟩ := h70
  obtain ⟨a73, b73, c73, d73⟩ := h73
  obtain ⟨a74, b74, c74, d74, e74, f74⟩ := h74
  obtain ⟨a72, b72⟩ := h72
  have hc1 := cast_bool hq (by omega) bc
  have hk1 := cast_bool hq (by omega) bk
  have hBn : B = 4294967296 := B_eq
  have cast_eq : ∀ {x y : ℕ}, x < 2 ^ 63 → y < 2 ^ 63 → (x : F) = y → x = y :=
    fun hx hy h => cast_inj hq hx hy h
  have limb : (r i).aL + B * (r i).cout = (r i).lO + 1 := by
    have := hlimb.1; have := hlimb.2
    apply cast_eq (by rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc1 with h | h <;> rw [h] <;> omega)
      (by omega)
    push_cast; rw [← Bf_eq]; linear_combination h71
  refine ⟨hc1, hk1, limb, ?_, ?_, ?_, ?_⟩
  · intro h0
    rw [h0] at a72 b72
    simp only [Nat.cast_zero, sub_zero, one_mul] at a72 b72
    refine ⟨cast_eq (by omega) (by omega) (sub_eq_zero.mp a72), ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hwR with h | h
    · rw [h] at b72; simp only [Nat.cast_zero, zero_mul, sub_zero, one_mul, zero_add] at b72
      simpa [ARow.valR, h] using cast_eq (by omega) (by omega) (sub_eq_zero.mp b72)
    · rw [h] at b72; simp only [Nat.cast_one, one_mul, sub_self, zero_mul, add_zero] at b72
      simpa [ARow.valR, h] using cast_eq (by omega) (by omega) (sub_eq_zero.mp b72)
  · intro h1 hk
    rw [h1, hk] at a73 b73 c73 d73
    simp only [Nat.cast_one, one_mul] at a73 b73 c73 d73
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact cast_eq (by omega) (by norm_num) ((sub_eq_zero.mp c73).symm.trans Nat.cast_one.symm)
    · apply cast_eq (by omega) (by omega); push_cast; linear_combination a73
    · exact cast_eq (by omega) (by omega) (sub_eq_zero.mp b73)
    · exact cast_eq (by omega) (by norm_num) ((sub_eq_zero.mp d73).symm.trans Nat.cast_one.symm)
  · intro h1 hk hw0
    rw [h1, hk, hw0] at a74
    simp only [Nat.cast_one, Nat.cast_zero, sub_zero, one_mul] at a74
    apply cast_eq (by omega) (by omega); push_cast; linear_combination a74
  · intro h1 hk hw1
    rw [h1, hk, hw1] at b74 c74 d74 e74 f74
    simp only [Nat.cast_one, Nat.cast_zero, sub_zero, one_mul] at b74 c74 d74 e74 f74
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · apply cast_eq (by omega) (by omega)
      rw [Nat.cast_sub (by norm_num [B]), ← Bf_eq]; push_cast; linear_combination b74
    · apply cast_eq (by omega) (by omega); push_cast; linear_combination c74
    · exact cast_eq (by omega) (by norm_num) (d74.trans Nat.cast_zero.symm)
    · exact cast_eq (by omega) (by norm_num) (e74.trans Nat.cast_zero.symm)
    · exact cast_eq (by omega) (by norm_num) ((sub_eq_zero.mp f74).trans Nat.cast_one.symm)

/-! ### `OldGenuine` from the consume (the served form is the named A-3s-class hypothesis) -/

/-- **`ConsumeServedQ` — the named hypothesis** (the exact shape the atom export balance's soundness
must deliver; A-3s class, NOT proved here): on the atom table read by the row environments `env k`
(`k < n`), every inc row's consumed key `oldKey = (idx_o, 0, l_o, kR_o, vR_o)` equals the export key
`CellH.keyH = (idx, wL, valL, wR, valR)` PROVIDED by some row `j < n` of the same table.  It is what
summand #4 gives outside its IO event: the atom table's `mh` provide (the original `accHQ`, terminal
`4 / 5`) balances its consumers (`cAcc`, terminal `10 / 11`, and the atom-walk instance), so a consumed
key with nonzero multiplicity is a provided key (`consumed_left_of_balanced`-shaped, under `γH′ρH′`). -/
def ConsumeServedQ (env : ℕ → Env F) (n : ℕ) : Prop :=
  ∀ i < n, (env i).trace inc = 1 → ∃ j < n,
    (CellH.keyH : List (CoeffExpr F)).map (fun g => g.eval (env j)) =
      (oldKey : List (CoeffExpr F)).map (fun g => g.eval (env i))

/-- **`OldGenuine` from the consume.**  Given `ConsumeServedQ` and, at every row, the reads, `wL = 0`
(g2), `wR` boolean (cell base gate), small values and the serial `idx = k` (`cellChip_serial`), every
inc row's old-node copy is genuine. -/
theorem oldGenuine_of_served (hq : 2 ^ 63 < ringChar F) {env : ℕ → Env F} {r : ℕ → ARow} {n : ℕ}
    (hR : ∀ k < n, Reads (env k) (r k)) (hwL : ∀ k < n, (env k).trace Cell.wL = 0)
    (hwR : ∀ k < n, (r k).wR ≤ 1) (hs : ∀ k < n, (r k).Small) (hidx : ∀ k < n, (r k).idx = k)
    (hserved : ConsumeServedQ env n) : ∀ i < n, (r i).inc = 1 → OldGenuine r i := by
  intro i hi hinc
  have hRi := hR i hi
  obtain ⟨j, hj, hkey⟩ := hserved i hi (by rw [hRi.inc, hinc, Nat.cast_one])
  have hRj := hR j hj
  simp only [CellH.keyH, oldKey, CellH.valE, List.map_cons, List.map_nil, CoeffExpr.eval,
    List.cons.injEq, and_true, hwL j hj, hRj.idx, hRj.aL, hRj.wR, hRj.idR, hRj.aR, hRi.idxO, hRi.lO,
    hRi.kRO, hRi.vRO, sub_zero, zero_mul, one_mul, zero_add] at hkey
  obtain ⟨e1, -, e3, e4, e5⟩ := hkey
  obtain ⟨s1, s2, s3, s4, s5, -⟩ := hs j hj
  obtain ⟨-, -, -, -, -, -, -, t8, t9, t10, t11⟩ := hs i hi
  have ce : ∀ {x y : ℕ}, x < 2 ^ 62 → y < 2 ^ 62 → (x : F) = y → x = y :=
    fun hx hy h => cast_inj hq (by omega) (by omega) h
  have hjo : j = (r i).idxO := by rw [← hidx j hj]; exact ce s1 t8 e1
  subst hjo
  refine ⟨ce s2 t9 e3, ce s3 t10 e4, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hwR _ hj) with h | h
  · rw [h] at e5; simp only [Nat.cast_zero, zero_mul, sub_zero, one_mul, zero_add] at e5
    simpa [ARow.valR, h] using ce s5 t11 e5
  · rw [h] at e5; simp only [Nat.cast_one, one_mul, sub_self, zero_mul, add_zero] at e5
    simpa [ARow.valR, h] using ce s4 t11 e5

/-- **`inc_chain_sound` with `OldGenuine` discharged by the consume**: rows past `n` carry no inc. -/
theorem inc_chain_sound_of_served (hq : 2 ^ 63 < ringChar F) {env : ℕ → Env F} {r : ℕ → ARow}
    {n : ℕ} (hR : ∀ k < n, Reads (env k) (r k)) (hwL : ∀ k < n, (env k).trace Cell.wL = 0)
    (hs : ∀ k < n, (r k).Small) (hidx : ∀ k < n, (r k).idx = k)
    (hserved : ConsumeServedQ env n) (hout : ∀ k, n ≤ k → (r k).inc = 0)
    (hB : LimbsBounded r) (hw : ∀ j, (r j).wR ≤ 1) (hok : ∀ j, (r j).inc = 1 → ChainOK r j)
    {i : ℕ} {lold : List ℕ} (hinc : (r i).inc = 1) (hold : Denotes r (r i).idxO lold) :
    ∃ lnew, Denotes r i lnew ∧ val lnew = val lold + 1 := by
  refine inc_chain_sound hB hw hok (fun j hj => ?_) hinc hold
  by_cases hjn : j < n
  · exact oldGenuine_of_served hq hR hwL (fun k _ => hw k) hs hidx hserved j hjn hj
  · have := hout j (by omega); omega

end Bridge

/-! ## 4. The honest two-row chain `2^64 + B − 1 ↦ 2^64 + B` -/

section Example

/-- The rows: `0, 1` the old atom `[B − 1, 0, 1]` (`= 2^64 + B − 1`); `2, 3` its `+1` chain, the new
atom `[0, 1, 1]`: row `2` carries out (`c_out = 1`, adjacent link to row `3`), row `3` stops
(`c_out = 0`, its tail is the old row `1`'s top limb `1`). -/
def exRows : ℕ → ARow
  | 0 => ⟨0, B - 1, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩
  | 1 => ⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩
  | 2 => ⟨2, 0, 1, 3, 0, 1, 1, 0, B - 1, 1, 1⟩
  | 3 => ⟨3, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1⟩
  | j => ⟨j, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

theorem ex_old : Denotes exRows 0 [B - 1, 0, 1] :=
  Denotes.step (r := exRows) (i := 0) rfl (Denotes.top (r := exRows) (i := 1) rfl)

theorem ex_old_val : val [B - 1, 0, 1] = 2 ^ 64 + B - 1 := by simp [val_cons, B]

theorem ex_bounded : LimbsBounded exRows := by
  intro j
  rcases j with _ | _ | _ | _ | j <;> simp [exRows, B]

theorem ex_wR : ∀ j, (exRows j).wR ≤ 1 := by
  intro j; rcases j with _ | _ | _ | _ | j <;> simp [exRows]

theorem ex_genuine : ∀ j, (exRows j).inc = 1 → OldGenuine exRows j := by
  intro j hj
  rcases j with _ | _ | _ | _ | j <;> simp [exRows] at hj ⊢ <;> simp [OldGenuine, exRows, ARow.valR]

theorem ex_small : ∀ j, j < 5 → (exRows j).Small := by
  intro j hj
  rcases j with _ | _ | _ | _ | _ | j <;> simp [ARow.Small, exRows, B] <;> omega

variable {F : Type} [Field F]

/-- The honest bit pattern of the limbs `0`, `1`, `B − 1` (the only limbs of the example). -/
def exBit (a i : ℕ) : F := if a = B - 1 then 1 else if a = 1 ∧ i = 0 then 1 else 0

/-- The honest base columns of a row (multiplicities `mb = mi = 0`, `conv = 0`: the gate-level example
is the chain; `inv_t = aR⁻¹` on top rows). -/
def exCol (a : ARow) (c : ℕ) : F :=
  if c = Cell.idx then a.idx else if c = Cell.aL then a.aL else if c = Cell.wR then a.wR
  else if c = Cell.idR then a.idR else if c = Cell.aR then a.aR else if c = inc then a.inc
  else if c = cout then a.cout else if c = idxO then a.idxO else if c = lO then a.lO
  else if c = kRO then a.kRO else if c = vRO then a.vRO
  else if c = invT then (if a.wR = 0 then ((a.aR : ℕ) : F)⁻¹ else 0)
  else if bitA ≤ c ∧ c < bitA + 32 then exBit a.aL (c - bitA)
  else if bitR ≤ c ∧ c < bitR + 32 then exBit a.aR (c - bitR)
  else 0

/-- Row `j`'s base environment (next row `j + 1`). -/
def exEnv (j : ℕ) : Env F := ⟨exCol (exRows j), exCol (exRows (j + 1)), fun _ => 0, fun _ => 0⟩

theorem ex_reads (j : ℕ) : Reads (exEnv (F := F) j) (exRows j) := by
  constructor <;> simp [exEnv, exCol, Cell.idx, Cell.aL, Cell.wR, Cell.idR, Cell.aR, inc, cout, idxO,
    lO, kRO, vRO, invT]

theorem ex_readsNext (j : ℕ) : ReadsNext (exEnv (F := F) j) (exRows (j + 1)) := by
  constructor <;> simp [exEnv, exCol, Cell.idx, Cell.aL, Cell.wR, Cell.idR, Cell.aR, inc, cout, idxO,
    lO, kRO, vRO, invT]

theorem ex_bits (j i : ℕ) (hi : i < 64) :
    (boolE (cv (bitA + i)) : CoeffExpr F).eval (exEnv j) = 0 := by
  have h2 : ¬ (130 + i = 2) := by omega
  have h7 : ¬ (130 + i = 7) := by omega
  have h6 : ¬ (130 + i = 6) := by omega
  have h4 : ¬ (130 + i = 4) := by omega
  have h8 : ¬ (130 + i = 8) := by omega
  have h197 : ¬ (130 + i = 197) := by omega
  have h199 : ¬ (130 + i = 199) := by omega
  have h200 : ¬ (130 + i = 200) := by omega
  have h201 : ¬ (130 + i = 201) := by omega
  have h202 : ¬ (130 + i = 202) := by omega
  have h203 : ¬ (130 + i = 203) := by omega
  have h194 : ¬ (130 + i = 194) := by omega
  simp only [CoeffExpr.eval, exEnv, exCol, Cell.idx, Cell.aL, Cell.wR, Cell.idR, Cell.aR, inc, cout,
    idxO, lO, kRO, vRO, invT, bitA, bitR, h2, h7, h6, h4, h8, h197, h199, h200, h201, h202, h203, h194, if_false]
  have h : ∀ x : F, (x = 0 ∨ x = 1) → x * (x - 1) = 0 := by
    intro x hx; rcases hx with rfl | rfl <;> simp
  apply h; clear h
  simp only [exBit]
  by_cases h1 : 130 + i < 162
  · simp [h1]; split_ifs <;> simp <;> tauto
  · have h3 : (162 ≤ 130 + i) := by omega
    by_cases h4' : 130 + i < 194
    · simp [h1, h3, h4']; split_ifs <;> simp <;> first | (intro hn; contradiction) | (intro _; assumption)
    · have : ¬ (130 + i < 194) := h4'
      simp [h1, this]

theorem ex_gates (j : ℕ) (hj : j < 4) : ∀ g ∈ (atomGates (F := F)), g.eval (exEnv j) = 0 := by
  simp only [atomGates, g1, g23, bnd, g70, g71, g72, g73, ovf, g74, g8, valR, CellH.valE,
    List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map, List.mem_range,
    List.not_mem_nil, IsEmpty.forall_iff, forall_const, implies_true, and_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, fun i hi => ex_bits j i hi⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
  interval_cases j <;>
  simp [CoeffExpr.eval, bitSum, CoeffExpr.sumList, List.range_succ, exEnv, exCol, exRows, exBit,
    Cell.idx, Cell.aL, Cell.wL, Cell.wR, Cell.idR, Cell.aR, inc, cout, idxO, lO, kRO, vRO, invT, invB,
    mb, mi, conv, bitA, bitR, B, Bf] <;> norm_num

/-- **Gate level ⇒ chain relations** on the example: rows `2`, `3` satisfy `ChainOK` because every added
base gate vanishes at their honest environments (`ex_gates`) — through the bridge `chainOK_of_gates`. -/
theorem ex_chainOK_of_gates (hq : 2 ^ 63 < ringChar F) :
    ∀ j, (exRows j).inc = 1 → ChainOK exRows j := by
  intro j hj
  have hj4 : j = 2 ∨ j = 3 := by
    rcases j with _ | _ | _ | _ | j <;> simp [exRows] at hj ⊢
  have hlt : j < 4 := by omega
  refine chainOK_of_gates (F := F) hq (ex_gates j hlt) (ex_reads j) (ex_readsNext j)
    (ex_small j (by omega)) (ex_small (j + 1) (by omega)) ?_ (ex_wR j) hj ?_
  · rcases hj4 with rfl | rfl <;> rfl
  · rcases hj4 with rfl | rfl <;> simp [exRows, B]

/-- **The example, end to end at gate level**: the `+1` of `2^64 + B − 1` written by rows `2, 3` denotes
`2^64 + B`; the chain relations come from the gates (any field with `2^63 < char`). -/
theorem ex_inc_sound_of_gates (hq : 2 ^ 63 < ringChar F) :
    ∃ lnew, Denotes exRows 2 lnew ∧ val lnew = 2 ^ 64 + B := by
  obtain ⟨l, hd, hv⟩ := inc_chain_sound ex_bounded ex_wR (ex_chainOK_of_gates (F := F) hq) ex_genuine
    (i := 2) rfl ex_old
  refine ⟨l, hd, ?_⟩
  rw [hv, ex_old_val]; norm_num [B]

/-- The new atom is exactly `[0, 1, 1]` (the row-`2` carry, the row-`3` stop). -/
theorem ex_new : Denotes exRows 2 [0, 1, 1] ∧ val [0, 1, 1] = 2 ^ 64 + B := by
  refine ⟨Denotes.step (r := exRows) (i := 2) rfl (Denotes.top (r := exRows) (i := 3) rfl), ?_⟩
  simp [val_cons, B]

/-- **Negative control** (the limb gate is load-bearing): writing `2` instead of `1` in row `3`'s limb
violates `ChainOK` (g7.1 in ℕ), and at gate level g7.1 evaluates to `1 ≠ 0`. -/
theorem ex_wrong_limb_rejected :
    ¬ ChainOK (Function.update exRows 3 { exRows 3 with aL := 2 }) 3 := by
  intro h; have := h.limb; simp [exRows] at this

theorem ex_wrong_limb_gate :
    (CoeffExpr.mul (cv inc) (.add (.sub (.sub (cv Cell.aL) (cv lO)) (.const 1))
      (.mul (.const Bf) (cv cout))) : CoeffExpr F).eval
      ⟨exCol { exRows 3 with aL := 2 }, fun _ => 0, fun _ => 0, fun _ => 0⟩ = 1 := by
  simp [CoeffExpr.eval, exCol, exRows, Cell.idx, Cell.aL, Cell.wR, Cell.idR, Cell.aR, inc, cout, idxO,
    lO, kRO, vRO]; norm_num

/-- The example's consumes are served by its own provides: row `2` consumes row `0`'s export key,
row `3` row `1`'s (the concrete instance of `ConsumeServedQ`). -/
theorem ex_served : ConsumeServedQ (exEnv (F := F)) 4 := by
  intro i hi hinc
  interval_cases i
  · simp [exEnv, exCol, exRows, inc, Cell.idx, Cell.aL, Cell.wR, Cell.idR, Cell.aR, cout, idxO, lO,
      kRO, vRO, invT] at hinc
  · simp [exEnv, exCol, exRows, inc, Cell.idx, Cell.aL, Cell.wR, Cell.idR, Cell.aR, cout, idxO, lO,
      kRO, vRO, invT] at hinc
  · refine ⟨0, by omega, ?_⟩
    simp [CellH.keyH, oldKey, CellH.valE, CoeffExpr.eval, exEnv, exCol, exRows, Cell.idx, Cell.aL,
      Cell.wL, Cell.idL, Cell.wR, Cell.idR, Cell.aR, inc, cout, idxO, lO, kRO, vRO, invT, bitA, bitR]
  · refine ⟨1, by omega, ?_⟩
    simp [CellH.keyH, oldKey, CellH.valE, CoeffExpr.eval, exEnv, exCol, exRows, Cell.idx, Cell.aL,
      Cell.wL, Cell.idL, Cell.wR, Cell.idR, Cell.aR, inc, cout, idxO, lO, kRO, vRO, invT, bitA, bitR]

/-- **The example with `OldGenuine` discharged by the consume** (`ex_served`) instead of by hand. -/
theorem ex_inc_sound_of_served (hq : 2 ^ 63 < ringChar F) :
    ∃ lnew, Denotes exRows 2 lnew ∧ val lnew = 2 ^ 64 + B := by
  obtain ⟨l, hd, hv⟩ := inc_chain_sound_of_served (F := F) (n := 4) hq (fun k _ => ex_reads k)
    (fun k _ => by simp [exEnv, exCol, Cell.wL, Cell.idx, Cell.aL, Cell.wR, Cell.idR, Cell.aR, inc,
      cout, idxO, lO, kRO, vRO, invT, bitA, bitR])
    (fun k hk => ex_small k (by omega)) (fun k hk => by interval_cases k <;> rfl) ex_served
    (fun k hk => by rcases k with _ | _ | _ | _ | k <;> first | omega | simp [exRows])
    ex_bounded ex_wR (ex_chainOK_of_gates (F := F) hq) (i := 2) rfl ex_old
  refine ⟨l, hd, ?_⟩
  rw [hv, ex_old_val]; norm_num [B]

end Example

end Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ
