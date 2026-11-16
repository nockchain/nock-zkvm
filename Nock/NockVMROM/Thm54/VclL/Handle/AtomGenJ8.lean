/-
  Nock/NockVMROM/Thm54/VclL/Handle/AtomGenJ8.lean

  * **The pad row** (`PadAt`): the two-limb row `(aL, aR) = (0, 1)` with `wL = wR = 0`, every added atom column
    `130.. 204` at `padNew` (bit `bitR + 0 = 1` for `aR = 1`, `inv_t = 1 = aR⁻¹`, all others `0`: `inc conv c_out
    kR_o mb mi idx_o l_o vR_o inv_b` and the other `63` bits).  `aR = 1` (not `0`) is FORCED: g3
    `(1 − wR)(aR·inv_t − 1)` (the canonical-top-limb gate) has no solution at `wR = aR = 0` (`g3_rejects_zero_top`).
    The pad row is the cell `[0 1]` (atom `2^32`, not big: `extB` ignores it).
  * **`pad_atomGates`**: the pad row satisfies EVERY added base gate of `atomChipHQ` (g1 bits, g2/g3, both `bnd`,
    g7.0 – g7.4, g8), whatever its next row is (every next-row read is guarded by `c_out = 0` or `inc = 0`);
    **`pad_gL`**: and the ruled gate `isL·c_out` of `atomChipHQL`.
  * **`padExt`**: the generator's column function `rows ++ [pad]` on `Fin (n0 + 1)`;
    **`hlast_padExt`**: the last row's `c_out` is `0`, in EXACTLY the form `AtomChipHQL.atomChipHQL_accepts_honest`'s
    `hlast` takes (`∀ i : Fin n, i + 1 = n → newB cout i = 0`), by construction.
  * **`pad_sum`**: the pad row contributes `0` to each of the three atom accumulators (`mb`, `inc`, `mi`): the
    terminal public sums over `n0 + 1` rows equal the sums over the `n0` list rows.
  * **`EZ_pad` / `hbase_pad`**: at the honest row environment `HonestA8.EZ` of the padded trace, the last row is a
    `PadAt` row (given the cell-part columns `wL wR aL aR` of the last row are `0 0 0 1`), hence `hbase` holds there.
  * **`atomChipHQL_accepts_honest_pad`**: `AtomChipHQL.atomChipHQL_accepts_honest` at `newB = padExt newR padNew`
    with `hlast` DISCHARGED, `hbase` needed only on the `n0` list rows, the three terminal publics stated over the
    list rows only.

  REMAINS (hypotheses of `atomChipHQL_accepts_honest_pad`, not discharged here): `hsat0` (the cell-part honest
  trace INCLUDING the pad cell `[0 1]` accepted by `cellChipHQ`: `mv = mx = mx1 = mh = 0`, `lo = 1`, `idx = n0`, its
  fingerprints / inverses from the honest cell generator), `hpadC` (the cell part's pad columns), `hbaseR` (the
  list rows' gates, including the pre-pad row read against the pad as its next row; it is next-row-free whenever that
  row has `c_out·kR_o = c_out·wR = 0`, ARGUMENT, not compiled), `hz1 hz2 hz3` (non-vanishing denominators,
  INCLUDING the pad row: completeness bad events), and the list rows' honest values from `demandA` (no field-level
  row generator from `GenXRows.demandA` exists yet).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AtomGenJ8

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.RangeHQ
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ Nock.NockVMROM.Thm54.VclL.Handle.QGates
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL
open Module
open scoped Polynomial

/-! ## 1. The pad row at gate level -/

section Gates
variable {F : Type} [Field F]

/-- The pad row's added atom columns (`130.. 204`): `bitR + 0 = 1` (`aR = 1`), `inv_t = 1`, all others `0`. -/
def padNew (j : ℕ) : F := if j = bitR then 1 else if j = invT then 1 else 0

/-- **The inert pad row**: `wL = wR = 0`, `(aL, aR) = (0, 1)`, the atom columns at `padNew`. -/
structure PadAt (e : Env F) : Prop where
  wL : e.trace Cell.wL = 0
  wR : e.trace Cell.wR = 0
  aL : e.trace Cell.aL = 0
  aR : e.trace Cell.aR = 1
  new : ∀ j, 130 ≤ j → j < 205 → e.trace j = padNew j

/-- Negative control for the choice `aR = 1`: g3 rejects a top limb `aR = 0` at `wR = 0` (any `inv_t`). -/
theorem g3_rejects_zero_top (e : Env F) (hw : e.trace Cell.wR = 0) (ha : e.trace Cell.aR = 0) :
    ((.mul (notE (cv Cell.wR)) (.sub (.mul (cv Cell.aR) (cv invT)) (.const 1)) : CoeffExpr F)).eval e = -1 := by
  simp [CoeffExpr.eval, hw, ha]

theorem g3_mem : ((.mul (notE (cv Cell.wR)) (.sub (.mul (cv Cell.aR) (cv invT)) (.const 1)) : CoeffExpr F)) ∈
    (atomGates (F := F)) := by
  simp [atomGates, g23]

variable {e : Env F}

theorem PadAt.col (hp : PadAt e) (j : ℕ) (h1 : 130 ≤ j) (h2 : j < 205) (h3 : j ≠ bitR) (h4 : j ≠ invT) :
    e.trace j = 0 := by
  rw [hp.new j h1 h2]; simp [padNew, h3, h4]

theorem PadAt.inc0 (hp : PadAt e) : e.trace inc = 0 := hp.col _ (by decide) (by decide) (by decide) (by decide)
theorem PadAt.conv0 (hp : PadAt e) : e.trace conv = 0 := hp.col _ (by decide) (by decide) (by decide) (by decide)
theorem PadAt.cout0 (hp : PadAt e) : e.trace cout = 0 := hp.col _ (by decide) (by decide) (by decide) (by decide)
theorem PadAt.kRO0 (hp : PadAt e) : e.trace kRO = 0 := hp.col _ (by decide) (by decide) (by decide) (by decide)
theorem PadAt.mb0 (hp : PadAt e) : e.trace mb = 0 := hp.col _ (by decide) (by decide) (by decide) (by decide)
theorem PadAt.mi0 (hp : PadAt e) : e.trace mi = 0 := hp.col _ (by decide) (by decide) (by decide) (by decide)
theorem PadAt.invT1 (hp : PadAt e) : e.trace invT = 1 := by
  rw [hp.new _ (by decide) (by decide)]; simp [padNew, bitR, invT]

/-- Every bit column is boolean on the pad row. -/
theorem PadAt.bool (hp : PadAt e) (i : ℕ) (hi : i < 64) : (boolE (cv (bitA + i)) : CoeffExpr F).eval e = 0 := by
  have h1 : 130 ≤ bitA + i := by simp [bitA]
  have h2 : bitA + i < 205 := by simp [bitA]; omega
  have h4 : bitA + i ≠ AtomChipHQ.invT := by simp only [bitA, AtomChipHQ.invT]; omega
  simp only [CoeffExpr.eval, hp.new _ h1 h2, padNew, if_neg h4]
  split_ifs <;> simp

/-- `aL`'s bits are `0` on the pad row. -/
theorem PadAt.bitSumA (hp : PadAt e) : (bitSum bitA 32 : CoeffExpr F).eval e = 0 := by
  rw [bitSum, CoeffExpr.eval_sumList]
  apply List.sum_eq_zero
  intro x hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have := hp.col (bitA + i) (by simp [bitA]) (by simp [bitA]; omega) (by simp [bitA, bitR]; omega)
    (by simp only [bitA, AtomChipHQ.invT]; omega)
  simp [CoeffExpr.eval, this]

/-- `aR`'s bits read `1` on the pad row. -/
theorem PadAt.bitSumR (hp : PadAt e) : (bitSum bitR 32 : CoeffExpr F).eval e = 1 := by
  rw [bitSum, CoeffExpr.eval_sumList, show (32 : ℕ) = 31 + 1 from rfl, List.range_succ_eq_map, List.map_cons,
    List.sum_cons, List.map_map]
  have h0 : e.trace bitR = 1 := by
    rw [hp.new bitR (by decide) (by decide)]; simp [padNew]
  have hrest : (List.map ((fun i => (CoeffExpr.mul (.const ((2 : F) ^ i)) (cv (bitR + i))).eval e) ∘ Nat.succ)
      (List.range 31)).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map, List.mem_range, Function.comp] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have := hp.col (bitR + (i + 1)) (by simp only [bitR]; omega) (by simp only [bitR]; omega) (by simp only [bitR]; omega)
      (by simp only [bitR, AtomChipHQ.invT]; omega)
    simp [CoeffExpr.eval, this]
  rw [hrest]
  simp [CoeffExpr.eval, h0]

/-- **`pad_atomGates`**: the inert pad row satisfies every added base gate of `atomChipHQ` (whatever its next
row: every next-row read is guarded by `c_out = 0`). -/
theorem pad_atomGates (hp : PadAt e) : ∀ g ∈ (atomGates (F := F)), g.eval e = 0 := by
  have hA := hp.bitSumA
  have hR := hp.bitSumR
  have hinc := hp.inc0; have hconv := hp.conv0; have hcout := hp.cout0; have hk := hp.kRO0
  have hmb := hp.mb0; have hmi := hp.mi0; have hiT := hp.invT1
  have hwL := hp.wL; have hwR := hp.wR; have haL := hp.aL; have haR := hp.aR
  simp only [atomGates, g1, g23, bnd, g70, g71, g72, g73, ovf, g74, g8, valR, CellH.valE,
    List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map, List.mem_range,
    List.not_mem_nil, IsEmpty.forall_iff, forall_const, implies_true, and_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, fun i hi => hp.bool i hi⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
  simp [CoeffExpr.eval, hA, hR, hinc, hconv, hcout, hk, hmb, hmi, hiT, hwL, hwR, haL, haR]

/-- The ruled gate `isL·c_out` of `atomChipHQL` vanishes on the pad row (at any `isL`). -/
theorem pad_gL (hp : PadAt e) : (gL : CoeffExpr F).eval e = 0 := by
  simp [gL, CoeffExpr.eval, hp.cout0]

end Gates

/-! ## 2. The padded generator: `rows ++ [pad]`, `hlast` by construction -/

section Gen
variable {F : Type} [Field F]

/-- **The generator's column function** on `n0 + 1` rows: the `n0` list rows, then the pad row `pad`. -/
def padExt {n0 : ℕ} (c : ℕ → Fin n0 → F) (pad : ℕ → F) : ℕ → Fin (n0 + 1) → F :=
  fun j i => if h : (i : ℕ) < n0 then c j ⟨i, h⟩ else pad j

theorem padExt_last {n0 : ℕ} (c : ℕ → Fin n0 → F) (pad : ℕ → F) (j : ℕ) (i : Fin (n0 + 1))
    (hi : (i : ℕ) = n0) : padExt c pad j i = pad j := by
  simp [padExt, hi]

theorem padExt_row {n0 : ℕ} (c : ℕ → Fin n0 → F) (pad : ℕ → F) (j : ℕ) (i : Fin (n0 + 1))
    (hi : (i : ℕ) < n0) : padExt c pad j i = c j ⟨i, hi⟩ := by
  simp [padExt, hi]

/-- **`hlast_padExt`**: the padded generator's last row carries no carry-out — exactly `atomChipHQL_accepts_honest`'s
`hlast` at `n = n0 + 1`, `newB = padExt newR padNew`, for ANY list rows `newR`. -/
theorem hlast_padExt {n0 : ℕ} (newR : ℕ → Fin n0 → F) :
    ∀ i : Fin (n0 + 1), (i : ℕ) + 1 = n0 + 1 → padExt newR padNew cout i = 0 := by
  intro i hi
  rw [padExt_last newR padNew cout i (by omega)]
  simp [padNew, cout, bitR, invT]

/-- The pad row is `inc = c_out = mb = mi = 0` in the generator's columns. -/
theorem padNew_inert : (padNew inc : F) = 0 ∧ (padNew cout : F) = 0 ∧ (padNew mb : F) = 0 ∧
    (padNew mi : F) = 0 ∧ (padNew conv : F) = 0 := by
  simp [padNew, inc, cout, mb, mi, conv, bitR, invT]

end Gen

/-! ## 3. At the honest trace (`HonestA8`) -/

section Honest
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n0 : ℕ} (hn : 0 < n0 + 1)
  (nodes : Fin (n0 + 1) → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin (n0 + 1) → F) (newR : ℕ → Fin n0 → F)

/-- The pad row's index. -/
def lastI : Fin (n0 + 1) := ⟨n0, by omega⟩

/-- **`pad_sum`**: the pad row contributes `0` to an accumulator whose multiplicity column is inert on it:
the sum over the `n0 + 1` rows equals the sum over the `n0` list rows. -/
theorem pad_sum (m : ℕ) (hm : (padNew m : F) = 0) (d : Fin (n0 + 1) → Quad (algebraMap F K δF)) :
    ∑ j ∈ Finset.range (n0 + 1), liftQ δF (HonestA8.cNat j (padExt newR padNew m)) * (HonestA8.dNat δF d j)⁻¹ =
      ∑ j ∈ Finset.range n0, liftQ δF (HonestA8.cNat j (padExt newR padNew m)) * (HonestA8.dNat δF d j)⁻¹ := by
  rw [Finset.sum_range_succ]
  have : HonestA8.cNat n0 (padExt newR padNew m) = 0 := by
    simp only [HonestA8.cNat, dif_pos (show n0 < n0 + 1 by omega)]
    rw [padExt_last newR padNew m _ rfl, hm]
  rw [this]
  simp

/-- **`EZ_pad`**: at the honest row environment of the padded trace, the last row is the inert pad row, given the
cell part's `wL wR aL aR` there are `0 0 0 1`. -/
theorem EZ_pad (hinj : Function.Injective nodes)
    (hpadC : col Cell.wL (lastI (n0 := n0)) = 0 ∧ col Cell.wR (lastI (n0 := n0)) = 0 ∧
      col Cell.aL (lastI (n0 := n0)) = 0 ∧ col Cell.aR (lastI (n0 := n0)) = 1) :
    PadAt (HonestA8.EZ δF b hn nodes orbit chals pubs col (padExt newR padNew) lastI) := by
  have hWA : (atomTemplateHQ δF).width 3 = 349 := HonestA8.atomTemplateHQ_width δF
  have key : ∀ j, 2 ≤ j → j < 205 →
      (HonestA8.EZ δF b hn nodes orbit chals pubs col (padExt newR padNew) lastI).trace j =
        (if j < 130 then col j lastI else padNew j) := by
    intro j h2 h3
    unfold HonestA8.EZ
    rw [env_trace hn nodes hinj _ _ _ _ lastI (by rw [hWA]; omega : j < (atomTemplateHQ δF).width 3)]
    have h0 : j ≠ 0 := by omega
    have h1 : j ≠ 1 := by omega
    simp only [fullCol, h0, h1, if_false, HonestA8.colZ, extColF, HonestA8.newZ]
    by_cases hj : j < 130
    · simp [hj]
    · simp only [hj, if_false, h3, if_true, show j < 313 by omega]
      exact padExt_last newR padNew j lastI rfl
  obtain ⟨c1, c2, c3, c4⟩ := hpadC
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [key Cell.wL (by decide) (by decide)]; simpa [Cell.wL] using c1
  · rw [key Cell.wR (by decide) (by decide)]; simpa [Cell.wR] using c2
  · rw [key Cell.aL (by decide) (by decide)]; simpa [Cell.aL] using c3
  · rw [key Cell.aR (by decide) (by decide)]; simpa [Cell.aR] using c4
  · intro j h1 h2
    rw [key j (by omega) h2, if_neg (by omega)]

/-- **`hbase_pad`**: `HonestA8`'s `hbase` holds at the pad row. -/
theorem hbase_pad (hinj : Function.Injective nodes)
    (hpadC : col Cell.wL (lastI (n0 := n0)) = 0 ∧ col Cell.wR (lastI (n0 := n0)) = 0 ∧
      col Cell.aL (lastI (n0 := n0)) = 0 ∧ col Cell.aR (lastI (n0 := n0)) = 1) :
    ∀ g ∈ (atomGates (F := F)),
      g.eval (HonestA8.EZ δF b hn nodes orbit chals pubs col (padExt newR padNew) lastI) = 0 :=
  pad_atomGates (EZ_pad δF b hn nodes orbit chals pubs col newR hinj hpadC)

/-- **`atomChipHQL_accepts_honest_pad`**: honest acceptance by the variant chip `atomChipHQL` of the padded
generator `newB = padExt newR padNew` (the `n0` list rows, then the inert pad row): `hlast` DISCHARGED by
construction (`hlast_padExt`), `hbase` required only on the list rows (the pad row's is `hbase_pad`), the three
terminal publics stated over the list rows only (`pad_sum`). -/
theorem atomChipHQL_accepts_honest_pad (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin (n0 + 1)) (hi : (i : ℕ) + 1 < n0 + 1), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hsat0 : (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies (honestQ hn nodes col _))
    (hpadC : col Cell.wL (lastI (n0 := n0)) = 0 ∧ col Cell.wR (lastI (n0 := n0)) = 0 ∧
      col Cell.aL (lastI (n0 := n0)) = 0 ∧ col Cell.aR (lastI (n0 := n0)) = 1)
    (hbaseR : ∀ i : Fin (n0 + 1), (i : ℕ) < n0 → ∀ g ∈ (atomGates (F := F)),
      g.eval (HonestA8.EZ δF b hn nodes orbit chals pubs col (padExt newR padNew) i) = 0)
    (hz1 : ∀ i, HonestA8.dMB δF b hn nodes orbit chals pubs col (padExt newR padNew) i ≠ 0)
    (hz2 : ∀ i, HonestA8.dC δF b hn nodes orbit chals pubs col (padExt newR padNew) i ≠ 0)
    (hz3 : ∀ i, HonestA8.dMI δF b hn nodes orbit chals pubs col (padExt newR padNew) i ≠ 0)
    (hpMB : Quad.mk _ (pubs pubMB) (pubs (pubMB + 1)) = ∑ j ∈ Finset.range n0,
      liftQ δF (HonestA8.cNat j (padExt newR padNew mb)) *
        (HonestA8.dNat δF (HonestA8.dMB δF b hn nodes orbit chals pubs col (padExt newR padNew)) j)⁻¹)
    (hpC : Quad.mk _ (pubs pubC) (pubs (pubC + 1)) = ∑ j ∈ Finset.range n0,
      liftQ δF (HonestA8.cNat j (padExt newR padNew inc)) *
        (HonestA8.dNat δF (HonestA8.dC δF b hn nodes orbit chals pubs col (padExt newR padNew)) j)⁻¹)
    (hpMI : Quad.mk _ (pubs pubMI) (pubs (pubMI + 1)) = ∑ j ∈ Finset.range n0,
      liftQ δF (HonestA8.cNat j (padExt newR padNew mi)) *
        (HonestA8.dNat δF (HonestA8.dMI δF b hn nodes orbit chals pubs col (padExt newR padNew)) j)⁻¹) :
    (atomChipHQL δF b hn nodes orbit chals pubs).rap.Satisfies
      (ofHQ δF b hn nodes orbit chals pubs
        (HonestA8.atomTraceHQ δF b hn nodes orbit chals pubs col (padExt newR padNew))) := by
  obtain ⟨i1, i2, i3, i4, -⟩ := (padNew_inert (F := F))
  refine atomChipHQL_accepts_honest δF b hn nodes orbit chals pubs col (padExt newR padNew) hinj hadj hsat0
    ?_ hz1 hz2 hz3 ?_ ?_ ?_ (hlast_padExt newR)
  · intro i
    by_cases hi : (i : ℕ) < n0
    · exact hbaseR i hi
    · have : i = lastI := Fin.ext (by simp [lastI]; omega)
      subst this
      exact hbase_pad δF b hn nodes orbit chals pubs col newR hinj hpadC
  · rw [pad_sum δF newR mb i3]; exact hpMB
  · rw [pad_sum δF newR inc i1]; exact hpC
  · rw [pad_sum δF newR mi i4]; exact hpMI

end Honest

end Nock.NockVMROM.Thm54.VclL.Handle.AtomGenJ8
