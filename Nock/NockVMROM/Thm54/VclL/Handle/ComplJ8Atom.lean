/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Atom.lean

* §1 **Honest atom rows at gate level, for arbitrary big atoms.**  `NRow` is one atom-table row read in ℕ (the cell
    part's `idx idR wL wR aL aR` and the added `inc conv c_out idx_o l_o kR_o vR_o mb mi`); `RowOK r rn` is the ℕ
    honest-row condition (limbs `< B`, `wL = 0`, the canonical top limb, the `mb` / `mi` boundary of a two-limb big
    root, the inc-chain relations of `ChainOK` read forwards, the conversion row).  `ReadsN` / `ReadsNextN`: a row
    environment carries the row's values, the limb bits (`testBit`), `inv_t = aR⁻¹` on an atom-topped row and
    `inv_b = aL⁻¹`.  **`atomGates_of_rowOK`**: every added base gate of `atomChipHQ` (g1 .. g8) vanishes.  The next
    row is read only when `c_out = 1` (every next-row read of g7.3′ / g7.4 carries the factor `c_out`).
  * §2 **The ℕ honest rows of an atom table at the spec level**: `AtomTab` (rows' limb suffixes `sp`, the tail
    pointer `ix`, inc / conversion flags, `mb` / `mi`), `AtomTab.row` (the old copy of an inc row is the canonical
    `limbs (val (sp j) − 1)`), `AtomTab.Valid` (canonical spines, tail-closed, LINK ORDER, the inc chain continues
    while the old row carries into a suffix row, conversion rows, big `mb` / `mi` roots, the last row is not an inc
    row); **`rowOK_of_valid`**: every row of a valid table is `RowOK` against its successor (comb spines, inc carry
    chains with the stop / link / both overflow cases, conversion rows), `rows_ok`.
  * §3 **`hpair`** from `HonestPairX.pairOK_of_genX` and the two run binders.
  * §5 **The generator's link order**: `linkOrder_spec` — `GenAtom.linkOrder L` is duplicate-free, has `L`'s
    members, and every element's link successor (the row `[0 X]`'s suffix `X ∈ L`) is the NEXT element (`LinkNext`).
  * §6 **The generator's inc chains**: `incChain_step`, `incChain_inc` (the rows `incChain` marks inc are exactly the
    reached depths `Reach`), `incChain_ok` (every written row carries the chain fields of its old suffix), and the
    fold over the slow OP4 operands `stInv_infoOfP` (L0's `infoOfP` at the fixed fuel: inc rows = rows reached by some
    operand's chain, chain fields = the old suffix's, `conv` / `mi` only at conversion / chain-head roots).
  * §7 **The generator's atom table is a valid `AtomTab`** at Goldilocks: `tabOf` (rows `acs`, `info`, `mb`),
    `link_gen`, `conv_at`, `GenHyp` (the run facts: big atoms are big, the slow OP4 operands' atoms are table atoms,
    a conversion forces the `p` duplicate, `mb` at big roots), **`valid_gen`**: L0's `acsP` / `infoOfP` (fixed
    fuel) / `mb` satisfy `AtomTab.Valid`, hence `RowOK` at every row (`AtomTab.rows_ok`).
  * §8 **The run facts of a generated run**: `s4_row` (an OP4 row of `genX` has `sf1 = v`, `e = v + 1`, under the run
    binders), `genHyp_j8` (`GenHyp` of `j8DataOf` at Goldilocks), **`valid_j8`**: the generator's atom table is
    valid for every generated run at Goldilocks, from `hax` / `hop5` only.
  * §9 **The generator's columns are the honest rows'**: `row_info` (the `info` chain / flag fields and `mb` at row `j`
    are `(tabOf …).row j`'s), `row_cell` (the cell-part `idx aL aR wL wR idR` of atom row `j` are `GenMem.cellD`'s
    data of `acs[j]`), so `newOf ((tabOf …).row)` and `CellAt` are the generator's own columns.
  * §4 **`atomOK` at a good coin**: both chip views (`atomChipHQ`, `atomChipHQL`) satisfied and bound by the honest
    349-column trace, from `RowOK` at every row (`hbase`), L2's cell-part acceptance `hsat0`, the three non-vanishing
    atom denominators (bad events) and the three atom terminals (balances).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AtomGenJ8
import Nock.NockVMROM.Thm54.VclL.Handle.HonestPairX
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.RangeHQ
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ Nock.NockVMROM.Thm54.VclL.Handle.QGates
open Module
open scoped Polynomial

/-! ## 1. Honest atom rows at gate level -/

section Nat

/-- The binary digits of `m < 2^n` sum back to `m`. -/
theorem sum_testBit (n : ℕ) : ∀ m, m < 2 ^ n →
    ∑ i ∈ Finset.range n, (if m.testBit i then 1 else 0) * 2 ^ i = m := by
  induction n with
  | zero => intro m hm; simp; omega
  | succ n ih =>
    intro m hm
    rw [Finset.sum_range_succ']
    have h1 : ∀ i, (if m.testBit (i + 1) then 1 else 0) * 2 ^ (i + 1) =
        2 * ((if (m / 2).testBit i then 1 else 0) * 2 ^ i) := by
      intro i; rw [Nat.testBit_add_one, pow_succ]; ring
    simp only [h1, ← Finset.mul_sum]
    have hm2 : m / 2 < 2 ^ n := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at hm; exact hm
    rw [ih (m / 2) hm2, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · have : decide (m % 2 = 1) = false := by simp [h]
      simp [this]; omega
    · have : decide (m % 2 = 1) = true := by simp [h]
      simp [this]; omega

end Nat

/-- **One atom-table row, read in ℕ.** -/
structure NRow where
  idx : ℕ
  idR : ℕ
  wL : ℕ
  wR : ℕ
  aL : ℕ
  aR : ℕ
  inc : ℕ
  conv : ℕ
  cout : ℕ
  idxO : ℕ
  lO : ℕ
  kRO : ℕ
  vRO : ℕ
  mb : ℕ
  mi : ℕ

/-- `valR`: the suffix serial if weighted, the top limb otherwise. -/
def NRow.valR (r : NRow) : ℕ := if r.wR = 1 then r.idR else r.aR

open Nock.Atoms (B) in
/-- **The ℕ honest-row condition** (row `r`, next row `rn`): what g1 .. g8 say, read forwards. -/
structure RowOK (r rn : NRow) : Prop where
  aL_lt : r.aL < B
  aR_lt : r.aR < B
  wL0 : r.wL = 0
  wR_le : r.wR ≤ 1
  top : r.wR = 0 → 0 < r.aR
  bmb : r.mb ≠ 0 → r.wR = 0 → r.aR = B - 1 ∧ 0 < r.aL
  bmi : r.mi ≠ 0 → r.wR = 0 → r.aR = B - 1 ∧ 0 < r.aL
  inc_le : r.inc ≤ 1
  conv_le : r.conv ≤ 1
  cout_le : r.cout ≤ 1
  kRO_le : r.kRO ≤ 1
  cout_inc : r.cout = 1 → r.inc = 1
  not_both : ¬ (r.inc = 1 ∧ r.conv = 1)
  mi_head : r.mi ≠ 0 → r.inc = 1 ∨ r.conv = 1
  limb : r.inc = 1 → r.aL + B * r.cout = r.lO + 1
  stop : r.inc = 1 → r.cout = 0 → r.wR = r.kRO ∧ r.valR = r.vRO
  link1 : r.cout = 1 → r.kRO = 1 → r.idR = r.idx + 1 ∧ rn.idxO = r.vRO
  link2 : r.cout = 1 → r.kRO = 1 → r.wR = 1 ∧ rn.inc = 1
  ovf0 : r.cout = 1 → r.kRO = 0 → r.wR = 0 → r.aR = r.vRO + 1
  ovf1 : r.cout = 1 → r.kRO = 0 → r.wR = 1 →
    r.vRO = B - 1 ∧ r.idR = r.idx + 1 ∧ rn.aL = 0 ∧ rn.wR = 0 ∧ rn.aR = 1
  cnv : r.conv = 1 → r.aL = 1 ∧ r.aR = B - 1 ∧ r.wR = 0

section Gates
variable {F : Type} [Field F]

/-- A field bit of `m`. -/
def bitF (m i : ℕ) : F := if m.testBit i then 1 else 0

/-- **A row environment carries row `r`**: the ℕ values, the limb bits, `inv_t`, `inv_b`. -/
structure ReadsN (e : Env F) (r : NRow) : Prop where
  idx : e.trace Cell.idx = r.idx
  idR : e.trace Cell.idR = r.idR
  wL : e.trace Cell.wL = r.wL
  wR : e.trace Cell.wR = r.wR
  aL : e.trace Cell.aL = r.aL
  aR : e.trace Cell.aR = r.aR
  bitsA : ∀ i < 32, e.trace (bitA + i) = bitF r.aL i
  bitsR : ∀ i < 32, e.trace (bitR + i) = bitF r.aR i
  invT : r.wR = 0 → e.trace invT = (r.aR : F)⁻¹
  invB : e.trace invB = (r.aL : F)⁻¹
  mb : e.trace mb = r.mb
  inc : e.trace inc = r.inc
  conv : e.trace conv = r.conv
  cout : e.trace cout = r.cout
  idxO : e.trace idxO = r.idxO
  lO : e.trace lO = r.lO
  kRO : e.trace kRO = r.kRO
  vRO : e.trace vRO = r.vRO
  mi : e.trace mi = r.mi

/-- The next row's columns the link gates read. -/
structure ReadsNextN (e : Env F) (rn : NRow) : Prop where
  idxO : e.traceNext idxO = rn.idxO
  inc : e.traceNext inc = rn.inc
  aL : e.traceNext Cell.aL = rn.aL
  wR : e.traceNext Cell.wR = rn.wR
  aR : e.traceNext Cell.aR = rn.aR

theorem natCast_ne_zero_of_lt (hB : Nock.Atoms.B < ringChar F) {x : ℕ} (h0 : 0 < x)
    (hx : x < Nock.Atoms.B) : (x : F) ≠ 0 := by
  intro h
  have := (CharP.cast_eq_zero_iff F (ringChar F) x).1 h
  exact absurd (Nat.le_of_dvd h0 this) (by omega)

theorem bitF_bool (m i : ℕ) : (bitF m i : F) * ((bitF m i : F) - 1) = 0 := by
  unfold bitF; split_ifs <;> simp

theorem eval_bits (base : ℕ) (e : Env F) (m : ℕ) (hm : m < 2 ^ 32)
    (hb : ∀ i < 32, e.trace (base + i) = bitF m i) :
    (bitSum (F := F) base 32).eval e = (m : F) := by
  rw [eval_bitSum]
  rw [Finset.sum_congr rfl fun i hi => by rw [hb i (Finset.mem_range.mp hi)]]
  have := sum_testBit 32 m hm
  have hc : ((∑ i ∈ Finset.range 32, (if m.testBit i then 1 else 0) * 2 ^ i : ℕ) : F) = (m : F) := by
    rw [this]
  rw [← hc]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold bitF; split_ifs <;> simp

theorem B_lt : Nock.Atoms.B = 2 ^ 32 := by simp [Nock.Atoms.B]

theorem Bf_sub_one : (Bf : F) - 1 = ((Nock.Atoms.B - 1 : ℕ) : F) := by
  rw [Nat.cast_sub (by rw [B_lt]; norm_num), Bf_eq]; simp

variable {e : Env F} {r rn : NRow}

theorem cases01 {x : ℕ} (h : x ≤ 1) : x = 0 ∨ x = 1 := by omega

/-- **`atomGates_of_rowOK`**: a row environment carrying an honest ℕ row (and, when it carries out, its next row)
satisfies every added base gate of `atomChipHQ`. -/
theorem atomGates_of_rowOK (hB : Nock.Atoms.B < ringChar F) (hr : ReadsN e r)
    (hn : r.cout = 1 → ReadsNextN e rn) (ok : RowOK r rn) :
    ∀ g ∈ (atomGates (F := F)), g.eval e = 0 := by
  have hBv : Nock.Atoms.B = 4294967296 := by rw [B_lt]; norm_num
  have haL := ok.aL_lt
  have haR := ok.aR_lt
  have hsA := eval_bits bitA e r.aL (by rw [← B_lt]; exact haL) hr.bitsA
  have hsR := eval_bits bitR e r.aR (by rw [← B_lt]; exact haR) hr.bitsR
  have hBm1 := Bf_sub_one (F := F)
  simp only [atomGates, g1, g23, bnd, g70, g71, g72, g73, ovf, g74, g8, valR, CellH.valE,
    List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map, List.mem_range,
    List.not_mem_nil, IsEmpty.forall_iff, forall_const, implies_true, and_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, fun i hi => ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  -- g1: limb sums
  · simp only [CoeffExpr.eval, hr.aL, hsA, sub_self]
  · simp only [CoeffExpr.eval, hr.aR, hsR, sub_self]
  -- g1: booleanity
  · have : (cv (bitA + i) : CoeffExpr F).eval e * ((cv (bitA + i) : CoeffExpr F).eval e - 1) = 0 := by
      show e.trace (bitA + i) * (e.trace (bitA + i) - 1) = 0
      by_cases h : i < 32
      · rw [hr.bitsA i h]; exact bitF_bool _ _
      · have h' : bitA + i = bitR + (i - 32) := by simp only [bitA, bitR]; omega
        rw [h', hr.bitsR (i - 32) (by omega)]; exact bitF_bool _ _
    simpa [CoeffExpr.eval] using this
  -- g2, g3
  · refine ⟨by simp [CoeffExpr.eval, hr.wL, ok.wL0], ?_⟩
    rcases cases01 ok.wR_le with h | h
    · have h0 := natCast_ne_zero_of_lt hB (ok.top h) haR
      simp [CoeffExpr.eval, hr.wR, hr.aR, h, hr.invT h, h0]
    · simp [CoeffExpr.eval, hr.wR, h]
  -- bnd mb
  · by_cases hm : r.mb = 0
    · simp [CoeffExpr.eval, hr.mb, hm]
    · rcases cases01 ok.wR_le with h | h
      · obtain ⟨h1, h2⟩ := ok.bmb hm h
        have h0 := natCast_ne_zero_of_lt hB h2 haL
        refine ⟨?_, ?_⟩
        · simp only [CoeffExpr.eval, hr.wR, hr.aR, h, h1, ← hBm1]; ring
        · simp [CoeffExpr.eval, hr.wR, hr.aL, h, hr.invB, h0]
      · simp [CoeffExpr.eval, hr.wR, h]
  -- bnd mi
  · by_cases hm : r.mi = 0
    · simp [CoeffExpr.eval, hr.mi, hm]
    · rcases cases01 ok.wR_le with h | h
      · obtain ⟨h1, h2⟩ := ok.bmi hm h
        have h0 := natCast_ne_zero_of_lt hB h2 haL
        refine ⟨?_, ?_⟩
        · simp only [CoeffExpr.eval, hr.wR, hr.aR, h, h1, ← hBm1]; ring
        · simp [CoeffExpr.eval, hr.wR, hr.aL, h, hr.invB, h0]
      · simp [CoeffExpr.eval, hr.wR, h]
  -- g7.0
  · have hi := cases01 ok.inc_le
    have hc := cases01 ok.conv_le
    have ho := cases01 ok.cout_le
    have hk := cases01 ok.kRO_le
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rcases hi with h | h <;> simp [CoeffExpr.eval, hr.inc, h]
    · rcases hc with h | h <;> simp [CoeffExpr.eval, hr.conv, h]
    · rcases ho with h | h <;> simp [CoeffExpr.eval, hr.cout, h]
    · rcases hk with h | h <;> simp [CoeffExpr.eval, hr.kRO, h]
    · rcases ho with h | h
      · simp [CoeffExpr.eval, hr.cout, h]
      · simp [CoeffExpr.eval, hr.cout, hr.inc, h, ok.cout_inc h]
    · rcases hi with h | h
      · simp [CoeffExpr.eval, hr.inc, h]
      · have : r.conv = 0 := by have := ok.not_both; omega
        simp [CoeffExpr.eval, hr.inc, hr.conv, h, this]
    · by_cases hm : r.mi = 0
      · simp [CoeffExpr.eval, hr.mi, hm]
      · rcases ok.mi_head hm with h | h
        · have : r.conv = 0 := by have := ok.not_both; omega
          simp [CoeffExpr.eval, hr.inc, hr.conv, h, this]
        · have : r.inc = 0 := by have := ok.not_both; rcases hi with h' | h' <;> omega
          simp [CoeffExpr.eval, hr.inc, hr.conv, h, this]
  -- g7.1
  · rcases cases01 ok.inc_le with h | h
    · simp [CoeffExpr.eval, hr.inc, h]
    · have hl := ok.limb h
      have : ((r.aL + Nock.Atoms.B * r.cout : ℕ) : F) = ((r.lO + 1 : ℕ) : F) := by rw [hl]
      push_cast at this
      simp only [CoeffExpr.eval, hr.inc, hr.aL, hr.lO, hr.cout, h, Nat.cast_one, one_mul, Bf_eq]
      linear_combination this
  -- g7.2
  · rcases cases01 ok.inc_le with h | h
    · simp [CoeffExpr.eval, hr.inc, h]
    · rcases cases01 ok.cout_le with hc | hc
      · obtain ⟨h1, h2⟩ := ok.stop h hc
        refine ⟨?_, ?_⟩
        · simp [CoeffExpr.eval, hr.inc, hr.cout, hr.wR, hr.kRO, h, hc, h1]
        · rcases cases01 ok.wR_le with hw | hw
          · have : r.aR = r.vRO := by simpa [NRow.valR, hw] using h2
            simp [CoeffExpr.eval, hr.inc, hr.cout, hr.wR, hr.aR, hr.vRO, h, hc, hw, this]
          · have : r.idR = r.vRO := by simpa [NRow.valR, hw] using h2
            simp [CoeffExpr.eval, hr.inc, hr.cout, hr.wR, hr.idR, hr.vRO, h, hc, hw, this]
      · simp [CoeffExpr.eval, hr.cout, hc]
  -- g7.3′
  · rcases cases01 ok.cout_le with hc | hc
    · simp [CoeffExpr.eval, hr.cout, hc]
    · have hN := hn hc
      have hinc := ok.cout_inc hc
      rcases cases01 ok.kRO_le with hk | hk
      · simp [CoeffExpr.eval, hr.cout, hr.kRO, hc, hk]
      · obtain ⟨h1, h2⟩ := ok.link1 hc hk
        obtain ⟨h3, h4⟩ := ok.link2 hc hk
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp [CoeffExpr.eval, hr.cout, hr.kRO, hr.inc, hr.idR, hr.idx, hc, hk, hinc, h1]
        · simp [CoeffExpr.eval, hr.cout, hr.kRO, hr.inc, hN.idxO, hr.vRO, hc, hk, hinc, h2]
        · simp [CoeffExpr.eval, hr.cout, hr.kRO, hr.wR, hc, hk, h3]
        · simp [CoeffExpr.eval, hr.cout, hr.kRO, hN.inc, hc, hk, h4]
  -- g7.4
  · rcases cases01 ok.cout_le with hc | hc
    · simp [CoeffExpr.eval, hr.cout, hc]
    · rcases cases01 ok.kRO_le with hk | hk
      · have hN := hn hc
        rcases cases01 ok.wR_le with hw | hw
        · have h1 := ok.ovf0 hc hk hw
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [CoeffExpr.eval, hr.cout, hr.kRO, hr.wR, hr.aR, hr.vRO, hc, hk, hw, h1]
        · obtain ⟨h1, h2, h3, h4, h5⟩ := ok.ovf1 hc hk hw
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [CoeffExpr.eval, hr.cout, hr.kRO, hr.wR, hc, hk, hw]
          · simp only [CoeffExpr.eval, hr.cout, hr.kRO, hr.wR, hr.vRO, hc, hk, hw, h1, ← hBm1]; ring
          · simp [CoeffExpr.eval, hr.cout, hr.kRO, hr.wR, hr.idR, hr.idx, hc, hk, hw, h2]
          · simp [CoeffExpr.eval, hr.cout, hr.kRO, hr.wR, hN.aL, hc, hk, hw, h3]
          · simp [CoeffExpr.eval, hr.cout, hr.kRO, hr.wR, hN.wR, hc, hk, hw, h4]
          · simp [CoeffExpr.eval, hr.cout, hr.kRO, hr.wR, hN.aR, hc, hk, hw, h5]
      · simp [CoeffExpr.eval, hr.cout, hr.kRO, hc, hk]
  -- g8
  · rcases cases01 ok.conv_le with hc | hc
    · simp [CoeffExpr.eval, hr.conv, hc]
    · obtain ⟨h1, h2, h3⟩ := ok.cnv hc
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [CoeffExpr.eval, hr.conv, hr.aL, hc, h1]
      · simp only [CoeffExpr.eval, hr.conv, hr.aR, hc, h2, ← hBm1]; ring
      · simp [CoeffExpr.eval, hr.conv, hr.wR, hc, h3]
      · simp [CoeffExpr.eval, hr.conv, hr.wL, hc, ok.wL0]

end Gates

/-! ## 4. The atom table honest at a good coin (one chip template; data as parameters) -/

noncomputable section

section Honest
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin n → F)

/-- **The honest added columns `130 .. 204`** of the rows `rows` (as `GenAtom.atomColD`): the limb bits,
`inv_t`, `inv_b`, `mb`, the inc-chain columns, `mi`. -/
def newOf (rows : ℕ → NRow) : ℕ → Fin n → F := fun c i =>
  if c < 162 then bitF (rows i).aL (c - 130)
  else if c < 194 then bitF (rows i).aR (c - 162)
  else if c = 194 then (if (rows i).wR = 0 then ((rows i).aR : F)⁻¹ else 0)
  else if c = 195 then ((rows i).aL : F)⁻¹
  else if c = 196 then ((rows i).mb : F) else if c = 197 then ((rows i).inc : F)
  else if c = 198 then ((rows i).conv : F) else if c = 199 then ((rows i).cout : F)
  else if c = 200 then ((rows i).idxO : F) else if c = 201 then ((rows i).lO : F)
  else if c = 202 then ((rows i).kRO : F) else if c = 203 then ((rows i).vRO : F)
  else ((rows i).mi : F)

/-- **The cell part carries the row's cell columns** (`idx idR wL wR aL aR`; L2's honest cell columns). -/
def CellAt (rows : ℕ → NRow) (i : Fin n) : Prop :=
  col Cell.idx i = (rows i).idx ∧ col Cell.idR i = (rows i).idR ∧ col Cell.wL i = (rows i).wL ∧
    col Cell.wR i = (rows i).wR ∧ col Cell.aL i = (rows i).aL ∧ col Cell.aR i = (rows i).aR

variable (newB : ℕ → Fin n → F)

theorem EZ_trace (hinj : Function.Injective nodes) (i : Fin n) (j : ℕ) (h2 : 2 ≤ j) (h3 : j < 205) :
    (HonestA8.EZ δF b hn nodes orbit chals pubs col newB i).trace j = if j < 130 then col j i else newB j i := by
  have hWA : (atomTemplateHQ δF).width 3 = 349 := HonestA8.atomTemplateHQ_width δF
  unfold HonestA8.EZ
  rw [env_trace hn nodes hinj _ _ _ _ i (by rw [hWA]; omega : j < (atomTemplateHQ δF).width 3)]
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  simp only [fullCol, h0, h1, if_false, HonestA8.colZ, extColF, HonestA8.newZ]
  by_cases hj : j < 130
  · simp [hj]
  · simp [hj, h3, show j < 313 by omega]

theorem EZ_traceNext (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (j : ℕ) (h2 : 2 ≤ j) (h3 : j < 205) :
    (HonestA8.EZ δF b hn nodes orbit chals pubs col newB i).traceNext j =
      if j < 130 then col j ⟨(i : ℕ) + 1, hi⟩ else newB j ⟨(i : ℕ) + 1, hi⟩ := by
  have hWA : (atomTemplateHQ δF).width 3 = 349 := HonestA8.atomTemplateHQ_width δF
  unfold HonestA8.EZ
  rw [env_traceNext hn nodes hinj _ _ _ _ hadj i hi (by rw [hWA]; omega : j < (atomTemplateHQ δF).width 3)]
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  simp only [fullCol, h0, h1, if_false, HonestA8.colZ, extColF, HonestA8.newZ]
  by_cases hj : j < 130
  · simp [hj]
  · simp [hj, h3, show j < 313 by omega]

theorem readsN_EZ (hinj : Function.Injective nodes) (rows : ℕ → NRow) (i : Fin n)
    (hc : CellAt col rows i) :
    ReadsN (HonestA8.EZ δF b hn nodes orbit chals pubs col (newOf rows) i) (rows i) := by
  have T := EZ_trace δF b hn nodes orbit chals pubs col (newOf rows) hinj i
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, fun k hk => ?_, fun hw => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [T _ (by decide) (by decide)]; simpa [Cell.idx] using c1
  · rw [T _ (by decide) (by decide)]; simpa [Cell.idR] using c2
  · rw [T _ (by decide) (by decide)]; simpa [Cell.wL] using c3
  · rw [T _ (by decide) (by decide)]; simpa [Cell.wR] using c4
  · rw [T _ (by decide) (by decide)]; simpa [Cell.aL] using c5
  · rw [T _ (by decide) (by decide)]; simpa [Cell.aR] using c6
  · rw [T _ (by simp only [bitA]; omega) (by simp only [bitA]; omega), if_neg (by simp only [bitA]; omega)]
    simp [newOf, bitA, show 130 + k < 162 by omega]
  · rw [T _ (by simp only [bitR]; omega) (by simp only [bitR]; omega), if_neg (by simp only [bitR]; omega)]
    simp [newOf, bitR, show ¬ (162 + k < 162) by omega, show 162 + k < 194 by omega]
  · rw [T _ (by decide) (by decide), if_neg (by decide)]; simp [newOf, AtomChipHQ.invT, hw]
  all_goals first
    | (rw [T _ (by decide) (by decide), if_neg (by decide)]
       simp [newOf, AtomChipHQ.invB, AtomChipHQ.mb, AtomChipHQ.inc, AtomChipHQ.conv, AtomChipHQ.cout,
         AtomChipHQ.idxO, AtomChipHQ.lO, AtomChipHQ.kRO, AtomChipHQ.vRO, AtomChipHQ.mi])

theorem readsNextN_EZ (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (rows : ℕ → NRow) (i : Fin n) (hi : (i : ℕ) + 1 < n) (hc : CellAt col rows ⟨(i : ℕ) + 1, hi⟩) :
    ReadsNextN (HonestA8.EZ δF b hn nodes orbit chals pubs col (newOf rows) i) (rows ((i : ℕ) + 1)) := by
  have T := EZ_traceNext δF b hn nodes orbit chals pubs col (newOf rows) hinj hadj i hi
  obtain ⟨-, -, -, c4, c5, c6⟩ := hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [T _ (by decide) (by decide), if_neg (by decide)]; simp [newOf, AtomChipHQ.idxO]
  · rw [T _ (by decide) (by decide), if_neg (by decide)]; simp [newOf, AtomChipHQ.inc]
  · rw [T _ (by decide) (by decide)]; simpa [Cell.aL] using c5
  · rw [T _ (by decide) (by decide)]; simpa [Cell.wR] using c4
  · rw [T _ (by decide) (by decide)]; simpa [Cell.aR] using c6

/-- **`hbase` for arbitrary honest rows**: `HonestA8`'s base-gate hypothesis at the honest added columns
`newOf rows`, from `RowOK` at every row (next row `i + 1`) and a last row without carry-out. -/
theorem hbase_of_rows (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hB : Nock.Atoms.B < ringChar F) (rows : ℕ → NRow) (hcell : ∀ i, CellAt col rows i)
    (hok : ∀ i : Fin n, RowOK (rows i) (rows ((i : ℕ) + 1))) (hlast : (rows (n - 1)).cout = 0) :
    ∀ i, ∀ g ∈ (atomGates (F := F)), g.eval (HonestA8.EZ δF b hn nodes orbit chals pubs col (newOf rows) i) = 0 := by
  intro i
  refine atomGates_of_rowOK hB (readsN_EZ δF b hn nodes orbit chals pubs col hinj rows i (hcell i))
    (fun hc => ?_) (hok i)
  have hi : (i : ℕ) + 1 < n := by
    by_contra hne
    have : (i : ℕ) = n - 1 := by omega
    rw [this, hlast] at hc; omega
  exact readsNextN_EZ δF b hn nodes orbit chals pubs col hinj hadj rows i hi (hcell _)

set_option maxRecDepth 20000 in
/-- **The atom table at a good coin** (`atomChipHQ` and its variant `atomChipHQL`, satisfied and bound) by the
honest trace `atomTraceHQ … col (newOf rows)`.  Inputs: L2's cell-part acceptance `hsat0`, the honest rows
(`RowOK`, the cell part's columns, no carry-out on the last row), the three non-vanishing atom denominators
(bad events) and the three atom terminals (balances). -/
theorem atomOK_of_rows (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hB : Nock.Atoms.B < ringChar F) (rows : ℕ → NRow) (hcell : ∀ i, CellAt col rows i)
    (hok : ∀ i : Fin n, RowOK (rows i) (rows ((i : ℕ) + 1))) (hlast : (rows (n - 1)).cout = 0)
    (hsat0 : (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies (honestQ hn nodes col _))
    (hz1 : ∀ i, HonestA8.dMB δF b hn nodes orbit chals pubs col (newOf rows) i ≠ 0)
    (hz2 : ∀ i, HonestA8.dC δF b hn nodes orbit chals pubs col (newOf rows) i ≠ 0)
    (hz3 : ∀ i, HonestA8.dMI δF b hn nodes orbit chals pubs col (newOf rows) i ≠ 0)
    (hpMB : Quad.mk _ (pubs pubMB) (pubs (pubMB + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (HonestA8.cNat j (newOf (n := n) rows mb)) *
        (HonestA8.dNat δF (HonestA8.dMB δF b hn nodes orbit chals pubs col (newOf rows)) j)⁻¹)
    (hpC : Quad.mk _ (pubs pubC) (pubs (pubC + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (HonestA8.cNat j (newOf (n := n) rows inc)) *
        (HonestA8.dNat δF (HonestA8.dC δF b hn nodes orbit chals pubs col (newOf rows)) j)⁻¹)
    (hpMI : Quad.mk _ (pubs pubMI) (pubs (pubMI + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (HonestA8.cNat j (newOf (n := n) rows mi)) *
        (HonestA8.dNat δF (HonestA8.dMI δF b hn nodes orbit chals pubs col (newOf rows)) j)⁻¹) :
    (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies
        (HonestA8.atomTraceHQ δF b hn nodes orbit chals pubs col (newOf rows)) ∧
      (atomChipHQ δF b hn nodes orbit chals pubs).BindsPreprocessing
        (HonestA8.atomTraceHQ δF b hn nodes orbit chals pubs col (newOf rows)) ∧
      (AtomChipHQL.atomChipHQL δF b hn nodes orbit chals pubs).rap.Satisfies
        (AtomChipHQL.ofHQ δF b hn nodes orbit chals pubs
          (HonestA8.atomTraceHQ δF b hn nodes orbit chals pubs col (newOf rows))) ∧
      (AtomChipHQL.atomChipHQL δF b hn nodes orbit chals pubs).BindsPreprocessing
        (AtomChipHQL.ofHQ δF b hn nodes orbit chals pubs
          (HonestA8.atomTraceHQ δF b hn nodes orbit chals pubs col (newOf rows))) := by
  have hbase := hbase_of_rows δF b hn nodes orbit chals pubs col hinj hadj hB rows hcell hok hlast
  have hL : ∀ i : Fin n, (i : ℕ) + 1 = n → newOf (F := F) rows cout i = 0 := by
    intro i hi
    have : (i : ℕ) = n - 1 := by omega
    simp [newOf, AtomChipHQ.cout, this, hlast]
  refine ⟨HonestA8.atomChipHQ_accepts_honest δF b hn nodes orbit chals pubs col (newOf rows) hinj hadj hsat0
      hbase hz1 hz2 hz3 hpMB hpC hpMI, ?_,
    AtomChipHQL.atomChipHQL_accepts_honest δF b hn nodes orbit chals pubs col (newOf rows) hinj hadj hsat0
      hbase hz1 hz2 hz3 hpMB hpC hpMI hL, ?_⟩
  · intro j
    fin_cases j
    · exact honestQ_zero hn nodes _ (by norm_num)
    · exact honestQ_one hn nodes _ (by norm_num)
  · intro j
    fin_cases j
    · exact honestQ_zero hn nodes _ (by norm_num)
    · exact honestQ_one hn nodes _ (by norm_num)

end Honest

/-- **Row nodes `ω^i`** (any chip, the atom table's `atomNodes`): injective and adjacent when `n ≤ 2^h`. -/
theorem powNodes_ok {F : Type} [Field F] {h n : ℕ} (orbit : StrictOrbitDomain F 3 h) (hn : n ≤ 2 ^ h) :
    Function.Injective (fun i : Fin n => orbit.ω ^ (i : ℕ)) ∧
      ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
        (fun i : Fin n => orbit.ω ^ (i : ℕ)) ⟨(i : ℕ) + 1, hi⟩ = (fun i : Fin n => orbit.ω ^ (i : ℕ)) i * orbit.ω := by
  refine ⟨fun a c hac => Fin.ext ?_, fun i hi => pow_succ _ _⟩
  have hord : orderOf orbit.ω = 3 * 2 ^ h := orbit.order_ω
  refine pow_injOn_Iio_orderOf ?_ ?_ hac
  · show (a : ℕ) < orderOf _; rw [hord]; have := a.isLt; omega
  · show (c : ℕ) < orderOf _; rw [hord]; have := c.isLt; omega

end

/-! ## 2. The ℕ honest rows of an atom table: comb spines, inc chains, conversion rows -/

section Spec
open Nock.Atoms (B val limbs Canonical Carry)

/-- A canonical nonempty tail of a canonical list is canonical. -/
theorem canonical_tail {a : ℕ} {l : List ℕ} (h : Canonical (a :: l)) (hl : l ≠ []) : Canonical l := by
  refine ⟨fun x hx => h.1 x (by simp [hx]), fun hne => ?_⟩
  have := h.2 (by simp)
  obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  rwa [Nock.Atoms.getLast_cons_cons'] at this

theorem carry_length_le {c : ℕ} {l l' : List ℕ} (h : Carry c l l') : l.length ≤ l'.length := by
  induction h with
  | nil0 => simp
  | nil1 => simp
  | cons _ _ _ _ _ ih => simp; omega

/-- The `+1` of the canonical `limbs (v − 1)` is the canonical nonempty `s` with `val s = v`. -/
theorem carry_pred {s : List ℕ} (hc : Canonical s) (hne : s ≠ []) :
    Carry 1 (limbs (val s - 1)) s := by
  have hv : val s ≠ 0 := by
    intro h0
    have := Nock.Atoms.limbs_val hc
    rw [h0] at this; simp [limbs] at this; exact hne this
  obtain ⟨l', h⟩ := Nock.Atoms.carry_exists (le_refl 1) (Nock.Atoms.limbs_canonical (val s - 1)).1
  have hc' := Nock.Atoms.carry_canonical h (Nock.Atoms.limbs_canonical _)
  have hv' := Nock.Atoms.carry_val h
  rw [Nock.Atoms.val_limbs] at hv'
  have : l' = s := Nock.Atoms.canonical_unique hc' hc (by rw [hv']; omega)
  rwa [this] at h

/-- **An atom table in ℕ, at the spec level** (the parameters a generator instantiates): `n` rows; row `j`'s limb
suffix `sp j` (its comb); `ix` the representative row of a suffix (the tail pointer); the inc / conversion flags;
the `mb` / `mi` multiplicities.  The old copy of an inc row is the canonical `limbs (val (sp j) − 1)`. -/
structure AtomTab where
  n : ℕ
  sp : ℕ → List ℕ
  ix : List ℕ → ℕ
  inc : ℕ → Bool
  conv : ℕ → Bool
  mb : ℕ → ℕ
  mi : ℕ → ℕ
  /-- The old index of an inc row (GLA fix (B)): the serial of a copy of its old suffix's comb (the generator's
  `idxO`; a depth-0 row of `p` keys the LAST copy of `comb p`).  `ix` stays the tail pointer. -/
  io : ℕ → ℕ
  /-- **The tail pointer of a row with suffix `s`** (G12 variant 3, a full-suffix pointer): the serial of a row
  carrying `s.tail`.  The generator's `ptrP` (variant 4, per component) routes it to the LAST copy of `comb p` when
  `s.tail = limbs p` and the head is out of the stop-edge component of `0` (`ComplJ8Data.FirstC`). -/
  ip : List ℕ → ℕ

namespace AtomTab
variable (T : AtomTab)

/-- The old copy of row `j` (an inc row's predecessor atom suffix). -/
def lo (j : ℕ) : List ℕ := limbs (val (T.sp j) - 1)

/-- **Row `j` read in ℕ** (as the generator's `atomColD` fills it). -/
def row (j : ℕ) : NRow where
  idx := j
  idR := if 3 ≤ (T.sp j).length then T.ip (T.sp j) else 0
  wL := 0
  wR := if 3 ≤ (T.sp j).length then 1 else 0
  aL := (T.sp j).headD 0
  aR := if 3 ≤ (T.sp j).length then 0 else (T.sp j).getD 1 0
  inc := if T.inc j then 1 else 0
  conv := if T.conv j then 1 else 0
  cout := if T.inc j ∧ (T.lo j).headD 0 = B - 1 then 1 else 0
  idxO := if T.inc j then T.io j else 0
  lO := if T.inc j then (T.lo j).headD 0 else 0
  kRO := if T.inc j ∧ 3 ≤ (T.lo j).length then 1 else 0
  vRO := if T.inc j then (if 3 ≤ (T.lo j).length then T.ip (T.lo j) else (T.lo j).getD 1 0) else 0
  mb := T.mb j
  mi := T.mi j

open Nock.Atoms (p) in
/-- **The structural invariants of an honest atom table** (what a generator must meet): canonical spines of length
`≥ 2`, tail-closed, LINK ORDER (a row `[0 X]` is followed by `X`), the inc chain continues while the old row carries
into a suffix row, conversion rows are `p = [1, B − 1]` and not inc rows, `mb` / `mi` rows are big roots (`mi` on a
chain head or conversion row), the last row is not an inc row (the pad row). -/
structure Valid : Prop where
  canon : ∀ j < T.n, 2 ≤ (T.sp j).length ∧ Canonical (T.sp j)
  tail : ∀ j < T.n, 3 ≤ (T.sp j).length → T.ip (T.sp j) < T.n ∧ T.sp (T.ip (T.sp j)) = (T.sp j).tail
  link : ∀ j < T.n, 3 ≤ (T.sp j).length → (T.sp j).headD 0 = 0 → T.ip (T.sp j) = j + 1
  incOld : ∀ j < T.n, T.inc j = true → 2 ≤ (T.lo j).length
  chain : ∀ j < T.n, T.inc j = true → (T.lo j).headD 0 = B - 1 → 3 ≤ (T.lo j).length → T.inc (j + 1) = true
  /-- The link of a carry chain (GLA fix (B)): the next row's old index is this row's old tail pointer. -/
  ioLink : ∀ j < T.n, T.inc j = true → (T.lo j).headD 0 = B - 1 → 3 ≤ (T.lo j).length →
    T.io (j + 1) = T.ip (T.lo j)
  /-- **Same pointer across a stop step**: an inc row whose old suffix `a :: st` does not
  carry (`a ≠ B − 1`) has the new suffix `(a + 1) :: st`; both point at the same row (same component of `comb p`). -/
  stop : ∀ j < T.n, T.inc j = true → ∀ a st, T.lo j = a :: st → a ≠ B - 1 → 2 ≤ st.length →
    T.ip ((a + 1) :: st) = T.ip (a :: st)
  conv : ∀ j < T.n, T.conv j = true → T.sp j = [1, B - 1] ∧ T.inc j = false
  mbBig : ∀ j < T.n, T.mb j ≠ 0 → p ≤ val (T.sp j)
  miBig : ∀ j < T.n, T.mi j ≠ 0 → p ≤ val (T.sp j) ∧ (T.inc j = true ∨ T.conv j = true)
  last : T.inc (T.n - 1) = false

variable {T}

/-- A big root of length two is `[a, B − 1]` with `a ≥ 1`. -/
theorem big_two {s : List ℕ} (hc : Canonical s) (h2 : ¬ 3 ≤ s.length) (hb : Nock.Atoms.p ≤ val s) :
    s.getD 1 0 = B - 1 ∧ 0 < s.headD 0 := by
  rcases (Nock.Atoms.big_iff hc).1 hb with h | ⟨a, b, rfl, hb', ha⟩
  · omega
  · simp [hb']; omega

/-- **The ℕ honest rows**: every row of a valid atom table satisfies `RowOK` against its successor, and the last
row has no carry-out. -/
theorem rowOK_of_valid (hv : T.Valid) : ∀ j < T.n, RowOK (T.row j) (T.row (j + 1)) := by
  intro j hj
  obtain ⟨h2, hc⟩ := hv.canon j hj
  obtain ⟨a', st, hs⟩ : ∃ a' st, T.sp j = a' :: st := by
    cases h : T.sp j with
    | nil => rw [h] at h2; simp at h2
    | cons x t => exact ⟨x, t, rfl⟩
  have hBv : B = 4294967296 := Nock.Atoms.B_eq
  have hlimbs := hc.1
  have hst : st ≠ [] := by intro e; rw [hs, e] at h2; simp at h2
  have hcst : Canonical st := canonical_tail (hs ▸ hc) hst
  have ha'B : a' < B := hlimbs a' (by simp [hs])
  -- the inc-row data
  have incData : T.inc j = true → ∃ a lt c, T.lo j = a :: lt ∧ lt ≠ [] ∧ a < B ∧ c ≤ 1 ∧
      a' + B * c = a + 1 ∧ Carry c lt st ∧ Canonical lt ∧ (c = 1 ↔ a = B - 1) := by
    intro hinc
    have hl2 := hv.incOld j hj hinc
    have hcar := carry_pred hc (by rw [hs]; simp)
    obtain ⟨a, lt, hlo⟩ : ∃ a lt, T.lo j = a :: lt := by
      cases h : T.lo j with
      | nil => rw [h] at hl2; simp at hl2
      | cons x t => exact ⟨x, t, rfl⟩
    have hlt : lt ≠ [] := by intro e; rw [hlo, e] at hl2; simp at hl2
    have hcl : Canonical (a :: lt) := hlo ▸ Nock.Atoms.limbs_canonical _
    unfold lo at hlo
    rw [hlo, hs] at hcar
    cases hcar with
    | cons hcin hco ha'' he hr =>
      rename_i c
      have haB : a < B := hcl.1 a (by simp)
      refine ⟨a, lt, c, by unfold lo; exact hlo, hlt, haB, hco, he, hr, canonical_tail hcl hlt, ?_⟩
      constructor
      · intro h1; subst h1; omega
      · intro h; rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hco with h0 | h1
        · subst h0; omega
        · exact h1
  have hlen : (T.sp j).length = st.length + 1 := by rw [hs]; simp
  have hhead : (T.sp j).headD 0 = a' := by rw [hs]; simp
  have htail : (T.sp j).tail = st := by rw [hs]; simp
  have hget : (T.sp j).getD 1 0 = st.headD 0 := by rw [hs]; cases st <;> simp
  have hstB : ∀ x ∈ st, x < B := fun x hx => hlimbs x (by simp [hs, hx])
  -- the short case: `st = [y]`, `y ≠ 0`
  have short : ¬ 3 ≤ (T.sp j).length → ∃ y, st = [y] ∧ 0 < y ∧ y < B := by
    intro h3
    match st, hst, hcst, hstB with
    | [y], _, hcy, hyB => exact ⟨y, rfl, Nat.pos_of_ne_zero (by simpa using hcy.2 (by simp)), hyB y (by simp)⟩
    | y :: z :: t, _, _, _ => exfalso; rw [hlen] at h3; simp at h3
  -- the next row when the chain links (`ix st = j + 1`)
  have nextRow : 3 ≤ (T.sp j).length → a' = 0 → T.ip (T.sp j) = j + 1 ∧ T.sp (j + 1) = st := by
    intro h3 h0
    have hl := hv.link j hj h3 (by rw [hhead, h0])
    have ht := hv.tail j hj h3
    rw [htail] at ht
    exact ⟨hl, by rw [← hl]; exact ht.2⟩
  refine
    { aL_lt := ?_, aR_lt := ?_, wL0 := rfl, wR_le := ?_, top := ?_, bmb := ?_, bmi := ?_, inc_le := ?_,
      conv_le := ?_, cout_le := ?_, kRO_le := ?_, cout_inc := ?_, not_both := ?_, mi_head := ?_, limb := ?_,
      stop := ?_, link1 := ?_, link2 := ?_, ovf0 := ?_, ovf1 := ?_, cnv := ?_ }
  · simp only [row, hhead]; exact ha'B
  · simp only [row]; split_ifs with h3
    · rw [hBv]; norm_num
    · obtain ⟨y, hy, -, hyB⟩ := short h3; rw [hget, hy]; simpa using hyB
  · simp only [row]; split_ifs <;> omega
  · simp only [row]; intro hw; split_ifs at hw ⊢ with h3
    · rw [hget]; obtain ⟨y, hy, hy0, -⟩ := short h3; rw [hy]; simpa using hy0
  · simp only [row]; intro hm hw; split_ifs at hw ⊢ with h3
    exact (big_two hc h3 (hv.mbBig j hj hm)).imp id id
  · simp only [row]; intro hm hw; split_ifs at hw ⊢ with h3
    exact (big_two hc h3 (hv.miBig j hj hm).1).imp id id
  · simp only [row]; split_ifs <;> omega
  · simp only [row]; split_ifs <;> omega
  · simp only [row]; split_ifs <;> omega
  · simp only [row]; split_ifs <;> omega
  · simp only [row]; intro h
    by_cases hi : T.inc j = true
    · simp [hi]
    · simp [hi] at h
  · simp only [row]; rintro ⟨h1, h2⟩
    split_ifs at h1 h2 with hi hc'
    · have := (hv.conv j hj hc').2; rw [this] at hi; exact absurd hi (by simp)
  · simp only [row]; intro hm
    rcases (hv.miBig j hj hm).2 with h | h <;> simp [h]
  · simp only [row]; intro hi
    split_ifs at hi with hinc
    obtain ⟨a, lt, c, hlo, -, -, hco, he, -, -, hiff⟩ := incData hinc
    rw [hhead, hlo]
    simp only [List.headD_cons, hinc, true_and]
    split_ifs with ha
    · rw [← hiff.2 ha]; omega
    · have : c = 0 := by rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hco with h | h; exact h; exact absurd (hiff.1 h) ha
      rw [this] at he; omega
  · simp only [row]; intro hi ho
    split_ifs at hi with hinc
    obtain ⟨a, lt, c, hlo, hlt, -, hco, he, hr, hclt, hiff⟩ := incData hinc
    rw [hlo] at ho ⊢
    simp only [List.headD_cons, hinc, true_and] at ho ⊢
    have hc0 : c = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hco with h | h
      · exact h
      · rw [if_pos (hiff.1 h)] at ho; exact absurd ho (by norm_num)
    rw [hc0] at hr
    have heq : st = lt := Nock.Atoms.carry_zero_eq hclt.1 hr
    have hl3 : (3 ≤ (T.sp j).length) ↔ (3 ≤ (a :: lt).length) := by rw [hlen, heq]; simp
    simp only [NRow.valR, List.length_cons, List.tail_cons]
    by_cases h3 : 3 ≤ (T.sp j).length
    · have h3' := hl3.1 h3
      simp only [List.length_cons] at h3'
      have ha1 : a' = a + 1 := by rw [hc0] at he; omega
      have haB : a ≠ B - 1 := fun h => by have := hiff.2 h; omega
      have hip := hv.stop j hj hinc a lt hlo haB (by omega)
      have hsp' : T.sp j = (a + 1) :: lt := by rw [hs, ha1, heq]
      simp [h3, h3', hsp', hip]
    · have h3' : ¬ 3 ≤ lt.length + 1 := fun h => h3 (hl3.2 (by simpa using h))
      simp only [h3, h3', if_false, and_false]
      refine ⟨by simp, ?_⟩
      rw [hget, heq]; cases lt <;> simp
  · simp only [row]; intro ho hk
    have hinc : T.inc j = true := by by_contra h; simp [h] at ho
    obtain ⟨a, lt, c, hlo, hlt, haB, hco, he, hr, hclt, hiff⟩ := incData hinc
    rw [hlo] at ho hk ⊢
    simp only [List.headD_cons, hinc, true_and, List.length_cons] at ho hk ⊢
    have ha : a = B - 1 := by by_contra h; simp [h] at ho
    have hc1 : c = 1 := hiff.2 ha
    have hlt2 : 3 ≤ lt.length + 1 := by by_contra h; simp [h] at hk
    have hle := carry_length_le hr
    have h3 : 3 ≤ (T.sp j).length := by rw [hlen]; omega
    have ha0 : a' = 0 := by rw [hc1] at he; omega
    obtain ⟨hix, hsp⟩ := nextRow h3 ha0
    have hinc1 : T.inc (j + 1) = true := hv.chain j hj hinc (by rw [hlo]; simp [ha]) (by rw [hlo]; simpa using hlt2)
    have hio := hv.ioLink j hj hinc (by rw [hlo]; simp [ha]) (by rw [hlo]; simpa using hlt2)
    rw [hlo] at hio
    refine ⟨?_, ?_⟩
    · simp [h3, htail, hix]
    · simp [hinc1, hio, hlt2]
  · simp only [row]; intro ho hk
    have hinc : T.inc j = true := by by_contra h; simp [h] at ho
    obtain ⟨a, lt, c, hlo, hlt, haB, hco, he, hr, hclt, hiff⟩ := incData hinc
    rw [hlo] at ho hk
    simp only [List.headD_cons, hinc, true_and, List.length_cons] at ho hk
    have ha : a = B - 1 := by by_contra h; simp [h] at ho
    have hc1 : c = 1 := hiff.2 ha
    have hlt2 : 3 ≤ lt.length + 1 := by by_contra h; simp [h] at hk
    have hle := carry_length_le hr
    have h3 : 3 ≤ (T.sp j).length := by rw [hlen]; omega
    have hinc1 : T.inc (j + 1) = true := hv.chain j hj hinc (by rw [hlo]; simp [ha]) (by rw [hlo]; simpa using hlt2)
    simp [h3, hinc1]
  · simp only [row]; intro ho hk hw
    have hinc : T.inc j = true := by by_contra h; simp [h] at ho
    obtain ⟨a, lt, c, hlo, hlt, haB, hco, he, hr, hclt, hiff⟩ := incData hinc
    rw [hlo] at ho hk ⊢
    simp only [List.headD_cons, hinc, true_and, List.length_cons] at ho hk ⊢
    have ha : a = B - 1 := by by_contra h; simp [h] at ho
    have hc1 : c = 1 := hiff.2 ha
    have hlt1 : ¬ 3 ≤ lt.length + 1 := by intro h; simp [h] at hk
    have h3 : ¬ 3 ≤ (T.sp j).length := by intro h; simp [h] at hw
    obtain ⟨y, hy, -, -⟩ := short h3
    obtain ⟨x, rfl⟩ : ∃ x, lt = [x] := by
      match lt, hlt, hlt1 with
      | [x], _, _ => exact ⟨x, rfl⟩
      | x :: z :: t, _, h => simp at h
    rw [hc1, hy] at hr
    rw [if_neg h3, hget, hy]
    cases hr with
    | @cons _ c' _ y' _ _ _ hco' hyB he' hr' =>
      cases hr'
      simp; omega
  · simp only [row]; intro ho hk hw
    have hinc : T.inc j = true := by by_contra h; simp [h] at ho
    obtain ⟨a, lt, c, hlo, hlt, haB, hco, he, hr, hclt, hiff⟩ := incData hinc
    rw [hlo] at ho hk ⊢
    simp only [List.headD_cons, hinc, true_and, List.length_cons] at ho hk ⊢
    have ha : a = B - 1 := by by_contra h; simp [h] at ho
    have hc1 : c = 1 := hiff.2 ha
    have hlt1 : ¬ 3 ≤ lt.length + 1 := by intro h; simp [h] at hk
    have h3 : 3 ≤ (T.sp j).length := by by_contra h; simp [h] at hw
    have ha0 : a' = 0 := by rw [hc1] at he; omega
    obtain ⟨hix, hsp⟩ := nextRow h3 ha0
    obtain ⟨x, rfl⟩ : ∃ x, lt = [x] := by
      match lt, hlt, hlt1 with
      | [x], _, _ => exact ⟨x, rfl⟩
      | x :: z :: t, _, h => simp at h
    have hxB : x < B := hclt.1 x (by simp)
    rw [hc1] at hr
    have hst2 : 2 ≤ st.length := by rw [hlen] at h3; omega
    cases hr with
    | @cons _ c' _ y _ st' _ hco' hyB he' hr' =>
      cases hr' with
      | nil0 => simp at hst2
      | nil1 =>
        have hx : x = B - 1 := by omega
        have hy0 : y = 0 := by omega
        subst hy0
        simp [h3, htail, hix, hsp, hx]
  · simp only [row]; intro hcv
    split_ifs at hcv with hcv'
    have := (hv.conv j hj hcv').1
    simp [this]

/-- The last row of a valid atom table carries no carry-out. -/
theorem cout_last (hv : T.Valid) : (T.row (T.n - 1)).cout = 0 := by
  simp [row, hv.last]

/-- **`RowOK` at every row of the chip** (`n = T.n`) and no carry-out on the last row: the row inputs of
`hbase_of_rows` / `atomOK_of_rows`. -/
theorem rows_ok (hv : T.Valid) {n : ℕ} (hn : T.n = n) :
    (∀ i : Fin n, RowOK (T.row i) (T.row ((i : ℕ) + 1))) ∧ (T.row (n - 1)).cout = 0 :=
  ⟨fun i => rowOK_of_valid hv i (hn ▸ i.isLt), hn ▸ cout_last hv⟩

end AtomTab
end Spec

/-! ## 3. `hpair`: the op-5 α-pair limb data (a fact about `pdX`, not about a table) -/

section Pair
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX (HdlOK isPair PairOK)

/-- **`hpair`**: on every node of the generated tree of `genX R fuel s f`, an op-5 α-pair row's honest limb data
`pdX sx` (any spine serial map `sx`) satisfies `PairOK`, under an honest handle map and the two run binders. -/
theorem hpair_of_binders {p : ℕ} [Fact p.Prime] {R : Nock.Jet.Registry} {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX R fuel s f = some (t, r)) {H : Noun → ℕ × ℕ}
    (hH : HdlOK (ringChar (ZMod p)) H) (hp63 : 2 ^ 63 < p) (sx : ℕ → ℕ → ℕ)
    (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t) :
    ∀ u, InTree t u → isPair H (rowOfSkelX u.label) →
      PairOK (F := ZMod p) (HonestPairX.pdX sx (rowOfSkelX u.label)) := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hB : Nock.Atoms.B ≤ ringChar (ZMod p) := by
    rw [hrc, B_lt]; have : (2 : ℕ) ^ 32 ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by norm_num); omega
  have hsm : ∀ u, InTree t u → HonestRowX.SmallX (ringChar (ZMod p)) (rowOfSkelX u.label) := by
    rw [hrc]; exact ComplJ8.smallX_of_binders hax hop5
  exact HonestPairX.pairOK_of_genX hgen hH hB sx hsm

end Pair

section Gen5
open Nock.V1J8.Gen
/-! ## 5. The generator's link order (`GenAtom.linkOrder`) -/



/-- `[0 n]`. -/
def up0 (n : Noun) : Noun := .cell (.atom 0) n

theorem leaves_up0 (n : Noun) : (up0 n).leaves = n.leaves + 1 := by
  simp [up0, Noun.leaves]; omega

theorem leaves_iter (n : Noun) (k : ℕ) : (up0^[k] n).leaves = n.leaves + k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', leaves_up0, ih]; omega

theorem linkSucc_some {L : List Noun} {m X : Noun} (h : linkSucc L m = some X) :
    m = up0 X ∧ X ∈ L ∧ X.isCell = true := by
  unfold linkSucc at h
  split at h
  · rename_i a b
    split_ifs at h with hm
    cases h
    exact ⟨rfl, hm, rfl⟩
  · cases h

theorem linkSucc_up0 {L : List Noun} {X : Noun} (hX : X ∈ L) (hc : X.isCell = true) :
    linkSucc L (up0 X) = some X := by
  cases X with
  | atom v => simp [Noun.isCell] at hc
  | cell a b => simp [linkSucc, up0, hX]

/-- The successor relation of the link order. -/
def LR (L : List Noun) (a b : Noun) : Prop := linkSucc L a = some b

/-- **`linkChain` from a member**: nonempty, starts at `h`, a chain of successors inside `L`, at most `g + 1` long,
and either its last element has no successor or the fuel is used up. -/
theorem linkChain_spec (L : List Noun) :
    ∀ (g : ℕ) (h : Noun), h ∈ L →
      (linkChain L g h).head? = some h ∧ List.IsChain (LR L) (linkChain L g h) ∧
        (∀ x ∈ linkChain L g h, x ∈ L) ∧ (linkChain L g h).length ≤ g + 1 ∧
        (∀ x, (linkChain L g h).getLast? = some x → linkSucc L x = none ∨
          (linkChain L g h).length = g + 1)
  | 0, h, hh => by simp [linkChain, hh]
  | g + 1, h, hh => by
    cases hm : linkSucc L h with
    | some m =>
      simp only [linkChain, hm]
      have hmL := (linkSucc_some hm).2.1
      obtain ⟨i1, i2, i3, i4, i5⟩ := linkChain_spec L g m hmL
      have hne : linkChain L g m ≠ [] := by intro e; rw [e] at i1; simp at i1
      obtain ⟨m', t, ht⟩ := List.exists_cons_of_ne_nil hne
      rw [ht] at i1 i2 i3 i4 i5 ⊢
      simp only [List.head?_cons, Option.some.injEq] at i1
      subst i1
      refine ⟨rfl, i2.cons (by simp [LR, hm]), ?_, by simp at i4 ⊢; omega, fun x hx => ?_⟩
      · intro x hx; simp at hx; rcases hx with rfl | hx; exact hh; exact i3 x (by simp [hx])
      · rw [List.getLast?_cons_cons] at hx
        rcases i5 x hx with h5 | h5
        · left; exact h5
        · right; simp at h5 ⊢; omega
    | none =>
      simp only [linkChain, hm]
      exact ⟨rfl, List.isChain_singleton _, by simp [hh], by simp, fun x hx => Or.inl (by simp at hx; subst hx; simpa using hm)⟩

/-- Along the successor relation the leaf count strictly decreases, so a chain has no repeats. -/
theorem chain_nodup {L : List Noun} {l : List Noun} (hc : List.IsChain (LR L) l) : l.Nodup := by
  have h1 : List.IsChain (fun a b : Noun => b.leaves < a.leaves) l :=
    hc.imp fun a b hab => by
      obtain ⟨e, -, -⟩ := linkSucc_some hab
      rw [e, leaves_up0]; omega
  have : IsTrans Noun (fun a b : Noun => b.leaves < a.leaves) := ⟨fun a b c h1 h2 => lt_trans h2 h1⟩
  have h2 := List.isChain_iff_pairwise.mp h1
  exact h2.imp fun h e => by subst e; omega

/-- Pigeonhole: a duplicate-free list inside `L` is at most `L` long. -/
theorem len_le_of_sub {l L : List Noun} (hn : l.Nodup) (hs : ∀ x ∈ l, x ∈ L) : l.length ≤ L.length :=
  (List.subperm_of_subset hn hs).length_le

/-- **The full chain**: from a member, with fuel `L.length`, the last element has no successor. -/
theorem linkChain_last (L : List Noun) (h : Noun) (hh : h ∈ L) :
    ∀ x, (linkChain L L.length h).getLast? = some x → linkSucc L x = none := by
  intro x hx
  obtain ⟨-, i2, i3, -, i5⟩ := linkChain_spec L L.length h hh
  rcases i5 x hx with h5 | h5
  · exact h5
  · have := len_le_of_sub (chain_nodup i2) i3; omega

/-- `linkHead` climbs `k ≤ f` steps through members, and stops early only at a top. -/
theorem linkHead_spec (L : List Noun) :
    ∀ (f : ℕ) (n : Noun), ∃ k ≤ f, linkHead L f n = up0^[k] n ∧
      (∀ i, 1 ≤ i → i ≤ k → up0^[i] n ∈ L) ∧ (k < f → up0 (up0^[k] n) ∉ L)
  | 0, n => ⟨0, le_rfl, rfl, fun i h1 h2 => by omega, fun h => by omega⟩
  | f + 1, n => by
    unfold linkHead
    split_ifs with hu
    · obtain ⟨k, hk, he, hm, ht⟩ := linkHead_spec L f (.cell (.atom 0) n)
      refine ⟨k + 1, by omega, ?_, fun i h1 h2 => ?_, fun h => ?_⟩
      · rw [he, Function.iterate_succ_apply]; rfl
      · rcases Nat.lt_or_ge i 2 with hi | hi
        · have : i = 1 := by omega
          subst this; exact hu
        · have := hm (i - 1) (by omega) (by omega)
          rw [show i = (i - 1) + 1 by omega, Function.iterate_succ_apply]; exact this
      · have := ht (by omega)
        rw [Function.iterate_succ_apply]; exact this
    · exact ⟨0, by omega, rfl, fun i h1 h2 => by omega, fun _ => hu⟩

/-- With fuel `L.length`, `linkHead` reaches a top: `[0 h] ∉ L`. -/
theorem linkHead_top (L : List Noun) (n : Noun) (hn : n ∈ L) :
    ∃ k, linkHead L L.length n = up0^[k] n ∧ (∀ i ≤ k, up0^[i] n ∈ L) ∧
      up0 (linkHead L L.length n) ∉ L := by
  obtain ⟨k, hk, he, hm, ht⟩ := linkHead_spec L L.length n
  have hm' : ∀ i ≤ k, up0^[i] n ∈ L := fun i hi => by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; exact hn
    · exact hm i h0 hi
  have hlt : k < L.length := by
    by_contra hge
    have hnd : ((List.range (k + 1)).map fun i => up0^[i] n).Nodup := by
      refine List.Nodup.map (fun a b hab => ?_) List.nodup_range
      have := congrArg Noun.leaves hab
      simp only [leaves_iter] at this; omega
    have := len_le_of_sub hnd (fun x hx => by
      simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact hm' i (by omega))
    simp at this; omega
  exact ⟨k, he, hm', by rw [he]; exact ht hlt⟩

/-- The downward path from `[0]^k n` reaches `n` within `k ≤ g` steps. -/
theorem mem_linkChain_iter (L : List Noun) (n : Noun) (hc : n.isCell = true) :
    ∀ (k g : ℕ), k ≤ g → (∀ i ≤ k, up0^[i] n ∈ L) → n ∈ linkChain L g (up0^[k] n)
  | 0, g, _, _ => by cases g <;> simp [linkChain] <;> split <;> simp
  | k + 1, g + 1, hk, hm => by
    rw [Function.iterate_succ_apply']
    have hc' : (up0^[k] n).isCell = true := by
      cases k with
      | zero => simpa using hc
      | succ k => rw [Function.iterate_succ_apply']; rfl
    simp only [linkChain, linkSucc_up0 (hm k (by omega)) hc']
    exact List.mem_cons_of_mem _ (mem_linkChain_iter L n hc k g (by omega) fun i hi => hm i (by omega))
  | k + 1, 0, hk, _ => by omega

/-- **The link-order invariant** of a list: every element's successor, if any, is the next element. -/
def LinkNext (L acc : List Noun) : Prop :=
  ∀ (i : ℕ) (hi : i < acc.length) (X : Noun), linkSucc L acc[i] = some X → acc[i + 1]? = some X

theorem linkNext_chain {L l : List Noun} (hc : List.IsChain (LR L) l)
    (hl : ∀ x, l.getLast? = some x → linkSucc L x = none) : LinkNext L l := by
  intro i hi X hX
  by_cases h1 : i + 1 < l.length
  · have := List.isChain_iff_getElem.mp hc i h1
    simp only [LR] at this
    rw [hX] at this
    cases this
    simp [h1]
  · have : l.getLast? = some l[i] := by
      rw [List.getLast?_eq_getElem?, show l.length - 1 = i by omega, List.getElem?_eq_getElem hi]
    rw [hl _ this] at hX; cases hX

theorem linkNext_append {L a c : List Noun} (ha : LinkNext L a) (hc : LinkNext L c) : LinkNext L (a ++ c) := by
  intro i hi X hX
  by_cases h1 : i < a.length
  · rw [List.getElem_append_left h1] at hX
    have := ha i h1 X hX
    by_cases h2 : i + 1 < a.length
    · rw [List.getElem?_append_left h2]; exact this
    · rw [List.getElem?_eq_none (by omega)] at this; cases this
  · rw [List.getElem_append_right (by omega)] at hX
    have := hc (i - a.length) (by simp at hi; omega) X hX
    rw [List.getElem?_append_right (by omega), show i + 1 - a.length = i - a.length + 1 by omega]
    exact this

/-- The successor of a member is a member. -/
theorem mem_of_linkNext {L acc : List Noun} (h : LinkNext L acc) {x X : Noun} (hx : x ∈ acc)
    (hX : linkSucc L x = some X) : X ∈ acc := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := h i hi X hX
  exact List.mem_of_getElem? this

/-- **The fold invariant** of `linkOrder`. -/
structure LInv (L acc : List Noun) : Prop where
  nodup : acc.Nodup
  sub : ∀ x ∈ acc, x ∈ L
  next : LinkNext L acc
  up : ∀ x ∈ acc, up0 x ∈ L → up0 x ∈ acc

theorem lInv_step (L : List Noun) (hcell : ∀ x ∈ L, x.isCell = true) {acc : List Noun} (hI : LInv L acc)
    {n : Noun} (hn : n ∈ L) (hna : n ∉ acc) :
    LInv L (acc ++ linkChain L L.length (linkHead L L.length n)) := by
  obtain ⟨k, hk, hmk, htop⟩ := linkHead_top L n hn
  set h := linkHead L L.length n with hh
  have hhL : h ∈ L := by rw [hk]; exact hmk k le_rfl
  set C := linkChain L L.length h with hC
  obtain ⟨c1, c2, c3, c4, -⟩ := linkChain_spec L L.length h hhL
  have cl := linkChain_last L h hhL
  rw [← hC] at c1 c2 c3 c4
  have hnC : n ∈ C := by
    rw [hC, hk]
    refine mem_linkChain_iter L n (hcell n hn) k L.length ?_ hmk
    by_contra hlt
    have hnd : ((List.range (k + 1)).map fun i => up0^[i] n).Nodup := by
      refine List.Nodup.map (fun a b hab => ?_) List.nodup_range
      have := congrArg Noun.leaves hab
      simp only [leaves_iter] at this; omega
    have := len_le_of_sub hnd (fun x hx => by
      simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact hmk i (by omega))
    simp at this; omega
  have hCne : C ≠ [] := by intro e; rw [e] at c1; simp at c1
  have h0 : C[0]'(List.length_pos_of_ne_nil hCne) = h := by
    rw [List.head?_eq_getElem?] at c1
    simpa [List.getElem?_eq_getElem (List.length_pos_of_ne_nil hCne)] using c1
  have hCnext : LinkNext L C := linkNext_chain c2 cl
  -- an element of `C` in `acc` puts the whole chain in `acc`
  have hdisj : ∀ x ∈ C, x ∉ acc := by
    intro x hxC hxa
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hxC
    -- climb to the head
    have climb : ∀ t, t ≤ j → C[j - t]'(by omega) ∈ acc := by
      intro t
      induction t with
      | zero => intro _; simpa using hxa
      | succ t ih =>
        intro ht
        have h1 := ih (by omega)
        have hch := List.isChain_iff_getElem.mp c2 (j - (t + 1)) (by omega)
        simp only [LR] at hch
        simp only [show j - (t + 1) + 1 = j - t by omega] at hch
        have e := (linkSucc_some hch).1
        rw [e]
        exact hI.up _ h1 (by rw [← e]; exact c3 _ (List.getElem_mem _))
    have hha : h ∈ acc := by have := climb j le_rfl; simp only [Nat.sub_self] at this; rwa [h0] at this
    -- descend through the whole chain
    have desc : ∀ t (ht : t < C.length), C[t] ∈ acc := by
      intro t
      induction t with
      | zero => intro ht; rw [h0]; exact hha
      | succ t ih =>
        intro ht
        have hch := List.isChain_iff_getElem.mp c2 t (by omega)
        simp only [LR] at hch
        exact mem_of_linkNext hI.next (ih (by omega)) hch
    obtain ⟨t, ht, hte⟩ := List.getElem_of_mem hnC
    exact hna (hte ▸ desc t ht)
  refine ⟨?_, ?_, linkNext_append hI.next hCnext, ?_⟩
  · exact List.nodup_append.mpr ⟨hI.nodup, chain_nodup c2, fun a ha b hb e => hdisj b hb (e ▸ ha)⟩
  · intro x hx; rcases List.mem_append.mp hx with hx | hx; exact hI.sub x hx; exact c3 x hx
  · intro x hx hu
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (hI.up x hx hu)
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0; rw [h0] at hu; exact absurd hu htop
      · have hch := List.isChain_iff_getElem.mp c2 (j - 1) (by omega)
        simp only [LR] at hch
        simp only [show j - 1 + 1 = j by omega] at hch
        rw [← (linkSucc_some hch).1]
        exact List.mem_append_right _ (List.getElem_mem _)

/-- **`linkOrder` is correct**: duplicate-free, the same members as `L`, and every element's link successor
`X` (the row `[0 X]`'s suffix `X ∈ L`) is the NEXT element. -/
theorem linkOrder_spec (L : List Noun) (hcell : ∀ x ∈ L, x.isCell = true) :
    (linkOrder L).Nodup ∧ (∀ x, x ∈ linkOrder L ↔ x ∈ L) ∧ LinkNext L (linkOrder L) := by
  have key : ∀ (l acc : List Noun), (∀ x ∈ l, x ∈ L) → LInv L acc →
      LInv L (l.foldl (fun acc n => if n ∈ acc then acc else
        acc ++ linkChain L L.length (linkHead L L.length n)) acc) ∧
      (∀ x ∈ acc, x ∈ l.foldl (fun acc n => if n ∈ acc then acc else
        acc ++ linkChain L L.length (linkHead L L.length n)) acc) ∧
      (∀ x ∈ l, x ∈ l.foldl (fun acc n => if n ∈ acc then acc else
        acc ++ linkChain L L.length (linkHead L L.length n)) acc) := by
    intro l
    induction l with
    | nil => intro acc _ hI; exact ⟨hI, fun x hx => hx, fun x hx => by simp at hx⟩
    | cons a l ih =>
      intro acc hl hI
      simp only [List.foldl_cons]
      have haL := hl a (by simp)
      have hstep : LInv L (if a ∈ acc then acc else acc ++ linkChain L L.length (linkHead L L.length a)) ∧
          a ∈ (if a ∈ acc then acc else acc ++ linkChain L L.length (linkHead L L.length a)) ∧
          ∀ x ∈ acc, x ∈ (if a ∈ acc then acc else acc ++ linkChain L L.length (linkHead L L.length a)) := by
        split_ifs with ha
        · exact ⟨hI, ha, fun x hx => hx⟩
        · refine ⟨lInv_step L hcell hI haL ha, ?_, fun x hx => List.mem_append_left _ hx⟩
          obtain ⟨k, hk, hmk, -⟩ := linkHead_top L a haL
          apply List.mem_append_right
          rw [hk]
          refine mem_linkChain_iter L a (hcell a haL) k L.length ?_ hmk
          by_contra hlt
          have hnd : ((List.range (k + 1)).map fun i => up0^[i] a).Nodup := by
            refine List.Nodup.map (fun x y hxy => ?_) List.nodup_range
            have := congrArg Noun.leaves hxy
            simp only [leaves_iter] at this; omega
          have := len_le_of_sub hnd (fun x hx => by
            simp only [List.mem_map, List.mem_range] at hx
            obtain ⟨i, hi, rfl⟩ := hx
            exact hmk i (by omega))
          simp at this; omega
      obtain ⟨r1, r2, r3⟩ := ih _ (fun x hx => hl x (by simp [hx])) hstep.1
      refine ⟨r1, fun x hx => r2 x (hstep.2.2 x hx), fun x hx => ?_⟩
      simp at hx
      rcases hx with rfl | hx
      · exact r2 x hstep.2.1
      · exact r3 x hx
  have hI0 : LInv L [] := ⟨List.nodup_nil, by simp, fun i hi => by simp at hi, by simp⟩
  obtain ⟨r1, -, r3⟩ := key L [] (fun x hx => hx) hI0
  exact ⟨r1.nodup, fun x => ⟨r1.sub x, r3 x⟩, r1.next⟩



end Gen5

section Gen6
open Nock.V1J8.Gen
open Nock.Atoms (B)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (keyP ptrP valROfK incChainK)

/-! ## 6. The generator's inc chains (`GenAtom.incChain`) -/

section Chain
variable {rows : Array Nock.Edit.GenX.RowNX}

theorem spineOf_cons2 (l : List ℕ) (h : 2 ≤ l.length) : spineOf l = combOf l :: spineOf l.tail := by
  match l, h with
  | x :: y :: r, _ => rfl

theorem spineOf_short (l : List ℕ) (h : l.length < 2) : spineOf l = [] := by
  match l, h with
  | [], _ => rfl
  | [x], _ => rfl

theorem combOf_cons (x : ℕ) (l : List ℕ) (h : 2 ≤ l.length) : combOf (x :: l) = .cell (.atom x) (combOf l) := by
  match l, h with
  | y :: z :: r, _ => rfl

theorem atomV_hd_combOf (l : List ℕ) (h : 2 ≤ l.length) : atomV (hdN' (combOf l)) = l.headD 0 := by
  match l, h with
  | [x, y], _ => rfl
  | x :: y :: z :: r, _ => rfl

theorem valROf_combOf (acsL : List Noun) (l : List ℕ) (h : 2 ≤ l.length) :
    valROf acsL (combOf l) = if 3 ≤ l.length then (1, idxOf acsL (combOf l.tail)) else (0, l.getD 1 0) := by
  match l, h with
  | [x, y], _ => simp [valROf, combOf, tlN']
  | x :: y :: z :: r, _ =>
    rw [combOf_cons x (y :: z :: r) (by simp)]
    cases r <;> simp [valROf, tlN', combOf]

theorem valROfK_combOf (ptr : Noun → ℕ) (l : List ℕ) (h : 2 ≤ l.length) :
    valROfK ptr (combOf l) = if 3 ≤ l.length then (1, ptr (combOf l)) else (0, l.getD 1 0) := by
  match l, h with
  | [x, y], _ => simp [valROfK, combOf, tlN']
  | x :: y :: z :: r, _ =>
    rw [combOf_cons x (y :: z :: r) (by simp)]
    cases r <;> simp [valROfK, tlN', combOf]

/-- The carry-continue condition of an old suffix (`c_out ∧ kR_o = 1`). -/
def Cnd (l : List ℕ) : Prop := l.headD 0 = B - 1 ∧ 3 ≤ l.length

instance (l : List ℕ) : Decidable (Cnd l) := by unfold Cnd; infer_instance

/-- Depth `d` is written by `incChain` at fuel `f` on the new / old limb lists `ln`, `lo`. -/
def Reach (f : ℕ) (ln lo : List ℕ) (d : ℕ) : Prop :=
  d < f ∧ 2 ≤ (ln.drop d).length ∧ 2 ≤ (lo.drop d).length ∧ ∀ i < d, Cnd (lo.drop i)

theorem drop_succ' (l : List ℕ) (d : ℕ) : l.drop (d + 1) = l.tail.drop d := by
  cases l <;> simp

theorem reach_succ {f : ℕ} {ln lo : List ℕ} {d : ℕ} :
    Reach (f + 1) ln lo (d + 1) ↔ Cnd lo ∧ Reach f ln.tail lo.tail d := by
  unfold Reach
  rw [drop_succ' ln, drop_succ' lo]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by simpa using h4 0 (by omega), by omega, h2, h3, fun i hi => ?_⟩
    have := h4 (i + 1) (by omega)
    rwa [drop_succ'] at this
  · rintro ⟨hc, h1, h2, h3, h4⟩
    refine ⟨by omega, h2, h3, fun i hi => ?_⟩
    rcases i with _ | i
    · simpa using hc
    · have := h4 i (by omega)
      rwa [drop_succ']

/-- The fields an inc row carries, read off its old suffix `l` (as `incChain` writes them). -/
def FieldsEq (p : ℕ) (acsL : List Noun) (rows : Array Nock.Edit.GenX.RowNX) (x : AInfo) (l : List ℕ) : Prop :=
  x.idxO = keyP p acsL (combOf l) ∧ x.lO = l.headD 0 ∧ x.cout = decide (l.headD 0 = B - 1) ∧
    x.kRO = (if 3 ≤ l.length then 1 else 0) ∧
    x.vRO = (if 3 ≤ l.length then ptrP p acsL rows (combOf l) else l.getD 1 0)

/-- A non-inc row carries zero chain fields. -/
def ZeroF (x : AInfo) : Prop := x.cout = false ∧ x.idxO = 0 ∧ x.lO = 0 ∧ x.kRO = 0 ∧ x.vRO = 0

/-- **The array invariant**: every inc row carries the fields of its old suffix `lof j`, every other row zero
chain fields. -/
def ArrOK (p : ℕ) (acsL : List Noun) (lof : ℕ → List ℕ) (rows : Array Nock.Edit.GenX.RowNX) (a : Array AInfo) : Prop :=
  ∀ j, ((a.getD j AInfo.z).inc = true → FieldsEq p acsL rows (a.getD j AInfo.z) (lof j)) ∧
    ((a.getD j AInfo.z).inc = false → ZeroF (a.getD j AInfo.z))

theorem getD_modify (a : Array AInfo) (i j : ℕ) (g : AInfo → AInfo) :
    (a.modify i g).getD j AInfo.z = if i = j ∧ j < a.size then g (a.getD j AInfo.z) else a.getD j AInfo.z := by
  by_cases hj : j < a.size
  · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify, hj, and_true]
    rw [Array.getElem?_eq_getElem hj]
    split_ifs <;> simp
  · have : ¬ j < (a.modify i g).size := by simpa using hj
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega : a.size ≤ j),
      Array.getElem?_eq_none (by simpa using (by omega : a.size ≤ j)), hj]

theorem size_incChain (p : ℕ) (acsL : List Noun) :
    ∀ (f : ℕ) (ns os : List Noun) (a : Array AInfo), (incChainK acsL (keyP p acsL) (ptrP p acsL rows) f ns os a).size = a.size
  | 0, _, _, a => rfl
  | _ + 1, [], _, a => rfl
  | _ + 1, _ :: _, [], a => rfl
  | f + 1, n :: ns, o :: os, a => by
    simp only [incChainK]
    split_ifs <;> simp [size_incChain p acsL f ns os]


/-- One `incChain` write: the new row `[ln]` gets the inc fields of the old suffix `lo`, the old row a consume. -/
noncomputable def wrA (p : ℕ) (acsL : List Noun) (rows : Array Nock.Edit.GenX.RowNX) (ln lo : List ℕ) (a : Array AInfo) : Array AInfo :=
  (a.modify (idxOf acsL (combOf ln)) fun x =>
    ⟨true, x.conv, decide (lo.headD 0 = B - 1), keyP p acsL (combOf lo), lo.headD 0,
      (if 3 ≤ lo.length then 1 else 0),
      (if 3 ≤ lo.length then ptrP p acsL rows (combOf lo) else lo.getD 1 0), x.mi, x.mhx⟩).modify
    (keyP p acsL (combOf lo)) fun x => ⟨x.inc, x.conv, x.cout, x.idxO, x.lO, x.kRO, x.vRO, x.mi, x.mhx + 1⟩

theorem incChain_step (p : ℕ) (acsL : List Noun) (f : ℕ) (ln lo : List ℕ) (a : Array AInfo) (hn : 2 ≤ ln.length)
    (ho : 2 ≤ lo.length) :
    incChainK acsL (keyP p acsL) (ptrP p acsL rows) (f + 1) (spineOf ln) (spineOf lo) a =
      if Cnd lo then incChainK acsL (keyP p acsL) (ptrP p acsL rows) f (spineOf ln.tail) (spineOf lo.tail) (wrA p acsL rows ln lo a)
      else wrA p acsL rows ln lo a := by
  rw [spineOf_cons2 ln hn, spineOf_cons2 lo ho]
  simp only [incChainK, valROfK_combOf (ptrP p acsL rows) lo ho, atomV_hd_combOf lo ho]
  by_cases h3 : 3 ≤ lo.length
  · simp only [h3, ite_true, Cnd, and_true, wrA, beq_self_eq_true, Bool.and_true, decide_eq_true_eq]
  · simp only [h3, ite_false, Cnd, and_false, wrA, Bool.and_false, ite_false]
    simp

theorem size_wrA (p : ℕ) (acsL : List Noun) (ln lo : List ℕ) (a : Array AInfo) : (wrA p acsL rows ln lo a).size = a.size := by
  simp [wrA]


theorem inc_wrA (p : ℕ) (acsL : List Noun) (ln lo : List ℕ) (a : Array AInfo) (k : ℕ) :
    ((wrA p acsL rows ln lo a).getD k AInfo.z).inc = true ↔
      (a.getD k AInfo.z).inc = true ∨ (k < a.size ∧ k = idxOf acsL (combOf ln)) := by
  simp only [wrA]
  rw [getD_modify, getD_modify]
  simp only [Array.size_modify]
  by_cases h1 : idxOf acsL (combOf ln) = k ∧ k < a.size
  · rw [if_pos h1]; split_ifs <;> simp [h1.2, h1.1]
  · rw [if_neg h1]; split_ifs <;> simp <;> omega

theorem exists_reach_iff {f : ℕ} {ln lo : List ℕ} (hn : 2 ≤ ln.length) (ho : 2 ≤ lo.length)
    (P : List ℕ → Prop) :
    (∃ d, Reach (f + 1) ln lo d ∧ P (ln.drop d)) ↔
      P ln ∨ (Cnd lo ∧ ∃ d, Reach f ln.tail lo.tail d ∧ P (ln.tail.drop d)) := by
  constructor
  · rintro ⟨d, hr, hp⟩
    rcases d with _ | d
    · exact Or.inl (by simpa using hp)
    · obtain ⟨hc, hr'⟩ := reach_succ.mp hr
      exact Or.inr ⟨hc, d, hr', by rwa [drop_succ'] at hp⟩
  · rintro (hp | ⟨hc, d, hr, hp⟩)
    · exact ⟨0, ⟨by omega, by simpa using hn, by simpa using ho, fun i hi => by omega⟩, by simpa using hp⟩
    · exact ⟨d + 1, reach_succ.mpr ⟨hc, hr⟩, by rwa [drop_succ']⟩

/-- **Which rows `incChain` marks inc.** -/
theorem incChain_inc (p : ℕ) (acsL : List Noun) :
    ∀ (f : ℕ) (ln lo : List ℕ) (a : Array AInfo) (j : ℕ),
      ((incChainK acsL (keyP p acsL) (ptrP p acsL rows) f (spineOf ln) (spineOf lo) a).getD j AInfo.z).inc = true ↔
        (a.getD j AInfo.z).inc = true ∨
          (j < a.size ∧ ∃ d, Reach f ln lo d ∧ j = idxOf acsL (combOf (ln.drop d)))
  | 0, ln, lo, a, j => by simp [incChainK, Reach]
  | f + 1, ln, lo, a, j => by
    by_cases hn : 2 ≤ ln.length
    · by_cases ho : 2 ≤ lo.length
      · rw [incChain_step p acsL f ln lo a hn ho]
        have E := exists_reach_iff (f := f) hn ho (fun l => j = idxOf acsL (combOf l))
        split_ifs with hc
        · rw [incChain_inc p acsL f ln.tail lo.tail (wrA p acsL rows ln lo a) j, inc_wrA, size_wrA]
          constructor
          · rintro ((h | ⟨h1, h2⟩) | ⟨h1, d, hd, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨h1, E.mpr (Or.inl h2)⟩
            · exact Or.inr ⟨h1, E.mpr (Or.inr ⟨hc, d, hd, h2⟩)⟩
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl (Or.inl h)
            · rcases E.mp h2 with h3 | ⟨-, d, hd, h3⟩
              · exact Or.inl (Or.inr ⟨h1, h3⟩)
              · exact Or.inr ⟨h1, d, hd, h3⟩
        · rw [inc_wrA]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨h1, E.mpr (Or.inl h2)⟩
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · rcases E.mp h2 with h3 | ⟨hc', -⟩
              · exact Or.inr ⟨h1, h3⟩
              · exact absurd hc' hc
      · rw [spineOf_short lo (by omega)]
        cases spineOf ln <;> simp only [incChainK] <;>
        · simp only [Reach, List.drop_eq_nil_iff, List.length_drop]
          constructor
          · intro h; exact Or.inl h
          · rintro (h | ⟨-, d, ⟨-, -, h3, -⟩, -⟩); exact h; omega
    · rw [spineOf_short ln (by omega)]
      simp only [incChainK]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨-, d, ⟨-, h2, -, -⟩, -⟩); exact h; simp at h2; omega

theorem wrA_ok (p : ℕ) (acsL : List Noun) (lof : ℕ → List ℕ) (ln lo : List ℕ) (a : Array AInfo)
    (ha : ArrOK p acsL lof rows a) (hl : lof (idxOf acsL (combOf ln)) = lo) : ArrOK p acsL lof rows (wrA p acsL rows ln lo a) := by
  intro j
  simp only [wrA]
  rw [getD_modify, getD_modify]
  simp only [Array.size_modify]
  obtain ⟨h1, h2⟩ := ha j
  by_cases hw : idxOf acsL (combOf ln) = j ∧ j < a.size
  · rw [if_pos hw]
    have hl' : lof j = lo := hw.1 ▸ hl
    refine ⟨fun _ => ?_, fun h => ?_⟩
    · rw [hl']; unfold FieldsEq; split_ifs <;> simp_all
    · split_ifs at h
  · rw [if_neg hw]
    split_ifs
    · exact ⟨fun h => h1 h, fun h => h2 h⟩
    · exact ⟨h1, h2⟩

/-- **`incChain` keeps the array invariant** when every written row's old suffix is the old suffix written. -/
theorem incChain_ok (p : ℕ) (acsL : List Noun) (lof : ℕ → List ℕ) :
    ∀ (f : ℕ) (ln lo : List ℕ) (a : Array AInfo), ArrOK p acsL lof rows a →
      (∀ d, Reach f ln lo d → lof (idxOf acsL (combOf (ln.drop d))) = lo.drop d) →
      ArrOK p acsL lof rows (incChainK acsL (keyP p acsL) (ptrP p acsL rows) f (spineOf ln) (spineOf lo) a)
  | 0, ln, lo, a, ha, _ => by simpa [incChainK] using ha
  | f + 1, ln, lo, a, ha, hl => by
    by_cases hn : 2 ≤ ln.length
    · by_cases ho : 2 ≤ lo.length
      · rw [incChain_step p acsL f ln lo a hn ho]
        have h0 : lof (idxOf acsL (combOf ln)) = lo := by
          simpa using hl 0 ⟨by omega, by simpa using hn, by simpa using ho, fun i hi => by omega⟩
        have hw := wrA_ok p acsL lof ln lo a ha h0
        split_ifs with hc
        · refine incChain_ok p acsL lof f ln.tail lo.tail _ hw fun d hd => ?_
          have := hl (d + 1) (reach_succ.mpr ⟨hc, hd⟩)
          rwa [drop_succ', drop_succ'] at this
        · exact hw
      · rw [spineOf_short lo (by omega)]
        cases spineOf ln <;> simpa [incChainK] using ha
    · rw [spineOf_short ln (by omega)]
      simpa [incChainK] using ha

/-! ### The fold over the slow OP4 operands (`ComplJ8Data.infoOfP`) -/

section Fold
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (incOpsP infoOfP rootIdxP)
open Nock.Edit Nock.Edit.GenX

/-- The fuel of `v`'s chain. -/
def fuelOf (v : ℕ) : ℕ := (spineOf (Nock.Atoms.limbs v)).length + 1

/-- One step of `infoOfP`'s fold. -/
noncomputable def stepF (p : ℕ) (acsL : List Noun) (rows : Array Nock.Edit.GenX.RowNX) (a : Array AInfo) (vc : ℕ × ℕ) : Array AInfo :=
  if vc.1 + 1 = p then
    a.modify (rootIdxP p acsL p) fun x => { x with conv := true, mi := x.mi + vc.2 }
  else
    (incChainK acsL (keyP p acsL) (ptrP p acsL rows) (fuelOf vc.1) (spineOf (Nock.Atoms.limbs (vc.1 + 1)))
      (spineOf (Nock.Atoms.limbs vc.1)) a).modify
      (rootIdxP p acsL (vc.1 + 1)) fun x => { x with mi := x.mi + vc.2 }

/-- The fold of `infoOfP` before the `mhx` recount. -/
noncomputable def infoFold (p : ℕ) (acsL : List Noun) (rows : Array Nock.Edit.GenX.RowNX) : Array AInfo :=
  (incOpsP p rows).foldl (stepF p acsL rows) (Array.replicate acsL.length AInfo.z)

theorem infoOfP_eq (p : ℕ) (acsL : List Noun) (rows : Array Nock.Edit.GenX.RowNX) :
    infoOfP p acsL rows = recountMhx (infoFold p acsL rows) := rfl

/-- **The recount changes `mhx` only.** -/
theorem getD_recountMhx (a : Array AInfo) (k : ℕ) :
    (recountMhx a).getD k AInfo.z = if k < a.size then { a.getD k AInfo.z with mhx := mhxOf a k } else AInfo.z := by
  by_cases hk : k < a.size
  · simp [recountMhx, Array.getD_eq_getD_getElem?, Array.getElem?_mapIdx, hk]
  · simp [recountMhx, Array.getD_eq_getD_getElem?, Array.getElem?_mapIdx, hk]

theorem recountMhx_size (a : Array AInfo) : (recountMhx a).size = a.size := by simp [recountMhx]

theorem getD_of_size_le (a : Array AInfo) (k : ℕ) (hk : ¬ k < a.size) : a.getD k AInfo.z = AInfo.z := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega : a.size ≤ k)]

/-- Every field but `mhx` of a recounted row is the row's. -/
theorem recountMhx_fields (a : Array AInfo) (k : ℕ) :
    ((recountMhx a).getD k AInfo.z).inc = (a.getD k AInfo.z).inc ∧
    ((recountMhx a).getD k AInfo.z).conv = (a.getD k AInfo.z).conv ∧
    ((recountMhx a).getD k AInfo.z).cout = (a.getD k AInfo.z).cout ∧
    ((recountMhx a).getD k AInfo.z).idxO = (a.getD k AInfo.z).idxO ∧
    ((recountMhx a).getD k AInfo.z).lO = (a.getD k AInfo.z).lO ∧
    ((recountMhx a).getD k AInfo.z).kRO = (a.getD k AInfo.z).kRO ∧
    ((recountMhx a).getD k AInfo.z).vRO = (a.getD k AInfo.z).vRO ∧
    ((recountMhx a).getD k AInfo.z).mi = (a.getD k AInfo.z).mi := by
  rw [getD_recountMhx]
  split_ifs with hk
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`infoOfP` against the bare fold**: every field but `idxO` (and `mhx`) is the fold's. -/
theorem info_fields (p : ℕ) (acsL : List Noun) (rows : Array Nock.Edit.GenX.RowNX) (k : ℕ) :
    ((infoOfP p acsL rows).getD k AInfo.z).inc = ((infoFold p acsL rows).getD k AInfo.z).inc ∧
    ((infoOfP p acsL rows).getD k AInfo.z).conv = ((infoFold p acsL rows).getD k AInfo.z).conv ∧
    ((infoOfP p acsL rows).getD k AInfo.z).cout = ((infoFold p acsL rows).getD k AInfo.z).cout ∧
    ((infoOfP p acsL rows).getD k AInfo.z).lO = ((infoFold p acsL rows).getD k AInfo.z).lO ∧
    ((infoOfP p acsL rows).getD k AInfo.z).kRO = ((infoFold p acsL rows).getD k AInfo.z).kRO ∧
    ((infoOfP p acsL rows).getD k AInfo.z).vRO = ((infoFold p acsL rows).getD k AInfo.z).vRO ∧
    ((infoOfP p acsL rows).getD k AInfo.z).mi = ((infoFold p acsL rows).getD k AInfo.z).mi := by
  rw [infoOfP_eq]
  obtain ⟨r1, r2, r3, -, r5, r6, r7, r8⟩ := recountMhx_fields (infoFold p acsL rows) k
  exact ⟨r1, r2, r3, r5, r6, r7, r8⟩

/-- **`infoOfP`'s `idxO`** is the fold's (G12 variant 3: no `fixOld` post-pass). -/
theorem info_idxO (p : ℕ) (acsL : List Noun) (rows : Array Nock.Edit.GenX.RowNX) (k : ℕ) :
    ((infoOfP p acsL rows).getD k AInfo.z).idxO = ((infoFold p acsL rows).getD k AInfo.z).idxO := by
  rw [infoOfP_eq]; exact (recountMhx_fields _ k).2.2.2.1

theorem info_size (p : ℕ) (acsL : List Noun) (rows : Array Nock.Edit.GenX.RowNX) :
    (infoOfP p acsL rows).size = (infoFold p acsL rows).size := by
  rw [infoOfP_eq, recountMhx_size]

variable (p : ℕ) (acsL : List Noun) (lof : ℕ → List ℕ)

/-- Row `k` is reached by the chain of an operand in `S`. -/
def IncR (S : List (ℕ × ℕ)) (k : ℕ) : Prop :=
  k < acsL.length ∧ ∃ vc ∈ S, vc.1 + 1 ≠ p ∧ ∃ d, Reach (fuelOf vc.1) (Nock.Atoms.limbs (vc.1 + 1))
    (Nock.Atoms.limbs vc.1) d ∧ k = idxOf acsL (combOf ((Nock.Atoms.limbs (vc.1 + 1)).drop d))

/-- **The fold invariant.** -/
structure StInv (rows : Array Nock.Edit.GenX.RowNX) (S : List (ℕ × ℕ)) (a : Array AInfo) : Prop where
  size : a.size = acsL.length
  ok : ArrOK p acsL lof rows a
  inc : ∀ k, (a.getD k AInfo.z).inc = true ↔ IncR p acsL S k
  conv : ∀ k, (a.getD k AInfo.z).conv = true → ∃ vc ∈ S, vc.1 + 1 = p ∧ k = rootIdxP p acsL p
  mi : ∀ k, (a.getD k AInfo.z).mi ≠ 0 → ∃ vc ∈ S, k = rootIdxP p acsL (vc.1 + 1)

theorem incChain_conv_mi (p : ℕ) (acsL : List Noun) :
    ∀ (f : ℕ) (ln lo : List ℕ) (a : Array AInfo) (k : ℕ),
      ((incChainK acsL (keyP p acsL) (ptrP p acsL rows) f (spineOf ln) (spineOf lo) a).getD k AInfo.z).conv = (a.getD k AInfo.z).conv ∧
      ((incChainK acsL (keyP p acsL) (ptrP p acsL rows) f (spineOf ln) (spineOf lo) a).getD k AInfo.z).mi = (a.getD k AInfo.z).mi
  | 0, ln, lo, a, k => by simp [incChainK]
  | f + 1, ln, lo, a, k => by
    by_cases hn : 2 ≤ ln.length
    · by_cases ho : 2 ≤ lo.length
      · rw [incChain_step p acsL f ln lo a hn ho]
        have hw : ((wrA p acsL rows ln lo a).getD k AInfo.z).conv = (a.getD k AInfo.z).conv ∧
            ((wrA p acsL rows ln lo a).getD k AInfo.z).mi = (a.getD k AInfo.z).mi := by
          simp only [wrA]; rw [getD_modify, getD_modify]; simp only [Array.size_modify]
          split_ifs <;> simp
        split_ifs
        · obtain ⟨h1, h2⟩ := incChain_conv_mi p acsL f ln.tail lo.tail (wrA p acsL rows ln lo a) k
          exact ⟨h1.trans hw.1, h2.trans hw.2⟩
        · exact hw
      · rw [spineOf_short lo (by omega)]
        cases spineOf ln <;> simp [incChainK]
    · rw [spineOf_short ln (by omega)]
      simp [incChainK]

/-- Two rows agree on the inc flag and the chain fields. -/
def SameF (x y : AInfo) : Prop :=
  x.inc = y.inc ∧ x.cout = y.cout ∧ x.idxO = y.idxO ∧ x.lO = y.lO ∧ x.kRO = y.kRO ∧ x.vRO = y.vRO

theorem arrOK_congr {a b : Array AInfo} (h : ∀ k, SameF (b.getD k AInfo.z) (a.getD k AInfo.z))
    (ha : ArrOK p acsL lof rows a) : ArrOK p acsL lof rows b := by
  intro k
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h k
  obtain ⟨g1, g2⟩ := ha k
  unfold FieldsEq ZeroF at *
  rw [h1, h2, h3, h4, h5, h6]
  exact ⟨g1, g2⟩

theorem incR_append (S : List (ℕ × ℕ)) (vc : ℕ × ℕ) (k : ℕ) :
    IncR p acsL (S ++ [vc]) k ↔ IncR p acsL S k ∨ (k < acsL.length ∧ vc.1 + 1 ≠ p ∧ ∃ d,
      Reach (fuelOf vc.1) (Nock.Atoms.limbs (vc.1 + 1)) (Nock.Atoms.limbs vc.1) d ∧
        k = idxOf acsL (combOf ((Nock.Atoms.limbs (vc.1 + 1)).drop d))) := by
  unfold IncR
  constructor
  · rintro ⟨hk, w, hw, h1, h2⟩
    rcases List.mem_append.mp hw with hw | hw
    · exact Or.inl ⟨hk, w, hw, h1, h2⟩
    · simp at hw; subst hw; exact Or.inr ⟨hk, h1, h2⟩
  · rintro (⟨hk, w, hw, h1, h2⟩ | ⟨hk, h1, h2⟩)
    · exact ⟨hk, w, List.mem_append_left _ hw, h1, h2⟩
    · exact ⟨hk, vc, by simp, h1, h2⟩

theorem stInv_step (S : List (ℕ × ℕ)) (a : Array AInfo) (vc : ℕ × ℕ) (hI : StInv p acsL lof rows S a)
    (hl : vc.1 + 1 ≠ p → ∀ d, Reach (fuelOf vc.1) (Nock.Atoms.limbs (vc.1 + 1)) (Nock.Atoms.limbs vc.1) d →
      lof (idxOf acsL (combOf ((Nock.Atoms.limbs (vc.1 + 1)).drop d))) = (Nock.Atoms.limbs vc.1).drop d) :
    StInv p acsL lof rows (S ++ [vc]) (stepF p acsL rows a vc) := by
  unfold stepF
  split_ifs with hp
  · have hf : ∀ k, SameF ((a.modify (rootIdxP p acsL p) fun x => { x with conv := true, mi := x.mi + vc.2 }).getD k
        AInfo.z) (a.getD k AInfo.z) :=
      fun k => by rw [getD_modify]; split_ifs <;> simp [SameF]
    refine ⟨by simp [hI.size], arrOK_congr p acsL lof hf hI.ok, fun k => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · rw [(hf k).1, hI.inc k, incR_append]
      constructor
      · exact Or.inl
      · rintro (h | ⟨-, h, -⟩); exact h; exact absurd hp h
    · rw [getD_modify] at hk
      split_ifs at hk with hr
      · exact ⟨vc, by simp, hp, hr.1.symm⟩
      · obtain ⟨w, hw, h1, h2⟩ := hI.conv k hk
        exact ⟨w, List.mem_append_left _ hw, h1, h2⟩
    · rw [getD_modify] at hk
      split_ifs at hk with hr
      · exact ⟨vc, by simp, by rw [hr.1.symm, hp]⟩
      · obtain ⟨w, hw, h1⟩ := hI.mi k hk
        exact ⟨w, List.mem_append_left _ hw, h1⟩
  · set a1 := incChainK acsL (keyP p acsL) (ptrP p acsL rows) (fuelOf vc.1) (spineOf (Nock.Atoms.limbs (vc.1 + 1))) (spineOf (Nock.Atoms.limbs vc.1)) a
      with ha1
    have hs1 : a1.size = a.size := size_incChain _ _ _ _ _ _
    have hf : ∀ k, SameF ((a1.modify (rootIdxP p acsL (vc.1 + 1)) fun x => { x with mi := x.mi + vc.2 }).getD k
        AInfo.z) (a1.getD k AInfo.z) :=
      fun k => by rw [getD_modify]; split_ifs <;> simp [SameF]
    have hcm := fun k => incChain_conv_mi (rows := rows) p acsL (fuelOf vc.1) (Nock.Atoms.limbs (vc.1 + 1)) (Nock.Atoms.limbs vc.1) a k
    refine ⟨by simp [hs1, hI.size], arrOK_congr p acsL lof hf (incChain_ok p acsL lof _ _ _ a hI.ok (hl hp)),
      fun k => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · rw [(hf k).1, ha1, incChain_inc, hI.inc k, incR_append, hI.size]
      constructor
      · rintro (h | ⟨h1, d, h2, h3⟩); exact Or.inl h; exact Or.inr ⟨h1, hp, d, h2, h3⟩
      · rintro (h | ⟨h1, -, d, h2, h3⟩); exact Or.inl h; exact Or.inr ⟨h1, d, h2, h3⟩
    · rw [getD_modify] at hk
      have hk' : (a.getD k AInfo.z).conv = true := by
        rw [← (hcm k).1]; split_ifs at hk <;> simpa using hk
      obtain ⟨w, hw, h1, h2⟩ := hI.conv k hk'
      exact ⟨w, List.mem_append_left _ hw, h1, h2⟩
    · rw [getD_modify] at hk
      split_ifs at hk with hr
      · exact ⟨vc, by simp, hr.1.symm⟩
      · rw [(hcm k).2] at hk
        obtain ⟨w, hw, h1⟩ := hI.mi k hk
        exact ⟨w, List.mem_append_left _ hw, h1⟩

/-- **The fold**: the bare fold `infoFold` satisfies the invariant over all its operands. -/
theorem stInv_infoFold (rows : Array Nock.Edit.GenX.RowNX)
    (hl : ∀ vc ∈ incOpsP p rows, vc.1 + 1 ≠ p → ∀ d, Reach (fuelOf vc.1) (Nock.Atoms.limbs (vc.1 + 1))
      (Nock.Atoms.limbs vc.1) d →
      lof (idxOf acsL (combOf ((Nock.Atoms.limbs (vc.1 + 1)).drop d))) = (Nock.Atoms.limbs vc.1).drop d) :
    StInv p acsL lof rows (incOpsP p rows) (infoFold p acsL rows) := by
  have key : ∀ (l S : List (ℕ × ℕ)) (a : Array AInfo), StInv p acsL lof rows S a → (∀ vc ∈ l, vc ∈ incOpsP p rows) →
      StInv p acsL lof rows (S ++ l) (l.foldl (stepF p acsL rows) a) := by
    intro l
    induction l with
    | nil => intro S a h _; simpa using h
    | cons vc l ih =>
      intro S a h hm
      have := ih (S ++ [vc]) _ (stInv_step p acsL lof S a vc h (hl vc (hm vc (by simp))))
        (fun w hw => hm w (by simp [hw]))
      simpa using this
  have h0 : StInv p acsL lof rows [] (Array.replicate acsL.length AInfo.z) := by
    refine ⟨by simp, fun k => ?_, fun k => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · have : (Array.replicate acsL.length AInfo.z).getD k AInfo.z = AInfo.z := by
        simp [Array.getD_eq_getD_getElem?]
        by_cases hk : k < acsL.length <;> simp [hk]
      rw [this]; exact ⟨fun h => by simp [AInfo.z] at h, fun _ => by simp [ZeroF, AInfo.z]⟩
    · have : (Array.replicate acsL.length AInfo.z).getD k AInfo.z = AInfo.z := by
        simp [Array.getD_eq_getD_getElem?]
        by_cases hk : k < acsL.length <;> simp [hk]
      rw [this]; simp [AInfo.z, IncR]
    · have : (Array.replicate acsL.length AInfo.z).getD k AInfo.z = AInfo.z := by
        simp [Array.getD_eq_getD_getElem?]
        by_cases hk : k < acsL.length <;> simp [hk]
      rw [this] at hk; simp [AInfo.z] at hk
    · have : (Array.replicate acsL.length AInfo.z).getD k AInfo.z = AInfo.z := by
        simp [Array.getD_eq_getD_getElem?]
        by_cases hk : k < acsL.length <;> simp [hk]
      rw [this] at hk; simp [AInfo.z] at hk
  simpa [infoFold] using key (incOpsP p rows) [] _ h0 (fun vc h => h)

/-- The fields an inc row carries other than its old index (`FieldsEq` without `idxO`; fix (B) sets the depth-0
old index of `p` apart). -/
def FieldsEqX (p : ℕ) (acsL : List Noun) (rows : Array Nock.Edit.GenX.RowNX) (x : AInfo) (l : List ℕ) : Prop :=
  x.lO = l.headD 0 ∧ x.cout = decide (l.headD 0 = B - 1) ∧ x.kRO = (if 3 ≤ l.length then 1 else 0) ∧
    x.vRO = (if 3 ≤ l.length then ptrP p acsL rows (combOf l) else l.getD 1 0)

/-- The array invariant without the inc rows' `idxO`. -/
def ArrOKX (rows : Array Nock.Edit.GenX.RowNX) (a : Array AInfo) : Prop :=
  ∀ j, ((a.getD j AInfo.z).inc = true → FieldsEqX p acsL rows (a.getD j AInfo.z) (lof j)) ∧
    ((a.getD j AInfo.z).inc = false → ZeroF (a.getD j AInfo.z))

/-- **The invariant of `infoOfP`** (after the fix-(B) post-pass and the `mhx` recount). -/
structure StInvP (rows : Array Nock.Edit.GenX.RowNX) (S : List (ℕ × ℕ)) (a : Array AInfo) : Prop where
  size : a.size = acsL.length
  ok : ArrOKX p acsL lof rows a
  inc : ∀ k, (a.getD k AInfo.z).inc = true ↔ IncR p acsL S k
  conv : ∀ k, (a.getD k AInfo.z).conv = true → ∃ vc ∈ S, vc.1 + 1 = p ∧ k = rootIdxP p acsL p
  mi : ∀ k, (a.getD k AInfo.z).mi ≠ 0 → ∃ vc ∈ S, k = rootIdxP p acsL (vc.1 + 1)

/-- **The fold, at `infoOfP`**: every field but the inc rows' `idxO` as `stInv_infoFold`. -/
theorem stInv_infoOfP (rows : Array Nock.Edit.GenX.RowNX)
    (hl : ∀ vc ∈ incOpsP p rows, vc.1 + 1 ≠ p → ∀ d, Reach (fuelOf vc.1) (Nock.Atoms.limbs (vc.1 + 1))
      (Nock.Atoms.limbs vc.1) d →
      lof (idxOf acsL (combOf ((Nock.Atoms.limbs (vc.1 + 1)).drop d))) = (Nock.Atoms.limbs vc.1).drop d) :
    StInvP p acsL lof rows (incOpsP p rows) (infoOfP p acsL rows) := by
  have hF := stInv_infoFold p acsL lof rows hl
  have hR := info_fields p acsL rows
  refine ⟨by rw [info_size]; exact hF.size, fun k => ?_, fun k => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨h1, h2, h3, h5, h6, h7, -⟩ := hR k
    obtain ⟨g1, g2⟩ := hF.ok k
    rw [h1]
    refine ⟨fun hi => ?_, fun hi => ?_⟩
    · obtain ⟨-, e2, e3, e4, e5⟩ := g1 hi
      exact ⟨h5.trans e2, h3.trans e3, h6.trans e4, h7.trans e5⟩
    · obtain ⟨z1, z2, z3, z4, z5⟩ := g2 hi
      refine ⟨h3.trans z1, ?_, h5.trans z3, h6.trans z4, h7.trans z5⟩
      rw [info_idxO]
      exact z2
  · rw [(hR k).1]; exact hF.inc k
  · rw [(hR k).2.1] at hk; exact hF.conv k hk
  · rw [(hR k).2.2.2.2.2.2] at hk; exact hF.mi k hk

end Fold

end Chain

end Gen6

section Gen7
open Nock.V1J8.Gen
open Nock.Atoms (B val limbs Canonical Carry)

/-! ## 7. The generator's atom table is a valid `AtomTab` -/

section Bridge

/-- The limb list of a comb (`combOf`'s inverse on lists of length `≥ 2`). -/
def unComb : Noun → List ℕ
  | .cell (.atom x) (.atom y) => [x, y]
  | .cell (.atom x) r => x :: unComb r
  | _ => []

theorem unComb_combOf : ∀ l : List ℕ, 2 ≤ l.length → unComb (combOf l) = l
  | [x, y], _ => rfl
  | x :: y :: z :: r, _ => by
    have ih := unComb_combOf (y :: z :: r) (by simp)
    rw [combOf_cons x (y :: z :: r) (by simp)]
    have hc : ∃ a b, combOf (y :: z :: r) = .cell a b := by
      cases r with
      | nil => exact ⟨_, _, rfl⟩
      | cons w r => exact ⟨_, _, combOf_cons y (z :: w :: r) (by simp)⟩
    obtain ⟨a, b, hab⟩ := hc
    rw [hab] at ih ⊢
    simp only [unComb, ih]

theorem combOf_inj {l l' : List ℕ} (h : 2 ≤ l.length) (h' : 2 ≤ l'.length) (e : combOf l = combOf l') : l = l' := by
  rw [← unComb_combOf l h, ← unComb_combOf l' h', e]

theorem combOf_isCell (l : List ℕ) (h : 2 ≤ l.length) : (combOf l).isCell = true := by
  match l, h with
  | [x, y], _ => rfl
  | x :: y :: z :: r, _ => rw [combOf_cons x (y :: z :: r) (by simp)]; rfl

theorem mem_spineOf : ∀ (l : List ℕ) (x : Noun), x ∈ spineOf l ↔ ∃ d, 2 ≤ (l.drop d).length ∧ x = combOf (l.drop d)
  | [], x => by simp [spineOf]
  | [a], x => by
    simp only [spineOf, List.not_mem_nil, false_iff, not_exists, not_and]
    intro d hd; cases d <;> simp at hd
  | a :: b :: r, x => by
    rw [spineOf_cons2 _ (by simp), List.mem_cons, List.tail_cons, mem_spineOf (b :: r) x]
    constructor
    · rintro (rfl | ⟨d, hd, rfl⟩)
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨d + 1, by simpa using hd, by simp⟩
    · rintro ⟨d, hd, rfl⟩
      rcases d with _ | d
      · exact Or.inl rfl
      · exact Or.inr ⟨d, by simpa using hd, by simp⟩

theorem mem_addNew : ∀ (ns acc : List Noun) (x : Noun), x ∈ addNew acc ns ↔ x ∈ acc ∨ x ∈ ns
  | [], acc, x => by simp [addNew]
  | n :: ns, acc, x => by
    have := mem_addNew ns (if n ∈ acc then acc else acc ++ [n]) x
    simp only [addNew, List.foldl_cons] at this ⊢
    rw [this]
    split_ifs with h
    · simp only [List.mem_cons]; constructor
      · rintro (h1 | h1); exact Or.inl h1; exact Or.inr (Or.inr h1)
      · rintro (h1 | rfl | h1); exact Or.inl h1; exact Or.inl h; exact Or.inr h1
    · simp [List.mem_append, or_assoc]

/-- The spine list `L` of the big atoms. -/
def spineL (bigs : List ℕ) : List Noun := bigs.foldl (fun acc a => addNew acc (spineOf (limbs a))) []

theorem mem_spineL (bigs : List ℕ) (x : Noun) : x ∈ spineL bigs ↔ ∃ a ∈ bigs, x ∈ spineOf (limbs a) := by
  have key : ∀ (l : List ℕ) (acc : List Noun), x ∈ l.foldl (fun acc a => addNew acc (spineOf (limbs a))) acc ↔
      x ∈ acc ∨ ∃ a ∈ l, x ∈ spineOf (limbs a) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons a l ih =>
      intro acc
      simp only [List.foldl_cons, ih, mem_addNew, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨b, hb, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨a, Or.inl rfl, h⟩
        · exact Or.inr ⟨b, Or.inr hb, h⟩
      · rintro (h | ⟨b, rfl | hb, h⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨b, hb, h⟩
  simpa [spineL] using key bigs []

theorem spineL_cells (bigs : List ℕ) : ∀ x ∈ spineL bigs, x.isCell = true := by
  intro x hx
  obtain ⟨a, -, hx⟩ := (mem_spineL bigs x).mp hx
  obtain ⟨d, hd, rfl⟩ := (mem_spineOf _ x).mp hx
  exact combOf_isCell _ hd

end Bridge

section Bridge2

/-! ### Serial lookups -/

theorem getElem?_idxD : ∀ (cs : List Noun) (x : Noun), x ∈ cs → cs[idxD cs x]? = some x
  | [], x, h => by simp at h
  | c :: cs, x, h => by
    simp only [idxD]
    split_ifs with hc
    · simp [hc]
    · have hx : x ∈ cs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hc
        · exact h
      simpa using getElem?_idxD cs x hx

theorem idxD_lt (cs : List Noun) (x : Noun) (h : x ∈ cs) : idxD cs x < cs.length := by
  have := getElem?_idxD cs x h
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at this; cases this

theorem idxD_append_left : ∀ (a b : List Noun) (x : Noun), x ∈ a → idxD (a ++ b) x = idxD a x
  | [], b, x, h => by simp at h
  | c :: a, b, x, h => by
    simp only [List.cons_append, idxD]
    split_ifs with hc
    · rfl
    · have hx : x ∈ a := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hc
        · exact h
      rw [idxD_append_left a b x hx]

theorem idxD_of_nodup : ∀ (cs : List Noun) (j : ℕ) (x : Noun), cs.Nodup → cs[j]? = some x → idxD cs x = j
  | [], j, x, _, h => by simp at h
  | c :: cs, 0, x, _, h => by simp at h; simp [idxD, h]
  | c :: cs, j + 1, x, hn, h => by
    simp at h
    have hcx : c ≠ x := by
      intro e; subst e
      exact (List.nodup_cons.mp hn).1 (List.mem_of_getElem? h)
    simp only [idxD, hcx, if_false]
    rw [idxD_of_nodup cs j x (List.nodup_cons.mp hn).2 h]

theorem idxOf_eq (cs : List Noun) (x : Noun) (h : x ∈ cs) : idxOf cs x = idxD cs x := by
  simp [idxOf, h]

theorem lastIdxOf_mem (l : List Noun) (n : Noun) (h : n ∈ l) : l[lastIdxOf l n]? = some n := by
  unfold lastIdxOf
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  have hm : (l[i], i) ∈ (l.zipIdx 0).reverse := by
    rw [List.mem_reverse, List.mem_zipIdx_iff_getElem?]
    simp [hi]
  cases hf : ((l.zipIdx 0).reverse.find? fun x => x.1 == l[i]) with
  | none =>
    rw [List.find?_eq_none] at hf
    have := hf _ hm
    simp at this
  | some y =>
    have hy := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [beq_iff_eq] at hp
    rw [List.mem_reverse] at hy
    obtain ⟨h1, h2⟩ := List.mem_zipIdx' (x := y.1) (i := y.2) hy
    simp only [Option.map_some, Option.getD_some]
    rw [List.getElem?_eq_getElem h1, ← h2, hp]

theorem lastIdxOf_append (a b : List Noun) (n : Noun) (hb : n ∉ b) :
    lastIdxOf (a ++ n :: b) n = a.length := by
  unfold lastIdxOf
  rw [List.zipIdx_append, List.reverse_append, List.zipIdx_cons, List.reverse_cons, List.find?_append,
    List.find?_append]
  have h1 : ((b.zipIdx (0 + a.length + 1)).reverse.find? fun x => x.1 == n) = none := by
    rw [List.find?_eq_none]
    intro x hx
    rw [List.mem_reverse] at hx
    have := (List.mem_zipIdx (x := x.1) (i := x.2) hx).2.2
    simp only [beq_iff_eq]
    intro e; apply hb; rw [← e, this]; exact List.getElem_mem _
  rw [h1]
  simp

end Bridge2

section Bridge3
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (acsP combPP rootIdxP incOpsP infoOfP)
open Nock.Edit Nock.Edit.GenX

/-! ### Limb facts -/

theorem canonical_drop : ∀ (l : List ℕ) (d : ℕ), Canonical l → l.drop d ≠ [] → Canonical (l.drop d)
  | l, 0, h, _ => by simpa using h
  | [], d + 1, _, hne => by simp at hne
  | a :: l, d + 1, h, hne => by
    simp only [List.drop_succ_cons] at hne ⊢
    have hl : l ≠ [] := by intro e; subst e; simp at hne
    exact canonical_drop l d (canonical_tail h hl) hne

theorem length_spineOf : ∀ l : List ℕ, (spineOf l).length = l.length - 1
  | [] => rfl
  | [_] => rfl
  | a :: b :: r => by rw [spineOf_cons2 _ (by simp), List.length_cons, List.tail_cons, length_spineOf (b :: r)]; simp

theorem limbs_big_len {a : ℕ} (h : Nock.Atoms.p ≤ a) : 2 ≤ (limbs a).length := Nock.Atoms.two_le_length_of_big h

theorem combPP_eq : combPP Nock.Atoms.p = combOf [1, B - 1] := by
  simp only [combPP, Nock.Atoms.limbs_p]

theorem padN_eq : padN = combOf [0, 1] := rfl

theorem canonical_one_top : Canonical [1, B - 1] := Nock.Atoms.canonical_one_top

theorem canonical_pad : Canonical [0, 1] := by
  refine ⟨fun x hx => ?_, fun _ => by simp⟩
  simp at hx; rcases hx with rfl | rfl <;> simp [Nock.Atoms.B]

/-- The carry into a reached depth is `1`. -/
theorem carry_reach {v : ℕ} (hv : 1 ≤ v + 1) :
    ∀ d, (∀ i < d, Cnd ((limbs v).drop i)) → 2 ≤ ((limbs v).drop d).length →
      Carry 1 ((limbs v).drop d) ((limbs (v + 1)).drop d)
  | 0, _, _ => by
    have hc := carry_pred (Nock.Atoms.limbs_canonical (v + 1)) (by
      intro e
      have := Nock.Atoms.val_limbs (v + 1)
      rw [e] at this; simp at this)
    rw [Nock.Atoms.val_limbs, Nat.add_sub_cancel] at hc
    simpa using hc
  | d + 1, hc, hl => by
    have ih := carry_reach hv d (fun i hi => hc i (by omega)) (by
      simp only [List.length_drop] at hl ⊢; omega)
    obtain ⟨hb, h3⟩ := hc d (by omega)
    rw [← List.tail_drop, ← List.tail_drop]
    generalize (limbs v).drop d = lo at ih hb h3
    generalize (limbs (v + 1)).drop d = ln at ih
    cases ih with
    | nil1 => simp at h3
    | @cons cin c a a' l l' hcin hco ha' he hr =>
      simp only [List.headD_cons] at hb
      have : c = 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hco with h0 | h1
        · subst h0 hb; have := Nock.Atoms.B_eq; simp at he; omega
        · exact h1
      subst this; simpa using hr

/-- At a reached depth the old suffix is the canonical predecessor of the new one. -/
theorem lo_reach {v f d : ℕ} (hr : Reach f (limbs (v + 1)) (limbs v) d) :
    limbs (val ((limbs (v + 1)).drop d) - 1) = (limbs v).drop d := by
  obtain ⟨-, -, h3, h4⟩ := hr
  have hc := carry_reach (v := v) (by omega) d h4 h3
  have hcan := canonical_drop (limbs v) d (Nock.Atoms.limbs_canonical v) (by intro e; rw [e] at h3; simp at h3)
  rw [Nock.Atoms.carry_val hc, Nat.add_sub_cancel, Nock.Atoms.limbs_val hcan]

end Bridge3

section Bridge4
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (acsP combPP rootIdxP incOpsP infoOfP)
open Nock.Edit Nock.Edit.GenX

/-- **The generator's atom table as an `AtomTab`**: rows `acs`, the inc / conversion data `info`, `mb`. -/
noncomputable def tabOf (acs : List Noun) (info : Array AInfo) (mb : Array ℕ) (rows : Array RowNX) : AtomTab where
  n := acs.length
  sp j := unComb (acs.getD j padN)
  ix s := idxOf acs (combOf s)
  inc j := (info.getD j AInfo.z).inc
  conv j := (info.getD j AInfo.z).conv
  mb j := mb.getD j 0
  mi j := (info.getD j AInfo.z).mi
  io j := (info.getD j AInfo.z).idxO
  ip l := ComplJ8Data.ptrP Nock.Atoms.p acs rows (combOf l)

theorem getD_of_getElem? {l : List Noun} {j : ℕ} {y : Noun} (h : l[j]? = some y) : l.getD j padN = y := by
  simp [List.getD_eq_getElem?_getD, h]

theorem limbs_Bm1 : limbs (B - 1) = [B - 1] := by
  have hc : Canonical [B - 1] := ⟨fun x hx => by simp at hx; subst hx; simp [Nock.Atoms.B], fun _ => by
    simp [Nock.Atoms.B]⟩
  have := Nock.Atoms.limbs_val hc
  simpa using this

theorem val_one_top : val [1, B - 1] = Nock.Atoms.p := by
  have := Nock.Atoms.val_limbs Nock.Atoms.p
  rwa [Nock.Atoms.limbs_p] at this

variable (bigs : List ℕ) (dupP : Bool) {rows : Array RowNX}

theorem acsP_eq : acsP Nock.Atoms.p bigs dupP = linkOrder (spineL bigs) ++
    ((if dupP && decide (Noun.cell (.atom 0) (combPP Nock.Atoms.p) ∈ spineL bigs) then [combPP Nock.Atoms.p]
      else []) ++ [padN]) := by
  unfold acsP spineL; rw [List.append_assoc]

theorem mem_acsP (y : Noun) : y ∈ acsP Nock.Atoms.p bigs dupP ↔ y ∈ spineL bigs ∨
    (y = combPP Nock.Atoms.p ∧ (dupP && decide (Noun.cell (.atom 0) (combPP Nock.Atoms.p) ∈ spineL bigs)) = true) ∨
    y = padN := by
  rw [acsP_eq, List.mem_append, (linkOrder_spec (spineL bigs) (spineL_cells bigs)).2.1, List.mem_append]
  split_ifs with h <;> simp [h]

theorem shape_acsP (hbigs : ∀ a ∈ bigs, Nock.Atoms.p ≤ a) (y : Noun) (hy : y ∈ acsP Nock.Atoms.p bigs dupP) :
    ∃ l, 2 ≤ l.length ∧ Canonical l ∧ y = combOf l ∧
      (3 ≤ l.length → y ∈ spineL bigs ∧ ∃ a ∈ bigs, ∃ d, l = (limbs a).drop d) := by
  rcases (mem_acsP bigs dupP y).mp hy with h | ⟨rfl, -⟩ | rfl
  · obtain ⟨a, ha, hs⟩ := (mem_spineL bigs y).mp h
    obtain ⟨d, hd, rfl⟩ := (mem_spineOf _ y).mp hs
    exact ⟨_, hd, canonical_drop _ d (Nock.Atoms.limbs_canonical a) (by intro e; rw [e] at hd; simp at hd), rfl,
      fun _ => ⟨h, a, ha, d, rfl⟩⟩
  · exact ⟨[1, B - 1], by simp, canonical_one_top, combPP_eq, fun h => by simp at h⟩
  · exact ⟨[0, 1], by simp, canonical_pad, padN_eq, fun h => by simp at h⟩

theorem sp_idx (info : Array AInfo) (mb : Array ℕ) (l : List ℕ) (hl : 2 ≤ l.length)
    (hm : combOf l ∈ acsP Nock.Atoms.p bigs dupP) :
    (tabOf (acsP Nock.Atoms.p bigs dupP) info mb rows).sp (idxOf (acsP Nock.Atoms.p bigs dupP) (combOf l)) = l ∧
      idxOf (acsP Nock.Atoms.p bigs dupP) (combOf l) < (acsP Nock.Atoms.p bigs dupP).length := by
  rw [idxOf_eq _ _ hm]
  refine ⟨?_, idxD_lt _ _ hm⟩
  simp only [tabOf]
  rw [getD_of_getElem? (getElem?_idxD _ _ hm), unComb_combOf l hl]

theorem sp_at (info : Array AInfo) (mb : Array ℕ) {j : ℕ} {l : List ℕ} (hl : 2 ≤ l.length)
    (h : (acsP Nock.Atoms.p bigs dupP)[j]? = some (combOf l)) :
    (tabOf (acsP Nock.Atoms.p bigs dupP) info mb rows).sp j = l := by
  simp only [tabOf]; rw [getD_of_getElem? h, unComb_combOf l hl]

open Classical in
/-- **The variant-4 tail pointer of a comb of length `≥ 3`**: the row key of the tail when the head is out of the
FIRST component, the first copy of the tail when it is in it (in particular at head `0`: link order). -/
theorem ptrP_combOf (acs : List Noun) (rows : Array RowNX) (l : List ℕ) (h3 : 3 ≤ l.length) :
    ComplJ8Data.ptrP Nock.Atoms.p acs rows (combOf l) =
      if ¬ ComplJ8Data.FirstC Nock.Atoms.p rows (l.headD 0) then ComplJ8Data.keyP Nock.Atoms.p acs (combOf l.tail)
      else idxOf acs (combOf l.tail) := by
  match l, h3 with
  | x :: y :: z :: r, _ =>
    rw [combOf_cons x (y :: z :: r) (by simp)]
    unfold ComplJ8Data.ptrP ComplJ8Data.keyP
    by_cases hx : ComplJ8Data.FirstC Nock.Atoms.p rows x <;>
      by_cases hc : combOf (y :: z :: r) = combPP Nock.Atoms.p <;> simp [tlN', hdN', atomV, hx, hc]

/-- **The row key of a spine comb is a row carrying it** (its first copy, or the last copy of `comb p`). -/
theorem sp_key (info : Array AInfo) (mb : Array ℕ) (l : List ℕ) (hl : 2 ≤ l.length)
    (hm : combOf l ∈ acsP Nock.Atoms.p bigs dupP) :
    (tabOf (acsP Nock.Atoms.p bigs dupP) info mb rows).sp (ComplJ8Data.keyP Nock.Atoms.p (acsP Nock.Atoms.p bigs dupP)
      (combOf l)) = l ∧
      ComplJ8Data.keyP Nock.Atoms.p (acsP Nock.Atoms.p bigs dupP) (combOf l) < (acsP Nock.Atoms.p bigs dupP).length := by
  unfold ComplJ8Data.keyP
  split_ifs with hc
  · have h0 := lastIdxOf_mem _ _ (hc ▸ hm)
    have h1 : (acsP Nock.Atoms.p bigs dupP)[lastIdxOf (acsP Nock.Atoms.p bigs dupP) (combPP Nock.Atoms.p)]? =
        some (combOf l) := by rw [h0, hc]
    refine ⟨sp_at (rows := rows) bigs dupP info mb hl h1, ?_⟩
    by_contra hge; rw [List.getElem?_eq_none (by omega)] at h1; cases h1
  · exact sp_idx (rows := rows) bigs dupP info mb l hl hm

theorem combPP_mem (hp : Nock.Atoms.p ∈ bigs) : combPP Nock.Atoms.p ∈ spineL bigs := by
  rw [mem_spineL]
  refine ⟨_, hp, (mem_spineOf _ _).mpr ⟨0, by rw [Nock.Atoms.limbs_p]; simp, by simp [combPP]⟩⟩

/-- **Link order of the generator's atom table** (`AtomTab.Valid.link`). -/
theorem link_gen (hbigs : ∀ a ∈ bigs, Nock.Atoms.p ≤ a) (info : Array AInfo) (mb : Array ℕ) (j : ℕ)
    (hj : j < (acsP Nock.Atoms.p bigs dupP).length)
    (h3 : 3 ≤ ((tabOf (acsP Nock.Atoms.p bigs dupP) info mb rows).sp j).length)
    (h0 : ((tabOf (acsP Nock.Atoms.p bigs dupP) info mb rows).sp j).headD 0 = 0) :
    (tabOf (acsP Nock.Atoms.p bigs dupP) info mb rows).ix ((tabOf (acsP Nock.Atoms.p bigs dupP) info mb rows).sp j).tail =
      j + 1 := by
  have hy0 : (acsP Nock.Atoms.p bigs dupP)[j]? = some (acsP Nock.Atoms.p bigs dupP)[j] :=
    List.getElem?_eq_getElem hj
  obtain ⟨l, hl2, hcl, hyl, h3l⟩ := shape_acsP bigs dupP hbigs _ (List.getElem_mem hj)
  rw [hyl] at hy0
  have hsp : (tabOf (acsP Nock.Atoms.p bigs dupP) info mb rows).sp j = l := sp_at (rows := rows) bigs dupP info mb hl2 hy0
  rw [hsp] at h3 h0 ⊢
  obtain ⟨hL, a, ha, d, rfl⟩ := h3l h3
  obtain ⟨hnd, hmem, hnext⟩ := linkOrder_spec (spineL bigs) (spineL_cells bigs)
  have htl : combOf ((limbs a).drop d).tail ∈ spineL bigs := by
    rw [mem_spineL]
    refine ⟨a, ha, (mem_spineOf _ _).mpr ⟨d + 1, ?_, by rw [List.tail_drop]⟩⟩
    simp only [List.length_drop] at h3 ⊢; omega
  have hy := hy0
  rw [acsP_eq] at hy
  -- `j` sits in the link-ordered part
  have hjR : j < (linkOrder (spineL bigs)).length := by
    by_contra hge
    rw [List.getElem?_append_right (by omega)] at hy
    have hE := List.mem_of_getElem? hy
    have h2 : ∀ l' : List ℕ, 2 ≤ l'.length → l'.length = 2 → combOf ((limbs a).drop d) = combOf l' → False :=
      fun l' h1 h2 e => by have := combOf_inj hl2 h1 e; rw [this] at h3; omega
    split_ifs at hE
    · simp only [List.mem_append, List.mem_singleton] at hE
      rcases hE with e | e
      · exact h2 _ (by simp) (by simp) (e.trans combPP_eq)
      · exact h2 _ (by simp) (by simp) (e.trans padN_eq)
    · simp only [List.nil_append, List.mem_singleton] at hE
      exact h2 _ (by simp) (by simp) (hE.trans padN_eq)
  rw [List.getElem?_append_left hjR] at hy
  -- `[0 X]` is followed by `X`
  have hsplit : (limbs a).drop d = 0 :: ((limbs a).drop d).tail := by
    cases h : (limbs a).drop d with
    | nil => rw [h] at h3; simp at h3
    | cons x t => rw [h] at h0; simp at h0; simp [h0]
  have hup : combOf ((limbs a).drop d) = up0 (combOf ((limbs a).drop d).tail) := by
    conv_lhs => rw [hsplit]
    rw [combOf_cons 0 _ (by simp only [List.length_tail]; omega)]; rfl
  have hRj : (linkOrder (spineL bigs))[j]'hjR = up0 (combOf ((limbs a).drop d).tail) := by
    rw [← hup]; exact (List.getElem?_eq_some_iff.mp hy).2
  have hs := hnext j hjR _ (by
    rw [hRj]; exact linkSucc_up0 htl (combOf_isCell _ (by simp only [List.length_tail]; omega)))
  have hmR : combOf ((limbs a).drop d).tail ∈ linkOrder (spineL bigs) := (hmem _).mpr htl
  simp only [tabOf]
  rw [idxOf_eq _ _ (by rw [acsP_eq]; exact List.mem_append_left _ hmR), acsP_eq,
    idxD_append_left _ _ _ hmR, idxD_of_nodup _ _ _ hnd hs]

end Bridge4

section Bridge5
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (acsP combPP rootIdxP incOpsP infoOfP)
open Nock.Edit Nock.Edit.GenX

variable (bigs : List ℕ) (dupP : Bool) (rows : Array RowNX)

/-- A conversion operand marks its root row `conv` (and nothing unsets it). -/
theorem conv_at (acsL : List Noun) (vc : ℕ × ℕ) (hvc : vc ∈ incOpsP Nock.Atoms.p rows)
    (hp : vc.1 + 1 = Nock.Atoms.p) (hr : rootIdxP Nock.Atoms.p acsL Nock.Atoms.p < acsL.length) :
    ((infoOfP Nock.Atoms.p acsL rows).getD (rootIdxP Nock.Atoms.p acsL Nock.Atoms.p) AInfo.z).conv = true := by
  rw [(info_fields _ _ _ _).2.1]
  unfold infoFold
  set r := rootIdxP Nock.Atoms.p acsL Nock.Atoms.p
  have pres : ∀ (a : Array AInfo) (w : ℕ × ℕ), (a.getD r AInfo.z).conv = true →
      ((stepF Nock.Atoms.p acsL rows a w).getD r AInfo.z).conv = true := by
    intro a w h
    unfold stepF
    split_ifs
    · rw [getD_modify]; split_ifs <;> first | rfl | exact h
    · rw [getD_modify]
      have := (incChain_conv_mi (rows := rows) Nock.Atoms.p acsL (fuelOf w.1) (limbs (w.1 + 1)) (limbs w.1) a r).1
      split_ifs <;> exact this.trans h
  have sz : ∀ (a : Array AInfo) (w : ℕ × ℕ), (stepF Nock.Atoms.p acsL rows a w).size = a.size := by
    intro a w; unfold stepF; split_ifs <;> simp [size_incChain]
  have key : ∀ (l : List (ℕ × ℕ)) (a : Array AInfo), a.size = acsL.length →
      (vc ∈ l ∨ (a.getD r AInfo.z).conv = true) → ((l.foldl (stepF Nock.Atoms.p acsL rows) a).getD r AInfo.z).conv = true := by
    intro l
    induction l with
    | nil => intro a _ h; simpa using h
    | cons w l ih =>
      intro a hs h
      simp only [List.foldl_cons]
      refine ih _ (by rw [sz]; exact hs) ?_
      rcases h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · right
          unfold stepF
          rw [if_pos hp, getD_modify, if_pos ⟨rfl, by omega⟩]
        · exact Or.inl h
      · exact Or.inr (pres a w h)
  exact key _ _ (by simp) (Or.inl hvc)

/-- The facts the generator's run supplies (`J8Data`): the big atoms are big, every slow OP4 operand's atoms are
big atoms of the table, a conversion forces the `p` duplicate, and `mb` sits at big roots. -/
structure GenHyp (mb : Array ℕ) : Prop where
  big : ∀ a ∈ bigs, Nock.Atoms.p ≤ a
  ops : ∀ vc ∈ incOpsP Nock.Atoms.p rows, (vc.1 + 1 = Nock.Atoms.p → Nock.Atoms.p ∈ bigs) ∧
    (vc.1 + 1 ≠ Nock.Atoms.p → vc.1 ∈ bigs ∧ vc.1 + 1 ∈ bigs)
  dup : (∃ vc ∈ incOpsP Nock.Atoms.p rows, vc.1 + 1 = Nock.Atoms.p) → dupP = true
  mb : ∀ j < (acsP Nock.Atoms.p bigs dupP).length, mb.getD j 0 ≠ 0 →
    ∃ a ∈ bigs, j = rootIdxP Nock.Atoms.p (acsP Nock.Atoms.p bigs dupP) a
  /-- The rows bound: the no-conflict counting of the variant-4 pointer needs `rows ≤ 2^31`. -/
  rows31 : rows.size ≤ 2 ^ 31

/-- In the corner the depth-1 write wants the FIRST copy of
`comb q` (the atom chip's link `rn.idxO = r.vRO`) while `q`'s own depth-0 row wants the LAST (the compute's inc record
keys `q` by `(2, lastIdxOf (comb q))`); no table passes both. Reachable: `s = [p·B u]`, `u = [B−1, 1, B−1]`,
`f = [[4 [4 [1 p−1]]] [4 [0 3]]]` (`Batch4851.FixB.noIncCorner_neg`). Holds under J-8's binders (two-limb big atoms, no
duplicate; `ComplJ8OfAtom.noIncCorner_of_j8`). -/
def NoIncCornerP (q : ℕ) (acs : List Noun) (ops : List (ℕ × ℕ)) : Prop :=
  (∃ vc ∈ ops, vc.1 = q) →
  (∃ vc ∈ ops, vc.1 + 1 ≠ q ∧ ∃ d, Reach (fuelOf vc.1) (limbs (vc.1 + 1)) (limbs vc.1) (d + 1) ∧
      (limbs (vc.1 + 1)).drop (d + 1) = limbs (q + 1)) →
  lastIdxOf acs (combPP q) = idxOf acs (combPP q)

/-- Without a `comb q` duplicate there is no corner. -/
theorem noIncCorner_of_last {q : ℕ} {acs : List Noun} {ops : List (ℕ × ℕ)}
    (h : lastIdxOf acs (combPP q) = idxOf acs (combPP q)) : NoIncCornerP q acs ops := fun _ _ => h

end Bridge5

section Bridge6
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (acsP combPP rootIdxP incOpsP infoOfP)
open Nock.Edit Nock.Edit.GenX

theorem carry_top {lo ln : List ℕ} (h : Carry 1 lo ln) (hb : lo.headD 0 = B - 1) (h2 : 1 ≤ lo.length) :
    ln.headD 0 = 0 ∧ lo.length ≤ ln.length ∧ Carry 1 lo.tail ln.tail := by
  have hle := carry_length_le h
  cases h with
  | nil1 => simp at h2
  | @cons cin c a a' l l' hcin hco ha' he hr =>
    simp only [List.headD_cons] at hb
    subst hb
    have hc : c = 1 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hco with h0 | h1
      · subst h0; have := Nock.Atoms.B_eq; simp at he; omega
      · exact h1
    subst hc
    refine ⟨?_, hle, by simpa using hr⟩
    have := Nock.Atoms.B_eq; simp only [List.headD_cons]; omega

theorem acs_last (bigs : List ℕ) (dupP : Bool) :
    (acsP Nock.Atoms.p bigs dupP)[(acsP Nock.Atoms.p bigs dupP).length - 1]? = some padN := by
  rw [← List.getLast?_eq_getElem?, acsP_eq]; simp

theorem combPP_ne_padN : combPP Nock.Atoms.p ≠ padN := by
  rw [combPP_eq, padN_eq]; intro e
  have := combOf_inj (by simp) (by simp) e
  simp at this

variable (bigs : List ℕ) (dupP : Bool) (rows : Array RowNX) (mb : Array ℕ)

local notation "ACS" => acsP Nock.Atoms.p bigs dupP
local notation "TT" => tabOf (acsP Nock.Atoms.p bigs dupP) (infoOfP Nock.Atoms.p (acsP Nock.Atoms.p bigs dupP) rows) mb rows

/-- **The generator's atom table is valid** (`AtomTab.Valid`, hence `RowOK` at every row by `rowOK_of_valid`):
L0's `acsP` / `infoOfP` (fixed fuel) / `mb` at Goldilocks, under the run facts `GenHyp`. -/
theorem valid_gen (hg : GenHyp bigs dupP rows mb) : (TT).Valid := by
  have hmemL : ∀ a ∈ bigs, ∀ d, 2 ≤ ((limbs a).drop d).length → combOf ((limbs a).drop d) ∈ ACS :=
    fun a ha d hd => (mem_acsP bigs dupP _).mpr
      (Or.inl ((mem_spineL bigs _).mpr ⟨a, ha, (mem_spineOf _ _).mpr ⟨d, hd, rfl⟩⟩))
  have hl : ∀ vc ∈ incOpsP Nock.Atoms.p rows, vc.1 + 1 ≠ Nock.Atoms.p → ∀ d,
      Reach (fuelOf vc.1) (limbs (vc.1 + 1)) (limbs vc.1) d →
      (TT).lo (idxOf ACS (combOf ((limbs (vc.1 + 1)).drop d))) = (limbs vc.1).drop d := by
    intro vc hvc hp d hr
    have hm := hmemL _ ((hg.ops vc hvc).2 hp).2 d hr.2.1
    unfold AtomTab.lo
    rw [(sp_idx (rows := rows) bigs dupP (infoOfP Nock.Atoms.p ACS rows) mb _ hr.2.1 hm).1]
    exact lo_reach hr
  have hI := stInv_infoOfP Nock.Atoms.p ACS (TT).lo rows hl
  have incD : ∀ j, (TT).inc j = true → j < (ACS).length ∧ ∃ vc ∈ incOpsP Nock.Atoms.p rows,
      vc.1 + 1 ≠ Nock.Atoms.p ∧ ∃ d, Reach (fuelOf vc.1) (limbs (vc.1 + 1)) (limbs vc.1) d ∧
        (TT).sp j = (limbs (vc.1 + 1)).drop d ∧ (TT).lo j = (limbs vc.1).drop d ∧
        j = idxOf ACS (combOf ((limbs (vc.1 + 1)).drop d)) := by
    intro j hj
    obtain ⟨hk, vc, hvc, hp, d, hr, rfl⟩ := (hI.inc j).mp hj
    have hm := hmemL _ ((hg.ops vc hvc).2 hp).2 d hr.2.1
    exact ⟨hk, vc, hvc, hp, d, hr, (sp_idx (rows := rows) bigs dupP (infoOfP Nock.Atoms.p ACS rows) mb _ hr.2.1 hm).1, hl vc hvc hp d hr, rfl⟩
  have spP : ∀ j, j = rootIdxP Nock.Atoms.p ACS Nock.Atoms.p → Nock.Atoms.p ∈ bigs →
      (TT).sp j = [1, B - 1] ∧ j < (ACS).length := by
    intro j hj hpb
    have hcm : combPP Nock.Atoms.p ∈ ACS := (mem_acsP bigs dupP _).mpr (Or.inl (combPP_mem bigs hpb))
    have hr : rootIdxP Nock.Atoms.p ACS Nock.Atoms.p = lastIdxOf ACS (combPP Nock.Atoms.p) := by
      simp [rootIdxP]
    have hg' := lastIdxOf_mem _ _ hcm
    rw [hj, hr]
    refine ⟨sp_at (rows := rows) bigs dupP _ mb (by simp) (by rw [← combPP_eq]; exact hg'), ?_⟩
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hg'; cases hg'
  refine
    { canon := fun j hj => ?_, tail := fun j hj h3 => ?_, link := fun j hj h3 h0 => ?_,
      incOld := fun j hj hinc => ?_, chain := fun j hj hinc hb h3 => ?_,
      ioLink := fun j hj hinc hb h3 => ?_, stop := fun j hj hinc a st hl0 ha h2 => ?_, conv := fun j hj hcv => ?_,
      mbBig := fun j hj hm => ?_, miBig := fun j hj hm => ?_, last := ?_ }
  · obtain ⟨l, h2, hc, hy, -⟩ := shape_acsP bigs dupP hg.big _ (List.getElem_mem hj)
    rw [sp_at (rows := rows) bigs dupP _ mb h2 (by rw [List.getElem?_eq_getElem hj, hy])]
    exact ⟨h2, hc⟩
  · obtain ⟨l, h2, hc, hy, h3l⟩ := shape_acsP bigs dupP hg.big _ (List.getElem_mem hj)
    have hsp := sp_at (rows := rows) bigs dupP (infoOfP Nock.Atoms.p ACS rows) mb h2 (by rw [List.getElem?_eq_getElem hj, hy])
    rw [hsp] at h3 ⊢
    obtain ⟨-, a, ha, d, rfl⟩ := h3l h3
    have h2' : 2 ≤ ((limbs a).drop (d + 1)).length := by simp only [List.length_drop] at h3 ⊢; omega
    have hm := hmemL a ha (d + 1) h2'
    have hip : (TT).ip ((limbs a).drop d) = ComplJ8Data.ptrP Nock.Atoms.p ACS rows (combOf ((limbs a).drop d)) := rfl
    rw [hip, ptrP_combOf _ _ _ h3, List.tail_drop]
    split_ifs <;> first
      | exact ⟨(sp_key (rows := rows) bigs dupP (infoOfP Nock.Atoms.p ACS rows) mb _ h2' hm).2,
          (sp_key (rows := rows) bigs dupP (infoOfP Nock.Atoms.p ACS rows) mb _ h2' hm).1⟩
      | exact ⟨(sp_idx (rows := rows) bigs dupP (infoOfP Nock.Atoms.p ACS rows) mb _ h2' hm).2,
          (sp_idx (rows := rows) bigs dupP (infoOfP Nock.Atoms.p ACS rows) mb _ h2' hm).1⟩
  · have hl0 := link_gen bigs dupP hg.big (infoOfP Nock.Atoms.p ACS rows) mb j hj h3 h0
    have hip : (TT).ip ((TT).sp j) = ComplJ8Data.ptrP Nock.Atoms.p ACS rows (combOf ((TT).sp j)) := rfl
    rw [hip, ptrP_combOf _ _ _ h3, if_neg (by rw [h0]; exact not_not.mpr (ComplJ8Data.firstC_zero _ _))]
    exact hl0
  · obtain ⟨-, vc, -, -, d, hr, -, hlo, -⟩ := incD j hinc
    rw [hlo]; exact hr.2.2.1
  · obtain ⟨hk, vc, hvc, hp, d, hr, hsp, hlo, hjeq⟩ := incD j hinc
    rw [hlo] at hb h3
    have hcar := carry_reach (v := vc.1) (by omega) d hr.2.2.2 hr.2.2.1
    obtain ⟨h0, hle, -⟩ := carry_top hcar hb (by omega)
    have h3n : 3 ≤ ((TT).sp j).length := by rw [hsp]; omega
    have hix := link_gen bigs dupP hg.big (infoOfP Nock.Atoms.p ACS rows) mb j hj h3n (by rw [hsp]; exact h0)
    rw [hsp, List.tail_drop] at hix
    simp only [tabOf] at hix
    have h2' : 2 ≤ ((limbs (vc.1 + 1)).drop (d + 1)).length := by simp only [List.length_drop] at hle h3 ⊢; omega
    have hreach : Reach (fuelOf vc.1) (limbs (vc.1 + 1)) (limbs vc.1) (d + 1) := by
      refine ⟨?_, h2', by simp only [List.length_drop] at h3 ⊢; omega, fun i hi => ?_⟩
      · unfold fuelOf; rw [length_spineOf]; simp only [List.length_drop] at h3; omega
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hr.2.2.2 i hi
        · exact ⟨hb, h3⟩
    have hm := hmemL _ ((hg.ops vc hvc).2 hp).2 (d + 1) h2'
    refine (hI.inc (j + 1)).mpr ⟨?_, vc, hvc, hp, d + 1, hreach, hix.symm⟩
    rw [← hix]; exact (sp_idx (rows := rows) bigs dupP (infoOfP Nock.Atoms.p ACS rows) mb _ h2' hm).2
  · -- G12 variant 3: the next row's old index is the row key of the old tail, which is the old row's pointer
    obtain ⟨hk, vc, hvc, hp, d, hr, hsp, hlo, hjeq⟩ := incD j hinc
    rw [hlo] at hb h3
    have hcar := carry_reach (v := vc.1) (by omega) d hr.2.2.2 hr.2.2.1
    obtain ⟨h0, hle, -⟩ := carry_top hcar hb (by omega)
    have h3n : 3 ≤ ((TT).sp j).length := by rw [hsp]; omega
    have hix := link_gen bigs dupP hg.big (infoOfP Nock.Atoms.p ACS rows) mb j hj h3n (by rw [hsp]; exact h0)
    rw [hsp, List.tail_drop] at hix
    simp only [tabOf] at hix
    have h2' : 2 ≤ ((limbs (vc.1 + 1)).drop (d + 1)).length := by simp only [List.length_drop] at hle h3 ⊢; omega
    have hreach : Reach (fuelOf vc.1) (limbs (vc.1 + 1)) (limbs vc.1) (d + 1) := by
      refine ⟨?_, h2', by simp only [List.length_drop] at h3 ⊢; omega, fun i hi => ?_⟩
      · unfold fuelOf; rw [length_spineOf]; simp only [List.length_drop] at h3; omega
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hr.2.2.2 i hi
        · exact ⟨hb, h3⟩
    have hm := hmemL _ ((hg.ops vc hvc).2 hp).2 (d + 1) h2'
    have hF := stInv_infoFold Nock.Atoms.p ACS (TT).lo rows hl
    have hfi : ((infoFold Nock.Atoms.p ACS rows).getD (j + 1) AInfo.z).inc = true := by
      rw [← (info_fields _ _ _ _).1]
      refine (hI.inc (j + 1)).mpr ⟨?_, vc, hvc, hp, d + 1, hreach, hix.symm⟩
      rw [← hix]; exact (sp_idx (rows := rows) bigs dupP (infoOfP Nock.Atoms.p ACS rows) mb _ h2' hm).2
    have hfo : ((infoFold Nock.Atoms.p ACS rows).getD (j + 1) AInfo.z).idxO =
        ComplJ8Data.keyP Nock.Atoms.p ACS (combOf ((limbs vc.1).drop (d + 1))) := by
      rw [((hF.ok (j + 1)).1 hfi).1, ← hix, hl vc hvc hp (d + 1) hreach]
    have hip : (TT).ip ((TT).lo j) = ComplJ8Data.ptrP Nock.Atoms.p ACS rows (combOf ((TT).lo j)) := rfl
    -- G12 variant 4: the carry-forced old row `[B-1 comb p]` is out of the FIRST component (no conflict, `h31`)
    have hB0 : ¬ ComplJ8Data.FirstC Nock.Atoms.p rows (((limbs vc.1).drop d).headD 0) := by
      rw [hb]; exact ComplJ8Data.not_firstC_top _ rows hg.rows31
    show ((infoOfP Nock.Atoms.p ACS rows).getD (j + 1) AInfo.z).idxO = (TT).ip ((TT).lo j)
    rw [hip, hlo, ptrP_combOf _ _ _ h3, if_pos hB0, List.tail_drop, info_idxO, hfo]
  · -- G12 variant 4: a stop step keeps the component of `comb p`
    obtain ⟨-, vc, hvc, hp, d, hr, -, hlo, -⟩ := incD j hinc
    classical
    have e1 : (TT).ip ((a + 1) :: st) = if ¬ ComplJ8Data.FirstC Nock.Atoms.p rows (a + 1) then
        ComplJ8Data.keyP Nock.Atoms.p ACS (combOf st) else idxOf ACS (combOf st) :=
      ptrP_combOf _ _ _ (by simp; omega)
    have e2 : (TT).ip (a :: st) = if ¬ ComplJ8Data.FirstC Nock.Atoms.p rows a then
        ComplJ8Data.keyP Nock.Atoms.p ACS (combOf st) else idxOf ACS (combOf st) :=
      ptrP_combOf _ _ _ (by simp; omega)
    rw [e1, e2]
    by_cases hst : st = limbs Nock.Atoms.p
    · have hS : ComplJ8Data.StopE Nock.Atoms.p rows a :=
        ⟨vc, hvc, hp, d, by rw [← hlo, hl0, hst], ha, fun i hi => (hr.2.2.2 i hi).1⟩
      have e := ComplJ8Data.firstC_succ_iff _ hS
      by_cases h : ComplJ8Data.FirstC Nock.Atoms.p rows a
      · have h' := e.mpr h; simp [h, h']
      · have h' : ¬ ComplJ8Data.FirstC Nock.Atoms.p rows (a + 1) := fun h' => h (e.mp h'); simp [h, h']
    · have hk : ComplJ8Data.keyP Nock.Atoms.p ACS (combOf st) = idxOf ACS (combOf st) := by
        unfold ComplJ8Data.keyP
        rw [if_neg]
        intro e
        exact hst (combOf_inj h2 (by rw [Nock.Atoms.limbs_p]; simp) e)
      rw [hk]; simp only [ite_self]
  · obtain ⟨vc, hvc, hp, hjr⟩ := hI.conv j hcv
    have hpb := (hg.ops vc hvc).1 hp
    obtain ⟨hsp, -⟩ := spP j hjr hpb
    refine ⟨hsp, ?_⟩
    cases hinc : (TT).inc j
    · rfl
    · exfalso
      obtain ⟨hk, vc', hvc', hp', d, hr', hsp', hlo', hjeq⟩ := incD j hinc
      rw [hsp] at hsp'
      rcases d with _ | d
      · apply hp'
        have := congrArg val hsp'
        simp only [List.drop_zero, Nock.Atoms.val_limbs] at this
        rw [← this, val_one_top]
      · obtain ⟨-, -, -, h4⟩ := hr'
        have hcd := h4 d (by omega)
        have hcar := carry_reach (v := vc'.1) (by omega) d (fun i hi => h4 i (by omega)) (by
          have := hcd.2; omega)
        obtain ⟨h0, -, -⟩ := carry_top hcar hcd.1 (by have := hcd.2; omega)
        have hnd : (limbs (vc'.1 + 1)).drop d = 0 :: [1, B - 1] := by
          have ht : ((limbs (vc'.1 + 1)).drop d).tail = [1, B - 1] := by rw [List.tail_drop]; exact hsp'.symm
          cases h : (limbs (vc'.1 + 1)).drop d with
          | nil => rw [h] at ht; simp at ht
          | cons x t => rw [h] at h0 ht; simp at h0 ht; rw [h0, ht]
        have hz : Noun.cell (.atom 0) (combPP Nock.Atoms.p) ∈ spineL bigs := by
          rw [mem_spineL]
          refine ⟨_, ((hg.ops vc' hvc').2 hp').2, (mem_spineOf _ _).mpr ⟨d, by rw [hnd]; simp, ?_⟩⟩
          rw [hnd, combOf_cons 0 _ (by simp), combPP_eq]
        have hd : dupP = true := hg.dup ⟨vc, hvc, hp⟩
        have hpL : combPP Nock.Atoms.p ∈ spineL bigs := by
          rw [mem_spineL]
          refine ⟨_, ((hg.ops vc' hvc').2 hp').2, (mem_spineOf _ _).mpr ⟨d + 1, ?_, ?_⟩⟩
          · rw [← List.tail_drop, hnd]; simp
          · rw [← List.tail_drop, hnd, combPP_eq]; rfl
        have hacs : ACS = linkOrder (spineL bigs) ++ (combPP Nock.Atoms.p :: [padN]) := by
          rw [acsP_eq]; simp [hd, hz]
        obtain ⟨hnd', hmem, -⟩ := linkOrder_spec (spineL bigs) (spineL_cells bigs)
        have hlast : lastIdxOf ACS (combPP Nock.Atoms.p) = (linkOrder (spineL bigs)).length := by
          rw [hacs]; exact lastIdxOf_append _ _ _ (by simp [combPP_ne_padN])
        have hr : rootIdxP Nock.Atoms.p ACS Nock.Atoms.p = lastIdxOf ACS (combPP Nock.Atoms.p) := by
          simp [rootIdxP]
        have hpR : combPP Nock.Atoms.p ∈ linkOrder (spineL bigs) := (hmem _).mpr hpL
        have hfirst : idxOf ACS (combPP Nock.Atoms.p) < (linkOrder (spineL bigs)).length := by
          rw [idxOf_eq _ _ (by rw [hacs]; exact List.mem_append_left _ hpR), hacs, idxD_append_left _ _ _ hpR]
          exact idxD_lt _ _ hpR
        have e1 : j = (linkOrder (spineL bigs)).length := by rw [hjr, hr, hlast]
        have e2 : j = idxOf ACS (combPP Nock.Atoms.p) := by
          rw [hjeq, ← List.tail_drop, hnd, combPP_eq]; rfl
        omega
  · obtain ⟨a, ha, rfl⟩ := hg.mb j hj hm
    by_cases hap : a = Nock.Atoms.p
    · subst hap
      rw [(spP _ rfl ha).1, val_one_top]
    · have hm2 := hmemL a ha 0 (by simpa using limbs_big_len (hg.big a ha))
      simp only [List.drop_zero] at hm2
      have : rootIdxP Nock.Atoms.p ACS a = idxOf ACS (combOf (limbs a)) := by simp [rootIdxP, hap]
      rw [this, (sp_idx (rows := rows) bigs dupP (infoOfP Nock.Atoms.p ACS rows) mb _ (limbs_big_len (hg.big a ha)) hm2).1, Nock.Atoms.val_limbs]
      exact hg.big a ha
  · obtain ⟨vc, hvc, hjr⟩ := hI.mi j hm
    by_cases hp : vc.1 + 1 = Nock.Atoms.p
    · rw [hp] at hjr
      obtain ⟨hsp, hlt⟩ := spP j hjr ((hg.ops vc hvc).1 hp)
      refine ⟨by rw [hsp, val_one_top], Or.inr ?_⟩
      have := conv_at rows ACS vc hvc hp (hjr ▸ hlt)
      rw [hjr]; exact this
    · obtain ⟨hv, hv1⟩ := (hg.ops vc hvc).2 hp
      have hl1 := limbs_big_len (hg.big _ hv1)
      have hm2 := hmemL _ hv1 0 (by simpa using hl1)
      simp only [List.drop_zero] at hm2
      have hroot : rootIdxP Nock.Atoms.p ACS (vc.1 + 1) = idxOf ACS (combOf (limbs (vc.1 + 1))) := by
        simp [rootIdxP, hp]
      rw [hroot] at hjr
      obtain ⟨hsp, hlt⟩ := sp_idx (rows := rows) bigs dupP (infoOfP Nock.Atoms.p ACS rows) mb _ hl1 hm2
      refine ⟨by rw [hjr, hsp, Nock.Atoms.val_limbs]; exact hg.big _ hv1, Or.inl ?_⟩
      refine (hI.inc j).mpr ⟨hjr ▸ hlt, vc, hvc, hp, 0, ⟨by unfold fuelOf; omega, by simpa using hl1,
        by simpa using limbs_big_len (hg.big _ hv), fun i hi => by omega⟩, by simpa using hjr⟩
  · cases hinc : (TT).inc ((TT).n - 1)
    · rfl
    · exfalso
      obtain ⟨hk, vc, hvc, hp, d, hr, hsp, hlo, -⟩ := incD _ hinc
      have hpad := sp_at (rows := rows) bigs dupP (infoOfP Nock.Atoms.p ACS rows) mb (l := [0, 1]) (by simp)
        (by rw [← padN_eq]; exact acs_last bigs dupP)
      have hn : (TT).n - 1 = (ACS).length - 1 := rfl
      rw [hn] at hsp hlo
      rw [hpad] at hsp
      have : (TT).lo ((ACS).length - 1) = [B - 1] := by
        unfold AtomTab.lo; rw [show (TT).sp ((ACS).length - 1) = [0, 1] from hpad]
        have : val [0, 1] - 1 = B - 1 := by simp
        rw [this, limbs_Bm1]
      rw [this] at hlo
      have := hr.2.2.1
      rw [← hlo] at this; simp at this

end Bridge6


end Gen7

section Gen8
open Nock.V1J8.Gen
open Nock.Atoms (B val limbs)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.Edit Nock.Edit.GenX Nock.Walk

/-! ## 8. The run facts of a generated run (`GenHyp` from `j8DataOf`) -/

section Run

/-- **An OP4 row of a generated run** increments its operand: `sf1 = v`, `e = v + 1` (`RowOKX .s4`, under the
two run binders). -/
theorem s4_row {R : Nock.Jet.Registry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
    (hgen : genX R fuel s f = some (t, r)) {q : ℕ} (hax : ComplJ8.ProgAxOK q t) (hop5 : ComplJ8.ProgOp5OK q t)
    {x : RowNX} (hx : x ∈ (rowsOfT t).toList) (hst : x.st = .s4) :
    ∃ n, x.sf1 = .atom n ∧ x.e = .atom (n + 1) := by
  simp only [rowsOfT, List.toList_toArray, List.mem_map] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  have hin : InTree t u := by
    obtain ⟨c, hc, h⟩ := (mem_bfsForest [t] u).mp hu
    simp at hc; subst hc; exact h
  have hok := HonestRowX.rowOKX_of_genX hgen hin (ComplJ8.smallX_of_binders hax hop5 u hin)
  simp only [HonestCompX.RowOKX, hst] at hok
  exact hok.2.2.2

theorem mem_bigsP (p : ℕ) (roots : List Noun) (rows : Array RowNX) (a : ℕ) :
    a ∈ bigsP p roots rows ↔ a ∈ (roots ++ rows.toList.flatMap rowHandleNounsX).flatMap leavesOf ∧ p ≤ a := by
  simp [bigsP, List.mem_mergeSort, List.mem_dedup, List.mem_filter, or_and_right]

theorem mem_incOpsP (p : ℕ) (rows : Array RowNX) (vc : ℕ × ℕ) (h : vc ∈ incOpsP p rows) :
    ∃ x ∈ rows.toList, x.st = .s4 ∧ x.sf1 = .atom vc.1 ∧ p ≤ vc.1 + 1 := by
  unfold incOpsP at h
  simp only [List.mem_map, List.mem_dedup] at h
  obtain ⟨v, hv, rfl⟩ := h
  rw [List.mem_filterMap] at hv
  obtain ⟨x, hx, hxv⟩ := hv
  refine ⟨x, hx, ?_⟩
  revert hxv
  cases hst : x.st <;> cases hs1 : x.sf1 <;> simp
  intro h1 h2; subst h2; exact ⟨rfl, h1⟩

theorem leaves_addCells (P : ℕ → Prop) :
    ∀ (n : Noun) (acc : List Noun), (∀ y ∈ acc, ∀ a ∈ leavesOf y, P a) → (∀ a ∈ leavesOf n, P a) →
      ∀ y ∈ addCells n acc, ∀ a ∈ leavesOf y, P a
  | .atom _, acc, hacc, _ => by simpa [addCells] using hacc
  | .cell u w, acc, hacc, hn => by
    simp only [addCells]
    split_ifs
    · exact hacc
    · have hu : ∀ a ∈ leavesOf u, P a := fun a ha => hn a (by simp [leavesOf, ha])
      have hw : ∀ a ∈ leavesOf w, P a := fun a ha => hn a (by simp [leavesOf, ha])
      refine leaves_addCells P w _ (leaves_addCells P u _ (fun y hy => ?_) hu) hw
      rcases List.mem_append.mp hy with hy | hy
      · exact hacc y hy
      · simp at hy; subst hy; exact hn

theorem leaves_cellsOfRoots (roots : List Noun) :
    ∀ y ∈ cellsOfRoots roots, ∀ a ∈ leavesOf y, a ∈ roots.flatMap leavesOf := by
  have key : ∀ (l acc : List Noun), (∀ y ∈ acc, ∀ a ∈ leavesOf y, a ∈ roots.flatMap leavesOf) →
      (∀ n ∈ l, n ∈ roots) → ∀ y ∈ l.foldl (fun acc n => addCells n acc) acc, ∀ a ∈ leavesOf y,
        a ∈ roots.flatMap leavesOf := by
    intro l
    induction l with
    | nil => intro acc h _; simpa using h
    | cons n l ih =>
      intro acc h hl
      simp only [List.foldl_cons]
      refine ih _ (leaves_addCells _ n acc h (fun a ha => List.mem_flatMap.mpr ⟨n, hl n (by simp), ha⟩))
        (fun m hm => hl m (by simp [hm]))
  exact key roots [] (by simp) (fun n hn => hn)

end Run

section RunJ8
variable (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **The run facts of a generated run** at Goldilocks (`GenHyp` of `j8DataOf`), under the two run binders. -/
theorem genHyp_j8 (hax : ComplJ8.ProgAxOK Nock.Atoms.p t) (hop5 : ComplJ8.ProgOp5OK Nock.Atoms.p t)
    (hN : (j8DataOf Nock.Atoms.p Rg Rt hgen).rows.size ≤ 2 ^ 31) :
    GenHyp (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs (j8DataOf Nock.Atoms.p Rg Rt hgen).dupP
      (j8DataOf Nock.Atoms.p Rg Rt hgen).rows (j8DataOf Nock.Atoms.p Rg Rt hgen).mb := by
  have hB : ∀ a, a ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs ↔
      a ∈ ((j8DataOf Nock.Atoms.p Rg Rt hgen).roots ++
        (j8DataOf Nock.Atoms.p Rg Rt hgen).rows.toList.flatMap rowHandleNounsX).flatMap leavesOf ∧
        Nock.Atoms.p ≤ a :=
    fun a => mem_bigsP Nock.Atoms.p _ _ a
  have hrowB : ∀ x ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).rows.toList, ∀ y ∈ rowHandleNounsX x, ∀ a ∈ leavesOf y,
      Nock.Atoms.p ≤ a → a ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs := by
    intro x hx y hy a ha hp
    exact (hB a).mpr ⟨List.mem_flatMap.mpr ⟨y, List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, hy⟩), ha⟩, hp⟩
  refine ⟨fun a ha => ((hB a).mp ha).2, fun vc hvc => ?_, fun ⟨vc, hvc, hp⟩ => ?_, fun j hj hm => ?_, hN⟩
  · obtain ⟨x, hx, hst, hs1, hle⟩ := mem_incOpsP _ _ vc hvc
    obtain ⟨n, hn1, he⟩ := s4_row hgen hax hop5 hx hst
    rw [hs1] at hn1; cases hn1
    have hsf : x.sf1 ∈ rowHandleNounsX x := by simp [rowHandleNounsX]
    have hee : x.e ∈ rowHandleNounsX x := by simp [rowHandleNounsX]
    refine ⟨fun hp => hrowB x hx _ hee _ (by rw [he]; simp [leavesOf, hp]) (by omega), fun hp => ⟨?_, ?_⟩⟩
    · exact hrowB x hx _ hsf _ (by rw [hs1]; simp [leavesOf]) (by omega)
    · exact hrowB x hx _ hee _ (by rw [he]; simp [leavesOf]) hle
  · show (incOpsP Nock.Atoms.p (rowsOfT t)).any (fun x => x.1 + 1 = Nock.Atoms.p) = true
    exact List.any_eq_true.mpr ⟨vc, hvc, by simp [hp]⟩
  · rw [mb_eq_cnt Nock.Atoms.p Rg Rt hgen j hj] at hm
    obtain ⟨q, hq, hq0⟩ : ∃ q ∈ ((mbRecs (j8DataOf Nock.Atoms.p Rg Rt hgen)).flatMap NamedRecs.recs).filter
        (fun q => q.1 = j), q.2 ≠ 0 := by
      by_contra hc
      simp only [not_exists, not_and, ne_eq, not_not] at hc
      apply hm
      unfold cnt
      exact List.sum_eq_zero fun x hx => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        exact hc q hq
    simp only [List.mem_filter, decide_eq_true_eq] at hq
    obtain ⟨hq, rfl⟩ := hq
    simp only [mbRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_filterMap,
      Option.map_eq_some_iff] at hq
    obtain ⟨n, hn, i, hi, rfl⟩ := hq
    obtain ⟨c, hc, hnc⟩ := List.mem_flatMap.mp hn
    cases n with
    | cell u w => simp [bigIdOfP] at hi
    | atom a =>
      simp only [bigIdOfP] at hi
      split_ifs at hi with hlt
      cases hi
      refine ⟨a, (hB a).mpr ⟨?_, by omega⟩, rfl⟩
      have hla : a ∈ leavesOf c := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hnc
        cases c with
        | atom b => rcases hnc with h | h <;> simp [hdN', tlN'] at h <;> subst h <;> simp [leavesOf]
        | cell u w => rcases hnc with h | h <;> simp [hdN', tlN'] at h <;> subst h <;> simp [leavesOf]
      have := leaves_cellsOfRoots _ c hc a hla
      exact List.mem_flatMap.mpr (by
        obtain ⟨y, hy, hay⟩ := List.mem_flatMap.mp this
        exact ⟨y, List.mem_append_left _ hy, hay⟩)

/-- **The generator's atom table is valid** for every generated run at Goldilocks: `AtomTab.Valid` of L0's `acs` /
`info` / `mb`, hence `RowOK` at every row (`AtomTab.rows_ok`), from the two run binders (G12 variant 3: no inc-corner
binder; variant 4: the rows bound `hN`, from `h31` by `ComplJ8OfAtom.rows_le_of_rows31`). -/
theorem valid_j8_gen (hax : ComplJ8.ProgAxOK Nock.Atoms.p t) (hop5 : ComplJ8.ProgOp5OK Nock.Atoms.p t)
    (hN : (j8DataOf Nock.Atoms.p Rg Rt hgen).rows.size ≤ 2 ^ 31) :
    (tabOf (j8DataOf Nock.Atoms.p Rg Rt hgen).acs (j8DataOf Nock.Atoms.p Rg Rt hgen).info
      (j8DataOf Nock.Atoms.p Rg Rt hgen).mb (j8DataOf Nock.Atoms.p Rg Rt hgen).rows).Valid :=
  valid_gen _ _ _ _ (genHyp_j8 Rg Rt hgen hax hop5 hN)

end RunJ8

end Gen8

section Gen9
open Nock.V1J8.Gen
open Nock.Atoms (B val limbs)

/-! ## 9. The generator's columns are the honest rows' (`tabOf … .row` = `atomColD`'s data) -/

section Cols
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (acsP combPP rootIdxP incOpsP infoOfP)
open Nock.Edit Nock.Edit.GenX

theorem hd_combOf (l : List ℕ) (h : 2 ≤ l.length) : hdN' (combOf l) = .atom (l.headD 0) := by
  match l, h with
  | [x, y], _ => rfl
  | x :: y :: z :: r, _ => rw [combOf_cons x (y :: z :: r) (by simp)]; rfl

theorem tl_combOf (l : List ℕ) (h : 2 ≤ l.length) :
    tlN' (combOf l) = if 3 ≤ l.length then combOf l.tail else .atom (l.getD 1 0) := by
  match l, h with
  | [x, y], _ => rfl
  | x :: y :: z :: r, _ => rw [combOf_cons x (y :: z :: r) (by simp)]; simp [tlN']

variable (bigs : List ℕ) (dupP : Bool) (rows : Array RowNX) (mb : Array ℕ)

/-- The fold invariant of the generator's `info` (`stInv_infoOfP` at the honest old suffixes). -/
theorem stInv_gen (hg : GenHyp bigs dupP rows mb) :
    StInvP Nock.Atoms.p (acsP Nock.Atoms.p bigs dupP)
      (tabOf (acsP Nock.Atoms.p bigs dupP) (infoOfP Nock.Atoms.p (acsP Nock.Atoms.p bigs dupP) rows) mb rows).lo
      rows (incOpsP Nock.Atoms.p rows) (infoOfP Nock.Atoms.p (acsP Nock.Atoms.p bigs dupP) rows) := by
  refine stInv_infoOfP _ _ _ rows fun vc hvc hp d hr => ?_
  have hm : combOf ((limbs (vc.1 + 1)).drop d) ∈ acsP Nock.Atoms.p bigs dupP :=
    (mem_acsP bigs dupP _).mpr (Or.inl ((mem_spineL bigs _).mpr
      ⟨_, ((hg.ops vc hvc).2 hp).2, (mem_spineOf _ _).mpr ⟨d, hr.2.1, rfl⟩⟩))
  unfold AtomTab.lo
  rw [(sp_idx (rows := rows) bigs dupP _ mb _ hr.2.1 hm).1]
  exact lo_reach hr

/-- **The generator's added atom columns are the honest rows'**: the inc / conversion / chain fields of `info` and
`mb` at row `j` are `(tabOf …).row j`'s (`0 / 1` for the flags). -/
theorem row_info (hg : GenHyp bigs dupP rows mb) (j : ℕ) :
    let T := tabOf (acsP Nock.Atoms.p bigs dupP) (infoOfP Nock.Atoms.p (acsP Nock.Atoms.p bigs dupP) rows) mb rows
    let x := (infoOfP Nock.Atoms.p (acsP Nock.Atoms.p bigs dupP) rows).getD j AInfo.z
    (T.row j).inc = (if x.inc then 1 else 0) ∧ (T.row j).conv = (if x.conv then 1 else 0) ∧
      (T.row j).cout = (if x.cout then 1 else 0) ∧ (T.row j).idxO = x.idxO ∧ (T.row j).lO = x.lO ∧
      (T.row j).kRO = x.kRO ∧ (T.row j).vRO = x.vRO ∧ (T.row j).mi = x.mi ∧ (T.row j).mb = mb.getD j 0 := by
  intro T x
  have hT : T = tabOf (acsP Nock.Atoms.p bigs dupP) (infoOfP Nock.Atoms.p (acsP Nock.Atoms.p bigs dupP) rows) mb rows :=
    rfl
  have hx : x = (infoOfP Nock.Atoms.p (acsP Nock.Atoms.p bigs dupP) rows).getD j AInfo.z := rfl
  obtain ⟨h1, h2⟩ := (stInv_gen bigs dupP rows mb hg).ok j
  simp only [← hT, ← hx] at h1 h2
  change (if x.inc = true then 1 else 0) = (if x.inc then 1 else 0) ∧
    (if x.conv = true then 1 else 0) = (if x.conv then 1 else 0) ∧
    (if x.inc = true ∧ (T.lo j).headD 0 = B - 1 then 1 else 0) = (if x.cout then 1 else 0) ∧
    (if x.inc = true then x.idxO else 0) = x.idxO ∧
    (if x.inc = true then (T.lo j).headD 0 else 0) = x.lO ∧
    (if x.inc = true ∧ 3 ≤ (T.lo j).length then 1 else 0) = x.kRO ∧
    (if x.inc = true then (if 3 ≤ (T.lo j).length then T.ip (T.lo j) else (T.lo j).getD 1 0) else 0) =
      x.vRO ∧ x.mi = x.mi ∧ mb.getD j 0 = mb.getD j 0
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · cases hi : x.inc
    · obtain ⟨z1, -⟩ := h2 hi; rw [z1]; simp
    · obtain ⟨-, e3, -, -⟩ := h1 hi; rw [e3]
      by_cases hb : (T.lo j).headD 0 = B - 1 <;> simp [hb]
  · cases hi : x.inc
    · obtain ⟨-, z2, -⟩ := h2 hi; rw [z2]; simp
    · rfl
  · cases hi : x.inc
    · obtain ⟨-, -, z3, -⟩ := h2 hi; rw [z3]; simp
    · obtain ⟨e2, -⟩ := h1 hi; rw [e2]; simp
  · cases hi : x.inc
    · obtain ⟨-, -, -, z4, -⟩ := h2 hi; rw [z4]; simp
    · obtain ⟨-, -, e4, -⟩ := h1 hi; rw [e4]
      by_cases h3 : 3 ≤ (T.lo j).length <;> simp [h3]
  · cases hi : x.inc
    · obtain ⟨-, -, -, -, z5⟩ := h2 hi; rw [z5]; simp
    · obtain ⟨-, -, -, e5⟩ := h1 hi; rw [e5]; simp only [if_true]; rfl

/-- **An inc row's old copy is a spine row** (GLA, additive): row `j` of the honest table with `inc` set has an old
limb list of length `≥ 2` whose comb is in the atom cell list (`v`'s depth-`d` suffix, `v` a big atom). -/
theorem inc_old (hg : GenHyp bigs dupP rows mb) (j : ℕ)
    (hj : (tabOf (acsP Nock.Atoms.p bigs dupP) (infoOfP Nock.Atoms.p (acsP Nock.Atoms.p bigs dupP) rows) mb rows).inc j
      = true) :
    j < (acsP Nock.Atoms.p bigs dupP).length ∧
    2 ≤ ((tabOf (acsP Nock.Atoms.p bigs dupP) (infoOfP Nock.Atoms.p (acsP Nock.Atoms.p bigs dupP) rows) mb rows).lo j).length ∧
    combOf ((tabOf (acsP Nock.Atoms.p bigs dupP) (infoOfP Nock.Atoms.p (acsP Nock.Atoms.p bigs dupP) rows) mb rows).lo j)
      ∈ acsP Nock.Atoms.p bigs dupP := by
  have hI := stInv_gen bigs dupP rows mb hg
  obtain ⟨hk, vc, hvc, hp, d, hr, rfl⟩ := (hI.inc j).mp hj
  have hm : combOf ((limbs (vc.1 + 1)).drop d) ∈ acsP Nock.Atoms.p bigs dupP :=
    (mem_acsP bigs dupP _).mpr (Or.inl ((mem_spineL bigs _).mpr
      ⟨_, ((hg.ops vc hvc).2 hp).2, (mem_spineOf _ _).mpr ⟨d, hr.2.1, rfl⟩⟩))
  have hlo : (tabOf (acsP Nock.Atoms.p bigs dupP) (infoOfP Nock.Atoms.p (acsP Nock.Atoms.p bigs dupP) rows) mb rows).lo
      (idxOf (acsP Nock.Atoms.p bigs dupP) (combOf ((limbs (vc.1 + 1)).drop d))) = (limbs vc.1).drop d := by
    unfold AtomTab.lo
    rw [(sp_idx (rows := rows) bigs dupP _ mb _ hr.2.1 hm).1]
    exact lo_reach hr
  rw [hlo]
  exact ⟨hk, hr.2.2.1, (mem_acsP bigs dupP _).mpr (Or.inl ((mem_spineL bigs _).mpr
    ⟨_, ((hg.ops vc hvc).2 hp).1, (mem_spineOf _ _).mpr ⟨d, hr.2.2.1, rfl⟩⟩))⟩

theorem idxOf_inj_mem {l : List Noun} {x y : Noun} (hx : x ∈ l) (hy : y ∈ l) (h : idxOf l x = idxOf l y) :
    x = y := by
  have e1 := getElem?_idxD _ _ hx
  have e2 := getElem?_idxD _ _ hy
  rw [← idxOf_eq _ _ hx, h, idxOf_eq _ _ hy, e2] at e1
  exact (Option.some.inj e1).symm

local notation "ACS" => acsP Nock.Atoms.p bigs dupP
local notation "TT" => tabOf (acsP Nock.Atoms.p bigs dupP) (infoOfP Nock.Atoms.p (acsP Nock.Atoms.p bigs dupP) rows) mb rows

theorem comb_mem_gen (hg : GenHyp bigs dupP rows mb) {a : ℕ} (ha : a ∈ bigs) (d : ℕ)
    (hd : 2 ≤ ((limbs a).drop d).length) : combOf ((limbs a).drop d) ∈ ACS :=
  (mem_acsP bigs dupP _).mpr (Or.inl ((mem_spineL bigs _).mpr ⟨a, ha, (mem_spineOf _ _).mpr ⟨d, hd, rfl⟩⟩))

/-- **`p`'s depth-0 row** (when `p` is a slow operand): the row `comb (p + 1)` is in the table, its old suffix is
`p`'s limbs. -/
theorem lo_fix (hg : GenHyp bigs dupP rows mb) (hq : ∃ w ∈ incOpsP Nock.Atoms.p rows, w.1 = Nock.Atoms.p) :
    combOf (limbs (Nock.Atoms.p + 1)) ∈ ACS ∧ 2 ≤ (limbs (Nock.Atoms.p + 1)).length ∧
      (TT).lo (idxOf ACS (combOf (limbs (Nock.Atoms.p + 1)))) = limbs Nock.Atoms.p := by
  obtain ⟨w, hw, hwp⟩ := hq
  have hb1 := ((hg.ops w hw).2 (by omega)).2
  rw [hwp] at hb1
  have hlp := limbs_big_len (hg.big _ hb1)
  have hm : combOf (limbs (Nock.Atoms.p + 1)) ∈ ACS := by simpa using comb_mem_gen bigs dupP rows mb hg hb1 0 (by simpa using hlp)
  refine ⟨hm, hlp, ?_⟩
  unfold AtomTab.lo
  rw [(sp_idx (rows := rows) bigs dupP _ mb _ hlp hm).1, Nock.Atoms.val_limbs, Nat.add_sub_cancel]

/-- **The old index of an inc row** (G12 variant 3): the row key of its old suffix's comb (the LAST copy of `comb p`
if the old suffix is `p`'s limbs, else the first copy). -/
theorem idxO_gen (hg : GenHyp bigs dupP rows mb) (j : ℕ) (hj : (TT).inc j = true) :
    ((TT).row j).idxO = ComplJ8Data.keyP Nock.Atoms.p ACS (combOf ((TT).lo j)) := by
  have hl : ∀ vc ∈ incOpsP Nock.Atoms.p rows, vc.1 + 1 ≠ Nock.Atoms.p → ∀ d,
      Reach (fuelOf vc.1) (limbs (vc.1 + 1)) (limbs vc.1) d →
      (TT).lo (idxOf ACS (combOf ((limbs (vc.1 + 1)).drop d))) = (limbs vc.1).drop d := by
    intro vc hvc hp d hr
    unfold AtomTab.lo
    rw [(sp_idx (rows := rows) bigs dupP _ mb _ hr.2.1 (comb_mem_gen bigs dupP rows mb hg ((hg.ops vc hvc).2 hp).2 d hr.2.1)).1]
    exact lo_reach hr
  have hF := stInv_infoFold Nock.Atoms.p ACS (TT).lo rows hl
  have hfi : ((infoFold Nock.Atoms.p ACS rows).getD j AInfo.z).inc = true := by
    rw [← (info_fields _ _ _ _).1]; exact hj
  show (if (TT).inc j = true then ((infoOfP Nock.Atoms.p ACS rows).getD j AInfo.z).idxO else 0) = _
  rw [if_pos hj, info_idxO]
  exact ((hF.ok j).1 hfi).1

/-- **An inc row's old index points at a copy of its old suffix's comb** (no limb count, no corner binder). -/
theorem idxO_copy (hg : GenHyp bigs dupP rows mb) (j : ℕ) (hj : (TT).inc j = true) :
    ((TT).row j).idxO < (ACS).length ∧ (ACS)[((TT).row j).idxO]? = some (combOf ((TT).lo j)) := by
  obtain ⟨-, -, hmem⟩ := inc_old bigs dupP rows mb hg j hj
  rw [idxO_gen bigs dupP rows mb hg j hj]
  unfold ComplJ8Data.keyP
  split_ifs with hc
  · have h0 := lastIdxOf_mem _ _ (hc ▸ hmem)
    have h1 : (ACS)[lastIdxOf ACS (combPP Nock.Atoms.p)]? = some (combOf ((TT).lo j)) := by rw [h0, hc]
    refine ⟨?_, h1⟩
    by_contra hge; rw [List.getElem?_eq_none (by omega)] at h1; cases h1
  · rw [idxOf_eq _ _ hmem]
    exact ⟨idxD_lt _ _ hmem, getElem?_idxD _ _ hmem⟩

/-- **Without a `comb p` duplicate** (J-8) every inc row's old index is the first copy of its old suffix. -/
theorem idxO_nodup (hg : GenHyp bigs dupP rows mb)
    (hd : lastIdxOf ACS (combPP Nock.Atoms.p) = idxOf ACS (combPP Nock.Atoms.p)) (j : ℕ) (hj : (TT).inc j = true) :
    ((TT).row j).idxO = (TT).ix ((TT).lo j) := by
  rw [idxO_gen bigs dupP rows mb hg j hj]
  show ComplJ8Data.keyP Nock.Atoms.p ACS (combOf ((TT).lo j)) = idxOf ACS (combOf ((TT).lo j))
  unfold ComplJ8Data.keyP
  split_ifs with hc
  · rw [hd, hc]
  · rfl

/-- **The depth-0 old index is the root serial** (GLC's `IdxOOK`; no corner binder): the inc row `comb (v + 1)` of a
non-conversion operand `v` keys `rootIdxP p acs v`. -/
theorem idxO_root (hg : GenHyp bigs dupP rows mb) (vc : ℕ × ℕ) (hvc : vc ∈ incOpsP Nock.Atoms.p rows)
    (hp : vc.1 + 1 ≠ Nock.Atoms.p) :
    ((TT).row (idxOf ACS (combOf (limbs (vc.1 + 1))))).idxO = rootIdxP Nock.Atoms.p ACS vc.1 := by
  have hI := stInv_gen bigs dupP rows mb hg
  obtain ⟨hv, hv1⟩ := (hg.ops vc hvc).2 hp
  have hl1 := limbs_big_len (hg.big _ hv1)
  have hl0 := limbs_big_len (hg.big _ hv)
  have hm1 : combOf (limbs (vc.1 + 1)) ∈ ACS := by simpa using comb_mem_gen bigs dupP rows mb hg hv1 0 (by simpa using hl1)
  have hr0 : Reach (fuelOf vc.1) (limbs (vc.1 + 1)) (limbs vc.1) 0 :=
    ⟨by unfold fuelOf; omega, by simpa using hl1, by simpa using hl0, fun i hi => by omega⟩
  have hinc : (TT).inc (idxOf ACS (combOf (limbs (vc.1 + 1)))) = true :=
    (hI.inc _).mpr ⟨(sp_idx (rows := rows) bigs dupP (infoOfP Nock.Atoms.p ACS rows) mb _ hl1 hm1).2, vc, hvc, hp, 0, hr0, by simp⟩
  have hlo : (TT).lo (idxOf ACS (combOf (limbs (vc.1 + 1)))) = limbs vc.1 := by
    unfold AtomTab.lo
    rw [(sp_idx (rows := rows) bigs dupP (infoOfP Nock.Atoms.p ACS rows) mb _ hl1 hm1).1, Nock.Atoms.val_limbs, Nat.add_sub_cancel]
  rw [idxO_gen bigs dupP rows mb hg _ hinc, hlo]
  unfold ComplJ8Data.keyP rootIdxP
  by_cases hv : vc.1 = Nock.Atoms.p
  · simp [hv, combPP]
  · have hne : combOf (limbs vc.1) ≠ combPP Nock.Atoms.p := by
      intro e
      have hlp := limbs_big_len (le_refl Nock.Atoms.p)
      have := congrArg val (combOf_inj hl0 hlp e)
      rw [Nock.Atoms.val_limbs, Nock.Atoms.val_limbs] at this
      exact hv this
    rw [if_neg hne, if_neg hv]

/-- **The generator's cell-part columns of an atom row are the honest row's**: at row `j` (noun `y = acs[j]`),
`aL = atomV (hd y)`, `wL`, `wR` are the cell flags of the children, `aR = atomV (tl y)`, `idR` the variant-3 pointer
`ptrP` of a cell tail (`GenMem.cellD` / `atomColD` re-keyed). -/
theorem row_cell (hg : GenHyp bigs dupP rows mb) (info : Array AInfo) (j : ℕ)
    (hj : j < (acsP Nock.Atoms.p bigs dupP).length) :
    let T := tabOf (acsP Nock.Atoms.p bigs dupP) info mb rows
    let y := (acsP Nock.Atoms.p bigs dupP)[j]
    (T.row j).idx = j ∧ (T.row j).aL = atomV (hdN' y) ∧ (T.row j).aR = atomV (tlN' y) ∧
      (T.row j).wL = (if (hdN' y).isCell then 1 else 0) ∧ (T.row j).wR = (if (tlN' y).isCell then 1 else 0) ∧
      (T.row j).idR = (if (tlN' y).isCell then ComplJ8Data.ptrP Nock.Atoms.p (acsP Nock.Atoms.p bigs dupP) rows y else 0) := by
  intro T y
  obtain ⟨l, h2, hc, hy, -⟩ := shape_acsP bigs dupP hg.big _ (List.getElem_mem hj)
  have hsp : T.sp j = l := sp_at (rows := rows) bigs dupP info mb h2 (by rw [List.getElem?_eq_getElem hj, hy])
  have hy' : y = combOf l := hy
  simp only [T, AtomTab.row] at hsp ⊢
  rw [hsp, hy', hd_combOf l h2, tl_combOf l h2]
  by_cases h3 : 3 ≤ l.length
  · have hct := combOf_isCell l.tail (by simp; omega)
    obtain ⟨u, w, huw⟩ : ∃ u w, combOf l.tail = .cell u w := by
      cases h : combOf l.tail with
      | atom v => rw [h] at hct; simp [Noun.isCell] at hct
      | cell u w => exact ⟨u, w, rfl⟩
    simp only [h3, if_true, huw, Noun.isCell, atomV, tabOf]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial | (rw [← huw]) | simp
  · simp only [h3, if_false, Noun.isCell, atomV, tabOf]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial | simp

end Cols

end Gen9

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom
