/-
  Nock/NockVMROM/Thm54/VclL/Chips/HonestMemGenCell.lean

`cellRow0 z cells vcs xs0 xs1 n` is the round-0 / round-1 content of the cell row of the noun `n`
  (`GenMemTable.rowB0`'s columns cast into the base field `F`, the `110` rank bits, the three NPR
  fingerprints at the tower seed `z`), with the export multiplicity SPLIT per side: `mx` counts the side-0
  export consumers `xs0`, `mx1` the side-1 consumers `xs1` (the generator's single `mx` has no side;
  `GenMemTable.rowB0.mx` is the count over `xs0 ++ xs1`).  `cellRows0` indexes the rows by closure position.
  `cellRows0_baseFacts` discharges `CellBaseFacts` and `cellRows0_cons` / `_atomL` / `_atomR` the row-level half of
  `CellMixedFacts`, from a nodup closure whose nouns are cells of rank `< 2^110`.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemFill
import Nock.NockVMROM.Thm54.TraceGen.GenPathRows

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.T0Tower
open Module
open scoped Polynomial

noncomputable section

/-- **A natural `x < 2^m` as the sum of its bits.** -/
theorem sum_testBit_nat : ∀ (m x : ℕ), x < 2 ^ m →
    x = ∑ k ∈ Finset.range m, 2 ^ k * (if x.testBit k then 1 else 0) := by
  intro m
  induction m with
  | zero => intro x hx; simp at hx; simp [hx]
  | succ m ih =>
    intro x hx
    rw [Finset.sum_range_succ']
    have h2 : x / 2 < 2 ^ m := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at hx; exact hx
    have hS := ih (x / 2) h2
    have e : ∀ k, 2 ^ (k + 1) * (if x.testBit (k + 1) then 1 else 0) =
        2 * (2 ^ k * (if (x / 2).testBit k then 1 else 0)) := by
      intro k; rw [Nat.testBit_succ, pow_succ]; ring
    simp only [e, ← Finset.mul_sum]
    simp only [Nat.testBit_zero, pow_zero, one_mul]
    generalize (∑ k ∈ Finset.range m, 2 ^ k * if (x / 2).testBit k = true then 1 else 0) = S at hS ⊢
    split_ifs with h <;> simp at h <;> omega

theorem sum_testBit_cast {F : Type} [Field F] (m x : ℕ) (hx : x < 2 ^ m) :
    (x : F) = ∑ k ∈ Finset.range m, (2 : F) ^ k * (if x.testBit k then 1 else 0) := by
  have h := congrArg (Nat.cast : ℕ → F) (sum_testBit_nat m x hx)
  rw [Nat.cast_sum] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

section GenCell
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

/-- Rank bit `k` of a rank `r`: `0 … 61` the bits of `r % 2^62`, `62 …` the bits of `r / 2^62`. -/
def rankBit (r k : ℕ) : F :=
  if k < 62 then (if (r % 2 ^ 62).testBit k then 1 else 0)
  else (if (r / 2 ^ 62).testBit (k - 62) then 1 else 0)

/-- **The B0 / B1 content of the cell row of `n`** (B2 fields `0`). -/
def cellRow0 (z : Quad (algebraMap F K δF)) (cells vcs xs0 xs1 : List Noun) (n : Noun) :
    CellVals F (Quad (algebraMap F K δF)) where
  idx := (cells.idxOf n : F)
  idL := if (hdN n).isCell then (cells.idxOf (hdN n) : F) else 0
  idR := if (tlN n).isCell then (cells.idxOf (tlN n) : F) else 0
  wL := if (hdN n).isCell then 1 else 0
  wR := if (tlN n).isCell then 1 else 0
  aL := match hdN n with | .atom v => (v : F) | _ => 0
  aR := match tlN n with | .atom v => (v : F) | _ => 0
  lo := ((rankOf n % 2 ^ 62 : ℕ) : F)
  hi := ((rankOf n / 2 ^ 62 : ℕ) : F)
  loL := ((rankOf (hdN n) % 2 ^ 62 : ℕ) : F)
  hiL := ((rankOf (hdN n) / 2 ^ 62 : ℕ) : F)
  loR := ((rankOf (tlN n) % 2 ^ 62 : ℕ) : F)
  hiR := ((rankOf (tlN n) / 2 ^ 62 : ℕ) : F)
  carry := (((rankOf (hdN n) % 2 ^ 62 + rankOf (tlN n) % 2 ^ 62 + 1) / 2 ^ 62 : ℕ) : F)
  mv := (vcs.count n : F)
  mx := (xs0.count n : F)
  mx1 := (xs1.count n : F)
  bit := rankBit (rankOf n)
  p := GlobalCarryRecognizer.enc z n
  l := GlobalCarryRecognizer.enc z (hdN n)
  r := GlobalCarryRecognizer.enc z (tlN n)
  vInv := 0
  lInv := 0
  rInv := 0
  x0Inv := 0
  x1Inv := 0
  vAcc := 0
  xAcc := 0

/-- **The cell rows by closure position** (`ℕ`-indexed; positions `≥ cells.length` are never read). -/
def cellRows0 (z : Quad (algebraMap F K δF)) (cells vcs xs0 xs1 : List Noun) (j : ℕ) :
    CellVals F (Quad (algebraMap F K δF)) :=
  cellRow0 δF z cells vcs xs0 xs1 (cells.getD j (.atom 0))

variable {δF}

theorem cellRows0_getElem (z : Quad (algebraMap F K δF)) (cells vcs xs0 xs1 : List Noun) {j : ℕ}
    (hj : j < cells.length) :
    cellRows0 δF z cells vcs xs0 xs1 j = cellRow0 δF z cells vcs xs0 xs1 cells[j] := by
  simp [cellRows0, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem cellRows0_idx (z : Quad (algebraMap F K δF)) (cells vcs xs0 xs1 : List Noun)
    (hnd : cells.Nodup) {j : ℕ} (hj : j < cells.length) :
    (cellRows0 δF z cells vcs xs0 xs1 j).idx = (j : F) := by
  rw [cellRows0_getElem z cells vcs xs0 xs1 hj]
  show (cells.idxOf cells[j] : F) = j
  rw [hnd.idxOf_getElem j hj]

/-- **The row-level base facts of one generated row** (`n = cell a b`, rank `< 2^110`). -/
theorem cellRow0_limbs (z : Quad (algebraMap F K δF)) (cells vcs xs0 xs1 : List Noun) (a b : Noun)
    (hr : rankOf (.cell a b) < 2 ^ 110) :
    let c := cellRow0 δF z cells vcs xs0 xs1 (.cell a b)
    c.lo + 2 ^ 62 * c.carry = c.loL + c.loR + 1 ∧ c.hi = c.hiL + c.hiR + c.carry ∧
    c.carry * (c.carry - 1) = 0 ∧
    c.lo = ∑ k ∈ Finset.range 62, (2 : F) ^ k * c.bit k ∧
    c.hi = ∑ k ∈ Finset.range 48, (2 : F) ^ k * c.bit (62 + k) ∧
    (∀ k < 110, c.bit k * (c.bit k - 1) = 0) := by
  intro c
  obtain ⟨hlo, hloL, hloR, hhi, hhiL, hhiR, hcar, e1, e2, -, -, -⟩ :=
    genMemTable_rank_limbs (q := 0) cells vcs xs0 a b hr
  simp only [rowB0] at hlo hloL hloR hhi hhiL hhiR hcar e1 e2
  dsimp only [c, cellRow0, hdN, tlN]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg (Nat.cast : ℕ → F) e1
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at this
    linear_combination this
  · have := congrArg (Nat.cast : ℕ → F) e2
    simp only [Nat.cast_add] at this
    exact this
  · generalize (rankOf a % 2 ^ 62 + rankOf b % 2 ^ 62 + 1) / 2 ^ 62 = cc at hcar ⊢
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcar with h | h <;> simp [h]
  · simp only [rankBit]
    rw [sum_testBit_cast 62 _ hlo]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp [Finset.mem_range.mp hk]
  · simp only [rankBit]
    rw [sum_testBit_cast 48 _ hhi]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    have h1 : ¬ 62 + k < 62 := by omega
    simp [h1]
  · intro k _
    simp only [rankBit]
    split_ifs <;> simp

end GenCell

section Facts
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] {δF : F}
  [Fact (¬ IsSquare (algebraMap F K δF))] (z : Quad (algebraMap F K δF)) (cells vcs xs0 xs1 : List Noun)
  (hcell : ∀ n ∈ cells, n.isCell = true)
include hcell

theorem cellRows0_shape {j : ℕ} (hj : j < cells.length) :
    ∃ a b, cells[j] = .cell a b ∧
      cellRows0 δF z cells vcs xs0 xs1 j = cellRow0 δF z cells vcs xs0 xs1 (.cell a b) := by
  have hc := hcell _ (List.getElem_mem hj)
  generalize hn : cells[j] = n at hc
  cases n with
  | atom _ => simp [Noun.isCell] at hc
  | cell a b => exact ⟨a, b, rfl, by rw [cellRows0_getElem z cells vcs xs0 xs1 hj, hn]⟩

/-- **`CellBaseFacts` of the generated table.** -/
theorem cellRows0_baseFacts (hnd : cells.Nodup) (hrank : ∀ n ∈ cells, rankOf n < 2 ^ 110) {N : ℕ}
    (hN : N = cells.length) (i : Fin N) :
    CellBaseFacts (fun j : Fin N => cellRows0 δF z cells vcs xs0 xs1 j) i := by
  subst hN
  have hi : (i : ℕ) < cells.length := i.isLt
  obtain ⟨a, b, hab, hrow⟩ := cellRows0_shape z cells vcs xs0 xs1 hcell hi
  have hr : rankOf (.cell a b) < 2 ^ 110 := hab ▸ hrank _ (List.getElem_mem hi)
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := cellRow0_limbs (δF := δF) z cells vcs xs0 xs1 a b hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    show (cellRows0 δF z cells vcs xs0 xs1 i).idx = 0
    rw [cellRows0_idx z cells vcs xs0 xs1 hnd hi, h0]; simp
  · intro hi'
    show (cellRows0 δF z cells vcs xs0 xs1 ((i : ℕ) + 1)).idx = (cellRows0 δF z cells vcs xs0 xs1 i).idx + 1
    rw [cellRows0_idx z cells vcs xs0 xs1 hnd hi', cellRows0_idx z cells vcs xs0 xs1 hnd hi]; simp
  · show (cellRows0 δF z cells vcs xs0 xs1 i).lo + _ * (cellRows0 δF z cells vcs xs0 xs1 i).carry = _
    rw [hrow]; exact l1
  · show (cellRows0 δF z cells vcs xs0 xs1 i).hi = _
    rw [hrow]; exact l2
  · show (cellRows0 δF z cells vcs xs0 xs1 i).carry * _ = 0
    rw [hrow]; exact l3
  · show (cellRows0 δF z cells vcs xs0 xs1 i).wL * ((cellRows0 δF z cells vcs xs0 xs1 i).wL - 1) = 0
    rw [hrow]; dsimp only [cellRow0, hdN]; split_ifs <;> simp [*]
  · show (cellRows0 δF z cells vcs xs0 xs1 i).wR * ((cellRows0 δF z cells vcs xs0 xs1 i).wR - 1) = 0
    rw [hrow]; dsimp only [cellRow0, tlN]; split_ifs <;> simp [*]
  · show (cellRows0 δF z cells vcs xs0 xs1 i).lo = ∑ k ∈ Finset.range 62, _ * (cellRows0 δF z cells vcs xs0 xs1 i).bit k
    rw [hrow]; exact l4
  · show (cellRows0 δF z cells vcs xs0 xs1 i).hi = ∑ k ∈ Finset.range 48, _ * (cellRows0 δF z cells vcs xs0 xs1 i).bit (62 + k)
    rw [hrow]; exact l5
  · intro k hk
    show (cellRows0 δF z cells vcs xs0 xs1 i).bit k * ((cellRows0 δF z cells vcs xs0 xs1 i).bit k - 1) = 0
    rw [hrow]; exact l6 k hk
  · intro hw
    have hw' : (cellRows0 δF z cells vcs xs0 xs1 i).wL = 0 := hw
    rw [hrow] at hw'
    dsimp only [cellRow0, hdN] at hw'
    cases a with
    | cell x y => simp [Noun.isCell] at hw'
    | atom v =>
      show (cellRows0 δF z cells vcs xs0 xs1 i).loL = 0 ∧ (cellRows0 δF z cells vcs xs0 xs1 i).hiL = 0
      rw [hrow]; simp [cellRow0, hdN, rankOf, Noun.internal]
  · intro hw
    have hw' : (cellRows0 δF z cells vcs xs0 xs1 i).wR = 0 := hw
    rw [hrow] at hw'
    dsimp only [cellRow0, tlN] at hw'
    cases b with
    | cell x y => simp [Noun.isCell] at hw'
    | atom v =>
      show (cellRows0 δF z cells vcs xs0 xs1 i).loR = 0 ∧ (cellRows0 δF z cells vcs xs0 xs1 i).hiR = 0
      rw [hrow]; simp [cellRow0, tlN, rankOf, Noun.internal]

/-- The row-level half of `CellMixedFacts`: cons and the atom pins. -/
theorem cellRows0_cons (hz : z ≠ 0) {j : ℕ} (hj : j < cells.length) :
    (cellRows0 δF z cells vcs xs0 xs1 j).p =
      ComputeTable.FP.cons z (cellRows0 δF z cells vcs xs0 xs1 j).l (cellRows0 δF z cells vcs xs0 xs1 j).r := by
  obtain ⟨a, b, -, hrow⟩ := cellRows0_shape z cells vcs xs0 xs1 hcell hj
  rw [hrow]
  exact GlobalCarryRecognizer.enc_cons hz a b

omit hcell in
theorem liftQ_natCast (v : ℕ) : liftQ δF (v : F) = (v : Quad (algebraMap F K δF)) := by
  simp [liftQ]

theorem cellRows0_atomL {j : ℕ} (hj : j < cells.length) :
    (cellRows0 δF z cells vcs xs0 xs1 j).wL = 0 →
      (cellRows0 δF z cells vcs xs0 xs1 j).l =
        ComputeTable.FP.atomFP z (liftQ δF (cellRows0 δF z cells vcs xs0 xs1 j).aL) := by
  obtain ⟨a, b, -, hrow⟩ := cellRows0_shape z cells vcs xs0 xs1 hcell hj
  rw [hrow]
  intro hw
  dsimp only [cellRow0, hdN] at hw ⊢
  cases a with
  | cell x y => simp [Noun.isCell] at hw
  | atom v => simp only [hdN]; rw [GlobalCarryRecognizer.enc_atom, liftQ_natCast]

theorem cellRows0_atomR {j : ℕ} (hj : j < cells.length) :
    (cellRows0 δF z cells vcs xs0 xs1 j).wR = 0 →
      (cellRows0 δF z cells vcs xs0 xs1 j).r =
        ComputeTable.FP.atomFP z (liftQ δF (cellRows0 δF z cells vcs xs0 xs1 j).aR) := by
  obtain ⟨a, b, -, hrow⟩ := cellRows0_shape z cells vcs xs0 xs1 hcell hj
  rw [hrow]
  intro hw
  dsimp only [cellRow0, tlN] at hw ⊢
  cases b with
  | cell x y => simp [Noun.isCell] at hw
  | atom v => simp only [tlN]; rw [GlobalCarryRecognizer.enc_atom, liftQ_natCast]

end Facts

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
