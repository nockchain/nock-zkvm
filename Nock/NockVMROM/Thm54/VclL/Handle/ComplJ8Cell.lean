/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Cell.lean

Per-chip: every theorem here is about ONE chip template (`cellChip`, the 40th's 225-column
  cell chip, and `cellChipHQKW`, the J-8 242-column wire-key twin).  The noun list `cells`, the big-atom serial map
  `big`, the multiplicities `mv mx mx1 mh` (indexed by serial) and the publics are PARAMETERS.  The list need NOT
  be duplicate-free (L3's atom cell list repeats `padN` and `combP`): a row's serial is its POSITION `j` (as the
  generator's `cellD`), and children point to the FIRST occurrence (`idxOf`).  No gate of these chips needs distinct
  rows.

  * `cellRowB`: the committed B0/B1 content of the cell row of a noun with big-atom children (a big child is
    weighted, `w = 1`, rank `(0, 0)`, its value column `0`, its id the atom-table serial `big a`), the 40th's
    `cellRow0` otherwise; `cellRowsB` indexes the rows by list position.
  * `cellRowsB_baseFacts`, `cellRowsB_cons`, `cellRowsB_atomL/R`: the row facts of `cellOk_sat`.
  * **`cellChip_honest_list`**: the 40th's `cellChip` accepts the honest trace of the filled rows of ANY
    list of cells of rank `< 2^110`, given the IO poles nonzero and publics `0..3` equal to the two terminals.
    (This is the `hsat0` of `HonestKW.cellChipHQKW_accepts_honest` and of the atom table's `HonestA8` /
    `AtomChipHQL` honest theorems through `CellTraceHQ.cellChipHQ_accepts_honest`.)
  * `sideOK_rowsB_L/R`: the per-child side condition `SideOK` at the honest kind bits, from `2^63 < char F`.
  * **`cellChipHQKW_honest_list`**: `cellChipHQKW` accepts `HonestKW.cellTraceHQKW` at those rows, given in
    addition the wire-key poles and the `𝕂′` public `pubHQ` equal to the handle total.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestKW
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemAccept
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemGenCell

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Cell

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.ComputeTable (FP)

noncomputable section

/-! ## 1. The rows -/

/-- A big-atom child: an atom the atom table serves (`big a = some serial`). -/
def isBig (big : Noun → Option ℕ) (n : Noun) : Bool := !n.isCell && (big n).isSome

section Rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The weight of a child: `1` for a cell or a big atom. -/
def wOf (big : Noun → Option ℕ) (n : Noun) : F := if n.isCell || isBig big n then 1 else 0

/-- The id of a child: the cell's list position, or the big atom's serial (`0` for a small atom). -/
def idOf (cells : List Noun) (big : Noun → Option ℕ) (n : Noun) : F :=
  if n.isCell then (cells.idxOf n : F) else (((big n).getD 0 : ℕ) : F)

/-- The value column of a child: the atom value for a small atom, `0` otherwise. -/
def aOf (big : Noun → Option ℕ) (n : Noun) : F :=
  if isBig big n then 0 else match n with | .atom v => (v : F) | _ => 0

/-- **The B0 / B1 content of the cell row of `n` at serial `j`** with big-atom children (B2 fields `0`). -/
def cellRowB (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ) (n : Noun) (j : ℕ) :
    CellVals F 𝕂′ :=
  { cellRow0 δF z cells [] [] [] n with
    idx := (j : F)
    idL := idOf cells big (hdN n)
    idR := idOf cells big (tlN n)
    wL := wOf big (hdN n)
    wR := wOf big (tlN n)
    aL := aOf big (hdN n)
    aR := aOf big (tlN n)
    mv := (mv j : F)
    mx := (mx j : F)
    mx1 := (mx1 j : F) }

/-- **The cell rows by list position.** -/
def cellRowsB (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ) (j : ℕ) :
    CellVals F 𝕂′ :=
  cellRowB δF z big cells mv mx mx1 (cells.getD j (.atom 0)) j

/-- The kind bit of a child (`1` exactly at a big atom). -/
def kbOf (big : Noun → Option ℕ) (n : Noun) : F := if isBig big n then 1 else 0

variable {δF}

theorem cellRowsB_getElem (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ) {j : ℕ}
    (hj : j < cells.length) :
    cellRowsB δF z big cells mv mx mx1 j = cellRowB δF z big cells mv mx mx1 cells[j] j := by
  simp [cellRowsB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem wOf_bool (big : Noun → Option ℕ) (n : Noun) : wOf (F := F) big n * (wOf big n - 1) = 0 := by
  unfold wOf; split_ifs <;> simp

theorem wOf_zero {big : Noun → Option ℕ} {n : Noun} (h : wOf (F := F) big n = 0) :
    ∃ v, n = .atom v ∧ isBig big n = false := by
  unfold wOf at h
  split_ifs at h with h1
  · exact absurd h one_ne_zero
  · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h1
    cases n with
    | cell _ _ => simp [Noun.isCell] at h1
    | atom v => exact ⟨v, rfl, h1.2⟩

end Rows

section Facts
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] {δF : F}
  [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

variable (z : Quad (algebraMap F K δF)) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ)

theorem cellRowsB_shape (hcell : ∀ c ∈ cells, c.isCell = true) {j : ℕ} (hj : j < cells.length) :
    ∃ a b, cells[j] = .cell a b ∧
      cellRowsB δF z big cells mv mx mx1 j = cellRowB δF z big cells mv mx mx1 (.cell a b) j := by
  have hc := hcell _ (List.getElem_mem hj)
  generalize hn : cells[j] = n at hc
  cases n with
  | atom _ => simp [Noun.isCell] at hc
  | cell a b => exact ⟨a, b, rfl, by rw [cellRowsB_getElem z big cells mv mx mx1 hj, hn]⟩

theorem cellRowsB_idx (j : ℕ) : (cellRowsB δF z big cells mv mx mx1 j).idx = (j : F) := rfl

/-- **`CellBaseFacts` of the rows** (any list of cells of rank `< 2^110`). -/
theorem cellRowsB_baseFacts (hcell : ∀ c ∈ cells, c.isCell = true) (hrank : ∀ n ∈ cells, rankOf n < 2 ^ 110) {N : ℕ}
    (hN : N = cells.length) (i : Fin N) :
    CellBaseFacts (fun j : Fin N => cellRowsB δF z big cells mv mx mx1 j) i := by
  subst hN
  have hi : (i : ℕ) < cells.length := i.isLt
  obtain ⟨a, b, hab, hrow⟩ := cellRowsB_shape z big cells mv mx mx1 hcell hi
  have hr : rankOf (.cell a b) < 2 ^ 110 := hab ▸ hrank _ (List.getElem_mem hi)
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := cellRow0_limbs (δF := δF) z cells [] [] [] a b hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    show (cellRowsB δF z big cells mv mx mx1 i).idx = 0
    rw [cellRowsB_idx z big cells mv mx mx1, h0]; simp
  · intro hi'
    show (cellRowsB δF z big cells mv mx mx1 ((i : ℕ) + 1)).idx = (cellRowsB δF z big cells mv mx mx1 i).idx + 1
    rw [cellRowsB_idx z big cells mv mx mx1, cellRowsB_idx z big cells mv mx mx1]
    simp
  · show (cellRowsB δF z big cells mv mx mx1 i).lo + _ * (cellRowsB δF z big cells mv mx mx1 i).carry = _
    rw [hrow]; exact l1
  · show (cellRowsB δF z big cells mv mx mx1 i).hi = _
    rw [hrow]; exact l2
  · show (cellRowsB δF z big cells mv mx mx1 i).carry * _ = 0
    rw [hrow]; exact l3
  · show (cellRowsB δF z big cells mv mx mx1 i).wL * ((cellRowsB δF z big cells mv mx mx1 i).wL - 1) = 0
    rw [hrow]; exact wOf_bool big _
  · show (cellRowsB δF z big cells mv mx mx1 i).wR * ((cellRowsB δF z big cells mv mx mx1 i).wR - 1) = 0
    rw [hrow]; exact wOf_bool big _
  · show (cellRowsB δF z big cells mv mx mx1 i).lo =
      ∑ k ∈ Finset.range 62, _ * (cellRowsB δF z big cells mv mx mx1 i).bit k
    rw [hrow]; exact l4
  · show (cellRowsB δF z big cells mv mx mx1 i).hi =
      ∑ k ∈ Finset.range 48, _ * (cellRowsB δF z big cells mv mx mx1 i).bit (62 + k)
    rw [hrow]; exact l5
  · intro k hk
    show (cellRowsB δF z big cells mv mx mx1 i).bit k * ((cellRowsB δF z big cells mv mx mx1 i).bit k - 1) = 0
    rw [hrow]; exact l6 k hk
  · intro hw
    have hw' : (cellRowsB δF z big cells mv mx mx1 i).wL = 0 := hw
    rw [hrow] at hw'
    obtain ⟨v, hv, -⟩ := wOf_zero hw'
    show (cellRowsB δF z big cells mv mx mx1 i).loL = 0 ∧ (cellRowsB δF z big cells mv mx mx1 i).hiL = 0
    rw [hrow]
    simp only [hdN] at hv
    subst hv
    simp [cellRowB, cellRow0, hdN, rankOf, Noun.internal]
  · intro hw
    have hw' : (cellRowsB δF z big cells mv mx mx1 i).wR = 0 := hw
    rw [hrow] at hw'
    obtain ⟨v, hv, -⟩ := wOf_zero hw'
    show (cellRowsB δF z big cells mv mx mx1 i).loR = 0 ∧ (cellRowsB δF z big cells mv mx mx1 i).hiR = 0
    rw [hrow]
    simp only [tlN] at hv
    subst hv
    simp [cellRowB, cellRow0, tlN, rankOf, Noun.internal]

theorem cellRowsB_cons (hcell : ∀ c ∈ cells, c.isCell = true) (hz : z ≠ 0) {j : ℕ} (hj : j < cells.length) :
    (cellRowsB δF z big cells mv mx mx1 j).p =
      FP.cons z (cellRowsB δF z big cells mv mx mx1 j).l (cellRowsB δF z big cells mv mx mx1 j).r := by
  obtain ⟨a, b, -, hrow⟩ := cellRowsB_shape z big cells mv mx mx1 hcell hj
  rw [hrow]
  exact GlobalCarryRecognizer.enc_cons hz a b

theorem cellRowsB_atomL (hcell : ∀ c ∈ cells, c.isCell = true) {j : ℕ} (hj : j < cells.length) :
    (cellRowsB δF z big cells mv mx mx1 j).wL = 0 →
      (cellRowsB δF z big cells mv mx mx1 j).l = FP.atomFP z (liftQ δF (cellRowsB δF z big cells mv mx mx1 j).aL) := by
  obtain ⟨a, b, -, hrow⟩ := cellRowsB_shape z big cells mv mx mx1 hcell hj
  rw [hrow]
  intro hw
  obtain ⟨v, hv, hb⟩ := wOf_zero hw
  simp only [hdN] at hv hb
  subst hv
  show GlobalCarryRecognizer.enc z (.atom v) = FP.atomFP z (liftQ δF (aOf big (.atom v)))
  rw [GlobalCarryRecognizer.enc_atom]
  simp only [aOf, hb, Bool.false_eq_true, if_false]
  rw [liftQ_natCast]

theorem cellRowsB_atomR (hcell : ∀ c ∈ cells, c.isCell = true) {j : ℕ} (hj : j < cells.length) :
    (cellRowsB δF z big cells mv mx mx1 j).wR = 0 →
      (cellRowsB δF z big cells mv mx mx1 j).r = FP.atomFP z (liftQ δF (cellRowsB δF z big cells mv mx mx1 j).aR) := by
  obtain ⟨a, b, -, hrow⟩ := cellRowsB_shape z big cells mv mx mx1 hcell hj
  rw [hrow]
  intro hw
  obtain ⟨v, hv, hb⟩ := wOf_zero hw
  simp only [tlN] at hv hb
  subst hv
  show GlobalCarryRecognizer.enc z (.atom v) = FP.atomFP z (liftQ δF (aOf big (.atom v)))
  rw [GlobalCarryRecognizer.enc_atom]
  simp only [aOf, hb, Bool.false_eq_true, if_false]
  rw [liftQ_natCast]

end Facts

/-! ## 2. `cellChip` (the 40th's 225-column cell chip) at an arbitrary noun list -/

section Accept
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The filled honest rows (`cellFill`: the five inverses and the two accumulators). -/
abbrev valsB (γ ρ z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ) :
    Fin n → CellVals F 𝕂′ :=
  fun i => cellFill δF γ ρ (cellRowsB δF z big cells mv mx mx1) i

/-- **`cellChip_honest_list`: the 40th's cell chip accepts the honest trace of ANY list of cells of rank
`< 2^110` with big-atom children**, at challenges carrying `(γ, ρ)` (`ChalsOK`) and `z` (leaves `2, 3`), given the
validity / export poles nonzero and publics `0..3` equal to the two terminals. -/
theorem cellChip_honest_list (γ ρ z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ)
    (hcell : ∀ c ∈ cells, c.isCell = true) (hrank : ∀ c ∈ cells, rankOf c < 2 ^ 110)
    (hN : n = cells.length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11) (hzc : Quad.mk _ (chals 2) (chals 3) = z) (hz : z ≠ 0)
    (hv : ∀ j < n, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (cellRowsB δF z big cells mv mx mx1 j)) ≠ 0)
    (hl : ∀ j < n, (cellRowsB δF z big cells mv mx mx1 j).wL ≠ 0 →
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (lKeyOf δF (cellRowsB δF z big cells mv mx mx1 j)) ≠ 0)
    (hr : ∀ j < n, (cellRowsB δF z big cells mv mx mx1 j).wR ≠ 0 →
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (rKeyOf δF (cellRowsB δF z big cells mv mx mx1 j)) ≠ 0)
    (hx0 : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (cellRowsB δF z big cells mv mx mx1 j) 0) ≠ 0)
    (hx1 : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (cellRowsB δF z big cells mv mx mx1 j) 1) ≠ 0)
    (hV : ∑ k ∈ Finset.range n, vTermOf δF (cellFillInv δF γ ρ (cellRowsB δF z big cells mv mx mx1 k)) =
      Quad.mk _ (pubs 0) (pubs 1))
    (hX : ∑ k ∈ Finset.range n, xTermOf δF (cellFillInv δF γ ρ (cellRowsB δF z big cells mv mx mx1 k)) =
      Quad.mk _ (pubs 2) (pubs 3)) :
    (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies
      (honestQ hn nodes (cellCol δF b (valsB δF γ ρ z big cells mv mx mx1)) _) := by
  have hlt : ∀ j < n, j < cells.length := fun j hj => hN ▸ hj
  have hok0 := cellOk_sat δF b hn nodes orbit chals pubs (valsB δF γ ρ z big cells mv mx mx1) hinj hadj γ ρ z hok
    hzc (fun i => cellBaseFacts_fill δF γ ρ (cellRowsB δF z big cells mv mx mx1) i
      (cellRowsB_baseFacts z big cells mv mx mx1 hcell hrank hN i))
    (fun i => cellFill_facts γ ρ (cellRowsB δF z big cells mv mx mx1) z pubs i hz
      (fun j hj => cellRowsB_cons z big cells mv mx mx1 hcell hz (hlt j hj))
      (fun j hj => cellRowsB_atomL z big cells mv mx mx1 hcell (hlt j hj))
      (fun j hj => cellRowsB_atomR z big cells mv mx mx1 hcell (hlt j hj)) hv hl hr hx0 hx1 hV hX)
  exact (cellChipOk_sat δF b hn nodes orbit chals pubs true _ hok0).2.1

/-- **`cellChipHQ_honest_list`: the 40th's `𝕂′` handle cell chip `cellChipHQ` (238 columns) accepts
`CellTraceHQ.cellTraceHQ` at the honest rows of ANY list of cells of rank `< 2^110` with big-atom children**:
`cellChip_honest_list`'s hypotheses, the handle poles, and the `𝕂′` public `pubHQ` equal to the handle total.
This is the `hsat0` of `HonestA8.atomChipHQ_accepts_honest` / `AtomChipHQL.atomChipHQL_accepts_honest`
(`col := CellTraceHQ.colHQ … (cellCol … (valsB …)) mhv (ivF …) (avF …)`). -/
theorem cellChipHQ_honest_list (γ ρ z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ)
    (mhv : Fin n → F)
    (hcell : ∀ c ∈ cells, c.isCell = true) (hrank : ∀ c ∈ cells, rankOf c < 2 ^ 110)
    (hN : n = cells.length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11) (hzc : Quad.mk _ (chals 2) (chals 3) = z) (hz : z ≠ 0)
    (hv : ∀ j < n, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (cellRowsB δF z big cells mv mx mx1 j)) ≠ 0)
    (hl : ∀ j < n, (cellRowsB δF z big cells mv mx mx1 j).wL ≠ 0 →
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (lKeyOf δF (cellRowsB δF z big cells mv mx mx1 j)) ≠ 0)
    (hr : ∀ j < n, (cellRowsB δF z big cells mv mx mx1 j).wR ≠ 0 →
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (rKeyOf δF (cellRowsB δF z big cells mv mx mx1 j)) ≠ 0)
    (hx0 : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (cellRowsB δF z big cells mv mx mx1 j) 0) ≠ 0)
    (hx1 : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (cellRowsB δF z big cells mv mx mx1 j) 1) ≠ 0)
    (hV : ∑ k ∈ Finset.range n, vTermOf δF (cellFillInv δF γ ρ (cellRowsB δF z big cells mv mx mx1 k)) =
      Quad.mk _ (pubs 0) (pubs 1))
    (hX : ∑ k ∈ Finset.range n, xTermOf δF (cellFillInv δF γ ρ (cellRowsB δF z big cells mv mx mx1 k)) =
      Quad.mk _ (pubs 2) (pubs 3))
    (hpole : ∀ i, CellTraceHQ.dRow δF b hn nodes orbit chals pubs (cellCol δF b (valsB δF γ ρ z big cells mv mx mx1))
      mhv i ≠ 0)
    (hpub : Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (CellTraceH.mN mhv j) *
        (CellTraceHQ.dN δF b hn nodes orbit chals pubs (cellCol δF b (valsB δF γ ρ z big cells mv mx mx1)) mhv j)⁻¹) :
    (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies
      (CellTraceHQ.cellTraceHQ δF b hn nodes orbit chals pubs (cellCol δF b (valsB δF γ ρ z big cells mv mx mx1)) mhv) :=
  CellTraceHQ.cellChipHQ_accepts_honest δF b hn nodes orbit chals pubs _ mhv hinj hadj
    (cellChip_honest_list δF b hn nodes orbit chals pubs γ ρ z big cells mv mx mx1 hcell hrank hN hinj hadj
      hok hzc hz hv hl hr hx0 hx1 hV hX) hpole hpub

/-- The preprocessing of the honest trace (both masks). -/
theorem cellChip_honest_list_bind (γ ρ z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun)
    (mv mx mx1 : ℕ → ℕ) :
    (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing
      (honestQ hn nodes (cellCol δF b (valsB δF γ ρ z big cells mv mx mx1)) _) := by
  intro j
  fin_cases j
  · exact honestQ_zero hn nodes _ (by rw [(cellChip_fingerprint δF b hn nodes orbit chals pubs).1]; omega)
  · exact honestQ_one hn nodes _ (by rw [(cellChip_fingerprint δF b hn nodes orbit chals pubs).1]; omega)

end Accept

/-! ## 3. The side condition and `cellChipHQKW` (the J-8 wire-key cell twin) at the list -/

section KW
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

local notation "𝕂′" => Quad (algebraMap F K δF)

theorem cellCol_lt (vals : Fin n → CellVals F 𝕂′) {j : ℕ} (hj : j < 129) (i : Fin n) :
    cellCol δF b vals j i = (vals i).base j := by
  simp [cellCol, hj]

/-- The rank limbs of a noun of rank `1 ≤ r < 2^110` sum to a nonzero field element when `2^63 < char F`. -/
theorem limbs_ne_zero (hp : 2 ^ 63 < ringChar F) {r : ℕ} (h1 : 1 ≤ r) (h2 : r < 2 ^ 110) :
    ((r % 2 ^ 62 : ℕ) : F) + ((r / 2 ^ 62 : ℕ) : F) ≠ 0 := by
  rw [← Nat.cast_add]
  intro h0
  rw [CharP.cast_eq_zero_iff F (ringChar F)] at h0
  have hb : r / 2 ^ 62 < 2 ^ 48 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; calc r < 2 ^ 110 := h2
      _ = 2 ^ 48 * 2 ^ 62 := by norm_num
  have hm : r % 2 ^ 62 < 2 ^ 62 := Nat.mod_lt _ (by positivity)
  have hpos : 0 < r % 2 ^ 62 + r / 2 ^ 62 := by
    by_contra hc
    have e1 : r % 2 ^ 62 = 0 := by omega
    have e2 : r / 2 ^ 62 = 0 := by omega
    have := Nat.div_add_mod r (2 ^ 62)
    omega
  have hlt : r % 2 ^ 62 + r / 2 ^ 62 < ringChar F := by
    have : (2 : ℕ) ^ 62 + 2 ^ 48 ≤ 2 ^ 63 := by norm_num
    omega
  exact absurd (Nat.le_of_dvd hpos h0) (by omega)

/-- **The side condition of a child** at the honest kind bit. -/
theorem sideOK_child (hp : 2 ^ 63 < ringChar F) (big : Noun → Option ℕ) (c : Noun) (hc : rankOf c < 2 ^ 110) :
    HonestK8.SideOK (kbOf big c : F) (wOf big c) ((rankOf c % 2 ^ 62 : ℕ) : F) ((rankOf c / 2 ^ 62 : ℕ) : F) := by
  cases c with
  | cell x y =>
    have hb : isBig big (.cell x y) = false := by simp [isBig, Noun.isCell]
    refine Or.inl ⟨by simp [kbOf, hb], Or.inr ⟨by simp [wOf, Noun.isCell], ?_⟩⟩
    exact limbs_ne_zero hp (by simp only [rankOf, Noun.internal]; omega) hc
  | atom v =>
    by_cases hb : isBig big (.atom v) = true
    · exact Or.inr ⟨by simp [kbOf, hb], by simp [wOf, hb], by simp [rankOf, Noun.internal],
        by simp [rankOf, Noun.internal]⟩
    · have hb' : isBig big (.atom v) = false := by simpa using hb
      exact Or.inl ⟨by simp [kbOf, hb'], Or.inl (by simp [wOf, hb', Noun.isCell])⟩

/-- The honest kind-bit columns (`130`, `131`). -/
abbrev kbLB (big : Noun → Option ℕ) (cells : List Noun) : Fin n → F :=
  fun i => kbOf big (hdN (cells.getD i (.atom 0)))
abbrev kbRB (big : Noun → Option ℕ) (cells : List Noun) : Fin n → F :=
  fun i => kbOf big (tlN (cells.getD i (.atom 0)))

theorem rank_children {a c : Noun} (hr : rankOf (.cell a c) < 2 ^ 110) :
    rankOf a < 2 ^ 110 ∧ rankOf c < 2 ^ 110 := by
  simp only [rankOf, Noun.internal] at hr ⊢; omega

theorem sideOK_rowsB_L (hp : 2 ^ 63 < ringChar F) (γ ρ z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun)
    (mv mx mx1 : ℕ → ℕ) (hcell : ∀ c ∈ cells, c.isCell = true) (hrank : ∀ c ∈ cells, rankOf c < 2 ^ 110)
    (hN : n = cells.length) (i : Fin n) :
    HonestK8.SideOK (kbLB big cells i)
      (cellCol δF b (valsB δF γ ρ z big cells mv mx mx1) Cell.wL i)
      (cellCol δF b (valsB δF γ ρ z big cells mv mx mx1) Cell.loL i)
      (cellCol δF b (valsB δF γ ρ z big cells mv mx mx1) Cell.hiL i) := by
  have hi : (i : ℕ) < cells.length := hN ▸ i.isLt
  obtain ⟨a, c, hac, hrow⟩ := cellRowsB_shape (δF := δF) z big cells mv mx mx1 hcell hi
  have hr := hac ▸ hrank _ (List.getElem_mem hi)
  have hg : cells.getD i (.atom 0) = .cell a c := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hac]
  rw [cellCol_lt δF b _ (by simp [Cell.wL]), cellCol_lt δF b _ (by simp [Cell.loL]),
    cellCol_lt δF b _ (by simp [Cell.hiL])]
  simp only [valsB, cellFill, cellFillInv, CellVals.base, Cell.wL, Cell.loL, Cell.hiL, hrow]
  simp only [kbLB, hg]
  exact sideOK_child hp big a (rank_children hr).1

theorem sideOK_rowsB_R (hp : 2 ^ 63 < ringChar F) (γ ρ z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun)
    (mv mx mx1 : ℕ → ℕ) (hcell : ∀ c ∈ cells, c.isCell = true) (hrank : ∀ c ∈ cells, rankOf c < 2 ^ 110)
    (hN : n = cells.length) (i : Fin n) :
    HonestK8.SideOK (kbRB big cells i)
      (cellCol δF b (valsB δF γ ρ z big cells mv mx mx1) Cell.wR i)
      (cellCol δF b (valsB δF γ ρ z big cells mv mx mx1) Cell.loR i)
      (cellCol δF b (valsB δF γ ρ z big cells mv mx mx1) Cell.hiR i) := by
  have hi : (i : ℕ) < cells.length := hN ▸ i.isLt
  obtain ⟨a, c, hac, hrow⟩ := cellRowsB_shape (δF := δF) z big cells mv mx mx1 hcell hi
  have hr := hac ▸ hrank _ (List.getElem_mem hi)
  have hg : cells.getD i (.atom 0) = .cell a c := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hac]
  rw [cellCol_lt δF b _ (by simp [Cell.wR]), cellCol_lt δF b _ (by simp [Cell.loR]),
    cellCol_lt δF b _ (by simp [Cell.hiR])]
  simp only [valsB, cellFill, cellFillInv, CellVals.base, Cell.wR, Cell.loR, Cell.hiR, hrow]
  simp only [kbRB, hg]
  exact sideOK_child hp big c (rank_children hr).2

/-- **The honest J-8 cell trace at the list** (242 columns). -/
abbrev cellTraceB (γ ρ z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 mh : ℕ → ℕ) :=
  HonestKW.cellTraceHQKW δF b hn nodes orbit chals pubs (cellCol δF b (valsB δF γ ρ z big cells mv mx mx1))
    (fun i : Fin n => (mh i : F)) (kbLB big cells) (kbRB big cells)

/-- **`cellChipHQKW_honest_list`: the J-8 cell chip accepts the honest trace of any list of cells of rank
`< 2^110` with big-atom children**: `cellChip_honest_list`'s hypotheses, `2^63 < char F`, the wire-key poles,
and the `𝕂′` public `pubHQ` equal to the handle total. -/
theorem cellChipHQKW_honest_list (hp : 2 ^ 63 < ringChar F) (γ ρ z : 𝕂′) (big : Noun → Option ℕ)
    (cells : List Noun) (mv mx mx1 mh : ℕ → ℕ)
    (hcell : ∀ c ∈ cells, c.isCell = true) (hrank : ∀ c ∈ cells, rankOf c < 2 ^ 110)
    (hN : n = cells.length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11) (hzc : Quad.mk _ (chals 2) (chals 3) = z) (hz : z ≠ 0)
    (hv : ∀ j < n, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (cellRowsB δF z big cells mv mx mx1 j)) ≠ 0)
    (hl : ∀ j < n, (cellRowsB δF z big cells mv mx mx1 j).wL ≠ 0 →
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (lKeyOf δF (cellRowsB δF z big cells mv mx mx1 j)) ≠ 0)
    (hr : ∀ j < n, (cellRowsB δF z big cells mv mx mx1 j).wR ≠ 0 →
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (rKeyOf δF (cellRowsB δF z big cells mv mx mx1 j)) ≠ 0)
    (hx0 : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (cellRowsB δF z big cells mv mx mx1 j) 0) ≠ 0)
    (hx1 : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (cellRowsB δF z big cells mv mx mx1 j) 1) ≠ 0)
    (hV : ∑ k ∈ Finset.range n, vTermOf δF (cellFillInv δF γ ρ (cellRowsB δF z big cells mv mx mx1 k)) =
      Quad.mk _ (pubs 0) (pubs 1))
    (hX : ∑ k ∈ Finset.range n, xTermOf δF (cellFillInv δF γ ρ (cellRowsB δF z big cells mv mx mx1 k)) =
      Quad.mk _ (pubs 2) (pubs 3))
    (hpole : ∀ i, HonestKW.dRowW δF b hn nodes orbit chals pubs (cellCol δF b (valsB δF γ ρ z big cells mv mx mx1))
      (fun i : Fin n => (mh i : F)) (kbLB big cells) (kbRB big cells) i ≠ 0)
    (hpub : Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (CellTraceH.mN (fun i : Fin n => (mh i : F)) j) *
        (HonestKW.dNW δF b hn nodes orbit chals pubs (cellCol δF b (valsB δF γ ρ z big cells mv mx mx1))
          (fun i : Fin n => (mh i : F)) (kbLB big cells) (kbRB big cells) j)⁻¹) :
    (HonestKW.cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies
      (cellTraceB δF b hn nodes orbit chals pubs γ ρ z big cells mv mx mx1 mh) :=
  HonestKW.cellChipHQKW_accepts_honest δF b hn nodes orbit chals pubs _ _ _ _ hinj hadj
    (cellChip_honest_list δF b hn nodes orbit chals pubs γ ρ z big cells mv mx mx1 hcell hrank hN hinj hadj
      hok hzc hz hv hl hr hx0 hx1 hV hX)
    (sideOK_rowsB_L δF b hp γ ρ z big cells mv mx mx1 hcell hrank hN)
    (sideOK_rowsB_R δF b hp γ ρ z big cells mv mx mx1 hcell hrank hN) hpole hpub

/-- The preprocessing of the honest J-8 cell trace (both masks). -/
theorem cellChipHQKW_honest_list_bind (γ ρ z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun)
    (mv mx mx1 mh : ℕ → ℕ) :
    (HonestKW.cellChipHQKW δF b hn nodes orbit chals pubs).BindsPreprocessing
      (cellTraceB δF b hn nodes orbit chals pubs γ ρ z big cells mv mx mx1 mh) := by
  intro j
  fin_cases j
  · exact honestQ_zero hn nodes _ (by rw [HonestKW.cellTemplateHQKW_width]; omega)
  · exact honestQ_one hn nodes _ (by rw [HonestKW.cellTemplateHQKW_width]; omega)

end KW

/-! ## 4. Pointer rows (J-9 B, one pointer everywhere)

The atom table's cell part must read ONE right-child pointer `pt` (the parent-indexed `ComplJ8Data.ptrP p acs rows`)
in its `idR` column, the same as the atom chip's inc/stop data (variant 4).  `cellRowBP` is `cellRowB` with `idR`
re-keyed: a cell right child of `n` gets `pt n`; every other field (and every non-cell `idR`) is `cellRowB`'s.  The
cell chip's honest acceptance does not read `idR`'s value beyond the `rKeyOf` poles, so the honest theorems carry over
verbatim (`cellChip_honest_listP`, `cellChipHQ_honest_listP`).  With `pt n := cells.idxOf (tlN n)` the row is
`cellRowB` (`idRP_idxOf`). -/

section Ptr
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The right-child id at a parent pointer `pt`: `pt n` at a cell right child, `idOf` otherwise. -/
def idRP (cells : List Noun) (big : Noun → Option ℕ) (pt : Noun → ℕ) (n : Noun) : F :=
  if (tlN n).isCell then (pt n : F) else idOf cells big (tlN n)

/-- **The cell row of `n` at serial `j`, right child at the pointer `pt`.** -/
def cellRowBP (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ) (pt : Noun → ℕ)
    (n : Noun) (j : ℕ) : CellVals F 𝕂′ :=
  { cellRowB δF z big cells mv mx mx1 n j with idR := idRP cells big pt n }

/-- **The pointer cell rows by list position.** -/
def cellRowsBP (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ) (pt : Noun → ℕ)
    (j : ℕ) : CellVals F 𝕂′ :=
  cellRowBP δF z big cells mv mx mx1 pt (cells.getD j (.atom 0)) j

variable {δF}

theorem idRP_idxOf (cells : List Noun) (big : Noun → Option ℕ) (n : Noun) :
    idRP (F := F) cells big (fun m => cells.idxOf (tlN m)) n = idOf cells big (tlN n) := by
  unfold idRP idOf; split_ifs <;> rfl

theorem cellRowsBP_getElem (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ)
    (pt : Noun → ℕ) {j : ℕ} (hj : j < cells.length) :
    cellRowsBP δF z big cells mv mx mx1 pt j = cellRowBP δF z big cells mv mx mx1 pt cells[j] j := by
  simp [cellRowsBP, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem cellRowsBP_idR (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ)
    (pt : Noun → ℕ) (j : ℕ) :
    (cellRowsBP δF z big cells mv mx mx1 pt j).idR = idRP cells big pt (cells.getD j (.atom 0)) := rfl

theorem cellRowsBP_baseFacts (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ)
    (pt : Noun → ℕ) (hcell : ∀ c ∈ cells, c.isCell = true) (hrank : ∀ n ∈ cells, rankOf n < 2 ^ 110) {N : ℕ}
    (hN : N = cells.length) (i : Fin N) :
    CellBaseFacts (fun j : Fin N => cellRowsBP δF z big cells mv mx mx1 pt j) i :=
  have h := cellRowsB_baseFacts z big cells mv mx mx1 hcell hrank hN i
  { serial0 := h.serial0, serialStep := h.serialStep, limbLo := h.limbLo, limbHi := h.limbHi,
    carry_bool := h.carry_bool, wL_bool := h.wL_bool, wR_bool := h.wR_bool, lo_bits := h.lo_bits,
    hi_bits := h.hi_bits, bit_bool := h.bit_bool, atomL := h.atomL, atomR := h.atomR }

end Ptr

section AcceptP
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The filled honest pointer rows. -/
abbrev valsBP (γ ρ z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ) (pt : Noun → ℕ) :
    Fin n → CellVals F 𝕂′ :=
  fun i => cellFill δF γ ρ (cellRowsBP δF z big cells mv mx mx1 pt) i

/-- **`cellChip_honest_list` at the pointer rows** (any `pt`). -/
theorem cellChip_honest_listP (γ ρ z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ)
    (pt : Noun → ℕ)
    (hcell : ∀ c ∈ cells, c.isCell = true) (hrank : ∀ c ∈ cells, rankOf c < 2 ^ 110)
    (hN : n = cells.length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11) (hzc : Quad.mk _ (chals 2) (chals 3) = z) (hz : z ≠ 0)
    (hv : ∀ j < n, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (cellRowsBP δF z big cells mv mx mx1 pt j)) ≠ 0)
    (hl : ∀ j < n, (cellRowsBP δF z big cells mv mx mx1 pt j).wL ≠ 0 →
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (lKeyOf δF (cellRowsBP δF z big cells mv mx mx1 pt j)) ≠ 0)
    (hr : ∀ j < n, (cellRowsBP δF z big cells mv mx mx1 pt j).wR ≠ 0 →
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (rKeyOf δF (cellRowsBP δF z big cells mv mx mx1 pt j)) ≠ 0)
    (hx0 : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (cellRowsBP δF z big cells mv mx mx1 pt j) 0) ≠ 0)
    (hx1 : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (cellRowsBP δF z big cells mv mx mx1 pt j) 1) ≠ 0)
    (hV : ∑ k ∈ Finset.range n, vTermOf δF (cellFillInv δF γ ρ (cellRowsBP δF z big cells mv mx mx1 pt k)) =
      Quad.mk _ (pubs 0) (pubs 1))
    (hX : ∑ k ∈ Finset.range n, xTermOf δF (cellFillInv δF γ ρ (cellRowsBP δF z big cells mv mx mx1 pt k)) =
      Quad.mk _ (pubs 2) (pubs 3)) :
    (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies
      (honestQ hn nodes (cellCol δF b (valsBP δF γ ρ z big cells mv mx mx1 pt)) _) := by
  have hlt : ∀ j < n, j < cells.length := fun j hj => hN ▸ hj
  have hok0 := cellOk_sat δF b hn nodes orbit chals pubs (valsBP δF γ ρ z big cells mv mx mx1 pt) hinj hadj γ ρ z
    hok hzc (fun i => cellBaseFacts_fill δF γ ρ (cellRowsBP δF z big cells mv mx mx1 pt) i
      (cellRowsBP_baseFacts z big cells mv mx mx1 pt hcell hrank hN i))
    (fun i => cellFill_facts γ ρ (cellRowsBP δF z big cells mv mx mx1 pt) z pubs i hz
      (fun j hj => cellRowsB_cons z big cells mv mx mx1 hcell hz (hlt j hj))
      (fun j hj => cellRowsB_atomL z big cells mv mx mx1 hcell (hlt j hj))
      (fun j hj => cellRowsB_atomR z big cells mv mx mx1 hcell (hlt j hj)) hv hl hr hx0 hx1 hV hX)
  exact (cellChipOk_sat δF b hn nodes orbit chals pubs true _ hok0).2.1

/-- **`cellChipHQ_honest_list` at the pointer rows** (any `pt`): the atom table's `hsat0`. -/
theorem cellChipHQ_honest_listP (γ ρ z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ)
    (pt : Noun → ℕ) (mhv : Fin n → F)
    (hcell : ∀ c ∈ cells, c.isCell = true) (hrank : ∀ c ∈ cells, rankOf c < 2 ^ 110)
    (hN : n = cells.length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11) (hzc : Quad.mk _ (chals 2) (chals 3) = z) (hz : z ≠ 0)
    (hv : ∀ j < n, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (cellRowsBP δF z big cells mv mx mx1 pt j)) ≠ 0)
    (hl : ∀ j < n, (cellRowsBP δF z big cells mv mx mx1 pt j).wL ≠ 0 →
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (lKeyOf δF (cellRowsBP δF z big cells mv mx mx1 pt j)) ≠ 0)
    (hr : ∀ j < n, (cellRowsBP δF z big cells mv mx mx1 pt j).wR ≠ 0 →
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (rKeyOf δF (cellRowsBP δF z big cells mv mx mx1 pt j)) ≠ 0)
    (hx0 : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (cellRowsBP δF z big cells mv mx mx1 pt j) 0) ≠ 0)
    (hx1 : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (cellRowsBP δF z big cells mv mx mx1 pt j) 1) ≠ 0)
    (hV : ∑ k ∈ Finset.range n, vTermOf δF (cellFillInv δF γ ρ (cellRowsBP δF z big cells mv mx mx1 pt k)) =
      Quad.mk _ (pubs 0) (pubs 1))
    (hX : ∑ k ∈ Finset.range n, xTermOf δF (cellFillInv δF γ ρ (cellRowsBP δF z big cells mv mx mx1 pt k)) =
      Quad.mk _ (pubs 2) (pubs 3))
    (hpole : ∀ i, CellTraceHQ.dRow δF b hn nodes orbit chals pubs
      (cellCol δF b (valsBP δF γ ρ z big cells mv mx mx1 pt)) mhv i ≠ 0)
    (hpub : Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (CellTraceH.mN mhv j) *
        (CellTraceHQ.dN δF b hn nodes orbit chals pubs (cellCol δF b (valsBP δF γ ρ z big cells mv mx mx1 pt))
          mhv j)⁻¹) :
    (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies
      (CellTraceHQ.cellTraceHQ δF b hn nodes orbit chals pubs (cellCol δF b (valsBP δF γ ρ z big cells mv mx mx1 pt))
        mhv) :=
  CellTraceHQ.cellChipHQ_accepts_honest δF b hn nodes orbit chals pubs _ mhv hinj hadj
    (cellChip_honest_listP δF b hn nodes orbit chals pubs γ ρ z big cells mv mx mx1 pt hcell hrank hN hinj hadj
      hok hzc hz hv hl hr hx0 hx1 hV hX) hpole hpub

/-- The preprocessing of the honest pointer trace (both masks). -/
theorem cellChip_honest_list_bindP (γ ρ z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun)
    (mv mx mx1 : ℕ → ℕ) (pt : Noun → ℕ) :
    (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing
      (honestQ hn nodes (cellCol δF b (valsBP δF γ ρ z big cells mv mx mx1 pt)) _) := by
  intro j
  fin_cases j
  · exact honestQ_zero hn nodes _ (by rw [(cellChip_fingerprint δF b hn nodes orbit chals pubs).1]; omega)
  · exact honestQ_one hn nodes _ (by rw [(cellChip_fingerprint δF b hn nodes orbit chals pubs).1]; omega)

end AcceptP

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Cell
