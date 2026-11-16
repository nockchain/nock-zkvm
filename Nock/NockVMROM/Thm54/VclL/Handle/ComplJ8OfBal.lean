/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8OfBal.lean

* §1 the serial LogUp identity (`sum_serial`): a sum over consumers of a per-serial term is the
    count-weighted sum over serials.
  * §2 cell-table rows (`cellRowsB`, any noun list, any big-atom map): a child cell's validity consumer key is the
    validity provider key of the row at the child's serial (`lTerm_cell`, `rTerm_cell`).
  * §3 the atom table's validity terminal is zero (`avT_zero_of`; at the run `balV3_run`, the third clause of
    `balV`, at every coin).
  * §4 tables under a key map (`mapTab`); the J chip's two publics as table totals at the run (`h3J_run` over
    `fS`, `h1J_run` over the handle-coin denominator `fH`): the J coins are the handle coins (`coinsJ_eq`,
    `coinsJX_eq`).
  * §5–6 the executable walk against the spec walk; `balF`'s cell / walk clause (`balF1_run`).

  * §8 `balV`'s atom handle clause: the atom cell handle key of a two-small-atom row (`aHx_two`), the atom-walk
    handle import as the `mhA`-weighted handle sum (`vhX_eq`), and `balV2_of_inc` (clause 2 with the inc part `hI`
    carried).
  * §9 the atom inc terminal: the two-limb fold over the slow increments (`fold_two`), the old-key denominator read
    off the row (`dC_key`), `incT_run` (`hI` discharged), and `balV2_run`, clause 2 at the run with nothing carried.
  * §10 `balV`'s first clause: the cell validity terminal at the run (`cvT_run`: claim + pin provider terms minus
    the big-child terms, from `mv_eq_cnt`), the atom table's `mb` terminal (`mbT_run`, from `mb_eq_cnt`), the
    big-atom key identity (`big_key`: `zAt = zJ`, `zA = zY`, the two-limb comb leaf `leafVal`), the claim / pin
    record sums (`claim_sum`, `pin_sum`), `balV1_run`, and **`balV_closed`**, `balV` at the run with nothing
    carried.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8BigBound
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Enc

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)

noncomputable section

/-! ## 1. The serial LogUp identity -/

section Serial
variable {ι R : Type} [CommRing R]

/-- **Consumers by serial**: `Σ_{x ∈ C} g (idx x) = Σ_{j < n} #{x ∈ C | idx x = j} · g j` when every serial is `< n`. -/
theorem sum_serial (n : ℕ) (idx : ι → ℕ) (g : ℕ → R) : ∀ C : List ι, (∀ x ∈ C, idx x < n) →
    (C.map fun x => g (idx x)).sum = ∑ j ∈ Finset.range n, ((C.filter fun x => idx x = j).length : R) * g j
  | [], _ => by simp
  | x :: C, h => by
    rw [List.map_cons, List.sum_cons, sum_serial n idx g C (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    have hx : idx x ∈ Finset.range n := Finset.mem_range.mpr (h x List.mem_cons_self)
    have hc : ∀ j, ((List.filter (fun y => decide (idx y = j)) (x :: C)).length : R) =
        (if idx x = j then 1 else 0) + ((List.filter (fun y => decide (idx y = j)) C).length : R) := by
      intro j
      by_cases hj : idx x = j
      · simp [List.filter_cons, hj]; ring
      · simp [List.filter_cons, hj]
    simp only [hc, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq _ _ _, if_pos hx]

end Serial

/-! ## 2. Cell-table rows: child consumer keys are provider keys -/

section Rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The validity inverse `1 / compress(vKey)` of cell row `j`. -/
abbrev vG (γ ρ z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ) (j : ℕ) : 𝕂′ :=
  (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (ComplJ8Cell.cellRowsB δF z big cells mv mx mx1 j)))⁻¹

theorem getD_idxOf (cells : List Noun) (c : Noun) (hc : c ∈ cells) : cells.getD (cells.idxOf c) (.atom 0) = c := by
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hc)]
  exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hc)

theorem rowsB_eq (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ) (k : ℕ) {y : Noun}
    (hy : cells.getD k (.atom 0) = y) :
    ComplJ8Cell.cellRowsB δF z big cells mv mx mx1 k = ComplJ8Cell.cellRowB δF z big cells mv mx mx1 y k := by
  rw [← hy]; rfl

/-- **A left child cell's consumer term is the provider term of its row.** -/
theorem lTerm_cell (γ ρ z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ) (k : ℕ)
    {y : Noun} (hy : cells.getD k (.atom 0) = y) (hc : hdN y ∈ cells) (hcell : (hdN y).isCell = true) :
    liftQ δF (ComplJ8Cell.cellRowsB δF z big cells mv mx mx1 k).wL *
        (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (lKeyOf δF (ComplJ8Cell.cellRowsB δF z big cells mv mx mx1 k)))⁻¹ =
      vG δF γ ρ z big cells mv mx mx1 (cells.idxOf (hdN y)) := by
  have hj := getD_idxOf cells _ hc
  unfold vG
  rw [rowsB_eq δF z big cells mv mx mx1 k hy, rowsB_eq δF z big cells mv mx mx1 _ hj]
  have hk : lKeyOf δF (ComplJ8Cell.cellRowB δF z big cells mv mx mx1 y k) =
      vKeyOf δF (ComplJ8Cell.cellRowB δF z big cells mv mx mx1 (hdN y) (cells.idxOf (hdN y))) := by
    funext i
    fin_cases i <;>
      simp [lKeyOf, vKeyOf, ComplJ8Cell.cellRowB, cellRow0, ComplJ8Cell.idOf, hcell]
  have hw : (ComplJ8Cell.cellRowB δF z big cells mv mx mx1 y k).wL = 1 := by
    simp [ComplJ8Cell.cellRowB, ComplJ8Cell.wOf, hcell]
  rw [hk, hw]; simp [liftQ]

/-- **A right child cell's consumer term is the provider term of its row.** -/
theorem rTerm_cell (γ ρ z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ) (k : ℕ)
    {y : Noun} (hy : cells.getD k (.atom 0) = y) (hc : tlN y ∈ cells) (hcell : (tlN y).isCell = true) :
    liftQ δF (ComplJ8Cell.cellRowsB δF z big cells mv mx mx1 k).wR *
        (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (rKeyOf δF (ComplJ8Cell.cellRowsB δF z big cells mv mx mx1 k)))⁻¹ =
      vG δF γ ρ z big cells mv mx mx1 (cells.idxOf (tlN y)) := by
  have hj := getD_idxOf cells _ hc
  unfold vG
  rw [rowsB_eq δF z big cells mv mx mx1 k hy, rowsB_eq δF z big cells mv mx mx1 _ hj]
  have hk : rKeyOf δF (ComplJ8Cell.cellRowB δF z big cells mv mx mx1 y k) =
      vKeyOf δF (ComplJ8Cell.cellRowB δF z big cells mv mx mx1 (tlN y) (cells.idxOf (tlN y))) := by
    funext i
    fin_cases i <;>
      simp [rKeyOf, vKeyOf, ComplJ8Cell.cellRowB, cellRow0, ComplJ8Cell.idOf, hcell]
  have hw : (ComplJ8Cell.cellRowB δF z big cells mv mx mx1 y k).wR = 1 := by
    simp [ComplJ8Cell.cellRowB, ComplJ8Cell.wOf, hcell]
  rw [hk, hw]; simp [liftQ]

/-- An atom child (not big) contributes nothing. -/
theorem lTerm_atom (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ) (k : ℕ)
    {y : Noun} (hy : cells.getD k (.atom 0) = y) (hcell : (hdN y).isCell = false)
    (hb : ComplJ8Cell.isBig big (hdN y) = false) :
    liftQ (K := K) δF (ComplJ8Cell.cellRowsB δF z big cells mv mx mx1 k).wL = 0 := by
  rw [rowsB_eq δF z big cells mv mx mx1 k hy]
  simp [ComplJ8Cell.cellRowB, ComplJ8Cell.wOf, hcell, hb, liftQ]

theorem rTerm_atom (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ) (k : ℕ)
    {y : Noun} (hy : cells.getD k (.atom 0) = y) (hcell : (tlN y).isCell = false)
    (hb : ComplJ8Cell.isBig big (tlN y) = false) :
    liftQ (K := K) δF (ComplJ8Cell.cellRowsB δF z big cells mv mx mx1 k).wR = 0 := by
  rw [rowsB_eq δF z big cells mv mx mx1 k hy]
  simp [ComplJ8Cell.cellRowB, ComplJ8Cell.wOf, hcell, hb, liftQ]


theorem sum_map_ite {R : Type} [AddCommMonoid R] (P : Noun → Bool) (g : Noun → R) : ∀ C : List Noun,
    (C.map fun y => if P y = true then g y else 0).sum = ((C.filter P).map g).sum
  | [] => rfl
  | c :: cs => by
    by_cases h : P c = true
    · simp [h, List.filter_cons, sum_map_ite P g cs]
    · simp [h, List.filter_cons, sum_map_ite P g cs]

/-- A sum over the row range of a function of the row noun is the list sum. -/
theorem sum_range_getD {R : Type} [AddCommMonoid R] (f : Noun → R) : ∀ cells : List Noun,
    ∑ k ∈ Finset.range cells.length, f (cells.getD k (.atom 0)) = (cells.map f).sum
  | [] => by simp
  | c :: cs => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    congr 1
    exact sum_range_getD f cs

/-- **The validity terminal of a closed cell list with no big children is zero**: the provider multiplicity of
row `j` is the number of child references at serial `j`, and every cell child is in the list. -/
theorem vSum_zero (γ ρ z : 𝕂′) (cells : List Noun) (mv mx mx1 : ℕ → ℕ)
    (hcl : ∀ y ∈ cells, ((hdN y).isCell = true → hdN y ∈ cells) ∧ ((tlN y).isCell = true → tlN y ∈ cells))
    (hmv : ∀ j < cells.length, (mv j : ℕ) =
      (cells.filter fun y => (hdN y).isCell && decide (cells.idxOf (hdN y) = j)).length +
      (cells.filter fun y => (tlN y).isCell && decide (cells.idxOf (tlN y) = j)).length) :
    ∑ k ∈ Finset.range cells.length,
      vTermOf δF (cellFillInv δF γ ρ (ComplJ8Cell.cellRowsB δF z (fun _ => none) cells mv mx mx1 k)) = 0 := by
  set G := vG δF γ ρ z (fun _ => none) cells mv mx mx1 with hG
  set n := cells.length
  let Lf : Noun → 𝕂′ := fun y => if (hdN y).isCell then G (cells.idxOf (hdN y)) else 0
  let Rf : Noun → 𝕂′ := fun y => if (tlN y).isCell then G (cells.idxOf (tlN y)) else 0
  have hrow : ∀ k ∈ Finset.range n,
      vTermOf δF (cellFillInv δF γ ρ (ComplJ8Cell.cellRowsB δF z (fun _ => none) cells mv mx mx1 k)) =
        liftQ δF ((mv k : ℕ) : F) * G k - Lf (cells.getD k (.atom 0)) - Rf (cells.getD k (.atom 0)) := by
    intro k hk
    have hy : cells.getD k (.atom 0) = cells.getD k (.atom 0) := rfl
    have hmem : cells.getD k (.atom 0) ∈ cells := by
      rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hk)]; exact List.getElem_mem _
    have hL : liftQ δF (ComplJ8Cell.cellRowsB δF z (fun _ => none) cells mv mx mx1 k).wL *
        (FiniteIO.compress (m := 5) ⟨γ, ρ⟩
          (lKeyOf δF (ComplJ8Cell.cellRowsB δF z (fun _ => none) cells mv mx mx1 k)))⁻¹ =
        Lf (cells.getD k (.atom 0)) := by
      by_cases hc : (hdN (cells.getD k (.atom 0))).isCell = true
      · simp only [Lf, hc, if_true]
        exact lTerm_cell δF γ ρ z _ cells mv mx mx1 k hy ((hcl _ hmem).1 hc) hc
      · have hc' : (hdN (cells.getD k (.atom 0))).isCell = false := by simpa using hc
        simp only [Lf, hc', if_false, Bool.false_eq_true]
        rw [lTerm_atom δF z _ cells mv mx mx1 k hy hc' (by simp [ComplJ8Cell.isBig]), zero_mul]
    have hR : liftQ δF (ComplJ8Cell.cellRowsB δF z (fun _ => none) cells mv mx mx1 k).wR *
        (FiniteIO.compress (m := 5) ⟨γ, ρ⟩
          (rKeyOf δF (ComplJ8Cell.cellRowsB δF z (fun _ => none) cells mv mx mx1 k)))⁻¹ =
        Rf (cells.getD k (.atom 0)) := by
      by_cases hc : (tlN (cells.getD k (.atom 0))).isCell = true
      · simp only [Rf, hc, if_true]
        exact rTerm_cell δF γ ρ z _ cells mv mx mx1 k hy ((hcl _ hmem).2 hc) hc
      · have hc' : (tlN (cells.getD k (.atom 0))).isCell = false := by simpa using hc
        simp only [Rf, hc', if_false, Bool.false_eq_true]
        rw [rTerm_atom δF z _ cells mv mx mx1 k hy hc' (by simp [ComplJ8Cell.isBig]), zero_mul]
    rw [← hL, ← hR]
    rfl
  rw [Finset.sum_congr rfl hrow, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_range_getD Lf cells, sum_range_getD Rf cells]
  -- consumers by serial
  have hlt : ∀ (sel : Noun → Noun), (∀ y ∈ cells, (sel y).isCell = true → sel y ∈ cells) →
      ∀ y ∈ cells.filter (fun y => (sel y).isCell), cells.idxOf (sel y) < n := by
    intro sel hs y hy
    obtain ⟨hy, hc⟩ := List.mem_filter.mp hy
    exact List.idxOf_lt_length_of_mem (hs y hy hc)
  have hLs := sum_serial n (fun y => cells.idxOf (hdN y)) G _ (hlt hdN fun y hy => (hcl y hy).1)
  have hRs := sum_serial n (fun y => cells.idxOf (tlN y)) G _ (hlt tlN fun y hy => (hcl y hy).2)
  rw [sum_map_ite, sum_map_ite, hLs, hRs, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hf : ∀ sel : Noun → Noun,
      (cells.filter fun a => decide (cells.idxOf (sel a) = j) && (sel a).isCell) =
        cells.filter fun a => (sel a).isCell && decide (cells.idxOf (sel a) = j) := by
    intro sel; congr 1; funext a; exact Bool.and_comm _ _
  rw [hmv j (Finset.mem_range.mp hj), List.filter_filter, List.filter_filter, hf hdN, hf tlN]
  simp only [liftQ, Nat.cast_add, map_add, map_natCast]
  ring

/-! ### Pointer rows (J-9 B one pointer): the right child is consumed at `pt y`, any copy of `tlN y` -/

/-- **A right child cell's consumer term at a pointer `pt` is the provider term of row `pt y`**, when that row
holds `tlN y`. -/
theorem rTerm_cellP (γ ρ z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 : ℕ → ℕ)
    (pt : Noun → ℕ) (k : ℕ) {y : Noun} (hy : cells.getD k (.atom 0) = y)
    (hpt : cells.getD (pt y) (.atom 0) = tlN y) (hcell : (tlN y).isCell = true) :
    liftQ δF (ComplJ8Cell.cellRowsBP δF z big cells mv mx mx1 pt k).wR *
        (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (rKeyOf δF (ComplJ8Cell.cellRowsBP δF z big cells mv mx mx1 pt k)))⁻¹ =
      vG δF γ ρ z big cells mv mx mx1 (pt y) := by
  unfold vG
  rw [rowsB_eq δF z big cells mv mx mx1 _ hpt]
  have e : ComplJ8Cell.cellRowsBP δF z big cells mv mx mx1 pt k =
      ComplJ8Cell.cellRowBP δF z big cells mv mx mx1 pt y k := by rw [← hy]; rfl
  rw [e]
  have hk : rKeyOf δF (ComplJ8Cell.cellRowBP δF z big cells mv mx mx1 pt y k) =
      vKeyOf δF (ComplJ8Cell.cellRowB δF z big cells mv mx mx1 (tlN y) (pt y)) := by
    funext i
    fin_cases i <;>
      simp [rKeyOf, vKeyOf, ComplJ8Cell.cellRowBP, ComplJ8Cell.cellRowB, cellRow0, ComplJ8Cell.idRP, hcell]
  have hw : (ComplJ8Cell.cellRowBP δF z big cells mv mx mx1 pt y k).wR = 1 := by
    simp [ComplJ8Cell.cellRowBP, ComplJ8Cell.cellRowB, ComplJ8Cell.wOf, hcell]
  rw [hk, hw]; simp [liftQ]

/-- **`vSum_zero` at the pointer rows**: the validity terminal of a closed cell list with no big children is zero
when every right child is consumed at a row `pt y` holding it and `mv` counts the right children at `pt`. -/
theorem vSum_zeroP (γ ρ z : 𝕂′) (cells : List Noun) (mv mx mx1 : ℕ → ℕ) (pt : Noun → ℕ)
    (hcl : ∀ y ∈ cells, ((hdN y).isCell = true → hdN y ∈ cells) ∧ ((tlN y).isCell = true → tlN y ∈ cells))
    (hpt : ∀ y ∈ cells, (tlN y).isCell = true → pt y < cells.length ∧ cells.getD (pt y) (.atom 0) = tlN y)
    (hmv : ∀ j < cells.length, (mv j : ℕ) =
      (cells.filter fun y => (hdN y).isCell && decide (cells.idxOf (hdN y) = j)).length +
      (cells.filter fun y => (tlN y).isCell && decide (pt y = j)).length) :
    ∑ k ∈ Finset.range cells.length,
      vTermOf δF (cellFillInv δF γ ρ (ComplJ8Cell.cellRowsBP δF z (fun _ => none) cells mv mx mx1 pt k)) = 0 := by
  set G := vG δF γ ρ z (fun _ => none) cells mv mx mx1 with hG
  set n := cells.length
  let Lf : Noun → 𝕂′ := fun y => if (hdN y).isCell then G (cells.idxOf (hdN y)) else 0
  let Rf : Noun → 𝕂′ := fun y => if (tlN y).isCell then G (pt y) else 0
  have hrow : ∀ k ∈ Finset.range n,
      vTermOf δF (cellFillInv δF γ ρ (ComplJ8Cell.cellRowsBP δF z (fun _ => none) cells mv mx mx1 pt k)) =
        liftQ δF ((mv k : ℕ) : F) * G k - Lf (cells.getD k (.atom 0)) - Rf (cells.getD k (.atom 0)) := by
    intro k hk
    have hy : cells.getD k (.atom 0) = cells.getD k (.atom 0) := rfl
    have hmem : cells.getD k (.atom 0) ∈ cells := by
      rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hk)]; exact List.getElem_mem _
    have hL : liftQ δF (ComplJ8Cell.cellRowsBP δF z (fun _ => none) cells mv mx mx1 pt k).wL *
        (FiniteIO.compress (m := 5) ⟨γ, ρ⟩
          (lKeyOf δF (ComplJ8Cell.cellRowsBP δF z (fun _ => none) cells mv mx mx1 pt k)))⁻¹ =
        Lf (cells.getD k (.atom 0)) := by
      by_cases hc : (hdN (cells.getD k (.atom 0))).isCell = true
      · simp only [Lf, hc, if_true]
        exact lTerm_cell δF γ ρ z _ cells mv mx mx1 k hy ((hcl _ hmem).1 hc) hc
      · have hc' : (hdN (cells.getD k (.atom 0))).isCell = false := by simpa using hc
        simp only [Lf, hc', if_false, Bool.false_eq_true]
        rw [show liftQ (K := K) δF (ComplJ8Cell.cellRowsBP δF z (fun _ => none) cells mv mx mx1 pt k).wL = 0 from
          lTerm_atom δF z _ cells mv mx mx1 k hy hc' (by simp [ComplJ8Cell.isBig]), zero_mul]
    have hR : liftQ δF (ComplJ8Cell.cellRowsBP δF z (fun _ => none) cells mv mx mx1 pt k).wR *
        (FiniteIO.compress (m := 5) ⟨γ, ρ⟩
          (rKeyOf δF (ComplJ8Cell.cellRowsBP δF z (fun _ => none) cells mv mx mx1 pt k)))⁻¹ =
        Rf (cells.getD k (.atom 0)) := by
      by_cases hc : (tlN (cells.getD k (.atom 0))).isCell = true
      · simp only [Rf, hc, if_true]
        exact rTerm_cellP δF γ ρ z _ cells mv mx mx1 pt k hy (hpt _ hmem hc).2 hc
      · have hc' : (tlN (cells.getD k (.atom 0))).isCell = false := by simpa using hc
        simp only [Rf, hc', if_false, Bool.false_eq_true]
        rw [show liftQ (K := K) δF (ComplJ8Cell.cellRowsBP δF z (fun _ => none) cells mv mx mx1 pt k).wR = 0 from
          rTerm_atom δF z _ cells mv mx mx1 k hy hc' (by simp [ComplJ8Cell.isBig]), zero_mul]
    rw [← hL, ← hR]
    rfl
  rw [Finset.sum_congr rfl hrow, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_range_getD Lf cells, sum_range_getD Rf cells]
  have hltL : ∀ y ∈ cells.filter (fun y => (hdN y).isCell), cells.idxOf (hdN y) < n := by
    intro y hy
    obtain ⟨hy, hc⟩ := List.mem_filter.mp hy
    exact List.idxOf_lt_length_of_mem ((hcl y hy).1 hc)
  have hltR : ∀ y ∈ cells.filter (fun y => (tlN y).isCell), pt y < n := by
    intro y hy
    obtain ⟨hy, hc⟩ := List.mem_filter.mp hy
    exact (hpt y hy hc).1
  have hLs := sum_serial n (fun y => cells.idxOf (hdN y)) G _ hltL
  have hRs := sum_serial n pt G _ hltR
  rw [sum_map_ite, sum_map_ite, hLs, hRs, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hfL : (cells.filter fun a => decide (cells.idxOf (hdN a) = j) && (hdN a).isCell) =
      cells.filter fun a => (hdN a).isCell && decide (cells.idxOf (hdN a) = j) := by
    congr 1; funext a; exact Bool.and_comm _ _
  have hfR : (cells.filter fun a => decide (pt a = j) && (tlN a).isCell) =
      cells.filter fun a => (tlN a).isCell && decide (pt a = j) := by
    congr 1; funext a; exact Bool.and_comm _ _
  rw [hmv j (Finset.mem_range.mp hj), List.filter_filter, List.filter_filter, hfL, hfR]
  simp only [liftQ, Nat.cast_add, map_add, map_natCast]
  ring

end Rows

/-! ## 3. The atom table's validity terminal is zero -/

section AtomV
open Nock.V1J8.Gen (idxD hdN' tlN')
open Nock.Atoms (limbs)

theorem idxOf_eq_idxD : ∀ (cs : List Noun) (x : Noun), cs.idxOf x = idxD cs x
  | [], _ => rfl
  | c :: cs, x => by
    rw [List.idxOf_cons, idxD, idxOf_eq_idxD cs x]
    by_cases h : c = x
    · simp [h]
    · have h' : (c == x) = false := by simpa using h
      simp [h, h']

theorem genIdxOf_eq (cs : List Noun) (x : Noun) (h : x ∈ cs) : Nock.V1J8.Gen.idxOf cs x = cs.idxOf x := by
  rw [idxOf_eq_idxD]; simp [Nock.V1J8.Gen.idxOf, h]

theorem hdN_eq (n : Noun) : hdN n = hdN' n := by cases n <;> rfl
theorem tlN_eq (n : Noun) : tlN n = tlN' n := by cases n <;> rfl

/-- **The atom cell list is closed under cell children** (heads are limbs; a long spine's tail is the next spine
cell). -/
theorem acsP_closed (bigs : List ℕ) (dupP : Bool) (hbigs : ∀ a ∈ bigs, Nock.Atoms.p ≤ a) :
    ∀ y ∈ ComplJ8Data.acsP Nock.Atoms.p bigs dupP,
      ((hdN y).isCell = true → hdN y ∈ ComplJ8Data.acsP Nock.Atoms.p bigs dupP) ∧
      ((tlN y).isCell = true → tlN y ∈ ComplJ8Data.acsP Nock.Atoms.p bigs dupP) := by
  intro y hy
  obtain ⟨l, h2, -, rfl, h3⟩ := ComplJ8Atom.shape_acsP bigs dupP hbigs y hy
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [hdN_eq, ComplJ8Atom.hd_combOf l h2] at hc; simp [Noun.isCell] at hc
  · rw [tlN_eq, ComplJ8Atom.tl_combOf l h2] at hc ⊢
    by_cases hl : 3 ≤ l.length
    · rw [if_pos hl]
      obtain ⟨-, a, ha, d, rfl⟩ := h3 hl
      refine (ComplJ8Atom.mem_acsP bigs dupP _).mpr (Or.inl ((ComplJ8Atom.mem_spineL bigs _).mpr
        ⟨a, ha, (ComplJ8Atom.mem_spineOf _ _).mpr ⟨d + 1, ?_, ?_⟩⟩))
      · simp only [List.length_drop] at hl ⊢; omega
      · rw [List.tail_drop]
    · rw [if_neg hl] at hc; simp [Noun.isCell] at hc

end AtomV

section AtomRun
open Nock.V1J8.Gen (idxD hdN' tlN')
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- **The one pointer lands on a copy of the tail** (any `J8Data`, closed list): `ptrP p acs rows y` is a row of
`acs` holding `tlN y` (the first copy, or the last copy of `comb p`). -/
theorem ptrP_getD (D : J8Data p Rg fuel s f r)
    (hcl : ∀ y ∈ D.acs, ((hdN y).isCell = true → hdN y ∈ D.acs) ∧ ((tlN y).isCell = true → tlN y ∈ D.acs)) :
    ∀ y ∈ D.acs, (tlN y).isCell = true →
      ComplJ8Data.ptrP p D.acs D.rows y < D.acs.length ∧
        D.acs.getD (ComplJ8Data.ptrP p D.acs D.rows y) (.atom 0) = tlN y := by
  intro y hy hc
  have hm := (hcl y hy).2 hc
  unfold ComplJ8Data.ptrP
  split_ifs with h
  · have hm' : ComplJ8Data.combPP p ∈ D.acs := by rw [← h.1, ← tlN_eq]; exact hm
    have e := ComplJ8Atom.lastIdxOf_mem D.acs _ hm'
    obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp e
    refine ⟨hlt, ?_⟩
    rw [List.getD_eq_getElem _ _ hlt, he, ← h.1, tlN_eq]
  · rw [← tlN_eq, genIdxOf_eq _ _ hm]
    exact ⟨List.idxOf_lt_length_of_mem hm, getD_idxOf _ _ hm⟩

/-- The atom validity multiplicity in the `List.idxOf` / pointer form, on a closed list. -/
theorem mvA_eq (D : J8Data p Rg fuel s f r)
    (hcl : ∀ y ∈ D.acs, ((hdN y).isCell = true → hdN y ∈ D.acs) ∧ ((tlN y).isCell = true → tlN y ∈ D.acs))
    (j : ℕ) : mvA D j =
      (D.acs.filter fun y => (hdN y).isCell && decide (D.acs.idxOf (hdN y) = j)).length +
      (D.acs.filter fun y => (tlN y).isCell && decide (ComplJ8Data.ptrP p D.acs D.rows y = j)).length := by
  unfold mvA
  congr 2
  · refine List.filter_congr fun y hy => ?_
    rw [← hdN_eq]
    by_cases hc : (hdN y).isCell = true
    · rw [genIdxOf_eq _ _ ((hcl y hy).1 hc)]
      by_cases h2 : D.acs.idxOf (hdN y) = j <;> simp [hc, h2]
    · simp [hc]

/-- **The atom validity terminal is zero** on a closed atom cell list (right children at the one pointer). -/
theorem avT_zero_of (D : J8Data p Rg fuel s f r)
    (hcl : ∀ y ∈ D.acs, ((hdN y).isCell = true → hdN y ∈ D.acs) ∧ ((tlN y).isCell = true → tlN y ∈ D.acs))
    (χ : Coins frameJ8 K) : avT δ D χ = 0 := by
  unfold avT
  exact vSum_zeroP (K := K) δ (γV δ χ) (ρV δ χ) (zA δ χ) D.acs (mvA D) (mxAF D) (fun _ => 0) (ptA D) hcl
    (ptrP_getD D hcl) fun j _ => mvA_eq D hcl j

end AtomRun

section AtomRunJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.Edit Nock.Edit.GenX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **The run's atom cell list is closed under cell children** (Goldilocks). -/
theorem acs_closed_run (hpG : p = Nock.Atoms.p) :
    ∀ y ∈ (j8DataOf p Rg Rt hgen).acs, ((hdN y).isCell = true → hdN y ∈ (j8DataOf p Rg Rt hgen).acs) ∧
      ((tlN y).isCell = true → tlN y ∈ (j8DataOf p Rg Rt hgen).acs) := by
  subst hpG
  exact acsP_closed _ _ fun a ha => ((ComplJ8Atom.mem_bigsP _ _ _ a).mp ha).2

/-- **`balV`'s third clause at the run**: the atom table's validity publics are zero (at every coin). -/
theorem balV3_run (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) :
    ((BRun δ b Rt hgen hpG h31).M χ).pubsA 0 = 0 ∧ ((BRun δ b Rt hgen hpG h31).M χ).pubsA 1 = 0 := by
  have h0 := avT_zero_of δ (j8DataOf p Rg Rt hgen) (acs_closed_run Rt hgen hpG) χ
  have hz : (0 : Quad (algebraMap (ZMod p) K δ)) = Quad.mk _ 0 0 :=
    ((Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩).symm
  refine ⟨?_, ?_⟩
  · show pubsAOf δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ 0 = 0
    simp [pubsAOf, pubsA1, pubsA0, pub2, h0, hz, Quad.re_mk, Quad.im_mk]
  · show pubsAOf δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ 1 = 0
    simp [pubsAOf, pubsA1, pubsA0, pub2, h0, hz, Quad.re_mk, Quad.im_mk]

end AtomRunJ8

/-! ## 4. Tables under a key map; the J chip's publics as table totals -/

section MapTab
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bal (Tab tot)
variable {α β R : Type} [CommRing R]

/-- A table with its keys re-encoded. -/
def mapTab (e : α → β) (T : Tab α R) : Tab β R := ⟨T.cons.map e, T.prov.map fun q => (e q.1, q.2)⟩

theorem tot_mapTab (f : β → R) (e : α → β) (T : Tab α R) : tot f (mapTab e T) = tot (f ∘ e) T := by
  simp [tot, mapTab, List.map_map, Function.comp_def]

end MapTab

section JRun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bal (Tab tot tots tabOfRows tot_tabOfRows_fin fS)
open Nock.Jet.RapJetJ8 (dJX dJ coinsJ coinsJX consKT keyK)
open Nock.Jet.ChipJ8T.HonestRAP (termJ sX)
open Nock.NockVMROM.Thm54.FiniteIO (compress)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Edit Nock.Edit.GenX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The J tagged coins are the handle coins `(γH, ρH)`. -/
theorem coinsJ_eq (χ : Coins frameJ8 K) : coinsJ δ (chalsJJ8 χ) = coinsCV b δ (chalVJ8 b χ) := by
  rw [coinsCV_J8]
  simp [coinsJ, chalsJJ8, gamHQ, rhoHQ, cGamHi, cRhoHi]

/-- The J export coins are the handle coins `(γH, ρH)`. -/
theorem coinsJX_eq (χ : Coins frameJ8 K) : coinsJX δ (chalsJJ8 χ) = coinsCV b δ (chalVJ8 b χ) := by
  rw [coinsCV_J8]
  simp [coinsJX, chalsJJ8, gamHQ, rhoHQ, cGamHi, cRhoHi]

/-- The handle-coin denominator of a `5`-record (the export balance's `f`). -/
abbrev fH (χ : Coins frameJ8 K) (x : Fin 5 → K) : 𝕂′ := (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹

theorem dJ_eq (χ : Coins frameJ8 K) : dJ δ (chalsJJ8 χ) = fS δ b χ ∘ keyK 8 := by
  funext κ; simp only [dJ, Function.comp_apply, fS, coinsJ_eq δ b χ]

theorem dJX_eq (χ : Coins frameJ8 K) : dJX δ (chalsJJ8 χ) = fH δ b χ ∘ keyK 5 := by
  funext κ; simp only [dJX, Function.comp_apply, fH, coinsJX_eq δ b χ]

/-- The J service table of the run (consumers `consKT`, providers `provJ`), keys as `8`-records. -/
def tabJS (D : J8Data p Rg fuel s f r) : Tab (Fin 8 → K) 𝕂′ :=
  mapTab (keyK 8) (tabOfRows (List.ofFn D.jrows.get) consKT (ComplJ8Jet.provJ δ))

/-- The J export table of the run (consumers only), keys as `5`-records. -/
def tabJX (D : J8Data p Rg fuel s f r) : Tab (Fin 5 → K) 𝕂′ :=
  mapTab (keyK 5) (tabOfRows (List.ofFn D.jrows.get) (Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.entsX)
    (fun _ => ([] : List (List (ZMod p) × 𝕂′))))

/-- **`h3J`: the J terminal public is the J service table's total** (at every coin). -/
theorem h3J_run (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) :
    Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 0) (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 1) =
      tots δ (fS δ b χ) [tabJS δ (j8DataOf p Rg Rt hgen)] := by
  show Quad.mk _ (pubsJOf δ (j8DataOf p Rg Rt hgen) χ 0) (pubsJOf δ (j8DataOf p Rg Rt hgen) χ 1) = _
  have e0 : pubsJOf δ (j8DataOf p Rg Rt hgen) χ 0 = pub2 δ (∑ k, termJ δ (chalsJJ8 χ) ((j8DataOf p Rg Rt hgen).jrows.get k)) 0 := by
    simp [pubsJOf]
  have e1 : pubsJOf δ (j8DataOf p Rg Rt hgen) χ 1 = pub2 δ (∑ k, termJ δ (chalsJJ8 χ) ((j8DataOf p Rg Rt hgen).jrows.get k)) 1 := by
    simp [pubsJOf]
  rw [e0, e1, pub2_mk]
  simp only [tots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, tabJS, tot_mapTab, ← dJ_eq]
  rw [← tot_tabOfRows_fin]
  exact Finset.sum_congr rfl fun i _ => ComplJ8Jet.termJ_row_eq_tot δ _ _

/-- **`h1J`: the J export public is the J export table's total** (at every coin). -/
theorem h1J_run (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) :
    Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 2) (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 3) =
      tots δ (fH δ b χ) [tabJX δ (j8DataOf p Rg Rt hgen)] := by
  show Quad.mk _ (pubsJOf δ (j8DataOf p Rg Rt hgen) χ 2) (pubsJOf δ (j8DataOf p Rg Rt hgen) χ 3) = _
  have e0 : pubsJOf δ (j8DataOf p Rg Rt hgen) χ 2 = pub2 δ (∑ k, sX δ (chalsJJ8 χ) ((j8DataOf p Rg Rt hgen).jrows.get k)) 2 := by
    simp [pubsJOf]
  have e1 : pubsJOf δ (j8DataOf p Rg Rt hgen) χ 3 = pub2 δ (∑ k, sX δ (chalsJJ8 χ) ((j8DataOf p Rg Rt hgen).jrows.get k)) 3 := by
    simp [pubsJOf]
  have h2 := pub2_mk2 δ (∑ k, sX δ (chalsJJ8 χ) ((j8DataOf p Rg Rt hgen).jrows.get k)) 2 rfl
  rw [show (2 : ℕ) + 1 = 3 from rfl] at h2
  rw [e0, e1, h2]
  simp only [tots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, tabJX, tot_mapTab, ← dJX_eq]
  have := tot_tabOfRows_fin (R := 𝕂′) (dJX δ (chalsJJ8 χ)) (j8DataOf p Rg Rt hgen).jrows.get
    (Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.entsX) (fun _ => ([] : List (List (ZMod p) × 𝕂′)))
  simp only [List.map_nil, List.sum_nil, sub_zero] at this
  rw [← this]
  rfl

end JRun

/-! ## 5. The executable walk rows against the spec walk rows

The honest walk traces are the SPEC rows `walkRows cells reads`; the cell table's multiplicities count the
EXECUTABLE rows `(walkGen …).1` (`bfsTN 70`).  On nodes the two agree up to order (`walkGen_nodes_perm`): the same
trie per root, the BFS at fuel `70 > 62 ≥` every target depth, the roots in first- vs last-occurrence order. -/

section WalkBridge
open Nock.NockVMROM.Thm54

/-- An executable trie node corresponds to a spec trie node, all remaining targets of length `≤ k`. -/
def CorrK (k : ℕ) (u : Nock.V1J8.Gen.TN) (t : NTree WN) : Prop :=
  ∃ (R n : Noun) (pre : ℕ) (bs : List Bool) (T : List (List Bool)),
    u = Nock.V1J8.Gen.trie R n pre bs.length T ∧ t = GenWalk.trie R n bs T ∧ ∀ s ∈ T, s.length ≤ k

theorem contT_eq (b : Bool) (T : List (List Bool)) : Nock.V1J8.Gen.contT b T = GenWalk.contT b T := rfl
theorem contB_eq (b : Bool) (T : List (List Bool)) : Nock.V1J8.Gen.contB b T = GenWalk.cont b T := rfl

theorem node_eq {k : ℕ} {u : Nock.V1J8.Gen.TN} {t : NTree WN} (h : CorrK k u t) :
    u.label.node = t.label.node := by
  obtain ⟨R, n, pre, bs, T, rfl, rfl, -⟩ := h
  cases n <;> rfl

theorem contT_nil_of_le0 (b : Bool) (T : List (List Bool)) (h : ∀ s ∈ T, s.length ≤ 0) :
    GenWalk.contT b T = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro s hs
  have := (mem_contT hs).1
  have := h _ this
  simp at this

theorem contT_le {k : ℕ} (b : Bool) (T : List (List Bool)) (h : ∀ s ∈ T, s.length ≤ k + 1) :
    ∀ s ∈ GenWalk.contT b T, s.length ≤ k := by
  intro s hs
  have := h _ (mem_contT hs).1
  simp at this; omega

theorem forall₂_append {α β : Type} {Rel : α → β → Prop} {a a' : List α} {c c' : List β}
    (h1 : List.Forall₂ Rel a c) (h2 : List.Forall₂ Rel a' c') : List.Forall₂ Rel (a ++ a') (c ++ c') := by
  induction h1 with
  | nil => simpa using h2
  | cons h _ ih => exact List.Forall₂.cons h ih

theorem kids_corr {k : ℕ} {u : Nock.V1J8.Gen.TN} {t : NTree WN} (h : CorrK (k + 1) u t) :
    List.Forall₂ (CorrK k) u.kids t.children := by
  obtain ⟨R, n, pre, bs, T, rfl, rfl, hT⟩ := h
  cases n with
  | atom a => exact List.Forall₂.nil
  | cell l r =>
    show List.Forall₂ (CorrK k)
      ((if Nock.V1J8.Gen.contB false T then [Nock.V1J8.Gen.trie R l (2 * pre) (bs.length + 1)
          (Nock.V1J8.Gen.contT false T)] else []) ++
       (if Nock.V1J8.Gen.contB true T then [Nock.V1J8.Gen.trie R r (2 * pre + 1) (bs.length + 1)
          (Nock.V1J8.Gen.contT true T)] else []))
      ((if cont false T then [GenWalk.trie R l (bs ++ [false]) (GenWalk.contT false T)] else []) ++
       (if cont true T then [GenWalk.trie R r (bs ++ [true]) (GenWalk.contT true T)] else []))
    rw [contB_eq, contB_eq, contT_eq, contT_eq]
    refine forall₂_append ?_ ?_
    · split_ifs
      · exact List.Forall₂.cons ⟨R, l, 2 * pre, bs ++ [false], _, by simp, rfl, contT_le false T hT⟩
          List.Forall₂.nil
      · exact List.Forall₂.nil
    · split_ifs
      · exact List.Forall₂.cons ⟨R, r, 2 * pre + 1, bs ++ [true], _, by simp, rfl, contT_le true T hT⟩
          List.Forall₂.nil
      · exact List.Forall₂.nil

theorem kids_nil0 {u : Nock.V1J8.Gen.TN} {t : NTree WN} (h : CorrK 0 u t) : u.kids = [] ∧ t.children = [] := by
  obtain ⟨R, n, pre, bs, T, rfl, rfl, hT⟩ := h
  cases n with
  | atom a => exact ⟨rfl, rfl⟩
  | cell l r =>
    have h0 := contT_nil_of_le0 false T hT
    have h1 := contT_nil_of_le0 true T hT
    have c0 : cont false T = false := by simp [cont, h0]
    have c1 : cont true T = false := by simp [cont, h1]
    refine ⟨?_, ?_⟩
    · show ((if Nock.V1J8.Gen.contB false T then _ else []) ++ (if Nock.V1J8.Gen.contB true T then _ else [])) = []
      rw [contB_eq, contB_eq, c0, c1]; rfl
    · show ((if cont false T then _ else []) ++ (if cont true T then _ else [])) = []
      rw [c0, c1]; rfl

theorem forall₂_flatMap {α β γ δ : Type} {Rel : α → β → Prop} {Rel' : γ → δ → Prop} {f : α → List γ}
    {g : β → List δ} (hfg : ∀ a b, Rel a b → List.Forall₂ Rel' (f a) (g b)) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ Rel l l' → List.Forall₂ Rel' (l.flatMap f) (l'.flatMap g)
  | _, _, .nil => List.Forall₂.nil
  | _, _, .cons h hs => by
    simp only [List.flatMap_cons]
    exact forall₂_append (hfg _ _ h) (forall₂_flatMap hfg hs)

theorem f2_left {α β : Type} {Rel : α → β → Prop} : ∀ {l : List α} {l' : List β}, List.Forall₂ Rel l l' →
    ∀ x ∈ l, ∃ y, Rel x y
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons hab hs, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, hab⟩
    · exact f2_left hs x h

theorem f2_right {α β : Type} {Rel : α → β → Prop} : ∀ {l : List α} {l' : List β}, List.Forall₂ Rel l l' →
    ∀ y ∈ l', ∃ x, Rel x y
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons hab hs, y, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, hab⟩
    · exact f2_right hs y h

theorem forall₂_map_node {k : ℕ} : ∀ {l : List Nock.V1J8.Gen.TN} {l' : List (NTree WN)},
    List.Forall₂ (CorrK k) l l' → (l.map fun u => u.label.node) = l'.map fun t => t.label.node
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp only [List.map_cons, node_eq h, forall₂_map_node hs]

/-- **The executable BFS is the spec BFS on nodes** once the fuel exceeds the target depth. -/
theorem bfsTN_node : ∀ (k m : ℕ), k + 1 ≤ m → ∀ (l : List Nock.V1J8.Gen.TN) (l' : List (NTree WN)),
    List.Forall₂ (CorrK k) l l' →
    ((Nock.V1J8.Gen.bfsTN m l).map Nock.V1J8.Gen.WRow.node) = (bfsForest l').map fun t => t.label.node
  | k, 0, hm, _, _, _ => by omega
  | k, m + 1, hm, [], l', h => by
    cases h; simp [Nock.V1J8.Gen.bfsTN, bfsForest]
  | k, m + 1, hm, u :: us, l', h => by
    cases h with
    | cons hu hus =>
      rename_i t ts
      rw [bfsForest]
      simp only [Nock.V1J8.Gen.bfsTN, List.map_append, List.map_map]
      have hnodes := forall₂_map_node (List.Forall₂.cons hu hus)
      have e1 : ((u :: us).map fun x => (Nock.V1J8.Gen.TN.label x).node) =
          (List.map (Nock.V1J8.Gen.WRow.node ∘ Nock.V1J8.Gen.TN.label) (u :: us)) := rfl
      rw [← e1, hnodes]
      congr 1
      cases k with
      | zero =>
        have hk : ((u :: us).flatMap Nock.V1J8.Gen.TN.kids) = [] := by
          rw [List.flatMap_eq_nil_iff]
          intro x hx
          obtain ⟨y, hy⟩ := f2_left (List.Forall₂.cons hu hus) x hx
          exact (kids_nil0 hy).1
        have hk' : ((t :: ts).flatMap NTree.children) = [] := by
          rw [List.flatMap_eq_nil_iff]
          intro x hx
          obtain ⟨y, hy⟩ := f2_right (List.Forall₂.cons hu hus) x hx
          exact (kids_nil0 hy).2
        rw [hk, hk']
        cases m <;> simp [Nock.V1J8.Gen.bfsTN, bfsForest]
      | succ k =>
        exact bfsTN_node k m (by omega) _ _
          (forall₂_flatMap (fun a b hab => kids_corr hab) (List.Forall₂.cons hu hus))

/-! ### The forest -/

theorem axisBits_go_eq : ∀ (f a : ℕ), Nock.V1J8.Gen.axisBits.go f a = VclL.axisBitsAux f a
  | 0, _ => rfl
  | f + 1, a => by
    simp only [Nock.V1J8.Gen.axisBits.go, VclL.axisBitsAux, axisBits_go_eq f (a / 2)]

theorem axisBits_eq (a : ℕ) : Nock.V1J8.Gen.axisBits a = VclL.axisBits a := axisBits_go_eq a a

theorem isPathAx_of_two_le {a : ℕ} (h : 2 ≤ a) : VclL.isPathAx a = true := by
  unfold VclL.isPathAx VclL.depthOf
  apply decide_eq_true
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  simp only [VclL.axisBits, VclL.axisBitsAux, if_pos h, List.length_append, List.length_singleton]
  omega

/-- The first-occurrence root fold of `groupReads`. -/
theorem rootsFold_spec : ∀ (l : List (Noun × ℕ)) (acc : List Noun), acc.Nodup →
    (l.foldl (fun acc p => if p.1 ∈ acc then acc else acc ++ [p.1]) acc).Nodup ∧
    ∀ x, x ∈ l.foldl (fun acc p => if p.1 ∈ acc then acc else acc ++ [p.1]) acc ↔ x ∈ acc ∨ x ∈ l.map Prod.fst
  | [], acc, h => ⟨h, fun x => by simp⟩
  | q :: l, acc, h => by
    simp only [List.foldl_cons]
    by_cases hq : q.1 ∈ acc
    · rw [if_pos hq]
      obtain ⟨h1, h2⟩ := rootsFold_spec l acc h
      refine ⟨h1, fun x => ?_⟩
      rw [h2]; simp only [List.map_cons, List.mem_cons]
      constructor
      · rintro (h | h) <;> simp [h]
      · rintro (h | rfl | h)
        · exact Or.inl h
        · exact Or.inl hq
        · exact Or.inr h
    · rw [if_neg hq]
      have hnd : (acc ++ [q.1]).Nodup := List.nodup_append.mpr ⟨h, List.nodup_singleton _, by
        intro a ha b hb hab; simp at hb; subst hb; subst hab; exact hq ha⟩
      obtain ⟨h1, h2⟩ := rootsFold_spec l _ hnd
      refine ⟨h1, fun x => ?_⟩
      rw [h2]; simp only [List.mem_append, List.mem_singleton, List.map_cons, List.mem_cons]
      tauto

theorem groupRoots_perm (rs : List (Noun × ℕ)) :
    (rs.foldl (fun acc p => if p.1 ∈ acc then acc else acc ++ [p.1]) []).Perm (rs.map Prod.fst).dedup := by
  obtain ⟨h1, h2⟩ := rootsFold_spec rs [] List.nodup_nil
  refine (List.perm_ext_iff_of_nodup h1 (List.nodup_dedup _)).mpr fun x => ?_
  rw [h2, List.mem_dedup]; simp

theorem pathKind_of_all {rs : List (Noun × ℕ)} (hall : ∀ x ∈ rs, VclL.isPathAx x.2 = true) :
    pathKind rs = rs := by
  unfold pathKind; exact List.filter_eq_self.mpr fun x hx => hall x hx

theorem targets_eq {rs : List (Noun × ℕ)} (hall : ∀ x ∈ rs, VclL.isPathAx x.2 = true) (r : Noun) :
    (rs.filter fun p => p.1 = r).map (fun p => Nock.V1J8.Gen.axisBits p.2) = targetsOf rs r := by
  unfold targetsOf; rw [pathKind_of_all hall]
  simp only [axisBits_eq]

theorem bfsForest_perm_of_perm {l l' : List (NTree WN)} (h : l.Perm l') : (bfsForest l).Perm (bfsForest l') :=
  ((bfsForest_perm_flatMap l).trans (h.flatMap_right _)).trans (bfsForest_perm_flatMap l').symm

/-- **The executable walk rows and the spec walk rows have the same nodes, up to order** (all reads path-kind,
depth `≤ 62`). -/
theorem walkGen_nodes_perm (cells : List Noun) (rs : List (Noun × ℕ))
    (hall : ∀ x ∈ rs, VclL.isPathAx x.2 = true) (h62 : ∀ r ∈ VclL.pathReads rs, VclL.depthOf r.2 ≤ 62) :
    ((Nock.V1J8.Gen.walkGen (cells.headD (.atom 0)) rs).1.map Nock.V1J8.Gen.WRow.node).Perm
      ((walkRows cells rs).map fun t => t.label.node) := by
  set dummy := cells.headD (.atom 0)
  set roots := rs.foldl (fun acc p => if p.1 ∈ acc then acc else acc ++ [p.1]) [] with hroots
  have hgs : Nock.V1J8.Gen.groupReads rs =
      roots.map fun r => (r, (rs.filter fun p => p.1 = r).map fun p => Nock.V1J8.Gen.axisBits p.2) := rfl
  have hperm := groupRoots_perm rs
  rw [← hroots] at hperm
  have hwr : walkRoots rs = (rs.map Prod.fst).dedup := by unfold walkRoots; rw [pathKind_of_all hall]
  -- the spec forest built from the exec roots
  let fs : List (NTree WN) := if roots = [] then [GenWalk.trie dummy dummy [] []]
    else roots.map fun r => GenWalk.trie r r [] (targetsOf rs r)
  have hfe : List.Forall₂ (CorrK 62)
      (if (Nock.V1J8.Gen.groupReads rs).isEmpty then [Nock.V1J8.Gen.trie dummy dummy 1 0 []]
        else (Nock.V1J8.Gen.groupReads rs).map fun g => Nock.V1J8.Gen.trie g.1 g.1 1 0 g.2) fs := by
    rw [hgs]
    by_cases h0 : roots = []
    · simp only [fs, h0, List.map_nil, List.isEmpty_nil, if_true]
      exact List.Forall₂.cons ⟨dummy, dummy, 1, [], [], rfl, rfl, by simp⟩ List.Forall₂.nil
    · have he : (roots.map fun r => (r, (rs.filter fun p => p.1 = r).map fun p => Nock.V1J8.Gen.axisBits p.2)).isEmpty
          = false := by simpa using h0
      simp only [fs, h0, he, if_false, Bool.false_eq_true, List.map_map]
      clear he hperm hroots h0
      induction roots with
      | nil => exact List.Forall₂.nil
      | cons r rt ih =>
        refine List.Forall₂.cons ⟨r, r, 1, [], targetsOf rs r, ?_, rfl, ?_⟩ ?_
        · simp only [List.map_cons, Function.comp_apply, targets_eq hall]; rfl
        · intro s hs
          have := (targetsOf_depth h62 r).2 s hs
          simp at this; omega
        · exact ih
  have hlist := bfsTN_node 62 70 (by norm_num) _ _ hfe
  have hws : (Nock.V1J8.Gen.walkGen dummy rs).1 = Nock.V1J8.Gen.bfsTN 70
      (if (Nock.V1J8.Gen.groupReads rs).isEmpty then [Nock.V1J8.Gen.trie dummy dummy 1 0 []]
        else (Nock.V1J8.Gen.groupReads rs).map fun g => Nock.V1J8.Gen.trie g.1 g.1 1 0 g.2) := rfl
  rw [hws, hlist]
  refine List.Perm.map _ (bfsForest_perm_of_perm ?_)
  unfold walkForest
  rw [hwr]
  by_cases h0 : roots = []
  · have : (rs.map Prod.fst).dedup = [] := List.Perm.eq_nil (hperm.symm.trans (by rw [h0]))
    simp only [fs, h0, this, if_true]; exact List.Perm.refl _
  · have h1 : (rs.map Prod.fst).dedup ≠ [] := fun e => h0 (List.Perm.eq_nil (hperm.trans (by rw [e])))
    simp only [fs, h0, h1, if_false]
    exact hperm.map _


end WalkBridge

/-! ## 6. `balF`'s cell / walk clause -/

section BalF
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.Edit Nock.Edit.GenX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem sum_range_getD' {α R : Type} [AddCommMonoid R] (d : α) (g : α → R) : ∀ l : List α,
    ∑ k ∈ Finset.range l.length, g (l.getD k d) = (l.map g).sum
  | [] => by simp
  | c :: cs => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    congr 1
    exact sum_range_getD' d g cs

theorem sumAt_cellPairs (cs : List Noun) (j : ℕ) : ∀ l : List Noun,
    ComplJ8Data.sumAt (ComplJ8Data.cellPairs cs l) j =
      (l.filter fun n => n.isCell && decide (Nock.V1J8.Gen.idxOf cs n = j)).length
  | [] => rfl
  | n :: l => by
    have ih := sumAt_cellPairs cs j l
    cases n with
    | atom v =>
      simp only [ComplJ8Data.cellPairs, List.filterMap_cons, List.filter_cons, Noun.isCell, Bool.false_and,
        Bool.false_eq_true, if_false] at ih ⊢
      exact ih
    | cell a c =>
      simp only [ComplJ8Data.cellPairs, List.filterMap_cons, List.filter_cons, Noun.isCell, Bool.true_and] at ih ⊢
      rw [ComplJ8Data.sumAt, List.filter_cons] at *
      by_cases h : Nock.V1J8.Gen.idxOf cs (.cell a c) = j
      · simp [h] at ih ⊢; omega
      · simp [h] at ih ⊢; exact ih

/-- **The cell export multiplicity counts the spec walk rows at the serial** (cell nodes). -/
theorem mx_spec (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads) (j : ℕ)
    (hj : j < (j8DataOf p Rg Rt hgen).cells.length) :
    (j8DataOf p Rg Rt hgen).mx.getD j 0 =
      ((walkRows (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads).filter fun t =>
        t.label.node.isCell && decide (Nock.V1J8.Gen.idxOf (j8DataOf p Rg Rt hgen).cells t.label.node = j)).length := by
  rw [ComplJ8Data.mx_eq_cnt p Rg Rt hgen j hj, ComplJ8Data.cnt_eq_sumAt]
  simp only [ComplJ8Data.wRecs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [sumAt_cellPairs]
  have hall : ∀ x ∈ (j8DataOf p Rg Rt hgen).reads, VclL.isPathAx x.2 = true := by
    intro x hx
    have : (j8DataOf p Rg Rt hgen).reads = Nock.V1J8.Gen.pathReads (j8DataOf p Rg Rt hgen).rows := rfl
    rw [this] at hx
    unfold Nock.V1J8.Gen.pathReads at hx
    exact isPathAx_of_two_le (by simpa using (List.mem_filter.mp hx).2)
  have h62 : ∀ r ∈ VclL.pathReads (j8DataOf p Rg Rt hgen).reads, VclL.depthOf r.2 ≤ 62 :=
    fun r hr => (hwalk r hr).trans (by norm_num)
  have hperm := walkGen_nodes_perm (j8DataOf p Rg Rt hgen).cells _ hall h62
  have hws : (j8DataOf p Rg Rt hgen).ws =
      (Nock.V1J8.Gen.walkGen ((j8DataOf p Rg Rt hgen).cells.headD (.atom 0)) (j8DataOf p Rg Rt hgen).reads).1 := rfl
  rw [hws, (hperm.filter _).length_eq, List.filter_map, List.length_map]
  rfl

/-- The walk row's export key is the cell row's export key at the node's serial (plain seed fingerprint). -/
theorem wxKey_eq0 (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (reads : List (Noun × ℕ))
    (mv mx mx1 : ℕ → ℕ) (α γ : K) (k : ℕ) (hmem : (wTrie cells reads k).label.node ∈ cells) :
    wxKeyV δ (walkRow0 δ z cells reads α γ k) =
      xKeyOf δ (ComplJ8Cell.cellRowsB δ z big cells mv mx mx1 (cells.idxOf (wTrie cells reads k).label.node)) 0 := by
  rw [rowsB_eq δ z big cells mv mx mx1 _ (getD_idxOf cells _ hmem)]
  funext i
  fin_cases i <;> simp [wxKeyV, xKeyOf, walkRow0, ComplJ8Cell.cellRowB, cellRow0]

/-- The walk row's export key is the cell row's export key at the node's serial (any encoder `E`). -/
theorem wxKey_eq (E : Noun → Nock.ComputeTable.FP 𝕂′) (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun)
    (reads : List (Noun × ℕ)) (mv mx mx1 : ℕ → ℕ) (α γ : K) (k : ℕ)
    (hmem : (wTrie cells reads k).label.node ∈ cells) :
    wxKeyV δ (ComplJ8Enc.walkRow0E δ E cells reads α γ k) =
      xKeyOf δ (ComplJ8Enc.cellRowsBE δ E z big cells mv mx mx1 (cells.idxOf (wTrie cells reads k).label.node)) 0 := by
  have hr : ComplJ8Enc.cellRowsBE δ E z big cells mv mx mx1 (cells.idxOf (wTrie cells reads k).label.node) =
      ComplJ8Enc.cellRowBE δ E z big cells mv mx mx1 (wTrie cells reads k).label.node
        (cells.idxOf (wTrie cells reads k).label.node) := by
    unfold ComplJ8Enc.cellRowsBE; rw [getD_idxOf cells _ hmem]
  rw [hr]
  funext i
  fin_cases i <;> simp [wxKeyV, xKeyOf, ComplJ8Enc.walkRow0E, ComplJ8Enc.cellRowBE, ComplJ8Cell.cellRowB, cellRow0]

/-- **The cell export terminal equals the walk import terminal** (every spec walk node a cell of the table). -/
theorem cxT_eq_wxT (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (hwcell : ∀ u ∈ walkRows (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads,
      u.label.node ∈ (j8DataOf p Rg Rt hgen).cells) (χ : Coins frameJ8 K) :
    cxT δ (j8DataOf p Rg Rt hgen) χ = wxT δ (j8DataOf p Rg Rt hgen) χ := by
  set D := j8DataOf p Rg Rt hgen with hD
  set n := D.cells.length
  set XG : ℕ → 𝕂′ := fun j => (FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩
    (xKeyOf δ (cRows δ D χ j) 0))⁻¹ with hXG
  have hcellsC : ∀ c ∈ D.cells, c.isCell = true := fun c hc => (ComplJ8Walk.cellsOfRoots_mem _ c hc).1
  -- the walk side
  have hW : wxT δ D χ = ((walkRows D.cells D.reads).map fun u => XG (D.cells.idxOf u.label.node)).sum := by
    unfold wxT
    rw [← sum_range_getD' (trie (.atom 0) (.atom 0) [] []) _ (walkRows D.cells D.reads)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hmem : (wTrie D.cells D.reads k).label.node ∈ D.cells :=
      hwcell _ (wTrie_mem _ _ (Finset.mem_range.mp hk))
    show (FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (wxKeyV δ (wR δ D χ k)))⁻¹ = _
    rw [show wR δ D χ k = ComplJ8Enc.walkRow0E δ (encR δ χ) D.cells D.reads (VerJ8.chalsMJ8 δ χ 0)
        (VerJ8.chalsMJ8 δ χ 1) k from rfl,
      wxKey_eq δ (encR δ χ) (zJ δ χ) (bigOf D) D.cells D.reads (mvF D) (mxF D) (fun _ => 0) _ _ k hmem]
    rfl
  have hS := sum_serial n (fun u : NTree WN => D.cells.idxOf u.label.node) XG (walkRows D.cells D.reads)
    (fun u hu => List.idxOf_lt_length_of_mem (hwcell u hu))
  -- the cell side
  have hC : cxT δ D χ = ∑ j ∈ Finset.range n, ((mxF D j : ℕ) : 𝕂′) * XG j := by
    unfold cxT
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [xTermOf, cellFillInv, hXG, ComplJ8Enc.cellRowsBE, ComplJ8Enc.cellRowBE, ComplJ8Cell.cellRowB, liftQ,
      map_natCast, Nat.cast_zero, map_zero, zero_mul, add_zero]
  rw [hC, hW, hS]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 2
  show D.mx.getD j 0 = _
  rw [mx_spec Rt hgen hwalk j (Finset.mem_range.mp hj)]
  congr 1
  refine List.filter_congr fun u hu => ?_
  have hm := hwcell u hu
  rw [hcellsC _ hm, ComplJ8OfBal.genIdxOf_eq _ _ hm]
  simp

/-- Every read of the run is a defined slot (`consEntriesX_sound` at the run's rows). -/
theorem reads_slot : ∀ x ∈ (j8DataOf p Rg Rt hgen).reads, (Noun.slot x.2 x.1).isSome := by
  intro x hx
  have hx' : x ∈ Nock.V1J8.Gen.pathReads (j8DataOf p Rg Rt hgen).rows := hx
  unfold Nock.V1J8.Gen.pathReads at hx'
  obtain ⟨hx', -⟩ := List.mem_filter.mp hx'
  obtain ⟨row, hrow, hx'⟩ := List.mem_flatMap.mp hx'
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx'
  have hrow' : row ∈ ((bfsForest [t]).map fun u => rowOfSkelX u.label) := by
    have : (j8DataOf p Rg Rt hgen).rows.toList = (bfsForest [t]).map fun u => rowOfSkelX u.label := by
      show (ComplJ8Data.rowsOfT t).toList = _
      simp [ComplJ8Data.rowsOfT]
    rwa [this] at hrow
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hrow'
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp hu
  rw [List.mem_singleton] at hc; subst hc
  have := (consEntriesX_sound u.label (inTree_rowSem hgen hin) e he).2
  simp [this]

theorem chainWalk_cons_cell {n : Noun} {b : Bool} {s : List Bool} (h : (chainWalk n (b :: s)).isSome) :
    ∃ l r, n = .cell l r := by
  cases n with
  | atom a => simp [chainWalk] at h
  | cell l r => exact ⟨l, r, rfl⟩

/-- **Every spec J-8 walk node is a cell of the table** (the run's reads are defined slots; the cell list is
child-closed and contains every cell read root). -/
theorem walkRows_node_cells : ∀ u ∈ walkRows (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads,
    u.label.node ∈ (j8DataOf p Rg Rt hgen).cells := by
  set D := j8DataOf p Rg Rt hgen with hD
  have hclosed : ComplJ8Data.ClP D.cells [] := ComplJ8Data.cells_closed _
  have htok : ∀ r, ∀ s ∈ targetsOf D.reads r, s ≠ [] ∧ (chainWalk r s).isSome := by
    intro r s hs
    refine ⟨targetsOf_ne _ r s hs, ?_⟩
    unfold targetsOf at hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hxk, hxr⟩ := List.mem_filter.mp hx
    have hxr : x.1 = r := of_decide_eq_true hxr
    have hpk := mem_pathKind.mp hxk
    have hsl := reads_slot Rt hgen x hpk.1
    rw [slot_eq_chainWalk _ (by have := two_le_of_path hpk.2; omega), hxr] at hsl
    exact hsl
  intro u hu
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp hu
  let Q : Noun → List Bool → List (List Bool) → Prop := fun n _ T =>
    n ∈ D.cells ∧ ∀ s ∈ T, s ≠ [] ∧ (chainWalk n s).isSome
  have hQ : ∀ l r bs T (b : Bool), Q (.cell l r) bs T → cont b T = true →
      Q (if b then r else l) (bs ++ [b]) (contT b T) := by
    intro l r bs T b hq hcont
    obtain ⟨hmem, hT⟩ := hq
    have hT' : ∀ s ∈ contT b T, s ≠ [] ∧ (chainWalk (if b then r else l) s).isSome := by
      intro s hs
      obtain ⟨hbs, hne⟩ := mem_contT hs
      exact ⟨hne, by simpa [chainWalk] using (hT _ hbs).2⟩
    refine ⟨?_, hT'⟩
    obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ (contT_ne_nil hcont)
    obtain ⟨hne, hsome⟩ := hT' s hs
    obtain ⟨b', s', rfl⟩ : ∃ b' s', s = b' :: s' := by
      cases s with
      | nil => exact absurd rfl hne
      | cons b' s' => exact ⟨b', s', rfl⟩
    obtain ⟨x, y, hxy⟩ := chainWalk_cons_cell hsome
    have hcl := hclosed l r hmem (by simp)
    cases b
    · simp only [Bool.false_eq_true, if_false] at hxy ⊢; exact hcl.1 x y hxy
    · simp only [if_true] at hxy ⊢; exact hcl.2 x y hxy
  rcases mem_walkForest hc with ⟨-, rfl⟩ | ⟨r, hr, rfl⟩
  · have hq : Q (D.cells.headD (.atom 0)) [] [] := by
      refine ⟨?_, by simp⟩
      have : 0 < D.cells.length := cells_pos (p := p) Rt hgen
      cases h : D.cells with
      | nil => rw [h] at this; simp at this
      | cons a l => simp
    obtain ⟨n', bs', T', rfl, hq'⟩ := inTree_trie_inv _ Q hQ hin _ _ _ rfl hq
    rw [(trie_label _ _ _ _).1]; exact hq'.1
  · have hrc : r ∈ D.cells := by
      obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ (targetsOf_ne_nil hr)
      obtain ⟨hsne, hsome⟩ := htok r s hs
      obtain ⟨b', s', rfl⟩ : ∃ b' s', s = b' :: s' := by
        cases s with
        | nil => exact absurd rfl hsne
        | cons b' s' => exact ⟨b', s', rfl⟩
      obtain ⟨x, y, hxy⟩ := chainWalk_cons_cell hsome
      unfold walkRoots at hr
      obtain ⟨z0, hz0, hz0r⟩ := List.mem_map.mp (List.mem_dedup.mp hr)
      obtain ⟨row, hrow, hroot⟩ := ComplJ8Data.pathReads_root _ z0 (mem_pathKind.mp hz0).1
      rw [hz0r] at hroot
      rcases ComplJ8Data.handle_noun_cases p Rg Rt hgen hrow hroot with ⟨_, hm⟩ | ⟨v, ev, _⟩ | ⟨v, ev, _⟩
      · exact hm
      · rw [hxy] at ev; cases ev
      · rw [hxy] at ev; cases ev
    have hq : Q r [] (targetsOf D.reads r) := ⟨hrc, htok r⟩
    obtain ⟨n', bs', T', rfl, hq'⟩ := inTree_trie_inv _ Q hQ hin _ _ _ rfl hq
    rw [(trie_label _ _ _ _).1]; exact hq'.1

/-- **`balF`'s first clause at the run** (every coin): the cell fingerprint-export publics are the J-8 walk's
fingerprint-import publics. -/
theorem balF1_run (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
 (χ : Coins frameJ8 K) :
    ((BRun δ b Rt hgen hpG h31).M χ).pubsC 2 = ((BRun δ b Rt hgen hpG h31).M χ).pubsW 0 ∧
    ((BRun δ b Rt hgen hpG h31).M χ).pubsC 3 = ((BRun δ b Rt hgen hpG h31).M χ).pubsW 1 := by
  have he := cxT_eq_wxT δ Rt hgen hwalk (walkRows_node_cells Rt hgen) χ
  refine ⟨?_, ?_⟩
  · show pubsCOf δ b (j8DataOf p Rg Rt hgen) (cells_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ 2 =
      pubsWOf δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ 0
    simp [pubsCOf, pubsC0, pubsWOf, pubsW0, pub2, he]
  · show pubsCOf δ b (j8DataOf p Rg Rt hgen) (cells_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ 3 =
      pubsWOf δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ 1
    simp [pubsCOf, pubsC0, pubsWOf, pubsW0, pub2, he]

/-- **`balF` at the run**, in `OpenJ8`'s form, with the atom / atom-walk clause carried (`hAV`). -/
theorem balF_run (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (hAV : ∀ χ, (BRun δ b Rt hgen hpG h31).Good χ →
      ((BRun δ b Rt hgen hpG h31).M χ).pubsA 2 = ((BRun δ b Rt hgen hpG h31).M χ).pubsV 0 ∧
      ((BRun δ b Rt hgen hpG h31).M χ).pubsA 3 = ((BRun δ b Rt hgen hpG h31).M χ).pubsV 1) :
    ∀ χ, (BRun δ b Rt hgen hpG h31).Good χ →
      (((BRun δ b Rt hgen hpG h31).M χ).pubsC 2 = ((BRun δ b Rt hgen hpG h31).M χ).pubsW 0 ∧
        ((BRun δ b Rt hgen hpG h31).M χ).pubsC 3 = ((BRun δ b Rt hgen hpG h31).M χ).pubsW 1) ∧
      (((BRun δ b Rt hgen hpG h31).M χ).pubsA 2 = ((BRun δ b Rt hgen hpG h31).M χ).pubsV 0 ∧
        ((BRun δ b Rt hgen hpG h31).M χ).pubsA 3 = ((BRun δ b Rt hgen hpG h31).M χ).pubsV 1) :=
  fun χ hχ => ⟨balF1_run δ b Rt hgen hpG h31 hwalk χ, hAV χ hχ⟩

end BalF

/-! ## 7. `balF`'s atom / atom-walk clause -/

section BalFA
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.Edit Nock.Edit.GenX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The executable walk rows ignore the dummy** when there is a read. -/
theorem walkGen_dummy (d d' : Noun) (rs : List (Noun × ℕ)) (hne : rs ≠ []) :
    (Nock.V1J8.Gen.walkGen d rs).1 = (Nock.V1J8.Gen.walkGen d' rs).1 := by
  have he : (Nock.V1J8.Gen.groupReads rs).isEmpty = false := by
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil rs hne
    have hm : q.1 ∈ rs.foldl (fun acc p => if p.1 ∈ acc then acc else acc ++ [p.1]) [] :=
      ((rootsFold_spec rs [] List.nodup_nil).2 q.1).mpr (Or.inr (List.mem_map_of_mem hq))
    have hgs : Nock.V1J8.Gen.groupReads rs =
        (rs.foldl (fun acc p => if p.1 ∈ acc then acc else acc ++ [p.1]) []).map
          fun r => (r, (rs.filter fun p => p.1 = r).map fun p => Nock.V1J8.Gen.axisBits p.2) := rfl
    rw [hgs, Bool.eq_false_iff]
    intro h
    rw [List.isEmpty_iff, List.map_eq_nil_iff] at h
    rw [h] at hm
    simp at hm
  have h1 : ∀ d0 : Noun, (Nock.V1J8.Gen.walkGen d0 rs).1 = Nock.V1J8.Gen.bfsTN 70
      (if (Nock.V1J8.Gen.groupReads rs).isEmpty then [Nock.V1J8.Gen.trie d0 d0 1 0 []]
        else (Nock.V1J8.Gen.groupReads rs).map fun g => Nock.V1J8.Gen.trie g.1 g.1 1 0 g.2) := fun _ => rfl
  rw [h1, h1]
  simp only [he, Bool.false_eq_true, if_false]

/-- **Every spec walk node is in the list** (generic): a child-closed list containing every path read root, every
path read a defined slot. -/
theorem walkRows_nodes_mem (cells : List Noun) (rs : List (Noun × ℕ)) (hne : cells ≠ [])
    (hcl : ∀ y ∈ cells, ((hdN y).isCell = true → hdN y ∈ cells) ∧ ((tlN y).isCell = true → tlN y ∈ cells))
    (hroot : ∀ x ∈ rs, VclL.isPathAx x.2 = true → x.1 ∈ cells ∧ (Noun.slot x.2 x.1).isSome) :
    ∀ u ∈ walkRows cells rs, u.label.node ∈ cells := by
  have htok : ∀ r, ∀ s ∈ targetsOf rs r, s ≠ [] ∧ (chainWalk r s).isSome := by
    intro r s hs
    refine ⟨targetsOf_ne _ r s hs, ?_⟩
    unfold targetsOf at hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hxk, hxr⟩ := List.mem_filter.mp hx
    have hxr : x.1 = r := of_decide_eq_true hxr
    have hpk := mem_pathKind.mp hxk
    have hsl := (hroot x hpk.1 hpk.2).2
    rw [slot_eq_chainWalk _ (by have := two_le_of_path hpk.2; omega), hxr] at hsl
    exact hsl
  intro u hu
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp hu
  let Q : Noun → List Bool → List (List Bool) → Prop := fun n _ T =>
    n ∈ cells ∧ ∀ s ∈ T, s ≠ [] ∧ (chainWalk n s).isSome
  have hQ : ∀ l r bs T (b : Bool), Q (.cell l r) bs T → cont b T = true →
      Q (if b then r else l) (bs ++ [b]) (contT b T) := by
    intro l r bs T b hq hcont
    obtain ⟨hmem, hT⟩ := hq
    have hT' : ∀ s ∈ contT b T, s ≠ [] ∧ (chainWalk (if b then r else l) s).isSome := by
      intro s hs
      obtain ⟨hbs, hne⟩ := mem_contT hs
      exact ⟨hne, by simpa [chainWalk] using (hT _ hbs).2⟩
    refine ⟨?_, hT'⟩
    obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ (contT_ne_nil hcont)
    obtain ⟨hne, hsome⟩ := hT' s hs
    obtain ⟨b', s', rfl⟩ : ∃ b' s', s = b' :: s' := by
      cases s with
      | nil => exact absurd rfl hne
      | cons b' s' => exact ⟨b', s', rfl⟩
    obtain ⟨x, y, hxy⟩ := chainWalk_cons_cell hsome
    have hcl' := hcl _ hmem
    cases b
    · simp only [Bool.false_eq_true, if_false] at hxy ⊢
      exact hcl'.1 (by rw [show hdN (Noun.cell l r) = l from rfl, hxy]; rfl)
    · simp only [if_true] at hxy ⊢
      exact hcl'.2 (by rw [show tlN (Noun.cell l r) = r from rfl, hxy]; rfl)
  rcases mem_walkForest hc with ⟨-, rfl⟩ | ⟨r, hr, rfl⟩
  · have hq : Q (cells.headD (.atom 0)) [] [] := by
      refine ⟨?_, by simp⟩
      cases h : cells with
      | nil => exact absurd h hne
      | cons a l => simp
    obtain ⟨n', bs', T', rfl, hq'⟩ := inTree_trie_inv _ Q hQ hin _ _ _ rfl hq
    rw [(trie_label _ _ _ _).1]; exact hq'.1
  · have hrc : r ∈ cells := by
      unfold walkRoots at hr
      obtain ⟨z0, hz0, hz0r⟩ := List.mem_map.mp (List.mem_dedup.mp hr)
      have hpk := mem_pathKind.mp hz0
      rw [← hz0r]; exact (hroot z0 hpk.1 hpk.2).1
    have hq : Q r [] (targetsOf rs r) := ⟨hrc, htok r⟩
    obtain ⟨n', bs', T', rfl, hq'⟩ := inTree_trie_inv _ Q hQ hin _ _ _ rfl hq
    rw [(trie_label _ _ _ _).1]; exact hq'.1

/-- The atom-walk reads: a two-limb big atom's comb at axis `2` or `3`. -/
theorem preads_shape
    (hbig : ∀ a ∈ (j8DataOf p Rg Rt hgen).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1]) :
    ∀ x ∈ (j8DataOf p Rg Rt hgen).preads, ∃ a ∈ (j8DataOf p Rg Rt hgen).bigs,
      x.1 = Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a) ∧ (x.2 = 2 ∨ x.2 = 3) := by
  set D := j8DataOf p Rg Rt hgen with hD
  intro x hx
  have hx' : x ∈ ComplJ8Data.pairReadsP D.H D.pd D.rows := hx
  unfold ComplJ8Data.pairReadsP at hx'
  obtain ⟨row, hrow, hx'⟩ := List.mem_flatMap.mp hx'
  split_ifs at hx' with hpair
  swap
  · simp at hx'
  simp only [Nock.V1J8.FillX.isPairB, Bool.and_eq_true, decide_eq_true_eq] at hpair
  obtain ⟨⟨⟨-, -⟩, h1⟩, h2⟩ := hpair
  -- the two leaves are big atoms of the run
  have hkind : ∀ n : Noun, n ∈ rowHandleNounsX row → (D.H n).1 = 2 →
      ∃ a, n = .atom a ∧ a ∈ D.bigs := by
    intro n hn hk
    have hH : D.H = ComplJ8Data.hdlP p D.cells D.acs := rfl
    rw [hH] at hk
    cases n with
    | cell l r' => simp [ComplJ8Data.hdlP] at hk
    | atom a =>
      have hpa : p ≤ a := by
        by_contra hlt
        simp [ComplJ8Data.hdlP, show a < p by omega] at hk
      refine ⟨a, rfl, ?_⟩
      show a ∈ ComplJ8Data.bigsP p D.roots D.rows
      refine (ComplJ8Atom.mem_bigsP p _ _ a).mpr ⟨?_, hpa⟩
      refine List.mem_flatMap.mpr ⟨.atom a, List.mem_append_right _ (List.mem_flatMap.mpr ⟨row, hrow, hn⟩), ?_⟩
      simp [leavesOf]
  obtain ⟨a, ha', ha⟩ := hkind row.ftth (by simp [rowHandleNounsX]) h1
  obtain ⟨c, hc', hc⟩ := hkind row.fttt (by simp [rowHandleNounsX]) h2
  have hpd : (D.pd row).1 = 2 ∨ (D.pd row).1 = 3 := by
    have e : D.pd row = HonestPairX.pdX (ComplJ8Data.sxPP p D.acs D.rows) row := rfl
    rw [e]
    unfold HonestPairX.pdX
    rw [ha', hc']
    simp only [(hbig a ha).2, (hbig c hc).2, HonestPairX.combFD]
    split_ifs <;> simp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
  rcases hx' with rfl | rfl
  · exact ⟨a, ha, by rw [ha']; rfl, hpd⟩
  · exact ⟨c, hc, by rw [hc']; rfl, hpd⟩

end BalFA

section BalFA2
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.Edit Nock.Edit.GenX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem wPairs_idxN (cs : List Noun) : ∀ ws : List Nock.V1J8.Gen.WRow,
    ComplJ8Data.wPairs (Nock.V1J8.Gen.idxN cs) cs ws = ComplJ8Data.cellPairs cs (ws.map Nock.V1J8.Gen.WRow.node)
  | [] => rfl
  | w :: ws => by
    have ih := wPairs_idxN cs ws
    rcases hw : w.node with v | ⟨x, y⟩
    · simp only [ComplJ8Data.wPairs, ComplJ8Data.cellPairs, List.filterMap_cons, List.map_cons, hw] at ih ⊢
      exact ih
    · simp only [ComplJ8Data.wPairs, ComplJ8Data.cellPairs, List.filterMap_cons, List.map_cons, hw,
        Nock.V1J8.Gen.wIdx, ite_self] at ih ⊢
      rw [ih]; rfl

theorem vs_eq (hne : (j8DataOf p Rg Rt hgen).preads ≠ []) :
    (j8DataOf p Rg Rt hgen).vs =
      (Nock.V1J8.Gen.walkGen ((j8DataOf p Rg Rt hgen).acs.headD (.atom 0)) (j8DataOf p Rg Rt hgen).preads).1 := by
  have h : (j8DataOf p Rg Rt hgen).vs = (if (j8DataOf p Rg Rt hgen).preads.isEmpty then
      (([], 0) : List Nock.V1J8.Gen.WRow × ℕ)
      else Nock.V1J8.Gen.walkGen Nock.V1J8.Gen.padN (j8DataOf p Rg Rt hgen).preads).1 := rfl
  rw [h, if_neg (by simpa using hne)]
  exact walkGen_dummy _ _ _ hne

theorem vs_nil (h0 : (j8DataOf p Rg Rt hgen).preads = []) : (j8DataOf p Rg Rt hgen).vs = [] := by
  have h : (j8DataOf p Rg Rt hgen).vs = (if (j8DataOf p Rg Rt hgen).preads.isEmpty then
      (([], 0) : List Nock.V1J8.Gen.WRow × ℕ)
      else Nock.V1J8.Gen.walkGen Nock.V1J8.Gen.padN (j8DataOf p Rg Rt hgen).preads).1 := rfl
  rw [h, if_pos (by rw [h0]; rfl)]

/-- **The atom export multiplicity counts the spec atom-walk rows at the serial**. -/
theorem mxA_spec (hrI : ComplJ8Data.rIAP p (j8DataOf p Rg Rt hgen).acs = Nock.V1J8.Gen.idxN (j8DataOf p Rg Rt hgen).acs)
    (hne : (j8DataOf p Rg Rt hgen).preads ≠ [])
    (hall : ∀ x ∈ (j8DataOf p Rg Rt hgen).preads, VclL.isPathAx x.2 = true)
    (h62 : ∀ r ∈ VclL.pathReads (j8DataOf p Rg Rt hgen).preads, VclL.depthOf r.2 ≤ 62) (j : ℕ)
    (hj : j < (j8DataOf p Rg Rt hgen).acs.length) :
    (j8DataOf p Rg Rt hgen).mxA.getD j 0 =
      ((walkRows (j8DataOf p Rg Rt hgen).acs (j8DataOf p Rg Rt hgen).preads).filter fun t =>
        t.label.node.isCell && decide (Nock.V1J8.Gen.idxOf (j8DataOf p Rg Rt hgen).acs t.label.node = j)).length := by
  rw [ComplJ8Data.mxA_eq_cnt p Rg Rt hgen j hj, ComplJ8Data.cnt_eq_sumAt]
  simp only [ComplJ8Data.awRecs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [hrI, wPairs_idxN, sumAt_cellPairs, vs_eq Rt hgen hne]
  have hperm := walkGen_nodes_perm (j8DataOf p Rg Rt hgen).acs _ hall h62
  rw [(hperm.filter _).length_eq, List.filter_map, List.length_map]
  rfl

theorem combOf_isCell : ∀ l : List ℕ, 2 ≤ l.length → (Nock.V1J8.Gen.combOf l).isCell = true
  | x :: y :: rest, _ => by cases rest <;> rfl
  | [], h => by simp at h
  | [_], h => by simp at h

theorem acs_cell (hpG : p = Nock.Atoms.p) : ∀ c ∈ (j8DataOf p Rg Rt hgen).acs, c.isCell = true := by
  subst hpG
  intro c hc
  obtain ⟨l, h2, -, rfl, -⟩ := ComplJ8Atom.shape_acsP _ _
    (fun a ha => ((ComplJ8Atom.mem_bigsP _ _ _ a).mp ha).2) c hc
  exact combOf_isCell l h2

/-- **The atom export terminal equals the atom-walk import terminal** (atom walk present). -/
theorem axT_eq_vxT (hpG : p = Nock.Atoms.p)
    (hrI : ComplJ8Data.rIAP p (j8DataOf p Rg Rt hgen).acs = Nock.V1J8.Gen.idxN (j8DataOf p Rg Rt hgen).acs)
    (hne : (j8DataOf p Rg Rt hgen).preads ≠ [])
    (hall : ∀ x ∈ (j8DataOf p Rg Rt hgen).preads, VclL.isPathAx x.2 = true)
    (h62 : ∀ r ∈ VclL.pathReads (j8DataOf p Rg Rt hgen).preads, VclL.depthOf r.2 ≤ 62)
    (hwcell : ∀ u ∈ walkRows (j8DataOf p Rg Rt hgen).acs (j8DataOf p Rg Rt hgen).preads,
      u.label.node ∈ (j8DataOf p Rg Rt hgen).acs) (χ : Coins frameJ8 K) :
    axT δ (j8DataOf p Rg Rt hgen) χ = vxT δ (j8DataOf p Rg Rt hgen) χ := by
  have hcellsC := acs_cell Rt hgen hpG
  have hspec := mxA_spec Rt hgen hrI hne hall h62
  set D := j8DataOf p Rg Rt hgen with hD
  set n := D.acs.length
  set XG : ℕ → 𝕂′ := fun j => (FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩
    (xKeyOf δ (aRows δ D χ j) 0))⁻¹ with hXG
  have hnV : nVOf D = (walkRows D.acs D.preads).length := by unfold nVOf; rw [if_neg hne]
  have hW : vxT δ D χ = ((walkRows D.acs D.preads).map fun u => XG (D.acs.idxOf u.label.node)).sum := by
    unfold vxT
    rw [hnV, ← sum_range_getD' (trie (.atom 0) (.atom 0) [] []) _ (walkRows D.acs D.preads)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hmem : (wTrie D.acs D.preads k).label.node ∈ D.acs :=
      hwcell _ (wTrie_mem _ _ (Finset.mem_range.mp hk))
    show (FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (wxKeyV δ (vR δ D χ k)))⁻¹ = _
    rw [show vR δ D χ k = walkRow0 δ (zA δ χ) D.acs D.preads (ChalsAZJ8.chalsAJ8Z δ χ 0)
        (ChalsAZJ8.chalsAJ8Z δ χ 1) k from rfl,
      wxKey_eq0 δ (zA δ χ) (fun _ => none) D.acs D.preads (mvA D) (mxAF D) (fun _ => 0) _ _ k hmem]
    rfl
  have hS := sum_serial n (fun u : NTree WN => D.acs.idxOf u.label.node) XG (walkRows D.acs D.preads)
    (fun u hu => List.idxOf_lt_length_of_mem (hwcell u hu))
  have hC : axT δ D χ = ∑ j ∈ Finset.range n, ((mxAF D j : ℕ) : 𝕂′) * XG j := by
    unfold axT
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [xTermOf, cellFillInv, hXG, ComplJ8Cell.cellRowsBP, ComplJ8Cell.cellRowBP, ComplJ8Cell.cellRowsB,
      ComplJ8Cell.cellRowB, liftQ, map_natCast,
      Nat.cast_zero, map_zero, zero_mul, add_zero]
  rw [hC, hW, hS]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 2
  show D.mxA.getD j 0 = _
  rw [hspec j (Finset.mem_range.mp hj)]
  congr 1
  refine List.filter_congr fun u hu => ?_
  have hm := hwcell u hu
  rw [hcellsC _ hm, ComplJ8OfBal.genIdxOf_eq _ _ hm]
  simp

/-- With no atom-walk read the atom export terminal is zero. -/
theorem axT_zero (h0 : (j8DataOf p Rg Rt hgen).preads = []) (χ : Coins frameJ8 K) :
    axT δ (j8DataOf p Rg Rt hgen) χ = 0 := by
  unfold axT
  refine Finset.sum_eq_zero fun j hj => ?_
  have hm : (j8DataOf p Rg Rt hgen).mxA.getD j 0 = 0 := by
    rw [ComplJ8Data.mxA_eq_cnt p Rg Rt hgen j (Finset.mem_range.mp hj), ComplJ8Data.cnt_eq_sumAt]
    simp [ComplJ8Data.awRecs, vs_nil Rt hgen h0, ComplJ8Data.wPairs, ComplJ8Data.sumAt]
  simp only [xTermOf, cellFillInv, ComplJ8Cell.cellRowsBP, ComplJ8Cell.cellRowBP, ComplJ8Cell.cellRowsB,
    ComplJ8Cell.cellRowB, liftQ, mxAF, hm,
    Nat.cast_zero, map_zero, zero_mul, add_zero]

theorem depthOf_le_of {a : ℕ} (h : a = 2 ∨ a = 3) : VclL.depthOf a ≤ 62 := by
  rcases h with rfl | rfl <;> decide

theorem comb_mem_acs (hpG : p = Nock.Atoms.p) {a : ℕ} (ha : a ∈ (j8DataOf p Rg Rt hgen).bigs)
    (h2 : 2 ≤ (Nock.Atoms.limbs a).length) :
    Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a) ∈ (j8DataOf p Rg Rt hgen).acs := by
  subst hpG
  rw [ComplJ8BigBound.data_acs hgen]
  exact (ComplJ8Atom.mem_acsP _ _ _).mpr (Or.inl ((ComplJ8Atom.mem_spineL _ _).mpr
    ⟨a, ha, (ComplJ8Atom.mem_spineOf _ _).mpr ⟨0, by simpa using h2, by simp⟩⟩))


theorem balF2_run (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hbig : ∀ a ∈ (j8DataOf p Rg Rt hgen).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1])
    (hrI : ComplJ8Data.rIAP p (j8DataOf p Rg Rt hgen).acs = Nock.V1J8.Gen.idxN (j8DataOf p Rg Rt hgen).acs)
    (χ : Coins frameJ8 K) :
    ((BRun δ b Rt hgen hpG h31).M χ).pubsA 2 = ((BRun δ b Rt hgen hpG h31).M χ).pubsV 0 ∧
    ((BRun δ b Rt hgen hpG h31).M χ).pubsA 3 = ((BRun δ b Rt hgen hpG h31).M χ).pubsV 1 := by
  have hsh := preads_shape Rt hgen hbig
  have hall : ∀ x ∈ (j8DataOf p Rg Rt hgen).preads, VclL.isPathAx x.2 = true := by
    intro x hx
    obtain ⟨a, -, -, h⟩ := hsh x hx
    exact isPathAx_of_two_le (by omega)
  have h62 : ∀ r ∈ VclL.pathReads (j8DataOf p Rg Rt hgen).preads, VclL.depthOf r.2 ≤ 62 := by
    intro x hx
    have hx' : x ∈ (j8DataOf p Rg Rt hgen).preads := by
      unfold VclL.pathReads at hx
      exact (List.mem_filter.mp (List.mem_dedup.mp hx)).1
    obtain ⟨a, -, -, h⟩ := hsh x hx'
    exact depthOf_le_of h
  have hwcell : ∀ u ∈ walkRows (j8DataOf p Rg Rt hgen).acs (j8DataOf p Rg Rt hgen).preads,
      u.label.node ∈ (j8DataOf p Rg Rt hgen).acs := by
    refine walkRows_nodes_mem _ _ (List.ne_nil_of_length_pos (acs_pos (p := p) Rt hgen))
      (acs_closed_run Rt hgen hpG) ?_
    intro x hx _
    obtain ⟨a, ha, h1, h2⟩ := hsh x hx
    have hl := (hbig a ha).2
    refine ⟨h1 ▸ comb_mem_acs Rt hgen hpG ha (by rw [hl]; simp), ?_⟩
    rw [h1, hl]
    rcases h2 with h | h <;> rw [h, slot_eq_chainWalk _ (by norm_num)] <;> rfl
  have hz : (0 : Quad (algebraMap (ZMod p) K δ)) = Quad.mk _ 0 0 :=
    ((Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩).symm
  refine ⟨?_, ?_⟩
  · show pubsAOf δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ 2 =
      pubsVOf δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ 0
    by_cases h0 : (j8DataOf p Rg Rt hgen).preads = []
    · simp [pubsAOf, pubsA1, pubsA0, pubsVOf, pub2, h0, axT_zero δ Rt hgen h0, hz, Quad.re_mk]
    · simp [pubsAOf, pubsA1, pubsA0, pubsVOf, pubsV0, pub2, h0,
        axT_eq_vxT δ Rt hgen hpG hrI h0 hall h62 hwcell χ]
  · show pubsAOf δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ 3 =
      pubsVOf δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ 1
    by_cases h0 : (j8DataOf p Rg Rt hgen).preads = []
    · simp [pubsAOf, pubsA1, pubsA0, pubsVOf, pub2, h0, axT_zero δ Rt hgen h0, hz, Quad.im_mk]
    · simp [pubsAOf, pubsA1, pubsA0, pubsVOf, pubsV0, pub2, h0,
        axT_eq_vxT δ Rt hgen hpG hrI h0 hall h62 hwcell χ]

/-- **`balF` at the run, closed** (`OpenJ8`'s form, nothing carried): at `complJ8`'s binders `hpG hop5 hclA hRt
h31` and the walk binder `hwalk`. -/
theorem balF_closed (hpG : p = Nock.Atoms.p) (hop5 : ComplJ8.ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads) :
    ∀ χ, (BRun δ b Rt hgen hpG h31).Good χ →
      (((BRun δ b Rt hgen hpG h31).M χ).pubsC 2 = ((BRun δ b Rt hgen hpG h31).M χ).pubsW 0 ∧
        ((BRun δ b Rt hgen hpG h31).M χ).pubsC 3 = ((BRun δ b Rt hgen hpG h31).M χ).pubsW 1) ∧
      (((BRun δ b Rt hgen hpG h31).M χ).pubsA 2 = ((BRun δ b Rt hgen hpG h31).M χ).pubsV 0 ∧
        ((BRun δ b Rt hgen hpG h31).M χ).pubsA 3 = ((BRun δ b Rt hgen hpG h31).M χ).pubsV 1) := by
  have hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31 := by
    have h := h31 (bfsForest [(j8DataOf p Rg Rt hgen).t]).length (by simp [sizesJ8])
    rw [ComplJ8BigBound.data_rows hgen]
    simpa [ComplJ8Data.rowsOfT, j8DataOf] using h
  obtain ⟨hb, -, -, -, -, -, hrI, -, -⟩ := ComplJ8BigBound.bigBound_single hgen hpG (hclA 0) (hclA 1) hRt hop5 hN
  exact balF_run δ b Rt hgen hpG h31 hwalk fun χ _ =>
    balF2_run δ b Rt hgen hpG h31 (fun a ha => ⟨(hb a ha).1, (hb a ha).2.2⟩) hrI χ

end BalFA2

/-! ## 8. `balV`'s atom handle clause (clause 2) -/

section BalV2
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.Edit Nock.Edit.GenX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The atom cell part's coin-free row environment reads the honest base columns (`k ∈ [2, 129)`). -/
theorem aE0_trace_col (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length)) (χ : Coins frameJ8 K)
    (i : Fin D.acs.length) (k : ℕ) (h2 : 2 ≤ k) (hk : k < 129) :
    (ComplJ8OfAtom.aE0 δ b D hA o χ i).trace k = colAH δ b D hA o χ (fun _ => 0) k i := by
  have hw : k < (cellTemplateHQ δ).width 3 := by rw [CellTraceHQ.cellTemplateHQ_width]; omega
  simp only [ComplJ8OfAtom.aE0, CellTraceHQ.E, Nock.Framework.Reify.envOfTrace, dif_pos hw]
  rw [honestQ_eval _ _ hinj]
  simp [fullCol, CellTraceHQ.colHQ, colAH, extColF, hk, show k ≠ 0 by omega, show k ≠ 1 by omega]

/-- **The atom cell handle key of a two-small-atom row**: `ρH + aHx j = ρH + recDen 0 γH (j, (0, x), (0, z))`. -/
theorem aHx_two (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length)) (χ : Coins frameJ8 K)
    (j : ℕ) (hj : j < D.acs.length) {x z : ℕ} (hy : D.acs[j] = Noun.cell (.atom x) (.atom z)) :
    ComplJ8OfAtom.aHx δ b D hA o j χ =
      recDen 0 (ComplJ8Bad.γH δ χ) (((j : ℕ) : ZMod p), ((0 : ZMod p), ((x : ℕ) : ZMod p)),
        ((0 : ZMod p), ((z : ℕ) : ZMod p))) := by
  obtain ⟨f0, -, f2, f3, f4, f5⟩ := ComplJ8OfAtom.colAH_fields δ b D hA o χ (fun _ => 0) ⟨j, hj⟩
  simp only [hy] at f0 f2 f3 f4 f5
  have htr := fun k h2 hk => aE0_trace_col δ b D hA o hinj χ ⟨j, hj⟩ k h2 hk
  unfold ComplJ8OfAtom.aHx
  rw [dif_pos hj]
  simp only [FiniteIO.compress, Walk.rlc, Fin.sum_univ_five, BalanceQ.liftRec, ServeH.keyVec5, CellH.keyH,
    CellH.valE, recDen]
  have t0 := htr Cell.idx (by decide) (by decide)
  have t1 := htr Cell.wL (by decide) (by decide)
  have t2 := htr Cell.aL (by decide) (by decide)
  have t3 := htr Cell.wR (by decide) (by decide)
  have t4 := htr Cell.aR (by decide) (by decide)
  simp [CoeffExpr.eval, cv, notE, t0, t1, t2, t3, t4, f0, f2, f3, f4, f5, Noun.isCell, Nock.V1J8.Gen.hdN',
    Nock.V1J8.Gen.tlN', Nock.V1J8.Gen.atomV, IsScalarTower.algebraMap_apply (ZMod p) K 𝕂′]

/-- **The atom cell handle key of any row with an atom head** (GLA, general limbs): `aHx j = recDen 0 γH (j, (0, x),
(wR, valR))`, the tail a cell (`wR = 1`, its serial) or an atom (`wR = 0`, its value). -/
theorem aHx_gen (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length)) (χ : Coins frameJ8 K)
    (j : ℕ) (hj : j < D.acs.length) (hhd : (Nock.V1J8.Gen.hdN' D.acs[j]).isCell = false) :
    ComplJ8OfAtom.aHx δ b D hA o j χ =
      recDen 0 (ComplJ8Bad.γH δ χ) (((j : ℕ) : ZMod p),
        ((0 : ZMod p), ((Nock.V1J8.Gen.atomV (Nock.V1J8.Gen.hdN' D.acs[j]) : ℕ) : ZMod p)),
        ((((if (Nock.V1J8.Gen.tlN' D.acs[j]).isCell then 1 else 0 : ℕ)) : ZMod p),
          (if (Nock.V1J8.Gen.tlN' D.acs[j]).isCell then ((ComplJ8Data.ptrP p D.acs D.rows D.acs[j] : ℕ) : ZMod p)
            else ((Nock.V1J8.Gen.atomV (Nock.V1J8.Gen.tlN' D.acs[j]) : ℕ) : ZMod p)))) := by
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := ComplJ8OfAtom.colAH_fields δ b D hA o χ (fun _ => 0) ⟨j, hj⟩
  simp only [Fin.val_mk] at f0 f1 f2 f3 f4 f5
  rw [hhd] at f2
  have htr := fun k h2 hk => aE0_trace_col δ b D hA o hinj χ ⟨j, hj⟩ k h2 hk
  unfold ComplJ8OfAtom.aHx
  rw [dif_pos hj]
  simp only [FiniteIO.compress, Walk.rlc, Fin.sum_univ_five, BalanceQ.liftRec, ServeH.keyVec5, CellH.keyH,
    CellH.valE, recDen]
  have t0 := htr Cell.idx (by decide) (by decide)
  have t1 := htr Cell.wL (by decide) (by decide)
  have t2 := htr Cell.aL (by decide) (by decide)
  have t3 := htr Cell.wR (by decide) (by decide)
  have t4 := htr Cell.aR (by decide) (by decide)
  have t5 := htr Cell.idR (by decide) (by decide)
  cases hc : (Nock.V1J8.Gen.tlN' D.acs[j]).isCell
  · rw [hc] at f1 f3
    simp [CoeffExpr.eval, cv, notE, t0, t1, t2, t3, t4, t5, f0, f1, f2, f3, f4, f5, hc,
      IsScalarTower.algebraMap_apply (ZMod p) K 𝕂′]
  · rw [hc] at f1 f3
    simp [CoeffExpr.eval, cv, notE, t0, t1, t2, t3, t4, t5, f0, f1, f2, f3, f4, f5, hc,
      IsScalarTower.algebraMap_apply (ZMod p) K 𝕂′]

/-- The atom cell list's rows are cells of two small atoms. -/
theorem acs_two (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
    (hpG : p = Nock.Atoms.p)
    (hb : ∀ a ∈ (j8DataOf p Rg Rt hgen).bigs, p ≤ a ∧ a < p + 2 ^ 31) :
    ∀ y ∈ (j8DataOf p Rg Rt hgen).acs, ∃ x z, y = Noun.cell (.atom x) (.atom z) ∧ x < p ∧ z < p := by
  subst hpG
  have hp : Nock.Atoms.p = 18446744069414584321 := by simp [Nock.Atoms.p, Nock.Field.p]
  have hB := Nock.Atoms.B_eq
  intro y hy
  rw [ComplJ8BigBound.data_acs hgen, (ComplJ8BigBound.acsP_two _ hb).2] at hy
  rcases List.mem_append.mp hy with hy | hy
  · have hy' := ((ComplJ8Atom.linkOrder_spec _ (ComplJ8Atom.spineL_cells _)).2.1 y).1 hy
    obtain ⟨a, ha, hy'⟩ := (ComplJ8Atom.mem_spineL _ y).1 hy'
    rw [ComplJ8BigBound.limbs_two (hb a ha).1 (hb a ha).2] at hy'
    simp only [Nock.V1J8.Gen.spineOf, Nock.V1J8.Gen.combOf, List.mem_singleton] at hy'
    have := (hb a ha).2
    exact ⟨_, _, hy', by omega, by omega⟩
  · rw [List.mem_singleton] at hy
    exact ⟨0, 1, hy, by omega, by omega⟩

/-- **The atom-walk handle import is the atom-walk-weighted atom cell handle sum** (atom walk present). -/
theorem vhX_eq (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
    (hpG : p = Nock.Atoms.p)
    (h2 : ∀ y ∈ (j8DataOf p Rg Rt hgen).acs, ∃ x z, y = Noun.cell (.atom x) (.atom z) ∧ x < p ∧ z < p)
    (hrI : ComplJ8Data.rIAP p (j8DataOf p Rg Rt hgen).acs = Nock.V1J8.Gen.idxN (j8DataOf p Rg Rt hgen).acs)
    (hne : (j8DataOf p Rg Rt hgen).preads ≠ [])
    (hall : ∀ x ∈ (j8DataOf p Rg Rt hgen).preads, VclL.isPathAx x.2 = true)
    (h62 : ∀ r ∈ VclL.pathReads (j8DataOf p Rg Rt hgen).preads, VclL.depthOf r.2 ≤ 62)
    (hwcell : ∀ u ∈ walkRows (j8DataOf p Rg Rt hgen).acs (j8DataOf p Rg Rt hgen).preads,
      u.label.node ∈ (j8DataOf p Rg Rt hgen).acs)
    (hA : 0 < (j8DataOf p Rg Rt hgen).acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjA : Function.Injective (powN o (j8DataOf p Rg Rt hgen).acs.length))
    (hinjV : Function.Injective (powN o (nVOf (j8DataOf p Rg Rt hgen)))) (χ : Coins frameJ8 K) :
    vhX δ b (j8DataOf p Rg Rt hgen) o χ = ∑ j ∈ Finset.range (j8DataOf p Rg Rt hgen).acs.length,
      (((j8DataOf p Rg Rt hgen).mhA.getD j 0 : ℕ) : 𝕂′) *
        (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b (j8DataOf p Rg Rt hgen) hA o j χ)⁻¹ := by
  have hcellsC := acs_cell Rt hgen hpG
  have hspec := mxA_spec Rt hgen hrI hne hall h62
  set D := j8DataOf p Rg Rt hgen with hD
  set n := D.acs.length
  set G : ℕ → 𝕂′ := fun j => (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b D hA o j χ)⁻¹ with hG
  have hnV : nVOf D = (walkRows D.acs D.preads).length := by unfold nVOf; rw [if_neg hne]
  have hterm : ∀ k ∈ Finset.range (nVOf D), (vdN δ b D o χ WalkHC.xKeyH k)⁻¹ =
      G (D.acs.idxOf (wTrie D.acs D.preads k).label.node) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hmem : (wTrie D.acs D.preads k).label.node ∈ D.acs :=
      hwcell _ (wTrie_mem _ _ (hnV ▸ hk'))
    obtain ⟨x, z, hxz, hx, hz⟩ := h2 _ hmem
    have hjl := List.idxOf_lt_length_of_mem hmem
    have hyj : D.acs[D.acs.idxOf (wTrie D.acs D.preads k).label.node] = Noun.cell (.atom x) (.atom z) := by
      rw [List.getElem_idxOf hjl]; exact hxz
    have hd : vdN δ b D o χ WalkHC.xKeyH k = ComplJ8Bad.ρH δ χ + recDen 0 (ComplJ8Bad.γH δ χ)
        ((ComplJ8OfAtom.vValsC δ D χ ⟨k, hk'⟩).idx, (kLV D ⟨k, hk'⟩, vLV D ⟨k, hk'⟩), (kRV D ⟨k, hk'⟩, vRV D ⟨k, hk'⟩)) := by
      simp only [vdN, WalkTraceHQ.dN, dif_pos hk']
      exact (ComplJ8OfAtom.aw_dRow_split δ b D o hinjV χ (pubsV0 δ D χ) ⟨k, hk'⟩).1
    have hH : D.H = ComplJ8Data.hdlP p D.cells D.acs := rfl
    have hv : (ComplJ8OfAtom.vValsC δ D χ ⟨k, hk'⟩).idx = ((D.acs.idxOf (wTrie D.acs D.preads k).label.node : ℕ) : ZMod p) := rfl
    have hkl : kLV D ⟨k, hk'⟩ = 0 ∧ vLV D ⟨k, hk'⟩ = ((x : ℕ) : ZMod p) ∧ kRV D ⟨k, hk'⟩ = 0 ∧
        vRV D ⟨k, hk'⟩ = ((z : ℕ) : ZMod p) := by
      simp only [kLV, vLV, kRV, vRV, vNode, hxz, hH]
      simp [VclL.hdN, VclL.tlN, ComplJ8Data.hdlP, hx, hz]
    simp only [hG]
    rw [hd, hv, hkl.1, hkl.2.1, hkl.2.2.1, hkl.2.2.2, aHx_two δ b D hA o hinjA χ _ hjl hyj]
  have hW : vhX δ b D o χ = ((walkRows D.acs D.preads).map fun u => G (D.acs.idxOf u.label.node)).sum := by
    unfold vhX
    rw [Finset.sum_congr rfl hterm, hnV]
    exact sum_range_getD' (trie (.atom 0) (.atom 0) [] []) (fun u => G (D.acs.idxOf u.label.node)) _
  have hS := sum_serial n (fun u : NTree WN => D.acs.idxOf u.label.node) G (walkRows D.acs D.preads)
    (fun u hu => List.idxOf_lt_length_of_mem (hwcell u hu))
  rw [hW, hS]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 2
  show _ = D.mxA.getD j 0
  rw [hspec j (Finset.mem_range.mp hj)]
  congr 1
  refine List.filter_congr fun u hu => ?_
  have hm := hwcell u hu
  rw [hcellsC _ hm, ComplJ8OfBal.genIdxOf_eq _ _ hm]
  simp

/-- **`balV`'s second clause at the run, with the inc part carried** (`hI`: the atom inc terminal is the
`mhx`-weighted atom cell handle sum; every coin). -/
theorem balV2_of_inc (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
    (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hbig : ∀ a ∈ (j8DataOf p Rg Rt hgen).bigs, p ≤ a ∧ a < p + 2 ^ 31 ∧
      Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1])
    (hrI : ComplJ8Data.rIAP p (j8DataOf p Rg Rt hgen).acs = Nock.V1J8.Gen.idxN (j8DataOf p Rg Rt hgen).acs)
    (hI : ∀ χ : Coins frameJ8 K,
      ∑ j ∈ Finset.range (j8DataOf p Rg Rt hgen).acs.length,
        liftQ δ (HonestA8.cNat j (newBA (j8DataOf p Rg Rt hgen) AtomChipHQ.inc)) *
          (HonestA8.dNat δ (HonestA8.dC δ b (acs_pos Rt hgen) (powN (orbJ8 _ (dvdOK_of_rows hpG _ h31)) _)
            (orbJ8 _ (dvdOK_of_rows hpG _ h31)) (ChalsAZJ8.chalsAJ8Z δ χ)
            (pubsAOf δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ)
            (colAH δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ
              (pubsAOf δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ))
            (newBA (j8DataOf p Rg Rt hgen))) j)⁻¹ =
        ∑ j ∈ Finset.range (j8DataOf p Rg Rt hgen).acs.length,
          ((((j8DataOf p Rg Rt hgen).info.getD j Nock.V1J8.Gen.AInfo.z).mhx : ℕ) : 𝕂′) *
            (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen)
              (orbJ8 _ (dvdOK_of_rows hpG _ h31)) j χ)⁻¹)
    (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (((BRun δ b Rt hgen hpG h31).M χ).pubsA CellHQ.pubHQ)
        (((BRun δ b Rt hgen hpG h31).M χ).pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) (((BRun δ b Rt hgen hpG h31).M χ).pubsA AtomChipHQ.pubC)
          (((BRun δ b Rt hgen hpG h31).M χ).pubsA (AtomChipHQ.pubC + 1)) +
        Quad.mk (algebraMap (ZMod p) K δ) (((BRun δ b Rt hgen hpG h31).M χ).pubsV WalkHQ.pubXQ)
          (((BRun δ b Rt hgen hpG h31).M χ).pubsV (WalkHQ.pubXQ + 1)) := by
  set D := j8DataOf p Rg Rt hgen with hD
  set hF := dvdOK_of_rows hpG D h31
  set o := orbJ8 D hF
  have hA : 0 < D.acs.length := acs_pos Rt hgen
  have hmA : D.acs.length ∈ sizesJ8 D := by simp [sizesJ8]
  have hmV : nVOf D ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjA := (powN_ok o (le_two_pow_ht D hmA)).1
  have hinjV := (powN_ok o (le_two_pow_ht D hmV)).1
  set G : ℕ → 𝕂′ := fun j => (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b D hA o j χ)⁻¹ with hG
  obtain ⟨-, -, tHQ, -, tC, -⟩ := ComplJ8OfAtom.atomTerms δ b D hA o χ
  show Quad.mk _ (pubsAOf δ b D hA o χ CellHQ.pubHQ) (pubsAOf δ b D hA o χ (CellHQ.pubHQ + 1)) =
    Quad.mk _ (pubsAOf δ b D hA o χ AtomChipHQ.pubC) (pubsAOf δ b D hA o χ (AtomChipHQ.pubC + 1)) +
      Quad.mk _ (pubsVOf δ b D o χ WalkHQ.pubXQ) (pubsVOf δ b D o χ (WalkHQ.pubXQ + 1))
  rw [tHQ, tC, hI χ]
  -- the cell part's handle provide, row by row
  have hL : ∑ j ∈ Finset.range D.acs.length, liftQ δ (CellTraceH.mN (mhvA D) j) *
      (CellTraceHQ.dN δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) (pubsAOf δ b D hA o χ) (aCol δ b D χ) (mhvA D) j)⁻¹ =
      ∑ j ∈ Finset.range D.acs.length, (((D.info.getD j Nock.V1J8.Gen.AInfo.z).mhx : ℕ) : 𝕂′) * G j +
      ∑ j ∈ Finset.range D.acs.length, ((D.mhA.getD j 0 : ℕ) : 𝕂′) * G j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    simp only [CellTraceH.mN, CellTraceHQ.dN, dif_pos hj', hG]
    rw [ComplJ8OfAtom.aRow_split δ b D hA o χ _ ⟨j, hj'⟩]
    simp only [mhvA, mhAF, liftQ, Nat.cast_add, map_add, map_natCast]
    ring
  rw [hL]
  congr 1
  by_cases h0 : D.preads = []
  · have hz : (0 : 𝕂′) = Quad.mk _ 0 0 := ((Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩).symm
    have hv : ∀ i, pubsVOf δ b D o χ i = 0 := fun i => by simp [pubsVOf, h0]
    rw [hv, hv, ← hz]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hm : D.mhA.getD j 0 = 0 := by
      show D.mxA.getD j 0 = 0
      rw [ComplJ8Data.mxA_eq_cnt p Rg Rt hgen j (Finset.mem_range.mp hj), ComplJ8Data.cnt_eq_sumAt]
      simp [ComplJ8Data.awRecs, vs_nil Rt hgen h0, ComplJ8Data.wPairs, ComplJ8Data.sumAt]
    simp [hm]
  · have hsh := preads_shape Rt hgen fun a ha => ⟨(hbig a ha).1, (hbig a ha).2.2⟩
    have hall : ∀ x ∈ D.preads, VclL.isPathAx x.2 = true := by
      intro x hx
      obtain ⟨a, -, -, h⟩ := hsh x hx
      exact isPathAx_of_two_le (by omega)
    have h62 : ∀ r ∈ VclL.pathReads D.preads, VclL.depthOf r.2 ≤ 62 := by
      intro x hx
      have hx' : x ∈ D.preads := by
        unfold VclL.pathReads at hx
        exact (List.mem_filter.mp (List.mem_dedup.mp hx)).1
      obtain ⟨a, -, -, h⟩ := hsh x hx'
      exact depthOf_le_of h
    have hwcell : ∀ u ∈ walkRows D.acs D.preads, u.label.node ∈ D.acs := by
      refine walkRows_nodes_mem _ _ (List.ne_nil_of_length_pos hA) (acs_closed_run Rt hgen hpG) ?_
      intro x hx _
      obtain ⟨a, ha, h1, h2⟩ := hsh x hx
      have hl := (hbig a ha).2.2
      refine ⟨h1 ▸ comb_mem_acs Rt hgen hpG ha (by rw [hl]; simp), ?_⟩
      rw [h1, hl]
      rcases h2 with h | h <;> rw [h, slot_eq_chainWalk _ (by norm_num)] <;> rfl
    have h4 : pubsVOf δ b D o χ WalkHQ.pubXQ = pub2 δ (vhX δ b D o χ) 4 := by
      simp [pubsVOf, h0, WalkHQ.pubXQ]
    have h5 : pubsVOf δ b D o χ (WalkHQ.pubXQ + 1) = pub2 δ (vhX δ b D o χ) 5 := by
      simp [pubsVOf, h0, WalkHQ.pubXQ]
    rw [h4, h5, pub2_mk2 δ _ 4 rfl,
      vhX_eq δ b Rt hgen hpG (acs_two Rt hgen hpG fun a ha => ⟨(hbig a ha).1, (hbig a ha).2.1⟩) hrI h0 hall h62
        hwcell hA o hinjA hinjV χ]

end BalV2

/-! ## 9. `balV`'s atom inc terminal (`hI` of `balV2_of_inc`) -/

section IncFold
open Nock.V1J8.Gen (AInfo idxOf combOf spineOf incChain)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom (wrA stepF fuelOf getD_modify inc_wrA size_wrA incChain_step
  spineOf_cons2 spineOf_short size_incChain Cnd)
variable (p : ℕ) (acsL : List Noun) (rows : Array Nock.Edit.GenX.RowNX)

theorem mhx_wrA (ln lo : List ℕ) (a : Array AInfo) (k : ℕ) :
    ((wrA p acsL rows ln lo a).getD k AInfo.z).mhx =
      (a.getD k AInfo.z).mhx +
        (if ComplJ8Data.keyP p acsL (combOf lo) = k ∧ k < a.size then 1 else 0) := by
  simp only [wrA]
  rw [getD_modify, getD_modify]
  simp only [Array.size_modify]
  split_ifs <;> simp

/-- One fold step on a two-limb operand: the new row becomes an inc row, the old row gets one consume. -/
theorem stepF_two (a : Array AInfo) (vc : ℕ × ℕ) (k : ℕ)
    (h2 : vc.1 + 1 ≠ p → (Nock.Atoms.limbs vc.1).length = 2 ∧ (Nock.Atoms.limbs (vc.1 + 1)).length = 2) :
    (stepF p acsL rows a vc).size = a.size ∧
    ((stepF p acsL rows a vc).getD k AInfo.z).mhx = (a.getD k AInfo.z).mhx +
      (if vc.1 + 1 ≠ p ∧ ComplJ8Data.keyP p acsL (combOf (Nock.Atoms.limbs vc.1)) = k ∧ k < a.size then 1 else 0) ∧
    (((stepF p acsL rows a vc).getD k AInfo.z).inc = true ↔ (a.getD k AInfo.z).inc = true ∨
      (vc.1 + 1 ≠ p ∧ k < a.size ∧ k = idxOf acsL (combOf (Nock.Atoms.limbs (vc.1 + 1))))) := by
  by_cases hp : vc.1 + 1 = p
  · have hp' : ¬ vc.1 + 1 ≠ p := not_not.mpr hp
    simp only [stepF, if_pos hp, hp', false_and, if_false, add_zero, false_and, or_false]
    refine ⟨by simp, ?_, ?_⟩
    · rw [getD_modify]; split_ifs <;> simp
    · rw [getD_modify]; split_ifs <;> simp
  · obtain ⟨ho, hn⟩ := h2 hp
    have hf : fuelOf vc.1 = 1 + 1 := by
      unfold fuelOf
      rw [spineOf_cons2 _ (by omega), spineOf_short _ (by simp [ho])]; simp
    have hc : ¬ Cnd (Nock.Atoms.limbs vc.1) := fun h => by have := h.2; omega
    simp only [stepF, if_neg hp]
    rw [hf, incChain_step p acsL 1 _ _ a (by omega) (by omega), if_neg hc]
    refine ⟨by simp [size_wrA], ?_, ?_⟩
    · have e : ∀ (c : Prop) [Decidable c] (x : AInfo), (if c then { x with mi := x.mi + vc.2 } else x).mhx = x.mhx :=
        fun c _ x => by split_ifs <;> rfl
      rw [getD_modify, e, mhx_wrA]
      by_cases hq : ComplJ8Data.keyP p acsL (combOf (Nock.Atoms.limbs vc.1)) = k ∧ k < a.size
      · rw [if_pos hq, if_pos ⟨hp, hq⟩]
      · rw [if_neg hq, if_neg (fun h => hq h.2)]
    · have e : ∀ (c : Prop) [Decidable c] (x : AInfo), (if c then { x with mi := x.mi + vc.2 } else x).inc = x.inc :=
        fun c _ x => by split_ifs <;> rfl
      rw [getD_modify, e, inc_wrA]
      constructor
      · rintro (h | ⟨h1, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hp, h1, h3⟩
      · rintro (h | ⟨-, h1, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h1, h3⟩

/-- **The fold over two-limb operands**: the inc rows are the new rows, the consume count of row `k` is the
number of operands whose old row is `k`. -/
theorem fold_two : ∀ (l : List (ℕ × ℕ)) (a : Array AInfo),
    (∀ vc ∈ l, vc.1 + 1 ≠ p → (Nock.Atoms.limbs vc.1).length = 2 ∧ (Nock.Atoms.limbs (vc.1 + 1)).length = 2) →
    (l.foldl (stepF p acsL rows) a).size = a.size ∧ ∀ k < a.size,
      ((l.foldl (stepF p acsL rows) a).getD k AInfo.z).mhx = (a.getD k AInfo.z).mhx +
        (l.filter fun vc => vc.1 + 1 ≠ p ∧ ComplJ8Data.keyP p acsL (combOf (Nock.Atoms.limbs vc.1)) = k).length ∧
      (((l.foldl (stepF p acsL rows) a).getD k AInfo.z).inc = true ↔ (a.getD k AInfo.z).inc = true ∨
        ∃ vc ∈ l, vc.1 + 1 ≠ p ∧ k = idxOf acsL (combOf (Nock.Atoms.limbs (vc.1 + 1))))
  | [], a, _ => ⟨rfl, fun k _ => ⟨by simp, by simp⟩⟩
  | vc :: l, a, h => by
    have hs := stepF_two p acsL rows a vc 0 (h vc List.mem_cons_self)
    obtain ⟨ih1, ih2⟩ := fold_two l (stepF p acsL rows a vc) fun w hw => h w (List.mem_cons_of_mem _ hw)
    simp only [List.foldl_cons]
    refine ⟨ih1.trans hs.1, fun k hk => ?_⟩
    have hk' : k < (stepF p acsL rows a vc).size := hs.1 ▸ hk
    obtain ⟨-, s2, s3⟩ := stepF_two p acsL rows a vc k (h vc List.mem_cons_self)
    obtain ⟨i2, i3⟩ := ih2 k hk'
    refine ⟨?_, ?_⟩
    · rw [i2, s2, List.filter_cons]
      by_cases hq : vc.1 + 1 ≠ p ∧ ComplJ8Data.keyP p acsL (combOf (Nock.Atoms.limbs vc.1)) = k
      · simp only [hq, hk, and_self, if_true, ne_eq, decide_true, List.length_cons]
        simp only [ne_eq] at hq; simp [hq]; omega
      · rw [if_neg (by tauto), if_neg (by simpa using hq)]; simp
    · rw [i3, s3]
      constructor
      · rintro ((h1 | ⟨h1, -, h3⟩) | ⟨w, hw, h1, h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨vc, List.mem_cons_self, h1, h3⟩
        · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, h1, h3⟩
      · rintro (h1 | ⟨w, hw, h1, h3⟩)
        · exact Or.inl (Or.inl h1)
        · rcases List.mem_cons.mp hw with rfl | hw
          · exact Or.inl (Or.inr ⟨h1, hk, h3⟩)
          · exact Or.inr ⟨w, hw, h1, h3⟩

end IncFold

section BalVI
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.Edit Nock.Edit.GenX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The atom table's old-key denominator, read off the row**: `dC = ρH + recDen 0 γH (idxO, (0, lO), (kRO, vRO))`
at the generator's row `(tabOf …).row i`. -/
theorem dC_key (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length)) (χ : Coins frameJ8 K)
    (pubs : ℕ → K) (i : Fin D.acs.length) :
    HonestA8.dC δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) pubs (colAH δ b D hA o χ pubs) (newBA D) i =
      ComplJ8Bad.ρH δ χ + recDen 0 (ComplJ8Bad.γH δ χ)
        (((((ComplJ8Atom.tabOf D.acs D.info D.mb D.rows).row i).idxO : ℕ) : ZMod p),
          ((0 : ZMod p), ((((ComplJ8Atom.tabOf D.acs D.info D.mb D.rows).row i).lO : ℕ) : ZMod p)),
          (((((ComplJ8Atom.tabOf D.acs D.info D.mb D.rows).row i).kRO : ℕ) : ZMod p),
            ((((ComplJ8Atom.tabOf D.acs D.info D.mb D.rows).row i).vRO : ℕ) : ZMod p))) := by
  rw [ComplJ8OfAtom.dC_eq]
  have ht : ∀ k, 130 ≤ k → k < 205 → (ComplJ8OfAtom.ezA δ b D hA o χ pubs i).trace k = newBA D k i := by
    intro k h1 h2
    rw [ComplJ8Atom.EZ_trace (δF := δ) (b := b) (hinj := hinj) (i := i) (j := k) (h2 := by omega) (h3 := h2)]
    simp [show ¬ k < 130 by omega]
  have t0 := ht 200 (by decide) (by decide)
  have t1 := ht 201 (by decide) (by decide)
  have t2 := ht 202 (by decide) (by decide)
  have t3 := ht 203 (by decide) (by decide)
  simp only [FiniteIO.compress, Walk.rlc, Fin.sum_univ_five, BalanceQ.liftRec, ServeH.keyVec5, AtomChipHQ.oldKey,
    recDen]
  simp [CoeffExpr.eval, cv, t0, t1, t2, t3, ComplJ8Atom.newOf, AtomChipHQ.idxO, AtomChipHQ.lO, AtomChipHQ.kRO,
    AtomChipHQ.vRO, IsScalarTower.algebraMap_apply (ZMod p) K 𝕂′]

theorem combOf_two (x y : ℕ) : Nock.V1J8.Gen.combOf [x, y] = Noun.cell (.atom x) (.atom y) := rfl


theorem row_two (T : ComplJ8Atom.AtomTab) (j : ℕ) {x y : ℕ} (hi : T.inc j = true) (hlo : T.lo j = [x, y]) :
    (T.row j).idxO = T.io j ∧ (T.row j).lO = x ∧ (T.row j).kRO = 0 ∧ (T.row j).vRO = y := by
  simp [ComplJ8Atom.AtomTab.row, hi, hlo]

theorem newBA_inc (D : J8Data p Rg fuel s f r) (i : Fin D.acs.length) :
    newBA D AtomChipHQ.inc i = if (D.info.getD i Nock.V1J8.Gen.AInfo.z).inc then 1 else 0 := by
  show (((ComplJ8Atom.tabOf D.acs D.info D.mb D.rows).row i).inc : ZMod p) = _
  simp only [ComplJ8Atom.AtomTab.row, ComplJ8Atom.tabOf]
  split_ifs <;> simp <;> first | assumption | rfl | simp_all

theorem sum_range_ite_list {R : Type} [AddCommMonoid R] (P : ℕ → Bool) (g : ℕ → R) : ∀ n : ℕ,
    ∑ m ∈ Finset.range n, (if P m = true then g m else 0) = (((List.range n).filter P).map g).sum
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_range_ite_list P g n, List.range_succ, List.filter_append, List.map_append,
      List.sum_append]
    cases hP : P n <;> simp [hP]

theorem toList_eq_range (a : Array Nock.V1J8.Gen.AInfo) :
    a.toList = (List.range a.size).map fun m => a.getD m Nock.V1J8.Gen.AInfo.z := by
  apply List.ext_getElem
  · simp
  · intro m h1 h2
    simp only [Array.length_toList] at h1
    simp [Array.getD_eq_getD_getElem?, h1]

/-- **`balV`'s atom inc terminal at the run, at GENERAL limbs** (GLA): with the recounted `mhx` (`mhxOf`: the inc
rows whose old row is `j`), the inc-weighted old-key LogUp total is the `mhx`-weighted atom cell handle sum.  Every
inc row's old key is the handle key of its old row (`inc_old`, `dC_key`, `aHx_gen`), and `mhx` counts the inc rows
by old row (`sum_serial`).  No limb count, no injectivity. -/
theorem incT_gen (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
    (hpG : p = Nock.Atoms.p) (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hlast : Nock.V1J8.Gen.lastIdxOf (j8DataOf p Rg Rt hgen).acs (ComplJ8Data.combPP p) =
      Nock.V1J8.Gen.idxOf (j8DataOf p Rg Rt hgen).acs (ComplJ8Data.combPP p)) (χ : Coins frameJ8 K) :
      ∑ j ∈ Finset.range (j8DataOf p Rg Rt hgen).acs.length,
        liftQ δ (HonestA8.cNat j (newBA (j8DataOf p Rg Rt hgen) AtomChipHQ.inc)) *
          (HonestA8.dNat δ (HonestA8.dC δ b (acs_pos Rt hgen) (powN (orbJ8 _ (dvdOK_of_rows hpG _ h31)) _)
            (orbJ8 _ (dvdOK_of_rows hpG _ h31)) (ChalsAZJ8.chalsAJ8Z δ χ)
            (pubsAOf δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ)
            (colAH δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ
              (pubsAOf δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ))
            (newBA (j8DataOf p Rg Rt hgen))) j)⁻¹ =
        ∑ j ∈ Finset.range (j8DataOf p Rg Rt hgen).acs.length,
          ((((j8DataOf p Rg Rt hgen).info.getD j Nock.V1J8.Gen.AInfo.z).mhx : ℕ) : 𝕂′) *
            (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen)
              (orbJ8 _ (dvdOK_of_rows hpG _ h31)) j χ)⁻¹ := by
  subst hpG
  set D := j8DataOf Nock.Atoms.p Rg Rt hgen with hD
  set hF := dvdOK_of_rows rfl D h31
  set o := orbJ8 D hF
  have hA : 0 < D.acs.length := acs_pos Rt hgen
  have hmA : D.acs.length ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjA := (powN_ok o (le_two_pow_ht D hmA)).1
  have hg := ComplJ8Atom.genHyp_j8 Rg Rt hgen hax hop5 (ComplJ8OfAtom.rows_le_of_rows31 Rt hgen h31)
  obtain ⟨-, -, htl⟩ := ComplJ8OfAtom.acs_ok Rg Rt hgen hax hop5 h31
  set T := ComplJ8Atom.tabOf D.acs D.info D.mb D.rows with hT
  set G : ℕ → Quad (algebraMap (ZMod Nock.Atoms.p) K δ) := fun j =>
    (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b D hA o j χ)⁻¹ with hG
  set J : ℕ → ℕ := fun m => (T.row m).idxO with hJ
  set C := (List.range D.acs.length).filter fun m => T.inc m with hCdef
  have hlt : ∀ c ∈ D.acs, Nock.V1J8.Gen.idxOf D.acs c < D.acs.length := by
    intro c hc; rw [genIdxOf_eq _ _ hc]; exact List.idxOf_lt_length_of_mem hc
  -- an inc row's old index and fields
  have hold : ∀ m, T.inc m = true → D.acs[J m]? = some (Nock.V1J8.Gen.combOf (T.lo m)) ∧
      J m < D.acs.length ∧ 2 ≤ (T.lo m).length ∧ Nock.V1J8.Gen.combOf (T.lo m) ∈ D.acs := by
    intro m hm
    obtain ⟨-, h2, hmem⟩ := ComplJ8Atom.inc_old _ _ _ _ hg m hm
    obtain ⟨hl, he⟩ := ComplJ8Atom.idxO_copy _ _ _ _ hg m hm
    exact ⟨he, hl, h2, hmem⟩
  -- the inc rows' terms
  have hterm : ∀ j ∈ Finset.range D.acs.length,
      liftQ δ (HonestA8.cNat j (newBA D AtomChipHQ.inc)) *
        (HonestA8.dNat δ (HonestA8.dC δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) (pubsAOf δ b D hA o χ)
          (colAH δ b D hA o χ (pubsAOf δ b D hA o χ)) (newBA D)) j)⁻¹ =
      if T.inc j = true then G (J j) else 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [HonestA8.cNat, HonestA8.dNat, dif_pos hj']
    rw [newBA_inc]
    by_cases hi : T.inc j = true
    · have hi' : (D.info.getD j Nock.V1J8.Gen.AInfo.z).inc = true := hi
      rw [if_pos hi', if_pos hi]
      obtain ⟨eJ, hJn, h2, hmem⟩ := hold j hi
      set l := T.lo j with hl
      rw [dC_key δ b D hA o hinjA χ _ ⟨j, hj'⟩]
      simp only [Fin.val_mk, liftQ, map_one, one_mul, hG]
      have hget : D.acs[J j]'hJn = Nock.V1J8.Gen.combOf l := by
        rw [List.getElem?_eq_getElem hJn] at eJ; exact Option.some.inj eJ
      have hhd : Nock.V1J8.Gen.hdN' D.acs[J j] = .atom (l.headD 0) := by rw [hget, ComplJ8Atom.hd_combOf l h2]
      rw [aHx_gen δ b D hA o hinjA χ (J j) hJn (by rw [hhd]; rfl), hhd]
      have hrow : (T.row j).idxO = J j ∧ (T.row j).lO = l.headD 0 ∧
          (T.row j).kRO = (if 3 ≤ l.length then 1 else 0) ∧
          (T.row j).vRO = (if 3 ≤ l.length then T.ip l else l.getD 1 0) := by
        refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp [ComplJ8Atom.AtomTab.row, hi, hl]
      rw [hrow.1, hrow.2.1, hrow.2.2.1, hrow.2.2.2]
      have htl' := ComplJ8Atom.tl_combOf l h2
      by_cases h3 : 3 ≤ l.length
      · have e2 : Nock.V1J8.Gen.tlN' D.acs[J j] = Nock.V1J8.Gen.combOf l.tail := by rw [hget, htl', if_pos h3]
        have hc : (Nock.V1J8.Gen.tlN' D.acs[J j]).isCell = true := by
          rw [e2]; exact ComplJ8Atom.combOf_isCell _ (by rw [List.length_tail]; omega)
        have hm2 : Nock.V1J8.Gen.combOf l.tail ∈ D.acs := e2 ▸ htl _ (List.getElem_mem _) hc
        have hix : T.ip l = ComplJ8Data.ptrP Nock.Atoms.p D.acs D.rows D.acs[J j] := by
          show ComplJ8Data.ptrP Nock.Atoms.p D.acs D.rows (Nock.V1J8.Gen.combOf l) = _
          rw [hget]
        have hc' : (Nock.V1J8.Gen.combOf l.tail).isCell = true := e2 ▸ hc
        simp only [if_pos h3, hc', if_true, hix, e2, Nock.V1J8.Gen.atomV]
      · have e2 : Nock.V1J8.Gen.tlN' D.acs[J j] = .atom (l.getD 1 0) := by rw [hget, htl', if_neg h3]
        simp only [if_neg h3, e2, Noun.isCell, Bool.false_eq_true, if_false, Nock.V1J8.Gen.atomV]
    · have hi' : ¬ (D.info.getD j Nock.V1J8.Gen.AInfo.z).inc = true := hi
      rw [if_neg hi', if_neg hi]
      simp only [liftQ, map_zero, zero_mul]
  rw [Finset.sum_congr rfl hterm, sum_range_ite_list (fun m => T.inc m) (fun m => G (J m)) D.acs.length]
  have hss := sum_serial D.acs.length J G C (fun m hm => (hold m (List.mem_filter.mp hm).2).2.1)
  rw [hss]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  congr 1
  -- the recounted mhx is the number of inc rows whose old row is `j`
  set Fd := ComplJ8Atom.infoFold Nock.Atoms.p D.acs D.rows with hFd
  have hinfo : D.info = Nock.V1J8.Gen.recountMhx Fd := ComplJ8Atom.infoOfP_eq _ _ _
  have hsz : Fd.size = D.acs.length := by
    have := ComplJ8Atom.recountMhx_size Fd
    rw [← hinfo] at this
    rw [← this]
    exact (ComplJ8Atom.stInv_gen _ _ _ _ hg).size
  have hm : (D.info.getD j Nock.V1J8.Gen.AInfo.z).mhx = Nock.V1J8.Gen.mhxOf Fd j := by
    rw [hinfo, ComplJ8Atom.getD_recountMhx, if_pos (by rw [hsz]; exact hj')]
  rw [hm]
  unfold Nock.V1J8.Gen.mhxOf
  rw [toList_eq_range, hsz, List.filter_map, List.length_map, hCdef, List.filter_filter]
  congr 2
  refine List.filter_congr fun m hmr => ?_
  have hR := ComplJ8Atom.recountMhx_fields Fd m
  have e1 : (Fd.getD m Nock.V1J8.Gen.AInfo.z).inc = T.inc m := by
    show _ = (D.info.getD m Nock.V1J8.Gen.AInfo.z).inc; rw [hinfo, hR.1]
  have e2 : (Fd.getD m Nock.V1J8.Gen.AInfo.z).idxO = (D.info.getD m Nock.V1J8.Gen.AInfo.z).idxO := by
    rw [hinfo, hR.2.2.2.1]
  have e3 : (T.row m).idxO = (D.info.getD m Nock.V1J8.Gen.AInfo.z).idxO :=
    (ComplJ8Atom.row_info _ _ _ _ hg m).2.2.2.1
  simp only [Function.comp, e1, e2, hJ, e3]
  cases T.inc m <;> simp <;> exact Bool.eq_iff_iff.mpr (by simp)

/-- **`balV`'s atom inc terminal at the run** (`hI` of `balV2_of_inc`, every coin): the inc-weighted old-key
LogUp total is the `mhx`-weighted atom cell handle sum. -/
theorem incT_run (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
    (hpG : p = Nock.Atoms.p) (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hlast : Nock.V1J8.Gen.lastIdxOf (j8DataOf p Rg Rt hgen).acs (ComplJ8Data.combPP p) =
      Nock.V1J8.Gen.idxOf (j8DataOf p Rg Rt hgen).acs (ComplJ8Data.combPP p))
    (hbig : ∀ a ∈ (j8DataOf p Rg Rt hgen).bigs, p ≤ a ∧ a < p + 2 ^ 31 ∧
      Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1]) (χ : Coins frameJ8 K) :
      ∑ j ∈ Finset.range (j8DataOf p Rg Rt hgen).acs.length,
        liftQ δ (HonestA8.cNat j (newBA (j8DataOf p Rg Rt hgen) AtomChipHQ.inc)) *
          (HonestA8.dNat δ (HonestA8.dC δ b (acs_pos Rt hgen) (powN (orbJ8 _ (dvdOK_of_rows hpG _ h31)) _)
            (orbJ8 _ (dvdOK_of_rows hpG _ h31)) (ChalsAZJ8.chalsAJ8Z δ χ)
            (pubsAOf δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ)
            (colAH δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ
              (pubsAOf δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ))
            (newBA (j8DataOf p Rg Rt hgen))) j)⁻¹ =
        ∑ j ∈ Finset.range (j8DataOf p Rg Rt hgen).acs.length,
          ((((j8DataOf p Rg Rt hgen).info.getD j Nock.V1J8.Gen.AInfo.z).mhx : ℕ) : 𝕂′) *
            (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen)
              (orbJ8 _ (dvdOK_of_rows hpG _ h31)) j χ)⁻¹ := by
  exact incT_gen δ b Rt hgen hpG hax hop5 h31 hlast χ


theorem balV2_run (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
    (hpG : p = Nock.Atoms.p) (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (((BRun δ b Rt hgen hpG h31).M χ).pubsA CellHQ.pubHQ)
        (((BRun δ b Rt hgen hpG h31).M χ).pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) (((BRun δ b Rt hgen hpG h31).M χ).pubsA AtomChipHQ.pubC)
          (((BRun δ b Rt hgen hpG h31).M χ).pubsA (AtomChipHQ.pubC + 1)) +
        Quad.mk (algebraMap (ZMod p) K δ) (((BRun δ b Rt hgen hpG h31).M χ).pubsV WalkHQ.pubXQ)
          (((BRun δ b Rt hgen hpG h31).M χ).pubsV (WalkHQ.pubXQ + 1)) := by
  have hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31 := by
    have h := h31 (bfsForest [(j8DataOf p Rg Rt hgen).t]).length (by simp [sizesJ8])
    rw [ComplJ8BigBound.data_rows hgen]
    simpa [ComplJ8Data.rowsOfT, j8DataOf] using h
  obtain ⟨hb, -, -, -, -, -, hrI, -, -⟩ := ComplJ8BigBound.bigBound_single hgen hpG (hclA 0) (hclA 1) hRt hop5 hN
  have hbig : ∀ a ∈ (j8DataOf p Rg Rt hgen).bigs, p ≤ a ∧ a < p + 2 ^ 31 ∧
      Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1] :=
    fun a ha => ⟨(hb a ha).1, by have := (hb a ha).2.1; omega, (hb a ha).2.2⟩
  exact balV2_of_inc δ b Rt hgen hpG h31 hbig hrI
    (fun χ => incT_run δ b Rt hgen hpG hax hop5 h31
      (ComplJ8OfAtom.last_eq_of_j8 Rt hgen hpG hop5 hclA hRt h31) hbig χ) χ

end BalVI

/-! ## 10. `balV`'s first clause: the cell validity terminal plus the atom-root terminal is the claim / pin sum -/

section SumAt
variable {R : Type} [CommRing R]

/-- **A count-weighted sum over serials is the record sum** (records of multiplicity `0` may be out of range). -/
theorem sum_sumAt (n : ℕ) (G : ℕ → R) : ∀ L : List (ℕ × ℕ), (∀ q ∈ L, 0 < q.2 → q.1 < n) →
    ∑ j ∈ Finset.range n, ((ComplJ8Data.sumAt L j : ℕ) : R) * G j = (L.map fun q => (q.2 : R) * G q.1).sum
  | [], _ => by simp [ComplJ8Data.sumAt]
  | q :: L, h => by
    have ih := sum_sumAt n G L fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hs : ∀ j, ComplJ8Data.sumAt (q :: L) j = (if q.1 = j then q.2 else 0) + ComplJ8Data.sumAt L j := by
      intro j
      by_cases hq : q.1 = j
      · simp [ComplJ8Data.sumAt, List.filter_cons, hq]
      · simp [ComplJ8Data.sumAt, List.filter_cons, hq]
    simp only [hs, Nat.cast_add, add_mul, Finset.sum_add_distrib, ih, List.map_cons, List.sum_cons]
    congr 1
    by_cases h0 : q.2 = 0
    · simp [h0]
    · have hlt := h q List.mem_cons_self (Nat.pos_of_ne_zero h0)
      simp only [Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq _ _ _, if_pos (Finset.mem_range.mpr hlt)]

theorem sum_map_ite' {α : Type} (P : α → Bool) (g : α → R) : ∀ C : List α,
    ((C.filter P).map g).sum = (C.map fun y => if P y = true then g y else 0).sum
  | [] => rfl
  | c :: cs => by
    by_cases h : P c = true
    · simp [h, List.filter_cons, sum_map_ite' P g cs]
    · simp [h, List.filter_cons, sum_map_ite' P g cs]

end SumAt

section CellPairs
open Nock.V1J8.Gen (hdN' tlN')
variable {R : Type} [CommRing R]

/-- The cell-reference record sum of a noun list. -/
theorem cellPairs_sum (cs : List Noun) (G : ℕ → R) : ∀ l : List Noun,
    ((ComplJ8Data.cellPairs cs l).map fun q => (q.2 : R) * G q.1).sum =
      (l.map fun n => if n.isCell then G (Nock.V1J8.Gen.idxOf cs n) else 0).sum
  | [] => rfl
  | n :: l => by
    have ih := cellPairs_sum cs G l
    cases n with
    | atom v =>
      simp only [ComplJ8Data.cellPairs, List.filterMap_cons] at ih ⊢
      simp [ih, Noun.isCell]
    | cell x y =>
      simp only [ComplJ8Data.cellPairs, List.filterMap_cons] at ih ⊢
      simp [ih, Noun.isCell]

end CellPairs


section ListSums
variable {R : Type} [CommRing R]

theorem sum_flatMap_two (a b : Noun → Noun) (g : Noun → R) : ∀ l : List Noun,
    ((l.flatMap fun n => [a n, b n]).map g).sum = (l.map fun n => g (a n) + g (b n)).sum
  | [] => rfl
  | n :: l => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, sum_flatMap_two a b g l]

theorem bigPairs_sum (f : Noun → Option ℕ) (H : ℕ → R) : ∀ l : List Noun,
    ((l.filterMap fun n => (f n).map fun i => ((i, 1) : ℕ × ℕ)).map fun q => (q.2 : R) * H q.1).sum =
      (l.map fun n => ((f n).map H).getD 0).sum
  | [] => rfl
  | n :: l => by
    have ih := bigPairs_sum f H l
    rcases h : f n with _ | i
    · simp [List.filterMap_cons, h, ih]
    · simp [List.filterMap_cons, h, ih]

end ListSums

section RowsV
open Nock.ComputeTable (FP)
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The validity key of a noun `n` at serial `j` under the encoder `E` (fingerprint, rank limbs, serial). -/
def kOf (E : Noun → FP 𝕂′) (n : Noun) (j : F) : Fin 5 → 𝕂′ :=
  ![(E n).size, (E n).dyck, (E n).leaf,
    Quad.mk _ (algebraMap F K ((n.internal % 2 ^ 62 : ℕ) : F)) (algebraMap F K ((n.internal / 2 ^ 62 : ℕ) : F)),
    liftQ δF j]

/-- Its validity inverse. -/
abbrev gOf (γ ρ : 𝕂′) (E : Noun → FP 𝕂′) (n : Noun) (j : F) : 𝕂′ :=
  (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (kOf δF E n j))⁻¹

/-- The provider inverse of cell row `j`. -/
abbrev cG (γ ρ : 𝕂′) (E : Noun → FP 𝕂′) (cells : List Noun) (j : ℕ) : 𝕂′ :=
  gOf δF γ ρ E (cells.getD j (.atom 0)) (j : F)

/-- A child's cell-reference term. -/
abbrev ccT (γ ρ : 𝕂′) (E : Noun → FP 𝕂′) (cells : List Noun) (n : Noun) : 𝕂′ :=
  if n.isCell then cG δF γ ρ E cells (cells.idxOf n) else 0

/-- A child's big-atom term. -/
abbrev btT (γ ρ : 𝕂′) (E : Noun → FP 𝕂′) (big : Noun → Option ℕ) (n : Noun) : 𝕂′ :=
  if ComplJ8Cell.isBig big n then gOf δF γ ρ E n (((big n).getD 0 : ℕ) : F) else 0

theorem vTerm_rowBE (γ ρ z : 𝕂′) (E : Noun → FP 𝕂′) (big : Noun → Option ℕ) (cells : List Noun)
    (mv mx mx1 : ℕ → ℕ) (k : ℕ) :
    vTermOf δF (cellFillInv δF γ ρ (ComplJ8Enc.cellRowsBE δF E z big cells mv mx mx1 k)) =
      liftQ δF ((mv k : ℕ) : F) * cG δF γ ρ E cells k -
      liftQ δF (ComplJ8Cell.wOf big (hdN (cells.getD k (.atom 0)))) *
        gOf δF γ ρ E (hdN (cells.getD k (.atom 0))) (ComplJ8Cell.idOf cells big (hdN (cells.getD k (.atom 0)))) -
      liftQ δF (ComplJ8Cell.wOf big (tlN (cells.getD k (.atom 0)))) *
        gOf δF γ ρ E (tlN (cells.getD k (.atom 0))) (ComplJ8Cell.idOf cells big (tlN (cells.getD k (.atom 0)))) :=
  rfl

theorem ct_split (γ ρ : 𝕂′) (E : Noun → FP 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (n : Noun)
    (hn : n.isCell = true → n ∈ cells) :
    liftQ δF (ComplJ8Cell.wOf big n) * gOf δF γ ρ E n (ComplJ8Cell.idOf cells big n) =
      ccT δF γ ρ E cells n + btT δF γ ρ E big n := by
  by_cases hc : n.isCell = true
  · have hb : ComplJ8Cell.isBig big n = false := by simp [ComplJ8Cell.isBig, hc]
    have hg := getD_idxOf cells n (hn hc)
    simp only [ccT, btT, cG, hc, hb, if_true, Bool.false_eq_true, if_false, add_zero, hg]
    simp [ComplJ8Cell.wOf, ComplJ8Cell.idOf, hc, liftQ]
  · have hc' : n.isCell = false := by simpa using hc
    by_cases hb : ComplJ8Cell.isBig big n = true
    · simp [ccT, btT, ComplJ8Cell.wOf, ComplJ8Cell.idOf, hc', hb, liftQ]
    · have hb' : ComplJ8Cell.isBig big n = false := by simpa using hb
      simp [ccT, btT, ComplJ8Cell.wOf, ComplJ8Cell.idOf, hc', hb', liftQ]

/-- **The cell validity terminal, generic**: provider terms minus every child's cell and big-atom terms. -/
theorem cvSum_gen (γ ρ z : 𝕂′) (E : Noun → FP 𝕂′) (big : Noun → Option ℕ) (cells : List Noun)
    (mv mx mx1 : ℕ → ℕ)
    (hcl : ∀ y ∈ cells, ((hdN y).isCell = true → hdN y ∈ cells) ∧ ((tlN y).isCell = true → tlN y ∈ cells)) :
    ∑ k ∈ Finset.range cells.length,
        vTermOf δF (cellFillInv δF γ ρ (ComplJ8Enc.cellRowsBE δF E z big cells mv mx mx1 k)) =
      ∑ k ∈ Finset.range cells.length, liftQ δF ((mv k : ℕ) : F) * cG δF γ ρ E cells k -
        (cells.map fun y => ccT δF γ ρ E cells (hdN y) + ccT δF γ ρ E cells (tlN y) +
          (btT δF γ ρ E big (hdN y) + btT δF γ ρ E big (tlN y))).sum := by
  have hrow : ∀ k ∈ Finset.range cells.length,
      vTermOf δF (cellFillInv δF γ ρ (ComplJ8Enc.cellRowsBE δF E z big cells mv mx mx1 k)) =
        liftQ δF ((mv k : ℕ) : F) * cG δF γ ρ E cells k -
          (fun y => ccT δF γ ρ E cells (hdN y) + ccT δF γ ρ E cells (tlN y) +
            (btT δF γ ρ E big (hdN y) + btT δF γ ρ E big (tlN y))) (cells.getD k (.atom 0)) := by
    intro k hk
    have hmem : cells.getD k (.atom 0) ∈ cells := by
      rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hk)]; exact List.getElem_mem _
    rw [vTerm_rowBE, ct_split δF γ ρ E big cells _ (hcl _ hmem).1, ct_split δF γ ρ E big cells _ (hcl _ hmem).2]
    ring
  rw [Finset.sum_congr rfl hrow, Finset.sum_sub_distrib]
  congr 1
  exact sum_range_getD (fun y : Noun => ccT δF γ ρ E cells (hdN y) + ccT δF γ ρ E cells (tlN y) +
    (btT δF γ ρ E big (hdN y) + btT δF γ ρ E big (tlN y))) cells

/-- A claim record is the validity key of its noun. -/
theorem claimVec_kOf (E : Noun → FP 𝕂′) (n : Noun) (j : F) :
    ClaimVS.claimVec δF (E n) j (((n.internal / 2 ^ 62 : ℕ)) : F) (((n.internal % 2 ^ 62 : ℕ)) : F) =
      kOf δF E n j := by
  funext c
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · show Quad.mk _ (algebraMap F K j) 0 = liftQ δF j
    rw [liftQ, Quad.mk_base]

end RowsV

section CellLeaves
open Nock.V1J8.Gen (addCells cellsOfRoots)

theorem addCells_inv (S : List ℕ) : ∀ (n : Noun) (acc : List Noun), (∀ a ∈ Nock.Edit.GenX.leavesOf n, a ∈ S) →
    (∀ y ∈ acc, y.isCell = true ∧ ∀ a ∈ Nock.Edit.GenX.leavesOf y, a ∈ S) →
    ∀ y ∈ addCells n acc, y.isCell = true ∧ ∀ a ∈ Nock.Edit.GenX.leavesOf y, a ∈ S
  | .atom _, acc, _, h => by simpa [addCells] using h
  | .cell u v, acc, hn, h => by
    unfold addCells
    split_ifs
    · exact h
    · have hu : ∀ a ∈ Nock.Edit.GenX.leavesOf u, a ∈ S := fun a ha =>
        hn a (by simp [Nock.Edit.GenX.leavesOf, ha])
      have hv : ∀ a ∈ Nock.Edit.GenX.leavesOf v, a ∈ S := fun a ha =>
        hn a (by simp [Nock.Edit.GenX.leavesOf, ha])
      refine addCells_inv S v _ hv (addCells_inv S u _ hu ?_)
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact h y hy
      · rw [List.mem_singleton] at hy; subst hy; exact ⟨rfl, hn⟩

/-- **Every cell of `cellsOfRoots roots` is a cell whose leaves are leaves of the roots.** -/
theorem cellsOfRoots_inv (roots : List Noun) : ∀ y ∈ cellsOfRoots roots,
    y.isCell = true ∧ ∀ a ∈ Nock.Edit.GenX.leavesOf y, a ∈ roots.flatMap Nock.Edit.GenX.leavesOf := by
  unfold cellsOfRoots
  have key : ∀ (l acc : List Noun), (∀ n ∈ l, ∀ a ∈ Nock.Edit.GenX.leavesOf n, a ∈ roots.flatMap Nock.Edit.GenX.leavesOf) →
      (∀ y ∈ acc, y.isCell = true ∧ ∀ a ∈ Nock.Edit.GenX.leavesOf y, a ∈ roots.flatMap Nock.Edit.GenX.leavesOf) →
      ∀ y ∈ l.foldl (fun acc n => addCells n acc) acc,
        y.isCell = true ∧ ∀ a ∈ Nock.Edit.GenX.leavesOf y, a ∈ roots.flatMap Nock.Edit.GenX.leavesOf := by
    intro l
    induction l with
    | nil => intro acc _ h; exact h
    | cons n l ih =>
      intro acc hl h
      exact ih _ (fun m hm => hl m (List.mem_cons_of_mem _ hm))
        (addCells_inv _ n acc (hl n List.mem_cons_self) h)
  exact key roots [] (fun n hn a ha => List.mem_flatMap.mpr ⟨n, hn, ha⟩) (by simp)

end CellLeaves


section EncLeaf
variable {L : Type} [Field L]

/-- The leaf coordinate of a two-atom cell's fingerprint. -/
theorem enc_leaf2 (z : L) (x y : ℕ) :
    (GlobalCarryRecognizer.enc z (.cell (.atom x) (.atom y))).leaf = (x : L) + z * (y : L) := by
  simp [GlobalCarryRecognizer.enc, NPR.leafF, Noun.leafList, NPR.listPoly, NPR.cpoly, Finset.sum_range_succ]
  ring

end EncLeaf

section AtomRole
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

set_option maxRecDepth 20000 in
/-- **The atom row's `𝕂` roles `0..5` are the cell part's roles** (the honest cell values). -/
theorem ekA_role (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length)) (χ : Coins frameJ8 K)
    (pubs : ℕ → K) (i : Fin D.acs.length) (t : ℕ) (ht : t < 6) :
    (ComplJ8OfAtom.ekA δ b D hA o χ pubs i).trace t =
      roleVal δ (ComplJ8Cell.valsBP δ (γV δ χ) (ρV δ χ) (zA δ χ) (fun _ => none) D.acs (mvA D) (mxAF D)
        (fun _ => 0) (ptA D) i) t := by
  refine gather_trace b _ _ t _ fun k => ?_
  have hk := k.isLt
  have hcol0 : (AtomChipHQ.atomTemplateHQ δ).col0 3 .traceCur t + k = 205 + 3 * t + k := by
    simp only [ChipTemplate.col0, AtomChipHQ.atomTemplateHQ_baseCols]
  have hWA : (AtomChipHQ.atomTemplateHQ δ).width 3 = 349 := HonestA8.atomTemplateHQ_width δ
  have hW' : (cellTemplateHQ δ).width 3 = 238 := CellTraceHQ.cellTemplateHQ_width δ
  have hW : (cellTemplate δ).width 3 = 225 := CellTraceH.cellTemplate_width δ
  rw [hcol0]
  simp only [ComplJ8OfAtom.ezA, HonestA8.EZ]
  rw [env_trace hA (powN o _) hinj _ _ _ _ i (by rw [hWA]; omega)]
  have e0 : 205 + 3 * t + (k : ℕ) ≠ 0 := by omega
  have e1 : 205 + 3 * t + (k : ℕ) ≠ 1 := by omega
  simp only [fullCol, e0, e1, if_false]
  rw [HonestA8.colZ, extColF, if_neg (by omega), if_neg (by omega), if_pos (by rw [hW']; omega)]
  rw [colAH, CellTraceHQ.colHQ, extColF, if_neg (by omega), if_neg (by omega), if_pos (by rw [hW]; omega)]
  rw [aCol, cellCol, if_neg (by omega)]
  have e3 : (205 + 3 * t + (k : ℕ) - (205 - 130) - (130 - 129) - 129) = 3 * t + k := by omega
  simp only [e3]
  rw [show (3 * t + (k : ℕ)) / 3 = t by omega]
  congr 1
  exact Fin.ext (by show (3 * t + (k : ℕ)) % 3 = k; omega)

/-- The atom row's `𝕂′` leaf (roles `4 / 5`) is its comb's fingerprint leaf at `zA`. -/
theorem ekA_leaf (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length)) (χ : Coins frameJ8 K)
    (pubs : ℕ → K) (i : Fin D.acs.length) :
    Quad.mk _ ((ComplJ8OfAtom.ekA δ b D hA o χ pubs i).trace 4) ((ComplJ8OfAtom.ekA δ b D hA o χ pubs i).trace 5) =
      (GlobalCarryRecognizer.enc (zA δ χ) D.acs[(i : ℕ)]).leaf := by
  rw [ekA_role δ b D hA o hinj χ pubs i 4 (by omega), ekA_role δ b D hA o hinj χ pubs i 5 (by omega)]
  simp only [roleVal, show (4 : ℕ) % 2 = 0 from rfl, show (5 : ℕ) % 2 = 1 from rfl, if_true,
    show ((1 : ℕ) = 0) = False from by simp, if_false, show (4 : ℕ) / 2 = 2 from rfl,
    show (5 : ℕ) / 2 = 2 from rfl, Quad.mk_re_im]
  simp [CellVals.qslot, ComplJ8Cell.valsBP, cellFill, cellFillInv, ComplJ8Cell.cellRowsBP, ComplJ8Cell.cellRowBP,
    ComplJ8Cell.cellRowB, cellRow0, List.getD_eq_getElem _ _ i.isLt]

end AtomRole


section BalV1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.Edit Nock.Edit.GenX
open Nock.V1J8.Gen (hdN' tlN')
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The run's cell list is closed under cell children (`hdN` / `tlN` form). -/
theorem cells_cl_run : ∀ y ∈ (j8DataOf p Rg Rt hgen).cells,
    ((hdN y).isCell = true → hdN y ∈ (j8DataOf p Rg Rt hgen).cells) ∧
      ((tlN y).isCell = true → tlN y ∈ (j8DataOf p Rg Rt hgen).cells) := by
  have hclosed : ComplJ8Data.ClP (j8DataOf p Rg Rt hgen).cells [] := ComplJ8Data.cells_closed _
  intro y hy
  cases y with
  | atom v => simp [hdN_eq, tlN_eq, hdN', tlN', Noun.isCell]
  | cell u v =>
    obtain ⟨h1, h2⟩ := hclosed u v hy (by simp)
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rw [hdN_eq] at hc ⊢
      simp only [hdN'] at hc ⊢
      cases u with
      | atom _ => simp [Noun.isCell] at hc
      | cell x y => exact h1 x y rfl
    · rw [tlN_eq] at hc ⊢
      simp only [tlN'] at hc ⊢
      cases v with
      | atom _ => simp [Noun.isCell] at hc
      | cell x y => exact h2 x y rfl

/-- The claim / cell-reference term at the generator's serial. -/
abbrev ccG (χ : Coins frameJ8 K) (n : Noun) : 𝕂′ :=
  if n.isCell then cG δ (γV δ χ) (ρV δ χ) (encR δ χ) (j8DataOf p Rg Rt hgen).cells
    (Nock.V1J8.Gen.idxOf (j8DataOf p Rg Rt hgen).cells n) else 0

theorem ccT_eq (χ : Coins frameJ8 K) (n : Noun) (hn : n.isCell = true → n ∈ (j8DataOf p Rg Rt hgen).cells) :
    ccT δ (γV δ χ) (ρV δ χ) (encR δ χ) (j8DataOf p Rg Rt hgen).cells n = ccG δ Rt hgen χ n := by
  by_cases hc : n.isCell = true
  · simp only [ccT, ccG, hc, if_true, genIdxOf_eq _ _ (hn hc)]
  · simp [ccT, ccG, hc]

/-- **The cell validity terminal at the run**: claim terms plus pin terms minus the big-child terms. -/
theorem cvT_run (χ : Coins frameJ8 K) :
    cvT δ (j8DataOf p Rg Rt hgen) χ =
      ([s, f, r].map fun x => ccG δ Rt hgen χ x).sum +
      ((j8DataOf p Rg Rt hgen).regs.map fun id => cG δ (γV δ χ) (ρV δ χ) (encR δ χ) (j8DataOf p Rg Rt hgen).cells
        ((j8DataOf p Rg Rt hgen).idx id)).sum -
      ((j8DataOf p Rg Rt hgen).cells.map fun y =>
        btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (j8DataOf p Rg Rt hgen)) (hdN y) +
          btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (j8DataOf p Rg Rt hgen)) (tlN y)).sum := by
  have hcl := cells_cl_run (p := p) Rt hgen
  set D := j8DataOf p Rg Rt hgen with hD
  set G := cG δ (γV δ χ) (ρV δ χ) (encR δ χ) D.cells with hG
  set L1 := ComplJ8Data.cellPairs D.cells (D.cells.flatMap fun n => [hdN' n, tlN' n]) with hL1
  set L2 := ComplJ8Data.cellPairs D.cells [s, f, r] with hL2
  set L3 := D.regs.map fun id => (D.idx id, 1) with hL3
  have hr : ∀ L ∈ [L1, L2, L3], ∀ q ∈ L, 0 < q.2 → q.1 < D.cells.length := by
    intro L hL q hq
    refine ComplJ8Data.vRecs_range p Rg Rt hgen q ?_
    simp only [ComplJ8Data.vRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl
    · exact Or.inl hq
    · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr hq)
  have hcnt : ∀ k < D.cells.length, mvF D k = ComplJ8Data.sumAt L1 k + ComplJ8Data.sumAt L2 k +
      ComplJ8Data.sumAt L3 k := by
    intro k hk
    show D.mv.getD k 0 = _
    rw [ComplJ8Data.mv_eq_cnt p Rg Rt hgen k hk, ComplJ8Data.cnt_eq_sumAt]
    simp only [ComplJ8Data.vRecs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [add_assoc]
  have h1 : ∑ k ∈ Finset.range D.cells.length, liftQ δ ((mvF D k : ℕ) : ZMod p) * G k =
      (L1.map fun q => (q.2 : 𝕂′) * G q.1).sum + (L2.map fun q => (q.2 : 𝕂′) * G q.1).sum +
        (L3.map fun q => (q.2 : 𝕂′) * G q.1).sum := by
    rw [Finset.sum_congr rfl (fun k hk => by rw [hcnt k (Finset.mem_range.mp hk)])]
    simp only [liftQ, Nat.cast_add, map_add, map_natCast, add_mul, Finset.sum_add_distrib]
    rw [sum_sumAt _ _ L1 (hr L1 (by simp)), sum_sumAt _ _ L2 (hr L2 (by simp)),
      sum_sumAt _ _ L3 (hr L3 (by simp))]
  have hS1 : (L1.map fun q => (q.2 : 𝕂′) * G q.1).sum =
      (D.cells.map fun y => ccG δ Rt hgen χ (hdN' y) + ccG δ Rt hgen χ (tlN' y)).sum := by
    rw [hL1, cellPairs_sum, sum_flatMap_two]
  have hS2 : (L2.map fun q => (q.2 : 𝕂′) * G q.1).sum = ([s, f, r].map fun x => ccG δ Rt hgen χ x).sum := by
    rw [hL2, cellPairs_sum]
  have hS3 : (L3.map fun q => (q.2 : 𝕂′) * G q.1).sum = (D.regs.map fun id => G (D.idx id)).sum := by
    simp [hL3, List.map_map, Function.comp_def]
  have h2 : (D.cells.map fun y => ccT δ (γV δ χ) (ρV δ χ) (encR δ χ) D.cells (hdN y) +
        ccT δ (γV δ χ) (ρV δ χ) (encR δ χ) D.cells (tlN y) +
        (btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf D) (hdN y) +
          btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf D) (tlN y))).sum =
      (D.cells.map fun y => ccG δ Rt hgen χ (hdN' y) + ccG δ Rt hgen χ (tlN' y)).sum +
        (D.cells.map fun y => btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf D) (hdN y) +
          btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf D) (tlN y)).sum := by
    rw [← List.sum_map_add]
    refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
    rw [ccT_eq δ Rt hgen χ _ (hcl y hy).1, ccT_eq δ Rt hgen χ _ (hcl y hy).2, hdN_eq, tlN_eq]
  unfold cvT
  rw [cvSum_gen δ _ _ _ _ _ _ _ _ _ hcl, ← hG, h1, h2, hS1, hS2, hS3]
  ring

/-- The atom table's `mb` column. -/
theorem newBA_mb (D : J8Data p Rg fuel s f r) (i : Fin D.acs.length) :
    newBA D AtomChipHQ.mb i = ((D.mb.getD i 0 : ℕ) : ZMod p) := by
  show (((ComplJ8Atom.tabOf D.acs D.info D.mb D.rows).row i).mb : ZMod p) = _
  rfl


section Horner2
variable {L : Type} [Field L]
theorem horner_two (z : L) (x y : ℕ) : G5J8.horner z [x, y] = (x : L) + z * (y : L) := by
  simp [G5J8.horner]
end Horner2

/-- The run's orbit. -/
abbrev oR (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) :
    StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataOf p Rg Rt hgen)) :=
  orbJ8 (j8DataOf p Rg Rt hgen) (dvdOK_of_rows hpG _ h31)

/-- The atom-root provider inverse of atom row `j` at the run. -/
abbrev HB (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) (j : ℕ) : 𝕂′ :=
  (HonestA8.dNat δ (HonestA8.dMB δ b (acs_pos Rt hgen) (powN (oR Rt hgen hpG h31) _) (oR Rt hgen hpG h31)
    (ChalsAZJ8.chalsAJ8Z δ χ) (pubsAOf δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (oR Rt hgen hpG h31) χ)
    (colAH δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (oR Rt hgen hpG h31) χ
      (pubsAOf δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (oR Rt hgen hpG h31) χ))
    (newBA (j8DataOf p Rg Rt hgen))) j)⁻¹

/-- A child's atom-root term (the atom table's `mb` consumer). -/
abbrev bhT (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) (n : Noun) : 𝕂′ :=
  ((ComplJ8Data.bigIdOfP p (j8DataOf p Rg Rt hgen).acs n).map (HB δ b Rt hgen hpG h31 χ)).getD 0

/-- **The atom table's `mb` terminal at the run** is the sum of the big-child atom-root terms. -/
theorem mbT_run (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (((BRun δ b Rt hgen hpG h31).M χ).pubsA AtomChipHQ.pubMB)
        (((BRun δ b Rt hgen hpG h31).M χ).pubsA (AtomChipHQ.pubMB + 1)) =
      ((j8DataOf p Rg Rt hgen).cells.map fun y =>
        bhT δ b Rt hgen hpG h31 χ (hdN' y) + bhT δ b Rt hgen hpG h31 χ (tlN' y)).sum := by
  refine ((ComplJ8OfAtom.atomTerms δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (oR Rt hgen hpG h31) χ).2.2.2.1).trans ?_
  obtain ⟨LB, hLB⟩ : ∃ LB, LB = ((j8DataOf p Rg Rt hgen).cells.flatMap fun n => [hdN' n, tlN' n]).filterMap
      fun n => (ComplJ8Data.bigIdOfP p (j8DataOf p Rg Rt hgen).acs n).map fun i => (i, 1) := ⟨_, rfl⟩
  refine (Finset.sum_congr rfl (g := fun j => ((ComplJ8Data.sumAt LB j : ℕ) : 𝕂′) * HB δ b Rt hgen hpG h31 χ j)
    fun j hj => ?_).trans ?_
  · have hj' := Finset.mem_range.mp hj
    have e : HonestA8.cNat j (newBA (j8DataOf p Rg Rt hgen) AtomChipHQ.mb) = ((ComplJ8Data.sumAt LB j : ℕ) : ZMod p) := by
      rw [HonestA8.cNat, dif_pos hj', newBA_mb]
      rw [ComplJ8Data.mb_eq_cnt p Rg Rt hgen j hj', ComplJ8Data.cnt_eq_sumAt]
      simp only [ComplJ8Data.mbRecs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hLB]
    rw [e]
    simp only [liftQ, map_natCast]
  · rw [sum_sumAt _ _ LB (fun q hq => ComplJ8Data.mbRecs_range p Rg Rt hgen q (by
      simp only [ComplJ8Data.mbRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil]; rw [← hLB]; exact hq)),
      hLB, bigPairs_sum (ComplJ8Data.bigIdOfP p (j8DataOf p Rg Rt hgen).acs) (HB δ b Rt hgen hpG h31 χ),
      sum_flatMap_two]

/-- The mb key read off an atom row. -/
theorem keyVec_mb (eK : Nock.Reified.Env K) (eF : Nock.Reified.Env (ZMod p)) :
    keyVec δ 5 (AtomChipHQ.mbKey (F := ZMod p)) eK eF =
      ![Quad.mk _ (eK.chal 37) (eK.chal 38), 0, Quad.mk _ (eK.trace 4) (eK.trace 5), 0, liftQ δ (eF.trace 2)] := by
  funext c
  fin_cases c <;>
    simp [keyVec, AtomChipHQ.mbKey, AtomChipHQ.zAt, ev_chal, ev_zero, ev_var, ev_base, Cell.pR, Cell.idx, cv,
      CoeffExpr.eval]

/-- **The big-atom key identity**: a big child's validity consumer key `(zJ, 0, leafVal zY a, 0, root)` is the atom
table's `mb` provider key of its root row `(zAt, 0, leaf, 0, idx)` (`zAt = zJ`, `zA = zY`, two limbs). -/
theorem big_key (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hl2 : ∀ a ∈ (j8DataOf p Rg Rt hgen).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1])
    (hroot : ∀ a, ComplJ8Data.rootIdxP p (j8DataOf p Rg Rt hgen).acs a =
      Nock.V1J8.Gen.idxOf (j8DataOf p Rg Rt hgen).acs (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)))
    (χ : Coins frameJ8 K) (a : ℕ) (ha : a ∈ (j8DataOf p Rg Rt hgen).bigs) :
    gOf δ (γV δ χ) (ρV δ χ) (encR δ χ) (.atom a)
        ((ComplJ8Data.rootIdxP p (j8DataOf p Rg Rt hgen).acs a : ℕ) : ZMod p) =
      HB δ b Rt hgen hpG h31 χ (ComplJ8Data.rootIdxP p (j8DataOf p Rg Rt hgen).acs a) := by
  have hmem : Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a) ∈ (j8DataOf p Rg Rt hgen).acs :=
    comb_mem_acs Rt hgen hpG ha (by rw [(hl2 a ha).2]; simp)
  have hjE : ComplJ8Data.rootIdxP p (j8DataOf p Rg Rt hgen).acs a =
      List.idxOf (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)) (j8DataOf p Rg Rt hgen).acs := by
    rw [hroot, genIdxOf_eq _ _ hmem]
  have hj : ComplJ8Data.rootIdxP p (j8DataOf p Rg Rt hgen).acs a < (j8DataOf p Rg Rt hgen).acs.length := by
    rw [hjE]; exact List.idxOf_lt_length_of_mem hmem
  have hget : (j8DataOf p Rg Rt hgen).acs[ComplJ8Data.rootIdxP p (j8DataOf p Rg Rt hgen).acs a]'hj =
      Noun.cell (.atom (a + 1 - p)) (.atom (Nock.Atoms.B - 1)) := by
    have key : ∀ (j : ℕ) (hj' : j < (j8DataOf p Rg Rt hgen).acs.length),
        j = List.idxOf (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)) (j8DataOf p Rg Rt hgen).acs →
        (j8DataOf p Rg Rt hgen).acs[j]'hj' = Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a) := by
      intro j hj' e; subst e; exact List.getElem_idxOf _
    rw [key _ hj hjE, (hl2 a ha).2, combOf_two]
  have hmA : (j8DataOf p Rg Rt hgen).acs.length ∈ sizesJ8 (j8DataOf p Rg Rt hgen) := by simp [sizesJ8]
  have hinj := (powN_ok (oR Rt hgen hpG h31) (le_two_pow_ht (j8DataOf p Rg Rt hgen) hmA)).1
  set i : Fin (j8DataOf p Rg Rt hgen).acs.length := ⟨_, hj⟩ with hi
  have hleaf := ekA_leaf δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (oR Rt hgen hpG h31) hinj χ
    (pubsAOf δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (oR Rt hgen hpG h31) χ) i
  have hidx : (ComplJ8OfAtom.ezA δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (oR Rt hgen hpG h31) χ
      (pubsAOf δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (oR Rt hgen hpG h31) χ) i).trace 2 =
      ((ComplJ8Data.rootIdxP p (j8DataOf p Rg Rt hgen).acs a : ℕ) : ZMod p) := by
    rw [ComplJ8Atom.EZ_trace (δF := δ) (b := b) (hinj := hinj) (i := i) (j := 2) (h2 := le_rfl) (h3 := by norm_num),
      if_pos (by norm_num)]
    exact (ComplJ8OfAtom.colAH_fields δ b _ (acs_pos Rt hgen) (oR Rt hgen hpG h31) χ _ i).1
  have hchal := ComplJ8OfAtom.ekA_chal δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (oR Rt hgen hpG h31) χ
    (pubsAOf δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) (oR Rt hgen hpG h31) χ) i
  -- the leaf values
  have hlimbs : ∀ x ∈ Nock.Atoms.limbs a, x < Nock.Atoms.B := fun x hx => (Nock.Atoms.limbs_canonical a).1 x hx
  have hlv := G5J8.leafVal_val (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2)) hlimbs
    (by rw [Nock.Atoms.val_limbs, ← hpG]; exact (hl2 a ha).1)
  rw [Nock.Atoms.val_limbs, (hl2 a ha).2, horner_two] at hlv
  rw [hget, enc_leaf2, ComplJ8OfAtom.zA_eq] at hleaf
  unfold HB gOf
  rw [HonestA8.dNat, dif_pos hj, ComplJ8OfAtom.dMB_eq, InhabJ8Good.compress_split, keyVec_mb, hchal,
    ChalsAZJ8.chalsAJ8Z_zAt, hleaf, hidx]
  refine congrArg (fun x => (ρV δ χ + FiniteIO.compress ⟨γV δ χ, 0⟩ x)⁻¹) ?_
  funext c
  fin_cases c
  · rfl
  · rfl
  · show Nock.Atoms.leafVal (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2)) a = _
    rw [hlv]
    rfl
  · show Quad.mk _ (algebraMap (ZMod p) K ((0 % 2 ^ 62 : ℕ) : ZMod p))
      (algebraMap (ZMod p) K ((0 / 2 ^ 62 : ℕ) : ZMod p)) = 0
    simp only [Nat.zero_mod, Nat.zero_div, Nat.cast_zero, map_zero]
    exact (Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩
  · rfl


/-- The atom children of the run's cells that are big are big atoms of the run. -/
theorem child_big (y : Noun) (hy : y ∈ (j8DataOf p Rg Rt hgen).cells) (n : Noun) (hn : n = hdN y ∨ n = tlN y)
    (a : ℕ) (ha : n = .atom a) (hp : p ≤ a) : a ∈ (j8DataOf p Rg Rt hgen).bigs := by
  obtain ⟨hc, hl⟩ := cellsOfRoots_inv (j8DataOf p Rg Rt hgen).roots y hy
  cases y with
  | atom _ => simp [Noun.isCell] at hc
  | cell u v =>
    have hal : a ∈ Nock.Edit.GenX.leavesOf (.cell u v) := by
      rcases hn with h | h
      · rw [h, hdN_eq] at ha; simp only [hdN'] at ha; subst ha; simp [Nock.Edit.GenX.leavesOf]
      · rw [h, tlN_eq] at ha; simp only [tlN'] at ha; subst ha; simp [Nock.Edit.GenX.leavesOf]
    have hr := hl a hal
    show a ∈ ComplJ8Data.bigsP p (j8DataOf p Rg Rt hgen).roots (j8DataOf p Rg Rt hgen).rows
    refine (ComplJ8Atom.mem_bigsP p _ _ a).mpr ⟨?_, hp⟩
    rw [List.flatMap_append]
    exact List.mem_append_left _ hr

/-- **A child's big-atom consumer term is its atom-root provider term.** -/
theorem bt_bh (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hl2 : ∀ a ∈ (j8DataOf p Rg Rt hgen).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1])
    (hroot : ∀ a, ComplJ8Data.rootIdxP p (j8DataOf p Rg Rt hgen).acs a =
      Nock.V1J8.Gen.idxOf (j8DataOf p Rg Rt hgen).acs (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)))
    (χ : Coins frameJ8 K) (n : Noun) (hn : ∀ a, n = .atom a → p ≤ a → a ∈ (j8DataOf p Rg Rt hgen).bigs) :
    btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (j8DataOf p Rg Rt hgen)) n = bhT δ b Rt hgen hpG h31 χ n := by
  cases n with
  | cell u v => simp [btT, bhT, ComplJ8Cell.isBig, Noun.isCell, ComplJ8Data.bigIdOfP]
  | atom v =>
    by_cases hv : v < p
    · simp [btT, bhT, ComplJ8Cell.isBig, Noun.isCell, ComplJ8Data.bigIdOfP, hv]
    · have hb : ComplJ8Cell.isBig (bigOf (j8DataOf p Rg Rt hgen)) (.atom v) = true := by
        simp [ComplJ8Cell.isBig, Noun.isCell, ComplJ8Data.bigIdOfP, hv]
      simp only [btT, hb, if_true, bhT, bigOf, ComplJ8Data.bigIdOfP, hv, if_false, Option.getD_some,
        Option.map_some]
      exact big_key δ b Rt hgen hpG h31 hl2 hroot χ v (hn v rfl (by omega))

/-- **The claim records' inverse sum** is the claim cell-reference sum. -/
theorem claim_sum (χ : Coins frameJ8 K) :
    ((AcceptsJ8P.claimRecsJ8 δ χ (ComplJ8.cJ s f r)
        (ComplJ8Comp.mCOf (j8DataOf p Rg Rt hgen).H (ComplJ8.cJ s f r))).map fun x =>
      (FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6),
        Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      ([s, f, r].map fun x => ccG δ Rt hgen χ x).sum := by
  have hterm : ∀ x ∈ [s, f, r], (if FrameVS.isCellN x = true then
      (FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩ (ClaimVS.claimVec δ (AcceptsJ8.encJ8 δ χ x)
        (((j8DataOf p Rg Rt hgen).H x).2 : ZMod p) ((AcceptsJ8P.rkC x).1 : ZMod p)
        ((AcceptsJ8P.rkC x).2 : ZMod p)))⁻¹ else 0) = ccG δ Rt hgen χ x := by
    intro x hx
    cases x with
    | atom v => simp [FrameVS.isCellN, ccG, Noun.isCell]
    | cell u v =>
      have hmem := ComplJ8Data.claim_mem_cells p Rg Rt hgen hx (.cell u v) (by simp [Nock.Jet.ChipJ8.subs])
      simp only [FrameVS.isCellN, if_true, ccG, Noun.isCell]
      rw [show ((j8DataOf p Rg Rt hgen).H (.cell u v)).2 =
          Nock.V1J8.Gen.idxOf (j8DataOf p Rg Rt hgen).cells (.cell u v) from rfl, genIdxOf_eq _ _ hmem]
      unfold cG
      rw [getD_idxOf _ _ hmem, AcceptsJ8P.rkC, claimVec_kOf]
  unfold AcceptsJ8P.claimRecsJ8 AcceptsJ8P.claimCells
  rw [List.map_map, sum_map_ite']
  have h3 : List.finRange 3 = [0, 1, 2] := by decide
  rw [h3]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp_def]
  rw [← hterm s (by simp), ← hterm f (by simp), ← hterm r (by simp)]
  rfl

/-- **The registry pin records' inverse sum** is the pin provider sum. -/
theorem pin_sum (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) :
    ((AcceptsJ8P.pinRecsJ8 δ (BRun δ b Rt hgen hpG h31).Pb χ).map fun x =>
      (FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6),
        Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      ((j8DataOf p Rg Rt hgen).regs.map fun id => cG δ (γV δ χ) (ρV δ χ) (encR δ χ) (j8DataOf p Rg Rt hgen).cells
        ((j8DataOf p Rg Rt hgen).idx id)).sum := by
  unfold AcceptsJ8P.pinRecsJ8
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left (l := (j8DataOf p Rg Rt hgen).regs) fun id hid => ?_)
  have hmem : Nock.Jet.Autogen.compile p (Rt id) ∈ (j8DataOf p Rg Rt hgen).cells := by
    have hm : Nock.Jet.Autogen.compile p (Rt id) ∈ (j8DataOf p Rg Rt hgen).roots :=
      List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨id, hid, rfl⟩))
    obtain ⟨a, c, hab⟩ := ComplJ8Data.compile_isCell p (Rt id)
    rw [hab] at hm ⊢
    exact ComplJ8Data.root_mem_cells p Rg Rt hgen hm
  show (FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩ (ClaimVS.claimVec δ
      (encR δ χ (Nock.Jet.Autogen.compile p (Rt id)))
      (((j8DataOf p Rg Rt hgen).idx id : ℕ) : ZMod p)
      ((AcceptsJ8P.rkC (Nock.Jet.Autogen.compile p (Rt id))).1 : ZMod p)
      ((AcceptsJ8P.rkC (Nock.Jet.Autogen.compile p (Rt id))).2 : ZMod p)))⁻¹ = _
  rw [show (j8DataOf p Rg Rt hgen).idx id =
      Nock.V1J8.Gen.idxOf (j8DataOf p Rg Rt hgen).cells (Nock.Jet.Autogen.compile p (Rt id)) from rfl,
    genIdxOf_eq _ _ hmem]
  unfold cG
  rw [getD_idxOf _ _ hmem, AcceptsJ8P.rkC, claimVec_kOf]

/-- **`balV`'s first clause at the run** (every coin): the claim and registry pin records' validity inverses sum to
the cell validity terminal plus the atom table's `mb` terminal. -/
theorem balV1_run (hpG : p = Nock.Atoms.p) (hop5 : ComplJ8.ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) :
    ((AcceptsJ8P.claimRecsJ8 δ χ (ComplJ8.cJ s f r) ((BRun δ b Rt hgen hpG h31).M χ).m ++
        AcceptsJ8P.pinRecsJ8 δ (BRun δ b Rt hgen hpG h31).Pb χ).map fun x => (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6), Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      Quad.mk (algebraMap (ZMod p) K δ) (((BRun δ b Rt hgen hpG h31).M χ).pubsC 0)
          (((BRun δ b Rt hgen hpG h31).M χ).pubsC 1) +
        Quad.mk (algebraMap (ZMod p) K δ) (((BRun δ b Rt hgen hpG h31).M χ).pubsA AtomChipHQ.pubMB)
          (((BRun δ b Rt hgen hpG h31).M χ).pubsA (AtomChipHQ.pubMB + 1)) := by
  have hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31 := by
    have h := h31 (bfsForest [(j8DataOf p Rg Rt hgen).t]).length (by simp [sizesJ8])
    rw [ComplJ8BigBound.data_rows hgen]
    simpa [ComplJ8Data.rowsOfT, j8DataOf] using h
  obtain ⟨hb, -, -, -, -, -, -, -, hroot⟩ :=
    ComplJ8BigBound.bigBound_single hgen hpG (hclA 0) (hclA 1) hRt hop5 hN
  have hl2 : ∀ a ∈ (j8DataOf p Rg Rt hgen).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1] :=
    fun a ha => ⟨(hb a ha).1, (hb a ha).2.2⟩
  have hcv : Quad.mk (algebraMap (ZMod p) K δ) (((BRun δ b Rt hgen hpG h31).M χ).pubsC 0)
      (((BRun δ b Rt hgen hpG h31).M χ).pubsC 1) = cvT δ (j8DataOf p Rg Rt hgen) χ := by
    show Quad.mk _ (pubsCOf δ b _ (cells_pos Rt hgen) (oR Rt hgen hpG h31) χ 0)
      (pubsCOf δ b _ (cells_pos Rt hgen) (oR Rt hgen hpG h31) χ 1) = _
    have e0 : pubsCOf δ b _ (cells_pos Rt hgen) (oR Rt hgen hpG h31) χ 0 = pub2 δ (cvT δ (j8DataOf p Rg Rt hgen) χ) 0 := by
      simp [pubsCOf, pubsC0]
    have e1 : pubsCOf δ b _ (cells_pos Rt hgen) (oR Rt hgen hpG h31) χ 1 = pub2 δ (cvT δ (j8DataOf p Rg Rt hgen) χ) 1 := by
      simp [pubsCOf, pubsC0]
    rw [e0, e1]
    exact pub2_mk2 δ _ 0 rfl
  have hbb : ((j8DataOf p Rg Rt hgen).cells.map fun y =>
      btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (j8DataOf p Rg Rt hgen)) (hdN y) +
        btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (j8DataOf p Rg Rt hgen)) (tlN y)).sum =
      ((j8DataOf p Rg Rt hgen).cells.map fun y =>
        bhT δ b Rt hgen hpG h31 χ (hdN' y) + bhT δ b Rt hgen hpG h31 χ (tlN' y)).sum := by
    refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
    rw [bt_bh δ b Rt hgen hpG h31 hl2 hroot χ _ fun a ha hp => child_big Rt hgen y hy _ (Or.inl rfl) a ha hp,
      bt_bh δ b Rt hgen hpG h31 hl2 hroot χ _ fun a ha hp => child_big Rt hgen y hy _ (Or.inr rfl) a ha hp,
      hdN_eq, tlN_eq]
  rw [show ((BRun δ b Rt hgen hpG h31).M χ).m = ComplJ8Comp.mCOf (j8DataOf p Rg Rt hgen).H (ComplJ8.cJ s f r) from rfl,
    List.map_append, List.sum_append, claim_sum δ Rt hgen χ, pin_sum δ b Rt hgen hpG h31 χ, hcv,
    cvT_run δ Rt hgen χ, mbT_run δ b Rt hgen hpG h31 χ, hbb]
  ring

/-- **`balV` at the run, closed** (`OpenJ8.balV`'s form, nothing carried): clause 1 (`balV1_run`), clause 2
(`balV2_run`), clause 3 (`balV3_run`), at `complJ8`'s binders `hpG hax hop5 hclA hRt h31`. -/
theorem balV_closed (hpG : p = Nock.Atoms.p) (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) :
    ∀ χ, (BRun δ b Rt hgen hpG h31).Good χ →
      ((AcceptsJ8P.claimRecsJ8 δ χ (ComplJ8.cJ s f r) ((BRun δ b Rt hgen hpG h31).M χ).m ++
          AcceptsJ8P.pinRecsJ8 δ (BRun δ b Rt hgen hpG h31).Pb χ).map fun x => (FiniteIO.compress (m := 5)
          ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6), Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
        Quad.mk (algebraMap (ZMod p) K δ) (((BRun δ b Rt hgen hpG h31).M χ).pubsC 0)
            (((BRun δ b Rt hgen hpG h31).M χ).pubsC 1) +
          Quad.mk (algebraMap (ZMod p) K δ) (((BRun δ b Rt hgen hpG h31).M χ).pubsA AtomChipHQ.pubMB)
            (((BRun δ b Rt hgen hpG h31).M χ).pubsA (AtomChipHQ.pubMB + 1)) ∧
      Quad.mk (algebraMap (ZMod p) K δ) (((BRun δ b Rt hgen hpG h31).M χ).pubsA CellHQ.pubHQ)
          (((BRun δ b Rt hgen hpG h31).M χ).pubsA (CellHQ.pubHQ + 1)) =
        Quad.mk (algebraMap (ZMod p) K δ) (((BRun δ b Rt hgen hpG h31).M χ).pubsA AtomChipHQ.pubC)
            (((BRun δ b Rt hgen hpG h31).M χ).pubsA (AtomChipHQ.pubC + 1)) +
          Quad.mk (algebraMap (ZMod p) K δ) (((BRun δ b Rt hgen hpG h31).M χ).pubsV WalkHQ.pubXQ)
            (((BRun δ b Rt hgen hpG h31).M χ).pubsV (WalkHQ.pubXQ + 1)) ∧
      (((BRun δ b Rt hgen hpG h31).M χ).pubsA 0 = 0 ∧ ((BRun δ b Rt hgen hpG h31).M χ).pubsA 1 = 0) :=
  fun χ _ => ⟨balV1_run δ b Rt hgen hpG hop5 hclA hRt h31 χ,
    balV2_run δ b Rt hgen hpG hax hop5 hclA hRt h31 χ, balV3_run δ b Rt hgen hpG h31 χ⟩

end BalV1

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
