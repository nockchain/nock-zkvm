/-
  Nock/NockVMROM/Thm54/VclL/Chips/HonestMemFill.lean

  **The honest round-2 fills of the memory tables and the
  fact lemmas they discharge.**

  The B2 columns of a table (the validity / export / path provider and consumer inverses and the
  accumulators) are a FUNCTION of the table's B0 / B1 content (`rows`) and of the IO coins `(γ, ρ)`:
  * `cellFillInv` — `vInv = den(vKey)⁻¹`, `lInv = wL·den(lKey)⁻¹` (zero-weight consumer inverse `= 0`),
    `rInv`, `x0Inv`, `x1Inv`; `cellFill` adds the prefix-sum accumulators `vAcc`, `xAcc`;
  * `pathFillInv` / `pathFill` — `xConsInv`, `pProvInv`, the prefix sums `xAcc`, `pAcc`;
  * `cellFill_facts` / `pathFill_facts`: the B2 halves of `CellMixedFacts` / `PathMixedFacts` follow from the
    row-level B0/B1 facts, the pole conditions (every consumed / provided denominator is nonzero) and the
    terminal values of the four accumulators (which fix the public values: `ρ_V`, `ρ_X + y`, `y`, `ρ_P`).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemPath

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

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

section CellFill
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

/-- The five inverses of a cell row, from its B0 / B1 content and the IO coins `(γ, ρ)`. -/
def cellFillInv (γ ρ : Quad (algebraMap F K δF)) (c : CellVals F (Quad (algebraMap F K δF))) :
    CellVals F (Quad (algebraMap F K δF)) :=
  { c with
    vInv := (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF c))⁻¹
    lInv := liftQ δF c.wL * (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (lKeyOf δF c))⁻¹
    rInv := liftQ δF c.wR * (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (rKeyOf δF c))⁻¹
    x0Inv := (FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF c 0))⁻¹
    x1Inv := (FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF c 1))⁻¹ }

/-- **The honest filled cell row `j`**: inverses and the two prefix-sum accumulators. -/
def cellFill (γ ρ : Quad (algebraMap F K δF)) (rows : ℕ → CellVals F (Quad (algebraMap F K δF)))
    (j : ℕ) : CellVals F (Quad (algebraMap F K δF)) :=
  { cellFillInv δF γ ρ (rows j) with
    vAcc := ∑ k ∈ Finset.range (j + 1), vTermOf δF (cellFillInv δF γ ρ (rows k))
    xAcc := ∑ k ∈ Finset.range (j + 1), xTermOf δF (cellFillInv δF γ ρ (rows k)) }

variable (γ ρ : Quad (algebraMap F K δF)) (rows : ℕ → CellVals F (Quad (algebraMap F K δF)))

theorem cellFill_base (j : ℕ) :
    (cellFill δF γ ρ rows j).idx = (rows j).idx ∧ (cellFill δF γ ρ rows j).mv = (rows j).mv ∧
    (cellFill δF γ ρ rows j).mx = (rows j).mx ∧ (cellFill δF γ ρ rows j).mx1 = (rows j).mx1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The base columns of the filled rows are the base columns of `rows`: the base gate facts transfer. -/
theorem cellBaseFacts_fill {n : ℕ} (i : Fin n)
    (h : CellBaseFacts (fun j : Fin n => rows j) i) :
    CellBaseFacts (fun j : Fin n => cellFill δF γ ρ rows j) i :=
  { serial0 := h.serial0, serialStep := h.serialStep, limbLo := h.limbLo, limbHi := h.limbHi,
    carry_bool := h.carry_bool, wL_bool := h.wL_bool, wR_bool := h.wR_bool, lo_bits := h.lo_bits,
    hi_bits := h.hi_bits, bit_bool := h.bit_bool, atomL := h.atomL, atomR := h.atomR }

theorem vTermOf_cellFill (j : ℕ) :
    vTermOf δF (cellFill δF γ ρ rows j) = vTermOf δF (cellFillInv δF γ ρ (rows j)) := rfl

theorem xTermOf_cellFill (j : ℕ) :
    xTermOf δF (cellFill δF γ ρ rows j) = xTermOf δF (cellFillInv δF γ ρ (rows j)) := rfl

variable {δF}

/-- **The B2 halves of `CellMixedFacts`** at the filled table, given the row facts, the poles and the
terminal values. -/
theorem cellFill_facts (z : Quad (algebraMap F K δF)) (pubs : ℕ → K) {n : ℕ} (i : Fin n)
    (hz : z ≠ 0)
    (hcons : ∀ j < n, (rows j).p = ComputeTable.FP.cons z (rows j).l (rows j).r)
    (hatL : ∀ j < n, (rows j).wL = 0 →
      (rows j).l = ComputeTable.FP.atomFP z (liftQ δF (rows j).aL))
    (hatR : ∀ j < n, (rows j).wR = 0 →
      (rows j).r = ComputeTable.FP.atomFP z (liftQ δF (rows j).aR))
    (hv : ∀ j < n, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (rows j)) ≠ 0)
    (hl : ∀ j < n, (rows j).wL ≠ 0 → FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (lKeyOf δF (rows j)) ≠ 0)
    (hr : ∀ j < n, (rows j).wR ≠ 0 → FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (rKeyOf δF (rows j)) ≠ 0)
    (hx0 : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (rows j) 0) ≠ 0)
    (hx1 : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (rows j) 1) ≠ 0)
    (hVt : ∑ k ∈ Finset.range n, vTermOf δF (cellFillInv δF γ ρ (rows k)) =
      Quad.mk _ (pubs 0) (pubs 1))
    (hXt : ∑ k ∈ Finset.range n, xTermOf δF (cellFillInv δF γ ρ (rows k)) =
      Quad.mk _ (pubs 2) (pubs 3)) :
    CellMixedFacts δF pubs γ ρ z (fun j : Fin n => cellFill δF γ ρ rows j) i := by
  have hi : (i : ℕ) < n := i.isLt
  refine ⟨hz, hcons i hi, hatL i hi, hatR i hi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact inv_mul_cancel₀ (hv i hi)
  · show liftQ δF (rows i).wL * (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (lKeyOf δF (rows i)))⁻¹ *
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (lKeyOf δF (rows i)) = liftQ δF (rows i).wL
    by_cases h : (rows i).wL = 0
    · simp [h, liftQ]
    · rw [mul_assoc, inv_mul_cancel₀ (hl i hi h), mul_one]
  · show liftQ δF (rows i).wR * (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (rKeyOf δF (rows i)))⁻¹ *
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (rKeyOf δF (rows i)) = liftQ δF (rows i).wR
    by_cases h : (rows i).wR = 0
    · simp [h, liftQ]
    · rw [mul_assoc, inv_mul_cancel₀ (hr i hi h), mul_one]
  · intro h; have h' : (rows i).wL = 0 := h; show liftQ δF (rows i).wL * _ = 0; simp [h', liftQ]
  · intro h; have h' : (rows i).wR = 0 := h; show liftQ δF (rows i).wR * _ = 0; simp [h', liftQ]
  · exact inv_mul_cancel₀ (hx0 i hi)
  · exact inv_mul_cancel₀ (hx1 i hi)
  · intro h0
    show ∑ k ∈ Finset.range ((i : ℕ) + 1), _ = _
    rw [h0, Finset.sum_range_one, vTermOf_cellFill]
  · intro hi'
    show ∑ k ∈ Finset.range ((i : ℕ) + 1 + 1), _ = ∑ k ∈ Finset.range ((i : ℕ) + 1), _ + _
    exact Finset.sum_range_succ _ _
  · intro hi'
    show ∑ k ∈ Finset.range ((i : ℕ) + 1), _ = _
    rw [hi', hVt]
  · intro h0
    show ∑ k ∈ Finset.range ((i : ℕ) + 1), _ = _
    rw [h0, Finset.sum_range_one, xTermOf_cellFill]
  · intro hi'
    show ∑ k ∈ Finset.range ((i : ℕ) + 1 + 1), _ = ∑ k ∈ Finset.range ((i : ℕ) + 1), _ + _
    exact Finset.sum_range_succ _ _
  · intro hi'
    show ∑ k ∈ Finset.range ((i : ℕ) + 1), _ = _
    rw [hi', hXt]

end CellFill

section PathFill
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

/-- The two inverses of a path row. -/
def pathFillInv (γ ρ : Quad (algebraMap F K δF)) (c : PathVals F (Quad (algebraMap F K δF))) :
    PathVals F (Quad (algebraMap F K δF)) :=
  { c with
    xConsInv := (FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (pxKeyOf δF c))⁻¹
    pProvInv := (FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (pRecOf δF c))⁻¹ }

/-- **The honest filled path row `j`**: inverses and the two prefix-sum accumulators. -/
def pathFill (γ ρ : Quad (algebraMap F K δF)) (rows : ℕ → PathVals F (Quad (algebraMap F K δF)))
    (j : ℕ) : PathVals F (Quad (algebraMap F K δF)) :=
  { pathFillInv δF γ ρ (rows j) with
    xAcc := ∑ k ∈ Finset.range (j + 1), (pathFillInv δF γ ρ (rows k)).xConsInv
    pAcc := ∑ k ∈ Finset.range (j + 1),
      liftQ δF (rows k).m * (pathFillInv δF γ ρ (rows k)).pProvInv }

variable (γ ρ : Quad (algebraMap F K δF)) (rows : ℕ → PathVals F (Quad (algebraMap F K δF)))

theorem pathBaseFacts_fill {n : ℕ} (i : Fin n)
    (h : PathBaseFacts (fun j : Fin n => rows j) i) :
    PathBaseFacts (fun j : Fin n => pathFill δF γ ρ rows j) i :=
  { side_bool := h.side_bool, first_bool := h.first_bool, last_bool := h.last_bool,
    first0 := h.first0, lastL := h.lastL, firstNext := h.firstNext, len_first := h.len_first,
    len_step := h.len_step, acc_first := h.acc_first, acc_step := h.acc_step,
    root_first := h.root_first, root_step := h.root_step, cert := h.cert, m_mask := h.m_mask,
    bit_bool := h.bit_bool }

variable {δF}

/-- **The B2 halves of `PathMixedFacts`** at the filled path table. -/
theorem pathFill_facts (pubs : ℕ → K) {n : ℕ} (i : Fin n)
    (hrf : ∀ j < n, (rows j).first = 1 → (rows j).root = (rows j).p)
    (hrs : ∀ j, j + 1 < n → (rows j).last = 0 → (rows (j + 1)).root = (rows j).root)
    (hps : ∀ j, j + 1 < n → (rows j).last = 0 → (rows (j + 1)).p = childOf δF (rows j))
    (hx : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (pxKeyOf δF (rows j)) ≠ 0)
    (hp : ∀ j < n, (rows j).last = 1 → FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (pRecOf δF (rows j)) ≠ 0)
    (hXt : ∑ k ∈ Finset.range n, (pathFillInv δF γ ρ (rows k)).xConsInv = Quad.mk _ (pubs 0) (pubs 1))
    (hPt : ∑ k ∈ Finset.range n, liftQ δF (rows k).m * (pathFillInv δF γ ρ (rows k)).pProvInv =
      Quad.mk _ (pubs 2) (pubs 3)) :
    PathMixedFacts δF pubs γ ρ (fun j : Fin n => pathFill δF γ ρ rows j) i := by
  have hi : (i : ℕ) < n := i.isLt
  refine ⟨hrf i hi, fun hi' => hrs i hi', fun hi' => hps i hi', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact inv_mul_cancel₀ (hx i hi)
  · intro hl
    exact inv_mul_cancel₀ (hp i hi hl)
  · intro h0
    show ∑ k ∈ Finset.range ((i : ℕ) + 1), _ = _
    rw [h0, Finset.sum_range_one]; rfl
  · intro hi'
    show ∑ k ∈ Finset.range ((i : ℕ) + 1 + 1), _ = ∑ k ∈ Finset.range ((i : ℕ) + 1), _ + _
    exact Finset.sum_range_succ _ _
  · intro hi'
    show ∑ k ∈ Finset.range ((i : ℕ) + 1), _ = _
    rw [hi', hXt]
  · intro h0
    show ∑ k ∈ Finset.range ((i : ℕ) + 1), _ = _
    rw [h0, Finset.sum_range_one]; rfl
  · intro hi'
    show ∑ k ∈ Finset.range ((i : ℕ) + 1 + 1), _ = ∑ k ∈ Finset.range ((i : ℕ) + 1), _ + _
    exact Finset.sum_range_succ _ _
  · intro hi'
    show ∑ k ∈ Finset.range ((i : ℕ) + 1), _ = _
    rw [hi', hPt]

end PathFill

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
