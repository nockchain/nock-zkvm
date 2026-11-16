/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestOp5NC.lean

  **The OP5 depth binder is real** (negative control +
  the one case where it is implied).  Additive; nothing existing changed.

  * `fdN_combN`, `ncRow_not_depthOK`, `ncRow_axis_ge`: two concrete nouns `[0 [0 … 0]]` / `[0 [0 … 1]]`
    (right combs of depth 64) differ only below depth 63; their first-difference axis is `≥ 2^63` and
    `Op5DepthRow` fails.  `ncRowShallow_depthOK` (depth 2) is the positive control: the same row shape passes.
  * `ncRun_*`: the same at RUN level: the program `[5 [1 A] [1 B]]` on subject `0` (`A`, `B` the combs) is a
    successful `genComputeSkeleton` run whose `programAxisBound (airReorder t)` is `< 2^63` (all rows are
    OP5 / OP1, so `honestAx = 0`) while `programOp5DepthOK t` is false: `programAxisBound` does not imply it.
  * `fdN_length_lt_leaves`, `programOp5DepthOK_of_leafBound`: the condition does follow when the window
    `programLeafBound (airReorder t) ≤ 63` (a toy window, far below the real one).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestAxisH
import Nock.NockVMROM.Thm54.VclL.Handle.HonestLeafH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.VclL.Compute

noncomputable section

/-- A right comb of depth `n` ending in `a`: `[0 [0 … a]]`. -/
def combN : ℕ → Noun → Noun
  | 0, a => a
  | n + 1, a => .cell (.atom 0) (combN n a)

theorem fdN_combN : ∀ n : ℕ,
    fdN (combN n (.atom 0)) (combN n (.atom 1)) = (List.replicate n true, .atom 0, .atom 1)
  | 0 => by simp [combN, fdN]
  | n + 1 => by
    simp only [combN, fdN, if_true, fdN_combN n, List.replicate_succ]

/-- The row of an OP5 "≠" whose operands are the depth-`n` combs. -/
def ncRow (n : ℕ) : RowN :=
  { op := 5, s := .atom 0, f := .atom 0, e := .atom 1,
    sf1 := combN n (.atom 0), sf2 := combN n (.atom 1) }

/-- **Negative control**: operands differing only at depth 64 violate the depth condition. -/
theorem ncRow_not_depthOK : ¬ Op5DepthRow (ncRow 64) := by
  intro h
  have := h rfl rfl (by simp [ncRow, fdN_combN])
  simp only [ncRow, fdN_combN, axisOfPath_lt_pow_iff, List.length_replicate] at this
  omega

/-- ... and the first-difference axis is at least `2^63` (it is `2^65 - 1`). -/
theorem ncRow_axis_ge : 2 ^ 63 ≤ axisOfPath (fdN (ncRow 64).sf1 (ncRow 64).sf2).1 := by
  have := (axisOfPath_lt_pow_iff (fdN (ncRow 64).sf1 (ncRow 64).sf2).1).not
  simp only [ncRow, fdN_combN, List.length_replicate] at this ⊢
  omega

/-- **Positive control**: the same row shape with the difference at depth 2 passes. -/
theorem ncRowShallow_depthOK : Op5DepthRow (ncRow 2) := by
  intro _ _ _
  simp only [ncRow, fdN_combN, axisOfPath_lt_pow_iff, List.length_replicate]
  omega

/-! ## Sufficient: a toy window -/

theorem fdN_length_lt_leaves : ∀ a b : Noun, (fdN a b).1.length < a.leaves
  | .atom x, .atom y => by simp [fdN, Noun.leaves]
  | .atom x, .cell y z => by simp [fdN, Noun.leaves]
  | .cell x y, .atom z => by
    have := Noun.one_le_leaves x
    simp [fdN, Noun.leaves]; omega
  | .cell a1 a2, .cell b1 b2 => by
    have h1 := Noun.one_le_leaves a1
    have h2 := Noun.one_le_leaves a2
    by_cases h : a1 = b1
    · subst h
      have ih := fdN_length_lt_leaves a2 b2
      simp only [fdN, if_true, List.length_cons, Noun.leaves]; omega
    · have ih := fdN_length_lt_leaves a1 b1
      simp only [fdN, h, if_false, List.length_cons, Noun.leaves]; omega

/-- With a window `programLeafBound ≤ 63` the operands (child results, `≤` the window) differ within
depth 63 automatically. -/
theorem programOp5DepthOK_of_leafBound {Kg : Type} [Field Kg] {fuel : ℕ} {subject formula result : Noun}
    {t : NTree (GenComputeRow Kg)}
    (h : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (hB : programLeafBound (airReorder t) ≤ 63) : programOp5DepthOK t := by
  refine (forall_bfsRows_iff (P := fun g => Op5DepthRow (rowOfSkel g.skel)) (airReorder t)).mpr ?_
  intro u hu
  have c0 := childT_leaves_le h hB u hu 0
  have c1 := childT_leaves_le h hB u hu 1
  have hrow := rowNounsBound_inTree hB u hu
  have hsub : u.label.skel.subject.leaves ≤ 63 := (leaves_le_rowB_subject _).trans hrow
  have hfor : u.label.skel.formula.leaves ≤ 63 := (leaves_le_rowB_formula _).trans hrow
  have hsm := rowOfSkel_sfm_leaves u.label.skel hfor hsub c0.1 c1.1 c1.2.1 c1.2.2
  intro _ _ _
  have := fdN_length_lt_leaves (rowOfSkel u.label.skel).sf1 (rowOfSkel u.label.skel).sf2
  rw [axisOfPath_lt_pow_iff]
  omega

/-! ## Run-level negative control -/

instance fact_prime_67_nc : Fact (Nat.Prime 67) := ⟨by norm_num⟩

/-- `[5 [1 A] [1 B]]` with `A = [0 [0 … 0]]`, `B = [0 [0 … 1]]` (depth 64). -/
def ncB : Noun := .cell (.atom 1) (combN 64 (.atom 0))
def ncC : Noun := .cell (.atom 1) (combN 64 (.atom 1))
def ncTail : Noun := .cell ncB ncC
def ncProg : Noun := .cell (.atom 5) ncTail

/-- The generated tree of `ncProg` on subject `0`. -/
def ncT : NTree (GenComputeRow (ZMod 67)) :=
  .node (skelNode (genSkelOp5 (.atom 0) ncProg (.atom 5) ncTail ncB ncC (combN 64 (.atom 0))
      (combN 64 (.atom 1)) (Noun.tis (combN 64 (.atom 0)) (combN 64 (.atom 1))))
      [⟨ncProg, ncTail, 3, 0⟩, ⟨ncTail, ncB, 2, 0⟩])
    [.node (skelNode (genSkelOp1 (.atom 0) ncB (combN 64 (.atom 0)) (.atom 1))
        [⟨ncB, combN 64 (.atom 0), 3, 0⟩]) [],
     .node (skelNode (genSkelOp1 (.atom 0) ncC (combN 64 (.atom 1)) (.atom 1))
        [⟨ncC, combN 64 (.atom 1), 3, 0⟩]) []]

theorem ncRun_gen : genComputeSkeleton (K := ZMod 67) 3 (.atom 0) ncProg =
    .ok (ncT, Noun.tis (combN 64 (.atom 0)) (combN 64 (.atom 1))) := by
  simp [genComputeSkeleton, ncProg, ncB, ncC, ncTail, ncT]

theorem root_mem_bfsRows {Kg : Type} [Field Kg] (t : NTree (GenComputeRow Kg)) :
    t.label ∈ bfsRows (airReorder t) := by
  have := (airReorder_label t).symm
  rw [this]
  unfold bfsRows
  exact List.mem_map.mpr ⟨airReorder t,
    (mem_bfsForest _ _).mpr ⟨airReorder t, List.mem_singleton_self _, InTree.here _⟩, rfl⟩

theorem ncT_root_row : (rowOfSkel ncT.label.skel).op = 5 ∧ (rowOfSkel ncT.label.skel).e = .atom 1 ∧
    (rowOfSkel ncT.label.skel).sf1 = combN 64 (.atom 0) ∧
    (rowOfSkel ncT.label.skel).sf2 = combN 64 (.atom 1) := by
  have hne : Noun.tis (combN 64 (.atom 0)) (combN 64 (.atom 1)) = .atom 1 := by
    simp [Noun.tis, combN]
  simp [rowOfSkel, ncT, skelNode, genSkelOp5, childT, ComputeTable.fanoutComp, hne]

/-- **RUN-LEVEL NEGATIVE CONTROL (the depth binder is real).**  The program `[5 [1 A] [1 B]]` on `0`
(`A`, `B` depth-64 combs differing only at the leaf) is a successful run; the OP0/OP9 axis bound holds
trivially (every row is OP5 / OP1, so `programAxisBound (airReorder t) = 0`), yet `programOp5DepthOK t` is
FALSE and the first-difference axis is `≥ 2^63`.  So `programAxisBound < 2^63` does not imply
`programOp5DepthOK`, and `haxisH` genuinely needs the second binder. -/
theorem ncRun_axisBound_lt : programAxisBound (airReorder ncT) < 2 ^ 63 := by
  have hz : ∀ sk : ComputeRowSkeleton, (sk.state = .s5 ∨ sk.state = .s1) → honestAx sk = 0 := by
    intro sk h; rcases h with h | h <;> simp [honestAx, h]
  have : programAxisBound (airReorder ncT) ≤ 0 := by
    refine programAxisBound_le_of_rows _ 0 ?_
    refine (forall_bfsRows_iff (P := fun g => honestAx g.skel ≤ 0) (airReorder ncT)).mpr ?_
    intro u hu
    obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label ncT u hu
    rw [hl]
    cases hu0 with
    | here => exact le_of_eq (hz _ (Or.inl (by simp [ncT, skelNode, genSkelOp5])))
    | sub hs h2 =>
      simp only [ncT, NTree.children, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;>
      · cases h2 with
        | here => exact le_of_eq (hz _ (Or.inr (by simp [skelNode, genSkelOp1])))
        | sub hs' _ => simp [NTree.children] at hs'
  omega

theorem ncRun_not_depthOK : ¬ programOp5DepthOK ncT := by
  intro hd
  have h := hd _ (root_mem_bfsRows ncT)
  obtain ⟨h1, h2, h3, h4⟩ := ncT_root_row
  simp only [Op5DepthRow, h1, h2, h3, h4] at h
  exact ncRow_not_depthOK (by simpa [Op5DepthRow, ncRow] using h)

theorem ncRun_axis_ge : 2 ^ 63 ≤ axisOfPath (fdN (rowOfSkel ncT.label.skel).sf1 (rowOfSkel ncT.label.skel).sf2).1 := by
  obtain ⟨-, -, h3, h4⟩ := ncT_root_row
  rw [h3, h4]; exact ncRow_axis_ge

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
