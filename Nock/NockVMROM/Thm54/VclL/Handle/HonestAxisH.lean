/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestAxisH.lean

  Additive; no handle accumulator, coin or IO summand
  is touched; no existing module edited.

  * `Op5DepthRow r` / `programOp5DepthOK t`: every OP5 "≠" row of the run's AIR-reordered tree whose first
    difference is not at the root has first-difference axis `< 2^63`, equivalently its two operands differ
    within depth 63 (`op5DepthRow_iff_length`).  Decidable (`instDecidableProgramOp5DepthOK`), hence computable
    from the run's rows.
  * `haxisH_of_run`: every consumed axis of `consEntriesAll (runRowsH t)` (OP0, OP9 and the OP5 first-difference
    pair) is `< 2^63`, from `programAxisBound (airReorder t) < 2^63 ∧ programOp5DepthOK t`.  The OP0/OP9 axes are
    `honestAx` (`programAxisBound` covers them); the OP5 pair axes are NOT covered by `programAxisBound`, whence
    the second conjunct.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestSizeH
import Nock.NockVMROM.Thm54.VclL.Compute.Hax63

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.VclL.Compute

noncomputable section

/-! ## 1. The depth condition -/

/-- **The OP5 depth condition at one honest row**: if the row is an OP5 "≠" (result `1`) whose first
difference is not at the root, the axis of that difference is `< 2^63`. -/
def Op5DepthRow (r : RowN) : Prop :=
  r.op = 5 → r.e = .atom 1 → (fdN r.sf1 r.sf2).1 ≠ [] → axisOfPath (fdN r.sf1 r.sf2).1 < 2 ^ 63

instance (r : RowN) : Decidable (Op5DepthRow r) := by unfold Op5DepthRow; infer_instance

/-- **`programOp5DepthOK t`**: every OP5 "≠" row of the run's AIR-reordered tree has first-difference axis
`< 2^63` (its operands differ within depth 63). -/
def programOp5DepthOK {Kg : Type} [Field Kg] (t : NTree (GenComputeRow Kg)) : Prop :=
  ∀ g ∈ bfsRows (airReorder t), Op5DepthRow (rowOfSkel g.skel)

instance instDecidableProgramOp5DepthOK {Kg : Type} [Field Kg] (t : NTree (GenComputeRow Kg)) :
    Decidable (programOp5DepthOK t) := by
  unfold programOp5DepthOK; infer_instance

/-- The Boolean form, computable from the run. -/
def programOp5DepthOKb {Kg : Type} [Field Kg] (t : NTree (GenComputeRow Kg)) : Bool :=
  decide (programOp5DepthOK t)

theorem programOp5DepthOKb_iff {Kg : Type} [Field Kg] (t : NTree (GenComputeRow Kg)) :
    programOp5DepthOKb t = true ↔ programOp5DepthOK t := by
  simp [programOp5DepthOKb]

theorem pow_le_axisFold (bits : List Bool) : 2 ^ bits.length ≤ axisFold bits := by
  induction bits using List.reverseRecOn with
  | nil => simp [axisFold]
  | append_singleton bs b ih =>
    rw [axisFold_append]; simp only [List.length_append, List.length_singleton]
    rw [pow_succ]; split_ifs <;> omega

/-- The length form of the condition: the axis of a path is `< 2^63` iff the path has `< 63` edges. -/
theorem axisOfPath_lt_pow_iff (p : List Bool) : axisOfPath p < 2 ^ 63 ↔ p.length < 63 := by
  rw [axisOfPath_eq]
  constructor
  · intro h
    by_contra hc
    have h1 : 2 ^ 63 ≤ 2 ^ p.length := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := pow_le_axisFold p
    omega
  · intro h
    have h1 := axisFold_lt p
    have h2 : 2 ^ (p.length + 1) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- **The condition as "the operands differ within depth 63"**. -/
theorem op5DepthRow_iff_length (r : RowN) :
    Op5DepthRow r ↔ (r.op = 5 → r.e = .atom 1 → (fdN r.sf1 r.sf2).1 ≠ [] → (fdN r.sf1 r.sf2).1.length < 63) := by
  unfold Op5DepthRow
  simp only [axisOfPath_lt_pow_iff]

/-! ## 2. `haxisH` from the run -/

section Axis
variable {Kg : Type} [Field Kg]

theorem rH_e (sk : ComputeRowSkeleton) : (rowOfSkelH sk).e = (rowOfSkel sk).e := by
  unfold rowOfSkelH
  by_cases h : (rowOfSkel sk).op = 3 <;> simp [h]

/-- OP0: the consumed axis is `honestAx`. -/
theorem op0_axis_eq (sk : ComputeRowSkeleton) (hop : (rowOfSkel sk).op = 0) (hs : (rowOfSkel sk).Sem) :
    honestAx sk = atomVal (rowOfSkel sk).ft := by
  have hst : sk.state = .s0 := by
    unfold rowOfSkel at hop; split at hop <;> simp_all
  have hf0 : (rowOfSkel sk).f = sk.formula := by simp [rowOfSkel, hst]
  simp only [RowN.Sem, hop] at hs
  obtain ⟨-, hf, ax, hft, -⟩ := hs
  have hfl : sk.formula = .cell (rowOfSkel sk).fh (.atom ax) := by rw [← hf0, hf, hft]
  rw [hft]
  unfold honestAx
  rw [hst, hfl]
  simp [atomVal]

/-- OP9: the consumed axis is `honestAx`. -/
theorem op9_axis_eq (sk : ComputeRowSkeleton) (hop : (rowOfSkel sk).op = 9) (hs : (rowOfSkel sk).Sem) :
    honestAx sk = atomVal (rowOfSkel sk).fth := by
  have hst : sk.state = .s9 := by
    unfold rowOfSkel at hop; split at hop <;> simp_all
  have hf0 : (rowOfSkel sk).f = sk.formula := by simp [rowOfSkel, hst]
  simp only [RowN.Sem, hop] at hs
  obtain ⟨-, hf, hft, -, ax, hfth, -⟩ := hs
  have hfl : sk.formula = .cell (rowOfSkel sk).fh (.cell (.atom ax) (rowOfSkel sk).ftt) := by
    rw [← hf0, hf, hft, hfth]
  rw [hfth]
  unfold honestAx
  rw [hst, hfl]
  simp [atomVal]

/-- **`haxisH` from the run.**  Every consumed axis is `< 2^63` from `programAxisBound < 2^63` (the OP0 / OP9
axes) and `programOp5DepthOK` (the OP5 first-difference pair). -/
theorem haxisH_of_run {fuel : ℕ} {subject formula result : Noun} {t : NTree (GenComputeRow Kg)}
    (h : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (hax : programAxisBound (airReorder t) < 2 ^ 63) (hd : programOp5DepthOK t) :
    ∀ x ∈ consEntriesAll (runRowsH t), x.2.1 < 2 ^ 63 := by
  intro x hx
  obtain ⟨g, hg, hx⟩ := List.mem_flatMap.mp hx
  have hsem := run_rows_sem h g hg
  have hAx : honestAx g.skel < 2 ^ 63 :=
    lt_of_le_of_lt (rowAx_le_programAxisBound (airReorder t) g hg) hax
  by_cases h5 : (rowOfSkel g.skel).op = 5
  · have hop : (rowOfSkelH g.skel).op = 5 := by rw [rowOfSkelH_op]; exact h5
    have hd5 := hd g hg
    simp only [Op5DepthRow] at hd5
    have hE : (hn (rowOfSkelH g.skel)).e = (rowOfSkel g.skel).e := by simp [hn, hop, rH_e]
    have h1 : (hn (rowOfSkelH g.skel)).sf1 = (rowOfSkel g.skel).sf1 := by simp [hn, hop, rH_sf1]
    have h2 : (hn (rowOfSkelH g.skel)).sf2 = (rowOfSkel g.skel).sf2 := by simp [hn, hop, rH_sf2]
    have hm : (hn (rowOfSkelH g.skel)).m =
        .atom (axisOfPath (fdN (rowOfSkel g.skel).sf1 (rowOfSkel g.skel).sf2).1) := by
      simp [hn, hop, rH_sf1, rH_sf2]
    have ht1 : (hn (rowOfSkelH g.skel)).ftth =
        (fdN (rowOfSkel g.skel).sf1 (rowOfSkel g.skel).sf2).2.1 := by simp [hn, hop, rH_sf1, rH_sf2]
    have ht2 : (hn (rowOfSkelH g.skel)).fttt =
        (fdN (rowOfSkel g.skel).sf1 (rowOfSkel g.skel).sf2).2.2 := by simp [hn, hop, rH_sf1, rH_sf2]
    have hop' : (hn (rowOfSkelH g.skel)).op = 5 := by simp [hn, hop]
    unfold consEntries at hx
    rw [hop', hE, h1, h2, hm, ht1, ht2] at hx
    simp only [show ¬ ((5 : ℕ) = 0) by omega, show ¬ ((5 : ℕ) = 9) by omega, false_and, if_false,
      List.nil_append, List.append_nil, true_and] at hx
    by_cases hc : (rowOfSkel g.skel).e = .atom 1 ∧
        (fdN (rowOfSkel g.skel).sf1 (rowOfSkel g.skel).sf2).1 ≠ []
    · rw [if_pos hc] at hx
      have hlt := hd5 h5 hc.1 hc.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simpa [atomVal] using hlt
    · rw [if_neg hc] at hx
      simp at hx
  · have hop5 : (rowOfSkelH g.skel).op ≠ 5 := by rw [rowOfSkelH_op]; exact h5
    rw [hn_of_ne _ hop5] at hx
    have hop' : (rowOfSkelH g.skel).op = (rowOfSkel g.skel).op := rowOfSkelH_op _
    unfold consEntries at hx
    have h5' : ¬ ((rowOfSkelH g.skel).op = 5 ∧ (rowOfSkelH g.skel).e = .atom 1 ∧
        (fdN (rowOfSkelH g.skel).sf1 (rowOfSkelH g.skel).sf2).1 ≠ []) := fun h => hop5 h.1
    rw [if_neg h5', List.append_nil] at hx
    rcases List.mem_append.mp hx with hx | hx
    · by_cases hc : (rowOfSkelH g.skel).op = 0 ∧ (rowOfSkelH g.skel).ft ≠ .atom 1
      · rw [if_pos hc] at hx
        simp only [List.mem_singleton] at hx
        subst hx
        have hop0 : (rowOfSkel g.skel).op = 0 := by rw [← hop']; exact hc.1
        have hne3 : (rowOfSkel g.skel).op ≠ 3 := by omega
        rw [rowOfSkelH_of_ne _ hne3]
        have := op0_axis_eq g.skel hop0 hsem
        show atomVal _ < 2 ^ 63
        rw [← this]; exact hAx
      · rw [if_neg hc] at hx; simp at hx
    · by_cases hc : (rowOfSkelH g.skel).op = 9 ∧ (rowOfSkelH g.skel).fth ≠ .atom 1
      · rw [if_pos hc] at hx
        simp only [List.mem_singleton] at hx
        subst hx
        have hop9 : (rowOfSkel g.skel).op = 9 := by rw [← hop']; exact hc.1
        have hne3 : (rowOfSkel g.skel).op ≠ 3 := by omega
        rw [rowOfSkelH_of_ne _ hne3]
        have := op9_axis_eq g.skel hop9 hsem
        show atomVal _ < 2 ^ 63
        rw [← this]; exact hAx
      · rw [if_neg hc] at hx; simp at hx

end Axis

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
