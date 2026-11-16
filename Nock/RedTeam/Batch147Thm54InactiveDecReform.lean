import Nock.NockVMROM.Thm54.GenericHonestCommitment
import Nock.NockVMROM.Thm54.TraceGen.Op1Data
import Nock.GlobalCarryRecognizer
import Nock.NockVMROM.Thm54.Walk37.PaperNames
import Nock.RedTeam.Batch91Thm54CompleteFalseAcceptance
import Nock.RedTeam.Batch96Thm54GenericHonestCommitment
import Nock.RedTeam.Batch128Thm54GenericHonestPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Independent spec-redteam of the `inactiveDec` reformulation

Construction files were not edited in this pass.

Paper frame (re-read at source):
Algorithm `V_comp` constrains private `Dec` columns only
for states that use them.  The constraint spec names the
six columns and does not zero-force inactive ones.  Paper-mandated zeros that
must survive: inactive mem records, inactive subformula
`(0,0,0)`, `mem_record₁`.

Consumed capstone:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`
(`«Thm:NockVMROM»`).

Five axes:
1. Vacuity — `BindComputeRow` is not `True` (corrupt active public formula FP);
   a nonzero inactive `f_th` is now accepted on the honest OP1 row.
2. Weakening — `ResidualPremises.inactiveDec` remains a field (now `True`);
   accounting stays `11+1+2`; `DecColumnNounRealization` still realizes active slots.
3. Definitional drift — paper does not mandate inactive private Dec zero;
   paper-mandated zeros still hold; `BindComputeRow` does not imply inactive `decFP = 0`.
4. Axiom leak — `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
5. Wrong layer — negatives reproduced at the consumed capstone / `11+1+2`, not an `MTree` shadow.

Disposition is compiled below.  `InactiveDecPadding = True` scoped to the
former `leanEncoding` extra is the intended `C7` outcome, not a capstone finding,
provided `11+1+2` and the paper zeros still hold.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch147

open scoped Classical
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.TraceGen.Op1Config
open Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton hiding F
open Nock.Framework

noncomputable section

/-! ## Fixtures: corrupt active formula; dirty inactive Dec -/

def badFormulaPub (z α : F) : ComputeTable.Pub F :=
  { computePub z α with f := ⟨1, 0, 0⟩ }

def badFormulaRow (z α : F) : ComputeTable.State × ComputeTable.DTcomp F :=
  (.s1, computeInputs z α, badFormulaPub z α, computeDec z)

def dirtyComputeDec (z : F) : ComputeTable.Dec F :=
  { computeDec z with f_th := ⟨1, 0, 0⟩ }

def dirtyComputeRow (z α : F) : ComputeTable.State × ComputeTable.DTcomp F :=
  (.s1, computeInputs z α, computePub z α, dirtyComputeDec z)

/-! ## Axis 1a. Vacuity: `BindComputeRow` is not trivially `True` -/

/-- The honest OP1 formula `[1 5]` is a two-leaf cell, so `enc 8` has `size = 8^2 ≠ 1`.
    Corrupting the **active** public formula fingerprint therefore fails `BindComputeRow`.
    Uses `enc_size` (`@[simp]`); does not `decide` the noncomputable `enc`. -/
theorem bindComputeRow_not_true_of_corrupt_formula :
    ¬ BindComputeRow seedZ computeSkeletonRow (badFormulaRow seedZ alphaA) := by
  intro h
  obtain ⟨_, _, _, _, hf, _⟩ := h
  simp [bindFP, badFormulaRow, badFormulaPub, computePub] at hf
  have hs := congrArg ComputeTable.FP.size hf
  simp [GlobalCarryRecognizer.enc_size, computeSkeletonRow, formulaNoun,
    headNoun, resultNoun, Noun.leaves, seedZ] at hs
  have hpow : (8 : F) ^ 2 = 64 := by decide
  rw [hpow] at hs
  exact absurd hs (by decide : (1 : F) ≠ 64)

/-! ## Axis 1b. A nonzero inactive Dec slot is now accepted -/

/-- OP1 inactive-slot classifier, independently `decide`d here. -/
theorem s1_four_inactive_dec_slots :
    decActive ComputeTable.State.s1 .f_th = false ∧
      decActive ComputeTable.State.s1 .f_tt = false ∧
      decActive ComputeTable.State.s1 .f_tth = false ∧
      decActive ComputeTable.State.s1 .f_ttt = false := by
  decide

theorem dirty_f_th_ne_zero :
    decFP (dirtyComputeDec seedZ) .f_th ≠ 0 := by
  intro h
  have hs := congrArg ComputeTable.FP.size h
  simp [decFP, dirtyComputeDec] at hs

/-- The honest OP1 `BindComputeRow` proof (`Op1Data.bind_computeRow`) still goes
    through after writing garbage into inactive `f_th`.  The else-branch is `True`. -/
theorem dirty_bind :
    BindComputeRow seedZ computeSkeletonRow (dirtyComputeRow seedZ alphaA) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP,
        computeSkeletonRow, dirtyComputeRow, dirtyComputeDec, computeDec, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp computeSkeletonRow.state) := by
      simp [computeSkeletonRow, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, dirtyComputeRow, computePub]
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, rfl⟩
    · rfl
    · rfl

/-- Dual of the deleted `Batch128.bindComputeRow_dec_else_branch`:
    `BindComputeRow` no longer implies inactive `decFP = 0`. -/
theorem bindComputeRow_does_not_force_inactive_dec_zero :
    BindComputeRow seedZ computeSkeletonRow (dirtyComputeRow seedZ alphaA) ∧
      decFP (dirtyComputeRow seedZ alphaA).2.2.2 .f_th ≠ 0 :=
  ⟨dirty_bind, dirty_f_th_ne_zero⟩

/-- Intended `C7` outcome: the former padding extra is `True` on the dirty row.
    Not a capstone finding. -/
theorem inactiveDecPadding_holds_on_dirty_row :
    InactiveDecPadding (dirtyComputeRow seedZ alphaA) :=
  trivial

theorem inactiveDecPadding_is_True
    (row : ComputeTable.State × ComputeTable.DTcomp F) :
    InactiveDecPadding row :=
  trivial

def f73_vcomp_accepts_nonzero_inactive_dec :=
  Batch96.f73_vcomp_accepts_nonzero_inactive_dec

/-! ## Axis 3. Paper-mandated zeros still live on the dirty accepted row -/

/-- Inactive subformula slots remain `(0,0,0)`.
    OP1 has `fanoutComp s1 = 0`. -/
theorem dirty_bind_inactive_subformula_zero (i : Fin 3) :
    computeSubformulaFPs (dirtyComputeRow seedZ alphaA).2.2.1 i = (0, 0, 0) := by
  obtain ⟨_, _, _, _, _, _, _, hsf, _⟩ := dirty_bind
  have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp computeSkeletonRow.state) := by
    simp [computeSkeletonRow, ComputeTable.fanoutComp]
  simpa [dif_neg hi] using hsf i

/-- Inactive memory records remain `MemRec.zero`.
    OP1 has `recordCount s1 = 1`, so slots 1 and 2 are inactive. -/
theorem dirty_bind_inactive_mem_zero :
    computeMemRec (dirtyComputeRow seedZ alphaA).2.2.1 1 = ComputeTable.MemRec.zero ∧
      computeMemRec (dirtyComputeRow seedZ alphaA).2.2.1 2 = ComputeTable.MemRec.zero := by
  obtain ⟨_, _, _, _, _, _, _, _, hmr⟩ := dirty_bind
  constructor
  · have hi : ¬ ((1 : ℕ) < recordCount computeSkeletonRow.state) := by
      simp [computeSkeletonRow, recordCount]
    simpa [dif_neg hi] using hmr (1 : Fin 3)
  · have hi : ¬ ((2 : ℕ) < recordCount computeSkeletonRow.state) := by
      simp [computeSkeletonRow, recordCount]
    simpa [dif_neg hi] using hmr (2 : Fin 3)

/-- Active private Dec columns are still realized (`DecColumnNounRealization`). -/
theorem dirty_decColumns :
    DecColumnNounRealization 97 (dirtyComputeRow seedZ alphaA) :=
  bindComputeRow_decColumns seedZ_ne_zero computeSkeletonRow_bounded dirty_bind

/-! ## Axis 2 / 5. -/

variable {F' K : Type} [Field F'] [Field K] [Algebra F' K]
variable [FiniteDimensional F' K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-- Four residual premises remain; `inactiveDec` is still a field (now `True`). -/
theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F' K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } :=
  Batch128.residualPremises_eta_still_four_batch128 P

theorem residualPremises_still_projects_inactiveDec
    {E : BuildableNockExecution F' K} (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  residualPremises_still_four P

/-- `inactiveDec_of_residual` is `trivial` after the reform; the field is not deleted. -/
theorem inactiveDec_of_residual_is_trivial
    {E : BuildableNockExecution F' K} (P : ResidualPremises E)
    (i : Fin E.cfg.compRows) :
    InactiveDecPadding (E.exec.computeRowAt i) :=
  inactiveDec_of_residual P i

variable [Fintype F'] [DecidableEq F']

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen
    (P : OptimizedFullStrictNockVMROMPackage F' K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F') :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  Batch128.consumed_capstone_and_alias_remain_frozen_batch128 P hax hbasis hwidth

theorem independent_exact_eleven_one_two_accounting :
    Batch128.substantiveFields128.length = 11 ∧
      Batch128.typeSummaryFields128.length = 1 ∧
      Batch128.residualFields128 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      Batch128.residualFields128.length = 2 ∧
      (Batch128.substantiveFields128 ++ Batch128.typeSummaryFields128 ++
        Batch128.residualFields128).Nodup ∧
      11 + 1 + 2 = 14 :=
  Batch128.independent_exact_eleven_one_two_accounting_batch128

/-- Paper-mandated inactive-subformula zero, still a theorem of `evalV`. -/
theorem paper_evalV_inactive_subformula_zero
    {inp : ComputeTable.Inputs K} {pub : ComputeTable.Pub K} {dec : ComputeTable.Dec K}
    (h : ComputeTable.evalV inp pub dec)
    (i : Fin 3) (hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp pub.state)) :
    computeSubformulaFPs pub i = (0, 0, 0) :=
  evalV_inactive_subformula_zero h i hi

/-- Paper-mandated inactive mem zero, still a theorem of `ComputeRowAccepted`. -/
theorem paper_bindMemRec_inactive {cfg : ExactConfig F' K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (i : Fin 3) (hi : ¬ ((i : ℕ) < recordCount row.1)) :
    computeMemRec row.2.2.1 i = ComputeTable.MemRec.zero :=
  bindMemRec_inactive hacc i hi

/-- Paper-mandated `mem_record₁`, still a theorem of `Vcomp`. -/
theorem paper_vcomp_mr1 {cfg : ExactConfig F' K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hacc : ExactExecution.ComputeRowAccepted cfg row) :
    row.2.2.1.mr1 =
      ⟨row.2.2.1.f, row.2.2.2.f_t, 3, row.2.2.1.ln_prev * row.2.1.α⟩ :=
  vcomp_mr1 hacc

end

/-! ## Axis 4. -/

#print axioms BindComputeRow
#print axioms DecColumnNounRealization
#print axioms bindComputeRow_of_axisAtoms
#print axioms bindComputeRow_of_residual
#print axioms inactiveDec_of_residual
#print axioms residualPremises_still_four
#print axioms optimizedFullStrictNockVMROM_of_package
#print axioms evalV_inactive_subformula_zero
#print axioms bindMemRec_inactive
#print axioms bindMemRec_mr1
#print axioms vcomp_mr1
#print axioms bindComputeRow_not_true_of_corrupt_formula
#print axioms s1_four_inactive_dec_slots
#print axioms dirty_f_th_ne_zero
#print axioms dirty_bind
#print axioms bindComputeRow_does_not_force_inactive_dec_zero
#print axioms inactiveDecPadding_holds_on_dirty_row
#print axioms inactiveDecPadding_is_True
#print axioms f73_vcomp_accepts_nonzero_inactive_dec
#print axioms dirty_bind_inactive_subformula_zero
#print axioms dirty_bind_inactive_mem_zero
#print axioms dirty_decColumns
#print axioms residualPremises_eta_still_four
#print axioms residualPremises_still_projects_inactiveDec
#print axioms inactiveDec_of_residual_is_trivial
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms independent_exact_eleven_one_two_accounting
#print axioms paper_evalV_inactive_subformula_zero
#print axioms paper_bindMemRec_inactive
#print axioms paper_vcomp_mr1

end Nock.RedTeam.Batch147
