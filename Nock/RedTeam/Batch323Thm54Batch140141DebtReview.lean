/-
  Nock/RedTeam/Batch323Thm54Batch140141DebtReview.lean

  Paper re-read at
  source: `:1090-1099`, `:1097`, `:1210-1214`, `:1846-1848`, `:1850-1855`.

  Every named theorem `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/
import Nock.RedTeam.Batch140Thm54CensusReduction
import Nock.RedTeam.Batch141Thm54CensusTerminal
import Nock.NockVMROM.Thm54.GenericHonestCommitment
import Nock.NockVMROM.Thm54.GenericHonestData

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch323

open scoped Classical
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.RedTeam.Batch140
open Nock.RedTeam.Batch141

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! `census_of_leafWindow` is a genuine change of object, not a
rename. `CombinedSkeletonCensus` does not imply `RowLeafWindow` (OP3
row: the census reads `sf 0.result` only under `wut`; the window
bounds the four-leaf noun). The paper window at the paper is
why the trade is legitimate. F97 `RowLeafWindow` was undecided in
that build — a residual, not an inhabitation.

`CommitmentResidual` is inhabited at F97 by a production
term. A2 is an equivalence from three residual fields. The check
*entails* the residual and is strictly stronger (dec-slot witness).
A universal `∀ E, CommitmentResidual E` would force `q = ringChar K`. -/

/-- Census does not imply the window -/
def b323_census_does_not_imply_window :=
  @b140_census_does_not_imply_rowLeafWindow

/-- OP5 third subformula is the atom `0` -/
def b323_s5_third_is_atom :=
  @b140_s5_third_subformula_is_atom

/-- Size coordinate cannot enforce the F97 window -/
def b323_f97_size_blind :=
  @b140_f97_size_coordinate_cannot_enforce_the_window

/-- Check entails the window -/
def b323_window_of_check :=
  @b140_rowLeafWindow_of_canonicalCommitmentCheck

/-- Residual does not imply check (dec-slot witness) -/
def b323_residual_does_not_imply_check :=
  @b141_residual_does_not_imply_check

/-- `CommitmentResidual` inhabited at F97. -/
def b323_commitmentResidual_inhabited :=
  @b141_commitmentResidual_inhabited_at_F97

/-- Universal residual would force `q = ringChar K` -/
def b323_generic_residual_forces_q :=
  @b141_generic_residual_forces_q_equality

/-- `≤` does not force `=`. -/
theorem b323_le_does_not_force_eq :
    ∃ q n : ℕ, 1 < q ∧ q ≤ n ∧ q ≠ n :=
  b141_le_does_not_force_eq

/-- Recorded as a prose defect, not a mathematical one. -/
theorem b323_b140_residual_eta_is_three (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    P = { axisAtoms := P.axisAtoms
          inactiveDec := P.inactiveDec
          q_eq_ringChar := P.q_eq_ringChar } :=
  b140_residualPremises_still_four P

theorem b323_b141_residual_eta_is_three (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    P = { axisAtoms := P.axisAtoms
          inactiveDec := P.inactiveDec
          q_eq_ringChar := P.q_eq_ringChar } :=
  b141_residualPremises_still_four P

/-- Census extras still five on both artifacts. -/
theorem b323_census_still_five {E : BuildableNockExecution F K}
    {P : ResidualPremises E} {M : MemoryRecordPremises E}
    (C : CensusRecordPremises E P M) :
    C = { slotSemantics := C.slotSemantics
          census := C.census
          sizeWindowBound := C.sizeWindowBound
          skeletonBounded := C.skeletonBounded
          combinedBounded := C.combinedBounded } :=
  b140_censusRecordPremises_still_five C

end

#print axioms b323_census_does_not_imply_window
#print axioms b323_s5_third_is_atom
#print axioms b323_f97_size_blind
#print axioms b323_window_of_check
#print axioms b323_residual_does_not_imply_check
#print axioms b323_commitmentResidual_inhabited
#print axioms b323_generic_residual_forces_q
#print axioms b323_le_does_not_force_eq
#print axioms b323_b140_residual_eta_is_three
#print axioms b323_b141_residual_eta_is_three
#print axioms b323_census_still_five

end Nock.RedTeam.Batch323
