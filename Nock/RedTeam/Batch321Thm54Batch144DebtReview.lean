/-
  Nock/RedTeam/Batch321Thm54Batch144DebtReview.lean

  Paper re-read at source:
  `:1097`, `:1210-1214`, `:1212`, `:1728`, `:1846-1848`, `:1850-1855`.

  Every named theorem `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/
import Nock.RedTeam.Batch144Thm54Batch141Gate
import Nock.NockVMROM.Thm54.GenericHonestCommitment
import Nock.NockVMROM.Thm54.GenericHonestData

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch321

open scoped Classical
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.RedTeam.Batch144

noncomputable section

variable {F K : Type} [Field F] 
  [Field K] [Algebra F K]

/-! `CanonicalCommitmentCheck`'s leaf conjunct is strictly
stronger than `RowLeafWindow` even after the four skeleton-layer
predicates (`RowCellIdentities`, `SkeletonSlotSemantics`,
`SkeletonRecordEquations`) are granted. The witness separates at
`memRec 0`, which those predicates do not read. Compiled scope is the four
skeleton predicates, not "every structural premise". -/

/-- The four-predicate separation still holds -/
def b321_residual_does_not_imply_check :=
  @b144_residual_does_not_imply_check

/-- `RowLeafWindow` is literally invariant under `dec` and `memRec`. -/
def b321_window_blind_to_dec_and_memRec :=
  @b144_rowLeafWindow_is_blind_to_dec_and_memRec

/-- Non-degeneracy: the witness passes the check at its true bound 3. -/
def b321_check_holds_at_own_bound :=
  @b144_check_holds_at_its_own_bound

/-- `CommitmentResidual` inhabited at F97 from a second production term. -/
def b321_commitmentResidual_inhabited :=
  @b144_commitmentResidual_inhabited_at_F97

/-- A2 from `bindsAt_of_scan` directly. -/
def b321_a2_direct :=
  @b144_bindsAt_of_commitmentResidual_direct

/-- Layer separation is non-vacuous at concrete rows. -/
theorem b321_layer_separation_nonvacuous :
    AO125.atomRow ≠ AO125.wideRow :=
  b144_layer_separation_is_nonvacuous

/-- `Vcomp` still pins `mr1` at `ComputeTable.lean:665` = the paper.
This is the compute-layer fact that excludes `b144MemRow`. -/
theorem b321_vcomp_pins_mr1
    {inp : ComputeTable.Inputs K} {pub : ComputeTable.Pub K}
    {dec : ComputeTable.Dec K}
    (h : ComputeTable.Vcomp inp pub dec) :
    pub.mr1 = ⟨pub.f, dec.f_t, 3, pub.ln_prev * inp.α⟩ :=
  h.2.1

/-- `ResidualPremises` eta is three fields. -/
theorem b321_residualPremises_eta (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    P = { axisAtoms := P.axisAtoms
          inactiveDec := P.inactiveDec
          q_eq_ringChar := P.q_eq_ringChar } :=
  b144_residualPremises_still_four P

/-- Census extras still five. -/
theorem b321_census_still_five {E : BuildableNockExecution F K}
    {P : ResidualPremises E} {M : MemoryRecordPremises E}
    (C : CensusRecordPremises E P M) :
    C = { slotSemantics := C.slotSemantics
          census := C.census
          sizeWindowBound := C.sizeWindowBound
          skeletonBounded := C.skeletonBounded
          combinedBounded := C.combinedBounded } :=
  b144_censusRecordPremises_still_five C

def b321_census_tight_at_two :=
  @b144_b140_census_is_tight_at_two

end

#print axioms b321_residual_does_not_imply_check
#print axioms b321_window_blind_to_dec_and_memRec
#print axioms b321_check_holds_at_own_bound
#print axioms b321_commitmentResidual_inhabited
#print axioms b321_a2_direct
#print axioms b321_layer_separation_nonvacuous
#print axioms b321_vcomp_pins_mr1
#print axioms b321_residualPremises_eta
#print axioms b321_census_still_five
#print axioms b321_census_tight_at_two

end Nock.RedTeam.Batch321
