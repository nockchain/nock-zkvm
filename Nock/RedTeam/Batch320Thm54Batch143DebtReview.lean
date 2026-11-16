/-
  Nock/RedTeam/Batch320Thm54Batch143DebtReview.lean

  Paper re-read at source:
  `:1090-1099`, `:1097`, `:1180-1184`, `:1188-1194`, `:1288-1290`,
  `:1708-1714`.

  Every named theorem `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`
  except `b320_eleven_one_two` / `b320_paper_window_is_seed_free` (axiom-free).
-/
import Nock.RedTeam.Batch143Thm54Batch137Gate
import Nock.NockVMROM.Thm54.GenericHonestCommitment
import Nock.NockVMROM.Thm54.GenericHonestData

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch320

open scoped Classical
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.RedTeam.Batch143

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! `enc z` is not injective on `BoundedBy q` nouns below a
leaf window, at every `q > 0` and every `Λ ≥ 1` with `Λ < orderOf z`.
The mechanism is a left comb of `orderOf z + 1` zero-leaves sharing the
atom-`0` fingerprint. That blocks a non-carrier `chooseNoun` route to
`C2`. The paper's `NockProgram^Λ` window does not
mention a seed, so the Lean hypothesis `leaves < orderOf z` is a
different, seed-dependent object. -/

/-- Comb leaf count, re-measured -/
theorem b320_leftComb_leaves (k : ℕ) : (leftComb k).leaves = k + 1 :=
  b143_leftComb_leaves k

/-- Full three-coordinate collision, re-measured -/
theorem b320_enc_leftComb_collision {K' : Type*} [Field K'] {z : K'}
    (hord : 2 ≤ orderOf z) :
    GlobalCarryRecognizer.enc z (leftComb (orderOf z)) =
      GlobalCarryRecognizer.enc z (.atom 0) :=
  b143_enc_leftComb_collision hord

/-- Route blocked at arbitrary `q`, `Λ` -/
theorem b320_route_blocked {K' : Type*} [Field K'] {z : K'} {q Λ : ℕ}
    (hq : 0 < q) (hΛ : 1 ≤ Λ) (hord : Λ < orderOf z) :
    ∃ real chosen : Noun,
      z ≠ 0 ∧ Λ < orderOf z ∧
        FieldEmbedding.BoundedBy q real ∧ real.leaves ≤ Λ ∧
          FieldEmbedding.BoundedBy q chosen ∧
            GlobalCarryRecognizer.enc z chosen = GlobalCarryRecognizer.enc z real ∧
              ¬ chosen.leaves ≤ Λ :=
  b143_route_blocked hq hΛ hord

/-- The paper window is a comparison of two numerals. No seed occurs. -/
theorem b320_paper_window_is_seed_free (n : Noun) (Λ : ℕ) :
    (n.leaves ≤ Λ) = (n.leaves ≤ Λ) :=
  rfl

/-- Seed-dependence of result 2, re-measured at `ZMod 11` -/
theorem b320_window_hypothesis_is_seed_dependent :
    (leftComb 2).leaves ≤ 3 ∧
      (leftComb 2).leaves < orderOf (3 : ZMod 11) ∧
        ¬ (leftComb 2).leaves < orderOf (-1 : ZMod 11) :=
  b143_window_hypothesis_is_seed_dependent

/-- F97 full-fingerprint collision still elaborates -/
def b320_f97_collision_elaborates :=
  @b143_f97_enc_collision_across_the_window

/-- Reconstruction subject pin still elaborates -/
def b320_skeleton_subject_elaborates :=
  @b143_skeleton_subject_is_root

/-- OP0 certificate-internal `slotSemantics` still elaborates -/
def b320_overlapB_s0_elaborates :=
  @b143_overlapB_s0_from_certificate_fields

/-- `ResidualPremises` is a three-field eta. -/
theorem b320_residualPremises_eta (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    P = { inactiveDec := P.inactiveDec
          axisAtoms := P.axisAtoms
          q_eq_ringChar := P.q_eq_ringChar } := by
  cases P; rfl

/-- `b143_residualPremises_still_four` is the three-conjunct projection,
not an eta. Adding a field would not break it. -/
theorem b320_still_four_is_the_projection (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  b143_residualPremises_still_four P

/-- Census extras still five named fields. -/
theorem b320_census_still_five {E : BuildableNockExecution F K}
    {P : ResidualPremises E} {M : MemoryRecordPremises E}
    (C : CensusRecordPremises E P M) :
    C = { slotSemantics := C.slotSemantics
          census := C.census
          sizeWindowBound := C.sizeWindowBound
          skeletonBounded := C.skeletonBounded
          combinedBounded := C.combinedBounded } :=
  b143_censusRecordPremises_still_five C

/-- Arithmetic identity, not a live field count. -/
theorem b320_eleven_one_two : 11 + 1 + 2 = 14 :=
  b143_eleven_one_two

end

#print axioms b320_leftComb_leaves
#print axioms b320_enc_leftComb_collision
#print axioms b320_route_blocked
#print axioms b320_paper_window_is_seed_free
#print axioms b320_window_hypothesis_is_seed_dependent
#print axioms b320_f97_collision_elaborates
#print axioms b320_skeleton_subject_elaborates
#print axioms b320_overlapB_s0_elaborates
#print axioms b320_residualPremises_eta
#print axioms b320_still_four_is_the_projection
#print axioms b320_census_still_five
#print axioms b320_eleven_one_two

end Nock.RedTeam.Batch320
