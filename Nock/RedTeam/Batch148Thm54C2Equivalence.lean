import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.NounRealization
import Nock.RedTeam.Batch143Thm54Batch137Gate
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Equivalence test of designed `C2` (`FPRealizedWithin`)

Construction files were not edited.
It is **not** added to `NounRealization.lean`.

Paper frame (re-read at source):
`Def:Nock Program`, window `NockProgram^Λ` at `1097`.  Consumer
`Corr:ion_single_security` (`1198`).  Census residual
`∀ s ∈ computeSkeletonRows (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
  RowLeafWindow E.Λ s` (`CensusExtraClosure.lean`, cite `1090-1099`).

Consumed capstone: `optimizedFullStrictNockVMROM_of_package` (`«Thm:NockVMROM»`).
Nothing here inhabits a named premise, adds a carrier field, weakens a census predicate,
or ticks a `§J` box.

The **designed encoding-layer field** `FPRealizedWithin` does **not** entail
`RowLeafWindow` on a reconstructed census row, for two independently compiled reasons:

1. **Collision inside the fingerprint.**  At F97's own seed, `q = 97`, `Λ = 7`,
   `enc z (leftComb 16) = enc z (.atom 0)` (`Batch143.b143_f97_enc_collision_across_the_window`).
   Atom `0` witnesses `FPRealizedWithin`; the seventeen-leaf comb does not sit in the window.
   So inhabiting the strengthened existential at a fingerprint does **not** force every
   `BoundedBy q` preimage of that fingerprint into `leaves ≤ Λ`.
2. **Layer mismatch.**  Reconstruction subjects are execution **labels**
   (`reconstructed_row_nouns_are_labels` / `b143_skeleton_subject_is_root`, `rfl`),
   not `chooseNoun` witnesses.  Indexing `FPRealized` by `Λ` does not change that
   equality, so designed `C2` cannot bound the public-triple conjuncts of
   `RowLeafWindow`.

The paper's `NockProgram^Λ` is **not** rejected.  What is declined is the proposed
repair of `FPRealized` as the object that unparks `census`.  `census` stays PARKED.
The `orderOf z ≤ Λ + 1` route is **not** revived.

Disposition is self-reported and ungated.  Do not read this file's presence as
`redteam-status.json` `passed`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch148

open scoped Classical
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.CensusExtraClosure
open Nock.RedTeam.Batch143

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## Shadow of the proposed field — not added to production -/

/-- Shadow only.  Production `FPRealized` (`NounRealization.lean:42-43`) is unchanged. -/
def FPRealizedWithin (z : K) (q Λ : ℕ) (fp : ComputeTable.FP K) : Prop :=
  ∃ n : Noun, FieldEmbedding.BoundedBy q n ∧ n.leaves ≤ Λ ∧
    GlobalCarryRecognizer.enc z n = fp

/-- The designed field strictly implies current `FPRealized`. -/
theorem fpRealized_of_within {z : K} {q Λ : ℕ} {fp : ComputeTable.FP K}
    (h : FPRealizedWithin z q Λ fp) : FPRealized z q fp := by
  obtain ⟨n, hb, _, henc⟩ := h
  exact ⟨n, hb, henc⟩

/-! ## Synthetic OP1 row: colliding subject, windowed formula/evaluation -/

/-- Fanout-zero OP1 row whose **subject** is the seventeen-leaf comb.  Formula and
evaluation are the one-leaf atom `0`.  Inactive subformula slots are `.atom 0` by
`skeletonSubformula`'s `dif_neg` -/
def c2EquivFailRow : ComputeRowSkeleton where
  state := .s1
  subject := leftComb 16
  formula := .atom 0
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => { root := .atom 0, child := .atom 0, axis := 0 }

theorem c2EquivFailRow_fanout_zero :
    ComputeTable.fanoutComp c2EquivFailRow.state = 0 := rfl

/-! ## Equivalence test at the released F97 seed -/

section LiveFixture

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusExecution

local instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

-- Form R leftover first-row counts (live is `chainOneBitWeight`).
variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
include hfirstD

/-- Designed `C2` holds at the colliding fingerprint: atom `0` is the windowed witness. -/
theorem b148_designed_c2_holds_at_colliding_fp :
    FPRealizedWithin (distinctCensusExecution hfirstD).cfg.challenges.z
      (distinctCensusExecution hfirstD).q (distinctCensusExecution hfirstD).Λ
      (GlobalCarryRecognizer.enc (distinctCensusExecution hfirstD).cfg.challenges.z (leftComb 16)) := by
  have hcoll := b143_f97_enc_collision_across_the_window hfirstD
  exact ⟨.atom 0, hcoll.2.2.1, hcoll.2.2.2.1, hcoll.1.symm⟩

/-- Inhabiting designed `C2` at a fingerprint does not window every bounded preimage. -/
theorem b148_within_does_not_window_every_preimage :
    FPRealizedWithin (distinctCensusExecution hfirstD).cfg.challenges.z
      (distinctCensusExecution hfirstD).q (distinctCensusExecution hfirstD).Λ
      (GlobalCarryRecognizer.enc (distinctCensusExecution hfirstD).cfg.challenges.z (leftComb 16)) ∧
      FieldEmbedding.BoundedBy (distinctCensusExecution hfirstD).q (leftComb 16) ∧
        ¬ (leftComb 16).leaves ≤ (distinctCensusExecution hfirstD).Λ :=
  ⟨b148_designed_c2_holds_at_colliding_fp hfirstD,
    (b143_f97_enc_collision_across_the_window hfirstD).2.1,
    (b143_f97_enc_collision_across_the_window hfirstD).2.2.2.2⟩

/-- `RowLeafWindow` fails at the synthetic row: the subject has seventeen leaves against `Λ = 7`.
Fanout is zero, so the subformula conjuncts are `.atom 0` and would pass. -/
theorem b148_rowLeafWindow_fails :
    ¬ RowLeafWindow (distinctCensusExecution hfirstD).Λ c2EquivFailRow := by
  intro h
  have : (c2EquivFailRow.subject).leaves ≤ (distinctCensusExecution hfirstD).Λ := h.1
  simp only [c2EquivFailRow] at this
  rw [b143_leftComb_leaves, show (distinctCensusExecution hfirstD).Λ = 7 from rfl] at this
  omega

/-- **The equivalence test.**  Designed `C2` holds at the row subject's fingerprint, and
`RowLeafWindow` fails at the same row.  Adding `n.leaves ≤ Λ` to the `FPRealized` existential
therefore does not discharge the parked census residual. -/
theorem b148_designed_c2_does_not_entail_rowLeafWindow :
    FPRealizedWithin (distinctCensusExecution hfirstD).cfg.challenges.z
      (distinctCensusExecution hfirstD).q (distinctCensusExecution hfirstD).Λ
      (GlobalCarryRecognizer.enc (distinctCensusExecution hfirstD).cfg.challenges.z
        c2EquivFailRow.subject) ∧
      ¬ RowLeafWindow (distinctCensusExecution hfirstD).Λ c2EquivFailRow := by
  refine ⟨?_, b148_rowLeafWindow_fails hfirstD⟩
  simpa [c2EquivFailRow] using b148_designed_c2_holds_at_colliding_fp hfirstD

end LiveFixture

/-! ## Layer: reconstruction subjects are labels, not choose-witnesses -/

/-- Reconstruction subject is the execution's own label, independently of the public-row
realization.  Indexing that realization by `Λ` cannot change this `rfl`. -/
theorem b148_reconstruction_subject_is_label {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row)) :
    (computeSkeletonOf data pubR).subject = data.root.subject :=
  b143_skeleton_subject_is_root data pubR

/-- Same for formula and evaluation — the other two public-triple conjuncts of `RowLeafWindow`. -/
theorem b148_reconstruction_public_triple_are_labels {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row)) :
    (computeSkeletonOf data pubR).subject = data.root.subject ∧
      (computeSkeletonOf data pubR).formula = data.root.formula ∧
        (computeSkeletonOf data pubR).evaluation = data.root.result :=
  ⟨rfl, rfl, rfl⟩

/-! ## Accounting: nothing moved -/

/-- Accounting: `CensusRecordPremises` is still five named fields -/
theorem b148_censusRecordPremises_still_five {E : BuildableNockExecution F K}
    {P : ResidualPremises E} {M : MemoryRecordPremises E}
    (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } := by
  cases C
  rfl

theorem b148_eleven_one_two : 11 + 1 + 2 = 14 := rfl

#print axioms FPRealizedWithin
#print axioms fpRealized_of_within
#print axioms c2EquivFailRow_fanout_zero
#print axioms b148_designed_c2_holds_at_colliding_fp
#print axioms b148_within_does_not_window_every_preimage
#print axioms b148_rowLeafWindow_fails
#print axioms b148_designed_c2_does_not_entail_rowLeafWindow
#print axioms b148_reconstruction_subject_is_label
#print axioms b148_reconstruction_public_triple_are_labels
#print axioms b148_censusRecordPremises_still_five
#print axioms b148_eleven_one_two

end

end Nock.RedTeam.Batch148
