/-
  Nock/RedTeam/Batch612Thm54PreseedRestatements.lean

  Notes only; not a pass.

  * The F97 multi-root fixture `traceSatisfactionM` now takes `hhalt : HaltRowsBase
    multiRootExecution.exec`.
  * `Batch580.memory_width_delta` changed MEANING, not only a numeral: it read
    "after-atom width = live + 1" (a delta of one column); it now reads "after-atom width = live"
    (delta zero).  The old statement is now FALSE (`old_memory_width_delta_false`).  The name
    "delta" no longer describes the claim; recorded as a note.
-/
import Nock.RedTeam.Batch580Thm54PreseedChronology
import Nock.NockVMROM.Thm54.MultiRootServedFixture
import Nock.NockVMROM.Thm54.MemoryHaltRowsBase

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch612

open Nock Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.MultiRootServedFixture

local instance prime97r : Fact (Nat.Prime 97) := ⟨by norm_num⟩
-- the fixture module's own local instances (`MultiRootServedFixture.lean:54-58`)
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-- `encS (atom k)` has a base-field leaf. -/
theorem encS_atom_leaf_base (k : ℕ) :
    ∃ a : F97, algebraMap F97 K97cubic a = (encS (Noun.atom k)).leaf :=
  ⟨(k : F97), by
    rw [encS, GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP_leaf, map_natCast]⟩

/-- **The new premise of the F97 multi-root receipt holds.** -/
theorem multiRoot_haltRowsBase :
    MemoryHaltLeavesHonest.HaltRowsBase (F := F97) multiRootExecution.exec := by
  intro row hrow hst
  change row ∈ execS.memoryRows at hrow
  rw [execution_rowsS.2] at hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    simp only [memLabelS, dummyHaltLabelS, aReadOuterLabel, bReadLabel, aDecomposeOuterLabel,
      bDecomposeLabel, aHeadHaltLabel, aReadInnerLabel, bVerifyLabel, bTailHaltLabel,
      aVerifyOuterLabel, bResultHaltLabel, aDecomposeInnerLabel, aInnerHeadHaltLabel,
      aVerifyInnerLabel, aTailHaltLabel, dummyHaltPubS, aReadOuterPub, aDecomposeOuterPub,
      aHeadHaltPub, aReadInnerPub, aVerifyOuterPub, aDecomposeInnerPub, aInnerHeadHaltPub,
      aVerifyInnerPub, aTailHaltPub, bReadPub, bDecomposePub, bVerifyPub, bResultHaltPub,
      bTailHaltPub, reduceCtorEq] at hst ⊢
  · exact encS_atom_leaf_base 0
  · exact encS_atom_leaf_base 4
  · exact encS_atom_leaf_base 9
  · exact encS_atom_leaf_base 7
  · exact encS_atom_leaf_base 0
  · exact encS_atom_leaf_base 2

open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace in
open Nock.NockVMROM.Thm54.BuildableChips in
theorem traceSatisfactionM_unconditional
    (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)
    (hax : FormRAxisBound sampledAssignmentM inputsM.basis)
    (hbasis : FormRBasis inputsM.basis)
    (hwidth : FormRWidth F97) :
    BuildableTraceSatisfaction topologyM tracesM :=
  traceSatisfactionM hmoreM hax hbasis hwidth multiRoot_haltRowsBase

/-! ## `memory_width_delta` changed meaning -/

theorem old_memory_width_delta_false :
    ¬ (Batch580.memoryWidthAfterAtom =
        Thm54Resources.memoryColumns Thm54Resources.deployedExtensionDegree + 1) := by
  rw [Thm54Resources.memoryColumns_deployed]
  decide

theorem new_memory_width_delta :
    Batch580.memoryWidthAfterAtom + 1 =
      Thm54Resources.memoryColumns Thm54Resources.deployedExtensionDegree :=
  Batch580.memory_width_delta

end Nock.RedTeam.Batch612

#print axioms Nock.RedTeam.Batch612.encS_atom_leaf_base
#print axioms Nock.RedTeam.Batch612.multiRoot_haltRowsBase
#print axioms Nock.RedTeam.Batch612.traceSatisfactionM_unconditional
#print axioms Nock.RedTeam.Batch612.old_memory_width_delta_false
