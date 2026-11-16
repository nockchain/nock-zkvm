import Nock.RedTeam.Batch133Thm54ForestExponentOrder
import Nock.RedTeam.Batch134Thm54ForestExponentClosure

/-!
**No carrier field is
added**, no production mathematics is edited, and no named premise of the released capstone is
weakened.  Nothing here describes the paper construction as defective.

## §a.

The
production docstring's `0 < orderOf α` side condition is therefore required, not decorative.

## §b.

The inference does not hold in either direction.

That corollary is compiled here
(`b134b_window_read_verify_exponents_unchanged`) so the ledger claim and the artifact agree
literally.  Full committed-template equality under the window is **not** claimed and is not proved.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch134b

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.NockVMROM.Thm54.ForestExponentWindow
open Nock.NockVMROM.Thm54.ForestExponentOrderClosure
open Nock.AxisBridge
open Nock.AxisBatching

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## §a. -/

/-- At `orderOf α = 0` the canonical
stamp leaves the *committed template's* memory forest — the `MemoryRowTemplate` rows that carry
`stamp.recordExponent` — literally unchanged, while "some committed exponent is at least
`orderOf α`" holds for every exponent. -/
theorem b134b_normData_published_forest_identity_of_orderOf_zero
    {E : BuildableNockExecution F K} (D : Data E) (z : K)
    (h0 : orderOf E.cfg.challenges.α = 0) :
    ((normData D).executionTemplate z).memoryForest =
      (D.executionTemplate z).memoryForest :=
  congrArg (fun l => l.map (mapNTree (renderMemoryTemplate z)))
    (Batch133.normData_is_identity_on_nodes_of_orderOf_zero D h0)

theorem b134b_normData_published_computeTree_identity
    {E : BuildableNockExecution F K} (D : Data E) (z : K) :
    ((normData D).executionTemplate z).computeTree =
      (D.executionTemplate z).computeTree := rfl

/-- Over a finite `K`,
`0 < orderOf α` is `α ≠ 0`. -/
theorem b134b_side_condition_is_alpha_ne_zero (α : K) :
    0 < orderOf α ↔ α ≠ 0 :=
  orderOf_pos_iff_ne_zero α

/-! ## §b. What the record-level pinning does and does not say -/

/-- `memoryRecordExp` is not "therefore unnormalised":
off the closed-form branch it is literally `0`, which is `< orderOf α` whenever `0 < orderOf α`.
Being `Classical.choose` of a `Prop` licenses only that the caller makes no choice — the pinning —
not any statement about the value's size -/
theorem b134b_memoryRecordExp_zero_of_not_closed {α ts : K}
    (h : ¬ MemoryTimestampClosedAt α ts) :
    memoryRecordExp α ts = 0 := by
  simp [memoryRecordExp, h]

/-- The record-level committed exponent
is a function of `E` alone. -/
theorem b134b_record_exponent_is_pinned_by_E (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows) :
    (memoryStampOf E i).recordExponent =
      memoryRecordExp E.cfg.challenges.α (E.exec.memoryRowAt i).2.2.mem.ts :=
  Batch133.honest_record_exponent_is_pinned_by_E E i

/-- …with no choice left to the premise bundle, which is what makes `normData D` fall outside the
record-level constructors' image in general -/
theorem b134b_record_nodes_are_determined (E : BuildableNockExecution F K)
    (M M' : MemoryRecordPremises E) :
    memoryNodesOf E M = memoryNodesOf E M' :=
  Batch133.honest_record_nodes_are_determined E M M'

/-! ## §c. Exactly what the window buys -/

/-- Under the window the licensed statement is the one the
production docstring now makes: every published **read and verify exponent** is returned unchanged.
This is a corollary of `alphaFreeRoot` equality per root index; committed-template equality is a
strictly larger claim and is **not** proved -/
theorem b134b_window_read_verify_exponents_unchanged {E : BuildableNockExecution F K} (D : Data E)
    (hw : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z) E.cfg.challenges.α)
    (i : Fin (configTemplateOf E E.cfg.challenges.z).kMem) :
    readExps (alphaFreeRoot ((normData D).executionTemplate E.cfg.challenges.z) i) =
        readExps (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) ∧
      verifyExps (alphaFreeRoot ((normData D).executionTemplate E.cfg.challenges.z) i) =
        verifyExps (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) :=
  ⟨congrArg readExps (Batch134.b134_normData_invisible_under_window D hw i),
    congrArg verifyExps (Batch134.b134_normData_invisible_under_window D hw i)⟩

theorem b134b_invisibility_is_alphaFreeRoot_equality {E : BuildableNockExecution F K} (D : Data E)
    (hw : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z) E.cfg.challenges.α)
    (i : Fin (configTemplateOf E E.cfg.challenges.z).kMem) :
    alphaFreeRoot ((normData D).executionTemplate E.cfg.challenges.z) i =
      alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i :=
  Batch134.b134_normData_invisible_under_window D hw i

/-! ## §d. -/

/-- The closure's honest shape is unchanged by anything in this module: still existential over
commitments of one execution, never universal in a supplied `D` -/
theorem b134b_closure_shape_unchanged {E : BuildableNockExecution F K}
    [Fintype F] [DecidableEq F] (D : Data E) (hgt : 11 < ringChar K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hα : E.cfg.challenges.α ≠ 0) :
    ∃ (D' : Data E) (hgenD' : GeneratedField.ClaimGenerated K D'.skeleton.publicClaim D'.Λ),
      D'.skeleton = D.skeleton ∧
        D'.memoryNodes.map (mapNTree MemoryNode.row) =
          D.memoryNodes.map (mapNTree MemoryNode.row) ∧
        (∀ a g : K, (packageOf D' hgt I hprl hmore hord hordM hrows hgenD' hF).strategy.Accepts (honestCoin E a g)
          E.cfg.challenges.lam) :=
  Batch134.b134_closure_is_existential_over_commitments D hgt I hprl hmore hord hordM hrows hgenF hF hα

end

#print axioms Nock.RedTeam.Batch134b.b134b_normData_published_forest_identity_of_orderOf_zero
#print axioms Nock.RedTeam.Batch134b.b134b_normData_published_computeTree_identity
#print axioms Nock.RedTeam.Batch134b.b134b_side_condition_is_alpha_ne_zero
#print axioms Nock.RedTeam.Batch134b.b134b_memoryRecordExp_zero_of_not_closed
#print axioms Nock.RedTeam.Batch134b.b134b_record_exponent_is_pinned_by_E
#print axioms Nock.RedTeam.Batch134b.b134b_record_nodes_are_determined
#print axioms Nock.RedTeam.Batch134b.b134b_window_read_verify_exponents_unchanged
#print axioms Nock.RedTeam.Batch134b.b134b_invisibility_is_alphaFreeRoot_equality
#print axioms Nock.RedTeam.Batch134b.b134b_closure_shape_unchanged

end Nock.RedTeam.Batch134b
