/-
  Nock/NockVMROM/Thm54/MemoryHaltRowsBase.lean

  `HaltRowsBase`: every `halt` row of an execution carries a
  leaf in the image of `𝔽`.  It follows from the skeleton binding of the memory rows, hence from the package's
  scan / frame / shape checks, and it is the `HaltLeavesBase` side condition of canonical memory
  completeness (`haltLeavesBase_of_rows`).  The package instance is
  `MemoryHaltLeavesHonest.package_haltLeavesBase`.
-/
import Nock.NockVMROM.Thm54.RawSemanticAssembly
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.MemoryHaltLeavesHonest

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.RawSemanticAssembly
open Nock.NockVMROM.Thm54.StrictCommitment
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Every `halt` row of an execution carries a base-field leaf. -/
def HaltRowsBase {cfg : ExactConfig F K} (exec : ExactExecution cfg) : Prop :=
  ∀ row ∈ exec.memoryRows, row.2.2.st = .halt →
    ∃ a : F, algebraMap F K a = row.2.2.pt.noun.leaf

/-- A bound memory row whose skeleton state is `halt` has the lifted atom as its leaf. -/
theorem bindMemoryRow_halt_leaf {z : K} {s : MemoryRowSkeleton}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (h : BindMemoryRow z s row) (hst : row.2.2.st = .halt) :
    ∃ a : F, algebraMap F K a = row.2.2.pt.noun.leaf := by
  obtain ⟨-, -, hst', hfp, -⟩ := h
  have hs : s.state = .halt := hst' ▸ hst
  refine ⟨(s.haltAtom hs : F), ?_⟩
  rw [hfp, s.haltParent hs, GlobalCarryRecognizer.enc_atom]
  simp [ComputeTable.FP.atomFP]

/-- Skeleton binding of every memory row gives `HaltRowsBase`. -/
theorem haltRowsBase_of_bind {z : K} {S : SemanticSkeleton}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : List.Forall₂ (BindMemoryRow z) (memorySkeletonRows S) exec.memoryRows) :
    HaltRowsBase (F := F) exec := by
  have key : ∀ {l₁ : List MemoryRowSkeleton} {l₂ : List (MemoryTable.MState × MemoryTable.DTmem K)},
      List.Forall₂ (BindMemoryRow z) l₁ l₂ → ∀ row ∈ l₂, ∃ s, BindMemoryRow z s row := by
    intro l₁ l₂ hf
    induction hf with
    | nil => intro row hrow; simp at hrow
    | cons hab _ ih =>
        intro row hrow
        rcases List.mem_cons.mp hrow with rfl | hrow
        · exact ⟨_, hab⟩
        · exact ih row hrow
  intro row hrow hst
  obtain ⟨s, hb⟩ := key h row hrow
  exact bindMemoryRow_halt_leaf hb hst

/-- Scan, frame and shape checks give `HaltRowsBase`. -/
theorem haltRowsBase_of_checks {z : K} {C : SkeletonCommitment}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hshape : ExecTreeShapeMatchesAt C exec)
    (hframe : RowFrameChecksAt z C exec)
    (hscan : ActiveFingerprintChecksAt z C exec) :
    HaltRowsBase (F := F) exec := by
  have hlenM : (memorySkeletonRows C.skeleton).length = exec.memoryRows.length := by
    simpa [memorySkeletonRows, ExactExecution.memoryRows] using
      memoryRows_length_eq_of_shapeMatch hshape.memory
  exact haltRowsBase_of_bind (forall₂_bindMemoryRow_of_scan hlenM hframe.memory hscan.2)

/-- `HaltRowsBase` of a family's execution is `HaltLeavesBase` of any sampled assignment on it. -/
theorem haltLeavesBase_of_rows [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K} (A : SampledIOSameExecutionAssignment R p)
    (h : HaltRowsBase (F := F) R.problem.exec) : HaltLeavesBase A := by
  intro i hst
  exact h _ (ExactExecution.memoryRowAt_mem _ i) hst

/-- Transport along the package's `family_cfg` / `family_exec` (`HEq`). -/
theorem haltRowsBase_heq {c₁ c₂ : ExactConfig F K}
    {e₁ : ExactExecution c₁} {e₂ : ExactExecution c₂} (hc : c₁ = c₂) (he : HEq e₁ e₂) :
    HaltRowsBase (F := F) e₂ → HaltRowsBase (F := F) e₁ := by
  subst hc; subst he; exact id

end

end Nock.NockVMROM.Thm54.MemoryHaltLeavesHonest

#print axioms Nock.NockVMROM.Thm54.MemoryHaltLeavesHonest.haltRowsBase_of_checks
#print axioms Nock.NockVMROM.Thm54.MemoryHaltLeavesHonest.haltLeavesBase_of_rows
