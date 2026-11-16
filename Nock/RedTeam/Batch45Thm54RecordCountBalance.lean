import Nock.NockVMROM.Capstone
import Nock.NockVMROM.Thm54.StrictPackage
import Nock.RedTeam.Batch28Thm54RowLayoutStaging

/-!
The paper requires
global record accounting in the memory traversal and states the resulting
`M + 2L` row count.  A row-count budget can recover equality of the
`verify_child` and `read_root` counts, but cannot recover equality or permutation of their record
values.

The checks below compile:

* the exact definitional shape of `RecordCountBalanced` and both directions of the budget iff;
* a concrete balanced `ExactExecution` with `M = 3`, `L = 1`;
* a second concrete balanced execution whose added and consumed singleton records differ, proving
  that count balance and `M + 2L` do not imply `PairedRecordLayout`;
* a concrete unbalanced execution for which both count balance and `M + 2L` fail;
* the production `RAP_NockMemIO_rows`, strict-package `mem_rows`, `StrictCostRealization`, and
  `StrictThm54Statement` paths from count balance alone;
* rejection of an unbalanced premise at the production row theorem's type; and
* preservation of the existing paper alias.

No strict-package inhabitant and no full record-pairing theorem is claimed.
-/

namespace Nock.RedTeam.Batch45

open scoped Classical
open Nock Nock.Walk Nock.NockVM
open Module
open Nock.ComputeTable Nock.MemoryTable
open Nock.Framework Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.RowLayout
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictPackage
open Nock.NockVMROM.Thm54.StrictExtension

noncomputable section

/-! ## 1. Exact proposition and both directions of the budget iff -/

/-- `RecordCountBalanced` is definitionally exactly equality of the two wrapper-state counts. -/
theorem recordCountBalanced_exact_shape
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    RecordCountBalanced exec ↔
      memoryStateCount exec .verify_child = memoryStateCount exec .read_root :=
  Iff.rfl

/-- The `M + 2L` budget forces exact count balance. -/
theorem budget_implies_recordCountBalanced
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (h : exec.memoryRows.length = memoryM exec + 2 * memoryL exec) :
    RecordCountBalanced exec :=
  (memory_rows_eq_M_add_two_mul_L_iff exec).mp h

/-- Exact count balance is sufficient for the `M + 2L` budget. -/
theorem recordCountBalanced_implies_budget
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (h : RecordCountBalanced exec) :
    exec.memoryRows.length = memoryM exec + 2 * memoryL exec :=
  (memory_rows_eq_M_add_two_mul_L_iff exec).mpr h

/-- The direct configured-row theorem consumes the same exact count proposition. -/
theorem recordCountBalanced_implies_configured_budget
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (h : RecordCountBalanced exec) :
    cfg.memRows = memoryM exec + 2 * memoryL exec :=
  memRows_eq_M_add_two_mul_L_of_count_balance h

/-! ## 2. Concrete positive non-vacuity -/

abbrev K17 := Nock.RedTeam.Batch28.K17

theorem concrete_balanced_execution_nonvacuous :
    RecordCountBalanced Nock.RedTeam.Batch28.b28Exec ∧
      memoryM Nock.RedTeam.Batch28.b28Exec = 3 ∧
      memoryL Nock.RedTeam.Batch28.b28Exec = 1 ∧
      Nock.RedTeam.Batch28.b28Exec.memoryRows.length =
        memoryM Nock.RedTeam.Batch28.b28Exec +
          2 * memoryL Nock.RedTeam.Batch28.b28Exec ∧
      Nock.RedTeam.Batch28.b28Cfg.memRows =
        memoryM Nock.RedTeam.Batch28.b28Exec +
          2 * memoryL Nock.RedTeam.Batch28.b28Exec := by
  exact ⟨Nock.RedTeam.Batch28.b28_recordCountBalanced,
    Nock.RedTeam.Batch28.b28_M, Nock.RedTeam.Batch28.b28_L,
    memory_rows_eq_M_add_two_mul_L_of_count_balance
      Nock.RedTeam.Batch28.b28_recordCountBalanced,
    memRows_eq_M_add_two_mul_L_of_count_balance
      Nock.RedTeam.Batch28.b28_recordCountBalanced⟩

/-! ## 3. Equal counts do not imply record permutation -/

/-- A second record differing only in timestamp. -/
def recB : MemRec K17 :=
  { Nock.RedTeam.Batch28.recA with ts := 5 }

theorem recB_ne_recA : recB ≠ Nock.RedTeam.Batch28.recA := by
  intro h
  have hts := congrArg (fun r : MemRec K17 => r.ts) h
  exact (by decide : (5 : K17) ≠ 4)
    (by simpa [recB, Nock.RedTeam.Batch28.recA] using hts)

def verifyLabelB : MState × MemoryTable.DTmem K17 :=
  (.verify_child,
    (Nock.RedTeam.Batch28.mInp, Nock.RedTeam.Batch28.memPub .verify_child recB))

def verifyTreeB : NTree (MState × MemoryTable.DTmem K17) :=
  .node verifyLabelB [Nock.RedTeam.Batch28.haltTree]

def mismatchedDecompTree : NTree (MState × MemoryTable.DTmem K17) :=
  .node Nock.RedTeam.Batch28.decompLabel [Nock.RedTeam.Batch28.haltTree, verifyTreeB]

def mismatchedMemoryTree : NTree (MState × MemoryTable.DTmem K17) :=
  .node Nock.RedTeam.Batch28.readLabel [mismatchedDecompTree]

def mismatchedExec : ExactExecution Nock.RedTeam.Batch28.b28Cfg where
  computeTree := Nock.RedTeam.Batch28.computeTree
  memoryForest := [mismatchedMemoryTree]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [Nock.RedTeam.Batch28.computeTree, bfsForest, NTree.size, totalSize,
      Nock.RedTeam.Batch28.b28Cfg]
  memory_bfs_length := by
    norm_num [mismatchedMemoryTree, mismatchedDecompTree, verifyTreeB,
      Nock.RedTeam.Batch28.haltTree, bfsForest, NTree.size, totalSize,
      Nock.RedTeam.Batch28.b28Cfg]

theorem mismatched_rows :
    mismatchedExec.memoryRows =
      [Nock.RedTeam.Batch28.readLabel, Nock.RedTeam.Batch28.decompLabel,
        Nock.RedTeam.Batch28.haltLabel, verifyLabelB, Nock.RedTeam.Batch28.haltLabel] := by
  norm_num [ExactExecution.memoryRows, mismatchedExec, mismatchedMemoryTree,
    mismatchedDecompTree, verifyTreeB, Nock.RedTeam.Batch28.haltTree, bfsForest,
    NTree.size, totalSize]

theorem mismatched_state_counts :
    memoryStateCount mismatchedExec .decompose = 1 ∧
      memoryStateCount mismatchedExec .halt = 2 ∧
      memoryStateCount mismatchedExec .read_root = 1 ∧
      memoryStateCount mismatchedExec .verify_child = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [memoryStateCount, fibreCount, mismatched_rows, Nock.RedTeam.Batch28.readLabel,
      Nock.RedTeam.Batch28.decompLabel, Nock.RedTeam.Batch28.haltLabel, verifyLabelB,
      Nock.RedTeam.Batch28.memPub]

theorem mismatched_recordCountBalanced : RecordCountBalanced mismatchedExec := by
  exact mismatched_state_counts.2.2.2.trans mismatched_state_counts.2.2.1.symm

theorem mismatched_M : memoryM mismatchedExec = 3 := by
  simp [memoryM, mismatched_state_counts.1, mismatched_state_counts.2.1]

theorem mismatched_L : memoryL mismatchedExec = 1 :=
  mismatched_state_counts.2.2.1

theorem mismatched_budget :
    mismatchedExec.memoryRows.length =
      memoryM mismatchedExec + 2 * memoryL mismatchedExec :=
  memory_rows_eq_M_add_two_mul_L_of_count_balance mismatched_recordCountBalanced

theorem mismatched_added_records :
    addedRecordList mismatchedExec = [Nock.RedTeam.Batch28.recA] := by
  simp [addedRecordList, MemoryTable.responseRecords, mismatched_rows,
    Nock.RedTeam.Batch28.readLabel, Nock.RedTeam.Batch28.decompLabel,
    Nock.RedTeam.Batch28.haltLabel, verifyLabelB, Nock.RedTeam.Batch28.memPub]

theorem mismatched_consumed_records :
    consumedRecordList mismatchedExec = [recB] := by
  simp [consumedRecordList, consumedRecords, mismatched_rows,
    Nock.RedTeam.Batch28.readLabel, Nock.RedTeam.Batch28.decompLabel,
    Nock.RedTeam.Batch28.haltLabel, verifyLabelB, Nock.RedTeam.Batch28.memPub]

theorem count_balance_and_budget_do_not_imply_paired_layout :
    RecordCountBalanced mismatchedExec ∧
      mismatchedExec.memoryRows.length =
        memoryM mismatchedExec + 2 * memoryL mismatchedExec ∧
      ¬ PairedRecordLayout mismatchedExec := by
  refine ⟨mismatched_recordCountBalanced, mismatched_budget, ?_⟩
  intro h
  change (consumedRecordList mismatchedExec).Perm (addedRecordList mismatchedExec) at h
  rw [mismatched_consumed_records, mismatched_added_records] at h
  exact recB_ne_recA (by simpa using h)

/-- Generic control: length equality alone cannot imply permutation. -/
theorem equal_lengths_not_perm :
    ([0] : List Nat).length = ([1] : List Nat).length ∧
      ¬ ([0] : List Nat).Perm [1] := by
  decide

/-- Therefore no universally quantified converse from equal lengths to `List.Perm` can be claimed. -/
theorem no_generic_length_converse :
    ¬ ∀ xs ys : List Nat, xs.length = ys.length → xs.Perm ys := by
  intro h
  exact equal_lengths_not_perm.2 (h [0] [1] rfl)

theorem paired_layout_implies_count_balance
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : PairedRecordLayout exec) :
    RecordCountBalanced exec :=
  recordCountBalanced_of_pairedRecordLayout h

/-! ## 4. A concrete load-bearing unbalanced execution -/

def haltChain : NTree (MState × MemoryTable.DTmem K17) :=
  .node Nock.RedTeam.Batch28.haltLabel [Nock.RedTeam.Batch28.haltTree]

def unbalancedDecompTree : NTree (MState × MemoryTable.DTmem K17) :=
  .node Nock.RedTeam.Batch28.decompLabel [haltChain, Nock.RedTeam.Batch28.haltTree]

def unbalancedMemoryTree : NTree (MState × MemoryTable.DTmem K17) :=
  .node Nock.RedTeam.Batch28.readLabel [unbalancedDecompTree]

/-- Five rows remain, but there is one `read_root` and no `verify_child`. -/
def unbalancedExec : ExactExecution Nock.RedTeam.Batch28.b28Cfg where
  computeTree := Nock.RedTeam.Batch28.computeTree
  memoryForest := [unbalancedMemoryTree]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [Nock.RedTeam.Batch28.computeTree, bfsForest, NTree.size, totalSize,
      Nock.RedTeam.Batch28.b28Cfg]
  memory_bfs_length := by
    norm_num [unbalancedMemoryTree, unbalancedDecompTree, haltChain,
      Nock.RedTeam.Batch28.haltTree, bfsForest, NTree.size, totalSize,
      Nock.RedTeam.Batch28.b28Cfg]

theorem unbalanced_rows :
    unbalancedExec.memoryRows =
      [Nock.RedTeam.Batch28.readLabel, Nock.RedTeam.Batch28.decompLabel,
        Nock.RedTeam.Batch28.haltLabel, Nock.RedTeam.Batch28.haltLabel,
        Nock.RedTeam.Batch28.haltLabel] := by
  norm_num [ExactExecution.memoryRows, unbalancedExec, unbalancedMemoryTree,
    unbalancedDecompTree, haltChain, Nock.RedTeam.Batch28.haltTree, bfsForest,
    NTree.size, totalSize]

theorem unbalanced_state_counts :
    memoryStateCount unbalancedExec .decompose = 1 ∧
      memoryStateCount unbalancedExec .halt = 3 ∧
      memoryStateCount unbalancedExec .read_root = 1 ∧
      memoryStateCount unbalancedExec .verify_child = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [memoryStateCount, fibreCount, unbalanced_rows, Nock.RedTeam.Batch28.readLabel,
      Nock.RedTeam.Batch28.decompLabel, Nock.RedTeam.Batch28.haltLabel,
      Nock.RedTeam.Batch28.memPub]

theorem unbalanced_not_countBalanced : ¬ RecordCountBalanced unbalancedExec := by
  intro h
  have h' :
      memoryStateCount unbalancedExec .verify_child =
        memoryStateCount unbalancedExec .read_root :=
    h
  rw [unbalanced_state_counts.2.2.2, unbalanced_state_counts.2.2.1] at h'
  omega

theorem unbalanced_budget_fails :
    unbalancedExec.memoryRows.length ≠
      memoryM unbalancedExec + 2 * memoryL unbalancedExec := by
  intro h
  exact unbalanced_not_countBalanced
    ((memory_rows_eq_M_add_two_mul_L_iff unbalancedExec).mp h)

/-- The condition is load-bearing on the real carrier: removing the matching wrapper breaks exactly
the count premise and exactly the row budget. -/
theorem count_condition_is_load_bearing :
    ¬ RecordCountBalanced unbalancedExec ∧
      unbalancedExec.memoryRows.length ≠
        memoryM unbalancedExec + 2 * memoryL unbalancedExec :=
  ⟨unbalanced_not_countBalanced, unbalanced_budget_fails⟩

/-! ## 5. Production and strict-consumer guards -/

/-- The production memory-RAP row theorem consumes count balance directly; no permutation premise
appears in this receipt. -/
theorem rap_memory_rows_from_count_balance
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {F₀ K₀ : Type} [Field F₀] [Field K₀] [Algebra F₀ K₀]
    {e h : ℕ} (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F e h) (H : Finset F)
    {cfg : ExactConfig F₀ K₀} {exec : ExactExecution cfg}
    (hbalance : RecordCountBalanced exec)
    (hH : H.card = exec.memoryRows.length) :
    (RAP_NockMemIO b chalVal pubVal orbit H).H.card =
      memoryM exec + 2 * memoryL exec :=
  RAP_NockMemIO_rows b chalVal pubVal orbit H hbalance hH

/-- An unbalanced negated premise is rejected at the production theorem's count-balance slot. -/
theorem rap_memory_rows_rejects_unbalanced_premise
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {e h : ℕ} (_b : Basis (Fin e) F K) (_chalVal _pubVal : ℕ → F)
    (_orbit : StrictOrbitDomain F e h) (H : Finset F)
    (_hH : H.card = unbalancedExec.memoryRows.length) : True := by
  fail_if_success
    exact RAP_NockMemIO_rows _b _chalVal _pubVal _orbit H
      unbalanced_not_countBalanced _hH
  trivial

/-- All production strict consumers project the same package count premise and resulting row
budget.  None asks for `PairedRecordLayout`. -/
theorem strict_consumers_use_record_count_balance
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
    RecordCountBalanced P.objects.exec ∧
      P.memRAP.H.card =
        memoryM P.objects.exec + 2 * memoryL P.objects.exec ∧
      StrictCostRealization P ∧
      (strictNockVMROM_of_package P).row_budgets.2 =
        P.mem_rows := by
  exact ⟨P.recordCountBalance, P.mem_rows, P.strictCostRealization, rfl⟩

/-- Count balance does not typecheck as the stronger permutation proposition in the strict package. -/
theorem strict_package_does_not_project_permutation
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (_P : StrictNockVMROMPackage F K hOrb q Λ) : True := by
  fail_if_success
    exact (_P.recordCountBalance : PairedRecordLayout _P.objects.exec)
  trivial

/-- R2a does not repoint the paper theorem alias or claim overall closure. -/
theorem paper_alias_unchanged :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  rfl

end
end Nock.RedTeam.Batch45

-- Production declarations.
#print axioms Nock.NockVMROM.Thm54.RowLayout.memory_rows_eq_M_add_two_mul_L_iff
#print axioms Nock.NockVMROM.Thm54.RowLayout.memRows_eq_M_add_two_mul_L_of_count_balance
#print axioms Nock.NockVMROM.Thm54.RowLayout.recordCountBalanced_of_pairedRecordLayout
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockMemIO_rows
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.mem_rows
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.strictCostRealization
#print axioms Nock.NockVMROM.Thm54.StrictPackage.strictNockVMROM_of_package

#print axioms Nock.RedTeam.Batch45.recordCountBalanced_exact_shape
#print axioms Nock.RedTeam.Batch45.budget_implies_recordCountBalanced
#print axioms Nock.RedTeam.Batch45.recordCountBalanced_implies_budget
#print axioms Nock.RedTeam.Batch45.recordCountBalanced_implies_configured_budget
#print axioms Nock.RedTeam.Batch45.concrete_balanced_execution_nonvacuous
#print axioms Nock.RedTeam.Batch45.count_balance_and_budget_do_not_imply_paired_layout
#print axioms Nock.RedTeam.Batch45.no_generic_length_converse
#print axioms Nock.RedTeam.Batch45.paired_layout_implies_count_balance
#print axioms Nock.RedTeam.Batch45.count_condition_is_load_bearing
#print axioms Nock.RedTeam.Batch45.rap_memory_rows_from_count_balance
#print axioms Nock.RedTeam.Batch45.rap_memory_rows_rejects_unbalanced_premise
#print axioms Nock.RedTeam.Batch45.strict_consumers_use_record_count_balance
#print axioms Nock.RedTeam.Batch45.strict_package_does_not_project_permutation
#print axioms Nock.RedTeam.Batch45.paper_alias_unchanged
