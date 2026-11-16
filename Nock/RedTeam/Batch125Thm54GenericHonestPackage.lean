import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.RedTeam.Batch124Thm54GenericHonestPackage
import Nock.RedTeam.Batch45Thm54RecordCountBalance
import Nock.NockVMROM.Thm54.Walk37.PaperNames
import Nock.MemoryTable
import Nock.NockVM
import Nock.ComputeTable
import Nock.IO
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:
`read_root` add the paper; `verify_child` remove the paper;
every timestamp added to `intermediate` and removed again the paper;
intermediate as `Thm:IO_result` on the two memory-table record columns
the paper; NMR CORE the paper; AIR matching the paper;
inverse-BFS forest the paper; joint NockVMROM

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  `PairedRecordLayout` stays named as
`consumedRecordList.Perm addedRecordList` of `MemRec`s, the intra-table
record-column matching the paper names as equivalent to
`Thm:IO_result` on the add/remove columns.  Honest `memoryForest`,
inverse-BFS `reconForest`, NMR noun/address carry, `recordPartition`,
wrapping `verifyPartition`, AIR `LmIO` of reconstructed timestamps,
`Vmem` `interV`, LogUp mass, and `RecordCountBalanced` are strictly
weaker objects.  Compiled `Thm:IO_result` (`io_result_LIO`) is
compute/memory RAP `L_IO`, not this intra-table perm.  AIR
`intermediate_matching` is `LmIO` of wrapping `α^e` lists (`List K`),
not `List (MemRec K)`.  `timestampClosed` and `ForestExponentOrder`
stay named.  `List.Perm` is not weakened to length.  Accounting remains
`11+1+2`.  Empty record perm on `E` is not rounded into a paper `IO_result` or
capstone failure.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch125

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.Framework
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.RowLayout

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## A. `PairedRecordLayout` is still named record `List.Perm` -/

/-- Independent unfold.  The extra is a permutation of `MemRec`s, not of
counts, exponents, timestamps, or LogUp mass -/
theorem paired_record_layout_is_consumed_added_perm
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    PairedRecordLayout exec =
      (consumedRecordList exec).Perm (addedRecordList exec) :=
  rfl

/-- Added records are `read_root` emissions of the BFS of `memoryForest`.
Independent unfold -/
theorem addedRecordList_from_memoryForest
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    addedRecordList exec =
      exec.memoryRows.flatMap
        (fun row =>
          match row.2.2.st with
          | .read_root => [row.2.2.mem]
          | .decompose | .halt | .verify_child => []) :=
  rfl

/-- Consumed records are `verify_child` removals of the **same** forest.
Independent unfold.  Same source does not equate the two projections. -/
theorem consumedRecordList_from_memoryForest
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    consumedRecordList exec =
      ((bfsForest exec.memoryForest).map NTree.label).flatMap
        (fun row => consumedRecords row.2.2) :=
  rfl

/-- Flat rows are a BFS projection, never a pairing of the two filters. -/
theorem memoryRows_are_bfs_of_memoryForest
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.memoryRows = (bfsForest exec.memoryForest).map NTree.label :=
  rfl

/-- `read_root` emits the row `mem` into the add list.  Independent unfold. -/
theorem responseRecords_of_read_root (pub : MemoryTable.Pub K)
    (h : pub.st = .read_root) (hver : pub.ver = true) :
    MemoryTable.responseRecords pub = [pub.mem] :=
  MemoryTable.responseRecords_eq_singleton_of_read_root pub h hver

/-- `verify_child` emits no add-list record under honest `ver = false` -/
theorem responseRecords_of_verify_child (pub : MemoryTable.Pub K)
    (h : pub.st = .verify_child) (hver : pub.ver = false) :
    MemoryTable.responseRecords pub = [] :=
  MemoryTable.responseRecords_eq_nil_of_verify_child pub h hver

/-- `verify_child` removes the row `mem` from `intermediate`.
Independent unfold -/
theorem consumedRecords_of_verify_child (pub : MemoryTable.Pub K)
    (h : pub.st = .verify_child) :
    consumedRecords pub = [pub.mem] := by
  simp [consumedRecords, h]

/-- `read_root` removes nothing from `intermediate` -/
theorem consumedRecords_of_read_root (pub : MemoryTable.Pub K)
    (h : pub.st = .read_root) :
    consumedRecords pub = [] := by
  simp [consumedRecords, h]

/-- The missing-hyp alias is definitionally the same extra.  Naming it
does not inhabit it -/
theorem intermediate_record_matching_aliases_paired_layout
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    IntermediateRecordMatching exec = PairedRecordLayout exec :=
  rfl

/-- Exhaustive eta: `E` carries count balance; there is no
`PairedRecordLayout` field -/
theorem execution_eta_has_count_balance_not_paired_layout
    (E : BuildableNockExecution F K) :
    E =
      { q := E.q
        q_gt_one := E.q_gt_one
        Λ := E.Λ
        cfg := E.cfg
        execA := E.execA
        exec := E.exec
        exec_encode := E.exec_encode
        semanticData := E.semanticData
        memoryTrace := E.memoryTrace
        requestNodup := E.requestNodup
        recordCountBalance := E.recordCountBalance
        q_le_ringChar := E.q_le_ringChar
        two_ne_zero := E.two_ne_zero
        Ksz_lt_ringChar := E.Ksz_lt_ringChar
        programIOCapacity := E.programIOCapacity
        memoryIOCapacity := E.memoryIOCapacity } :=
  BuildableNockExecution.eta_with_memoryTrace E

/-! ## B. Each listed candidate is honestly weaker -/

/-- Inverse-BFS reconstruction roundtrips the same forest labels, including
each node's `mem`.  It does not permute consumed against added. -/
theorem reconForest_roundtrip_is_label_equality
    (E : BuildableNockExecution F K) (M : MemoryRecordPremises E) :
    (memoryForestOf E M).map (mapNTree MemoryNode.row) = E.execA.memoryForest :=
  GenericHonestData.reconForest_roundtrip_is_label_equality E M

/-- `VerifyRoute.here` binds the walked noun to the service child and the
committed address to the service axis.  Independent cases.  It does not
bind `mem.ts` or the full `MemRec` -/
theorem verify_route_here_binds_child_and_address
    {e : ℕ} {child : Noun} {recAxis : K} {n : Noun} {a : K} {c : MTree K}
    (h : VerifyRoute e child recAxis [] n (.verify e a c)) :
    n = child ∧ a = recAxis := by
  cases h with
  | here hchild hcommitted => exact ⟨hchild, hcommitted⟩
  | verify_other hne => exact (hne rfl).elim

/-- `ServiceWalk.verify` recurses on the same noun.  Independent cases.
It does not bind a `MemRec` -/
theorem service_walk_verify_recurses_on_noun
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {services : List (Service cfg exec)} {n : Noun} {e : ℕ} {a : K}
    {c : MTree K} (h : ServiceWalk services n (.verify e a c)) :
    ServiceWalk services n c := by
  cases h with
  | verify below => exact below

/-- `recordPartition` identifies this root's `read_root` emissions with
service records.  There is no consumed-record field. -/
theorem record_partition_is_read_root_emissions
    (E : BuildableNockExecution F K) (i : Fin E.cfg.kMem) :
    rootResponseRecords E.execA i =
      (E.memoryTrace.roots i).services.map Service.record :=
  (E.memoryTrace.roots i).recordPartition

/-- Exhaustive `RootTrace` contents used here: read-record partition,
wrapping-exponent partitions, noun-indexed walk.  No consumed-`MemRec`
partition -/
theorem root_trace_has_read_records_and_exponent_partitions
    (E : BuildableNockExecution F K) (i : Fin E.cfg.kMem) :
    rootResponseRecords E.execA i =
        (E.memoryTrace.roots i).services.map Service.record ∧
      (readExps (exactAxisTree E.cfg E.execA i)).Perm
        ((E.memoryTrace.roots i).services.map Service.exponent) ∧
      (verifyExps (exactAxisTree E.cfg E.execA i)).Perm
        ((E.memoryTrace.roots i).services.map Service.exponent) ∧
      ServiceWalk (E.memoryTrace.roots i).services
        (E.memoryTrace.roots i).subject (exactAxisTree E.cfg E.execA i) :=
  ⟨(E.memoryTrace.roots i).recordPartition,
    (E.memoryTrace.roots i).readPartition,
    (E.memoryTrace.roots i).verifyPartition,
    (E.memoryTrace.roots i).traversal⟩

/-- Per-root `verifyPartition` is a `List ℕ` permutation of wrapping MTree
exponents with service exponents, not of `MemRec`s. -/
theorem verifyPartition_permutes_exponents
    (E : BuildableNockExecution F K) (i : Fin E.cfg.kMem) :
    (verifyExps (exactAxisTree E.cfg E.execA i)).Perm
      ((E.memoryTrace.roots i).services.map Service.exponent) :=
  (E.memoryTrace.roots i).verifyPartition

/-- Independent unfold of the wrapping reconstructed request list: field
powers of axis-tree exponents, not live `MemRec`s. -/
theorem forest_read_timestamps_are_wrapping_powers
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) :
    forestReadTimestamps cfg exec =
      (List.finRange cfg.kMem).flatMap fun i =>
        (readExps (exactAxisTree cfg exec i)).map
          (fun e => cfg.challenges.α ^ e) :=
  rfl

/-- Independent unfold of the wrapping reconstructed response list. -/
theorem forest_verify_timestamps_are_wrapping_powers
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) :
    forestVerifyTimestamps cfg exec =
      (List.finRange cfg.kMem).flatMap fun i =>
        (verifyExps (exactAxisTree cfg exec i)).map
          (fun e => cfg.challenges.α ^ e) :=
  rfl

/-- Structural `intermediate` matching on `E` is `LmIO` of those wrapping
`List K` powers, not of `List (MemRec K)`. -/
theorem execution_structural_intermediate_matching
    (E : BuildableNockExecution F K) :
    IO.LmIO E.cfg.Ksz (forestReadTimestamps E.cfg E.execA)
      (forestVerifyTimestamps E.cfg E.execA) :=
  E.memoryTrace.intermediateMatching

/-- `LmIO` is unique-request matching of two lists of the same type.  On
`E` those lists are wrapping timestamps -/
theorem lmio_is_finset_equality {R : Type} [DecidableEq R] (n : ℕ)
    (req resp : List R) :
    IO.LmIO n req resp ↔
      (IO.InRange n req.length ∧ resp.length ≤ req.length ∧ resp.Nodup
        ∧ req.toFinset = resp.toFinset) :=
  IO.LmIO_iff n req resp

/-- Compiled `Thm:IO_result` endpoint `L_IO` is `InRange ∧ Nodup ∧ Perm`
of two lists of the same type.  Independent unfold -/
theorem lio_endpoint_is_list_perm {R : Type} {n : ℕ} (req resp : List R) :
    IO.LIO n req resp =
      (IO.InRange n resp.length ∧ resp.Nodup ∧ req.Perm resp) :=
  rfl

/-- Citation of the compiled compute/memory RAP biconditional.  Its
record lists are `Fin M → 𝔽` RLC vectors of `IO_prog` / `IO_mem`, not
the intra-table add/remove `MemRec` columns -/
noncomputable def compiled_io_result_LIO := @Nock.IO.io_result_LIO

/-- `read_root` `interV` is the per-row add of `pole⁻¹`.  Independent unfold. -/
theorem interV_of_read_root (inp : MemoryTable.Inputs K) (p : MemoryTable.Pub K)
    (h : p.st = .read_root) :
    MemoryTable.interV inp p ↔
      p.icur - p.ipre = (MemoryTable.pole inp p.mem p.cprime)⁻¹ := by
  simp [MemoryTable.interV, h]

/-- `verify_child` `interV` is the per-row remove of `pole⁻¹`.  Independent unfold. -/
theorem interV_of_verify_child (inp : MemoryTable.Inputs K)
    (p : MemoryTable.Pub K) (h : p.st = .verify_child) :
    MemoryTable.interV inp p ↔
      p.ipre - p.icur = (MemoryTable.pole inp p.mem p.cprime)⁻¹ := by
  simp [MemoryTable.interV, h]

/-- Every accepted memory row satisfies `Vmem`.  That is the per-row
algorithmic verifier, not a record perm -/
theorem execution_vmem
    (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows) :
    MemoryTable.Vmem (E.exec.memoryRowAt i).2.1 (E.exec.memoryRowAt i).2.2 :=
  (memoryRowAccepted_of_execution E i).2.2.1

/-- Production `read_root` `interV` on `E` is that pole add. -/
theorem read_root_interV_is_pole_add
    (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows)
    (h : (E.exec.memoryRowAt i).1 = .read_root) :
    let p := (E.exec.memoryRowAt i).2.2
    p.icur - p.ipre =
      (MemoryTable.pole (E.exec.memoryRowAt i).2.1 p.mem p.cprime)⁻¹ :=
  GenericHonestData.read_root_interV_is_pole_add E i h

/-- Production `verify_child` `interV` on `E` is that pole remove. -/
theorem verify_child_interV_is_pole_remove
    (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows)
    (h : (E.exec.memoryRowAt i).1 = .verify_child) :
    let p := (E.exec.memoryRowAt i).2.2
    p.ipre - p.icur =
      (MemoryTable.pole (E.exec.memoryRowAt i).2.1 p.mem p.cprime)⁻¹ :=
  GenericHonestData.verify_child_interV_is_pole_remove E i h

/-- Chained LogUp with zero boundaries forces equal pole mass, not
`List.Perm` of `MemRec`s -/
theorem interChain_balance_is_logup_mass
    (inp : MemoryTable.Inputs K) (rows : List (MemoryTable.Pub K))
    (h : MemoryTable.InterChain inp 0 0 rows) :
    ((rows.filter (fun p => decide (p.st = MemoryTable.MState.read_root))).map
        (fun p => (MemoryTable.pole inp p.mem p.cprime)⁻¹)).sum
      = ((rows.filter
            (fun p => decide (p.st = MemoryTable.MState.verify_child))).map
          (fun p => (MemoryTable.pole inp p.mem p.cprime)⁻¹)).sum :=
  MemoryTable.interChain_balance inp rows h

/-- Independent unfold -/
theorem recordCountBalanced_is_count_equality
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    RecordCountBalanced exec =
      (memoryStateCount exec .verify_child =
        memoryStateCount exec .read_root) :=
  rfl

/-- Count balance is length equality of the two record lists.
Independent of `List.Perm` -/
theorem recordCountBalanced_iff_consumed_added_length
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    RecordCountBalanced exec ↔
      (consumedRecordList exec).length = (addedRecordList exec).length := by
  unfold RecordCountBalanced
  rw [verifyChildCount_eq_consumed_length, readRootCount_eq_added_length]

/-- `E.recordCountBalance` is that count equality -/
theorem execution_recordCountBalance_is_count_equality
    (E : BuildableNockExecution F K) :
    memoryStateCount E.exec .verify_child =
      memoryStateCount E.exec .read_root :=
  E.recordCountBalance

/-- Perm implies counts.  No converse is claimed here -/
theorem paired_layout_implies_count_balance
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : PairedRecordLayout exec) :
    RecordCountBalanced exec :=
  recordCountBalanced_of_pairedRecordLayout h

/-- Length equality is not permutation.  Independent List witness. -/
theorem equal_length_not_perm_witness :
    ∃ l1 l2 : List ℕ, l1.length = l2.length ∧ ¬ l1.Perm l2 := by
  refine ⟨[0], [1], rfl, ?_⟩
  intro h
  have : (0 : ℕ) ∈ ([1] : List ℕ) := h.mem_iff.mp (by simp)
  simp at this

/-- No universally quantified converse from equal lengths to `List.Perm`. -/
theorem no_generic_length_converse :
    ¬ ∀ xs ys : List ℕ, xs.length = ys.length → xs.Perm ys := by
  intro h
  obtain ⟨l1, l2, hlen, hnp⟩ := equal_length_not_perm_witness
  exact hnp (h l1 l2 hlen)

/-- Equal additive mass is not permutation.  Independent List witness
for the LogUp-mass shape -/
theorem equal_sum_not_perm_witness :
    ∃ l1 l2 : List ℕ, l1.sum = l2.sum ∧ ¬ l1.Perm l2 := by
  refine ⟨[0], [0, 0], rfl, ?_⟩
  intro h
  have := h.length_eq
  simp at this

/-- No universally quantified converse from equal sums to `List.Perm`. -/
theorem no_generic_sum_converse :
    ¬ ∀ xs ys : List ℕ, xs.sum = ys.sum → xs.Perm ys := by
  intro h
  obtain ⟨l1, l2, hsum, hnp⟩ := equal_sum_not_perm_witness
  exact hnp (h l1 l2 hsum)

/-- Timestamp equality does not identify `MemRec`s: two records may share
`ts` and differ in `axis`.  Not a live-row claim -/
theorem same_ts_can_differ_in_axis :
    ∃ r s : ComputeTable.MemRec K, r.ts = s.ts ∧ r.axis ≠ s.axis := by
  refine ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, rfl, ?_⟩
  exact zero_ne_one

/-- Count balance and `M+2L` hold while the record perm fails. -/
theorem count_balance_does_not_imply_paired_layout :
    RecordCountBalanced Batch45.mismatchedExec ∧
      Batch45.mismatchedExec.memoryRows.length =
        memoryM Batch45.mismatchedExec + 2 * memoryL Batch45.mismatchedExec ∧
      ¬ PairedRecordLayout Batch45.mismatchedExec :=
  Batch45.count_balance_and_budget_do_not_imply_paired_layout

/-! ## C. Missing hyp is record-column matching, not `True`; extras stay named -/

/-- The perm extra inhabits `timestampClosed` via already-held
`Service.timestamp`.  It is not derived from `E` -/
theorem timestampClosed_of_paired_record_layout
    {E : BuildableNockExecution F K}
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (h : PairedRecordLayout E.exec) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt E.cfg.challenges.α
          (E.exec.memoryRowAt i).2.2.mem.ts :=
  GenericHonestData.timestampClosed_of_paired_record_layout hhon h

/-- Production alias still takes the perm extra. -/
theorem timestampClosed_of_intermediate_record_matching
    {E : BuildableNockExecution F K}
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (h : IntermediateRecordMatching E.exec) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt E.cfg.challenges.α
          (E.exec.memoryRowAt i).2.2.mem.ts :=
  GenericHonestData.timestampClosed_of_intermediate_record_matching hhon h

/-- Honest filler still takes live `ts = α^e` as a named input. -/
theorem filler_still_takes_timestampClosed
    (E : BuildableNockExecution F K)
    (timestampClosed :
      ∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts)
    (honestVer :
      ∀ row ∈ E.exec.memoryRows,
        row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    (GenericHonestData.memoryRecordPremises_of_timestampClosed E
        timestampClosed honestVer).timestampClosed =
      timestampClosed :=
  rfl

/-- Two-field eta is unchanged.  `timestampClosed` is still a field. -/
theorem memoryRecordPremises_eta_still_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } :=
  Batch124.memoryRecordPremises_eta_still_two M

/-- After this inventory, both NMR extras remain on the eta.
`timestampClosed` stays named -/
theorem memoryRecordPremises_still_two_after_record_layout_inventory
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
      (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) :=
  ⟨GenericHonestData.axisNat_of_execution E M.honestVer, M.timestampClosed⟩

/-- Uniqueness window is still `e < orderOf α` -/
theorem ForestExponentOrder_expands
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) :
    ForestExponentOrder E α =
      ((∀ i e, e ∈ readExps (alphaFreeRoot E i) → e < orderOf α) ∧
        (∀ i e, e ∈ verifyExps (alphaFreeRoot E i) → e < orderOf α)) :=
  Batch124.ForestExponentOrder_expands E α

/-- Generic fibre `Accepts` still takes `ForestExponentOrder`.  Not `∀ ω`. -/
theorem packageOf_fibre_accepts_still_takes_window
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (horder : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α) :
    ∀ a g : K,
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts (honestCoin E a g) E.cfg.challenges.lam :=
  GenericHonestPackage.packageOf_fibre_accepts D hgt I hprl hmore hord hordM hrows hgenF hF horder

theorem packageOf_not_forall_omega
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) (lmb : K) :
    ¬ ∀ ω : JointCoins K, (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts ω lmb :=
  GenericHonestPackage.packageOf_not_forall_omega D hgt I hprl hmore hord hordM hrows hgenF hF (lmb := lmb)

theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } :=
  Batch124.residualPremises_eta_still_four P

theorem censusRecordPremises_eta_still_five
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } :=
  Batch124.censusRecordPremises_eta_still_five C

/-! ## D. -/

/-- NMR address space remains Nat-cast of `mem.axis`.  Timestamp space
remains the named extra.  Empty record perm on `E` is not a paper-`IO_result` or capstone failure. -/
theorem nmr_axis_is_address_not_record_perm
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
      (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) :=
  memoryRecordPremises_still_two_after_record_layout_inventory M

theorem released_builder_still_takes_hzero
    {E : BuildableNockExecution F K}
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = default)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    Nonempty (OptimizedFullStrictNockVMROMPackage F K I.hOrb) :=
  Batch124.released_builder_still_takes_hzero I hprl hmore hord hordM hrows hhon R hzero hgenF hF

inductive ReviewedField125
  | structural
  | optimized_chips
  | shared_io
  | perfect_completeness
  | containment
  | walk_bounds
  | p8_fixed_field_soundness
  | p8_fixed_field_bits
  | acceptance_to_target
  | complete_false_acceptance_bound
  | complete_false_acceptance_bits
  | exact_resources
  | row_budgets
  | shared_forest_axis
deriving DecidableEq

def substantiveFields125 : List ReviewedField125 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields125 : List ReviewedField125 := [.structural]

def residualFields125 : List ReviewedField125 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Keeping `PairedRecordLayout` named is not a statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields125.length = 11 ∧
      typeSummaryFields125.length = 1 ∧
      residualFields125 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields125.length = 2 ∧
      (substantiveFields125 ++ typeSummaryFields125 ++ residualFields125).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

variable [Fintype F] [DecidableEq F]

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  ⟨optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth, rfl⟩

/-! ## E. F73: extras remain named; window remains named -/

namespace Concrete

open ConcreteStrictPackage
open BuildableConcrete
open HonestCommitment.Concrete
open GenericHonestArrays.Concrete
open BuildableChips.Concrete
open GenericHonestPackage.Concrete

local instance : Fact (Nat.Prime 73) := concrete_prime73
noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- F73 execution carries count balance, not a compiled record perm. -/
theorem f73_carries_recordCountBalance :
    RecordCountBalanced concreteExecution.exec :=
  concreteExecution.recordCountBalance

/-- F73 structural matching is wrapping-timestamp `LmIO`, not `MemRec` perm. -/
theorem f73_structural_matching_is_timestamp_lmio :
    IO.LmIO concreteExecution.cfg.Ksz
      (forestReadTimestamps concreteExecution.cfg concreteExecution.execA)
      (forestVerifyTimestamps concreteExecution.cfg concreteExecution.execA) :=
  execution_structural_intermediate_matching concreteExecution

/-- Filler on F73 still requires named `timestampClosed` -/
theorem f73_filler_still_takes_timestampClosed
    (timestampClosed :
      ∀ i : Fin concreteExecution.cfg.memRows,
        memoryMemRecKind (concreteExecution.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt concreteExecution.cfg.challenges.α
            (concreteExecution.exec.memoryRowAt i).2.2.mem.ts) :
    MemoryRecordPremises concreteExecution :=
  GenericHonestData.memoryRecordPremises_of_timestampClosed
    concreteExecution timestampClosed concrete_honest_ver

-- Form R leftover LaterSeedZeros residual.
variable (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution)
include hmore73

/-- Generic fibre `Accepts` on the F73 package still takes
`ForestExponentOrder`. -/
theorem f73_fibre_accepts_still_takes_window
    (horder : ForestExponentOrder
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α) :
    ∀ a g : K73cubic,
      (package73Of hmore73).strategy.Accepts (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam :=
  GenericHonestPackage.Concrete.package73Of_fibre_accepts hmore73 horder

theorem f73_not_forall_omega (lmb : K73cubic) :
    ¬ ∀ ω : JointCoins K73cubic, (package73Of hmore73).strategy.Accepts ω lmb :=
  GenericHonestPackage.packageOf_not_forall_omega data73
    GenericHonestArrays.Concrete.f73_char_gt_eleven inputs73Fold2
    BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
    hmore73
    BuildablePackage.Concrete.concreteExecution_walk_order
    BuildablePackage.Concrete.concreteExecution_memory_walk_order
    BuildablePackage.Concrete.concreteExecution_rowsBound
    data73_generated OptimizedStrictFullPackage.Concrete.f73_primeField (lmb := lmb)

end Concrete

#print axioms paired_record_layout_is_consumed_added_perm
#print axioms addedRecordList_from_memoryForest
#print axioms consumedRecordList_from_memoryForest
#print axioms memoryRows_are_bfs_of_memoryForest
#print axioms responseRecords_of_read_root
#print axioms responseRecords_of_verify_child
#print axioms consumedRecords_of_verify_child
#print axioms consumedRecords_of_read_root
#print axioms intermediate_record_matching_aliases_paired_layout
#print axioms execution_eta_has_count_balance_not_paired_layout
#print axioms reconForest_roundtrip_is_label_equality
#print axioms verify_route_here_binds_child_and_address
#print axioms service_walk_verify_recurses_on_noun
#print axioms record_partition_is_read_root_emissions
#print axioms root_trace_has_read_records_and_exponent_partitions
#print axioms verifyPartition_permutes_exponents
#print axioms forest_read_timestamps_are_wrapping_powers
#print axioms forest_verify_timestamps_are_wrapping_powers
#print axioms execution_structural_intermediate_matching
#print axioms lmio_is_finset_equality
#print axioms lio_endpoint_is_list_perm
#print axioms interV_of_read_root
#print axioms interV_of_verify_child
#print axioms execution_vmem
#print axioms read_root_interV_is_pole_add
#print axioms verify_child_interV_is_pole_remove
#print axioms interChain_balance_is_logup_mass
#print axioms recordCountBalanced_is_count_equality
#print axioms recordCountBalanced_iff_consumed_added_length
#print axioms execution_recordCountBalance_is_count_equality
#print axioms paired_layout_implies_count_balance
#print axioms equal_length_not_perm_witness
#print axioms no_generic_length_converse
#print axioms equal_sum_not_perm_witness
#print axioms no_generic_sum_converse
#print axioms same_ts_can_differ_in_axis
#print axioms count_balance_does_not_imply_paired_layout
#print axioms timestampClosed_of_paired_record_layout
#print axioms timestampClosed_of_intermediate_record_matching
#print axioms filler_still_takes_timestampClosed
#print axioms memoryRecordPremises_eta_still_two
#print axioms memoryRecordPremises_still_two_after_record_layout_inventory
#print axioms ForestExponentOrder_expands
#print axioms packageOf_fibre_accepts_still_takes_window
#print axioms packageOf_not_forall_omega
#print axioms residualPremises_eta_still_four
#print axioms censusRecordPremises_eta_still_five
#print axioms nmr_axis_is_address_not_record_perm
#print axioms released_builder_still_takes_hzero
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms Concrete.f73_carries_recordCountBalance
#print axioms Concrete.f73_structural_matching_is_timestamp_lmio
#print axioms Concrete.f73_filler_still_takes_timestampClosed
#print axioms Concrete.f73_fibre_accepts_still_takes_window
#print axioms Concrete.f73_not_forall_omega

end
end Nock.RedTeam.Batch125
