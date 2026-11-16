import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.RedTeam.Batch123Thm54GenericHonestPackage
import Nock.RedTeam.Batch45Thm54RecordCountBalance
import Nock.NockVMROM.Thm54.Walk37.PaperNames
import Nock.MemoryTable
import Nock.NockVM
import Nock.ComputeTable
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:
`Def:NMR` address the paper; timestamp space the paper; NMR CORE
the paper; lookup the paper; live `z^i` the paper;
`verify_child` removal the paper; count/`M+2L` the paper;
joint NockVMROM the paper.

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  `MemoryRecordPremises.timestampClosed` stays named.
`PairedRecordLayout` (`consumedRecordList.Perm addedRecordList`) would
identify each live `mem` with a `Service.record` and therefore inhabit the
extra; it does not sit on `E`.  `E` carries `RecordCountBalanced` (row
counts).  `verifyPartition` permutes wrapping MTree exponents, not records.
Wrapping `timestampExp` is not a witness.  Positive lemmas still take the
perm extra.  `ForestExponentOrder` stays named.  Accounting remains `11+1+2`.
Empty
`verify_child` service-record identification is not rounded into a paper
timestamp or capstone failure.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch124

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

/-! ## A. `axisNat` is address, not timestamp space -/

/-- Named extra: live `mem.ts` is some power of fibre `α`.
Independent unfold -/
theorem timestampClosed_is_existence (α ts : K) :
    MemoryTimestampClosedAt α ts = ∃ e : ℕ, ts = α ^ e :=
  rfl

/-- Live `mem.axis` is a Nat-cast.
Independent of `timestampClosed` -/
theorem axisNat_extra_is_nat_cast
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  M.axisNat

/-- The named extra quantifies the timestamp field, not the address field. -/
theorem timestampClosed_quantifies_ts
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ e : ℕ, (E.exec.memoryRowAt i).2.2.mem.ts = E.cfg.challenges.α ^ e :=
  fun i hact => (timestampClosed_is_existence _ _).mp (M.timestampClosed i hact)

/-- Address-column equality does not identify timestamps: two records may share
`axis` and differ in `ts`.  Not a live-row claim -/
theorem same_axis_can_differ_in_ts :
    ∃ r s : ComputeTable.MemRec K, r.axis = s.axis ∧ r.ts ≠ s.ts := by
  refine ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩, rfl, ?_⟩
  exact zero_ne_one

/-- Live kinds remain `read_root` and `verify_child` -/
theorem memoryMemRecKind_active_iff (s : MemoryTable.MState) :
    memoryMemRecKind s = .active ↔ s = .read_root ∨ s = .verify_child :=
  Batch123.memoryMemRecKind_active_iff s

/-- Named extra still applies to `verify_child` -/
theorem extra_applies_to_verify_child
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E)
    (i : Fin E.cfg.memRows)
    (h : (E.exec.memoryRowAt i).1 = .verify_child) :
    MemoryTimestampClosedAt E.cfg.challenges.α
      (E.exec.memoryRowAt i).2.2.mem.ts :=
  M.timestampClosed i (by simp [memoryMemRecKind, h])

/-- `vaxis` at a matching verify node is the committed address, not `mem.ts`.
Independent unfold -/
theorem vaxis_of_matching_verify (e : ℕ) (a : K) (c : MTree K) :
    vaxis e (.verify e a c) = a := by
  simp [vaxis]

/-- `Relaxis` at a verify node ignores the committed address and recurses.
Independent unfold -/
theorem relaxis_at_verify_ignores_committed_axis
    (e e' : ℕ) (a : K) (c : MTree K) :
    Relaxis e (.verify e' a c) = Relaxis e c := by
  simp [Relaxis]

/-- Production `axisNat` on `verify_child` is still the address column. -/
theorem axisNat_of_verify_child_is_address_column
    (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows)
    (h : (E.exec.memoryRowAt i).1 = .verify_child) :
    ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  GenericHonestData.axisNat_of_verify_child E i
    (by simpa [GenericHonestData.exec_memoryRowAt_encode] using h)

theorem inhabited_axisNat_from_E (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  GenericHonestData.axisNat_of_execution E hhon

/-- `VerifyRoute.here` binds the committed address to the record axis.
It does not mention `mem.ts` -/
theorem verifyRoute_here_binds_address
    {e : ℕ} {child : Noun} {recAxis a : K} {n : Noun} {c : MTree K}
    (hchild : n = child) (hcommitted : a = recAxis)
    (hr : readCount e c = 0) (hv : verifyCount e c = 0) :
    VerifyRoute e child recAxis [] n (.verify e a c) :=
  VerifyRoute.here hchild hcommitted hr hv

/-- `ServiceWalk.read` threads `s.record.axis` into the route, not `s.record.ts`. -/
theorem serviceWalk_read_binds_record_axis
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {services : List (Service cfg exec)} {n : Noun} {e : ℕ} {c : MTree K}
    (s : Service cfg exec) (hs : s ∈ services) (he : s.exponent = e)
    (hroot : s.root = n)
    (route : VerifyRoute e s.child s.record.axis (axisPath s.axis) n c)
    (below : ServiceWalk services n c) :
    ServiceWalk services n (.read e c) :=
  ServiceWalk.read s hs he hroot route below

/-! ## B. `timestampClosed` stays named; `PairedRecordLayout` is the extra hyp -/

/-- Two-field eta is unchanged.  `timestampClosed` is still a field. -/
theorem memoryRecordPremises_eta_still_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } :=
  Batch123.memoryRecordPremises_eta_still_two M

/-- Honest filler still takes live `ts = α^e` as a named input, not a perm. -/
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

/-- `PairedRecordLayout` is the consumed/added `MemRec` permutation.
Independent unfold -/
theorem paired_record_layout_is_consumed_added_perm
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    PairedRecordLayout exec =
      (consumedRecordList exec).Perm (addedRecordList exec) :=
  rfl

/-- `E` carries row-count balance.  There is no `PairedRecordLayout` field. -/
theorem execution_carries_recordCountBalance
    (E : BuildableNockExecution F K) :
    RecordCountBalanced E.exec :=
  E.recordCountBalance

/-- Exhaustive eta: `recordCountBalance` is present; `PairedRecordLayout` is
not a field -/
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

/-- `verify_child` still emits no external IO response -/
theorem verify_child_emits_no_response (pub : MemoryTable.Pub K)
    (h : pub.st = .verify_child) (hver : pub.ver = false) :
    MemoryTable.responseRecords pub = [] :=
  Batch122.verify_child_emits_no_response pub h hver

/-- A `read_root` row's `mem` is in `addedRecordList` -/
theorem read_root_mem_in_addedRecordList
    (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows)
    (h : (E.exec.memoryRowAt i).1 = .read_root) :
    (E.exec.memoryRowAt i).2.2.mem ∈ addedRecordList E.exec :=
  GenericHonestData.read_root_mem_in_addedRecordList E i h

/-- A `verify_child` row's `mem` is in `consumedRecordList` -/
theorem verify_child_mem_in_consumedRecordList
    (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows)
    (h : (E.exec.memoryRowAt i).1 = .verify_child) :
    (E.exec.memoryRowAt i).2.2.mem ∈ consumedRecordList E.exec :=
  GenericHonestData.verify_child_mem_in_consumedRecordList E i h

/-- Added `read_root` records are already service records -/
theorem service_record_of_added
    {E : BuildableNockExecution F K} {r : ComputeTable.MemRec K}
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hr : r ∈ addedRecordList E.execA) :
    ∃ s : Service E.cfg E.execA, r = s.record :=
  GenericHonestData.service_record_of_added hhon hr

/-- `read_root` identification does not need the perm -/
theorem read_root_identified_without_perm
    (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (i : Fin E.cfg.memRows)
    (h : (E.exec.memoryRowAt i).1 = .read_root) :
    ∃ s : Service E.cfg E.execA,
      (E.exec.memoryRowAt i).2.2.mem.ts = s.record.ts := by
  obtain ⟨rA, hrA, hts⟩ :=
    GenericHonestData.exec_added_ts_of_execA (read_root_mem_in_addedRecordList E i h)
  obtain ⟨s, hs⟩ := service_record_of_added hhon hrA
  exact ⟨s, by rw [hts, hs]⟩

/-- `verify_child` identification uses the consumed/added perm extra.
Independently reconstructed; does not derive the perm from `E`. -/
theorem verify_child_identified_from_paired_layout
    {E : BuildableNockExecution F K}
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hperm : PairedRecordLayout E.exec)
    (i : Fin E.cfg.memRows)
    (h : (E.exec.memoryRowAt i).1 = .verify_child) :
    ∃ s : Service E.cfg E.execA,
      (E.exec.memoryRowAt i).2.2.mem.ts = s.record.ts := by
  have hcons := verify_child_mem_in_consumedRecordList E i h
  have hadd :
      (E.exec.memoryRowAt i).2.2.mem ∈ addedRecordList E.exec :=
    (paired_record_layout_is_consumed_added_perm E.exec ▸ hperm).mem_iff.mp hcons
  obtain ⟨rA, hrA, hts⟩ := GenericHonestData.exec_added_ts_of_execA hadd
  obtain ⟨s, hs⟩ := service_record_of_added hhon hrA
  exact ⟨s, by rw [hts, hs]⟩

/-- Missing hypothesis after `axisNat`: the perm identifies every live `mem.ts`
with a `Service.record.ts`.  The perm is an extra binder -/
theorem identified_service_timestamps_of_paired_record_layout
    {E : BuildableNockExecution F K}
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (h : PairedRecordLayout E.exec) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ s : Service E.cfg E.execA,
          (E.exec.memoryRowAt i).2.2.mem.ts = s.record.ts := by
  intro i hact
  cases hst : (E.exec.memoryRowAt i).1 with
  | decompose => simp [memoryMemRecKind, hst] at hact
  | halt => simp [memoryMemRecKind, hst] at hact
  | read_root => exact read_root_identified_without_perm E hhon i hst
  | verify_child => exact verify_child_identified_from_paired_layout hhon h i hst

/-- The perm extra inhabits `timestampClosed` via already-held `Service.timestamp`.
It is not derived from `E` -/
theorem timestampClosed_of_paired_record_layout
    {E : BuildableNockExecution F K}
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (h : PairedRecordLayout E.exec) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt E.cfg.challenges.α
          (E.exec.memoryRowAt i).2.2.mem.ts := by
  intro i hact
  obtain ⟨s, hs⟩ := identified_service_timestamps_of_paired_record_layout hhon h i hact
  exact ⟨s.exponent, hs.trans s.timestamp⟩

/-- Production positive lemma agrees, and still takes the perm extra. -/
theorem production_timestampClosed_of_paired_record_layout
    {E : BuildableNockExecution F K}
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (h : PairedRecordLayout E.exec) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt E.cfg.challenges.α
          (E.exec.memoryRowAt i).2.2.mem.ts :=
  GenericHonestData.timestampClosed_of_paired_record_layout hhon h

/-! ## C. `RecordCountBalanced` is row counts, not the record perm -/

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

/-- Count balance and `M+2L` hold while the record perm fails.  Same-axis
records with distinct timestamps -/
theorem count_balance_does_not_imply_paired_layout :
    RecordCountBalanced Batch45.mismatchedExec ∧
      Batch45.mismatchedExec.memoryRows.length =
        memoryM Batch45.mismatchedExec + 2 * memoryL Batch45.mismatchedExec ∧
      ¬ PairedRecordLayout Batch45.mismatchedExec :=
  Batch45.count_balance_and_budget_do_not_imply_paired_layout

/-! ## D. `verifyPartition` permutes wrapping exponents, not records -/

/-- Per-root `verifyPartition` is a `List ℕ` permutation of wrapping MTree
exponents with service exponents -/
theorem verifyPartition_permutes_exponents
    (E : BuildableNockExecution F K) (i : Fin E.cfg.kMem) :
    (verifyExps (exactAxisTree E.cfg E.execA i)).Perm
      ((E.memoryTrace.roots i).services.map Service.exponent) :=
  (E.memoryTrace.roots i).verifyPartition

/-- `timestampExpAt` is wrapping `timestampExp` of that node's `mem.ts`.
Not a closed-form witness -/
theorem timestampExpAt_is_wrapping_timestampExp (α : K)
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K)) :
    timestampExpAt α t = timestampExp α (NTree.label t).2.2.mem.ts :=
  rfl

/-- Without an exponent witness, wrapping `timestampExp` is junk `0`. -/
theorem timestampExp_eq_zero_of_not_closed {α ts : K}
    (h : ¬ TimestampClosedAt α ts) :
    timestampExp α ts = 0 :=
  Batch122.timestampExp_eq_zero_of_not_closed h

/-- Reconstructed wrapping power of a non-closed timestamp is `1`, not `mem.ts`. -/
theorem reconstructed_power_of_not_closed {α ts : K}
    (h : ¬ TimestampClosedAt α ts) :
    α ^ timestampExp α ts = 1 :=
  Batch122.reconstructed_power_of_not_closed h

/-- `recordPartition` is `read_root` emissions, not `verify_child` records. -/
theorem recordPartition_is_read_root_emissions
    {E : BuildableNockExecution F K} (i : Fin E.cfg.kMem) :
    rootResponseRecords E.execA i =
      (E.memoryTrace.roots i).services.map Service.record :=
  (E.memoryTrace.roots i).recordPartition

/-! ## E. -/

/-- Uniqueness window is still `e < orderOf α` -/
theorem ForestExponentOrder_expands
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) :
    ForestExponentOrder E α =
      ((∀ i e, e ∈ readExps (alphaFreeRoot E i) → e < orderOf α) ∧
        (∀ i e, e ∈ verifyExps (alphaFreeRoot E i) → e < orderOf α)) :=
  Batch123.ForestExponentOrder_expands E α

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
    (_hhon : ∀ row ∈ E.exec.memoryRows,
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
    (_hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) (lmb : K) :
    ¬ ∀ ω : JointCoins K, (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts ω lmb :=
  GenericHonestPackage.packageOf_not_forall_omega D hgt I hprl hmore hord hordM hrows hgenF hF (lmb := lmb)

theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } :=
  Batch123.residualPremises_eta_still_four P

theorem censusRecordPremises_eta_still_five
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } :=
  Batch123.censusRecordPremises_eta_still_five C

/-- After filling `axisNat`, both NMR extras remain on the eta.
`timestampClosed` stays named -/
theorem memoryRecordPremises_still_two_after_timestamp_identification
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
      (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) :=
  ⟨inhabited_axisNat_from_E E M.honestVer, M.timestampClosed⟩

/-! ## F. -/

/-- NMR address space remains Nat-cast of `mem.axis`.  Timestamp space remains
the named extra. -/
theorem nmr_axis_is_address_not_timestamp_power
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
      (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) :=
  memoryRecordPremises_still_two_after_timestamp_identification M

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
  Batch123.released_builder_still_takes_hzero I hprl hmore hord hordM hrows hhon R hzero hgenF hF

inductive ReviewedField124
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

def substantiveFields124 : List ReviewedField124 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields124 : List ReviewedField124 := [.structural]

def residualFields124 : List ReviewedField124 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Keeping `timestampClosed` named is not a statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields124.length = 11 ∧
      typeSummaryFields124.length = 1 ∧
      residualFields124 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields124.length = 2 ∧
      (substantiveFields124 ++ typeSummaryFields124 ++ residualFields124).Nodup ∧
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

/-! ## G. F73: extra remains named; window remains named -/

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

/-- F73 assembled rows inhabit `axisNat` from `E`; that is address, not `ts`. -/
theorem f73_axisNat_of_execution :
    ∀ i : Fin concreteExecution.cfg.memRows,
      memoryMemRecKind (concreteExecution.exec.memoryRowAt i).1 = .active →
        ∃ n : ℕ, (concreteExecution.execA.memoryRowAt i).2.2.mem.axis =
          (n : K73cubic) :=
  inhabited_axisNat_from_E concreteExecution
    BuildableChips.Concrete.concrete_honest_ver

/-- F73 execution carries count balance, not a compiled record perm. -/
theorem f73_carries_recordCountBalance :
    RecordCountBalanced concreteExecution.exec :=
  concreteExecution.recordCountBalance

/-- Filler on F73 still requires named `timestampClosed` -/
theorem f73_filler_still_takes_timestampClosed
    (timestampClosed :
      ∀ i : Fin concreteExecution.cfg.memRows,
        memoryMemRecKind (concreteExecution.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt concreteExecution.cfg.challenges.α
            (concreteExecution.exec.memoryRowAt i).2.2.mem.ts) :
    MemoryRecordPremises concreteExecution :=
  GenericHonestData.memoryRecordPremises_of_timestampClosed
    concreteExecution timestampClosed BuildableChips.Concrete.concrete_honest_ver

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
    data73_generated OptimizedStrictFullPackage.Concrete.f73_primeField
   

/-- F73 wrapping `α = 4`, `ts = 0` is not closed.  Not a live-row claim. -/
theorem f73_zero_not_timestampClosed :
    ¬ MemoryTimestampClosedAt (4 : K73cubic) 0 := by
  have hα : (4 : K73cubic) ≠ 0 :=
    Nock.RedTeam.Batch122.Concrete.f73_alpha_ne_zero
  simpa using (Batch122.zero_not_closed_of_ne_zero hα)

end Concrete

#print axioms timestampClosed_is_existence
#print axioms axisNat_extra_is_nat_cast
#print axioms timestampClosed_quantifies_ts
#print axioms same_axis_can_differ_in_ts
#print axioms memoryMemRecKind_active_iff
#print axioms extra_applies_to_verify_child
#print axioms vaxis_of_matching_verify
#print axioms relaxis_at_verify_ignores_committed_axis
#print axioms axisNat_of_verify_child_is_address_column
#print axioms inhabited_axisNat_from_E
#print axioms verifyRoute_here_binds_address
#print axioms serviceWalk_read_binds_record_axis
#print axioms memoryRecordPremises_eta_still_two
#print axioms filler_still_takes_timestampClosed
#print axioms paired_record_layout_is_consumed_added_perm
#print axioms execution_carries_recordCountBalance
#print axioms execution_eta_has_count_balance_not_paired_layout
#print axioms verify_child_emits_no_response
#print axioms read_root_mem_in_addedRecordList
#print axioms verify_child_mem_in_consumedRecordList
#print axioms service_record_of_added
#print axioms read_root_identified_without_perm
#print axioms verify_child_identified_from_paired_layout
#print axioms identified_service_timestamps_of_paired_record_layout
#print axioms timestampClosed_of_paired_record_layout
#print axioms production_timestampClosed_of_paired_record_layout
#print axioms recordCountBalanced_is_count_equality
#print axioms recordCountBalanced_iff_consumed_added_length
#print axioms execution_recordCountBalance_is_count_equality
#print axioms paired_layout_implies_count_balance
#print axioms equal_length_not_perm_witness
#print axioms no_generic_length_converse
#print axioms count_balance_does_not_imply_paired_layout
#print axioms verifyPartition_permutes_exponents
#print axioms timestampExpAt_is_wrapping_timestampExp
#print axioms timestampExp_eq_zero_of_not_closed
#print axioms reconstructed_power_of_not_closed
#print axioms recordPartition_is_read_root_emissions
#print axioms ForestExponentOrder_expands
#print axioms packageOf_fibre_accepts_still_takes_window
#print axioms packageOf_not_forall_omega
#print axioms residualPremises_eta_still_four
#print axioms censusRecordPremises_eta_still_five
#print axioms memoryRecordPremises_still_two_after_timestamp_identification
#print axioms nmr_axis_is_address_not_timestamp_power
#print axioms released_builder_still_takes_hzero
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms Concrete.f73_axisNat_of_execution
#print axioms Concrete.f73_carries_recordCountBalance
#print axioms Concrete.f73_filler_still_takes_timestampClosed
#print axioms Concrete.f73_fibre_accepts_still_takes_window
#print axioms Concrete.f73_not_forall_omega
#print axioms Concrete.f73_zero_not_timestampClosed

end
end Nock.RedTeam.Batch124
