import Nock.NockVMROM.Thm54
import Nock.NockVMROM.Thm54.Walk37.PaperNames
import Nock.RedTeam.Batch91Thm54CompleteFalseAcceptance
import Nock.RedTeam.Batch153Thm54C1PairedRecordGate
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
CL/CM are claims under attack, not evidence.

Paper frame:
* Add to `intermediate` at `read_root`; unique timestamp
  `z^i`.
* Remove at `verify_child` (`1415`).
* Every timestamp added then removed again (`1427`).
* `intermediate` constraints as `RAP_mem-IO` / `RAP_comp-IO`; argument
  equivalent to `Thm:IO_result`; IO and `intermediate` are the two memory
  record columns matched within the same table (`1431`).
* Algorithm Memspec add (`2072`) / remove (`2080`).

Consumed capstone:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`
(`«Thm:NockVMROM»`). Untouched.

Claims under attack:
* **CL:** `DistinctCensusC1.pairedRecordLayout_distinctCensus` is a direct
  `Perm` (swap last two of four) at `distinctCensusExecution hfirstD` F97. Designed
  C1 inhabited (`intermediatePreimageD`); fifteenth field not added. J.00
  tick at F97. Same written-scope rule as `skeletonBounded`. Not claimed:
  `∀ E` PRL from `E` alone; C1 as a field.
* **CM:** `timestampClosed` at F97 via
  `timestampClosed_of_paired_record_layout pairedRecordLayout_distinctCensus`.
  Contingent row. Also inhabited at Op6/Op9 as finite column reads.

Five axes:

**S0** (vacuity): CLEAR — F97 Perm is a last-two swap of real NMR records
(`recR ≠ recL` from `α^4`/`α^3` in `Iio (orderOf α)`); lists not identical;
C1 inhabited and columns not identical.

**S1** (weakening): CLEAR on the written-scope claim. Generic constructor
still takes named `timestampClosed`; the PRL bridge still takes PRL. C1 is
not a field. CL already disclaims `∀ E`.

**S2** (drift): CLEAR — C1 is an NMR-record preimage; PRL is `MemRec` Perm;
`timestampClosed` is `∃ e, ts = α^e`. Counted-event route still takes event
exclusions. `RecordCountBalanced` is strictly weaker. `c1_iff` reverse
ignores PRL (fixture coincidence; not claimed).

**S3** (axioms): ⊆ `{propext, Classical.choice, Quot.sound}`. The `11+1+2`
pin is axiom-free.

**S4** (layer): CLEAR — fourteen fields; residual premises three;
`MemoryRecordPremises` still two; capstone untouched; CM contingent on PRL
at F97; Op6/Op9 finite reads are additional inhabitants, not a widening.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch159

open scoped Classical
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusC1
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.DistinctCensusFold2
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.PairedRecordCountedEvent
open Nock.NockVMROM.Thm54.RowLayout
open Nock.RedTeam.Batch91

local instance prime97d : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97d : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## Axis 1. Vacuity: F97 Perm is a last-two swap of real NMR records -/

abbrev fr (r : ComputeTable.MemRec K97cubic) : ComputeTable.MemRec K97cubic :=
  NockVM.formRRow r MemoryTable.formRDefault

theorem f97_added_is_FTLR :
    addedRecordList execD = [fr recF, fr recT, fr recL, fr recR] :=
  addedRecordList_distinctCensus

theorem f97_consumed_is_FTRL :
    consumedRecordList execD = [fr recF, fr recT, fr recR, fr recL] :=
  consumedRecordList_distinctCensus

/-- Distinct timestamps `z^i`: exponents 4 and 3 lie in `Iio (orderOf α)`. -/
theorem recR_ne_recL : fr recR ≠ fr recL := by
  intro h
  have hts := congrArg (fun r : ComputeTable.MemRec K97cubic => r.ts) h
  simp [fr, NockVM.formRRow, recR, recL] at hts
  have h4 : 4 ∈ Set.Iio (orderOf alphaD) := by
    rw [Set.mem_Iio, alphaD_order]; norm_num
  have h3 : 3 ∈ Set.Iio (orderOf alphaD) := by
    rw [Set.mem_Iio, alphaD_order]; norm_num
  have : 4 = 3 := pow_injOn_Iio_orderOf h4 h3 hts
  nomatch this

theorem f97_lists_not_identical :
    consumedRecordList execD ≠ addedRecordList execD := by
  rw [f97_consumed_is_FTRL, f97_added_is_FTLR]
  intro h
  have h2 := congrArg (fun l : List (ComputeTable.MemRec K97cubic) => l[2]?) h
  simp at h2
  exact recR_ne_recL h2

theorem f97_perm_is_last_two_swap :
    [fr recF, fr recT, fr recR, fr recL].Perm [fr recF, fr recT, fr recL, fr recR] :=
  (((List.Perm.swap (fr recR) (fr recL) []).cons (fr recT)).cons (fr recF)).symm

/-- Independent reconstruction of the named extra at F97: last-two swap,
    not `List.Perm.refl`. -/
theorem f97_paired_from_lists :
    PairedRecordLayout execD := by
  rw [PairedRecordLayout, f97_added_is_FTLR, f97_consumed_is_FTRL]
  exact f97_perm_is_last_two_swap

theorem f97_perm_is_not_identity :
    ¬ ([fr recF, fr recT, fr recR, fr recL] = [fr recF, fr recT, fr recL, fr recR]) := by
  intro h
  have h2 := congrArg (fun l : List (ComputeTable.MemRec K97cubic) => l[2]?) h
  simp at h2
  exact recR_ne_recL h2

theorem f97_c1_inhabited :
    Nonempty (SemanticIntermediatePreimage cfgD execD) :=
  ⟨intermediatePreimageD⟩

theorem f97_c1_columns_not_identical :
    intermediatePreimageD.semanticConsumed ≠ intermediatePreimageD.semanticAdded := by
  intro h
  have h2 :=
    congrArg (fun l : List ((nmrMEF F97 K97cubic).Rec) => l[2]?) h
  simp [intermediatePreimageD] at h2
  have : semR ≠ semL := by
    intro he
    have := congrArg (fun r : (nmrMEF F97 K97cubic).Rec => r.2.2) he
    norm_num [semR, semL] at this
  exact this h2

/-- CL's named discharge object agrees with the independent last-two swap. -/
theorem cl_discharge_agrees_with_independent_perm :
    PairedRecordLayout execD :=
  pairedRecordLayout_distinctCensus

/-! ## Axis 1 continued / CM contingency. `timestampClosed` at F97 from PRL -/

-- Form R leftover first-row `counts = 0` / `indicator = 0` (live is `chainOneBitWeight`).
variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)


/-- CM at F97: the named extra through the existing bridge, applied to the
    independent Perm, not to a new constructor. -/
theorem timestampClosed_at_f97_from_independent_prl :
    ∀ i : Fin (distinctCensusExecution hfirstD).cfg.memRows,
      memoryMemRecKind ((distinctCensusExecution hfirstD).exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt (distinctCensusExecution hfirstD).cfg.challenges.α
          ((distinctCensusExecution hfirstD).exec.memoryRowAt i).2.2.mem.ts :=
  GenericHonestData.timestampClosed_of_paired_record_layout
    (E := distinctCensusExecution hfirstD)
    (DistinctCensusCommitment.honestVerD hfirstD) f97_paired_from_lists

/-- Production CM path is definitionally the same bridge at the CL Perm. -/
theorem cm_production_path_is_the_bridge :
    timestampClosed_of_distinctCensus_paired_records hfirstD =
      GenericHonestData.timestampClosed_of_paired_record_layout
        (E := distinctCensusExecution hfirstD)
        (DistinctCensusCommitment.honestVerD hfirstD)
        pairedRecordLayout_distinctCensus := by
  -- Both sides are the production bridge at the CL Perm under honest `ver`.
  rfl

/-- Op6 finite-column-read inhabitant: a different proof, not a widening of
    the F97 written scope. -/
def op6_timestampClosed_finite_read :=
  SizeWindowBoundOp6.timestampClosed

def op9_timestampClosed_finite_read :=
  SlotSemanticsOp9.timestampClosed

/-! ## Axis 2. Weakening: written-scope tick; generic extra remains -/

/-- `MemoryRecordPremises` is still two named fields. `timestampClosed` is
    not deleted. If PRL or C1 were a field this would not compile. -/
theorem memoryRecordPremises_eta_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } := by
  cases M
  rfl

/-- `axisNat` is still filled from `E` (NMR). `timestampClosed` stays named. -/
theorem axisNat_still_from_nmr (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  GenericHonestData.axisNat_of_execution E hhon

/-- Honest assembly still takes named `timestampClosed`. -/
def memoryRecordPremises_constructor_still_takes_timestampClosed :=
  @GenericHonestData.memoryRecordPremises_of_timestampClosed

/-- The PRL → `timestampClosed` bridge still takes PRL as a hypothesis.
    CM is not an independent generic close. -/
def timestampClosed_bridge_still_takes_prl :=
  @GenericHonestData.timestampClosed_of_paired_record_layout

/-- Named-premises `Data` constructor still takes `MemoryRecordPremises`.
    Not `∀ E, Data E`. Not C1. -/
def dataOfCensus_still_takes_named_memory :=
  @GenericHonestData.dataOfCensus

/-- Package constructor still takes `Data E` and `Inputs E`. -/
def packageOf_still_takes_data_and_inputs :=
  @GenericHonestPackage.packageOf

/-- Three-field eta: `firstLine` already left. C1 is not a residual field. -/
theorem residualPremises_eta_three
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

theorem censusRecordPremises_eta_five
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } := by
  cases C
  rfl

/-- Fourteen fields: C1 was not added. If it were a field this would fail. -/
theorem still_fourteen (E : BuildableNockExecution F K) :
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
  E.eta_with_memoryTrace

/-- The generic extra remaining is the
    constructor still taking named `timestampClosed` / PRL, which CL already
    disclaims as `∀ E`. -/
theorem batch153_tick_not_licensed_is_fixture_prl :
    PairedRecordLayout execD :=
  Batch153.batch153_tick_not_licensed.1

/-- CL does not claim a generic close. -/
theorem written_scope_inhabitant_is_the_gated_perm :
    PairedRecordLayout execD ∧
      (∀ i : Fin (distinctCensusExecution hfirstD).cfg.memRows,
        memoryMemRecKind ((distinctCensusExecution hfirstD).exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt (distinctCensusExecution hfirstD).cfg.challenges.α
            ((distinctCensusExecution hfirstD).exec.memoryRowAt i).2.2.mem.ts) :=
  ⟨f97_paired_from_lists, timestampClosed_at_f97_from_independent_prl hfirstD⟩

/-! ## Axis 3. Drift: C1 / PRL / timestampClosed / counted-event / counts -/

theorem prl_is_consumed_added_perm
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    PairedRecordLayout exec =
      (consumedRecordList exec).Perm (addedRecordList exec) :=
  paired_record_layout_is_consumed_added_perm exec

theorem timestampClosed_is_existence (α ts : K) :
    MemoryTimestampClosedAt α ts = ∃ e : ℕ, ts = α ^ e :=
  rfl

/-- C1 is a semantic NMR-record preimage, not the `MemRec` Perm and not
    `∃ e, ts = α^e`. -/
theorem c1_has_semantic_columns
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticIntermediatePreimage cfg exec) :
    IO.LmIO cfg.Ksz w.semanticConsumed w.semanticAdded ∧
      bridgeRecords F K cfg.challenges.α cfg.challenges.lam w.semanticAdded =
        (addedRecordList exec).map (fun r => NockVM.encRecC r (exec.cprimeOf r)) ∧
      bridgeRecords F K cfg.challenges.α cfg.challenges.lam w.semanticConsumed =
        (consumedRecordList exec).map (fun r => NockVM.encRecC r (exec.cprimeOf r)) :=
  ⟨w.semantic_lmio, w.added_bridge, w.consumed_bridge⟩

/-- `E` already carries count balance, which is strictly weaker than PRL. -/
theorem execution_already_has_count_balance
    (E : BuildableNockExecution F K) :
    memoryStateCount E.exec .verify_child =
      memoryStateCount E.exec .read_root :=
  execution_recordCountBalance_is_count_equality E

theorem prl_implies_count_balance
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : PairedRecordLayout exec) :
    RecordCountBalanced exec :=
  recordCountBalanced_of_pairedRecordLayout h

/-- Length equality does not recover `List.Perm`. No converse is claimed. -/
theorem equal_lengths_not_perm :
    ([0] : List Nat).length = ([1] : List Nat).length ∧
      ¬ ([0] : List Nat).Perm [1] := by
  decide

/-- Counted-event route still takes event exclusions. Not retried. -/
def counted_event_route_still_takes_exclusions :=
  @pairedRecordLayout_of_counted_events

/-- Production `c1_iff_paired_at_f97` reverse does not inspect PRL.
    Fixture coincidence, not type interchange. CL does not claim it. -/
theorem f97_c1_reverse_ignores_paired
    (_h : PairedRecordLayout execD) :
    Nonempty (SemanticIntermediatePreimage cfgD execD) :=
  ⟨intermediatePreimageD⟩

theorem c1_implies_prl_on_every_E
    (E : BuildableNockExecution F K)
    (w : SemanticIntermediatePreimage E.cfg E.exec) :
    PairedRecordLayout E.exec :=
  pairedRecordLayout_of_intermediatePreimage E w

/-! ## Axis 5. -/

theorem residualPremises_still_three_fields
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  residualPremises_still_three P

/-- Outcome 2: no constructor `∀ E, Data E`. -/
theorem no_universal_data_from_E_alone
    (g : ∀ E : BuildableNockExecution F K, Data E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  GenericHonestData.generic_data_would_force_q_equality g

variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]
variable [Fintype F] [DecidableEq F]

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen
    {n : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K n)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  ⟨optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth, rfl⟩

theorem capstone_at_f97_packageR
    (hax : OptimizedComputeFinalTrace.FormRAxisBound
      (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis (packageR hfirstD).optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F97) :
    OptimizedFullStrictThm54Statement (packageR hfirstD) :=
  optimizedFullStrictNockVMROM_of_package (packageR hfirstD) hax hbasis hwidth

theorem independent_exact_eleven_one_two_accounting :
    Batch91.reviewedSubstantiveFields.length = 11 ∧
      Batch91.reviewedTypeSummaryFields.length = 1 ∧
      Batch91.reviewedResidualFields =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      Batch91.reviewedResidualFields.length = 2 ∧
      (Batch91.reviewedSubstantiveFields ++ Batch91.reviewedTypeSummaryFields ++
        Batch91.reviewedResidualFields).Nodup ∧
      11 + 1 + 2 = 14 :=
  Batch91.exact_eleven_one_two_partition

theorem eleven_one_two_pin : 11 + 1 + 2 = 14 :=
  GenericHonestPackage.residual_pair_still_eleven_one_two

end

/-! ## Axis 4. -/

#print axioms f97_added_is_FTLR
#print axioms f97_consumed_is_FTRL
#print axioms recR_ne_recL
#print axioms f97_lists_not_identical
#print axioms f97_perm_is_last_two_swap
#print axioms f97_paired_from_lists
#print axioms f97_perm_is_not_identity
#print axioms f97_c1_inhabited
#print axioms f97_c1_columns_not_identical
#print axioms cl_discharge_agrees_with_independent_perm
#print axioms timestampClosed_at_f97_from_independent_prl
#print axioms cm_production_path_is_the_bridge
#print axioms op6_timestampClosed_finite_read
#print axioms op9_timestampClosed_finite_read
#print axioms memoryRecordPremises_eta_two
#print axioms axisNat_still_from_nmr
#print axioms memoryRecordPremises_constructor_still_takes_timestampClosed
#print axioms timestampClosed_bridge_still_takes_prl
#print axioms dataOfCensus_still_takes_named_memory
#print axioms packageOf_still_takes_data_and_inputs
#print axioms residualPremises_eta_three
#print axioms censusRecordPremises_eta_five
#print axioms still_fourteen
#print axioms batch153_tick_not_licensed_is_fixture_prl
#print axioms written_scope_inhabitant_is_the_gated_perm
#print axioms prl_is_consumed_added_perm
#print axioms timestampClosed_is_existence
#print axioms c1_has_semantic_columns
#print axioms execution_already_has_count_balance
#print axioms prl_implies_count_balance
#print axioms equal_lengths_not_perm
#print axioms counted_event_route_still_takes_exclusions
#print axioms f97_c1_reverse_ignores_paired
#print axioms c1_implies_prl_on_every_E
#print axioms residualPremises_still_three_fields
#print axioms no_universal_data_from_E_alone
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms capstone_at_f97_packageR
#print axioms independent_exact_eleven_one_two_accounting
#print axioms eleven_one_two_pin
#print axioms optimizedFullStrictNockVMROM_of_package

end Nock.RedTeam.Batch159
