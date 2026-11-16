import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.Framework.NockInstances

/-!
# Exact execution-dependent realization of `Def:one-hot`

There is no free row type: compute and memory
rows are separately tagged wrappers around the two active `Fin` prefixes of `cfg`, and every table
value is read through `exec.computePubAt`, `exec.computeDecAt`, or `exec.memoryPubAt`.

The paper's advertised size remains **ten numeric opcodes plus the separately represented
structural `cons` action**.  For condition 4, `OP_IO` is all eleven actions because every Nock action
opens at least the always-operative first record.  Consequently condition 4b's "no requesting
opcode is active" antecedent is impossible; this module proves that vacuity explicitly.  It also
proves the substantive second half of condition 4: slots at or beyond the active action's
`recordCount` are zero.

Condition 2 is represented honestly.  Every active memory row has exactly one `pub.mem` column and
that exact eight-coordinate value is exposed as `memoryRecordAt`; the row is accepted by `Vmem`.
For padding/non-record states this one column may be `MemRec.zero`.  This does not mean that every
row emits an external response: condition 5 uses the canonical `responseRecords` extractor, under
which only `read_root` emits.

Likewise, `recordCount` is the opcode's structural lookup arity forced by `memBlk`; it is not
claimed equal to the length of the nonzero-filtered `requestRecords` list in degenerate field rows.
The exact three slots and the canonical filtered extractor are both exposed.
-/

namespace Nock.NockVMROM.Thm54

open Classical
open Nock Nock.ComputeTable Nock.MemoryTable
open Nock.Framework

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## Exact row indices and canonical projections -/

/-- The two row tags are distinct indices, not values stored in a free common `Row` type. -/
inductive ExactRowTag
  | compute
  | memory
deriving DecidableEq

/-- The active row count selected by a row tag. -/
def exactRowCount (cfg : ExactConfig F K) : ExactRowTag → ℕ
  | .compute => cfg.compRows
  | .memory => cfg.memRows

/-- A tag-indexed active row.  The tag remains in the type even when the two active counts happen
to be equal, so a compute row cannot be passed to a memory-row API by definitional reduction. -/
structure ExactRowIndex (cfg : ExactConfig F K) (tag : ExactRowTag) where
  index : Fin (exactRowCount cfg tag)

/-- Official compute-row index of the realization. -/
abbrev ExactComputeRow (cfg : ExactConfig F K) := ExactRowIndex cfg .compute

/-- Official memory-row index of the realization. -/
abbrev ExactMemoryRow (cfg : ExactConfig F K) := ExactRowIndex cfg .memory

/-- The canonical public compute row under the tagged active index. -/
def exactComputePubAt {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : ExactComputeRow cfg) : ComputeTable.Pub K :=
  exec.computePubAt i.index

/-- The canonical decomposition row under the same tagged compute index. -/
def exactComputeDecAt {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : ExactComputeRow cfg) : ComputeTable.Dec K :=
  exec.computeDecAt i.index

/-- The canonical public memory row under the tagged active index. -/
def exactMemoryPubAt {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : ExactMemoryRow cfg) : MemoryTable.Pub K :=
  exec.memoryPubAt i.index

/-- Both official row domains are inhabited because `ExactConfig` requires positive active
capacities. -/
theorem exactRowDomains_nonempty (cfg : ExactConfig F K) :
    Nonempty (ExactComputeRow cfg) ∧ Nonempty (ExactMemoryRow cfg) :=
  ⟨⟨⟨⟨0, cfg.compRows_pos⟩⟩⟩, ⟨⟨⟨0, cfg.memRows_pos⟩⟩⟩⟩

/-- The tag equality needed to transport a compute row into the memory-row API is impossible. -/
theorem exactRowTags_discriminated :
    ExactRowTag.compute ≠ ExactRowTag.memory := by
  intro h
  cases h

/-! ## Condition data, all defined from the exact execution -/

/-- The ten numeric selectors `OP_0,...,OP_9`, read from the actual canonical compute row. -/
def numericSelector {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : ExactComputeRow cfg) (op : Fin 10) : K :=
  ComputeTable.opSel (exactComputePubAt exec i).state (sfin op.castSucc)

/-- The separately represented structural `cons` selector, read from the same actual row. -/
def structuralConsSelector {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : ExactComputeRow cfg) : K :=
  ComputeTable.opSel (exactComputePubAt exec i).state (sfin (Fin.last 10))

/-- A uniform eleven-action selector used only where the paper quantifies over `OP`.  Indices
`0,...,9` are numeric and index `10` is structural `cons`. -/
def actionSelector {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : ExactComputeRow cfg) (action : Fin 11) : K :=
  ComputeTable.opSel (exactComputePubAt exec i).state (sfin action)

/-- Nock's memory-requesting action set.  It is all ten numeric actions plus structural `cons`. -/
def exactOPIO : Finset (Fin 11) := Finset.univ

/-- The exact action-dependent number of structurally opened records. -/
def exactRegs (action : Fin 11) : ℕ :=
  recordCount (sfin action)

/-- One of the three exact unencoded `IO_comp` slots. -/
def computeRawIO {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : ExactComputeRow cfg) (slot : Fin 3) : ComputeTable.MemRec K :=
  ![(exactComputePubAt exec i).mr1,
    (exactComputePubAt exec i).mr2,
    (exactComputePubAt exec i).mr3] slot

/-- The three unencoded `IO_comp` slots of one actual compute row, in canonical paper order. -/
def computeRawIOSlots {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : ExactComputeRow cfg) : List (ComputeTable.MemRec K) :=
  List.ofFn (computeRawIO exec i)

/-- The eight-coordinate encoding of one exact `IO_comp` slot. -/
def computeIO {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : ExactComputeRow cfg) (slot : Fin 3) : Fin 9 → K :=
  NockVM.encRec (computeRawIO exec i slot)

/-- The single nine-coordinate memory-record representation contributed by an actual memory row.
It may be the encoding of `MemRec.zero`; external emission is a separate condition-5 notion. -/
def memoryRecordAt {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : ExactMemoryRow cfg) : Fin 9 → K :=
  NockVM.encRecC (exactMemoryPubAt exec i).mem (exactMemoryPubAt exec i).cprime

/-- The actual raw `pub.mem` list, with one entry for every active memory row. -/
def actualMemoryRecords {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    List (ComputeTable.MemRec K) :=
  List.ofFn fun i : Fin cfg.memRows => (exec.memoryPubAt i).mem

/-- The encoded version of `actualMemoryRecords`. -/
def actualEncodedMemoryRecords {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    List (Fin 9 → K) :=
  List.ofFn fun i : Fin cfg.memRows =>
    NockVM.encRecC (exec.memoryPubAt i).mem (exec.memoryPubAt i).cprime

/-! ## The five paper conditions -/

/-- Paper condition 1 on every actual compute row, together with the exact active-capacity bound
`h₁ = cfg.compRows ≤ 2^cfg.orbit.h`. -/
structure ExactOneHotCondition1 (cfg : ExactConfig F K)
    (exec : ExactExecution cfg) : Prop where
  h1_capacity : cfg.compRows ≤ 2 ^ cfg.orbit.h
  numeric_boolean :
    ∀ (i : ExactComputeRow cfg) (op : Fin 10),
      numericSelector exec i op * (1 - numericSelector exec i op) = 0
  structural_boolean :
    ∀ i : ExactComputeRow cfg,
      structuralConsSelector exec i * (1 - structuralConsSelector exec i) = 0
  exactly_one_action :
    ∀ i : ExactComputeRow cfg,
      (∑ op : Fin 10, numericSelector exec i op) + structuralConsSelector exec i = 1

/-- Paper condition 2 on every actual memory row, together with
`h₂ = cfg.memRows ≤ 2^cfg.orbit.h`.

"One record verified per row" means that `Vmem` accepts the row containing exactly its one
`pub.mem` column and `memoryRecordAt` is that column's exact nine-coordinate representation.  No
nonzero or `read_root` premise is asserted: zero/padding rows still have this represented column. -/
structure ExactOneHotCondition2 (cfg : ExactConfig F K)
    (exec : ExactExecution cfg) : Prop where
  h2_capacity : cfg.memRows ≤ 2 ^ cfg.orbit.h
  row_verified :
    ∀ i : ExactMemoryRow cfg,
      MemoryTable.Vmem cfg.challenges.memoryInputs (exactMemoryPubAt exec i)
  exact_record_representation :
    ∀ i : ExactMemoryRow cfg,
      memoryRecordAt exec i =
        NockVM.encRecC (exactMemoryPubAt exec i).mem (exactMemoryPubAt exec i).cprime

/-- Paper condition 3: `IO_comp` is exactly the row's three canonical record slots,
`requestRecords` is exactly their canonical nonzero-filtered list, and the active action's
structural record arity lies in `[1,3]`. -/
structure ExactOneHotCondition3 (cfg : ExactConfig F K)
    (exec : ExactExecution cfg) : Prop where
  exact_slot_vector :
    ∀ i : ExactComputeRow cfg,
      List.ofFn (computeRawIO exec i) = computeRawIOSlots exec i
  canonical_request_extractor :
    ∀ i : ExactComputeRow cfg,
      ComputeTable.requestRecords (exactComputePubAt exec i) =
        (computeRawIOSlots exec i).filter
          (fun r => decide (r ≠ (ComputeTable.MemRec.zero : ComputeTable.MemRec K)))
  recordCount_pos :
    ∀ i : ExactComputeRow cfg,
      1 ≤ recordCount (exactComputePubAt exec i).state
  recordCount_le_three :
    ∀ i : ExactComputeRow cfg,
      recordCount (exactComputePubAt exec i).state ≤ 3

/-- Paper condition 4.  `OP_IO` and `regs` are the concrete all-action set and
state-dependent arity function.  The no-`OP_IO` antecedent is proved impossible.  The zero-padding
clauses are substantive consequences of the accepted row's `memBlk`. -/
structure ExactOneHotCondition4 (cfg : ExactConfig F K)
    (exec : ExactExecution cfg) : Prop where
  opIO_all : exactOPIO = Finset.univ
  regs_exact : ∀ action : Fin 11, exactRegs action = recordCount (sfin action)
  no_zero_opIO_antecedent :
    ∀ i : ExactComputeRow cfg,
      ¬ (∑ action ∈ exactOPIO, actionSelector exec i action) = 0
  extra_raw_slots_zero :
    ∀ (i : ExactComputeRow cfg) (slot : Fin 3),
      recordCount (exactComputePubAt exec i).state ≤ (slot : ℕ) →
        computeRawIO exec i slot = ComputeTable.MemRec.zero
  extra_encoded_slots_zero :
    ∀ (i : ExactComputeRow cfg) (slot : Fin 3),
      recordCount (exactComputePubAt exec i).state ≤ (slot : ℕ) →
        ∀ c : Fin 9, computeIO exec i slot c = 0

/-- Paper condition 5.  The number of emitted responses is at most the number of actual memory
rows, and every raw or encoded emitted response is the `mem` value of an actual `ver = true` row.  The witness also places the raw record in the full actual memory-row `mem`
list. -/
structure ExactOneHotCondition5 (cfg : ExactConfig F K)
    (exec : ExactExecution cfg) : Prop where
  response_capacity : exec.rawResponses.length ≤ cfg.memRows
  raw_responses_in_place :
    ∀ r ∈ exec.rawResponses,
      ∃ i : ExactMemoryRow cfg,
        (exactMemoryPubAt exec i).ver = true ∧
          r = (exactMemoryPubAt exec i).mem ∧
          r ∈ actualMemoryRecords exec
  encoded_responses_in_place :
    ∀ r ∈ exec.derivedResponseIO,
      ∃ i : ExactMemoryRow cfg,
        (exactMemoryPubAt exec i).ver = true ∧
          r = memoryRecordAt exec i ∧
          (exactMemoryPubAt exec i).mem ∈ actualMemoryRecords exec

/-- Its only indices are the one `cfg` and its one
dependent `exec`; in particular there is no selectable `Row` type or independently supplied IO. -/
structure OneHotRealization (cfg : ExactConfig F K)
    (exec : ExactExecution cfg) : Prop where
  condition1 : ExactOneHotCondition1 cfg exec
  condition2 : ExactOneHotCondition2 cfg exec
  condition3 : ExactOneHotCondition3 cfg exec
  condition4 : ExactOneHotCondition4 cfg exec
  condition5 : ExactOneHotCondition5 cfg exec

/-! ## Extractor and padding lemmas -/

private theorem flatMap_length_le_length_of_each_le_one
    {α β : Type*} (xs : List α) (f : α → List β)
    (h : ∀ x ∈ xs, (f x).length ≤ 1) :
    (xs.flatMap f).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hx : (f x).length ≤ 1 := h x (by simp)
      have hxs : ∀ y ∈ xs, (f y).length ≤ 1 := by
        intro y hy
        exact h y (by simp [hy])
      have htail := ih hxs
      omega

/-- The canonical response extractor has at most one output per actual memory row. -/
theorem rawResponses_length_le_memRows {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) :
    exec.rawResponses.length ≤ cfg.memRows := by
  have hflat :
      (exec.memoryRows.flatMap
        (fun row => MemoryTable.responseRecords row.2.2)).length ≤
        exec.memoryRows.length := by
    apply flatMap_length_le_length_of_each_le_one
    intro row hrow
    cases hv : row.2.2.ver <;> simp [MemoryTable.responseRecords, hv]
  simpa [ExactExecution.rawResponses] using hflat

/-- Every raw response selected by `rawResponses` comes from a canonical indexed `ver = true` row
and belongs to the actual memory-row record list. -/
theorem rawResponses_in_place_from_extractors {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) :
    ∀ r ∈ exec.rawResponses,
      ∃ i : ExactMemoryRow cfg,
        (exactMemoryPubAt exec i).ver = true ∧
          r = (exactMemoryPubAt exec i).mem ∧
          r ∈ actualMemoryRecords exec := by
  intro r hr
  rw [ExactExecution.rawResponses,
    exec.memoryRows_eq_ofFn_memoryRowAt] at hr
  obtain ⟨row, hrow, hrecord⟩ := List.mem_flatMap.mp hr
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hrow
  subst row
  change r ∈ MemoryTable.responseRecords (exec.memoryPubAt i) at hrecord
  cases hver : (exec.memoryPubAt i).ver with
  | false => simp [MemoryTable.responseRecords, hver] at hrecord
  | true =>
      have hrmem : r = (exec.memoryPubAt i).mem := by
        simpa [MemoryTable.responseRecords, hver] using hrecord
      refine ⟨⟨i⟩, ?_, hrmem, ?_⟩
      · simpa [exactMemoryPubAt] using hver
      · apply List.mem_ofFn.mpr
        exact ⟨i, hrmem.symm⟩

/-- Encoded responses inherit the same in-place indexed `ver = true` witness. -/
theorem encodedResponses_in_place_from_extractors {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) :
    ∀ r ∈ exec.derivedResponseIO,
      ∃ i : ExactMemoryRow cfg,
        (exactMemoryPubAt exec i).ver = true ∧
          r = memoryRecordAt exec i ∧
          (exactMemoryPubAt exec i).mem ∈ actualMemoryRecords exec := by
  intro r hr
  rw [ExactExecution.derivedResponseIO] at hr
  obtain ⟨row, hrow, hr'⟩ := List.mem_flatMap.mp hr
  split_ifs at hr' with hver
  · have hrfl : r = NockVM.encRecC row.2.2.mem row.2.2.cprime :=
      List.mem_singleton.mp hr'
    rw [ExactExecution.memoryRows_eq_ofFn_memoryRowAt] at hrow
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
    refine ⟨⟨i⟩, ?_, ?_, ?_⟩
    · simpa [exactMemoryPubAt, ExactExecution.memoryPubAt] using hver
    · rw [hrfl, memoryRecordAt, exactMemoryPubAt]
      rfl
    · exact List.mem_ofFn.mpr ⟨i, rfl⟩
  · cases hr'

/-- Zero is absent when every opcode-active request record is nonzero.  The premise is explicit:
the canonical extractor omits inactive slots by state arity and does not discard an active record
merely because its field encoding is zero. -/
theorem zero_padding_not_mem_rawRequests {cfg : ExactConfig F K}
    (exec : ExactExecution cfg)
    (hactive : ∀ row ∈ exec.computeRows, ∀ r ∈
      NockVM.activeRequestRecords row.2.2.1,
      r ≠ (ComputeTable.MemRec.zero : ComputeTable.MemRec K)) :
    (ComputeTable.MemRec.zero : ComputeTable.MemRec K) ∉ exec.rawRequests := by
  intro hzero
  rw [ExactExecution.rawRequests] at hzero
  obtain ⟨row, hrow, hrecord⟩ := List.mem_flatMap.mp hzero
  exact hactive row hrow _ hrecord rfl

/-! ## Realization from the exact chained language -/

/-- Every exact chained semantic execution realizes all five paper conditions.  `Vmem` supplies
condition 2; `Vcomp` supplies the `memBlk` facts used for condition-4 zero padding.  All remaining
facts are exact-capacity, selector, or canonical-extractor consequences. -/
theorem ChainedSemanticExactLanguage.oneHotRealization
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    OneHotRealization cfg exec where
  condition1 :=
    { h1_capacity := cfg.compRows_le
      numeric_boolean := by
        intro i op
        exact ComputeTable.opSel_boolean
          (exactComputePubAt exec i).state (sfin op.castSucc)
      structural_boolean := by
        intro i
        exact ComputeTable.opSel_boolean
          (exactComputePubAt exec i).state (sfin (Fin.last 10))
      exactly_one_action := by
        intro i
        simp only [numericSelector, structuralConsSelector]
        rw [← Fin.sum_univ_castSucc
          (f := fun action : Fin 11 =>
            ComputeTable.opSel (K := K) (exactComputePubAt exec i).state (sfin action))]
        exact (nock_opcode_oneHot K (exactComputePubAt exec i).state).2 }
  condition2 :=
    { h2_capacity := cfg.memRows_le
      row_verified := by
        intro i
        exact h.semantic.memoryVmemAt i.index
      exact_record_representation := by
        intro i
        rfl }
  condition3 :=
    { exact_slot_vector := by
        intro i
        rfl
      canonical_request_extractor := by
        intro i
        simp [computeRawIOSlots, computeRawIO, ComputeTable.requestRecords_spec]
      recordCount_pos := by
        intro i
        exact Nock.Framework.recordCount_pos (exactComputePubAt exec i).state
      recordCount_le_three := by
        intro i
        simpa [NockVM.mem_record_arity] using
          Nock.Framework.recordCount_le (exactComputePubAt exec i).state }
  condition4 :=
    { opIO_all := rfl
      regs_exact := fun _ => rfl
      no_zero_opIO_antecedent := by
        intro i hzero
        have hone :
            (∑ action ∈ exactOPIO, actionSelector exec i action) = (1 : K) := by
          simpa [exactOPIO, actionSelector] using
            (nock_opcode_oneHot K (exactComputePubAt exec i).state).2
        exact zero_ne_one (hzero.symm.trans hone)
      extra_raw_slots_zero := by
        intro i slot hslot
        have hv := h.semantic.computeVcompAt i.index
        have hmem :
            ComputeTable.memBlk cfg.challenges.computeInputs
              (exactComputePubAt exec i) (exactComputeDecAt exec i) := by
          exact hv.2.2.2.1
        fin_cases slot
        · norm_num at hslot
          have hpos := Nock.Framework.recordCount_pos (exactComputePubAt exec i).state
          omega
        · norm_num at hslot
          have hz := Nock.Framework.memBlk_mr2_zero K
            cfg.challenges.computeInputs
            (exactComputePubAt exec i) (exactComputeDecAt exec i)
            hmem (by simpa using hslot)
          simpa [computeRawIO] using hz
        · norm_num at hslot
          have hz := Nock.Framework.memBlk_mr3_zero K
            cfg.challenges.computeInputs
            (exactComputePubAt exec i) (exactComputeDecAt exec i)
            hmem (by simpa using hslot)
          simpa [computeRawIO] using hz
      extra_encoded_slots_zero := by
        intro i slot hslot c
        have hz :
            computeRawIO exec i slot =
              (ComputeTable.MemRec.zero : ComputeTable.MemRec K) := by
          have hv := h.semantic.computeVcompAt i.index
          have hmem :
              ComputeTable.memBlk cfg.challenges.computeInputs
                (exactComputePubAt exec i) (exactComputeDecAt exec i) := by
            exact hv.2.2.2.1
          fin_cases slot
          · norm_num at hslot
            have hpos := Nock.Framework.recordCount_pos (exactComputePubAt exec i).state
            omega
          · norm_num at hslot
            have hz2 := Nock.Framework.memBlk_mr2_zero K
              cfg.challenges.computeInputs
              (exactComputePubAt exec i) (exactComputeDecAt exec i)
              hmem (by simpa using hslot)
            simpa [computeRawIO] using hz2
          · norm_num at hslot
            have hz3 := Nock.Framework.memBlk_mr3_zero K
              cfg.challenges.computeInputs
              (exactComputePubAt exec i) (exactComputeDecAt exec i)
              hmem (by simpa using hslot)
            simpa [computeRawIO] using hz3
        rw [computeIO, hz]
        exact Nock.Framework.encRec_zero K c }
  condition5 :=
    { response_capacity := rawResponses_length_le_memRows exec
      raw_responses_in_place := rawResponses_in_place_from_extractors exec
      encoded_responses_in_place := encodedResponses_in_place_from_extractors exec }

/-- The exact chained realization of all five `Def:one-hot` clauses for
every concrete configuration and its dependent execution.  Keeping `cfg` and `exec` inside this
proposition lets the Layer-1 capstone pin the complete exact statement without inventing a free row
type; the strict package specializes the same proposition to its one shared execution. -/
abbrev ExactChainedOneHot (F K : Type) [Field F] [Field K] [Algebra F K] : Prop :=
  ∀ (cfg : ExactConfig F K) (exec : ExactExecution cfg),
    ChainedSemanticExactLanguage cfg exec → OneHotRealization cfg exec

/-- The exact chained Nock execution realizes every `Def:one-hot` condition. -/
theorem exactChainedOneHot (F K : Type) [Field F] [Field K] [Algebra F K] :
    ExactChainedOneHot F K :=
  fun _ _ h => h.oneHotRealization

/-! ## Explicit condition-4b and negative regressions -/

/-- Condition 4b's first zero-row clause is true only by an impossible antecedent.  This theorem
keeps the vacuity visible at the use site rather than presenting it as a substantive zero gate. -/
theorem OneHotRealization.condition4b_vacuous
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (R : OneHotRealization cfg exec) :
    ∀ i : ExactComputeRow cfg,
      (∑ action ∈ exactOPIO, actionSelector exec i action) = 0 →
        ∀ (slot : Fin 3) (c : Fin 9), computeIO exec i slot c = 0 := by
  intro i hzero
  exact (R.condition4.no_zero_opIO_antecedent i hzero).elim

/-- Missing-memory-row regression: an emitted response cannot lack a matching actual memory row. -/
theorem OneHotRealization.missing_memory_row_rejected
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (R : OneHotRealization cfg exec) (r : ComputeTable.MemRec K)
    (hemitted : r ∈ exec.rawResponses)
    (hmissing : ∀ i : ExactMemoryRow cfg, (exactMemoryPubAt exec i).mem ≠ r) :
    False := by
  obtain ⟨i, -, hr, -⟩ := R.condition5.raw_responses_in_place r hemitted
  exact hmissing i hr.symm

/-- Foreign raw-response regression: a record outside the actual memory-row `mem` list cannot be
emitted by the official realization. -/
theorem OneHotRealization.foreign_raw_response_rejected
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (R : OneHotRealization cfg exec) (r : ComputeTable.MemRec K)
    (hforeign : r ∉ actualMemoryRecords exec) :
    r ∉ exec.rawResponses := by
  intro hemitted
  obtain ⟨i, hstate, hr, hmem⟩ :=
    R.condition5.raw_responses_in_place r hemitted
  exact hforeign hmem

/-- The official encoded response list is a subset of the encoded actual memory-row record list. -/
theorem OneHotRealization.derivedResponseIO_subset_actualEncodedMemoryRecords
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (R : OneHotRealization cfg exec) :
    exec.derivedResponseIO ⊆ actualEncodedMemoryRecords exec := by
  intro r hr
  obtain ⟨i, -, hir, -⟩ := R.condition5.encoded_responses_in_place r hr
  apply List.mem_ofFn.mpr
  exact ⟨i.index, hir.symm⟩

/-- Foreign encoded-response regression. -/
theorem OneHotRealization.foreign_encoded_response_rejected
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (R : OneHotRealization cfg exec) (r : Fin 9 → K)
    (hforeign : r ∉ actualEncodedMemoryRecords exec) :
    r ∉ exec.derivedResponseIO :=
  fun hr => hforeign (R.derivedResponseIO_subset_actualEncodedMemoryRecords hr)

/-- The two exact active capacities exposed by the official realization. -/
theorem OneHotRealization.active_capacities
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (R : OneHotRealization cfg exec) :
    cfg.compRows ≤ 2 ^ cfg.orbit.h ∧ cfg.memRows ≤ 2 ^ cfg.orbit.h :=
  ⟨R.condition1.h1_capacity, R.condition2.h2_capacity⟩

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.ChainedSemanticExactLanguage.oneHotRealization
#print axioms Nock.NockVMROM.Thm54.OneHotRealization.condition4b_vacuous
#print axioms Nock.NockVMROM.Thm54.OneHotRealization.missing_memory_row_rejected
#print axioms Nock.NockVMROM.Thm54.OneHotRealization.foreign_encoded_response_rejected
#print axioms Nock.NockVMROM.Thm54.zero_padding_not_mem_rawRequests
#print axioms Nock.NockVMROM.Thm54.exactRowDomains_nonempty
#print axioms Nock.NockVMROM.Thm54.exactRowTags_discriminated
