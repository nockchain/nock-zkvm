import Nock.NockVMROM.Thm54.MonolithicRowLayout
import Nock.NockVMROM.Thm54.FiniteFieldIO
import Nock.NockVMROM.Thm54.ChainedLanguage

/-!
Theorem 5.4 fixes the memory chip `RAP_NockMem-IO` as verifying "a forest with
`M` nodes and `L` memory records", with

* `M + 2L` **total number of rows**.

The four memory states are `{decompose, halt, read_root, verify_child}`.
`decompose` and `halt` are the genuine forest nodes; `read_root` and `verify_child` are the two
unit-fanout wrapper states added in the paper so that each memory record is *added* to the
`intermediate` accumulator once and *removed* once.  Hence the row
budget `M + 2L`.

## What is proved here, over the real carrier

`ExactExecution.memoryRows` is the BFS projection of the authoritative memory forest.  Over it:

* `memoryRows_state_partition` — the four per-state row counts sum to the total, unconditionally;
* `readRootCount_eq_L` — the `read_root` row count *is* `L = derivedResponseIO.length`,
  unconditionally, because `MemoryTable.responseRecords` emits exactly one record on a
  `read_root` row and none on any other row;
* `RecordCountBalanced` — the exact row-accounting proposition
  `#verify_child = #read_root`;
* `memory_rows_eq_M_add_two_mul_L_iff` — the paper's row budget holds **iff**
  `RecordCountBalanced`, unconditionally;
* `memory_rows_eq_M_add_two_mul_L_of_count_balance` — the row budget directly from that exact
  count premise;
* `PairedRecordLayout` remains available as a stronger optional control: its multiset permutation
  implies `RecordCountBalanced`, but the row budget does not imply the permutation.

The row-count identity is equivalent to count balance.  It does not recover which records were
paired.

## Co-residence of the finite-field IO accumulator

Packet C's `FiniteIO.PostChallengeIOWitness` indexes its response accumulator by *records*
(`Fin (responses.length + 1)`).  Read naively that is an appended `L + 1` phase.  This module
shows it is not one: the same accumulator is realized as a `read_root`-selector-gated column over
the table's own `M + 2L` rows (`coResidentAcc`), which

* is stationary on every non-`read_root` row (`coResidentAcc_stationary`),
* fires on exactly the `L` `read_root` rows (`coResidentAcc_firing_rows`), and
* already equals Packet C's record-indexed terminal at row index `M + 2L`
  (`coResidentAcc_terminal_eq_responseAcc`).

`NoAppendedIOPhase` bundles these and `noAppendedIOPhase_of_accepts` discharges it from
`FiniteIO.FiniteIOAccepts`.
-/

namespace Nock.NockVMROM.Thm54.RowLayout

open Nock Nock.Walk

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## The four memory states and their row counts -/

/-- The four memory states `𝒮 = {decompose, halt, read_root, verify_child}`. -/
def memStates : List MemoryTable.MState :=
  [.decompose, .halt, .read_root, .verify_child]

theorem memStates_nodup : memStates.Nodup := by decide

theorem mem_memStates (s : MemoryTable.MState) : s ∈ memStates := by
  cases s <;> decide

/-- The memory-table row count of one state, over the authoritative BFS row list.  The state is
read off the row's public label `Pub.st`, which is what drives record emission. -/
def memoryStateCount {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (s : MemoryTable.MState) : ℕ :=
  fibreCount (fun row : MemoryTable.MState × MemoryTable.DTmem K => row.2.2.st)
    exec.memoryRows s

/-- `M` — the forest nodes proper: the `decompose` and `halt` rows. -/
def memoryM {cfg : ExactConfig F K} (exec : ExactExecution cfg) : ℕ :=
  memoryStateCount exec .decompose + memoryStateCount exec .halt

/-- `L` — the paper's memory-record count in the `M + 2L` row budget.
Unconditionally the `#read_root` fibre (available from `RecordCountBalanced` alone). Under
honest `ver = (st = read_root)` this equals `|IO_mem| = derivedResponseIO.length`. -/
def memoryL {cfg : ExactConfig F K} (exec : ExactExecution cfg) : ℕ :=
  memoryStateCount exec .read_root

/-- IO-list length reading of `L` (equals `memoryL` under honest `ver`). -/
def responseCount {cfg : ExactConfig F K} (exec : ExactExecution cfg) : ℕ :=
  exec.derivedResponseIO.length

/-- **Unconditional four-way row partition.**  Every memory row is in exactly one of the four
states, so the four counts sum to the total row count. -/
theorem memoryRows_state_partition {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    memoryStateCount exec .decompose + memoryStateCount exec .halt
        + memoryStateCount exec .read_root + memoryStateCount exec .verify_child
      = exec.memoryRows.length := by
  have h :=
    sum_fibreCount_eq_length memStates memStates_nodup
      (fun row : MemoryTable.MState × MemoryTable.DTmem K => row.2.2.st)
      exec.memoryRows (fun row _ => mem_memStates row.2.2.st)
  simpa [memStates, memoryStateCount, List.sum_cons, add_assoc] using h

/-! ## `read_root` rows are exactly the `L` served records -/

/-- The encoded served-record list has one entry per `ver = true` row.
    Under honest `ver = (st = read_root)` this equals the `read_root` fibre count. -/
theorem length_flatMap_responseRecords
    (l : List (MemoryTable.MState × MemoryTable.DTmem K))
    (hhon : ∀ a ∈ l, a.2.2.ver = decide (a.2.2.st = MemoryTable.MState.read_root)) :
    (l.flatMap (fun row => if row.2.2.ver then [NockVM.encRecC row.2.2.mem row.2.2.cprime] else [])).length
      = fibreCount (fun row : MemoryTable.MState × MemoryTable.DTmem K => row.2.2.st) l
          MemoryTable.MState.read_root := by
  induction l with
  | nil => simp [fibreCount]
  | cons a t ih =>
    have hhon' : ∀ a ∈ t, a.2.2.ver = decide (a.2.2.st = MemoryTable.MState.read_root) := by
      intro x hx; exact hhon x (by simp [hx])
    have ha := hhon a (by simp)
    rw [List.flatMap_cons, List.length_append, ih hhon', fibreCount_cons]
    rw [show a.2.2.ver = decide (a.2.2.st = MemoryTable.MState.read_root) from ha]
    cases h : a.2.2.st <;> simp [h] <;> try omega

/-- Under honest `ver`, the IO-list length equals the budget `L = #read_root`. -/
theorem responseCount_eq_L {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (hhon : ∀ row ∈ exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    responseCount exec = memoryL exec := by
  unfold responseCount memoryL ExactExecution.derivedResponseIO memoryStateCount
  exact length_flatMap_responseRecords exec.memoryRows hhon

theorem readRootCount_eq_L {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (_hhon : ∀ row ∈ exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    memoryStateCount exec .read_root = memoryL exec :=
  rfl

/-! ## The record-balance hypothesis and the `M + 2L` budget -/

/-- **Exact record-count balance for the `M + 2L` budget**.
There is one `verify_child` wrapper row for every `read_root` wrapper row.  This proposition records
only the row accounting required by Theorem 5.4; it does not assert that the two record lists are a
multiset permutation. -/
def RecordCountBalanced {cfg : ExactConfig F K} (exec : ExactExecution cfg) : Prop :=
  memoryStateCount exec .verify_child = memoryStateCount exec .read_root

/-- The record removed from `intermediate` by a `verify_child` row;
every other state removes nothing.  This is the exact mirror of the by-state `read_root`
add below.  External IO uses `MemoryTable.responseRecords` (`ver`). -/
def consumedRecords (pub : MemoryTable.Pub K) : List (ComputeTable.MemRec K) :=
  match pub.st with
  | .verify_child => [pub.mem]
  | _ => []

/-- Records added to `intermediate` by the `read_root` rows, in BFS row order.  By state — not by `ver` (external IO is `responseRecords`). -/
def addedRecordList {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    List (ComputeTable.MemRec K) :=
  exec.memoryRows.flatMap fun row =>
    match row.2.2.st with
    | .read_root => [row.2.2.mem]
    | .decompose | .halt | .verify_child => []

/-- Records removed from `intermediate` by the `verify_child` rows, in BFS row order. -/
def consumedRecordList {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    List (ComputeTable.MemRec K) :=
  exec.memoryRows.flatMap (fun row => consumedRecords row.2.2)

omit [Field K] in
theorem length_flatMap_consumedRecords
    (l : List (MemoryTable.MState × MemoryTable.DTmem K)) :
    (l.flatMap (fun row => consumedRecords row.2.2)).length
      = fibreCount (fun row : MemoryTable.MState × MemoryTable.DTmem K => row.2.2.st) l
          MemoryTable.MState.verify_child := by
  induction l with
  | nil => simp [fibreCount]
  | cons a t ih =>
    rw [List.flatMap_cons, List.length_append, ih, fibreCount_cons]
    cases h : a.2.2.st <;> simp [consumedRecords, h] <;> try omega

theorem verifyChildCount_eq_consumed_length {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) :
    memoryStateCount exec .verify_child = (consumedRecordList exec).length :=
  (length_flatMap_consumedRecords exec.memoryRows).symm

omit [Field K] in
theorem length_flatMap_addedRecords
    (l : List (MemoryTable.MState × MemoryTable.DTmem K)) :
    (l.flatMap fun row =>
        match row.2.2.st with
        | .read_root => [row.2.2.mem]
        | .decompose | .halt | .verify_child => []).length
      = fibreCount (fun row : MemoryTable.MState × MemoryTable.DTmem K => row.2.2.st) l
          MemoryTable.MState.read_root := by
  induction l with
  | nil => simp [fibreCount]
  | cons a t ih =>
    rw [List.flatMap_cons, List.length_append, ih, fibreCount_cons]
    cases h : a.2.2.st <;> simp [h] <;> try omega

theorem readRootCount_eq_added_length {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) :
    memoryStateCount exec .read_root = (addedRecordList exec).length := by
  unfold addedRecordList memoryStateCount
  exact (length_flatMap_addedRecords exec.memoryRows).symm

omit [Field K] in
/-- Under honest `ver`, the flatMap of `responseRecords` equals the by-state add list. -/
theorem flatMap_responseRecords_eq_added
    (l : List (MemoryTable.MState × MemoryTable.DTmem K))
    (hhon : ∀ a ∈ l, a.2.2.ver = decide (a.2.2.st = MemoryTable.MState.read_root)) :
    l.flatMap (fun row => MemoryTable.responseRecords row.2.2) =
      l.flatMap fun row =>
        match row.2.2.st with
        | .read_root => [row.2.2.mem]
        | .decompose | .halt | .verify_child => [] := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have hhon' : ∀ a ∈ t, a.2.2.ver = decide (a.2.2.st = MemoryTable.MState.read_root) := by
      intro x hx; exact hhon x (by simp [hx])
    have ha := hhon a (by simp)
    rw [List.flatMap_cons, List.flatMap_cons, ih hhon',
      MemoryTable.responseRecords_of_honest_ver _ ha]
    cases a.2.2.st <;> rfl

/-- Under honest `ver`, raw external responses equal the intermediate add list. -/
theorem rawResponses_eq_addedRecordList {cfg : ExactConfig F K}
    (exec : ExactExecution cfg)
    (hhon : ∀ row ∈ exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    ExactExecution.rawResponses exec = addedRecordList exec := by
  rw [ExactExecution.rawResponses_eq_memoryRows, addedRecordList]
  exact flatMap_responseRecords_eq_added exec.memoryRows hhon

/-- **`PairedRecordLayout`.**  Every memory record that a `read_root` row adds to
the `intermediate` accumulator is removed again by a `verify_child` row, and nothing else is
removed: the two record lists agree as multisets.  This is the paper's own statement of the
memory layout — "every timestamp needs to be removed from the IO multiset, added to
`intermediate`, and then removed again".  It is a stronger optional condition sufficient for the
row budget; the budget itself needs only `RecordCountBalanced`. -/
def PairedRecordLayout {cfg : ExactConfig F K} (exec : ExactExecution cfg) : Prop :=
  (consumedRecordList exec).Perm (addedRecordList exec)

theorem mem_addedRecordList_of_read_root {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) (i : Fin cfg.memRows)
    (h : (exec.memoryPubAt i).st = MemoryTable.MState.read_root) :
    (exec.memoryPubAt i).mem ∈ addedRecordList exec := by
  rw [addedRecordList, List.mem_flatMap]
  refine ⟨exec.memoryRowAt i, exec.memoryRowAt_mem i, ?_⟩
  simp only [ExactExecution.memoryPubAt] at h ⊢
  simp [h]

theorem mem_consumedRecordList_of_verify_child {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) (i : Fin cfg.memRows)
    (h : (exec.memoryPubAt i).st = MemoryTable.MState.verify_child) :
    (exec.memoryPubAt i).mem ∈ consumedRecordList exec := by
  rw [consumedRecordList, List.mem_flatMap]
  refine ⟨exec.memoryRowAt i, exec.memoryRowAt_mem i, ?_⟩
  simp [consumedRecords, ExactExecution.memoryPubAt] at h ⊢
  simp [h]

/-- Under `PairedRecordLayout`, `#verify_child = |addedRecordList|` (hence `= memoryL`). -/
theorem verifyChildCount_eq_added_length {cfg : ExactConfig F K}
    {exec : ExactExecution cfg} (h : PairedRecordLayout exec) :
    memoryStateCount exec .verify_child = (addedRecordList exec).length := by
  rw [verifyChildCount_eq_consumed_length]
  exact h.length_eq

theorem verifyChildCount_eq_readRootCount {cfg : ExactConfig F K}
    {exec : ExactExecution cfg} (h : PairedRecordLayout exec) :
    memoryStateCount exec .verify_child = memoryStateCount exec .read_root := by
  rw [verifyChildCount_eq_added_length h, readRootCount_eq_added_length exec]

/-- A multiset-level record pairing implies the count balance needed by the row budget. -/
theorem recordCountBalanced_of_pairedRecordLayout {cfg : ExactConfig F K}
    {exec : ExactExecution cfg} (h : PairedRecordLayout exec) :
    RecordCountBalanced exec :=
  verifyChildCount_eq_readRootCount h

/-- **The `M + 2L` row budget is *equivalent* to `verify_child`/`read_root` row-count balance.**
Unconditional against the **read_root count** (not yet `memoryL`); under honest `ver` one has
`readRootCount_eq_L` so the paper's `M + 2L` with `L = derivedResponseIO.length` follows. -/
theorem memory_rows_eq_M_add_two_mul_L_iff {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) :
    exec.memoryRows.length = memoryM exec + 2 * memoryL exec
      ↔ RecordCountBalanced exec := by
  have hpart := memoryRows_state_partition exec
  unfold memoryM memoryL RecordCountBalanced
  omega

/-- **`M + 2L` total rows directly from exact count balance**. -/
theorem memory_rows_eq_M_add_two_mul_L_of_count_balance {cfg : ExactConfig F K}
    {exec : ExactExecution cfg} (h : RecordCountBalanced exec) :
    exec.memoryRows.length = memoryM exec + 2 * memoryL exec :=
  (memory_rows_eq_M_add_two_mul_L_iff exec).mpr h

theorem memory_rows_eq_M_add_two_mul_memoryL_of_count_balance {cfg : ExactConfig F K}
    {exec : ExactExecution cfg} (h : RecordCountBalanced exec) :
    exec.memoryRows.length = memoryM exec + 2 * memoryL exec :=
  memory_rows_eq_M_add_two_mul_L_of_count_balance h

theorem memory_rows_eq_M_add_two_mul_memoryL_iff {cfg : ExactConfig F K}
    (exec : ExactExecution cfg)
    (_hhon : ∀ row ∈ exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    exec.memoryRows.length = memoryM exec + 2 * memoryL exec
      ↔ RecordCountBalanced exec :=
  memory_rows_eq_M_add_two_mul_L_iff exec

/-- **`M + 2L` total number of rows.** -/
theorem memory_rows_eq_M_add_two_mul_L {cfg : ExactConfig F K}
    {exec : ExactExecution cfg} (h : PairedRecordLayout exec) :
    exec.memoryRows.length = memoryM exec + 2 * memoryL exec :=
  memory_rows_eq_M_add_two_mul_L_of_count_balance
    (recordCountBalanced_of_pairedRecordLayout h)

/-- The configured active memory length is the paper's `M + 2L`. -/
theorem memRows_eq_M_add_two_mul_L_of_count_balance {cfg : ExactConfig F K}
    {exec : ExactExecution cfg} (h : RecordCountBalanced exec) :
    cfg.memRows = memoryM exec + 2 * memoryL exec := by
  rw [← exec.memoryRows_length]
  exact memory_rows_eq_M_add_two_mul_L_of_count_balance h

theorem memRows_eq_M_add_two_mul_L {cfg : ExactConfig F K}
    {exec : ExactExecution cfg} (h : PairedRecordLayout exec) :
    cfg.memRows = memoryM exec + 2 * memoryL exec := by
  rw [← exec.memoryRows_length]
  exact memory_rows_eq_M_add_two_mul_L h

/-! ## Co-residence: the IO accumulator is a selector-gated column on these rows -/

/-- The paper's `ver` selector as a field element. -/
def ioSelector (row : MemoryTable.MState × MemoryTable.DTmem K) : K :=
  if row.2.2.ver then 1 else 0

/-- The selector-gated contribution of one memory row to the IO accumulator column.  On a
`ver = false` row this is exactly `0`, so the row is a no-op for the accumulator. -/
def ioRowTerm (comp : (Fin 9 → K) → K)
    (row : MemoryTable.MState × MemoryTable.DTmem K) : K :=
  ioSelector row * (comp (NockVM.encRecC row.2.2.mem row.2.2.cprime))⁻¹

/-- Signed `read − verify` selector for the internal `intermediate` column. -/
def interSelector (row : MemoryTable.MState × MemoryTable.DTmem K) : K :=
  if row.2.2.st = MemoryTable.MState.read_root then 1
  else if row.2.2.st = MemoryTable.MState.verify_child then -1
  else 0

/-- Row-level memory: the intermediate record is the row's own `(…, T, ts, C')`
(`encRecC mem cprime`, the record the chip's `poleSource` reads at role 57), not `C' = 1`. -/
def interRowTerm (comp : (Fin 9 → K) → K)
    (row : MemoryTable.MState × MemoryTable.DTmem K) : K :=
  interSelector row * (comp (NockVM.encRecC row.2.2.mem row.2.2.cprime))⁻¹

/-- **The co-resident intermediate accumulator** at sampled `(γ, interPole)`.
Signed twin of `coResidentAcc`. -/
def interResidentAcc (comp : (Fin 9 → K) → K)
    (rows : List (MemoryTable.MState × MemoryTable.DTmem K)) (i : ℕ) : K :=
  ((rows.take i).map (interRowTerm comp)).sum

@[simp] theorem interResidentAcc_zero (comp : (Fin 9 → K) → K)
    (rows : List (MemoryTable.MState × MemoryTable.DTmem K)) :
    interResidentAcc comp rows 0 = 0 := by
  simp [interResidentAcc]

theorem interResidentAcc_succ (comp : (Fin 9 → K) → K)
    (rows : List (MemoryTable.MState × MemoryTable.DTmem K)) {i : ℕ}
    (hi : i < rows.length) :
    interResidentAcc comp rows (i + 1)
      = interResidentAcc comp rows i + interRowTerm comp rows[i] := by
  unfold interResidentAcc
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]

/-- The column at the last row is the signed sum over every memory row. -/
theorem interResidentAcc_last (comp : (Fin 9 → K) → K)
    (rows : List (MemoryTable.MState × MemoryTable.DTmem K)) :
    interResidentAcc comp rows rows.length = (rows.map (interRowTerm comp)).sum := by
  simp [interResidentAcc, List.take_length]

/-- Signed row sum = added-record sum minus consumed-record sum.
Both sides are by-state (`interSelector` / `addedRecordList` / `consumedRecords`). -/
theorem sum_interRowTerm_eq_added_sub_consumed (comp : (Fin 9 → K) → K)
    (rows : List (MemoryTable.MState × MemoryTable.DTmem K))
    (cp : ComputeTable.MemRec K → K)
    (hcp : ∀ row ∈ rows, row.2.2.cprime = cp row.2.2.mem) :
    (rows.map (interRowTerm comp)).sum
      = (((rows.flatMap fun row =>
              match row.2.2.st with
              | .read_root => [row.2.2.mem]
              | .decompose | .halt | .verify_child => []).map
            (fun r => NockVM.encRecC r (cp r))).map (fun v => (comp v)⁻¹)).sum
        - (((rows.flatMap (fun row => consumedRecords row.2.2)).map
            (fun r => NockVM.encRecC r (cp r))).map
              (fun v => (comp v)⁻¹)).sum := by
  induction rows with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons,
      ih (fun row hrow => hcp row (List.mem_cons_of_mem a hrow)), List.flatMap_cons,
      List.flatMap_cons, List.map_append, List.map_append, List.map_append, List.map_append,
      List.sum_append, List.sum_append]
    have ha : a.2.2.cprime = cp a.2.2.mem := hcp a (List.mem_cons_self ..)
    cases h : a.2.2.st <;>
      (simp [consumedRecords, interRowTerm, interSelector, h, ha]; try ring)

/-- **Terminal vanishing from PRL.** -/
theorem interResidentAcc_last_of_paired {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) (comp : (Fin 9 → K) → K)
    (h : PairedRecordLayout exec) (hC : exec.CprimeCoherent) :
    interResidentAcc comp exec.memoryRows exec.memoryRows.length = 0 := by
  rw [interResidentAcc_last,
    sum_interRowTerm_eq_added_sub_consumed comp _ exec.cprimeOf
      (ExactExecution.cprime_eq_cprimeOf hC)]
  exact sub_eq_zero.mpr
    (((h.map (fun r => NockVM.encRecC r (exec.cprimeOf r))).map
      (fun r => (comp r)⁻¹)).sum_eq).symm

/-- **The co-resident IO accumulator column.**  One value per memory-row boundary
`0 … memoryRows.length`; there is no record-indexed phase. -/
def coResidentAcc (comp : (Fin 9 → K) → K)
    (rows : List (MemoryTable.MState × MemoryTable.DTmem K)) (i : ℕ) : K :=
  ((rows.take i).map (ioRowTerm comp)).sum

@[simp] theorem coResidentAcc_zero (comp : (Fin 9 → K) → K)
    (rows : List (MemoryTable.MState × MemoryTable.DTmem K)) :
    coResidentAcc comp rows 0 = 0 := by
  simp [coResidentAcc]

/-- The column is updated by a single row-local transition per memory row. -/
theorem coResidentAcc_succ (comp : (Fin 9 → K) → K)
    (rows : List (MemoryTable.MState × MemoryTable.DTmem K)) {i : ℕ}
    (hi : i < rows.length) :
    coResidentAcc comp rows (i + 1)
      = coResidentAcc comp rows i + ioRowTerm comp rows[i] := by
  unfold coResidentAcc
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]

/-- **Selector gating.**  On any `ver = false` row the accumulator is stationary. -/
theorem coResidentAcc_stationary (comp : (Fin 9 → K) → K)
    (rows : List (MemoryTable.MState × MemoryTable.DTmem K)) {i : ℕ}
    (hi : i < rows.length) (hver : rows[i].2.2.ver = false) :
    coResidentAcc comp rows (i + 1) = coResidentAcc comp rows i := by
  rw [coResidentAcc_succ comp rows hi]
  simp [ioRowTerm, ioSelector, hver]

/-- On a `ver = true` row the accumulator adds exactly the reciprocal of the compressed served
record — the same summand Packet C's record-indexed accumulator adds. -/
theorem coResidentAcc_step_read_root (comp : (Fin 9 → K) → K)
    (rows : List (MemoryTable.MState × MemoryTable.DTmem K)) {i : ℕ}
    (hi : i < rows.length) (hver : rows[i].2.2.ver = true) :
    coResidentAcc comp rows (i + 1)
      = coResidentAcc comp rows i
        + (comp (NockVM.encRecC rows[i].2.2.mem rows[i].2.2.cprime))⁻¹ := by
  rw [coResidentAcc_succ comp rows hi]
  simp [ioRowTerm, ioSelector, hver]

/-- Row-wise and record-wise summation agree: the gated row column and the record column have the
same total. -/
theorem sum_ioRowTerm_eq_record_sum (comp : (Fin 9 → K) → K)
    (rows : List (MemoryTable.MState × MemoryTable.DTmem K)) :
    (rows.map (ioRowTerm comp)).sum
      = ((rows.flatMap fun row =>
            if row.2.2.ver then [NockVM.encRecC row.2.2.mem row.2.2.cprime] else []).map
          (fun v => (comp v)⁻¹)).sum := by
  induction rows with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ih, List.flatMap_cons, List.map_append,
      List.sum_append]
    cases hv : a.2.2.ver <;>
      simp [ioRowTerm, ioSelector, hv]

/-- The column's value at the last table row is the sum over the `L` served records. -/
theorem coResidentAcc_last {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (comp : (Fin 9 → K) → K) :
    coResidentAcc comp exec.memoryRows exec.memoryRows.length
      = (exec.derivedResponseIO.map (fun v => (comp v)⁻¹)).sum := by
  unfold coResidentAcc
  rw [List.take_of_length_le (le_refl _)]
  rw [sum_ioRowTerm_eq_record_sum]
  rfl

/-- **The co-resident column reaches Packet C's record-indexed terminal.**  Given a finite-field
IO witness accepted against the very same served-record list, the selector-gated column over the
`M + 2L` memory rows already equals `responseAcc (Fin.last _)` at row `M + 2L`. -/
theorem coResidentAcc_terminal_eq_responseAcc {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) {coins : FiniteIO.IOCoins K}
    {records : FiniteIO.PreChallengeRecords K 9}
    {w : FiniteIO.PostChallengeIOWitness records coins}
    (hacc : FiniteIO.FiniteIOAccepts records coins w)
    (hrec : records.responses = exec.derivedResponseIO) :
    coResidentAcc (FiniteIO.compress coins) exec.memoryRows exec.memoryRows.length
      = w.responseAcc (Fin.last _) := by
  rw [coResidentAcc_last exec (FiniteIO.compress coins), hacc.responseTerm, FiniteIO.responseAcc_last hacc, ← hrec]
  rw [← FiniteIO.sum_fin_get records.responses (fun v => (FiniteIO.compress coins v)⁻¹)]
  exact Finset.sum_congr rfl (fun j _ => (FiniteIO.responseInv_eq hacc j).symm)

theorem coResidentAcc_terminal_eq_responseAcc_map {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) {m : ℕ} {coins : FiniteIO.IOCoins K}
    {records : FiniteIO.PreChallengeRecords K m}
    {w : FiniteIO.PostChallengeIOWitness records coins}
    (hacc : FiniteIO.FiniteIOAccepts records coins w)
    (f : (Fin 9 → K) → (Fin m → K))
    (hrec : records.responses = exec.derivedResponseIO.map f) :
    coResidentAcc (fun v => FiniteIO.compress coins (f v)) exec.memoryRows
        exec.memoryRows.length
      = w.responseAcc (Fin.last _) := by
  rw [coResidentAcc_last exec, hacc.responseTerm, FiniteIO.responseAcc_last hacc]
  have hsum : (exec.derivedResponseIO.map (fun v => (FiniteIO.compress coins (f v))⁻¹)).sum
      = (records.responses.map (fun v => (FiniteIO.compress coins v)⁻¹)).sum := by
    rw [hrec, List.map_map]; rfl
  rw [hsum, ← FiniteIO.sum_fin_get records.responses (fun v => (FiniteIO.compress coins v)⁻¹)]
  exact Finset.sum_congr rfl (fun j _ => (FiniteIO.responseInv_eq hacc j).symm)

/-- Exactly `responseCount` of the rows fire the IO `ver` selector. -/
theorem coResidentAcc_firing_rows {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.memoryRows.countP
        (fun row : MemoryTable.MState × MemoryTable.DTmem K => row.2.2.ver)
      = responseCount exec := by
  unfold responseCount ExactExecution.derivedResponseIO
  induction exec.memoryRows with
  | nil => simp
  | cons a t ih =>
    rw [List.flatMap_cons, List.length_append, List.countP_cons]
    cases hv : a.2.2.ver <;> simp [hv, ih, add_comm]

/-- Under honest `ver`, the firing count is the budget `L`. -/
theorem coResidentAcc_firing_rows_eq_L {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (hhon : ∀ row ∈ exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    exec.memoryRows.countP
        (fun row : MemoryTable.MState × MemoryTable.DTmem K => row.2.2.ver)
      = memoryL exec :=
  (coResidentAcc_firing_rows exec).trans (responseCount_eq_L exec hhon)

/-- **No appended IO phase.**  The finite-field IO accumulator of Packet C is *co-resident* with
the memory table: it is a column on the table's own rows, starting at `0` before row `0`, updated
by one row-local `read_root`-gated transition per memory row, stationary on every other row, and
already at the record-indexed terminal by the last table row.  Nothing is evaluated after row
`M + 2L`, so no `records + 1` phase is appended. -/
structure NoAppendedIOPhase {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (coins : FiniteIO.IOCoins K)
    {records : FiniteIO.PreChallengeRecords K 9}
    (w : FiniteIO.PostChallengeIOWitness records coins) : Prop where
  /-- The records the IO witness commits to are exactly the rows' served records. -/
  records_are_row_records : records.responses = exec.derivedResponseIO
  /-- The column starts empty before the first table row. -/
  init : coResidentAcc (FiniteIO.compress coins) exec.memoryRows 0 = 0
  /-- One row-local transition per memory row — no extra rows. -/
  rowLocal : ∀ i, ∀ hi : i < exec.memoryRows.length,
    coResidentAcc (FiniteIO.compress coins) exec.memoryRows (i + 1)
      = coResidentAcc (FiniteIO.compress coins) exec.memoryRows i + ioRowTerm (FiniteIO.compress coins) exec.memoryRows[i]
  /-- Selector-gated: `ver = false` rows are no-ops. -/
  gated : ∀ i, ∀ hi : i < exec.memoryRows.length,
    exec.memoryRows[i].2.2.ver = false →
      coResidentAcc (FiniteIO.compress coins) exec.memoryRows (i + 1) = coResidentAcc (FiniteIO.compress coins) exec.memoryRows i
  /-- Exactly `L` rows fire the selector. -/
  firing :
    exec.memoryRows.countP
        (fun row : MemoryTable.MState × MemoryTable.DTmem K => row.2.2.ver)
      = responseCount exec
  /-- The record-indexed terminal is reached at the last table row. -/
  terminalOnTable :
    coResidentAcc (FiniteIO.compress coins) exec.memoryRows exec.memoryRows.length = w.responseAcc (Fin.last _)

/-- Co-residence holds for every accepted finite-field IO witness over the rows' own served
records. -/
theorem noAppendedIOPhase_of_accepts {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    {coins : FiniteIO.IOCoins K} {records : FiniteIO.PreChallengeRecords K 9}
    {w : FiniteIO.PostChallengeIOWitness records coins}
    (hacc : FiniteIO.FiniteIOAccepts records coins w)
    (hrec : records.responses = exec.derivedResponseIO) :
    NoAppendedIOPhase exec coins w where
  records_are_row_records := hrec
  init := coResidentAcc_zero (FiniteIO.compress coins) exec.memoryRows
  rowLocal := fun _ hi => coResidentAcc_succ (FiniteIO.compress coins) exec.memoryRows hi
  gated := fun _ hi hver => coResidentAcc_stationary (FiniteIO.compress coins) exec.memoryRows hi hver
  firing := coResidentAcc_firing_rows exec
  terminalOnTable := coResidentAcc_terminal_eq_responseAcc exec hacc hrec

/-- **The co-resident column lives on exactly `M + 2L` rows.**  Combining the layout
theorem with co-residence: the IO accumulator column has one entry per memory-row boundary. -/
theorem coResident_column_height {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : RecordCountBalanced exec) (coins : FiniteIO.IOCoins K) :
    coResidentAcc (FiniteIO.compress coins) exec.memoryRows (memoryM exec + 2 * memoryL exec)
      = coResidentAcc (FiniteIO.compress coins) exec.memoryRows exec.memoryRows.length := by
  exact congrArg (coResidentAcc (FiniteIO.compress coins) exec.memoryRows)
    (memory_rows_eq_M_add_two_mul_L_of_count_balance h).symm

end

end Nock.NockVMROM.Thm54.RowLayout

#print axioms Nock.NockVMROM.Thm54.RowLayout.memStates_nodup
#print axioms Nock.NockVMROM.Thm54.RowLayout.mem_memStates
#print axioms Nock.NockVMROM.Thm54.RowLayout.memoryRows_state_partition
#print axioms Nock.NockVMROM.Thm54.RowLayout.length_flatMap_responseRecords
#print axioms Nock.NockVMROM.Thm54.RowLayout.readRootCount_eq_L
#print axioms Nock.NockVMROM.Thm54.RowLayout.length_flatMap_consumedRecords
#print axioms Nock.NockVMROM.Thm54.RowLayout.verifyChildCount_eq_consumed_length
#print axioms Nock.NockVMROM.Thm54.RowLayout.readRootCount_eq_added_length
#print axioms Nock.NockVMROM.Thm54.RowLayout.verifyChildCount_eq_readRootCount
#print axioms Nock.NockVMROM.Thm54.RowLayout.recordCountBalanced_of_pairedRecordLayout
#print axioms Nock.NockVMROM.Thm54.RowLayout.memory_rows_eq_M_add_two_mul_L_iff
#print axioms Nock.NockVMROM.Thm54.RowLayout.memory_rows_eq_M_add_two_mul_L_of_count_balance
#print axioms Nock.NockVMROM.Thm54.RowLayout.memory_rows_eq_M_add_two_mul_L
#print axioms Nock.NockVMROM.Thm54.RowLayout.memRows_eq_M_add_two_mul_L_of_count_balance
#print axioms Nock.NockVMROM.Thm54.RowLayout.memRows_eq_M_add_two_mul_L
#print axioms Nock.NockVMROM.Thm54.RowLayout.coResidentAcc_zero
#print axioms Nock.NockVMROM.Thm54.RowLayout.coResidentAcc_succ
#print axioms Nock.NockVMROM.Thm54.RowLayout.coResidentAcc_stationary
#print axioms Nock.NockVMROM.Thm54.RowLayout.coResidentAcc_step_read_root
#print axioms Nock.NockVMROM.Thm54.RowLayout.sum_ioRowTerm_eq_record_sum
#print axioms Nock.NockVMROM.Thm54.RowLayout.coResidentAcc_last
#print axioms Nock.NockVMROM.Thm54.RowLayout.coResidentAcc_terminal_eq_responseAcc
#print axioms Nock.NockVMROM.Thm54.RowLayout.coResidentAcc_firing_rows
#print axioms Nock.NockVMROM.Thm54.RowLayout.noAppendedIOPhase_of_accepts
#print axioms Nock.NockVMROM.Thm54.RowLayout.coResident_column_height
