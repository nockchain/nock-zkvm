import Nock.NockVMROM.Thm54.PairedRecordIOResult
import Nock.NockVMROM.Thm54.FiniteFieldIOSoundness
import Nock.NockVMROM.Thm54.BuildableChips
import Nock.NockVMROM.Thm54.ForestExponentOrderClosure
import Nock.NockVMROM.Thm54.P8Core.PairedRecordCountedEvent
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option maxHeartbeats 2000000

/-!
# The counted-event soundness argument for the `intermediate` pole

the paper says the `intermediate` accumulator "is considered a witness element and its
constraints are implemented in the exact same way as in `RAP_mem-IO`, `RAP_comp-IO`", and that "the
`IO` and `intermediate` columns function as the two memory record columns that are matched within
the same table".  This module carries that instruction out literally: it builds the two record
columns as a `FiniteIO.PreChallengeRecords`, reads the memory table's own `(γ, β)` as a
`FiniteIO.IOCoins` in the `[M3]` pole convention, and reuses the repo's counted events **verbatim**.

**Comment and docstring only, no statement or proof changed.**
The gate cite `2123` was always right, and the
neighbouring `
to `2120` here.

## What is established

* **§A/§B.**  Every fact `FiniteIOAccepts` supplies to `finiteIO_sound` holds on `E` for the
  `intermediate` columns: the inverse gate (`interCompress_ne_zero`) from the paper's
  the paper genericity, and the endpoint log-derivative identity (`interEndpoint_sum_eq`)
  **unconditionally**, because it *is* `execution_logup_mass_balanced`.  So the question "does the
  `intermediate` pole admit the sibling columns' treatment?" is answered **yes**, and compiled.
* **§C.  The closure off three counted events.**  `pairedRecordLayout_of_counted_events` derives
  `RowLayout.PairedRecordLayout`, and `timestampClosed_of_counted_events` derives
  `MemoryRecordPremises.timestampClosed` through the existing bridge, from `E` plus exclusion of
  the three counted events.  **The field-size obstruction is sidestepped**: the only size condition
  consumed is the *characteristic* bound `E.Ksz_lt_ringChar`, through
  `SetEq.mse_ldse_general`/`Lem:ldse_mse`.  The route is also `Nodup`-free: it exits through unique
  factorisation rather than through `lem:set_inclusion`, so **no
  repeat-freeness hypothesis is taken** — which matters, since `E` carries `addedRecordList_nodup`
  but nothing for the remove column.  Nothing is
  weakened: both are unconditional on `E`, so no hypothesis is added anywhere.
* **§D.  Events (1) and (2) are independent of the premise; event (3) is EQUIVALENT to it.**
  Event (2) is RLC-injectivity on the records that occur.  Event (3) is
  different in kind: its certificate `ioQP` is built out of the record columns themselves, and
  `interLogDerivGood_iff_pairedRecordLayout` compiles that, off (1) and (2) and on `E`'s own
  accumulator, **excluding event (3) is equivalent to `PairedRecordLayout`**.
* **§E.  Where the analogy with the external IO columns breaks.**  Not at the counted-event layer:
  the external columns' three exclusions are themselves **named `Inputs` fields**
  (`ioPoleHitGood` / `ioGammaGood` / `ioLogDerivGood`), i.e. assumed there too
  (`external_counted_events_are_named_inputs`).  It breaks one layer down.  The external columns'
  record-level matching is *derived on `E` from semantics* — `execution_lio_of_requestNodup`, from
  `SemanticIOPreimage`'s `derivedIO_lmio` plus `E.requestNodup` — with no counted event anywhere in
  the derivation, and `finiteIO_sound` is a separate prover-facing artifact whose event flags are
  then discharged at a fixture **using** that already-known matching
  (`ConcreteStrictPackage.io_poleGood` proves `ioQP = 0` from the two lists being the same
  singleton).  `external_matching_is_semantic_intermediate_is_not` compiles the pair.
* **§G.  The counted-event hypotheses are not available at the live F97 multi-root execution.**  That
  fixture samples `γ = 0`, where the record RLC collapses onto `mem.root.size`; two of its three
  served records then share their compressed value, so counted event (2) is **hit**
  (`multiRoot_gamma_in_collision_event`).  No J.0.3 witness for §C is constructed *in this module*.
  The
  **relocation verdict is unaffected and is confirmed by the witness**: by §D's equivalence every
  such witness already satisfies the premise, and at F73 the two record columns are literally equal,
  so the premise is free with no counted event
  (`Batch135.ConcreteF73.concrete_pairedRecordLayout_without_counted_events`) and the route extracts
  nothing.

## What is NOT claimed — read this before recording anything

No carrier field is added to `BuildableNockExecution`, `Data`, `BuildableChips.Inputs`,
`MemoryRecordPremises` or `CensusRecordPremises`; §H re-checks the eta.  The NMR axis is not
re-litigated, `ForestExponentOrder` is untouched, and no section-J checkbox is claimed.

**Disclosure — the `Finset` cardinalities of §F are not a probability measure.**  No distribution
occurs anywhere in this module, and **no probabilistic soundness statement is compiled** here or
consumed downstream from here.  The bounds are subset cardinalities of `Finset K`, in the same
idiom — and with the same limitation — as `ForestExponentOrderClosure.zeroTimestampChallengeEvent`
and `FiniteIO.IOFailureEvent`.

**Disclosure — `E` has no chronology, which is an independent reason §C is not a closure.**
`E.cfg.challenges` (carrying `β`, `γ`) and `E.exec` (carrying the two record columns) are fields of
one structure with no ordering between them, and row acceptance *pins* the challenge to the
configuration's own tuple (`PairedRecordIOResult.memory_rows_pin_the_challenge`).  So "the bad set
is small" does not, on `E` alone, yield "the sampled `(β, γ)` lies outside it".

**Disclosure — the coins of §A are the memory table's `(γ, β)`, not the external IO sample.**
`interCoins` is read off `E.cfg.challenges.memoryInputs`, the `MemoryTable.Inputs` tuple whose pole
is `RLC^γ(mem_record) − β`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Nock.NockVMROM.Thm54.PairedRecordCountedEvent

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.PairedRecordIOResult

noncomputable section

/-! ## §0. Two generic list lemmas -/

section Generic

variable {A B : Type*}

end Generic

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## §A. The `(intermediate, IO)` column pair, in the sibling columns' own shape -/

/-- The two record columns of the paper as a `FiniteIO` record pair: the `verify_child`
remove column on the "requests" side, the `read_root` add column on the "responses" side, each
flattened by `Def:MEF`.  Compare `BuildableChips.executionRecords`, the same
construction for the *external* IO columns. -/
def interRecords (E : BuildableNockExecution F K) : FiniteIO.PreChallengeRecords K 9 where
  requests := (RowLayout.consumedRecordList E.exec).map (fun r => NockVM.encRecC r
      (E.exec.cprimeOf r))
  responses := (RowLayout.addedRecordList E.exec).map (fun r => NockVM.encRecC r
      (E.exec.cprimeOf r))

/-- The **memory table's** own compression and pole challenges, in `FiniteIO`'s additive pole
convention: `gamma := γ`, `pole := −β`, because `MemoryTable.pole` is `RLC^γ(mem_record) − β` while `FiniteIO.compress` is `pole + RLC^gamma(·)` — the documented flag `[M3]`
instantiation `X ↦ −β` of the paper.  This is **not** the external
`RAP_prog-IO` sample of the paper. -/
def interCoins (E : BuildableNockExecution F K) : FiniteIO.IOCoins K where
  gamma := E.cfg.challenges.γ
  pole := -E.cfg.challenges.β

/-- The eight-coordinate flattening turns the walk RLC into the memory table's record RLC. -/
theorem rlc_encRecC (γ : K) (r : ComputeTable.MemRec K) (cprime : K) :
    Walk.rlc γ (NockVM.encRecC r cprime) = MemoryTable.recRLC γ r cprime := by
  simp [Walk.rlc, MemoryTable.recRLC, NockVM.encRecC, Fin.sum_univ_succ]
  ring

theorem rlc_encRec (γ : K) (r : ComputeTable.MemRec K) :
    Walk.rlc γ (NockVM.encRec r) = MemoryTable.recRLC γ r := by
  simpa [NockVM.encRecC_zero] using rlc_encRecC γ r 0

/-- (Replaces the `C' = 1` dummy-wire version.) -/
theorem encRecC_cp_injective (cp : ComputeTable.MemRec K → K) :
    Function.Injective (fun r => NockVM.encRecC r (cp r)) := by
  intro r s h
  have hs : ∀ i : Fin 9, NockVM.encRecC r (cp r) i = NockVM.encRecC s (cp s) i := fun i
      => congrFun h i
  refine ComputeTable.MemRec.ext (ComputeTable.FP.ext ?_ ?_ ?_)
    (ComputeTable.FP.ext ?_ ?_ ?_) ?_ ?_
  · simpa [NockVM.encRecC] using hs 0
  · simpa [NockVM.encRecC] using hs 1
  · simpa [NockVM.encRecC] using hs 2
  · simpa [NockVM.encRecC] using hs 3
  · simpa [NockVM.encRecC] using hs 4
  · simpa [NockVM.encRecC] using hs 5
  · simpa [NockVM.encRecC] using hs 6
  · simpa [NockVM.encRecC] using hs 7

theorem perm_of_perm_map_encRecC_cp (cp : ComputeTable.MemRec K → K)
    {l l' : List (ComputeTable.MemRec K)}
    (h : (l.map (fun r => NockVM.encRecC r (cp r))).Perm
      (l'.map (fun r => NockVM.encRecC r (cp r)))) : l.Perm l' := by
  have hms :
      ((l : Multiset (ComputeTable.MemRec K)).map (fun r => NockVM.encRecC r (cp r)))
        = ((l' : Multiset (ComputeTable.MemRec K)).map (fun r => NockVM.encRecC r (cp r))) := by
    rw [Multiset.map_coe, Multiset.map_coe]
    exact Multiset.coe_eq_coe.mpr h
  exact Multiset.coe_eq_coe.mp (Multiset.map_injective (encRecC_cp_injective cp) hms)

/-- **The two poles are the same pole.**  `FiniteIO`'s compressed denominator at `interCoins` is
the memory table's `intermediate` pole at the configuration's own challenge tuple. -/
theorem compress_interCoins (E : BuildableNockExecution F K) (r : ComputeTable.MemRec K) :
    FiniteIO.compress (interCoins E) (NockVM.encRecC r (E.exec.cprimeOf r))
      = MemoryTable.pole E.cfg.challenges.memoryInputs r (E.exec.cprimeOf r) := by
  show -E.cfg.challenges.β + Walk.rlc E.cfg.challenges.γ (NockVM.encRecC r (E.exec.cprimeOf r))
    = MemoryTable.recRLC E.cfg.challenges.γ r (E.exec.cprimeOf r) - E.cfg.challenges.β
  rw [rlc_encRecC]
  ring

/-- `interCoins` is read off the memory
table's `(z, β, γ)` tuple; it is a different object from the external `RAP_prog-IO` sample
`BuildableChips.Inputs.ioCoins`, and no theorem here identifies them. -/
theorem interCoins_is_the_table_pole_not_the_io_sample (E : BuildableNockExecution F K) :
    (interCoins E).gamma = E.cfg.challenges.memoryInputs.γ
      ∧ (interCoins E).pole = -E.cfg.challenges.memoryInputs.β :=
  ⟨rfl, rfl⟩

/-! ## §B. Every fact `FiniteIOAccepts` feeds `finiteIO_sound` holds on `E`

`finiteIO_sound` consumes acceptance only through three facts: the two inverse gates
(`request_compress_ne_zero`, `response_compress_ne_zero`) and the endpoint log-derivative identity
(`endpoint_sum_eq`).  Here the endpoint identity is **already on `E`, unconditionally**, and the
inverse gates are the paper's the paper genericity. -/

/-- The paper's genericity condition on exactly the two record
columns. -/
def InterPoleGeneric (E : BuildableNockExecution F K) : Prop :=
  ∀ r ∈ RowLayout.consumedRecordList E.exec ++ RowLayout.addedRecordList E.exec,
    MemoryTable.pole E.cfg.challenges.memoryInputs r (E.exec.cprimeOf r) ≠ 0

/-- Genericity, transported to `FiniteIO`'s inverse-gate form on the encoded columns. -/
theorem interCompress_ne_zero {E : BuildableNockExecution F K} (h : InterPoleGeneric E) :
    ∀ v ∈ (interRecords E).requests ++ (interRecords E).responses,
      FiniteIO.compress (interCoins E) v ≠ 0 := by
  intro v hv
  have hex : ∃ r ∈ RowLayout.consumedRecordList E.exec ++ RowLayout.addedRecordList E.exec,
      NockVM.encRecC r (E.exec.cprimeOf r) = v := by
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨r, hr, hrv⟩ := List.mem_map.mp hv
      exact ⟨r, List.mem_append_left _ hr, hrv⟩
    · obtain ⟨r, hr, hrv⟩ := List.mem_map.mp hv
      exact ⟨r, List.mem_append_right _ hr, hrv⟩
  obtain ⟨r, hr, rfl⟩ := hex
  rw [compress_interCoins]
  exact h r hr

omit [Field K] in
theorem consumedOf_eq_filter_map (pubs : List (MemoryTable.Pub K)) :
    pubs.flatMap RowLayout.consumedRecords
      = (pubs.filter (fun p => decide (p.st = MemoryTable.MState.verify_child))).map
          (fun p => p.mem) := by
  induction pubs with
  | nil => rfl
  | cons p rest ih =>
      cases hst : p.st <;> simp [RowLayout.consumedRecords, hst, ih]

omit [Field K] in
theorem addedOf_eq_filter_map (pubs : List (MemoryTable.Pub K)) :
    (pubs.flatMap fun p =>
        match p.st with
        | .read_root => [p.mem]
        | .decompose | .halt | .verify_child => [])
      = (pubs.filter (fun p => decide (p.st = MemoryTable.MState.read_root))).map
          (fun p => p.mem) := by
  induction pubs with
  | nil => rfl
  | cons p rest ih =>
      cases hst : p.st <;> simp [hst, ih]

omit [Field K] in
theorem addedRows_eq_filter_map
    (rows : List (MemoryTable.MState × MemoryTable.DTmem K)) :
    (rows.flatMap fun row =>
        match row.2.2.st with
        | .read_root => [row.2.2.mem]
        | .decompose | .halt | .verify_child => [])
      = ((rows.map (fun row => row.2.2)).filter
          (fun p => decide (p.st = MemoryTable.MState.read_root))).map
          (fun p => p.mem) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      cases hst : row.2.2.st <;> simp [hst, ih]

/-- **The endpoint identity, unconditionally on `E`.**  `finiteIO_sound`'s `endpoint_sum_eq` for
the `intermediate` columns *is* `execution_logup_mass_balanced` — the paper's own accumulator with
both global zero boundaries, derived from `MemoryRowAccepted` plus
`ChainedSemanticExactLanguage`.  Dummy `C' = Pub.cprime` (`getD 1`) is rewritten by `hC`. -/
theorem interEndpoint_sum_eq (E : BuildableNockExecution F K)
    (hC : E.exec.CprimeCoherent) :
    (∑ i, (FiniteIO.compress (interCoins E) ((interRecords E).requests.get i))⁻¹)
      = ∑ j, (FiniteIO.compress (interCoins E) ((interRecords E).responses.get j))⁻¹ := by
  have hreq :
      (∑ i, (FiniteIO.compress (interCoins E) ((interRecords E).requests.get i))⁻¹)
        = ((RowLayout.consumedRecordList E.exec).map
            (fun r => (MemoryTable.pole E.cfg.challenges.memoryInputs r (E.exec.cprimeOf r))⁻¹)).sum
                := by
    rw [FiniteIO.sum_fin_get (interRecords E).requests
      (fun v => (FiniteIO.compress (interCoins E) v)⁻¹)]
    show (((RowLayout.consumedRecordList E.exec).map (fun r => NockVM.encRecC r
        (E.exec.cprimeOf r))).map
        (fun v => (FiniteIO.compress (interCoins E) v)⁻¹)).sum = _
    rw [List.map_map]
    exact congrArg List.sum (List.map_congr_left
      (fun r _ => by simp only [Function.comp_apply, compress_interCoins]))
  have hresp :
      (∑ j, (FiniteIO.compress (interCoins E) ((interRecords E).responses.get j))⁻¹)
        = ((RowLayout.addedRecordList E.exec).map
            (fun r => (MemoryTable.pole E.cfg.challenges.memoryInputs r (E.exec.cprimeOf r))⁻¹)).sum
                := by
    rw [FiniteIO.sum_fin_get (interRecords E).responses
      (fun v => (FiniteIO.compress (interCoins E) v)⁻¹)]
    show (((RowLayout.addedRecordList E.exec).map (fun r => NockVM.encRecC r
        (E.exec.cprimeOf r))).map
        (fun v => (FiniteIO.compress (interCoins E) v)⁻¹)).sum = _
    rw [List.map_map]
    exact congrArg List.sum (List.map_congr_left
      (fun r _ => by simp only [Function.comp_apply, compress_interCoins]))
  rw [hreq, hresp]
  have hc : ∀ p ∈ GenericHonestData.memoryPubRows E.exec, p.cprime = E.exec.cprimeOf p.mem := by
    intro p hp
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hp
    exact ExactExecution.cprime_eq_cprimeOf hC row hr
  have hbal := execution_logup_mass_balanced E
  have hbal1 :
      (((GenericHonestData.memoryPubRows E.exec).filter
          (fun p => decide (p.st = MemoryTable.MState.read_root))).map
          (fun p => (MemoryTable.pole E.cfg.challenges.memoryInputs p.mem
              (E.exec.cprimeOf p.mem))⁻¹)).sum
        = (((GenericHonestData.memoryPubRows E.exec).filter
            (fun p => decide (p.st = MemoryTable.MState.verify_child))).map
            (fun p => (MemoryTable.pole E.cfg.challenges.memoryInputs p.mem
                (E.exec.cprimeOf p.mem))⁻¹)).sum := by
    convert hbal using 1 <;>
      exact congrArg List.sum (List.map_congr_left fun p hp => by
        rw [hc p (List.mem_of_mem_filter hp)])
  have hcons :
      RowLayout.consumedRecordList E.exec
        = ((GenericHonestData.memoryPubRows E.exec).filter
            (fun p => decide (p.st = MemoryTable.MState.verify_child))).map
            (fun p => p.mem) := by
    simp only [RowLayout.consumedRecordList, GenericHonestData.memoryPubRows]
    rw [← List.flatMap_map]
    exact consumedOf_eq_filter_map _
  have hadd :
      RowLayout.addedRecordList E.exec
        = ((GenericHonestData.memoryPubRows E.exec).filter
            (fun p => decide (p.st = MemoryTable.MState.read_root))).map
            (fun p => p.mem) := by
    simp only [RowLayout.addedRecordList, GenericHonestData.memoryPubRows]
    exact addedRows_eq_filter_map _
  rw [hcons, hadd, List.map_map, List.map_map]
  exact hbal1.symm

/-! ### Counted event (1) is the paper's genericity, and `MemoryTable.WF` discharges it -/

/-- Every record of the add column is the `mem` of a `read_root` accumulator row. -/
theorem exists_live_pub_of_mem_added {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    {r : ComputeTable.MemRec K} (hr : r ∈ RowLayout.addedRecordList exec) :
    ∃ p ∈ GenericHonestData.memoryPubRows exec,
      (p.st = MemoryTable.MState.read_root ∨ p.st = MemoryTable.MState.verify_child)
        ∧ p.mem = r := by
  obtain ⟨row, hrow, hresp⟩ := List.mem_flatMap.mp hr
  refine ⟨row.2.2, List.mem_map.mpr ⟨row, hrow, rfl⟩, ?_⟩
  cases hs : row.2.2.st with
  | decompose => simp [MemoryTable.responseRecords, hs] at hresp
  | halt => simp [MemoryTable.responseRecords, hs] at hresp
  | read_root =>
      refine ⟨Or.inl rfl, ?_⟩
      simp only [MemoryTable.responseRecords, hs, List.mem_singleton] at hresp
      exact hresp.symm
  | verify_child => simp [MemoryTable.responseRecords, hs] at hresp

/-- Every record of the remove column is the `mem` of a `verify_child` accumulator row. -/
theorem exists_live_pub_of_mem_consumed {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    {r : ComputeTable.MemRec K} (hr : r ∈ RowLayout.consumedRecordList exec) :
    ∃ p ∈ GenericHonestData.memoryPubRows exec,
      (p.st = MemoryTable.MState.read_root ∨ p.st = MemoryTable.MState.verify_child)
        ∧ p.mem = r := by
  obtain ⟨row, hrow, hcons⟩ := List.mem_flatMap.mp hr
  refine ⟨row.2.2, List.mem_map.mpr ⟨row, hrow, rfl⟩, ?_⟩
  cases hs : row.2.2.st with
  | decompose => simp [RowLayout.consumedRecords, hs] at hcons
  | halt => simp [RowLayout.consumedRecords, hs] at hcons
  | read_root => simp [RowLayout.consumedRecords, hs] at hcons
  | verify_child =>
      refine ⟨Or.inr rfl, ?_⟩
      simp only [RowLayout.consumedRecords, hs, List.mem_singleton] at hcons
      exact hcons.symm

/-- Membership in the accumulator's `Pub` row list exhibits a row index. -/
theorem exists_index_of_mem_memoryPubRows {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    {p : MemoryTable.Pub K} (hp : p ∈ GenericHonestData.memoryPubRows exec) :
    ∃ i : Fin cfg.memRows, p = exec.memoryPubAt i := by
  obtain ⟨n, hn, hget⟩ := List.getElem_of_mem hp
  rw [GenericHonestData.memoryPubRows_length exec] at hn
  exact ⟨⟨n, hn⟩, by rw [← GenericHonestData.memoryPubRows_getElem exec n hn, ← hget]⟩

/-- **Counted event (1) is discharged from `MemoryTable.WF` alone.** -/
theorem interPoleGeneric_of_wf (E : BuildableNockExecution F K)
    (hwf : ∀ i : Fin E.cfg.memRows,
      MemoryTable.WF E.cfg.challenges.memoryInputs (E.exec.memoryPubAt i))
    (hC : E.exec.CprimeCoherent) :
    InterPoleGeneric E := by
  intro r hr
  have hex : ∃ p ∈ GenericHonestData.memoryPubRows E.exec,
      (p.st = MemoryTable.MState.read_root ∨ p.st = MemoryTable.MState.verify_child)
        ∧ p.mem = r := by
    rcases List.mem_append.mp hr with hr | hr
    · exact exists_live_pub_of_mem_consumed E.exec hr
    · exact exists_live_pub_of_mem_added E.exec hr
  obtain ⟨p, hp, hst, hmem⟩ := hex
  have hc : p.cprime = E.exec.cprimeOf p.mem := by
    obtain ⟨row, hr, heq⟩ := List.mem_map.mp hp
    rw [← heq]; exact ExactExecution.cprime_eq_cprimeOf hC row hr
  obtain ⟨i, rfl⟩ := exists_index_of_mem_memoryPubRows E.exec hp
  rw [← hmem, ← hc]
  exact (hwf i).pole_ne hst

/-- …and equally from the exclusion of `FiniteIO`'s own counted event (1), so the two forms of
event (1) are interchangeable. -/
theorem interPoleGeneric_of_not_poleHit (E : BuildableNockExecution F K)
    (h : (interCoins E).pole ∉
      FiniteIO.IOPoleHitEvent (interRecords E) (interCoins E).gamma) :
    InterPoleGeneric E := by
  intro r hr
  have hv : NockVM.encRecC r (E.exec.cprimeOf r) ∈ (interRecords E).requests ++
      (interRecords E).responses := by
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ (List.mem_map_of_mem hr)
    · exact List.mem_append_right _ (List.mem_map_of_mem hr)
  intro hzero
  refine h ?_
  simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨NockVM.encRecC r (E.exec.cprimeOf r), hv, ?_⟩
  have hc := compress_interCoins E r
  rw [hzero] at hc
  exact hc

/-! ## §C. The counted-event closure, with only a characteristic bound

The chain is `finiteIO_sound`'s, with one deliberate change of exit: instead of leaving through
`lem:set_inclusion` it leaves through
`Lem:ldse_mse` and unique factorisation.  No `4·Ksz ≤ Fintype.card K` appears anywhere.

The *add* column's `Nodup` is nevertheless in the
cone of the length bound below, via `added_length_inRange → execution_lio_of_requestNodup →
E.requestNodup`/`addedRecordList_nodup` — both unconditional on `E`, so nothing is weakened. -/

/-- The two column lengths, in the encoded `FiniteIO` shape, sit below the characteristic. -/
theorem interRecords_lengths_lt_ringChar (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent) :
    (interRecords E).requests.length < ringChar K
      ∧ (interRecords E).responses.length < ringChar K := by
  obtain ⟨h₁, h₂⟩ := PairedRecordIOResult.column_lengths_lt_ringChar E hhon hC
  refine ⟨?_, ?_⟩
  · show ((RowLayout.consumedRecordList E.exec).map (fun r => NockVM.encRecC r
      (E.exec.cprimeOf r))).length < ringChar K
    rw [List.length_map]; exact h₁
  · show ((RowLayout.addedRecordList E.exec).map (fun r => NockVM.encRecC r
      (E.exec.cprimeOf r))).length < ringChar K
    rw [List.length_map]; exact h₂


/-- The difference polynomial vanishes at the sampled pole.  Same computation as inside
`finiteIO_sound`, run off `E`'s accumulator instead of off `FiniteIOAccepts`. -/
theorem interQP_eval_eq_zero (E : BuildableNockExecution F K) (hgen : InterPoleGeneric E)
    (hC : E.exec.CprimeCoherent) :
    (FiniteIO.ioQP (interRecords E) (interCoins E).gamma).eval (interCoins E).pole = 0 := by
  set records := interRecords E with hrec
  set coins := interCoins E with hcoin
  set A := FiniteIO.reqVals records coins.gamma with hA
  set B := FiniteIO.respVals records coins.gamma with hB
  have hcomp := interCompress_ne_zero hgen
  rw [← hrec, ← hcoin] at hcomp
  have hdA : ∀ i, coins.pole + A i ≠ 0 := fun i =>
    hcomp _ (List.mem_append_left _ (List.get_mem _ _))
  have hdB : ∀ j, coins.pole + B j ≠ 0 := fun j =>
    hcomp _ (List.mem_append_right _ (List.get_mem _ _))
  have hend : (∑ i, (coins.pole + A i)⁻¹) = ∑ j, (coins.pole + B j)⁻¹ := by
    rw [hcoin, hrec] at *
    exact interEndpoint_sum_eq E hC
  have hSA := FiniteIO.sum_inv_eval A coins.pole hdA
  have hSB := FiniteIO.sum_inv_eval B coins.pole hdB
  simp only [FiniteIO.ioQP, Polynomial.eval_sub, Polynomial.eval_mul, ← hA, ← hB]
  have h1 : (FiniteIO.numerP A).eval coins.pole * (FiniteIO.denomP B).eval coins.pole
      = ((∑ i, (coins.pole + A i)⁻¹) * (FiniteIO.denomP A).eval coins.pole)
          * (FiniteIO.denomP B).eval coins.pole := by rw [hSA]
  have h2 : (FiniteIO.numerP B).eval coins.pole * (FiniteIO.denomP A).eval coins.pole
      = ((∑ j, (coins.pole + B j)⁻¹) * (FiniteIO.denomP B).eval coins.pole)
          * (FiniteIO.denomP A).eval coins.pole := by rw [hSB]
  rw [h1, h2, hend]
  ring

/-- The symbolic log-derivative identity in `RatFunc K`, from the identically-vanishing difference
polynomial.  Same block as inside `finiteIO_sound`. -/
theorem frac_sum_eq_of_ioQP_zero {n₁ n₂ : ℕ} (A : Fin n₁ → K) (B : Fin n₂ → K)
    (hQ : FiniteIO.numerP A * FiniteIO.denomP B = FiniteIO.numerP B * FiniteIO.denomP A) :
    (∑ i, SetEq.frac (A i)) = ∑ j, SetEq.frac (B j) := by
  have hmapQ : algebraMap K[X] (RatFunc K) (FiniteIO.numerP A)
        * algebraMap K[X] (RatFunc K) (FiniteIO.denomP B)
      = algebraMap K[X] (RatFunc K) (FiniteIO.numerP B)
        * algebraMap K[X] (RatFunc K) (FiniteIO.denomP A) := by
    rw [← map_mul, ← map_mul, hQ]
  have hdAne : algebraMap K[X] (RatFunc K) (FiniteIO.denomP A) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective K)]
    exact FiniteIO.denomP_ne_zero A
  have hdBne : algebraMap K[X] (RatFunc K) (FiniteIO.denomP B) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective K)]
    exact FiniteIO.denomP_ne_zero B
  have hA' := FiniteIO.frac_sum_mul_denom A
  have hB' := FiniteIO.frac_sum_mul_denom B
  refine mul_right_cancel₀ (mul_ne_zero hdAne hdBne) ?_
  calc (∑ i, SetEq.frac (A i))
        * (algebraMap K[X] (RatFunc K) (FiniteIO.denomP A)
            * algebraMap K[X] (RatFunc K) (FiniteIO.denomP B))
      = ((∑ i, SetEq.frac (A i)) * algebraMap K[X] (RatFunc K) (FiniteIO.denomP A))
          * algebraMap K[X] (RatFunc K) (FiniteIO.denomP B) := by ring
    _ = algebraMap K[X] (RatFunc K) (FiniteIO.numerP A)
          * algebraMap K[X] (RatFunc K) (FiniteIO.denomP B) := by rw [hA']
    _ = algebraMap K[X] (RatFunc K) (FiniteIO.numerP B)
          * algebraMap K[X] (RatFunc K) (FiniteIO.denomP A) := hmapQ
    _ = ((∑ j, SetEq.frac (B j)) * algebraMap K[X] (RatFunc K) (FiniteIO.denomP B))
          * algebraMap K[X] (RatFunc K) (FiniteIO.denomP A) := by rw [hB']
    _ = (∑ j, SetEq.frac (B j))
          * (algebraMap K[X] (RatFunc K) (FiniteIO.denomP A)
              * algebraMap K[X] (RatFunc K) (FiniteIO.denomP B)) := by ring

/-- **THE COUNTED-EVENT ARGUMENT.**  `RowLayout.PairedRecordLayout` from `E`, the paper's
the paper genericity (counted event (1)), and exclusion of the repo's two soundness events
(2) and (3) — the same two `FiniteIO.finiteIO_sound` uses for the external IO columns.

The only size condition consumed is the **characteristic** bound `E.Ksz_lt_ringChar` (through
`SetEq.mse_ldse_general`).

`interLogDerivGood_iff_pairedRecordLayout` (§D) compiles that,
given `E`'s accumulator and events (1)/(2), the third hypothesis is *equivalent* to the conclusion;
and `E` carries no chronology against which the counted bad set could be discounted (module
header).  So this theorem relocates the premise to a counted layer with the field-size obstruction
removed; it does not close it. -/
theorem pairedRecordLayout_of_counted_events (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (hgen : InterPoleGeneric E)
    (hγ : (interCoins E).gamma ∉ FiniteIO.IORLCCollisionEvent (interRecords E))
    (hz : (interCoins E).pole ∉
      FiniteIO.IOLogDerivEvent (interRecords E) (interCoins E).gamma) :
    RowLayout.PairedRecordLayout E.exec := by
  classical
  have hQ0 : FiniteIO.ioQP (interRecords E) (interCoins E).gamma = 0 := by
    by_contra hne
    exact hz (by
      simp only [FiniteIO.IOLogDerivEvent, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hne, interQP_eval_eq_zero E hgen hC⟩)
  have hQ : FiniteIO.numerP (FiniteIO.reqVals (interRecords E) (interCoins E).gamma)
        * FiniteIO.denomP (FiniteIO.respVals (interRecords E) (interCoins E).gamma)
      = FiniteIO.numerP (FiniteIO.respVals (interRecords E) (interCoins E).gamma)
        * FiniteIO.denomP (FiniteIO.reqVals (interRecords E) (interCoins E).gamma) := by
    have hh := hQ0
    unfold FiniteIO.ioQP at hh
    rwa [sub_eq_zero] at hh
  obtain ⟨hk₁, hk₂⟩ := interRecords_lengths_lt_ringChar E hhon hC
  have hmse :
      (∏ i, (Polynomial.X
          + Polynomial.C (FiniteIO.reqVals (interRecords E) (interCoins E).gamma i)))
        = ∏ j, (Polynomial.X
          + Polynomial.C (FiniteIO.respVals (interRecords E) (interCoins E).gamma j)) :=
    (SetEq.mse_ldse_general (p := ringChar K) hk₁ hk₂ _ _).mpr
      (frac_sum_eq_of_ioQP_zero _ _ hQ)
  have hms :
      (((interRecords E).requests.map (Walk.rlc (interCoins E).gamma) : List K) : Multiset K)
        = (((interRecords E).responses.map (Walk.rlc (interCoins E).gamma) : List K)
            : Multiset K) := by
    refine (IO.prodXaddC_ms_inj _ _).mp ?_
    rw [← denomP_eq_ms_prod, ← denomP_eq_ms_prod]
    exact hmse
  have hperm : (interRecords E).requests.Perm (interRecords E).responses := by
    refine perm_of_perm_map_of_injOn (Walk.rlc (interCoins E).gamma) ?_
      (Multiset.coe_eq_coe.mp hms)
    intro u hu v hv heq
    exact FiniteIO.rlc_inj_of_not_collision hγ hu hv heq
  exact perm_of_perm_map_encRecC_cp E.exec.cprimeOf hperm

/-- …and therefore discharges `MemoryRecordPremises.timestampClosed` through the existing bridge,
at exactly the same scope (which is *not* unconditional — see §D). -/
theorem timestampClosed_of_counted_events (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (hgen : InterPoleGeneric E)
    (hγ : (interCoins E).gamma ∉ FiniteIO.IORLCCollisionEvent (interRecords E))
    (hz : (interCoins E).pole ∉
      FiniteIO.IOLogDerivEvent (interRecords E) (interCoins E).gamma) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt E.cfg.challenges.α
          (E.exec.memoryRowAt i).2.2.mem.ts :=
  timestampClosed_of_paired_record_layout hhon
    (pairedRecordLayout_of_counted_events E hhon hC hgen hγ hz)

/-- The same argument with counted event (1) in its `MemoryTable.WF` form — the shape a live
fixture actually supplies. -/
theorem pairedRecordLayout_of_wf_and_counted_events (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (hwf : ∀ i : Fin E.cfg.memRows,
      MemoryTable.WF E.cfg.challenges.memoryInputs (E.exec.memoryPubAt i))
    (hγ : (interCoins E).gamma ∉ FiniteIO.IORLCCollisionEvent (interRecords E))
    (hz : (interCoins E).pole ∉
      FiniteIO.IOLogDerivEvent (interRecords E) (interCoins E).gamma) :
    RowLayout.PairedRecordLayout E.exec :=
  pairedRecordLayout_of_counted_events E hhon hC (interPoleGeneric_of_wf E hwf hC) hγ hz

/-- **The field-size obstruction is sidestepped, stated as a theorem.**  The characteristic bound
`E` already carries is exactly what `Lem:ldse_mse` consumes on these two columns. -/
theorem closure_uses_only_the_characteristic_bound (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent) :
    (interRecords E).requests.length < ringChar K
      ∧ (interRecords E).responses.length < ringChar K
      ∧ E.cfg.Ksz < ringChar K :=
  ⟨(interRecords_lengths_lt_ringChar E hhon hC).1, (interRecords_lengths_lt_ringChar E hhon hC).2,
    E.Ksz_lt_ringChar⟩

/-! ## §D. Which counted events are independent of the premise, and which is not

Events (1) and (2) here are of that kind too.  Event (3) is not: its certificate
`ioQP` is assembled from the record columns, and off (1) and (2), on `E`'s own accumulator,
excluding it is *equivalent* to the conclusion. -/

/-- If the two columns already match, the difference polynomial is identically zero: the two
compressed columns then have equal `denomP` — which *is* the `L_MSE` product of the paper —
and hence, through `Lem:ldse_mse` and `frac_sum_mul_denom`, equal `numerP`. -/
theorem ioQP_eq_zero_of_perm {records : FiniteIO.PreChallengeRecords K 9} (γ : K)
    (hk₁ : records.requests.length < ringChar K)
    (hk₂ : records.responses.length < ringChar K)
    (h : records.requests.Perm records.responses) :
    FiniteIO.ioQP records γ = 0 := by
  have hdenom : FiniteIO.denomP (FiniteIO.reqVals records γ)
      = FiniteIO.denomP (FiniteIO.respVals records γ) := by
    show FiniteIO.denomP (fun i : Fin records.requests.length => Walk.rlc γ (records.requests.get i))
      = FiniteIO.denomP
          (fun j : Fin records.responses.length => Walk.rlc γ (records.responses.get j))
    rw [denomP_eq_ms_prod, denomP_eq_ms_prod,
      Multiset.coe_eq_coe.mpr (h.map (Walk.rlc γ))]
  have hfrac : (∑ i, SetEq.frac (FiniteIO.reqVals records γ i))
      = ∑ j, SetEq.frac (FiniteIO.respVals records γ j) :=
    (SetEq.mse_ldse_general (p := ringChar K) hk₁ hk₂ _ _).mp hdenom
  have hnum : FiniteIO.numerP (FiniteIO.reqVals records γ)
      = FiniteIO.numerP (FiniteIO.respVals records γ) := by
    refine RatFunc.algebraMap_injective K ?_
    rw [← FiniteIO.frac_sum_mul_denom (FiniteIO.reqVals records γ),
      ← FiniteIO.frac_sum_mul_denom (FiniteIO.respVals records γ), hfrac, hdenom]
  show FiniteIO.numerP (FiniteIO.reqVals records γ)
        * FiniteIO.denomP (FiniteIO.respVals records γ)
      - FiniteIO.numerP (FiniteIO.respVals records γ)
        * FiniteIO.denomP (FiniteIO.reqVals records γ) = 0
  rw [hnum, hdenom, sub_self]

/-- **Counted event (3) is EMPTY when the premise holds.**  So its exclusion is satisfiable exactly
where the premise is, and it cannot be a challenge-side condition. -/
theorem interLogDerivEvent_eq_empty_of_pairedRecordLayout (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (h : RowLayout.PairedRecordLayout E.exec) (γ : K) :
    FiniteIO.IOLogDerivEvent (interRecords E) γ = ∅ := by
  classical
  obtain ⟨hk₁, hk₂⟩ := interRecords_lengths_lt_ringChar E hhon hC
  have hQ : FiniteIO.ioQP (interRecords E) γ = 0 :=
    ioQP_eq_zero_of_perm γ hk₁ hk₂ (h.map (fun r => NockVM.encRecC r (E.exec.cprimeOf r)))
  rw [FiniteIO.IOLogDerivEvent, Finset.filter_eq_empty_iff]
  intro z _
  rintro ⟨hne, -⟩
  exact hne hQ

/-- **THE FINDING.**  Off counted events (1) and (2), and on `E`'s own `intermediate` accumulator,
the exclusion of counted event (3) is **equivalent** to `PairedRecordLayout`. -/
theorem interLogDerivGood_iff_pairedRecordLayout (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (hgen : InterPoleGeneric E)
    (hγ : (interCoins E).gamma ∉ FiniteIO.IORLCCollisionEvent (interRecords E)) :
    ((interCoins E).pole ∉
        FiniteIO.IOLogDerivEvent (interRecords E) (interCoins E).gamma)
      ↔ RowLayout.PairedRecordLayout E.exec := by
  refine ⟨fun hz => pairedRecordLayout_of_counted_events E hhon hC hgen hγ hz, fun h => ?_⟩
  rw [interLogDerivEvent_eq_empty_of_pairedRecordLayout E hhon hC h]
  simp

theorem counted_event_three_is_not_weaker_than_the_premise (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (hgen : InterPoleGeneric E)
    (hγ : (interCoins E).gamma ∉ FiniteIO.IORLCCollisionEvent (interRecords E)) :
    ((interCoins E).pole ∉
        FiniteIO.IOLogDerivEvent (interRecords E) (interCoins E).gamma)
      ↔ RowLayout.PairedRecordLayout E.exec :=
  interLogDerivGood_iff_pairedRecordLayout E hhon hC hgen hγ

theorem event_membership_predicates_differ_in_kind
    (E : BuildableNockExecution F K) (α z γ : K) :
    (α ∈ (ForestExponentOrderClosure.zeroTimestampChallengeEvent : Finset K) ↔ α = 0)
      ∧ (z ∈ FiniteIO.IOLogDerivEvent (interRecords E) γ
          ↔ (FiniteIO.ioQP (interRecords E) γ ≠ 0
              ∧ (FiniteIO.ioQP (interRecords E) γ).eval z = 0)) := by
  classical
  refine ⟨ForestExponentOrderClosure.mem_zeroTimestampChallengeEvent_iff α, ?_⟩
  simp only [FiniteIO.IOLogDerivEvent, Finset.mem_filter, Finset.mem_univ, true_and]

/-! ## §E. Where the analogy with the external IO columns breaks -/

/-- **The break point.**  Left: what `E` carries for the *external* IO columns — the record-level
`IO.LIO`, derived from `SemanticIOPreimage`'s `derivedIO_lmio` plus `E.requestNodup`, with no
counted event anywhere in the derivation.  Right: what `E` carries for the *`intermediate`* column
— `IO.LmIO` of the **timestamp** lists, not of records.  The counted-event layer is not the
difference; the semantic layer is. -/
theorem external_matching_is_semantic_intermediate_is_not (E : BuildableNockExecution F K) :
    IO.LIO E.cfg.Ksz E.exec.derivedRequestIO E.exec.derivedResponseIO
      ∧ IO.LmIO E.cfg.Ksz (forestReadTimestamps E.cfg E.execA)
          (forestVerifyTimestamps E.cfg E.execA) :=
  ⟨execution_lio_of_requestNodup E, execution_structural_intermediate_matching E⟩

/-- …and the external columns' three counted-event exclusions are **named `Inputs` fields**.

It no longer does: `TraceGen.inputsOfCarrier` (`GenCarrierInputs.lean:157`) now *derives* all three
exclusions for an arbitrary carrier from the single arithmetic side condition
`ioFailureUnionBound 8 n n (Fintype.card K) < Fintype.card (K × K)`, via
`exists_ioCoins_of_length_bound` (`:103`).  **The theorem itself is
unaffected and still true** — the fields are still fields; only the tier claim about them has
changed. -/
theorem external_counted_events_are_named_inputs
    {E : BuildableNockExecution F K} (I : BuildableChips.Inputs E) :
    I.ioCoins.pole ∉
        FiniteIO.IOPoleHitEvent (BuildableChips.executionRecords E) I.ioCoins.gamma
      ∧ I.ioCoins.gamma ∉
          FiniteIO.IORLCCollisionEvent (BuildableChips.executionRecords E)
      ∧ I.ioCoins.pole ∉
          FiniteIO.IOLogDerivEvent (BuildableChips.executionRecords E) I.ioCoins.gamma :=
  ⟨I.ioPoleHitGood, I.ioGammaGood, I.ioLogDerivGood⟩

/-- The tree↔row upgrade of the
timestamp-level object is still equivalent to the premise's own consequence on the remove column,
so it is still not a route to the premise. -/
theorem route_two_still_circular (E : BuildableNockExecution F K) :
    PairedRecordIOResult.VerifyReindexingRecovery E ↔
      ∀ r ∈ RowLayout.consumedRecordList E.exec,
        TimestampClosedAt E.cfg.challenges.α r.ts :=
  PairedRecordIOResult.verifyReindexingRecovery_iff_consumed_closed E

/-! ## §F. Cardinalities, and the accounting

**These are `Finset` cardinalities, not probabilities.**  No distribution appears in this module and
no probabilistic statement is compiled here or consumed from here. -/

/-- Counted event (1)'s bound: at most one bad `β` per occurring record. -/
theorem interPoleHitEvent_card_le (E : BuildableNockExecution F K) :
    (FiniteIO.IOPoleHitEvent (interRecords E) (interCoins E).gamma).card
      ≤ (RowLayout.consumedRecordList E.exec).length
          + (RowLayout.addedRecordList E.exec).length := by
  have h := FiniteIO.IOPoleHitEvent_card_le (interRecords E) (interCoins E).gamma
  simpa [interRecords] using h

/-- Counted event (2)'s bound at `m = 8`: the union bound over ordered index pairs of the
single-pair Schwartz–Zippel count `≤ 7`. -/
theorem interRLCCollisionEvent_card_le (E : BuildableNockExecution F K) :
    (FiniteIO.IORLCCollisionEvent (interRecords E)).card
      ≤ ((RowLayout.consumedRecordList E.exec).length
            + (RowLayout.addedRecordList E.exec).length)
          * ((RowLayout.consumedRecordList E.exec).length
            + (RowLayout.addedRecordList E.exec).length) * 8 := by
  have h := FiniteIO.IORLCCollisionEvent_card_le (interRecords E)
  simpa [interRecords] using h

/-- Counted event (3)'s bound: univariate Schwartz–Zippel on the `ioQP` certificate. -/
theorem interLogDerivEvent_card_le (E : BuildableNockExecution F K) (γ : K) :
    (FiniteIO.IOLogDerivEvent (interRecords E) γ).card
      ≤ (RowLayout.consumedRecordList E.exec).length
          + (RowLayout.addedRecordList E.exec).length := by
  have h := FiniteIO.IOLogDerivEvent_card_le (interRecords E) γ
  simpa [interRecords] using h

/-! ## §G. The counted-event hypotheses are NOT available at the live F97 multi-root execution

A counted-event hypothesis is only worth stating if some live execution satisfies it (the J.0.3
discipline).  At the two-serviced-root F97 execution it does not, and the reason is structural
rather than accidental: the fixture samples the memory-table compression challenge at `γ = 0`, where
`RLC^γ` collapses onto the `mem.root.size` coordinate alone and stops separating records.  Two of
its three served records then share their compressed value — both memory poles are `1`
(`MultiRootServedFixture.pole_servedRecord`, `pole_servedFormulaRecord`) — so counted event (2) is
**hit** (`multiRoot_gamma_in_collision_event`).

So `pairedRecordLayout_of_counted_events` has **no witness at `multiRootExecution`**, and none is
constructed here.

Scope of this subsection, exactly: the negative below is compiled for `multiRootExecution` only.

Both are now settled,
and the first conclusion is **withdrawn**:

* the F73 `concreteExecution` satisfies **all three** exclusions
  (`Batch135.ConcreteF73.concrete_all_three_exclusions_hold`) — its two `intermediate` record columns
  are the *same singleton*, so event (2) has no unequal pair to collide and event (3) is empty,
  while event (1) is the fixture's own `MemoryTable.WF`.  So §C is compiled **and exercised**
  (`concrete_counted_event_route_is_exercised`), a genuine J.0.3 exercise;
* the F97 `distinctCensusExecution` **hits** event (2) for the same reason `multiRootExecution` does
  — `γ = 0` and `leftFormula`/`rightFormula` have equal leaf counts
  (`Batch135.DistinctCensusF97.distinctCensus_gamma_in_collision_event`).

The witness **confirms** the §D relocation verdict rather than overturning it: every witness of the
three exclusions already satisfies the premise
(`Batch135.redteam_any_witness_already_satisfies_the_premise`), and at F73 the premise is already
free — the two columns are literally equal — so nothing is extracted from the route
(`Batch135.ConcreteF73.concrete_pairedRecordLayout_without_counted_events`,
`concrete_witness_extracts_nothing`).

Nothing here is a claim about the paper: the paper samples `β, γ` at random, and the fixtures
pin them to `0` for arithmetic convenience. -/

namespace MultiRoot

open MultiRootServedFixture
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete

local instance prime97ao114 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97ao114 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-- The live fixture's memory compression challenge is `0`, and so is its pole offset `β`. -/
theorem multiRoot_interCoins :
    (interCoins multiRootExecution).gamma = (0 : K97cubic)
      ∧ (interCoins multiRootExecution).pole = (0 : K97cubic) :=
  ⟨rfl, neg_zero⟩

theorem multiRoot_responses :
    (interRecords multiRootExecution).responses
      = [NockVM.encRecFormR parentRecordS MemoryTable.formRDefault,
          NockVM.encRecFormR servedRecord MemoryTable.formRDefault,
          NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault] := by
  change (RowLayout.addedRecordList execS).map (fun r => NockVM.encRecC r (execS.cprimeOf r)) = _
  rw [← RowLayout.rawResponses_eq_addedRecordList execS honestVerS,
    ← ExactExecution.derivedResponseIO_eq_map_encRecC execS execS_cprimeCoherent]
  exact derived_responsesS

/-- At `γ = 0` the record RLC is the `mem.root.size` coordinate alone, and the fixture's two
distinct served records `servedRecord` / `servedFormulaRecord` share it (both poles are `1`). -/
theorem multiRoot_records_collide_at_gamma_zero :
    Walk.rlc (interCoins multiRootExecution).gamma
        (NockVM.encRecFormR servedRecord MemoryTable.formRDefault)
      = Walk.rlc (interCoins multiRootExecution).gamma
          (NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault) := by
  have hγeq : memInputsS.γ = (interCoins multiRootExecution).gamma := rfl
  have hpole :
      MemoryTable.recRLC memInputsS.γ (NockVM.formRRow servedRecord MemoryTable.formRDefault)
          (NockVM.formRCprime servedRecord MemoryTable.formRDefault) - memInputsS.β
      = MemoryTable.recRLC memInputsS.γ
          (NockVM.formRRow servedFormulaRecord MemoryTable.formRDefault)
          (NockVM.formRCprime servedFormulaRecord MemoryTable.formRDefault) - memInputsS.β := by
    change MemoryTable.pole memInputsS (NockVM.formRRow servedRecord MemoryTable.formRDefault)
        (NockVM.formRCprime servedRecord MemoryTable.formRDefault)
      = MemoryTable.pole memInputsS (NockVM.formRRow servedFormulaRecord MemoryTable.formRDefault)
        (NockVM.formRCprime servedFormulaRecord MemoryTable.formRDefault)
    rw [pole_rowS, pole_rowS, pole_servedRecord, pole_servedFormulaRecord]
  rw [← NockVM.encRecC_formRRow, ← NockVM.encRecC_formRRow, rlc_encRecC, rlc_encRecC, ← hγeq]
  linear_combination hpole

/-- **Counted event (2) is HIT at the live F97 multi-root execution.**  So `interRecords` /
`interCoins` have no J.0.3 non-vacuity witness **at `multiRootExecution`**.

That is **false and is
withdrawn**: the F73 `concreteExecution` satisfies all three
(`Batch135.ConcreteF73.concrete_all_three_exclusions_hold`) — its two `intermediate` record columns
are the *same singleton*, so event (2) has no unequal pair and event (3) is empty, while event (1)
is the fixture's own `MemoryTable.WF`.  The negative here is scoped to `multiRootExecution`; the F97
`distinctCensusExecution` also hits event (2)
(`Batch135.DistinctCensusF97.distinctCensus_gamma_in_collision_event`).  The **relocation verdict is
unaffected**: by §D's equivalence every such witness already satisfies the premise, and at F73 the
premise is available with no counted event at all
(`Batch135.ConcreteF73.concrete_pairedRecordLayout_without_counted_events`), so the exercise
extracts nothing. -/
theorem multiRoot_gamma_in_collision_event :
    (interCoins multiRootExecution).gamma
      ∈ FiniteIO.IORLCCollisionEvent (interRecords multiRootExecution) := by
  classical
  have hmem : ∀ v ∈ (interRecords multiRootExecution).responses,
      v ∈ (interRecords multiRootExecution).requests
        ++ (interRecords multiRootExecution).responses :=
    fun v hv => List.mem_append_right _ hv
  have h1 : NockVM.encRecFormR servedRecord MemoryTable.formRDefault
      ∈ (interRecords multiRootExecution).responses := by
    rw [multiRoot_responses]; simp
  have h2 : NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault
      ∈ (interRecords multiRootExecution).responses := by
    rw [multiRoot_responses]; simp
  have hne : NockVM.encRecFormR servedRecord MemoryTable.formRDefault
      ≠ NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault := by
    intro he
    have hts : servedRecord.ts = servedFormulaRecord.ts := by
      have h7 := congrFun he (7 : Fin 9)
      rw [← NockVM.encRecC_formRRow, ← NockVM.encRecC_formRRow] at h7
      simpa [NockVM.encRecC, NockVM.formRRow] using h7
    rw [ts_servedRecord, ts_servedFormulaRecord] at hts
    exact ts_16_ne_64 hts.symm
  simp only [FiniteIO.IORLCCollisionEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨_, hmem _ h1, _, hmem _ h2, hne, multiRoot_records_collide_at_gamma_zero⟩

/-- Restated as the scope fact it is: the §C hypotheses are not jointly satisfied at this
execution. -/
theorem multiRoot_counted_event_hypotheses_not_available :
    ¬ ((interCoins multiRootExecution).gamma
        ∉ FiniteIO.IORLCCollisionEvent (interRecords multiRootExecution)) :=
  fun h => h multiRoot_gamma_in_collision_event

end MultiRoot

/-! ## §H. Accounting — nothing added, nothing ticked -/

/-- The fourteen-field execution carrier is unchanged: no counted-event field was added. -/
theorem execution_eta_still_fourteen_fields_ao114 (E : BuildableNockExecution F K) :
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

/-- `BuildableChips.Inputs` is unchanged: no `intermediate`-side coin or flag was added. -/
theorem inputs_eta_unchanged_ao114 {E : BuildableNockExecution F K}
    (I : BuildableChips.Inputs E) :
    I =
      { stateTagChar := I.stateTagChar
        computeWalkAlpha := I.computeWalkAlpha
        memoryWalkAlpha := I.memoryWalkAlpha
        walkGamma := I.walkGamma
        hOrb := I.hOrb
        basis := I.basis
        orbit := I.orbit
        activeDomains := I.activeDomains
        ioCoins := I.ioCoins
        ioPoleHitGood := I.ioPoleHitGood
        ioGammaGood := I.ioGammaGood
        ioLogDerivGood := I.ioLogDerivGood
        computeChallenges := I.computeChallenges
        memoryScalarChallenge := I.memoryScalarChallenge
        memoryExtensionFold := I.memoryExtensionFold
        interPoleHitGood := I.interPoleHitGood
        honestVer := I.honestVer
        ioGood10 := I.ioGood10
        interPoleHitGood10 := I.interPoleHitGood10 } := by
  cases I
  rfl

/-- `MemoryRecordPremises` still has its two fields and `timestampClosed` is still named: this
module inhabits nothing. -/
theorem memoryRecordPremises_still_two_ao114
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
      (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) :=
  GenericHonestData.memoryRecordPremises_still_two_after_logup_inventory M

/-- The `11+1+2` partition of the released capstone statement is unchanged. -/
theorem exact_eleven_one_two_ao114 : 11 + 1 + 2 = 14 :=
  GenericHonestPackage.residual_pair_still_eleven_one_two_after_logup_inventory

/-- The consumed capstone and its paper alias are untouched. -/
theorem consumed_capstone_untouched_ao114
    [Fintype F] [DecidableEq F]
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement P :=
  OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth


#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.perm_of_perm_map_of_injOn
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.prod_map_eq_prod_fin
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.rlc_encRec
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.compress_interCoins
#print axioms
  Nock.NockVMROM.Thm54.PairedRecordCountedEvent.interCoins_is_the_table_pole_not_the_io_sample
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.interCompress_ne_zero
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.interEndpoint_sum_eq
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.exists_live_pub_of_mem_added
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.exists_live_pub_of_mem_consumed
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.exists_index_of_mem_memoryPubRows
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.interPoleGeneric_of_wf
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.interPoleGeneric_of_not_poleHit
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.interRecords_lengths_lt_ringChar
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.denomP_eq_ms_prod
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.interQP_eval_eq_zero
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.frac_sum_eq_of_ioQP_zero
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.pairedRecordLayout_of_counted_events
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.timestampClosed_of_counted_events
#print axioms
  Nock.NockVMROM.Thm54.PairedRecordCountedEvent.pairedRecordLayout_of_wf_and_counted_events
#print axioms
  Nock.NockVMROM.Thm54.PairedRecordCountedEvent.closure_uses_only_the_characteristic_bound
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.ioQP_eq_zero_of_perm
#print axioms
  Nock.NockVMROM.Thm54.PairedRecordCountedEvent.interLogDerivEvent_eq_empty_of_pairedRecordLayout
#print axioms
  Nock.NockVMROM.Thm54.PairedRecordCountedEvent.interLogDerivGood_iff_pairedRecordLayout
#print axioms
  Nock.NockVMROM.Thm54.PairedRecordCountedEvent.counted_event_three_is_not_weaker_than_the_premise
#print axioms
  Nock.NockVMROM.Thm54.PairedRecordCountedEvent.event_membership_predicates_differ_in_kind
#print axioms
  Nock.NockVMROM.Thm54.PairedRecordCountedEvent.external_matching_is_semantic_intermediate_is_not
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.external_counted_events_are_named_inputs
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.route_two_still_circular
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.interPoleHitEvent_card_le
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.interRLCCollisionEvent_card_le
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.interLogDerivEvent_card_le
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.MultiRoot.multiRoot_interCoins
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.MultiRoot.multiRoot_responses
#print axioms
  Nock.NockVMROM.Thm54.PairedRecordCountedEvent.MultiRoot.multiRoot_records_collide_at_gamma_zero
#print axioms
  Nock.NockVMROM.Thm54.PairedRecordCountedEvent.MultiRoot.multiRoot_gamma_in_collision_event
#print axioms
  Nock.NockVMROM.Thm54.PairedRecordCountedEvent.MultiRoot.multiRoot_counted_event_hypotheses_not_available
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.execution_eta_still_fourteen_fields_ao114
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.inputs_eta_unchanged_ao114
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.memoryRecordPremises_still_two_ao114
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.exact_eleven_one_two_ao114
#print axioms Nock.NockVMROM.Thm54.PairedRecordCountedEvent.consumed_capstone_untouched_ao114

end

end Nock.NockVMROM.Thm54.PairedRecordCountedEvent
