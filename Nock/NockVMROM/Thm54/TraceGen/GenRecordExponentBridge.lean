/-
  Nock/NockVMROM/Thm54/TraceGen/GenRecordExponentBridge.lean

  This module proves it.

  ## The pairing, by exponent

  the paper: the memory timestamp "is unique and represents the line number of the compute
  table at which the memory record was requested, thus having the closed form `z^i ∈ 𝕂`, where `i`
  is the compute table line number".  The honest fill reads that line number as a *position*
  (`RecordCarrier.honestExp`: the record's `1`-based index in the derived request list); the
  template carries it as a *Nat* (`MemoryTimestampRow.recordExponent`).  The bridge has three steps.

  * **§A — compute side, α-free + specialization.**  For every record `x` of the derived request
    list, its position is the committed template exponent of the request it encodes, and its
    timestamp slot (`7`) is `α` to that exponent (`request_honestExp_eq_recordExponent`).  The
    position is `Σ_{k' < k} arity(k') + j + 1` (`RecordCarrier.honestExp_flatMap`); the arities are
    the template's `recordCount`s through `ComputeTimestampSpecializesAt` (row state = stamp state,
    i.e. the template topology); the template's prefix sum is its `lnPrevExponent`
    (`template_lnPrev_eq_prefix`: `computeStartsAtZero` / `computeLineChain` /
    `computeLineAdvance`); and `computeRecordOffsets` makes the record exponent `lnPrev + j + 1`.
    The timestamp is `compute_ts_eq_pow_of_origin` (honest origin `ln_prev = α^{lnPrev}`).
  * **§B — memory side.**  A live (`read_root` / `verify_child`) memory row's record has timestamp
    `α^{recordExponent}` (`MemoryTimestampSpecializesAt`).  If that record is one of the derived
    requests, both exponents are `≤ L` (`L = totalRecordCount`, the paper's line count), and
    `L < orderOf α` (the paper, `N, L ∈ negl(𝕂)`), then `α^e = α^{pos}` forces `e = pos`:
    `reqIdxNat_eq_recordExponent_of_mem`.  The membership is the honest response/request pairing:
    for `read_root` rows it is `L_IO` itself (`SampledIOSameExecutionAssignment.lio`, with `ver =
    (st = read_root)`), `reqIdxNat_eq_recordExponent_readRoot`; for `verify_child` rows it is the
    paired `intermediate` layout plus `CprimeCoherent`, `reqIdxNat_eq_recordExponent_live`.
  * **§C — the generated execution.**  Every premise of §B is discharged by the generator for
    any accepted program (`genComputeSkeleton … =.ok (t, result)`) at the generated timestamp
    skeleton `genTimestampSkeleton`: the timestamp equations (`genComputeTimestamps`,
    `genMemoryTimestamps`), the origins (`genComputeOrigins`), the memory window
    (`genMemForestFromTree_stamp_exp_le_totalRecordCount`), the layout and coherence
    (`genExactExecution_pairedRecordLayout`, `genExactExecution_cprimeCoherent`).  The one window
    premise `accAt … < orderOf α` is the generator's own (`genExactExecution_cprimeCoherent`'s
    `horbα`; `nockCompiles`'s `hwin : accAt … + 3 < B ≤ orderOf α` implies it):
    `generated_reqIdxNat_eq_recordExponent`.

  ## Scope

  * The window `L < orderOf α` is used, and it is needed **in this form**: `reqIdx` is a position
    (α-free value) while the template exponent reaches the row only through `α^e`.  At an `α` of
    small order two distinct line numbers collide in the timestamp slot and the record matched by
    `L_IO` need not determine the exponent.  The generator's own side condition supplies it.
  * `R` is related to the generated execution by its **row lists** (`hcr`, `hmr`), which is what
    `reqIdxNat`, `derivedRequestIO`, `PairedRecordLayout` and `CprimeCoherent` read.  The production
    family built from `genBuildableOfProgram` has those lists by `change`
    (`genBuildableOfProgram_pairedRecordLayout`).
-/
import Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization
import Nock.NockVMROM.Thm54.ForestExponentWindow
import Nock.NockVMROM.Thm54.TraceGen.GenExponentLineNumbers
import Nock.NockVMROM.Thm54.TraceGen.GenChainedLanguage
import Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLayout

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen.GenRecordExponentBridge

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.ForestExponentWindow
open Nock.NockVMROM.Thm54.RowLayout
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization
open Nock.Framework.Thm54

/-! ## §A. Compute side: the position of a derived request is its template exponent -/

section ComputeSide

variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq K]

/-- The active request prefix of a row has the state's record count. -/
theorem activeRequestRecords_length (pub : ComputeTable.Pub K) :
    (NockVM.activeRequestRecords pub).length = Nock.Framework.recordCount pub.state := by
  cases h : pub.state <;> simp [NockVM.activeRequestRecords, h, Nock.Framework.recordCount]

/-- The `j`-th active request record is the `j`-th public memory-record slot. -/
theorem activeRequestRecords_getElem (pub : ComputeTable.Pub K) (j : ℕ)
    (hj : j < (NockVM.activeRequestRecords pub).length) :
    ∃ hj3 : j < 3, (NockVM.activeRequestRecords pub)[j] = computeMemRec pub ⟨j, hj3⟩ := by
  have hlen := activeRequestRecords_length pub
  have hle : Nock.Framework.recordCount pub.state ≤ 3 := by
    cases pub.state <;> simp [Nock.Framework.recordCount]
  have hj3 : j < 3 := by omega
  refine ⟨hj3, ?_⟩
  clear hlen hle
  revert hj
  unfold NockVM.activeRequestRecords
  cases pub.state <;> intro hj <;> (simp only [List.length_cons, List.length_nil] at hj) <;>
    (interval_cases j <;> rfl)

/-- Along a line-exponent chain the line exponent of row `k` is the head's plus the prefix sum of
`recordCount` (the production copy of `Batch671.lnPrev_prefix_of_chain`). -/
theorem lnPrev_prefix_of_chain :
    ∀ (L : List ComputeTimestampRow), ComputeLineExponentChain L →
      (∀ s ∈ L, s.lnExponent = s.lnPrevExponent + Nock.Framework.recordCount s.state) →
      ∀ (k : ℕ) (hk : k < L.length) (h0 : 0 < L.length),
        (L[k]'hk).lnPrevExponent =
          (L[0]'h0).lnPrevExponent +
            ((L.take k).map fun s => Nock.Framework.recordCount s.state).sum
  | [], _, _, k, hk, _ => absurd hk (by simp)
  | [a], _, _, k, hk, _ => by
      have : k = 0 := by simpa using hk
      subst this; simp
  | a :: b :: rest, hchain, hadv, k, hk, h0 => by
      cases k with
      | zero => simp
      | succ k =>
          have hk' : k < (b :: rest).length := by simpa using hk
          have ih := lnPrev_prefix_of_chain (b :: rest) hchain.2
            (fun s hs => hadv s (List.mem_cons_of_mem _ hs)) k hk' (by simp)
          have hab : a.lnExponent = b.lnPrevExponent := hchain.1
          have ha := hadv a (by simp)
          simp only [List.getElem_cons_succ, List.getElem_cons_zero] at ih ⊢
          rw [ih, ← hab, ha]
          simp [List.take_succ_cons, List.map_cons, List.sum_cons]
          ring

/-- **The template's line exponent is the prefix sum of the template arities** (α-free). -/
theorem template_lnPrev_eq_prefix {base : SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base) (k : ℕ) (hk : k < S.computeRows.length) :
    (S.computeRows[k]'hk).lnPrevExponent =
      ((S.computeRows.take k).map fun s => Nock.Framework.recordCount s.state).sum := by
  have h0 : 0 < S.computeRows.length := by omega
  rw [lnPrev_prefix_of_chain S.computeRows S.computeLineChain S.computeLineAdvance k hk h0]
  have hz : (S.computeRows[0]'h0).lnPrevExponent = 0 := by
    have hs := S.computeStartsAtZero
    revert h0 hs
    cases S.computeRows with
    | nil => intro h0; simp at h0
    | cons r rest => intro _ hs; exact hs
  rw [hz, zero_add]

/-- The encoded request's timestamp slot is the record's timestamp. -/
theorem encRecFormR_seven (r : ComputeTable.MemRec K) (lmb : K) :
    NockVM.encRecFormR r lmb 7 = r.ts := rfl

/-- The memory row's encoded record carries its timestamp in slot `7`. -/
theorem encRecC_seven (r : ComputeTable.MemRec K) (c : K) : NockVM.encRecC r c 7 = r.ts := rfl

/-- Sums of a row statistic agree along a `Forall₂` that identifies it pointwise. -/
theorem sum_map_eq_of_forall₂ {A B : Type} {f : A → ℕ} {g : B → ℕ} :
    ∀ {l₁ : List A} {l₂ : List B}, List.Forall₂ (fun a b => f a = g b) l₁ l₂ →
      (l₁.map f).sum = (l₂.map g).sum := by
  intro l₁ l₂ h
  induction h with
  | nil => rfl
  | cons hab _ ih => simp [hab, ih]

/-- **§A, the compute-side identification.**  On rows that specialize the template `S` at `α`
with honest origin, every record `x` of the (duplicate-free) derived request list sits at the
position of a committed template record exponent, and its timestamp slot is `α` to that
exponent. -/
theorem request_honestExp_eq_recordExponent {base : SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base) {α lmb : K}
    {rows : List (ComputeTable.State × ComputeTable.DTcomp K)}
    (hts : List.Forall₂ (ComputeTimestampSpecializesAt α) S.computeRows rows)
    (hor : List.Forall₂ (fun stamp row => row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
      S.computeRows rows)
    (hnd : (rows.flatMap fun row =>
      (NockVM.activeRequestRecords row.2.2.1).map fun r => NockVM.encRecFormR r lmb).Nodup)
    {x : Fin 9 → K}
    (hx : x ∈ rows.flatMap fun row =>
      (NockVM.activeRequestRecords row.2.2.1).map fun r => NockVM.encRecFormR r lmb) :
    ∃ stamp ∈ S.computeRows, ∃ i : Fin 3,
      (i : ℕ) < Nock.Framework.recordCount stamp.state ∧
      RecordCarrier.honestExp (rows.flatMap fun row =>
        (NockVM.activeRequestRecords row.2.2.1).map fun r => NockVM.encRecFormR r lmb) x =
          stamp.recordExponent i ∧
      x 7 = α ^ stamp.recordExponent i := by
  set f : ComputeTable.State × ComputeTable.DTcomp K → List (Fin 9 → K) :=
    fun row => (NockVM.activeRequestRecords row.2.2.1).map fun r => NockVM.encRecFormR r lmb
    with hf
  obtain ⟨row, hrow, hxrow⟩ := List.mem_flatMap.mp hx
  obtain ⟨k, hk, hkrow⟩ := List.getElem_of_mem hrow
  subst hkrow
  obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hxrow
  subst hjx
  have hlen : S.computeRows.length = rows.length := hts.length_eq
  have hkS : k < S.computeRows.length := by omega
  have hspec : ComputeTimestampSpecializesAt α (S.computeRows[k]'hkS) (rows[k]'hk) := by
    have := (List.forall₂_iff_get.mp hts).2 k hkS hk
    simpa using this
  have hori : (rows[k]'hk).2.2.1.ln_prev = α ^ (S.computeRows[k]'hkS).lnPrevExponent := by
    have := (List.forall₂_iff_get.mp hor).2 k hkS hk
    simpa using this
  have hstate : (rows[k]'hk).2.2.1.state = (S.computeRows[k]'hkS).state := hspec.2.2.1
  have hj' : j < (NockVM.activeRequestRecords (rows[k]'hk).2.2.1).length := by
    simpa [hf] using hj
  obtain ⟨hj3, hget⟩ := activeRequestRecords_getElem _ j hj'
  have hjrc : j < Nock.Framework.recordCount (S.computeRows[k]'hkS).state := by
    rw [← hstate, ← activeRequestRecords_length]; exact hj'
  have hmemS : S.computeRows[k]'hkS ∈ S.computeRows := List.getElem_mem hkS
  refine ⟨S.computeRows[k]'hkS, hmemS, ⟨j, hj3⟩, hjrc, ?_, ?_⟩
  · -- the position
    rw [RecordCarrier.honestExp_flatMap rows f hnd k hk j hj]
    have htake : List.Forall₂
        (fun s r => Nock.Framework.recordCount s.state = (f r).length)
        (S.computeRows.take k) (rows.take k) := by
      refine List.forall₂_take k ?_
      refine hts.imp ?_
      intro s r hrs
      rw [hf, List.length_map, activeRequestRecords_length, hrs.2.2.1]
    rw [← sum_map_eq_of_forall₂ htake, ← template_lnPrev_eq_prefix S k hkS,
      S.computeRecordOffsets _ hmemS ⟨j, hj3⟩ hjrc]
  · -- the timestamp slot
    have hel : (f (rows[k]'hk))[j]'hj =
        NockVM.encRecFormR ((NockVM.activeRequestRecords (rows[k]'hk).2.2.1)[j]'hj') lmb := by
      simp [hf]
    rw [hel, encRecFormR_seven, hget]
    have hge : (S.computeRows[k]'hkS).lnPrevExponent ≤
        (S.computeRows[k]'hkS).recordExponent ⟨j, hj3⟩ := by
      rw [S.computeRecordOffsets _ hmemS ⟨j, hj3⟩ hjrc]; omega
    have hactive : computeMemRecKind (S.computeRows[k]'hkS).state ⟨j, hj3⟩ = .active := by
      simp [computeMemRecKind, hjrc]
    exact compute_ts_eq_pow_of_origin hspec hori ⟨j, hj3⟩ hge hactive

end ComputeSide

/-! ## §B. Memory side: `reqIdx = recordExponent` on every live row whose record is requested -/

section MemorySide

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-- Two exponents inside the injective power window of `α` are equal when their powers are. -/
theorem eq_of_pow_eq_of_lt_orderOf {α : K} {a b : ℕ} (ha : a < orderOf α) (hb : b < orderOf α)
    (h : α ^ a = α ^ b) : a = b := by
  have hfin : IsOfFinOrder α := orderOf_pos_iff.mp (by omega)
  have := (hfin.pow_inj_mod).mp h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- The indexed memory row is the `i`-th entry of the BFS row list. -/
theorem memoryPubAt_eq_getElem (R : PlusIOSegmentedFamily F K) (i : Fin R.problem.cfg.memRows)
    (hi : (i : ℕ) < R.problem.exec.memoryRows.length) :
    R.problem.exec.memoryPubAt i = (R.problem.exec.memoryRows[(i : ℕ)]'hi).2.2 := by
  simp [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, List.get_eq_getElem]

/-- **§B, the core bridge.**  Let the generated rows specialize an α-free timestamp template `S`
at `α` (compute and memory timestamp equations, honest origin), with the line count inside the
power window (`L < orderOf α`) and every memory stamp a line number (`≤ L`).  Then on every live
memory row whose record is one of the derived requests, the honest carrier is the committed
template exponent. -/
theorem reqIdxNat_eq_recordExponent_of_mem (A : SampledIOSameExecutionAssignment R p)
    {base : SemanticSkeleton} (S : SemanticTimestampSkeleton F K base) {α : K}
    (hts : List.Forall₂ (ComputeTimestampSpecializesAt α) S.computeRows
      R.problem.exec.computeRows)
    (hor : List.Forall₂ (fun stamp row => row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
      S.computeRows R.problem.exec.computeRows)
    (hmts : List.Forall₂ (MemoryTimestampSpecializesAt α) S.memoryRows
      R.problem.exec.memoryRows)
    (hwin : totalRecordCount S.computeRows < orderOf α)
    (hmemle : ∀ stamp ∈ S.memoryRows, stamp.recordExponent ≤ totalRecordCount S.computeRows)
    (i : Fin R.problem.cfg.memRows) (hi : (i : ℕ) < S.memoryRows.length)
    (hlive : (R.problem.exec.memoryPubAt i).st = .read_root ∨
      (R.problem.exec.memoryPubAt i).st = .verify_child)
    (hreq : NockVM.encRecC (R.problem.exec.memoryPubAt i).mem
        (R.problem.exec.memoryPubAt i).cprime ∈ R.problem.exec.derivedRequestIO) :
    reqIdxNat R (R.problem.exec.memoryPubAt i) = (S.memoryRows[(i : ℕ)]'hi).recordExponent := by
  have hL : R.problem.exec.derivedRequestIO =
      R.problem.exec.computeRows.flatMap fun row =>
        (NockVM.activeRequestRecords row.2.2.1).map
          fun r => NockVM.encRecFormR r R.problem.cfg.challenges.lam := by
    rw [ExactExecution.derivedRequestIO_eq_computeRows, List.map_flatMap]
  have hnd : (R.problem.exec.computeRows.flatMap fun row =>
      (NockVM.activeRequestRecords row.2.2.1).map
        fun r => NockVM.encRecFormR r R.problem.cfg.challenges.lam).Nodup := by
    rw [← hL, ← A.requests_eq]; exact A.sampled.uniqueRequest
  set x := NockVM.encRecC (R.problem.exec.memoryPubAt i).mem
    (R.problem.exec.memoryPubAt i).cprime with hx
  rw [hL] at hreq
  obtain ⟨stamp, hstamp, j, hj, hpos, hts7⟩ :=
    request_honestExp_eq_recordExponent S hts hor hnd hreq
  -- memory timestamp
  have hiR : (i : ℕ) < R.problem.exec.memoryRows.length := by
    rw [← hmts.length_eq]; exact hi
  have hmspec : MemoryTimestampSpecializesAt α (S.memoryRows[(i : ℕ)]'hi)
      (R.problem.exec.memoryRows[(i : ℕ)]'hiR) := by
    have := (List.forall₂_iff_get.mp hmts).2 i hi hiR
    simpa using this
  have hpub := memoryPubAt_eq_getElem R i hiR
  have hactive : memoryMemRecKind (S.memoryRows[(i : ℕ)]'hi).state = .active := by
    rw [← hmspec.2.1, ← hpub]
    rcases hlive with h | h <;> rw [h] <;> rfl
  have hmts7 : x 7 = α ^ (S.memoryRows[(i : ℕ)]'hi).recordExponent := by
    rw [hx, encRecC_seven, hpub, hmspec.2.2.1, if_pos hactive]
  -- the window
  have hlenL : (R.problem.exec.computeRows.flatMap fun row =>
      (NockVM.activeRequestRecords row.2.2.1).map
        fun r => NockVM.encRecFormR r R.problem.cfg.challenges.lam).length =
        totalRecordCount S.computeRows := by
    rw [List.length_flatMap, totalRecordCount]
    refine (sum_map_eq_of_forall₂ (hts.imp ?_)).symm
    intro s r hrs
    rw [List.length_map, activeRequestRecords_length, hrs.2.2.1]
  have hposle : RecordCarrier.honestExp (R.problem.exec.computeRows.flatMap fun row =>
      (NockVM.activeRequestRecords row.2.2.1).map
        fun r => NockVM.encRecFormR r R.problem.cfg.challenges.lam) x ≤
        totalRecordCount S.computeRows := by
    rw [← hlenL, RecordCarrier.honestExp]
    have := List.idxOf_lt_length_of_mem hreq
    omega
  have hlt1 : stamp.recordExponent j < orderOf α := by
    rw [← hpos]; exact lt_of_le_of_lt hposle hwin
  have hlt2 : (S.memoryRows[(i : ℕ)]'hi).recordExponent < orderOf α :=
    lt_of_le_of_lt (hmemle _ (List.getElem_mem hi)) hwin
  have heq := eq_of_pow_eq_of_lt_orderOf hlt2 hlt1 (hmts7.symm.trans hts7)
  -- conclude
  have hreqIdx : reqIdxNat R (R.problem.exec.memoryPubAt i) =
      RecordCarrier.honestExp R.problem.exec.derivedRequestIO x := by
    simp only [reqIdxNat, if_pos hlive, hx]
  rw [hreqIdx, hL, hpos, heq]

/-- A `read_root` row's record is one of the derived requests: `ver = (st = read_root)` puts it in
the response list, and `L_IO` makes the responses a permutation of the
requests. -/
theorem readRoot_mem_derivedRequestIO (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows)
    (hst : (R.problem.exec.memoryPubAt i).st = .read_root) :
    NockVM.encRecC (R.problem.exec.memoryPubAt i).mem (R.problem.exec.memoryPubAt i).cprime ∈
      R.problem.exec.derivedRequestIO := by
  have hrow := R.problem.exec.memoryRowAt_mem i
  have hver : (R.problem.exec.memoryRowAt i).2.2.ver = true := by
    rw [A.honestVer _ hrow]
    simpa [ExactExecution.memoryPubAt] using hst
  have hresp : NockVM.encRecC (R.problem.exec.memoryPubAt i).mem
      (R.problem.exec.memoryPubAt i).cprime ∈ R.problem.exec.derivedResponseIO := by
    rw [ExactExecution.derivedResponseIO_eq_memoryRows, List.mem_flatMap]
    refine ⟨R.problem.exec.memoryRowAt i, hrow, ?_⟩
    simp [hver, ExactExecution.memoryPubAt]
  exact A.lio.2.2.symm.subset hresp

/-- A `verify_child` row's record is one of the derived requests, through the paired
`intermediate` layout and `C'` coherence. -/
theorem verifyChild_mem_derivedRequestIO (A : SampledIOSameExecutionAssignment R p)
    (hprl : PairedRecordLayout R.problem.exec) (hC : R.problem.exec.CprimeCoherent)
    (i : Fin R.problem.cfg.memRows)
    (hst : (R.problem.exec.memoryPubAt i).st = .verify_child) :
    NockVM.encRecC (R.problem.exec.memoryPubAt i).mem (R.problem.exec.memoryPubAt i).cprime ∈
      R.problem.exec.derivedRequestIO := by
  have hrow := R.problem.exec.memoryRowAt_mem i
  have hcons : (R.problem.exec.memoryPubAt i).mem ∈ consumedRecordList R.problem.exec := by
    rw [consumedRecordList, List.mem_flatMap]
    refine ⟨R.problem.exec.memoryRowAt i, hrow, ?_⟩
    have hst' : (R.problem.exec.memoryRowAt i).2.2.st = .verify_child := hst
    simp only [consumedRecords, hst']
    exact List.mem_singleton_self _
  have hadd := hprl.subset hcons
  rw [addedRecordList, List.mem_flatMap] at hadd
  obtain ⟨row', hrow', hin⟩ := hadd
  have hst' : row'.2.2.st = .read_root ∧ row'.2.2.mem = (R.problem.exec.memoryPubAt i).mem := by
    revert hin
    cases row'.2.2.st <;> simp [eq_comm]
  have hver : row'.2.2.ver = true := by
    rw [A.honestVer _ hrow']; simpa using hst'.1
  have hcp : row'.2.2.cprime = (R.problem.exec.memoryPubAt i).cprime :=
    hC _ hrow' _ hrow hst'.2
  have hresp : NockVM.encRecC (R.problem.exec.memoryPubAt i).mem
      (R.problem.exec.memoryPubAt i).cprime ∈ R.problem.exec.derivedResponseIO := by
    rw [ExactExecution.derivedResponseIO_eq_memoryRows, List.mem_flatMap]
    refine ⟨row', hrow', ?_⟩
    simp [hver, ← hst'.2, ← hcp]
  exact A.lio.2.2.symm.subset hresp

/-- **The bridge on `read_root` rows**: no premise beyond the specialization and the window. -/
theorem reqIdxNat_eq_recordExponent_readRoot (A : SampledIOSameExecutionAssignment R p)
    {base : SemanticSkeleton} (S : SemanticTimestampSkeleton F K base) {α : K}
    (hts : List.Forall₂ (ComputeTimestampSpecializesAt α) S.computeRows
      R.problem.exec.computeRows)
    (hor : List.Forall₂ (fun stamp row => row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
      S.computeRows R.problem.exec.computeRows)
    (hmts : List.Forall₂ (MemoryTimestampSpecializesAt α) S.memoryRows
      R.problem.exec.memoryRows)
    (hwin : totalRecordCount S.computeRows < orderOf α)
    (hmemle : ∀ stamp ∈ S.memoryRows, stamp.recordExponent ≤ totalRecordCount S.computeRows)
    (i : Fin R.problem.cfg.memRows) (hi : (i : ℕ) < S.memoryRows.length)
    (hst : (R.problem.exec.memoryPubAt i).st = .read_root) :
    reqIdxNat R (R.problem.exec.memoryPubAt i) = (S.memoryRows[(i : ℕ)]'hi).recordExponent :=
  reqIdxNat_eq_recordExponent_of_mem A S hts hor hmts hwin hmemle i hi (Or.inl hst)
    (readRoot_mem_derivedRequestIO A i hst)

/-- **The bridge on every live row** (`read_root` and `verify_child`), given the paired layout and
`C'` coherence. -/
theorem reqIdxNat_eq_recordExponent_live (A : SampledIOSameExecutionAssignment R p)
    {base : SemanticSkeleton} (S : SemanticTimestampSkeleton F K base) {α : K}
    (hts : List.Forall₂ (ComputeTimestampSpecializesAt α) S.computeRows
      R.problem.exec.computeRows)
    (hor : List.Forall₂ (fun stamp row => row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
      S.computeRows R.problem.exec.computeRows)
    (hmts : List.Forall₂ (MemoryTimestampSpecializesAt α) S.memoryRows
      R.problem.exec.memoryRows)
    (hwin : totalRecordCount S.computeRows < orderOf α)
    (hmemle : ∀ stamp ∈ S.memoryRows, stamp.recordExponent ≤ totalRecordCount S.computeRows)
    (hprl : PairedRecordLayout R.problem.exec) (hC : R.problem.exec.CprimeCoherent)
    (i : Fin R.problem.cfg.memRows) (hi : (i : ℕ) < S.memoryRows.length)
    (hlive : (R.problem.exec.memoryPubAt i).st = .read_root ∨
      (R.problem.exec.memoryPubAt i).st = .verify_child) :
    reqIdxNat R (R.problem.exec.memoryPubAt i) = (S.memoryRows[(i : ℕ)]'hi).recordExponent := by
  refine reqIdxNat_eq_recordExponent_of_mem A S hts hor hmts hwin hmemle i hi hlive ?_
  rcases hlive with h | h
  · exact readRoot_mem_derivedRequestIO A i h
  · exact verifyChild_mem_derivedRequestIO A hprl hC i h

/-- **Padding rows.**  On `decompose` / `halt` rows the carrier is `0`; the template stamps the
noun-walk rows `0` too (`GenExponentLineNumbers` §G), but `0` is not a line number, so this is the
carrier's own convention and not an identification. -/
theorem reqIdxNat_padding (i : Fin R.problem.cfg.memRows)
    (h1 : (R.problem.exec.memoryPubAt i).st ≠ .read_root)
    (h2 : (R.problem.exec.memoryPubAt i).st ≠ .verify_child) :
    reqIdxNat R (R.problem.exec.memoryPubAt i) = 0 := by
  simp [reqIdxNat, h1, h2]

end MemorySide

/-! ## §C. The generated execution -/

section Generated

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-- **F3 closed on the generated execution.**  For any accepted program (`h`), at the generated
α-free timestamp skeleton `genTimestampSkeleton` (the template the generator commits before `α`),
on any family `R` whose rows are the generated execution's rows, every live memory row carries
`reqIdx = recordExponent`.  The only window premise is the generator's own `accAt … < orderOf α`
(`genExactExecution_cprimeCoherent`'s `horbα`). -/
theorem generated_reqIdxNat_eq_recordExponent (A : SampledIOSameExecutionAssignment R p)
    (z α : K) (chal : ChallengeVector K) (hzc : chal.z = z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h) (a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α)
    (hcr : R.problem.exec.computeRows =
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).computeRows)
    (hmr : R.problem.exec.memoryRows =
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).memoryRows)
    (i : Fin R.problem.cfg.memRows)
    (hi : (i : ℕ) < (genTimestampSkeleton F (airReorder t)
      (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))
      (genComputeSkeleton_memForest_stampsWellFormed z α h)).memoryRows.length)
    (hlive : (R.problem.exec.memoryPubAt i).st = .read_root ∨
      (R.problem.exec.memoryPubAt i).st = .verify_child) :
    reqIdxNat R (R.problem.exec.memoryPubAt i) =
      ((genTimestampSkeleton F (airReorder t)
        (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))
        (genComputeSkeleton_memForest_stampsWellFormed z α h)).memoryRows[(i : ℕ)]'hi).recordExponent := by
  set S := genTimestampSkeleton F (airReorder t)
    (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))
    (genComputeSkeleton_memForest_stampsWellFormed z α h) with hS
  set G := genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
    (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem with hG
  have hts : List.Forall₂ (ComputeTimestampSpecializesAt α) S.computeRows
      R.problem.exec.computeRows := by
    rw [hcr]
    exact genComputeTimestamps (F := F) chal Ksz orbit horb z α a b c t
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem
  have hor : List.Forall₂ (fun stamp row => row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
      S.computeRows R.problem.exec.computeRows := by
    rw [hcr]
    exact genComputeOrigins (F := F) chal Ksz orbit horb z α a b c t
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem
  have hmts : List.Forall₂ (MemoryTimestampSpecializesAt α) S.memoryRows
      R.problem.exec.memoryRows := by
    rw [hmr]
    exact genMemoryTimestamps (F := F) chal Ksz orbit horb z α a b c h hmempos hcomp hmem
  have hwin : totalRecordCount S.computeRows < orderOf α := by
    rw [hS, genTimestampSkeleton_computeRows, ← accAt_len_eq_totalRecordCount]
    exact horbα
  have hmemle : ∀ stamp ∈ S.memoryRows,
      stamp.recordExponent ≤ totalRecordCount S.computeRows := by
    intro stamp hstamp
    rw [hS, genTimestampSkeleton_computeRows]
    rw [hS, genTimestampSkeleton_memoryRows] at hstamp
    exact genMemForestFromTree_stamp_exp_le_totalRecordCount (encC z) z α (airReorder t) hstamp
  have hhon : ∀ row ∈ G.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
    rw [← hmr]; exact A.honestVer
  have hprlG : PairedRecordLayout G := by
    refine genExactExecution_pairedRecordLayout chal Ksz orbit horb z α a b c
      (memInputs z) t hmempos hcomp hmem ?_ hhon
    intro row hrow
    rw [genExactExecutionA_memoryRows] at hrow
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hrow
    exact genThreadedMemory_state z α (memInputs z) h n hn
  have hprl : PairedRecordLayout R.problem.exec := by
    unfold PairedRecordLayout consumedRecordList addedRecordList at hprlG ⊢
    rw [hmr]; exact hprlG
  have hCG : G.CprimeCoherent :=
    genExactExecution_cprimeCoherent (F := F) z α chal hzc Ksz orbit horb a b c h
      hmempos hcomp hmem horbα
  have hC : R.problem.exec.CprimeCoherent := by
    unfold ExactExecution.CprimeCoherent at hCG ⊢
    rw [hmr]; exact hCG
  exact reqIdxNat_eq_recordExponent_live A S hts hor hmts hwin hmemle hprl hC i hi hlive

end Generated

section Production

/-- **F3 on the production family, composed.**  For `E = genBuildableOfProgram …` (the carrier
`nockCompiles` builds) and its exact family completion `C`, every live memory row of `C.family`
carries `reqIdx = recordExponent` of the generated α-free template.  `hzc` comes from `hinp`, the
window `horbα` from the program's own `hB`/`hwin` (`horb_of_window`), and the row-list premises
`hcr`/`hmr` hold by `rfl`. -/
theorem production_reqIdxNat_eq_recordExponent {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {q Λ : ℕ}
    (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hseed : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz)
    (hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz)
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q)
    (hq : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)))
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t)))
    (hKszChar : Ksz < ringChar K)
    (hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h)
    (hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h)
    (hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    {I : BuildableChips.Inputs (genBuildableOfProgram (F := F) z α hz htwo a b c chal hinp hmi Ksz orbit horb
        h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst)}
    (C : BuildableChips.ExactFamilyCompletion _ I)
    (A : SampledIOSameExecutionAssignment C.family (ringChar K))
    (i : Fin C.family.problem.cfg.memRows)
    (hi : (i : ℕ) < (genTimestampSkeleton F (airReorder t)
      (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))
      (genComputeSkeleton_memForest_stampsWellFormed z α h)).memoryRows.length)
    (hlive : (C.family.problem.exec.memoryPubAt i).st = MemoryTable.MState.read_root ∨
      (C.family.problem.exec.memoryPubAt i).st = MemoryTable.MState.verify_child) :
    reqIdxNat C.family (C.family.problem.exec.memoryPubAt i) =
      ((genTimestampSkeleton F (airReorder t)
        (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))
        (genComputeSkeleton_memForest_stampsWellFormed z α h)).memoryRows[(i : ℕ)]'hi).recordExponent := by
  have hzc : chal.z = z := by
    have := congrArg ComputeTable.Inputs.z hinp
    simpa [ChallengeVector.computeInputs] using this
  exact generated_reqIdxNat_eq_recordExponent A z α chal hzc Ksz orbit horb a b c h hmempos hcomp hmem
    (horb_of_window hB hwin) rfl rfl i hi hlive

end Production

end Nock.NockVMROM.Thm54.TraceGen.GenRecordExponentBridge
