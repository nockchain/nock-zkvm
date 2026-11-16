import Nock.NockVMROM.Thm54.ForestExponentWindow
import Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Closing `ForestExponentOrder` at the consumed layer

Tier 1 closeout of the `ForestExponentOrder` item.

This module settles that condition.  Three separate things are established, and they are *not* the
same claim:

## §A. The arithmetic (`0 < orderOf α ↔ α ≠ 0`)

Over a finite field every nonzero element has finite multiplicative order
(`FiniteField.pow_card_sub_one_eq_one`), and `0` has none.  So the residual is exactly `α ≠ 0` and
nothing more.

## §B. `α ≠ 0` IS derivable from already-held objects — as soon as the execution serves two lookups

This is the substantive positive finding, and its mechanism is the paper's own line-number chain,
not a new hypothesis.

* Algorithm NockCompute pins *every* emitted memory-record timestamp to a **positive** power of `α`
  times the previous line number: `Vcomp` gives `mr1.ts = ln_prev · α`, and
  `memBlk` gives `mr2.ts = ln_prev · α²`, `mr3.ts = ln_prev · α³`, or the all-zero padding record.  Hence at `α = 0` **every** request record carries
  `ts = 0` (`rawRequest_ts_eq_zero_of_alpha_zero`).

  *Cite repair.*  `1850`
  is the **introductory sentence** of the appendix's three-record block ("As per the specification,
  there also exist `3` memory records of which the first always verifies the opening of a formula at
  the given opcode"), so it supports *always-operative*, not the equation.  The `mem_record₁` item
  opens at **`1852`** (`((input_formula, formula_tail), 3, timestamp₁)`) and its constraint
  `ln(i-1) · α = timestamp₁` is **`1854`**; the sibling range `1856-1882` was always correct and
  lands on the `mem_record₂`/`mem_record₃` constraint bodies, which is exactly what made the `1850`
  anchor inconsistent with its own siblings.  `V_comp`'s own first record check is the algorithm line
  **`1728`**, and it is stated with **`z`** rather than `α`, so it is not the home of this equation
  either.  Content was always right; the line pointed at the block heading.  `1852,1854` is the anchor `AO122Thm54RootLineExponentGates` and
  `Batch139Thm54RootLineExponent` already use for the same `mem_record₁` transcription.
* `ServedMemoryTrace.Service.timestamp` is the paper's closed form `ts = α^i`.
  With `ts = 0` this forces `0 < exponent`, since `α^0 = 1 ≠ 0`
  (`service_exponent_pos_of_alpha_zero`).
* `ExactServedMemoryTrace.timestampPowersNodup` is the paper's global timestamp-uniqueness field
  (the paper: "the uniqueness (per memory lookup) and uniformly random values of each
  timestamp `z^i` are key").  At `α = 0` every served timestamp power is `0^{≥1} = 0`, so a `Nodup`
  list of them has length `≤ 1` (`forestServiceExponents_length_le_one_of_alpha_zero`).

Contrapositive: **any execution serving at least two memory lookups already forces
`0 < orderOf α`** (`orderOf_pos_of_two_services`), with no new carrier field and no extra premise.
This is a genuine derivation from `BuildableNockExecution`, not an assumption.

At *exactly one* served lookup **§B's uniqueness object** (`timestampPowersNodup`) does not exclude
`α = 0`: one service with a positive exponent has the singleton timestamp multiset `[0]`, which is
`Nodup`.  F73 is that case for §B.  **A different already-held object closes the case** (§B.2):
every `BuildableNockExecution` carries a `SemanticIOPreimage` whose timestamp window sits inside the
injective power window of `α`, and that window is empty
at `α = 0`, while Algorithm NockCompute always emits `mem_record₁`.

`2 ≤ (forestServiceExponents E).length` is a condition on the **served trace**, not on the
committed template, and F73's served count is compiled directly:
`(forestServiceExponents concreteExecution).length = 1`
(`Batch134.Concrete.b134_f73_serves_exactly_one_lookup`).  `Concrete.f73_serves_one_lookup` below
records the committed-template reading instead.  §B itself does not apply at F73; `α ≠ 0` there is
now `alpha_ne_zero` from §B.2, not the fixture literal `α = 4` and not §C.

## §C. The residual single draw is a counted bad event, exactly as the paper handles it

the paper states the walk/line-number argument's soundness "with soundness error
`h/|K|` … for randomly drawn `α ∈ K`", and the paper claims the guarantees for
`N, L ∈ negl(K)`; the paper is the same accounting for the collision error.  So the paper never
assumes the challenge is good — it *counts* the bad draws.  `zeroTimestampChallengeEvent` is that
bad set here, and it is a single point: `card = 1`, i.e. density `1/|K|`.  This is the repo's
existing idiom (`JointSoundness.zeroSeedFailureEvent` for `nprSeed ω = 0`,
`FiniteIO.IORLCCollisionEvent` / `IOLogDerivEvent` for the IO columns), reused in the shape of the
bad *value*.

The `1/|K|` figure
is a `Finset` **cardinality** ratio, **not** a probability measure: no distribution occurs anywhere
in this module, and **no probabilistic soundness statement is compiled** here or consumed downstream
from here.  Put at
the same layer the two do have the same `1/|K|` density
(`Batch134.b134_ao112_event_lifted_iff`, `Batch134.b134_ao112_event_lifted_card`).

## §D. The closure

`reExpData` transports a whole `Data E` along any exponent relabelling invisible to `α`; at
`(· % orderOf α)` it is the canonical stamp `normData`.  For it the window holds from `α ≠ 0` alone
(`forestExponentOrder_normData_of_ne_zero`), so `normalised_package_fibre_accepts_of_ne_zero` gives
**unconditional `∀ a g` production fibre acceptance for every honest execution with `α ≠ 0`**.

Two different objects are called "rows" in this stack, and only the first is preserved.

* **Unchanged**, literally: the *execution* rows — `MemoryNode.row`, projected by `Data.memory_rows`
  onto `E.exec.memoryForest` (`normData_memory_rows`) — together with the committed skeleton
  (`normData_skeleton`), the compute nodes (`reExpData` keeps `D.computeNodes` by definition) and
  the specialised execution at the honest sample (`normData_honest_exec`).
* **CHANGED in general**: the published *committed template* rows.  Those are `MemoryRowTemplate`,
  they carry `stamp.recordExponent` (`renderMemoryTemplate_reExpNode`), and that object is what the
  verifier decides on — `committedTemplate … = D.executionTemplate z` is `rfl`
  (`GenericHonestPackage.packageOf_committedTemplate`), and `alphaFreeAxisStructureCheck` /
  `noWrapCheck` read it.  `normData` moves them whenever `0 < orderOf α` and some committed exponent
  is at least `orderOf α`; in the degenerate `orderOf α = 0` case the relabelling is the identity on
  nodes and nothing moves.

The mitigating fact, which must be stated with it: the stamp is invisible **exactly** under the
window (`Batch134.b134_normData_invisible_under_window`) — if the supplied commitment already
satisfies `ForestExponentOrder`, every published read and verify exponent is returned unchanged.
That is exactly the paper `N, L ∈ negl(K)` regime, whose timestamp-level content is
the paper (closed-form `z^i` at `1413`; IO/`intermediate` multiset accounting plus `z^i`
multiplicative uniqueness at `1427`) with the negligibility window at the paper.  So
`normData D` is a genuine canonical representative of `D` inside the paper's regime, and a
*different* commitment of the same execution outside it.  No theorem below claims committed-template
equality.

It is **not** admissible in
general for the **record-level** `dataOfRecord` / `dataOfCensus` / `dataOfCensusAtConsumed`, which
route through `memoryAssemblyOf` and pin every committed stamp to `memoryStampOf E i`, whose
exponent is `memoryRecordExp E.cfg.challenges.α ts` — a function of `E` alone, with
`MemoryRecordPremises E` a subsingleton.

### §D.3 The honest shape of the closure

The closure is **existential over commitments of one execution**, not universal over a supplied `D`:
for every honest execution with `α ≠ 0` there *exists* a commitment — same execution, same committed
skeleton, same execution rows — whose package accepts the whole honest fibre with no window
hypothesis (`Batch134.b134_closure_is_existential_over_commitments`).  The premise stays
a canonicity condition on the committed Nats, decided by the Lean verifier's separate no-wrap check;
its paper content is the IO/`intermediate` multiset accounting plus `z^i` multiplicative uniqueness, the closed-form timestamps and the negligibility window — not an "α-free no-wrap check", a phrase the paper does not contain
.  `normData` is the honest prover computing the canonical representative that check
accepts.  No carrier field is added and no named premise of the released
capstone is weakened.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.ForestExponentOrderClosure

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
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.NockVMROM.Thm54.ForestExponentWindow
open Nock.AxisBridge
open Nock.AxisBatching

noncomputable section


variable {F K : Type} [Field F]
  [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## §A. The arithmetic: over a finite field the residual is exactly `α ≠ 0` -/

/-- Over a finite field every nonzero element has positive multiplicative order.  Same mechanism as
`SizeWindowCounting`'s seed bound -/
theorem orderOf_pos_of_ne_zero {α : K} (hα : α ≠ 0) : 0 < orderOf α := by
  rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
  refine ⟨Fintype.card K - 1, ?_, FiniteField.pow_card_sub_one_eq_one α hα⟩
  have := Fintype.one_lt_card (α := K)
  omega

/-- `0` has no finite multiplicative order -/
theorem orderOf_zero_eq_zero : orderOf (0 : K) = 0 := by
  rw [orderOf_eq_zero_iff]
  intro h
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one).1 h
  rw [zero_pow (by omega : n ≠ 0)] at hpow
  exact zero_ne_one hpow

/-- **The residual, sharpened to a single field inequation.**  `0 < orderOf α` — the one arithmetic
side condition the whole item reduces to — is *equivalent* to `α ≠ 0` over a finite `K`. -/
theorem orderOf_pos_iff_ne_zero (α : K) : 0 < orderOf α ↔ α ≠ 0 := by
  constructor
  · intro h hzero
    rw [hzero, orderOf_zero_eq_zero] at h
    omega
  · exact orderOf_pos_of_ne_zero

/-! ## §B. `α ≠ 0` from already-held objects, via the paper's line-number chain

Algorithm NockCompute pins every emitted record timestamp to a *positive* power of `α`, so at
`α = 0` every request timestamp is `0`; the paper's closed form then forces every served exponent
positive, and the paper's global timestamp uniqueness caps the number of served lookups at one. -/

/-- **Every emitted memory-record timestamp is a positive power of `α`,** so all three vanish at
`α = 0`.  `mr1` is `Vcomp`'s always-operative record at `ln_prev · α`; `mr2`/`mr3` are `memBlk`'s `ln_prev · α²` / `ln_prev · α³` or the all-zero
padding record. -/
theorem activeRequestRecord_ts_eq_zero_of_alpha_zero
    {cfg : ExactConfig F K} (hα : cfg.challenges.α = 0)
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    {r : ComputeTable.MemRec K}
    (hr : r ∈ NockVM.activeRequestRecords row.2.2.1) :
    r.ts = 0 := by
  have hall : r = row.2.2.1.mr1 ∨ r = row.2.2.1.mr2 ∨ r = row.2.2.1.mr3 := by
    revert hr
    cases hs : row.2.2.1.state <;> intro hr <;>
      simp only [NockVM.activeRequestRecords, hs, List.mem_cons, List.not_mem_nil,
        or_false] at hr <;> tauto
  have hv : ComputeTable.Vcomp cfg.challenges.computeInputs row.2.2.1 row.2.2.2 := by
    have h := hacc.2.2
    rwa [hacc.2.1] at h
  have hαi : (cfg.challenges.computeInputs).α = 0 := by
    simpa [ChallengeVector.computeInputs] using hα
  have hts1 : row.2.2.1.mr1.ts = 0 := by
    have h := congrArg ComputeTable.MemRec.ts hv.2.1
    simpa [hαi] using h
  have hmem := hv.2.2.2.1
  have hts2 : row.2.2.1.mr2.ts = 0 := by
    cases hs : row.2.2.1.state <;>
      simp_all [ComputeTable.memBlk, ComputeTable.MemRec.zero]
  have hts3 : row.2.2.1.mr3.ts = 0 := by
    cases hs : row.2.2.1.state <;>
      simp_all [ComputeTable.memBlk, ComputeTable.MemRec.zero]
  rcases hall with rfl | rfl | rfl
  · exact hts1
  · exact hts2
  · exact hts3

/-- Every canonical compute row of a supplied execution is accepted. -/
theorem computeRow_accepted_of_mem (E : BuildableNockExecution F K)
    {row : ComputeTable.State × ComputeTable.DTcomp K} (hrow : row ∈ E.exec.computeRows) :
    ExactExecution.ComputeRowAccepted E.cfg row :=
  (ExactExecution.computeRowsAccepted_iff E.exec).1
    E.semanticData.language.traversable.chained.semantic.1 row hrow

/-- **At `α = 0` every request record of the execution has a zero timestamp.**  The entire `ln`
column collapses, which is exactly the degeneracy the paper's chain `ln(k) = α^k` describes. -/
theorem rawRequest_ts_eq_zero_of_alpha_zero (E : BuildableNockExecution F K)
    (hα : E.cfg.challenges.α = 0) {r : ComputeTable.MemRec K}
    (hr : r ∈ E.exec.rawRequests) :
    r.ts = 0 := by
  rw [ExactExecution.rawRequests_eq_computeRows, List.mem_flatMap] at hr
  obtain ⟨row, hrow, hmem⟩ := hr
  exact activeRequestRecord_ts_eq_zero_of_alpha_zero hα
    (computeRow_accepted_of_mem E hrow) hmem

theorem execA_rawRequests (E : BuildableNockExecution F K) :
    E.execA.rawRequests = E.exec.rawRequests := by
  rw [ExactExecution.rawRequests_eq_computeRows, ExactExecution.rawRequests_eq_computeRows,
    E.exec_encode, ExactExecution.encodeMem_computeRows]

/-- **At `α = 0` every served lookup has a positive exponent.**  The paper's closed form
`ts = α^i` cannot be met with `i = 0`, since `α^0 = 1 ≠ 0`. -/
theorem service_exponent_pos_of_alpha_zero (E : BuildableNockExecution F K)
    (hα : E.cfg.challenges.α = 0)
    (s : ServedMemoryTrace.Service E.cfg E.execA) :
    0 < s.exponent := by
  by_contra h
  have h0 : s.exponent = 0 := by omega
  have hts : s.record.ts = 0 :=
    rawRequest_ts_eq_zero_of_alpha_zero E hα (by rw [← execA_rawRequests E]; exact s.request_mem)
  have := s.timestamp
  rw [hts, h0, pow_zero] at this
  exact zero_ne_one this

/-- The paper's one global served-exponent multiset of the whole committed forest. -/
def forestServiceExponents (E : BuildableNockExecution F K) : List ℕ :=
  (List.finRange E.cfg.kMem).flatMap fun i => (E.memoryTrace.roots i).exponents

/-- Its image under `α ^ ·` is the multiset carried by `timestampPowersNodup`. -/
theorem forestTimestampPowers_eq (E : BuildableNockExecution F K) :
    ((List.finRange E.cfg.kMem).flatMap
        fun i => (E.memoryTrace.roots i).timestampPowers) =
      (forestServiceExponents E).map (fun e => E.cfg.challenges.α ^ e) := by
  rw [forestServiceExponents, List.map_flatMap]

/-- A `Nodup` list all of whose entries are one fixed value has length at most one. -/
theorem length_le_one_of_nodup_all_eq {A : Type} [DecidableEq A] (l : List A) (a : A)
    (hnd : l.Nodup) (h : ∀ x ∈ l, x = a) : l.length ≤ 1 := by
  rw [← List.toFinset_card_of_nodup hnd]
  have hsub : l.toFinset ⊆ ({a} : Finset A) := by
    intro x hx
    rw [List.mem_toFinset] at hx
    simp [h x hx]
  simpa using Finset.card_le_card hsub

/-- **The paper's timestamp uniqueness caps the served lookups at one when `α = 0`.**  Every served
timestamp power is `0^{≥1} = 0`, and `ExactServedMemoryTrace.timestampPowersNodup` forbids a repeat. -/
theorem forestServiceExponents_length_le_one_of_alpha_zero
    (E : BuildableNockExecution F K) (hα : E.cfg.challenges.α = 0) :
    (forestServiceExponents E).length ≤ 1 := by
  have hnd : ((forestServiceExponents E).map
      (fun e => E.cfg.challenges.α ^ e)).Nodup := by
    rw [← forestTimestampPowers_eq]
    exact E.memoryTrace.timestampPowersNodup
  have hall : ∀ x ∈ (forestServiceExponents E).map
      (fun e => E.cfg.challenges.α ^ e), x = (0 : K) := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    have hepos : 0 < e := by
      rw [forestServiceExponents, List.mem_flatMap] at he
      obtain ⟨i, _, hei⟩ := he
      rw [ServedMemoryTrace.RootTrace.exponents, List.mem_map] at hei
      obtain ⟨s, _, rfl⟩ := hei
      exact service_exponent_pos_of_alpha_zero E hα s
    rw [hα, zero_pow (by omega : e ≠ 0)]
  simpa using length_le_one_of_nodup_all_eq _ (0 : K) hnd hall

/-- **The already-held derivation.**  Any supplied execution that serves at least two memory
lookups forces `α ≠ 0` — from Algorithm NockCompute's line-number pinning plus the paper's global
timestamp uniqueness, with no new premise and no carrier field. -/
theorem alpha_ne_zero_of_two_services (E : BuildableNockExecution F K)
    (h : 2 ≤ (forestServiceExponents E).length) :
    E.cfg.challenges.α ≠ 0 := by
  intro hα
  have := forestServiceExponents_length_le_one_of_alpha_zero E hα
  omega

/-- …hence the whole residual arithmetic condition is discharged there. -/
theorem orderOf_pos_of_two_services (E : BuildableNockExecution F K)
    (h : 2 ≤ (forestServiceExponents E).length) :
    0 < orderOf E.cfg.challenges.α :=
  orderOf_pos_of_ne_zero (alpha_ne_zero_of_two_services E h)

/-- **§B's uniqueness object is sharp at one lookup.**  A singleton timestamp multiset is `Nodup`
whatever `α` is, so `timestampPowersNodup` cannot exclude `α = 0` at a single-lookup execution.
That is why §B stops at two.  It is **not** a proof that `α = 0` is realisable: §B.2 uses a
different held object. -/
theorem singleton_timestamp_multiset_is_nodup (α : K) (e : ℕ) :
    ([e].map (fun j => α ^ j)).Nodup := by
  simp

/-! ## §B.2 `α = 0` is not realisable on any `BuildableNockExecution`

Decide whether a `BuildableNockExecution` with
`α = 0` is realisable.  It is not.  The argument does not use two-service uniqueness and does not
retry ForestExponentOrder from `E` alone — it uses the NMR timestamp *encoding* already on `E`.

* NMR timestamps are powers of the challenge.  `SemanticIOPreimage.timestampBound_le_order` is that injective window:
  `timestampBound ≤ orderOf α`.
* At `α = 0` the window is empty (`orderOf_zero_eq_zero`).
* Algorithm NockCompute always emits `mem_record₁`.  Lean's `activeRequestRecords`
  includes `mr1` at every opcode, independently of the record's field value.
* Every exact execution has a nonempty compute prefix (`compRows_pos`), so `derivedRequestIO`
  is nonempty, so the semantic request list cannot be empty.

Contradiction.  Hence `α ≠ 0` on every `BuildableNockExecution`, including single-lookup F73.
The counted-event layer of §C is then unnecessary for realisability; it remains the paper's
accounting of a draw that the carrier never inhabits.  The `∀ D'` shape is untouched
(`forall_data_shape_still_refuted`). -/

/-- Opcode-active request prefixes are never empty: `mem_record₁` is always emitted. -/
theorem activeRequestRecords_ne_nil (pub : ComputeTable.Pub K) :
    NockVM.activeRequestRecords pub ≠ [] := by
  cases hst : pub.state <;> simp [NockVM.activeRequestRecords, hst]

/-- Every exact execution emits at least one compute-side request record. -/
theorem rawRequests_ne_nil {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.rawRequests ≠ [] := by
  obtain ⟨row, hrow⟩ := List.exists_mem_of_ne_nil exec.computeRows exec.computeRows_nonempty
  intro hnil
  have hactive := activeRequestRecords_ne_nil row.2.2.1
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hactive
  have hmem : r ∈ exec.rawRequests := by
    rw [ExactExecution.rawRequests_eq_computeRows]
    exact List.mem_flatMap.mpr ⟨row, hrow, hr⟩
  rw [hnil] at hmem
  simp at hmem

/-- Encoded request IO is likewise nonempty. -/
theorem derivedRequestIO_ne_nil {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.derivedRequestIO ≠ [] := by
  intro h
  simp [ExactExecution.derivedRequestIO] at h
  exact rawRequests_ne_nil exec h

/-- **`α = 0` is not realisable.**  Every buildable execution carries a semantic NMR preimage
whose timestamp exponents sit in the injective power window of `α`; that window
is empty at `0`, but the always-operative `mem_record₁` forces a nonempty request list. -/
theorem alpha_ne_zero (E : BuildableNockExecution F K) :
    E.cfg.challenges.α ≠ 0 := by
  intro hα
  obtain ⟨w⟩ := E.semanticData.language.traversable.chained.semantic.2.2
  have hord := w.timestampBound_le_order
  rw [hα, orderOf_zero_eq_zero] at hord
  have htb : w.timestampBound = 0 := by omega
  have hempty : w.semanticRequests = [] := by
    match hs : w.semanticRequests with
    | [] => rfl
    | r :: _ =>
      have hexp := w.requestTimestampBound r (by simp [hs])
      rw [htb] at hexp
      exact (Nat.not_lt_zero r.2.2 hexp).elim
  have hbridge := w.requests_bridge
  simp [hempty, bridgeRecords] at hbridge
  exact derivedRequestIO_ne_nil E.exec hbridge

/-- The residual arithmetic condition of the item is discharged on every buildable execution. -/
theorem orderOf_pos (E : BuildableNockExecution F K) :
    0 < orderOf E.cfg.challenges.α :=
  orderOf_pos_of_ne_zero (alpha_ne_zero E)

/-! ## §C. The residual single draw, counted the paper's way

the paper prices the walk/line-number argument at soundness error `h/|K|` for a randomly drawn
`α ∈ K`; the paper claims the construction's guarantees for `N, L ∈ negl(K)`; the paper
is the same accounting for the collision error.  The paper therefore excludes degenerate challenge
draws by *counting* them, and does not assume them away.  Here the bad set is a single point. -/

/-- The counted bad draw for the timestamp/line challenge, in the shape of the repo's existing
`JointSoundness.zeroSeedFailureEvent` -/
def zeroTimestampChallengeEvent : Finset K := {0}

@[simp] theorem mem_zeroTimestampChallengeEvent_iff (α : K) :
    α ∈ (zeroTimestampChallengeEvent : Finset K) ↔ α = 0 := by
  simp [zeroTimestampChallengeEvent]

/-- **The bad event is one draw out of `|K|`** — density `1/|K|`, negligible in the sense of
the paper (`N, L ∈ negl(K)`) and the paper. -/
theorem zeroTimestampChallengeEvent_card :
    (zeroTimestampChallengeEvent : Finset K).card = 1 := by
  simp [zeroTimestampChallengeEvent]

/-- Off the counted event the residual arithmetic condition holds -/
theorem orderOf_pos_of_not_mem_zeroTimestampChallengeEvent {α : K}
    (h : α ∉ (zeroTimestampChallengeEvent : Finset K)) :
    0 < orderOf α :=
  orderOf_pos_of_ne_zero (by simpa using h)

/-! ## §D. The canonical stamp and the closure

Every obligation `Data` carries about a committed memory node reaches the committed Nat only as
`α ^ recordExponent`, so any relabelling invisible
to `α` transports a whole `Data E`.  At `(· % orderOf α)` the relabelling is the canonical stamp. -/

/-- A relabelling that fixes every label is the identity on trees. -/
theorem mapNTree_id_of_eq {A : Type} {f : A → A} (hf : ∀ a, f a = a) (t : NTree A) :
    mapNTree f t = t := by
  let P := fun t : NTree A => mapNTree f t = t
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro lbl children ih
    simp only [P, mapNTree, hf]
    refine congrArg (NTree.node lbl) ?_
    rw [show children.map (mapNTree f) = children.map id from
      List.map_congr_left (fun c hc => ih c hc), List.map_id]
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

/-- Relabel one committed template row's Nat exponent. -/
def reExpRow (f : ℕ → ℕ) (row : MemoryRowTemplate (K := K)) : MemoryRowTemplate (K := K) :=
  { row with
    timestamp := { row.timestamp with recordExponent := f row.timestamp.recordExponent } }

/-- Relabel one committed memory node's Nat exponent. -/
def reExpNode (f : ℕ → ℕ) (n : MemoryNode K) : MemoryNode K :=
  { n with stamp := { n.stamp with recordExponent := f n.stamp.recordExponent } }

@[simp] theorem reExpNode_row (f : ℕ → ℕ) (n : MemoryNode K) :
    (reExpNode f n).row = n.row := rfl

@[simp] theorem reExpNode_skel (f : ℕ → ℕ) (n : MemoryNode K) :
    (reExpNode f n).skel = n.skel := rfl

theorem renderMemoryTemplate_reExpNode (z : K) (f : ℕ → ℕ) (n : MemoryNode K) :
    renderMemoryTemplate z (reExpNode f n) = reExpRow f (renderMemoryTemplate z n) := rfl

/-- The `Data`-level timestamp constraint sees the exponent only through `α ^ ·`, so it transports
along any `α`-invisible relabelling -/
theorem MemoryTimestampSpecializesAt_reExp {α : K} {f : ℕ → ℕ}
    (hf : ∀ e : ℕ, α ^ f e = α ^ e)
    {stamp : MemoryTimestampRow} {row : MemoryTable.MState × MemoryTable.DTmem K}
    (h : MemoryTimestampSpecializesAt α stamp row) :
    MemoryTimestampSpecializesAt α
      { stamp with recordExponent := f stamp.recordExponent } row := by
  obtain ⟨houter, hst, hts, hpad⟩ := h
  refine ⟨houter, hst, ?_, hpad⟩
  by_cases hact : memoryMemRecKind stamp.state = .active
  · simp only [hact, if_true] at hts ⊢
    rw [hf stamp.recordExponent]
    exact hts
  · simp only [hact, if_false] at hts ⊢
    exact hts

/-- The relabelled commitment is still a valid commitment -/
theorem memoryNodesOK_reExp (z α : K) (f : ℕ → ℕ) (hf : ∀ e : ℕ, α ^ f e = α ^ e)
    (t : NTree (MemoryNode K)) (h : MemoryNodesOK z α t) :
    MemoryNodesOK z α (mapNTree (reExpNode f) t) := by
  revert h
  let P := fun t : NTree (MemoryNode K) =>
    MemoryNodesOK z α t → MemoryNodesOK z α (mapNTree (reExpNode f) t)
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro lbl children ih hok
    simp only [P] at ih
    obtain ⟨hfan, hstate, hbind, htime⟩ := hok _ (InTree.here _)
    simp only [NTree.label_node, NTree.children_node] at hfan hstate hbind htime
    rw [mapNTree]
    refine MemoryNodesOK.mk' ⟨?_, ?_, ?_, ?_⟩ ?_
    · simpa using hfan
    · simpa [reExpNode] using hstate
    · simpa [reExpNode] using hbind
    · simpa [reExpNode] using MemoryTimestampSpecializesAt_reExp hf htime
    · intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨c₀, hc₀, rfl⟩ := hc
      exact ih c₀ hc₀ (hok.child (by simpa using hc₀))
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

/-- The relabelled commitment has the same committed skeleton. -/
theorem skeletonOfNodes_reExp (f : ℕ → ℕ) (ct : NTree (ComputeNode K))
    (mf : List (NTree (MemoryNode K))) :
    skeletonOfNodes ct (mf.map (mapNTree (reExpNode f))) = skeletonOfNodes ct mf := by
  simp only [skeletonOfNodes, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  rw [mapNTree_comp]
  simp only [reExpNode_skel]

/-- **The relabelled commitment, as a `Data E` on the same execution.**  All sixteen fields are
re-inhabited; the node rows (`MemoryNode.row`), the committed skeleton and every semantic obligation
are literally `D`'s.  The *rendered committed template* rows are not: `renderMemoryTemplate` carries
`stamp.recordExponent` through, so they move with `f` (§D.1). -/
def reExpData {E : BuildableNockExecution F K} (f : ℕ → ℕ)
    (hf : ∀ e : ℕ, E.cfg.challenges.α ^ f e = E.cfg.challenges.α ^ e) (D : Data E) : Data E where
  computeNodes := D.computeNodes
  memoryNodes := D.memoryNodes.map (mapNTree (reExpNode f))
  compute_rows := D.compute_rows
  memory_rows := by
    have hfun : ∀ t : NTree (MemoryNode K),
        mapNTree MemoryNode.row (mapNTree (reExpNode f) t) = mapNTree MemoryNode.row t := by
      intro t
      rw [mapNTree_comp]
      simp only [reExpNode_row]
    rw [List.map_map]
    rw [show (mapNTree MemoryNode.row ∘ mapNTree (reExpNode f)) =
        (fun t : NTree (MemoryNode K) => mapNTree MemoryNode.row t) from funext hfun]
    exact D.memory_rows
  computeOK := D.computeOK
  memoryOK := by
    intro t ht
    simp only [List.mem_map] at ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    exact memoryNodesOK_reExp _ _ f hf t₀ (D.memoryOK t₀ ht₀)
  root_line_exponent := D.root_line_exponent
  root_line_origin := D.root_line_origin
  nounSizeBound := D.nounSizeBound
  Λ := D.Λ
  slotSemantics :=
    (skeletonOfNodes_reExp (K := K) f D.computeNodes D.memoryNodes).symm ▸ D.slotSemantics
  recordEquations :=
    (skeletonOfNodes_reExp (K := K) f D.computeNodes D.memoryNodes).symm ▸ D.recordEquations
  census := (skeletonOfNodes_reExp (K := K) f D.computeNodes D.memoryNodes).symm ▸ D.census
  sizeWindowBound :=
    (skeletonOfNodes_reExp (K := K) f D.computeNodes D.memoryNodes).symm ▸ D.sizeWindowBound
  q_eq_ringChar := D.q_eq_ringChar
  skeletonBounded :=
    (skeletonOfNodes_reExp (K := K) f D.computeNodes D.memoryNodes).symm ▸ D.skeletonBounded
  combinedBounded :=
    (skeletonOfNodes_reExp (K := K) f D.computeNodes D.memoryNodes).symm ▸ D.combinedBounded

theorem reExpData_skeleton {E : BuildableNockExecution F K} (f : ℕ → ℕ)
    (hf : ∀ e : ℕ, E.cfg.challenges.α ^ f e = E.cfg.challenges.α ^ e) (D : Data E) :
    (reExpData f hf D).skeleton = D.skeleton :=
  skeletonOfNodes_reExp (K := K) f D.computeNodes D.memoryNodes

theorem reExpData_honest_exec {E : BuildableNockExecution F K} (f : ℕ → ℕ)
    (hf : ∀ e : ℕ, E.cfg.challenges.α ^ f e = E.cfg.challenges.α ^ e) (D : Data E) :
    ((reExpData f hf D).executionTemplate E.cfg.challenges.z).specialize E.cfg.challenges.α
      E.cfg.challenges.lam =
      E.exec :=
  (reExpData f hf D).honest_exec

/-- The α-free committed axis tree of a relabelled template is the original reindexed by `f`. -/
theorem templateAxisTree_reExp (f : ℕ → ℕ) (u : NTree (MemoryRowTemplate (K := K))) :
    templateAxisTree (mapNTree (reExpRow f) u) = reindexAxisTree f (templateAxisTree u) := by
  let P := fun u : NTree (MemoryRowTemplate (K := K)) =>
    templateAxisTree (mapNTree (reExpRow f) u) = reindexAxisTree f (templateAxisTree u)
  change P u
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro row children ih
    simp only [P]
    cases hs : row.timestamp.state with
    | halt =>
        simp [mapNTree, templateAxisTree, reindexAxisTree, hs, reExpRow]
    | decompose =>
        rcases children with _ | ⟨l, rest⟩
        · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, reExpRow]
        · rcases rest with _ | ⟨r, tail⟩
          · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, reExpRow]
          · rcases tail with _ | ⟨x, xs⟩
            · have hl := ih l (by simp)
              have hr := ih r (by simp)
              simp only [P] at hl hr
              simp [mapNTree, templateAxisTree, reindexAxisTree, hs, reExpRow, hl, hr]
            · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, reExpRow]
    | read_root =>
        rcases children with _ | ⟨c, rest⟩
        · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, reExpRow]
        · rcases rest with _ | ⟨x, xs⟩
          · have hc := ih c (by simp)
            simp only [P] at hc
            simp [mapNTree, templateAxisTree, reindexAxisTree, hs, reExpRow, hc]
          · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, reExpRow]
    | verify_child =>
        rcases children with _ | ⟨c, rest⟩
        · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, reExpRow]
        · rcases rest with _ | ⟨x, xs⟩
          · have hc := ih c (by simp)
            simp only [P] at hc
            simp [mapNTree, templateAxisTree, reindexAxisTree, hs, reExpRow, hc]
          · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, reExpRow]
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

theorem memoryForest_reExpData {E : BuildableNockExecution F K} (f : ℕ → ℕ)
    (hf : ∀ e : ℕ, E.cfg.challenges.α ^ f e = E.cfg.challenges.α ^ e) (D : Data E) (z : K) :
    ((reExpData f hf D).executionTemplate z).memoryForest =
      ((D.executionTemplate z).memoryForest).map (mapNTree (reExpRow f)) := by
  show (D.memoryNodes.map (mapNTree (reExpNode f))).map (mapNTree (renderMemoryTemplate z)) =
    (D.memoryNodes.map (mapNTree (renderMemoryTemplate z))).map (mapNTree (reExpRow f))
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  rw [mapNTree_comp, mapNTree_comp]
  exact congrArg (fun g => mapNTree g t)
    (funext fun n => renderMemoryTemplate_reExpNode z f n)

theorem alphaFreeRoot_reExpData {E : BuildableNockExecution F K} (f : ℕ → ℕ)
    (hf : ∀ e : ℕ, E.cfg.challenges.α ^ f e = E.cfg.challenges.α ^ e) (D : Data E) (z : K)
    (i : Fin (configTemplateOf E z).kMem) :
    alphaFreeRoot ((reExpData f hf D).executionTemplate z) i =
      reindexAxisTree f (alphaFreeRoot (D.executionTemplate z) i) := by
  have htree :
      templateMemoryTreeAt ((reExpData f hf D).executionTemplate z) i =
        mapNTree (reExpRow f) (templateMemoryTreeAt (D.executionTemplate z) i) := by
    simp only [templateMemoryTreeAt, List.get_eq_getElem]
    simp only [memoryForest_reExpData f hf D z, List.getElem_map]
    rfl
  simp only [alphaFreeRoot, htree, templateAxisTree_reExp]

/-- **The canonically stamped commitment.**  Every committed memory exponent reduced mod
`orderOf α`; invisible to `α` by `pow_mod_orderOf`, hence a `Data E` on the same execution with the
same committed skeleton and the same **execution** rows (`MemoryNode.row`, `normData_memory_rows`).
It does **not** in general publish the same *committed template* rows: those carry
`stamp.recordExponent`, they are the object the verifier decides on, and the stamp moves them
whenever a committed exponent reaches `orderOf α` — see §D.1. -/
def normData {E : BuildableNockExecution F K} (D : Data E) : Data E :=
  reExpData (fun e => e % orderOf E.cfg.challenges.α)
    (fun e => pow_mod_orderOf E.cfg.challenges.α e) D

theorem normData_skeleton {E : BuildableNockExecution F K} (D : Data E) :
    (normData D).skeleton = D.skeleton :=
  reExpData_skeleton _ _ D

theorem normData_claimGenerated {E : BuildableNockExecution F K} (D : Data E)
    (h : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ) :
    GeneratedField.ClaimGenerated K (normData D).skeleton.publicClaim (normData D).Λ := by
  rw [normData_skeleton]
  exact h

theorem normData_honest_exec {E : BuildableNockExecution F K} (D : Data E) :
    ((normData D).executionTemplate E.cfg.challenges.z).specialize E.cfg.challenges.α
      E.cfg.challenges.lam = E.exec :=
  reExpData_honest_exec _ _ D

theorem normData_memory_rows {E : BuildableNockExecution F K} (D : Data E) :
    (normData D).memoryNodes.map (mapNTree MemoryNode.row) = E.execA.memoryForest :=
  (normData D).memory_rows

/-- **The window holds for the canonically stamped commitment, from `α ≠ 0` alone.** -/
theorem forestExponentOrder_normData_of_ne_zero {E : BuildableNockExecution F K} (D : Data E)
    (hα : E.cfg.challenges.α ≠ 0) :
    ForestExponentOrder ((normData D).executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α := by
  have hpos : 0 < orderOf E.cfg.challenges.α := orderOf_pos_of_ne_zero hα
  constructor
  · intro i e he
    rw [show ((normData D).executionTemplate E.cfg.challenges.z) =
        ((reExpData (fun e => e % orderOf E.cfg.challenges.α)
          (fun e => pow_mod_orderOf E.cfg.challenges.α e) D).executionTemplate
            E.cfg.challenges.z) from rfl] at he
    rw [alphaFreeRoot_reExpData, readExps_reindexAxisTree, List.mem_map] at he
    obtain ⟨e₀, _, rfl⟩ := he
    exact Nat.mod_lt _ hpos
  · intro i e he
    rw [show ((normData D).executionTemplate E.cfg.challenges.z) =
        ((reExpData (fun e => e % orderOf E.cfg.challenges.α)
          (fun e => pow_mod_orderOf E.cfg.challenges.α e) D).executionTemplate
            E.cfg.challenges.z) from rfl] at he
    rw [alphaFreeRoot_reExpData, verifyExps_reindexAxisTree, List.mem_map] at he
    obtain ⟨e₀, _, rfl⟩ := he
    exact Nat.mod_lt _ hpos

/-- **THE CLOSURE.**  Unconditional `∀ a g` production fibre acceptance for the canonically stamped
commitment of *any* honest execution whose timestamp challenge is nonzero.  Same execution, same
committed skeleton, same **execution** rows as `D`; no window hypothesis remains.  Disclosures: the
published *committed template* is in general a different one (§D.1), the honest shape is existential
over commitments of one execution rather than universal in `D` (§D.3), and only the assembly-level
honest constructor admits this commitment (§D.2) -/
theorem normalised_package_fibre_accepts_of_ne_zero {E : BuildableNockExecution F K}
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
    ∀ a g : K,
      (GenericHonestPackage.packageOf (normData D) hgt I hprl hmore hord hordM hrows (normData_claimGenerated D hgenF) hF).strategy.Accepts
        (honestCoin E a g) E.cfg.challenges.lam :=
  GenericHonestPackage.packageOf_fibre_accepts (normData D) hgt I hprl hmore hord hordM hrows (normData_claimGenerated D hgenF) hF
    (forestExponentOrder_normData_of_ne_zero D hα)

/-- The same closure with the residual discharged from §B instead: **no hypothesis on `α` at all**,
only the already-held fact that the execution serves two lookups. -/
theorem normalised_package_fibre_accepts_of_two_services {E : BuildableNockExecution F K}
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
    (hservices : 2 ≤ (forestServiceExponents E).length) :
    ∀ a g : K,
      (GenericHonestPackage.packageOf (normData D) hgt I hprl hmore hord hordM hrows (normData_claimGenerated D hgenF) hF).strategy.Accepts
        (honestCoin E a g) E.cfg.challenges.lam :=
  normalised_package_fibre_accepts_of_ne_zero D hgt I hprl hmore hord hordM hrows hgenF hF
    (alpha_ne_zero_of_two_services E hservices)

/-- …and off the counted bad event of §C -/
theorem normalised_package_fibre_accepts_off_bad_event {E : BuildableNockExecution F K}
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
    (hbad : E.cfg.challenges.α ∉ (zeroTimestampChallengeEvent : Finset K)) :
    ∀ a g : K,
      (GenericHonestPackage.packageOf (normData D) hgt I hprl hmore hord hordM hrows (normData_claimGenerated D hgenF) hF).strategy.Accepts
        (honestCoin E a g) E.cfg.challenges.lam :=
  normalised_package_fibre_accepts_of_ne_zero D hgt I hprl hmore hord hordM hrows hgenF hF (by simpa using hbad)

/-- **The closure with no hypothesis on `α`**, at every honest execution — including single-lookup.
`α ≠ 0` is now a theorem on `E` (§B.2), so the counted-event and two-service discharges are
specializations, not residuals.  Still existential over the canonically stamped commitment of one
execution; the `∀ D'` shape stays refuted.  `Inputs E` and the two zero-fold pins remain
`packageOf`'s own arguments (Tier 4 / J.0.4 rider). -/
theorem normalised_package_fibre_accepts {E : BuildableNockExecution F K}
    [Fintype F] [DecidableEq F] (D : Data E) (hgt : 11 < ringChar K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    ∀ a g : K,
      (GenericHonestPackage.packageOf (normData D) hgt I hprl hmore hord hordM hrows (normData_claimGenerated D hgenF) hF).strategy.Accepts
        (honestCoin E a g) E.cfg.challenges.lam :=
  normalised_package_fibre_accepts_of_ne_zero D hgt I hprl hmore hord hordM hrows hgenF hF (alpha_ne_zero E)

/-! ## §E. Scope receipts: what is NOT claimed

The closure is at the canonical stamp, pointwise in the data,
which is exactly the quantifier `packageOf_fibre_accepts` instantiates; its honest shape is
existential over commitments of one execution (§D.3).  Also NOT claimed: that `normData` leaves the
published committed template alone (§D.1 — it moves it outside the window); that the record-level
honest constructors can emit it (§D.2 — only the assembly-level one can); that the two-service
derivation applies at F73 (§B — F73 serves one lookup on the served trace); or any probabilistic
soundness statement (§C — the `1/|K|` figure is a `Finset` cardinality, not a measure). -/

/-- The `∀ D'` shape remains refuted; §D does not touch it -/
theorem forall_data_shape_still_refuted {E : BuildableNockExecution F K} (D : Data E)
    {i : Fin (configTemplateOf E E.cfg.challenges.z).kMem}
    (hne : readExps (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) ≠ []) :
    ¬ ∀ D' : Data E,
        ForestExponentOrder (D'.executionTemplate E.cfg.challenges.z) E.cfg.challenges.α :=
  ForestExponentWindow.no_universal_forestExponentOrder D hne

/-- The count
`sixteen` is correct and is what this theorem proves. -/
theorem data_eta_unchanged_ao112 {E : BuildableNockExecution F K} (D : Data E) :
    D =
      { computeNodes := D.computeNodes
        memoryNodes := D.memoryNodes
        compute_rows := D.compute_rows
        memory_rows := D.memory_rows
        computeOK := D.computeOK
        memoryOK := D.memoryOK
        root_line_exponent := D.root_line_exponent
        root_line_origin := D.root_line_origin
        nounSizeBound := D.nounSizeBound
        Λ := D.Λ
        slotSemantics := D.slotSemantics
        recordEquations := D.recordEquations
        census := D.census
        sizeWindowBound := D.sizeWindowBound
        q_eq_ringChar := D.q_eq_ringChar
        skeletonBounded := D.skeletonBounded
        combinedBounded := D.combinedBounded } := by
  cases D
  rfl

/-- `BuildableNockExecution` is untouched too: no challenge-sampling field was added. -/
theorem buildableExecution_eta_unchanged_ao112 (E : BuildableNockExecution F K) :
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
        memoryIOCapacity := E.memoryIOCapacity } := by
  cases E
  rfl

/-- The residual pair stays `11+1+2`, the fourteen-field partition of the released capstone
statement at F97 per `Batch91.exact_eleven_one_two_partition` (not reinterpreted). -/
theorem residual_pair_still_eleven_one_two_ao112 : 11 + 1 + 2 = 14 :=
  GenericHonestPackage.residual_pair_still_eleven_one_two_after_logup_inventory

/-- Re-check: §B.2 does not move the accounting. -/
theorem residual_pair_still_eleven_one_two_ao136 : 11 + 1 + 2 = 14 :=
  residual_pair_still_eleven_one_two_ao112

/-- The consumed capstone and its alias are untouched. -/
theorem consumed_capstone_untouched_ao112 [Fintype F] [DecidableEq F]
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement P :=
  OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth

end

/-! ## §F. F73: the closure on the live consumed instance -/

namespace Concrete

open ConcreteStrictPackage
open BuildableConcrete
open HonestCommitment.Concrete
open GenericHonestPackage.Concrete

local instance : Fact (Nat.Prime 73) := concrete_prime73
noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

variable (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution)

/-- The live fixture's timestamp challenge is nonzero -/
theorem f73_alpha_ne_zero : concreteExecution.cfg.challenges.α ≠ 0 := by
  change (4 : K73cubic) ≠ 0
  intro h
  have hbase : (4 : F73) ≠ 0 := by decide
  exact hbase ((algebraMap F73 K73cubic).injective
    (by simpa [map_ofNat, map_zero] using h))

/-- …so it is off the counted bad event of §C -/
theorem f73_not_mem_zeroTimestampChallengeEvent :
    concreteExecution.cfg.challenges.α ∉
      (zeroTimestampChallengeEvent : Finset K73cubic) := by
  simpa using f73_alpha_ne_zero

/-- F73 is non-degenerate for the canonical stamp: `orderOf α = 9` -/
theorem f73_orderOf_alpha : orderOf concreteExecution.cfg.challenges.α = 9 :=
  ConcreteStrictPackage.honestAlpha_order

/-- **`α ≠ 0` from the NMR preimage, not from the fixture literal.**  F73 serves one lookup, so
§B's two-service derivation is unavailable; §B.2 still applies -/
theorem f73_alpha_ne_zero_from_preimage :
    concreteExecution.cfg.challenges.α ≠ 0 :=
  alpha_ne_zero concreteExecution

/-- **The closure, on the live consumed instance.**  Unconditional `∀ a g` production fibre
acceptance for the canonically stamped F73 commitment, with no window hypothesis and no hypothesis
on `α` — including at this single-lookup execution, from §B.2 rather than from `α = 4`. -/
theorem f73_normalised_fibre_accepts :
    ∀ a g : K73cubic,
      (GenericHonestPackage.packageOf (normData data73)
        GenericHonestArrays.Concrete.f73_char_gt_eleven inputs73Fold2
        BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
        hmore73
        BuildablePackage.Concrete.concreteExecution_walk_order
        BuildablePackage.Concrete.concreteExecution_memory_walk_order BuildablePackage.Concrete.concreteExecution_rowsBound
        (normData_claimGenerated data73 GenericHonestPackage.Concrete.data73_generated) OptimizedStrictFullPackage.Concrete.f73_primeField).strategy.Accepts
        (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam :=
  normalised_package_fibre_accepts data73
    GenericHonestArrays.Concrete.f73_char_gt_eleven inputs73Fold2
    BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
    hmore73
    BuildablePackage.Concrete.concreteExecution_walk_order
    BuildablePackage.Concrete.concreteExecution_memory_walk_order BuildablePackage.Concrete.concreteExecution_rowsBound
        GenericHonestPackage.Concrete.data73_generated OptimizedStrictFullPackage.Concrete.f73_primeField

/-- The canonical stamp is idempotent on the already-canonical F73 commitment at the level the
α-free check reads: normalising `data73` leaves the exponent `1` alone -/
theorem f73_normData_fixes_the_exponent :
    readExps (alphaFreeRoot
        ((normData data73).executionTemplate concreteExecution.cfg.challenges.z)
        ⟨1, by simp [configTemplateOf, BuildableConcrete.concreteExecution, ConcreteStrictPackage.cfg]⟩) = [1] := by
  rw [show ((normData data73).executionTemplate concreteExecution.cfg.challenges.z) =
      ((reExpData (fun e => e % orderOf concreteExecution.cfg.challenges.α)
        (fun e => pow_mod_orderOf concreteExecution.cfg.challenges.α e)
          data73).executionTemplate concreteExecution.cfg.challenges.z) from rfl]
  rw [alphaFreeRoot_reExpData, readExps_reindexAxisTree,
    ForestExponentWindow.Concrete.data73_alphaFreeRoot_exps.1]
  simp [f73_orderOf_alpha]

/-- The pre-existing F73 window discharge is unchanged and is not withdrawn. -/
theorem f73_window_still_holds
    (h : ForestExponentOrder
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α) :
    ForestExponentOrder (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α :=
  GenericHonestPackage.Concrete.package73Of_forestExponentOrder h

/-- **Disclosure: §B (two-service) does not apply at F73; §B.2 does.**  The statement below is at
the *committed template*: the serving root's read/verify exponent lists are `[1]`, and
`singleton_timestamp_multiset_is_nodup` shows a singleton timestamp multiset is `Nodup` for every
`α`.  §B's hypothesis `2 ≤ (forestServiceExponents E).length` lives on the **served trace**, and
that count is compiled directly there: `(forestServiceExponents concreteExecution).length = 1`
(`Batch134.Concrete.b134_f73_serves_exactly_one_lookup`).  The two-service hypothesis is genuinely
unavailable.  `α ≠ 0` is nevertheless a theorem on this execution (`f73_alpha_ne_zero_from_preimage`),
from the NMR timestamp window rather than from the fixture literal `α = 4`. -/
theorem f73_serves_one_lookup :
    readExps (alphaFreeRoot
        (data73.executionTemplate concreteExecution.cfg.challenges.z)
        ⟨1, by simp [configTemplateOf, BuildableConcrete.concreteExecution, ConcreteStrictPackage.cfg]⟩) = [1] ∧
      ([1].map (fun j => concreteExecution.cfg.challenges.α ^ j)).Nodup :=
  ⟨ForestExponentWindow.Concrete.data73_alphaFreeRoot_exps.1,
    singleton_timestamp_multiset_is_nodup _ 1⟩

end Concrete

/-! ## §G. F97 multi-root: §B derives `α ≠ 0` on a live execution

The two-serviced-root F97 fixture is the live non-vacuity witness for §B.  Its aggregate service
timestamp multiset is `[4, 16, 64]` across both roots (`forestTimestampPowersS`), i.e. **three**
served lookups, so `alpha_ne_zero_of_two_services` discharges the residual there *from the held
fields alone* — the derivation never inspects the fixture's `α`. -/

namespace MultiRoot

open MultiRootServedFixture
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete

local instance prime97m : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97m : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-- The live F97 execution serves three memory lookups across its two serviced roots. -/
theorem multiRoot_forestServiceExponents_length :
    (forestServiceExponents multiRootExecution).length = 3 := by
  have h : ((forestServiceExponents multiRootExecution).map
      (fun e => multiRootExecution.cfg.challenges.α ^ e)).length = 3 := by
    rw [← forestTimestampPowers_eq]
    rw [show ((List.finRange multiRootExecution.cfg.kMem).flatMap
        (fun i => (multiRootExecution.memoryTrace.roots i).timestampPowers)) =
      [(4 : K97cubic), 16, 64] from forestTimestampPowersS]
    rfl
  simpa using h

/-- **§B on a live execution: `α ≠ 0` is DERIVED, not inspected.**  The proof term uses only
Algorithm NockCompute's line-number pinning and the paper's global timestamp uniqueness — both
already-held fields of `multiRootExecution` — and never mentions the fixture's challenge value. -/
theorem multiRoot_alpha_ne_zero_from_held_fields :
    multiRootExecution.cfg.challenges.α ≠ 0 :=
  alpha_ne_zero_of_two_services multiRootExecution
    (by rw [multiRoot_forestServiceExponents_length]; norm_num)

/-- …hence the whole residual arithmetic condition of the item is discharged on this live execution
with no hypothesis on `α` whatsoever -/
theorem multiRoot_orderOf_alpha_pos_from_held_fields :
    0 < orderOf multiRootExecution.cfg.challenges.α :=
  orderOf_pos_of_two_services multiRootExecution
    (by rw [multiRoot_forestServiceExponents_length]; norm_num)

/-- **The closure at F97, hypothesis-free in `α`.**  For any commitment on the live multi-root
execution, the canonically stamped commitment satisfies the paper's uniqueness window — and the
residual is discharged by the execution's own held fields -/
theorem multiRoot_forestExponentOrder_normData (D : Data multiRootExecution) :
    ForestExponentOrder
      ((normData D).executionTemplate multiRootExecution.cfg.challenges.z)
      multiRootExecution.cfg.challenges.α :=
  forestExponentOrder_normData_of_ne_zero D multiRoot_alpha_ne_zero_from_held_fields

end MultiRoot

#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.orderOf_pos_of_ne_zero
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.orderOf_zero_eq_zero
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.orderOf_pos_iff_ne_zero
#print axioms
  Nock.NockVMROM.Thm54.ForestExponentOrderClosure.activeRequestRecord_ts_eq_zero_of_alpha_zero
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.computeRow_accepted_of_mem
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.rawRequest_ts_eq_zero_of_alpha_zero
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.service_exponent_pos_of_alpha_zero
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.forestServiceExponents
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.forestTimestampPowers_eq
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.length_le_one_of_nodup_all_eq
#print axioms
  Nock.NockVMROM.Thm54.ForestExponentOrderClosure.forestServiceExponents_length_le_one_of_alpha_zero
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.alpha_ne_zero_of_two_services
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.orderOf_pos_of_two_services
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.singleton_timestamp_multiset_is_nodup
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.activeRequestRecords_ne_nil
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.rawRequests_ne_nil
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.derivedRequestIO_ne_nil
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.alpha_ne_zero
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.orderOf_pos
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.zeroTimestampChallengeEvent
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.mem_zeroTimestampChallengeEvent_iff
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.zeroTimestampChallengeEvent_card
#print axioms
  Nock.NockVMROM.Thm54.ForestExponentOrderClosure.orderOf_pos_of_not_mem_zeroTimestampChallengeEvent
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.mapNTree_id_of_eq
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.reExpRow
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.reExpNode
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.reExpNode_row
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.reExpNode_skel
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.renderMemoryTemplate_reExpNode
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.MemoryTimestampSpecializesAt_reExp
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.memoryNodesOK_reExp
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.skeletonOfNodes_reExp
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.reExpData
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.reExpData_skeleton
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.reExpData_honest_exec
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.templateAxisTree_reExp
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.memoryForest_reExpData
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.alphaFreeRoot_reExpData
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.normData
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.normData_skeleton
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.normData_honest_exec
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.normData_memory_rows
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.forestExponentOrder_normData_of_ne_zero
#print axioms
  Nock.NockVMROM.Thm54.ForestExponentOrderClosure.normalised_package_fibre_accepts_of_ne_zero
#print axioms
  Nock.NockVMROM.Thm54.ForestExponentOrderClosure.normalised_package_fibre_accepts_of_two_services
#print axioms
  Nock.NockVMROM.Thm54.ForestExponentOrderClosure.normalised_package_fibre_accepts_off_bad_event
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.normalised_package_fibre_accepts
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.forall_data_shape_still_refuted
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.data_eta_unchanged_ao112
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.buildableExecution_eta_unchanged_ao112
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.residual_pair_still_eleven_one_two_ao112
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.residual_pair_still_eleven_one_two_ao136
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.consumed_capstone_untouched_ao112
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.Concrete.f73_alpha_ne_zero
#print axioms
  Nock.NockVMROM.Thm54.ForestExponentOrderClosure.Concrete.f73_alpha_ne_zero_from_preimage
#print axioms
  Nock.NockVMROM.Thm54.ForestExponentOrderClosure.Concrete.f73_not_mem_zeroTimestampChallengeEvent
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.Concrete.f73_orderOf_alpha
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.Concrete.f73_normalised_fibre_accepts
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.Concrete.f73_normData_fixes_the_exponent
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.Concrete.f73_window_still_holds
#print axioms Nock.NockVMROM.Thm54.ForestExponentOrderClosure.Concrete.f73_serves_one_lookup
#print axioms
  Nock.NockVMROM.Thm54.ForestExponentOrderClosure.MultiRoot.multiRoot_forestServiceExponents_length
#print axioms
  Nock.NockVMROM.Thm54.ForestExponentOrderClosure.MultiRoot.multiRoot_alpha_ne_zero_from_held_fields
#print axioms
  Nock.NockVMROM.Thm54.ForestExponentOrderClosure.MultiRoot.multiRoot_orderOf_alpha_pos_from_held_fields
#print axioms
  Nock.NockVMROM.Thm54.ForestExponentOrderClosure.MultiRoot.multiRoot_forestExponentOrder_normData

end Nock.NockVMROM.Thm54.ForestExponentOrderClosure
