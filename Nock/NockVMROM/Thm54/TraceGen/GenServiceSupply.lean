/-
  Nock/NockVMROM/Thm54/TraceGen/GenServiceSupply.lean

  **`Service cfg exec` at a request produced by the generator.**

  `ServedMemoryTrace.Service` (`ServedMemoryTrace.lean:184`) is the compute-side half of the
  memory partition: an emitted `MemRec`, the `(root, child, axis)` it realizes, the exponent of
  its timestamp, and the Nock fact `slot axis root = some child`.  Every `RootTrace` builder in
  `GenServedRootTrace.lean` takes a `Service` as an *argument* — nothing in the tree constructs
  one at a generated trace, so `ExactServedMemoryTrace.semanticCoverage` has no existential to
  discharge.  This module builds it.

  What was actually missing was **position**, in three separate places, and none of it is
  mathematics:

  * `extractNodeReqsAux_mem` (`GenMatmulMem.lean:1208`) says a memory request came from *some*
    `ServiceReq` of the row.  The exponent it carries is `getRecordExp stamp i` for the request's
    **index** `i`, so membership alone cannot say which timestamp a request has.  §A is the
    index-carrying form: length, `getElem`, and a membership eliminator that names `i`.
  * `requestsMatchMemory` (`GenSemanticLmIO.lean:770`) is a *list* equality
    `requestTriples g = memoryTriples g`, and `memoryTriples_of_count1/2/3`
    (`GenSemanticLmIO.lean:786/793/802`) read it off at literal
    record counts.  §B is the index form: the `k`-th request's triple is the `k`-th skeleton memory
    record's, for any state, with no case split.
  * `Service.request_mem` wants `record ∈ exec.rawRequests`, i.e. membership in a `flatMap` over
    *all* compute rows.  §C reduces that to one row and one active record slot.

  **§D is the served record's timestamp at a generated row; §E is the supply itself.**
  `SemanticTrace.ServedNounLookup` already carries `RealizesMemRec` and
  the recognizer's `ServedLookup`, and `RecognizerCompleteness.servedLookup_iff_slot` turns the
  latter into `Noun.slot` with no side condition, so a `Service` at a lookup needs exactly two new
  facts: the record is emitted (§C) and its timestamp is a power of `α` (§D).

  **Scope.**  Every declaration here is generic in the **field** and in the **axis**: nothing
  carries an `axis = 2` / `axis = 3` hypothesis.  The served-walk theory's axis restriction lives in `GenTierAMemoryTrace.lean` — its `serviceWalk_*` lemmas take
  `haxis : s.axis = 2` / `= 3` — is a property of Tier A's program, and is not reproduced here.
  It is **not** a restriction of `GenServedRootTrace.lean`, whose builders take a free
  `haxis : s.axis = ax`.

  Genericity in the **state** is not uniform, and four declarations are the exceptions: the two
  §C slot-membership lemmas `mr2_mem_activeRequestRecords` (`pub.state =.s0`) and
  `mr3_mem_activeRequestRecords` (`.s9`), and the two §D timestamp lemmas `renderNode_mr2_ts`
  (`.s0`) and `renderNode_mr3_ts` (`.s9`).  That is by design — `servedTuplesOf` reads exactly
  `.s0`'s `mr2` and `.s9`'s `mr3` — but "any state" is false of those four.  §E is generic in the
  **program**: `renderOp0Row` / `renderOp9Row` fix the served record's timestamp at
  `α ^ recordExponent 1` / `α ^ recordExponent 2` for every accepted program.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenServedForest
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticData
import Nock.NockVMROM.Thm54.RecognizerCompleteness

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace

variable {K : Type} [Field K]

/-! ## A. `extractNodeReqsAux`, carrying its index

`extractNodeReqsAux stamp i rs` walks `rs` and stamps the `k`-th entry with
`getRecordExp stamp (i + k)`.  `extractNodeReqsAux_mem` forgets `k`, and with it the exponent.
These three recover it. -/

/-- **The `k`-th extracted request, with its exponent.**  This is the fact
`extractNodeReqsAux_mem` drops: the exponent is `getRecordExp stamp (i + k)`, so it is determined
by the request's *position*, not by its value. -/
theorem extractNodeReqsAux_getElem (stamp : ComputeTimestampRow) (i : ℕ)
    (rs : List (ServiceReq K)) (k : ℕ) (hk : k < rs.length) :
    (extractNodeReqsAux stamp i rs)[k]'
        (by rw [extractNodeReqsAux_length (K := K)]; exact hk) =
      { root := rs[k].root, child := rs[k].child, axis := rs[k].axis,
        recordExp := getRecordExp stamp (i + k) } := by
  induction rs generalizing i k with
  | nil => exact absurd hk (Nat.not_lt_zero k)
  | cons r rs ih =>
      cases k with
      | zero => simp [extractNodeReqsAux]
      | succ k =>
          have hk' : k < rs.length := Nat.lt_of_succ_lt_succ (by rwa [List.length_cons] at hk)
          have hih := ih (i + 1) k hk'
          have hidx : i + 1 + k = i + (k + 1) := by omega
          rw [hidx] at hih
          simpa only [extractNodeReqsAux, List.getElem_cons_succ] using hih

/-- **`extractNodeReqsAux_mem`, strengthened to carry the index.**  Membership in the extracted
list pins the source request *and* its position, hence its committed exponent.  The original
(`GenMatmulMem.lean:1208`) is the `root`/`child`/`axis` projection of this with `k` forgotten. -/
theorem extractNodeReqsAux_mem_index (stamp : ComputeTimestampRow) (i : ℕ)
    (rs : List (ServiceReq K)) (r : MemRecordReq)
    (hr : r ∈ extractNodeReqsAux stamp i rs) :
    ∃ k, ∃ hk : k < rs.length,
      r = { root := rs[k].root, child := rs[k].child, axis := rs[k].axis,
            recordExp := getRecordExp stamp (i + k) } := by
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hr
  have hk' : k < rs.length := by
    rwa [extractNodeReqsAux_length (K := K)] at hk
  exact ⟨k, hk', by rw [← hget, extractNodeReqsAux_getElem stamp i rs k hk']⟩

/-- The row-level form: `extractNodeReqs` starts at index `0`, so the `k`-th memory request of a
row carries the `k`-th record exponent of that row's timestamp. -/
theorem extractNodeReqs_getElem (g : GenComputeRow K) (k : ℕ) (hk : k < g.requests.length) :
    (extractNodeReqs g)[k]'(by rw [extractNodeReqs_length]; exact hk) =
      { root := g.requests[k].root, child := g.requests[k].child,
        axis := g.requests[k].axis, recordExp := getRecordExp g.stamp k } := by
  simpa [extractNodeReqs] using extractNodeReqsAux_getElem g.stamp 0 g.requests k hk


/-! ## B. `memoryTriples`, carrying its index

`memoryTriples_of_count1/2/3` (`GenSemanticLmIO.lean:786/793/802`) read the list off at a *literal*
record count, so every consumer of `requestsMatchMemory` has to case-split on the state first.
`memoryTriples_getElem` is the same content at an arbitrary index and arbitrary state, and
`requests_getElem_triple` is what a `Service` supply actually wants: the `k`-th `ServiceReq` of a
row is the `k`-th memory record of its skeleton. -/

/-- **The `k`-th memory triple is the `k`-th skeleton memory record.**  Index form of
`memoryTriples_of_count1/2/3`, with no case split on the state.  Stated with `getElem?` because a
dependent `getElem` index proof mentions `memoryTriples g` itself, which blocks the rewrite. -/
theorem memoryTriples_getElem? (g : GenComputeRow K) (k : ℕ)
    (hk : k < Nock.Framework.recordCount g.skel.state) (h3 : k < 3) :
    (memoryTriples g)[k]? = some (recTriple (g.skel.memoryRecord ⟨k, h3⟩ hk)) := by
  rcases recordCount_eq_123 g.skel.state with hn | hn | hn
  · rw [memoryTriples_of_count1 g hn]
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  · rw [memoryTriples_of_count2 g hn]
    have hk2 : k < 2 := hn ▸ hk
    interval_cases k <;> rfl
  · rw [memoryTriples_of_count3 g hn]
    have hk3 : k < 3 := hn ▸ hk
    interval_cases k <;> rfl

/-- **The `k`-th service request of a row is the `k`-th memory record of its skeleton.**

`requestsMatchMemory` is a list equality; this is that equality read at one
index, which is the form the memory-forest builder needs — `extractNodeReqs` stamps request `k`
with `getRecordExp stamp k` (§A), so a request and the record it serves must agree slot by slot,
not merely as multisets. -/
theorem requests_getElem_triple (g : GenComputeRow K) (h : requestsMatchMemory g)
    (k : ℕ) (hk : k < g.requests.length) :
    ∃ (h3 : k < 3) (hc : k < Nock.Framework.recordCount g.skel.state),
      g.requests[k].root = (g.skel.memoryRecord ⟨k, h3⟩ hc).root ∧
        g.requests[k].child = (g.skel.memoryRecord ⟨k, h3⟩ hc).child ∧
          g.requests[k].axis = (g.skel.memoryRecord ⟨k, h3⟩ hc).axis := by
  have hlen := requestsMatch_length g h
  have hc : k < Nock.Framework.recordCount g.skel.state := hlen ▸ hk
  have h3 : k < 3 := by
    rcases recordCount_eq_123 g.skel.state with hn | hn | hn <;> omega
  have h1 : (requestTriples g)[k]? =
      some (g.requests[k].root, g.requests[k].child, g.requests[k].axis) := by
    simp [requestTriples, List.getElem?_map, List.getElem?_eq_getElem hk]
  rw [show requestTriples g = memoryTriples g from h,
    memoryTriples_getElem? g k hc h3] at h1
  have heq := (Option.some.inj h1).symm
  exact ⟨h3, hc, congrArg Prod.fst heq, congrArg (fun p => p.2.1) heq,
    congrArg (fun p => p.2.2) heq⟩

/-! ## C. `Service`, supplied at a served lookup

`SemanticTrace.ServedNounLookup` (`SemanticTrace.lean:47`) already carries two of the four
non-trivial `Service` fields: `realization` is literally `RealizesMemRec`, and `served` is the
recognizer's `ServedLookup`, which `RecognizerCompleteness.servedLookup_iff_slot`
(`RecognizerCompleteness.lean:162`) turns into `Noun.slot axis root = some child` with **no side
condition and no restriction on the axis**.

So a `Service` at a lookup needs exactly two new facts, and both are positional rather than
mathematical: the record is one of the row's *emitted* records, and its timestamp is a power of
`α`.

Everything in this section holds at an arbitrary `ExactExecution` — no generator, no fixed axis,
no fixed state beyond the `activeRequestRecords` arity table. -/

/-- OP0 emits `mr1, mr2`; the served slot lookup is the second (`servedTuplesOf`,
`BoundSemanticTrace.lean:298`) -/
theorem mr2_mem_activeRequestRecords (pub : ComputeTable.Pub K) (h : pub.state = .s0) :
    computeMemRec pub 1 ∈ Nock.NockVM.activeRequestRecords pub := by
  simp [Nock.NockVM.activeRequestRecords, h, computeMemRec]

/-- OP9 emits `mr1, mr2, mr3`; the served arm fetch is the third (`servedTuplesOf`,
`BoundSemanticTrace.lean:293`) -/
theorem mr3_mem_activeRequestRecords (pub : ComputeTable.Pub K) (h : pub.state = .s9) :
    computeMemRec pub 2 ∈ Nock.NockVM.activeRequestRecords pub := by
  simp [Nock.NockVM.activeRequestRecords, h, computeMemRec]

section Supply

variable {F : Type} [Field F] [Algebra F K]

/-- Any active request record of any compute row is one of the execution's raw requests.  This is
the whole content of `Service.request_mem`: `rawRequests` is a `flatMap` over every compute row
(`Language.lean:33`), so membership at one row suffices. -/
theorem mem_rawRequests_of_computeRowAt {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : Fin cfg.compRows) (r : ComputeTable.MemRec K)
    (hr : r ∈ Nock.NockVM.activeRequestRecords (exec.computeRowAt i).2.2.1) :
    r ∈ exec.rawRequests := by
  rw [ExactExecution.rawRequests_eq_computeRows]
  refine List.mem_flatMap.mpr ⟨exec.computeRowAt i, ?_, hr⟩
  exact List.get_mem _ _

/-- **`Service` from a served lookup.**  The generic supply: given one OP0/OP9 `ServedNounLookup`
whose record the execution actually emits and whose timestamp is `α ^ e`, this is the
compute-side service `RootTrace` and `ExactServedMemoryTrace.semanticCoverage` ask for.

`served` is discharged through the recognizer completeness equivalence, so **no axis hypothesis
appears** — contrast the served-walk lemmas of `GenTierAMemoryTrace.lean`
(`serviceWalk_recordTree_axis2` / `_axis3`), whose `haxis : s.axis = 2` / `= 3` is a property of
Tier A's program.  `GenServedRootTrace.lean`'s `RootTrace` builders are *not* the
contrast: they take a free `haxis : s.axis = ax` -/
def Service.ofServedLookup {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (l : SemanticTrace.ServedNounLookup cfg.challenges.z) (e : ℕ)
    (hmem : l.record ∈ exec.rawRequests)
    (hts : l.record.ts = cfg.challenges.α ^ e) :
    ServedMemoryTrace.Service cfg exec where
  exponent := e
  record := l.record
  root := l.root
  child := l.child
  axis := l.axis
  request_mem := hmem
  timestamp := hts
  realization := l.realization
  served := (RecognizerCompleteness.servedLookup_iff_slot l.axis l.root l.child).mp l.served

@[simp] theorem Service.ofServedLookup_record {cfg : ExactConfig F K}
    {exec : ExactExecution cfg}
    (l : SemanticTrace.ServedNounLookup cfg.challenges.z) (e : ℕ)
    (hmem : l.record ∈ exec.rawRequests) (hts : l.record.ts = cfg.challenges.α ^ e) :
    (Service.ofServedLookup (exec := exec) l e hmem hts).record = l.record := rfl

@[simp] theorem Service.ofServedLookup_root {cfg : ExactConfig F K}
    {exec : ExactExecution cfg}
    (l : SemanticTrace.ServedNounLookup cfg.challenges.z) (e : ℕ)
    (hmem : l.record ∈ exec.rawRequests) (hts : l.record.ts = cfg.challenges.α ^ e) :
    (Service.ofServedLookup (exec := exec) l e hmem hts).root = l.root := rfl

@[simp] theorem Service.ofServedLookup_child {cfg : ExactConfig F K}
    {exec : ExactExecution cfg}
    (l : SemanticTrace.ServedNounLookup cfg.challenges.z) (e : ℕ)
    (hmem : l.record ∈ exec.rawRequests) (hts : l.record.ts = cfg.challenges.α ^ e) :
    (Service.ofServedLookup (exec := exec) l e hmem hts).child = l.child := rfl

@[simp] theorem Service.ofServedLookup_axis {cfg : ExactConfig F K}
    {exec : ExactExecution cfg}
    (l : SemanticTrace.ServedNounLookup cfg.challenges.z) (e : ℕ)
    (hmem : l.record ∈ exec.rawRequests) (hts : l.record.ts = cfg.challenges.α ^ e) :
    (Service.ofServedLookup (exec := exec) l e hmem hts).axis = l.axis := rfl

@[simp] theorem Service.ofServedLookup_exponent {cfg : ExactConfig F K}
    {exec : ExactExecution cfg}
    (l : SemanticTrace.ServedNounLookup cfg.challenges.z) (e : ℕ)
    (hmem : l.record ∈ exec.rawRequests) (hts : l.record.ts = cfg.challenges.α ^ e) :
    (Service.ofServedLookup (exec := exec) l e hmem hts).exponent = e := rfl

end Supply

/-! ## D. The served record's timestamp at a generated row

`renderNode` (`Gen.lean:2884`) dispatches on `g.skel.state`, and the OP0/OP9 renderers commit the
served record's timestamp as a fixed power of `α`: `renderOp0Row` puts `α ^ recordExponent 1` in
`mr2` (`Gen.lean:2802`) and `renderOp9Row` puts `α ^ recordExponent 2` in `mr3`
(`Gen.lean:2837`) — the same two slots `servedTuplesOf` reads.  Neither depends on the program.

`setRowCoins` rewrites only the input coins (`GenWF.lean:45`), so it leaves every record alone. -/

/-- The OP0 served record is timestamped `α ^ recordExponent 1` -/
theorem renderNode_mr2_ts (z α : K) (g : GenComputeRow K) (h : g.skel.state = .s0) :
    (computeMemRec (renderNode z α g).row.2.2.1 1).ts = α ^ g.stamp.recordExponent 1 := by
  unfold renderNode
  rw [h]
  rfl

/-- The OP9 served arm fetch is timestamped `α ^ recordExponent 2`. -/
theorem renderNode_mr3_ts (z α : K) (g : GenComputeRow K) (h : g.skel.state = .s9) :
    (computeMemRec (renderNode z α g).row.2.2.1 2).ts = α ^ g.stamp.recordExponent 2 := by
  unfold renderNode
  rw [h]
  rfl

section Generated

variable {F : Type} [Field F] [Algebra F K]

/-- Every compute row of a generated execution is a rendered BFS node with the coins overwritten.
This is the step `genComputeRowsAccepted` (`GenSemanticDataParts.lean:213`) takes inline; naming it
lets a service supply reach the row's `stamp`. -/
theorem exists_renderNode_of_mem_computeRows (z α : K) (a b c : K)
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (row : ComputeTable.State × ComputeTable.DTcomp K)
    (hrow : row ∈ (genExactExecutionA (F := F) chal Ksz orbit horb a b c
      (genComputeRows z α t) mf hmempos hcomp hmem).computeRows) :
    ∃ g ∈ bfsRows (bfsAssign (airReorder t)),
      row = setRowCoins a b c (renderNode z α g).row := by
  rw [genExactExecutionA_computeRows chal Ksz orbit horb a b c] at hrow
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hrow
  rw [genComputeRows, bfsRows_renderRows] at hg
  obtain ⟨gl, hgl, rfl⟩ := List.mem_map.mp hg
  exact ⟨gl, hgl, rfl⟩

/-- **The served record of any OP0 row of a generated execution is a power of `α`.** -/
theorem gen_s0_served_ts (z α : K) (a b c : K)
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (row : ComputeTable.State × ComputeTable.DTcomp K)
    (hrow : row ∈ (genExactExecutionA (F := F) chal Ksz orbit horb a b c
      (genComputeRows z α t) mf hmempos hcomp hmem).computeRows)
    (hst : row.2.2.1.state = .s0) :
    ∃ e, (computeMemRec row.2.2.1 1).ts = α ^ e := by
  obtain ⟨g, _, rfl⟩ := exists_renderNode_of_mem_computeRows (F := F) z α a b c chal Ksz orbit
    horb t mf hmempos hcomp hmem row hrow
  refine ⟨g.stamp.recordExponent 1, ?_⟩
  have hskel : g.skel.state = .s0 := by
    rw [← renderNode_pub_state z α g]
    exact hst
  simpa using renderNode_mr2_ts z α g hskel

/-- **The served arm fetch of any OP9 row of a generated execution is a power of `α`.** -/
theorem gen_s9_served_ts (z α : K) (a b c : K)
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (row : ComputeTable.State × ComputeTable.DTcomp K)
    (hrow : row ∈ (genExactExecutionA (F := F) chal Ksz orbit horb a b c
      (genComputeRows z α t) mf hmempos hcomp hmem).computeRows)
    (hst : row.2.2.1.state = .s9) :
    ∃ e, (computeMemRec row.2.2.1 2).ts = α ^ e := by
  obtain ⟨g, _, rfl⟩ := exists_renderNode_of_mem_computeRows (F := F) z α a b c chal Ksz orbit
    horb t mf hmempos hcomp hmem row hrow
  refine ⟨g.stamp.recordExponent 2, ?_⟩
  have hskel : g.skel.state = .s9 := by
    rw [← renderNode_pub_state z α g]
    exact hst
  simpa using renderNode_mr3_ts z α g hskel

end Generated

/-! ## E. The supply, assembled

The two capstones.  Given one served lookup of a generated execution whose record is the row's
OP0 `mr2` or OP9 `mr3` — which is exactly what `BoundSemanticTrace.servedTuplesOf`
(`BoundSemanticTrace.lean:291`) says a row's served lookups are — there **is** a `Service` over
it, agreeing with the lookup on all four coordinates `semanticCoverage` compares.

`hα` is `chal.α = α`: the compiler's own choice of timestamp challenge, already fixed by
`genSemanticData`'s `hinp : chal.computeInputs = ⟨α, z, a, b, c⟩` (`GenSemanticData.lean:120`).
No hypothesis restricts the axis, the state beyond `{OP0, OP9}`, the field, or the program. -/

section Assembled

variable {F : Type} [Field F] [Algebra F K]

/-- **`Service` at an OP0 served lookup of a generated execution.** -/
theorem exists_service_of_gen_s0_lookup (z α : K) (a b c : K)
    (chal : ChallengeVector K) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (row : ComputeTable.State × ComputeTable.DTcomp K)
    (hrow : row ∈ (genExactExecutionA (F := F) chal Ksz orbit horb a b c
      (genComputeRows z α t) mf hmempos hcomp hmem).computeRows)
    (hst : row.2.2.1.state = .s0)
    (l : SemanticTrace.ServedNounLookup
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
        hmempos hcomp hmem).challenges.z)
    (hrec : l.record = computeMemRec row.2.2.1 1) :
    ∃ s : ServedMemoryTrace.Service
        (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
          hmempos hcomp hmem)
        (genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
          hmempos hcomp hmem),
      s.record = l.record ∧ s.root = l.root ∧ s.child = l.child ∧ s.axis = l.axis := by
  obtain ⟨e, he⟩ := gen_s0_served_ts (F := F) z α a b c chal Ksz orbit horb t mf
    hmempos hcomp hmem row hrow hst
  have hmem' : l.record ∈ (genExactExecutionA (F := F) chal Ksz orbit horb a b c
      (genComputeRows z α t) mf hmempos hcomp hmem).rawRequests := by
    rw [ExactExecution.rawRequests_eq_computeRows]
    exact List.mem_flatMap.mpr ⟨row, hrow, by rw [hrec]; exact mr2_mem_activeRequestRecords _ hst⟩
  have hts : l.record.ts =
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
        hmempos hcomp hmem).challenges.α ^ e := by
    rw [hrec, he]
    exact congrArg (· ^ e) hα.symm
  exact ⟨Service.ofServedLookup l e hmem' hts, rfl, rfl, rfl, rfl⟩

/-- **`Service` at an OP9 served lookup of a generated execution.** -/
theorem exists_service_of_gen_s9_lookup (z α : K) (a b c : K)
    (chal : ChallengeVector K) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (row : ComputeTable.State × ComputeTable.DTcomp K)
    (hrow : row ∈ (genExactExecutionA (F := F) chal Ksz orbit horb a b c
      (genComputeRows z α t) mf hmempos hcomp hmem).computeRows)
    (hst : row.2.2.1.state = .s9)
    (l : SemanticTrace.ServedNounLookup
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
        hmempos hcomp hmem).challenges.z)
    (hrec : l.record = computeMemRec row.2.2.1 2) :
    ∃ s : ServedMemoryTrace.Service
        (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
          hmempos hcomp hmem)
        (genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
          hmempos hcomp hmem),
      s.record = l.record ∧ s.root = l.root ∧ s.child = l.child ∧ s.axis = l.axis := by
  obtain ⟨e, he⟩ := gen_s9_served_ts (F := F) z α a b c chal Ksz orbit horb t mf
    hmempos hcomp hmem row hrow hst
  have hmem' : l.record ∈ (genExactExecutionA (F := F) chal Ksz orbit horb a b c
      (genComputeRows z α t) mf hmempos hcomp hmem).rawRequests := by
    rw [ExactExecution.rawRequests_eq_computeRows]
    exact List.mem_flatMap.mpr ⟨row, hrow, by rw [hrec]; exact mr3_mem_activeRequestRecords _ hst⟩
  have hts : l.record.ts =
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
        hmempos hcomp hmem).challenges.α ^ e := by
    rw [hrec, he]
    exact congrArg (· ^ e) hα.symm
  exact ⟨Service.ofServedLookup l e hmem' hts, rfl, rfl, rfl, rfl⟩

end Assembled

/-! ## F. The interface to `semanticCoverage`

`ExactServedMemoryTrace.semanticCoverage` (`ServedMemoryTrace.lean:616`) quantifies over
`(D.rows row).needs.served`, and what a caller can say about those lookups is
`BoundSemanticTrace.servedTuplesOf` — `buildCoveredRow`'s second component (`:320`).  This is §E
keyed on that membership instead of on a named record slot, so a consumer needs only the tuple
fact and never has to case-split on the state itself.

`hst` is `BindComputeRow`'s `hpubState` (`SemanticStrategy`), which every binding already carries. -/

section Interface

variable {F : Type} [Field F] [Algebra F K]

/-- **`Service` at any served tuple of a generated row.**  The OP0/OP9 case split is done here, so
`semanticCoverage` sees one theorem -/
theorem exists_service_of_servedTuple (z α : K) (a b c : K)
    (chal : ChallengeVector K) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (row : ComputeTable.State × ComputeTable.DTcomp K)
    (hrow : row ∈ (genExactExecutionA (F := F) chal Ksz orbit horb a b c
      (genComputeRows z α t) mf hmempos hcomp hmem).computeRows)
    (skel : BoundSemanticTrace.RowSkeleton)
    (hst : row.2.2.1.state = skel.state)
    (l : SemanticTrace.ServedNounLookup
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
        hmempos hcomp hmem).challenges.z)
    (htuple : (l.record, l.root, l.axis, l.child) ∈
      BoundSemanticTrace.servedTuplesOf (K := K) skel row.2.2.1) :
    ∃ s : ServedMemoryTrace.Service
        (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
          hmempos hcomp hmem)
        (genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
          hmempos hcomp hmem),
      s.record = l.record ∧ s.root = l.root ∧ s.child = l.child ∧ s.axis = l.axis := by
  unfold BoundSemanticTrace.servedTuplesOf at htuple
  by_cases h9 : skel.state = .s9
  · rw [if_pos h9] at htuple
    have hrec : l.record = computeMemRec row.2.2.1 2 :=
      congrArg Prod.fst (List.mem_singleton.mp htuple)
    exact exists_service_of_gen_s9_lookup (F := F) z α a b c chal hα Ksz orbit horb t mf
      hmempos hcomp hmem row hrow (hst.trans h9) l hrec
  · rw [if_neg h9] at htuple
    by_cases h0 : skel.state = .s0
    · rw [if_pos h0] at htuple
      have hrec : l.record = computeMemRec row.2.2.1 1 :=
        congrArg Prod.fst (List.mem_singleton.mp htuple)
      exact exists_service_of_gen_s0_lookup (F := F) z α a b c chal hα Ksz orbit horb t mf
        hmempos hcomp hmem row hrow (hst.trans h0) l hrec
    · rw [if_neg h0] at htuple
      exact absurd htuple (List.not_mem_nil)

end Interface

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.extractNodeReqsAux_getElem
#print axioms Nock.NockVMROM.Thm54.TraceGen.extractNodeReqsAux_mem_index
#print axioms Nock.NockVMROM.Thm54.TraceGen.extractNodeReqs_getElem
#print axioms Nock.NockVMROM.Thm54.TraceGen.memoryTriples_getElem?
#print axioms Nock.NockVMROM.Thm54.TraceGen.requests_getElem_triple
#print axioms Nock.NockVMROM.Thm54.TraceGen.mem_rawRequests_of_computeRowAt
#print axioms Nock.NockVMROM.Thm54.TraceGen.mr2_mem_activeRequestRecords
#print axioms Nock.NockVMROM.Thm54.TraceGen.mr3_mem_activeRequestRecords
#print axioms Nock.NockVMROM.Thm54.TraceGen.Service.ofServedLookup
#print axioms Nock.NockVMROM.Thm54.TraceGen.renderNode_mr2_ts
#print axioms Nock.NockVMROM.Thm54.TraceGen.renderNode_mr3_ts
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_renderNode_of_mem_computeRows
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_s0_served_ts
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_s9_served_ts
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_service_of_gen_s0_lookup
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_service_of_gen_s9_lookup
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_service_of_servedTuple
