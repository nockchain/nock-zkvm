/-
  Nock/NockVMROM/Thm54/TraceGen/GenServedRoots.lean

  **The join: `roots` for the generated carrier.**

  `ExactServedMemoryTrace`'s other three fields all bottom out on
  `roots : ∀ i : Fin cfg.kMem, RootTrace cfg exec i`, and the two builders that produce a
  `RootTrace` — `rootTraceOfRecordTree` and `rootTraceOfChainedPair` (`GenServedRootTrace.lean`) —
  each want a `Service` per *memory-record request* of the forest root's originating compute node.

  That is what `semanticCoverage` needs and it is not what
  `roots` needs: a forest root is built from *any* active record of *any* row, so the supply has to
  be keyed on `MemRecordReq` and cover `mr1`/`mr2`/`mr3` at all eleven states. This section is that
  generalisation.

  **Nothing here is new mathematics** and the pieces were all located in `ET` §3:

  * `BindMemRec` **is** `RealizesMemRec` up to argument order — `bindFP z n fp` is `fp = enc z n`
    (`SemanticStrategy.lean:129`) and `Realizes z fp n` is `fp = enc z n`
    (`OpcodeSemantics.lean:53`).  `realizesMemRec_of_bindMemRec` below is that transposition.
  * `Service.served` needs no axis hypothesis.
  * `request_mem` is membership of `computeMemRec pub k` in `activeRequestRecords pub`, which is the
    arity table (`NockVM.lean:622`) read against `recordCount` (`NockInstances.lean:61`).
  * the timestamp is `renderNode_active_timestamps` (`GenGenericRowFacts.lean`, relocated there by `FP`), already generic
    across all eleven states — despite living in a fixture-named file.

  **Scope.** §A is at an arbitrary `ExactExecution`: no generator, no fixed axis, no fixed state
  beyond the arity table, no fixed field.

  -- the paper
-/
import Nock.NockVMROM.Thm54.TraceGen.GenServiceSupply
import Nock.NockVMROM.Thm54.TraceGen.GenMemForestOrder
import Nock.NockVMROM.Thm54.TraceGen.GenBalance

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.Framework.Thm54

variable {K : Type} [Field K]

-- Form R `λ` of the generated memory rows (the configuration's `λ`; 28th λ-fix).
variable {lmb : K}

/-! ## A. `Service` at an arbitrary memory-record request

The `EV` supply is keyed on a `ServedNounLookup`, which exists only at `.s0`/`.s9`.  A forest root
is built from any active record of any row, so the key here is the record slot itself. -/

/-- **`RealizesMemRec` from `BindMemRec`.**  Argument transposition: both sides are
`fp = enc z n` on the root and child coordinates plus the same axis equation. -/
theorem realizesMemRec_of_bindMemRec {z : K} {s : MemRecSkeleton}
    {r : ComputeTable.MemRec K} (h : BindMemRec z s r) :
    OpcodeSemantics.RealizesMemRec z r s.root s.child s.axis where
  root_realizes := h.1
  child_realizes := h.2.1
  axis_realizes := h.2.2

/-- **Every active record slot is an emitted request.**  The arity table
(`activeRequestRecords`, `NockVM.lean:622`) agrees with `recordCount`
(`NockInstances.lean:61`) state by state; this is that agreement read as membership. -/
theorem computeMemRec_mem_activeRequestRecords (pub : ComputeTable.Pub K) (k : Fin 3)
    (hk : (k : ℕ) < Nock.Framework.recordCount pub.state) :
    computeMemRec pub k ∈ Nock.NockVM.activeRequestRecords pub := by
  rw [Nock.NockVM.activeRequestRecords]
  revert hk
  cases hs : pub.state <;> simp only [Nock.Framework.recordCount] <;> intro hk <;>
    fin_cases k <;>
      simp_all [computeMemRec]

section Supply

variable {F : Type} [Field F] [Algebra F K]

/-- **`Service` at a memory-record request.**

The generalisation of `Service.ofServedLookup` (`EV`) from the two served slots to every active
record slot of every state. **No axis hypothesis appears** — but by a different mechanism than
`EV`'s: that route discharges `served` through `RecognizerCompleteness.servedLookup_iff_slot`, while
this one takes `hslot` and sets `served := hslot` directly. -/
def Service.ofMemRecordReq {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (r : MemRecordReq) (rec : ComputeTable.MemRec K) (e : ℕ)
    (hreal : OpcodeSemantics.RealizesMemRec cfg.challenges.z rec r.root r.child r.axis)
    (hmem : rec ∈ exec.rawRequests)
    (hts : rec.ts = cfg.challenges.α ^ e)
    (hslot : Noun.slot r.axis r.root = some r.child) :
    ServedMemoryTrace.Service cfg exec where
  exponent := e
  record := rec
  root := r.root
  child := r.child
  axis := r.axis
  request_mem := hmem
  timestamp := hts
  realization := hreal
  served := hslot

@[simp] theorem Service.ofMemRecordReq_record {cfg : ExactConfig F K}
    {exec : ExactExecution cfg} (r : MemRecordReq) (rec : ComputeTable.MemRec K) (e : ℕ)
    (hreal : OpcodeSemantics.RealizesMemRec cfg.challenges.z rec r.root r.child r.axis)
    (hmem : rec ∈ exec.rawRequests) (hts : rec.ts = cfg.challenges.α ^ e)
    (hslot : Noun.slot r.axis r.root = some r.child) :
    (Service.ofMemRecordReq (exec := exec) r rec e hreal hmem hts hslot).record = rec := rfl

@[simp] theorem Service.ofMemRecordReq_root {cfg : ExactConfig F K}
    {exec : ExactExecution cfg} (r : MemRecordReq) (rec : ComputeTable.MemRec K) (e : ℕ)
    (hreal : OpcodeSemantics.RealizesMemRec cfg.challenges.z rec r.root r.child r.axis)
    (hmem : rec ∈ exec.rawRequests) (hts : rec.ts = cfg.challenges.α ^ e)
    (hslot : Noun.slot r.axis r.root = some r.child) :
    (Service.ofMemRecordReq (exec := exec) r rec e hreal hmem hts hslot).root = r.root := rfl

@[simp] theorem Service.ofMemRecordReq_child {cfg : ExactConfig F K}
    {exec : ExactExecution cfg} (r : MemRecordReq) (rec : ComputeTable.MemRec K) (e : ℕ)
    (hreal : OpcodeSemantics.RealizesMemRec cfg.challenges.z rec r.root r.child r.axis)
    (hmem : rec ∈ exec.rawRequests) (hts : rec.ts = cfg.challenges.α ^ e)
    (hslot : Noun.slot r.axis r.root = some r.child) :
    (Service.ofMemRecordReq (exec := exec) r rec e hreal hmem hts hslot).child = r.child := rfl

@[simp] theorem Service.ofMemRecordReq_axis {cfg : ExactConfig F K}
    {exec : ExactExecution cfg} (r : MemRecordReq) (rec : ComputeTable.MemRec K) (e : ℕ)
    (hreal : OpcodeSemantics.RealizesMemRec cfg.challenges.z rec r.root r.child r.axis)
    (hmem : rec ∈ exec.rawRequests) (hts : rec.ts = cfg.challenges.α ^ e)
    (hslot : Noun.slot r.axis r.root = some r.child) :
    (Service.ofMemRecordReq (exec := exec) r rec e hreal hmem hts hslot).axis = r.axis := rfl

@[simp] theorem Service.ofMemRecordReq_exponent {cfg : ExactConfig F K}
    {exec : ExactExecution cfg} (r : MemRecordReq) (rec : ComputeTable.MemRec K) (e : ℕ)
    (hreal : OpcodeSemantics.RealizesMemRec cfg.challenges.z rec r.root r.child r.axis)
    (hmem : rec ∈ exec.rawRequests) (hts : rec.ts = cfg.challenges.α ^ e)
    (hslot : Noun.slot r.axis r.root = some r.child) :
    (Service.ofMemRecordReq (exec := exec) r rec e hreal hmem hts hslot).exponent
      = e := rfl

end Supply

/-! ## B.1 Plumbing: from a node of the generated tree to an emitted request

Three small transports.  `mem_computeRows_of_bfsRows` is the easy direction of the equation
`exists_renderNode_of_mem_computeRows` (`EV` §D) reads backwards;
`mem_rawRequests_of_mem_computeRows` is the list-membership form of `EV`'s
`mem_rawRequests_of_computeRowAt`; and `computeMemRec_eq_getElem` is the arity table read as an
index rather than as membership, which is what lets `renderNode_active_timestamps` — a list
equality — be read at one slot. -/

/-- The arity table as a length. -/
theorem activeRequestRecords_length_eq (pub : ComputeTable.Pub K) :
    (Nock.NockVM.activeRequestRecords pub).length
      = Nock.Framework.recordCount pub.state := by
  cases hs : pub.state <;>
    simp [Nock.NockVM.activeRequestRecords, hs, Nock.Framework.recordCount]

/-- The `k`-th active request record is the `k`-th record slot. -/
theorem computeMemRec_eq_getElem (pub : ComputeTable.Pub K) (k : Fin 3)
    (hk' : (k : ℕ) < (Nock.NockVM.activeRequestRecords pub).length) :
    (Nock.NockVM.activeRequestRecords pub)[(k : ℕ)] = computeMemRec pub k := by
  rw [activeRequestRecords_length_eq] at hk'
  cases hs : pub.state <;> rw [hs] at hk' <;>
    simp only [Nock.Framework.recordCount] at hk' <;>
    fin_cases k <;> simp_all [Nock.NockVM.activeRequestRecords, computeMemRec]

/-- **The `k`-th record of a rendered row carries the `k`-th committed exponent.**

`renderNode_active_timestamps` (`GenGenericRowFacts.lean`, relocated by `FP`) is the list equality across all eleven
states; this is it read at one slot, which is the form a `Service`'s `timestamp` field wants. -/
theorem renderNode_computeMemRec_ts (z α : K) (g : GenComputeRow K) (k : Fin 3)
    (hk : (k : ℕ) < Nock.Framework.recordCount g.skel.state) :
    (computeMemRec (renderNode z α g).row.2.2.1 k).ts = α ^ getRecordExp g.stamp (k : ℕ) := by
  have hst : (renderNode z α g).row.2.2.1.state = g.skel.state :=
    (renderNode_state_agree z α g).symm.trans (renderNode_state z α g)
  have hlen : (Nock.NockVM.activeRequestRecords (renderNode z α g).row.2.2.1).length
      = Nock.Framework.recordCount g.skel.state := by
    rw [activeRequestRecords_length_eq, hst]
  have hk1 : (k : ℕ) < ((Nock.NockVM.activeRequestRecords
      (renderNode z α g).row.2.2.1).map (fun r => r.ts)).length := by
    rw [List.length_map, hlen]; exact hk
  have hk0 : (k : ℕ) < (Nock.NockVM.activeRequestRecords
      (renderNode z α g).row.2.2.1).length := by rw [hlen]; exact hk
  have heq := List.getElem_of_eq (renderNode_active_timestamps z α g) hk1
  rw [List.getElem_map, List.getElem_map, List.getElem_range] at heq
  rw [← heq, computeMemRec_eq_getElem _ k hk0]

section Gen

variable {F : Type} [Field F] [Algebra F K]

/-- The easy direction: a node of the assigned tree renders to a row of the execution. -/
theorem mem_computeRows_of_bfsRows (z α : K) (a b c : K)
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    {g : GenComputeRow K} (hg : g ∈ bfsRows (bfsAssign (airReorder t))) :
    setRowCoins a b c (renderNode z α g).row ∈
      (genExactExecutionA (F := F) chal Ksz orbit horb a b c
        (genComputeRows z α t) mf hmempos hcomp hmem).computeRows := by
  rw [genExactExecutionA_computeRows chal Ksz orbit horb a b c]
  refine List.mem_map.mpr ⟨renderNode z α g, ?_, rfl⟩
  rw [genComputeRows, bfsRows_renderRows]
  exact List.mem_map.mpr ⟨g, hg, rfl⟩

/-- List-membership form of `EV`'s `mem_rawRequests_of_computeRowAt`. -/
theorem mem_rawRequests_of_mem_computeRows {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    {row : ComputeTable.State × ComputeTable.DTcomp K} (hrow : row ∈ exec.computeRows)
    {r : ComputeTable.MemRec K}
    (hr : r ∈ Nock.NockVM.activeRequestRecords row.2.2.1) :
    r ∈ exec.rawRequests := by
  rw [ExactExecution.rawRequests_eq_computeRows]
  exact List.mem_flatMap.mpr ⟨row, hrow, hr⟩

/-! ## B.2 The supply, at a memory-record request of a generated node

The `roots` builders want, for one `MemRecordReq r` of the compute node a forest root came from, a
`Service` whose record is *exactly* `⟨E r.root, E r.child, r.axis, α ^ r.recordExp⟩` with
`E = encC z`.  Five facts combine, and `ET` §3 located every one of them:

* the request's own fields, at an index (`EV` §A: `extractNodeReqsAux_mem_index`);
* `requestsMatchMemory` read at that index (`EV` §B: `requests_getElem_triple`), which identifies
  the request's `root`/`child`/`axis` with the skeleton's `k`-th memory record;
* `BindComputeRow`'s memory component, from `ComputeNodesOK` at the rendered node, which realizes
  that record's coordinates as `enc z` of those nouns — and `encC_eq` (`Encode.lean:63`) makes `enc`
  and `encC` the same function;
* the timestamp, §B.1's `renderNode_computeMemRec_ts`;
* membership in `rawRequests`, §A's arity-table lemma plus §B.1's two transports. -/

/-- **`Service` at any memory-record request of any node of a generated trace.**

The `roots`-facing supply, and the generalisation of `EV`'s served-lookup supply from `.s0`'s `mr2`
and `.s9`'s `mr3` to every active record slot at every state.  `hslot` is the caller's, because
`RequestWF` supplies it per request (`ET` §1) and threading it through here would duplicate that
induction. -- the paper -/
theorem exists_service_of_memRecordReq (z α : K) (a b c : K)
    (chal : ChallengeVector K) (hz : chal.z = z) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    {u : NTree (GenComputeRow K)} (hu : InTree (bfsAssign (airReorder t)) u)
    {r : MemRecordReq} (hr : r ∈ extractNodeReqs u.label)
    (hslot : Noun.slot r.axis r.root = some r.child) :
    ∃ s : ServedMemoryTrace.Service
        (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
          hmempos hcomp hmem)
        (genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
          hmempos hcomp hmem),
      s.root = r.root ∧ s.child = r.child ∧ s.axis = r.axis ∧
        s.exponent = timestampExp chal.α (chal.α ^ r.recordExp) ∧
        s.record = ⟨encC z r.root, encC z r.child, (r.axis : K), chal.α ^ r.recordExp⟩ := by
  -- the request, at an index of the row's own request list
  obtain ⟨k, hk, hrk⟩ :=
    extractNodeReqsAux_mem_index u.label.stamp 0 u.label.requests r hr
  -- the serving identity at that index
  have hmatch : requestsMatchMemory u.label :=
    genComputeSkeleton_air_requestsMatch h u hu
  obtain ⟨h3, hc, hroot, hchild, haxis⟩ := requests_getElem_triple u.label hmatch k hk
  -- the rendered node's local validity
  have hOK := genComputeSkeleton_airReorder_computeNodes_OK (p := (t, result)) z α h
  have hnode : InTree (mapNTree GenComputeRow.node
      (renderRows z α (bfsAssign (airReorder t))))
      (mapNTree GenComputeRow.node (mapNTree (renderNode z α) u)) := by
    rw [renderRows_eq_mapNTree]
    exact mapNTree_inTree _ (mapNTree_inTree _ hu)
  obtain ⟨-, -, hbind, -⟩ := hOK _ hnode
  rw [mapNTree_label, mapNTree_label] at hbind
  simp only [GenComputeRow.node_skel, GenComputeRow.node_row, renderNode_op1_skel] at hbind
  -- BindComputeRow's memory component at slot k
  have hmr := hbind.2.2.2.2.2.2.2.2 ⟨k, h3⟩
  rw [dif_pos hc] at hmr
  have hreal := realizesMemRec_of_bindMemRec hmr
  have hr1 : (computeMemRec (renderNode z α u.label).row.2.2.1 ⟨k, h3⟩).root
      = GlobalCarryRecognizer.enc z (u.label.skel.memoryRecord ⟨k, h3⟩ hc).root :=
    hreal.root_realizes
  have hr2 : (computeMemRec (renderNode z α u.label).row.2.2.1 ⟨k, h3⟩).child
      = GlobalCarryRecognizer.enc z (u.label.skel.memoryRecord ⟨k, h3⟩ hc).child :=
    hreal.child_realizes
  have hr3 : (computeMemRec (renderNode z α u.label).row.2.2.1 ⟨k, h3⟩).axis
      = ((u.label.skel.memoryRecord ⟨k, h3⟩ hc).axis : K) :=
    hreal.axis_realizes
  -- the timestamp at slot k
  have hts : (computeMemRec (renderNode z α u.label).row.2.2.1 ⟨k, h3⟩).ts
      = α ^ getRecordExp u.label.stamp k := by
    have := renderNode_computeMemRec_ts z α u.label ⟨k, h3⟩ hc
    simpa using this
  -- the record is emitted
  have hrowmem := mem_computeRows_of_bfsRows (F := F) z α a b c chal Ksz orbit horb t mf
    hmempos hcomp hmem (g := u.label)
    (List.mem_map.mpr ⟨u, (mem_bfsForest _ u).mpr
      ⟨_, List.mem_singleton_self _, hu⟩, rfl⟩)
  have hreqmem : computeMemRec (renderNode z α u.label).row.2.2.1 ⟨k, h3⟩ ∈
      (genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
        hmempos hcomp hmem).rawRequests := by
    refine mem_rawRequests_of_mem_computeRows _ hrowmem ?_
    rw [setRowCoins_pub]
    refine computeMemRec_mem_activeRequestRecords _ ⟨k, h3⟩ ?_
    rw [show (renderNode z α u.label).row.2.2.1.state = u.label.skel.state from
      (renderNode_state_agree z α u.label).symm.trans (renderNode_state z α u.label)]
    exact hc
  -- `r`'s own fields, from the index equation
  have hrroot : r.root = (u.label.skel.memoryRecord ⟨k, h3⟩ hc).root := by
    simp only [hrk]; exact hroot
  have hrchild : r.child = (u.label.skel.memoryRecord ⟨k, h3⟩ hc).child := by
    simp only [hrk]; exact hchild
  have hraxis : r.axis = (u.label.skel.memoryRecord ⟨k, h3⟩ hc).axis := by
    simp only [hrk]; exact haxis
  have hrexp : r.recordExp = getRecordExp u.label.stamp k := by
    simp only [hrk, Nat.zero_add]
  -- assemble; every obligation is discharged before the term is built, so that no proof
  -- metavariable ends up inside a rewrite motive
  have hz' : (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
      hmempos hcomp hmem).challenges.z = z := by rw [genExactConfig]; exact hz
  have hα' : (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
      hmempos hcomp hmem).challenges.α = α := by rw [genExactConfig]; exact hα
  have hrealr : OpcodeSemantics.RealizesMemRec
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
        hmempos hcomp hmem).challenges.z
      (computeMemRec (renderNode z α u.label).row.2.2.1 ⟨k, h3⟩) r.root r.child r.axis := by
    rw [hz']
    exact ⟨hr1.trans (congrArg (GlobalCarryRecognizer.enc z) hrroot).symm,
      hr2.trans (congrArg (GlobalCarryRecognizer.enc z) hrchild).symm,
      hr3.trans (congrArg (fun n : ℕ => (n : K)) hraxis).symm⟩
  have htsr : (computeMemRec (renderNode z α u.label).row.2.2.1 ⟨k, h3⟩).ts =
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
        hmempos hcomp hmem).challenges.α ^ timestampExp chal.α (chal.α ^ r.recordExp) := by
    rw [hα', hα, timestampExp_pow_self, hts, hrexp]
  have hrecord : computeMemRec (renderNode z α u.label).row.2.2.1 ⟨k, h3⟩ =
      ⟨encC z r.root, encC z r.child, (r.axis : K), chal.α ^ r.recordExp⟩ := by
    refine ComputeTable.MemRec.ext ?_ ?_ ?_ ?_
    · exact hr1.trans ((congrArg (GlobalCarryRecognizer.enc z) hrroot).symm.trans
        (encC_eq z r.root).symm)
    · exact hr2.trans ((congrArg (GlobalCarryRecognizer.enc z) hrchild).symm.trans
        (encC_eq z r.child).symm)
    · exact hr3.trans (congrArg (fun n : ℕ => (n : K)) hraxis).symm
    · rw [hts, hrexp, hα]
  exact ⟨Service.ofMemRecordReq (exec := genExactExecutionA (F := F) chal Ksz orbit horb a b c
      (genComputeRows z α t) mf hmempos hcomp hmem) r
      (computeMemRec (renderNode z α u.label).row.2.2.1 ⟨k, h3⟩)
      (timestampExp chal.α (chal.α ^ r.recordExp)) hrealr hreqmem htsr hslot,
    rfl, rfl, rfl, rfl, hrecord⟩

end Gen

/-! ## C. `roots`, at the generated carrier

`ExactServedMemoryTrace.roots` (`ServedMemoryTrace.lean:609`) wants a `RootTrace` at *every* forest
index.  `RootShape` (`GenServedForest.lean`) says what the tree at that index is, §B says which
`Service` each of its requests carries, and `rootTraceOfRecordTree` / `rootTraceOfChainedPair`
(`GenServedRootTrace.lean:350,931`) turn those into the `RootTrace`.  Three things stand between
them.

* **The index bridge.**  The builders speak of `exactAxisTree cfg exec i` and
  `rootResponseRecords exec i`; the classification speaks of a member of the *unthreaded*
  `genMemForestFromTree`, while the carrier commits `threadGenForest inp 0` of it.  §C.1 is that
  bridge — Tier A's `memoryTreeAt_threaded` / `exactAxisTree_assigned` /
  `rootResponseRecords_assigned` (`GenTierAMemoryTrace.lean:960,968,1180`) with the configuration
  removed, composed with `axisMTree_threadGenForest` / `servedGen_thread_get`, which are generic
  despite their file name.  `threadGenForest_length` keeps the classified index and the built index
  the same one.

* **The chain's `hne` needs the orbit, not just distinct exponents.**  `timestampExp α x` is a
  choice on the *field value* `x` (`AxisSoundness.lean:50`), so at `α = 1` — or any `α` with
  `α ^ 2 = 1` — `timestampExp α (α ^ e₁})` and `timestampExp α (α ^ e₂)` are the *same term* however
  far apart `e₁` and `e₂` are. It also
  subsumes `α ≠ 0`, since `orderOf (0 : K) = 0`. `timestampExp_pow_ne_of_lt_orderOf` below is that
  step and it is carried as a hypothesis, never assumed.

* **`RootShape` is a `Prop` and `RootTrace` is a `Type`**, so the disjunction cannot be eliminated
  into the data.  §C.2 goes through `Exists.choose` on a statement that *also pins the readout*: an
  opaque `Nonempty.some` would be useless, because `ExactServedMemoryTrace`'s other three fields
  quantify over `(roots i)`'s contents.  `RootServiceShape` is that readout — it names the tree, the
  request(s), the `Service`(s) and the exact `services` list.  What makes the choice demonstrably
  non-opaque is that pin plus `genRoots_services_length`; `RootServiceShape.timestampPowers` reads
  the multiset out in the same *shape* as `genMemForest_timestampPowers_nodup`'s `h1`/`h2`
  right-hand sides, but is **not an instance of those hypotheses**, which quantify over a
  tree-indexed readout (`FN` §3, `FU`).

-- 
-/

/-- **Distinct exponents inside the orbit give distinct timestamp exponents.**

`α ^ ·` is injective below `orderOf α`, and
`timestampExp_pow_self` (`GenMemForestOrder.lean:295`) inverts it. -- the paper -/
theorem timestampExp_pow_ne_of_lt_orderOf {α : K} {e1 e2 : ℕ}
    (h1 : e1 < orderOf α) (h2 : e2 < orderOf α) (hne : e1 ≠ e2) :
    timestampExp α (α ^ e1) ≠ timestampExp α (α ^ e2) := by
  intro heq
  refine hne (pow_injOn_Iio_orderOf (Set.mem_Iio.mpr h1) (Set.mem_Iio.mpr h2) ?_)
  show α ^ e1 = α ^ e2
  rw [← timestampExp_pow_self α e1, ← timestampExp_pow_self α e2, heq]

/-- Every record exponent of a generated node lies below `orderOf α` once the compute line count
does.  `genForestRecordExps_le` (`GenMemForestOrder.lean:155`) bounds it by the line count; `horb`
is the orbit-capacity restriction. -/
theorem extractNodeReqs_recordExp_lt_orderOf {t : NTree (GenComputeRow K)} (α : K)
    (hmatch : treeRequestsMatch (bfsAssign t))
    (horb : accAt t (bfsRows t).length < orderOf α)
    {n : NTree (GenComputeRow K)} (hn : InTree (bfsAssign t) n)
    {r : MemRecordReq} (hr : r ∈ extractNodeReqs n.label) :
    r.recordExp < orderOf α := by
  refine lt_of_le_of_lt (genForestRecordExps_le t hmatch ?_) horb
  rw [genForestRecordExps]
  refine List.mem_flatMap.mpr ⟨n, ?_, List.mem_map.mpr ⟨r, hr, rfl⟩⟩
  have hmem : n ∈ dfsForest [bfsAssign t] :=
    (mem_dfsForest _ n).mpr ⟨_, List.mem_singleton_self _, hn⟩
  simpa [dfsForest] using hmem

section Index

variable {F : Type} [Field F] [Algebra F K]

/-! ### C.1 The execution's memory root at a forest index -/

theorem genExactConfig_kMem
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    (genExactConfig (F := F) chal Ksz orbit horb ct mf hmempos hcomp hmem).kMem
      = mf.length := rfl

/-- **The generated execution's `i`-th memory root is the `i`-th committed tree.**  Tier A's
`memoryTreeAt_threaded` (`GenTierAMemoryTrace.lean:960`) with the configuration removed. -/
theorem genExactExecutionA_memoryTreeAt
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (i : Fin (genExactConfig (F := F) chal Ksz orbit horb ct mf hmempos hcomp hmem).kMem) :
    (genExactExecutionA (F := F) chal Ksz orbit horb a b c ct mf
        hmempos hcomp hmem).memoryTreeAt i
      = mapNTree GenMemoryRow.row (mf[(i : ℕ)]'i.isLt) := by
  unfold ExactExecution.memoryTreeAt
  show (List.map (mapNTree GenMemoryRow.row) mf).get _ = _
  exact List.get_eq_getElem.trans (List.getElem_map _)

theorem genExactExecutionA_exactAxisTree
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (i : Fin (genExactConfig (F := F) chal Ksz orbit horb ct mf hmempos hcomp hmem).kMem) :
    exactAxisTree (genExactConfig (F := F) chal Ksz orbit horb ct mf hmempos hcomp hmem)
        (genExactExecutionA (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem) i
      = axisMTree chal.α (mapNTree GenMemoryRow.row (mf[(i : ℕ)]'i.isLt)) := by
  rw [exactAxisTree, genExactExecutionA_memoryTreeAt]
  rfl

theorem genExactExecutionA_rootResponseRecords
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (i : Fin (genExactConfig (F := F) chal Ksz orbit horb ct mf hmempos hcomp hmem).kMem) :
    rootResponseRecords
        (genExactExecutionA (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem) i
      = servedGen [mf[(i : ℕ)]'i.isLt] := by
  unfold rootResponseRecords
  rw [genExactExecutionA_memoryTreeAt]
  exact servedGen_mapped_row _

end Index

/-! ### C.2 The choice packaging

`RootServiceShape` is the readout the choice has to pin.  It names the tree at the index, the
request(s) it came from, the `Service`(s) that serve them and the literal `services` list, so every
`ExactServedMemoryTrace` field that quantifies over `(roots i)`'s contents can still be proved. -/

section Choice

variable {F : Type} [Field F] [Algebra F K]

/-- One `Service` serving one `MemRecordReq`: the five equations both builders want. -/
def ServiceMatches (E : Noun → ComputeTable.FP K) (α : K)
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (s : ServedMemoryTrace.Service cfg exec) (r : MemRecordReq) : Prop :=
  s.root = r.root ∧ s.child = r.child ∧ s.axis = r.axis ∧
    s.exponent = timestampExp α (α ^ r.recordExp) ∧
    s.record = ⟨E r.root, E r.child, (r.axis : K), α ^ r.recordExp⟩

/-- **The readout of one built root.**  `RootShape`'s two disjuncts, each carrying the `Service`s
and the literal `services` list the corresponding builder installed. -/
def RootServiceShape (E : Noun → ComputeTable.FP K) (z α lmb : K)
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    (reqs : List MemRecordReq) (u : NTree (GenMemoryRow K))
    (R : RootTrace cfg exec i) : Prop :=
  (∃ r ∈ reqs, u = genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp ∧
      ∃ s, ServiceMatches E α s r ∧ R.services = [s]) ∨
    (∃ r1 ∈ reqs, ∃ r2 ∈ reqs, r1.child = r2.root ∧ r1.recordExp ≠ r2.recordExp ∧
      genAnnotatedChainedTree E z α lmb [r1, r2] = some u ∧
      ∃ s1 s2, ServiceMatches E α s1 r1 ∧ ServiceMatches E α s2 r2 ∧
        R.services = [s1, s2])

/-- **The chosen root's timestamp multiset, with the tree it sits at named.**  This is what makes
the choice non-opaque.

**It is not an instance of `genMemForest_timestampPowers_nodup`'s `h1`/`h2`**
(`GenMemForestOrder.lean:270`), and must not be described as one: those quantify over a
*tree-indexed readout* `rd`, and this supplies no `rd` — it is a fact about one `RootTrace` at one
index. It has the same **shape** as `h1`/`h2`'s right-hand sides, which is why it will be the input
to whatever `rd` §D eventually settles on, and that is the whole of the connection. -/
theorem RootServiceShape.timestampPowers {E : Noun → ComputeTable.FP K} {z α : K}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    {reqs : List MemRecordReq} {u : NTree (GenMemoryRow K)} {R : RootTrace cfg exec i}
    (hα : cfg.challenges.α = α) (h : RootServiceShape E z α lmb reqs u R) :
    (∃ r ∈ reqs, u = genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp ∧
        R.timestampPowers = [α ^ r.recordExp]) ∨
      (∃ r1 ∈ reqs, ∃ r2 ∈ reqs, genAnnotatedChainedTree E z α lmb [r1, r2] = some u ∧
        R.timestampPowers = [α ^ r1.recordExp, α ^ r2.recordExp]) := by
  subst hα
  rcases h with ⟨r, hr, hu, s, hs, hsv⟩ | ⟨r1, h1, r2, h2, _, _, ht, s1, s2, hs1, hs2, hsv⟩
  · exact Or.inl ⟨r, hr, hu,
      timestampPowers_of_services_singleton R s r.recordExp hsv hs.2.2.2.1⟩
  · exact Or.inr ⟨r1, h1, r2, h2, ht,
      timestampPowers_of_services_pair R s1 s2 r1.recordExp r2.recordExp hsv
        hs1.2.2.2.1 hs2.2.2.2.1⟩

/-- **The built root carries one or two services**, so the choice produced real data: with
`RootTrace.recordPartition` this makes `rootResponseRecords` at that root a non-empty record
list. -/
theorem RootServiceShape.services_length {E : Noun → ComputeTable.FP K} {z α : K}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    {reqs : List MemRecordReq} {u : NTree (GenMemoryRow K)} {R : RootTrace cfg exec i}
    (h : RootServiceShape E z α lmb reqs u R) :
    R.services.length = 1 ∨ R.services.length = 2 := by
  rcases h with ⟨-, -, -, s, -, hsv⟩ | ⟨-, -, -, -, -, -, -, s1, s2, -, -, hsv⟩
  · exact Or.inl (by rw [hsv]; rfl)
  · exact Or.inr (by rw [hsv]; rfl)

/-- **`roots` at one index, from the classification.**

`RootShape` is a `Prop` disjunction and `RootTrace` is a `Type`, so the two cannot be joined by
large elimination; this existence statement is what a choice is taken on, and it pins the readout so
the choice is not opaque.  `hlt` is the orbit-capacity restriction, per request — without it the
chain builder's `hne` is not merely unproved but false (see the section header).
-- -/
theorem exists_rootTrace_of_rootShape
    (E : Noun → ComputeTable.FP K) (z α : K)
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    (hα : cfg.challenges.α = α)
    (reqs : List MemRecordReq) (u : NTree (GenMemoryRow K))
    (hshape : RootShape E z α lmb reqs u)
    (hslot : ∀ r ∈ reqs, Noun.slot r.axis r.root = some r.child)
    (hsvc : ∀ r ∈ reqs, ∃ s : ServedMemoryTrace.Service cfg exec, ServiceMatches E α s r)
    (hlt : ∀ r ∈ reqs, r.recordExp < orderOf α)
    (hax : exactAxisTree cfg exec i = axisMTree α (mapNTree GenMemoryRow.row u))
    (hsrv : rootResponseRecords exec i = servedGen [u]) :
    ∃ R : RootTrace cfg exec i, RootServiceShape E z α lmb reqs u R := by
  subst hα
  rcases hshape with ⟨r, hr, rfl⟩ | ⟨r1, h1, r2, h2, hlink, hne, ht⟩
  · obtain ⟨s, hs1, hs2, hs3, hs4, hs5⟩ := hsvc r hr
    exact ⟨rootTraceOfRecordTree E z r.root r.child r.axis r.recordExp s
        hs1 hs2 hs3 hs4 hs5 (hslot r hr) hax hsrv,
      Or.inl ⟨r, hr, rfl, s, ⟨hs1, hs2, hs3, hs4, hs5⟩, rfl⟩⟩
  · obtain ⟨s1, ha1, ha2, ha3, ha4, ha5⟩ := hsvc r1 h1
    obtain ⟨s2, hb1, hb2, hb3, hb4, hb5⟩ := hsvc r2 h2
    have hnee : timestampExp cfg.challenges.α (cfg.challenges.α ^ r1.recordExp) ≠
        timestampExp cfg.challenges.α (cfg.challenges.α ^ r2.recordExp) :=
      timestampExp_pow_ne_of_lt_orderOf (hlt r1 h1) (hlt r2 h2) hne
    exact ⟨rootTraceOfChainedPair E z r1 r2 u ht hlink s1 s2
        ha1 ha2 ha3 ha4 ha5 hb1 hb2 hb3 hb4 hb5
        (hslot r1 h1) (hslot r2 h2) hnee hax hsrv,
      Or.inr ⟨r1, h1, r2, h2, hlink, hne, ht, s1, s2,
        ⟨ha1, ha2, ha3, ha4, ha5⟩, ⟨hb1, hb2, hb3, hb4, hb5⟩, rfl⟩⟩

end Choice

/-! ### C.3 The generated carrier

`genMemoryForest z α inp t` is `threadGenForest inp 0` of the classified forest
(`GenSemanticDataParts.lean:43`), so the index bridge of §C.1 composes with the two threading
transports and the classification lands at the same index the builder builds at. -/

section GenRoots

variable {F : Type} [Field F] [Algebra F K]

theorem genMemoryForest_eq_thread (z α : K) (inp : MemoryTable.Inputs K)
    (t : NTree (GenComputeRow K)) :
    genMemoryForest z α lmb inp t
      = threadGenForest inp 0
          (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t))) := rfl

/-- A forest index of the generated configuration indexes the *unthreaded* classified forest too:
`threadGenForest` preserves length. -/
theorem genRoot_index_lt (z α : K) (inp : MemoryTable.Inputs K)
    (t : NTree (GenComputeRow K))
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h)
    (i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem) :
    (i : ℕ) < (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t))).length := by
  have h : (i : ℕ) <
      (threadGenForest inp 0
        (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))).length := i.isLt
  rwa [threadGenForest_length] at h

theorem genExactExecutionA_exactAxisTree_unthreaded (z α : K) (inp : MemoryTable.Inputs K)
    (t : NTree (GenComputeRow K)) (a b c : K)
    (chal : ChallengeVector K) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h)
    (i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem) :
    exactAxisTree
        (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
          (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem)
        (genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
          (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem) i
      = axisMTree α (mapNTree GenMemoryRow.row
          ((genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))[(i : ℕ)]'
            (genRoot_index_lt (F := F) z α inp t chal Ksz orbit horb
              hmempos hcomp hmem i))) := by
  rw [genExactExecutionA_exactAxisTree, hα]
  exact axisMTree_threadGenForest inp 0 α _
    (genRoot_index_lt (F := F) z α inp t chal Ksz orbit horb hmempos hcomp hmem i)

theorem genExactExecutionA_rootResponseRecords_unthreaded (z α : K) (inp : MemoryTable.Inputs K)
    (t : NTree (GenComputeRow K)) (a b c : K)
    (chal : ChallengeVector K)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h)
    (i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem) :
    rootResponseRecords
        (genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
          (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem) i
      = servedGen [(genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))[(i : ℕ)]'
          (genRoot_index_lt (F := F) z α inp t chal Ksz orbit horb hmempos hcomp hmem i)] := by
  rw [genExactExecutionA_rootResponseRecords]
  exact servedGen_thread_get inp 0 _
    (genRoot_index_lt (F := F) z α inp t chal Ksz orbit horb hmempos hcomp hmem i)

/-- **A `RootTrace` at every forest index of the generated carrier, with its readout.**

Everything is composed here and nothing is assumed beyond the program's acceptance and the
orbit-capacity restriction `horbα`: the classification
(`rootShape_genMemForestFromTree` + `nodeExpsNodup_of_requestsMatch`), the per-request `hslot`
(`bfsAssign_extract_requests_slot ∘ treeRequestsWF_airReorder ∘ genComputeSkeleton_tree_requests_wf`),
the per-request `Service` (§B), the per-request exponent bound, and §C.1's index bridge.
-- -/
theorem exists_rootTrace_gen (z α a b c : K)
    (chal : ChallengeVector K) (hz : chal.z = z) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h)
    (i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem) :
    ∃ R : RootTrace
        (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
          (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem)
        (genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
          (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem) i,
      ∃ n, InTree (bfsAssign (airReorder t)) n ∧
        RootServiceShape (encC z) z α chal.lam (extractNodeReqs n.label)
          ((genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))[(i : ℕ)]'
            (genRoot_index_lt (F := F) z α inp t chal Ksz orbit horb hmempos hcomp hmem i))
          R := by
  have hidx := genRoot_index_lt (F := F) z α inp t chal Ksz orbit horb hmempos hcomp hmem i
  have hmatch : treeRequestsMatch (bfsAssign (airReorder t)) :=
    genComputeSkeleton_air_requestsMatch h
  obtain ⟨n, hn, hshape⟩ := rootShape_genMemForestFromTree (encC z) z α
    (bfsAssign (airReorder t)) (nodeExpsNodup_of_requestsMatch (airReorder t) hmatch)
    _ (List.getElem_mem hidx)
  have hslot := bfsAssign_extract_requests_slot (airReorder t)
    (treeRequestsWF_airReorder (genComputeSkeleton_tree_requests_wf h)) n hn
  have hsvc : ∀ r ∈ extractNodeReqs n.label,
      ∃ s : ServedMemoryTrace.Service
        (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
          (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem)
        (genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
          (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem),
      ServiceMatches (encC z) α s r := by
    intro r hr
    obtain ⟨s, k1, k2, k3, k4, k5⟩ :=
      exists_service_of_memRecordReq (F := F) z α a b c chal hz hα Ksz orbit horb h
        (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem hn hr (hslot r hr)
    exact ⟨s, k1, k2, k3, by rw [k4, hα], by rw [k5, hα]⟩
  have hlt : ∀ r ∈ extractNodeReqs n.label, r.recordExp < orderOf α := fun r hr =>
    extractNodeReqs_recordExp_lt_orderOf α hmatch horbα hn hr
  have hαc : (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).challenges.α = α := hα
  obtain ⟨R, hR⟩ := exists_rootTrace_of_rootShape (F := F) (encC z) z α hαc
    (extractNodeReqs n.label) _ hshape hslot hsvc hlt
    (genExactExecutionA_exactAxisTree_unthreaded (F := F) z α inp t a b c chal hα
      Ksz orbit horb hmempos hcomp hmem i)
    (genExactExecutionA_rootResponseRecords_unthreaded (F := F) z α inp t a b c chal
      Ksz orbit horb hmempos hcomp hmem i)
  exact ⟨R, n, hn, hR⟩

/-- **`ExactServedMemoryTrace.roots`, for the generated carrier.**  The choice; its readout is
`genRoots_spec`. -/
noncomputable def genRoots (z α a b c : K)
    (chal : ChallengeVector K) (hz : chal.z = z) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h) :
    ∀ i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem,
      RootTrace
        (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
          (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem)
        (genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
          (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem) i :=
  fun i => (exists_rootTrace_gen (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
    hmempos hcomp hmem i).choose

/-- **The chosen root's readout.**  This is what keeps the choice usable: the other three
`ExactServedMemoryTrace` fields quantify over `(roots i)`'s contents, and this names them. -/
theorem genRoots_spec (z α a b c : K)
    (chal : ChallengeVector K) (hz : chal.z = z) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h)
    (i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem) :
    ∃ n, InTree (bfsAssign (airReorder t)) n ∧
      RootServiceShape (encC z) z α chal.lam (extractNodeReqs n.label)
        ((genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))[(i : ℕ)]'
          (genRoot_index_lt (F := F) z α inp t chal Ksz orbit horb hmempos hcomp hmem i))
        (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
          hmempos hcomp hmem i) :=
  (exists_rootTrace_gen (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
    hmempos hcomp hmem i).choose_spec

/-- **The chosen root's timestamp multiset, at the tree the classification named.**

The same *shape* as `genMemForest_timestampPowers_nodup`'s `h1`/`h2` right-hand sides
(`GenMemForestOrder.lean:270`) and **not an instance of them**: those quantify over a tree-indexed
readout `rd`, and this is a fact about one `RootTrace` at one index (`FN` §3, `FU`).  Non-opacity of
the choice is carried by the tree pin in `RootServiceShape` together with
`genRoots_services_length`, not by this. -/
theorem genRoots_timestampPowers (z α a b c : K)
    (chal : ChallengeVector K) (hz : chal.z = z) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h)
    (i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem) :
    (∃ r : MemRecordReq, (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))[(i : ℕ)]'
          (genRoot_index_lt (F := F) z α inp t chal Ksz orbit horb hmempos hcomp hmem i)
            = genAnnotatedRecordTree (encC z) z α chal.lam r.root r.child r.axis r.recordExp ∧
        (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
          hmempos hcomp hmem i).timestampPowers = [α ^ r.recordExp]) ∨
      (∃ r1 r2 : MemRecordReq, genAnnotatedChainedTree (encC z) z α chal.lam [r1, r2] =
            some ((genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))[(i : ℕ)]'
              (genRoot_index_lt (F := F) z α inp t chal Ksz orbit horb hmempos hcomp hmem i)) ∧
        (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
          hmempos hcomp hmem i).timestampPowers
            = [α ^ r1.recordExp, α ^ r2.recordExp]) := by
  obtain ⟨n, -, hR⟩ := genRoots_spec (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
    hmempos hcomp hmem i
  have hαc : (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).challenges.α = α := hα
  rcases hR.timestampPowers hαc with ⟨r, -, hu, hts⟩ | ⟨r1, -, r2, -, ht, hts⟩
  · exact Or.inl ⟨r, hu, hts⟩
  · exact Or.inr ⟨r1, r2, ht, hts⟩

/-- **Every built root of the generated carrier carries a service.**  Non-vacuity of the choice:
the chosen `RootTrace` is not an empty traversal. -/
theorem genRoots_services_length (z α a b c : K)
    (chal : ChallengeVector K) (hz : chal.z = z) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h)
    (i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem) :
    (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
        hmempos hcomp hmem i).services.length = 1 ∨
      (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
        hmempos hcomp hmem i).services.length = 2 := by
  obtain ⟨n, -, hR⟩ := genRoots_spec (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
    hmempos hcomp hmem i
  exact RootServiceShape.services_length hR

/-- **And therefore serves a record.**  `RootTrace.recordPartition` (`ServedMemoryTrace.lean:499`)
identifies `rootResponseRecords` with the services' records, so a non-empty `services` means the
forest root really emits `read_root` rows. -- the paper -/
theorem genRoots_rootResponseRecords_ne_nil (z α a b c : K)
    (chal : ChallengeVector K) (hz : chal.z = z) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h)
    (i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem) :
    rootResponseRecords
        (genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
          (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem) i ≠ [] := by
  have hlen := genRoots_services_length (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
    hmempos hcomp hmem i
  have hrec := (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
    hmempos hcomp hmem i).recordPartition
  intro hnil
  rw [hnil] at hrec
  have : (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
      hmempos hcomp hmem i).services.length = 0 := by
    rw [← List.length_map (f := ServedMemoryTrace.Service.record), ← hrec]
    rfl
  omega

end GenRoots

section IndexRange

variable {F : Type} [Field F] [Algebra F K]

/-! ## §D.0 `forestIndexRange`, filled

Recorded at `FU`; this is the third
time an estimate on this field family has been pessimistic. -/

/-- Both `RootTrace` builders install one or two services, so every generated root is within the
bound `services_sum_le_two_mul` wants. -/
theorem genRoots_services_length_le_two (z α a b c : K)
    (chal : ChallengeVector K) (hz : chal.z = z) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h)
    (i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem) :
    (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
      hmempos hcomp hmem i).services.length ≤ 2 := by
  rcases genRoots_services_length (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
    hmempos hcomp hmem i with h1 | h2
  · rw [h1]; norm_num
  · rw [h2]

/-- **`forestIndexRange` at the generated carrier.**

`hKsz2 : 2 * kMem ≤ Ksz` is the compiler's choice of `Ksz` — `genExactConfig` takes it as a free
parameter, and `2 * kMem` is an explicit bound the generator can compute.  Everything else comes
from `genRoots`.  Note `hmempos` supplies the lower half: a non-empty BFS forces `kMem ≥ 1`, so a
root exists, and every generated root serves at least one record.
-- -/
theorem genRoots_forestIndexRange (z α a b c : K)
    (chal : ChallengeVector K) (hz : chal.z = z) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h)
    (hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem ≤ Ksz) :
    IO.InRange
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).Ksz
      ((List.finRange (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem).flatMap
        (fun i => (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
          hmempos hcomp hmem i).timestampPowers)).length := by
  have hk : 0 < (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem := by
    rw [genExactConfig_kMem]
    exact List.length_pos_of_ne_nil (ne_nil_of_bfsForest_length_pos hmempos)
  refine forestIndexRange_of_services _ ⟨0, hk⟩ ?_ ?_
  · rcases genRoots_services_length (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
      hmempos hcomp hmem ⟨0, hk⟩ with h1 | h2
    · rw [h1]
    · rw [h2]; norm_num
  · refine le_trans (services_sum_le_two_mul _ (fun i =>
      genRoots_services_length_le_two (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
        hmempos hcomp hmem i)) ?_
    exact hKsz2

end IndexRange

/-! ## §D.1 `horbα` at a finite carrier

That is a real observation about the *Lean* statement, which quantifies
over `[Field K]` and so is more general than the paper.

**It is not a restriction where the paper instantiates.**  `Def:NMR` puts the timestamp base in the
extension field: "the timestamp space `𝒯 := β^k ∈ 𝕂` is an integer `k`, encoded as a power of
`β ∈ 𝕂`", with `𝕂` the degree-`e` extension of `𝔽` (`Def:RAP` item 2, `:140`). What makes
the timestamp base finite-order is `𝔽` being **finite**, which the paper states at the paper
("a finite field `𝔽`", `Def:Canonical_RAP`) and `:158-159` — the cites this docstring should have
carried and did not.

This section discharges that as theorems rather than as a docstring: at a finite carrier, finite
order is **free**, and the premise is satisfiable for a trace shorter than the field.

-- 
-/

section FiniteOrbit

/-- **Finite order is free at a finite carrier.**  So `horbα` carries no root-of-unity content
where the paper instantiates: it is exactly the row-count-versus-orbit bound, plus `α ≠ 0`. -/
theorem orderOf_pos_of_ne_zero [Finite K] {α : K} (hα : α ≠ 0) : 0 < orderOf α := by
  rw [orderOf_pos_iff]
  have : IsOfFinOrder (Units.mk0 α hα) := isOfFinOrder_of_finite _
  rwa [← orderOf_pos_iff, ← orderOf_units, Units.val_mk0, orderOf_pos_iff] at this

/-- **A primitive element realises the largest possible orbit.**  The multiplicative group of a
finite field is cyclic, so some `α` has order `card K - 1`. -/
theorem exists_orderOf_eq_card_sub_one [Fintype K] [DecidableEq K] :
    ∃ α : K, α ≠ 0 ∧ orderOf α = Fintype.card K - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  refine ⟨(g : K), g.ne_zero, ?_⟩
  rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hg,
    Nat.card_eq_fintype_card, Fintype.card_units]

/-- **`horbα` is satisfiable at any finite carrier whose field is larger than the trace.**

The compiler chooses `α`, so this is the form a generator uses: a trace of `n` records fits inside
some orbit as soon as `n < card K - 1`. -/
theorem exists_alpha_orbit_gt [Fintype K] [DecidableEq K] (n : ℕ)
    (hn : n < Fintype.card K - 1) :
    ∃ α : K, α ≠ 0 ∧ n < orderOf α := by
  obtain ⟨α, hα0, hα⟩ := exists_orderOf_eq_card_sub_one (K := K)
  exact ⟨α, hα0, by rw [hα]; exact hn⟩

/-! ### How this wires into the assembly

There are **two** orbit-premise shapes in the generic infrastructure, and they are not independent:

* `genSemanticData` and `genLanguage` take `(B : ℕ) (hB : B ≤ orderOf α)` together with
  `hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B`
  (`GenSemanticData.lean:132-133`, `GenChainedLanguage.lean:1417-1418` and four sibling sites);
* `genRoots` and `FB`'s two `nodup` theorems take
  `horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α`
  (`GenMemForestOrder.lean:168`, `:280`).

The first **implies** the second, so **§C introduced no new precondition at the assembly level** —
`sd` was already carrying something strictly stronger. `horb_of_window` is that one line, and it is
worth having written down because the two shapes look unrelated and a future assembly would
otherwise carry both.

`exists_alpha_assembly_orbit` then provisions all of it from a single `α`, which is what a generator
actually does: it *chooses* `α` rather than receiving it. -/

/-- **`horbα` follows from the window premise `sd` already carries.**  `n < n + 3 < B ≤ orderOf α`.
So the orbit condition §C states is not additional to the assembly's. -/
theorem horb_of_window {α : K} {n B : ℕ} (hB : B ≤ orderOf α) (hwin : n + 3 < B) :
    n < orderOf α := by omega

/-- **One `α` meets every orbit condition the assembly states.**

Take `n := accAt (airReorder t) (bfsRows (airReorder t)).length`, the trace's record count. At a
finite carrier whose field outruns it, a single primitive `α` supplies `α ≠ 0`, the window bound
`hwin` with `B := orderOf α`, `hB` reflexively, and `genRoots`' `horbα`. This is the generator's
`α`-choice, and it is why the orbit restriction is a sizing condition rather than an assumption
about the program. -/
theorem exists_alpha_assembly_orbit [Fintype K] [DecidableEq K] (n : ℕ)
    (hn : n + 3 < Fintype.card K - 1) :
    ∃ α : K, α ≠ 0 ∧ ∃ B : ℕ, B ≤ orderOf α ∧ n + 3 < B ∧ n < orderOf α := by
  obtain ⟨α, h0, hgt⟩ := exists_alpha_orbit_gt (K := K) (n + 3) hn
  exact ⟨α, h0, orderOf α, le_rfl, hgt, horb_of_window le_rfl hgt⟩

end FiniteOrbit

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.realizesMemRec_of_bindMemRec
#print axioms Nock.NockVMROM.Thm54.TraceGen.computeMemRec_mem_activeRequestRecords
#print axioms Nock.NockVMROM.Thm54.TraceGen.Service.ofMemRecordReq
#print axioms Nock.NockVMROM.Thm54.TraceGen.activeRequestRecords_length_eq
#print axioms Nock.NockVMROM.Thm54.TraceGen.computeMemRec_eq_getElem
#print axioms Nock.NockVMROM.Thm54.TraceGen.renderNode_computeMemRec_ts
#print axioms Nock.NockVMROM.Thm54.TraceGen.mem_computeRows_of_bfsRows
#print axioms Nock.NockVMROM.Thm54.TraceGen.mem_rawRequests_of_mem_computeRows
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_service_of_memRecordReq

#print axioms Nock.NockVMROM.Thm54.TraceGen.timestampExp_pow_ne_of_lt_orderOf
#print axioms Nock.NockVMROM.Thm54.TraceGen.extractNodeReqs_recordExp_lt_orderOf
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecutionA_memoryTreeAt
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecutionA_exactAxisTree
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecutionA_rootResponseRecords
#print axioms Nock.NockVMROM.Thm54.TraceGen.RootServiceShape.timestampPowers
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_rootTrace_of_rootShape
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRoot_index_lt
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecutionA_exactAxisTree_unthreaded
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecutionA_rootResponseRecords_unthreaded
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_rootTrace_gen
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRoots
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRoots_spec
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRoots_timestampPowers
#print axioms Nock.NockVMROM.Thm54.TraceGen.RootServiceShape.services_length
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRoots_services_length
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRoots_rootResponseRecords_ne_nil
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRoots_services_length_le_two
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRoots_forestIndexRange
#print axioms Nock.NockVMROM.Thm54.TraceGen.orderOf_pos_of_ne_zero
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_orderOf_eq_card_sub_one
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_alpha_orbit_gt
#print axioms Nock.NockVMROM.Thm54.TraceGen.horb_of_window
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_alpha_assembly_orbit
