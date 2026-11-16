/-
  Nock/NockVMROM/Thm54/TraceGen/GenServiceBookkeeping.lean

  `GenAxisBoundaryPriced.servedSlotCovers_of_accepts` discharges
  `GenGlobalCollision.ServedSlotCovers` at a production-accepted coin outside summand 4 of
  `FailureUnion`, carrying four residuals.  Two of them are bookkeeping, and this module is those
  two.  The IO record matching (residual (b), the paper `1431`, `1441`) is **not**
  touched: it is named where it is used and carried.

  ## §A.  The prover's nouns have a leaf bound, and it is committed trace data

  `GenGlobalCollision.globalBadSeeds_card_le` takes `hS : ∀ n ∈ S, n.leaves ≤ Λ`, and
  `GenGlobalCollision`'s header records that as carried because `ServedMemoryTrace.Service` has no
  leaf bound.  `IK`/`IG` proposed routing it through `RootTrace.subject`.  That is not needed, and
  the reason is that `GenNounRecovery.recoveredLabelling` is a **structural** function of the
  committed memory walk:

  * `leaves_recoveredLabelling_le_size` — the recovered noun at *any* address has at most
    `NTree.size` leaves, by induction on `MemoryFingerprintStructure`.  Since
    `Nock.Walk.bfsForest_length` makes `NTree.size` the walk's own row count, this is a bound in
    committed trace data, not a premise about a subject noun.
  * `Service.leaves_child_le_root` — **unconditional for every `Service`**: `Service.served` is
    `Noun.slot axis root = some child` and `slot` never grows the leaf count
    (`TraceGen.slot_leaves_le`).  So the child half of the bound is free at `Service`, with no
    witness, no walk and no acceptance.

  Combining them, a `GenAxisBoundaryPriced.PricedRecordWitness` bounds both of its served nouns by
  its own region's size.  `FieldEmbedding.slot_boundedBy` plus
  `GenNounRecovery.recoveredLabelling_spec` does the same for `FieldEmbedding.BoundedBy q`, so
  `hbN` is discharged on the service side too.

  ## §B.  The index set, bounded by the row counts

  `GenGlobalCollision.lean`'s `composed_numerator_at_batch258_tight` docstring asserts
  `N.card ≤ 4 · (#OP0 rows + #OP9 rows)` in prose; there was no theorem, and `S.card` appears
  squared in the numerator, so without one the sixth event is not effective.

  The obstruction was that `ServedSlotCovers exec q S` quantifies the service **existentially**, so
  no `S` can be read off `exec`.  §B fixes that by making the served nouns *named*: a
  `PricedAssignment` supplies, per OP0/OP9 committed row, a witness whose served nouns are
  `rootOf row` and `childOf row` for two given functions.  Then `traceNounTable` is a concrete
  `Finset Noun` built from the committed rows, and `card_traceNounTable_le` bounds it by
  `2 · #(OP0/OP9 rows) + 6 · #(skeleton rows)`.  Composed with `globalBadSeeds_card_le`, the sixth
  event has a numerator in trace data alone (`globalBadSeeds_card_le_traceNounTable`).

  The `6` is not slack from the service side — it is `SkeletonRecordNounsIn`, which quantifies over
  *all* `recordCount ≤ 3` records of every committed row, two nouns each.  The prose figure `4`
  counts only the served slot's record; the definition asks for more.

  ## §C.  `Service.timestamp` is a **compute**-side column, and that is why `IF` does not close it

  `IL`'s brief for this module conjectured that
  `GenTimestampClosed.productionStrategy_timestampClosed` plus
  `timestampExp_recovers_ts_iff_closed` gives `Service.timestamp` at a template-specialized
  execution.  **It does not, and the reason is a real asymmetry rather than a missing lemma.**

  `Service.record ∈ exec.rawRequests` (`Language.lean:33`) is a **compute**-table record, and
  `SemanticTimestampStrategy.ComputeRowTemplate.specialize` (`:391`) emits it through
  `specializeMemRecScaled α lnPrev …` with `lnPrev = computeLineOrigin … * α ^ e` (`:359`), so
  `ts = origin · α ^ n` for an α-free committed `origin` that `V_comp` never pins.
  `productionStrategy_timestampClosed` is about `MemoryRowTemplate.specialize` (`:435`), which
  takes the **unscaled** `specializeMemRec` — that is exactly the asymmetry
  `GenTimestampClosed`'s own §A states.  `ProductionStrategy` reaches the templates through
  `DataOnlySeedFixedTimestampCarrier`, which has **no** `originOne` field (the semantic
  `SeedFixedTimestampCarrier` does, `SemanticTimestampStrategy.lean:1604`), and `BindComputeRow`
  says nothing about any timestamp column.  So there is no supplier at production scope, and none
  is faked here.

  What §C does instead is state the two honest reductions, one of which was already in the tree:

  * `computeRecord_timestampClosed_of_lnPrev` — closure of the record timestamp from closure of the
    row's own `ln_prev`.  This is `compute_ts_eq_pow_of_origin`
    (`SemanticTimestampStrategy.lean:594`) with the ladder condition
    `lnPrevExponent ≤ recordExponent i` **dropped**: for orbit *membership* the truncated
    subtraction is harmless, so the whole of (d) is the single scalar `ln_prev ∈ ⟨α⟩`.
  * `timestampClosed_of_servedMatch` — closure from a timestamp equality with an active memory row
    of the same specialized execution, which is `productionStrategy_timestampClosed` transported.
    That premise is a **projection of residual (b)** onto the `ts` column: it is what the LogUp
    request/response match would give, and it is carried, not proved.

  ## Not claimed

  No `sorry`, no `admit`, no `native_decide`, no new axiom, no carrier field.  `Gen.lean`,
  `Thm54.lean` and `ServedMemoryTrace.lean` unedited.  Residual (b) is not absorbed.

  Scope: §A and §B are `∀ K` field-generic with no fixed prime, program, axis or fixture.  §C's
  production statements are over an arbitrary `ProductionStrategy F K` at `p = ringChar K`.

  Every the paper line below was re-read at source.  One trap is worth writing down: the paper
  prints the timestamp closed form at `:1413` as `z^i` and the compute ladder at `:1728` as
  `ln_prev · z`, but that `z` is **`Def:NMR`'s timestamp base**, which is this tree's
  `ChallengeVector.α` — *not* the NPR seed `ChallengeVector.z`.  So "the paper's `z^i`" and "this
  module's `α ^ e`" are the same object, and the `α`/`z` in any statement here is the Lean name,
  never the paper's letter.

  -- 1288-1291 (slot/NMR addressing), 1413 (the closed form, printed `z^i`), 1431 (the
  -- `intermediate` accumulator) / 1441 (the IO matching between the two tables), 1450
  -- (`N, L ∈ negl(𝕂)`), 1728-1801 (`V_comp`; `:1728` is `ln_prev · z`, and the origin is unpinned),
  -- 1866/1881 (the two served record slots)
-/
import Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced
import Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision
import Nock.NockVMROM.Thm54.TraceGen.GenTimestampClosed
import Nock.NockVMROM.Thm54.TraceGen.GenSubISAWindow

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping

open scoped Classical

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TraceGen.GenNounRecovery
open Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## §A.  Leaf and window bounds on the prover's own nouns -/

section Leaves

/-- **The recovered noun's leaf count is bounded by the committed walk's node count.**

`recoveredLabelling` is structural: a `halt` node contributes one leaf, a `decompose` node the sum
of its children's, and `read_root`/`verify_child` pass through.  So the noun the service serves is
never bigger than the memory rows that carry it — and by `Nock.Walk.bfsForest_length` that node
count *is* a row count of the committed table.  Holds at every address, so both the root (`a = 1`)
and any descendant instance are covered. -/
theorem leaves_recoveredLabelling_le_size {z : K}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : MemoryFingerprintStructure z tree) (q : ℕ) :
    ∀ a : ℕ, (GlobalCarryAxis.nounOf (recoveredLabelling q tree a)).leaves ≤ tree.size := by
  induction h with
  | halt data atomShape =>
      intro a
      simp [recoveredLabelling_halt, GlobalCarryAxis.nounOf, Noun.leaves, NTree.size]
  | decompose data left right consEq hl hr ihl ihr =>
      intro a
      have hL := ihl (2 * a)
      have hR := ihr (2 * a + 1)
      have hsz : (NTree.node (MemoryTable.MState.decompose, data) [left, right]).size
          = 1 + (left.size + right.size) := by
        simp [NTree.size]
      rw [recoveredLabelling_decompose, hsz]
      show (Noun.cell _ _).leaves ≤ _
      simp only [Noun.leaves]
      omega
  | readRoot data child passEq hc ih =>
      intro a
      have hC := ih a
      have hsz : (NTree.node (MemoryTable.MState.read_root, data) [child]).size
          = 1 + child.size := by
        simp [NTree.size]
      rw [recoveredLabelling_readRoot, hsz]
      omega
  | verifyChild data child passEq hc ih =>
      intro a
      have hC := ih a
      have hsz : (NTree.node (MemoryTable.MState.verify_child, data) [child]).size
          = 1 + child.size := by
        simp [NTree.size]
      rw [recoveredLabelling_verifyChild, hsz]
      omega

/-- **The child half of the leaf bound is free at every `Service`.**  `Service.served` is a
`Noun.slot` equation, and a slot result is a subtree, so it cannot have more leaves than the root.
No witness, no walk, no acceptance, no seed. -/
theorem Service.leaves_child_le_root {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (s : ServedMemoryTrace.Service cfg exec) : s.child.leaves ≤ s.root.leaves :=
  TraceGen.slot_leaves_le s.axis s.root s.served

/-- Boundedness transports the same way. -/
theorem Service.boundedBy_child {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {q : ℕ} (s : ServedMemoryTrace.Service cfg exec)
    (h : FieldEmbedding.BoundedBy q s.root) : FieldEmbedding.BoundedBy q s.child :=
  FieldEmbedding.slot_boundedBy q s.axis s.root h s.served

/-- `NTree.size` **is** a row count: `Nock.Walk.bfsForest_length` at a one-tree forest. -/
theorem size_eq_bfsForest_length {LT : Type} (t : NTree LT) :
    t.size = (bfsForest [t]).length := by
  rw [bfsForest_length]
  simp [totalSize]

/-- The service root's leaf bound, read as a memory **row count** of the region's own walk. -/
theorem leaves_recoveredRootNoun_le_rows {z : K} (q : ℕ) {d : MemoryTable.DTmem K}
    {region : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : MemoryFingerprintStructure z
      (NTree.node (MemoryTable.MState.read_root, d) [region])) :
    (recoveredRootNoun q (NTree.node (MemoryTable.MState.read_root, d) [region])).leaves
      ≤ (bfsForest [(NTree.node (MemoryTable.MState.read_root, d) [region] :
          NTree (MemoryTable.MState × MemoryTable.DTmem K))]).length := by
  rw [← size_eq_bfsForest_length]
  exact leaves_recoveredLabelling_le_size h q 1

end Leaves

/-! ### The same two bounds at a `PricedRecordWitness` -/

section WitnessLeaves

variable {cfg : ExactConfig F K} {exec : ExactExecution cfg}

/-- The served root noun of a priced witness has at most `region.size + 1` leaves — the node count
of the committed region plus its own `read_root` row. -/
theorem leaves_servedRoot_le {q : ℕ} {r : ComputeTable.MemRec K}
    (W : PricedRecordWitness cfg exec q r) :
    W.servedRoot.leaves ≤ W.region.size + 1 := by
  have h := leaves_recoveredLabelling_le_size W.fingerprints q 1
  have hsz : (NTree.node (MemoryTable.MState.read_root, W.rootData) [W.region]).size
      = 1 + W.region.size := by
    simp [NTree.size]
  rw [hsz] at h
  have : W.servedRoot
      = GlobalCarryAxis.nounOf
          (recoveredLabelling q (.node (.read_root, W.rootData) [W.region]) 1) := rfl
  rw [this]
  omega

/-- And so does the served child noun, through `Noun.slot`. -/
theorem leaves_servedChild_le [Fintype K] [DecidableEq K] {q : ℕ} {r : ComputeTable.MemRec K}
    (hz : cfg.challenges.z ≠ 0) (W : PricedRecordWitness cfg exec q r)
    (hvalid : ExactMemoryAxisValidity cfg exec) :
    W.servedChild.leaves ≤ W.region.size + 1 :=
  le_trans (TraceGen.slot_leaves_le W.addr W.servedRoot (W.realizes_and_served hz hvalid).2)
    (leaves_servedRoot_le W)

/-- `FieldEmbedding.BoundedBy` on the served root is *also* free: it is one projection of
`recoveredLabelling_spec`, whose only inputs are `z ≠ 0` and the witness's own two committed
fields. -/
theorem boundedBy_servedRoot {q : ℕ} {r : ComputeTable.MemRec K}
    (hz : cfg.challenges.z ≠ 0) (W : PricedRecordWitness cfg exec q r) :
    FieldEmbedding.BoundedBy q W.servedRoot :=
  (recoveredLabelling_spec hz W.fingerprints W.leaves 1).2.2.1

/-- …and on the served child, through `Noun.slot`. -/
theorem boundedBy_servedChild [Fintype K] [DecidableEq K] {q : ℕ} {r : ComputeTable.MemRec K}
    (hz : cfg.challenges.z ≠ 0) (W : PricedRecordWitness cfg exec q r)
    (hvalid : ExactMemoryAxisValidity cfg exec) :
    FieldEmbedding.BoundedBy q W.servedChild :=
  FieldEmbedding.slot_boundedBy q W.addr W.servedRoot (boundedBy_servedRoot hz W)
    (W.realizes_and_served hz hvalid).2

end WitnessLeaves


/-! ## §B.  A concrete index set for the sixth event, bounded by the row counts

`GenGlobalCollision.globalBadSeeds_card_le` costs `S.card · (S.card − 1) · (2Λ − 1)`, so the sixth
event is only effective if `S.card` is bounded by trace data.  It cannot be read off `exec` while
`ServedSlotCovers` keeps the service existential, so §B *names* the served nouns first: two
functions `rootOf`/`childOf` on committed rows, which the assignment below is required to hit. -/

section IndexSet

/-- The committed compute rows whose state consumes a served record — OP0's `mr2` and OP9's `mr3`.  Exactly the rows `ServedSlotCovers` quantifies over. -/
def servedStateRows (rows : List (ComputeTable.State × ComputeTable.DTcomp K)) :
    List (ComputeTable.State × ComputeTable.DTcomp K) :=
  rows.filter fun row =>
    decide (row.2.2.1.state = ComputeTable.State.s0) ||
      decide (row.2.2.1.state = ComputeTable.State.s9)

theorem length_servedStateRows_le (rows : List (ComputeTable.State × ComputeTable.DTcomp K)) :
    (servedStateRows rows).length ≤ rows.length :=
  List.length_filter_le _ _

theorem mem_servedStateRows {rows : List (ComputeTable.State × ComputeTable.DTcomp K)}
    {row : ComputeTable.State × ComputeTable.DTcomp K} (hrow : row ∈ rows)
    (hst : row.2.2.1.state = ComputeTable.State.s0 ∨
      row.2.2.1.state = ComputeTable.State.s9) :
    row ∈ servedStateRows rows := by
  refine List.mem_filter.mpr ⟨hrow, ?_⟩
  rcases hst with h | h <;> simp [h]

/-- **The service half of the index set**: the named served nouns of the OP0/OP9 rows, and nothing
else.  Two entries per such row. -/
def serviceNounTable (rows : List (ComputeTable.State × ComputeTable.DTcomp K))
    (rootOf childOf : ComputeTable.State × ComputeTable.DTcomp K → Noun) : Finset Noun :=
  ((servedStateRows rows).map rootOf).toFinset ∪ ((servedStateRows rows).map childOf).toFinset

theorem mem_serviceNounTable_root {rows : List (ComputeTable.State × ComputeTable.DTcomp K)}
    {rootOf childOf : ComputeTable.State × ComputeTable.DTcomp K → Noun}
    {row : ComputeTable.State × ComputeTable.DTcomp K} (hrow : row ∈ rows)
    (hst : row.2.2.1.state = ComputeTable.State.s0 ∨
      row.2.2.1.state = ComputeTable.State.s9) :
    rootOf row ∈ serviceNounTable rows rootOf childOf :=
  Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem (mem_servedStateRows hrow hst)))

theorem mem_serviceNounTable_child {rows : List (ComputeTable.State × ComputeTable.DTcomp K)}
    {rootOf childOf : ComputeTable.State × ComputeTable.DTcomp K → Noun}
    {row : ComputeTable.State × ComputeTable.DTcomp K} (hrow : row ∈ rows)
    (hst : row.2.2.1.state = ComputeTable.State.s0 ∨
      row.2.2.1.state = ComputeTable.State.s9) :
    childOf row ∈ serviceNounTable rows rootOf childOf :=
  Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map_of_mem (mem_servedStateRows hrow hst)))

theorem card_serviceNounTable_le (rows : List (ComputeTable.State × ComputeTable.DTcomp K))
    (rootOf childOf : ComputeTable.State × ComputeTable.DTcomp K → Noun) :
    (serviceNounTable rows rootOf childOf).card ≤ 2 * (servedStateRows rows).length := by
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 := List.toFinset_card_le ((servedStateRows rows).map rootOf)
  have h2 := List.toFinset_card_le ((servedStateRows rows).map childOf)
  simp only [List.length_map] at h1 h2
  omega

/-- A length bound for `flatMap`, which is the whole of the skeleton-side count. -/
theorem length_flatMap_le {α β : Type} (n : ℕ) :
    ∀ (l : List α) (f : α → List β), (∀ a ∈ l, (f a).length ≤ n) →
      (l.flatMap f).length ≤ n * l.length := by
  intro l f
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro h
      have ha : (f a).length ≤ n := h a (by simp)
      have ht : (t.flatMap f).length ≤ n * t.length := ih fun b hb => h b (by simp [hb])
      have : ((a :: t).flatMap f).length = (f a).length + (t.flatMap f).length := by
        simp [List.flatMap_cons]
      rw [this, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- The `root`/`child` nouns of every active memory record of one committed skeleton row.  All of
them, because that is what `GenGlobalCollision.SkeletonRecordNounsIn` asks for — up to
`Nock.Framework.recordCount ≤ 3` records, two nouns each. -/
def skeletonRecordNounList (s : ComputeRowSkeleton) : List Noun :=
  (List.finRange 3).flatMap fun i : Fin 3 =>
    if h : (i : ℕ) < Nock.Framework.recordCount s.state then
      [(s.memoryRecord i h).root, (s.memoryRecord i h).child]
    else []

theorem length_skeletonRecordNounList_le (s : ComputeRowSkeleton) :
    (skeletonRecordNounList s).length ≤ 6 := by
  have h := length_flatMap_le (α := Fin 3) (β := Noun) 2 (List.finRange 3)
    (fun i : Fin 3 =>
      if h : (i : ℕ) < Nock.Framework.recordCount s.state then
        [(s.memoryRecord i h).root, (s.memoryRecord i h).child]
      else [])
    (by
      intro i _
      by_cases hi : (i : ℕ) < Nock.Framework.recordCount s.state
      · simp [hi]
      · simp [hi])
  simpa [skeletonRecordNounList] using h

theorem mem_skeletonRecordNounList (s : ComputeRowSkeleton) (i : Fin 3)
    (h : (i : ℕ) < Nock.Framework.recordCount s.state) :
    (s.memoryRecord i h).root ∈ skeletonRecordNounList s ∧
      (s.memoryRecord i h).child ∈ skeletonRecordNounList s := by
  constructor <;>
    refine List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩ <;> simp [h]

/-- **The skeleton half of the index set.** -/
def skeletonNounTable (S : SemanticSkeleton) : Finset Noun :=
  ((computeSkeletonRows S).flatMap skeletonRecordNounList).toFinset

theorem card_skeletonNounTable_le (S : SemanticSkeleton) :
    (skeletonNounTable S).card ≤ 6 * (computeSkeletonRows S).length := by
  refine le_trans (List.toFinset_card_le _) ?_
  exact length_flatMap_le 6 _ _ fun s _ => length_skeletonRecordNounList_le s

theorem mem_skeletonNounTable {S : SemanticSkeleton} {s : ComputeRowSkeleton}
    (hs : s ∈ computeSkeletonRows S) (i : Fin 3)
    (h : (i : ℕ) < Nock.Framework.recordCount s.state) :
    (s.memoryRecord i h).root ∈ skeletonNounTable S ∧
      (s.memoryRecord i h).child ∈ skeletonNounTable S := by
  obtain ⟨hr, hc⟩ := mem_skeletonRecordNounList s i h
  exact ⟨List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨s, hs, hr⟩),
    List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨s, hs, hc⟩)⟩

/-- **The index set of the sixth event, entirely in committed trace data.**  Nothing here mentions
a seed, a coin, an `ExactExecutionSemanticData` or a `Service`; `rootOf`/`childOf` are the *names*
of the served nouns and the assignment below is what ties them to real witnesses. -/
def traceNounTable (S : SemanticSkeleton)
    (rows : List (ComputeTable.State × ComputeTable.DTcomp K))
    (rootOf childOf : ComputeTable.State × ComputeTable.DTcomp K → Noun) : Finset Noun :=
  skeletonNounTable S ∪ serviceNounTable rows rootOf childOf

/-- **The bound residual (c) asked for.**  `2` per OP0/OP9 committed row for the service nouns and
`6` per committed skeleton row for the record nouns.

The `6` is `SkeletonRecordNounsIn`'s own arithmetic, not slack: it quantifies over *all*
`recordCount ≤ 3` records of every row.  `GenGlobalCollision.composed_numerator_at_batch258_tight`'s
docstring figure `4 · (#OP0 + #OP9)` counts only the served slot's record, which is less than the
predicate asks for. -/
theorem card_traceNounTable_le (S : SemanticSkeleton)
    (rows : List (ComputeTable.State × ComputeTable.DTcomp K))
    (rootOf childOf : ComputeTable.State × ComputeTable.DTcomp K → Noun) :
    (traceNounTable S rows rootOf childOf).card
      ≤ 6 * (computeSkeletonRows S).length + 2 * rows.length := by
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 := card_skeletonNounTable_le S
  have h2 := card_serviceNounTable_le rows rootOf childOf
  have h3 := length_servedStateRows_le rows
  have h4 : 2 * (servedStateRows rows).length ≤ 2 * rows.length := by omega
  omega

theorem mem_traceNounTable_of_service {S : SemanticSkeleton}
    {rows : List (ComputeTable.State × ComputeTable.DTcomp K)}
    {rootOf childOf : ComputeTable.State × ComputeTable.DTcomp K → Noun}
    {row : ComputeTable.State × ComputeTable.DTcomp K} (hrow : row ∈ rows)
    (hst : row.2.2.1.state = ComputeTable.State.s0 ∨
      row.2.2.1.state = ComputeTable.State.s9) :
    rootOf row ∈ traceNounTable S rows rootOf childOf ∧
      childOf row ∈ traceNounTable S rows rootOf childOf :=
  ⟨Finset.mem_union_right _ (mem_serviceNounTable_root hrow hst),
   Finset.mem_union_right _ (mem_serviceNounTable_child hrow hst)⟩

/-- `hin` of `GenGlobalCollision.slotSemantics_of_serviceCovers`, at the concrete table.  The only
premise left is the axis window `axis < q`, which is a no-wraparound condition on committed `ℕ`
data. -/
theorem skeletonRecordNounsIn_traceNounTable {q : ℕ} (S : SemanticSkeleton)
    (rows : List (ComputeTable.State × ComputeTable.DTcomp K))
    (rootOf childOf : ComputeTable.State × ComputeTable.DTcomp K → Noun)
    (hax : ∀ s ∈ computeSkeletonRows S, ∀ (i : Fin 3)
      (h : (i : ℕ) < Nock.Framework.recordCount s.state), (s.memoryRecord i h).axis < q) :
    ∀ s ∈ computeSkeletonRows S,
      GenGlobalCollision.SkeletonRecordNounsIn q (traceNounTable S rows rootOf childOf) s := by
  intro s hs i h
  obtain ⟨hr, hc⟩ := mem_skeletonNounTable hs i h
  exact ⟨Finset.mem_union_left _ hr, Finset.mem_union_left _ hc, hax s hs i h⟩

variable [Fintype K] [DecidableEq K]

/-- **The sixth event, priced in trace data alone.**  `globalBadSeeds` at the concrete table costs
at most `B(B−1)(2Λ−1)` with `B = 6·#skeleton rows + 2·#compute rows` — no quantity in the numerator
is chosen by the prover beyond the committed row counts and the leaf window. -/
theorem globalBadSeeds_card_le_traceNounTable (Λ : ℕ) (S : SemanticSkeleton)
    (rows : List (ComputeTable.State × ComputeTable.DTcomp K))
    (rootOf childOf : ComputeTable.State × ComputeTable.DTcomp K → Noun)
    (hleaf : ∀ n ∈ traceNounTable S rows rootOf childOf, n.leaves ≤ Λ) :
    (GenGlobalCollision.globalBadSeeds (K := K) (traceNounTable S rows rootOf childOf)).card
      ≤ (6 * (computeSkeletonRows S).length + 2 * rows.length) *
          (6 * (computeSkeletonRows S).length + 2 * rows.length - 1) * (2 * Λ - 1) := by
  refine le_trans (GenGlobalCollision.globalBadSeeds_card_le Λ _ hleaf) ?_
  have hB := card_traceNounTable_le S rows rootOf childOf
  exact Nat.mul_le_mul (Nat.mul_le_mul hB (Nat.sub_le_sub_right hB 1)) (le_refl _)

end IndexSet


/-! ## §C.  Residual (d): `Service.timestamp` is a compute-side column

`Service.record ∈ exec.rawRequests` is a **compute** record, and the compute specializer scales by
the committed line origin.  `GenTimestampClosed`'s free closure is about the **memory**
specializer, which is unscaled.  So there is no supplier at production scope; what there is, is a
reduction to one scalar per row, and a transport from a timestamp match with the memory side. -/

section Timestamp

open Nock.NockVMROM.Thm54.SemanticTimestampStrategy

/-- **(d), reduced to one scalar.**  If the row's own line number `ln_prev` is in the orbit of `α`,
every active record timestamp of that row is.  This is
`SemanticTimestampStrategy.compute_ts_eq_pow_of_origin` with the ladder condition
`lnPrevExponent ≤ recordExponent i` **dropped**: closure only needs *some* exponent, and the
truncated subtraction supplies one either way. -/
theorem computeRecord_timestampClosed_of_lnPrev {α : K} {stamp : ComputeTimestampRow}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (htime : ComputeTimestampSpecializesAt α stamp row)
    {k : ℕ} (hln : row.2.2.1.ln_prev = α ^ k)
    (i : Fin 3) (hact : computeMemRecKind stamp.state i = FPSlotKind.active) :
    TimestampClosedAt α (computeMemRec row.2.2.1 i).ts := by
  refine ⟨k + (stamp.recordExponent i - stamp.lnPrevExponent), ?_⟩
  have ht := htime.2.2.2.2.1 i
  rw [if_pos hact] at ht
  rw [ht, hln, pow_add]

/-- The line column itself closes the same way, so the whole row's timestamp family is one scalar's
worth of freedom. -/
theorem computeLn_timestampClosed_of_lnPrev {α : K} {stamp : ComputeTimestampRow}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (htime : ComputeTimestampSpecializesAt α stamp row)
    {k : ℕ} (hln : row.2.2.1.ln_prev = α ^ k) :
    TimestampClosedAt α row.2.2.1.ln := by
  refine ⟨k + (stamp.lnExponent - stamp.lnPrevExponent), ?_⟩
  rw [htime.2.2.2.1, hln, pow_add]

end Timestamp

section ProductionTimestamp

variable [Fintype K] [DecidableEq K] [charRing : CharP K (ringChar K)]

open Nock.NockVMROM.Thm54.ProductionP8Containment

/-- **(d) from the timestamp column of the IO record match.**  A compute-side timestamp that equals
the timestamp of an *active* memory row of the same specialized execution is closed, because
`GenTimestampClosed.productionStrategy_timestampClosed` gives the memory side for free.

This premise is a **projection of residual (b)** onto the
`ts` column: it is what the LogUp request/response multiset match would deliver.  It is carried
here, not proved. -/
theorem timestampClosed_of_servedMatch (T : ProductionStrategy F K)
    (z : K) (hz : z ≠ 0) (α lmb : K) {ts : K}
    (j : Fin (T.specializedCfg z hz α lmb).memRows)
    (hact : memoryMemRecKind ((T.specializedExec z hz α lmb).memoryRowAt j).1 = FPSlotKind.active)
    (hmatch : ts = ((T.specializedExec z hz α lmb).memoryRowAt j).2.2.mem.ts) :
    TimestampClosedAt (T.specializedCfg z hz α lmb).challenges.α ts := by
  obtain ⟨e, he⟩ := GenTimestampClosed.productionStrategy_timestampClosed T z hz α lmb j hact
  exact ⟨e, hmatch.trans he⟩

/-- The two served slots' form of that premise, keyed exactly on the rows `ServedSlotCovers`
quantifies over. -/
def ServedRequestTimestampMatched (T : ProductionStrategy F K)
    (z : K) (hz : z ≠ 0) (α lmb : K) : Prop :=
  (∀ row ∈ (T.specializedExec z hz α lmb).computeRows,
      row.2.2.1.state = ComputeTable.State.s0 →
      ∃ j : Fin (T.specializedCfg z hz α lmb).memRows,
        memoryMemRecKind ((T.specializedExec z hz α lmb).memoryRowAt j).1 = FPSlotKind.active ∧
          (computeMemRec row.2.2.1 1).ts
            = ((T.specializedExec z hz α lmb).memoryRowAt j).2.2.mem.ts) ∧
  (∀ row ∈ (T.specializedExec z hz α lmb).computeRows,
      row.2.2.1.state = ComputeTable.State.s9 →
      ∃ j : Fin (T.specializedCfg z hz α lmb).memRows,
        memoryMemRecKind ((T.specializedExec z hz α lmb).memoryRowAt j).1 = FPSlotKind.active ∧
          (computeMemRec row.2.2.1 2).ts
            = ((T.specializedExec z hz α lmb).memoryRowAt j).2.2.mem.ts)

theorem timestampClosed_s0_of_matched {T : ProductionStrategy F K}
    {z : K} {hz : z ≠ 0} {α lmb : K} (M : ServedRequestTimestampMatched T z hz α lmb) :
    ∀ row ∈ (T.specializedExec z hz α lmb).computeRows,
      row.2.2.1.state = ComputeTable.State.s0 →
      TimestampClosedAt (T.specializedCfg z hz α lmb).challenges.α
        (computeMemRec row.2.2.1 1).ts := by
  intro row hrow hst
  obtain ⟨j, hact, hmatch⟩ := M.1 row hrow hst
  exact timestampClosed_of_servedMatch T z hz α lmb j hact hmatch

theorem timestampClosed_s9_of_matched {T : ProductionStrategy F K}
    {z : K} {hz : z ≠ 0} {α lmb : K} (M : ServedRequestTimestampMatched T z hz α lmb) :
    ∀ row ∈ (T.specializedExec z hz α lmb).computeRows,
      row.2.2.1.state = ComputeTable.State.s9 →
      TimestampClosedAt (T.specializedCfg z hz α lmb).challenges.α
        (computeMemRec row.2.2.1 2).ts := by
  intro row hrow hst
  obtain ⟨j, hact, hmatch⟩ := M.2 row hrow hst
  exact timestampClosed_of_servedMatch T z hz α lmb j hact hmatch

end ProductionTimestamp


/-! ## §D.  The assignment, and the composed statements

`ServedSlotCovers` keeps its service existential, so nothing can read an index set off it.  A
`PricedAssignment` is the same supply with the served nouns **named** by two functions on committed
rows — which is what makes §B's table definable — plus the two window conditions.  It carries no
timestamp: that is residual (d) and enters separately. -/

section Assignment

variable [Fintype K] [DecidableEq K]
variable {cfg : ExactConfig F K} {exec : ExactExecution cfg}

theorem mem_of_mem_servedStateRows
    {rows : List (ComputeTable.State × ComputeTable.DTcomp K)}
    {row : ComputeTable.State × ComputeTable.DTcomp K} (h : row ∈ servedStateRows rows) :
    row ∈ rows ∧ (row.2.2.1.state = ComputeTable.State.s0 ∨
      row.2.2.1.state = ComputeTable.State.s9) := by
  obtain ⟨hrow, hb⟩ := List.mem_filter.mp h
  refine ⟨hrow, ?_⟩
  rcases (Bool.or_eq_true _ _).mp hb with hb' | hb'
  · exact Or.inl (of_decide_eq_true hb')
  · exact Or.inr (of_decide_eq_true hb')

/-- **A named, windowed service assignment.**  Per OP0/OP9 committed row: a
`GenAxisBoundaryPriced.PricedRecordWitness` whose served nouns are `rootOf row` / `childOf row`,
whose Nock address fits the cast window `q`, and whose committed region has at most `Λ - 1` rows.

The `region.size + 1 ≤ Λ` conjunct is the leaf window read on committed trace
data: by `Nock.Walk.bfsForest_length` the region's node count is a memory row count, and §A turns
it into the leaf bound `globalBadSeeds_card_le` wants. -/
def PricedAssignment (cfg : ExactConfig F K) (exec : ExactExecution cfg) (q Λ : ℕ)
    (rootOf childOf : ComputeTable.State × ComputeTable.DTcomp K → Noun) : Prop :=
  (∀ row ∈ exec.computeRows, row.2.2.1.state = ComputeTable.State.s0 →
      ∃ W : PricedRecordWitness cfg exec q (computeMemRec row.2.2.1 1),
        W.servedRoot = rootOf row ∧ W.servedChild = childOf row ∧
          W.addr < q ∧ W.region.size + 1 ≤ Λ) ∧
  (∀ row ∈ exec.computeRows, row.2.2.1.state = ComputeTable.State.s9 →
      ∃ W : PricedRecordWitness cfg exec q (computeMemRec row.2.2.1 2),
        W.servedRoot = rootOf row ∧ W.servedChild = childOf row ∧
          W.addr < q ∧ W.region.size + 1 ≤ Λ)

/-- **The service side of `hN` is discharged.**  `GenGlobalCollision`'s residual 2 — "the leaf
bound on the prover's nouns is carried, not derived" — is derived here, from the region-size window
alone.  No `RootTrace.subject`, no commitment to a subject noun. -/
theorem serviceNounTable_leaves_le {q Λ : ℕ}
    {rootOf childOf : ComputeTable.State × ComputeTable.DTcomp K → Noun}
    (hz : cfg.challenges.z ≠ 0) (hvalid : ExactMemoryAxisValidity cfg exec)
    (A : PricedAssignment cfg exec q Λ rootOf childOf) :
    ∀ n ∈ serviceNounTable exec.computeRows rootOf childOf, n.leaves ≤ Λ := by
  intro n hn
  rcases Finset.mem_union.mp hn with hn | hn
  · obtain ⟨row, hrowf, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hn)
    obtain ⟨hrow, hst⟩ := mem_of_mem_servedStateRows hrowf
    rcases hst with hst | hst
    · obtain ⟨W, hR, -, -, hsz⟩ := A.1 row hrow hst
      exact hR ▸ le_trans (leaves_servedRoot_le W) hsz
    · obtain ⟨W, hR, -, -, hsz⟩ := A.2 row hrow hst
      exact hR ▸ le_trans (leaves_servedRoot_le W) hsz
  · obtain ⟨row, hrowf, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hn)
    obtain ⟨hrow, hst⟩ := mem_of_mem_servedStateRows hrowf
    rcases hst with hst | hst
    · obtain ⟨W, -, hC, -, hsz⟩ := A.1 row hrow hst
      exact hC ▸ le_trans (leaves_servedChild_le hz W hvalid) hsz
    · obtain ⟨W, -, hC, -, hsz⟩ := A.2 row hrow hst
      exact hC ▸ le_trans (leaves_servedChild_le hz W hvalid) hsz

/-- And so is `hbN` on the service side — `FieldEmbedding.BoundedBy q` needs nothing but `z ≠ 0`
and the witness's own committed fields. -/
theorem serviceNounTable_boundedBy {q Λ : ℕ}
    {rootOf childOf : ComputeTable.State × ComputeTable.DTcomp K → Noun}
    (hz : cfg.challenges.z ≠ 0) (hvalid : ExactMemoryAxisValidity cfg exec)
    (A : PricedAssignment cfg exec q Λ rootOf childOf) :
    ∀ n ∈ serviceNounTable exec.computeRows rootOf childOf,
      FieldEmbedding.BoundedBy q n := by
  intro n hn
  rcases Finset.mem_union.mp hn with hn | hn
  · obtain ⟨row, hrowf, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hn)
    obtain ⟨hrow, hst⟩ := mem_of_mem_servedStateRows hrowf
    rcases hst with hst | hst
    · obtain ⟨W, hR, -, -, -⟩ := A.1 row hrow hst
      exact hR ▸ boundedBy_servedRoot hz W
    · obtain ⟨W, hR, -, -, -⟩ := A.2 row hrow hst
      exact hR ▸ boundedBy_servedRoot hz W
  · obtain ⟨row, hrowf, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hn)
    obtain ⟨hrow, hst⟩ := mem_of_mem_servedStateRows hrowf
    rcases hst with hst | hst
    · obtain ⟨W, -, hC, -, -⟩ := A.1 row hrow hst
      exact hC ▸ boundedBy_servedChild hz W hvalid
    · obtain ⟨W, -, hC, -, -⟩ := A.2 row hrow hst
      exact hC ▸ boundedBy_servedChild hz W hvalid

/-- The whole table's leaf bound: the service half from the assignment, the skeleton half from a
measurement of the committed skeleton. -/
theorem traceNounTable_leaves_le {q Λ : ℕ} {S : SemanticSkeleton}
    {rootOf childOf : ComputeTable.State × ComputeTable.DTcomp K → Noun}
    (hz : cfg.challenges.z ≠ 0) (hvalid : ExactMemoryAxisValidity cfg exec)
    (A : PricedAssignment cfg exec q Λ rootOf childOf)
    (hskel : ∀ n ∈ skeletonNounTable S, n.leaves ≤ Λ) :
    ∀ n ∈ traceNounTable S exec.computeRows rootOf childOf, n.leaves ≤ Λ := by
  intro n hn
  rcases Finset.mem_union.mp hn with hn | hn
  · exact hskel n hn
  · exact serviceNounTable_leaves_le hz hvalid A n hn

theorem traceNounTable_boundedBy {q Λ : ℕ} {S : SemanticSkeleton}
    {rootOf childOf : ComputeTable.State × ComputeTable.DTcomp K → Noun}
    (hz : cfg.challenges.z ≠ 0) (hvalid : ExactMemoryAxisValidity cfg exec)
    (A : PricedAssignment cfg exec q Λ rootOf childOf)
    (hskel : ∀ n ∈ skeletonNounTable S, FieldEmbedding.BoundedBy q n) :
    ∀ n ∈ traceNounTable S exec.computeRows rootOf childOf,
      FieldEmbedding.BoundedBy q n := by
  intro n hn
  rcases Finset.mem_union.mp hn with hn | hn
  · exact hskel n hn
  · exact serviceNounTable_boundedBy hz hvalid A n hn

/-- `hts0`/`hts9` are residual (d) and nothing else. -/
theorem servedSlotCovers_of_pricedAssignment {q Λ : ℕ} {S : SemanticSkeleton}
    {rootOf childOf : ComputeTable.State × ComputeTable.DTcomp K → Noun}
    (hz : cfg.challenges.z ≠ 0) (hvalid : ExactMemoryAxisValidity cfg exec)
    (A : PricedAssignment cfg exec q Λ rootOf childOf)
    (hts0 : ∀ row ∈ exec.computeRows, row.2.2.1.state = ComputeTable.State.s0 →
      TimestampClosedAt cfg.challenges.α (computeMemRec row.2.2.1 1).ts)
    (hts9 : ∀ row ∈ exec.computeRows, row.2.2.1.state = ComputeTable.State.s9 →
      TimestampClosedAt cfg.challenges.α (computeMemRec row.2.2.1 2).ts) :
    GenGlobalCollision.ServedSlotCovers exec q
      (traceNounTable S exec.computeRows rootOf childOf) := by
  refine servedSlotCovers_of_priced_witnesses hz hvalid ?_ ?_
  · intro row hrow hst
    obtain ⟨W, hR, hC, haq, -⟩ := A.1 row hrow hst
    obtain ⟨e, he⟩ := hts0 row hrow hst
    obtain ⟨hmR, hmC⟩ :=
      mem_traceNounTable_of_service (S := S) (rootOf := rootOf) (childOf := childOf)
        hrow (Or.inl hst)
    exact ⟨W, e, he, hR ▸ hmR, hC ▸ hmC, haq⟩
  · intro row hrow hst
    obtain ⟨W, hR, hC, haq, -⟩ := A.2 row hrow hst
    obtain ⟨e, he⟩ := hts9 row hrow hst
    obtain ⟨hmR, hmC⟩ :=
      mem_traceNounTable_of_service (S := S) (rootOf := rootOf) (childOf := childOf)
        hrow (Or.inr hst)
    exact ⟨W, e, he, hR ▸ hmR, hC ▸ hmC, haq⟩

/-- **The served half of `hop` at an arbitrary committed skeleton, with the sixth event's index set
bounded by the row counts.**  `GenGlobalCollision.slotSemantics_of_serviceCovers` with every
noun-table side condition discharged from §A/§B: `hbN` and `hcov` from the assignment, `hin` from
the axis window, and the `Λ` leaf bound available as `traceNounTable_leaves_le`.

Still carried, and named: `hgood` (the sixth event's own exclusion, now priced by
`globalBadSeeds_card_le_traceNounTable`), `hrec` (the record equations), `binds`, and residual (d)
as `hts0`/`hts9`. -/
theorem slotSemantics_of_pricedAssignment {q Λ : ℕ} {S : SemanticSkeleton}
    {rootOf childOf : ComputeTable.State × ComputeTable.DTcomp K → Noun}
    (hz : cfg.challenges.z ≠ 0) (hvalid : ExactMemoryAxisValidity cfg exec)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (A : PricedAssignment cfg exec q Λ rootOf childOf)
    (hskel : ∀ n ∈ skeletonNounTable S, FieldEmbedding.BoundedBy q n)
    (hax : ∀ s ∈ computeSkeletonRows S, ∀ (i : Fin 3)
      (h : (i : ℕ) < Nock.Framework.recordCount s.state), (s.memoryRecord i h).axis < q)
    (hts0 : ∀ row ∈ exec.computeRows, row.2.2.1.state = ComputeTable.State.s0 →
      TimestampClosedAt cfg.challenges.α (computeMemRec row.2.2.1 1).ts)
    (hts9 : ∀ row ∈ exec.computeRows, row.2.2.1.state = ComputeTable.State.s9 →
      TimestampClosedAt cfg.challenges.α (computeMemRec row.2.2.1 2).ts)
    (hgood : cfg.challenges.z ∉
      GenGlobalCollision.globalBadSeeds (K := K)
        (traceNounTable S exec.computeRows rootOf childOf))
    (hrec : ∀ s ∈ computeSkeletonRows S, ServedLookupBridge.SkeletonRecordEquations s)
    (binds : BindsAt cfg.challenges.z S cfg exec) :
    ∀ s ∈ computeSkeletonRows S, ServedLookupBridge.SkeletonSlotSemantics s :=
  GenGlobalCollision.slotSemantics_of_serviceCovers rfl hgood hcast
    (traceNounTable_boundedBy hz hvalid A hskel)
    (servedSlotCovers_of_pricedAssignment hz hvalid A hts0 hts9)
    (skeletonRecordNounsIn_traceNounTable S exec.computeRows rootOf childOf hax)
    hrec binds

/-- **Naming the served nouns is free.**  A `PricedAssignment` looks stronger than the witness
supply `servedSlotCovers_of_priced_witnesses` asks for, because it fixes two *functions* on rows.
It is not: classical choice over the committed row list produces them.  So bounding `S.card` by
`card_traceNounTable_le` costs nothing over the existential form, and residual (c) is closed rather
than traded. -/
theorem exists_pricedAssignment_of_witnesses {q Λ : ℕ}
    (h0 : ∀ row ∈ exec.computeRows, row.2.2.1.state = ComputeTable.State.s0 →
        ∃ W : PricedRecordWitness cfg exec q (computeMemRec row.2.2.1 1),
          W.addr < q ∧ W.region.size + 1 ≤ Λ)
    (h9 : ∀ row ∈ exec.computeRows, row.2.2.1.state = ComputeTable.State.s9 →
        ∃ W : PricedRecordWitness cfg exec q (computeMemRec row.2.2.1 2),
          W.addr < q ∧ W.region.size + 1 ≤ Λ) :
    ∃ rootOf childOf : ComputeTable.State × ComputeTable.DTcomp K → Noun,
      PricedAssignment cfg exec q Λ rootOf childOf := by
  classical
  have hall : ∀ row : ComputeTable.State × ComputeTable.DTcomp K, ∃ p : Noun × Noun,
      row ∈ exec.computeRows →
        ((row.2.2.1.state = ComputeTable.State.s0 →
            ∃ W : PricedRecordWitness cfg exec q (computeMemRec row.2.2.1 1),
              W.servedRoot = p.1 ∧ W.servedChild = p.2 ∧
                W.addr < q ∧ W.region.size + 1 ≤ Λ) ∧
          (row.2.2.1.state = ComputeTable.State.s9 →
            ∃ W : PricedRecordWitness cfg exec q (computeMemRec row.2.2.1 2),
              W.servedRoot = p.1 ∧ W.servedChild = p.2 ∧
                W.addr < q ∧ W.region.size + 1 ≤ Λ)) := by
    intro row
    by_cases hm : row ∈ exec.computeRows
    · by_cases hs0 : row.2.2.1.state = ComputeTable.State.s0
      · obtain ⟨W, ha, hsz⟩ := h0 row hm hs0
        refine ⟨(W.servedRoot, W.servedChild), fun _ => ⟨fun _ => ⟨W, rfl, rfl, ha, hsz⟩, ?_⟩⟩
        intro hs9
        rw [hs0] at hs9
        exact absurd hs9 (by decide)
      · by_cases hs9 : row.2.2.1.state = ComputeTable.State.s9
        · obtain ⟨W, ha, hsz⟩ := h9 row hm hs9
          exact ⟨(W.servedRoot, W.servedChild),
            fun _ => ⟨fun h => absurd h hs0, fun _ => ⟨W, rfl, rfl, ha, hsz⟩⟩⟩
        · exact ⟨(Noun.atom 0, Noun.atom 0),
            fun _ => ⟨fun h => absurd h hs0, fun h => absurd h hs9⟩⟩
    · exact ⟨(Noun.atom 0, Noun.atom 0), fun h => absurd h hm⟩
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice hall
  exact ⟨fun row => (f row).1, fun row => (f row).2,
    fun row hrow hst => (hf row hrow).1 hst,
    fun row hrow hst => (hf row hrow).2 hst⟩

end Assignment

/-! ### The same at a production-accepted coin outside summand 4 -/

section Production

variable [Fintype K] [DecidableEq K] [charRing : CharP K (ringChar K)]

open Nock.NockVMROM.Thm54.ProductionP8Containment

/-- **The headline.**

No boundary premise, no polynomial identity, no new failure event: the axis half is still summand
4 of `FailureUnion`. -/
theorem servedSlotCovers_of_accepts_bounded
    (T : ProductionStrategy F K) (ω : JointCoins K) {lmb : K} (hz : nprSeed ω ≠ 0)
    (hacc : T.Accepts ω lmb)
    (hvalid : ExactMemoryAxisValidity
      (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb)
      (T.specializedExec (nprSeed ω) hz (alphaM ω) lmb))
    {q Λ : ℕ} {S : SemanticSkeleton}
    {rootOf childOf : ComputeTable.State × ComputeTable.DTcomp K → Noun}
    (hzc : (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb).challenges.z ≠ 0)
    (A : PricedAssignment (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb)
      (T.specializedExec (nprSeed ω) hz (alphaM ω) lmb) q Λ rootOf childOf)
    (M : ServedRequestTimestampMatched T (nprSeed ω) hz (alphaM ω) lmb) :
    GenGlobalCollision.ServedSlotCovers (T.specializedExec (nprSeed ω) hz (alphaM ω) lmb) q
      (traceNounTable S (T.specializedExec (nprSeed ω) hz (alphaM ω) lmb).computeRows
        rootOf childOf) :=
  servedSlotCovers_of_pricedAssignment hzc hvalid A
    (timestampClosed_s0_of_matched M) (timestampClosed_s9_of_matched M)

end Production

/-! ## §E.  Axiom receipts -/

section Receipts

#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.leaves_recoveredLabelling_le_size
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.Service.leaves_child_le_root
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.size_eq_bfsForest_length
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.leaves_recoveredRootNoun_le_rows
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.leaves_servedRoot_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.leaves_servedChild_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.boundedBy_servedRoot
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.boundedBy_servedChild
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.card_traceNounTable_le
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.globalBadSeeds_card_le_traceNounTable
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.skeletonRecordNounsIn_traceNounTable
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.computeRecord_timestampClosed_of_lnPrev
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.computeLn_timestampClosed_of_lnPrev
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.timestampClosed_of_servedMatch
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.serviceNounTable_leaves_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.serviceNounTable_boundedBy
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.traceNounTable_leaves_le
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.exists_pricedAssignment_of_witnesses
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.servedSlotCovers_of_pricedAssignment
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.slotSemantics_of_pricedAssignment
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping.servedSlotCovers_of_accepts_bounded

end Receipts

end

end Nock.NockVMROM.Thm54.TraceGen.GenServiceBookkeeping
