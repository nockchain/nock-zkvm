/-
  Nock/NockVMROM/Thm54/TraceGen/GenServedFromRecord.lean

  **X2, consumed: `Service.served` at a COMMITTED memory record.**

  `GenNounRecovery.MemoryNounRecovery.served_of_node` produces the literal `Service.served` shape
  `Noun.slot axis root = some child` at a node of the *recovered* labelling.  Its docstring
  (`GenNounRecovery.lean`, §C) names two things a consumer must add to reach a committed record —
  (i) that the record's committed `mem.axis` is the node's topological address, and (ii) that its
  committed `mem.child` is the node's `pt.noun`.  Both are supplied here: (ii) in §C from
  `MemoryTable.eqBlk` alone, (i) in §E from `AxisBatching.axis_batching_sound` through
  `AxisBridge`'s existing model bridge.  §D/§F compose them into the whole geometric content of a
  `ServedMemoryTrace.Service`, and §G reduces `GenGlobalCollision.ServedSlotCovers` — the premise
  `hop`'s served half needs — to a noun-free, slot-free statement about the committed memory walk.

  ## Map

  * §A  `NodeAddr` — the walk's own `1 / 2a / 2a+1` addressing.
  * §B  the recovered noun and `Noun.slot` at an addressed node — `served_of_node`, instantiated.
  * §C  (ii): `mem_root = parent` / `mem_child = parent`, one projection out of `Vmem`.
  * §D  the `Service` core with the axis premised.
  * §E  (i): `Relaxis` (a `K`-valued address) is the cast of the `ℕ` address; then the committed
        `mem.axis` column is that cast.
  * §F  §D with (i) discharged.
  * §G  `CommittedRecordWitness` and `ServedSlotCovers`.

  ## (ii) — `mem.child` is the node's `pt.noun`, and NO collision event is needed

  `MemoryTable.eqBlk` at `.verify_child` has
  `p.mem.child = p.pt.noun` as its fifth conjunct, and at `.read_root`
  `p.mem.root = p.pt.noun` as its fifth.  Both are **fingerprint** equations, and
  `OpcodeSemantics.RealizesMemRec` is a fingerprint-level predicate
  (`Realizes z fp n := fp = enc z n`, `OpcodeSemantics.lean:53`).  A `Service` **chooses** its own
  `root`/`child` nouns, so the recovered nouns can be handed to it directly: no noun *equality* is
  required, hence no application of `GenGlobalCollision.globalBadSeeds`.

  The collision event does still enter — but downstream and already counted, at
  `GenGlobalCollision.service_eq_of_bindMemRec`, where the *service's* nouns are identified with
  the *skeleton's*.  Constructing the service is free of it.

  ## (i) — the model bridge already exists; what is owed is a `ℕ`-vs-`K` address identification

  `AxisDescent.axis_correct` is stated over `AxisBatching.MTree K`, but the bridge from the walk
  model `NTree (MState × DTmem K)` to it is **already in the tree**: `AxisBridge.ofNTree`
  (`AxisBridge.lean:578`) reads a `MemWalk K` of real `MemoryTable.Pub` rows off exactly that
  `NTree`, `MemWalk.toMTree` (`:129`) reads the `AxisBatching.MTree K` off that, and
  `AxisBridge.committed_axis_correct_of_memtrace` (`:333`) already concludes
  `row.mem.axis = Relaxis e (...)` — committed axis = topological address — for a real
  `Vmem`-satisfying trace.  So no tree-model bridge is owed.

  What `Relaxis` returns is a **`K`**-valued address (`vaddr e c + 2^(vdep e c)`, the doubling
  performed in `K`), while `RealizesMemRec.axis_realizes` wants `r.axis = ((a : ℕ) : K)` for the
  `ℕ` address that `GlobalCarryAxis.axisOf` carries.  §E proves that identification along a
  descent path — `relaxis_eq_natCast` — so what was owed for (i) was the `ℕ`-vs-`K` step, not a
  model bridge.

  Two honest scope facts about §E.  So nothing here is stronger than the constraint set and nothing is unpriced;
  see `TraceGen/GenAxisBoundaryPriced.lean`, whose `servedSlotCovers_of_accepts` restates this
  module's headline with no boundary, no polynomial and no bad event in its statement.  And the served region's `read_root`
  must be the root of the walk `AxisRoute` is taken on, which is what makes the record's
  region-relative address coincide with the recovered labelling's absolute one; a `read_root`
  nested inside a larger walk needs the count-localization extended above the `read_root` node.

  ## What is NOT routed through

  The only inputs here
  are the committed memory walk, its per-row `MemoryTable.Vmem`, and the recovered labelling.

  Everything is `∀ z q tree` over an arbitrary field `K`; no hypothesis fixes an axis, a prime, a
  program or a fixture.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNounRecovery
import Nock.NockVMROM.Thm54.ServedMemoryTrace

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen.GenServedFromRecord

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen.GenNounRecovery

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## §A.  The topological address of a node of the committed walk

The paper's addresses are the globally anchored `1 / 2a / 2a+1` carry.  `NodeAddr a t b s` says: reading `t` as a subtree whose own root
sits at address `a`, the node `s` sits at address `b`.  The two axis-lookup states are
**transparent** — a `read_root` or `verify_child` row has fanout `1` and `pt.noun = lc.noun`, so it denotes the same noun at the same address as its single child.
Only `decompose` consumes an address bit, which is the paper's own recursion. -/

inductive NodeAddr :
    ℕ → NTree (MemoryTable.MState × MemoryTable.DTmem K) →
    ℕ → NTree (MemoryTable.MState × MemoryTable.DTmem K) → Prop
  | here (a : ℕ) (t : NTree (MemoryTable.MState × MemoryTable.DTmem K)) : NodeAddr a t a t
  | left {a b : ℕ} {d : MemoryTable.DTmem K}
      {l r s : NTree (MemoryTable.MState × MemoryTable.DTmem K)} :
      NodeAddr (2 * a) l b s → NodeAddr a (.node (.decompose, d) [l, r]) b s
  | right {a b : ℕ} {d : MemoryTable.DTmem K}
      {l r s : NTree (MemoryTable.MState × MemoryTable.DTmem K)} :
      NodeAddr (2 * a + 1) r b s → NodeAddr a (.node (.decompose, d) [l, r]) b s
  | read {a b : ℕ} {d : MemoryTable.DTmem K}
      {c s : NTree (MemoryTable.MState × MemoryTable.DTmem K)} :
      NodeAddr a c b s → NodeAddr a (.node (.read_root, d) [c]) b s
  | verify {a b : ℕ} {d : MemoryTable.DTmem K}
      {c s : NTree (MemoryTable.MState × MemoryTable.DTmem K)} :
      NodeAddr a c b s → NodeAddr a (.node (.verify_child, d) [c]) b s

namespace NodeAddr

/-- An addressed node is a node of the walk. -/
theorem inTree {a b : ℕ} {t s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : NodeAddr a t b s) : InTree t s := by
  induction h with
  | here a t => exact InTree.here t
  | left _ ih => exact InTree.sub (by simp) ih
  | right _ ih => exact InTree.sub (by simp) ih
  | read _ ih => exact InTree.sub (by simp) ih
  | verify _ ih => exact InTree.sub (by simp) ih

/-- The verifier-free fingerprint structure is inherited at an addressed node. -/
theorem fingerprintStructure {z : K} {a b : ℕ}
    {t s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : NodeAddr a t b s) (hstructure : MemoryFingerprintStructure z t) :
    MemoryFingerprintStructure z s := by
  induction h with
  | here a t => exact hstructure
  | left _ ih =>
      cases hstructure with
      | decompose _ _ _ _ hl _ => exact ih hl
  | right _ ih =>
      cases hstructure with
      | decompose _ _ _ _ _ hr => exact ih hr
  | read _ ih =>
      cases hstructure with
      | readRoot _ _ _ hc => exact ih hc
  | verify _ ih =>
      cases hstructure with
      | verifyChild _ _ _ hc => exact ih hc

/-- Bounded atom leaves are inherited at an addressed node. -/
theorem leafAtoms {q a b : ℕ}
    {t s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : NodeAddr a t b s) (hleaves : MemoryLeafAtomsRealized q t) :
    MemoryLeafAtomsRealized q s := by
  induction h with
  | here a t => exact hleaves
  | left _ ih => exact ih hleaves.1
  | right _ ih => exact ih hleaves.2
  | read _ ih => exact ih hleaves
  | verify _ ih => exact ih hleaves

/-- **The address descent is the labelling's subtree relation.**  Purely structural: it holds of
`GenNounRecovery.recoveredLabelling` for *any* walk, with no accepted-structure hypothesis, because
the labelling's recursion is the same recursion — `decompose` becomes a `MemTree.node` with the
`2a`/`2a+1` carry and the two axis-lookup rows are transparent. -/
-- the paper, 1301 (locally updatable)
theorem sub_recoveredLabelling {q a b : ℕ}
    {t s : NTree (MemoryTable.MState × MemoryTable.DTmem K)} (h : NodeAddr a t b s) :
    GlobalCarryAxis.Sub (recoveredLabelling q s b) (recoveredLabelling q t a) := by
  induction h with
  | here a t => exact GlobalCarryAxis.Sub.refl
  | left _ ih =>
      rw [recoveredLabelling_decompose]
      exact GlobalCarryAxis.Sub.node_l ih
  | right _ ih =>
      rw [recoveredLabelling_decompose]
      exact GlobalCarryAxis.Sub.node_r ih
  | read _ ih => rwa [recoveredLabelling_readRoot]
  | verify _ ih => rwa [recoveredLabelling_verifyChild]

end NodeAddr

/-! ## §B.  The recovered noun and the slot relation at an addressed node

`recoveredLabelling_spec` at the *subtree* is what ties the node's recovered noun to that node's
own committed fingerprint; `NodeAddr.sub_recoveredLabelling` is what puts it inside the root
labelling, so `served_of_node` applies with the node's address as the axis. -/

/-- The recovered noun of an addressed node encodes to that node's committed parent fingerprint. -/
-- the paper, 2058
theorem enc_nodeNoun {z : K} (hz : z ≠ 0) {q a b : ℕ}
    {t s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hstructure : MemoryFingerprintStructure z t)
    (hleaves : MemoryLeafAtomsRealized q t)
    (h : NodeAddr a t b s) :
    GlobalCarryRecognizer.enc z (GlobalCarryAxis.nounOf (recoveredLabelling q s b))
      = memoryTreeRootFP s :=
  (recoveredLabelling_spec hz (h.fingerprintStructure hstructure)
    (h.leafAtoms hleaves) b).2.2.2.1

/-- The recovered noun of an addressed node is a bounded noun. -/
theorem bounded_nodeNoun {z : K} (hz : z ≠ 0) {q a b : ℕ}
    {t s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hstructure : MemoryFingerprintStructure z t)
    (hleaves : MemoryLeafAtomsRealized q t)
    (h : NodeAddr a t b s) :
    FieldEmbedding.BoundedBy q (GlobalCarryAxis.nounOf (recoveredLabelling q s b)) :=
  (recoveredLabelling_spec hz (h.fingerprintStructure hstructure)
    (h.leafAtoms hleaves) b).2.2.1

/-- The addressed node's carried axis is its topological address. -/
theorem axisOf_nodeNoun {z : K} (hz : z ≠ 0) {q a b : ℕ}
    {t s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hstructure : MemoryFingerprintStructure z t)
    (hleaves : MemoryLeafAtomsRealized q t)
    (h : NodeAddr a t b s) :
    GlobalCarryAxis.axisOf (recoveredLabelling q s b) = b :=
  (recoveredLabelling_spec hz (h.fingerprintStructure hstructure)
    (h.leafAtoms hleaves) b).2.1

/-- **`Service.served` at an addressed node of the committed walk.**  This is
`MemoryNounRecovery.served_of_node` instantiated at the recovery's own labelling, with the axis
supplied by the walk topology instead of by a chosen `MemTree` node. -/
theorem served_at_address {z : K} (hz : z ≠ 0) {q b : ℕ}
    {tree s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hstructure : MemoryFingerprintStructure z tree)
    (hleaves : MemoryLeafAtomsRealized q tree)
    (h : NodeAddr 1 tree b s) :
    Noun.slot b (recoveredRootNoun q tree)
      = some (GlobalCarryAxis.nounOf (recoveredLabelling q s b)) :=
  (recoveryOf hz hstructure hleaves).served_of_node
    (h.sub_recoveredLabelling (q := q))
    (axisOf_nodeNoun hz hstructure hleaves h) rfl

/-! ## §C.  (ii) — the two committed row equations, read off `MemoryTable.Vmem`

the paper and `2075-2079` are algorithm lines; `MemoryTable.eqBlk` transcribes them
(`MemoryTable.lean:202-225`) and `Vmem = eqBlk ∧ interV` (`:264`).  Both equations below are one
projection out of `eqBlk`; nothing is assumed. -/

/-- **`read_root`: `mem_root = parent`**. -/
theorem memRoot_eq_ptNoun {inp : MemoryTable.Inputs K} {p : MemoryTable.Pub K}
    (hV : MemoryTable.Vmem inp p) (hst : p.st = MemoryTable.MState.read_root) :
    p.mem.root = p.pt.noun := by
  have h := hV.2.1
  simp only [MemoryTable.eqBlk, hst] at h
  exact h.2.2.2.2.1

/-- **`verify_child`: `mem_child = parent`**.  This is (ii). -/
theorem memChild_eq_ptNoun {inp : MemoryTable.Inputs K} {p : MemoryTable.Pub K}
    (hV : MemoryTable.Vmem inp p) (hst : p.st = MemoryTable.MState.verify_child) :
    p.mem.child = p.pt.noun := by
  have h := hV.2.1
  simp only [MemoryTable.eqBlk, hst] at h
  exact h.2.2.2.2.1

/-- The `read_root` row's committed record root is realized by the recovered **root** noun. -/
theorem root_realizes_of_readRoot {z : K} (hz : z ≠ 0) {q : ℕ}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hstructure : MemoryFingerprintStructure z tree)
    (hleaves : MemoryLeafAtomsRealized q tree)
    (hV : MemoryTable.Vmem tree.label.2.1 tree.label.2.2)
    (hst : tree.label.2.2.st = MemoryTable.MState.read_root) :
    OpcodeSemantics.Realizes z tree.label.2.2.mem.root (recoveredRootNoun q tree) := by
  have hspec := (recoveredLabelling_spec hz hstructure hleaves 1).2.2.2.1
  show tree.label.2.2.mem.root = _
  rw [memRoot_eq_ptNoun hV hst]
  exact hspec.symm

/-- The `verify_child` row's committed record child is realized by the recovered noun **at that
node's address**.  (ii), assembled with §B. -/
theorem child_realizes_of_verifyChild {z : K} (hz : z ≠ 0) {q b : ℕ}
    {tree s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hstructure : MemoryFingerprintStructure z tree)
    (hleaves : MemoryLeafAtomsRealized q tree)
    (h : NodeAddr 1 tree b s)
    (hV : MemoryTable.Vmem s.label.2.1 s.label.2.2)
    (hst : s.label.2.2.st = MemoryTable.MState.verify_child) :
    OpcodeSemantics.Realizes z s.label.2.2.mem.child
      (GlobalCarryAxis.nounOf (recoveredLabelling q s b)) := by
  show s.label.2.2.mem.child = _
  rw [memChild_eq_ptNoun hV hst]
  exact (enc_nodeNoun hz hstructure hleaves h).symm

/-! ## §D.  The composition: the `Service` core at a committed record

A `ServedMemoryTrace.Service` has eight fields.  The three *nouns/axis* coordinates
(`root`, `child`, `axis`) are produced here; `realization` and `served` are proved here; and the
three remaining fields are premises of the theorems below, marked as such:

* `record`/`request_mem` — membership of the record in `exec.rawRequests` (`Language.lean`), a
  compute-side emission fact;
* `exponent`/`timestamp` — `record.ts = α ^ e`, the compute table's line-number timestamp;
* the **record identity** `hroot`/`hchild` below — that the committed `mem` of the walk's
  `read_root` row and of the `verify_child` row are the *same* record as `r`.  That is the LogUp
  `intermediate` matching, carried, not derived;
* the **address identity** `hcommitted` — (i); see §E.
-/

/-- **The `Service` core at a committed record.**  Everything a `Service` needs about nouns: the
realization of all three record coordinates and the paper's slot relation, at the *committed*
record of the walk's `read_root`/`verify_child` pair.

Nothing here is a collision event: `Realizes` is fingerprint-level and the nouns are produced, not
identified. -/
theorem realizesMemRec_and_served_of_committed {z : K} (hz : z ≠ 0) {q b : ℕ}
    {tree s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hstructure : MemoryFingerprintStructure z tree)
    (hleaves : MemoryLeafAtomsRealized q tree)
    (h : NodeAddr 1 tree b s)
    -- the walk root is the `read_root` row of the served record
    (hVroot : MemoryTable.Vmem tree.label.2.1 tree.label.2.2)
    (hstRoot : tree.label.2.2.st = MemoryTable.MState.read_root)
    -- the addressed node is the matching `verify_child` row
    (hVnode : MemoryTable.Vmem s.label.2.1 s.label.2.2)
    (hstNode : s.label.2.2.st = MemoryTable.MState.verify_child)
    -- the record identity
    {r : ComputeTable.MemRec K}
    (hroot : r.root = tree.label.2.2.mem.root)
    (hchild : r.child = s.label.2.2.mem.child)
    -- (i): the committed axis column is the node's topological address
    (hcommitted : r.axis = (b : K)) :
    OpcodeSemantics.RealizesMemRec z r
        (recoveredRootNoun q tree)
        (GlobalCarryAxis.nounOf (recoveredLabelling q s b)) b ∧
      Noun.slot b (recoveredRootNoun q tree)
        = some (GlobalCarryAxis.nounOf (recoveredLabelling q s b)) := by
  refine ⟨⟨?_, ?_, hcommitted⟩, served_at_address hz hstructure hleaves h⟩
  · show r.root = _
    rw [hroot]
    exact root_realizes_of_readRoot hz hstructure hleaves hVroot hstRoot
  · show r.child = _
    rw [hchild]
    exact child_realizes_of_verifyChild hz hstructure hleaves h hVnode hstNode

/-- The same statement in `∃`-form over the served nouns — the shape a `Service` constructor
consumes, with the bounded-noun and axis-window data a `GenGlobalCollision` index set needs. -/
-- the paper, 1288-1295
theorem exists_served_of_committed {z : K} (hz : z ≠ 0) {q b : ℕ}
    {tree s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hstructure : MemoryFingerprintStructure z tree)
    (hleaves : MemoryLeafAtomsRealized q tree)
    (h : NodeAddr 1 tree b s)
    (hVroot : MemoryTable.Vmem tree.label.2.1 tree.label.2.2)
    (hstRoot : tree.label.2.2.st = MemoryTable.MState.read_root)
    (hVnode : MemoryTable.Vmem s.label.2.1 s.label.2.2)
    (hstNode : s.label.2.2.st = MemoryTable.MState.verify_child)
    {r : ComputeTable.MemRec K}
    (hroot : r.root = tree.label.2.2.mem.root)
    (hchild : r.child = s.label.2.2.mem.child)
    (hcommitted : r.axis = (b : K)) :
    ∃ root child : Noun,
      FieldEmbedding.BoundedBy q root ∧ FieldEmbedding.BoundedBy q child ∧
        OpcodeSemantics.RealizesMemRec z r root child b ∧
        Noun.slot b root = some child := by
  obtain ⟨hreal, hserved⟩ :=
    realizesMemRec_and_served_of_committed hz hstructure hleaves h hVroot hstRoot hVnode hstNode
      hroot hchild hcommitted
  exact ⟨_, _, (recoveredLabelling_spec hz hstructure hleaves 1).2.2.1,
    bounded_nodeNoun hz hstructure hleaves h, hreal, hserved⟩

/-! ## §E.  (i) — the committed axis column IS the node's `ℕ` topological address

The tree-model bridge is **not** owed: `AxisBridge.ofNTree` already reads a `MemWalk K` of real
`MemoryTable.Pub` rows off `NTree (MState × DTmem K)`, and `MemWalk.toMTree` reads the
`AxisBatching.MTree K` off that.  What is owed is that `Relaxis` — the *`K`*-valued topological
address `vaddr + 2^vdep` that `AxisDescent`/`AxisBatching` computes by doubling **in `K`** — is the
cast of the `ℕ` address `GlobalCarryAxis.axisOf` carries.  That is §E.

`AxisRoute e recAxis a b t` is the descent from a subtree `t` whose root sits at address `a` down
to the `verify_child` node for timestamp `e`, which sits at address `b` and commits `recAxis` in
its `mem.axis` column.  The sibling `readCount`/`verifyCount = 0` conditions are the ordinary
timestamp-locality data; they are what makes the `vaddr`/`vdep`
recursions pick the routed branch. -/

section AxisIdentification

open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge

/-- Zero read- and verify-multiplicity below a node makes it well-nested for that timestamp. -/
private theorem nested_of_counts_zero (e : ℕ) :
    ∀ t : MTree K, readCount e t = 0 → verifyCount e t = 0 → Nested e t := by
  intro t
  induction t with
  | halt => simp [Nested]
  | decompose l r ihl ihr =>
      simp only [readCount, verifyCount]
      intro hr hv
      exact ⟨by omega, by omega, ihl (by omega) (by omega), ihr (by omega) (by omega)⟩
  | read e' c ih =>
      simp only [readCount, verifyCount, Nested]
      intro hr hv
      by_cases he : e' = e
      · rw [if_pos he] at hr
        exact ih (by omega) hv
      · rw [if_neg he] at hr
        exact ih (by omega) hv
  | verify e' x c ih =>
      simp only [readCount, verifyCount, Nested]
      intro hr hv
      by_cases he : e' = e
      · rw [if_pos he] at hv
        omega
      · rw [if_neg he] at hv
        exact ⟨fun h => absurd h he, ih hr (by omega)⟩

-- the paper, 1408 (the verify is deferred), 1413 (unique `z^i`)
/-- The address-carrying descent to the `verify_child` node of timestamp `e`, on the idealized
`AxisBatching.MTree`. -/
inductive AxisRoute (e : ℕ) (recAxis : K) : ℕ → ℕ → MTree K → Prop
  | here {a : ℕ} {x : K} {c : MTree K}
      (hcommitted : x = recAxis)
      (hr : readCount e c = 0) (hv : verifyCount e c = 0) :
      AxisRoute e recAxis a a (.verify e x c)
  | left {a b : ℕ} {l r : MTree K}
      (route : AxisRoute e recAxis (2 * a) b l)
      (hr : readCount e r = 0) (hv : verifyCount e r = 0) :
      AxisRoute e recAxis a b (.decompose l r)
  | right {a b : ℕ} {l r : MTree K}
      (hr : readCount e l = 0) (hv : verifyCount e l = 0)
      (route : AxisRoute e recAxis (2 * a + 1) b r) :
      AxisRoute e recAxis a b (.decompose l r)
  | read_other {a b e' : ℕ} {c : MTree K}
      (hne : e' ≠ e) (route : AxisRoute e recAxis a b c) :
      AxisRoute e recAxis a b (.read e' c)
  | verify_other {a b e' : ℕ} {x : K} {c : MTree K}
      (hne : e' ≠ e) (route : AxisRoute e recAxis a b c) :
      AxisRoute e recAxis a b (.verify e' x c)

/-- **The route's closed form.**  Its timestamp is used exactly once on the verify side and not at
all on the read side, the subtree is well-nested, `vaxis` returns the committed column, and — the
point of §E — the `ℕ` address `b` satisfies the `K`-level doubling identity
`b = a·2^{vdep} + vaddr`.  Everything is derived; the route carries no address equation. -/
theorem AxisRoute.spec {e : ℕ} {recAxis : K} {a b : ℕ} {t : MTree K}
    (h : AxisRoute e recAxis a b t) :
    readCount e t = 0 ∧ verifyCount e t = 1 ∧ Nested e t ∧
      vaxis e t = recAxis ∧
      ((b : ℕ) : K) = ((a : ℕ) : K) * 2 ^ (vdep e t) + vaddr e t := by
  induction h with
  | here hcommitted hr hv =>
      subst hcommitted
      refine ⟨by simp [readCount, hr], by simp [verifyCount, hv], ?_, by simp [vaxis],
        by simp [vdep, vaddr]⟩
      refine ⟨fun _ => hr, nested_of_counts_zero e _ hr hv⟩
  | @left a b l r route hr hv ih =>
      obtain ⟨hrl, hvl, hnl, hax, haddr⟩ := ih
      refine ⟨by simp [readCount, hrl, hr], by simp [verifyCount, hvl, hv], ?_,
        by simp [vaxis, hvl, hax], ?_⟩
      · exact ⟨by omega, by omega, hnl, nested_of_counts_zero e _ hr hv⟩
      · simp only [vdep, vaddr, if_pos hvl, pow_succ]
        rw [haddr]
        push_cast
        ring
  | @right a b l r hr hv route ih =>
      obtain ⟨hrr, hvr, hnr, hax, haddr⟩ := ih
      have hvne : verifyCount e l ≠ 1 := by omega
      refine ⟨by simp [readCount, hrr, hr], by simp [verifyCount, hvr, hv], ?_,
        by simp [vaxis, hvne, hax], ?_⟩
      · exact ⟨by omega, by omega, nested_of_counts_zero e _ hr hv, hnr⟩
      · simp only [vdep, vaddr, if_neg hvne, pow_succ]
        rw [haddr]
        push_cast
        ring
  | read_other hne route ih =>
      simpa [readCount, verifyCount, Nested, vaxis, vdep, vaddr, hne] using ih
  | verify_other hne route ih =>
      simpa [readCount, verifyCount, Nested, vaxis, vdep, vaddr, hne] using ih

/-- **`Relaxis` is the cast of the `ℕ` address.**  The `K`-valued topological address of
`AxisBatching`/`AxisDescent`, taken at the `read_root` that opens the region, is exactly
`((b : ℕ) : K)` for the ordinary Nock axis `b` the walk topology assigns to the verified node. -/
theorem relaxis_eq_natCast {e : ℕ} {recAxis : K} {b : ℕ} {c : MTree K}
    (h : AxisRoute e recAxis 1 b c) :
    Relaxis e (MTree.read e c : MTree K) = ((b : ℕ) : K) := by
  obtain ⟨-, -, -, -, haddr⟩ := h.spec
  simp only [Relaxis, if_pos]
  rw [haddr]
  push_cast
  ring

/-- **(i), on the idealized tree.**  With the terminal `axis_counts` boundary holding as a
polynomial identity — `AxisBridge`'s own perfect form — the committed `mem.axis` column of the
routed `verify_child` row *is* the cast of its `ℕ` topological address.  This is
`AxisBatching.axis_batching_sound` composed with `relaxis_eq_natCast`; no new event is counted.

⚠ `hterm` is the **perfect** boundary `countsP = 0` as a polynomial identity, which is strictly
stronger than what the AIR checks — the AIR checks the column's *evaluation* at the challenge. -/
-- the paper, 1415
theorem committed_axis_eq_address (h2 : (2 : K) ≠ 0)
    {e : ℕ} {recAxis : K} {b : ℕ} {c : MTree K}
    (hterm : countsP_bin (MTree.read e c : MTree K) = 0)
    (h : AxisRoute e recAxis 1 b c) :
    recAxis = ((b : ℕ) : K) := by
  obtain ⟨hr, hv, hn, hax, -⟩ := h.spec
  have hsound :=
    axis_batching_sound h2 (MTree.read e c) hterm e
      (by simpa [Nested] using hn) (by simp [readCount, hr]) (by simp [verifyCount, hv])
  rw [relaxis_eq_natCast h] at hsound
  rw [← hsound]
  simpa [vaxis] using hax.symm

/-! ### The same route on the committed walk

`WalkAxisRoute` is `AxisRoute` read on `NTree (MState × DTmem K)` itself: the walk's own
`read_root`/`verify_child`/`decompose` rows, with the timestamp exponent supplied by
`AxisBridge`'s exponent map `E` (which `AxisBridge.expOf` shows need not be a free oracle).  It
projects onto **both** models: to `NodeAddr` (§A, hence to the recovered labelling) and to
`AxisRoute` (hence to the `AxisBatching` soundness). -/

/-- The address-carrying descent on the committed memory walk. -/
inductive WalkAxisRoute
    (E : NTree (MemoryTable.MState × MemoryTable.DTmem K) → ℕ) (e : ℕ) (recAxis : K) :
    ℕ → ℕ → NTree (MemoryTable.MState × MemoryTable.DTmem K) →
      NTree (MemoryTable.MState × MemoryTable.DTmem K) → Prop
  | here {a : ℕ} {d : MemoryTable.DTmem K}
      {c : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
      (hE : E (.node (.verify_child, d) [c]) = e)
      (hcommitted : d.2.mem.axis = recAxis)
      (hr : readCount e (MemWalk.toMTree (ofNTree E c)) = 0)
      (hv : verifyCount e (MemWalk.toMTree (ofNTree E c)) = 0) :
      WalkAxisRoute E e recAxis a a
        (.node (.verify_child, d) [c]) (.node (.verify_child, d) [c])
  | left {a b : ℕ} {d : MemoryTable.DTmem K}
      {l r s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
      (route : WalkAxisRoute E e recAxis (2 * a) b l s)
      (hr : readCount e (MemWalk.toMTree (ofNTree E r)) = 0)
      (hv : verifyCount e (MemWalk.toMTree (ofNTree E r)) = 0) :
      WalkAxisRoute E e recAxis a b (.node (.decompose, d) [l, r]) s
  | right {a b : ℕ} {d : MemoryTable.DTmem K}
      {l r s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
      (hr : readCount e (MemWalk.toMTree (ofNTree E l)) = 0)
      (hv : verifyCount e (MemWalk.toMTree (ofNTree E l)) = 0)
      (route : WalkAxisRoute E e recAxis (2 * a + 1) b r s) :
      WalkAxisRoute E e recAxis a b (.node (.decompose, d) [l, r]) s
  | read_other {a b : ℕ} {d : MemoryTable.DTmem K}
      {c s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
      (hne : E (.node (.read_root, d) [c]) ≠ e)
      (route : WalkAxisRoute E e recAxis a b c s) :
      WalkAxisRoute E e recAxis a b (.node (.read_root, d) [c]) s
  | verify_other {a b : ℕ} {d : MemoryTable.DTmem K}
      {c s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
      (hne : E (.node (.verify_child, d) [c]) ≠ e)
      (route : WalkAxisRoute E e recAxis a b c s) :
      WalkAxisRoute E e recAxis a b (.node (.verify_child, d) [c]) s

namespace WalkAxisRoute

variable {E : NTree (MemoryTable.MState × MemoryTable.DTmem K) → ℕ}

/-- The walk route is an address descent in the sense of §A. -/
theorem toNodeAddr {e : ℕ} {recAxis : K} {a b : ℕ}
    {t s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : WalkAxisRoute E e recAxis a b t s) : NodeAddr a t b s := by
  induction h with
  | here _ _ _ _ => exact NodeAddr.here _ _
  | left _ _ _ ih => exact NodeAddr.left ih
  | right _ _ _ ih => exact NodeAddr.right ih
  | read_other _ _ ih => exact NodeAddr.read ih
  | verify_other _ _ ih => exact NodeAddr.verify ih

/-- The routed node is a `verify_child` row, and it is the row committing `recAxis`. -/
theorem target {e : ℕ} {recAxis : K} {a b : ℕ}
    {t s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : WalkAxisRoute E e recAxis a b t s) :
    s.label.1 = MemoryTable.MState.verify_child ∧ s.label.2.2.mem.axis = recAxis := by
  induction h with
  | here _ hcommitted _ _ => exact ⟨rfl, hcommitted⟩
  | left _ _ _ ih => exact ih
  | right _ _ _ ih => exact ih
  | read_other _ _ ih => exact ih
  | verify_other _ _ ih => exact ih

/-- The walk route is an `AxisRoute` on the `AxisBatching` model, through `AxisBridge`. -/
theorem toAxisRoute {e : ℕ} {recAxis : K} {a b : ℕ}
    {t s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : WalkAxisRoute E e recAxis a b t s) :
    AxisRoute e recAxis a b (MemWalk.toMTree (ofNTree E t)) := by
  induction h with
  | @here a d c hE hcommitted hr hv =>
      rw [ofNTree_verify]
      rw [hE]
      exact AxisRoute.here hcommitted hr hv
  | left _ hr hv ih =>
      rw [ofNTree_decompose]
      exact AxisRoute.left ih hr hv
  | right hr hv _ ih =>
      rw [ofNTree_decompose]
      exact AxisRoute.right hr hv ih
  | read_other hne _ ih =>
      rw [ofNTree_read]
      exact AxisRoute.read_other hne ih
  | verify_other hne _ ih =>
      rw [ofNTree_verify]
      exact AxisRoute.verify_other hne ih

end WalkAxisRoute

/-- **(i), on the committed walk.**  The `verify_child` row reached by an address descent from the
`read_root` that opens its region commits, in its `mem.axis` column, exactly the cast of that
node's ordinary Nock axis.

Premises, all `AxisBridge`'s own and none new: `char ≠ 2`,
the perfect-form terminal `axis_counts` boundary as a polynomial identity, and the route's
sibling timestamp-locality conditions. -/
theorem committed_axis_eq_address_of_walk (h2 : (2 : K) ≠ 0)
    {E : NTree (MemoryTable.MState × MemoryTable.DTmem K) → ℕ} {e : ℕ} {recAxis : K} {b : ℕ}
    {d : MemoryTable.DTmem K} {c s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hE : E (.node (.read_root, d) [c]) = e)
    (hterm :
      countsP_bin (MemWalk.toMTree (ofNTree E (.node (.read_root, d) [c]))) = 0)
    (hroute : WalkAxisRoute E e recAxis 1 b c s) :
    recAxis = ((b : ℕ) : K) := by
  have hshape :
      MemWalk.toMTree (ofNTree E (.node (.read_root, d) [c]))
        = (MTree.read e (MemWalk.toMTree (ofNTree E c)) : MTree K) := by
    rw [ofNTree_read, hE]
    rfl
  rw [hshape] at hterm
  exact committed_axis_eq_address h2 hterm hroute.toAxisRoute

end AxisIdentification

/-! ## §F.  (i) and (ii) together: the `Service` core with the axis derived

`served_of_committed_walk` is the composition: nothing about nouns, axes or the slot relation is
premised any more.  What is left of a `ServedMemoryTrace.Service` is exactly the three
non-geometric fields — `request_mem`, `exponent`/`timestamp` — and the record identity that the
LogUp `intermediate` matching supplies. -/

section Composition

open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge

/-- **The `Service` core at a committed record, axis included.**  §D with `hcommitted` discharged
by §E. -/
theorem served_of_committed_walk {z : K} (hz : z ≠ 0) (h2 : (2 : K) ≠ 0) {q b : ℕ}
    {E : NTree (MemoryTable.MState × MemoryTable.DTmem K) → ℕ} {e : ℕ}
    {d : MemoryTable.DTmem K} {c s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hstructure : MemoryFingerprintStructure z (.node (.read_root, d) [c]))
    (hleaves : MemoryLeafAtomsRealized q (.node (.read_root, d) [c]))
    (hVroot : MemoryTable.Vmem d.1 d.2)
    (hstRoot : d.2.st = MemoryTable.MState.read_root)
    (hVnode : MemoryTable.Vmem s.label.2.1 s.label.2.2)
    (hstNode : s.label.2.2.st = MemoryTable.MState.verify_child)
    (hE : E (.node (.read_root, d) [c]) = e)
    (hterm : countsP_bin (MemWalk.toMTree (ofNTree E (.node (.read_root, d) [c]))) = 0)
    {r : ComputeTable.MemRec K}
    (hroute : WalkAxisRoute E e r.axis 1 b c s)
    (hroot : r.root = d.2.mem.root)
    (hchild : r.child = s.label.2.2.mem.child) :
    OpcodeSemantics.RealizesMemRec z r
        (recoveredRootNoun q (.node (.read_root, d) [c]))
        (GlobalCarryAxis.nounOf (recoveredLabelling q s b)) b ∧
      Noun.slot b (recoveredRootNoun q (.node (.read_root, d) [c]))
        = some (GlobalCarryAxis.nounOf (recoveredLabelling q s b)) :=
  realizesMemRec_and_served_of_committed hz hstructure hleaves
    (NodeAddr.read hroute.toNodeAddr) hVroot hstRoot hVnode hstNode hroot hchild
    (committed_axis_eq_address_of_walk h2 hE hterm hroute)

end Composition

/-! ## §G.  A noun-free, slot-free supply premise, and `ServedSlotCovers`

`GenGlobalCollision.ServedSlotCovers` is the premise
`operationalCore_of_accepted_and_serviceCovers` needs for `hop`'s served half.  §G reduces it to
`CommittedRecordWitness`: a premise that mentions **no noun, no `Noun.slot`, no `Service` and no
`ComputeRowSemanticData`** — only the committed memory walk of the record, its per-row
`MemoryTable.Vmem`, and the walk's own address descent.  Everything noun-shaped is *produced*
here by §A–§F.

What `CommittedRecordWitness` still carries, and why each is legitimate:

* `route`, `expRoot`, `recRoot`, `recChild` — the **IO record matching**: that the record the
  compute table emitted is the record the memory walk's `read_root`/`verify_child` pair serves.
  That is the paper's LogUp `intermediate` multiset, which
  is an assumption of the memory walk here, not a fact about nouns.
* `terminal` — `AxisBridge`'s perfect-form `axis_counts` boundary, the
  same premise `axis_lookups_valid_perfect_of_memtrace` takes.
* the sibling `readCount`/`verifyCount = 0` conditions inside `route` — timestamp locality.

What §G does **not** discharge, and it is the honest residual: the `S`-membership and `axis < q`
conjuncts of `ServedSlotCovers`.  Those index the counted event, and the nouns they must contain
are the *recovered* ones — the quantifier-order caveat `GenNounRecovery` §D records about itself.
`GenNounRecovery.recoveredRootNoun` being seed-free is what makes them writable in advance, so
they are stated as premises about that function rather than about a chosen labelling. -/

section Supply

open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge

/-- **The memory-side commitment of one emitted record.**  Noun-free and slot-free: every field is
either committed trace data, a `MemoryTable.Vmem` row, or a walk-topology descent. -/
structure CommittedRecordWitness (z : K) (q : ℕ)
    (E : NTree (MemoryTable.MState × MemoryTable.DTmem K) → ℕ)
    (r : ComputeTable.MemRec K) where
  /-- The `read_root` row that opens the served region. -/
  rootData : MemoryTable.DTmem K
  /-- The subtree below it. -/
  region : NTree (MemoryTable.MState × MemoryTable.DTmem K)
  /-- The matching `verify_child` node. -/
  verifyNode : NTree (MemoryTable.MState × MemoryTable.DTmem K)
  /-- Its ordinary Nock axis in the region. -/
  addr : ℕ
  /-- The record's timestamp exponent on the memory side. -/
  memExponent : ℕ
  fingerprints : MemoryFingerprintStructure z (.node (.read_root, rootData) [region])
  leaves : MemoryLeafAtomsRealized q (.node (.read_root, rootData) [region])
  vRoot : MemoryTable.Vmem rootData.1 rootData.2
  stRoot : rootData.2.st = MemoryTable.MState.read_root
  vNode : MemoryTable.Vmem verifyNode.label.2.1 verifyNode.label.2.2
  stNode : verifyNode.label.2.2.st = MemoryTable.MState.verify_child
  expRoot : E (.node (.read_root, rootData) [region]) = memExponent
  terminal :
    countsP_bin (MemWalk.toMTree (ofNTree E (.node (.read_root, rootData) [region]))) = 0
  route : WalkAxisRoute E memExponent r.axis 1 addr region verifyNode
  recRoot : r.root = rootData.2.mem.root
  recChild : r.child = verifyNode.label.2.2.mem.child

namespace CommittedRecordWitness

variable {z : K} {q : ℕ} {E : NTree (MemoryTable.MState × MemoryTable.DTmem K) → ℕ}
  {r : ComputeTable.MemRec K}

/-- The served root noun the witness determines: seed-free, a function of the committed walk. -/
def servedRoot (W : CommittedRecordWitness z q E r) : Noun :=
  recoveredRootNoun q (.node (.read_root, W.rootData) [W.region])

/-- The served child noun the witness determines: seed-free, a function of the committed walk. -/
def servedChild (W : CommittedRecordWitness z q E r) : Noun :=
  GlobalCarryAxis.nounOf (recoveredLabelling q W.verifyNode W.addr)

/-- **The witness realizes the record and serves it.**  §F, packaged. -/
theorem realizes_and_served (hz : z ≠ 0) (h2 : (2 : K) ≠ 0)
    (W : CommittedRecordWitness z q E r) :
    OpcodeSemantics.RealizesMemRec z r W.servedRoot W.servedChild W.addr ∧
      Noun.slot W.addr W.servedRoot = some W.servedChild :=
  served_of_committed_walk hz h2 W.fingerprints W.leaves W.vRoot W.stRoot W.vNode W.stNode
    W.expRoot W.terminal W.route W.recRoot W.recChild

end CommittedRecordWitness

variable [Fintype K] [DecidableEq K]
variable {cfg : ExactConfig F K} {exec : ExactExecution cfg}

/-- **A `Service` from a committed record.**  The three geometric fields (`root`, `child`, `axis`)
are the witness's; `realization` and `served` are §F.  The two non-geometric premises are named:
`hreq` (the record is one of the execution's raw requests) and `hts`. -/
theorem exists_service_of_witness (h2 : (2 : K) ≠ 0) {q : ℕ}
    {E : NTree (MemoryTable.MState × MemoryTable.DTmem K) → ℕ}
    {r : ComputeTable.MemRec K}
    (hz : cfg.challenges.z ≠ 0)
    (W : CommittedRecordWitness cfg.challenges.z q E r)
    (hreq : r ∈ exec.rawRequests)
    {e : ℕ} (hts : r.ts = cfg.challenges.α ^ e) :
    ∃ svc : ServedMemoryTrace.Service cfg exec,
      svc.record = r ∧ svc.root = W.servedRoot ∧ svc.child = W.servedChild ∧
        svc.axis = W.addr := by
  obtain ⟨hreal, hserved⟩ := W.realizes_and_served hz h2
  exact ⟨{ exponent := e, record := r, root := W.servedRoot, child := W.servedChild,
           axis := W.addr, request_mem := hreq, timestamp := hts,
           realization := hreal, served := hserved },
         rfl, rfl, rfl, rfl⟩

/-- **`ServedSlotCovers` from committed-record witnesses.**  This is the premise
`GenGlobalCollision.operationalCore_of_accepted_and_serviceCovers` needs for `hop`'s served half,
now supplied from a statement about the committed memory walk alone.

Read the hypotheses as the answer to "under what side conditions": per OP0 / OP9 row, one
`CommittedRecordWitness` for that row's served record (the IO matching), the compute-side
timestamp exponent, the axis window `addr < q`, and the two recovered nouns lying in the counted
event's index set `S`. -/
theorem servedSlotCovers_of_witnesses (h2 : (2 : K) ≠ 0) {q : ℕ} {S : Finset Noun}
    {E : NTree (MemoryTable.MState × MemoryTable.DTmem K) → ℕ}
    (hz : cfg.challenges.z ≠ 0)
    (hs0 : ∀ row ∈ exec.computeRows, row.2.2.1.state = ComputeTable.State.s0 →
      ∃ (W : CommittedRecordWitness cfg.challenges.z q E (computeMemRec row.2.2.1 1)) (e : ℕ),
        (computeMemRec row.2.2.1 1).ts = cfg.challenges.α ^ e ∧
          W.servedRoot ∈ S ∧ W.servedChild ∈ S ∧ W.addr < q)
    (hs9 : ∀ row ∈ exec.computeRows, row.2.2.1.state = ComputeTable.State.s9 →
      ∃ (W : CommittedRecordWitness cfg.challenges.z q E (computeMemRec row.2.2.1 2)) (e : ℕ),
        (computeMemRec row.2.2.1 2).ts = cfg.challenges.α ^ e ∧
          W.servedRoot ∈ S ∧ W.servedChild ∈ S ∧ W.addr < q) :
    GenGlobalCollision.ServedSlotCovers exec q S := by
  refine ⟨?_, ?_⟩
  · intro row hrow hst
    obtain ⟨W, e, hts, hrS, hcS, haq⟩ := hs0 row hrow hst
    have hreq : computeMemRec row.2.2.1 1 ∈ exec.rawRequests :=
      GenGlobalCollision.mem_rawRequests_of_bound hrow _
        (mr2_mem_activeRequestRecords _ hst)
    obtain ⟨svc, hrec, hr, hc, ha⟩ := exists_service_of_witness h2 hz W hreq hts
    exact ⟨svc, hrec, by rw [hr]; exact hrS, by rw [hc]; exact hcS, by rw [ha]; exact haq⟩
  · intro row hrow hst
    obtain ⟨W, e, hts, hrS, hcS, haq⟩ := hs9 row hrow hst
    have hreq : computeMemRec row.2.2.1 2 ∈ exec.rawRequests :=
      GenGlobalCollision.mem_rawRequests_of_bound hrow _
        (mr3_mem_activeRequestRecords _ hst)
    obtain ⟨svc, hrec, hr, hc, ha⟩ := exists_service_of_witness h2 hz W hreq hts
    exact ⟨svc, hrec, by rw [hr]; exact hrS, by rw [hc]; exact hcS, by rw [ha]; exact haq⟩

end Supply

/-! ## §H.  Axiom receipts -/

section Receipts

#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServedFromRecord.NodeAddr.sub_recoveredLabelling
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServedFromRecord.served_at_address
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServedFromRecord.memChild_eq_ptNoun
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServedFromRecord.child_realizes_of_verifyChild
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenServedFromRecord.realizesMemRec_and_served_of_committed
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServedFromRecord.relaxis_eq_natCast
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServedFromRecord.committed_axis_eq_address
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenServedFromRecord.committed_axis_eq_address_of_walk
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServedFromRecord.served_of_committed_walk
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServedFromRecord.exists_service_of_witness
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenServedFromRecord.servedSlotCovers_of_witnesses

end Receipts

end

end Nock.NockVMROM.Thm54.TraceGen.GenServedFromRecord
