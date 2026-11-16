import Nock.NockVMROM.Thm54.JointSoundness

/-!
# Seed-independent semantic skeletons

`SemanticSkeleton` is fixed before the NPR seed.  It contains only Nock nouns, Nat axes, and
the ordered compute/memory tree topology.  `BindsAt` is the after-seed relation to one
`ExactExecution`; it has no decoder and introduces no noun existential.

The compute inventory is:

* always-live `s`, `f`, `e`, `f_h`, and `f_t`;
* `f_th/f_tt` in states `s2,s5,s6,s7,s8,s9`;
* `f_tth/f_ttt` only in state `s6`;
* the active prefix of the three `sf` triples;
* the active prefix of `mr1/mr2/mr3`, including root, child, and a Nat axis.

The memory inventory is `pt.noun`, the active child prefix, and the live memory record in
`read_root`/`verify_child`.  A halt node additionally precommits its Nat atom.  Paper-mandated
inactive zeros stay: inactive memory records are `MemRec.zero` and
inactive subformula triples are `(0,0,0)`.  Private `Dec` columns are
unconstrained by `Vcomp`; `BindComputeRow`'s
inactive-Dec else-branch is `True`.  Do not read this as a zero-padding
demand on inactive `f_th`/`f_tt`/`f_tth`/`f_ttt`.
-/

namespace Nock.NockVMROM.Thm54.SemanticStrategy

open scoped Classical
open Nock Nock.Walk

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## Stable slot inventory -/

inductive DecSlot
  | f_h | f_t | f_th | f_tt | f_tth | f_ttt
deriving DecidableEq, Repr

def decFP (dec : ComputeTable.Dec K) : DecSlot → ComputeTable.FP K
  | .f_h => dec.f_h
  | .f_t => dec.f_t
  | .f_th => dec.f_th
  | .f_tt => dec.f_tt
  | .f_tth => dec.f_tth
  | .f_ttt => dec.f_ttt

def hasTailDecomposition : ComputeTable.State → Bool
  | .s2 | .s5 | .s6 | .s7 | .s8 | .s9 => true
  | _ => false

def decActive (st : ComputeTable.State) : DecSlot → Bool
  | .f_h | .f_t => true
  | .f_th | .f_tt => hasTailDecomposition st
  | .f_tth | .f_ttt => st == .s6

theorem decActive_cases (st : ComputeTable.State) :
    decActive st .f_h = true ∧ decActive st .f_t = true ∧
      (decActive st .f_th = true ↔
        st = .s2 ∨ st = .s5 ∨ st = .s6 ∨ st = .s7 ∨ st = .s8 ∨ st = .s9) ∧
      (decActive st .f_tt = true ↔
        st = .s2 ∨ st = .s5 ∨ st = .s6 ∨ st = .s7 ∨ st = .s8 ∨ st = .s9) ∧
      (decActive st .f_tth = true ↔ st = .s6) ∧
      (decActive st .f_ttt = true ↔ st = .s6) := by
  cases st <;> decide

inductive TripleSlot
  | subject | formula | result
deriving DecidableEq, Repr

def tripleFP
    (x : ComputeTable.FP K × ComputeTable.FP K × ComputeTable.FP K) :
    TripleSlot → ComputeTable.FP K
  | .subject => x.1
  | .formula => x.2.1
  | .result => x.2.2

inductive MemRecNounSlot
  | root | child
deriving DecidableEq, Repr

def memRecFP (r : ComputeTable.MemRec K) : MemRecNounSlot → ComputeTable.FP K
  | .root => r.root
  | .child => r.child

/-! ## Pre-seed row and tree data -/

structure MemRecSkeleton where
  root : Noun
  child : Noun
  axis : ℕ

structure ComputeRowSkeleton where
  state : ComputeTable.State
  subject : Noun
  formula : Noun
  evaluation : Noun
  decomposition : ∀ slot : DecSlot, decActive state slot = true → Noun
  subformula :
    ∀ i : Fin 3, (i : ℕ) < ComputeTable.fanoutComp state → TripleSlot → Noun
  memoryRecord :
    ∀ i : Fin 3, (i : ℕ) < Nock.Framework.recordCount state → MemRecSkeleton

structure MemoryRowSkeleton where
  state : MemoryTable.MState
  parent : Noun
  haltAtom : state = .halt → ℕ
  haltParent : ∀ h : state = .halt, parent = .atom (haltAtom h)
  child :
    ∀ i : Fin 2, (i : ℕ) < MemoryTable.fanoutMem state → Noun
  memoryRecord : memoryMemRecKind state = .active → MemRecSkeleton

/-- The complete field-independent commitment.  Tree roots, child order, forest-root order, row
order, states, nouns, and Nat axes are all fixed before `z`. -/
structure SemanticSkeleton where
  computeTree : NTree ComputeRowSkeleton
  memoryForest : List (NTree MemoryRowSkeleton)

def computeSkeletonRows (S : SemanticSkeleton) : List ComputeRowSkeleton :=
  (bfsForest [S.computeTree]).map NTree.label

def memorySkeletonRows (S : SemanticSkeleton) : List MemoryRowSkeleton :=
  (bfsForest S.memoryForest).map NTree.label

/-! ## Exact after-seed binding -/

def bindFP (z : K) (n : Noun) (fp : ComputeTable.FP K) : Prop :=
  fp = GlobalCarryRecognizer.enc z n

def BindMemRec (z : K) (s : MemRecSkeleton) (r : ComputeTable.MemRec K) : Prop :=
  bindFP z s.root r.root ∧ bindFP z s.child r.child ∧ r.axis = (s.axis : K)

/-- Row-level memory binding: a memory row stores
    the Form R encoding of the skeleton record — `axis = T`, `cprime = C'` at the row's `λ`
    (`lmb`; honestly the configuration's `cfg.challenges.lam`, 28th λ-fix).  The skeleton's `ℕ`
    axis is the Nock axis; the encode reads
    it through `nockAxisOf`, exactly as `NockVM.encRecFormR` does on the compute IO. -/
def BindMemRow (z : K) (s : MemRecSkeleton) (r : ComputeTable.MemRec K) (cprime lmb : K) :
    Prop :=
  bindFP z s.root r.root ∧ bindFP z s.child r.child ∧
    r.axis = MemoryTable.formRT lmb (MemoryTable.nockAxisOf ((s.axis : ℕ) : K)) ∧
    cprime = MemoryTable.formRC lmb (MemoryTable.nockAxisOf ((s.axis : ℕ) : K))

/-- The a-bearing record a row-level memory row encodes. -/
def MemRecSkeleton.aRecord (s : MemRecSkeleton) (r : ComputeTable.MemRec K) :
    ComputeTable.MemRec K :=
  { r with axis := ((s.axis : ℕ) : K) }

/-- A row-level row's IO record is the Form R encode of the a-bearing skeleton record. -/
theorem BindMemRow.encRecC_eq {z : K} {s : MemRecSkeleton} {r : ComputeTable.MemRec K}
    {cprime lmb : K} (h : BindMemRow z s r cprime lmb) :
    NockVM.encRecC r cprime = NockVM.encRecFormR (s.aRecord r) lmb := by
  obtain ⟨_, _, hax, hc⟩ := h
  unfold NockVM.encRecFormR
  rw [hc]
  cases r
  simp only [MemRecSkeleton.aRecord] at hax ⊢
  rw [← hax]

def BindComputeRow (z : K) (s : ComputeRowSkeleton)
    (row : ComputeTable.State × ComputeTable.DTcomp K) : Prop :=
  row.1 = s.state ∧ row.2.1.z = z ∧ row.2.2.1.state = s.state ∧
  bindFP z s.subject row.2.2.1.s ∧
  bindFP z s.formula row.2.2.1.f ∧
  bindFP z s.evaluation row.2.2.1.e ∧
  (∀ slot : DecSlot,
    if h : decActive s.state slot = true
    then bindFP z (s.decomposition slot h) (decFP row.2.2.2 slot)
    else True) ∧
  (∀ i : Fin 3,
    if h : (i : ℕ) < ComputeTable.fanoutComp s.state
    then ∀ slot : TripleSlot,
      bindFP z (s.subformula i h slot)
        (tripleFP (computeSubformulaFPs row.2.2.1 i) slot)
    else computeSubformulaFPs row.2.2.1 i = (0, 0, 0)) ∧
  (∀ i : Fin 3,
    if h : (i : ℕ) < Nock.Framework.recordCount s.state
    then BindMemRec z (s.memoryRecord i h) (computeMemRec row.2.2.1 i)
    else computeMemRec row.2.2.1 i = ComputeTable.MemRec.zero)

def BindMemoryRow (z : K) (s : MemoryRowSkeleton)
    (row : MemoryTable.MState × MemoryTable.DTmem K) : Prop :=
  row.1 = s.state ∧ row.2.1.z = z ∧ row.2.2.st = s.state ∧
  bindFP z s.parent row.2.2.pt.noun ∧
  (∀ i : Fin 2,
    if h : (i : ℕ) < MemoryTable.fanoutMem s.state
    then bindFP z (s.child i h) (memoryChildCell row.2.2 i).noun
    else memoryChildCell row.2.2 i = MemoryTable.Cell.zero) ∧
  (if h : memoryMemRecKind s.state = .active
    then BindMemRow z (s.memoryRecord h) row.2.2.mem row.2.2.cprime row.2.2.lambda
    else row.2.2.mem = ComputeTable.MemRec.zero) ∧
  -- Honest `ver = (st = read_root)`.
  row.2.2.ver = decide (s.state = MemoryTable.MState.read_root)

/-- A-bearing memory binding of a **template** row.
`MemoryRowTemplate.specialize` turns it into the row-level `BindMemoryRow` of the executed row
. -/
def BindMemoryRowA (z : K) (s : MemoryRowSkeleton)
    (row : MemoryTable.MState × MemoryTable.DTmem K) : Prop :=
  row.1 = s.state ∧ row.2.1.z = z ∧ row.2.2.st = s.state ∧
  bindFP z s.parent row.2.2.pt.noun ∧
  (∀ i : Fin 2,
    if h : (i : ℕ) < MemoryTable.fanoutMem s.state
    then bindFP z (s.child i h) (memoryChildCell row.2.2 i).noun
    else memoryChildCell row.2.2 i = MemoryTable.Cell.zero) ∧
  (if h : memoryMemRecKind s.state = .active
    then BindMemRec z (s.memoryRecord h) row.2.2.mem
    else row.2.2.mem = ComputeTable.MemRec.zero) ∧
  row.2.2.ver = decide (s.state = MemoryTable.MState.read_root)

theorem BindMemoryRow.ver_eq (z : K) {s : MemoryRowSkeleton}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (h : BindMemoryRow z s row) :
    row.2.2.ver = decide (s.state = MemoryTable.MState.read_root) :=
  h.2.2.2.2.2.2

theorem BindMemoryRow.honest_ver (z : K) {s : MemoryRowSkeleton}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (h : BindMemoryRow z s row) :
    row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  rw [h.2.2.1]; exact BindMemoryRow.ver_eq z h

inductive ComputeTreeBinds (z : K) :
    NTree ComputeRowSkeleton →
      NTree (ComputeTable.State × ComputeTable.DTcomp K) → Prop
  | node {s sc row rc}
      (shape : sc.length = ComputeTable.fanoutComp s.state)
      (rowBinding : BindComputeRow z s row)
      (children : List.Forall₂ (ComputeTreeBinds z) sc rc) :
      ComputeTreeBinds z (.node s sc) (.node row rc)

inductive MemoryTreeBinds (z : K) :
    NTree MemoryRowSkeleton →
      NTree (MemoryTable.MState × MemoryTable.DTmem K) → Prop
  | node {s sc row rc}
      (shape : sc.length = MemoryTable.fanoutMem s.state)
      (rowBinding : BindMemoryRow z s row)
      (children : List.Forall₂ (MemoryTreeBinds z) sc rc) :
      MemoryTreeBinds z (.node s sc) (.node row rc)

namespace ComputeTreeBinds

theorem root {z : K} {s : NTree ComputeRowSkeleton}
    {tree : NTree (ComputeTable.State × ComputeTable.DTcomp K)}
    (h : ComputeTreeBinds z s tree) :
    BindComputeRow z s.label tree.label := by
  cases h
  assumption

end ComputeTreeBinds

namespace MemoryTreeBinds

theorem root {z : K} {s : NTree MemoryRowSkeleton}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : MemoryTreeBinds z s tree) :
    BindMemoryRow z s.label tree.label := by
  cases h
  assumption

theorem children {z : K} {s : NTree MemoryRowSkeleton}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : MemoryTreeBinds z s tree) :
    List.Forall₂ (MemoryTreeBinds z) s.children tree.children := by
  cases h
  assumption

end MemoryTreeBinds

theorem ComputeTreeBinds.children {z : K} {s : NTree ComputeRowSkeleton}
    {tree : NTree (ComputeTable.State × ComputeTable.DTcomp K)}
    (h : ComputeTreeBinds z s tree) :
    List.Forall₂ (ComputeTreeBinds z) s.children tree.children := by
  cases h
  assumption

/-- Generic level-order coherence: a recursive relation that relates roots and recursively relates
ordered child lists induces the corresponding `Forall₂` relation on canonical BFS labels. -/
private theorem bfsRows_ofTreeBindings
    {A B : Type} (RowRel : A → B → Prop)
    (TreeRel : NTree A → NTree B → Prop)
    (rootRel : ∀ s tree, TreeRel s tree → RowRel s.label tree.label)
    (childRel : ∀ s tree, TreeRel s tree →
      List.Forall₂ TreeRel s.children tree.children) :
    ∀ {ss : List (NTree A)} {trees : List (NTree B)},
      List.Forall₂ TreeRel ss trees →
      List.Forall₂ RowRel
        ((bfsForest ss).map NTree.label)
        ((bfsForest trees).map NTree.label) := by
  suffices H :
      ∀ n : ℕ, ∀ {ss : List (NTree A)} {trees : List (NTree B)},
        totalSize ss ≤ n →
        List.Forall₂ TreeRel ss trees →
        List.Forall₂ RowRel
          ((bfsForest ss).map NTree.label)
          ((bfsForest trees).map NTree.label) by
    intro ss trees h
    exact H (totalSize ss) le_rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro ss trees hsize htrees
      cases htrees with
      | nil => simp [bfsForest_nil]
      | @cons s tree ss trees hhead htail =>
          let source : List (NTree A) := s :: ss
          let target : List (NTree B) := tree :: trees
          have hsource : source ≠ [] := by simp [source]
          have htarget : target ≠ [] := by simp [target]
          have hall : List.Forall₂ TreeRel source target :=
            .cons hhead htail
          have hroots :
              List.Forall₂ RowRel
                (source.map NTree.label) (target.map NTree.label) :=
            List.rel_map (fun a b hab => rootRel a b hab) hall
          have hchildren :
              List.Forall₂ TreeRel
                (source.flatMap NTree.children)
                (target.flatMap NTree.children) :=
            List.rel_flatMap hall (fun a b hab => childRel a b hab)
          have htotal := totalSize_flatMap_children source
          have hsourceLen : 0 < source.length := List.length_pos_of_ne_nil hsource
          have hlt : totalSize (source.flatMap NTree.children) < n := by
            change totalSize source ≤ n at hsize
            omega
          rw [bfsForest_cons_eq source hsource,
            bfsForest_cons_eq target htarget, List.map_append, List.map_append]
          exact List.rel_append hroots
            (ih _ hlt le_rfl hchildren)

namespace ComputeTreeBinds

/-- Recursive compute-tree binding induces the canonical BFS row binding mechanically. -/
theorem bfs_rows {z : K} {s : NTree ComputeRowSkeleton}
    {tree : NTree (ComputeTable.State × ComputeTable.DTcomp K)}
    (h : ComputeTreeBinds z s tree) :
    List.Forall₂ (BindComputeRow z)
      ((bfsForest [s]).map NTree.label)
      ((bfsForest [tree]).map NTree.label) :=
  bfsRows_ofTreeBindings (BindComputeRow z) (ComputeTreeBinds z)
    (fun _ _ ht => ht.root) (fun _ _ ht => ht.children) (.cons h .nil)

end ComputeTreeBinds

namespace MemoryTreeBinds

/-- Forest form: recursive memory-tree bindings induce aggregate canonical BFS row bindings while
preserving forest-root order. -/
theorem forest_bfs_rows {z : K}
    {ss : List (NTree MemoryRowSkeleton)}
    {trees : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))}
    (h : List.Forall₂ (MemoryTreeBinds z) ss trees) :
    List.Forall₂ (BindMemoryRow z)
      ((bfsForest ss).map NTree.label)
      ((bfsForest trees).map NTree.label) :=
  bfsRows_ofTreeBindings (BindMemoryRow z) (MemoryTreeBinds z)
    (fun _ _ ht => ht.root) (fun _ _ ht => ht.children) h

/-- Single-tree specialization of `forest_bfs_rows`. -/
theorem bfs_rows {z : K} {s : NTree MemoryRowSkeleton}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : MemoryTreeBinds z s tree) :
    List.Forall₂ (BindMemoryRow z)
      ((bfsForest [s]).map NTree.label)
      ((bfsForest [tree]).map NTree.label) :=
  forest_bfs_rows (.cons h .nil)

end MemoryTreeBinds

/-- Full canonical binding to one later exact execution.  The recursive clauses pin tree shape and
child order; the BFS clauses pin every canonical flat row index used by the exact tables. -/
structure BindsAt (z : K) (S : SemanticSkeleton)
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop where
  sampledSeed : cfg.challenges.z = z
  computeTree : ComputeTreeBinds z S.computeTree exec.computeTree
  memoryForest : List.Forall₂ (MemoryTreeBinds z) S.memoryForest exec.memoryForest
  computeRows :
    List.Forall₂ (BindComputeRow z) (computeSkeletonRows S) exec.computeRows
  memoryRows :
    List.Forall₂ (BindMemoryRow z) (memorySkeletonRows S) exec.memoryRows

namespace BindsAt

/-- Preferred constructor: recursive bindings are the source of truth; canonical flat bindings are
derived rather than independently supplied. -/
def ofTreeBindings {z : K} {S : SemanticSkeleton}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (sampledSeed : cfg.challenges.z = z)
    (computeTree : ComputeTreeBinds z S.computeTree exec.computeTree)
    (memoryForest :
      List.Forall₂ (MemoryTreeBinds z) S.memoryForest exec.memoryForest) :
    BindsAt z S cfg exec where
  sampledSeed := sampledSeed
  computeTree := computeTree
  memoryForest := memoryForest
  computeRows := by
    simpa [computeSkeletonRows, ExactExecution.computeRows] using computeTree.bfs_rows
  memoryRows := by
    simpa [memorySkeletonRows, ExactExecution.memoryRows] using
      MemoryTreeBinds.forest_bfs_rows memoryForest

/-- The compute flat binding consumed downstream is derivable from the recursive field, even for a
legacy `BindsAt` value whose redundant flat proof was supplied directly. -/
theorem derived_computeRows {z : K} {S : SemanticSkeleton}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : BindsAt z S cfg exec) :
    List.Forall₂ (BindComputeRow z) (computeSkeletonRows S) exec.computeRows := by
  simpa [computeSkeletonRows, ExactExecution.computeRows] using h.computeTree.bfs_rows

/-- The memory flat binding consumed downstream is likewise exactly the aggregate BFS relation
derived from the recursive ordered forest binding. -/
theorem derived_memoryRows {z : K} {S : SemanticSkeleton}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : BindsAt z S cfg exec) :
    List.Forall₂ (BindMemoryRow z) (memorySkeletonRows S) exec.memoryRows := by
  simpa [memorySkeletonRows, ExactExecution.memoryRows] using
    MemoryTreeBinds.forest_bfs_rows h.memoryForest

end BindsAt

/-! ## Pre-seed boundedness -/

def MemRecSkeleton.BoundedBy (q : ℕ) (s : MemRecSkeleton) : Prop :=
  FieldEmbedding.BoundedBy q s.root ∧
    FieldEmbedding.BoundedBy q s.child

/- Nat axes are precommitted and bound to field casts by `BindMemRec`, but noun realization does
not require an axis range hypothesis.  The separate discrimination theorem
`shared_slot_axis_eq` therefore takes `axis < q` assumptions explicitly instead of strengthening
this noun-only boundedness predicate. -/

def ComputeRowSkeleton.BoundedBy (q : ℕ) (s : ComputeRowSkeleton) : Prop :=
  FieldEmbedding.BoundedBy q s.subject ∧
  FieldEmbedding.BoundedBy q s.formula ∧
  FieldEmbedding.BoundedBy q s.evaluation ∧
  (∀ slot h, FieldEmbedding.BoundedBy q (s.decomposition slot h)) ∧
  (∀ i h slot, FieldEmbedding.BoundedBy q (s.subformula i h slot)) ∧
  (∀ i h, (s.memoryRecord i h).BoundedBy q)

def MemoryRowSkeleton.BoundedBy (q : ℕ) (s : MemoryRowSkeleton) : Prop :=
  FieldEmbedding.BoundedBy q s.parent ∧
  (∀ i h, FieldEmbedding.BoundedBy q (s.child i h)) ∧
  (∀ h, (s.memoryRecord h).BoundedBy q)

structure SemanticSkeleton.BoundedBy (q : ℕ) (S : SemanticSkeleton) : Prop where
  computeRows : (computeSkeletonRows S).Forall (ComputeRowSkeleton.BoundedBy q)
  memoryRows : (memorySkeletonRows S).Forall (MemoryRowSkeleton.BoundedBy q)
  memoryTrees :
    ∀ tree ∈ S.memoryForest, ∀ node, InTree tree node →
      node.label.BoundedBy q

/-! ## Row realization -/

/-- Separate realization predicate for the private `Dec` columns omitted by
`ExactExecutionNounRealization`.

Every state-active decomposition slot has a bounded noun realization; inactive slots
contribute `True` (C7: `Vcomp` does not mention them, and `BindComputeRow`'s else-branch
is `True`).  This is intentionally a separate bridge for
`SemanticTrace.ComputeRowSemanticData` and its `RootRealization`/`TailRealization`/
`BranchTailRealization` inputs rather than a silent change to the established public-row language.
-/
structure DecColumnNounRealization
    (q : ℕ) (row : ComputeTable.State × ComputeTable.DTcomp K) : Prop where
  slot :
    ∀ slot : DecSlot,
      if decActive row.1 slot = true then
        FPSlotRealized row.2.1.z q .active (decFP row.2.2.2 slot)
      else True

def ComputeDecColumnsNounRealization
    (q : ℕ) (rows : List (ComputeTable.State × ComputeTable.DTcomp K)) : Prop :=
  rows.Forall (DecColumnNounRealization q)

/-- Aggregate private-column realization on the exact canonical compute BFS rows. -/
def ExactExecutionDecColumnNounRealization
    (q : ℕ) {cfg : ExactConfig F K} (exec : ExactExecution cfg) : Prop :=
  ComputeDecColumnsNounRealization q exec.computeRows

theorem bindFP_realized {z : K} (hz : z ≠ 0) {q : ℕ} {n : Noun}
    {fp : ComputeTable.FP K} (hb : FieldEmbedding.BoundedBy q n)
    (h : bindFP z n fp) :
    FPSlotRealized z q .active fp := by
  refine ⟨⟨n, hb, h.symm⟩, ?_⟩
  exact FPRealized.ne_zero hz ⟨n, hb, h.symm⟩

theorem bindMemRec_realized {z : K} (hz : z ≠ 0) {q : ℕ}
    {s : MemRecSkeleton} {r : ComputeTable.MemRec K}
    (hb : s.BoundedBy q) (h : BindMemRec z s r) :
    MemRecSlotRealized z q .active r := by
  refine ⟨?_, bindFP_realized hz hb.1 h.1, bindFP_realized hz hb.2 h.2.1⟩
  intro hr
  have hroot : r.root = 0 := by rw [hr]; rfl
  exact (bindFP_realized hz hb.1 h.1).2 hroot

theorem bindMemRow_realized {z : K} (hz : z ≠ 0) {q : ℕ}
    {s : MemRecSkeleton} {r : ComputeTable.MemRec K} {cprime lmb : K}
    (hb : s.BoundedBy q) (h : BindMemRow z s r cprime lmb) :
    MemRecSlotRealized z q .active r := by
  refine ⟨?_, bindFP_realized hz hb.1 h.1, bindFP_realized hz hb.2 h.2.1⟩
  intro hr
  have hroot : r.root = 0 := by rw [hr]; rfl
  exact (bindFP_realized hz hb.1 h.1).2 hroot

theorem bindComputeRow_decColumns {z : K} (hz : z ≠ 0) {q : ℕ}
    {s : ComputeRowSkeleton}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hb : s.BoundedBy q) (h : BindComputeRow z s row) :
    DecColumnNounRealization q row := by
  obtain ⟨houter, hseed, hstate, hs, hf, he, hdec, hsf, hmr⟩ := h
  refine ⟨?_⟩
  intro slot
  by_cases ha : decActive s.state slot = true
  · simp only [show decActive row.1 slot = true from houter ▸ ha, ↓reduceIte, hseed]
    have hh := hdec slot
    simp only [dif_pos ha] at hh
    exact bindFP_realized hz (hb.2.2.2.1 slot ha) hh
  · simp only [show ¬ (decActive row.1 slot = true) from houter ▸ ha, ↓reduceIte]
    trivial

theorem bindComputeRow_realized {z : K} (hz : z ≠ 0) {q : ℕ}
    {s : ComputeRowSkeleton}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hb : s.BoundedBy q) (h : BindComputeRow z s row) :
    ComputePublicRowNounRealization q (computePublicLabel row) := by
  obtain ⟨houter, hseed, hstate, hs, hf, he, hdec, hsf, hmr⟩ := h
  simp only [computePublicLabel]
  have realizeFP {n : Noun} {fp : ComputeTable.FP K}
      (hn : FieldEmbedding.BoundedBy q n) (heq : bindFP z n fp) :
      FPSlotRealized row.2.1.z q .active fp := by
    rw [hseed]
    exact bindFP_realized hz hn heq
  have realizeMR {m : MemRecSkeleton} {r : ComputeTable.MemRec K}
      (hmBound : m.BoundedBy q) (heq : BindMemRec z m r) :
      MemRecSlotRealized row.2.1.z q .active r := by
    rw [hseed]
    exact bindMemRec_realized hz hmBound heq
  refine
    { subject := realizeFP hb.1 hs
      formula := realizeFP hb.2.1 hf
      evaluation := realizeFP hb.2.2.1 he
      subformula := ?_
      memoryRecord := ?_ }
  · intro i
    by_cases hi : (i : ℕ) < ComputeTable.fanoutComp s.state
    · have hi' : computeSubformulaKind row.1 i = .active := by
        simp [computeSubformulaKind, houter, hi]
      rw [hi']
      have hh := hsf i
      simp only [dif_pos hi] at hh
      exact ⟨realizeFP (hb.2.2.2.2.1 i hi .subject) (hh .subject),
        realizeFP (hb.2.2.2.2.1 i hi .formula) (hh .formula),
        realizeFP (hb.2.2.2.2.1 i hi .result) (hh .result)⟩
    · have hi' : computeSubformulaKind row.1 i = .padding := by
        simp [computeSubformulaKind, houter, hi]
      rw [hi']
      have hh := hsf i
      simp only [dif_neg hi] at hh
      change
        (computeSubformulaFPs row.2.2.1 i).1 = 0 ∧
          (computeSubformulaFPs row.2.2.1 i).2.1 = 0 ∧
          (computeSubformulaFPs row.2.2.1 i).2.2 = 0
      exact
        ⟨congrArg Prod.fst hh,
          congrArg (fun x => x.2.1) hh,
          congrArg (fun x => x.2.2) hh⟩
  · intro i
    by_cases hi : (i : ℕ) < Nock.Framework.recordCount s.state
    · have hi' : computeMemRecKind row.1 i = .active := by
        simp [computeMemRecKind, houter, hi]
      rw [hi']
      have hh := hmr i
      simp only [dif_pos hi] at hh
      exact realizeMR (hb.2.2.2.2.2 i hi) hh
    · have hi' : computeMemRecKind row.1 i = .padding := by
        simp [computeMemRecKind, houter, hi]
      rw [hi']
      have hh := hmr i
      simp only [dif_neg hi] at hh
      exact hh

theorem bindMemoryRow_realized {z : K} (hz : z ≠ 0) {q : ℕ}
    {s : MemoryRowSkeleton}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (hb : s.BoundedBy q) (h : BindMemoryRow z s row) :
    MemoryPublicRowNounRealization q row := by
  obtain ⟨houter, hseed, hstate, hpt, hchild, hmem, _hver⟩ := h
  have realizeFP {n : Noun} {fp : ComputeTable.FP K}
      (hn : FieldEmbedding.BoundedBy q n) (heq : bindFP z n fp) :
      FPSlotRealized row.2.1.z q .active fp := by
    rw [hseed]
    exact bindFP_realized hz hn heq
  have realizeMR {m : MemRecSkeleton} {r : ComputeTable.MemRec K} {c l : K}
      (hmBound : m.BoundedBy q) (heq : BindMemRow z m r c l) :
      MemRecSlotRealized row.2.1.z q .active r := by
    rw [hseed]
    exact bindMemRow_realized hz hmBound heq
  refine
    { parent := realizeFP hb.1 hpt
      child := ?_
      memoryRecord := ?_ }
  · intro i
    by_cases hi : (i : ℕ) < MemoryTable.fanoutMem s.state
    · have hi' : memoryChildKind row.1 i = .active := by
        simp [memoryChildKind, houter, hi]
      rw [hi']
      have hh := hchild i
      simp only [dif_pos hi] at hh
      change FPSlotRealized row.2.1.z q .active (memoryChildCell row.2.2 i).noun
      exact realizeFP (hb.2.1 i hi) hh
    · have hi' : memoryChildKind row.1 i = .padding := by
        simp [memoryChildKind, houter, hi]
      rw [hi']
      have hh := hchild i
      simp only [dif_neg hi] at hh
      exact hh
  · cases hk : memoryMemRecKind s.state with
    | active =>
        have hk' : memoryMemRecKind row.1 = .active := by simpa [houter] using hk
        rw [hk']
        have hh := hmem
        have hactive : memoryMemRecKind s.state = .active := hk
        rw [dif_pos hactive] at hh
        exact realizeMR (hb.2.2 hactive) hh
    | padding =>
        have hk' : memoryMemRecKind row.1 = .padding := by simpa [houter] using hk
        rw [hk']
        have hh := hmem
        have hnot : memoryMemRecKind s.state ≠ .active := by
          rw [hk]
          decide
        rw [dif_neg hnot] at hh
        exact hh

private theorem forall₂_realize_compute {z : K} (hz : z ≠ 0) {q : ℕ} :
    ∀ {ss : List ComputeRowSkeleton}
      {rows : List (ComputeTable.State × ComputeTable.DTcomp K)},
      ss.Forall (ComputeRowSkeleton.BoundedBy q) →
      List.Forall₂ (BindComputeRow z) ss rows →
      (rows.map computePublicLabel).Forall (ComputePublicRowNounRealization q) := by
  intro ss rows hb hbind
  induction hbind with
  | nil => simp
  | cons hs htail ih =>
      rw [List.forall_cons] at hb
      rw [List.map_cons, List.forall_cons]
      exact ⟨bindComputeRow_realized hz hb.1 hs, ih hb.2⟩

private theorem forall₂_realize_memory {z : K} (hz : z ≠ 0) {q : ℕ} :
    ∀ {ss : List MemoryRowSkeleton}
      {rows : List (MemoryTable.MState × MemoryTable.DTmem K)},
      ss.Forall (MemoryRowSkeleton.BoundedBy q) →
      List.Forall₂ (BindMemoryRow z) ss rows →
      rows.Forall (MemoryPublicRowNounRealization q) := by
  intro ss rows hb hbind
  induction hbind with
  | nil => simp
  | cons hs htail ih =>
      rw [List.forall_cons] at hb ⊢
      exact ⟨bindMemoryRow_realized hz hb.1 hs, ih hb.2⟩

private theorem forall₂_realize_decColumns {z : K} (hz : z ≠ 0) {q : ℕ} :
    ∀ {ss : List ComputeRowSkeleton}
      {rows : List (ComputeTable.State × ComputeTable.DTcomp K)},
      ss.Forall (ComputeRowSkeleton.BoundedBy q) →
      List.Forall₂ (BindComputeRow z) ss rows →
      rows.Forall (DecColumnNounRealization q) := by
  intro ss rows hb hbind
  induction hbind with
  | nil => simp
  | cons hs htail ih =>
      rw [List.forall_cons] at hb ⊢
      exact ⟨bindComputeRow_decColumns hz hb.1 hs, ih hb.2⟩

/-! ## Recursive precommitted memory atoms -/

theorem memoryTree_leafAtoms {z : K} {q : ℕ} :
    ∀ {st : NTree MemoryRowSkeleton}
      {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)},
      (∀ node, InTree st node → node.label.BoundedBy q) →
      MemoryTreeBinds z st tree →
      MemoryLeafAtomsRealized q tree := by
  intro st tree hb hbind
  cases st with
  | node s sc =>
      cases tree with
      | node row rc =>
          rcases row with ⟨rowState, rowData⟩
          cases hbind with
          | node hshape hrow hchildren =>
          have hsBound := hb (.node s sc) (InTree.here _)
          rcases hrow with ⟨hstate, hseed, hpubState, hpt, hchild, hmem⟩
          change rowState = s.state at hstate
          subst rowState
          cases hs : s.state with
          | halt =>
              have hlen : sc.length = 0 := by
                simpa [MemoryTable.fanoutMem, hs] using hshape
              have hsc : sc = [] := List.eq_nil_of_length_eq_zero hlen
              subst hsc
              cases hchildren
              simp only [MemoryLeafAtomsRealized]
              let hhalt : s.state = .halt := hs
              have hatomBound : s.haltAtom hhalt < q := by
                have hpBound := hsBound.1
                change FieldEmbedding.BoundedBy q s.parent at hpBound
                rw [s.haltParent hhalt] at hpBound
                exact hpBound
              refine ⟨s.haltAtom hhalt, hatomBound, ?_⟩
              have hp := s.haltParent hhalt
              rw [hp] at hpt
              have hleaf := congrArg ComputeTable.FP.leaf hpt
              simpa [bindFP, GlobalCarryRecognizer.enc_atom] using hleaf.symm
          | decompose =>
              have hlen : sc.length = rc.length := hchildren.length_eq
              have hsc : sc.length = 2 := by
                simpa [MemoryTable.fanoutMem, hs] using hshape
              obtain ⟨sl, sr, rfl⟩ := List.length_eq_two.mp hsc
              have hrc : rc.length = 2 := by omega
              obtain ⟨tl, tr, rfl⟩ := List.length_eq_two.mp hrc
              cases hchildren with
              | cons hleft hrest =>
                  cases hrest with
                  | cons hright hnil =>
                      simp only [MemoryLeafAtomsRealized]
                      exact
                        ⟨memoryTree_leafAtoms (st := sl) (tree := tl)
                            (fun node hn => hb node (InTree.sub (by simp) hn)) hleft,
                          memoryTree_leafAtoms (st := sr) (tree := tr)
                            (fun node hn => hb node (InTree.sub (by simp) hn)) hright⟩
          | read_root =>
              have hsc : sc.length = 1 := by
                simpa [MemoryTable.fanoutMem, hs] using hshape
              obtain ⟨schild, rfl⟩ := List.length_eq_one_iff.mp hsc
              have hrc : rc.length = 1 := by simpa using hchildren.length_eq.symm
              obtain ⟨tchild, rfl⟩ := List.length_eq_one_iff.mp hrc
              cases hchildren with
              | cons hchildBind hnil =>
                  simp only [MemoryLeafAtomsRealized]
                  have hsub : InTree (.node s [schild]) schild :=
                    InTree.sub (by simp) (InTree.here _)
                  exact memoryTree_leafAtoms (st := schild) (tree := tchild)
                    (fun node hn => hb node (InTree_trans hsub hn)) hchildBind
          | verify_child =>
              have hsc : sc.length = 1 := by
                simpa [MemoryTable.fanoutMem, hs] using hshape
              obtain ⟨schild, rfl⟩ := List.length_eq_one_iff.mp hsc
              have hrc : rc.length = 1 := by simpa using hchildren.length_eq.symm
              obtain ⟨tchild, rfl⟩ := List.length_eq_one_iff.mp hrc
              cases hchildren with
              | cons hchildBind hnil =>
                  simp only [MemoryLeafAtomsRealized]
                  have hsub : InTree (.node s [schild]) schild :=
                    InTree.sub (by simp) (InTree.here _)
                  exact memoryTree_leafAtoms (st := schild) (tree := tchild)
                    (fun node hn => hb node (InTree_trans hsub hn)) hchildBind

private theorem forest_leafAtoms {z : K} {q : ℕ}
    {ss : List (NTree MemoryRowSkeleton)}
    {trees : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))}
    (hb : ∀ tree ∈ ss, ∀ node, InTree tree node → node.label.BoundedBy q)
    (hbind : List.Forall₂ (MemoryTreeBinds z) ss trees) :
    ∀ tree ∈ trees, MemoryLeafAtomsRealized q tree := by
  intro tree htree
  induction hbind with
  | nil => simp at htree
  | cons hhead htail ih =>
      simp only [List.mem_cons] at htree
      rcases htree with rfl | htree
      · exact memoryTree_leafAtoms (hb _ (by simp)) hhead
      · exact ih (fun t ht => hb t (by simp [ht])) htree

/-! ## Main noun-existence theorem -/

/-- All private decomposition columns on canonical compute rows are realized from the recursive
tree binding and noun bounds.  No independently supplied `BindsAt.computeRows` proof is used. -/
theorem BindsAt.decColumnNounRealization {z : K} (hz : z ≠ 0) {q : ℕ}
    {S : SemanticSkeleton} (hb : S.BoundedBy q)
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : BindsAt z S cfg exec) :
    ExactExecutionDecColumnNounRealization q exec := by
  exact forall₂_realize_decColumns hz hb.computeRows h.derived_computeRows

theorem BindsAt.nounRealization {z : K} (hz : z ≠ 0) {q : ℕ}
    {S : SemanticSkeleton} (hb : S.BoundedBy q)
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : BindsAt z S cfg exec) :
    ExactExecutionNounRealization q cfg exec := by
  refine
    { computeTree := ?_
      memoryForest := ?_
      memoryLeaves := ?_ }
  · unfold ComputePublicTreeNounRealization ComputePublicRowsNounRealization
    rw [ExactExecution.computePublicTree_bfs]
    exact forall₂_realize_compute hz hb.computeRows h.derived_computeRows
  · exact forall₂_realize_memory hz hb.memoryRows h.derived_memoryRows
  · exact forest_leafAtoms hb.memoryTrees h.memoryForest

/-! ## Root projections and P8 adapter -/

def SemanticSkeleton.publicClaim (S : SemanticSkeleton) : P8PublicClaim where
  subject := S.computeTree.label.subject
  formula := S.computeTree.label.formula
  result := S.computeTree.label.evaluation

theorem BindsAt.root_bindings {z : K} {S : SemanticSkeleton}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : BindsAt z S cfg exec) :
    bindFP z S.publicClaim.subject exec.computeTree.label.2.2.1.s ∧
      bindFP z S.publicClaim.formula exec.computeTree.label.2.2.1.f ∧
      bindFP z S.publicClaim.result exec.computeTree.label.2.2.1.e := by
  have hr := h.computeTree.root
  exact ⟨hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1⟩

/-- Canonical index zero is the authoritative compute-tree root. -/
theorem computePubAt_root_eq {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.computePubAt ⟨0, cfg.compRows_pos⟩ = exec.computeTree.label.2.2.1 := by
  unfold ExactExecution.computePubAt ExactExecution.computeRowAt ExactExecution.computeRows
  simp [bfsForest]
  rfl

variable {p : ℕ} [CharP K p]

/-- The post-seed payload other than the legacy three root equations. -/
structure SeedPayload (z : K) where
  family : PlusIOSegmentedFamily F K
  sampledSeed : family.problem.cfg.challenges.z = z
  computeTableAux : ExactCanonicalProgAux family.problem
  memoryTableAux : ExactCanonicalMemAux family.problem
  exactIO : ExactDerivedIOAssignment family p

/-- Construct the legacy root-bound commitment by projection from the full skeleton binding. -/
def SeedPayload.toP8SeedCommitment
    {S : SemanticSkeleton} {z : K} (P : SeedPayload (F := F) (K := K) (p := p) z)
    (hbind : BindsAt z S P.family.problem.cfg P.family.problem.exec) :
    P8SeedCommitment (F := F) (K := K) S.publicClaim z where
  family := P.family
  sampled_seed := P.sampledSeed
  subject_binding := by
    rw [exactRootComputePub, computePubAt_root_eq]
    exact hbind.root_bindings.1
  formula_binding := by
    rw [exactRootComputePub, computePubAt_root_eq]
    exact hbind.root_bindings.2.1
  result_binding := by
    rw [exactRootComputePub, computePubAt_root_eq]
    exact hbind.root_bindings.2.2
  computeTableAux := P.computeTableAux
  memoryTableAux := P.memoryTableAux
  exactIO := P.exactIO

/-- A seed payload together with the full pre-seed binding.  Its `commitment` projection generates
the old three root equations from that binding. -/
structure BoundSeedCommitment (S : SemanticSkeleton) (z : K) where
  payload : SeedPayload (F := F) (K := K) (p := p) z
  binds :
    BindsAt z S payload.family.problem.cfg payload.family.problem.exec

def BoundSeedCommitment.commitment
    {S : SemanticSkeleton} {z : K}
    (C : BoundSeedCommitment (F := F) (K := K) (p := p) S z) :
    P8SeedCommitment (F := F) (K := K) S.publicClaim z :=
  C.payload.toP8SeedCommitment C.binds

/-- Challenge-ordered P8 strategy whose full skeleton, not merely its public root, is fixed before
`z`.  Forgetting `binds` gives the existing `P8Strategy` interface unchanged. -/
structure BoundP8Strategy where
  skeleton : SemanticSkeleton
  afterSeed : ∀ z : K, z ≠ 0 → BoundSeedCommitment (F := F) (K := K) skeleton z
  afterWalk :
    ∀ (ω : JointCoins K) (hz : nprSeed ω ≠ 0),
      P8WalkResponse ((afterSeed (nprSeed ω) hz).commitment) ω

def BoundP8Strategy.toP8Strategy (T : BoundP8Strategy (F := F) (K := K)) :
    P8Strategy (F := F) (K := K) where
  claim := T.skeleton.publicClaim
  afterSeed z hz := (T.afterSeed z hz).commitment
  afterWalk ω hz := T.afterWalk ω hz

theorem BoundP8Strategy.nounRealizationAt
    (T : BoundP8Strategy (F := F) (K := K)) {q : ℕ}
    (hb : T.skeleton.BoundedBy q) (z : K) (hz : z ≠ 0) :
    let C := T.afterSeed z hz
    ExactExecutionNounRealization q C.payload.family.problem.cfg
      C.payload.family.problem.exec := by
  dsimp
  exact (T.afterSeed z hz).binds.nounRealization hz hb

/-! ## Non-splicing discrimination -/

/-- At one canonical slot, two pre-seed assignments bound to the same after-seed fingerprint
cannot differ once that exact pair is covered by the P8 collision census (`PairFaithful`). -/
theorem shared_slot_noun_eq {z : K} {q : ℕ} {fp : ComputeTable.FP K}
    {left right : Noun}
    (hl : bindFP z left fp) (hr : bindFP z right fp)
    (hfaith : OpcodeSemantics.PairFaithful z q left right)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q)) :
    left = right := by
  apply hfaith.eq_of_enc_eq hcast
  exact hl.symm.trans hr

/-- Nat axes in one canonical record slot cannot be spliced when both are in the bounded range and
Nat casts are injective there. -/
theorem shared_slot_axis_eq {q : ℕ} {left right : ℕ}
    (hl : left < q) (hr : right < q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (heq : (left : K) = (right : K)) :
    left = right :=
  hcast hl hr heq

/-- Both bindings address the same
canonical root of the same execution; the only extra assumptions are the three exact
`PairFaithful` events and bounded Nat-cast injectivity used by the P8 collision census. -/
theorem BindsAt.shared_root_nouns_eq
    {z : K} {q : ℕ} {left right : SemanticSkeleton}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hl : BindsAt z left cfg exec) (hr : BindsAt z right cfg exec)
    (hs : OpcodeSemantics.PairFaithful z q
      left.publicClaim.subject right.publicClaim.subject)
    (hf : OpcodeSemantics.PairFaithful z q
      left.publicClaim.formula right.publicClaim.formula)
    (he : OpcodeSemantics.PairFaithful z q
      left.publicClaim.result right.publicClaim.result)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q)) :
    left.publicClaim = right.publicClaim := by
  have hsEq :=
    shared_slot_noun_eq hl.root_bindings.1 hr.root_bindings.1 hs hcast
  have hfEq :=
    shared_slot_noun_eq hl.root_bindings.2.1 hr.root_bindings.2.1 hf hcast
  have heEq :=
    shared_slot_noun_eq hl.root_bindings.2.2 hr.root_bindings.2.2 he hcast
  cases hleft : left.publicClaim
  cases hright : right.publicClaim
  simp_all

/-- Honest scope: full skeleton injectivity is exactly the conjunction of canonical topology
agreement and pair-faithfulness for every differing noun assignment.  `BindsAt` supplies the
common field equations and forbids row permutation, but `PairFaithful` itself must come from the
finite P8 collision census. -/
def FullNonSplicingHypothesis (z : K) (q : ℕ)
    (left right : SemanticSkeleton) : Prop :=
  (mapNTree (fun r => r.state) left.computeTree =
      mapNTree (fun r => r.state) right.computeTree) ∧
  (left.memoryForest.map (mapNTree (fun r => r.state)) =
      right.memoryForest.map (mapNTree (fun r => r.state))) ∧
  (∀ n₁ n₂ fp, bindFP z n₁ fp → bindFP z n₂ fp →
    OpcodeSemantics.PairFaithful z q n₁ n₂)

end

end Nock.NockVMROM.Thm54.SemanticStrategy

#print axioms Nock.NockVMROM.Thm54.SemanticStrategy.decActive_cases
#print axioms Nock.NockVMROM.Thm54.SemanticStrategy.ComputeTreeBinds.bfs_rows
#print axioms Nock.NockVMROM.Thm54.SemanticStrategy.MemoryTreeBinds.bfs_rows
#print axioms Nock.NockVMROM.Thm54.SemanticStrategy.MemoryTreeBinds.forest_bfs_rows
#print axioms Nock.NockVMROM.Thm54.SemanticStrategy.BindsAt.ofTreeBindings
#print axioms Nock.NockVMROM.Thm54.SemanticStrategy.BindsAt.derived_computeRows
#print axioms Nock.NockVMROM.Thm54.SemanticStrategy.BindsAt.derived_memoryRows
#print axioms Nock.NockVMROM.Thm54.SemanticStrategy.bindComputeRow_decColumns
#print axioms Nock.NockVMROM.Thm54.SemanticStrategy.BindsAt.decColumnNounRealization
#print axioms Nock.NockVMROM.Thm54.SemanticStrategy.bindComputeRow_realized
#print axioms Nock.NockVMROM.Thm54.SemanticStrategy.memoryTree_leafAtoms
#print axioms Nock.NockVMROM.Thm54.SemanticStrategy.BindsAt.nounRealization
#print axioms Nock.NockVMROM.Thm54.SemanticStrategy.BindsAt.root_bindings
#print axioms Nock.NockVMROM.Thm54.SemanticStrategy.SeedPayload.toP8SeedCommitment
#print axioms Nock.NockVMROM.Thm54.SemanticStrategy.BoundP8Strategy.nounRealizationAt
#print axioms Nock.NockVMROM.Thm54.SemanticStrategy.shared_slot_noun_eq
#print axioms Nock.NockVMROM.Thm54.SemanticStrategy.BindsAt.shared_root_nouns_eq
