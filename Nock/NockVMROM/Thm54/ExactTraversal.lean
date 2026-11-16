import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.Framework.Traversal

/-!
# Exact cumulative Theorem 5.4 traversal layer

This module is the P6 refinement of the forest-first P3 carrier.  It does not infer topology from
`ChainedSemanticExactLanguage`: the cumulative predicate below adds exact arity-3 compute and
arity-2 memory `RVT` facts on the same authoritative `computeTree` and `memoryForest`.

The public compute tree omits `Dec`; the authoritative tree retains `Dec` in its aligned witness
labels.  Consequently no public/private tree identification is asserted.
-/

namespace Nock.NockVMROM.Thm54

open scoped Classical
open Nock Nock.Walk Nock.Reified

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## Public compute projection and aligned decided-column witness -/

/-- Public compute labels retain the outer state and the complete `(Inputs, Pub)` row. -/
abbrev ComputePublicLabel (K : Type) [Field K] :=
  ComputeTable.State × (ComputeTable.Inputs K × ComputeTable.Pub K)

/-- Forget exactly the private `Dec` component of a compute label. -/
def computePublicLabel (row : ComputeTable.State × ComputeTable.DTcomp K) :
    ComputePublicLabel K :=
  (row.1, (row.2.1, row.2.2.1))

/-- The decided columns retained by the witness side of an exact public row. -/
def computeWitnessDec (row : ComputeTable.State × ComputeTable.DTcomp K) :
    ComputeTable.Dec K :=
  row.2.2.2

/-- Reassemble the authoritative private label from a public label and its aligned `Dec`. -/
def alignComputeLabel (row : ComputePublicLabel K × ComputeTable.Dec K) :
    ComputeTable.State × ComputeTable.DTcomp K :=
  (row.1.1, (row.1.2.1, (row.1.2.2, row.2)))

@[simp]
theorem alignComputeLabel_split (row : ComputeTable.State × ComputeTable.DTcomp K) :
    alignComputeLabel (computePublicLabel row, computeWitnessDec row) = row := by
  cases row
  rfl

/-- Type-level discrimination: the public compute label ends at `Pub`; `Dec` is not a field of
this type. -/
theorem computePublicLabel_type :
    ComputePublicLabel K =
      (ComputeTable.State × (ComputeTable.Inputs K × ComputeTable.Pub K)) :=
  rfl

/-- Field-level discrimination: state, inputs, and public columns are projected publicly, while
`Dec` is recovered only from the separate aligned witness projection. -/
theorem computePublicLabel_field_discrimination
    (row : ComputeTable.State × ComputeTable.DTcomp K) :
    (computePublicLabel row).1 = row.1 ∧
      (computePublicLabel row).2.1 = row.2.1 ∧
      (computePublicLabel row).2.2 = row.2.2.1 ∧
      computeWitnessDec row = row.2.2.2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Relabel a tree without changing any edge or child order. -/
def mapNTree {α β : Type*} (f : α → β) : NTree α → NTree β
  | .node lbl children => .node (f lbl) (children.map (mapNTree f))

@[simp]
theorem mapNTree_label {α β : Type*} (f : α → β) (t : NTree α) :
    (mapNTree f t).label = f t.label := by
  cases t
  simp [mapNTree, NTree.label]

@[simp]
theorem mapNTree_children {α β : Type*} (f : α → β) (t : NTree α) :
    (mapNTree f t).children = t.children.map (mapNTree f) := by
  cases t
  simp [mapNTree, NTree.children]

/-- The exact public projection of the authoritative Dec-carrying compute tree. -/
def ExactExecution.computePublicTree {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    NTree (ComputePublicLabel K) :=
  mapNTree computePublicLabel exec.computeTree

/-- Public and private trees are aligned when the public tree is exactly the label projection of
the private Dec-carrying witness tree. -/
def ComputeTreeWitnessAligned
    (publicTree : NTree (ComputePublicLabel K))
    (witnessTree : NTree (ComputeTable.State × ComputeTable.DTcomp K)) : Prop :=
  publicTree = mapNTree computePublicLabel witnessTree

theorem ExactExecution.computePublicTree_witnessAligned
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    ComputeTreeWitnessAligned exec.computePublicTree exec.computeTree :=
  rfl

private theorem flatMap_children_mapNTree {α β : Type*}
    (f : α → β) (l : List (NTree α)) :
    (l.map (mapNTree f)).flatMap NTree.children =
      (l.flatMap NTree.children).map (mapNTree f) := by
  induction l with
  | nil => rfl
  | cons t ts ih =>
      simp [mapNTree_children, ih]

/-- BFS commutes with exact tree relabeling. -/
theorem bfsForest_mapNTree {α β : Type*} (f : α → β) (l : List (NTree α)) :
    bfsForest (l.map (mapNTree f)) = (bfsForest l).map (mapNTree f) := by
  generalize hn : totalSize l = n
  induction n using Nat.strong_induction_on generalizing l with
  | h n ih =>
      by_cases hl : l = []
      · subst l
        simp [bfsForest_nil]
      · have hmapped : l.map (mapNTree f) ≠ [] := by simp [hl]
        rw [bfsForest_cons_eq l hl, bfsForest_cons_eq _ hmapped, List.map_append]
        have hchildren :
            (l.map (mapNTree f)).flatMap NTree.children =
              (l.flatMap NTree.children).map (mapNTree f) := by
          exact flatMap_children_mapNTree f l
        rw [hchildren]
        have hsize := totalSize_flatMap_children l
        have hpos : 0 < l.length := List.length_pos_of_ne_nil hl
        have hlt : totalSize (l.flatMap NTree.children) < n := by omega
        rw [ih _ hlt (l.flatMap NTree.children) rfl]

/-- The public BFS readout is the exact projection of every authoritative private BFS row. -/
def ExactExecution.computePublicRows {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    List (ComputePublicLabel K) :=
  exec.computeRows.map computePublicLabel

/-- The aligned decided-column witness, in the same authoritative BFS order. -/
def ExactExecution.computeDecRows {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    List (ComputeTable.Dec K) :=
  exec.computeRows.map computeWitnessDec

/-- Exact row-wise public/witness alignment: zipping and reassembling recovers the private rows
literally, rather than merely proving an inclusion into an accepted language. -/
def ComputeReadoutWitnessAligned
    (publicRows : List (ComputePublicLabel K))
    (decRows : List (ComputeTable.Dec K))
    (privateRows : List (ComputeTable.State × ComputeTable.DTcomp K)) : Prop :=
  publicRows.length = decRows.length ∧
    List.zipWith (fun p d => alignComputeLabel (p, d)) publicRows decRows = privateRows

private theorem zipWith_compute_split
    (rows : List (ComputeTable.State × ComputeTable.DTcomp K)) :
    List.zipWith (fun p d => alignComputeLabel (p, d))
        (rows.map computePublicLabel) (rows.map computeWitnessDec) = rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp [ih]

theorem ExactExecution.computeReadout_witnessAligned
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    ComputeReadoutWitnessAligned exec.computePublicRows exec.computeDecRows exec.computeRows := by
  constructor
  · simp [ExactExecution.computePublicRows, ExactExecution.computeDecRows]
  · exact zipWith_compute_split exec.computeRows

/-- The projected public tree has exactly the public BFS readout just defined. -/
theorem ExactExecution.computePublicTree_bfs
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    (bfsForest [exec.computePublicTree]).map NTree.label = exec.computePublicRows := by
  rw [show [exec.computePublicTree] = [exec.computeTree].map (mapNTree computePublicLabel) by rfl,
    bfsForest_mapNTree]
  simp [ExactExecution.computePublicRows, ExactExecution.computeRows, List.map_map,
    Function.comp_def]

@[simp]
theorem ExactExecution.computePublicRows_length
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.computePublicRows.length = cfg.compRows := by
  simp [ExactExecution.computePublicRows]

@[simp]
theorem ExactExecution.computeDecRows_length
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.computeDecRows.length = cfg.compRows := by
  simp [ExactExecution.computeDecRows]

/-! ## D5 forest round-trip and structural child positions -/

private theorem flatMap_getElem?_of_eq_some {α β : Type*} (f : α → List β) :
    ∀ (xs : List α) {k j : ℕ} {x : α}, xs[k]? = some x → j < (f x).length →
      (xs.flatMap f)[((xs.take k).flatMap f).length + j]? = (f x)[j]? := by
  intro xs
  induction xs with
  | nil =>
      intro k j x hx
      simp at hx
  | cons y ys ih =>
      intro k j x hx hj
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst x
          simpa using (List.getElem?_append_left (l₂ := ys.flatMap f) hj)
      | succ k =>
          simp only [List.getElem?_cons_succ] at hx
          simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
          rw [List.getElem?_append_right (by simp; omega)]
          have hidx :
              (List.length (f y) + List.length ((List.take k ys).flatMap f) + j) -
                  List.length (f y) =
                List.length ((List.take k ys).flatMap f) + j := by omega
          rw [hidx]
          exact ih hx hj

private theorem bfsForest_child_pos_of_eq_some {LT : Type*}
    (l : List (NTree LT)) (hl : l ≠ [])
    {i j : ℕ} {t : NTree LT} (_hi : 1 ≤ i)
    (ht : (bfsForest l)[i - 1]? = some t) (hj : j < t.children.length) :
    (bfsForest l)[firstCF l.length (foCol (bfsForest l)) i + j - 1]? =
      t.children[j]? := by
  have hflat := flatMap_getElem?_of_eq_some NTree.children (bfsForest l) ht hj
  have hqueue := bfsForest_eq_append_flatMap l hl
  let p := firstCF l.length (foCol (bfsForest l)) i + j - 1
  have hidx :
      p - l.length =
        ((bfsForest l).take (i - 1) |>.flatMap NTree.children).length + j := by
    dsimp [p]
    rw [← Sf_foCol]
    unfold firstCF
    omega
  calc
    (bfsForest l)[p]? =
        (l ++ (bfsForest l).flatMap NTree.children)[p]? :=
      congrArg (fun xs => xs[p]?) hqueue
    _ = ((bfsForest l).flatMap NTree.children)[p - l.length]? :=
      List.getElem?_append_right (by dsimp [p]; unfold firstCF; omega)
    _ = t.children[j]? := by rw [hidx]; exact hflat

/-- D5 child-position theorem for an honest nonempty aggregate BFS forest. -/
theorem exact_bfsForest_child_pos {LT : Type*} (l : List (NTree LT)) (hl : l ≠ [])
    {i j : ℕ} (hi : 1 ≤ i) (hj : j < foCol (bfsForest l) i) :
    (bfsForest l)[firstCF l.length (foCol (bfsForest l)) i + j - 1]? =
      (bfsForest l)[i - 1]?.bind (fun t => t.children[j]?) := by
  cases ht : (bfsForest l)[i - 1]? with
  | none =>
      exfalso
      unfold foCol at hj
      rw [ht] at hj
      simp at hj
  | some t =>
      have hlen : foCol (bfsForest l) i = t.children.length := by
        unfold foCol
        rw [ht]
        rfl
      simpa using bfsForest_child_pos_of_eq_some l hl hi ht (hlen ▸ hj)

private theorem buildTF_bfsForest_get {LT : Type*}
    (l : List (NTree LT)) (hl : l ≠ []) (lbl : ℕ → LT)
    (hlbl : ∀ i t, 1 ≤ i → (bfsForest l)[i - 1]? = some t → lbl i = t.label) :
    ∀ {i : ℕ} {t : NTree LT}, 1 ≤ i → (bfsForest l)[i - 1]? = some t →
      buildTF l.length (foCol (bfsForest l)) lbl (bfsForest l).length i = t := by
  intro i t hi ht
  let W := bfsForest l
  let fo := foCol W
  let h := W.length
  have hih : i ≤ h := by
    have := (List.getElem?_eq_some_iff.mp ht).1
    dsimp [W, h]
    omega
  have hSf : l.length + Sf fo h = h := by
    simpa [W, fo, h] using foCol_Sf_tilingF l hl
  have hvalid : BFSValidF l.length fo h := by
    simpa [W, fo, h] using foCol_BFSValidF l hl
  generalize hd : h + 1 - i = d
  induction d using Nat.strong_induction_on generalizing i t with
  | h d ih =>
      cases t with
      | node a ch =>
          have hfo : fo i = ch.length := by
            dsimp [fo, W, foCol]
            rw [ht]
            rfl
          rw [buildTF]
          rw [NTree.node.injEq]
          constructor
          · simpa using hlbl i (NTree.node a ch) hi ht
          · rw [List.attach_map_val,
              childIdxsF_eq l.length fo h hSf hvalid hi hih, hfo]
            apply List.ext_getElem?
            intro j
            by_cases hj : j < ch.length
            · rw [List.getElem?_map, List.getElem?_range' hj,
                List.getElem?_eq_getElem hj]
              simp only [Nat.one_mul, Option.map_some]
              let q := firstCF l.length fo i + j
              have hpos : W[q - 1]? = some ch[j] := by
                have hp := bfsForest_child_pos_of_eq_some l hl hi ht hj
                simpa [W, fo, q, List.getElem?_eq_getElem hj] using hp
              have hqh : q ≤ h := by
                have := (List.getElem?_eq_some_iff.mp hpos).1
                omega
              have hqi : 1 ≤ q := by
                dsimp [q, firstCF]
                omega
              have hlt : h + 1 - q < d := by
                have hv := hvalid i hi hih
                dsimp [q, firstCF] at *
                omega
              have heq := ih (h + 1 - q) hlt hqi hpos hqh rfl
              rw [heq]
            · rw [List.getElem?_map, List.getElem?_eq_none (by simp; omega),
                List.getElem?_eq_none (Nat.le_of_not_lt hj)]
              rfl

private theorem reconForest_eq_of_bfs_rows {LT : Type*}
    (l : List (NTree LT)) (hl : l ≠ []) (lbl : ℕ → LT)
    (hlbl : ∀ i t, 1 ≤ i → (bfsForest l)[i - 1]? = some t → lbl i = t.label) :
    reconForest l.length (foCol (bfsForest l)) lbl (bfsForest l).length = l := by
  rw [reconForest]
  apply List.ext_getElem?
  intro j
  by_cases hj : j < l.length
  · rw [List.getElem?_map, List.getElem?_range' hj,
      List.getElem?_eq_getElem hj]
    simp only [Nat.one_mul, Option.map_some]
    have hqueue := bfsForest_eq_append_flatMap l hl
    have hrow : (bfsForest l)[j]? = some l[j] := by
      calc
        (bfsForest l)[j]? =
            (l ++ (bfsForest l).flatMap NTree.children)[j]? :=
          congrArg (fun xs => xs[j]?) hqueue
        _ = l[j]? := List.getElem?_append_left hj
        _ = some l[j] := List.getElem?_eq_getElem hj
    have heq := buildTF_bfsForest_get l hl lbl hlbl (i := j + 1) (t := l[j])
      (by omega) (by simpa using hrow)
    simpa [Nat.add_comm] using congrArg some heq
  · rw [List.getElem?_map, List.getElem?_eq_none (by simp; omega),
      List.getElem?_eq_none (Nat.le_of_not_lt hj)]
    rfl

/-- D5 inverse direction: reconstructing a nonempty honest BFS forest returns that forest
literally. -/
theorem exact_reconForest_bfsForest {LT : Type*} (l : List (NTree LT)) (hl : l ≠ [])
    (fallback : LT) :
    reconForest l.length (foCol (bfsForest l))
        (fun i => ((bfsForest l)[i - 1]?).map NTree.label |>.getD fallback)
        (bfsForest l).length = l := by
  apply reconForest_eq_of_bfs_rows l hl
  intro i t hi ht
  rw [ht]
  rfl

/-- Exact equivalence between structural child labels and their D5 `firstCF` BFS positions. -/
theorem exact_childLink_firstCF_iff {LT : Type*}
    (l : List (NTree LT)) (hl : l ≠ []) {n i : ℕ} {t : NTree LT}
    (R : LT → (Fin n → Option LT) → Prop) (hi : 1 ≤ i)
    (ht : (bfsForest l)[i - 1]? = some t) :
    R t.label (fun j => t.childLabel j) ↔
      R t.label (fun j => if (j : ℕ) < foCol (bfsForest l) i then
        ((bfsForest l)[firstCF l.length (foCol (bfsForest l)) i + j - 1]?).map
          NTree.label
        else none) := by
  have hfo : foCol (bfsForest l) i = t.children.length := by
    unfold foCol
    rw [ht]
    rfl
  have hfun :
      (fun j : Fin n => t.childLabel j) =
        (fun j : Fin n => if (j : ℕ) < foCol (bfsForest l) i then
          ((bfsForest l)[firstCF l.length (foCol (bfsForest l)) i + j - 1]?).map
            NTree.label
          else none) := by
    funext j
    by_cases hj : (j : ℕ) < foCol (bfsForest l) i
    · rw [if_pos hj, bfsForest_child_pos_of_eq_some l hl hi ht (hfo ▸ hj)]
      rfl
    · have hj' : t.children.length ≤ (j : ℕ) := by rw [← hfo]; omega
      simp [hj, NTree.childLabel, NTree.childOpt, List.getElem?_eq_none hj']
  rw [hfun]

/-! ## Exact topology predicates and literal traversal clauses -/

/-- Exact arity-3 compute topology on the authoritative compute tree. -/
def ComputeExactTopology {cfg : ExactConfig F K} (exec : ExactExecution cfg) : Prop :=
  RVTWithArity (ComputeTable.Fcomp (K := K)) exec.computeTree

/-- Public arity-3 compute traversal membership.  The tree itself contains only
`State × (Inputs × Pub)` labels.  Verification existentially carries a Dec-bearing private tree
whose exact public projection is this tree and which satisfies `RVTWithArity Fcomp`. -/
def ComputePublicExactTopology
    (publicTree : NTree (ComputePublicLabel K)) : Prop :=
  ∃ witnessTree : NTree (ComputeTable.State × ComputeTable.DTcomp K),
    ComputeTreeWitnessAligned publicTree witnessTree ∧
      RVTWithArity (ComputeTable.Fcomp (K := K)) witnessTree

abbrev ComputePrivateExactWitness
    (publicTree : NTree (ComputePublicLabel K)) :=
  {witnessTree : NTree (ComputeTable.State × ComputeTable.DTcomp K) //
    ComputeTreeWitnessAligned publicTree witnessTree ∧
      RVTWithArity (ComputeTable.Fcomp (K := K)) witnessTree}

noncomputable def ComputePublicExactTopology.privateWitness
    {publicTree : NTree (ComputePublicLabel K)}
    (h : ComputePublicExactTopology publicTree) :
    ComputePrivateExactWitness publicTree :=
  ⟨Classical.choose h, Classical.choose_spec h⟩

theorem ExactExecution.computePublicExactTopology
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ComputeExactTopology exec) :
    ComputePublicExactTopology exec.computePublicTree :=
  ⟨exec.computeTree, exec.computePublicTree_witnessAligned, h⟩

/-- Exact arity-2 topology on every authoritative memory root. -/
def MemoryExactTopology {cfg : ExactConfig F K} (exec : ExactExecution cfg) : Prop :=
  ∀ t ∈ exec.memoryForest, RVTWithArity (MemoryTable.Fmem (K := K)) t

/-- The cumulative P6 language: P3 chaining plus both topology facts on the same forest-first
execution (`Def:traversable`).  No topology field is derived from `chained`. -/
structure TraversableChainedSemanticExactLanguage
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop where
  chained : ChainedSemanticExactLanguage cfg exec
  compute_topology : ComputeExactTopology exec
  memory_topology : MemoryExactTopology exec

/-- Proof-carrying members of the exact cumulative P6 language. -/
abbrev TraversableChainedAcceptedExecution (cfg : ExactConfig F K) :=
  { exec : ExactExecution cfg // TraversableChainedSemanticExactLanguage cfg exec }

/-- Static compute-root index of this exact carrier. -/
def exactCompRoots (_cfg : ExactConfig F K) : ℕ := 1

/-- Static memory-root index of this exact carrier. -/
def exactMemRoots (cfg : ExactConfig F K) : ℕ := cfg.kMem

@[simp]
theorem exactCompRoots_eq_one (cfg : ExactConfig F K) :
    exactCompRoots cfg = 1 :=
  rfl

theorem exactMemRoots_eq_forest_length
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exactMemRoots cfg = exec.memoryForest.length :=
  exec.memory_root_count.symm

theorem exactMemRoots_pos
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    0 < exactMemRoots cfg :=
  exec.memoryRootCount_pos

/-- A convenient label for the nonempty memory reconstruction's unreachable fallback branch. -/
def ExactExecution.memoryFallbackLabel
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    MemoryTable.MState × MemoryTable.DTmem K :=
  (exec.memoryForest.get
    ⟨0, List.length_pos_of_ne_nil exec.memoryForest_nonempty⟩).label

/-- Literal compute traversal clause: one root, exact RVT/arity, D3 queue facts, D5 round-trip,
and the child-link biconditional at every BFS row. -/
def ComputeExactTraversalClause {cfg : ExactConfig F K} (exec : ExactExecution cfg) : Prop :=
  [exec.computeTree].length = exactCompRoots cfg ∧
    ComputeExactTopology exec ∧
    BFSValidF [exec.computeTree].length
      (foCol (bfsForest [exec.computeTree])) (bfsForest [exec.computeTree]).length ∧
    [exec.computeTree].length +
        Sf (foCol (bfsForest [exec.computeTree])) (bfsForest [exec.computeTree]).length =
      (bfsForest [exec.computeTree]).length ∧
    reconForest [exec.computeTree].length (foCol (bfsForest [exec.computeTree]))
        (fun i => ((bfsForest [exec.computeTree])[i - 1]?).map NTree.label
          |>.getD exec.computeTree.label)
        (bfsForest [exec.computeTree]).length = [exec.computeTree] ∧
    ∀ i t, 1 ≤ i → (bfsForest [exec.computeTree])[i - 1]? = some t →
      (ComputeTable.childLinkComp t.label (fun j => t.childLabel j) ↔
        ComputeTable.childLinkComp t.label
          (fun j => if (j : ℕ) < foCol (bfsForest [exec.computeTree]) i then
            ((bfsForest [exec.computeTree])[
              firstCF [exec.computeTree].length
                (foCol (bfsForest [exec.computeTree])) i + j - 1]?).map NTree.label
            else none))

/-- Literal memory traversal clause, with the configured root count identified with the actual
nonempty forest length. -/
def MemoryExactTraversalClause {cfg : ExactConfig F K} (exec : ExactExecution cfg) : Prop :=
  exec.memoryForest.length = exactMemRoots cfg ∧
    exec.memoryForest ≠ [] ∧
    MemoryExactTopology exec ∧
    BFSValidF exec.memoryForest.length
      (foCol (bfsForest exec.memoryForest)) (bfsForest exec.memoryForest).length ∧
    exec.memoryForest.length +
        Sf (foCol (bfsForest exec.memoryForest)) (bfsForest exec.memoryForest).length =
      (bfsForest exec.memoryForest).length ∧
    reconForest exec.memoryForest.length (foCol (bfsForest exec.memoryForest))
        (fun i => ((bfsForest exec.memoryForest)[i - 1]?).map NTree.label
          |>.getD exec.memoryFallbackLabel)
        (bfsForest exec.memoryForest).length = exec.memoryForest ∧
    ∀ i t, 1 ≤ i → (bfsForest exec.memoryForest)[i - 1]? = some t →
      (MemoryTable.childLinkMem t.label (fun j => t.childLabel j) ↔
        MemoryTable.childLinkMem t.label
          (fun j => if (j : ℕ) < foCol (bfsForest exec.memoryForest) i then
            ((bfsForest exec.memoryForest)[
              firstCF exec.memoryForest.length
                (foCol (bfsForest exec.memoryForest)) i + j - 1]?).map NTree.label
            else none))

theorem computeExactTopology_iff_traversalClause
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    ComputeExactTopology exec ↔ ComputeExactTraversalClause exec := by
  constructor
  · intro htop
    refine ⟨rfl, htop, foCol_BFSValidF _ (by simp), foCol_Sf_tilingF _ (by simp),
      exact_reconForest_bfsForest _ (by simp) _, ?_⟩
    intro i t hi ht
    exact exact_childLink_firstCF_iff [exec.computeTree] (by simp)
      ComputeTable.childLinkComp hi ht
  · exact fun h => h.2.1

theorem memoryExactTopology_iff_traversalClause
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    MemoryExactTopology exec ↔ MemoryExactTraversalClause exec := by
  constructor
  · intro htop
    refine ⟨exec.memory_root_count, exec.memoryForest_nonempty, htop,
      foCol_BFSValidF _ exec.memoryForest_nonempty,
      foCol_Sf_tilingF _ exec.memoryForest_nonempty,
      exact_reconForest_bfsForest _ exec.memoryForest_nonempty _, ?_⟩
    intro i t hi ht
    exact exact_childLink_firstCF_iff exec.memoryForest exec.memoryForest_nonempty
      MemoryTable.childLinkMem hi ht
  · exact fun h => h.2.2.1

/-- The cumulative predicate is exactly P3 acceptance plus the two literal traversal clauses. -/
theorem traversableChainedSemanticExactLanguage_iff
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} :
    TraversableChainedSemanticExactLanguage cfg exec ↔
      ChainedSemanticExactLanguage cfg exec ∧
        ComputeExactTraversalClause exec ∧ MemoryExactTraversalClause exec := by
  constructor
  · intro h
    exact ⟨h.chained, (computeExactTopology_iff_traversalClause exec).1 h.compute_topology,
      (memoryExactTopology_iff_traversalClause exec).1 h.memory_topology⟩
  · rintro ⟨hchain, hcomp, hmem⟩
    exact ⟨hchain, (computeExactTopology_iff_traversalClause exec).2 hcomp,
      (memoryExactTopology_iff_traversalClause exec).2 hmem⟩

theorem TraversableChainedSemanticExactLanguage.toChained
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : TraversableChainedSemanticExactLanguage cfg exec) :
    ChainedSemanticExactLanguage cfg exec :=
  h.chained

theorem TraversableChainedSemanticExactLanguage.toSemantic
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : TraversableChainedSemanticExactLanguage cfg exec) :
    SemanticExactLanguage cfg exec :=
  h.chained.semantic

/-! ## Paper-scoped component languages and literal RVT-product equivalences -/

/-- The paper's exact one-factor PUBLIC arity-3 compute RVT product.  Its tree labels contain no
`Dec`; each membership proof existentially supplies the aligned private Fcomp/RVT witness. -/
abbrev ComputePublicExactRVTProduct (K : Type) [Field K] :=
  Π _ : Fin 1,
    {t : NTree (ComputePublicLabel K) // ComputePublicExactTopology t}

/-- The exact `cfg.kMem`-factor arity-2 memory RVT product. -/
abbrev MemoryExactRVTProduct (cfg : ExactConfig F K) :=
  Π _ : Fin cfg.kMem,
    {t : NTree (MemoryTable.MState × MemoryTable.DTmem K) //
      RVTWithArity (MemoryTable.Fmem (K := K)) t}

/-- Canonical static indexing of the authoritative memory roots. -/
def ExactExecution.memoryTreeAt
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) (i : Fin cfg.kMem) :
    NTree (MemoryTable.MState × MemoryTable.DTmem K) :=
  exec.memoryForest.get (Fin.cast exec.memory_root_count.symm i)

theorem ExactExecution.memoryForest_eq_ofFn_memoryTreeAt
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.memoryForest = List.ofFn exec.memoryTreeAt := by
  apply List.ext_get
  · simp [exec.memory_root_count]
  · intro n hleft hright
    simp [ExactExecution.memoryTreeAt]

/-! ### D5 uniqueness from public BFS rows -/

/-- D5 uniqueness: nonempty forests with the same root count, public BFS labels, and
state-determined fanout are literally equal. -/
theorem exact_forest_eq_of_bfs_labels
    {LT : Type*} (fanout : LT → ℕ)
    {forest₁ forest₂ : List (NTree LT)}
    (hne₁ : forest₁ ≠ []) (hne₂ : forest₂ ≠ [])
    (hroots : forest₁.length = forest₂.length)
    (hbind₁ : ∀ t ∈ bfsForest forest₁, fanout t.label = t.children.length)
    (hbind₂ : ∀ t ∈ bfsForest forest₂, fanout t.label = t.children.length)
    (hrows :
      (bfsForest forest₁).map NTree.label =
        (bfsForest forest₂).map NTree.label) :
    forest₁ = forest₂ := by
  let W₁ := bfsForest forest₁
  let W₂ := bfsForest forest₂
  have hrowsW : W₁.map NTree.label = W₂.map NTree.label := by
    simpa [W₁, W₂] using hrows
  have hlen : W₁.length = W₂.length := by
    simpa using congrArg List.length hrowsW
  have hfo : foCol W₁ = foCol W₂ := by
    funext i
    unfold foCol
    cases h₁ : W₁[i - 1]? with
    | none =>
        have hg := congrArg (fun xs => xs[i - 1]?) hrowsW
        simp only [List.getElem?_map, h₁, Option.map_none] at hg
        cases h₂ : W₂[i - 1]? with
        | none => rfl
        | some t₂ => simp [h₂] at hg
    | some t₁ =>
        have hg := congrArg (fun xs => xs[i - 1]?) hrowsW
        simp only [List.getElem?_map, h₁, Option.map_some] at hg
        cases h₂ : W₂[i - 1]? with
        | none => simp [h₂] at hg
        | some t₂ =>
            simp only [h₂, Option.map_some, Option.some.injEq] at hg
            have hm₁ : t₁ ∈ W₁ :=
              List.mem_iff_getElem?.mpr ⟨i - 1, h₁⟩
            have hm₂ : t₂ ∈ W₂ :=
              List.mem_iff_getElem?.mpr ⟨i - 1, h₂⟩
            have hchildren : t₁.children.length = t₂.children.length := by
              calc
                t₁.children.length = fanout t₁.label :=
                  (hbind₁ t₁ (by simpa [W₁] using hm₁)).symm
                _ = fanout t₂.label := congrArg fanout hg
                _ = t₂.children.length :=
                  hbind₂ t₂ (by simpa [W₂] using hm₂)
            simpa using hchildren
  let fallback := forest₁.get
    ⟨0, List.length_pos_of_ne_nil hne₁⟩ |>.label
  have hlabels :
      (fun i => (W₁[i - 1]?).map NTree.label |>.getD fallback) =
        (fun i => (W₂[i - 1]?).map NTree.label |>.getD fallback) := by
    funext i
    have hg := congrArg (fun xs => xs[i - 1]?) hrowsW
    simp only [List.getElem?_map] at hg
    exact congrArg (fun x => x.getD fallback) hg
  have hr₁ := exact_reconForest_bfsForest forest₁ hne₁ fallback
  have hr₂ := exact_reconForest_bfsForest forest₂ hne₂ fallback
  calc
    forest₁ =
        reconForest forest₁.length (foCol W₁)
          (fun i => (W₁[i - 1]?).map NTree.label |>.getD fallback) W₁.length :=
      hr₁.symm
    _ = reconForest forest₂.length (foCol W₂)
          (fun i => (W₂[i - 1]?).map NTree.label |>.getD fallback) W₂.length := by
      rw [hroots, hfo, hlen, hlabels]
    _ = forest₂ := hr₂

theorem ComputePublicExactTopology.fanout_binding
    {publicTree : NTree (ComputePublicLabel K)}
    (h : ComputePublicExactTopology publicTree) :
    ∀ t ∈ bfsForest [publicTree],
      ComputeTable.fanoutComp t.label.1 = t.children.length := by
  obtain ⟨witnessTree, halign, hrvt⟩ := h
  subst publicTree
  intro t ht
  rw [show [mapNTree computePublicLabel witnessTree] =
      [witnessTree].map (mapNTree computePublicLabel) by rfl,
    bfsForest_mapNTree, List.mem_map] at ht
  obtain ⟨privateTree, hprivate, rfl⟩ := ht
  have hin : InTree witnessTree privateTree := by
    rw [mem_bfsForest] at hprivate
    obtain ⟨root, hroot, hin⟩ := hprivate
    simp only [List.mem_singleton] at hroot
    subst root
    exact hin
  have hfanout :=
    fanout_eq_children_length_of_properArity
      (ComputeTable.comp_stateSep (K := K)) hrvt.1 hrvt.2 privateTree hin
  change ComputeTable.fanoutComp privateTree.label.1 = privateTree.children.length at hfanout
  simpa [computePublicLabel] using hfanout

theorem MemoryExactTopology.fanout_binding
    {forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))}
    (h : ∀ t ∈ forest, RVTWithArity (MemoryTable.Fmem (K := K)) t) :
    ∀ t ∈ bfsForest forest,
      MemoryTable.fanoutMem t.label.1 = t.children.length := by
  intro t ht
  rw [mem_bfsForest] at ht
  obtain ⟨root, hroot, hin⟩ := ht
  exact fanout_eq_children_length_of_properArity
    (MemoryTable.mem_stateSep (K := K)) (h root hroot).1 (h root hroot).2 t hin

/-! ### Independently accepted public row languages -/

/-- Verifier-free compute traversal relation: exact state fanout occupancy and child-content
linking, with no `Vcomp` or state/public equality conjunct. -/
def ComputeTreeStructure
    (lbl : ComputeTable.State × ComputeTable.DTcomp K)
    (xout : Fin 3 → Option (ComputeTable.State × ComputeTable.DTcomp K)) : Prop :=
  (∀ i : Fin 3, (i : ℕ) < ComputeTable.fanoutComp lbl.1 ↔ xout i ≠ none) ∧
    ComputeTable.childLinkComp lbl xout

/-- Verifier-free memory traversal relation: exact state fanout occupancy and child-content
linking, with no `Vmem` or state/public equality conjunct. -/
def MemoryTreeStructure
    (lbl : MemoryTable.MState × MemoryTable.DTmem K)
    (xout : Fin 2 → Option (MemoryTable.MState × MemoryTable.DTmem K)) : Prop :=
  (∀ i : Fin 2, (i : ℕ) < MemoryTable.fanoutMem lbl.1 ↔ xout i ≠ none) ∧
    MemoryTable.childLinkMem lbl xout

/-- Direct fixed-production acceptance of one public compute row against its private `Dec`. -/
def ComputePublicRowAccepted
    (row : ComputePublicLabel K) (dec : ComputeTable.Dec K) : Prop :=
  row.1 = row.2.2.state ∧ ComputeTable.Vcomp row.2.1 row.2.2 dec

/-- Direct fixed-production acceptance of one public memory row. -/
def MemoryPublicRowAccepted
    (row : MemoryTable.MState × MemoryTable.DTmem K) : Prop :=
  row.1 = row.2.2.st ∧ MemoryTable.Vmem row.2.1 row.2.2

/-- Nodewise splitting of the production compute relation into its independently checked row
verifier and verifier-free structure. -/
theorem fcomp_iff_rowAccepted_and_structure
    (lbl : ComputeTable.State × ComputeTable.DTcomp K)
    (xout : Fin 3 → Option (ComputeTable.State × ComputeTable.DTcomp K)) :
    ComputeTable.Fcomp lbl xout ↔
      ComputePublicRowAccepted (computePublicLabel lbl) (computeWitnessDec lbl) ∧
        ComputeTreeStructure lbl xout := by
  constructor
  · intro h
    exact ⟨⟨h.1.symm, h.2.1⟩, h.2.2⟩
  · rintro ⟨hrow, hstruct⟩
    exact ⟨hrow.1.symm, hrow.2, hstruct⟩

/-- Nodewise splitting of the production memory relation into row verification and structure. -/
theorem fmem_iff_rowAccepted_and_structure
    (lbl : MemoryTable.MState × MemoryTable.DTmem K)
    (xout : Fin 2 → Option (MemoryTable.MState × MemoryTable.DTmem K)) :
    MemoryTable.Fmem lbl xout ↔
      MemoryPublicRowAccepted lbl ∧ MemoryTreeStructure lbl xout := by
  constructor
  · intro h
    exact ⟨⟨h.1.symm, h.2.1⟩, h.2.2⟩
  · rintro ⟨hrow, hstruct⟩
    exact ⟨hrow.1.symm, hrow.2, hstruct⟩

/-- A verifier-free compute-structure tree aligned to the exact public and Dec BFS rows. -/
abbrev ComputePublicRowsTreeWitness
    (rows : List (ComputePublicLabel K))
    (decs : List (ComputeTable.Dec K)) :=
  {t : NTree (ComputeTable.State × ComputeTable.DTcomp K) //
    (bfsForest [t]).map (fun node => computePublicLabel node.label) = rows ∧
      (bfsForest [t]).map (fun node => computeWitnessDec node.label) = decs ∧
      RVTWithArity (ComputeTreeStructure (K := K)) t ∧
      (∀ node ∈ bfsForest [t],
        ComputeTable.fanoutComp node.label.1 = node.children.length)}

/-- A verifier-free memory-structure forest witnessing one exact ordered public row list. -/
abbrev MemoryPublicRowsForestWitness
    (cfg : ExactConfig F K)
    (rows : List (MemoryTable.MState × MemoryTable.DTmem K)) :=
  {forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K)) //
    forest.length = cfg.kMem ∧ forest ≠ [] ∧
      (∀ t ∈ forest, RVTWithArity (MemoryTreeStructure (K := K)) t) ∧
      (∀ node ∈ bfsForest forest,
        MemoryTable.fanoutMem node.label.1 = node.children.length) ∧
      (bfsForest forest).map NTree.label = rows}

/-- Proof-only compute witness bundle.  The `Dec` list and structural tree are not source data. -/
abbrev ComputePublicRowsAcceptedWitness (rows : List (ComputePublicLabel K)) :=
  {decs : List (ComputeTable.Dec K) //
    decs.length = rows.length ∧
      List.Forall₂ ComputePublicRowAccepted rows decs ∧
      Nonempty (ComputePublicRowsTreeWitness rows decs)}

/-- Independently accepted PUBLIC compute statements.  The data are only ordered
`State × (Inputs × Pub)` rows.  Acceptance separately requires an exact one-root BFS/topology
witness and an existential aligned `Dec` list satisfying the fixed production `Vcomp` row fold. -/
def ComputePublicRowsAccepted (rows : List (ComputePublicLabel K)) : Prop :=
  Nonempty (ComputePublicRowsAcceptedWitness rows)

/-- Independently accepted PUBLIC memory statements.  The data are only ordered public memory
rows.  Acceptance requires the exact nonempty `cfg.kMem`-root BFS topology and the fixed production
`Vmem` row fold. -/
def MemoryPublicRowsAccepted
    (cfg : ExactConfig F K)
    (rows : List (MemoryTable.MState × MemoryTable.DTmem K)) : Prop :=
  Nonempty (MemoryPublicRowsForestWitness cfg rows) ∧
    rows.Forall MemoryPublicRowAccepted

abbrev ComputePublicAcceptedLanguage (K : Type) [Field K] :=
  {rows : List (ComputePublicLabel K) // ComputePublicRowsAccepted rows}

abbrev MemoryPublicAcceptedLanguage (cfg : ExactConfig F K) :=
  {rows : List (MemoryTable.MState × MemoryTable.DTmem K) //
    MemoryPublicRowsAccepted cfg rows}

private theorem forall₂_map_pair_iff
    {α β γ : Type*} (R : β → γ → Prop) (f : α → β) (g : α → γ) :
    ∀ xs : List α,
      List.Forall₂ R (xs.map f) (xs.map g) ↔ ∀ x ∈ xs, R (f x) (g x) := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- Node-by-node assembly: fixed `Vcomp` rows plus verifier-free structural RVT are exactly
production `Fcomp` RVT. -/
theorem rvt_fcomp_iff_structure_and_rows
    (tree : NTree (ComputeTable.State × ComputeTable.DTcomp K)) :
    RVT (ComputeTable.Fcomp (K := K)) tree ↔
      RVT (ComputeTreeStructure (K := K)) tree ∧
        ∀ node ∈ bfsForest [tree],
          ComputePublicRowAccepted
            (computePublicLabel node.label) (computeWitnessDec node.label) := by
  constructor
  · intro hrvt
    have hallF :=
      (RVT_iff_forall_InTree (ComputeTable.Fcomp (K := K)) tree).1 hrvt
    refine ⟨(RVT_iff_forall_InTree (ComputeTreeStructure (K := K)) tree).2 ?_, ?_⟩
    · intro node hin
      have hFcon := hallF node hin
      have hsplit :=
        (fcomp_iff_rowAccepted_and_structure node.label
          (fun i => node.childLabel i)).1 hFcon.1
      refine ⟨hsplit.2, ?_⟩
      constructor
      · intro hleaf
        exact ((fcomp_iff_rowAccepted_and_structure node.label (fun _ => none)).1
          (hFcon.2.mp hleaf)).2
      · intro hstruct
        exact hFcon.2.mpr
          ((fcomp_iff_rowAccepted_and_structure node.label (fun _ => none)).2
            ⟨hsplit.1, hstruct⟩)
    · intro node hnode
      rw [mem_bfsForest] at hnode
      obtain ⟨root, hroot, hin⟩ := hnode
      simp only [List.mem_singleton] at hroot
      subst root
      exact ((fcomp_iff_rowAccepted_and_structure node.label
        (fun i => node.childLabel i)).1 (hallF node hin).1).1
  · rintro ⟨hstruct, hrows⟩
    have hallS :=
      (RVT_iff_forall_InTree (ComputeTreeStructure (K := K)) tree).1 hstruct
    apply (RVT_iff_forall_InTree (ComputeTable.Fcomp (K := K)) tree).2
    intro node hin
    have hnode : node ∈ bfsForest [tree] := by
      rw [mem_bfsForest]
      exact ⟨tree, by simp, hin⟩
    have hrow := hrows node hnode
    have hScon := hallS node hin
    refine ⟨(fcomp_iff_rowAccepted_and_structure node.label
      (fun i => node.childLabel i)).2 ⟨hrow, hScon.1⟩, ?_⟩
    constructor
    · intro hleaf
      exact ((fcomp_iff_rowAccepted_and_structure node.label (fun _ => none)).2
        ⟨hrow, hScon.2.mp hleaf⟩)
    · intro hFnone
      exact hScon.2.mpr
        ((fcomp_iff_rowAccepted_and_structure node.label (fun _ => none)).1 hFnone).2

theorem rvt_fmem_iff_structure_and_rows
    (tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)) :
    RVT (MemoryTable.Fmem (K := K)) tree ↔
      RVT (MemoryTreeStructure (K := K)) tree ∧
        ∀ node ∈ bfsForest [tree], MemoryPublicRowAccepted node.label := by
  constructor
  · intro hrvt
    have hallF :=
      (RVT_iff_forall_InTree (MemoryTable.Fmem (K := K)) tree).1 hrvt
    refine ⟨(RVT_iff_forall_InTree (MemoryTreeStructure (K := K)) tree).2 ?_, ?_⟩
    · intro node hin
      have hFcon := hallF node hin
      have hsplit :=
        (fmem_iff_rowAccepted_and_structure node.label
          (fun i => node.childLabel i)).1 hFcon.1
      refine ⟨hsplit.2, ?_⟩
      constructor
      · intro hleaf
        exact ((fmem_iff_rowAccepted_and_structure node.label (fun _ => none)).1
          (hFcon.2.mp hleaf)).2
      · intro hstruct
        exact hFcon.2.mpr
          ((fmem_iff_rowAccepted_and_structure node.label (fun _ => none)).2
            ⟨hsplit.1, hstruct⟩)
    · intro node hnode
      rw [mem_bfsForest] at hnode
      obtain ⟨root, hroot, hin⟩ := hnode
      simp only [List.mem_singleton] at hroot
      subst root
      exact ((fmem_iff_rowAccepted_and_structure node.label
        (fun i => node.childLabel i)).1 (hallF node hin).1).1
  · rintro ⟨hstruct, hrows⟩
    have hallS :=
      (RVT_iff_forall_InTree (MemoryTreeStructure (K := K)) tree).1 hstruct
    apply (RVT_iff_forall_InTree (MemoryTable.Fmem (K := K)) tree).2
    intro node hin
    have hnode : node ∈ bfsForest [tree] := by
      rw [mem_bfsForest]
      exact ⟨tree, by simp, hin⟩
    have hrow := hrows node hnode
    have hScon := hallS node hin
    refine ⟨(fmem_iff_rowAccepted_and_structure node.label
      (fun i => node.childLabel i)).2 ⟨hrow, hScon.1⟩, ?_⟩
    constructor
    · intro hleaf
      exact ((fmem_iff_rowAccepted_and_structure node.label (fun _ => none)).2
        ⟨hrow, hScon.2.mp hleaf⟩)
    · intro hFnone
      exact hScon.2.mpr
        ((fmem_iff_rowAccepted_and_structure node.label (fun _ => none)).1 hFnone).2

theorem ComputePublicExactTopology.rowsAccepted
    {publicTree : NTree (ComputePublicLabel K)}
    (h : ComputePublicExactTopology publicTree) :
    ∃ decs : List (ComputeTable.Dec K),
      decs.length = ((bfsForest [publicTree]).map NTree.label).length ∧
        List.Forall₂ ComputePublicRowAccepted
          ((bfsForest [publicTree]).map NTree.label) decs := by
  obtain ⟨witnessTree, halign, hrvt⟩ := h
  subst publicTree
  let nodes := bfsForest [witnessTree]
  have haccepted :
      ∀ t ∈ nodes,
        ComputePublicRowAccepted
          (computePublicLabel t.label) (computeWitnessDec t.label) := by
    intro t ht
    have hin : InTree witnessTree t := by
      rw [mem_bfsForest] at ht
      obtain ⟨root, hroot, hin⟩ := ht
      simp only [List.mem_singleton] at hroot
      subst root
      exact hin
    have hF :=
      ((RVT_iff_forall_InTree (ComputeTable.Fcomp (K := K)) witnessTree).1 hrvt.1
        t hin).1
    exact ⟨hF.1.symm, hF.2.1⟩
  have hforallAux :
      ∀ xs : List (NTree (ComputeTable.State × ComputeTable.DTcomp K)),
        (∀ t ∈ xs,
          ComputePublicRowAccepted
            (computePublicLabel t.label) (computeWitnessDec t.label)) →
        List.Forall₂ ComputePublicRowAccepted
          (xs.map (fun t => computePublicLabel t.label))
          (xs.map (fun t => computeWitnessDec t.label)) := by
    intro xs hall
    induction xs with
    | nil => exact List.Forall₂.nil
    | cons t ts ih =>
        exact List.Forall₂.cons (hall t (by simp))
          (ih (fun s hs => hall s (by simp [hs])))
  have hforall :
      List.Forall₂ ComputePublicRowAccepted
        (nodes.map (fun t => computePublicLabel t.label))
        (nodes.map (fun t => computeWitnessDec t.label)) :=
    hforallAux nodes haccepted
  have hpublic :
      (bfsForest [mapNTree computePublicLabel witnessTree]).map NTree.label =
        nodes.map (fun t => computePublicLabel t.label) := by
    rw [show [mapNTree computePublicLabel witnessTree] =
      [witnessTree].map (mapNTree computePublicLabel) by rfl,
      bfsForest_mapNTree]
    simp [nodes, List.map_map, Function.comp_def]
  refine ⟨nodes.map (fun t => computeWitnessDec t.label), ?_, ?_⟩
  · rw [hpublic]
    simp
  · rw [hpublic]
    exact hforall

theorem MemoryExactTopology.rowsAccepted
    {forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))}
    (h : ∀ t ∈ forest, RVTWithArity (MemoryTable.Fmem (K := K)) t) :
    ((bfsForest forest).map NTree.label).Forall MemoryPublicRowAccepted := by
  rw [List.forall_iff_forall_mem]
  intro row hrow
  rw [List.mem_map] at hrow
  obtain ⟨t, ht, rfl⟩ := hrow
  rw [mem_bfsForest] at ht
  obtain ⟨root, hroot, hin⟩ := ht
  have hF :=
    ((RVT_iff_forall_InTree (MemoryTable.Fmem (K := K)) root).1
      (h root hroot).1 t hin).1
  exact ⟨hF.1.symm, hF.2.1⟩

/-- The proof-chosen Dec/fold/structure bundle. -/
noncomputable def ComputePublicAcceptedLanguage.acceptedWitness
    (x : ComputePublicAcceptedLanguage K) :
    ComputePublicRowsAcceptedWitness x.1 :=
  Classical.choice x.2

/-- The proof-chosen verifier-free private structure tree. -/
noncomputable def ComputePublicAcceptedLanguage.treeWitness
    (x : ComputePublicAcceptedLanguage K) :
    ComputePublicRowsTreeWitness x.1 x.acceptedWitness.1 :=
  Classical.choice x.acceptedWitness.2.2.2

/-- The proof-chosen public memory forest.  D5 uniqueness below makes this choice canonical. -/
noncomputable def MemoryPublicAcceptedLanguage.forestWitness
    {cfg : ExactConfig F K} (x : MemoryPublicAcceptedLanguage cfg) :
    MemoryPublicRowsForestWitness cfg x.1 :=
  Classical.choice x.2.1

/-- Forward reconstruction of the one public compute tree from accepted public rows. -/
noncomputable def computePublicToRVTProduct
    (x : ComputePublicAcceptedLanguage K) :
    ComputePublicExactRVTProduct K := by
  let privateTree := x.treeWitness.1
  have hfold :
      List.Forall₂ ComputePublicRowAccepted
        ((bfsForest [privateTree]).map (fun node => computePublicLabel node.label))
        ((bfsForest [privateTree]).map (fun node => computeWitnessDec node.label)) := by
    rw [x.treeWitness.2.1, x.treeWitness.2.2.1]
    exact x.acceptedWitness.2.2.1
  have hall :
      ∀ node ∈ bfsForest [privateTree],
        ComputePublicRowAccepted
          (computePublicLabel node.label) (computeWitnessDec node.label) :=
    (forall₂_map_pair_iff ComputePublicRowAccepted
      (fun node : NTree (ComputeTable.State × ComputeTable.DTcomp K) =>
        computePublicLabel node.label)
      (fun node => computeWitnessDec node.label)
      (bfsForest [privateTree])).1 hfold
  have hrvt :
      RVTWithArity (ComputeTable.Fcomp (K := K)) privateTree :=
    ⟨(rvt_fcomp_iff_structure_and_rows privateTree).2
      ⟨x.treeWitness.2.2.2.1.1, hall⟩,
      x.treeWitness.2.2.2.1.2⟩
  exact fun _ =>
    ⟨mapNTree computePublicLabel privateTree, ⟨privateTree, rfl, hrvt⟩⟩

/-- Public BFS readout of a one-factor compute RVT product. -/
noncomputable def computePublicOfRVTProduct
    (x : ComputePublicExactRVTProduct K) :
    ComputePublicAcceptedLanguage K := by
  let t := x ⟨0, by omega⟩
  let privateWitness := t.2.privateWitness
  let privateTree := privateWitness.1
  have halign : ComputeTreeWitnessAligned t.1 privateTree := privateWitness.2.1
  have hrvt : RVTWithArity (ComputeTable.Fcomp (K := K)) privateTree :=
    privateWitness.2.2
  let nodes := bfsForest [privateTree]
  let rows := nodes.map (fun node => computePublicLabel node.label)
  let decs := nodes.map (fun node => computeWitnessDec node.label)
  have hsplit := (rvt_fcomp_iff_structure_and_rows privateTree).1 hrvt.1
  have hfold :
      List.Forall₂ ComputePublicRowAccepted rows decs :=
    (forall₂_map_pair_iff ComputePublicRowAccepted
      (fun node : NTree (ComputeTable.State × ComputeTable.DTcomp K) =>
        computePublicLabel node.label)
      (fun node => computeWitnessDec node.label) nodes).2 hsplit.2
  have hpublic :
      (bfsForest [t.1]).map NTree.label = rows := by
    rw [halign]
    rw [show [mapNTree computePublicLabel privateTree] =
      [privateTree].map (mapNTree computePublicLabel) by rfl,
      bfsForest_mapNTree]
    simp [rows, nodes, List.map_map, Function.comp_def]
  have hfanout :
      ∀ node ∈ nodes,
        ComputeTable.fanoutComp node.label.1 = node.children.length := by
    intro node hnode
    rw [mem_bfsForest] at hnode
    obtain ⟨root, hroot, hin⟩ := hnode
    simp only [List.mem_singleton] at hroot
    subst root
    have hf := fanout_eq_children_length_of_properArity
      (ComputeTable.comp_stateSep (K := K)) hrvt.1 hrvt.2 node hin
    change ComputeTable.fanoutComp node.label.1 = node.children.length at hf
    exact hf
  refine ⟨(bfsForest [t.1]).map NTree.label, ?_⟩
  refine ⟨decs, by simp [decs, rows, hpublic], ?_, ?_⟩
  · rw [hpublic]
    exact hfold
  · exact ⟨⟨privateTree, by simpa [rows] using hpublic.symm,
      rfl, ⟨hsplit.1, hrvt.2⟩, by simpa [nodes] using hfanout⟩⟩

theorem computePublicToOfRVTProduct
    (x : ComputePublicAcceptedLanguage K) :
    computePublicOfRVTProduct (computePublicToRVTProduct x) = x := by
  apply Subtype.ext
  change (bfsForest [(computePublicToRVTProduct x ⟨0, by omega⟩).1]).map
      NTree.label = x.1
  change (bfsForest [mapNTree computePublicLabel x.treeWitness.1]).map
      NTree.label = x.1
  rw [show [mapNTree computePublicLabel x.treeWitness.1] =
    [x.treeWitness.1].map (mapNTree computePublicLabel) by rfl,
    bfsForest_mapNTree]
  simpa [List.map_map, Function.comp_def] using x.treeWitness.2.1

theorem computePublicOfToRVTProduct
    (x : ComputePublicExactRVTProduct K) :
    computePublicToRVTProduct (computePublicOfRVTProduct x) = x := by
  funext i
  fin_cases i
  apply Subtype.ext
  let y := computePublicOfRVTProduct x
  have hrows :
      (bfsForest [mapNTree computePublicLabel y.treeWitness.1]).map NTree.label =
        (bfsForest [(x ⟨0, by omega⟩).1]).map NTree.label := by
    rw [show [mapNTree computePublicLabel y.treeWitness.1] =
      [y.treeWitness.1].map (mapNTree computePublicLabel) by rfl,
      bfsForest_mapNTree]
    simpa [List.map_map, Function.comp_def, y, computePublicOfRVTProduct] using
      y.treeWitness.2.1
  have hforest := exact_forest_eq_of_bfs_labels
    (fun lbl : ComputePublicLabel K => ComputeTable.fanoutComp lbl.1)
    (forest₁ := [mapNTree computePublicLabel y.treeWitness.1])
    (forest₂ := [(x ⟨0, by omega⟩).1])
    (by simp) (by simp) rfl
    (computePublicToRVTProduct y ⟨0, by omega⟩).2.fanout_binding
    (x ⟨0, by omega⟩).2.fanout_binding hrows
  simpa [computePublicToRVTProduct, y] using hforest

/-- Literal one-root compute component bijection (`Def:traversable`). -/
noncomputable def computePublicTraversalEquiv (K : Type) [Field K] :
    ComputePublicAcceptedLanguage K ≃ ComputePublicExactRVTProduct K where
  toFun := computePublicToRVTProduct
  invFun := computePublicOfRVTProduct
  left_inv := computePublicToOfRVTProduct
  right_inv := computePublicOfToRVTProduct

/-- Forward ordered-root reconstruction from accepted public memory rows. -/
noncomputable def memoryPublicToRVTProduct
    {cfg : ExactConfig F K} (x : MemoryPublicAcceptedLanguage cfg) :
    MemoryExactRVTProduct cfg := by
  let forest := x.forestWitness.1
  have hall :
      ∀ node ∈ bfsForest forest, MemoryPublicRowAccepted node.label := by
    intro node hnode
    have hlabel : node.label ∈ (bfsForest forest).map NTree.label :=
      List.mem_map.mpr ⟨node, hnode, rfl⟩
    rw [x.forestWitness.2.2.2.2.2] at hlabel
    exact (List.forall_iff_forall_mem.mp x.2.2) node.label hlabel
  exact fun i => by
    let tree := forest.get (Fin.cast x.forestWitness.2.1.symm i)
    have htree : tree ∈ forest :=
      List.get_mem _ (Fin.cast x.forestWitness.2.1.symm i)
    have hrows :
        ∀ node ∈ bfsForest [tree], MemoryPublicRowAccepted node.label := by
      intro node hnode
      rw [mem_bfsForest] at hnode
      obtain ⟨root, hroot, hin⟩ := hnode
      simp only [List.mem_singleton] at hroot
      subst root
      apply hall node
      rw [mem_bfsForest]
      exact ⟨tree, htree, hin⟩
    exact ⟨tree,
      ⟨(rvt_fmem_iff_structure_and_rows tree).2
        ⟨(x.forestWitness.2.2.2.1 tree htree).1, hrows⟩,
        (x.forestWitness.2.2.2.1 tree htree).2⟩⟩

/-- Aggregate BFS readout of an ordered memory RVT product. -/
noncomputable def memoryPublicOfRVTProduct
    (cfg : ExactConfig F K) (hk : 0 < cfg.kMem)
    (x : MemoryExactRVTProduct cfg) :
    MemoryPublicAcceptedLanguage cfg := by
  let forest := List.ofFn (fun i => (x i).1)
  let rows := (bfsForest forest).map NTree.label
  have hlength : forest.length = cfg.kMem := by simp [forest]
  have hnonempty : forest ≠ [] :=
    List.ne_nil_of_length_pos (by simpa [hlength] using hk)
  have htopology :
      ∀ t ∈ forest, RVTWithArity (MemoryTable.Fmem (K := K)) t := by
    intro t ht
    dsimp [forest] at ht
    rw [List.mem_ofFn'] at ht
    obtain ⟨i, rfl⟩ := ht
    exact (x i).2
  have hstructure :
      ∀ t ∈ forest, RVTWithArity (MemoryTreeStructure (K := K)) t := by
    intro t ht
    have hfull := htopology t ht
    exact ⟨(rvt_fmem_iff_structure_and_rows t).1 hfull.1 |>.1, hfull.2⟩
  have hfanout :
      ∀ node ∈ bfsForest forest,
        MemoryTable.fanoutMem node.label.1 = node.children.length :=
    MemoryExactTopology.fanout_binding htopology
  exact
    ⟨rows, ⟨⟨⟨forest, hlength, hnonempty, hstructure, hfanout, rfl⟩⟩,
      MemoryExactTopology.rowsAccepted htopology⟩⟩

theorem memoryPublicToOfRVTProduct
    (cfg : ExactConfig F K) (hk : 0 < cfg.kMem)
    (x : MemoryPublicAcceptedLanguage cfg) :
    memoryPublicOfRVTProduct cfg hk (memoryPublicToRVTProduct x) = x := by
  apply Subtype.ext
  obtain ⟨hlength, hnonempty, hstructure, hfanout, hroweq⟩ :=
    x.forestWitness.2
  have hforest :
      List.ofFn (fun i => (memoryPublicToRVTProduct x i).1) =
        x.forestWitness.1 := by
    apply List.ext_get
    · simp [hlength]
    · intro n hleft hright
      simp [memoryPublicToRVTProduct]
  change (bfsForest (List.ofFn fun i => (memoryPublicToRVTProduct x i).1)).map
      NTree.label = x.1
  rw [hforest]
  exact hroweq

theorem memoryPublicOfToRVTProduct
    (cfg : ExactConfig F K) (hk : 0 < cfg.kMem)
    (x : MemoryExactRVTProduct cfg) :
    memoryPublicToRVTProduct (memoryPublicOfRVTProduct cfg hk x) = x := by
  funext i
  apply Subtype.ext
  let y := memoryPublicOfRVTProduct cfg hk x
  let originalForest := List.ofFn (fun i => (x i).1)
  let chosenForest := y.forestWitness.1
  obtain ⟨ychosenLength, ychosenNonempty, ychosenStructure,
    ychosenFanout, ychosenRows⟩ := y.forestWitness.2
  have hyrows :
      y.1 = (bfsForest originalForest).map NTree.label := by
    rfl
  have hrows :
      (bfsForest chosenForest).map NTree.label =
        (bfsForest originalForest).map NTree.label := by
    exact ychosenRows.trans hyrows
  have horiginalTopology :
      ∀ t ∈ originalForest, RVTWithArity (MemoryTable.Fmem (K := K)) t := by
    intro t ht
    dsimp [originalForest] at ht
    rw [List.mem_ofFn'] at ht
    obtain ⟨j, rfl⟩ := ht
    exact (x j).2
  have hforest := exact_forest_eq_of_bfs_labels
    (fun lbl : MemoryTable.MState × MemoryTable.DTmem K =>
      MemoryTable.fanoutMem lbl.1)
    (forest₁ := chosenForest) (forest₂ := originalForest)
    ychosenNonempty
    (List.ne_nil_of_length_pos (by simpa [originalForest] using hk))
    (by rw [ychosenLength]; simp [originalForest])
    ychosenFanout
    (MemoryExactTopology.fanout_binding horiginalTopology) hrows
  change y.forestWitness.1.get
    (Fin.cast ychosenLength.symm i) = (x i).1
  have hopt := congrArg (fun forest => forest[(i : ℕ)]?)
    (show y.forestWitness.1 = originalForest by simpa [chosenForest] using hforest)
  have hleft : (i : ℕ) < y.forestWitness.1.length := by
    simpa using (Fin.cast ychosenLength.symm i).isLt
  rw [List.getElem?_eq_getElem hleft] at hopt
  simp [originalForest] at hopt
  simpa [List.get_eq_getElem] using hopt

/-- Literal ordered memory component bijection (`Def:traversable`). -/
noncomputable def memoryPublicTraversalEquiv
    (cfg : ExactConfig F K) (hk : 0 < cfg.kMem) :
    MemoryPublicAcceptedLanguage cfg ≃ MemoryExactRVTProduct cfg where
  toFun := memoryPublicToRVTProduct
  invFun := memoryPublicOfRVTProduct cfg hk
  left_inv := memoryPublicToOfRVTProduct cfg hk
  right_inv := memoryPublicOfToRVTProduct cfg hk

/-- The two independent public component languages of packet-local `Def:traversable`. -/
abbrev PacketLocalPublicAcceptedLanguage (cfg : ExactConfig F K) :=
  ComputePublicAcceptedLanguage K × MemoryPublicAcceptedLanguage cfg

/-- The two independent RVT products of packet-local `Def:traversable`. -/
abbrev PacketLocalExactRVTProducts (cfg : ExactConfig F K) :=
  ComputePublicExactRVTProduct K × MemoryExactRVTProduct cfg

/-- Packet-local PAPER-SCOPED `Def:traversable` result.  This is the product of
the two component bijections.  Its source and target contain no `ExactExecution`, P3 chaining proof,
IO object, or private `Dec` statement data. -/
def packetLocalDefTraversableEquiv
    (cfg : ExactConfig F K) (hk : 0 < cfg.kMem) :
    PacketLocalPublicAcceptedLanguage cfg ≃ PacketLocalExactRVTProducts cfg where
  toFun x :=
    (computePublicTraversalEquiv K x.1, memoryPublicTraversalEquiv cfg hk x.2)
  invFun x :=
    ((computePublicTraversalEquiv K).symm x.1,
      (memoryPublicTraversalEquiv cfg hk).symm x.2)
  left_inv x := by
    simp
  right_inv x := by
    simp

/-- The paper-scoped `Def:traversable` claim for one exact configuration
.  The same `cfg` indexes both independently accepted public component
languages and both exact-arity RVT products.  `Nonempty` expresses existence of the required
bijections inside `Prop`; each witness is a genuine `Equiv`, so both inverse laws are part of its
type. -/
structure DefTraversableRealization (cfg : ExactConfig F K) : Prop where
  /-- `φ_comp`: complete accepted public compute rows are bijective with the one-factor arity-3
  `Fcomp` RVT product. -/
  compute :
    Nonempty (ComputePublicAcceptedLanguage K ≃ ComputePublicExactRVTProduct K)
  /-- `φ_mem`: complete accepted public memory rows are bijective with the `cfg.kMem`-factor
  arity-2 `Fmem` RVT product. -/
  memory :
    Nonempty (MemoryPublicAcceptedLanguage cfg ≃ MemoryExactRVTProduct cfg)
  /-- The two component bijections on the same configuration, paired exactly as the final sentence
  of `Def:traversable`. -/
  paired :
    Nonempty (PacketLocalPublicAcceptedLanguage cfg ≃ PacketLocalExactRVTProducts cfg)

/-- Positive memory-root count is the only necessary side condition for the literal memory
bijection; the zero-root impossibility is proved below. -/
theorem defTraversableRealization (cfg : ExactConfig F K) (hk : 0 < cfg.kMem) :
    DefTraversableRealization cfg :=
  ⟨⟨computePublicTraversalEquiv K⟩, ⟨memoryPublicTraversalEquiv cfg hk⟩,
    ⟨packetLocalDefTraversableEquiv cfg hk⟩⟩

/-- Universal exact `Def:traversable` proposition used by the Layer-1 Nock capstone.  It quantifies
over the complete exact configuration rather than a free legacy `TraversalModel`. -/
abbrev ExactDefTraversable (F K : Type) [Field F] [Field K] [Algebra F K] : Prop :=
  ∀ cfg : ExactConfig F K, 0 < cfg.kMem → DefTraversableRealization cfg

/-- Every positive-root exact Nock configuration has the two paper-scoped component bijections. -/
theorem exactDefTraversable (F K : Type) [Field F] [Field K] [Algebra F K] :
    ExactDefTraversable F K :=
  defTraversableRealization

/-! ## Bridge from the cumulative exact package to the independent component languages -/

/-- A cumulative P3/P6 execution projects to one public compute statement.  This is a projection,
not the source of the paper component bijection. -/
def TraversableChainedSemanticExactLanguage.computePublicAccepted
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : TraversableChainedSemanticExactLanguage cfg exec) :
    ComputePublicAcceptedLanguage K := by
  let htop := exec.computePublicExactTopology h.compute_topology
  have hsplit :=
    (rvt_fcomp_iff_structure_and_rows exec.computeTree).1 h.compute_topology.1
  have hfanout :
      ∀ node ∈ bfsForest [exec.computeTree],
        ComputeTable.fanoutComp node.label.1 = node.children.length := by
    intro node hnode
    rw [mem_bfsForest] at hnode
    obtain ⟨root, hroot, hin⟩ := hnode
    simp only [List.mem_singleton] at hroot
    subst root
    have hf := fanout_eq_children_length_of_properArity
      (ComputeTable.comp_stateSep (K := K))
      h.compute_topology.1 h.compute_topology.2 node hin
    change ComputeTable.fanoutComp node.label.1 = node.children.length at hf
    exact hf
  refine ⟨exec.computePublicRows, ?_⟩
  have hfold :
      List.Forall₂ ComputePublicRowAccepted
        exec.computePublicRows exec.computeDecRows := by
    have hfold' := (forall₂_map_pair_iff ComputePublicRowAccepted
      (fun node : NTree (ComputeTable.State × ComputeTable.DTcomp K) =>
        computePublicLabel node.label)
      (fun node => computeWitnessDec node.label)
      (bfsForest [exec.computeTree])).2 hsplit.2
    simpa [ExactExecution.computePublicRows, ExactExecution.computeDecRows,
      ExactExecution.computeRows, List.map_map, Function.comp_def] using hfold'
  refine ⟨exec.computeDecRows, by simp, hfold, ?_⟩
  refine ⟨⟨exec.computeTree, ?_, ?_,
    ⟨hsplit.1, h.compute_topology.2⟩, hfanout⟩⟩
  · simp [ExactExecution.computePublicRows, ExactExecution.computeRows,
      List.map_map, Function.comp_def]
  · simp [ExactExecution.computeDecRows, ExactExecution.computeRows,
      List.map_map, Function.comp_def]

/-- A cumulative P3/P6 execution projects to its ordered public memory forest. -/
def TraversableChainedSemanticExactLanguage.memoryPublicAccepted
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : TraversableChainedSemanticExactLanguage cfg exec) :
    MemoryPublicAcceptedLanguage cfg := by
  have hstructure :
      ∀ t ∈ exec.memoryForest,
        RVTWithArity (MemoryTreeStructure (K := K)) t := by
    intro t ht
    have hfull := h.memory_topology t ht
    exact ⟨(rvt_fmem_iff_structure_and_rows t).1 hfull.1 |>.1, hfull.2⟩
  have hfanout := MemoryExactTopology.fanout_binding h.memory_topology
  refine ⟨exec.memoryRows, ?_⟩
  refine ⟨⟨⟨exec.memoryForest, exec.memory_root_count, exec.memoryForest_nonempty,
    hstructure, hfanout, rfl⟩⟩, ?_⟩
  exact MemoryExactTopology.rowsAccepted h.memory_topology

/-- Paired projection from the full exact package to the two independent paper component
languages. -/
def TraversableChainedSemanticExactLanguage.publicAcceptedComponents
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : TraversableChainedSemanticExactLanguage cfg exec) :
    PacketLocalPublicAcceptedLanguage cfg :=
  (h.computePublicAccepted, h.memoryPublicAccepted)

theorem computePublicTraversalEquiv_left_inverse
    (x : ComputePublicAcceptedLanguage K) :
    (computePublicTraversalEquiv K).symm (computePublicTraversalEquiv K x) = x :=
  (computePublicTraversalEquiv K).left_inv x

theorem computePublicTraversalEquiv_right_inverse
    (x : ComputePublicExactRVTProduct K) :
    computePublicTraversalEquiv K ((computePublicTraversalEquiv K).symm x) = x :=
  (computePublicTraversalEquiv K).right_inv x

theorem memoryPublicTraversalEquiv_left_inverse
    (cfg : ExactConfig F K) (hk : 0 < cfg.kMem)
    (x : MemoryPublicAcceptedLanguage cfg) :
    (memoryPublicTraversalEquiv cfg hk).symm
        (memoryPublicTraversalEquiv cfg hk x) = x :=
  (memoryPublicTraversalEquiv cfg hk).left_inv x

theorem memoryPublicTraversalEquiv_right_inverse
    (cfg : ExactConfig F K) (hk : 0 < cfg.kMem)
    (x : MemoryExactRVTProduct cfg) :
    memoryPublicTraversalEquiv cfg hk
        ((memoryPublicTraversalEquiv cfg hk).symm x) = x :=
  (memoryPublicTraversalEquiv cfg hk).right_inv x

/-! ## Negative regressions -/

/-- Empty accepted row lists cannot inhabit the cumulative exact language. -/
theorem traversable_exact_empty_rows_impossible
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (_h : TraversableChainedSemanticExactLanguage cfg exec) :
    exec.computeRows ≠ [] ∧ exec.memoryRows ≠ [] :=
  ⟨exec.computeRows_nonempty, exec.memoryRows_nonempty⟩

/-- A compute-root count different from one cannot describe this exact carrier. -/
theorem traversable_exact_wrong_compute_root_count
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (_h : TraversableChainedSemanticExactLanguage cfg exec)
    {roots : ℕ} (hwrong : roots ≠ 1) :
    [exec.computeTree].length ≠ roots := by
  simpa using hwrong.symm

/-- A memory-root count different from `cfg.kMem` cannot describe this exact carrier. -/
theorem traversable_exact_wrong_memory_root_count
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (_h : TraversableChainedSemanticExactLanguage cfg exec)
    {roots : ℕ} (hwrong : roots ≠ cfg.kMem) :
    exec.memoryForest.length ≠ roots := by
  intro h
  apply hwrong
  exact h.symm.trans exec.memory_root_count

/-- Different private Dec-bearing witnesses of one public tree produce the same public statement:
the witness is existential proof data, not part of statement identity. -/
theorem computePublicAccepted_eq_of_private_witnesses
    (rows : List (ComputePublicLabel K))
    (witness₁ witness₂ : ComputePublicRowsAcceptedWitness rows) :
    (⟨rows, ⟨witness₁⟩⟩ : ComputePublicAcceptedLanguage K) =
      (⟨rows, ⟨witness₂⟩⟩ : ComputePublicAcceptedLanguage K) := by
  apply Subtype.ext
  rfl

/-- At `kMem = 0`, nonemptiness makes the public memory language empty. -/
theorem memoryPublicAcceptedLanguage_isEmpty_of_kMem_eq_zero
    (cfg : ExactConfig F K) (hk : cfg.kMem = 0) :
    IsEmpty (MemoryPublicAcceptedLanguage cfg) := by
  constructor
  intro x
  let witness := x.forestWitness
  have hlen : witness.1.length = 0 := witness.2.1.trans hk
  exact witness.2.2.1 (List.eq_nil_of_length_eq_zero hlen)

/-- The raw `Fin 0` RVT product is nevertheless inhabited, without choosing any tree. -/
theorem memoryExactRVTProduct_nonempty_of_kMem_eq_zero
    (cfg : ExactConfig F K) (hk : cfg.kMem = 0) :
    Nonempty (MemoryExactRVTProduct cfg) :=
  ⟨fun i => Fin.elim0 (Fin.cast hk i)⟩

/-- Therefore no memory component equivalence exists at zero roots; the positive-root hypothesis
on `memoryPublicTraversalEquiv` is logically necessary. -/
theorem no_memoryPublicTraversalEquiv_of_kMem_eq_zero
    (cfg : ExactConfig F K) (hk : cfg.kMem = 0) :
    ¬ Nonempty (MemoryPublicAcceptedLanguage cfg ≃ MemoryExactRVTProduct cfg) := by
  rintro ⟨e⟩
  obtain ⟨p⟩ := memoryExactRVTProduct_nonempty_of_kMem_eq_zero cfg hk
  exact (memoryPublicAcceptedLanguage_isEmpty_of_kMem_eq_zero cfg hk).false (e.symm p)

/-- Failed inverse laws are uninhabited for the literal public compute equivalence. -/
theorem computePublicTraversalEquiv_no_failed_inverse :
    ¬ ∃ x : ComputePublicAcceptedLanguage K,
      (computePublicTraversalEquiv K).symm
          (computePublicTraversalEquiv K x) ≠ x := by
  rintro ⟨x, hx⟩
  exact hx ((computePublicTraversalEquiv K).left_inv x)

/-- Failed inverse laws are uninhabited for the literal positive-root memory equivalence. -/
theorem memoryPublicTraversalEquiv_no_failed_inverse
    (cfg : ExactConfig F K) (hk : 0 < cfg.kMem) :
    ¬ ∃ x : MemoryExactRVTProduct cfg,
      memoryPublicTraversalEquiv cfg hk
          ((memoryPublicTraversalEquiv cfg hk).symm x) ≠ x := by
  rintro ⟨x, hx⟩
  exact hx ((memoryPublicTraversalEquiv cfg hk).right_inv x)

/-- The legacy empty accepted compute statement behind the singleton-readout mismatch cannot be
the public readout of any exact cumulative execution.  The exact readout is the whole positive BFS
list, not a per-label singleton. -/
theorem legacy_empty_singleton_readout_mismatch_cannot_inhabit
    {cfg : ExactConfig F K} (x : TraversableChainedAcceptedExecution cfg) :
    x.1.computePublicRows ≠ [] := by
  exact List.ne_nil_of_length_pos (by simpa using cfg.compRows_pos)



@[simp]
theorem properArity_node_iff {LT : Type*} {n : ℕ} (lbl : LT) (children : List (NTree LT)) :
    ProperArity n (.node lbl children) ↔
      children.length ≤ n ∧ ∀ child ∈ children, ProperArity n child := by
  constructor
  · intro h
    refine ⟨h.root, ?_⟩
    intro child hchild
    exact h.ofChild hchild
  · rintro ⟨hroot, hchildren⟩ t ht
    cases ht with
    | here => exact hroot
    | sub hchild hsub => exact hchildren _ hchild _ hsub

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.ExactExecution.computeReadout_witnessAligned
#print axioms Nock.NockVMROM.Thm54.ExactExecution.computePublicTree_bfs
#print axioms Nock.NockVMROM.Thm54.computePublicLabel_field_discrimination
#print axioms Nock.NockVMROM.Thm54.ExactExecution.computePublicExactTopology
#print axioms Nock.NockVMROM.Thm54.exact_bfsForest_child_pos
#print axioms Nock.NockVMROM.Thm54.exact_reconForest_bfsForest
#print axioms Nock.NockVMROM.Thm54.exact_childLink_firstCF_iff
#print axioms Nock.NockVMROM.Thm54.computeExactTopology_iff_traversalClause
#print axioms Nock.NockVMROM.Thm54.memoryExactTopology_iff_traversalClause
#print axioms Nock.NockVMROM.Thm54.traversableChainedSemanticExactLanguage_iff
#print axioms Nock.NockVMROM.Thm54.rvt_fcomp_iff_structure_and_rows
#print axioms Nock.NockVMROM.Thm54.rvt_fmem_iff_structure_and_rows
#print axioms Nock.NockVMROM.Thm54.computePublicTraversalEquiv
#print axioms Nock.NockVMROM.Thm54.memoryPublicTraversalEquiv
#print axioms Nock.NockVMROM.Thm54.packetLocalDefTraversableEquiv
#print axioms Nock.NockVMROM.Thm54.defTraversableRealization
#print axioms Nock.NockVMROM.Thm54.exactDefTraversable
#print axioms Nock.NockVMROM.Thm54.TraversableChainedSemanticExactLanguage.publicAcceptedComponents
#print axioms Nock.NockVMROM.Thm54.computePublicAccepted_eq_of_private_witnesses
#print axioms Nock.NockVMROM.Thm54.no_memoryPublicTraversalEquiv_of_kMem_eq_zero
#print axioms Nock.NockVMROM.Thm54.legacy_empty_singleton_readout_mismatch_cannot_inhabit
