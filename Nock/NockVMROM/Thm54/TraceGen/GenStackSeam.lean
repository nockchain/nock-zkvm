/-
  Nock/NockVMROM/Thm54/TraceGen/GenStackSeam.lean

  `HT` recorded that the production stack (`accepted_outside_failureUnion` → `GenuineWitness`) and
  the chip stack (`SharedTableWalkRow.computeWalk_final_prob_of_acceptance` = `«Thm:Walk_IOP»`,
  `memoryWalk_final_prob_of_acceptance` = `«Corr:forest»`) are *conjoined, not composed*: nothing
  projected `GenuineWitness.computeTopology` / `.memoryTopology`
  (`ProductionP8Containment.lean:314-366`, constructed at `:803-804`), so the walk chip's
  conclusion object (`Walk.ReconGoal` / `Walk.ForestReconGoal`, `Walk.lean:2830` / `:3633`) and the
  production stack's committed object (`ComputeExactTopology` / `MemoryExactTopology`,
  `ExactTraversal.lean:384` / `:415`) were two propositions that happened to coincide.

  This module composes them, in the direction `HT` §5 predicted.

  * §1 is the abstract seam, `∀`-generic in the label types, the arity and the row relation:
    a forest of `RVTWithArity L`-trees whose aggregate BFS has the committed length *is* a
    `ForestReconGoal` witness (`forestReconGoal_of_rvtWithArity`), hence a `ReconGoal` witness at
    one root (`reconGoal_of_rvtWithArity`).  The labels clause is the BFS-length proof field; the
    fanout and leaf clauses come from `StateSep` exactly as `Walk.reconTree_bindings` gets them —
    `fanout_eq_children_length_of_properArity` for the fanout clause (this is where
    `RVTWithArity`'s `ProperArity` half is spent; `ReconGoal` itself asks only for bare `RVT`, so
    the production stack's committed object is strictly *stronger* than the walk's conclusion) and
    `walk_leaf_iff_Sleaf` for the leaf clause.  **`RawTopologyBindingResidual` is not needed for
    any of them** — `computeBinding_of_exactTopology` (`RawTopologySoundness.lean:217`) already
    runs the other way through the same two lemmas.

  * §2 instantiates it at the Thm54 objects.  `ComputeExactTopology exec` is *definitionally*
    `RVTWithArity Fcomp exec.computeTree`, and `exec.compute_bfs_length` /
    `exec.memory_bfs_length` (`Execution.lean:34,36`) are the committed lengths, so no arithmetic
    side condition is introduced.  The row-label functions are literally
    `SharedTableWalkRow.computeRowLabel` / `memoryRowLabel` (`rfl`), i.e. the columns the walk
    capstone is stated at.

  * §3 is the `HT` §5 answer, and it is the strong one: the walk bad-challenge event is **empty**,
    not something to pay `h/|K|` for.  `Walk.ReconGoal` is `α`/`γ`-independent and mentions
    neither the encoder nor the child column, so `NockVM.walkBad` (`NockVM.lean:542`) is the
    filter of a predicate whose second conjunct is `¬ ReconGoal`: once the committed object holds
    the tree, the filter is empty for *every* encoder, child column and fanout column.
    `walkBad = ∅` — no injectivity, no row acceptance, no arity premise.

  * §4 lands that at the consumed capstone: `computeWalkBadRatio = 0` and
    `memoryWalkBadRatio = 0` for **every** `OptimizedFullStrictNockVMROMPackage`, unconditionally,
    because `topologyBinding`, `computeRowsAccepted` and `memoryRowsAccepted` are already fields
    (`OptimizedStrictFullPackage.lean:57-59`).

  * §5 is the projection `HT` §4 asked for: `GenuineWitness.computeReconGoal` /
    `.memoryForestReconGoal` consume `w.computeTopology` / `w.memoryTopology` — the first
    declarations to do so — at the labels of *that coin's own* specialized execution, so no
    dependent transport is needed there.  `reconGoal_of_genuineTargetAt` /
    `walkBad_eq_empty_of_genuineTargetAt` carry it to `GenuineTargetAt`, hence (with
    `OptimizedFullStrictThm54Statement.containment`) to every accepting coin outside
    `FailureUnion`.

  * §6 is the transport `HT` §4(ii) named.  It is *not* needed for §4 (the package's walkFamily
    facts are already fields), and where it is needed — identifying the coin-indexed
    `specializedExec` with `walkFamily.exec` — it is available unconditionally only at the honest
    coin, via `honest_specialization` (`:50`) composed with `walkFamily_problem` (`:52`).  For a
    general coin the identification is the hypothesis field
    `OptimizedProductionAcceptanceAt.same_problem` (`:407`), so §6 is stated as a lemma taking the
    problem equality, plus the honest-coin corollary.  Nothing here weakens that: the whole-record
    `RawProblem` equality is a clean `cases`, no `HEq` juggling required.

  Every declaration below is `∀`-generic in `F K` (§1 additionally in the label types and arity);
  no fixture, no field pin, no characteristic hypothesis.
-/

import Nock.NockVMROM.Thm54.SharedTableWalkRow
import Nock.NockVMROM.Thm54.RawTopologySoundness
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.GenStackSeam

open Classical
open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SharedTableWalkRow
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

/-! ## §1 The abstract seam

Fully generic: label types, arity and row relation are variables.  Nothing about Nock, the field,
or the challenge coins enters. -/

section Abstract

variable {S DT : Type*} {n : ℕ} {L : (S × DT) → (Fin n → Option (S × DT)) → Prop}

/-- BFS-indexed (1-based, as in the paper's walk) committed row labels of a forest, with the
`getD` default the production accessors use. -/
def rowLabelOf (ts : List (NTree (S × DT))) (dflt : NTree (S × DT)) (i : ℕ) : S × DT :=
  (((bfsForest ts)[i - 1]?).getD dflt).label

/-- The aggregate BFS label list *is* the committed row column, whenever the committed row count
is the real aggregate BFS length.  This is the `ReconGoal`/`ForestReconGoal` labels clause. -/
theorem bfs_labels_eq_rowLabels (ts : List (NTree (S × DT))) (dflt : NTree (S × DT)) {h : ℕ}
    (hlen : (bfsForest ts).length = h) :
    (bfsForest ts).map NTree.label = (List.range' 1 h).map (rowLabelOf ts dflt) := by
  refine List.ext_getElem (by simp [hlen]) ?_
  intro i h₁ h₂
  have hi : i < (bfsForest ts).length := by simpa using h₁
  have hr : i < (List.range' 1 h).length := by simpa using h₂
  rw [List.getElem_map, List.getElem_map, List.getElem_range' hr]
  simp only [rowLabelOf, Nat.one_mul, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem hi, Option.getD_some]

/-- **The seam, forest form.**  A list of `kroots` trees each in `L_RVT^{L,n}`
(`RVTWithArity`, `Traversal.lean:356`) whose aggregate BFS has the committed length satisfies the
literal `Corr:forest` conclusion `ForestReconGoal` at its own
BFS row labels.  The `ProperArity` half of `RVTWithArity` is what discharges the fanout clause. -/
theorem forestReconGoal_of_rvtWithArity (St : StateSep L)
    (ts : List (NTree (S × DT))) (dflt : NTree (S × DT)) {kroots h : ℕ}
    (hk : ts.length = kroots) (hlen : (bfsForest ts).length = h)
    (htop : ∀ t ∈ ts, RVTWithArity L t) :
    ForestReconGoal St (rowLabelOf ts dflt) kroots h := by
  have hstruct : ∀ t ∈ bfsForest ts,
      St.fanout (NTree.label t).1 = t.children.length ∧
        (t.isLeaf ↔ St.Sleaf (NTree.label t).1) := by
    intro t ht
    rw [mem_bfsForest] at ht
    obtain ⟨root, hroot, hin⟩ := ht
    have hrt := htop root hroot
    exact ⟨fanout_eq_children_length_of_properArity St hrt.1 hrt.2 t hin,
      (walk_leaf_iff_Sleaf St hrt.1 hin).1⟩
  exact ⟨ts, hk, fun t ht => (htop t ht).1,
    bfs_labels_eq_rowLabels ts dflt hlen,
    fun t ht => (hstruct t ht).1, fun t ht => (hstruct t ht).2⟩

/-- **The seam, single-root form.**  The literal `Thm:Walk_IOP` conclusion `ReconGoal` from one `RVTWithArity` tree, through the mechanized
`kroots = 1` collapse `Walk.ForestReconGoal_one`. -/
theorem reconGoal_of_rvtWithArity (St : StateSep L)
    (tree : NTree (S × DT)) {h : ℕ}
    (hlen : (bfsForest [tree]).length = h)
    (htop : RVTWithArity L tree) :
    ReconGoal St (rowLabelOf [tree] tree) h :=
  (ForestReconGoal_one St (rowLabelOf [tree] tree) h).1
    (forestReconGoal_of_rvtWithArity St [tree] tree (by simp) hlen
      (by intro t ht; rw [List.mem_singleton] at ht; exact ht ▸ htop))

/-! ### `walkBad` is the filter of a predicate containing `¬ ReconGoal` -/

variable {Kc : Type*} [Field Kc] [Fintype Kc] [DecidableEq Kc]

omit [DecidableEq Kc] in
/-- **`walkBad = ∅` from the reconstruction goal alone.**  `Walk.ReconGoal` is `α`/`γ`-independent
and mentions neither the node encoder, the child column nor the fanout column, so it empties the
bad-challenge set for *every* choice of them: no encoder injectivity, no row acceptance, no arity
premise. -/
theorem walkBad_eq_empty_of_reconGoal {node_size : ℕ} (St : StateSep L)
    (enc : (S × DT) → (Fin node_size → Kc)) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT)
    (fo : ℕ → ℕ) (h : ℕ) (hrec : ReconGoal St lbl h) :
    NockVM.walkBad St enc lbl clab fo h = ∅ := by
  rw [NockVM.walkBad, Finset.filter_eq_empty_iff]
  exact fun _ _ hp => hp.2 hrec

omit [DecidableEq Kc] in
/-- The multi-root analogue. -/
theorem walkBadForest_eq_empty_of_forestReconGoal {node_size : ℕ} (St : StateSep L)
    (enc : (S × DT) → (Fin node_size → Kc)) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT)
    (fo : ℕ → ℕ) (kroots h : ℕ) (hrec : ForestReconGoal St lbl kroots h) :
    NockVM.walkBadForest St enc lbl clab fo kroots h = ∅ := by
  rw [NockVM.walkBadForest, Finset.filter_eq_empty_iff]
  exact fun _ _ hp => hp.2 hrec

end Abstract

/-! ## §2 The Thm54 instantiation

`ComputeExactTopology exec` is definitionally `RVTWithArity Fcomp exec.computeTree`, and
`MemoryExactTopology exec` is `RVTWithArity Fmem` at every root.  The committed lengths are the
`ExactExecution` proof fields, so §1 applies with no side condition at all. -/

section Production

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Exec-level compute row labels; equal to `SharedTableWalkRow.computeRowLabel` by `rfl`. -/
def execComputeRowLabel {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    ℕ → ComputeTable.State × ComputeTable.DTcomp K :=
  rowLabelOf [exec.computeTree] exec.computeTree

/-- Exec-level memory row labels; equal to `SharedTableWalkRow.memoryRowLabel` by `rfl`. -/
def execMemoryRowLabel {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    ℕ → MemoryTable.MState × MemoryTable.DTmem K :=
  rowLabelOf exec.memoryForest
    (exec.memoryForest.get ⟨0, List.length_pos_of_ne_nil exec.memoryForest_nonempty⟩)

theorem computeRowLabel_eq (R : RawPlusIOSegmentedFamily F K) :
    computeRowLabel R = execComputeRowLabel R.exec := rfl

theorem memoryRowLabel_eq (R : RawPlusIOSegmentedFamily F K) :
    memoryRowLabel R = execMemoryRowLabel R.exec := rfl

/-- **`HT` §4(i), compute.**  The committed compute object of the production stack yields the chip
stack's conclusion: `ComputeExactTopology` ⟹ the literal `«Thm:Walk_IOP»` goal `ReconGoal` at the
committed compute rows.  No acceptance, no coin, no arithmetic side condition. -/
theorem computeReconGoal_of_exactTopology {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (htop : ComputeExactTopology exec) :
    ReconGoal (ComputeTable.comp_stateSep (K := K)) (execComputeRowLabel exec) cfg.compRows :=
  reconGoal_of_rvtWithArity (ComputeTable.comp_stateSep (K := K)) exec.computeTree
    exec.compute_bfs_length htop

/-- **`HT` §4(i), memory.**  `MemoryExactTopology` ⟹ the literal `«Corr:forest»` goal
`ForestReconGoal` at the committed memory rows, with `kroots` the real root count. -/
theorem memoryForestReconGoal_of_exactTopology {cfg : ExactConfig F K}
    {exec : ExactExecution cfg} (htop : MemoryExactTopology exec) :
    ForestReconGoal (MemoryTable.mem_stateSep (K := K)) (execMemoryRowLabel exec)
      exec.memoryForest.length cfg.memRows :=
  forestReconGoal_of_rvtWithArity (MemoryTable.mem_stateSep (K := K)) exec.memoryForest _
    rfl exec.memory_bfs_length htop

/-- The same at the walk family's own columns (`computeRowLabel`, definitionally). -/
theorem computeReconGoal (R : RawPlusIOSegmentedFamily F K)
    (htop : ComputeExactTopology R.exec) :
    ReconGoal (ComputeTable.comp_stateSep (K := K)) (computeRowLabel R) R.cfg.compRows :=
  computeReconGoal_of_exactTopology htop

theorem memoryForestReconGoal (R : RawPlusIOSegmentedFamily F K)
    (htop : MemoryExactTopology R.exec) :
    ForestReconGoal (MemoryTable.mem_stateSep (K := K)) (memoryRowLabel R)
      R.exec.memoryForest.length R.cfg.memRows :=
  memoryForestReconGoal_of_exactTopology htop

/-- Both goals from the seam premise the topology AIR actually prices: the binding residual,
under canonical row acceptance (`exactTopology_iff_rawTopologyBindingResidual_of_rowsAccepted`
is an **iff**, so this is not a strengthening). -/
theorem reconGoals_of_binding (R : RawPlusIOSegmentedFamily F K)
    (hc : R.exec.ComputeRowsAccepted) (hm : R.exec.MemoryRowsAccepted)
    (hbind : RawTopologyBindingResidual R) :
    ReconGoal (ComputeTable.comp_stateSep (K := K)) (computeRowLabel R) R.cfg.compRows ∧
      ForestReconGoal (MemoryTable.mem_stateSep (K := K)) (memoryRowLabel R)
        R.exec.memoryForest.length R.cfg.memRows := by
  obtain ⟨htc, htm⟩ :=
    (exactTopology_iff_rawTopologyBindingResidual_of_rowsAccepted R hc hm).2 hbind
  exact ⟨computeReconGoal R htc, memoryForestReconGoal R htm⟩

/-! ## §3 The `HT` §5 answer: the walk failure event is empty -/

section Empty

variable [Fintype K] [DecidableEq K]

omit [DecidableEq K] in
/-- **`walkBad = ∅`, compute.**  Given the committed exact topology, the compute walk chip's
bad-challenge set is *empty* — for every node encoder, child column and fanout column.  So the
`h/|K| + ε_RLC` walk term is not slack that has to be paid; it is a majorant of `0`. -/
theorem computeWalkBad_eq_empty {ncs : ℕ}
    (enc : (ComputeTable.State × ComputeTable.DTcomp K) → (Fin ncs → K))
    (clab : ℕ → ℕ → ComputeTable.State × ComputeTable.DTcomp K) (fo : ℕ → ℕ)
    (R : RawPlusIOSegmentedFamily F K) (htop : ComputeExactTopology R.exec) :
    NockVM.walkBad (ComputeTable.comp_stateSep (K := K)) enc (computeRowLabel R) clab fo
      R.cfg.compRows = ∅ :=
  walkBad_eq_empty_of_reconGoal _ enc _ clab fo _ (computeReconGoal R htop)

omit [DecidableEq K] in
/-- **`walkBadForest = ∅`, memory.** -/
theorem memoryWalkBadForest_eq_empty {nms : ℕ}
    (enc : (MemoryTable.MState × MemoryTable.DTmem K) → (Fin nms → K))
    (clab : ℕ → ℕ → MemoryTable.MState × MemoryTable.DTmem K) (fo : ℕ → ℕ)
    (R : RawPlusIOSegmentedFamily F K) (htop : MemoryExactTopology R.exec) :
    NockVM.walkBadForest (MemoryTable.mem_stateSep (K := K)) enc (memoryRowLabel R) clab fo
      R.exec.memoryForest.length R.cfg.memRows = ∅ :=
  walkBadForest_eq_empty_of_forestReconGoal _ enc _ clab fo _ _ (memoryForestReconGoal R htop)

/-- The single-root memory form, through the mechanized `kroots = 1` collapse
`NockVM.walkBad_eq_walkBadForest_one`: at one memory root the two recognizers are the same
`Finset`, so it is empty too. -/
theorem memoryWalkBad_eq_empty_of_one_root {nms : ℕ}
    (enc : (MemoryTable.MState × MemoryTable.DTmem K) → (Fin nms → K))
    (clab : ℕ → ℕ → MemoryTable.MState × MemoryTable.DTmem K) (fo : ℕ → ℕ)
    (R : RawPlusIOSegmentedFamily F K) (htop : MemoryExactTopology R.exec)
    (hone : R.exec.memoryForest.length = 1) :
    NockVM.walkBad (MemoryTable.mem_stateSep (K := K)) enc (memoryRowLabel R) clab fo
      R.cfg.memRows = ∅ := by
  rw [NockVM.walkBad_eq_walkBadForest_one]
  have h := memoryWalkBadForest_eq_empty enc clab fo R htop
  rwa [hone] at h

omit [DecidableEq K] in
/-- Both, from the binding residual under row acceptance. -/
theorem walkBads_eq_empty_of_binding {ncs nms : ℕ}
    (encc : (ComputeTable.State × ComputeTable.DTcomp K) → (Fin ncs → K))
    (encm : (MemoryTable.MState × MemoryTable.DTmem K) → (Fin nms → K))
    (clabc : ℕ → ℕ → ComputeTable.State × ComputeTable.DTcomp K)
    (clabm : ℕ → ℕ → MemoryTable.MState × MemoryTable.DTmem K)
    (foc fom : ℕ → ℕ)
    (R : RawPlusIOSegmentedFamily F K)
    (hc : R.exec.ComputeRowsAccepted) (hm : R.exec.MemoryRowsAccepted)
    (hbind : RawTopologyBindingResidual R) :
    NockVM.walkBad (ComputeTable.comp_stateSep (K := K)) encc (computeRowLabel R) clabc foc
        R.cfg.compRows = ∅ ∧
      NockVM.walkBadForest (MemoryTable.mem_stateSep (K := K)) encm (memoryRowLabel R) clabm fom
        R.exec.memoryForest.length R.cfg.memRows = ∅ := by
  obtain ⟨hrc, hrm⟩ := reconGoals_of_binding R hc hm hbind
  exact ⟨walkBad_eq_empty_of_reconGoal _ encc _ clabc foc _ hrc,
    walkBadForest_eq_empty_of_forestReconGoal _ encm _ clabm fom _ _ hrm⟩

end Empty

end Production

/-! ## §4 At the consumed capstone: both walk ratios are zero

`topologyBinding`, `computeRowsAccepted` and `memoryRowsAccepted` are *fields* of
`OptimizedFullStrictNockVMROMPackage`, so this is unconditional in the package — no coin, no
honest-coin restriction, no added hypothesis. -/

section Capstone

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-- The package's walk family carries the exact compute topology, from fields only. -/
theorem package_computeExactTopology (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    ComputeExactTopology P.walkFamily.exec :=
  ((exactTopology_iff_rawTopologyBindingResidual_of_rowsAccepted P.walkFamily
    P.computeRowsAccepted P.memoryRowsAccepted).2 P.topologyBinding).1

/-- …and the exact memory topology. -/
theorem package_memoryExactTopology (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    MemoryExactTopology P.walkFamily.exec :=
  ((exactTopology_iff_rawTopologyBindingResidual_of_rowsAccepted P.walkFamily
    P.computeRowsAccepted P.memoryRowsAccepted).2 P.topologyBinding).2

/-- **`«Thm:Walk_IOP»` at the package, as a fact rather than a probability.** -/
theorem package_computeReconGoal (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    ReconGoal (ComputeTable.comp_stateSep (K := K)) (computeRowLabel P.walkFamily)
      P.walkFamily.cfg.compRows :=
  computeReconGoal P.walkFamily (package_computeExactTopology P)

/-- **`«Corr:forest»` at the package, as a fact rather than a probability.** -/
theorem package_memoryForestReconGoal (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    ForestReconGoal (MemoryTable.mem_stateSep (K := K)) (memoryRowLabel P.walkFamily)
      P.walkFamily.exec.memoryForest.length P.walkFamily.cfg.memRows :=
  memoryForestReconGoal P.walkFamily (package_memoryExactTopology P)

/-- **`HT` §5, decided: the compute walk bad event is empty at the consumed capstone.** -/
theorem package_computeWalkBad_eq_empty (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    NockVM.walkBad (ComputeTable.comp_stateSep (K := K)) P.walkFamily.compNodeEncode
      (computeRowLabel P.walkFamily) (computeChildLabel P.walkFamily)
      (foCol P.walkFamily.computeWalkRows) P.walkFamily.cfg.compRows = ∅ :=
  walkBad_eq_empty_of_reconGoal _ _ _ _ _ _ (package_computeReconGoal P)

/-- **…and the memory one.** -/
theorem package_memoryWalkBadForest_eq_empty
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    NockVM.walkBadForest (MemoryTable.mem_stateSep (K := K)) P.walkFamily.memNodeEncode
      (memoryRowLabel P.walkFamily) (memoryChildLabel P.walkFamily)
      (foCol P.walkFamily.memoryWalkRows) P.walkFamily.exec.memoryForest.length
      P.walkFamily.cfg.memRows = ∅ :=
  walkBadForest_eq_empty_of_forestReconGoal _ _ _ _ _ _ _ (package_memoryForestReconGoal P)

/-- `computeWalkBadRatio` (`OptimizedStrictFullPackage.lean:118`) is the cardinality of exactly the
set §4 just emptied, so it is `0` for every package. -/
theorem package_computeWalkBadRatio_eq_zero
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    P.computeWalkBadRatio = 0 := by
  rw [OptimizedFullStrictNockVMROMPackage.computeWalkBadRatio,
    package_computeWalkBad_eq_empty P]
  simp

theorem package_memoryWalkBadRatio_eq_zero
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    P.memoryWalkBadRatio = 0 := by
  rw [OptimizedFullStrictNockVMROMPackage.memoryWalkBadRatio,
    package_memoryWalkBadForest_eq_empty P]
  simp

/-- The `walk_bounds` conjunction of `OptimizedFullStrictThm54Statement` (`:885`) re-derived from
emptiness rather than from `Walk_IOP_final_prob`: `0 ≤ bound`.  Independent of the walk chip's
Schwartz–Zippel/RLC counting. -/
theorem package_walk_bounds_of_empty (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    P.computeWalkBadRatio ≤ P.computeWalkBound ∧
      P.memoryWalkBadRatio ≤ P.memoryWalkBound := by
  have hcb : (0 : ℚ) ≤ P.computeWalkBound := by
    rw [OptimizedFullStrictNockVMROMPackage.computeWalkBound]
    positivity
  have hmb : (0 : ℚ) ≤ P.memoryWalkBound := by
    rw [OptimizedFullStrictNockVMROMPackage.memoryWalkBound]
    positivity
  exact ⟨by rw [package_computeWalkBadRatio_eq_zero P]; exact hcb,
    by rw [package_memoryWalkBadRatio_eq_zero P]; exact hmb⟩

end Capstone

/-! ## §5 The projection `HT` §4 asked for: consuming `GenuineWitness`

These are the first declarations to project `GenuineWitness.computeTopology` /
`.memoryTopology`.  They are stated at the labels of *that coin's own* specialized execution, so
no dependent transport occurs. -/

section Genuine

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

omit [Fintype K] [DecidableEq K] in
/-- **`GenuineWitness` ⟹ `«Thm:Walk_IOP»` conclusion.**  `w.computeTopology` projected, at last. -/
theorem GenuineWitness.computeReconGoal {T : ProductionStrategy F K} {q Λ : ℕ}
    {z : K} {hz : z ≠ 0} {α lmb : K} (w : GenuineWitness T q Λ z hz α lmb) :
    ReconGoal (ComputeTable.comp_stateSep (K := K))
      (execComputeRowLabel (T.specializedExec z hz α lmb)) (T.specializedCfg z hz α lmb).compRows :=
  computeReconGoal_of_exactTopology w.computeTopology

omit [Fintype K] [DecidableEq K] in
/-- **`GenuineWitness` ⟹ `«Corr:forest»` conclusion.**  `w.memoryTopology` projected. -/
theorem GenuineWitness.memoryForestReconGoal {T : ProductionStrategy F K} {q Λ : ℕ}
    {z : K} {hz : z ≠ 0} {α lmb : K} (w : GenuineWitness T q Λ z hz α lmb) :
    ForestReconGoal (MemoryTable.mem_stateSep (K := K))
      (execMemoryRowLabel (T.specializedExec z hz α lmb))
      (T.specializedExec z hz α lmb).memoryForest.length (T.specializedCfg z hz α lmb).memRows :=
  memoryForestReconGoal_of_exactTopology w.memoryTopology

omit [Fintype K] in
/-- **`GenuineTargetAt` ⟹ both walk conclusions at that coin's specialization.**  Composed with
`OptimizedFullStrictThm54Statement.containment` this says: every accepting coin outside
`FailureUnion` already carries the chip stack's conclusion. -/
theorem reconGoals_of_genuineTargetAt {T : ProductionStrategy F K} {q Λ : ℕ}
    {ω : JointCoins K} {lmb : K} (hz : nprSeed ω ≠ 0) (h : GenuineTargetAt T q Λ ω lmb) :
    ReconGoal (ComputeTable.comp_stateSep (K := K))
        (execComputeRowLabel (T.specializedExec (nprSeed ω) hz (alphaM ω) lmb))
        (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb).compRows ∧
      ForestReconGoal (MemoryTable.mem_stateSep (K := K))
        (execMemoryRowLabel (T.specializedExec (nprSeed ω) hz (alphaM ω) lmb))
        (T.specializedExec (nprSeed ω) hz (alphaM ω) lmb).memoryForest.length
        (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb).memRows := by
  rw [GenuineTargetAt, dif_pos hz] at h
  obtain ⟨w⟩ := h
  exact ⟨GenuineWitness.computeReconGoal w, GenuineWitness.memoryForestReconGoal w⟩

/-- **…hence the walk bad events are empty at every genuine coin**, for every encoder/child/fanout
column.  The `HT` §4 seam, closed in the `∀ ω` direction. -/
theorem walkBads_eq_empty_of_genuineTargetAt {T : ProductionStrategy F K} {q Λ : ℕ}
    {ω : JointCoins K} {lmb : K} (hz : nprSeed ω ≠ 0) (h : GenuineTargetAt T q Λ ω lmb)
    {ncs nms : ℕ}
    (encc : (ComputeTable.State × ComputeTable.DTcomp K) → (Fin ncs → K))
    (encm : (MemoryTable.MState × MemoryTable.DTmem K) → (Fin nms → K))
    (clabc : ℕ → ℕ → ComputeTable.State × ComputeTable.DTcomp K)
    (clabm : ℕ → ℕ → MemoryTable.MState × MemoryTable.DTmem K)
    (foc fom : ℕ → ℕ) :
    NockVM.walkBad (ComputeTable.comp_stateSep (K := K)) encc
        (execComputeRowLabel (T.specializedExec (nprSeed ω) hz (alphaM ω) lmb)) clabc foc
        (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb).compRows = ∅ ∧
      NockVM.walkBadForest (MemoryTable.mem_stateSep (K := K)) encm
        (execMemoryRowLabel (T.specializedExec (nprSeed ω) hz (alphaM ω) lmb)) clabm fom
        (T.specializedExec (nprSeed ω) hz (alphaM ω) lmb).memoryForest.length
        (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb).memRows = ∅ := by
  obtain ⟨hrc, hrm⟩ := reconGoals_of_genuineTargetAt hz h
  exact ⟨walkBad_eq_empty_of_reconGoal _ encc _ clabc foc _ hrc,
    walkBadForest_eq_empty_of_forestReconGoal _ encm _ clabm fom _ _ hrm⟩

end Genuine

/-! ## §6 The dependent transport `HT` §4(ii) named

Not needed for §4 — the package's `walkFamily` facts are fields — and available unconditionally
only at the honest coin.  The transport itself is a `cases` on a whole-record `RawProblem`
equality; no `Sigma.mk.inj_iff`/`HEq` step is required in this direction, because
`ComputeExactTopology`/`execComputeRowLabel` are functions of the *record*, and the equality that
`honest_specialization` + `walkFamily_problem` deliver is a record equality. -/

section Transport

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem computeExactTopology_of_problem_eq {Q₁ Q₂ : RawProblem F K} (heq : Q₁ = Q₂)
    (htop : ComputeExactTopology Q₁.exec) : ComputeExactTopology Q₂.exec := by
  cases heq; exact htop

theorem memoryExactTopology_of_problem_eq {Q₁ Q₂ : RawProblem F K} (heq : Q₁ = Q₂)
    (htop : MemoryExactTopology Q₁.exec) : MemoryExactTopology Q₂.exec := by
  cases heq; exact htop

theorem execComputeRowLabel_of_problem_eq {Q₁ Q₂ : RawProblem F K} (heq : Q₁ = Q₂) :
    execComputeRowLabel Q₁.exec = execComputeRowLabel Q₂.exec := by
  cases heq; rfl

theorem execMemoryRowLabel_of_problem_eq {Q₁ Q₂ : RawProblem F K} (heq : Q₁ = Q₂) :
    execMemoryRowLabel Q₁.exec = execMemoryRowLabel Q₂.exec := by
  cases heq; rfl

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

/-- The honest coin's specialization *is* the walk family's problem, unconditionally, from the two
package fields `honest_specialization` (`:50`) and `walkFamily_problem` (`:52`). -/
theorem package_honest_problem_eq {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    specializedProblem P.optimized.verifier.raw.timestamp P.honestSeed P.honestSeed_ne
        P.honestAlpha P.optimized.objects.cfg.challenges.lam = P.walkFamily.problem :=
  P.honest_specialization.trans P.walkFamily_problem.symm

/-- **`HT` §4(ii) at the honest coin.**  A `GenuineWitness` at the honest seed/alpha of the
package's own strategy transports to the walk family's columns, so the two stacks' conclusions are
literally the same proposition there.  `P.strategy.verifier = P.optimized.verifier` by `rfl`
(`productionStrategy_of_scan`), which is why no further identification is needed. -/
theorem package_honest_walkFamily_reconGoals {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb) {q Λ : ℕ}
    (w : GenuineWitness P.strategy q Λ P.honestSeed P.honestSeed_ne P.honestAlpha
      P.optimized.objects.cfg.challenges.lam) :
    ReconGoal (ComputeTable.comp_stateSep (K := K)) (computeRowLabel P.walkFamily)
        P.walkFamily.cfg.compRows ∧
      ForestReconGoal (MemoryTable.mem_stateSep (K := K)) (memoryRowLabel P.walkFamily)
        P.walkFamily.exec.memoryForest.length P.walkFamily.cfg.memRows := by
  have heq := package_honest_problem_eq P
  exact ⟨computeReconGoal P.walkFamily
      (computeExactTopology_of_problem_eq heq w.computeTopology),
    memoryForestReconGoal P.walkFamily
      (memoryExactTopology_of_problem_eq heq w.memoryTopology)⟩

end Transport

/-! ## §7 The composition, at the consumed capstone

`P.containment` (`OptimizedStrictFullPackage.lean:148`, the unconditional package form of
`OptimizedFullStrictThm54Statement.containment` `:882`) fed into §5. -/

section Composed

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-- **Production acceptance ⟹ the walk chips' conclusions.**  Every coin the production stack
accepts outside `FailureUnion` already carries `«Thm:Walk_IOP»`'s and `«Corr:forest»`'s literal
conclusions at that coin's own specialized execution — no `h/|K|` payment, no encoder, no
challenge. -/
theorem package_reconGoals_of_accepted
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb) {ω : JointCoins K} {lmb : K}
    (hz : nprSeed ω ≠ 0) (hacc : P.strategy.Accepts ω lmb)
    (hout : ω ∉ ProductionP8Containment.FailureUnion P.strategy P.optimized.census lmb) :
    ReconGoal (ComputeTable.comp_stateSep (K := K))
        (execComputeRowLabel (P.strategy.specializedExec (nprSeed ω) hz (alphaM ω) lmb))
        (P.strategy.specializedCfg (nprSeed ω) hz (alphaM ω) lmb).compRows ∧
      ForestReconGoal (MemoryTable.mem_stateSep (K := K))
        (execMemoryRowLabel (P.strategy.specializedExec (nprSeed ω) hz (alphaM ω) lmb))
        (P.strategy.specializedExec (nprSeed ω) hz (alphaM ω) lmb).memoryForest.length
        (P.strategy.specializedCfg (nprSeed ω) hz (alphaM ω) lmb).memRows :=
  reconGoals_of_genuineTargetAt hz (P.containment ω lmb hacc hout)

/-- …hence the coin-indexed walk bad events are empty there too. -/
theorem package_walkBads_eq_empty_of_accepted
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb) {ω : JointCoins K} {lmb : K}
    (hz : nprSeed ω ≠ 0) (hacc : P.strategy.Accepts ω lmb)
    (hout : ω ∉ ProductionP8Containment.FailureUnion P.strategy P.optimized.census lmb)
    {ncs nms : ℕ}
    (encc : (ComputeTable.State × ComputeTable.DTcomp K) → (Fin ncs → K))
    (encm : (MemoryTable.MState × MemoryTable.DTmem K) → (Fin nms → K))
    (clabc : ℕ → ℕ → ComputeTable.State × ComputeTable.DTcomp K)
    (clabm : ℕ → ℕ → MemoryTable.MState × MemoryTable.DTmem K)
    (foc fom : ℕ → ℕ) :
    NockVM.walkBad (ComputeTable.comp_stateSep (K := K)) encc
        (execComputeRowLabel (P.strategy.specializedExec (nprSeed ω) hz (alphaM ω) lmb)) clabc foc
        (P.strategy.specializedCfg (nprSeed ω) hz (alphaM ω) lmb).compRows = ∅ ∧
      NockVM.walkBadForest (MemoryTable.mem_stateSep (K := K)) encm
        (execMemoryRowLabel (P.strategy.specializedExec (nprSeed ω) hz (alphaM ω) lmb)) clabm fom
        (P.strategy.specializedExec (nprSeed ω) hz (alphaM ω) lmb).memoryForest.length
        (P.strategy.specializedCfg (nprSeed ω) hz (alphaM ω) lmb).memRows = ∅ :=
  walkBads_eq_empty_of_genuineTargetAt hz (P.containment ω lmb hacc hout) encc encm clabc clabm foc fom

end Composed

end

end Nock.NockVMROM.Thm54.GenStackSeam

#print axioms Nock.NockVMROM.Thm54.GenStackSeam.bfs_labels_eq_rowLabels
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.forestReconGoal_of_rvtWithArity
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.reconGoal_of_rvtWithArity
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.walkBad_eq_empty_of_reconGoal
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.walkBadForest_eq_empty_of_forestReconGoal
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.computeRowLabel_eq
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.memoryRowLabel_eq
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.computeReconGoal_of_exactTopology
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.memoryForestReconGoal_of_exactTopology
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.computeReconGoal
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.memoryForestReconGoal
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.reconGoals_of_binding
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.computeWalkBad_eq_empty
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.memoryWalkBadForest_eq_empty
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.memoryWalkBad_eq_empty_of_one_root
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.walkBads_eq_empty_of_binding
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.package_computeExactTopology
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.package_memoryExactTopology
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.package_computeReconGoal
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.package_memoryForestReconGoal
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.package_computeWalkBad_eq_empty
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.package_memoryWalkBadForest_eq_empty
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.package_computeWalkBadRatio_eq_zero
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.package_memoryWalkBadRatio_eq_zero
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.package_walk_bounds_of_empty
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.GenuineWitness.computeReconGoal
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.GenuineWitness.memoryForestReconGoal
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.reconGoals_of_genuineTargetAt
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.walkBads_eq_empty_of_genuineTargetAt
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.computeExactTopology_of_problem_eq
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.memoryExactTopology_of_problem_eq
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.execComputeRowLabel_of_problem_eq
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.execMemoryRowLabel_of_problem_eq
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.package_honest_problem_eq
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.package_honest_walkFamily_reconGoals
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.package_reconGoals_of_accepted
#print axioms Nock.NockVMROM.Thm54.GenStackSeam.package_walkBads_eq_empty_of_accepted
