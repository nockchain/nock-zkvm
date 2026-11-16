/-
  Nock/NockVMROM/Thm54/SharedTableWalkRow.lean

  `RedTeam.Batch18.b18_walk_final_prob_requires_semantic_bindings` records that `hfo` and `hFcommit`
  are open premises of the walk theorem: the seven-gate `walkAIR` shape alone does not instantiate
  them.  This module instantiates them from the production objects.

  ## The single selector bank

  The
  authoritative `ComputeTable.comp_stateSep` / `MemoryTable.mem_stateSep` are the *only* source of a fanout, and every column below is a projection of the
  authoritative BFS list `R.computeWalkRows = bfsForest [R.exec.computeTree]` /
  `R.memoryWalkRows = bfsForest R.exec.memoryForest`:

  * the walk state and data are `computeRowLabel R i` — literally the BFS node's label;
  * the walk `cur` column is `Walk.curCol` of that same list at the RLC valuation
    (`curCol_eq_rlc_rowLabel`), so the walk row and the table row are one object;
  * each active child payload is `computeChildLabel R i (j+1)` — the BFS node's own `j`-th child
    label (`childLabel_eq_childLabel`), i.e. the topology BFS child index;
  * the fanout column is `Walk.foCol` of that list, and `hfo_compute` proves it *equals* the
    authoritative `comp_stateSep.fanout` of the row state.

  ## What discharges what

  * `hfo` comes from `RawTopologySoundness.RawTopologyBindingResidual` alone (fanout = real child
    count), which acceptance supplies through
    `RawTopologyAIR.RawMessage.exactTopology_of_accepts_and_verifierGeneratedTopologyRAPOfCommittedArrays`
    and `exactTopology_iff_rawTopologyBindingResidual_of_rowsAccepted`.
  * `hFcommit` needs the binding residual *and* canonical row acceptance
    (`ExactExecution.ComputeRowsAccepted`), because `Fcomp` carries `Vcomp` and the state tag.
  * `hSf`, `hvalid`, `harity` are structural facts of a genuine BFS list
    (`Walk.foCol_Sf_tiling` / `Walk.foCol_BFSValid` and their forest forms), so the walk capstone is
    reached with *no* remaining walk-side hypothesis.

  No new random-collision event is introduced: every statement in this module is deterministic in the
  committed data, and the walk capstone's own `γ`/`α` events are the ones already counted by
  `Walk_IOP_final_prob`.  The one `γ` RLC event of the topology AIR is the pre-existing
  `topologyBadGammas` / `topologyWorkload` accounting (`RawTopologyAIR.topologyAIR_random_workload`).
-/

import Nock.NockVMROM.Thm54.RawTopologyAIR

namespace Nock.NockVMROM.Thm54.SharedTableWalkRow

open Classical
open Nock Nock.Walk
open Nock.NockVMROM.Thm54

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## The authoritative BFS lists -/

theorem computeWalkRows_eq (R : RawPlusIOSegmentedFamily F K) :
    R.computeWalkRows = bfsForest [R.exec.computeTree] := rfl

theorem memoryWalkRows_eq (R : RawPlusIOSegmentedFamily F K) :
    R.memoryWalkRows = bfsForest R.exec.memoryForest := rfl

/-! ## The one shared row

`computeNodeAtIdx R i` is the `i`-th (1-indexed, as in the paper's walk) authoritative BFS node.
Its label is the table row, its children are the walk children, and `Walk.foCol` of the same list is
the fanout column. -/

/-- The `i`-th authoritative compute BFS node (1-indexed). -/
def computeNodeAtIdx (R : RawPlusIOSegmentedFamily F K) (i : ℕ) :
    NTree (ComputeTable.State × ComputeTable.DTcomp K) :=
  (R.computeWalkRows[i - 1]?).getD R.exec.computeTree

/-- The `i`-th authoritative memory BFS node (1-indexed). -/
def memoryNodeAtIdx (R : RawPlusIOSegmentedFamily F K) (i : ℕ) :
    NTree (MemoryTable.MState × MemoryTable.DTmem K) :=
  (R.memoryWalkRows[i - 1]?).getD
    (R.exec.memoryForest.get ⟨0, List.length_pos_of_ne_nil R.exec.memoryForest_nonempty⟩)

/-- The committed compute walk row label. -/
def computeRowLabel (R : RawPlusIOSegmentedFamily F K) (i : ℕ) :
    ComputeTable.State × ComputeTable.DTcomp K :=
  (computeNodeAtIdx R i).label

/-- The committed memory walk row label. -/
def memoryRowLabel (R : RawPlusIOSegmentedFamily F K) (i : ℕ) :
    MemoryTable.MState × MemoryTable.DTmem K :=
  (memoryNodeAtIdx R i).label

/-- The committed compute child label at walk row `i`, child slot `l` (1-indexed). -/
def computeChildLabel (R : RawPlusIOSegmentedFamily F K) (i l : ℕ) :
    ComputeTable.State × ComputeTable.DTcomp K :=
  (((computeNodeAtIdx R i).children[l - 1]?).getD R.exec.computeTree).label

/-- The committed memory child label at walk row `i`, child slot `l` (1-indexed). -/
def memoryChildLabel (R : RawPlusIOSegmentedFamily F K) (i l : ℕ) :
    MemoryTable.MState × MemoryTable.DTmem K :=
  (((memoryNodeAtIdx R i).children[l - 1]?).getD
    (R.exec.memoryForest.get ⟨0, List.length_pos_of_ne_nil R.exec.memoryForest_nonempty⟩)).label

/-! ### In-range identification -/

theorem computeWalkRows_getElem?
    (R : RawPlusIOSegmentedFamily F K) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ R.cfg.compRows) :
    R.computeWalkRows[i - 1]? = some (computeNodeAtIdx R i) := by
  have hlt : i - 1 < R.computeWalkRows.length := by
    rw [computeWalkRows_length]; omega
  rw [computeNodeAtIdx, List.getElem?_eq_getElem hlt]
  rfl

theorem memoryWalkRows_getElem?
    (R : RawPlusIOSegmentedFamily F K) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ R.cfg.memRows) :
    R.memoryWalkRows[i - 1]? = some (memoryNodeAtIdx R i) := by
  have hlt : i - 1 < R.memoryWalkRows.length := by
    rw [memoryWalkRows_length]; omega
  rw [memoryNodeAtIdx, List.getElem?_eq_getElem hlt]
  rfl

theorem computeNodeAtIdx_mem
    (R : RawPlusIOSegmentedFamily F K) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ R.cfg.compRows) :
    computeNodeAtIdx R i ∈ R.computeWalkRows :=
  List.mem_of_getElem? (computeWalkRows_getElem? R h1 h2)

theorem memoryNodeAtIdx_mem
    (R : RawPlusIOSegmentedFamily F K) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ R.cfg.memRows) :
    memoryNodeAtIdx R i ∈ R.memoryWalkRows :=
  List.mem_of_getElem? (memoryWalkRows_getElem? R h1 h2)

/-- The walk fanout column of the authoritative list is the real child count of the shared row. -/
theorem foCol_compute_eq
    (R : RawPlusIOSegmentedFamily F K) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ R.cfg.compRows) :
    foCol R.computeWalkRows i = (computeNodeAtIdx R i).children.length := by
  rw [foCol, computeWalkRows_getElem? R h1 h2]
  rfl

theorem foCol_memory_eq
    (R : RawPlusIOSegmentedFamily F K) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ R.cfg.memRows) :
    foCol R.memoryWalkRows i = (memoryNodeAtIdx R i).children.length := by
  rw [foCol, memoryWalkRows_getElem? R h1 h2]
  rfl

/-- The walk `cur` column at the RLC valuation is the RLC of the shared row's own encoding: the
walk row and the table row are literally one object. -/
theorem curCol_eq_rlc_rowLabel {ncs : ℕ}
    (enc : (ComputeTable.State × ComputeTable.DTcomp K) → (Fin ncs → K)) (γ : K)
    (R : RawPlusIOSegmentedFamily F K) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ R.cfg.compRows) :
    curCol (fun t => rlc γ (enc (NTree.label t))) R.computeWalkRows i =
      rlc γ (enc (computeRowLabel R i)) := by
  rw [curCol, computeWalkRows_getElem? R h1 h2]
  rfl

/-- The walk `chld` column is the RLC of the shared row's own `l`-th child label. -/
theorem chldCol_eq_rlc_childLabel {ncs : ℕ}
    (enc : (ComputeTable.State × ComputeTable.DTcomp K) → (Fin ncs → K)) (γ : K)
    (R : RawPlusIOSegmentedFamily F K) {i l : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ R.cfg.compRows)
    (hl : l - 1 < (computeNodeAtIdx R i).children.length) :
    chldCol (fun t => rlc γ (enc (NTree.label t))) R.computeWalkRows i l =
      rlc γ (enc (computeChildLabel R i l)) := by
  rw [chldCol, computeWalkRows_getElem? R h1 h2]
  simp only [Option.bind_some, computeChildLabel,
    List.getElem?_eq_getElem hl, Option.map_some, Option.getD_some]

/-- The committed child label is the shared row's `NTree.childLabel`, i.e. exactly the topology BFS
child at that slot. -/
theorem childLabel_eq_childLabel
    (R : RawPlusIOSegmentedFamily F K) {i : ℕ} {j : ℕ}
    (hj : j < (computeNodeAtIdx R i).children.length) :
    (computeNodeAtIdx R i).childLabel j = some (computeChildLabel R i (j + 1)) := by
  simp only [NTree.childLabel, NTree.childOpt, computeChildLabel, Nat.add_sub_cancel,
    List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]

theorem memoryChildLabel_eq_childLabel
    (R : RawPlusIOSegmentedFamily F K) {i : ℕ} {j : ℕ}
    (hj : j < (memoryNodeAtIdx R i).children.length) :
    (memoryNodeAtIdx R i).childLabel j = some (memoryChildLabel R i (j + 1)) := by
  simp only [NTree.childLabel, NTree.childOpt, memoryChildLabel, Nat.add_sub_cancel,
    List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]

/-! ## Structural walk hypotheses (no prover input) -/

theorem compute_hSf (R : RawPlusIOSegmentedFamily F K) :
    Sf (foCol R.computeWalkRows) R.cfg.compRows + 1 = R.cfg.compRows := by
  have h := foCol_Sf_tiling (LT := ComputeTable.State × ComputeTable.DTcomp K)
    R.exec.computeTree
  rw [← computeWalkRows_eq R] at h
  rwa [computeWalkRows_length R] at h

theorem compute_hvalid (R : RawPlusIOSegmentedFamily F K) :
    BFSValid (foCol R.computeWalkRows) R.cfg.compRows := by
  have h := foCol_BFSValid (LT := ComputeTable.State × ComputeTable.DTcomp K)
    R.exec.computeTree
  rw [← computeWalkRows_eq R] at h
  rwa [computeWalkRows_length R] at h

theorem memory_kroots_pos (R : RawPlusIOSegmentedFamily F K) :
    1 ≤ R.exec.memoryForest.length :=
  List.length_pos_of_ne_nil R.exec.memoryForest_nonempty

theorem memory_hSf (R : RawPlusIOSegmentedFamily F K) :
    R.exec.memoryForest.length + Sf (foCol R.memoryWalkRows) R.cfg.memRows = R.cfg.memRows := by
  have h := foCol_Sf_tilingF (LT := MemoryTable.MState × MemoryTable.DTmem K)
    R.exec.memoryForest R.exec.memoryForest_nonempty
  rw [← memoryWalkRows_eq R] at h
  rwa [memoryWalkRows_length R] at h

theorem memory_hvalid (R : RawPlusIOSegmentedFamily F K) :
    BFSValidF R.exec.memoryForest.length (foCol R.memoryWalkRows) R.cfg.memRows := by
  have h := foCol_BFSValidF (LT := MemoryTable.MState × MemoryTable.DTmem K)
    R.exec.memoryForest R.exec.memoryForest_nonempty
  rw [← memoryWalkRows_eq R] at h
  rwa [memoryWalkRows_length R] at h

/-! ## `hfo`: the fanout column IS the authoritative selector bank -/

/-- **B1, compute `hfo`.**  The walk fanout column equals `comp_stateSep.fanout` of the shared row's
state, from the topology binding residual alone.  `comp_stateSep` is aliased, not re-defined. -/
theorem hfo_compute (R : RawPlusIOSegmentedFamily F K)
    (hbind : RawTopologyBindingResidual R) :
    ∀ i, 1 ≤ i → i ≤ R.cfg.compRows →
      foCol R.computeWalkRows i =
        (ComputeTable.comp_stateSep (K := K)).fanout (computeRowLabel R i).1 := by
  intro i h1 h2
  rw [foCol_compute_eq R h1 h2]
  exact ((hbind.1 _ (computeNodeAtIdx_mem R h1 h2)).1).symm

/-- **B1, memory `hfo`.** -/
theorem hfo_memory (R : RawPlusIOSegmentedFamily F K)
    (hbind : RawTopologyBindingResidual R) :
    ∀ i, 1 ≤ i → i ≤ R.cfg.memRows →
      foCol R.memoryWalkRows i =
        (MemoryTable.mem_stateSep (K := K)).fanout (memoryRowLabel R i).1 := by
  intro i h1 h2
  rw [foCol_memory_eq R h1 h2]
  exact ((hbind.2 _ (memoryNodeAtIdx_mem R h1 h2)).1).symm

/-- Arity bound of the compute fanout column, at every index. -/
theorem harity_compute (R : RawPlusIOSegmentedFamily F K)
    (hbind : RawTopologyBindingResidual R) :
    ∀ i, foCol R.computeWalkRows i ≤ 3 := by
  intro i
  rcases hopt : R.computeWalkRows[i - 1]? with _ | t
  · simp [foCol, hopt]
  · have hmem : t ∈ R.computeWalkRows := List.mem_of_getElem? hopt
    have hb := (hbind.1 t hmem).1
    have : foCol R.computeWalkRows i = t.children.length := by
      rw [foCol, hopt]; rfl
    rw [this, ← hb]
    exact (ComputeTable.comp_stateSep (K := K)).fanout_le t.label.1

/-- Arity bound of the memory fanout column, at every index. -/
theorem harity_memory (R : RawPlusIOSegmentedFamily F K)
    (hbind : RawTopologyBindingResidual R) :
    ∀ i, foCol R.memoryWalkRows i ≤ 2 := by
  intro i
  rcases hopt : R.memoryWalkRows[i - 1]? with _ | t
  · simp [foCol, hopt]
  · have hmem : t ∈ R.memoryWalkRows := List.mem_of_getElem? hopt
    have hb := (hbind.2 t hmem).1
    have : foCol R.memoryWalkRows i = t.children.length := by
      rw [foCol, hopt]; rfl
    rw [this, ← hb]
    exact (MemoryTable.mem_stateSep (K := K)).fanout_le t.label.1

/-! ## `hFcommit`: the committed children satisfy `Fcomp` / `Fmem` -/

/-- **B1, compute `hFcommit`.**  Joint table + topology acceptance: canonical row acceptance gives
the state tag and `Vcomp`, and the topology binding residual gives both the dynamic-labeling
prefix and the `x_out^comp` child link. -/
theorem hFcommit_compute (R : RawPlusIOSegmentedFamily F K)
    (hrows : R.exec.ComputeRowsAccepted)
    (hbind : RawTopologyBindingResidual R) :
    ∀ i, 1 ≤ i → i ≤ R.cfg.compRows →
      ComputeTable.Fcomp (computeRowLabel R i)
        (fun j : Fin 3 =>
          if (j : ℕ) < foCol R.computeWalkRows i then
            some (computeChildLabel R i ((j : ℕ) + 1)) else none) := by
  intro i h1 h2
  have hmem := computeNodeAtIdx_mem R h1 h2
  obtain ⟨hfan, hlink⟩ := hbind.1 _ hmem
  have hlabel : (computeNodeAtIdx R i).label ∈ R.exec.computeRows :=
    List.mem_map.mpr ⟨computeNodeAtIdx R i, hmem, rfl⟩
  have hrow := (ExactExecution.computeRowsAccepted_iff R.exec).1 hrows _ hlabel
  have hfoi : foCol R.computeWalkRows i = (computeNodeAtIdx R i).children.length :=
    foCol_compute_eq R h1 h2
  have hfan' : ComputeTable.fanoutComp (computeRowLabel R i).1 =
      foCol R.computeWalkRows i := by
    rw [hfoi]; exact hfan
  refine ⟨hrow.1.symm, hrow.2.2, ?_, ?_⟩
  · intro j
    rw [hfan']
    by_cases hj : (j : ℕ) < foCol R.computeWalkRows i <;> simp [hj]
  · intro j hj
    rw [hfan'] at hj
    have hjlen : (j : ℕ) < (computeNodeAtIdx R i).children.length := by
      rw [← hfoi]; exact hj
    have hchild := hlink j (by rw [hfan]; exact hjlen)
    simp only [childLabel_eq_childLabel R hjlen] at hchild
    simp only [if_pos hj]
    exact hchild

/-- **B1, memory `hFcommit`.** -/
theorem hFcommit_memory (R : RawPlusIOSegmentedFamily F K)
    (hrows : R.exec.MemoryRowsAccepted)
    (hbind : RawTopologyBindingResidual R) :
    ∀ i, 1 ≤ i → i ≤ R.cfg.memRows →
      MemoryTable.Fmem (memoryRowLabel R i)
        (fun j : Fin 2 =>
          if (j : ℕ) < foCol R.memoryWalkRows i then
            some (memoryChildLabel R i ((j : ℕ) + 1)) else none) := by
  intro i h1 h2
  have hmem := memoryNodeAtIdx_mem R h1 h2
  obtain ⟨hfan, hlink⟩ := hbind.2 _ hmem
  have hlabel : (memoryNodeAtIdx R i).label ∈ R.exec.memoryRows :=
    List.mem_map.mpr ⟨memoryNodeAtIdx R i, hmem, rfl⟩
  have hrow := (ExactExecution.memoryRowsAccepted_iff R.exec).1 hrows _ hlabel
  have hfoi : foCol R.memoryWalkRows i = (memoryNodeAtIdx R i).children.length :=
    foCol_memory_eq R h1 h2
  have hfan' : MemoryTable.fanoutMem (memoryRowLabel R i).1 =
      foCol R.memoryWalkRows i := by
    rw [hfoi]; exact hfan
  refine ⟨hrow.1.symm, hrow.2.2.1, ?_, ?_⟩
  · intro j
    rw [hfan']
    by_cases hj : (j : ℕ) < foCol R.memoryWalkRows i <;> simp [hj]
  · intro j hj
    rw [hfan'] at hj
    have hjlen : (j : ℕ) < (memoryNodeAtIdx R i).children.length := by
      rw [← hfoi]; exact hj
    have hchild := hlink j (by rw [hfan]; exact hjlen)
    simp only [memoryChildLabel_eq_childLabel R hjlen] at hchild
    simp only [if_pos hj]
    exact hchild

/-! ## The walk capstone with every hypothesis discharged -/

section Prob

variable [Fintype K] [DecidableEq K]

/-- **B1 capstone, compute walk.**  `Walk.Walk_IOP_final_prob` at the production columns, with
`hSf`, `hvalid`, `harity`, `hfo` and `hFcommit` all discharged internally from joint table + walk
acceptance and the topology binding residual.  Only the node encoding (a backend parameter) and its
injectivity remain. -/
theorem computeWalk_final_prob_of_acceptance {ncs : ℕ}
    (enc : (ComputeTable.State × ComputeTable.DTcomp K) → (Fin ncs → K))
    (hEnc : Function.Injective enc)
    (R : RawPlusIOSegmentedFamily F K)
    (hrows : R.exec.ComputeRowsAccepted)
    (hbind : RawTopologyBindingResidual R) :
    ((NockVM.walkBad (ComputeTable.comp_stateSep (K := K)) enc
        (computeRowLabel R) (computeChildLabel R) (foCol R.computeWalkRows)
        R.cfg.compRows).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (R.cfg.compRows : ℚ) / (Fintype.card K : ℚ)
          + ((R.cfg.compRows * (ncs - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ) :=
  NockVM.walkBad_prob (ComputeTable.comp_stateSep (K := K)) enc hEnc
    (computeRowLabel R) (computeChildLabel R) (foCol R.computeWalkRows)
    (compute_hSf R) (compute_hvalid R) (harity_compute R hbind)
    (hfo_compute R hbind) (hFcommit_compute R hrows hbind)

/-- **B1 capstone, compute walk, at the paper's label**: the encoder
need only determine the `LT_comp` projection; `Fcomp` reads children through that projection
(`ComputeTable.Fcomp_respects_labelOf`). -/
theorem computeWalk_final_prob_of_acceptance_of_label {ncs : ℕ}
    (enc : (ComputeTable.State × ComputeTable.DTcomp K) → (Fin ncs → K))
    (hEnc : ∀ a b, enc a = enc b →
      ComputeTable.computeLabelOf a = ComputeTable.computeLabelOf b)
    (R : RawPlusIOSegmentedFamily F K)
    (hrows : R.exec.ComputeRowsAccepted)
    (hbind : RawTopologyBindingResidual R) :
    ((NockVM.walkBad (ComputeTable.comp_stateSep (K := K)) enc
        (computeRowLabel R) (computeChildLabel R) (foCol R.computeWalkRows)
        R.cfg.compRows).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (R.cfg.compRows : ℚ) / (Fintype.card K : ℚ)
          + ((R.cfg.compRows * (ncs - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ) :=
  NockVM.walkBad_prob_of_label (ComputeTable.comp_stateSep (K := K))
    ComputeTable.computeLabelOf
    (fun lbl _ _ h hF => ComputeTable.Fcomp_respects_labelOf lbl h hF)
    enc hEnc
    (computeRowLabel R) (computeChildLabel R) (foCol R.computeWalkRows)
    (compute_hSf R) (compute_hvalid R) (harity_compute R hbind)
    (hfo_compute R hbind) (hFcommit_compute R hrows hbind)

/-- **B1 capstone, memory walk**. -/
theorem memoryWalk_final_prob_of_acceptance {nms : ℕ}
    (enc : (MemoryTable.MState × MemoryTable.DTmem K) → (Fin nms → K))
    (hEnc : Function.Injective enc)
    (R : RawPlusIOSegmentedFamily F K)
    (hrows : R.exec.MemoryRowsAccepted)
    (hbind : RawTopologyBindingResidual R) :
    ((NockVM.walkBadForest (MemoryTable.mem_stateSep (K := K)) enc
        (memoryRowLabel R) (memoryChildLabel R) (foCol R.memoryWalkRows)
        R.exec.memoryForest.length R.cfg.memRows).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (R.cfg.memRows : ℚ) / (Fintype.card K : ℚ)
          + ((R.cfg.memRows * (nms - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ) :=
  NockVM.walkBadForest_prob (MemoryTable.mem_stateSep (K := K)) enc hEnc
    (memoryRowLabel R) (memoryChildLabel R) (foCol R.memoryWalkRows)
    (memory_kroots_pos R) (memory_hSf R) (memory_hvalid R) (harity_memory R hbind)
    (hfo_memory R hbind) (hFcommit_memory R hrows hbind)

/-- **B1 capstone, memory walk, at the paper's label**: the encoder need only determine the `x^mem` projection; `Fmem`
reads children through that projection (`MemoryTable.Fmem_respects_labelOf`). -/
theorem memoryWalk_final_prob_of_acceptance_of_label {nms : ℕ}
    (enc : (MemoryTable.MState × MemoryTable.DTmem K) → (Fin nms → K))
    (hEnc : ∀ a b, enc a = enc b →
      MemoryTable.memoryLabelOf a = MemoryTable.memoryLabelOf b)
    (R : RawPlusIOSegmentedFamily F K)
    (hrows : R.exec.MemoryRowsAccepted)
    (hbind : RawTopologyBindingResidual R) :
    ((NockVM.walkBadForest (MemoryTable.mem_stateSep (K := K)) enc
        (memoryRowLabel R) (memoryChildLabel R) (foCol R.memoryWalkRows)
        R.exec.memoryForest.length R.cfg.memRows).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (R.cfg.memRows : ℚ) / (Fintype.card K : ℚ)
          + ((R.cfg.memRows * (nms - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ) :=
  NockVM.walkBadForest_prob_of_label (MemoryTable.mem_stateSep (K := K))
    MemoryTable.memoryLabelOf
    (fun lbl _ _ h hF => MemoryTable.Fmem_respects_labelOf lbl h hF)
    enc hEnc
    (memoryRowLabel R) (memoryChildLabel R) (foCol R.memoryWalkRows)
    (memory_kroots_pos R) (memory_hSf R) (memory_hvalid R) (harity_memory R hbind)
    (hfo_memory R hbind) (hFcommit_memory R hrows hbind)

end Prob

/-! ## OP0 slice: what the shared row rejects

There is no free selector column: `comp_stateSep.fanout` is a total function of the committed state,
so an all-zero or duplicated selector cannot even be expressed.  The two rejection facts that remain
meaningful are therefore stated against the authoritative selector bank. -/

/-- A row whose real child count disagrees with `comp_stateSep.fanout` of its committed state
falsifies the topology binding residual — so it can never reach the walk capstone. -/
theorem wrong_fanout_no_binding (R : RawPlusIOSegmentedFamily F K)
    {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ R.cfg.compRows)
    (hne : foCol R.computeWalkRows i ≠
      (ComputeTable.comp_stateSep (K := K)).fanout (computeRowLabel R i).1) :
    ¬ RawTopologyBindingResidual R := fun hbind => hne (hfo_compute R hbind i h1 h2)

/-- An `OP_0` (`s0`) row is a walk leaf: the authoritative selector bank gives it fanout `0`, so any
committed child at that row is rejected. -/
theorem s0_is_leaf (R : RawPlusIOSegmentedFamily F K)
    (hbind : RawTopologyBindingResidual R)
    {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ R.cfg.compRows)
    (hs0 : (computeRowLabel R i).1 = .s0) :
    foCol R.computeWalkRows i = 0 ∧ (computeNodeAtIdx R i).children = [] := by
  have hfo := hfo_compute R hbind i h1 h2
  have hzero : foCol R.computeWalkRows i = 0 := by
    rw [hfo, hs0]
    rfl
  refine ⟨hzero, ?_⟩
  have := foCol_compute_eq R h1 h2
  rw [hzero] at this
  exact List.eq_nil_of_length_eq_zero this.symm

/-- The memory analogue: a `halt` row is a walk leaf. -/
theorem halt_is_leaf (R : RawPlusIOSegmentedFamily F K)
    (hbind : RawTopologyBindingResidual R)
    {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ R.cfg.memRows)
    (hhalt : (memoryRowLabel R i).1 = .halt) :
    foCol R.memoryWalkRows i = 0 ∧ (memoryNodeAtIdx R i).children = [] := by
  have hfo := hfo_memory R hbind i h1 h2
  have hzero : foCol R.memoryWalkRows i = 0 := by
    rw [hfo, hhalt]
    rfl
  refine ⟨hzero, ?_⟩
  have := foCol_memory_eq R h1 h2
  rw [hzero] at this
  exact List.eq_nil_of_length_eq_zero this.symm

end

end Nock.NockVMROM.Thm54.SharedTableWalkRow

#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.computeWalkRows_getElem?
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.memoryWalkRows_getElem?
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.foCol_compute_eq
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.foCol_memory_eq
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.curCol_eq_rlc_rowLabel
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.chldCol_eq_rlc_childLabel
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.childLabel_eq_childLabel
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.memoryChildLabel_eq_childLabel
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.compute_hSf
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.compute_hvalid
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.memory_hSf
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.memory_hvalid
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.hfo_compute
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.hfo_memory
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.harity_compute
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.harity_memory
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.hFcommit_compute
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.hFcommit_memory
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.computeWalk_final_prob_of_acceptance
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.memoryWalk_final_prob_of_acceptance
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.memoryWalk_final_prob_of_acceptance_of_label
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.wrong_fanout_no_binding
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.s0_is_leaf
#print axioms Nock.NockVMROM.Thm54.SharedTableWalkRow.halt_is_leaf
