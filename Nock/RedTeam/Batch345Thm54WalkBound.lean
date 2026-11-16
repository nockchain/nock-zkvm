/-
  Nock/RedTeam/Batch345Thm54WalkBound.lean

  **Walk bound vs topology event.**  Measure whether
  `NockVM.walkBad` is the projection of
  `specializedTopologyFailureEvent` / `topologyBadGammas` (already in
  `ProductionP8Containment.lean::FailureUnion`), or a separate summand.

  Verdict, compiled:

  * **Family-level, under binding: subsumed.**  At any
    `RawPlusIOSegmentedFamily` carrying `ComputeRowsAccepted` /
    `MemoryRowsAccepted` / `RawTopologyBindingResidual` — the hypotheses of
    `SharedTableWalkRow.lean::computeWalk_final_prob_of_acceptance` —
    `walkBad` and `topologyBadGammas` are both empty.  The inclusion
    `walkBad ⊆ topologyGammaLift` is therefore a corollary, and
    `walk_bounds` is `0 ≤ bound`.  No `walkFamily_problem` is used: the
    comparison is stated at one family.
  * **They are not the same event.**  `topologyBadGammas` is the `γ`-only RLC collision of *link payloads*
    (`Fin 9` / `Fin 5`).  Emptiness hypotheses differ (`ReconGoal` vs
    payload equality).
  * **Package-level vs `specializedTopologyFailureEvent`:** that event
    reads `topologyBadGammas` of the *coin-indexed*
    `(T.afterAlphaM z hz αM).familyData.base`
    (`TemplateRawJointSoundness.lean::mem_specializedTopologyFailureEvent_iff`).
    `walk_bounds` reads `walkBad` of the package's single `walkFamily`.
    The inclusion at a common family does
    **not** need that equality to be stated; the strategy-level
    identification does.
  * Instrument: `ℕ` arithmetic
    off `NodeEncoding.computeNode_width` and
    `RawTopologyRAP.lean::topologyWorkload`.
  * Figure delta landed: none.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.TraceGen.GenStackSeam
import Nock.NockVMROM.Thm54.RawTopologyRAP
import Nock.NockVMROM.Thm54.NodeEncoding
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch345

open Classical
open Nock Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SharedTableWalkRow
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.GenStackSeam

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## §A — the two events, at a common family

No `walkFamily_problem`.  `walkBad` is `Finset (K × K)`; `topologyBadGammas`
is `Finset K`.  The lift is the cylinder on the `γ` coordinate. -/

/-- Cylinder of `topologyBadGammas` in the walk chip's `(α, γ)` plane. -/
def topologyGammaLift (R : RawPlusIOSegmentedFamily F K)
    [Fintype K] [DecidableEq K] : Finset (K × K) :=
  Finset.univ.filter fun p => p.2 ∈ topologyBadGammas R

/-- The compute walk event `walk_bounds` prices, at an arbitrary family. -/
def familyComputeWalkBad (R : RawPlusIOSegmentedFamily F K)
    [Fintype K] [DecidableEq K] : Finset (K × K) :=
  NockVM.walkBad (ComputeTable.comp_stateSep (K := K)) R.compNodeEncode
    (computeRowLabel R) (computeChildLabel R)
    (foCol R.computeWalkRows) R.cfg.compRows

/-- The memory walk event (`Corr:forest`). -/
def familyMemoryWalkBad (R : RawPlusIOSegmentedFamily F K)
    [Fintype K] [DecidableEq K] : Finset (K × K) :=
  NockVM.walkBadForest (MemoryTable.mem_stateSep (K := K)) R.memNodeEncode
    (memoryRowLabel R) (memoryChildLabel R)
    (foCol R.memoryWalkRows) R.exec.memoryForest.length R.cfg.memRows

/-- `specializedTopologyFailureEvent` reads the *after-`alphaM`* family, not a
fixed `walkFamily`.  Compiled shape of the object mismatch. -/
theorem specializedTopologyFailureEvent_reads_afterAlphaM
    {p : ℕ} [CharP K p] (T : Strategy F K p) [Fintype K] [DecidableEq K]
    (ω : JointCoins K) (lmb : K) :
    ω ∈ specializedTopologyFailureEvent T lmb ↔
      ∃ hz : nprSeed ω ≠ 0,
        gamma ω ∈ topologyBadGammas
          (T.afterAlphaM (nprSeed ω) hz (alphaM ω) lmb).familyData.base :=
  mem_specializedTopologyFailureEvent_iff T lmb ω

/-- Honest-coin identification of the two families uses `walkFamily_problem`. -/
theorem honest_identification_uses_walkFamily_problem
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    specializedProblem P.optimized.verifier.raw.timestamp
        P.honestSeed P.honestSeed_ne P.honestAlpha P.optimized.objects.cfg.challenges.lam =
      P.walkFamily.problem :=
  package_honest_problem_eq P

/-! ## §B — both events empty under the walk-capstone hypotheses -/

theorem computePayload_eq_of_binding
    {t : NTree (ComputeTable.State × ComputeTable.DTcomp K)}
    (hb : RawComputeTopologyBinding t) (i : Fin 3)
    (hi : (i : ℕ) < ComputeTable.fanoutComp t.label.1) :
    computeActualPayload t i = computeExpectedPayload t i := by
  have hlink := hb.2 i hi
  unfold computeActualPayload computeExpectedPayload
  cases hc : t.childLabel i with
  | none =>
    simp only [hc, Option.map_none] at hlink
    exact absurd hlink (by simp)
  | some c =>
    simp only [hc, Option.map_some, Option.some.injEq] at hlink
    rw [← hlink]
    rfl

theorem memoryPayload_eq_of_binding
    {t : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hb : RawMemoryTopologyBinding t) (i : Fin 2)
    (hi : (i : ℕ) < MemoryTable.fanoutMem t.label.1) :
    memoryActualPayload t i = memoryExpectedPayload t i := by
  have hlink := hb.2 i hi
  unfold memoryActualPayload memoryExpectedPayload
  cases hc : t.childLabel i with
  | none =>
    simp only [hc, Option.map_none] at hlink
    exact absurd hlink (by simp)
  | some c =>
    simp only [hc, Option.map_some, Option.some.injEq] at hlink
    exact hlink

variable [Fintype K] [DecidableEq K]

theorem computeSlotBadGammas_empty_of_binding
    {t : NTree (ComputeTable.State × ComputeTable.DTcomp K)}
    (hb : RawComputeTopologyBinding t) (i : Fin 3) :
    computeSlotBadGammas t i = ∅ := by
  unfold computeSlotBadGammas
  split_ifs with hi hne
  · exact absurd (congrArg ComputeLinkPayload.encode
      (computePayload_eq_of_binding hb i hi)) hne
  · rfl
  · rfl

theorem memorySlotBadGammas_empty_of_binding
    {t : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hb : RawMemoryTopologyBinding t) (i : Fin 2) :
    memorySlotBadGammas t i = ∅ := by
  unfold memorySlotBadGammas
  split_ifs with hi hne
  · exact absurd (congrArg MemoryLinkPayload.encode
      (memoryPayload_eq_of_binding hb i hi)) hne
  · rfl
  · rfl

/-- Binding empties the topology `γ`-event.  Generic; the F97 namesake in
`MultiRootHonestArrays.lean` is the same proof at a fixture. -/
theorem topologyBadGammas_empty_of_binding
    (R : RawPlusIOSegmentedFamily F K) (h : RawTopologyBindingResidual R) :
    topologyBadGammas R = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro γ hγ
  rcases Finset.mem_union.1 hγ with hc | hm
  · obtain ⟨x, hx, hmem⟩ := Finset.mem_biUnion.1 hc
    have hk : x.1 < R.computeWalkRows.length :=
      Finset.mem_range.1 (Finset.mem_product.1 hx).1
    have hrow : R.computeWalkRows.getD x.1 R.exec.computeTree ∈ R.computeWalkRows := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      exact List.getElem_mem hk
    rw [computeSlotBadGammas_empty_of_binding (h.1 _ hrow) x.2] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  · obtain ⟨x, hx, hmem⟩ := Finset.mem_biUnion.1 hm
    have hk : x.1 < R.memoryWalkRows.length :=
      Finset.mem_range.1 (Finset.mem_product.1 hx).1
    have hrow :
        R.memoryWalkRows.getD x.1
            (R.exec.memoryForest.get
              ⟨0, List.length_pos_of_ne_nil R.exec.memoryForest_nonempty⟩) ∈
          R.memoryWalkRows := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      exact List.getElem_mem hk
    rw [memorySlotBadGammas_empty_of_binding (h.2 _ hrow) x.2] at hmem
    exact absurd hmem (Finset.notMem_empty _)

/-- `walkBad = ∅` from the walk-capstone hypotheses.  No encoder injectivity. -/
theorem familyComputeWalkBad_eq_empty_of_binding
    (R : RawPlusIOSegmentedFamily F K)
    (hc : R.exec.ComputeRowsAccepted) (hm : R.exec.MemoryRowsAccepted)
    (hbind : RawTopologyBindingResidual R) :
    familyComputeWalkBad R = ∅ :=
  (walkBads_eq_empty_of_binding R.compNodeEncode R.memNodeEncode
    (computeChildLabel R) (memoryChildLabel R)
    (foCol R.computeWalkRows) (foCol R.memoryWalkRows)
    R hc hm hbind).1

theorem familyMemoryWalkBad_eq_empty_of_binding
    (R : RawPlusIOSegmentedFamily F K)
    (hc : R.exec.ComputeRowsAccepted) (hm : R.exec.MemoryRowsAccepted)
    (hbind : RawTopologyBindingResidual R) :
    familyMemoryWalkBad R = ∅ :=
  (walkBads_eq_empty_of_binding R.compNodeEncode R.memNodeEncode
    (computeChildLabel R) (memoryChildLabel R)
    (foCol R.computeWalkRows) (foCol R.memoryWalkRows)
    R hc hm hbind).2

/-- **Compiled inclusion.**  Under the hypotheses that state `walk_bounds`,
`walkBad ⊆ topologyGammaLift`.  Both sides are empty. -/
theorem walkBad_subset_topologyEvent
    (R : RawPlusIOSegmentedFamily F K)
    (hc : R.exec.ComputeRowsAccepted) (hm : R.exec.MemoryRowsAccepted)
    (hbind : RawTopologyBindingResidual R) :
    familyComputeWalkBad R ⊆ topologyGammaLift R := by
  rw [familyComputeWalkBad_eq_empty_of_binding R hc hm hbind]
  exact Finset.empty_subset _

theorem walkBadForest_subset_topologyEvent
    (R : RawPlusIOSegmentedFamily F K)
    (hc : R.exec.ComputeRowsAccepted) (hm : R.exec.MemoryRowsAccepted)
    (hbind : RawTopologyBindingResidual R) :
    familyMemoryWalkBad R ⊆ topologyGammaLift R := by
  rw [familyMemoryWalkBad_eq_empty_of_binding R hc hm hbind]
  exact Finset.empty_subset _

/-- Binding empties the topology lift too: the inclusion is `∅ ⊆ ∅`. -/
theorem topologyGammaLift_eq_empty_of_binding
    (R : RawPlusIOSegmentedFamily F K) (hbind : RawTopologyBindingResidual R) :
    topologyGammaLift R = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro p hp
  have hγ : p.2 ∈ topologyBadGammas R := (Finset.mem_filter.mp hp).2
  rw [topologyBadGammas_empty_of_binding R hbind] at hγ
  exact absurd hγ (Finset.notMem_empty _)

/-! ## §C — `walk_bounds_of_containment`

The conjunct is `0 ≤ bound`, from emptiness, not from `Walk_IOP_final_prob`. -/

def familyComputeWalkBadRatio (R : RawPlusIOSegmentedFamily F K) : ℚ :=
  ((familyComputeWalkBad R).card : ℚ) /
    ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))

def familyComputeWalkBound (R : RawPlusIOSegmentedFamily F K) : ℚ :=
  (R.cfg.compRows : ℚ) / (Fintype.card K : ℚ) +
    ((R.cfg.compRows * (R.compNodeWidth - 1) : ℕ) : ℚ) /
      (Fintype.card K : ℚ)

def familyMemoryWalkBadRatio (R : RawPlusIOSegmentedFamily F K) : ℚ :=
  ((familyMemoryWalkBad R).card : ℚ) /
    ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))

def familyMemoryWalkBound (R : RawPlusIOSegmentedFamily F K) : ℚ :=
  (R.cfg.memRows : ℚ) / (Fintype.card K : ℚ) +
    ((R.cfg.memRows * (R.memNodeWidth - 1) : ℕ) : ℚ) /
      (Fintype.card K : ℚ)

theorem familyComputeWalkBadRatio_eq_zero_of_binding
    (R : RawPlusIOSegmentedFamily F K)
    (hc : R.exec.ComputeRowsAccepted) (hm : R.exec.MemoryRowsAccepted)
    (hbind : RawTopologyBindingResidual R) :
    familyComputeWalkBadRatio R = 0 := by
  rw [familyComputeWalkBadRatio, familyComputeWalkBad_eq_empty_of_binding R hc hm hbind]
  simp

theorem familyMemoryWalkBadRatio_eq_zero_of_binding
    (R : RawPlusIOSegmentedFamily F K)
    (hc : R.exec.ComputeRowsAccepted) (hm : R.exec.MemoryRowsAccepted)
    (hbind : RawTopologyBindingResidual R) :
    familyMemoryWalkBadRatio R = 0 := by
  rw [familyMemoryWalkBadRatio, familyMemoryWalkBad_eq_empty_of_binding R hc hm hbind]
  simp

/-- **`walk_bounds` at an arbitrary family**, from containment (binding +
row acceptance), not from Schwartz–Zippel. -/
theorem walk_bounds_of_containment
    (R : RawPlusIOSegmentedFamily F K)
    (hc : R.exec.ComputeRowsAccepted) (hm : R.exec.MemoryRowsAccepted)
    (hbind : RawTopologyBindingResidual R) :
    familyComputeWalkBadRatio R ≤ familyComputeWalkBound R ∧
      familyMemoryWalkBadRatio R ≤ familyMemoryWalkBound R := by
  have hcb : (0 : ℚ) ≤ familyComputeWalkBound R := by
    rw [familyComputeWalkBound]; positivity
  have hmb : (0 : ℚ) ≤ familyMemoryWalkBound R := by
    rw [familyMemoryWalkBound]; positivity
  exact ⟨by rw [familyComputeWalkBadRatio_eq_zero_of_binding R hc hm hbind]; exact hcb,
    by rw [familyMemoryWalkBadRatio_eq_zero_of_binding R hc hm hbind]; exact hmb⟩

/-- Independent of
`computeWalk_final_prob_of_acceptance`. -/
theorem package_walk_bounds_of_containment
    [CharP K (ringChar K)] [FiniteDimensional F K] {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    P.computeWalkBadRatio ≤ P.computeWalkBound ∧
      P.memoryWalkBadRatio ≤ P.memoryWalkBound :=
  package_walk_bounds_of_empty P

/-! ## §D — negative control: the walk majorant is not ≤ the topology summand

Instrument: `ℕ` comparison of the two numerators at the production widths.
`computeWalkBound` = `(N + N·(w−1)) / |𝕂|` with `w = 87`
(`NodeEncoding.lean::computeNode_width`).  Topology compute = `N · 3 · 8`
(`RawTopologyRAP.lean::topologyWorkload`). -/

theorem computeWalkBound_numerator_eq {N w : ℕ} (hw : 1 ≤ w) :
    N + N * (w - 1) = N * w := by
  have h : w - 1 + 1 = w := Nat.sub_add_cancel hw
  calc
    N + N * (w - 1) = N * 1 + N * (w - 1) := by ring
    _ = N * (1 + (w - 1)) := by ring
    _ = N * w := by rw [Nat.add_comm, h]

theorem production_computeWalk_numerator (N : ℕ) :
    N + N * (NodeEncoding.computeNodeWidth - 1) = N * 10 := by
  have hw : 1 ≤ NodeEncoding.computeNodeWidth := by
    rw [NodeEncoding.computeNode_width]; omega
  rw [computeWalkBound_numerator_eq hw, NodeEncoding.computeNode_width]

theorem topology_compute_numerator (N : ℕ) : N * 3 * 8 = N * 24 := by ring

theorem topology_full_numerator_at_eq_counts (N : ℕ) :
    N * 3 * 8 + N * 2 * 4 = N * 32 := by ring

/-- At the paper's label width
`10` it IS: `10 N ≤ 24 N`.  The walk's own `ε_RLC` summand is now dominated
by the topology summand it replaces (`Corr:forest`, `Thm:Walk_IOP`, `:966`). -/
theorem computeWalkBound_le_topologyCompute (N : ℕ) :
    N + N * (NodeEncoding.computeNodeWidth - 1) ≤ N * 3 * 8 := by
  rw [production_computeWalk_numerator, topology_compute_numerator]
  omega

theorem computeWalkBound_le_fullTopology_at_eq_counts (N : ℕ) :
    N + N * (NodeEncoding.computeNodeWidth - 1) ≤ N * 3 * 8 + N * 2 * 4 := by
  rw [production_computeWalk_numerator, topology_full_numerator_at_eq_counts]
  omega

theorem production_memoryWalk_numerator (M : ℕ) :
    M + M * (NodeEncoding.memoryNodeWidth - 1) = M * 6 := by
  have hw : 1 ≤ NodeEncoding.memoryNodeWidth := by
    rw [NodeEncoding.memoryNode_width]; omega
  rw [computeWalkBound_numerator_eq hw, NodeEncoding.memoryNode_width]

/-- At the paper's `x^mem` width
`6` it IS: `6 M ≤ 8 M`. -/
theorem memoryWalkBound_le_topologyMemory (M : ℕ) :
    M + M * (NodeEncoding.memoryNodeWidth - 1) ≤ M * 2 * 4 := by
  rw [production_memoryWalk_numerator]
  omega

/-! `computeWalk_final_prob_of_acceptance` needs three hypotheses besides the
family.  None is a field of `OptimizedProductionAcceptanceAt`. -/

/-- The production encoder is the `LT_comp` projection, injective on `computeLabelOf` (what the walk
binds) and on nothing more. -/
theorem production_compNodeEncode_labelOf
    (hchar : NodeEncoding.StateTagChar K) :
    ∀ a b, NodeEncoding.computeNodeEncode (K := K) hchar a =
        NodeEncoding.computeNodeEncode hchar b →
      ComputeTable.computeLabelOf a = ComputeTable.computeLabelOf b :=
  fun _ _ h => NodeEncoding.computeNodeEncode_labelOf_eq hchar h

/-- The production memory encoder is the `x^mem` projection, injective on
`memoryLabelOf` (what the walk binds) and on nothing more. -/
theorem production_memNodeEncode_labelOf
    (hchar : NodeEncoding.StateTagChar K) :
    ∀ a b, NodeEncoding.memoryNodeEncode (K := K) hchar a =
        NodeEncoding.memoryNodeEncode hchar b →
      MemoryTable.memoryLabelOf a = MemoryTable.memoryLabelOf b :=
  fun _ _ h => NodeEncoding.memoryNodeEncode_labelOf_eq hchar h

/-- (2) `ComputeRowsAccepted` is `Vcomp` on `ExactExecution.computeRows`
(`Language.lean::ComputeRowsAccepted`).  Deployed acceptance is
`RAP.SatisfiesWithPreprocessing` on traces. -/
theorem computeRowsAccepted_is_Vcomp_on_bfs
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.ComputeRowsAccepted ↔
      ∀ row ∈ exec.computeRows, ExactExecution.ComputeRowAccepted cfg row :=
  ExactExecution.computeRowsAccepted_iff exec

/-- (3) `RawTopologyBindingResidual` is the local parent-child link
(`RawTopologySoundness.lean::RawTopologyBindingResidual`). -/
theorem topologyBinding_of_compressedCheck_outside_bad
    (hchar : NodeEncoding.StateTagChar K)
    (R : RawPlusIOSegmentedFamily F K) (γ : K)
    (hcheck : TopologyCompressedCheck R γ)
    (hγ : γ ∉ topologyBadGammas R) :
    RawTopologyBindingResidual R :=
  rawTopologyBindingResidual_of_compressedCheck hchar R γ hcheck hγ

/-- Replay `walk_bounds_of_containment` at
`strategyOfTraces Qc Qm`'s family by discharging `ComputeRowsAccepted`,
`MemoryRowsAccepted`, `RawTopologyBindingResidual`. -/
theorem h14_must_discharge_walk_hyps
    (R : RawPlusIOSegmentedFamily F K)
    (hc : R.exec.ComputeRowsAccepted) (hm : R.exec.MemoryRowsAccepted)
    (hbind : RawTopologyBindingResidual R) :
    familyComputeWalkBadRatio R ≤ familyComputeWalkBound R ∧
      familyMemoryWalkBadRatio R ≤ familyMemoryWalkBound R :=
  walk_bounds_of_containment R hc hm hbind

end

end Nock.RedTeam.Batch345

#print axioms Nock.RedTeam.Batch345.walkBad_subset_topologyEvent
#print axioms Nock.RedTeam.Batch345.walk_bounds_of_containment
#print axioms Nock.RedTeam.Batch345.package_walk_bounds_of_containment
#print axioms Nock.RedTeam.Batch345.computeWalkBound_le_topologyCompute
#print axioms Nock.RedTeam.Batch345.computeWalkBound_le_fullTopology_at_eq_counts
#print axioms Nock.RedTeam.Batch345.memoryWalkBound_le_topologyMemory
#print axioms Nock.RedTeam.Batch345.specializedTopologyFailureEvent_reads_afterAlphaM
#print axioms Nock.RedTeam.Batch345.honest_identification_uses_walkFamily_problem
#print axioms Nock.RedTeam.Batch345.h14_must_discharge_walk_hyps
