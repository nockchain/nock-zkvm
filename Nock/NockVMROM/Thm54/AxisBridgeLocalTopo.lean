/-
  Nock/NockVMROM/Thm54/AxisBridgeLocalTopo.lean

  M′'s β-free `FmemTopo`
  (`MemoryTopoBetaFree.lean`) therefore cannot feed `exactAxisBridgeLocal`.  This module is the
  additive twin:

  * `ExactAxisBridgeLocalTopo` — the same three fields, with `rvt : RVTWithArity FmemTopo`
    (`shared_inputs` and `fanout` are character-identical to the production fields);
  * `exactAxisBridgeLocalTopo` — the `exactAxisBridgeLocal` analogue, from the β-free topology
    `MemoryExactTopologyTopo` and the shared-inputs row fact `MemorySharedInputs` (the `.2.1`
    conjunct of `MemoryRowAccepted`, without its `Vmem` conjunct);
  * `exactAxisBridgeLocal_toTopo` — the production bridge implies the twin (the twin is no weaker as
    a consumer target), and `TraversableChainedSemanticExactLanguage.exactAxisBridgeLocalTopo`,
    the production language feeds the twin;
  * `exactAxisBridgeLocal_of_topo` — the converse, which needs exactly `interV` at every node
    (`verBool` is free, `MemoryTable.verBool_holds`).  That is the one β-dependent fact between
    the twin and the production bridge, and it is needed only to feed consumers still typed on
    `RVT Fmem`; the twin's own conclusion needs no β-dependent fact.

  The production `MemoryExactTopology` / `ExactAxisBridgeLocal` are not touched (route (ii) is
  out of scope).
-/
import Nock.NockVMROM.Thm54.AxisSoundness
import Nock.NockVMROM.Thm54.MemoryTopoBetaFree

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.AxisBridgeLocalTopo

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MemoryTopoBetaFree

/-! ## A. Generic: `RVT Fmem` versus `RVTWithArity FmemTopo` on one memory tree -/

section Tree
variable {K : Type} [Field K]

/-- `FmemTopo` at `⊥` children forces fanout `0`. -/
theorem fanoutMem_eq_zero_of_fmemTopo_none (lbl : MemoryTable.MState × MemoryTable.DTmem K)
    (h : FmemTopo lbl (fun _ => none)) : MemoryTable.fanoutMem lbl.1 = 0 := by
  have h0 := (h.2.2.1 ⟨0, by norm_num⟩)
  simp only [ne_eq, not_true_eq_false, iff_false, not_lt, Nat.le_zero] at h0
  exact h0

theorem fanoutMem_le_two (s : MemoryTable.MState) : MemoryTable.fanoutMem s ≤ 2 := by
  cases s <;> simp [MemoryTable.fanoutMem]

/-- **Production shape → twin shape, one tree.**  `RVT Fmem` plus the fanout binding gives
`RVTWithArity FmemTopo`: the per-node clause by `fmemTopo_of_fmem`, the leaf clause through the
fanout binding (`FmemTopo` at `⊥` forces fanout `0`), the arity from `fanoutMem ≤ 2`. -/
theorem rvtWithArity_topo_of_rvt_fmem (t : NTree (MemoryTable.MState × MemoryTable.DTmem K))
    (hrvt : RVT (MemoryTable.Fmem (K := K)) t)
    (hfan : ∀ t', InTree t t' →
      MemoryTable.fanoutMem (NTree.label t').1 = (NTree.children t').length) :
    RVTWithArity (FmemTopo (K := K)) t := by
  refine ⟨?_, ?_⟩
  · rw [RVT_iff_forall_InTree]
    intro s hs
    have hF := (RVT_iff_forall_InTree (MemoryTable.Fmem (K := K)) t).mp hrvt s hs
    refine ⟨fmemTopo_of_fmem _ _ hF.1, ⟨fun hleaf => fmemTopo_of_fmem _ _ (hF.2.mp hleaf), ?_⟩⟩
    intro hT
    have h0 := fanoutMem_eq_zero_of_fmemTopo_none _ hT
    rw [hfan s hs] at h0
    exact List.length_eq_zero_iff.mp h0
  · intro s hs
    rw [← hfan s hs]
    exact fanoutMem_le_two _

/-- **Twin shape → production shape, one tree: exactly `interV` is missing.**  `RVTWithArity
FmemTopo` plus `interV` at every node gives `RVT Fmem` (`verBool` holds definitionally,
`MemoryTable.verBool_holds`).  `interV` reads the inputs' `β` through `MemoryTable.pole`; it is the named β-dependent fact. -/
theorem rvt_fmem_of_rvtWithArity_topo (t : NTree (MemoryTable.MState × MemoryTable.DTmem K))
    (htopo : RVTWithArity (FmemTopo (K := K)) t)
    (hinter : ∀ t', InTree t t' →
      MemoryTable.interV (NTree.label t').2.1 (NTree.label t').2.2) :
    RVT (MemoryTable.Fmem (K := K)) t := by
  rw [RVT_iff_forall_InTree]
  intro s hs
  have hT := (RVT_iff_forall_InTree (FmemTopo (K := K)) t).mp htopo.1 s hs
  have hI := hinter s hs
  have up : ∀ xout, FmemTopo (NTree.label s) xout → MemoryTable.Fmem (NTree.label s) xout :=
    fun xout h => ⟨h.1, ⟨MemoryTable.verBool_holds _, h.2.1, hI⟩, h.2.2.1, h.2.2.2⟩
  refine ⟨up _ hT.1, ⟨fun hleaf => up _ (hT.2.mp hleaf), fun hF => hT.2.mpr
    (fmemTopo_of_fmem _ _ hF)⟩⟩

end Tree

/-! ## B. The twin structure and its source theorem -/

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]

/-- The β-free twin of `MemoryExactTopology`: exact arity-2 topology on every authoritative memory
root, on `FmemTopo` (no `Vmem`, no `interV`). -/
def MemoryExactTopologyTopo {cfg : ExactConfig F K} (exec : ExactExecution cfg) : Prop :=
  ∀ t ∈ exec.memoryForest, RVTWithArity (FmemTopo (K := K)) t

/-- The shared-inputs conjunct of `MemoryRowAccepted` alone (its `.2.1`), without `Vmem`. -/
def MemorySharedInputs {cfg : ExactConfig F K} (exec : ExactExecution cfg) : Prop :=
  ∀ row ∈ exec.memoryRows, row.2.1 = cfg.challenges.memoryInputs

/-- **The β-free twin of `ExactAxisBridgeLocal`.**  `shared_inputs` and `fanout` are the
production fields verbatim; `rvt` is `RVTWithArity FmemTopo` instead of `RVT Fmem`. -/
structure ExactAxisBridgeLocalTopo
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) (i : Fin cfg.kMem) : Prop where
  rvt : RVTWithArity (FmemTopo (K := K)) (exec.memoryTreeAt i)
  shared_inputs :
    ∀ t', InTree (exec.memoryTreeAt i) t' →
      (NTree.label t').2.1 = cfg.challenges.memoryInputs
  fanout :
    ∀ t', InTree (exec.memoryTreeAt i) t' →
      MemoryTable.fanoutMem (NTree.label t').1 = (NTree.children t').length

omit [Fintype K] [DecidableEq K] in
/-- `MemoryExactTopology.fanout_binding` on the β-free predicate (same proof through
`mem_stateSep_topo`). -/
theorem MemoryExactTopologyTopo.fanout_binding
    {forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))}
    (h : ∀ t ∈ forest, RVTWithArity (FmemTopo (K := K)) t) :
    ∀ t ∈ bfsForest forest,
      MemoryTable.fanoutMem t.label.1 = t.children.length := by
  intro t ht
  rw [mem_bfsForest] at ht
  obtain ⟨root, hroot, hin⟩ := ht
  exact fanout_eq_children_length_of_properArity
    (mem_stateSep_topo (K := K)) (h root hroot).1 (h root hroot).2 t hin

omit [Fintype K] [DecidableEq K] in
/-- **The `exactAxisBridgeLocal` analogue.**  Same conclusion shape as
`TraversableChainedSemanticExactLanguage.exactAxisBridgeLocal`, from the β-free topology and the
shared-inputs row fact; the proof is the production one with `mem_stateSep_topo`. -/
theorem exactAxisBridgeLocalTopo
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (htop : MemoryExactTopologyTopo exec) (hinp : MemorySharedInputs exec)
    (i : Fin cfg.kMem) :
    ExactAxisBridgeLocalTopo cfg exec i := by
  have hroot : exec.memoryTreeAt i ∈ exec.memoryForest := exec.memoryTreeAt_mem i
  refine ⟨htop _ hroot, ?_, ?_⟩
  · intro t' ht'
    have hglobal : t' ∈ bfsForest exec.memoryForest := by
      rw [mem_bfsForest]
      exact ⟨exec.memoryTreeAt i, hroot, ht'⟩
    exact hinp (NTree.label t') (by
      rw [ExactExecution.memoryRows]
      exact List.mem_map.mpr ⟨t', hglobal, rfl⟩)
  · intro t' ht'
    apply MemoryExactTopologyTopo.fanout_binding htop
    rw [mem_bfsForest]
    exact ⟨exec.memoryTreeAt i, hroot, ht'⟩

omit [Fintype K] [DecidableEq K] in
/-- `MemorySharedInputs` from the production row acceptance (its `.2.1`). -/
theorem memorySharedInputs_of_rowsAccepted
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : exec.MemoryRowsAccepted) : MemorySharedInputs exec :=
  fun row hrow => ((ExactExecution.memoryRowsAccepted_iff exec).1 h row hrow).2.1

/-! ## C. Receipts: the twin is no weaker than production; exactly `interV` separates them -/

/-- **Production bridge ⟹ twin.**  Every `ExactAxisBridgeLocal` is an `ExactAxisBridgeLocalTopo`
(same `shared_inputs`, same `fanout`; `rvt` through `rvtWithArity_topo_of_rvt_fmem`).  So any
consumer that can be stated against the twin is at least as widely applicable as one stated
against the production bridge. -/
theorem exactAxisBridgeLocal_toTopo
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    (h : ExactAxisBridgeLocal cfg exec i) : ExactAxisBridgeLocalTopo cfg exec i :=
  ⟨rvtWithArity_topo_of_rvt_fmem _ h.rvt h.fanout, h.shared_inputs, h.fanout⟩

theorem _root_.Nock.NockVMROM.Thm54.TraversableChainedSemanticExactLanguage.exactAxisBridgeLocalTopo
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : TraversableChainedSemanticExactLanguage cfg exec) (i : Fin cfg.kMem) :
    ExactAxisBridgeLocalTopo cfg exec i :=
  exactAxisBridgeLocal_toTopo (h.exactAxisBridgeLocal i)

/-- **Twin + `interV` ⟹ production bridge.**  The only datum the twin lacks for the production
bridge is `interV` at every node of the root.  A consumer typed on `ExactAxisBridgeLocal.rvt : RVT Fmem` can be fed
from the twin exactly when this fact is available. -/
theorem exactAxisBridgeLocal_of_topo
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    (h : ExactAxisBridgeLocalTopo cfg exec i)
    (hinter : ∀ t', InTree (exec.memoryTreeAt i) t' →
      MemoryTable.interV (NTree.label t').2.1 (NTree.label t').2.2) :
    ExactAxisBridgeLocal cfg exec i :=
  ⟨rvt_fmem_of_rvtWithArity_topo _ h.rvt hinter, h.shared_inputs, h.fanout⟩

end

end Nock.NockVMROM.Thm54.AxisBridgeLocalTopo

#print axioms Nock.NockVMROM.Thm54.AxisBridgeLocalTopo.rvtWithArity_topo_of_rvt_fmem
#print axioms Nock.NockVMROM.Thm54.AxisBridgeLocalTopo.rvt_fmem_of_rvtWithArity_topo
#print axioms Nock.NockVMROM.Thm54.AxisBridgeLocalTopo.exactAxisBridgeLocalTopo
#print axioms Nock.NockVMROM.Thm54.AxisBridgeLocalTopo.exactAxisBridgeLocal_toTopo
#print axioms Nock.NockVMROM.Thm54.AxisBridgeLocalTopo.exactAxisBridgeLocal_of_topo
#print axioms Nock.NockVMROM.Thm54.TraversableChainedSemanticExactLanguage.exactAxisBridgeLocalTopo
