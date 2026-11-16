import Nock.NockVMROM.Thm54.RawVerifier

/-!
# Exact raw-verifier topology seam

The current walk trace derives `cur`, `chld`, and `fo` from the same stored tree/forest.  Its AIR
checks the resulting scalar BFS multiset recurrence, but it has no column or constraint comparing:

* the real child count with `fanoutComp` / `fanoutMem` of the row state; or
* an active child's `(s,f,e)` / `pt` payload with the parent `sfTriple` / `lc,rc` payload.

Consequently canonical injective node encoding removes encoder substitution, but does not create
the absent expected-label comparison.  The residual below is exactly that local relation: it
contains no `Vcomp`, `Vmem`, `Fcomp`, `Fmem`, `RVT`, semantic target, evaluator, or StepROM fact.

Once the residual is supplied, the canonical row predicates derived in `RawVerifier` assemble it
to the exact production `RVTWithArity Fcomp/Fmem` targets.  Conversely those targets imply the
residual, so the seam is neither weaker prose nor a disguised semantic assumption.
-/

namespace Nock.NockVMROM.Thm54

open Classical
open Nock Nock.Walk

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {p : ℕ} [CharP K p]

/-- The exact compute-side local relation missing from the current walk AIR. -/
def RawComputeTopologyBinding
    (t : NTree (ComputeTable.State × ComputeTable.DTcomp K)) : Prop :=
  ComputeTable.fanoutComp t.label.1 = t.children.length ∧
    ComputeTable.childLinkComp t.label (fun j => t.childLabel j)

/-- The exact memory-side local relation missing from the current walk AIR. -/
def RawMemoryTopologyBinding
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K)) : Prop :=
  MemoryTable.fanoutMem t.label.1 = t.children.length ∧
    MemoryTable.childLinkMem t.label (fun j => t.childLabel j)

/-- Only the unverified local topology linkage, over every authoritative aggregate BFS row. -/
def RawTopologyBindingResidual (R : RawPlusIOSegmentedFamily F K) : Prop :=
  (∀ t ∈ R.computeWalkRows, RawComputeTopologyBinding t) ∧
    (∀ t ∈ R.memoryWalkRows, RawMemoryTopologyBinding t)

private theorem computeStructure_of_binding
    (tree : NTree (ComputeTable.State × ComputeTable.DTcomp K))
    (hbind : ∀ t ∈ bfsForest [tree], RawComputeTopologyBinding t) :
    RVTWithArity (ComputeTreeStructure (K := K)) tree := by
  have hrvt : RVT (ComputeTreeStructure (K := K)) tree := by
    apply (RVT_iff_forall_InTree (ComputeTreeStructure (K := K)) tree).2
    intro t ht
    have htmem : t ∈ bfsForest [tree] := by
      rw [mem_bfsForest]
      exact ⟨tree, by simp, ht⟩
    obtain ⟨hfan, hlink⟩ := hbind t htmem
    refine ⟨⟨?_, hlink⟩, ?_⟩
    · intro i
      rw [childLabel_ne_none_iff]
      omega
    · constructor
      · intro hleaf
        have hlen : t.children.length = 0 := by
          simpa [NTree.isLeaf] using congrArg List.length hleaf
        have hfan0 : ComputeTable.fanoutComp t.label.1 = 0 := hfan.trans hlen
        refine ⟨?_, ?_⟩
        · intro i
          constructor
          · intro hi
            rw [hfan0] at hi
            omega
          · intro hne
            exact False.elim (hne rfl)
        · intro i hi
          rw [hfan0] at hi
          omega
      · intro hnone
        have hfan0 : ComputeTable.fanoutComp t.label.1 = 0 := by
          by_contra hne
          have hpos : 0 < ComputeTable.fanoutComp t.label.1 :=
            Nat.pos_of_ne_zero hne
          have hslot := hnone.1 (0 : Fin 3)
          simp only [ne_eq, not_true_eq_false, iff_false, not_lt] at hslot
          omega
        unfold NTree.isLeaf
        apply List.eq_nil_of_length_eq_zero
        omega
  refine ⟨hrvt, ?_⟩
  intro t ht
  have htmem : t ∈ bfsForest [tree] := by
    rw [mem_bfsForest]
    exact ⟨tree, by simp, ht⟩
  calc
    t.children.length = ComputeTable.fanoutComp t.label.1 := (hbind t htmem).1.symm
    _ ≤ 3 := (ComputeTable.comp_stateSep (K := K)).fanout_le t.label.1

private theorem memoryStructure_of_binding
    (tree : NTree (MemoryTable.MState × MemoryTable.DTmem K))
    (hbind : ∀ t ∈ bfsForest [tree], RawMemoryTopologyBinding t) :
    RVTWithArity (MemoryTreeStructure (K := K)) tree := by
  have hrvt : RVT (MemoryTreeStructure (K := K)) tree := by
    apply (RVT_iff_forall_InTree (MemoryTreeStructure (K := K)) tree).2
    intro t ht
    have htmem : t ∈ bfsForest [tree] := by
      rw [mem_bfsForest]
      exact ⟨tree, by simp, ht⟩
    obtain ⟨hfan, hlink⟩ := hbind t htmem
    refine ⟨⟨?_, hlink⟩, ?_⟩
    · intro i
      rw [childLabel_ne_none_iff]
      omega
    · constructor
      · intro hleaf
        have hlen : t.children.length = 0 := by
          simpa [NTree.isLeaf] using congrArg List.length hleaf
        have hfan0 : MemoryTable.fanoutMem t.label.1 = 0 := hfan.trans hlen
        refine ⟨?_, ?_⟩
        · intro i
          constructor
          · intro hi
            rw [hfan0] at hi
            omega
          · intro hne
            exact False.elim (hne rfl)
        · intro i hi
          rw [hfan0] at hi
          omega
      · intro hnone
        have hfan0 : MemoryTable.fanoutMem t.label.1 = 0 := by
          by_contra hne
          have hpos : 0 < MemoryTable.fanoutMem t.label.1 :=
            Nat.pos_of_ne_zero hne
          have hslot := hnone.1 (0 : Fin 2)
          simp only [ne_eq, not_true_eq_false, iff_false, not_lt] at hslot
          omega
        unfold NTree.isLeaf
        apply List.eq_nil_of_length_eq_zero
        omega
  refine ⟨hrvt, ?_⟩
  intro t ht
  have htmem : t ∈ bfsForest [tree] := by
    rw [mem_bfsForest]
    exact ⟨tree, by simp, ht⟩
  calc
    t.children.length = MemoryTable.fanoutMem t.label.1 := (hbind t htmem).1.symm
    _ ≤ 2 := (MemoryTable.mem_stateSep (K := K)).fanout_le t.label.1

/-- Canonically accepted rows plus the exact local compute linkage yield production
`RVTWithArity Fcomp` on the authoritative compute tree. -/
theorem computeExactTopology_of_rowsAccepted_and_binding
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hrows : exec.ComputeRowsAccepted)
    (hbind : ∀ t ∈ bfsForest [exec.computeTree], RawComputeTopologyBinding t) :
    ComputeExactTopology exec := by
  have hstructure := computeStructure_of_binding exec.computeTree hbind
  refine ⟨(rvt_fcomp_iff_structure_and_rows exec.computeTree).2
    ⟨hstructure.1, ?_⟩, hstructure.2⟩
  intro node hnode
  have hlabel : node.label ∈ exec.computeRows := by
    exact List.mem_map.mpr ⟨node, hnode, rfl⟩
  have hrow :=
    (ExactExecution.computeRowsAccepted_iff exec).1 hrows node.label hlabel
  exact ⟨hrow.1, hrow.2.2⟩

/-- Canonically accepted rows plus the exact local memory linkage yield production
`RVTWithArity Fmem` on every authoritative memory root. -/
theorem memoryExactTopology_of_rowsAccepted_and_binding
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hrows : exec.MemoryRowsAccepted)
    (hbind : ∀ t ∈ bfsForest exec.memoryForest, RawMemoryTopologyBinding t) :
    MemoryExactTopology exec := by
  intro root hroot
  have hrootBind :
      ∀ t ∈ bfsForest [root], RawMemoryTopologyBinding t := by
    intro t ht
    apply hbind t
    rw [mem_bfsForest] at ht ⊢
    obtain ⟨r, hr, hin⟩ := ht
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨root, hroot, hin⟩
  have hstructure := memoryStructure_of_binding root hrootBind
  refine ⟨(rvt_fmem_iff_structure_and_rows root).2
    ⟨hstructure.1, ?_⟩, hstructure.2⟩
  intro node hnode
  have hnodeAll : node ∈ bfsForest exec.memoryForest := by
    rw [mem_bfsForest] at hnode ⊢
    obtain ⟨r, hr, hin⟩ := hnode
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨root, hroot, hin⟩
  have hlabel : node.label ∈ exec.memoryRows :=
    List.mem_map.mpr ⟨node, hnodeAll, rfl⟩
  have hrow :=
    (ExactExecution.memoryRowsAccepted_iff exec).1 hrows node.label hlabel
  exact ⟨hrow.1, hrow.2.2.1⟩

/-- All derivations surrounding the missing local seam are complete: raw acceptance supplies the
canonical row predicates, and the residual supplies only fanout/child-content linkage. -/
theorem RawMessage.exactTopology_of_accepts_and_binding
    {R : RawPlusIOSegmentedFamily F K}
    {claim : P8PublicClaim} {ω : JointCoins K}
    (M : RawMessage R p) (hchar : NodeEncoding.StateTagChar K)
    (hlam : ∀ i, (R.exec.memoryPubAt i).lambda = R.cfg.challenges.lam)
    (haccept : M.Accepts claim ω)
    (hbind : RawTopologyBindingResidual R) :
    ComputeExactTopology R.exec ∧ MemoryExactTopology R.exec := by
  constructor
  · apply computeExactTopology_of_rowsAccepted_and_binding
      (M.computeRowsAccepted_of_accepts hchar haccept)
    simpa [RawTopologyBindingResidual, RawPlusIOSegmentedFamily.computeWalkRows] using hbind.1
  · apply memoryExactTopology_of_rowsAccepted_and_binding
      (M.memoryRowsAccepted_of_accepts hchar hlam haccept)
    simpa [RawTopologyBindingResidual, RawPlusIOSegmentedFamily.memoryWalkRows] using hbind.2

/-- Production exact topology implies the compute half of the residual. -/
theorem computeBinding_of_exactTopology
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (htop : ComputeExactTopology exec) :
    ∀ t ∈ bfsForest [exec.computeTree], RawComputeTopologyBinding t := by
  intro t ht
  have hin : InTree exec.computeTree t := by
    rw [mem_bfsForest] at ht
    obtain ⟨root, hroot, hin⟩ := ht
    simp only [List.mem_singleton] at hroot
    subst root
    exact hin
  have hF :=
    ((RVT_iff_forall_InTree (ComputeTable.Fcomp (K := K)) exec.computeTree).1
      htop.1 t hin).1
  exact
    ⟨fanout_eq_children_length_of_properArity
      (ComputeTable.comp_stateSep (K := K)) htop.1 htop.2 t hin,
      hF.2.2.2⟩

/-- Production exact topology implies the memory half of the residual. -/
theorem memoryBinding_of_exactTopology
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (htop : MemoryExactTopology exec) :
    ∀ t ∈ bfsForest exec.memoryForest, RawMemoryTopologyBinding t := by
  intro t ht
  rw [mem_bfsForest] at ht
  obtain ⟨root, hroot, hin⟩ := ht
  have hrootTop := htop root hroot
  have hF :=
    ((RVT_iff_forall_InTree (MemoryTable.Fmem (K := K)) root).1
      hrootTop.1 t hin).1
  exact
    ⟨fanout_eq_children_length_of_properArity
      (MemoryTable.mem_stateSep (K := K)) hrootTop.1 hrootTop.2 t hin,
      hF.2.2.2⟩

/-- Exact characterization of the remaining seam once canonical row acceptance is known. -/
theorem exactTopology_iff_rawTopologyBindingResidual_of_rowsAccepted
    (R : RawPlusIOSegmentedFamily F K)
    (hcomp : R.exec.ComputeRowsAccepted)
    (hmem : R.exec.MemoryRowsAccepted) :
    (ComputeExactTopology R.exec ∧ MemoryExactTopology R.exec) ↔
      RawTopologyBindingResidual R := by
  constructor
  · rintro ⟨hc, hm⟩
    constructor
    · simpa [RawPlusIOSegmentedFamily.computeWalkRows] using
        computeBinding_of_exactTopology hc
    · simpa [RawPlusIOSegmentedFamily.memoryWalkRows] using
        memoryBinding_of_exactTopology hm
  · intro hbind
    constructor
    · apply computeExactTopology_of_rowsAccepted_and_binding hcomp
      simpa [RawTopologyBindingResidual, RawPlusIOSegmentedFamily.computeWalkRows] using hbind.1
    · apply memoryExactTopology_of_rowsAccepted_and_binding hmem
      simpa [RawTopologyBindingResidual, RawPlusIOSegmentedFamily.memoryWalkRows] using hbind.2

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.RawMessage.exactTopology_of_accepts_and_binding
#print axioms Nock.NockVMROM.Thm54.computeBinding_of_exactTopology
#print axioms Nock.NockVMROM.Thm54.memoryBinding_of_exactTopology
#print axioms Nock.NockVMROM.Thm54.exactTopology_iff_rawTopologyBindingResidual_of_rowsAccepted
