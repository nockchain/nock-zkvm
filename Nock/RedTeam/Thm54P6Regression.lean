import Nock.NockVMROM.Thm54.ExactTraversal
import Nock.RedTeam.Thm54P3Nonvacuity

/-!
It imports production from scratch, never the reverse.
-/

open scoped Classical

namespace Nock.RedTeam.Thm54P6Regression

open Nock Nock.Walk Nock.NockVMROM.Thm54
open Nock.RedTeam.Thm54P3Nonvacuity

noncomputable section

abbrev K17 := Nock.RedTeam.Thm54P2Nonvacuity.K17

theorem computeTree_properArity :
    ProperArity 3 Nock.RedTeam.Thm54P2Nonvacuity.computeTree := by
  simp [Nock.RedTeam.Thm54P2Nonvacuity.computeTree, properArity_node_iff]

theorem tailTreeP3_properArity :
    ProperArity 2 tailTreeP3 := by
  simp [tailTreeP3, properArity_node_iff]

theorem verifyTree_properArity :
    ProperArity 2 verifyTree := by
  simp [verifyTree, tailTreeP3, properArity_node_iff]

theorem headTreeP3_properArity :
    ProperArity 2 headTreeP3 := by
  simp [headTreeP3, properArity_node_iff]

theorem decompTreeP3_properArity :
    ProperArity 2 decompTreeP3 := by
  simp [decompTreeP3, headTreeP3, verifyTree, tailTreeP3, properArity_node_iff]

theorem readTreeP3_properArity :
    ProperArity 2 readTreeP3 := by
  simp [readTreeP3, decompTreeP3, headTreeP3, verifyTree, tailTreeP3,
    properArity_node_iff]

theorem dummyTree_properArity :
    ProperArity 2 dummyTree := by
  simp [dummyTree, properArity_node_iff]

theorem production_compute_topology :
    ComputeExactTopology exec :=
  ⟨Nock.RedTeam.Thm54P2Nonvacuity.computeTree_rvt, computeTree_properArity⟩

theorem production_compute_public_topology :
    ComputePublicExactTopology exec.computePublicTree :=
  exec.computePublicExactTopology production_compute_topology

theorem production_memory_topology :
    MemoryExactTopology exec := by
  intro t ht
  change t ∈ [dummyTree, readTreeP3] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact ⟨dummyTree_rvt, dummyTree_properArity⟩
  · exact ⟨readTree_rvt_p3, readTreeP3_properArity⟩

theorem production_traversable_chained :
    TraversableChainedSemanticExactLanguage cfg exec where
  chained := production_chained
  compute_topology := production_compute_topology
  memory_topology := production_memory_topology

def acceptedExecutionP6 : TraversableChainedAcceptedExecution cfg :=
  ⟨exec, production_traversable_chained⟩

/-- The cumulative exact package projects to the independent public compute statement language. -/
def productionComputePublicAccepted : ComputePublicAcceptedLanguage K17 :=
  production_traversable_chained.computePublicAccepted

/-- The cumulative exact package projects to the independent ordered memory statement language. -/
def productionMemoryPublicAccepted : MemoryPublicAcceptedLanguage cfg :=
  production_traversable_chained.memoryPublicAccepted

/-- Both independent public component statements for the balanced witness. -/
def productionPublicAcceptedComponents : PacketLocalPublicAcceptedLanguage cfg :=
  production_traversable_chained.publicAcceptedComponents

/-- The one-factor compute product is genuinely public; the Dec-bearing tree occurs only inside
the existential topology proof. -/
def productionComputePublicRVTProduct : ComputePublicExactRVTProduct K17 :=
  computePublicTraversalEquiv K17 productionComputePublicAccepted

/-- The ordered two-root memory product obtained by the pure memory component bijection. -/
def productionMemoryRVTProduct : MemoryExactRVTProduct cfg :=
  memoryPublicTraversalEquiv cfg exec.memoryRootCount_pos productionMemoryPublicAccepted

/-- The packet-local paper result maps the two public statements to the two pure RVT products. -/
def productionPacketLocalRVTProducts : PacketLocalExactRVTProducts cfg :=
  packetLocalDefTraversableEquiv cfg exec.memoryRootCount_pos productionPublicAcceptedComponents

/-- The committed public tree and row readout are exactly aligned to the authoritative private
tree and its separate decided-column witness rows. -/
theorem production_public_private_alignment :
    ComputeTreeWitnessAligned exec.computePublicTree exec.computeTree ∧
      ComputeReadoutWitnessAligned
        exec.computePublicRows exec.computeDecRows exec.computeRows :=
  ⟨exec.computePublicTree_witnessAligned, exec.computeReadout_witnessAligned⟩

/-- Its exact root products are inhabited with one PUBLIC compute factor and two memory factors. -/
theorem production_rvt_products_nonempty :
    Nonempty (ComputePublicExactRVTProduct K17) ∧
      Nonempty (MemoryExactRVTProduct cfg) := by
  exact ⟨⟨productionComputePublicRVTProduct⟩, ⟨productionMemoryRVTProduct⟩⟩

theorem production_literal_traversal_clauses :
    ComputeExactTraversalClause exec ∧ MemoryExactTraversalClause exec :=
  ⟨(computeExactTopology_iff_traversalClause exec).1 production_compute_topology,
    (memoryExactTopology_iff_traversalClause exec).1 production_memory_topology⟩

/-- Concrete static root counts: one compute root and exactly the two committed memory roots. -/
theorem production_root_counts :
    exactCompRoots cfg = 1 ∧
      exactMemRoots cfg = 2 ∧
      exec.memoryForest.length = exactMemRoots cfg := by
  norm_num [exactCompRoots, exactMemRoots, cfg, exec]

theorem production_public_readout_not_empty :
    exec.computePublicRows ≠ [] :=
  legacy_empty_singleton_readout_mismatch_cannot_inhabit acceptedExecutionP6

/-- Regression: both pure component equivalences satisfy literal round-trips on the balanced
witness, without carrying the source execution in either target. -/
theorem production_inverse_roundtrips :
    (computePublicTraversalEquiv K17).symm productionComputePublicRVTProduct =
        productionComputePublicAccepted ∧
      (memoryPublicTraversalEquiv cfg exec.memoryRootCount_pos).symm
          productionMemoryRVTProduct = productionMemoryPublicAccepted := by
  constructor
  · exact (computePublicTraversalEquiv K17).left_inv _
  · exact (memoryPublicTraversalEquiv cfg exec.memoryRootCount_pos).left_inv _

/-- The paired packet-local equivalence also round-trips the two independent public statements. -/
theorem production_packet_local_roundtrip :
    (packetLocalDefTraversableEquiv cfg exec.memoryRootCount_pos).symm
        productionPacketLocalRVTProducts = productionPublicAcceptedComponents :=
  (packetLocalDefTraversableEquiv cfg exec.memoryRootCount_pos).left_inv _

/-! ## Adversarial accepted-row regressions -/

def badComputeInputs : ComputeTable.Inputs K17 :=
  { Nock.RedTeam.Thm54P2Nonvacuity.cInp with α := 0 }

def badComputeRows : List (ComputePublicLabel K17) :=
  [(.s1, (badComputeInputs, Nock.RedTeam.Thm54P2Nonvacuity.cPub))]

theorem badComputeInputs_no_Vcomp (dec : ComputeTable.Dec K17) :
    ¬ ComputeTable.Vcomp badComputeInputs
      Nock.RedTeam.Thm54P2Nonvacuity.cPub dec := by
  intro h
  have ht := congrArg (fun mr : ComputeTable.MemRec K17 => mr.ts) h.2.1
  norm_num [badComputeInputs, Nock.RedTeam.Thm54P2Nonvacuity.cPub,
    Nock.RedTeam.Thm54P2Nonvacuity.sharedRecord] at ht
  exact (by decide : (4 : K17) ≠ 0) ht

theorem badComputeRows_leaf_shaped :
    ComputeTable.fanoutComp (badComputeRows[0]'(by simp [badComputeRows])).1 = 0 := by
  rfl

theorem badComputeRows_valid_one_root_layout :
    BFSValidF 1 (fun _ => 0) badComputeRows.length ∧
      1 + Sf (fun _ => 0) badComputeRows.length = badComputeRows.length := by
  constructor
  · intro i hi hih
    simp [badComputeRows, Sf] at hih ⊢
    omega
  · norm_num [badComputeRows, Sf]

def badComputePrivateLabel :
    ComputeTable.State × ComputeTable.DTcomp K17 :=
  (.s1, (badComputeInputs, Nock.RedTeam.Thm54P2Nonvacuity.cPub,
    Nock.RedTeam.Thm54P2Nonvacuity.cDec))

def badComputeStructureTree :
    NTree (ComputeTable.State × ComputeTable.DTcomp K17) :=
  .node badComputePrivateLabel []

theorem badComputeStructureTree_rvt :
    RVT (ComputeTreeStructure (K := K17)) badComputeStructureTree := by
  unfold badComputeStructureTree RVT
  have hstruct :
      ComputeTreeStructure badComputePrivateLabel (fun _ => none) := by
    constructor
    · intro i
      simp [badComputePrivateLabel, ComputeTreeStructure, ComputeTable.fanoutComp]
    · intro i hi
      simp [badComputePrivateLabel, ComputeTable.childLinkComp,
        ComputeTable.fanoutComp] at hi
  exact ⟨hstruct, by simp, ⟨fun _ => hstruct, fun _ => rfl⟩⟩

theorem badComputeStructureTree_arity :
    ProperArity 3 badComputeStructureTree := by
  simp [badComputeStructureTree, properArity_node_iff]

theorem badComputeStructuralWitness :
    Nonempty (ComputePublicRowsTreeWitness badComputeRows
      [Nock.RedTeam.Thm54P2Nonvacuity.cDec]) := by
  refine ⟨⟨badComputeStructureTree, ?_, ?_,
    ⟨badComputeStructureTree_rvt, badComputeStructureTree_arity⟩, ?_⟩⟩
  · simp [badComputeStructureTree, badComputePrivateLabel, badComputeRows,
      bfsForest, computePublicLabel]
  · simp [badComputeStructureTree, badComputePrivateLabel, bfsForest, computeWitnessDec]
  · intro node hnode
    have hnode' : node = badComputeStructureTree := by
      simpa [badComputeStructureTree, bfsForest] using hnode
    subst node
    rfl

theorem badComputeRows_not_accepted :
    ¬ ComputePublicRowsAccepted badComputeRows := by
  rintro ⟨witness⟩
  let decs := witness.1
  have hlen := witness.2.1
  have hrows := witness.2.2.1
  have hlen' : decs.length = 1 := by simpa [badComputeRows] using hlen
  obtain ⟨dec, hdecs⟩ := List.length_eq_one_iff.mp hlen'
  change witness.1 = [dec] at hdecs
  rw [hdecs] at hrows
  have hrow :
      ComputePublicRowAccepted
        (.s1, (badComputeInputs, Nock.RedTeam.Thm54P2Nonvacuity.cPub)) dec := by
    simpa [badComputeRows] using hrows
  exact badComputeInputs_no_Vcomp dec hrow.2

theorem badComputeStructure_not_equivalent_to_acceptance :
    ¬ (ComputePublicRowsAccepted badComputeRows ↔
      ∃ decs, Nonempty (ComputePublicRowsTreeWitness badComputeRows decs)) := by
  intro hiff
  apply badComputeRows_not_accepted
  exact hiff.mpr
    ⟨[Nock.RedTeam.Thm54P2Nonvacuity.cDec], badComputeStructuralWitness⟩

def badMemoryInputs : MemoryTable.Inputs K17 :=
  { Nock.RedTeam.Thm54P2Nonvacuity.mInp with z := 0 }

def badMemoryRows :
    List (MemoryTable.MState × MemoryTable.DTmem K17) :=
  [(.halt, (badMemoryInputs, pDummy)), (.halt, (badMemoryInputs, pDummy))]

theorem badMemoryInputs_no_Vmem :
    ¬ MemoryTable.Vmem badMemoryInputs pDummy := by
  intro h
  have hz := h.2.1.1
  norm_num [badMemoryInputs, pDummy, Nock.RedTeam.Thm54P2Nonvacuity.headCell,
    Nock.RedTeam.Thm54P2Nonvacuity.headFP] at hz

theorem badMemoryRows_leaf_shaped :
    MemoryTable.fanoutMem (badMemoryRows[0]'(by simp [badMemoryRows])).1 = 0 := by
  rfl

theorem badMemoryRows_valid_configured_root_layout :
    badMemoryRows.length = cfg.kMem ∧
      BFSValidF cfg.kMem (fun _ => 0) badMemoryRows.length ∧
      cfg.kMem + Sf (fun _ => 0) badMemoryRows.length = badMemoryRows.length := by
  norm_num [badMemoryRows, cfg, BFSValidF, Sf]

def badMemoryStructureLabel :
    MemoryTable.MState × MemoryTable.DTmem K17 :=
  (.halt, (badMemoryInputs, pDummy))

def badMemoryStructureTree :
    NTree (MemoryTable.MState × MemoryTable.DTmem K17) :=
  .node badMemoryStructureLabel []

def badMemoryStructureForest :
    List (NTree (MemoryTable.MState × MemoryTable.DTmem K17)) :=
  [badMemoryStructureTree, badMemoryStructureTree]

theorem badMemoryStructureTree_rvt :
    RVT (MemoryTreeStructure (K := K17)) badMemoryStructureTree := by
  unfold badMemoryStructureTree RVT
  have hstruct :
      MemoryTreeStructure badMemoryStructureLabel (fun _ => none) := by
    constructor
    · intro i
      simp [badMemoryStructureLabel, MemoryTreeStructure, MemoryTable.fanoutMem]
    · intro i hi
      simp [badMemoryStructureLabel, MemoryTable.childLinkMem,
        MemoryTable.fanoutMem] at hi
  exact ⟨hstruct, by simp, ⟨fun _ => hstruct, fun _ => rfl⟩⟩

theorem badMemoryStructureTree_arity :
    ProperArity 2 badMemoryStructureTree := by
  simp [badMemoryStructureTree, properArity_node_iff]

theorem badMemoryStructuralWitness :
    Nonempty (MemoryPublicRowsForestWitness cfg badMemoryRows) := by
  refine ⟨⟨badMemoryStructureForest, ?_, by simp [badMemoryStructureForest],
    ?_, ?_, ?_⟩⟩
  · norm_num [badMemoryStructureForest, cfg]
  · intro t ht
    simp only [badMemoryStructureForest, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨badMemoryStructureTree_rvt, badMemoryStructureTree_arity⟩
    · exact ⟨badMemoryStructureTree_rvt, badMemoryStructureTree_arity⟩
  · intro node hnode
    have hnode' : node = badMemoryStructureTree := by
      simpa [badMemoryStructureForest, badMemoryStructureTree, bfsForest] using hnode
    subst node
    rfl
  · simp [badMemoryStructureForest, badMemoryStructureTree, badMemoryStructureLabel,
      badMemoryRows, bfsForest]

theorem badMemoryRows_not_accepted :
    ¬ MemoryPublicRowsAccepted cfg badMemoryRows := by
  rintro ⟨_, hrows⟩
  have hrow :
      MemoryPublicRowAccepted (.halt, (badMemoryInputs, pDummy)) := by
    exact hrows.1
  exact badMemoryInputs_no_Vmem hrow.2

theorem badMemoryStructure_not_equivalent_to_acceptance :
    ¬ (MemoryPublicRowsAccepted cfg badMemoryRows ↔
      Nonempty (MemoryPublicRowsForestWitness cfg badMemoryRows)) := by
  intro hiff
  exact badMemoryRows_not_accepted (hiff.mpr badMemoryStructuralWitness)

end

end Nock.RedTeam.Thm54P6Regression

#print axioms Nock.RedTeam.Thm54P6Regression.production_compute_topology
#print axioms Nock.RedTeam.Thm54P6Regression.production_compute_public_topology
#print axioms Nock.RedTeam.Thm54P6Regression.production_memory_topology
#print axioms Nock.RedTeam.Thm54P6Regression.production_traversable_chained
#print axioms Nock.RedTeam.Thm54P6Regression.acceptedExecutionP6
#print axioms Nock.RedTeam.Thm54P6Regression.productionComputePublicAccepted
#print axioms Nock.RedTeam.Thm54P6Regression.productionMemoryPublicAccepted
#print axioms Nock.RedTeam.Thm54P6Regression.productionPublicAcceptedComponents
#print axioms Nock.RedTeam.Thm54P6Regression.productionComputePublicRVTProduct
#print axioms Nock.RedTeam.Thm54P6Regression.productionMemoryRVTProduct
#print axioms Nock.RedTeam.Thm54P6Regression.productionPacketLocalRVTProducts
#print axioms Nock.RedTeam.Thm54P6Regression.production_public_private_alignment
#print axioms Nock.RedTeam.Thm54P6Regression.production_literal_traversal_clauses
#print axioms Nock.RedTeam.Thm54P6Regression.production_inverse_roundtrips
#print axioms Nock.RedTeam.Thm54P6Regression.production_packet_local_roundtrip
#print axioms Nock.RedTeam.Thm54P6Regression.badComputeRows_not_accepted
#print axioms Nock.RedTeam.Thm54P6Regression.badMemoryRows_not_accepted
#print axioms Nock.RedTeam.Thm54P6Regression.badComputeStructure_not_equivalent_to_acceptance
#print axioms Nock.RedTeam.Thm54P6Regression.badMemoryStructure_not_equivalent_to_acceptance
