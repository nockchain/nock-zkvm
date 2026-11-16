/-
  Nock/NockVMROM/Thm54/TraceGen/Checker.lean

  The EXECUTABLE three-chip
  AIR checker over the generated rows.

  For every compute/memory row of a generated trace this ships the per-row AIR acceptance
  statement — `∃` an auxiliary witness under which every constraint of the reified per-row
  compute AIR `computeAIR` / memory AIR `memoryAIR` evaluates to zero at the honest one-hot selector.

  The per-row content is discharged through the tight biconditionals `computeAIR_iff_Vcomp` and `memoryAIR_iff_Vmem`: given the algorithmic
  verifier acceptance (`Vcomp`/`Vmem`) and genericity (`WF`) of a row, the AIR is satisfied at that
  row.  Those acceptance/genericity witnesses are exactly the ones the semantic-CORE web already
  proved for the OP1 slice (`Op1RowWeb`) and the cons slice (`ConsRowWeb`/`ConsMemoryWeb`).

  The generated corollaries (`gen_op1_computeAIR_zero`, `gen_op1_memoryAIR_zero`,
  `gen_cons_computeAIR_zero`, `gen_cons_memoryAIR_zero`) transport the config-tree checks across the
  already-proven generator node/row-projection equalities (`Op1GenData.gen_computeNodes_eq`,
  `ConsGen.genTrace_cons_computeRows`, `ConsGenMem.gen_consMemForest_rows`, …), so that the checker
  is stated of *the generator's own emitted rows*, not a hand-built shadow.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op1GenData
import Nock.NockVMROM.Thm54.TraceGen.ConsGenMem

namespace Nock.NockVMROM.Thm54.TraceGen.Checker

open Nock Nock.Walk Nock.Reified Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.ForestExponentWindow
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy

variable {K : Type*} [Field K]

/-! ## The per-row AIR-satisfaction predicates -/

/-- **Per-row compute-AIR check.**  There is an auxiliary witness column assignment `ex` under which
    every constraint of the reified per-row compute AIR `computeAIR` evaluates to zero at the honest
    one-hot selector `opSel pub.state` of the row `(state, inp, pub, dec)`. -/
def ComputeRowChecks (r : ComputeTable.State × ComputeTable.DTcomp K) : Prop :=
  ∃ ex : ComputeTable.Extra K,
    ∀ c ∈ computeAIR.constraints,
      c.expr.eval (computeEnvFull r.2.1 (ComputeTable.opSel r.2.2.1.state) r.2.2.1 r.2.2.2 ex) = 0

/-- **Per-row memory-AIR check.**  There is a LogUp inverse-witness column `g` under which every
    constraint of the reified per-row memory AIR `memoryAIR` evaluates to zero at the honest one-hot
    selector `opSel mrow.st` of the row `(mstate, minp, mrow)`. -/
def MemoryRowChecks (r : MemoryTable.MState × MemoryTable.DTmem K) : Prop :=
  ∃ g : K,
    ∀ c ∈ (memoryAIR (K := K)).constraints,
      c.expr.eval (memoryEnvFull r.2.1 (MemoryTable.opSel r.2.2.st) r.2.2 g) = 0

/-- The compute check follows from the algorithmic verifier acceptance `Vcomp` and the genericity
    `WF` of the row, via the tight biconditional `computeAIR_iff_Vcomp`. -/
theorem computeRowChecks_of_Vcomp {inp : ComputeTable.Inputs K} {pub : ComputeTable.Pub K}
    {dec : ComputeTable.Dec K} (st : ComputeTable.State)
    (wf : ComputeTable.WF inp pub) (hv : ComputeTable.Vcomp inp pub dec) (hz : inp.z ≠ 0) :
    ComputeRowChecks (st, (inp, pub, dec)) :=
  (computeAIR_iff_Vcomp inp pub dec wf).mpr ⟨hv, hz⟩

/-- The memory check follows from the algorithmic verifier acceptance `Vmem` and the genericity `WF`
    of the row, via the tight biconditional `memoryAIR_iff_Vmem`. -/
theorem memoryRowChecks_of_Vmem {minp : MemoryTable.Inputs K} {mrow : MemoryTable.Pub K}
    (st : MemoryTable.MState) (wf : MemoryTable.WF minp mrow)
    (hv : MemoryTable.Vmem minp mrow) (hz : minp.z ≠ 0) :
    MemoryRowChecks (st, (minp, mrow)) :=
  (memoryAIR_iff_Vmem minp mrow wf).mpr ⟨hv, hz⟩

/-! ## A whole-tree "every row satisfies the check" predicate -/

/-- Every label of an `NTree` satisfies `P` (recursion mirrors `Walk.RVT`). -/
def NTree.All {LT : Type*} (P : LT → Prop) : NTree LT → Prop
  | .node l ch => P l ∧ ∀ s ∈ ch, NTree.All P s
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ‹s ∈ ch›
  omega

theorem all_leaf {LT : Type*} {P : LT → Prop} {l : LT} (h : P l) :
    NTree.All P (.node l []) := by
  unfold NTree.All; exact ⟨h, by intro s hs; simp at hs⟩

theorem all_node1 {LT : Type*} {P : LT → Prop} {l : LT} {c₁ : NTree LT}
    (h : P l) (h₁ : NTree.All P c₁) : NTree.All P (.node l [c₁]) := by
  unfold NTree.All
  refine ⟨h, ?_⟩
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs; exact h₁

theorem all_node2 {LT : Type*} {P : LT → Prop} {l : LT} {c₁ c₂ : NTree LT}
    (h : P l) (h₁ : NTree.All P c₁) (h₂ : NTree.All P c₂) :
    NTree.All P (.node l [c₁, c₂]) := by
  unfold NTree.All
  refine ⟨h, ?_⟩
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact h₁
  · exact h₂

/-! ## OP1 slice: every config compute/memory row passes its chip -/

open Nock.NockVMROM.Thm54.TraceGen.Op1Config in
/-- **The single OP1 compute row passes the compute chip.**  `computeAIR` is satisfied at the honest
    selector of the generated `OP_1` row. -/
theorem op1_compute_all :
    NTree.All ComputeRowChecks (Op1Config.exec Op1Config.seedZ Op1Config.alphaA).computeTree :=
  all_leaf (computeRowChecks_of_Vcomp _ compute_wf compute_accepts seedZ_ne_zero)

open Nock.NockVMROM.Thm54.TraceGen.Op1Config in
/-- **Every OP1 memory row passes the memory chip.**  Each of the five rows
    `read, decompose, halt₁, verify, haltᵣ` satisfies `memoryAIR` at its honest selector. -/
theorem op1_memory_all
    (hread : Vmem (Op1Config.memoryInputs Op1Config.seedZ)
      (Op1Config.readPub Op1Config.seedZ Op1Config.alphaA))
    (hdec : Vmem (Op1Config.memoryInputs Op1Config.seedZ)
      (Op1Config.decomposePub Op1Config.seedZ Op1Config.alphaA))
    (hver : Vmem (Op1Config.memoryInputs Op1Config.seedZ)
      (Op1Config.verifyPub Op1Config.seedZ Op1Config.alphaA)) :
    NTree.All MemoryRowChecks (Op1Config.readTree Op1Config.seedZ Op1Config.alphaA) :=
  all_node1 (memoryRowChecks_of_Vmem _ read_wf hread seedZ_ne_zero)
    (all_node2 (memoryRowChecks_of_Vmem _ decompose_wf hdec seedZ_ne_zero)
      (all_leaf (memoryRowChecks_of_Vmem _ head_wf head_accepts seedZ_ne_zero))
      (all_node1 (memoryRowChecks_of_Vmem _ verify_wf hver seedZ_ne_zero)
        (all_leaf (memoryRowChecks_of_Vmem _ tail_wf tail_accepts seedZ_ne_zero))))

/-! ## cons slice: every config compute/memory row passes its chip -/

open Nock.NockVMROM.Thm54.TraceGen.ConsConfig in
/-- **Every cons compute row passes the compute chip.**  The `.cons` autocons root and its two `OP_1` children each satisfy `computeAIR`. -/
theorem cons_compute_all : NTree.All ComputeRowChecks ConsConfig.computeTree :=
  all_node2 (computeRowChecks_of_Vcomp _ cons_wf cons_accepts seedZ_ne_zero)
    (all_leaf (computeRowChecks_of_Vcomp _ op1L_wf op1L_accepts seedZ_ne_zero))
    (all_leaf (computeRowChecks_of_Vcomp _ op1R_wf op1R_accepts seedZ_ne_zero))

open Nock.NockVMROM.Thm54.TraceGen.ConsConfig in
/-- **Every cons memory row passes the memory chip.**  All thirteen rows of the served forest
    satisfy `memoryAIR` at their honest selectors.  The seven
    non-record-touching rows (`decompose`/`halt`) discharge `WF` vacuously (`pole_ne` fires only in
    `read_root`/`verify_child`). -/
theorem cons_memory_all
    (hReadF : Vmem ConsConfig.memInputs ConsConfig.pReadF)
    (hDecF : Vmem ConsConfig.memInputs ConsConfig.pDecF)
    (hReadL : Vmem ConsConfig.memInputs ConsConfig.pReadL)
    (hReadR : Vmem ConsConfig.memInputs ConsConfig.pReadR)
    (hDecL : Vmem ConsConfig.memInputs ConsConfig.pDecL)
    (hVerifyF : Vmem ConsConfig.memInputs ConsConfig.pVerifyF)
    (hVerifyL : Vmem ConsConfig.memInputs ConsConfig.pVerifyL)
    (hDecR : Vmem ConsConfig.memInputs ConsConfig.pDecR)
    (hVerifyR : Vmem ConsConfig.memInputs ConsConfig.pVerifyR) :
    NTree.All MemoryRowChecks ConsConfig.rootTree := by
  have decF_wf : MemoryTable.WF ConsConfig.memInputs pDecF := ⟨fun h => by simp [pDecF, decPub] at h⟩
  have decL_wf : MemoryTable.WF ConsConfig.memInputs pDecL := ⟨fun h => by simp [pDecL, decPub] at h⟩
  have decR_wf : MemoryTable.WF ConsConfig.memInputs pDecR := ⟨fun h => by simp [pDecR, decPub] at h⟩
  have haltL1_wf : MemoryTable.WF ConsConfig.memInputs pHaltL1 := ⟨fun h => by simp [pHaltL1, haltPub] at h⟩
  have haltL5_wf : MemoryTable.WF ConsConfig.memInputs pHaltL5 := ⟨fun h => by simp [pHaltL5, haltPub] at h⟩
  have haltR1_wf : MemoryTable.WF ConsConfig.memInputs pHaltR1 := ⟨fun h => by simp [pHaltR1, haltPub] at h⟩
  have haltR6_wf : MemoryTable.WF ConsConfig.memInputs pHaltR6 := ⟨fun h => by simp [pHaltR6, haltPub] at h⟩
  exact
    all_node1 (memoryRowChecks_of_Vmem _ pReadF_wf hReadF seedZ_ne_zero)
      (all_node2 (memoryRowChecks_of_Vmem _ decF_wf hDecF seedZ_ne_zero)
        (all_node1 (memoryRowChecks_of_Vmem _ pReadL_wf hReadL seedZ_ne_zero)
          (all_node2 (memoryRowChecks_of_Vmem _ decL_wf hDecL seedZ_ne_zero)
            (all_leaf (memoryRowChecks_of_Vmem _ haltL1_wf pHaltL1_accepts seedZ_ne_zero))
            (all_node1 (memoryRowChecks_of_Vmem _ pVerifyL_wf hVerifyL seedZ_ne_zero)
              (all_leaf (memoryRowChecks_of_Vmem _ haltL5_wf pHaltL5_accepts seedZ_ne_zero)))))
        (all_node1 (memoryRowChecks_of_Vmem _ pReadR_wf hReadR seedZ_ne_zero)
          (all_node1 (memoryRowChecks_of_Vmem _ pVerifyF_wf hVerifyF seedZ_ne_zero)
            (all_node2 (memoryRowChecks_of_Vmem _ decR_wf hDecR seedZ_ne_zero)
              (all_leaf (memoryRowChecks_of_Vmem _ haltR1_wf pHaltR1_accepts seedZ_ne_zero))
              (all_node1 (memoryRowChecks_of_Vmem _ pVerifyR_wf hVerifyR seedZ_ne_zero)
                (all_leaf (memoryRowChecks_of_Vmem _ haltR6_wf pHaltR6_accepts seedZ_ne_zero)))))))

/-! ## The generated rows: transport across the node/row-projection equalities

    The generator's own emitted rows are exactly the config rows the chips accept above; we transport
    the whole-tree checks across the already-proven projection equalities. -/

/-- The row-projection of the OP1 committed compute node tree is the config compute tree. -/
theorem op1ComputeTree_row :
    mapNTree ComputeNode.row Op1Config.op1ComputeTree
      = (Op1Config.exec Op1Config.seedZ Op1Config.alphaA).computeTree := by
  simp only [Op1Config.op1ComputeTree, Op1Config.op1ComputeNode, mapNTree, List.map_nil,
    Op1Config.exec]

theorem op1MemTree_row :
    mapNTree MemoryNode.row Op1Config.op1MemTree
      = Op1Config.readTreeA Op1Config.seedZ Op1Config.alphaA := by
  simp only [Op1Config.op1MemTree, Op1Config.op1ReadNode, Op1Config.op1DecomposeNode,
    Op1Config.op1HeadNode, Op1Config.op1VerifyNode, Op1Config.op1TailNode, mapNTree, List.map_nil,
    List.map_cons, Op1Config.readTreeA, Op1Config.decomposeTreeA, Op1Config.headTreeA,
    Op1Config.verifyTreeA, Op1Config.tailTreeA]

/-- The row encode of the OP1 a-bearing root tree is the executed root tree (`exec_encode`). -/
theorem op1_readTree_encode :
    mapNTree (MemoryRowTemplate.encodeRow MemoryTable.formRDefault) (Op1Config.readTreeA Op1Config.seedZ Op1Config.alphaA)
      = Op1Config.readTree Op1Config.seedZ Op1Config.alphaA := by
  have h := congrArg ExactExecution.memoryForest
    (Op1Config.exec_encode Op1Config.seedZ Op1Config.alphaA)
  simp only [Op1Config.exec, Op1Config.execA, ExactExecution.encodeMem, List.map_cons,
    List.map_nil] at h
  exact ((List.cons.inj (List.cons.inj h).2).1).symm

/-- The row encode of the cons a-bearing root tree is the executed root tree (`exec_encode`). -/
theorem cons_rootTree_encode :
    mapNTree (MemoryRowTemplate.encodeRow MemoryTable.formRDefault) ConsConfig.rootTreeA = ConsConfig.rootTree := by
  have h := congrArg ExactExecution.memoryForest ConsConfig.exec_encode
  simp only [ConsConfig.exec, ConsConfig.execA, ExactExecution.encodeMem, List.map_cons,
    List.map_nil] at h
  exact ((List.cons.inj (List.cons.inj h).2).1).symm

/-- Row encode of a generated served forest, factored through the node projection. -/
theorem gen_memForest_encode {F : Type} [Field F] (G : GenTrace F F) :
    G.memoryNodes.map
        (mapNTree (fun g => MemoryRowTemplate.encodeRow MemoryTable.formRDefault (GenMemoryRow.node g).row))
      = (G.memoryNodes.map (mapNTree (fun g => (GenMemoryRow.node g).row))).map
          (mapNTree (MemoryRowTemplate.encodeRow MemoryTable.formRDefault)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro t _
  exact (mapNTree_comp (fun g => (GenMemoryRow.node g).row) (MemoryRowTemplate.encodeRow MemoryTable.formRDefault) t).symm

/-- The OP1 generated compute node tree, projected to its rows, is the config compute tree. -/
theorem gen_op1_computeRows_eq {G : GenTrace Op1Config.F Op1Config.F}
    (h : mapNTree GenComputeRow.node G.computeNodes = Op1Config.op1ComputeTree) :
    mapNTree GenComputeRow.row G.computeNodes
      = (Op1Config.exec Op1Config.seedZ Op1Config.alphaA).computeTree := by
  rw [show mapNTree GenComputeRow.row G.computeNodes
        = mapNTree ComputeNode.row (mapNTree GenComputeRow.node G.computeNodes) from
      (mapNTree_comp GenComputeRow.node ComputeNode.row G.computeNodes).symm, h,
    op1ComputeTree_row]

/-- The OP1 generated served forest, projected to its rows, is the config memory forest. -/
theorem gen_op1_memForest_rows {G : GenTrace Op1Config.F Op1Config.F}
    (h : G.memoryNodes.map (mapNTree GenMemoryRow.node) = [Op1Config.op1MemTree]) :
    G.memoryNodes.map (mapNTree (fun g => (GenMemoryRow.node g).row))
      = [Op1Config.readTreeA Op1Config.seedZ Op1Config.alphaA] := by
  have hcompose :
      G.memoryNodes.map (mapNTree (fun g => (GenMemoryRow.node g).row))
        = (G.memoryNodes.map (mapNTree GenMemoryRow.node)).map (mapNTree MemoryNode.row) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro t _
    exact (mapNTree_comp GenMemoryRow.node MemoryNode.row t).symm
  rw [hcompose, h, List.map_cons, List.map_nil, op1MemTree_row]

/-- **Generated OP1 compute chip.**  Every row of the generator's committed compute tree for
    `*[0 [1 5]] = 5` satisfies `computeAIR` at its honest selector. -/
theorem gen_op1_computeAIR_zero (n : ℕ) (G : GenTrace Op1Config.F Op1Config.F)
    (hgen : genTrace 97 3 Op1Config.seedZ Op1Config.alphaA (n + 1)
        Op1Skeleton.subjectNoun Op1Skeleton.formulaNoun = .ok G) :
    NTree.All ComputeRowChecks (mapNTree GenComputeRow.row G.computeNodes) := by
  rw [gen_op1_computeRows_eq (genTrace_spec n G hgen).computeNodes_eq]
  exact op1_compute_all

/-- **Generated OP1 memory chip.** -/
theorem gen_op1_memoryAIR_zero (n : ℕ) (G : GenTrace Op1Config.F Op1Config.F)
    (hgen : genTrace 97 3 Op1Config.seedZ Op1Config.alphaA (n + 1)
        Op1Skeleton.subjectNoun Op1Skeleton.formulaNoun = .ok G)
    (hread : Vmem (Op1Config.memoryInputs Op1Config.seedZ)
      (Op1Config.readPub Op1Config.seedZ Op1Config.alphaA))
    (hdec : Vmem (Op1Config.memoryInputs Op1Config.seedZ)
      (Op1Config.decomposePub Op1Config.seedZ Op1Config.alphaA))
    (hver : Vmem (Op1Config.memoryInputs Op1Config.seedZ)
      (Op1Config.verifyPub Op1Config.seedZ Op1Config.alphaA)) :
    ∀ t ∈ G.memoryNodes.map
        (mapNTree (fun g => MemoryRowTemplate.encodeRow MemoryTable.formRDefault (GenMemoryRow.node g).row)),
      NTree.All MemoryRowChecks t := by
  rw [gen_memForest_encode, gen_op1_memForest_rows (genTrace_spec n G hgen).memoryForest_eq,
    List.map_cons, List.map_nil, op1_readTree_encode]
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  subst ht
  exact op1_memory_all hread hdec hver

/-- The cons generated served forest, projected to its rows, is the config memory forest. -/
theorem gen_cons_memForest_rows {G : GenTrace ConsConfig.F ConsConfig.F}
    (h : G.memoryNodes.map (mapNTree GenMemoryRow.node) = [ConsConfig.consMemTree]) :
    G.memoryNodes.map (mapNTree (fun g => (GenMemoryRow.node g).row))
      = [mapNTree MemoryNode.row ConsConfig.consMemTree] := by
  have hcompose :
      G.memoryNodes.map (mapNTree (fun g => (GenMemoryRow.node g).row))
        = (G.memoryNodes.map (mapNTree GenMemoryRow.node)).map (mapNTree MemoryNode.row) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro t _
    exact (mapNTree_comp GenMemoryRow.node MemoryNode.row t).symm
  rw [hcompose, h]
  rfl

/-- **Generated cons compute chip.**  Every row of the generator's committed compute tree for
    `*[0 [[1 5] [1 6]]] = [5 6]` satisfies `computeAIR` at its honest selector. -/
theorem gen_cons_computeAIR_zero (n : ℕ) :
    ∃ G : GenTrace ConsConfig.F ConsConfig.F,
      genTrace 97 4 ConsConfig.seedZ ConsConfig.alphaA (n + 2)
          ConsSkeleton.subjectNoun ConsSkeleton.formulaNoun = .ok G ∧
        NTree.All ComputeRowChecks (mapNTree GenComputeRow.row G.computeNodes) := by
  obtain ⟨G, hgen, hrows⟩ := genTrace_cons_computeRows n
  exact ⟨G, hgen, by rw [hrows]; exact cons_compute_all⟩

/-- **Generated cons memory chip.** -/
theorem gen_cons_memoryAIR_zero (n : ℕ) (G : GenTrace ConsConfig.F ConsConfig.F)
    (hgen : genTrace 97 4 ConsConfig.seedZ ConsConfig.alphaA (n + 2)
        ConsSkeleton.subjectNoun ConsSkeleton.formulaNoun = .ok G)
    (hReadF : Vmem ConsConfig.memInputs ConsConfig.pReadF)
    (hDecF : Vmem ConsConfig.memInputs ConsConfig.pDecF)
    (hReadL : Vmem ConsConfig.memInputs ConsConfig.pReadL)
    (hReadR : Vmem ConsConfig.memInputs ConsConfig.pReadR)
    (hDecL : Vmem ConsConfig.memInputs ConsConfig.pDecL)
    (hVerifyF : Vmem ConsConfig.memInputs ConsConfig.pVerifyF)
    (hVerifyL : Vmem ConsConfig.memInputs ConsConfig.pVerifyL)
    (hDecR : Vmem ConsConfig.memInputs ConsConfig.pDecR)
    (hVerifyR : Vmem ConsConfig.memInputs ConsConfig.pVerifyR) :
    ∀ t ∈ G.memoryNodes.map
        (mapNTree (fun g => MemoryRowTemplate.encodeRow MemoryTable.formRDefault (GenMemoryRow.node g).row)),
      NTree.All MemoryRowChecks t := by
  rw [gen_memForest_encode, gen_cons_memForest_rows (consGenTrace_spec n G hgen).memoryForest_eq]
  intro t ht
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ht
  subst ht
  have hrow : mapNTree MemoryNode.row ConsConfig.consMemTree = ConsConfig.rootTreeA := by
    have h := ConsConfig.cons_memory_rows
    simp only [List.map] at h
    exact (List.cons.inj (List.cons.inj h).2).1
  rw [hrow, cons_rootTree_encode]
  exact cons_memory_all hReadF hDecF hReadL hReadR hDecL hVerifyF hVerifyL hDecR hVerifyR

end Nock.NockVMROM.Thm54.TraceGen.Checker

#print axioms Nock.NockVMROM.Thm54.TraceGen.Checker.op1_compute_all
#print axioms Nock.NockVMROM.Thm54.TraceGen.Checker.op1_memory_all
#print axioms Nock.NockVMROM.Thm54.TraceGen.Checker.cons_compute_all
#print axioms Nock.NockVMROM.Thm54.TraceGen.Checker.cons_memory_all
#print axioms Nock.NockVMROM.Thm54.TraceGen.Checker.gen_op1_computeAIR_zero
#print axioms Nock.NockVMROM.Thm54.TraceGen.Checker.gen_op1_memoryAIR_zero
#print axioms Nock.NockVMROM.Thm54.TraceGen.Checker.gen_cons_computeAIR_zero
#print axioms Nock.NockVMROM.Thm54.TraceGen.Checker.gen_cons_memoryAIR_zero
