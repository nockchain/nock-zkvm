/-
  Nock/NockVMROM/Thm54/TraceGen/Op2RowWebK3.lean

  Stage 3 of the OP2 Layer-2 CORE, over `K3`: the per-row `Vcomp` acceptance, genericity
  (`WF`), whole-tree row acceptance, BFS line-number chain, and arity-3 `Fcomp` topology
  of the four-row fan-out-3 eval program

      `*[0 [2 [1 [0 1]] [1 [1 5]]]] = 5`

  The genuinely-new site is the `.s2` parent:
  `fanoutComp.s2 = 3`, two live memory records (formula-open @3 and formula-tail @2),
  and `evalV` threading `sf1/sf2/sf3` with the third child's subject equal to the
  computed `sf1`.  The three `.s1` children reuse the OP1 `Vcomp` shape, the third
  over the computed subject `[0 1]`.  Memory `Vmem` lives in `Op2MemoryWebK3`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3
import Nock.NockVMROM.Thm54.TraceGen.Op2SemanticDataK3
import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.NockVMROM.Thm54.ExactTraversal

namespace Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

open Nock Nock.Walk Nock.MemoryTable Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

/-! ## The four compute rows are accepted by `V_comp` -/

/-- The `.s2` parent row is accepted: formula opens as `[2 [b c]]`, the two live
records reconstruct the formula-open and formula-tail cells, and the evaluation
block threads `sf1/sf2/sf3` to `op2Result`. -/
theorem parent_accepts : Vcomp (compInputs seedZ alphaA) (parentPub seedZ alphaA)
    (parentDec seedZ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op2Head op2ParentTail
  · ext <;>
      norm_num [parentPub, recF, parentDec, compInputs, fp, seedZ, alphaA]
  · simp [SVhead, headAtom, parentPub, parentDec, compInputs, fp, op2Head,
      GlobalCarryRecognizer.enc_atom, State.toNat, seedZ, alphaA]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · ext <;>
        norm_num [parentPub, recT, parentDec, compInputs, fp, seedZ, alphaA]
    · exact (GlobalCarryRecognizer.enc_cons seedZ_ne_zero op2ChildFormula1
        op2ChildFormula2).symm
    · rfl
    · simp [parentPub, compInputs]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The first `OP_1` child `*[0 [1 [0 1]]] = [0 1]` is accepted. -/
theorem child1_accepts : Vcomp (compInputs seedZ alphaA) (child1Pub seedZ alphaA)
    (op1DecOf seedZ op2Sf1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op1Head op2Sf1
  · ext <;>
      norm_num [child1Pub, op1PubOf, recB, op1DecOf, compInputs, fp, seedZ, alphaA,
        pow_succ, pow_two]
  · simp [SVhead, headAtom, child1Pub, op1PubOf, op1DecOf, fp, op1Head,
      GlobalCarryRecognizer.enc_atom, State.toNat, compInputs, seedZ]
  · exact ⟨rfl, rfl, by simp [child1Pub, op1PubOf, compInputs]⟩
  · exact ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- The second `OP_1` child `*[0 [1 [1 5]]] = [1 5]` is accepted. -/
theorem child2_accepts : Vcomp (compInputs seedZ alphaA) (child2Pub seedZ alphaA)
    (op1DecOf seedZ op2Sf2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op1Head op2Sf2
  · ext <;>
      norm_num [child2Pub, op1PubOf, recC, op1DecOf, compInputs, fp, seedZ, alphaA,
        pow_succ, pow_two]
  · simp [SVhead, headAtom, child2Pub, op1PubOf, op1DecOf, fp, op1Head,
      GlobalCarryRecognizer.enc_atom, State.toNat, compInputs, seedZ]
  · exact ⟨rfl, rfl, by simp [child2Pub, op1PubOf, compInputs, pow_succ]⟩
  · exact ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- The third `OP_1` child `*[[0 1] [1 5]] = 5` (computed subject `sf1`) is accepted. -/
theorem child3_accepts : Vcomp (compInputs seedZ alphaA) (child3Pub seedZ alphaA)
    (op1DecOf seedZ op2Result) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op1Head op2Result
  · ext <;>
      norm_num [child3Pub, op1PubOf, recS, op1DecOf, compInputs, fp, seedZ, alphaA,
        pow_succ, pow_two]
  · simp [SVhead, headAtom, child3Pub, op1PubOf, op1DecOf, fp, op1Head,
      GlobalCarryRecognizer.enc_atom, State.toNat, compInputs, seedZ]
  · exact ⟨rfl, rfl, by simp [child3Pub, op1PubOf, compInputs, pow_succ]⟩
  · exact ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-! ## Compute genericity (`WF`) per row -/

theorem parent_wf : ComputeTable.WF (compInputs seedZ alphaA) (parentPub seedZ alphaA) where
  rlc5 := by simp [parentPub]
  size8 := by simp [parentPub]
  size11 := by simp [parentPub]

theorem child1_wf : ComputeTable.WF (compInputs seedZ alphaA) (child1Pub seedZ alphaA) where
  rlc5 := by simp [child1Pub, op1PubOf]
  size8 := by simp [child1Pub, op1PubOf]
  size11 := by simp [child1Pub, op1PubOf]

theorem child2_wf : ComputeTable.WF (compInputs seedZ alphaA) (child2Pub seedZ alphaA) where
  rlc5 := by simp [child2Pub, op1PubOf]
  size8 := by simp [child2Pub, op1PubOf]
  size11 := by simp [child2Pub, op1PubOf]

theorem child3_wf : ComputeTable.WF (compInputs seedZ alphaA) (child3Pub seedZ alphaA) where
  rlc5 := by simp [child3Pub, op1PubOf]
  size8 := by simp [child3Pub, op1PubOf]
  size11 := by simp [child3Pub, op1PubOf]

/-! ## Whole-tree compute-row acceptance -/

theorem computeRowsAccepted : (exec seedZ alphaA).ComputeRowsAccepted := by
  rw [ExactExecution.computeRowsAccepted_iff, computeRows_eq]
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl, parent_accepts⟩
  · exact ⟨rfl, rfl, child1_accepts⟩
  · exact ⟨rfl, rfl, child2_accepts⟩
  · exact ⟨rfl, rfl, child3_accepts⟩

/-! ## BFS re-indexing of the canonical compute rows -/

theorem computePubAt_zero :
    (exec seedZ alphaA).computePubAt ⟨0, by norm_num [cfg]⟩ = parentPub seedZ alphaA := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt, computeRows_eq, cfg,
    parentRow]

theorem computePubAt_one :
    (exec seedZ alphaA).computePubAt ⟨1, by norm_num [cfg]⟩ = child1Pub seedZ alphaA := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt, computeRows_eq, cfg,
    child1Row, child1Pub]

theorem computePubAt_two :
    (exec seedZ alphaA).computePubAt ⟨2, by norm_num [cfg]⟩ = child2Pub seedZ alphaA := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt, computeRows_eq, cfg,
    child2Row, child2Pub]

theorem computePubAt_three :
    (exec seedZ alphaA).computePubAt ⟨3, by norm_num [cfg]⟩ = child3Pub seedZ alphaA := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt, computeRows_eq, cfg,
    child3Row, child3Pub]

theorem compute_wf_all :
    ∀ i, ComputeTable.WF (cfg seedZ alphaA).challenges.computeInputs
      ((exec seedZ alphaA).computePubAt i) := by
  intro i
  fin_cases i
  · rw [computePubAt_zero]; exact parent_wf
  · rw [computePubAt_one]; exact child1_wf
  · rw [computePubAt_two]; exact child2_wf
  · rw [computePubAt_three]; exact child3_wf

/-- Adjacent compute rows share the line-number boundary (`ln` of `i` is `ln_prev` of
`i+1`): `1 → α² → α³ → α⁴ → α⁵`. -/
theorem compute_chain :
    ∀ i : Fin (cfg seedZ alphaA).compRows,
      ∀ _ : (i : ℕ) + 1 < (cfg seedZ alphaA).compRows,
        ((exec seedZ alphaA).computePubAt i).ln =
          ((exec seedZ alphaA).computePubAt ⟨(i : ℕ) + 1, by omega⟩).ln_prev := by
  intro i hi
  fin_cases i
  · rw [computePubAt_zero, computePubAt_one]
    simp [parentPub, child1Pub, op1PubOf]
  · rw [computePubAt_one, computePubAt_two]
    simp [child1Pub, child2Pub, op1PubOf, pow_succ]
  · rw [computePubAt_two, computePubAt_three]
    simp [child2Pub, child3Pub, op1PubOf, pow_succ]
  · simp [cfg] at hi

/-! ## Arity-3 `Fcomp` topology on the fan-out-3 compute tree -/

theorem child1Row_fcomp :
    ComputeTable.Fcomp (child1Row seedZ alphaA) (fun _ => none) := by
  refine ⟨rfl, child1_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [child1Row, ComputeTable.fanoutComp]
  · intro i hi; simp [child1Row, ComputeTable.fanoutComp] at hi

theorem child2Row_fcomp :
    ComputeTable.Fcomp (child2Row seedZ alphaA) (fun _ => none) := by
  refine ⟨rfl, child2_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [child2Row, ComputeTable.fanoutComp]
  · intro i hi; simp [child2Row, ComputeTable.fanoutComp] at hi

theorem child3Row_fcomp :
    ComputeTable.Fcomp (child3Row seedZ alphaA) (fun _ => none) := by
  refine ⟨rfl, child3_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [child3Row, ComputeTable.fanoutComp]
  · intro i hi; simp [child3Row, ComputeTable.fanoutComp] at hi

theorem child1Tree_rvt :
    RVT (ComputeTable.Fcomp (K := K)) (.node (child1Row seedZ alphaA) []) := by
  unfold RVT
  refine ⟨?_, by simp, ?_⟩
  · rw [show (fun i : Fin 3 =>
        (NTree.node (child1Row seedZ alphaA) ([] : List (NTree _))).childLabel i)
        = (fun _ => none) by funext i; fin_cases i <;> rfl]
    exact child1Row_fcomp
  · exact ⟨fun _ => child1Row_fcomp, fun _ => rfl⟩

theorem child2Tree_rvt :
    RVT (ComputeTable.Fcomp (K := K)) (.node (child2Row seedZ alphaA) []) := by
  unfold RVT
  refine ⟨?_, by simp, ?_⟩
  · rw [show (fun i : Fin 3 =>
        (NTree.node (child2Row seedZ alphaA) ([] : List (NTree _))).childLabel i)
        = (fun _ => none) by funext i; fin_cases i <;> rfl]
    exact child2Row_fcomp
  · exact ⟨fun _ => child2Row_fcomp, fun _ => rfl⟩

theorem child3Tree_rvt :
    RVT (ComputeTable.Fcomp (K := K)) (.node (child3Row seedZ alphaA) []) := by
  unfold RVT
  refine ⟨?_, by simp, ?_⟩
  · rw [show (fun i : Fin 3 =>
        (NTree.node (child3Row seedZ alphaA) ([] : List (NTree _))).childLabel i)
        = (fun _ => none) by funext i; fin_cases i <;> rfl]
    exact child3Row_fcomp
  · exact ⟨fun _ => child3Row_fcomp, fun _ => rfl⟩

theorem computeTree_rvt :
    RVT (ComputeTable.Fcomp (K := K)) (computeTree seedZ alphaA) := by
  unfold computeTree RVT
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨rfl, parent_accepts, ?_, ?_⟩
    · intro i
      fin_cases i <;>
        simp [parentRow, ComputeTable.fanoutComp, NTree.childLabel, NTree.childOpt]
    · intro i hi
      fin_cases i
      · simp [parentRow, child1Row, child1Pub, op1PubOf, parentPub, ComputeTable.sfTriple,
          NTree.childLabel, NTree.childOpt, NTree.label]
      · simp [parentRow, child2Row, child2Pub, op1PubOf, parentPub, ComputeTable.sfTriple,
          NTree.childLabel, NTree.childOpt, NTree.label]
      · simp [parentRow, child3Row, child3Pub, op1PubOf, parentPub, ComputeTable.sfTriple,
          NTree.childLabel, NTree.childOpt, NTree.label]
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact child1Tree_rvt
    · exact child2Tree_rvt
    · exact child3Tree_rvt
  · refine ⟨fun h => absurd h (by simp [NTree.isLeaf]), fun h => ?_⟩
    exfalso
    have h0 := h.2.2.1 ⟨0, by norm_num⟩
    simp [ComputeTable.fanoutComp, parentRow] at h0

theorem compute_topology : ComputeExactTopology (exec seedZ alphaA) := by
  refine ⟨?_, ?_⟩
  · show RVT (ComputeTable.Fcomp (K := K)) (exec seedZ alphaA).computeTree
    exact computeTree_rvt
  · show ProperArity 3 (exec seedZ alphaA).computeTree
    simp [exec, computeTree]

end

end Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.parent_accepts
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.computeRowsAccepted
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.compute_topology
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.compute_chain
