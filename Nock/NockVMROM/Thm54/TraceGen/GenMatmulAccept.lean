/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulAccept.lean

  Compute-row acceptance of the generated assigned AIR-ordered matmul
  BFS render.  State-tag and challenge-input agreement are unconditional
  on `renderNode`.  `Vcomp` is `genComputeSkeleton_inTree_Vcomp`
  transported through `airReorder` labels, with tree-local autocons
  `headCell`, OP5 operand non-collision, and OP3 cell-size hypotheses.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulNodup
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonVcomp
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderChildLink
import Nock.NockVMROM.Thm54.TraceGen.GenTierAAccept
import Nock.NockVMROM.Thm54.Language

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun
open Nock.ComputeTable
open Nock.NockVMROM.Thm54

variable {K : Type} [Field K]

theorem genComputeSkeleton_airReorder_bfsLabelAt_Vcomp
    (z α : K) (hz : z ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hdyck : ∀ v, InTree t v → v.label.skel.state = State.cons →
      (encC z (formulaHead v.label.skel.formula)).dyck ≠ 0)
    (hncol : ∀ v, InTree t v → v.label.skel.state = State.s5 →
      op5ResultsAgree z v.label.skel)
    (hsz : ∀ v, InTree t v → v.label.skel.state = State.s3 →
      op3CallSizeOk z v.label.skel)
    {i : ℕ} (hi : i ∈ List.range' 1 (bfsForest [airReorder t]).length) :
    Vcomp (renderNode z α (bfsLabelAt (airReorder t) i)).row.2.1
      (renderNode z α (bfsLabelAt (airReorder t) i)).row.2.2.1
      (renderNode z α (bfsLabelAt (airReorder t) i)).row.2.2.2 := by
  have hi' := lt_bfsRows_of_mem_range' hi
  have hlen : i - 1 < (bfsForest [airReorder t]).length := by
    simpa [bfsRows_length] using hi'
  have hmem : (bfsForest [airReorder t])[i - 1] ∈
      bfsForest [airReorder t] := List.getElem_mem hlen
  have hin : InTree (airReorder t) (bfsForest [airReorder t])[i - 1] := by
    obtain ⟨r, hr, hIn⟩ := (mem_bfsForest [airReorder t] _).mp hmem
    simp only [List.mem_singleton] at hr
    subst r
    exact hIn
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label t _ hin
  rw [bfsLabelAt_eq (airReorder t) i hi']
  have hrow :
      (bfsRows (airReorder t))[i - 1] =
        (bfsForest [airReorder t])[i - 1].label := by
    simp [bfsRows]
  simp [hrow, hl]
  exact genComputeSkeleton_inTree_Vcomp z α hz h hdyck hncol hsz u0 hu0
    (accAt (airReorder t) (i - 1))

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

open Nock Nock.Walk Nock.Noun
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

theorem mm_range (i : ℕ) (hi : i ∈ List.range' 1 401) :
    i ∈ List.range' 1 (bfsForest [mmTreeAir (K := K)]).length := by
  simpa [mmTreeAir_bfsForest_length] using hi

theorem computeRow_state_inputs (z α : K) (i : ℕ) :
    (setRowCoins (0 : K) 0 1
        (renderNode z α (bfsLabelAt (mmTreeAir (K := K)) i)).row).1 =
      (setRowCoins (0 : K) 0 1
        (renderNode z α (bfsLabelAt (mmTreeAir (K := K)) i)).row).2.2.1.state ∧
    (setRowCoins (0 : K) 0 1
        (renderNode z α (bfsLabelAt (mmTreeAir (K := K)) i)).row).2.1 =
      ⟨α, z, 0, 0, 1⟩ := by
  constructor
  · simpa [setRowCoins] using
      renderNode_state_agree z α (bfsLabelAt (mmTreeAir (K := K)) i)
  · simp [setRowCoins, renderNode_inputs]

theorem computeRowAccepted_of_Vcomp (z α : K) {i : ℕ}
    (_hi : i ∈ List.range' 1 (bfsForest [mmTreeAir (K := K)]).length)
    (hV : Vcomp
      (renderNode z α (bfsLabelAt (mmTreeAir (K := K)) i)).row.2.1
      (renderNode z α (bfsLabelAt (mmTreeAir (K := K)) i)).row.2.2.1
      (renderNode z α (bfsLabelAt (mmTreeAir (K := K)) i)).row.2.2.2) :
    ExactExecution.ComputeRowAccepted (cfg z α)
      (setRowCoins (0 : K) 0 1
        (renderNode z α (bfsLabelAt (mmTreeAir (K := K)) i)).row) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (computeRow_state_inputs z α i).1
  · simpa [cfg, ChallengeVector.computeInputs] using
      (computeRow_state_inputs z α i).2
  · exact (Vcomp_setRowCoins (0 : K) 0 1 _).mpr hV

/-- `ComputeRowsAccepted` for the assigned AIR matmul render, given autocons
    `headCell` and OP5/OP3 NPR seed hypotheses -/
theorem computeRowsAccepted_of_seed (z α : K) (hz : z ≠ 0)
    (hdyck : ∀ v, InTree (mmTree (K := K)) v →
      v.label.skel.state = State.cons →
      (encC z (formulaHead v.label.skel.formula)).dyck ≠ 0)
    (hncol : ∀ v, InTree (mmTree (K := K)) v →
      v.label.skel.state = State.s5 →
      op5ResultsAgree z v.label.skel)
    (hsz : ∀ v, InTree (mmTree (K := K)) v →
      v.label.skel.state = State.s3 →
      op3CallSizeOk z v.label.skel) :
    (exec z α).ComputeRowsAccepted := by
  rw [ExactExecution.computeRowsAccepted_iff, computeRows_eq]
  intro row hrow
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow
  refine computeRowAccepted_of_Vcomp z α hi ?_
  unfold mmTreeAir at hi ⊢
  exact genComputeSkeleton_airReorder_bfsLabelAt_Vcomp z α hz
    (mmTree_gen (K := K)) hdyck hncol hsz hi

end Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_airReorder_bfsLabelAt_Vcomp
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.computeRowsAccepted_of_seed
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.computeRowAccepted_of_Vcomp
