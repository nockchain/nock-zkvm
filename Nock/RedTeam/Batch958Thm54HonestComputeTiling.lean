/-
  Nock/RedTeam/Batch958Thm54HonestComputeTiling.lean

  `computeTilingEventOf Qc = computeTilingEvent (foOf (computeSourceEnv Qc)) N` is
  `{ω | αc^(1 + Sf fo N) = αc^N ∧ 1 + Sf fo N ≠ N}` (`WalkTilingEvents.mem_computeTilingEvent_iff`):
  EMPTY as soon as the committed fanout column tiles.  At the canonical trace the decoded state of
  every row is the exec row's state (`src_rowState_honest`: the source environment embeds the
  one-hot base selectors, `Batch843.honest_base_selector`, `Batch908.toSourceEnv_gather_trace`),
  so `foOf` is the exec fanout, and the exec compute tree tiles (`Batch843.tiles_queued_honest`
  under `ComputeExactTopology`, which every buildable carrier has: `E.traversal.1`).

  Status: **proved** (honest-trace identity), for every coin, at every package whose execution has
  the exact compute topology, hence at every built (and so every generated) package.
-/
import Nock.RedTeam.Batch909Thm54R4HonestInstance
import Nock.RedTeam.Batch843Thm54HonestAlignment
import Nock.RedTeam.Batch465Thm54DeployedRootLabelEqClaim
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch958

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.OptimizedCanonicalHostileLists
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.WrapFixesVcomp
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.Framework
open Nock.Reified
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- **The decoded state of the canonical source row is the exec row's state** (every package). -/
theorem src_rowState_honest (i : Fin P.optimized.family.problem.cfg.compRows) :
    rowStateOf (P.computeSourceEnv (canonicalComputeTrace P) i) =
      (P.optimized.family.problem.exec.computePubAt i).state := by
  rw [Batch465.rowStateOf_eq_computeStateOf]
  apply computeStateOf_of_oneHot
  intro s
  have hs : opCol s < 13 := by cases s <;> decide
  have h := Batch908.toSourceEnv_gather_trace (K := K) P.optimized.basis
    (P.computeBaseEnv (canonicalComputeTrace P) i) (opCol s) (Or.inl hs)
  have hb := Batch843.honest_base_selector P i s
  have hb' : (P.computeBaseEnv (canonicalComputeTrace P) i).trace (opCol s) =
      if s = (P.optimized.family.problem.exec.computePubAt i).state then 1 else 0 := hb
  change (CorrectedFinalTypedEnv.toSourceEnv (gatherCorrectedFinalTypedEnv P.optimized.basis
    (P.computeBaseEnv (canonicalComputeTrace P) i))).trace (opCol s) = _
  rw [h, hb']
  split_ifs <;> simp

/-- The committed fanout column at the canonical trace is the typed rows' fanout column. -/
theorem foOf_honest (i : ℕ) (hi1 : 1 ≤ i) (hiN : i ≤ P.optimized.family.problem.cfg.compRows) :
    foOf (P.computeSourceEnv (canonicalComputeTrace P)) i =
      Batch771.foRows computeFanout (typedComputeRows P (honestComputeTrace P)) i := by
  have hlt : i - 1 < P.optimized.family.problem.cfg.compRows := by omega
  unfold foOf Batch771.foRows
  rw [dif_pos ⟨hi1, hlt⟩]
  have hlen : i - 1 < (typedComputeRows P (honestComputeTrace P)).length := by
    rw [typedComputeRows_length]; exact hlt
  rw [List.getElem?_eq_getElem hlen]
  simp only [Option.map_some, Option.getD_some, typedComputeRows, List.getElem_map,
    List.getElem_finRange]
  unfold rowFanout
  rw [src_rowState_honest]
  have ht := Batch843.typed_state_honest P ⟨i - 1, hlt⟩
  show fanoutComp _ = computeFanout (typedComputeLabel P (honestComputeTrace P) ⟨i - 1, hlt⟩)
  rcases hc : typedComputeLabel P (honestComputeTrace P) ⟨i - 1, hlt⟩ with ⟨st, d⟩
  rw [hc] at ht
  simp only at ht
  rw [ht]
  rfl

/-- **Component 6 at the honest instance**: the compute tiling event is empty at the canonical
trace (for every coin), under the exec compute topology. -/
theorem computeTiling_empty_honest
    (htopE : ComputeExactTopology P.optimized.family.problem.exec) :
    P.computeTilingEventOf (canonicalComputeTrace P) = ∅ := by
  apply WalkTilingEvents.computeTilingEvent_empty_of_tiling
  obtain ⟨ht, -⟩ := Batch843.tiles_queued_honest P htopE
  have hsf := ht.sf
  rw [typedComputeRows_length] at hsf
  rw [WalkForestPrefixAlphaEvents.Sf_congr_on (fun i h1 h2 => foOf_honest P i h1 h2)]
  exact hsf

theorem tileC_honest (htopE : ComputeExactTopology P.optimized.family.problem.exec) :
    P.honestTuple.1 ∉ P.computeTilingEventOf (canonicalComputeTrace P) := by
  rw [computeTiling_empty_honest P htopE]
  exact Finset.notMem_empty _

end

end Nock.RedTeam.Batch958

#print axioms Nock.RedTeam.Batch958.src_rowState_honest
#print axioms Nock.RedTeam.Batch958.computeTiling_empty_honest
#print axioms Nock.RedTeam.Batch958.tileC_honest
