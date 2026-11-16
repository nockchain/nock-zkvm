/-
  Nock/NockVMROM/Thm54/P8Core/SVCompute/QueueTwins.lean

  **The compute queue witness of `WalkQueueDeployed` at a datum and a
  layout.**  `queueNonEmpty_gate_zero`, `queueTiling_gate_zero`, `count_ne_ln_of_queue`,
  `count_eq_ln_last`, `deployed_bfsValid`, `deployed_tiling` and the compute half of
  `TracesWalkHyps` (`tracesWalkHyps_compute`): the live proofs with `P c Qc hsat hax hbasis hwidth`
  replaced by `D L c Q RF hchar hadj` (see `WalkTwins`).  The memory half of `WalkQueueDeployed`
  (`deployed_bfsValid_memory`, `deployed_tiling_memory`, `kMem_pos`) is WALK and has no twin.
-/
import Nock.NockVMROM.Thm54.P8Core.SVCompute.RootTwins
import Nock.NockVMROM.Thm54.P8Core.WalkQueueDeployed

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.SVCompute

open scoped Classical
open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.RedTeam.Batch459
open Nock.RedTeam.Batch478

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {h : ℕ}
  (D : ChipData F K h) (L : ChipLayout F K h)
  (c : OptimizedProductionChallengeTuple K F) (Q : Fin (chipOf D L c).rap.w → F[X])
  (RF : RowFacts D L c Q)
  (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (hadj : D.Adjacent)

section Queue

include RF hchar hadj

omit hadj in
theorem queueNonEmpty_gate_zeroD (i : Fin (D.N)) :
    walkQueueNonEmpty.eval (envRD D L c Q i) = 0 := by
  have hc := (row_obligations_atD D L c Q RF i).extensionCore21 packedQueueNonEmptyId
  have hsem : correctedCoreSemanticValue (rowEnvAtD D c Q i) packedQueueNonEmptyId =
      (correctedFinalExtGate packedQueueNonEmptyId).eval (rowEnvAtD D c Q i) := by
    simp [correctedCoreSemanticValue]
  have hsrc :=
    (correctedFinalExtGate_eval_source (rowEnvAtD D c Q i) packedQueueNonEmptyId).trans
      (hsem.symm.trans hc)
  rw [finalExtTransitionGates_get_queueNonEmpty] at hsrc
  exact hsrc

omit hadj in
theorem queueTiling_gate_zeroD (i : Fin (D.N)) :
    walkQueueTiling.eval (envRD D L c Q i) = 0 := by
  have hc := (row_obligations_atD D L c Q RF i).extensionCore21 packedQueueTilingId
  have hsem : correctedCoreSemanticValue (rowEnvAtD D c Q i) packedQueueTilingId =
      (correctedFinalExtGate packedQueueTilingId).eval (rowEnvAtD D c Q i) := by
    simp [correctedCoreSemanticValue]
  have hsrc :=
    (correctedFinalExtGate_eval_source (rowEnvAtD D c Q i) packedQueueTilingId).trans
      (hsem.symm.trans hc)
  rw [finalExtTransitionGates_get_queueTiling] at hsrc
  exact hsrc

theorem count_ne_ln_of_queueD (i : Fin (D.N))
    (hi : (i : ℕ) + 1 < D.N) :
    countWD D L c Q ((i : ℕ) + 1) ≠ lnWD D L c Q ((i : ℕ) + 1) := by
  have hgate := queueNonEmpty_gate_zeroD D L c Q RF hchar i
  have hnl := notLast_walkD D L c Q RF hchar hadj i hi
  have h12 : (envRD D L c Q i).trace 12 = 0 := by
    rw [envRD, CorrectedFinalTypedEnv.toSourceEnv]
    change algebraMap F K ((rowEnvAtD D c Q i).baseTrace 12) = 0
    rw [hnl, map_zero]
  have hrow : rowOfD D ((i : ℕ) + 1) = i := rowOf_succD D (i : ℕ) i.isLt
  rw [countWD, lnWD, hrow]
  rw [walkQueueNonEmpty_eval] at hgate
  simp only [h12, sub_zero, one_mul, Int.cast_one] at hgate
  intro heq
  have : (walkInv .traceCur).eval (envRD D L c Q i) * (0 : K) - (1 : K) = 0 := by
    simpa [heq, sub_self] using hgate
  simp at this

theorem count_eq_ln_lastD :
    countWD D L c Q (D.N) = lnWD D L c Q (D.N) := by
  have hgate := queueTiling_gate_zeroD D L c Q RF hchar (lastRowD D)
  have hlast := isLast_source_lastD D L c Q RF hchar hadj
  have hrow : rowOfD D (D.N) = lastRowD D := rowOf_rowsD D
  rw [countWD, lnWD, hrow]
  rw [walkQueueTiling_eval, hlast, one_mul] at hgate
  exact sub_eq_zero.mp hgate

/-- Queue-validity, no condition on `α`.  `Batch478::bfsValid_of_ratio_gate`. -/
theorem deployed_bfsValidD :
    BFSValid (foWD D L c Q RF hchar) (D.N) := by
  have hw := deployed_walkSatD D L c Q RF hchar hadj
  refine bfsValid_of_ratio_gate (K := K) (α := alphaC c.1) ?_
  intro i hi1 hih
  have hk : i - 1 < D.N := by omega
  let k : Fin (D.N) := ⟨i - 1, hk⟩
  have hki : (k : ℕ) + 1 = i := Nat.sub_add_cancel hi1
  have hne := count_ne_ln_of_queueD D L c Q RF hchar hadj k (by omega)
  have hcnt := Walk.count_closed hw i hi1 (le_of_lt hih)
  have hln := Walk.ln_closed hw i hi1 (le_of_lt hih)
  rw [hki] at hne
  rw [hcnt, hln] at hne
  rw [pow_add, pow_one]
  exact hne

/-- Last-row gate forces the tiling outside the priced event. -/
theorem deployed_tilingD
    (hα : c.1 ∉ computeTilingEvent (foWD D L c Q RF hchar) (D.N)) :
    Sf (foWD D L c Q RF hchar) (D.N) + 1 = D.N := by
  have hw := deployed_walkSatD D L c Q RF hchar hadj
  have hterm := count_eq_ln_lastD D L c Q RF hchar hadj
  have hcnt := Walk.count_closed hw (D.N) hw.hpos (le_rfl)
  have hln := Walk.ln_closed hw (D.N) hw.hpos (le_rfl)
  have hpow : alphaC c.1 ^ (1 + Sf (foWD D L c Q RF hchar) (D.N)) =
      alphaC c.1 ^ D.N := by
    rw [pow_add, pow_one, ← hcnt, ← hln]
    exact hterm
  by_contra hne
  exact hα ((mem_computeTilingEvent_iff (foWD D L c Q RF hchar) (D.N) c.1).2
    ⟨hpow, by omega⟩)

end Queue

/-- Compute half of `TracesWalkHyps` at the family remapping (`tracesWalkHyps_compute`). -/
theorem tracesWalkHyps_computeD (Qh : Fin L.w → F[X])
    (RF' : RowFacts D L c (famQ D L c Qh))
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (hadj : D.Adjacent)
    (hα : c.1 ∉ computeTilingEvent (foWD D L c (famQ D L c Qh) RF' hchar) D.N) :
    Sf (foCD D L c Qh) D.N + 1 = D.N ∧ BFSValid (foCD D L c Qh) D.N := by
  have hfo := foW_eq_foC_allD D L c Qh RF' hchar
  have htile := deployed_tilingD D L c (famQ D L c Qh) RF' hchar hadj (by
    simpa [hfo] using hα)
  have hv := deployed_bfsValidD D L c (famQ D L c Qh) RF' hchar hadj
  exact ⟨by simpa [hfo] using htile, by simpa [hfo] using hv⟩

end

end Nock.NockVMROM.Thm54.SVCompute
