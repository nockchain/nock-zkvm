/-
  Nock/NockVMROM/Thm54/P8Core/PartASummandsB0.lean

  **H2.1 for the consumed summands whose coin is in message M1
  (or that read the base block only), at the parallel package and `repartitionedChronology`.**

  Each summand below is shown to depend on the two committed traces ONLY through their B0 columns
  (round 0 under `newComputeColRound` / `newMemoryColRound`).

  * summand 1, its M1 part (`m1Part`: zero seed, guarded census, envelope axis share, guarded size
    windows; coins `z`, `αM`) — L0's `p8Slot_m1Part_B0` (`AgreeB0`);
  * summand 3, the timestamp collision (coin `αM`) — the request COUNT reads the activity masks,
    i.e. the base selectors `0..12` (`hostileRequests_length_B0`);
  * summand 6, compute tiling (coin `αC`) — the fanout reads the state selectors (`foOf_B0`);
  * summand 7, memory tiling (coin `αW`) — `foOfMem` reads memory base `0..2`;
  * summand 11, the decoded λ (coins `(αM, λ)`) — L0's `summand11_B0`;
  * summand 14, `α = 0` — reads nothing.

  The bridge from trace-level B0 agreement to L0's env-level `AgreeB0` is `agreeB0_of_trace`.
  Scope: the repartitioned schedule and the parallel package only
-/
import Nock.NockVMROM.Thm54.P8Core.PartAColumnsToEnvs
import Nock.NockVMROM.Thm54.P8Core.PartAB0Locality
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.PartAStaged

open Nock Nock.Reified Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.RepartitionedStaging
open Nock.NockVMROM.Thm54.PartA12
open scoped Polynomial

noncomputable section

section Package

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## 1. Source-level agreement for any gathered family environment -/

/-- Any two base environments whose traces agree on the columns of round `≤ s` (and beyond the
303 landed columns) give gathered source environments agreeing at every source index of round
`≤ s`. -/
theorem gather_src_agree (b : Module.Basis (Fin 3) F K) {s : ℕ} {E₁ E₂ : Env F}
    (h : ∀ c, newComputeColRound c ≤ s ∨ 303 ≤ c → E₁.trace c = E₂.trace c) (j : ℕ)
    (hj : srcRoundW j ≤ s) :
    (gatherCorrectedFinalTypedEnv b E₁).toSourceEnv.trace j =
      (gatherCorrectedFinalTypedEnv b E₂).toSourceEnv.trace j :=
  landed_src_trace_congr b j fun c hc => h c (Or.inl ((physOf_round_le j c hc).trans hj))

/-- The family compute environment at ANY tuple of a truncated trace. -/
theorem family_src_agree {s : ℕ} {Qc Qc' : Fin 309 → F[X]} (h : AgreeC309 s Qc Qc')
    (c : OptimizedProductionChallengeTuple K F) (i : Fin P.optimized.family.problem.cfg.compRows)
    (j : ℕ) (hj : srcRoundW j ≤ s) :
    (FamilyEnvCore.rowEnvAt P.optimized c
        (FamilyEnvCore.familyQc P.optimized c (truncQc P Qc)) i).toSourceEnv.trace j =
      (FamilyEnvCore.rowEnvAt P.optimized c
        (FamilyEnvCore.familyQc P.optimized c (truncQc P Qc')) i).toSourceEnv.trace j := by
  unfold FamilyEnvCore.rowEnvAt
  refine gather_src_agree P.optimized.basis (fun col hcol => ?_) j hj
  rw [congrFun (FamilyEnvCore.familyQc_envTrace P.optimized (truncQc P Qc) c _ _ _ _) col,
    congrFun (FamilyEnvCore.familyQc_envTrace P.optimized (truncQc P Qc') c _ _ _ _) col]
  exact (trunc_base_trace P h _ _ _ _ col hcol).1

/-! ## 2. Trace-level B0 agreement gives L0's `AgreeB0` -/

theorem computeB0Reads_colRound0 : ∀ j ∈ PartAB0.computeB0Reads, newComputeColRound j = 0 := by
  decide

theorem computeB0Reads_srcRound0 : ∀ j ∈ PartAB0.computeB0Reads, srcRoundW j = 0 := by
  decide

theorem preZMemCols_round0 :
    ∀ b ∈ PreZComputeCore.Served.preZMemCols, newMemoryColRound b = 0 := by decide

theorem lamMemReads_round0' : ∀ b ∈ PartAB0.lamMemReads, newMemoryColRound b = 0 := by decide

/-- **The bridge**: B0 agreement of the truncated compute traces and of the memory traces is L0's
row-environment `AgreeB0`. -/
theorem agreeB0_of_trace {Qc Qc' : Fin 309 → F[X]} {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hC : AgreeC309 0 Qc Qc') (hM : AgreeM P 0 Qm Qm') :
    PartAB0.AgreeB0 P.optimized (truncQc P Qc) (truncQc P Qc') Qm Qm' := by
  refine ⟨?_, ?_⟩
  · intro i k hk
    exact family_src_agree P hC _ i k (by rw [computeB0Reads_srcRound0 k hk])
  · intro i b hb
    rw [← OptimizedFailureEventEv.memoryBaseEnv_trace P Qm _ i,
      ← OptimizedFailureEventEv.memoryBaseEnv_trace P Qm' _ i]
    exact (memoryBaseEnv_agree P hM i b (by rw [preZMemCols_round0 b hb])).1

/-! ## 3. The B0 summands, one by one -/

/-- **Summand 1, its M1 part.** -/
theorem summand1_m1_B0 {Qc Qc' : Fin 309 → F[X]} {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hC : AgreeC309 0 Qc Qc') (hM : AgreeM P 0 Qm Qm') (lmb : K) :
    PartAB0.m1Part (OptimizedFailureEventEv.builtStrategyEv P (truncQc P Qc) Qm) P.optimized.Λ lmb =
      PartAB0.m1Part (OptimizedFailureEventEv.builtStrategyEv P (truncQc P Qc') Qm') P.optimized.Λ
        lmb :=
  PartAB0.p8Slot_m1Part_B0 P (agreeB0_of_trace P hC hM) _ lmb

/-- **Summand 3**: the request count reads the base selectors only. -/
theorem hostileRequests_length_B0 {Qc Qc' : Fin 309 → F[X]} (hC : AgreeC309 0 Qc Qc') :
    (P.hostileRequests (truncQc P Qc)).length = (P.hostileRequests (truncQc P Qc')).length := by
  unfold OptimizedFullStrictNockVMROMPackage.hostileRequests
  rw [List.length_flatten, List.length_flatten, List.map_ofFn, List.map_ofFn, List.sum_ofFn,
    List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine FamilyEnvCore.rowRequests_length_congr fun j => FamilyEnvCore.activeMask_congr ?_ j
  funext k
  simp only [gatherCorrectedFinalTypedEnv, OptimizedFullStrictNockVMROMPackage.computeBaseEnv]
  exact (trunc_base_trace P hC _ _ _ _ k (Or.inl (by
    have := k.isLt; unfold newComputeColRound; simp [this]))).1

/-- The compute fanout reads the state selectors `1..10` (B0). -/
theorem foOf_B0 {Qc Qc' : Fin 309 → F[X]} (hC : AgreeC309 0 Qc Qc') :
    ComputeWalkRootEvents.foOf (P.computeSourceEnv (truncQc P Qc)) =
      ComputeWalkRootEvents.foOf (P.computeSourceEnv (truncQc P Qc')) := by
  funext i
  unfold ComputeWalkRootEvents.foOf
  split_ifs with hi
  · simp only [ComputeWalkRootEvents.rowFanout]
    congr 1
    have ht : ∀ j, j < 13 → (P.computeSourceEnv (truncQc P Qc) ⟨i - 1, hi.2⟩).trace j =
        (P.computeSourceEnv (truncQc P Qc') ⟨i - 1, hi.2⟩).trace j := fun j hj =>
      (computeSourceEnv_agree P hC _ j (by unfold srcRoundW; simp [hj])).1
    unfold ComputeWalkRootEvents.rowStateOf
    rw [ht 1 (by omega), ht 2 (by omega), ht 3 (by omega), ht 4 (by omega), ht 5 (by omega),
      ht 6 (by omega), ht 7 (by omega), ht 8 (by omega), ht 9 (by omega), ht 10 (by omega)]
  · rfl

/-- **Summand 6.** -/
theorem summand6_B0 {Qc Qc' : Fin 309 → F[X]} (hC : AgreeC309 0 Qc Qc') :
    P.computeTilingEventOf (truncQc P Qc) = P.computeTilingEventOf (truncQc P Qc') := by
  unfold OptimizedFullStrictNockVMROMPackage.computeTilingEventOf
  rw [foOf_B0 P hC]

/-- The memory fanout reads memory base `0..2` (B0). -/
theorem foOfMem_B0 {Qm Qm' : Fin P.memoryChip.rap.w → F[X]} (hM : AgreeM P 0 Qm Qm') :
    WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm) = WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm') := by
  funext i
  unfold WalkTilingEvents.foOfMem
  split_ifs with hi
  · have ht : ∀ b, b < 3 → (P.memoryBaseEnv Qm ⟨i - 1, hi.2⟩).trace b =
        (P.memoryBaseEnv Qm' ⟨i - 1, hi.2⟩).trace b := fun b hb =>
      (memoryBaseEnv_agree P hM _ b (by unfold newMemoryColRound; simp [show b < 6 by omega])).1
    unfold WalkTilingEvents.memRowStateOf
    rw [ht 0 (by omega), ht 1 (by omega), ht 2 (by omega)]
  · rfl

/-- **Summand 7.** -/
theorem summand7_B0 {Qm Qm' : Fin P.memoryChip.rap.w → F[X]} (hM : AgreeM P 0 Qm Qm') :
    P.memoryTilingEventOf Qm = P.memoryTilingEventOf Qm' := by
  unfold OptimizedFullStrictNockVMROMPackage.memoryTilingEventOf
  rw [foOfMem_B0 P hM]

/-- **Summand 11.** -/
theorem summand11_B0' {Qc Qc' : Fin 309 → F[X]} {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hC : AgreeC309 0 Qc Qc') (hM : AgreeM P 0 Qm Qm') :
    P.decodedLambdaEventOf (truncQc P Qc) Qm = P.decodedLambdaEventOf (truncQc P Qc') Qm' :=
  PartAB0.summand11_B0 P (fun i k hk => (computeSourceEnv_agree P hC i k
      (by rw [computeB0Reads_srcRound0 k hk])).1)
    (fun i b hb => (memoryBaseEnv_agree P hM i b (by rw [lamMemReads_round0' b hb])).1)

/-- **Summand 12.** -/
theorem summand12_B0' {Qc Qc' : Fin 309 → F[X]} {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hC : AgreeC309 0 Qc Qc') (hM : AgreeM P 0 Qm Qm') :
    OptimizedFailureEventEv.reqPairEv P (truncQc P Qc) Qm =
      OptimizedFailureEventEv.reqPairEv P (truncQc P Qc') Qm' :=
  PartAB0.summand12_B0 P (agreeB0_of_trace P hC hM)
    (fun i b hb => (memoryBaseEnv_agree P hM i b (by rw [preZMemCols_round0 b hb])).1)

/-- **Summand 13.** -/
theorem summand13_B0' {Qc Qc' : Fin 309 → F[X]} {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hC : AgreeC309 0 Qc Qc') (hM : AgreeM P 0 Qm Qm') :
    OptimizedFailureEventEv.rootResultEv P (truncQc P Qc) Qm =
      OptimizedFailureEventEv.rootResultEv P (truncQc P Qc') Qm' :=
  PartAB0.summand13_B0 P (agreeB0_of_trace P hC hM)

end Package

end

end Nock.NockVMROM.Thm54.PartAStaged
