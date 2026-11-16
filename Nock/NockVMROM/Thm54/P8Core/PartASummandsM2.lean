/-
  Nock/NockVMROM/Thm54/P8Core/PartASummandsM2.lean

For each such summand: the coin(s), the bad set as a function of the two committed traces and
  the coins it reads directly, the B0 ∪ B1 column congruence of that bad set (so, along a staged
  strategy, `ReadsOn` the M1 coins and the direct reads, `readsOn_of_colCongr₂`), and its uniform
  card bound:

  | # | summand | coin (index) | direct reads | card |
  |---|---|---|---|---|
  | 2 | `famIOEventOf` | `(IOγ, IOpole)` = `(4, 5)` | the nine non-IO coins | `ioFailureUnionBound 10 (3N) M` |
  | 4 | inter pole | `(IOγ, interPole)` = `(4, 9)` | none | `ioFailureUnionBound 10 M M + |𝕂|·M` |
  | 5α | compute walk root, `α`-half | `αC` (0) | `γ, αM, z` | `N` (under tiling) |
  | 5γ | compute walk root, `γ`-half | `γ` (1) | `z` | `9` |
  | 8 | compute prefix-γ | `γ` (1) | none | `9N` |
  | 9 | memory prefix-γ | `γ` (1) | none | `5M` |
  | 10 | memory forest-α | `αW` (11) | `γ` | `M` (under tiling) |

  The topology sub-event of summand 1 (coin `γ`) is `PartATopology12`.
  Scope: the repartitioned schedule and the parallel package only.  -- the paper
-/
import Nock.NockVMROM.Thm54.P8Core.PartASummandsB0

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.PartAStaged

open Nock Nock.Reified Nock.Framework Nock.Framework.Reify Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.RepartitionedStaging
open Nock.NockVMROM.Thm54.PartA12
open scoped Polynomial

noncomputable section

/-! ## 0. -/

theorem goodSrc_round_le (j : ℕ) (h : Unhosted309.goodSrc (.traceCur, j) = true) :
    srcRoundW j ≤ 1 := by
  simp only [Unhosted309.goodSrc, decide_eq_true_eq] at h
  unfold srcRoundW
  rw [newComputeRoleRound_eq]
  split_ifs <;> omega

theorem labelRoles_round_le : ∀ r ∈ PartAB0.labelRoles, newMemoryRoleRound r ≤ 1 := by decide
theorem stateBase_round0 : ∀ b ∈ PartAB0.stateBase, newMemoryColRound b = 0 := by decide
theorem recordRoles_round_le : ∀ r ∈ PartAB0.recordRoles ++ [39], newMemoryRoleRound r ≤ 1 := by
  decide
theorem interBase_round0 : ∀ b ∈ [2, 3, 181], newMemoryColRound b = 0 := by decide

/-- The source expression of compute record slot `c` of request `j` (`rowRecord`'s body). -/
def recExpr (j c : ℕ) : Expr :=
  if c = 9 then (sampledSlotE .traceCur (67 + 8 * j)).subst finalSampledNamespace
  else if c = 6 then (sampledSlotT .traceCur (67 + 8 * j)).subst finalSampledNamespace
  else if c = 8 then (sampledSlotC .traceCur (67 + 8 * j)).subst finalSampledNamespace
  else (computeTraceSubst .traceCur (67 + 8 * j + c)).subst finalSampledNamespace

/-- Every trace read of every compute record slot. -/
def recReads : List (VarKind × ℕ) :=
  (List.range 3).flatMap fun j => (List.range 10).flatMap fun c => Unhosted309.readsE (recExpr j c)


theorem recReads_round_le :
    ∀ q ∈ recReads, (q.1 = .traceCur ∨ q.1 = .traceNext) → srcRoundW q.2 ≤ 1 := by decide +kernel

theorem recExpr_reads (j : Fin 3) (c : Fin 10) :
    ∀ q ∈ Unhosted309.readsE (recExpr j c), q ∈ recReads := by
  intro q hq
  simp only [recReads, List.mem_flatMap, List.mem_range]
  exact ⟨j, j.isLt, c, c.isLt, hq⟩

section Package

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## 1. Family compute environments: trace AND traceNext agreement -/

theorem family_src_agree₂ {s : ℕ} {Qc Qc' : Fin 309 → F[X]} (h : AgreeC309 s Qc Qc')
    (c : OptimizedProductionChallengeTuple K F) (i : Fin P.optimized.family.problem.cfg.compRows)
    (j : ℕ) (hj : srcRoundW j ≤ s) :
    (FamilyEnvCore.rowEnvAt P.optimized c
        (FamilyEnvCore.familyQc P.optimized c (truncQc P Qc)) i).toSourceEnv.traceNext j =
      (FamilyEnvCore.rowEnvAt P.optimized c
        (FamilyEnvCore.familyQc P.optimized c (truncQc P Qc')) i).toSourceEnv.traceNext j := by
  unfold FamilyEnvCore.rowEnvAt
  refine landed_src_traceNext_congr P.optimized.basis j fun col hcol => ?_
  rw [congrFun (FamilyEnvCore.familyQc_envTraceNext P.optimized (truncQc P Qc) c _ _ _ _) col,
    congrFun (FamilyEnvCore.familyQc_envTraceNext P.optimized (truncQc P Qc') c _ _ _ _) col]
  exact (trunc_base_trace P h _ _ _ _ col (Or.inl ((physOf_round_le j col hcol).trans hj))).2

/-! ## 2. Summand 2: the family IO event, pair `(IOγ, IOpole)` -/

theorem rowRecord_eq_recExpr (env : CorrectedFinalTypedEnv F K) (j : Fin 3) (c : Fin 10) :
    OptimizedComputeHostileAccumulator.rowRecord env j c = (recExpr j c).eval env.toSourceEnv := by
  unfold OptimizedComputeHostileAccumulator.rowRecord recExpr
  split_ifs <;> rfl

/-- The compute request list at a family environment reads B0 ∪ B1 only. -/
theorem hostileRequestsAt_B01 {Qc Qc' : Fin 309 → F[X]} (h : AgreeC309 1 Qc Qc')
    (c : OptimizedProductionChallengeTuple K F) :
    FamilyEnvCore.hostileRequestsAt P.optimized c (FamilyEnvCore.familyQc P.optimized c (truncQc P Qc)) =
      FamilyEnvCore.hostileRequestsAt P.optimized c
        (FamilyEnvCore.familyQc P.optimized c (truncQc P Qc')) := by
  unfold FamilyEnvCore.hostileRequestsAt
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  have hbase : (FamilyEnvCore.rowEnvAt P.optimized c
      (FamilyEnvCore.familyQc P.optimized c (truncQc P Qc)) i).baseTrace =
      (FamilyEnvCore.rowEnvAt P.optimized c
        (FamilyEnvCore.familyQc P.optimized c (truncQc P Qc')) i).baseTrace := by
    funext k
    have := family_src_agree P h c i k (by unfold srcRoundW; simp [k.isLt])
    simpa [CorrectedFinalTypedEnv.toSourceEnv, k.isLt] using this
  have hmask := fun j => FamilyEnvCore.activeMask_congr hbase j
  have hrec : ∀ j, OptimizedComputeHostileAccumulator.rowRecord (FamilyEnvCore.rowEnvAt P.optimized c
      (FamilyEnvCore.familyQc P.optimized c (truncQc P Qc)) i) j =
      OptimizedComputeHostileAccumulator.rowRecord (FamilyEnvCore.rowEnvAt P.optimized c
        (FamilyEnvCore.familyQc P.optimized c (truncQc P Qc')) i) j := by
    intro j; funext cc
    rw [rowRecord_eq_recExpr, rowRecord_eq_recExpr]
    apply Unhosted309.eval_congr_reads
    rintro ⟨k, n⟩ hq
    have hr := recReads_round_le _ (recExpr_reads j cc _ hq)
    cases k
    · exact family_src_agree P h c i n (hr (Or.inl rfl))
    · exact family_src_agree₂ P h c i n (hr (Or.inr rfl))
    · rfl
    · rfl
  unfold OptimizedComputeHostileAccumulator.rowRequests
  simp only [hmask, hrec]

/-- The memory response list at a family environment reads B0 ∪ B1 only. -/
theorem hostileResponsesAt_B01 {Qm Qm' : Fin P.memoryChip.rap.w → F[X]} (h : AgreeM P 1 Qm Qm')
    (c : OptimizedProductionChallengeTuple K F) :
    FamilyEnvCore.hostileResponsesAt P.optimized c (FamilyEnvCore.familyQm P.optimized c Qm) =
      FamilyEnvCore.hostileResponsesAt P.optimized c (FamilyEnvCore.familyQm P.optimized c Qm') := by
  unfold FamilyEnvCore.hostileResponsesAt
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  simp only [FamilyEnvCore.memEnvK, FamilyEnvCore.memEnvF, FamilyEnvCore.honestQm_familyQm]
  apply PartAB0.rowResponses_congr'
  · intro r hr
    exact (memorySourceEnv_agree P h i r ((recordRoles_round_le r hr).trans le_rfl)).1
  · exact (memoryBaseEnv_agree P h i 181 (by decide)).1

/-- **Summand 2's records read B0 ∪ B1 only**, at every rest of coins. -/
theorem famR_B01 {Qc Qc' : Fin 309 → F[X]} {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hC : AgreeC309 1 Qc Qc') (hM : AgreeM P 1 Qm Qm') (r : FamilyEnvCore.Rest K) :
    FamilyEnvCore.famR P.optimized (truncQc P Qc) Qm r = FamilyEnvCore.famR P.optimized (truncQc P Qc') Qm' r := by
  unfold FamilyEnvCore.famR FamilyEnvCore.hostileRecordsAt
  rw [hostileRequestsAt_B01 P hC, hostileResponsesAt_B01 P hM]

/-- Summand 2's bad pair set on the coin vector. -/
def bad2 (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) (x : Fin 12 → K) : Finset (K × K) :=
  FiniteIO.IOFailureEvent (FamilyEnvCore.famR P.optimized (truncQc P Qc) Qm (restOfVec x))

theorem bad2_coins (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    ReadsOn (C := K) ({0, 1, 2, 3, 6, 7, 8, 9, 10} : Finset (Fin 12)) (bad2 P Qc Qm) :=
  summand2_readsOn P (truncQc P Qc) Qm

theorem bad2_card (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) (x : Fin 12 → K) :
    (bad2 P Qc Qm x).card ≤
      FiniteIO.ioFailureUnionBound 10 (3 * P.optimized.family.problem.cfg.compRows)
        P.optimized.family.problem.cfg.memRows (Fintype.card K) :=
  (FiniteIO.IOFailureEvent_card_le _).trans
    (ioFailureUnionBound_mono₂ 10 _ _ _ _ (Fintype.card K)
      (FamilyEnvCore.hostileRequestsAt_length_le P.optimized _ _)
      (FamilyEnvCore.hostileResponsesAt_length_le P.optimized _ _))

theorem mem_summand2 (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) (x : Fin 12 → K)
    (h : tuple12OfVec (F := F) x ∈ cyl12 (P.famIOEventOf (truncQc P Qc) Qm)) :
    (x 4, x 5) ∈ bad2 P Qc Qm x := by
  have := (summand2_eq_cylinder₂ P (truncQc P Qc) Qm (tuple12OfVec x)).1 h
  rw [landedVec12_tuple12OfVec] at this
  simpa [cylinder₂, bad2] using this

/-! ## 3. Summand 4: the internal pole, pair `(IOγ, interPole)` -/

/-- Summand 4's bad pair set (fixed by the committed memory trace). -/
def bad4 (Qm : Fin P.memoryChip.rap.w → F[X]) : Finset (K × K) :=
  interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm)

theorem bad4_B01 {Qm Qm' : Fin P.memoryChip.rap.w → F[X]} (h : AgreeM P 1 Qm Qm') :
    bad4 P Qm = bad4 P Qm' := by
  unfold bad4
  rw [PartAB0.tie4, PartAB0.tie4]
  apply PartAB0.summand4_envLocal
  · intro i r hr
    exact (memorySourceEnv_agree P h i r
      (recordRoles_round_le r (List.mem_append_left _ hr))).1
  · intro i b hb
    exact (memoryBaseEnv_agree P h i b (by rw [interBase_round0 b hb]; exact Nat.zero_le _)).1

theorem bad4_card (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (bad4 P Qm).card ≤ FiniteIO.ioFailureUnionBound 10 P.optimized.family.problem.cfg.memRows
      P.optimized.family.problem.cfg.memRows (Fintype.card K) +
        Fintype.card K * P.optimized.family.problem.cfg.memRows := by
  unfold bad4 interFailurePairs
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ ?_
  · exact (FiniteIO.IOFailureEvent_card_le (P.hostileInterRecords Qm)).trans
      (ioFailureUnionBound_mono₂ 10 (P.hostileInterRecords Qm).requests.length
        (P.hostileInterRecords Qm).responses.length _ _ (Fintype.card K)
        (P.hostileInterReads_length_le Qm) (P.hostileInterVerifies_length_le Qm))
  · have hcov : allRowPoleHitEvent (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) ⊆
        (Finset.univ : Finset K).biUnion (fun γ =>
          ({γ} : Finset K) ×ˢ
            FiniteIO.IOPoleHitEvent
              ⟨List.ofFn (fun i =>
                OptimizedMemoryHostileAccumulator.rowRecord (P.memorySourceEnv Qm i)
                  (P.memoryBaseEnv Qm i)), []⟩ γ) := by
      intro q hq
      simp only [allRowPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      refine Finset.mem_biUnion.mpr ⟨q.1, Finset.mem_univ _, ?_⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, hq⟩
    refine (Finset.card_le_card hcov).trans ?_
    refine (Finset.card_biUnion_le (s := (Finset.univ : Finset K))
      (t := fun γ => ({γ} : Finset K) ×ˢ
        FiniteIO.IOPoleHitEvent
          ⟨List.ofFn (fun i =>
            OptimizedMemoryHostileAccumulator.rowRecord (P.memorySourceEnv Qm i)
              (P.memoryBaseEnv Qm i)), []⟩ γ)).trans ?_
    have hsum : ∀ γ ∈ (Finset.univ : Finset K),
        (({γ} : Finset K) ×ˢ
          FiniteIO.IOPoleHitEvent
            ⟨List.ofFn (fun i =>
              OptimizedMemoryHostileAccumulator.rowRecord (P.memorySourceEnv Qm i)
                (P.memoryBaseEnv Qm i)), []⟩ γ).card ≤ P.optimized.family.problem.cfg.memRows := by
      intro γ _
      rw [Finset.card_product, Finset.card_singleton, one_mul]
      exact (FiniteIO.IOPoleHitEvent_card_le _ γ).trans (by simp [List.length_ofFn])
    refine (Finset.sum_le_sum hsum).trans ?_
    simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem mem_summand4 (Qm : Fin P.memoryChip.rap.w → F[X]) (x : Fin 12 → K)
    (h : tuple12OfVec (F := F) x ∈ cyl12 (liftInterPoleFailure (F := F) (bad4 P Qm))) :
    (x 4, x 9) ∈ bad4 P Qm := by
  have := (summand4_eq_cylinder₂ (bad4 P Qm) (tuple12OfVec x)).1 h
  rw [landedVec12_tuple12OfVec] at this
  simpa [cylinder₂] using this

/-! ## 4. Summand 5: the compute walk root, two halves -/

/-- The committed compute table of a truncated trace. -/
abbrev cenvs (Qc : Fin 309 → F[X]) : Fin P.optimized.family.problem.cfg.compRows → Env K :=
  P.computeSourceEnv (truncQc P Qc)

theorem cenvs_decoders_B01 {Qc Qc' : Fin 309 → F[X]} (h : AgreeC309 1 Qc Qc')
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    ComputeWalkRootEvents.rowLabelVec (cenvs P Qc i) = ComputeWalkRootEvents.rowLabelVec (cenvs P Qc' i) ∧
      (∀ l, ComputeWalkRootEvents.rowChildVec (cenvs P Qc i) l =
        ComputeWalkRootEvents.rowChildVec (cenvs P Qc' i) l) ∧
      ComputeWalkRootEvents.rowFanout (cenvs P Qc i) = ComputeWalkRootEvents.rowFanout (cenvs P Qc' i) := by
  apply Unhosted309.decoders_congr_good
  rintro ⟨k, j⟩ hq
  cases k
  · exact (computeSourceEnv_agree P h i j (goodSrc_round_le j hq)).1
  all_goals simp [Unhosted309.goodSrc] at hq

/-- The claim's label at seed `z`. -/
abbrev uClaim (z : K) : Fin 10 → K :=
  ComputeWalkSeed.claimLabelVec z P.optimized.verifier.raw.claim

/-- Summand 5's `α`-half bad set (coin `αC`, index 0; reads `γ`, `αM`, `z`). -/
def bad5a (Qc : Fin 309 → F[X]) (x : Fin 12 → K) : Finset K :=
  if Walk.Sf (ComputeWalkRootEvents.foOf (cenvs P Qc)) P.optimized.family.problem.cfg.compRows + 1 =
      P.optimized.family.problem.cfg.compRows then
    ComputeWalkRootEvents.alphaBadAt (cenvs P Qc) (uClaim P) (x 1) (x 2, x 3)
  else ∅

/-- Summand 5's `γ`-half bad set (coin `γ`, index 1; reads `z`). -/
def bad5g (Qc : Fin 309 → F[X]) (x : Fin 12 → K) : Finset K :=
  ComputeWalkRootEvents.gammaBadOf (uClaim P (x 3))
    (ComputeWalkRootEvents.rowLabelVec (cenvs P Qc ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩))

theorem bad5a_B01 {Qc Qc' : Fin 309 → F[X]} (h : AgreeC309 1 Qc Qc') : bad5a P Qc = bad5a P Qc' := by
  obtain ⟨hc, hl, hf⟩ := Unhosted309.operands_congr (cenvs_decoders_B01 P h)
  funext x
  unfold bad5a ComputeWalkRootEvents.alphaBadAt
  rw [hc, hl, hf]

theorem bad5g_B01 {Qc Qc' : Fin 309 → F[X]} (h : AgreeC309 1 Qc Qc') : bad5g P Qc = bad5g P Qc' := by
  funext x
  unfold bad5g
  rw [(cenvs_decoders_B01 P h _).1]

theorem bad5a_coins (Qc : Fin 309 → F[X]) : ReadsOn (C := K) ({1, 2, 3} : Finset (Fin 12)) (bad5a P Qc) := by
  intro x y h
  unfold bad5a
  rw [h 1 (by simp), h 2 (by simp), h 3 (by simp)]

theorem bad5g_coins (Qc : Fin 309 → F[X]) : ReadsOn (C := K) ({3} : Finset (Fin 12)) (bad5g P Qc) := by
  intro x y h
  unfold bad5g
  rw [h 3 (by simp)]

theorem bad5a_card (Qc : Fin 309 → F[X]) (x : Fin 12 → K) :
    (bad5a P Qc x).card ≤ ComputeWalkRootEvents.walkAlphaRootBound P.optimized.family.problem.cfg.compRows := by
  unfold bad5a
  split_ifs with ht
  · exact ComputeWalkRootEvents.alphaBadAt_card_le_of_tiling _ _ _ _ ht
  · simp

theorem bad5g_card (Qc : Fin 309 → F[X]) (x : Fin 12 → K) :
    (bad5g P Qc x).card ≤ ComputeWalkRootEvents.walkRootGammaBound :=
  ComputeWalkRootEvents.gammaBadOf_card_le _ _

theorem mem_summand5 (Qc : Fin 309 → F[X]) (x : Fin 12 → K)
    (h : tuple12OfVec (F := F) x ∈ cyl12 (liftP8Failure (F := F) (P.computeWalkRootEvent (truncQc P Qc)))) :
    x 0 ∈ bad5a P Qc x ∨ x 1 ∈ bad5g P Qc x := by
  rw [mem_cyl12_liftP8] at h
  simp only [OptimizedFullStrictNockVMROMPackage.computeWalkRootEvent,
    ComputeWalkRootEvents.rootEvent, Finset.mem_union] at h
  rcases h with h | h
  · left
    unfold ComputeWalkRootEvents.alphaRootEventConsumed at h
    unfold bad5a
    split_ifs at h with ht
    · simp only [ComputeWalkRootEvents.alphaRootEvent, Finset.mem_filter, Finset.mem_univ,
        true_and] at h
      rw [if_pos ht]
      exact h
    · simp at h
  · right
    rw [ComputeWalkRootEvents.mem_gammaRootEvent_iff] at h
    exact h

/-- **Summand 5 = L2's event at the 309 chip** (the six walk columns are read by no summand):
the parallel package's event is `computeWalkRootEvent309`. -/
theorem summand5_eq309 (Qc : Fin 309 → F[X]) :
    P.computeWalkRootEvent (truncQc P Qc) = Unhosted309.computeWalkRootEvent309 P Qc := by
  unfold OptimizedFullStrictNockVMROMPackage.computeWalkRootEvent Unhosted309.computeWalkRootEvent309
  apply Unhosted309.rootEvent_congr
  · intro i
    apply Unhosted309.decoders_congr_good
    rintro ⟨k, j⟩ hq
    cases k
    · show (P.computeSourceEnv (truncQc P Qc) i).trace j = (Unhosted309.computeSourceEnv309 P Qc i).trace j
      have hj := goodSrc_round_le j hq
      have h303 : j ≠ 303 ∧ j ≠ 306 := by
        simp only [Unhosted309.goodSrc, decide_eq_true_eq] at hq; omega
      simp only [Unhosted309.computeSourceEnv309, Unhosted309.Env309.toSourceEnv, Unhosted309.gather309,
        if_neg h303.1, if_neg h303.2]
      exact landed_src_trace_congr P.optimized.basis j fun col hcol => by
        simp only [OptimizedFullStrictNockVMROMPackage.computeBaseEnv, Unhosted309.computeBaseEnv309,
          envOfTrace]
        have hr := (physOf_round_le j col hcol).trans hj
        have hc : col < 303 := by
          by_contra hc; unfold newComputeColRound at hr; split_ifs at hr <;> omega
        have hw : col < P.computeChip.rap.w := by rw [computeWidth303]; exact hc
        rw [dif_pos hw, dif_pos (by omega : col < 309)]
        rfl
    all_goals simp [Unhosted309.goodSrc] at hq
  · rfl

/-! ## 5. Summand 8: the compute prefix-γ -/

/-- Summand 8's bad set (coin `γ`; reads no coin). -/
def bad8 (Qc : Fin 309 → F[X]) : Finset K :=
  prefixBadGammas (WalkPrefixGammaEvents.committedComputeV (cenvs P Qc))
    (WalkPrefixGammaEvents.committedComputeCv (cenvs P Qc))
    (ComputeWalkRootEvents.foOf (cenvs P Qc)) P.optimized.family.problem.cfg.compRows

theorem bad8_B01 {Qc Qc' : Fin 309 → F[X]} (h : AgreeC309 1 Qc Qc') : bad8 P Qc = bad8 P Qc' := by
  have hd := cenvs_decoders_B01 P h
  have hV : WalkPrefixGammaEvents.committedComputeV (cenvs P Qc) =
      WalkPrefixGammaEvents.committedComputeV (cenvs P Qc') := by
    funext i; unfold WalkPrefixGammaEvents.committedComputeV; split_ifs
    · rw [(hd _).1]
    · rfl
  have hCv : WalkPrefixGammaEvents.committedComputeCv (cenvs P Qc) =
      WalkPrefixGammaEvents.committedComputeCv (cenvs P Qc') := by
    funext i l; unfold WalkPrefixGammaEvents.committedComputeCv; split_ifs
    · rw [(hd _).2.1]
    · rfl
  have hfo := (Unhosted309.operands_congr hd).2.2
  unfold bad8
  rw [hV, hCv, hfo]

theorem bad8_card (Qc : Fin 309 → F[X]) :
    (bad8 P Qc).card ≤ WalkPrefixGammaEvents.computePrefixGammaBound P.optimized.family.problem.cfg.compRows := by
  refine (prefixBadGammas_card_le (node_size := 10) _ _ _ _).trans ?_
  simp only [WalkPrefixGammaEvents.computePrefixGammaBound]
  omega

theorem mem_summand8 (Qc : Fin 309 → F[X]) (x : Fin 12 → K)
    (h : tuple12OfVec (F := F) x ∈ cyl12 (liftP8Failure (F := F) (P.computePrefixGammaEventOf (truncQc P Qc)))) :
    x 1 ∈ bad8 P Qc := by
  rw [mem_cyl12_liftP8] at h
  exact (WalkPrefixGammaEvents.computePrefixGammaEventOf_eq_prefix _ _).1 h

/-- **Summand 8 = L2's event at the 309 chip.** -/
theorem summand8_eq309 (Qc : Fin 309 → F[X]) :
    P.computePrefixGammaEventOf (truncQc P Qc) = Unhosted309.computePrefixGammaEventOf309 P Qc := by
  unfold OptimizedFullStrictNockVMROMPackage.computePrefixGammaEventOf
    Unhosted309.computePrefixGammaEventOf309
  apply Unhosted309.prefixGamma_congr
  intro i
  apply Unhosted309.decoders_congr_good
  rintro ⟨k, j⟩ hq
  cases k
  · show (P.computeSourceEnv (truncQc P Qc) i).trace j = (Unhosted309.computeSourceEnv309 P Qc i).trace j
    have hj := goodSrc_round_le j hq
    have h303 : j ≠ 303 ∧ j ≠ 306 := by
      simp only [Unhosted309.goodSrc, decide_eq_true_eq] at hq; omega
    simp only [Unhosted309.computeSourceEnv309, Unhosted309.Env309.toSourceEnv, Unhosted309.gather309,
      if_neg h303.1, if_neg h303.2]
    exact landed_src_trace_congr P.optimized.basis j fun col hcol => by
      simp only [OptimizedFullStrictNockVMROMPackage.computeBaseEnv, Unhosted309.computeBaseEnv309,
        envOfTrace]
      have hr := (physOf_round_le j col hcol).trans hj
      have hc : col < 303 := by
        by_contra hc; unfold newComputeColRound at hr; split_ifs at hr <;> omega
      have hw : col < P.computeChip.rap.w := by rw [computeWidth303]; exact hc
      rw [dif_pos hw, dif_pos (by omega : col < 309)]
      rfl
  all_goals simp [Unhosted309.goodSrc] at hq

/-! ## 6. Summands 9 and 10: the memory prefix-γ and forest-α (on `αW`) -/

abbrev menvK (Qm : Fin P.memoryChip.rap.w → F[X]) := P.memorySourceEnv Qm
abbrev menvF (Qm : Fin P.memoryChip.rap.w → F[X]) := P.memoryBaseEnv Qm

theorem menvs_B01 {Qm Qm' : Fin P.memoryChip.rap.w → F[X]} (h : AgreeM P 1 Qm Qm') :
    WalkPrefixGammaEvents.committedMemoryV (menvK P Qm) (menvF P Qm) =
        WalkPrefixGammaEvents.committedMemoryV (menvK P Qm') (menvF P Qm') ∧
      WalkPrefixGammaEvents.committedMemoryCv (menvK P Qm) =
        WalkPrefixGammaEvents.committedMemoryCv (menvK P Qm') ∧
      WalkTilingEvents.foOfMem (menvF P Qm) = WalkTilingEvents.foOfMem (menvF P Qm') :=
  PartAB0.VCvfo_congr
    (fun i r hr => (memorySourceEnv_agree P h i r (labelRoles_round_le r hr)).1)
    (fun i b hb => (memoryBaseEnv_agree P h i b
      (by rw [stateBase_round0 b hb]; exact Nat.zero_le _)).1)

/-- Summand 9's bad set (coin `γ`; reads no coin). -/
def bad9 (Qm : Fin P.memoryChip.rap.w → F[X]) : Finset K :=
  forestPrefixBadGammas (WalkPrefixGammaEvents.committedMemoryV (menvK P Qm) (menvF P Qm))
    (WalkPrefixGammaEvents.committedMemoryCv (menvK P Qm)) (WalkTilingEvents.foOfMem (menvF P Qm))
    P.optimized.family.problem.cfg.kMem P.optimized.family.problem.cfg.memRows

theorem bad9_B01 {Qm Qm' : Fin P.memoryChip.rap.w → F[X]} (h : AgreeM P 1 Qm Qm') :
    bad9 P Qm = bad9 P Qm' := by
  obtain ⟨h1, h2, h3⟩ := menvs_B01 P h
  unfold bad9; rw [h1, h2, h3]

theorem bad9_card (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (bad9 P Qm).card ≤ WalkPrefixGammaEvents.memoryPrefixGammaBound P.optimized.family.problem.cfg.memRows := by
  refine (forestPrefixBadGammas_card_le (node_size := 6) _ _ _ _ _).trans ?_
  simp only [WalkPrefixGammaEvents.memoryPrefixGammaBound]
  omega

theorem mem_summand9 (Qm : Fin P.memoryChip.rap.w → F[X]) (x : Fin 12 → K)
    (h : tuple12OfVec (F := F) x ∈ cyl12 (liftP8Failure (F := F) (P.memoryPrefixGammaEventOf Qm))) :
    x 1 ∈ bad9 P Qm := by
  rw [mem_cyl12_liftP8] at h
  exact (WalkPrefixGammaEvents.memoryPrefixGammaEventOfEnvs_eq_prefix _ _ _ _).1 h

/-- Summand 10's bad set (coin `αW`, index 11; reads `γ`, index 1). -/
def bad10 (Qm : Fin P.memoryChip.rap.w → F[X]) (x : Fin 12 → K) : Finset K :=
  if P.optimized.family.problem.cfg.kMem + Walk.Sf (WalkTilingEvents.foOfMem (menvF P Qm))
      P.optimized.family.problem.cfg.memRows = P.optimized.family.problem.cfg.memRows then
    WalkForestPrefixAlphaEvents.alphaBadAt
      (WalkPrefixGammaEvents.committedMemoryV (menvK P Qm) (menvF P Qm))
      (WalkPrefixGammaEvents.committedMemoryCv (menvK P Qm)) (WalkTilingEvents.foOfMem (menvF P Qm))
      P.optimized.family.problem.cfg.kMem P.optimized.family.problem.cfg.memRows (x 1)
  else ∅

theorem bad10_B01 {Qm Qm' : Fin P.memoryChip.rap.w → F[X]} (h : AgreeM P 1 Qm Qm') :
    bad10 P Qm = bad10 P Qm' := by
  obtain ⟨h1, h2, h3⟩ := menvs_B01 P h
  funext x; unfold bad10; rw [h1, h2, h3]

theorem bad10_coins (Qm : Fin P.memoryChip.rap.w → F[X]) :
    ReadsOn (C := K) ({1} : Finset (Fin 12)) (bad10 P Qm) := by
  intro x y h
  unfold bad10
  rw [h 1 (by simp)]

theorem bad10_card (Qm : Fin P.memoryChip.rap.w → F[X]) (x : Fin 12 → K) :
    (bad10 P Qm x).card ≤
      WalkForestPrefixAlphaEvents.memoryForestAlphaBound P.optimized.family.problem.cfg.memRows := by
  unfold bad10
  split_ifs with ht
  · exact WalkForestPrefixAlphaEvents.alphaBadAt_card_le_of_tiling _ _ _ _ _ _ ht
  · simp

theorem mem_summand10 (Qm : Fin P.memoryChip.rap.w → F[X]) (x : Fin 12 → K)
    (h : tuple12OfVec (F := F) x ∈ liftWalkWFailure (F := F) (P.memoryForestAlphaEventOf Qm)) :
    x 11 ∈ bad10 P Qm x := by
  rw [mem_liftWalkWFailure] at h
  simp only [OptimizedFullStrictNockVMROMPackage.memoryForestAlphaEventOf,
    WalkForestPrefixAlphaEvents.memoryForestAlphaEventOfEnvs,
    WalkForestPrefixAlphaEvents.memoryForestAlphaEventConsumed] at h
  unfold bad10
  split_ifs at h with ht
  · rw [if_pos ht]
    simp only [WalkForestPrefixAlphaEvents.memoryForestAlphaEvent, Finset.mem_filter,
      Finset.mem_univ, true_and] at h
    exact h
  · simp at h

end Package

end

end Nock.NockVMROM.Thm54.PartAStaged
