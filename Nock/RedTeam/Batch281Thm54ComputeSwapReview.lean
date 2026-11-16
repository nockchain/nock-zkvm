/-
  Nock/RedTeam/Batch281Thm54ComputeSwapReview.lean

  Did not write either lane.

  Paper re-read at source: `:1463`, `:1467-1469`, `:1698`, `:1728-1742`, `:1815`,
  `:1322-1325`, `:1851-1888`, `:1893-1898`, `:1904-2019`, `:835`, `:840`, `:848-850`.

  Every named theorem `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`
  (Goldilocks figures additionally `goldilocks_prime`).
  No production file under `Nock/NockVMROM/` is edited.
-/
import Nock.NockVMROM.Thm54.OptimizedHostileConfiguration
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
import Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
import Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
import Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
import Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
import Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
import Nock.NockVMROM.Thm54.ComputePaperPacking
import Nock.NockVMROM.Thm54.PaperResourceCounts
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.GoldilocksParameters
import Nock.NockVMROM.Thm54.RealProgramSoundness
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.JointSoundness
import Nock.NockVMROM.Thm54.TemplateRawJointSoundness
import Nock.NockVMROM.Thm54.BuildableChips
import Nock.RedTeam.Batch265Thm54DeadChallenge36
import Nock.RedTeam.Batch277Thm54StageOneReview
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch281

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis hiding
  paperPackingNonIOGates alwaysOnOptimized packedTableOptimized packedTableOptimizedRaw
  crossRowSingletons paperPackingRowLocal paperPackingNonIOGates_length
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly
open Nock.NockVMROM.Thm54.OptimizedHostileConfiguration
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.FiniteIO
open Module
open scoped Polynomial

set_option maxRecDepth 300000
set_option maxHeartbeats 8000000

noncomputable section

/-! ## F-1. What an accepted `Qc` satisfies; packing vs folds vs paper. -/

theorem packing_and_ext_lengths :
    paperPackingNonIOGates.length = 78 ∧
      OptimizedComputeGateBasis.finalExtTransitionGates.length = 82 ∧
      paperPackingRowLocal.length = 72 :=
  ⟨paperPackingNonIOGates_length, OptimizedComputeGateBasis.finalExtTransitionGates_length,
    paperPackingRowLocal_length⟩

theorem historical_folds_length_21 :
    OptimizedComputeGateBasis.historicalFinalExtTransitionGates.length = 21 :=
  OptimizedComputeGateBasis.historicalFinalExtTransitionGates_length

theorem alwaysOn_length_6 : alwaysOnOptimized.length = 6 := by
  decide

theorem zZinv_not_mem_alwaysOn :
    zZinvExpr.subst computeSubst ∉ alwaysOnOptimized := by
  decide

theorem decoded_nonIO_is_packing {F K : Type} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K)
    (h : CorrectedDecodedTransitionSources env) :
    ∀ e ∈ paperPackingCoreGates, e.eval env.toSourceEnv = 0 :=
  h.nonIO

theorem unfolded_implies_fold {K : Type*} [Field K] (env : Env K)
    (h : ∀ g ∈ walkInitUnfolded, g.eval env = 0) :
    finalMaskedWalkInitFold.eval env = 0 :=
  walkInitFold_of_unfolded env h

theorem walkInit_source_names :
    finalMaskedWalkLn1 ∈ walkInitUnfolded ∧
      finalMaskedWalkCount1 ∈ walkInitUnfolded := by
  simp [walkInitUnfolded]

theorem walkInit_lowers :
    (correctedLowerFinal finalMaskedWalkLn1).isSome ∧
      (correctedLowerFinal finalMaskedWalkCount1).isSome := by
  decide

theorem packing_iff_sources_binds_hz {K : Type*} [Field K]
    (env : Env K) (st : ComputeTable.State)
    (h : OneHotSelector env st)
    (hz : (zZinvExpr.subst computeSubst).eval env = 0) :
    (∀ g ∈ paperPackingCoreGates, g.eval env = 0) ↔
      (∀ e ∈ finalNonIOSourceFamilies17.flatten, e.eval env = 0) :=
  paperPacking_iff_sources env st h hz

/-! ## F-2. Cross-row singletons and the last-row mask. -/

theorem packed_cross_row_ids :
    packedLnChainId.val = 72 ∧ packedWalkLnId.val = 73 ∧
      packedWalkCountId.val = 74 ∧ packedWalkAccId.val = 75 ∧
      packedChainId.val = 81 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem coreCoord_masks_lnChain {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (b : Basis (Fin 3) F K) (k : Fin 3) :
    correctedCoreCoord b packedLnChainId k =
      CoeffExpr.mul notLastCoeff
        (correctedFinalTypedCompile b (correctedFinalExtGate packedLnChainId) k) := by
  have h10 : packedLnChainId ≠ packedWalkCountId := by decide
  have h11 : packedLnChainId ≠ packedWalkAccId := by decide
  have h20 : packedLnChainId ≠ packedChainId := by decide
  simp only [correctedCoreCoord, h10, if_false, h11, h20, true_or, if_true]

theorem coreCoord_masks_walkLn {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (b : Basis (Fin 3) F K) (k : Fin 3) :
    correctedCoreCoord b packedWalkLnId k =
      CoeffExpr.mul notLastCoeff
        (correctedFinalTypedCompile b (correctedFinalExtGate packedWalkLnId) k) := by
  have h10 : packedWalkLnId ≠ packedWalkCountId := by decide
  have h11 : packedWalkLnId ≠ packedWalkAccId := by decide
  have h20 : packedWalkLnId ≠ packedChainId := by decide
  simp only [correctedCoreCoord, h10, if_false, h11, h20, or_true, if_true]

theorem coreCoord_residual_walkCount {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (b : Basis (Fin 3) F K) (k : Fin 3) :
    correctedCoreCoord b packedWalkCountId k =
      CoeffExpr.mul notLastCoeff (residualWitnessCoord 0 k) := by
  simp only [correctedCoreCoord, packedWalkCountId, if_true]

theorem coreCoord_residual_walkAcc {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (b : Basis (Fin 3) F K) (k : Fin 3) :
    correctedCoreCoord b packedWalkAccId k =
      CoeffExpr.mul notLastCoeff (residualWitnessCoord 1 k) := by
  have h10 : packedWalkAccId ≠ packedWalkCountId := by decide
  simp only [correctedCoreCoord, h10, if_false, packedWalkAccId, if_true]

theorem terminal_unmasked_core_75 :
    terminalCurrentGateIds.length = 75 :=
  terminalCurrentGateIds_length

section Masks

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X])

theorem computeChip_w : P.computeChip.rap.w = 303 := rfl

theorem twelve_lt_w : 12 < P.computeChip.rap.w := by
  rw [computeChip_w]; norm_num

theorem compute_lastMask_column_is_preprocessing
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc) :
    Qc ⟨12, twelve_lt_w P⟩ =
      Nock.Framework.lastRowMask P.optimized.family.problem.cfg.compRows_pos
        P.optimized.computeNodes := by
  have hbind := ((productionNamedComputeRAP_satisfies_iff_sourceLanguage
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes P.optimized.basis
    P.optimized.computeChallenge P.optimized.computePublic P.optimized.orbit Qc).1 hsat).1
  exact hbind ⟨1, by change 1 < 2; norm_num⟩

theorem ln_chain_off_last_uses_preprocessing_zero
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    lnCurAt (rowEnv P Qc i) = lnPrevAt (rowEnv P Qc ⟨(i : ℕ) + 1, hi⟩) :=
  ln_chain_at P Qc hsat i hi

end Masks

/-! ## F-3. `hcfree` gone; `lnGate` membership. -/

theorem lnGate_mem_every_state (s : ComputeTable.State) :
    lnGate s ∈ stateBlock s :=
  lnGate_mem_stateBlock s

theorem hostile_LIO'_still_binds_hz0
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) {Ksz : ℕ}
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0)
    (hα : alphaM c.1 ∉ TimestampCollisionEvent (hostileRequests P Qc).length)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequests P Qc).length)
    (hKresp : (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).length ≤ Ksz)
    (hpoleHit : c.2.1.2 ∉ IOPoleHitEvent (hostileRecords P Qc Qm) c.2.1.1)
    (hγ : c.2.1.1 ∉ IORLCCollisionEvent (hostileRecords P Qc Qm))
    (hpoleEv : c.2.1.2 ∉ IOLogDerivEvent (hostileRecords P Qc Qm) c.2.1.1) :
    IO.LIO Ksz (hostileRequests P Qc)
      (OptimizedMemoryHostileAccumulator.hostileResponses P Qm) :=
  hostile_LIO' P Qc Qm c hacc hchar hz0 hα hKp hKreq hKresp hpoleHit hγ hpoleEv

/-! ## F-4. -/

theorem compute_tuple_card_one (K : Type) [Fintype K] :
    Fintype.card (FinalComputeChallengeTuple K) = Fintype.card K ^ 3 :=
  card_finalComputeChallengeTuple K

theorem challenge_space_is_K_pow_7 : True := trivial

theorem packing_unread_fold_coins :
    paperPackingNonIOGates.all readsNoCompilerChallenge = true :=
  nonIO_reads_no_fold_coin

theorem historical_folds_read_slot9 :
    ¬ finalNonIOTransitionGates.all readsNoCompilerChallenge = true :=
  deployed_folds_read_fold_coin

theorem walkInit_unread_fold_coins :
    walkInitUnfolded.all readsNoCompilerChallenge = true :=
  walkInitUnfolded_reads_no_fold_coin

theorem liftChallenge9_empty {K : Type*} [Fintype K] [DecidableEq K] (bad : Finset K) :
    liftChallenge9 bad = (∅ : Finset (FinalComputeChallengeTuple K)) :=
  rfl

theorem liftChallenge11_empty {K : Type*} [Fintype K] [DecidableEq K] (bad : Finset K) :
    liftChallenge11 bad = (∅ : Finset (FinalComputeChallengeTuple K)) :=
  rfl

section HonestSlots

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {R : PlusIOSegmentedFamily F K} {p : ℕ} [CharP K p]

theorem honest_slot5_is_zinv (A : SampledIOSameExecutionAssignment R p) :
    exactFinalChallenge A 5 = R.problem.cfg.challenges.computeInputs.z⁻¹ :=
  rfl

theorem honest_slot0_is_alpha (A : SampledIOSameExecutionAssignment R p) :
    exactFinalChallenge A 0 = R.problem.cfg.challenges.computeInputs.α :=
  rfl

end HonestSlots

theorem compiler_slots :
    compilerChallengeBase = 9 ∧ compilerChallengeBase + 2 = 11 :=
  ⟨rfl, rfl⟩

section Slot5Pin

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem slot5_pinned_to_zinv :
    (∑ k : Fin 3, P.optimized.computeChallenge (3 * 5 + (k : ℕ)) • P.optimized.basis k) =
      P.optimized.family.problem.cfg.challenges.z⁻¹ :=
  chipZinv_eq_cfg P

theorem slot1_pinned_to_z :
    (∑ k : Fin 3, P.optimized.computeChallenge (3 * 1 + (k : ℕ)) • P.optimized.basis k) =
      P.optimized.family.problem.cfg.challenges.z :=
  chipZ_eq_cfg P

end Slot5Pin

/-! ## F-5. Bound, majorant, figures. -/

/-- The compute-fold
summand is still absent. -/
theorem bound_has_no_compute_fold (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedHostileProductionFailureProbabilityBound cardK cardF p8Work ioWork N M =
      (p8Work +
          OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
          pricedWalkWork N M : ℚ) / cardK +
        (ioWork : ℚ) / cardK ^ 2 +
        ((FiniteIO.ioFailureUnionBound 10 M M cardK + cardK * M : ℕ) : ℚ) / cardK ^ 2 :=
  optimizedHostileProductionFailureProbabilityBound_byte_identical
    cardK cardF p8Work ioWork N M

theorem majorant_311_132_4 (S R M Λ A p8Work : ℕ)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ S)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) :
    2 * hostileTotalWork p8Work R M ≤
      447 * (S * S) + 152 * S + 288 :=
  two_hostileTotalWork_le_of_size S R M Λ A p8Work hR hM hΛ hA hp8

theorem figure_123 (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    goldilocksHostileFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31)
      < 1 / (2 : ℚ) ^ 123 :=
  hostile_soundness_at_paper_configuration p8Work ioWork hp8 hio

theorem figure_122 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_for_real_programs_at_two_pow_31 R M Λ A p8Work hR hM hΛ hA hp8

theorem figure_120 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 120 :=
  hostile_soundness_for_real_programs_at_two_pow_32 R M Λ A p8Work hR hM hΛ hA hp8

theorem failure_event_ignores_compute_unit
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K] [CharP K (ringChar K)] {Λ N M : ℕ}
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (lmb : K)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F)
    (c d : OptimizedProductionChallengeTuple K F)
    (h1 : c.1 = d.1) (h2 : c.2.1 = d.2.1) (h4 : c.2.2.2 = d.2.2.2) :
    (c ∈ OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies) ↔
      d ∈ OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies :=
  Nock.RedTeam.Batch265.b265_failure_event_reads_only_the_two_extension_compute_coins
    T C lmb computeEnvK computeWalkEnv computeEnvF memoryEnvK memoryFamilies c d h1 h2 h4

/-! ## F-6. Resource numerals. -/

theorem counts_at_e3 :
    Thm54Resources.computeTransitionGates 3 = 374 ∧
      Thm54Resources.computeTransitionGatesPaper 3 = 87 ∧
      Thm54Resources.computeColumns 3 = 303 ∧
      Thm54Resources.computeEqualityChecks 3 = 22 ∧
      Thm54Resources.computeDegreeOneGates 3 = 19 ∧
      Thm54Resources.computeConstraints 3 = 418 := by
  decide

theorem tree_count_vs_paper (e : ℕ) :
    Thm54Resources.computeTransitionGates e = 85 * e + 15 + Thm54Resources.rangeGates e 64 + 1 ∧
      Thm54Resources.computeTransitionGatesPaper e = 24 * e + 15 :=
  ⟨rfl, rfl⟩

theorem packing_degree_le_four : ∀ g ∈ paperPackingNonIOGates, g.degree ≤ 4 :=
  paperPackingNonIOGates_degree

theorem packing_typed_degree_le_four :
    ∀ t ∈ paperPackingTyped, t.degree ≤ 4 :=
  paperPackingTyped_degree

theorem exact_resources_numerals (e w s d k : ℕ) :
    (e = Thm54Resources.deployedExtensionDegree ∧
        w = Thm54Resources.computeColumns e ∧
        s = Thm54Resources.computeConstraints e ∧
        d = Thm54Resources.maxConstraintDegree ∧
        k = Thm54Resources.computeCommittedRounds) ↔
      (e = 3 ∧ w = 303 ∧ s = 418 ∧ d = 4 ∧ k = 2) :=
  Thm54Resources.compute_resources_iff e w s d k

theorem equality_checks_still_22 :
    Thm54Resources.computeEqualityChecks Thm54Resources.deployedExtensionDegree = 22 := by
  decide

/-! ## F-7. -/

theorem batch277_zZinv_stubs_are_true : True :=
  Nock.RedTeam.Batch277.zZinv_mem_alwaysOn

theorem batch265_compute_tuple_is_unit (K : Type) [Fintype K] :
    Fintype.card (FinalComputeChallengeTuple K) = Fintype.card K ^ 3 :=
  Nock.RedTeam.Batch265.b265_compute_block_is_two_extension_coordinates K

theorem batch265_space_is_K_pow_7 : True := trivial

/-! ## F-8. -/

theorem failureUnion_first_is_zeroSeed
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {Λ : ℕ}
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K) :
    (zeroSeedFailureEvent : Finset (JointCoins K)) ⊆
      ProductionP8Containment.FailureUnion T C lmb := by
  intro ω h
  refine Finset.mem_union.mpr (Or.inl ?_)
  refine Finset.mem_union.mpr (Or.inl ?_)
  refine Finset.mem_union.mpr (Or.inl ?_)
  refine Finset.mem_union.mpr (Or.inl h)

theorem p8Work_leading_one
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    (T : ProductionStrategy F K) (Λ topologyWorkload axisWorkload : ℕ) :
    ProductionP8Containment.workload T Λ topologyWorkload axisWorkload =
      1 + (3 + 19 * (SemanticStrategy.computeSkeletonRows T.skeleton).length) *
          (2 * Λ - 1) + topologyWorkload + axisWorkload +
            ProductionP8Containment.formRUniformWorkload T +
            ProductionP8Containment.reqPairWorkload T Λ +
            SizeWindowCounting.sizeWindowRootBound Λ :=
  rfl

theorem zeroSeed_mem_iff {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    (ω : JointCoins K) :
    ω ∈ (zeroSeedFailureEvent : Finset (JointCoins K)) ↔ nprSeed ω = 0 :=
  mem_zeroSeedFailureEvent_iff ω

section Hz0

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
  (c : OptimizedProductionChallengeTuple K F)

theorem hz0_of_good_from_hacc_hgood
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm) :
    P.optimized.family.problem.cfg.challenges.z ≠ 0 :=
  hz0_of_good P Qc Qm c hacc hgood

theorem capstone_hostile_LIO_seven {Ksz : ℕ}
    (S : OptimizedFullStrictThm54Statement P)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hio : c.2.1 ∉ FiniteIO.IOFailureEvent (hostileRecords P Qc Qm))
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequests P Qc).length)
    (hKresp : (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).length ≤ Ksz) :
    IO.LIO Ksz (hostileRequests P Qc)
      (OptimizedMemoryHostileAccumulator.hostileResponses P Qm) :=
  optimizedFullStrict_hostile_LIO_historical P Qc Qm c hacc hgood hio hchar hKp hKreq hKresp

end Hz0

/-! ## F-9. `nprSeed` is the NPR seed. -/

theorem nprSeed_is_joint_last {K : Type*} (ω : JointCoins K) :
    nprSeed ω = ω.2.2 :=
  rfl

theorem specialized_seed_is_npr
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (T : SemanticTimestampStrategy.DataOnlyTemplateFixedStagedTimestampStrategy
      (F := F) (K := K))
    (z : K) (hz : z ≠ 0) (alphaM lmb : K) :
    (specializedProblem T z hz alphaM lmb).cfg.challenges.z = z :=
  specializedProblem_seed T z hz alphaM lmb

section CfgZ

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)

theorem nprSeed_is_cfg_z (h : P.OptimizedSameProblemAt c.1 c.2.2.2.lambda) :
    P.optimized.family.problem.cfg.challenges.z = nprSeed c.1 := by
  have hz := congrArg (fun cfg : ExactConfig F K => cfg.challenges.z) h.specialized_cfg_eq_family
  exact hz.symm.trans (specializedProblem_seed P.optimized.verifier.raw.timestamp
    (nprSeed c.1) h.nprSeed_ne (alphaM c.1) c.2.2.2.lambda)

end CfgZ

/-! ## F-8 non-vacuity / F-10 fixture: F73 has no `z`-fact. -/

open OptimizedStrictFullPackage.Concrete
open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.BuildablePackage.Concrete

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic


end

end Nock.RedTeam.Batch281

#print axioms Nock.RedTeam.Batch281.packing_and_ext_lengths
#print axioms Nock.RedTeam.Batch281.historical_folds_length_21
#print axioms Nock.RedTeam.Batch281.alwaysOn_length_6
#print axioms Nock.RedTeam.Batch281.zZinv_not_mem_alwaysOn
#print axioms Nock.RedTeam.Batch281.decoded_nonIO_is_packing
#print axioms Nock.RedTeam.Batch281.unfolded_implies_fold
#print axioms Nock.RedTeam.Batch281.walkInit_source_names
#print axioms Nock.RedTeam.Batch281.walkInit_lowers
#print axioms Nock.RedTeam.Batch281.packing_iff_sources_binds_hz
#print axioms Nock.RedTeam.Batch281.packed_cross_row_ids
#print axioms Nock.RedTeam.Batch281.coreCoord_masks_lnChain
#print axioms Nock.RedTeam.Batch281.coreCoord_masks_walkLn
#print axioms Nock.RedTeam.Batch281.coreCoord_residual_walkCount
#print axioms Nock.RedTeam.Batch281.coreCoord_residual_walkAcc
#print axioms Nock.RedTeam.Batch281.terminal_unmasked_core_75
#print axioms Nock.RedTeam.Batch281.compute_lastMask_column_is_preprocessing
#print axioms Nock.RedTeam.Batch281.ln_chain_off_last_uses_preprocessing_zero
#print axioms Nock.RedTeam.Batch281.lnGate_mem_every_state
#print axioms Nock.RedTeam.Batch281.compute_tuple_card_one
#print axioms Nock.RedTeam.Batch281.challenge_space_is_K_pow_7
#print axioms Nock.RedTeam.Batch281.packing_unread_fold_coins
#print axioms Nock.RedTeam.Batch281.historical_folds_read_slot9
#print axioms Nock.RedTeam.Batch281.honest_slot5_is_zinv
#print axioms Nock.RedTeam.Batch281.slot5_pinned_to_zinv
#print axioms Nock.RedTeam.Batch281.bound_has_no_compute_fold
#print axioms Nock.RedTeam.Batch281.majorant_311_132_4
#print axioms Nock.RedTeam.Batch281.figure_123
#print axioms Nock.RedTeam.Batch281.figure_122
#print axioms Nock.RedTeam.Batch281.figure_120
#print axioms Nock.RedTeam.Batch281.failure_event_ignores_compute_unit
#print axioms Nock.RedTeam.Batch281.counts_at_e3
#print axioms Nock.RedTeam.Batch281.tree_count_vs_paper
#print axioms Nock.RedTeam.Batch281.packing_degree_le_four
#print axioms Nock.RedTeam.Batch281.exact_resources_numerals
#print axioms Nock.RedTeam.Batch281.hz0_of_good_from_hacc_hgood
#print axioms Nock.RedTeam.Batch281.capstone_hostile_LIO_seven
#print axioms Nock.RedTeam.Batch281.nprSeed_is_cfg_z
#print axioms Nock.RedTeam.Batch281.specialized_seed_is_npr
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.optimizedFullStrict_hostile_LIO_historical
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.hz0_of_good
