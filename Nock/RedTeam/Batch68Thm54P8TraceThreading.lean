import Nock.NockVMROM.Thm54.OptimizedStrictFullPackageConcrete
import Nock.RedTeam.Batch67Thm54OptimizedStrictFullPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame: the paper;
consumed capstone: the paper.

This artifact does not judge the paper construction.  It preserves the compiled pre-repair
factorization that found the missing link, then records the production repair's mandatory whole
problem equality and the concrete seed-2 rejection.
-/

namespace Nock.RedTeam.Batch68

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness

noncomputable section

structure TraceAcceptanceAt
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (r : (K × K) × (FinalComputeChallengeTuple K × MemoryChallengeTuple K)) : Prop where
  sampled_io_coins :
    r.1 = (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole)
  compute_satisfies : RAP.SatisfiesWithPreprocessing P.computeChip Qc
  memory_satisfies : RAP.SatisfiesWithPreprocessing P.memoryChip Qm

/-- The factorization theorems — the
point of the batch — are unchanged in shape. -/
structure PreRepairOptimizedProductionAcceptanceAt
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) : Prop where
  p8 : P.strategy.Accepts c.1 c.2.2.2.lambda
  sampled_io_coins :
    c.2.1 = (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole)
  compute_satisfies : RAP.SatisfiesWithPreprocessing P.computeChip Qc
  memory_satisfies : RAP.SatisfiesWithPreprocessing P.memoryChip Qm

/-- The repaired production acceptance has the additional mandatory `OptimizedSameProblemAt` factor. -/
theorem acceptance_factors_without_execution_link
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (j : JointCoins K)
    (r : (K × K) × (FinalComputeChallengeTuple K × MemoryChallengeTuple K)) :
    PreRepairOptimizedProductionAcceptanceAt P Qc Qm (j, r) ↔
      P.strategy.Accepts j r.2.2.lambda ∧ TraceAcceptanceAt P Qc Qm r := by
  constructor
  · intro h
    exact ⟨h.p8,
      { sampled_io_coins := h.sampled_io_coins
        compute_satisfies := h.compute_satisfies
        memory_satisfies := h.memory_satisfies }⟩
  · rintro ⟨hp8, h⟩
    exact
      { p8 := hp8
        sampled_io_coins := h.sampled_io_coins
        compute_satisfies := h.compute_satisfies
        memory_satisfies := h.memory_satisfies }

structure TraceTargetAt
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (r : (K × K) × (FinalComputeChallengeTuple K × MemoryChallengeTuple K)) : Prop where
  sampled_io : IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs
  sampled_io_event_good : r.1 ∉ FiniteIO.IOFailureEvent P.optimized.sampled.sampled.records
  compute_source :
    ∀ i,
      CorrectedComputeSourceObligations P.optimized.family.problem.cfg.compRows
        (gatherCorrectedFinalTypedEnv P.optimized.basis (P.computeBaseEnv Qc i))
        (P.computeBaseEnv Qc i)
  compute :
    ∀ (i : Fin P.optimized.family.problem.cfg.compRows),
      (i : ℕ) + 1 < P.optimized.family.problem.cfg.compRows →
      CorrectedDecodedTransitionSources
        (gatherCorrectedFinalTypedEnv P.optimized.basis (P.computeBaseEnv Qc i))
  memory :
    ∀ (i : Fin P.optimized.family.problem.cfg.memRows),
      ∀ e ∈ (transitionSources (K := K)),
        Expr.eval (K := K) e (P.memorySourceEnv Qm i) = 0
  compute_collision_good :
    r.2.1 ∉ extensionFinalComputeCollisionEvent (P.computeSourceEnv Qc) (P.computeWalkEnv Qc)
  memory_collision_good :
    r.2.2 ∉ extensionMemoryCollisionEvent (P.memorySourceEnv Qm)
  aggregate_forest_axis : P.optimized.OptimizedSharedMemoryConnective

structure PreRepairOptimizedProductionGenuineTargetAt
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) : Prop where
  p8 : GenuineTargetAt P.strategy P.q P.optimized.Λ c.1 c.2.2.2.lambda
  sampled_io : IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs
  sampled_io_event_good :
    c.2.1 ∉ FiniteIO.IOFailureEvent P.optimized.sampled.sampled.records
  compute_source :
    ∀ i,
      CorrectedComputeSourceObligations P.optimized.family.problem.cfg.compRows
        (gatherCorrectedFinalTypedEnv P.optimized.basis (P.computeBaseEnv Qc i))
        (P.computeBaseEnv Qc i)
  compute :
    ∀ (i : Fin P.optimized.family.problem.cfg.compRows),
      (i : ℕ) + 1 < P.optimized.family.problem.cfg.compRows →
      CorrectedDecodedTransitionSources
        (gatherCorrectedFinalTypedEnv P.optimized.basis (P.computeBaseEnv Qc i))
  memory :
    ∀ (i : Fin P.optimized.family.problem.cfg.memRows),
      ∀ e ∈ (transitionSources (K := K)),
        Expr.eval (K := K) e (P.memorySourceEnv Qm i) = 0
  compute_collision_good :
    c.2.2.1 ∉ extensionFinalComputeCollisionEvent (P.computeSourceEnv Qc) (P.computeWalkEnv Qc)
  memory_collision_good :
    c.2.2.2 ∉ extensionMemoryCollisionEvent (P.memorySourceEnv Qm)
  aggregate_forest_axis : P.optimized.OptimizedSharedMemoryConnective

/-- The repaired production target exports the additional mandatory `OptimizedSameProblemAt` factor. -/
theorem target_factors_without_execution_link
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (j : JointCoins K)
    (r : (K × K) × (FinalComputeChallengeTuple K × MemoryChallengeTuple K)) :
    PreRepairOptimizedProductionGenuineTargetAt P Qc Qm (j, r) ↔
      GenuineTargetAt P.strategy P.q P.optimized.Λ j r.2.2.lambda ∧ TraceTargetAt P Qc Qm r := by
  constructor
  · intro h
    exact ⟨h.p8,
      { sampled_io := h.sampled_io
        sampled_io_event_good := h.sampled_io_event_good
        compute_source := h.compute_source
        compute := h.compute
        memory := h.memory
        compute_collision_good := h.compute_collision_good
        memory_collision_good := h.memory_collision_good
        aggregate_forest_axis := h.aggregate_forest_axis }⟩
  · rintro ⟨hp8, h⟩
    exact
      { p8 := hp8
        sampled_io := h.sampled_io
        sampled_io_event_good := h.sampled_io_event_good
        compute_source := h.compute_source
        compute := h.compute
        memory := h.memory
        compute_collision_good := h.compute_collision_good
        memory_collision_good := h.memory_collision_good
        aggregate_forest_axis := h.aggregate_forest_axis }

/-- Repaired
acceptance additionally carries `h.same_problem`; this projection intentionally forgets it. -/
theorem batch67_challenge_pins_are_trace_side_only
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (j : JointCoins K)
    (r : (K × K) × (FinalComputeChallengeTuple K × MemoryChallengeTuple K))
    (h : P.OptimizedHistoricalAcceptanceAt Qc Qm (j, r)) :
    TraceAcceptanceAt P Qc Qm r :=
  { sampled_io_coins := h.sampled_io_coins
    compute_satisfies := h.compute_satisfies
    memory_satisfies := h.memory_satisfies }

/-- The repaired acceptance exports the whole package problem equality together with the exact
optimized-family cfg equality and dependent execution `HEq`. -/
theorem repaired_acceptance_exports_same_problem
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    specializedProblem P.optimized.verifier.raw.timestamp
          (nprSeed c.1) h.same_problem.nprSeed_ne (alphaM c.1) c.2.2.2.lambda =
        { cfg := P.objects.cfg, exec := P.objects.exec } ∧
      (specializedProblem P.optimized.verifier.raw.timestamp
          (nprSeed c.1) h.same_problem.nprSeed_ne (alphaM c.1) c.2.2.2.lambda).cfg =
        P.optimized.family.problem.cfg ∧
      HEq
        (specializedProblem P.optimized.verifier.raw.timestamp
          (nprSeed c.1) h.same_problem.nprSeed_ne (alphaM c.1) c.2.2.2.lambda).exec
        P.optimized.family.problem.exec :=
  ⟨h.same_problem.specialized_eq_objects,
    h.same_problem.specialized_cfg_eq_family,
    h.same_problem.specialized_exec_heq_family⟩

/-! The production acceptance is the two family-chip
satisfactions and the target carries neither `p8` nor `same_problem` (the disclosed p8 gap).  The
acceptance receipts above are restated against `OptimizedHistoricalAcceptanceAt` (the pre-2a
acceptance, verbatim); `repaired_target_exports_same_problem` and
`repaired_connective_preserves_same_problem` were deleted: the field they project is gone. -/

open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.Concrete

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

def alternateSeed : K73cubic := 2

theorem alternateSeed_ne : alternateSeed ≠ 0 := by
  simpa [alternateSeed] using
    concreteOptimizedFullStrictPackage.optimized.two_ne_zero

/-- the paper: concrete seed-substitution witness.
The same production verifier is specializable at seed `2`, while the optimized family and
`objects.cfg` are fixed at the honest seed `1`; the two configurations are unequal. -/
theorem concrete_seed2_specialization_differs_from_optimized_family :
    let P := concreteOptimizedFullStrictPackage
    (specializedProblem P.optimized.verifier.raw.timestamp
      alternateSeed alternateSeed_ne honestAlpha MemoryTable.formRDefault).cfg ≠ P.optimized.family.problem.cfg ∧
    (specializedProblem P.optimized.verifier.raw.timestamp
      alternateSeed alternateSeed_ne honestAlpha MemoryTable.formRDefault).cfg ≠ P.objects.cfg := by
  let P := concreteOptimizedFullStrictPackage
  have hobjects :
      (specializedProblem P.optimized.verifier.raw.timestamp
        alternateSeed alternateSeed_ne honestAlpha MemoryTable.formRDefault).cfg ≠ P.objects.cfg := by
    change
      (ConcreteStrictPackage.cfg alternateSeed honestAlpha) ≠
        (ConcreteStrictPackage.cfg ConcreteStrictPackage.honestSeed honestAlpha)
    intro h
    have hz := congrArg
      (fun c : ExactConfig F73 K73cubic => c.challenges.z) h
    have hz' : (2 : K73cubic) = 1 := by
      simpa only [ConcreteStrictPackage.cfg, alternateSeed,
        ConcreteStrictPackage.honestSeed] using hz
    have hzero : (1 : K73cubic) = 0 := by
      calc
        (1 : K73cubic) = 2 - 1 := by ring
        _ = 1 - 1 := by rw [hz']
        _ = 0 := by ring
    exact one_ne_zero hzero
  refine ⟨?_, hobjects⟩
  intro hfamily
  exact hobjects (hfamily.trans P.optimized.family_cfg)

def alternateJointCoins : JointCoins K73cubic :=
  ((honestAlphaC, honestGamma), (honestAlpha, alternateSeed))

def alternateProductionChallenge :
    OptimizedProductionChallengeTuple K73cubic F73 :=
  (alternateJointCoins, concreteProductionChallenge.2)

/-- The contradiction is the mandatory whole-problem equality, not a new
probabilistic failure event. -/
theorem concrete_seed2_mismatch_rejected_by_repaired_acceptance :
    ¬ concreteOptimizedFullStrictPackage.OptimizedHistoricalAcceptanceAt
      concreteComputeTrace concreteMemoryTrace alternateProductionChallenge := by
  intro hacc
  have hcfg :=
    congrArg RawProblem.cfg hacc.same_problem.specialized_eq_objects
  have hl : concreteProductionChallenge.2.2.2.lambda = MemoryTable.formRDefault :=
    hacc.same_problem.lam_eq
  exact concrete_seed2_specialization_differs_from_optimized_family.2 (by
    have hcfg' := hcfg
    simp only [alternateProductionChallenge, alternateJointCoins,
      alternateSeed, nprSeed, alphaM] at hcfg'
    rw [hl] at hcfg'
    exact hcfg')

#print axioms acceptance_factors_without_execution_link
#print axioms target_factors_without_execution_link
#print axioms batch67_challenge_pins_are_trace_side_only
#print axioms repaired_acceptance_exports_same_problem
#print axioms concrete_seed2_specialization_differs_from_optimized_family
#print axioms concrete_seed2_mismatch_rejected_by_repaired_acceptance

end
end Nock.RedTeam.Batch68
