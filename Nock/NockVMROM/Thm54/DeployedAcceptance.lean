import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.P8Core.DeployedAcceptance

/-!
# `DeployedAcceptance`: what the deployed chips check

Acceptance at the consumed chips is `RAP.SatisfiesWithPreprocessing` of both tables, plus the
coin-slot pins the chips actually read, and nothing else (no `p8`, no `same_problem`).
`DeployedAcceptanceAt` is the same two conjuncts at the family chips `computeChipAt c` /
`memoryChipAt c`, with no pin fields.  Its traces are typed at the family-chip width, so the kernel
need not unify `P.computeChip.rap.w` with `(P.computeChipAt c).rap.w` (those projections mention
different `chalVal` terms; the values are both `199` / `196`).

The public equality checks are already gates: `finalEndpointEqualityChecks`
(`OptimizedComputeFinal.lean`) are the last 22 members of `correctedFinalComputeAllGates`, which is
the compute chip's committed list (`OptimizedComputeCorrectedFinal.lean`).
`CorrectedComputeSourceObligations.selectorEquality2` reads them off `compute_satisfies`
(`row_obligations`).  The memory chip's public bindings are part of its own gates, so no further
binding field is needed (`finalEndpointEqualityChecks_mem_allGates`).
-/

open Nock Nock.NockVMROM Nock.NockVMROM.Thm54
namespace Nock.Walk37

namespace Nock.NockVMROM.Thm54

open scoped Polynomial
open Polynomial
open Nock.Framework
open OptimizedStrictPackage
open OptimizedStrictFullPackage
open OptimizedComputeCorrectedFinal
open OptimizedComputeFinal

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-- The capstone acceptance is `DeployedAcceptanceAt` at the reindexed package traces. -/
theorem deployedAcceptanceAt_iff_acceptance
    {P : OptimizedFullStrictNockVMROMPackage F K hOrb}
    {c : OptimizedProductionChallengeTuple K F}
    {Qc : Fin P.computeChip.rap.w → F[X]}
    {Qm : Fin P.memoryChip.rap.w → F[X]} :
    DeployedAcceptanceAt P c (P.familyQc c Qc) (P.familyQm c Qm) ↔
      P.OptimizedProductionAcceptanceAt Qc Qm c :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- From the capstone acceptance to the family predicate. -/
theorem DeployedAcceptanceAt.of_acceptance
    {P : OptimizedFullStrictNockVMROMPackage F K hOrb}
    {c : OptimizedProductionChallengeTuple K F}
    {Qc : Fin P.computeChip.rap.w → F[X]}
    {Qm : Fin P.memoryChip.rap.w → F[X]}
    (h : P.OptimizedProductionAcceptanceAt Qc Qm c) :
    DeployedAcceptanceAt P c (P.familyQc c Qc) (P.familyQm c Qm) :=
  deployedAcceptanceAt_iff_acceptance.2 h

/-- Both *constant* chips plus the three coin-slot pins: acceptance
without `p8` and `same_problem`.  For the family chips use `DeployedAcceptanceAt`. -/
structure DeployedAcceptance
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) : Prop where
  compute_satisfies :
    RAP.SatisfiesWithPreprocessing P.computeChip Qc
  memory_satisfies :
    RAP.SatisfiesWithPreprocessing P.memoryChip Qm
  sampled_io_coins :
    c.2.1 =
      (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole)
  memory_sampled_coins :
    ∀ i, (P.memorySourceEnv Qm i).chal 4 = c.2.1.1 ∧
      (P.memorySourceEnv Qm i).chal 5 = c.2.1.2
  memory_intermediate_pole :
    ∀ i, (P.memorySourceEnv Qm i).chal 6 = c.2.2.2.interPole

/-- Constructor: family satisfaction is exactly the two fields. -/
theorem DeployedAcceptanceAt.mk'
    {P : OptimizedFullStrictNockVMROMPackage F K hOrb}
    {c : OptimizedProductionChallengeTuple K F}
    {Qc : Fin (P.computeChipAt c).rap.w → F[X]}
    {Qm : Fin (P.memoryChipAt c).rap.w → F[X]}
    (hc : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (hm : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm) :
    DeployedAcceptanceAt P c Qc Qm :=
  ⟨hc, hm⟩


namespace OptimizedStrictFullPackage
namespace OptimizedFullStrictNockVMROMPackage

open OptimizedStrictPackage ProductionP8Containment RawSemanticAssembly SemanticStrategy
open OptimizedComputeCollisionBound OptimizedMemoryCollisionAccounting
set_option linter.overlappingInstances false

variable (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

structure OptimizedHistoricalAcceptanceAt
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) : Prop where
  p8 : P.strategy.Accepts c.1 c.2.2.2.lambda
  same_problem : P.OptimizedSameProblemAt c.1 c.2.2.2.lambda
  sampled_io_coins :
    c.2.1 =
      (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole)
  memory_sampled_coins :
    ∀ i, (P.memorySourceEnv Qm i).chal 4 = c.2.1.1 ∧ (P.memorySourceEnv Qm i).chal 5 = c.2.1.2
  memory_intermediate_pole :
    ∀ i, (P.memorySourceEnv Qm i).chal 6 = c.2.2.2.interPole
  compute_satisfies :
    RAP.SatisfiesWithPreprocessing P.computeChip Qc
  memory_satisfies :
    RAP.SatisfiesWithPreprocessing P.memoryChip Qm

structure OptimizedHistoricalTraceAcceptanceAt
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (r : (K × K) × (FinalComputeChallengeTuple K × MemoryChallengeTuple K)) : Prop where
  sampled_io_coins :
    r.1 = (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole)
  memory_sampled_coins :
    ∀ i, (P.memorySourceEnv Qm i).chal 4 = r.1.1 ∧ (P.memorySourceEnv Qm i).chal 5 = r.1.2
  memory_intermediate_pole :
    ∀ i, (P.memorySourceEnv Qm i).chal 6 = r.2.2.interPole
  compute_satisfies : RAP.SatisfiesWithPreprocessing P.computeChip Qc
  memory_satisfies : RAP.SatisfiesWithPreprocessing P.memoryChip Qm

theorem optimizedHistoricalAcceptanceAt_iff
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (j : JointCoins K)
    (r : (K × K) × (FinalComputeChallengeTuple K × MemoryChallengeTuple K)) :
    P.OptimizedHistoricalAcceptanceAt Qc Qm (j, r) ↔
      P.strategy.Accepts j r.2.2.lambda ∧ P.OptimizedSameProblemAt j r.2.2.lambda ∧
        P.OptimizedHistoricalTraceAcceptanceAt Qc Qm r := by
  constructor
  · intro h
    exact ⟨h.p8, h.same_problem,
      { sampled_io_coins := h.sampled_io_coins
        memory_sampled_coins := h.memory_sampled_coins
        memory_intermediate_pole := h.memory_intermediate_pole
        compute_satisfies := h.compute_satisfies
        memory_satisfies := h.memory_satisfies }⟩
  · rintro ⟨hp8, hsame, h⟩
    exact
      { p8 := hp8
        same_problem := hsame
        sampled_io_coins := h.sampled_io_coins
        memory_sampled_coins := h.memory_sampled_coins
        memory_intermediate_pole := h.memory_intermediate_pole
        compute_satisfies := h.compute_satisfies
        memory_satisfies := h.memory_satisfies }

theorem sampled_io_event_good_of_historical
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    c.2.1 ∉ FiniteIO.IOFailureEvent P.optimized.sampled.sampled.records := by
  rw [hacc.sampled_io_coins]
  exact P.optimized.sampled.sampled.coins_not_failure

theorem sampled_inter_event_good_of_historical
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hC : P.optimized.family.problem.exec.CprimeCoherent) :
    (c.2.1.1, c.2.2.2.interPole) ∉
      FiniteIO.IOFailureEvent P.optimized.sampled.interRecords := by
  have hγ : c.2.1.1 = P.optimized.sampled.sampled.coins.gamma :=
    congrArg Prod.fst hacc.sampled_io_coins
  have hpole : c.2.2.2.interPole = P.optimized.sampled.interPole := by
    have h := hacc.memory_intermediate_pole
      ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩
    have hpin := P.memorySourceEnv_inter_pole Qm
      ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩
    rw [hpin] at h
    exact h.symm.trans P.packageInterPole_eq_sampled
  rw [hγ, hpole]
  exact P.optimized.sampled.inter_coins_not_failure P.optimized.pairedRecordLayout hC

end OptimizedFullStrictNockVMROMPackage
end OptimizedStrictFullPackage

open OptimizedStrictFullPackage in
theorem deployedAcceptance_of_historical
    {P : OptimizedFullStrictNockVMROMPackage F K hOrb}
    {Qc : Fin P.computeChip.rap.w → F[X]}
    {Qm : Fin P.memoryChip.rap.w → F[X]}
    {c : OptimizedProductionChallengeTuple K F}
    (h : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    DeployedAcceptance P Qc Qm c where
  compute_satisfies := h.compute_satisfies
  memory_satisfies := h.memory_satisfies
  sampled_io_coins := h.sampled_io_coins
  memory_sampled_coins := h.memory_sampled_coins
  memory_intermediate_pole := h.memory_intermediate_pole

/-- Every `finalEndpointEqualityChecks` gate is a member of the compute
chip's committed list, so no extra public-binding field is needed. -/
theorem finalEndpointEqualityChecks_mem_allGates
    {n : ℕ} (b : Module.Basis (Fin 3) F K) :
    ∀ g ∈ (finalEndpointEqualityChecks (F := F)),
      g ∈ correctedFinalComputeAllGates n b := by
  intro g hg
  simp only [correctedFinalComputeAllGates, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr hg)))

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.finalEndpointEqualityChecks_mem_allGates

end Nock.Walk37
