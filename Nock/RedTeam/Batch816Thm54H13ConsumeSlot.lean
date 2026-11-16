/-
  Nock/RedTeam/Batch816Thm54H13ConsumeSlot.lean

  * **Q1** `reqPairEventOf_card_le`: `≤ |𝕂|¹⁰ · M·(2Λg − 1)` of the `|𝕂|¹¹` tuples, generic, at
    every `(Qc, Qm)`, NO premise (the guard is inside `pairBadSeeds`; rule 8(b)).
  * **Q2** `pairs_length`: `#pairs = memRows` at every trace.
-/
import Lean
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.PreZCensusCore
import Nock.NockVMROM.Thm54.PreSeedCensusFigures
import Nock.NockVMROM.Thm54.HostileWorkloadMajorant
import Nock.RedTeam.Batch742Thm54RouteBCensus
import Nock.RedTeam.Batch752Thm54PreZCensusCoreLift
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

open Lean Elab Command

namespace Nock.RedTeam.Batch816

open Nock
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.PreSeedCensusFigures
open Nock.NockVMROM.Thm54.HostileWorkloadMajorant
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.Reified
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound

noncomputable section

/-! ## A. -/

section Slot
variable {F K : Type} [Field F] [Field K] [Algebra F K] [CharP K (ringChar K)]

/-- **Option W summand** (trace-uniform, configuration constants only; sits beside
`formRUniformWorkload` inside `workload`). -/
def reqPairWorkload (T : ProductionStrategy F K) (Λ : ℕ) : ℕ :=
  (SemanticStrategy.memorySkeletonRows T.skeleton).length *
    (2 * ((SemanticStrategy.memorySkeletonRows T.skeleton).length ⊔ Λ) - 1)

/-- Negative control (iii): `+ 0`. -/
def reqPairWorkloadPert (T : ProductionStrategy F K) (Λ : ℕ) : ℕ :=
  (SemanticStrategy.memorySkeletonRows T.skeleton).length *
    (2 * ((SemanticStrategy.memorySkeletonRows T.skeleton).length ⊔ Λ) - 1) + 0

end Slot

section Pinned
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- `Λg := memRows ⊔ P.optimized.Λ` — two package fields, so a configuration constant. -/
def pairWindow : ℕ := P.optimized.family.problem.cfg.memRows ⊔ P.optimized.Λ

def reqPairEventOf (Qm : Fin P.memoryChip.rap.w → Polynomial F) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  liftP8Failure (F := F) (reqPairEventOfEnvs K P.q P.optimized.family.problem.cfg.kMem
    (pairWindow P) (P.memoryBaseEnv Qm) P.optimized.family.problem.cfg.memRows_pos
    (requestTargets P.strategy.skeleton))

theorem reqPairEventOf_card_le (Qm : Fin P.memoryChip.rap.w → Polynomial F) :
    (reqPairEventOf P Qm).card ≤
      Fintype.card K ^ 10 *
        (P.optimized.family.problem.cfg.memRows * (2 * pairWindow P - 1)) := by
  have hB := reqPairEventOfEnvs_card_le K P.q P.optimized.family.problem.cfg.kMem
    (pairWindow P) (P.memoryBaseEnv Qm) P.optimized.family.problem.cfg.memRows_pos
    (requestTargets P.strategy.skeleton)
  unfold reqPairEventOf liftP8Failure
  rw [Finset.card_product, Finset.card_univ]
  have hrest :
      Fintype.card ((K × K) × FinalComputeChallengeTuple K × MemoryChallengeTuple K) =
        Fintype.card K ^ 7 := by
    simp only [Fintype.card_prod, card_finalComputeChallengeTuple, card_memoryChallengeTuple]
    ring
  rw [hrest]
  calc _ ≤ P.optimized.family.problem.cfg.memRows * (2 * pairWindow P - 1) *
        Fintype.card K ^ 3 * Fintype.card K ^ 7 := Nat.mul_le_mul_right _ hB
    _ = _ := by ring

theorem reqPairEventOf_card_le_workload (Qm : Fin P.memoryChip.rap.w → Polynomial F) :
    (reqPairEventOf P Qm).card ≤
      Fintype.card K ^ 10 * reqPairWorkload P.strategy P.optimized.Λ := by
  have hcfg : P.optimized.family.problem.cfg =
      P.strategy.specializedCfg P.honestSeed P.honestSeed_ne P.honestAlpha
        P.optimized.objects.cfg.challenges.lam := by
    rw [P.optimized.family_cfg]
    exact (congrArg (fun x => x.cfg) P.honest_specialization).symm
  have hM : P.optimized.family.problem.cfg.memRows =
      (SemanticStrategy.memorySkeletonRows P.strategy.skeleton).length := by
    rw [hcfg]
    have h := (P.optimized.strategy_bindsAll P.honestSeed P.honestSeed_ne P.honestAlpha
      P.optimized.objects.cfg.challenges.lam).memoryRows.length_eq
    rw [ExactExecution.memoryRows_length] at h
    exact h.symm
  have h := reqPairEventOf_card_le P Qm
  unfold reqPairWorkload
  rw [← hM]
  simpa [pairWindow] using h

/-- Q2: `#pairs = memRows` at every trace (the env-level count is the `Fin M` index). -/
theorem pairs_length (Qm : Fin P.memoryChip.rap.w → Polynomial F) :
    (reqPairsOfEnvs K P.q P.optimized.family.problem.cfg.kMem (P.memoryBaseEnv Qm)
      P.optimized.family.problem.cfg.memRows_pos (requestTargets P.strategy.skeleton)).length =
      P.optimized.family.problem.cfg.memRows :=
  reqPairsOfEnvs_length _ _ _ _ _ _

/-! ## B. -/

def optimizedFailureEvent' (Qc : Fin P.computeChip.rap.w → Polynomial F)
    (Qm : Fin P.memoryChip.rap.w → Polynomial F) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  P.optimizedFailureEvent Qc Qm ∪ reqPairEventOf P Qm

/-- The new conjunct `hpair`, exposed on the `JointCoins` component (as `hαM` is). -/
theorem good_components' (Qc : Fin P.computeChip.rap.w → Polynomial F)
    (Qm : Fin P.memoryChip.rap.w → Polynomial F) (c : OptimizedProductionChallengeTuple K F)
    (hgood : c ∉ optimizedFailureEvent' P Qc Qm) :
    c ∉ P.optimizedFailureEvent Qc Qm ∧
      c.1 ∉ reqPairEventOfEnvs K P.q P.optimized.family.problem.cfg.kMem (pairWindow P)
        (P.memoryBaseEnv Qm) P.optimized.family.problem.cfg.memRows_pos
        (requestTargets P.strategy.skeleton) := by
  simp only [optimizedFailureEvent', Finset.mem_union, not_or] at hgood
  refine ⟨hgood.1, fun h => hgood.2 ?_⟩
  exact Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩

theorem notMem_of_components' (Qc : Fin P.computeChip.rap.w → Polynomial F)
    (Qm : Fin P.memoryChip.rap.w → Polynomial F) (c : OptimizedProductionChallengeTuple K F)
    (hold : c ∉ P.optimizedFailureEvent Qc Qm)
    (hpair : c.1 ∉ reqPairEventOfEnvs K P.q P.optimized.family.problem.cfg.kMem (pairWindow P)
        (P.memoryBaseEnv Qm) P.optimized.family.problem.cfg.memRows_pos
        (requestTargets P.strategy.skeleton)) :
    c ∉ optimizedFailureEvent' P Qc Qm := by
  simp only [optimizedFailureEvent', Finset.mem_union, not_or]
  exact ⟨hold, fun h => hpair (Finset.mem_product.mp h).1⟩

/-- Acceptance-to-target is monotone in the event: the larger union keeps the conjunct. -/
theorem acceptance_to_target' (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → Polynomial F)
    (Qm : Fin P.memoryChip.rap.w → Polynomial F) (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedProductionAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.consumedFailureEvent Qc Qm ∪ optimizedFailureEvent' P Qc Qm) :
    P.OptimizedProductionGenuineTargetAt Qc Qm c :=
  P.acceptance_outside_failure_implies_target hax hbasis hwidth Qc Qm c hacc
    (fun h => hgood (Finset.mem_union_left _ h))

theorem cardBound_add_p8 (cardK cardF p8Work w ioWork N M : ℕ) :
    optimizedHostileProductionFailureCardBound cardK cardF (p8Work + w) ioWork N M =
      optimizedHostileProductionFailureCardBound cardK cardF p8Work ioWork N M +
        cardK ^ 10 * w := by
  simp only [optimizedHostileProductionFailureCardBound,
    optimizedTrimmedProductionFailureCardBound]
  ring

theorem falseAcceptance_card_le_records'
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → Polynomial F)
    (Qm : Fin P.memoryChip.rap.w → Polynomial F) :
    (P.OptimizedFalseAcceptanceSet Qc Qm).card ≤
      optimizedHostileProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (OptimizedFailureEventEv.workloadEv P P.optimized.Λ +
          reqPairWorkload P.strategy P.optimized.Λ)
        P.hostileIOWork
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows := by
  rw [cardBound_add_p8]
  exact (P.optimizedFalseAcceptance_card_le_records hax hbasis hwidth Qc Qm).trans (Nat.le_add_right _ _)

/-- The IO slot is `P.hostileIOWork`, the row-count majorant the family IO event
is priced at.) -/
theorem failureEvent'_card_le (Qc : Fin P.computeChip.rap.w → Polynomial F)
    (Qm : Fin P.memoryChip.rap.w → Polynomial F)
    (hold : (P.optimizedFailureEvent Qc Qm).card ≤
      optimizedHostileProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (workload P.strategy P.optimized.Λ
          (fixedTopologyWorkload P.strategy) (fixedAxisWorkload P.strategy))
        P.hostileIOWork
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows) :
    (optimizedFailureEvent' P Qc Qm).card ≤
      optimizedHostileProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (workload P.strategy P.optimized.Λ
          (fixedTopologyWorkload P.strategy) (fixedAxisWorkload P.strategy) +
          reqPairWorkload P.strategy P.optimized.Λ)
        P.hostileIOWork
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows := by
  rw [cardBound_add_p8]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add hold (reqPairEventOf_card_le_workload P Qm))

end Pinned


end

end Nock.RedTeam.Batch816

#print axioms Nock.RedTeam.Batch816.reqPairEventOf_card_le
#print axioms Nock.RedTeam.Batch816.reqPairEventOf_card_le_workload
#print axioms Nock.RedTeam.Batch816.pairs_length
#print axioms Nock.RedTeam.Batch816.acceptance_to_target'
#print axioms Nock.RedTeam.Batch816.failureEvent'_card_le
