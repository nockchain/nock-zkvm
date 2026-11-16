/-
  Nock/NockVMROM/Thm54/P8Core/Batch489Thm54FoOfEqFoW.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch489Thm54FoOfEqFoW`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch489Thm54FoOfEqFoW.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch465Thm54DeployedRootLabelEqClaim
import Nock.NockVMROM.Thm54.P8Core.WalkQueueDeployed
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch489

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.RedTeam.Batch459
open Nock.RedTeam.Batch465
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
variable (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
variable (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
variable (hchar : MemStateTagChar F)
variable (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
variable (hbasis : FormRBasis P.optimized.basis)
variable (hwidth : FormRWidth F)
include hsatC

/-- `Sf` of the consumed compute fanout equals `Sf` of the chip column. -/
theorem Sf_foOf_eq_foW :
    Sf (foOf (P.computeSourceEnv Qc₀)) (rows P) =
      Sf (Batch459.foW P c (familyQc P c Qc₀) hsatC) (rows P) := by
  refine Finset.sum_congr rfl fun i hi => ?_
  have hii : 1 ≤ i ∧ i ≤ rows P := Finset.mem_Icc.mp hi
  exact Batch465.foOf_eq_foW P c Qc₀ hsatC i hii.1 hii.2

/-- The consumed compute tiling Finset is the chip theorem's Finset. -/
theorem computeTilingEventOf_eq_foW :
    P.computeTilingEventOf Qc₀ =
      WalkTilingEvents.computeTilingEvent
        (Batch459.foW P c (familyQc P c Qc₀) hsatC) (rows P) := by
  apply Finset.ext
  intro ω
  simp only [OptimizedFullStrictNockVMROMPackage.computeTilingEventOf,
    WalkTilingEvents.mem_computeTilingEvent_iff,
    Sf_foOf_eq_foW P c Qc₀ hsatC]

omit hsatC

/-- Package `memoryBaseEnv` and family `memoryBaseEnvAt` share selector columns. -/
theorem memoryBaseEnv_trace_eq
    (i : Fin (memRows P)) :
    (P.memoryBaseEnv Qm₀ i).trace = (memoryBaseEnvAt P c Qm₀ i).trace := by
  funext j
  simp only [OptimizedFullStrictNockVMROMPackage.memoryBaseEnv,
    FamilyComputeRows.memoryBaseEnvAt, envOfTrace]

/-- `memRowStateOf` of the consumed memory env is the chip's `stAt`. -/
theorem memRowStateOf_eq_stAt
    (i : Fin (memRows P)) :
    memRowStateOf (P.memoryBaseEnv Qm₀ i) =
      MemoryWalkDeployed.stAt P c (familyQm P c Qm₀) i := by
  have htr := memoryBaseEnv_trace_eq P c Qm₀ i
  have hhonest : honestQm P c (familyQm P c Qm₀) = Qm₀ :=
    WalkQueueDeployed.honestQm_familyQm P c Qm₀
  unfold MemoryWalkDeployed.stAt MemoryWalkDeployed.envF MemoryWalkDeployed.Qmh
  rw [hhonest]
  unfold memRowStateOf StrategyOfTraces.memoryStateOf
  rw [htr]

/-- Memory twin of `Batch465::foOf_eq_foW`. -/
theorem foOfMem_eq_foWmem (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ memRows P) :
    foOfMem (P.memoryBaseEnv Qm₀) i =
      MemoryWalkDeployed.foW P c (familyQm P c Qm₀) i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < memRows P := by omega
  have hpos : 1 ≤ k + 1 ∧ k + 1 - 1 < P.optimized.family.problem.cfg.memRows := by
    refine ⟨by omega, ?_⟩
    simpa [memRows, Nat.add_sub_cancel] using hk
  unfold foOfMem
  rw [dif_pos hpos]
  have hrow : MemoryWalkDeployed.rowOf P (k + 1) = ⟨k, hk⟩ :=
    MemoryWalkDeployed.rowOf_succ P k hk
  unfold MemoryWalkDeployed.foW
  rw [hrow, MemoryWalkDeployed.pubAt_st]
  have hst := memRowStateOf_eq_stAt P c Qm₀ ⟨k, hk⟩
  simp only [Nat.add_sub_cancel] at hst ⊢
  exact congrArg fanoutMem hst

/-- `Sf` of the consumed memory fanout equals `Sf` of the chip column. -/
theorem Sf_foOfMem_eq_foWmem :
    Sf (foOfMem (P.memoryBaseEnv Qm₀)) (memRows P) =
      Sf (MemoryWalkDeployed.foW P c (familyQm P c Qm₀)) (memRows P) := by
  refine Finset.sum_congr rfl fun i hi => ?_
  have hii : 1 ≤ i ∧ i ≤ memRows P := Finset.mem_Icc.mp hi
  exact foOfMem_eq_foWmem P c Qm₀ i hii.1 hii.2

/-- The consumed memory tiling Finset is the chip theorem's Finset. -/
theorem memoryTilingEventOf_eq_foWmem :
    P.memoryTilingEventOf Qm₀ =
      WalkTilingEvents.memoryTilingEvent
        (MemoryWalkDeployed.foW P c (familyQm P c Qm₀))
        P.optimized.family.problem.cfg.kMem (memRows P) := by
  apply Finset.ext
  intro ω
  simp only [OptimizedFullStrictNockVMROMPackage.memoryTilingEventOf,
    WalkTilingEvents.mem_memoryTilingEvent_iff,
    Sf_foOfMem_eq_foWmem P c Qm₀]

include hsatC hsatM hchar
include hax hbasis hwidth

/-- `c ∉ optimizedFailureEvent` discharges both tiling exclusions, hence
`TracesWalkHyps`.  Chip satisfaction and `MemStateTagChar` are the queue
theorems' existing hypotheses, not new walk hyps. -/
theorem tracesWalkHyps_of_failureEvent
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀) :
    TracesWalkHyps P Qc₀ Qm₀ c := by
  have hc := P.optimizedFailureEvent_good_components Qc₀ Qm₀ c hgood
  have htileC : c.1 ∉ P.computeTilingEventOf Qc₀ := hc.2.2.2.2.2.1
  have htileM : c.1 ∉ P.memoryTilingEventOf Qm₀ := hc.2.2.2.2.2.2.1
  have hC : c.1 ∉ WalkTilingEvents.computeTilingEvent
      (Batch459.foW P c (familyQc P c Qc₀) hsatC) (rows P) := by
    rwa [← computeTilingEventOf_eq_foW P c Qc₀ hsatC]
  have hM : c.1 ∉ WalkTilingEvents.memoryTilingEvent
      (MemoryWalkDeployed.foW P c (familyQm P c Qm₀))
      P.optimized.family.problem.cfg.kMem (memRows P) := by
    rwa [← memoryTilingEventOf_eq_foWmem P c Qm₀]
  exact tracesWalkHyps_of_chips P c Qc₀ Qm₀ hsatC hsatM hchar hax hbasis hwidth hC hM

/-- Same conclusion from `DeployedAcceptanceAt` at the family remapping. -/
theorem tracesWalkHyps_of_deployed
    (hacc : DeployedAcceptanceAt P c (familyQc P c Qc₀) (familyQm P c Qm₀))
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀) :
    TracesWalkHyps P Qc₀ Qm₀ c :=
  tracesWalkHyps_of_failureEvent P c Qc₀ Qm₀ hacc.compute_satisfies
    hacc.memory_satisfies hchar hax hbasis hwidth hgood

end

end Nock.RedTeam.Batch489
