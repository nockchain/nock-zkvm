/-
  Nock/NockVMROM/Thm54/P8Core/Batch409Thm54SeedBoundaryKside.lean

  The
  remaining declarations stay in `Nock/RedTeam/Batch409Thm54SeedBoundaryKside.lean`, which imports this module. This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`. -/
import Nock.NockVMROM.Thm54.P8Core.Batch408Thm54SeedBoundaryGates
import Nock.NockVMROM.Thm54.P8Core.FamilyMemoryRows

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch409

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Reified.Trans
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.RedTeam.Batch408
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem rootMaskCounts_mem_mixed (b : Module.Basis (Fin 3) F K) :
    rootMaskCountsGate (F := F) ∈ mixedTransitionGates (F := F) (K := K) b := by
  refine List.mem_append_left _ ?_
  change rootMaskCountsGate (F := F) ∈ paperKGates (F := F)
  exact Batch408.rootMaskCountsGate_mem

theorem rootMaskIndicator_mem_mixed (b : Module.Basis (Fin 3) F K) :
    rootMaskIndicatorGate (F := F) ∈ mixedTransitionGates (F := F) (K := K) b := by
  refine List.mem_append_left _ ?_
  change rootMaskIndicatorGate (F := F) ∈ paperKGates (F := F)
  exact Batch408.rootMaskIndicatorGate_mem

section DeployedZero

variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
  [CharP K (ringChar K)]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
  (i : Fin P.optimized.family.problem.cfg.memRows)
  (hi : (i : ℕ) < P.optimized.family.problem.cfg.kMem)
include hsat hi

/-- Hostile: on any trace the family chip accepts, every masked root row has
    `pt.counts = 0` and `pt.indicator = 0`. -/
theorem deployed_root_accumulators_zero :
    (memorySourceEnvAt P c (honestQm P c Qm) i).trace 4 = 0 ∧
      (memorySourceEnvAt P c (honestQm P c Qm) i).trace 3 = 0 := by
  have hcntG := mixed_at_family P c Qm hsat i (rootMaskCountsGate (F := F))
    (rootMaskCounts_mem_mixed P.optimized.basis)
  have hindG := mixed_at_family P c Qm hsat i (rootMaskIndicatorGate (F := F))
    (rootMaskIndicator_mem_mixed P.optimized.basis)
  let S := namedSourceMemoryRAP
    P.optimized.family.problem.cfg.memRows_pos
    P.optimized.memoryNodes P.optimized.basis
    (memoryChalValOfTuple P.optimized.basis c)
    (P.familyMemoryPublic c) P.optimized.orbit
    P.optimized.family.problem.cfg.kMem
  have h2 : 2 < S.fixedCount := by
    change 2 < 4
    exact Nat.lt_succ_of_lt (Nat.lt_succ_self 2)
  have hbind := (source_sat_at P c Qm hsat).2 ⟨2, h2⟩
  have hmask : (memoryBaseEnvAt P c (honestQm P c Qm) i).trace 153 = 1 := by
    rw [← envF_eq_base]
    simp only [Nock.Framework.Reify.envOfTrace]
    have hlt : (153 : ℕ) < 182 := by decide
    rw [dif_pos hlt]
    have hcol : S.preprocessingColumn ⟨2, h2⟩ = ⟨153, hlt⟩ := rfl
    have hproj : projAt P c Qm ⟨153, hlt⟩ = S.preprocessing ⟨2, h2⟩ := by
      convert hbind
      · exact congrArg (projAt P c Qm) hcol.symm
    rw [hproj]
    change (rootRowMask P.optimized.memoryNodes
      P.optimized.family.problem.cfg.kMem).eval (P.optimized.memoryNodes i) = 1
    rw [rootRowMask_eval P.optimized.memoryNodes
      P.optimized.family.problem.cfg.kMem
      P.optimized.memoryNodes_injective i, if_pos hi]
  have hcnt := Batch408.rootMaskCountsGate_eval
    (memorySourceEnvAt P c (honestQm P c Qm) i)
    (memoryBaseEnvAt P c (honestQm P c Qm) i)
  have hind := Batch408.rootMaskIndicatorGate_eval
    (memorySourceEnvAt P c (honestQm P c Qm) i)
    (memoryBaseEnvAt P c (honestQm P c Qm) i)
  rw [hcnt, hmask] at hcntG
  rw [hind, hmask] at hindG
  rw [map_one, one_mul] at hcntG hindG
  exact ⟨hcntG, hindG⟩

end DeployedZero

end Nock.RedTeam.Batch409
