/-
  Nock/NockVMROM/Thm54/P8Core/EvOnly/Batch501Thm54MemoryTopologyEv.lean

  The originals are untouched.  Imports P8Core only; never the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch501Thm54MemoryTopology
import Nock.NockVMROM.Thm54.P8Core.PlacementABridge
import Nock.NockVMROM.Thm54.P8Core.EvOnly.OptimizedHostileTimestampsEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch465Thm54DeployedRootLabelEqClaimEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch489Thm54FoOfEqFoWEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch490Thm54TopologyAssemblyEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch500Thm54GammaTransportEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch501

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
open Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.MemoryWalkLabel
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.HostilePoleAlignment
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.Framework
open Nock.Framework.Reify
open MonolithicRAP
open Nock.RedTeam.Batch489
open Nock.RedTeam.Batch490
open Nock.RedTeam.Batch500
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.MemoryTopoBetaFree (FmemTopo mem_stateSep_topo respects_pt_topo memPtOf)

noncomputable section

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

section PricedForestGamma

variable {F : Type} [Field F] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])

/-- `c ∉ optimizedFailureEvent` discharges the memory forest `hγ`. -/
theorem hγM_of_good_ev
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P Qc₀ Qm₀) :
    gamma c.1 ∉
      forestPrefixBadGammas
        (committedMemoryV (P.memorySourceEnv Qm₀) (P.memoryBaseEnv Qm₀))
        (committedMemoryCv (P.memorySourceEnv Qm₀))
        (WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm₀))
        P.optimized.family.problem.cfg.kMem
        P.optimized.family.problem.cfg.memRows :=
  hγM_of_priced P c Qm₀
    (Nock.NockVMROM.Thm54.PlacementA.good_components_of_Ev P Qc₀ Qm₀ c hgood).2.2.2.2.2.2.2.2.1

end PricedForestGamma

section Projection

variable {K : Type} [Field K]

end Projection

section ForestMap

variable {K : Type*} [Field K] {n m : ℕ}

end ForestMap

section MemoryVectors

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hchar : MemStateTagChar F)
  (hz : nprSeed c.1 ≠ 0)

include hz
include hsatM hchar

end MemoryVectors

section ForestVecBFT

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hchar : MemStateTagChar F)
include hsatM hchar

/-- Tiling exclusion the chip theorem takes, from the priced event. -/
theorem htileαM_of_good_ev
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P Qc₀ Qm₀) :
    c.1 ∉ WalkTilingEvents.memoryTilingEvent
      (foW P c (familyQm P c Qm₀)) (kMemP P) (memRowsP P) := by
  have htileM : c.1 ∉ P.memoryTilingEventOf Qm₀ :=
    (Nock.NockVMROM.Thm54.PlacementA.good_components_of_Ev P Qc₀ Qm₀ c hgood).2.2.2.2.2.2.1
  rwa [← memoryTilingEventOf_eq_foWmem P c Qm₀]

end ForestVecBFT

section MemoryTopology

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hchar : MemStateTagChar F)
  (hz : nprSeed c.1 ≠ 0)
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hsatM hchar hz
include hsatC
include hax hbasis hwidth

/-- **The β-free memory topology of `execOfTraces`** (M′, `m-prime-topo`): every reconstructed
memory tree is in `L_RVT^{FmemTopo,2}`.  Restated: the former conclusion was the production
`MemoryExactTopology` (`RVTWithArity Fmem`, uniform-β `V_mem`) under `hexp0`, unsatisfiable on record rows whenever `γ ≠ 0`;
the production `MemoryExactTopology` is NOT concluded here. -/
theorem execOfTraces_memoryTopology_ev
    (h : TracesWalkHyps P Qc₀ Qm₀ c)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P Qc₀ Qm₀)
    (hα : alphaM c.1 ∉ walkForestPrefixAlphaEvent
      (curW P c (familyQm P c Qm₀)) (chldW P c (familyQm P c Qm₀))
      (foW P c (familyQm P c Qm₀)) (kMemP P) (memRowsP P)) :
    ∀ t ∈ (execOfTraces P Qc₀ Qm₀ c h).memoryForest, RVTWithArity (FmemTopo (K := K)) t := by
  have hfo : foW P c (familyQm P c Qm₀) = foM P Qm₀ c := by
    funext i
    have hw := foW_eq_foM_all P c (familyQm P c Qm₀) i
    rw [MemoryWalkDeployed.Qmh, WalkQueueDeployed.honestQm_familyQm P c Qm₀] at hw
    exact hw
  have hv : BFSValidF (kMemP P) (foM P Qm₀ c) (memRowsP P) := by
    rw [← hfo]
    exact deployed_bfsValid_memory P c (familyQm P c Qm₀) hsatM hchar
  have htile : kMemP P + Sf (foM P Qm₀ c) (memRowsP P) = memRowsP P := by
    rw [← hfo]
    exact deployed_tiling_memory P c (familyQm P c Qm₀) hsatM hchar
      (htileαM_of_good_ev P c Qc₀ Qm₀ hsatM hchar hgood)
  have hγ : gamma c.1 ∉ forestPrefixBadGammas (VdM P c Qm₀) (CvdM P c Qm₀)
      (foM P Qm₀ c) (kMemP P) (memRowsP P) := by
    rw [← forestPrefixBadGammas_VdM_eq_committed P c Qm₀]
    exact hγM_of_good_ev P c Qc₀ Qm₀ hgood
  have hb' := deployed_forestVecBFT_pt P c Qm₀ hsatM hchar hγ hα
    (htileαM_of_good_ev P c Qc₀ Qm₀ hsatM hchar hgood)
  have harity : ∀ i, foM P Qm₀ c i ≤ 2 :=
    fun i => fanoutMem_le_two (lblM P Qm₀ c i).1
  have hF : ∀ i, 1 ≤ i → i ≤ memRowsP P →
      FmemTopo (lblM P Qm₀ c i)
        (fun j : Fin 2 =>
          if (j : ℕ) < foM P Qm₀ c i then
            some (lblM P Qm₀ c (firstCF (kMemP P) (foM P Qm₀ c) i + j))
          else none) := by
    intro i hi1 hih
    refine respects_pt_topo (lblM P Qm₀ c i) _ _ ?_
      (hFcommit_memory_of_good P c Qm₀ hsatM hchar hz i hi1 hih)
    intro j
    by_cases hj : (j : ℕ) < foM P Qm₀ c i
    · have hkey := ForestVecBFT_layout
        (fun i => encPT (lblM P Qm₀ c i))
        (fun i l => encPT (clabOfMem (lblM P Qm₀ c) i l))
        (foM P Qm₀ c) htile hb' hi1 hih hj
      rw [if_pos hj, if_pos hj]
      simp only [Option.map_some]
      exact congrArg some (encPT_label _ _ hkey)
    · rw [if_neg hj, if_neg hj]
  have hrvt := reconForest_RVT (mem_stateSep_topo (K := K)) (kMemP P)
    (foM P Qm₀ c) (lblM P Qm₀ c) (memRowsP P)
    (MemoryWalkDeployed.kMem_pos P) htile hv harity
    (fun i _ _ => rfl) hF
  have hpa := reconForest_properArity (kMemP P) (foM P Qm₀ c)
    (lblM P Qm₀ c) (memRowsP P) (MemoryWalkDeployed.kMem_pos P) htile hv harity
  intro t ht
  exact RVTWithArity.mk' (hrvt t (by
      change t ∈ (execOfTraces P Qc₀ Qm₀ c h).memoryForest
      exact ht))
    (hpa t (by
      change t ∈ (execOfTraces P Qc₀ Qm₀ c h).memoryForest
      exact ht))

omit hax hbasis hwidth in
theorem hαM_of_good_ev
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P Qc₀ Qm₀) :
    alphaM c.1 ∉ walkForestPrefixAlphaEvent
      (curW P c (familyQm P c Qm₀)) (chldW P c (familyQm P c Qm₀))
      (foW P c (familyQm P c Qm₀)) (kMemP P) (memRowsP P) := by
  have hαM : c.1 ∉ P.memoryForestAlphaEventOf Qm₀ :=
    (Nock.NockVMROM.Thm54.PlacementA.good_components_of_Ev P Qc₀ Qm₀ c hgood).2.2.2.2.2.2.2.2.2.1
  have htileα := htileαM_of_good_ev P c Qc₀ Qm₀ hsatM hchar hgood
  have htile : kMemP P + Sf (foW P c (familyQm P c Qm₀)) (memRowsP P) =
      memRowsP P :=
    deployed_tiling_memory P c (familyQm P c Qm₀) hsatM hchar htileα
  have htile' : kMemP P + Sf (WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm₀))
      (memRowsP P) = memRowsP P := by
    rw [Sf_foOfMem_eq_foWmem P c Qm₀]; exact htile
  have hmem : alphaM c.1 ∉ walkForestPrefixAlphaEvent
      (curOfMem (committedMemoryV (P.memorySourceEnv Qm₀) (P.memoryBaseEnv Qm₀))
        (gamma c.1))
      (chldOfMem (committedMemoryCv (P.memorySourceEnv Qm₀)) (gamma c.1))
      (WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm₀)) (kMemP P) (memRowsP P) :=
    (mem_memoryForestAlphaEventOfEnvs_of_tiling
      (P.memorySourceEnv Qm₀) (P.memoryBaseEnv Qm₀) (kMemP P) htile' c.1).mpr.mt
      (by simpa [OptimizedFullStrictNockVMROMPackage.memoryForestAlphaEventOf] using hαM)
  have heq : walkForestPrefixAlphaEvent
      (curOfMem (committedMemoryV (P.memorySourceEnv Qm₀) (P.memoryBaseEnv Qm₀))
        (gamma c.1))
      (chldOfMem (committedMemoryCv (P.memorySourceEnv Qm₀)) (gamma c.1))
      (WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm₀)) (kMemP P) (memRowsP P) =
      walkForestPrefixAlphaEvent
        (curW P c (familyQm P c Qm₀)) (chldW P c (familyQm P c Qm₀))
        (foW P c (familyQm P c Qm₀)) (kMemP P) (memRowsP P) := by
    refine WalkForestPrefixAlphaEvents.walkForestPrefixAlphaEvent_congr_on
      (kMem_le_memRows P) ?_ ?_ ?_
    · intro i h1 h2
      simp only [curOfMem]
      have hV := VdM_eq_committed P c Qm₀ i h1 h2
      have hcur : curW P c (familyQm P c Qm₀) i =
          rlc (gamma c.1) (VdM P c Qm₀ i) := rfl
      rw [hV, hcur]
    · intro i l h1 h2
      simp only [chldOfMem]
      have hC := CvdM_eq_committed P c Qm₀ i l h1 h2
      have hch : chldW P c (familyQm P c Qm₀) i l =
          rlc (gamma c.1) (CvdM P c Qm₀ i l) := rfl
      rw [hC, hch]
    · intro i h1 h2
      exact foOfMem_eq_foWmem P c Qm₀ i h1 h2
  rwa [heq] at hmem

/-- **Exact remaining hyp.**  `DeployedAcceptanceAt` + priced events give the β-free memory
    topology of `execOfTraces` (M′: `∀ t ∈ memoryForest, RVTWithArity FmemTopo t`, no `hexp0`)
    once `α ∉ walkForestPrefixAlphaEvent`.  That event is the paper's `:1008` `h/|K|`. -/
theorem memoryTopology_of_deployed_ev
    (hacc : DeployedAcceptanceAt P c (familyQc P c Qc₀) (familyQm P c Qm₀))
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P Qc₀ Qm₀)
    (hα : alphaM c.1 ∉ walkForestPrefixAlphaEvent
      (curW P c (familyQm P c Qm₀)) (chldW P c (familyQm P c Qm₀))
      (foW P c (familyQm P c Qm₀)) (kMemP P) (memRowsP P)) :
    ∀ t ∈ (execOfTraces P Qc₀ Qm₀ c
      (tracesWalkHyps_of_deployed_ev P c Qc₀ Qm₀ hsatC hsatM hchar hax hbasis hwidth hacc hgood)).memoryForest,
      RVTWithArity (FmemTopo (K := K)) t :=
  execOfTraces_memoryTopology_ev P c Qc₀ Qm₀ hsatC hsatM hchar hz hax hbasis hwidth
    (tracesWalkHyps_of_deployed_ev P c Qc₀ Qm₀ hsatC hsatM hchar hax hbasis hwidth hacc hgood)
    hgood hα

theorem memoryTopology_of_deployed_of_good_ev
    (hacc : DeployedAcceptanceAt P c (familyQc P c Qc₀) (familyQm P c Qm₀))
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P Qc₀ Qm₀) :
    ∀ t ∈ (execOfTraces P Qc₀ Qm₀ c
      (tracesWalkHyps_of_deployed_ev P c Qc₀ Qm₀ hsatC hsatM hchar hax hbasis hwidth hacc hgood)).memoryForest,
      RVTWithArity (FmemTopo (K := K)) t :=
  memoryTopology_of_deployed_ev P c Qc₀ Qm₀ hsatC hsatM hchar hz hax hbasis hwidth hacc hgood
    (hαM_of_good_ev P c Qc₀ Qm₀ hsatC hsatM hchar hz hgood)

end MemoryTopology

end

end Nock.RedTeam.Batch501

