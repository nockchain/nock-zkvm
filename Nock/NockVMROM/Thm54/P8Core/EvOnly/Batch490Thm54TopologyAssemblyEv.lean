/-
  Nock/NockVMROM/Thm54/P8Core/EvOnly/Batch490Thm54TopologyAssemblyEv.lean

  The originals are untouched.  Imports P8Core only; never the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch490Thm54TopologyAssembly
import Nock.NockVMROM.Thm54.P8Core.PlacementABridge
import Nock.NockVMROM.Thm54.P8Core.EvOnly.OptimizedHostileTimestampsEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch465Thm54DeployedRootLabelEqClaimEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch489Thm54FoOfEqFoWEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch490

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.WrapFixesVcomp
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.Framework
open Nock.Framework.Reify
open MonolithicRAP
open Nock.RedTeam.Batch465
open Nock.RedTeam.Batch471
open Nock.RedTeam.Batch489
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

section ComputeFcommit

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hz : nprSeed c.1 ≠ 0)

include hsat hz

end ComputeFcommit

section ComputeVecBFT

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hsat
include hax hbasis hwidth

end ComputeVecBFT

section ComputeTopology

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hz : nprSeed c.1 ≠ 0)
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hsatC hz
include hax hbasis hwidth

end ComputeTopology

section AlphaEventEq

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

end AlphaEventEq

section PricedDischarge

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
  (hz : nprSeed c.1 ≠ 0)
  (hchar : MemStateTagChar F)
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hsatC
include hax hbasis hwidth

/-- Tiling of the consumed `foOf` table, from the priced tiling event. -/
theorem foOf_tiles_of_good_ev
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P Qc₀ Qm₀) :
    Sf (foOf (P.computeSourceEnv Qc₀)) (rows P) + 1 = rows P := by
  have htileC : c.1 ∉ P.computeTilingEventOf Qc₀ :=
    (Nock.NockVMROM.Thm54.PlacementA.good_components_of_Ev P Qc₀ Qm₀ c hgood).2.2.2.2.2.1
  have htileW : c.1 ∉ WalkTilingEvents.computeTilingEvent
      (Batch459.foW P c (familyQc P c Qc₀) hsatC) (rows P) := by
    rwa [← computeTilingEventOf_eq_foW P c Qc₀ hsatC]
  have hSfW : Sf (Batch459.foW P c (familyQc P c Qc₀) hsatC) (rows P) + 1 = rows P :=
    deployed_tiling P c (familyQc P c Qc₀) hsatC hax hbasis hwidth htileW
  rw [Sf_foOf_eq_foW P c Qc₀ hsatC]
  exact hSfW

/-- Priced walk-root + tiling ⇒ outside `alphaRootEvent`. -/
theorem not_mem_alphaRoot_of_good_ev
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P Qc₀ Qm₀) :
    c.1 ∉ alphaRootEvent (P.computeSourceEnv Qc₀)
      (fun z => claimLabelVec z P.optimized.verifier.raw.claim) := by
  have hwalk : c.1 ∉ P.computeWalkRootEvent Qc₀ :=
    (Nock.NockVMROM.Thm54.PlacementA.good_components_of_Ev P Qc₀ Qm₀ c hgood).2.2.2.2.1
  have htile : Sf (foOf (P.computeSourceEnv Qc₀)) (rows P) + 1 = rows P :=
    foOf_tiles_of_good_ev P c Qc₀ Qm₀ hsatC hax hbasis hwidth hgood
  have hcons : c.1 ∉ alphaRootEventConsumed (P.computeSourceEnv Qc₀)
      (fun z => claimLabelVec z P.optimized.verifier.raw.claim) :=
    ((notMem_rootEvent_iff (P.computeSourceEnv Qc₀)
      (fun z => claimLabelVec z P.optimized.verifier.raw.claim)
      (rowLabelVec (P.computeSourceEnv Qc₀
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩)) c.1).1
      (by simpa [OptimizedFullStrictNockVMROMPackage.computeWalkRootEvent] using hwalk)).1
  simp only [alphaRootEventConsumed, htile, ↓reduceIte] at hcons
  exact hcons

/-- `hseed` of `deployed_prefixBFT` from `c ∉ optimizedFailureEvent`. -/
theorem hseed_of_good_ev
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P Qc₀ Qm₀) :
    seedOfClaim P.optimized.verifier.raw.claim c =
      rlc (gamma c.1) (Vd P c Qc₀ 1) * alphaC c.1 :=
  hseed_of_alphaRoot P c Qc₀ hsatC hax hbasis hwidth
    (not_mem_alphaRoot_of_good_ev P c Qc₀ Qm₀ hsatC hax hbasis hwidth hgood)

/-- Tiling exclusion the chip theorem takes, from the priced event. -/
theorem htileα_of_good_ev
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P Qc₀ Qm₀) :
    c.1 ∉ WalkTilingEvents.computeTilingEvent
      (Batch459.foW P c (familyQc P c Qc₀) hsatC) (rows P) := by
  have htileC : c.1 ∉ P.computeTilingEventOf Qc₀ :=
    (Nock.NockVMROM.Thm54.PlacementA.good_components_of_Ev P Qc₀ Qm₀ c hgood).2.2.2.2.2.1
  rwa [← computeTilingEventOf_eq_foW P c Qc₀ hsatC]

include hz hchar hsatM

/-- **Exact failing statement.**  `DeployedAcceptanceAt` + priced events give
`ComputeExactTopology` of `execOfTraces` once `γ ∉ prefixBadGammas`.  That
event is not a component of `optimizedFailureEvent` (priced `γ` is the
root/claim collision only). -/
theorem computeTopology_of_deployed_ev
    (hacc : DeployedAcceptanceAt P c (familyQc P c Qc₀) (familyQm P c Qm₀))
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P Qc₀ Qm₀)
    (hγ : gamma c.1 ∉ prefixBadGammas (Vd P c Qc₀) (Cvd P c Qc₀ hsatC)
      (foC P Qc₀ c) (rows P)) :
    ComputeExactTopology (execOfTraces P Qc₀ Qm₀ c
      (tracesWalkHyps_of_deployed_ev P c Qc₀ Qm₀ hsatC hsatM hchar hax hbasis hwidth hacc hgood)) :=
  execOfTraces_computeTopology P c Qc₀ Qm₀ hsatC hz hax hbasis hwidth
    (tracesWalkHyps_of_deployed_ev P c Qc₀ Qm₀ hsatC hsatM hchar hax hbasis hwidth hacc hgood)
    (hseed_of_good_ev P c Qc₀ Qm₀ hsatC hax hbasis hwidth hgood)
    (walkPrefixAlpha_of_alphaRoot P c Qc₀ hsatC hax hbasis hwidth
      (not_mem_alphaRoot_of_good_ev P c Qc₀ Qm₀ hsatC hax hbasis hwidth hgood))
    hγ
    (htileα_of_good_ev P c Qc₀ Qm₀ hsatC hax hbasis hwidth hgood)

end PricedDischarge

section MemoryFcommit

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hchar : MemStateTagChar F)
  (hz : nprSeed c.1 ≠ 0)

include hsatM hchar hz

end MemoryFcommit

end Nock.RedTeam.Batch490

