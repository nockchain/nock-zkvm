/-
  Nock/RedTeam/Batch913Thm54SpecializeAFromAcceptance.lean

  `Batch912.bridgeTwinA_of_deployed` (the `specializeA`-view restatement of
  `Batch761.bridgeTwin_of_deployed`) carries `hpow` only.  Composed here through the two reindexing
  identities (`honestQc_familyQc`, `WalkQueueDeployed.honestQm_familyQm`).

  So the `hW` consumer of the Part 2 skeleton (`MemoryExactTopology` consumption → the bridge
  twin) needs no new mathematics on the A-view: only its statement moves from `specializedExec`
  to the a-bearing `ExactExecutionTemplate.specializeA`.
-/
import Nock.RedTeam.Batch912Thm54SpecializeARoute
import Nock.RedTeam.Batch844Thm54HpowHW
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch913

open scoped Polynomial
open Nock Nock.Walk Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.AxisBridgeLocalTopo
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.CoordinateBasis
open MonolithicRAP

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])

theorem honestQc_familyQc : honestQc P c (familyQc P c Qc₀) = Qc₀ := by
  funext j
  unfold honestQc familyQc
  apply congrArg Qc₀
  exact Fin.ext (by rw [Fin.val_cast, Fin.val_cast])

/-- **The A-view bridge twin from family acceptance.**  No `WrapMemoryIdentity`, no `hpow`. -/
theorem bridgeTwinA_of_family_acceptance
    (hchar : MemStateTagChar F)
    (hz : nprSeed c.1 ≠ 0)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (hacc : DeployedAcceptanceAt P c (familyQc P c Qc₀) (familyQm P c Qm₀))
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀)
    (hio : FamilyIOGood P c (familyQc P c Qc₀) (familyQm P c Qm₀))
    (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K)
    (hb1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0)
    (hα0 : alphaM c.1 ≠ 0)
    (i : Fin ((cfgTemplateOfTraces P Qc₀ Qm₀ c (nprSeed c.1)).specialize
      (alphaM c.1) c.2.2.2.lambda).kMem) :
    ExactAxisBridgeLocalTopo _
      (Batch912.execA P c Qc₀ Qm₀
        (Batch489.tracesWalkHyps_of_deployed P c Qc₀ Qm₀ hacc.compute_satisfies
          hacc.memory_satisfies hchar hax hbasis hwidth hacc hgood)) i := by
  have hgood' : c ∉ P.optimizedFailureEvent (honestQc P c (familyQc P c Qc₀))
      (honestQm P c (familyQm P c Qm₀)) := by
    rw [honestQc_familyQc, WalkQueueDeployed.honestQm_familyQm]
    exact hgood
  have hpow := Batch844.hpow_of_family_acceptance P c (familyQc P c Qc₀) (familyQm P c Qm₀)
    hacc hgood' hio hrb hb1 hα0
  rw [WalkQueueDeployed.honestQm_familyQm] at hpow
  exact Batch912.bridgeTwinA_of_deployed P c Qc₀ Qm₀ hacc.compute_satisfies hacc.memory_satisfies
    hchar hz hax hbasis hwidth hacc hgood hpow i

end

end Nock.RedTeam.Batch913

#print axioms Nock.RedTeam.Batch913.honestQc_familyQc
#print axioms Nock.RedTeam.Batch913.bridgeTwinA_of_family_acceptance
