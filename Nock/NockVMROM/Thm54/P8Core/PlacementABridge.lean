/-
  Nock/NockVMROM/Thm54/P8Core/PlacementABridge.lean

  Of its 12 slots:
  * slots 1–10 are literal summands of Ev (`comps1_10_literal`);

  Imports P8Core only; never the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.OptimizedFailureEventEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.PlacementA

open scoped Polynomial
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.P8EventEv

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X])
  (Qm : Fin P.memoryChip.rap.w → F[X])
  (c : OptimizedProductionChallengeTuple K F)

theorem comps1_10_literal (h : c ∉ optimizedFailureEventEv P Qc Qm) :
      c ∉ P.famIOEventOf Qc Qm ∧
      alphaM c.1 ∉
        OptimizedHostileTimestamps.TimestampCollisionEvent (P.hostileRequests Qc).length ∧
      (c.2.1.1, c.2.2.2.interPole) ∉
        interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) ∧
      c.1 ∉ P.computeWalkRootEvent Qc ∧
      c.1 ∉ P.computeTilingEventOf Qc ∧
      c.1 ∉ P.memoryTilingEventOf Qm ∧
      c.1 ∉ P.computePrefixGammaEventOf Qc ∧
      c.1 ∉ P.memoryPrefixGammaEventOf Qm ∧
      c.1 ∉ P.memoryForestAlphaEventOf Qm ∧
      c ∉ P.decodedLambdaEventOf Qc Qm := by
  have g := optimizedFailureEventEv_good_components P Qc Qm c h
  with_reducible exact ⟨g.2.1, g.2.2.1, g.2.2.2.1, g.2.2.2.2.1, g.2.2.2.2.2.1, g.2.2.2.2.2.2.1,
    g.2.2.2.2.2.2.2.1, g.2.2.2.2.2.2.2.2.1, g.2.2.2.2.2.2.2.2.2.1, g.2.2.2.2.2.2.2.2.2.2.1⟩

/-- **Slot 0's only consumed content is implied**: `zeroSeedFailureEvent` is the first summand of
Ev's `evFailureUnion`. -/
theorem comp0_zeroSeed_of_Ev (h : c ∉ optimizedFailureEventEv P Qc Qm) : nprSeed c.1 ≠ 0 := by
  have hp8 := (optimizedFailureEventEv_good_components P Qc Qm c h).1
  intro hz
  refine hp8 ?_
  simp [evFailureUnion, mem_zeroSeedFailureEvent_iff, hz]

theorem good_components_of_Ev (h : c ∉ optimizedFailureEventEv P Qc Qm) :
    nprSeed c.1 ≠ 0 ∧
      c ∉ P.famIOEventOf Qc Qm ∧
      alphaM c.1 ∉
        OptimizedHostileTimestamps.TimestampCollisionEvent (P.hostileRequests Qc).length ∧
      (c.2.1.1, c.2.2.2.interPole) ∉
        interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) ∧
      c.1 ∉ P.computeWalkRootEvent Qc ∧
      c.1 ∉ P.computeTilingEventOf Qc ∧
      c.1 ∉ P.memoryTilingEventOf Qm ∧
      c.1 ∉ P.computePrefixGammaEventOf Qc ∧
      c.1 ∉ P.memoryPrefixGammaEventOf Qm ∧
      c.1 ∉ P.memoryForestAlphaEventOf Qm ∧
      c ∉ P.decodedLambdaEventOf Qc Qm ∧
      c.1 ∉ reqPairEv P Qc Qm := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := comps1_10_literal P Qc Qm c h
  exact ⟨comp0_zeroSeed_of_Ev P Qc Qm c h, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    (optimizedFailureEventEv_good_components P Qc Qm c h).2.2.2.2.2.2.2.2.2.2.2.1⟩

end

end Nock.NockVMROM.Thm54.PlacementA
