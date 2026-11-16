/-
  Nock/RedTeam/Batch1013Thm54AxisViewTransfer.lean

  * `accepts_R0A_iff` — acceptance is the round-0 strategy's (`Iff.rfl`: same verifier);
  * `genuine_R0A_iff` — the genuine target transfers (the containment witness's fields are the
    verifier's);
  * `censusA` / `failureUnion_R0A_eq` — a census of the round-0 skeleton is a census of the a-bearing
    one (same compute tree, the only part the census reads), and `FailureUnion` is equal (`rfl`);
  * `hcomp_same` — the compute-tree side of `BindsAtCoin` is the round-0 strategy's (`Iff.rfl`).

  Option B adds no `StrategyOfTracesR0A` frontier name.
-/
import Nock.RedTeam.Batch1011Thm54AxisViewBindsAtCoin
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch1013

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.StrategyOfTracesR0 Nock.NockVMROM.Thm54.StrategyOfTracesR0A
open scoped Polynomial
open Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (FamilyEnvCore.honestQc P.optimized c Qc)
        (FamilyEnvCore.honestQm P.optimized c Qm) c)

/-- The a-bearing round-0 strategy at the family traces. -/
abbrev TA := strategyOfTracesR0A P.optimized P.stateTagChar (FamilyEnvCore.honestQc P.optimized c Qc)
  (FamilyEnvCore.honestQm P.optimized c Qm) c h

/-- The round-0 strategy at the family traces. -/
abbrev T0 := strategyOfTracesR0 P.optimized P.stateTagChar (FamilyEnvCore.honestQc P.optimized c Qc)
  (FamilyEnvCore.honestQm P.optimized c Qm) c h

/-- (1) Acceptance is literally the round-0 strategy's. -/
theorem accepts_R0A_iff (ω : JointCoins K) (l : K) :
    (TA P c Qc Qm h).Accepts ω l ↔ (T0 P c Qc Qm h).Accepts ω l := Iff.rfl

/-- (2) The genuine target transfers. -/
theorem genuine_R0A_iff (q Λ : ℕ) (ω : JointCoins K) (l : K) :
    GenuineTargetAt (TA P c Qc Qm h) q Λ ω l ↔ GenuineTargetAt (T0 P c Qc Qm h) q Λ ω l := by
  unfold GenuineTargetAt
  split_ifs with hz
  · constructor
    · rintro ⟨w⟩; exact ⟨{ w with }⟩
    · rintro ⟨w⟩; exact ⟨{ w with }⟩
  · exact Iff.rfl

/-- (3) A census of the round-0 skeleton is a census of the a-bearing skeleton (same compute tree). -/
def censusA {Λ : ℕ} (C : EdgeComparisonCensus.CombinedSkeletonCensus K (T0 P c Qc Qm h).skeleton Λ) :
    EdgeComparisonCensus.CombinedSkeletonCensus K (TA P c Qc Qm h).skeleton Λ :=
  ⟨⟨C.p8.leaves_bounded⟩, C.edges⟩

theorem failureUnion_R0A_eq {Λ : ℕ}
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K (T0 P c Qc Qm h).skeleton Λ) (l : K) :
    FailureUnion (TA P c Qc Qm h) (censusA P c Qc Qm h C) l = FailureUnion (T0 P c Qc Qm h) C l := rfl

/-- (4) The compute-tree side of `BindsAtCoin` is the round-0 strategy's. -/
theorem hcomp_same (hz : nprSeed c.1 ≠ 0) :
    (SemanticStrategy.ComputeTreeBinds (nprSeed c.1) (TA P c Qc Qm h).skeleton.computeTree
      ((TA P c Qc Qm h).specializedExec (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeTree) ↔
    (SemanticStrategy.ComputeTreeBinds (nprSeed c.1) (T0 P c Qc Qm h).skeleton.computeTree
      ((T0 P c Qc Qm h).specializedExec (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeTree) :=
  Iff.rfl

end

end Nock.RedTeam.Batch1013

#print axioms Nock.RedTeam.Batch1013.accepts_R0A_iff
#print axioms Nock.RedTeam.Batch1013.genuine_R0A_iff
#print axioms Nock.RedTeam.Batch1013.failureUnion_R0A_eq
#print axioms Nock.RedTeam.Batch1013.hcomp_same
