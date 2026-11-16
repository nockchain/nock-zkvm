/-
  Nock/RedTeam/Batch992Thm54HgoodFill.lean

  Measured by reading the proofs of `Batch963.hgood_zero_built` and everything it calls (the
  `H.<field>` projections, transitively):

  | component | consumer | `HonestFill` fields read |
  |---|---|---|
  | 2 (family IO) | `Batch909.hioEvent_honest` → `Batch907.hio_honest` → `hostileRecordsAt_honest` → `rowEnvAt_honest` / `familyComputePublic_honest`, and `canonical_coins_not_hostile_failure` | `hchalC`, `hst`, `hs`, `hf`, `he`, `hax`, `hwidth` |
  | 3 (timestamp) | `Batch957.timestamp_honest` → `hostileRequests_canonical_length` (`canonical_hostileRequests`) | `hax`, `hwidth` |
  | 4 (inter pole) | `Batch963.inter_of_sides` (`canonical_inter_not_hostile_failure`) | `hC` |
  | 5 (walk root) | `Batch962.walkRoot_honest` | `hst`, `hs`, `hf`, `he` |
  | 1, 6–12 | — | none |

  **`hchalM`, `hmore` and `hbasis` are not consumed by `hgood`.**  `hchalM` is read only by
  `Batch906.deployedAcceptance_honest` (honest acceptance at the family memory chip, the R4
  receipt's premise), which `hgood` does not use.
-/
import Nock.RedTeam.Batch991Thm54HonestPoleAssembly
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Nock.RedTeam.Batch992

open Nock
open Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.RedTeam.Batch906
open Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
open scoped Polynomial
open Polynomial
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Nock.NockVMROM.Thm54.CoordinateBasis

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-- **The `HonestFill` fields `hgood` consumes** (see the table above). -/
structure HgoodFill (P : OptimizedFullStrictNockVMROMPackage F K hOrb) : Prop where
  hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis
  hwidth : OptimizedComputeFinalTrace.FormRWidth F
  hC : P.optimized.family.problem.exec.CprimeCoherent
  hchalC : DeployedChipFamily.computeChalValOfTuple P.optimized.basis P.honestTuple =
    P.optimized.computeChallenge
  hst : (P.optimized.family.problem.exec.computePubAt
      ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).state =
    ComputeWalkSeed.rootStateOfFormula P.optimized.verifier.raw.claim.formula
  hs : (P.optimized.family.problem.exec.computePubAt
      ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).s =
    GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1) P.optimized.verifier.raw.claim.subject
  hf : (P.optimized.family.problem.exec.computePubAt
      ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).f =
    GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1) P.optimized.verifier.raw.claim.formula
  he : (P.optimized.family.problem.exec.computePubAt
      ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).e =
    GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1) P.optimized.verifier.raw.claim.result

/-- `HgoodFill` is a projection of `HonestFill` (it drops `hbasis`, `hmore`, `hchalM`). -/
theorem HgoodFill.of_honestFill {P : OptimizedFullStrictNockVMROMPackage F K hOrb}
    (H : HonestFill P) : HgoodFill P :=
  ⟨H.hax, H.hwidth, H.hC, H.hchalC, H.hst, H.hs, H.hf, H.he⟩

variable {P : OptimizedFullStrictNockVMROMPackage F K hOrb}


theorem familyComputePublic_honest (G : HgoodFill P) :
    P.familyComputePublic P.honestTuple = P.optimized.computePublic :=
  DeployedChipFamily.computePublicOfTuple_eq_pkg_of_seed
    P.optimized.basis P.optimized.verifier.raw.claim P.optimized.family
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computePublic
    P.honestTuple P.optimized.computePublicPins rfl
    (P.computeWalkSeed_eq_seedOfClaim_honest G.hst G.hs G.hf G.he).symm

theorem rowEnvAt_honest (G : HgoodFill P) (a : Fin P.optimized.family.problem.cfg.compRows) :
    rowEnvAt P P.honestTuple (QcH P) a =
      gatherCorrectedFinalTypedEnv P.optimized.basis
        (P.computeBaseEnv (canonicalComputeTrace P) a) := by
  unfold rowEnvAt
  rw [G.hchalC, familyComputePublic_honest G]
  congr 1

theorem hostileRequestsAt_honest (G : HgoodFill P) :
    hostileRequestsAt P P.honestTuple (QcH P) = P.hostileRequests (canonicalComputeTrace P) := by
  unfold hostileRequestsAt OptimizedFullStrictNockVMROMPackage.hostileRequests
  refine congrArg List.flatten (congrArg List.ofFn (funext fun a => ?_))
  rw [rowEnvAt_honest G a]

theorem hostileRecordsAt_honest (G : HgoodFill P) :
    hostileRecordsAt P P.honestTuple (QmH P) (QcH P) =
      P.hostileRecords (canonicalComputeTrace P) (canonicalMemoryTrace P) := by
  unfold hostileRecordsAt OptimizedFullStrictNockVMROMPackage.hostileRecords
  rw [hostileRequestsAt_honest G, hostileResponsesAt_eq_package, honestQm_QmH]

theorem hio_honest (G : HgoodFill P) : FamilyIOGood P P.honestTuple (QcH P) (QmH P) := by
  unfold FamilyIOGood
  rw [hostileRecordsAt_honest G]
  exact OptimizedCanonicalHostileLists.canonical_coins_not_hostile_failure P G.hax G.hwidth

/-- Component 2 over `HgoodFill`. -/
theorem hioEvent_honest (G : HgoodFill P) :
    P.honestTuple ∉ P.famIOEventOf (canonicalComputeTrace P) (canonicalMemoryTrace P) := by
  intro hm
  have h := (FamilyEnvCore.mem_famIOEventOf_iff P.optimized (canonicalComputeTrace P)
    (canonicalMemoryTrace P) P.honestTuple).1 hm
  exact hio_honest G h

/-- Component 3 over `HgoodFill`. -/
theorem timestamp_honest (G : HgoodFill P)
    (hα0 : alphaM P.honestTuple.1 ≠ 0)
    (hord : P.optimized.family.problem.exec.derivedRequestIO.length ≤
      orderOf (alphaM P.honestTuple.1)) :
    alphaM P.honestTuple.1 ∉ OptimizedHostileTimestamps.TimestampCollisionEvent
      (P.hostileRequests (canonicalComputeTrace P)).length := by
  have hlen : (P.hostileRequests (canonicalComputeTrace P)).length =
      P.optimized.family.problem.exec.derivedRequestIO.length := by
    have h := OptimizedCanonicalHostileLists.canonical_hostileRequests P G.hax G.hwidth
    have h' : P.hostileRequests (canonicalComputeTrace P) =
        (honestRecords10 P.optimized.family).requests := h
    rw [h', honestRecords10, RecordCarrier.extRecords_requests,
      List.length_map]
  rw [hlen]
  exact OptimizedHostileTimestamps.not_mem_event_of_le_orderOf hα0 hord

/-- Component 5 over `HgoodFill`. -/
theorem walkRoot_honest (G : HgoodFill P) :
    P.honestTuple.1 ∉ P.computeWalkRootEvent (canonicalComputeTrace P) := by
  have hN := P.optimized.family.problem.cfg.compRows_pos
  refine notMem_rootEvent_of_root_eq_of_isFullBFT _ _ _ _ hN rfl ?_
    (Batch962.isFullBFT_honest P _)
  rw [Batch962.rowLabelVec_honest P ⟨0, hN⟩]
  exact (ComputeWalkSeed.labelVecOfPub_eq_claimLabelVec _ _ _ G.hst G.hs G.hf G.he).symm

theorem hgood_of_fill (G : HgoodFill P)
    (htopE : ComputeExactTopology P.optimized.family.problem.exec)
    (hU : P.honestTuple.1 ∉ ProductionP8Containment.FailureUnion P.strategy
      P.optimized.census P.objects.cfg.challenges.lam)
    (hα0 : alphaM P.honestTuple.1 ≠ 0)
    (hord : P.optimized.family.problem.exec.derivedRequestIO.length ≤
      orderOf (alphaM P.honestTuple.1))
    (hinter : (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.interPole) ∉
      interFailurePairs (P.hostileInterRecords (canonicalMemoryTrace P))
        (P.memorySourceEnv (canonicalMemoryTrace P)) (P.memoryBaseEnv (canonicalMemoryTrace P)))
    (hlam : P.honestTuple ∉ P.decodedLambdaEventOf (canonicalComputeTrace P)
      (canonicalMemoryTrace P))
    (hpair : P.honestTuple.1 ∉ PreSeedCensus.reqPairEventOfEnvs K P.q
      P.optimized.family.problem.cfg.kMem
      (P.optimized.family.problem.cfg.memRows ⊔ P.optimized.Λ)
      (P.memoryBaseEnv (canonicalMemoryTrace P)) P.optimized.family.problem.cfg.memRows_pos
      (PreSeedCensus.requestTargets P.strategy.skeleton)) :
    P.honestTuple ∉ P.optimizedFailureEvent (honestQc P P.honestTuple (QcH P))
      (honestQm P P.honestTuple (QmH P)) := by
  rw [honestQc_QcH, honestQm_QmH]
  refine P.notMem_optimizedFailureEvent_of_components _ _ _ hU
    (hioEvent_honest G) (timestamp_honest G hα0 hord) ?_
    (walkRoot_honest G) (Batch958.tileC_honest P htopE) (Batch959.tileM_honest P)
    ?_ ?_ ?_ hlam hpair
  · have hp : P.honestTuple.2.2.2.interPole = P.optimized.sampled.interPole :=
      P.packageInterPole_eq_sampled
    change (P.optimized.sampled.sampled.coins.gamma, P.honestTuple.2.2.2.interPole) ∉ _
    rw [hp]
    exact hinter
  · rw [Batch962.computePrefixGamma_empty_honest P]; exact Finset.notMem_empty _
  · rw [Batch960.memoryPrefixGamma_empty_honest P]; exact Finset.notMem_empty _
  · rw [Batch960.memoryForestAlpha_empty_honest P]; exact Finset.notMem_empty _

end

end Nock.RedTeam.Batch992

#print axioms Nock.RedTeam.Batch992.HgoodFill.of_honestFill
#print axioms Nock.RedTeam.Batch992.hioEvent_honest
#print axioms Nock.RedTeam.Batch992.timestamp_honest
#print axioms Nock.RedTeam.Batch992.walkRoot_honest
#print axioms Nock.RedTeam.Batch992.hgood_of_fill
