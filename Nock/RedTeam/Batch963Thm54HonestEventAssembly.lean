/-
  Nock/RedTeam/Batch963Thm54HonestEventAssembly.lean

  What this file assembles instead is `hgood` itself
  (`c ∉ optimizedFailureEvent` at the honest tuple and traces) from

  * the PROVED components, at every package: 2 (IO, `Batch909.hioEvent_honest`), 5 (walk root,
    `Batch962.walkRoot_honest`), 7, 8, 9, 10 (`Batch959` / `Batch962` / `Batch960`), and 6 under
    the exec compute topology;

  `HonestEventOpen P` is that open list; `hgood_of_open` is the assembly at any package, and
  `hgood_zero_built` the instance at every built zero-array package (the shape of the generated
  one), where 1 and 6 and `inactiveMem` are discharged.  With `Batch956.genData_seed_good` and
  `Batch957.gen_timestamp_premises` the seed and timestamp premises are theorems at the generated
  carrier, so at a generated package the open list is exactly {4 via `interGamma8` /
  `inactiveCprime`, 11, 12}.
-/
import Nock.RedTeam.Batch956Thm54HonestP8Union
import Nock.RedTeam.Batch957Thm54HonestTimestampInter
import Nock.RedTeam.Batch961Thm54HonestLambdaPairStop
import Nock.RedTeam.Batch962Thm54HonestComputeWalkVec
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Nock.RedTeam.Batch963

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.RedTeam.Batch906
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-- **The open components at the honest instance** (all else is proved). -/
structure HonestEventOpen (P : OptimizedFullStrictNockVMROMPackage F K hOrb) : Prop where
  failureUnion : P.honestTuple.1 ∉ ProductionP8Containment.FailureUnion P.strategy
    P.optimized.census P.objects.cfg.challenges.lam
  /-- Component 3's premises (the §1 binder `α`; `hwin` at the generated carrier). -/
  alphaNe : alphaM P.honestTuple.1 ≠ 0
  alphaOrd : P.optimized.family.problem.exec.derivedRequestIO.length ≤
    orderOf (alphaM P.honestTuple.1)
  inter : (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.interPole) ∉
    interFailurePairs (P.hostileInterRecords (canonicalMemoryTrace P))
      (P.memorySourceEnv (canonicalMemoryTrace P)) (P.memoryBaseEnv (canonicalMemoryTrace P))
  lam : P.honestTuple ∉ P.decodedLambdaEventOf (canonicalComputeTrace P) (canonicalMemoryTrace P)
  pair : P.honestTuple.1 ∉ PreSeedCensus.reqPairEventOfEnvs K P.q
    P.optimized.family.problem.cfg.kMem
    (P.optimized.family.problem.cfg.memRows ⊔ P.optimized.Λ)
    (P.memoryBaseEnv (canonicalMemoryTrace P)) P.optimized.family.problem.cfg.memRows_pos
    (PreSeedCensus.requestTargets P.strategy.skeleton)

/-- **`hgood` at the honest instance from the open components** (any package, under the exec
compute topology). -/
theorem hgood_of_open {P : OptimizedFullStrictNockVMROMPackage F K hOrb} (H : HonestFill P)
    (htopE : ComputeExactTopology P.optimized.family.problem.exec) (O : HonestEventOpen P) :
    P.honestTuple ∉ P.optimizedFailureEvent (honestQc P P.honestTuple (QcH P))
      (honestQm P P.honestTuple (QmH P)) := by
  rw [honestQc_QcH, honestQm_QmH]
  refine P.notMem_optimizedFailureEvent_of_components _ _ _ O.failureUnion
    (Batch909.hioEvent_honest H) (Batch957.timestamp_honest H O.alphaNe O.alphaOrd) ?_
    (Batch962.walkRoot_honest P H) (Batch958.tileC_honest P htopE) (Batch959.tileM_honest P)
    ?_ ?_ ?_ O.lam O.pair
  · have hp : P.honestTuple.2.2.2.interPole = P.optimized.sampled.interPole :=
      P.packageInterPole_eq_sampled
    change (P.optimized.sampled.sampled.coins.gamma, P.honestTuple.2.2.2.interPole) ∉ _
    rw [hp]
    exact O.inter
  · rw [Batch962.computePrefixGamma_empty_honest P]; exact Finset.notMem_empty _
  · rw [Batch960.memoryPrefixGamma_empty_honest P]; exact Finset.notMem_empty _
  · rw [Batch960.memoryForestAlpha_empty_honest P]; exact Finset.notMem_empty _

/-- Component 4 from its four closed-form side conditions (the existing lemma). -/
theorem inter_of_sides {P : OptimizedFullStrictNockVMROMPackage F K hOrb} (H : HonestFill P)
    (h0 : P.optimized.sampled.interPole ≠ 0)
    (hγ8 : P.optimized.sampled.interPole + P.optimized.sampled.sampled.coins.gamma ^ 8 ≠ 0)
    (hz : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .read_root →
      (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .verify_child →
      (P.optimized.family.problem.exec.memoryPubAt i).mem = ComputeTable.MemRec.zero)
    (hzc : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .read_root →
      (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .verify_child →
      (P.optimized.family.problem.exec.memoryPubAt i).cprime = 1) :
    (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.interPole) ∉
      interFailurePairs (P.hostileInterRecords (canonicalMemoryTrace P))
        (P.memorySourceEnv (canonicalMemoryTrace P)) (P.memoryBaseEnv (canonicalMemoryTrace P)) :=
  OptimizedCanonicalHostileLists.canonical_inter_not_hostile_failure P h0 hγ8 hz hzc H.hC

theorem hgood_zero_built (E : BuildableNockExecution F K) (D : Data E) (I : Inputs E)
    (hzero : I.computeChallenges =
      (default : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (H : HonestFill (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord
      hordM hrows))
    (hgoodSeed : E.cfg.challenges.z ∉ D.census.census.badSeeds (K := K))
    (hwin : E.cfg.challenges.z ∉ sizeWindowFailureSeeds (K := K) D.skeleton)
    (hα0 : E.cfg.challenges.α ≠ 0)
    (hαord : E.exec.derivedRequestIO.length ≤ orderOf E.cfg.challenges.α)
    (hγ8 : (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).optimized.sampled.interPole +
      (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).optimized.sampled.sampled.coins.gamma ^ 8 ≠ 0)
    (h0 : (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).optimized.sampled.interPole ≠ 0)
    (hzc : ∀ i : Fin (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord
        hordM hrows).optimized.family.problem.cfg.memRows,
      ((buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).optimized.family.problem.exec.memoryPubAt i).st ≠ .read_root →
      ((buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).optimized.family.problem.exec.memoryPubAt i).st ≠ .verify_child →
      ((buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).optimized.family.problem.exec.memoryPubAt i).cprime = 1)
    (hlam : (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).honestTuple ∉
      (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).decodedLambdaEventOf
        (canonicalComputeTrace (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl
          hmore hord hordM hrows hgenF hF))
        (canonicalMemoryTrace (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl
          hmore hord hordM hrows hgenF hF)))
    (hpair : (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).honestTuple.1 ∉ PreSeedCensus.reqPairEventOfEnvs K
        (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM hrows hgenF hF).q
        (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
          hrows).optimized.family.problem.cfg.kMem
        ((buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
          hrows).optimized.family.problem.cfg.memRows ⊔
          (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
            hrows).optimized.Λ)
        ((buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
          hrows).memoryBaseEnv
          (canonicalMemoryTrace (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl
            hmore hord hordM hrows hgenF hF)))
        (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
          hrows).optimized.family.problem.cfg.memRows_pos
        (PreSeedCensus.requestTargets (buildFullPackage E I (commitmentResidualOfZero D) hzero
          hprl hmore hord hordM hrows hgenF hF).strategy.skeleton)) :
    (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).honestTuple ∉
      (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM
        hrows).optimizedFailureEvent
        (honestQc _ (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord
          hordM hrows).honestTuple (QcH _))
        (honestQm _ (buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord
          hordM hrows).honestTuple (QmH _)) := by
  refine hgood_of_open H E.traversal.1
    { failureUnion := Batch956.honestTuple_not_mem_failureUnion_zero D I hzero hprl hmore hord
        hordM hrows hgenF hF hgoodSeed hwin
      alphaNe := hα0
      alphaOrd := hαord
      inter := inter_of_sides H h0 hγ8
        (Batch957.inactiveMem_buildable E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM hrows hgenF hF) hzc
      lam := hlam
      pair := hpair }

end

end Nock.RedTeam.Batch963

#print axioms Nock.RedTeam.Batch963.hgood_of_open
#print axioms Nock.RedTeam.Batch963.hgood_zero_built
