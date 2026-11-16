import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
import Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
import Nock.NockVMROM.Thm54.OptimizedMemoryFingerprintObstruction
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.ComputeWalkSeed
import Nock.GlobalCarryRecognizer
import Nock.NockVMROM.Thm54.FormRAxisEvent
import Nock.NockVMROM.Thm54.DecodedLambdaEvent
import Nock.NockVMROM.Thm54.PreZCensusCore
import Nock.NockVMROM.Thm54.FamilyEnvCore
import Nock.NockVMROM.Thm54.P8Core.TraceGen.GenAirOrder
import Nock.NockVMROM.Thm54.P8Core.TraceGen.GenTraceConfined

/-!
# Full optimized strict package: the definitions

The package structure `OptimizedFullStrictNockVMROMPackage`, the chip, environment and record layer
built on it (deployed chips at a sampled tuple, honest coins and tuples, memory source environments
and their coin pins), the failure event consumed by the false-acceptance bound together with its
component lemmas (hostile request/response lists and their length bounds, prefix-γ and forest-α
events), and the two row-count majorant abbreviations.  The theorem statement over these objects is
in `OptimizedStrictFullPackage.lean`.
-/

open Nock Nock.NockVMROM Nock.NockVMROM.Thm54
namespace Nock.Walk37

namespace Nock.NockVMROM.Thm54
namespace OptimizedStrictFullPackage

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open MonolithicRAP
open RawSemanticAssembly SemanticStrategy StrictCommitment
open TemplateRawJointSoundness ServedLookupBridge
open ProductionP8Containment
open ProductionAxisStructureVerifier TemplateAxisCounting
open OptimizedComputeCorrectedFinal
open OptimizedComputeFinalTrace
open OptimizedComputeSampledTrace
open OptimizedComputeSemanticRealization
open OptimizedComputeCollisionBound
open OptimizedComputeSubstitution
open OptimizedMemoryRAP
open OptimizedMemoryGateBasis
open OptimizedMemoryCanonicalTrace
open OptimizedMemoryCanonicalSatisfaction
open OptimizedMemoryCollisionAccounting
open OptimizedStrictPackage
open SharedTableWalkRow

noncomputable section

/-- The
optimized same-assignment package is stored instead; no `StrictNockVMROMPackage` is a field. -/
structure OptimizedFullStrictNockVMROMPackage
    (F K : Type) [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    (hOrb : ℕ) where
  optimized : OptimizedStrictNockVMROMPackage F K hOrb
  honestSeed : K
  honestSeed_ne : honestSeed ≠ 0
  honestAlpha : K
  honest_specialization :
    specializedProblem optimized.verifier.raw.timestamp honestSeed honestSeed_ne honestAlpha
        optimized.objects.cfg.challenges.lam =
      ⟨optimized.objects.cfg, optimized.objects.exec⟩
  chained : ChainedSemanticExactLanguage optimized.objects.cfg optimized.objects.exec
  walkFamily : RawPlusIOSegmentedFamily F K
  walkFamily_problem : walkFamily.problem = ⟨optimized.objects.cfg, optimized.objects.exec⟩
  /-- The compute encoder is the `LT_comp` projection, injective on `computeLabelOf` and on
  nothing more. -/
  compEnc_inj : ∀ a b, walkFamily.compNodeEncode a = walkFamily.compNodeEncode b →
    ComputeTable.computeLabelOf a = ComputeTable.computeLabelOf b
  /-- The memory encoder is the `x^mem` projection, injective on `memoryLabelOf` and on nothing
  more. -/
  memEnc_inj : ∀ a b, walkFamily.memNodeEncode a = walkFamily.memNodeEncode b →
    MemoryTable.memoryLabelOf a = MemoryTable.memoryLabelOf b
  computeRowsAccepted : walkFamily.exec.ComputeRowsAccepted
  memoryRowsAccepted : walkFamily.exec.MemoryRowsAccepted
  topologyBinding : RawTopologyBindingResidual walkFamily
  recordEquations : ∀ s ∈ computeSkeletonRows optimized.commitment.skeleton,
    SkeletonRecordEquations s
  ioStrategy :
    FiniteIO.FiniteIOStrategy K 9 optimized.objects.cfg.Ksz (ringChar K)
  io_requests : ioStrategy.records.requests = optimized.objects.reqRecs
  io_responses : ioStrategy.records.responses = optimized.objects.respRecs
  q : ℕ
  stateTagChar : NodeEncoding.StateTagChar K
  q_gt_one : 1 < q
  q_eq_ringChar : q = ringChar K
  skeletonBounded : optimized.commitment.skeleton.BoundedBy q
  combinedBounded : CombinedBoundedBy K q optimized.commitment.skeleton
  KszBound : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
    (specializedProblem optimized.verifier.raw.timestamp z hz α lmb).cfg.Ksz < ringChar K
  progCapacity : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
    (specializedProblem optimized.verifier.raw.timestamp z hz α lmb).exec.derivedRequestIO.length +
        1 ≤
      2 ^ (specializedProblem optimized.verifier.raw.timestamp z hz α lmb).cfg.orbit.h
  memCapacity : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
    (specializedProblem optimized.verifier.raw.timestamp z hz α lmb).exec.derivedResponseIO.length +
        1 ≤
      2 ^ (specializedProblem optimized.verifier.raw.timestamp z hz α lmb).cfg.orbit.h
  /-- Both row-count majorants of the hostile
  IO window lie below the characteristic.  Generated packages fill it from the program-level
  `hrows` (`TraceGen.genPackage_rowsBound_of_hrows`; at `F = ZMod p` from `hF`,
  `TraceGen.GoodSeed.hrows_of_hF`). -/
  rowsBound : 3 * optimized.objects.cfg.compRows < ringChar K ∧
    optimized.objects.cfg.memRows < ringChar K
  /-- Honest data: no trace,
  tuple or chip is mentioned.  Generated packages fill it from the chain's `h` / `hG` /
  `leafBound_of_traceConfined`. -/
  generated :
    ∃ (gfuel : ℕ) (G : Nock.Walk.NTree (TraceGen.GenComputeRow K)) (R : Noun) (fuel : ℕ) (r : Noun),
      TraceGen.genComputeSkeleton (K := K) gfuel optimized.verifier.raw.claim.subject
          optimized.verifier.raw.claim.formula = .ok (G, R) ∧
        FieldEmbedding.evalGBy (ringChar K) fuel optimized.verifier.raw.claim.subject
          optimized.verifier.raw.claim.formula = some r ∧
        TraceGen.programLeafBound (TraceGen.airReorder G) ≤ optimized.Λ
  /-- True at `F = ZMod p`; the general-`F` theorem
  `nockCompiles_p76` carries it as the binder `hF`. -/
  primeField : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x

namespace OptimizedFullStrictNockVMROMPackage

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

abbrev objects := P.optimized.objects
abbrev strategy := P.optimized.strategy

@[simp] theorem strategy_skeleton :
    P.strategy.skeleton = P.optimized.commitment.skeleton := rfl

theorem castInj :
    Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio P.q) := by
  rw [P.q_eq_ringChar]
  exact StrictRawReconstruction.charCast_injOn (ringChar K)

theorem one_le_Ksz : 0 < P.objects.cfg.Ksz := by
  obtain ⟨w⟩ := P.chained.semantic.2.2
  exact Thm54.one_le_Ksz w

theorem perfect_completeness :
    Language
      (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
      (stmtOfExact P.objects.cfg P.objects.exec) :=
  perfect_completeness_is_forward P.chained

theorem shared_io :
    IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs := by
  have h := P.ioStrategy.lio
  rw [P.io_requests, P.io_responses] at h
  exact h

def computeWalkBadRatio : ℚ :=
  ((NockVM.walkBad (ComputeTable.comp_stateSep (K := K)) P.walkFamily.compNodeEncode
      (computeRowLabel P.walkFamily) (computeChildLabel P.walkFamily)
      (Nock.Walk.foCol P.walkFamily.computeWalkRows) P.walkFamily.cfg.compRows).card : ℚ) /
    ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))

def computeWalkBound : ℚ :=
  (P.walkFamily.cfg.compRows : ℚ) / (Fintype.card K : ℚ) +
    ((P.walkFamily.cfg.compRows * (P.walkFamily.compNodeWidth - 1) : ℕ) : ℚ) /
      (Fintype.card K : ℚ)

def memoryWalkBadRatio : ℚ :=
  ((NockVM.walkBadForest (MemoryTable.mem_stateSep (K := K)) P.walkFamily.memNodeEncode
      (memoryRowLabel P.walkFamily) (memoryChildLabel P.walkFamily)
      (Nock.Walk.foCol P.walkFamily.memoryWalkRows) P.walkFamily.exec.memoryForest.length
      P.walkFamily.cfg.memRows).card : ℚ) /
    ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))

def memoryWalkBound : ℚ :=
  (P.walkFamily.cfg.memRows : ℚ) / (Fintype.card K : ℚ) +
    ((P.walkFamily.cfg.memRows * (P.walkFamily.memNodeWidth - 1) : ℕ) : ℚ) /
      (Fintype.card K : ℚ)

theorem computeWalk_bound : P.computeWalkBadRatio ≤ P.computeWalkBound :=
  computeWalk_final_prob_of_acceptance_of_label P.walkFamily.compNodeEncode P.compEnc_inj
    P.walkFamily P.computeRowsAccepted P.topologyBinding

theorem memoryWalk_bound : P.memoryWalkBadRatio ≤ P.memoryWalkBound :=
  memoryWalk_final_prob_of_acceptance_of_label P.walkFamily.memNodeEncode P.memEnc_inj
    P.walkFamily P.memoryRowsAccepted P.topologyBinding

theorem containment (ω : JointCoins K) (lmb : K)
    (hacc : P.strategy.Accepts ω lmb)
    (hout : ω ∉ ProductionP8Containment.FailureUnion P.strategy P.optimized.census lmb) :
    GenuineTargetAt P.strategy P.q P.optimized.Λ ω lmb :=
  verifierGeneratedTopologyRawContainment_of_slotSemantics
    P.optimized.verifier P.optimized.commitment P.q
    P.optimized.claim_eq P.optimized.shapeMatch P.optimized.rowFrame P.optimized.scan
    P.optimized.census P.stateTagChar P.q_gt_one P.q_eq_ringChar P.castInj
    P.skeletonBounded P.combinedBounded P.recordEquations P.optimized.slotSemantics
    P.KszBound P.progCapacity P.memCapacity ω lmb hacc hout
    (fun hz i => P.optimized.verifier.familyAt_memoryLambda ω lmb hz i)

include P in
theorem two_ne_zero : (2 : K) ≠ 0 := by
  intro hzero
  have hnat : (2 : ℕ) = 0 :=
    P.stateTagChar (show (2 : ℕ) ∈ Set.Iic 11 by simp)
      (show (0 : ℕ) ∈ Set.Iic 11 by simp) (by simpa using hzero)
  omega

theorem p8_fixedField_falseAcceptance_le (lmb : K) :
    |jointProbability
        (FalseAcceptanceSet P.strategy P.q P.optimized.Λ lmb)| ≤
      (workload P.strategy P.optimized.Λ
          (fixedTopologyWorkload P.strategy)
          (fixedAxisWorkload P.strategy) : ℝ) /
        (Fintype.card K : ℝ) :=
  jointProbability_falseAcceptance_le (two_ne_zero P) P.strategy lmb
    P.optimized.census P.q
    (fixedTopologyWorkload P.strategy) (fixedAxisWorkload P.strategy)
    (by simpa using P.optimized.sizeWindowBound)
    (topologyWorkload_le_fixedTopologyWorkload P.strategy)
    (templateAxisWorkload_le_fixedAxisWorkload P.strategy) (fun ω => P.containment ω lmb)

theorem p8_fixedField_falseAcceptance_le_two_pow_neg
    (lmb : K) (b : ℕ)
    (hsupport :
      workload P.strategy P.optimized.Λ
          (fixedTopologyWorkload P.strategy)
          (fixedAxisWorkload P.strategy) * 2 ^ b ≤ Fintype.card K) :
    |jointProbability
        (FalseAcceptanceSet P.strategy P.q P.optimized.Λ lmb)| ≤ 1 / 2 ^ b := by
  refine (P.p8_fixedField_falseAcceptance_le lmb).trans ?_
  have hcard : (0 : ℝ) < (Fintype.card K : ℝ) := by positivity
  have hpow : (0 : ℝ) < 2 ^ b := by positivity
  have hreal :
      (workload P.strategy P.optimized.Λ
          (fixedTopologyWorkload P.strategy)
          (fixedAxisWorkload P.strategy) : ℝ) * 2 ^ b ≤
        (Fintype.card K : ℝ) := by
    exact_mod_cast hsupport
  rw [div_le_div_iff₀ hcard hpow]
  linarith

abbrev computeChip : FixedPreprocessingRAP F :=
  ProductionNamedComputeRAP P.optimized.family.problem.cfg.compRows_pos
    P.optimized.computeNodes P.optimized.basis P.optimized.computeChallenge
    P.optimized.computePublic P.optimized.orbit

abbrev memoryChip : FixedPreprocessingRAP F :=
  namedFinalMemoryRAP P.optimized.family.problem.cfg.memRows_pos
    P.optimized.memoryNodes P.optimized.basis P.optimized.memoryChallenge
    P.optimized.memoryPublic P.optimized.orbit
    P.optimized.family.problem.cfg.kMem

/-- Family compute publics at tuple `c`: slots `0..2` are the walk's
    `initial_count = alphaC c.1`,
    slots `3..5` the verifier seed `seedOfClaim`; every other
    slot is the package map. -/
abbrev familyComputePublic [Fintype F] (c : OptimizedProductionChallengeTuple K F) : ℕ → F :=
  DeployedChipFamily.computePublicOfTuple P.optimized.basis
    P.optimized.verifier.raw.claim P.optimized.computePublic c

/-- Deployed compute chip at a sampled tuple.  Gate bodies are those of `computeChip`;
`chalVal` is `computeChalValOfTuple P.optimized.basis c`; publics are
`familyComputePublic c`. -/
abbrev computeChipAt [Fintype F] (c : OptimizedProductionChallengeTuple K F) : FixedPreprocessingRAP F :=
  DeployedChipFamily.computeChipAt P.optimized.family.problem.cfg.compRows_pos
    P.optimized.computeNodes P.optimized.basis
    (P.familyComputePublic c) P.optimized.orbit c

/-- Family memory publics at tuple `c`: slots `6..8` are the memory walk's
    `initial_count = alphaM c.1 ^ kMem` — the forest recognizer's `α^k`; every other slot (the seed `9..11`,
    `requests` `12..14`) is the package map. -/
abbrev familyMemoryPublic [Fintype F] (c : OptimizedProductionChallengeTuple K F) : ℕ → F :=
  DeployedChipFamily.memoryPublicOfTuple P.optimized.basis
    P.optimized.verifier.raw.claim P.optimized.family.problem.cfg.kMem
    P.optimized.memoryPublic c

/-- Deployed memory chip at a sampled tuple.  Gate bodies are those of `memoryChip`;
`chalVal` is `memoryChalValOfTuple P.optimized.basis c`; publics are
`familyMemoryPublic c` (slots `6..8` = `alphaM c.1 ^ kMem`). -/
abbrev memoryChipAt [Fintype F] (c : OptimizedProductionChallengeTuple K F) : FixedPreprocessingRAP F :=
  DeployedChipFamily.memoryChipAt P.optimized.family.problem.cfg.memRows_pos
    P.optimized.memoryNodes P.optimized.basis (P.familyMemoryPublic c)
    P.optimized.orbit c P.optimized.family.problem.cfg.kMem

/-! Thin re-exports at `O := P.optimized` of `FamilyEnvCore`, re-parameterised over
`OptimizedStrictNockVMROMPackage` (definitionally equal).  `famIOEventOf` is re-exported by its
body (definitionally the lifted one). -/

/-- Reindex a constant-chip compute trace at the family width. -/
abbrev familyQc [Fintype F] [DecidableEq F] (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin P.computeChip.rap.w → F[X]) : Fin (P.computeChipAt c).rap.w → F[X] :=
  FamilyEnvCore.familyQc P.optimized c Qc

/-- Reindex a constant-chip memory trace at the family width. -/
abbrev familyQm [Fintype F] [DecidableEq F] (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X]) : Fin (P.memoryChipAt c).rap.w → F[X] :=
  FamilyEnvCore.familyQm P.optimized c Qm

/-- Family-chip compute row environment. -/
abbrev rowEnvAt [Fintype F] [DecidableEq F] (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) : CorrectedFinalTypedEnv F K :=
  FamilyEnvCore.rowEnvAt P.optimized c Qc i

/-- Base-field family memory row environment of a family trace. -/
abbrev memEnvF [Fintype F] [DecidableEq F] (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) : Env F :=
  FamilyEnvCore.memEnvF P.optimized c Qm i

/-- Gathered `𝕂` family memory row environment of a family trace. -/
abbrev memEnvK [Fintype F] [DecidableEq F] (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) : Env K :=
  FamilyEnvCore.memEnvK P.optimized c Qm i

/-- The request list a family compute trace commits to. -/
abbrev hostileRequestsAt [Fintype F] [DecidableEq F] (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X]) : List (Fin 10 → K) :=
  FamilyEnvCore.hostileRequestsAt P.optimized c Qc

/-- The records both family chips commit to. -/
abbrev hostileRecordsAt [Fintype F] [DecidableEq F] (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (Qc : Fin (P.computeChipAt c).rap.w → F[X]) : FiniteIO.PreChallengeRecords K 10 :=
  FamilyEnvCore.hostileRecordsAt P.optimized c Qm Qc

abbrev famIOEventOf [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.filter fun c =>
    c.2.1 ∈ FiniteIO.IOFailureEvent (P.hostileRecordsAt c (P.familyQm c Qm) (P.familyQc c Qc))

theorem famIOEventOf_card_le [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (P.famIOEventOf Qc Qm).card ≤
      Fintype.card K ^ 9 *
        FiniteIO.ioFailureUnionBound 10 (3 * P.optimized.family.problem.cfg.compRows)
          P.optimized.family.problem.cfg.memRows (Fintype.card K) :=
  FamilyEnvCore.famIOEventOf_card_le P.optimized Qc Qm

/-- `(a, b, c)` sit at `c.2.2.1`.  `MemoryTable.formRDefault` is only a
fixture's sample of that coordinate. -/
def honestProductionTuple [Fintype F] (j : JointCoins K) (lmb : K) :
    OptimizedProductionChallengeTuple K F :=
  (j,
    ((P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole),
      (⟨P.objects.cfg.challenges.a, P.objects.cfg.challenges.b, P.objects.cfg.challenges.c⟩,
        ⟨∑ k : Fin 3,
          P.optimized.memoryChallenge (6 + 3 * 6 + (k : ℕ)) • P.optimized.basis k,
          lmb⟩)))

/-- The tuple's `λ` coordinate is the sampled `λ`. -/
@[simp] theorem honestProductionTuple_lambda [Fintype F] (j : JointCoins K) (lmb : K) :
    (P.honestProductionTuple (F := F) j lmb).2.2.2.lambda = lmb := rfl

/-- Honest JointCoins: compute-walk `αc`, walk-node RLC `γ`, timestamp `α`, NPR seed `z`. -/
def honestJointCoins : JointCoins K :=
  ((P.optimized.family.computeWalkAlpha, P.optimized.family.walkGamma),
    (P.objects.cfg.challenges.α, P.objects.cfg.challenges.z))

/-- The honest production tuple at the package's own coins: the joint coins of its objects and
the `λ` its objects were specialized at (`objects.cfg.challenges.lam`). -/
def honestTuple [Fintype F] : OptimizedProductionChallengeTuple K F :=
  P.honestProductionTuple P.honestJointCoins P.objects.cfg.challenges.lam

/-- `computeKOfTuple` at the honest tuple is `exactFinalChallenge` of the package
assignment — including slots `2,3,4 ↦ (a,b,c)`. -/
theorem computeKOfTuple_honest [Fintype F] (q : ℕ) :
    DeployedChipFamily.computeKOfTuple P.honestTuple q =
      OptimizedComputeSameExecution.exactFinalChallenge P.optimized.sampled q := by
  have hcfg :
      P.optimized.family.problem.cfg.challenges = P.objects.cfg.challenges :=
    congrArg ExactConfig.challenges P.optimized.family_cfg
  match q with
  | 0 =>
      simp [DeployedChipFamily.computeKOfTuple, honestTuple, honestProductionTuple,
        honestJointCoins, OptimizedComputeSameExecution.exactFinalChallenge,
        alphaM, ChallengeVector.computeInputs, hcfg]
  | 1 =>
      simp [DeployedChipFamily.computeKOfTuple, honestTuple, honestProductionTuple,
        honestJointCoins, OptimizedComputeSameExecution.exactFinalChallenge,
        nprSeed, ChallengeVector.computeInputs, hcfg]
  | 2 =>
      simp [DeployedChipFamily.computeKOfTuple, honestTuple, honestProductionTuple,
        OptimizedComputeSameExecution.exactFinalChallenge,
        ChallengeVector.computeInputs, hcfg]
  | 3 =>
      simp [DeployedChipFamily.computeKOfTuple, honestTuple, honestProductionTuple,
        OptimizedComputeSameExecution.exactFinalChallenge,
        ChallengeVector.computeInputs, hcfg]
  | 4 =>
      simp [DeployedChipFamily.computeKOfTuple, honestTuple, honestProductionTuple,
        OptimizedComputeSameExecution.exactFinalChallenge,
        ChallengeVector.computeInputs, hcfg]
  | 5 =>
      simp [DeployedChipFamily.computeKOfTuple, honestTuple, honestProductionTuple,
        honestJointCoins, OptimizedComputeSameExecution.exactFinalChallenge,
        nprSeed, ChallengeVector.computeInputs, hcfg]
  | 6 =>
      simp [DeployedChipFamily.computeKOfTuple, honestTuple, honestProductionTuple,
        honestJointCoins, OptimizedComputeSameExecution.exactFinalChallenge,
        alphaC]
  | 7 =>
      simp [DeployedChipFamily.computeKOfTuple, honestTuple, honestProductionTuple,
        OptimizedComputeSameExecution.exactFinalChallenge]
  | 8 =>
      simp [DeployedChipFamily.computeKOfTuple, honestTuple, honestProductionTuple,
        OptimizedComputeSameExecution.exactFinalChallenge]
  | 9 =>
      simp [DeployedChipFamily.computeKOfTuple, honestTuple, honestProductionTuple,
        OptimizedComputeSameExecution.exactFinalChallenge, hcfg]
  | 10 =>
      simp [DeployedChipFamily.computeKOfTuple, honestTuple, honestProductionTuple,
        honestJointCoins, OptimizedComputeSameExecution.exactFinalChallenge, gamma]
  | _ + 11 =>
      simp [DeployedChipFamily.computeKOfTuple,
        OptimizedComputeSameExecution.exactFinalChallenge]

/-- `chalValOfTuple_honest` on every cubic slot the compute chip can read.
Slots `2,3,4` carry `cfg.challenges.a,b,c`, not `0`. -/
theorem chalValOfTuple_honest [Fintype F] (q : Fin 12) (k : Fin 3) :
    DeployedChipFamily.computeChalValOfTuple P.optimized.basis P.honestTuple
        (3 * (q : ℕ) + (k : ℕ)) =
      P.optimized.computeChallenge (3 * (q : ℕ) + (k : ℕ)) := by
  rw [DeployedChipFamily.computeChalValOfTuple_slot, P.optimized.computeChallengePins]
  exact congrArg (fun z => CoordinateBasis.coord P.optimized.basis z k)
    (P.computeKOfTuple_honest q)

/-- Honest family seed equals the verifier seed once the root `LT_comp` label is
    the claim's.
    `s`/`f`/`e` are `BindsAt.root_bindings`; the state hypothesis is
    `genComputeSkeleton_root_state`. -/
theorem computeWalkSeed_eq_seedOfClaim_honest [Fintype F]
    (hst :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).state =
        ComputeWalkSeed.rootStateOfFormula P.optimized.verifier.raw.claim.formula)
    (hs :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).s =
        GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1)
          P.optimized.verifier.raw.claim.subject)
    (hf :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).f =
        GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1)
          P.optimized.verifier.raw.claim.formula)
    (he :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).e =
        GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1)
          P.optimized.verifier.raw.claim.result) :
    P.optimized.family.computeWalkSeed =
      ComputeWalkSeed.seedOfClaim P.optimized.verifier.raw.claim P.honestTuple := by
  have hEnc : ∀ t, P.optimized.family.computeNodeVal t =
      Nock.Walk.rlc P.optimized.family.walkGamma
        (ComputeTable.labelVecOfPub t.label.2.2.1) :=
    P.optimized.computeObligations.2.2.2.1
  have hγ : gamma P.honestTuple.1 = P.optimized.family.walkGamma := by
    simp [honestTuple, honestProductionTuple, honestJointCoins, gamma]
  have hα : alphaC P.honestTuple.1 = P.optimized.family.computeWalkAlpha := by
    simp [honestTuple, honestProductionTuple, honestJointCoins, alphaC]
  exact ComputeWalkSeed.computeWalkSeed_eq_seedOfClaim
    (R := P.optimized.family) hEnc P.optimized.verifier.raw.claim P.honestTuple
    hγ hα hst hs hf he

/-- RAP structures compare `chalVal` and `pubVal` as functions.  After the seed
    wiring, publics agree at `honestTuple` once the honest seed is the verifier
    seed (`genComputeSkeleton_root_state` + `root_bindings`).  The family's `initial_count` slots
    `0..2` read `alphaC c.1`; at `honestTuple` that is the family's `computeWalkAlpha` by `rfl`
    (`honestJointCoins`), so no further hypothesis is needed. -/
theorem computeChipAt_honest_of_chalVal [Fintype F]
    (h : DeployedChipFamily.computeChalValOfTuple P.optimized.basis P.honestTuple =
      P.optimized.computeChallenge)
    (hst :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).state =
        ComputeWalkSeed.rootStateOfFormula P.optimized.verifier.raw.claim.formula)
    (hs :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).s =
        GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1)
          P.optimized.verifier.raw.claim.subject)
    (hf :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).f =
        GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1)
          P.optimized.verifier.raw.claim.formula)
    (he :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).e =
        GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1)
          P.optimized.verifier.raw.claim.result) :
    P.computeChipAt P.honestTuple = P.computeChip := by
  have hpub :
      DeployedChipFamily.computePublicOfTuple P.optimized.basis
        P.optimized.verifier.raw.claim P.optimized.computePublic P.honestTuple =
        P.optimized.computePublic :=
    DeployedChipFamily.computePublicOfTuple_eq_pkg_of_seed
      P.optimized.basis P.optimized.verifier.raw.claim P.optimized.family
      P.optimized.family.problem.cfg.compRows_pos P.optimized.computePublic
      P.honestTuple P.optimized.computePublicPins rfl
      (computeWalkSeed_eq_seedOfClaim_honest P hst hs hf he).symm
  simp only [computeChipAt, computeChip, DeployedChipFamily.computeChipAt, hpub]
  congr

/-- `memoryKOfTuple` at the honest tuple reads the family's
walk-node RLC coin `walkGamma` at memory slot `7` — the coin the in-gate `x^mem` label RLCs
read. -/
theorem memoryKOfTuple_honest_walkGamma [Fintype F] :
    DeployedChipFamily.memoryKOfTuple P.honestTuple 7 = P.optimized.family.walkGamma := by
  simp [DeployedChipFamily.memoryKOfTuple, honestTuple, honestProductionTuple, honestJointCoins,
    gamma]

/-- **The memory honest identity.**  At the honest tuple, once the
memory `chalVal` agrees with the package's, the family memory publics ARE the package map: the
chalVal agreement at walk-α slot `3` (`memoryChalValOfTuple_slot`, `memoryKOfTuple c 3 = alphaM
c.1`) with the package pin `walkChallenge` gives `alphaM honestTuple = memoryWalkAlpha`, and
`walkInitialCount` pins publics `6..8` to `memoryWalkAlpha ^ kMem`
(`DeployedChipFamily.memoryPublicOfTuple_eq_pkg_of_alpha`).  No hypothesis beyond `h`. -/
theorem familyMemoryPublic_honest_of_chalVal [Fintype F]
    (h : DeployedChipFamily.memoryChalValOfTuple P.optimized.basis P.honestTuple =
      P.optimized.memoryChallenge) :
    P.familyMemoryPublic P.honestTuple = P.optimized.memoryPublic := by
  have hα : alphaM P.honestTuple.1 = P.optimized.family.memoryWalkAlpha := by
    have hpin := P.optimized.memoryCoordinatePins.walkChallenge
    have hslot : ∀ k : Fin 3,
        P.optimized.memoryChallenge (6 + 3 * 3 + (k : ℕ)) =
          CoordinateBasis.coord P.optimized.basis (alphaM P.honestTuple.1) k := by
      intro k
      rw [← h]
      exact DeployedChipFamily.memoryChalValOfTuple_slot P.optimized.basis P.honestTuple
        ⟨3, by decide⟩ k
    rw [← hpin]
    simp only [hslot]
    exact (CoordinateBasis.reconstruct_coord P.optimized.basis _).symm
  exact DeployedChipFamily.memoryPublicOfTuple_eq_pkg_of_alpha P.optimized.basis
    P.optimized.verifier.raw.claim P.optimized.family P.optimized.sampled
    P.optimized.memoryChallenge P.optimized.memoryPublic P.honestTuple
    P.optimized.memoryCoordinatePins hα

/-- The deployed memory chip at the honest tuple IS the package's memory chip once `chalVal`
agrees (`familyMemoryPublic_honest_of_chalVal` + the chalVal pin). -/
theorem memoryChipAt_honest_of_chalVal [Fintype F]
    (h : DeployedChipFamily.memoryChalValOfTuple P.optimized.basis P.honestTuple =
      P.optimized.memoryChallenge) :
    P.memoryChipAt P.honestTuple = P.memoryChip := by
  simp only [memoryChipAt, memoryChip, DeployedChipFamily.memoryChipAt, h,
    P.familyMemoryPublic_honest_of_chalVal h]

/-- Satisfaction of the honest chip is satisfaction of `computeChipAt honestTuple`
once `chalVal` agrees: the RAP structures are equal
(`computeChipAt_honest_of_chalVal`).  Stated as structure equality because
`SatisfiesWithPreprocessing C Qc` is dependent in `C.rap.w`. -/

theorem compute_row_budget :
    P.computeChip.rap.H.card = P.objects.cfg.compRows := by
  change (rowNodeSet P.optimized.computeNodes).card = _
  exact P.optimized.exact_row_domains.1.trans
    (congrArg ExactConfig.compRows P.optimized.family_cfg)

theorem memory_row_budget :
    P.memoryChip.rap.H.card =
      RowLayout.memoryM P.objects.exec + 2 * RowLayout.memoryL P.objects.exec := by
  change (rowNodeSet P.optimized.memoryNodes).card = _
  rw [P.optimized.exact_row_domains.2, P.optimized.family_cfg]
  exact RowLayout.memRows_eq_M_add_two_mul_L_of_count_balance
    P.optimized.recordCountBalance

/-- The full two-RAP realization relation: optimized chips, one execution, shared IO, both walks,
and the aggregate forest/axis connective. -/
structure OptimizedFullTwoRAPRealization : Prop where
  optimized_chips :
    OptimizedComputeRealizationAt P.optimized.sampled P.optimized.computeObligations
        P.optimized.computeNodes P.optimized.basis P.optimized.computeChallenge
        P.optimized.computePublic P.optimized.orbit ∧
      OptimizedMemoryRealizationAt P.optimized.sampled P.optimized.memoryProduction
        P.optimized.memoryNodes P.optimized.basis P.optimized.memoryChallenge
        P.optimized.memoryPublic P.optimized.orbit
  compute_chip_domain : P.computeChip.rap.H = rowNodeSet P.optimized.computeNodes
  memory_chip_domain : P.memoryChip.rap.H = rowNodeSet P.optimized.memoryNodes
  compute_row_budget : P.computeChip.rap.H.card = P.objects.cfg.compRows
  memory_row_budget :
    P.memoryChip.rap.H.card =
      RowLayout.memoryM P.objects.exec + 2 * RowLayout.memoryL P.objects.exec
  walk_family : P.walkFamily.problem = ⟨P.objects.cfg, P.objects.exec⟩
  shared_io : IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs
  compute_walk_bound : P.computeWalkBadRatio ≤ P.computeWalkBound
  memory_walk_bound : P.memoryWalkBadRatio ≤ P.memoryWalkBound
  aggregate_forest_axis : P.optimized.OptimizedSharedMemoryConnective

theorem optimizedFullTwoRAPRealizationOf
    (hchips :
      OptimizedComputeRealizationAt P.optimized.sampled P.optimized.computeObligations
          P.optimized.computeNodes P.optimized.basis P.optimized.computeChallenge
          P.optimized.computePublic P.optimized.orbit ∧
        OptimizedMemoryRealizationAt P.optimized.sampled P.optimized.memoryProduction
          P.optimized.memoryNodes P.optimized.basis P.optimized.memoryChallenge
          P.optimized.memoryPublic P.optimized.orbit) :
    P.OptimizedFullTwoRAPRealization where
  optimized_chips := hchips
  compute_chip_domain := rfl
  memory_chip_domain := rfl
  compute_row_budget := P.compute_row_budget
  memory_row_budget := P.memory_row_budget
  walk_family := P.walkFamily_problem
  shared_io := P.shared_io
  compute_walk_bound := P.computeWalk_bound
  memory_walk_bound := P.memoryWalk_bound
  aggregate_forest_axis := P.optimized.shared_memory_connective

theorem optimizedFullTwoRAPRealization
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    P.OptimizedFullTwoRAPRealization :=
  P.optimizedFullTwoRAPRealizationOf
    (P.optimized.realization_surface_of_leafCover hax hbasis hwidth)

/-- **Theorem 5.4's efficiency requirements.**

`Def:RAP` makes `(𝕂, e)` a component of the RAP tuple, recorded as the
structure field `RAP.e`, and Theorem 5.4 states every resource of both chips as an *affine
function of that `e`* rather than as a numeral.  These conjuncts name the paper's formulas,
evaluated at each chip's own recorded extension degree, and pin that degree to the one this tree
deploys.  At `e = 3` this is equivalent to the numeric form, which
`exact_resources_iff_deployed_numerals` proves.

The parametric shape is what makes a `𝕂`-valued gate expressible: such a gate is committed by
its `e` base-field coordinates, so retyping a scalar gate moves a `+1` to a `+e` — a change of
coefficient in a formula the paper already writes affinely, not a broken numeral. -/
structure OptimizedFullCostRealization : Prop where
  exact_resources :
    let C := P.computeChip
    let M := P.memoryChip
    (C.rap.e = Thm54Resources.deployedExtensionDegree ∧
        C.rap.w = Thm54Resources.computeColumns C.rap.e ∧
        C.rap.s = Thm54Resources.computeConstraints C.rap.e ∧
        C.rap.d = Thm54Resources.maxConstraintDegree ∧
        C.rap.k = Thm54Resources.computeCommittedRounds) ∧
      (M.rap.e = Thm54Resources.deployedExtensionDegree ∧
        M.rap.w = Thm54Resources.memoryColumns M.rap.e ∧
        M.rap.s = Thm54Resources.memoryConstraints M.rap.e ∧
        M.rap.d = Thm54Resources.maxConstraintDegree ∧
        M.rap.k = Thm54Resources.memoryCommittedRounds)
  transition_fingerprints :
    P.computeChip.rap.s
        - Thm54Resources.computeEndpointConstraints P.computeChip.rap.e
        = Thm54Resources.computeTransitionGates P.computeChip.rap.e ∧
      P.memoryChip.rap.s
        - Thm54Resources.memoryEndpointConstraints P.memoryChip.rap.e
        = Thm54Resources.memoryTransitionGates P.memoryChip.rap.e
  compute_row_budget : P.computeChip.rap.H.card = P.objects.cfg.compRows
  memory_row_budget :
    P.memoryChip.rap.H.card =
      RowLayout.memoryM P.objects.exec + 2 * RowLayout.memoryL P.objects.exec

theorem optimizedFullCostRealization : P.OptimizedFullCostRealization :=
  ⟨P.optimized.exact_chip_resources_paper, P.optimized.exact_transition_fingerprints_paper,
    P.compute_row_budget, P.memory_row_budget⟩

/-- **The parametric `exact_resources` conjunct, read back as numerals.**  It is equivalent to the
numeric form `(w, s, d, k) = (303, 418, 4, 2)` for the compute chip and `(205, 156, 4, 1)` for the
memory chip at `e = 3`, together with the pin of each chip's recorded extension degree to `3` that
the parametric statement carries as its first conjunct.  Both directions are proved from
`Thm54Resources.compute_resources_iff` / `memory_resources_iff`.

Writing the conjunct affinely is what makes a `𝕂`-valued gate expressible: the four memory equality
checks are `𝕂`-valued mixed gates, so `Thm54Resources.memoryEqualityChecks` is `4·e` (`12` committed
base-field gates at `e = 3`) rather than the constant `4`. -/
theorem exact_resources_iff_deployed_numerals :
    (let C := P.computeChip
     let M := P.memoryChip
     (C.rap.e = Thm54Resources.deployedExtensionDegree ∧
        C.rap.w = Thm54Resources.computeColumns C.rap.e ∧
        C.rap.s = Thm54Resources.computeConstraints C.rap.e ∧
        C.rap.d = Thm54Resources.maxConstraintDegree ∧
        C.rap.k = Thm54Resources.computeCommittedRounds) ∧
      (M.rap.e = Thm54Resources.deployedExtensionDegree ∧
        M.rap.w = Thm54Resources.memoryColumns M.rap.e ∧
        M.rap.s = Thm54Resources.memoryConstraints M.rap.e ∧
        M.rap.d = Thm54Resources.maxConstraintDegree ∧
        M.rap.k = Thm54Resources.memoryCommittedRounds))
      ↔
    (let C := P.computeChip
     let M := P.memoryChip
     (C.rap.e = 3 ∧ C.rap.w = 303 ∧ C.rap.s = 418 ∧ C.rap.d = 4 ∧ C.rap.k = 2) ∧
      (M.rap.e = 3 ∧ M.rap.w = 205 ∧ M.rap.s = 156 ∧ M.rap.d = 4 ∧ M.rap.k = 1)) := by
  dsimp only
  exact and_congr (Thm54Resources.compute_resources_iff _ _ _ _ _)
    (Thm54Resources.memory_resources_iff _ _ _ _ _)

/-- **The numeric fingerprint, read off the parametric field:** the column, gate-count, degree and
round numerals of both chips, and the transition counts `s - 44 = 374` (compute) and `s - 0 = 156`
(memory). -/
theorem cost_realization_deployed_numerals (R : P.OptimizedFullCostRealization) :
    (P.computeChip.rap.w = 303 ∧ P.computeChip.rap.s = 418 ∧
        P.computeChip.rap.d = 4 ∧ P.computeChip.rap.k = 2) ∧
      (P.memoryChip.rap.w = 205 ∧ P.memoryChip.rap.s = 156 ∧
        P.memoryChip.rap.d = 4 ∧ P.memoryChip.rap.k = 1) ∧
      (P.computeChip.rap.s - 44 = 374 ∧ P.memoryChip.rap.s - 0 = 156) := by
  have hnum := P.exact_resources_iff_deployed_numerals.mp R.exact_resources
  have htr := R.transition_fingerprints
  dsimp only at hnum htr
  refine ⟨⟨hnum.1.2.1, hnum.1.2.2.1, hnum.1.2.2.2.1, hnum.1.2.2.2.2⟩,
    ⟨hnum.2.2.1, hnum.2.2.2.1, hnum.2.2.2.2.1, hnum.2.2.2.2.2⟩, ?_, ?_⟩
  · exact (Thm54Resources.compute_transition_fingerprint_iff _ _
      (R.exact_resources.1.1)).mp htr.1
  · exact (Thm54Resources.memory_transition_fingerprint_iff _ _
      (R.exact_resources.2.1)).mp htr.2

@[reducible] def structural
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    VerifiableVMCompilation
      (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
      (nmrMEF F K) K 10 3
      (∀ lmb : K, FixedFieldSoundnessClaim P.strategy P.q P.optimized.Λ lmb)
      P.p8_fixedField_falseAcceptance_le
      (OptimizedFullCostRealization P)
      P.optimizedFullCostRealization
      (CombinedCompletenessAt P.objects.cfg P.objects.exec)
      (exactChainedHasPerfectCompleteness F K P.objects.cfg P.objects.exec)
      (OptimizedFullTwoRAPRealization P)
      (P.optimizedFullTwoRAPRealization hax hbasis hwidth)
      (nock_uniqueMES F K _ _ _)
      (ExactChainedHasCanonicalRAP2 F K)
      (exactChainedHasCanonicalRAP2 F K)
      (OneHotRealization P.objects.cfg P.objects.exec)
      P.chained.oneHotRealization
      (DefTraversableRealization P.objects.cfg)
      (defTraversableRealization P.objects.cfg P.objects.exec.memoryRootCount_pos)
      ⟨⟨stmtOfExact P.objects.cfg P.objects.exec, P.perfect_completeness⟩⟩ :=
  ⟨⟩

/-! ## One accepted trace pair and one complete challenge tuple -/

def computeBaseEnv
    (Qc : Fin P.computeChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) : Env F :=
  envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
    P.optimized.computeChallenge P.optimized.computePublic

def computeSourceEnv
    (Qc : Fin P.computeChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) : Env K :=
  (gatherCorrectedFinalTypedEnv P.optimized.basis (P.computeBaseEnv Qc i)).toSourceEnv

def computeWalkEnv (Qc : Fin P.computeChip.rap.w → F[X]) : Env K :=
  P.computeSourceEnv Qc ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩

def computeScalarEnv (Qc : Fin P.computeChip.rap.w → F[X]) : Env F :=
  P.computeBaseEnv Qc ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩

def memorySourceTrace
    (Qm : Fin P.memoryChip.rap.w → F[X]) : Fin 182 → F[X] :=
  RAPPadding.projectTrace
    (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
      P.optimized.memoryNodes P.optimized.basis P.optimized.memoryChallenge
      P.optimized.memoryPublic P.optimized.orbit
      P.optimized.family.problem.cfg.kMem).rap
    (RAPPadding.firstRoundExtra
      (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
        P.optimized.memoryNodes P.optimized.basis P.optimized.memoryChallenge
        P.optimized.memoryPublic P.optimized.orbit
        P.optimized.family.problem.cfg.kMem).rap
      (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
        P.optimized.memoryNodes P.optimized.basis P.optimized.memoryChallenge
        P.optimized.memoryPublic P.optimized.orbit
        P.optimized.family.problem.cfg.kMem).rounds_pos
      (RAPPadding.memoryResidualColumns 3)) Qm

def memoryBaseEnv
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) : Env F :=
  envOfTrace (P.memorySourceTrace Qm) P.optimized.orbit.ω
    (P.optimized.memoryNodes i) P.optimized.memoryChallenge P.optimized.memoryPublic

def memorySourceEnv
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) : Env K :=
  gatherEnv P.optimized.basis ((memorySourceTemplate P.optimized.basis).col0 3)
    (P.memoryBaseEnv Qm i)

def memoryScalarFamilies
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) : Fin 7 → Fin 3 → F :=
  repairedMemoryScalarFamilies P.optimized.basis (P.memoryBaseEnv Qm i)

/-- **The memory chip's `𝕂` challenge slots `4`/`5` are the package's sampled IO coins, at every
row and for every candidate trace**: a challenge is not a trace column, so
`memorySourceEnv Qm i` reads it off `P.optimized.memoryChallenge`, which the package pins to the
sampled coins (`OptimizedStrictNockVMROMPackage.memoryCoordinatePins.sampledGamma`/`sampledPole`).
This is what every constructor of `OptimizedProductionAcceptanceAt.memory_sampled_coins` supplies,
once `sampled_io_coins` has identified the tuple's coins with the package's. -/
theorem memorySourceEnv_sampled_coins
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (P.memorySourceEnv Qm i).chal 4 = P.optimized.sampled.sampled.coins.gamma ∧
      (P.memorySourceEnv Qm i).chal 5 = P.optimized.sampled.sampled.coins.pole :=
  ⟨P.optimized.memoryCoordinatePins.sampledGamma, P.optimized.memoryCoordinatePins.sampledPole⟩

/-- The memory chip's `𝕂` challenge slot `6` is the package's internal `intermediate` LogUp pole
A challenge is not a trace column, so `memorySourceEnv Qm i` reads it
off `P.optimized.memoryChallenge` at physical slots `24..26`. -/
def packageInterPole : K :=
  ∑ k : Fin 3, P.optimized.memoryChallenge (6 + 3 * 6 + (k : ℕ)) • P.optimized.basis k

theorem memorySourceEnv_inter_pole
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (P.memorySourceEnv Qm i).chal 6 = P.packageInterPole :=
  rfl

/-- `memory_sampled_coins` from `sampled_io_coins`: the pin is discharged by the package for any
trace once the tuple's IO coins are the package's. -/
theorem memory_sampled_coins_of_io_coins
    (Qm : Fin P.memoryChip.rap.w → F[X]) (c : K × K)
    (hc : c = (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole)) :
    ∀ i, (P.memorySourceEnv Qm i).chal 4 = c.1 ∧ (P.memorySourceEnv Qm i).chal 5 = c.2 := by
  subst hc
  exact P.memorySourceEnv_sampled_coins Qm

/-- `memory_intermediate_pole` from the tuple coordinate: the pin is discharged by the package
for any trace once the tuple's `interPole` is the package slot. -/
theorem memory_intermediate_pole_of_tuple
    (Qm : Fin P.memoryChip.rap.w → F[X]) (z : K)
    (hz : z = P.packageInterPole) :
    ∀ i, (P.memorySourceEnv Qm i).chal 6 = z := by
  subst hz
  intro i
  exact P.memorySourceEnv_inter_pole Qm i

/-! ### The records a candidate trace pair commits to

The prover commits `Com(IO_prog)` and only then receives the IO coins; the memory table's records
are obtained from the computation table.  Here the two committed traces are that commitment: the
compute chip's request list is the decoded record of every active slot of every row and the memory
chip's response list is the record of every `ver = 1` row.  These are
`OptimizedComputeHostileAccumulator.hostileRequests` / `OptimizedMemoryHostileAccumulator.hostileResponses`,
restated here (definitionally the same lists, `OptimizedHostileIOAssembly.hostileRecords_eq_package`)
so that the consumed failure event can name them. -/

/-- The request list the compute trace `Qc` commits to: every row's active-slot records, in row
order. -/
def hostileRequests
    (Qc : Fin P.computeChip.rap.w → F[X]) : List (Fin 10 → K) :=
  (List.ofFn fun i : Fin P.optimized.family.problem.cfg.compRows =>
    OptimizedComputeHostileAccumulator.rowRequests
      (gatherCorrectedFinalTypedEnv P.optimized.basis (P.computeBaseEnv Qc i))).flatten

/-- The response list the memory trace `Qm` commits to: every `ver = 1` row's record, in row order. -/
def hostileResponses
    (Qm : Fin P.memoryChip.rap.w → F[X]) : List (Fin 10 → K) :=
  (List.ofFn fun i : Fin P.optimized.family.problem.cfg.memRows =>
    OptimizedMemoryHostileAccumulator.rowResponses (P.memorySourceEnv Qm i)
      (P.memoryBaseEnv Qm i)).flatten

/-- The records both chips commit to, as the IO soundness layer's `PreChallengeRecords`. -/
def hostileRecords
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) : FiniteIO.PreChallengeRecords K 10 :=
  ⟨P.hostileRequests Qc, P.hostileResponses Qm⟩

/-- Intermediate `read_root` records the memory trace commits (base selector 2).  At most one
per row, so length `≤ M`.  Mirrors `MemoryInternalPole.hostileReads` without importing that
module (it sits downstream of this one). -/
def hostileInterReads
    [DecidableEq F]
    (Qm : Fin P.memoryChip.rap.w → F[X]) : List (Fin 10 → K) :=
  (List.ofFn fun i : Fin P.optimized.family.problem.cfg.memRows =>
    if (P.memoryBaseEnv Qm i).trace 2 = 1 then
      [OptimizedMemoryHostileAccumulator.rowRecord (P.memorySourceEnv Qm i)
        (P.memoryBaseEnv Qm i)]
    else []).flatten

/-- Intermediate `verify_child` records the memory trace commits (base selector 3). -/
def hostileInterVerifies
    [DecidableEq F]
    (Qm : Fin P.memoryChip.rap.w → F[X]) : List (Fin 10 → K) :=
  (List.ofFn fun i : Fin P.optimized.family.problem.cfg.memRows =>
    if (P.memoryBaseEnv Qm i).trace 3 = 1 then
      [OptimizedMemoryHostileAccumulator.rowRecord (P.memorySourceEnv Qm i)
        (P.memoryBaseEnv Qm i)]
    else []).flatten

def hostileInterRecords
    [DecidableEq F]
    (Qm : Fin P.memoryChip.rap.w → F[X]) : FiniteIO.PreChallengeRecords K 10 :=
  ⟨P.hostileInterReads Qm, P.hostileInterVerifies Qm⟩

theorem hostileInterReads_length_le
    [DecidableEq F]
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (P.hostileInterReads Qm).length ≤ P.optimized.family.problem.cfg.memRows := by
  unfold hostileInterReads
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  calc (∑ i : Fin P.optimized.family.problem.cfg.memRows,
          (if (P.memoryBaseEnv Qm i).trace 2 = 1 then
            [OptimizedMemoryHostileAccumulator.rowRecord (P.memorySourceEnv Qm i)
        (P.memoryBaseEnv Qm i)]
          else []).length)
        ≤ ∑ _i : Fin P.optimized.family.problem.cfg.memRows, 1 :=
          Finset.sum_le_sum fun i _ => by split_ifs <;> simp
      _ = P.optimized.family.problem.cfg.memRows := by simp

theorem hostileInterVerifies_length_le
    [DecidableEq F]
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (P.hostileInterVerifies Qm).length ≤ P.optimized.family.problem.cfg.memRows := by
  unfold hostileInterVerifies
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  calc (∑ i : Fin P.optimized.family.problem.cfg.memRows,
          (if (P.memoryBaseEnv Qm i).trace 3 = 1 then
            [OptimizedMemoryHostileAccumulator.rowRecord (P.memorySourceEnv Qm i)
        (P.memoryBaseEnv Qm i)]
          else []).length)
        ≤ ∑ _i : Fin P.optimized.family.problem.cfg.memRows, 1 :=
          Finset.sum_le_sum fun i _ => by split_ifs <;> simp
      _ = P.optimized.family.problem.cfg.memRows := by simp

/-- **`|hostileRequests| ≤ 3 · compRows`** for every trace: a row emits at most three records. -/
theorem hostileRequests_length_le
    (Qc : Fin P.computeChip.rap.w → F[X]) :
    (P.hostileRequests Qc).length ≤ 3 * P.optimized.family.problem.cfg.compRows := by
  unfold hostileRequests
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  calc (∑ i : Fin P.optimized.family.problem.cfg.compRows,
          (OptimizedComputeHostileAccumulator.rowRequests
            (gatherCorrectedFinalTypedEnv P.optimized.basis (P.computeBaseEnv Qc i))).length)
        ≤ ∑ _i : Fin P.optimized.family.problem.cfg.compRows, 3 :=
          Finset.sum_le_sum fun i _ =>
            OptimizedComputeHostileAccumulator.rowRequests_length_le _
      _ = 3 * P.optimized.family.problem.cfg.compRows := by simp [mul_comm]

/-- **`|hostileResponses| ≤ memRows`** for every trace: a row serves at most one record. -/
theorem hostileResponses_length_le
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (P.hostileResponses Qm).length ≤ P.optimized.family.problem.cfg.memRows := by
  unfold hostileResponses
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  calc (∑ i : Fin P.optimized.family.problem.cfg.memRows,
          (OptimizedMemoryHostileAccumulator.rowResponses (P.memorySourceEnv Qm i)
            (P.memoryBaseEnv Qm i)).length)
        ≤ ∑ _i : Fin P.optimized.family.problem.cfg.memRows, 1 :=
          Finset.sum_le_sum fun i _ =>
            OptimizedMemoryHostileAccumulator.rowResponses_length_le _ _
      _ = P.optimized.family.problem.cfg.memRows := by simp

/-- The table is the `c`-free `computeSourceEnv` (trace columns only —
`ComputeWalkRootEvents.rowLabelVec_congr`); `v` is the decoded row-0 label. -/
def computeWalkRootEvent
    [Fintype F]
    (Qc : Fin P.computeChip.rap.w → F[X]) : Finset (JointCoins K) :=
  ComputeWalkRootEvents.rootEvent (P.computeSourceEnv Qc)
    (fun z => ComputeWalkSeed.claimLabelVec z P.optimized.verifier.raw.claim)
    (ComputeWalkRootEvents.rowLabelVec
      (P.computeSourceEnv Qc ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩))

/-- `|walkRoot| ≤ (N + 9) · |𝕂|³` at `N = compRows` (paper's `h` plus γ-collision). -/
theorem computeWalkRootEvent_card_le
    [Fintype F]
    (Qc : Fin P.computeChip.rap.w → F[X]) :
    (P.computeWalkRootEvent Qc).card ≤
      ComputeWalkRootEvents.walkRootBound P.optimized.family.problem.cfg.compRows *
        Fintype.card K ^ 3 :=
  ComputeWalkRootEvents.card_rootEvent_le _ _ _

/-- Compute tiling event of the committed table (`foOf` of `computeSourceEnv`). -/
def computeTilingEventOf
    [Fintype F]
    (Qc : Fin P.computeChip.rap.w → F[X]) : Finset (JointCoins K) :=
  WalkTilingEvents.computeTilingEvent
    (ComputeWalkRootEvents.foOf (P.computeSourceEnv Qc))
    P.optimized.family.problem.cfg.compRows

theorem computeTilingEventOf_card_le
    [Fintype F]
    (Qc : Fin P.computeChip.rap.w → F[X]) :
    (P.computeTilingEventOf Qc).card ≤
      WalkTilingEvents.computeTilingBound P.optimized.family.problem.cfg.compRows *
        Fintype.card K ^ 3 :=
  WalkTilingEvents.card_computeTilingEvent_le _
    (ComputeWalkRootEvents.foOf_le_three (P.computeSourceEnv Qc)) _

/-- Memory tiling event of the committed table (`foOfMem` of `memoryBaseEnv`). -/
def memoryTilingEventOf
    [Fintype F] [DecidableEq F]
    (Qm : Fin P.memoryChip.rap.w → F[X]) : Finset (JointCoins K) :=
  WalkTilingEvents.memoryTilingEvent
    (WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm))
    P.optimized.family.problem.cfg.kMem
    P.optimized.family.problem.cfg.memRows

theorem memoryTilingEventOf_card_le
    [Fintype F] [DecidableEq F]
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (P.memoryTilingEventOf Qm).card ≤
      WalkTilingEvents.memoryTilingBound P.optimized.family.problem.cfg.memRows *
        Fintype.card K ^ 3 := by
  refine WalkTilingEvents.card_memoryTilingEvent_le _
    (WalkTilingEvents.foOfMem_le_two (P.memoryBaseEnv Qm)) _ _ ?_
  have hlen : P.objects.exec.memoryForest.length ≤
      Nock.Walk.totalSize P.objects.exec.memoryForest := by
    have h := Nock.Walk.totalSize_flatMap_children P.objects.exec.memoryForest
    omega
  have hkObj : P.objects.cfg.kMem ≤ P.objects.cfg.memRows := by
    rw [← P.objects.exec.memory_root_count, ← P.objects.exec.memory_bfs_length,
      Nock.Walk.bfsForest_length]
    exact hlen
  have hk := congrArg ExactConfig.kMem P.optimized.family_cfg
  have hm := congrArg ExactConfig.memRows P.optimized.family_cfg
  rw [hk, hm]
  exact hkObj

/-- Compute whole-table prefix γ-event of the committed table (`rowLabelVec` of
`computeSourceEnv`). -/
def computePrefixGammaEventOf
    [Fintype F]
    (Qc : Fin P.computeChip.rap.w → F[X]) : Finset (JointCoins K) :=
  WalkPrefixGammaEvents.computePrefixGammaEventOf (P.computeSourceEnv Qc)

theorem computePrefixGammaEventOf_card_le
    [Fintype F]
    (Qc : Fin P.computeChip.rap.w → F[X]) :
    (P.computePrefixGammaEventOf Qc).card ≤
      WalkPrefixGammaEvents.computePrefixGammaBound
        P.optimized.family.problem.cfg.compRows * Fintype.card K ^ 3 :=
  WalkPrefixGammaEvents.card_computePrefixGammaEventOf_le _

/-- Memory whole-table prefix γ-event of the committed table (`memRowLabelVec` of
`memorySourceEnv` / `memoryBaseEnv`). -/
def memoryPrefixGammaEventOf
    [Fintype F] [DecidableEq F]
    (Qm : Fin P.memoryChip.rap.w → F[X]) : Finset (JointCoins K) :=
  WalkPrefixGammaEvents.memoryPrefixGammaEventOfEnvs
    (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm)
    P.optimized.family.problem.cfg.kMem

theorem memoryPrefixGammaEventOf_card_le
    [Fintype F] [DecidableEq F]
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (P.memoryPrefixGammaEventOf Qm).card ≤
      WalkPrefixGammaEvents.memoryPrefixGammaBound
        P.optimized.family.problem.cfg.memRows * Fintype.card K ^ 3 :=
  WalkPrefixGammaEvents.card_memoryPrefixGammaEventOfEnvs_le _ _ _

/-- Memory forest α-event of the committed table (`Corr:forest`), consumed
under tiling. -/
def memoryForestAlphaEventOf
    [Fintype F] [DecidableEq F]
    (Qm : Fin P.memoryChip.rap.w → F[X]) : Finset (JointCoins K) :=
  WalkForestPrefixAlphaEvents.memoryForestAlphaEventOfEnvs
    (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm)
    P.optimized.family.problem.cfg.kMem

theorem memoryForestAlphaEventOf_card_le
    [Fintype F] [DecidableEq F]
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (P.memoryForestAlphaEventOf Qm).card ≤
      WalkForestPrefixAlphaEvents.memoryForestAlphaBound
        P.optimized.family.problem.cfg.memRows * Fintype.card K ^ 3 :=
  WalkForestPrefixAlphaEvents.card_memoryForestAlphaEventOfEnvs_le _ _ _

def decodedLambdaEventOf
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) : Finset (OptimizedProductionChallengeTuple K F) :=
  DecodedLambdaEvent.decodedLambdaEventOfEnvs
    (P.computeSourceEnv Qc) (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm)
    P.optimized.family.problem.cfg.kMem

theorem decodedLambdaEventOf_card_le
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (P.decodedLambdaEventOf Qc Qm).card ≤
      Fintype.card K ^ 10 * ProductionP8Containment.formRUniformWorkload P.strategy := by
  have hcfg : P.optimized.family.problem.cfg =
      P.strategy.specializedCfg P.honestSeed P.honestSeed_ne P.honestAlpha
        P.optimized.objects.cfg.challenges.lam := by
    rw [P.optimized.family_cfg]
    exact (congrArg (fun x => x.cfg) P.honest_specialization).symm
  have hN : P.optimized.family.problem.cfg.compRows =
      (SemanticStrategy.computeSkeletonRows P.strategy.skeleton).length := by
    rw [hcfg]
    have h := (P.optimized.strategy_bindsAll P.honestSeed P.honestSeed_ne P.honestAlpha
      P.optimized.objects.cfg.challenges.lam).computeRows.length_eq
    rw [ExactExecution.computeRows_length] at h
    exact h.symm
  have hM : P.optimized.family.problem.cfg.memRows =
      (SemanticStrategy.memorySkeletonRows P.strategy.skeleton).length := by
    rw [hcfg]
    have h := (P.optimized.strategy_bindsAll P.honestSeed P.honestSeed_ne P.honestAlpha
      P.optimized.objects.cfg.challenges.lam).memoryRows.length_eq
    rw [ExactExecution.memoryRows_length] at h
    exact h.symm
  have hW : ProductionP8Containment.formRUniformWorkload P.strategy =
      DecodedLambdaEvent.formRUniformWorkloadOf (FormRAxisEvent.formRN K)
        (SemanticStrategy.computeSkeletonRows P.strategy.skeleton).length
        (SemanticStrategy.memorySkeletonRows P.strategy.skeleton).length := by
    unfold ProductionP8Containment.formRUniformWorkload DecodedLambdaEvent.formRUniformWorkloadOf
    ring
  rw [hW, ← hN, ← hM]
  exact DecodedLambdaEvent.decodedLambdaEventOfEnvs_card_le _ _ _ _

def reqPairEventOf
    [Fintype F] [DecidableEq F]
    (Qm : Fin P.memoryChip.rap.w → F[X]) : Finset (OptimizedProductionChallengeTuple K F) :=
  liftP8Failure (F := F) (PreSeedCensus.reqPairEventOfEnvs K P.q
    P.optimized.family.problem.cfg.kMem
    (P.optimized.family.problem.cfg.memRows ⊔ P.optimized.Λ) (P.memoryBaseEnv Qm)
    P.optimized.family.problem.cfg.memRows_pos (PreSeedCensus.requestTargets P.strategy.skeleton))

theorem reqPairEventOf_card_le
    [Fintype F] [DecidableEq F]
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (P.reqPairEventOf Qm).card ≤
      Fintype.card K ^ 10 * ProductionP8Containment.reqPairWorkload P.strategy P.optimized.Λ := by
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
  have hB := PreSeedCensus.reqPairEventOfEnvs_card_le K P.q P.optimized.family.problem.cfg.kMem
    (P.optimized.family.problem.cfg.memRows ⊔ P.optimized.Λ) (P.memoryBaseEnv Qm)
    P.optimized.family.problem.cfg.memRows_pos (PreSeedCensus.requestTargets P.strategy.skeleton)
  unfold reqPairEventOf liftP8Failure
  rw [Finset.card_product, Finset.card_univ]
  have hrest :
      Fintype.card ((K × K) × FinalComputeChallengeTuple K × MemoryChallengeTuple K) =
        Fintype.card K ^ 7 := by
    simp only [Fintype.card_prod, card_finalComputeChallengeTuple, card_memoryChallengeTuple]
    ring
  rw [hrest]
  have hW : ProductionP8Containment.reqPairWorkload P.strategy P.optimized.Λ =
      P.optimized.family.problem.cfg.memRows *
        (2 * (P.optimized.family.problem.cfg.memRows ⊔ P.optimized.Λ) - 1) := by
    unfold ProductionP8Containment.reqPairWorkload
    rw [← hM]
  rw [hW]
  calc _ ≤ P.optimized.family.problem.cfg.memRows *
        (2 * (P.optimized.family.problem.cfg.memRows ⊔ P.optimized.Λ) - 1) *
        Fintype.card K ^ 3 * Fintype.card K ^ 7 := Nat.mul_le_mul_right _ hB
    _ = _ := by ring

/-- The capstone's consumed event is
`consumedFailureEvent` in the statement half (the 2b-ii event `optimizedFailureEventEv`, inlined);
this definition stays for its P8Core consumers (`good_components`, the `_ev` bridges) and is no
longer read by the statement. -/
def optimizedFailureEvent
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  OptimizedHostileProductionFailureEvent P.strategy P.optimized.census
    P.objects.cfg.challenges.lam (P.famIOEventOf Qc Qm) (P.hostileRequests Qc).length
    (P.computeSourceEnv Qc) (P.computeWalkEnv Qc) (P.computeScalarEnv Qc)
    (P.memorySourceEnv Qm) (P.memoryScalarFamilies Qm)
    (P.hostileInterRecords Qm) (P.memoryBaseEnv Qm)
    (P.computeWalkRootEvent Qc)
    (P.computeTilingEventOf Qc)
    (P.memoryTilingEventOf Qm)
    (P.computePrefixGammaEventOf Qc)
    (P.memoryPrefixGammaEventOf Qm)
    (P.memoryForestAlphaEventOf Qm)
    (P.decodedLambdaEventOf Qc Qm)
    (PreSeedCensus.reqPairEventOfEnvs K P.q P.optimized.family.problem.cfg.kMem
      (P.optimized.family.problem.cfg.memRows ⊔ P.optimized.Λ) (P.memoryBaseEnv Qm)
      P.optimized.family.problem.cfg.memRows_pos (PreSeedCensus.requestTargets P.strategy.skeleton))

theorem optimizedFailureEvent_good_components
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm) :
    c.1 ∉ ProductionP8Containment.FailureUnion P.strategy P.optimized.census
        P.objects.cfg.challenges.lam ∧
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
      c.1 ∉ PreSeedCensus.reqPairEventOfEnvs K P.q P.optimized.family.problem.cfg.kMem
        (P.optimized.family.problem.cfg.memRows ⊔ P.optimized.Λ) (P.memoryBaseEnv Qm)
        P.optimized.family.problem.cfg.memRows_pos
        (PreSeedCensus.requestTargets P.strategy.skeleton) := by
  simp only [optimizedFailureEvent, OptimizedHostileProductionFailureEvent,
    OptimizedProductionFailureEvent, Finset.mem_union, not_or] at hgood
  rcases hgood with
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hp8, hio⟩, hts⟩, hinter⟩, hwalk⟩, htileC⟩, htileM⟩, hγC⟩, hγM⟩, hαM⟩, hlamEv⟩,
      hpair⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlamEv, ?_⟩
  · intro h
    apply hp8
    exact Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩
  · exact hio
  · intro h
    exact hts ((mem_liftTimestampFailure_iff _ _).2 h)
  · intro h
    exact hinter ((mem_liftInterPoleFailure_iff _ _).2 h)
  · intro h
    apply hwalk
    exact Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩
  · intro h
    apply htileC
    exact Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩
  · intro h
    apply htileM
    exact Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩
  · intro h
    apply hγC
    exact Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩
  · intro h
    apply hγM
    exact Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩
  · intro h
    apply hαM
    exact Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩
  · intro h
    apply hpair
    exact Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩

/-- Membership in the consumed event, component-wise (the converse of
`optimizedFailureEvent_good_components`). -/
theorem notMem_optimizedFailureEvent_of_components
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hp8 : c.1 ∉ ProductionP8Containment.FailureUnion P.strategy P.optimized.census
      P.objects.cfg.challenges.lam)
    (hio : c ∉ P.famIOEventOf Qc Qm)
    (hts : alphaM c.1 ∉
      OptimizedHostileTimestamps.TimestampCollisionEvent (P.hostileRequests Qc).length)
    (hinter : (c.2.1.1, c.2.2.2.interPole) ∉
      interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm))
    (hwalk : c.1 ∉ P.computeWalkRootEvent Qc)
    (htileC : c.1 ∉ P.computeTilingEventOf Qc)
    (htileM : c.1 ∉ P.memoryTilingEventOf Qm)
    (hγC : c.1 ∉ P.computePrefixGammaEventOf Qc)
    (hγM : c.1 ∉ P.memoryPrefixGammaEventOf Qm)
    (hαM : c.1 ∉ P.memoryForestAlphaEventOf Qm)
    (hlamEv : c ∉ P.decodedLambdaEventOf Qc Qm)
    (hpair : c.1 ∉ PreSeedCensus.reqPairEventOfEnvs K P.q P.optimized.family.problem.cfg.kMem
      (P.optimized.family.problem.cfg.memRows ⊔ P.optimized.Λ) (P.memoryBaseEnv Qm)
      P.optimized.family.problem.cfg.memRows_pos
      (PreSeedCensus.requestTargets P.strategy.skeleton)) :
    c ∉ P.optimizedFailureEvent Qc Qm := by
  simp only [optimizedFailureEvent, OptimizedHostileProductionFailureEvent,
    OptimizedProductionFailureEvent, Finset.mem_union, not_or]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hlamEv⟩, ?_⟩
  · intro h
    exact hp8 (Finset.mem_product.mp h).1
  · exact hio
  · intro h
    exact hts ((mem_liftTimestampFailure_iff _ _).1 h)
  · intro h
    exact hinter ((mem_liftInterPoleFailure_iff _ _).1 h)
  · intro h
    exact hwalk (Finset.mem_product.mp h).1
  · intro h
    exact htileC (Finset.mem_product.mp h).1
  · intro h
    exact htileM (Finset.mem_product.mp h).1
  · intro h
    exact hγC (Finset.mem_product.mp h).1
  · intro h
    exact hγM (Finset.mem_product.mp h).1
  · intro h
    exact hαM (Finset.mem_product.mp h).1
  · intro h
    exact hpair (Finset.mem_product.mp h).1

/-- The IO union bound at the row-count majorants of the traces' records. -/
abbrev hostileIOWork [Fintype F] : ℕ :=
  FiniteIO.ioFailureUnionBound 10 (3 * P.optimized.family.problem.cfg.compRows)
    P.optimized.family.problem.cfg.memRows (Fintype.card K)

/-- The internal-pole union bound at the row-count majorants of the intermediate lists
(`MemoryInternalPole.interWork`, both lists length `≤ M`). -/
abbrev hostileInterWork [Fintype F] : ℕ :=
  FiniteIO.ioFailureUnionBound 10 P.optimized.family.problem.cfg.memRows
    P.optimized.family.problem.cfg.memRows (Fintype.card K) +
    Fintype.card K * P.optimized.family.problem.cfg.memRows

end OptimizedFullStrictNockVMROMPackage

end
end OptimizedStrictFullPackage
end Nock.NockVMROM.Thm54

end Nock.Walk37
