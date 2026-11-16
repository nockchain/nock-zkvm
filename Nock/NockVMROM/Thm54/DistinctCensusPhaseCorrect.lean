import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
import Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
import Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
import Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Phase-correct later-round message over the distinct-pair `OP_5` census

`DistinctCensusHonestArrays` constructed `(packageH hfirstD)` over the seed-`8` `OP_5` execution whose
consumed census contains `([7 9], [8 10])`. Its later-round walk columns ignore the coin, so
acceptance is the single specialized witness `(packageH hfirstD).Accepts coinH cfgD.challenges.lam` at
`(alphaC, gamma) = (0, 0)`.

This module uses the MultiRoot chronology split (`MultiRootPhaseCorrect`) on the **same**
`(dataD hfirstD)` skeleton.  `jointVerification_complete` bundles two choices the
paper makes at different rounds: public IO endpoints, a function of the committed derived lists
alone, and the six-family assignment, whose walk components depend on the sampled `α, γ`
.  Splitting them is all that is needed:

* `uniformEndpointsQ_exist` hoists the endpoint choice out of the walk challenges.
* `alphaMCommitmentQ` is the pre-challenge message: endpoints and table/IO arrays come from the
  single reference assignment `assignmentQ 0 0`, and it takes no `a`/`g` argument.
* `walkArraysQ ω` is the later-round message and a genuine function of the sampled coin.

The resulting `packageQ` is one closed definition.  Seed stays `8`.  The coin of this census is
`coinQ a g = ((a, g), (alphaD, seedD))`; it is **not** `coinN`, whose NPR seed is the released
fixture's `-1` (this census's unique collision seed).
-/

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect

open scoped Classical Polynomial
open Nock Nock.Noun Nock.Walk Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open SemanticStrategy SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.EqualityOperandCensus
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment
open Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
open Nock.NockVMROM.Thm54.MultiRootHonestArrays
open Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance

noncomputable section

local instance prime97q : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97q : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
include hfirstD

/-! ## A. The raw family at an arbitrary pair of sampled walk challenges -/

/-- The committed post-`alphaM` data of `DistinctCensusHonestArrays`, with the two later coins
inserted.  Only `computeWalkAlpha` and `walkGamma` move. -/
def rawFamilyQ (a g : K97cubic) : RawPlusIOSegmentedFamily F97 K97cubic :=
  (familyDataD0 hfirstD seedD seedH_ne alphaD cfgD.challenges.lam).atCoins a g

theorem rawFamilyQ_coins (a g : K97cubic) :
    (rawFamilyQ hfirstD a g).computeWalkAlpha = a ∧ (rawFamilyQ hfirstD a g).walkGamma = g ∧
      (rawFamilyQ hfirstD a g).memoryWalkAlpha = alphaD :=
  ⟨rfl, rfl, rfl⟩

theorem rawFamilyQ_problem (a g : K97cubic) : (rawFamilyQ hfirstD a g).problem = ⟨cfgD, execD⟩ :=
  specializedProblemD_honest hfirstD

theorem rawFamilyQ_tableAssumptions (a g : K97cubic) :
    (rawFamilyQ hfirstD a g).problem.TableCompletenessAssumptions := by
  rw [rawFamilyQ_problem]
  exact ⟨seedH_ne, (chainedD hfirstD).compute_wf, (chainedD hfirstD).memory_wf,
    (chainedD hfirstD).memory_same_lambda⟩

theorem rawFamilyQ_progCapacity (a g : K97cubic) :
    (rawFamilyQ hfirstD a g).exec.derivedRequestIO.length + 1 ≤ 2 ^ (rawFamilyQ hfirstD a g).cfg.orbit.h := by
  change
    (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.derivedRequestIO.length + 1 ≤
      2 ^ (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).cfg.orbit.h
  rw [specializedProblemD_honest hfirstD]
  change execD.derivedRequestIO.length + 1 ≤ 2 ^ cfgD.orbit.h
  rw [derived_requestsD]
  norm_num [cfgD, orbitD]

theorem rawFamilyQ_memCapacity (a g : K97cubic) :
    (rawFamilyQ hfirstD a g).exec.derivedResponseIO.length + 1 ≤ 2 ^ (rawFamilyQ hfirstD a g).cfg.orbit.h := by
  change
    (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.derivedResponseIO.length + 1 ≤
      2 ^ (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).cfg.orbit.h
  rw [specializedProblemD_honest hfirstD]
  change execD.derivedResponseIO.length + 1 ≤ 2 ^ cfgD.orbit.h
  rw [derived_responsesD]
  norm_num [cfgD, orbitD]

def legacyZeroFamilyQ (a g : K97cubic) : PlusIOSegmentedFamily F97 K97cubic :=
  (rawFamilyQ hfirstD a g).toLegacy (rawFamilyQ_tableAssumptions hfirstD a g)
    (fun _ _ h => NodeEncoding.computeNodeEncode_labelOf_eq stateTagChar97 h)
    (fun _ _ h => NodeEncoding.memoryNodeEncode_labelOf_eq stateTagChar97 h)
    (rawFamilyQ_progCapacity hfirstD a g) (rawFamilyQ_memCapacity hfirstD a g)

theorem legacyZeroFamilyQ_chained (a g : K97cubic) :
    ChainedSemanticExactLanguage (legacyZeroFamilyQ hfirstD a g).problem.cfg
      (legacyZeroFamilyQ hfirstD a g).problem.exec := by
  change ChainedSemanticExactLanguage
    (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).cfg
    (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec
  rw [specializedProblemD_honest hfirstD]
  exact (chainedD hfirstD)

def legacyZeroFamilyQ_semanticWitness (a g : K97cubic) :
    SemanticIOWitness (legacyZeroFamilyQ hfirstD a g).problem.cfg
      (legacyZeroFamilyQ hfirstD a g).problem.exec := by
  change SemanticIOWitness
    (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).cfg
    (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec
  rw [specializedProblemD_honest hfirstD]
  exact
    { timestampBound := semanticPreimageD.timestampBound
      timestampBound_le_order := semanticPreimageD.timestampBound_le_order
      semanticRequests := semanticPreimageD.semanticRequests
      semanticResponses := semanticPreimageD.semanticResponses
      requestTimestampBound := semanticPreimageD.requestTimestampBound
      responseTimestampBound := semanticPreimageD.responseTimestampBound
      semantic_lmio := semanticPreimageD.semantic_lmio
      requestTimestamp_determines := semanticPreimageD.requestTimestamp_determines
      requests_bridge := semanticPreimageD.requests_bridge
      responses_bridge := semanticPreimageD.responses_bridge
      semanticRequests_nodup := semRecs_nodup }

theorem legacyZeroFamilyQ_KszBound (a g : K97cubic) :
    (legacyZeroFamilyQ hfirstD a g).problem.cfg.Ksz < ringChar K97cubic := by
  change (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).cfg.Ksz < ringChar K97cubic
  rw [specializedProblemD_honest hfirstD, ringChar_K97]
  norm_num [cfgD]

/-! ## B. Public IO endpoints chosen before the walk coins -/

/-- **One endpoint triple for every sampled walk-challenge pair**. -/
theorem uniformEndpointsQ_exist :
    ∃ requests responses outMem : IOField K97cubic,
      ∀ a g : K97cubic,
        Nonempty (JointAssignment
          ((legacyZeroFamilyQ hfirstD a g).withIOEndpoints requests responses outMem)
          (ringChar K97cubic)) := by
  have hLIO :
      IO.LIO (legacyZeroFamilyD hfirstD).problem.cfg.Ksz
        (legacyZeroFamilyD hfirstD).problem.exec.derivedRequestIO
        (legacyZeroFamilyD hfirstD).problem.exec.derivedResponseIO :=
    ((legacyZeroFamilyD_semanticWitness hfirstD).strongExactLanguage_of_semanticExactLanguage
      (legacyZeroFamilyD_chained hfirstD).semantic).2.2
  obtain ⟨requests, responses, outMem, ⟨io⟩⟩ :=
    ExactDerivedIOAssignment.exists_with_public_endpoints_of_semanticIOWitness
      (p := ringChar K97cubic) (legacyZeroFamilyD hfirstD) (legacyZeroFamilyD_KszBound hfirstD)
      (legacyZeroFamilyD_semanticWitness hfirstD) (legacyZeroFamilyD_chained hfirstD).semantic
  refine ⟨requests, responses, outMem, fun a g => ?_⟩
  have io' :
      ExactDerivedIOAssignment
        ((legacyZeroFamilyQ hfirstD a g).withIOEndpoints requests responses outMem)
        (ringChar K97cubic) :=
    ioAtWalkChallenges io a g alphaD
  obtain ⟨A, hA⟩ :=
    PlusIOSameExecutionAssignment.exists_satisfies_of_chained_IO
      (R := (legacyZeroFamilyQ hfirstD a g).withIOEndpoints requests responses outMem)
      (p := ringChar K97cubic)
      (legacyZeroFamilyQ_chained hfirstD a g) io'
  exact
    ⟨{ sameExecution := A
       sixFamilies := hA
       sharedIO :=
         (sharedIOSat_iff_LIO
           ((legacyZeroFamilyQ hfirstD a g).withIOEndpoints requests responses outMem)
           (legacyZeroFamilyQ_KszBound hfirstD a g)).2 hLIO }⟩

structure PhaseCompletionQ where
  requests : IOField K97cubic
  responses : IOField K97cubic
  outMem : IOField K97cubic
  assignment : ∀ a g : K97cubic,
    JointAssignment ((legacyZeroFamilyQ hfirstD a g).withIOEndpoints requests responses outMem)
      (ringChar K97cubic)

theorem phaseCompletionQ_nonempty : Nonempty (PhaseCompletionQ hfirstD) := by
  obtain ⟨requests, responses, outMem, h⟩ := uniformEndpointsQ_exist hfirstD
  exact ⟨⟨requests, responses, outMem, fun a g => Classical.choice (h a g)⟩⟩

noncomputable def completionQ : PhaseCompletionQ hfirstD :=
  Classical.choice (phaseCompletionQ_nonempty hfirstD)

abbrev legacyFamilyQ (a g : K97cubic) : PlusIOSegmentedFamily F97 K97cubic :=
  (legacyZeroFamilyQ hfirstD a g).withIOEndpoints (completionQ hfirstD).requests (completionQ hfirstD).responses
    (completionQ hfirstD).outMem

abbrev assignmentQ (a g : K97cubic) :
    PlusIOSameExecutionAssignment (legacyFamilyQ hfirstD a g) (ringChar K97cubic) :=
  ((completionQ hfirstD).assignment a g).sameExecution

theorem legacyFamilyQ_endpoints (a g a' g' : K97cubic) :
    (legacyFamilyQ hfirstD a g).requests = (legacyFamilyQ hfirstD a' g').requests ∧
      (legacyFamilyQ hfirstD a g).responses = (legacyFamilyQ hfirstD a' g').responses ∧
      (legacyFamilyQ hfirstD a g).outMem = (legacyFamilyQ hfirstD a' g').outMem ∧
      (legacyFamilyQ hfirstD a g).problem = (legacyFamilyQ hfirstD a' g').problem ∧
      (legacyFamilyQ hfirstD a g).computeWalkAlpha = a ∧
      (legacyFamilyQ hfirstD a g).walkGamma = g :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## C. The pre-challenge message -/

def acceptedFamilyDataQ (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    AlphaMFamilyData (timestampD hfirstD) z hz α lmb where
  compNodeWidth := NodeEncoding.computeNodeWidth
  compNodeEncode := NodeEncoding.computeNodeEncode stateTagChar97
  memNodeWidth := NodeEncoding.memoryNodeWidth
  memNodeEncode := NodeEncoding.memoryNodeEncode stateTagChar97
  requests := (completionQ hfirstD).requests
  responses := (completionQ hfirstD).responses
  outMem := (completionQ hfirstD).outMem

theorem acceptedFamilyQ_response_length (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    (acceptedFamilyDataQ hfirstD z hz α lmb).base.exec.derivedResponseIO.length = 4 :=
  responseLenD hfirstD z hz α lmb

theorem legacyFamilyQ_response_length (a g : K97cubic) :
    (legacyFamilyQ hfirstD a g).problem.exec.derivedResponseIO.length = 4 :=
  responseLenD hfirstD seedD seedH_ne alphaD cfgD.challenges.lam

/-- **The committed later-round-`alphaM` message.**  No `alphaC`, no `gamma`, and no `(a, g)`
parameter. -/
def alphaMCommitmentQ (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    AlphaMCommitment (p := ringChar K97cubic) (timestampD hfirstD) z hz α lmb where
  familyData := acceptedFamilyDataQ hfirstD z hz α lmb
  tables :=
    { compute := (assignmentQ hfirstD 0 0).computeTableAux
      memory := (assignmentQ hfirstD 0 0).memoryTableAux }
  io :=
    { multiplicity := fun j =>
        (assignmentQ hfirstD 0 0).exactIO.multiplicity
          ⟨j, by
            have hj := j.isLt
            have hsource := acceptedFamilyQ_response_length hfirstD z hz α lmb
            have htarget := legacyFamilyQ_response_length hfirstD 0 0
            omega⟩
      progAcc := (assignmentQ hfirstD 0 0).exactIO.progAcc
      memAcc := (assignmentQ hfirstD 0 0).exactIO.memAcc }

/-! ## D. The post-challenge message, a genuine function of the sampled coin -/

/-- The honest coin of this census at sampled walk challenges `(a, g)`.  Seed stays `8`.
This is not `coinN`: that constructor uses the released fixture seed `-1`. -/
def coinQ (a g : K97cubic) : JointCoins K97cubic := ((a, g), (alphaD, seedD))

theorem coinQ_coordinates (a g : K97cubic) :
    alphaC (coinQ a g) = a ∧ gamma (coinQ a g) = g ∧
      alphaM (coinQ a g) = alphaD ∧ nprSeed (coinQ a g) = seedD :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem coinQ_seed_ne (a g : K97cubic) : nprSeed (coinQ a g) ≠ 0 := seedH_ne

theorem coinH_eq_coinQ_zero : coinH = coinQ 0 0 := rfl

/-- **The later-round walk columns**.  Unlike `(walkArraysD hfirstD)`, this reads its
`ω` argument. -/
def walkArraysQ (ω : JointCoins K97cubic) (_lmb : K97cubic) (_hz : nprSeed ω ≠ 0) : RawWalkArrays K97cubic where
  computeLn := (assignmentQ hfirstD (alphaC ω) (gamma ω)).computeWalk.ln
  computeCount := (assignmentQ hfirstD (alphaC ω) (gamma ω)).computeWalk.count
  computeAcc := (assignmentQ hfirstD (alphaC ω) (gamma ω)).computeWalk.acc
  memoryLn := (assignmentQ hfirstD (alphaC ω) (gamma ω)).memoryWalk.ln
  memoryCount := (assignmentQ hfirstD (alphaC ω) (gamma ω)).memoryWalk.count
  memoryAcc := (assignmentQ hfirstD (alphaC ω) (gamma ω)).memoryWalk.acc

theorem walkArraysQ_reads_the_coin (ω : JointCoins K97cubic) (lmb : K97cubic) (hz : nprSeed ω ≠ 0) :
    (walkArraysQ hfirstD ω lmb hz).computeLn = (assignmentQ hfirstD (alphaC ω) (gamma ω)).computeWalk.ln ∧
      (walkArraysQ hfirstD ω lmb hz).computeCount = (assignmentQ hfirstD (alphaC ω) (gamma ω)).computeWalk.count ∧
      (walkArraysQ hfirstD ω lmb hz).computeAcc = (assignmentQ hfirstD (alphaC ω) (gamma ω)).computeWalk.acc ∧
      (walkArraysQ hfirstD ω lmb hz).memoryLn = (assignmentQ hfirstD (alphaC ω) (gamma ω)).memoryWalk.ln ∧
      (walkArraysQ hfirstD ω lmb hz).memoryCount = (assignmentQ hfirstD (alphaC ω) (gamma ω)).memoryWalk.count ∧
      (walkArraysQ hfirstD ω lmb hz).memoryAcc = (assignmentQ hfirstD (alphaC ω) (gamma ω)).memoryWalk.acc :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def mixedAssignmentQ (a g : K97cubic) :
    PlusIOSameExecutionAssignment (legacyFamilyQ hfirstD a g) (ringChar K97cubic) where
  computeTableAux := (assignmentQ hfirstD 0 0).computeTableAux
  memoryTableAux := (assignmentQ hfirstD 0 0).memoryTableAux
  computeWalk := (assignmentQ hfirstD a g).computeWalk
  memoryWalk := (assignmentQ hfirstD a g).memoryWalk
  exactIO := ioAtWalkChallenges (assignmentQ hfirstD 0 0).exactIO a g alphaD

theorem mixedAssignmentQ_satisfies (a g : K97cubic) : (mixedAssignmentQ hfirstD a g).Satisfies := by
  have h0 := ((completionQ hfirstD).assignment 0 0).sixFamilies
  have hag := ((completionQ hfirstD).assignment a g).sixFamilies
  exact ⟨h0.1, h0.2.1, hag.2.2.1, hag.2.2.2.1, h0.2.2.2.2.1, h0.2.2.2.2.2⟩

/-! ## E. The phase-correct raw strategy -/

def rawStrategyQ : TemplateRawJointSoundness.Strategy F97 K97cubic (ringChar K97cubic) where
  timestamp := (timestampD hfirstD)
  afterAlphaM := alphaMCommitmentQ hfirstD
  afterCoins := walkArraysQ hfirstD

theorem rawStrategyQ_familyAt (a g : K97cubic) :
    (rawStrategyQ hfirstD).familyAt (coinQ a g) cfgD.challenges.lam seedH_ne =
      RawPlusIOSegmentedFamily.ofLegacy (legacyFamilyQ hfirstD a g) := rfl

theorem rawStrategyQ_messageAt (a g : K97cubic) :
    (rawStrategyQ hfirstD).messageAt (coinQ a g) cfgD.challenges.lam seedH_ne =
      RawMessage.ofLegacy (mixedAssignmentQ hfirstD a g) := rfl

theorem alphaMCommitmentQ_same_across_coins (a g a' g' : K97cubic) :
    (rawStrategyQ hfirstD).alphaMCommitment (coinQ a g) cfgD.challenges.lam seedH_ne =
      (rawStrategyQ hfirstD).alphaMCommitment (coinQ a' g') cfgD.challenges.lam seedH_ne := rfl

abbrev rawLegacyQ (a g : K97cubic) : RawPlusIOSegmentedFamily F97 K97cubic :=
  RawPlusIOSegmentedFamily.ofLegacy (legacyFamilyQ hfirstD a g)

theorem rawLegacyQ_computeRowsAccepted (a g : K97cubic) :
    (rawLegacyQ hfirstD a g).exec.ComputeRowsAccepted := by
  change (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.ComputeRowsAccepted
  rw [specializedProblemD_honest hfirstD]
  exact compute_rows_acceptedD

theorem rawLegacyQ_memoryRowsAccepted (a g : K97cubic) :
    (rawLegacyQ hfirstD a g).exec.MemoryRowsAccepted := by
  change (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.MemoryRowsAccepted
  rw [specializedProblemD_honest hfirstD]
  exact memory_rows_acceptedD

theorem rawLegacyQ_computePubAt_zero (a g : K97cubic) :
    (rawLegacyQ hfirstD a g).exec.computePubAt ⟨0, (rawLegacyQ hfirstD a g).cfg.compRows_pos⟩ = op5PubD := by
  change
    (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.computePubAt
        ⟨0, (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).cfg.compRows_pos⟩ =
      op5PubD
  rw [specializedProblemD_honest hfirstD]
  exact computePubAtD_zero

theorem rawLegacyQ_Ksz (a g : K97cubic) : (rawLegacyQ hfirstD a g).cfg.Ksz = 4 := by
  change (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).cfg.Ksz = 4
  rw [specializedProblemD_honest hfirstD]
  rfl

theorem rawLegacyQ_requests (a g : K97cubic) :
    (rawLegacyQ hfirstD a g).exec.derivedRequestIO =
      [NockVM.encRecFormR recF MemoryTable.formRDefault,
          NockVM.encRecFormR recT MemoryTable.formRDefault,
              NockVM.encRecFormR recL MemoryTable.formRDefault,
                  NockVM.encRecFormR recR MemoryTable.formRDefault] := by
  change
    (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.derivedRequestIO = _
  rw [specializedProblemD_honest hfirstD]
  exact derived_requestsD

theorem rawLegacyQ_responses (a g : K97cubic) :
    (rawLegacyQ hfirstD a g).exec.derivedResponseIO =
      [NockVM.encRecFormR recF MemoryTable.formRDefault,
          NockVM.encRecFormR recT MemoryTable.formRDefault,
              NockVM.encRecFormR recL MemoryTable.formRDefault,
                  NockVM.encRecFormR recR MemoryTable.formRDefault] := by
  change
    (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.derivedResponseIO = _
  rw [specializedProblemD_honest hfirstD]
  exact derived_responsesD

theorem honestVerifierGatesQ (a g : K97cubic) :
    (RawMessage.ofLegacy (mixedAssignmentQ hfirstD a g)).VerifierGates skelD.publicClaim (coinQ a g) := by
  refine ⟨seedH_ne, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact rowAlignment_of_rowsAcceptedM (rawLegacyQ hfirstD a g)
      (rawLegacyQ_computeRowsAccepted hfirstD a g) (rawLegacyQ_memoryRowsAccepted hfirstD a g)
  · refine ⟨rfl, ?_, rfl, ?_⟩
    · intro hchar
      have hh : hchar = stateTagChar97 := Subsingleton.elim _ _
      subst hchar
      rfl
    · intro hchar
      have hh : hchar = stateTagChar97 := Subsingleton.elim _ _
      subst hchar
      rfl
  · rw [rawLegacyQ_computePubAt_zero hfirstD a g, claimD hfirstD]
    rfl
  · rw [rawLegacyQ_computePubAt_zero hfirstD a g, claimD hfirstD]
    rfl
  · rw [rawLegacyQ_computePubAt_zero hfirstD a g, claimD hfirstD]
    rfl
  · exact ((completionQ hfirstD).assignment 0 0).public_endpoints.1
  · exact ((completionQ hfirstD).assignment 0 0).public_endpoints.2
  · exact (assignmentQ hfirstD 0 0).exactIO.multiplicity_ne_zero
  · rw [rawLegacyQ_requests hfirstD a g, rawLegacyQ_Ksz hfirstD a g]
    norm_num [IO.InRange]
  · rw [rawLegacyQ_requests hfirstD a g, ← derived_requestsD]
    exact requestsD_nodup
  · rw [rawLegacyQ_responses hfirstD a g, rawLegacyQ_Ksz hfirstD a g]
    norm_num
  · rw [rawLegacyQ_responses hfirstD a g, ← derived_responsesD]
    exact responsesD_nodup

theorem rawStrategyQ_accepts (a g : K97cubic) : (rawStrategyQ hfirstD).Accepts (coinQ a g) cfgD.challenges.lam := by
  apply ((rawStrategyQ hfirstD).accepts_iff_raw (coinQ a g) cfgD.challenges.lam seedH_ne).2
  change (RawMessage.ofLegacy (mixedAssignmentQ hfirstD a g)).Accepts skelD.publicClaim (coinQ a g)
  exact RawMessage.accepts_of_legacy_assignment
    skelD.publicClaim (coinQ a g) (mixedAssignmentQ hfirstD a g)
    (mixedAssignmentQ_satisfies hfirstD a g) (honestVerifierGatesQ hfirstD a g)

theorem acceptedQ_walk_challenges (a g : K97cubic) :
    ((rawStrategyQ hfirstD).familyAt (coinQ a g) cfgD.challenges.lam seedH_ne).computeWalkAlpha = a ∧
      ((rawStrategyQ hfirstD).familyAt (coinQ a g) cfgD.challenges.lam seedH_ne).walkGamma = g ∧
      ((rawStrategyQ hfirstD).familyAt (coinQ a g) cfgD.challenges.lam seedH_ne).memoryWalkAlpha = alphaD ∧
      (∀ kind, (((rawStrategyQ hfirstD).familyAt (coinQ a g) cfgD.challenges.lam seedH_ne).computeWalkRAP kind).Satisfies
        ((rawStrategyQ hfirstD).messageAt (coinQ a g) cfgD.challenges.lam seedH_ne).computeWalkTrace) ∧
      (∀ kind, (((rawStrategyQ hfirstD).familyAt (coinQ a g) cfgD.challenges.lam seedH_ne).memoryWalkRAP kind).Satisfies
        ((rawStrategyQ hfirstD).messageAt (coinQ a g) cfgD.challenges.lam seedH_ne).memoryWalkTrace) := by
  have h := ((rawStrategyQ hfirstD).accepts_iff_six_families (coinQ a g) cfgD.challenges.lam seedH_ne).1
    (rawStrategyQ_accepts hfirstD a g)
  exact ⟨rfl, rfl, rfl, h.2.2.2.1, h.2.2.2.2.1⟩

/-! ## F. The verifier and the constructed package -/

theorem honest_exactTopologyQ (a g : K97cubic) :
    ComputeExactTopology ((rawStrategyQ hfirstD).familyAt (coinQ a g) cfgD.challenges.lam seedH_ne).exec ∧
      MemoryExactTopology ((rawStrategyQ hfirstD).familyAt (coinQ a g) cfgD.challenges.lam seedH_ne).exec := by
  change ComputeExactTopology
      (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec ∧
    MemoryExactTopology
      (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec
  rw [specializedProblemD_honest hfirstD]
  exact ⟨compute_topologyD, memory_topologyD⟩

def verifierQ : ProductionRawVerifier.TemplateAdapter.Strategy F97 K97cubic (ringChar K97cubic) :=
  HonestCommitment.verifierOf (dataD hfirstD) (alphaMCommitmentQ hfirstD) (walkArraysQ hfirstD)

theorem verifierQ_eq :
    verifierQ hfirstD = ProductionRawVerifier.TemplateAdapter.Strategy.honest (rawStrategyQ hfirstD) := rfl

theorem verifierQ_accepts (a g : K97cubic) : (verifierQ hfirstD).Accepts (coinQ a g) cfgD.challenges.lam :=
  ProductionRawVerifier.TemplateAdapter.Strategy.honest_accepts
    (rawStrategyQ hfirstD) (coinQ a g) cfgD.challenges.lam seedH_ne (rawStrategyQ_accepts hfirstD a g) (honest_exactTopologyQ hfirstD a g)

theorem structuralChecksQ :
    ProductionAxisStructureVerifier.structuralChecksAt (verifierQ hfirstD) seedD seedH_ne
      alphaD = true := by
  change
    (ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck (templateD hfirstD) &&
      ProductionAxisStructureVerifier.noWrapCheck (templateD hfirstD) alphaD) = true
  simp [alphaFreeAxisStructureD, noWrapD]

def residualHonestQ : BuildablePackage.CommitmentResidual (distinctCensusExecution hfirstD) :=
  HonestCommitment.commitmentResidualOf (dataD hfirstD) (alphaMCommitmentQ hfirstD) (walkArraysQ hfirstD)

/-- **The phase-correct package over the distinct-pair census.**  It has no `a`/`g` parameter. -/
theorem phase_walkOrder :
    2 ≤ (distinctCensusExecution hfirstD).cfg.compRows →
      (distinctCensusExecution hfirstD).cfg.compRows ≤ orderOf (inputsD hfirstD).computeWalkAlpha := fun _ => by
  have hα : (inputsD hfirstD).computeWalkAlpha = (2 : K97cubic) := rfl
  have hrows : (distinctCensusExecution hfirstD).cfg.compRows = 3 := rfl
  rw [hα, Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete.omega2_order, hrows]
  norm_num

def packageQ :
    OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F97 K97cubic 5 :=
  BuildablePackage.buildFullPackage (distinctCensusExecution hfirstD) (inputsD hfirstD)
    (residualHonestQ hfirstD)
    (inputsD_challenges hfirstD) DistinctCensusC1.pairedRecordLayout_distinctCensus
    (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD) (by
      change 1 ≤ 1; trivial))
    (phase_walkOrder hfirstD) (walkOrderMemD hfirstD) (DistinctCensusCommitment.rowsBoundD hfirstD)
    (DistinctCensusCommitment.residualD_generated hfirstD) DistinctCensusCommitment.f97_primeFieldD

theorem statementQ
    (hax : FormRAxisBound (packageQ hfirstD).optimized.sampled (packageQ hfirstD).optimized.basis)
    (hbasis : FormRBasis (packageQ hfirstD).optimized.basis)
    (hwidth : FormRWidth F97) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageQ hfirstD) :=
  BuildablePackage.universalOptimizedFullStrictThm54 (distinctCensusExecution hfirstD) (inputsD hfirstD)
    (residualHonestQ hfirstD) (inputsD_challenges hfirstD)
    DistinctCensusC1.pairedRecordLayout_distinctCensus
    (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD) (by
      change 1 ≤ 1; trivial))
    (phase_walkOrder hfirstD) (walkOrderMemD hfirstD) (DistinctCensusCommitment.rowsBoundD hfirstD)
    (DistinctCensusCommitment.residualD_generated hfirstD) DistinctCensusCommitment.f97_primeFieldD
    hax hbasis hwidth

variable (hrootAt : ∀ a g : K97cubic,
  (packageQ hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
include hrootAt

theorem packageQ_verifier : (packageQ hfirstD).strategy.verifier = verifierQ hfirstD := rfl

theorem packageQ_seed : (packageQ hfirstD).honestSeed = seedD := rfl

/-- **The one package accepts the coin at every sampled walk-challenge pair.** -/
theorem packageQ_accepts (a g : K97cubic) : (packageQ hfirstD).strategy.Accepts (coinQ a g) cfgD.challenges.lam := by
  apply ((packageQ hfirstD).strategy.accepts_iff (coinQ a g) cfgD.challenges.lam seedH_ne).2
  constructor
  · apply (ProductionAxisStructureVerifier.accepts_iff (verifierQ hfirstD) (coinQ a g) cfgD.challenges.lam seedH_ne).2
    exact ⟨((verifierQ hfirstD).accepts_iff_production (coinQ a g) cfgD.challenges.lam seedH_ne).1
      (verifierQ_accepts hfirstD a g), structuralChecksQ hfirstD⟩
  · exact hrootAt a g

/-! ## G. The five counted failure events, at the one package -/

theorem coinQ_not_zeroSeedFailureEvent (a g : K97cubic) :
    coinQ a g ∉ (zeroSeedFailureEvent : Finset (JointCoins K97cubic)) := by
  rw [mem_zeroSeedFailureEvent_iff]
  exact seedH_ne

theorem coinQ_not_collisionFailureEvent (a g : K97cubic) :
    coinQ a g ∉ collisionFailureEvent censusD.census := by
  rw [mem_collisionFailureEvent_iff]
  rintro ⟨i, hi⟩
  have hmem := censusD_pair_mem hfirstD i
  rcases op5Pairs_dichotomy _ hmem with hself | hpair
  · apply hi
    rw [show nprSeed (coinQ a g) = seedD from rfl, ← hself]
    exact sepSeed_self seedD _
  · rw [hpair] at hi
    exact hi operands_sepSeed

theorem baseQ_binding :
    RawTopologyBindingResidual
      (acceptedFamilyDataQ hfirstD seedD seedH_ne alphaD cfgD.challenges.lam).base := by
  have hc :
      (acceptedFamilyDataQ hfirstD seedD seedH_ne alphaD cfgD.challenges.lam).base.exec.ComputeRowsAccepted := by
    change
      (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.ComputeRowsAccepted
    rw [specializedProblemD_honest hfirstD]
    exact compute_rows_acceptedD
  have hm :
      (acceptedFamilyDataQ hfirstD seedD seedH_ne alphaD cfgD.challenges.lam).base.exec.MemoryRowsAccepted := by
    change
      (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.MemoryRowsAccepted
    rw [specializedProblemD_honest hfirstD]
    exact memory_rows_acceptedD
  apply (exactTopology_iff_rawTopologyBindingResidual_of_rowsAccepted _ hc hm).1
  constructor
  · change ComputeExactTopology
      (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec
    rw [specializedProblemD_honest hfirstD]
    exact compute_topologyD
  · change MemoryExactTopology
      (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec
    rw [specializedProblemD_honest hfirstD]
    exact memory_topologyD

theorem coinQ_not_specializedTopologyFailureEvent (a g : K97cubic) :
    coinQ a g ∉ specializedTopologyFailureEvent (verifierQ hfirstD).raw cfgD.challenges.lam := by
  rw [mem_specializedTopologyFailureEvent_iff]
  rintro ⟨hz, hbad⟩
  change g ∈
    topologyBadGammas (acceptedFamilyDataQ hfirstD seedD seedH_ne alphaD cfgD.challenges.lam).base at hbad
  rw [topologyBadGammas_empty_of_binding _ (baseQ_binding hfirstD hrootAt)] at hbad
  exact absurd hbad (Finset.notMem_empty _)

theorem coinQ_not_guardedAxisFailureEvent (a g : K97cubic) :
    coinQ a g ∉ ProductionP8Containment.guardedAxisFailureEvent (packageQ hfirstD).strategy
      cfgD.challenges.lam := by
  rw [ProductionP8Containment.mem_guardedAxisFailureEvent_iff]
  rintro ⟨hz, hbad⟩
  change alphaD ∈
    ProductionAxisStructureVerifier.verifierGuardedRootUnion (templateD hfirstD)
      cfgD.challenges.lam at hbad
  obtain ⟨i, -, hmem⟩ := Finset.mem_biUnion.1 hbad
  simp only [ProductionAxisStructureVerifier.verifierGuardedRootAlphas,
    Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  obtain ⟨-, -, ⟨e, hread, hverify, hne⟩, -, -⟩ := hmem
  exact hne
    (axis_eq_relaxis_transportedD hfirstD _ (dataD hfirstD).honest_execA i e hread hverify)

theorem coinQ_not_sizeWindowFailure (a g : K97cubic) :
    coinQ a g ∉ SizeWindowCounting.SizeWindowFailure skelD := by
  rw [SizeWindowCounting.mem_SizeWindowFailure_iff]
  rintro ⟨-, n, hn, _⟩
  rw [sizeWindowNounsD hfirstD] at hn
  exact List.not_mem_nil hn

theorem coinQ_not_failureUnion (a g : K97cubic) :
    coinQ a g ∉ ProductionP8Containment.FailureUnion (packageQ hfirstD).strategy
      (packageQ hfirstD).optimized.census cfgD.challenges.lam := by
  intro hbad
  simp only [ProductionP8Containment.FailureUnion, Finset.mem_union] at hbad
  rcases hbad with hbad | hbad
  · rcases hbad with hbad | hbad
    · rcases hbad with hbad | hbad
      · rcases hbad with hbad | hbad
        · exact coinQ_not_zeroSeedFailureEvent hfirstD hrootAt a g hbad
        · exact coinQ_not_collisionFailureEvent hfirstD hrootAt a g hbad
      · exact coinQ_not_specializedTopologyFailureEvent hfirstD hrootAt a g hbad
    · exact coinQ_not_guardedAxisFailureEvent hfirstD hrootAt a g hbad
  · exact coinQ_not_sizeWindowFailure hfirstD hrootAt a g hbad

theorem genuineTargetQ (a g : K97cubic) :
    ProductionP8Containment.GenuineTargetAt (packageQ hfirstD).strategy 97 7 (coinQ a g) cfgD.challenges.lam :=
  (packageQ hfirstD).containment (coinQ a g) cfgD.challenges.lam (packageQ_accepts hfirstD hrootAt a g)
    (coinQ_not_failureUnion hfirstD hrootAt a g)

/-! ## H. Quantifier order, nonzero challenges, non-constant walks -/

/-- **`∃ P, ∀ a g` — the package is outside the quantifier.** -/
theorem exists_package_accepting_every_challenge_pair :
    ∃ P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F97 K97cubic 5,
      ∀ a g : K97cubic, P.strategy.Accepts (coinQ a g) cfgD.challenges.lam :=
  ⟨packageQ hfirstD, packageQ_accepts hfirstD hrootAt⟩

theorem commit_then_sample_completeness
    (hax : FormRAxisBound (packageQ hfirstD).optimized.sampled (packageQ hfirstD).optimized.basis)
    (hbasis : FormRBasis (packageQ hfirstD).optimized.basis)
    (hwidth : FormRWidth F97) :
    ∃ P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F97 K97cubic 5,
      OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement P ∧
        ∀ a g : K97cubic,
          P.strategy.Accepts (coinQ a g) cfgD.challenges.lam ∧
            coinQ a g ∉ ProductionP8Containment.FailureUnion P.strategy P.optimized.census cfgD.challenges.lam ∧
            ProductionP8Containment.GenuineTargetAt P.strategy 97 7 (coinQ a g) cfgD.challenges.lam :=
  ⟨packageQ hfirstD, statementQ hfirstD hax hbasis hwidth,
    fun a g => ⟨packageQ_accepts hfirstD hrootAt a g, coinQ_not_failureUnion hfirstD hrootAt a g,
      genuineTargetQ hfirstD hrootAt a g⟩⟩

/-- The one package accepts coins with **different** `alphaC` and **different** `gamma`, including
a nonzero pair.  The isolated walk layer remains degenerate at `(0, 0)`; that coin is still
accepted, and is not hidden. -/
theorem packageQ_accepts_distinct_challenges :
    (packageQ hfirstD).strategy.Accepts (coinQ 0 0) cfgD.challenges.lam ∧
      (packageQ hfirstD).strategy.Accepts (coinQ alphaCN gammaN) cfgD.challenges.lam ∧
      alphaC (coinQ 0 0) = 0 ∧ gamma (coinQ 0 0) = 0 ∧
      alphaC (coinQ alphaCN gammaN) ≠ 0 ∧ gamma (coinQ alphaCN gammaN) ≠ 0 :=
  ⟨packageQ_accepts hfirstD hrootAt 0 0, packageQ_accepts hfirstD hrootAt alphaCN gammaN, rfl, rfl,
    alphaCN_ne_zero, gammaN_ne_zero⟩

/-- Acceptance plus `ln(1) = alphaC` proves the walk columns cannot be the same term at the zero
and nonzero coins of record. -/
theorem walkArraysQ_is_nonconstant_on_accepted_coins :
    walkArraysQ hfirstD (coinQ 0 0) cfgD.challenges.lam seedH_ne ≠ walkArraysQ hfirstD (coinQ alphaCN gammaN) cfgD.challenges.lam seedH_ne := by
  intro hw
  have hsix0 :=
    ((rawStrategyQ hfirstD).accepts_iff_six_families (coinQ 0 0) cfgD.challenges.lam seedH_ne).1
      (rawStrategyQ_accepts hfirstD 0 0)
  have hsixN :=
    ((rawStrategyQ hfirstD).accepts_iff_six_families (coinQ alphaCN gammaN) cfgD.challenges.lam seedH_ne).1
      (rawStrategyQ_accepts hfirstD alphaCN gammaN)
  have hcert0 :=
    (((rawStrategyQ hfirstD).messageAt (coinQ 0 0) cfgD.challenges.lam seedH_ne).computeWalkRAP_wholeTrace_iff).1
      hsix0.2.2.2.1
  have hcertN :=
    (((rawStrategyQ hfirstD).messageAt (coinQ alphaCN gammaN) cfgD.challenges.lam seedH_ne).computeWalkRAP_wholeTrace_iff).1
      hsixN.2.2.2.1
  have h0 := hcert0.1.ln1
  have hN := hcertN.1.ln1
  change (walkArraysQ hfirstD (coinQ 0 0) cfgD.challenges.lam seedH_ne).computeLn 1 = 0 at h0
  change (walkArraysQ hfirstD (coinQ alphaCN gammaN) cfgD.challenges.lam seedH_ne).computeLn 1 = alphaCN at hN
  apply alphaCN_ne_zero
  calc
    alphaCN = (walkArraysQ hfirstD (coinQ alphaCN gammaN) cfgD.challenges.lam seedH_ne).computeLn 1 := hN.symm
    _ = (walkArraysQ hfirstD (coinQ 0 0) cfgD.challenges.lam seedH_ne).computeLn 1 :=
      congrArg (fun W : RawWalkArrays K97cubic => W.computeLn 1) hw.symm
    _ = 0 := h0

/-! ## I. -/

theorem packageQ_census_is_the_committed_census :
    (packageQ hfirstD).optimized.commitment.skeleton = skelD ∧
      (packageQ hfirstD).strategy.skeleton = skelD ∧
      (packageQ hfirstD).optimized.census = censusD ∧
      (residualHonestQ hfirstD).census = censusD ∧
      (dataD hfirstD).census = censusD :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem packageQ_consumed_census_has_genuine_distinct_pair :
    ∃ i : Fin (packageQ hfirstD).optimized.census.census.count,
      (packageQ hfirstD).optimized.census.census.pair i =
          (operandLeft, operandRight) ∧
        ((packageQ hfirstD).optimized.census.census.pair i).1 ≠
          ((packageQ hfirstD).optimized.census.census.pair i).2 :=
  censusD_has_distinct_pair

theorem packageQ_accepts_with_substantive_collision_exclusion (a g : K97cubic) :
    (packageQ hfirstD).strategy.Accepts (coinQ a g) cfgD.challenges.lam ∧
      (∃ i : Fin (packageQ hfirstD).optimized.census.census.count,
        (packageQ hfirstD).optimized.census.census.pair i = (operandLeft, operandRight) ∧
          ((packageQ hfirstD).optimized.census.census.pair i).1 ≠
            ((packageQ hfirstD).optimized.census.census.pair i).2) ∧
      nprSeed (coinQ a g) = seedD ∧ seedD = (8 : K97cubic) ∧ seedD ≠ -1 ∧
      coinQ a g ∉ collisionFailureEvent (packageQ hfirstD).optimized.census.census ∧
      coinQ a g ∉ ProductionP8Containment.FailureUnion (packageQ hfirstD).strategy
        (packageQ hfirstD).optimized.census cfgD.challenges.lam ∧
      ProductionP8Containment.GenuineTargetAt (packageQ hfirstD).strategy 97 7 (coinQ a g) cfgD.challenges.lam :=
  ⟨packageQ_accepts hfirstD hrootAt a g,
    packageQ_consumed_census_has_genuine_distinct_pair hfirstD hrootAt,
    rfl, rfl, seedD_ne_neg_one, coinQ_not_collisionFailureEvent hfirstD hrootAt a g,
    coinQ_not_failureUnion hfirstD hrootAt a g, genuineTargetQ hfirstD hrootAt a g⟩

theorem packageQ_regression :
    (packageQ hfirstD).objects.cfg = cfgD ∧
      (packageQ hfirstD).objects.exec = execD ∧
      (packageQ hfirstD).computeChip.rap.w = 303 ∧ (packageQ hfirstD).computeChip.rap.s = 418 ∧
      (packageQ hfirstD).memoryChip.rap.w = 205 ∧ (packageQ hfirstD).memoryChip.rap.s = 156 ∧
      (packageQ hfirstD).computeChip.rap.H.card = 3 ∧
      (distinctCensusExecution hfirstD).cfg.compRows = 3 ∧
      (distinctCensusExecution hfirstD).cfg.memRows = 21 ∧
      (distinctCensusExecution hfirstD).cfg.kMem = 1 ∧
      (inputsD hfirstD).computeChallenges = default ∧
      (inputsD hfirstD).hOrb = 5 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · exact (BuildablePackage.constructed_resources (distinctCensusExecution hfirstD) (inputsD hfirstD)
      (residualHonestQ hfirstD) (inputsD_challenges hfirstD) DistinctCensusC1.pairedRecordLayout_distinctCensus
      (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD) (by
      change 1 ≤ 1; trivial))
      (phase_walkOrder hfirstD) (walkOrderMemD hfirstD) (DistinctCensusCommitment.rowsBoundD hfirstD)
    (DistinctCensusCommitment.residualD_generated hfirstD) DistinctCensusCommitment.f97_primeFieldD).1
  · exact (BuildablePackage.constructed_resources (distinctCensusExecution hfirstD) (inputsD hfirstD)
      (residualHonestQ hfirstD) (inputsD_challenges hfirstD) DistinctCensusC1.pairedRecordLayout_distinctCensus
      (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD) (by
      change 1 ≤ 1; trivial))
      (phase_walkOrder hfirstD) (walkOrderMemD hfirstD) (DistinctCensusCommitment.rowsBoundD hfirstD)
    (DistinctCensusCommitment.residualD_generated hfirstD) DistinctCensusCommitment.f97_primeFieldD).2.1
  · exact (BuildablePackage.constructed_resources (distinctCensusExecution hfirstD) (inputsD hfirstD)
      (residualHonestQ hfirstD) (inputsD_challenges hfirstD) DistinctCensusC1.pairedRecordLayout_distinctCensus
      (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD) (by
      change 1 ≤ 1; trivial))
      (phase_walkOrder hfirstD) (walkOrderMemD hfirstD) (DistinctCensusCommitment.rowsBoundD hfirstD)
    (DistinctCensusCommitment.residualD_generated hfirstD) DistinctCensusCommitment.f97_primeFieldD).2.2.1
  · exact (BuildablePackage.constructed_resources (distinctCensusExecution hfirstD) (inputsD hfirstD)
      (residualHonestQ hfirstD) (inputsD_challenges hfirstD) DistinctCensusC1.pairedRecordLayout_distinctCensus
      (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD) (by
      change 1 ≤ 1; trivial))
      (phase_walkOrder hfirstD) (walkOrderMemD hfirstD) (DistinctCensusCommitment.rowsBoundD hfirstD)
    (DistinctCensusCommitment.residualD_generated hfirstD) DistinctCensusCommitment.f97_primeFieldD).2.2.2
  · exact (BuildablePackage.constructed_row_budgets (distinctCensusExecution hfirstD) (inputsD hfirstD)
      (residualHonestQ hfirstD) (inputsD_challenges hfirstD) DistinctCensusC1.pairedRecordLayout_distinctCensus
      (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD) (by
      change 1 ≤ 1; trivial))
      (phase_walkOrder hfirstD) (walkOrderMemD hfirstD) (DistinctCensusCommitment.rowsBoundD hfirstD)
    (DistinctCensusCommitment.residualD_generated hfirstD) DistinctCensusCommitment.f97_primeFieldD).1

theorem packageQ_commitment_unchanged :
    residualHonestQ hfirstD =
        HonestCommitment.commitmentResidualOf (dataD hfirstD) (alphaMCommitmentQ hfirstD) (walkArraysQ hfirstD) ∧
      (packageQ hfirstD).optimized.commitment.skeleton = (dataD hfirstD).skeleton ∧
      (packageQ hfirstD).optimized.commitment.skeleton = skelD ∧
      (packageQ hfirstD).objects.cfg = cfgD ∧ (packageQ hfirstD).objects.exec = execD ∧
      (packageQ hfirstD).optimized.census = censusD :=
  ⟨rfl, rfl, dataD_skeleton hfirstD, rfl, rfl, rfl⟩

/-! ## J. Optimized acceptance, still inside the compute failure event

The generic canonical bridge (`canonicalProductionAcceptance`) applies at `packageQ` for every
sampled `(a, g)`.  That does **not** discharge `acceptance_to_target`: the committed compute
tree is `OP_5` then two `OP_1` rows, so the first compiled state is `s5`
and the last is `s1`.  Neither is `s0`, the terminal-selector head at public offset 31 vanishes,
and the compiler-fold `⟨0,0⟩` pins scalar challenge 36 at `0`, which is then a root of a
nonzero selector polynomial.  The same obstruction is independent of
the later-round walk arrays, so phase-correct completeness does not move it. -/

abbrev computeTraceQ := canonicalComputeTrace (packageQ hfirstD)
abbrev memoryTraceQ := canonicalMemoryTrace (packageQ hfirstD)
abbrev tupleQ (a g : K97cubic) := canonicalProductionTuple (packageQ hfirstD) (coinQ a g)

theorem packageQ_optimized_acceptance (a g : K97cubic)
    (hax : FormRAxisBound (packageQ hfirstD).optimized.sampled (packageQ hfirstD).optimized.basis)
    (hbasis : FormRBasis (packageQ hfirstD).optimized.basis)
    (hwidth : FormRWidth F97) :
    (packageQ hfirstD).OptimizedHistoricalAcceptanceAt (computeTraceQ hfirstD) (memoryTraceQ hfirstD)
      (tupleQ hfirstD a g) :=
  canonicalProductionAcceptance (packageQ hfirstD) (coinQ a g) (packageQ_accepts hfirstD hrootAt a g)
    rfl rfl (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD) (by
      change 1 ≤ 1; trivial))
    DistinctCensusExecution.execD_cprimeCoherent hax hbasis hwidth

theorem packageQ_first_state :
    ((packageQ hfirstD).optimized.family.problem.exec.computePubAt
      ⟨0, (packageQ hfirstD).optimized.family.problem.cfg.compRows_pos⟩).state = .s5 := by
  change (execD.computePubAt ⟨0, _⟩).state = _
  rw [computePubAtD_zero]
  rfl

theorem packageQ_last_state :
    ((packageQ hfirstD).optimized.family.problem.exec.computePubAt
      ⟨(packageQ hfirstD).optimized.family.problem.cfg.compRows - 1,
        Nat.sub_lt (packageQ hfirstD).optimized.family.problem.cfg.compRows_pos Nat.one_pos⟩).state =
      .s1 := by
  change (execD.computePubAt ⟨2, _⟩).state = _
  rw [computePubAtD_two]
  rfl

theorem packageQ_selector31_head_zero :
    ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)).trace 0 -
      ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)).pub 31 = 0 := by
  rw [canonical_selector31_head (packageQ hfirstD), packageQ_first_state hfirstD hrootAt,
    packageQ_last_state hfirstD hrootAt]
  norm_num [OptimizedComputeCodec.stateIndex]

theorem packageQ_selector31_second_nonzero :
    ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)).trace 1 -
      ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)).pub 32 = -1 := by
  have ht := canonical_scalarEnv_trace (packageQ hfirstD) (1 : Fin 11)
  have hp := (packageQ hfirstD).optimized.computePublicPins.2.2 (1 : Fin 11)
  change ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)).trace 1 = _ at ht
  have hp' :
      ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)).pub 32 =
        (if (1 : Fin 11) = OptimizedComputeCodec.stateIndex
            ((packageQ hfirstD).optimized.family.problem.exec.computePubAt
              ⟨(packageQ hfirstD).optimized.family.problem.cfg.compRows - 1,
                Nat.sub_lt (packageQ hfirstD).optimized.family.problem.cfg.compRows_pos
                  Nat.one_pos⟩).state then 1 else 0) := by
    change (packageQ hfirstD).optimized.computePublic 32 = _
    simpa using hp
  rw [ht, hp', packageQ_first_state hfirstD hrootAt, packageQ_last_state hfirstD hrootAt]
  norm_num [OptimizedComputeCodec.stateIndex]

/-- The tuple-level statement is not restated here. -/
theorem packageQ_zero_was_a_bad_selector_challenge :
    (0 : F97) ∈
      finalSelectorBadChallenges ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)) := by
  apply Finset.mem_union_right
  unfold selectorBadChallenges valueBadChallenges
  have hnonzero :
      ∃ a ∈ selectorErrors ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)) 31, a ≠ 0 := by
    refine ⟨-1, ?_, neg_ne_zero.mpr one_ne_zero⟩
    simp [selectorErrors, packageQ_selector31_second_nonzero hfirstD hrootAt]
  rw [if_pos hnonzero]
  simp [selectorErrors, valueRlcPolynomial, packageQ_selector31_head_zero hfirstD hrootAt]

/-- **Rung B stop — stage 3e released it, and W1 removed the coin it was about.**

This is a *release*, not a
regression; the full tuple-level statement is not restated here. -/
theorem accepted_optimized_tuple_is_inside_historical_compute_failure (a g : K97cubic)
    (hax : FormRAxisBound (packageQ hfirstD).optimized.sampled (packageQ hfirstD).optimized.basis)
    (hbasis : FormRBasis (packageQ hfirstD).optimized.basis)
    (hwidth : FormRWidth F97) :
    (packageQ hfirstD).OptimizedHistoricalAcceptanceAt (computeTraceQ hfirstD) (memoryTraceQ hfirstD)
      (tupleQ hfirstD a g) ∧
      (0 : F97) ∈
        finalSelectorBadChallenges ((packageQ hfirstD).computeScalarEnv (computeTraceQ hfirstD)) :=
  ⟨packageQ_optimized_acceptance hfirstD hrootAt a g hax hbasis hwidth,
    packageQ_zero_was_a_bad_selector_challenge hfirstD hrootAt⟩

end

end Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect

#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.uniformEndpointsQ_exist
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.phaseCompletionQ_nonempty
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.alphaMCommitmentQ
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.walkArraysQ
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.walkArraysQ_reads_the_coin
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.mixedAssignmentQ_satisfies
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.rawStrategyQ_accepts
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.packageQ
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.statementQ
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.packageQ_accepts
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.coinQ_not_collisionFailureEvent
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.coinQ_not_failureUnion
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.genuineTargetQ
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.exists_package_accepting_every_challenge_pair
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.commit_then_sample_completeness
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.packageQ_accepts_distinct_challenges
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.walkArraysQ_is_nonconstant_on_accepted_coins
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.packageQ_consumed_census_has_genuine_distinct_pair
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.packageQ_accepts_with_substantive_collision_exclusion
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.packageQ_regression
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.packageQ_optimized_acceptance
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.packageQ_first_state
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.packageQ_last_state
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.packageQ_selector31_head_zero
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.packageQ_selector31_second_nonzero
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.packageQ_zero_was_a_bad_selector_challenge
#print axioms Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect.accepted_optimized_tuple_is_inside_historical_compute_failure
