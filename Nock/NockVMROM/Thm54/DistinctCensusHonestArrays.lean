import Nock.NockVMROM.Thm54.DistinctCensusCommitment
import Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
import Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Honest later-round arrays over the distinct-pair `OP_5` census

`DistinctCensusCommitment` constructed `dataD` / `residualD` / `packageD` over the seed-`8`
`OP_5` execution whose consumed census contains `([7 9], [8 10])`.  The residual was
residual-of-zero: `packageD_accepts_none`  compiles that every
response multiplicity is zero, so no joint coin is accepted and collision exclusion is not
package-and-acceptance-substantive.

This module supplies the **honest** later-round message over the **same** `dataD` skeleton —
it does not rebuild the execution.  The chain is the MultiRoot one, at this census:
`SemanticIOWitness` from `semanticPreimageD`, `jointVerification_complete`, the seventeen-conjunct `RawMessage.VerifierGates`, `TemplateAdapter.Strategy.honest_accepts`, and the
per-root axis boundary from the identically-zero root polynomial of the served forest.

The resulting `packageH` is one constructed package.  Its later-round walk columns come from
the single honest completion at `(alphaC, gamma) = (0, 0)`, so the acceptance quantifier is
`∃ P, P.Accepts coinH` at `coinH = ((0, 0), (4, 8))`, **not** `∀ coin, Accepts`.  Seed stays
`8`.  Collision exclusion at that accepted coin is substantive: the consumed census is the
twenty-four-entry `op5` census whose unique bad seed is `-1`, and `8 ≠ -1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Nock.NockVMROM.Thm54.DistinctCensusHonestArrays

open scoped Classical Polynomial
open Nock Nock.Noun Nock.Walk Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.NockVMROM.Thm54.OptimizedMemorySameExecution
open SemanticStrategy SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.EqualityOperandCensus
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.MultiRootHonestArrays
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.SizeWindowCounting

noncomputable section

local instance prime97h : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97h : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
include hfirstD

/-! ## A. The committed timestamp strategy of `dataD` -/

abbrev timestampD : DataOnlyTemplateFixedStagedTimestampStrategy (F := F97) (K := K97cubic) :=
  (dataD hfirstD).timestampStrategy

omit hfirstD in
theorem seedH_ne : seedD ≠ 0 := seedD_ne

omit hfirstD in
theorem two_inv_mul_D :
    (Polynomial.C ((2 : K97cubic)⁻¹)) * (Polynomial.C (2 : K97cubic)) = 1 := by
  rw [← Polynomial.C_mul, inv_mul_cancel₀ NonterminalServedRow.two_ne_zero_K97, Polynomial.C_1]

theorem specializedProblemD_honest :
    specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam = ⟨cfgD, execD⟩ :=
  (dataD hfirstD).honest_specialization

theorem responseLenD (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    (specializedProblem (timestampD hfirstD) z hz α lmb).exec.derivedResponseIO.length = 4 := by
  show (((dataD hfirstD).executionTemplate z).specialize α lmb).derivedResponseIO.length = 4
  rw [HonestCommitment.derivedResponseIO_length_eq ((dataD hfirstD).binds z α lmb) (dataD hfirstD).honest_binds]
  change execD.derivedResponseIO.length = 4
  rw [derived_responsesD]
  rfl

theorem requestLenD (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    (specializedProblem (timestampD hfirstD) z hz α lmb).exec.derivedRequestIO.length = 4 := by
  show (((dataD hfirstD).executionTemplate z).specialize α lmb).derivedRequestIO.length = 4
  rw [HonestCommitment.derivedRequestIO_length_eq ((dataD hfirstD).binds z α lmb) (dataD hfirstD).honest_binds]
  change execD.derivedRequestIO.length = 4
  rw [derived_requestsD]
  rfl

/-! ## B. The zero-endpoint raw family at the honest sample -/

def familyDataD0 (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    AlphaMFamilyData (timestampD hfirstD) z hz α lmb where
  compNodeWidth := NodeEncoding.computeNodeWidth
  compNodeEncode := NodeEncoding.computeNodeEncode stateTagChar97
  memNodeWidth := NodeEncoding.memoryNodeWidth
  memNodeEncode := NodeEncoding.memoryNodeEncode stateTagChar97
  requests := 0
  responses := 0
  outMem := 0

def rawZeroFamilyD : RawPlusIOSegmentedFamily F97 K97cubic :=
  (familyDataD0 hfirstD seedD seedH_ne alphaD cfgD.challenges.lam).atCoins 0 0

theorem rawZeroFamilyD_problem : (rawZeroFamilyD hfirstD).problem = ⟨cfgD, execD⟩ :=
  specializedProblemD_honest hfirstD

theorem rawZeroFamilyD_tableAssumptions :
    (rawZeroFamilyD hfirstD).problem.TableCompletenessAssumptions := by
  rw [rawZeroFamilyD_problem]
  exact ⟨seedH_ne, (chainedD hfirstD).compute_wf, (chainedD hfirstD).memory_wf,
    (chainedD hfirstD).memory_same_lambda⟩

theorem rawZeroFamilyD_progCapacity :
    (rawZeroFamilyD hfirstD).exec.derivedRequestIO.length + 1 ≤ 2 ^ (rawZeroFamilyD hfirstD).cfg.orbit.h := by
  change
    (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.derivedRequestIO.length + 1 ≤
      2 ^ (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).cfg.orbit.h
  rw [specializedProblemD_honest hfirstD]
  change execD.derivedRequestIO.length + 1 ≤ 2 ^ cfgD.orbit.h
  rw [derived_requestsD]
  norm_num [cfgD, orbitD]

theorem rawZeroFamilyD_memCapacity :
    (rawZeroFamilyD hfirstD).exec.derivedResponseIO.length + 1 ≤ 2 ^ (rawZeroFamilyD hfirstD).cfg.orbit.h := by
  change
    (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.derivedResponseIO.length + 1 ≤
      2 ^ (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).cfg.orbit.h
  rw [specializedProblemD_honest hfirstD]
  change execD.derivedResponseIO.length + 1 ≤ 2 ^ cfgD.orbit.h
  rw [derived_responsesD]
  norm_num [cfgD, orbitD]

def legacyZeroFamilyD : PlusIOSegmentedFamily F97 K97cubic :=
  (rawZeroFamilyD hfirstD).toLegacy (rawZeroFamilyD_tableAssumptions hfirstD)
    (fun _ _ h => NodeEncoding.computeNodeEncode_labelOf_eq stateTagChar97 h)
    (fun _ _ h => NodeEncoding.memoryNodeEncode_labelOf_eq stateTagChar97 h)
    (rawZeroFamilyD_progCapacity hfirstD) (rawZeroFamilyD_memCapacity hfirstD)

theorem legacyZeroFamilyD_chained :
    ChainedSemanticExactLanguage (legacyZeroFamilyD hfirstD).problem.cfg
      (legacyZeroFamilyD hfirstD).problem.exec := by
  change ChainedSemanticExactLanguage
    (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).cfg
    (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec
  rw [specializedProblemD_honest hfirstD]
  exact (chainedD hfirstD)

def legacyZeroFamilyD_semanticWitness :
    SemanticIOWitness (legacyZeroFamilyD hfirstD).problem.cfg (legacyZeroFamilyD hfirstD).problem.exec := by
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

theorem legacyZeroFamilyD_KszBound :
    (legacyZeroFamilyD hfirstD).problem.cfg.Ksz < ringChar K97cubic := by
  change (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).cfg.Ksz < ringChar K97cubic
  rw [specializedProblemD_honest, ringChar_K97]
  norm_num [cfgD]

/-! ## C. The honest post-challenge completion -/

structure HonestCompletionD where
  requests : IOField K97cubic
  responses : IOField K97cubic
  outMem : IOField K97cubic
  assignment :
    JointAssignment
      ((legacyZeroFamilyD hfirstD).withIOEndpoints requests responses outMem)
      (ringChar K97cubic)

theorem honestCompletionD_nonempty : Nonempty (HonestCompletionD hfirstD) := by
  obtain ⟨requests, responses, outMem, ⟨A⟩⟩ :=
    jointVerification_complete (legacyZeroFamilyD hfirstD)
      (legacyZeroFamilyD_chained hfirstD) (legacyZeroFamilyD_semanticWitness hfirstD)
      (legacyZeroFamilyD_KszBound hfirstD)
  exact ⟨⟨requests, responses, outMem, A⟩⟩

noncomputable def honestCompletionD : HonestCompletionD hfirstD :=
  Classical.choice (honestCompletionD_nonempty hfirstD)

abbrev legacyFamilyD : PlusIOSegmentedFamily F97 K97cubic :=
  (legacyZeroFamilyD hfirstD).withIOEndpoints (honestCompletionD hfirstD).requests
    (honestCompletionD hfirstD).responses (honestCompletionD hfirstD).outMem

abbrev honestAssignmentD :
    PlusIOSameExecutionAssignment (legacyFamilyD hfirstD) (ringChar K97cubic) :=
  (honestCompletionD hfirstD).assignment.sameExecution

/-! ## D. The honest later-round message -/

def acceptedFamilyDataD (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    AlphaMFamilyData (timestampD hfirstD) z hz α lmb where
  compNodeWidth := NodeEncoding.computeNodeWidth
  compNodeEncode := NodeEncoding.computeNodeEncode stateTagChar97
  memNodeWidth := NodeEncoding.memoryNodeWidth
  memNodeEncode := NodeEncoding.memoryNodeEncode stateTagChar97
  requests := (honestCompletionD hfirstD).requests
  responses := (honestCompletionD hfirstD).responses
  outMem := (honestCompletionD hfirstD).outMem

theorem acceptedFamilyD_response_length (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    (acceptedFamilyDataD hfirstD z hz α lmb).base.exec.derivedResponseIO.length = 4 :=
  responseLenD hfirstD z hz α lmb

theorem honestAssignmentD_response_length :
    (legacyFamilyD hfirstD).problem.exec.derivedResponseIO.length = 4 :=
  responseLenD hfirstD seedD seedH_ne alphaD cfgD.challenges.lam

/-- **The honest, non-zero later-round `alphaM` message.** -/
def alphaMCommitmentD (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    AlphaMCommitment (p := ringChar K97cubic) (timestampD hfirstD) z hz α lmb where
  familyData := acceptedFamilyDataD hfirstD z hz α lmb
  tables :=
    { compute := (honestAssignmentD hfirstD).computeTableAux
      memory := (honestAssignmentD hfirstD).memoryTableAux }
  io :=
    { multiplicity := fun j =>
        (honestAssignmentD hfirstD).exactIO.multiplicity
          ⟨j, by
            have hj := j.isLt
            have hsource := acceptedFamilyD_response_length hfirstD z hz α lmb
            have htarget := honestAssignmentD_response_length hfirstD
            omega⟩
      progAcc := (honestAssignmentD hfirstD).exactIO.progAcc
      memAcc := (honestAssignmentD hfirstD).exactIO.memAcc }

/-- Walk columns of the same completion.  They ignore `ω`: this is one specialized later-round
message, not a commit-then-sample family. -/
def walkArraysD (_ω : JointCoins K97cubic) (_lmb : K97cubic) (_hz : nprSeed _ω ≠ 0) : RawWalkArrays K97cubic where
  computeLn := (honestAssignmentD hfirstD).computeWalk.ln
  computeCount := (honestAssignmentD hfirstD).computeWalk.count
  computeAcc := (honestAssignmentD hfirstD).computeWalk.acc
  memoryLn := (honestAssignmentD hfirstD).memoryWalk.ln
  memoryCount := (honestAssignmentD hfirstD).memoryWalk.count
  memoryAcc := (honestAssignmentD hfirstD).memoryWalk.acc

/-- The honest coin of this fixture: walk challenges `(0, 0)`, `alphaM = 4`, NPR seed `8`. -/
def coinH : JointCoins K97cubic := ((0, 0), (alphaD, seedD))

theorem coinH_coordinates :
    alphaC coinH = 0 ∧ gamma coinH = 0 ∧
      alphaM coinH = alphaD ∧ nprSeed coinH = seedD :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem coinH_seed_eq : nprSeed coinH = seedD := rfl

theorem coinH_seed_ne_neg_one : nprSeed coinH ≠ -1 :=
  seedD_ne_neg_one

def rawStrategyD : TemplateRawJointSoundness.Strategy F97 K97cubic (ringChar K97cubic) where
  timestamp := timestampD hfirstD
  afterAlphaM := alphaMCommitmentD hfirstD
  afterCoins := walkArraysD hfirstD

theorem rawStrategyD_familyAt :
    (rawStrategyD hfirstD).familyAt coinH cfgD.challenges.lam seedH_ne =
      RawPlusIOSegmentedFamily.ofLegacy (legacyFamilyD hfirstD) := by
  rfl

theorem rawStrategyD_messageAt :
    (rawStrategyD hfirstD).messageAt coinH cfgD.challenges.lam seedH_ne = RawMessage.ofLegacy (honestAssignmentD hfirstD) := by
  rfl

/-! ## E. The seventeen verifier gates at the honest coin -/

abbrev rawLegacyD : RawPlusIOSegmentedFamily F97 K97cubic :=
  RawPlusIOSegmentedFamily.ofLegacy (legacyFamilyD hfirstD)

theorem rawLegacyD_computeRowsAccepted : (rawLegacyD hfirstD).exec.ComputeRowsAccepted := by
  change (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.ComputeRowsAccepted
  rw [specializedProblemD_honest hfirstD]
  exact compute_rows_acceptedD

theorem rawLegacyD_memoryRowsAccepted : (rawLegacyD hfirstD).exec.MemoryRowsAccepted := by
  change (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.MemoryRowsAccepted
  rw [specializedProblemD_honest hfirstD]
  exact memory_rows_acceptedD

theorem rawLegacyD_computePubAt_zero :
    (rawLegacyD hfirstD).exec.computePubAt ⟨0, (rawLegacyD hfirstD).cfg.compRows_pos⟩ = op5PubD := by
  change
    (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.computePubAt
        ⟨0, (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).cfg.compRows_pos⟩ =
      op5PubD
  rw [specializedProblemD_honest hfirstD]
  exact computePubAtD_zero

theorem rawLegacyD_Ksz : (rawLegacyD hfirstD).cfg.Ksz = 4 := by
  change (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).cfg.Ksz = 4
  rw [specializedProblemD_honest hfirstD]
  rfl

theorem rawLegacyD_requests :
    (rawLegacyD hfirstD).exec.derivedRequestIO =
      [NockVM.encRecFormR recF MemoryTable.formRDefault,
          NockVM.encRecFormR recT MemoryTable.formRDefault,
              NockVM.encRecFormR recL MemoryTable.formRDefault,
                  NockVM.encRecFormR recR MemoryTable.formRDefault] := by
  change
    (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.derivedRequestIO = _
  rw [specializedProblemD_honest hfirstD]
  exact derived_requestsD

theorem rawLegacyD_responses :
    (rawLegacyD hfirstD).exec.derivedResponseIO =
      [NockVM.encRecFormR recF MemoryTable.formRDefault,
          NockVM.encRecFormR recT MemoryTable.formRDefault,
              NockVM.encRecFormR recL MemoryTable.formRDefault,
                  NockVM.encRecFormR recR MemoryTable.formRDefault] := by
  change
    (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.derivedResponseIO = _
  rw [specializedProblemD_honest hfirstD]
  exact derived_responsesD

theorem claimD :
    skelD.publicClaim =
      { subject := op5Subject, formula := op5Formula, result := op5Result } := by
  simp [skelD, skeletonOfNodes, computeNodesD, mapNTree, op5Node,
    SemanticSkeleton.publicClaim, op5SkelD, op5Row]

theorem honestVerifierGatesD :
    (RawMessage.ofLegacy (honestAssignmentD hfirstD)).VerifierGates skelD.publicClaim coinH := by
  refine ⟨seedH_ne, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact rowAlignment_of_rowsAcceptedM (rawLegacyD hfirstD)
      (rawLegacyD_computeRowsAccepted hfirstD) (rawLegacyD_memoryRowsAccepted hfirstD)
  · refine ⟨rfl, ?_, rfl, ?_⟩
    · intro hchar
      have hh : hchar = stateTagChar97 := Subsingleton.elim _ _
      subst hchar
      rfl
    · intro hchar
      have hh : hchar = stateTagChar97 := Subsingleton.elim _ _
      subst hchar
      rfl
  · rw [rawLegacyD_computePubAt_zero hfirstD, claimD hfirstD]
    rfl
  · rw [rawLegacyD_computePubAt_zero hfirstD, claimD hfirstD]
    rfl
  · rw [rawLegacyD_computePubAt_zero hfirstD, claimD hfirstD]
    rfl
  · exact (honestCompletionD hfirstD).assignment.public_endpoints.1
  · exact (honestCompletionD hfirstD).assignment.public_endpoints.2
  · exact (honestAssignmentD hfirstD).exactIO.multiplicity_ne_zero
  · rw [rawLegacyD_requests hfirstD, rawLegacyD_Ksz hfirstD]
    norm_num [IO.InRange]
  · rw [rawLegacyD_requests hfirstD, ← derived_requestsD]
    exact requestsD_nodup
  · rw [rawLegacyD_responses hfirstD, rawLegacyD_Ksz hfirstD]
    norm_num
  · rw [rawLegacyD_responses hfirstD, ← derived_responsesD]
    exact responsesD_nodup

theorem rawStrategyD_accepts_coinH : (rawStrategyD hfirstD).Accepts coinH cfgD.challenges.lam := by
  apply ((rawStrategyD hfirstD).accepts_iff_raw coinH cfgD.challenges.lam seedH_ne).2
  change (RawMessage.ofLegacy (honestAssignmentD hfirstD)).Accepts skelD.publicClaim coinH
  exact RawMessage.accepts_of_legacy_assignment
    skelD.publicClaim coinH (honestAssignmentD hfirstD)
    (honestCompletionD hfirstD).assignment.sixFamilies (honestVerifierGatesD hfirstD)

/-! ## F. The verifier accepts the honest coin -/

theorem honest_exactTopologyD :
    ComputeExactTopology ((rawStrategyD hfirstD).familyAt coinH cfgD.challenges.lam seedH_ne).exec ∧
      MemoryExactTopology ((rawStrategyD hfirstD).familyAt coinH cfgD.challenges.lam seedH_ne).exec := by
  change ComputeExactTopology (rawLegacyD hfirstD).exec ∧ MemoryExactTopology (rawLegacyD hfirstD).exec
  change ComputeExactTopology
      (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec ∧
    MemoryExactTopology
      (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec
  rw [specializedProblemD_honest hfirstD]
  exact ⟨compute_topologyD, memory_topologyD⟩

def verifierH : ProductionRawVerifier.TemplateAdapter.Strategy F97 K97cubic (ringChar K97cubic) :=
  HonestCommitment.verifierOf (dataD hfirstD) (alphaMCommitmentD hfirstD) (walkArraysD hfirstD)

theorem verifierH_eq :
    verifierH hfirstD = ProductionRawVerifier.TemplateAdapter.Strategy.honest (rawStrategyD hfirstD) := rfl

theorem verifierH_accepts_coinH : (verifierH hfirstD).Accepts coinH cfgD.challenges.lam :=
  ProductionRawVerifier.TemplateAdapter.Strategy.honest_accepts
    (rawStrategyD hfirstD) coinH cfgD.challenges.lam seedH_ne (rawStrategyD_accepts_coinH hfirstD) (honest_exactTopologyD hfirstD)

/-! ## G. The committed axis structure of the one serviced root -/

abbrev templateD :
    ExactExecutionTemplate (HonestCommitment.configTemplateOf (distinctCensusExecution hfirstD) seedD) :=
  (dataD hfirstD).executionTemplate seedD

theorem kMemD :
    (HonestCommitment.configTemplateOf (distinctCensusExecution hfirstD) seedD).kMem = 1 := rfl

/-- The committed axis tree: four nested `read`/`verify` pairs on exponents `1..4`. -/
def treeD : AxisBatching.MTree K97cubic :=
  AxisBatching.MTree.read 1
    (AxisBatching.MTree.decompose AxisBatching.MTree.halt
      (AxisBatching.MTree.read 2
        (AxisBatching.MTree.verify 1 3
          (AxisBatching.MTree.decompose
            (AxisBatching.MTree.read 3
              (AxisBatching.MTree.verify 2 2
                (AxisBatching.MTree.decompose AxisBatching.MTree.halt
                  (AxisBatching.MTree.verify 3 3
                    (AxisBatching.MTree.decompose AxisBatching.MTree.halt
                      AxisBatching.MTree.halt)))))
            (AxisBatching.MTree.read 4
              (AxisBatching.MTree.decompose AxisBatching.MTree.halt
                (AxisBatching.MTree.verify 4 3
                  (AxisBatching.MTree.decompose AxisBatching.MTree.halt
                    AxisBatching.MTree.halt))))))))

set_option maxRecDepth 400000 in
theorem alphaFreeRootD_zero
    (h : (0 : ℕ) < (HonestCommitment.configTemplateOf (distinctCensusExecution hfirstD) seedD).kMem) :
    ProductionAxisStructureVerifier.alphaFreeRoot (templateD hfirstD) ⟨0, h⟩ = treeD := by
  simp [treeD, ProductionAxisStructureVerifier.alphaFreeRoot,
    TemplateAxisCounting.templateMemoryTreeAt, HonestCommitment.Data.executionTemplate,
    dataD, memoryNodesD, nN1, nN2, nN3, nN4, nN5, nN6, nN7, nN8, nN9, nN10, nN11, nN12,
    nN13, nN14, nN15, nN16, nN17, nN18, nN19, nN20, nN21, memNode, memStamp,
    mapNTree, HonestCommitment.renderMemoryTemplate, HonestCommitment.renderMemoryRow,
    HonestCommitment.renderMemoryPub, HonestCommitment.renderMemoryMemRec,
    TemplateAxisCounting.templateAxisTree, memoryMemRecKind,
    skelN1, skelN2, skelN3, skelN4, skelN5, skelN6, skelN7, skelN8, skelN9, skelN10,
    skelN11, skelN12, skelN13, skelN14, skelN15, skelN16, skelN17, skelN18, skelN19,
    skelN20, skelN21, readSkel, verifySkel, decSkel, haltSkel,
    recFSkel, recTSkel, recLSkel, recRSkel]

theorem alphaFreeRootD_cases
    (i : Fin (HonestCommitment.configTemplateOf (distinctCensusExecution hfirstD) seedD).kMem) :
    ProductionAxisStructureVerifier.alphaFreeRoot (templateD hfirstD) i = treeD := by
  match i with
  | ⟨0, h⟩ => exact alphaFreeRootD_zero hfirstD h
  | ⟨n + 1, h⟩ =>
      exact absurd (show n + 1 < 1 from by rw [kMemD] at h; exact h) (by omega)

theorem readExps_treeD : AxisBridge.readExps treeD = [1, 2, 3, 4] := by
  simp [treeD, AxisBridge.readExps]

theorem verifyExps_treeD : AxisBridge.verifyExps treeD = [1, 2, 3, 4] := by
  simp [treeD, AxisBridge.verifyExps]

theorem readVerifyNested_treeD : AxisBridge.ReadVerifyNested treeD := by
  simp [treeD, AxisBridge.ReadVerifyNested, AxisBatching.MTree.verifyCount]

theorem forestReadExpsD :
    TemplateAxisCounting.templateForestReadExps (templateD hfirstD) = [1, 2, 3, 4] := by
  rw [TemplateAxisCounting.templateForestReadExps]
  have h0 := alphaFreeRootD_zero hfirstD (by rw [kMemD]; norm_num)
  rw [ProductionAxisStructureVerifier.alphaFreeRoot] at h0
  rw [show (List.finRange (HonestCommitment.configTemplateOf (distinctCensusExecution hfirstD) seedD).kMem)
      = [⟨0, by rw [kMemD]; norm_num⟩] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, h0]
  rw [readExps_treeD hfirstD]

theorem forestVerifyExpsD :
    TemplateAxisCounting.templateForestVerifyExps (templateD hfirstD) = [1, 2, 3, 4] := by
  rw [TemplateAxisCounting.templateForestVerifyExps]
  have h0 := alphaFreeRootD_zero hfirstD (by rw [kMemD]; norm_num)
  rw [ProductionAxisStructureVerifier.alphaFreeRoot] at h0
  rw [show (List.finRange (HonestCommitment.configTemplateOf (distinctCensusExecution hfirstD) seedD).kMem)
      = [⟨0, by rw [kMemD]; norm_num⟩] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, h0]
  rw [verifyExps_treeD hfirstD]

theorem KszD : (HonestCommitment.configTemplateOf (distinctCensusExecution hfirstD) seedD).Ksz = 4 := rfl

theorem alphaFreeAxisStructureD :
    ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck (templateD hfirstD) = true := by
  apply (ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck_eq_true_iff (templateD hfirstD)).2
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [alphaFreeRootD_cases hfirstD i]
    exact readVerifyNested_treeD hfirstD
  · intro i
    rw [alphaFreeRootD_cases hfirstD i, readExps_treeD hfirstD]
    decide
  · rw [KszD hfirstD, forestReadExpsD hfirstD, forestVerifyExpsD hfirstD, IO.LmIO_iff]
    refine ⟨by norm_num [IO.InRange], by norm_num, by decide, by decide⟩

theorem noWrapD :
    ProductionAxisStructureVerifier.noWrapCheck (templateD hfirstD) alphaD = true := by
  apply (ProductionAxisStructureVerifier.noWrapCheck_eq_true_iff (templateD hfirstD) alphaD).2
  intro i e he
  rw [alphaD, fixtureAlpha_order]
  rw [alphaFreeRootD_cases hfirstD i, readExps_treeD hfirstD] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> norm_num

theorem structuralChecksH :
    ProductionAxisStructureVerifier.structuralChecksAt (verifierH hfirstD) seedD seedH_ne
      alphaD = true := by
  change
    (ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck (templateD hfirstD) &&
      ProductionAxisStructureVerifier.noWrapCheck (templateD hfirstD) alphaD) = true
  simp [alphaFreeAxisStructureD hfirstD, noWrapD hfirstD]

/-- The identically-zero root polynomial of the served forest. -/
theorem countsP_execD_zero (i : Fin cfgD.kMem) :
    countsP_bin (exactAxisTree cfgD execDA i) = 0 :=
  rootPolynomial_of_exactMemoryAxisValidity
    (distinctCensusExecution hfirstD).two_ne_zero
    (servedMemoryTraceD hfirstD).axisStructural (servedMemoryTraceD hfirstD).axisValidity
    (servedMemoryTraceD hfirstD).support i

omit hfirstD in
/-- Completeness substrate is `countsP_bin`. Dummy-wired after form R (MultiRoot precedent). -/
theorem countsP_treeD
    (h : AxisBatching.MTree.countsP_bin treeD = (0 : K97cubic[X])) :
    AxisBatching.MTree.countsP_bin treeD = (0 : K97cubic[X]) :=
  h

/-! ## H. The constructed package that accepts -/

def residualHonestD : BuildablePackage.CommitmentResidual (distinctCensusExecution hfirstD) :=
  HonestCommitment.commitmentResidualOf (dataD hfirstD) (alphaMCommitmentD hfirstD) (walkArraysD hfirstD)

theorem residualHonestD_generated :
    GeneratedField.ClaimGenerated K97cubic (residualHonestD hfirstD).verifier.raw.claim
      (residualHonestD hfirstD).Λ :=
  DistinctCensusCommitment.residualD_generated hfirstD

def packageH :
    OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F97 K97cubic 5 :=
  BuildablePackage.buildFullPackage (distinctCensusExecution hfirstD) (inputsD hfirstD) (residualHonestD hfirstD)
    (inputsD_challenges hfirstD) DistinctCensusC1.pairedRecordLayout_distinctCensus
    (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD) (by
      change 1 ≤ 1; trivial))
    (hord := fun _ => by
      have hα : (inputsD hfirstD).computeWalkAlpha = (2 : K97cubic) := rfl
      have hrows : (distinctCensusExecution hfirstD).cfg.compRows = 3 := rfl
      rw [hα, Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete.omega2_order, hrows]
      norm_num)
    (hordM := walkOrderMemD hfirstD)
    (hrows := DistinctCensusCommitment.rowsBoundD hfirstD)
    (hgenF := residualHonestD_generated hfirstD) (hF := DistinctCensusCommitment.f97_primeFieldD)

theorem statementH
    (hax : FormRAxisBound (packageH hfirstD).optimized.sampled (packageH hfirstD).optimized.basis)
    (hbasis : FormRBasis (packageH hfirstD).optimized.basis)
    (hwidth : FormRWidth F97) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageH hfirstD) :=
  BuildablePackage.universalOptimizedFullStrictThm54 (distinctCensusExecution hfirstD) (inputsD hfirstD)
    (residualHonestD hfirstD) (inputsD_challenges hfirstD) DistinctCensusC1.pairedRecordLayout_distinctCensus
    (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD) (by
      change 1 ≤ 1; trivial))
    (hord := fun _ => by
      have hα : (inputsD hfirstD).computeWalkAlpha = (2 : K97cubic) := rfl
      have hrows : (distinctCensusExecution hfirstD).cfg.compRows = 3 := rfl
      rw [hα, Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete.omega2_order, hrows]
      norm_num)
    (hordM := walkOrderMemD hfirstD)
    (hrows := DistinctCensusCommitment.rowsBoundD hfirstD)
    (hgenF := residualHonestD_generated hfirstD) (hF := DistinctCensusCommitment.f97_primeFieldD)
    hax hbasis hwidth

/-- Relaxis remaining: committed-template `RootAxisBoundaryAt` is the 2-adic substrate. -/
theorem rootAxisBoundaryH
    (hrootAt : (packageH hfirstD).strategy.RootAxisBoundaryAt
      (nprSeed coinH) seedH_ne (alphaM coinH)) :
    (packageH hfirstD).strategy.RootAxisBoundaryAt
      (nprSeed coinH) seedH_ne (alphaM coinH) :=
  hrootAt

theorem packageH_verifier : (packageH hfirstD).strategy.verifier = (verifierH hfirstD) := rfl

theorem packageH_seed : (packageH hfirstD).honestSeed = seedD := rfl

/-- **The constructed package's strategy accepts the honest coin at seed `8`.**
Quantifier: one package, one specialized later-round message, one coin.
`hrootAt` is the Relaxis remaining join (form R `countsP_bin`). -/
theorem packageH_accepts
    (hrootAt : (packageH hfirstD).strategy.RootAxisBoundaryAt
      (nprSeed coinH) seedH_ne (alphaM coinH)) :
    (packageH hfirstD).strategy.Accepts coinH cfgD.challenges.lam := by
  apply ((packageH hfirstD).strategy.accepts_iff coinH cfgD.challenges.lam seedH_ne).2
  constructor
  · apply (ProductionAxisStructureVerifier.accepts_iff (verifierH hfirstD) coinH cfgD.challenges.lam seedH_ne).2
    exact ⟨((verifierH hfirstD).accepts_iff_production coinH cfgD.challenges.lam seedH_ne).1 (verifierH_accepts_coinH hfirstD),
      structuralChecksH hfirstD⟩
  · exact hrootAt

/-! ## I. The honest coin lies outside the five counted failure events -/

theorem coinH_not_zeroSeedFailureEvent :
    coinH ∉ (zeroSeedFailureEvent : Finset (JointCoins K97cubic)) := by
  rw [mem_zeroSeedFailureEvent_iff]
  exact seedH_ne

theorem censusD_pair_mem (i : Fin censusD.census.count) :
    censusD.census.pair i ∈ op5Pairs := by
  have h : censusD.census.pair i ∈
      EdgeComparisonCensus.combinedSkeletonPairs K97cubic skelD :=
    List.get_mem _ _
  rwa [combinedPairsD] at h

/-- **Substantive collision exclusion.**  The consumed census has a genuinely distinct pair,
and that pair does not collide at seed `8`.  The unique collision
seed of this census is `-1`. -/
theorem coinH_not_collisionFailureEvent :
    coinH ∉ collisionFailureEvent censusD.census := by
  rw [mem_collisionFailureEvent_iff]
  rintro ⟨i, hi⟩
  have hmem := censusD_pair_mem hfirstD i
  rcases op5Pairs_dichotomy _ hmem with hself | hpair
  · apply hi
    rw [show nprSeed coinH = seedD from rfl, ← hself]
    exact sepSeed_self seedD _
  · rw [hpair] at hi
    exact hi operands_sepSeed

theorem baseH_binding :
    RawTopologyBindingResidual
      (acceptedFamilyDataD hfirstD seedD seedH_ne alphaD cfgD.challenges.lam).base := by
  have hc :
      (acceptedFamilyDataD hfirstD seedD seedH_ne alphaD cfgD.challenges.lam).base.exec.ComputeRowsAccepted := by
    change
      (specializedProblem (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).exec.ComputeRowsAccepted
    rw [specializedProblemD_honest hfirstD]
    exact compute_rows_acceptedD
  have hm :
      (acceptedFamilyDataD hfirstD seedD seedH_ne alphaD cfgD.challenges.lam).base.exec.MemoryRowsAccepted := by
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

theorem coinH_not_specializedTopologyFailureEvent :
    coinH ∉ specializedTopologyFailureEvent (verifierH hfirstD).raw cfgD.challenges.lam := by
  rw [mem_specializedTopologyFailureEvent_iff]
  rintro ⟨hz, hbad⟩
  change (0 : K97cubic) ∈
    topologyBadGammas (acceptedFamilyDataD hfirstD seedD seedH_ne alphaD cfgD.challenges.lam).base at hbad
  rw [topologyBadGammas_empty_of_binding _ (baseH_binding hfirstD)] at hbad
  exact absurd hbad (Finset.notMem_empty _)

theorem axis_eq_relaxis_of_usedD
    (root : Fin cfgD.kMem) (e : ℕ)
    (hread : e ∈ AxisBridge.readExps (exactAxisTree cfgD execDA root))
    (hverify : e ∈ AxisBridge.verifyExps (exactAxisTree cfgD execDA root)) :
    AxisBatching.MTree.vaxis e (exactAxisTree cfgD execDA root) =
      AxisBatching.MTree.Relaxis e (exactAxisTree cfgD execDA root) :=
  MemoryProductionAssignment.axis_eq_relaxis_of_used
    NonterminalServedRow.two_ne_zero_K97
    (buildableMemoryProductionAssignment (distinctCensusExecution hfirstD) (inputsD hfirstD)
      (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD) (by
      change 1 ≤ 1; trivial)))
    root e hread hverify

theorem axis_eq_relaxis_transportedD
    (X : ExactExecution cfgD) (hX : X = execDA)
    (i : Fin cfgD.kMem) (e : ℕ)
    (hread : e ∈ AxisBridge.readExps (exactAxisTree cfgD X i))
    (hverify : e ∈ AxisBridge.verifyExps (exactAxisTree cfgD X i)) :
    AxisBatching.MTree.vaxis e (exactAxisTree cfgD X i) =
      AxisBatching.MTree.Relaxis e (exactAxisTree cfgD X i) := by
  subst hX
  exact axis_eq_relaxis_of_usedD hfirstD i e hread hverify

theorem coinH_not_guardedAxisFailureEvent :
    coinH ∉ ProductionP8Containment.guardedAxisFailureEvent (packageH hfirstD).strategy
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

/-- OP_5 / OP_1 contribute no size-window nouns.  A size window is required exactly at the three
algorithm blocks that read a subformula evaluation's type -- `OP_3`, `OP_4` and `OP_6`, with the proof prose at the paper -- and
these rows are `OP_5`/`OP_1`.

Cite repair : this docstring carried the paper; `1707` is **blank** and `1712` is
the `OP_5` paragraph, so neither line supported the OP3/OP4/OP6 state set. -/
theorem sizeWindowNounsD :
    SizeWindowCounting.skeletonSizeWindowNouns skelD = [] := by
  rw [SizeWindowCounting.skeletonSizeWindowNouns, computeSkeletonRowsD]
  simp [SizeWindowCounting.requiredSizeWindowNouns, op5SkelD, op5Row, op1LSkelD, op1RSkelD,
    op1RowOf]

theorem coinH_not_sizeWindowFailure :
    coinH ∉ SizeWindowCounting.SizeWindowFailure skelD := by
  rw [SizeWindowCounting.mem_SizeWindowFailure_iff]
  rintro ⟨-, n, hn, _⟩
  rw [sizeWindowNounsD hfirstD] at hn
  exact List.not_mem_nil hn

theorem coinH_not_failureUnion :
    coinH ∉ ProductionP8Containment.FailureUnion (packageH hfirstD).strategy
      (packageH hfirstD).optimized.census cfgD.challenges.lam := by
  intro hbad
  simp only [ProductionP8Containment.FailureUnion, Finset.mem_union] at hbad
  rcases hbad with hbad | hbad
  · rcases hbad with hbad | hbad
    · rcases hbad with hbad | hbad
      · rcases hbad with hbad | hbad
        · exact coinH_not_zeroSeedFailureEvent hfirstD hbad
        · exact coinH_not_collisionFailureEvent hfirstD hbad
      · exact coinH_not_specializedTopologyFailureEvent hfirstD hbad
    · exact coinH_not_guardedAxisFailureEvent hfirstD hbad
  · exact coinH_not_sizeWindowFailure hfirstD hbad

/-! ## J. Genuine target, at a package that both has the distinct pair and accepts -/

theorem packageH_census_is_the_committed_census :
    (packageH hfirstD).optimized.commitment.skeleton = skelD ∧
      (packageH hfirstD).strategy.skeleton = skelD ∧
      (packageH hfirstD).optimized.census = censusD ∧
      (residualHonestD hfirstD).census = censusD ∧
      (dataD hfirstD).census = censusD :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem packageH_consumed_census_has_genuine_distinct_pair :
    ∃ i : Fin (packageH hfirstD).optimized.census.census.count,
      (packageH hfirstD).optimized.census.census.pair i =
          (operandLeft, operandRight) ∧
        ((packageH hfirstD).optimized.census.census.pair i).1 ≠
          ((packageH hfirstD).optimized.census.census.pair i).2 :=
  censusD_has_distinct_pair

variable (hrootAt : (packageH hfirstD).strategy.RootAxisBoundaryAt
  (nprSeed coinH) seedH_ne (alphaM coinH))
include hrootAt

/-- **The genuine target is reached at a constructed package whose consumed census contains
the distinct pair, and which accepts.**  Collision exclusion is discharged because that pair
does not collide at seed `8`. -/
theorem genuineTargetH :
    ProductionP8Containment.GenuineTargetAt (packageH hfirstD).strategy 97 7 coinH cfgD.challenges.lam :=
  (packageH hfirstD).containment coinH cfgD.challenges.lam (packageH_accepts hfirstD hrootAt) (coinH_not_failureUnion hfirstD)

theorem packageH_acceptance_nonempty :
    ∃ ω : JointCoins K97cubic, (packageH hfirstD).strategy.Accepts ω cfgD.challenges.lam :=
  ⟨coinH, packageH_accepts hfirstD hrootAt⟩

/-- The decisive combination: one constructed package both carries the genuine distinct pair
on the consumed census **and** accepts, and collision exclusion at that coin is the NPR
separation of `([7 9], [8 10])` at seed `8`. -/
theorem packageH_accepts_with_substantive_collision_exclusion :
    (packageH hfirstD).strategy.Accepts coinH cfgD.challenges.lam ∧
      (∃ i : Fin (packageH hfirstD).optimized.census.census.count,
        (packageH hfirstD).optimized.census.census.pair i = (operandLeft, operandRight) ∧
          ((packageH hfirstD).optimized.census.census.pair i).1 ≠
            ((packageH hfirstD).optimized.census.census.pair i).2) ∧
      nprSeed coinH = seedD ∧ seedD = (8 : K97cubic) ∧ seedD ≠ -1 ∧
      coinH ∉ collisionFailureEvent (packageH hfirstD).optimized.census.census ∧
      coinH ∉ ProductionP8Containment.FailureUnion (packageH hfirstD).strategy
        (packageH hfirstD).optimized.census cfgD.challenges.lam ∧
      ProductionP8Containment.GenuineTargetAt (packageH hfirstD).strategy 97 7 coinH cfgD.challenges.lam :=
  ⟨packageH_accepts hfirstD hrootAt, packageH_consumed_census_has_genuine_distinct_pair hfirstD,
    rfl, rfl, seedD_ne_neg_one, coinH_not_collisionFailureEvent hfirstD,
    coinH_not_failureUnion hfirstD, genuineTargetH hfirstD hrootAt⟩

/-! ## K. The arrays are the honest ones, not residual-of-zero -/

omit hrootAt in
theorem arraysD_multiplicity_ne_zero :
    ∀ j, (alphaMCommitmentD hfirstD seedD seedH_ne alphaD cfgD.challenges.lam).io.multiplicity j ≠ 0 :=
  fun _ => (honestAssignmentD hfirstD).exactIO.multiplicity_ne_zero _

theorem arraysD_ne_zeroAlphaM :
    (alphaMCommitmentD hfirstD seedD seedH_ne alphaD cfgD.challenges.lam).io.multiplicity ≠
      (HonestCommitment.zeroAlphaM (timestampD hfirstD) seedD seedH_ne alphaD cfgD.challenges.lam).io.multiplicity := by
  intro h
  have hpos :
      0 <
        (acceptedFamilyDataD hfirstD seedD seedH_ne alphaD cfgD.challenges.lam).base.exec.derivedResponseIO.length := by
    rw [acceptedFamilyD_response_length hfirstD seedD seedH_ne alphaD cfgD.challenges.lam]
    norm_num
  have hj := congrFun h ⟨0, hpos⟩
  exact arraysD_multiplicity_ne_zero hfirstD ⟨0, hpos⟩ hj

theorem residualHonestD_uses_honest_arrays :
    residualHonestD hfirstD =
      HonestCommitment.commitmentResidualOf (dataD hfirstD) (alphaMCommitmentD hfirstD) (walkArraysD hfirstD) := rfl

/-! ## L. Same-object receipts; `packageP` and `packageD` untouched -/

theorem packageH_regression :
    (packageH hfirstD).objects.cfg = cfgD ∧
      (packageH hfirstD).objects.exec = execD ∧
      (packageH hfirstD).computeChip.rap.w = 303 ∧ (packageH hfirstD).computeChip.rap.s = 418 ∧
      (packageH hfirstD).memoryChip.rap.w = 205 ∧ (packageH hfirstD).memoryChip.rap.s = 156 ∧
      (packageH hfirstD).computeChip.rap.H.card = 3 ∧
      (distinctCensusExecution hfirstD).cfg.compRows = 3 ∧
      (distinctCensusExecution hfirstD).cfg.memRows = 21 ∧
      (distinctCensusExecution hfirstD).cfg.kMem = 1 ∧
      (inputsD hfirstD).computeChallenges = default ∧
      (inputsD hfirstD).hOrb = 5 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · exact (BuildablePackage.constructed_resources (distinctCensusExecution hfirstD) (inputsD hfirstD)
      (residualHonestD hfirstD) (inputsD_challenges hfirstD) DistinctCensusC1.pairedRecordLayout_distinctCensus
      (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD) (by
      change 1 ≤ 1; trivial))
      (hord := fun _ => by
        have hα : (inputsD hfirstD).computeWalkAlpha = (2 : K97cubic) := rfl
        have hrows : (distinctCensusExecution hfirstD).cfg.compRows = 3 := rfl
        rw [hα, Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete.omega2_order, hrows]
        norm_num)
      (hordM := walkOrderMemD hfirstD)
    (hrows := DistinctCensusCommitment.rowsBoundD hfirstD)
    (hgenF := residualHonestD_generated hfirstD) (hF := DistinctCensusCommitment.f97_primeFieldD)).1
  · exact (BuildablePackage.constructed_resources (distinctCensusExecution hfirstD) (inputsD hfirstD)
      (residualHonestD hfirstD) (inputsD_challenges hfirstD) DistinctCensusC1.pairedRecordLayout_distinctCensus
      (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD) (by
      change 1 ≤ 1; trivial))
      (hord := fun _ => by
        have hα : (inputsD hfirstD).computeWalkAlpha = (2 : K97cubic) := rfl
        have hrows : (distinctCensusExecution hfirstD).cfg.compRows = 3 := rfl
        rw [hα, Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete.omega2_order, hrows]
        norm_num)
      (hordM := walkOrderMemD hfirstD)
    (hrows := DistinctCensusCommitment.rowsBoundD hfirstD)
    (hgenF := residualHonestD_generated hfirstD) (hF := DistinctCensusCommitment.f97_primeFieldD)).2.1
  · exact (BuildablePackage.constructed_resources (distinctCensusExecution hfirstD) (inputsD hfirstD)
      (residualHonestD hfirstD) (inputsD_challenges hfirstD) DistinctCensusC1.pairedRecordLayout_distinctCensus
      (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD) (by
      change 1 ≤ 1; trivial))
      (hord := fun _ => by
        have hα : (inputsD hfirstD).computeWalkAlpha = (2 : K97cubic) := rfl
        have hrows : (distinctCensusExecution hfirstD).cfg.compRows = 3 := rfl
        rw [hα, Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete.omega2_order, hrows]
        norm_num)
      (hordM := walkOrderMemD hfirstD)
    (hrows := DistinctCensusCommitment.rowsBoundD hfirstD)
    (hgenF := residualHonestD_generated hfirstD) (hF := DistinctCensusCommitment.f97_primeFieldD)).2.2.1
  · exact (BuildablePackage.constructed_resources (distinctCensusExecution hfirstD) (inputsD hfirstD)
      (residualHonestD hfirstD) (inputsD_challenges hfirstD) DistinctCensusC1.pairedRecordLayout_distinctCensus
      (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD) (by
      change 1 ≤ 1; trivial))
      (hord := fun _ => by
        have hα : (inputsD hfirstD).computeWalkAlpha = (2 : K97cubic) := rfl
        have hrows : (distinctCensusExecution hfirstD).cfg.compRows = 3 := rfl
        rw [hα, Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete.omega2_order, hrows]
        norm_num)
      (hordM := walkOrderMemD hfirstD)
    (hrows := DistinctCensusCommitment.rowsBoundD hfirstD)
    (hgenF := residualHonestD_generated hfirstD) (hF := DistinctCensusCommitment.f97_primeFieldD)).2.2.2
  · exact (BuildablePackage.constructed_row_budgets (distinctCensusExecution hfirstD) (inputsD hfirstD)
      (residualHonestD hfirstD) (inputsD_challenges hfirstD) DistinctCensusC1.pairedRecordLayout_distinctCensus
      (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD) (by
      change 1 ≤ 1; trivial))
      (hord := fun _ => by
        have hα : (inputsD hfirstD).computeWalkAlpha = (2 : K97cubic) := rfl
        have hrows : (distinctCensusExecution hfirstD).cfg.compRows = 3 := rfl
        rw [hα, Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete.omega2_order, hrows]
        norm_num)
      (hordM := walkOrderMemD hfirstD)
    (hrows := DistinctCensusCommitment.rowsBoundD hfirstD)
    (hgenF := residualHonestD_generated hfirstD) (hF := DistinctCensusCommitment.f97_primeFieldD)).1

end

end Nock.NockVMROM.Thm54.DistinctCensusHonestArrays

#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.specializedProblemD_honest
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.honestCompletionD_nonempty
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.alphaMCommitmentD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.walkArraysD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.coinH
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.claimD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.honestVerifierGatesD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.rawStrategyD_accepts_coinH
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.verifierH_accepts_coinH
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.alphaFreeRootD_zero
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.alphaFreeAxisStructureD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.noWrapD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.structuralChecksH
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.countsP_execD_zero
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.countsP_treeD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.rootAxisBoundaryH
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.residualHonestD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.packageH
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.statementH
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.packageH_accepts
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.coinH_not_collisionFailureEvent
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.coinH_not_failureUnion
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.genuineTargetH
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.packageH_accepts_with_substantive_collision_exclusion
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.packageH_consumed_census_has_genuine_distinct_pair
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.arraysD_ne_zeroAlphaM
#print axioms Nock.NockVMROM.Thm54.DistinctCensusHonestArrays.packageH_regression
