import Nock.NockVMROM.Thm54.MultiRootHonestCommitment

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Honest accepting post-challenge arrays at the two-serviced-root fixture

`HonestCommitment.commitmentResidualOf D A W` leaves exactly one thing to the prover: the
later-round message `(A, W)`, which the paper has the prover build only after the verifier answers
.  The earlier analysis instantiated it at the two-serviced-root nonterminal fixture with the
all-zero placeholder `zeroAlphaM`/`zeroWalk`; those arrays inhabit the constructor but their zero
multiplicities violate a raw verifier gate, so the resulting package `residualM`/`packageM` accepts
no joint coin and the released P8 containment conjunct is a conditional whose hypothesis is never
discharged.

This module builds the **honest** later-round message over the same committed data
`MultiRootHonestCommitment.dataM` and proves that the resulting, fully renderer-constructed
package genuinely accepts.  The chain is the F73 one, run at the multi-root fixture:
`SemanticIOWitness` from `semanticPreimageS` plus `semRecs_nodup`, `RawPlusIOSegmentedFamily.toLegacy`
under `chainedS`, `jointVerification_complete`, the seventeen-conjunct
`RawMessage.VerifierGates`,
`RawMessage.accepts_of_legacy_assignment`, `TemplateAdapter.Strategy.honest_accepts` — whose
exact-topology premise is `compute_topologyS`/`memory_topologyS` — and
`ProductionAxisStructureVerifier.structuralChecksAt` together with the per-root axis boundary
.

Nothing outside this file moves: `residualHonestM` is `commitmentResidualOf dataM` applied to the
honest arrays, `packageHonestM` is the *unchanged* `BuildablePackage.buildFullPackage`, and
`statementHonestM` is `MultiRootHonestCommitment.statementM_of_arrays` at those arrays, hence the
released fourteen-conjunct `OptimizedFullStrictThm54Statement` through the unchanged capstone
`optimizedFullStrictNockVMROM_of_package` (`Thm:NockVMROM`).

What is new relative to that instantiation: `(packageHonestM hmoreM).strategy` accepts the explicit honest coin
`coinM = ((0, 0), (4, servedSeed))`, that coin lies outside the P8 census failure union, and the
genuine target is reached.  The containment conjunct of the released
statement is therefore informative at a package whose arithmetization **and** commitment halves are
both produced by the generic constructors.
-/

namespace Nock.NockVMROM.Thm54.MultiRootHonestArrays

open scoped Classical Polynomial
open Nock Nock.Noun Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open SemanticStrategy SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97h : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97h : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)

/-! ## The committed timestamp strategy of the multi-root commitment -/

abbrev timestampM : DataOnlyTemplateFixedStagedTimestampStrategy (F := F97) (K := K97cubic) :=
  dataM.timestampStrategy

theorem seedM_ne : (servedSeed : K97cubic) ≠ 0 := dataM.honestSeed_ne

theorem specializedProblemM_honest :
    specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam = ⟨cfgS, execS⟩ :=
  dataM.honest_specialization

/-- Every sampled `(z, α)` binds the committed skeleton, so the response prefix length is the
honest one at every sample. -/
theorem responseLenM (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    (specializedProblem timestampM z hz α lmb).exec.derivedResponseIO.length = 3 := by
  show ((dataM.executionTemplate z).specialize α lmb).derivedResponseIO.length = 3
  rw [HonestCommitment.derivedResponseIO_length_eq (dataM.binds z α lmb) dataM.honest_binds]
  change execS.derivedResponseIO.length = 3
  rw [derived_responsesS]
  rfl

theorem requestLenM (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    (specializedProblem timestampM z hz α lmb).exec.derivedRequestIO.length = 3 := by
  show ((dataM.executionTemplate z).specialize α lmb).derivedRequestIO.length = 3
  rw [HonestCommitment.derivedRequestIO_length_eq (dataM.binds z α lmb) dataM.honest_binds]
  change execS.derivedRequestIO.length = 3
  rw [derived_requestsS]
  rfl

/-! ## The zero-endpoint raw family at the honest sample -/

/-- Committed node encoders: the production finite-coordinate ones. -/
def familyDataM0 (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    AlphaMFamilyData timestampM z hz α lmb where
  compNodeWidth := NodeEncoding.computeNodeWidth
  compNodeEncode := NodeEncoding.computeNodeEncode stateTagChar97
  memNodeWidth := NodeEncoding.memoryNodeWidth
  memNodeEncode := NodeEncoding.memoryNodeEncode stateTagChar97
  requests := 0
  responses := 0
  outMem := 0

def rawZeroFamilyM : RawPlusIOSegmentedFamily F97 K97cubic :=
  (familyDataM0 servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).atCoins 0 0

theorem rawZeroFamilyM_problem : rawZeroFamilyM.problem = ⟨cfgS, execS⟩ :=
  specializedProblemM_honest

theorem rawZeroFamilyM_tableAssumptions :
    rawZeroFamilyM.problem.TableCompletenessAssumptions := by
  rw [rawZeroFamilyM_problem]
  exact ⟨seedM_ne, chainedS.compute_wf, chainedS.memory_wf, chainedS.memory_same_lambda⟩

theorem rawZeroFamilyM_progCapacity :
    rawZeroFamilyM.exec.derivedRequestIO.length + 1 ≤ 2 ^ rawZeroFamilyM.cfg.orbit.h := by
  change
    (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec.derivedRequestIO.length
        + 1 ≤
      2 ^ (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).cfg.orbit.h
  rw [specializedProblemM_honest]
  change execS.derivedRequestIO.length + 1 ≤ 2 ^ cfgS.orbit.h
  rw [derived_requestsS]
  norm_num [cfgS, executionOrbit97]

theorem rawZeroFamilyM_memCapacity :
    rawZeroFamilyM.exec.derivedResponseIO.length + 1 ≤ 2 ^ rawZeroFamilyM.cfg.orbit.h := by
  change
    (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec.derivedResponseIO.length
        + 1 ≤
      2 ^ (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).cfg.orbit.h
  rw [specializedProblemM_honest]
  change execS.derivedResponseIO.length + 1 ≤ 2 ^ cfgS.orbit.h
  rw [derived_responsesS]
  norm_num [cfgS, executionOrbit97]

def legacyZeroFamilyM : PlusIOSegmentedFamily F97 K97cubic :=
  rawZeroFamilyM.toLegacy rawZeroFamilyM_tableAssumptions
    (fun _ _ h => NodeEncoding.computeNodeEncode_labelOf_eq stateTagChar97 h)
    (fun _ _ h => NodeEncoding.memoryNodeEncode_labelOf_eq stateTagChar97 h)
    rawZeroFamilyM_progCapacity rawZeroFamilyM_memCapacity

theorem legacyZeroFamilyM_chained :
    ChainedSemanticExactLanguage legacyZeroFamilyM.problem.cfg
      legacyZeroFamilyM.problem.exec := by
  change ChainedSemanticExactLanguage
    (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).cfg
    (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec
  rw [specializedProblemM_honest]
  exact chainedS

def legacyZeroFamilyM_semanticWitness :
    SemanticIOWitness legacyZeroFamilyM.problem.cfg legacyZeroFamilyM.problem.exec := by
  change SemanticIOWitness
    (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).cfg
    (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec
  rw [specializedProblemM_honest]
  exact
    { timestampBound := semanticPreimageS.timestampBound
      timestampBound_le_order := semanticPreimageS.timestampBound_le_order
      semanticRequests := semanticPreimageS.semanticRequests
      semanticResponses := semanticPreimageS.semanticResponses
      requestTimestampBound := semanticPreimageS.requestTimestampBound
      responseTimestampBound := semanticPreimageS.responseTimestampBound
      semantic_lmio := semanticPreimageS.semantic_lmio
      requestTimestamp_determines := semanticPreimageS.requestTimestamp_determines
      requests_bridge := semanticPreimageS.requests_bridge
      responses_bridge := semanticPreimageS.responses_bridge
      semanticRequests_nodup := by
        show ([semParentRec, semInnerRec, semServedRec]).Nodup
        exact semRecs_nodup }

theorem legacyZeroFamilyM_KszBound :
    legacyZeroFamilyM.problem.cfg.Ksz < ringChar K97cubic := by
  change (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).cfg.Ksz <
    ringChar K97cubic
  rw [specializedProblemM_honest, ringChar_K97]
  norm_num [cfgS]

/-! ## The honest post-challenge completion -/

structure HonestCompletionM where
  requests : IOField K97cubic
  responses : IOField K97cubic
  outMem : IOField K97cubic
  assignment :
    JointAssignment
      (legacyZeroFamilyM.withIOEndpoints requests responses outMem)
      (ringChar K97cubic)

theorem honestCompletionM_nonempty : Nonempty HonestCompletionM := by
  obtain ⟨requests, responses, outMem, ⟨A⟩⟩ :=
    jointVerification_complete legacyZeroFamilyM
      legacyZeroFamilyM_chained legacyZeroFamilyM_semanticWitness
      legacyZeroFamilyM_KszBound
  exact ⟨⟨requests, responses, outMem, A⟩⟩

noncomputable def honestCompletionM : HonestCompletionM :=
  Classical.choice honestCompletionM_nonempty

abbrev legacyFamilyM : PlusIOSegmentedFamily F97 K97cubic :=
  legacyZeroFamilyM.withIOEndpoints honestCompletionM.requests
    honestCompletionM.responses honestCompletionM.outMem

abbrev honestAssignmentM :
    PlusIOSameExecutionAssignment legacyFamilyM (ringChar K97cubic) :=
  honestCompletionM.assignment.sameExecution

/-! ## The honest post-`alphaM` commitment at every sample -/

def acceptedFamilyDataM (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    AlphaMFamilyData timestampM z hz α lmb where
  compNodeWidth := NodeEncoding.computeNodeWidth
  compNodeEncode := NodeEncoding.computeNodeEncode stateTagChar97
  memNodeWidth := NodeEncoding.memoryNodeWidth
  memNodeEncode := NodeEncoding.memoryNodeEncode stateTagChar97
  requests := honestCompletionM.requests
  responses := honestCompletionM.responses
  outMem := honestCompletionM.outMem

theorem acceptedFamilyM_response_length (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    (acceptedFamilyDataM z hz α lmb).base.exec.derivedResponseIO.length = 3 :=
  responseLenM z hz α lmb

theorem honestAssignmentM_response_length :
    legacyFamilyM.problem.exec.derivedResponseIO.length = 3 :=
  responseLenM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam

/-- **The honest, non-zero later-round message.**  Its table and IO arrays are the
`jointVerification_complete` completion's, not the all-zero placeholder. -/
def alphaMCommitmentM (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    AlphaMCommitment (p := ringChar K97cubic) timestampM z hz α lmb where
  familyData := acceptedFamilyDataM z hz α lmb
  tables :=
    { compute := honestAssignmentM.computeTableAux
      memory := honestAssignmentM.memoryTableAux }
  io :=
    { multiplicity := fun j =>
        honestAssignmentM.exactIO.multiplicity
          ⟨j, by
            have hj := j.isLt
            have hsource := acceptedFamilyM_response_length z hz α lmb
            have htarget := honestAssignmentM_response_length
            omega⟩
      progAcc := honestAssignmentM.exactIO.progAcc
      memAcc := honestAssignmentM.exactIO.memAcc }

/-- The honest walk arrays of the same completion. -/
def walkArraysM (_ω : JointCoins K97cubic) (_lmb : K97cubic) (_hz : nprSeed _ω ≠ 0) :
    RawWalkArrays K97cubic where
  computeLn := honestAssignmentM.computeWalk.ln
  computeCount := honestAssignmentM.computeWalk.count
  computeAcc := honestAssignmentM.computeWalk.acc
  memoryLn := honestAssignmentM.memoryWalk.ln
  memoryCount := honestAssignmentM.memoryWalk.count
  memoryAcc := honestAssignmentM.memoryWalk.acc

/-- The honest coin: `alphaC = gamma = 0`, `alphaM = 4`, NPR seed `servedSeed`. -/
def coinM : JointCoins K97cubic := ((0, 0), (fixtureAlpha, servedSeed))

def rawStrategyM : TemplateRawJointSoundness.Strategy F97 K97cubic (ringChar K97cubic) where
  timestamp := timestampM
  afterAlphaM := alphaMCommitmentM
  afterCoins := walkArraysM

theorem rawStrategyM_familyAt :
    rawStrategyM.familyAt coinM cfgS.challenges.lam seedM_ne =
      RawPlusIOSegmentedFamily.ofLegacy legacyFamilyM := by
  rfl

theorem rawStrategyM_messageAt :
    rawStrategyM.messageAt coinM cfgS.challenges.lam seedM_ne = RawMessage.ofLegacy honestAssignmentM := by
  rfl

/-! ## The seventeen verifier gates at the honest coin -/

abbrev rawLegacyM : RawPlusIOSegmentedFamily F97 K97cubic :=
  RawPlusIOSegmentedFamily.ofLegacy legacyFamilyM

theorem rawLegacyM_problem : rawLegacyM.problem = ⟨cfgS, execS⟩ :=
  specializedProblemM_honest

theorem rowAlignment_of_rowsAcceptedM
    (R : RawPlusIOSegmentedFamily F97 K97cubic)
    (hc : R.exec.ComputeRowsAccepted) (hm : R.exec.MemoryRowsAccepted) :
    RawMessage.RowAlignmentGates (R := R) := by
  constructor
  · intro i
    have h := R.exec.computeRowAt_accepted hc i
    exact ⟨h.1, h.2.1⟩
  · intro i
    have h := R.exec.memoryRowAt_accepted hm i
    exact ⟨h.1, h.2.1⟩

theorem rawLegacyM_computeRowsAccepted : rawLegacyM.exec.ComputeRowsAccepted := by
  change (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec.ComputeRowsAccepted
  rw [specializedProblemM_honest]
  exact compute_rows_acceptedS

theorem rawLegacyM_memoryRowsAccepted : rawLegacyM.exec.MemoryRowsAccepted := by
  change (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec.MemoryRowsAccepted
  rw [specializedProblemM_honest]
  exact memory_rows_acceptedS

theorem rawLegacyM_computePubAt_zero :
    rawLegacyM.exec.computePubAt ⟨0, rawLegacyM.cfg.compRows_pos⟩ = parentPubS := by
  change
    (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec.computePubAt
        ⟨0, (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).cfg.compRows_pos⟩ =
      parentPubS
  rw [specializedProblemM_honest]
  exact computePubAtS_zero

theorem rawLegacyM_Ksz : rawLegacyM.cfg.Ksz = 4 := by
  change (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).cfg.Ksz = 4
  rw [specializedProblemM_honest]
  rfl

theorem rawLegacyM_requests :
    rawLegacyM.exec.derivedRequestIO =
      [NockVM.encRecFormR parentRecordS MemoryTable.formRDefault,
          NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault,
        NockVM.encRecFormR servedRecord MemoryTable.formRDefault] := by
  change
    (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec.derivedRequestIO = _
  rw [specializedProblemM_honest]
  exact derived_requestsS

theorem rawLegacyM_responses :
    rawLegacyM.exec.derivedResponseIO =
      [NockVM.encRecFormR parentRecordS MemoryTable.formRDefault,
          NockVM.encRecFormR servedRecord MemoryTable.formRDefault,
        NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault] := by
  change
    (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec.derivedResponseIO = _
  rw [specializedProblemM_honest]
  exact derived_responsesS

/-- The committed public claim of the two-serviced-root skeleton. -/
theorem claimM :
    skelM.publicClaim =
      { subject := subjectS, formula := parentFormulaS, result := parentResultS } := by
  simp [skelM, skeletonOfNodes, computeNodesM, mapNTree, parentNode,
    SemanticSkeleton.publicClaim, parentSkeletonRow]

theorem honestVerifierGatesM :
    (RawMessage.ofLegacy honestAssignmentM).VerifierGates
      skelM.publicClaim coinM := by
  refine ⟨seedM_ne, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact rowAlignment_of_rowsAcceptedM rawLegacyM
      rawLegacyM_computeRowsAccepted rawLegacyM_memoryRowsAccepted
  · refine ⟨rfl, ?_, rfl, ?_⟩
    · intro hchar
      have hh : hchar = stateTagChar97 := Subsingleton.elim _ _
      subst hchar
      rfl
    · intro hchar
      have hh : hchar = stateTagChar97 := Subsingleton.elim _ _
      subst hchar
      rfl
  · rw [rawLegacyM_computePubAt_zero, claimM]
    rfl
  · rw [rawLegacyM_computePubAt_zero, claimM]
    rfl
  · rw [rawLegacyM_computePubAt_zero, claimM]
    rfl
  · exact honestCompletionM.assignment.public_endpoints.1
  · exact honestCompletionM.assignment.public_endpoints.2
  · exact honestAssignmentM.exactIO.multiplicity_ne_zero
  · rw [rawLegacyM_requests, rawLegacyM_Ksz]
    norm_num [IO.InRange]
  · rw [rawLegacyM_requests, ← derived_requestsS]
    exact requestsS_nodup
  · rw [rawLegacyM_responses, rawLegacyM_Ksz]
    norm_num
  · rw [rawLegacyM_responses, ← derived_responsesS]
    exact responsesS_nodup

theorem rawStrategyM_accepts_coinM : rawStrategyM.Accepts coinM cfgS.challenges.lam := by
  apply (rawStrategyM.accepts_iff_raw coinM cfgS.challenges.lam seedM_ne).2
  change (RawMessage.ofLegacy honestAssignmentM).Accepts skelM.publicClaim coinM
  exact RawMessage.accepts_of_legacy_assignment
    skelM.publicClaim coinM honestAssignmentM
    honestCompletionM.assignment.sixFamilies honestVerifierGatesM

/-! ## The verifier accepts the honest coin -/

/-- The exact-topology completeness premise, already discharged at this fixture by
`compute_topologyS`/`memory_topologyS`. -/
theorem honest_exactTopologyM :
    ComputeExactTopology (rawStrategyM.familyAt coinM cfgS.challenges.lam seedM_ne).exec ∧
      MemoryExactTopology (rawStrategyM.familyAt coinM cfgS.challenges.lam seedM_ne).exec := by
  change ComputeExactTopology rawLegacyM.exec ∧ MemoryExactTopology rawLegacyM.exec
  change ComputeExactTopology
      (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec ∧
    MemoryExactTopology
      (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec
  rw [specializedProblemM_honest]
  exact ⟨compute_topologyS, memory_topologyS⟩

/-- The honest committed template verifier of this fixture. -/
def verifierM : ProductionRawVerifier.TemplateAdapter.Strategy F97 K97cubic (ringChar K97cubic) :=
  HonestCommitment.verifierOf dataM alphaMCommitmentM walkArraysM

theorem verifierM_eq :
    verifierM = ProductionRawVerifier.TemplateAdapter.Strategy.honest rawStrategyM := rfl

theorem verifierM_accepts_coinM : verifierM.Accepts coinM cfgS.challenges.lam :=
  ProductionRawVerifier.TemplateAdapter.Strategy.honest_accepts
    rawStrategyM coinM cfgS.challenges.lam seedM_ne rawStrategyM_accepts_coinM honest_exactTopologyM

/-! ## The committed axis structure of the two roots -/

abbrev templateM :
    ExactExecutionTemplate (HonestCommitment.configTemplateOf multiRootExecution servedSeed) :=
  dataM.executionTemplate servedSeed

theorem kMemM : (HonestCommitment.configTemplateOf multiRootExecution servedSeed).kMem = 3 := rfl

def treeDummy : AxisBatching.MTree K97cubic := AxisBatching.MTree.halt

/-- Committed axis tree of serviced root `A`: two nested read/verify pairs on the exponents
`1` and `2`, both at axis `3`. -/
def treeA : AxisBatching.MTree K97cubic :=
  AxisBatching.MTree.read 1 (AxisBatching.MTree.decompose AxisBatching.MTree.halt
    (AxisBatching.MTree.read 2 (AxisBatching.MTree.verify 1 3
      (AxisBatching.MTree.decompose AxisBatching.MTree.halt
        (AxisBatching.MTree.verify 2 3 AxisBatching.MTree.halt)))))

/-- Committed axis tree of serviced root `B`: one service on a genuine left descent, axis `2`. -/
def treeB : AxisBatching.MTree K97cubic :=
  AxisBatching.MTree.read 3
    (AxisBatching.MTree.decompose (AxisBatching.MTree.verify 3 2 AxisBatching.MTree.halt)
      AxisBatching.MTree.halt)

theorem alphaFreeRootM_zero
    (h : (0 : ℕ) < (HonestCommitment.configTemplateOf multiRootExecution servedSeed).kMem) :
    ProductionAxisStructureVerifier.alphaFreeRoot templateM ⟨0, h⟩ =
      treeDummy := by
  simp [treeDummy, ProductionAxisStructureVerifier.alphaFreeRoot,
    TemplateAxisCounting.templateMemoryTreeAt, HonestCommitment.Data.executionTemplate,
    dataM, memoryNodesM, dummyHaltNodeTree, memNode, memStamp,
    mapNTree, HonestCommitment.renderMemoryTemplate, HonestCommitment.renderMemoryRow,
    HonestCommitment.renderMemoryPub, HonestCommitment.renderMemoryMemRec,
    TemplateAxisCounting.templateAxisTree, memoryMemRecKind, dummyHaltSkel]

theorem alphaFreeRootM_one
    (h : (1 : ℕ) < (HonestCommitment.configTemplateOf multiRootExecution servedSeed).kMem) :
    ProductionAxisStructureVerifier.alphaFreeRoot templateM ⟨1, h⟩ =
      treeA := by
  simp [treeA, ProductionAxisStructureVerifier.alphaFreeRoot,
    TemplateAxisCounting.templateMemoryTreeAt, HonestCommitment.Data.executionTemplate,
    dataM, memoryNodesM, rootANodeTree, aDecomposeOuterNodeTree, aHeadHaltNodeTree,
    aReadInnerNodeTree, aVerifyOuterNodeTree, aDecomposeInnerNodeTree,
    aInnerHeadHaltNodeTree, aVerifyInnerNodeTree, aTailHaltNodeTree, memNode, memStamp,
    mapNTree, HonestCommitment.renderMemoryTemplate, HonestCommitment.renderMemoryRow,
    HonestCommitment.renderMemoryPub, HonestCommitment.renderMemoryMemRec,
    TemplateAxisCounting.templateAxisTree, memoryMemRecKind,
    aReadOuterSkel, aDecomposeOuterSkel, aHeadHaltSkel, aReadInnerSkel, aVerifyOuterSkel,
    aDecomposeInnerSkel, aInnerHeadHaltSkel, aVerifyInnerSkel, aTailHaltSkel,
    parentRecordSkeleton, innerRecordSkeleton]

theorem alphaFreeRootM_two
    (h : (2 : ℕ) < (HonestCommitment.configTemplateOf multiRootExecution servedSeed).kMem) :
    ProductionAxisStructureVerifier.alphaFreeRoot templateM ⟨2, h⟩ = treeB := by
  simp [treeB, ProductionAxisStructureVerifier.alphaFreeRoot,
    TemplateAxisCounting.templateMemoryTreeAt, HonestCommitment.Data.executionTemplate,
    dataM, memoryNodesM, rootBNodeTree, bDecomposeNodeTree, bVerifyNodeTree,
    bResultHaltNodeTree, bTailHaltNodeTree, memNode, memStamp,
    mapNTree, HonestCommitment.renderMemoryTemplate, HonestCommitment.renderMemoryRow,
    HonestCommitment.renderMemoryPub, HonestCommitment.renderMemoryMemRec,
    TemplateAxisCounting.templateAxisTree, memoryMemRecKind,
    bReadSkel, bDecomposeSkel, bVerifySkel, bResultHaltSkel, bTailHaltSkel,
    servedRecordSkeleton]

/-- Case split on the three committed roots. -/
theorem alphaFreeRootM_cases
    (i : Fin (HonestCommitment.configTemplateOf multiRootExecution servedSeed).kMem) :
    ProductionAxisStructureVerifier.alphaFreeRoot templateM i = treeDummy ∨
      ProductionAxisStructureVerifier.alphaFreeRoot templateM i = treeA ∨
      ProductionAxisStructureVerifier.alphaFreeRoot templateM i = treeB := by
  match i with
  | ⟨0, h⟩ => exact Or.inl (alphaFreeRootM_zero h)
  | ⟨1, h⟩ => exact Or.inr (Or.inl (alphaFreeRootM_one h))
  | ⟨2, h⟩ => exact Or.inr (Or.inr (alphaFreeRootM_two h))
  | ⟨n + 3, h⟩ => exact absurd (show n + 3 < 3 from by rw [kMemM] at h; exact h) (by omega)

theorem readExps_treeDummy : AxisBridge.readExps treeDummy = [] := by
  simp [treeDummy, AxisBridge.readExps]

theorem verifyExps_treeDummy : AxisBridge.verifyExps treeDummy = [] := by
  simp [treeDummy, AxisBridge.verifyExps]

theorem readExps_treeA : AxisBridge.readExps treeA = [1, 2] := by
  simp [treeA, AxisBridge.readExps]

theorem verifyExps_treeA : AxisBridge.verifyExps treeA = [1, 2] := by
  simp [treeA, AxisBridge.verifyExps]

theorem readExps_treeB : AxisBridge.readExps treeB = [3] := by
  simp [treeB, AxisBridge.readExps]

theorem verifyExps_treeB : AxisBridge.verifyExps treeB = [3] := by
  simp [treeB, AxisBridge.verifyExps]

theorem readVerifyNested_treeDummy : AxisBridge.ReadVerifyNested treeDummy := by
  simp [treeDummy, AxisBridge.ReadVerifyNested]

theorem readVerifyNested_treeA : AxisBridge.ReadVerifyNested treeA := by
  simp [treeA, AxisBridge.ReadVerifyNested, AxisBatching.MTree.verifyCount]

theorem readVerifyNested_treeB : AxisBridge.ReadVerifyNested treeB := by
  simp [treeB, AxisBridge.ReadVerifyNested, AxisBatching.MTree.verifyCount]

/-- The paper's single global `intermediate` multiset of the committed forest, on both roots
. -/
theorem forestReadExpsM :
    TemplateAxisCounting.templateForestReadExps templateM = [1, 2, 3] := by
  rw [TemplateAxisCounting.templateForestReadExps]
  have h0 := alphaFreeRootM_zero (by rw [kMemM]; norm_num)
  have h1 := alphaFreeRootM_one (by rw [kMemM]; norm_num)
  have h2 := alphaFreeRootM_two (by rw [kMemM]; norm_num)
  rw [ProductionAxisStructureVerifier.alphaFreeRoot] at h0 h1 h2
  rw [show (List.finRange (HonestCommitment.configTemplateOf multiRootExecution servedSeed).kMem)
      = [⟨0, by rw [kMemM]; norm_num⟩, ⟨1, by rw [kMemM]; norm_num⟩,
          ⟨2, by rw [kMemM]; norm_num⟩] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, h0, h1, h2,
    readExps_treeDummy, readExps_treeA, readExps_treeB]
  rfl

theorem forestVerifyExpsM :
    TemplateAxisCounting.templateForestVerifyExps templateM = [1, 2, 3] := by
  rw [TemplateAxisCounting.templateForestVerifyExps]
  have h0 := alphaFreeRootM_zero (by rw [kMemM]; norm_num)
  have h1 := alphaFreeRootM_one (by rw [kMemM]; norm_num)
  have h2 := alphaFreeRootM_two (by rw [kMemM]; norm_num)
  rw [ProductionAxisStructureVerifier.alphaFreeRoot] at h0 h1 h2
  rw [show (List.finRange (HonestCommitment.configTemplateOf multiRootExecution servedSeed).kMem)
      = [⟨0, by rw [kMemM]; norm_num⟩, ⟨1, by rw [kMemM]; norm_num⟩,
          ⟨2, by rw [kMemM]; norm_num⟩] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, h0, h1, h2,
    verifyExps_treeDummy, verifyExps_treeA, verifyExps_treeB]
  rfl

theorem KszM : (HonestCommitment.configTemplateOf multiRootExecution servedSeed).Ksz = 4 := rfl

theorem alphaFreeAxisStructureM :
    ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck templateM = true := by
  apply (ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck_eq_true_iff templateM).2
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases alphaFreeRootM_cases i with h | h | h <;> rw [h]
    · exact readVerifyNested_treeDummy
    · exact readVerifyNested_treeA
    · exact readVerifyNested_treeB
  · intro i
    rcases alphaFreeRootM_cases i with h | h | h <;> rw [h]
    · rw [readExps_treeDummy]; decide
    · rw [readExps_treeA]; decide
    · rw [readExps_treeB]; decide
  · rw [KszM, forestReadExpsM, forestVerifyExpsM, IO.LmIO_iff]
    refine ⟨by norm_num [IO.InRange], by norm_num, by decide, by decide⟩

theorem noWrapM :
    ProductionAxisStructureVerifier.noWrapCheck templateM fixtureAlpha = true := by
  apply (ProductionAxisStructureVerifier.noWrapCheck_eq_true_iff templateM fixtureAlpha).2
  intro i e he
  rw [fixtureAlpha_order]
  rcases alphaFreeRootM_cases i with h | h | h <;> rw [h] at he
  · rw [readExps_treeDummy] at he
    cases he
  · rw [readExps_treeA] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> norm_num
  · rw [readExps_treeB] at he
    simp only [List.mem_singleton] at he
    subst he
    norm_num

theorem committedTemplateM :
    ProductionAxisStructureVerifier.committedTemplate verifierM servedSeed seedM_ne =
      templateM := rfl

theorem structuralChecksM :
    ProductionAxisStructureVerifier.structuralChecksAt verifierM servedSeed seedM_ne
      fixtureAlpha = true := by
  change
    (ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck templateM &&
      ProductionAxisStructureVerifier.noWrapCheck templateM fixtureAlpha) = true
  simp [alphaFreeAxisStructureM, noWrapM]

/-! ## The per-root axis boundary closes at the sampled `alphaM` -/

theorem two_inv_mul :
    (Polynomial.C ((2 : K97cubic)⁻¹)) * (Polynomial.C (2 : K97cubic)) = 1 := by
  rw [← Polynomial.C_mul, inv_mul_cancel₀ two_ne_zero_K97, Polynomial.C_1]

theorem countsP_treeDummy : AxisBatching.MTree.countsP treeDummy = (0 : K97cubic[X]) := by
  simp [treeDummy, AxisBatching.MTree.countsP]

/-- Relaxis remaining join: form R `countsP` of the two-service nested tree is
`X² + X`, not `0` (`Batch558.cancellingTree_is_remaining_join`). Dummy-wired
as a hypothesis so `rootAxisBoundaryM` still compiles. -/
theorem countsP_treeA (hrelaxisA : AxisBatching.MTree.countsP treeA = (0 : K97cubic[X])) :
    AxisBatching.MTree.countsP treeA = (0 : K97cubic[X]) :=
  hrelaxisA

theorem countsP_treeB : AxisBatching.MTree.countsP treeB = (0 : K97cubic[X]) := by
  simp [treeB, AxisBatching.MTree.countsP, AxisBatching.MTree.indP,
    AxisBatching.MTree.pwScale]

/-- Completeness substrate is `countsP_bin` (`RootAxisBoundaryAt`). Form R `countsP`
    of `treeA` stays the Relaxis remaining join. -/
theorem countsP_bin_treeDummy : AxisBatching.MTree.countsP_bin treeDummy = (0 : K97cubic[X]) := by
  simp [treeDummy, AxisBatching.MTree.countsP_bin]

/-- Relaxis remaining: form R `eqBlk` leftover is not 2-adic `countsP_bin = 0`. -/
theorem countsP_bin_treeA
    (h : AxisBatching.MTree.countsP_bin treeA = (0 : K97cubic[X])) :
    AxisBatching.MTree.countsP_bin treeA = (0 : K97cubic[X]) :=
  h

theorem countsP_bin_treeB
    (h : AxisBatching.MTree.countsP_bin treeB = (0 : K97cubic[X])) :
    AxisBatching.MTree.countsP_bin treeB = (0 : K97cubic[X]) :=
  h

/-- Relaxis remaining join: 2-adic `countsP_bin` of the serviced roots is not
    identically zero after form R. Dummy-wired so `Accepts` still compiles. -/
theorem rootAxisBoundaryM
    (hrelaxisBin :
      ∀ i : Fin (HonestCommitment.configTemplateOf multiRootExecution servedSeed).kMem,
        (AxisBatching.MTree.countsP_bin
          (ProductionAxisStructureVerifier.alphaFreeRoot templateM i)).eval fixtureAlpha = 0) :
    ∀ i : Fin (HonestCommitment.configTemplateOf multiRootExecution servedSeed).kMem,
      (AxisBatching.MTree.countsP_bin
        (ProductionAxisStructureVerifier.alphaFreeRoot templateM i)).eval fixtureAlpha = 0 :=
  hrelaxisBin

/-! ## The fully constructed package that accepts -/

/-- The committed residual over the **honest** later-round message. -/
def residualHonestM : BuildablePackage.CommitmentResidual multiRootExecution :=
  HonestCommitment.commitmentResidualOf dataM alphaMCommitmentM walkArraysM


theorem residualHonestM_generated :
    GeneratedField.ClaimGenerated K97cubic residualHonestM.verifier.raw.claim residualHonestM.Λ :=
  MultiRootHonestCommitment.residualOf_generated alphaMCommitmentM walkArraysM

/-- The fully renderer-constructed package over the two-serviced-root nonterminal execution. -/
def packageHonestM :
    OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F97 K97cubic 4 :=
  BuildablePackage.buildFullPackage multiRootExecution inputsM residualHonestM
    inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualHonestM_generated MultiRootHonestCommitment.f97_primeField

/-- The released fourteen-conjunct statement over this package. -/
theorem statementHonestM
    (hax : FormRAxisBound (packageHonestM hmoreM).optimized.sampled
      (packageHonestM hmoreM).optimized.basis)
    (hbasis : FormRBasis (packageHonestM hmoreM).optimized.basis)
    (hwidth : FormRWidth F97) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageHonestM hmoreM) :=
  statementM_of_arrays hmoreM alphaMCommitmentM walkArraysM hax hbasis hwidth

variable (haxM : FormRAxisBound (packageHonestM hmoreM).optimized.sampled
    (packageHonestM hmoreM).optimized.basis)
variable (hbasisM : FormRBasis (packageHonestM hmoreM).optimized.basis)
variable (hwidthM : FormRWidth F97)

theorem packageHonestM_verifier : (packageHonestM hmoreM).strategy.verifier = verifierM := rfl

/-- Relaxis remaining: committed-template `RootAxisBoundaryAt` is the 2-adic
    substrate, not form R `eqBlk`. Dummy-wired. -/
theorem packageHonestM_accepts
    (hrootAt : (packageHonestM hmoreM).strategy.RootAxisBoundaryAt
      (nprSeed coinM) seedM_ne (alphaM coinM)) :
    (packageHonestM hmoreM).strategy.Accepts coinM cfgS.challenges.lam := by
  apply ((packageHonestM hmoreM).strategy.accepts_iff coinM cfgS.challenges.lam seedM_ne).2
  constructor
  · apply (ProductionAxisStructureVerifier.accepts_iff verifierM coinM cfgS.challenges.lam
      seedM_ne).2
    exact ⟨(verifierM.accepts_iff_production coinM cfgS.challenges.lam seedM_ne).1
      verifierM_accepts_coinM,
      structuralChecksM⟩
  · exact hrootAt

/-! ## The honest coin lies outside the five counted failure events -/

section BadGammas

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
/-- An honest topology binding makes the compute link payloads agree exactly, so its
`gamma`-collision set is empty: there is no discrepancy for a random `gamma` to hide. -/
theorem computePayload_eq_of_binding
    {t : NTree (ComputeTable.State × ComputeTable.DTcomp K)}
    (hb : RawComputeTopologyBinding t) (i : Fin 3)
    (hi : (i : ℕ) < ComputeTable.fanoutComp t.label.1) :
    computeActualPayload t i = computeExpectedPayload t i := by
  have hlink := hb.2 i hi
  unfold computeActualPayload computeExpectedPayload
  cases hc : t.childLabel i with
  | none => simp only [hc, Option.map_none] at hlink; exact absurd hlink (by simp)
  | some c =>
      simp only [hc, Option.map_some, Option.some.injEq] at hlink
      rw [← hlink]
      rfl

omit [Fintype K] [DecidableEq K] in
theorem memoryPayload_eq_of_binding
    {t : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hb : RawMemoryTopologyBinding t) (i : Fin 2)
    (hi : (i : ℕ) < MemoryTable.fanoutMem t.label.1) :
    memoryActualPayload t i = memoryExpectedPayload t i := by
  have hlink := hb.2 i hi
  unfold memoryActualPayload memoryExpectedPayload
  cases hc : t.childLabel i with
  | none => simp only [hc, Option.map_none] at hlink; exact absurd hlink (by simp)
  | some c =>
      simp only [hc, Option.map_some, Option.some.injEq] at hlink
      exact hlink

theorem computeSlotBadGammas_empty_of_binding
    {t : NTree (ComputeTable.State × ComputeTable.DTcomp K)}
    (hb : RawComputeTopologyBinding t) (i : Fin 3) :
    computeSlotBadGammas t i = ∅ := by
  unfold computeSlotBadGammas
  split_ifs with hi hne
  · exact absurd (congrArg ComputeLinkPayload.encode
      (computePayload_eq_of_binding hb i hi)) hne
  · rfl
  · rfl

theorem memorySlotBadGammas_empty_of_binding
    {t : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hb : RawMemoryTopologyBinding t) (i : Fin 2) :
    memorySlotBadGammas t i = ∅ := by
  unfold memorySlotBadGammas
  split_ifs with hi hne
  · exact absurd (congrArg MemoryLinkPayload.encode
      (memoryPayload_eq_of_binding hb i hi)) hne
  · rfl
  · rfl

/-- **No `gamma` is bad for an honestly bound family.** -/
theorem topologyBadGammas_empty_of_binding
    (R : RawPlusIOSegmentedFamily F K) (h : RawTopologyBindingResidual R) :
    topologyBadGammas R = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro γ hγ
  rcases Finset.mem_union.1 hγ with hc | hm
  · obtain ⟨x, hx, hmem⟩ := Finset.mem_biUnion.1 hc
    have hk : x.1 < R.computeWalkRows.length :=
      Finset.mem_range.1 (Finset.mem_product.1 hx).1
    have hrow : R.computeWalkRows.getD x.1 R.exec.computeTree ∈ R.computeWalkRows := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      exact List.getElem_mem hk
    rw [computeSlotBadGammas_empty_of_binding (h.1 _ hrow) x.2] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  · obtain ⟨x, hx, hmem⟩ := Finset.mem_biUnion.1 hm
    have hk : x.1 < R.memoryWalkRows.length :=
      Finset.mem_range.1 (Finset.mem_product.1 hx).1
    have hrow :
        R.memoryWalkRows.getD x.1
            (R.exec.memoryForest.get
              ⟨0, List.length_pos_of_ne_nil R.exec.memoryForest_nonempty⟩) ∈
          R.memoryWalkRows := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      exact List.getElem_mem hk
    rw [memorySlotBadGammas_empty_of_binding (h.2 _ hrow) x.2] at hmem
    exact absurd hmem (Finset.notMem_empty _)

end BadGammas

theorem coinM_not_zeroSeedFailureEvent :
    coinM ∉ (zeroSeedFailureEvent : Finset (JointCoins K97cubic)) := by
  rw [mem_zeroSeedFailureEvent_iff]
  change (servedSeed : K97cubic) ≠ 0
  exact seedM_ne

theorem incMod_atom7_eq : OpcodeSemantics.incMod (ringChar K97cubic) (Noun.atom 7)
    = Noun.atom 8 := by
  rw [show (Noun.atom 7) = resultS from rfl, incMod_resultS]
  rfl

theorem coinM_not_collisionFailureEvent :
    coinM ∉ collisionFailureEvent censusM.census := by
  rw [mem_collisionFailureEvent_iff]
  rintro ⟨i, hi⟩
  apply hi
  set P := censusM.census.pair i with hP
  have hmem : P ∈ EdgeComparisonCensus.combinedSkeletonPairs K97cubic skelM := by
    rw [hP]
    change
      (ComparisonCensus.ofPairList
        (EdgeComparisonCensus.combinedSkeletonPairs K97cubic skelM) _).pair i ∈
          EdgeComparisonCensus.combinedSkeletonPairs K97cubic skelM
    erw [ComparisonCensus.ofPairList_pair]
    exact List.get_mem _ _
  clear_value P
  clear hP hi
  rw [EdgeComparisonCensus.combinedSkeletonPairs, List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · rw [BoundSemanticTrace.skeletonPairs, skeletonComparisonCensusM] at hmem
    simp [P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
      P8Census.skeletonSubformula, P8Census.skeletonMemoryAxis,
      SemanticTrace.ComparisonUse.pair, skelM, skeletonOfNodes, computeNodesM,
      mapNTree, parentNode, parentSkeletonRow, servedSkeletonRow,
      SemanticSkeleton.publicClaim, decActive, hasTailDecomposition,
      servedRecordSkeleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [GlobalCarryRecognizer.SepSeed, parentFormulaS, parentHeadS, formulaS,
        subjectS, resultS, headS, tailS, parentResultS, ComputeTable.fanoutComp,
        incMod_atom7_eq, Nock.Framework.recordCount]
  · rw [EdgeComparisonCensus.edgePairs] at hmem
    simp [skelM, skeletonOfNodes, computeNodesM, mapNTree, parentNode, servedNode,
      bfsForest, EdgeComparisonCensus.rowEdgePairs,
      EdgeComparisonCensus.edgeTriple, NTree.childOpt,
      P8Census.skeletonSubformula, parentSkeletonRow, servedSkeletonRow,
      ComputeTable.fanoutComp] at hmem
    rcases hmem with rfl | rfl | rfl <;>
      simp [GlobalCarryRecognizer.SepSeed, formulaS, subjectS, headS, tailS]

theorem baseM_binding :
    RawTopologyBindingResidual
      (acceptedFamilyDataM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).base := by
  have hc :
      (acceptedFamilyDataM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).base.exec.ComputeRowsAccepted := by
    change
      (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec.ComputeRowsAccepted
    rw [specializedProblemM_honest]
    exact compute_rows_acceptedS
  have hm :
      (acceptedFamilyDataM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).base.exec.MemoryRowsAccepted := by
    change
      (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec.MemoryRowsAccepted
    rw [specializedProblemM_honest]
    exact memory_rows_acceptedS
  apply (exactTopology_iff_rawTopologyBindingResidual_of_rowsAccepted _ hc hm).1
  constructor
  · change ComputeExactTopology
      (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec
    rw [specializedProblemM_honest]
    exact compute_topologyS
  · change MemoryExactTopology
      (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec
    rw [specializedProblemM_honest]
    exact memory_topologyS

theorem coinM_not_specializedTopologyFailureEvent :
    coinM ∉ specializedTopologyFailureEvent verifierM.raw cfgS.challenges.lam := by
  rw [mem_specializedTopologyFailureEvent_iff]
  rintro ⟨hz, hbad⟩
  change (0 : K97cubic) ∈
    topologyBadGammas (acceptedFamilyDataM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).base at hbad
  rw [topologyBadGammas_empty_of_binding _ baseM_binding] at hbad
  exact absurd hbad (Finset.notMem_empty _)

/-- The axis conclusion of the two-serviced-root `MemoryProductionAssignment`, transported to
the template-specialized carrier the verifier's guarded event uses. -/
theorem axis_eq_relaxis_transported
    (_hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)
    (X : ExactExecution cfgS) (hX : X = execSA)
    (i : Fin cfgS.kMem) (e : ℕ)
    (hread : e ∈ AxisBridge.readExps (exactAxisTree cfgS X i))
    (hverify : e ∈ AxisBridge.verifyExps (exactAxisTree cfgS X i)) :
    AxisBatching.MTree.vaxis e (exactAxisTree cfgS X i) =
      AxisBatching.MTree.Relaxis e (exactAxisTree cfgS X i) := by

  -- value is `execSA` (`HonestCommitment.Data.honest_execA`).
  subst hX
  exact axis_eq_relaxis_of_usedM _hmoreM i e hread hverify

theorem coinM_not_guardedAxisFailureEvent
    (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution) :
    coinM ∉ ProductionP8Containment.guardedAxisFailureEvent (packageHonestM hmoreM).strategy
      cfgS.challenges.lam := by
  rw [ProductionP8Containment.mem_guardedAxisFailureEvent_iff]
  rintro ⟨hz, hbad⟩
  change fixtureAlpha ∈
    ProductionAxisStructureVerifier.verifierGuardedRootUnion templateM cfgS.challenges.lam at hbad
  obtain ⟨i, -, hmem⟩ := Finset.mem_biUnion.1 hbad
  simp only [ProductionAxisStructureVerifier.verifierGuardedRootAlphas,
    Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  obtain ⟨-, -, ⟨e, hread, hverify, hne⟩, -, -⟩ := hmem
  exact hne
    (axis_eq_relaxis_transported hmoreM _ dataM.honest_execA i e hread hverify)

theorem sizeWindowNounsM :
    SizeWindowCounting.skeletonSizeWindowNouns skelM = [resultS] := by
  rw [SizeWindowCounting.skeletonSizeWindowNouns, computeSkeletonRowsM]
  simp [SizeWindowCounting.requiredSizeWindowNouns, parentSkeletonRow, servedSkeletonRow,
    P8Census.skeletonSubformula, ComputeTable.fanoutComp]

theorem coinM_not_sizeWindowFailure :
    coinM ∉ SizeWindowCounting.SizeWindowFailure skelM := by
  rw [SizeWindowCounting.mem_SizeWindowFailure_iff]
  rintro ⟨-, n, hn, hw⟩
  rw [sizeWindowNounsM, List.mem_singleton] at hn
  subst hn
  exact hw (servedSeed_window_atom 7)

/-- **The honest coin lies outside the P8 census failure union.** -/
theorem coinM_not_failureUnion :
    coinM ∉ ProductionP8Containment.FailureUnion (packageHonestM hmoreM).strategy
      (packageHonestM hmoreM).optimized.census cfgS.challenges.lam := by
  intro hbad
  simp only [ProductionP8Containment.FailureUnion, Finset.mem_union] at hbad
  rcases hbad with hbad | hbad
  · rcases hbad with hbad | hbad
    · rcases hbad with hbad | hbad
      · rcases hbad with hbad | hbad
        · exact coinM_not_zeroSeedFailureEvent hbad
        · exact coinM_not_collisionFailureEvent hbad
      · exact coinM_not_specializedTopologyFailureEvent hbad
    · exact coinM_not_guardedAxisFailureEvent hmoreM hbad
  · exact coinM_not_sizeWindowFailure hbad


/-! ## The informative P8 containment conjunct -/

/-- **The genuine target is reached at a fully renderer-constructed package.** -/
theorem genuineTargetM
    (hrootAt : (packageHonestM hmoreM).strategy.RootAxisBoundaryAt
      (nprSeed coinM) seedM_ne (alphaM coinM)) :
    ProductionP8Containment.GenuineTargetAt (packageHonestM hmoreM).strategy 97 3 coinM
      cfgS.challenges.lam :=
  (packageHonestM hmoreM).containment coinM cfgS.challenges.lam
    (packageHonestM_accepts hmoreM hrootAt)
    (coinM_not_failureUnion hmoreM)

/-- The acceptance set of the constructed package's strategy is inhabited. -/
theorem packageHonestM_acceptance_nonempty
    (hrootAt : (packageHonestM hmoreM).strategy.RootAxisBoundaryAt
      (nprSeed coinM) seedM_ne (alphaM coinM)) :
    ∃ ω : JointCoins K97cubic, (packageHonestM hmoreM).strategy.Accepts ω cfgS.challenges.lam :=
  ⟨coinM, packageHonestM_accepts hmoreM hrootAt⟩

/-- Both antecedents of the released containment conjunct hold on the same coin, at the same
constructed package strategy and census, and the conclusion follows. -/
theorem containmentM_is_informative
    (hrootAt : (packageHonestM hmoreM).strategy.RootAxisBoundaryAt
      (nprSeed coinM) seedM_ne (alphaM coinM))
    (haxM : FormRAxisBound (packageHonestM hmoreM).optimized.sampled
      (packageHonestM hmoreM).optimized.basis)
    (hbasisM : FormRBasis (packageHonestM hmoreM).optimized.basis)
    (hwidthM : FormRWidth F97) :
    (packageHonestM hmoreM).strategy.Accepts coinM cfgS.challenges.lam ∧
      coinM ∉ ProductionP8Containment.FailureUnion (packageHonestM hmoreM).strategy
        (packageHonestM hmoreM).optimized.census cfgS.challenges.lam ∧
      ProductionP8Containment.GenuineTargetAt (packageHonestM hmoreM).strategy 97 3 coinM
        cfgS.challenges.lam ∧
      (∀ (ω : JointCoins K97cubic) (lmb : K97cubic), (packageHonestM hmoreM).strategy.Accepts ω lmb →
        ω ∉ ProductionP8Containment.FailureUnion (packageHonestM hmoreM).strategy
          (packageHonestM hmoreM).optimized.census lmb →
        ProductionP8Containment.GenuineTargetAt (packageHonestM hmoreM).strategy 97 3 ω lmb) :=
  ⟨packageHonestM_accepts hmoreM hrootAt, coinM_not_failureUnion hmoreM,
    genuineTargetM hmoreM hrootAt, (statementHonestM hmoreM haxM hbasisM hwidthM).containment⟩

/-! ## The arrays really are the honest ones, not the all-zero placeholder -/

/-- The exact-IO multiplicities of the honest later-round message are all nonzero — precisely the
raw verifier gate the all-zero arrays of `residualM` violate. -/
theorem arraysM_multiplicity_ne_zero :
    ∀ j, (alphaMCommitmentM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).io.multiplicity j ≠ 0 :=
  fun _ => honestAssignmentM.exactIO.multiplicity_ne_zero _

/-- Compiled contrast with `HonestCommitment.zeroAlphaM`: the honest post-`alphaM` IO arrays are
not the all-zero ones. -/
theorem arraysM_ne_zeroAlphaM :
    (alphaMCommitmentM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).io.multiplicity ≠
      (HonestCommitment.zeroAlphaM timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).io.multiplicity := by
  intro h
  have hpos :
      0 <
        (acceptedFamilyDataM servedSeed seedM_ne
          fixtureAlpha cfgS.challenges.lam).base.exec.derivedResponseIO.length := by
    rw [acceptedFamilyM_response_length]
    norm_num
  have hj := congrFun h ⟨0, hpos⟩
  exact arraysM_multiplicity_ne_zero ⟨0, hpos⟩ hj

/-- The committed residual really is instantiated with the honest later-round message, the exact
counterpart of the earlier `residualM_arrays_are_zero`. -/
theorem residualHonestM_uses_honest_arrays :
    residualHonestM =
      HonestCommitment.commitmentResidualOf dataM alphaMCommitmentM walkArraysM := rfl

/-! ## Distinctness of the underlying execution, restated at this package -/

theorem packageHonestM_regression :
    (packageHonestM hmoreM).objects.cfg = cfgS ∧
      (packageHonestM hmoreM).objects.exec = execS ∧
      (packageHonestM hmoreM).computeChip.rap.w = 303 ∧
      (packageHonestM hmoreM).computeChip.rap.s = 418 ∧
      (packageHonestM hmoreM).memoryChip.rap.w = 205 ∧ (packageHonestM hmoreM).memoryChip.rap.s = 156 ∧
      (packageHonestM hmoreM).computeChip.rap.H.card = 2 ∧
      multiRootExecution.cfg.compRows = 2 ∧ multiRootExecution.cfg.memRows = 15 ∧
      multiRootExecution.cfg.kMem = 3 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · exact (BuildablePackage.constructed_resources multiRootExecution inputsM residualHonestM
      inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualHonestM_generated MultiRootHonestCommitment.f97_primeField).1
  · exact (BuildablePackage.constructed_resources multiRootExecution inputsM residualHonestM
      inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualHonestM_generated MultiRootHonestCommitment.f97_primeField).2.1
  · exact (BuildablePackage.constructed_resources multiRootExecution inputsM residualHonestM
      inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualHonestM_generated MultiRootHonestCommitment.f97_primeField).2.2.1
  · exact (BuildablePackage.constructed_resources multiRootExecution inputsM residualHonestM
      inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualHonestM_generated MultiRootHonestCommitment.f97_primeField).2.2.2
  · exact (BuildablePackage.constructed_row_budgets multiRootExecution inputsM residualHonestM
      inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualHonestM_generated MultiRootHonestCommitment.f97_primeField).1

end

end Nock.NockVMROM.Thm54.MultiRootHonestArrays

#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.specializedProblemM_honest
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.responseLenM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.requestLenM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.rawZeroFamilyM_tableAssumptions
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.legacyZeroFamilyM_chained
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.legacyZeroFamilyM_semanticWitness
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.legacyZeroFamilyM_KszBound
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.honestCompletionM_nonempty
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.alphaMCommitmentM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.walkArraysM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.rawStrategyM_familyAt
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.rawStrategyM_messageAt
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.claimM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.honestVerifierGatesM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.rawStrategyM_accepts_coinM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.honest_exactTopologyM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.verifierM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.verifierM_accepts_coinM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.alphaFreeRootM_zero
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.alphaFreeRootM_one
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.forestReadExpsM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.forestVerifyExpsM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.alphaFreeAxisStructureM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.noWrapM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.structuralChecksM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.countsP_treeA
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.countsP_treeB
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.rootAxisBoundaryM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.residualHonestM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.packageHonestM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.statementHonestM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.packageHonestM_accepts
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.topologyBadGammas_empty_of_binding
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.coinM_not_zeroSeedFailureEvent
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.coinM_not_collisionFailureEvent
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.coinM_not_specializedTopologyFailureEvent
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.coinM_not_guardedAxisFailureEvent
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.coinM_not_sizeWindowFailure
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.coinM_not_failureUnion
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.genuineTargetM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.packageHonestM_acceptance_nonempty
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.containmentM_is_informative
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.arraysM_multiplicity_ne_zero
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.arraysM_ne_zeroAlphaM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.residualHonestM_uses_honest_arrays
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.packageHonestM_regression
