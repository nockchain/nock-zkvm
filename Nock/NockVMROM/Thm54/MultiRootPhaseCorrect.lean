import Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# One package, every sampled walk challenge: the phase-correct later-round message

`MultiRootNonzeroChallenges` proves `∀ a g, Accepts (packageHonestN a g) (coinN a g)`.  The
package there is rebuilt at each pair, because `alphaMCommitmentN a g` reads the IO endpoints and
the table arrays off `honestCompletionN a g`, a `Classical.choice` taken *after* the pair is fixed.
That is per-tuple completeness, not the paper's chronology.

The paper fixes the chronology exactly: the prover commits at the paper, the verifier answers
with `α, γ ∈ 𝕂` at the paper, and only then does the prover build `ln`, `count` and
`acc_walk`.  The Lean types already carry that split —
`TemplateRawJointSoundness.Strategy.afterAlphaM` has the API `(z, hz, alphaM)` and cannot mention
`alphaC` or `gamma`, while `afterCoins` is a function of the whole coin.  This module uses both
halves as intended:

* `uniformEndpoints_exist` hoists the endpoint choice out of the walk challenges.  The endpoints
  come from `ExactDerivedIOAssignment.exists_with_public_endpoints_of_semanticIOWitness` applied to
  the *coin-free* problem, so one triple `(requests, responses, outMem)` serves every `(a, g)`; only
  then is a joint assignment chosen at each pair.
* `alphaMCommitmentP` is the pre-challenge message.  Its endpoints and its table/IO arrays are read
  off the single reference assignment `assignmentP 0 0`, and it takes no `a`/`g` argument.
* `walkArraysP ω` is the later-round message and is a genuine function of the sampled coin: it
  returns the walk columns of `assignmentP (alphaC ω) (gamma ω)`.

The resulting `packageP` is one closed definition, and `exists_package_accepting_every_challenge_pair`
states the acceptance with the package **outside** the quantifier.
-/

namespace Nock.NockVMROM.Thm54.MultiRootPhaseCorrect

open scoped Classical Polynomial
open Nock Nock.Noun Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open SemanticStrategy SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.MultiRootHonestArrays
open Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97p : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97p : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)

/-! ## The public IO endpoints are chosen before the walk coins

`jointVerification_complete` bundles two choices which the paper makes at different rounds: the
public IO endpoints, which are a function of the committed execution's derived request/response
lists alone, and the six-family assignment, whose two walk components depend on the sampled
`α`, `γ`.  Splitting them is all that is needed: the endpoint constructor
`ExactDerivedIOAssignment.exists_with_public_endpoints_of_semanticIOWitness` reads only
`R.problem`, which `AlphaMFamilyData.atCoins` leaves untouched. -/

/-- The exact derived-IO assignment reads only the committed problem and the three public IO
endpoints, never a walk challenge, so it transports verbatim across `withWalkChallenges`.  Every
field is copied definitionally; only the *index* of the type moves. -/
def ioAtWalkChallenges {F K : Type} [Field F] [Field K] [Algebra F K]
    {R : PlusIOSegmentedFamily F K} {p : ℕ} [CharP K p]
    (io : ExactDerivedIOAssignment R p) (αc γ αm : K) :
    ExactDerivedIOAssignment (R.withWalkChallenges αc γ αm) p where
  multiplicity := io.multiplicity
  progAcc := io.progAcc
  memAcc := io.memAcc
  multiplicity_ne_zero := io.multiplicity_ne_zero
  progSat := io.progSat
  memSat := io.memSat
  endpoints_agree := io.endpoints_agree
  memory_closes := io.memory_closes

/-- **One endpoint triple for every sampled walk-challenge pair**. -/
theorem uniformEndpoints_exist :
    ∃ requests responses outMem : IOField K97cubic,
      ∀ a g : K97cubic,
        Nonempty (JointAssignment
          ((legacyZeroFamilyN a g).withIOEndpoints requests responses outMem)
          (ringChar K97cubic)) := by
  have hLIO :
      IO.LIO legacyZeroFamilyM.problem.cfg.Ksz
        legacyZeroFamilyM.problem.exec.derivedRequestIO
        legacyZeroFamilyM.problem.exec.derivedResponseIO :=
    (legacyZeroFamilyM_semanticWitness.strongExactLanguage_of_semanticExactLanguage
      legacyZeroFamilyM_chained.semantic).2.2
  obtain ⟨requests, responses, outMem, ⟨io⟩⟩ :=
    ExactDerivedIOAssignment.exists_with_public_endpoints_of_semanticIOWitness
      (p := ringChar K97cubic) legacyZeroFamilyM legacyZeroFamilyM_KszBound
      legacyZeroFamilyM_semanticWitness legacyZeroFamilyM_chained.semantic
  refine ⟨requests, responses, outMem, fun a g => ?_⟩
  have io' :
      ExactDerivedIOAssignment
        ((legacyZeroFamilyN a g).withIOEndpoints requests responses outMem)
        (ringChar K97cubic) :=
    ioAtWalkChallenges io a g fixtureAlpha
  obtain ⟨A, hA⟩ :=
    PlusIOSameExecutionAssignment.exists_satisfies_of_chained_IO
      (R := (legacyZeroFamilyN a g).withIOEndpoints requests responses outMem)
      (p := ringChar K97cubic)
      (legacyZeroFamilyN_chained a g) io'
  exact
    ⟨{ sameExecution := A
       sixFamilies := hA
       sharedIO :=
         (sharedIOSat_iff_LIO
           ((legacyZeroFamilyN a g).withIOEndpoints requests responses outMem)
           (legacyZeroFamilyN_KszBound a g)).2 hLIO }⟩

/-- The completion of record: one endpoint triple, and one joint assignment at each sampled pair.
The endpoint fields are **not** indexed by `(a, g)`; that is the whole point. -/
structure PhaseCompletion where
  requests : IOField K97cubic
  responses : IOField K97cubic
  outMem : IOField K97cubic
  assignment : ∀ a g : K97cubic,
    JointAssignment ((legacyZeroFamilyN a g).withIOEndpoints requests responses outMem)
      (ringChar K97cubic)

theorem phaseCompletion_nonempty : Nonempty PhaseCompletion := by
  obtain ⟨requests, responses, outMem, h⟩ := uniformEndpoints_exist
  exact ⟨⟨requests, responses, outMem, fun a g => Classical.choice (h a g)⟩⟩

noncomputable def completionP : PhaseCompletion := Classical.choice phaseCompletion_nonempty

/-- The exact family at the sampled pair `(a, g)`.  Only the two walk challenges move; the
endpoints are `completionP`'s, hence the same at every pair. -/
abbrev legacyFamilyP (a g : K97cubic) : PlusIOSegmentedFamily F97 K97cubic :=
  (legacyZeroFamilyN a g).withIOEndpoints completionP.requests completionP.responses
    completionP.outMem

abbrev assignmentP (a g : K97cubic) :
    PlusIOSameExecutionAssignment (legacyFamilyP a g) (ringChar K97cubic) :=
  (completionP.assignment a g).sameExecution

/-- Compiled receipt that the endpoint half really is pair-independent. -/
theorem legacyFamilyP_endpoints (a g a' g' : K97cubic) :
    (legacyFamilyP a g).requests = (legacyFamilyP a' g').requests ∧
      (legacyFamilyP a g).responses = (legacyFamilyP a' g').responses ∧
      (legacyFamilyP a g).outMem = (legacyFamilyP a' g').outMem ∧
      (legacyFamilyP a g).problem = (legacyFamilyP a' g').problem ∧
      (legacyFamilyP a g).computeWalkAlpha = a ∧
      (legacyFamilyP a g).walkGamma = g :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The pre-challenge message

`AlphaMFamilyData` and `AlphaMCommitment` are indexed by `(z, hz, alphaM)` only; the type itself
forbids a walk challenge from appearing here.  The definitions below take no
`a`/`g` argument either: the endpoints are `completionP`'s and the table/IO arrays are the reference
assignment's. -/

def acceptedFamilyDataP (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    AlphaMFamilyData timestampM z hz α lmb where
  compNodeWidth := NodeEncoding.computeNodeWidth
  compNodeEncode := NodeEncoding.computeNodeEncode stateTagChar97
  memNodeWidth := NodeEncoding.memoryNodeWidth
  memNodeEncode := NodeEncoding.memoryNodeEncode stateTagChar97
  requests := completionP.requests
  responses := completionP.responses
  outMem := completionP.outMem

theorem acceptedFamilyP_response_length (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    (acceptedFamilyDataP z hz α lmb).base.exec.derivedResponseIO.length = 3 :=
  responseLenM z hz α lmb

theorem legacyFamilyP_response_length (a g : K97cubic) :
    (legacyFamilyP a g).problem.exec.derivedResponseIO.length = 3 :=
  responseLenM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam

/-- **The committed later-round-`alphaM` message.**  No `alphaC`, no `gamma`, and no `(a, g)`
parameter: one object, fixed before the verifier answers. -/
def alphaMCommitmentP (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    AlphaMCommitment (p := ringChar K97cubic) timestampM z hz α lmb where
  familyData := acceptedFamilyDataP z hz α lmb
  tables :=
    { compute := (assignmentP 0 0).computeTableAux
      memory := (assignmentP 0 0).memoryTableAux }
  io :=
    { multiplicity := fun j =>
        (assignmentP 0 0).exactIO.multiplicity
          ⟨j, by
            have hj := j.isLt
            have hsource := acceptedFamilyP_response_length z hz α lmb
            have htarget := legacyFamilyP_response_length 0 0
            omega⟩
      progAcc := (assignmentP 0 0).exactIO.progAcc
      memAcc := (assignmentP 0 0).exactIO.memAcc }

/-! ## The post-challenge message, a genuine function of the sampled coin -/

/-- **The later-round walk columns**.  Unlike `walkArraysN`, this reads its
`ω` argument: it returns the walk assignment built at that coin's own `alphaC` and `gamma`. -/
def walkArraysP (ω : JointCoins K97cubic) (_lmb : K97cubic) (_hz : nprSeed ω ≠ 0) : RawWalkArrays K97cubic where
  computeLn := (assignmentP (alphaC ω) (gamma ω)).computeWalk.ln
  computeCount := (assignmentP (alphaC ω) (gamma ω)).computeWalk.count
  computeAcc := (assignmentP (alphaC ω) (gamma ω)).computeWalk.acc
  memoryLn := (assignmentP (alphaC ω) (gamma ω)).memoryWalk.ln
  memoryCount := (assignmentP (alphaC ω) (gamma ω)).memoryWalk.count
  memoryAcc := (assignmentP (alphaC ω) (gamma ω)).memoryWalk.acc

theorem walkArraysP_reads_the_coin (ω : JointCoins K97cubic) (lmb : K97cubic) (hz : nprSeed ω ≠ 0) :
    (walkArraysP ω lmb hz).computeLn = (assignmentP (alphaC ω) (gamma ω)).computeWalk.ln ∧
      (walkArraysP ω lmb hz).computeCount = (assignmentP (alphaC ω) (gamma ω)).computeWalk.count ∧
      (walkArraysP ω lmb hz).computeAcc = (assignmentP (alphaC ω) (gamma ω)).computeWalk.acc ∧
      (walkArraysP ω lmb hz).memoryLn = (assignmentP (alphaC ω) (gamma ω)).memoryWalk.ln ∧
      (walkArraysP ω lmb hz).memoryCount = (assignmentP (alphaC ω) (gamma ω)).memoryWalk.count ∧
      (walkArraysP ω lmb hz).memoryAcc = (assignmentP (alphaC ω) (gamma ω)).memoryWalk.acc :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The message the verifier actually reads

Committed tables and IO from the reference assignment, walks from the assignment at this coin.
Both halves live over the *same* exact family, because the four non-walk RAPs and their traces
read only `problem`, `requests`, `responses` and `outMem`. -/

def mixedAssignmentP (a g : K97cubic) :
    PlusIOSameExecutionAssignment (legacyFamilyP a g) (ringChar K97cubic) where
  computeTableAux := (assignmentP 0 0).computeTableAux
  memoryTableAux := (assignmentP 0 0).memoryTableAux
  computeWalk := (assignmentP a g).computeWalk
  memoryWalk := (assignmentP a g).memoryWalk
  exactIO := ioAtWalkChallenges (assignmentP 0 0).exactIO a g fixtureAlpha

/-- **The six families accept the mixed message.**  Two conjuncts come from the assignment at this
coin — those are exactly the compute-walk and memory-walk RAPs — and four from the reference
assignment, whose RAPs and traces are the identical terms at every pair. -/
theorem mixedAssignmentP_satisfies (a g : K97cubic) : (mixedAssignmentP a g).Satisfies := by
  have h0 := (completionP.assignment 0 0).sixFamilies
  have hag := (completionP.assignment a g).sixFamilies
  exact ⟨h0.1, h0.2.1, hag.2.2.1, hag.2.2.2.1, h0.2.2.2.2.1, h0.2.2.2.2.2⟩

/-! ## The phase-correct raw strategy -/

def rawStrategyP : TemplateRawJointSoundness.Strategy F97 K97cubic (ringChar K97cubic) where
  timestamp := timestampM
  afterAlphaM := alphaMCommitmentP
  afterCoins := walkArraysP

theorem rawStrategyP_familyAt (a g : K97cubic) :
    rawStrategyP.familyAt (coinN a g) cfgS.challenges.lam seedM_ne =
      RawPlusIOSegmentedFamily.ofLegacy (legacyFamilyP a g) := rfl

theorem rawStrategyP_messageAt (a g : K97cubic) :
    rawStrategyP.messageAt (coinN a g) cfgS.challenges.lam seedM_ne =
      RawMessage.ofLegacy (mixedAssignmentP a g) := rfl

/-- **The commit-then-sample receipt.**  The pre-challenge message is the *same term* at two coins
with different `alphaC` and `gamma`; the paper samples them only after the paper. -/
theorem alphaMCommitmentP_same_across_coins (a g a' g' : K97cubic) :
    rawStrategyP.alphaMCommitment (coinN a g) cfgS.challenges.lam seedM_ne =
      rawStrategyP.alphaMCommitment (coinN a' g') cfgS.challenges.lam seedM_ne := rfl

abbrev rawLegacyP (a g : K97cubic) : RawPlusIOSegmentedFamily F97 K97cubic :=
  RawPlusIOSegmentedFamily.ofLegacy (legacyFamilyP a g)

theorem rawLegacyP_computeRowsAccepted (a g : K97cubic) :
    (rawLegacyP a g).exec.ComputeRowsAccepted :=
  rawLegacyM_computeRowsAccepted

theorem rawLegacyP_memoryRowsAccepted (a g : K97cubic) :
    (rawLegacyP a g).exec.MemoryRowsAccepted :=
  rawLegacyM_memoryRowsAccepted

theorem rawLegacyP_computePubAt_zero (a g : K97cubic) :
    (rawLegacyP a g).exec.computePubAt ⟨0, (rawLegacyP a g).cfg.compRows_pos⟩ = parentPubS :=
  rawLegacyM_computePubAt_zero

theorem rawLegacyP_Ksz (a g : K97cubic) : (rawLegacyP a g).cfg.Ksz = 4 :=
  rawLegacyM_Ksz

theorem rawLegacyP_requests (a g : K97cubic) :
    (rawLegacyP a g).exec.derivedRequestIO =
      [NockVM.encRecFormR parentRecordS MemoryTable.formRDefault,
          NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault,
        NockVM.encRecFormR servedRecord MemoryTable.formRDefault] :=
  rawLegacyM_requests

theorem rawLegacyP_responses (a g : K97cubic) :
    (rawLegacyP a g).exec.derivedResponseIO =
      [NockVM.encRecFormR parentRecordS MemoryTable.formRDefault,
          NockVM.encRecFormR servedRecord MemoryTable.formRDefault,
        NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault] :=
  rawLegacyM_responses

theorem honestVerifierGatesP (a g : K97cubic) :
    (RawMessage.ofLegacy (mixedAssignmentP a g)).VerifierGates skelM.publicClaim (coinN a g) := by
  refine ⟨seedM_ne, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact rowAlignment_of_rowsAcceptedM (rawLegacyP a g)
      (rawLegacyP_computeRowsAccepted a g) (rawLegacyP_memoryRowsAccepted a g)
  · refine ⟨rfl, ?_, rfl, ?_⟩
    · intro hchar
      have hh : hchar = stateTagChar97 := Subsingleton.elim _ _
      subst hchar
      rfl
    · intro hchar
      have hh : hchar = stateTagChar97 := Subsingleton.elim _ _
      subst hchar
      rfl
  · rw [rawLegacyP_computePubAt_zero a g, claimM]
    rfl
  · rw [rawLegacyP_computePubAt_zero a g, claimM]
    rfl
  · rw [rawLegacyP_computePubAt_zero a g, claimM]
    rfl
  · exact (completionP.assignment 0 0).public_endpoints.1
  · exact (completionP.assignment 0 0).public_endpoints.2
  · exact (assignmentP 0 0).exactIO.multiplicity_ne_zero
  · rw [rawLegacyP_requests a g, rawLegacyP_Ksz a g]
    norm_num [IO.InRange]
  · rw [rawLegacyP_requests a g, ← derived_requestsS]
    exact requestsS_nodup
  · rw [rawLegacyP_responses a g, rawLegacyP_Ksz a g]
    norm_num
  · rw [rawLegacyP_responses a g, ← derived_responsesS]
    exact responsesS_nodup

theorem rawStrategyP_accepts (a g : K97cubic) : rawStrategyP.Accepts (coinN a g) cfgS.challenges.lam := by
  apply (rawStrategyP.accepts_iff_raw (coinN a g) cfgS.challenges.lam seedM_ne).2
  change (RawMessage.ofLegacy (mixedAssignmentP a g)).Accepts skelM.publicClaim (coinN a g)
  exact RawMessage.accepts_of_legacy_assignment
    skelM.publicClaim (coinN a g) (mixedAssignmentP a g)
    (mixedAssignmentP_satisfies a g) (honestVerifierGatesP a g)

/-- The walk RAPs the acceptance discharges carry the sampled coins: the accepted family's own
compute-walk challenge is `a` and its topology-compression challenge is `g`. -/
theorem acceptedP_walk_challenges (a g : K97cubic) :
    (rawStrategyP.familyAt (coinN a g) cfgS.challenges.lam seedM_ne).computeWalkAlpha = a ∧
      (rawStrategyP.familyAt (coinN a g) cfgS.challenges.lam seedM_ne).walkGamma = g ∧
      (rawStrategyP.familyAt (coinN a g) cfgS.challenges.lam seedM_ne).memoryWalkAlpha = fixtureAlpha ∧
      (∀ kind, ((rawStrategyP.familyAt (coinN a g) cfgS.challenges.lam seedM_ne).computeWalkRAP kind).Satisfies
        (rawStrategyP.messageAt (coinN a g) cfgS.challenges.lam seedM_ne).computeWalkTrace) ∧
      (∀ kind, ((rawStrategyP.familyAt (coinN a g) cfgS.challenges.lam seedM_ne).memoryWalkRAP kind).Satisfies
        (rawStrategyP.messageAt (coinN a g) cfgS.challenges.lam seedM_ne).memoryWalkTrace) := by
  have h := (rawStrategyP.accepts_iff_six_families (coinN a g) cfgS.challenges.lam seedM_ne).1
    (rawStrategyP_accepts a g)
  exact ⟨rfl, rfl, rfl, h.2.2.2.1, h.2.2.2.2.1⟩

/-! ## The verifier and the constructed package -/

theorem honest_exactTopologyP (a g : K97cubic) :
    ComputeExactTopology (rawStrategyP.familyAt (coinN a g) cfgS.challenges.lam seedM_ne).exec ∧
      MemoryExactTopology (rawStrategyP.familyAt (coinN a g) cfgS.challenges.lam seedM_ne).exec := by
  change ComputeExactTopology
      (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec ∧
    MemoryExactTopology
      (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec
  rw [specializedProblemM_honest]
  exact ⟨compute_topologyS, memory_topologyS⟩

/-- The one committed template verifier: `dataM` unchanged, the phase-correct later-round pair. -/
def verifierP : ProductionRawVerifier.TemplateAdapter.Strategy F97 K97cubic (ringChar K97cubic) :=
  HonestCommitment.verifierOf dataM alphaMCommitmentP walkArraysP

theorem verifierP_eq :
    verifierP = ProductionRawVerifier.TemplateAdapter.Strategy.honest rawStrategyP := rfl

theorem verifierP_accepts (a g : K97cubic) : verifierP.Accepts (coinN a g) cfgS.challenges.lam :=
  ProductionRawVerifier.TemplateAdapter.Strategy.honest_accepts
    rawStrategyP (coinN a g) cfgS.challenges.lam seedM_ne (rawStrategyP_accepts a g) (honest_exactTopologyP a g)

theorem structuralChecksP :
    ProductionAxisStructureVerifier.structuralChecksAt verifierP servedSeed seedM_ne
      fixtureAlpha = true := by
  change
    (ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck templateM &&
      ProductionAxisStructureVerifier.noWrapCheck templateM fixtureAlpha) = true
  simp [alphaFreeAxisStructureM, noWrapM]

/-- The committed residual: `dataM`, the coin-free `alphaMCommitmentP`, and the coin-reading
`walkArraysP`. -/
def residualHonestP : BuildablePackage.CommitmentResidual multiRootExecution :=
  HonestCommitment.commitmentResidualOf dataM alphaMCommitmentP walkArraysP

theorem residualHonestP_generated :
    GeneratedField.ClaimGenerated K97cubic residualHonestP.verifier.raw.claim residualHonestP.Λ :=
  MultiRootHonestCommitment.residualOf_generated alphaMCommitmentP walkArraysP

/-- **The phase-correct package.**  It has no `a`/`g` parameter. -/
def packageP :
    OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F97 K97cubic 4 :=
  BuildablePackage.buildFullPackage multiRootExecution inputsM residualHonestP
    inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualHonestP_generated MultiRootHonestCommitment.f97_primeField

/-- The released fourteen-conjunct statement over this one package, through the unchanged
`statementM_of_arrays`. -/
theorem statementP
    (hax : FormRAxisBound (packageP hmoreM).optimized.sampled
      (packageP hmoreM).optimized.basis)
    (hbasis : FormRBasis (packageP hmoreM).optimized.basis)
    (hwidth : FormRWidth F97) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageP hmoreM) :=
  statementM_of_arrays hmoreM alphaMCommitmentP walkArraysP hax hbasis hwidth

variable (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
    (packageP hmoreM).optimized.basis)
variable (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
variable (hwidthP : FormRWidth F97)

theorem packageP_verifier : (packageP hmoreM).strategy.verifier = verifierP := rfl

/-- **The one package accepts the coin at every sampled walk-challenge pair.** -/
theorem packageP_accepts
    (a g : K97cubic)
    (hrootAt : (packageP hmoreM).strategy.RootAxisBoundaryAt
      (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    (packageP hmoreM).strategy.Accepts (coinN a g) cfgS.challenges.lam := by
  apply (((packageP hmoreM).strategy.accepts_iff (coinN a g) cfgS.challenges.lam seedM_ne)).2
  constructor
  · apply (ProductionAxisStructureVerifier.accepts_iff verifierP (coinN a g) cfgS.challenges.lam seedM_ne).2
    exact ⟨(verifierP.accepts_iff_production (coinN a g) cfgS.challenges.lam seedM_ne).1
      (verifierP_accepts a g), structuralChecksP⟩
  · exact hrootAt

/-! ## The five counted failure events, at the one package -/

theorem coinP_not_zeroSeedFailureEvent (a g : K97cubic) :
    coinN a g ∉ (zeroSeedFailureEvent : Finset (JointCoins K97cubic)) :=
  coinN_not_zeroSeedFailureEvent a g

theorem coinP_not_collisionFailureEvent (a g : K97cubic) :
    coinN a g ∉ collisionFailureEvent censusM.census :=
  coinN_not_collisionFailureEvent a g

theorem baseP_binding :
    RawTopologyBindingResidual
      (acceptedFamilyDataP servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).base :=
  baseM_binding

theorem coinP_not_specializedTopologyFailureEvent (a g : K97cubic) :
    coinN a g ∉ specializedTopologyFailureEvent verifierP.raw cfgS.challenges.lam := by
  rw [mem_specializedTopologyFailureEvent_iff]
  rintro ⟨hz, hbad⟩
  change g ∈
    topologyBadGammas (acceptedFamilyDataP servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).base at hbad
  rw [topologyBadGammas_empty_of_binding _ baseP_binding] at hbad
  exact absurd hbad (Finset.notMem_empty _)

theorem coinP_not_guardedAxisFailureEvent (a g : K97cubic) :
    coinN a g ∉ ProductionP8Containment.guardedAxisFailureEvent (packageP hmoreM).strategy
      cfgS.challenges.lam := by
  intro h
  exact coinM_not_guardedAxisFailureEvent hmoreM
    (ProductionP8Containment.mem_guardedAxisFailureEvent_iff _ _ coinM |>.2
      ((ProductionP8Containment.mem_guardedAxisFailureEvent_iff _ _ (coinN a g)).1 h))

theorem coinP_not_sizeWindowFailure (a g : K97cubic) :
    coinN a g ∉ SizeWindowCounting.SizeWindowFailure skelM :=
  coinN_not_sizeWindowFailure a g

theorem coinP_not_failureUnion (a g : K97cubic) :
    coinN a g ∉ ProductionP8Containment.FailureUnion (packageP hmoreM).strategy
      (packageP hmoreM).optimized.census cfgS.challenges.lam := by
  intro hbad
  simp only [ProductionP8Containment.FailureUnion, Finset.mem_union] at hbad
  rcases hbad with hbad | hbad
  · rcases hbad with hbad | hbad
    · rcases hbad with hbad | hbad
      · rcases hbad with hbad | hbad
        · exact coinP_not_zeroSeedFailureEvent a g hbad
        · exact coinP_not_collisionFailureEvent a g hbad
      · exact coinP_not_specializedTopologyFailureEvent a g hbad
    · exact coinP_not_guardedAxisFailureEvent hmoreM a g hbad
  · exact coinP_not_sizeWindowFailure a g hbad

/-- **The genuine target is reached at every coin in the range, at the one package.** -/
theorem genuineTargetP
    (hrootAt : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g)))
    (a g : K97cubic) :
    ProductionP8Containment.GenuineTargetAt (packageP hmoreM).strategy 97 3 (coinN a g) cfgS.challenges.lam :=
  (packageP hmoreM).containment (coinN a g) cfgS.challenges.lam (packageP_accepts hmoreM a g (hrootAt a g))
    (coinP_not_failureUnion hmoreM a g)

/-! ## The delivery, with the quantifier order visible in the type -/

/-- **`∃ P, ∀ a g` — the package is outside the quantifier.** -/
theorem exists_package_accepting_every_challenge_pair
    (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)
    (hrootAt : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    ∃ P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F97 K97cubic 4,
      ∀ a g : K97cubic, P.strategy.Accepts (coinN a g) cfgS.challenges.lam :=
  ⟨packageP hmoreM, fun a g => packageP_accepts hmoreM a g (hrootAt a g)⟩

/-- The full commit-then-sample delivery at the one package: the released fourteen-conjunct
statement, acceptance at every sampled pair, exclusion from the failure union at every sampled
pair, and the genuine target at every sampled pair. -/
theorem commit_then_sample_completeness
    (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)
    (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
      (packageP hmoreM).optimized.basis)
    (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
    (hwidthP : FormRWidth F97)
    (hrootAt : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    ∃ P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F97 K97cubic 4,
      OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement P ∧
        ∀ a g : K97cubic,
          P.strategy.Accepts (coinN a g) cfgS.challenges.lam ∧
            coinN a g ∉ ProductionP8Containment.FailureUnion P.strategy P.optimized.census cfgS.challenges.lam ∧
            ProductionP8Containment.GenuineTargetAt P.strategy 97 3 (coinN a g) cfgS.challenges.lam :=
  ⟨packageP hmoreM, statementP hmoreM haxP hbasisP hwidthP,
    fun a g => ⟨packageP_accepts hmoreM a g (hrootAt a g), coinP_not_failureUnion hmoreM a g,
      genuineTargetP hmoreM hrootAt a g⟩⟩

/-- The one package accepts coins with **different** `alphaC` and **different** `gamma`; this is
what `rawStrategyN` cannot do, because its walk arrays ignore their `ω` argument while
`ln(1) = α` pins the walk columns. -/
theorem packageP_accepts_distinct_challenges
    (hrootAt : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    (packageP hmoreM).strategy.Accepts (coinN 0 0) cfgS.challenges.lam ∧
      (packageP hmoreM).strategy.Accepts coinNonzero cfgS.challenges.lam ∧
      alphaC (coinN 0 0) ≠ alphaC coinNonzero ∧
      gamma (coinN 0 0) ≠ gamma coinNonzero := by
  refine ⟨packageP_accepts hmoreM 0 0 (hrootAt 0 0), packageP_accepts hmoreM alphaCN gammaN (hrootAt alphaCN gammaN), ?_, ?_⟩
  · exact fun h => alphaCN_ne_zero h.symm
  · exact fun h => gammaN_ne_zero h.symm

/-! ## The committed half is `dataM`, unchanged -/

theorem packageP_commitment_unchanged :
    residualHonestP =
        HonestCommitment.commitmentResidualOf dataM alphaMCommitmentP walkArraysP ∧
      (packageP hmoreM).optimized.commitment.skeleton = dataM.skeleton ∧
      (packageP hmoreM).optimized.commitment.skeleton = skelM ∧
      (packageP hmoreM).objects.cfg = cfgS ∧ (packageP hmoreM).objects.exec = execS ∧
      (packageP hmoreM).optimized.census = censusM :=
  ⟨rfl, rfl, dataM_skeleton, rfl, rfl, rfl⟩

theorem packageP_regression :
    (packageP hmoreM).computeChip.rap.w = 303 ∧ (packageP hmoreM).computeChip.rap.s = 418 ∧
      (packageP hmoreM).memoryChip.rap.w = 205 ∧ (packageP hmoreM).memoryChip.rap.s = 156 ∧
      (packageP hmoreM).computeChip.rap.H.card = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (BuildablePackage.constructed_resources multiRootExecution inputsM
      residualHonestP inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualHonestP_generated MultiRootHonestCommitment.f97_primeField).1
  · exact (BuildablePackage.constructed_resources multiRootExecution inputsM
      residualHonestP inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualHonestP_generated MultiRootHonestCommitment.f97_primeField).2.1
  · exact (BuildablePackage.constructed_resources multiRootExecution inputsM
      residualHonestP inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualHonestP_generated MultiRootHonestCommitment.f97_primeField).2.2.1
  · exact (BuildablePackage.constructed_resources multiRootExecution inputsM
      residualHonestP inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualHonestP_generated MultiRootHonestCommitment.f97_primeField).2.2.2
  · exact (BuildablePackage.constructed_row_budgets multiRootExecution inputsM
      residualHonestP inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualHonestP_generated MultiRootHonestCommitment.f97_primeField).1

/-! The two controls are statements about the isolated walk layer and the isolated topology
compression, so they are unchanged objects; what is new is that they now sit beside an acceptance
by **one** package rather than by a package rebuilt at the coin. -/

/-- The materially altered non-BFT walk is still rejected at the nonzero compute-walk challenge of
record, and the single-coordinate payload mutation is still seen by the nonzero topology challenge
of record, at the coin the one package accepts. -/
theorem packageP_rejection_receipts
    (hrootAt : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    (packageP hmoreM).strategy.Accepts coinNonzero cfgS.challenges.lam ∧
      alphaC coinNonzero ≠ 0 ∧ gamma coinNonzero ≠ 0 ∧
      ¬ IsFullBFT alteredCurN alteredChildN alteredFanoutN 2 ∧
      (¬ ∃ ln count acc : ℕ → K97cubic,
        WalkSat alteredCurN alteredChildN alteredFanoutN ln count acc (alphaC coinNonzero)
          (alteredCurN 1 * alphaC coinNonzero) (alphaC coinNonzero) 2 ∧ acc 2 = 0) ∧
      (∃ ln count acc : ℕ → K97cubic,
        WalkSat alteredCurN alteredChildN alteredFanoutN ln count acc 0
          (alteredCurN 1 * 0) 0 2 ∧ acc 2 = 0) ∧
      (0 : K97cubic) ∈ computeSlotBadGammas badComputeTreeN 0 ∧
      gamma coinNonzero ∉ computeSlotBadGammas badComputeTreeN 0 :=
  ⟨packageP_accepts hmoreM alphaCN gammaN (hrootAt alphaCN gammaN), alphaCN_ne_zero, gammaN_ne_zero,
    alteredN_not_isFullBFT, altered_non_bft_walk_rejected_at_alphaCN.2,
    altered_non_bft_walk_accepts_at_zero.2,
    zero_is_bad_gamma_for_unbound_treeN, gammaN_not_bad_for_unbound_treeN⟩

/-! ## The two `p8_fixed_field_*` conjuncts at the one package

Prove that acceptance pins
the NPR seed to `servedSeed` and `alphaM` to `fixtureAlpha`, after which the four remaining failure
events are excluded and `FalseAcceptanceSet` is empty.  That sub-goal is unchanged and is still
**not** proved.  What the phase-correct package changes is the other half of the reduction: the
whole `(servedSeed, fixtureAlpha)` fibre — all `97 ^ 6` coins of it — is now excluded from the
false-acceptance set of **one** strategy, whereas `MultiRootNonzeroChallenges` excluded a single
coin from each of a family of strategies. -/

/-- Any coin with the committed seed and `alphaM` is `coinN` of its own two walk challenges. -/
theorem coin_eq_coinN {ω : JointCoins K97cubic}
    (hz : nprSeed ω = servedSeed) (hα : alphaM ω = fixtureAlpha) :
    ω = coinN (alphaC ω) (gamma ω) := by
  obtain ⟨⟨a, g⟩, ⟨α, z⟩⟩ := ω
  change z = (servedSeed : K97cubic) at hz
  change α = fixtureAlpha at hα
  subst hz
  subst hα
  rfl

/-- **The one package accepts the entire committed fibre**, not merely a `coinN`-shaped list. -/
theorem packageP_accepts_fibre {ω : JointCoins K97cubic}
    (hrootAt : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g)))
    (hz : nprSeed ω = servedSeed) (hα : alphaM ω = fixtureAlpha) :
    (packageP hmoreM).strategy.Accepts ω cfgS.challenges.lam := by
  rw [coin_eq_coinN hz hα]
  exact packageP_accepts hmoreM (alphaC ω) (gamma ω) (hrootAt (alphaC ω) (gamma ω))

theorem genuineTargetP_fibre {ω : JointCoins K97cubic}
    (hrootAt : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g)))
    (hz : nprSeed ω = servedSeed) (hα : alphaM ω = fixtureAlpha) :
    ProductionP8Containment.GenuineTargetAt (packageP hmoreM).strategy 97 3 ω cfgS.challenges.lam := by
  rw [coin_eq_coinN hz hα]
  exact genuineTargetP hmoreM hrootAt (alphaC ω) (gamma ω)

/-- **No coin of the committed fibre is a false acceptance of the one package.** -/
theorem falseAcceptanceP_disjoint_fibre {ω : JointCoins K97cubic}
    (hrootAt : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g)))
    (hz : nprSeed ω = servedSeed) (hα : alphaM ω = fixtureAlpha) :
    ω ∉ ProductionP8Containment.FalseAcceptanceSet (packageP hmoreM).strategy 97 3 cfgS.challenges.lam := by
  rw [ProductionP8Containment.mem_falseAcceptanceSet_iff]
  exact fun h => h.2 (genuineTargetP_fibre hmoreM hrootAt hz hα)

/-- Contrapositive: every false acceptance, if one exists, is off the committed fibre. -/
theorem falseAcceptanceP_off_fibre
    (hrootAt : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    ∀ ω ∈ ProductionP8Containment.FalseAcceptanceSet (packageP hmoreM).strategy 97 3 cfgS.challenges.lam,
      nprSeed ω ≠ 0 ∧ (nprSeed ω ≠ servedSeed ∨ alphaM ω ≠ fixtureAlpha) := by
  intro ω hω
  have hacc := (ProductionP8Containment.mem_falseAcceptanceSet_iff _ _ _ _ _).1 hω
  refine ⟨accepts_seed_ne_zero hacc.1, ?_⟩
  by_contra hcon
  push_neg at hcon
  exact falseAcceptanceP_disjoint_fibre hmoreM hrootAt hcon.1 hcon.2 hω

/-- If acceptance pins the seed and
`alphaM`, the false-acceptance set is empty and the two `p8_fixed_field_*` conjuncts carry no
witness content.  The hypothesis is not discharged here. -/
theorem falseAcceptanceP_empty_of_fibre_pinned
    (hrootAt : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g)))
    (h : ∀ ω : JointCoins K97cubic, (packageP hmoreM).strategy.Accepts ω cfgS.challenges.lam →
      nprSeed ω = servedSeed ∧ alphaM ω = fixtureAlpha) :
    ProductionP8Containment.FalseAcceptanceSet (packageP hmoreM).strategy 97 3 cfgS.challenges.lam = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro ω hω
  have hacc := (ProductionP8Containment.mem_falseAcceptanceSet_iff _ _ _ _ _).1 hω
  obtain ⟨hz, hα⟩ := h ω hacc.1
  exact falseAcceptanceP_disjoint_fibre hmoreM hrootAt hz hα hω

theorem coinN_injective :
    Function.Injective (fun p : K97cubic × K97cubic => coinN p.1 p.2) := by
  rintro ⟨a, g⟩ ⟨a', g'⟩ h
  simp only [coinN, Prod.mk.injEq] at h
  exact Prod.ext h.1.1 h.1.2

/-- The excluded fibre has exactly `97 ^ 6` coins, out of the `97 ^ 12` of the joint space. -/
theorem acceptedRangeP_card :
    (Finset.univ.image (fun p : K97cubic × K97cubic => coinN p.1 p.2)).card = 97 ^ 6 ∧
      Fintype.card (JointCoins K97cubic) = 97 ^ 12 := by
  constructor
  · rw [Finset.card_image_of_injective _ coinN_injective, Finset.card_univ,
      Fintype.card_prod, cardK97cubic]
    ring
  · rw [card_jointCoins, cardK97cubic]
    ring

/-- The recorded state of the two conjuncts at the phase-correct witness, with no upgrade smuggled
in: acceptance is non-empty on a `97 ^ 6`-element fibre of one strategy, every false acceptance
would have to lie off that fibre with a nonzero seed, and emptiness still waits on the single
unproved sub-goal.  The conjuncts remain **unclassified**. -/
theorem p8_fixed_field_status_P
    (hrootAt : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    (∀ ω : JointCoins K97cubic, nprSeed ω = servedSeed → alphaM ω = fixtureAlpha →
        (packageP hmoreM).strategy.Accepts ω cfgS.challenges.lam ∧
          ω ∉ ProductionP8Containment.FalseAcceptanceSet (packageP hmoreM).strategy 97 3 cfgS.challenges.lam) ∧
      (∀ ω ∈ ProductionP8Containment.FalseAcceptanceSet (packageP hmoreM).strategy 97 3 cfgS.challenges.lam,
        nprSeed ω ≠ 0 ∧ (nprSeed ω ≠ servedSeed ∨ alphaM ω ≠ fixtureAlpha)) ∧
      ((∀ ω : JointCoins K97cubic, (packageP hmoreM).strategy.Accepts ω cfgS.challenges.lam →
          nprSeed ω = servedSeed ∧ alphaM ω = fixtureAlpha) →
        ProductionP8Containment.FalseAcceptanceSet (packageP hmoreM).strategy 97 3 cfgS.challenges.lam = ∅) :=
  ⟨fun _ hz hα => ⟨packageP_accepts_fibre hmoreM hrootAt hz hα,
      falseAcceptanceP_disjoint_fibre hmoreM hrootAt hz hα⟩,
    falseAcceptanceP_off_fibre hmoreM hrootAt, falseAcceptanceP_empty_of_fibre_pinned hmoreM hrootAt⟩

end

end Nock.NockVMROM.Thm54.MultiRootPhaseCorrect

#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.ioAtWalkChallenges
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.uniformEndpoints_exist
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.phaseCompletion_nonempty
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.completionP
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.legacyFamilyP
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.assignmentP
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.legacyFamilyP_endpoints
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.acceptedFamilyDataP
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.acceptedFamilyP_response_length
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.legacyFamilyP_response_length
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.alphaMCommitmentP
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.walkArraysP
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.walkArraysP_reads_the_coin
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.mixedAssignmentP
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.mixedAssignmentP_satisfies
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.rawStrategyP
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.rawStrategyP_familyAt
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.rawStrategyP_messageAt
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.alphaMCommitmentP_same_across_coins
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.rawLegacyP
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.rawLegacyP_computeRowsAccepted
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.rawLegacyP_memoryRowsAccepted
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.rawLegacyP_computePubAt_zero
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.rawLegacyP_Ksz
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.rawLegacyP_requests
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.rawLegacyP_responses
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.honestVerifierGatesP
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.rawStrategyP_accepts
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.acceptedP_walk_challenges
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.honest_exactTopologyP
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.verifierP
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.verifierP_eq
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.verifierP_accepts
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.structuralChecksP
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.residualHonestP
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.packageP
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.statementP
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.packageP_verifier
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.packageP_accepts
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.coinP_not_zeroSeedFailureEvent
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.coinP_not_collisionFailureEvent
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.baseP_binding
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.coinP_not_specializedTopologyFailureEvent
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.coinP_not_guardedAxisFailureEvent
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.coinP_not_sizeWindowFailure
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.coinP_not_failureUnion
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.genuineTargetP
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.exists_package_accepting_every_challenge_pair
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.commit_then_sample_completeness
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.packageP_accepts_distinct_challenges
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.packageP_commitment_unchanged
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.packageP_regression
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.packageP_rejection_receipts
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.coin_eq_coinN
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.packageP_accepts_fibre
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.genuineTargetP_fibre
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.falseAcceptanceP_disjoint_fibre
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.falseAcceptanceP_off_fibre
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.falseAcceptanceP_empty_of_fibre_pinned
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.coinN_injective
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.acceptedRangeP_card
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.p8_fixed_field_status_P
