import Nock.NockVMROM.Thm54.MultiRootHonestArrays
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Accepting the two-serviced-root package at nonzero LogUp challenges

`MultiRootHonestArrays` makes the fully renderer-constructed package `packageHonestM` accept the
honest coin `coinM = ((0, 0), (4, servedSeed))`.  Both sampled LogUp challenges are zero there, and
the isolated compute-walk layer is degenerate at zero: the all-zero line/count/accumulator columns
satisfy every recurrence whatever the current-node, child and fanout data are, and the topology
`RLC^γ` collapses to projection onto coordinate zero.

This module removes that qualification.  The honest post-challenge message is rebuilt at an
**arbitrary** pair of sampled walk challenges `(a, g)` — nothing else in the construction moves,
because `AlphaMFamilyData.atCoins` is exactly the insertion of the two coins the prover cannot see
when it commits and `jointVerification_complete` is
generic in the family's `computeWalkAlpha`, `memoryWalkAlpha` and `walkGamma`.  The committed data
`MultiRootHonestCommitment.dataM`, the committed execution, the committed axis trees and the census
are all untouched; `statementM_of_arrays` still supplies the released fourteen-conjunct statement
through the unchanged `optimizedFullStrictNockVMROM_of_package`.

The specialization of record is `coinN alphaCN gammaN` with `alphaCN = 2` and `gammaN = 5`, the two
nonzero walk challenges the pre-compilation backend inputs `inputsM` already carry
(`MultiRootServedFixture`).  Alongside the acceptance this module compiles the two receipts which
say the collapsed layers are genuinely exercised at that coin:

* `nonzero_gamma_not_bad_for_unbound_tree` — the single-coordinate payload mutation which `γ = 0`
  hides is visible to every nonzero `γ`, so the topology compression at `gammaN` is a real test.
-/

namespace Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges

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
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97z : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97z : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)

/-! ## The two sampled walk challenges -/

/-- The sampled compute-walk challenge of record: nonzero. -/
def alphaCN : K97cubic := 2

/-- The sampled topology-compression challenge of record: nonzero. -/
def gammaN : K97cubic := 5

theorem alphaCN_ne_zero : alphaCN ≠ 0 := two_ne_zero_K97

theorem gammaN_ne_zero : gammaN ≠ 0 := by
  intro hk
  have hbase : (5 : F97) ≠ 0 := by decide
  apply hbase
  apply (algebraMap F97 K97cubic).injective
  simpa only [map_ofNat, map_zero, gammaN] using hk

/-! ## The raw family at an arbitrary pair of sampled walk challenges -/

/-- The committed post-`alphaM` data of `MultiRootHonestArrays`, with the two later coins inserted.  Only `computeWalkAlpha` and `walkGamma` move. -/
def rawFamilyN (a g : K97cubic) : RawPlusIOSegmentedFamily F97 K97cubic :=
  (familyDataM0 servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).atCoins a g

theorem rawFamilyN_coins (a g : K97cubic) :
    (rawFamilyN a g).computeWalkAlpha = a ∧ (rawFamilyN a g).walkGamma = g ∧
      (rawFamilyN a g).memoryWalkAlpha = fixtureAlpha :=
  ⟨rfl, rfl, rfl⟩

theorem rawFamilyN_problem (a g : K97cubic) : (rawFamilyN a g).problem = ⟨cfgS, execS⟩ :=
  specializedProblemM_honest

theorem rawFamilyN_tableAssumptions (a g : K97cubic) :
    (rawFamilyN a g).problem.TableCompletenessAssumptions :=
  rawZeroFamilyM_tableAssumptions

theorem rawFamilyN_progCapacity (a g : K97cubic) :
    (rawFamilyN a g).exec.derivedRequestIO.length + 1 ≤ 2 ^ (rawFamilyN a g).cfg.orbit.h :=
  rawZeroFamilyM_progCapacity

theorem rawFamilyN_memCapacity (a g : K97cubic) :
    (rawFamilyN a g).exec.derivedResponseIO.length + 1 ≤ 2 ^ (rawFamilyN a g).cfg.orbit.h :=
  rawZeroFamilyM_memCapacity

def legacyZeroFamilyN (a g : K97cubic) : PlusIOSegmentedFamily F97 K97cubic :=
  (rawFamilyN a g).toLegacy (rawFamilyN_tableAssumptions a g)
    (fun _ _ h => NodeEncoding.computeNodeEncode_labelOf_eq stateTagChar97 h)
    (fun _ _ h => NodeEncoding.memoryNodeEncode_labelOf_eq stateTagChar97 h)
    (rawFamilyN_progCapacity a g) (rawFamilyN_memCapacity a g)

theorem legacyZeroFamilyN_chained (a g : K97cubic) :
    ChainedSemanticExactLanguage (legacyZeroFamilyN a g).problem.cfg
      (legacyZeroFamilyN a g).problem.exec :=
  legacyZeroFamilyM_chained

def legacyZeroFamilyN_semanticWitness (a g : K97cubic) :
    SemanticIOWitness (legacyZeroFamilyN a g).problem.cfg
      (legacyZeroFamilyN a g).problem.exec :=
  legacyZeroFamilyM_semanticWitness

theorem legacyZeroFamilyN_KszBound (a g : K97cubic) :
    (legacyZeroFamilyN a g).problem.cfg.Ksz < ringChar K97cubic :=
  legacyZeroFamilyM_KszBound

/-! ## The honest post-challenge completion at those challenges -/

structure HonestCompletionN (a g : K97cubic) where
  requests : IOField K97cubic
  responses : IOField K97cubic
  outMem : IOField K97cubic
  assignment :
    JointAssignment
      ((legacyZeroFamilyN a g).withIOEndpoints requests responses outMem)
      (ringChar K97cubic)

theorem honestCompletionN_nonempty (a g : K97cubic) : Nonempty (HonestCompletionN a g) := by
  obtain ⟨requests, responses, outMem, ⟨A⟩⟩ :=
    jointVerification_complete (legacyZeroFamilyN a g)
      (legacyZeroFamilyN_chained a g) (legacyZeroFamilyN_semanticWitness a g)
      (legacyZeroFamilyN_KszBound a g)
  exact ⟨⟨requests, responses, outMem, A⟩⟩

noncomputable def honestCompletionN (a g : K97cubic) : HonestCompletionN a g :=
  Classical.choice (honestCompletionN_nonempty a g)

abbrev legacyFamilyN (a g : K97cubic) : PlusIOSegmentedFamily F97 K97cubic :=
  (legacyZeroFamilyN a g).withIOEndpoints (honestCompletionN a g).requests
    (honestCompletionN a g).responses (honestCompletionN a g).outMem

abbrev honestAssignmentN (a g : K97cubic) :
    PlusIOSameExecutionAssignment (legacyFamilyN a g) (ringChar K97cubic) :=
  (honestCompletionN a g).assignment.sameExecution

/-! ## The honest later-round message at those challenges -/

def acceptedFamilyDataN (a g : K97cubic) (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    AlphaMFamilyData timestampM z hz α lmb where
  compNodeWidth := NodeEncoding.computeNodeWidth
  compNodeEncode := NodeEncoding.computeNodeEncode stateTagChar97
  memNodeWidth := NodeEncoding.memoryNodeWidth
  memNodeEncode := NodeEncoding.memoryNodeEncode stateTagChar97
  requests := (honestCompletionN a g).requests
  responses := (honestCompletionN a g).responses
  outMem := (honestCompletionN a g).outMem

theorem acceptedFamilyN_response_length (a g : K97cubic) (z : K97cubic) (hz : z ≠ 0)
    (α lmb : K97cubic) :
    (acceptedFamilyDataN a g z hz α lmb).base.exec.derivedResponseIO.length = 3 :=
  responseLenM z hz α lmb

theorem honestAssignmentN_response_length (a g : K97cubic) :
    (legacyFamilyN a g).problem.exec.derivedResponseIO.length = 3 :=
  responseLenM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam

/-- The honest table and IO arrays of the completion at `(a, g)`. -/
def alphaMCommitmentN (a g : K97cubic) (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic) :
    AlphaMCommitment (p := ringChar K97cubic) timestampM z hz α lmb where
  familyData := acceptedFamilyDataN a g z hz α lmb
  tables :=
    { compute := (honestAssignmentN a g).computeTableAux
      memory := (honestAssignmentN a g).memoryTableAux }
  io :=
    { multiplicity := fun j =>
        (honestAssignmentN a g).exactIO.multiplicity
          ⟨j, by
            have hj := j.isLt
            have hsource := acceptedFamilyN_response_length a g z hz α lmb
            have htarget := honestAssignmentN_response_length a g
            omega⟩
      progAcc := (honestAssignmentN a g).exactIO.progAcc
      memAcc := (honestAssignmentN a g).exactIO.memAcc }

/-- The honest walk arrays of the same completion. -/
def walkArraysN (a g : K97cubic) (_ω : JointCoins K97cubic) (_lmb : K97cubic)
    (_hz : nprSeed _ω ≠ 0) :
    RawWalkArrays K97cubic where
  computeLn := (honestAssignmentN a g).computeWalk.ln
  computeCount := (honestAssignmentN a g).computeWalk.count
  computeAcc := (honestAssignmentN a g).computeWalk.acc
  memoryLn := (honestAssignmentN a g).memoryWalk.ln
  memoryCount := (honestAssignmentN a g).memoryWalk.count
  memoryAcc := (honestAssignmentN a g).memoryWalk.acc

/-- The honest coin at the sampled walk challenges `(a, g)`. -/
def coinN (a g : K97cubic) : JointCoins K97cubic := ((a, g), (fixtureAlpha, servedSeed))

theorem coinN_coordinates (a g : K97cubic) :
    alphaC (coinN a g) = a ∧ gamma (coinN a g) = g ∧
      alphaM (coinN a g) = fixtureAlpha ∧ nprSeed (coinN a g) = servedSeed :=
  ⟨rfl, rfl, rfl, rfl⟩

def rawStrategyN (a g : K97cubic) :
    TemplateRawJointSoundness.Strategy F97 K97cubic (ringChar K97cubic) where
  timestamp := timestampM
  afterAlphaM := alphaMCommitmentN a g
  afterCoins := walkArraysN a g

theorem rawStrategyN_familyAt (a g : K97cubic) :
    (rawStrategyN a g).familyAt (coinN a g) cfgS.challenges.lam seedM_ne =
      RawPlusIOSegmentedFamily.ofLegacy (legacyFamilyN a g) := rfl

theorem rawStrategyN_messageAt (a g : K97cubic) :
    (rawStrategyN a g).messageAt (coinN a g) cfgS.challenges.lam seedM_ne =
      RawMessage.ofLegacy (honestAssignmentN a g) := rfl

/-! ## The seventeen verifier gates at the nonzero coin -/

abbrev rawLegacyN (a g : K97cubic) : RawPlusIOSegmentedFamily F97 K97cubic :=
  RawPlusIOSegmentedFamily.ofLegacy (legacyFamilyN a g)

theorem rawLegacyN_computeRowsAccepted (a g : K97cubic) :
    (rawLegacyN a g).exec.ComputeRowsAccepted :=
  rawLegacyM_computeRowsAccepted

theorem rawLegacyN_memoryRowsAccepted (a g : K97cubic) :
    (rawLegacyN a g).exec.MemoryRowsAccepted :=
  rawLegacyM_memoryRowsAccepted

theorem rawLegacyN_computePubAt_zero (a g : K97cubic) :
    (rawLegacyN a g).exec.computePubAt ⟨0, (rawLegacyN a g).cfg.compRows_pos⟩ = parentPubS :=
  rawLegacyM_computePubAt_zero

theorem rawLegacyN_Ksz (a g : K97cubic) : (rawLegacyN a g).cfg.Ksz = 4 :=
  rawLegacyM_Ksz

theorem rawLegacyN_requests (a g : K97cubic) :
    (rawLegacyN a g).exec.derivedRequestIO =
      [NockVM.encRecFormR parentRecordS MemoryTable.formRDefault,
          NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault,
        NockVM.encRecFormR servedRecord MemoryTable.formRDefault] :=
  rawLegacyM_requests

theorem rawLegacyN_responses (a g : K97cubic) :
    (rawLegacyN a g).exec.derivedResponseIO =
      [NockVM.encRecFormR parentRecordS MemoryTable.formRDefault,
          NockVM.encRecFormR servedRecord MemoryTable.formRDefault,
        NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault] :=
  rawLegacyM_responses

theorem honestVerifierGatesN (a g : K97cubic) :
    (RawMessage.ofLegacy (honestAssignmentN a g)).VerifierGates skelM.publicClaim (coinN a g) := by
  refine ⟨seedM_ne, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact rowAlignment_of_rowsAcceptedM (rawLegacyN a g)
      (rawLegacyN_computeRowsAccepted a g) (rawLegacyN_memoryRowsAccepted a g)
  · refine ⟨rfl, ?_, rfl, ?_⟩
    · intro hchar
      have hh : hchar = stateTagChar97 := Subsingleton.elim _ _
      subst hchar
      rfl
    · intro hchar
      have hh : hchar = stateTagChar97 := Subsingleton.elim _ _
      subst hchar
      rfl
  · rw [rawLegacyN_computePubAt_zero, claimM]
    rfl
  · rw [rawLegacyN_computePubAt_zero, claimM]
    rfl
  · rw [rawLegacyN_computePubAt_zero, claimM]
    rfl
  · exact (honestCompletionN a g).assignment.public_endpoints.1
  · exact (honestCompletionN a g).assignment.public_endpoints.2
  · exact (honestAssignmentN a g).exactIO.multiplicity_ne_zero
  · rw [rawLegacyN_requests, rawLegacyN_Ksz]
    norm_num [IO.InRange]
  · rw [rawLegacyN_requests, ← derived_requestsS]
    exact requestsS_nodup
  · rw [rawLegacyN_responses, rawLegacyN_Ksz]
    norm_num
  · rw [rawLegacyN_responses, ← derived_responsesS]
    exact responsesS_nodup

theorem rawStrategyN_accepts_coinN (a g : K97cubic) :
    (rawStrategyN a g).Accepts (coinN a g) cfgS.challenges.lam := by
  apply ((rawStrategyN a g).accepts_iff_raw (coinN a g) cfgS.challenges.lam seedM_ne).2
  change (RawMessage.ofLegacy (honestAssignmentN a g)).Accepts skelM.publicClaim (coinN a g)
  exact RawMessage.accepts_of_legacy_assignment
    skelM.publicClaim (coinN a g) (honestAssignmentN a g)
    (honestCompletionN a g).assignment.sixFamilies (honestVerifierGatesN a g)

/-! ## The verifier accepts the nonzero coin -/

theorem honest_exactTopologyN (a g : K97cubic) :
    ComputeExactTopology ((rawStrategyN a g).familyAt (coinN a g) cfgS.challenges.lam seedM_ne).exec ∧
      MemoryExactTopology ((rawStrategyN a g).familyAt (coinN a g) cfgS.challenges.lam seedM_ne).exec := by
  change ComputeExactTopology
      (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec ∧
    MemoryExactTopology
      (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec
  rw [specializedProblemM_honest]
  exact ⟨compute_topologyS, memory_topologyS⟩

def verifierN (a g : K97cubic) :
    ProductionRawVerifier.TemplateAdapter.Strategy F97 K97cubic (ringChar K97cubic) :=
  HonestCommitment.verifierOf dataM (alphaMCommitmentN a g) (walkArraysN a g)

theorem verifierN_eq (a g : K97cubic) :
    verifierN a g = ProductionRawVerifier.TemplateAdapter.Strategy.honest (rawStrategyN a g) := rfl

theorem verifierN_accepts_coinN (a g : K97cubic) : (verifierN a g).Accepts (coinN a g) cfgS.challenges.lam :=
  ProductionRawVerifier.TemplateAdapter.Strategy.honest_accepts
    (rawStrategyN a g) (coinN a g) cfgS.challenges.lam seedM_ne (rawStrategyN_accepts_coinN a g)
    (honest_exactTopologyN a g)

theorem structuralChecksN (a g : K97cubic) :
    ProductionAxisStructureVerifier.structuralChecksAt (verifierN a g) servedSeed seedM_ne
      fixtureAlpha = true := by
  change
    (ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck templateM &&
      ProductionAxisStructureVerifier.noWrapCheck templateM fixtureAlpha) = true
  simp [alphaFreeAxisStructureM, noWrapM]

/-! ## The constructed package at the nonzero coin -/

def residualHonestN (a g : K97cubic) : BuildablePackage.CommitmentResidual multiRootExecution :=
  HonestCommitment.commitmentResidualOf dataM (alphaMCommitmentN a g) (walkArraysN a g)

theorem residualHonestN_generated (a g : K97cubic) :
    GeneratedField.ClaimGenerated K97cubic (residualHonestN a g).verifier.raw.claim
      (residualHonestN a g).Λ :=
  MultiRootHonestCommitment.residualOf_generated (alphaMCommitmentN a g) (walkArraysN a g)

/-- The fully renderer-constructed package whose later-round message is honest at `(a, g)`. -/
def packageHonestN (a g : K97cubic) :
    OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F97 K97cubic 4 :=
  BuildablePackage.buildFullPackage multiRootExecution inputsM (residualHonestN a g)
    inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
    (residualHonestN_generated a g) MultiRootHonestCommitment.f97_primeField

/-- The released fourteen-conjunct statement over this package, through the unchanged
`statementM_of_arrays`. -/
theorem statementHonestN (a g : K97cubic)
    (hax : FormRAxisBound (packageHonestN hmoreM a g).optimized.sampled
      (packageHonestN hmoreM a g).optimized.basis)
    (hbasis : FormRBasis (packageHonestN hmoreM a g).optimized.basis)
    (hwidth : FormRWidth F97) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageHonestN hmoreM a g) :=
  statementM_of_arrays hmoreM (alphaMCommitmentN a g) (walkArraysN a g) hax hbasis hwidth

theorem packageHonestN_verifier (a g : K97cubic) :
    (packageHonestN hmoreM a g).strategy.verifier = verifierN a g := rfl

/-- The walk RAPs discharged by the acceptance are the ones carrying the sampled challenges: the
accepted family's own compute-walk challenge is `a` and its topology-compression challenge is `g`. -/
theorem acceptedN_walk_challenges (a g : K97cubic) :
    ((rawStrategyN a g).familyAt (coinN a g) cfgS.challenges.lam seedM_ne).computeWalkAlpha = a ∧
      ((rawStrategyN a g).familyAt (coinN a g) cfgS.challenges.lam seedM_ne).walkGamma = g ∧
      ((rawStrategyN a g).familyAt (coinN a g) cfgS.challenges.lam seedM_ne).memoryWalkAlpha = fixtureAlpha ∧
      (∀ kind, (((rawStrategyN a g).familyAt (coinN a g) cfgS.challenges.lam seedM_ne).computeWalkRAP kind).Satisfies
        ((rawStrategyN a g).messageAt (coinN a g) cfgS.challenges.lam seedM_ne).computeWalkTrace) ∧
      (∀ kind, (((rawStrategyN a g).familyAt (coinN a g) cfgS.challenges.lam seedM_ne).memoryWalkRAP kind).Satisfies
        ((rawStrategyN a g).messageAt (coinN a g) cfgS.challenges.lam seedM_ne).memoryWalkTrace) := by
  have h := ((rawStrategyN a g).accepts_iff_six_families (coinN a g) cfgS.challenges.lam seedM_ne).1
    (rawStrategyN_accepts_coinN a g)
  exact ⟨rfl, rfl, rfl, h.2.2.2.1, h.2.2.2.2.1⟩

/-- Relaxis remaining: dummy-wired `RootAxisBoundaryAt` (form R leftover). -/
theorem packageHonestN_accepts
    (a g : K97cubic)
    (hrootAt : (packageHonestN hmoreM a g).strategy.RootAxisBoundaryAt
      (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    (packageHonestN hmoreM a g).strategy.Accepts (coinN a g) cfgS.challenges.lam := by
  apply ((packageHonestN hmoreM a g).strategy.accepts_iff (coinN a g) cfgS.challenges.lam seedM_ne).2
  constructor
  · apply (ProductionAxisStructureVerifier.accepts_iff (verifierN a g) (coinN a g) cfgS.challenges.lam seedM_ne).2
    exact ⟨((verifierN a g).accepts_iff_production (coinN a g) cfgS.challenges.lam seedM_ne).1
      (verifierN_accepts_coinN a g), structuralChecksN a g⟩
  · exact hrootAt

/-! ## The nonzero coin lies outside the five counted failure events -/

theorem coinN_not_zeroSeedFailureEvent (a g : K97cubic) :
    coinN a g ∉ (zeroSeedFailureEvent : Finset (JointCoins K97cubic)) := by
  rw [mem_zeroSeedFailureEvent_iff]
  change (servedSeed : K97cubic) ≠ 0
  exact seedM_ne

theorem coinN_not_collisionFailureEvent (a g : K97cubic) :
    coinN a g ∉ collisionFailureEvent censusM.census := by
  rw [mem_collisionFailureEvent_iff]
  intro h
  exact coinM_not_collisionFailureEvent ((mem_collisionFailureEvent_iff _ coinM).2 h)

theorem baseN_binding (a g : K97cubic) :
    RawTopologyBindingResidual
      (acceptedFamilyDataN a g servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).base :=
  baseM_binding

theorem coinN_not_specializedTopologyFailureEvent (a g : K97cubic) :
    coinN a g ∉ specializedTopologyFailureEvent (verifierN a g).raw cfgS.challenges.lam := by
  rw [mem_specializedTopologyFailureEvent_iff]
  rintro ⟨hz, hbad⟩
  change g ∈
    topologyBadGammas (acceptedFamilyDataN a g servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).base at hbad
  rw [topologyBadGammas_empty_of_binding _ (baseN_binding a g)] at hbad
  exact absurd hbad (Finset.notMem_empty _)

theorem coinN_not_guardedAxisFailureEvent (a g : K97cubic) :
    coinN a g ∉
      ProductionP8Containment.guardedAxisFailureEvent (packageHonestN hmoreM a g).strategy
        cfgS.challenges.lam := by
  intro h
  exact coinM_not_guardedAxisFailureEvent hmoreM
    (ProductionP8Containment.mem_guardedAxisFailureEvent_iff _ _ coinM |>.2
      ((ProductionP8Containment.mem_guardedAxisFailureEvent_iff _ _ (coinN a g)).1 h))

theorem coinN_not_sizeWindowFailure (a g : K97cubic) :
    coinN a g ∉ SizeWindowCounting.SizeWindowFailure skelM := by
  intro h
  exact coinM_not_sizeWindowFailure
    ((SizeWindowCounting.mem_SizeWindowFailure_iff _ coinM).2
      ((SizeWindowCounting.mem_SizeWindowFailure_iff _ (coinN a g)).1 h))

theorem coinN_not_failureUnion (a g : K97cubic) :
    coinN a g ∉ ProductionP8Containment.FailureUnion (packageHonestN hmoreM a g).strategy
      (packageHonestN hmoreM a g).optimized.census cfgS.challenges.lam := by
  intro hbad
  simp only [ProductionP8Containment.FailureUnion, Finset.mem_union] at hbad
  rcases hbad with hbad | hbad
  · rcases hbad with hbad | hbad
    · rcases hbad with hbad | hbad
      · rcases hbad with hbad | hbad
        · exact coinN_not_zeroSeedFailureEvent a g hbad
        · exact coinN_not_collisionFailureEvent a g hbad
      · exact coinN_not_specializedTopologyFailureEvent a g hbad
    · exact coinN_not_guardedAxisFailureEvent hmoreM a g hbad
  · exact coinN_not_sizeWindowFailure a g hbad


/-- **The genuine target is reached at the nonzero-challenge coin.** -/
theorem genuineTargetN (a g : K97cubic)
    (hrootAt : (packageHonestN hmoreM a g).strategy.RootAxisBoundaryAt
      (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    ProductionP8Containment.GenuineTargetAt (packageHonestN hmoreM a g).strategy 97 3 (coinN a g) cfgS.challenges.lam :=
  (packageHonestN hmoreM a g).containment (coinN a g) cfgS.challenges.lam
    (packageHonestN_accepts hmoreM a g hrootAt)
    (coinN_not_failureUnion hmoreM a g)

theorem packageHonestN_acceptance_nonempty (a g : K97cubic)
    (hrootAt : (packageHonestN hmoreM a g).strategy.RootAxisBoundaryAt
      (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    ∃ ω : JointCoins K97cubic, (packageHonestN hmoreM a g).strategy.Accepts ω cfgS.challenges.lam :=
  ⟨coinN a g, packageHonestN_accepts hmoreM a g hrootAt⟩

theorem containmentN_is_informative (a g : K97cubic)
    (hrootAt : (packageHonestN hmoreM a g).strategy.RootAxisBoundaryAt
      (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g)))
    (hax : FormRAxisBound (packageHonestN hmoreM a g).optimized.sampled
      (packageHonestN hmoreM a g).optimized.basis)
    (hbasis : FormRBasis (packageHonestN hmoreM a g).optimized.basis)
    (hwidth : FormRWidth F97) :
    (packageHonestN hmoreM a g).strategy.Accepts (coinN a g) cfgS.challenges.lam ∧
      coinN a g ∉ ProductionP8Containment.FailureUnion (packageHonestN hmoreM a g).strategy
        (packageHonestN hmoreM a g).optimized.census cfgS.challenges.lam ∧
      ProductionP8Containment.GenuineTargetAt (packageHonestN hmoreM a g).strategy 97 3 (coinN a g) cfgS.challenges.lam ∧
      (∀ ω : JointCoins K97cubic, (packageHonestN hmoreM a g).strategy.Accepts ω cfgS.challenges.lam →
        ω ∉ ProductionP8Containment.FailureUnion (packageHonestN hmoreM a g).strategy
          (packageHonestN hmoreM a g).optimized.census cfgS.challenges.lam →
        ProductionP8Containment.GenuineTargetAt (packageHonestN hmoreM a g).strategy 97 3 ω cfgS.challenges.lam) :=
  ⟨packageHonestN_accepts hmoreM a g hrootAt, coinN_not_failureUnion hmoreM a g,
    genuineTargetN hmoreM a g hrootAt,
    fun ω => (statementHonestN hmoreM a g hax hbasis hwidth).containment ω cfgS.challenges.lam⟩

/-! ## The witness of record, at `alphaC = 2` and `gamma = 5` -/

/-- The accepted coin of record: **both** LogUp challenges are nonzero. -/
def coinNonzero : JointCoins K97cubic := coinN alphaCN gammaN

theorem coinNonzero_challenges_ne_zero :
    alphaC coinNonzero ≠ 0 ∧ gamma coinNonzero ≠ 0 :=
  ⟨alphaCN_ne_zero, gammaN_ne_zero⟩

def packageNonzero : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F97 K97cubic 4 :=
  packageHonestN hmoreM alphaCN gammaN

theorem statementNonzero
    (hax : FormRAxisBound (packageNonzero hmoreM).optimized.sampled
      (packageNonzero hmoreM).optimized.basis)
    (hbasis : FormRBasis (packageNonzero hmoreM).optimized.basis)
    (hwidth : FormRWidth F97) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageNonzero hmoreM) :=
  statementHonestN hmoreM alphaCN gammaN hax hbasis hwidth

theorem packageNonzero_accepts
    (hrootAt : (packageNonzero hmoreM).strategy.RootAxisBoundaryAt
      (nprSeed coinNonzero) seedM_ne (alphaM coinNonzero)) :
    (packageNonzero hmoreM).strategy.Accepts coinNonzero cfgS.challenges.lam :=
  packageHonestN_accepts hmoreM alphaCN gammaN hrootAt

theorem coinNonzero_not_failureUnion :
    coinNonzero ∉ ProductionP8Containment.FailureUnion (packageNonzero hmoreM).strategy
      (packageNonzero hmoreM).optimized.census cfgS.challenges.lam :=
  coinN_not_failureUnion hmoreM alphaCN gammaN

theorem genuineTargetNonzero
    (hrootAt : (packageNonzero hmoreM).strategy.RootAxisBoundaryAt
      (nprSeed coinNonzero) seedM_ne (alphaM coinNonzero)) :
    ProductionP8Containment.GenuineTargetAt (packageNonzero hmoreM).strategy 97 3 coinNonzero cfgS.challenges.lam :=
  genuineTargetN hmoreM alphaCN gammaN hrootAt

/-- The whole delivery in one statement: a nonzero-challenge accepted coin at a fully
renderer-constructed package, outside the failure union, reaching the genuine target under the
released containment implication. -/
theorem nonzero_challenge_witness
    (hrootAt : (packageNonzero hmoreM).strategy.RootAxisBoundaryAt
      (nprSeed coinNonzero) seedM_ne (alphaM coinNonzero))
    (hax : FormRAxisBound (packageNonzero hmoreM).optimized.sampled
      (packageNonzero hmoreM).optimized.basis)
    (hbasis : FormRBasis (packageNonzero hmoreM).optimized.basis)
    (hwidth : FormRWidth F97) :
    alphaC coinNonzero ≠ 0 ∧ gamma coinNonzero ≠ 0 ∧
      (packageNonzero hmoreM).strategy.Accepts coinNonzero cfgS.challenges.lam ∧
      coinNonzero ∉ ProductionP8Containment.FailureUnion (packageNonzero hmoreM).strategy
        (packageNonzero hmoreM).optimized.census cfgS.challenges.lam ∧
      ProductionP8Containment.GenuineTargetAt (packageNonzero hmoreM).strategy 97 3 coinNonzero cfgS.challenges.lam ∧
      OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageNonzero hmoreM) :=
  ⟨alphaCN_ne_zero, gammaN_ne_zero, packageNonzero_accepts hmoreM hrootAt, coinNonzero_not_failureUnion hmoreM,
    genuineTargetNonzero hmoreM hrootAt, statementNonzero hmoreM hax hbasis hwidth⟩

theorem packageNonzero_regression :
    (packageNonzero hmoreM).objects.cfg = cfgS ∧
      (packageNonzero hmoreM).objects.exec = execS ∧
      (packageNonzero hmoreM).computeChip.rap.w = 303 ∧
      (packageNonzero hmoreM).computeChip.rap.s = 418 ∧
      (packageNonzero hmoreM).memoryChip.rap.w = 205 ∧ (packageNonzero hmoreM).memoryChip.rap.s = 156 ∧
      (packageNonzero hmoreM).computeChip.rap.H.card = 2 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact (BuildablePackage.constructed_resources multiRootExecution inputsM
      (residualHonestN alphaCN gammaN) inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      (residualHonestN_generated alphaCN gammaN) MultiRootHonestCommitment.f97_primeField).1
  · exact (BuildablePackage.constructed_resources multiRootExecution inputsM
      (residualHonestN alphaCN gammaN) inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      (residualHonestN_generated alphaCN gammaN) MultiRootHonestCommitment.f97_primeField).2.1
  · exact (BuildablePackage.constructed_resources multiRootExecution inputsM
      (residualHonestN alphaCN gammaN) inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      (residualHonestN_generated alphaCN gammaN) MultiRootHonestCommitment.f97_primeField).2.2.1
  · exact (BuildablePackage.constructed_resources multiRootExecution inputsM
      (residualHonestN alphaCN gammaN) inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      (residualHonestN_generated alphaCN gammaN) MultiRootHonestCommitment.f97_primeField).2.2.2
  · exact (BuildablePackage.constructed_row_budgets multiRootExecution inputsM
      (residualHonestN alphaCN gammaN) inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      (residualHonestN_generated alphaCN gammaN) MultiRootHonestCommitment.f97_primeField).1

/-! ## Receipt 1: the isolated compute walk is exercised only at a nonzero challenge

The three columns below are that control's data, verbatim.  The theorem
`altered_walk_accepting_challenge_iff` says the set of challenges at which the isolated walk layer
accepts it is exactly `{0}`, so at `alphaCN` the same altered walk is
rejected. -/

def alteredCurN : ℕ → K97cubic
  | 1 => 1
  | 2 => 1
  | _ => 0

def alteredChildN : ℕ → ℕ → K97cubic := fun _ _ => 0
def alteredFanoutN : ℕ → ℕ := fun _ => 0

theorem alteredN_not_isFullBFT :
    ¬ IsFullBFT alteredCurN alteredChildN alteredFanoutN 2 := by
  intro h
  have hc := congrArg (fun p : K97cubic[X] => p.coeff 2) h
  norm_num [IsFullBFT, nodeListP, nodeQueueP, queueTerm, alteredCurN,
    alteredChildN, alteredFanoutN, Sf, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at hc
  have hx : (Polynomial.X : K97cubic[X]).coeff 2 = 0 := by
    rw [Polynomial.coeff_X]
    norm_num
  rw [hx] at hc
  exact one_ne_zero hc

theorem nodeListP_alteredN_eval (α : K97cubic) :
    (nodeListP alteredCurN 2).eval α = α + α ^ 2 := by
  have hIcc : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := rfl
  simp [nodeListP, hIcc, alteredCurN]

theorem nodeQueueP_alteredN_eval (α : K97cubic) :
    (nodeQueueP alteredCurN alteredChildN alteredFanoutN 2).eval α = α := by
  have hIcc : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := rfl
  simp [nodeQueueP, queueTerm, alteredFanoutN, hIcc, alteredCurN]

/-- **The decisive walk-layer receipt.**  The isolated walk layer accepts the altered non-BFT walk
at exactly one sampled challenge, `alphaC = 0`. -/
theorem altered_walk_accepting_challenge_iff (α : K97cubic) :
    (∃ ln count acc : ℕ → K97cubic,
        WalkSat alteredCurN alteredChildN alteredFanoutN ln count acc α (alteredCurN 1 * α) α 2 ∧
          acc 2 = 0) ↔ α = 0 := by
  constructor
  · rintro ⟨ln, count, acc, hw, hacc⟩
    have h := (walk_out_zero_iff hw rfl rfl).1 hacc
    rw [nodeListP_alteredN_eval, nodeQueueP_alteredN_eval] at h
    have hsq : α ^ 2 = 0 := by linear_combination h
    exact pow_eq_zero_iff (two_ne_zero) |>.1 hsq
  · rintro rfl
    refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, ?_, rfl⟩
    refine
      { hpos := by norm_num
        ln1 := rfl
        lnInc := ?_
        count1 := ?_
        countInc := ?_
        accInit := ?_
        accStep := ?_ }
    · intro i _ _; simp
    · simp
    · intro i _ _; simp
    · simp [alteredFanoutN]
    · intro i _ _; simp [alteredFanoutN]

/-- The same
materially altered non-BFT walk is now rejected: no line/count/accumulator columns close it at
`alphaCN`. -/
theorem altered_non_bft_walk_rejected_at_alphaCN :
    ¬ IsFullBFT alteredCurN alteredChildN alteredFanoutN 2 ∧
      ¬ ∃ ln count acc : ℕ → K97cubic,
          WalkSat alteredCurN alteredChildN alteredFanoutN ln count acc alphaCN
            (alteredCurN 1 * alphaCN) alphaCN 2 ∧ acc 2 = 0 :=
  ⟨alteredN_not_isFullBFT,
    fun h => alphaCN_ne_zero ((altered_walk_accepting_challenge_iff alphaCN).1 h)⟩

theorem altered_non_bft_walk_accepts_at_zero :
    ¬ IsFullBFT alteredCurN alteredChildN alteredFanoutN 2 ∧
      ∃ ln count acc : ℕ → K97cubic,
        WalkSat alteredCurN alteredChildN alteredFanoutN ln count acc 0
          (alteredCurN 1 * 0) 0 2 ∧ acc 2 = 0 :=
  ⟨alteredN_not_isFullBFT, (altered_walk_accepting_challenge_iff 0).2 rfl⟩

/-! ## Receipt 2: the topology compression is exercised only at a nonzero challenge -/

/-- A single-coordinate unit shift moves the `RLC^γ` by exactly `γ ^ c₀`. -/
theorem rlc_of_single_unit_shift {K : Type} [Field K] {n : ℕ} (γ : K) (c₀ : Fin n)
    (v w : Fin n → K) (h : ∀ c, v c = w c + (if c = c₀ then 1 else 0)) :
    rlc γ v = rlc γ w + γ ^ (c₀ : ℕ) := by
  simp only [rlc, h, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ c₀ (fun c : Fin n => γ ^ (c : ℕ))]
  simp

/-- One non-leading coordinate of the child payload is altered. -/
def badServedPubN : ComputeTable.Pub K97cubic :=
  { servedPub with s := { servedPub.s with dyck := servedPub.s.dyck + 1 } }

def badServedRowN : ComputeTable.State × ComputeTable.DTcomp K97cubic :=
  (.s0, (servedInputs, badServedPubN, servedDec))

def badComputeTreeN : NTree (ComputeTable.State × ComputeTable.DTcomp K97cubic) :=
  .node parentRowS [.node badServedRowN []]

/-- The mutation is exactly a unit shift of compute coordinate `1`, the child subject's `dyck`
fingerprint; every other coordinate of the actual and expected payloads agrees. -/
theorem badComputeTreeN_single_unit_shift (c : Fin 9) :
    ComputeLinkPayload.encode (computeActualPayload badComputeTreeN 0) c =
      ComputeLinkPayload.encode (computeExpectedPayload badComputeTreeN 0) c +
        (if c = 1 then 1 else 0) := by
  fin_cases c <;>
    simp [computeActualPayload, computeExpectedPayload, badComputeTreeN, badServedRowN,
      badServedPubN, ComputeLinkPayload.encode, ComputeLinkPayload.ofTriple,
      NTree.childLabel, NTree.childOpt, parentRowS, parentPubS, servedPub,
      ComputeTable.sfTriple]

theorem bad_compute_payloads_differN :
    ComputeLinkPayload.encode (computeActualPayload badComputeTreeN 0) ≠
      ComputeLinkPayload.encode (computeExpectedPayload badComputeTreeN 0) := by
  intro h
  have hdyck := congrFun h (1 : Fin 9)
  rw [badComputeTreeN_single_unit_shift (1 : Fin 9)] at hdyck
  simp at hdyck

theorem badComputeTreeN_slot_active :
    (((0 : Fin 3) : ℕ)) < ComputeTable.fanoutComp badComputeTreeN.label.1 := by
  simp [badComputeTreeN, parentRowS, ComputeTable.fanoutComp]

theorem zero_is_bad_gamma_for_unbound_treeN :
    (0 : K97cubic) ∈ computeSlotBadGammas badComputeTreeN 0 := by
  rw [computeSlotBadGammas, dif_pos badComputeTreeN_slot_active,
    dif_pos bad_compute_payloads_differN]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [rlc_of_single_unit_shift 0 (1 : Fin 9) _ _ badComputeTreeN_single_unit_shift]
  simp

/-- **Every nonzero `γ` sees it.**  The topology compression at `gammaN` is therefore a real test
rather than a projection onto coordinate zero. -/
theorem nonzero_gamma_not_bad_for_unbound_treeN (γ : K97cubic) (hγ : γ ≠ 0) :
    γ ∉ computeSlotBadGammas badComputeTreeN 0 := by
  rw [computeSlotBadGammas, dif_pos badComputeTreeN_slot_active,
    dif_pos bad_compute_payloads_differN]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [rlc_of_single_unit_shift γ (1 : Fin 9) _ _ badComputeTreeN_single_unit_shift]
  intro heq
  exact hγ (by simpa using heq)

theorem gammaN_not_bad_for_unbound_treeN :
    gammaN ∉ computeSlotBadGammas badComputeTreeN 0 :=
  nonzero_gamma_not_bad_for_unbound_treeN gammaN gammaN_ne_zero

theorem nonzero_coin_exercises_both_layers :
    ((0 : K97cubic) ∈ computeSlotBadGammas badComputeTreeN 0 ∧
        gamma coinNonzero ∉ computeSlotBadGammas badComputeTreeN 0) ∧
      ((∃ ln count acc : ℕ → K97cubic,
          WalkSat alteredCurN alteredChildN alteredFanoutN ln count acc 0
            (alteredCurN 1 * 0) 0 2 ∧ acc 2 = 0) ∧
        ¬ ∃ ln count acc : ℕ → K97cubic,
          WalkSat alteredCurN alteredChildN alteredFanoutN ln count acc (alphaC coinNonzero)
            (alteredCurN 1 * alphaC coinNonzero) (alphaC coinNonzero) 2 ∧ acc 2 = 0) :=
  ⟨⟨zero_is_bad_gamma_for_unbound_treeN, gammaN_not_bad_for_unbound_treeN⟩,
    ⟨altered_non_bft_walk_accepts_at_zero.2, altered_non_bft_walk_rejected_at_alphaCN.2⟩⟩

/-! ## Where the two `p8_fixed_field_*` conjuncts stand

The two theorems below
localize the remaining question rather than pretending to settle it: a false acceptance must be an
accepted coin **inside** the failure union, and no accepted coin has a zero NPR seed, so only the
collision, specialized-topology, guarded-axis and size-window components can host one.  The coin of
record is outside all four. -/

theorem accepts_seed_ne_zero
    {T : ProductionP8Containment.ProductionStrategy F97 K97cubic} {ω : JointCoins K97cubic}
    {lmb : K97cubic} (h : T.Accepts ω lmb) : nprSeed ω ≠ 0 := by
  by_contra hz
  rw [ProductionP8Containment.ProductionStrategy.Accepts, dif_neg (not_not_intro hz)] at h
  exact h

/-- **A false acceptance would have to be an accepted coin inside the failure union.**  This is the
contrapositive of the released `containment` conjunct on the constructed package. -/
theorem falseAcceptanceN_subset_accepted_inside_failureUnion (a g : K97cubic)
    (hax : FormRAxisBound (packageHonestN hmoreM a g).optimized.sampled
      (packageHonestN hmoreM a g).optimized.basis)
    (hbasis : FormRBasis (packageHonestN hmoreM a g).optimized.basis)
    (hwidth : FormRWidth F97) :
    ProductionP8Containment.FalseAcceptanceSet (packageHonestN hmoreM a g).strategy 97 3 cfgS.challenges.lam ⊆
      Finset.univ.filter fun ω =>
        (packageHonestN hmoreM a g).strategy.Accepts ω cfgS.challenges.lam ∧
          ω ∈ ProductionP8Containment.FailureUnion (packageHonestN hmoreM a g).strategy
            (packageHonestN hmoreM a g).optimized.census cfgS.challenges.lam := by
  intro ω hω
  rw [ProductionP8Containment.mem_falseAcceptanceSet_iff] at hω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hω.1, ?_⟩
  by_contra hout
  exact hω.2 ((statementHonestN hmoreM a g hax hbasis hwidth).containment ω cfgS.challenges.lam hω.1 hout)

/-- Sharper: the zero-seed component of the union cannot host one, because acceptance already
forces a nonzero NPR seed. -/
theorem falseAcceptanceN_not_zeroSeed (a g : K97cubic)
    (hax : FormRAxisBound (packageHonestN hmoreM a g).optimized.sampled
      (packageHonestN hmoreM a g).optimized.basis)
    (hbasis : FormRBasis (packageHonestN hmoreM a g).optimized.basis)
    (hwidth : FormRWidth F97) :
    ∀ ω ∈ ProductionP8Containment.FalseAcceptanceSet (packageHonestN hmoreM a g).strategy 97 3 cfgS.challenges.lam,
      ω ∉ (zeroSeedFailureEvent : Finset (JointCoins K97cubic)) ∧
        ω ∈ ProductionP8Containment.FailureUnion (packageHonestN hmoreM a g).strategy
          (packageHonestN hmoreM a g).optimized.census cfgS.challenges.lam := by
  intro ω hω
  have hmem := falseAcceptanceN_subset_accepted_inside_failureUnion hmoreM a g hax hbasis hwidth hω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  refine ⟨?_, hmem.2⟩
  rw [mem_zeroSeedFailureEvent_iff]
  exact accepts_seed_ne_zero hmem.1

/-- The exhibited accepted coin is not such a witness, so nothing here inhabits the set. -/
theorem coinNonzero_not_falseAcceptance
    (hrootAt : (packageNonzero hmoreM).strategy.RootAxisBoundaryAt
      (nprSeed coinNonzero) seedM_ne (alphaM coinNonzero)) :
    coinNonzero ∉ ProductionP8Containment.FalseAcceptanceSet (packageNonzero hmoreM).strategy 97 3 cfgS.challenges.lam := by
  rw [ProductionP8Containment.mem_falseAcceptanceSet_iff]
  exact fun h => h.2 (genuineTargetNonzero hmoreM hrootAt)

/-- The recorded state of the two conjuncts at this witness, with no upgrade smuggled in: the
production acceptance set is non-empty, every false acceptance is an accepted coin inside the
failure union with a nonzero seed, and the exhibited accepted coin is not one. -/
theorem p8_fixed_field_status
    (hrootAt : (packageNonzero hmoreM).strategy.RootAxisBoundaryAt
      (nprSeed coinNonzero) seedM_ne (alphaM coinNonzero))
    (hax : FormRAxisBound (packageNonzero hmoreM).optimized.sampled
      (packageNonzero hmoreM).optimized.basis)
    (hbasis : FormRBasis (packageNonzero hmoreM).optimized.basis)
    (hwidth : FormRWidth F97) :
    (∃ ω : JointCoins K97cubic, (packageNonzero hmoreM).strategy.Accepts ω cfgS.challenges.lam) ∧
      (ProductionP8Containment.FalseAcceptanceSet (packageNonzero hmoreM).strategy 97 3 cfgS.challenges.lam ⊆
        Finset.univ.filter fun ω =>
          (packageNonzero hmoreM).strategy.Accepts ω cfgS.challenges.lam ∧
            ω ∈ ProductionP8Containment.FailureUnion (packageNonzero hmoreM).strategy
              (packageNonzero hmoreM).optimized.census cfgS.challenges.lam) ∧
      coinNonzero ∉ ProductionP8Containment.FalseAcceptanceSet (packageNonzero hmoreM).strategy 97 3 cfgS.challenges.lam :=
  ⟨packageHonestN_acceptance_nonempty hmoreM alphaCN gammaN hrootAt,
    falseAcceptanceN_subset_accepted_inside_failureUnion hmoreM alphaCN gammaN hax hbasis hwidth,
    coinNonzero_not_falseAcceptance hmoreM hrootAt⟩

end

end Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges

#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.alphaCN_ne_zero
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.gammaN_ne_zero
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.rawFamilyN_coins
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.rawFamilyN_problem
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.legacyZeroFamilyN_chained
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.legacyZeroFamilyN_semanticWitness
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.legacyZeroFamilyN_KszBound
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.honestCompletionN_nonempty
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.alphaMCommitmentN
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.walkArraysN
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.coinN_coordinates
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.rawStrategyN_familyAt
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.rawStrategyN_messageAt
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.honestVerifierGatesN
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.rawStrategyN_accepts_coinN
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.honest_exactTopologyN
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.verifierN
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.verifierN_accepts_coinN
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.structuralChecksN
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.residualHonestN
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.packageHonestN
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.statementHonestN
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.acceptedN_walk_challenges
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.packageHonestN_accepts
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.coinN_not_zeroSeedFailureEvent
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.coinN_not_collisionFailureEvent
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.baseN_binding
#print axioms
  Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.coinN_not_specializedTopologyFailureEvent
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.coinN_not_guardedAxisFailureEvent
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.coinN_not_sizeWindowFailure
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.coinN_not_failureUnion
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.genuineTargetN
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.packageHonestN_acceptance_nonempty
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.containmentN_is_informative
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.coinNonzero
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.coinNonzero_challenges_ne_zero
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.packageNonzero
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.statementNonzero
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.packageNonzero_accepts
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.coinNonzero_not_failureUnion
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.genuineTargetNonzero
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.nonzero_challenge_witness
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.packageNonzero_regression
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.alteredN_not_isFullBFT
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.nodeListP_alteredN_eval
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.nodeQueueP_alteredN_eval
#print axioms
  Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.altered_walk_accepting_challenge_iff
#print axioms
  Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.altered_non_bft_walk_rejected_at_alphaCN
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.altered_non_bft_walk_accepts_at_zero
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.rlc_of_single_unit_shift
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.badComputeTreeN_single_unit_shift
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.bad_compute_payloads_differN
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.zero_is_bad_gamma_for_unbound_treeN
#print axioms
  Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.nonzero_gamma_not_bad_for_unbound_treeN
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.gammaN_not_bad_for_unbound_treeN
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.nonzero_coin_exercises_both_layers
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.accepts_seed_ne_zero
#print axioms
  Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.falseAcceptanceN_subset_accepted_inside_failureUnion
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.falseAcceptanceN_not_zeroSeed
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.coinNonzero_not_falseAcceptance
#print axioms Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges.p8_fixed_field_status
