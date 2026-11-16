import Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
import Nock.RedTeam.Batch80Thm54NonzeroChallenges
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# One phase-correct package and the committed fibre

Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

The load-bearing question is the mixed six-family assignment.  The receipts below
separate the four definitionally challenge-independent table/IO terms from the two
walk terms at the sampled pair.  They also check the endpoint transport field by
field, the quantifier order and commitment chronology, direct non-constancy of the
post-coin walk response, the preserved malformed controls, and the exact committed
fibre excluded from false acceptance.
-/

namespace Nock.RedTeam.Batch81

open scoped Classical Polynomial
open Nock Nock.Noun Nock.Walk Nock.NockVMROM
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.MultiRootHonestArrays
open Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)

variable (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
    (packageP hmoreM).optimized.basis)
variable (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)

/-- Form R width at F97 (`Nat.size 97 = 7`). -/
theorem formRWidthP : FormRWidth F97 := formRWidth97

/-! ## A. The four reference families are literally challenge-independent -/

/-- Exhaustive family-level receipt: changing `(alphaC,gamma)` changes exactly the
walk challenge fields.  The exact problem, encoders, endpoints and capacities are
the reference family's fields because the whole record is `withWalkChallenges`. -/
theorem family_is_reference_with_only_walk_challenges (a g : K97cubic) :
    legacyFamilyP a g =
      (legacyFamilyP 0 0).withWalkChallenges a g fixtureAlpha :=
  rfl

/-- The four reused RAP objects are the same terms at every pair, not merely
extensionally equivalent predicates.  Only the two walk RAPs are omitted here. -/
theorem four_nonwalk_RAPs_are_definitionally_pair_independent
    (a g a' g' : K97cubic) (kind : Nock.Reified.ConstraintKind) :
    (legacyFamilyP a g).computeTableRAP kind =
        (legacyFamilyP a' g').computeTableRAP kind ∧
      (legacyFamilyP a g).memoryTableRAP kind =
        (legacyFamilyP a' g').memoryTableRAP kind ∧
      (legacyFamilyP a g).computeIORAP kind =
        (legacyFamilyP a' g').computeIORAP kind ∧
      (legacyFamilyP a g).memoryIORAP kind =
        (legacyFamilyP a' g').memoryIORAP kind :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The corresponding four traces in the mixed assignment are also literally the
reference traces.  This checks both sides of each reused satisfaction judgment. -/
theorem four_nonwalk_traces_are_definitionally_reference_terms (a g : K97cubic) :
    (mixedAssignmentP a g).computeTableTrace =
        (assignmentP 0 0).computeTableTrace ∧
      (mixedAssignmentP a g).memoryTableTrace =
        (assignmentP 0 0).memoryTableTrace ∧
      (mixedAssignmentP a g).computeIOTrace =
        (assignmentP 0 0).computeIOTrace ∧
      (mixedAssignmentP a g).memoryIOTrace =
        (assignmentP 0 0).memoryIOTrace :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- At proposition level, all four reused family/trace satisfaction terms reduce
definitionally to the reference assignment's terms. -/
theorem four_nonwalk_satisfaction_terms_are_reference (a g : K97cubic) :
    ((∀ kind, ((legacyFamilyP a g).computeTableRAP kind).Satisfies
        (mixedAssignmentP a g).computeTableTrace) ↔
      (∀ kind, ((legacyFamilyP 0 0).computeTableRAP kind).Satisfies
        (assignmentP 0 0).computeTableTrace)) ∧
    ((∀ kind, ((legacyFamilyP a g).memoryTableRAP kind).Satisfies
        (mixedAssignmentP a g).memoryTableTrace) ↔
      (∀ kind, ((legacyFamilyP 0 0).memoryTableRAP kind).Satisfies
        (assignmentP 0 0).memoryTableTrace)) ∧
    ((∀ kind, ((legacyFamilyP a g).computeIORAP kind).Satisfies
        (mixedAssignmentP a g).computeIOTrace) ↔
      (∀ kind, ((legacyFamilyP 0 0).computeIORAP kind).Satisfies
        (assignmentP 0 0).computeIOTrace)) ∧
    ((∀ kind, ((legacyFamilyP a g).memoryIORAP kind).Satisfies
        (mixedAssignmentP a g).memoryIOTrace) ↔
      (∀ kind, ((legacyFamilyP 0 0).memoryIORAP kind).Satisfies
        (assignmentP 0 0).memoryIOTrace)) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- Conversely, both walk traces in the mixed assignment are exactly the sampled
pair's traces.  No walk column from the reference index `(0,0)` is used. -/
theorem two_walk_traces_are_exactly_the_sampled_pair (a g : K97cubic) :
    (mixedAssignmentP a g).computeWalkTrace =
        (assignmentP a g).computeWalkTrace ∧
      (mixedAssignmentP a g).memoryWalkTrace =
        (assignmentP a g).memoryWalkTrace ∧
      (mixedAssignmentP a g).computeWalk.ln = (assignmentP a g).computeWalk.ln ∧
      (mixedAssignmentP a g).computeWalk.count = (assignmentP a g).computeWalk.count ∧
      (mixedAssignmentP a g).computeWalk.acc = (assignmentP a g).computeWalk.acc ∧
      (mixedAssignmentP a g).memoryWalk.ln = (assignmentP a g).memoryWalk.ln ∧
      (mixedAssignmentP a g).memoryWalk.count = (assignmentP a g).memoryWalk.count ∧
      (mixedAssignmentP a g).memoryWalk.acc = (assignmentP a g).memoryWalk.acc :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact six-way provenance of `mixedAssignmentP_satisfies`: the two walk
judgments are the current pair's terms, while the other four are the reference
terms checked above. -/
theorem mixed_assignment_six_family_provenance (a g : K97cubic) :
    (mixedAssignmentP a g).Satisfies ∧
      (∀ kind, ((legacyFamilyP a g).computeWalkRAP kind).Satisfies
        (assignmentP a g).computeWalkTrace) ∧
      (∀ kind, ((legacyFamilyP a g).memoryWalkRAP kind).Satisfies
        (assignmentP a g).memoryWalkTrace) ∧
      (∀ kind, ((legacyFamilyP 0 0).computeTableRAP kind).Satisfies
        (assignmentP 0 0).computeTableTrace) ∧
      (∀ kind, ((legacyFamilyP 0 0).memoryTableRAP kind).Satisfies
        (assignmentP 0 0).memoryTableTrace) ∧
      (∀ kind, ((legacyFamilyP 0 0).computeIORAP kind).Satisfies
        (assignmentP 0 0).computeIOTrace) ∧
      (∀ kind, ((legacyFamilyP 0 0).memoryIORAP kind).Satisfies
        (assignmentP 0 0).memoryIOTrace) := by
  have h0 := (completionP.assignment 0 0).sixFamilies
  have hag := (completionP.assignment a g).sixFamilies
  exact ⟨mixedAssignmentP_satisfies a g, hag.2.2.1, hag.2.2.2.1,
    h0.1, h0.2.1, h0.2.2.2.2.1, h0.2.2.2.2.2⟩

/-! ## B. Endpoint hoisting and exact-IO transport -/

/-- `ioAtWalkChallenges` preserves every data and proof field of
`ExactDerivedIOAssignment`; only its dependent family index moves. -/
theorem io_transport_preserves_every_field
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {R : PlusIOSegmentedFamily F K} {p : ℕ} [CharP K p]
    (io : ExactDerivedIOAssignment R p) (a g m : K) :
    (ioAtWalkChallenges io a g m).multiplicity = io.multiplicity ∧
      (ioAtWalkChallenges io a g m).progAcc = io.progAcc ∧
      (ioAtWalkChallenges io a g m).memAcc = io.memAcc ∧
      (ioAtWalkChallenges io a g m).multiplicity_ne_zero =
        io.multiplicity_ne_zero ∧
      (ioAtWalkChallenges io a g m).progSat = io.progSat ∧
      (ioAtWalkChallenges io a g m).memSat = io.memSat ∧
      (ioAtWalkChallenges io a g m).endpoints_agree = io.endpoints_agree ∧
      (ioAtWalkChallenges io a g m).memory_closes = io.memory_closes :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The hoisted endpoints are one closed triple and are shared by every pair;
the problem and all three endpoint fields are definitionally pair-independent. -/
theorem endpoint_hoist_is_uniform_and_nonempty :
    (∀ a g a' g' : K97cubic,
      (legacyFamilyP a g).problem = (legacyFamilyP a' g').problem ∧
      (legacyFamilyP a g).requests = (legacyFamilyP a' g').requests ∧
      (legacyFamilyP a g).responses = (legacyFamilyP a' g').responses ∧
      (legacyFamilyP a g).outMem = (legacyFamilyP a' g').outMem) ∧
      (∀ a g : K97cubic,
        Nonempty (JointAssignment (legacyFamilyP a g) (ringChar K97cubic))) := by
  constructor
  · intro a g a' g'
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro a g
    exact ⟨completionP.assignment a g⟩

/-! ## C. Closed package, quantifier order, and post-coin non-constancy -/

/-- One closed package inhabits the advertised existential-before-universal
statement, and the stronger bundled delivery uses that same package. -/
theorem closed_package_quantifier_order
    (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
      (packageP hmoreM).optimized.basis)
    (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
    (hrootAt : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    (∀ a g : K97cubic, (packageP hmoreM).strategy.Accepts (coinN a g) cfgS.challenges.lam) ∧
      (∃ P : OptimizedFullStrictNockVMROMPackage F97 K97cubic 4,
        ∀ a g : K97cubic, P.strategy.Accepts (coinN a g) cfgS.challenges.lam) ∧
      (∃ P : OptimizedFullStrictNockVMROMPackage F97 K97cubic 4,
        OptimizedFullStrictThm54Statement P ∧
          ∀ a g : K97cubic,
            P.strategy.Accepts (coinN a g) cfgS.challenges.lam ∧
            coinN a g ∉ FailureUnion P.strategy P.optimized.census cfgS.challenges.lam ∧
            GenuineTargetAt P.strategy 97 3 (coinN a g) cfgS.challenges.lam) :=
  ⟨fun a g => packageP_accepts hmoreM a g (hrootAt a g),
    exists_package_accepting_every_challenge_pair hmoreM hrootAt,
    commit_then_sample_completeness hmoreM haxP hbasisP (formRWidthP) hrootAt⟩

/-- The committed `afterAlphaM` message is identical across arbitrary walk coins,
while one package accepts two pairs differing in both sampled coordinates. -/
theorem fixed_commitment_distinct_coin_acceptance
    (hrootAt : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    (∀ a g a' g' : K97cubic,
      rawStrategyP.alphaMCommitment (coinN a g) cfgS.challenges.lam seedM_ne =
        rawStrategyP.alphaMCommitment (coinN a' g') cfgS.challenges.lam seedM_ne) ∧
      (packageP hmoreM).strategy.Accepts (coinN 0 0) cfgS.challenges.lam ∧
      (packageP hmoreM).strategy.Accepts coinNonzero cfgS.challenges.lam ∧
      alphaC (coinN 0 0) ≠ alphaC coinNonzero ∧
      gamma (coinN 0 0) ≠ gamma coinNonzero :=
  ⟨alphaMCommitmentP_same_across_coins, packageP_accepts_distinct_challenges hmoreM hrootAt⟩

/-- The production file only states that `walkArraysP` reads its coin.  Acceptance
plus `ln(1)=alphaC` proves the stronger behavioral fact directly: its outputs at
the zero and nonzero coins cannot be equal. -/
theorem walkArraysP_is_nonconstant_on_accepted_coins :
    walkArraysP (coinN 0 0) cfgS.challenges.lam seedM_ne ≠ walkArraysP coinNonzero cfgS.challenges.lam seedM_ne := by
  intro hw
  have hsix0 :=
    (rawStrategyP.accepts_iff_six_families (coinN 0 0) cfgS.challenges.lam seedM_ne).1
      (rawStrategyP_accepts 0 0)
  have hsixN :=
    (rawStrategyP.accepts_iff_six_families coinNonzero cfgS.challenges.lam seedM_ne).1
      (rawStrategyP_accepts alphaCN gammaN)
  have hcert0 :=
    ((rawStrategyP.messageAt (coinN 0 0) cfgS.challenges.lam seedM_ne).computeWalkRAP_wholeTrace_iff).1
      hsix0.2.2.2.1
  have hcertN :=
    ((rawStrategyP.messageAt coinNonzero cfgS.challenges.lam seedM_ne).computeWalkRAP_wholeTrace_iff).1
      hsixN.2.2.2.1
  have h0 := hcert0.1.ln1
  have hN := hcertN.1.ln1
  change (walkArraysP (coinN 0 0) cfgS.challenges.lam seedM_ne).computeLn 1 = 0 at h0
  change (walkArraysP coinNonzero cfgS.challenges.lam seedM_ne).computeLn 1 = alphaCN at hN
  apply alphaCN_ne_zero
  calc
    alphaCN = (walkArraysP coinNonzero cfgS.challenges.lam seedM_ne).computeLn 1 := hN.symm
    _ = (walkArraysP (coinN 0 0) cfgS.challenges.lam seedM_ne).computeLn 1 :=
      congrArg (fun W : RawWalkArrays K97cubic => W.computeLn 1) hw.symm
    _ = 0 := h0

/-- The committed execution, skeleton and census are the prior objects, while the
pre-challenge message remains pair-independent. -/
theorem committed_half_and_execution_unchanged :
    residualHonestP =
        HonestCommitment.commitmentResidualOf dataM alphaMCommitmentP walkArraysP ∧
      (packageP hmoreM).optimized.commitment.skeleton = skelM ∧
      (packageP hmoreM).objects.cfg = cfgS ∧
      (packageP hmoreM).objects.exec = execS ∧
      (packageP hmoreM).optimized.census = censusM ∧
      (∀ a g a' g' : K97cubic,
        rawStrategyP.alphaMCommitment (coinN a g) cfgS.challenges.lam seedM_ne =
          rawStrategyP.alphaMCommitment (coinN a' g') cfgS.challenges.lam seedM_ne) := by
  exact ⟨(packageP_commitment_unchanged hmoreM).1,
    (packageP_commitment_unchanged hmoreM).2.2.1,
    (packageP_commitment_unchanged hmoreM).2.2.2.1,
    (packageP_commitment_unchanged hmoreM).2.2.2.2.1,
    (packageP_commitment_unchanged hmoreM).2.2.2.2.2,
    alphaMCommitmentP_same_across_coins⟩

/-! ## D. Preserved malformed controls and fourteen-field recount -/

theorem preserved_rejection_controls
    (hrootAt : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    (packageP hmoreM).strategy.Accepts coinNonzero cfgS.challenges.lam ∧
      alphaC coinNonzero ≠ 0 ∧ gamma coinNonzero ≠ 0 ∧
      ¬ IsFullBFT alteredCurN alteredChildN alteredFanoutN 2 ∧
      (¬ ∃ ln count acc : ℕ → K97cubic,
        WalkSat alteredCurN alteredChildN alteredFanoutN ln count acc
          (alphaC coinNonzero) (alteredCurN 1 * alphaC coinNonzero)
          (alphaC coinNonzero) 2 ∧ acc 2 = 0) ∧
      (∃ ln count acc : ℕ → K97cubic,
        WalkSat alteredCurN alteredChildN alteredFanoutN ln count acc 0
          (alteredCurN 1 * 0) 0 2 ∧ acc 2 = 0) ∧
      (0 : K97cubic) ∈ computeSlotBadGammas badComputeTreeN 0 ∧
      gamma coinNonzero ∉ computeSlotBadGammas badComputeTreeN 0 :=
  packageP_rejection_receipts hmoreM hrootAt

theorem fourteen_field_recount_preserved
    (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
      (packageP hmoreM).optimized.basis)
    (hbasisP : FormRBasis (packageP hmoreM).optimized.basis) :
    (8 + 1 + 5 = 14) ∧
      Nonempty (OptimizedFullStrictThm54Statement (packageP hmoreM)) :=
  ⟨by norm_num, ⟨statementP hmoreM haxP hbasisP formRWidthP⟩⟩

/-! ## The exact committed fibre -/

/-- The `coinN` image is exactly, not merely a subset of, the fibre where seed
and `alphaM` equal the committed values. -/
theorem coinN_image_iff_committed_fibre (ω : JointCoins K97cubic) :
    ω ∈ Finset.univ.image
        (fun pair : K97cubic × K97cubic => coinN pair.1 pair.2) ↔
      nprSeed ω = servedSeed ∧ alphaM ω = fixtureAlpha := by
  constructor
  · intro h
    obtain ⟨pair, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨rfl, rfl⟩
  · rintro ⟨hz, hα⟩
    apply Finset.mem_image.mpr
    refine ⟨(alphaC ω, gamma ω), Finset.mem_univ _, ?_⟩
    exact (coin_eq_coinN hz hα).symm

/-- Exactly `97^6` coins are certified outside false acceptance, out of the
`97^12`-coin joint space. -/
theorem committed_fibre_exclusion_and_cardinality
    (hrootAt : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    (∀ ω : JointCoins K97cubic,
      nprSeed ω = servedSeed → alphaM ω = fixtureAlpha →
        ω ∉ FalseAcceptanceSet (packageP hmoreM).strategy 97 3 cfgS.challenges.lam) ∧
      (Finset.univ.image
        (fun pair : K97cubic × K97cubic => coinN pair.1 pair.2)).card = 97 ^ 6 ∧
      Fintype.card (JointCoins K97cubic) = 97 ^ 12 :=
  ⟨fun _ hz hα => falseAcceptanceP_disjoint_fibre hmoreM hrootAt hz hα,
    acceptedRangeP_card.1, acceptedRangeP_card.2⟩

/-- The remaining classification step is still exactly an implication from the
undischarged fibre-pinning hypothesis; this receipt does not inhabit it. -/
theorem remaining_false_acceptance_step_is_conditional
    (hrootAt : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    (∀ ω : JointCoins K97cubic, (packageP hmoreM).strategy.Accepts ω cfgS.challenges.lam →
      nprSeed ω = servedSeed ∧ alphaM ω = fixtureAlpha) →
      FalseAcceptanceSet (packageP hmoreM).strategy 97 3 cfgS.challenges.lam = ∅ :=
  falseAcceptanceP_empty_of_fibre_pinned hmoreM hrootAt

/-! ## F. Release and design-principle regression -/

theorem released_aliases_direct_capstone_and_control_unchanged :
    @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package ∧
      @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch80.released_aliases_and_control_unchanged

/-- Same-execution threading and the memoryless/positionless fixture remain
visible at the consumed package: one exact execution, two active compute rows,
fourteen active memory rows, and the unchanged shared forest-axis connective. -/
theorem single_execution_threading_regression
    (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
      (packageP hmoreM).optimized.basis)
    (hbasisP : FormRBasis (packageP hmoreM).optimized.basis) :
    (packageP hmoreM).objects.cfg = cfgS ∧ (packageP hmoreM).objects.exec = execS ∧
      (packageP hmoreM).computeChip.rap.H.card = 2 ∧
      (packageP hmoreM).memoryChip.rap.H.card =
        RowLayout.memoryM multiRootExecution.exec +
          2 * RowLayout.memoryL multiRootExecution.exec ∧
      Nonempty (packageP hmoreM).optimized.OptimizedSharedMemoryConnective := by
  refine ⟨rfl, rfl, (packageP_regression hmoreM).2.2.2.2, ?_,
    ⟨(statementP hmoreM haxP hbasisP formRWidthP).shared_forest_axis⟩⟩
  exact (BuildablePackage.constructed_row_budgets multiRootExecution inputsM
    residualHonestP inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualHonestP_generated MultiRootHonestCommitment.f97_primeField).2

#print axioms family_is_reference_with_only_walk_challenges
#print axioms four_nonwalk_RAPs_are_definitionally_pair_independent
#print axioms four_nonwalk_traces_are_definitionally_reference_terms
#print axioms four_nonwalk_satisfaction_terms_are_reference
#print axioms two_walk_traces_are_exactly_the_sampled_pair
#print axioms mixed_assignment_six_family_provenance
#print axioms io_transport_preserves_every_field
#print axioms endpoint_hoist_is_uniform_and_nonempty
#print axioms closed_package_quantifier_order
#print axioms fixed_commitment_distinct_coin_acceptance
#print axioms walkArraysP_is_nonconstant_on_accepted_coins
#print axioms committed_half_and_execution_unchanged
#print axioms preserved_rejection_controls
#print axioms fourteen_field_recount_preserved
#print axioms coinN_image_iff_committed_fibre
#print axioms committed_fibre_exclusion_and_cardinality
#print axioms remaining_false_acceptance_step_is_conditional
#print axioms released_aliases_direct_capstone_and_control_unchanged
#print axioms single_execution_threading_regression

#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.uniformEndpoints_exist
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.mixedAssignmentP_satisfies
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.alphaMCommitmentP_same_across_coins
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.packageP_accepts
#print axioms
  Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.exists_package_accepting_every_challenge_pair
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.commit_then_sample_completeness
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.packageP_accepts_distinct_challenges
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.packageP_rejection_receipts
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.falseAcceptanceP_disjoint_fibre
#print axioms Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.acceptedRangeP_card
#print axioms
  Nock.NockVMROM.Thm54.MultiRootPhaseCorrect.falseAcceptanceP_empty_of_fibre_pinned

#print axioms «Thm:IO_result»
#print axioms «Thm:Walk_IOP»
#print axioms «Corr:forest»
#print axioms «Thm:deterministic_Trace»
#print axioms «Lem:NPR_decomp»
#print axioms «Thm:Noun_Validation»
#print axioms «Thm:comp_38»
#print axioms «Thm:mem_38»
#print axioms «Thm:NockVMROM»
#print axioms «Lem:equiv_compute»
#print axioms «Lem:equiv_mem»
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVM.V_NockVMROM_forest

end
end Nock.RedTeam.Batch81
