import Nock.NockVMROM.Thm54.BuildablePackage
import Nock.NockVMROM.Thm54.NonterminalServedRow
import Nock.RedTeam.Batch76Thm54GlobalIntermediate
import Nock.RedTeam.Batch69Thm54RepairedP8TraceThreading
import Nock.NockVMROM.Thm54.Walk37.PaperNames

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Theorem 5.4 universal-package Milestone 5

Paper frame:
the paper.

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

* the twenty-one-field `CommitmentResidual` is supplied, including the complete honest
  specialization and all-seed committed checks;
* the package fields outside that residual are assembled from one `E` and `I`;
* the new OP0/OP4 fixture reaches compute-side row/tree semantics only, not an exact execution or
  any package constructor.
-/

namespace Nock.RedTeam.Batch77

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.RawSemanticAssembly
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrictCommitment
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [DecidableEq F]
variable [CharP K (ringChar K)]

/-! ## A. Exact residual inventory and load-bearing specialization -/

/-- It contains no optimized chip, trace, sampled assignment, topology output, or package. -/
theorem commitmentResidual_eta
    {E : BuildableNockExecution F K} (R : CommitmentResidual E) :
    R =
      { verifier := R.verifier
        commitment := R.commitment
        claim_eq := R.claim_eq
        scan := R.scan
        shapeMatch := R.shapeMatch
        rowFrame := R.rowFrame
        slotSemantics := R.slotSemantics
        recordEquations := R.recordEquations
        Λ := R.Λ
        census := R.census
        sizeWindowBound := R.sizeWindowBound
        honestSeed := R.honestSeed
        honestSeed_ne := R.honestSeed_ne
        honestAlpha := R.honestAlpha
        honest_specialization := R.honest_specialization
        computeLineOrigin := R.computeLineOrigin
        q_eq_ringChar := R.q_eq_ringChar
        skeletonBounded := R.skeletonBounded
        combinedBounded := R.combinedBounded
        KszBound := R.KszBound
        progCapacity := R.progCapacity
        memCapacity := R.memCapacity } := by
  cases R
  rfl

/-- The residual does supply the entire exact problem at its honest point.  This is not derivable
from `E`; it is the load-bearing bridge from the pre-seed template to `E`. -/
theorem residual_supplies_exact_honest_problem
    {E : BuildableNockExecution F K} (R : CommitmentResidual E) :
    specializedProblem R.verifier.raw.timestamp R.honestSeed R.honestSeed_ne R.honestAlpha
        E.cfg.challenges.lam = ⟨E.cfg, E.exec⟩ :=
  R.honest_specialization

/-- Consequently the committed specialization cannot be detached to an independently chosen
configuration or dependent execution. -/
theorem residual_honest_specialization_forces_same_execution
    {E : BuildableNockExecution F K} (R : CommitmentResidual E) :
    (specializedProblem R.verifier.raw.timestamp R.honestSeed
          R.honestSeed_ne R.honestAlpha E.cfg.challenges.lam).cfg = E.cfg ∧
      HEq (specializedProblem R.verifier.raw.timestamp R.honestSeed
          R.honestSeed_ne R.honestAlpha E.cfg.challenges.lam).exec E.exec := by
  rw [R.honest_specialization]
  exact ⟨rfl, HEq.rfl⟩

/-- The three all-seed checks and three all-seed bounds really are assumptions projected from the
residual; the package constructor proves none of them. -/
theorem all_seed_commitment_strength_is_explicit
    {E : BuildableNockExecution F K} (R : CommitmentResidual E) :
    (∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      ActiveFingerprintChecksAt z R.commitment
        (specializedProblem R.verifier.raw.timestamp z hz α lmb).exec) ∧
    (∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      ExecTreeShapeMatchesAt R.commitment
        (specializedProblem R.verifier.raw.timestamp z hz α lmb).exec) ∧
    (∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      RowFrameChecksAt z R.commitment
        (specializedProblem R.verifier.raw.timestamp z hz α lmb).exec) ∧
    (∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      (specializedProblem R.verifier.raw.timestamp z hz α lmb).cfg.Ksz < ringChar K) ∧
    (∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      (specializedProblem R.verifier.raw.timestamp z hz α lmb).exec.derivedRequestIO.length + 1 ≤
        2 ^ (specializedProblem R.verifier.raw.timestamp z hz α lmb).cfg.orbit.h) ∧
    (∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      (specializedProblem R.verifier.raw.timestamp z hz α lmb).exec.derivedResponseIO.length + 1 ≤
        2 ^ (specializedProblem R.verifier.raw.timestamp z hz α lmb).cfg.orbit.h) :=
  ⟨R.scan, R.shapeMatch, R.rowFrame, R.KszBound, R.progCapacity, R.memCapacity⟩

/-! ## B. Field-by-field package split -/

/-- Ten are literal
`R` projections, four are literal `E`/`I` projections, and twenty-one are constructed expressions
of `E` and `I`. -/
theorem built_optimized_package_eta
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = default)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha) :
    buildOptimizedStrictPackage E I R hzero hprl hmore hord hordM =
      { objects := buildObjects E
        verifier := R.verifier
        commitment := R.commitment
        claim_eq := R.claim_eq
        scan := R.scan
        shapeMatch := R.shapeMatch
        rowFrame := R.rowFrame
        slotSemantics := R.slotSemantics
        recordCountBalance := E.recordCountBalance
        Λ := R.Λ
        census := R.census
        sizeWindowBound := R.sizeWindowBound
        family := (exactFamilyCompletion E I).family
        family_cfg := rfl
        family_exec := HEq.rfl
        sampled := sampledAssignment E I
        computeObligations := computeObligations E I
        memoryExecA := E.execA
        memoryProduction := BuildableAxisWitness.buildableMemoryProductionAssignment E I hmore
        basis := I.basis
        orbit := I.orbit
        computeNodes := computeNodes E I
        computeNodes_injective := computeNodes_injective E I
        computeAdjacentOrbit := computeNodes_adjacent E I
        computeChallenge := computeChallenge E I
        computePublic := computePublic E I
        computeChallengePins := zeroChallengePins E I hzero
        computePublicPins := computePublic_pins E I
        computeRequestsPins := computeRequests_pins E I
        computeLineOrigin := R.computeLineOrigin
        computeWalkOrder := fun hrows => by
          have hα : (exactFamilyCompletion E I).family.computeWalkAlpha =
              I.computeWalkAlpha := by
            simp [ExactFamilyCompletion.family, zeroEndpointFamily]
            rfl
          have hcfg : (exactFamilyCompletion E I).family.problem.cfg.compRows =
              E.cfg.compRows := by
            simp [ExactFamilyCompletion.family, zeroEndpointFamily]
            rfl
          rw [hα]
          exact hord (by rwa [← hcfg])
        memoryWalkOrder := fun hrows => by
          have hα : (exactFamilyCompletion E I).family.memoryWalkAlpha =
              I.memoryWalkAlpha := by
            simp [ExactFamilyCompletion.family, zeroEndpointFamily]
            rfl
          have hcfg : (exactFamilyCompletion E I).family.problem.cfg.memRows =
              E.cfg.memRows := by
            simp [ExactFamilyCompletion.family, zeroEndpointFamily]
            rfl
          rw [hα]
          exact hordM (by rwa [← hcfg])
        memoryNodes := memoryNodes E I
        memoryNodes_injective := memoryNodes_injective E I
        memoryChallenge := memoryChallenge E I
        memoryPublic := memoryPublic E I
        memoryCoordinatePins := memoryCoordinatePins E I
        memoryOrbitAligned := memoryNodes_adjacent E I
        memoryDenominatorsSafe := memoryDenominatorsSafe_of_sampled (sampledAssignment E I)
        two_ne_zero := E.two_ne_zero
        pairedRecordLayout := hprl } :=
  rfl

/-- Eleven are literal
`R` projections, six are `E`/`I` projections or semantic projections, nine are constructed
expressions (counting the constructed optimized package as one field), and three are the caller's
hypotheses: `rowsBound` (H1.5b Part 2a) is `hrows`, `generated` / `primeField`
are `hgenF` / `hF`. -/
theorem built_full_package_eta
    (E : BuildableNockExecution F K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = default)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    buildFullPackage E I R hzero hprl hmore hord hordM hrows =
      { optimized := buildOptimizedStrictPackage E I R hzero hprl hmore hord hordM
        honestSeed := R.honestSeed
        honestSeed_ne := R.honestSeed_ne
        honestAlpha := R.honestAlpha
        honest_specialization := R.honest_specialization
        chained := E.chained
        walkFamily := (buildTopology E I).rawFamily
        walkFamily_problem := topology_problem_same_execution E I
        compEnc_inj := (exactFamilyCompletion E I).family.compNodeEncode_labelOf
        memEnc_inj := (exactFamilyCompletion E I).family.memNodeEncode_labelOf
        computeRowsAccepted := BuildablePackage.computeRowsAccepted E
        memoryRowsAccepted := BuildablePackage.memoryRowsAccepted E
        topologyBinding := BuildableTopologyCorrectness.rawTopologyBinding E I
        recordEquations := R.recordEquations
        ioStrategy := finiteIOStrategy E I
        io_requests := rfl
        io_responses := rfl
        q := E.q
        stateTagChar := I.stateTagChar
        q_gt_one := E.q_gt_one
        q_eq_ringChar := R.q_eq_ringChar
        skeletonBounded := R.skeletonBounded
        combinedBounded := R.combinedBounded
        KszBound := R.KszBound
        progCapacity := R.progCapacity
        memCapacity := R.memCapacity
        rowsBound := hrows
        generated := hgenF
        primeField := hF } :=
  rfl

/-- The prose count `22` for constructed optimized fields is off by one. -/
theorem exact_field_count_adjudication :
    35 = 10 + 4 + 21 ∧
      29 = 11 + 6 + 9 + 3 ∧
      22 ≠ 21 := by
  norm_num

/-- Every central arithmetization object is independent of which residual witness is supplied.
Changing `R` can change the committed strategy, but cannot replace the execution-derived objects,
family, sampled assignment, chips, or memory-production assignment. -/
theorem constructed_core_is_residual_independent
    (E : BuildableNockExecution F K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (R S : CommitmentResidual E)
    (hzero : I.computeChallenges = default)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenR : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hgenS : GeneratedField.ClaimGenerated K S.verifier.raw.claim S.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    (buildFullPackage E I R hzero hprl hmore hord hordM hrows).objects =
        (buildFullPackage E I S hzero hprl hmore hord hordM hrows).objects ∧
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).optimized.family =
        (buildFullPackage E I S hzero hprl hmore hord hordM hrows).optimized.family ∧
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).optimized.sampled =
        (buildFullPackage E I S hzero hprl hmore hord hordM hrows).optimized.sampled ∧
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).computeChip =
        (buildFullPackage E I S hzero hprl hmore hord hordM hrows).computeChip ∧
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).memoryChip =
        (buildFullPackage E I S hzero hprl hmore hord hordM hrows).memoryChip ∧
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).optimized.memoryProduction =
        (buildFullPackage E I S hzero hprl hmore hord hordM hrows).optimized.memoryProduction :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A detached exact problem cannot be substituted: equality of the built walk-family problem
forces both the configuration and dependent execution of `E`. -/
theorem detached_walk_problem_forces_same_execution
    (E : BuildableNockExecution F K) (I : Inputs E)
    (Q : RawProblem F K)
    (h : (buildTopology E I).rawFamily.problem = Q) :
    Q.cfg = E.cfg ∧ HEq Q.exec E.exec := by
  rw [topology_problem_same_execution E I] at h
  subst Q
  exact ⟨rfl, HEq.rfl⟩

/-! ## C. The zero-tuple restriction is a released-field restriction -/

/-- Every backend input has a zero-tuple admissible variant with all other data fields unchanged.
Thus `hzero` does not constrain the execution, orbit, basis, IO coins, or memory challenges. -/
theorem every_input_has_zero_tuple_variant
    {E : BuildableNockExecution F K} (I : Inputs E) :
    let J := I.withComputeChallenges default
    J.computeChallenges = default ∧
      J.stateTagChar = I.stateTagChar ∧
      J.computeWalkAlpha = I.computeWalkAlpha ∧
      J.memoryWalkAlpha = I.memoryWalkAlpha ∧
      J.walkGamma = I.walkGamma ∧
      J.hOrb = I.hOrb ∧
      J.basis = I.basis ∧
      J.orbit = I.orbit ∧
      J.ioCoins = I.ioCoins ∧
      J.memoryScalarChallenge = I.memoryScalarChallenge ∧
      J.memoryExtensionFold = I.memoryExtensionFold := by
  simp [Inputs.withComputeChallenges]

/-- The generic chip/trace path accepts arbitrary tuples and pins them with the parameterized
`ExactFinalChallengeCoordinatesWith`; no zero premise occurs. -/
theorem arbitrary_tuple_chip_path
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (c d : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hC : E.exec.CprimeCoherent)
    (haxc : FormRAxisBound (sampledAssignment E (I.withComputeChallenges c))
      (I.withComputeChallenges c).basis)
    (haxd : FormRAxisBound (sampledAssignment E (I.withComputeChallenges d))
      (I.withComputeChallenges d).basis)
    (hbasis : FormRBasis I.basis)
    (hwidth : FormRWidth F)
    (hhalt : MemoryHaltLeavesHonest.HaltRowsBase (F := F) E.exec) :
    ExactFinalChallengeCoordinatesWith I.basis
        (sampledAssignment E (I.withComputeChallenges c)) c
        (computeChallenge E (I.withComputeChallenges c)) ∧
      BuildableTraceSatisfaction
        (buildTopology E (I.withComputeChallenges c))
        (buildTraces E (I.withComputeChallenges c)) ∧
      BuildableTraceSatisfaction
        (buildTopology E (I.withComputeChallenges d))
        (buildTraces E (I.withComputeChallenges d)) := by
  exact ⟨computeChallenge_pins E (I.withComputeChallenges c),
    (challenge_substitution_traces_satisfy E I R.computeLineOrigin hprl
      hmore hord hordM c d hC haxc haxd hbasis hwidth hhalt).1,
    (challenge_substitution_traces_satisfy E I R.computeLineOrigin hprl
      hmore hord hordM c d hC haxc haxd hbasis hwidth hhalt).2⟩

/-! ## D. F97 is an excluded bad-seed fixture -/

namespace F97

open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.SemanticTrace

local instance prime97F : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-- Whenever a committed skeleton lists a noun requiring a size window, the F97 fixture seed is
literally in the production bad-seed set. -/
theorem fixture_seed_is_counted_by_sizeWindowFailure
    (S : SemanticSkeleton) (n : Noun)
    (hn : n ∈ skeletonSizeWindowNouns S) :
    fixtureSeed ∈ sizeWindowFailureSeeds (K := K97cubic) S := by
  rw [mem_sizeWindowFailureSeeds_iff]
  exact ⟨by simpa [fixtureSeed_eq_one], n, hn, no_sizeWindow_at_fixtureSeed n⟩

/-- Exact fixture-level adjudication: no semantic bundle/buildable execution exists at the pinned
seed, and the fixture's OP4/OP1 rows contain no served lookup even independently of that seed. -/
theorem fixture_obstruction_is_exactly_scoped :
    IsEmpty (ExactExecutionSemanticData 97 3 cfg97 exec97) ∧
      (∀ E : BuildableNockExecution F97 K97cubic,
        E.cfg = cfg97 → HEq E.exec exec97 → False) ∧
      (∀ row ∈ exec97.computeRows, requiredServedLookups row.1 = 0) :=
  ⟨no_semantic_data_for_exec97 97 3,
    fun E hcfg hexec => no_buildable_execution_over_f97 E hcfg hexec,
    f97_rows_require_no_served_lookups⟩

end F97

/-! ## E. Genuine nonterminal OP0 compute-side service -/

namespace Served

open Nock.Noun Nock.Walk ComputeTable
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
local instance char97 : CharP K97cubic 97 := inferInstance

/-- The served subject is a real cell, axis 2 is not the root axis, and slot 2 performs the real
left descent required by the paper. -/
theorem served_lookup_is_nontrivial :
    subjectS = .cell (.atom 7) (.atom 9) ∧
      (2 : ℕ) ≠ 1 ∧
      Noun.slot 2 subjectS = some resultS :=
  ⟨rfl, by decide, slot_subjectS⟩

/-- The semantic service is tied to the accepted row's own `mr2` record, with the exact paper
root/child/axis triple. -/
theorem served_record_is_the_row_mr2 :
    servedPub.mr2 = servedRecord ∧
      servedRecord.root = encS subjectS ∧
      servedRecord.child = encS resultS ∧
      servedRecord.axis = 2 ∧
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun subjectS 1) 2 resultS :=
  ⟨rfl, rfl, rfl, rfl, servedLookup_served⟩

/-- Explicit constructor exposing the load-bearing child evaluation premise of the OP4 parent.
The premise is precisely the derived evaluation exported by the served OP0 certificate. -/
def parentCertificateFromServedEvaluation
    (fuel : ℕ)
    (heval : FieldEmbedding.evalFBy 97 (fuel + 1) subjectS formulaS = some resultS) :
    LocalOpcodeCertificate 97 3 parentRowData := by
  refine .s4 parentRowData (fuel + 1) parentCall rfl servedSeed_ne q_eq_ringChar97
    cast_injOn_97 ?_ ?_ ?_ ?_ ?_ (servedSeed_window_atom 7) heval parentS_accepts
  · simp [ComparisonListed, parentRowData, parentComparisons, parentRoot, parentHeadS]
  · simp [ComparisonListed, parentRowData, parentComparisons, parentRoot, parentFormulaS]
  · simp [ComparisonListed, parentRowData, parentComparisons, parentRoot, parentCall, subjectS]
  · simp [ComparisonListed, parentRowData, parentComparisons, parentRoot, parentCall]
  · have hinc :
        OpcodeSemantics.incMod (ringChar K97cubic) parentCall.result = parentResultS :=
      incMod_resultS
    unfold ComparisonListed; rw [hinc]
    simp [parentRowData, parentComparisons, parentRoot, parentResultS]

/-- The actual served-row theorem supplies that premise, so the parent certificate and semantics
are not merely colocated above an unrelated lookup. -/
theorem parent_certificate_consumes_served_child :
    ∃ fuel : ℕ,
      FieldEmbedding.evalFBy 97 (fuel + 1) subjectS formulaS = some resultS ∧
        Nonempty (LocalOpcodeCertificate 97 3 parentRowData) := by
  obtain ⟨fuel, _, _, heval⟩ := served_semantics
  exact ⟨fuel, heval, ⟨parentCertificateFromServedEvaluation fuel heval⟩⟩

/-- Exact positive scope of the additive fixture. -/
theorem compute_side_scope_reached :
    Vcomp servedInputs servedPub servedDec ∧
      requiredServedLookups servedRow.1 = 1 ∧
      Nonempty (LocalOpcodeCertificate 97 3 servedRowData) ∧
      RVT (ComputeTable.Fcomp (K := K97cubic)) computeTreeS ∧
      parentPubS.state = .s4 ∧
      ComputeTable.fanoutComp parentPubS.state = 1 :=
  ⟨served_accepts, rfl, ⟨servedCertificate⟩, computeTreeS_rvt, rfl, rfl⟩

end Served

/-! ## F. -/

noncomputable local instance : Fintype ConcreteStrictPackage.K73cubic :=
  Fintype.ofFinite ConcreteStrictPackage.K73cubic
noncomputable local instance : DecidableEq ConcreteStrictPackage.K73cubic :=
  Classical.decEq ConcreteStrictPackage.K73cubic
local instance : CharP ConcreteStrictPackage.K73cubic 73 := inferInstance
local instance : CharP ConcreteStrictPackage.K73cubic
    (ringChar ConcreteStrictPackage.K73cubic) :=
  ringChar.charP ConcreteStrictPackage.K73cubic

/-- Concrete non-vacuity is F73 only: it supplies the residual, the constructed package, and the
released statement on one identical execution. -/
theorem f73_exact_nonvacuity
    (hmore : BuildableAxisWitness.LaterSeedZeros BuildableConcrete.concreteExecution)
    (hax : FormRAxisBound
      (BuildablePackage.Concrete.package73 hmore).optimized.sampled
      (BuildablePackage.Concrete.package73 hmore).optimized.basis)
    (hbasis : FormRBasis (BuildablePackage.Concrete.package73 hmore).optimized.basis)
    (hwidth : FormRWidth ConcreteStrictPackage.F73) :
    Nonempty
      (CommitmentResidual BuildableConcrete.concreteExecution) ∧
      Nonempty
        (OptimizedFullStrictThm54Statement (BuildablePackage.Concrete.package73 hmore)) ∧
      (BuildablePackage.Concrete.package73 hmore).objects.cfg =
        BuildableConcrete.concreteExecution.cfg ∧
      (BuildablePackage.Concrete.package73 hmore).objects.exec =
        BuildableConcrete.concreteExecution.exec :=
  ⟨⟨BuildablePackage.Concrete.residual73⟩,
    BuildablePackage.Concrete.statement73_nonvacuous hmore hax hbasis hwidth, rfl, rfl⟩


theorem released_aliases_unchanged :
    @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package ∧
      @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch69.repaired_alias_and_forest_control

#print axioms Nock.NockVMROM.Thm54.BuildablePackage.CommitmentResidual
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.buildObjects
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.zeroChallengePins
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.buildOptimizedStrictPackage
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.buildFullPackage
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.universalOptimizedFullStrictThm54
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.universalContainment
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.universalFixedFieldSoundness
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.constructed_same_execution
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.constructed_resources
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.constructed_row_budgets
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.constructed_memoryProduction
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.Concrete.residual73
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.Concrete.package73
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.Concrete.statement73

#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.no_sizeWindow_at_fixtureSeed
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.no_semantic_data_for_exec97
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.no_buildable_execution_over_f97
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.f97_rows_require_no_served_lookups
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.served_accepts
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.servedLookup_served
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.servedRecord_realizes
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.servedCertificate
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.served_semantics
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.parentRowS_accepts
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.computeTreeS_rvt
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.parentCertificate_nonempty
#print axioms Nock.NockVMROM.Thm54.NonterminalServedRow.parentS_semantics

#print axioms commitmentResidual_eta
#print axioms residual_supplies_exact_honest_problem
#print axioms residual_honest_specialization_forces_same_execution
#print axioms all_seed_commitment_strength_is_explicit
#print axioms built_optimized_package_eta
#print axioms built_full_package_eta
#print axioms exact_field_count_adjudication
#print axioms constructed_core_is_residual_independent
#print axioms detached_walk_problem_forces_same_execution
#print axioms every_input_has_zero_tuple_variant
#print axioms arbitrary_tuple_chip_path
#print axioms F97.fixture_seed_is_counted_by_sizeWindowFailure
#print axioms F97.fixture_obstruction_is_exactly_scoped
#print axioms Served.served_lookup_is_nontrivial
#print axioms Served.served_record_is_the_row_mr2
#print axioms Served.parentCertificateFromServedEvaluation
#print axioms Served.parent_certificate_consumes_served_child
#print axioms Served.compute_side_scope_reached
#print axioms f73_exact_nonvacuity
#print axioms released_aliases_unchanged

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
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVM.V_NockVMROM_forest

end
end Nock.RedTeam.Batch77
