import Nock.NockVMROM.Thm54.BuildableAxisWitness
import Nock.NockVMROM.Thm54.GeneratedField
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Milestones 0--4 build, from one `BuildableNockExecution` and one pre-compilation
`BuildableChips.Inputs`, every *arithmetization* half of the released strict package: the exact
six-family completion, the sampled finite IO, the strict active domains and interpolation nodes,
the complete compute/memory coordinate layouts and their exact pins, the corrected `199/98` and
repaired `196/112` fixed-preprocessing chips, their canonical polynomial traces, the verifier-
generated topology payload arrays and their binding residual, and the axis-side
`MemoryProductionAssignment`.

What those two inputs do **not** determine is the *committed* half: the template verifier, the
committed skeleton and its public claim, the per-seed active-fingerprint / tree-shape / row-frame
checks, the skeleton slot semantics and record equations, the comparison census and its size
window, the honest seed/`alphaM` pair at which the committed template specializes to this very
execution, and the all-seed characteristic/capacity bounds.

`buildOptimizedStrictPackage` and `buildFullPackage` then assemble the actual released package
types, and `universalOptimizedFullStrictThm54` applies the *unchanged* released capstone
`optimizedFullStrictNockVMROM_of_package` to a package that was constructed rather than supplied.

That pin
names only the twelve cubic triples, so zero folds `9` and `11` inhabit it; selector slot `36` is
not a cubic index.  The additive `buildFullPackageWith` takes `ExactFinalChallengeCoordinatesWith` together
with those two zero cubic folds and still produces an `OptimizedFullStrictNockVMROMPackage` the
unchanged released statement can consume.
-/

namespace Nock.NockVMROM.Thm54
namespace BuildablePackage

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open RawSemanticAssembly SemanticStrategy StrictCommitment
open TemplateRawJointSoundness ServedLookupBridge
open ProductionP8Containment
open ProductionAxisStructureVerifier TemplateAxisCounting
open OptimizedComputeCorrectedFinal
open OptimizedComputeCanonicalSatisfaction
open OptimizedMemoryRAP OptimizedMemoryCanonicalSatisfaction
open OptimizedStrictPackage OptimizedStrictFullPackage
open BuildableChips
open OptimizedComputeFinalTrace
open OptimizedComputeCollisionBound

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## The exact commitment residual -/

/-- Every field here is about the *committed template and skeleton*, never about a chip, trace,
coordinate layout, active domain, sampled assignment, axis conclusion, topology binding, or
optimized realization: all of those are constructed by Milestones 2--4 below.  `honest_specialization`
is the one field that links the two halves, and it is exactly the paper's statement that the
committed template, at the honest seed and `alphaM`, specializes to this supplied execution. -/
structure CommitmentResidual (E : BuildableNockExecution F K) where
  /-- The committed template verifier. -/
  verifier : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K)
  /-- The committed semantic skeleton. -/
  commitment : SkeletonCommitment
  claim_eq : commitment.skeleton.publicClaim = verifier.raw.claim
  scan : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
    ActiveFingerprintChecksAt z commitment
      (specializedProblem verifier.raw.timestamp z hz α lmb).exec
  shapeMatch : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
    ExecTreeShapeMatchesAt commitment
      (specializedProblem verifier.raw.timestamp z hz α lmb).exec
  rowFrame : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
    RowFrameChecksAt z commitment
      (specializedProblem verifier.raw.timestamp z hz α lmb).exec
  slotSemantics : ∀ s ∈ computeSkeletonRows commitment.skeleton,
    SkeletonSlotSemantics s
  recordEquations : ∀ s ∈ computeSkeletonRows commitment.skeleton,
    SkeletonRecordEquations s
  /-- The paper's leaf window for the comparison census. -/
  Λ : ℕ
  census : EdgeComparisonCensus.CombinedSkeletonCensus K commitment.skeleton Λ
  sizeWindowBound :
    SizeWindowCounting.SizeWindowNounsBoundedBy commitment.skeleton Λ
  honestSeed : K
  honestSeed_ne : honestSeed ≠ 0
  honestAlpha : K
  /-- The committed template specializes, at this seed and `alphaM`, to exactly the supplied
  execution.  This is the single link between the committed and the constructed halves. -/
  honest_specialization :
    specializedProblem verifier.raw.timestamp honestSeed honestSeed_ne honestAlpha
        E.cfg.challenges.lam =
      ⟨E.cfg, E.exec⟩
  /-- The honest prover's line-number origin: the supplied execution's first compute row has
  `ln_prev = 1`.  `V_comp` (`:1728-1742`) does not check it. -/
  computeLineOrigin : (E.exec.computePubAt ⟨0, E.cfg.compRows_pos⟩).ln_prev = 1
  /-- The buildable input carries `E.q ≤ ringChar K`; the released package needs equality. -/
  q_eq_ringChar : E.q = ringChar K
  skeletonBounded : commitment.skeleton.BoundedBy E.q
  combinedBounded : CombinedBoundedBy K E.q commitment.skeleton
  KszBound : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
    (specializedProblem verifier.raw.timestamp z hz α lmb).cfg.Ksz < ringChar K
  progCapacity : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
    (specializedProblem verifier.raw.timestamp z hz α lmb).exec.derivedRequestIO.length + 1 ≤
      2 ^ (specializedProblem verifier.raw.timestamp z hz α lmb).cfg.orbit.h
  memCapacity : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
    (specializedProblem verifier.raw.timestamp z hz α lmb).exec.derivedResponseIO.length + 1 ≤
      2 ^ (specializedProblem verifier.raw.timestamp z hz α lmb).cfg.orbit.h

/-! ## Objects, families, and the constructed optimized package -/

/-- Threaded objects are a function of the supplied execution: both IO lists are the derived ones.
-/
def buildObjects (E : BuildableNockExecution F K) : StrictThreadedObjects F K where
  cfg := E.cfg
  exec := E.exec
  reqRecs := E.exec.derivedRequestIO
  respRecs := E.exec.derivedResponseIO
  req_eq_derived := rfl
  resp_eq_derived := rfl

/-- Exact compute rows accepted, from the retained semantic input. -/
theorem computeRowsAccepted (E : BuildableNockExecution F K) :
    E.exec.ComputeRowsAccepted :=
  E.chained.semantic.1

/-- Exact memory rows accepted, from the retained semantic input. -/
theorem memoryRowsAccepted (E : BuildableNockExecution F K) :
    E.exec.MemoryRowsAccepted :=
  E.chained.semantic.2.1

theorem zeroChallengePins
    (E : BuildableNockExecution F K) (I : Inputs E)
    (hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K)) :
    ExactFinalChallengeCoordinates I.basis (sampledAssignment E I) (computeChallenge E I) :=
  (historical_zero_compute_challenges_compatible E I hzero).1

theorem hzero_implies_zero_cubic
    (E : BuildableNockExecution F K) (I : Inputs E)
    (_hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K)) :
    True :=
  trivial

/-- Inventory: zero cubic folds already inhabit the released pin, so a nonzero selector fold is
compatible with `OptimizedStrictNockVMROMPackage.computeChallengePins`. -/
theorem zeroChallengePins_of_zero_cubic
    (E : BuildableNockExecution F K) (I : Inputs E) :
    ExactFinalChallengeCoordinates I.basis (sampledAssignment E I) (computeChallenge E I) :=
  computeChallenge_historical_pins_of_zero_cubic E I

/-- **Milestone 5, first half, pin-generic.**  The released `computeChallengePins` field is filled
by a supplied `ExactFinalChallengeCoordinates` inhabitant, not by `hzero`. -/
def buildOptimizedStrictPackageFromPins
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hpins : ExactFinalChallengeCoordinates I.basis (sampledAssignment E I)
      (computeChallenge E I))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha) :
    OptimizedStrictNockVMROMPackage F K I.hOrb where
  objects := buildObjects E
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
  computeChallengePins := hpins
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
  pairedRecordLayout := hprl

/-- **Milestone 5, first half.** -/
def buildOptimizedStrictPackage
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha) :
    OptimizedStrictNockVMROMPackage F K I.hOrb :=
  buildOptimizedStrictPackageFromPins E I R (zeroChallengePins E I hzero) hprl hmore hord hordM

/-- **Milestone 5, second half, pin-generic.** -/
def buildFullPackageFromPins
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hpins : ExactFinalChallengeCoordinates I.basis (sampledAssignment E I)
      (computeChallenge E I))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ := by claim_generated)
    (hF : GeneratedField.PrimeFieldElems F := by prime_field_elems) :
    OptimizedFullStrictNockVMROMPackage F K I.hOrb where
  optimized := buildOptimizedStrictPackageFromPins E I R hpins hprl hmore hord hordM
  honestSeed := R.honestSeed
  honestSeed_ne := R.honestSeed_ne
  honestAlpha := R.honestAlpha
  honest_specialization := R.honest_specialization
  chained := E.chained
  walkFamily := (buildTopology E I).rawFamily
  walkFamily_problem := topology_problem_same_execution E I
  compEnc_inj := (exactFamilyCompletion E I).family.compNodeEncode_labelOf
  memEnc_inj := (exactFamilyCompletion E I).family.memNodeEncode_labelOf
  computeRowsAccepted := computeRowsAccepted E
  memoryRowsAccepted := memoryRowsAccepted E
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
  primeField := hF

/-- **Milestone 5, second half.**  The released constructor still takes `hzero`. -/
def buildFullPackage
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ := by claim_generated)
    (hF : GeneratedField.PrimeFieldElems F := by prime_field_elems) :
    OptimizedFullStrictNockVMROMPackage F K I.hOrb :=
  buildFullPackageFromPins E I R (zeroChallengePins E I hzero) hprl hmore hord hordM hrows hgenF hF

/-- Additive constructor: `ExactFinalChallengeCoordinatesWith` plus zero cubic folds `9` and `11`.
The selector fold `36` may be any field element.  The result is still an
`OptimizedFullStrictNockVMROMPackage` the unchanged released statement consumes. -/
def buildFullPackageWith
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hwith : ExactFinalChallengeCoordinatesWith I.basis (sampledAssignment E I)
      I.computeChallenges (computeChallenge E I))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ := by claim_generated)
    (hF : GeneratedField.PrimeFieldElems F := by prime_field_elems) :
    OptimizedFullStrictNockVMROMPackage F K I.hOrb :=
  buildFullPackageFromPins E I R (historical_pins_of_with_zero_cubic E I hwith) hprl hmore hord hordM hrows hgenF hF

/-- Inventory: the released constructor still requires the whole triple `⟨0,0⟩`.  A package
at a nonzero selector fold needs the additive `buildFullPackageWith` constructor, not a
deletion of this `hzero` field. -/
theorem released_builder_requires_hzero
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    Nonempty (OptimizedFullStrictNockVMROMPackage F K I.hOrb) :=
  ⟨buildFullPackage E I R hzero hprl hmore hord hordM hrows⟩


variable [Fintype F] [DecidableEq F]

/-- **The universal Theorem-5.4 statement.**  The consumed capstone `optimizedFullStrictNockVMROM_of_package` is unchanged. -/
theorem universalOptimizedFullStrictThm54
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hax : FormRAxisBound
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).optimized.sampled
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).optimized.basis)
    (hbasis : FormRBasis
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).optimized.basis)
    (hwidth : FormRWidth F) :
    OptimizedFullStrictThm54Statement (buildFullPackage E I R hzero hprl hmore hord hordM hrows) :=
  optimizedFullStrictNockVMROM_of_package
    (buildFullPackage E I R hzero hprl hmore hord hordM hrows) hax hbasis hwidth

theorem universalContainment
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hax : FormRAxisBound
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).optimized.sampled
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).optimized.basis)
    (hbasis : FormRBasis
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).optimized.basis)
    (hwidth : FormRWidth F) :
    ∀ (ω : JointCoins K) (lmb : K),
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).strategy.Accepts ω lmb →
      ω ∉ ProductionP8Containment.FailureUnion
        (buildFullPackage E I R hzero hprl hmore hord hordM hrows).strategy R.census lmb →
      GenuineTargetAt (buildFullPackage E I R hzero hprl hmore hord hordM hrows).strategy E.q R.Λ ω
        lmb :=
  (universalOptimizedFullStrictThm54 E I R hzero hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).containment

theorem universalFixedFieldSoundness
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hax : FormRAxisBound
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).optimized.sampled
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).optimized.basis)
    (hbasis : FormRBasis
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).optimized.basis)
    (hwidth : FormRWidth F) (lmb : K) :
    |jointProbability
        (FalseAcceptanceSet (buildFullPackage E I R hzero hprl hmore hord hordM hrows).strategy E.q R.Λ
          lmb)| ≤
      (workload (buildFullPackage E I R hzero hprl hmore hord hordM hrows).strategy R.Λ
          (fixedTopologyWorkload (buildFullPackage E I R hzero hprl hmore hord hordM hrows).strategy)
          (fixedAxisWorkload (buildFullPackage E I R hzero hprl hmore hord hordM hrows).strategy) : ℝ) /
        (Fintype.card K : ℝ) :=
  (universalOptimizedFullStrictThm54 E I R hzero hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).p8_fixed_field_soundness
    lmb

/-- The pin-generic constructor still consumes the unchanged released capstone. -/
theorem universalOptimizedFullStrictThm54FromPins
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hpins : ExactFinalChallengeCoordinates I.basis (sampledAssignment E I)
      (computeChallenge E I))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hax : FormRAxisBound
      (buildFullPackageFromPins E I R hpins hprl hmore hord hordM hrows).optimized.sampled
      (buildFullPackageFromPins E I R hpins hprl hmore hord hordM hrows).optimized.basis)
    (hbasis : FormRBasis
      (buildFullPackageFromPins E I R hpins hprl hmore hord hordM hrows).optimized.basis)
    (hwidth : FormRWidth F) :
    OptimizedFullStrictThm54Statement (buildFullPackageFromPins E I R hpins hprl hmore hord hordM hrows) :=
  optimizedFullStrictNockVMROM_of_package
    (buildFullPackageFromPins E I R hpins hprl hmore hord hordM hrows) hax hbasis hwidth

/-- The additive `With` constructor still consumes the unchanged released capstone. -/
theorem universalOptimizedFullStrictThm54With
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hwith : ExactFinalChallengeCoordinatesWith I.basis (sampledAssignment E I)
      I.computeChallenges (computeChallenge E I))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hax : FormRAxisBound
      (buildFullPackageWith E I R hwith hprl hmore hord hordM hrows).optimized.sampled
      (buildFullPackageWith E I R hwith hprl hmore hord hordM hrows).optimized.basis)
    (hbasis : FormRBasis
      (buildFullPackageWith E I R hwith hprl hmore hord hordM hrows).optimized.basis)
    (hwidth : FormRWidth F) :
    OptimizedFullStrictThm54Statement (buildFullPackageWith E I R hwith hprl hmore hord hordM hrows) :=
  optimizedFullStrictNockVMROM_of_package
    (buildFullPackageWith E I R hwith hprl hmore hord hordM hrows) hax hbasis hwidth

theorem buildFullPackage_eq_fromPins_of_hzero
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    buildFullPackage E I R hzero hprl hmore hord hordM hrows =
      buildFullPackageFromPins E I R (zeroChallengePins E I hzero) hprl hmore hord hordM hrows :=
  rfl

/-! ## Same-object receipts -/

/-- The constructed package cannot select another execution: its objects, walk family, exact
family, sampled records, and both optimized chips are the ones derived from `E` and `I`. -/
theorem constructed_same_execution
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    (buildFullPackage E I R hzero hprl hmore hord hordM hrows).objects.cfg = E.cfg ∧
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).objects.exec = E.exec ∧
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).objects.reqRecs = E.exec.derivedRequestIO ∧
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).objects.respRecs = E.exec.derivedResponseIO ∧
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).walkFamily.problem = ⟨E.cfg, E.exec⟩ ∧
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).optimized.family.problem.cfg = E.cfg ∧
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).optimized.family.problem.exec = E.exec ∧
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).optimized.sampled = sampledAssignment E I ∧
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).computeChip = (buildTopology E I).computeChip ∧
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).memoryChip = (buildTopology E I).memoryChip :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem constructed_resources
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    (buildFullPackage E I R hzero hprl hmore hord hordM hrows).computeChip.rap.w = 303 ∧
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).computeChip.rap.s = 418 ∧
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).memoryChip.rap.w = 205 ∧
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).memoryChip.rap.s = 156 :=
  chip_resources E I

theorem constructed_row_budgets
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    (buildFullPackage E I R hzero hprl hmore hord hordM hrows).computeChip.rap.H.card = E.cfg.compRows ∧
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows).memoryChip.rap.H.card =
        RowLayout.memoryM E.exec + 2 * RowLayout.memoryL E.exec :=
  raw_row_cards E I

/-- The axis-side memory production assignment consumed by the constructed package is the
Milestone-4 generic one, on the identical execution. -/
theorem constructed_memoryProduction
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    (buildFullPackage E I R hzero hprl hmore hord hordM hrows).optimized.memoryProduction =
      BuildableAxisWitness.buildableMemoryProductionAssignment E I :=
  rfl

/-! ## F73 instantiation: every arithmetization field is constructed -/

namespace Concrete

open ConcreteStrictPackage
open BuildableConcrete
open BuildableChips.Concrete

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := ConcreteStrictPackage.concrete_char73
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

def inputs73zero : Inputs concreteExecution :=
  inputs73.withComputeChallenges (default : FinalComputeChallengeTuple K73cubic)

theorem inputs73zero_challenges : inputs73zero.computeChallenges = (default : FinalComputeChallengeTuple K73cubic) := rfl

theorem concreteExecution_walk_order :
    2 ≤ concreteExecution.cfg.compRows →
      concreteExecution.cfg.compRows ≤ orderOf inputs73zero.computeWalkAlpha := fun h => by
  have : concreteExecution.cfg.compRows = 1 := rfl
  omega

theorem concreteExecution_memory_walk_order :
    2 ≤ concreteExecution.cfg.memRows →
      concreteExecution.cfg.memRows ≤ orderOf inputs73zero.memoryWalkAlpha := by
  intro _
  have hrows : concreteExecution.cfg.memRows = 6 := rfl
  have hα : inputs73zero.memoryWalkAlpha = honestAlpha := rfl
  have hord : orderOf honestAlpha = 9 := honestAlpha_order
  rw [hrows, hα, hord]
  omega

theorem concreteExecution_alpha_memory_walk_order :
    2 ≤ concreteExecution.cfg.memRows →
      concreteExecution.cfg.memRows ≤ orderOf concreteExecution.cfg.challenges.α := by
  simpa [show inputs73zero.memoryWalkAlpha = concreteExecution.cfg.challenges.α from rfl]
    using concreteExecution_memory_walk_order

/-- F73 `PairedRecordLayout` by fixture listing. -/
theorem concreteExecution_pairedRecordLayout :
    RowLayout.PairedRecordLayout concreteExecution.exec := by
  show RowLayout.PairedRecordLayout (exec honestSeed honestAlpha)
  have hcons :
      RowLayout.consumedRecordList (exec honestSeed honestAlpha)
        = [rowRecord honestSeed honestAlpha] := by
    show (exec honestSeed honestAlpha).memoryRows.flatMap
        (fun row => RowLayout.consumedRecords row.2.2) = _
    rw [(execution_rows honestSeed honestAlpha).2]
    rfl
  have hadd :
      RowLayout.addedRecordList (exec honestSeed honestAlpha)
        = [rowRecord honestSeed honestAlpha] := by
    show (exec honestSeed honestAlpha).memoryRows.flatMap
        (fun row =>
          match row.2.2.st with
          | .read_root => [row.2.2.mem]
          | .decompose | .halt | .verify_child => []) = _
    rw [(execution_rows honestSeed honestAlpha).2]
    rfl
  rw [RowLayout.PairedRecordLayout, hcons, hadd]

/-- F73 honest `ver = (st = read_root)` by fixture listing. -/
theorem concreteExecution_honestVer :
    ∀ row ∈ concreteExecution.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  show ∀ row ∈ (exec honestSeed honestAlpha).memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)
  simp [(execution_rows honestSeed honestAlpha).2, dummyHaltRow, dummyHaltPub,
    readRow, decomposeRow, headRow, verifyRow, tailRow, readPub, decomposePub,
    headPub, verifyPub, tailPub]

/-- The existing F73 committed layer, re-expressed as the exact Milestone-5 residual.  Nothing in
this record is a chip, trace, coordinate, active domain, sampled assignment, or axis conclusion. -/
def residual73 : CommitmentResidual concreteExecution where
  verifier := ConcreteStrictPackage.verifier
  commitment := ConcreteStrictPackage.commitment
  claim_eq := rfl
  scan := fun z hz α lmb =>
    activeFingerprintChecksAt_of_bindsAt (bindsAt_specialized z hz α lmb)
  shapeMatch := fun z hz α lmb =>
    execTreeShapeMatchesAt_of_bindsAt (bindsAt_specialized z hz α lmb)
  rowFrame := fun z hz α lmb =>
    rowFrameChecksAt_of_bindsAt (bindsAt_specialized z hz α lmb)
  slotSemantics := ConcreteStrictPackage.slotSemantics
  recordEquations := ConcreteStrictPackage.recordEquations
  Λ := 2
  census := ConcreteStrictPackage.census
  sizeWindowBound := ConcreteStrictPackage.sizeWindowBound
  honestSeed := honestSeed
  honestSeed_ne := honestSeed_ne
  honestAlpha := honestAlpha
  honest_specialization :=
    verifier_specializedProblem honestSeed honestSeed_ne honestAlpha
  computeLineOrigin := concrete_line_origin
  q_eq_ringChar := ConcreteStrictPackage.q_eq_ringChar
  skeletonBounded := ConcreteStrictPackage.skeletonBounded
  combinedBounded := ConcreteStrictPackage.combinedBounded
  KszBound := ConcreteStrictPackage.KszBound
  progCapacity := ConcreteStrictPackage.progCapacity
  memCapacity := ConcreteStrictPackage.memCapacity

theorem concreteExecution_rowsBound :
    3 * concreteExecution.cfg.compRows < ringChar K73cubic ∧
      concreteExecution.cfg.memRows < ringChar K73cubic := by
  rw [← ConcreteStrictPackage.q_eq_ringChar]
  exact ⟨by decide, by decide⟩

theorem concreteExecution_generated :
    GeneratedField.ClaimGenerated K73cubic residual73.verifier.raw.claim residual73.Λ :=
  GeneratedField.claimGenerated_of_eq rfl rfl
    (OptimizedStrictFullPackage.Concrete.f73_program_generated 2 le_rfl)

/-- The F73 package with a *constructed* arithmetization half.
`hmore` is the remaining Relaxis join at form R (`kMem = 2` dummy halt). -/
def package73 (hmore : BuildableAxisWitness.LaterSeedZeros concreteExecution) :
    OptimizedFullStrictNockVMROMPackage F73 K73cubic 3 :=
  buildFullPackage concreteExecution inputs73zero residual73 inputs73zero_challenges
    concreteExecution_pairedRecordLayout
    hmore
    concreteExecution_walk_order concreteExecution_memory_walk_order concreteExecution_rowsBound
    concreteExecution_generated OptimizedStrictFullPackage.Concrete.f73_primeField

/-- Non-vacuity of the universal theorem: the released fourteen-field statement holds of the
constructed F73 package. -/
theorem statement73
    (hmore : BuildableAxisWitness.LaterSeedZeros concreteExecution)
    (hax : FormRAxisBound (package73 hmore).optimized.sampled (package73 hmore).optimized.basis)
    (hbasis : FormRBasis (package73 hmore).optimized.basis)
    (hwidth : FormRWidth F73) :
    OptimizedFullStrictThm54Statement (package73 hmore) :=
  universalOptimizedFullStrictThm54 concreteExecution inputs73zero residual73
    inputs73zero_challenges concreteExecution_pairedRecordLayout
    hmore
    concreteExecution_walk_order concreteExecution_memory_walk_order concreteExecution_rowsBound
    concreteExecution_generated OptimizedStrictFullPackage.Concrete.f73_primeField
    hax hbasis hwidth

theorem statement73_nonvacuous
    (hmore : BuildableAxisWitness.LaterSeedZeros concreteExecution)
    (hax : FormRAxisBound (package73 hmore).optimized.sampled (package73 hmore).optimized.basis)
    (hbasis : FormRBasis (package73 hmore).optimized.basis)
    (hwidth : FormRWidth F73) :
    Nonempty (OptimizedFullStrictThm54Statement (package73 hmore)) :=
  ⟨statement73 hmore hax hbasis hwidth⟩

theorem regression73
    (hmore : BuildableAxisWitness.LaterSeedZeros concreteExecution)
    (hax : FormRAxisBound (package73 hmore).optimized.sampled (package73 hmore).optimized.basis)
    (hbasis : FormRBasis (package73 hmore).optimized.basis)
    (hwidth : FormRWidth F73) :
    (package73 hmore).objects.cfg = concreteExecution.cfg ∧
      (package73 hmore).objects.exec = concreteExecution.exec ∧
      (package73 hmore).computeChip.rap.w = 303 ∧ (package73 hmore).computeChip.rap.s = 418 ∧
      (package73 hmore).memoryChip.rap.w = 205 ∧ (package73 hmore).memoryChip.rap.s = 156 ∧
      (package73 hmore).computeChip.rap.H.card = concreteExecution.cfg.compRows ∧
      (∀ (ω : JointCoins K73cubic) (lmb : K73cubic), (package73 hmore).strategy.Accepts ω lmb →
        ω ∉ ProductionP8Containment.FailureUnion (package73 hmore).strategy residual73.census lmb →
        GenuineTargetAt (package73 hmore).strategy 73 2 ω lmb) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (constructed_resources concreteExecution inputs73zero residual73
      inputs73zero_challenges concreteExecution_pairedRecordLayout
      hmore
      concreteExecution_walk_order concreteExecution_memory_walk_order concreteExecution_rowsBound
      concreteExecution_generated OptimizedStrictFullPackage.Concrete.f73_primeField).1
  · exact (constructed_resources concreteExecution inputs73zero residual73
      inputs73zero_challenges concreteExecution_pairedRecordLayout
      hmore
      concreteExecution_walk_order concreteExecution_memory_walk_order concreteExecution_rowsBound
      concreteExecution_generated OptimizedStrictFullPackage.Concrete.f73_primeField).2.1
  · exact (constructed_resources concreteExecution inputs73zero residual73
      inputs73zero_challenges concreteExecution_pairedRecordLayout
      hmore
      concreteExecution_walk_order concreteExecution_memory_walk_order concreteExecution_rowsBound
      concreteExecution_generated OptimizedStrictFullPackage.Concrete.f73_primeField).2.2.1
  · exact (constructed_resources concreteExecution inputs73zero residual73
      inputs73zero_challenges concreteExecution_pairedRecordLayout
      hmore
      concreteExecution_walk_order concreteExecution_memory_walk_order concreteExecution_rowsBound
      concreteExecution_generated OptimizedStrictFullPackage.Concrete.f73_primeField).2.2.2
  · exact (constructed_row_budgets concreteExecution inputs73zero residual73
      inputs73zero_challenges concreteExecution_pairedRecordLayout
      hmore
      concreteExecution_walk_order concreteExecution_memory_walk_order concreteExecution_rowsBound
      concreteExecution_generated OptimizedStrictFullPackage.Concrete.f73_primeField).1
  · exact universalContainment concreteExecution inputs73zero residual73
      inputs73zero_challenges concreteExecution_pairedRecordLayout
      hmore
      concreteExecution_walk_order concreteExecution_memory_walk_order concreteExecution_rowsBound
      concreteExecution_generated OptimizedStrictFullPackage.Concrete.f73_primeField
      hax hbasis hwidth

end Concrete

end

end BuildablePackage
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.BuildablePackage.buildObjects
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.computeRowsAccepted
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.memoryRowsAccepted
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.zeroChallengePins
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.hzero_implies_zero_cubic
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.zeroChallengePins_of_zero_cubic
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.buildOptimizedStrictPackageFromPins
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.buildOptimizedStrictPackage
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.buildFullPackageFromPins
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.buildFullPackage
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.buildFullPackageWith
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.released_builder_requires_hzero
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.universalOptimizedFullStrictThm54
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.universalOptimizedFullStrictThm54FromPins
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.universalOptimizedFullStrictThm54With
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.buildFullPackage_eq_fromPins_of_hzero
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.universalContainment
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.universalFixedFieldSoundness
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.constructed_same_execution
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.constructed_resources
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.constructed_row_budgets
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.constructed_memoryProduction
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.Concrete.residual73
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.Concrete.package73
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.Concrete.statement73
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.Concrete.regression73
