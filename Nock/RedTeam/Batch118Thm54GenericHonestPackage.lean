import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.RedTeam.Batch117Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  Additive `inputsOfWalkSample I a g` sets chip
`computeWalkAlpha` / `walkGamma` from the same fibre pair `(a, g)` that
`honestCoin` already quantifies, and those equal `alphaC` / `gamma` of
`honestCoin E a g`.  `packageOf`'s existing signature is unchanged;
`packageOfWalkSample` is `packageOf` at the overlay.  Fibre `Accepts`
stays `∀ a g` (and even `∀ a' g'` on each overlaid package).  F73 chip
walk α differs at `(0,0)` versus `(1,0)`.  FiniteIO `(gamma, pole)` plus
goodness flags stay named: not a coordinate of `ChallengeVector` /
`SemanticIOPreimage` / `honestCoin`.  Compiler folds `9`/`11`/`36` are
unchanged.  Remaining `Inputs` fields stay named (`memoryWalkAlpha`, IO,
compiler/interpolation, `hOrb`/`basis`/`orbit`/`activeDomains`).
Accounting remains `11+1+2`.  Walk overlay is not rounded into a paper RAP or
capstone failure.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch118

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.AxisBridge
open Nock.Framework

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## A. Walk overlay is 1-1 with `honestCoin` `(a, g)` -/

/-- Overlay writes chip walk coins from the free pair -/
theorem overlay_sets_walk_coins_from_pair {E : BuildableNockExecution F K}
    (I : Inputs E) (a g : K) :
    (inputsOfWalkSample I a g).computeWalkAlpha = a ∧
      (inputsOfWalkSample I a g).walkGamma = g :=
  ⟨rfl, rfl⟩

/-- Those coins are `alphaC` / `gamma` of the fibre coin -/
theorem overlay_eq_honestCoin_walk {E : BuildableNockExecution F K}
    (I : Inputs E) (a g : K) :
    (inputsOfWalkSample I a g).computeWalkAlpha = alphaC (honestCoin E a g) ∧
      (inputsOfWalkSample I a g).walkGamma = gamma (honestCoin E a g) ∧
      honestCoin E a g = ((a, g), (E.cfg.challenges.α, E.cfg.challenges.z)) :=
  ⟨rfl, rfl, rfl⟩

/-- Distinct later-round pairs remain distinct after overlay. -/
theorem overlay_injective_on_walk_pair {E : BuildableNockExecution F K}
    (I : Inputs E) {a g a' g' : K}
    (h : inputsOfWalkSample I a g = inputsOfWalkSample I a' g') :
    a = a' ∧ g = g' := by
  exact ⟨congrArg Inputs.computeWalkAlpha h, congrArg Inputs.walkGamma h⟩

/-- Chip family consumes the overlaid pair, not a different object. -/
theorem family_reads_overlay_walk_pair {E : BuildableNockExecution F K}
    (I : Inputs E) (a g : K) :
    (zeroEndpointFamily E (inputsOfWalkSample I a g)).computeWalkAlpha = a ∧
      (zeroEndpointFamily E (inputsOfWalkSample I a g)).walkGamma = g ∧
      (zeroEndpointFamily E (inputsOfWalkSample I a g)).memoryWalkAlpha =
        I.memoryWalkAlpha :=
  ⟨rfl, rfl, rfl⟩

theorem overlay_does_not_thread_memoryWalkAlpha
    {E : BuildableNockExecution F K} (I : Inputs E) (a g : K) :
    (inputsOfWalkSample I a g).memoryWalkAlpha = I.memoryWalkAlpha ∧
      alphaM (honestCoin E a g) = E.cfg.challenges.α :=
  ⟨rfl, rfl⟩

theorem atJointCoins_threads_three_walk_challenges
    (problem : ExactCanonicalRAPProblem F K)
    (hchar : NodeEncoding.StateTagChar K) (ω : JointCoins K)
    (requests responses outMem : IOField K)
    (progIO_capacity :
      problem.exec.derivedRequestIO.length + 1 ≤ 2 ^ problem.cfg.orbit.h)
    (memIO_capacity :
      problem.exec.derivedResponseIO.length + 1 ≤ 2 ^ problem.cfg.orbit.h) :
    let R := PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncodersAtJointCoins
      problem hchar ω requests responses outMem progIO_capacity memIO_capacity
    R.computeWalkAlpha = alphaC ω ∧
      R.walkGamma = gamma ω ∧
      R.memoryWalkAlpha = alphaM ω :=
  ⟨rfl, rfl, rfl⟩

/-! ## B. `packageOf` signature unchanged; overlay is additive -/

/-- Independent expansion of the record `packageOf` still consumes. -/
theorem inputs_is_fifteen_fields {E : BuildableNockExecution F K}
    (I : Inputs E) :
    I =
      { stateTagChar := I.stateTagChar
        computeWalkAlpha := I.computeWalkAlpha
        memoryWalkAlpha := I.memoryWalkAlpha
        walkGamma := I.walkGamma
        hOrb := I.hOrb
        basis := I.basis
        orbit := I.orbit
        activeDomains := I.activeDomains
        ioCoins := I.ioCoins
        ioPoleHitGood := I.ioPoleHitGood
        ioGammaGood := I.ioGammaGood
        ioLogDerivGood := I.ioLogDerivGood
        computeChallenges := I.computeChallenges
        memoryScalarChallenge := I.memoryScalarChallenge
        memoryExtensionFold := I.memoryExtensionFold
        interPoleHitGood := I.interPoleHitGood
        honestVer := I.honestVer
        ioGood10 := I.ioGood10
        interPoleHitGood10 := I.interPoleHitGood10 } := by
  cases I
  rfl

/-- `packageOf` is still `Data` plus `11 < ringChar` plus named `Inputs`. -/
theorem packageOf_signature_unchanged
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    packageOf D hgt I hprl hmore hord hordM hrows hgenF hF =
      buildFullPackageWith E I (commitmentResidualOfArrays_of_char D hgt)
        (computeChallenge_pins E I) hprl hmore hord hordM hrows hgenF hF :=
  rfl

/-- Walk-sample package is `packageOf` at the overlay.  Additive. -/
theorem packageOfWalkSample_is_packageOf_at_overlay
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (a g : K)
    (hordA : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf a) :
    packageOfWalkSample D hgt I hprl hmore hord hordM hrows hgenF hF a g hordA =
      packageOf D hgt (inputsOfWalkSample I a g) hprl hmore
        (fun hrows => by simpa [inputsOfWalkSample] using hordA hrows)
        (fun hrows => by simpa [inputsOfWalkSample] using hordM hrows) hrows :=
  rfl

/-- Constructed sampled assignment sits at the overlaid record. -/
theorem packageOfWalkSample_sampled_reads_overlay
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (a g : K)
    (hordA : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf a) :
    (packageOfWalkSample D hgt I hprl hmore hord hordM hrows hgenF hF a g hordA).optimized.sampled =
      sampledAssignment E (inputsOfWalkSample I a g) :=
  rfl

/-! ## C. `∀ a g` preserved; overlay does not pick a unique pair -/

/-- Completeness at the threaded sample is still `∀ a g`. -/
theorem overlay_fibre_accepts_still_forall_ag
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (horder : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α) :
    ∀ (a g : K)
      (hordA : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf a),
      (packageOfWalkSample D hgt I hprl hmore hord hordM hrows hgenF hF a g hordA).strategy.Accepts
        (honestCoin E a g) E.cfg.challenges.lam :=
  packageOfWalkSample_fibre_accepts D hgt I hprl hmore hord hordM hrows hgenF hF horder

/-- Residual `Accepts` on one overlaid package remains `∀ a' g'`.
Chip walk coins are not that quantifier -/
theorem overlay_accepts_ignores_chip_walk_pair
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (horder : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α) :
    ∀ (a g a' g' : K)
      (hordA : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf a),
      (packageOfWalkSample D hgt I hprl hmore hord hordM hrows hgenF hF a g hordA).strategy.Accepts
        (honestCoin E a' g') E.cfg.challenges.lam :=
  packageOfWalkSample_fibre_accepts_still_forall_ag D hgt I hprl hmore hord hordM hrows hgenF hF horder

/-- Named `packageOf` (no overlay) is still `∀ a g` under one `Inputs`. -/
theorem packageOf_fibre_accepts_still_forall_ag
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (horder : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α) :
    ∀ a g : K,
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts (honestCoin E a g) E.cfg.challenges.lam :=
  GenericHonestPackage.packageOf_fibre_accepts_still_forall_ag D hgt I hprl hmore hord hordM hrows hgenF hF
    horder

/-! ## D. IO coins stay named; overlay does not inhabit them -/

/-- Table challenge vector is `(a,b,c,α,z,β,γ)`, not FiniteIO `(gamma, pole)`. -/
theorem challengeVector_is_seven_table_fields (v : ChallengeVector K) :
    v = ⟨v.a, v.b, v.c, v.α, v.z, v.β, v.γ, v.lam⟩ := by
  cases v
  rfl

/-- `SemanticIOPreimage` is timestamp-bounded derived IO. -/
theorem semanticIOPreimage_has_no_io_coins
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticIOPreimage cfg exec) :
    w =
      { timestampBound := w.timestampBound
        timestampBound_le_order := w.timestampBound_le_order
        semanticRequests := w.semanticRequests
        semanticResponses := w.semanticResponses
        requestTimestampBound := w.requestTimestampBound
        responseTimestampBound := w.responseTimestampBound
        semantic_lmio := w.semantic_lmio
        requestTimestamp_determines := w.requestTimestamp_determines
        requests_bridge := w.requests_bridge
        responses_bridge := w.responses_bridge } := by
  cases w
  rfl

/-- `honestCoin` is four `K` coordinates.  No FiniteIO pole. -/
theorem honestCoin_is_not_ioCoins
    (E : BuildableNockExecution F K) (a g : K) :
    honestCoin E a g =
      ((alphaC (honestCoin E a g), gamma (honestCoin E a g)),
        (alphaM (honestCoin E a g), nprSeed (honestCoin E a g))) :=
  rfl

/-- FiniteIO coins are `(gamma, pole)` -/
theorem ioCoins_are_gamma_and_pole (c : FiniteIO.IOCoins K) :
    c = ⟨c.gamma, c.pole⟩ := by
  cases c
  rfl

/-- Overlay copies FiniteIO coins and goodness flags. -/
theorem overlay_preserves_io {E : BuildableNockExecution F K}
    (I : Inputs E) (a g : K) :
    (inputsOfWalkSample I a g).ioCoins = I.ioCoins ∧
      (inputsOfWalkSample I a g).ioPoleHitGood = I.ioPoleHitGood ∧
      (inputsOfWalkSample I a g).ioGammaGood = I.ioGammaGood ∧
      (inputsOfWalkSample I a g).ioLogDerivGood = I.ioLogDerivGood :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Sampled assignment still reads the named FiniteIO coins. -/
theorem sampled_of_overlay_reads_named_io
    {E : BuildableNockExecution F K} (I : Inputs E) (a g : K) :
    (sampledAssignment E (inputsOfWalkSample I a g)).sampled.coins =
      I.ioCoins :=
  rfl

/-- Overlay walk `γ` is the fibre parameter `g`, not table `ChallengeVector.γ`. -/
theorem overlay_walkGamma_is_fibre_not_table
    {E : BuildableNockExecution F K} (I : Inputs E) (a g : K) :
    (inputsOfWalkSample I a g).walkGamma = g ∧
      E.cfg.challenges.γ = E.cfg.challenges.γ :=
  ⟨rfl, rfl⟩

/-! ## E. -/

theorem computeChallenges_are_folds_9_11_36
    (c : FinalComputeChallengeTuple K) :
    c = ⟨c.eqA, c.eqB, c.eqC⟩ := by
  cases c
  rfl

theorem overlay_preserves_cubic {E : BuildableNockExecution F K}
    (I : Inputs E) (a g : K) :
    (inputsOfWalkSample I a g).computeChallenges = I.computeChallenges ∧
      (inputsOfWalkSample I a g).computeChallenges =
        I.computeChallenges :=
  ⟨rfl, rfl⟩

theorem challenge36_is_base_field (c : FinalComputeChallengeTuple K) :
    c = ⟨c.eqA, c.eqB, c.eqC⟩ := by
  cases c; rfl

theorem fold2_and_walk_sample_commute {E : BuildableNockExecution F K}
    (I : Inputs E) (a g : K) :
    inputsOfWalkSample (inputsFold2 I) a g =
      inputsFold2 (inputsOfWalkSample I a g) :=
  rfl

/-! ## F. Not a silent inhabit of the whole `Inputs` record -/

/-- Named remainder after the walk overlay, including `activeDomains`. -/
theorem overlay_preserves_named_remainder {E : BuildableNockExecution F K}
    (I : Inputs E) (a g : K) :
    (inputsOfWalkSample I a g).stateTagChar = I.stateTagChar ∧
      (inputsOfWalkSample I a g).memoryWalkAlpha = I.memoryWalkAlpha ∧
      (inputsOfWalkSample I a g).hOrb = I.hOrb ∧
      (inputsOfWalkSample I a g).basis = I.basis ∧
      (inputsOfWalkSample I a g).orbit = I.orbit ∧
      (inputsOfWalkSample I a g).activeDomains = I.activeDomains ∧
      (inputsOfWalkSample I a g).ioCoins = I.ioCoins ∧
      (inputsOfWalkSample I a g).computeChallenges = I.computeChallenges ∧
      (inputsOfWalkSample I a g).memoryScalarChallenge =
        I.memoryScalarChallenge ∧
      (inputsOfWalkSample I a g).memoryExtensionFold = I.memoryExtensionFold :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem censusRecordPremises_eta_still_five
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } :=
  Batch117.censusRecordPremises_eta_still_five C

theorem dataOfCensusAtConsumed_still_names_remaining_extras
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (slotSemantics :
      ∀ s ∈ computeSkeletonRows
          (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
        ServedLookupBridge.SkeletonSlotSemantics s)
    (census :
      EdgeComparisonCensus.CombinedSkeletonCensus K
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ)
    (sizeWindowBound :
      SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ)
    (skeletonBounded :
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q)
    (hgt : 11 < ringChar K)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    let D := dataOfCensusAtConsumed E P M slotSemantics census
      sizeWindowBound skeletonBounded hgt hln
    D.slotSemantics = slotSemantics ∧
      D.census = census ∧
      D.sizeWindowBound = sizeWindowBound ∧
      D.skeletonBounded = skeletonBounded :=
  Batch117.dataOfCensusAtConsumed_still_names_remaining_extras E P M
    slotSemantics census sizeWindowBound skeletonBounded hgt hln

theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } :=
  Batch117.residualPremises_eta_still_four P

theorem memoryRecordPremises_eta_still_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } :=
  Batch117.memoryRecordPremises_eta_still_two M

theorem packageOf_not_forall_omega
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) (lmb : K) :
    ¬ ∀ ω : JointCoins K, (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts ω lmb :=
  GenericHonestPackage.packageOf_not_forall_omega D hgt I hprl hmore hord hordM hrows hgenF hF (lmb := lmb)

theorem released_builder_still_takes_hzero
    {E : BuildableNockExecution F K}
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = default)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    Nonempty (OptimizedFullStrictNockVMROMPackage F K I.hOrb) :=
  ⟨buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF⟩

/-- NMR address space remains the Nat-cast memory-table axis. -/
theorem nmr_axis_is_not_inputs_sample
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  M.axisNat

theorem sizeWindowBound_still_leaves_le_Lambda
    {S : SemanticSkeleton} {Λ : ℕ} :
    SizeWindowCounting.SizeWindowNounsBoundedBy S Λ =
      ∀ n ∈ SizeWindowCounting.skeletonSizeWindowNouns S, n.leaves ≤ Λ :=
  Batch117.sizeWindowBound_still_leaves_le_Lambda

inductive ReviewedField118
  | structural
  | optimized_chips
  | shared_io
  | perfect_completeness
  | containment
  | walk_bounds
  | p8_fixed_field_soundness
  | p8_fixed_field_bits
  | acceptance_to_target
  | complete_false_acceptance_bound
  | complete_false_acceptance_bits
  | exact_resources
  | row_budgets
  | shared_forest_axis
deriving DecidableEq

def substantiveFields118 : List ReviewedField118 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields118 : List ReviewedField118 := [.structural]

def residualFields118 : List ReviewedField118 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- The walk overlay is not a statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields118.length = 11 ∧
      typeSummaryFields118.length = 1 ∧
      residualFields118 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields118.length = 2 ∧
      (substantiveFields118 ++ typeSummaryFields118 ++ residualFields118).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

variable [Fintype F] [DecidableEq F]

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  ⟨optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth, rfl⟩

theorem statementOfWalkSample_still_takes_named_inputs
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (a g : K)
    (hordA : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf a)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound
      (packageOfWalkSample D hgt I hprl hmore hord hordM hrows hgenF hF a g hordA).optimized.sampled
      (packageOfWalkSample D hgt I hprl hmore hord hordM hrows hgenF hF a g hordA).optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis
      (packageOfWalkSample D hgt I hprl hmore hord hordM hrows hgenF hF a g hordA).optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement (packageOfWalkSample D hgt I hprl hmore hord hordM hrows hgenF hF a g hordA) :=
  statementOfWalkSample D hgt I hprl hmore hord hordM hrows hgenF hF a g hordA hax hbasis hwidth

/-! ## G. F73 two-pair witness is non-vacuous -/

namespace Concrete

open ConcreteStrictPackage
open BuildableConcrete
open HonestCommitment.Concrete
open GenericHonestArrays.Concrete
open BuildableChips.Concrete
open GenericHonestPackage.Concrete

local instance : Fact (Nat.Prime 73) := concrete_prime73
noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- F73 overlay walk α differs at `(0,0)` versus `(1,0)`.  Not a unique pair. -/
theorem f73_walk_alpha_differs_at_zero_zero_vs_one_zero :
    (inputs73Walk 0 0).computeWalkAlpha ≠
        (inputs73Walk 1 0).computeWalkAlpha ∧
      (inputs73Walk 0 0).computeWalkAlpha = 0 ∧
      (inputs73Walk 1 0).computeWalkAlpha = 1 ∧
      (inputs73Walk 0 0).computeWalkAlpha =
        alphaC (honestCoin concreteExecution 0 0) ∧
      (inputs73Walk 1 0).computeWalkAlpha =
        alphaC (honestCoin concreteExecution 1 0) := by
  refine ⟨?hne, rfl, rfl, rfl, rfl⟩
  intro h
  exact zero_ne_one h

/-- F73 overlay walk γ differs at `(0,0)` versus `(0,1)`. -/
theorem f73_walk_gamma_differs_at_zero_zero_vs_zero_one :
    (inputs73Walk 0 0).walkGamma ≠ (inputs73Walk 0 1).walkGamma ∧
      (inputs73Walk 0 0).walkGamma = 0 ∧
      (inputs73Walk 0 1).walkGamma = 1 := by
  refine ⟨?hne, rfl, rfl⟩
  intro h
  exact zero_ne_one h

/-- Overlay walk γ at `(0,1)` is not table `ChallengeVector.γ` (`0` on F73). -/
theorem f73_overlay_walkGamma_ne_table_gamma :
    (inputs73Walk 0 1).walkGamma ≠ concreteExecution.cfg.challenges.γ ∧
      concreteExecution.cfg.challenges.γ = 0 := by
  refine ⟨?hne, rfl⟩
  intro h
  exact zero_ne_one h.symm

/-- Overlay does not inhabit FiniteIO coins -/
theorem f73_overlay_preserves_io_and_folds :
    (inputs73Walk 0 0).ioCoins = inputs73Fold2.ioCoins ∧
      (inputs73Walk 1 0).ioCoins = inputs73Fold2.ioCoins ∧
      (inputs73Walk 0 0).computeChallenges = inputs73Fold2.computeChallenges ∧
      (inputs73Walk 1 0).memoryWalkAlpha = inputs73Fold2.memoryWalkAlpha :=
  ⟨rfl, rfl, rfl, rfl⟩

-- Form R leftover LaterSeedZeros residual.
variable (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution)
include hmore73

theorem f73_packageOf_signature_unchanged :
    package73Of hmore73 = packageOf data73 f73_char_gt_eleven inputs73Fold2
      BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
      hmore73
      BuildablePackage.Concrete.concreteExecution_walk_order
    BuildablePackage.Concrete.concreteExecution_memory_walk_order
    BuildablePackage.Concrete.concreteExecution_rowsBound
    data73_generated OptimizedStrictFullPackage.Concrete.f73_primeField :=
  rfl

theorem f73_walk_package_is_additive (a g : K73cubic) :
    package73OfWalk hmore73 a g =
      packageOf data73 f73_char_gt_eleven (inputs73Walk a g)
        BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
        hmore73
        (f73_walkOrderA a)
        BuildablePackage.Concrete.concreteExecution_memory_walk_order
        BuildablePackage.Concrete.concreteExecution_rowsBound
        data73_generated OptimizedStrictFullPackage.Concrete.f73_primeField :=
  rfl

theorem f73_not_forall_omega (lmb : K73cubic) :
    ¬ ∀ ω : JointCoins K73cubic, (package73Of hmore73).strategy.Accepts ω lmb :=
  GenericHonestPackage.Concrete.package73Of_not_forall_omega hmore73 (lmb := lmb)

end Concrete

#print axioms overlay_sets_walk_coins_from_pair
#print axioms overlay_eq_honestCoin_walk
#print axioms overlay_injective_on_walk_pair
#print axioms family_reads_overlay_walk_pair
#print axioms overlay_does_not_thread_memoryWalkAlpha
#print axioms atJointCoins_threads_three_walk_challenges
#print axioms inputs_is_fifteen_fields
#print axioms packageOf_signature_unchanged
#print axioms packageOfWalkSample_is_packageOf_at_overlay
#print axioms packageOfWalkSample_sampled_reads_overlay
#print axioms overlay_fibre_accepts_still_forall_ag
#print axioms overlay_accepts_ignores_chip_walk_pair
#print axioms packageOf_fibre_accepts_still_forall_ag
#print axioms challengeVector_is_seven_table_fields
#print axioms semanticIOPreimage_has_no_io_coins
#print axioms honestCoin_is_not_ioCoins
#print axioms ioCoins_are_gamma_and_pole
#print axioms overlay_preserves_io
#print axioms sampled_of_overlay_reads_named_io
#print axioms overlay_walkGamma_is_fibre_not_table
#print axioms computeChallenges_are_folds_9_11_36
#print axioms overlay_preserves_cubic
#print axioms challenge36_is_base_field
#print axioms fold2_and_walk_sample_commute
#print axioms overlay_preserves_named_remainder
#print axioms censusRecordPremises_eta_still_five
#print axioms dataOfCensusAtConsumed_still_names_remaining_extras
#print axioms residualPremises_eta_still_four
#print axioms memoryRecordPremises_eta_still_two
#print axioms packageOf_not_forall_omega
#print axioms released_builder_still_takes_hzero
#print axioms nmr_axis_is_not_inputs_sample
#print axioms sizeWindowBound_still_leaves_le_Lambda
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms statementOfWalkSample_still_takes_named_inputs
#print axioms Concrete.f73_walk_alpha_differs_at_zero_zero_vs_one_zero
#print axioms Concrete.f73_walk_gamma_differs_at_zero_zero_vs_zero_one
#print axioms Concrete.f73_overlay_walkGamma_ne_table_gamma
#print axioms Concrete.f73_overlay_preserves_io_and_folds
#print axioms Concrete.f73_packageOf_signature_unchanged
#print axioms Concrete.f73_walk_package_is_additive
#print axioms Concrete.f73_not_forall_omega

end
end Nock.RedTeam.Batch118
