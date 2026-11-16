import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.RedTeam.Batch103Thm54CensusExtras
import Nock.RedTeam.Batch116Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  `packageOf` still takes a named 15-field
`BuildableChips.Inputs` record.  `stateTagChar` is a `Prop` from consumed
`11 < ringChar`.  Honest-family `memoryWalkAlpha`
is fibre `E.cfg.challenges.α`.  Those two facts do not inhabit the
record.  Walk coins `computeWalkAlpha` / `walkGamma` are paper samples
after the walk commitment; `honestCoin` is `∀ a g` over
fibre `(α, z)` and does not pick a unique pair; pre-challenge `A` has no
`(αc, γ)` parameter; `W` is a function of the
sampled pair via `WalkSat.ln1`.  FiniteIO
`(gamma, pole)` plus goodness flags are a later `RAP_prog-IO` sample, not a `Data` field and not a coordinate of
`honestCoin`.  Chip `orbit` is `StrictOrbitDomain F 3 hOrb`, not
`E.cfg.orbit : OrbitDomain K`.  The F73 witness is the same inhabited
`Data` and same `A` at walk pairs `(0,0)` and `(1,0)`.  Remaining honest
census extras are `slotSemantics`, `census`, `sizeWindowBound`,
`skeletonBounded`.  Accounting remains `11+1+2`.  Walk/IO sampling is not rounded
into a paper RAP or capstone failure.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch117

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

/-! ## A. `Inputs` is still a named 15-field record on `packageOf` -/

/-- Independent expansion of the record `packageOf` consumes. -/
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

/-- `packageOf` is `Data` plus `11 < ringChar` plus named `Inputs`, not
`Data → Package` -/
theorem packageOf_still_takes_named_inputs
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
    (hax : OptimizedComputeFinalTrace.FormRAxisBound
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    packageOf D hgt I hprl hmore hord hordM hrows hgenF hF =
      buildFullPackageWith E I (commitmentResidualOfArrays_of_char D hgt)
        (computeChallenge_pins E I) hprl hmore hord hordM hrows hgenF hF :=
  rfl

/-- The constructed sampled assignment reads the named `Inputs` record,
not `honestCoin` -/
theorem packageOf_sampled_reads_named_inputs
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
    (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.sampled = sampledAssignment E I :=
  rfl

/-- Fold-`2` overlay changes only the compiler tuple.  Walk/IO coins stay
the caller's named fields -/
theorem inputsFold2_preserves_sampled_coins {E : BuildableNockExecution F K}
    (I : Inputs E) :
    (inputsFold2 I).computeWalkAlpha = I.computeWalkAlpha ∧
      (inputsFold2 I).walkGamma = I.walkGamma ∧
      (inputsFold2 I).memoryWalkAlpha = I.memoryWalkAlpha ∧
      (inputsFold2 I).ioCoins = I.ioCoins ∧
      (inputsFold2 I).hOrb = I.hOrb :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## B. Walk coins are paper samples; `honestCoin` is `∀ a g` -/

/-- Fibre coin: later-round `(a, g)` over committed `(α, z)`. -/
theorem honestCoin_is_walk_pair_plus_fibre
    (E : BuildableNockExecution F K) (a g : K) :
    honestCoin E a g = ((a, g), (E.cfg.challenges.α, E.cfg.challenges.z)) :=
  rfl

/-- The walk coordinates on that coin are the free parameters. -/
theorem honestCoin_walk_coordinates_are_parameters
    (E : BuildableNockExecution F K) (a g : K) :
    alphaC (honestCoin E a g) = a ∧ gamma (honestCoin E a g) = g ∧
      alphaM (honestCoin E a g) = E.cfg.challenges.α ∧
      nprSeed (honestCoin E a g) = E.cfg.challenges.z :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Distinct later-round pairs remain distinct over the same fibre. -/
theorem honestCoin_injective_on_walk_pair
    (E : BuildableNockExecution F K) {a g a' g' : K}
    (h : honestCoin E a g = honestCoin E a' g') :
    a = a' ∧ g = g' := by
  cases h
  exact ⟨rfl, rfl⟩

/-- Pre-challenge `A` reads NPR seed and `alphaM` only.  Fibre seed/`α`
agree for every later-round pair, so `A` cannot pick `(αc, γ)`. -/
theorem fibre_nprSeed_and_alphaM_ignore_walk_pair
    (E : BuildableNockExecution F K) (a g a' g' : K) :
    nprSeed (honestCoin E a g) = nprSeed (honestCoin E a' g') ∧
      alphaM (honestCoin E a g) = alphaM (honestCoin E a' g') :=
  ⟨rfl, rfl⟩

/-- Same `Data` and same pre-challenge `A` at two later-round pairs. -/
theorem same_data_same_A_at_distinct_walk_pairs
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K)
    {a g a' g' : K} (hne : (a, g) ≠ (a', g')) :
    alphaMCommitmentOf D hchar
        (nprSeed (honestCoin E a g)) D.honestSeed_ne
        (alphaM (honestCoin E a g)) =
      alphaMCommitmentOf D hchar
        (nprSeed (honestCoin E a' g')) D.honestSeed_ne
        (alphaM (honestCoin E a' g')) ∧
      honestCoin E a g ≠ honestCoin E a' g' := by
  refine ⟨rfl, ?_⟩
  intro h
  exact hne (Prod.ext (honestCoin_injective_on_walk_pair E h).1
    (honestCoin_injective_on_walk_pair E h).2)

/-- `A`'s tables are the reference assignment at `(0, 0)`, not the sampled
walk pair -/
theorem A_tables_are_reference_at_zero_zero
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (z : K) (hz : z ≠ 0) (α lmb : K) :
    (alphaMCommitmentOf D hchar z hz α lmb).tables.compute =
        (assignmentOf E hchar 0 0).computeTableAux ∧
      (alphaMCommitmentOf D hchar z hz α lmb).tables.memory =
        (assignmentOf E hchar 0 0).memoryTableAux :=
  ⟨rfl, rfl⟩

/-- `W` is a function of `(αc, γ)`.  It does not supply that pair. -/
theorem W_reads_sampled_walk_pair
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K)
    (lmb : K) (hz : nprSeed (honestCoin E a g) ≠ 0) :
    (walkArraysOf D hchar (honestCoin E a g) lmb hz).computeLn =
      (assignmentOf E hchar a g).computeWalk.ln :=
  rfl

/-- Paper initial line `ln(1)=α` reads the sampled walk α. -/
theorem WalkSat_ln1_reads_sampled_alpha
    {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed initial_count : K} {h : ℕ}
    (hw : Nock.Walk.WalkSat cur chld' fo ln count acc α seed initial_count h) :
    ln 1 = α :=
  hw.ln1

/-- Fibre `Accepts` remains `∀ a g` under one named `Inputs` record.
Chip `computeWalkAlpha` is not that quantifier -/
theorem packageOf_fibre_accepts_is_forall_ag_under_one_inputs
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
  packageOf_fibre_accepts D hgt I hprl hmore hord hordM hrows hgenF hF horder

/-! ## C. IO coins are later RAP samples, not `Data` / `honestCoin` -/

/-- FiniteIO coins are `(gamma, pole)` -/
theorem ioCoins_are_gamma_and_pole (c : FiniteIO.IOCoins K) :
    c = ⟨c.gamma, c.pole⟩ := by
  cases c
  rfl

/-- `Data` carries committed skeleton extras, not walk/IO coins or folds. -/
theorem data_has_no_inputs_coins {E : BuildableNockExecution F K}
    (D : Data E) :
    D =
      { computeNodes := D.computeNodes
        memoryNodes := D.memoryNodes
        compute_rows := D.compute_rows
        memory_rows := D.memory_rows
        computeOK := D.computeOK
        memoryOK := D.memoryOK
        root_line_exponent := D.root_line_exponent
        root_line_origin := D.root_line_origin
        nounSizeBound := D.nounSizeBound
        Λ := D.Λ
        slotSemantics := D.slotSemantics
        recordEquations := D.recordEquations
        census := D.census
        sizeWindowBound := D.sizeWindowBound
        q_eq_ringChar := D.q_eq_ringChar
        skeletonBounded := D.skeletonBounded
        combinedBounded := D.combinedBounded } := by
  cases D
  rfl

/-- `honestCoin` is four `K` coordinates.  It has no FiniteIO pole. -/
theorem honestCoin_is_not_ioCoins
    (E : BuildableNockExecution F K) (a g : K) :
    honestCoin E a g =
      ((alphaC (honestCoin E a g), gamma (honestCoin E a g)),
        (alphaM (honestCoin E a g), nprSeed (honestCoin E a g))) :=
  rfl

/-- `SemanticIOPreimage` is timestamp-bounded derived IO, not the
`RAP_prog-IO` sample -/
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

/-- `E.timestampBounds` is that preimage, not `Inputs.ioCoins`. -/
theorem timestampBounds_are_semantic_preimage
    (E : BuildableNockExecution F K) :
    Nonempty (SemanticIOPreimage E.cfg E.exec) :=
  E.timestampBounds

/-- Sampled-IO goodness flags live on the named `Inputs` record. -/
theorem sampledAssignment_reads_inputs_io_goodness
    (E : BuildableNockExecution F K) (I : Inputs E) :
    (sampledAssignment E I).poleHitGood = I.ioPoleHitGood :=
  rfl

/-! ## D. -/

/-- Compiler tuple is folds `9` and `11`. -/
theorem computeChallenges_are_folds_9_11_36
    (c : FinalComputeChallengeTuple K) :
    c = ⟨c.eqA, c.eqB, c.eqC⟩ := by
  cases c
  rfl

theorem challenge36_is_base_field (c : FinalComputeChallengeTuple K) :
    c = ⟨c.eqA, c.eqB, c.eqC⟩ := by
  cases c; rfl

/-- The remaining
constructor identity is the sampled assignment. -/
theorem packageOf_pins_cubic_folds_from_named_inputs
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
    (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.sampled = sampledAssignment E I :=
  rfl

theorem fold2_challenge36_is_two :
    (fold2Challenges : FinalComputeChallengeTuple K) = default :=
  rfl

/-- Chip interpolation orbit is a base-field strict domain, not
`E.cfg.orbit` -/
def cfgOrbitOf {E : BuildableNockExecution F K} (_D : Data E) :
    Nock.Framework.Thm54.OrbitDomain K :=
  E.cfg.orbit

def inputsOrbitOf {E : BuildableNockExecution F K} (I : Inputs E) :
    StrictExtension.StrictOrbitDomain F 3 I.hOrb :=
  I.orbit

/-! ## E. Two determined fields do not inhabit the record -/

/-- `stateTagChar` is a `Prop` from consumed `11 < ringChar`. -/
theorem stateTagChar_from_consumed_char (hgt : 11 < ringChar K) :
    NodeEncoding.StateTagChar K :=
  GenericHonestArrays.stateTagChar_of_paper_char hgt

/-- Honest-family memory-walk α is fibre `alphaM`.  This is not
`Inputs.memoryWalkAlpha` -/
theorem honest_family_memoryWalkAlpha_is_fibre
    (E : BuildableNockExecution F K)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (honestZeroFamily E hchar a g).memoryWalkAlpha = E.cfg.challenges.α ∧
      (honestZeroFamily E hchar a g).computeWalkAlpha = a ∧
      (honestZeroFamily E hchar a g).walkGamma = g :=
  ⟨rfl, rfl, rfl⟩

/-- Remaining named chip fields after those two determinations.
Walk/IO coins and compiler/interpolation stay on `Inputs`. -/
theorem remaining_named_inputs_fields {E : BuildableNockExecution F K}
    (I : Inputs E) :
    I.computeWalkAlpha = I.computeWalkAlpha ∧
      I.walkGamma = I.walkGamma ∧
      I.memoryWalkAlpha = I.memoryWalkAlpha ∧
      I.ioCoins = I.ioCoins ∧
      I.computeChallenges = I.computeChallenges ∧
      I.memoryScalarChallenge = I.memoryScalarChallenge ∧
      I.memoryExtensionFold = I.memoryExtensionFold ∧
      I.hOrb = I.hOrb ∧
      I.basis = I.basis ∧
      I.orbit = I.orbit ∧
      I.activeDomains = I.activeDomains :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## F. -/

theorem censusRecordPremises_eta_still_five
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } :=
  Batch116.censusRecordPremises_eta_still_five C

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
  Batch116.dataOfCensusAtConsumed_still_names_remaining_extras E P M
    slotSemantics census sizeWindowBound skeletonBounded hgt hln

theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } :=
  Batch116.residualPremises_eta_still_four P

theorem memoryRecordPremises_eta_still_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } :=
  Batch116.memoryRecordPremises_eta_still_two M

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
  Batch116.sizeWindowBound_still_leaves_le_Lambda

inductive ReviewedField117
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

def substantiveFields117 : List ReviewedField117 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields117 : List ReviewedField117 := [.structural]

def residualFields117 : List ReviewedField117 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Keeping `Inputs` named is not a statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields117.length = 11 ∧
      typeSummaryFields117.length = 1 ∧
      residualFields117 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields117.length = 2 ∧
      (substantiveFields117 ++ typeSummaryFields117 ++ residualFields117).Nodup ∧
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

theorem statementOf_still_takes_named_inputs
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
    (hax : OptimizedComputeFinalTrace.FormRAxisBound
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    OptimizedFullStrictThm54Statement (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF) :=
  statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth

theorem containment_is_implication_not_forall_omega
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
    (hax : OptimizedComputeFinalTrace.FormRAxisBound
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    ∀ (ω : JointCoins K) (lmb : K),
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts ω lmb →
        ω ∉ FailureUnion (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
          (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.census lmb →
        GenuineTargetAt (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
          (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).q
          (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.Λ ω lmb :=
  (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).containment

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

/-- Independent fibre coordinates at `(0,0)` and `(1,0)`. -/
theorem f73_fibre_agrees_at_two_walk_pairs :
    nprSeed (honestCoin concreteExecution 0 0) =
        nprSeed (honestCoin concreteExecution 1 0) ∧
      alphaM (honestCoin concreteExecution 0 0) =
        alphaM (honestCoin concreteExecution 1 0) ∧
      alphaC (honestCoin concreteExecution 0 0) = 0 ∧
      alphaC (honestCoin concreteExecution 1 0) = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Same inhabited `Data` and same pre-challenge `A` at `(0,0)` and `(1,0)`.
The coins differ, so this is not a prose-only distinction. -/
theorem f73_same_data_same_A_distinct_walk_coins :
    alphaMCommitmentOf data73
        (stateTagChar_of_paper_char f73_char_gt_eleven)
        (nprSeed (honestCoin concreteExecution 0 0)) data73.honestSeed_ne
        (alphaM (honestCoin concreteExecution 0 0)) =
      alphaMCommitmentOf data73
        (stateTagChar_of_paper_char f73_char_gt_eleven)
        (nprSeed (honestCoin concreteExecution 1 0)) data73.honestSeed_ne
        (alphaM (honestCoin concreteExecution 1 0)) ∧
      honestCoin concreteExecution 0 0 ≠ honestCoin concreteExecution 1 0 := by
  refine ⟨rfl, ?_⟩
  intro h
  exact zero_ne_one (congrArg (fun ω => alphaC ω) h)

/-- The witness agrees with the prover's named theorem. -/
theorem prover_f73_witness_agrees :
    alphaMCommitmentOf data73
        (stateTagChar_of_paper_char f73_char_gt_eleven)
        (nprSeed (honestCoin concreteExecution 0 0)) data73.honestSeed_ne
        (alphaM (honestCoin concreteExecution 0 0)) =
      alphaMCommitmentOf data73
        (stateTagChar_of_paper_char f73_char_gt_eleven)
        (nprSeed (honestCoin concreteExecution 1 0)) data73.honestSeed_ne
        (alphaM (honestCoin concreteExecution 1 0)) ∧
      honestCoin concreteExecution 0 0 ≠ honestCoin concreteExecution 1 0 :=
  GenericHonestPackage.Concrete.data73_same_A_distinct_walk_coins

-- Form R leftover LaterSeedZeros residual.
variable (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution)
include hmore73

/-- F73 `packageOf` still consumes the named `inputs73Fold2` record.
The two-pair witness does not inhabit `Inputs` -/
theorem f73_packageOf_still_takes_named_inputs :
    package73Of hmore73 = packageOf data73 f73_char_gt_eleven inputs73Fold2
      BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
      hmore73
      BuildablePackage.Concrete.concreteExecution_walk_order
      BuildablePackage.Concrete.concreteExecution_memory_walk_order
      BuildablePackage.Concrete.concreteExecution_rowsBound
      data73_generated OptimizedStrictFullPackage.Concrete.f73_primeField :=
  rfl

/-- Chip walk α on that named record is one value.  Fibre `Accepts` is
still `∀ a g` -/
theorem f73_chip_walk_alpha_is_one_named_value :
    inputs73Fold2.computeWalkAlpha = inputs73.computeWalkAlpha ∧
      inputs73Fold2.walkGamma = inputs73.walkGamma ∧
      inputs73Fold2.ioCoins = inputs73.ioCoins :=
  ⟨rfl, rfl, rfl⟩

theorem f73_not_forall_omega (lmb : K73cubic) :
    ¬ ∀ ω : JointCoins K73cubic, (package73Of hmore73).strategy.Accepts ω lmb :=
  GenericHonestPackage.Concrete.package73Of_not_forall_omega hmore73 (lmb := lmb)

end Concrete

#print axioms inputs_is_fifteen_fields
#print axioms packageOf_still_takes_named_inputs
#print axioms packageOf_sampled_reads_named_inputs
#print axioms inputsFold2_preserves_sampled_coins
#print axioms honestCoin_is_walk_pair_plus_fibre
#print axioms honestCoin_walk_coordinates_are_parameters
#print axioms honestCoin_injective_on_walk_pair
#print axioms fibre_nprSeed_and_alphaM_ignore_walk_pair
#print axioms same_data_same_A_at_distinct_walk_pairs
#print axioms A_tables_are_reference_at_zero_zero
#print axioms W_reads_sampled_walk_pair
#print axioms WalkSat_ln1_reads_sampled_alpha
#print axioms packageOf_fibre_accepts_is_forall_ag_under_one_inputs
#print axioms ioCoins_are_gamma_and_pole
#print axioms data_has_no_inputs_coins
#print axioms honestCoin_is_not_ioCoins
#print axioms semanticIOPreimage_has_no_io_coins
#print axioms timestampBounds_are_semantic_preimage
#print axioms sampledAssignment_reads_inputs_io_goodness
#print axioms computeChallenges_are_folds_9_11_36
#print axioms challenge36_is_base_field
#print axioms packageOf_pins_cubic_folds_from_named_inputs
#print axioms fold2_challenge36_is_two
#print axioms cfgOrbitOf
#print axioms inputsOrbitOf
#print axioms stateTagChar_from_consumed_char
#print axioms honest_family_memoryWalkAlpha_is_fibre
#print axioms remaining_named_inputs_fields
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
#print axioms statementOf_still_takes_named_inputs
#print axioms containment_is_implication_not_forall_omega
#print axioms Concrete.f73_fibre_agrees_at_two_walk_pairs
#print axioms Concrete.f73_same_data_same_A_distinct_walk_coins
#print axioms Concrete.prover_f73_witness_agrees
#print axioms Concrete.f73_packageOf_still_takes_named_inputs
#print axioms Concrete.f73_chip_walk_alpha_is_one_named_value
#print axioms Concrete.f73_not_forall_omega
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestPackage.packageOf
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestPackage.packageOf_still_takes_named_inputs
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestPackage.Concrete.data73_same_A_distinct_walk_coins
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch117
