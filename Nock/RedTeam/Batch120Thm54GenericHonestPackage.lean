import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.RedTeam.Batch119Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
import Nock.MemoryTable
import Nock.Walk
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  `executionRecords` is the pre-challenge commitment of
`E.exec.derivedRequestIO` / `derivedResponseIO`,
not the later `RAP_prog-IO` sample.  Table `(γ, β)` are
`MemoryTable.Inputs`, not FiniteIO `(gamma, pole)`.  F73 numerical
coincidence `ioCoins = ⟨0,0⟩` with table `γ = β = 0` does not identify
the objects; F73 table `α = 4` is not FiniteIO `gamma`.  The three flags
are counted event-avoidance proofs, not `True`.  No invented IO poles.
`packageOf`'s existing signature is unchanged.  Fibre `Accepts` stays
`∀ a g`.  Accounting remains `11+1+2`.  The missing later sample is not
rounded into a paper RAP or capstone failure.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch120

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

/-! ## A. IO coins/flags stay named on `packageOf` and overlays -/

/-- Fifteen-field eta still carries FiniteIO coins and the three flags. -/
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

/-- FiniteIO coins are the two-field pair `(gamma, pole)`. -/
theorem ioCoins_are_gamma_and_pole (c : FiniteIO.IOCoins K) :
    c = ⟨c.gamma, c.pole⟩ := by
  cases c
  rfl

/-- `packageOf` still consumes a named `Inputs` record. -/
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

/-- Completeness consumes the named coins and the three named flags.
`True` is not a substitute -/
theorem finiteIOStrategy_reads_named_io
    (E : BuildableNockExecution F K) (I : Inputs E) :
    (finiteIOStrategy E I).coins = I.ioCoins ∧
      (finiteIOStrategy E I).gammaGood = I.ioGammaGood ∧
      (finiteIOStrategy E I).poleGood = I.ioLogDerivGood ∧
      (sampledAssignment E I).poleHitGood = I.ioPoleHitGood :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem ao96_overlay_preserves_io {E : BuildableNockExecution F K}
    (I : Inputs E) (a g : K) :
    (inputsOfWalkSample I a g).ioCoins = I.ioCoins ∧
      (inputsOfWalkSample I a g).ioPoleHitGood = I.ioPoleHitGood ∧
      (inputsOfWalkSample I a g).ioGammaGood = I.ioGammaGood ∧
      (inputsOfWalkSample I a g).ioLogDerivGood = I.ioLogDerivGood :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Sibling fibre-α overlay copies named FiniteIO coins/flags. -/
theorem sibling_overlay_preserves_io {E : BuildableNockExecution F K}
    (I : Inputs E) :
    (inputsOfFibreAlphaM I).ioCoins = I.ioCoins ∧
      (inputsOfFibreAlphaM I).ioPoleHitGood = I.ioPoleHitGood ∧
      (inputsOfFibreAlphaM I).ioGammaGood = I.ioGammaGood ∧
      (inputsOfFibreAlphaM I).ioLogDerivGood = I.ioLogDerivGood :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem composed_overlay_preserves_io {E : BuildableNockExecution F K}
    (I : Inputs E) (a g : K) :
    (inputsOfWalkSampleWithAlphaM I a g).ioCoins = I.ioCoins ∧
      (inputsOfWalkSampleWithAlphaM I a g).ioPoleHitGood = I.ioPoleHitGood ∧
      (inputsOfWalkSampleWithAlphaM I a g).ioGammaGood = I.ioGammaGood ∧
      (inputsOfWalkSampleWithAlphaM I a g).ioLogDerivGood = I.ioLogDerivGood :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Sampled assignment of the composed overlay still reads named FiniteIO. -/
theorem sampled_of_composed_reads_named_io
    {E : BuildableNockExecution F K} (I : Inputs E) (a g : K) :
    (sampledAssignment E (inputsOfWalkSampleWithAlphaM I a g)).sampled.coins =
      I.ioCoins :=
  rfl

/-! ## B. Missing hypothesis is the later RAP sample, not `True` -/

/-- Pre-challenge IO lists sit on `E.exec`.  The `RAP_prog-IO` sample is
not among them -/
theorem executionRecords_are_pre_challenge
    (E : BuildableNockExecution F K) :
    executionRecords E =
      { requests := E.exec.derivedRequestIO
        responses := E.exec.derivedResponseIO } :=
  rfl

/-- `ExactConfig` carries table challenges, orbit, and row maps.  It has
no FiniteIO `(gamma, pole)` field -/
theorem exactConfig_has_no_ioCoins (cfg : ExactConfig F K) :
    cfg =
      { challenges := cfg.challenges
        Ksz := cfg.Ksz
        kMem := cfg.kMem
        orbit := cfg.orbit
        orbit_h_pos := cfg.orbit_h_pos
        compRows := cfg.compRows
        memRows := cfg.memRows
        compRows_pos := cfg.compRows_pos
        memRows_pos := cfg.memRows_pos
        compRows_le := cfg.compRows_le
        memRows_le := cfg.memRows_le
        eDeg := cfg.eDeg
        eDeg_eq_one := cfg.eDeg_eq_one
        compNodes := cfg.compNodes
        compNodes_spec := cfg.compNodes_spec
        memNodes := cfg.memNodes
        memNodes_spec := cfg.memNodes_spec } := by
  cases cfg
  rfl

/-- `Data` has no Inputs coins -/
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

/-- Semantic IO preimage is timestamp-bounded derived IO.  No coins. -/
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

/-- `honestCoin` is the walk pair plus fibre `(α, z)`.  No FiniteIO pole. -/
theorem honestCoin_is_walk_and_fibre
    (E : BuildableNockExecution F K) (a g : K) :
    honestCoin E a g = ((a, g), (E.cfg.challenges.α, E.cfg.challenges.z)) :=
  rfl

/-- Missing hypothesis: a later `RAP_prog-IO` sample after `Com(IO_prog)`,
plus the three counted event-avoidance proofs.  Already-held objects do
not carry that sample -/
theorem ioCoins_missing_later_rap_prog_io_sample
    {E : BuildableNockExecution F K} (I : Inputs E) (a g : K) :
    executionRecords E =
        { requests := E.exec.derivedRequestIO
          responses := E.exec.derivedResponseIO } ∧
      E.cfg.challenges.memoryInputs =
        { z := E.cfg.challenges.z
          β := E.cfg.challenges.β
          γ := E.cfg.challenges.γ } ∧
      I.ioCoins = ⟨I.ioCoins.gamma, I.ioCoins.pole⟩ ∧
      honestCoin E a g =
        ((a, g), (E.cfg.challenges.α, E.cfg.challenges.z)) ∧
      (inputsOfWalkSampleWithAlphaM I a g).ioCoins = I.ioCoins ∧
      (inputsOfWalkSampleWithAlphaM I a g).ioPoleHitGood = I.ioPoleHitGood ∧
      (inputsOfWalkSampleWithAlphaM I a g).ioGammaGood = I.ioGammaGood ∧
      (inputsOfWalkSampleWithAlphaM I a g).ioLogDerivGood = I.ioLogDerivGood ∧
      (sampledAssignment E (inputsOfWalkSampleWithAlphaM I a g)).sampled.coins =
        I.ioCoins ∧
      (finiteIOStrategy E I).gammaGood = I.ioGammaGood ∧
      (finiteIOStrategy E I).poleGood = I.ioLogDerivGood ∧
      (sampledAssignment E I).poleHitGood = I.ioPoleHitGood :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## C. Table `(γ, β)` ≠ FiniteIO `(gamma, pole)` -/

theorem challengeVector_is_seven_table_fields (v : ChallengeVector K) :
    v = ⟨v.a, v.b, v.c, v.α, v.z, v.β, v.γ, v.lam⟩ := by
  cases v
  rfl

/-- Table `(γ, β)` sit on three-field `MemoryTable.Inputs` together with `z`. -/
theorem memoryInputs_is_z_beta_gamma (v : ChallengeVector K) :
    v.memoryInputs =
      { z := v.z
        β := v.β
        γ := v.γ } :=
  rfl

/-- Memory-table LogUp pole is `RLC^γ(record) − β` -/
theorem memory_table_pole_is_recRLC_sub_beta
    (inp : MemoryTable.Inputs K) (r : Nock.ComputeTable.MemRec K) :
    MemoryTable.pole inp r = MemoryTable.recRLC inp.γ r - inp.β :=
  rfl

/-- FiniteIO compression is `pole + RLC^gamma(record)` -/
theorem finiteIO_compress_is_pole_plus_rlc
    (c : FiniteIO.IOCoins K) (v : Fin 8 → K) :
    FiniteIO.compress (m := 8) c v = c.pole + Walk.rlc c.gamma v :=
  rfl

/-! ## D. Flags are counted event-avoidance proofs, not `True` -/

/-- Named `ioPoleHitGood` inhabits event (1), not `True` -/
theorem ioPoleHitGood_is_event_avoidance
    {E : BuildableNockExecution F K} (I : Inputs E) :
    I.ioCoins.pole ∉
      FiniteIO.IOPoleHitEvent (executionRecords E) I.ioCoins.gamma :=
  I.ioPoleHitGood

/-- Named `ioGammaGood` inhabits event (2), not `True` -/
theorem ioGammaGood_is_event_avoidance
    {E : BuildableNockExecution F K} (I : Inputs E) :
    I.ioCoins.gamma ∉ FiniteIO.IORLCCollisionEvent (executionRecords E) :=
  I.ioGammaGood

/-- Named `ioLogDerivGood` inhabits event (3), not `True` -/
theorem ioLogDerivGood_is_event_avoidance
    {E : BuildableNockExecution F K} (I : Inputs E) :
    I.ioCoins.pole ∉
      FiniteIO.IOLogDerivEvent (executionRecords E) I.ioCoins.gamma :=
  I.ioLogDerivGood

/-- Strategy flags are those same named event-avoidance proofs. -/
theorem strategy_flags_are_named_events
    (E : BuildableNockExecution F K) (I : Inputs E) :
    (finiteIOStrategy E I).gammaGood =
        (I.ioGammaGood :
          I.ioCoins.gamma ∉ FiniteIO.IORLCCollisionEvent (executionRecords E)) ∧
      (finiteIOStrategy E I).poleGood =
        (I.ioLogDerivGood :
          I.ioCoins.pole ∉
            FiniteIO.IOLogDerivEvent (executionRecords E) I.ioCoins.gamma) ∧
      (sampledAssignment E I).poleHitGood =
        (I.ioPoleHitGood :
          I.ioCoins.pole ∉
            FiniteIO.IOPoleHitEvent (executionRecords E) I.ioCoins.gamma) :=
  ⟨rfl, rfl, rfl⟩

/-! ## E. Walk overlays unchanged; no invented poles; no selector -/

theorem ao96_overlay_still_only_walk_pair {E : BuildableNockExecution F K}
    (I : Inputs E) (a g : K) :
    (inputsOfWalkSample I a g).computeWalkAlpha = a ∧
      (inputsOfWalkSample I a g).walkGamma = g ∧
      (inputsOfWalkSample I a g).memoryWalkAlpha = I.memoryWalkAlpha ∧
      (inputsOfWalkSample I a g).ioCoins = I.ioCoins :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem computeChallenges_are_folds_9_11_36
    (c : FinalComputeChallengeTuple K) :
    c = ⟨c.eqA, c.eqB, c.eqC⟩ := by
  cases c
  rfl

theorem composed_preserves_cubic {E : BuildableNockExecution F K}
    (I : Inputs E) (a g : K) :
    (inputsOfWalkSampleWithAlphaM I a g).computeChallenges =
      I.computeChallenges :=
  rfl

/-- Remaining named `Inputs` fields after the IO inventory. -/
theorem remaining_named_after_io_inventory
    {E : BuildableNockExecution F K} (I : Inputs E) (a g : K) :
    (inputsOfWalkSampleWithAlphaM I a g).ioCoins = I.ioCoins ∧
      (inputsOfWalkSampleWithAlphaM I a g).computeChallenges =
        I.computeChallenges ∧
      (inputsOfWalkSampleWithAlphaM I a g).memoryScalarChallenge =
        I.memoryScalarChallenge ∧
      (inputsOfWalkSampleWithAlphaM I a g).memoryExtensionFold =
        I.memoryExtensionFold ∧
      (inputsOfWalkSampleWithAlphaM I a g).hOrb = I.hOrb ∧
      (inputsOfWalkSampleWithAlphaM I a g).basis = I.basis ∧
      (inputsOfWalkSampleWithAlphaM I a g).orbit = I.orbit ∧
      (inputsOfWalkSampleWithAlphaM I a g).activeDomains = I.activeDomains :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem packageOf_still_takes_named_inputs_after_io_inventory
    {E : BuildableNockExecution F K} (D : Data E)
    (hgt : 11 < ringChar K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hordMα : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf E.cfg.challenges.α)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (a g : K)
    (hordA : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf a) :
    packageOf D hgt I hprl hmore hord hordM hrows hgenF hF =
      buildFullPackageWith E I (commitmentResidualOfArrays_of_char D hgt)
        (computeChallenge_pins E I) hprl hmore hord hordM hrows hgenF hF ∧
      packageOfWalkSampleWithAlphaM D hgt I hprl hmore hord hordMα hrows hgenF hF a g hordA =
        packageOf D hgt (inputsOfWalkSampleWithAlphaM I a g) hprl hmore
          (fun hrows => by simpa [inputsOfWalkSampleWithAlphaM, inputsOfWalkSample,
            inputsOfFibreAlphaM] using hordA hrows)
          (fun hrows => by simpa [inputsOfWalkSampleWithAlphaM, inputsOfWalkSample,
            inputsOfFibreAlphaM] using hordMα hrows) hrows hgenF hF :=
  ⟨rfl, rfl⟩

theorem censusRecordPremises_eta_still_five
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } :=
  Batch119.censusRecordPremises_eta_still_five C

theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } :=
  Batch119.residualPremises_eta_still_four P

theorem memoryRecordPremises_eta_still_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } :=
  Batch119.memoryRecordPremises_eta_still_two M

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
  Batch119.dataOfCensusAtConsumed_still_names_remaining_extras E P M
    slotSemantics census sizeWindowBound skeletonBounded hgt hln

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

/-! ## F. Wrong layer: NMR / capstone not re-litigated -/

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
  Batch119.sizeWindowBound_still_leaves_le_Lambda

inductive ReviewedField120
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

def substantiveFields120 : List ReviewedField120 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields120 : List ReviewedField120 := [.structural]

def residualFields120 : List ReviewedField120 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Named FiniteIO is not a statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields120.length = 11 ∧
      typeSummaryFields120.length = 1 ∧
      residualFields120 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields120.length = 2 ∧
      (substantiveFields120 ++ typeSummaryFields120 ++ residualFields120).Nodup ∧
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

/-! ## G. `∀ a g` preserved -/

theorem overlay_fibre_accepts_still_forall_ag
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf E.cfg.challenges.α)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (horder : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α) :
    ∀ (a g : K)
      (hordA : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf a),
      (packageOfWalkSampleWithAlphaM D hgt I hprl hmore hord hordM hrows hgenF hF a g hordA).strategy.Accepts
        (honestCoin E a g) E.cfg.challenges.lam :=
  packageOfWalkSampleWithAlphaM_fibre_accepts D hgt I hprl hmore hord hordM hrows hgenF hF horder

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

/-! ## H. F73 coincidence is not identification -/

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

/-- F73 FiniteIO coins are the named Inputs field `⟨0, 0⟩`.  Table
`ChallengeVector.γ`/`β` are also `0`.  That numerical coincidence does
not identify FiniteIO with `MemoryTable.Inputs` -/
theorem f73_numerical_coincidence :
    inputs73Fold2.ioCoins = ⟨(0 : K73cubic), 0⟩ ∧
      concreteExecution.cfg.challenges.γ = 0 ∧
      concreteExecution.cfg.challenges.β = 0 ∧
      concreteExecution.cfg.challenges.memoryInputs =
        { z := concreteExecution.cfg.challenges.z
          β := (0 : K73cubic)
          γ := 0 } ∧
      inputs73Fold2.ioCoins =
        ⟨concreteExecution.cfg.challenges.γ,
          concreteExecution.cfg.challenges.β⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Paper RAP_prog-IO letter `α` is not table `ChallengeVector.α`.
F73 table `α = 4` is not FiniteIO `gamma = 0` -/
theorem f73_table_alpha_ne_io_gamma :
    concreteExecution.cfg.challenges.α ≠ inputs73Fold2.ioCoins.gamma ∧
      concreteExecution.cfg.challenges.α = (4 : K73cubic) ∧
      inputs73Fold2.ioCoins.gamma = 0 := by
  refine ⟨?hne, rfl, rfl⟩
  intro h
  have h4 : (4 : K73cubic) ≠ 0 := by
    intro h0
    have hbase : (4 : F73) ≠ 0 := by decide
    exact hbase ((algebraMap F73 K73cubic).injective
      (by simpa [map_ofNat, map_zero] using h0))
  exact h4 h

/-- Memory-table `Inputs` still carries the NPR seed `z`; FiniteIO does not.
The F73 zero coincidence therefore does not collapse the objects. -/
theorem f73_memoryInputs_still_carries_z :
    concreteExecution.cfg.challenges.memoryInputs.z =
        concreteExecution.cfg.challenges.z ∧
      inputs73Fold2.ioCoins = ⟨(0 : K73cubic), 0⟩ :=
  ⟨rfl, rfl⟩

/-- Composed overlay still reads the named F73 coins -/
theorem f73_composed_still_reads_named_io :
    (inputs73WalkWithAlphaM 0 0).ioCoins = inputs73Fold2.ioCoins ∧
      (sampledAssignment concreteExecution
          (inputs73WalkWithAlphaM 0 0)).sampled.coins =
        inputs73Fold2.ioCoins ∧
      (inputs73WalkWithAlphaM 0 0).computeChallenges =
        inputs73Fold2.computeChallenges :=
  ⟨rfl, rfl, rfl⟩

/-- Named F73 flags inhabit the three counted events, not `True`. -/
theorem f73_flags_are_event_avoidance :
    inputs73Fold2.ioCoins.pole ∉
        FiniteIO.IOPoleHitEvent (executionRecords concreteExecution)
          inputs73Fold2.ioCoins.gamma ∧
      inputs73Fold2.ioCoins.gamma ∉
        FiniteIO.IORLCCollisionEvent (executionRecords concreteExecution) ∧
      inputs73Fold2.ioCoins.pole ∉
        FiniteIO.IOLogDerivEvent (executionRecords concreteExecution)
          inputs73Fold2.ioCoins.gamma :=
  ⟨inputs73Fold2.ioPoleHitGood, inputs73Fold2.ioGammaGood,
    inputs73Fold2.ioLogDerivGood⟩

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

theorem f73_not_forall_omega (lmb : K73cubic) :
    ¬ ∀ ω : JointCoins K73cubic, (package73Of hmore73).strategy.Accepts ω lmb :=
  GenericHonestPackage.Concrete.package73Of_not_forall_omega hmore73 (lmb := lmb)

end Concrete

#print axioms inputs_is_fifteen_fields
#print axioms ioCoins_are_gamma_and_pole
#print axioms packageOf_signature_unchanged
#print axioms finiteIOStrategy_reads_named_io
#print axioms ao96_overlay_preserves_io
#print axioms sibling_overlay_preserves_io
#print axioms composed_overlay_preserves_io
#print axioms sampled_of_composed_reads_named_io
#print axioms executionRecords_are_pre_challenge
#print axioms exactConfig_has_no_ioCoins
#print axioms data_has_no_inputs_coins
#print axioms semanticIOPreimage_has_no_io_coins
#print axioms honestCoin_is_walk_and_fibre
#print axioms ioCoins_missing_later_rap_prog_io_sample
#print axioms challengeVector_is_seven_table_fields
#print axioms memoryInputs_is_z_beta_gamma
#print axioms memory_table_pole_is_recRLC_sub_beta
#print axioms finiteIO_compress_is_pole_plus_rlc
#print axioms ioPoleHitGood_is_event_avoidance
#print axioms ioGammaGood_is_event_avoidance
#print axioms ioLogDerivGood_is_event_avoidance
#print axioms strategy_flags_are_named_events
#print axioms ao96_overlay_still_only_walk_pair
#print axioms computeChallenges_are_folds_9_11_36
#print axioms composed_preserves_cubic
#print axioms remaining_named_after_io_inventory
#print axioms packageOf_still_takes_named_inputs_after_io_inventory
#print axioms censusRecordPremises_eta_still_five
#print axioms residualPremises_eta_still_four
#print axioms memoryRecordPremises_eta_still_two
#print axioms dataOfCensusAtConsumed_still_names_remaining_extras
#print axioms packageOf_not_forall_omega
#print axioms released_builder_still_takes_hzero
#print axioms nmr_axis_is_not_inputs_sample
#print axioms sizeWindowBound_still_leaves_le_Lambda
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms overlay_fibre_accepts_still_forall_ag
#print axioms packageOf_fibre_accepts_still_forall_ag
#print axioms Concrete.f73_numerical_coincidence
#print axioms Concrete.f73_table_alpha_ne_io_gamma
#print axioms Concrete.f73_memoryInputs_still_carries_z
#print axioms Concrete.f73_composed_still_reads_named_io
#print axioms Concrete.f73_flags_are_event_avoidance
#print axioms Concrete.f73_packageOf_signature_unchanged
#print axioms Concrete.f73_not_forall_omega

end
end Nock.RedTeam.Batch120
