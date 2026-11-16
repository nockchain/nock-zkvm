import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.RedTeam.Batch118Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  Sibling overlay `inputsOfFibreAlphaM` sets chip
`memoryWalkAlpha` from fibre `alphaM` / `E.cfg.challenges.α` /
`honestCoin`'s `(α, z)`.  That field equals
`honestZeroFamily.memoryWalkAlpha` and equals `atJointCoins` at
`honestCoin` on the memory-walk coordinate.  The sibling overlay does
not fill `computeWalkAlpha` / `walkGamma`; those stay the caller's named
fields.  `packageOf`'s existing signature is unchanged; fibre `Accepts` stays
`∀ a g`.  FiniteIO `(gamma, pole)` plus goodness flags stay named.
Compiler folds `9`/`11`/`36` are unchanged.  Remaining `Inputs` fields
stay named.  Accounting remains `11+1+2`.  The overlay is not rounded into a
paper RAP or capstone failure.  Identity with `atJointCoins` is the
three chip walk coins on the composed overlay, not a silent inhabit of
the whole `Inputs` record or of IO endpoints.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch119

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

/-! ## A. Overlay is 1-1 with fibre `alphaM` -/

/-- Sibling overlay writes chip memory-walk α from the execution table
timestamp -/
theorem overlay_sets_memoryWalkAlpha_from_fibre
    {E : BuildableNockExecution F K} (I : Inputs E) :
    (inputsOfFibreAlphaM I).memoryWalkAlpha = E.cfg.challenges.α :=
  rfl

/-- That coordinate is `alphaM` of `honestCoin`, and `honestCoin` is
`((a, g), (α, z))` -/
theorem overlay_eq_alphaM_and_honestCoin
    {E : BuildableNockExecution F K} (I : Inputs E) (a g : K) :
    (inputsOfFibreAlphaM I).memoryWalkAlpha = alphaM (honestCoin E a g) ∧
      honestCoin E a g = ((a, g), (E.cfg.challenges.α, E.cfg.challenges.z)) ∧
      alphaM (honestCoin E a g) = E.cfg.challenges.α :=
  ⟨rfl, rfl, rfl⟩

/-- Same object as honest-family memory-walk α -/
theorem overlay_eq_honestZeroFamily
    {E : BuildableNockExecution F K} (I : Inputs E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (inputsOfFibreAlphaM I).memoryWalkAlpha =
      (honestZeroFamily E hchar a g).memoryWalkAlpha :=
  rfl

/-- `atJointCoins` at `honestCoin` reads the same memory-walk coordinate.
Not a claim that the whole family or the whole `Inputs` record matches. -/
theorem overlay_eq_atJointCoins_memoryWalkAlpha
    {E : BuildableNockExecution F K} (I : Inputs E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    let R := (honestZeroFamily E hchar 0 0).atJointCoins (honestCoin E a g)
    (inputsOfFibreAlphaM I).memoryWalkAlpha = R.memoryWalkAlpha ∧
      R.memoryWalkAlpha = alphaM (honestCoin E a g) :=
  ⟨rfl, rfl⟩

/-- Chip family consumes the overlaid fibre α, not a different object.
Sibling overlay leaves later-round walk coins named -/
theorem family_reads_overlay_alphaM {E : BuildableNockExecution F K}
    (I : Inputs E) :
    (zeroEndpointFamily E (inputsOfFibreAlphaM I)).memoryWalkAlpha =
        E.cfg.challenges.α ∧
      (zeroEndpointFamily E (inputsOfFibreAlphaM I)).computeWalkAlpha =
        I.computeWalkAlpha ∧
      (zeroEndpointFamily E (inputsOfFibreAlphaM I)).walkGamma =
        I.walkGamma :=
  ⟨rfl, rfl, rfl⟩

/-- Fibre `alphaM` is the same at every later-round pair.  Not a unique pair. -/
theorem overlay_ignores_walk_pair {E : BuildableNockExecution F K}
    (I : Inputs E) (a g a' g' : K) :
    (inputsOfFibreAlphaM I).memoryWalkAlpha = alphaM (honestCoin E a g) ∧
      alphaM (honestCoin E a g) = alphaM (honestCoin E a' g') :=
  ⟨rfl, rfl⟩

/-- Sibling overlay is not a silent `atJointCoins` inhabit: it does not
write `computeWalkAlpha` / `walkGamma` -/
theorem sibling_overlay_does_not_fill_compute_walk
    {E : BuildableNockExecution F K} (I : Inputs E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (inputsOfFibreAlphaM I).computeWalkAlpha = I.computeWalkAlpha ∧
      (inputsOfFibreAlphaM I).walkGamma = I.walkGamma ∧
      ((honestZeroFamily E hchar 0 0).atJointCoins (honestCoin E a g)).computeWalkAlpha =
        a ∧
      ((honestZeroFamily E hchar 0 0).atJointCoins (honestCoin E a g)).walkGamma =
        g :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## B. -/

theorem ao96_overlay_still_only_walk_pair
    {E : BuildableNockExecution F K} (I : Inputs E) (a g : K) :
    (inputsOfWalkSample I a g).computeWalkAlpha = a ∧
      (inputsOfWalkSample I a g).walkGamma = g ∧
      (inputsOfWalkSample I a g).memoryWalkAlpha = I.memoryWalkAlpha :=
  ⟨rfl, rfl, rfl⟩

theorem composition_is_additive {E : BuildableNockExecution F K}
    (I : Inputs E) (a g : K) :
    inputsOfWalkSampleWithAlphaM I a g =
      inputsOfFibreAlphaM (inputsOfWalkSample I a g) :=
  rfl

theorem fibre_alphaM_commutes_with_ao96 {E : BuildableNockExecution F K}
    (I : Inputs E) (a g : K) :
    inputsOfFibreAlphaM (inputsOfWalkSample I a g) =
      inputsOfWalkSample (inputsOfFibreAlphaM I) a g :=
  rfl

/-- Composed overlay's three chip walk coins match `atJointCoins` at
`honestCoin`.  Remaining `Inputs` fields are not that identity. -/
theorem composed_three_coins_eq_atJointCoins
    {E : BuildableNockExecution F K} (I : Inputs E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    let R := (honestZeroFamily E hchar 0 0).atJointCoins (honestCoin E a g)
    (inputsOfWalkSampleWithAlphaM I a g).computeWalkAlpha = R.computeWalkAlpha ∧
      (inputsOfWalkSampleWithAlphaM I a g).walkGamma = R.walkGamma ∧
      (inputsOfWalkSampleWithAlphaM I a g).memoryWalkAlpha = R.memoryWalkAlpha ∧
      (inputsOfWalkSampleWithAlphaM I a g).computeWalkAlpha =
        alphaC (honestCoin E a g) ∧
      (inputsOfWalkSampleWithAlphaM I a g).walkGamma =
        gamma (honestCoin E a g) ∧
      (inputsOfWalkSampleWithAlphaM I a g).memoryWalkAlpha =
        alphaM (honestCoin E a g) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Distinct later-round pairs remain distinct after the composed overlay. -/
theorem composed_injective_on_walk_pair {E : BuildableNockExecution F K}
    (I : Inputs E) {a g a' g' : K}
    (h : inputsOfWalkSampleWithAlphaM I a g =
      inputsOfWalkSampleWithAlphaM I a' g') :
    a = a' ∧ g = g' :=
  ⟨congrArg Inputs.computeWalkAlpha h, congrArg Inputs.walkGamma h⟩

/-! ## C. `packageOf` signature unchanged; `∀ a g` preserved -/

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

theorem packageOfFibreAlphaM_is_packageOf_at_overlay
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
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    packageOfFibreAlphaM D hgt I hprl hmore hord hordM hrows hgenF hF =
      packageOf D hgt (inputsOfFibreAlphaM I) hprl hmore
        (fun hrows => by simpa [inputsOfFibreAlphaM] using hord hrows)
        (fun hrows => by simpa [inputsOfFibreAlphaM] using hordM hrows) hrows :=
  rfl

theorem packageOfWalkSampleWithAlphaM_is_packageOf_at_composed
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
    (a g : K)
    (hordA : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf a) :
    packageOfWalkSampleWithAlphaM D hgt I hprl hmore hord hordM hrows hgenF hF a g hordA =
      packageOf D hgt (inputsOfWalkSampleWithAlphaM I a g) hprl hmore
        (fun hrows => by simpa [inputsOfWalkSampleWithAlphaM, inputsOfWalkSample,
          inputsOfFibreAlphaM] using hordA hrows)
        (fun hrows => by simpa [inputsOfWalkSampleWithAlphaM, inputsOfWalkSample,
          inputsOfFibreAlphaM] using hordM hrows) hrows :=
  rfl

theorem packageOfWalkSample_still_ao96
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

theorem overlay_accepts_ignores_chip_walk_pair
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
    ∀ (a g a' g' : K)
      (hordA : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf a),
      (packageOfWalkSampleWithAlphaM D hgt I hprl hmore hord hordM hrows hgenF hF a g hordA).strategy.Accepts
        (honestCoin E a' g') E.cfg.challenges.lam :=
  packageOfWalkSampleWithAlphaM_fibre_accepts_still_forall_ag D hgt I hprl hmore hord hordM hrows hgenF hF
    horder

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

/-! ## D. IO still named; compiler folds not invented -/

theorem challengeVector_is_seven_table_fields (v : ChallengeVector K) :
    v = ⟨v.a, v.b, v.c, v.α, v.z, v.β, v.γ, v.lam⟩ := by
  cases v
  rfl

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

theorem honestCoin_is_not_ioCoins
    (E : BuildableNockExecution F K) (a g : K) :
    honestCoin E a g =
      ((alphaC (honestCoin E a g), gamma (honestCoin E a g)),
        (alphaM (honestCoin E a g), nprSeed (honestCoin E a g))) :=
  rfl

theorem ioCoins_are_gamma_and_pole (c : FiniteIO.IOCoins K) :
    c = ⟨c.gamma, c.pole⟩ := by
  cases c
  rfl

theorem overlay_preserves_io {E : BuildableNockExecution F K}
    (I : Inputs E) :
    (inputsOfFibreAlphaM I).ioCoins = I.ioCoins ∧
      (inputsOfFibreAlphaM I).ioPoleHitGood = I.ioPoleHitGood ∧
      (inputsOfFibreAlphaM I).ioGammaGood = I.ioGammaGood ∧
      (inputsOfFibreAlphaM I).ioLogDerivGood = I.ioLogDerivGood :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem sampled_of_overlay_reads_named_io
    {E : BuildableNockExecution F K} (I : Inputs E) :
    (sampledAssignment E (inputsOfFibreAlphaM I)).sampled.coins = I.ioCoins :=
  rfl

theorem composed_preserves_io {E : BuildableNockExecution F K}
    (I : Inputs E) (a g : K) :
    (inputsOfWalkSampleWithAlphaM I a g).ioCoins = I.ioCoins ∧
      (inputsOfWalkSampleWithAlphaM I a g).ioPoleHitGood = I.ioPoleHitGood ∧
      (inputsOfWalkSampleWithAlphaM I a g).ioGammaGood = I.ioGammaGood ∧
      (inputsOfWalkSampleWithAlphaM I a g).ioLogDerivGood = I.ioLogDerivGood :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem computeChallenges_are_folds_9_11_36
    (c : FinalComputeChallengeTuple K) :
    c = ⟨c.eqA, c.eqB, c.eqC⟩ := by
  cases c
  rfl

theorem overlay_preserves_cubic {E : BuildableNockExecution F K}
    (I : Inputs E) :
    (inputsOfFibreAlphaM I).computeChallenges = I.computeChallenges ∧
      (inputsOfFibreAlphaM I).computeChallenges =
        I.computeChallenges :=
  ⟨rfl, rfl⟩

theorem challenge36_is_base_field (c : FinalComputeChallengeTuple K) :
    c = ⟨c.eqA, c.eqB, c.eqC⟩ := by
  cases c; rfl

theorem fold2_and_fibre_alphaM_commute {E : BuildableNockExecution F K}
    (I : Inputs E) :
    inputsOfFibreAlphaM (inputsFold2 I) = inputsFold2 (inputsOfFibreAlphaM I) :=
  rfl

/-! ## E. Not a silent inhabit of the whole `Inputs` record -/

theorem overlay_preserves_named_remainder {E : BuildableNockExecution F K}
    (I : Inputs E) :
    (inputsOfFibreAlphaM I).stateTagChar = I.stateTagChar ∧
      (inputsOfFibreAlphaM I).computeWalkAlpha = I.computeWalkAlpha ∧
      (inputsOfFibreAlphaM I).walkGamma = I.walkGamma ∧
      (inputsOfFibreAlphaM I).hOrb = I.hOrb ∧
      (inputsOfFibreAlphaM I).basis = I.basis ∧
      (inputsOfFibreAlphaM I).orbit = I.orbit ∧
      (inputsOfFibreAlphaM I).activeDomains = I.activeDomains ∧
      (inputsOfFibreAlphaM I).ioCoins = I.ioCoins ∧
      (inputsOfFibreAlphaM I).computeChallenges = I.computeChallenges ∧
      (inputsOfFibreAlphaM I).memoryScalarChallenge =
        I.memoryScalarChallenge ∧
      (inputsOfFibreAlphaM I).memoryExtensionFold = I.memoryExtensionFold :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem composed_preserves_named_remainder {E : BuildableNockExecution F K}
    (I : Inputs E) (a g : K) :
    (inputsOfWalkSampleWithAlphaM I a g).stateTagChar = I.stateTagChar ∧
      (inputsOfWalkSampleWithAlphaM I a g).hOrb = I.hOrb ∧
      (inputsOfWalkSampleWithAlphaM I a g).basis = I.basis ∧
      (inputsOfWalkSampleWithAlphaM I a g).orbit = I.orbit ∧
      (inputsOfWalkSampleWithAlphaM I a g).activeDomains = I.activeDomains ∧
      (inputsOfWalkSampleWithAlphaM I a g).ioCoins = I.ioCoins ∧
      (inputsOfWalkSampleWithAlphaM I a g).computeChallenges =
        I.computeChallenges ∧
      (inputsOfWalkSampleWithAlphaM I a g).memoryScalarChallenge =
        I.memoryScalarChallenge ∧
      (inputsOfWalkSampleWithAlphaM I a g).memoryExtensionFold =
        I.memoryExtensionFold :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem censusRecordPremises_eta_still_five
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } :=
  Batch118.censusRecordPremises_eta_still_five C

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
  Batch118.dataOfCensusAtConsumed_still_names_remaining_extras E P M
    slotSemantics census sizeWindowBound skeletonBounded hgt hln

theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } :=
  Batch118.residualPremises_eta_still_four P

theorem memoryRecordPremises_eta_still_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } :=
  Batch118.memoryRecordPremises_eta_still_two M

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
  Batch118.sizeWindowBound_still_leaves_le_Lambda

inductive ReviewedField119
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

def substantiveFields119 : List ReviewedField119 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields119 : List ReviewedField119 := [.structural]

def residualFields119 : List ReviewedField119 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- The fibre-α overlay is not a statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields119.length = 11 ∧
      typeSummaryFields119.length = 1 ∧
      residualFields119 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields119.length = 2 ∧
      (substantiveFields119 ++ typeSummaryFields119 ++ residualFields119).Nodup ∧
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

theorem statementOfWalkSampleWithAlphaM_still_takes_named_inputs
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
    (a g : K)
    (hordA : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf a)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound
      (packageOfWalkSampleWithAlphaM D hgt I hprl hmore hord hordM hrows hgenF hF a g hordA).optimized.sampled
      (packageOfWalkSampleWithAlphaM D hgt I hprl hmore hord hordM hrows hgenF hF a g hordA).optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis
      (packageOfWalkSampleWithAlphaM D hgt I hprl hmore hord hordM hrows hgenF hF a g hordA).optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement
      (packageOfWalkSampleWithAlphaM D hgt I hprl hmore hord hordM hrows hgenF hF a g hordA) :=
  statementOfWalkSampleWithAlphaM D hgt I hprl hmore hord hordM hrows hgenF hF a g hordA hax hbasis hwidth

/-! ## F. F73 non-vacuity: fibre αm is table α = 4, not table γ, not later-round αc -/

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

/-- F73 fibre memory-walk α is table `α = 4`, equal at `(0,0)` and `(1,0)`. -/
theorem f73_fibre_alphaM_is_four :
    (inputsOfFibreAlphaM inputs73Fold2).memoryWalkAlpha =
        concreteExecution.cfg.challenges.α ∧
      (inputsOfFibreAlphaM inputs73Fold2).memoryWalkAlpha =
        alphaM (honestCoin concreteExecution 0 0) ∧
      (inputsOfFibreAlphaM inputs73Fold2).memoryWalkAlpha =
        alphaM (honestCoin concreteExecution 1 0) ∧
      (inputsOfFibreAlphaM inputs73Fold2).memoryWalkAlpha = (4 : K73cubic) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- F73 fibre `alphaM` is not table `ChallengeVector.γ` -/
theorem f73_fibre_alphaM_ne_table_gamma :
    (inputsOfFibreAlphaM inputs73Fold2).memoryWalkAlpha ≠
        concreteExecution.cfg.challenges.γ ∧
      concreteExecution.cfg.challenges.γ = 0 := by
  refine ⟨?hne, rfl⟩
  intro h
  have h4 : (4 : K73cubic) ≠ 0 := by
    intro h0
    have hbase : (4 : F73) ≠ 0 := by decide
    exact hbase ((algebraMap F73 K73cubic).injective
      (by simpa [map_ofNat, map_zero] using h0))
  exact h4 h

theorem f73_ao96_still_preserves_memoryWalkAlpha (a g : K73cubic) :
    (inputs73Walk a g).memoryWalkAlpha = inputs73Fold2.memoryWalkAlpha :=
  rfl

/-- Composed overlay shares fibre αm at `(0,0)` versus `(1,0)` and differs
on chip walk α.  Not a unique pair -/
theorem f73_composed_same_alphaM_distinct_alphaC :
    (inputs73WalkWithAlphaM 0 0).memoryWalkAlpha =
        (inputs73WalkWithAlphaM 1 0).memoryWalkAlpha ∧
      (inputs73WalkWithAlphaM 0 0).computeWalkAlpha ≠
        (inputs73WalkWithAlphaM 1 0).computeWalkAlpha ∧
      (inputs73WalkWithAlphaM 0 0).computeWalkAlpha ≠
        (inputs73WalkWithAlphaM 0 0).memoryWalkAlpha ∧
      (inputs73WalkWithAlphaM 0 0).ioCoins = inputs73Fold2.ioCoins ∧
      (inputs73WalkWithAlphaM 0 0).computeChallenges =
        inputs73Fold2.computeChallenges := by
  refine ⟨rfl, ?hneC, ?hneM, rfl, rfl⟩
  · intro h
    exact zero_ne_one h
  · intro h
    have h4 : (4 : K73cubic) ≠ 0 := by
      intro h0
      have hbase : (4 : F73) ≠ 0 := by decide
      exact hbase ((algebraMap F73 K73cubic).injective
        (by simpa [map_ofNat, map_zero] using h0))
    exact h4 h.symm

/-- Sibling overlay does not inhabit FiniteIO coins or compiler folds. -/
theorem f73_sibling_preserves_io_and_folds :
    (inputsOfFibreAlphaM inputs73Fold2).ioCoins = inputs73Fold2.ioCoins ∧
      (inputsOfFibreAlphaM inputs73Fold2).computeChallenges =
        inputs73Fold2.computeChallenges ∧
      (inputsOfFibreAlphaM inputs73Fold2).computeWalkAlpha =
        inputs73Fold2.computeWalkAlpha ∧
      (inputsOfFibreAlphaM inputs73Fold2).walkGamma =
        inputs73Fold2.walkGamma :=
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

theorem f73_composed_package_is_additive (a g : K73cubic) :
    package73OfWalkWithAlphaM hmore73 a g =
      packageOf data73 f73_char_gt_eleven (inputs73WalkWithAlphaM a g)
        BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
        hmore73
        (f73_walkOrderA a)
        BuildablePackage.Concrete.concreteExecution_alpha_memory_walk_order
    BuildablePackage.Concrete.concreteExecution_rowsBound
    data73_generated OptimizedStrictFullPackage.Concrete.f73_primeField :=
  rfl

theorem f73_not_forall_omega (lmb : K73cubic) :
    ¬ ∀ ω : JointCoins K73cubic, (package73Of hmore73).strategy.Accepts ω lmb :=
  GenericHonestPackage.Concrete.package73Of_not_forall_omega hmore73 (lmb := lmb)

end Concrete

#print axioms overlay_sets_memoryWalkAlpha_from_fibre
#print axioms overlay_eq_alphaM_and_honestCoin
#print axioms overlay_eq_honestZeroFamily
#print axioms overlay_eq_atJointCoins_memoryWalkAlpha
#print axioms family_reads_overlay_alphaM
#print axioms overlay_ignores_walk_pair
#print axioms sibling_overlay_does_not_fill_compute_walk
#print axioms ao96_overlay_still_only_walk_pair
#print axioms composition_is_additive
#print axioms fibre_alphaM_commutes_with_ao96
#print axioms composed_three_coins_eq_atJointCoins
#print axioms composed_injective_on_walk_pair
#print axioms inputs_is_fifteen_fields
#print axioms packageOf_signature_unchanged
#print axioms packageOfFibreAlphaM_is_packageOf_at_overlay
#print axioms packageOfWalkSampleWithAlphaM_is_packageOf_at_composed
#print axioms packageOfWalkSample_still_ao96
#print axioms overlay_fibre_accepts_still_forall_ag
#print axioms overlay_accepts_ignores_chip_walk_pair
#print axioms packageOf_fibre_accepts_still_forall_ag
#print axioms challengeVector_is_seven_table_fields
#print axioms semanticIOPreimage_has_no_io_coins
#print axioms honestCoin_is_not_ioCoins
#print axioms ioCoins_are_gamma_and_pole
#print axioms overlay_preserves_io
#print axioms sampled_of_overlay_reads_named_io
#print axioms composed_preserves_io
#print axioms computeChallenges_are_folds_9_11_36
#print axioms overlay_preserves_cubic
#print axioms challenge36_is_base_field
#print axioms fold2_and_fibre_alphaM_commute
#print axioms overlay_preserves_named_remainder
#print axioms composed_preserves_named_remainder
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
#print axioms statementOfWalkSampleWithAlphaM_still_takes_named_inputs
#print axioms Concrete.f73_fibre_alphaM_is_four
#print axioms Concrete.f73_fibre_alphaM_ne_table_gamma
#print axioms Concrete.f73_ao96_still_preserves_memoryWalkAlpha
#print axioms Concrete.f73_composed_same_alphaM_distinct_alphaC
#print axioms Concrete.f73_sibling_preserves_io_and_folds
#print axioms Concrete.f73_packageOf_signature_unchanged
#print axioms Concrete.f73_composed_package_is_additive
#print axioms Concrete.f73_not_forall_omega

end
end Nock.RedTeam.Batch119
