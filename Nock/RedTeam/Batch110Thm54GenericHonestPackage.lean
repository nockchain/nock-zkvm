import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.RedTeam.Batch109Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  Both structural Booleans on the `packageOf` committed
template at honest `alphaM` inhabit from specialized
`ExactAxisStructuralRefinement` plus the named uniqueness window
`ForestExponentOrder`: every committed-forest read
and verify exponent lies below `orderOf alphaM`.  Production
`strategy.Accepts` on the fibre is then `∀ a g`.  That predicate is
production `ProductionStrategy.Accepts`, not residual verifier `Accepts`.
Read-exponent
uniqueness takes no extra.  Axis-structure modules are additive: existing
forward lemmas keep their types.  Not `∀ ω`.  Accounting remains `11+1+2`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch110

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
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
open Nock.NockVMROM.Thm54.ProductionRawVerifier
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.Framework

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## A. Production `Accepts` is production, not residual verifier `Accepts` -/

/-- Package `strategy.Accepts` is production `Accepts` -/
theorem package_strategy_accepts_is_production
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
    (ω : JointCoins K) (lmb : K) :
    (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts ω lmb =
      ProductionStrategy.Accepts (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy ω lmb :=
  rfl

/-- Residual verifier `Accepts` is the template-adapter predicate, a strictly
smaller object -/
theorem residual_accepts_is_template_adapter
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (ω : JointCoins K) (lmb : K) :
    (commitmentResidualOfArrays_of_char D hgt).verifier.Accepts ω lmb =
      TemplateAdapter.Strategy.Accepts
        (commitmentResidualOfArrays_of_char D hgt).verifier ω lmb :=
  rfl

theorem committed_template_is_data_template
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
    (hF : GeneratedField.PrimeFieldElems F) :
    committedTemplate (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier
      E.cfg.challenges.z D.honestSeed_ne =
      D.executionTemplate E.cfg.challenges.z :=
  rfl

/-- Independent reconstruction of the fibre iff: production `Accepts` at
`honestCoin` is exactly `structuralChecksAt = true`.  Not `∀ ω`. -/
theorem fibre_accepts_iff_structural_independently
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
    (a g : K) :
    (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts (honestCoin E a g) E.cfg.challenges.lam ↔
      structuralChecksAt (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier
        (nprSeed (honestCoin E a g)) D.honestSeed_ne
        (alphaM (honestCoin E a g)) = true :=
  GenericHonestPackage.packageOf_fibre_accepts_iff_structural D hgt I hprl hmore hord hordM hrows hgenF hF a g

theorem structuralChecksAt_splits_independently
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
    (hF : GeneratedField.PrimeFieldElems F) :
    structuralChecksAt (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier
      E.cfg.challenges.z D.honestSeed_ne E.cfg.challenges.α =
      (alphaFreeAxisStructureCheck
        (committedTemplate (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier
          E.cfg.challenges.z D.honestSeed_ne) &&
        noWrapCheck
          (committedTemplate (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier
            E.cfg.challenges.z D.honestSeed_ne)
          E.cfg.challenges.α) :=
  rfl

/-! ## B. `ForestExponentOrder` is a real extra, not `True`, not from `E` -/

/-- The named uniqueness window expands to two boundedness statements, not
`True` -/
theorem ForestExponentOrder_expands
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) :
    ForestExponentOrder E α =
      ((∀ i e, e ∈ readExps (alphaFreeRoot E i) → e < orderOf α) ∧
        (∀ i e, e ∈ verifyExps (alphaFreeRoot E i) → e < orderOf α)) :=
  rfl

/-- `noWrapCheck` is only the read half.  The verify half of the window is
not this Boolean -/
theorem noWrapCheck_is_read_half
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) :
    noWrapCheck E α = true ↔
      ∀ i e, e ∈ readExps (alphaFreeRoot E i) → e < orderOf α :=
  noWrapCheck_eq_true_iff E α

/-- The uniqueness window is a property of the committed template and honest
`alphaM`, not of later-round `(a, g)` -/
theorem ForestExponentOrder_ignores_later_round
    {E : BuildableNockExecution F K} (D : Data E) (a g : K) :
    ForestExponentOrder
        (D.executionTemplate (nprSeed (honestCoin E a g)))
        (alphaM (honestCoin E a g)) =
      ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
        E.cfg.challenges.α :=
  ForestExponentOrder_of_honestCoin D a g

/-- `Data` still does not carry an exponent-order field.  The fifteen-field
`Inputs` record is unchanged -/
theorem inputs_eta_still_named {E : BuildableNockExecution F K} (I : Inputs E) :
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

/-- `E` already supplies a global semantic-IO timestamp preimage.  That object
bounds derived-IO record Nats on specialized `cfg`/`exec`, not α-free template
tree exponents. -/
theorem timestampBounds_are_semantic_preimage
    (E : BuildableNockExecution F K) :
    Nonempty (SemanticIOPreimage E.cfg E.exec) :=
  E.timestampBounds

theorem semantic_preimage_bounds_derived_io_nats
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticIOPreimage cfg exec) :
    (∀ r ∈ w.semanticRequests, r.2.2 < orderOf cfg.challenges.α) ∧
      (∀ r ∈ w.semanticResponses, r.2.2 < orderOf cfg.challenges.α) :=
  ⟨w.requestTimestamp_lt_order, w.responseTimestamp_lt_order⟩

/-- Specialized structural refinement is already on `E.memoryTrace`.  That is
not `ForestExponentOrder` and not the α-free Boolean -/
theorem specialized_structural_already_on_execution
    (E : BuildableNockExecution F K) :
    ExactAxisStructuralRefinement E.cfg E.execA :=
  E.memoryTrace.axisStructural

theorem packageOf_specialized_structural_independently
    {E : BuildableNockExecution F K} (D : Data E) :
    ExactAxisStructuralRefinement
      ((configTemplateOf E E.cfg.challenges.z).specialize E.cfg.challenges.α E.cfg.challenges.lam)
      ((D.executionTemplate E.cfg.challenges.z).specializeA E.cfg.challenges.α E.cfg.challenges.lam) :=
  GenericHonestPackage.packageOf_specialized_structural D

/-! ## C. Both Booleans inhabited from the window; nodup takes no extra -/

/-- Read-exponent uniqueness on the committed template, from specialized
timestamp uniqueness.  No uniqueness-window extra -/
theorem read_exponents_nodup_independently
    {E : BuildableNockExecution F K} (D : Data E) :
    ∀ i, (readExps (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i)).Nodup :=
  GenericHonestPackage.packageOf_read_exponents_nodup D

/-- Independent reconstruction of `noWrapCheck` from the read half of the
window -/
theorem noWrapCheck_independently
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
    (horder : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α) :
    noWrapCheck
      (committedTemplate (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier
        E.cfg.challenges.z D.honestSeed_ne)
      E.cfg.challenges.α = true := by
  rw [committed_template_is_data_template D hgt I hprl hmore hord hordM hrows hgenF hF]
  exact (noWrapCheck_eq_true_iff _ _).2 horder.1

/-- Independent reconstruction of `alphaFreeAxisStructureCheck` from
specialized refinement plus both halves of the window. -/
theorem alphaFreeAxisStructureCheck_independently
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
    (horder : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α) :
    alphaFreeAxisStructureCheck
      (committedTemplate (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier
        E.cfg.challenges.z D.honestSeed_ne) = true := by
  rw [committed_template_is_data_template D hgt I hprl hmore hord hordM hrows hgenF hF]
  exact (alphaFreeAxisStructureCheck_eq_true_iff _).2
    (alphaFreeAxisStructure_of_specialized
      (D.executionTemplate E.cfg.challenges.z) E.cfg.challenges.α
      (packageOf_specialized_structural_independently D) horder.1 horder.2)

theorem structuralChecksAt_independently
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
    (horder : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α) :
    structuralChecksAt (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier
      E.cfg.challenges.z D.honestSeed_ne E.cfg.challenges.α = true := by
  rw [structuralChecksAt_splits_independently D hgt I hprl hmore hord hordM hrows hgenF hF]
  simp [alphaFreeAxisStructureCheck_independently D hgt I hprl hmore hord hordM hrows hgenF hF horder,
    noWrapCheck_independently D hgt I hprl hmore hord hordM hrows hgenF hF horder]

/-- The remaining Boolean is the committed template at honest `(z, α)`, not a
function of later-round `(a, g)` -/
theorem structuralChecksAt_ignores_later_round
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
    (a g : K) :
    structuralChecksAt (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier
      (nprSeed (honestCoin E a g)) D.honestSeed_ne
      (alphaM (honestCoin E a g)) =
      structuralChecksAt (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier
        E.cfg.challenges.z D.honestSeed_ne E.cfg.challenges.α := by
  simp [honestCoin, nprSeed, alphaM]

/-! ## D. Production fibre `Accepts` inhabited `∀ a g` under the window -/

/-- Independent reconstruction: production `strategy.Accepts` at `honestCoin`,
for `∀ a g`, from the uniqueness window.  This is production `Accepts`, not
verifier `Accepts`.  Not `∀ ω` -/
theorem fibre_accepts_independently
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
    (horder : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α) :
    ∀ a g : K,
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts (honestCoin E a g) E.cfg.challenges.lam := by
  intro a g
  refine (fibre_accepts_iff_structural_independently D hgt I hprl hmore hord hordM hrows hgenF hF a g).2 ?_
  simpa [honestCoin, nprSeed, alphaM] using
    structuralChecksAt_independently D hgt I hprl hmore hord hordM hrows hgenF hF horder

/-- Same inhabitant, written as the production projection -/
theorem fibre_accepts_is_production_accepts
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
    (horder : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α) :
    ∀ a g : K,
      ProductionStrategy.Accepts (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
        (honestCoin E a g) E.cfg.challenges.lam := by
  intro a g
  rw [← package_strategy_accepts_is_production D hgt I hprl hmore hord hordM hrows hgenF hF]
  exact fibre_accepts_independently D hgt I hprl hmore hord hordM hrows hgenF hF horder a g

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
    (hF : GeneratedField.PrimeFieldElems F) (lmb : K) :
    ¬ ∀ ω : JointCoins K, (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts ω lmb :=
  GenericHonestPackage.packageOf_not_forall_omega D hgt I hprl hmore hord hordM hrows hgenF hF (lmb := lmb)

theorem package_accepts_zero_npr_is_false
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) (lmb : K) :
    ¬ P.strategy.Accepts ((0, 0), (0, 0)) lmb := by
  simp [ProductionStrategy.Accepts, nprSeed]

/-! ## E. Axis-structure modules: existing forward lemmas keep their types -/

/-- Forward reindex still needs only `ReadVerifyNested`.  The reverse added
an injectivity hypothesis; this forward lemma did not gain one. -/
theorem forward_reindex_still_needs_only_nested
    (f : ℕ → ℕ) {t : MTree K} (h : ReadVerifyNested t) :
    ReadVerifyNested (reindexAxisTree f t) :=
  readVerifyNested_reindexAxisTree f h

/-- Reverse reindex is the new additive lemma and does take injectivity. -/
theorem reverse_reindex_takes_injectivity
    (f : ℕ → ℕ) {t : MTree K}
    (hinj : ∀ x y,
      (x ∈ readExps t ∨ x ∈ verifyExps t) →
        (y ∈ readExps t ∨ y ∈ verifyExps t) → f x = f y → x = y)
    (h : ReadVerifyNested (reindexAxisTree f t)) :
    ReadVerifyNested t :=
  readVerifyNested_of_reindexAxisTree f hinj h

/-- Forward `LmIO` map still injects only on requests -/
theorem forward_lmIO_still_injective_on_requests_only
    {R S : Type*} [DecidableEq R] [DecidableEq S]
    (Ksz : ℕ) (requests responses : List R) (f : R → S)
    (h : IO.LmIO Ksz requests responses)
    (hinj : ∀ x ∈ requests, ∀ y ∈ requests, f x = f y → x = y) :
    IO.LmIO Ksz (requests.map f) (responses.map f) :=
  lmIO_map_of_injective_on_requests Ksz requests responses f h hinj

/-- Forward transport to specialized refinement still requires **both**
Booleans -/
theorem forward_refinement_still_needs_both_booleans
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α lmb : K)
    (hstructure : alphaFreeAxisStructureCheck E = true)
    (hnowrap : noWrapCheck E α = true) :
    ExactAxisStructuralRefinement (T.specialize α lmb) (E.specializeA α lmb) :=
  exactAxisStructuralRefinement_of_checks E α (lmb := lmb) hstructure hnowrap

/-- Recovered exponents are injective on the uniqueness window.  This is the
new additive injectivity lemma, not a weakening of `recoveredExponent_pow`. -/
theorem recoveredExponent_injOn_window (α : K) :
    Set.InjOn (recoveredExponent α) (Set.Iio (orderOf α)) :=
  recoveredExponent_injOn_Iio_orderOf α

/-! ## F. Named extras remain; `packageR` is not this module -/

theorem censusRecordPremises_eta_still_five
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } := by
  cases C
  rfl

theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

theorem memoryRecordPremises_eta_still_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } := by
  cases M
  rfl

theorem any_universal_data_still_forces_q_pin
    (g : ∀ E : BuildableNockExecution F K, Data E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  GenericHonestPackage.generic_data_would_force_q_equality (F := F) (K := K) g

theorem released_builder_still_takes_hzero
    {E : BuildableNockExecution F K}
    (I : Inputs E)
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
    Nonempty (OptimizedFullStrictNockVMROMPackage F K I.hOrb) :=
  ⟨buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF⟩

/-! ## G. F73: production fibre `Accepts` under the same named window -/

variable [Fintype F] [DecidableEq F]

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

variable (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution)
include hmore73

theorem package73Of_fibre_accepts
    (horder : ForestExponentOrder
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α) :
    ∀ a g : K73cubic,
      (package73Of hmore73).strategy.Accepts (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam :=
  GenericHonestPackage.Concrete.package73Of_fibre_accepts hmore73 horder

theorem package73Of_fibre_accepts_is_production
    (horder : ForestExponentOrder
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α) (a g : K73cubic) :
    ProductionStrategy.Accepts (package73Of hmore73).strategy
      (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam := by
  have h := package73Of_fibre_accepts hmore73 horder a g
  simpa [package_strategy_accepts_is_production data73 f73_char_gt_eleven
    inputs73Fold2 BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
    hmore73
    BuildablePackage.Concrete.concreteExecution_walk_order
    BuildablePackage.Concrete.concreteExecution_memory_walk_order]
    using h

theorem package73Of_structuralChecksAt
    (horder : ForestExponentOrder
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α) :
    structuralChecksAt (package73Of hmore73).strategy.verifier
      concreteExecution.cfg.challenges.z data73.honestSeed_ne
      concreteExecution.cfg.challenges.α = true :=
  GenericHonestPackage.Concrete.package73Of_structuralChecksAt hmore73 horder

theorem package73Of_read_exponents_nodup :
    ∀ i, (readExps (alphaFreeRoot
      (data73.executionTemplate concreteExecution.cfg.challenges.z) i)).Nodup :=
  GenericHonestPackage.packageOf_read_exponents_nodup data73

theorem package73Of_not_forall_omega (lmb : K73cubic) :
    ¬ ∀ ω : JointCoins K73cubic, (package73Of hmore73).strategy.Accepts ω lmb :=
  GenericHonestPackage.Concrete.package73Of_not_forall_omega hmore73 (lmb := lmb)

/-- Negative control: the hand-built F73 package still inhabits production
`Accepts` at its own honest coin by unfolding that fixture's forest.  The
generic `packageOf` path does not inherit that inhabitant. -/
theorem concrete_fixture_production_accepts_honestCoins :
    concreteStrictPackage.strategy.Accepts honestCoins MemoryTable.formRDefault :=
  ConcreteStrictPackage.production_accepts_honestCoins

end Concrete

/-! ## H. -/

inductive ReviewedField110
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

def substantiveFields110 : List ReviewedField110 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields110 : List ReviewedField110 := [.structural]

def residualFields110 : List ReviewedField110 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Strategy completeness on the fibre is not a statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields110.length = 11 ∧
      typeSummaryFields110.length = 1 ∧
      residualFields110 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields110.length = 2 ∧
      (substantiveFields110 ++ typeSummaryFields110 ++ residualFields110).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

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
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    ∀ (ω : JointCoins K) (lmb : K),
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts ω lmb →
        ω ∉ FailureUnion (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
          (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.census lmb →
        GenuineTargetAt (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
          (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).q
          (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.Λ ω lmb :=
  (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).containment

#print axioms package_strategy_accepts_is_production
#print axioms residual_accepts_is_template_adapter
#print axioms committed_template_is_data_template
#print axioms fibre_accepts_iff_structural_independently
#print axioms structuralChecksAt_splits_independently
#print axioms ForestExponentOrder_expands
#print axioms noWrapCheck_is_read_half
#print axioms ForestExponentOrder_ignores_later_round
#print axioms inputs_eta_still_named
#print axioms timestampBounds_are_semantic_preimage
#print axioms semantic_preimage_bounds_derived_io_nats
#print axioms specialized_structural_already_on_execution
#print axioms packageOf_specialized_structural_independently
#print axioms read_exponents_nodup_independently
#print axioms noWrapCheck_independently
#print axioms alphaFreeAxisStructureCheck_independently
#print axioms structuralChecksAt_independently
#print axioms structuralChecksAt_ignores_later_round
#print axioms fibre_accepts_independently
#print axioms fibre_accepts_is_production_accepts
#print axioms packageOf_not_forall_omega
#print axioms package_accepts_zero_npr_is_false
#print axioms forward_reindex_still_needs_only_nested
#print axioms reverse_reindex_takes_injectivity
#print axioms forward_lmIO_still_injective_on_requests_only
#print axioms forward_refinement_still_needs_both_booleans
#print axioms recoveredExponent_injOn_window
#print axioms censusRecordPremises_eta_still_five
#print axioms residualPremises_eta_still_four
#print axioms memoryRecordPremises_eta_still_two
#print axioms any_universal_data_still_forces_q_pin
#print axioms released_builder_still_takes_hzero
#print axioms Concrete.package73Of_fibre_accepts
#print axioms Concrete.package73Of_fibre_accepts_is_production
#print axioms Concrete.package73Of_structuralChecksAt
#print axioms Concrete.package73Of_read_exponents_nodup
#print axioms Concrete.package73Of_not_forall_omega
#print axioms Concrete.concrete_fixture_production_accepts_honestCoins
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms containment_is_implication_not_forall_omega
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.ForestExponentOrder
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.packageOf_fibre_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.packageOf_noWrapCheck
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.packageOf_alphaFreeAxisStructureCheck
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch110
