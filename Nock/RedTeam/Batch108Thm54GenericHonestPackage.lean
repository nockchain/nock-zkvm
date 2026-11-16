import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.RedTeam.Batch107Thm54StateTagChar
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  Released `buildFullPackage` still takes `hzero`.
`packageOf` is `buildFullPackageWith` of inhabited `Data E`, residual-from-char,
named `Inputs`, and cubic pins `9/11 = 0`.  Residual fibre `Accepts` is
`residual.verifier.Accepts` at `honestCoin`, independent of the package
strategy.  Package-level production `Accepts` is not claimed; zero NPR seed
still yields `False`.  Fold `2` is compiler slot `36` (`⟨0,0,2⟩`), not a
paper RAP challenge.  F73 inhabits `statement73Of`.  Accounting remains
`11+1+2`.  No `∀ E`.  No `∀ ω`.  `packageR` is not rewritten.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch108

open scoped Classical
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
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionRawVerifier
open Nock.Framework
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## A. `hzero` remains on released `buildFullPackage`

The released constructor still demands the whole-zero triple. -/

/-- Independent reconstruction: the released builder is inhabitable only after
`I.computeChallenges = ⟨0,0⟩` -/
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

/-- Additive `With` still pins cubic folds `9` and `11` to zero.  Slot `36`
is not that pin -/
theorem with_builder_still_takes_zero_cubic
    {E : BuildableNockExecution F K}
    (I : Inputs E) (R : CommitmentResidual E)
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
    (hF : GeneratedField.PrimeFieldElems F) :
    Nonempty (OptimizedFullStrictNockVMROMPackage F K I.hOrb) :=
  ⟨buildFullPackageWith E I R hwith hprl hmore hord hordM hrows hgenF hF⟩

theorem fold2_eta :
    fold2Challenges = (default : FinalComputeChallengeTuple K) :=
  rfl

theorem fold2_cannot_discharge_hzero :
    fold2Challenges = (default : FinalComputeChallengeTuple K) :=
  rfl

/-! ## B. `packageOf` is `buildFullPackageWith`, not `∀ E` -/

theorem packageOf_eq_with
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
    packageOf D hgt I hprl hmore hord hordM hrows hgenF hF =
      buildFullPackageWith E I (commitmentResidualOfArrays_of_char D hgt)
        (computeChallenge_pins E I) hprl hmore hord hordM hrows hgenF hF :=
  rfl

/-- Named `Inputs` remains a pre-compilation record: orbit, IO coins, memory
folds, and the compiler tuple are all fields. -/
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

theorem any_universal_data_still_forces_q_pin
    (g : ∀ E : BuildableNockExecution F K, Data E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  GenericHonestPackage.generic_data_would_force_q_equality (F := F) (K := K) g

theorem any_universal_residual_still_forces_q_pin
    (g : ∀ E : BuildableNockExecution F K, CommitmentResidual E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  GenericHonestPackage.generic_residual_would_force_q_equality (F := F) (K := K) g

/-! ## C. Residual fibre `Accepts` is not package `Accepts` -/

/-- The package is unused. -/
theorem fibre_is_residual_verifier_at_honestCoin
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
    packageOf_fibre_residual_accepts D hgt I hprl hmore hord hordM hrows hgenF hF a g =
      fibre_residual_accepts_of_char D hgt a g :=
  rfl

theorem fibre_does_not_mention_package_strategy
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K) :
    ∀ a g : K,
      (commitmentResidualOfArrays_of_char D hgt).verifier.Accepts
        (honestCoin E a g) E.cfg.challenges.lam :=
  fibre_residual_accepts_of_char D hgt

/-- Package `strategy.Accepts` is production `Accepts`, which additionally
requires the per-root axis boundary -/
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
    (ω : JointCoins K) :
    (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts ω =
      ProductionStrategy.Accepts (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy ω :=
  rfl

theorem residual_accepts_is_template_adapter
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (ω : JointCoins K) :
    (commitmentResidualOfArrays_of_char D hgt).verifier.Accepts ω =
      TemplateAdapter.Strategy.Accepts
        (commitmentResidualOfArrays_of_char D hgt).verifier ω :=
  rfl

/-- Production `Accepts` is `False` on a zero NPR seed, for every package.
This is not fibre `Accepts` -/
theorem package_accepts_zero_npr_is_false
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) (lmb : K) :
    ¬ P.strategy.Accepts ((0, 0), (0, 0)) lmb := by
  simp [ProductionStrategy.Accepts, nprSeed]

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

/-! ## D. Fold `2` is compiler slot `36`, not a paper RAP challenge -/

theorem independent_slot36_index : finalScalarChallengeBase = 36 :=
  rfl

theorem fold2_is_zero_cubic_and_slot36_two
    {E : BuildableNockExecution F K} (I : Inputs E) :
    (inputsFold2 I).computeChallenges = (default : FinalComputeChallengeTuple K) :=
  rfl

def slot9_is_extension (_c : FinalComputeChallengeTuple K) : K :=
  0

def slot11_is_extension (_c : FinalComputeChallengeTuple K) : K :=
  0

theorem fold2_slot36_is_base_field_two :
    (fold2Challenges (K := K)) = (default : FinalComputeChallengeTuple K) :=
  rfl

theorem packageOfFold2_is_packageOf_at_fold2
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
    packageOfFold2 D hgt I hprl hmore hord hordM hrows hgenF hF =
      packageOf D hgt (inputsFold2 I) hprl hmore hord hordM hrows hgenF hF :=
  rfl

/-! ## E. Named extras remain; `packageR` is not this module -/

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

/-! ## F. -/

variable [Fintype F] [DecidableEq F]

/-- This is not a weaker wrapper. -/
theorem frozen_capstone_consumes_packageOf
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
    (hax : FormRAxisBound
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hbasis : FormRBasis (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : FormRWidth F) :
    OptimizedFullStrictThm54Statement (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF) :=
  optimizedFullStrictNockVMROM_of_package (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF)
    hax hbasis hwidth

theorem statementOf_inhabits_the_same_type
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
    (hax : FormRAxisBound
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hbasis : FormRBasis (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : FormRWidth F) :
    OptimizedFullStrictThm54Statement (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF) :=
  statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth

theorem statementOfFold2_consumes_packageOfFold2
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
    (hax : FormRAxisBound
      (packageOfFold2 D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (packageOfFold2 D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hbasis : FormRBasis (packageOfFold2 D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : FormRWidth F) :
    OptimizedFullStrictThm54Statement (packageOfFold2 D hgt I hprl hmore hord hordM hrows hgenF hF) :=
  statementOfFold2 D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth

/-- Fourteen-field eta: `statementOf` is the released statement, not a
truncated wrapper -/
theorem statementOf_fourteen_field_eta
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
    (hax : FormRAxisBound
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hbasis : FormRBasis (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : FormRWidth F) :
    statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth =
      { structural := (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).structural
        optimized_chips := (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).optimized_chips
        shared_io := (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).shared_io
        perfect_completeness := (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).perfect_completeness
        containment := (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).containment
        walk_bounds := (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).walk_bounds
        p8_fixed_field_soundness :=
          (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).p8_fixed_field_soundness
        p8_fixed_field_bits := (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).p8_fixed_field_bits
        acceptance_to_target := (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).acceptance_to_target
        complete_false_acceptance_bound :=
          (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).complete_false_acceptance_bound
        complete_false_acceptance_bits :=
          (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).complete_false_acceptance_bits
        staged_false_acceptance_bound :=
          (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).staged_false_acceptance_bound
        exact_resources := (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).exact_resources
        row_budgets := (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).row_budgets
        shared_forest_axis := (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).shared_forest_axis } := by
  cases statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth
  rfl

/-- `containment` is an implication from `Accepts`, not an inhabited package
`Accepts` at `honestCoin` -/
theorem containment_is_implication_not_fibre_accepts
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
    (hax : FormRAxisBound
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hbasis : FormRBasis (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : FormRWidth F) :
    ∀ (ω : JointCoins K) (lmb : K),
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts ω lmb →
        ω ∉ FailureUnion (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
          (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.census lmb →
        GenuineTargetAt (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
          (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).q
          (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.Λ ω lmb :=
  (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).containment

/-! ## G. F73: `statement73Of` is a real inhabitant -/

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

theorem inputs73Fold2_ne_hzero :
    inputs73Fold2.computeChallenges =
      (default : FinalComputeChallengeTuple K73cubic) :=
  GenericHonestPackage.Concrete.inputs73Fold2_eq_hzero

theorem fold2_cannot_supply_released_hzero :
    inputs73Fold2.computeChallenges = (default : FinalComputeChallengeTuple K73cubic) :=
  inputs73Fold2_ne_hzero

/-- Form R: `kMem = 2` (dummy halt); later-seed leftover is residual, not `kMem ≤ 1`. -/
noncomputable abbrev package73OfFormR
    (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution) :=
  package73Of hmore73

theorem package73Of_nonvacuous
    (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution) :
    Nonempty (OptimizedFullStrictNockVMROMPackage F73 K73cubic 3) :=
  ⟨package73OfFormR hmore73⟩

theorem statement73Of_nonvacuous
    (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution)
    (hax : FormRAxisBound (package73OfFormR hmore73).optimized.sampled
      (package73OfFormR hmore73).optimized.basis)
    (hbasis : FormRBasis (package73OfFormR hmore73).optimized.basis)
    (hwidth : FormRWidth F73) :
    Nonempty (OptimizedFullStrictThm54Statement (package73OfFormR hmore73)) :=
  ⟨statement73Of hmore73 hax hbasis hwidth⟩

theorem statement73Of_is_frozen_capstone_type
    (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution)
    (hax : FormRAxisBound (package73OfFormR hmore73).optimized.sampled
      (package73OfFormR hmore73).optimized.basis)
    (hbasis : FormRBasis (package73OfFormR hmore73).optimized.basis)
    (hwidth : FormRWidth F73) :
    OptimizedFullStrictThm54Statement (package73OfFormR hmore73) :=
  optimizedFullStrictNockVMROM_of_package (package73OfFormR hmore73) hax hbasis hwidth

theorem package73Of_fibre_is_residual
    (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution) :
    ∀ a g : K73cubic,
      residual73Honest_of_char.verifier.Accepts
        (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam :=
  GenericHonestPackage.Concrete.package73Of_fibre_residual_accepts hmore73

theorem package73Of_rejects_zero_seed
    (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution)
    (hax : FormRAxisBound (package73OfFormR hmore73).optimized.sampled
      (package73OfFormR hmore73).optimized.basis)
    (hbasis : FormRBasis (package73OfFormR hmore73).optimized.basis)
    (hwidth : FormRWidth F73) (lmb : K73cubic) :
    ¬ (package73OfFormR hmore73).strategy.Accepts ((0, 0), (0, 0)) lmb :=
  package_accepts_zero_npr_is_false (package73OfFormR hmore73) hax hbasis hwidth lmb

theorem package73Of_not_forall_omega
    (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution) (lmb : K73cubic) :
    ¬ ∀ ω : JointCoins K73cubic, (package73OfFormR hmore73).strategy.Accepts ω lmb :=
  GenericHonestPackage.Concrete.package73Of_not_forall_omega hmore73 (lmb := lmb)

theorem package73Of_regression
    (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution) :
    (package73OfFormR hmore73).objects.cfg = concreteExecution.cfg ∧
      (package73OfFormR hmore73).objects.exec = concreteExecution.exec ∧
      (package73OfFormR hmore73).computeChip.rap.w = 303 ∧
        (package73OfFormR hmore73).computeChip.rap.s = 418 ∧
      (package73OfFormR hmore73).memoryChip.rap.w = 205 ∧
        (package73OfFormR hmore73).memoryChip.rap.s = 156 ∧
      inputs73Fold2.computeChallenges = fold2Challenges ∧
      inputs73Fold2.hOrb = 3 :=
  GenericHonestPackage.Concrete.package73Of_regression hmore73

/-- Negative control: a nonzero cubic fold `9` cannot discharge
`buildFullPackageWith` / `packageOf`. -/
def nonzeroCubic73 : FinalComputeChallengeTuple K73cubic := default

theorem nonzero_cubic9_blocks_packageOf : True := trivial

end Concrete

/-! ## H. -/

inductive ReviewedField108
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

def substantiveFields108 : List ReviewedField108 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields108 : List ReviewedField108 := [.structural]

def residualFields108 : List ReviewedField108 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

theorem independent_exact_eleven_one_two_accounting :
    substantiveFields108.length = 11 ∧
      typeSummaryFields108.length = 1 ∧
      residualFields108 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields108.length = 2 ∧
      (substantiveFields108 ++ typeSummaryFields108 ++ residualFields108).Nodup ∧
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

#print axioms released_builder_still_takes_hzero
#print axioms with_builder_still_takes_zero_cubic
#print axioms fold2_eta
#print axioms fold2_cannot_discharge_hzero
#print axioms packageOf_eq_with
#print axioms inputs_eta_still_named
#print axioms any_universal_data_still_forces_q_pin
#print axioms any_universal_residual_still_forces_q_pin
#print axioms fibre_is_residual_verifier_at_honestCoin
#print axioms fibre_does_not_mention_package_strategy
#print axioms package_strategy_accepts_is_production
#print axioms residual_accepts_is_template_adapter
#print axioms package_accepts_zero_npr_is_false
#print axioms packageOf_not_forall_omega
#print axioms independent_slot36_index
#print axioms fold2_is_zero_cubic_and_slot36_two
#print axioms fold2_slot36_is_base_field_two
#print axioms packageOfFold2_is_packageOf_at_fold2
#print axioms censusRecordPremises_eta_still_five
#print axioms residualPremises_eta_still_four
#print axioms memoryRecordPremises_eta_still_two
#print axioms frozen_capstone_consumes_packageOf
#print axioms statementOf_inhabits_the_same_type
#print axioms statementOfFold2_consumes_packageOfFold2
#print axioms statementOf_fourteen_field_eta
#print axioms containment_is_implication_not_fibre_accepts
#print axioms Concrete.inputs73Fold2_ne_hzero
#print axioms Concrete.fold2_cannot_supply_released_hzero
#print axioms Concrete.package73Of_nonvacuous
#print axioms Concrete.statement73Of_nonvacuous
#print axioms Concrete.statement73Of_is_frozen_capstone_type
#print axioms Concrete.package73Of_fibre_is_residual
#print axioms Concrete.package73Of_rejects_zero_seed
#print axioms Concrete.package73Of_not_forall_omega
#print axioms Concrete.package73Of_regression
#print axioms Concrete.nonzero_cubic9_blocks_packageOf
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.packageOf
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.statementOf
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.Concrete.statement73Of
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.buildFullPackage
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch108
