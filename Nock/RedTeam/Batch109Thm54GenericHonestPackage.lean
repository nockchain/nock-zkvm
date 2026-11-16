import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.RedTeam.Batch108Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  Package `strategy.verifier` is definitionally the residual
verifier (`rfl`).  Residual fibre `Accepts` transports to that verifier at
`honestCoin` for `∀ a g`.  Production `strategy.Accepts` is
`ProductionStrategy.Accepts`, a strictly larger predicate: it additionally
requires `structuralChecksAt` and `RootAxisBoundaryAt`.  The per-root axis
boundary at honest `(z, α)` is independently compiled from specialized zero
`countsP` and does not mention later-round `(a, g)`.
Production fibre `Accepts` is therefore equivalent to
`structuralChecksAt = true`.  That Boolean expands to
`alphaFreeAxisStructureCheck && noWrapCheck`.
Neither conjunct is `true` by `rfl` on the generic `packageOf` template;
neither is inhabited from `Data` alone.  Specialized
`ExactAxisStructuralRefinement` is already on `E.memoryTrace` and is a
different object.  Production `strategy.Accepts` is not inhabited `∀ a g`.
Not `∀ ω`.  Accounting remains `11+1+2`.  F73 inhabits verifier `Accepts`
and the root-axis boundary; it does not inhabit production `Accepts`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch109

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
open Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.Framework

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## A. `rfl` verifier identity: package strategy.verifier is residual -/

/-- Independent reconstruction: the constructed package strategy's verifier is
definitionally the residual verifier consumed by `packageOf`.
Not production `Accepts` -/
theorem strategy_verifier_is_residual_rfl
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
    (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier =
      (commitmentResidualOfArrays_of_char D hgt).verifier :=
  rfl

/-- The same identity, written as the production `ProductionStrategy.verifier`
projection -/
theorem production_strategy_verifier_projection
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
    (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier =
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.strategy.verifier :=
  rfl

/-! ## B. Package verifier `Accepts` holds; it is residual, not production -/

/-- Residual fibre `Accepts` does not mention the package strategy. -/
theorem residual_verifier_accepts_without_package
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K) :
    ∀ a g : K,
      (commitmentResidualOfArrays_of_char D hgt).verifier.Accepts
        (honestCoin E a g) E.cfg.challenges.lam :=
  fibre_residual_accepts_of_char D hgt

/-- Independent transport: package-strategy `verifier.Accepts` at `honestCoin`.
This is residual `Accepts`, not production `strategy.Accepts`. -/
theorem package_verifier_accepts_independently
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
    ∀ a g : K,
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier.Accepts (honestCoin E a g) E.cfg.challenges.lam := by
  intro a g
  rw [strategy_verifier_is_residual_rfl D hgt I]
  exact residual_verifier_accepts_without_package D hgt a g

theorem residual_accepts_is_template_adapter
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (ω : JointCoins K) (lmb : K) :
    (commitmentResidualOfArrays_of_char D hgt).verifier.Accepts ω lmb =
      TemplateAdapter.Strategy.Accepts
        (commitmentResidualOfArrays_of_char D hgt).verifier ω lmb :=
  rfl

/-! ## C. Production `Accepts` is a larger predicate -/

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

/-- Production `Accepts` additionally requires axis-structure and the per-root
boundary.  Verifier `Accepts` is only the first conjunct of the first half. -/
theorem production_accepts_expands
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
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts ω lmb ↔
      ProductionAxisStructureAccepts
        (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier ω lmb ∧
        (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.RootAxisBoundaryAt
          (nprSeed ω) hz (alphaM ω) :=
  (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.accepts_iff ω lmb hz

theorem production_axis_accepts_expands
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
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    ProductionAxisStructureAccepts
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier ω lmb ↔
      ((packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier.messageAt ω lmb hz).VerifierChecks
        (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier.raw.claim ω ∧
        structuralChecksAt (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier
          (nprSeed ω) hz (alphaM ω) = true :=
  ProductionAxisStructureVerifier.accepts_iff
    (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier ω lmb hz

/-- Zero NPR seed still yields production `False` for every package.
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

/-! ## D. `RootAxisBoundaryAt` at honest `(z, α)`, independent of `(a, g)`

Paper NMR/forest: halt zeros of `axis_counts`/`axis_indicator`; mutated subjects feed the same forest. -/

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

/-- Independent reconstruction of the honest-sample root polynomial: specialized
`countsP_bin` (Form R completeness substrate) evaluates to zero at the honest sample.
Independent of later-round `(a, g)` -/
theorem honest_root_polynomial_zero
    {E : BuildableNockExecution F K} (D : Data E)
    (i : Fin (configTemplateOf E E.cfg.challenges.z).kMem) :
    (countsP_bin
      (templateAxisTree
        (templateMemoryTreeAt (D.executionTemplate E.cfg.challenges.z) i))).eval
      E.cfg.challenges.α = 0 := by
  have heval := specialized_countsP_bin_eval (lmb := E.cfg.challenges.lam)
    (D.executionTemplate E.cfg.challenges.z) E.cfg.challenges.α i
  rw [← heval]
  have hcfg := D.honest_cfg
  have hexec := heq_of_eq D.honest_execA
  have htree := GenericHonestPackage.exactAxisTree_congr hcfg hexec i
  have hzero := rootPolynomial_of_exactMemoryAxisValidity E.two_ne_zero
    E.memoryTrace.axisStructural E.memoryTrace.axisValidity E.memoryTrace.support
      ⟨i.val, hcfg ▸ i.isLt⟩
  rw [htree, hzero]
  simp

/-- Production per-root axis boundary of the constructed package at the honest
sample.  Not `structuralChecksAt`, and not `strategy.Accepts`. -/
theorem package_root_axis_boundary_independently
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
    (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.RootAxisBoundaryAt
      E.cfg.challenges.z D.honestSeed_ne E.cfg.challenges.α := by
  intro i
  have htmpl := committed_template_is_data_template D hgt I
  have hbound := honest_root_polynomial_zero D
  revert i
  rw [htmpl]
  exact hbound

/-- The boundary is a statement about `(z, α)` only: later-round `(a, g)` do
not appear in the type -/
theorem root_axis_boundary_ignores_later_round
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
    (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.RootAxisBoundaryAt
      (nprSeed (honestCoin E a g)) D.honestSeed_ne
      (alphaM (honestCoin E a g)) := by
  simpa [honestCoin, nprSeed, alphaM] using
    package_root_axis_boundary_independently D hgt I hprl hmore hord hordM hrows hgenF hF

/-! ## E. `structuralChecksAt` is the remaining conjunct; both halves stay open -/

/-- Independent reconstruction of the fibre iff: production `Accepts` at
`honestCoin` is exactly `structuralChecksAt = true`.  Verifier `Accepts` and
`RootAxisBoundaryAt` are already compiled.  Not `∀ ω`. -/
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

/-- This is `rfl`. -/
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

/-- α-free structure is a `decide` of per-root ancestry/nodup plus the one
global `intermediate` exponent matching.  Not `true` by `rfl`. -/
theorem alphaFree_expands_to_decide
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) :
    alphaFreeAxisStructureCheck E =
      (decide (∀ i : Fin T.kMem,
          alphaFreeRootStructureCheck (alphaFreeRoot E i) = true) &&
        forestExponentPartitionCheck E) :=
  rfl

/-- No-wrap is a `decide` that every read exponent lies below `orderOf α`.
Not `true` by `rfl` -/
theorem noWrap_expands_to_decide
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) :
    noWrapCheck E α =
      decide (∀ i : Fin T.kMem,
          rootNoWrapCheck α (alphaFreeRoot E i) = true) :=
  rfl

/-- Specialized `ExactAxisStructuralRefinement` is already on the supplied
execution.  This is not `alphaFreeAxisStructureCheck` and not `noWrapCheck`. -/
theorem specialized_structural_already_on_execution
    (E : BuildableNockExecution F K) :
    ExactAxisStructuralRefinement E.cfg E.execA :=
  E.memoryTrace.axisStructural

/-- Forward transport from the α-free/no-wrap pair to the specialized
refinement requires **both** halves.  `Data` supplies neither Boolean. -/
theorem specialized_of_checks_needs_both
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α lmb : K)
    (hstructure : alphaFreeAxisStructureCheck E = true)
    (hnowrap : noWrapCheck E α = true) :
    ExactAxisStructuralRefinement (T.specialize α lmb) (E.specializeA α lmb) :=
  exactAxisStructuralRefinement_of_checks E α (lmb := lmb) hstructure hnowrap

/-- Named remaining conjunct: production fibre `Accepts` from the Boolean.
The Boolean itself is not inhabited -/
theorem fibre_accepts_of_structural_independently
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
    (hstruct :
      structuralChecksAt (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier
        E.cfg.challenges.z D.honestSeed_ne E.cfg.challenges.α = true) :
    ∀ a g : K,
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts (honestCoin E a g) E.cfg.challenges.lam :=
  GenericHonestPackage.packageOf_fibre_accepts_of_structural D hgt I hprl hmore hord hordM hrows hgenF hF hstruct

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

/-! ## G. F73: verifier `Accepts` and root-axis boundary inhabit; production does not -/

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

-- Form R leftover LaterSeedZeros residual.
variable (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution)
include hmore73

theorem package73_z : concreteExecution.cfg.challenges.z = honestSeed :=
  rfl

theorem package73_alpha : concreteExecution.cfg.challenges.α = honestAlpha :=
  rfl

theorem package73Of_strategy_verifier :
    (package73Of hmore73).strategy.verifier = residual73Honest_of_char.verifier :=
  GenericHonestPackage.Concrete.package73Of_strategy_verifier hmore73

theorem package73Of_fibre_verifier_accepts :
    ∀ a g : K73cubic,
      (package73Of hmore73).strategy.verifier.Accepts
        (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam :=
  GenericHonestPackage.Concrete.package73Of_fibre_verifier_accepts hmore73

theorem package73Of_fibre_root_axis_boundary :
    (package73Of hmore73).strategy.RootAxisBoundaryAt
      concreteExecution.cfg.challenges.z data73.honestSeed_ne
      concreteExecution.cfg.challenges.α :=
  GenericHonestPackage.Concrete.package73Of_fibre_root_axis_boundary hmore73

theorem package73Of_fibre_accepts_iff_structural (a g : K73cubic) :
    (package73Of hmore73).strategy.Accepts (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam ↔
      structuralChecksAt (package73Of hmore73).strategy.verifier
        (nprSeed (honestCoin concreteExecution a g)) data73.honestSeed_ne
        (alphaM (honestCoin concreteExecution a g)) = true :=
  GenericHonestPackage.Concrete.package73Of_fibre_accepts_iff_structural hmore73 a g

/-- F73 production `Accepts` is still exactly the remaining Boolean.  This
module does not inhabit that Boolean -/
theorem package73Of_accepts_iff_structuralChecksAt (a g : K73cubic) :
    (package73Of hmore73).strategy.Accepts (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam ↔
      structuralChecksAt (package73Of hmore73).strategy.verifier
        concreteExecution.cfg.challenges.z data73.honestSeed_ne
        concreteExecution.cfg.challenges.α = true :=
  package73Of_fibre_accepts_iff_structural hmore73 a g

theorem package73Of_structuralChecksAt_splits :
    structuralChecksAt (package73Of hmore73).strategy.verifier
      honestSeed data73.honestSeed_ne honestAlpha =
      (alphaFreeAxisStructureCheck
        (committedTemplate (package73Of hmore73).strategy.verifier
          honestSeed data73.honestSeed_ne) &&
        noWrapCheck
          (committedTemplate (package73Of hmore73).strategy.verifier
            honestSeed data73.honestSeed_ne)
          honestAlpha) :=
  rfl

/-- The F73 committed template is the `Data` template, not the hand-built
`ConcreteStrictPackage.executionTemplate`.  Fixture `honest_structuralChecks`
does not transport by `rfl` -/
theorem package73_committed_is_data_template :
    committedTemplate (package73Of hmore73).strategy.verifier
      honestSeed data73.honestSeed_ne =
      data73.executionTemplate honestSeed :=
  rfl

theorem package73Of_rejects_zero_seed
    (hax : OptimizedComputeFinalTrace.FormRAxisBound (package73Of hmore73).optimized.sampled
      (package73Of hmore73).optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis (package73Of hmore73).optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F73) (lmb : K73cubic) :
    ¬ (package73Of hmore73).strategy.Accepts ((0, 0), (0, 0)) lmb :=
  package_accepts_zero_npr_is_false (package73Of hmore73) hax hbasis hwidth lmb

theorem package73Of_not_forall_omega (lmb : K73cubic) :
    ¬ ∀ ω : JointCoins K73cubic, (package73Of hmore73).strategy.Accepts ω lmb :=
  GenericHonestPackage.Concrete.package73Of_not_forall_omega hmore73 (lmb := lmb)

/-- Negative control: the hand-built F73 package *does* inhabit production
`Accepts` at its own honest coin, by unfolding that fixture's forest. -/
theorem concrete_fixture_production_accepts_honestCoins :
    concreteStrictPackage.strategy.Accepts honestCoins MemoryTable.formRDefault :=
  ConcreteStrictPackage.production_accepts_honestCoins

end Concrete

/-! ## H. -/

inductive ReviewedField109
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

def substantiveFields109 : List ReviewedField109 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields109 : List ReviewedField109 := [.structural]

def residualFields109 : List ReviewedField109 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Strategy completeness on the fibre is not a statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields109.length = 11 ∧
      typeSummaryFields109.length = 1 ∧
      residualFields109 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields109.length = 2 ∧
      (substantiveFields109 ++ typeSummaryFields109 ++ residualFields109).Nodup ∧
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

#print axioms strategy_verifier_is_residual_rfl
#print axioms production_strategy_verifier_projection
#print axioms residual_verifier_accepts_without_package
#print axioms package_verifier_accepts_independently
#print axioms residual_accepts_is_template_adapter
#print axioms package_strategy_accepts_is_production
#print axioms production_accepts_expands
#print axioms production_axis_accepts_expands
#print axioms package_accepts_zero_npr_is_false
#print axioms packageOf_not_forall_omega
#print axioms committed_template_is_data_template
#print axioms honest_root_polynomial_zero
#print axioms package_root_axis_boundary_independently
#print axioms root_axis_boundary_ignores_later_round
#print axioms fibre_accepts_iff_structural_independently
#print axioms structuralChecksAt_splits_independently
#print axioms alphaFree_expands_to_decide
#print axioms noWrap_expands_to_decide
#print axioms specialized_structural_already_on_execution
#print axioms specialized_of_checks_needs_both
#print axioms fibre_accepts_of_structural_independently
#print axioms censusRecordPremises_eta_still_five
#print axioms residualPremises_eta_still_four
#print axioms memoryRecordPremises_eta_still_two
#print axioms inputs_eta_still_named
#print axioms any_universal_data_still_forces_q_pin
#print axioms released_builder_still_takes_hzero
#print axioms Concrete.package73Of_strategy_verifier
#print axioms Concrete.package73Of_fibre_verifier_accepts
#print axioms Concrete.package73Of_fibre_root_axis_boundary
#print axioms Concrete.package73Of_fibre_accepts_iff_structural
#print axioms Concrete.package73Of_accepts_iff_structuralChecksAt
#print axioms Concrete.package73Of_structuralChecksAt_splits
#print axioms Concrete.package73_committed_is_data_template
#print axioms Concrete.package73Of_rejects_zero_seed
#print axioms Concrete.package73Of_not_forall_omega
#print axioms Concrete.concrete_fixture_production_accepts_honestCoins
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms containment_is_implication_not_fibre_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.packageOf_strategy_verifier
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.packageOf_fibre_verifier_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.packageOf_fibre_root_axis_boundary
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.packageOf_fibre_accepts_iff_structural
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.packageOf_structuralChecksAt_splits
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch109
