import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.OptimizedCanonicalHostileLists
import Nock.NockVMROM.Thm54.HonestCommitment
import Nock.NockVMROM.Thm54.BuildableChips
import Nock.NockVMROM.Thm54.MemoryHaltLeavesHonest

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Generic canonical traces of a constructed package (hoisted from `MultiRootOptimizedAcceptance`)

`canonicalComputeTrace` / `canonicalMemoryTrace` and their satisfaction, the canonical
acceptance tuple and the memory-collision half of the failure event are generic over
`OptimizedFullStrictNockVMROMPackage`; they lived inside the multi-root fixture module and so
made every consumer (`OptimizedComputeCanonicalDenominator`, `OptimizedHostileIOAssembly`, ...)
import that fixture. Hoisted unchanged (same namespace, same names) apart from the 28th
`C' = 1` -> `CprimeCoherent` conversion. -/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance

open scoped Classical Polynomial
open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
open Nock.NockVMROM.Thm54.OptimizedComputeSampledTrace
open Nock.NockVMROM.Thm54.OptimizedComputeOverlay
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.StrictExtension
open Module
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.Noun Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open SemanticStrategy SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips

noncomputable section

section Generic

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)] [FiniteDimensional F K]
variable {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

omit [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] in
/-- Specialization depends on the seed and `alphaM` values only, not on the nonzero proof. -/
theorem specializedProblem_congr
    (T : SemanticTimestampStrategy.DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    {z z' α α' lmb : K} (hz : z ≠ 0) (hz' : z' ≠ 0) (hzz : z = z') (haa : α = α') :
    specializedProblem T z hz α lmb = specializedProblem T z' hz' α' lmb := by
  subst hzz
  subst haa
  have h : hz = hz' := Subsingleton.elim _ _
  rw [h]

/-- The canonical `199`-column compute trace of the package's own chip. -/
def canonicalComputeTrace : Fin P.computeChip.rap.w → F[X] :=
  correctedCanonicalFinalTrace P.optimized.sampled
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
    P.optimized.basis P.optimized.computeChallenge P.optimized.computePublic
    P.optimized.orbit

/-- The canonical `196`-column memory trace of the package's own chip. -/
def canonicalMemoryTrace : Fin P.memoryChip.rap.w → F[X] :=
  canonicalFinalMemoryTrace P.optimized.sampled P.optimized.memoryNodes
    P.optimized.basis P.optimized.memoryChallenge P.optimized.memoryPublic
    P.optimized.orbit

theorem canonicalComputeTrace_satisfies
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    RAP.SatisfiesWithPreprocessing P.computeChip (canonicalComputeTrace P) := by
  simpa [canonicalComputeTrace] using
    correctedCanonicalFinalTrace_satisfies
      P.optimized.sampled P.optimized.computeObligations
      P.optimized.family.problem.cfg.compRows_pos
      P.optimized.computeNodes P.optimized.computeNodes_injective
      P.optimized.basis P.optimized.computeChallenge P.optimized.computePublic
      P.optimized.orbit P.optimized.computeAdjacentOrbit
      P.optimized.computeChallengePins P.optimized.computePublicPins
      P.optimized.computeRequestsPins P.optimized.computeLineOrigin
      P.optimized.computeWalkOrder hax hbasis hwidth

theorem canonicalMemoryTrace_satisfies
    (hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
        (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hC : P.optimized.family.problem.exec.CprimeCoherent) :
    RAP.SatisfiesWithPreprocessing P.memoryChip (canonicalMemoryTrace P) := by
  simpa [canonicalMemoryTrace] using
    canonicalFinalMemoryTrace_satisfies P.optimized.sampled P.optimized.memoryProduction
      P.optimized.memoryNodes P.optimized.memoryNodes_injective P.optimized.basis
      P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit
      P.optimized.memoryCoordinatePins P.optimized.memoryOrbitAligned
      P.optimized.memoryDenominatorsSafe P.optimized.pairedRecordLayout
      P.optimized.sampled.honestVer P.optimized.memoryWalkOrder hmore
      P.optimized.family.problem.memory_same_lambda hC
      (MemoryPaperFactorization.hdenAll_of_interPoleHitGood P.optimized.sampled
        P.optimized.memoryNodes P.optimized.memoryNodes_injective P.optimized.basis
        P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit
        P.optimized.memoryCoordinatePins P.optimized.sampled.honestVer hC)
      (MemoryHaltLeavesHonest.package_haltLeavesBase P)

/-- Honest matmul (or any constructed package) at the deployed `cfg.kMem` chip. -/
theorem honest_matmul_accepted_at_deployed_chip
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
        (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hC : P.optimized.family.problem.exec.CprimeCoherent) :
    RAP.SatisfiesWithPreprocessing P.memoryChip (canonicalMemoryTrace P) :=
  canonicalMemoryTrace_satisfies P hmore hC

/-- Honest Peano-fib (or any constructed package) at the deployed `cfg.kMem` chip. -/
theorem honest_peano_fib_accepted_at_deployed_chip
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
        (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hC : P.optimized.family.problem.exec.CprimeCoherent) :
    RAP.SatisfiesWithPreprocessing P.memoryChip (canonicalMemoryTrace P) :=
  canonicalMemoryTrace_satisfies P hmore hC

/-- The compute-chip challenge tuple the verifier reads off the canonical trace: the
package's equality coins `(a, b, c)`. -/
def canonicalComputeChallengeTuple : FinalComputeChallengeTuple K :=
  ⟨P.objects.cfg.challenges.a, P.objects.cfg.challenges.b, P.objects.cfg.challenges.c⟩

/-- The memory-chip challenge tuple the verifier reads off the canonical trace: the internal
`intermediate` LogUp pole at slot `6` (W4 stage 2). -/
def canonicalMemoryChallengeTuple : MemoryChallengeTuple K :=
  ⟨P.packageInterPole, P.objects.cfg.challenges.lam⟩

/-- The optimized chip-level challenge tuple at a joint coin. -/
def canonicalProductionTuple (j : JointCoins K) :
    OptimizedProductionChallengeTuple K F :=
  (j,
    ((P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole),
      (canonicalComputeChallengeTuple P, canonicalMemoryChallengeTuple P)))

/-- **The canonical traces satisfy every acceptance field except P8 and the same-problem link.** -/
theorem canonicalTraceAcceptance
    (hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
        (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hC : P.optimized.family.problem.exec.CprimeCoherent)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    P.OptimizedHistoricalTraceAcceptanceAt (canonicalComputeTrace P) (canonicalMemoryTrace P)
      ((P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole),
        (canonicalComputeChallengeTuple P, canonicalMemoryChallengeTuple P)) where
  sampled_io_coins := rfl
  memory_sampled_coins := P.memorySourceEnv_sampled_coins (canonicalMemoryTrace P)
  memory_intermediate_pole :=
    P.memory_intermediate_pole_of_tuple (canonicalMemoryTrace P) _ rfl
  compute_satisfies := canonicalComputeTrace_satisfies P hax hbasis hwidth
  memory_satisfies := canonicalMemoryTrace_satisfies P hmore hC

/-- **The optimized chip-level acceptance at any coin the package accepts on its honest fibre.** -/
theorem canonicalProductionAcceptance (j : JointCoins K)
    (hp8 : P.strategy.Accepts j P.objects.cfg.challenges.lam)
    (hseed : nprSeed j = P.honestSeed) (halpha : alphaM j = P.honestAlpha)
    (hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
        (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hC : P.optimized.family.problem.exec.CprimeCoherent)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    P.OptimizedHistoricalAcceptanceAt (canonicalComputeTrace P) (canonicalMemoryTrace P)
      (canonicalProductionTuple P j) := by
  have hz : nprSeed j ≠ 0 := by rw [hseed]; exact P.honestSeed_ne
  refine (P.optimizedHistoricalAcceptanceAt_iff (canonicalComputeTrace P)
    (canonicalMemoryTrace P) j _).2 ⟨hp8, ?_, canonicalTraceAcceptance P hmore hC hax hbasis hwidth⟩
  refine OptimizedSameProblemAt.of_objects P j P.objects.cfg.challenges.lam hz ?_
  have hcongr :
      specializedProblem P.optimized.verifier.raw.timestamp (nprSeed j) hz (alphaM j)
          P.objects.cfg.challenges.lam =
        specializedProblem P.optimized.verifier.raw.timestamp P.honestSeed P.honestSeed_ne
          P.honestAlpha P.objects.cfg.challenges.lam :=
    specializedProblem_congr P.optimized.verifier.raw.timestamp hz P.honestSeed_ne hseed halpha
  rw [hcongr]
  exact P.honest_specialization

/-! ### The memory half of the optimized failure event, at the canonical trace -/

theorem canonical_memoryBaseEnv (i : Fin P.optimized.family.problem.cfg.memRows) :
    P.memoryBaseEnv (canonicalMemoryTrace P) i =
      canonicalPhysicalEnv P.optimized.sampled P.optimized.memoryNodes P.optimized.basis
        P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit i := by
  unfold OptimizedFullStrictNockVMROMPackage.memoryBaseEnv
  unfold OptimizedFullStrictNockVMROMPackage.memorySourceTrace
  unfold canonicalMemoryTrace
  unfold canonicalPhysicalEnv
  unfold canonicalFinalMemoryTrace
  dsimp only
  erw [project_rightPadTrace]

theorem canonical_memorySourceEnv (i : Fin P.optimized.family.problem.cfg.memRows) :
    P.memorySourceEnv (canonicalMemoryTrace P) i =
      canonicalGatheredEnv P.optimized.sampled P.optimized.memoryNodes P.optimized.basis
        P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit i := by
  unfold OptimizedFullStrictNockVMROMPackage.memorySourceEnv
  unfold canonicalGatheredEnv
  rw [canonical_memoryBaseEnv]

theorem canonical_memory_collision_good
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hinter : P.optimized.sampled.interPole ≠ 0) :
    RepairedMemoryCollisionGood P.optimized.basis
      (P.memoryBaseEnv (canonicalMemoryTrace P) i)
      (P.memorySourceEnv (canonicalMemoryTrace P) i) := by
  rw [canonical_memoryBaseEnv, canonical_memorySourceEnv]
  set envK :=
    canonicalGatheredEnv P.optimized.sampled P.optimized.memoryNodes P.optimized.basis
      P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit i
  refine ⟨foldCollisionExcluded_of_nonagg envK ?rest ?chal, ?scalar⟩
  · intro e he h23 h24
    exact canonical_transitionSources P.optimized.sampled
      P.optimized.memoryProduction.toChipAssignment
      P.optimized.family.problem.memory_same_lambda P.optimized.memoryNodes
      P.optimized.memoryNodes_injective P.optimized.basis P.optimized.memoryChallenge
      P.optimized.memoryPublic P.optimized.orbit P.optimized.memoryCoordinatePins
      P.optimized.memoryOrbitAligned P.optimized.memoryDenominatorsSafe i
      e (extensionFoldSources_subset_transitionSources e he) h23 h24
  · have hpin : OptimizedMemoryGateBasis.foldChallenge.eval envK =
        P.optimized.sampled.interPole :=
      P.optimized.memoryCoordinatePins.sampledInterPole
    rw [hpin]
    exact hinter
  exact canonical_scalarCollisionExcluded P.optimized.sampled
    P.optimized.memoryProduction.toChipAssignment P.optimized.memoryNodes
    P.optimized.memoryNodes_injective P.optimized.basis P.optimized.memoryChallenge
    P.optimized.memoryPublic P.optimized.orbit P.optimized.memoryOrbitAligned i


theorem canonical_memory_outside_failure :
    canonicalMemoryChallengeTuple P ∉
      extensionMemoryCollisionEvent (P.memorySourceEnv (canonicalMemoryTrace P)) := by
  simp [extensionMemoryCollisionEvent]


end Generic

end -- noncomputable section

end Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
