import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedStrictPackageConcrete
import Nock.NockVMROM.Thm54.OptimizedCanonicalHostileLists
import Nock.NockVMROM.Thm54.MemoryHaltLeavesHonest
import Nock.NockVMROM.Thm54.GeneratedField

/-!
A concrete inhabitant of the full strict package over `F73 = ZMod 73` and the cubic extension
`K73cubic`: the package `concreteOptimizedFullStrictPackage`, its full statement, resource figures,
containment and production-acceptance facts, and the facts that the concrete memory and compute
challenges lie outside the consumed failure events.
-/

open Nock Nock.NockVMROM Nock.NockVMROM.Thm54
namespace Nock.Walk37

namespace Nock.NockVMROM.Thm54
namespace OptimizedStrictFullPackage
namespace Concrete

open scoped Polynomial
open Nock Nock.Framework Module
open Nock.Reified
open TemplateRawJointSoundness
open ConcreteStrictPackage
open OptimizedStrictPackage
open OptimizedStrictPackage.Concrete
open OptimizedComputeFinalTrace OptimizedComputeCollisionBound
open OptimizedComputeCanonicalSatisfaction
open OptimizedComputeFinalTypedLowering
open OptimizedComputeSemanticRealization
open OptimizedMemoryCanonicalSatisfaction
open OptimizedMemoryCanonicalSatisfaction.Concrete
open OptimizedComputeSubstitution

noncomputable section

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-! ### Shared by every F73 package (`BuildablePackage.Concrete.package73`,
`HonestCommitment.Concrete.package73'`, `GenericHonestPackage.Concrete.package73Of*`). -/

/-- The generator's reordered tree for `*[0 [1 2]]` has leaf bound exactly `2`. -/
theorem f73_leafIs :
    GeneratedField.LeafIs (K := K73cubic) 1 (.atom 0) (.cell (.atom 1) (.atom 2)) 2 := by
  gen_simp

/-- The guarded evaluator terminates on `*[0 [1 2]]`. -/
theorem f73_evalIsSome :
    (FieldEmbedding.evalGBy (ringChar K73cubic) 1 (.atom 0) (.cell (.atom 1) (.atom 2))).isSome := by
  eval_simp

/-- Program-level `generated` for the F73 program at any window `Λ ≥ 2`. -/
theorem f73_program_generated (Λ : ℕ) (hΛ : 2 ≤ Λ) :
    ∃ (gfuel : ℕ) (G : Nock.Walk.NTree (TraceGen.GenComputeRow K73cubic)) (R : Noun) (fuel : ℕ)
      (r : Noun),
      TraceGen.genComputeSkeleton (K := K73cubic) gfuel (.atom 0) (.cell (.atom 1) (.atom 2)) =
          .ok (G, R) ∧
        FieldEmbedding.evalGBy (ringChar K73cubic) fuel (.atom 0) (.cell (.atom 1) (.atom 2)) =
          some r ∧
        TraceGen.programLeafBound (TraceGen.airReorder G) ≤ Λ :=
  GeneratedField.generated_of _ _ _ _ 1 1 (GeneratedField.le_of_leafIs f73_leafIs hΛ) f73_evalIsSome

/-- Negative control: the F73 window has zero margin (`Λ = 1` is refuted). -/
theorem f73_leaf_margin_zero :
    ¬ ∃ (G : Nock.Walk.NTree (TraceGen.GenComputeRow K73cubic)) (R : Noun),
      TraceGen.genComputeSkeleton (K := K73cubic) 1 (.atom 0) (.cell (.atom 1) (.atom 2)) =
          .ok (G, R) ∧
        TraceGen.programLeafBound (TraceGen.airReorder G) ≤ 1 := by
  rintro ⟨G, R, hx, hle⟩
  have h := f73_leafIs
  unfold GeneratedField.LeafIs at h
  rw [hx] at h
  simp only at h
  omega

/-- `primeField` at `F73 = ZMod 73`. -/
theorem f73_primeField : GeneratedField.PrimeFieldElems F73 := by
  haveI : Fact (Nat.Prime 73) := ⟨by norm_num⟩
  exact GeneratedField.primeFieldElems_zmod 73

def concreteOptimizedFullStrictPackage :
    OptimizedFullStrictNockVMROMPackage F73 K73cubic 2 where
  optimized := concreteOptimizedStrictPackage
  honestSeed := honestSeed
  honestSeed_ne := honestSeed_ne
  honestAlpha := honestAlpha
  honest_specialization :=
    verifier_specializedProblem honestSeed honestSeed_ne honestAlpha
  chained := honest_chained
  walkFamily := walkFamily
  walkFamily_problem := walkFamily_problem
  compEnc_inj := compEnc_inj
  memEnc_inj := memEnc_inj
  computeRowsAccepted := by
    change
      (specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault).exec.ComputeRowsAccepted
    rw [specializedProblem_eq]
    exact honest_computeRowsAccepted
  memoryRowsAccepted := by
    change
      (specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault).exec.MemoryRowsAccepted
    rw [specializedProblem_eq]
    exact honest_memoryRowsAccepted
  topologyBinding := topologyBinding
  recordEquations := recordEquations
  ioStrategy := ioStrategy
  io_requests := rfl
  io_responses := rfl
  q := 73
  stateTagChar := stateTagChar
  q_gt_one := by norm_num
  q_eq_ringChar := q_eq_ringChar
  skeletonBounded := skeletonBounded
  combinedBounded := combinedBounded
  KszBound := KszBound
  progCapacity := progCapacity
  memCapacity := memCapacity
  rowsBound := by
    rw [← ConcreteStrictPackage.q_eq_ringChar]
    exact ⟨by decide, by decide⟩
  generated := GeneratedField.claimGenerated_of_eq rfl rfl (f73_program_generated 2 le_rfl)
  primeField := f73_primeField

theorem concrete_full_statement
    (hbasis : FormRBasis basis73) :
    OptimizedFullStrictThm54Statement concreteOptimizedFullStrictPackage :=
  optimizedFullStrictNockVMROM_of_package concreteOptimizedFullStrictPackage
    Nock.RedTeam.Batch62.concreteFormRAxisBound hbasis
    Nock.RedTeam.Batch62.concreteFormRWidth

theorem concrete_full_nonvacuous
    (hbasis : FormRBasis basis73) :
    Nonempty (OptimizedFullStrictThm54Statement concreteOptimizedFullStrictPackage) :=
  ⟨concrete_full_statement hbasis⟩

theorem concrete_restored_clauses
    (hbasis : FormRBasis basis73) :
    Language
        (Tag F73 K73cubic
          concreteOptimizedFullStrictPackage.objects.cfg.challenges.α
          concreteOptimizedFullStrictPackage.objects.cfg.challenges.β
          concreteOptimizedFullStrictPackage.objects.cfg.Ksz)
        (stmtOfExact concreteOptimizedFullStrictPackage.objects.cfg
          concreteOptimizedFullStrictPackage.objects.exec) ∧
      IO.LIO concreteOptimizedFullStrictPackage.objects.cfg.Ksz
        concreteOptimizedFullStrictPackage.objects.reqRecs
        concreteOptimizedFullStrictPackage.objects.respRecs ∧
      (concreteOptimizedFullStrictPackage.computeWalkBadRatio ≤
          concreteOptimizedFullStrictPackage.computeWalkBound ∧
        concreteOptimizedFullStrictPackage.memoryWalkBadRatio ≤
          concreteOptimizedFullStrictPackage.memoryWalkBound) ∧
      (concreteOptimizedFullStrictPackage.computeChip.rap.H.card =
          concreteOptimizedFullStrictPackage.objects.cfg.compRows ∧
        concreteOptimizedFullStrictPackage.memoryChip.rap.H.card =
          RowLayout.memoryM concreteOptimizedFullStrictPackage.objects.exec +
            2 * RowLayout.memoryL concreteOptimizedFullStrictPackage.objects.exec) :=
  ⟨(concrete_full_statement hbasis).perfect_completeness,
    (concrete_full_statement hbasis).shared_io,
    (concrete_full_statement hbasis).walk_bounds,
    (concrete_full_statement hbasis).row_budgets⟩

theorem concrete_containment
    (hbasis : FormRBasis basis73) :
    ∀ (ω : JointCoins K73cubic) (lmb : K73cubic),
      concreteOptimizedFullStrictPackage.strategy.Accepts ω lmb →
      ω ∉ ProductionP8Containment.FailureUnion
        concreteOptimizedFullStrictPackage.strategy
        concreteOptimizedFullStrictPackage.optimized.census lmb →
      ProductionP8Containment.GenuineTargetAt
        concreteOptimizedFullStrictPackage.strategy 73
        concreteOptimizedFullStrictPackage.optimized.Λ ω lmb :=
  (concrete_full_statement hbasis).containment

theorem concrete_exact_optimized_resources
    (hbasis : FormRBasis basis73) :
    concreteOptimizedFullStrictPackage.OptimizedFullCostRealization :=
  (concrete_full_statement hbasis).exact_resources

theorem concrete_memory_axis_forest
    (hbasis : FormRBasis basis73) :
    concreteOptimizedFullStrictPackage.optimized.OptimizedSharedMemoryConnective :=
  (concrete_full_statement hbasis).shared_forest_axis

noncomputable def concreteComputeTrace :=
  correctedCanonicalFinalTrace
    concreteOptimizedFullStrictPackage.optimized.sampled
    concreteOptimizedFullStrictPackage.optimized.family.problem.cfg.compRows_pos
    concreteOptimizedFullStrictPackage.optimized.computeNodes
    concreteOptimizedFullStrictPackage.optimized.basis
    concreteOptimizedFullStrictPackage.optimized.computeChallenge
    concreteOptimizedFullStrictPackage.optimized.computePublic
    concreteOptimizedFullStrictPackage.optimized.orbit

noncomputable def concreteMemoryTrace :=
  OptimizedMemoryCanonicalSatisfaction.canonicalFinalMemoryTrace
    concreteOptimizedFullStrictPackage.optimized.sampled
    concreteOptimizedFullStrictPackage.optimized.memoryNodes
    concreteOptimizedFullStrictPackage.optimized.basis
    concreteOptimizedFullStrictPackage.optimized.memoryChallenge
    concreteOptimizedFullStrictPackage.optimized.memoryPublic
    concreteOptimizedFullStrictPackage.optimized.orbit

def concreteProductionChallenge :
    OptimizedProductionChallengeTuple K73cubic F73 :=
  let P := concreteOptimizedFullStrictPackage
  (honestCoins,
    ((P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole),
      (⟨P.objects.cfg.challenges.a, P.objects.cfg.challenges.b, P.objects.cfg.challenges.c⟩,
        ⟨P.packageInterPole, P.objects.cfg.challenges.lam⟩)))

theorem concrete_production_acceptance
    (hbasis : FormRBasis basis73)
    (hmore : ∀ i : Fin honestLegacyFamily.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < honestLegacyFamily.problem.cfg.kMem →
        (honestLegacyFamily.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (honestLegacyFamily.problem.exec.memoryPubAt i).pt.indicator = 0) :
    concreteOptimizedFullStrictPackage.OptimizedHistoricalAcceptanceAt
      concreteComputeTrace concreteMemoryTrace concreteProductionChallenge := by
  let P := concreteOptimizedFullStrictPackage
  refine
    { p8 := ?_
      same_problem := ?_
      sampled_io_coins := rfl
      memory_sampled_coins := P.memory_sampled_coins_of_io_coins concreteMemoryTrace _ rfl
      memory_intermediate_pole := P.memory_intermediate_pole_of_tuple concreteMemoryTrace _ rfl
      compute_satisfies := by
        simpa [concreteComputeTrace] using
          correctedCanonicalFinalTrace_satisfies
            P.optimized.sampled P.optimized.computeObligations
            P.optimized.family.problem.cfg.compRows_pos
            P.optimized.computeNodes P.optimized.computeNodes_injective
            P.optimized.basis P.optimized.computeChallenge P.optimized.computePublic
            P.optimized.orbit P.optimized.computeAdjacentOrbit
            P.optimized.computeChallengePins P.optimized.computePublicPins
            P.optimized.computeRequestsPins P.optimized.computeLineOrigin
            P.optimized.computeWalkOrder
            Nock.RedTeam.Batch62.concreteFormRAxisBound hbasis
            Nock.RedTeam.Batch62.concreteFormRWidth
      memory_satisfies := by
        have hC : P.optimized.family.problem.exec.CprimeCoherent :=
          OptimizedMemoryCanonicalSatisfaction.Concrete.honest_hC
        simpa [concreteMemoryTrace] using
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
            (MemoryHaltLeavesHonest.package_haltLeavesBase P) }
  · exact ConcreteStrictPackage.production_accepts_honestCoins
  · apply OptimizedFullStrictNockVMROMPackage.OptimizedSameProblemAt.of_objects P
      ConcreteStrictPackage.honestCoins P.objects.cfg.challenges.lam
      ConcreteStrictPackage.honestSeed_ne
    simpa [P, concreteOptimizedFullStrictPackage,
      ConcreteStrictPackage.honestCoins, nprSeed, alphaM] using
      P.honest_specialization

/-- The concrete memory challenge is outside the consumed all-row event
`extensionMemoryCollisionEvent`. -/
theorem concrete_memory_challenge_outside_failure :
    concreteProductionChallenge.2.2.2 ∉
      OptimizedMemoryCollisionAccounting.extensionMemoryCollisionEvent
        (concreteOptimizedFullStrictPackage.memorySourceEnv concreteMemoryTrace) := by
  simp [OptimizedMemoryCollisionAccounting.extensionMemoryCollisionEvent]

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
/-- The concrete compute challenge is outside the consumed two-lift event `extensionFinalComputeCollisionEvent`. -/
theorem concrete_compute_challenge_outside_failure :
    concreteProductionChallenge.2.2.1 ∉
      extensionFinalComputeCollisionEvent
        (concreteOptimizedFullStrictPackage.computeSourceEnv concreteComputeTrace)
        (concreteOptimizedFullStrictPackage.computeWalkEnv concreteComputeTrace) := by
  simp [extensionFinalComputeCollisionEvent]

#print axioms concreteOptimizedFullStrictPackage
#print axioms concrete_full_statement
#print axioms concrete_restored_clauses
#print axioms concrete_containment
#print axioms concrete_exact_optimized_resources
#print axioms concrete_memory_axis_forest
#print axioms concrete_production_acceptance
#print axioms concrete_memory_challenge_outside_failure
#print axioms concrete_compute_challenge_outside_failure

end
end Concrete
end OptimizedStrictFullPackage
end Nock.NockVMROM.Thm54

end Nock.Walk37
