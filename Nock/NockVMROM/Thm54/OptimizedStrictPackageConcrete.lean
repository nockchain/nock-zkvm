import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.RedTeam.Batch62Thm54CanonicalComputeSatisfaction

/-!
# Concrete optimized strict package
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedStrictPackage
namespace Concrete

open Nock Nock.Framework Module
open ConcreteStrictPackage
open TemplateRawJointSoundness
open OptimizedComputeFinalTrace
open OptimizedComputeCanonicalSatisfaction
open OptimizedComputeCorrectedFinal
open OptimizedComputeCollisionBound
open OptimizedMemoryCollisionAccounting
open OptimizedComputeSampledTrace.Concrete
open OptimizedMemorySameExecution.Concrete
open OptimizedMemoryCanonicalSatisfaction
open OptimizedMemoryCanonicalSatisfaction.Concrete

noncomputable section

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

theorem concrete_two_ne_zero : (2 : K73cubic) ≠ 0 := by
  intro hk
  have htwoBase : (2 : F73) ≠ 0 := by decide
  apply htwoBase
  apply (algebraMap F73 K73cubic).injective
  simpa only [map_ofNat, map_zero] using hk

noncomputable def concreteOptimizedStrictPackage :
    OptimizedStrictNockVMROMPackage F73 K73cubic 2 where
  objects := ConcreteStrictPackage.objects
  verifier := ConcreteStrictPackage.verifier
  commitment := ConcreteStrictPackage.commitment
  claim_eq := rfl
  scan := fun z hz α lmb =>
    RawSemanticAssembly.activeFingerprintChecksAt_of_bindsAt (bindsAt_specialized z hz α lmb)
  shapeMatch := fun z hz α lmb =>
    RawSemanticAssembly.execTreeShapeMatchesAt_of_bindsAt (bindsAt_specialized z hz α lmb)
  rowFrame := fun z hz α lmb =>
    RawSemanticAssembly.rowFrameChecksAt_of_bindsAt (bindsAt_specialized z hz α lmb)
  slotSemantics := ConcreteStrictPackage.slotSemantics
  recordCountBalance := ConcreteStrictPackage.recordCountBalance
  Λ := 2
  census := ConcreteStrictPackage.census
  sizeWindowBound := ConcreteStrictPackage.sizeWindowBound
  family := honestLegacyFamily
  family_cfg := by
    change (specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault).cfg =
      cfg honestSeed honestAlpha
    rw [specializedProblem_eq]
  family_exec := by
    change HEq (specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault).exec
      (exec honestSeed honestAlpha)
    rw [specializedProblem_eq]
  sampled := honestSampled
  computeObligations := honest_obligations
  memoryExecA := honestExecA
  memoryProduction := honestProduction
  basis := basis73
  orbit := strictOrbit
  computeNodes := Nock.RedTeam.Batch62.concreteNodes
  computeNodes_injective := Nock.RedTeam.Batch62.concreteNodes_injective
  computeAdjacentOrbit := Nock.RedTeam.Batch62.concrete_orbit_step_vacuous
  computeChallenge := Nock.RedTeam.Batch62.concreteChallengeCoordinates
  computePublic := Nock.RedTeam.Batch62.concretePublicCoordinates
  computeChallengePins := Nock.RedTeam.Batch62.concreteChallengeCoordinates_exact
  computePublicPins := Nock.RedTeam.Batch62.concretePublicCoordinates_exact
  computeRequestsPins := Nock.RedTeam.Batch62.concreteRequests_exact
  computeLineOrigin := Nock.RedTeam.Batch62.concreteLineOrigin
  computeWalkOrder := fun h => by
    have : honestLegacyFamily.problem.cfg.compRows = 1 := rfl
    omega
  memoryNodes := honestMemoryNodes
  memoryNodes_injective := honestMemoryNodes_injective
  memoryChallenge := honestMemoryChalVal
  memoryPublic := honestMemoryPubVal
  memoryCoordinatePins := honestMemoryPins
  memoryOrbitAligned := honestMemoryNodes_aligned
  memoryDenominatorsSafe := honestMemoryDenominatorsSafe
  two_ne_zero := concrete_two_ne_zero
  pairedRecordLayout := honest_pairedRecordLayout
  memoryWalkOrder := honest_memory_walk_order

theorem concrete_nonvacuous :
    Nonempty (OptimizedStrictNockVMROMPackage F73 K73cubic 2) :=
  ⟨concreteOptimizedStrictPackage⟩

theorem concrete_source_and_final_satisfaction
    (hbasis : FormRBasis basis73)
    (hmore : ∀ i : Fin honestLegacyFamily.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < honestLegacyFamily.problem.cfg.kMem →
        (honestLegacyFamily.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (honestLegacyFamily.problem.exec.memoryPubAt i).pt.indicator = 0) :
    RAP.SatisfiesWithPreprocessing
        (ProductionNamedComputeRAP honestLegacyFamily.problem.cfg.compRows_pos
          Nock.RedTeam.Batch62.concreteNodes basis73
          Nock.RedTeam.Batch62.concreteChallengeCoordinates
          Nock.RedTeam.Batch62.concretePublicCoordinates strictOrbit)
        (OptimizedComputeFinalTrace.correctedCanonicalFinalTrace
          OptimizedComputeSampledTrace.Concrete.honestSampled
          honestLegacyFamily.problem.cfg.compRows_pos
          Nock.RedTeam.Batch62.concreteNodes basis73
          Nock.RedTeam.Batch62.concreteChallengeCoordinates
          Nock.RedTeam.Batch62.concretePublicCoordinates strictOrbit) ∧
      RAP.SatisfiesWithPreprocessing
        (OptimizedMemoryRAP.namedFinalMemoryRAP
          honestLegacyFamily.problem.cfg.memRows_pos honestMemoryNodes
          basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
          honestLegacyFamily.problem.cfg.kMem)
        (canonicalFinalMemoryTrace
          OptimizedComputeSampledTrace.Concrete.honestSampled
          honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal
          strictOrbit) :=
  ⟨Nock.RedTeam.Batch62.concrete_correctedCanonicalFinalTrace_satisfies hbasis,
    honest_final_memory_satisfies hmore⟩

theorem concrete_exact_resources :
    let P := concreteOptimizedStrictPackage
    let C := ProductionNamedComputeRAP P.family.problem.cfg.compRows_pos P.computeNodes
      P.basis P.computeChallenge P.computePublic P.orbit
    let M := OptimizedMemoryRAP.namedFinalMemoryRAP P.family.problem.cfg.memRows_pos P.memoryNodes
      P.basis P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem
    C.rap.w = 303 ∧ C.rap.s = 418 ∧ C.rap.d = 4 ∧ C.rap.k = 2 ∧
      M.rap.w = 205 ∧ M.rap.s = 156 ∧ M.rap.d = 4 ∧ M.rap.k = 1 :=
  concreteOptimizedStrictPackage.exact_chip_resources

theorem concrete_strict_capstone
    (hbasis : FormRBasis basis73) :
    OptimizedStrictThm54Statement concreteOptimizedStrictPackage :=
  optimizedStrictNockVMROM_of_package concreteOptimizedStrictPackage
    Nock.RedTeam.Batch62.concreteFormRAxisBound hbasis
    Nock.RedTeam.Batch62.concreteFormRWidth

/-- The corrected compute collision-good premise has a concrete complement witness for every
single-row environment used by this package. -/
theorem concrete_compute_good_complement
    (envK : Fin 1 → Nock.Reified.Env K73cubic)
    (walkEnv : Nock.Reified.Env K73cubic) :
    ∃ c : FinalComputeChallengeTuple K73cubic,
      c ∉ extensionFinalComputeCollisionEvent envK walkEnv :=
  OptimizedComputeCollisionConcrete.concrete_exists_good_challenge_tuple envK walkEnv

/-- The consumed `19·M` all-row fold union is non-vacuous for the concrete five-row memory
execution.  It was stated over the five-lift `61/14` union until stage 3d; the
four base-field coordinates it also quantified over are gone from `MemoryChallengeTuple`. -/
theorem concrete_memory_good_complement
    (envK : Fin 5 → Nock.Reified.Env K73cubic) :
    ∃ c : MemoryChallengeTuple K73cubic,
      ExtensionMemoryCollisionGood envK c := by
  apply exists_extensionMemoryCollisionGood_of_bound_lt
  rw [OptimizedComputeCollisionConcrete.concrete_field_cards.2]
  norm_num

/-- Direct malformed controls inherited by the concrete optimized realization surface. -/
def concrete_compute_malformed_rejection :=
  Nock.RedTeam.Batch62.malformed_terminal_current_table_value_rejected

def concrete_memory_malformed_rejection :=
  honest_direct_malformed_production_census

#print axioms concreteOptimizedStrictPackage
#print axioms concrete_nonvacuous
#print axioms concrete_source_and_final_satisfaction
#print axioms concrete_exact_resources
#print axioms concrete_strict_capstone
#print axioms concrete_compute_good_complement
#print axioms concrete_memory_good_complement
#print axioms concrete_compute_malformed_rejection
#print axioms concrete_memory_malformed_rejection

end
end Concrete
end OptimizedStrictPackage
end Nock.NockVMROM.Thm54
