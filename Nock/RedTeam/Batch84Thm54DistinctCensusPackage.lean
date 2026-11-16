import Nock.NockVMROM.Thm54.DistinctCensusCommitment
import Nock.NockVMROM.Thm54.BuildableAxisWitness
import Nock.NockVMROM.Thm54.MultiRootServedFixture
import Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
import Nock.NockVMROM.Thm54.MultiRootHonestArrays
import Nock.RedTeam.Batch83Thm54DistinctCensus
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# The distinct census carried to a constructed package

Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

The principal same-object check is package-relative: the `CombinedSkeletonCensus`
stored in `(packageD hfirstD).optimized.census` is the census of the committed skeleton
stored in `(packageD hfirstD).strategy.skeleton`, and that skeleton is the one whose
three compute rows and twenty-one-row memory forest specialize to `execD`.

The all-zero later-round message is also classified exactly.  It is an honest
constructor input, but its zero response multiplicities violate a mandatory raw
verifier gate.  Thus `packageD` accepts no coin, all optimized acceptance sets
are empty, and the six acceptance/security fields of `statementD` have no
acceptance witness at this fixture.  The other seven first-order fields remain
substantive; `structural` remains the dependent type-level summary.  The
`9 + 1 + 4` accounting remains the authoritative accounting at `packageP`, not
a claim about this zero-message package.
-/

set_option autoImplicit false

namespace Nock.RedTeam.Batch84

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Noun Nock.Walk Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.EqualityOperandCensus
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
open Nock.NockVMROM.Thm54.MultiRootHonestArrays
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
include hfirstD

/-! ## A. Same-object census provenance at the consumed package -/

/-- The package, its production strategy, its commitment residual, and its
`HonestCommitment.Data` all carry the same committed skeleton and census. -/
theorem package_census_is_the_committed_census :
    (packageD hfirstD).optimized.commitment.skeleton = skelD ∧
      (packageD hfirstD).strategy.skeleton = skelD ∧
      (packageD hfirstD).optimized.census = censusD ∧
      (residualD hfirstD).census = censusD ∧
      (dataD hfirstD).census = censusD ∧
      EdgeComparisonCensus.combinedSkeletonPairs K97cubic
        (packageD hfirstD).strategy.skeleton = op5Pairs :=
  ⟨rfl, rfl, rfl, rfl, rfl, combinedPairsD⟩

/-- The actual census consumed by `statementD` contains the exceptional pair,
and the two displayed operands are genuinely distinct. -/
theorem consumed_package_census_has_genuine_distinct_pair :
    ∃ i : Fin (packageD hfirstD).optimized.census.census.count,
      (packageD hfirstD).optimized.census.census.pair i =
          (operandLeft, operandRight) ∧
        ((packageD hfirstD).optimized.census.census.pair i).1 ≠
          ((packageD hfirstD).optimized.census.census.pair i).2 := by
  change ∃ i : Fin censusD.census.count,
    censusD.census.pair i = (operandLeft, operandRight) ∧
      (censusD.census.pair i).1 ≠ (censusD.census.pair i).2
  exact censusD_has_distinct_pair

/-- Negative control: the consumed package census is not the old fourteen-entry
self-comparison census.  It has the twenty-four production occurrences. -/
theorem consumed_census_is_not_the_released_fixture_census
    (hmoreM : LaterSeedZeros (F := F97) (K := K97cubic) multiRootExecution)
    (hrootAtP : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    (packageD hfirstD).optimized.census.census.count = 24 ∧
      censusM.census.count = 14 ∧
      (packageD hfirstD).optimized.census.census.count ≠ censusM.census.count := by
  have hD : (packageD hfirstD).optimized.census.census.count = 24 := by
    change
      (EdgeComparisonCensus.combinedSkeletonPairs K97cubic skelD).length = 24
    rw [combinedPairsD, op5Pairs_length]
  have hM : censusM.census.count = 14 :=
    Nock.RedTeam.Batch82.censusM_count_is_fourteen hmoreM hrootAtP
  refine ⟨hD, hM, ?_⟩
  rw [hD, hM]
  norm_num

/-- The package-level collision event is nonempty on its genuine distinct
occurrence.  This is a census fact, not an accepted-transcript claim. -/
theorem consumed_package_collision_event_nonempty :
    (collisionFailureEvent (K := K97cubic)
      (packageD hfirstD).optimized.census.census).Nonempty := by
  obtain ⟨i, hi, _⟩ := consumed_package_census_has_genuine_distinct_pair hfirstD
  refine ⟨((0, 0), (0, -1)), ?_⟩
  rw [mem_collisionFailureEvent_iff]
  exact ⟨i, by rw [hi]; exact operands_not_sepSeed_at_neg_one⟩

/-! ## B. The twenty-one-row forest services the four committed records -/

def rootIndexD : Fin cfgD.kMem := ⟨0, by norm_num [cfgD]⟩

/-- The package threads the exact execution, and the exact execution's compute
requests, memory responses, and service records are the same four NMR records.
Thus the forest is not merely `RVT`-accepted. -/
theorem forest_services_the_four_committed_records :
    (packageD hfirstD).objects.cfg = cfgD ∧
      (packageD hfirstD).objects.exec = execD ∧
      (packageD hfirstD).objects.exec.memoryRows.length = 21 ∧
      (packageD hfirstD).objects.exec.rawRequests = [recF, recT, recL, recR] ∧
      ServedMemoryTrace.rootResponseRecords (distinctCensusExecution hfirstD).execA rootIndexD =
        [recF, recT, recL, recR] ∧
      ((distinctCensusExecution hfirstD).memoryTrace.roots rootIndexD).services.map
          (fun s => s.record) = [recF, recT, recL, recR] ∧
      (packageD hfirstD).optimized.memoryProduction =
        BuildableAxisWitness.buildableMemoryProductionAssignment
          (distinctCensusExecution hfirstD) (inputsD hfirstD)
          (BuildableAxisWitness.hmore_of_kMem_le_one
            (distinctCensusExecution hfirstD) (by change 1 ≤ 1; trivial)) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl⟩
  · change execD.memoryRows.length = 21
    rw [execution_rowsD.2]
    rfl
  · exact rawRequestsD
  · exact rootResponseRecordsD
  · change (rootTracesD rootIndexD).services.map (fun s => s.record) =
      [recF, recT, recL, recR]
    rw [show rootTracesD rootIndexD = rootTraceD from rfl]
    rfl

/-! ## C. Fixture parameters are separated rather than conflated -/

/-- The former therefore does not trivialize the latter. -/
theorem compiler_fold_is_not_the_op5_table_rlc :
    (inputsD hfirstD).computeChallenges = default ∧
      cfgD.challenges.a = 0 ∧ cfgD.challenges.b = 0 ∧
      cfgD.challenges.c = 1 ∧ cfgD.challenges.c ≠ 0 :=
  ⟨rfl, rfl, rfl, rfl, one_ne_zero⟩

/-- Orbit height five is capacity-driven: sixteen rows are too few for the
twenty-one-row forest, while thirty-two suffice. -/
theorem orbit_height_five_is_capacity_driven :
    (inputsD hfirstD).hOrb = 5 ∧ cfgD.memRows = 21 ∧
      2 ^ 4 < cfgD.memRows ∧ cfgD.memRows ≤ 2 ^ (inputsD hfirstD).hOrb :=
  ⟨rfl, rfl, by norm_num [cfgD], by
    have horb : (inputsD hfirstD).hOrb = 5 := rfl
    rw [horb]
    norm_num [cfgD]⟩

/-! ## D. The zero later-round message makes acceptance empty -/

/-- Exact receipt that `residualD` is the all-zero post-challenge message of -/
theorem residualD_arrays_are_zero :
    residualD hfirstD =
      HonestCommitment.commitmentResidualOf (dataD hfirstD)
        (fun z hz α lmb =>
          HonestCommitment.zeroAlphaM (dataD hfirstD).timestampStrategy z hz α lmb)
        (fun _ _ _ => HonestCommitment.zeroWalk) :=
  rfl

/-- The all-zero response multiplicities violate the mandatory nonzero
multiplicity gate, so no joint coin is accepted. -/
theorem packageD_accepts_none (ω : JointCoins K97cubic) (lmb : K97cubic) :
    ¬ (packageD hfirstD).strategy.Accepts ω lmb := by
  intro hacc
  by_cases hz : nprSeed ω = 0
  · simp [ProductionStrategy.Accepts, hz] at hacc
  · have hp :
        ProductionAxisStructureAccepts (packageD hfirstD).strategy.verifier ω lmb ∧
          (packageD hfirstD).strategy.RootAxisBoundaryAt (nprSeed ω) hz (alphaM ω) := by
      simpa [ProductionStrategy.Accepts, hz] using hacc
    have hprod : ProductionAxisStructureAccepts (packageD hfirstD).strategy.verifier ω lmb := hp.1
    have hchecks :=
      ((ProductionAxisStructureVerifier.accepts_iff
        (packageD hfirstD).strategy.verifier ω lmb hz).1 hprod).1
    have hgates := hchecks.1
    unfold RawMessage.VerifierGates at hgates
    rcases hgates with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hmult, _, _, _, _⟩
    have hlen :
        ((packageD hfirstD).strategy.verifier.raw.familyAt ω lmb hz).exec.derivedResponseIO.length = 4 := by
      change (((dataD hfirstD).executionTemplate (nprSeed ω)).specialize
        (alphaM ω) lmb).derivedResponseIO.length = 4
      rw [derivedResponseIO_length_eq
        ((dataD hfirstD).binds (nprSeed ω) (alphaM ω) lmb) (dataD hfirstD).honest_binds]
      change execD.derivedResponseIO.length = 4
      rw [derived_responsesD]
      rfl
    let j : Fin
        ((packageD hfirstD).strategy.verifier.raw.familyAt ω lmb hz).exec.derivedResponseIO.length :=
      ⟨0, by rw [hlen]; decide⟩
    have hne := hmult j
    exact hne rfl

theorem packageD_falseAcceptance_empty :
    FalseAcceptanceSet (packageD hfirstD).strategy 97 7 cfgD.challenges.lam = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro ω hω
  rw [mem_falseAcceptanceSet_iff] at hω
  exact packageD_accepts_none hfirstD ω cfgD.challenges.lam hω.1

theorem packageD_optimized_accepts_none
    (Qc : Fin (packageD hfirstD).computeChip.rap.w → F97[X])
    (Qm : Fin (packageD hfirstD).memoryChip.rap.w → F97[X])
    (c : OptimizedProductionChallengeTuple K97cubic F97) :
    ¬ (packageD hfirstD).OptimizedHistoricalAcceptanceAt Qc Qm c :=
  fun h => packageD_accepts_none hfirstD c.1 c.2.2.2.lambda h.p8


/-- `statementD` is inhabited, but this is not an acceptance witness. -/
theorem statementD_nonvacuous_but_acceptance_empty
    (haxD : FormRAxisBound (packageD hfirstD).optimized.sampled
      (packageD hfirstD).optimized.basis)
    (hbasisD : FormRBasis (packageD hfirstD).optimized.basis)
    (hwidthD : FormRWidth F97) :
    Nonempty (OptimizedFullStrictThm54Statement (packageD hfirstD)) ∧
      (¬ ∃ (ω : JointCoins K97cubic) (lmb : K97cubic), (packageD hfirstD).strategy.Accepts ω lmb) ∧
      (∀ (Qc : Fin (packageD hfirstD).computeChip.rap.w → F97[X])
        (Qm : Fin (packageD hfirstD).memoryChip.rap.w → F97[X]),
        ¬ ∃ c : OptimizedProductionChallengeTuple K97cubic F97,
          (packageD hfirstD).OptimizedHistoricalAcceptanceAt Qc Qm c) := by
  refine ⟨⟨statementD hfirstD haxD hbasisD hwidthD⟩, ?_, ?_⟩
  · rintro ⟨ω, lmb, hω⟩
    exact packageD_accepts_none hfirstD ω lmb hω
  · intro Qc Qm
    rintro ⟨c, hc⟩
    exact packageD_optimized_accepts_none hfirstD Qc Qm c hc

/-! ## E. Statement shape and package-relative accounting -/

/-- Seven non-acceptance-facing fields remain directly inhabited, while both
false-acceptance sets are empty.  This is the exact `7 + 1 + 6` scope of the
zero-message package. -/
theorem statementD_exact_scope
    (haxD : FormRAxisBound (packageD hfirstD).optimized.sampled
      (packageD hfirstD).optimized.basis)
    (hbasisD : FormRBasis (packageD hfirstD).optimized.basis)
    (hwidthD : FormRWidth F97) :
    OptimizedComputeRealizationAt (packageD hfirstD).optimized.sampled
        (packageD hfirstD).optimized.computeObligations (packageD hfirstD).optimized.computeNodes
        (packageD hfirstD).optimized.basis (packageD hfirstD).optimized.computeChallenge
        (packageD hfirstD).optimized.computePublic (packageD hfirstD).optimized.orbit ∧
      OptimizedMemoryRealizationAt (packageD hfirstD).optimized.sampled
        (packageD hfirstD).optimized.memoryProduction (packageD hfirstD).optimized.memoryNodes
        (packageD hfirstD).optimized.basis (packageD hfirstD).optimized.memoryChallenge
        (packageD hfirstD).optimized.memoryPublic (packageD hfirstD).optimized.orbit ∧
      IO.LIO (packageD hfirstD).objects.cfg.Ksz (packageD hfirstD).objects.reqRecs
        (packageD hfirstD).objects.respRecs ∧
      Language
        (Tag F97 K97cubic (packageD hfirstD).objects.cfg.challenges.α
          (packageD hfirstD).objects.cfg.challenges.β (packageD hfirstD).objects.cfg.Ksz)
        (stmtOfExact (packageD hfirstD).objects.cfg (packageD hfirstD).objects.exec) ∧
      (packageD hfirstD).computeWalkBadRatio ≤ (packageD hfirstD).computeWalkBound ∧
      (packageD hfirstD).memoryWalkBadRatio ≤ (packageD hfirstD).memoryWalkBound ∧
      (packageD hfirstD).OptimizedFullCostRealization ∧
      (packageD hfirstD).computeChip.rap.H.card = (packageD hfirstD).objects.cfg.compRows ∧
      (packageD hfirstD).memoryChip.rap.H.card =
        RowLayout.memoryM (packageD hfirstD).objects.exec +
          2 * RowLayout.memoryL (packageD hfirstD).objects.exec ∧
      (packageD hfirstD).optimized.OptimizedSharedMemoryConnective ∧
      FalseAcceptanceSet (packageD hfirstD).strategy 97 7 cfgD.challenges.lam = ∅ :=
  ⟨(statementD hfirstD haxD hbasisD hwidthD).optimized_chips.1, (statementD hfirstD haxD hbasisD hwidthD).optimized_chips.2,
    (statementD hfirstD haxD hbasisD hwidthD).shared_io, (statementD hfirstD haxD hbasisD hwidthD).perfect_completeness,
    (statementD hfirstD haxD hbasisD hwidthD).walk_bounds.1, (statementD hfirstD haxD hbasisD hwidthD).walk_bounds.2,
    (statementD hfirstD haxD hbasisD hwidthD).exact_resources, (statementD hfirstD haxD hbasisD hwidthD).row_budgets.1,
    (statementD hfirstD haxD hbasisD hwidthD).row_budgets.2, (statementD hfirstD haxD hbasisD hwidthD).shared_forest_axis,
    packageD_falseAcceptance_empty hfirstD⟩

/-- Exact eta receipt: no field was moved or dropped when `statementD` was
inhabited. -/
theorem statementD_fourteen_field_eta
    (haxD : FormRAxisBound (packageD hfirstD).optimized.sampled
      (packageD hfirstD).optimized.basis)
    (hbasisD : FormRBasis (packageD hfirstD).optimized.basis)
    (hwidthD : FormRWidth F97) :
    statementD hfirstD haxD hbasisD hwidthD =
      { structural := (statementD hfirstD haxD hbasisD hwidthD).structural
        optimized_chips := (statementD hfirstD haxD hbasisD hwidthD).optimized_chips
        shared_io := (statementD hfirstD haxD hbasisD hwidthD).shared_io
        perfect_completeness := (statementD hfirstD haxD hbasisD hwidthD).perfect_completeness
        containment := (statementD hfirstD haxD hbasisD hwidthD).containment
        walk_bounds := (statementD hfirstD haxD hbasisD hwidthD).walk_bounds
        p8_fixed_field_soundness := (statementD hfirstD haxD hbasisD hwidthD).p8_fixed_field_soundness
        p8_fixed_field_bits := (statementD hfirstD haxD hbasisD hwidthD).p8_fixed_field_bits
        acceptance_to_target := (statementD hfirstD haxD hbasisD hwidthD).acceptance_to_target
        complete_false_acceptance_bound :=
          (statementD hfirstD haxD hbasisD hwidthD).complete_false_acceptance_bound
        complete_false_acceptance_bits :=
          (statementD hfirstD haxD hbasisD hwidthD).complete_false_acceptance_bits
        staged_false_acceptance_bound :=
          (statementD hfirstD haxD hbasisD hwidthD).staged_false_acceptance_bound
        exact_resources := (statementD hfirstD haxD hbasisD hwidthD).exact_resources
        row_budgets := (statementD hfirstD haxD hbasisD hwidthD).row_budgets
        shared_forest_axis := (statementD hfirstD haxD hbasisD hwidthD).shared_forest_axis } := by
  cases statementD hfirstD haxD hbasisD hwidthD
  rfl

/-- Accounting is package-relative. -/
theorem package_relative_accounting
    (hmoreM : LaterSeedZeros (F := F97) (K := K97cubic) multiRootExecution)
    (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
      (packageP hmoreM).optimized.basis)
    (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
    (hwidthP : FormRWidth F97)
    (haxD : FormRAxisBound (packageD hfirstD).optimized.sampled
      (packageD hfirstD).optimized.basis)
    (hbasisD : FormRBasis (packageD hfirstD).optimized.basis)
    (hwidthD : FormRWidth F97) :
    (9 + 1 + 4 = 14) ∧
      Nonempty (OptimizedFullStrictThm54Statement (packageP hmoreM)) ∧
      (7 + 1 + 6 = 14) ∧
      Nonempty (OptimizedFullStrictThm54Statement (packageD hfirstD)) ∧
      (∀ (ω : JointCoins K97cubic) (lmb : K97cubic), ¬ (packageD hfirstD).strategy.Accepts ω lmb) :=
  ⟨by norm_num, ⟨statementP hmoreM haxP hbasisP hwidthP⟩, by norm_num, ⟨statementD hfirstD haxD hbasisD hwidthD⟩,
    packageD_accepts_none hfirstD⟩

/-! ## F. -/

omit hfirstD in
theorem released_aliases_and_control_unchanged
    (hmoreM : LaterSeedZeros (F := F97) (K := K97cubic) multiRootExecution)
    (hrootAtP : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package ∧
      @«Thm:NockVMROM:forest-control» =
        @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch83.released_aliases_and_control_unchanged hmoreM hrootAtP

#print axioms package_census_is_the_committed_census
#print axioms consumed_package_census_has_genuine_distinct_pair
#print axioms consumed_census_is_not_the_released_fixture_census
#print axioms consumed_package_collision_event_nonempty
#print axioms forest_services_the_four_committed_records
#print axioms compiler_fold_is_not_the_op5_table_rlc
#print axioms orbit_height_five_is_capacity_driven
#print axioms residualD_arrays_are_zero
#print axioms packageD_accepts_none
#print axioms packageD_falseAcceptance_empty
#print axioms packageD_optimized_accepts_none
#print axioms statementD_nonvacuous_but_acceptance_empty
#print axioms statementD_exact_scope
#print axioms statementD_fourteen_field_eta
#print axioms package_relative_accounting
#print axioms released_aliases_and_control_unchanged

#print axioms DistinctCensusExecution.distinctCensusExecution
#print axioms DistinctCensusExecution.servedMemoryTraceD
#print axioms DistinctCensusCommitment.dataD
#print axioms DistinctCensusCommitment.combinedPairsD
#print axioms DistinctCensusCommitment.residualD
#print axioms DistinctCensusCommitment.inputsD
#print axioms DistinctCensusCommitment.packageD
#print axioms DistinctCensusCommitment.statementD
#print axioms DistinctCensusCommitment.residualD_has_distinct_pair

#print axioms «Thm:IO_result»
#print axioms «Thm:Walk_IOP»
#print axioms «Corr:forest»
#print axioms «Thm:deterministic_Trace»
#print axioms «Lem:NPR_decomp»
#print axioms «Thm:Noun_Validation»
#print axioms «Thm:comp_38»
#print axioms «Thm:mem_38»
#print axioms «Thm:NockVMROM»
#print axioms «Lem:equiv_compute»
#print axioms «Lem:equiv_mem»
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVM.V_NockVMROM_forest

end
end Nock.RedTeam.Batch84
