import Nock.NockVMROM.Thm54.DistinctCensusP8FixedField
import Nock.NockVMROM.Thm54.WalkTilingEvents
import Nock.RedTeam.Batch88Thm54CompilerFoldCorrespondence

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!

Paper frame:
the paper.

Consumed Lean objects:
`DistinctCensusFold2.packageR`,
`ProductionP8Containment.FalseAcceptanceSet`,
`OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageR hfirstD)`, and
`optimizedFullStrictNockVMROM_of_package (packageR hfirstD) hax hbasis hwidth`.

Result: FINDING.  The two P8 fields use exactly the same false-acceptance set,
the size-window and collision localizations are correct, and the optimized
same-problem record pins both committed coordinates.  But production
acceptance also pins the complete fibre: `alphaM = 4` follows from the
memory-walk initial-line gate, and `nprSeed = 8` follows because the same
committed OP_5 `invGen` witness satisfies the unequal-operand RLC equation at
the sampled seed and at the honest seed.  Therefore the production
false-acceptance set is empty and the prover's “unclassified” stop is
under-closed.  This is a fixture-level Lean accounting finding, not a mismatch
with the paper's probabilistic P8 construction.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch89

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Walk Framework Framework.Reify Framework.Thm54
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.EqualityOperandCensus
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment
open Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
open Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
open Nock.NockVMROM.Thm54.DistinctCensusFold2
open Nock.NockVMROM.Thm54.DistinctCensusP8FixedField
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97b89 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97b89 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
include hfirstD
variable (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
variable (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
variable (hwidthR : FormRWidth F97)
include haxR hbasisR hwidthR
variable (hrootAt : ∀ a g : K97cubic,
  (packageR hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
include hrootAt
variable (hrootAtQ : ∀ a g : K97cubic,
  (packageQ hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
include hrootAtQ

/-! ## A. The two fields use one exact event -/

abbrev falseAcceptanceR : Finset (JointCoins K97cubic) :=
  FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam

/-- Both statement fields have literally the same probability term on the same
`FalseAcceptanceSet`; the bit field adds only the support arithmetic
. -/
theorem p8_fields_share_the_exact_false_acceptance_set :
    falseAcceptanceR hfirstD =
        FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam ∧
      |(jointProbability (falseAcceptanceR hfirstD))| ≤
        (workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
            (fixedTopologyWorkload (packageR hfirstD).strategy)
            (fixedAxisWorkload (packageR hfirstD).strategy) : ℝ) /
          (Fintype.card K97cubic : ℝ) ∧
      ∀ b : ℕ,
        workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
            (fixedTopologyWorkload (packageR hfirstD).strategy)
            (fixedAxisWorkload (packageR hfirstD).strategy) * 2 ^ b ≤
          Fintype.card K97cubic →
        |(jointProbability (falseAcceptanceR hfirstD))| ≤ 1 / 2 ^ b :=
  ⟨rfl, (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_soundness cfgD.challenges.lam, fun b hs => (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_bits cfgD.challenges.lam b hs⟩

/-- Negative-control formulation: once the ordinary bound and support
inequality are supplied, the bit bound is pure ordered-field arithmetic.  It
does not introduce a second acceptance event. -/
theorem p8_bits_are_derived_from_the_same_event
    (b : ℕ)
    (hsound :
      |(jointProbability (falseAcceptanceR hfirstD))| ≤
        (workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
            (fixedTopologyWorkload (packageR hfirstD).strategy)
            (fixedAxisWorkload (packageR hfirstD).strategy) : ℝ) /
          (Fintype.card K97cubic : ℝ))
    (hsupport :
      workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
          (fixedTopologyWorkload (packageR hfirstD).strategy)
          (fixedAxisWorkload (packageR hfirstD).strategy) * 2 ^ b ≤
        Fintype.card K97cubic) :
    |(jointProbability (falseAcceptanceR hfirstD))| ≤ 1 / 2 ^ b := by
  have hcard : (0 : ℝ) < (Fintype.card K97cubic : ℝ) := by positivity
  have hpow : (0 : ℝ) < 2 ^ b := by positivity
  have hreal :
      (workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
          (fixedTopologyWorkload (packageR hfirstD).strategy)
          (fixedAxisWorkload (packageR hfirstD).strategy) : ℝ) * 2 ^ b ≤
        (Fintype.card K97cubic : ℝ) := by
    exact_mod_cast hsupport
  apply hsound.trans
  rw [div_le_div_iff₀ hcard hpow]
  linarith

/-! ## B. Size windows inspect exactly OP_3/4/6 -/

/-- `requiredSizeWindowNouns` does inspect opcode state; it is nonempty exactly
for OP_3, OP_4, and OP_6.  Thus package-R emptiness comes from this skeleton
having none of those rows, not from an event predicate that ignores them
. -/
theorem required_size_windows_exactly_s3_s4_s6
    (s : ComputeRowSkeleton) :
    requiredSizeWindowNouns s ≠ [] ↔
      s.state = .s3 ∨ s.state = .s4 ∨ s.state = .s6 := by
  cases h : s.state <;> simp [requiredSizeWindowNouns, h]

/-- Independent replay on the consumed skeleton. -/
theorem consumed_size_window_event_is_empty :
    SizeWindowFailure (K := K97cubic) (packageR hfirstD).strategy.skeleton = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro ω hω
  rw [mem_SizeWindowFailure_iff] at hω
  obtain ⟨_, n, hn, _⟩ := hω
  rw [packageR_skeleton hfirstD hrootAt hrootAtQ, sizeWindowNounsD hfirstD] at hn
  exact List.not_mem_nil hn

/-! ## C. The consumed census contains the paper NPR collision object -/

/-- The exact consumed package census, exact unequal nouns, and exact bad-seed
event inhabitant are threaded in one statement.  The final two equalities are
the NPR fingerprint collision of `Lem:ion_univariate_sec`, not a renamed
cardinality bound. -/
theorem consumed_op5_pair_is_the_npr_collision_object :
    (∃ i : Fin (packageR hfirstD).optimized.census.census.count,
      (packageR hfirstD).optimized.census.census.pair i = (operandLeft, operandRight) ∧
        ((packageR hfirstD).optimized.census.census.pair i).1 ≠
          ((packageR hfirstD).optimized.census.census.pair i).2) ∧
      (((0, 0), (0, -1)) : JointCoins K97cubic) ∈
        collisionFailureEvent (packageR hfirstD).optimized.census.census ∧
      NPR.fn (K := K97cubic) operandLeft (-1) =
        NPR.fn (K := K97cubic) operandRight (-1) ∧
      GlobalCarryRecognizer.enc (-1 : K97cubic) operandLeft =
        GlobalCarryRecognizer.enc (-1 : K97cubic) operandRight := by
  refine ⟨packageR_consumed_census_has_genuine_distinct_pair hfirstD hrootAt hrootAtQ, ?_, ?_, ?_⟩
  · rw [mem_collisionFailureEvent_iff]
    obtain ⟨i, hi, _⟩ := packageR_consumed_census_has_genuine_distinct_pair hfirstD hrootAt hrootAtQ
    exact ⟨i, by rw [hi]; exact operands_not_sepSeed_at_neg_one⟩
  · exact (operands_fn_eq_iff (-1)).2 rfl
  · exact operands_enc_eq_at_neg_one

/-! ## D. Optimized pinning, independently replayed -/

theorem optimized_same_problem_really_pins_both_coordinates
    (ω : JointCoins K97cubic) (lmb : K97cubic)
    (hsame : (packageR hfirstD).OptimizedSameProblemAt ω lmb) :
    nprSeed ω = seedD ∧ alphaM ω = alphaD := by
  have hcfg := congrArg RawProblem.cfg hsame.specialized_eq_objects
  constructor
  · have hz : nprSeed ω = (packageR hfirstD).objects.cfg.challenges.z := by
      calc
        nprSeed ω =
            (specializedProblem (packageR hfirstD).optimized.verifier.raw.timestamp
              (nprSeed ω) hsame.nprSeed_ne (alphaM ω) lmb).cfg.challenges.z :=
          (specializedProblem_seed _ _ _ _ _).symm
        _ = (packageR hfirstD).objects.cfg.challenges.z :=
          congrArg (fun cfg : ExactConfig F97 K97cubic => cfg.challenges.z) hcfg
    rw [hz, (packageR_regression hfirstD hrootAt hrootAtQ).1, seedD_cfg]
  · have hα : alphaM ω = (packageR hfirstD).objects.cfg.challenges.α := by
      calc
        alphaM ω =
            (specializedProblem (packageR hfirstD).optimized.verifier.raw.timestamp
              (nprSeed ω) hsame.nprSeed_ne (alphaM ω) lmb).cfg.challenges.α :=
          (specializedProblem_tableAlpha _ _ _ _ _).symm
        _ = (packageR hfirstD).objects.cfg.challenges.α :=
          congrArg (fun cfg : ExactConfig F97 K97cubic => cfg.challenges.α) hcfg
    rw [hα, (packageR_regression hfirstD hrootAt hrootAtQ).1]
    rfl

theorem optimized_acceptance_really_pins_both_coordinates
    (c : OptimizedProductionChallengeTuple K97cubic F97)
    (hacc :
      (packageR hfirstD).OptimizedHistoricalAcceptanceAt
        (computeTraceR hfirstD) (memoryTraceR hfirstD) c) :
    nprSeed c.1 = seedD ∧ alphaM c.1 = alphaD :=
  optimized_same_problem_really_pins_both_coordinates hfirstD haxR hbasisR hwidthR
    hrootAt hrootAtQ c.1 c.2.2.2.lambda hacc.same_problem

/-! ## E. Production acceptance: alphaM is pinned, the seed remains open -/

/-- Exact production predicate expansion.  No `OptimizedSameProblemAt` occurs in
this type.  This structural absence is not, by itself, a proof that the
package-specific predicate fails to imply a seed equality. -/
theorem production_acceptance_exact_shape
    (ω : JointCoins K97cubic) (hz : nprSeed ω ≠ 0) :
    (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam ↔
      ((((packageR hfirstD).strategy.verifier.messageAt ω cfgD.challenges.lam hz).VerifierChecks
          (packageR hfirstD).strategy.verifier.raw.claim ω ∧
        ProductionAxisStructureVerifier.structuralChecksAt
          (packageR hfirstD).strategy.verifier (nprSeed ω) hz (alphaM ω) = true) ∧
      (packageR hfirstD).strategy.RootAxisBoundaryAt (nprSeed ω) hz (alphaM ω)) := by
  rw [(packageR hfirstD).strategy.accepts_iff ω cfgD.challenges.lam hz,
    ProductionAxisStructureVerifier.accepts_iff
      (packageR hfirstD).strategy.verifier ω cfgD.challenges.lam hz]

omit hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ

/-- Row-level extraction retaining the prover's actual auxiliary columns. -/
theorem compute_rapcomp_at_of_satisfies
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K]
    {p : ℕ} [CharP K p]
    {R : RawPlusIOSegmentedFamily F K}
    (M : RawMessage R p)
    (hchar : NodeEncoding.StateTagChar K)
    (hrap : ∀ kind, (R.computeTableRAP kind).Satisfies M.computeTableTrace)
    (i : Fin R.cfg.compRows) :
    ComputeTable.RAPcomp R.cfg.challenges.computeInputs
      (R.exec.computePubAt i) (R.exec.computeDecAt i) (M.tables.compute i) := by
  let env := fun i : Fin R.cfg.compRows =>
    computeEnvFull R.cfg.challenges.computeInputs
      (ComputeTable.opSel (R.exec.computePubAt i).state)
      (R.exec.computePubAt i) (R.exec.computeDecAt i) (M.tables.compute i)
  have hrowRAP :=
    (computeRowSegment_iff R.cfg M.computeTableTrace).1 (hrap .row)
  have hrows :
      ∀ i, ∀ c ∈ computeAIR.constraints, c.expr.eval (env i) = 0 := by
    apply (satisfies_iff_perRow_env env R.cfg.compNodes R.cfg.compNodes_injective
      R.cfg.challenges.computeValuation R.cfg.eDeg R.cfg.orbit.h
      R.cfg.orbit.ω R.cfg.orbit.βcoset R.cfg.orbit.βcoset_ne_zero
      R.cfg.orbit_h_pos (fun _ => rfl) (fun _ => rfl)).1
    simpa [env, RawMessage.computeTableTrace] using hrowRAP
  obtain ⟨s, hs, hlocal, _⟩ :=
    computeAIR_sound_free R.cfg.challenges.computeInputs
      (ComputeTable.opSel (R.exec.computePubAt i).state)
      (R.exec.computePubAt i) (R.exec.computeDecAt i) (M.tables.compute i)
      (RawMessage.freeSelectorChar_of_stateTagChar hchar) (hrows i)
  have hstate : s = (R.exec.computePubAt i).state := by
    by_contra hne
    have he := congrFun hs (R.exec.computePubAt i).state
    simp [ComputeTable.opSel, Ne.symm hne] at he
  subst s
  simpa using hlocal

include hfirstD hrootAt hrootAtQ


theorem production_acceptance_pins_alphaM
    (ω : JointCoins K97cubic) (hacc : (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam) :
    alphaM ω = alphaD := by
  have hz : nprSeed ω ≠ 0 :=
    MultiRootNonzeroChallenges.accepts_seed_ne_zero hacc
  have hverifier : (verifierQ hfirstD).Accepts ω cfgD.challenges.lam := by
    change (packageR hfirstD).strategy.verifier.Accepts ω cfgD.challenges.lam
    exact (packageR hfirstD).strategy.productionRawAccepts_of_accepts ω cfgD.challenges.lam hz hacc
  have hsixω :=
    ((verifierQ hfirstD).accepts_iff_eight_segmented_families ω cfgD.challenges.lam hz).1 hverifier
  have hcertω :=
    (((verifierQ hfirstD).messageAt ω cfgD.challenges.lam hz).raw.memoryWalkRAP_wholeTrace_iff).1
      hsixω.2.2.2.2.1
  have hω := hcertω.1.ln1
  have hsixTarget :=
    (PlusIOSameExecutionAssignment.satisfies_iff_six_families
      (assignmentQ hfirstD (alphaC ω) (gamma ω))).1
      ((completionQ hfirstD).assignment (alphaC ω) (gamma ω)).sixFamilies
  have hcertTarget :=
    (PlusIOSameExecutionAssignment.memoryWalkRAP_wholeTrace_iff
      (assignmentQ hfirstD (alphaC ω) (gamma ω))).1 hsixTarget.2.2.2.1
  have ht := hcertTarget.1.ln1
  change (assignmentQ hfirstD (alphaC ω) (gamma ω)).memoryWalk.ln 1 = alphaM ω at hω
  change (assignmentQ hfirstD (alphaC ω) (gamma ω)).memoryWalk.ln 1 = alphaD at ht
  exact hω.symm.trans ht

/-- The package-specific seed pin omitted earlier.  The same committed OP_5
inverse witness appears in the accepted row at `nprSeed ω` and in the known
accepted row at seed `8`; subtracting the two RLC equations pins the seed. -/
theorem production_acceptance_pins_seed
    (ω : JointCoins K97cubic) (hacc : (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam) :
    nprSeed ω = seedD := by
  have hz : nprSeed ω ≠ 0 :=
    MultiRootNonzeroChallenges.accepts_seed_ne_zero hacc
  have hverifier : (verifierQ hfirstD).Accepts ω cfgD.challenges.lam := by
    change (packageR hfirstD).strategy.verifier.Accepts ω cfgD.challenges.lam
    exact (packageR hfirstD).strategy.productionRawAccepts_of_accepts ω cfgD.challenges.lam hz hacc
  have hsixω :=
    ((verifierQ hfirstD).accepts_iff_eight_segmented_families ω cfgD.challenges.lam hz).1 hverifier
  let iω : Fin ((verifierQ hfirstD).familyAt ω cfgD.challenges.lam hz).cfg.compRows :=
    ⟨0, ((verifierQ hfirstD).familyAt ω cfgD.challenges.lam hz).cfg.compRows_pos⟩
  have hcur := compute_rapcomp_at_of_satisfies
    ((verifierQ hfirstD).messageAt ω cfgD.challenges.lam hz).raw stateTagChar97 hsixω.2.1 iω
  have htargetVerifier := verifierQ_accepts hfirstD (alphaC ω) (gamma ω)
  have hsixTarget :=
    ((verifierQ hfirstD).accepts_iff_eight_segmented_families
      (coinQ (alphaC ω) (gamma ω)) cfgD.challenges.lam seedH_ne).1 htargetVerifier
  let it : Fin
      ((verifierQ hfirstD).familyAt (coinQ (alphaC ω) (gamma ω)) cfgD.challenges.lam seedH_ne).cfg.compRows :=
    ⟨0, ((verifierQ hfirstD).familyAt
      (coinQ (alphaC ω) (gamma ω)) cfgD.challenges.lam seedH_ne).cfg.compRows_pos⟩
  have htarget := compute_rapcomp_at_of_satisfies
    ((verifierQ hfirstD).messageAt (coinQ (alphaC ω) (gamma ω)) cfgD.challenges.lam seedH_ne).raw
    stateTagChar97 hsixTarget.2.1 it
  have hstateCur :
      (((verifierQ hfirstD).familyAt ω cfgD.challenges.lam hz).exec.computePubAt iω).state = .s5 := by
    simp [iω, verifierQ, HonestCommitment.verifierOf,
      ProductionRawVerifier.TemplateAdapter.Strategy.honest,
      acceptedFamilyDataQ, alphaMCommitmentQ,
      TemplateRawJointSoundness.Strategy.alphaMCommitment,
      TemplateRawJointSoundness.Strategy.familyAt,
      AlphaMFamilyData.atCoins,
      ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      specializedProblem, HonestCommitment.Data.timestampStrategy,
      HonestCommitment.Data.executionTemplate,
      DataOnlyTemplateFixedStagedTimestampStrategy.ofRawData,
      ExactExecutionTemplate.specialize, ComputeRowTemplate.specialize,
      specializeMemRecScaled, computeLineOrigin,
      ExactExecution.computePubAt, ExactExecution.computeRowAt,
      ExactExecution.computeRows, bfsForest,
      HonestCommitment.renderComputeTemplate, HonestCommitment.renderComputeRow,
      dataD, skelD, HonestCommitment.skeletonOfNodes, computeNodesD, op5Node,
      op5Stamp, op5SkelD, op5Row] <;> rfl
  have hstateTarget :
      (((verifierQ hfirstD).familyAt
        (coinQ (alphaC ω) (gamma ω)) cfgD.challenges.lam seedH_ne).exec.computePubAt it).state = .s5 := by
    simp [it, verifierQ, HonestCommitment.verifierOf,
      ProductionRawVerifier.TemplateAdapter.Strategy.honest,
      acceptedFamilyDataQ, alphaMCommitmentQ, coinQ,
      TemplateRawJointSoundness.Strategy.alphaMCommitment,
      TemplateRawJointSoundness.Strategy.familyAt,
      AlphaMFamilyData.atCoins,
      ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      specializedProblem, HonestCommitment.Data.timestampStrategy,
      HonestCommitment.Data.executionTemplate,
      DataOnlyTemplateFixedStagedTimestampStrategy.ofRawData,
      ExactExecutionTemplate.specialize, ComputeRowTemplate.specialize,
      specializeMemRecScaled, computeLineOrigin,
      ExactExecution.computePubAt, ExactExecution.computeRowAt,
      ExactExecution.computeRows, bfsForest,
      HonestCommitment.renderComputeTemplate, HonestCommitment.renderComputeRow,
      dataD, skelD, HonestCommitment.skeletonOfNodes, computeNodesD, op5Node,
      op5Stamp, op5SkelD, op5Row] <;> rfl
  have hecur := hcur.2.2.2.2
  have hetarget := htarget.2.2.2.2
  rw [show ((verifierQ hfirstD).familyAt ω cfgD.challenges.lam hz).cfg.challenges.computeInputs =
      ((verifierQ hfirstD).familyAt ω cfgD.challenges.lam hz).cfg.challenges.computeInputs from rfl] at hecur
  simp only [ComputeTable.evalR, hstateCur] at hecur
  simp only [ComputeTable.evalR, hstateTarget] at hetarget
  rcases hecur with ⟨_, _, _, _, _, _, _, _, _, _, _, hcurInv⟩
  rcases hetarget with ⟨_, _, _, _, _, _, _, _, _, _, _, htargetInv⟩
  dsimp [iω, it] at hcurInv htargetInv
  simp [verifierQ, HonestCommitment.verifierOf,
    ProductionRawVerifier.TemplateAdapter.Strategy.honest,
    acceptedFamilyDataQ, alphaMCommitmentQ, rawStrategyQ,
    TemplateRawJointSoundness.Strategy.alphaMCommitment,
    TemplateRawJointSoundness.Strategy.familyAt,
    TemplateRawJointSoundness.Strategy.messageAt,
    AlphaMFamilyData.atCoins, AlphaMCommitment.tablesAt,
    ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
    ProductionRawVerifier.TemplateAdapter.Strategy.messageAt,
    specializedProblem, HonestCommitment.Data.timestampStrategy,
    HonestCommitment.Data.executionTemplate, HonestCommitment.configTemplateOf,
    DataOnlyTemplateFixedStagedTimestampStrategy.ofRawData,
    ExactExecutionTemplate.specialize, ComputeRowTemplate.specialize,
    specializeMemRecScaled, computeLineOrigin,
    ExactExecution.computePubAt, ExactExecution.computeRowAt,
    ExactExecution.computeRows, bfsForest,
    HonestCommitment.renderComputeTemplate, HonestCommitment.renderComputeRow,
    HonestCommitment.renderInputs, HonestCommitment.renderPub,
    HonestCommitment.renderDec,
    dataD, skelD, HonestCommitment.skeletonOfNodes, computeNodesD, op5Node,
    op5SkelD, op5Row, op5PubD, op5Dec, compInputs] at hcurInv htargetInv
  let i0 : Fin (legacyFamilyQ hfirstD 0 0).problem.cfg.compRows :=
    ⟨0, (legacyFamilyQ hfirstD 0 0).problem.cfg.compRows_pos⟩
  let g : K97cubic := ((assignmentQ hfirstD 0 0).computeTableAux i0).invGen
  have hresult (z : K97cubic) :
      (GlobalCarryRecognizer.enc z op5Result).leaf = 1 := by
    rw [GlobalCarryRecognizer.enc_leaf]
    change (NPR.listPoly [(1 : K97cubic)]).eval z = 1
    rw [NPR.listPoly_cons, NPR.listPoly_nil]
    simp
  have hresultPoly (z : K97cubic) :
      (NPR.listPoly (NPR.leafF (K := K97cubic) op5Result)).eval z = 1 := by
    rw [← GlobalCarryRecognizer.enc_leaf]
    exact hresult z
  have hcurSimple : g * (-(1 + nprSeed ω)) = 1 := by
    simp [g, i0, acceptedFamilyDataQ, AlphaMFamilyData.atCoins, specializedProblem,
      HonestCommitment.configTemplateOf, ExactConfigTemplate.specialize,
      ChallengeVectorTemplate.specialize, distinctCensusExecution, cfgD, compInputs,
      ChallengeVector.computeInputs, ComputeTable.fanoutComp,
      HonestCommitment.renderSubFP, op5SkelD, op5Row,
      leafPoly_eval_left, leafPoly_eval_right, hresultPoly] at hcurInv
    erw [List.getElem_cons_zero] at hcurInv
    simp [HonestCommitment.renderSubFP, op5SkelD, op5Row,
      leafPoly_eval_left, leafPoly_eval_right, hresultPoly] at hcurInv
    change g * (7 + 9 * nprSeed ω - (8 + 10 * nprSeed ω)) = 1 at hcurInv
    calc
      g * (-(1 + nprSeed ω)) =
          g * (7 + 9 * nprSeed ω - (8 + 10 * nprSeed ω)) := by ring
      _ = 1 := hcurInv
  have htargetSimple : g * (-(1 + seedD)) = 1 := by
    simp [g, i0, coinQ, acceptedFamilyDataQ, AlphaMFamilyData.atCoins, specializedProblem,
      HonestCommitment.configTemplateOf, ExactConfigTemplate.specialize,
      ChallengeVectorTemplate.specialize, distinctCensusExecution, cfgD, compInputs,
      ChallengeVector.computeInputs, ComputeTable.fanoutComp,
      HonestCommitment.renderSubFP, op5SkelD, op5Row,
      leafPoly_eval_left, leafPoly_eval_right, hresultPoly] at htargetInv
    erw [List.getElem_cons_zero] at htargetInv
    simp [HonestCommitment.renderSubFP, op5SkelD, op5Row,
      leafPoly_eval_left, leafPoly_eval_right, hresultPoly] at htargetInv
    change g * (7 + 9 * seedD - (8 + 10 * seedD)) = 1 at htargetInv
    calc
      g * (-(1 + seedD)) =
          g * (7 + 9 * seedD - (8 + 10 * seedD)) := by ring
      _ = 1 := htargetInv
  have hg : g ≠ 0 := by
    intro hg
    rw [hg, zero_mul] at htargetSimple
    exact zero_ne_one htargetSimple
  have hprod : g * (nprSeed ω - seedD) = 0 := by
    linear_combination -hcurSimple + htargetSimple
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hg)

def ProductionSeedPin : Prop :=
  ∀ ω : JointCoins K97cubic,
    (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam → nprSeed ω = seedD

/-- Production acceptance pins the complete committed fibre. -/
theorem production_acceptance_pins_fibre
    (ω : JointCoins K97cubic) (hacc : (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam) :
    nprSeed ω = seedD ∧ alphaM ω = alphaD :=
  ⟨production_acceptance_pins_seed hfirstD hrootAt hrootAtQ ω hacc,
    production_acceptance_pins_alphaM hfirstD hrootAt hrootAtQ ω hacc⟩


theorem full_production_fibre_pin_iff_seed_pin :
    (∀ ω : JointCoins K97cubic, (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam →
      nprSeed ω = seedD ∧ alphaM ω = alphaD) ↔ ProductionSeedPin hfirstD := by
  constructor
  · intro h ω hacc
    exact (h ω hacc).1
  · intro h ω hacc
    exact ⟨h ω hacc, production_acceptance_pins_alphaM hfirstD hrootAt hrootAtQ ω hacc⟩


theorem production_seed_pin_is_discharged : ProductionSeedPin hfirstD :=
  fun ω hacc => production_acceptance_pins_seed hfirstD hrootAt hrootAtQ ω hacc

/-- Wrong-layer/vacuity guard: the generic implication remains explicit. -/
theorem false_acceptance_empty_of_supplied_seed_pin
    (hseed : ProductionSeedPin hfirstD) :
    falseAcceptanceR hfirstD = ∅ :=
  falseAcceptanceR_empty_of_fibre_pinned hfirstD hrootAt hrootAtQ
    (full_production_fibre_pin_iff_seed_pin hfirstD hrootAt hrootAtQ |>.2 hseed)

include hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ

/-- FINDING at the consumed package: the production false-acceptance set is
empty. -/
theorem falseAcceptanceR_empty :
    falseAcceptanceR hfirstD = ∅ :=
  false_acceptance_empty_of_supplied_seed_pin hfirstD hrootAt hrootAtQ
    (production_seed_pin_is_discharged hfirstD hrootAt hrootAtQ)

/-- The same-set claim now forces the two fields to classify together as bounds
on an empty production false-acceptance set.  Their statement shape remains
the paper's probabilistic bound. -/
theorem both_p8_fields_classify_empty :
    falseAcceptanceR hfirstD = ∅ ∧
      |(jointProbability (falseAcceptanceR hfirstD))| ≤
        (workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
            (fixedTopologyWorkload (packageR hfirstD).strategy)
            (fixedAxisWorkload (packageR hfirstD).strategy) : ℝ) /
          (Fintype.card K97cubic : ℝ) ∧
      ∀ b : ℕ,
        workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
            (fixedTopologyWorkload (packageR hfirstD).strategy)
            (fixedAxisWorkload (packageR hfirstD).strategy) * 2 ^ b ≤
          Fintype.card K97cubic →
        |(jointProbability (falseAcceptanceR hfirstD))| ≤ 1 / 2 ^ b :=
  ⟨falseAcceptanceR_empty hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ,
    (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_soundness cfgD.challenges.lam,
    fun b hs => (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_bits cfgD.challenges.lam b hs⟩

include hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ

/-! ## F. Probabilistic paper claim and exact accounting -/

/-- The inhabited P8 probability bound coexists with a nonempty collision
event.  Thus the field is a probabilistic union-bound claim, not an assertion
that every constituent bad event is empty. -/
theorem probabilistic_bound_coexists_with_present_p8_collision :
    |(jointProbability (falseAcceptanceR hfirstD))| ≤
        (workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
            (fixedTopologyWorkload (packageR hfirstD).strategy)
            (fixedAxisWorkload (packageR hfirstD).strategy) : ℝ) /
          (Fintype.card K97cubic : ℝ) ∧
      (collisionFailureEvent (K := K97cubic)
        (packageR hfirstD).optimized.census.census).Nonempty :=
  ⟨(statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_soundness cfgD.challenges.lam,
    ⟨((0, 0), (0, -1)),
      (consumed_op5_pair_is_the_npr_collision_object
        hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ).2.1⟩⟩

/-- The four residual field names are exhibited at the unchanged consumed
fourteen-field statement; no class is silently moved. -/
theorem exact_four_named_tail_and_accounting :
    (9 + 1 + 4 = 14) ∧
      (|(jointProbability (falseAcceptanceR hfirstD))| ≤
        (workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
            (fixedTopologyWorkload (packageR hfirstD).strategy)
            (fixedAxisWorkload (packageR hfirstD).strategy) : ℝ) /
          (Fintype.card K97cubic : ℝ)) ∧
      (∀ b : ℕ,
        workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
            (fixedTopologyWorkload (packageR hfirstD).strategy)
            (fixedAxisWorkload (packageR hfirstD).strategy) * 2 ^ b ≤
          Fintype.card K97cubic →
        |(jointProbability (falseAcceptanceR hfirstD))| ≤ 1 / 2 ^ b) ∧
      (∀ (Qc : Fin (packageR hfirstD).computeChip.rap.w → F97[X])
          (Qm : Fin (packageR hfirstD).memoryChip.rap.w → F97[X]),
        (((packageR hfirstD).OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
            Fintype.card (OptimizedProductionChallengeTuple K97cubic F97) ≤
          optimizedProductionFailureProbabilityBound
            (Fintype.card K97cubic) (Fintype.card F97)
            (OptimizedFailureEventEv.workloadEv (packageR hfirstD) (packageR hfirstD).optimized.Λ +
              OptimizedHostileTimestamps.timestampCollisionBound
                (3 * (packageR hfirstD).optimized.family.problem.cfg.compRows) +
                pricedWalkWork (packageR hfirstD).optimized.family.problem.cfg.compRows
              (packageR hfirstD).optimized.family.problem.cfg.memRows)
            ((packageR hfirstD).hostileIOWork + (packageR hfirstD).hostileInterWork)
            (packageR hfirstD).optimized.family.problem.cfg.compRows
            (packageR hfirstD).optimized.family.problem.cfg.memRows) ∧
      (∀ (Qc : Fin (packageR hfirstD).computeChip.rap.w → F97[X])
          (Qm : Fin (packageR hfirstD).memoryChip.rap.w → F97[X]) (b : ℕ),
        optimizedProductionFailureProbabilityBound
            (Fintype.card K97cubic) (Fintype.card F97)
            (OptimizedFailureEventEv.workloadEv (packageR hfirstD) (packageR hfirstD).optimized.Λ +
              OptimizedHostileTimestamps.timestampCollisionBound
                (3 * (packageR hfirstD).optimized.family.problem.cfg.compRows) +
                pricedWalkWork (packageR hfirstD).optimized.family.problem.cfg.compRows
              (packageR hfirstD).optimized.family.problem.cfg.memRows)
            ((packageR hfirstD).hostileIOWork + (packageR hfirstD).hostileInterWork)
            (packageR hfirstD).optimized.family.problem.cfg.compRows
            (packageR hfirstD).optimized.family.problem.cfg.memRows * 2 ^ b ≤ 1 →
        (((packageR hfirstD).OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
            Fintype.card (OptimizedProductionChallengeTuple K97cubic F97) ≤
          1 / 2 ^ b) :=
  ⟨by norm_num, (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_soundness cfgD.challenges.lam,
    fun b hs => (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_bits cfgD.challenges.lam b hs,
    (packageR hfirstD).optimizedFalseAcceptance_probability_le_legacy haxR hbasisR hwidthR,
    (packageR hfirstD).optimizedFalseAcceptance_probability_le_two_pow_neg_legacy haxR hbasisR hwidthR⟩

/-- The live released capstone still consumes the exact same package statement. -/
theorem consumed_capstone_is_inhabited 
    (hax : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasis : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidth : FormRWidth F97):
    OptimizedFullStrictThm54Statement (packageR hfirstD) :=
  optimizedFullStrictNockVMROM_of_package (packageR hfirstD) hax hbasis hwidth

#print axioms p8_fields_share_the_exact_false_acceptance_set
#print axioms p8_bits_are_derived_from_the_same_event
#print axioms required_size_windows_exactly_s3_s4_s6
#print axioms consumed_size_window_event_is_empty
#print axioms consumed_op5_pair_is_the_npr_collision_object
#print axioms optimized_same_problem_really_pins_both_coordinates
#print axioms optimized_acceptance_really_pins_both_coordinates
#print axioms production_acceptance_exact_shape
#print axioms compute_rapcomp_at_of_satisfies
#print axioms production_acceptance_pins_alphaM
#print axioms production_acceptance_pins_seed
#print axioms production_acceptance_pins_fibre
#print axioms full_production_fibre_pin_iff_seed_pin
#print axioms production_seed_pin_is_discharged
#print axioms false_acceptance_empty_of_supplied_seed_pin
#print axioms falseAcceptanceR_empty
#print axioms both_p8_fields_classify_empty
#print axioms probabilistic_bound_coexists_with_present_p8_collision
#print axioms exact_four_named_tail_and_accounting
#print axioms consumed_capstone_is_inhabited

#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch89
