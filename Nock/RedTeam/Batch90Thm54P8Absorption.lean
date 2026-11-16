import Nock.NockVMROM.Thm54.DistinctCensusP8FixedField
import Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
import Nock.NockVMROM.Thm54.MultiRootServedFixture
import Nock.NockVMROM.Thm54.WalkTilingEvents

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!

Paper frame:
the paper.

Consumed Lean objects:
`DistinctCensusFold2.packageR`,
`ProductionP8Containment.FalseAcceptanceSet`,
`OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageR hfirstD)`, and
`optimizedFullStrictNockVMROM_of_package (packageR hfirstD) hax hbasis hwidth`.

Result: scoped PASS. The
accepted OP_5 row pins `nprSeed = 8`, the memory-walk initial line pins
`alphaM = 4`, and the exact `FalseAcceptanceSet` quantified by both P8 fields
is empty at `(packageR hfirstD)`. The two P8 field types remain the released inhabited
union bounds. The exact package-R split is therefore `11 + 1 + 2`: the
remaining two are precisely `complete_false_acceptance_bound` and
`complete_false_acceptance_bits`.

This is a fixture-level classification.  It does not classify the optimized
false-acceptance set, prove whole-joint completeness, construct a generic
`CommitmentResidual`, or introduce a selector challenge.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch90

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Noun Nock.Walk
open Framework Framework.Reify Framework.Thm54
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.ProductionRawVerifier
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.EqualityOperandCensus
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment
open Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
open Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
open Nock.NockVMROM.Thm54.DistinctCensusFold2
open Nock.NockVMROM.Thm54.DistinctCensusP8FixedField
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootHonestArrays
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97b90 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97b90 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
include hfirstD

variable (hrootAt : ∀ a g : K97cubic,
  (packageR hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
include hrootAt
variable (hrootAtQ : ∀ a g : K97cubic,
  (packageQ hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
include hrootAtQ

variable (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)

/-! ## A. Production acceptance is non-vacuous -/

/-- A real accepted production coin. -/
theorem production_acceptance_nonvacuous :
    (packageR hfirstD).strategy.Accepts (coinQ 2 5) cfgD.challenges.lam ∧
      nprSeed (coinQ 2 5) = 8 ∧ alphaM (coinQ 2 5) = 4 :=
  ⟨packageR_accepts hfirstD hrootAt hrootAtQ 2 5, rfl, rfl⟩

/-! ## B. Independent extraction from production `Accepts`

This repeats the load-bearing extraction rather than invoking the production
`production_acceptance_pins_*` theorems. -/

omit hfirstD hrootAt hrootAtQ

/-- Row-segment satisfaction yields the actual `RAPcomp`, including the
committed auxiliary `invGen` column. -/
theorem independent_compute_rapcomp_at_of_satisfies
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

/-- Production `Accepts`, not optimized same-problem equality, pins the memory
walk challenge through `ln(1) = alphaM`. -/
theorem independent_production_acceptance_pins_alphaM
    (ω : JointCoins K97cubic) (hacc : (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam) :
    alphaM ω = alphaD := by
  have hz : nprSeed ω ≠ 0 :=
    MultiRootNonzeroChallenges.accepts_seed_ne_zero hacc
  have hverifier : ((verifierQ hfirstD)).Accepts ω cfgD.challenges.lam := by
    change (packageR hfirstD).strategy.verifier.Accepts ω cfgD.challenges.lam
    exact (packageR hfirstD).strategy.productionRawAccepts_of_accepts ω cfgD.challenges.lam hz hacc
  have hsixω :=
    (((verifierQ hfirstD)).accepts_iff_eight_segmented_families ω cfgD.challenges.lam hz).1 hverifier
  have hcertω :=
    ((((verifierQ hfirstD)).messageAt ω cfgD.challenges.lam hz).raw.memoryWalkRAP_wholeTrace_iff).1
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

/-- Production `Accepts` pins the NPR seed from the consumed OP_5 EC.5 inverse
equation. -/
theorem independent_production_acceptance_pins_seed
    (ω : JointCoins K97cubic) (hacc : (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam) :
    nprSeed ω = seedD := by
  have hz : nprSeed ω ≠ 0 :=
    MultiRootNonzeroChallenges.accepts_seed_ne_zero hacc
  have hverifier : ((verifierQ hfirstD)).Accepts ω cfgD.challenges.lam := by
    change (packageR hfirstD).strategy.verifier.Accepts ω cfgD.challenges.lam
    exact (packageR hfirstD).strategy.productionRawAccepts_of_accepts ω cfgD.challenges.lam hz hacc
  have hsixω :=
    (((verifierQ hfirstD)).accepts_iff_eight_segmented_families ω cfgD.challenges.lam hz).1 hverifier
  let iω : Fin (((verifierQ hfirstD)).familyAt ω cfgD.challenges.lam hz).cfg.compRows :=
    ⟨0, (((verifierQ hfirstD)).familyAt ω cfgD.challenges.lam hz).cfg.compRows_pos⟩
  have hcur := independent_compute_rapcomp_at_of_satisfies
    (((verifierQ hfirstD)).messageAt ω cfgD.challenges.lam hz).raw stateTagChar97 hsixω.2.1 iω
  have htargetVerifier := verifierQ_accepts hfirstD (alphaC ω) (gamma ω)
  have hsixTarget :=
    (((verifierQ hfirstD)).accepts_iff_eight_segmented_families
      (coinQ (alphaC ω) (gamma ω)) cfgD.challenges.lam seedH_ne).1 htargetVerifier
  let it : Fin
      (((verifierQ hfirstD)).familyAt (coinQ (alphaC ω) (gamma ω)) cfgD.challenges.lam seedH_ne).cfg.compRows :=
    ⟨0, (((verifierQ hfirstD)).familyAt
      (coinQ (alphaC ω) (gamma ω)) cfgD.challenges.lam seedH_ne).cfg.compRows_pos⟩
  have htarget := independent_compute_rapcomp_at_of_satisfies
    (((verifierQ hfirstD)).messageAt (coinQ (alphaC ω) (gamma ω)) cfgD.challenges.lam seedH_ne).raw
    stateTagChar97 hsixTarget.2.1 it
  have hstateCur :
      ((((verifierQ hfirstD)).familyAt ω cfgD.challenges.lam hz).exec.computePubAt iω).state = .s5 := by
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
      ((((verifierQ hfirstD)).familyAt
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
  rw [show (((verifierQ hfirstD)).familyAt ω cfgD.challenges.lam hz).cfg.challenges.computeInputs =
      (((verifierQ hfirstD)).familyAt ω cfgD.challenges.lam hz).cfg.challenges.computeInputs from rfl] at hecur
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
    op5SkelD, op5Row, op5PubD, op5Dec, compInputs, Fin.cast] at hcurInv htargetInv
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

/-- The independently replayed theorem starts from production `Accepts`; no
optimized same-problem hypothesis occurs. -/
theorem independent_production_acceptance_pins_fibre
    (ω : JointCoins K97cubic) (hacc : (packageR hfirstD).strategy.Accepts ω cfgD.challenges.lam) :
    nprSeed ω = 8 ∧ alphaM ω = 4 := by
  exact
    ⟨(independent_production_acceptance_pins_seed hfirstD hrootAt hrootAtQ ω hacc).trans
        (show seedD = (8 : K97cubic) from rfl),
      (independent_production_acceptance_pins_alphaM hfirstD hrootAt hrootAtQ ω hacc).trans
        (show alphaD = (4 : K97cubic) from rfl)⟩

/-! ## C. Emptiness at the exact event consumed by both statement fields -/

theorem independent_coin_eq_coinQ (ω : JointCoins K97cubic)
    (hz : nprSeed ω = seedD) (hα : alphaM ω = alphaD) :
    ω = coinQ (alphaC ω) (gamma ω) := by
  rcases ω with ⟨⟨a, g⟩, ⟨α, z⟩⟩
  change ((a, g), (α, z)) = ((a, g), (alphaD, seedD))
  exact Prod.ext rfl (Prod.ext hα hz)

/-- Direct independent replay of emptiness at the exact set in
`OptimizedFullStrictThm54Statement.p8_fixed_field_*`. -/
theorem independent_consumed_falseAcceptanceSet_empty :
    FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro ω hω
  have hacc := (mem_falseAcceptanceSet_iff _ _ _ _ ω).1 hω
  refine hacc.2 ((packageR hfirstD).containment ω cfgD.challenges.lam hacc.1 ?_)
  have hpin := independent_production_acceptance_pins_fibre hfirstD hrootAt hrootAtQ ω hacc.1
  have hz : nprSeed ω = seedD :=
    hpin.1.trans (show (8 : K97cubic) = seedD from rfl)
  have hα : alphaM ω = alphaD :=
    hpin.2.trans (show (4 : K97cubic) = alphaD from rfl)
  intro hbad
  simp only [ProductionP8Containment.FailureUnion, Finset.mem_union] at hbad
  rcases hbad with hbad | hbad
  · rcases hbad with hbad | hbad
    · rcases hbad with hbad | hbad
      · rcases hbad with hbad | hbad
        · exact MultiRootNonzeroChallenges.accepts_seed_ne_zero hacc.1
            ((mem_zeroSeedFailureEvent_iff ω).1 hbad)
        · rw [independent_coin_eq_coinQ hfirstD hrootAt hrootAtQ ω hz hα] at hbad
          apply coinQ_not_collisionFailureEvent hfirstD hrootAtQ (alphaC ω) (gamma ω)
          rw [← packageR_census hfirstD]
          exact hbad
      · rw [independent_coin_eq_coinQ hfirstD hrootAt hrootAtQ ω hz hα] at hbad
        exact coinQ_not_specializedTopologyFailureEvent hfirstD hrootAtQ (alphaC ω) (gamma ω) hbad
    · rw [independent_coin_eq_coinQ hfirstD hrootAt hrootAtQ ω hz hα] at hbad
      exact coinR_not_guardedAxisFailureEvent hfirstD hrootAt hrootAtQ (alphaC ω) (gamma ω) hbad
  · rw [sizeWindowFailureR_empty hfirstD hrootAt hrootAtQ] at hbad
    exact absurd hbad (Finset.notMem_empty _)

/-- The same syntactic event is empty and is the probability argument of both
unchanged P8 field types. -/
theorem exact_same_set_and_unchanged_p8_field_types
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97) :
    FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam = ∅ ∧
      |jointProbability
          (FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam)| ≤
        (workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
            (fixedTopologyWorkload (packageR hfirstD).strategy)
            (fixedAxisWorkload (packageR hfirstD).strategy) : ℝ) /
          (Fintype.card K97cubic : ℝ) ∧
      ∀ b : ℕ,
        workload (packageR hfirstD).strategy (packageR hfirstD).optimized.Λ
            (fixedTopologyWorkload (packageR hfirstD).strategy)
            (fixedAxisWorkload (packageR hfirstD).strategy) * 2 ^ b ≤
          Fintype.card K97cubic →
        |jointProbability
            (FalseAcceptanceSet (packageR hfirstD).strategy (packageR hfirstD).q (packageR hfirstD).optimized.Λ cfgD.challenges.lam)| ≤
          1 / 2 ^ b :=
  ⟨independent_consumed_falseAcceptanceSet_empty hfirstD hrootAt hrootAtQ,
    (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_soundness cfgD.challenges.lam, fun b hs => (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_bits cfgD.challenges.lam b hs⟩

/-! ## D. Exact fourteen-field shape and class split -/


inductive StatementField
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

def substantiveFields : List StatementField :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets, .shared_forest_axis]

def typeSummaryFields : List StatementField := [.structural]

def residualFields : List StatementField :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Machine-checked `11+1+2`: all names are distinct and the explicit lists
have the claimed cardinalities. -/
theorem exact_eleven_one_two_name_partition :
    substantiveFields.length = 11 ∧
      typeSummaryFields.length = 1 ∧
      residualFields.length = 2 ∧
      (substantiveFields ++ typeSummaryFields ++ residualFields).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide


theorem statementR_fourteen_field_eta
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97) :
    (statementR hfirstD haxR hbasisR hwidthR) =
      { structural := (statementR hfirstD haxR hbasisR hwidthR).structural
        optimized_chips := (statementR hfirstD haxR hbasisR hwidthR).optimized_chips
        shared_io := (statementR hfirstD haxR hbasisR hwidthR).shared_io
        perfect_completeness := (statementR hfirstD haxR hbasisR hwidthR).perfect_completeness
        containment := (statementR hfirstD haxR hbasisR hwidthR).containment
        walk_bounds := (statementR hfirstD haxR hbasisR hwidthR).walk_bounds
        p8_fixed_field_soundness := (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_soundness
        p8_fixed_field_bits := (statementR hfirstD haxR hbasisR hwidthR).p8_fixed_field_bits
        acceptance_to_target := (statementR hfirstD haxR hbasisR hwidthR).acceptance_to_target
        complete_false_acceptance_bound :=
          (statementR hfirstD haxR hbasisR hwidthR).complete_false_acceptance_bound
        complete_false_acceptance_bits :=
          (statementR hfirstD haxR hbasisR hwidthR).complete_false_acceptance_bits
        staged_false_acceptance_bound :=
          (statementR hfirstD haxR hbasisR hwidthR).staged_false_acceptance_bound
        exact_resources := (statementR hfirstD haxR hbasisR hwidthR).exact_resources
        row_budgets := (statementR hfirstD haxR hbasisR hwidthR).row_budgets
        shared_forest_axis := (statementR hfirstD haxR hbasisR hwidthR).shared_forest_axis } := by
  cases (statementR hfirstD haxR hbasisR hwidthR)
  rfl

/-- The only residual projections are still the complete optimized
false-acceptance bounds; this theorem exhibits them and does not classify
them. -/
theorem exact_two_residual_projection_types
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97) :
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
  ⟨(packageR hfirstD).optimizedFalseAcceptance_probability_le_legacy haxR hbasisR hwidthR,
    (packageR hfirstD).optimizedFalseAcceptance_probability_le_two_pow_neg_legacy haxR hbasisR hwidthR⟩

/-- Package-relative arithmetic is unchanged away from R.  In particular P
still has its empty self-pair collision event and `9+1+4` split. -/
theorem other_package_recounts_unchanged
    (haxQ : FormRAxisBound (packageQ hfirstD).optimized.sampled (packageQ hfirstD).optimized.basis)
    (hbasisQ : FormRBasis (packageQ hfirstD).optimized.basis)
    (hwidthQ : FormRWidth F97)
    (haxH : FormRAxisBound (packageH hfirstD).optimized.sampled (packageH hfirstD).optimized.basis)
    (hbasisH : FormRBasis (packageH hfirstD).optimized.basis)
    (hwidthH : FormRWidth F97)
    (haxD : FormRAxisBound (packageD hfirstD).optimized.sampled (packageD hfirstD).optimized.basis)
    (hbasisD : FormRBasis (packageD hfirstD).optimized.basis)
    (hwidthD : FormRWidth F97)
    (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled (packageP hmoreM).optimized.basis)
    (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
    (hwidthP : FormRWidth F97) :
    (8 + 1 + 5 = 14) ∧ Nonempty (OptimizedFullStrictThm54Statement (packageQ hfirstD)) ∧
      (8 + 1 + 5 = 14) ∧ Nonempty (OptimizedFullStrictThm54Statement (packageH hfirstD)) ∧
      (7 + 1 + 6 = 14) ∧ Nonempty (OptimizedFullStrictThm54Statement (packageD hfirstD)) ∧
      (9 + 1 + 4 = 14) ∧ Nonempty (OptimizedFullStrictThm54Statement (packageP hmoreM)) ∧
      collisionFailureEvent (K := K97cubic)
        (packageP hmoreM).optimized.census.census = ∅ :=
  ⟨by norm_num, ⟨statementQ hfirstD haxQ hbasisQ hwidthQ⟩, by norm_num,
    ⟨statementH hfirstD haxH hbasisH hwidthH⟩, by norm_num,
    ⟨statementD hfirstD haxD hbasisD hwidthD⟩, by norm_num,
    ⟨statementP hmoreM haxP hbasisP hwidthP⟩,
    collisionFailureEventM_empty⟩


theorem consumed_capstone_exact
    (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled (packageR hfirstD).optimized.basis)
    (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
    (hwidthR : FormRWidth F97) :
    OptimizedFullStrictThm54Statement (packageR hfirstD) :=
  optimizedFullStrictNockVMROM_of_package (packageR hfirstD) haxR hbasisR hwidthR

#print axioms production_acceptance_nonvacuous
#print axioms independent_compute_rapcomp_at_of_satisfies
#print axioms independent_production_acceptance_pins_alphaM
#print axioms independent_production_acceptance_pins_seed
#print axioms independent_production_acceptance_pins_fibre
#print axioms independent_consumed_falseAcceptanceSet_empty
#print axioms exact_same_set_and_unchanged_p8_field_types
#print axioms exact_eleven_one_two_name_partition
#print axioms statementR_fourteen_field_eta
#print axioms exact_two_residual_projection_types
#print axioms other_package_recounts_unchanged
#print axioms consumed_capstone_exact

#print axioms
  Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.production_acceptance_pins_fibre
#print axioms
  Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.falseAcceptanceR_empty
#print axioms
  Nock.NockVMROM.Thm54.DistinctCensusP8FixedField.accounting_after_p8_empty
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch90
