import Nock.NockVMROM.Thm54.MultiRootHonestArrays
import Nock.RedTeam.Batch78Thm54ConvergedCommitment
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Accepting package at the zero walk challenges

Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

The controls below separate three facts which must not be conflated:

* `alphaC coinM = gamma coinM = 0`.  At the isolated compute-walk layer this is
  degenerate: the all-zero line/count/accumulator assignment accepts arbitrary
  current-node, child, and fanout columns.
* The IO LogUp layer does not use those two sampled walk coordinates.  It is the
  symbolic `RatFunc (RatFunc K)` construction and raw acceptance still implies
  the exact `LIO` relation.  A duplicated response multiset is rejected.
* The full package also carries the authoritative exact execution and exact
  topology.  The isolated walk control is therefore not promoted to a
  package-level false-acceptance claim.
-/

namespace Nock.RedTeam.Batch79

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Noun Nock.Walk Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.MultiRootHonestArrays

noncomputable section

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)

/-! ## A. Exact sampled coordinates and the degenerate compute walk -/

theorem coinM_coordinates :
    alphaC coinM = 0 ∧ gamma coinM = 0 ∧ alphaM coinM = fixtureAlpha ∧
      nprSeed coinM = servedSeed :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- At zero, the walk-node RLC is projection onto coordinate zero. -/
theorem rlc_zero_is_first_coordinate
    {K : Type} [Field K] {n : ℕ} (v : Fin (n + 1) → K) :
    rlc 0 v = v 0 := by
  simp [rlc, Fin.sum_univ_succ]

/-- At `alphaC = 0`, all-zero scalar walk columns satisfy every recurrence and
the terminal check, independently of the committed node, child, and fanout data. -/
theorem zero_alpha_walk_closes
    {K : Type} [Field K]
    (cur : ℕ → K) (chld : ℕ → ℕ → K) (fo : ℕ → ℕ) {h : ℕ} (hh : 1 ≤ h) :
    WalkSat cur chld fo (fun _ => 0) (fun _ => 0) (fun _ => 0)
        0 0 0 h ∧
      (fun _ : ℕ => (0 : K)) h = 0 := by
  constructor
  · refine
      { hpos := hh
        ln1 := rfl
        lnInc := ?_
        count1 := ?_
        countInc := ?_
        accInit := ?_
        accStep := ?_ }
    · intro i hi hlt
      simp
    · simp
    · intro i hi hlt
      simp
    · simp
    · intro i hi hlt
      simp
  · rfl

def alteredCur : ℕ → K97cubic
  | 1 => 1
  | 2 => 1
  | _ => 0

def alteredChild : ℕ → ℕ → K97cubic := fun _ _ => 0
def alteredFanout : ℕ → ℕ := fun _ => 0

/-- Decisive walk-layer control: a concrete two-row scalar sequence which is
not a full BFT nevertheless has accepting zero walk columns. -/
theorem altered_non_bft_walk_accepts_at_zero :
    (∃ ln count acc : ℕ → K97cubic,
      WalkSat alteredCur alteredChild alteredFanout ln count acc 0 0 0 2 ∧
        acc 2 = 0) ∧
      ¬ IsFullBFT alteredCur alteredChild alteredFanout 2 := by
  constructor
  · exact ⟨fun _ => 0, fun _ => 0, fun _ => 0,
      (zero_alpha_walk_closes alteredCur alteredChild alteredFanout (by norm_num)).1, rfl⟩
  · intro h
    have hc := congrArg (fun p : K97cubic[X] => p.coeff 2) h
    norm_num [IsFullBFT, nodeListP, nodeQueueP, queueTerm, alteredCur,
      alteredChild, alteredFanout, Sf, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at hc
    have hx : (X : K97cubic[X]).coeff 2 = 0 := by
      rw [Polynomial.coeff_X]
      norm_num
    rw [hx] at hc
    exact one_ne_zero hc

/-! ## B. The IO LogUp conditions do not collapse with the walk coins -/

/-- The final specialization retains the exact problem and production message. -/
theorem zero_coin_family_is_final_specialization :
    rawStrategyM.familyAt coinM cfgS.challenges.lam seedM_ne =
        RawPlusIOSegmentedFamily.ofLegacy legacyFamilyM ∧
      rawStrategyM.messageAt coinM cfgS.challenges.lam seedM_ne =
        RawMessage.ofLegacy honestAssignmentM :=
  ⟨rawStrategyM_familyAt, rawStrategyM_messageAt⟩

/-- The proof passes through the symbolic IO RAPs, whose `RLC` and log-derivative
variables are `RatFunc` indeterminates rather than `alphaC` or `gamma`. -/
theorem coinM_acceptance_forces_exact_io :
    IO.LIO rawLegacyM.cfg.Ksz rawLegacyM.exec.derivedRequestIO
      rawLegacyM.exec.derivedResponseIO := by
  have hraw :
      (RawMessage.ofLegacy honestAssignmentM).Accepts skelM.publicClaim coinM := by
    exact ⟨honestVerifierGatesM,
      RawMessage.sixRAPSatisfy_of_legacy honestAssignmentM
        honestCompletionM.assignment.sixFamilies⟩
  have hprog :
      rawLegacyM.exec.derivedRequestIO.length + 1 ≤ 2 ^ rawLegacyM.cfg.orbit.h := by
    have hh : rawLegacyM.cfg.orbit.h = cfgS.orbit.h :=
      congrArg (fun P : RawProblem F97 K97cubic => P.cfg.orbit.h) rawLegacyM_problem
    rw [rawLegacyM_requests, hh]
    norm_num [cfgS, executionOrbit97]
  have hmem :
      rawLegacyM.exec.derivedResponseIO.length + 1 ≤ 2 ^ rawLegacyM.cfg.orbit.h := by
    have hh : rawLegacyM.cfg.orbit.h = cfgS.orbit.h :=
      congrArg (fun P : RawProblem F97 K97cubic => P.cfg.orbit.h) rawLegacyM_problem
    rw [rawLegacyM_responses, hh]
    norm_num [cfgS, executionOrbit97]
  apply (RawMessage.ofLegacy honestAssignmentM).lio_of_accepts
    legacyZeroFamilyM_KszBound
  · exact hprog
  · exact hmem
  · exact hraw

def duplicatedResponsesM : List (Fin 9 → K97cubic) :=
  [NockVM.encRecFormR parentRecordS MemoryTable.formRDefault,
      NockVM.encRecFormR servedRecord MemoryTable.formRDefault,
    NockVM.encRecFormR servedRecord MemoryTable.formRDefault]

/-- A materially altered response multiset with a duplicate is rejected by the
exact IO condition; zero walk coins do not make this condition automatic. -/
theorem duplicated_response_multiset_rejected :
    ¬ IO.LIO 4 rawLegacyM.exec.derivedRequestIO duplicatedResponsesM := by
  intro h
  have hnd := h.2.1
  simp [duplicatedResponsesM] at hnd

/-- The accepted honest lists are a genuine non-identity permutation. -/
theorem accepted_io_is_nonidentity_permutation :
    rawLegacyM.exec.derivedResponseIO.Perm rawLegacyM.exec.derivedRequestIO ∧
      rawLegacyM.exec.derivedResponseIO ≠ rawLegacyM.exec.derivedRequestIO := by
  change
    (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec.derivedResponseIO.Perm
        (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec.derivedRequestIO ∧
      (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec.derivedResponseIO ≠
        (specializedProblem timestampM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).exec.derivedRequestIO
  rw [specializedProblemM_honest]
  exact Nock.RedTeam.Batch78.responses_are_genuine_nonidentity_permutation

/-- The consumed package is not a false acceptance: its target is the complete
`GenuineWitness` target, not the isolated walk predicate. -/
theorem coinM_not_falseAcceptance
    (hrootAt : (packageHonestM hmoreM).strategy.RootAxisBoundaryAt
      (nprSeed coinM) seedM_ne (alphaM coinM)) :
    coinM ∉ FalseAcceptanceSet (packageHonestM hmoreM).strategy 97 3 cfgS.challenges.lam := by
  rw [mem_falseAcceptanceSet_iff]
  exact fun h => h.2 (genuineTargetM hmoreM hrootAt)

/-! ## C. `topologyBadGammas_empty_of_binding` is binding-driven -/

/-- Change one non-leading coordinate of the child payload. -/
def badServedPub : ComputeTable.Pub K97cubic :=
  { servedPub with s := { servedPub.s with dyck := servedPub.s.dyck + 1 } }

def badServedRow : ComputeTable.State × ComputeTable.DTcomp K97cubic :=
  (.s0, (servedInputs, badServedPub, servedDec))

def badComputeTree : NTree (ComputeTable.State × ComputeTable.DTcomp K97cubic) :=
  .node parentRowS [.node badServedRow []]

theorem bad_compute_payloads_differ :
    ComputeLinkPayload.encode (computeActualPayload badComputeTree 0) ≠
      ComputeLinkPayload.encode (computeExpectedPayload badComputeTree 0) := by
  intro h
  have hdyck := congrFun h (1 : Fin 9)
  simp only [computeActualPayload, computeExpectedPayload,
    ComputeLinkPayload.encode, ComputeLinkPayload.ofTriple] at hdyck
  change servedPub.s.dyck + 1 = (encS subjectS).dyck at hdyck
  change (encS subjectS).dyck + 1 = (encS subjectS).dyck at hdyck
  have hone : (1 : K97cubic) = 0 := by
    apply add_left_cancel (a := (encS subjectS).dyck)
    simpa only [add_zero] using hdyck
  exact one_ne_zero hone

/-- Without binding, zero is genuinely a bad topology gamma: it hides the
non-leading mutation while the full payloads differ. -/
theorem zero_is_bad_gamma_for_unbound_tree :
    (0 : K97cubic) ∈ computeSlotBadGammas badComputeTree 0 := by
  rw [computeSlotBadGammas, dif_pos (by simp [badComputeTree, parentRowS,
    ComputeTable.fanoutComp]), dif_pos bad_compute_payloads_differ]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [rlc_zero_is_first_coordinate, rlc_zero_is_first_coordinate]
  rfl

theorem honest_binding_eliminates_all_bad_gammas :
    RawTopologyBindingResidual
        (acceptedFamilyDataM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).base ∧
      topologyBadGammas
          (acceptedFamilyDataM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).base = ∅ :=
  ⟨baseM_binding,
    topologyBadGammas_empty_of_binding
      (acceptedFamilyDataM servedSeed seedM_ne fixtureAlpha cfgS.challenges.lam).base baseM_binding⟩

/-! ## D. Statement recount controls -/

/-- The production acceptance source is nonempty, while no claim that its
false-acceptance subset is inhabited is smuggled into the recount. -/
theorem production_acceptance_nonempty_but_false_subset_only
    (hrootAt : (packageHonestM hmoreM).strategy.RootAxisBoundaryAt
      (nprSeed coinM) seedM_ne (alphaM coinM)) :
    (∃ ω : JointCoins K97cubic, (packageHonestM hmoreM).strategy.Accepts ω cfgS.challenges.lam) ∧
      FalseAcceptanceSet (packageHonestM hmoreM).strategy 97 3 cfgS.challenges.lam ⊆
        Finset.univ.filter (fun ω => (packageHonestM hmoreM).strategy.Accepts ω cfgS.challenges.lam) := by
  refine ⟨packageHonestM_acceptance_nonempty hmoreM hrootAt, ?_⟩
  intro ω hω
  rw [mem_falseAcceptanceSet_iff] at hω
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hω.1⟩

/-! ## Private `Dec` data and `SepSeed` -/

theorem dec_active_counts_match_semantic_counts (st : ComputeTable.State) :
    (decActive st .f_th = true ↔ requiredTailRealizations st = 1) ∧
      (decActive st .f_tt = true ↔ requiredTailRealizations st = 1) ∧
      (decActive st .f_tth = true ↔ requiredBranchTailRealizations st = 1) ∧
      (decActive st .f_ttt = true ↔ requiredBranchTailRealizations st = 1) := by
  cases st <;> decide

/-- Exhaustive eta receipt for the semantic row data: the root, counted tails,
and counted branch tails are present, but boundedness ranges only over the
separately supplied `realizedNouns`. -/
theorem semantic_row_data_eta
    {K : Type} [Field K] {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (D : ComputeRowSemanticData q Λ row) :
    D =
      { root := D.root
        tails := D.tails
        branchTails := D.branchTails
        calls := D.calls
        windows := D.windows
        axisGates := D.axisGates
        tails_count := D.tails_count
        branchTails_count := D.branchTails_count
        calls_count := D.calls_count
        windows_count := D.windows_count
        axisGates_count := D.axisGates_count
        realizedNouns := D.realizedNouns
        subject_mem := D.subject_mem
        formula_mem := D.formula_mem
        result_mem := D.result_mem
        bounded := D.bounded
        comparisons := D.comparisons
        comparison_faithful := D.comparison_faithful
        comparison_leaves := D.comparison_leaves
        comparison_roles := D.comparison_roles
        axisGate_listed := D.axisGate_listed
        axisGate_tail_mem := D.axisGate_tail_mem
        needs := D.needs } := by
  cases D
  rfl

/- NOTE (inactiveDec reform): `inactive_dec_padding_is_exact_zero` was deleted
because `DecColumnNounRealization` no longer requires `FPSlotRealized.padding`
for inactive slots — those positions now satisfy `True`. See `SemanticStrategy.DecColumnNounRealization`. -/

/-- Public noun realization and private `Dec` realization are separate inputs. -/
theorem exact_noun_realization_eta
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {q : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (D : ExactExecutionNounRealization q cfg exec) :
    D =
      { computeTree := D.computeTree
        memoryForest := D.memoryForest
        memoryLeaves := D.memoryLeaves } := by
  cases D
  rfl

def collidingWitness :
    FPRealizationWitness servedSeed 97
      (GlobalCarryRecognizer.enc servedSeed subjectS) where
  noun := Nock.RedTeam.Batch78.collidingSubject
  bounded := by
    simp [Nock.RedTeam.Batch78.collidingSubject, FieldEmbedding.BoundedBy]
  encoding := Nock.RedTeam.Batch78.collidingSubject_enc_eq

def subjectWitness :
    FPRealizationWitness servedSeed 97
      (GlobalCarryRecognizer.enc servedSeed subjectS) where
  noun := subjectS
  bounded := by simp [subjectS, FieldEmbedding.BoundedBy]
  encoding := rfl

/-- Existence of bounded witnesses does not imply coherence at an arbitrary seed. -/
theorem colliding_witnesses_are_not_coherent :
    collidingWitness.noun ≠ subjectWitness.noun :=
  Nock.RedTeam.Batch78.collidingSubject_ne

theorem servedSeed_not_separating :
    ¬ GlobalCarryRecognizer.SepSeed servedSeed
      Nock.RedTeam.Batch78.collidingSubject subjectS := by
  intro hsep
  have hdata :
      (NPR.leafF (K := K97cubic) Nock.RedTeam.Batch78.collidingSubject,
        NPR.dyckBits (K := K97cubic) Nock.RedTeam.Batch78.collidingSubject) ≠
      (NPR.leafF (K := K97cubic) subjectS,
        NPR.dyckBits (K := K97cubic) subjectS) := by
    intro h
    have hl := congrArg Prod.fst h
    norm_num [Nock.RedTeam.Batch78.collidingSubject, subjectS, NPR.leafF,
      Noun.leafList] at hl
    have hnat : (8 : ℕ) = 7 :=
      stateTagChar97 (by norm_num) (by norm_num) hl.1
    omega
  exact (hsep hdata) (GlobalCarryRecognizer.enc_eq_imp_fn_eq servedSeed
    Nock.RedTeam.Batch78.collidingSubject subjectS
    Nock.RedTeam.Batch78.collidingSubject_enc_eq)

/-! ## F. Scope and regression controls -/

/-- Acceptance consumes the literal committed exponent trees; no fixture
`Exists.choose` exponent occurs in this chain. -/
theorem literal_axis_chain_reaches_package
    (hrootAt : (packageHonestM hmoreM).strategy.RootAxisBoundaryAt
      (nprSeed coinM) seedM_ne (alphaM coinM)) :
    TemplateAxisCounting.templateForestReadExps templateM = [1, 2, 3] ∧
      TemplateAxisCounting.templateForestVerifyExps templateM = [1, 2, 3] ∧
      (packageHonestM hmoreM).strategy.Accepts coinM cfgS.challenges.lam :=
  ⟨forestReadExpsM, forestVerifyExpsM, packageHonestM_accepts hmoreM hrootAt⟩

/-- The array-level difference implies a difference of the dependent residual
records; no exponent identification is needed. -/
theorem residualHonestM_ne_residualM : residualHonestM ≠ residualM := by
  intro h
  have hw := congrArg
    (fun R : BuildablePackage.CommitmentResidual multiRootExecution =>
      R.verifier.raw.afterCoins coinM cfgS.challenges.lam seedM_ne)
    h
  have hln := congrArg (fun W : RawWalkArrays K97cubic => W.memoryLn 1) hw
  have hsix :=
    (PlusIOSameExecutionAssignment.satisfies_iff_six_families honestAssignmentM).1
      honestCompletionM.assignment.sixFamilies
  have hcert :=
    (PlusIOSameExecutionAssignment.memoryWalkRAP_wholeTrace_iff honestAssignmentM).1
      hsix.2.2.2.1
  have hln1 : honestAssignmentM.memoryWalk.ln 1 = fixtureAlpha := by
    have halpha : legacyZeroFamilyM.memoryWalkAlpha = fixtureAlpha := rfl
    exact hcert.1.ln1.trans halpha
  have hzero : honestAssignmentM.memoryWalk.ln 1 = 0 := by
    change honestAssignmentM.memoryWalk.ln 1 = 0 at hln
    exact hln
  have hfour : (fixtureAlpha : K97cubic) ≠ 0 := by
    intro h40
    have hnat : (4 : ℕ) = 0 :=
      stateTagChar97 (by norm_num) (by norm_num) (by simpa [fixtureAlpha] using h40)
    omega
  exact hfour (hln1.symm.trans hzero)

theorem released_aliases_unchanged :
    @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package ∧
      @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch78.released_aliases_unchanged

#print axioms coinM_coordinates
#print axioms rlc_zero_is_first_coordinate
#print axioms zero_alpha_walk_closes
#print axioms altered_non_bft_walk_accepts_at_zero
#print axioms coinM_acceptance_forces_exact_io
#print axioms duplicated_response_multiset_rejected
#print axioms accepted_io_is_nonidentity_permutation
#print axioms coinM_not_falseAcceptance
#print axioms zero_is_bad_gamma_for_unbound_tree
#print axioms honest_binding_eliminates_all_bad_gammas
#print axioms production_acceptance_nonempty_but_false_subset_only
#print axioms dec_active_counts_match_semantic_counts
#print axioms semantic_row_data_eta
-- inactive_dec_padding_is_exact_zero: deleted (inactiveDec reform)
#print axioms exact_noun_realization_eta
#print axioms collidingWitness
#print axioms subjectWitness
#print axioms colliding_witnesses_are_not_coherent
#print axioms servedSeed_not_separating
#print axioms literal_axis_chain_reaches_package
#print axioms residualHonestM_ne_residualM
#print axioms released_aliases_unchanged

#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.packageHonestM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.statementHonestM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.packageHonestM_accepts
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.coinM_not_failureUnion
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.genuineTargetM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.containmentM_is_informative
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.topologyBadGammas_empty_of_binding
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.arraysM_ne_zeroAlphaM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.arraysM_multiplicity_ne_zero
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.residualHonestM_uses_honest_arrays
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestArrays.packageHonestM_regression

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
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVM.V_NockVMROM_forest

end
end Nock.RedTeam.Batch79
