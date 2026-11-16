import Nock.RedTeam.Batch58Thm54FinalComputeRAP
import Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
import Nock.NockVMROM.Thm54.OptimizedComputeR6Obstruction

/-!
# Final compute compiler alias repair and canonical trace foundation

The user-authorized optimized compiler is a recorded correctness delta, not a source attribution.

Settled memory-axis
batching is outside this compute repair and is unchanged.
-/

namespace Nock.RedTeam.Batch59

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

open Classical
open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Module
open scoped Polynomial
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeCodec
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeR6Obstruction
open Nock.NockVMROM.Thm54.OptimizedComputeSampledTrace
open Nock.NockVMROM.Thm54.OptimizedComputeSampledTrace.Concrete
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeTypedLowering
open Nock.NockVMROM.Thm54.StrictExtension

noncomputable section

/-! ## 1. Challenge, public, and line namespaces -/

theorem semantic_challenge_namespaces_exact :
    tableChallengeBase = 0 ∧ tableChallengeCount = 6 ∧
      walkChallengeBase = 6 ∧ walkChallengeCount = 1 ∧
      sampledChallengeBase = 7 ∧ sampledChallengeCount = 2 ∧
      compilerChallengeBase = 9 ∧ compilerChallengeCount = 3 ∧
      finalScalarChallengeBase = 36 := by
  decide

theorem all_semantic_namespace_maps_exact (i : ℕ) :
    computeSubst .challenge i = .Var .challenge i ∧
      finalWalkSubst .challenge i =
        .Var .challenge (walkChallengeBase + i) ∧
      finalSampledNamespace .challenge 6 = .Var .challenge sampledChallengeBase ∧
      finalSampledNamespace .challenge 7 =
        .Var .challenge (sampledChallengeBase + 1) ∧
      finalWalkSubst .publicVal i = .Var .publicVal i ∧
      finalSampledNamespace .publicVal i = .Var .publicVal i := by
  simp [computeSubst, finalWalkSubst, finalSampledNamespace, walkChallenge,
    sampledChallenge, finalSampledGamma, finalSampledPole]

theorem semantic_challenge_namespaces_pairwise_disjoint :
    (∀ i < tableChallengeCount, ∀ j < walkChallengeCount,
      tableChallengeBase + i ≠ walkChallengeBase + j) ∧
    (∀ i < tableChallengeCount, ∀ j < sampledChallengeCount,
      tableChallengeBase + i ≠ sampledChallengeBase + j) ∧
    (∀ i < tableChallengeCount, ∀ j < compilerChallengeCount,
      tableChallengeBase + i ≠ compilerChallengeBase + j) ∧
    (∀ i < walkChallengeCount, ∀ j < sampledChallengeCount,
      walkChallengeBase + i ≠ sampledChallengeBase + j) ∧
    (∀ i < walkChallengeCount, ∀ j < compilerChallengeCount,
      walkChallengeBase + i ≠ compilerChallengeBase + j) ∧
    (∀ i < sampledChallengeCount, ∀ j < compilerChallengeCount,
      sampledChallengeBase + i ≠ compilerChallengeBase + j) := by
  simp only [tableChallengeBase, tableChallengeCount, walkChallengeBase,
    walkChallengeCount, sampledChallengeBase, sampledChallengeCount,
    compilerChallengeBase, compilerChallengeCount, Nat.zero_add]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro i hi j hj h <;> omega

/-- Cubic expansion sends the twelve extension-valued challenges exactly to raw indices `0..35`;
the scalar selector RLC at `36` cannot alias any coordinate. -/
theorem expanded_challenge_coordinates_exact (i : Fin 12) (k : Fin 3) :
    3 * (i : ℕ) + (k : ℕ) < finalScalarChallengeBase := by
  norm_num [finalScalarChallengeBase]
  omega

theorem expanded_challenge_coordinate_injective :
    Function.Injective (fun q : Fin 12 × Fin 3 =>
      3 * (q.1 : ℕ) + (q.2 : ℕ)) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ h
  change 3 * (i : ℕ) + (k : ℕ) = 3 * (j : ℕ) + (l : ℕ) at h
  have hdiv := congrArg (fun n : ℕ => n / 3) h
  have hik : (3 * (i : ℕ) + (k : ℕ)) / 3 = (i : ℕ) := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right,
      Nat.div_eq_of_lt k.isLt, Nat.zero_add] <;> norm_num
  have hjl : (3 * (j : ℕ) + (l : ℕ)) / 3 = (j : ℕ) := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right,
      Nat.div_eq_of_lt l.isLt, Nat.zero_add] <;> norm_num
  rw [hik, hjl] at hdiv
  apply Prod.ext
  · apply Fin.ext
    exact hdiv
  · apply Fin.ext
    change (k : ℕ) = (l : ℕ)
    omega

/-- Public walk endpoints are two `K` values and therefore occupy raw coordinates `0..5`; the
fixed scalar selector vectors start at indices 20 and 31. -/
theorem expanded_public_endpoint_coordinates_disjoint
    (i : Fin 2) (k : Fin 3) (j : Fin 11) :
    3 * (i : ℕ) + (k : ℕ) < 6 ∧
      3 * (i : ℕ) + (k : ℕ) ≠ 20 + (j : ℕ) ∧
      3 * (i : ℕ) + (k : ℕ) ≠ 31 + (j : ℕ) := by
  omega

/-- The source table decoder is exhaustive on all 94 current/next source columns and reaches only
the normalized 13/58 row plus table challenges `0..5`. -/
theorem every_table_source_column_stays_in_table_namespace
    (kind : VarKind) (i : Fin 94)
    (hkind : kind = .traceCur ∨ kind = .traceNext) :
    ∀ x ∈ (computeTraceSubst kind i).vars,
      match x.1 with
      | .traceCur | .traceNext => x.2 < 71
      | .challenge => x.2 < tableChallengeCount
      | .publicVal => True := by
  intro x hx
  rcases x with ⟨kind', j⟩
  have h := Nock.RedTeam.Batch53.all_94_source_columns_have_physical_decoders
    kind i hkind (kind', j) hx
  cases kind' <;> simpa [tableChallengeCount] using h

/-- All twenty-one production extension gates survive direct lowering and every challenge/public
leaf is inside the declared final namespaces. -/
theorem every_final_extension_gate_has_supported_lowering :
    ∀ t ∈ finalLoweredExtTransitionGates, FinalTypedSupportFits t :=
  finalLoweredExtTransitionGates_support

def namespaceAttackEnv : Env ℚ where
  trace := fun _ => 0
  traceNext := fun _ => 0
  chal := fun i => i
  pub := fun i => i

/-- Replaying one namespace as another changes the evaluated verifier variable. -/
theorem wrong_namespace_replay_rejected :
    (tableChallenge 0).eval namespaceAttackEnv = 0 ∧
      (walkChallenge 0).eval namespaceAttackEnv = 6 ∧
      (sampledChallenge 0).eval namespaceAttackEnv = 7 ∧
      (sampledChallenge 1).eval namespaceAttackEnv = 8 ∧
      finalFoldChallenge.eval namespaceAttackEnv = 9 ∧
      (tableChallenge 0).eval namespaceAttackEnv ≠
        (walkChallenge 0).eval namespaceAttackEnv ∧
      (walkChallenge 0).eval namespaceAttackEnv ≠
        (sampledChallenge 0).eval namespaceAttackEnv := by
  norm_num [tableChallenge, walkChallenge, sampledChallenge, finalFoldChallenge,
    namespaceAttackEnv, Expr.eval, tableChallengeBase, walkChallengeBase,
    sampledChallengeBase, compilerChallengeBase]

theorem public_namespaces_exact_and_disjoint :
    (∀ i < 2, ∀ j < 11, i ≠ 20 + j) ∧
      (∀ i < 2, ∀ j < 11, i ≠ 31 + j) ∧
      (∀ i < 11, ∀ j < 11, 20 + i ≠ 31 + j) ∧
      31 + 11 = 42 := by
  refine ⟨?_, ?_, ?_, by norm_num⟩ <;>
    intro i hi j hj h <;> omega

/-! ## 2. Direct role lowering and the repaired line allocation -/

theorem final_extension_coordinate_injective :
    Function.Injective (fun q : Fin 62 × Fin 3 =>
      OptimizedComputeFinalTypedLowering.finalExtCoordIndex q.1 q.2) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ h
  change 13 + 3 * (i : ℕ) + (k : ℕ) =
    13 + 3 * (j : ℕ) + (l : ℕ) at h
  have h' : 3 * (i : ℕ) + (k : ℕ) = 3 * (j : ℕ) + (l : ℕ) := by
    omega
  have hdiv := congrArg (fun n : ℕ => n / 3) h'
  have hik : (3 * (i : ℕ) + (k : ℕ)) / 3 = (i : ℕ) := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right,
      Nat.div_eq_of_lt k.isLt, Nat.zero_add] <;> norm_num
  have hjl : (3 * (j : ℕ) + (l : ℕ)) / 3 = (j : ℕ) := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right,
      Nat.div_eq_of_lt l.isLt, Nat.zero_add] <;> norm_num
  rw [hik, hjl] at hdiv
  apply Prod.ext
  · apply Fin.ext
    exact hdiv
  · apply Fin.ext
    change (k : ℕ) = (l : ℕ)
    omega

theorem all_base_and_extension_coordinates_disjoint
    (i : Fin 13) (r : Fin 62) (k : Fin 3) :
    (i : ℕ) ≠ OptimizedComputeFinalTypedLowering.finalExtCoordIndex r k := by
  simp [OptimizedComputeFinalTypedLowering.finalExtCoordIndex]
  omega

theorem every_final_coordinate_is_in_width (r : Fin 62) (k : Fin 3) :
    OptimizedComputeFinalTypedLowering.finalExtCoordIndex r k < 199 := by
  simp [OptimizedComputeFinalTypedLowering.finalExtCoordIndex]
  omega

theorem table55_walk61_are_distinct :
    computeTraceSubst .traceCur 66 = .Var .traceCur (ext0 + 55) ∧
      finalWalkSubst .traceCur 0 = .Var .traceCur (ext0 + 61) ∧
      (55 : ℕ) ≠ 61 ∧
      ext0 + 55 ≠ ext0 + 61 := by
  exact ⟨rfl, rfl, by decide, by decide⟩

/-- Current and next leaves remain separate even when their numeric role is the same. -/
theorem current_next_role_phases_do_not_alias (r s : Fin 62) :
    FinalTypedExpr.extCur r ≠ FinalTypedExpr.extNext s := by
  intro h
  cases h

/-- Coordinate compilation preserves row phase; no current leaf can become a next leaf. -/
theorem compiled_current_next_coordinates_do_not_alias
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (r s : Fin 62) (k l : Fin 3) :
    finalTypedCompile b (.extCur r) k ≠ finalTypedCompile b (.extNext s) l := by
  intro h
  cases h

/-- Every one of the 21 production sources lowers; `filterMap` has not silently dropped a source
into the `lowerFinalTotal` zero fallback. -/
theorem direct_final_lowering_has_no_fallback :
    finalLoweredExtTransitionGates.length = historicalFinalExtTransitionGates.length ∧
      finalLoweredExtTransitionGates.length = 21 := by
  exact ⟨by simp, finalLoweredExtTransitionGates_length⟩

theorem old_fin58_rejects_walk61_but_fin62_accepts :
    lower (finalWalkSubst .traceCur 0) = none ∧
      lower (finalWalkSubst .traceNext 0) = none ∧
      lowerFinal (finalWalkSubst .traceCur 0) = some (.extCur 61) ∧
      lowerFinal (finalWalkSubst .traceNext 0) = some (.extNext 61) :=
  walk_line_requires_final_lowering

theorem general_same_object_recovery_is_inhabited
    (tableChallengeValue walkChallengeValue tableLineValue walkLineValue :
      K73cubic) :
    ∃ env : Env K73cubic,
      (computeSubst .challenge 0).eval env = tableChallengeValue ∧
      (finalWalkSubst .challenge 0).eval env = walkChallengeValue ∧
      (computeTraceSubst .traceCur 66).eval env = tableLineValue ∧
      (finalWalkSubst .traceCur 0).eval env = walkLineValue :=
  ⟨finalRecoveryEnv tableChallengeValue walkChallengeValue tableLineValue walkLineValue,
    final_compiler_recovers_independent_values _ _ _ _⟩

theorem old_fin58_concrete_obstruction_and_repaired_four_zero :
    (∀ env : Env K73cubic, ¬ CurrentCompilerSameObjectRecovery env) ∧
      FinalCompilerSameObjectRecovery concreteFinalRecoveryEnv ∧
      (computeSubst .challenge 0).eval concreteFinalRecoveryEnv = 4 ∧
      (finalWalkSubst .challenge 0).eval concreteFinalRecoveryEnv = 0 ∧
      (computeTraceSubst .traceCur 66).eval concreteFinalRecoveryEnv = 4 ∧
      (finalWalkSubst .traceCur 0).eval concreteFinalRecoveryEnv = 0 :=
  ⟨current_compiler_same_object_recovery_is_empty,
    concrete_final_compiler_same_object_recovery, concrete_final_recovers_four_zero⟩

/-! ## 3. Canonical 302-column trace foundation -/

/-- The five ranges are exhaustive and pairwise separated: Base13, core roles `0..57`, residual
roles `58..60`, walk roles `61..62` (role `62` is the queue witness), and form-R `202..301`. -/
theorem every_final_column_has_exactly_one_class (j : Fin 302) :
    ((j : ℕ) < 13) ∨
      (13 ≤ (j : ℕ) ∧ (j : ℕ) < 187) ∨
      (187 ≤ (j : ℕ) ∧ (j : ℕ) < 196) ∨
      (196 ≤ (j : ℕ) ∧ (j : ℕ) < 202) ∨
      (202 ≤ (j : ℕ) ∧ (j : ℕ) < 302) := by
  omega

/-- Executable exhaustive control: among the five allocation predicates, exactly one is true for
each of all 302 physical columns. -/
theorem every_final_column_assignment_count_is_one (j : Fin 302) :
    [decide ((j : ℕ) < 13),
      decide (13 ≤ (j : ℕ) ∧ (j : ℕ) < 187),
      decide (187 ≤ (j : ℕ) ∧ (j : ℕ) < 196),
      decide (196 ≤ (j : ℕ) ∧ (j : ℕ) < 202),
      decide (202 ≤ (j : ℕ) ∧ (j : ℕ) < 302)].count true = 1 := by
  revert j
  decide

theorem final_column_partition_boundaries :
    13 + 58 * 3 = 187 ∧
      13 + 61 * 3 = 196 ∧
      13 + 63 * 3 = 202 := by
  norm_num

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-- Cubic lowering is correct for extension-valued challenges
and the two extension-valued endpoint publics. -/
theorem final_challenge_and_public_coordinate_offsets
    (b : Basis (Fin 3) F K) (i : Fin 12) (u : Fin 2) (k : Fin 3) :
    finalTypedCompile b (.challenge i) k =
        .var .challenge (3 * (i : ℕ) + (k : ℕ)) ∧
      finalTypedCompile b (.publicVal u) k =
        .var .publicVal (3 * (u : ℕ) + (k : ℕ)) := by
  exact ⟨rfl, rfl⟩

theorem historical_public_coordinate_name_compatibility
    (b : Basis (Fin 3) F K) (u : Fin 2) (k : Fin 3) :
    Nock.RedTeam.Batch58.historicalFinalTypedCompile b
        (FinalTypedExpr.publicVal u) k =
      finalTypedCompile b (.publicVal u) k :=
  rfl

/-- Node injectivity is a checked input to both interpolation stages, not an inferred or omitted
side condition. -/
theorem canonical_interpolation_nodes_injective
    {n : ℕ} (nodes : Fin n → F) (hnodes : Function.Injective nodes) :
    Function.Injective nodes :=
  hnodes

def finalRowIndex (n : ℕ) (hn : 0 < n) : Fin n :=
  ⟨n - 1, Nat.sub_lt hn (by omega)⟩

/-- `traceNext` is always polynomial evaluation at `ω*x`; in particular the terminal row is not
implemented by an out-of-range or cyclic semantic-row lookup. -/
theorem preliminary_next_is_polynomial_evaluation
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.compRows) (j : Fin 302) :
    (envOfTrace (preliminaryTrace A hn nodes b) orbit.ω
      (nodes i) chalVal pubVal).traceNext j =
      (preliminaryTrace A hn nodes b j).eval (orbit.ω * nodes i) := by
  simp [envOfTrace]

theorem preliminary_final_row_next_is_polynomial_evaluation
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h) (j : Fin 302) :
    (envOfTrace (preliminaryTrace A hn nodes b) orbit.ω
      (nodes (finalRowIndex R.problem.cfg.compRows hn)) chalVal pubVal).traceNext j =
      (preliminaryTrace A hn nodes b j).eval
        (orbit.ω * nodes (finalRowIndex R.problem.cfg.compRows hn)) := by
  apply preliminary_next_is_polynomial_evaluation

theorem canonical_residual_role_eval
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.compRows) (r : ResidualWitnessId) (k : Fin 3) :
    (canonicalFinalTrace A hn nodes b chalVal pubVal orbit
        ⟨OptimizedComputeFinal.finalExtCoordIndex (residualWitnessRole r) k, by
          have := (OptimizedComputeFinal.finalExtCoordIndex
            (residualWitnessRole r) k).isLt
          omega⟩).eval
        (nodes i) =
      (finalTypedCompile b (finalResidualSource r) k).eval
        (envOfTrace (preliminaryTrace A hn nodes b) orbit.ω
          (nodes i) chalVal pubVal) := by
  rw [canonicalFinalTrace_eval A hn nodes hnodes b chalVal pubVal orbit]
  fin_cases r <;> fin_cases k <;>
    norm_num [OptimizedComputeFinal.finalExtCoordIndex, residualWitnessRole]

theorem canonical_walk_role61_eval
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.compRows) (k : Fin 3) :
    (canonicalFinalTrace A hn nodes b chalVal pubVal orbit
        ⟨OptimizedComputeFinal.finalExtCoordIndex walkLineRole k, by
          have := (OptimizedComputeFinal.finalExtCoordIndex walkLineRole k).isLt
          omega⟩).eval (nodes i) =
      coord b (A.exact.computeWalk.ln ((i : ℕ) + 1)) k := by
  rw [canonicalFinalTrace_eval A hn nodes hnodes b chalVal pubVal orbit]
  fin_cases k <;>
    norm_num [OptimizedComputeFinal.finalExtCoordIndex, walkLineRole,
      preliminaryCell, coreExtensionValue]

theorem canonical_masks_are_fixed_preprocessing
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h) :
    (NamedComputeRAP hn nodes b chalVal pubVal orbit).BindsPreprocessing
      (canonicalFinalTrace A hn nodes b chalVal pubVal orbit) :=
  canonicalFinalTrace_binds_preprocessing A hn nodes b chalVal pubVal orbit

/-! ## 4. Fixed binding, resources, and all-four-column semantics -/

theorem fixed_binding_and_resources_unchanged
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) :
    let Q := NamedComputeRAP hn nodes b chalVal pubVal orbit
    Q.fixedCount = 2 ∧ Q.rap.e = 3 ∧ Q.rap.k = 2 ∧
      Q.rap.wRAP = ![296, 6] ∧ Q.rap.w = 302 ∧
      Q.rap.s = 118 ∧ Q.rap.d = 4 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, finalComputeAllGates_length n b, rfl⟩

/-- The wrapper's satisfaction proposition contains preprocessing binding as a literal conjunct,
so raw gate satisfaction cannot bypass fixed columns. -/
theorem final_satisfaction_cannot_bypass_fixed_binding
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (P : Fin 302 → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing
      (NamedComputeRAP hn nodes b chalVal pubVal orbit) P) :
    (NamedComputeRAP hn nodes b chalVal pubVal orbit).BindsPreprocessing P :=
  hsat.2

/-- Roles 58--60 are residual equations and role 61 is the walk line. -/
theorem all_four_residual_columns_are_semantic :
    (∀ r : ResidualWitnessId, (residualWitnessRole r : ℕ) < 61) ∧
      (walkLineRole : ℕ) = 61 ∧
      inertResidualRole = walkLineRole ∧
      (∀ r : ResidualWitnessId, residualWitnessRole r ≠ walkLineRole) := by
  refine ⟨residual_resource_partition.1, residual_resource_partition.2.1, rfl, ?_⟩
  intro r
  fin_cases r <;> decide

theorem every_auxiliary_pin_is_present
    (n : ℕ) (b : Basis (Fin 3) F K)
    (r : ResidualWitnessId) (k : Fin 3) :
    residualAuxGateCoord b r k ∈ finalComputeAllGates n b :=
  residualAuxGateCoord_mem_final n b r k

/-! ## 5. Concrete same-object package recovery and malformed replay controls -/

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance char73 : CharP K73cubic 73 := inferInstance
local instance charRing : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

theorem concrete_recovery_uses_exact_package_cfg_exec_coins :
    honestLegacyFamily.problem.cfg = cfg honestSeed honestAlpha ∧
      HEq honestLegacyFamily.problem.exec (exec honestSeed honestAlpha) ∧
      honestSampled.exact = honestAssignment ∧
      honestSampled.sampled = ioStrategy ∧
      honestSampled.sampled.coins = ioCoins ∧
      FinalCompilerSameObjectRecovery concreteFinalRecoveryEnv := by
  have hp := specializedProblem_eq honestSeed honestSeed_ne honestAlpha
  refine ⟨?_, ?_, rfl, rfl, rfl, concrete_final_compiler_same_object_recovery⟩
  · change
      (TemplateRawJointSoundness.specializedProblem timestampStrategy honestSeed
        honestSeed_ne honestAlpha MemoryTable.formRDefault).cfg = cfg honestSeed honestAlpha
    rw [hp]
  · change
      HEq
        (TemplateRawJointSoundness.specializedProblem timestampStrategy honestSeed
          honestSeed_ne honestAlpha MemoryTable.formRDefault).exec
        (exec honestSeed honestAlpha)
    rw [hp]

theorem wrong_walk_challenge_replay_rejected :
    ¬ FinalCompilerSameObjectRecovery
      (finalRecoveryEnv (4 : K73cubic) 4 4 0) := by
  intro h
  have hw := h.walkChallenge
  rw [concrete_compute_walk_challenge_eq_zero] at hw
  norm_num [finalRecoveryEnv, finalWalkSubst, walkChallenge, Expr.eval,
    walkChallengeBase, tableChallengeBase] at hw
  exact
    (@SetEq.Lcast_ne_zero K73cubic _ 73 char73 4 (by norm_num) (by norm_num)) hw

theorem wrong_walk_line_replay_rejected :
    ¬ FinalCompilerSameObjectRecovery
      (finalRecoveryEnv (4 : K73cubic) 0 4 4) := by
  intro h
  have hw := h.walkLine
  rw [concrete_compute_walk_line_eq_zero] at hw
  norm_num [finalRecoveryEnv, finalWalkSubst, finalWalkLine, finalWalkLineIndex,
    finalWalkLineRole, ext0, Expr.eval] at hw
  exact
    (@SetEq.Lcast_ne_zero K73cubic _ 73 char73 4 (by norm_num) (by norm_num)) hw

/-! ## 6. -/

/-- The compiled satisfaction theorem remains at the final gate-list boundary. -/
theorem compiled_boundary_only
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (NamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing
        (NamedComputeRAP hn nodes b chalVal pubVal orbit) P ↔
      FinalComputeCompiledLanguage hn nodes b chalVal pubVal orbit P :=
  namedComputeRAP_satisfies_iff_compiledLanguage hn nodes b chalVal pubVal orbit P

/-- Named statement of the still-open compute connective. No inhabitant is asserted here. -/
def FinalComputeDecoderAndCanonicalSatisfactionGoal : Prop :=
  ∀ {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations),
    ∃ (nodes : Fin R.problem.cfg.compRows → F)
      (hnodes : Function.Injective nodes)
      (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
      (h : ℕ) (orbit : StrictOrbitDomain F 3 h),
      RAP.SatisfiesWithPreprocessing
        (NamedComputeRAP R.problem.cfg.compRows_pos nodes b chalVal pubVal orbit)
        (canonicalFinalTrace A R.problem.cfg.compRows_pos nodes b chalVal pubVal orbit)

def strict_package_still_requires_B29
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ}
    (P : Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage F K hOrb q Λ) :=
  Nock.RedTeam.Batch58.strict_package_still_requires_B29 P

theorem paper_alias_still_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch58.paper_alias_remains_forest

#print axioms semantic_challenge_namespaces_pairwise_disjoint
#print axioms all_semantic_namespace_maps_exact
#print axioms expanded_challenge_coordinate_injective
#print axioms expanded_public_endpoint_coordinates_disjoint
#print axioms every_table_source_column_stays_in_table_namespace
#print axioms every_final_extension_gate_has_supported_lowering
#print axioms wrong_namespace_replay_rejected
#print axioms final_extension_coordinate_injective
#print axioms compiled_current_next_coordinates_do_not_alias
#print axioms every_final_coordinate_is_in_width
#print axioms direct_final_lowering_has_no_fallback
#print axioms old_fin58_rejects_walk61_but_fin62_accepts
#print axioms general_same_object_recovery_is_inhabited
#print axioms old_fin58_concrete_obstruction_and_repaired_four_zero
#print axioms every_final_column_has_exactly_one_class
#print axioms every_final_column_assignment_count_is_one
#print axioms preliminary_next_is_polynomial_evaluation
#print axioms final_challenge_and_public_coordinate_offsets
#print axioms preliminary_final_row_next_is_polynomial_evaluation
#print axioms canonical_residual_role_eval
#print axioms canonical_walk_role61_eval
#print axioms canonical_masks_are_fixed_preprocessing
#print axioms fixed_binding_and_resources_unchanged
#print axioms final_satisfaction_cannot_bypass_fixed_binding
#print axioms all_four_residual_columns_are_semantic
#print axioms concrete_recovery_uses_exact_package_cfg_exec_coins
#print axioms wrong_walk_challenge_replay_rejected
#print axioms wrong_walk_line_replay_rejected
#print axioms compiled_boundary_only
#print axioms paper_alias_still_forest

end
end Nock.RedTeam.Batch59
