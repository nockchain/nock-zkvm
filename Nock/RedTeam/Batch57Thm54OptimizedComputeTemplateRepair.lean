import Nock.RedTeam.Batch56Thm54OptimizedComputeGateBasis
import Nock.NockVMROM.Thm54.OptimizedComputeTypedRowSemantics

/-!
* mixed normalized expressions lower without erasure to `Fin 13` base and `Fin 58` extension roles;
* the dedicated coordinate compiler evaluates correctly and all cubic trace coordinates are below
  width 187, including extension role 57;
* the non-IO source partition has exactly 511 distinct equations, including the displayed combined
  equation exactly once, and the walk endpoint source has all four equations including `walkOut`;
* the 13/21 row-local iff uses one typed environment and the explicit summary/RLC collision
  exclusions;
* the actual coordinate-expanded RAP has core fingerprint 187/87, two rounds, degree at most four,
  and pads to 199/98 with satisfaction preserved.

Axis descent/batching results are unchanged and are not re-litigated here.
-/

namespace Nock.RedTeam.Batch57

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

open Nock
open Nock.Reified
open Nock.ComputeTable
open Module
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeRowSemantics
open Nock.NockVMROM.Thm54.OptimizedComputeTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeTypedRowSemantics
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.StrictExtension
open scoped Polynomial

noncomputable section

/-! ## 1. Typed support and the retired index-68 attack -/

/-- Every trace leaf in a typed expression lands in the cubic 187-column core. -/
def TypedTraceFits187 : TypedExpr → Prop
  | .baseCur i | .baseNext i => (i : ℕ) < 13
  | .extCur i | .extNext i =>
      ∀ k : Fin 3, extCoordIndex 3 i k < 187
  | .challenge _ | .publicVal _ | .const _ => True
  | .add x y | .sub x y | .mul x y => TypedTraceFits187 x ∧ TypedTraceFits187 y
  | .neg x | .pow x _ => TypedTraceFits187 x

instance typedTraceFits187Decidable (t : TypedExpr) : Decidable (TypedTraceFits187 t) := by
  induction t <;> simp only [TypedTraceFits187] <;> infer_instance

theorem every_typed_expression_fits_187 (t : TypedExpr) : TypedTraceFits187 t := by
  induction t with
  | baseCur i => exact i.isLt
  | baseNext i => exact i.isLt
  | extCur i =>
      intro k
      exact extCoordIndex_lt (by decide : 0 < 3) i k
  | extNext i =>
      intro k
      exact extCoordIndex_lt (by decide : 0 < 3) i k
  | challenge i => trivial
  | publicVal i => trivial
  | const c => trivial
  | add x y hx hy => exact ⟨hx, hy⟩
  | sub x y hx hy => exact ⟨hx, hy⟩
  | mul x y hx hy => exact ⟨hx, hy⟩
  | neg x hx => exact hx
  | pow x n hx => exact hx

theorem every_load_bearing_typed_body_fits :
    (∀ t ∈ loweredExtTransitionGates, TypedTraceFits187 t) ∧
      (∀ t ∈ loweredEndpointDeg1, TypedTraceFits187 t) ∧
      (∀ t ∈ loweredEndpointDeg3, TypedTraceFits187 t) :=
  ⟨fun t _ => every_typed_expression_fits_187 t,
    fun t _ => every_typed_expression_fits_187 t,
    fun t _ => every_typed_expression_fits_187 t⟩

theorem every_base_body_uses_only_fin13 :
    ∀ g ∈ (baseTransitionGates (F := ℚ)), BaseSupportFits13 g :=
  baseTransitionGates_support

theorem every_nontrace_role_is_in_declared_range :
    (∀ t ∈ loweredExtTransitionGates, TypedSupportFits t) ∧
      (∀ t ∈ loweredEndpointDeg1, TypedSupportFits t) ∧
      (∀ t ∈ loweredEndpointDeg3, TypedSupportFits t) :=
  ⟨loweredExtTransitionGates_support,
    loweredEndpoint_support.1, loweredEndpoint_support.2⟩

def CoeffTraceFits187 {F : Type*} : CoeffExpr F → Prop
  | .const _ => True
  | .var .traceCur i | .var .traceNext i => i < 187
  | .var .challenge _ | .var .publicVal _ => True
  | .add x y | .sub x y | .mul x y => CoeffTraceFits187 x ∧ CoeffTraceFits187 y
  | .neg x | .pow x _ => CoeffTraceFits187 x

theorem coeff_sumList_fits187 {F ι : Type*} [Field F]
    (xs : List ι) (f : ι → CoeffExpr F)
    (h : ∀ i ∈ xs, CoeffTraceFits187 (f i)) :
    CoeffTraceFits187 (CoeffExpr.sumList xs f) := by
  induction xs with
  | nil => trivial
  | cons a xs ih =>
      exact ⟨h a (by simp), ih (fun i hi => h i (by simp [hi]))⟩

theorem mulVec_fits187
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (u v : Fin 3 → CoeffExpr F)
    (hu : ∀ i, CoeffTraceFits187 (u i))
    (hv : ∀ i, CoeffTraceFits187 (v i)) :
    ∀ k, CoeffTraceFits187 (mulVec b u v k) := by
  intro k
  apply coeff_sumList_fits187
  intro i hi
  apply coeff_sumList_fits187
  intro j hj
  exact ⟨⟨hu i, hv j⟩, trivial⟩

theorem powVec_fits187
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (u : Fin 3 → CoeffExpr F)
    (hu : ∀ i, CoeffTraceFits187 (u i)) :
    ∀ n k, CoeffTraceFits187 (powVec b u n k) := by
  intro n
  induction n with
  | zero =>
      intro k
      trivial
  | succ n ih =>
      exact mulVec_fits187 b (powVec b u n) u ih hu

theorem typedCompile_fits187
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (t : TypedExpr) :
    ∀ k, CoeffTraceFits187 (typedCompile b t k) := by
  induction t with
  | baseCur i =>
      intro k
      exact ⟨i.isLt.trans (by decide), trivial⟩
  | baseNext i =>
      intro k
      exact ⟨i.isLt.trans (by decide), trivial⟩
  | extCur i =>
      intro k
      exact extCoordIndex_lt (by decide : 0 < 3) i k
  | extNext i =>
      intro k
      exact extCoordIndex_lt (by decide : 0 < 3) i k
  | challenge i =>
      intro k
      trivial
  | publicVal i =>
      intro k
      trivial
  | const c =>
      intro k
      trivial
  | add x y hx hy =>
      intro k
      exact ⟨hx k, hy k⟩
  | sub x y hx hy =>
      intro k
      exact ⟨hx k, hy k⟩
  | mul x y hx hy =>
      exact mulVec_fits187 b (typedCompile b x) (typedCompile b y) hx hy
  | neg x hx =>
      intro k
      exact hx k
  | pow x n hx =>
      exact powVec_fits187 b (typedCompile b x) hx n

theorem every_compiled_typed_body_avoids_coeffToMv_fallback
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) :
    (∀ t ∈ loweredExtTransitionGates, ∀ k,
        CoeffTraceFits187 (typedCompile b t k)) ∧
      (∀ t ∈ loweredEndpointDeg1, ∀ k,
        CoeffTraceFits187 (typedCompile b t k)) ∧
      (∀ t ∈ loweredEndpointDeg3, ∀ k,
        CoeffTraceFits187 (typedCompile b t k)) :=
  ⟨fun t _ => typedCompile_fits187 b t,
    fun t _ => typedCompile_fits187 b t,
    fun t _ => typedCompile_fits187 b t⟩

/-- The old mixed index 68 is extension role 55, whose last cubic coordinate is 180, not 217. -/
theorem repaired_index68_lowering :
    lower (.Var .traceCur 68) = some (.extCur ⟨55, by decide⟩) ∧
      extCoordIndex 3 ⟨55, by decide⟩ ⟨0, by decide⟩ = 178 ∧
      extCoordIndex 3 ⟨55, by decide⟩ ⟨2, by decide⟩ = 180 ∧
      extCoordIndex 3 ⟨55, by decide⟩ ⟨2, by decide⟩ < 187 := by
  decide

/-- Mixed 12 is the final base role, mixed 13 starts extension role zero, and mixed 70 is role 57.
The next mixed index is rejected rather than replaced by a default expression. -/
theorem exact_mixed_lowering_boundaries :
    lower (.Var .traceCur 12) = some (.baseCur ⟨12, by decide⟩) ∧
      lower (.Var .traceCur 13) = some (.extCur ⟨0, by decide⟩) ∧
      lower (.Var .traceCur 70) = some (.extCur ⟨57, by decide⟩) ∧
      lower (.Var .traceCur 71) = none := by
  decide

theorem final_extension_role_uses_final_three_columns :
    extCoordIndex 3 ⟨57, by decide⟩ ⟨0, by decide⟩ = 184 ∧
      extCoordIndex 3 ⟨57, by decide⟩ ⟨1, by decide⟩ = 185 ∧
      extCoordIndex 3 ⟨57, by decide⟩ ⟨2, by decide⟩ = 186 := by
  decide

theorem extension_role_58_is_impossible :
    ¬ ∃ i : Fin 58, (i : ℕ) = 58 := by
  intro h
  obtain ⟨i, hi⟩ := h
  exact (Nat.ne_of_lt i.isLt) hi

theorem cubic_extension_coordinates_injective :
    Function.Injective
      (fun p : Fin 58 × Fin 3 => extCoordIndex 3 p.1 p.2) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ h
  have hcore : 3 * (i : ℕ) + (k : ℕ) = 3 * (j : ℕ) + (l : ℕ) := by
    simp only [extCoordIndex] at h
    omega
  obtain ⟨hdivi, hmodi⟩ := std_index (e := 3) (i : ℕ) k
  obtain ⟨hdivj, hmodj⟩ := std_index (e := 3) (j : ℕ) l
  have hij : (i : ℕ) = (j : ℕ) := by
    calc
      (i : ℕ) = (3 * (i : ℕ) + (k : ℕ)) / 3 := hdivi.symm
      _ = (3 * (j : ℕ) + (l : ℕ)) / 3 := congrArg (fun n => n / 3) hcore
      _ = (j : ℕ) := hdivj
  have hkl : (k : ℕ) = (l : ℕ) := by
    calc
      (k : ℕ) = (3 * (i : ℕ) + (k : ℕ)) % 3 := hmodi.symm
      _ = (3 * (j : ℕ) + (l : ℕ)) % 3 := congrArg (fun n => n % 3) hcore
      _ = (l : ℕ) := hmodj
  apply Prod.ext
  · exact Fin.ext hij
  · exact Fin.ext hkl

theorem base_and_extension_coordinates_disjoint
    (i : Fin 13) (j : Fin 58) (k : Fin 3) :
    (i : ℕ) ≠ extCoordIndex 3 j k := by
  simp [extCoordIndex]
  omega

/-! ## 2. Evaluation and coordinate compilation in both directions -/

theorem lowering_eval_zero_iff
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : TypedEnv F K) (e : Expr) (t : TypedExpr)
    (h : lower e = some t) :
    e.eval env.toMixedEnv = 0 ↔ t.eval env = 0 := by
  rw [lower_eval env e t h]

theorem all_transition_lowering_eval_iff
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : TypedEnv F K) :
    (∀ t ∈ loweredExtTransitionGates, t.eval env = 0) ↔
      ∀ g ∈ extTransitionGates, g.eval env.toMixedEnv = 0 :=
  loweredExtTransitionGates_eval_iff env

theorem typed_coordinate_compile_zero_iff
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] {e : ℕ} (he : 0 < e)
    (b : Basis (Fin e) F K) (env : TypedEnv F K) (t : TypedExpr) :
    t.eval env = 0 ↔
      ∀ k, (typedCompile b t k).eval (env.toCoeffEnv b) = 0 := by
  rw [eq_iff_coords_eq b (t.eval env) 0]
  constructor
  · intro h k
    rw [← typedCompile_eval he b env t k, h k, coord_zero]
  · intro h k
    rw [coord_zero, typedCompile_eval he b env t k]
    exact h k

theorem lowering_drops_no_gate_and_has_no_typed_collision :
    loweredExtTransitionGates.length = 21 ∧
      loweredExtTransitionGates.length = extTransitionGates.length ∧
      loweredExtTransitionGates.Nodup := by
  decide

/-! ## 3. Exact source and endpoint partitions -/

def stateBlocks : List Expr :=
  [stateBlock .s0, stateBlock .s1, stateBlock .s2, stateBlock .s3,
    stateBlock .s4, stateBlock .s5, stateBlock .s6, stateBlock .s7,
    stateBlock .s8, stateBlock .s9, stateBlock .cons].flatten

theorem exact_511_source_partition :
    Nock.Reified.perStateGated.length = 499 ∧
      refoldedPerStateGates.length = 499 ∧
      stateBlocks = refoldedPerStateGates ∧
      sourceFamilies20.flatten.length = 511 ∧
      nonIOSourceFamilies17.flatten.length = 511 ∧
      sourceFamilies20.flatten.Nodup ∧
      nonIOSourceFamilies17.flatten.Nodup := by
  decide

theorem combined_equation_occurs_exactly_once :
    sourceFamilies20.flatten.count optimizedCombinedGate = 1 ∧
      nonIOSourceFamilies17.flatten.count optimizedCombinedGate = 1 := by
  decide

theorem source_refolding_has_exact_coverage (e : Expr) :
    e ∈ nonIOSourceFamilies17.flatten ↔ e ∈ sourceFamilies20.flatten :=
  nonIO_source_coverage e

theorem source_and_gate_bodies_are_syntactically_nonzero_nodup :
    sourceFamilies20.flatten.Nodup ∧
      nonIOSourceFamilies17.flatten.Nodup ∧
      (baseTransitionGates (F := ℚ)).Nodup ∧
      extTransitionGates.Nodup ∧
      (∀ g ∈ (baseTransitionGates (F := ℚ)), g ≠ .const 0) ∧
      (∀ g ∈ extTransitionGates, g ≠ (.Const 0 : Expr)) := by
  refine ⟨complete_nonIO_source_partition.2.2.1,
    complete_nonIO_source_partition.2.2.2.1, ?_, ?_,
    baseTransitionGates_nonzero, extTransitionGates_nonzero⟩ <;> decide

theorem exact_walk_endpoint_partition :
    optimizedWalkEndpointSources.length = 4 ∧
      optimizedWalkEndpointSources.Nodup ∧
      optimizedWalkEndpointSources.count optimizedWalkLn1 = 1 ∧
      optimizedWalkEndpointSources.count optimizedWalkCount1 = 1 ∧
      optimizedWalkEndpointSources.count optimizedWalkAccInit = 1 ∧
      optimizedWalkEndpointSources.count optimizedWalkOut = 1 ∧
      loweredEndpointDeg1.length = 2 ∧
      loweredEndpointDeg3.length = 1 ∧
      (endpointEqualityChecks (F := ℚ)).length = 2 := by
  decide

/-! ## 4. RLC exactness and negative controls -/

theorem exact_refold_semantics
    {K : Type*} [Field K] (env : Env K)
    (hfree : ∀ es ∈ nonIOSourceFamilies17, CollisionFree env es) :
    (∀ g ∈ nonIOTransitionGates, g.eval env = 0) ↔
      ∀ e ∈ sourceFamilies20.flatten, e.eval env = 0 :=
  nonIOTransitionGates_eval_iff env hfree

theorem cancellation_control_rejects_erasing_the_rlc_premise :
    (rlcFold [.Const 1, .Const (-1)]).eval cancellationEnv = 0 ∧
      ¬ CollisionFree cancellationEnv [.Const 1, .Const (-1)] := by
  refine ⟨cancellation_counterexample.1, ?_⟩
  intro hfree
  exact cancellation_counterexample.2 (hfree cancellation_counterexample.1)

def sourceWithoutCombined : List Expr :=
  sourceFamilies20.flatten.erase optimizedCombinedGate

theorem missing_combined_constituent_control :
    sourceWithoutCombined.length = 510 ∧
      sourceWithoutCombined.Nodup ∧
      optimizedCombinedGate ∉ sourceWithoutCombined ∧
      sourceWithoutCombined ≠ sourceFamilies20.flatten := by
  decide

/-! ## 5. Same-environment row-local rejection controls -/

theorem malformed_selector_rejected
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) (env : TypedEnv F K)
    (hbase : SummaryCollisionFree (env.toCoeffEnv b))
    (hfold : ∀ es ∈ nonIOSourceFamilies17, CollisionFree env.toMixedEnv es)
    (hbad : (selectorOneHot (F := F)).eval (env.toCoeffEnv b) ≠ 0) :
    ¬ TypedRowTransitionSat b env := by
  apply typed_malformed_source_rejected b env hbase hfold
  intro hsource
  exact hbad (hsource.1 selectorOneHot (by simp [baseSourceGates]))

theorem malformed_record_family_rejected
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) (env : TypedEnv F K)
    (hbase : SummaryCollisionFree (env.toCoeffEnv b))
    (hfold : ∀ es ∈ nonIOSourceFamilies17, CollisionFree env.toMixedEnv es)
    (g : Expr) (hg : g ∈ stateBlock .s0) (hbad : g.eval env.toMixedEnv ≠ 0) :
    ¬ TypedRowTransitionSat b env := by
  apply typed_malformed_source_rejected b env hbase hfold
  intro hsource
  apply hbad
  exact hsource.2.1 g (by
    apply List.mem_flatten.mpr
    exact ⟨stateBlock .s0, by simp [sourceFamilies20], hg⟩)

theorem malformed_walk_rejected
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) (env : TypedEnv F K)
    (hbase : SummaryCollisionFree (env.toCoeffEnv b))
    (hfold : ∀ es ∈ nonIOSourceFamilies17, CollisionFree env.toMixedEnv es)
    (hbad : (Trans.walkLnStep.subst walkSubst).eval env.toMixedEnv ≠ 0) :
    ¬ TypedRowTransitionSat b env := by
  apply typed_malformed_source_rejected b env hbase hfold
  intro hsource
  exact hbad (hsource.2.1 _ (by simp [sourceFamilies20]))

theorem malformed_io_rejected
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) (env : TypedEnv F K)
    (hbase : SummaryCollisionFree (env.toCoeffEnv b))
    (hfold : ∀ es ∈ nonIOSourceFamilies17, CollisionFree env.toMixedEnv es)
    (hbad : (legacySampledDenomPin .traceCur 0).eval env.toMixedEnv ≠ 0) :
    ¬ TypedRowTransitionSat b env := by
  apply typed_malformed_source_rejected b env hbase hfold
  intro hsource
  exact hbad (hsource.2.2 _ (by simp [legacySampledIOTransitionGates,
    legacyDenomPinGates]))

/-! ## 6. Actual template, coordinate-expanded RAP, padding, and non-vacuous slices -/

theorem actual_template_fingerprint :
    (compOptimizedTemplate ℚ).rounds = 2 ∧
      (compOptimizedTemplate ℚ).baseCols = 13 ∧
      (compOptimizedTemplate ℚ).extCols = 58 ∧
      (compOptimizedTemplate ℚ).baseTransition.length = 13 ∧
      (compOptimizedTemplate ℚ).extTransition.length = 21 ∧
      (compOptimizedTemplate ℚ).extDeg1.length = 2 ∧
      (compOptimizedTemplate ℚ).extDeg3.length = 1 ∧
      (compOptimizedTemplate ℚ).equalityChecks.length = 2 ∧
      (compOptimizedTemplate ℚ).width 3 = 187 := by
  exact ⟨compOptimizedTemplate_shape.1,
    compOptimizedTemplate_shape.2.1,
    compOptimizedTemplate_shape.2.2.1,
    compOptimizedTemplate_shape.2.2.2.1,
    compOptimizedTemplate_shape.2.2.2.2.1,
    compOptimizedTemplate_shape.2.2.2.2.2.1,
    compOptimizedTemplate_shape.2.2.2.2.2.2.1,
    compOptimizedTemplate_shape.2.2.2.2.2.2.2,
    compOptimizedTemplate_cubic_counts.1⟩

theorem actual_coordinate_gate_count_and_degree
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (b : Basis (Fin 3) F K) :
    (compOptimizedAllGates b).length = 87 ∧
      ∀ g ∈ compOptimizedAllGates b, g.degree ≤ 4 :=
  ⟨compOptimizedAllGates_length b, compOptimizedAllGates_degree b⟩

theorem core_has_only_reviewed_gate_buckets
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (b : Basis (Fin 3) F K) :
    compOptimizedAllGates b =
      baseTransitionGates ++
        compileTypedList b loweredExtTransitionGates ++
        compileTypedList b loweredEndpointDeg1 ++
        compileTypedList b loweredEndpointDeg3 ++
        endpointEqualityChecks :=
  rfl

theorem actual_core_and_padded_rap_fingerprints
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] {h : ℕ} (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    (compOptimizedCoreRAP b chalVal pubVal orbit H).w = 187 ∧
      (compOptimizedCoreRAP b chalVal pubVal orbit H).s = 87 ∧
      (compOptimizedCoreRAP b chalVal pubVal orbit H).k = 2 ∧
      (compOptimizedCoreRAP b chalVal pubVal orbit H).d = 4 ∧
      (compOptimizedPaddedRAP b chalVal pubVal orbit H).w = 199 ∧
      (compOptimizedPaddedRAP b chalVal pubVal orbit H).s = 98 := by
  exact ⟨(compOptimizedCoreRAP_fingerprint b chalVal pubVal orbit H).1,
    (compOptimizedCoreRAP_fingerprint b chalVal pubVal orbit H).2,
    compOptimizedCoreRAP_rounds b chalVal pubVal orbit H, rfl,
    (compOptimizedPaddedRAP_fingerprint b chalVal pubVal orbit H).1,
    (compOptimizedPaddedRAP_fingerprint b chalVal pubVal orbit H).2⟩

theorem actual_padding_satisfaction_iff
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] {h : ℕ} (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) (H : Finset F)
    (P : Fin (compOptimizedPaddedRAP b chalVal pubVal orbit H).w → F[X]) :
    (compOptimizedPaddedRAP b chalVal pubVal orbit H).Satisfies P ↔
      let R := compOptimizedCoreRAP b chalVal pubVal orbit H
      R.Satisfies
        (Nock.NockVMROM.Thm54.RAPPadding.projectTrace R
          (Nock.NockVMROM.Thm54.RAPPadding.firstRoundExtra R (by
              rw [show R.k = 2 from
                compOptimizedCoreRAP_rounds b chalVal pubVal orbit H]
              norm_num)
            (Nock.NockVMROM.Thm54.RAPPadding.computeResidualColumns 3)) P) :=
  compOptimizedPaddedRAP_satisfies_iff b chalVal pubVal orbit H P

theorem repaired_slices_are_concretely_nonvacuous :
    SummaryCollisionFree Nock.RedTeam.Batch56.baseWitnessEnv ∧
      (∀ g ∈ (baseTransitionGates (F := ℚ)),
        g.eval Nock.RedTeam.Batch56.baseWitnessEnv = 0) ∧
      FoldedProgStep3
        (0 : Nock.NockVMROM.Thm54.ConcreteStrictPackage.K73cubic)
        1 1 1 1 1 0 0 := by
  exact ⟨Nock.RedTeam.Batch56.base13_collision_premise_nonvacuous.1,
    Nock.RedTeam.Batch56.base13_collision_premise_nonvacuous.2,
    Nock.RedTeam.Batch55.concrete_op1_safe_denominators_and_acceptance.2.2.2.1⟩

/-! ## 7. Scope guards -/

theorem reviewed_row_iff_stops_at_source_semantics
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) (env : TypedEnv F K)
    (hbase : SummaryCollisionFree (env.toCoeffEnv b))
    (hfold : ∀ es ∈ nonIOSourceFamilies17, CollisionFree env.toMixedEnv es) :
    TypedRowTransitionSat b env ↔
      CompleteSourceRow (env.toCoeffEnv b) env.toMixedEnv :=
  typedRowTransitionSat_iff_completeSource b env hbase hfold

def strict_package_still_requires_B29
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ}
    (P : Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage F K hOrb q Λ) :=
  Nock.RedTeam.Batch53.strict_package_still_requires_B29 P

theorem paper_alias_remains_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch55.paper_alias_is_still_forest

#print axioms every_load_bearing_typed_body_fits
#print axioms every_compiled_typed_body_avoids_coeffToMv_fallback
#print axioms repaired_index68_lowering
#print axioms cubic_extension_coordinates_injective
#print axioms lowering_eval_zero_iff
#print axioms typed_coordinate_compile_zero_iff
#print axioms exact_511_source_partition
#print axioms combined_equation_occurs_exactly_once
#print axioms exact_refold_semantics
#print axioms cancellation_control_rejects_erasing_the_rlc_premise
#print axioms malformed_selector_rejected
#print axioms malformed_record_family_rejected
#print axioms malformed_walk_rejected
#print axioms malformed_io_rejected
#print axioms actual_core_and_padded_rap_fingerprints
#print axioms actual_padding_satisfaction_iff
#print axioms repaired_slices_are_concretely_nonvacuous
#print axioms strict_package_still_requires_B29
#print axioms paper_alias_remains_forest

end
end Nock.RedTeam.Batch57
