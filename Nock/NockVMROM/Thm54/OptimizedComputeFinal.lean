import Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering

/-!
# Final optimized compute RAP with semantic residuals

Three extension columns are used as
residual witnesses for the three degree-four cross-row equations whose literal multiplication by
`1-isLast` would have degree five.  The three residual extension gates pin those witnesses to the
original equations.  The corresponding core transition slots enforce `(1-isLast) * y = 0`, which
is quadratic.  The fourth extension column is the dedicated compute-walk line role.

The two residual base gates split fixed-mask booleanity and endpoint overlap consistency.  This
module constructs the final `199/98`, degree-four RAP directly; it does not use zero-gate padding.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeFinal

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Module
open OptimizedComputeBaseGates
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeTemplate
open OptimizedComputeTypedLowering
open OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open scoped Polynomial

noncomputable section

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-! ## Final Base15 -/

def firstMaskBoolean : CoeffExpr F :=
  .mul isFirstVar (.sub (.const 1) isFirstVar)

def lastMaskBoolean : CoeffExpr F :=
  .mul isLastVar (.sub (.const 1) isLastVar)

/-- The endpoint masks overlap exactly in the singleton case and are disjoint otherwise. -/
def endpointOverlapConsistency (n : ℕ) : CoeffExpr F :=
  if n = 1 then
    .sub (.mul isFirstVar isLastVar) (.const 1)
  else
    .mul isFirstVar isLastVar

def finalSelectorPublicCheck (kind : VarKind) (publicBase : ℕ) : CoeffExpr F :=
  CoeffExpr.sumList (List.range 11) fun i =>
    .mul (.pow (.var .challenge finalScalarChallengeBase) i)
      (.sub (.var kind i) (.var .publicVal (publicBase + i)))

/-- **The compressed endpoint equality checks, retained and no longer committed.**

Two gates, each folding eleven distinct column-vs-public equalities against powers of the scalar
coin `finalScalarChallengeBase = 36`.

The compression is **lossy in the usual direction**: the twenty-two individual gates force these
two (`decompressed_forces_compressed`), and the converse needs a good coin — which is exactly the
`20/|𝔽|` charge the replacement deletes. -/
def finalMaskedEndpointEqualityChecks : List (CoeffExpr F) :=
  [.mul isFirstVar (finalSelectorPublicCheck .traceCur 20),
    .mul isLastVar (finalSelectorPublicCheck .traceCur 31)]

@[simp] theorem finalMaskedEndpointEqualityChecks_length :
    (finalMaskedEndpointEqualityChecks (F := F)).length = 2 := rfl

/-- One masked column-vs-public equality: `mask · (traceCur i − publicVal (base + i)) = 0`. -/
def endpointEqualityCheck (mask : CoeffExpr F) (publicBase i : ℕ) : CoeffExpr F :=
  .mul mask (.sub (.var .traceCur i) (.var .publicVal (publicBase + i)))

/-- **The de-compressed endpoint equality checks: twenty-two individually-tagged equations.**

The two compressed gates above are
replaced here by the eleven equations each one folded.

Degree goes **down**: `mask · diff` is degree `2`, against `mask · χⁱ · diff` at degree `i + 2`
before the coin was fixed. -/
def finalEndpointEqualityChecks : List (CoeffExpr F) :=
  (List.range 11).map (endpointEqualityCheck isFirstVar 20) ++
    (List.range 11).map (endpointEqualityCheck isLastVar 31)

@[simp] theorem finalEndpointEqualityChecks_length :
    (finalEndpointEqualityChecks (F := F)).length = 22 := by
  simp [finalEndpointEqualityChecks]

theorem endpointEqualityCheck_degree (mask : CoeffExpr F) (hmask : mask.degree ≤ 1)
    (publicBase i : ℕ) :
    (endpointEqualityCheck mask publicBase i).degree ≤ 2 := by
  simp only [endpointEqualityCheck, CoeffExpr.degree]
  have : (max 1 0 : ℕ) = 1 := by decide
  omega

theorem finalEndpointEqualityChecks_degree :
    ∀ g ∈ (finalEndpointEqualityChecks (F := F)), g.degree ≤ 2 := by
  intro g hg
  simp only [finalEndpointEqualityChecks, List.mem_append, List.mem_map,
    List.mem_range] at hg
  rcases hg with ⟨i, _, rfl⟩ | ⟨i, _, rfl⟩
  · exact endpointEqualityCheck_degree _ (by simp [isFirstVar, bv, CoeffExpr.degree]) _ _
  · exact endpointEqualityCheck_degree _ (by simp [isLastVar, bv, CoeffExpr.degree]) _ _

/-- **The de-compressed gates force the compressed ones, at every coin value.**

This is the licence for the replacement, and it is the compute analogue of
`MixedCoordinateCompiler.mixedCompile_zero_iff` on the memory side: the committed
chip enforces at least what the compressed chip did, with no randomness.  The converse is false
without a good coin, which is what `finalSelectorBadChallenges` priced. -/
theorem decompressed_forces_compressed (env : Env F)
    (h : ∀ g ∈ (finalEndpointEqualityChecks (F := F)), g.eval env = 0) :
    ∀ g ∈ (finalMaskedEndpointEqualityChecks (F := F)), g.eval env = 0 := by
  have hmem (mask : CoeffExpr F) (base : ℕ) (i : ℕ) (hi : i < 11)
      (hin : endpointEqualityCheck mask base i ∈ (finalEndpointEqualityChecks (F := F))) :
      mask.eval env * (env.trace i - env.pub (base + i)) = 0 := by
    simpa [endpointEqualityCheck, CoeffExpr.eval] using h _ hin
  have hfirst : ∀ i < 11,
      (isFirstVar (F := F)).eval env * (env.trace i - env.pub (20 + i)) = 0 := by
    intro i hi
    refine hmem _ _ i hi ?_
    simp only [finalEndpointEqualityChecks, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl ⟨i, hi, rfl⟩
  have hlast : ∀ i < 11,
      (isLastVar (F := F)).eval env * (env.trace i - env.pub (31 + i)) = 0 := by
    intro i hi
    refine hmem _ _ i hi ?_
    simp only [finalEndpointEqualityChecks, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inr ⟨i, hi, rfl⟩
  intro g hg
  simp only [finalMaskedEndpointEqualityChecks, List.mem_cons, List.not_mem_nil,
    or_false] at hg
  have expand (base : ℕ) (mask : CoeffExpr F)
      (hall : ∀ i < 11, mask.eval env * (env.trace i - env.pub (base + i)) = 0) :
      (CoeffExpr.mul mask (finalSelectorPublicCheck (F := F) .traceCur base)).eval env = 0 := by
    have h0 := hall 0 (by norm_num); have h1 := hall 1 (by norm_num)
    have h2 := hall 2 (by norm_num); have h3 := hall 3 (by norm_num)
    have h4 := hall 4 (by norm_num); have h5 := hall 5 (by norm_num)
    have h6 := hall 6 (by norm_num); have h7 := hall 7 (by norm_num)
    have h8 := hall 8 (by norm_num); have h9 := hall 9 (by norm_num)
    have h10 := hall 10 (by norm_num)
    simp only [CoeffExpr.eval, finalSelectorPublicCheck, CoeffExpr.eval_sumList,
      List.range, List.range.loop]
    simp only [List.map, List.sum_cons, List.sum_nil, CoeffExpr.eval] at *
    ring_nf
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    linear_combination h0 + env.chal finalScalarChallengeBase * h1 +
      env.chal finalScalarChallengeBase ^ 2 * h2 +
      env.chal finalScalarChallengeBase ^ 3 * h3 +
      env.chal finalScalarChallengeBase ^ 4 * h4 +
      env.chal finalScalarChallengeBase ^ 5 * h5 +
      env.chal finalScalarChallengeBase ^ 6 * h6 +
      env.chal finalScalarChallengeBase ^ 7 * h7 +
      env.chal finalScalarChallengeBase ^ 8 * h8 +
      env.chal finalScalarChallengeBase ^ 9 * h9 +
      env.chal finalScalarChallengeBase ^ 10 * h10
  rcases hg with rfl | rfl
  · exact expand 20 _ hfirst
  · exact expand 31 _ hlast

theorem finalSelectorPublicCheck_degree (kind : VarKind) (publicBase : ℕ) :
    (finalSelectorPublicCheck (F := F) kind publicBase).degree ≤ 1 := by
  apply CoeffExpr.degree_sumList_le
  intro i hi
  cases kind <;> simp [CoeffExpr.degree]

theorem finalMaskedEndpointEqualityChecks_degree :
    ∀ g ∈ (finalMaskedEndpointEqualityChecks (F := F)), g.degree ≤ 2 := by
  intro g hg
  simp only [finalMaskedEndpointEqualityChecks, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · simp only [CoeffExpr.degree, isFirstVar, bv]
    exact Nat.add_le_add_right
      (finalSelectorPublicCheck_degree (F := F) .traceCur 20) 1
  · simp only [CoeffExpr.degree, isLastVar, bv]
    exact Nat.add_le_add_right
      (finalSelectorPublicCheck_degree (F := F) .traceCur 31) 1

/-- **The licence for deleting the `20/|𝔽|` collision charge.**

Wherever the mask is nonzero — which is exactly the row the check is about — the de-compressed
gates determine the eleven column-vs-public equations outright, with **no coin**.  The compressed
gate could not: recovering those equations from `finalSelectorPublicCheck` required
`challenge36` to miss `OptimizedComputeCollisionBound.finalSelectorBadChallenges`
(`selector_sources_zero_of_good`), and that exclusion is precisely what was priced at `20/|𝔽|`. -/
theorem endpointEqualityChecks_determine_public (env : Env F) (publicBase : ℕ)
    (mask : CoeffExpr F) (hmask : mask.eval env ≠ 0)
    (h : ∀ i, i < 11 → (endpointEqualityCheck mask publicBase i).eval env = 0) :
    ∀ i, i < 11 → env.trace i = env.pub (publicBase + i) := by
  intro i hi
  have hgate := h i hi
  simp only [endpointEqualityCheck, CoeffExpr.eval, mul_eq_zero, sub_eq_zero] at hgate
  exact hgate.resolve_left hmask

/-- Eleven selector booleanities, one-hotness, two fixed-mask booleanities, and exact overlap. -/
def finalBaseTransitionGates (n : ℕ) : List (CoeffExpr F) :=
  (List.range 11).map selectorBool ++
    [selectorOneHot, firstMaskBoolean, lastMaskBoolean, endpointOverlapConsistency n]

@[simp] theorem finalBaseTransitionGates_length (n : ℕ) :
    (finalBaseTransitionGates (F := F) n).length = 15 := by
  simp [finalBaseTransitionGates]

theorem finalBaseTransitionGates_degree (n : ℕ) :
    ∀ g ∈ (finalBaseTransitionGates (F := F) n), g.degree ≤ 2 := by
  intro g hg
  simp only [finalBaseTransitionGates, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ⟨i, hi, rfl⟩ | rfl | rfl | rfl | rfl
  · simp [selectorBool, bv, CoeffExpr.degree]
  · exact (maskedBaseTransitionGates_degree selectorOneHot (by
      simp [maskedBaseTransitionGates])).trans (by decide)
  · simp [firstMaskBoolean, isFirstVar, bv, CoeffExpr.degree]
  · simp [lastMaskBoolean, isLastVar, bv, CoeffExpr.degree]
  · by_cases hn : n = 1 <;>
      simp [endpointOverlapConsistency, hn, isFirstVar, isLastVar, bv, CoeffExpr.degree]

/-! ## Residual extension columns and gates -/

abbrev CoreExtGateId := Fin 21
abbrev ResidualWitnessId := Fin 3
abbrev FinalExtensionColumn := Fin 62

/-- Scalar coordinate of final extension role `i`. -/
def finalExtCoordIndex (i : FinalExtensionColumn) (k : Fin 3) : Fin 199 :=
  ⟨13 + 3 * (i : ℕ) + (k : ℕ), by omega⟩

/-- The three semantic residual witnesses occupy extension roles 58, 59, and 60. -/
def residualWitnessRole (j : ResidualWitnessId) : FinalExtensionColumn :=
  ⟨58 + (j : ℕ), by omega⟩

/-- Extension role 61 is the dedicated compute-walk line. -/
def walkLineRole : FinalExtensionColumn := 61

def inertResidualRole : FinalExtensionColumn := 61

theorem residual_resource_partition :
    (∀ j : ResidualWitnessId, (residualWitnessRole j : ℕ) < 61) ∧
      (walkLineRole : ℕ) = 61 ∧
      Fintype.card ResidualWitnessId = 3 ∧
      Fintype.card FinalExtensionColumn = 62 := by
  constructor
  · intro j
    fin_cases j <;> norm_num [residualWitnessRole]
  · norm_num [walkLineRole]

def oldExtGate (i : CoreExtGateId) : TypedExpr :=
  loweredExtTransitionGates.get ⟨i, by simpa using i.isLt⟩

def finalExtGate (i : CoreExtGateId) : FinalTypedExpr :=
  finalLoweredExtTransitionGates.get ⟨i, by simpa using i.isLt⟩

/-- Walk-count, walk-accumulator, and sampled-IO are the exact three degree-four cross-row
residuals. -/
def residualSource : ResidualWitnessId → TypedExpr
  | 0 => oldExtGate 10
  | 1 => oldExtGate 11
  | 2 => oldExtGate 20

def finalResidualSource : ResidualWitnessId → FinalTypedExpr
  | 0 => finalExtGate 10
  | 1 => finalExtGate 11
  | 2 => finalExtGate 20

theorem residual_source_degree_census :
    (residualSource 0).degree = 4 ∧
      (residualSource 1).degree = 4 ∧
      (residualSource 2).degree = 4 ∧
      (oldExtGate 8).degree = 1 ∧
      (oldExtGate 9).degree = 1 := by
  decide

/-- There are three degree-four residuals but two additional linear cross-row equations.  Both
linear equations are masked directly; neither consumes an auxiliary column. -/
theorem exact_cross_row_mask_census :
    Fintype.card ResidualWitnessId = 3 ∧
      ({8, 9} : Finset CoreExtGateId).card = 2 := by
  decide

def notLastCoeff : CoeffExpr F :=
  .sub (.const 1) isLastVar

def residualWitnessCoord (j : ResidualWitnessId) (k : Fin 3) : CoeffExpr F :=
  .var .traceCur (finalExtCoordIndex (residualWitnessRole j) k)

/-- The modified 21-gate core.  Slots 8 and 9 are the two safe linear cross-row equations and are
masked directly. -/
def finalCoreExtGateCoord (b : Basis (Fin 3) F K)
    (i : CoreExtGateId) (k : Fin 3) : CoeffExpr F :=
  if i = 10 then
    .mul notLastCoeff (residualWitnessCoord 0 k)
  else if i = 11 then
    .mul notLastCoeff (residualWitnessCoord 1 k)
  else if i = 20 then
    .mul notLastCoeff (residualWitnessCoord 2 k)
  else if i = 8 ∨ i = 9 then
    .mul notLastCoeff (finalTypedCompile b (finalExtGate i) k)
  else
    finalTypedCompile b (finalExtGate i) k

/-- One residual extension gate pins one extension-valued witness to its original degree-four
equation. -/
def residualAuxGateCoord (b : Basis (Fin 3) F K)
    (j : ResidualWitnessId) (k : Fin 3) : CoeffExpr F :=
  .sub (residualWitnessCoord j k) (finalTypedCompile b (finalResidualSource j) k)

def compileFinalCoreExt (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  (List.ofFn fun i : CoreExtGateId =>
    List.ofFn fun k : Fin 3 => finalCoreExtGateCoord b i k).flatten

def compileResidualAux (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  (List.ofFn fun j : ResidualWitnessId =>
    List.ofFn fun k : Fin 3 => residualAuxGateCoord b j k).flatten

@[simp] theorem compileFinalCoreExt_length (b : Basis (Fin 3) F K) :
    (compileFinalCoreExt b).length = 63 := by
  simp [compileFinalCoreExt]

@[simp] theorem compileResidualAux_length (b : Basis (Fin 3) F K) :
    (compileResidualAux b).length = 9 := by
  simp [compileResidualAux]

theorem finalCoreExtGateCoord_degree (b : Basis (Fin 3) F K)
    (i : CoreExtGateId) (k : Fin 3) :
    (finalCoreExtGateCoord b i k).degree ≤ 4 := by
  by_cases h10 : i = 10
  · subst i
    simp [finalCoreExtGateCoord, notLastCoeff, residualWitnessCoord, isLastVar, bv,
      CoeffExpr.degree]
  by_cases h11 : i = 11
  · subst i
    simp [finalCoreExtGateCoord, notLastCoeff, residualWitnessCoord, isLastVar, bv,
      CoeffExpr.degree]
  by_cases h20 : i = 20
  · subst i
    simp [finalCoreExtGateCoord, notLastCoeff, residualWitnessCoord, isLastVar, bv,
      CoeffExpr.degree]
  by_cases hsafe : i = 8 ∨ i = 9
  · have htyped : (finalTypedCompile b (finalExtGate i) k).degree ≤ 3 := by
      rcases hsafe with rfl | rfl <;>
        exact (finalTypedCompile_degree_le b _ k).trans (by decide)
    simp only [finalCoreExtGateCoord, h10, h11, h20, hsafe, if_false, if_true,
      CoeffExpr.degree]
    exact Nat.add_le_add (by simp [notLastCoeff, isLastVar, bv, CoeffExpr.degree]) htyped
  · simp only [finalCoreExtGateCoord, h10, h11, h20, hsafe, if_false]
    exact (finalTypedCompile_degree_le b (finalExtGate i) k).trans
      (finalLoweredExtTransitionGates_degree _ (List.get_mem _ _))

theorem residualAuxGateCoord_degree (b : Basis (Fin 3) F K)
    (j : ResidualWitnessId) (k : Fin 3) :
    (residualAuxGateCoord b j k).degree ≤ 4 := by
  have hsource : (finalResidualSource j).degree ≤ 4 := by
    fin_cases j <;> decide
  simp only [residualAuxGateCoord, CoeffExpr.degree]
  exact max_le (by simp [residualWitnessCoord, CoeffExpr.degree])
    ((finalTypedCompile_degree_le b (finalResidualSource j) k).trans hsource)

theorem compileFinalCoreExt_degree (b : Basis (Fin 3) F K) :
    ∀ g ∈ compileFinalCoreExt b, g.degree ≤ 4 := by
  intro g hg
  rw [compileFinalCoreExt] at hg
  obtain ⟨xs, hxs, hg⟩ := List.mem_flatten.mp hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hxs
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
  exact finalCoreExtGateCoord_degree b i k

theorem compileResidualAux_degree (b : Basis (Fin 3) F K) :
    ∀ g ∈ compileResidualAux b, g.degree ≤ 4 := by
  intro g hg
  rw [compileResidualAux] at hg
  obtain ⟨xs, hxs, hg⟩ := List.mem_flatten.mp hg
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hxs
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
  exact residualAuxGateCoord_degree b j k

/-! ## Exact auxiliary semantics -/

theorem residual_aux_masked_iff_original (b : Basis (Fin 3) F K)
    (env : Env F) (j : ResidualWitnessId)
    (haux : ∀ k : Fin 3, (residualAuxGateCoord b j k).eval env = 0) :
    (∀ k : Fin 3,
        (CoeffExpr.mul notLastCoeff (residualWitnessCoord j k)).eval env = 0) ↔
      ∀ k : Fin 3,
        (CoeffExpr.mul notLastCoeff
          (finalTypedCompile b (finalResidualSource j) k)).eval env = 0 := by
  constructor
  · intro hmask k
    have hy : (residualWitnessCoord j k).eval env =
        (finalTypedCompile b (finalResidualSource j) k).eval env := by
      simpa [residualAuxGateCoord, CoeffExpr.eval, sub_eq_zero] using haux k
    simpa [CoeffExpr.eval, hy] using hmask k
  · intro horiginal k
    have hy : (residualWitnessCoord j k).eval env =
        (finalTypedCompile b (finalResidualSource j) k).eval env := by
      simpa [residualAuxGateCoord, CoeffExpr.eval, sub_eq_zero] using haux k
    simpa [CoeffExpr.eval, hy] using horiginal k

theorem wrong_residual_aux_rejected (b : Basis (Fin 3) F K)
    (env : Env F) (j : ResidualWitnessId) (k : Fin 3)
    (hwrong : (residualWitnessCoord j k).eval env ≠
      (finalTypedCompile b (finalResidualSource j) k).eval env) :
    (residualAuxGateCoord b j k).eval env ≠ 0 := by
  simpa [residualAuxGateCoord, CoeffExpr.eval, sub_eq_zero] using hwrong

/-! ## Final direct RAP -/

def finalComputeAllGates (n : ℕ) (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  finalBaseTransitionGates n ++
    compileFinalCoreExt b ++
    compileResidualAux b ++
    compileFinalTypedList b finalLoweredMaskedEndpointDeg2 ++
    compileFinalTypedList b finalLoweredMaskedEndpointDeg4 ++
    finalEndpointEqualityChecks

@[simp] theorem finalComputeAllGates_length (n : ℕ) (b : Basis (Fin 3) F K) :
    (finalComputeAllGates n b).length = 118 := by
  simp [finalComputeAllGates, compileFinalTypedList_length, finalLoweredMaskedEndpoint_counts,
    finalEndpointEqualityChecks]

theorem finalComputeAllGates_degree (n : ℕ) (b : Basis (Fin 3) F K) :
    ∀ g ∈ finalComputeAllGates n b, g.degree ≤ 4 := by
  intro g hg
  simp only [finalComputeAllGates, List.mem_append] at hg
  rcases hg with ((((hb | hc) | ha) | h2) | h4) | heq
  · exact (finalBaseTransitionGates_degree n g hb).trans (by decide)
  · exact compileFinalCoreExt_degree b g hc
  · exact compileResidualAux_degree b g ha
  · exact (compileFinalTypedList_degree b finalLoweredMaskedEndpointDeg2 2
      finalLoweredMaskedEndpoint_degrees.1 g h2).trans (by decide)
  · exact compileFinalTypedList_degree b finalLoweredMaskedEndpointDeg4 4
      finalLoweredMaskedEndpoint_degrees.2 g h4
  · exact (finalEndpointEqualityChecks_degree g heq).trans (by decide)

theorem final_resource_census (n : ℕ) (b : Basis (Fin 3) F K) :
    (finalBaseTransitionGates (F := F) n).length = 15 ∧
      (compileFinalCoreExt b).length = 21 * 3 ∧
      (compileResidualAux b).length = 3 * 3 ∧
      (compileFinalTypedList b finalLoweredMaskedEndpointDeg2).length = 2 * 3 ∧
      (compileFinalTypedList b finalLoweredMaskedEndpointDeg4).length = 1 * 3 ∧
      (finalEndpointEqualityChecks (F := F)).length = 22 ∧
      (finalComputeAllGates n b).length = 118 := by
  simp [compileFinalTypedList_length, finalLoweredMaskedEndpoint_counts]

theorem residualAuxGateCoord_mem_final (n : ℕ) (b : Basis (Fin 3) F K)
    (j : ResidualWitnessId) (k : Fin 3) :
    residualAuxGateCoord b j k ∈ finalComputeAllGates n b := by
  have hinner :
      residualAuxGateCoord b j k ∈
        List.ofFn (fun q : Fin 3 => residualAuxGateCoord b j q) :=
    List.mem_ofFn.mpr ⟨k, rfl⟩
  have houter :
      List.ofFn (fun q : Fin 3 => residualAuxGateCoord b j q) ∈
        List.ofFn (fun r : ResidualWitnessId =>
          List.ofFn fun q : Fin 3 => residualAuxGateCoord b r q) :=
    List.mem_ofFn.mpr ⟨j, rfl⟩
  have haux : residualAuxGateCoord b j k ∈ compileResidualAux b := by
    rw [compileResidualAux]
    exact List.mem_flatten.mpr ⟨_, houter, hinner⟩
  simp only [finalComputeAllGates, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr haux)))

def finalComputeRAP {h n : ℕ} (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (H : Finset F) : RAP F where
  e := 3
  k := 2
  wRAP := ![296, 6]
  w := 302
  w_eq := by rw [Fin.sum_univ_two]; norm_num
  h := h
  d := 4
  s := (finalComputeAllGates n b).length
  ω := orbit.ω
  β := orbit.βcoset
  I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
  C := fun i => coeffToMv chalVal pubVal ((finalComputeAllGates n b).get i)
  C_vars := fun i => coeffToMv_vars chalVal pubVal _
  C_deg := fun i =>
    (coeffToMv_totalDegree_le chalVal pubVal _).trans
      (finalComputeAllGates_degree n b _ (List.get_mem _ _))
  H := H
  β_ne_zero := orbit.βcoset_ne_zero
  I_bound := by
    intro q hq
    have hq2 : q.2 = 0 ∨ q.2 = 1 := by
      have h2 := (Finset.mem_product.mp hq).2
      simpa [Finset.mem_insert, Finset.mem_singleton] using h2
    have hge : 2 ≤ 2 ^ h := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) orbit.h_pos
    rcases hq2 with hq' | hq' <;> rw [hq'] <;> omega

def finalFixedPreprocessingRAP {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) :
    FixedPreprocessingRAP F where
  rap := finalComputeRAP (n := n) b chalVal pubVal orbit (rowNodeSet nodes)
  rounds_pos := by norm_num [finalComputeRAP]
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨11 + (j : ℕ), by
        change 11 + (j : ℕ) < 296
        omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

/-- Strict-package-facing name for the final compute RAP.  Unlike raw `RAP`, this object carries
the verifier-fixed endpoint preprocessing assignment. -/
abbrev NamedComputeRAP := @finalFixedPreprocessingRAP

def finalFirstFixedId {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) :
    Fin (NamedComputeRAP hn nodes b chalVal pubVal orbit).fixedCount :=
  ⟨0, by simp [finalFixedPreprocessingRAP]⟩

def FinalComputeCompiledLanguage {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (finalFixedPreprocessingRAP hn nodes b chalVal pubVal orbit).rap.w → F[X]) : Prop :=
  (finalFixedPreprocessingRAP hn nodes b chalVal pubVal orbit).BindsPreprocessing P ∧
    ∀ x ∈ rowNodeSet nodes, ∀ g ∈ finalComputeAllGates n b,
      g.eval (envOfTrace P orbit.ω x chalVal pubVal) = 0

theorem finalComputeRAP_fingerprint {h n : ℕ}
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    (finalComputeRAP (n := n) b chalVal pubVal orbit H).w = 302 ∧
      (finalComputeRAP (n := n) b chalVal pubVal orbit H).s = 118 ∧
      (finalComputeRAP (n := n) b chalVal pubVal orbit H).d = 4 :=
  ⟨rfl, finalComputeAllGates_length n b, rfl⟩

theorem finalFixedPreprocessingRAP_satisfies_iff_allRows {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (finalFixedPreprocessingRAP hn nodes b chalVal pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing
        (finalFixedPreprocessingRAP hn nodes b chalVal pubVal orbit) P ↔
      (finalFixedPreprocessingRAP hn nodes b chalVal pubVal orbit).BindsPreprocessing P ∧
        ∀ x ∈ rowNodeSet nodes, ∀ g ∈ finalComputeAllGates n b,
          g.eval (envOfTrace P orbit.ω x chalVal pubVal) = 0 := by
  let R := finalFixedPreprocessingRAP hn nodes b chalVal pubVal orbit
  have key : ∀ (i : Fin R.rap.s) (x : F),
      (R.rap.compose P i).eval x =
        ((finalComputeAllGates n b).get i).eval
          (envOfTrace P orbit.ω x chalVal pubVal) := by
    intro i x
    rw [Reify.compose_eval]
    exact eval_coeffToMv P orbit.ω x chalVal pubVal _
  constructor
  · rintro ⟨hraw, hfixed⟩
    refine ⟨hfixed, ?_⟩
    intro x hx g hg
    obtain ⟨i, hget⟩ := List.mem_iff_get.mp hg
    have hz := hraw i x hx
    rw [key i x] at hz
    rwa [← hget]
  · rintro ⟨hfixed, hall⟩
    refine ⟨?_, hfixed⟩
    intro i x hx
    rw [key i x]
    exact hall x hx _ (List.get_mem _ _)

theorem namedComputeRAP_satisfies_iff_compiledLanguage {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (NamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing
        (NamedComputeRAP hn nodes b chalVal pubVal orbit) P ↔
      FinalComputeCompiledLanguage hn nodes b chalVal pubVal orbit P := by
  exact finalFixedPreprocessingRAP_satisfies_iff_allRows
    hn nodes b chalVal pubVal orbit P

theorem final_wrong_first_mask_rejected {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (NamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w → F[X])
    (hwrong :
      P ((NamedComputeRAP hn nodes b chalVal pubVal orbit).preprocessingColumn
        (finalFirstFixedId hn nodes b chalVal pubVal orbit)) ≠ firstRowMask nodes) :
    ¬ RAP.SatisfiesWithPreprocessing
      (NamedComputeRAP hn nodes b chalVal pubVal orbit) P := by
  apply RAP.not_satisfiesWithPreprocessing_of_wrong
    (NamedComputeRAP hn nodes b chalVal pubVal orbit) P
      (finalFirstFixedId hn nodes b chalVal pubVal orbit)
  exact hwrong

theorem final_not_satisfies_of_gate_nonzero {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (finalFixedPreprocessingRAP hn nodes b chalVal pubVal orbit).rap.w → F[X])
    (x : F) (hx : x ∈ rowNodeSet nodes)
    (g : CoeffExpr F) (hg : g ∈ finalComputeAllGates n b)
    (hbad : g.eval (envOfTrace P orbit.ω x chalVal pubVal) ≠ 0) :
    ¬ RAP.SatisfiesWithPreprocessing
      (finalFixedPreprocessingRAP hn nodes b chalVal pubVal orbit) P := by
  intro hsat
  have hall := ((finalFixedPreprocessingRAP_satisfies_iff_allRows
    hn nodes b chalVal pubVal orbit P).1 hsat).2
  exact hbad (hall x hx g hg)

theorem final_wrong_residual_aux_rejected {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (finalFixedPreprocessingRAP hn nodes b chalVal pubVal orbit).rap.w → F[X])
    (x : F) (hx : x ∈ rowNodeSet nodes) (j : ResidualWitnessId) (k : Fin 3)
    (hwrong :
      (residualWitnessCoord j k).eval (envOfTrace P orbit.ω x chalVal pubVal) ≠
        (finalTypedCompile b (finalResidualSource j) k).eval
          (envOfTrace P orbit.ω x chalVal pubVal)) :
    ¬ RAP.SatisfiesWithPreprocessing
      (finalFixedPreprocessingRAP hn nodes b chalVal pubVal orbit) P := by
  apply final_not_satisfies_of_gate_nonzero hn nodes b chalVal pubVal orbit P x hx
    (residualAuxGateCoord b j k) (residualAuxGateCoord_mem_final n b j k)
  exact wrong_residual_aux_rejected b
    (envOfTrace P orbit.ω x chalVal pubVal) j k hwrong

theorem final_wrong_selector_rejected {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (NamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w → F[X])
    (x : F) (hx : x ∈ rowNodeSet nodes)
    (hbad : selectorOneHot.eval (envOfTrace P orbit.ω x chalVal pubVal) ≠ 0) :
    ¬ RAP.SatisfiesWithPreprocessing
      (NamedComputeRAP hn nodes b chalVal pubVal orbit) P := by
  apply final_not_satisfies_of_gate_nonzero hn nodes b chalVal pubVal orbit P x hx
    selectorOneHot
  · simp [finalComputeAllGates, finalBaseTransitionGates]
  · exact hbad

def finalTerminalTyped : FinalTypedExpr :=
  finalLoweredMaskedEndpointDeg2.get
    ⟨1, finalLoweredMaskedEndpoint_counts.1 ▸ by decide⟩

theorem finalTerminalTyped_eq :
    finalTerminalTyped = lowerFinalTotal finalMaskedWalkOut := by
  decide

theorem final_wrong_terminal_rejected {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (NamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w → F[X])
    (x : F) (hx : x ∈ rowNodeSet nodes) (k : Fin 3)
    (hbad : (finalTypedCompile b finalTerminalTyped k).eval
      (envOfTrace P orbit.ω x chalVal pubVal) ≠ 0) :
    ¬ RAP.SatisfiesWithPreprocessing
      (NamedComputeRAP hn nodes b chalVal pubVal orbit) P := by
  have hterminal :
      finalTypedCompile b finalTerminalTyped k ∈
        compileFinalTypedList b finalLoweredMaskedEndpointDeg2 := by
    apply List.mem_flatten.mpr
    refine ⟨List.ofFn (fun q : Fin 3 => finalTypedCompile b finalTerminalTyped q), ?_, ?_⟩
    · apply List.mem_map.mpr
      exact ⟨finalTerminalTyped, List.get_mem _ _, rfl⟩
    · exact List.mem_ofFn.mpr ⟨k, rfl⟩
  apply final_not_satisfies_of_gate_nonzero hn nodes b chalVal pubVal orbit P x hx
    (finalTypedCompile b finalTerminalTyped k)
  · simp only [finalComputeAllGates, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hterminal))
  · exact hbad

/-- Coin mutation is a residual-source mutation in the sampled-IO slot. -/
theorem final_wrong_coin_rejected {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (NamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w → F[X])
    (x : F) (hx : x ∈ rowNodeSet nodes) (k : Fin 3)
    (hwrong :
      (residualWitnessCoord 2 k).eval (envOfTrace P orbit.ω x chalVal pubVal) ≠
        (finalTypedCompile b (finalResidualSource 2) k).eval
          (envOfTrace P orbit.ω x chalVal pubVal)) :
    ¬ RAP.SatisfiesWithPreprocessing
      (NamedComputeRAP hn nodes b chalVal pubVal orbit) P :=
  final_wrong_residual_aux_rejected hn nodes b chalVal pubVal orbit P x hx 2 k hwrong

#print axioms finalBaseTransitionGates_degree
#print axioms residual_source_degree_census
#print axioms exact_cross_row_mask_census
#print axioms residual_aux_masked_iff_original
#print axioms wrong_residual_aux_rejected
#print axioms final_resource_census
#print axioms finalComputeRAP_fingerprint
#print axioms finalFixedPreprocessingRAP_satisfies_iff_allRows
#print axioms namedComputeRAP_satisfies_iff_compiledLanguage
#print axioms final_wrong_first_mask_rejected
#print axioms final_wrong_residual_aux_rejected
#print axioms final_wrong_selector_rejected
#print axioms final_wrong_terminal_rejected
#print axioms final_wrong_coin_rejected

end
end OptimizedComputeFinal
end Nock.NockVMROM.Thm54
