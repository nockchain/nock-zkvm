import Nock.RedTeam.Batch57Thm54OptimizedComputeTemplateRepair
import Nock.NockVMROM.Thm54.OptimizedComputeFinal
import Nock.NockVMROM.Thm54.OptimizedComputeAllRowsObstruction

/-!
* two polynomial-bound Lagrange endpoint masks in the designated first-round prefix;
* three degree-four semantic residuals carried by extension roles 58--60, with exact auxiliary pins;
* two directly masked linear cross-row equations and two additional load-bearing base equations;
* the direct `199/98`, degree-four, two-round final RAP and its same-object all-row compiled-language
  biconditional;
* malformed mask, auxiliary, selector, terminal, and sampled-coin controls.

The endpoint-mask, residual,
resource, and malformed-input controls below are retained and updated only to elaborate against
that typed production surface.

The right side remains the complete
compiled gate list, not a decoded same-execution `Vcomp`/walk/sampled-IO theorem.
-/

namespace Nock.RedTeam.Batch58

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Module
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeAllRowsObstruction
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedComputeTypedLowering
open Nock.NockVMROM.Thm54.RAPPadding
open Nock.NockVMROM.Thm54.StrictExtension
open scoped Polynomial

noncomputable section

abbrev F73 := ZMod 73

abbrev HistoricalFinalTypedExpr := FinalTypedExpr

abbrev historicalFinalTypedCompile := @finalTypedCompile

abbrev HistoricalNamedComputeRAP := @NamedComputeRAP

/-! ## 1. Fixed preprocessing and exact endpoint semantics -/

def nodes01 : Fin 2 → F73
  | 0 => 0
  | 1 => 1

def nodes10 : Fin 2 → F73
  | 0 => 1
  | 1 => 0

theorem nodes01_injective : Function.Injective nodes01 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [nodes01] at hij ⊢

theorem nodes10_injective : Function.Injective nodes10 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [nodes10] at hij ⊢

/-- On the ordered two-row family, the Lagrange masks have the exact four endpoint values. -/
theorem exact_two_row_lagrange_values :
    (firstRowMask nodes01).eval (nodes01 0) = 1 ∧
      (firstRowMask nodes01).eval (nodes01 1) = 0 ∧
      (lastRowMask (by decide) nodes01).eval (nodes01 0) = 0 ∧
      (lastRowMask (by decide) nodes01).eval (nodes01 1) = 1 := by
  constructor
  · exact firstRowMask_first (by decide) nodes01 nodes01_injective
  constructor
  · simpa [nodes01] using firstRowMask_eval nodes01 nodes01_injective (1 : Fin 2)
  constructor
  · simpa [nodes01] using
      lastRowMask_eval (by decide) nodes01 nodes01_injective (0 : Fin 2)
  · exact lastRowMask_last (by decide) nodes01 nodes01_injective

/-- Singleton preprocessing is not forced into the multirow-disjoint convention. -/
theorem singleton_has_both_endpoint_masks
    (nodes : Fin 1 → F73) :
    (firstRowMask nodes).eval (nodes 0) = 1 ∧
      (lastRowMask (by decide) nodes).eval (nodes 0) = 1 :=
  singleton_endpoint_masks nodes

/-- Neither fixed endpoint mask can be replaced by the zero polynomial on a nonempty injective
row family. -/
theorem endpoint_masks_cannot_be_zero
    {F : Type*} [Field F] {n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (hinj : Function.Injective nodes) :
    firstRowMask nodes ≠ 0 ∧ lastRowMask hn nodes ≠ 0 := by
  constructor
  · intro hz
    have h := firstRowMask_first hn nodes hinj
    rw [hz] at h
    simpa using h
  · intro hz
    have h := lastRowMask_last hn nodes hinj
    rw [hz] at h
    simpa using h

/-- The row-node `Finset` forgets order, but preprocessing does not: swapping the ordered family
keeps the same domain and changes the first-row polynomial. -/
theorem reordered_nodes_change_the_fixed_mask :
    rowNodeSet nodes01 = rowNodeSet nodes10 ∧
      firstRowMask nodes01 ≠ firstRowMask nodes10 := by
  constructor
  · ext x
    simp [rowNodeSet, nodes01, nodes10]
    tauto
  · intro heq
    have hleft : (firstRowMask nodes01).eval 0 = 1 := by
      simpa [nodes01] using firstRowMask_first (by decide) nodes01 nodes01_injective
    have hright : (firstRowMask nodes10).eval 0 = 0 := by
      simpa [nodes10] using firstRowMask_eval nodes10 nodes10_injective (1 : Fin 2)
    rw [heq] at hleft
    exact zero_ne_one (hright.symm.trans hleft)

/-- Duplicate row points cannot realize contradictory first-row values.  This is why exact
endpoint semantics is scoped to injective node families rather than inferred from `rowNodeSet`. -/
theorem duplicate_nodes_reject_endpoint_semantics
    (dup : Fin 2 → F73) (hdup : dup 0 = dup 1) :
    ¬ ∃ p : F73[X], p.eval (dup 0) = 1 ∧ p.eval (dup 1) = 0 := by
  rintro ⟨p, h0, h1⟩
  rw [hdup] at h0
  exact one_ne_zero (h0.symm.trans h1)

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

def finalLastFixedId {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) :
    Fin (NamedComputeRAP hn nodes b chalVal pubVal orbit).fixedCount :=
  ⟨1, by simp [NamedComputeRAP, finalFixedPreprocessingRAP]⟩

/-- The fixed columns are exactly Base13 slots 11 and 12, both in the 196-column round-zero
prefix; the interaction round remains a separate three-column block. -/
theorem final_preprocessing_round_binding_exact
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) :
    let R := NamedComputeRAP hn nodes b chalVal pubVal orbit
    R.rap.k = 2 ∧ R.rap.wRAP = ![296, 6] ∧
      R.fixedCount = 2 ∧
      (R.preprocessingColumn (finalFirstFixedId hn nodes b chalVal pubVal orbit) : ℕ) = 11 ∧
      (R.preprocessingColumn (finalLastFixedId hn nodes b chalVal pubVal orbit) : ℕ) = 12 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Binding has no hidden rows or columns: it is exactly the two claimed polynomial equalities. -/
theorem final_binds_preprocessing_iff
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin 302 → F[X]) :
    (NamedComputeRAP hn nodes b chalVal pubVal orbit).BindsPreprocessing P ↔
      P 11 = firstRowMask nodes ∧ P 12 = lastRowMask hn nodes := by
  constructor
  · intro hbind
    exact ⟨hbind (finalFirstFixedId hn nodes b chalVal pubVal orbit),
      hbind (finalLastFixedId hn nodes b chalVal pubVal orbit)⟩
  · rintro ⟨hfirst, hlast⟩ j
    fin_cases j
    · exact hfirst
    · exact hlast

theorem wrong_last_mask_rejected
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (P : Fin 302 → F[X])
    (hwrong : P 12 ≠ lastRowMask hn nodes) :
    ¬ RAP.SatisfiesWithPreprocessing
      (NamedComputeRAP hn nodes b chalVal pubVal orbit) P := by
  intro hsat
  exact hwrong ((final_binds_preprocessing_iff hn nodes b chalVal pubVal orbit P).1 hsat.2).2

theorem wrong_first_mask_rejected
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (P : Fin 302 → F[X])
    (hwrong : P 11 ≠ firstRowMask nodes) :
    ¬ RAP.SatisfiesWithPreprocessing
      (NamedComputeRAP hn nodes b chalVal pubVal orbit) P := by
  intro hsat
  exact hwrong ((final_binds_preprocessing_iff hn nodes b chalVal pubVal orbit P).1 hsat.2).1

/-! ## 2. Exact auxiliary semantics and the repaired degree-five originals -/

/-- Independent source-level recreation of the three literal degree-five masks. -/
def originalDegreeFiveResiduals : List Expr :=
  [lastMaskedTransition (Trans.walkCountStep.subst walkSubst),
    lastMaskedTransition (Trans.walkAccStep.subst walkSubst),
    lastMaskedTransition optimizedFoldedProgStep3]

theorem original_degree_five_residuals_exact :
    originalDegreeFiveResiduals.map Expr.degree = [5, 5, 5] := by
  decide

/-- The three new typed residuals are exactly the old extension gates at positions 10, 11, 20,
and remain genuine degree-four expressions before the last-row mask. -/
theorem final_residual_sources_are_exact_old_gates :
    residualSource 0 = oldExtGate 10 ∧
      residualSource 1 = oldExtGate 11 ∧
      residualSource 2 = oldExtGate 20 ∧
      (∀ j : ResidualWitnessId, (residualSource j).degree = 4) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro j
  fin_cases j <;> decide

/-- At every row and coordinate, a residual auxiliary pin turns the new quadratic mask check into
the original masked degree-four residual, in both directions. -/
theorem residual_block_iff_original
    (b : Basis (Fin 3) F K) (env : Env F) (j : ResidualWitnessId)
    (haux : ∀ k : Fin 3, (residualAuxGateCoord b j k).eval env = 0) :
    (∀ k : Fin 3,
        (CoeffExpr.mul notLastCoeff (residualWitnessCoord j k)).eval env = 0) ↔
      ∀ k : Fin 3,
        (CoeffExpr.mul notLastCoeff
          (finalTypedCompile b (finalResidualSource j) k)).eval env = 0 := by
  constructor
  · intro h k
    exact (residual_aux_masked_iff_original b env j haux).1 h k
  · intro h k
    exact (residual_aux_masked_iff_original b env j haux).2 h k

/-- No wrong auxiliary coordinate can satisfy its pin equation, independently of the mask value. -/
theorem wrong_auxiliary_cannot_bypass
    (b : Basis (Fin 3) F K) (env : Env F)
    (j : ResidualWitnessId) (k : Fin 3)
    (hwrong : (residualWitnessCoord j k).eval env ≠
      (finalTypedCompile b (finalResidualSource j) k).eval env) :
    (residualAuxGateCoord b j k).eval env ≠ 0 := by
  simpa [residualAuxGateCoord, CoeffExpr.eval, sub_eq_zero] using hwrong

/-- Final satisfaction pins every auxiliary coordinate on every active row to the exact coordinate
of its designated degree-four residual. -/
theorem final_satisfaction_pins_every_auxiliary
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (P : Fin 302 → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing
      (NamedComputeRAP hn nodes b chalVal pubVal orbit) P) :
    ∀ x ∈ rowNodeSet nodes, ∀ j : ResidualWitnessId, ∀ k : Fin 3,
      (residualWitnessCoord j k).eval
          (envOfTrace P orbit.ω x chalVal pubVal) =
        (finalTypedCompile b (finalResidualSource j) k).eval
          (envOfTrace P orbit.ω x chalVal pubVal) := by
  have hall := ((finalFixedPreprocessingRAP_satisfies_iff_allRows
    hn nodes b chalVal pubVal orbit P).1 hsat).2
  intro x hx j k
  have hpin := hall x hx (residualAuxGateCoord b j k)
    (residualAuxGateCoord_mem_final n b j k)
  change (residualWitnessCoord j k).eval
      (envOfTrace P orbit.ω x chalVal pubVal) -
        (finalTypedCompile b (finalResidualSource j) k).eval
          (envOfTrace P orbit.ω x chalVal pubVal) = 0 at hpin
  exact sub_eq_zero.mp hpin

/-- The local auxiliary equation is satisfiable for every source value and mask, and after the pin
the masked check is exactly the original check.  This is a concrete scalar non-vacuity principle,
not a claim of a canonical full polynomial witness. -/
theorem residual_auxiliary_local_nonvacuity
    (g mask : F) :
    ∃ y : F, y - g = 0 ∧ (mask * y = 0 ↔ mask * g = 0) := by
  exact ⟨g, sub_self g, Iff.rfl⟩

/-! ## 3. Exact final resources and support -/

theorem final_transition_taxonomy
    (n : ℕ) (b : Basis (Fin 3) F K) :
    (finalBaseTransitionGates (F := F) n).length = 15 ∧
      (compileFinalCoreExt b).length = 21 * 3 ∧
      (compileResidualAux b).length = 3 * 3 ∧
      15 + 21 * 3 + 3 * 3 = 15 + 24 * 3 ∧
      (compileTypedList b loweredMaskedEndpointDeg2).length = 2 * 3 ∧
      (compileTypedList b loweredMaskedEndpointDeg4).length = 1 * 3 ∧
      (maskedEndpointEqualityChecks (F := F)).length = 2 ∧
      (finalComputeAllGates n b).length = 118 := by
  norm_num [compileTypedList_length, loweredMaskedEndpoint_counts]

theorem final_column_taxonomy :
    13 + 58 * 3 = 187 ∧
      13 + 63 * 3 = 202 ∧
      62 = 58 + 3 + 1 ∧
      Fintype.card ResidualWitnessId = 3 ∧
      (walkLineRole : ℕ) = 61 := by
  norm_num [walkLineRole]

theorem historical_padding_fingerprint_only
    {h : ℕ} (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    (compOptimizedPaddedRAP b chalVal pubVal orbit H).w = 199 ∧
      (compOptimizedPaddedRAP b chalVal pubVal orbit H).s = 98 ∧
      (compileResidualAux b).length = 9 := by
  exact ⟨(compOptimizedPaddedRAP_fingerprint b chalVal pubVal orbit H).1,
    (compOptimizedPaddedRAP_fingerprint b chalVal pubVal orbit H).2,
    compileResidualAux_length b⟩

/-- Trace-variable support predicate for the actual final width. -/
def CoeffTraceFits199 : CoeffExpr F → Prop
  | .const _ => True
  | .var .traceCur i | .var .traceNext i => i < 202
  | .var .challenge _ | .var .publicVal _ => True
  | .add x y | .sub x y | .mul x y => CoeffTraceFits199 x ∧ CoeffTraceFits199 y
  | .neg x | .pow x _ => CoeffTraceFits199 x

theorem coeff_support_sumList {ι : Type*} (xs : List ι) (f : ι → CoeffExpr F)
    (h : ∀ i ∈ xs, CoeffTraceFits199 (f i)) :
    CoeffTraceFits199 (CoeffExpr.sumList xs f) := by
  induction xs with
  | nil => trivial
  | cons a xs ih =>
      exact ⟨h a (by simp), ih (fun i hi => h i (by simp [hi]))⟩

theorem fits187_implies_fits199 (g : CoeffExpr F)
    (h : Nock.RedTeam.Batch57.CoeffTraceFits187 g) :
    CoeffTraceFits199 g := by
  induction g with
  | const c => trivial
  | var kind i =>
      cases kind <;> simp only [Nock.RedTeam.Batch57.CoeffTraceFits187,
        CoeffTraceFits199] at h ⊢
      all_goals omega
  | add x y hx hy =>
      exact ⟨hx h.1, hy h.2⟩
  | sub x y hx hy =>
      exact ⟨hx h.1, hy h.2⟩
  | mul x y hx hy =>
      exact ⟨hx h.1, hy h.2⟩
  | neg x hx => exact hx h
  | pow x n hx => exact hx h

theorem mulVec_fits199
    (b : Basis (Fin 3) F K) (u v : Fin 3 → CoeffExpr F)
    (hu : ∀ i, CoeffTraceFits199 (u i))
    (hv : ∀ i, CoeffTraceFits199 (v i)) :
    ∀ k, CoeffTraceFits199 (mulVec b u v k) := by
  intro k
  apply coeff_support_sumList
  intro i hi
  apply coeff_support_sumList
  intro j hj
  exact ⟨⟨hu i, hv j⟩, trivial⟩

theorem powVec_fits199
    (b : Basis (Fin 3) F K) (u : Fin 3 → CoeffExpr F)
    (hu : ∀ i, CoeffTraceFits199 (u i)) :
    ∀ n k, CoeffTraceFits199 (powVec b u n k) := by
  intro n
  induction n with
  | zero =>
      intro k
      trivial
  | succ n ih =>
      exact mulVec_fits199 b (powVec b u n) u ih hu

theorem finalTypedCompile_fits199
    (b : Basis (Fin 3) F K) (t : FinalTypedExpr) (k : Fin 3) :
    CoeffTraceFits199 (finalTypedCompile b t k) := by
  induction t generalizing k with
  | baseCur i =>
      simp [finalTypedCompile, CoeffTraceFits199]
      omega
  | baseNext i =>
      simp [finalTypedCompile, CoeffTraceFits199]
      omega
  | extCur i =>
      simp [finalTypedCompile, OptimizedComputeFinalTypedLowering.finalExtCoordIndex,
        CoeffTraceFits199]
      omega
  | extNext i =>
      simp [finalTypedCompile, OptimizedComputeFinalTypedLowering.finalExtCoordIndex,
        CoeffTraceFits199]
      omega
  | challenge i => simp [finalTypedCompile, CoeffTraceFits199]
  | publicVal i => simp [finalTypedCompile, CoeffTraceFits199]
  | const c => simp [finalTypedCompile, CoeffTraceFits199]
  | add x y hx hy =>
      exact ⟨hx k, hy k⟩
  | sub x y hx hy =>
      exact ⟨hx k, hy k⟩
  | mul x y hx hy =>
      exact mulVec_fits199 b _ _ hx hy k
  | neg x hx => exact hx k
  | pow x n hx =>
      exact powVec_fits199 b _ hx n k

theorem residual_witness_coordinate_fits
    (j : ResidualWitnessId) (k : Fin 3) :
    CoeffTraceFits199 (residualWitnessCoord (F := F) j k) := by
  fin_cases j <;> fin_cases k <;>
    norm_num [residualWitnessCoord, OptimizedComputeFinal.finalExtCoordIndex,
      residualWitnessRole, CoeffTraceFits199]

theorem final_core_coordinate_fits
    (b : Basis (Fin 3) F K) (i : CoreExtGateId) (k : Fin 3) :
    CoeffTraceFits199 (finalCoreExtGateCoord b i k) := by
  unfold finalCoreExtGateCoord
  split
  · exact ⟨by simp [notLastCoeff, isLastVar, bv, CoeffTraceFits199],
      residual_witness_coordinate_fits 0 k⟩
  split
  · exact ⟨by simp [notLastCoeff, isLastVar, bv, CoeffTraceFits199],
      residual_witness_coordinate_fits 1 k⟩
  split
  · exact ⟨by simp [notLastCoeff, isLastVar, bv, CoeffTraceFits199],
      residual_witness_coordinate_fits 2 k⟩
  split
  · exact ⟨by simp [notLastCoeff, isLastVar, bv, CoeffTraceFits199],
      finalTypedCompile_fits199 b _ k⟩
  · exact finalTypedCompile_fits199 b _ k

theorem residual_aux_coordinate_fits
    (b : Basis (Fin 3) F K) (j : ResidualWitnessId) (k : Fin 3) :
    CoeffTraceFits199 (residualAuxGateCoord b j k) :=
  ⟨residual_witness_coordinate_fits j k,
    finalTypedCompile_fits199 b _ k⟩

theorem final_base_gate_fits
    (n : ℕ) (g : CoeffExpr F) (hg : g ∈ finalBaseTransitionGates n) :
    CoeffTraceFits199 g := by
  simp only [finalBaseTransitionGates, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ⟨i, hi, rfl⟩ | rfl | rfl | rfl | rfl
  · simp [selectorBool, bv, CoeffTraceFits199]
    omega
  · simp only [selectorOneHot, CoeffTraceFits199]
    exact ⟨coeff_support_sumList _ _ (fun i hi => by
      have hi' := List.mem_range.mp hi
      simpa [bv, CoeffTraceFits199] using hi'.trans (by decide : 11 < 202)), trivial⟩
  · simp [firstMaskBoolean, isFirstVar, bv, CoeffTraceFits199]
  · simp [lastMaskBoolean, isLastVar, bv, CoeffTraceFits199]
  · by_cases hn : n = 1 <;>
      simp [endpointOverlapConsistency, hn, isFirstVar, isLastVar, bv, CoeffTraceFits199]

theorem final_all_constraints_fit_width
    (n : ℕ) (b : Basis (Fin 3) F K) :
    ∀ g ∈ finalComputeAllGates n b, CoeffTraceFits199 g := by
  intro g hg
  simp only [finalComputeAllGates, List.mem_append] at hg
  rcases hg with ((((hb | hc) | ha) | h2) | h4) | heq
  · exact final_base_gate_fits n g hb
  · rw [compileFinalCoreExt] at hc
    obtain ⟨xs, hxs, hg⟩ := List.mem_flatten.mp hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    exact final_core_coordinate_fits b i k
  · rw [compileResidualAux] at ha
    obtain ⟨xs, hxs, hg⟩ := List.mem_flatten.mp ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    exact residual_aux_coordinate_fits b j k
  · rw [compileFinalTypedList] at h2
    obtain ⟨xs, hxs, hg⟩ := List.mem_flatten.mp h2
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hxs
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    exact finalTypedCompile_fits199 b t k
  · rw [compileFinalTypedList] at h4
    obtain ⟨xs, hxs, hg⟩ := List.mem_flatten.mp h4
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hxs
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    exact finalTypedCompile_fits199 b t k
  · simp only [finalEndpointEqualityChecks, List.mem_append, List.mem_map,
      List.mem_range] at heq
    have h199 : (11 : ℕ) < 202 := by decide
    rcases heq with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · refine ⟨by simp [isFirstVar, bv, CoeffTraceFits199], ?_⟩
      simpa [endpointEqualityCheck, CoeffTraceFits199] using hi.trans h199
    · refine ⟨by simp [isLastVar, bv, CoeffTraceFits199], ?_⟩
      simpa [endpointEqualityCheck, CoeffTraceFits199] using hi.trans h199

/-- Exact direct RAP metadata, including the full adjacent-row symbolic-variable domain. -/
theorem final_rap_metadata_exact
    {h n : ℕ} (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    let R := finalComputeRAP (n := n) b chalVal pubVal orbit H
    R.e = 3 ∧ R.k = 2 ∧ R.wRAP = ![296, 6] ∧
      R.w = 302 ∧ R.s = 118 ∧ R.d = 4 ∧ R.H = H ∧
      R.I = Finset.univ ×ˢ ({0, 1} : Finset ℕ) := by
  exact ⟨rfl, rfl, rfl, rfl, finalComputeAllGates_length n b, rfl, rfl, rfl⟩

/-- The actual reified `MvPolynomial` constraints, not merely their source expressions, all satisfy
the final degree-four cap. -/
theorem final_mvpolynomial_degree_le_four
    {h n : ℕ} (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) (H : Finset F)
    (i : Fin (finalComputeRAP (n := n) b chalVal pubVal orbit H).s) :
    ((finalComputeRAP (n := n) b chalVal pubVal orbit H).C i).totalDegree ≤ 4 :=
  (finalComputeRAP (n := n) b chalVal pubVal orbit H).C_deg i

/-! ## 4. Load-bearing residual resources and malformed controls -/

def lastBooleanAttackEnv : Env F73 where
  trace i := if i = 0 then 1 else if i = 12 then 2 else 0
  traceNext _ := 0
  chal _ := 0
  pub _ := 0

def overlapAttackEnv : Env F73 where
  trace i := if i = 0 ∨ i = 11 ∨ i = 12 then 1 else 0
  traceNext _ := 0
  chal _ := 0
  pub _ := 0

/-- The separately allocated last-mask boolean gate is load-bearing. -/
theorem last_mask_boolean_gate_load_bearing :
    firstMaskBoolean.eval lastBooleanAttackEnv = 0 ∧
      (endpointOverlapConsistency 2).eval lastBooleanAttackEnv = 0 ∧
      lastMaskBoolean.eval lastBooleanAttackEnv ≠ 0 := by
  norm_num [firstMaskBoolean, lastMaskBoolean, endpointOverlapConsistency,
    isFirstVar, isLastVar, bv, lastBooleanAttackEnv, CoeffExpr.eval] <;> decide

/-- The singleton/multirow overlap equation is independently load-bearing. -/
theorem overlap_gate_load_bearing :
    firstMaskBoolean.eval overlapAttackEnv = 0 ∧
      lastMaskBoolean.eval overlapAttackEnv = 0 ∧
      (endpointOverlapConsistency 2).eval overlapAttackEnv ≠ 0 := by
  norm_num [firstMaskBoolean, lastMaskBoolean, endpointOverlapConsistency,
    isFirstVar, isLastVar, bv, overlapAttackEnv, CoeffExpr.eval]

def singletonBaseEnv : Env F73 where
  trace i := if i = 0 ∨ i = 11 ∨ i = 12 then 1 else 0
  traceNext _ := 0
  chal _ := 0
  pub _ := 0

/-- The three endpoint-mask equations are jointly non-vacuous in the singleton convention. -/
theorem final_mask_row_nonvacuous :
    firstMaskBoolean.eval singletonBaseEnv = 0 ∧
      lastMaskBoolean.eval singletonBaseEnv = 0 ∧
      (endpointOverlapConsistency 1).eval singletonBaseEnv = 0 := by
  norm_num [firstMaskBoolean, lastMaskBoolean, endpointOverlapConsistency,
    isFirstVar, isLastVar, bv, singletonBaseEnv, CoeffExpr.eval]

theorem residual_roles_are_three_semantic_plus_walk :
    (∀ j : ResidualWitnessId, (residualWitnessRole j : ℕ) ∈ ({58, 59, 60} : Finset ℕ)) ∧
      (walkLineRole : ℕ) = 61 ∧
      (∀ j : ResidualWitnessId, residualWitnessRole j ≠ walkLineRole) := by
  constructor
  · intro j
    fin_cases j <;> simp [residualWitnessRole]
  constructor
  · rfl
  · intro j
    fin_cases j <;> decide

/-- Every auxiliary equation is actually present in the final list; no filler gate bucket is
appended. -/
theorem every_residual_aux_gate_is_load_bearing_member
    (n : ℕ) (b : Basis (Fin 3) F K) (j : ResidualWitnessId) (k : Fin 3) :
    residualAuxGateCoord b j k ∈ finalComputeAllGates n b ∧
      residualAuxGateCoord b j k =
        .sub (residualWitnessCoord j k)
          (finalTypedCompile b (finalResidualSource j) k) :=
  ⟨residualAuxGateCoord_mem_final n b j k, rfl⟩

theorem reject_loaded_gate
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (P : Fin 302 → F[X])
    (x : F) (hx : x ∈ rowNodeSet nodes)
    (g : CoeffExpr F) (hg : g ∈ finalComputeAllGates n b)
    (hbad : g.eval (envOfTrace P orbit.ω x chalVal pubVal) ≠ 0) :
    ¬ RAP.SatisfiesWithPreprocessing
      (NamedComputeRAP hn nodes b chalVal pubVal orbit) P := by
  intro hsat
  have hall := ((finalFixedPreprocessingRAP_satisfies_iff_allRows
    hn nodes b chalVal pubVal orbit P).1 hsat).2
  exact hbad (hall x hx g hg)

/-- Independently reconstructed malformed selector control. -/
theorem malformed_selector_control
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (P : Fin 302 → F[X])
    (x : F) (hx : x ∈ rowNodeSet nodes)
    (hbad : selectorOneHot.eval (envOfTrace P orbit.ω x chalVal pubVal) ≠ 0) :
    ¬ RAP.SatisfiesWithPreprocessing
      (NamedComputeRAP hn nodes b chalVal pubVal orbit) P := by
  apply reject_loaded_gate hn nodes b chalVal pubVal orbit P x hx selectorOneHot
  · simp [finalComputeAllGates, finalBaseTransitionGates]
  · exact hbad

theorem final_terminal_gate_mem
    (n : ℕ) (b : Basis (Fin 3) F K) (k : Fin 3) :
    finalTypedCompile b finalTerminalTyped k ∈ finalComputeAllGates n b := by
  have hterminal :
      finalTypedCompile b finalTerminalTyped k ∈
        compileFinalTypedList b finalLoweredMaskedEndpointDeg2 := by
    apply List.mem_flatten.mpr
    refine ⟨List.ofFn (fun q : Fin 3 => finalTypedCompile b finalTerminalTyped q), ?_, ?_⟩
    · apply List.mem_map.mpr
      exact ⟨finalTerminalTyped, List.get_mem _ _, rfl⟩
    · exact List.mem_ofFn.mpr ⟨k, rfl⟩
  simp only [finalComputeAllGates, List.mem_append]
  exact Or.inl (Or.inl (Or.inr hterminal))

/-- Independently reconstructed malformed terminal control. -/
theorem malformed_terminal_control
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (P : Fin 302 → F[X])
    (x : F) (hx : x ∈ rowNodeSet nodes) (k : Fin 3)
    (hbad : (finalTypedCompile b finalTerminalTyped k).eval
      (envOfTrace P orbit.ω x chalVal pubVal) ≠ 0) :
    ¬ RAP.SatisfiesWithPreprocessing
      (NamedComputeRAP hn nodes b chalVal pubVal orbit) P := by
  exact reject_loaded_gate hn nodes b chalVal pubVal orbit P x hx
    (finalTypedCompile b finalTerminalTyped k) (final_terminal_gate_mem n b k) hbad

/-- Independently reconstructed malformed sampled-coin/IO residual control. -/
theorem malformed_coin_control
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (P : Fin 302 → F[X])
    (x : F) (hx : x ∈ rowNodeSet nodes) (k : Fin 3)
    (hwrong : (residualWitnessCoord 2 k).eval
        (envOfTrace P orbit.ω x chalVal pubVal) ≠
      (finalTypedCompile b (finalResidualSource 2) k).eval
        (envOfTrace P orbit.ω x chalVal pubVal)) :
    ¬ RAP.SatisfiesWithPreprocessing
      (NamedComputeRAP hn nodes b chalVal pubVal orbit) P := by
  apply reject_loaded_gate hn nodes b chalVal pubVal orbit P x hx
    (residualAuxGateCoord b 2 k) (residualAuxGateCoord_mem_final n b 2 k)
  exact wrong_auxiliary_cannot_bypass b
    (envOfTrace P orbit.ω x chalVal pubVal) 2 k hwrong

/-! ## 5. -/

theorem final_same_object_all_row_boundary
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (NamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing
        (NamedComputeRAP hn nodes b chalVal pubVal orbit) P ↔
      FinalComputeCompiledLanguage hn nodes b chalVal pubVal orbit P :=
  namedComputeRAP_satisfies_iff_compiledLanguage hn nodes b chalVal pubVal orbit P

def strict_package_still_requires_B29
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ}
    (P : Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage F K hOrb q Λ) :=
  Nock.RedTeam.Batch57.strict_package_still_requires_B29 P

theorem paper_alias_remains_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch57.paper_alias_remains_forest

#print axioms exact_two_row_lagrange_values
#print axioms singleton_has_both_endpoint_masks
#print axioms endpoint_masks_cannot_be_zero
#print axioms reordered_nodes_change_the_fixed_mask
#print axioms duplicate_nodes_reject_endpoint_semantics
#print axioms final_preprocessing_round_binding_exact
#print axioms final_binds_preprocessing_iff
#print axioms wrong_last_mask_rejected
#print axioms wrong_first_mask_rejected
#print axioms original_degree_five_residuals_exact
#print axioms residual_block_iff_original
#print axioms wrong_auxiliary_cannot_bypass
#print axioms final_satisfaction_pins_every_auxiliary
#print axioms residual_auxiliary_local_nonvacuity
#print axioms final_transition_taxonomy
#print axioms final_column_taxonomy
#print axioms final_all_constraints_fit_width
#print axioms final_rap_metadata_exact
#print axioms final_mvpolynomial_degree_le_four
#print axioms last_mask_boolean_gate_load_bearing
#print axioms overlap_gate_load_bearing
#print axioms final_mask_row_nonvacuous
#print axioms every_residual_aux_gate_is_load_bearing_member
#print axioms malformed_selector_control
#print axioms malformed_terminal_control
#print axioms malformed_coin_control
#print axioms final_same_object_all_row_boundary
#print axioms strict_package_still_requires_B29
#print axioms paper_alias_remains_forest

end
end Nock.RedTeam.Batch58
