import Nock.NockVMROM.Thm54.VclL.Compute.TowerChip

/-!
# Route (d), phase 2 : the width-309 (walk) append-only theory and the special core gates

* `reEnv309`, `isCoordEnv309_reEnv`, `toQW_eval_of_noImW`, `toQW_fst_eval_of_qLinearW`,
  `appendOnlyW_iff`: the `WTyped` twin of `TowerD.appendOnly_iff` (queue / endpoint / aux gates);
* `imFree_iff` / `imFreeW_iff`: an Im-free gate holds in `𝕂′` iff its existing compiled body vanishes
  (no Im twin is needed);
* `maskedGate_iff`: the `notLast`-masked bodies (core 72/73/74/75) against the typed masked gate.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

section W
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The pre-tower reading of a width-309 environment (Re halves). -/
def reEnv309 (eK : Env K) (eF : Env F) : Env309 F K where
  base := reEnv eK eF
  walk j := eK.trace (303 + 3 * (j : ℕ))
  walkNext j := eK.traceNext (303 + 3 * (j : ℕ))

theorem isCoordEnv309_reEnv (b : Basis (Fin 3) F K) {eK : Env K} {eF : Env F}
    (h : IsCoordEnv b col0Id eK eF) : IsCoordEnv309 b (reEnv309 eK eF) eF where
  base := isCorrectedFinalCoordEnv_reEnv b h
  walk j k := h.trace (303 + 3 * (j : ℕ)) k
  walkNext j k := h.traceNext (303 + 3 * (j : ℕ)) k

theorem qLinear_of_noIm (M : ImMap) : ∀ g : CorrectedFinalTypedExpr, hasIm M g = false →
    qLinear M g = true
  | .baseCur _, _ | .baseNext _, _ | .extCur _, _ | .extNext _, _ | .challenge _, _
  | .extensionPublic _, _ | .scalarPublic _, _ | .const _, _ | .certBase _, _ | .certExt _, _
  | .expCur, _ => rfl
  | .add x y, h => by
      simp only [hasIm, Bool.or_eq_false_iff] at h
      simp [qLinear, qLinear_of_noIm M x h.1, qLinear_of_noIm M y h.2]
  | .sub x y, h => by
      simp only [hasIm, Bool.or_eq_false_iff] at h
      simp [qLinear, qLinear_of_noIm M x h.1, qLinear_of_noIm M y h.2]
  | .mul x y, h => by
      simp only [hasIm, Bool.or_eq_false_iff] at h
      simp [qLinear, h.1, qLinear_of_noIm M y h.2]
  | .neg x, h => by
      simp only [hasIm] at h
      simpa [qLinear] using qLinear_of_noIm M x h
  | .pow x m, h => by
      simp only [hasIm] at h
      simp [qLinear, h]
  | .lamPow d, h => by
      simpa [hasIm, qLinear] using h

theorem qLinearW_of_noImW (M : ImMap) : ∀ g : WTyped, hasImW M g = false → qLinearW M g = true
  | .leaf t, h => qLinear_of_noIm M t h
  | .wCur _, _ | .wNext _, _ => rfl
  | .add x y, h => by
      simp only [hasImW, Bool.or_eq_false_iff] at h
      simp [qLinearW, qLinearW_of_noImW M x h.1, qLinearW_of_noImW M y h.2]
  | .sub x y, h => by
      simp only [hasImW, Bool.or_eq_false_iff] at h
      simp [qLinearW, qLinearW_of_noImW M x h.1, qLinearW_of_noImW M y h.2]
  | .mul x y, h => by
      simp only [hasImW, Bool.or_eq_false_iff] at h
      simp [qLinearW, h.1, qLinearW_of_noImW M y h.2]
  | .neg x, h => by
      simp only [hasImW] at h
      simpa [qLinearW] using qLinearW_of_noImW M x h
  | .pow x m, h => by
      simp only [hasImW] at h
      simp [qLinearW, h]

variable (δ : F)

theorem toQW_eval_of_noImW (M : ImMap) (n : ℕ) (hn : n = MemoryTable.pwScaleExp K) (eK : Env K)
    (eF : Env F) : ∀ g : WTyped, hasImW M g = false →
      (toQW F M n δ g).2.eval eK eF = 0 ∧ (toQW F M n δ g).1.eval eK eF = g.eval (reEnv309 eK eF)
  | .leaf t, h => toQ_eval_of_noIm δ M n hn eK eF t h
  | .wCur j, h => by
      simp only [hasImW, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      simp only [toQW, h]; exact ⟨qvar_snd_eval_none .., qvar_fst_eval ..⟩
  | .wNext j, h => by
      simp only [hasImW, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      simp only [toQW, h]; exact ⟨qvar_snd_eval_none .., qvar_fst_eval ..⟩
  | .add x y, h => by
      simp only [hasImW, Bool.or_eq_false_iff] at h
      have hx := toQW_eval_of_noImW M n hn eK eF x h.1
      have hy := toQW_eval_of_noImW M n hn eK eF y h.2
      simp only [toQW, qadd, MixedExpr.eval, WTyped.eval, hx.1, hx.2, hy.1, hy.2]
      simp
  | .sub x y, h => by
      simp only [hasImW, Bool.or_eq_false_iff] at h
      have hx := toQW_eval_of_noImW M n hn eK eF x h.1
      have hy := toQW_eval_of_noImW M n hn eK eF y h.2
      simp only [toQW, qsub, MixedExpr.eval, WTyped.eval, hx.1, hx.2, hy.1, hy.2]
      simp
  | .mul x y, h => by
      simp only [hasImW, Bool.or_eq_false_iff] at h
      have hx := toQW_eval_of_noImW M n hn eK eF x h.1
      have hy := toQW_eval_of_noImW M n hn eK eF y h.2
      simp only [toQW, qmul, MixedExpr.eval, CoeffExpr.eval, WTyped.eval, hx.1, hx.2,
        hy.1, hy.2]
      simp
  | .neg x, h => by
      simp only [hasImW] at h
      have hx := toQW_eval_of_noImW M n hn eK eF x h
      simp only [toQW, qneg, MixedExpr.eval, WTyped.eval, hx.1, hx.2]
      simp
  | .pow x m, h => by
      simp only [hasImW] at h
      have hx := toQW_eval_of_noImW M n hn eK eF x h
      have hp := qpow_eval_of_im_zero δ eK eF _ hx.1 m
      simp only [toQW, WTyped.eval]
      exact ⟨hp.2, by rw [hp.1, hx.2]⟩

theorem toQW_fst_eval_of_qLinearW (M : ImMap) (n : ℕ) (hn : n = MemoryTable.pwScaleExp K)
    (eK : Env K) (eF : Env F) : ∀ g : WTyped, qLinearW M g = true →
      (toQW F M n δ g).1.eval eK eF = g.eval (reEnv309 eK eF)
  | .leaf t, h => toQ_fst_eval_of_qLinear δ M n hn eK eF t h
  | .wCur j, _ => by simp only [toQW]; exact qvar_fst_eval ..
  | .wNext j, _ => by simp only [toQW]; exact qvar_fst_eval ..
  | .add x y, h => by
      simp only [qLinearW, Bool.and_eq_true] at h
      simp only [toQW, qadd, MixedExpr.eval, WTyped.eval,
        toQW_fst_eval_of_qLinearW M n hn eK eF x h.1, toQW_fst_eval_of_qLinearW M n hn eK eF y h.2]
  | .sub x y, h => by
      simp only [qLinearW, Bool.and_eq_true] at h
      simp only [toQW, qsub, MixedExpr.eval, WTyped.eval,
        toQW_fst_eval_of_qLinearW M n hn eK eF x h.1, toQW_fst_eval_of_qLinearW M n hn eK eF y h.2]
  | .mul x y, h => by
      simp only [qLinearW, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
      rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · have hx' := toQW_eval_of_noImW δ M n hn eK eF x hx
        simp only [toQW, qmul, MixedExpr.eval, CoeffExpr.eval, WTyped.eval, hx'.1,
          hx'.2, toQW_fst_eval_of_qLinearW M n hn eK eF y hy]
        simp
      · have hy' := toQW_eval_of_noImW δ M n hn eK eF y hy
        simp only [toQW, qmul, MixedExpr.eval, CoeffExpr.eval, WTyped.eval, hy'.1,
          hy'.2, toQW_fst_eval_of_qLinearW M n hn eK eF x hx]
        simp
  | .neg x, h => by
      simp only [qLinearW] at h
      simp only [toQW, qneg, MixedExpr.eval, WTyped.eval,
        toQW_fst_eval_of_qLinearW M n hn eK eF x h]
  | .pow x m, h => by
      simp only [qLinearW, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_true_eq] at h
      rcases h with hx | ⟨hm, hx⟩
      · exact (toQW_eval_of_noImW δ M n hn eK eF (.pow x m) (by simp [hasImW, hx])).2
      · have ih := toQW_fst_eval_of_qLinearW M n hn eK eF x hx
        interval_cases m
        · simp [toQW, qpow, MixedExpr.eval, WTyped.eval]
        · simp [toQW, qpow, qmul, MixedExpr.eval, CoeffExpr.eval, WTyped.eval, ih]

variable [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **Append-only at width 309**: the chip's existing `compile309` body together with the appended
Im twin vanish iff the walk-language gate holds in `𝕂′` at `towerEnv309`. -/
theorem appendOnlyW_iff [FiniteDimensional F K] (b : Basis (Fin 3) F K) (M : ImMap) (n : ℕ)
    (hn : n = MemoryTable.pwScaleExp K) {eK : Env K} {eF : Env F} (h : IsCoordEnv b col0Id eK eF)
    (g : WTyped) (hlin : qLinearW M g = true) :
    ((∀ k, (compile309 b g k).eval eF = 0) ∧
        ∀ k, (mixedCompile b col0Id (toQW F M n δ g).2 k).eval eF = 0) ↔
      g.eval (towerEnv309 δ M eK eF) = 0 := by
  rw [← toQW_compiled_iff δ b M n hn h g]
  have hre : (∀ k, (compile309 b g k).eval eF = 0) ↔
      ∀ k, (mixedCompile b col0Id (toQW F M n δ g).1 k).eval eF = 0 := by
    rw [compile309_zero_iff b (reEnv309 eK eF) eF (isCoordEnv309_reEnv b h),
      ← mixedCompile_zero_iff b col0Id h, toQW_fst_eval_of_qLinearW δ M n hn eK eF g hlin]
  rw [hre]

/-- An Im-free walk-language gate: its existing body vanishes iff it holds in `𝕂′`. -/
theorem imFreeW_iff [FiniteDimensional F K] (b : Basis (Fin 3) F K) (M : ImMap) (n : ℕ)
    (hn : n = MemoryTable.pwScaleExp K) {eK : Env K} {eF : Env F} (h : IsCoordEnv b col0Id eK eF)
    (g : WTyped) (hi : hasImW M g = false) :
    (∀ k, (compile309 b g k).eval eF = 0) ↔ g.eval (towerEnv309 δ M eK eF) = 0 := by
  have hlin : qLinearW M g = true := qLinearW_of_noImW M g hi
  rw [← appendOnlyW_iff δ b M n hn h g hlin]
  constructor
  · intro h1
    refine ⟨h1, fun k => ?_⟩
    rw [← mixedCompile_eval b col0Id h, (toQW_eval_of_noImW δ M n hn eK eF g hi).1]
    exact coord_zero' b k
  · exact fun h1 => h1.1

/-- An Im-free typed gate: its existing compiled body vanishes iff it holds in `𝕂′`. -/
theorem imFree_iff [FiniteDimensional F K] (b : Basis (Fin 3) F K) (M : ImMap) (n : ℕ)
    (hn : n = MemoryTable.pwScaleExp K) {eK : Env K} {eF : Env F} (h : IsCoordEnv b col0Id eK eF)
    (g : CorrectedFinalTypedExpr) (hi : hasIm M g = false) :
    (∀ k, (correctedFinalTypedCompile b g k).eval eF = 0) ↔ g.eval (towerEnv δ M eK eF) = 0 := by
  rw [← appendOnly_iff δ b M n hn h g (qLinear_of_noIm M g hi)]
  constructor
  · intro h1
    refine ⟨h1, fun k => ?_⟩
    rw [← mixedCompile_eval b col0Id h, (toQ_eval_of_noIm δ M n hn eK eF g hi).1]
    exact coord_zero' b k
  · exact fun h1 => h1.1

end W

section Mask
variable {F K' : Type} [Field F] [Field K'] [Algebra F K']

/-- The `notLast`-masked typed gate (`(1 - last)·g`, `last` = base column 12). -/
def maskT (g : CorrectedFinalTypedExpr) : CorrectedFinalTypedExpr :=
  .mul (.sub (.const 1) (.baseCur 12)) g

/-- **Masking transport**: scaling a Re/Im coordinate pair by `a = 1 - last ∈ 𝔽` multiplies the
`𝕂′` value by `algebraMap a`; the pair vanishes iff `a = 0` or the pair did. -/
theorem mask_pair_iff (a : F) (x y : Fin 3 → F) (v : K')
    (hv : ((∀ k, x k = 0) ∧ ∀ k, y k = 0) ↔ v = 0) :
    ((∀ k, a * x k = 0) ∧ ∀ k, a * y k = 0) ↔ algebraMap F K' a * v = 0 := by
  rw [mul_eq_zero, map_eq_zero_iff _ (algebraMap F K').injective, ← hv]
  by_cases ha : a = 0
  · simp [ha]
  · simp [ha]

end Mask

/-! ## Special core ids (72..77, 81) -/

/-- Receipts: the Im-freeness of the special bodies' sources at the source-layout map. -/
theorem special_noIm :
    hasIm towerM (correctedFinalExtGate packedLnChainId) = false ∧
    hasIm towerM (correctedFinalExtGate packedWalkLnId) = false ∧
    hasIm towerM (.extCur 58) = false ∧ hasIm towerM accAfterChain = false ∧
    hasImW towerM queueNonEmpty309 = false ∧ hasImW towerM queueTiling309 = false ∧
    (towerM.ext 59).isSome = true := by
  decide +kernel

theorem towerM_ext59 : towerM.ext 59 = some walkAccImCol := by
  decide +kernel

theorem coeff_eval {F : Type} [Field F] (eF : Env F) (g : CoeffExpr F) :
    ((CoeffExpr.mul (OptimizedComputeFinal.notLastCoeff) g).eval eF) =
      (1 - eF.trace 12) * g.eval eF := by
  simp [OptimizedComputeFinal.notLastCoeff, CoeffExpr.eval, OptimizedComputeBaseGates.isLastVar,
    OptimizedComputeBaseGates.bv]

section Special
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable (b : Basis (Fin 3) F K) (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]
  (n : ℕ) (hn : n = MemoryTable.pwScaleExp K) {eK : Env K} {eF : Env F}
  (h : IsCoordEnv b col0Id eK eF)
include h hn

private theorem baseEval (g : CorrectedFinalTypedExpr) :
    (maskT g).eval (towerEnv δ towerM eK eF) =
      (1 - algebraMap F (Quad (algebraMap F K δ)) (eF.trace 12)) * g.eval (towerEnv δ towerM eK eF) := by
  simp [maskT, CorrectedFinalTypedExpr.eval, towerEnv]

/-- Masked, Im-free: core 72 / 73. -/
theorem masked_imFree_iff (g : CorrectedFinalTypedExpr) (hi : hasIm towerM g = false) :
    (∀ k, (CoeffExpr.mul (OptimizedComputeFinal.notLastCoeff)
        (correctedFinalTypedCompile b g k)).eval eF = 0) ↔
      (maskT g).eval (towerEnv δ towerM eK eF) = 0 := by
  rw [baseEval b δ n hn h]
  have := mask_pair_iff (K' := Quad (algebraMap F K δ)) (1 - eF.trace 12)
    (fun k => (correctedFinalTypedCompile b g k).eval eF) (fun _ => 0)
    (g.eval (towerEnv δ towerM eK eF))
    (by rw [← imFree_iff δ b towerM n hn h g hi]; simp)
  simp only [mul_zero, implies_true, and_true] at this
  simp only [coeff_eval]
  simpa using this

omit hn in
theorem coords_zero_iff (c : ℕ) (x : K) (hc : ∀ k : Fin 3, eF.trace (c + k) = coord b x k) :
    (∀ k : Fin 3, eF.trace (c + k) = 0) ↔ x = 0 := by
  rw [eq_iff_coords_eq b x 0]
  simp only [coord_zero, hc]

omit h hn in
theorem walkCount_body (k : Fin 3) :
    correctedCoreCoord309 b packedWalkCountId k =
      .mul OptimizedComputeFinal.notLastCoeff (correctedFinalTypedCompile b (.extCur 58) k) := by
  simp [correctedCoreCoord309, correctedCoreCoord, packedQueueNonEmptyId, packedQueueTilingId,
    packedWalkCountId, OptimizedComputeFinal.residualWitnessCoord, correctedFinalTypedCompile,
    OptimizedComputeFinal.finalExtCoordIndex, correctedFinalExtCoordIndex,
    OptimizedComputeFinal.residualWitnessRole]

omit h hn in
theorem walkAcc_body (k : Fin 3) :
    correctedCoreCoord309 b packedWalkAccId k =
      .mul OptimizedComputeFinal.notLastCoeff (correctedFinalTypedCompile b (.extCur 59) k) := by
  simp [correctedCoreCoord309, correctedCoreCoord, packedQueueNonEmptyId, packedQueueTilingId,
    packedWalkCountId, packedWalkAccId, OptimizedComputeFinal.residualWitnessCoord,
    correctedFinalTypedCompile, OptimizedComputeFinal.finalExtCoordIndex,
    correctedFinalExtCoordIndex, OptimizedComputeFinal.residualWitnessRole]

/-- **Core 74** (`notLast · w58`, no Im): holds iff the masked typed residual vanishes. -/
theorem gate74_iff :
    (∀ k, (correctedCoreCoord309 b packedWalkCountId k).eval eF = 0) ↔
      (maskT (.extCur 58)).eval (towerEnv δ towerM eK eF) = 0 := by
  simp only [walkCount_body]
  exact masked_imFree_iff b δ n hn h _ special_noIm.2.2.1

/-- **Core 75** (`notLast · w59`; `w59` carries an Im half): the Re body and the appended Im twin
vanish iff the masked typed residual vanishes in `𝕂′`. -/
theorem gate75_iff :
    ((∀ k, (correctedCoreCoord309 b packedWalkAccId k).eval eF = 0) ∧
      ∀ k, (coreIm b δ n towerM packedWalkAccId k).eval eF = 0) ↔
      (maskT (.extCur 59)).eval (towerEnv δ towerM eK eF) = 0 := by
  rw [baseEval b δ n hn h]
  have hIm : ∀ k, coreIm b δ n towerM packedWalkAccId k =
      .mul OptimizedComputeFinal.notLastCoeff (.var .traceCur (walkAccImCol + (k : ℕ))) := by
    intro k; simp [coreIm]
  have := mask_pair_iff (K' := Quad (algebraMap F K δ)) (1 - eF.trace 12)
    (fun k => (correctedFinalTypedCompile b (.extCur 59) k).eval eF)
    (fun k => eF.trace (walkAccImCol + (k : ℕ)))
    ((CorrectedFinalTypedExpr.extCur 59).eval (towerEnv δ towerM eK eF))
    (by
      have e : (CorrectedFinalTypedExpr.extCur 59).eval (towerEnv δ towerM eK eF) =
          Quad.mk _ (eK.trace (13 + 3 * 59)) (eK.trace walkAccImCol) := by
        simp [CorrectedFinalTypedExpr.eval, towerEnv, imVal, towerM_ext59]
      rw [e, Quad.mk_eq_zero_iff]
      refine and_congr ?_ ?_
      · rw [← coords_zero_iff b h (13 + 3 * 59) _ (fun k => h.trace _ k)]
        simp [correctedFinalTypedCompile, correctedFinalExtCoordIndex, CoeffExpr.eval]
      · exact coords_zero_iff b h walkAccImCol _ (fun k => h.trace _ k))
  simp only [walkAcc_body, hIm, coeff_eval]
  simp only [CoeffExpr.eval]
  simpa using this

omit h hn in
theorem lnMasked_body (i : CorrectedCoreExtGateId)
    (hi : i = packedLnChainId ∨ i = packedWalkLnId) (k : Fin 3) :
    correctedCoreCoord309 b i k =
      .mul OptimizedComputeFinal.notLastCoeff (correctedFinalTypedCompile b (correctedFinalExtGate i) k) := by
  rcases hi with rfl | rfl <;>
  simp [correctedCoreCoord309, correctedCoreCoord, packedQueueNonEmptyId, packedQueueTilingId,
    packedWalkCountId, packedWalkAccId, packedChainId, packedLnChainId, packedWalkLnId]

omit h hn in
theorem chain_body (k : Fin 3) :
    correctedCoreCoord309 b packedChainId k = correctedFinalTypedCompile b accAfterChain k := by
  simp [correctedCoreCoord309, correctedCoreCoord, packedQueueNonEmptyId, packedQueueTilingId,
    packedWalkCountId, packedWalkAccId, packedChainId]

/-- The typed / walk-language target of each special core id. -/
def specialTarget (i : CorrectedCoreExtGateId) : WTyped :=
  if i = packedWalkCountId then .leaf (maskT (.extCur 58))
  else if i = packedWalkAccId then .leaf (maskT (.extCur 59))
  else if i = packedQueueNonEmptyId then queueNonEmpty309
  else if i = packedQueueTilingId then queueTiling309
  else if i = packedChainId then .leaf accAfterChain
  else .leaf (maskT (correctedFinalExtGate i))

/-- **Special core ids (72..77, 81)**: the chip's Re bodies (and, at 75, the Im twin) vanish iff
the target gate holds in `𝕂′` at `towerEnv309`. -/
theorem specialGate_iff (i : CorrectedCoreExtGateId) (hs : specialCore i = true) :
    ((∀ k, (coreRe b δ n towerM i k).eval eF = 0) ∧
      (i = packedWalkAccId → ∀ k, (coreIm b δ n towerM i k).eval eF = 0)) ↔
      (specialTarget i).eval (towerEnv309 δ towerM eK eF) = 0 := by
  have hre : ∀ k, coreRe b δ n towerM i k = correctedCoreCoord309 b i k := by
    intro k; simp [coreRe, hs]
  simp only [hre]
  rcases i with ⟨v, hv⟩
  have hv' : v = 72 ∨ v = 73 ∨ v = 74 ∨ v = 75 ∨ v = 76 ∨ v = 77 ∨ v = 81 := by
    simp [specialCore] at hs; omega
  rcases hv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have := masked_imFree_iff b δ n hn h (correctedFinalExtGate packedLnChainId) special_noIm.1
    simp only [lnMasked_body b _ (Or.inl rfl)]
    simpa [specialTarget, WTyped.eval, towerEnv309, packedLnChainId, packedWalkCountId,
      packedWalkAccId, packedQueueNonEmptyId, packedQueueTilingId, packedChainId] using this
  · have := masked_imFree_iff b δ n hn h (correctedFinalExtGate packedWalkLnId) special_noIm.2.1
    simp only [lnMasked_body b _ (Or.inr rfl)]
    simpa [specialTarget, WTyped.eval, towerEnv309, packedLnChainId, packedWalkCountId,
      packedWalkAccId, packedQueueNonEmptyId, packedQueueTilingId, packedChainId, packedWalkLnId]
      using this
  · have := gate74_iff b δ n hn h
    simpa [specialTarget, WTyped.eval, towerEnv309, packedWalkCountId, packedWalkAccId] using this
  · have := gate75_iff b δ n hn h
    simpa [specialTarget, WTyped.eval, towerEnv309, packedWalkCountId, packedWalkAccId] using this
  · have := imFreeW_iff δ b towerM n hn h queueNonEmpty309 special_noIm.2.2.2.2.1
    simpa [specialTarget, correctedCoreCoord309, packedQueueNonEmptyId, packedWalkCountId,
      packedWalkAccId] using this
  · have := imFreeW_iff δ b towerM n hn h queueTiling309 special_noIm.2.2.2.2.2.1
    simpa [specialTarget, correctedCoreCoord309, packedQueueNonEmptyId, packedQueueTilingId,
      packedWalkCountId, packedWalkAccId] using this
  · have := imFree_iff δ b towerM n hn h accAfterChain special_noIm.2.2.2.1
    simp only [chain_body]
    simpa [specialTarget, WTyped.eval, towerEnv309, packedChainId, packedWalkCountId,
      packedWalkAccId, packedQueueNonEmptyId, packedQueueTilingId] using this

/-! ## Aux and endpoint twins (item 2) -/

/-- The Im twin (compiled) of a walk-language gate. -/
def wIm {F K : Type} [Field F] [Field K] [Algebra F K] (b : Basis (Fin 3) F K) (δ : F) (n : ℕ)
    (g : WTyped) (k : Fin 3) : CoeffExpr F :=
  mixedCompile b col0Id (toQW F towerM n δ g).2 k

/-- The typed target of residual-witness position `j` (`w_{58+j} - source_j`, or the accumulator
step at `j = 2`). -/
def auxTarget (j : CorrectedResidualWitnessId) : WTyped :=
  if h : j = 2 then .leaf correctedAccAfterStep
  else .sub (.leaf (.extCur (residualWitnessRole j))) (residualSource309 (aux309Idx j h))

/-- The 13 appended-Im-relevant walk-language gates of the tower chip: aux, ep2, ep4. -/
def towerWGates : List WTyped :=
  (List.finRange 3).map auxTarget ++ endpoint2_309 ++ endpoint4_309

omit h hn in
/-- Receipt: every aux / endpoint gate is `qLinearW` at the source-layout map (so the existing
body is its Re twin and only an Im twin is appended). -/
theorem towerWGates_qLinear : ∀ g ∈ towerWGates, qLinearW towerM g = true := by
  decide +kernel

omit h hn in
/-- Receipt: which of them carry an Im twin (aux1, ep2 `Out`, ep4). -/
theorem towerWGates_hasIm :
    towerWGates.map (hasImW towerM) =
      [false, true, false, false, false, true, false, false, false, true] := by
  decide +kernel

omit h hn in
theorem auxRe_eq (j : CorrectedResidualWitnessId) (k : Fin 3) :
    correctedAuxCoord309 b j k = compile309 b (auxTarget j) k := by
  fin_cases j
  · simp [correctedAuxCoord309, auxTarget, aux309Idx, compile309, correctedFinalTypedCompile,
      OptimizedComputeFinal.residualWitnessCoord, OptimizedComputeFinal.finalExtCoordIndex,
      correctedFinalExtCoordIndex, OptimizedComputeFinal.residualWitnessRole,
      residualWitnessRole]
  · simp [correctedAuxCoord309, auxTarget, aux309Idx, compile309, correctedFinalTypedCompile,
      OptimizedComputeFinal.residualWitnessCoord, OptimizedComputeFinal.finalExtCoordIndex,
      correctedFinalExtCoordIndex, OptimizedComputeFinal.residualWitnessRole,
      residualWitnessRole]
  · simp [correctedAuxCoord309, auxTarget, compile309, correctedAuxCoord]

/-- **Walk-language transport**: for a `qLinearW` gate the existing body and (when it carries an
Im half) the appended Im twin vanish iff the gate holds in `𝕂′`. -/
theorem gateW_iff (g : WTyped) (hl : qLinearW towerM g = true) :
    ((∀ k, (compile309 b g k).eval eF = 0) ∧
      (hasImW towerM g = true → ∀ k, (wIm b δ n g k).eval eF = 0)) ↔
      g.eval (towerEnv309 δ towerM eK eF) = 0 := by
  rw [← appendOnlyW_iff δ b towerM n hn h g hl]
  by_cases hi : hasImW towerM g = true
  · simp [hi, wIm]
  · have hi' : hasImW towerM g = false := by simpa using hi
    constructor
    · rintro ⟨h1, -⟩
      refine ⟨h1, fun k => ?_⟩
      rw [← mixedCompile_eval b col0Id h, (toQW_eval_of_noImW δ towerM n hn eK eF g hi').1]
      exact coord_zero' b k
    · rintro ⟨h1, -⟩
      exact ⟨h1, fun hh => absurd hh hi⟩

end Special

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
