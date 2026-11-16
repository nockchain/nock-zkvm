import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestPlace

/-!
# The base gates, the 22 endpoint equalities, the IO vestige joined to placement

* `base15_of_cells` / `eq22_of_cells`: `TowerKeptHolds.base` and `.eq` from the honest base cells of a
  row (one-hot state, `isFirst`/`isLast` masks) and the selector public banks `x 20..41` (one-hots of the
  first / last row states).
* `honest_core81`, `honest_accInit`, `honest_accTerminal`: core `81`, ep2 `accInit`, ep2 `accTerminal`
  at the honest fill whose IO-vestige roles `32..35`, `60` are zero and whose request publics
  `x 6..8` are zero.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinal Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 300000

noncomputable section

/-! ## 1. Base gates and endpoint equalities from the base cells -/

section Base
variable {F : Type} [Field F]

/-- The honest base cells of row `i` of `n`: one-hot state `s`, first / last masks. -/
structure HonestBaseCells (n i s : ℕ) (E : Env F) : Prop where
  sel : ∀ j, j < 11 → E.trace j = if j = s then 1 else 0
  first : E.trace 11 = if i = 0 then 1 else 0
  last : E.trace 12 = if i + 1 = n then 1 else 0

theorem selectorSum_eval (s : ℕ) (hs : s < 11) (E : Env F) (hsel : ∀ j, j < 11 → E.trace j = if j = s then 1 else 0) :
    (selectorSum : CoeffExpr F).eval E = 1 := by
  rw [selectorSum, CoeffExpr.eval_sumList]
  simp only [bv, CoeffExpr.eval]
  rw [List.map_congr_left (fun j hj => by rw [hsel j (List.mem_range.mp hj)])]
  have : ∀ l : List ℕ, s ∈ l → l.Nodup → (l.map (fun j => (if j = s then (1 : F) else 0))).sum = 1 := by
    intro l hl hnd
    induction l with
    | nil => simp at hl
    | cons a l ih =>
      rcases List.mem_cons.mp hl with hsa | hl'
      · subst hsa
        simp only [List.map_cons, List.sum_cons, if_true]
        have : ∀ j ∈ l, j ≠ s := fun j hj hja => (List.nodup_cons.mp hnd).1 (hja ▸ hj)
        rw [List.map_congr_left (fun j hj => by rw [if_neg (this j hj)])]
        simp
      · have hne : a ≠ s := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hl')
        simp only [List.map_cons, List.sum_cons, if_neg hne, zero_add]
        exact ih hl' (List.nodup_cons.mp hnd).2
  exact this _ (List.mem_range.mpr hs) (List.nodup_range)

/-- **`TowerKeptHolds.base`** from the honest base cells (`n` rows, row `i < n`). -/
theorem base15_of_cells (n i s : ℕ) (hi : i < n) (hs : s < 11) (E : Env F) (h : HonestBaseCells n i s E) :
    ∀ g ∈ finalBaseTransitionGates n, g.eval E = 0 := by
  intro g hg
  simp only [finalBaseTransitionGates, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ⟨j, hj, rfl⟩ | rfl | rfl | rfl | rfl
  · simp only [selectorBool, bv, CoeffExpr.eval]
    rw [h.sel j hj]
    by_cases hjs : j = s <;> simp [hjs]
  · simp only [selectorOneHot, CoeffExpr.eval, selectorSum_eval s hs E h.sel, sub_self]
  · simp only [firstMaskBoolean, isFirstVar, bv, CoeffExpr.eval, h.first]
    by_cases h0 : i = 0 <;> simp [h0]
  · simp only [lastMaskBoolean, isLastVar, bv, CoeffExpr.eval, h.last]
    by_cases h0 : i + 1 = n <;> simp [h0]
  · by_cases hn1 : n = 1
    · simp only [endpointOverlapConsistency, hn1, if_true, CoeffExpr.eval, isFirstVar, isLastVar, bv,
        h.first, h.last]
      have : i = 0 := by omega
      simp [this, hn1]
    · simp only [endpointOverlapConsistency, hn1, if_false, CoeffExpr.eval, isFirstVar, isLastVar, bv,
        h.first, h.last]
      by_cases h0 : i = 0
      · have : ¬ (i + 1 = n) := by omega
        simp [this]
      · simp [h0]

/-- **`TowerKeptHolds.eq`**: the 22 endpoint equalities against the selector banks `x 20..41`
(one-hots of the first / last row states `s0`, `sL`). -/
theorem eq22_of_cells (n i s s0 sL : ℕ) (E : Env F) (h : HonestBaseCells n i s E)
    (hp0 : ∀ j, j < 11 → E.pub (20 + j) = if j = s0 then 1 else 0)
    (hpL : ∀ j, j < 11 → E.pub (31 + j) = if j = sL then 1 else 0)
    (h0 : i = 0 → s = s0) (hL : i + 1 = n → s = sL) :
    ∀ g ∈ (finalEndpointEqualityChecks : List (CoeffExpr F)), g.eval E = 0 := by
  intro g hg
  simp only [finalEndpointEqualityChecks, List.mem_append, List.mem_map, List.mem_range] at hg
  rcases hg with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · simp only [endpointEqualityCheck, isFirstVar, bv, CoeffExpr.eval, h.first, h.sel j hj, hp0 j hj]
    by_cases hi : i = 0
    · simp [hi, h0 hi]
    · simp [hi]
  · simp only [endpointEqualityCheck, isLastVar, bv, CoeffExpr.eval, h.last, h.sel j hj, hpL j hj]
    by_cases hi : i + 1 = n
    · simp [hi, hL hi]
    · simp [hi]

end Base

/-! ## 2. The honest cells read off the placement -/

section Cells
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- The honest base cells of the pull-back follow from the row's `base` data. -/
theorem honestBaseCells_of_src (b : Basis (Fin 3) F K) (v : TowerRowVals (K := K) δ) (E : Env F)
    (hF : ∀ c, SrcRead c → E.trace c = srcColT b v c) (n i s : ℕ)
    (hsel : ∀ j (hj : j < 11), v.base ⟨j, by omega⟩ = if j = s then 1 else 0)
    (hfirst : v.base 11 = if i = 0 then 1 else 0) (hlast : v.base 12 = if i + 1 = n then 1 else 0) :
    HonestBaseCells n i s E := by
  have hb : ∀ j (hj : j < 13), E.trace j = v.base ⟨j, hj⟩ := fun j hj => by
    rw [hF _ (Or.inl (by omega))]; simp [srcColT, hj]
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · rw [hb j (by omega), hsel j hj]
  · rw [hb 11 (by omega)]; exact hfirst
  · rw [hb 12 (by omega)]; exact hlast

end Cells

/-! ## 3. Core `81`, ep2 `accInit` / `accTerminal` at the honest vestige -/

section Vestige2
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

theorem lowerLeaf_accInit : lowerLeaf finalAccInit = .leaf (.mul (.baseCur 11) (.extCur 32)) := by
  decide +kernel

theorem lowerLeaf_accTerminal :
    lowerLeaf finalAccTerminal = .leaf (.mul (.baseCur 12) (.sub (.extCur 60) (.extensionPublic 2))) := by
  decide +kernel

theorem coreTarget_81 : coreTarget 81 = .leaf accAfterChain := by decide +kernel

theorem towerM_vestige_none' : towerM.ext 60 = none ∧ towerM.ext 32 = none ∧ towerM.extPub 2 = none := by
  decide +kernel

/-- A `𝕂′` role whose fill is `0` and which has no Im column reads `0` in the tower env (current row). -/
theorem tower_ext_zero (b : Basis (Fin 3) F K) (v : TowerRowVals (K := K) δ) (eF : Env F)
    (hF : ∀ c, SrcRead c → eF.trace c = srcColT b v c) (r : Fin 63) (hn : towerM.ext r = none)
    (h0 : v.ext r = 0) :
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.extTrace r = 0 := by
  rw [towerEnv309_ext_of_src b v eF hF r (fun _ => by rw [h0]; exact quad_im_zero _)]
  exact h0

theorem tower_extNext_zero (b : Basis (Fin 3) F K) (v : TowerRowVals (K := K) δ) (eF : Env F)
    (hF : ∀ c, SrcRead c → eF.traceNext c = srcColT b v c) (r : Fin 63) (hn : towerM.ext r = none)
    (h0 : v.ext r = 0) :
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.extTraceNext r = 0 := by
  rw [towerEnv309_extNext_of_src b v eF hF r (fun _ => by rw [h0]; exact quad_im_zero _)]
  exact h0

/-- **Core `81`** (`accAfterChain`) at the honest fill: row `v` has `acc_after = 0`, the next row `v'`
has `acc = 0`. -/
theorem honest_core81 (b : Basis (Fin 3) F K) (v v' : TowerRowVals (K := K) δ) (eF : Env F)
    (hF : ∀ c, SrcRead c → eF.trace c = srcColT b v c)
    (hFn : ∀ c, SrcRead c → eF.traceNext c = srcColT b v' c)
    (h60 : v.ext 60 = 0) (h32 : v'.ext 32 = 0) :
    towerHolds δ (gatherEnv b eF) eF (coreTarget 81) := by
  rw [coreTarget_81]
  unfold towerHolds
  exact accAfterChain_eval_zero _ (tower_ext_zero b v eF hF 60 towerM_vestige_none'.1 h60)
    (tower_extNext_zero b v' eF hFn 32 towerM_vestige_none'.2.1 h32)

/-- **ep2 `accInit`** at the honest fill with `acc = 0` (role `32`). -/
theorem honest_accInit (b : Basis (Fin 3) F K) (v : TowerRowVals (K := K) δ) (eF : Env F)
    (hF : ∀ c, SrcRead c → eF.trace c = srcColT b v c) (h32 : v.ext 32 = 0) :
    towerHolds δ (gatherEnv b eF) eF (lowerLeaf finalAccInit) := by
  rw [lowerLeaf_accInit]
  unfold towerHolds
  simp [WTyped.eval, CorrectedFinalTypedExpr.eval, tower_ext_zero b v eF hF 32 towerM_vestige_none'.2.1 h32]

/-- The extension public `E2` reads `0` when the request publics `x 6..8` are zero. -/
theorem tower_pub2_zero (b : Basis (Fin 3) F K) (eF : Env F) (hp : ∀ k, k < 3 → eF.pub (6 + k) = 0) :
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.extensionPublic 2 = 0 := by
  have e : (towerEnv309 δ towerM (gatherEnv b eF) eF).base.extensionPublic 2 =
      (towerGather δ b).pubSlot eF.pub 2 := (towerGather δ b).pub_eq eF 2
  rw [e]
  have h2 : towerM.extPub ⟨2, by norm_num⟩ = none := by decide +kernel
  simp only [towerGather, show (2 : ℕ) < 3 by norm_num, dite_true, h2, imVal]
  have : LogUp.limbVal b eF.pub (3 * 2) = 0 := by
    unfold LogUp.limbVal
    apply Finset.sum_eq_zero
    intro k _
    rw [show 3 * 2 + (k : ℕ) = 6 + k from rfl, hp k k.isLt, zero_smul]
  rw [this]
  simp [Quad.mk]

/-- **ep2 `accTerminal`** at the honest fill with `acc_after = 0` (role `60`) and `x 6..8 = 0`. -/
theorem honest_accTerminal (b : Basis (Fin 3) F K) (v : TowerRowVals (K := K) δ) (eF : Env F)
    (hF : ∀ c, SrcRead c → eF.trace c = srcColT b v c) (h60 : v.ext 60 = 0)
    (hp : ∀ k, k < 3 → eF.pub (6 + k) = 0) :
    towerHolds δ (gatherEnv b eF) eF (lowerLeaf finalAccTerminal) := by
  rw [lowerLeaf_accTerminal]
  unfold towerHolds
  simp [WTyped.eval, CorrectedFinalTypedExpr.eval, tower_ext_zero b v eF hF 60 towerM_vestige_none'.1 h60,
    tower_pub2_zero b eF hp]

end Vestige2

/-! ## 4. The scalar public banks are the package's -/

section Banks
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (χ : Coins frameVCL K)

/-- **Public placement (scalar banks)**: `pubCFT` reads the package publics `x` on `6..8` (the request
publics, `:= 0` at VCL) and on `20..41` (the selector banks: one-hots of the first / last row states). -/
theorem pubCFT_bank {hC : ℕ} {S : MemShape} (V : VerifierData F K hC S) (x : ℕ → F)
    (ρ : Fin 3 → Quad (algebraMap F K δ)) (j : ℕ) (hj : (6 ≤ j ∧ j < 9) ∨ (20 ≤ j ∧ j < 42)) :
    pubCFT δ V x ρ χ j = x j := by
  rw [pubCFT_lt δ χ V x ρ j (Or.inl (by omega))]
  unfold pubVQ7T
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]

end Banks

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
