import Nock.NockVMROM.Thm54.VclL.Compute.TowerSat

/-!
# The honest fill of the tower compute chip — interface and placement

* `TowerRowVals`: one honest row as pure data (no proof fields): the 13 base columns over `𝔽`, the 63
  extension roles and the two walk columns as `𝕂′ = Quad δ` values, and the VCL-only columns over `𝔽`.
* `srcColT`: the 309 SOURCE-layout column function of a row: Re limbs at the existing role columns
  `13 + 3r + k`, walk Re at `303..308`, and Im limbs at the `towerM` Im triples (`327..`), located by
  the explicit inverse `imOwner`.
* `vclColT` / `honestQT`: the VCL-layout column function (`vclCol` preimages) and its interpolation
  over the row nodes.
* **Placement** (`pull_honestQT_trace`, `towerEnv309_ext_of_src`, …): at a row node, the pull-back of the
  honest trace reads `srcColT`, and the tower typed environment `towerEnv309` built from it reads back
  the row's `𝕂′` values, for every role whose `𝕂′` value has an Im column or a zero Im half.
* **First gate family (C2c, IO vestige)**: the kept accumulator gates of the retired sampled-IO block
  (core `81` = `accAfterChain`, aux `2` = `correctedAccAfterStep`) hold at the honest fill whose roles
  `32..35`, `60` are zero (`honest_vestige_chain`, `honest_vestige_aux2`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.Framework

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

/-! ## 1. The Im-column inverse of `towerM` -/

/-- Owner of the Im triple number `q` (source column `327 + 3q`): FP ranks `0..49` are roles
`0..31`, `36..53`; then roles `56`, `57`, `59`; `63` codes walk column `W1`. -/
def imOwner (q : ℕ) : Option ℕ :=
  if q < 32 then some q else if q < 50 then some (q + 4) else if q = 50 then some 56
  else if q = 51 then some 57 else if q = 52 then some 59 else if q = 53 then some 63 else none

/-- **Every `towerM` Im triple is owned by its role** (computed over the 63 roles). -/
theorem towerM_ext_owner_all : ∀ r : Fin 63, (towerM.ext r).all (fun c =>
    decide (327 ≤ c ∧ c + 3 ≤ 489 ∧ (c - 327) % 3 = 0 ∧ imOwner ((c - 327) / 3) = some r.val)) = true := by
  decide +kernel

theorem towerM_walk_owner : towerM.walk 1 = some 486 ∧ towerM.walk 0 = none ∧ imOwner 53 = some 63 := by
  decide +kernel

theorem towerM_ext_owner (r : Fin 63) (c : ℕ) (h : towerM.ext r = some c) :
    327 ≤ c ∧ c + 3 ≤ 489 ∧ (c - 327) % 3 = 0 ∧ imOwner ((c - 327) / 3) = some r.val := by
  have := towerM_ext_owner_all r
  rw [h] at this
  simpa using this

/-! ## 2. One honest row, and its source-layout column function -/

section Fill
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K]
variable (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **One honest tower row, as data.** -/
structure TowerRowVals where
  base : Fin 13 → F
  ext : Fin 63 → Quad (algebraMap F K δ)
  walk : Fin 2 → Quad (algebraMap F K δ)
  vcl : ℕ → F

variable {δ}

/-- **The source-layout column function of a row** (309 layout plus the Im triples at `327..`). -/
def srcColT (b : Basis (Fin 3) F K) (v : TowerRowVals (K := K) δ) (c : ℕ) : F :=
  if h : c < 13 then v.base ⟨c, h⟩
  else if h : c < 202 then
    coord b (Quad.re _ (v.ext ⟨(c - 13) / 3, by omega⟩)) ⟨(c - 13) % 3, Nat.mod_lt _ (by decide)⟩
  else if h : 303 ≤ c ∧ c < 309 then
    coord b (Quad.re _ (v.walk ⟨(c - 303) / 3, by omega⟩)) ⟨(c - 303) % 3, Nat.mod_lt _ (by decide)⟩
  else if 327 ≤ c then
    match imOwner ((c - 327) / 3) with
    | some r =>
        if hr : r < 63 then
          coord b (Quad.im _ (v.ext ⟨r, hr⟩)) ⟨(c - 327) % 3, Nat.mod_lt _ (by decide)⟩
        else coord b (Quad.im _ (v.walk 1)) ⟨(c - 327) % 3, Nat.mod_lt _ (by decide)⟩
    | none => 0
  else 0

theorem srcColT_role (b : Basis (Fin 3) F K) (v : TowerRowVals (K := K) δ) (r : Fin 63) (k : Fin 3) :
    srcColT b v (13 + 3 * (r : ℕ) + k) = coord b (Quad.re _ (v.ext r)) k := by
  have hr := r.isLt
  have hk := k.isLt
  have h1 : ¬ (13 + 3 * (r : ℕ) + k < 13) := by omega
  have h2 : 13 + 3 * (r : ℕ) + k < 202 := by omega
  simp only [srcColT, h1, h2, dif_neg, dif_pos, not_false_eq_true]
  have e1 : (13 + 3 * (r : ℕ) + k - 13) / 3 = r := by omega
  have e2 : (13 + 3 * (r : ℕ) + k - 13) % 3 = k := by omega
  all_goals (congr 2; exact congrArg _ (Fin.ext e1))

theorem srcColT_walk (b : Basis (Fin 3) F K) (v : TowerRowVals (K := K) δ) (j : Fin 2) (k : Fin 3) :
    srcColT b v (303 + 3 * (j : ℕ) + k) = coord b (Quad.re _ (v.walk j)) k := by
  have hj := j.isLt
  have hk := k.isLt
  have h1 : ¬ (303 + 3 * (j : ℕ) + k < 13) := by omega
  have h2 : ¬ (303 + 3 * (j : ℕ) + k < 202) := by omega
  have h3 : 303 ≤ 303 + 3 * (j : ℕ) + k ∧ 303 + 3 * (j : ℕ) + k < 309 := by omega
  simp only [srcColT, h1, h2, h3, dif_neg, dif_pos, not_false_eq_true, and_self]
  have e1 : (303 + 3 * (j : ℕ) + k - 303) / 3 = j := by omega
  have e2 : (303 + 3 * (j : ℕ) + k - 303) % 3 = k := by omega
  all_goals (congr 2; exact congrArg _ (Fin.ext e1))

theorem srcColT_im (b : Basis (Fin 3) F K) (v : TowerRowVals (K := K) δ) (r : Fin 63) (c : ℕ)
    (hc : towerM.ext r = some c) (k : Fin 3) :
    srcColT b v (c + k) = coord b (Quad.im _ (v.ext r)) k := by
  obtain ⟨h327, -, hmod, hown⟩ := towerM_ext_owner r c hc
  have hk := k.isLt
  have h1 : ¬ (c + k < 13) := by omega
  have h2 : ¬ (c + k < 202) := by omega
  have h3 : ¬ (303 ≤ c + k ∧ c + k < 309) := by omega
  have h4 : 327 ≤ c + k := by omega
  have eq : (c + k - 327) / 3 = (c - 327) / 3 := by omega
  have em : (c + k - 327) % 3 = k := by omega
  simp only [srcColT, h1, h2, h3, h4, dif_neg, not_false_eq_true, if_true, eq, hown, r.isLt, dif_pos]
  congr 1
  exact Fin.ext em

theorem srcColT_walkIm (b : Basis (Fin 3) F K) (v : TowerRowVals (K := K) δ) (k : Fin 3) :
    srcColT b v (486 + k) = coord b (Quad.im _ (v.walk 1)) k := by
  have hk := k.isLt
  have h1 : ¬ (486 + (k : ℕ) < 13) := by omega
  have h2 : ¬ (486 + (k : ℕ) < 202) := by omega
  have h3 : ¬ (303 ≤ 486 + (k : ℕ) ∧ 486 + (k : ℕ) < 309) := by omega
  have h4 : 327 ≤ 486 + (k : ℕ) := by omega
  have eq : (486 + (k : ℕ) - 327) / 3 = 53 := by omega
  have em : (486 + (k : ℕ) - 327) % 3 = k := by omega
  simp only [srcColT, h1, h2, h3, h4, dif_neg, not_false_eq_true, if_true, eq,
    towerM_walk_owner.2.2]
  simp only [show ¬ (63 < 63) from by omega, dif_neg, not_false_eq_true]
  congr 1
  exact Fin.ext em

/-! ## 3. The VCL-layout fill and the interpolated honest trace -/

/-- **The VCL-layout column function**: source columns by their `vclCol` preimage (`< 202` fixed;
walk `208..213` and Im `232..393` are source `+ 95`); the VCL-only columns from `vcl`, including the
appended Im inverse / accumulator columns `394..408`. -/
def vclColT (b : Basis (Fin 3) F K) {n : ℕ} (rows : Fin n → TowerRowVals (K := K) δ) (j : ℕ)
    (i : Fin n) : F :=
  if j < 202 then srcColT b (rows i) j
  else if (208 ≤ j ∧ j < 214) ∨ (232 ≤ j ∧ j < 394) then srcColT b (rows i) (j + 95)
  else (rows i).vcl j

/-- **`honestQT`**: column `j` interpolates `vclColT … j` at the row nodes. -/
def honestQT (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (rows : Fin n → TowerRowVals (K := K) δ) (w : ℕ) : Fin w → F[X] :=
  fun j => Lagrange.interpolate Finset.univ nodes (vclColT b rows j)

theorem honestQT_eval (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (hinj : Function.Injective nodes) (rows : Fin n → TowerRowVals (K := K) δ) {w : ℕ}
    (j : Fin w) (i : Fin n) :
    (honestQT b nodes rows w j).eval (nodes i) = vclColT b rows j i :=
  Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)

/-- **Stagedness**: a column's polynomial depends only on that column's values. -/
theorem honestQT_congr (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (rows rows' : Fin n → TowerRowVals (K := K) δ) (w : ℕ) (j : Fin w)
    (h : vclColT b rows j = vclColT b rows' j) :
    honestQT b nodes rows w j = honestQT b nodes rows' w j := by
  simp only [honestQT, h]

/-- The row environment of the honest trace reads `vclColT`. -/
theorem env_honestQT_trace (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (hinj : Function.Injective nodes) (rows : Fin n → TowerRowVals (K := K) δ) {w : ℕ}
    (ω : F) (cv pv : ℕ → F) (i : Fin n) {j : ℕ} (hj : j < w) :
    (Reify.envOfTrace (honestQT b nodes rows w) ω (nodes i) cv pv).trace j = vclColT b rows j i := by
  simp only [Reify.envOfTrace, hj, dif_pos]
  exact honestQT_eval b nodes hinj rows ⟨j, hj⟩ i

theorem env_honestQT_trace_zero (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (rows : Fin n → TowerRowVals (K := K) δ) {w : ℕ} (ω x : F) (cv pv : ℕ → F) {j : ℕ} (hj : j < w)
    (hv : ∀ i, vclColT b rows j i = 0) :
    (Reify.envOfTrace (honestQT b nodes rows w) ω x cv pv).trace j = 0 := by
  have h0 : vclColT b rows j = 0 := funext hv
  simp only [Reify.envOfTrace, hj, dif_pos, honestQT, h0, map_zero, Polynomial.eval_zero]

/-- The source columns the kept tower gates read (`NoFormR`, base / Re / walk and the `towerM` Im
triples `327..488`; the appended VCL-only Im columns `394..408` are read directly, not via a source
preimage). -/
def SrcRead (c : ℕ) : Prop := c < 202 ∨ (303 ≤ c ∧ c < 309) ∨ (327 ≤ c ∧ c < 489)

/-- **Placement 1 (pull-back)**: the pull-back of the honest row environment reads the source fill. -/
theorem pull_honestQT_trace (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (hinj : Function.Injective nodes) (rows : Fin n → TowerRowVals (K := K) δ)
    (ω : F) (cv pv : ℕ → F) (i : Fin n) (c : ℕ) (hc : SrcRead c) :
    (pullEnv (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv)).trace c =
      srcColT b (rows i) c := by
  have hw : vclWidthT = 410 := rfl
  simp only [pullEnv]
  unfold SrcRead at hc
  rcases hc with h | h | h
  · have hv : vclCol c = c := by simp [vclCol, h]
    rw [hv, env_honestQT_trace b nodes hinj rows ω cv pv i (by rw [hw]; omega)]
    simp [vclColT, h]
  · have hv : vclCol c = c - 95 := by
      simp only [vclCol, serialCol]; split_ifs <;> omega
    rw [hv, env_honestQT_trace b nodes hinj rows ω cv pv i (by rw [hw]; omega)]
    have h1 : ¬ (c - 95 < 202) := by omega
    have h2 : (208 ≤ c - 95 ∧ c - 95 < 214) ∨ (232 ≤ c - 95 ∧ c - 95 < 394) := by omega
    simp only [vclColT, h1, h2, if_false, if_true]
    congr 1; omega
  · have hv : vclCol c = c - 95 := by
      simp only [vclCol, serialCol]; split_ifs <;> omega
    rw [hv, env_honestQT_trace b nodes hinj rows ω cv pv i (by rw [hw]; omega)]
    have h1 : ¬ (c - 95 < 202) := by omega
    have h2 : (208 ≤ c - 95 ∧ c - 95 < 214) ∨ (232 ≤ c - 95 ∧ c - 95 < 394) := by omega
    simp only [vclColT, h1, h2, if_false, if_true]
    congr 1; omega

end Fill

/-! ## 4. Placement 2: the tower typed environment reads back the row's `𝕂′` values -/

section Back
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **Placement 2 (extension roles)**: if the source columns of `eF` carry the fill of `v`, then
`towerEnv309` reads role `r` as `v.ext r`, provided `r` has an Im column or `v.ext r` is `𝕂`-valued. -/
theorem towerEnv309_ext_of_src (b : Basis (Fin 3) F K) (v : TowerRowVals (K := K) δ) (eF : Env F)
    (hF : ∀ c, SrcRead c → eF.trace c = srcColT b v c) (r : Fin 63)
    (hK : towerM.ext r = none → Quad.im _ (v.ext r) = 0) :
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.extTrace r = v.ext r := by
  have hre : (gatherEnv b eF).trace (13 + 3 * (r : ℕ)) = Quad.re _ (v.ext r) := by
    simp only [gatherEnv]
    apply LogUp.limbVal_eq_of_coords
    intro k
    rw [hF _ (Or.inl (by have := r.isLt; have := k.isLt; omega)), srcColT_role]
  have him : imVal (gatherEnv b eF).trace (towerM.ext r) = Quad.im _ (v.ext r) := by
    cases hc : towerM.ext r with
    | none => simp only [imVal]; exact (hK hc).symm
    | some c =>
      simp only [imVal, gatherEnv]
      apply LogUp.limbVal_eq_of_coords
      intro k
      obtain ⟨h327, hlt, -, -⟩ := towerM_ext_owner r c hc
      rw [hF _ (Or.inr (Or.inr (by have := k.isLt; omega))), srcColT_im b v r c hc k]
  show Quad.mk _ ((gatherEnv b eF).trace (13 + 3 * (r : ℕ))) (imVal (gatherEnv b eF).trace (towerM.ext r)) = _
  rw [hre, him, Quad.mk_re_im]

/-- **Placement 2 (base columns)**. -/
theorem towerEnv309_base_of_src (b : Basis (Fin 3) F K) (v : TowerRowVals (K := K) δ) (eF : Env F)
    (hF : ∀ c, SrcRead c → eF.trace c = srcColT b v c) (j : Fin 13) :
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.baseTrace j = v.base j := by
  show eF.trace j = _
  rw [hF _ (Or.inl (by have := j.isLt; omega))]
  simp [srcColT, j.isLt]

end Back

/-! ## 5. The first C2 gate family: the IO vestige (core `81`, aux `2`) at zero roles -/

section Vestige
open CorrectedFinalTypedExpr

/-- The lowered accumulator step, written out (checked against the lowering by `decide`). -/
def accStepTerm : CorrectedFinalTypedExpr :=
  .sub (.mul (.mul (.mul (.sub (.extCur 60) (.extCur 32)) (.extCur 33)) (.extCur 34)) (.extCur 35))
    (.add (.add (.mul (.mul (.const 1) (.extCur 34)) (.extCur 35))
        (.mul (.mul (.add (.baseCur 0) (.add (.baseCur 2) (.add (.baseCur 5) (.add (.baseCur 6)
          (.add (.baseCur 7) (.add (.baseCur 8) (.baseCur 9))))))) (.extCur 33)) (.extCur 35)))
      (.mul (.mul (.add (.baseCur 6) (.baseCur 9)) (.extCur 33)) (.extCur 34)))

theorem correctedAccAfterStep_eq : correctedAccAfterStep = accStepTerm := by
  set_option maxRecDepth 300000 in decide +kernel

variable {F K' : Type} [Field F] [Field K'] [Algebra F K']

/-- **Aux `2` vanishes when the three sampled denominators (roles `33..35`) are zero.** -/
theorem accAfterStep_eval_zero (E : CorrectedFinalTypedEnv F K')
    (h33 : E.extTrace 33 = 0) (h34 : E.extTrace 34 = 0) (h35 : E.extTrace 35 = 0) :
    correctedAccAfterStep.eval E = 0 := by
  rw [correctedAccAfterStep_eq]
  simp [accStepTerm, CorrectedFinalTypedExpr.eval, h33, h34, h35]

/-- **Core `81` vanishes when `acc_after` (role `60`) and the next accumulator (role `32`) are zero.** -/
theorem accAfterChain_eval_zero (E : CorrectedFinalTypedEnv F K')
    (h60 : E.extTrace 60 = 0) (h32 : E.extTraceNext 32 = 0) :
    accAfterChain.eval E = 0 := by
  simp [accAfterChain, CorrectedFinalTypedExpr.eval, h60, h32]

end Vestige

section VestigeHonest
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

theorem quad_im_zero (d : K) [Fact (¬ IsSquare d)] : Quad.im d (0 : Quad d) = 0 := by
  have h := Quad.im_mk d (0 : K) 0
  rwa [show Quad.mk d (0 : K) 0 = 0 by simp [Quad.mk]] at h

theorem towerM_vestige_none : towerM.ext 32 = none ∧ towerM.ext 33 = none ∧ towerM.ext 34 = none ∧
    towerM.ext 35 = none ∧ towerM.ext 60 = none := by decide +kernel

/-- **The honest fill satisfies aux `2` in `𝕂′`** when its sampled-denominator roles are zero. -/
theorem honest_vestige_aux2 (b : Basis (Fin 3) F K) (v : TowerRowVals (K := K) δ) (eF : Env F)
    (hF : ∀ c, SrcRead c → eF.trace c = srcColT b v c)
    (h33 : v.ext 33 = 0) (h34 : v.ext 34 = 0) (h35 : v.ext 35 = 0) :
    towerHolds δ (gatherEnv b eF) eF (auxTarget 2) := by
  have z : ∀ r : Fin 63, v.ext r = 0 → towerM.ext r = none →
      (towerEnv309 δ towerM (gatherEnv b eF) eF).base.extTrace r = 0 := fun r hr hn => by
    rw [towerEnv309_ext_of_src b v eF hF r (fun _ => by rw [hr]; exact quad_im_zero _)]
    exact hr
  unfold towerHolds auxTarget
  simp only [dif_pos]
  exact accAfterStep_eval_zero _ (z 33 h33 towerM_vestige_none.2.1) (z 34 h34 towerM_vestige_none.2.2.1)
    (z 35 h35 towerM_vestige_none.2.2.2.1)

end VestigeHonest

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
