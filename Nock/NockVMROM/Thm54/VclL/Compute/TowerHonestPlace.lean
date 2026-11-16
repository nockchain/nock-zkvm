import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestFill
import Nock.NockVMROM.Thm54.VclL.Compute.TowerSummandsQ7

/-!
# Next-row, challenge and public placement of the honest tower fill

* Next-row placement (`pullNext_honestQT_trace`, `towerEnv309_extNext_of_src`, `_baseNext_of_src`,
  `_walk_of_src`, `_walkNext_of_src`): when the next point `ω·x` is the node of the next row, the
  pull-back's `traceNext` reads `srcColT` of that row and the tower environment reads back its values.
* Challenge / public placement: at `eF.chal = chalVQ7T`, `eF.pub = pubCFT`, the typed environment's
  challenge slots `1..6, 10` and extension publics `0, 1` are the DESIGN §(a) values.
* `Vcomp_abc_irrel`: `Vcomp` does not read `(a, b, c)`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.Framework Nock.NockVMROM.Thm54.SVFrame Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

/-! ## 1. Next-row placement -/

section Next
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

theorem envNext_honestQT_trace (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (hinj : Function.Injective nodes) (rows : Fin n → TowerRowVals (K := K) δ) {w : ℕ}
    (ω : F) (cv pv : ℕ → F) (i i' : Fin n) (hadj : ω * nodes i = nodes i') {j : ℕ} (hj : j < w) :
    (Reify.envOfTrace (honestQT b nodes rows w) ω (nodes i) cv pv).traceNext j = vclColT b rows j i' := by
  simp only [Reify.envOfTrace, hj, dif_pos]
  rw [hadj]
  exact honestQT_eval b nodes hinj rows ⟨j, hj⟩ i'

/-- **Next-row placement (pull-back)**: with `ω·x_i = x_{i'}` the pull-back's `traceNext` reads the
source fill of row `i'`. -/
theorem pullNext_honestQT_trace (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (hinj : Function.Injective nodes) (rows : Fin n → TowerRowVals (K := K) δ)
    (ω : F) (cv pv : ℕ → F) (i i' : Fin n) (hadj : ω * nodes i = nodes i') (c : ℕ) (hc : SrcRead c) :
    (pullEnv (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv)).traceNext c =
      srcColT b (rows i') c := by
  have hw : vclWidthT = 410 := rfl
  simp only [pullEnv]
  unfold SrcRead at hc
  rcases hc with h | h | h
  · have hv : vclCol c = c := by simp [vclCol, h]
    rw [hv, envNext_honestQT_trace b nodes hinj rows ω cv pv i i' hadj (by rw [hw]; omega)]
    simp [vclColT, h]
  all_goals
    have hv : vclCol c = c - 95 := by
      simp only [vclCol, serialCol]; split_ifs <;> omega
    rw [hv, envNext_honestQT_trace b nodes hinj rows ω cv pv i i' hadj (by rw [hw]; omega)]
    have h1 : ¬ (c - 95 < 202) := by omega
    have h2 : (208 ≤ c - 95 ∧ c - 95 < 214) ∨ (232 ≤ c - 95 ∧ c - 95 < 394) := by omega
    simp only [vclColT, h1, h2, if_false, if_true]
    congr 1; omega

variable [FiniteDimensional F K]

theorem towerEnv309_extNext_of_src (b : Basis (Fin 3) F K) (v : TowerRowVals (K := K) δ) (eF : Env F)
    (hF : ∀ c, SrcRead c → eF.traceNext c = srcColT b v c) (r : Fin 63)
    (hK : towerM.ext r = none → Quad.im _ (v.ext r) = 0) :
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.extTraceNext r = v.ext r := by
  have hre : (gatherEnv b eF).traceNext (13 + 3 * (r : ℕ)) = Quad.re _ (v.ext r) := by
    simp only [gatherEnv]
    apply LogUp.limbVal_eq_of_coords
    intro k
    rw [hF _ (Or.inl (by have := r.isLt; have := k.isLt; omega)), srcColT_role]
  have him : imVal (gatherEnv b eF).traceNext (towerM.ext r) = Quad.im _ (v.ext r) := by
    cases hc : towerM.ext r with
    | none => simp only [imVal]; exact (hK hc).symm
    | some c =>
      simp only [imVal, gatherEnv]
      apply LogUp.limbVal_eq_of_coords
      intro k
      obtain ⟨h327, hlt, -, -⟩ := towerM_ext_owner r c hc
      rw [hF _ (Or.inr (Or.inr (by have := k.isLt; omega))), srcColT_im b v r c hc k]
  show Quad.mk _ ((gatherEnv b eF).traceNext (13 + 3 * (r : ℕ))) (imVal (gatherEnv b eF).traceNext (towerM.ext r)) = _
  rw [hre, him, Quad.mk_re_im]

theorem towerEnv309_baseNext_of_src (b : Basis (Fin 3) F K) (v : TowerRowVals (K := K) δ) (eF : Env F)
    (hF : ∀ c, SrcRead c → eF.traceNext c = srcColT b v c) (j : Fin 13) :
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.baseTraceNext j = v.base j := by
  show eF.traceNext j = _
  rw [hF _ (Or.inl (by have := j.isLt; omega))]
  simp [srcColT, j.isLt]

/-- Walk columns: `W0` is `𝕂`-valued (no Im column), `W1` has its Im triple at `486`. -/
theorem towerEnv309_walk_of_src (b : Basis (Fin 3) F K) (v : TowerRowVals (K := K) δ) (eF : Env F)
    (hF : ∀ c, SrcRead c → eF.trace c = srcColT b v c) (hW0 : Quad.im _ (v.walk 0) = 0) (j : Fin 2) :
    (towerEnv309 δ towerM (gatherEnv b eF) eF).walk j = v.walk j := by
  have hre : (gatherEnv b eF).trace (303 + 3 * (j : ℕ)) = Quad.re _ (v.walk j) := by
    simp only [gatherEnv]
    apply LogUp.limbVal_eq_of_coords
    intro k
    rw [hF _ (Or.inr (Or.inl (by have := j.isLt; have := k.isLt; omega))), srcColT_walk]
  have him : imVal (gatherEnv b eF).trace (towerM.walk j) = Quad.im _ (v.walk j) := by
    fin_cases j
    · have h0 : towerM.walk 0 = none := towerM_walk_owner.2.1 ▸ rfl
      simp only [Fin.zero_eta, h0, imVal]; exact hW0.symm
    · have h1 : towerM.walk 1 = some 486 := towerM_walk_owner.1
      simp only [Fin.mk_one, h1, imVal, gatherEnv]
      apply LogUp.limbVal_eq_of_coords
      intro k
      rw [hF _ (Or.inr (Or.inr (by have := k.isLt; omega))), srcColT_walkIm]
  show Quad.mk _ ((gatherEnv b eF).trace (303 + 3 * (j : ℕ))) (imVal (gatherEnv b eF).trace (towerM.walk j)) = _
  rw [hre, him, Quad.mk_re_im]

theorem towerEnv309_walkNext_of_src (b : Basis (Fin 3) F K) (v : TowerRowVals (K := K) δ) (eF : Env F)
    (hF : ∀ c, SrcRead c → eF.traceNext c = srcColT b v c) (hW0 : Quad.im _ (v.walk 0) = 0) (j : Fin 2) :
    (towerEnv309 δ towerM (gatherEnv b eF) eF).walkNext j = v.walk j := by
  have hre : (gatherEnv b eF).traceNext (303 + 3 * (j : ℕ)) = Quad.re _ (v.walk j) := by
    simp only [gatherEnv]
    apply LogUp.limbVal_eq_of_coords
    intro k
    rw [hF _ (Or.inr (Or.inl (by have := j.isLt; have := k.isLt; omega))), srcColT_walk]
  have him : imVal (gatherEnv b eF).traceNext (towerM.walk j) = Quad.im _ (v.walk j) := by
    fin_cases j
    · have h0 : towerM.walk 0 = none := towerM_walk_owner.2.1
      simp only [Fin.zero_eta, h0, imVal]; exact hW0.symm
    · have h1 : towerM.walk 1 = some 486 := towerM_walk_owner.1
      simp only [Fin.mk_one, h1, imVal, gatherEnv]
      apply LogUp.limbVal_eq_of_coords
      intro k
      rw [hF _ (Or.inr (Or.inr (by have := k.isLt; omega))), srcColT_walkIm]
  show Quad.mk _ ((gatherEnv b eF).traceNext (303 + 3 * (j : ℕ))) (imVal (gatherEnv b eF).traceNext (towerM.walk j)) = _
  rw [hre, him, Quad.mk_re_im]

end Next

/-! ## 2. Challenge and public placement -/

section ChalPub
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K) (χ : Coins frameVCL K)

private theorem chalSlot_K (q : ℕ) (hq : q < 12) (hnone : towerM.chal ⟨q, hq⟩ = none) (k : K)
    (hk : chalKQ7T δ χ q = k) :
    (towerGather δ b).chalSlot (chalVQ7T δ b χ) q = algebraMap K (Quad (algebraMap F K δ)) k := by
  have h1 := limbVal_chalVQ7T δ b χ q (by omega)
  simp only [towerGather, hq, dite_true, hnone, imVal]
  rw [h1, hk]
  exact Quad.mk_base _ _

theorem chalSlot_two_T : (towerGather δ b).chalSlot (chalVQ7T δ b χ) 2 =
    algebraMap K (Quad (algebraMap F K δ)) (χ ⟨8, by decide⟩) :=
  chalSlot_K δ b χ 2 (by norm_num) (by decide) _ (by simp [chalKQ7T, chalKQ7])

theorem chalSlot_three_T : (towerGather δ b).chalSlot (chalVQ7T δ b χ) 3 =
    algebraMap K (Quad (algebraMap F K δ)) (χ ⟨9, by decide⟩) :=
  chalSlot_K δ b χ 3 (by norm_num) (by decide) _ (by simp [chalKQ7T, chalKQ7])

theorem chalSlot_four_T : (towerGather δ b).chalSlot (chalVQ7T δ b χ) 4 =
    algebraMap K (Quad (algebraMap F K δ)) (χ ⟨10, by decide⟩) :=
  chalSlot_K δ b χ 4 (by norm_num) (by decide) _ (by simp [chalKQ7T, chalKQ7])

/-- **Challenge placement.**  At `eF.chal = chalVQ7T`, the tower typed environment's challenge slots
are the DESIGN §(a) values: `z′ = (χ2, χ3)`, `a,b,c = χ8,χ9,χ10`, `z′⁻¹`, walk `α = χ0`, walk `γ = χ1`. -/
theorem towerEnv309_chal_placement (eF : Env F) (h : eF.chal = chalVQ7T δ b χ) :
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.chal 1 = zQuad δ χ ∧
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.chal 2 = algebraMap K _ (χ ⟨8, by decide⟩) ∧
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.chal 3 = algebraMap K _ (χ ⟨9, by decide⟩) ∧
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.chal 4 = algebraMap K _ (χ ⟨10, by decide⟩) ∧
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.chal 5 = (zQuad δ χ)⁻¹ ∧
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.chal 6 = algebraMap K _ (χ ⟨0, by decide⟩) ∧
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.chal 10 = algebraMap K _ (χ ⟨1, by decide⟩) := by
  have e : ∀ q : Fin 12, (towerEnv309 δ towerM (gatherEnv b eF) eF).base.chal q =
      (towerGather δ b).chalSlot eF.chal q := fun q => (towerGather δ b).chal_eq eF q
  rw [e, e, e, e, e, e, e, h]
  exact ⟨chalSlot_one_T δ b χ, chalSlot_two_T δ b χ, chalSlot_three_T δ b χ, chalSlot_four_T δ b χ,
    chalSlot_five_T δ b χ, chalSlot_six_T δ b χ, chalSlot_ten_T δ b χ⟩

/-- **Public placement.**  At `eF.pub = pubCFT`, the extension publics are `E0 = χ0` and
`E1 = seedVCLT`. -/
theorem towerEnv309_pub_placement {hC : ℕ} {S : MemShape} (V : VerifierData F K hC S) (x : ℕ → F)
    (ρ : Fin 3 → Quad (algebraMap F K δ)) (eF : Env F) (h : eF.pub = pubCFT δ V x ρ χ)
    (hb : V.basis = b) :
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.extensionPublic 0 =
        algebraMap K (Quad (algebraMap F K δ)) (χ ⟨0, by decide⟩) ∧
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.extensionPublic 1 = seedVCLT δ V.claim χ := by
  subst hb
  have e : ∀ q : Fin 3, (towerEnv309 δ towerM (gatherEnv V.basis eF) eF).base.extensionPublic q =
      (towerGather δ V.basis).pubSlot eF.pub q := fun q => (towerGather δ V.basis).pub_eq eF q
  rw [e, e, h]
  exact ⟨pubSlot_zero_T δ χ V x ρ, pubSlot_one_T δ χ V x ρ⟩

end ChalPub

/-! ## 3. `Vcomp` does not read `(a, b, c)` -/

section Abc
open Nock.ComputeTable
variable {K : Type} [Field K]

theorem Vcomp_abc_irrel (inp : Inputs K) (a b c : K) (pub : Pub K) (dec : Dec K) :
    Vcomp ⟨inp.α, inp.z, a, b, c⟩ pub dec ↔ Vcomp inp pub dec := by
  unfold Vcomp
  rfl

end Abc

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
