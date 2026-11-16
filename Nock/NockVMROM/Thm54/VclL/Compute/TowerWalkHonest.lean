import Nock.NockVMROM.Thm54.VclL.Compute.TowerLookupHonest
import Nock.NockVMROM.Thm54.VclL.Compute.TowerGenMap
import Nock.NockVMROM.Thm54.VclL.Compute.WalkGatesT
import Nock.NockVMROM.Thm54.Unhosted309Insensitive

/-!
# 1914): the walk side of the honest tower compute env

* **Residual roles `58/59` (item 5).**  The residual sources `residualSource309 0/1` (`walkCountStep309`,
  `walkAccStep309`) read NO column of roles `58/59` (`residual_reads_class`, by `decide`): they read
  `W0/W1` (cur and next), the next row's selectors `0..10`, the next row's roles `0..31`, `39..43`, `61`
  and challenges `6/10`.  So the fill defines them NON-circularly as `residualVal j v v' ch`, the source
  evaluated on `rowSrcEnv v v' ch` (the current row's walk columns and the next row's data with roles
  `58/59` zeroed), and `residual_eq_of_fill` proves the `WalkRowEnv.r58/r59` equations at the tower env.
  `rowSrcEnv_ext5859_irrel`: the value does not depend on either row's roles `58/59`.
* **`𝕂`-valuedness (item 4).**  `HonestWalk.cnt_isK` / `ln_isK` / `inv_isK`: at a `𝕂`-valued walk coin the
  walk count, line and queue inverse are `𝕂`-valued on `1..h` (closed forms `α·α^{S_f}` / `α^k`);
  `residualVal_zero_isK`: the residual-`58` value is `𝕂`-valued when `W0` (both rows) and challenge `6` are.
* **Per-row placement (item 6).**  `honestQT_hF` / `honestQT_hFn`: the `hF` / `hFn` hypotheses of every
  C1/C2 placement lemma at the interpolated honest trace (one line each from `pull(Next)_honestQT_trace`).
* **Lookup inverses (item 1 consumer).**  `vclFill_invQ`: at a row whose VCL-only columns are `vclFill`,
  the three slot-inverse `Q`-values (Re AND Im) of `lookupGatesT_honest`'s `hinv0/1/2` are the filled
  `𝕂′` values.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.Framework Nock.Framework.Reify

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

/-! ## 1. `𝕂`-valued elements of `𝕂′` -/

section IsK
variable {K : Type} [Field K] [Fintype K] (d : K) [Fact (¬ IsSquare d)]

theorem quad_im_eq_zero_iff (x : Quad d) : Quad.im d x = 0 ↔ x ∈ (algebraMap K (Quad d)).range := by
  constructor
  · intro h
    refine ⟨Quad.re d x, ?_⟩
    rw [← Quad.mk_base, ← h, Quad.mk_re_im]
  · rintro ⟨a, rfl⟩
    rw [← Quad.mk_base, Quad.im_mk]

/-- `Expr.eval` stays in a subring when every read does. -/
theorem eval_mem_subring {L : Type} [Field L] (S : Subring L) (E : Env L) :
    ∀ e : Expr, (∀ p ∈ readsE e, varVal E p.1 p.2 ∈ S) → e.eval E ∈ S
  | .Var k j, h => by have := h (k, j) (by simp [readsE]); cases k <;> exact this
  | .Const c, _ => by simp only [Expr.eval]; exact intCast_mem S c
  | .Add a b, h => by
      simp only [readsE, List.mem_append] at h
      exact S.add_mem (eval_mem_subring S E a fun p hp => h p (Or.inl hp))
        (eval_mem_subring S E b fun p hp => h p (Or.inr hp))
  | .Sub a b, h => by
      simp only [readsE, List.mem_append] at h
      exact S.sub_mem (eval_mem_subring S E a fun p hp => h p (Or.inl hp))
        (eval_mem_subring S E b fun p hp => h p (Or.inr hp))
  | .Mul a b, h => by
      simp only [readsE, List.mem_append] at h
      exact S.mul_mem (eval_mem_subring S E a fun p hp => h p (Or.inl hp))
        (eval_mem_subring S E b fun p hp => h p (Or.inr hp))
  | .Neg a, h => S.neg_mem (eval_mem_subring S E a h)
  | .Pow a n, h => S.pow_mem (eval_mem_subring S E a h) n

end IsK

/-! ## 2. Item 4: the honest walk is `𝕂`-valued at a `𝕂`-valued coin -/

section WalkK
variable {K : Type} [Field K] [Fintype K] {d : K} [Fact (¬ IsSquare d)]

/-- **`Im(cnt) = 0`** on `1..h` when the walk coin is `𝕂`-valued. -/
theorem HonestWalk.cnt_isK (D : HonestWalk (Quad d)) (hα : Quad.im d D.α = 0) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ D.W.length) : Quad.im d (D.cnt k) = 0 := by
  rw [quad_im_eq_zero_iff] at hα ⊢
  rw [Walk.count_closed D.sat k hk1 hk]
  exact (algebraMap K (Quad d)).range.mul_mem hα ((algebraMap K (Quad d)).range.pow_mem hα _)

/-- **`Im(ln) = 0`** on `1..h` when the walk coin is `𝕂`-valued. -/
theorem HonestWalk.ln_isK (D : HonestWalk (Quad d)) (hα : Quad.im d D.α = 0) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ D.W.length) : Quad.im d (D.ln k) = 0 := by
  rw [quad_im_eq_zero_iff] at hα ⊢
  rw [Walk.ln_closed D.sat k hk1 hk]
  exact (algebraMap K (Quad d)).range.pow_mem hα _

/-- **The queue inverse `(cnt − ln)⁻¹` is `𝕂`-valued** on `1..h`. -/
theorem HonestWalk.inv_isK (D : HonestWalk (Quad d)) (hα : Quad.im d D.α = 0) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ D.W.length) : Quad.im d ((D.cnt k - D.ln k)⁻¹) = 0 := by
  have hc := (quad_im_eq_zero_iff d _).mp (D.cnt_isK hα k hk1 hk)
  have hl := (quad_im_eq_zero_iff d _).mp (D.ln_isK hα k hk1 hk)
  obtain ⟨a, ha⟩ := (algebraMap K (Quad d)).range.sub_mem hc hl
  rw [quad_im_eq_zero_iff]
  exact ⟨a⁻¹, by rw [map_inv₀, ha]⟩

end WalkK

/-! ## 3. Item 5: the residual roles `58/59`, non-circularly -/

/-- The trace-role reads of the residual sources: a role with an Im column other than `59`, or role
`61` (`𝕂`-valued walk line). -/
def resRoleOk (c : ℕ) : Bool :=
  c = 74 || (decide (13 ≤ c ∧ c < 76 ∧ c ≠ 72) &&
    (if h : c - 13 < 63 then (towerM.ext ⟨c - 13, h⟩).isSome else false))

/-- **The residual sources read no column of roles `58/59`**: current-row reads are `W0/W1`, next-row
reads are `W0/W1`, selectors `< 13`, and roles in `resRoleOk` (never `58` = col `71`, `59` = col `72`);
the rest are challenges.  Checked by `decide`. -/
theorem residual_reads_class :
    ∀ e ∈ [walkCountStep309, walkAccStep309], ∀ p ∈ readsE e,
      (p.1 = .traceCur ∧ (p.2 = 303 ∨ p.2 = 306)) ∨
      (p.1 = .traceNext ∧ (p.2 = 303 ∨ p.2 = 306 ∨ p.2 < 13 ∨ resRoleOk p.2 = true)) ∨
      p.1 = .challenge := by
  decide +kernel

theorem resRoleOk_spec (c : ℕ) (h : resRoleOk c = true) :
    13 ≤ c ∧ c < 76 ∧ c ≠ 71 ∧ c ≠ 72 ∧
      (c = 74 ∨ ∃ hc : c - 13 < 63, (towerM.ext ⟨c - 13, hc⟩).isSome = true) := by
  unfold resRoleOk at h
  by_cases h74 : c = 74
  · subst h74; decide
  · simp only [h74, decide_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
    have h5 : c - 13 < 63 := by omega
    rw [dif_pos h5] at h4
    refine ⟨h1, h2, ?_, h3, Or.inr ⟨h5, h4⟩⟩
    rintro rfl
    revert h5 h4
    decide +kernel

section Residual
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **The residual read environment of a row pair**: current-row `W0/W1`; next-row `W0/W1`, base, and
roles with `58/59` ZEROED; challenges `ch`; no publics. -/
def rowSrcEnv (v v' : TowerRowVals (K := K) δ) (ch : ℕ → Quad (algebraMap F K δ)) :
    Env (Quad (algebraMap F K δ)) where
  trace c := if c = 303 then v.walk 0 else if c = 306 then v.walk 1 else 0
  traceNext c := if c = 303 then v'.walk 0 else if c = 306 then v'.walk 1
    else if h : c < 13 then algebraMap F _ (v'.base ⟨c, h⟩)
    else if h : c < 76 then (if c = 71 ∨ c = 72 then 0 else v'.ext ⟨c - 13, by omega⟩) else 0
  chal := ch
  pub := fun _ => 0

/-- **The honest residual value** `j ∈ {0, 1}` of a row pair (no reference to roles `58/59`). -/
def residualVal (j : Fin 2) (v v' : TowerRowVals (K := K) δ) (ch : ℕ → Quad (algebraMap F K δ)) :
    Quad (algebraMap F K δ) :=
  if j = 0 then walkCountStep309.eval (rowSrcEnv v v' ch) else walkAccStep309.eval (rowSrcEnv v v' ch)

/-- **Irrelevance**: the residual read environment does not depend on roles `58/59` of either row. -/
theorem rowSrcEnv_ext5859_irrel (v v' w w' : TowerRowVals (K := K) δ) (ch : ℕ → Quad (algebraMap F K δ))
    (hw : v.walk = w.walk) (hw' : v'.walk = w'.walk) (hb' : v'.base = w'.base)
    (he' : ∀ r : Fin 63, r.val ≠ 58 → r.val ≠ 59 → v'.ext r = w'.ext r) :
    rowSrcEnv v v' ch = rowSrcEnv w w' ch := by
  unfold rowSrcEnv
  congr 1
  · funext c; simp only [hw]
  · funext c
    simp only [hw', hb']
    split_ifs with h1 h2 h3 h4 h5 <;> try rfl
    exact he' _ (by simp; omega) (by simp; omega)

variable [FiniteDimensional F K]

/-- **The residual equations at the tower env** (`WalkRowEnv.r58/r59`'s right-hand sides): with the
current and next rows placed (`hF`, `hFn`), `W0` of both rows and role `61` of the next row `𝕂`-valued,
the residual sources at the tower env are `residualVal` of the row pair, at the env's challenges. -/
theorem residual_eq_of_fill (b : Basis (Fin 3) F K) (v v' : TowerRowVals (K := K) δ) (eF : Env F)
    (hF : ∀ c, SrcRead c → eF.trace c = srcColT b v c)
    (hFn : ∀ c, SrcRead c → eF.traceNext c = srcColT b v' c)
    (hW0 : Quad.im _ (v.walk 0) = 0) (hW0' : Quad.im _ (v'.walk 0) = 0)
    (h61' : Quad.im _ (v'.ext 61) = 0) (j : Fin 2) :
    (residualSource309 j).eval (towerEnv309 δ towerM (gatherEnv b eF) eF) =
      residualVal j v v' (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv.chal := by
  set env := towerEnv309 δ towerM (gatherEnv b eF) eF with henv
  have agree : ∀ e ∈ [walkCountStep309, walkAccStep309], ∀ p ∈ readsE e,
      varVal env.toSourceEnv p.1 p.2 = varVal (rowSrcEnv v v' env.toSourceEnv.chal) p.1 p.2 := by
    intro e he p hp
    rcases residual_reads_class e he p hp with ⟨hk, hc⟩ | ⟨hk, hc⟩ | hk
    · obtain ⟨k, c⟩ := p
      simp only at hk hc
      subst hk
      rcases hc with rfl | rfl
      · show env.toSourceEnv.trace 303 = (rowSrcEnv v v' _).trace 303
        simp only [Env309.toSourceEnv, rowSrcEnv, if_true]
        exact towerEnv309_walk_of_src b v eF hF hW0 0
      · show env.toSourceEnv.trace 306 = (rowSrcEnv v v' _).trace 306
        simp only [Env309.toSourceEnv, rowSrcEnv, if_true, show (306 : ℕ) ≠ 303 by decide, if_false]
        exact towerEnv309_walk_of_src b v eF hF hW0 1
    · obtain ⟨k, c⟩ := p
      simp only at hk hc
      subst hk
      show env.toSourceEnv.traceNext c = (rowSrcEnv v v' _).traceNext c
      rcases hc with rfl | rfl | hc | hc
      · simp only [Env309.toSourceEnv, rowSrcEnv, if_true]
        exact towerEnv309_walkNext_of_src b v' eF hFn hW0' 0
      · simp only [Env309.toSourceEnv, rowSrcEnv, if_true, show (306 : ℕ) ≠ 303 by decide, if_false]
        exact towerEnv309_walkNext_of_src b v' eF hFn hW0' 1
      · have a1 : c ≠ 303 := by omega
        have a2 : c ≠ 306 := by omega
        simp only [Env309.toSourceEnv, rowSrcEnv, a1, a2, if_false, CorrectedFinalTypedEnv.toSourceEnv,
          hc, dif_pos]
        congr 1
        exact towerEnv309_baseNext_of_src b v' eF hFn ⟨c, hc⟩
      · obtain ⟨h13, h76, h71, h72, hrole⟩ := resRoleOk_spec c hc
        have a1 : c ≠ 303 := by omega
        have a2 : c ≠ 306 := by omega
        have a3 : ¬ c < 13 := by omega
        have a4 : ¬ (c = 71 ∨ c = 72) := by omega
        simp only [Env309.toSourceEnv, rowSrcEnv, a1, a2, if_false, CorrectedFinalTypedEnv.toSourceEnv,
          a3, h76, dif_neg, dif_pos, a4, not_false_eq_true]
        apply towerEnv309_extNext_of_src b v' eF hFn
        intro hn
        rcases hrole with h74 | ⟨hc', hs⟩
        · subst h74; exact h61'
        · rw [hn] at hs; exact absurd hs (by decide)
    · obtain ⟨k, c⟩ := p
      simp only at hk
      subst hk
      rfl
  fin_cases j
  · show (residualSource309 0).eval env = _
    rw [residual0_eval]
    simp only [residualVal, Fin.zero_eta, if_true]
    exact eval_congr_reads _ (agree _ (by simp))
  · show (residualSource309 1).eval env = _
    rw [residual1_eval]
    simp only [residualVal, Fin.mk_one, show (1 : Fin 2) ≠ 0 by decide, if_false]
    exact eval_congr_reads _ (agree _ (by simp))

/-- **`WalkRowEnv.r58 / r59` at the honest fill**: if the row's roles `58/59` carry `residualVal` of the
row pair (role `58` additionally `𝕂`-valued: it has no Im column), the tower env meets both equations. -/
theorem r5859_of_fill (b : Basis (Fin 3) F K) (v v' : TowerRowVals (K := K) δ) (eF : Env F)
    (hF : ∀ c, SrcRead c → eF.trace c = srcColT b v c)
    (hFn : ∀ c, SrcRead c → eF.traceNext c = srcColT b v' c)
    (hW0 : Quad.im _ (v.walk 0) = 0) (hW0' : Quad.im _ (v'.walk 0) = 0)
    (h61' : Quad.im _ (v'.ext 61) = 0)
    (h58 : v.ext 58 = residualVal 0 v v' (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv.chal)
    (h59 : v.ext 59 = residualVal 1 v v' (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv.chal)
    (h58K : Quad.im _ (v.ext 58) = 0) :
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.extTrace 58 =
        (residualSource309 0).eval (towerEnv309 δ towerM (gatherEnv b eF) eF) ∧
      (towerEnv309 δ towerM (gatherEnv b eF) eF).base.extTrace 59 =
        (residualSource309 1).eval (towerEnv309 δ towerM (gatherEnv b eF) eF) := by
  refine ⟨?_, ?_⟩
  · rw [towerEnv309_ext_of_src b v eF hF 58 (fun _ => h58K), residual_eq_of_fill b v v' eF hF hFn hW0 hW0'
      h61' 0]
    exact h58
  · rw [towerEnv309_ext_of_src b v eF hF 59 (fun h => absurd h (by decide)),
      residual_eq_of_fill b v v' eF hF hFn hW0 hW0' h61' 1]
    exact h59

/-- **The residual-`58` value is `𝕂`-valued** when `W0` of both rows and challenge `6` are (the only
non-base reads of `walkCountStep309`); so `h58K` above is satisfiable at honest data. -/
theorem residualVal_zero_isK (v v' : TowerRowVals (K := K) δ) (ch : ℕ → Quad (algebraMap F K δ))
    (hW0 : Quad.im _ (v.walk 0) = 0) (hW0' : Quad.im _ (v'.walk 0) = 0) (h6 : Quad.im _ (ch 6) = 0) :
    Quad.im _ (residualVal 0 v v' ch) = 0 := by
  have hcls : ∀ p ∈ readsE walkCountStep309,
      (p.1 = .traceCur ∧ p.2 = 303) ∨ (p.1 = .traceNext ∧ (p.2 = 303 ∨ p.2 < 11)) ∨
        (p.1 = .challenge ∧ p.2 = 6) := by decide +kernel
  simp only [residualVal, if_true]
  rw [quad_im_eq_zero_iff]
  apply eval_mem_subring
  intro p hp
  rcases hcls p hp with ⟨hk, hc⟩ | ⟨hk, hc⟩ | ⟨hk, hc⟩ <;> obtain ⟨k, c⟩ := p <;> simp only at hk hc <;>
    subst hk
  · subst hc
    show (rowSrcEnv v v' ch).trace 303 ∈ _
    simp only [rowSrcEnv, if_true]
    exact (quad_im_eq_zero_iff _ _).mp hW0
  · show (rowSrcEnv v v' ch).traceNext c ∈ _
    rcases hc with rfl | hc
    · simp only [rowSrcEnv, if_true]
      exact (quad_im_eq_zero_iff _ _).mp hW0'
    · have a1 : c ≠ 303 := by omega
      have a2 : c ≠ 306 := by omega
      simp only [rowSrcEnv, a1, a2, if_false, show c < 13 by omega, dif_pos]
      exact ⟨algebraMap F K (v'.base ⟨c, by omega⟩), (IsScalarTower.algebraMap_apply F K _ _).symm⟩
  · subst hc
    exact (quad_im_eq_zero_iff _ _).mp h6

end Residual

/-! ## 4. Item 6: the per-row placement hypotheses at the interpolated honest trace -/

section Place
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **`hF` at row `i`** of the honest trace (the source env of every C1/C2 placement lemma). -/
theorem honestQT_hF (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F) (hinj : Function.Injective nodes)
    (rows : Fin n → TowerRowVals (K := K) δ) (ω : F) (cv pv : ℕ → F) (i : Fin n) :
    ∀ c, SrcRead c →
      (pullEnv (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv)).trace c =
        srcColT b (rows i) c :=
  fun c hc => pull_honestQT_trace b nodes hinj rows ω cv pv i c hc

/-- **`hFn` at row `i`** with successor `i'` (`ω·x_i = x_{i'}`, the cyclic successor). -/
theorem honestQT_hFn (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F) (hinj : Function.Injective nodes)
    (rows : Fin n → TowerRowVals (K := K) δ) (ω : F) (cv pv : ℕ → F) (i i' : Fin n)
    (hadj : ω * nodes i = nodes i') :
    ∀ c, SrcRead c →
      (pullEnv (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv)).traceNext c =
        srcColT b (rows i') c :=
  fun c hc => pullNext_honestQT_trace b nodes hinj rows ω cv pv i i' hadj c hc

end Place

/-! ## 5. Item 1 consumer: the slot inverses of `lookupGatesT_honest` read back from the fill -/

section Inv
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **The three slot-inverse `Q`-values (Re and Im) at a row filled by `vclFill`** are the filled values:
`hinv0/1/2` of `lookupGatesT_honest` reduce to the fill choosing `inv_j := den_j′⁻¹`. -/
theorem vclFill_invQ (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F) (hinj : Function.Injective nodes)
    (rows : Fin n → TowerRowVals (K := K) δ) (ω : F) (cv pv : ℕ → F) (i : Fin n)
    (ser : F) (ax : ℕ) (fIdx vI0 vI1 : F) (inv0 inv1 inv2 accX accP : Quad (algebraMap F K δ))
    (hv : (rows i).vcl = vclFill b ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP) :
    Q.val δ (invQ F inv0Base (invImBase 0))
        (gatherEnv b (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv))
        (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv) = inv0 ∧
      Q.val δ (invQ F (lookupInvBase 0) (invImBase 1))
        (gatherEnv b (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv))
        (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv) = inv1 ∧
      Q.val δ (invQ F (lookupInvBase 1) (invImBase 2))
        (gatherEnv b (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv))
        (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv) = inv2 := by
  have re1 : ∀ k : Fin 3, vclFill (δ := δ) b ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP
      (lookupInvBase 0 + k) = coord b (Quad.re _ inv1) k := by
    intro k; fin_cases k <;>
      simp [vclFill, limbAt, z1Col, inv0Base, lookupInvBase, accExportBase, accPathBase, invImBase, accImExport,
        accImPath, coord]
  have re2 : ∀ k : Fin 3, vclFill (δ := δ) b ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP
      (lookupInvBase 1 + k) = coord b (Quad.re _ inv2) k := by
    intro k; fin_cases k <;>
      simp [vclFill, limbAt, z1Col, inv0Base, lookupInvBase, accExportBase, accPathBase, invImBase, accImExport,
        accImPath, coord]
  refine ⟨?_, ?_, ?_⟩
  · exact invQ_val_honestQT b nodes hinj rows ω cv pv i _ _ (Or.inr (by simp [inv0Base]))
      (by simp [invImBase]) inv0 (fun k => by rw [hv]; exact vclFill_inv0 b _ _ _ _ _ _ _ _ _ _ k)
      (fun k => by rw [hv]; exact (vclFill_invIm b _ _ _ _ _ _ _ _ _ _ k).1)
  · exact invQ_val_honestQT b nodes hinj rows ω cv pv i _ _ (Or.inr (by simp [lookupInvBase]))
      (by simp [invImBase]) inv1 (fun k => by rw [hv]; exact re1 k)
      (fun k => by rw [hv]; exact (vclFill_invIm b _ _ _ _ _ _ _ _ _ _ k).2.1)
  · exact invQ_val_honestQT b nodes hinj rows ω cv pv i _ _ (Or.inr (by simp [lookupInvBase]))
      (by simp [invImBase]) inv2 (fun k => by rw [hv]; exact re2 k)
      (fun k => by rw [hv]; exact (vclFill_invIm b _ _ _ _ _ _ _ _ _ _ k).2.2)

end Inv

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
