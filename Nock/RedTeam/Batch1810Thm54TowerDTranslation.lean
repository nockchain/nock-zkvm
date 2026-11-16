/-
  Nock/RedTeam/Batch1810Thm54TowerDTranslation.lean

  **Route (d) phase 1 — the `(Re, Im)` translation.**

  * §C negative controls: `qmul`'s Im sign flipped admits a false product (`flipped_qmul_fires`);
    the Im twin of core gate 27 dropped admits a hostile Im limb (`dropped_im_twin_admits_hostile`).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerD
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false
set_option maxRecDepth 300000

namespace Nock.RedTeam.Batch1810

open Nock Nock.Reified Module
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD

/-! ## A. Measurements -/

def exprTraceVars : Expr → List ℕ
  | .Var .traceCur i => [i]
  | .Var .traceNext i => [i]
  | .Var _ _ => []
  | .Const _ => []
  | .Add x y => exprTraceVars x ++ exprTraceVars y
  | .Sub x y => exprTraceVars x ++ exprTraceVars y
  | .Neg x => exprTraceVars x
  | .Mul x y => exprTraceVars x ++ exprTraceVars y
  | .Pow x _ => exprTraceVars x

def fpSourceSlots : List ℕ :=
  (List.range 54).map (· + 11) ++ (List.range 6).map (· + 67) ++ (List.range 6).map (· + 75) ++
    (List.range 6).map (· + 83)

def fpRawCols : List ℕ :=
  (fpSourceSlots.flatMap fun i => exprTraceVars (computeTraceSubst .traceCur i)).eraseDups

/-- **The fingerprint roles, re-measured**: the extension roles carrying an FP coordinate under
`computeTraceSubst` are exactly `fpRoleList` (`0..31`, `36..53`). -/
theorem fpRoleList_eq_measured :
    (List.range 63).filter (fun r => fpRawCols.contains (13 + r)) = fpRoleList := by
  decide +kernel

def core (i : ℕ) : CorrectedFinalTypedExpr := correctedLoweredExt.getD i (.const 0)

theorem hasIm_core_fpImMap :
    ((List.range 82).filter fun i => hasIm fpImMap (core i)).length = 76 := by
  decide +kernel

/-- Every other gate's existing body is its Re twin
(`appendOnly_iff`). -/
theorem nonLinear_core_fpImMap :
    (List.range 82).filter (fun i => !qLinear fpImMap (core i)) =
      [0, 1, 2, 3, 4, 5, 29, 30, 31, 32, 34, 35, 36, 37, 38, 39, 42, 59, 60, 61, 62, 63, 64, 69,
        70, 71, 75, 78, 79, 80] := by
  decide +kernel

/-- The map with the two inverse witnesses (roles 56, 57) also `𝕂′` (Im at `382`, `385`). -/
def invImMap : ImMap := (fpImMap.addExt 56 382).addExt 57 385

/-- With the inverse witnesses `𝕂′`, gates 33 and 67 also need `qmul`. -/
theorem nonLinear_core_inv :
    (List.range 82).filter (fun i => !qLinear invImMap (core i)) =
      [0, 1, 2, 3, 4, 5, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 42, 59, 60, 61, 62, 63, 64,
        67, 69, 70, 71, 75, 78, 79, 80] := by
  decide +kernel

/-- The endpoints: `ep2` 1, 2 and `ep4` carry an Im half; all are `qLinear`. -/
theorem endpoints_fpImMap :
    correctedEndpoint2.map (fun g => (hasIm fpImMap g, qLinear fpImMap g)) =
      [(false, true), (true, true), (true, true), (false, true), (false, true), (false, true)] ∧
    correctedEndpoint4.map (fun g => (hasIm fpImMap g, qLinear fpImMap g)) = [(true, true)] := by
  constructor <;> decide +kernel

/-! ## B. -/

section KeyDen
variable (F : Type) [Field F]

/-- A `𝕂′` coin as a pair of `𝕂` coin slots (raw limb bases). -/
def qchal (i i' : ℕ) : Q F := (.Var .challenge i, .Var .challenge i')

/-- `den′ = ρ′ + Σ_{c<m} γ′^c · rec_c` over `𝕂′`. -/
def keyDenQ (δ : F) (γ γ' ρ ρ' : ℕ) : (m : ℕ) → (Fin m → Q F) → Q F
  | 0, _ => qchal F ρ ρ'
  | m + 1, rec =>
      qadd F (keyDenQ δ γ γ' ρ ρ' m fun c => rec c.castSucc)
        (qmul F δ (qpow F δ (qchal F γ γ') m) (rec (Fin.last m)))

/-- The export record's 10 entries at route (d)'s columns: Re at roles `0..9`, Im at `fpImCol`. -/
def exportRecQ : Fin 10 → Q F := fun c =>
  qvar F .traceCur (13 + 3 * (c : ℕ)) (fpImCol ⟨c, by omega⟩)

def slotGateQ (δ : F) (γ γ' ρ ρ' : ℕ) (invRe invIm : ℕ) (act : CoeffExpr F) : Q F :=
  qsub F (qmul F δ (qvar F .traceCur invRe (some invIm)) (keyDenQ F δ γ γ' ρ ρ' 10 (exportRecQ F)))
    (.Lift act, .Const 0)

/-- IO coins at route (d)'s slots: `γ′ = (7, 14)`, `ρ′ = (8, 15)` (raw limb bases 21/42, 24/45). -/
theorem keyDenQ_degree : qdeg ℚ (keyDenQ ℚ 7 21 42 24 45 10 (exportRecQ ℚ)) = 1 := by
  decide +kernel

theorem slotGateQ_degree :
    qdeg ℚ (slotGateQ ℚ 7 21 42 24 45 214 388 (.var .traceCur 6)) = 2 := by
  decide +kernel

section Val
variable {K : Type} [Field K] [Algebra F K] (δ : F) (eK : Env K) (eF : Env F)

/-- **The pair gate is the `𝕂′` denominator**: `ρ′ + Σ_c γ′^c · rec_c`. -/
theorem keyDenQ_val (γ γ' ρ ρ' : ℕ) : ∀ (m : ℕ) (rec : Fin m → Q F),
    Q.val δ (keyDenQ F δ γ γ' ρ ρ' m rec) eK eF =
      Q.val δ (qchal F ρ ρ') eK eF +
        ∑ c : Fin m, Q.val δ (qchal F γ γ') eK eF ^ (c : ℕ) * Q.val δ (rec c) eK eF
  | 0, _ => by simp [keyDenQ]
  | m + 1, rec => by
      rw [keyDenQ, qadd_val, keyDenQ_val γ γ' ρ ρ' m, qmul_val, qpow_val, Fin.sum_univ_castSucc]
      simp [add_assoc]

end Val
end KeyDen

/-! ## C. Negative controls -/

section NC
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- `qmul` with its Im sign flipped: `(ac + δbd) + (ad − bc)√δ`. -/
def qmulFlip (δ : F) (a b : Q F) : Q F :=
  (.Add (.Mul a.1 b.1) (.Scale (.const δ) (.Mul a.2 b.2)), .Sub (.Mul a.1 b.2) (.Mul a.2 b.1))

/-- **NC (a): the flipped sign fires.**  The cons-size shape `w − x·y` with `x = √δ`, `y = 1`,
`w = −√δ`: the true pair is NOT zero (the `𝕂′` gate fails, `toQ_isZero_iff`), the flipped pair IS
zero — the flipped translation would accept a false product (char `≠ 2`). -/
theorem flipped_qmul_fires (δ : F) (h2 : (2 : K) ≠ 0) :
    ∃ eK : Env K, ∀ eF : Env F,
      Q.IsZero (qsub F (qvar F .traceCur 4 (some 5))
          (qmulFlip δ (qvar F .traceCur 0 (some 1)) (qvar F .traceCur 2 (some 3)))) eK eF ∧
      ¬ Q.IsZero (qsub F (qvar F .traceCur 4 (some 5))
          (qmul F δ (qvar F .traceCur 0 (some 1)) (qvar F .traceCur 2 (some 3)))) eK eF := by
  refine ⟨⟨fun c => if c = 1 then 1 else if c = 2 then 1 else if c = 5 then -1 else 0,
    fun _ => 0, fun _ => 0, fun _ => 0⟩, fun eF => ⟨?_, ?_⟩⟩
  · simp [Q.IsZero, qsub, qmulFlip, qvar, MixedExpr.eval, CoeffExpr.eval]
  · simp only [Q.IsZero, qsub, qmul, qvar, MixedExpr.eval, CoeffExpr.eval]
    intro ⟨_, h⟩
    apply h2
    norm_num at h
    exact h

/-- Core gate 27 (the atom test `b0·(size − z)`, the paper). -/
def g27 : CorrectedFinalTypedExpr :=
  .add (.mul (.baseCur 0) (.sub (.extCur 39) (.challenge 1))) (.const 0)

theorem core27_eq : core 27 = g27 := by decide +kernel

theorem g27_linear : qLinear fpImMap g27 = true := by decide

/-- The hostile raw trace: selector `b0 = 1`, the Re limbs of role 39 equal to `z`'s (both `0`), and
ONE Im limb of role 39 (raw `337 = fpImCol 39`) set to `1`. -/
def hostileF : Env F :=
  ⟨fun c => if c = 0 then 1 else if c = 337 then 1 else 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

theorem fpImCol_39 : fpImCol 39 = some 337 := by decide

/-- **NC (b): one Im twin dropped admits a hostile Im limb.**  At `hostileF` the chip's existing
compiled gate 27 (the Re twin) vanishes in every coordinate, the appended Im twin does not, and the
`𝕂′` gate fails at the tower reading.  Dropping the Im twin from the chip would accept it. -/
theorem dropped_im_twin_admits_hostile [FiniteDimensional F K] (b : Basis (Fin 3) F K) (δ : F)
    [Fact (¬ IsSquare (algebraMap F K δ))] :
    (∀ k, (correctedFinalTypedCompile b g27 k).eval hostileF = 0) ∧
      ¬ (∀ k, (mixedCompile b col0Id
          (toQ F fpImMap (MemoryTable.pwScaleExp K) δ g27).2 k).eval hostileF = 0) ∧
      g27.eval (towerEnv δ fpImMap (gatherEnv b hostileF) hostileF) ≠ 0 := by
  have h := isCoordEnv_gather b (hostileF (F := F))
  have hb0 : b 0 ≠ 0 := b.ne_zero 0
  have hre : (toQ F fpImMap (MemoryTable.pwScaleExp K) δ g27).1.eval (gatherEnv b hostileF)
      hostileF = 0 := by
    simp [g27, toQ, qadd, qmul, qsub, qlift, qvar, qconst, fpImMap, fpImCol_39, towerChal,
      MixedExpr.eval, CoeffExpr.eval, gatherEnv, VclL.Compute.LogUp.limbVal, Fin.sum_univ_three,
      hostileF]
  have him : (toQ F fpImMap (MemoryTable.pwScaleExp K) δ g27).2.eval (gatherEnv b hostileF)
      hostileF = b 0 := by
    simp [g27, toQ, qadd, qmul, qsub, qlift, qvar, qconst, fpImMap, fpImCol_39, towerChal,
      MixedExpr.eval, CoeffExpr.eval, gatherEnv, VclL.Compute.LogUp.limbVal, Fin.sum_univ_three,
      hostileF]
  refine ⟨?_, ?_, ?_⟩
  · rw [correctedFinalTypedCompile_zero_iff b _ _ (isCorrectedFinalCoordEnv_reEnv b h),
      ← toQ_fst_eval_of_qLinear δ fpImMap _ rfl _ _ g27 g27_linear]
    exact hre
  · rw [← mixedCompile_zero_iff b col0Id h, him]; exact hb0
  · intro hz
    have h2 := ((toQ_isZero_iff δ fpImMap _ rfl _ _ g27).mpr hz).2
    rw [him] at h2
    exact hb0 h2

/-! ## D. Finding: the inverse witness 57 must be `𝕂′` -/

/-- Core gate 34, `b3·(z − size)·(inv_gen·(z − size) − 1)` (`inv_gen` = role 57). -/
def g34 : CorrectedFinalTypedExpr :=
  .mul (.baseCur 3) (.mul (.sub (.challenge 1) (.extCur 15))
    (.sub (.mul (.extCur 57) (.sub (.challenge 1) (.extCur 15))) (.const 1)))

theorem core34_eq : core 34 = g34 := by decide +kernel

theorem fpImCol_15 : fpImCol 15 = some 277 := by decide
theorem fpImCol_57 : fpImCol 57 = none := by decide

/-- **The obstruction**: under route (d)'s map as specified (`fpImMap`: role 57 has no Im), the
`𝕂′` gate 34 FAILS at every row with `b3 = 1` whose `z′ − size′` has a nonzero Im half — an
element of `𝕂` cannot invert an element outside `𝕂`.  The honest `inv_gen` is `(z′ − size′)⁻¹`,
so the honest op-3 rows are rejected unless role 57 also gets an Im role (`invImMap`). -/
theorem fpImMap_inv_gen_obstruction (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]
    (eK : Env K) (eF : Env F) (hb3 : eF.trace 3 = 1) (him : eK.chal 36 - eK.trace 277 ≠ 0) :
    g34.eval (towerEnv δ fpImMap eK eF) ≠ 0 := by
  set d := algebraMap F K δ
  have hD : (towerEnv δ fpImMap eK eF).chal 1 - (towerEnv δ fpImMap eK eF).extTrace 15 =
      Quad.mk d (eK.chal 3 - eK.trace 58) (eK.chal 36 - eK.trace 277) := by
    simp [towerEnv, fpImMap, towerChal, fpImCol_15, imVal, Quad.mk_sub, d]
  have h57 : (towerEnv δ fpImMap eK eF).extTrace 57 = Quad.mk d (eK.trace 184) 0 := by
    simp [towerEnv, fpImMap, fpImCol_57, imVal, d]
  simp only [g34, CorrectedFinalTypedExpr.eval, hD, h57]
  have hb : algebraMap F (Quad d) ((towerEnv δ fpImMap eK eF).baseTrace 3) = 1 := by
    simp [towerEnv, hb3]
  rw [hb, one_mul]
  intro h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact him ((Quad.mk_eq_zero_iff d _ _).mp h).2
  · rw [Quad.mk_mul, show ((1 : ℤ) : Quad d) = Quad.mk d 1 0 by simp [Quad.mk_one'], Quad.mk_sub,
      Quad.mk_eq_zero_iff] at h
    obtain ⟨h1, h2⟩ := h
    have ha : eK.trace 184 = 0 := by
      have : eK.trace 184 * (eK.chal 36 - eK.trace 277) = 0 := by linear_combination h2
      exact (mul_eq_zero.mp this).resolve_right him
    rw [ha] at h1
    norm_num at h1

end NC

end Nock.RedTeam.Batch1810

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.limbVal_tower
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerBasis_apply
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.fpImCol_ge_width
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.fpImCol_lt
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.fpImCol_disjoint
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.toQ_val
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.toQW_val
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.toQ_isZero_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.toQ_compiled_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.toQW_compiled_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.appendOnly_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.toQ_qdeg_le
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerTwin_degree_le_four
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.isCoordEnv_gather
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.ringChar_quad
#print axioms Nock.RedTeam.Batch1810.fpRoleList_eq_measured
#print axioms Nock.RedTeam.Batch1810.hasIm_core_fpImMap
#print axioms Nock.RedTeam.Batch1810.nonLinear_core_fpImMap
#print axioms Nock.RedTeam.Batch1810.nonLinear_core_inv
#print axioms Nock.RedTeam.Batch1810.endpoints_fpImMap
#print axioms Nock.RedTeam.Batch1810.keyDenQ_val
#print axioms Nock.RedTeam.Batch1810.keyDenQ_degree
#print axioms Nock.RedTeam.Batch1810.slotGateQ_degree
#print axioms Nock.RedTeam.Batch1810.flipped_qmul_fires
#print axioms Nock.RedTeam.Batch1810.dropped_im_twin_admits_hostile
#print axioms Nock.RedTeam.Batch1810.fpImMap_inv_gen_obstruction
