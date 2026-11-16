/-
  NockvmE2E/Exec/VKSpec.lean   (pcs (b),  section 2; KERNEL-checked, Mathlib)

  The SPEC verifier key `vkSpec` (defined, executably, in `VKSpecExe.lean`) and its link to the proof model:
    * `fj XI col : (ZMod p)[X]` : the fixed polynomials f_j (pre columns from the instance's coefficients, `Z_H`, one `Zout` per short table);
    * `fixTrue_eq_fj`   : `toKV (fixTrue XI col pt) = eval (toKV pt) (fj XI col)`           (the link to `FixFail`'s `fixTrue`);
    * `specWord_eval`   : the committed word of column `col` at FRI-domain index `i` is `f_j(dShift * dGen^i)`   (the spec leaves);
    * `natDegree_fj_le` : `deg f_j <= hN` (`hpd` from `j8ShapeOk`, `hN = 2^(k+1)`: `natDegree_fj_le_J8`);
    * `HSpec XI`        : the NAMED HYPOTHESIS `forall Hf, setup' XI Hf = some (vkSpec XI Hf)` (deployed setup = spec; NOT proved here: the
                          deployed `setup'` uses `while` loops, `partial` and an NTT; the executed comparison is `nockvm-e2e-vkspec`).
  No axiom, no `sorry`.
-/
import NockvmE2E.Exec.SoundOnlineP
import NockvmE2E.Exec.VKSpecExe
import NockvmE2E.Exec.J8Shape

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec.VF NockvmE2E.Exec.VL

section Spec
open Polynomial

/-- the fixed polynomial `f_j` of column `col` (the mathematical object the committed word is the LDE of) -/
noncomputable def fj (XI : ExecInst) : FixCol → (ZMod NockvmE2E.Exec.p)[X]
  | .pre c => ∑ m ∈ Finset.range XI.pre[c]!.size, C (zv (XI.pre[c]!)[m]!) * Polynomial.X ^ m
  | .zh => ∏ i ∈ Finset.range XI.hN, (Polynomial.X - C (zv XI.hShift * zv XI.hGen ^ i))
  | .zout t => ∏ i ∈ Finset.range (XI.hN - tabHN XI t), (Polynomial.X - C (zv XI.hShift * zv XI.hGen ^ (tabHN XI t + i)))

/-! ### the K3 link: `fixTrue` is the evaluation of `f_j` -/

theorem fixTrue_eq_fj (XI : ExecInst) (hS : canon XI.hShift) (hpre : ∀ c : ℕ, ∀ a ∈ XI.pre[c]!.toList, canon a)
    (col : FixCol) (pt : VF.K3) (hz : canon3 pt) :
    toKV (fixTrue XI col pt) = eval (toKV pt) ((fj XI col).map (algebraMap (ZMod NockvmE2E.Exec.p) KC)) := by
  cases col with
  | pre c =>
    unfold fixTrue
    rw [DagSem.toKV_hornerG _ _ (hpre c)]
    simp only [fj, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      Polynomial.eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rfl
  | zh =>
    unfold fixTrue zhEval
    rw [(zh_prod pt hz XI.hShift XI.hGen hS XI.hN).1]
    simp only [fj, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X, eval_prod, eval_sub, eval_C, eval_X]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [psiV, map_mul, map_pow]
  | zout t =>
    unfold fixTrue zoutEval
    have hc : canon (VF.mul XI.hShift (VF.pow XI.hGen (tabHN XI t))) := mul_lt _ _
    rw [(zh_prod pt hz _ XI.hGen hc _).1, psiV_mul, psiV_pow]
    simp only [fj, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X, eval_prod, eval_sub, eval_C, eval_X]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [psiV, map_mul, map_pow, pow_add]
    ring

/-! ### the base-field link: the spec words are values of `f_j` -/

theorem hornerB_nil (x : G) : hornerB [] x = 0 := by unfold hornerB; rw [List.foldr_nil]
theorem hornerB_cons (x c : G) (l : List G) : hornerB (c :: l) x = VF.add (VF.mul (hornerB l x) x) c := by
  unfold hornerB; rw [List.foldr_cons]

theorem hornerB_step (x c : G) (l : List G) (hc : canon c)
    (h2 : zv (hornerB l x) = ∑ m ∈ Finset.range l.length, zv l[m]! * zv x ^ m) :
    zv (hornerB (c :: l) x) = ∑ m ∈ Finset.range (c :: l).length, zv (c :: l)[m]! * zv x ^ m := by
  have hs : ∑ m ∈ Finset.range l.length, zv l[m]! * zv x ^ (m + 1) =
      (∑ m ∈ Finset.range l.length, zv l[m]! * zv x ^ m) * zv x := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by rw [pow_succ, mul_assoc]
  rw [hornerB_cons, zv_add _ _ (mul_lt _ _) hc, zv_mul, h2, List.length_cons, Finset.sum_range_succ']
  simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, pow_zero, mul_one]
  rw [← hs]

theorem hornerB_canon (x : G) : ∀ (l : List G), (∀ a ∈ l, canon a) → canon (hornerB l x)
  | [], _ => by rw [hornerB_nil]; exact Gold.zero_lt
  | c :: l, h => by
    rw [hornerB_cons]
    exact add_lt _ _ (mul_lt _ _) (h c (by simp))

theorem hornerB_zv (x : G) : ∀ (l : List G), (∀ a ∈ l, canon a) →
    zv (hornerB l x) = ∑ m ∈ Finset.range l.length, zv l[m]! * zv x ^ m
  | [], _ => by
    rw [hornerB_nil, List.length_nil, Finset.range_zero, Finset.sum_empty, zv_zero]
  | c :: l, h => hornerB_step x c l (h c (by simp)) (hornerB_zv x l (fun a ha => h a (List.mem_cons_of_mem _ ha)))

theorem hornerB_spec (x : G) (l : List G) (h : ∀ a ∈ l, canon a) :
    canon (hornerB l x) ∧ zv (hornerB l x) = ∑ m ∈ Finset.range l.length, zv l[m]! * zv x ^ m :=
  ⟨hornerB_canon x l h, hornerB_zv x l h⟩

theorem prodLinG_spec (hGen x start : G) (hx : canon x) (hs : canon start) : ∀ n : ℕ,
    canon (prodLinG hGen x start n).1 ∧ canon (prodLinG hGen x start n).2 ∧
    zv (prodLinG hGen x start n).1 = ∏ i ∈ Finset.range n, (zv x - zv start * zv hGen ^ i) ∧
    zv (prodLinG hGen x start n).2 = zv start * zv hGen ^ n := by
  intro n
  induction n with
  | zero => exact ⟨Gold.one_lt, hs, by simp [prodLinG, zv_one], by simp [prodLinG]⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    have e : prodLinG hGen x start (n + 1) =
        (VF.mul (prodLinG hGen x start n).1 (VF.sub x (prodLinG hGen x start n).2), VF.mul (prodLinG hGen x start n).2 hGen) := by
      simp [prodLinG, List.range_succ, List.foldl_append]
    rw [e]
    refine ⟨mul_lt _ _, mul_lt _ _, ?_, ?_⟩
    · simp only []
      rw [zv_mul, zv_sub _ _ hx h2, h3, h4, Finset.prod_range_succ]
    · simp only []
      rw [zv_mul, h4]; ring

/-- the spec value of fixed column `col` at a canonical base point is the evaluation of `f_j` -/
theorem colG_eval (XI : ExecInst) (hS : canon XI.hShift) (hpre : ∀ c : ℕ, ∀ a ∈ XI.pre[c]!.toList, canon a)
    (col : FixCol) (x : G) (hx : canon x) : zv (colG XI col x) = eval (zv x) (fj XI col) := by
  cases col with
  | pre c =>
    simp only [colG, fj, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [(hornerB_spec x _ (hpre c)).2, Array.length_toList]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [getElem!_pos XI.pre[c]!.toList m (by simpa using hm), getElem!_pos XI.pre[c]! m hm]
    simp
  | zh =>
    simp only [colG, zhG, fj, eval_prod, eval_sub, eval_C, eval_X]
    exact (prodLinG_spec XI.hGen x XI.hShift hx hS XI.hN).2.2.1
  | zout t =>
    simp only [colG, zoutG, fj, eval_prod, eval_sub, eval_C, eval_X]
    have hc : canon (VF.mul XI.hShift (VF.pow XI.hGen (tabHN XI t))) := mul_lt _ _
    rw [(prodLinG_spec XI.hGen x _ hx hc (XI.hN - tabHN XI t)).2.2.1, zv_mul, zv_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_add]; ring

/-- **the spec leaf**: the committed word of column `col` at FRI-domain index `i` is `f_j(dShift * dGen^i)` -/
theorem specWord_eval (XI : ExecInst) (hS : canon XI.hShift) (hpre : ∀ c : ℕ, ∀ a ∈ XI.pre[c]!.toList, canon a)
    (col : FixCol) (i : ℕ) :
    zv (specWord XI col i) = eval (zv XI.dShift * zv XI.dGen ^ i) (fj XI col) := by
  unfold specWord domPt
  rw [colG_eval XI hS hpre col _ (mul_lt _ _), zv_mul, zv_pow]

/-! ### degree bounds -/

theorem natDegree_fj_le (XI : ExecInst) (hpd : ∀ c < XI.nc, XI.pre[c]!.size ≤ XI.hN + 1) (col : FixCol)
    (hcol : ∀ c, col = FixCol.pre c → c < XI.nc) : (fj XI col).natDegree ≤ XI.hN := by
  cases col with
  | pre c =>
    have hc := hpd c (hcol c rfl)
    refine natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
    rw [Finset.mem_range] at hm
    exact (natDegree_C_mul_X_pow_le (zv (XI.pre[c]!)[m]!) m).trans (Nat.le_of_lt_succ (lt_of_lt_of_le hm hc))
  | zh =>
    simp only [fj]
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => 1) fun i _ => ?_).trans (by simp)
    exact (natDegree_X_sub_C _).le
  | zout t =>
    simp only [fj]
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => 1) fun i _ => ?_).trans (by simp)
    exact (natDegree_X_sub_C _).le

theorem fixCols_pre_lt (XI : ExecInst) : ∀ col ∈ fixCols XI, ∀ c, col = FixCol.pre c → c < XI.nc := by
  intro col h c hc
  subst hc
  unfold fixCols at h
  simp only [Array.mem_append, Array.mem_map, Array.mem_filter, Array.mem_range] at h
  rcases h with (⟨a, ⟨ha, _⟩, e⟩ | h) | ⟨t, _, e⟩
  · simp only [FixCol.pre.injEq] at e; subst e; exact ha
  · simp at h
  · cases e


/-- the setup gates give a canonical `hShift` and canonical `pre` coefficients -/
theorem canon_of_gates {XI : ExecInst} (hg : setupGates XI = true) :
    canon XI.hShift ∧ ∀ c : ℕ, ∀ a ∈ XI.pre[c]!.toList, canon a := by
  have h1 : instCanon XI = true := by
    simp only [setupGates, Bool.and_eq_true] at hg; tauto
  simp only [instCanon, Bool.and_eq_true, Array.all_eq_true] at h1
  refine ⟨HdagU.canon_of_based _ h1.1.1.1.2, fun c a ha => ?_⟩
  by_cases hc : c < XI.pre.size
  · rw [getElem!_pos XI.pre c hc] at ha
    have h3 := h1.1.2 c hc
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    exact HdagU.canon_of_based _ (h3 j (by simpa using hj))
  · rw [getElem!_neg XI.pre c hc] at ha
    change a ∈ (#[] : Array G).toList at ha
    simp at ha

/-- **degree bound, J-8 shape**: every fixed polynomial has degree `<= hN = 2^(k+1)` -/
theorem natDegree_fj_le_J8 {XI : ExecInst} (hsh : J8Shape.j8ShapeOk XI = true) :
    ∀ col ∈ fixCols XI, (fj XI col).natDegree ≤ 2 ^ (XI.k + 1) := by
  intro col hcol
  rw [← J8Shape.hN_of_shape hsh]
  exact natDegree_fj_le XI (J8Shape.hpd_of_shape hsh) col (fixCols_pre_lt XI col hcol)

end Spec

/-! ### the spec VK and the named hypothesis -/

theorem eraseXS_eq (XI : ExecInst) : eraseXS XI = eraseX XI := rfl

/-- **`HSpec`** (NAMED HYPOTHESIS, label: executed, not proved): the deployed setup returns the spec VK, for every side hash.
Evidence: `nockvm-e2e-vkspec` (roots equal on the J-8 samples, real Tip5 and a toy hash).  Since HSpec  the setup is
total and structurally recursive (`VKSetupR.lean`: `nttR`, `cosetLdeR`, `prodLinR`; `fxSubRootF`), so it is provable;
`while` loops are not the blocker (Lean 4.35 unfolds them).  It holds only under `hN < 2^nD` (not implied by `setupGates`). -/
def HSpec (XI : ExecInst) : Prop := ∀ Hf : HFn, setup' XI Hf = some (vkSpec XI Hf)

/-- under `HSpec` and the gates, the honest VK of `exec_e2e_J8V'` (`vkSide = (mkVKData' _ Hf).vk`) IS the spec VK -/
theorem mkVKData'_vk_eq_vkSpec {XI : ExecInst} (hspec : HSpec XI) (hg : setupGates XI = true) (Hf : HFn) :
    (mkVKData' XI Hf).vk = vkSpec XI Hf := by
  have h := hspec Hf
  rw [setup'_of_gates hg] at h
  exact Option.some.inj h

theorem vkSpec_cols (XI : ExecInst) (Hf : HFn) : (vkSpec XI Hf).cols = fixCols XI := rfl
theorem vkSpec_X (XI : ExecInst) (Hf : HFn) : (vkSpec XI Hf).X = eraseX XI := rfl

end NockvmE2E.Exec.V

#print axioms NockvmE2E.Exec.V.fixTrue_eq_fj
#print axioms NockvmE2E.Exec.V.colG_eval
#print axioms NockvmE2E.Exec.V.specWord_eval
#print axioms NockvmE2E.Exec.V.natDegree_fj_le_J8
#print axioms NockvmE2E.Exec.V.canon_of_gates
#print axioms NockvmE2E.Exec.V.mkVKData'_vk_eq_vkSpec
