/-
  NockvmE2E/Exec/MaskOkK.lean   (Prop side of `hcur1`; proof-only)

  Soundness of `MaskOk.maskCol` (the exe's mask check): if the coefficient array `pre` (all coefficients canonical) passes `maskCol` at the nodes `g^i`,
  `i < n` (`g` = `X.hGen`, nodes injective), then, as polynomials over `ZMod p`, `polyOfArr pre` is
    pos 0:  `Nock.Framework.firstRowMask nodes`,
    pos 1:  `Nock.Framework.lastRowMask hn nodes`,
    pos ≥ 2: `rootRowMaskW nodes k` with `k` the returned number of leading ones (`k ≤ n`).
  Route: Horner (`peval`) = `Polynomial.eval` of `polyOfArr` (canonical coefficients); degree `< pre.size ≤ n`; Lagrange `eq_interpolate_of_eval_eq`.
-/
import Mathlib.LinearAlgebra.Lagrange
import Nock.Framework.EndpointMasks
import Nock.NockVMROM.Thm54.VclL.Chips.WalkChip
import NockvmE2E.Exec.MaskOk
import NockvmE2E.Exec.VLink

set_option autoImplicit false

namespace NockvmE2E.Exec.MaskOkK
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VF NockvmE2E.Exec.VL NockvmE2E.Exec.MaskOk Polynomial

/-- the polynomial over `ZMod p` with the given coefficient list -/
noncomputable def polyOfList : List G → (ZMod p)[X]
  | [] => 0
  | c :: cs => C (zv c) + X * polyOfList cs

noncomputable def polyOfArr (a : Array G) : (ZMod p)[X] := polyOfList a.toList

theorem degree_polyOfList (l : List G) : (polyOfList l).degree < (l.length : WithBot ℕ) := by
  induction l with
  | nil => simp [polyOfList]
  | cons c cs ih =>
    rw [degree_lt_iff_coeff_zero] at ih ⊢
    intro m hm
    simp only [polyOfList, coeff_add, coeff_C]
    rcases m with _ | m
    · simp at hm
    · have h := ih m (by simp at hm; exact_mod_cast (by omega))
      simp [coeff_X_mul, h]

theorem hor_zv (x : G) (hx : canon x) :
    ∀ l : List G, (∀ c ∈ l, canon c) → zv (hor x l) = (polyOfList l).eval (zv x) ∧ canon (hor x l)
  | [], _ => ⟨by simp only [hor, polyOfList, eval_zero]; exact zv_zero, Gold.zero_lt⟩
  | c :: cs, h => by
    have hc : canon c := h c (List.mem_cons_self ..)
    obtain ⟨ih1, ih2⟩ := hor_zv x hx cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
    have hm := mul_lt (hor x cs) x
    refine ⟨?_, add_lt _ _ hm hc⟩
    show zv (VF.add (VF.mul (hor x cs) x) c) = _
    rw [zv_add _ _ hm hc, zv_mul, ih1]
    simp only [polyOfList, eval_add, eval_mul, eval_C, eval_X]
    rw [add_comm, mul_comm]

theorem peval_hor (pa : Array G) (x : G) : peval pa x = hor x pa.toList := rfl

theorem peval_zv (pa : Array G) (x : G) (hx : canon x) (hp : ∀ c ∈ pa.toList, canon c) :
    zv (peval pa x) = (polyOfArr pa).eval (zv x) := by
  rw [peval_hor]; exact (hor_zv x hx pa.toList hp).1

theorem evalNodesAux_spec (p : Array G) (g : G) (hg : canon g) (hp : ∀ c ∈ p.toList, canon c) :
    ∀ (k : Nat) (x : G) (acc : Array G), canon x →
      (evalNodesAux p g k x acc).toList.map zv =
        acc.toList.map zv ++ (List.range k).map (fun j => (polyOfArr p).eval (zv x * zv g ^ j))
  | 0, x, acc, _ => by simp [evalNodesAux]
  | k + 1, x, acc, hx => by
    have ih := evalNodesAux_spec p g hg hp k (VF.mul x g) (acc.push (peval p x)) (mul_lt x g)
    simp only [evalNodesAux]
    rw [ih, Array.toList_push, List.map_append, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.append_assoc, List.map_map]
    rw [peval_zv p x hx hp]
    have e : ∀ j : ℕ, (polyOfArr p).eval (zv (VF.mul x g) * zv g ^ j) = (polyOfArr p).eval (zv x * zv g ^ (j + 1)) := by
      intro j; rw [zv_mul]; ring_nf
    simp [Function.comp, e]

theorem evalNodes_spec (p : Array G) (g : G) (hg : canon g) (hp : ∀ c ∈ p.toList, canon c) (n : Nat) :
    (evalNodes p g n).toList.map zv = (List.range n).map (fun j => (polyOfArr p).eval (zv g ^ j)) := by
  have := evalNodesAux_spec p g hg hp n 1 (Array.mkEmpty n) (by simpa [canon] using Gold.one_lt)
  simpa [evalNodes, zv_one] using this

theorem evalNodes_size (pa : Array G) (g : G) (hg : canon g) (hp : ∀ c ∈ pa.toList, canon c) (n : Nat) :
    (evalNodes pa g n).size = n := by
  have h := congrArg List.length (evalNodes_spec pa g hg hp n)
  simpa using h

theorem eval_of_pat (pa : Array G) (g : G) (hg : canon g) (hp : ∀ c ∈ pa.toList, canon c) (n : Nat) (f : ℕ → G)
    (h : evalNodes pa g n = (Array.range n).map f) :
    ∀ j < n, (polyOfArr pa).eval (zv g ^ j) = zv (f j) := by
  have h1 := evalNodes_spec pa g hg hp n
  rw [h] at h1
  simp only [Array.toList_map, Array.toList_range, List.map_map] at h1
  intro j hj
  exact ((List.map_inj_left.mp h1) j (List.mem_range.mpr hj)).symm

/-- the core: a polynomial of degree `< n` whose values at the nodes are `r` is the interpolant -/
theorem eq_interp {n : Nat} (nodes : Fin n → ZMod p) (hinj : Function.Injective nodes) (P : (ZMod p)[X])
    (hdeg : P.degree < (n : WithBot ℕ)) (r : Fin n → ZMod p) (hv : ∀ i : Fin n, P.eval (nodes i) = r i) :
    P = Lagrange.interpolate Finset.univ nodes r := by
  apply Lagrange.eq_interpolate_of_eval_eq _ hinj.injOn (by simpa using hdeg)
  intro i _; exact hv i

theorem interp_of_pat (X : ExecInst) (n : Nat) (hg : canon X.hGen)
    (hinj : Function.Injective (fun i : Fin n => zv X.hGen ^ (i : ℕ)))
    (pre : Array G) (hp : ∀ c ∈ pre.toList, canon c) (hs : ¬ pre.size > n) (f : ℕ → G)
    (h : evalNodes pre X.hGen n = (Array.range n).map f) :
    polyOfArr pre = Lagrange.interpolate Finset.univ (fun i : Fin n => zv X.hGen ^ (i : ℕ)) (fun i => zv (f i)) := by
  have hdeg : (polyOfArr pre).degree < (n : WithBot ℕ) := by
    have h0 := degree_polyOfList pre.toList
    have hle : ((pre.toList.length : ℕ) : WithBot ℕ) ≤ (n : WithBot ℕ) := by
      exact_mod_cast (by simpa using not_lt.mp hs)
    exact lt_of_lt_of_le h0 hle
  exact eq_interp _ hinj _ hdeg _ (fun i => eval_of_pat pre X.hGen hg hp n f h i i.2)

theorem maskCol_sound (X : ExecInst) (n pos : Nat) (hn : 0 < n) (hg : canon X.hGen)
    (hinj : Function.Injective (fun i : Fin n => zv X.hGen ^ (i : ℕ)))
    (pre : Array G) (hp : ∀ c ∈ pre.toList, canon c) (k : Nat) (h : maskCol X n pos pre = some k) :
    (pos = 0 → polyOfArr pre = Nock.Framework.firstRowMask (fun i : Fin n => zv X.hGen ^ (i : ℕ))) ∧
    (pos = 1 → polyOfArr pre = Nock.Framework.lastRowMask hn (fun i : Fin n => zv X.hGen ^ (i : ℕ))) ∧
    (2 ≤ pos → k ≤ n ∧ polyOfArr pre = Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.rootRowMaskW
        (fun i : Fin n => zv X.hGen ^ (i : ℕ)) k) := by
  unfold maskCol at h
  by_cases hs : pre.size > n
  · simp [hs] at h
  simp only [hs, ite_false] at h
  have hsz := evalNodes_size pre X.hGen hg hp n
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => ?_⟩
  · subst h0
    simp only [beq_self_eq_true, ite_true] at h
    by_cases hv : evalNodes pre X.hGen n == rootPat n 1
    · have hv' : evalNodes pre X.hGen n = rootPat n 1 := beq_iff_eq.mp hv
      rw [interp_of_pat X n hg hinj pre hp hs _ hv']
      unfold Nock.Framework.firstRowMask
      congr 1; funext i
      by_cases hi : (i : ℕ) = 0 <;> simp [hi, zv_one, zv_zero]
    · simp [hv] at h
  · subst h1
    simp only [show (1 == 0) = false from rfl, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true] at h
    by_cases hv : evalNodes pre X.hGen n == lastPat n
    · have hv' : evalNodes pre X.hGen n = lastPat n := beq_iff_eq.mp hv
      rw [interp_of_pat X n hg hinj pre hp hs _ hv']
      unfold Nock.Framework.lastRowMask
      congr 1; funext i
      by_cases hi : (i : ℕ) + 1 = n
      · have : i = ⟨n - 1, by omega⟩ := Fin.ext (by simp; omega)
        rw [if_pos this]; simp [hi, zv_one]
      · have : i ≠ ⟨n - 1, by omega⟩ := fun e => hi (by rw [e]; simp; omega)
        rw [if_neg this]; simp [hi, zv_zero]
    · simp [hv] at h
  · have h0 : ¬ pos = 0 := by omega
    have h1 : ¬ pos = 1 := by omega
    simp only [beq_iff_eq, h0, h1, ite_false] at h
    unfold leadingOnes at h
    by_cases hv : evalNodes pre X.hGen n == rootPat (evalNodes pre X.hGen n).size
        ((evalNodes pre X.hGen n).toList.filter (· == 1)).length
    · simp only [hv, ite_true, Option.some.injEq] at h
      have hv' := beq_iff_eq.mp hv
      rw [hsz] at hv'
      subst h
      have hkn : ((evalNodes pre X.hGen n).toList.filter (· == 1)).length ≤ n := by
        have := List.length_filter_le (· == 1) (evalNodes pre X.hGen n).toList
        simpa [hsz] using this
      refine ⟨hkn, ?_⟩
      rw [interp_of_pat X n hg hinj pre hp hs _ hv']
      unfold Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.rootRowMaskW
      congr 1; funext i
      by_cases hi : (i : ℕ) < ((evalNodes pre X.hGen n).toList.filter (· == 1)).length <;> simp [hi, zv_one, zv_zero]
    · simp [hv] at h

end NockvmE2E.Exec.MaskOkK

#print axioms NockvmE2E.Exec.MaskOkK.maskCol_sound
