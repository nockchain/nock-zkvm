/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AComputeAll.lean

-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeWalk
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAcc
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeInv
import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestT
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.HonestSatX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAll

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9)
open Nock.V1J9A.GenCompX9
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD (lnClosed cntClosed accClosed)
open Nock.NockVMROM.Thm54.VclL.HonestSatX9 (accW9)

/-- The step of `walkVals9`, restated. -/
def stepW (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (α γ : K3)
    (st : List (K3 × K3 × K3 × K3) × K3 × K3 × K3 × K3 × ℕ) (u : NTree LX9) :
    List (K3 × K3 × K3 × K3) × K3 × K3 × K3 × K3 × ℕ :=
  match st with
  | (out, lnP, cntP, accP, aSf, i) =>
    let fo := u.children.length
    let ln := if i = 0 then α else lnP * α
    let cnt := if i = 0 then α * CompX.powK α fo else cntP * CompX.powK α fo
    let cs := (u.children.zipIdx 1).foldl
      (fun s (ch : NTree LX9 × ℕ) => s + nodeV9E H pd idOf γ ch.1 * CompX.powK α ch.2 * aSf) 0
    let cur := nodeV9E H pd idOf γ u
    let acc := if i = 0 then α * cs else accP - cur * ln + α * cs
    (out ++ [(ln, cnt, acc, (cnt - ln)⁻¹)], ln, cnt, acc, aSf * CompX.powK α fo, i + 1)

theorem walkVals9_eq (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))
    (α γ : K3) :
    walkVals9 H pd idOf W α γ = (W.foldl (stepW H pd idOf α γ) ([], 0, 0, 0, 1, 0)).1 := rfl

theorem rlcL_succ_shift (g : KC) (vs : List KC) (n : ℕ) : rlcL g (n + 1) vs = g * rlcL g n vs := by
  induction vs generalizing n with
  | nil => simp [rlcL]
  | cons v vs ih => simp only [rlcL]; rw [ih]; ring

theorem toK_k3 (x : ZMod P) : K3.toK (k3 x) = algebraMap (ZMod P) KC x := by
  unfold k3; rw [toK_g3, Gold.toZ_ofZ]

theorem nodeV9E_foldl (γ : K3) (vs : List (ZMod P)) (s p : K3) :
    K3.toK ((vs.map k3).foldl (fun (st : K3 × K3) v => (st.1 + st.2 * v, st.2 * γ)) (s, p)).1 =
      K3.toK s + K3.toK p * rlcL (K3.toK γ) 0 (vs.map (algebraMap (ZMod P) KC)) := by
  induction vs generalizing s p with
  | nil => simp [rlcL]
  | cons v vs ih =>
    simp only [List.map_cons, List.foldl_cons, rlcL]
    rw [ih, K3.toK_add, K3.toK_mul, K3.toK_mul, toK_k3, rlcL_succ_shift]
    ring

/-- **`hnode` discharged**: the executable node value is the honest `nodeV9` (in `KC`). -/
theorem nodeV9E_eq (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (γ : K3)
    (u : NTree LX9) :
    K3.toK (nodeV9E H pd idOf γ u) =
      Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReadsAt.nodeV9 (F := ZMod P) (K := KC) H pd idOf (K3.toK γ) u := by
  unfold nodeV9E Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReadsAt.nodeV9
  rw [nodeV9E_foldl, Nock.V1J9A.FillX9.nodeLab9E_eq]
  simp [K3.toK_zero, K3.toK_one]

/-- fanout column of the BFS list (0-indexed). -/
def foW (W : List (NTree LX9)) (i : ℕ) : ℕ := ((W[i]?).map fun t => t.children.length).getD 0

theorem foW_eq (W : List (NTree LX9)) (i : ℕ) : foW W i = Walk.foCol W (i + 1) := by
  simp [foW, Walk.foCol]

theorem powK_succ' (α : K3) (n : ℕ) : CompX.powK α (n + 1) = CompX.powK α n * α := rfl

theorem powK_add' (α : K3) (m n : ℕ) : CompX.powK α (m + n) = CompX.powK α m * CompX.powK α n :=
  K3.toK_injective (by rw [K3.toK_mul, CompX.toK_powK, CompX.toK_powK, CompX.toK_powK, pow_add])

theorem k3_one_mul (a : K3) : (1 : K3) * a = a :=
  K3.toK_injective (by rw [K3.toK_mul, K3.toK_one, one_mul])

theorem k3_mul_assoc (a b c : K3) : a * b * c = a * (b * c) :=
  K3.toK_injective (by simp only [K3.toK_mul]; ring)

theorem powK_zero' (α : K3) : CompX.powK α 0 = 1 := rfl

/-- **Invariant of the foldl** at the prefix of length `k`. -/
theorem foldl_inv (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))
    (α γ : K3) : ∀ k, k ≤ W.length →
    ∃ out lnP cntP accP,
      (W.take k).foldl (stepW H pd idOf α γ) ([], 0, 0, 0, 1, 0) =
        (out, lnP, cntP, accP, CompX.powK α (∑ i ∈ Finset.range k, foW W i), k) ∧
      out.length = k ∧
      (∀ j < k, (out.getD j (0, 0, 0, 0)).1 = CompX.powK α (j + 1) ∧
        (out.getD j (0, 0, 0, 0)).2.1 = α * CompX.powK α (∑ i ∈ Finset.range (j + 1), foW W i)) ∧
      (0 < k → lnP = CompX.powK α k ∧ cntP = α * CompX.powK α (∑ i ∈ Finset.range k, foW W i)) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨[], 0, 0, 0, by simp [CompX.powK], rfl, by simp, by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨out, lnP, cntP, accP, hst, hlen, hj, hl⟩ := ih (by omega)
    have hk' : k < W.length := by omega
    have htake : W.take (k + 1) = W.take k ++ [W[k]] := by
      rw [List.take_add_one]; simp [List.getElem?_eq_getElem hk']
    have hfo : foW W k = W[k].children.length := by simp [foW, List.getElem?_eq_getElem hk']
    have hsum : CompX.powK α (∑ i ∈ Finset.range (k + 1), foW W i) =
        CompX.powK α (∑ i ∈ Finset.range k, foW W i) * CompX.powK α W[k].children.length := by
      rw [Finset.sum_range_succ, hfo, powK_add']
    rw [htake, List.foldl_append, hst]
    simp only [List.foldl_cons, List.foldl_nil, stepW]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left 4
    · rw [hsum]
    · simp [hlen]
    · intro j hjk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with hjk | hjk
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact hj j hjk
      · subst hjk
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simp only [hlen, Nat.sub_self, List.getD_cons_zero]
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · subst h0
          simp only [if_true, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
          refine ⟨?_, ?_⟩
          · rw [powK_succ', powK_zero']; exact (k3_one_mul α).symm
          · rw [hfo]
        · simp only [if_neg (show j ≠ 0 by omega)]
          obtain ⟨h1, h2⟩ := hl h0
          refine ⟨?_, ?_⟩
          · rw [h1, powK_succ']
          · rw [h2, hsum, k3_mul_assoc]
    · intro _
      by_cases h0 : k = 0
      · subst h0
        simp only [if_true, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
        refine ⟨?_, ?_⟩
        · rw [powK_succ', powK_zero']; exact (k3_one_mul α).symm
        · rw [hfo]
      · simp only [if_neg h0]
        obtain ⟨h1, h2⟩ := hl (by omega)
        refine ⟨?_, ?_⟩
        · rw [h1, powK_succ']
        · rw [h2, hsum, k3_mul_assoc]

/-- **ln / cnt columns of `walkVals9` are the honest closed forms** (in `KC`, rows `j < |W|`). -/
theorem walkVals9_ln_cnt (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (α γ : K3) {j : ℕ} (hj : j < W.length) :
    K3.toK ((walkVals9 H pd idOf W α γ).getD j (0, 0, 0, 0)).1 = lnClosed (K3.toK α) (j + 1) ∧
    K3.toK ((walkVals9 H pd idOf W α γ).getD j (0, 0, 0, 0)).2.1 =
      cntClosed (Walk.foCol W) (K3.toK α) (K3.toK α) (j + 1) := by
  obtain ⟨out, lnP, cntP, accP, hst, hlen, hjj, _⟩ := foldl_inv H pd idOf W α γ W.length le_rfl
  rw [List.take_length] at hst
  rw [walkVals9_eq, hst]
  obtain ⟨h1, h2⟩ := hjj j hj
  simp only
  rw [h1, h2]
  have hS : ∑ i ∈ Finset.range (j + 1), foW W i = Walk.Sf (Walk.foCol W) (j + 1) := by
    unfold Walk.Sf
    rw [Walk.sum_Icc_one_eq_range]
    exact Finset.sum_congr rfl (fun i _ => foW_eq W i)
  constructor
  · rw [CompX.toK_powK]; rfl
  · rw [K3.toK_mul, CompX.toK_powK, hS]; rfl

/-! ## The accumulator column -/

theorem cs_sum (nodeV : NTree LX9 → KC) (F : NTree LX9 → K3) (hF : ∀ u, K3.toK (F u) = nodeV u) (α a : K3) :
    ∀ (L : List (NTree LX9)) (s0 : K3) (n : ℕ),
      K3.toK ((L.zipIdx n).foldl (fun s (ch : NTree LX9 × ℕ) => s + F ch.1 * CompX.powK α ch.2 * a) s0) =
      K3.toK s0 + ∑ i ∈ Finset.range L.length,
        ((L[i]?).map nodeV).getD 0 * K3.toK α ^ (n + i) * K3.toK a := by
  intro L
  induction L with
  | nil => intro s0 n; simp
  | cons x l ih =>
    intro s0 n
    rw [List.zipIdx_cons, List.foldl_cons, ih, K3.toK_add, K3.toK_mul, K3.toK_mul, CompX.toK_powK, hF,
      List.length_cons, Finset.sum_range_succ']
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]
    have h : ∀ i : ℕ, n + 1 + i = n + (i + 1) := fun i => by omega
    simp only [h]
    ring

theorem accW9_succ (nodeV : NTree LX9 → KC) (W : List (NTree LX9)) (α : KC) (k : ℕ) :
    accW9 nodeV W α (k + 1) = accW9 nodeV W α k - Walk.curCol nodeV W (k + 1) * α ^ (k + 1) +
      α * Walk.childSum (Walk.chldCol nodeV W) (Walk.foCol W) α (k + 1) := by
  unfold accW9 accClosed
  rw [Walk.nodeListP_succ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Finset.sum_Icc_succ_top (by omega)]
  ring

theorem accW9_zero (nodeV : NTree LX9 → KC) (W : List (NTree LX9)) (α : KC) :
    accW9 nodeV W α 0 = Walk.curCol nodeV W 1 * α := by
  unfold accW9 accClosed
  simp [Walk.nodeListP_eval]

theorem acc_step (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))
    (α γ : K3) (nodeV : NTree LX9 → KC) (hnode : ∀ u, K3.toK (nodeV9E H pd idOf γ u) = nodeV u)
    {k : ℕ} (hk : k < W.length) (lnP accP aSf : K3)
    (hl : 0 < k → K3.toK lnP = K3.toK α ^ k)
    (ha : 0 < k → K3.toK accP = accW9 nodeV W (K3.toK α) k)
    (hs : K3.toK aSf = K3.toK α ^ Walk.Sf (Walk.foCol W) k) :
    K3.toK (if k = 0 then
        α * (W[k].children.zipIdx 1).foldl
          (fun s (ch : NTree LX9 × ℕ) => s + nodeV9E H pd idOf γ ch.1 * CompX.powK α ch.2 * aSf) 0
      else accP - nodeV9E H pd idOf γ W[k] * (if k = 0 then α else lnP * α) + α * (W[k].children.zipIdx 1).foldl
          (fun s (ch : NTree LX9 × ℕ) => s + nodeV9E H pd idOf γ ch.1 * CompX.powK α ch.2 * aSf) 0) =
      accW9 nodeV W (K3.toK α) (k + 1) := by
  have hcur : Walk.curCol nodeV W (k + 1) = nodeV W[k] := by
    simp [Walk.curCol, List.getElem?_eq_getElem hk]
  have hfo : Walk.foCol W (k + 1) = W[k].children.length := by
    simp [Walk.foCol, List.getElem?_eq_getElem hk]
  have hcs := cs_sum nodeV (nodeV9E H pd idOf γ) hnode α aSf W[k].children 0 1
  have hcsum : Walk.childSum (Walk.chldCol nodeV W) (Walk.foCol W) (K3.toK α) (k + 1) =
      ∑ i ∈ Finset.range W[k].children.length,
        ((W[k].children[i]?).map nodeV).getD 0 * K3.toK α ^ (1 + i) * K3.toK aSf := by
    unfold Walk.childSum
    rw [hfo, Walk.sum_Icc_one_eq_range, hs]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Walk.chldCol nodeV W (k + 1) (i + 1) = ((W[k].children[i]?).map nodeV).getD 0 := by
      simp [Walk.chldCol, List.getElem?_eq_getElem hk]
    simp only [Nat.add_sub_cancel]
    rw [this, pow_add, pow_add]
    ring
  rw [accW9_succ, hcur]
  by_cases h0 : k = 0
  · subst h0
    simp only [if_true]
    rw [accW9_zero, K3.toK_mul, hcs, K3.toK_zero, zero_add, ← hcsum]
    have h1 : Walk.curCol nodeV W 1 = nodeV W[0] := hcur
    rw [h1]
    simp only [zero_add, pow_one]
    ring
  · simp only [if_neg h0]
    rw [K3.toK_add, K3.toK_sub, K3.toK_mul, K3.toK_mul, K3.toK_mul, hcs, K3.toK_zero, zero_add, ← hcsum,
      ha (by omega), hnode, hl (by omega)]
    ring

theorem sf_eq_range (W : List (NTree LX9)) (k : ℕ) :
    Walk.Sf (Walk.foCol W) k = ∑ i ∈ Finset.range k, foW W i := by
  unfold Walk.Sf
  rw [Walk.sum_Icc_one_eq_range]
  exact Finset.sum_congr rfl (fun i _ => (foW_eq W i).symm)

/-- **Invariant of the foldl, accumulator column.** -/
theorem foldl_acc (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))
    (α γ : K3) (nodeV : NTree LX9 → KC) (hnode : ∀ u, K3.toK (nodeV9E H pd idOf γ u) = nodeV u) :
    ∀ k, k ≤ W.length →
    ∃ out lnP cntP accP,
      (W.take k).foldl (stepW H pd idOf α γ) ([], 0, 0, 0, 1, 0) =
        (out, lnP, cntP, accP, CompX.powK α (∑ i ∈ Finset.range k, foW W i), k) ∧
      out.length = k ∧
      (∀ j < k, K3.toK (out.getD j (0, 0, 0, 0)).2.2.1 = accW9 nodeV W (K3.toK α) (j + 1)) ∧
      (∀ j < k, (out.getD j (0, 0, 0, 0)).2.2.2 =
        ((out.getD j (0, 0, 0, 0)).2.1 - (out.getD j (0, 0, 0, 0)).1)⁻¹) ∧
      (0 < k → K3.toK lnP = K3.toK α ^ k ∧ K3.toK accP = accW9 nodeV W (K3.toK α) k) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨[], 0, 0, 0, by simp [CompX.powK], rfl, by simp, by simp, by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨out, lnP, cntP, accP, hst, hlen, hj, hi, hl⟩ := ih (by omega)
    have hk' : k < W.length := by omega
    have htake : W.take (k + 1) = W.take k ++ [W[k]] := by
      rw [List.take_add_one]; simp [List.getElem?_eq_getElem hk']
    have hfo : foW W k = W[k].children.length := by simp [foW, List.getElem?_eq_getElem hk']
    have hsum : CompX.powK α (∑ i ∈ Finset.range (k + 1), foW W i) =
        CompX.powK α (∑ i ∈ Finset.range k, foW W i) * CompX.powK α W[k].children.length := by
      rw [Finset.sum_range_succ, hfo, powK_add']
    have hstep := acc_step H pd idOf W α γ nodeV hnode hk' lnP accP
      (CompX.powK α (∑ i ∈ Finset.range k, foW W i))
      (fun h => (hl h).1) (fun h => (hl h).2)
      (by rw [CompX.toK_powK, sf_eq_range])
    rw [htake, List.foldl_append, hst]
    simp only [List.foldl_cons, List.foldl_nil, stepW]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left 4
    · rw [hsum]
    · simp [hlen]
    · intro j hjk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with hjk | hjk
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact hj j hjk
      · subst hjk
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simp only [hlen, Nat.sub_self, List.getD_cons_zero]
        exact hstep
    · intro j hjk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with hjk | hjk
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact hi j hjk
      · subst hjk
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simp only [hlen, Nat.sub_self, List.getD_cons_zero]
    · intro _
      refine ⟨?_, hstep⟩
      by_cases h0 : k = 0
      · subst h0
        simp only [if_true, zero_add, pow_one]
      · simp only [if_neg h0]
        rw [K3.toK_mul, (hl (by omega)).1, pow_succ]

/-- **acc column of `walkVals9` is the honest `accW9`** (rows `j < |W|`), given the node-value bridge. -/
theorem walkVals9_acc (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (α γ : K3) (nodeV : NTree LX9 → KC)
    (hnode : ∀ u, K3.toK (nodeV9E H pd idOf γ u) = nodeV u) {j : ℕ} (hj : j < W.length) :
    K3.toK ((walkVals9 H pd idOf W α γ).getD j (0, 0, 0, 0)).2.2.1 = accW9 nodeV W (K3.toK α) (j + 1) := by
  obtain ⟨out, lnP, cntP, accP, hst, hlen, hjj, _, _⟩ := foldl_acc H pd idOf W α γ nodeV hnode W.length le_rfl
  rw [List.take_length] at hst
  rw [walkVals9_eq, hst]
  exact hjj j hj

/-- **inverse column of `walkVals9`** (`hinv` of `compTable9_eq_trX9_walk`). -/
theorem walkVals9_inv (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (α γ : K3) (nodeV : NTree LX9 → KC)
    (hnode : ∀ u, K3.toK (nodeV9E H pd idOf γ u) = nodeV u) {j : ℕ} (hj : j < W.length) :
    ((walkVals9 H pd idOf W α γ).getD j (0, 0, 0, 0)).2.2.2 =
      (((walkVals9 H pd idOf W α γ).getD j (0, 0, 0, 0)).2.1 -
        ((walkVals9 H pd idOf W α γ).getD j (0, 0, 0, 0)).1)⁻¹ := by
  obtain ⟨out, lnP, cntP, accP, hst, hlen, _, hii, _⟩ := foldl_acc H pd idOf W α γ nodeV hnode W.length le_rfl
  rw [List.take_length] at hst
  rw [walkVals9_eq, hst]
  exact hii j hj

/-! ## Column coverage and the unconditional link -/

/-- **Coverage**: `invPermX9` maps `d < 137` into `[0, 137)`, which splits into base (`< 69` or `≥ 123`),
`69..92`, `93..110`, `111..122`: no range is missing. -/
theorem invPermX9_lt (d : ℕ) (hd : d < 137) : ComplJ9ACompRow.invPermX9 d < 137 := by
  unfold ComplJ9ACompRow.invPermX9; split_ifs <;> omega

theorem coverage9 (c : ℕ) (hc : c < 137) :
    (c < 69 ∨ 123 ≤ c) ∨ (69 ≤ c ∧ c < 93) ∨ (93 ≤ c ∧ c < 111) ∨ (111 ≤ c ∧ c < 123) := by omega

/-- **Compute table = `trX9`, unconditional** at the honest closed-form walk functions (`lnClosed`, `cntClosed`,
`accW9`), given the node-value bridge `hnode` (`nodeV9E` is `nodeV` in `KC`). -/
theorem compTable9_eq_trX9_all
    [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
    (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (pub : ℕ → ZMod P) (χe : CoinsE) (nodeV : NTree LX9 → KC)
    (hnode : ∀ u, K3.toK (nodeV9E H pd idOf (χe ⟨14, by decide⟩) u) = nodeV u)
    {j : ℕ} (hj : j < W.length) {d : ℕ} (hd : d < 137) :
    ((compTable9 H pd idOf W pub χe).getD j #[]).getD d 0 =
      Nock.NockVMROM.Thm54.VclL.HonestTraceX9.trX9 powerBasis3 deltaF H pd idOf W (Example.chalE χe) pub
        (lnClosed (K3.toK (χe ⟨13, by decide⟩)))
        (cntClosed (Walk.foCol W) (K3.toK (χe ⟨13, by decide⟩)) (K3.toK (χe ⟨13, by decide⟩)))
        (accW9 nodeV W (K3.toK (χe ⟨13, by decide⟩))) j (ComplJ9ACompRow.invPermX9 d) := by
  have hc := invPermX9_lt d hd
  rcases coverage9 _ hc with h | h | h | h
  · exact GenPortJ9ACompute.compTable9_eq_trX9_base powerBasis3 deltaF H pd idOf W pub χe (Example.chalE χe) pub
      _ _ _ hj hd h
  · exact GenPortJ9ACompute.compTable9_eq_trX9_inv H pd idOf W pub χe _ _ _ hj hd h
  · exact GenPortJ9AComputeAcc.compTable9_eq_trX9_acc_conc H pd idOf W pub χe _ _ _ hj hd h
  · refine GenPortJ9AComputeWalk.compTable9_eq_trX9_walk H pd idOf W pub χe (Example.chalE χe) pub _ _ _
      ?_ ?_ ?_ ?_ hj hd h
    · intro j' hj'
      exact (walkVals9_ln_cnt H pd idOf W _ _ hj').1.symm
    · intro j' hj'
      exact (walkVals9_ln_cnt H pd idOf W _ _ hj').2.symm
    · intro j' hj'
      exact (walkVals9_acc H pd idOf W _ _ nodeV hnode hj').symm
    · intro j' hj'
      exact walkVals9_inv H pd idOf W _ _ nodeV hnode hj'

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAcc
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (slotsX9)
/-- **Totals, coordinatewise**: coordinate `i < 18` of the `prefixSums` total of `termRow9` is the `cNA`
coordinate `i % 3` of the honest accumulator `accV9 … (i / 3) |W|`. -/
theorem totals9_getD (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (pub : ℕ → ZMod P) (χe : CoinsE) {i : ℕ} (hi : i < 18) :
    (totals9 H pd idOf W pub χe).getD i 0 =
      Nock.NockVMROM.Thm54.VclL.HonestTraceX.cNA powerBasis3
        (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.accV9 powerBasis3 deltaF H pd idOf W (Example.chalE χe) pub
          (i / 3) W.length) (i % 3) := by
  unfold totals9
  rw [prefixSums_total_getD _ hi]
  simp only [List.length_map, List.length_range]
  simp only [Nock.NockVMROM.Thm54.VclL.HonestTraceX9.accV9]
  rw [cNA_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' : r < W.length := Finset.mem_range.1 hr
  have hrow : (((List.range W.length).map fun j =>
      termRow9 (envX9 H pd idOf W pub χe j) (invsOf9 (envX9 H pd idOf W pub χe j))).getD r #[]) =
      termRow9 (envX9 H pd idOf W pub χe r) (invsOf9 (envX9 H pd idOf W pub χe r)) := by
    simp [List.getD_eq_getElem?_getD, hr']
  rw [hrow]
  have hs : i < 18 := hi
  have ha : i / 3 < 6 := by omega
  have hent : (termRow9 (envX9 H pd idOf W pub χe r) (invsOf9 (envX9 H pd idOf W pub χe r))).getD i 0 =
      (((slotsX9 (F := ZMod P)).map fun S =>
          (S.actB (accSpecE (i / 3)).1).eval (envX9 H pd idOf W pub χe r)).zipIdx 0).foldl
        (fun s (x : ZMod P × ℕ) => s + x.1 * limbZ (if (accSpecE (i / 3)).2
          then ((invsOf9 (envX9 H pd idOf W pub χe r)).getD x.2 0).im
          else ((invsOf9 (envX9 H pd idOf W pub χe r)).getD x.2 0).re) (i % 3)) 0 := by
    simp only [termRow9, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hs, dite_true, Option.getD_some, actsOf9]
  rw [hent]
  have hspec : Nock.NockVMROM.Thm54.VclL.HonestTraceX.accSpec (i / 3) = accSpecE (i / 3) := by
    generalize i / 3 = a at ha
    interval_cases a <;> rfl
  rw [hspec]
  exact (cNA_termVal powerBasis3 _ _ _ _ _ (hAct_conc H pd idOf W pub χe r _)
    (fun s hs k hk => hInv_conc H pd idOf W pub χe r hs hk) (Nat.mod_lt _ (by norm_num))).symm

/-- The final publics of `compGenX9` (pass 1 at `ρ = 0`, then `ρ`, `ρS` from the totals). -/
def pubFinal9 (c : P8PublicClaim) (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (χe : CoinsE) : ℕ → ZMod P :=
  let m := mOf c H
  let pub0 := Nock.V1J9.Check9.pubVJ9E c m (fun _ => 0) 0 χe
  let r := rhoOfTot (totals9 H pd idOf W pub0 χe)
  Nock.V1J9.Check9.pubVJ9E c m r.1 r.2 χe

theorem compGenX9_rows (c : P8PublicClaim) (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
    (idOf : ℕ → ℕ) (W : List (NTree LX9)) (χe : CoinsE) :
    (compGenX9 c H pd idOf W χe).rows = compTable9 H pd idOf W (pubFinal9 c H pd idOf W χe) χe := rfl

/-- **`compGenX9_eq`**: every entry of the generator's output table is the proofs' honest trace `trX9`. -/
theorem compGenX9_eq
    [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
    (c : P8PublicClaim) (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (χe : CoinsE) (nodeV : NTree LX9 → KC)
    (hnode : ∀ u, K3.toK (nodeV9E H pd idOf (χe ⟨14, by decide⟩) u) = nodeV u)
    {j : ℕ} (hj : j < W.length) {d : ℕ} (hd : d < 137) :
    (((compGenX9 c H pd idOf W χe).rows).getD j #[]).getD d 0 =
      Nock.NockVMROM.Thm54.VclL.HonestTraceX9.trX9 powerBasis3 deltaF H pd idOf W (Example.chalE χe)
        (pubFinal9 c H pd idOf W χe)
        (lnClosed (K3.toK (χe ⟨13, by decide⟩)))
        (cntClosed (Walk.foCol W) (K3.toK (χe ⟨13, by decide⟩)) (K3.toK (χe ⟨13, by decide⟩)))
        (accW9 nodeV W (K3.toK (χe ⟨13, by decide⟩))) j (ComplJ9ACompRow.invPermX9 d) := by
  rw [compGenX9_rows]
  exact compTable9_eq_trX9_all H pd idOf W _ χe nodeV hnode hj hd

/-- **Totals as `K3`**: the `K3` read at column `3*m` (`m < 6`) of the totals has semantic value `accV9 … m |W|`. -/
theorem totals9_readK (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (pub : ℕ → ZMod P) (χe : CoinsE) {m : ℕ} (hm : m < 6) :
    K3.toK (Nock.V1J8.CompX.readK (fun c => (totals9 H pd idOf W pub χe).getD c 0) (3 * m)) =
      Nock.NockVMROM.Thm54.VclL.HonestTraceX9.accV9 powerBasis3 deltaF H pd idOf W (Example.chalE χe) pub
        m W.length := by
  rw [← Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ACompute.limbVal_readK]
  refine Nock.NockVMROM.Thm54.VclL.HonestTraceX.limbVal_of_cNA powerBasis3 _ _ _ fun k => ?_
  have hk := k.isLt
  rw [totals9_getD H pd idOf W pub χe (by omega)]
  have e1 : (3 * m + (k : ℕ)) / 3 = m := by omega
  have e2 : (3 * m + (k : ℕ)) % 3 = k := by omega
  rw [e1, e2]

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAll

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAll.walkVals9_ln_cnt
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAll.walkVals9_acc
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAll.walkVals9_inv
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAll.compTable9_eq_trX9_all
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAll.compGenX9_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAll.nodeV9E_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAll.totals9_getD
