/-
  NockvmE2E/Exec/HSpecAlg.lean   (HSpec, ; KERNEL-checked, Mathlib)

  Algebra of the setup code of `VKSetupR.lean`: the recursive NTT `nttR` evaluates the polynomial at the domain (`nttR_spec`), the coset LDE
  `cosetLdeR` is the Horner value at `7·g^i` (`cosetLdeR_eq`, exact `UInt64` equality), `prodLinR` is the linear-factor product
  (`prodLinR_spec`), `orbitPts_spec`, `hpd_of_tabsOk`, and `lde_word`: the committed word IS the spec word.
  No axiom, no `sorry`.
-/
import NockvmE2E.Exec.VKSetupR
import NockvmE2E.Exec.VKSpec
import NockvmE2E.Exec.J8Shape

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec.VF NockvmE2E.Exec.VL

/-! ### the NTT -/

theorem evensG_eq : ∀ a : List G, evensG a = NTT.evens a
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: t => by simp only [evensG, NTT.evens, evensG_eq t]

theorem oddsG_eq : ∀ a : List G, oddsG a = NTT.odds a
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: t => by simp only [oddsG, NTT.odds, oddsG_eq t]

theorem evens_mem {α : Type} : ∀ (a : List α) (x : α), x ∈ NTT.evens a → x ∈ a
  | [], x, h => by simp [NTT.evens] at h
  | [y], x, h => by simpa [NTT.evens] using h
  | y :: z :: t, x, h => by
    simp only [NTT.evens, List.mem_cons] at h
    rcases h with h | h
    · exact h ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (evens_mem t x h))

theorem odds_mem {α : Type} : ∀ (a : List α) (x : α), x ∈ NTT.odds a → x ∈ a
  | [], x, h => by simp [NTT.odds] at h
  | [y], x, h => by simp [NTT.odds] at h
  | y :: z :: t, x, h => by
    simp only [NTT.odds, List.mem_cons] at h
    rcases h with h | h
    · exact List.mem_cons_of_mem _ (h ▸ List.mem_cons_self)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (odds_mem t x h))

theorem getD_zipWithG (f : G → G → G) (e t : List G) (j : ℕ) (he : j < e.length) (ht : j < t.length) :
    (List.zipWith f e t).getD j 0 = f (e.getD j 0) (t.getD j 0) := by
  simp [List.getD_eq_getElem?_getD, he, ht]

theorem canon_of_getD (l : List G) (h : ∀ j < l.length, canon (l.getD j 0)) : ∀ x ∈ l, canon x := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have := h j hj
  simpa [List.getD_eq_getElem?_getD, hj] using this

/-- the butterfly, low half (`ZMod p` only) -/
theorem ntt_lo (k : ℕ) (W : ZMod NockvmE2E.Exec.p) (f : ℕ → ZMod NockvmE2E.Exec.p) (j : ℕ) :
    (∑ i ∈ Finset.range (2 ^ k), f (2 * i) * (W * W) ^ (i * j)) +
      W ^ j * ∑ i ∈ Finset.range (2 ^ k), f (2 * i + 1) * (W * W) ^ (i * j) =
    ∑ i ∈ Finset.range (2 ^ k), (f (2 * i) * W ^ (2 * i * j) + f (2 * i + 1) * W ^ ((2 * i + 1) * j)) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- the butterfly, high half -/
theorem ntt_hi (k : ℕ) (W : ZMod NockvmE2E.Exec.p) (hw : W ^ 2 ^ k = -1) (f : ℕ → ZMod NockvmE2E.Exec.p) (j : ℕ) :
    (∑ i ∈ Finset.range (2 ^ k), f (2 * i) * (W * W) ^ (i * j)) -
      W ^ j * ∑ i ∈ Finset.range (2 ^ k), f (2 * i + 1) * (W * W) ^ (i * j) =
    ∑ i ∈ Finset.range (2 ^ k), (f (2 * i) * W ^ (2 * i * (2 ^ k + j)) + f (2 * i + 1) * W ^ ((2 * i + 1) * (2 ^ k + j))) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : W ^ (2 * i * (2 ^ k + j)) = W ^ (2 * i * j) := by
    have : W ^ (2 * i * (2 ^ k + j)) = (W ^ 2 ^ k) ^ (2 * i) * W ^ (2 * i * j) := by ring
    rw [this, hw, Even.neg_one_pow ⟨i, by ring⟩, one_mul]
  have e2 : W ^ ((2 * i + 1) * (2 ^ k + j)) = -W ^ ((2 * i + 1) * j) := by
    have : W ^ ((2 * i + 1) * (2 ^ k + j)) = (W ^ 2 ^ k) ^ (2 * i + 1) * W ^ ((2 * i + 1) * j) := by ring
    rw [this, hw, Odd.neg_one_pow ⟨i, rfl⟩, neg_one_mul]
  rw [e1, e2]
  ring

/-- the conclusion of `nttR_spec` -/
def NttP (k : ℕ) (w : G) (a : List G) : Prop :=
  (nttR k w a).length = 2 ^ k ∧ (∀ x ∈ nttR k w a, canon x) ∧
    ∀ j < 2 ^ k, zv ((nttR k w a).getD j 0) = ∑ i ∈ Finset.range (2 ^ k), zv (a.getD i 0) * zv w ^ (i * j)

theorem nttR_base (w : G) (a : List G) (h : a.length = 2 ^ 0) (hc : ∀ x ∈ a, canon x) : NttP 0 w a := by
  have h1 : a.length = 1 := by simpa using h
  obtain ⟨x, rfl⟩ : ∃ x, a = [x] := by
    match a, h1 with
    | [x], _ => exact ⟨x, rfl⟩
  refine ⟨by simp [nttR], by simpa [nttR] using hc, ?_⟩
  intro j hj
  have : j = 0 := by simpa using hj
  subst this
  simp [nttR]

theorem nttR_succ (k : ℕ) (w : G) (a : List G) : nttR (k + 1) w a =
    List.zipWith VF.add (nttR k (VF.mul w w) (evensG a))
      (List.zipWith VF.mul ((List.range (2 ^ k)).map (VF.pow w ·)) (nttR k (VF.mul w w) (oddsG a))) ++
    List.zipWith VF.sub (nttR k (VF.mul w w) (evensG a))
      (List.zipWith VF.mul ((List.range (2 ^ k)).map (VF.pow w ·)) (nttR k (VF.mul w w) (oddsG a))) := by
  rw [nttR]

/-! the butterfly on generic lists -/

theorem bf_len (N : ℕ) (e t : List G) (le : e.length = N) (lt : t.length = N) :
    (List.zipWith VF.add e t ++ List.zipWith VF.sub e t).length = 2 * N := by
  simp [le, lt]; omega

theorem bf_lo (N : ℕ) (e t : List G) (le : e.length = N) (lt : t.length = N)
    (ecan : ∀ j < N, canon (e.getD j 0)) (tcan : ∀ j < N, canon (t.getD j 0)) (j : ℕ) (hj : j < N) :
    canon ((List.zipWith VF.add e t ++ List.zipWith VF.sub e t).getD j 0) ∧
    zv ((List.zipWith VF.add e t ++ List.zipWith VF.sub e t).getD j 0) = zv (e.getD j 0) + zv (t.getD j 0) := by
  have h1 : (List.zipWith VF.add e t).length = N := by simp [le, lt]
  rw [List.getD_append _ _ _ _ (by rw [h1]; exact hj), getD_zipWithG _ _ _ _ (by omega) (by omega)]
  exact ⟨add_lt _ _ (ecan j hj) (tcan j hj), zv_add _ _ (ecan j hj) (tcan j hj)⟩

theorem bf_hi (N : ℕ) (e t : List G) (le : e.length = N) (lt : t.length = N)
    (ecan : ∀ j < N, canon (e.getD j 0)) (tcan : ∀ j < N, canon (t.getD j 0)) (j : ℕ) (hj : j < N) :
    canon ((List.zipWith VF.add e t ++ List.zipWith VF.sub e t).getD (N + j) 0) ∧
    zv ((List.zipWith VF.add e t ++ List.zipWith VF.sub e t).getD (N + j) 0) = zv (e.getD j 0) - zv (t.getD j 0) := by
  have h1 : (List.zipWith VF.add e t).length = N := by simp [le, lt]
  rw [List.getD_append_right _ _ _ _ (by rw [h1]; omega), h1, Nat.add_sub_cancel_left,
    getD_zipWithG _ _ _ _ (by omega) (by omega)]
  exact ⟨sub_lt _ _ (ecan j hj) (tcan j hj), zv_sub _ _ (ecan j hj) (tcan j hj)⟩

theorem bf_canon (N : ℕ) (e t : List G) (le : e.length = N) (lt : t.length = N)
    (ecan : ∀ j < N, canon (e.getD j 0)) (tcan : ∀ j < N, canon (t.getD j 0)) :
    ∀ x ∈ List.zipWith VF.add e t ++ List.zipWith VF.sub e t, canon x := by
  refine canon_of_getD _ fun j hj => ?_
  rw [bf_len N e t le lt] at hj
  rcases lt_or_ge j N with hjk | hjk
  · exact (bf_lo N e t le lt ecan tcan j hjk).1
  · obtain ⟨j', rfl⟩ : ∃ j', j = N + j' := ⟨j - N, by omega⟩
    exact (bf_hi N e t le lt ecan tcan j' (by omega)).1

theorem tw_len (N : ℕ) (w : G) (o : List G) (lo : o.length = N) :
    (List.zipWith VF.mul ((List.range N).map (VF.pow w ·)) o).length = N := by
  rw [List.length_zipWith, List.length_map, List.length_range, lo, Nat.min_self]

theorem tw_get (N : ℕ) (w : G) (o : List G) (lo : o.length = N) (j : ℕ) (hj : j < N) :
    (List.zipWith VF.mul ((List.range N).map (VF.pow w ·)) o).getD j 0 = VF.mul (VF.pow w j) (o.getD j 0) := by
  rw [getD_zipWithG _ _ _ _ (by rw [List.length_map, List.length_range]; exact hj) (by omega)]
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

theorem nttR_step (k : ℕ) (w : G) (a : List G) (h : a.length = 2 ^ (k + 1)) (hc : ∀ x ∈ a, canon x)
    (hw : zv w ^ 2 ^ k = -1) (IHe' : NttP k (VF.mul w w) (evensG a)) (IHo' : NttP k (VF.mul w w) (oddsG a)) :
    NttP (k + 1) w a := by
  have he : (evensG a).length = 2 ^ k := by rw [evensG_eq, NTT.length_evens, h, pow_succ]; omega
  have ho : (oddsG a).length = 2 ^ k := by rw [oddsG_eq, NTT.length_odds, h, pow_succ]; omega
  obtain ⟨le, ce, IHe⟩ := IHe'
  obtain ⟨lo, co, IHo⟩ := IHo'
  have tlen := tw_len (2 ^ k) w _ lo
  have tget := tw_get (2 ^ k) w _ lo
  have tcan : ∀ j' < 2 ^ k, canon ((List.zipWith VF.mul ((List.range (2 ^ k)).map (VF.pow w ·)) (nttR k (VF.mul w w) (oddsG a))).getD j' 0) := by
    intro j' hj'; rw [tget j' hj']; exact mul_lt _ _
  have ecan : ∀ j' < 2 ^ k, canon ((nttR k (VF.mul w w) (evensG a)).getD j' 0) := by
    intro j' hj'
    have := ce ((nttR k (VF.mul w w) (evensG a))[j']'(by omega)) (List.getElem_mem _)
    simpa [List.getD_eq_getElem?_getD, hj', le] using this
  have hE : ∀ j' < 2 ^ k, zv ((nttR k (VF.mul w w) (evensG a)).getD j' 0) =
      ∑ i ∈ Finset.range (2 ^ k), zv (a.getD (2 * i) 0) * (zv w * zv w) ^ (i * j') := by
    intro j' hj'; rw [IHe j' hj']
    exact Finset.sum_congr rfl fun i _ => by rw [evensG_eq, NTT.getD_evens, zv_mul]
  have hO : ∀ j' < 2 ^ k, zv ((nttR k (VF.mul w w) (oddsG a)).getD j' 0) =
      ∑ i ∈ Finset.range (2 ^ k), zv (a.getD (2 * i + 1) 0) * (zv w * zv w) ^ (i * j') := by
    intro j' hj'; rw [IHo j' hj']
    exact Finset.sum_congr rfl fun i _ => by rw [oddsG_eq, NTT.getD_odds, zv_mul]
  have hlen := bf_len (2 ^ k) _ _ le tlen
  have hcan := bf_canon (2 ^ k) _ _ le tlen ecan tcan
  have hlo := bf_lo (2 ^ k) _ _ le tlen ecan tcan
  have hhi := bf_hi (2 ^ k) _ _ le tlen ecan tcan
  rw [← nttR_succ] at hlen hcan hlo hhi
  unfold NttP
  refine ⟨by rw [hlen]; ring, hcan, ?_⟩
  intro j hj
  rw [show 2 ^ (k + 1) = 2 * 2 ^ k by ring, NTT.sum_range_two_mul]
  rw [show 2 ^ (k + 1) = 2 * 2 ^ k by ring] at hj
  rcases lt_or_ge j (2 ^ k) with hjk | hjk
  · rw [(hlo j hjk).2, tget j hjk, zv_mul, zv_pow, hE j hjk, hO j hjk]
    exact ntt_lo k (zv w) (fun m => zv (a.getD m 0)) j
  · obtain ⟨j', rfl⟩ : ∃ j', j = 2 ^ k + j' := ⟨j - 2 ^ k, by omega⟩
    have hj' : j' < 2 ^ k := by omega
    rw [(hhi j' hj').2, tget j' hj', zv_mul, zv_pow, hE j' hj', hO j' hj']
    exact ntt_hi k (zv w) hw (fun m => zv (a.getD m 0)) j'

theorem nttR_spec : ∀ (k : ℕ) (w : G) (a : List G), a.length = 2 ^ k → (∀ x ∈ a, canon x) → canon w →
    (k = 0 ∨ zv w ^ 2 ^ (k - 1) = -1) →
    (nttR k w a).length = 2 ^ k ∧ (∀ x ∈ nttR k w a, canon x) ∧
    ∀ j < 2 ^ k, zv ((nttR k w a).getD j 0) = ∑ i ∈ Finset.range (2 ^ k), zv (a.getD i 0) * zv w ^ (i * j) := by
  intro k
  induction k with
  | zero => intro w a h hc _ _; exact nttR_base w a h hc
  | succ k ih =>
    intro w a h hc hw0 hk
    have hw : zv w ^ 2 ^ k = -1 := by simpa using hk.resolve_left (by omega)
    have he : (evensG a).length = 2 ^ k := by rw [evensG_eq, NTT.length_evens, h, pow_succ]; omega
    have ho : (oddsG a).length = 2 ^ k := by rw [oddsG_eq, NTT.length_odds, h, pow_succ]; omega
    have hce : ∀ x ∈ evensG a, canon x := fun x hx => hc x (evens_mem a x (by rwa [evensG_eq] at hx))
    have hco : ∀ x ∈ oddsG a, canon x := fun x hx => hc x (odds_mem a x (by rwa [oddsG_eq] at hx))
    have hww : canon (VF.mul w w) := mul_lt _ _
    have hk' : k = 0 ∨ zv (VF.mul w w) ^ 2 ^ (k - 1) = -1 := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exact Or.inl h0
      · right
        rw [zv_mul, ← sq, ← pow_mul, show 2 * 2 ^ (k - 1) = 2 ^ k by rw [← pow_succ']; congr 1; omega]
        exact hw
    exact nttR_step k w a h hc hw (ih _ _ he hce hww hk') (ih _ _ ho hco hww hk')

/-! ### the domain generator -/

theorem canon_seven : canon (7 : G) := by unfold canon; rw [p_lit]; decide

theorem canon_idx (a : Array G) (ha : ∀ x ∈ a.toList, canon x) (m : ℕ) : canon a[m]! := by
  by_cases h : m < a.size
  · rw [getElem!_pos a m h]; exact ha _ (by simp)
  · rw [getElem!_neg a m h]; exact Gold.zero_lt

theorem zv_dGenOf (n : ℕ) : zv (dGenOf n) = gZ ^ 2 ^ (32 - n) := by
  unfold dGenOf
  rw [zv_pow, zv_pow, zv_seven]
  rfl

theorem dGenOf_prim {n : ℕ} (hn : n ≤ 32) : n = 0 ∨ zv (dGenOf n) ^ 2 ^ (n - 1) = -1 := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · exact Or.inl h0
  · right
    rw [zv_dGenOf, ← pow_mul, ← pow_add, show 32 - n + (n - 1) = 31 by omega]
    exact gZ_pow_2_31_eq

/-! ### coset LDE -/

theorem cosetLdeR_eq (coef : Array G) (ld : ℕ) (g : G) (hg : canon g) (hprim : ld = 0 ∨ zv g ^ 2 ^ (ld - 1) = -1)
    (hc : ∀ x ∈ coef.toList, canon x) (hs : coef.size ≤ 2 ^ ld) (i : ℕ) (hi : i < 2 ^ ld) :
    (cosetLdeR coef ld g)[i]! = hornerB coef.toList (VF.mul 7 (VF.pow g i)) := by
  set A : List G := (List.range (2 ^ ld)).map
    (fun i => if i < coef.size then VF.mul coef[i]! (VF.pow VF.seven i) else 0) with hA
  have hAlen : A.length = 2 ^ ld := by simp [hA]
  have hAget : ∀ m < 2 ^ ld, A.getD m 0 =
      if m < coef.size then VF.mul coef[m]! (VF.pow VF.seven m) else 0 := by
    intro m hm; simp [hA, List.getD_eq_getElem?_getD, hm]
  have hAc : ∀ x ∈ A, canon x := by
    apply canon_of_getD
    intro m hm
    rw [hAlen] at hm
    rw [hAget m hm]
    split
    · exact mul_lt _ _
    · exact Gold.zero_lt
  obtain ⟨hl, hcn, hv⟩ := nttR_spec ld g A hAlen hAc hg hprim
  have hget : (cosetLdeR coef ld g)[i]! = (nttR ld g A).getD i 0 := by
    show ((nttR ld g A).toArray)[i]! = _
    rw [getElem!_pos _ i (by simp [hl]; exact hi)]
    simp [List.getD_eq_getElem?_getD, hl, hi]
  rw [hget]
  have hcanL : canon ((nttR ld g A).getD i 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact hcn _ (List.getElem_mem _)
  have hcanR := (hornerB_spec (VF.mul 7 (VF.pow g i)) coef.toList hc).1
  refine J8Shape.zv_inj_canon hcanL hcanR ?_
  rw [hv i hi, hornerB_zv _ _ hc, Array.length_toList]
  have h1 : ∀ m ∈ Finset.range (2 ^ ld), zv (A.getD m 0) * zv g ^ (m * i) =
      if m < coef.size then zv coef[m]! * (zv (VF.mul 7 (VF.pow g i))) ^ m else 0 := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [hAget m hm]
    split
    · rw [zv_mul, zv_mul, zv_pow, zv_pow, show zv (7 : G) = 7 from rfl, show zv VF.seven = 7 from rfl]
      ring
    · simp [zv_zero]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  have h2 : (Finset.range (2 ^ ld)).filter (· < coef.size) = Finset.range coef.size := by
    ext m; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [h2]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [getElem!_pos coef.toList m (by simpa using hm), getElem!_pos coef m hm]
  simp

/-! ### the orbit -/

def orbSt (S g : G) (n : ℕ) : Array G × G :=
  (List.range n).foldl (fun (st : Array G × G) _ => (st.1.push st.2, VF.mul st.2 g)) (#[], S)

theorem orbitPts_eq (XI : ExecInst) : orbitPts XI= (orbSt XI.hShift XI.hGen XI.hN).1 := by
  unfold orbitPts orbSt
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.forIn_pure_yield_eq_foldl]
  simp [← List.range_eq_range']
  rfl

theorem orbSt_succ (S g : G) (n : ℕ) :
    orbSt S g (n + 1) = ((orbSt S g n).1.push (orbSt S g n).2, VF.mul (orbSt S g n).2 g) := by
  simp [orbSt, List.range_succ, List.foldl_append]

theorem orbSt_spec (S g : G) (hS : canon S) : ∀ n : ℕ,
    (orbSt S g n).1.size = n ∧ canon (orbSt S g n).2 ∧ zv (orbSt S g n).2 = zv S * zv g ^ n ∧
    ∀ i < n, canon (orbSt S g n).1[i]! ∧ zv (orbSt S g n).1[i]! = zv S * zv g ^ i
  | 0 => ⟨by simp [orbSt], by simpa [orbSt] using hS, by simp [orbSt], fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨h1, h2, h3, h4⟩ := orbSt_spec S g hS n
    rw [orbSt_succ]
    refine ⟨by simp [h1], mul_lt _ _, by simp only []; rw [zv_mul, h3]; ring, ?_⟩
    intro i hi
    have hsz : i < ((orbSt S g n).1.push (orbSt S g n).2).size := by simp [h1]; omega
    simp only []
    rw [getElem!_pos _ i hsz, Array.getElem_push]
    split
    · rename_i hlt
      rw [← getElem!_pos _ i (by omega)]
      exact h4 i (by omega)
    · have : i = n := by omega
      subst this
      exact ⟨h2, h3⟩

theorem orbitPts_spec (XI : ExecInst) (hS : canon XI.hShift) :
    (orbitPts XI).size = XI.hN ∧ ∀ i < XI.hN, canon (orbitPts XI)[i]! ∧ zv (orbitPts XI)[i]! = zv XI.hShift * zv XI.hGen ^ i := by
  rw [orbitPts_eq]
  obtain ⟨h1, -, -, h4⟩ := orbSt_spec XI.hShift XI.hGen hS XI.hN
  exact ⟨h1, h4⟩

theorem orbitPts_canon (XI : ExecInst) (hS : canon XI.hShift) (i : ℕ) : canon (orbitPts XI)[i]! := by
  obtain ⟨h1, h2⟩ := orbitPts_spec XI hS
  by_cases hi : i < XI.hN
  · exact (h2 i hi).1
  · rw [getElem!_neg _ i (by omega)]; exact Gold.zero_lt

/-! ### linear-factor products -/

def evalA (a : Array G) (y : ZMod NockvmE2E.Exec.p) : ZMod NockvmE2E.Exec.p :=
  ∑ m ∈ Finset.range a.size, zv a[m]! * y ^ m

theorem mulLin_size (a : Array G) (h : G) : (mulLin a h).size = a.size + 1 := by simp [mulLin]

theorem mulLin_idx (a : Array G) (h : G) (m : ℕ) (hm : m < a.size + 1) :
    (mulLin a h)[m]! = VF.sub (if m == 0 then 0 else a[m - 1]!) (VF.mul h (if m < a.size then a[m]! else 0)) := by
  unfold mulLin
  rw [getElem!_pos _ m (by simpa using hm)]
  simp

theorem mulLin_canon (a : Array G) (h : G) (ha : ∀ x ∈ a.toList, canon x) :
    ∀ x ∈ (mulLin a h).toList, canon x := by
  intro x hx
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hx
  have hm' : m < a.size + 1 := by simpa [mulLin_size] using hm
  have := mulLin_idx a h m hm'
  rw [getElem!_pos _ m (by simpa [mulLin_size] using hm')] at this
  simp only [Array.getElem_toList]
  rw [this]
  refine sub_lt _ _ ?_ (mul_lt _ _)
  split
  · exact Gold.zero_lt
  · exact canon_idx a ha _

theorem mulLin_val (a : Array G) (h : G) (ha : ∀ x ∈ a.toList, canon x) (m : ℕ) (hm : m < a.size + 1) :
    zv (mulLin a h)[m]! = (if m = 0 then 0 else zv a[m - 1]!) - zv h * (if m < a.size then zv a[m]! else 0) := by
  rw [mulLin_idx a h m hm]
  have c1 : canon (if m == 0 then (0 : G) else a[m - 1]!) := by
    split
    · exact Gold.zero_lt
    · exact canon_idx a ha _
  have c2 : canon (VF.mul h (if m < a.size then a[m]! else 0)) := mul_lt _ _
  have z1 : zv (if m == 0 then (0 : G) else a[m - 1]!) = if m = 0 then 0 else zv a[m - 1]! := by
    by_cases hm0 : m = 0
    · simp [hm0, zv_zero]
    · simp [hm0]
  have z2 : zv (if m < a.size then a[m]! else 0) = if m < a.size then zv a[m]! else 0 := by
    by_cases hlt : m < a.size
    · rw [if_pos hlt, if_pos hlt]
    · rw [if_neg hlt, if_neg hlt]; rfl
  rw [zv_sub _ _ c1 c2, zv_mul, z1, z2]

theorem mulLin_eval (a : Array G) (h : G) (ha : ∀ x ∈ a.toList, canon x) (y : ZMod NockvmE2E.Exec.p) :
    evalA (mulLin a h) y = evalA a y * (y - zv h) := by
  unfold evalA
  rw [mulLin_size]
  have e : ∀ m ∈ Finset.range (a.size + 1), zv (mulLin a h)[m]! * y ^ m =
      (if m = 0 then 0 else zv a[m - 1]!) * y ^ m - zv h * ((if m < a.size then zv a[m]! else 0) * y ^ m) := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [mulLin_val a h ha m hm]; ring
  have s1 : ∑ m ∈ Finset.range (a.size + 1), (if m = 0 then 0 else zv a[m - 1]!) * y ^ m =
      (∑ m ∈ Finset.range a.size, zv a[m]! * y ^ m) * y := by
    rw [Finset.sum_range_succ', Finset.sum_mul]
    simp [pow_succ, mul_assoc]
  have s2 : ∑ m ∈ Finset.range (a.size + 1), (if m < a.size then zv a[m]! else 0) * y ^ m =
      ∑ m ∈ Finset.range a.size, zv a[m]! * y ^ m := by
    rw [Finset.sum_range_succ]
    simp only [lt_irrefl, if_false, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    simp [hm]
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.mul_sum, s1, s2]
  ring

theorem prodLin_fold (pts : Array G) (hp : ∀ i : ℕ, canon pts[i]!) : ∀ (n lo : ℕ) (a : Array G),
    (∀ x ∈ a.toList, canon x) →
    ((List.range' lo n).foldl (fun (a : Array G) (i : ℕ) => mulLin a pts[i]!) a).size = a.size + n ∧
    (∀ x ∈ ((List.range' lo n).foldl (fun (a : Array G) (i : ℕ) => mulLin a pts[i]!) a).toList, canon x) ∧
    ∀ y, evalA ((List.range' lo n).foldl (fun (a : Array G) (i : ℕ) => mulLin a pts[i]!) a) y =
      evalA a y * ∏ i ∈ Finset.Ico lo (lo + n), (y - zv pts[i]!)
  | 0, lo, a, ha => ⟨by simp, by simpa using ha, fun y => by simp⟩
  | n + 1, lo, a, ha => by
    rw [List.range'_succ, List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := prodLin_fold pts hp n (lo + 1) (mulLin a pts[lo]!) (mulLin_canon a _ ha)
    refine ⟨by rw [h1, mulLin_size]; omega, h2, fun y => ?_⟩
    rw [h3, mulLin_eval a _ ha, show lo + (n + 1) = lo + 1 + n by omega,
      Finset.prod_eq_prod_Ico_succ_bot (by omega : lo < lo + 1 + n)]
    ring

theorem prodLinR_spec (pts : Array G) (hp : ∀ i : ℕ, canon pts[i]!) (lo hi : ℕ) :
    (prodLinR pts lo hi).size = hi - lo + 1 ∧ (∀ x ∈ (prodLinR pts lo hi).toList, canon x) ∧
    ∀ y, evalA (prodLinR pts lo hi) y = ∏ i ∈ Finset.Ico lo (lo + (hi - lo)), (y - zv pts[i]!) := by
  have h1 : ∀ x ∈ (#[1] : Array G).toList, canon x := by
    intro x hx; simp at hx; subst hx; exact Gold.one_lt
  obtain ⟨a, b, c⟩ := prodLin_fold pts hp (hi - lo) lo #[1] h1
  refine ⟨by unfold prodLinR; rw [a]; simp; omega, b, fun y => ?_⟩
  unfold prodLinR
  rw [c]
  simp [evalA, zv_one]

theorem hornerB_evalA (a : Array G) (ha : ∀ x ∈ a.toList, canon x) (y : G) :
    canon (hornerB a.toList y) ∧ zv (hornerB a.toList y) = evalA a (zv y) := by
  refine ⟨(hornerB_spec y _ ha).1, ?_⟩
  rw [hornerB_zv y _ ha, Array.length_toList]
  unfold evalA
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [getElem!_pos a.toList m (by simpa using hm), getElem!_pos a m hm]
  simp

/-! ### the table layout -/

/-- fold invariant for `tabsOk` -/
theorem fold_inv (f : Nat × Nat × Bool → TabInst → Nat × Nat × Bool) (Q : ℕ → Prop)
    (hf1 : ∀ st t, (f st t).1 = st.1 + t.nc)
    (hf2 : ∀ st t, (f st t).2.2 = true → st.2.2 = true ∧ ∀ c, st.1 ≤ c → c < st.1 + t.nc → Q c) :
    ∀ (ts : List TabInst) (st : Nat × Nat × Bool), (ts.foldl f st).2.2 = true →
      st.2.2 = true ∧ ∀ c, st.1 ≤ c → c < (ts.foldl f st).1 → Q c
  | [], st, h => ⟨h, fun c h1 h2 => absurd h2 (by simp; omega)⟩
  | t :: ts, st, h => by
    obtain ⟨ih1, ih2⟩ := fold_inv f Q hf1 hf2 ts (f st t) h
    obtain ⟨g1, g2⟩ := hf2 st t ih1
    refine ⟨g1, fun c hc1 hc2 => ?_⟩
    by_cases hlt : c < st.1 + t.nc
    · exact g2 c hc1 hlt
    · exact ih2 c (by rw [hf1]; omega) hc2

theorem hpd_of_tabsOk (XI : ExecInst) (h : tabsOk XI= true) : ∀ c < XI.nc, XI.pre[c]!.size ≤ XI.hN + 1 := by
  unfold tabsOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨_, hok, hn, _⟩ := h
  rw [← Array.foldl_toList] at hok hn
  refine fun c hc => (fold_inv _ (fun c => XI.pre[c]!.size ≤ XI.hN + 1) ?_ ?_ XI.tabs.toList _ hok).2 c (Nat.zero_le _) (by omega)
  · intro st t; rfl
  · intro st t hh
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range, and_assoc] at hh
    obtain ⟨hok, hcol, -, -, -, -, -, -, -, hall, -⟩ := hh
    refine ⟨hok, fun c hc1 hc2 => ?_⟩
    have := hall (c - t.col0) (by omega)
    have e : t.col0 + (c - t.col0) = c := by omega
    rw [e] at this
    split at this
    · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at this
      obtain ⟨-, h2⟩ := this
      split at h2
      · simpa using h2
      · simp only [beq_iff_eq] at h2; omega
    · simp only [Bool.and_eq_true, beq_iff_eq] at this
      have := this.2; omega

/-! ### the committed word is the spec word -/

theorem paramsOk_of_gates {XI : ExecInst} (hg : setupGates XI= true) : paramsOk XI= true := by
  simp only [setupGates, Bool.and_eq_true] at hg; tauto

theorem tabsOk_of_gates {XI : ExecInst} (hg : setupGates XI= true) : tabsOk XI= true := by
  simp only [setupGates, Bool.and_eq_true] at hg; tauto

theorem dGen_eq_of_paramsOk {XI : ExecInst} (hp : paramsOk XI= true) : XI.dGen = dGenOf XI.nD := by
  unfold paramsOk at hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact hp.2

theorem lde_word (XI : ExecInst) (hg : setupGates XI= true) (hD : XI.hN < 2 ^ XI.nD) (col : FixCol)
    (hcol : col ∈ fixCols XI) (i : ℕ) (hi : i < 2 ^ XI.nD) :
    (cosetLdeR (fixPoly XI (orbitPts XI) col) XI.nD XI.dGen)[i]! = specWord XI col i := by
  obtain ⟨hS, hpre⟩ := canon_of_gates hg
  have hp := paramsOk_of_gates hg
  have htabs := tabsOk_of_gates hg
  have hdS := J8Shape.dShift_of_paramsOk XI hp
  have hn32 := J8Shape.nD_le_of_paramsOk XI hp
  have hdG := dGen_eq_of_paramsOk hp
  have hprim : XI.nD = 0 ∨ zv XI.dGen ^ 2 ^ (XI.nD - 1) = -1 := by rw [hdG]; exact dGenOf_prim hn32
  have hgc : canon XI.dGen := by rw [hdG]; exact Inst.canon_pow _ _
  have hpt : canon (VF.mul 7 (VF.pow XI.dGen i)) := mul_lt _ _
  have horb := orbitPts_canon XI hS
  obtain ⟨hosz, hoi⟩ := orbitPts_spec XI hS
  unfold specWord domPt
  rw [hdS]
  cases col with
  | pre c =>
    have hc : c < XI.nc := fixCols_pre_lt XI _ hcol c rfl
    have hsz : XI.pre[c]!.size ≤ 2 ^ XI.nD := by have := hpd_of_tabsOk XI htabs c hc; omega
    show (cosetLdeR XI.pre[c]! XI.nD XI.dGen)[i]! = hornerB XI.pre[c]!.toList _
    exact cosetLdeR_eq _ _ _ hgc hprim (hpre c) hsz i hi
  | zh =>
    obtain ⟨hs, hc, hv⟩ := prodLinR_spec (orbitPts XI) horb 0 XI.hN
    have hsz : (prodLinR (orbitPts XI) 0 XI.hN).size ≤ 2 ^ XI.nD := by omega
    show (cosetLdeR (prodLinR (orbitPts XI) 0 XI.hN) XI.nD XI.dGen)[i]! = zhG XI _
    rw [cosetLdeR_eq _ _ _ hgc hprim hc hsz i hi]
    obtain ⟨hl1, hl2⟩ := hornerB_evalA _ hc (VF.mul 7 (VF.pow XI.dGen i))
    obtain ⟨r1, r2, r3, -⟩ := prodLinG_spec XI.hGen (VF.mul 7 (VF.pow XI.dGen i)) XI.hShift hpt hS XI.hN
    refine J8Shape.zv_inj_canon hl1 r1 ?_
    unfold zhG
    rw [hl2, hv, r3, Nat.zero_add, Nat.sub_zero, ← Finset.range_eq_Ico]
    refine Finset.prod_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [(hoi m hm).2]
  | zout t =>
    obtain ⟨hs, hc, hv⟩ := prodLinR_spec (orbitPts XI) horb (tabHN XI t) XI.hN
    have hsz : (prodLinR (orbitPts XI) (tabHN XI t) XI.hN).size ≤ 2 ^ XI.nD := by omega
    show (cosetLdeR (prodLinR (orbitPts XI) (tabHN XI t) XI.hN) XI.nD XI.dGen)[i]! = zoutG XI (tabHN XI t) _
    rw [cosetLdeR_eq _ _ _ hgc hprim hc hsz i hi]
    obtain ⟨hl1, hl2⟩ := hornerB_evalA _ hc (VF.mul 7 (VF.pow XI.dGen i))
    have hst : canon (VF.mul XI.hShift (VF.pow XI.hGen (tabHN XI t))) := mul_lt _ _
    obtain ⟨r1, r2, r3, -⟩ := prodLinG_spec XI.hGen (VF.mul 7 (VF.pow XI.dGen i))
      (VF.mul XI.hShift (VF.pow XI.hGen (tabHN XI t))) hpt hst (XI.hN - tabHN XI t)
    refine J8Shape.zv_inj_canon hl1 r1 ?_
    unfold zoutG
    rw [hl2, hv, r3, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel_left]
    refine Finset.prod_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [(hoi (tabHN XI t + m) (by omega)).2]
    simp only [zv_mul, zv_pow, pow_add]
    ring

end NockvmE2E.Exec.V

#print axioms NockvmE2E.Exec.V.nttR_spec
#print axioms NockvmE2E.Exec.V.cosetLdeR_eq
#print axioms NockvmE2E.Exec.V.prodLinR_spec
#print axioms NockvmE2E.Exec.V.orbitPts_spec
#print axioms NockvmE2E.Exec.V.hpd_of_tabsOk
#print axioms NockvmE2E.Exec.V.lde_word
