/-
  Nock/Atoms/Fingerprint.lean

  **Limb-coin fingerprints of atoms — injectivity, the
  Schwartz–Zippel event bounds, and the same-coin collision.**

  A big
  atom's limb polynomial `A_n(Y) = Σ lᵢ Yⁱ` is evaluated at a LIMB coin `y`, separate from the
  structure coin `z`; at the noun level a big atom is a leaf `⟨z, 0, A_n(y)⟩`.

  * `natPoly`, `limbPoly l := natPoly l` mapped to `𝔽_p`; `val_eq_eval` (`val l = natPoly(l)(B)`).
  * `limbPoly_injOn` — on canonical lists, `limbPoly` is injective (coefficients `< B < p`).
  * `L n` (`C n` for small `n < p`, `limbPoly (limbs n)` for big) and `L_injective`: the leaf
    polynomial map `ℕ → 𝔽_p[Y]` is injective (small/small, big/big, small/big by degree).
  * **Step 1 (one `card_roots'`):** `card_limb_collision_le` — two distinct canonical limb lists
    have the same `A(y)` at ≤ `max len − 1` points `y` of any field `K ⊇ 𝔽_p`; `card_leafVal_collision_le`
    the same for `leafVal y n := aeval y (L n)`.
  * **Step 2 (a second `card_roots'`):** `card_leafSum_collision_le` — two distinct same-length
    atom sequences, read as the leaf coordinate `Σ leafVal y nᵢ · zⁱ` (Horner, the `cons` rule
    `leaf = a.leaf + a.size · b.leaf` at atom size `z`), collide at ≤ `|K|·(k − 1) + |K|·(N − 1)`
    pairs `(z, y)`.  Exactly two Schwartz–Zippel steps.
  * Positive control
    `limbCoin_separates`: at the limb coin they differ at `(z, y) = (0, 1)` over `𝔽_p`.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Defs
import Nock.Atoms.Limbs
import Nock.ComputeTable

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.Atoms

open Polynomial

/-- The base field `𝔽_p`. -/
abbrev Fp : Type := ZMod p

/-! ## Limb polynomials -/

/-- The limb polynomial over `ℕ`: `Σ lᵢ Xⁱ` (Horner form). -/
noncomputable def natPoly : List ℕ → ℕ[X]
  | [] => 0
  | a :: l => C a + X * natPoly l

theorem coeff_natPoly (l : List ℕ) (i : ℕ) : (natPoly l).coeff i = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp [natPoly]
  | cons a l ih =>
    cases i with
    | zero => simp [natPoly]
    | succ i => simp [natPoly, coeff_X_mul, ih]

theorem val_eq_eval (l : List ℕ) : val l = (natPoly l).eval B := by
  induction l with
  | nil => simp [natPoly]
  | cons a l ih => simp [natPoly, ih]

/-- The limb polynomial over `𝔽_p`. -/
noncomputable def limbPoly (l : List ℕ) : Fp[X] := (natPoly l).map (Nat.castRingHom Fp)

theorem coeff_limbPoly (l : List ℕ) (i : ℕ) : (limbPoly l).coeff i = ((l.getD i 0 : ℕ) : Fp) := by
  simp [limbPoly, coeff_map, coeff_natPoly]

theorem getD_lt_B {l : List ℕ} (hl : ∀ a ∈ l, a < B) (i : ℕ) : l.getD i 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => simp [B]
  | some a => simpa using hl a (List.mem_of_getElem? h)

theorem B_lt_p : B < p := by norm_num [B, Nock.Field.p]

theorem natCast_inj_lt {a b : ℕ} (ha : a < p) (hb : b < p) (h : (a : Fp) = (b : Fp)) : a = b := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- On lists with limbs `< B`, equal `𝔽_p` limb polynomials have equal values. -/
theorem val_eq_of_limbPoly_eq {l l' : List ℕ} (hl : ∀ a ∈ l, a < B) (hl' : ∀ a ∈ l', a < B)
    (h : limbPoly l = limbPoly l') : val l = val l' := by
  have hn : natPoly l = natPoly l' := by
    ext i
    have := congrArg (fun q => q.coeff i) h
    simp only [coeff_limbPoly] at this
    rw [coeff_natPoly, coeff_natPoly]
    exact natCast_inj_lt (lt_trans (getD_lt_B hl i) B_lt_p) (lt_trans (getD_lt_B hl' i) B_lt_p) this
  rw [val_eq_eval, val_eq_eval, hn]

/-- **`limbPoly` is injective on canonical lists.** -/
theorem limbPoly_injOn {l l' : List ℕ} (hl : Canonical l) (hl' : Canonical l')
    (h : limbPoly l = limbPoly l') : l = l' :=
  canonical_unique hl hl' (val_eq_of_limbPoly_eq hl.1 hl'.1 h)

theorem degree_limbPoly_lt (l : List ℕ) : (limbPoly l).degree < l.length := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_limbPoly, List.getD_eq_default _ _ hm, Nat.cast_zero]

/-! ## The leaf polynomial of an atom -/

/-- **`L n`**: the constant `n` for a small atom, the limb polynomial for a big one. -/
noncomputable def L (n : ℕ) : Fp[X] := if n < p then C (n : Fp) else limbPoly (limbs n)

/-- The length bound of `L n`: `1` for small, the limb count for big. -/
def lenL (n : ℕ) : ℕ := if n < p then 1 else (limbs n).length

theorem degree_L_lt (n : ℕ) : (L n).degree < lenL n := by
  unfold L lenL
  split_ifs
  · exact lt_of_le_of_lt degree_C_le (by norm_num)
  · exact degree_limbPoly_lt _

theorem one_le_lenL (n : ℕ) : 1 ≤ lenL n := by
  unfold lenL; split_ifs with h
  · exact le_refl _
  · have := two_le_length_of_big (n := n) (by unfold IsBig; omega); omega

/-- The top coefficient of a big atom's limb polynomial is nonzero, at index `len − 1 ≥ 1`. -/
theorem coeff_top_limbs_ne_zero {n : ℕ} (hn : p ≤ n) :
    (limbPoly (limbs n)).coeff ((limbs n).length - 1) ≠ 0 := by
  have h2 := two_le_length_of_big (n := n) hn
  have hne : limbs n ≠ [] := by intro h; rw [h] at h2; simp at h2
  have htop := (limbs_canonical n).2 hne
  have hlt := (limbs_canonical n).1 _ (List.getLast_mem hne)
  rw [coeff_limbPoly]
  have hi : (limbs n).length - 1 < (limbs n).length := by omega
  have hg : (limbs n).getD ((limbs n).length - 1) 0 = (limbs n).getLast hne := by
    rw [List.getD_eq_getElem _ _ hi, List.getLast_eq_getElem]
  rw [hg]
  intro h0
  apply htop
  exact natCast_inj_lt (lt_trans hlt B_lt_p) (by norm_num [Nock.Field.p]) (by simpa using h0)

/-- **`L` is injective**: as polynomials in `Y` over `𝔽_p`, distinct atoms have distinct leaf
polynomials (SPEC-SEMANTICS S2.3: small/small by `n < p`, big/big by canonical uniqueness,
small/big by degree). -/
theorem L_injective : Function.Injective L := by
  intro n m h
  unfold L at h
  by_cases hn : n < p <;> by_cases hm : m < p <;> simp only [hn, hm, if_true, if_false] at h
  · exact natCast_inj_lt hn hm (C_injective h)
  · exfalso
    have h1 := congrArg (fun q => q.coeff ((limbs m).length - 1)) h
    have h2 := two_le_length_of_big (n := m) (by unfold IsBig; omega)
    simp only [coeff_C] at h1
    rw [if_neg (by omega)] at h1
    exact coeff_top_limbs_ne_zero (n := m) (by omega) h1.symm
  · exfalso
    have h1 := congrArg (fun q => q.coeff ((limbs n).length - 1)) h
    have h2 := two_le_length_of_big (n := n) (by unfold IsBig; omega)
    simp only [coeff_C] at h1
    rw [if_neg (by omega)] at h1
    exact coeff_top_limbs_ne_zero (n := n) (by omega) h1
  · have := limbPoly_injOn (limbs_canonical n) (limbs_canonical m) h
    rw [← val_limbs n, ← val_limbs m, this]

/-! ## The univariate event at the limb coin -/

section Events

variable {K : Type*} [Field K] [Algebra Fp K] [Fintype K] [DecidableEq K]

/-- **Generic univariate Schwartz–Zippel** (one `card_roots'`): two distinct `𝔽_p` polynomials of
degree `< N` agree at ≤ `N − 1` points of `K`. -/
theorem card_agree_le {f g : Fp[X]} {N : ℕ} (hfg : f ≠ g) (hf : f.degree < N) (hg : g.degree < N) :
    (Finset.univ.filter (fun y : K => aeval y f = aeval y g)).card ≤ N - 1 := by
  set D : K[X] := (f - g).map (algebraMap Fp K) with hD
  have hD0 : D ≠ 0 := by
    rw [hD, Ne, Polynomial.map_eq_zero_iff (algebraMap Fp K).injective]
    exact sub_ne_zero.mpr hfg
  have hsub : Finset.univ.filter (fun y : K => aeval y f = aeval y g) ⊆ D.roots.toFinset := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [Multiset.mem_toFinset, mem_roots hD0, IsRoot, hD, eval_map_algebraMap, map_sub, hy,
      sub_self]
  have hdeg : (f - g).degree < N := lt_of_le_of_lt (degree_sub_le f g) (max_lt hf hg)
  have hnat : D.natDegree < N := by
    rw [hD, natDegree_map_eq_of_injective (algebraMap Fp K).injective]
    exact (natDegree_lt_iff_degree_lt (sub_ne_zero.mpr hfg)).mpr hdeg
  calc _ ≤ D.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card D.roots := Multiset.toFinset_card_le _
    _ ≤ D.natDegree := card_roots' D
    _ ≤ N - 1 := by omega

/-- **Step 1 for limb lists**: two distinct canonical limb lists give the same `A(y)` at no more
than `max len − 1` points `y`. -/
theorem card_limb_collision_le {l l' : List ℕ} (hl : Canonical l) (hl' : Canonical l')
    (hne : l ≠ l') :
    (Finset.univ.filter (fun y : K => aeval y (limbPoly l) = aeval y (limbPoly l'))).card ≤
      max l.length l'.length - 1 :=
  card_agree_le (fun h => hne (limbPoly_injOn hl hl' h))
    (lt_of_lt_of_le (degree_limbPoly_lt l) (by exact_mod_cast le_max_left _ _))
    (lt_of_lt_of_le (degree_limbPoly_lt l') (by exact_mod_cast le_max_right _ _))

/-- The leaf value of an atom at the limb coin `y`: `n` if small, `A_n(y)` if big. -/
noncomputable def leafVal (y : K) (n : ℕ) : K := aeval y (L n)

theorem leafVal_small (y : K) {n : ℕ} (hn : n < p) : leafVal y n = algebraMap Fp K (n : Fp) := by
  simp [leafVal, L, hn]

/-- **Step 1 for atoms**: distinct atoms have the same `leafVal` at ≤ `max lenL − 1` coins `y`. -/
theorem card_leafVal_collision_le {n m : ℕ} (hne : n ≠ m) :
    (Finset.univ.filter (fun y : K => leafVal y n = leafVal y m)).card ≤ max (lenL n) (lenL m) - 1 :=
  card_agree_le (fun h => hne (L_injective h))
    (lt_of_lt_of_le (degree_L_lt n) (by exact_mod_cast le_max_left _ _))
    (lt_of_lt_of_le (degree_L_lt m) (by exact_mod_cast le_max_right _ _))

/-! ## The bivariate leaf coordinate -/

/-- The leaf coordinate of a right comb of atoms `[n₀ [n₁ … ]]` read with each leaf at the limb
coin: `Σ leafVal y nᵢ · zⁱ` (Horner, `cons`'s `leaf = a.leaf + a.size · b.leaf` at atom size `z`). -/
noncomputable def leafSum (y z : K) : List ℕ → K
  | [] => 0
  | n :: ns => leafVal y n + z * leafSum y z ns

/-- The same, as a polynomial in the structure variable `Z`. -/
noncomputable def zPoly (y : K) : List ℕ → K[X]
  | [] => 0
  | n :: ns => C (leafVal y n) + X * zPoly y ns

theorem eval_zPoly (y z : K) (ns : List ℕ) : (zPoly y ns).eval z = leafSum y z ns := by
  induction ns with
  | nil => simp [zPoly, leafSum]
  | cons n ns ih => simp [zPoly, leafSum, ih]

theorem coeff_zPoly (y : K) (ns : List ℕ) (i : ℕ) :
    (zPoly y ns).coeff i = (ns.map (leafVal y)).getD i 0 := by
  induction ns generalizing i with
  | nil => simp [zPoly]
  | cons n ns ih =>
    cases i with
    | zero => simp [zPoly]
    | succ i => simp [zPoly, coeff_X_mul, ih]

theorem degree_zPoly_lt (y : K) (ns : List ℕ) : (zPoly y ns).degree < ns.length := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_zPoly, List.getD_eq_default _ _ (by simpa using hm)]

/-- **Zippel, two `card_roots'`):** two same-length atom sequences that
differ at position `j` have equal leaf coordinates at ≤ `|K|·(k − 1) + |K|·(N − 1)` coin pairs
`(z, y)`, where `k` is the length and `N ≥ lenL` of the two differing atoms. -/
theorem card_leafSum_collision_le {ns ms : List ℕ} (hlen : ns.length = ms.length)
    {j : ℕ} (hj : j < ns.length) (hdiff : ns[j] ≠ ms[j]'(hlen ▸ hj)) {N : ℕ}
    (hN : max (lenL ns[j]) (lenL (ms[j]'(hlen ▸ hj))) ≤ N) :
    (Finset.univ.filter (fun zy : K × K => leafSum zy.2 zy.1 ns = leafSum zy.2 zy.1 ms)).card ≤
      Fintype.card K * (ns.length - 1) + Fintype.card K * (N - 1) := by
  set a := ns[j]
  set b := ms[j]'(hlen ▸ hj)
  set Ybad := Finset.univ.filter (fun y : K => leafVal y a = leafVal y b)
  have hYbad : Ybad.card ≤ N - 1 :=
    le_trans (card_leafVal_collision_le hdiff) (Nat.sub_le_sub_right hN 1)
  -- split by whether the coefficient at `j` vanishes at `y`
  have hsplit : Finset.univ.filter (fun zy : K × K => leafSum zy.2 zy.1 ns = leafSum zy.2 zy.1 ms)
      ⊆ (Finset.univ.filter (fun zy : K × K => leafVal zy.2 a ≠ leafVal zy.2 b ∧
            leafSum zy.2 zy.1 ns = leafSum zy.2 zy.1 ms)) ∪ (Finset.univ ×ˢ Ybad) := by
    intro zy hzy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hzy
    by_cases h : leafVal zy.2 a = leafVal zy.2 b
    · exact Finset.mem_union_right _ (by simp [Ybad, h])
    · exact Finset.mem_union_left _ (by simp [h, hzy])
  -- the good-`y` part: for each `y`, a nonzero polynomial in `z` of degree `< k`
  have hgood : (Finset.univ.filter (fun zy : K × K => leafVal zy.2 a ≠ leafVal zy.2 b ∧
        leafSum zy.2 zy.1 ns = leafSum zy.2 zy.1 ms)).card ≤ Fintype.card K * (ns.length - 1) := by
    rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product_right]
    have hper : ∀ y : K, (∑ z : K, if leafVal y a ≠ leafVal y b ∧
        leafSum y z ns = leafSum y z ms then 1 else 0) ≤ ns.length - 1 := by
      intro y
      rw [← Finset.card_filter]
      by_cases hy : leafVal y a = leafVal y b
      · simp [hy]
      · set D := zPoly y ns - zPoly y ms
        have hD0 : D ≠ 0 := by
          intro h0
          have := congrArg (fun q => q.coeff j) h0
          simp only [D, coeff_sub, coeff_zPoly, coeff_zero] at this
          rw [List.getD_eq_getElem _ _ (by simpa using hj),
            List.getD_eq_getElem _ _ (by simpa [← hlen] using hj)] at this
          simp only [List.getElem_map] at this
          exact hy (sub_eq_zero.mp this)
        have hsub : Finset.univ.filter (fun z : K => leafVal y a ≠ leafVal y b ∧
            leafSum y z ns = leafSum y z ms) ⊆ D.roots.toFinset := by
          intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
          rw [Multiset.mem_toFinset, mem_roots hD0, IsRoot, eval_sub, eval_zPoly, eval_zPoly,
            hz.2, sub_self]
        have hdeg : D.degree < ns.length := lt_of_le_of_lt (degree_sub_le _ _)
          (max_lt (degree_zPoly_lt y ns) (hlen ▸ degree_zPoly_lt y ms))
        have hnat : D.natDegree < ns.length := (natDegree_lt_iff_degree_lt hD0).mpr hdeg
        calc _ ≤ D.roots.toFinset.card := Finset.card_le_card hsub
          _ ≤ Multiset.card D.roots := Multiset.toFinset_card_le _
          _ ≤ D.natDegree := card_roots' D
          _ ≤ ns.length - 1 := by omega
    calc _ ≤ ∑ _y : K, (ns.length - 1) := Finset.sum_le_sum (fun y _ => hper y)
      _ = Fintype.card K * (ns.length - 1) := by simp [Finset.card_univ]
  calc _ ≤ _ := Finset.card_le_card hsplit
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ Fintype.card K * (ns.length - 1) + Fintype.card K * (N - 1) := by
      rw [Finset.card_product, Finset.card_univ]
      exact Nat.add_le_add hgood (Nat.mul_le_mul_left _ hYbad)

end Events

/-! ## Negative control: the same-coin encoding is not injective -/

section SameCoin

open Nock.ComputeTable

variable {K : Type*} [Field K]

/-- The limb polynomial evaluated at the STRUCTURE coin (the refuted same-coin encoding). -/
def sameCoinA (z : K) : List ℕ → K
  | [] => 0
  | a :: l => (a : K) + z * sameCoinA z l

/-- The same-coin fingerprint of a big atom: a leaf `⟨z, 0, A(z)⟩`. -/
def sameCoinBig (z : K) (l : List ℕ) : FP K := FP.atomFP z (sameCoinA z l)

/-- The nouns `[big[5,2,1] 0]` and `[big[5,1,1] 1]` —
distinct, with canonical big limb lists — have the SAME same-coin fingerprint at EVERY `z`. -/
theorem sameCoin_collision (z : K) :
    FP.cons z (sameCoinBig z [5, 2, 1]) (FP.atomFP z 0) =
      FP.cons z (sameCoinBig z [5, 1, 1]) (FP.atomFP z 1) := by
  ext <;> simp [FP.cons, sameCoinBig, sameCoinA, FP.atomFP] <;> ring

theorem sameCoin_collision_nouns_distinct :
    Canonical [5, 2, 1] ∧ Canonical [5, 1, 1] ∧ IsBig (val [5, 2, 1]) ∧ IsBig (val [5, 1, 1]) ∧
      ([5, 2, 1], 0) ≠ ([5, 1, 1], (1 : ℕ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, by decide⟩
  · intro a ha; simp at ha; rcases ha with rfl | rfl | rfl <;> norm_num [B]
  · intro _; simp
  · intro a ha; simp at ha; rcases ha with rfl | rfl <;> norm_num [B]
  · intro _; simp
  · unfold IsBig; simp [B, Nock.Field.p]
  · unfold IsBig; simp [B, Nock.Field.p]

theorem sameCoin_collision_419 (z : K) (a0 : ℕ) :
    FP.cons z (sameCoinBig z [a0, 2]) (FP.atomFP z 0) =
      FP.cons z (sameCoinBig z [a0, 1]) (FP.atomFP z 1) := by
  ext <;> simp [FP.cons, sameCoinBig, sameCoinA, FP.atomFP] <;> ring

end SameCoin

/-- **Positive control**: at the limb coin the two nouns of `sameCoin_collision` are separated —
over `𝔽_p` at `(z, y) = (0, 1)` their leaf coordinates are `8` and `7`. -/
theorem limbCoin_separates :
    leafSum (K := Fp) 1 0 [val [5, 2, 1], 0] ≠ leafSum (K := Fp) 1 0 [val [5, 1, 1], 1] := by
  have h1 : ¬ val [5, 2, 1] < p := by simp [B, Nock.Field.p]
  have h2 : ¬ val [5, 1, 1] < p := by simp [B, Nock.Field.p]
  have c1 : Canonical [5, 2, 1] := sameCoin_collision_nouns_distinct.1
  have c2 : Canonical [5, 1, 1] := sameCoin_collision_nouns_distinct.2.1
  simp only [leafSum, leafVal, L, h1, h2, if_false, limbs_val c1, limbs_val c2, zero_mul, add_zero]
  simp [limbPoly, natPoly]
  decide

end Nock.Atoms
