import NockvmE2E.Exec.Inst
import NockvmE2E.Exec.SoundFri
import NockvmE2E.Merkle.RapFriQueryOnly

set_option autoImplicit false

namespace NockvmE2E.Exec.DomIdx
open NockvmE2E.Exec Domain

theorem msu_val (n : ℕ) (hn : n ≤ 32) (j : Fin (2 ^ n)) :
    ((CosetFftDomainClass.mkSubgroupUnit (smoothDomain n hn) j : KCˣ) : KC) = ((zeta n : KCˣ) : KC) ^ j.val := by
  have h0 : (smoothDomain n hn) 0 = algebraMap (ZMod p) KC 7 := by
    rw [Inst.smoothDomain_apply]; simp
  have h7 : algebraMap (ZMod p) KC 7 ≠ 0 := fun h => seven_ne_zero ((algebraMap (ZMod p) KC).injective (by simpa using h))
  show ((smoothDomain n hn) 0)⁻¹ * (smoothDomain n hn) j = _
  rw [h0, Inst.smoothDomain_apply, ← mul_assoc, inv_mul_cancel₀ h7, one_mul]

theorem sub_apply (n : ℕ) (hn : n ≤ 32) (m : ℕ) (hm : m < n) (u : Fin (2 ^ (n - m))) :
    (smoothDomain n hn).subdomain m u =
      (algebraMap (ZMod p) KC 7) ^ 2 ^ m * ((zeta n : KCˣ) : KC) ^ (2 ^ m * u.val) := by
  rw [CosetFftDomainClass.subdomain_apply, msu_val]
  have h0 : (smoothDomain n hn) 0 = algebraMap (ZMod p) KC 7 := by
    rw [Inst.smoothDomain_apply]; simp
  rw [h0]
  have : (CosetFftDomainClass.subdomain_embed (n := n) m u).val = 2 ^ m * u.val := by
    simp [CosetFftDomainClass.subdomain_embed, show ¬ n ≤ m by omega]
  rw [this]

theorem seven_ne : algebraMap (ZMod p) KC 7 ≠ 0 :=
  fun h => seven_ne_zero ((algebraMap (ZMod p) KC).injective (by simpa using h))

/-- core: equal `2^e`-th powers of `ζ`-powers force congruence of exponents mod `2^n / 2^e` -/
theorem zeta_cancel (n : ℕ) (hn : n ≤ 32) (e : ℕ) (he : e ≤ n) (a b : ℕ)
    (h : (((zeta n : KCˣ) : KC) ^ a) ^ 2 ^ e = (((zeta n : KCˣ) : KC) ^ b) ^ 2 ^ e) :
    a % 2 ^ (n - e) = b % 2 ^ (n - e) := by
  rw [← pow_mul, ← pow_mul] at h
  have h' : (zeta n) ^ (a * 2 ^ e) = (zeta n) ^ (b * 2 ^ e) := Units.ext (by simpa using h)
  rw [pow_eq_pow_iff_modEq, orderOf_zeta hn] at h'
  have h2 : 2 ^ n = 2 ^ (n - e) * 2 ^ e := by rw [← pow_add]; congr 1; omega
  rw [h2] at h'
  exact Nat.ModEq.mul_right_cancel' (by positivity) h'

/-- index arithmetic: squares of subdomain points -/
theorem sub_idx_sq (n : ℕ) (hn : n ≤ 32) (m : ℕ) (hm : m + 1 ≤ n) (u : Fin (2 ^ (n - m))) (P : ℕ)
    (h : ((smoothDomain n hn).subdomain m u) ^ 2 =
      (((algebraMap (ZMod p) KC 7) * ((zeta n : KCˣ) : KC) ^ P) ^ 2 ^ m) ^ 2) :
    u.val % 2 ^ (n - m - 1) = P % 2 ^ (n - m - 1) := by
  rw [sub_apply n hn m (by omega)] at h
  generalize hZ : ((zeta n : KCˣ) : KC) = zz at h
  generalize hA : algebraMap (ZMod p) KC 7 = aa at h
  have hA0 : aa ≠ 0 := hA ▸ seven_ne
  have h1 : (aa ^ 2 ^ m) ^ 2 * (zz ^ (2 ^ m * u.val)) ^ 2 = (aa ^ 2 ^ m) ^ 2 * (zz ^ (P * 2 ^ m)) ^ 2 := by
    rw [← mul_pow, ← mul_pow]
    convert h using 2
    rw [mul_pow, ← pow_mul, mul_comm P]
  have h2 := mul_left_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hA0)) h1
  subst hZ
  have key : ∀ a : ℕ, (((zeta n : KCˣ) : KC) ^ a) ^ 2 ^ (m + 1) = (((zeta n : KCˣ) : KC) ^ (2 ^ m * a)) ^ 2 := by
    intro a; rw [← pow_mul, ← pow_mul, pow_succ]; congr 1; ring
  have h3 := zeta_cancel n hn (m + 1) hm u.val P (by rw [key, key, mul_comm (2 ^ m) P]; exact h2)
  have h4 : n - (m + 1) = n - m - 1 := by omega
  rwa [h4] at h3

theorem sub_idx_eq (n : ℕ) (hn : n ≤ 32) (m : ℕ) (hm : m + 1 ≤ n) (u : Fin (2 ^ (n - m))) (P : ℕ)
    (h : (smoothDomain n hn).subdomain m u =
      ((algebraMap (ZMod p) KC 7) * ((zeta n : KCˣ) : KC) ^ P) ^ 2 ^ m) :
    u.val % 2 ^ (n - m) = P % 2 ^ (n - m) := by
  rw [sub_apply n hn m (by omega), mul_pow] at h
  have h2 := mul_left_cancel₀ (pow_ne_zero _ seven_ne) h
  exact zeta_cancel n hn m (by omega) u.val P (by
    rw [← pow_mul, ← pow_mul, mul_comm u.val, mul_comm P] ; rw [← pow_mul, mul_comm P] at h2; exact h2)

theorem pt_idx (n : ℕ) (hn : n ≤ 32) (e : ℕ) (he : e ≤ n) (a b : ℕ)
    (h : ((algebraMap (ZMod p) KC 7) * ((zeta n : KCˣ) : KC) ^ a) ^ 2 ^ e =
      ((algebraMap (ZMod p) KC 7) * ((zeta n : KCˣ) : KC) ^ b) ^ 2 ^ e) :
    a % 2 ^ (n - e) = b % 2 ^ (n - e) := by
  rw [mul_pow, mul_pow] at h
  exact zeta_cancel n hn e he a b (mul_left_cancel₀ (pow_ne_zero _ seven_ne) h)

theorem mod_weaken {a b M N : ℕ} (hMN : M ≤ N) (h : a % 2 ^ N = b % 2 ^ N) : a % 2 ^ M = b % 2 ^ M :=
  Nat.ModEq.of_dvd (pow_dvd_pow 2 hMN) h

section Read
open NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri Fri.Spec.QueryRound BatchedFri.Spec BatchedFri.Spec.BatchingRound NockvmE2E.Merkle.RapFriQ

variable {n k : ℕ} {ω : SmoothCosetFftDomain n KC} (s : Fin (k + 1) → ℕ+) (l : ℕ)

theorem readSet_idx (hn : n ≤ 32) (hω : ω = smoothDomain n hn) (hn1 : 1 ≤ n) (hs1 : ∀ i, (s i).val = 1)
    (hs : (∑ j, (s j).val) ≤ n) (xs : Fin l → (ω.subdomain 0).toFinset) (pos : Fin l → ℕ)
    (hx : ∀ j, (xs j).val = algebraMap (ZMod p) KC 7 * ((zeta n : KCˣ) : KC) ^ pos j)
    (x : Fin (2 ^ n)) (hxr : x ∈ readSet s l hs xs) : ∃ j, x.val % 2 ^ (n - 1) = pos j % 2 ^ (n - 1) := by
  subst hω
  obtain ⟨y, hy, rfl⟩ := hxr
  obtain ⟨j, hj⟩ := hy
  refine ⟨j, ?_⟩
  have hxv : (smoothDomain n hn) ((CosetFftDomain.equivToFinset (smoothDomain n hn)).symm (initialDomainPoint s 0 y)) = y.val := by
    rw [CosetFftDomain.equivToFinset_symm_apply]; rfl
  rw [Inst.smoothDomain_apply] at hxv
  have hsum : (∑ j ∈ finRangeTo (k + 1) (0 : Fin (k + 1)).val, (s j).val) = 0 := by simp [finRangeTo]
  rcases hj with hj | hj
  · have h1 := (mem_queryBlock_iff_pow_eq s hs 0 (xs j) y).mp hj
    have hq : (queryPoint s hs 0 (xs j)).val = (xs j).val := by simp [queryPoint]
    rw [hq, hs1, ← hxv, hx j] at h1
    exact pt_idx n hn 1 hn1 _ _ h1
  · have hf : Fri.Spec.foldingPrefix s (Fin.castSucc 0) = 0 := by simp
    rw [hf, pow_zero, pow_one, hx j] at hj
    rw [hj] at hxv
    exact mod_weaken (Nat.sub_le n 1) (pt_idx n hn 0 (Nat.zero_le _) _ _ (by simpa using hxv))

theorem readPts_idx (hn : n ≤ 32) (hω : ω = smoothDomain n hn) (hs1 : ∀ i, (s i).val = 1)
    (hs : (∑ j, (s j).val) ≤ n) (xs : Fin l → (ω.subdomain 0).toFinset) (pos : Fin l → ℕ)
    (hx : ∀ j, (xs j).val = algebraMap (ZMod p) KC 7 * ((zeta n : KCˣ) : KC) ^ pos j)
    (i : ℕ) (hi : i + 2 ≤ n) (hik : i < k) (y : wordDom (ω := ω) s i)
    (hy : y ∈ readPts s l hs xs ⟨i + 1, by omega⟩) :
    ∃ j, ((ω.subdomain (∑ j ∈ finRangeTo (k + 1) (i + 1), (s j).val)).equivToFinset.symm y).val
        % 2 ^ (n - i - 2) = pos j % 2 ^ (n - i - 2) := by
  subst hω
  obtain ⟨j, hj⟩ := hy
  refine ⟨j, ?_⟩
  have hm : (∑ j ∈ finRangeTo (k + 1) (i + 1), (s j).val) = i + 1 := by
    have := foldingPrefix_eq s hs1 (Fin.castSucc ⟨i + 1, by omega⟩)
    simpa [Fri.Spec.foldingPrefix] using this
  have hyv := CosetFftDomain.equivToFinset_symm_apply
    ((smoothDomain n hn).subdomain (∑ j ∈ finRangeTo (k + 1) (i + 1), (s j).val)) y
  generalize hu : (CosetFftDomain.equivToFinset
    ((smoothDomain n hn).subdomain (∑ j ∈ finRangeTo (k + 1) (i + 1), (s j).val))).symm y = u at hyv ⊢
  have hmn : (∑ j ∈ finRangeTo (k + 1) (i + 1), (s j).val) + 1 ≤ n := by rw [hm]; omega
  rcases hj with hj | hj
  · have h1 := (mem_queryBlock_iff_pow_eq s hs ⟨i + 1, by omega⟩ (xs j) y).mp hj
    have hq : (queryPoint s hs ⟨i + 1, by omega⟩ (xs j)).val =
        (xs j).val ^ 2 ^ (∑ j ∈ finRangeTo (k + 1) (i + 1), (s j).val) := rfl
    rw [hs1, hq, ← hyv, hx j, pow_one] at h1
    have h2 := sub_idx_sq n hn _ hmn u (pos j) h1
    have e : n - (∑ j ∈ finRangeTo (k + 1) (i + 1), (s j).val) - 1 = n - i - 2 := by rw [hm]; omega
    rwa [e] at h2
  · have hj' : (CosetFftDomain.subdomain (smoothDomain n hn) (∑ j ∈ finRangeTo (k + 1) (i + 1), (s j).val)) u =
        ((algebraMap (ZMod p) KC 7) * ((zeta n : KCˣ) : KC) ^ pos j) ^ 2 ^ (∑ j ∈ finRangeTo (k + 1) (i + 1), (s j).val) := by
      rw [hyv, hj, hx j]; rfl
    have h2 := sub_idx_eq n hn _ hmn u (pos j) hj'
    refine mod_weaken ?_ h2
    rw [hm]; omega

/-! ## non-vacuity: `n = 3`, `k = 1`, `l = 1`, `xs 0 = ω 5` -/

section Toy
open Fri.Spec

noncomputable abbrev ωT : SmoothCosetFftDomain 3 KC := smoothDomain 3 (by norm_num)
local notation "sT" => (fun _ : Fin (1 + 1) => (1 : ℕ+))

theorem toy_hs : (∑ j, ((sT j : ℕ+) : ℕ)) ≤ 3 := by simp

/-- the single query point `ω 5` -/
noncomputable def toyXs : Fin 1 → (ωT.subdomain 0).toFinset :=
  fun _ => (ωT.subdomain 0).equivToFinset ⟨5, by norm_num⟩

theorem toyXs_val (j : Fin 1) : (toyXs j).val = algebraMap (ZMod p) KC 7 * ((zeta 3 : KCˣ) : KC) ^ 5 := by
  show (ωT.subdomain 0) _ = _
  rw [CosetFftDomainClass.subdomain_0_apply, Inst.smoothDomain_apply]

theorem toy_mem : (5 : Fin (2 ^ 3)) ∈ readSet sT 1 toy_hs toyXs := by
  refine ⟨⟨(toyXs 0).val, (toyXs 0).2⟩, ⟨0, Or.inr ?_⟩, ?_⟩
  · simp
  · symm
    rw [Equiv.symm_apply_eq]
    ext
    show (toyXs 0).val = ωT 5
    rw [Inst.smoothDomain_apply, toyXs_val]
    rfl

/-- `readSet_idx` on the toy: the residue of the read point `5` is `1 = 5 % 4` -/
theorem toy_idx : ∃ j : Fin 1, (5 : Fin (2 ^ 3)).val % 2 ^ (3 - 1) = (fun _ => 5) j % 2 ^ (3 - 1) :=
  readSet_idx (ω := ωT) sT 1 (by norm_num) rfl (by norm_num) (fun _ => rfl) toy_hs toyXs (fun _ => 5)
    toyXs_val 5 toy_mem

example : (5 : Fin (2 ^ 3)).val % 2 ^ (3 - 1) = 1 := by decide

end Toy

end Read

#print axioms sub_idx_sq
#print axioms sub_idx_eq
#print axioms readSet_idx
#print axioms readPts_idx
#print axioms toy_idx

end NockvmE2E.Exec.DomIdx
