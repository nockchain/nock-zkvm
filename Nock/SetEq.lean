/-
  Nock/SetEq.lean

  The set-equality / log-derivative algebra of paper §2.1: the
  foundation of the IO linking between the compute and memory tables.  This is pure
  finite-field / field-of-fractions algebra, independent of Nock/nouns.

  We work over a field `L` playing the role of `𝔽(Y)` — the field of fractions of the
  multilinear polynomials over `𝔽` in the RLC variable(s) `Y`.  Since `𝔽(Y)` has the same
  characteristic as `𝔽`, the paper's hypothesis "char `p > n`" becomes `[CharP L p]` with
  `n < p`.  The one-variable rational function field `𝔽(X,Y) = L(X)` is `RatFunc L`, and
  `1/(X + aᵢ)` is `frac aᵢ = (algebraMap L[X] (RatFunc L) (X + C aᵢ))⁻¹`.

  Core fact (`sum_frac_eq_zero_iff`).  For a `Finset L` of *distinct* poles `P`
  and coefficients `ρ : L → L`, `∑_{c∈P} ρ c · 1/(X+c) = 0` in `RatFunc L` iff every
  `ρ c = 0`.  This is the partial-fraction / linear-independence statement (distinct
  simple denominators have unique residues).  Proof: clear denominators by multiplying by
  `∏_{c∈P}(X+c)` (`RatFunc.algebraMap_injective`), reducing to a polynomial identity
  `∑_c C(ρ c)·∏_{d≠c}(X+d) = 0`, then evaluate at `X = -c₀` to isolate `ρ c₀`.

  Results:
  * `ldse_mse` — product-eq ⇔ sum-of-inverses-eq (LogUp identity).
  * `set_inclusion` — the core: log-derivative multiplicity decomposition.
  * `mse_ldse_equiv` — the conditions `MSEcond` and `LDSEcond` (the defining equations of the languages
    `L_MSE` and `L_LDSE`) coincide.
-/
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

open Polynomial BigOperators
open scoped Classical

namespace Nock
namespace SetEq

variable {L : Type*} [Field L]

/-- `1/(X + c)` in the rational function field `L(X) = RatFunc L`. -/
noncomputable def frac (c : L) : RatFunc L :=
  (algebraMap (Polynomial L) (RatFunc L) (Polynomial.X + Polynomial.C c))⁻¹

/-- `X + C c` is nonzero (it is monic of degree 1). -/
theorem poleP_ne_zero (c : L) : (Polynomial.X + Polynomial.C c) ≠ 0 :=
  (Polynomial.monic_X_add_C c).ne_zero

/-- Its image in `RatFunc L` is nonzero. -/
theorem algebraMap_poleP_ne_zero (c : L) :
    algebraMap (Polynomial L) (RatFunc L) (Polynomial.X + Polynomial.C c) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective L)]
  exact poleP_ne_zero c

/-- `r • frac c = (X + C c)⁻¹ · C r`, rewriting the `L`-scalar action as multiplication by
    the image of the constant polynomial `C r`. -/
theorem smul_frac (r : L) (c : L) :
    r • frac c = algebraMap (Polynomial L) (RatFunc L) (Polynomial.C r) * frac c := by
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply L (Polynomial L) (RatFunc L),
    Polynomial.algebraMap_eq]

/-- **Partial-fraction linear independence (core).**  For distinct poles `P : Finset L`
    and residues `ρ : L → L`, the log-derivative sum `∑_{c∈P} ρ c / (X+c)` vanishes in
    `RatFunc L` iff every residue is zero. -/
theorem sum_frac_eq_zero_iff (P : Finset L) (ρ : L → L) :
    (∑ c ∈ P, ρ c • frac c) = 0 ↔ ∀ c ∈ P, ρ c = 0 := by
  classical
  set A := algebraMap (Polynomial L) (RatFunc L) with hA
  -- The cleared-denominator numerator polynomial.
  set N : Polynomial L :=
    ∑ c ∈ P, Polynomial.C (ρ c) * ∏ d ∈ P.erase c, (Polynomial.X + Polynomial.C d) with hN
  -- Multiplying the sum by `∏_{c∈P}(X+c)` gives `A N`.
  have key : A (∏ c ∈ P, (Polynomial.X + Polynomial.C c)) * (∑ c ∈ P, ρ c • frac c) = A N := by
    rw [Finset.mul_sum, hN, map_sum]
    apply Finset.sum_congr rfl
    intro c hc
    have hsplit :
        (∏ d ∈ P, (Polynomial.X + Polynomial.C d))
          = (Polynomial.X + Polynomial.C c) * ∏ d ∈ P.erase c, (Polynomial.X + Polynomial.C d) :=
      (Finset.mul_prod_erase P (fun d => (Polynomial.X + Polynomial.C d)) hc).symm
    rw [smul_frac, frac, hsplit, map_mul]
    rw [show A (Polynomial.X + Polynomial.C c)
            * A (∏ d ∈ P.erase c, (Polynomial.X + Polynomial.C d))
            * ((A (Polynomial.C (ρ c))) * (A (Polynomial.X + Polynomial.C c))⁻¹)
          = A (Polynomial.C (ρ c))
            * A (∏ d ∈ P.erase c, (Polynomial.X + Polynomial.C d))
            * (A (Polynomial.X + Polynomial.C c) * (A (Polynomial.X + Polynomial.C c))⁻¹)
        by ring]
    rw [mul_inv_cancel₀ (algebraMap_poleP_ne_zero c), mul_one, ← map_mul]
  -- Transfer: sum = 0 ↔ A N = 0 ↔ N = 0.
  have hPp : A (∏ c ∈ P, (Polynomial.X + Polynomial.C c)) ≠ 0 := by
    rw [Ne, ← map_zero A, (RatFunc.algebraMap_injective L).eq_iff]
    exact Finset.prod_ne_zero_iff.mpr (fun c _ => poleP_ne_zero c)
  have hsum_iff : (∑ c ∈ P, ρ c • frac c) = 0 ↔ N = 0 := by
    constructor
    · intro h
      have : A N = 0 := by rw [← key, h, mul_zero]
      rwa [← map_zero A, (RatFunc.algebraMap_injective L).eq_iff] at this
    · intro h
      have hAN : A N = 0 := by rw [h, map_zero]
      have := key.trans hAN
      exact (mul_eq_zero.mp this).resolve_left hPp
  rw [hsum_iff]
  -- N = 0 ↔ all residues 0, by evaluating at X = -c₀.
  constructor
  · intro hNzero c₀ hc₀
    have heval : N.eval (-c₀) = 0 := by rw [hNzero]; simp
    rw [hN, Polynomial.eval_finsetSum] at heval
    -- Only the c = c₀ term survives.
    have hterm : ∀ c ∈ P, c ≠ c₀ →
        (Polynomial.C (ρ c) * ∏ d ∈ P.erase c, (Polynomial.X + Polynomial.C d)).eval (-c₀) = 0 := by
      intro c hc hcne
      rw [Polynomial.eval_mul, Polynomial.eval_prod]
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (i := c₀)
      · exact Finset.mem_erase.mpr ⟨(Ne.symm hcne), hc₀⟩
      · simp
    rw [Finset.sum_eq_single c₀ hterm (fun h => absurd hc₀ h)] at heval
    rw [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_C] at heval
    have hprod_ne : (∏ d ∈ P.erase c₀, (Polynomial.X + Polynomial.C d).eval (-c₀)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro d hd
      have hdne : d ≠ c₀ := (Finset.mem_erase.mp hd).1
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      rw [add_comm, ← sub_eq_add_neg]
      exact sub_ne_zero.mpr hdne
    exact (mul_eq_zero.mp heval).resolve_right hprod_ne
  · intro h
    rw [hN]
    apply Finset.sum_eq_zero
    intro c hc
    rw [h c hc, map_zero, zero_mul]

/-- **Grouping.**  A log-derivative sum `∑ i, μ i · 1/(X + a i)` regrouped over any finset
    `P` of poles containing the image of `a`: the coefficient at pole `c` is the sum of the
    `μ i` over the fiber `a⁻¹(c)` (and `0` for poles not hit). -/
theorem frac_sum_eq_sum_image {ι : Type*} [Fintype ι]
    (a : ι → L) (μ : ι → L) (P : Finset L) (hsub : Finset.univ.image a ⊆ P) :
    (∑ i, μ i • frac (a i))
      = ∑ c ∈ P, (∑ i ∈ Finset.univ.filter (fun i => a i = c), μ i) • frac c := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := P) (g := a)
        (fun i _ => hsub (Finset.mem_image_of_mem a (Finset.mem_univ i)))
        (fun i => μ i • frac (a i))]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- **Coefficient comparison.**  Two log-derivative sums are equal in `RatFunc L` iff, at
    every pole `c` in the combined support, the fiber-summed coefficients agree.  Immediate
    from grouping + the partial-fraction core `sum_frac_eq_zero_iff`. -/
theorem frac_eq_iff_coeff {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (a : ι₁ → L) (μ₁ : ι₁ → L) (b : ι₂ → L) (μ₂ : ι₂ → L) :
    (∑ i, μ₁ i • frac (a i) = ∑ j, μ₂ j • frac (b j))
    ↔ ∀ c ∈ (Finset.univ.image a ∪ Finset.univ.image b),
         (∑ i ∈ Finset.univ.filter (fun i => a i = c), μ₁ i)
           = (∑ j ∈ Finset.univ.filter (fun j => b j = c), μ₂ j) := by
  set P := Finset.univ.image a ∪ Finset.univ.image b with hP
  have ha : Finset.univ.image a ⊆ P := Finset.subset_union_left
  have hb : Finset.univ.image b ⊆ P := Finset.subset_union_right
  rw [frac_sum_eq_sum_image a μ₁ P ha, frac_sum_eq_sum_image b μ₂ P hb, ← sub_eq_zero,
    ← Finset.sum_sub_distrib]
  have hrw : (∑ c ∈ P, ((∑ i ∈ Finset.univ.filter (fun i => a i = c), μ₁ i) • frac c
            - (∑ j ∈ Finset.univ.filter (fun j => b j = c), μ₂ j) • frac c))
        = ∑ c ∈ P, ((∑ i ∈ Finset.univ.filter (fun i => a i = c), μ₁ i)
            - (∑ j ∈ Finset.univ.filter (fun j => b j = c), μ₂ j)) • frac c := by
    apply Finset.sum_congr rfl; intro c _; rw [sub_smul]
  rw [hrw, sum_frac_eq_zero_iff]
  refine forall_congr' (fun c => imp_congr_right (fun _ => ?_))
  rw [sub_eq_zero]

/-- Nat casts are injective below the characteristic: if `x, y < p` and `(x : L) = (y : L)`
    in a field of characteristic `p`, then `x = y`. -/
theorem natCast_inj_of_lt {p : ℕ} [CharP L p] {x y : ℕ} (hx : x < p) (hy : y < p)
    (h : (x : L) = (y : L)) : x = y := by
  wlog hle : y ≤ x generalizing x y
  · exact (this hy hx h.symm (le_of_lt (not_le.mp hle))).symm
  have hz : ((x - y : ℕ) : L) = 0 := by rw [Nat.cast_sub hle, h, sub_self]
  rw [CharP.cast_eq_zero_iff L p] at hz
  have hlt : x - y < p := lt_of_le_of_lt (Nat.sub_le x y) hx
  have : x - y = 0 := Nat.eq_zero_of_dvd_of_lt hz hlt
  omega

/-- The multiset of values of a finite family. -/
noncomputable def valMultiset {ι : Type*} [Fintype ι] (a : ι → L) : Multiset L :=
  Finset.univ.val.map a

/-- The fiber-cardinality coefficient (with `μ = 1`) is the multiplicity of `c` in the
    value multiset. -/
theorem sum_one_filter_eq_count {ι : Type*} [Fintype ι] (a : ι → L) (c : L) :
    (∑ _i ∈ Finset.univ.filter (fun i => a i = c), (1 : L))
      = ((Multiset.count c (valMultiset a) : ℕ) : L) := by
  have hc : (Finset.univ.filter (fun i => a i = c)).card = Multiset.count c (valMultiset a) := by
    rw [valMultiset, Multiset.count_map,
      Finset.filter_congr (fun x _ => (eq_comm : (a x = c) ↔ (c = a x)))]
    rfl
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, hc]

/-- `∏ i, (X + C (a i))` regrouped as a multiset product. -/
theorem prod_X_add_C_eq {ι : Type*} [Fintype ι] (a : ι → L) :
    (∏ i, (Polynomial.X + Polynomial.C (a i)))
      = ((valMultiset a).map (fun c => Polynomial.X + Polynomial.C c)).prod := by
  rw [valMultiset, Finset.prod_eq_multiset_prod, Multiset.map_map]
  rfl

/-- Roots of `∏(X + C aᵢ)` are the negated values (multiset). -/
theorem roots_prod_X_add_C {ι : Type*} [Fintype ι] (a : ι → L) :
    (∏ i, (Polynomial.X + Polynomial.C (a i))).roots
      = (valMultiset a).map (fun c => -c) := by
  rw [prod_X_add_C_eq]
  have hmap : ((valMultiset a).map (fun c => Polynomial.X + Polynomial.C c))
      = (((valMultiset a).map (fun c => -c)).map (fun d => Polynomial.X - Polynomial.C d)) := by
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro c _
    simp [sub_eq_add_neg]
  rw [hmap, Polynomial.roots_multiset_prod_X_sub_C]

/-- **Product ⇔ multiset.**  `∏(X + C aᵢ) = ∏(X + C bᵢ)` iff the value multisets coincide.
    (Unique factorization: read off via `roots`, using `X + C c = X - C (-c)`.) -/
theorem prod_X_add_C_eq_iff {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (a : ι₁ → L) (b : ι₂ → L) :
    (∏ i, (Polynomial.X + Polynomial.C (a i)) = ∏ j, (Polynomial.X + Polynomial.C (b j)))
      ↔ valMultiset a = valMultiset b := by
  constructor
  · intro h
    have hr := congrArg Polynomial.roots h
    rw [roots_prod_X_add_C a, roots_prod_X_add_C b] at hr
    exact Multiset.map_injective neg_injective hr
  · intro h
    rw [prod_X_add_C_eq, prod_X_add_C_eq, h]

/-- **`Lem:ldse_mse`, general form.**  For families `{aᵢ}` (length `n₁`) and
    `{bⱼ}` (length `n₂`) over a field `L` of characteristic `p > n₁, n₂`, the multiplicative
    set equality `∏(X+aᵢ) = ∏(X+bⱼ)` in `L[X]` is equivalent to the log-derivative set
    equality `Σ 1/(X+aᵢ) = Σ 1/(X+bⱼ)` in `L(X) = RatFunc L`.  Stated for possibly-unequal
    lengths: equality of either side already forces the multisets of roots to coincide (hence
    `n₁ = n₂`).  This is the standard LogUp identity. -/
theorem mse_ldse_general {p : ℕ} [CharP L p] {n₁ n₂ : ℕ} (hn₁ : n₁ < p) (hn₂ : n₂ < p)
    (a : Fin n₁ → L) (b : Fin n₂ → L) :
    (∏ i, (Polynomial.X + Polynomial.C (a i)) = ∏ j, (Polynomial.X + Polynomial.C (b j)))
      ↔ (∑ i, frac (a i) = ∑ j, frac (b j)) := by
  rw [prod_X_add_C_eq_iff a b]
  -- Sum side ↔ coefficient (count) equality (in L).
  have hsum : (∑ i, frac (a i) = ∑ j, frac (b j))
      ↔ ∀ c ∈ (Finset.univ.image a ∪ Finset.univ.image b),
           ((Multiset.count c (valMultiset a) : ℕ) : L)
             = ((Multiset.count c (valMultiset b) : ℕ) : L) := by
    have h1 : (∑ i, frac (a i)) = ∑ i, (1 : L) • frac (a i) := by simp
    have h2 : (∑ j, frac (b j)) = ∑ j, (1 : L) • frac (b j) := by simp
    rw [h1, h2, frac_eq_iff_coeff]
    refine forall_congr' (fun c => imp_congr_right (fun _ => ?_))
    rw [sum_one_filter_eq_count, sum_one_filter_eq_count]
  rw [hsum, Multiset.ext]
  constructor
  · intro h c _
    rw [h c]
  · intro h c
    by_cases hc : c ∈ (Finset.univ.image a ∪ Finset.univ.image b)
    · have hca : Multiset.count c (valMultiset a) < p :=
        lt_of_le_of_lt (Multiset.count_le_card _ _)
          (by rw [valMultiset, Multiset.card_map]; simpa using hn₁)
      have hcb : Multiset.count c (valMultiset b) < p :=
        lt_of_le_of_lt (Multiset.count_le_card _ _)
          (by rw [valMultiset, Multiset.card_map]; simpa using hn₂)
      exact natCast_inj_of_lt hca hcb (h c hc)
    · rw [Finset.mem_union, not_or] at hc
      have hca : Multiset.count c (valMultiset a) = 0 := by
        rw [Multiset.count_eq_zero, valMultiset]
        intro hmem
        obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
        exact hc.1 (by rw [← hi]; exact Finset.mem_image_of_mem a (Finset.mem_univ i))
      have hcb : Multiset.count c (valMultiset b) = 0 := by
        rw [Multiset.count_eq_zero, valMultiset]
        intro hmem
        obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
        exact hc.2 (by rw [← hi]; exact Finset.mem_image_of_mem b (Finset.mem_univ i))
      rw [hca, hcb]

/-- **`Lem:ldse_mse`, as stated in the paper ** (equal length `n`). -/
theorem ldse_mse {p : ℕ} [CharP L p] {n : ℕ} (hn : n < p) (a b : Fin n → L) :
    (∏ i, (Polynomial.X + Polynomial.C (a i)) = ∏ i, (Polynomial.X + Polynomial.C (b i)))
      ↔ (∑ i, frac (a i) = ∑ i, frac (b i)) :=
  mse_ldse_general hn hn a b


/-! ### The core inclusion lemma -/

/-- The prime-subfield embedding `𝔽_p = ZMod p ↪ L` (exists since `char L = p`).  This
    realizes the paper's "multiplicities `mᵢ ∈ 𝔽_p ⊆ 𝔽`". -/
noncomputable def castZ (p : ℕ) [CharP L p] : ZMod p →+* L := ZMod.castHom (dvd_refl p) L

/-- `c` is a value of `a` iff its multiplicity is positive. -/
theorem mem_image_iff_count_pos {ι : Type*} [Fintype ι] (a : ι → L) (c : L) :
    c ∈ Finset.univ.image a ↔ 0 < Multiset.count c (valMultiset a) := by
  rw [Multiset.count_pos, valMultiset, Multiset.mem_map, Finset.mem_image]
  simp

/-- The fiber cardinality equals the multiplicity in the value multiset. -/
theorem filter_card_eq_count {ι : Type*} [Fintype ι] (a : ι → L) (c : L) :
    (Finset.univ.filter (fun i => a i = c)).card = Multiset.count c (valMultiset a) := by
  rw [valMultiset, Multiset.count_map,
    Finset.filter_congr (fun x _ => (eq_comm : (a x = c) ↔ (c = a x)))]
  rfl

/-- The value multiset of a family has cardinality equal to the index type. -/
theorem card_valMultiset {ι : Type*} [Fintype ι] (a : ι → L) :
    Multiset.card (valMultiset a) = Fintype.card ι := by
  rw [valMultiset, Multiset.card_map]
  exact Finset.card_univ

/-- Below the characteristic, a nat cast into `ZMod p` is nonzero iff the nat is positive. -/
theorem zmod_natCast_ne_zero_iff {p k : ℕ} (hkp : k < p) : (k : ZMod p) ≠ 0 ↔ 0 < k := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact absurd (h0 ▸ dvd_zero p) h
    · exact h0
  · intro hpos hdvd
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hkp)

/-- Below the characteristic, a positive nat cast into `L` is nonzero. -/
theorem Lcast_ne_zero {p : ℕ} [CharP L p] {k : ℕ} (hk : 0 < k) (hkp : k < p) :
    (k : L) ≠ 0 := by
  intro h
  have hk0 : k = 0 :=
    natCast_inj_of_lt hkp (by omega) (by rw [h, Nat.cast_zero])
  omega

/-- The prime-subfield embedding is injective. -/
theorem castZ_injective (p : ℕ) [CharP L p] :
    Function.Injective (castZ p : ZMod p →+* L) :=
  ZMod.castHom_injective L

/-- **Construction of multiplicities from an inclusion.**  If `S ⊆ T` then there is a
    multiplicity vector `m ∈ 𝔽_p^{n₂}` realizing the log-derivative equation, and `m j ≠ 0`
    exactly for the responses `b j` that lie in `S`.  (Distribute each `S`-residue over its
    `T`-fiber as `count_a / count_b`, cancelling the fiber size.) -/
theorem exists_m_of_subset {p : ℕ} [CharP L p] {n₁ n₂ : ℕ} (hn₁ : n₁ < p) (hn₂ : n₂ < p)
    (a : Fin n₁ → L) (b : Fin n₂ → L)
    (hST : Finset.univ.image a ⊆ Finset.univ.image b) :
    ∃ m : Fin n₂ → ZMod p,
      (∀ j, m j ≠ 0 ↔ b j ∈ Finset.univ.image a)
        ∧ (∑ i, frac (a i) = ∑ j, (castZ p (m j) : L) • frac (b j)) := by
  haveI : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero L (by omega)⟩
  refine ⟨fun j => (↑(Multiset.count (b j) (valMultiset a)) : ZMod p)
                     * (↑(Multiset.count (b j) (valMultiset b)) : ZMod p)⁻¹, ?_, ?_⟩
  · -- support: m j ≠ 0 ↔ b j ∈ S
    intro j
    dsimp only
    have hbj : b j ∈ Finset.univ.image b := Finset.mem_image_of_mem b (Finset.mem_univ j)
    have hβpos : 0 < Multiset.count (b j) (valMultiset b) := (mem_image_iff_count_pos b (b j)).mp hbj
    have hβlt : Multiset.count (b j) (valMultiset b) < p :=
      lt_of_le_of_lt (Multiset.count_le_card _ _) (by rw [card_valMultiset]; simpa using hn₂)
    have hαlt : Multiset.count (b j) (valMultiset a) < p :=
      lt_of_le_of_lt (Multiset.count_le_card _ _) (by rw [card_valMultiset]; simpa using hn₁)
    have hβne : (↑(Multiset.count (b j) (valMultiset b)) : ZMod p) ≠ 0 :=
      (zmod_natCast_ne_zero_iff hβlt).mpr hβpos
    constructor
    · intro hmne
      by_contra hmem
      apply hmne
      have hα0 : Multiset.count (b j) (valMultiset a) = 0 := by
        rw [Multiset.count_eq_zero]
        intro hh
        exact hmem ((mem_image_iff_count_pos a (b j)).mpr (Multiset.count_pos.mpr hh))
      rw [hα0, Nat.cast_zero, zero_mul]
    · intro hmem
      have hαpos : 0 < Multiset.count (b j) (valMultiset a) := (mem_image_iff_count_pos a (b j)).mp hmem
      exact mul_ne_zero ((zmod_natCast_ne_zero_iff hαlt).mpr hαpos) (inv_ne_zero hβne)
  · -- the equation, via coefficient comparison
    have h1 : (∑ i, frac (a i)) = ∑ i, (1 : L) • frac (a i) := by simp
    rw [h1, frac_eq_iff_coeff]
    intro c hc
    dsimp only
    have hcT : c ∈ Finset.univ.image b := by
      rw [Finset.mem_union] at hc; rcases hc with h | h; exacts [hST h, h]
    have hβpos : 0 < Multiset.count c (valMultiset b) := (mem_image_iff_count_pos b c).mp hcT
    have hβlt : Multiset.count c (valMultiset b) < p :=
      lt_of_le_of_lt (Multiset.count_le_card _ _) (by rw [card_valMultiset]; simpa using hn₂)
    have hβne : (↑(Multiset.count c (valMultiset b)) : ZMod p) ≠ 0 :=
      (zmod_natCast_ne_zero_iff hβlt).mpr hβpos
    rw [sum_one_filter_eq_count, ← map_sum]
    have hsumfib :
        (∑ j ∈ Finset.univ.filter (fun j => b j = c),
            ((↑(Multiset.count (b j) (valMultiset a)) : ZMod p)
              * (↑(Multiset.count (b j) (valMultiset b)) : ZMod p)⁻¹))
          = (↑(Multiset.count c (valMultiset a)) : ZMod p) := by
      rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]),
        Finset.sum_const, nsmul_eq_mul, filter_card_eq_count]
      rw [show (↑(Multiset.count c (valMultiset b)) : ZMod p)
              * ((↑(Multiset.count c (valMultiset a)) : ZMod p)
                * (↑(Multiset.count c (valMultiset b)) : ZMod p)⁻¹)
            = (↑(Multiset.count c (valMultiset a)) : ZMod p)
                * ((↑(Multiset.count c (valMultiset b)) : ZMod p)
                  * (↑(Multiset.count c (valMultiset b)) : ZMod p)⁻¹) by ring,
        mul_inv_cancel₀ hβne, mul_one]
    rw [hsumfib, map_natCast]

/-- **`lem:set_inclusion` — the core inclusion lemma.**  With `a : [n₁] → S`, `b : [n₂] → T`
    surjective onto their images (char `p > n₁, n₂`): `S ⊆ T` iff there is a multiplicity
    vector `m ∈ 𝔽_p^{n₂}` with `Σ 1/(X+aᵢ) = Σ mⱼ/(X+bⱼ)` in `L(X)`. -/
theorem set_inclusion {p : ℕ} [CharP L p] {n₁ n₂ : ℕ} (hn₁ : n₁ < p) (hn₂ : n₂ < p)
    (a : Fin n₁ → L) (b : Fin n₂ → L) :
    (Finset.univ.image a ⊆ Finset.univ.image b)
      ↔ ∃ m : Fin n₂ → ZMod p, (∑ i, frac (a i) = ∑ j, (castZ p (m j) : L) • frac (b j)) := by
  haveI : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero L (by omega)⟩
  constructor
  · intro hST
    obtain ⟨m, _, heq⟩ := exists_m_of_subset hn₁ hn₂ a b hST
    exact ⟨m, heq⟩
  · rintro ⟨m, heq⟩
    have heq' : (∑ i, (1 : L) • frac (a i)) = ∑ j, (castZ p (m j) : L) • frac (b j) := by
      simpa using heq
    have hco := (frac_eq_iff_coeff a (fun _ => (1 : L)) b (fun j => (castZ p (m j) : L))).mp heq'
    intro c hcS
    by_contra hcT
    have hmem : c ∈ (Finset.univ.image a ∪ Finset.univ.image b) := Finset.mem_union_left _ hcS
    have hcoeff := hco c hmem
    rw [sum_one_filter_eq_count] at hcoeff
    have hfilter : Finset.univ.filter (fun j => b j = c) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro j _ h
      exact hcT (h ▸ Finset.mem_image_of_mem b (Finset.mem_univ j))
    rw [hfilter, Finset.sum_empty] at hcoeff
    have hpos : 0 < Multiset.count c (valMultiset a) := (mem_image_iff_count_pos a c).mp hcS
    have hlt : Multiset.count c (valMultiset a) < p :=
      lt_of_le_of_lt (Multiset.count_le_card _ _) (by rw [card_valMultiset]; simpa using hn₁)
    exact Lcast_ne_zero hpos hlt hcoeff

/-- **`lem:set_inclusion` — the "moreover" clause.**  If `S = T`, the multiplicity vector
    can be chosen with every `mⱼ ≠ 0`. -/
theorem set_inclusion_eq {p : ℕ} [CharP L p] {n₁ n₂ : ℕ} (hn₁ : n₁ < p) (hn₂ : n₂ < p)
    (a : Fin n₁ → L) (b : Fin n₂ → L) (hST : Finset.univ.image a = Finset.univ.image b) :
    ∃ m : Fin n₂ → ZMod p, (∀ j, m j ≠ 0)
      ∧ (∑ i, frac (a i) = ∑ j, (castZ p (m j) : L) • frac (b j)) := by
  obtain ⟨m, hm, heq⟩ := exists_m_of_subset hn₁ hn₂ a b hST.le
  refine ⟨m, ?_, heq⟩
  intro j
  rw [hm j, hST]
  exact Finset.mem_image_of_mem b (Finset.mem_univ j)

/-- **`lem:set_inclusion` — the converse.**  If the responses `b` are distinct and every
    `mⱼ ≠ 0`, then the log-derivative equation forces `S = T`. -/
theorem set_inclusion_eq_of_injective {p : ℕ} [CharP L p] {n₁ n₂ : ℕ}
    (hn₁ : n₁ < p) (hn₂ : n₂ < p) (a : Fin n₁ → L) (b : Fin n₂ → L)
    (hbinj : Function.Injective b) (m : Fin n₂ → ZMod p) (hm : ∀ j, m j ≠ 0)
    (heq : ∑ i, frac (a i) = ∑ j, (castZ p (m j) : L) • frac (b j)) :
    Finset.univ.image a = Finset.univ.image b := by
  haveI : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero L (by omega)⟩
  have heq' : (∑ i, (1 : L) • frac (a i)) = ∑ j, (castZ p (m j) : L) • frac (b j) := by
    simpa using heq
  have hco := (frac_eq_iff_coeff a (fun _ => (1 : L)) b (fun j => (castZ p (m j) : L))).mp heq'
  apply Finset.Subset.antisymm
  · -- S ⊆ T
    intro c hcS
    by_contra hcT
    have hmem : c ∈ (Finset.univ.image a ∪ Finset.univ.image b) := Finset.mem_union_left _ hcS
    have hcoeff := hco c hmem
    rw [sum_one_filter_eq_count] at hcoeff
    have hfilter : Finset.univ.filter (fun j => b j = c) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro j _ h
      exact hcT (h ▸ Finset.mem_image_of_mem b (Finset.mem_univ j))
    rw [hfilter, Finset.sum_empty] at hcoeff
    have hpos : 0 < Multiset.count c (valMultiset a) := (mem_image_iff_count_pos a c).mp hcS
    have hlt : Multiset.count c (valMultiset a) < p :=
      lt_of_le_of_lt (Multiset.count_le_card _ _) (by rw [card_valMultiset]; simpa using hn₁)
    exact Lcast_ne_zero hpos hlt hcoeff
  · -- T ⊆ S
    intro c hcT
    by_contra hcS
    have hmem : c ∈ (Finset.univ.image a ∪ Finset.univ.image b) := Finset.mem_union_right _ hcT
    have hcoeff := hco c hmem
    rw [sum_one_filter_eq_count] at hcoeff
    have hcount0 : Multiset.count c (valMultiset a) = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem2
      exact hcS ((mem_image_iff_count_pos a c).mpr (Multiset.count_pos.mpr hmem2))
    rw [hcount0, Nat.cast_zero] at hcoeff
    obtain ⟨j₀, _, hj₀⟩ := Finset.mem_image.mp hcT
    have hfilter : Finset.univ.filter (fun j => b j = c) = {j₀} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj₀⟩
      · intro j hj
        exact hbinj ((Finset.mem_filter.mp hj).2.trans hj₀.symm)
    rw [hfilter, Finset.sum_singleton] at hcoeff
    exact hm j₀ ((map_eq_zero_iff (castZ p) (castZ_injective p)).mp hcoeff.symm)

/-! ### Languages and the MSE ≡ LDSE equivalence

  Here the base field `𝔽` has characteristic `p`; the RLC variable `Y` makes the working
  field `𝔽(Y) = RatFunc 𝔽`, and the log-derivative variable `X` sits on top, so the full
  field `𝔽(X,Y)` is `RatFunc (RatFunc 𝔽)`.  A memory record is a vector `𝔽^m` (`Fin m → 𝔽`)
  and a record sequence of length `k` is `Fin k → (Fin m → 𝔽)`. -/

section Languages

variable {𝔽 : Type*} [Field 𝔽] {p : ℕ} [CharP 𝔽 p]

/-- **`RLC^Y`.**  The random linear combination
    `RLC^Y(v) = Σ_{i=1}^{m} Y^{i-1} · v(i)`, landing in `𝔽(Y) = RatFunc 𝔽` (0-indexed here,
    so the exponent is `i`).  Realized as the image of the coefficient polynomial. -/
noncomputable def RLCpoly {m : ℕ} (v : Fin m → 𝔽) : Polynomial 𝔽 :=
  ∑ i : Fin m, Polynomial.C (v i) * Polynomial.X ^ (i : ℕ)

/-- `RLC^Y(v) ∈ 𝔽(Y)`. -/
noncomputable def RLC {m : ℕ} (v : Fin m → 𝔽) : RatFunc 𝔽 :=
  algebraMap (Polynomial 𝔽) (RatFunc 𝔽) (RLCpoly v)

/-- **RLC is injective**: distinct records give distinct random linear combinations (the
    variable `Y` is symbolic, so `RLC` just repackages the coefficient vector). -/
theorem RLC_injective {m : ℕ} : Function.Injective (RLC (𝔽 := 𝔽) (m := m)) := by
  have hpoly : Function.Injective (RLCpoly (𝔽 := 𝔽) (m := m)) := by
    intro v w h
    funext j
    have hc := congrArg (fun q => Polynomial.coeff q (j : ℕ)) h
    simpa [RLCpoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Finset.sum_ite_eq', Fin.val_eq_val] using hc
  exact fun v w h => hpoly ((RatFunc.algebraMap_injective 𝔽) h)

/-- The defining condition of `L_MSE^{Y,K}(𝔽)` for record sequences of the
    given dimensions: `∏(RLC(reqᵢ)+X) = ∏(RLC(respⱼ)+X)` in `𝔽(Y)[X]`. -/
def MSEcond {k₁ k₂ m : ℕ} (req : Fin k₁ → Fin m → 𝔽) (resp : Fin k₂ → Fin m → 𝔽) : Prop :=
  (∏ i, (Polynomial.X + Polynomial.C (RLC (req i))))
    = ∏ j, (Polynomial.X + Polynomial.C (RLC (resp j)))

/-- The defining condition of `L_LDSE^{Y,K}(𝔽)`: the log-derivative set
    equality `Σ 1/(RLC(reqᵢ)+X) = Σ 1/(RLC(respⱼ)+X)` in `𝔽(X,Y)`. -/
def LDSEcond {k₁ k₂ m : ℕ} (req : Fin k₁ → Fin m → 𝔽) (resp : Fin k₂ → Fin m → 𝔽) : Prop :=
  (∑ i, frac (RLC (req i))) = ∑ j, frac (RLC (resp j))

/-- **`Lem:mse_ldse_equiv`.**  When `char 𝔽 = p > K ≥ k₁, k₂`, the
    multiplicative and log-derivative set-equality conditions coincide, so `L_MSE ≡ L_LDSE`.
    (The shared membership constraint `k₁, k₂, m ∈ [K]` is the same for both languages;
    this lemma is the equivalence of their defining equations, via `mse_ldse_general`.) -/
theorem mse_ldse_equiv {k₁ k₂ m : ℕ} (hk₁ : k₁ < p) (hk₂ : k₂ < p)
    (req : Fin k₁ → Fin m → 𝔽) (resp : Fin k₂ → Fin m → 𝔽) :
    MSEcond req resp ↔ LDSEcond req resp :=
  mse_ldse_general hk₁ hk₂ (fun i => RLC (req i)) (fun j => RLC (resp j))

end Languages

end SetEq
end Nock
