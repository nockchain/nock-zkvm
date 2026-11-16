/-
the DEEP data of an abstract J-8 interface `J : RapAirJ B K`.
`DeepParams` / `AirShape` over base-field word traces `Fin (2^n) → B`, the coins `K`, on the extended frame
`extFrame J.Φ0 2`:
  * `decB`/`tp`: the base-field reading of a word (the `B`-polynomial behind FRI's unique decoding, `udDecode_base`);
  * `PubRead` (PROPOSED interface fields): public columns, their fixed opening points, the message read from them;
  * `deepParamsJ`: `Cp` = the composed constraints at the decoded base trace (`J.compose`, `pread`), `hC` from `J.hdeg`;
  * `airJ`: `Cv` (evaluation of `J.C` at the opened values, preprocessed columns read as their fixed polynomial);
  * `hlink`, `hRest` (links to `J.acc_of`, `J.Pub`, `J.StmtOK`).
-/
import NockvmE2E.J8.Input
import NockvmE2E.Succ.BaseWords
import NockvmE2E.Succ.Deep
import NockvmE2E.Deep.UDLink

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial NockvmE2E.Rap NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriDeep NockvmE2E.Succ.BaseWords
  Fri.Spec Domain
open scoped NNReal

namespace NockvmE2E.J8

/-! ## 1. Degree of a composition -/

section Degree

variable {B : Type} [Field B] {σ : Type}

/-- `natDegree (aeval f q) ≤ totalDegree q · D` when every `f i` has `natDegree ≤ D`. -/
theorem natDegree_aeval_le (q : MvPolynomial σ B) (f : σ → B[X]) (D : ℕ) (hf : ∀ i, (f i).natDegree ≤ D) :
    (MvPolynomial.aeval f q).natDegree ≤ q.totalDegree * D := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine natDegree_sum_le_of_forall_le _ _ (fun m hm => ?_)
  refine (natDegree_mul_le).trans ?_
  have h1 : (algebraMap B B[X] (q.coeff m)).natDegree = 0 := by
    rw [Polynomial.algebraMap_apply]; simp
  rw [h1, zero_add]
  refine (natDegree_prod_le _ _).trans ?_
  have h2 : ∀ i ∈ m.support, ((f i) ^ m i).natDegree ≤ m i * D := fun i _ =>
    (natDegree_pow_le).trans (Nat.mul_le_mul_left _ (hf i))
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.sum_mul]
  exact Nat.mul_le_mul_right _ (MvPolynomial.le_totalDegree hm)

end Degree

/-! ## 1b. The vanishing factor `Z_{H∖H_t}` (union domain) -/

section Zout

variable {B : Type} [Field B] [DecidableEq B]

/-- `Z_{H∖H_t}`. -/
noncomputable def Zout (H Ht : Finset B) : B[X] := ∏ h ∈ H \ Ht, (Polynomial.X - Polynomial.C h)

theorem eval_Zout_ne (H Ht : Finset B) {x : B} (hx : x ∈ Ht) : eval x (Zout H Ht) ≠ 0 := by
  simp only [Zout, eval_prod, eval_sub, eval_X, eval_C]
  refine Finset.prod_ne_zero_iff.mpr (fun h hh => sub_ne_zero.mpr ?_)
  rintro rfl
  exact (Finset.mem_sdiff.mp hh).2 hx

theorem eval_Zout_eq_zero (H Ht : Finset B) {x : B} (hx : x ∈ H \ Ht) : eval x (Zout H Ht) = 0 := by
  simp only [Zout, eval_prod]
  exact Finset.prod_eq_zero hx (by simp)

theorem Zout_natDegree (H Ht : Finset B) : (Zout H Ht).natDegree = (H \ Ht).card := by
  simp [Zout]

/-- (U1+U2) the product vanishes on `H` iff the factor vanishes on `H_t` (for `H_t ⊆ H`). -/
theorem vanish_iff (H Ht : Finset B) (hsub : Ht ⊆ H) (c : B[X]) :
    (∀ x ∈ H, eval x (c * Zout H Ht) = 0) ↔ ∀ x ∈ Ht, eval x c = 0 := by
  constructor
  · intro h x hx
    have := h x (hsub hx)
    rw [eval_mul] at this
    exact (mul_eq_zero.mp this).resolve_right (eval_Zout_ne H Ht hx)
  · intro h x hx
    rw [eval_mul]
    by_cases hxt : x ∈ Ht
    · rw [h x hxt, zero_mul]
    · rw [eval_Zout_eq_zero H Ht (Finset.mem_sdiff.mpr ⟨hx, hxt⟩), mul_zero]

theorem Zout_self (H : Finset B) : Zout H H = 1 := by simp [Zout]

/-- (U3) degree: `deg c ≤ d|H|` ⇒ `deg (c · Zout) ≤ (3(d-1)+1)|H|` when `2 ≤ d` or `Ht = H`. -/
theorem deg_le (H Ht : Finset B) (c : B[X]) (d : ℕ) (hd : 2 ≤ d ∨ Ht = H) (hc : c.natDegree ≤ d * H.card) :
    (c * Zout H Ht).natDegree ≤ (3 * (d - 1) + 1) * H.card := by
  rcases hd with hd | rfl
  · refine natDegree_mul_le.trans ?_
    rw [Zout_natDegree]
    have h1 : (H \ Ht).card ≤ H.card := Finset.card_le_card Finset.sdiff_subset
    have h2 : d * H.card + H.card ≤ (3 * (d - 1) + 1) * H.card := by
      have : d + 1 ≤ 3 * (d - 1) + 1 := by omega
      nlinarith
    omega
  · rw [Zout_self, mul_one]
    exact hc.trans (Nat.mul_le_mul_right _ (by omega))

end Zout

/-! ## 2. The base-field reading of a word -/

section Words

variable {B K : Type} [Field B] [Fintype B] [DecidableEq B] [NonBinaryField K] [Fintype K] [DecidableEq K]
  [Algebra B K] {n : ℕ}

open Classical in
/-- The `B`-polynomial whose image is FRI's decoding of the lifted word (`0` if there is none). -/
noncomputable def decB (ω : SmoothCosetFftDomain n K) (δ : ℝ≥0) (N : ℕ) (w : Fin (2 ^ n) → B) : B[X] :=
  if h : ∃ q : B[X], udDecodeB ω δ N w = q.map (algebraMap B K) then h.choose else 0

/-- The word polynomial in `K[X]` (`DeepParams.toPoly`). -/
noncomputable def tp (ω : SmoothCosetFftDomain n K) (δ : ℝ≥0) (N : ℕ) (w : Fin (2 ^ n) → B) : K[X] :=
  (decB ω δ N w).map (algebraMap B K)

theorem tp_eq (ω : SmoothCosetFftDomain n K) {δ : ℝ≥0} {N : ℕ}
    (hω : ∀ i, domEmb ω i ∈ Set.range (algebraMap B K)) (hN : N + 1 ≤ 2 ^ n)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb ω) (N + 1) : Set (Fin (2 ^ n) → K))) :
    tp (B := B) ω δ N = udDecodeB ω δ N := by
  funext w
  have h : ∃ q : B[X], udDecodeB ω δ N w = q.map (algebraMap B K) := by
    obtain ⟨q, hq⟩ := udDecode_base (B := B) hω hN hδ w
    exact ⟨q, hq⟩
  simp only [tp, decB, dif_pos h]
  exact h.choose_spec.symm

theorem decB_natDegree_le (ω : SmoothCosetFftDomain n K) (δ : ℝ≥0) {N D : ℕ} (hND : N ≤ D)
    (w : Fin (2 ^ n) → B) : (decB ω δ N w).natDegree ≤ D := by
  by_cases h : ∃ q : B[X], udDecodeB ω δ N w = q.map (algebraMap B K)
  · have h1 := h.choose_spec
    have h2 := udDecode_natDegree_lt (ω := ω) δ N (liftW w)
    have h3 : (decB ω δ N w).natDegree = (udDecodeB ω δ N w).natDegree := by
      have h4 := congrArg natDegree h1
      rw [natDegree_map] at h4
      rw [decB, dif_pos h]
      exact h4.symm
    rw [h3]
    have : (udDecodeB ω δ N w).natDegree < N + 1 := h2
    omega
  · simp [decB, h]

end Words

/-! ## 3. Public columns, the word map, the DEEP data -/

section Kit

variable {B K : Type} [Field B] [Fintype B] [DecidableEq B] [NonBinaryField K] [Fintype K] [DecidableEq K]
  [Algebra B K] {n : ℕ}

/-- **PROPOSED interface fields** (not in `RapAirJ`): the public columns (opened at fixed off-domain points `ppt`,
the same for every offset), and the public message `rd` read from their values. The constraints `C` read the
public message only through `rd` (`hCpub`: no public-column variable occurs in `C`). -/
structure PubRead (J : RapAirJ B K) where
  pub : J.ι0 → Bool
  ppt : J.ι0 → K
  rd : (J.ι0 → K) → J.Msg
  /-- A generator of `K` over `B` (`[K:B] = 3`): the quotient-chunk basis is `gen^0, gen^1, gen^2`. -/
  gen : K
  hrd : ∀ v v' : J.ι0 → K, (∀ c, pub c = true → v c = v' c) → rd v = rd v'
  hCpub : ∀ χ M i, ∀ p ∈ (J.C χ M i).vars, pub p.1 = false

variable (J : RapAirJ B K) (pr : PubRead J) (ω : SmoothCosetFftDomain n K) (δ : ℝ≥0) (N : ℕ)

/-- The word layout of the interface: column `j` is word column `j`; a preprocessed column reads as its fixed
polynomial, every other one as `decB`. -/
noncomputable def wmJ : WordMap J J.colRound0 (Fin (2 ^ n) → B) where
  col := id
  hcol := fun _ => rfl
  hround := J.hround
  dec j w := match J.pre j with
    | some c => c
    | none => decB ω δ N w
  hpre j c h w := by simp only [h]

/-- The public message read off a word trace (the round-2 public columns at their fixed points). -/
noncomputable def preadJ (tr : Tr J.ι0 (Fin (2 ^ n) → B)) : J.Msg :=
  pr.rd (fun c => eval (pr.ppt c) (tp ω δ N (tr c)))

/-- The trace domain inside `K`. -/
noncomputable def HK : Finset K := J.H.map ⟨algebraMap B K, (algebraMap B K).injective⟩

theorem card_HK : (HK J).card = J.H.card := Finset.card_map _

theorem mem_HK {x : K} : x ∈ HK J ↔ ∃ x0 ∈ J.H, algebraMap B K x0 = x := by
  simp [HK]

/-- The degree of a decoded base column. -/
theorem base_natDegree_le {N : ℕ} (hNH : N ≤ J.H.card)
    (hpd : ∀ j c, J.pre j = some c → c.natDegree ≤ J.H.card) (tr : Tr J.ι0 (Fin (2 ^ n) → B)) (j : J.ι0) :
    ((wmJ J ω δ N).base tr j).natDegree ≤ J.H.card := by
  show (match J.pre j with | some c => c | none => decB ω δ N (tr j)).natDegree ≤ _
  cases hj : J.pre j with
  | some c => exact hpd j c hj
  | none => exact decB_natDegree_le ω δ hNH _

theorem natDegree_shift_le (q : B[X]) (o : B) :
    (q.comp (Polynomial.C o * Polynomial.X)).natDegree ≤ q.natDegree := by
  refine natDegree_comp_le.trans ?_
  have : (Polynomial.C o * Polynomial.X : B[X]).natDegree ≤ 1 :=
    natDegree_mul_le.trans (by simp)
  nlinarith

theorem compose_natDegree_le {N : ℕ} (hNH : N ≤ J.H.card)
    (hpd : ∀ j c, J.pre j = some c → c.natDegree ≤ J.H.card) (χ : Coins J.Φ0 K) (M : J.Msg)
    (tr : Tr J.ι0 (Fin (2 ^ n) → B)) (i : Fin J.ns) :
    (J.compose χ M ((wmJ J ω δ N).base tr) i).natDegree ≤ J.d * J.H.card := by
  have h := natDegree_aeval_le (J.C χ M i)
    (fun p : J.ι0 × Fin J.r => ((wmJ J ω δ N).base tr p.1).comp (Polynomial.C (J.off (J.tabC p.1) p.2) * Polynomial.X))
    J.H.card (fun p => (natDegree_shift_le _ _).trans (base_natDegree_le J ω δ hNH hpd tr p.1))
  exact h.trans (Nat.mul_le_mul_right _ (J.hdeg χ M i))


/-- The DEEP data of the interface (`R = 2`, `nq = d - 1` base chunk columns of degree `< |H|`). -/
noncomputable def deepParamsJ (hNH : N ≤ J.H.card)
    (hpd : ∀ j c, J.pre j = some c → c.natDegree ≤ J.H.card) :
    DeepParams (extFrame J.Φ0 2) K J.ι0 (Fin (2 ^ n) → B) J.colRound0 where
  R := 2
  nq := 3 * (J.d - 1)
  e := 3
  cw := fun j => pr.gen ^ (j.1 % 3)
  ns := J.ns
  a := ⟨J.Φ0.n, by show J.Φ0.n < J.Φ0.n + 2; omega⟩
  z := ⟨J.Φ0.n + 1, by show J.Φ0.n + 1 < J.Φ0.n + 2; omega⟩
  ha := by simp [extFrame]
  hz := by simp [extFrame]
  hcol := J.hround
  H := HK J
  D := Finset.univ.image (domEmb ω)
  toPoly := tp ω δ N
  hβ := fun w => by
    rw [card_HK]
    unfold tp
    rw [natDegree_map]
    exact decB_natDegree_le ω δ hNH w
  Cp := fun χ tr i =>
    (J.compose (restr 2 χ) (preadJ J pr ω δ N tr) ((wmJ J ω δ N).base tr) i *
      Zout J.H (J.Ht (J.tabS i))).map (algebraMap B K)
  hC := fun χ tr i => by
    refine (natDegree_map_le).trans ?_
    rw [card_HK]
    exact deg_le J.H (J.Ht (J.tabS i)) _ J.d
      (J.hd2.imp_right (fun h => h _)) (compose_natDegree_le J ω δ hNH hpd _ _ tr i)
  hCcoin := fun χ χ' h => by
    have : restr 2 χ = restr 2 χ' := by
      funext i
      refine h (extC J.Φ0 2 i) ?_
      rw [sampledAfter_extC]
      exact J.hcoin i
    funext tr i
    simp only [this]

theorem aeval_shift (q : B[X]) (o : B) (y : K) :
    Polynomial.aeval y (q.comp (Polynomial.C o * Polynomial.X)) =
      eval (y * algebraMap B K o) (q.map (algebraMap B K)) := by
  rw [eval_map_algebraMap, Polynomial.aeval_comp]
  rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X, mul_comm]

theorem cv_aux [NeZero J.r] (χ : Coins (extFrame J.Φ0 2) K) (tr : Tr J.ι0 (Fin (2 ^ n) → B)) (i : Fin J.ns) (y : K)
    (v : J.ι0 × Fin J.r → K)
    (hv : ∀ ck, v ck = eval (if pr.pub ck.1 then pr.ppt ck.1 else y * algebraMap B K (J.off (J.tabC ck.1) ck.2))
      (tp ω δ N (tr ck.1))) :
    eval y ((J.compose (restr 2 χ) (preadJ J pr ω δ N tr) ((wmJ J ω δ N).base tr) i).map (algebraMap B K)) =
      MvPolynomial.aeval (fun p : J.ι0 × Fin J.r =>
        match J.pre p.1 with
        | some c => eval (y * algebraMap B K (J.off (J.tabC p.1) p.2)) (c.map (algebraMap B K))
        | none => v p)
      (J.C (restr 2 χ) (pr.rd (fun c => v (c, 0))) i) := by
  rw [eval_map_algebraMap]
  unfold RapAirJ.compose
  rw [MvPolynomial.comp_aeval_apply (φ := Polynomial.aeval y)]
  have hrd : pr.rd (fun c => v (c, 0)) = preadJ J pr ω δ N tr := by
    refine pr.hrd _ _ (fun c hc => ?_)
    rw [hv]
    simp [hc]
  rw [hrd]
  simp only [MvPolynomial.aeval_def]
  apply MvPolynomial.eval₂_congr
  intro p c hc hne
  have hmem : p ∈ (J.C (restr 2 χ) (preadJ J pr ω δ N tr) i).vars :=
    (MvPolynomial.mem_vars_iff_mem_support p).2 ⟨c, MvPolynomial.mem_support_iff.2 hne, hc⟩
  have hnp := pr.hCpub _ _ _ p hmem
  show Polynomial.aeval y (((wmJ J ω δ N).base tr p.1).comp (Polynomial.C (J.off (J.tabC p.1) p.2) * Polynomial.X)) = _
  rw [aeval_shift, hv p, hnp]
  show eval _ ((match J.pre p.1 with | some c => c | none => decB ω δ N (tr p.1)).map _) = _
  cases J.pre p.1 <;> simp [tp]

/-- The AIR shape: `Cv` evaluates `J.C` at the opened values (preprocessed columns at their fixed polynomial),
with the public message `rd` of the opened public columns. -/
noncomputable def airJ [NeZero J.r] (hNH : N ≤ J.H.card)
    (hpd : ∀ j c, J.pre j = some c → c.natDegree ≤ J.H.card) :
    AirShape (deepParamsJ J pr ω δ N hNH hpd) J.r where
  off _ := 1  -- unused: `pt` is given per column
  pt c k y := if pr.pub c then pr.ppt c else y * algebraMap B K (J.off (J.tabC c) k)
  Cv χ y i v := MvPolynomial.aeval (fun p : J.ι0 × Fin J.r =>
      match J.pre p.1 with
      | some c => eval (y * algebraMap B K (J.off (J.tabC p.1) p.2)) (c.map (algebraMap B K))
      | none => v p)
    (J.C (restr 2 χ) (pr.rd (fun c => v (c, 0))) i) *
    eval y ((Zout J.H (J.Ht (J.tabS i))).map (algebraMap B K))
  hCv χ tr i y := by
    change eval y (Polynomial.map (algebraMap B K) (J.compose (restr 2 χ) (preadJ J pr ω δ N tr)
      ((wmJ J ω δ N).base tr) i * Zout J.H (J.Ht (J.tabS i)))) = _
    rw [Polynomial.map_mul, eval_mul]
    exact congrArg (· * _) (cv_aux J pr ω δ N χ tr i y _ (fun ck => rfl))

/-! ## 4. The statement, `Rest`, `RestV` and the two links -/

variable (hNH : N ≤ J.H.card) (hpd : ∀ j c, J.pre j = some c → c.natDegree ≤ J.H.card)

/-- The RAP statement of the interface at the word layout `wmJ`. -/
noncomputable abbrev R0J : RapStatement (extFrame J.Φ0 2) K J.ι0 (Fin (2 ^ n) → B) J.colRound0 :=
  rapJ J (wmJ J ω δ N) (preadJ J pr ω δ N)

/-- The non-constraint checks on a trace: `Pub` of the public message read off the trace, and `StmtOK`. -/
def RestJ : (R0J J pr ω δ N).M0 → DeepTr (deepParamsJ J pr ω δ N hNH hpd) → (R0J J pr ω δ N).Mfin →
    Coins (extFrame J.Φ0 2) K → Prop :=
  fun _ tr _ χ => J.Pub (restr 2 χ) (preadJ J pr ω δ N ((deepParamsJ J pr ω δ N hNH hpd).restr tr)) ∧ J.StmtOK

/-- The same on the opened values: the public message is read off the opened public columns. -/
def RestVJ [NeZero J.r] : (R0J J pr ω δ N).M0 → DeepFin (deepParamsJ J pr ω δ N hNH hpd) (r := J.r) (R0J J pr ω δ N) →
    Coins (extFrame J.Φ0 2) K → Prop :=
  fun _ fin χ => J.Pub (restr 2 χ) (pr.rd (fun c => fin.2.1 (c, 0))) ∧ J.StmtOK

/-- **`hlink`**: vanishing of the composed constraints on `H`, `Pub`, `StmtOK` give `J.Acc` (via `J.acc_of`). -/
theorem hlink_J :
    ∀ m0 (tr : DeepTr (deepParamsJ J pr ω δ N hNH hpd)) fin χ, RestJ J pr ω δ N hNH hpd m0 tr fin χ →
      (∀ i, ∀ x ∈ (deepParamsJ J pr ω δ N hNH hpd).H,
        eval x ((deepParamsJ J pr ω δ N hNH hpd).Cp χ ((deepParamsJ J pr ω δ N hNH hpd).restr tr) i) = 0) →
      (R0J J pr ω δ N).Accepts m0 ((deepParamsJ J pr ω δ N hNH hpd).restr tr) fin χ := by
  intro m0 tr fin χ hr hv
  refine J.acc_of _ _ _ (fun i x hx => ?_) hr.1 hr.2 ((wmJ J ω δ N).base_pre _)
  have hall : ∀ y ∈ J.H, eval y (J.compose (restr 2 χ) (preadJ J pr ω δ N ((deepParamsJ J pr ω δ N hNH hpd).restr tr))
      ((wmJ J ω δ N).base ((deepParamsJ J pr ω δ N hNH hpd).restr tr)) i * Zout J.H (J.Ht (J.tabS i))) = 0 := by
    intro y hy
    have h := hv i (algebraMap B K y) ((mem_HK J).2 ⟨y, hy, rfl⟩)
    change eval (algebraMap B K y) (Polynomial.map (algebraMap B K) _) = 0 at h
    rw [eval_map, eval₂_at_apply] at h
    exact (map_eq_zero_iff _ (algebraMap B K).injective).1 h
  exact (vanish_iff J.H (J.Ht (J.tabS i)) (J.hHt _) _).1 hall x hx

/-- **`hRest`**: the opened public columns determine the public message. -/
theorem hRest_J [NeZero J.r] :
    ∀ m0 (tr : DeepTr (deepParamsJ J pr ω δ N hNH hpd)) fin χ, RestVJ J pr ω δ N hNH hpd m0 fin χ →
      SatClaims (deepOI (deepParamsJ J pr ω δ N hNH hpd)) tr
        (deepClaims (deepParamsJ J pr ω δ N hNH hpd) (airJ J pr ω δ N hNH hpd) (R0J J pr ω δ N) χ fin) →
      RestJ J pr ω δ N hNH hpd m0 tr fin.1 χ := by
  intro m0 tr fin χ hr hs
  refine ⟨?_, hr.2⟩
  have : pr.rd (fun c => fin.2.1 (c, 0)) =
      preadJ J pr ω δ N ((deepParamsJ J pr ω δ N hNH hpd).restr tr) := by
    refine pr.hrd _ _ (fun c hc => ?_)
    have := hs _ (List.mem_append_left _ (List.mem_map.mpr
      ⟨(c, 0), Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩))
    change eval _ (tp ω δ N (tr (Sum.inl c))) = fin.2.1 (c, 0) at this
    rw [← this]
    show _ = eval (pr.ppt c) (tp ω δ N (tr (Sum.inl c)))
    simp [airJ, hc]
  rw [← this]
  exact hr.1

end Kit

end NockvmE2E.J8
