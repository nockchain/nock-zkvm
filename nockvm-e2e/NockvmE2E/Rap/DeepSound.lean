/-
the two new summands `s_α`, `s_ζ`, the extended statement, the error identity
`epsilonOf (old ++ [s_α, s_ζ]) = ε_old + ε_α + ε_ζ`, and `SoundG_deep`.
-/
import NockvmE2E.Rap.DeepFrame

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace NockvmE2E.Rap

section
variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} (P : DeepParams Φ K ι β colRound)

/-- The α-side bad set reads the coins of rounds `< R` only (through `Cp`). -/
theorem DeepParams.badAlpha_congr (χ χ' : Coins Φ K) (h : ∀ i, Φ.sampledAfter i < P.R → χ i = χ' i)
    (tr : Tr ι β) : P.badAlpha χ tr = P.badAlpha χ' tr := by
  have e := P.hCcoin χ χ' h
  have h1 : P.HasBad χ = P.HasBad χ' := by
    funext tr; simp only [DeepParams.HasBad, e]
  have hx : P.x0 χ = P.x0 χ' := by
    funext tr
    have key : ∀ c c' : Fin P.ns → K[X], c = c' → ∀ (h : ∃ x ∈ P.H, ∃ i, eval x (c i) ≠ 0)
        (h' : ∃ x ∈ P.H, ∃ i, eval x (c' i) ≠ 0), h.choose = h'.choose := by
      rintro c _ rfl _ _; rfl
    by_cases hb : P.HasBad χ tr
    · have hb' : P.HasBad χ' tr := by rw [← congrFun h1 tr]; exact hb
      simp only [DeepParams.x0, dif_pos hb, dif_pos hb']
      exact key _ _ (congrFun e tr) hb hb'
    · have hb' : ¬ P.HasBad χ' tr := by rw [← congrFun h1 tr]; exact hb
      simp only [DeepParams.x0, dif_neg hb, dif_neg hb']
  have hp : P.Palpha χ = P.Palpha χ' := by
    funext tr; simp only [DeepParams.Palpha, hx, e]
  have h1' := congrFun h1 tr
  have hp' := congrFun hp tr
  unfold DeepParams.badAlpha
  congr! 3
  rw [hp']

/-- `Gpoly` reads the coins of rounds `< R` only (through `Cp`). -/
theorem DeepParams.Gpoly_congr (χ χ' : Coins Φ K) (h : ∀ i, Φ.sampledAfter i < P.R → χ i = χ' i)
    (tr : DeepTr P) (α : K) : P.Gpoly χ tr α = P.Gpoly χ' tr α := by
  have e := P.hCcoin χ χ' h
  unfold DeepParams.Gpoly DeepParams.Apoly
  rw [e]

/-- `s_α`: coins `{α}`, reads the committed old columns (coins sampled before round `R`),
weight `ns − 1`. -/
noncomputable def DeepParams.sAlpha : BadSummand Φ K (DeepTr P) (DeepStaged P) where
  coins := {P.a}
  dep := Finset.univ.filter fun i => Φ.sampledAfter i < P.R
  disj := by simp [Finset.disjoint_singleton_left, P.ha]
  badSet tr χ := P.badAlpha χ (P.restr tr)
  weight := P.ns - 1
  card_le tr χ := P.badAlpha_card χ _
  readsOn Q hQ χ χ' h := by
    have : P.restr (Q χ) = P.restr (Q χ') := funext fun j =>
      hQ (Sum.inl j) χ χ' (fun i hi => h i (by simpa using lt_of_lt_of_le hi (P.hcol j)))
    show P.badAlpha χ (P.restr (Q χ)) = P.badAlpha χ' (P.restr (Q χ'))
    rw [this]
    exact P.badAlpha_congr χ χ' (fun i hi => h i (by simpa using hi)) _

/-- `s_ζ`: coins `{ζ}`, reads every column (all committed by round `R+1`) and `α`; the dependency set
is the coins sampled by round `R` (it contains `α`). Weight `|D| + (nq+1)·|H|`. -/
noncomputable def DeepParams.sZeta : BadSummand Φ K (DeepTr P) (DeepStaged P) where
  coins := {P.z}
  dep := Finset.univ.filter fun i => Φ.sampledAfter i ≤ P.R
  disj := by simp [Finset.disjoint_singleton_left, P.hz]
  badSet tr χ := P.badZeta χ tr (χ P.a)
  weight := P.D.card + (P.nq + 1) * P.H.card
  card_le tr χ := P.badZeta_card χ tr _
  readsOn Q hQ χ χ' h := by
    have hq : Q χ = Q χ' := funext fun j =>
      hQ j χ χ' (fun i hi => h i (by
        have : Φ.sampledAfter i < P.R + 1 := by
          rcases j with j | j
          · exact lt_of_lt_of_le (show Φ.sampledAfter i < colRound j from hi) (by have := P.hcol j; omega)
          · exact hi
        simpa [Nat.lt_succ_iff] using this))
    have ha : χ P.a = χ' P.a := h P.a (by simp [P.ha])
    show P.badZeta χ (Q χ) (χ P.a) = P.badZeta χ' (Q χ') (χ' P.a)
    have hg : ∀ tr α, P.Gpoly χ tr α = P.Gpoly χ' tr α := fun tr α =>
      P.Gpoly_congr χ χ' (fun i hi => h i (by simpa using hi.le)) tr α
    rw [hq, ha]
    unfold DeepParams.badZeta
    simp only [hg]

/-- Lift an old summand to the extended traces (it reads the old columns only). -/
def DeepParams.liftS (s : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound)) :
    BadSummand Φ K (DeepTr P) (DeepStaged P) where
  coins := s.coins
  dep := s.dep
  disj := s.disj
  badSet tr χ := s.badSet (P.restr tr) χ
  weight := s.weight
  card_le _ _ := s.card_le _ _
  readsOn Q hQ := s.readsOn (fun χ => P.restr (Q χ)) (fun j χ χ' h => hQ (Sum.inl j) χ χ' h)

/-- **The extended statement** (goal 1): same messages and holds; summands `old ++ [s_α, s_ζ]`; acceptance
is the polynomial opening identity `G_α(ζ) = 0` together with `Rest` (the part of the verifier's checks that
is not the quotient identity). -/
noncomputable def DeepParams.statement (R0 : RapStatement Φ K ι β colRound)
    (Rest : R0.M0 → Tr (ι ⊕ Fin P.nq) β → R0.Mfin → Coins Φ K → Prop) :
    RapStatement Φ K (ι ⊕ Fin P.nq) β P.colRoundX where
  M0 := R0.M0
  Mfin := R0.Mfin
  summands m0 := (R0.summands m0).map P.liftS ++ [P.sAlpha, P.sZeta]
  Accepts m0 tr fin χ := eval (χ P.z) (P.Gpoly χ tr (χ P.a)) = 0 ∧ Rest m0 tr fin χ
  Holds := R0.Holds

/-- **Goal 1.** `ε_{old ++ [s_α, s_ζ]} = ε_old + (ns−1)/|K| + (|D| + (nq+1)|H|)/|K|`. -/
theorem epsilon_deep (R0 : RapStatement Φ K ι β colRound) (Rest) (m0 : R0.M0) :
    epsilonOf ((P.statement R0 Rest).summands m0) =
      epsilonOf (R0.summands m0) + ((P.ns - 1 : ℕ) : ℚ) / (Fintype.card K : ℚ) +
        ((P.D.card + (P.nq + 1) * P.H.card : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
  have hmap : epsilonOf ((R0.summands m0).map P.liftS) = epsilonOf (R0.summands m0) := by
    simp [epsilonOf, List.map_map, Function.comp_def, DeepParams.liftS]
  show epsilonOf ((R0.summands m0).map P.liftS ++ [P.sAlpha, P.sZeta]) = _
  simp only [epsilonOf, List.map_append, List.sum_append] at hmap ⊢
  rw [hmap]
  simp [DeepParams.sAlpha, DeepParams.sZeta, add_assoc]

/-- Membership in the lifted summand is membership of the old one on the restricted traces. -/
theorem mem_liftS (s : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound)) (tr : DeepTr P) (χ) :
    (P.liftS s).mem tr χ ↔ s.mem (P.restr tr) χ := Iff.rfl

theorem sZeta_mem (tr : DeepTr P) (χ : Coins Φ K) :
    P.sZeta.mem tr χ ↔ χ P.z ∈ P.D ∨
      (P.Gpoly χ tr (χ P.a) ≠ 0 ∧ eval (χ P.z) (P.Gpoly χ tr (χ P.a)) = 0) := by
  classical
  unfold BadSummand.mem
  exact ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

theorem sAlpha_mem (tr : DeepTr P) (χ : Coins Φ K) :
    P.sAlpha.mem tr χ ↔ P.HasBad χ (P.restr tr) ∧ eval (χ P.a) (P.Palpha χ (P.restr tr)) = 0 := by
  classical
  unfold BadSummand.mem
  exact ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

theorem eval_Apoly (χ : Coins Φ K) (tr : Tr ι β) (α x : K) :
    eval x (P.Apoly χ tr α) = ∑ i : Fin P.ns, α ^ i.1 * eval x (P.Cp χ tr i) := by
  simp [DeepParams.Apoly, eval_finsetSum]

theorem eval_Palpha (χ : Coins Φ K) (tr : Tr ι β) (α : K) :
    eval α (P.Palpha χ tr) = eval (P.x0 χ tr) (P.Apoly χ tr α) := by
  rw [eval_Apoly]
  simp only [DeepParams.Palpha, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem eval_Zpoly {x : K} (hx : x ∈ P.H) : eval x P.Zpoly = 0 := by
  simp only [DeepParams.Zpoly, eval_prod]
  exact Finset.prod_eq_zero hx (by simp)

/-- **Goal 2: `SoundG_deep`.** The old `SoundG` (pointwise soundness of the polynomial acceptance) and the
link "constraints vanish on `H` (+ `Rest`) give the old acceptance" yield `SoundG` of the extended statement;
the proof is exactly the two one-variable Schwartz–Zippel steps priced by `s_ζ` and `s_α`. -/
theorem soundG_deep (R0 : RapStatement Φ K ι β colRound) (Rest) (hsound : SoundG R0)
    (hlink : ∀ m0 (tr : DeepTr P) fin χ, Rest m0 tr fin χ →
      (∀ i, ∀ x ∈ P.H, eval x (P.Cp χ (P.restr tr) i) = 0) → R0.Accepts m0 (P.restr tr) fin χ) :
    SoundG (P.statement R0 Rest) := by
  intro m0 tr fin χ ⟨hG, hrest⟩ hall
  have hz : ¬ P.sZeta.mem tr χ := hall _ (by simp [DeepParams.statement])
  have ha : ¬ P.sAlpha.mem tr χ := hall _ (by simp [DeepParams.statement])
  rw [sZeta_mem] at hz
  rw [sAlpha_mem] at ha
  -- step 1: `G_α = 0`
  have hG0 : P.Gpoly χ tr (χ P.a) = 0 := by
    by_contra h; exact hz (Or.inr ⟨h, hG⟩)
  -- hence `Σ αⁱ C_i` vanishes on `H`
  have hA : ∀ x ∈ P.H, eval x (P.Apoly χ (P.restr tr) (χ P.a)) = 0 := by
    intro x hx
    have := congrArg (eval x) hG0
    simpa [DeepParams.Gpoly, eval_Zpoly P hx] using this
  -- step 2: every `C_i` vanishes on `H`
  have hC : ∀ i, ∀ x ∈ P.H, eval x (P.Cp χ (P.restr tr) i) = 0 := by
    by_contra hc
    push Not at hc
    have hb : P.HasBad χ (P.restr tr) := by
      obtain ⟨i, x, hx, h⟩ := hc; exact ⟨x, hx, i, h⟩
    have hx0 : P.x0 χ (P.restr tr) ∈ P.H := by
      have := hb.choose_spec.1
      simpa [DeepParams.x0, hb] using this
    exact ha ⟨hb, by rw [eval_Palpha]; exact hA _ hx0⟩
  exact hsound m0 (P.restr tr) fin χ (hlink m0 tr fin χ hrest hC) (fun s hs hm => by
    exact hall (P.liftS s) (by simp [DeepParams.statement]; exact Or.inl ⟨s, hs, rfl⟩) hm)

end

end NockvmE2E.Rap
