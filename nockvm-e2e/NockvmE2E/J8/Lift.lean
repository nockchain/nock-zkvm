/-
generic transport of priced summands.
  * `extFrame`: the frame extension `Φ0 → ΦX` (adds `α` after round `R`, `ζ` after round `R+1`);
  * `pullback`: a summand over traces `Tr0` as a summand over `Tr1` along `f : Tr1 → Tr0`
    (staging transported by a hypothesis; discharged for column-wise maps by `staged_colMap`);
  * `liftX`: a summand over `Φ` as one over `extFrame Φ R` (needs every column round `≤ R`, so no column
    reads `α`, `ζ`);
  * `epsilonOf` is preserved by both; a round sub-sum is `≤ ofReal epsilonOf`.
Nothing here depends on J-8 or on the DEEP/FRI layers.
-/
import NockvmE2E.Rap.Frame
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal

namespace NockvmE2E.J8

open NockvmE2E.Rap

/-! ## 1. The frame extension -/

/-- `Φ` plus two coins: `α` sampled after round `R`, `ζ` after round `R+1`. -/
def extFrame (Φ : CoinFrame) (R : ℕ) : CoinFrame where
  n := Φ.n + 2
  sampledAfter i := if h : i.val < Φ.n then Φ.sampledAfter ⟨i.val, h⟩ else R + (i.val - Φ.n)

/-- The old coins inside the new ones. -/
def extC (Φ : CoinFrame) (R : ℕ) (i : Fin Φ.n) : Fin (extFrame Φ R).n :=
  ⟨i.val, by show i.val < Φ.n + 2; omega⟩

theorem extC_injective (Φ : CoinFrame) (R : ℕ) : Function.Injective (extC Φ R) := fun a b h => by
  have := congrArg Fin.val h
  exact Fin.ext this

theorem sampledAfter_extC (Φ : CoinFrame) (R : ℕ) (i : Fin Φ.n) :
    (extFrame Φ R).sampledAfter (extC Φ R i) = Φ.sampledAfter i := by
  simp [extFrame, extC, i.2]

variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K]

/-- Restrict a `ΦX`-coin vector to the old coins. -/
def restr (R : ℕ) (χ : Coins (extFrame Φ R) K) : Coins Φ K := fun i => χ (extC Φ R i)

/-- Extend an old coin vector by `0` on `α`, `ζ`. -/
def extendC [Zero K] (R : ℕ) (χ : Coins Φ K) : Coins (extFrame Φ R) K :=
  fun i => if h : i.val < Φ.n then χ ⟨i.val, h⟩ else 0

theorem restr_extendC [Zero K] (R : ℕ) (χ : Coins Φ K) : restr R (extendC R χ) = χ := by
  funext i; simp [restr, extendC, extC, i.2]

/-! ## 2. Pullback along a trace map -/

section Pullback

variable {Tr0 Tr1 : Type} {S0 : (Coins Φ K → Tr0) → Prop} {S1 : (Coins Φ K → Tr1) → Prop}

/-- A summand over `Tr0` as a summand over `Tr1`, along `f : Tr1 → Tr0` (staging transported by `hf`). -/
def pullback (f : Tr1 → Tr0) (hf : ∀ Q : Coins Φ K → Tr1, S1 Q → S0 (fun χ => f (Q χ)))
    (s : BadSummand Φ K Tr0 S0) : BadSummand Φ K Tr1 S1 where
  coins := s.coins
  dep := s.dep
  disj := s.disj
  badSet tr χ := s.badSet (f tr) χ
  weight := s.weight
  card_le tr χ := s.card_le (f tr) χ
  readsOn Q hQ := s.readsOn (fun χ => f (Q χ)) (hf Q hQ)

theorem mem_pullback (f : Tr1 → Tr0) (hf : ∀ Q : Coins Φ K → Tr1, S1 Q → S0 (fun χ => f (Q χ)))
    (s : BadSummand Φ K Tr0 S0) (tr : Tr1) (χ : Coins Φ K) :
    (pullback f hf s).mem tr χ ↔ s.mem (f tr) χ := Iff.rfl

theorem epsilonOf_map_pullback (f : Tr1 → Tr0)
    (hf : ∀ Q : Coins Φ K → Tr1, S1 Q → S0 (fun χ => f (Q χ)))
    (L : List (BadSummand Φ K Tr0 S0)) :
    epsilonOf (L.map (pullback f hf)) = epsilonOf L := by
  unfold epsilonOf
  simp only [List.map_map]
  rfl

end Pullback

/-- **Column-wise maps transport staging**: `f tr j = g j (tr (e j))` with `colRound (e j) = colRound0 j`. -/
theorem staged_colMap {ι ι0 β B' : Type} (colRound : ι → ℕ) (colRound0 : ι0 → ℕ) (e : ι0 → ι)
    (hcol : ∀ j, colRound (e j) = colRound0 j) (g : ι0 → β → B') :
    ∀ Q : Coins Φ K → Tr ι β, TracesStaged Φ colRound Q →
      TracesStaged Φ colRound0 (fun χ => fun j => g j (Q χ (e j))) := by
  intro Q hQ j χ χ' h
  show g j (Q χ (e j)) = g j (Q χ' (e j))
  rw [hQ (e j) χ χ' (by rw [hcol]; exact h)]

/-! ## 3. Lift to the extended frame -/

section Lift

variable {ι β : Type} {colRound : ι → ℕ} {R : ℕ}

/-- The old coins inside the new, as an equivalence of the coin sets. -/
noncomputable def coinEquiv (R : ℕ) (S : Finset (Fin Φ.n)) :
    S ≃ (S.map ⟨extC Φ R, extC_injective Φ R⟩) :=
  Equiv.ofBijective (fun i => ⟨extC Φ R i.1, Finset.mem_map_of_mem _ i.2⟩)
    ⟨fun a b h => Subtype.ext (extC_injective Φ R (congrArg Subtype.val h)), fun ⟨x, hx⟩ => by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact ⟨⟨y, hy⟩, rfl⟩⟩

/-- The induced bijection of coin assignments. -/
noncomputable def coinFunEquiv (R : ℕ) (S : Finset (Fin Φ.n)) :
    (S → K) ≃ (S.map ⟨extC Φ R, extC_injective Φ R⟩ → K) :=
  (coinEquiv R S).arrowCongr (Equiv.refl K)

/-- **`liftX`**: a summand over `Φ` as a summand over `extFrame Φ R`. -/
noncomputable def liftX [Zero K] (hR : ∀ j, colRound j ≤ R)
    (s : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound)) :
    BadSummand (extFrame Φ R) K (Tr ι β) (TracesStaged (extFrame Φ R) colRound) where
  coins := s.coins.map ⟨extC Φ R, extC_injective Φ R⟩
  dep := s.dep.map ⟨extC Φ R, extC_injective Φ R⟩
  disj := Finset.disjoint_map _ |>.mpr s.disj
  badSet tr χ := (s.badSet tr (restr R χ)).map (coinFunEquiv R s.coins).toEmbedding
  weight := s.weight
  card_le tr χ := by rw [Finset.card_map]; exact s.card_le _ _
  readsOn Q hQ := by
    have hQ0 : TracesStaged Φ colRound (fun χ0 : Coins Φ K => Q (extendC R χ0)) := by
      intro j χ χ' h
      refine hQ j _ _ ?_
      intro i hi
      by_cases hn : i.val < Φ.n
      · have := h ⟨i.val, hn⟩ (by simpa [extFrame, hn] using hi)
        simp [extendC, hn, this]
      · simp [extendC, hn]
    have hQeq : ∀ χ : Coins (extFrame Φ R) K, Q χ = Q (extendC R (restr R χ)) := by
      intro χ
      funext j
      refine hQ j _ _ ?_
      intro i hi
      by_cases hn : i.val < Φ.n
      · simp [extendC, restr, extC, hn]
      · exfalso
        have := hR j
        simp [extFrame, hn] at hi
        omega
    intro χ χ' h
    show ((s.badSet (Q χ) (restr R χ)).map _) = ((s.badSet (Q χ') (restr R χ')).map _)
    rw [hQeq χ, hQeq χ']
    have := s.readsOn _ hQ0 (restr R χ) (restr R χ') (fun j hj => h (extC Φ R j)
      (Finset.mem_map_of_mem _ hj))
    exact congrArg (Finset.map (coinFunEquiv R s.coins).toEmbedding) this

variable [Zero K]

theorem mem_liftX (hR : ∀ j, colRound j ≤ R) (s : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound))
    (tr : Tr ι β) (χ : Coins (extFrame Φ R) K) :
    (liftX hR s).mem tr χ ↔ s.mem tr (restr R χ) := by
  unfold BadSummand.mem liftX
  show _ ∈ (s.badSet tr (restr R χ)).map (coinFunEquiv R s.coins).toEmbedding ↔ _
  rw [Finset.mem_map_equiv]
  exact Iff.rfl

theorem sampledAfter_liftX (hR : ∀ j, colRound j ≤ R) (s : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound))
    {i : Fin (extFrame Φ R).n} (hi : i ∈ (liftX hR s).coins) :
    ∃ i0 ∈ s.coins, i = extC Φ R i0 := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hi
  exact ⟨y, hy, rfl⟩

theorem epsilonOf_map_liftX (hR : ∀ j, colRound j ≤ R)
    (L : List (BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound))) :
    epsilonOf (L.map (liftX hR)) = epsilonOf L := by
  unfold epsilonOf
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro s _
  simp [liftX]

end Lift

/-! ## 4. A round sub-sum is bounded by `epsilonOf` -/

section Bound

variable {Tr : Type} {Staged : (Coins Φ K → Tr) → Prop}

/-- The `ℝ≥0∞` price of a summand (the summand of `Rap.roundBound`). -/
noncomputable def termE (s : BadSummand Φ K Tr Staged) : ℝ≥0∞ :=
  (s.weight : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞) ^ s.coins.card

theorem termE_eq (hK : 0 < Fintype.card K) (s : BadSummand Φ K Tr Staged) :
    termE s = ENNReal.ofReal
      ((((s.weight : ℚ) / ((Fintype.card K : ℚ) ^ s.coins.card) : ℚ) : ℝ)) := by
  have hpos : (0 : ℝ) < ((Fintype.card K : ℝ)) ^ s.coins.card := pow_pos (by exact_mod_cast hK) _
  push_cast
  rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]
  rfl

theorem epsilonOf_nonneg (L : List (BadSummand Φ K Tr Staged)) : 0 ≤ epsilonOf L := by
  unfold epsilonOf
  apply List.sum_nonneg
  intro x hx
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx
  positivity

theorem sum_termE_eq (hK : 0 < Fintype.card K) (L : List (BadSummand Φ K Tr Staged)) :
    (L.map termE).sum = ENNReal.ofReal ((epsilonOf L : ℚ) : ℝ) := by
  induction L with
  | nil => simp [epsilonOf]
  | cons s L ih =>
    have h1 : epsilonOf (s :: L) =
        ((s.weight : ℚ) / ((Fintype.card K : ℚ) ^ s.coins.card)) + epsilonOf L := by
      simp [epsilonOf]
    rw [List.map_cons, List.sum_cons, ih, termE_eq hK, h1]
    push_cast
    rw [ENNReal.ofReal_add (by positivity) (by exact_mod_cast epsilonOf_nonneg L)]

/-- **A round's sub-sum of the prices is `≤ ofReal (epsilonOf L)`.** -/
theorem sum_round_le (hK : 0 < Fintype.card K) (L : List (BadSummand Φ K Tr Staged))
    (blk : BadSummand Φ K Tr Staged → ℕ) (r : ℕ) :
    (L.map fun s => if blk s = r then termE s else 0).sum ≤
      ENNReal.ofReal ((epsilonOf L : ℚ) : ℝ) := by
  rw [← sum_termE_eq hK L]
  apply List.sum_le_sum
  intro s _
  split_ifs <;> simp

end Bound

end NockvmE2E.J8
