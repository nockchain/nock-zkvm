/-
  Nock/NockVMROM/Thm54/P8Core/SVFrame/FibreBound.lean

  **The generic fibre bound for a `BadSummand` and the union
  bound over a summand list.**

  * `BadSummand.event` — the coin vectors `χ` lying in a summand's bad set at their own traces `Q χ`
    (a staged prover strategy).
  * `BadSummand.event_card_le` — along ANY strategy in the summand's `Staged` class, with
    `c = s.coins.card`: `#{χ | s.mem (Q χ) χ} ≤ s.weight · |𝕂|^(n − c)`.  The proof is the fibre
    principle (`SeedFibers.fiberEvent_card_le`) over the `n − c` coordinates outside `s.coins`, with
    the priced coordinates `χ|coins` as the fibre: the bad set reads only `dep` (`s.readsOn`), and
    `dep` misses every priced coin (`s.disj`).  This is `PartAEvents12.cylinder₂_card_le` at any
    `coins.card` (`cylinder₂` is `coins = {i, j}`), with `RoundFibred.ReadsOn` in its frame form
    `ReadsOnC`.
  * `BadSummand.event_prob_le` — the same as a probability, `≤ weight / |𝕂|^c`.
  * `union_card_le` / **`union_prob_le`** — `Pr_χ[∃ s ∈ L, s.mem (Q χ) χ] ≤ epsilonOf L`: the
    assembly of `PartAStaged12.staged_consumed_card_le`, done once over a list.
  * It is not a `BadSummand` only because of `disj`
    (`¬ Disjoint {0} {0}`), which is therefore load-bearing.
-/
import Nock.NockVMROM.Thm54.P8Core.SVFrame.MemSoundnessFamily

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.SVFrame

open Nock.NockVMROM.Thm54

noncomputable section

/-! ## 1. The fibre bound for one summand -/

section Fibre

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {Tr : Type}
  {Staged : (Coins Φ K → Tr) → Prop}

open Classical in
/-- The event of a summand along a strategy `Q`: the coin vectors in the summand's bad set at their
own traces. -/
def BadSummand.event (s : BadSummand Φ K Tr Staged) (Q : Coins Φ K → Tr) : Finset (Coins Φ K) :=
  Finset.univ.filter fun χ => s.mem (Q χ) χ

open Classical in
theorem BadSummand.mem_event (s : BadSummand Φ K Tr Staged) (Q : Coins Φ K → Tr) (χ : Coins Φ K) :
    χ ∈ s.event Q ↔ s.mem (Q χ) χ := by
  simp [BadSummand.event]

/-- The free coordinates of a summand (outside its priced coins) number `n − c`. -/
theorem card_free_coords (coins : Finset (Fin Φ.n)) :
    Fintype.card ({k : Fin Φ.n // k ∉ coins} → K) = Fintype.card K ^ (Φ.n - coins.card) := by
  classical
  rw [Fintype.card_fun]
  congr 1
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun k : Fin Φ.n => k ∉ coins) = Finset.univ \ coins := by
    ext k; simp
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]

/-- **The fibre bound** (`cylinder₂_card_le` at any `coins.card`): along any strategy of the
summand's staged class, `#{χ | s.mem (Q χ) χ} ≤ s.weight · |𝕂|^(n − c)`. -/
theorem BadSummand.event_card_le (s : BadSummand Φ K Tr Staged) (Q : Coins Φ K → Tr)
    (hQ : Staged Q) :
    (s.event Q).card ≤ s.weight * Fintype.card K ^ (Φ.n - s.coins.card) := by
  classical
  let Rr := {k : Fin Φ.n // k ∉ s.coins}
  -- complete the free coordinates by `0` on the priced coins
  let ext : (Rr → K) → Coins Φ K := fun r k => if h : k ∉ s.coins then r ⟨k, h⟩ else 0
  let g : (Rr → K) → Finset (s.coins → K) := fun r => s.badSet (Q (ext r)) (ext r)
  have key : ∀ χ : Coins Φ K, g (fun k : Rr => χ k.1) = s.badSet (Q χ) χ := by
    intro χ
    refine (s.readsOn Q hQ (ext fun k : Rr => χ k.1) χ ?_)
    intro k hk
    have hkc : k ∉ s.coins := fun hc => Finset.disjoint_left.mp s.disj hc hk
    simp [ext, hkc]
  have h1 : (s.event Q).card ≤ (fiberEvent (Finset.univ : Finset (Rr → K)) g).card := by
    refine Finset.card_le_card_of_injOn
      (fun χ : Coins Φ K => ((fun k : Rr => χ k.1), (fun i : s.coins => χ i))) ?_ ?_
    · intro χ hχ
      have hχ' : (fun i : s.coins => χ i) ∈ s.badSet (Q χ) χ := (s.mem_event Q χ).1 hχ
      refine (mem_fiberEvent_iff (Finset.univ : Finset (Rr → K)) g _ _).2
        ⟨Finset.mem_univ _, ?_⟩
      show (fun i : s.coins => χ i) ∈ g (fun k : Rr => χ k.1)
      rw [key]
      exact hχ'
    · intro χ _ χ' _ h
      funext k
      by_cases hk : k ∈ s.coins
      · exact congrFun (congrArg Prod.snd h) ⟨k, hk⟩
      · exact congrFun (congrArg Prod.fst h) ⟨k, hk⟩
  refine h1.trans ?_
  refine le_trans (fiberEvent_card_le (Finset.univ : Finset (Rr → K)) g s.weight
    (fun r _ => s.card_le _ _)) ?_
  rw [Finset.card_univ, card_free_coords (K := K) s.coins, Nat.mul_comm]

/-- The coin space has `|𝕂|^n` points. -/
theorem card_coins : Fintype.card (Coins Φ K) = Fintype.card K ^ Φ.n := by
  simp [Coins, Fintype.card_fun]

/-- **The fibre bound as a probability**: `Pr_χ[s.mem (Q χ) χ] ≤ weight / |𝕂|^c`. -/
theorem BadSummand.event_prob_le (s : BadSummand Φ K Tr Staged) (Q : Coins Φ K → Tr)
    (hQ : Staged Q) :
    ((s.event Q).card : ℚ) / Fintype.card (Coins Φ K) ≤
      (s.weight : ℚ) / (Fintype.card K : ℚ) ^ s.coins.card := by
  have hK : (0 : ℚ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hc : s.coins.card ≤ Φ.n := by
    simpa using Finset.card_le_univ s.coins
  rw [card_coins, div_le_div_iff₀ (by push_cast; positivity) (by positivity)]
  have h := s.event_card_le Q hQ
  have h' : ((s.event Q).card : ℚ) ≤ (s.weight : ℚ) * (Fintype.card K : ℚ) ^ (Φ.n - s.coins.card) := by
    exact_mod_cast h
  calc ((s.event Q).card : ℚ) * (Fintype.card K : ℚ) ^ s.coins.card
      ≤ (s.weight : ℚ) * (Fintype.card K : ℚ) ^ (Φ.n - s.coins.card) *
          (Fintype.card K : ℚ) ^ s.coins.card := by gcongr
    _ = (s.weight : ℚ) * ((Fintype.card K ^ Φ.n : ℕ) : ℚ) := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hc]; push_cast; ring

end Fibre

/-! ## 2. The union bound over a summand list -/

section Union

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {Tr : Type}
  {Staged : (Coins Φ K → Tr) → Prop}

open Classical in
/-- The union event of a summand list along a strategy. -/
def unionEvent (L : List (BadSummand Φ K Tr Staged)) (Q : Coins Φ K → Tr) : Finset (Coins Φ K) :=
  Finset.univ.filter fun χ => ∃ s ∈ L, s.mem (Q χ) χ

open Classical in
theorem unionEvent_subset (L : List (BadSummand Φ K Tr Staged)) (Q : Coins Φ K → Tr) :
    unionEvent L Q ⊆ (L.map fun s => s.event Q).foldr (· ∪ ·) ∅ := by
  induction L with
  | nil => intro χ hχ; simp [unionEvent] at hχ
  | cons s L ih =>
      intro χ hχ
      simp only [unionEvent, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons] at hχ
      obtain ⟨s', hs', hm⟩ := hχ
      simp only [List.map_cons, List.foldr_cons, Finset.mem_union]
      rcases hs' with rfl | hs'
      · exact Or.inl ((s'.mem_event Q χ).2 hm)
      · exact Or.inr (ih (by simp [unionEvent]; exact ⟨s', hs', hm⟩))

theorem card_foldr_union_le (L : List (Finset (Coins Φ K))) :
    (L.foldr (· ∪ ·) ∅).card ≤ (L.map Finset.card).sum := by
  induction L with
  | nil => simp
  | cons A L ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      exact (Finset.card_union_le _ _).trans (by omega)

theorem union_card_le (L : List (BadSummand Φ K Tr Staged)) (Q : Coins Φ K → Tr) :
    (unionEvent L Q).card ≤ (L.map fun s => (s.event Q).card).sum := by
  refine (Finset.card_le_card (unionEvent_subset L Q)).trans ?_
  refine (card_foldr_union_le _).trans (le_of_eq ?_)
  rw [List.map_map]; rfl

theorem epsilonOf_cons (s : BadSummand Φ K Tr Staged) (L : List (BadSummand Φ K Tr Staged)) :
    epsilonOf (s :: L) = (s.weight : ℚ) / (Fintype.card K : ℚ) ^ s.coins.card + epsilonOf L := by
  simp [epsilonOf]

/-- The summed per-summand probabilities are at most `epsilonOf`. -/
theorem sum_event_prob_le (L : List (BadSummand Φ K Tr Staged)) (Q : Coins Φ K → Tr)
    (hQ : Staged Q) :
    (((L.map fun s => (s.event Q).card).sum : ℕ) : ℚ) / Fintype.card (Coins Φ K) ≤ epsilonOf L := by
  induction L with
  | nil => simp [epsilonOf]
  | cons s L ih =>
      rw [epsilonOf_cons, List.map_cons, List.sum_cons, Nat.cast_add, add_div]
      exact add_le_add (s.event_prob_le Q hQ) ih

/-- **The union bound**: along any strategy of the staged class,
`Pr_χ[∃ s ∈ L, s.mem (Q χ) χ] ≤ epsilonOf L`. -/
theorem union_prob_le (L : List (BadSummand Φ K Tr Staged)) (Q : Coins Φ K → Tr) (hQ : Staged Q) :
    ((unionEvent L Q).card : ℚ) / Fintype.card (Coins Φ K) ≤ epsilonOf L := by
  have hpos : (0 : ℚ) < Fintype.card (Coins Φ K) := by exact_mod_cast Fintype.card_pos
  have h1 : ((unionEvent L Q).card : ℚ) ≤ (((L.map fun s => (s.event Q).card).sum : ℕ) : ℚ) := by
    exact_mod_cast union_card_le L Q
  exact le_trans (div_le_div_of_nonneg_right h1 hpos.le) (sum_event_prob_le L Q hQ)

end Union

/-! ## 3. Negative control: a read set meeting the priced coins admits no bound -/

section NegativeControl

/-- A two-coin frame (coins `0, 1`). -/
abbrev frameNC : CoinFrame := ⟨2, fun _ => 0⟩

instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- The priced (and read) coin set `{0}`. -/
abbrev coinsNC : Finset (Fin frameNC.n) := {0}

/-- The would-be summand's bad set: the singleton `{χ 0}` — it reads the very coin it prices. -/
def badNC (χ : Coins frameNC (ZMod 97)) : Finset (coinsNC → ZMod 97) := {fun _ => χ 0}

open Classical in
/-- So the fibre bound needs `disj`: without it no bound holds. -/
theorem dep_meets_coins_no_bound :
    (∀ χ, (badNC χ).card ≤ 1) ∧ ReadsOnC frameNC ({0} : Finset (Fin frameNC.n)) badNC ∧
      ¬ Disjoint coinsNC ({0} : Finset (Fin frameNC.n)) ∧
      (Finset.univ.filter fun χ : Coins frameNC (ZMod 97) =>
          (fun i : coinsNC => χ i) ∈ badNC χ).card = 97 ^ 2 ∧
      ¬ ((Finset.univ.filter fun χ : Coins frameNC (ZMod 97) =>
          (fun i : coinsNC => χ i) ∈ badNC χ).card ≤
        1 * Fintype.card (ZMod 97) ^ (frameNC.n - coinsNC.card)) := by
  have hall : (Finset.univ.filter fun χ : Coins frameNC (ZMod 97) =>
      (fun i : coinsNC => χ i) ∈ badNC χ) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro χ _
    simp only [badNC, Finset.mem_singleton]
    funext i
    have hi : (i : Fin frameNC.n) = 0 := Finset.mem_singleton.mp i.2
    rw [hi]
  have hcard : (Finset.univ : Finset (Coins frameNC (ZMod 97))).card = 97 ^ 2 := by
    rw [Finset.card_univ, card_coins, ZMod.card]
  refine ⟨fun χ => by simp [badNC], ?_, ?_, ?_, ?_⟩
  · intro χ χ' h
    simp only [badNC, h 0 (Finset.mem_singleton_self 0)]
  · simp [coinsNC]
  · rw [hall, hcard]
  · have h1 : frameNC.n - coinsNC.card = 1 := by decide
    rw [hall, hcard, ZMod.card, h1]
    norm_num

end NegativeControl

end

end Nock.NockVMROM.Thm54.SVFrame
