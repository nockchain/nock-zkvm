/-
  Nock/RedTeam/Batch478Thm54QueueGateRatioForm.lean

  The proposal under attack: one `𝕂`-valued witness column `walk_inv` and two gates
  `walk_inv(i) · (count(i) − ln(i)) = 1` for `i < h`, `count(h) = ln(h)`; the paper's `inv_gen`
  idiom applied to the walk columns of the paper.
  With `ln(i) = α^i` (`:816`, `:840`, `:2282`) and `count(i) = initial_count · α^{Σ_{j≤i} fanout}`
  (`:813`, `:845`, `:2284`; `initial_count = α` at `:962`, `α^k` for a `k`-root forest at
  `:1006`), `count(i) = ln(i)` reads `α^{k + Sf(i)} = α^i`, i.e. `α^{q(i)} = 1` where
  `q(i) = k + Sf(i) − i` is the integer BFS queue length after row `i`.

  What is COMPILED here (all generic in the field, no characteristic assumption unless stated):

  * A1 `bfsValidF_of_ratio_gate` — the transition gate alone forces queue-validity
    (`Walk.BFSValidF k fo h`) with **no hypothesis on `α` at all**: the queue moves by `≥ −1`
    per row from `k ≥ 1`, so the first underflow passes through `q = 0` exactly, where
    `count = ln` holds as `α^n = α^n` for EVERY `α` (including `α = 0`, `α = 1`, small order).
  * Together: `walk_ratio_gate_sound` from `Walk.WalkSat` with
    `initial_count = α^k`.
  * A3 `char_bound_does_not_suffice` — the characteristic is the WRONG quantity: at `α = −1`
    a one-row table whose root declares two children (`k = 1`, `fo 1 = 2`, `1 + Sf = 3 ≠ 1`)
    passes both gates in every field, while `1 + Sf = 3 < p` for every `p ≥ 5`.  The
    `Walk.QGate` bound `1 + Sf fo h < p` (`Nock/Walk.lean`) is a bound for a DIFFERENT gate
    (a scalar counter in `𝔽`), not for this one.
  * A4 `terminal_event_card_le` / `nontiling_accepting_alphas_subset` — the soundness price of
    the terminal gate on a queue-valid, non-tiling committed fanout column is the coin event
    `{α : α^d = 1} ∪ {0}`, `d = k + Sf fo h − h ≥ 1`, of size `≤ d + 1` (`Polynomial.card_nthRoots`);
    at compute arity `fanout ≤ 3` that is `≤ 2h + 2` — the paper's order `h/|𝕂|` (`:966`), not
    `h²`.  No event is needed for the queue-validity half (A1).

  The walk coin `alphaC` (`JointCoins.lean`,
  compute challenge slot `6`, `OptimizedComputeSubstitution.walkChallengeBase`) is NOT the
  theorem's timestamp `α` of `hwin : programAcc + 3 < orderOf α`
  (`GenNockCompilesCarrier.lean::nockCompiles_zmod`): `honestJointCoins`
  (`OptimizedStrictFullPackage.lean`) sets `alphaC := family.computeWalkAlpha` and the
  timestamp coordinate `:= cfg.challenges.α` separately, and the compiler instantiates
  `computeWalkAlpha = memoryWalkAlpha = 0` (`GenNockCompilesBounded.lean:447`, `:639`:
  `… hcard 0 0 0 (fun _ => 0) 0`).
-/
import Nock.WalkPrefix

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch478

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk

section Generic
variable {K : Type*} [Field K]

/-- A field element of positive (finite) multiplicative order is nonzero. -/
theorem ne_zero_of_orderOf_pos {α : K} (h : 0 < orderOf α) : α ≠ 0 := by
  intro h0
  have hfin : IsOfFinOrder α := orderOf_pos_iff.mp h
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  rw [h0, zero_pow (Nat.pos_iff_ne_zero.mp hn)] at hpow
  exact zero_ne_one hpow

/-- `α^{i+d} = α^i` with `α ≠ 0` gives `α^d = 1`. -/
theorem pow_eq_one_of_pow_add_eq {α : K} (hα : α ≠ 0) {i d : ℕ} (h : α ^ (i + d) = α ^ i) :
    α ^ d = 1 := by
  rw [pow_add] at h
  have hi : α ^ i ≠ 0 := pow_ne_zero i hα
  have : α ^ i * α ^ d = α ^ i * 1 := by rw [mul_one]; exact h
  exact mul_left_cancel₀ hi this

/-! ## A1. Queue-validity from the transition gate — no hypothesis on `α` -/

/-- **The transition gate `count(i) ≠ ln(i)` for `i < h` forces queue-validity**, with no
condition on `α`.  Induction: `q(0) = k ≥ 1`; if `q(i) ≥ 1` then `q(i+1) ≥ 0`, and
`q(i+1) = 0` would make `count(i+1) = ln(i+1)` as the syntactic identity `α^n = α^n`. -/
theorem lt_of_ratio_gate {fo : ℕ → ℕ} {α : K} {k h : ℕ} (hk : 1 ≤ k)
    (hgate : ∀ i, 1 ≤ i → i < h → α ^ (k + Sf fo i) ≠ α ^ i) :
    ∀ i, i < h → i < k + Sf fo i := by
  intro i
  induction i with
  | zero => intro _; rw [Sf_zero]; omega
  | succ m ih =>
    intro hm
    have ihm : m < k + Sf fo m := ih (by omega)
    have hge : m + 1 ≤ k + Sf fo (m + 1) := by rw [Sf_succ]; omega
    rcases lt_or_eq_of_le hge with hlt | heq
    · exact hlt
    · have heq' : α ^ (k + Sf fo (m + 1)) = α ^ (m + 1) := by rw [← heq]
      exact absurd heq' (hgate (m + 1) (by omega) hm)

theorem bfsValidF_of_ratio_gate {fo : ℕ → ℕ} {α : K} {k h : ℕ} (hk : 1 ≤ k)
    (hgate : ∀ i, 1 ≤ i → i < h → α ^ (k + Sf fo i) ≠ α ^ i) :
    BFSValidF k fo h := by
  intro i hi1 hih
  have := lt_of_ratio_gate hk hgate (i - 1) (by omega)
  omega

/-- Single tree: `k = 1`. -/
theorem bfsValid_of_ratio_gate {fo : ℕ → ℕ} {α : K} {h : ℕ}
    (hgate : ∀ i, 1 ≤ i → i < h → α ^ (1 + Sf fo i) ≠ α ^ i) :
    BFSValid fo h :=
  bfsValidF_of_ratio_gate (le_refl 1) hgate

/-! ## A2. Tiling from the terminal gate — the exact order condition -/

/-- **The terminal gate `count(h) = ln(h)` forces the tiling** under
`k + Sf fo h − h < orderOf α` (the terminal overshoot is below the order of `α`). -/
theorem tiling_of_ratio_gate {fo : ℕ → ℕ} {α : K} {k h : ℕ} (hk : 1 ≤ k) (hh : 1 ≤ h)
    (hgate : ∀ i, 1 ≤ i → i < h → α ^ (k + Sf fo i) ≠ α ^ i)
    (hterm : α ^ (k + Sf fo h) = α ^ h)
    (hord : k + Sf fo h - h < orderOf α) :
    k + Sf fo h = h := by
  have hv := bfsValidF_of_ratio_gate hk hgate
  have hle : h ≤ k + Sf fo h := by
    have := hv h hh (le_refl h)
    have := Sf_mono fo (Nat.sub_le h 1)
    omega
  obtain ⟨d, hd⟩ : ∃ d, k + Sf fo h = h + d := ⟨k + Sf fo h - h, by omega⟩
  have hdlt : d < orderOf α := by omega
  have hpos : 0 < orderOf α := lt_of_le_of_lt (Nat.zero_le d) hdlt
  have hα : α ≠ 0 := ne_zero_of_orderOf_pos hpos
  rw [hd] at hterm
  have h1 : α ^ d = 1 := pow_eq_one_of_pow_add_eq hα hterm
  have hdvd : orderOf α ∣ d := orderOf_dvd_of_pow_eq_one h1
  have hd0 : d = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hdlt
  omega

/-- **The ratio gate, from `Walk.WalkSat` with `initial_count = α^k`:** queue-validity and
tiling of the committed fanout column.  The only side condition is on the terminal gate. -/
theorem walk_ratio_gate_sound {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed : K} {k h : ℕ}
    (hw : WalkSat cur chld' fo ln count acc α seed (α ^ k) h) (hk : 1 ≤ k)
    (hgate : ∀ i, 1 ≤ i → i < h → count i ≠ ln i) (hterm : count h = ln h)
    (hord : k + Sf fo h - h < orderOf α) :
    BFSValidF k fo h ∧ k + Sf fo h = h := by
  have hcount : ∀ i, 1 ≤ i → i ≤ h → count i = α ^ (k + Sf fo i) := by
    intro i hi1 hih
    rw [count_closed hw i hi1 hih, pow_add]
  have hln := ln_closed hw
  have hgate' : ∀ i, 1 ≤ i → i < h → α ^ (k + Sf fo i) ≠ α ^ i := by
    intro i hi1 hih
    rw [← hcount i hi1 (le_of_lt hih), ← hln i hi1 (le_of_lt hih)]
    exact hgate i hi1 hih
  have hterm' : α ^ (k + Sf fo h) = α ^ h := by
    rw [← hcount h hw.hpos (le_refl h), ← hln h hw.hpos (le_refl h)]
    exact hterm
  exact ⟨bfsValidF_of_ratio_gate hk hgate',
    tiling_of_ratio_gate hk hw.hpos hgate' hterm' hord⟩

/-- Single tree, recognizer inputs. -/
theorem walk_ratio_gate_sound_tree {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed : K} {h : ℕ}
    (hw : WalkSat cur chld' fo ln count acc α seed α h)
    (hgate : ∀ i, 1 ≤ i → i < h → count i ≠ ln i) (hterm : count h = ln h)
    (hord : 1 + Sf fo h - h < orderOf α) :
    BFSValid fo h ∧ Sf fo h + 1 = h := by
  have hw' : WalkSat cur chld' fo ln count acc α seed (α ^ 1) h := by simpa using hw
  obtain ⟨hv, ht⟩ := walk_ratio_gate_sound hw' (le_refl 1) hgate hterm hord
  exact ⟨hv, by omega⟩

/-! ## A3. The characteristic is the wrong quantity -/

/-- One row, root declares two children. -/
def fo2 : ℕ → ℕ := fun _ => 2

theorem fo2_Sf_one : 1 + Sf fo2 1 = 3 := by rw [Sf_one]; rfl

/-- **At `α = −1` the ratio gate accepts a non-tiling table in EVERY field**: `h = 1`, the
transition gate is vacuous, the terminal gate reads `(−1)^3 = (−1)^1`, and `1 + Sf = 3 ≠ 1`.
The `QGate`-style characteristic bound `1 + Sf fo h < p` holds for every `p ≥ 5` and does not
help: what matters is `orderOf α` (`= 2 ≤ d = 2` here), not `p`. -/
theorem char_bound_does_not_suffice :
    (∀ i, 1 ≤ i → i < 1 → (-1 : K) ^ (1 + Sf fo2 i) ≠ (-1 : K) ^ i) ∧
      (-1 : K) ^ (1 + Sf fo2 1) = (-1 : K) ^ 1 ∧ 1 + Sf fo2 1 ≠ 1 := by
  refine ⟨fun i hi1 hi0 => absurd (lt_of_le_of_lt hi1 hi0) (by omega), ?_, ?_⟩
  · rw [fo2_Sf_one]; norm_num
  · rw [fo2_Sf_one]; norm_num

/-! ## A4. The soundness price of the terminal gate -/

/-- On a queue-valid but NON-tiling committed column, an accepting `α` for the terminal gate is
`0` or a `d`-th root of unity, `d = k + Sf fo h − h ≥ 1`. -/
theorem nontiling_accepting_alphas_subset {fo : ℕ → ℕ} {k h : ℕ} (hh : 1 ≤ h)
    (hv : BFSValidF k fo h) (α : K)
    (hterm : α ^ (k + Sf fo h) = α ^ h) :
    α = 0 ∨ α ^ (k + Sf fo h - h) = 1 := by
  have hle : h ≤ k + Sf fo h := by
    have := hv h hh (le_refl h)
    have := Sf_mono fo (Nat.sub_le h 1)
    omega
  by_cases hα : α = 0
  · exact Or.inl hα
  · right
    obtain ⟨d, hd⟩ : ∃ d, k + Sf fo h = h + d := ⟨k + Sf fo h - h, by omega⟩
    have : k + Sf fo h - h = d := by omega
    rw [this]
    rw [hd] at hterm
    exact pow_eq_one_of_pow_add_eq hα hterm

section Card
variable [Fintype K] [DecidableEq K]

/-- `#{α : α^d = 1} ≤ d` for `d ≥ 1` (`Polynomial.card_nthRoots`). -/
theorem terminal_event_card_le {d : ℕ} (hd : 0 < d) :
    (Finset.univ.filter (fun a : K => a ^ d = 1)).card ≤ d := by
  have hset : (Finset.univ.filter (fun a : K => a ^ d = 1)) = (nthRoots d (1 : K)).toFinset := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Multiset.mem_toFinset,
      mem_nthRoots hd]
  rw [hset]
  exact le_trans (Multiset.toFinset_card_le _) (card_nthRoots d 1)

/-- The terminal gate's bad-coin event on a fixed queue-valid non-tiling column has size
`≤ d + 1` with `d = k + Sf fo h − h`: the paper's `O(h)/|𝕂|` order, and at
arity `n` (`Sf fo h ≤ h·n`, `Walk.Sf_le_mul`) `≤ k + h·(n − 1) + 1`. -/
theorem terminal_bad_event_card_le {fo : ℕ → ℕ} {k h : ℕ} (hh : 1 ≤ h)
    (hv : BFSValidF k fo h) (hne : k + Sf fo h ≠ h) :
    (Finset.univ.filter (fun a : K => a ^ (k + Sf fo h) = a ^ h)).card
      ≤ (k + Sf fo h - h) + 1 := by
  have hle : h ≤ k + Sf fo h := by
    have := hv h hh (le_refl h)
    have := Sf_mono fo (Nat.sub_le h 1)
    omega
  have hd : 0 < k + Sf fo h - h := by have := hne; omega
  have hsub : (Finset.univ.filter (fun a : K => a ^ (k + Sf fo h) = a ^ h))
      ⊆ (Finset.univ.filter (fun a : K => a ^ (k + Sf fo h - h) = 1)) ∪ {0} := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rcases nontiling_accepting_alphas_subset hh hv a ha.2 with h0 | h1
    · exact Finset.mem_union_right _ (by simp [h0])
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  have := terminal_event_card_le (K := K) hd
  simp only [Finset.card_singleton]
  omega

end Card

/-! ## Completeness: honest columns pass at every `α` of order `≥ h` -/

/-- **Honest completeness of the ratio gate.**  On a queue-valid tiling column, the transition
gate holds at every row `i < h` and the terminal gate holds, provided `h ≤ orderOf α`: the
honest queue length `q(i) = k + Sf fo i − i` satisfies `1 ≤ q(i) ≤ h − 1 < orderOf α`. -/
theorem honest_ratio_gate {fo : ℕ → ℕ} {α : K} {k h : ℕ}
    (hv : BFSValidF k fo h) (ht : k + Sf fo h = h) (hord : h ≤ orderOf α) :
    (∀ i, 1 ≤ i → i < h → α ^ (k + Sf fo i) ≠ α ^ i) ∧ α ^ (k + Sf fo h) = α ^ h := by
  refine ⟨?_, by rw [ht]⟩
  intro i hi1 hih heq
  have hq : i + 1 ≤ k + Sf fo i := by
    have := hv (i + 1) (by omega) hih
    simpa using this
  obtain ⟨d, hd⟩ : ∃ d, k + Sf fo i = i + d := ⟨k + Sf fo i - i, by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hdlt : d < orderOf α := by
    have := Sf_mono fo (le_of_lt hih)
    omega
  have hpos : 0 < orderOf α := lt_of_le_of_lt (Nat.zero_le d) hdlt
  have hα : α ≠ 0 := ne_zero_of_orderOf_pos hpos
  rw [hd] at heq
  have h1 : α ^ d = 1 := pow_eq_one_of_pow_add_eq hα heq
  have hdvd : orderOf α ∣ d := orderOf_dvd_of_pow_eq_one h1
  have := Nat.le_of_dvd hd1 hdvd
  omega

/-! ## B1. Degenerate coins -/

/-- At `α = 0` the transition gate is unsatisfiable for `h ≥ 2` (`count(1) = ln(1) = 0`). -/
theorem alpha_zero_gate_unsat {fo : ℕ → ℕ} {k h : ℕ} (hk : 1 ≤ k) (hh : 2 ≤ h) :
    ¬ (∀ i, 1 ≤ i → i < h → (0 : K) ^ (k + Sf fo i) ≠ (0 : K) ^ i) := by
  intro hgate
  apply hgate 1 (le_refl 1) (by omega)
  rw [zero_pow (by omega), zero_pow (by omega)]

/-- At `α = 1` the transition gate is unsatisfiable for `h ≥ 2` (`count ≡ ln ≡ 1`). -/
theorem alpha_one_gate_unsat {fo : ℕ → ℕ} {k h : ℕ} (hh : 2 ≤ h) :
    ¬ (∀ i, 1 ≤ i → i < h → (1 : K) ^ (k + Sf fo i) ≠ (1 : K) ^ i) := by
  intro hgate
  apply hgate 1 (le_refl 1) (by omega)
  simp

end Generic

/-! ## Records -/

/-- The walk coin is not the theorem's timestamp coin; the compiler's walk coin is `0`.

The `hwin` entry below, "bounds the TIMESTAMP coin only", is
the record as of this batch.  Repair (ii) retyped `hwin` to the pair
`programAcc … + 3 < orderOf α ∧ programMemShape α … ≤ orderOf α`, so it now also bounds the memory
walk's line numbers, and the generator builds the memory walk at `α`.  The string is left as written. -/
def compilerWalkAlphaRecord : List (String × String) :=
  [("alphaC", "JointCoins.lean: ω.1.1; compute challenge slot 6 (walkChallengeBase); a sampled coin"),
    ("timestamp α", "OptimizedStrictFullPackage.honestJointCoins: cfg.challenges.α, separate coordinate"),
    ("hwin", "nockCompiles_zmod: programAcc + 3 < orderOf α bounds the TIMESTAMP coin only"),
    ("compiler walk α", "GenNockCompilesBounded.lean:447,639: `… hcard 0 0 0 (fun _ => 0) 0` — both walk αs are 0"),
    ("consequence", "alpha_zero_gate_unsat: at the compiler's own triple the ratio gate rejects every h ≥ 2")]

theorem compilerWalkAlphaRecord_length : compilerWalkAlphaRecord.length = 5 := by decide

/-- Side conditions of the ratio form, exact. -/
def sideConditions : List (String × String) :=
  [("soundness / queue-validity", "none (bfsValidF_of_ratio_gate)"),
    ("soundness / tiling", "k + Sf fo h − h < orderOf α; priced ≤ (d+1)/|K| (terminal_bad_event_card_le)"),
    ("completeness", "h ≤ orderOf α (honest_ratio_gate); fails at α ∈ {0, 1} and at small order"),
    ("characteristic", "irrelevant: char_bound_does_not_suffice")]

theorem sideConditions_length : sideConditions.length = 4 := by decide

end Nock.RedTeam.Batch478

#print axioms Nock.RedTeam.Batch478.bfsValidF_of_ratio_gate
#print axioms Nock.RedTeam.Batch478.tiling_of_ratio_gate
#print axioms Nock.RedTeam.Batch478.walk_ratio_gate_sound
#print axioms Nock.RedTeam.Batch478.walk_ratio_gate_sound_tree
#print axioms Nock.RedTeam.Batch478.char_bound_does_not_suffice
#print axioms Nock.RedTeam.Batch478.terminal_bad_event_card_le
#print axioms Nock.RedTeam.Batch478.honest_ratio_gate
#print axioms Nock.RedTeam.Batch478.alpha_zero_gate_unsat
#print axioms Nock.RedTeam.Batch478.alpha_one_gate_unsat
