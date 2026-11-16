/-
the NEGATIVE theorem. Merkle commitments over words with
succinct (query-based) verification do NOT have unique accepted commitments: flipping ONE word position
outside the queried set gives a different root and an accepted proof, with probability ≥ 1 − l/N.

MODEL (all explicit):
* A binary Merkle tree of depth `n` over `N = 2^n` words `w : ℕ → α` (positions `off … off + 2^n − 1`),
  leaf hash `L : α → Y`, node hash `H : Y → Y → Y`; `root`, the authentication path `auth` (sibling roots,
  top-down), and the path check `rootOf` are concrete and computable. The hash is ABSTRACT: the
  collision-freeness the theorems need is the hypothesis `Inj L H` (injective on the inputs involved; in
  the ROM this holds except with the collision probability, which only strengthens the negative result:
  the counterexample needs no collision).
* The succinct verifier reads the root, opened values at the query set `S` with their paths, and a local
  check `chk S vals` on the opened values only (`Local chk`: it depends on `vals` only on `S`). This is the
  proximity test / constraint check at the queried positions (it may be any such predicate).
* The query set is `S(s) = {s k | k < l}` for `s : Fin l → Fin N`, the `l` FS-derived positions. Because
  the FS coins of the second proof come from the random oracle at the NEW root, `s` is uniform and independent
  of the flipped position `j` (fixed before the root is hashed). `prob` is the exact counting measure.
CORRECTION to the brief: the openings at `S` of `w′` are NOT literally identical to those of `w` (sibling
hashes along a path can change when `j` lies in a sibling subtree). What is identical is the opened VALUES;
each opening verifies against its own root (`opening_complete`). Hence two ACCEPTED proofs, DIFFERENT roots.
-/
import Mathlib

set_option autoImplicit false

namespace NockvmE2E.Ung

open Finset

section Tree

variable {α Y : Type} (L : α → Y) (H : Y → Y → Y)

/-- Merkle root of the `2^n` words at `off, …, off + 2^n − 1`. -/
def root : ℕ → (ℕ → α) → ℕ → Y
  | 0, w, off => L (w off)
  | n + 1, w, off => H (root n w off) (root n w (off + 2 ^ n))

/-- Authentication path (sibling roots, top-down) of the word at relative position `i`. -/
def auth : ℕ → (ℕ → α) → ℕ → ℕ → List Y
  | 0, _, _, _ => []
  | n + 1, w, off, i =>
      if i < 2 ^ n then root L H n w (off + 2 ^ n) :: auth n w off i
      else root L H n w off :: auth n w (off + 2 ^ n) (i - 2 ^ n)

/-- The root recomputed from an opened value `a` at relative position `i` and a path. -/
def rootOf : ℕ → ℕ → α → List Y → Option Y
  | 0, _, a, [] => some (L a)
  | 0, _, _, _ :: _ => none
  | _ + 1, _, _, [] => none
  | n + 1, i, a, s :: ss =>
      (rootOf n (i % 2 ^ n) a ss).map fun r => if i < 2 ^ n then H r s else H s r

/-- **Opening completeness**: the honest path of position `i` verifies against the honest root. -/
theorem opening_complete : ∀ (n : ℕ) (w : ℕ → α) (off i : ℕ), i < 2 ^ n →
    rootOf L H n i (w (off + i)) (auth L H n w off i) = some (root L H n w off)
  | 0, w, off, i, hi => by
      have : i = 0 := by simpa using hi
      subst this; simp [rootOf, auth, root]
  | n + 1, w, off, i, hi => by
      have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      by_cases h : i < 2 ^ n
      · simp only [auth, h, ite_true, rootOf, Nat.mod_eq_of_lt h]
        rw [opening_complete n w off i h]
        simp [root]
      · have hlt : i - 2 ^ n < 2 ^ n := by omega
        simp only [auth, h, ite_false, rootOf]
        have hm : i % 2 ^ n = i - 2 ^ n := by
          have : i = (i - 2 ^ n) + 2 ^ n := by omega
          conv_lhs => rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
        have hw : off + i = off + 2 ^ n + (i - 2 ^ n) := by omega
        rw [hm, hw, opening_complete n w (off + 2 ^ n) (i - 2 ^ n) hlt]
        simp [root]

/-- Collision-freeness on the inputs involved, as a hypothesis (injective leaf and node hashes). -/
structure Inj : Prop where
  leaf : Function.Injective L
  node : ∀ a b c d, H a b = H c d → a = c ∧ b = d

variable {L H}

/-- Equal roots force equal words at every position (collision-free hash). -/
theorem root_inj (h : Inj L H) : ∀ (n : ℕ) (w w' : ℕ → α) (off : ℕ),
    root L H n w off = root L H n w' off → ∀ i, i < 2 ^ n → w (off + i) = w' (off + i)
  | 0, w, w', off, e, i, hi => by
      have : i = 0 := by simpa using hi
      subst this; simpa [root] using h.leaf e
  | n + 1, w, w', off, e, i, hi => by
      obtain ⟨e1, e2⟩ := h.node _ _ _ _ (by simpa only [root] using e)
      by_cases hn : i < 2 ^ n
      · exact root_inj h n w w' off e1 i hn
      · have hlt : i - 2 ^ n < 2 ^ n := by
          have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
          omega
        have := root_inj h n w w' (off + 2 ^ n) e2 (i - 2 ^ n) hlt
        have hw : off + i = off + 2 ^ n + (i - 2 ^ n) := by omega
        rw [hw]; exact this

end Tree

section Flip

variable {α Y : Type} {L : α → Y} {H : Y → Y → Y}

/-- A local check on the opened values: it reads `vals` only on the queried set. -/
def Local (chk : Finset ℕ → (ℕ → α) → Prop) : Prop :=
  ∀ S v v', (∀ i ∈ S, v i = v' i) → (chk S v ↔ chk S v')

/-- The succinct verifier: every opening in `S` verifies against `rt`, and the local check on the opened
values holds. -/
def Acc (L : α → Y) (H : Y → Y → Y) (n : ℕ) (chk : Finset ℕ → (ℕ → α) → Prop) (rt : Y) (S : Finset ℕ)
    (vals : ℕ → α) (pf : ℕ → List Y) : Prop :=
  (∀ i ∈ S, rootOf L H n i (vals i) (pf i) = some rt) ∧ chk S vals

/-- The honest proof of word `w` on query set `S`. -/
def AccHonest (L : α → Y) (H : Y → Y → Y) (n : ℕ) (chk : Finset ℕ → (ℕ → α) → Prop)
    (w : ℕ → α) (S : Finset ℕ) : Prop :=
  Acc L H n chk (root L H n w 0) S w (auth L H n w 0)

theorem accHonest_iff {n : ℕ} {chk : Finset ℕ → (ℕ → α) → Prop} {w : ℕ → α} {S : Finset ℕ}
    (hS : ∀ i ∈ S, i < 2 ^ n) : AccHonest L H n chk w S ↔ chk S w := by
  refine ⟨fun h => h.2, fun h => ⟨fun i hi => ?_, h⟩⟩
  simpa using opening_complete L H n w 0 i (hS i hi)

/-- **(i)** The flip changes the root. -/
theorem flip_root_ne (hI : Inj L H) {n : ℕ} (w : ℕ → α) {j : ℕ} (hj : j < 2 ^ n) {a : α}
    (ha : a ≠ w j) : root L H n (Function.update w j a) 0 ≠ root L H n w 0 := by
  intro e
  have := root_inj hI n _ _ 0 e j hj
  simp at this
  exact ha this

/-- **(ii)** The opened values at every `i ≠ j` are unchanged. -/
theorem flip_values (w : ℕ → α) {j : ℕ} {a : α} {S : Finset ℕ} (hjS : j ∉ S) :
    ∀ i ∈ S, Function.update w j a i = w i := fun i hi =>
  Function.update_of_ne (fun h => hjS (by rw [← h]; exact hi)) _ _

/-- **(iii)** A verifier that reads only the root-consistency of the openings at `S` and a local check on the
opened values accepts the flipped word's honest proof iff it accepts the original's. -/
theorem flip_accepts_iff (chk : Finset ℕ → (ℕ → α) → Prop) (hloc : Local chk) {n : ℕ} (w : ℕ → α)
    {S : Finset ℕ} (hS : ∀ i ∈ S, i < 2 ^ n) {j : ℕ} (hjS : j ∉ S) (a : α) :
    AccHonest L H n chk (Function.update w j a) S ↔ AccHonest L H n chk w S := by
  rw [accHonest_iff hS, accHonest_iff hS]
  exact hloc S _ _ (flip_values w hjS)

/-- **The negative theorem, deterministic form**: if `w` is accepted on `S` and `j ∉ S`, the one-leaf flip is
ALSO accepted on `S`, with a DIFFERENT root. Two accepted proofs, same queried openings' values, distinct
commitments. -/
theorem merkle_not_unique (hI : Inj L H) (chk : Finset ℕ → (ℕ → α) → Prop) (hloc : Local chk) {n : ℕ}
    (w : ℕ → α) {S : Finset ℕ} (hS : ∀ i ∈ S, i < 2 ^ n) {j : ℕ} (hj : j < 2 ^ n) (hjS : j ∉ S)
    {a : α} (ha : a ≠ w j) (hacc : AccHonest L H n chk w S) :
    AccHonest L H n chk (Function.update w j a) S ∧
      root L H n (Function.update w j a) 0 ≠ root L H n w 0 ∧
      (∀ i ∈ S, Function.update w j a i = w i) :=
  ⟨(flip_accepts_iff chk hloc w hS hjS a).mpr hacc, flip_root_ne hI w hj ha, flip_values w hjS⟩

end Flip

/-! ## Probability form -/

section Prob

/-- Exact counting probability over uniformly drawn query tuples `s : Fin l → Fin N`. -/
noncomputable def prob (l N : ℕ) (P : (Fin l → Fin N) → Prop) [DecidablePred P] : ℚ :=
  ((univ.filter P).card : ℚ) / (Fintype.card (Fin l → Fin N) : ℚ)

/-- The query set drawn by the tuple `s`. -/
def qset {l N : ℕ} (s : Fin l → Fin N) : Finset ℕ := univ.image fun k => (s k : ℕ)

private theorem card_fix (l N : ℕ) (k : Fin l) (j : Fin N) :
    (univ.filter fun s : Fin l → Fin N => s k = j).card = N ^ (l - 1) := by
  have : (univ.filter fun s : Fin l → Fin N => s k = j) =
      Fintype.piFinset (fun i => if i = k then {j} else univ) := by
    ext s; simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i; by_cases hi : i = k
      · subst hi; simp [h]
      · simp [hi]
    · intro h; simpa using h k
  rw [this, Fintype.card_piFinset]
  simp only [apply_ite card, card_singleton, card_univ, Fintype.card_fin]
  rw [Finset.prod_ite]
  simp [Finset.filter_ne', Finset.card_erase_of_mem]

/-- Union bound: `Pr[j ∈ S] ≤ l / N`. -/
theorem prob_mem_le (l N : ℕ) (j : Fin N) :
    prob l N (fun s => (j : ℕ) ∈ qset s) ≤ (l : ℚ) / N := by
  unfold prob
  rcases l with _ | m
  · have : (univ.filter fun s : Fin 0 → Fin N => (j : ℕ) ∈ qset s) = ∅ := by
      ext s; simp [qset, Finset.univ_eq_empty]
    rw [this]; simp
  · have hN : 0 < N := Fin.pos j
    have hsub : (univ.filter fun s : Fin (m + 1) → Fin N => (j : ℕ) ∈ qset s) ⊆
        univ.biUnion fun k => univ.filter fun s : Fin (m + 1) → Fin N => s k = j := by
      intro s hs
      simp only [mem_filter, mem_univ, true_and, qset, mem_image] at hs
      obtain ⟨k, hk⟩ := hs
      simp only [mem_biUnion, mem_univ, mem_filter, true_and]
      exact ⟨k, Fin.ext hk⟩
    have hc := (card_le_card hsub).trans (card_biUnion_le)
    simp only [card_fix, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, Nat.add_sub_cancel] at hc
    simp only [Fintype.card_fun, Fintype.card_fin]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : ((univ.filter fun s : Fin (m + 1) → Fin N => (j : ℕ) ∈ qset s).card : ℚ) ≤
        (((m + 1) * N ^ m : ℕ) : ℚ) := by exact_mod_cast hc
    have h2 := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℚ) N)
    push_cast at h2 ⊢
    have h3 : ((m : ℚ) + 1) * (N : ℚ) ^ m * N = ((m : ℚ) + 1) * (N : ℚ) ^ (m + 1) := by ring
    linarith

/-- Counting monotonicity. -/
theorem prob_mono {l N : ℕ} {P Q : (Fin l → Fin N) → Prop} [DecidablePred P] [DecidablePred Q] (h : ∀ s, P s → Q s) :
    prob l N P ≤ prob l N Q := by
  unfold prob
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast card_le_card (fun s hs => by
    simp only [mem_filter, mem_univ, true_and] at hs ⊢; exact h s hs)

theorem prob_union_le {l N : ℕ} (P Q : (Fin l → Fin N) → Prop) [DecidablePred P] [DecidablePred Q] :
    prob l N (fun s => P s ∨ Q s) ≤ prob l N P + prob l N Q := by
  unfold prob
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have : (univ.filter fun s => P s ∨ Q s) = (univ.filter P) ∪ (univ.filter Q) := by
    ext s; simp
  rw [this]
  exact_mod_cast card_union_le _ _

theorem prob_true (l N : ℕ) (hN : 0 < N) : prob l N (fun _ => True) = 1 := by
  unfold prob
  have h : (Fintype.card (Fin l → Fin N) : ℚ) ≠ 0 := by
    simp only [Fintype.card_fun, Fintype.card_fin]; positivity
  simp only [filter_true_of_mem (fun _ _ => trivial), card_univ]
  exact div_self h

end Prob

/-! ## The negative theorem, probability form -/

section Neg

open scoped Classical

variable {α Y : Type} {L : α → Y} {H : Y → Y → Y}

theorem qset_lt {l n : ℕ} (s : Fin l → Fin (2 ^ n)) : ∀ i ∈ qset s, i < 2 ^ n := by
  intro i hi
  simp only [qset, mem_image, mem_univ, true_and] at hi
  obtain ⟨k, rfl⟩ := hi
  exact (s k).isLt

/-- **Merkle ≠ unique, probability form (general `w`).** For every word `w`, flipped position `j` and
replacement `a ≠ w j`, with the flipped word's own FS query tuple `s` uniform and independent of `j`:
the roots differ (collision-free hash), and
`Pr_s[flipped word accepted] ≥ Pr_s[w accepted] − l/N`. -/
theorem merkle_flip_prob (hI : Inj L H) (chk : Finset ℕ → (ℕ → α) → Prop) (hloc : Local chk) (n l : ℕ)
    (w : ℕ → α) (j : Fin (2 ^ n)) {a : α} (ha : a ≠ w j) :
    root L H n (Function.update w j a) 0 ≠ root L H n w 0 ∧
    prob l (2 ^ n) (fun s => AccHonest L H n chk w (qset s)) - (l : ℚ) / (2 ^ n : ℕ) ≤
      prob l (2 ^ n) (fun s => AccHonest L H n chk (Function.update w j a) (qset s)) := by
  refine ⟨flip_root_ne hI w j.isLt ha, ?_⟩
  have h1 : prob l (2 ^ n) (fun s => AccHonest L H n chk w (qset s)) ≤
      prob l (2 ^ n) (fun s => AccHonest L H n chk (Function.update w j a) (qset s) ∨
        (j : ℕ) ∈ qset s) := prob_mono fun s hs => by
    by_cases hj : (j : ℕ) ∈ qset s
    · exact Or.inr hj
    · exact Or.inl ((flip_accepts_iff chk hloc w (qset_lt s) hj a).mpr hs)
  have h2 := prob_union_le (l := l) (N := 2 ^ n)
    (fun s => AccHonest L H n chk (Function.update w j a) (qset s)) (fun s => (j : ℕ) ∈ qset s)
  have h3 := prob_mem_le l (2 ^ n) j
  linarith

/-- **Merkle ≠ unique, honest form** (this is the `ε_uniq ≈ 1` statement): if the honest word `w` is
accepted on every query set (completeness of the local check), the one-leaf flip is accepted with
probability `≥ 1 − l/N`, under a DIFFERENT root. So two accepted proofs for the same statement with
different commitments exist except with probability `l/N`: `ε_uniq ≥ 1 − l/N`. -/
theorem merkle_ungrind_negative (hI : Inj L H) (chk : Finset ℕ → (ℕ → α) → Prop) (hloc : Local chk)
    (n l : ℕ) (w : ℕ → α) (hhon : ∀ S : Finset ℕ, (∀ i ∈ S, i < 2 ^ n) → chk S w)
    (j : Fin (2 ^ n)) {a : α} (ha : a ≠ w j) :
    root L H n (Function.update w j a) 0 ≠ root L H n w 0 ∧
    (∀ s : Fin l → Fin (2 ^ n), AccHonest L H n chk w (qset s)) ∧
    1 - (l : ℚ) / (2 ^ n : ℕ) ≤
      prob l (2 ^ n) (fun s => AccHonest L H n chk (Function.update w j a) (qset s)) := by
  have hall : ∀ s : Fin l → Fin (2 ^ n), AccHonest L H n chk w (qset s) := fun s =>
    (accHonest_iff (qset_lt s)).mpr (hhon _ (qset_lt s))
  refine ⟨flip_root_ne hI w j.isLt ha, hall, ?_⟩
  have h0 : prob l (2 ^ n) (fun s => AccHonest L H n chk w (qset s)) = 1 := by
    rw [← prob_true l (2 ^ n) (Nat.two_pow_pos n)]
    exact le_antisymm (prob_mono fun _ _ => trivial) (prob_mono fun s _ => hall s)
  have := (merkle_flip_prob hI chk hloc n l w j ha).2
  linarith

end Neg

/-! ## Non-vacuity: the hypotheses are satisfiable (free/injective hash) -/

/-- The free hash: leaf and node constructors. -/
inductive FreeTree (α : Type) : Type
  | leaf : α → FreeTree α
  | node : FreeTree α → FreeTree α → FreeTree α

theorem inj_free (α : Type) : Inj (FreeTree.leaf : α → FreeTree α) FreeTree.node where
  leaf a b h := by cases h; rfl
  node a b c d h := by cases h; exact ⟨rfl, rfl⟩

/-- With the free hash and the trivial local check, a concrete flip over `Bool` words of length 4:
the flipped word is accepted on every query set avoiding the flipped position, with a different root. -/
theorem merkle_not_unique_example :
    root (FreeTree.leaf : Bool → FreeTree Bool) FreeTree.node 2 (Function.update (fun _ => false) 3 true) 0 ≠
      root (FreeTree.leaf : Bool → FreeTree Bool) FreeTree.node 2 (fun _ => false) 0 :=
  flip_root_ne (inj_free Bool) (fun _ => false) (by norm_num) (by simp)

end NockvmE2E.Ung
