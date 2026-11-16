/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/OpenCoreWP1.lean

 **Trace uniqueness on the P1 fragment: the walk trie and the core walk columns.**

 * §1 **abstract BFS rows** (`BFSRows`): rows `0 .. n−1`, roots `0 .. kr−1`; row `i`'s `l`-th child sits at
 position `kr + P i + l` (`P i` = the fanouts of the rows before `i`) and carries the child step
 `(serial, 2·prefix + side, len + 1)`; every non-root row is such a child of an earlier row. **`bfs_unique_of_cover`**:
 two BFS row families with the same `n`, `kr`, strictly increasing root serials, each covering one key set `S`
 of `n` keys `(serial, prefix)`, agree on every row (flags, serial, prefix, length). The keys are distinct
 (`keys_inj`), the flags are read off the key set (`flag_iff`), the root serials are the key set's prefix-1
 part in increasing order (`strictMono_eq`), the rest is an induction along the BFS positions (`pos_inj`).
 * §2 **the walk forest as BFS rows** (`bfsRows_of_goal`): `ForestReconGoal` with the root gate, the queue
 validity, the fanout column and the axis bound gives `BFSRows` of the row labels (the positional lemma
 `flatMap_getElem?_pos` on `bfsForest ts = ts ++ (bfsForest ts).flatMap children`).
 * §3 the J-8 walk chip: `walkJ8_bfsRows` (outside the walk event) and the label fields as columns
 (`lbl_fields`).
 * §4 two accepted tuples: **`trie_eq`**, the trie columns `pre ridx len cL cR` agree at every row, and `idx` on
 the root rows; the cover comes either from the pin E10 (`cover_E10`, no path reads: one row, `idx = 0`) or
 from a covering key set `S` of `nW` keys (the honest read closure).
 * §5 **`r0W_auxW_r1W`**: `OpenP1.r0W`, `OpenP1.auxW` and `OpenP1.r1W` from `trie_eq`, `r0W_auxW_of_core` and the
 remaining named hypotheses (non-root `idx`, `mL mR`, `kL vL kR vR`, the round-1 labels), each stated given
 the trie agreement.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0WP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkForestP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1

noncomputable section

/-! ## 1. Abstract BFS rows -/

/-- Fanout of a state `(cL, cR)`. -/
def fo (s : Bool × Bool) : ℕ := (if s.1 then 1 else 0) + (if s.2 then 1 else 0)

/-- The side of child slot `l` (0-based): slot 0 is the left child when `cL`, else the right one. -/
def side (s : Bool × Bool) (l : ℕ) : Bool := if l = 0 then !s.1 else true

def bit (b : Bool) : ℕ := if b then 1 else 0

theorem fo_le_two {s : Bool × Bool} : fo s ≤ 2 := by
  rcases s with ⟨_ | _, _ | _⟩ <;> simp [fo]

/-- Prefix sum of fanouts of rows `< i`. -/
def P (st : ℕ → Bool × Bool) (i : ℕ) : ℕ := ∑ j ∈ Finset.range i, fo (st j)

/-- **BFS rows** (0-based, `n` rows, roots `0 .. kr−1`): row data `st` (child flags), `r` (root serial), `a`
(prefix), `d` (length). Every row's `l`-th child sits at position `kr + P i + l` and carries the child step;
every non-root row is such a child of an earlier row. -/
structure BFSRows (n kr : ℕ) (st : ℕ → Bool × Bool) (r a d : ℕ → ℕ) : Prop where
  kr_le : kr ≤ n
  root : ∀ j < kr, a j = 1 ∧ d j = 0
  child : ∀ i < n, ∀ l < fo (st i), kr + P st i + l < n ∧ r (kr + P st i + l) = r i ∧
    a (kr + P st i + l) = 2 * a i + bit (side (st i) l) ∧ d (kr + P st i + l) = d i + 1
  parent : ∀ m, kr ≤ m → m < n → ∃ i < m, ∃ l < fo (st i), m = kr + P st i + l

theorem P_succ (st : ℕ → Bool × Bool) (i : ℕ) : P st (i + 1) = P st i + fo (st i) := by
  simp [P, Finset.sum_range_succ]

theorem P_mono (st : ℕ → Bool × Bool) {i j : ℕ} (h : i ≤ j) : P st i ≤ P st j := by
  unfold P
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

/-- Positions of child slots are injective. -/
theorem pos_inj (st : ℕ → Bool × Bool) {i i' l l' : ℕ} (hl : l < fo (st i)) (hl' : l' < fo (st i'))
    (h : P st i + l = P st i' + l') : i = i' ∧ l = l' := by
  rcases lt_trichotomy i i' with hi | hi | hi
  · exfalso
    have := P_mono st (Nat.succ_le_of_lt hi)
    rw [P_succ] at this
    omega
  · subst hi; exact ⟨rfl, by omega⟩
  · exfalso
    have := P_mono st (Nat.succ_le_of_lt hi)
    rw [P_succ] at this
    omega

/-- `P` agrees on two flag families agreeing below `i`. -/
theorem P_congr {st st' : ℕ → Bool × Bool} {i : ℕ} (h : ∀ j < i, st j = st' j) : P st i = P st' i := by
  unfold P
  exact Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.mp hj)]

theorem side_false {s : Bool × Bool} {l : ℕ} (hl : l < fo s) (h : side s l = false) : l = 0 ∧ s.1 = true := by
  rcases s with ⟨_ | _, _ | _⟩ <;> simp [side, fo] at hl h ⊢ <;> omega

theorem side_true {s : Bool × Bool} {l : ℕ} (hl : l < fo s) (h : side s l = true) :
    s.2 = true ∧ l = (if s.1 then 1 else 0) := by
  rcases s with ⟨_ | _, _ | _⟩ <;> simp [side, fo] at hl h ⊢ <;> omega

section One
variable {n kr : ℕ} {st : ℕ → Bool × Bool} {r a d : ℕ → ℕ}

theorem a_pos (B : BFSRows n kr st r a d) : ∀ j < n, 1 ≤ a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hr : j < kr
    · rw [(B.root j hr).1]
    · obtain ⟨i, hi, l, hl, rfl⟩ := B.parent j (by omega) hj
      rw [(B.child i (by omega) l hl).2.2.1]
      have := ih i hi (by omega)
      omega

/-- Root rows are exactly the rows of prefix `1`. -/
theorem root_iff (B : BFSRows n kr st r a d) {j : ℕ} (hj : j < n) : j < kr ↔ a j = 1 := by
  constructor
  · intro h; exact (B.root j h).1
  · intro h
    by_contra hr
    obtain ⟨i, hi, l, hl, rfl⟩ := B.parent j (by omega) hj
    rw [(B.child i (by omega) l hl).2.2.1] at h
    have := a_pos B i (by omega)
    omega

/-- **Keys are distinct** once the roots' serials are. -/
theorem keys_inj (B : BFSRows n kr st r a d) (hroots : ∀ i < kr, ∀ j < kr, r i = r j → i = j) :
    ∀ N, ∀ i < N, ∀ j < N, i < n → j < n → r i = r j → a i = a j → i = j := by
  intro N
  induction N with
  | zero => intro i hi; omega
  | succ N ih =>
    intro i hi j hj hin hjn hr ha
    by_cases hik : i < kr <;> by_cases hjk : j < kr
    · exact hroots i hik j hjk hr
    · exfalso
      have h1 := (root_iff B hin).mp hik
      have h2 := (root_iff B hjn).not.mp hjk
      omega
    · exfalso
      have h1 := (root_iff B hjn).mp hjk
      have h2 := (root_iff B hin).not.mp hik
      omega
    · obtain ⟨i', hi', l, hl, rfl⟩ := B.parent i (by omega) hin
      obtain ⟨j', hj', l', hl', rfl⟩ := B.parent j (by omega) hjn
      obtain ⟨-, ri, ai, -⟩ := B.child i' (by omega) l hl
      obtain ⟨-, rj, aj, -⟩ := B.child j' (by omega) l' hl'
      rw [ri, rj] at hr
      rw [ai, aj] at ha
      have hb : bit (side (st i') l) = bit (side (st j') l') := by
        unfold bit at ha ⊢; split_ifs at ha ⊢ <;> omega
      have ha' : a i' = a j' := by unfold bit at hb ha; split_ifs at hb ha <;> omega
      have e := ih i' (by omega) j' (by omega) (by omega) (by omega) hr ha'
      subst e
      have hs : side (st i') l = side (st i') l' := by
        unfold bit at hb; split_ifs at hb with h1 h2 h2 <;> simp_all
      have hll : l = l' := by
        cases hsd : side (st i') l
        · rw [hsd] at hs
          exact (side_false hl hsd).1.trans (side_false hl' hs.symm).1.symm
        · rw [hsd] at hs
          exact (side_true hl hsd).2.trans (side_true hl' hs.symm).2.symm
      rw [hll]

/-- **The child flags are determined by the key set** (distinct keys). -/
theorem flag_iff (B : BFSRows n kr st r a d) (hinj : ∀ i < n, ∀ j < n, r i = r j → a i = a j → i = j)
    {i : ℕ} (hi : i < n) :
    ((st i).1 = true ↔ ∃ m < n, r m = r i ∧ a m = 2 * a i) ∧
      ((st i).2 = true ↔ ∃ m < n, r m = r i ∧ a m = 2 * a i + 1) := by
  have hpar : ∀ m < n, ∀ b : Bool, r m = r i → a m = 2 * a i + bit b →
      ∃ l < fo (st i), side (st i) l = b := by
    intro m hm b hr ha
    have hm1 : ¬ m < kr := by
      intro hmk
      have := (B.root m hmk).1
      have := a_pos B i hi
      unfold bit at ha; split_ifs at ha <;> omega
    obtain ⟨i', hi', l, hl, rfl⟩ := B.parent m (by omega) hm
    obtain ⟨-, ri, ai, -⟩ := B.child i' (by omega) l hl
    rw [ri] at hr
    rw [ai] at ha
    have hb : bit (side (st i') l) = bit b := by unfold bit at ha ⊢; split_ifs at ha ⊢ <;> omega
    have ha' : a i' = a i := by unfold bit at hb ha; split_ifs at hb ha <;> omega
    have e := hinj i' (by omega) i hi hr ha'
    subst e
    refine ⟨l, hl, ?_⟩
    unfold bit at hb; split_ifs at hb with h1 h2 h2 <;> simp_all
  refine ⟨⟨fun h => ?_, fun ⟨m, hm, hr, ha⟩ => ?_⟩, ⟨fun h => ?_, fun ⟨m, hm, hr, ha⟩ => ?_⟩⟩
  · have hl : 0 < fo (st i) := by unfold fo; rw [if_pos h]; omega
    obtain ⟨hlt, hr, ha, -⟩ := B.child i hi 0 hl
    refine ⟨_, hlt, hr, ?_⟩
    rw [ha]; simp [side, h, bit]
  · obtain ⟨l, hl, hs⟩ := hpar m hm false hr (by simpa [bit] using ha)
    exact (side_false hl hs).2
  · have hl : (if (st i).1 then 1 else 0) < fo (st i) := by unfold fo; rw [if_pos h]; split_ifs <;> omega
    obtain ⟨hlt, hr, ha, -⟩ := B.child i hi _ hl
    refine ⟨_, hlt, hr, ?_⟩
    rw [ha]
    have : side (st i) (if (st i).1 then 1 else 0) = true := by
      unfold side; split_ifs with h1 h2 <;> simp_all
    simp [this, bit]
  · obtain ⟨l, hl, hs⟩ := hpar m hm true hr (by simpa [bit] using ha)
    exact (side_true hl hs).1

end One

/-- Two strictly increasing families on `[0, k)` with the same value set agree. -/
theorem strictMono_eq {k : ℕ} {f g : ℕ → ℕ} (hf : ∀ i j, i < j → j < k → f i < f j)
    (hg : ∀ i j, i < j → j < k → g i < g j)
    (hset : ∀ x, (∃ i < k, f i = x) ↔ (∃ i < k, g i = x)) : ∀ i < k, f i = g i := by
  let f' : Fin k → ℕ := fun i => f i
  let g' : Fin k → ℕ := fun i => g i
  have hf' : StrictMono f' := fun i j hij => hf i j hij j.isLt
  have hg' : StrictMono g' := fun i j hij => hg i j hij j.isLt
  have hr : Set.range f' = Set.range g' := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj, e⟩ := (hset (f i)).mp ⟨i, i.isLt, rfl⟩
      exact ⟨⟨j, hj⟩, e⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj, e⟩ := (hset (g i)).mpr ⟨i, i.isLt, rfl⟩
      exact ⟨⟨j, hj⟩, e⟩
  have := (hf'.range_inj_of_wellFoundedLT hg').mp hr
  intro i hi
  exact congrFun this ⟨i, hi⟩

/-- **BFS rows are determined by their key set and root order.** Two BFS row families with the same `n`, `kr`,
strictly increasing root serials and the same key set `{(r j, a j)}` agree on every row. -/
theorem bfs_unique {n kr : ℕ} {st st' : ℕ → Bool × Bool} {r a d r' a' d' : ℕ → ℕ}
    (B : BFSRows n kr st r a d) (B' : BFSRows n kr st' r' a' d')
    (hmono : ∀ i j, i < j → j < kr → r i < r j) (hmono' : ∀ i j, i < j → j < kr → r' i < r' j)
    (hset : ∀ x y, (∃ j < n, r j = x ∧ a j = y) ↔ (∃ j < n, r' j = x ∧ a' j = y)) :
    ∀ j < n, st j = st' j ∧ r j = r' j ∧ a j = a' j ∧ d j = d' j := by
  have hroots : ∀ i < kr, ∀ j < kr, r i = r j → i = j := by
    intro i hi j hj e
    rcases lt_trichotomy i j with h | h | h
    · have := hmono i j h hj; omega
    · exact h
    · have := hmono j i h hi; omega
  have hroots' : ∀ i < kr, ∀ j < kr, r' i = r' j → i = j := by
    intro i hi j hj e
    rcases lt_trichotomy i j with h | h | h
    · have := hmono' i j h hj; omega
    · exact h
    · have := hmono' j i h hi; omega
  have hinj : ∀ i < n, ∀ j < n, r i = r j → a i = a j → i = j := fun i hi j hj =>
    keys_inj B hroots (n + 1) i (by omega) j (by omega) hi hj
  have hinj' : ∀ i < n, ∀ j < n, r' i = r' j → a' i = a' j → i = j := fun i hi j hj =>
    keys_inj B' hroots' (n + 1) i (by omega) j (by omega) hi hj
  -- the root serials agree
  have hr0 : ∀ i < kr, r i = r' i := by
    refine strictMono_eq hmono hmono' fun x => ⟨fun ⟨i, hi, e⟩ => ?_, fun ⟨i, hi, e⟩ => ?_⟩
    · obtain ⟨j, hj, e1, e2⟩ := (hset x 1).mp ⟨i, by have := B.kr_le; omega, e, (B.root i hi).1⟩
      exact ⟨j, (root_iff B' hj).mpr e2, e1⟩
    · obtain ⟨j, hj, e1, e2⟩ := (hset x 1).mpr ⟨i, by have := B'.kr_le; omega, e, (B'.root i hi).1⟩
      exact ⟨j, (root_iff B hj).mpr e2, e1⟩
  -- flags from keys
  have hst : ∀ j < n, r j = r' j → a j = a' j → st j = st' j := by
    intro j hj er ea
    obtain ⟨f1, f2⟩ := flag_iff B hinj hj
    obtain ⟨g1, g2⟩ := flag_iff B' hinj' hj
    have e1 : (st j).1 = (st' j).1 := by
      rw [Bool.eq_iff_iff, f1, g1, er, ea]
      exact ⟨fun ⟨m, hm, h1, h2⟩ => (hset _ _).mp ⟨m, hm, h1, h2⟩,
        fun ⟨m, hm, h1, h2⟩ => (hset _ _).mpr ⟨m, hm, h1, h2⟩⟩
    have e2 : (st j).2 = (st' j).2 := by
      rw [Bool.eq_iff_iff, f2, g2, er, ea]
      exact ⟨fun ⟨m, hm, h1, h2⟩ => (hset _ _).mp ⟨m, hm, h1, h2⟩,
        fun ⟨m, hm, h1, h2⟩ => (hset _ _).mpr ⟨m, hm, h1, h2⟩⟩
    exact Prod.ext e1 e2
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hjk : j < kr
    · have er := hr0 j hjk
      have ea : a j = a' j := by rw [(B.root j hjk).1, (B'.root j hjk).1]
      exact ⟨hst j hj er ea, er, ea, by rw [(B.root j hjk).2, (B'.root j hjk).2]⟩
    · obtain ⟨i, hi, l, hl, hpos⟩ := B.parent j (by omega) hj
      obtain ⟨i', hi', l', hl', hpos'⟩ := B'.parent j (by omega) hj
      -- the decompositions agree
      have hPc : ∀ m, m < max i i' + 1 → P st m = P st' m := by
        intro m hm
        exact P_congr fun x hx => (ih x (by omega) (by omega)).1
      have hfo : fo (st' i') = fo (st i') := by rw [(ih i' hi' (by omega)).1]
      have e : P st i + l = P st i' + l' := by
        rw [hPc i' (by omega)]; omega
      obtain ⟨rfl, rfl⟩ := pos_inj st hl (by rw [← hfo]; exact hl') e
      obtain ⟨hs, hr, ha, hd⟩ := ih i hi (by omega)
      obtain ⟨-, r1, a1, d1⟩ := B.child i (by omega) l hl
      have hl2 : l < fo (st' i) := by rw [← hs]; exact hl
      obtain ⟨-, r2, a2, d2⟩ := B'.child i (by omega) l hl2
      rw [← hpos] at r1 a1 d1
      rw [← hpos'] at r2 a2 d2
      have er : r j = r' j := by rw [r1, r2, hr]
      have ea : a j = a' j := by rw [a1, a2, ha, hs]
      exact ⟨hst j hj er ea, er, ea, by rw [d1, d2, hd]⟩

/-- **The key set is a covering set of the right size.** Distinct keys over `n` rows covering a set `S` of `n`
keys are exactly `S`. -/
theorem keyset_eq_of_cover {n : ℕ} {r a : ℕ → ℕ} (hinj : ∀ i < n, ∀ j < n, r i = r j → a i = a j → i = j)
    (S : Finset (ℕ × ℕ)) (hS : S.card = n) (hcov : ∀ s ∈ S, ∃ j < n, r j = s.1 ∧ a j = s.2) :
    ∀ x y, (∃ j < n, r j = x ∧ a j = y) ↔ (x, y) ∈ S := by
  classical
  set T := (Finset.range n).image fun j => (r j, a j) with hT
  have hTc : T.card = n := by
    rw [hT, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj e
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    simp only [Prod.mk.injEq] at e
    exact hinj i hi j hj e.1 e.2
  have hsub : S ⊆ T := by
    intro s hs
    obtain ⟨j, hj, e1, e2⟩ := hcov s hs
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, by rw [e1, e2]⟩
  have heq : S = T := Finset.eq_of_subset_of_card_le hsub (by rw [hS, hTc])
  intro x y
  rw [heq, hT, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl, rfl⟩; exact ⟨j, Finset.mem_range.mpr hj, rfl⟩
  · rintro ⟨j, hj, e⟩
    simp only [Prod.mk.injEq] at e
    exact ⟨j, Finset.mem_range.mp hj, e.1, e.2⟩

/-- **Two BFS row families covering one key set of `n` keys agree**, given strictly increasing root serials. -/
theorem bfs_unique_of_cover {n kr : ℕ} {st st' : ℕ → Bool × Bool} {r a d r' a' d' : ℕ → ℕ}
    (B : BFSRows n kr st r a d) (B' : BFSRows n kr st' r' a' d')
    (hmono : ∀ i j, i < j → j < kr → r i < r j) (hmono' : ∀ i j, i < j → j < kr → r' i < r' j)
    (S : Finset (ℕ × ℕ)) (hS : S.card = n)
    (hcov : ∀ s ∈ S, ∃ j < n, r j = s.1 ∧ a j = s.2) (hcov' : ∀ s ∈ S, ∃ j < n, r' j = s.1 ∧ a' j = s.2) :
    ∀ j < n, st j = st' j ∧ r j = r' j ∧ a j = a' j ∧ d j = d' j := by
  have hroots : ∀ (r : ℕ → ℕ), (∀ i j, i < j → j < kr → r i < r j) → ∀ i < kr, ∀ j < kr, r i = r j → i = j := by
    intro r hm i hi j hj e
    rcases lt_trichotomy i j with h | h | h
    · have := hm i j h hj; omega
    · exact h
    · have := hm j i h hi; omega
  have h1 := keyset_eq_of_cover (fun i hi j hj => keys_inj B (hroots r hmono) (n + 1) i (by omega) j (by omega) hi hj)
    S hS hcov
  have h2 := keyset_eq_of_cover (fun i hi j hj => keys_inj B' (hroots r' hmono') (n + 1) i (by omega) j (by omega)
    hi hj) S hS hcov'
  exact bfs_unique B B' hmono hmono' fun x y => (h1 x y).trans (h2 x y).symm



/-! ## 2. The walk forest as BFS rows -/

theorem flatMap_getElem?_pos {α β : Type*} (f : α → List β) :
    ∀ (L : List α) (i l : ℕ) (hi : i < L.length), l < (f L[i]).length →
      (L.flatMap f)[((L.take i).flatMap f).length + l]? = (f L[i])[l]?
  | [], i, l, hi, _ => absurd hi (by simp)
  | x :: L, 0, l, _, hl => by
    simp only [List.take_zero, List.flatMap_nil, List.length_nil, zero_add, List.flatMap_cons,
      List.getElem_cons_zero] at hl ⊢
    rw [List.getElem?_append_left hl]
  | x :: L, i + 1, l, hi, hl => by
    simp only [List.take_succ_cons, List.flatMap_cons, List.length_append, List.getElem_cons_succ] at hl ⊢
    rw [List.getElem?_append_right (by omega), show (f x).length + ((L.take i).flatMap f).length + l -
      (f x).length = ((L.take i).flatMap f).length + l by omega]
    exact flatMap_getElem?_pos f L i l (by simp at hi; omega) hl

theorem flatMap_decomp {α β : Type*} (f : α → List β) :
    ∀ (L : List α) (t : ℕ), t < (L.flatMap f).length →
      ∃ i, ∃ hi : i < L.length, ∃ l, l < (f L[i]).length ∧ t = ((L.take i).flatMap f).length + l
  | [], t, ht => by simp at ht
  | x :: L, t, ht => by
    simp only [List.flatMap_cons, List.length_append] at ht
    by_cases h0 : t < (f x).length
    · exact ⟨0, by simp, t, by simpa using h0, by simp⟩
    · obtain ⟨i, hi, l, hl, e⟩ := flatMap_decomp f L (t - (f x).length) (by omega)
      refine ⟨i + 1, by simp; omega, l, by simpa using hl, ?_⟩
      simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
      omega

theorem take_flatMap_length {α β : Type*} (f : α → List β) (L : List α) (g : ℕ → ℕ)
    (hg : ∀ j (hj : j < L.length), (f L[j]).length = g j) :
    ∀ i ≤ L.length, ((L.take i).flatMap f).length = ∑ j ∈ Finset.range i, g j := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    rw [List.take_succ, List.getElem?_eq_getElem (by omega), List.flatMap_append, List.length_append,
      ih (by omega), Finset.sum_range_succ]
    simp [hg i (by omega)]

/-! ## The forest of a walk table as BFS rows -/

section Goal
open Nock.Walk Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
variable {q : ℕ} {Kfp : Type} [Field Kfp] [DecidableEq Kfp]

theorem fo_eq (s : Bool × Bool) : fo s = WalkVCL.fanout s := rfl

theorem val_lin {x : ZMod q} (hq : 2 ^ 63 < q) (hx : x.val < 2 ^ 62) (b : Bool) :
    (2 * x + bitZ b).val = 2 * x.val + bit b := by
  have e : (2 * x + bitZ b : ZMod q) = ((2 * x.val + bit b : ℕ) : ZMod q) := by
    have hx' : ((x.val : ℕ) : ZMod q) = x := by
      haveI : NeZero q := ⟨by omega⟩
      exact ZMod.natCast_zmod_val x
    cases b <;> simp [bitZ, bit, hx']
  rw [e, ZMod.val_natCast_of_lt]
  unfold bit; split_ifs <;> omega

theorem val_succ {x : ZMod q} (hq : 2 ^ 63 < q) (hx : x.val < 62) : (x + 1).val = x.val + 1 := by
  have e : (x + 1 : ZMod q) = ((x.val + 1 : ℕ) : ZMod q) := by
    haveI : NeZero q := ⟨by omega⟩
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [e, ZMod.val_natCast_of_lt (by omega)]

theorem val_one' (hq : 2 ^ 63 < q) : (1 : ZMod q).val = 1 := by
  rw [show (1 : ZMod q) = ((1 : ℕ) : ZMod q) by simp, ZMod.val_natCast_of_lt (by omega)]

/-- **The walk forest as BFS rows.** `ForestReconGoal` with the root gate, the queue validity, the fanout column and
the axis bound gives the abstract BFS rows of the row labels (0-based: row `j` is label `j + 1`; serial, prefix and
length as naturals). -/
theorem bfsRows_of_goal {X : List (XKey Kfp)} {lbl : ℕ → LT q Kfp} {kroots h : ℕ} {fo' : ℕ → ℕ}
    (hq : 2 ^ 63 < q) (hk : 1 ≤ kroots)
    (hG : ForestReconGoal (stateSep (q := q) X 62) lbl kroots h)
    (hroot : ∀ i, 1 ≤ i → i ≤ kroots → RootOK (lbl i).2)
    (hvalid : BFSValidF kroots fo' h) (hfo : ∀ i, 1 ≤ i → i ≤ h → fo' i = WalkVCL.fanout (lbl i).1)
    (haxis : ∀ i, 1 ≤ i → i ≤ h → ∀ b, (2 * (lbl i).2.pre + bitZ b).val < 2 ^ 62) :
    BFSRows h kroots (fun j => (lbl (j + 1)).1) (fun j => (lbl (j + 1)).2.ridx.val)
      (fun j => (lbl (j + 1)).2.pre.val) (fun j => (lbl (j + 1)).2.len.val) := by
  obtain ⟨ts, hlen, hrvt, hlab, hfan, -⟩ := hG
  set st : ℕ → Bool × Bool := fun j => (lbl (j + 1)).1 with hst
  set W := bfsForest ts with hW
  have hne : ts ≠ [] := by intro e; rw [e] at hlen; simp at hlen; omega
  have hsplit : W = ts ++ W.flatMap NTree.children := bfsForest_eq_append_flatMap ts hne
  have hWlen : W.length = h := by have := congrArg List.length hlab; simpa using this
  have hWl : ∀ j (hj : j < W.length), W[j].label = lbl (j + 1) := by
    intro j hj
    have e := congrArg (fun l => l[j]?) hlab
    simp only [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem?_range' (by omega : j < h)] at e
    simp only [Option.map_some, Option.some.injEq] at e
    rw [e]; congr 1; omega
  have hrvtW : ∀ t ∈ W, RVT (WalkVCL.F (q := q) X 62) t := by
    intro t ht
    obtain ⟨c, hc, hin⟩ := (mem_bfsForest ts t).mp ht
    exact RVT_of_InTree (hrvt c hc) hin
  have hch : ∀ j (hj : j < W.length), (W[j].children).length = fo (st j) := by
    intro j hj
    rw [← hfan _ (List.getElem_mem hj), hWl j hj]
    rfl
  have hP : ∀ i ≤ W.length, ((W.take i).flatMap NTree.children).length = P st i := fun i hi =>
    take_flatMap_length NTree.children W (fun j => fo (st j)) hch i hi
  have hkh : kroots ≤ h := by
    have := congrArg List.length hsplit
    rw [List.length_append] at this; omega
  -- the child slots
  have hpos : ∀ i (hi : i < W.length) l (hl : l < (W[i].children).length),
      W[kroots + P st i + l]? = some ((W[i].children)[l]) := by
    intro i hi l hl
    have e1 : W[kroots + P st i + l]? = (ts ++ W.flatMap NTree.children)[kroots + P st i + l]? :=
      congrArg (fun L => L[kroots + P st i + l]?) hsplit
    rw [e1, List.getElem?_append_right (by omega), hlen,
      show kroots + P st i + l - kroots = ((W.take i).flatMap NTree.children).length + l by
        rw [hP i (by omega)]; omega,
      flatMap_getElem?_pos NTree.children W i l hi hl, List.getElem?_eq_getElem hl]
  -- the child relation (field form)
  have hrel : ∀ i (hi : i < W.length) l (hl : l < fo (st i)),
      ∃ k ∈ X, WalkVCL.ChildOK k (side (st i) l) (lbl (i + 1)).2 (lbl (kroots + P st i + l + 1)) ∧
        (lbl (i + 1)).2.len.val < 62 := by
    intro i hi l hl
    have hl' : l < (W[i].children).length := by rw [hch i hi]; exact hl
    have hm := hpos i hi l hl'
    have hmlt : kroots + P st i + l < W.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hm; simp at hm
    have hml : (W[i].children)[l].label = lbl (kroots + P st i + l + 1) := by
      rw [← hWl _ hmlt]
      rw [List.getElem?_eq_getElem hmlt, Option.some.injEq] at hm
      rw [hm]
    have hF := F_of_rvt (hrvtW _ (List.getElem_mem hi))
    rw [hWl i hi] at hF
    obtain ⟨h62, -, k, hkX, -, h1, h2⟩ := hF
    have hcl : W[i].childLabel l = some (lbl (kroots + P st i + l + 1)) := by
      simp only [NTree.childLabel, NTree.childOpt, List.getElem?_eq_getElem hl', Option.map_some, hml]
    refine ⟨k, hkX, ?_, h62⟩
    have hsi : (lbl (i + 1)).1 = st i := rfl
    rcases hs : st i with ⟨s1, s2⟩
    rw [hs] at hl
    rw [hsi, hs] at h1 h2
    have hfo2 : fo (s1, s2) ≤ 2 := fo_le_two
    rcases (by have := lt_of_lt_of_le hl hfo2; omega : l = 0 ∨ l = 1) with rfl | rfl
    · cases s1
      · have hs2 : s2 = true := by cases s2 <;> simp [fo] at hl ⊢
        obtain ⟨c, hc, hok⟩ := h2 hs2
        have hc' : W[i].childLabel 0 = some c := by simpa using hc
        have : c = lbl (kroots + P st i + 0 + 1) := Option.some.inj (hc'.symm.trans hcl)
        subst this; simpa [side] using hok
      · obtain ⟨c, hc, hok⟩ := h1 rfl
        have hc' : W[i].childLabel 0 = some c := by simpa using hc
        have : c = lbl (kroots + P st i + 0 + 1) := Option.some.inj (hc'.symm.trans hcl)
        subst this; simpa [side] using hok
    · have hb : s1 = true ∧ s2 = true := by cases s1 <;> cases s2 <;> simp [fo] at hl ⊢
      obtain ⟨rfl, rfl⟩ := hb
      obtain ⟨c, hc, hok⟩ := h2 rfl
      have hc' : W[i].childLabel 1 = some c := by simpa using hc
      have : c = lbl (kroots + P st i + 1 + 1) := Option.some.inj (hc'.symm.trans hcl)
      subst this; simpa [side] using hok
  have hSf : ∀ i ≤ h, Sf fo' i = P st i := by
    intro i
    induction i with
    | zero => intro _; simp [Sf, P]
    | succ i ih =>
      intro hi
      rw [Sf_succ, P_succ, ih (by omega), hfo (i + 1) (by omega) hi]
      rfl
  have hparent : ∀ m, kroots ≤ m → m < h → ∃ i < m, ∃ l < fo (st i), m = kroots + P st i + l := by
    intro m hkm hm
    have hlenF : m - kroots < (W.flatMap NTree.children).length := by
      have := congrArg List.length hsplit
      rw [List.length_append] at this; omega
    obtain ⟨i, hi, l, hl, e⟩ := flatMap_decomp NTree.children W (m - kroots) hlenF
    rw [hP i (by omega)] at e
    have hv := hvalid (i + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at hv
    rw [hSf i (by omega)] at hv
    exact ⟨i, by omega, l, by rw [← hch i hi]; exact hl, by omega⟩
  have hprel : ∀ j < h, (lbl (j + 1)).2.pre.val < 2 ^ 62 := by
    intro j hj
    by_cases hjk : j < kroots
    · rw [(hroot (j + 1) (by omega) (by omega)).1, val_one' hq]; norm_num
    · obtain ⟨i, hi, l, hl, rfl⟩ := hparent j (by omega) hj
      obtain ⟨k, -, hok, -⟩ := hrel i (by omega) l hl
      rw [hok.2.1]
      exact haxis (i + 1) (by omega) (by omega) _
  refine ⟨hkh, fun j hj => ?_, fun i hi l hl => ?_, hparent⟩
  · obtain ⟨h1, h2, -⟩ := hroot (j + 1) (by omega) (by omega)
    exact ⟨by rw [h1, val_one' hq], by rw [h2, ZMod.val_zero]⟩
  · obtain ⟨k, -, hok, h62⟩ := hrel i (by omega) l hl
    have hl' : l < (W[i]'(by omega)).children.length := by rw [hch i (by omega)]; exact hl
    have hm := hpos i (by omega) l hl'
    have hmlt : kroots + P st i + l < h := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hm; simp at hm
    refine ⟨hmlt, by rw [hok.2.2.2.1], ?_, ?_⟩
    · rw [hok.2.1, val_lin hq (hprel i hi)]
    · rw [hok.2.2.2.2, val_succ hq h62]

end Goal


/-! ## 3. The J-8 walk chip -/

section Chip
open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkForestP1 (walkW walkJ8_forest)

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.w → F[X])

/-- Row `j`'s base environment of the J-8 walk trace. -/
abbrev envQ (j : ℕ) : Env F :=
  Reify.envOfTrace Q orbit.ω (if hj : j < n then nodes ⟨j, hj⟩ else nodes ⟨0, hn⟩) (slotVal b 25 chals)
    (slotVal b 25 pubs)

/-- The walk data's row environment reads the J-8 trace on columns `< 14`. -/
theorem env0_trace (j : ℕ) {c : ℕ} (hc : c < 14) :
    (Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.walkEnvF b hn nodes orbit chals pubs (AtomWalkAW.restrictWalkK δF kroots b hn nodes orbit chals pubs
      (bitFix δF kroots b hn nodes orbit chals pubs Q)) j).trace c =
      (envQ δF kroots b hn nodes orbit chals pubs Q j).trace c := by
  rw [← AtomWalkAW.walkEnvFA_trace δF kroots b hn nodes orbit chals pubs _ j (by omega : c < 21)]
  exact walkEnvFA_bitFix δF kroots b hn nodes orbit chals pubs Q j c (Or.inl hc)

/-- **The label fields of walk row `j` are its columns**: flags `decide (cL = 1)`, `decide (cR = 1)`; serial,
prefix and length as naturals (`natOf`). -/
theorem lbl_fields (hF : GeneratedField.PrimeFieldElems F) (j : ℕ) :
    ((walkW δF kroots b hn nodes orbit chals pubs Q).lbl (j + 1)).1 =
        (decide ((envQ δF kroots b hn nodes orbit chals pubs Q j).trace WChip.cL = 1),
          decide ((envQ δF kroots b hn nodes orbit chals pubs Q j).trace WChip.cR = 1)) ∧
      ((walkW δF kroots b hn nodes orbit chals pubs Q).lbl (j + 1)).2.ridx.val =
        natOf ((envQ δF kroots b hn nodes orbit chals pubs Q j).trace WChip.ridx) ∧
      ((walkW δF kroots b hn nodes orbit chals pubs Q).lbl (j + 1)).2.pre.val =
        natOf ((envQ δF kroots b hn nodes orbit chals pubs Q j).trace WChip.pre) ∧
      ((walkW δF kroots b hn nodes orbit chals pubs Q).lbl (j + 1)).2.len.val =
        natOf ((envQ δF kroots b hn nodes orbit chals pubs Q j).trace WChip.len) := by
  have hv : ∀ x : F, (zq x).val = natOf x := fun x => ZMod.val_natCast_of_lt (natOf_lt hF x)
  simp only [walkW, walkDataOf, lblRow, Nat.add_sub_cancel, hv,
    env0_trace δF kroots b hn nodes orbit chals pubs Q j (show WChip.cL < 14 by decide),
    env0_trace δF kroots b hn nodes orbit chals pubs Q j (show WChip.cR < 14 by decide),
    env0_trace δF kroots b hn nodes orbit chals pubs Q j (show WChip.ridx < 14 by decide),
    env0_trace δF kroots b hn nodes orbit chals pubs Q j (show WChip.pre < 14 by decide),
    env0_trace δF kroots b hn nodes orbit chals pubs Q j (show WChip.len < 14 by decide)]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

open scoped Classical in
/-- **The rows of an accepted J-8 walk trace are BFS rows** (outside the walk event): `BFSRows` of the row labels,
by `walkJ8_forest` and `bfsRows_of_goal` (axis bound `walkJ8_axis_lt`). -/
theorem walkJ8_bfsRows
    (hsat : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hF : GeneratedField.PrimeFieldElems F)
    (hk : 1 ≤ kroots) (hkn : kroots ≤ n) (hkp : kroots + n < ringChar F) (hq : 2 ^ 63 < ringChar F)
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap F K δF) (walkW δF kroots b hn nodes orbit chals pubs Q)) :
    BFSRows n kroots (fun j => ((walkW δF kroots b hn nodes orbit chals pubs Q).lbl (j + 1)).1)
      (fun j => ((walkW δF kroots b hn nodes orbit chals pubs Q).lbl (j + 1)).2.ridx.val)
      (fun j => ((walkW δF kroots b hn nodes orbit chals pubs Q).lbl (j + 1)).2.pre.val)
      (fun j => ((walkW δF kroots b hn nodes orbit chals pubs Q).lbl (j + 1)).2.len.val) := by
  obtain ⟨hyp, hRG, hG⟩ := walkJ8_forest δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF hk hkn
    hkp hq hout
  have hax := walkJ8_axis_lt δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF hk hkn hkp hq hout
  exact bfsRows_of_goal hq hk hG (fun i h1 h2 => (hRG i h1 h2).1) hyp.2.2.1 hyp.2.2.2.2.1
    (fun i h1 h2 bb => (hax i h1 h2 bb).2)

end Chip

/-! ## 4. Two accepted tuples: the trie columns -/

section TU
open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qW)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0WP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkForestP1 (walkW)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsWalkP1 (rowIx rowIx_val)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K) [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

/-- The walk data of a J-8 tuple's walk view. -/
abbrev WT (Pb : PubJ8 p) (chals pubs : ℕ → K) (tr : TrJ8 (ZMod p)) :
    WalkData (ringChar (ZMod p)) (Quad (algebraMap (ZMod p) K δ)) :=
  walkW δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals pubs (qW δ b Pb tr chals pubs)

theorem envQ_eq (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (chals pubs : ℕ → K) {j : ℕ} (hj : j < Pb.nW) :
    envQ δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals pubs (qW δ b Pb tr chals pubs) j =
      envB δ b Pb tr chals pubs j := by
  simp only [envQ, envB, dif_pos hj, rowIx_mk Pb hj]

theorem pF : GeneratedField.PrimeFieldElems (ZMod p) := GeneratedField.primeFieldElems_zmod p

/-- The label fields of a J-8 tuple's walk row `j < nW`, as columns of `envB`. -/
theorem lbl_cols (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (chals pubs : ℕ → K) {j : ℕ} (hj : j < Pb.nW) :
    ((WT δ b Pb chals pubs tr).lbl (j + 1)).1 =
        (decide ((envB δ b Pb tr chals pubs j).trace WChip.cL = 1),
          decide ((envB δ b Pb tr chals pubs j).trace WChip.cR = 1)) ∧
      ((WT δ b Pb chals pubs tr).lbl (j + 1)).2.ridx.val = natOf ((envB δ b Pb tr chals pubs j).trace WChip.ridx) ∧
      ((WT δ b Pb chals pubs tr).lbl (j + 1)).2.pre.val = natOf ((envB δ b Pb tr chals pubs j).trace WChip.pre) ∧
      ((WT δ b Pb chals pubs tr).lbl (j + 1)).2.len.val = natOf ((envB δ b Pb tr chals pubs j).trace WChip.len) := by
  have := lbl_fields δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals pubs (qW δ b Pb tr chals pubs) pF j
  rwa [envQ_eq δ b Pb tr chals pubs hj] at this

variable {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {r : RowsJ8} {g : ℕ}

/-- The walk chip's base gates at row `i`. -/
theorem base_at {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} (hA : AcceptsJ8V δ b Pb Rg c χ M tr r g) (i : ℕ) :
    ∀ g ∈ (walkTemplateJ8 (F := ZMod p) δ Pb.kroots).baseTransition,
      g.eval (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW i) = 0 := fun g hg =>
  ((expandChip_satisfies_iff_language (walkTemplateJ8 δ Pb.kroots) b _ _ Pb.orbitW _
    (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)).mp hA.hsatW
    (Pb.nodesW (rowIx Pb.hnW i)) (mem_rowNodeSet Pb.nodesW (rowIx Pb.hnW i))).1 g hg

theorem mem_baseJ8 (kroots : ℕ) {g : CoeffExpr (ZMod p)} (hg : g ∈ basePre ∨ g ∈ basePost kroots) :
    g ∈ (walkTemplateJ8 (F := ZMod p) δ kroots).baseTransition := by
  show g ∈ baseGatesJ8 kroots ++ CellTwinK.baseHK
  simp only [baseGatesJ8, List.mem_append, List.mem_singleton]
  tauto

/-- The child flags are boolean. -/
theorem flags_bool {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} (hA : AcceptsJ8V δ b Pb Rg c χ M tr r g) (i : ℕ) :
    ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW i).trace WChip.cL = 0 ∨
        (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW i).trace WChip.cL = 1) ∧
      ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW i).trace WChip.cR = 0 ∨
        (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW i).trace WChip.cR = 1) := by
  have g1 := base_at δ b hA i _ (mem_baseJ8 δ Pb.kroots (Or.inl (by simp [basePre])) :
    (boolE (cv WChip.cL) : CoeffExpr (ZMod p)) ∈ _)
  have g2 := base_at δ b hA i _ (mem_baseJ8 δ Pb.kroots (Or.inl (by simp [basePre])) :
    (boolE (cv WChip.cR) : CoeffExpr (ZMod p)) ∈ _)
  simp only [boolE, CoeffExpr.eval, cv] at g1 g2
  exact ⟨OpenR0WP1.bool01 g1, OpenR0WP1.bool01 g2⟩

/-- On a root row, `ridx = idx` and `pre = 1`. -/
theorem root_cols {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    (hA : AcceptsJ8V δ b Pb Rg c χ M tr r g) (hW : (canonW b Pb).Satisfies (sideWQ tr ax))
    {i : ℕ} (hi : i < Pb.kroots) (hin : i < Pb.nW) :
    (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW i).trace WChip.ridx =
        (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW i).trace WChip.idx ∧
      (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW i).trace WChip.pre = 1 := by
  have R := walkRowFacts_of δ b Pb hA hW
  have hr : (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW i).trace WChip.rM = 1 := by
    have := R.rM i hin; rw [if_pos hi] at this; exact this
  have g1 := base_at δ b hA i _ (mem_baseJ8 δ Pb.kroots (Or.inr (by simp [basePost])) :
    (.mul (cv WChip.rM) (.sub (cv WChip.ridx) (cv WChip.idx)) : CoeffExpr (ZMod p)) ∈ _)
  have g2 := base_at δ b hA i _ (mem_baseJ8 δ Pb.kroots (Or.inr (by simp [basePost])) :
    (.mul (cv WChip.rM) (.sub (cv WChip.pre) (.const 1)) : CoeffExpr (ZMod p)) ∈ _)
  simp only [CoeffExpr.eval, cv, hr, one_mul] at g1 g2
  exact ⟨sub_eq_zero.mp g1, sub_eq_zero.mp g2⟩

/-- **The root serials strictly increase** (as naturals), given each is below `2^32`. -/
theorem root_mono (hpG : p = Nock.Atoms.p) {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    (hA : AcceptsJ8V δ b Pb Rg c χ M tr r g) (hW : (canonW b Pb).Satisfies (sideWQ tr ax))
    (hkn : Pb.kroots ≤ Pb.nW)
    (hrb : ∀ j < Pb.kroots, natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.ridx) < 2 ^ 32) :
    ∀ i j, i < j → j < Pb.kroots →
      natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW i).trace WChip.ridx) <
        natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.ridx) := by
  have R := walkRowFacts_of δ b Pb hA hW
  have hp : 2 ^ 34 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  set v : ℕ → ℕ := fun j => natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.ridx) with hv
  have step : ∀ j, j + 1 < Pb.kroots → v j < v (j + 1) := by
    intro j hj
    have hjn : j < Pb.nW := by omega
    have hjn' : j + 1 < Pb.nW := by omega
    set x := Pb.nodesW ⟨j, hjn⟩
    have hx : x ∈ rowNodeSet Pb.nodesW := mem_rowNodeSet Pb.nodesW _
    have hωx : Pb.orbitW.ω * x = Pb.nodesW ⟨j + 1, hjn'⟩ := by
      rw [mul_comm]; exact (hA.hadjW ⟨j, hjn⟩ hjn').symm
    have hL : (tr.W ⟨WChip.isL, by decide⟩).eval x = 0 := by
      have := R.isL j hjn
      rw [envB_eval δ b Pb tr _ _ (by decide) hjn, if_neg (by omega)] at this
      exact this
    have hr : (tr.W ⟨WChip.rM, by decide⟩).eval x = 1 := by
      have := R.rM j hjn
      rw [envB_eval δ b Pb tr _ _ (by decide) hjn, if_pos (by omega)] at this
      exact this
    have hr' : (tr.W ⟨WChip.rM, by decide⟩).eval (Pb.orbitW.ω * x) = 1 := by
      have := R.rM (j + 1) hjn'
      rw [envB_eval δ b Pb tr _ _ (by decide) hjn', if_pos hj] at this
      rw [hωx]; exact this
    obtain ⟨d, hd, e⟩ := walk_rootorder_row b Pb tr ax hW hx hL hr hr'
    rw [hωx] at e
    have e0 : (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.ridx = (tr.W ⟨WChip.ridx, by decide⟩).eval x :=
      envB_eval δ b Pb tr _ _ (by decide) hjn
    have e1 : (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW (j + 1)).trace WChip.ridx =
        (tr.W ⟨WChip.ridx, by decide⟩).eval (Pb.nodesW ⟨j + 1, hjn'⟩) :=
      envB_eval δ b Pb tr _ _ (by decide) hjn'
    have hc0 : ((v j : ℕ) : ZMod p) = (tr.W ⟨WChip.ridx, by decide⟩).eval x := by
      rw [hv, ← e0]; exact natOf_cast pF _
    have hc1 : ((v (j + 1) : ℕ) : ZMod p) = (tr.W ⟨WChip.ridx, by decide⟩).eval (Pb.nodesW ⟨j + 1, hjn'⟩) := by
      rw [hv, ← e1]; exact natOf_cast pF _
    have hlt1 : v (j + 1) < p := by
      have := natOf_lt pF ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW (j + 1)).trace WChip.ridx)
      rwa [ZMod.ringChar_zmod_n] at this
    have hb := hrb j (by omega)
    refine ridx_lt_of_rootorder hd hlt1 (by simp only [hv] at hb ⊢; omega) ?_
    rw [hc1, e, ← hc0]
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | rfl
    · exact (ih h (by omega)).trans (step j hj)
    · exact step i hj

/-- **The pin E10 gives a one-key cover**: with `idx = 0` on row `0`, row `0` (a root) has key `(0, 1)`. -/
theorem cover_E10 {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    (hA : AcceptsJ8V δ b Pb Rg c χ M tr r g) (hW : (canonW b Pb).Satisfies (sideWQ tr ax))
    (hk : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW)
    (hE : (tr.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW ⟨0, by omega⟩) = 0) :
    ∀ s ∈ ({(0, 1)} : Finset (ℕ × ℕ)), ∃ j < Pb.nW,
      natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.ridx) = s.1 ∧
        natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.pre) = s.2 := by
  intro s hs
  rw [Finset.mem_singleton] at hs
  subst hs
  obtain ⟨e1, e2⟩ := root_cols δ b hA hW (i := 0) (by omega) (by omega)
  refine ⟨0, by omega, ?_, ?_⟩
  · rw [e1, envB_eval δ b Pb tr _ _ (by decide) (by omega), hE]
    have := natOf_natCast pF (F := ZMod p) (k := 0) (by rw [ZMod.ringChar_zmod_n]; exact (Fact.out : p.Prime).pos)
    simpa using this
  · rw [e2]
    have := natOf_natCast pF (F := ZMod p) (k := 1) (by rw [ZMod.ringChar_zmod_n]; exact (Fact.out : p.Prime).one_lt)
    simpa using this

/-- The cover hypothesis of a tuple: every key of `S` is some row's `(ridx, pre)` (as naturals). -/
def CoversW (S : Finset (ℕ × ℕ)) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) : Prop :=
  ∀ s ∈ S, ∃ j < Pb.nW, natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.ridx) = s.1 ∧
    natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.pre) = s.2

/-- The trie columns: `pre ridx len cL cR`. -/
def trieW : List ℕ := [4, 5, 6, 7, 8]

open scoped Classical in
/-- **The walk tries of two accepted tuples are equal.** At one layout, claim and coin, outside the walk event at
both traces, with `1 ≤ kroots ≤ nW`, `kroots + nW < p`, root serials below `2^32`, and one key set `S` of `nW` keys
covered by both: the trie columns `pre ridx len cL cR` agree at every row, and `idx` agrees on the root rows. -/
theorem trie_eq {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {M M' : MsgJ8' p K δ}
    {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon2 δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hk : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW) (hkp : Pb.kroots + Pb.nW < p)
    (hout : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr))
    (hout' : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M'.pubsW tr'))
    (hrb : ∀ j < Pb.kroots, natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.ridx) < 2 ^ 32)
    (hrb' : ∀ j < Pb.kroots, natOf ((envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace WChip.ridx) < 2 ^ 32)
    (S : Finset (ℕ × ℕ)) (hS : S.card = Pb.nW)
    (hcov : CoversW δ b (Pb := Pb) (χ := χ) S M tr) (hcov' : CoversW δ b (Pb := Pb) (χ := χ) S M' tr') :
    (∀ j < Pb.nW, ∀ col ∈ trieW, (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace col =
      (envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace col) ∧
    (∀ j < Pb.kroots, (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.idx =
      (envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace WChip.idx) := by
  have hA := h.1.1
  have hA' := h'.1.1
  have hW := h.1.2.hW
  have hW' := h'.1.2.hW
  have hq : 2 ^ 63 < ringChar (ZMod p) := two63_lt_ringChar hpG
  have hkp' : Pb.kroots + Pb.nW < ringChar (ZMod p) := by rw [ZMod.ringChar_zmod_n]; exact hkp
  set chals := chalsMJ8 δ χ
  have B := walkJ8_bfsRows δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW _ hA.hsatW hA.hbindW hA.hinjW
    hA.hadjW pF hk hkn hkp' hq hout
  have B' := walkJ8_bfsRows δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M'.pubsW _ hA'.hsatW hA'.hbindW
    hA'.hinjW hA'.hadjW pF hk hkn hkp' hq hout'
  set e := fun j => envB δ b Pb tr chals M.pubsW j
  set e' := fun j => envB δ b Pb tr' chals M'.pubsW j
  have L := fun j (hj : j < Pb.nW) => lbl_cols δ b Pb tr chals M.pubsW hj
  have L' := fun j (hj : j < Pb.nW) => lbl_cols δ b Pb tr' chals M'.pubsW hj
  have mono := root_mono δ b hpG hA hW hkn hrb
  have mono' := root_mono δ b hpG hA' hW' hkn hrb'
  have U := bfs_unique_of_cover B B'
    (fun i j hij hj => by rw [(L i (by omega)).2.1, (L j (by omega)).2.1]; exact mono i j hij hj)
    (fun i j hij hj => by rw [(L' i (by omega)).2.1, (L' j (by omega)).2.1]; exact mono' i j hij hj)
    S hS
    (fun s hs => by
      obtain ⟨j, hj, e1, e2⟩ := hcov s hs
      exact ⟨j, hj, by rw [(L j hj).2.1]; exact e1, by rw [(L j hj).2.2.1]; exact e2⟩)
    (fun s hs => by
      obtain ⟨j, hj, e1, e2⟩ := hcov' s hs
      exact ⟨j, hj, by rw [(L' j hj).2.1]; exact e1, by rw [(L' j hj).2.2.1]; exact e2⟩)
  have hcols : ∀ j < Pb.nW, ∀ col ∈ trieW, (e j).trace col = (e' j).trace col := by
    intro j hj col hcol
    obtain ⟨u1, u2, u3, u4⟩ := U j hj
    obtain ⟨l1, l2, l3, l4⟩ := L j hj
    obtain ⟨l1', l2', l3', l4'⟩ := L' j hj
    rw [l1, l1'] at u1
    rw [l2, l2'] at u2
    rw [l3, l3'] at u3
    rw [l4, l4'] at u4
    obtain ⟨bL, bR⟩ := flags_bool δ b hA j
    obtain ⟨bL', bR'⟩ := flags_bool δ b hA' j
    have hdec : ∀ {x y : ZMod p}, (x = 0 ∨ x = 1) → (y = 0 ∨ y = 1) → decide (x = 1) = decide (y = 1) → x = y := by
      intro x y hx hy hd
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all
    simp only [trieW, List.mem_cons, List.not_mem_nil, or_false] at hcol
    rcases hcol with rfl | rfl | rfl | rfl | rfl
    · exact natOf_inj pF u3
    · exact natOf_inj pF u2
    · exact natOf_inj pF u4
    · exact hdec bL bL' (congrArg Prod.fst u1)
    · exact hdec bR bR' (congrArg Prod.snd u1)
  refine ⟨hcols, fun j hj => ?_⟩
  rw [← (root_cols δ b hA hW hj (by omega)).1, ← (root_cols δ b hA' hW' hj (by omega)).1]
  exact hcols j (by omega) WChip.ridx (by simp [trieW, WChip.ridx])

/-! ## 5. `OpenP1.r0W`, `OpenP1.auxW`, `OpenP1.r1W` -/

/-- Two tuples agree on the columns of `cols` at every walk row node. -/
def AgreeW (Pb : PubJ8 p) (tr tr' : TrJ8 (ZMod p)) (cols : List ℕ) : Prop :=
  ∀ j : Fin 166, (j : ℕ) ∈ cols → ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)

open scoped Classical in
/-- **The walk's round-0, aux and round-1 columns agree** for two tuples accepted by `AcceptsCanon2` at one layout,
claim and coin, outside the walk event at both traces.

The trie columns (`pre ridx len cL cR`) and `idx` on the root rows are DERIVED (`trie_eq`). The cover is split on
`noPath` (the claim has no path read):
* `noPath`: the pin E10 (`hE10`, `hE10'`: `idx = 0` on row `0`) and `nW = 1` (`hnW1`, the canonical size);
* `¬ noPath`: `hreadsEq`, a key set `S` of `nW` keys `(serial, prefix)` covered by both tuples (the honest read
 closure: every read's record is provided by a walk row, and the ancestors by the forest).
The remaining hypotheses, each given the trie agreement: `hidxN` (`idx` on the non-root rows), `hmLR` (`mL mR`),
`hkv` (`kL vL kR vR`), `hr1` (the round-1 labels `p l r root`, given also `idx`). -/
theorem r0W_auxW_r1W {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {M M' : MsgJ8' p K δ}
    {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon2 δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hk : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW) (hkp : Pb.kroots + Pb.nW < p)
    (hout : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr))
    (hout' : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M'.pubsW tr'))
    (hrb : ∀ j < Pb.kroots, natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.ridx) < 2 ^ 32)
    (hrb' : ∀ j < Pb.kroots, natOf ((envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace WChip.ridx) < 2 ^ 32)
    (noPath : Prop)
    (hE10 : noPath → (tr.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW ⟨0, by omega⟩) = 0)
    (hE10' : noPath → (tr'.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW ⟨0, by omega⟩) = 0)
    (hnW1 : noPath → Pb.nW = 1)
    (hreadsEq : ¬ noPath → ∃ S : Finset (ℕ × ℕ), S.card = Pb.nW ∧
      CoversW δ b (Pb := Pb) (χ := χ) S M tr ∧ CoversW δ b (Pb := Pb) (χ := χ) S M' tr')
    (hidxN : AgreeW Pb tr tr' trieW → ∀ i : Fin Pb.nW, Pb.kroots ≤ (i : ℕ) →
      (tr.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW i) = (tr'.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW i))
    (hmLR : AgreeW Pb tr tr' trieW → AgreeW Pb tr tr' [WChip.mL, WChip.mR])
    (hkv : AgreeW Pb tr tr' trieW → AgreeW Pb tr tr' [21, 22, 23, 24])
    (hr1 : AgreeW Pb tr tr' trieW → AgreeW Pb tr tr' [WChip.idx] →
      ∀ j : Fin 166, 25 ≤ (j : ℕ) → (j : ℕ) < 97 → ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) :
    (∀ j : Fin 166, (j : ℕ) < 25 → ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) ∧
      (∀ j i, (ax.W j).eval (Pb.nodesW i) = (ax'.W j).eval (Pb.nodesW i)) ∧
      (∀ j : Fin 166, 25 ≤ (j : ℕ) → (j : ℕ) < 97 →
        ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) := by
  have hA := h.1.1
  have hA' := h'.1.1
  -- the cover
  obtain ⟨S, hS, hcov, hcov'⟩ : ∃ S : Finset (ℕ × ℕ), S.card = Pb.nW ∧
      CoversW δ b (Pb := Pb) (χ := χ) S M tr ∧ CoversW δ b (Pb := Pb) (χ := χ) S M' tr' := by
    by_cases hP : noPath
    · exact ⟨{(0, 1)}, by rw [hnW1 hP]; rfl, cover_E10 δ b hA h.1.2.hW hk hkn (hE10 hP),
        cover_E10 δ b hA' h'.1.2.hW hk hkn (hE10' hP)⟩
    · exact hreadsEq hP
  obtain ⟨hT, hI⟩ := trie_eq δ b h h' hk hkn hkp hout hout' hrb hrb' S hS hcov hcov'
  have hTr : AgreeW Pb tr tr' trieW := by
    intro j hj i
    have := hT i i.isLt j hj
    rwa [envB_eval δ b Pb tr _ _ j.isLt i.isLt, envB_eval δ b Pb tr' _ _ j.isLt i.isLt] at this
  have hId : AgreeW Pb tr tr' [WChip.idx] := by
    intro j hj i
    simp only [List.mem_singleton] at hj
    have hj' : j = ⟨WChip.idx, by decide⟩ := Fin.ext hj
    subst hj'
    by_cases hik : (i : ℕ) < Pb.kroots
    · have := hI i hik
      rwa [envB_eval δ b Pb tr _ _ (by decide) i.isLt, envB_eval δ b Pb tr' _ _ (by decide) i.isLt] at this
    · exact hidxN hTr i (by omega)
  have hM := hmLR hTr
  have hK := hkv hTr
  have hcore : ∀ j : Fin 166, (j : ℕ) ∈ OpenR0WP1.coreW → ∀ i,
      (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i) := by
    intro j hj i
    simp only [OpenR0WP1.coreW, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with e | e | e | e | e | e | e | e | e | e | e | e
    · exact hId j (by simp [e, WChip.idx]) i
    · exact hTr j (by simp [e, trieW]) i
    · exact hTr j (by simp [e, trieW]) i
    · exact hTr j (by simp [e, trieW]) i
    · exact hTr j (by simp [e, trieW]) i
    · exact hTr j (by simp [e, trieW]) i
    · exact hM j (by simp [e, WChip.mL]) i
    · exact hM j (by simp [e, WChip.mR]) i
    · exact hK j (by simp [e]) i
    · exact hK j (by simp [e]) i
    · exact hK j (by simp [e]) i
    · exact hK j (by simp [e]) i
  obtain ⟨r0, aux⟩ := r0W_auxW_of_core δ b h h' hcore
  exact ⟨r0, aux, hr1 hTr hId⟩

end TU

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1.bfs_unique_of_cover
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1.bfsRows_of_goal
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1.walkJ8_bfsRows
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1.cover_E10
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1.trie_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1.r0W_auxW_r1W
