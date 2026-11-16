/-
  Nock/WalkPrefix.lean

  **The queue-empty PREFIX of a `RAP_walk` table is the root's BFS; the rest is orphan
  cycles.**

  Paper: the paper (the walk columns — there is no queue column), `:805-816`
  (initial inputs), `:817-860` (the six constraints), `:958-966` (`Thm:Walk_IOP`: the
  statement is "`slt ∈ L_RVT`", error `h/|K|`), `:2263-2302` (the proof; `:2263` "we take
  the following as self-evident … a list of tree nodes"; `:2278` the degree telescoping;
  `:2281` `node_list = node_queue_h ⟺ full BFT`).

  The K side repairs it with a committed
  queue-length gate (`Walk.QGate`, `Walk.lean`).

  Positions (`:2276`): child slot `(i, l)` lands at `1 + l + Σ_{m<i} fanout(m)`, i.e. at
  `Walk.firstC fo i + (l − 1)`, and positions `2, 3, …` are each hit exactly once
  (`Walk.tiling`).  Queue length before row `i` is `1 + Σ_{m<i} fanout(m) − (i − 1)`; it is
  `≥ 1` for every `i ≤ k` iff `BFSValid fo k`.  `prefixLen fo h` is the largest `k ≤ h` with
  `BFSValid fo k`; either `Sf fo k + 1 = k` (the queue empties exactly at `k`,
  `prefixLen_tiling_of_lt`) or `k = h` (`prefixLen_dichotomy`).

  What the identity gives, with NO tiling hypothesis on the whole table:
  * `isFullBFT_iff_getD`: `node_list = node_queue_h` is padded coefficient-list equality;
  * `isFullBFT_prefix`: the identity at `h` restricts to the identity at every `k ≤ h` with
    `Sf fo k + 1 = k` — so at `k = prefixLen fo h` the EXISTING machinery
    (`isFullBFT_curVals`, `VecBFT`, `reconTree`, `ReconGoal`) applies verbatim;
  * `overflow_children_rlc_zero`: if `k = h` and `1 + Sf fo h > h`, the children at positions
    `> h` have `RLC^γ = 0` (the zero label, `Walk.rlc γ 0 = 0`; lifted to the zero vector
    outside `overflowBadGammas`).

  The α-event (`walkPrefixAlphaEvent`) is the paper's root event of `:2301` WITHOUT the
  presupposition that the queue polynomial has degree `≤ h`: its size is
  `≤ max h (1 + Sf fo h)`, which is the paper's `h` iff `1 + Sf fo h ≤ h`
  (`paper_constant_iff_tiling`), and `≤ 1 + h·n` at arity `n` (`Walk.Sf_le_mul`).

  Nothing here uses the labeling language `F`; the `F` side composes at
  `reconTree_ReconGoal_prefix` through `reconTree_ReconGoal_of_label` at height
  `prefixLen fo h`.
-/
import Nock.Walk

set_option autoImplicit false

namespace Nock
namespace Walk

open Polynomial BigOperators
open scoped Classical

/-! ## A. `lpoly` equality is padded coefficient-list equality -/

section LpolyPad
variable {K : Type*} [Field K]

theorem lpoly_coeff_lt (e : ℕ) (l : List K) {n : ℕ} (hn : n < e) : (lpoly e l).coeff n = 0 := by
  induction l generalizing e with
  | nil => simp
  | cons a rest ih =>
    rw [lpoly_cons, coeff_add, coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero, zero_add]
    exact ih (e + 1) (by omega)

/-- **`lpoly` equality ⟺ the coefficient lists agree at every index, padded with `0`.**
    The lists need not have equal length — this is what `lpoly_inj` lacks and what the prefix
    argument needs: `node_list` has `h` coefficients, `node_queue_h` has `1 + Sf fo h`. -/
theorem lpoly_eq_iff_getD (e : ℕ) (l₁ l₂ : List K) :
    lpoly e l₁ = lpoly e l₂ ↔ ∀ j, l₁.getD j 0 = l₂.getD j 0 := by
  constructor
  · intro h j
    have := congrArg (fun q : K[X] => q.coeff (e + j)) h
    simpa only [lpoly_coeff_add] using this
  · intro h
    ext n
    rcases lt_or_ge n e with hn | hn
    · rw [lpoly_coeff_lt e l₁ hn, lpoly_coeff_lt e l₂ hn]
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [lpoly_coeff_add, lpoly_coeff_add, h j]

/-- Equal-length lists that agree at every `getD` are equal. -/
theorem list_eq_of_length_eq_of_getD_eq {α : Type*} (d : α) {l₁ l₂ : List α}
    (hlen : l₁.length = l₂.length) (h : ∀ i, l₁.getD i d = l₂.getD i d) : l₁ = l₂ := by
  apply List.ext_getElem hlen
  intro i hi hi2
  have := h i
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hi2] at this
  simpa using this

theorem take_getD_eq {α : Type*} (d : α) {l : List α} {i n : ℕ} (hi : i < n) :
    (l.take n).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

theorem getD_ge_length {α : Type*} (d : α) {l : List α} {i : ℕ} (hi : l.length ≤ i) :
    l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]; rfl

end LpolyPad

/-! ## B. The scalar identity restricts to every tiling prefix -/

section ScalarPrefix
variable {K : Type*} [Field K]

theorem curVals_getD_lt (cur : ℕ → K) {h j : ℕ} (hj : j < h) :
    (curVals cur h).getD j 0 = cur (j + 1) := by
  rw [curVals, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]; rfl

theorem curVals_getD_ge (cur : ℕ → K) {h j : ℕ} (hj : h ≤ j) :
    (curVals cur h).getD j 0 = 0 :=
  getD_ge_length 0 (by rw [curVals_length]; exact hj)

theorem flatBlks_add (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (k m : ℕ) :
    flatBlks chld' fo (k + m) =
      flatBlks chld' fo k ++ (List.range m).flatMap (fun i => blkVals chld' fo (k + i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Nat.add_assoc, flatBlks_succ, ih, List.range_succ, List.flatMap_append,
      List.append_assoc]
    simp

/-- The flattened children of rows `1..h` extend those of rows `1..k` (`k ≤ h`). -/
theorem flatBlks_getD_prefix (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) {k h j : ℕ} (hk : k ≤ h)
    (hj : j < Sf fo k) : (flatBlks chld' fo h).getD j 0 = (flatBlks chld' fo k).getD j 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [flatBlks_add, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [flatBlks_length]; exact hj)]

/-- **`node_list = node_queue_h` is padded list equality**: row `p`'s value equals the queue's value at position `p`, both sides
    read as `0` past their ends.  No tiling hypothesis. -/
theorem isFullBFT_iff_getD (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (h : ℕ) :
    IsFullBFT cur chld' fo h ↔
      ∀ j, (curVals cur h).getD j 0 = (cur 1 :: flatBlks chld' fo h).getD j 0 := by
  have hq : nodeQueueP cur chld' fo h = lpoly 1 (cur 1 :: flatBlks chld' fo h) := by
    rw [nodeQueueP_eq_gen, lpoly_cons, pow_one]
  unfold IsFullBFT
  rw [nodeListP_eq_lpoly_gen, hq]
  exact lpoly_eq_iff_getD 1 _ _

/-- **THE PREFIX IDENTITY.**  If the whole-table identity holds and the queue empties exactly
    at row `k ≤ h` (`Sf fo k + 1 = k`), then the identity holds for the table truncated to
    rows `1..k`: rows `2..k` are exactly the children of rows `1..k` in BFS order.  Rows
    `> k` cannot interfere — their children start at position `k + 1`
    (`later_rows_children_beyond`).  No `BFSValid` hypothesis. -/
theorem isFullBFT_prefix {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {h k : ℕ}
    (hk : k ≤ h) (hSfk : Sf fo k + 1 = k) (hbft : IsFullBFT cur chld' fo h) :
    IsFullBFT cur chld' fo k := by
  rw [isFullBFT_iff_getD] at hbft ⊢
  intro j
  rcases lt_or_ge j k with hj | hj
  · have h1 : (curVals cur k).getD j 0 = (curVals cur h).getD j 0 := by
      rw [curVals_getD_lt cur hj, curVals_getD_lt cur (lt_of_lt_of_le hj hk)]
    rw [h1, hbft j]
    cases j with
    | zero => rfl
    | succ j' =>
      rw [List.getD_cons_succ, List.getD_cons_succ]
      exact flatBlks_getD_prefix chld' fo hk (by omega)
  · rw [curVals_getD_ge cur hj, getD_ge_length 0 (by rw [List.length_cons, flatBlks_length]; omega)]

/-- **Overflow children are RLC-zero.**  If the identity holds at `h` and the queue has more
    than `h` entries, every queue entry past position `h` (0-indexed `j ≥ h − 1` in the flattened
    children) is `0` — the zero label. -/
theorem overflow_children_rlc_zero {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {h : ℕ}
    (hbft : IsFullBFT cur chld' fo h) {j : ℕ} (hj : h ≤ j + 1) :
    (flatBlks chld' fo h).getD j 0 = 0 := by
  rw [isFullBFT_iff_getD] at hbft
  have := hbft (j + 1)
  rw [curVals_getD_ge cur hj, List.getD_cons_succ] at this
  exact this.symm

end ScalarPrefix

/-! ## C. The prefix length: the first row at which the BFS queue empties -/

section PrefixLen
variable (fo : ℕ → ℕ)

theorem bfsValid_zero : BFSValid fo 0 := fun i hi1 hi0 => absurd (le_trans hi1 hi0) (by omega)

theorem bfsValid_one : BFSValid fo 1 := by
  intro i hi1 hih
  have : i = 1 := by omega
  subst this; simp [Sf]

theorem BFSValid.mono {k k' : ℕ} (hkk : k ≤ k') (hv : BFSValid fo k') : BFSValid fo k :=
  fun i hi1 hik => hv i hi1 (le_trans hik hkk)

/-- **The queue-empty prefix length**: the largest `k ≤ h` such that the BFS queue is nonempty
    before every row `i ≤ k` (`BFSValid fo k`, i.e. `1 + Σ_{m<i} fanout(m) − (i−1) ≥ 1`).  Rows
    `1..k` are the root's BFS; if `k < h`, the queue empties exactly at `k`
    (`prefixLen_tiling_of_lt`) and rows `k+1..h` are disconnected from the root. -/
noncomputable def prefixLen (h : ℕ) : ℕ := Nat.findGreatest (fun k => BFSValid fo k) h

theorem bfsValid_prefixLen (h : ℕ) : BFSValid fo (prefixLen fo h) :=
  Nat.findGreatest_spec (Nat.zero_le h) (bfsValid_zero fo)

theorem prefixLen_le (h : ℕ) : prefixLen fo h ≤ h := Nat.findGreatest_le h

theorem one_le_prefixLen {h : ℕ} (hh : 1 ≤ h) : 1 ≤ prefixLen fo h :=
  Nat.le_findGreatest hh (bfsValid_one fo)

theorem not_bfsValid_of_prefixLen_lt {h k : ℕ} (hk : prefixLen fo h < k) (hkh : k ≤ h) :
    ¬ BFSValid fo k :=
  Nat.findGreatest_is_greatest hk hkh

/-- A queue-valid table is its own prefix (honest traces: `Walk.foCol_BFSValid`). -/
theorem prefixLen_eq_of_bfsValid {h : ℕ} (hv : BFSValid fo h) : prefixLen fo h = h :=
  le_antisymm (prefixLen_le fo h) (Nat.le_findGreatest le_rfl hv)

/-- **The queue empties exactly at the prefix end.**  If `prefixLen fo h < h` then
    `Sf fo (prefixLen fo h) + 1 = prefixLen fo h` — the tiling at `k`, DERIVED, not assumed. -/
theorem prefixLen_tiling_of_lt {h : ℕ} (hh : 1 ≤ h) (hlt : prefixLen fo h < h) :
    Sf fo (prefixLen fo h) + 1 = prefixLen fo h := by
  have hk1 : 1 ≤ prefixLen fo h := one_le_prefixLen fo hh
  have hv : BFSValid fo (prefixLen fo h) := bfsValid_prefixLen fo h
  have hnv : ¬ BFSValid fo (prefixLen fo h + 1) :=
    not_bfsValid_of_prefixLen_lt fo (Nat.lt_succ_self _) hlt
  have hvk := hv (prefixLen fo h) hk1 le_rfl
  have hmono : Sf fo (prefixLen fo h - 1) ≤ Sf fo (prefixLen fo h) := Sf_mono fo (Nat.sub_le _ 1)
  have hfail : ¬ (prefixLen fo h + 1 ≤ 1 + Sf fo (prefixLen fo h)) := by
    intro hle
    apply hnv
    intro i hi1 hik
    rcases Nat.lt_or_ge i (prefixLen fo h + 1) with hlt' | hge
    · exact hv i hi1 (by omega)
    · have : i = prefixLen fo h + 1 := by omega
      subst this
      simpa using hle
  omega

/-- Either the queue empties exactly at `prefixLen`, or the whole table is queue-valid. -/
theorem prefixLen_dichotomy {h : ℕ} (hh : 1 ≤ h) :
    Sf fo (prefixLen fo h) + 1 = prefixLen fo h ∨ (prefixLen fo h = h ∧ BFSValid fo h) := by
  rcases lt_or_eq_of_le (prefixLen_le fo h) with hlt | heq
  · exact Or.inl (prefixLen_tiling_of_lt fo hh hlt)
  · exact Or.inr ⟨heq, heq ▸ bfsValid_prefixLen fo h⟩

/-- If the table is not queue-valid, the prefix is proper and tiles. -/
theorem prefixLen_lt_of_not_bfsValid {h : ℕ} (hnv : ¬ BFSValid fo h) : prefixLen fo h < h :=
  lt_of_le_of_ne (prefixLen_le fo h) (fun heq => hnv (heq ▸ bfsValid_prefixLen fo h))

/-! ### Positions -/

/-- Within a queue-valid prefix, a row's children lie strictly after it (`:2276`). -/
theorem prefix_pos_gt {k i : ℕ} (hv : BFSValid fo k) (hi1 : 1 ≤ i) (hik : i ≤ k) :
    i < firstC fo i := by
  have := hv i hi1 hik
  unfold firstC; omega

/-- Once the queue has emptied at `k`, rows `> k` place their children at positions `> k` only:
    they are disconnected from the root. -/
theorem later_rows_children_beyond {k i : ℕ} (hSfk : Sf fo k + 1 = k) (hki : k < i) :
    k + 1 ≤ firstC fo i := by
  have hmono : Sf fo k ≤ Sf fo (i - 1) := Sf_mono fo (by omega)
  unfold firstC; omega

/-- The children of rows `1..k` occupy exactly positions `2..k` (`Walk.tiling` at the prefix). -/
theorem prefix_children_cover {k : ℕ} (hSfk : Sf fo k + 1 = k) :
    (List.range' 1 k).flatMap (fun i => List.range' (firstC fo i) (fo i)) =
      List.range' 2 (k - 1) := by
  rw [tiling fo k 1 le_rfl, firstC_one]
  have hfc : firstC fo (1 + k) = k + 1 := by
    unfold firstC; rw [Nat.add_sub_cancel_left]; omega
  rw [hfc]
  congr 1

end PrefixLen

/-! ## D. Vector lift: the committed vectors of the prefix form a genuine BFS layout -/

section VecPrefix
variable {K : Type*} [Field K] {node_size : ℕ}

theorem curValsV_getD_lt (V : ℕ → Fin node_size → K) {h j : ℕ} (hj : j < h) :
    (curValsV V h).getD j 0 = V (j + 1) := by
  rw [curValsV, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]; rfl

theorem flatBlksV_add (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) (k m : ℕ) :
    flatBlksV Cv fo (k + m) =
      flatBlksV Cv fo k ++ (List.range m).flatMap (fun i => blkValsV Cv fo (k + i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Nat.add_assoc, flatBlksV_succ, ih, List.range_succ, List.flatMap_append,
      List.append_assoc]
    simp

theorem flatBlksV_getD_prefix (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) {k h j : ℕ}
    (hk : k ≤ h) (hj : j < Sf fo k) :
    (flatBlksV Cv fo h).getD j 0 = (flatBlksV Cv fo k).getD j 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [flatBlksV_add, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [flatBlksV_length]; exact hj)]

theorem rlc_zero (γ : K) : rlc γ (0 : Fin node_size → K) = 0 := by simp [rlc]

/-- `getD` through the `RLC^γ` image (default `0 = rlc γ 0`). -/
theorem getD_map_rlc (γ : K) (l : List (Fin node_size → K)) (j : ℕ) :
    (l.map (rlc γ)).getD j 0 = rlc γ (l.getD j 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? with
  | none => simp [rlc_zero]
  | some v => rfl

variable [Fintype K] [DecidableEq K]

/-- **The one γ-event of the prefix route**: an RLC collision at some in-range position
    (`< h`) between the committed node vector and the queue's vector at that position.
    Card `≤ h·(node_size − 1)` (`prefixBadGammas_card_le`). -/
noncomputable def prefixBadGammas (V : ℕ → Fin node_size → K) (Cv : ℕ → ℕ → Fin node_size → K)
    (fo : ℕ → ℕ) (h : ℕ) : Finset K :=
  BadRLCList (curValsV V h) ((V 1 :: flatBlksV Cv fo h).take h)

theorem prefixBadGammas_card_le (V : ℕ → Fin node_size → K) (Cv : ℕ → ℕ → Fin node_size → K)
    (fo : ℕ → ℕ) (h : ℕ) :
    (prefixBadGammas V Cv fo h).card ≤ h * (node_size - 1) := by
  refine le_trans (badRLCList_card_le _ _) ?_
  apply Nat.mul_le_mul_right
  rw [curValsV_length]; exact min_le_left _ _

/-- The bad set at a tiling prefix `k ≤ h` is contained in the bad set at `h`. -/
theorem badRLCList_prefix_subset (V : ℕ → Fin node_size → K) (Cv : ℕ → ℕ → Fin node_size → K)
    (fo : ℕ → ℕ) {k h : ℕ} (hk : k ≤ h) (hSfk : Sf fo k + 1 = k) :
    BadRLCList (curValsV V k) (V 1 :: flatBlksV Cv fo k) ⊆ prefixBadGammas V Cv fo h := by
  intro γ hγ
  simp only [BadRLCList, prefixBadGammas, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_range] at hγ ⊢
  obtain ⟨i, hi, hne, heq⟩ := hγ
  rw [curValsV_length, List.length_cons, flatBlksV_length, hSfk, min_self] at hi
  have hSfh : Sf fo k ≤ Sf fo h := Sf_mono fo hk
  have e1 : (curValsV V k).getD i 0 = (curValsV V h).getD i 0 := by
    rw [curValsV_getD_lt V hi, curValsV_getD_lt V (lt_of_lt_of_le hi hk)]
  have e2 : (V 1 :: flatBlksV Cv fo k).getD i 0 =
      ((V 1 :: flatBlksV Cv fo h).take h).getD i 0 := by
    rw [take_getD_eq 0 (lt_of_lt_of_le hi hk)]
    cases i with
    | zero => rfl
    | succ j =>
      rw [List.getD_cons_succ, List.getD_cons_succ]
      exact (flatBlksV_getD_prefix Cv fo hk (by omega)).symm
  refine ⟨i, ?_, ?_, ?_⟩
  · rw [curValsV_length, List.length_take, List.length_cons, flatBlksV_length]
    omega
  · rw [← e1, ← e2]; exact hne
  · rw [← e1, ← e2]; exact heq

/-- **The conclusion of the prefix route** (γ-free, α-free: a property of the committed
    vectors).  With `k = prefixLen fo h`: the prefix is queue-valid, and EITHER the queue
    empties at `k` and rows `1..k` are a genuine vector BFS (`VecBFT` at `k`, so `reconTree`
    at `k` applies), OR the whole table is queue-valid with an overflowing queue
    (`1 + Sf fo h > h`), the in-range positions `1..h` are the queue's first `h` entries,
    and the overflow entries are RLC-zero (`overflow_children_rlc_zero`). -/
def PrefixBFT (V : ℕ → Fin node_size → K) (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ)
    (h : ℕ) : Prop :=
  BFSValid fo (prefixLen fo h) ∧
    ((Sf fo (prefixLen fo h) + 1 = prefixLen fo h ∧ VecBFT V Cv fo (prefixLen fo h)) ∨
      (prefixLen fo h = h ∧ h < Sf fo h + 1 ∧
        curValsV V h = (V 1 :: flatBlksV Cv fo h).take h))

/-- **VECTOR PREFIX BFT FROM THE IDENTITY.**  The scalar identity `node_list = node_queue_h`
    at `γ ∉ prefixBadGammas` yields `PrefixBFT`.  No tiling and no queue-validity hypothesis
    on the table: both are DERIVED at `prefixLen fo h`. -/
theorem prefixBFT_of_isFullBFT (V : ℕ → Fin node_size → K) (Cv : ℕ → ℕ → Fin node_size → K)
    (fo : ℕ → ℕ) {h : ℕ} (hh : 1 ≤ h) {γ : K} (hγ : γ ∉ prefixBadGammas V Cv fo h)
    (hbft : IsFullBFT (fun i => rlc γ (V i)) (fun i l => rlc γ (Cv i l)) fo h) :
    PrefixBFT V Cv fo h := by
  refine ⟨bfsValid_prefixLen fo h, ?_⟩
  by_cases htile : Sf fo (prefixLen fo h) + 1 = prefixLen fo h
  · left
    refine ⟨htile, ?_⟩
    have hkle : prefixLen fo h ≤ h := prefixLen_le fo h
    have hbk := isFullBFT_prefix hkle htile hbft
    have hscalar := isFullBFT_curVals htile hbk
    rw [curVals_rlc, flatBlks_rlc] at hscalar
    have hmap : (curValsV V (prefixLen fo h)).map (rlc γ) =
        (V 1 :: flatBlksV Cv fo (prefixLen fo h)).map (rlc γ) := by
      rw [List.map_cons]; exact hscalar
    have hlen : (curValsV V (prefixLen fo h)).length =
        (V 1 :: flatBlksV Cv fo (prefixLen fo h)).length := by
      rw [curValsV_length, List.length_cons, flatBlksV_length]; omega
    have hγ' : γ ∉ BadRLCList (curValsV V (prefixLen fo h))
        (V 1 :: flatBlksV Cv fo (prefixLen fo h)) :=
      fun hmem => hγ (badRLCList_prefix_subset V Cv fo hkle htile hmem)
    exact rlc_lift_list hlen hγ' hmap
  · right
    have hkh : prefixLen fo h = h := by
      rcases prefixLen_dichotomy fo hh with h1 | ⟨h2, _⟩
      · exact absurd h1 htile
      · exact h2
    have hv : BFSValid fo h := hkh ▸ bfsValid_prefixLen fo h
    have hgt : h < Sf fo h + 1 := by
      have h1 := hv h hh le_rfl
      have h2 : Sf fo (h - 1) ≤ Sf fo h := Sf_mono fo (Nat.sub_le h 1)
      rw [hkh] at htile
      omega
    refine ⟨hkh, hgt, ?_⟩
    rw [isFullBFT_iff_getD] at hbft
    have hlen : (curValsV V h).length = ((V 1 :: flatBlksV Cv fo h).take h).length := by
      rw [curValsV_length, List.length_take, List.length_cons, flatBlksV_length]; omega
    have hmap : (curValsV V h).map (rlc γ) = ((V 1 :: flatBlksV Cv fo h).take h).map (rlc γ) := by
      apply list_eq_of_length_eq_of_getD_eq (0 : K)
      · rw [List.length_map, List.length_map]; exact hlen
      · intro j
        have hb := hbft j
        rw [curVals_rlc, flatBlks_rlc] at hb
        rw [hb, List.map_take, List.map_cons]
        rcases lt_or_ge j h with hj | hj
        · rw [take_getD_eq 0 hj]
        · have hlen' :
              ((rlc γ (V 1) :: (flatBlksV Cv fo h).map (rlc γ)).take h).length ≤ j := by
            rw [List.length_take, List.length_cons, List.length_map, flatBlksV_length]; omega
          rw [getD_ge_length 0 hlen']
          have h0 := hbft j
          rw [curVals_getD_ge _ hj, flatBlks_rlc] at h0
          exact h0.symm
    exact rlc_lift_list hlen hγ hmap

/-- The overflow γ-event: some overflow child is a nonzero vector with `RLC^γ = 0`.
    It is `BadRLCList` against the zero list, so `card ≤ Sf fo h · (node_size − 1)`. -/
noncomputable def overflowBadGammas (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) (h : ℕ) :
    Finset K :=
  BadRLCList (flatBlksV Cv fo h) (List.replicate (Sf fo h) 0)

theorem overflowBadGammas_card_le (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) (h : ℕ) :
    (overflowBadGammas Cv fo h).card ≤ Sf fo h * (node_size - 1) := by
  refine le_trans (badRLCList_card_le _ _) ?_
  apply Nat.mul_le_mul_right
  rw [flatBlksV_length, List.length_replicate, min_self]

/-- **Overflow children are the ZERO VECTOR** outside `overflowBadGammas`: with the identity at
    `h` and the queue overflowing, every flattened child at index `j ≥ h − 1` is `0` — the label
    `(tag 0, s = 0, f = 0, e = 0)`.  Whether a chip's gates accept that label is a chip question
; the walk alone does not exclude it. -/
theorem overflow_children_zero (V : ℕ → Fin node_size → K) (Cv : ℕ → ℕ → Fin node_size → K)
    (fo : ℕ → ℕ) {h : ℕ} {γ : K} (hγ : γ ∉ overflowBadGammas Cv fo h)
    (hbft : IsFullBFT (fun i => rlc γ (V i)) (fun i l => rlc γ (Cv i l)) fo h)
    {j : ℕ} (hj : h ≤ j + 1) (hjS : j < Sf fo h) :
    (flatBlksV Cv fo h).getD j 0 = 0 := by
  have hz := overflow_children_rlc_zero hbft hj
  rw [flatBlks_rlc, getD_map_rlc] at hz
  by_contra hne
  apply hγ
  simp only [overflowBadGammas, BadRLCList, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨j, ?_, ?_, ?_⟩
  · rw [Finset.mem_range, flatBlksV_length, List.length_replicate, min_self]; exact hjS
  · rw [List.getD_eq_getElem?_getD (l := List.replicate _ _), List.getElem?_replicate,
      if_pos hjS]
    exact hne
  · rw [List.getD_eq_getElem?_getD (l := List.replicate _ _), List.getElem?_replicate,
      if_pos hjS, Option.getD_some, rlc_zero]
    exact hz

end VecPrefix

/-! ## E. The α-event, honestly: no presupposed degree -/

section AlphaEvent
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Degree-free root counting for the walk identity: at most `max h (1 + Sf fo h)` challenges
    `α` satisfy `node_list(α) = node_queue_h(α)` when the polynomials differ.  The paper's
    `h/|K|` is the case `1 + Sf fo h ≤ h`, i.e. it PRESUPPOSES the
    tiling (`Walk.walk_soundness_card` carries `hdeg` for exactly this reason). -/
theorem walk_soundness_card_max {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {h : ℕ}
    (hne : nodeListP cur h ≠ nodeQueueP cur chld' fo h) :
    (Finset.univ.filter
        (fun r : K => (nodeListP cur h).eval r = (nodeQueueP cur chld' fo h).eval r)).card
      ≤ max h (1 + Sf fo h) :=
  eval_eq_card_le hne (le_trans (nodeListP_natDegree_le cur h) (le_max_left _ _))
    (le_trans (nodeQueueP_natDegree_le cur chld' fo h) (le_max_right _ _))

/-- **The α-event of the prefix route**: empty when the identity holds as polynomials; otherwise
    the roots of `node_list − node_queue_h`. -/
noncomputable def walkPrefixAlphaEvent (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (h : ℕ) : Finset K :=
  if IsFullBFT cur chld' fo h then ∅
  else Finset.univ.filter
    (fun r : K => (nodeListP cur h).eval r = (nodeQueueP cur chld' fo h).eval r)

theorem walkPrefixAlphaEvent_card_le (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (h : ℕ) :
    (walkPrefixAlphaEvent cur chld' fo h).card ≤ max h (1 + Sf fo h) := by
  unfold walkPrefixAlphaEvent
  split_ifs with hbft
  · simp
  · exact walk_soundness_card_max hbft

/-- At arity `n` (`fo i ≤ n`, `Walk.Sf_le_mul`) the event has size `≤ 1 + h·n`; at the compute
    walk's `fanoutComp ≤ 3` that is `1 + 3h`. -/
theorem walkPrefixAlphaEvent_card_le_arity (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (h : ℕ) {n : ℕ} (hn : 1 ≤ n) (harity : ∀ i, fo i ≤ n) :
    (walkPrefixAlphaEvent cur chld' fo h).card ≤ 1 + h * n := by
  refine le_trans (walkPrefixAlphaEvent_card_le cur chld' fo h) ?_
  have h1 := Sf_le_mul harity h
  have h2 : h ≤ h * n := Nat.le_mul_of_pos_right h hn
  rw [max_le_iff]; omega

/-- **`WalkSat ∧ out_walk = 0 ⟹ identity or α ∈ event`** (recognizer setting `:958-966`). -/
theorem isFullBFT_or_mem_alphaEvent {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed initial_count : K} {h : ℕ}
    (hw : WalkSat cur chld' fo ln count acc α seed initial_count h)
    (hseed : seed = cur 1 * α) (hic : initial_count = α) (hout : acc h = 0) :
    IsFullBFT cur chld' fo h ∨ α ∈ walkPrefixAlphaEvent cur chld' fo h := by
  by_cases hbft : IsFullBFT cur chld' fo h
  · exact Or.inl hbft
  · right
    unfold walkPrefixAlphaEvent
    rw [if_neg hbft, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (walk_out_zero_iff hw hseed hic).mp hout⟩

/-- The paper's constant `h` is the event bound iff the queue polynomial's degree is `≤ h`,
    i.e. iff `1 + Sf fo h ≤ h` — the tiling presupposition of `:2278`/`:2301`. -/
theorem paper_constant_iff_tiling (fo : ℕ → ℕ) (h : ℕ) :
    max h (1 + Sf fo h) = h ↔ 1 + Sf fo h ≤ h := by
  constructor
  · intro heq; have := le_max_right h (1 + Sf fo h); omega
  · intro hle; exact max_eq_left hle

end AlphaEvent

/-! ## F. Composed soundness of the prefix route, cardinality form -/

section ComposePrefix
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {node_size : ℕ}

/-- **Soundness of the prefix route** (`Thm:Walk_IOP` `:966` without the tiling presupposition):
    the number of `(α, γ)` at which the `RAP_walk` gates accept with the recognizer inputs
    (`seed = α·RLC^γ(V 1)`, `initial_count = α`) yet the committed vectors do NOT satisfy
    `PrefixBFT` is `≤ |K|·max(h, 1 + Sf fo h) + |K|·h·(node_size − 1)`.  Compare
    `Walk.walk_IOP_soundness_card`, which needs `hlen : Sf fo h + 1 = h` and concludes `VecBFT`
    at `h`; here nothing is assumed of `fo` and the conclusion is at `prefixLen fo h`. -/
theorem walk_IOP_prefix_soundness_card
    (V : ℕ → Fin node_size → K) (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) {h : ℕ}
    (hh : 1 ≤ h) :
    (Finset.univ.filter (fun p : K × K =>
        (∃ ln count acc : ℕ → K,
          WalkSat (fun i => rlc p.2 (V i)) (fun i l => rlc p.2 (Cv i l)) fo ln count acc
            p.1 (rlc p.2 (V 1) * p.1) p.1 h ∧ acc h = 0)
        ∧ ¬ PrefixBFT V Cv fo h)).card
      ≤ Fintype.card K * max h (1 + Sf fo h) + Fintype.card K * (h * (node_size - 1)) := by
  set P1 : K → K → Prop := fun α γ =>
    α ∈ walkPrefixAlphaEvent (fun i => rlc γ (V i)) (fun i l => rlc γ (Cv i l)) fo h with hP1
  set P2 : K → K → Prop := fun _α γ => γ ∈ prefixBadGammas V Cv fo h with hP2
  have hsub : (Finset.univ.filter (fun p : K × K =>
      (∃ ln count acc : ℕ → K,
        WalkSat (fun i => rlc p.2 (V i)) (fun i l => rlc p.2 (Cv i l)) fo ln count acc
          p.1 (rlc p.2 (V 1) * p.1) p.1 h ∧ acc h = 0)
      ∧ ¬ PrefixBFT V Cv fo h))
      ⊆ Finset.univ.filter (fun p : K × K => P1 p.1 p.2)
        ∪ Finset.univ.filter (fun p : K × K => P2 p.1 p.2) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨⟨ln, count, acc, hw, hacc0⟩, hnot⟩ := hp.2
    rw [Finset.mem_union]
    rcases isFullBFT_or_mem_alphaEvent hw rfl rfl hacc0 with hbft | hα
    · right
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show p.2 ∈ prefixBadGammas V Cv fo h
      by_contra hγ
      exact hnot (prefixBFT_of_isFullBFT V Cv fo hh hγ hbft)
    · left
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hα⟩
  have hb1 : (Finset.univ.filter (fun p : K × K => P1 p.1 p.2)).card
      ≤ Fintype.card K * max h (1 + Sf fo h) := by
    refine le_trans (Finset.card_le_card (?_ : _ ⊆ Finset.univ.biUnion
        (fun γ : K => (Finset.univ.filter (fun α : K => P1 α γ)).image (fun α => (α, γ))))) ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_biUnion.mpr ⟨p.2, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩, rfl⟩⟩
    · refine le_trans Finset.card_biUnion_le ?_
      refine le_trans (Finset.sum_le_sum (fun γ _ => Finset.card_image_le)) ?_
      refine le_trans (Finset.sum_le_sum (g := fun _ => max h (1 + Sf fo h))
        (fun γ (_ : γ ∈ Finset.univ) => ?_)) ?_
      · simp only [hP1]
        have hset : (Finset.univ.filter (fun α : K =>
            α ∈ walkPrefixAlphaEvent (fun i => rlc γ (V i)) (fun i l => rlc γ (Cv i l)) fo h))
            = walkPrefixAlphaEvent (fun i => rlc γ (V i)) (fun i l => rlc γ (Cv i l)) fo h := by
          ext α; simp
        rw [hset]
        exact walkPrefixAlphaEvent_card_le _ _ _ _
      · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hb2 : (Finset.univ.filter (fun p : K × K => P2 p.1 p.2)).card
      ≤ Fintype.card K * (h * (node_size - 1)) := by
    refine le_trans (Finset.card_le_card (?_ : _ ⊆ Finset.univ.biUnion
        (fun α : K => (Finset.univ.filter (fun γ : K => P2 α γ)).image (fun γ => (α, γ))))) ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨p.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩, rfl⟩⟩
    · refine le_trans Finset.card_biUnion_le ?_
      refine le_trans (Finset.sum_le_sum (fun α _ => Finset.card_image_le)) ?_
      refine le_trans (Finset.sum_le_sum (g := fun _ => h * (node_size - 1))
        (fun α (_ : α ∈ Finset.univ) => ?_)) ?_
      · simp only [hP2]
        have hset : (Finset.univ.filter (fun γ : K => γ ∈ prefixBadGammas V Cv fo h))
            = prefixBadGammas V Cv fo h := by ext γ; simp
        rw [hset]
        exact prefixBadGammas_card_le V Cv fo h
      · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  calc _ ≤ (Finset.univ.filter (fun p : K × K => P1 p.1 p.2)
              ∪ Finset.univ.filter (fun p : K × K => P2 p.1 p.2)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter (fun p : K × K => P1 p.1 p.2)).card
          + (Finset.univ.filter (fun p : K × K => P2 p.1 p.2)).card := Finset.card_union_le _ _
    _ ≤ Fintype.card K * max h (1 + Sf fo h) + Fintype.card K * (h * (node_size - 1)) :=
        Nat.add_le_add hb1 hb2

end ComposePrefix

/-! ## G. The `F` side at the prefix: `ReconGoal` at height `prefixLen fo h` -/

section ReconPrefix
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {node_size n : ℕ}
variable {S DT : Type*} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}

/-- **`Thm:Walk_IOP`'s conclusion at the prefix.**  Under the committed per-row `F`-constraints
    on rows `1..prefixLen fo h` ONLY (rows beyond the prefix are not asked anything), the
    state-defined fanout on the prefix, and `PrefixBFT` in its tiling case, there is
    `slt ∈ L_RVT^{F,n}` whose BFS is exactly rows `1..prefixLen fo h` — the tree hanging from
    row 1.  Reuses `reconTree_ReconGoal_of_label` at height `prefixLen fo h`. -/
theorem reconTree_ReconGoal_prefix {L : Type*} (St : StateSep F) (labelOf : S × DT → L)
    (hResp : RespectsChildLabels F labelOf)
    (enc : (S × DT) → (Fin node_size → K))
    (hEnc : ∀ a b, enc a = enc b → labelOf a = labelOf b)
    (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ) {h : ℕ}
    (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ prefixLen fo h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ prefixLen fo h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none))
    (htile : Sf fo (prefixLen fo h) + 1 = prefixLen fo h)
    (hpre : PrefixBFT (fun i => enc (lbl i)) (fun i l => enc (clab i l)) fo h) :
    ReconGoal St lbl (prefixLen fo h) := by
  obtain ⟨hv, hcase⟩ := hpre
  rcases hcase with ⟨_, hbft⟩ | ⟨hkh, hgt, _⟩
  · exact reconTree_ReconGoal_of_label St labelOf hResp enc hEnc lbl clab fo htile hv harity
      hfo hFcommit hbft
  · exfalso; rw [hkh] at htile; omega

/-- The tiling hypothesis of `reconTree_ReconGoal_prefix` is automatic whenever the prefix is
    proper (`prefixLen fo h < h`), i.e. whenever the table is not queue-valid. -/
theorem reconTree_ReconGoal_prefix_of_lt {L : Type*} (St : StateSep F) (labelOf : S × DT → L)
    (hResp : RespectsChildLabels F labelOf)
    (enc : (S × DT) → (Fin node_size → K))
    (hEnc : ∀ a b, enc a = enc b → labelOf a = labelOf b)
    (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ) {h : ℕ} (hh : 1 ≤ h)
    (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ prefixLen fo h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ prefixLen fo h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none))
    (hlt : prefixLen fo h < h)
    (hpre : PrefixBFT (fun i => enc (lbl i)) (fun i l => enc (clab i l)) fo h) :
    ReconGoal St lbl (prefixLen fo h) :=
  reconTree_ReconGoal_prefix St labelOf hResp enc hEnc lbl clab fo harity hfo hFcommit
    (prefixLen_tiling_of_lt fo hh hlt) hpre

end ReconPrefix

/-! ## H. The forest analogue — the memory table is a
  `kMem`-root forest.  Roots occupy positions `1..kroots`; child slot
  `(i, l)` lands at `kroots + l + Σ_{m<i} fanout(m)` (`Walk.firstCF`); queue length before row
  `i` is `kroots + Σ_{m<i} fanout(m) − (i − 1)`. -/

section ForestPrefix
variable {K : Type*} [Field K]

theorem append_getD_lt {α : Type*} (d : α) (l l' : List α) {j : ℕ} (hj : j < l.length) :
    (l ++ l').getD j d = l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem append_getD_ge {α : Type*} (d : α) (l l' : List α) {j : ℕ} (hj : l.length ≤ j) :
    (l ++ l').getD j d = l'.getD (j - l.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right hj]

/-- The forest identity (`Corr:forest`) is padded list equality: roots, then the flattened
    children. -/
theorem isForestFullBFT_iff_getD (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (kroots h : ℕ) :
    IsForestFullBFT cur chld' fo kroots h ↔
      ∀ j, (curVals cur h).getD j 0 = (curVals cur kroots ++ flatBlks chld' fo h).getD j 0 := by
  unfold IsForestFullBFT
  rw [nodeListP_eq_lpoly_gen, forestQueueP_eq_lpoly]
  exact lpoly_eq_iff_getD 1 _ _

/-- **The forest prefix identity.**  The identity at `h` restricts to every `k` with
    `kroots ≤ k ≤ h` at which the aggregate queue empties (`kroots + Sf fo k = k`). -/
theorem isForestFullBFT_prefix {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {kroots h k : ℕ} (hkr : kroots ≤ k) (hk : k ≤ h) (hSfk : kroots + Sf fo k = k)
    (hbft : IsForestFullBFT cur chld' fo kroots h) :
    IsForestFullBFT cur chld' fo kroots k := by
  rw [isForestFullBFT_iff_getD] at hbft ⊢
  intro j
  rcases lt_or_ge j k with hj | hj
  · have h1 : (curVals cur k).getD j 0 = (curVals cur h).getD j 0 := by
      rw [curVals_getD_lt cur hj, curVals_getD_lt cur (lt_of_lt_of_le hj hk)]
    rw [h1, hbft j]
    rcases lt_or_ge j kroots with hjr | hjr
    · rw [append_getD_lt 0 _ _ (by rw [curVals_length]; exact hjr),
        append_getD_lt 0 _ _ (by rw [curVals_length]; exact hjr)]
    · rw [append_getD_ge 0 _ _ (by rw [curVals_length]; exact hjr),
        append_getD_ge 0 _ _ (by rw [curVals_length]; exact hjr), curVals_length]
      exact flatBlks_getD_prefix chld' fo hk (by omega)
  · rw [curVals_getD_ge cur hj,
      getD_ge_length 0 (by rw [List.length_append, curVals_length, flatBlks_length]; omega)]

/-- Forest overflow entries (aggregate queue past position `h`) are RLC-zero. -/
theorem forest_overflow_rlc_zero {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {kroots h : ℕ}
    (hbft : IsForestFullBFT cur chld' fo kroots h) {j : ℕ} (hj : h ≤ kroots + j) :
    (flatBlks chld' fo h).getD j 0 = 0 := by
  rw [isForestFullBFT_iff_getD] at hbft
  have := hbft (kroots + j)
  rw [curVals_getD_ge cur hj, append_getD_ge 0 _ _ (by rw [curVals_length]; omega),
    curVals_length, Nat.add_sub_cancel_left] at this
  exact this.symm

variable (kroots : ℕ) (fo : ℕ → ℕ)

theorem bfsValidF_zero : BFSValidF kroots fo 0 :=
  fun i hi1 hi0 => absurd (le_trans hi1 hi0) (by omega)

theorem bfsValidF_kroots : BFSValidF kroots fo kroots :=
  fun i _ hik => by have := Nat.zero_le (Sf fo (i - 1)); omega

/-- **The forest queue-empty prefix length**: the largest `k ≤ h` with `BFSValidF kroots fo k`. -/
noncomputable def prefixLenF (h : ℕ) : ℕ := Nat.findGreatest (fun k => BFSValidF kroots fo k) h

theorem bfsValidF_prefixLenF (h : ℕ) : BFSValidF kroots fo (prefixLenF kroots fo h) :=
  Nat.findGreatest_spec (Nat.zero_le h) (bfsValidF_zero kroots fo)

theorem prefixLenF_le (h : ℕ) : prefixLenF kroots fo h ≤ h := Nat.findGreatest_le h

theorem kroots_le_prefixLenF {h : ℕ} (hkh : kroots ≤ h) : kroots ≤ prefixLenF kroots fo h :=
  Nat.le_findGreatest hkh (bfsValidF_kroots kroots fo)

theorem not_bfsValidF_of_prefixLenF_lt {h k : ℕ} (hk : prefixLenF kroots fo h < k) (hkh : k ≤ h) :
    ¬ BFSValidF kroots fo k :=
  Nat.findGreatest_is_greatest hk hkh

theorem prefixLenF_eq_of_bfsValidF {h : ℕ} (hv : BFSValidF kroots fo h) :
    prefixLenF kroots fo h = h :=
  le_antisymm (prefixLenF_le kroots fo h) (Nat.le_findGreatest le_rfl hv)

/-- The aggregate queue empties exactly at a proper forest prefix. -/
theorem prefixLenF_tiling_of_lt {h : ℕ} (hk1 : 1 ≤ kroots) (hkh : kroots ≤ h)
    (hlt : prefixLenF kroots fo h < h) :
    kroots + Sf fo (prefixLenF kroots fo h) = prefixLenF kroots fo h := by
  have hkk : kroots ≤ prefixLenF kroots fo h := kroots_le_prefixLenF kroots fo hkh
  have hv : BFSValidF kroots fo (prefixLenF kroots fo h) := bfsValidF_prefixLenF kroots fo h
  have hnv : ¬ BFSValidF kroots fo (prefixLenF kroots fo h + 1) :=
    not_bfsValidF_of_prefixLenF_lt kroots fo (Nat.lt_succ_self _) hlt
  have hvk := hv (prefixLenF kroots fo h) (by omega) le_rfl
  have hmono : Sf fo (prefixLenF kroots fo h - 1) ≤ Sf fo (prefixLenF kroots fo h) :=
    Sf_mono fo (Nat.sub_le _ 1)
  have hfail : ¬ (prefixLenF kroots fo h + 1 ≤ kroots + Sf fo (prefixLenF kroots fo h)) := by
    intro hle
    apply hnv
    intro i hi1 hik
    rcases Nat.lt_or_ge i (prefixLenF kroots fo h + 1) with hlt' | hge
    · exact hv i hi1 (by omega)
    · have : i = prefixLenF kroots fo h + 1 := by omega
      subst this
      simpa using hle
  omega

theorem prefixLenF_dichotomy {h : ℕ} (hk1 : 1 ≤ kroots) (hkh : kroots ≤ h) :
    kroots + Sf fo (prefixLenF kroots fo h) = prefixLenF kroots fo h ∨
      (prefixLenF kroots fo h = h ∧ BFSValidF kroots fo h) := by
  rcases lt_or_eq_of_le (prefixLenF_le kroots fo h) with hlt | heq
  · exact Or.inl (prefixLenF_tiling_of_lt kroots fo hk1 hkh hlt)
  · exact Or.inr ⟨heq, heq ▸ bfsValidF_prefixLenF kroots fo h⟩

/-- Once the aggregate queue has emptied at `k`, rows `> k` place their children beyond `k`. -/
theorem later_rows_children_beyondF {k i : ℕ} (hSfk : kroots + Sf fo k = k) (hki : k < i) :
    k + 1 ≤ firstCF kroots fo i := by
  have hmono : Sf fo k ≤ Sf fo (i - 1) := Sf_mono fo (by omega)
  unfold firstCF; omega

end ForestPrefix

section ForestVecPrefix
variable {K : Type*} [Field K] {node_size : ℕ} [Fintype K] [DecidableEq K]

/-- The forest route's one γ-event. -/
noncomputable def forestPrefixBadGammas (V : ℕ → Fin node_size → K)
    (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) (kroots h : ℕ) : Finset K :=
  BadRLCList (curValsV V h) ((curValsV V kroots ++ flatBlksV Cv fo h).take h)

theorem forestPrefixBadGammas_card_le (V : ℕ → Fin node_size → K)
    (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) (kroots h : ℕ) :
    (forestPrefixBadGammas V Cv fo kroots h).card ≤ h * (node_size - 1) := by
  refine le_trans (badRLCList_card_le _ _) ?_
  apply Nat.mul_le_mul_right
  rw [curValsV_length]; exact min_le_left _ _

theorem badRLCList_forest_prefix_subset (V : ℕ → Fin node_size → K)
    (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) {kroots k h : ℕ} (hkr : kroots ≤ k)
    (hk : k ≤ h) (hSfk : kroots + Sf fo k = k) :
    BadRLCList (curValsV V k) (curValsV V kroots ++ flatBlksV Cv fo k) ⊆
      forestPrefixBadGammas V Cv fo kroots h := by
  intro γ hγ
  simp only [BadRLCList, forestPrefixBadGammas, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_range] at hγ ⊢
  obtain ⟨i, hi, hne, heq⟩ := hγ
  rw [curValsV_length, List.length_append, curValsV_length, flatBlksV_length, hSfk, min_self] at hi
  have hSfh : Sf fo k ≤ Sf fo h := Sf_mono fo hk
  have e1 : (curValsV V k).getD i 0 = (curValsV V h).getD i 0 := by
    rw [curValsV_getD_lt V hi, curValsV_getD_lt V (lt_of_lt_of_le hi hk)]
  have e2 : (curValsV V kroots ++ flatBlksV Cv fo k).getD i 0 =
      ((curValsV V kroots ++ flatBlksV Cv fo h).take h).getD i 0 := by
    rw [take_getD_eq 0 (lt_of_lt_of_le hi hk)]
    rcases lt_or_ge i kroots with hir | hir
    · rw [append_getD_lt 0 _ _ (by rw [curValsV_length]; exact hir),
        append_getD_lt 0 _ _ (by rw [curValsV_length]; exact hir)]
    · rw [append_getD_ge 0 _ _ (by rw [curValsV_length]; exact hir),
        append_getD_ge 0 _ _ (by rw [curValsV_length]; exact hir), curValsV_length]
      exact (flatBlksV_getD_prefix Cv fo hk (by omega)).symm
  refine ⟨i, ?_, ?_, ?_⟩
  · rw [curValsV_length, List.length_take, List.length_append, curValsV_length, flatBlksV_length]
    omega
  · rw [← e1, ← e2]; exact hne
  · rw [← e1, ← e2]; exact heq

/-- The forest route's conclusion at `k = prefixLenF kroots fo h`. -/
def ForestPrefixBFT (V : ℕ → Fin node_size → K) (Cv : ℕ → ℕ → Fin node_size → K)
    (fo : ℕ → ℕ) (kroots h : ℕ) : Prop :=
  BFSValidF kroots fo (prefixLenF kroots fo h) ∧
    ((kroots + Sf fo (prefixLenF kroots fo h) = prefixLenF kroots fo h ∧
        ForestVecBFT V Cv fo kroots (prefixLenF kroots fo h)) ∨
      (prefixLenF kroots fo h = h ∧ h < kroots + Sf fo h ∧
        curValsV V h = (curValsV V kroots ++ flatBlksV Cv fo h).take h))

/-- **Forest vector prefix BFT from the forest identity**, outside `forestPrefixBadGammas`. -/
theorem forestPrefixBFT_of_isForestFullBFT (V : ℕ → Fin node_size → K)
    (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) {kroots h : ℕ} (hk1 : 1 ≤ kroots)
    (hkh : kroots ≤ h) {γ : K} (hγ : γ ∉ forestPrefixBadGammas V Cv fo kroots h)
    (hbft : IsForestFullBFT (fun i => rlc γ (V i)) (fun i l => rlc γ (Cv i l)) fo kroots h) :
    ForestPrefixBFT V Cv fo kroots h := by
  refine ⟨bfsValidF_prefixLenF kroots fo h, ?_⟩
  by_cases htile : kroots + Sf fo (prefixLenF kroots fo h) = prefixLenF kroots fo h
  · left
    refine ⟨htile, ?_⟩
    have hkle : prefixLenF kroots fo h ≤ h := prefixLenF_le kroots fo h
    have hkr : kroots ≤ prefixLenF kroots fo h := kroots_le_prefixLenF kroots fo hkh
    have hbk := isForestFullBFT_prefix hkr hkle htile hbft
    have hscalar := isForestFullBFT_curVals htile hbk
    rw [curVals_rlc, curVals_rlc, flatBlks_rlc, ← List.map_append] at hscalar
    have hlen : (curValsV V (prefixLenF kroots fo h)).length =
        (curValsV V kroots ++ flatBlksV Cv fo (prefixLenF kroots fo h)).length := by
      rw [curValsV_length, List.length_append, curValsV_length, flatBlksV_length]; omega
    have hγ' : γ ∉ BadRLCList (curValsV V (prefixLenF kroots fo h))
        (curValsV V kroots ++ flatBlksV Cv fo (prefixLenF kroots fo h)) :=
      fun hmem => hγ (badRLCList_forest_prefix_subset V Cv fo hkr hkle htile hmem)
    exact rlc_lift_list hlen hγ' hscalar
  · right
    have hkeq : prefixLenF kroots fo h = h := by
      rcases prefixLenF_dichotomy kroots fo hk1 hkh with h1 | ⟨h2, _⟩
      · exact absurd h1 htile
      · exact h2
    have hv : BFSValidF kroots fo h := hkeq ▸ bfsValidF_prefixLenF kroots fo h
    have hgt : h < kroots + Sf fo h := by
      have h1 := hv h (by omega) le_rfl
      have h2 : Sf fo (h - 1) ≤ Sf fo h := Sf_mono fo (Nat.sub_le h 1)
      rw [hkeq] at htile
      omega
    refine ⟨hkeq, hgt, ?_⟩
    rw [isForestFullBFT_iff_getD] at hbft
    have hlen : (curValsV V h).length =
        ((curValsV V kroots ++ flatBlksV Cv fo h).take h).length := by
      rw [curValsV_length, List.length_take, List.length_append, curValsV_length,
        flatBlksV_length]; omega
    have hmap : (curValsV V h).map (rlc γ) =
        ((curValsV V kroots ++ flatBlksV Cv fo h).take h).map (rlc γ) := by
      apply list_eq_of_length_eq_of_getD_eq (0 : K)
      · rw [List.length_map, List.length_map]; exact hlen
      · intro j
        have hb := hbft j
        rw [curVals_rlc, curVals_rlc, flatBlks_rlc, ← List.map_append] at hb
        rw [hb, List.map_take]
        rcases lt_or_ge j h with hj | hj
        · rw [take_getD_eq 0 hj]
        · have hlen' :
              (((curValsV V kroots ++ flatBlksV Cv fo h).map (rlc γ)).take h).length ≤ j := by
            rw [List.length_take, List.length_map, List.length_append, curValsV_length,
              flatBlksV_length]; omega
          rw [getD_ge_length 0 hlen']
          have h0 := hbft j
          rw [curVals_getD_ge _ hj, curVals_rlc, flatBlks_rlc, ← List.map_append] at h0
          exact h0.symm
    exact rlc_lift_list hlen hγ hmap

end ForestVecPrefix

section ForestAlphaEvent
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Degree-free bound on the forest queue polynomial (`Walk.forestQueueP_natDegree_le` carries
    the tiling hypothesis `kroots + Sf fo h ≤ h`). -/
theorem forestQueueP_natDegree_le' (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (kroots h : ℕ) :
    (forestQueueP cur chld' fo kroots h).natDegree ≤ kroots + Sf fo h := by
  have hsum : (∑ i ∈ Finset.Icc 1 h, childSumP chld' fo i).natDegree ≤ Sf fo h := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    refine le_trans (childSumP_natDegree_le chld' fo i) ?_
    have hik := Finset.mem_Icc.mp hi
    have hsi : Sf fo (i - 1) + fo i = Sf fo i := (Sf_pred_succ fo hik.1).symm
    have := Sf_mono fo hik.2
    omega
  unfold forestQueueP
  refine le_trans (natDegree_add_le _ _) ?_
  rw [max_le_iff]
  refine ⟨le_trans (nodeListP_natDegree_le cur kroots) (by omega), ?_⟩
  refine le_trans natDegree_mul_le ?_
  rw [natDegree_X_pow]
  omega

/-- The forest α-event, degree-free: `≤ max h (kroots + Sf fo h)`; the paper's `h/|K|` at
    `Corr:forest` presupposes `kroots + Sf fo h ≤ h`. -/
noncomputable def walkForestPrefixAlphaEvent (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (kroots h : ℕ) : Finset K :=
  if IsForestFullBFT cur chld' fo kroots h then ∅
  else Finset.univ.filter
    (fun r : K => (nodeListP cur h).eval r = (forestQueueP cur chld' fo kroots h).eval r)

theorem walkForestPrefixAlphaEvent_card_le (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (kroots h : ℕ) :
    (walkForestPrefixAlphaEvent cur chld' fo kroots h).card ≤ max h (kroots + Sf fo h) := by
  unfold walkForestPrefixAlphaEvent
  split_ifs with hbft
  · simp
  · exact eval_eq_card_le hbft (le_trans (nodeListP_natDegree_le cur h) (le_max_left _ _))
      (le_trans (forestQueueP_natDegree_le' cur chld' fo kroots h) (le_max_right _ _))

theorem isForestFullBFT_or_mem_alphaEvent {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed initial_count : K} {h kroots : ℕ}
    (hw : WalkSat cur chld' fo ln count acc α seed initial_count h)
    (hseed : seed = (nodeListP cur kroots).eval α) (hic : initial_count = α ^ kroots)
    (hout : acc h = 0) :
    IsForestFullBFT cur chld' fo kroots h ∨
      α ∈ walkForestPrefixAlphaEvent cur chld' fo kroots h := by
  by_cases hbft : IsForestFullBFT cur chld' fo kroots h
  · exact Or.inl hbft
  · right
    unfold walkForestPrefixAlphaEvent
    rw [if_neg hbft, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (forest_out_zero_iff hw hseed hic).mp hout⟩

end ForestAlphaEvent

section ForestReconPrefix
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {node_size n : ℕ}
variable {S DT : Type*} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}

/-- **`Corr:forest`'s conclusion at the forest prefix**: `ForestReconGoal` at height
    `prefixLenF kroots fo h`, from the per-row `F`-constraints on the prefix only. -/
theorem reconForest_ForestReconGoal_prefix {L : Type*} (St : StateSep F)
    (labelOf : S × DT → L) (hResp : RespectsChildLabels F labelOf)
    (enc : (S × DT) → (Fin node_size → K))
    (hEnc : ∀ a b, enc a = enc b → labelOf a = labelOf b)
    (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ) {kroots h : ℕ} (hk : 1 ≤ kroots)
    (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ prefixLenF kroots fo h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ prefixLenF kroots fo h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none))
    (htile : kroots + Sf fo (prefixLenF kroots fo h) = prefixLenF kroots fo h)
    (hpre : ForestPrefixBFT (fun i => enc (lbl i)) (fun i l => enc (clab i l)) fo kroots h) :
    ForestReconGoal St lbl kroots (prefixLenF kroots fo h) := by
  obtain ⟨hv, hcase⟩ := hpre
  rcases hcase with ⟨_, hbft⟩ | ⟨hkh, hgt, _⟩
  · exact reconForest_ForestReconGoal_of_label St labelOf hResp enc hEnc lbl clab fo hk htile hv
      harity hfo hFcommit hbft
  · exfalso; rw [hkh] at htile; omega

end ForestReconPrefix

end Walk
end Nock
