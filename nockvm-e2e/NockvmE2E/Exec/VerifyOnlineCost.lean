/-
  NockvmE2E/Exec/VerifyOnlineCost.lean   

  Cost of `verifyOnline`: every loop is over a list whose length is bounded by (l, k, nD, c, r, d, #tabs, |DAG|, ...), never by `hN`.

  WHAT IS PROVED (kernel) and WHAT IS A MODEL (labels):
   [kernel, linked] `goRootT` = a tick-counting copy of `goRootF` with `(goRootT ..).1 = goRootF ..` (the Merkle recursion, the one
        loop whose trip count is not visible from the source);  `goRootT_calls_le`: calls <= |sel| * (e + 1) + 1 under `LbWell sel`, which holds for every tree of `verifyOnline` (`treeSel_sorted`, `lbWell_of_sorted`).
   [kernel] the sizes of the lists the loops range over: `treeSel`, `sortedDistinct`, `openPts`, `openingList`, `fixOps`, `blockLayout`.
   [model]  `TripVec` collects one natural per loop family, each field is literally the length of the list in the source of
        `verifyOnlineE` / `verifyFix`; `costModel` charges unit cost per iteration (field ops, one Tip5 permutation, nested loops
        multiplied).  It is NOT a step semantics of the Lean program; `verifyOnline_cost` bounds `costModel`.
   Not covered: the cost of `X.pubCheck` (instance-data function, claim size, opaque); `verifyOnline` itself is not ticked, so
   the link from the model to the program is by inspection of the loops, except for `goRootT`.
-/
import NockvmE2E.Exec.VerifyOnline
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec.VF

/-! ### A. the Merkle recursion: a ticked copy of `goRootF` and its call count -/

/-- `goRootF` with a call counter (every call, including the failing ones, is one tick) -/
def goRootT (H : HFn) (sp : TSpec) (j : Nat) (sel : Array Nat) (leaf : Nat → Dg5) (sibs : Array Dg5) :
    Nat → Nat → Nat → Nat → Nat → Option (Dg5 × Nat) × Nat
  | 0, _, _, _, _ => (none, 1)
  | f + 1, idx, lo, cnt, s =>
  if cnt == 1 then
    let r := lb sel lo
    (if sel[r]? == some lo then some (leaf r, s) else none, 1)
  else
    let L := sp.split cnt
    if L == 0 || L ≥ cnt then (none, 1) else
    let a := lb sel lo
    let b := lb sel (lo + L)
    let c := lb sel (lo + cnt)
    let node (l r : Dg5) : Dg5 := H ([tagNode, j, idx] ++ l ++ r)
    if b > a && c > b then
      let p1 := goRootT H sp j sel leaf sibs f (2 * idx) lo L s
      match p1.1 with
      | none => (none, p1.2 + 1)
      | some (l, s1) =>
        let p2 := goRootT H sp j sel leaf sibs f (2 * idx + 1) (lo + L) (cnt - L) s1
        match p2.1 with
        | none => (none, p1.2 + p2.2 + 1)
        | some (r, s2) => (some (node l r, s2), p1.2 + p2.2 + 1)
    else if b > a then
      match sibs[s]? with
      | none => (none, 1)
      | some sib =>
        let p1 := goRootT H sp j sel leaf sibs f (2 * idx) lo L (s + 1)
        match p1.1 with
        | none => (none, p1.2 + 1)
        | some (l, s1) => (some (node l sib, s1), p1.2 + 1)
    else if c > b then
      match sibs[s]? with
      | none => (none, 1)
      | some sib =>
        let p1 := goRootT H sp j sel leaf sibs f (2 * idx + 1) (lo + L) (cnt - L) (s + 1)
        match p1.1 with
        | none => (none, p1.2 + 1)
        | some (r, s1) => (some (node sib r, s1), p1.2 + 1)
    else (none, 1)

/-- the ticked copy computes the same result as `goRootF` -/
theorem goRootT_fst (H : HFn) (sp : TSpec) (j : Nat) (sel : Array Nat) (leaf : Nat → Dg5) (sibs : Array Dg5) :
    ∀ (f idx lo cnt s : Nat), (goRootT H sp j sel leaf sibs f idx lo cnt s).1 = goRootF H sp j sel leaf sibs f idx lo cnt s := by
  intro f
  induction f with
  | zero => intro idx lo cnt s; simp [goRootT, goRootF]
  | succ f ih =>
    intro idx lo cnt s
    simp only [goRootT, goRootF]
    by_cases h1 : cnt == 1
    · simp [h1]
    · simp only [h1, ite_false, Bool.false_eq_true]
      by_cases hL : (sp.split cnt == 0 || decide (sp.split cnt ≥ cnt)) = true
      · simp [hL]
      · simp only [hL, ite_false, Bool.false_eq_true]
        by_cases hb : (lb sel (lo + sp.split cnt) > lb sel lo && lb sel (lo + cnt) > lb sel (lo + sp.split cnt)) = true
        · simp only [hb, ite_true]
          have e1 := ih (2 * idx) lo (sp.split cnt) s
          rcases hp : goRootT H sp j sel leaf sibs f (2 * idx) lo (sp.split cnt) s with ⟨r1, n1⟩
          rw [hp] at e1
          simp only at e1
          rw [← e1]
          cases r1 with
          | none => simp
          | some v =>
            obtain ⟨l, s1⟩ := v
            have e2 := ih (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) s1
            rcases hq : goRootT H sp j sel leaf sibs f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) s1 with ⟨r2, n2⟩
            rw [hq] at e2
            simp only at e2
            simp only [hq]
            show _ = Option.bind (some (l, s1)) _
            rw [Option.bind_some, ← e2]
            cases r2 <;> simp
        · simp only [hb, ite_false, Bool.false_eq_true]
          by_cases hb2 : lb sel (lo + sp.split cnt) > lb sel lo
          · simp only [hb2, ite_true]
            cases hs : sibs[s]? with
            | none => simp
            | some sib =>
              have e1 := ih (2 * idx) lo (sp.split cnt) (s + 1)
              rcases hp : goRootT H sp j sel leaf sibs f (2 * idx) lo (sp.split cnt) (s + 1) with ⟨r1, n1⟩
              rw [hp] at e1
              simp only at e1
              rw [← e1]
              cases r1 <;> simp
          · simp only [hb2, ite_false]
            by_cases hb3 : lb sel (lo + cnt) > lb sel (lo + sp.split cnt)
            · simp only [hb3, ite_true]
              cases hs : sibs[s]? with
              | none => simp
              | some sib =>
                have e1 := ih (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) (s + 1)
                rcases hp : goRootT H sp j sel leaf sibs f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) (s + 1) with ⟨r1, n1⟩
                rw [hp] at e1
                simp only at e1
                rw [← e1]
                cases r1 <;> simp
            · simp [hb3]

/-- `lb` on the selected-leaf array behaves like a counting function: monotone and at most `sel.size`
(true for strictly sorted arrays, which is what `treeSel` produces; instantiated in the report) -/
def LbWell (sel : Array Nat) : Prop := (∀ x y, x ≤ y → lb sel x ≤ lb sel y) ∧ (∀ x, lb sel x ≤ sel.size)

/-- both tree skeletons (`ragSpec`, `friSpec`) split a node of `cnt ≥ 2` leaves into parts of at most `⌈cnt/2⌉` leaves -/
def SpecHalf (sp : TSpec) : Prop :=
  ∀ cnt, 2 ≤ cnt → 0 < sp.split cnt → sp.split cnt < cnt → sp.split cnt ≤ (cnt + 1) / 2 ∧ cnt - sp.split cnt ≤ (cnt + 1) / 2

theorem friSpec_half (total : Nat) : SpecHalf (friSpec total) := by
  intro cnt h2 h0 h1; simp only [friSpec] at *; omega

theorem ragSpec_half (W half : Nat) : SpecHalf (ragSpec W half) := by
  intro cnt h2 h0 h1
  simp only [ragSpec] at *
  by_cases a : cnt > 2 * W
  · simp only [a, ite_true] at *; omega
  · by_cases b : cnt == 2 * W
    · have hb' : cnt = 2 * W := by simpa using b
      simp only [a, b, ite_true, ite_false] at *
      omega
    · simp only [a, b, ite_false, Bool.false_eq_true] at *; omega

theorem call_arith2 (A B C e n1 n2 : Nat) (hAB : A < B) (hBC : B < C) (he : 1 ≤ e)
    (h1 : n1 ≤ max 1 ((B - A) * e)) (h2 : n2 ≤ max 1 ((C - B) * e)) :
    n1 + n2 + 1 ≤ max 1 ((C - A) * (e + 1)) := by
  obtain ⟨m1, hm1⟩ : ∃ m1, B - A = m1 := ⟨_, rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ m2, C - B = m2 := ⟨_, rfl⟩
  have hm : C - A = m1 + m2 := by omega
  rw [hm1] at h1; rw [hm2] at h2; rw [hm]
  have p1 : 1 ≤ m1 * e := Nat.mul_pos (by omega) he
  have p2 : 1 ≤ m2 * e := Nat.mul_pos (by omega) he
  have q := Nat.le_max_right 1 ((m1 + m2) * (e + 1))
  have q2 : (m1 + m2) * (e + 1) = m1 * e + m2 * e + m1 + m2 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]; omega
  rw [Nat.max_eq_right p1] at h1; rw [Nat.max_eq_right p2] at h2
  omega

theorem call_arith1 (A B C e n : Nat) (hAB : A < B) (he : 1 ≤ e)
    (h1 : n ≤ max 1 ((B - A) * e)) (hCB : C - A = B - A) :
    n + 1 ≤ max 1 ((C - A) * (e + 1)) := by
  rw [hCB]
  obtain ⟨m1, hm1⟩ : ∃ m1, B - A = m1 := ⟨_, rfl⟩
  rw [hm1] at h1 ⊢
  have p1 : 1 ≤ m1 * e := Nat.mul_pos (by omega) he
  have q := Nat.le_max_right 1 (m1 * (e + 1))
  have q2 : m1 * (e + 1) = m1 * e + m1 := by simp only [Nat.mul_add, Nat.mul_one]
  rw [Nat.max_eq_right p1] at h1
  omega

/-- the number of calls of the Merkle recursion over a node with `m` selected leaves in a subtree of at most `2^e` leaves:
`≤ max 1 (m * (e + 1))`, i.e. `|sel| · depth`, not the number of leaves of the tree -/
theorem goRootT_calls_le (H : HFn) (sp : TSpec) (j : Nat) (sel : Array Nat) (leaf : Nat → Dg5) (sibs : Array Dg5)
    (hsp : SpecHalf sp) (hl : LbWell sel) :
    ∀ (f e idx lo cnt s : Nat), cnt ≤ 2 ^ e →
      (goRootT H sp j sel leaf sibs f idx lo cnt s).2 ≤ max 1 ((lb sel (lo + cnt) - lb sel lo) * (e + 1)) := by
  obtain ⟨hmono, hbd⟩ := hl
  intro f
  induction f with
  | zero => intro e idx lo cnt s _; simp [goRootT, Nat.le_max_left]
  | succ f ih =>
    intro e idx lo cnt s hc
    simp only [goRootT]
    by_cases h1 : cnt == 1
    · simp [h1, Nat.le_max_left]
    · simp only [h1, ite_false, Bool.false_eq_true]
      by_cases hL : (sp.split cnt == 0 || decide (sp.split cnt ≥ cnt)) = true
      · simp [hL, Nat.le_max_left]
      · simp only [hL, ite_false, Bool.false_eq_true]
        have hne : sp.split cnt ≠ 0 := by intro h; apply hL; simp [h]
        have hlt : sp.split cnt < cnt := Nat.lt_of_not_ge (fun h => hL (by simp [h]))
        have hc1 : cnt ≠ 1 := by simpa using h1
        have hc0 : cnt ≠ 0 := by intro h; subst h; omega
        have h2 : 2 ≤ cnt := by omega
        obtain ⟨hs1, hs2⟩ := hsp cnt h2 (by omega) hlt
        have he : 1 ≤ e := by
          cases e with
          | zero => simp at hc; omega
          | succ e => omega
        obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
        have hpow : 2 ^ (e' + 1) = 2 * 2 ^ e' := by rw [Nat.pow_succ]; omega
        have hc1' : sp.split cnt ≤ 2 ^ e' := by omega
        have hc2' : cnt - sp.split cnt ≤ 2 ^ e' := by omega
        have m1 := hmono lo (lo + sp.split cnt) (by omega)
        have m2 := hmono (lo + sp.split cnt) (lo + cnt) (by omega)
        have hr : lo + sp.split cnt + (cnt - sp.split cnt) = lo + cnt := by omega
        have i1 := fun s' => ih e' (2 * idx) lo (sp.split cnt) s' hc1'
        have i2 := fun s1 => ih e' (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) s1 hc2'
        simp only [hr] at i2
        have hone : ∀ n, n ≤ 1 → n ≤ max 1 ((lb sel (lo + cnt) - lb sel lo) * (e' + 1 + 1)) :=
          fun n hn => Nat.le_trans hn (Nat.le_max_left _ _)
        by_cases hb : (lb sel (lo + sp.split cnt) > lb sel lo && lb sel (lo + cnt) > lb sel (lo + sp.split cnt)) = true
        · simp only [hb, ite_true]
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
          obtain ⟨hb1, hb2⟩ := hb
          have a2 := fun n1 n2 => call_arith2 (lb sel lo) (lb sel (lo + sp.split cnt)) (lb sel (lo + cnt)) (e' + 1) n1 n2 hb1 hb2 (by omega)
          rcases hp : goRootT H sp j sel leaf sibs f (2 * idx) lo (sp.split cnt) s with ⟨r1, n1⟩
          have j1 := i1 s
          rw [hp] at j1; simp only at j1
          cases r1 with
          | none => have := a2 n1 0 j1 (Nat.le_max_left _ _); simp only; omega
          | some v =>
            obtain ⟨l, s1⟩ := v
            rcases hq : goRootT H sp j sel leaf sibs f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) s1 with ⟨r2, n2⟩
            have j2 := i2 s1
            rw [hq] at j2; simp only at j2
            have := a2 n1 n2 j1 j2
            simp only [hq]
            cases r2 <;> simp only <;> omega
        · simp only [hb, ite_false, Bool.false_eq_true]
          simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hb
          by_cases hb2 : lb sel (lo + sp.split cnt) > lb sel lo
          · simp only [hb2, ite_true]
            have hceq : lb sel (lo + cnt) = lb sel (lo + sp.split cnt) := by have := hb hb2; omega
            cases hs : sibs[s]? with
            | none => simp [Nat.le_max_left]
            | some sib =>
              simp only
              have a1 := fun n => call_arith1 (lb sel lo) (lb sel (lo + sp.split cnt)) (lb sel (lo + cnt)) (e' + 1) n hb2 (by omega)
              rcases hp : goRootT H sp j sel leaf sibs f (2 * idx) lo (sp.split cnt) (s + 1) with ⟨r1, n1⟩
              have j1 := i1 (s + 1)
              rw [hp] at j1; simp only at j1
              have := a1 n1 j1 (by omega)
              cases r1 <;> simp only <;> omega
          · simp only [hb2, ite_false]
            by_cases hb3 : lb sel (lo + cnt) > lb sel (lo + sp.split cnt)
            · simp only [hb3, ite_true]
              have haeq : lb sel (lo + sp.split cnt) = lb sel lo := by omega
              cases hs : sibs[s]? with
              | none => simp [Nat.le_max_left]
              | some sib =>
                simp only
                have a1 := fun n => call_arith1 (lb sel lo) (lb sel (lo + cnt)) (lb sel (lo + cnt)) (e' + 1) n (by omega) (by omega)
                rcases hp : goRootT H sp j sel leaf sibs f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) (s + 1) with ⟨r1, n1⟩
                have j1 := i2 (s + 1)
                rw [hp] at j1; simp only [haeq] at j1
                have := a1 n1 j1 (by omega)
                cases r1 <;> simp only <;> omega
            · simp [hb3, Nat.le_max_left]

/-- the whole recursion of `goRoot` (`lo = 0`, `cnt = total ≤ 2^e`): at most `1 + |sel| · (e + 1)` calls -/
theorem goRoot_calls_le (H : HFn) (sp : TSpec) (j : Nat) (sel : Array Nat) (leaf : Nat → Dg5) (sibs : Array Dg5)
    (hsp : SpecHalf sp) (hl : LbWell sel) (e : Nat) (he : sp.total ≤ 2 ^ e) :
    (goRootT H sp j sel leaf sibs sp.total 1 0 sp.total 0).2 ≤ 1 + sel.size * (e + 1) := by
  have h := goRootT_calls_le H sp j sel leaf sibs hsp hl sp.total e 1 0 sp.total 0 he
  have h2 : lb sel (0 + sp.total) - lb sel 0 ≤ sel.size := by have := hl.2 (0 + sp.total); omega
  have h3 := Nat.mul_le_mul_right (e + 1) h2
  have h4 := Nat.le_max_right 1 ((lb sel (0 + sp.total) - lb sel 0) * (e + 1))
  have h5 := Nat.le_max_left 1 ((lb sel (0 + sp.total) - lb sel 0) * (e + 1))
  rcases Nat.le_total 1 ((lb sel (0 + sp.total) - lb sel 0) * (e + 1)) with h6 | h6
  · rw [Nat.max_eq_right h6] at h; omega
  · rw [Nat.max_eq_left h6] at h; omega

/-! ### B. sizes of the lists the loops range over -/

theorem sum_map_le {α : Type} (g : α → Nat) (B : Nat) : ∀ xs : List α, (∀ x ∈ xs, g x ≤ B) → (xs.map g).sum ≤ xs.length * B
  | [], _ => by simp
  | x :: xs, h => by
    have h1 := h x (by simp)
    have h2 := sum_map_le g B xs (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- a fold that pushes at most `B` entries per step -/
theorem foldl_push_size {α γ β : Type} (f : Array γ × β → α → Array γ × β) (B : Nat)
    (h : ∀ st x, (f st x).1.size ≤ st.1.size + B) :
    ∀ (xs : List α) (st : Array γ × β), (xs.foldl f st).1.size ≤ st.1.size + xs.length * B
  | [], st => by simp
  | x :: xs, st => by
    have := foldl_push_size f B h xs (f st x)
    have := h st x
    simp only [List.foldl_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem insertD_length (x : Nat) : ∀ l : List Nat, (insertD x l).length ≤ l.length + 1
  | [] => by simp [insertD]
  | y :: ys => by
    simp only [insertD]
    split
    · simp
    · split
      · simp
      · have := insertD_length x ys
        simp only [List.length_cons]; omega

theorem sortedDistinct_size (a : Array Nat) : (sortedDistinct a).size ≤ a.size := by
  have key : ∀ (xs acc : List Nat), (xs.foldl (fun acc x => insertD x acc) acc).length ≤ acc.length + xs.length := by
    intro xs
    induction xs with
    | nil => intro acc; simp
    | cons x xs ih =>
      intro acc
      have := ih (insertD x acc)
      have := insertD_length x acc
      simp only [List.foldl_cons, List.length_cons]; omega
  have := key a.toList []
  simpa [sortedDistinct] using this

/-- the selected leaves of a tree: at most `2·W` per query position (RAP trees) / 2 per query position (FRI trees) -/
theorem treeSel_size_le (X : ExecInst) (Wb j : Nat) (pos : Array Nat) :
    (treeSel X Wb j pos).size ≤ 2 * (Wb + 1) * pos.size := by
  have gen : ∀ (g : Array Nat) (B : Nat) (f : Nat → Array Nat), (∀ x, (f x).size ≤ B) →
      (g.flatMap f).size ≤ g.size * B := by
    intro g B f hf
    rw [Array.size_flatMap, ← Array.sum_eq_sum_toList, Array.toList_map]
    have := sum_map_le (fun a => (f a).size) B g.toList (fun x _ => hf x)
    simpa using this
  have hs := sortedDistinct_size (pos.map (· % 2 ^ (X.nD - 1)))
  have hs' := sortedDistinct_size (pos.map (· % 2 ^ (X.nD - (j - 3) - 1)))
  simp only [Array.size_map] at hs hs'
  unfold treeSel
  split
  · split
    · simp
    · have h3 := Nat.mul_le_mul_right (2 * Wb) hs
      have h4 : pos.size * (2 * Wb) ≤ 2 * (Wb + 1) * pos.size := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
      refine Nat.le_trans (gen _ (2 * Wb) _ (by intro x; simp)) ?_
      omega
  · have h3 := Nat.mul_le_mul_right 2 hs'
    have h4 : pos.size * 2 ≤ 2 * (Wb + 1) * pos.size := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
    refine Nat.le_trans (gen _ 2 _ (by intro x; simp)) ?_
    omega

theorem openPts_size (X : ExecInst) (zeta : K3) : (openPts X zeta).size = X.r + 2 := by
  have key : ∀ (xs : List Nat) (st : Array K3 × K3),
      (xs.foldl (fun (st : Array K3 × K3) _ => (st.1.push (K3.mul zeta st.2), K3.smul X.hGen st.2)) st).1.size = st.1.size + xs.length := by
    intro xs
    induction xs with
    | nil => intro st; simp
    | cons x xs ih => intro st; simp only [List.foldl_cons, List.length_cons]; rw [ih]; simp; omega
  unfold openPts
  simp only [Array.size_push]
  rw [key]; simp

theorem openingList_size_le (X : ExecInst) (cs : K3) (vT : Array (Array K3)) (vQ : Array K3) :
    (openingList X cs vT vQ).size ≤ (X.nc + X.nq) * (X.r + 1) := by
  unfold openingList
  refine Nat.le_trans (foldl_push_size _ (X.r + 1) ?_ _ _) (by simp)
  intro st c
  split
  all_goals first
    | (refine Nat.le_trans (foldl_push_size _ 1 ?_ _ _) ?_ <;>
        first | (intro st' x; simp; done) | (simp only [List.length_range]; omega))
    | (simp <;> omega)

theorem fixLen_le (X : ExecInst) (c : FixCol) : fixLen X c ≤ X.r + 1 := by
  cases c <;> simp [fixLen] <;> omega

theorem fixOps_size_le (X : ExecInst) (cols : Array FixCol) (cs : K3) (vF : Array (Array K3)) :
    (fixOps X cols cs vF).size ≤ cols.size * (X.r + 1) := by
  unfold fixOps
  refine Nat.le_trans (foldl_push_size _ (X.r + 1) ?_ _ _) (by simp)
  intro st j
  refine Nat.le_trans (foldl_push_size _ 1 ?_ _ _) ?_ <;> first | (intro st' x; simp; done) | skip
  have := fixLen_le X cols[j]!
  simp only [List.length_range]; omega

/-- every block width `W_b` is at most the number of columns -/
theorem blockLayout_le (X : ExecInst) (j : Nat) : (blockLayout X).1.getD j 0 ≤ X.nc + X.nq := by
  unfold blockLayout
  have key : ∀ (xs : List Nat) (st : Array Nat × Array Nat) (n0 : Nat), st.1.size = 4 → (∀ j, st.1.getD j 0 ≤ n0) →
      (xs.foldl (fun (st : Array Nat × Array Nat) c =>
        if X.blockOf[c]! < 4 then (st.1.modify X.blockOf[c]! (· + 1), st.2.set! c st.1[X.blockOf[c]!]!) else st) st).1.size = 4 ∧
      ∀ j, (xs.foldl (fun (st : Array Nat × Array Nat) c =>
        if X.blockOf[c]! < 4 then (st.1.modify X.blockOf[c]! (· + 1), st.2.set! c st.1[X.blockOf[c]!]!) else st) st).1.getD j 0 ≤ n0 + xs.length := by
    intro xs
    induction xs with
    | nil => intro st n0 h1 h2; exact ⟨h1, by simpa using h2⟩
    | cons x xs ih =>
      intro st n0 h1 h2
      simp only [List.foldl_cons, List.length_cons]
      have step : ∀ st' : Array Nat × Array Nat, st'.1.size = 4 ∧ (∀ j, st'.1.getD j 0 ≤ n0 + 1) → True := fun _ _ => trivial
      by_cases hb : X.blockOf[x]! < 4
      · simp only [hb, ite_true]
        have := ih (st.1.modify X.blockOf[x]! (· + 1), st.2.set! x st.1[X.blockOf[x]!]!) (n0 + 1)
          (by simpa using h1)
          (by
            intro j'
            simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
            by_cases hj : X.blockOf[x]! = j'
            · simp only [hj, ite_true]
              have := h2 j'
              simp only [Array.getD_eq_getD_getElem?] at this
              cases hh : st.1[j']? <;> simp [hh] at this ⊢ <;> omega
            · simp only [hj, ite_false]
              have := h2 j'
              simp only [Array.getD_eq_getD_getElem?] at this
              omega)
        constructor
        · exact this.1
        · intro j'; have := this.2 j'; omega
      · simp only [hb, ite_false]
        have := ih st n0 h1 h2
        constructor
        · exact this.1
        · intro j'; have := this.2 j'; omega
  have := (key (List.range (X.nc + X.nq)) (Array.replicate 4 0, Array.replicate (X.nc + X.nq) 0) 0 (by simp) (by
    intro j'; simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]; split <;> simp)).2 j
  simpa using this

/-! ### C. the cost model and the theorem -/

/-- the parameters the cost depends on.  There is **no `hN` here**: `hb` is the bit length of `hN` (the only place the trace height
enters: `K3.pow ζ hN`, square-and-multiply), and `Dims.ofJ8` shows `hb ≤ nD + 1`.  `c = nc + nq`, `nT = #tabs`, `nder = |derived|`,
`derC` = total bit length of the derived-slot exponents, `npub = |pubOf|`, `Wm` = max RAP block width (`≤ c`, `blockLayout_le`),
`dag` = |DAG| (all chip expression nodes incl. the bit lengths of their `pow` exponents, plus the columns/publics each table reads),
`nco` = number of coin limbs, `F = |fixed columns|`, `zLen`, `piLen`, `pfLen` = sizes of the statement / main proof / side proof. -/
structure Dims where
  l : Nat
  k : Nat
  nD : Nat
  r : Nat
  d : Nat
  nq : Nat
  c : Nat
  F : Nat
  nT : Nat
  nder : Nat
  derC : Nat
  npub : Nat
  Wm : Nat
  dag : Nat
  hb : Nat
  nco : Nat
  zLen : Nat
  piLen : Nat
  pfLen : Nat

/-- the model: one unit per field operation / loop iteration / Tip5 permutation, nested loops multiplied -/
def costModel (P : Dims) : Nat :=
  let sel := 2 * (P.Wm + 1) * P.l                      -- selected leaves of one tree (`treeSel_size_le`)
  let calls := 1 + sel * (P.nD + P.Wm + 1)             -- goRoot calls (`goRoot_calls_le`)
  let nodeC := 3 * sel + 5                             -- 3 `lb` (each ≤ |sel| + 1 steps) + one hash
  let treeC := P.l * P.l + 2 * sel + calls * nodeC + sel + 1   -- sortedDistinct + treeSel + goRoot + the leaf checks
  let fsIn := P.zLen + 5 * (P.k + 4) + 3 * (P.c * (P.r + 1)) + 3 * P.d + 3 * P.nq + 1
  let fsOut := 3 * P.nco + P.l + 3
  let fsC := (P.k + 9) * (fsIn + fsOut + 2)            -- every FS call hashes the whole prefix
  let wordC := P.c * (P.r + 1) * (sel + P.nD + 80) + (P.r + 2) * 80 + P.nD + 1   -- `deepWord`
  let friQ := 2 * wordC + P.k * (2 * sel + 2 * P.nD + 10) + P.d + P.nD + 10      -- one FRI query
  let deepC := P.dag + P.derC + P.c + P.nT + P.npub + P.hb + P.nq * (P.nq + 1) + (P.r + 2) * (P.nD + 1) +
    P.c * P.r + P.F + P.nco + 10
  (P.zLen + P.piLen + P.pfLen) + 2 * fsC + 2 * (P.k + 4) * treeC + deepC + 2 * P.l * friQ + P.c + P.F + 10

/-- the total size parameter -/
def Dims.S (P : Dims) : Nat :=
  P.l + P.k + P.nD + P.r + P.d + P.nq + P.c + P.F + P.nT + P.nder + P.derC + P.npub + P.Wm + P.dag + P.hb + P.nco +
    P.zLen + P.piLen + P.pfLen + 1

/-- **cost is polynomial in the parameters** (no `hN`): `costModel P ≤ 6000 · S^6` (all coefficients summed: 5064) -/
theorem costModel_le (P : Dims) : costModel P ≤ 6000 * P.S ^ 6 := by
  have hS : ∀ x, x ≤ P.S → True := fun _ _ => trivial
  have h1 : 1 ≤ P.S := by simp [Dims.S]
  have hl : P.l ≤ P.S := by simp [Dims.S]; omega
  have hk : P.k ≤ P.S := by simp [Dims.S]; omega
  have hnD : P.nD ≤ P.S := by simp [Dims.S]; omega
  have hr : P.r ≤ P.S := by simp [Dims.S]; omega
  have hd : P.d ≤ P.S := by simp [Dims.S]; omega
  have hnq : P.nq ≤ P.S := by simp [Dims.S]; omega
  have hc : P.c ≤ P.S := by simp [Dims.S]; omega
  have hF : P.F ≤ P.S := by simp [Dims.S]; omega
  have hnT : P.nT ≤ P.S := by simp [Dims.S]; omega
  have hderC : P.derC ≤ P.S := by simp [Dims.S]; omega
  have hnpub : P.npub ≤ P.S := by simp [Dims.S]; omega
  have hWm : P.Wm ≤ P.S := by simp [Dims.S]; omega
  have hdag : P.dag ≤ P.S := by simp [Dims.S]; omega
  have hhb : P.hb ≤ P.S := by simp [Dims.S]; omega
  have hnco : P.nco ≤ P.S := by simp [Dims.S]; omega
  have hz : P.zLen ≤ P.S := by simp [Dims.S]; omega
  have hpi : P.piLen ≤ P.S := by simp [Dims.S]; omega
  have hpf : P.pfLen ≤ P.S := by simp [Dims.S]; omega
  have mono : costModel P ≤ costModel ⟨P.S, P.S, P.S, P.S, P.S, P.S, P.S, P.S, P.S, P.S, P.S, P.S, P.S, P.S, P.S, P.S, P.S, P.S, P.S⟩ := by
    unfold costModel
    simp only []
    gcongr
  refine Nat.le_trans mono ?_
  generalize P.S = S at *
  unfold costModel
  simp only []
  ring_nf
  have p : ∀ j, j ≤ 6 → S ^ j ≤ S ^ 6 := fun j hj => Nat.pow_le_pow_right h1 hj
  have := p 0 (by omega); have := p 1 (by omega); have := p 2 (by omega); have := p 3 (by omega)
  have := p 4 (by omega); have := p 5 (by omega); have := p 6 (by omega)
  linarith

/-! ### D. the model instantiated on a verifier run: every loop is over one of the lists of `Dims` -/

/-- node count of a constraint expression, charging a `pow` its exponent bit length (square-and-multiply) -/
def exSize : Tr.Ex → Nat
  | .add a b => 1 + exSize a + exSize b
  | .sub a b => 1 + exSize a + exSize b
  | .mul a b => 1 + exSize a + exSize b
  | .neg a => 1 + exSize a
  | .pow a n => 2 + Nat.log2 n + exSize a
  | _ => 1

/-- |DAG|: per table, the columns and publics it reads, its shared nodes and its constraints (`evalDag`, `curNxt` slices) -/
def dagSize (X : ExecInst) : Nat :=
  (X.tabs.toList.map fun t =>
    1 + t.nc + t.npub + (t.chip.shared.toList.map exSize).sum + (t.chip.cons.toList.map (fun c => exSize c.e)).sum).sum

def derivedBits (X : ExecInst) : Nat := (X.derived.toList.map fun be => Nat.log2 be.2 + 1).sum

def limbsOf (a : Array (List Nat)) : Nat := (a.toList.map List.length).sum
def proofSize (π : FlatProof) : Nat :=
  π.roots.size + limbsOf π.roots + π.vT.size + (π.vT.toList.map (·.size)).sum + π.vQ.size + π.pfinal.size + π.pos.size +
    π.vals.size + (π.vals.toList.map (·.size)).sum + π.sibs.size + (π.sibs.toList.map (fun a => a.size + limbsOf a)).sum

def fixSize (πF : FixProof) : Nat :=
  πF.vF.size + (πF.vF.toList.map (·.size)).sum + πF.pfinal.size + πF.pos.size + πF.roots.size + limbsOf πF.roots +
    πF.vals.size + (πF.vals.toList.map (·.size)).sum + πF.sibs.size + (πF.sibs.toList.map (fun a => a.size + limbsOf a)).sum

/-- the parameters of one verifier run.  `hb := nD + 1` stands for the bit length of `hN` (`bits_hN_le`): `hN` itself does not occur. -/
def Dims.ofRun (vk : VK) (z : List Nat) (π : FlatProof) (πF : FixProof) : Dims :=
  { l := vk.X.l, k := vk.X.k, nD := vk.X.nD, r := vk.X.r, d := vk.X.d, nq := vk.X.nq, c := vk.X.nc + vk.X.nq,
    F := vk.cols.size, nT := vk.X.tabs.size, nder := vk.X.derived.size, derC := derivedBits vk.X,
    npub := vk.X.pubOf.size, Wm := vk.X.nc + vk.X.nq + vk.cols.size, dag := dagSize vk.X, hb := vk.X.nD + 1,
    nco := vk.X.nCoins[0]! + vk.X.nCoins[1]!, zLen := z.length, piLen := proofSize π, pfLen := fixSize πF }

/-- the only trace-height dependence of the verifier: `K3.pow ζ hN` takes `log₂ hN + 1 ≤ nD + 1` squarings (J-8: `hN = 2^(k+1)`, `nD = k + 7`) -/
theorem bits_hN_le (hN nD : Nat) (h : hN ≤ 2 ^ nD) : Nat.log2 hN + 1 ≤ nD + 1 := by
  by_cases h0 : hN = 0
  · simp [h0]
  · have : Nat.log2 hN < nD + 1 := (Nat.log2_lt h0).2 (Nat.lt_of_le_of_lt h (Nat.pow_lt_pow_right (by omega) (by omega)))
    omega

theorem bang_eq_getD (W : Array Nat) (j : Nat) : W[j]! = W.getD j 0 := by
  simp only [getElem!_def, Array.getD_eq_getD_getElem?]
  cases W[j]? <;> rfl

/-- the Merkle skeleton of tree `j`, as in `treeCheck` / `verifyFix` -/
def specOf (X : ExecInst) (W : Array Nat) (half0 j : Nat) : TSpec :=
  if j < 4 then ragSpec W[j]! half0 else friSpec (2 ^ (X.nD - (j - 3)))

theorem specOf_half (X : ExecInst) (W : Array Nat) (half0 j : Nat) : SpecHalf (specOf X W half0 j) := by
  unfold specOf; split
  · exact ragSpec_half _ _
  · exact friSpec_half _

/-- the skeleton has at most `2^(nD + Wb)` leaves where `Wb` bounds the block width and `half0 = 2^(nD-1)` -/
theorem specOf_total_le (X : ExecInst) (W : Array Nat) (j Wm : Nat) (h1 : 1 ≤ X.nD) (hW : W[j]! ≤ Wm) :
    (specOf X W (2 ^ (X.nD - 1)) j).total ≤ 2 ^ (X.nD + Wm) := by
  unfold specOf; split
  · simp only [ragSpec]
    have h2 : W[j]! < 2 ^ W[j]! := Nat.lt_two_pow_self
    have h3 : 2 ^ W[j]! ≤ 2 ^ Wm := Nat.pow_le_pow_right (by omega) hW
    have h4 : 2 ^ (X.nD - 1) * 2 = 2 ^ X.nD := by
      rw [← Nat.pow_succ]; congr 1; omega
    calc 2 ^ (X.nD - 1) * 2 * W[j]! = 2 ^ X.nD * W[j]! := by rw [h4]
      _ ≤ 2 ^ X.nD * 2 ^ Wm := Nat.mul_le_mul_left _ (by omega)
      _ = 2 ^ (X.nD + Wm) := by rw [Nat.pow_add]
  · simp only [friSpec]
    exact Nat.pow_le_pow_right (by omega) (by omega)

/-- **the Merkle recursion of any tree**: at most `1 + |sel| · (nD + Wm + 1)` calls -/
theorem tree_calls_le (X : ExecInst) (H : HFn) (W : Array Nat) (j Wm : Nat) (sel : Array Nat) (leaf : Nat → Dg5) (sibs : Array Dg5)
    (h1 : 1 ≤ X.nD) (hW : W[j]! ≤ Wm) (hl : LbWell sel) :
    let sp := specOf X W (2 ^ (X.nD - 1)) j
    (goRootT H sp j sel leaf sibs sp.total 1 0 sp.total 0).2 ≤ 1 + sel.size * (X.nD + Wm + 1) :=
  goRoot_calls_le H _ j sel leaf sibs (specOf_half X W _ j) hl (X.nD + Wm) (specOf_total_le X W j Wm h1 hW)

/-- **`verifyOnline_cost_of_lb`** (the cost theorem with `LbWell` as hypotheses; `verifyOnline_cost` below discharges them).  For a run of `verifyOnline` whose shape gates passed (`π.pos`, `πF.pos` of length `l`), with `hN ≤ 2^nD`
and `1 ≤ nD` (J-8: `hN = 2^(k+1)`, `nD = k+7`) and the selected-leaf arrays well-behaved for `lb` (`LbWell`, true for sorted arrays):
(1) every tree's selected-leaf array has at most `2(Wm+1)l` entries and its Merkle recursion at most `1 + 2(Wm+1)l(nD+Wm+1)` calls,
(2) the DEEP point list has `r+2`, the opening list at most `c(r+1)` and the side-proof opening list at most `F(r+1)` entries,
(3) `K3.pow ζ hN` takes at most `nD+1` squarings,
(4) the model `costModel` of the run is at most `6000 · S^6`, `S` the sum of the parameters (no `hN`).
All other loops of `verifyOnlineE`/`verifyFix` are `List.range` of a parameter or `π.pos`/`πF.pos`/`X.tabs`/... (see the report). -/
theorem verifyOnline_cost_of_lb (vk : VK) (H : HFn) (z : List Nat) (π : FlatProof) (πF : FixProof) (zeta cs : K3)
    (hpos : π.pos.size = vk.X.l) (hposF : πF.pos.size = vk.X.l) (h1 : 1 ≤ vk.X.nD) (hN : vk.X.hN ≤ 2 ^ vk.X.nD)
    (hlb : ∀ j, LbWell (treeSel vk.X ((blockLayout vk.X).1.getD j 0) j π.pos))
    (hlbF : ∀ j, LbWell (if j == 0 then treeSel vk.X vk.cols.size 0 πF.pos else if j < 4 then #[] else treeSel vk.X 0 j πF.pos)) :
    -- (1)
    (∀ j, (treeSel vk.X ((blockLayout vk.X).1.getD j 0) j π.pos).size ≤ 2 * ((Dims.ofRun vk z π πF).Wm + 1) * vk.X.l) ∧
    (∀ j, (if j == 0 then treeSel vk.X vk.cols.size 0 πF.pos else if j < 4 then #[] else treeSel vk.X 0 j πF.pos).size ≤
        2 * ((Dims.ofRun vk z π πF).Wm + 1) * vk.X.l) ∧
    (∀ (j : Nat) (leaf : Nat → Dg5) (sibs : Array Dg5),
      let W := (blockLayout vk.X).1
      let sp := specOf vk.X W (2 ^ (vk.X.nD - 1)) j
      (goRootT H sp j (treeSel vk.X (W.getD j 0) j π.pos) leaf sibs sp.total 1 0 sp.total 0).2 ≤
        1 + 2 * ((Dims.ofRun vk z π πF).Wm + 1) * vk.X.l * (vk.X.nD + (Dims.ofRun vk z π πF).Wm + 1)) ∧
    (∀ (j : Nat) (leaf : Nat → Dg5) (sibs : Array Dg5),
      let W : Array Nat := #[vk.cols.size, 0, 0, 0]
      let sp := specOf vk.X W (2 ^ (vk.X.nD - 1)) j
      (goRootT H sp j (if j == 0 then treeSel vk.X vk.cols.size 0 πF.pos else if j < 4 then #[] else treeSel vk.X 0 j πF.pos)
          leaf sibs sp.total 1 0 sp.total 0).2 ≤
        1 + 2 * ((Dims.ofRun vk z π πF).Wm + 1) * vk.X.l * (vk.X.nD + (Dims.ofRun vk z π πF).Wm + 1)) ∧
    -- (2)
    (openPts vk.X zeta).size = vk.X.r + 2 ∧
    (∀ vT vQ, (openingList vk.X cs vT vQ).size ≤ (vk.X.nc + vk.X.nq) * (vk.X.r + 1)) ∧
    (∀ vF, (fixOps vk.X vk.cols cs vF).size ≤ vk.cols.size * (vk.X.r + 1)) ∧
    -- (3)
    Nat.log2 vk.X.hN + 1 ≤ vk.X.nD + 1 ∧
    -- (4)
    costModel (Dims.ofRun vk z π πF) ≤ 6000 * (Dims.ofRun vk z π πF).S ^ 6 := by
  have hWm : ∀ j, (blockLayout vk.X).1.getD j 0 ≤ (Dims.ofRun vk z π πF).Wm := by
    intro j; have := blockLayout_le vk.X j; simp only [Dims.ofRun]; omega
  have hselF : ∀ j, (if j == 0 then treeSel vk.X vk.cols.size 0 πF.pos else if j < 4 then #[] else treeSel vk.X 0 j πF.pos).size ≤
        2 * ((Dims.ofRun vk z π πF).Wm + 1) * vk.X.l := by
    intro j
    have hF : vk.cols.size ≤ (Dims.ofRun vk z π πF).Wm := by simp only [Dims.ofRun]; omega
    split
    · have := treeSel_size_le vk.X vk.cols.size 0 πF.pos
      have h2 := Nat.mul_le_mul_right πF.pos.size (Nat.mul_le_mul_left 2 (Nat.succ_le_succ hF))
      rw [hposF] at this h2
      exact Nat.le_trans this h2
    · split
      · simp
      · have := treeSel_size_le vk.X 0 j πF.pos
        have h2 := Nat.mul_le_mul_right πF.pos.size (Nat.mul_le_mul_left 2 (Nat.succ_le_succ (Nat.zero_le (Dims.ofRun vk z π πF).Wm)))
        rw [hposF] at this h2
        exact Nat.le_trans this h2
  refine ⟨?_, hselF, ?_, ?_, openPts_size _ _, fun vT vQ => openingList_size_le _ _ _ _, fun vF => fixOps_size_le _ _ _ _,
    bits_hN_le _ _ hN, costModel_le _⟩
  · intro j
    have := treeSel_size_le vk.X ((blockLayout vk.X).1.getD j 0) j π.pos
    have h2 := Nat.mul_le_mul_right π.pos.size (Nat.mul_le_mul_left 2 (Nat.succ_le_succ (hWm j)))
    rw [hpos] at this h2
    exact Nat.le_trans this (by rw [Nat.mul_comm] at h2 ⊢; omega)
  · intro j leaf sibs W sp
    have h := tree_calls_le vk.X H W j (Dims.ofRun vk z π πF).Wm (treeSel vk.X (W.getD j 0) j π.pos) leaf sibs h1
      (by rw [bang_eq_getD]; exact hWm j) (hlb j)
    refine Nat.le_trans h ?_
    have hs : (treeSel vk.X (W.getD j 0) j π.pos).size ≤ 2 * ((Dims.ofRun vk z π πF).Wm + 1) * vk.X.l := by
      have := treeSel_size_le vk.X (W.getD j 0) j π.pos
      have h2 := Nat.mul_le_mul_right π.pos.size (Nat.mul_le_mul_left 2 (Nat.succ_le_succ (hWm j)))
      rw [hpos] at this h2
      exact Nat.le_trans this h2
    have := Nat.mul_le_mul_right (vk.X.nD + (Dims.ofRun vk z π πF).Wm + 1) hs
    omega
  · intro j leaf sibs W sp
    have hF : vk.cols.size ≤ (Dims.ofRun vk z π πF).Wm := by simp only [Dims.ofRun]; omega
    have h := tree_calls_le vk.X H W j (Dims.ofRun vk z π πF).Wm _ leaf sibs h1
      (by
        match j with
        | 0 => simpa [W] using hF
        | 1 | 2 | 3 => simp [W]
        | j + 4 => simp [W, getElem!_def]) (hlbF j)
    refine Nat.le_trans h ?_
    have := Nat.mul_le_mul_right (vk.X.nD + (Dims.ofRun vk z π πF).Wm + 1) (hselF j)
    omega


/-- sorted (non-decreasing) array -/
def SortedArr (a : Array Nat) : Prop := ∀ i j, i < j → j < a.size → a[i]! ≤ a[j]!

/-- `lb` of a sorted array is the number of entries `< x` -/
theorem lbGo_spec (a : Array Nat) (x : Nat) (hs : SortedArr a) :
    ∀ (f lo hi : Nat), lo ≤ hi → hi ≤ a.size → hi - lo ≤ f → (∀ i, i < lo → a[i]! < x) →
      (∀ i, hi ≤ i → i < a.size → x ≤ a[i]!) →
      lbGo a x f lo hi ≤ a.size ∧ (∀ i, i < lbGo a x f lo hi → a[i]! < x) ∧
        (∀ i, lbGo a x f lo hi ≤ i → i < a.size → x ≤ a[i]!) := by
  intro f
  induction f with
  | zero =>
    intro lo hi h1 h2 h3 h4 h5
    have : lo = hi := by omega
    subst this
    simp only [lbGo]; exact ⟨h2, h4, h5⟩
  | succ f ih =>
    intro lo hi h1 h2 h3 h4 h5
    simp only [lbGo]
    by_cases hlt : lo < hi
    · simp only [hlt, ite_true]
      have hmid1 : lo ≤ (lo + hi) / 2 := by omega
      have hmid2 : (lo + hi) / 2 < hi := by omega
      by_cases hm : a[(lo + hi) / 2]! < x
      · simp only [hm, ite_true]
        refine ih ((lo + hi) / 2 + 1) hi (by omega) h2 (by omega) ?_ h5
        intro i hi'
        by_cases hil : i < lo
        · exact h4 i hil
        · rcases Nat.eq_or_lt_of_le (show i ≤ (lo + hi) / 2 by omega) with h | h
          · subst h; exact hm
          · exact Nat.lt_of_le_of_lt (hs i _ h (by omega)) hm
      · simp only [hm, ite_false]
        refine ih lo ((lo + hi) / 2) hmid1 (by omega) (by omega) h4 ?_
        intro i hi' hsz
        by_cases hih : hi ≤ i
        · exact h5 i hih hsz
        · rcases Nat.eq_or_lt_of_le hi' with h | h
          · subst h; omega
          · exact Nat.le_trans (Nat.le_of_not_lt hm) (hs _ i h hsz)
    · simp only [hlt, ite_false]
      have : lo = hi := by omega
      subst this
      exact ⟨h2, h4, h5⟩

theorem lbWell_of_sorted (a : Array Nat) (hs : SortedArr a) : LbWell a := by
  have spec : ∀ x, lb a x ≤ a.size ∧ (∀ i, i < lb a x → a[i]! < x) ∧ (∀ i, lb a x ≤ i → i < a.size → x ≤ a[i]!) :=
    fun x => lbGo_spec a x hs (a.size + 1) 0 a.size (by omega) (Nat.le_refl _) (by omega) (by intros; omega)
      (by intro i h1 h2; omega)
  refine ⟨?_, fun x => (spec x).1⟩
  intro x y hxy
  by_contra hcon
  have hlt : lb a y < lb a x := by omega
  have h1 := (spec x).2.1 (lb a y) hlt
  have h2 := (spec y).2.2 (lb a y) (Nat.le_refl _) (Nat.lt_of_lt_of_le hlt (spec x).1)
  omega

/-- a non-empty instance of `LbWell` (the vacuity witness): `#[2, 5, 7]` -/
example : LbWell #[2, 5, 7] := lbWell_of_sorted _ (by
  intro i j hij hj
  simp only [Array.size] at hj
  have : j < 3 := hj
  have : i < 3 := by omega
  interval_cases i <;> interval_cases j <;> simp_all <;> decide)

/-- `LbWell` is satisfiable: the empty selection (a non-empty instance is `lbWell_of_sorted` below, if present) -/
theorem lbWell_empty : LbWell (#[] : Array Nat) := by
  refine ⟨?_, ?_⟩ <;> intros <;> simp [lb, lbGo]


/-! ### E. `treeSel` is sorted, so `LbWell` holds for every tree of `verifyOnline` (discharges `hlb`, `hlbF`) -/

theorem pairwise_to_sorted (a : Array Nat) (h : List.Pairwise (· < ·) a.toList) : SortedArr a := by
  intro i j hij hj
  rw [List.pairwise_iff_getElem] at h
  have hi : i < a.toList.length := by simp; omega
  have hj' : j < a.toList.length := by simpa using hj
  have := h i j hi hj' hij
  have e1 : a[i]! = a.toList[i] := by rw [← Array.getElem!_toList, getElem!_pos a.toList i hi]
  have e2 : a[j]! = a.toList[j] := by rw [← Array.getElem!_toList, getElem!_pos a.toList j hj']
  rw [e1, e2]; exact Nat.le_of_lt this

theorem mem_insertD (x : Nat) : ∀ (l : List Nat) (b : Nat), b ∈ insertD x l → b = x ∨ b ∈ l
  | [], b, h => by simp [insertD] at h; exact Or.inl h
  | y :: ys, b, h => by
    simp only [insertD] at h
    split at h
    · simp at h; rcases h with h | h | h <;> simp [h]
    · split at h
      · simp at h; simp [h]
      · simp at h
        rcases h with h | h
        · simp [h]
        · rcases mem_insertD x ys b h with h | h <;> simp [h]

theorem insertD_pairwise (x : Nat) : ∀ l : List Nat, List.Pairwise (· < ·) l → List.Pairwise (· < ·) (insertD x l)
  | [], _ => by simp [insertD]
  | y :: ys, h => by
    simp only [List.pairwise_cons] at h
    obtain ⟨h1, h2⟩ := h
    simp only [insertD]
    split
    · rename_i hxy
      simp only [List.pairwise_cons, List.mem_cons]
      refine ⟨?_, h1, h2⟩
      intro b hb; rcases hb with rfl | hb
      · exact hxy
      · exact Nat.lt_trans hxy (h1 b hb)
    · split
      · rename_i hne hxy
        simp only [List.pairwise_cons]; exact ⟨h1, h2⟩
      · rename_i hne hxy
        have hyx : y < x := by
          have : ¬ x = y := by simpa using hxy
          omega
        simp only [List.pairwise_cons]
        refine ⟨?_, insertD_pairwise x ys h2⟩
        intro b hb
        rcases mem_insertD x ys b hb with rfl | hb
        · exact hyx
        · exact h1 b hb

theorem sortedDistinct_pairwise (a : Array Nat) : List.Pairwise (· < ·) (sortedDistinct a).toList := by
  have key : ∀ (xs acc : List Nat), List.Pairwise (· < ·) acc →
      List.Pairwise (· < ·) (xs.foldl (fun acc x => insertD x acc) acc) := by
    intro xs
    induction xs with
    | nil => intro acc h; simpa using h
    | cons x xs ih => intro acc h; exact ih _ (insertD_pairwise x acc h)
  simpa [sortedDistinct] using key a.toList [] (by simp)

theorem treeSel_sorted (X : ExecInst) (Wb j : Nat) (pos : Array Nat) : SortedArr (treeSel X Wb j pos) := by
  apply pairwise_to_sorted
  unfold treeSel
  split
  · split
    · simp
    · rw [Array.toList_flatMap, List.pairwise_flatMap]
      have hp := sortedDistinct_pairwise (pos.map (· % 2 ^ (X.nD - 1)))
      refine ⟨?_, ?_⟩
      · intro g _
        simp only [Array.toList_map, Array.toList_range]
        rw [List.pairwise_map]
        refine List.Pairwise.imp (fun {a b} hab => ?_) (List.pairwise_lt_range (n := 2 * Wb))
        omega
      · refine List.Pairwise.imp_of_mem (fun {g g'} hg hg' hlt => ?_) hp
        intro x hx y hy
        simp only [Array.toList_map, Array.toList_range, List.mem_map, List.mem_range] at hx hy
        obtain ⟨u, hu, rfl⟩ := hx
        obtain ⟨v, hv, rfl⟩ := hy
        have : (g + 1) * (2 * Wb) ≤ g' * (2 * Wb) := Nat.mul_le_mul_right _ hlt
        have e : g * 2 * Wb = g * (2 * Wb) := by rw [Nat.mul_assoc]
        have e' : g' * 2 * Wb = g' * (2 * Wb) := by rw [Nat.mul_assoc]
        rw [e, e']
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
  · rw [Array.toList_flatMap, List.pairwise_flatMap]
    have hp := sortedDistinct_pairwise (pos.map (· % 2 ^ (X.nD - (j - 3) - 1)))
    refine ⟨?_, ?_⟩
    · intro g _; simp
    · refine List.Pairwise.imp_of_mem (fun {g g'} hg hg' hlt => ?_) hp
      intro x hx y hy
      simp at hx hy
      omega

/-- `LbWell` for every tree of the main proof and of the side proof -/
theorem hlb_main (X : ExecInst) (pos : Array Nat) (W : Array Nat) (j : Nat) : LbWell (treeSel X (W.getD j 0) j pos) :=
  lbWell_of_sorted _ (treeSel_sorted _ _ _ _)

theorem hlb_side (X : ExecInst) (F : Nat) (pos : Array Nat) (j : Nat) :
    LbWell (if j == 0 then treeSel X F 0 pos else if j < 4 then #[] else treeSel X 0 j pos) := by
  split
  · exact lbWell_of_sorted _ (treeSel_sorted _ _ _ _)
  · split
    · exact lbWell_empty
    · exact lbWell_of_sorted _ (treeSel_sorted _ _ _ _)

/-- **`verifyOnline_cost`** (headline).  For every verifier key, statement, proof and side proof whose position arrays have the gated length `l`
(the shape gates of `verifyOnlineE`/`verifyFix`), with `hN ≤ 2^nD` and `1 ≤ nD` (J-8: `hN = 2^(k+1)`, `nD = k+7`):
(1) every tree's selected-leaf array has at most `2(Wm+1)l` entries and its Merkle recursion (`goRootT`, the ticked copy of `goRoot`, equal to it by
`goRootT_fst`) at most `1 + 2(Wm+1)l(nD+Wm+1)` calls, in the main proof and in the side proof; (2) the DEEP point / opening / fixed-opening lists have
`r+2`, `≤ c(r+1)`, `≤ F(r+1)` entries; (3) `K3.pow ζ hN` takes `≤ nD+1` squarings; (4) `costModel` of the run is `≤ 6000·S^6` with `S` the sum of the
parameters of `Dims` (no `hN`; `hb := nD+1`).  `costModel` is a MODEL (see the file header), not a step semantics. -/
theorem verifyOnline_cost (vk : VK) (H : HFn) (z : List Nat) (π : FlatProof) (πF : FixProof) (zeta cs : K3)
    (hpos : π.pos.size = vk.X.l) (hposF : πF.pos.size = vk.X.l) (h1 : 1 ≤ vk.X.nD) (hN : vk.X.hN ≤ 2 ^ vk.X.nD) :
    (∀ j, (treeSel vk.X ((blockLayout vk.X).1.getD j 0) j π.pos).size ≤ 2 * ((Dims.ofRun vk z π πF).Wm + 1) * vk.X.l) ∧
    (∀ j, (if j == 0 then treeSel vk.X vk.cols.size 0 πF.pos else if j < 4 then #[] else treeSel vk.X 0 j πF.pos).size ≤
        2 * ((Dims.ofRun vk z π πF).Wm + 1) * vk.X.l) ∧
    (∀ (j : Nat) (leaf : Nat → Dg5) (sibs : Array Dg5),
      let W := (blockLayout vk.X).1
      let sp := specOf vk.X W (2 ^ (vk.X.nD - 1)) j
      (goRootT H sp j (treeSel vk.X (W.getD j 0) j π.pos) leaf sibs sp.total 1 0 sp.total 0).2 ≤
        1 + 2 * ((Dims.ofRun vk z π πF).Wm + 1) * vk.X.l * (vk.X.nD + (Dims.ofRun vk z π πF).Wm + 1)) ∧
    (∀ (j : Nat) (leaf : Nat → Dg5) (sibs : Array Dg5),
      let W : Array Nat := #[vk.cols.size, 0, 0, 0]
      let sp := specOf vk.X W (2 ^ (vk.X.nD - 1)) j
      (goRootT H sp j (if j == 0 then treeSel vk.X vk.cols.size 0 πF.pos else if j < 4 then #[] else treeSel vk.X 0 j πF.pos)
          leaf sibs sp.total 1 0 sp.total 0).2 ≤
        1 + 2 * ((Dims.ofRun vk z π πF).Wm + 1) * vk.X.l * (vk.X.nD + (Dims.ofRun vk z π πF).Wm + 1)) ∧
    (openPts vk.X zeta).size = vk.X.r + 2 ∧
    (∀ vT vQ, (openingList vk.X cs vT vQ).size ≤ (vk.X.nc + vk.X.nq) * (vk.X.r + 1)) ∧
    (∀ vF, (fixOps vk.X vk.cols cs vF).size ≤ vk.cols.size * (vk.X.r + 1)) ∧
    Nat.log2 vk.X.hN + 1 ≤ vk.X.nD + 1 ∧
    costModel (Dims.ofRun vk z π πF) ≤ 6000 * (Dims.ofRun vk z π πF).S ^ 6 :=
  verifyOnline_cost_of_lb vk H z π πF zeta cs hpos hposF h1 hN
    (fun j => hlb_main vk.X π.pos _ j) (fun j => hlb_side vk.X vk.cols.size πF.pos j)


/-! #### `powAux` (square-and-multiply): ticked copies, equal results, `log2 e + 2` iterations -/

/-- iteration count of `powAux` (same control flow) -/
def powCnt : Nat → Nat → Nat
  | 0, _ => 1
  | f + 1, k => if k == 0 then 1 else 1 + powCnt f (k / 2)

def K3.powAuxT : Nat → K3 → Nat → K3 → K3 × Nat
  | 0, _, _, r => (r, 1)
  | f + 1, b, k, r =>
    if k == 0 then (r, 1)
    else let p := K3.powAuxT f (K3.mul b b) (k / 2) (if k % 2 == 1 then K3.mul r b else r); (p.1, p.2 + 1)

theorem K3_powAuxT_spec : ∀ (f : Nat) (b : K3) (k : Nat) (r : K3),
    (K3.powAuxT f b k r).1 = K3.powAux f b k r ∧ (K3.powAuxT f b k r).2 = powCnt f k := by
  intro f
  induction f with
  | zero => intro b k r; simp [K3.powAuxT, K3.powAux, powCnt]
  | succ f ih =>
    intro b k r
    by_cases hk : k == 0
    · simp [K3.powAuxT, K3.powAux, powCnt, hk]
    · have := ih (K3.mul b b) (k / 2) (if k % 2 == 1 then K3.mul r b else r)
      simp only [K3.powAuxT, K3.powAux, powCnt, hk, ite_false, Bool.false_eq_true]
      exact ⟨this.1, by rw [this.2]; omega⟩

def VF.powAuxT : Nat → G → Nat → G → G × Nat
  | 0, _, _, r => (r, 1)
  | f + 1, b, k, r =>
    if k == 0 then (r, 1)
    else let p := VF.powAuxT f (VF.mul b b) (k / 2) (if k % 2 == 1 then VF.mul r b else r); (p.1, p.2 + 1)

theorem VF_powAuxT_spec : ∀ (f : Nat) (b : G) (k : Nat) (r : G),
    (VF.powAuxT f b k r).1 = VF.powAux f b k r ∧ (VF.powAuxT f b k r).2 = powCnt f k := by
  intro f
  induction f with
  | zero => intro b k r; simp [VF.powAuxT, VF.powAux, powCnt]
  | succ f ih =>
    intro b k r
    by_cases hk : k == 0
    · simp [VF.powAuxT, VF.powAux, powCnt, hk]
    · have := ih (VF.mul b b) (k / 2) (if k % 2 == 1 then VF.mul r b else r)
      simp only [VF.powAuxT, VF.powAux, powCnt, hk, ite_false, Bool.false_eq_true]
      exact ⟨this.1, by rw [this.2]; omega⟩

/-- with fuel `e + 1` (as in `pow`): at most `log2 e + 2` iterations, i.e. the bit length of the exponent -/
theorem powCnt_le : ∀ (f k : Nat), k + 1 ≤ f + 1 → powCnt (f) k ≤ Nat.log2 k + 2 := by
  intro f
  induction f with
  | zero => intro k _; cases k <;> simp [powCnt]
  | succ f ih =>
    intro k hk
    by_cases h0 : k = 0
    · subst h0; simp [powCnt]
    · by_cases h1 : k = 1
      · subst h1
        have : powCnt f 0 = 1 := by cases f <;> simp [powCnt]
        simp [powCnt, this, Nat.log2]
      · have hk2 : 2 ≤ k := by omega
        have := ih (k / 2) (by omega)
        have hl : Nat.log2 k = Nat.log2 (k / 2) + 1 := by
          rw [Nat.log2_def]; simp [show 1 ≤ k from by omega, show 2 ≤ k from hk2]
        simp only [powCnt, h0, beq_iff_eq, ite_false]
        omega

theorem pow_iters (e : Nat) : powCnt (e + 1) e ≤ Nat.log2 e + 2 := powCnt_le (e + 1) e (by omega)

/-! ### F. loop-pinned ports: every loop of `verifyOnlineE` / `verifyFix` and of the helpers they call, tagged, with `rfl` equalities.

`lp id xs` / `lpA id a` are identities that tag the list / array a loop iterates over.  Each primed function is a textual copy of the
original with its loop lists tagged, and `f' = f := rfl` (kernel) pins that the tagged lists ARE the lists the real function iterates over.
Structural recursions (`friSteps`, `insertD`, `lbGo`, `goRootF`, `powAux`) are treated as
loops over their list/fuel argument; `goRootF` and `powAux` get ticked copies like in §A. -/

@[inline] def lp {α : Type} (_id : Nat) (xs : List α) : List α := xs
@[inline] def lpA {α : Type} (_id : Nat) (a : Array α) : Array α := a

def deepMsg' (vT : Array (Array K3)) (vQ : Array K3) : List Nat :=
  (lp 10 vT.toList).flatMap (fun a => (lp 11 a.toList).flatMap K3.limbs) ++ (lp 12 vQ.toList).flatMap K3.limbs
theorem deepMsg_eq : deepMsg = deepMsg' := rfl

def k3s' (l : List Nat) (n : Nat) : Array K3 := (lpA 13 (Array.range n)).map fun i => K3.ofLimbs (l.drop (3 * i))
theorem k3s_eq : k3s = k3s' := rfl

def blockLayout' (X : ExecInst) : Array Nat × Array Nat :=
  (lp 14 (List.range (X.nc + X.nq))).foldl
    (fun (st : Array Nat × Array Nat) c =>
      let b := X.blockOf[c]!
      if b < 4 then (st.1.modify b (· + 1), st.2.set! c st.1[b]!) else st)
    (Array.replicate 4 0, Array.replicate (X.nc + X.nq) 0)
theorem blockLayout_eqC : blockLayout = blockLayout' := rfl

def treeSel' (X : ExecInst) (Wb j : Nat) (pos : Array Nat) : Array Nat :=
  if j < 4 then
    (if Wb == 0 then #[] else
      (lpA 16 (sortedDistinct (lpA 15 pos |>.map (· % 2 ^ (X.nD - 1))))).flatMap fun g => (lpA 17 (Array.range (2 * Wb))).map (g * 2 * Wb + ·))
  else
    let halfw := 2 ^ (X.nD - (j - 3) - 1)
    (lpA 16 (sortedDistinct (lpA 15 pos |>.map (· % halfw)))).flatMap fun g => #[2 * g, 2 * g + 1]
theorem treeSel_eq : treeSel = treeSel' := rfl

def sortedDistinct' (a : Array Nat) : Array Nat := ((lp 18 a.toList).foldl (fun acc x => insertD x acc) []).toArray
theorem sortedDistinct_eq : sortedDistinct = sortedDistinct' := rfl

def openPts' (X : ExecInst) (zeta : K3) : Array K3 :=
  let st := (lp 20 (List.range X.r)).foldl
    (fun (st : Array K3 × K3) _ => (st.1.push (K3.mul zeta st.2), K3.smul X.hGen st.2)) (#[], K3.one)
  (st.1.push X.ppt).push zeta
theorem openPts_eqC : openPts = openPts' := rfl

def openingList' (X : ExecInst) (cs : K3) (vT : Array (Array K3)) (vQ : Array K3) : Array (Nat × Nat × K3 × K3) :=
  ((lp 21 (List.range (X.nc + X.nq))).foldl
    (fun (st : Array (Nat × Nat × K3 × K3) × K3) c =>
      match kindG X c with
      | 0 | 1 => (lp 22 (List.range X.r)).foldl
          (fun (st : Array (Nat × Nat × K3 × K3) × K3) o => (st.1.push (c, o, st.2, vT[c]![o]!), K3.mul st.2 cs)) st
      | 2 => (lp 22 (List.range X.r)).foldl
          (fun (st : Array (Nat × Nat × K3 × K3) × K3) _ => (st.1.push (c, X.r, st.2, vT[c]![0]!), K3.mul st.2 cs)) st
      | 3 => (st.1.push (c, X.r + 1, st.2, vQ[c - X.nc]!), K3.mul st.2 cs)
      | _ => st)
    (#[], K3.one)).1
theorem openingList_eq : openingList = openingList' := rfl

def deepWord' (X : ExecInst) (pts : Array K3) (ops : Array (Nat × Nat × K3 × K3)) (baseAt : Nat → Nat → G) (idx : Nat) : K3 :=
  let y := VF.mul X.dShift (VF.pow X.dGen idx)
  let accs := (lp 23 ops.toList).foldl
    (fun (accs : Array K3) (o : Nat × Nat × K3 × K3) =>
      accs.modify o.2.1 fun a => K3.add a (K3.mul o.2.2.1 (K3.sub (K3.ofG (baseAt o.1 idx)) o.2.2.2)))
    (Array.replicate (X.r + 2) K3.zero)
  (lp 24 (List.range (X.r + 2))).foldl
    (fun tot p => K3.add tot (K3.mul accs[p]! (K3.inv (K3.sub (K3.ofG y) pts[p]!)))) K3.zero
theorem deepWord_eqC : deepWord = deepWord' := rfl

def evalDag' (ch : Tr.Chip) (env : DEnv) : Array K3 :=
  let memo := (lp 26 ch.shared.toList).foldl (fun (memo : Array K3) s => memo.push (evK env memo s)) (Array.mkEmpty ch.shared.size)
  (lpA 27 ch.cons).map fun c => evK env memo c.e
theorem evalDag_eq : evalDag = evalDag' := rfl

def fixLayout' (X : ExecInst) (cols : Array FixCol) : FixLay :=
  (lp 28 (List.range cols.size)).foldl (fun (st : FixLay) j =>
    match cols[j]! with
    | .pre c => { st with pre := st.pre.set! c j }
    | .zh => { st with zh := j }
    | .zout t => { st with zout := st.zout.set! t j })
    { pre := Array.replicate X.nc 0, zh := 0, zout := Array.replicate X.tabs.size 0 }
theorem fixLayout_eq : fixLayout = fixLayout' := rfl

def fixOps' (X : ExecInst) (cols : Array FixCol) (cs : K3) (vF : Array (Array K3)) : Array (Nat × Nat × K3 × K3) :=
  ((lp 29 (List.range cols.size)).foldl
    (fun (st : Array (Nat × Nat × K3 × K3) × K3) j =>
      (lp 30 (List.range (fixLen X cols[j]!))).foldl
        (fun (st : Array (Nat × Nat × K3 × K3) × K3) o => (st.1.push (j, o, st.2, vF[j]![o]!), K3.mul st.2 cs)) st)
    (#[], K3.one)).1
theorem fixOps_eq : fixOps = fixOps' := rfl

def allCanonOnline' (z : List Nat) (π : FlatProof) : Bool :=
  (lp 40 z).all based && (lpA 41 π.roots).all (fun l => dgOk l) && (lpA 42 π.vT).all (fun a => (lpA 43 a).all k3Ok) &&
  (lpA 44 π.vQ).all k3Ok && (lpA 45 π.pfinal).all k3Ok &&
  (lpA 46 π.vals).all (fun a => (lpA 47 a).all based) && (lpA 48 π.sibs).all (fun a => (lpA 49 a).all dgOk)
theorem allCanonOnline_eq : allCanonOnline = allCanonOnline' := rfl

def chalsOnline (X : ExecInst) (FS : FSFn) (z : List Nat) (msgs : Array (List Nat)) : Array (List Nat) :=
  (lpA 4 (Array.range msgs.size)).map fun i => if roundNl X i == 0 then [] else FS (z :: (msgs.extract 0 (i + 1)).toList) (roundNl X i)
def chalsFix (X : ExecInst) (FSf : FSFn) (z : List Nat) (msgs : Array (List Nat)) : Array (List Nat) :=
  (lpA 72 (Array.range msgs.size)).map fun i =>
    if fixNl X.k X.l i == 0 then [] else FSf (z :: (msgs.extract 0 (i + 1)).toList) (fixNl X.k X.l i)

def verifyFixT (vk : VK) (H : HFn) (FSf : FSFn) (z ctx : List Nat) (zeta : K3) (πF : FixProof) : Except String Unit :=
  let X := vk.X
  let k := X.k
  let F := vk.cols.size
  let Hf := hFix H
  ckE (πF.vF.size == F && (lp 60 (List.range F)).all (fun j => πF.vF[j]!.size == fixLen X vk.cols[j]!) &&
       πF.pfinal.size == X.d && πF.pos.size == X.l && πF.roots.size == k &&
       πF.vals.size == 1 + k && πF.sibs.size == 1 + k) "fix: proof shape" >>= fun _ =>
  ckE ((lpA 61 πF.vF).all (fun a => (lpA 62 a).all k3Ok) && (lpA 63 πF.pfinal).all k3Ok && (lpA 64 πF.roots).all dgOk &&
       (lpA 65 πF.vals).all (fun a => (lpA 66 a).all based) && (lpA 67 πF.sibs).all (fun a => (lpA 68 a).all dgOk) &&
       (lp 69 z).all based && (lp 70 ctx).all based) "fix: non-canonical limb" >>= fun _ =>
  ckE ((lpA 71 πF.pos).all (· < 2 ^ X.nD)) "fix: position range" >>= fun _ =>
  let msgs := fixMsgs k ctx πF.vF πF.roots πF.pfinal
  let chals : Array (List Nat) := chalsFix X FSf z msgs
  ckE ((lpA 73 chals).all (fun a => (lp 74 a).all based)) "fix: non-canonical Fiat-Shamir challenge limb" >>= fun _ =>
  let cs := K3.ofLimbs chals[1]!
  let alphas : Array K3 := (lpA 75 (Array.range (k + 1))).map fun w => K3.ofLimbs chals[2 + w]!
  let xs : Array Nat := (lpA 76 chals[3 + k]!.toArray).map (· % 2 ^ X.nD)
  ckE (πF.pos == xs) "fix: positions differ from the FS query challenge" >>= fun _ =>
  let half0 := 2 ^ (X.nD - 1)
  let sels : Array (Array Nat) := (lpA 77 (Array.range (4 + k))).map fun j =>
    if j == 0 then treeSel' X F 0 πF.pos else if j < 4 then #[] else treeSel' X 0 j πF.pos
  let z5 : Dg5 := [0, 0, 0, 0, 0]
  let πa : FlatProof :=
    { roots := #[vk.root, z5, z5, z5] ++ πF.roots, vT := #[], vQ := #[], pfinal := πF.pfinal, pos := πF.pos,
      vals := #[πF.vals[0]!, #[], #[], #[]] ++ πF.vals.extract 1 (1 + k),
      sibs := #[πF.sibs[0]!, #[], #[], #[]] ++ πF.sibs.extract 1 (1 + k) }
  (lp 78 (List.range (4 + k))).forM (treeCheck X Hf πa #[F, 0, 0, 0] half0 sels) >>= fun _ =>
  let pts := openPts' X zeta
  let dN := 2 ^ X.nD
  (lp 79 (List.range X.r)).forM (fun o => ckE (pts[o]!.pow dN != K3.ofG (VF.pow X.dShift dN)) "fix: OffDom fails") >>= fun _ =>
  let ops := fixOps' X vk.cols cs πF.vF
  let baseAt (c idx : Nat) : G :=
    UInt64.ofNat πa.vals[0]![lb sels[0]! ((idx % half0) * 2 * F + (idx / half0) * F + c)]!
  let word0 := deepWord' X pts ops baseAt
  (lp 80 πF.pos.toList).forM (fun q =>
    let g0 := q % half0
    friSteps X πa.vals sels alphas q (lp 81 (List.range' 1 k))
      (foldK3 (word0 g0) (word0 (g0 + half0)) (yAt X 0 g0) alphas[0]!) g0 >>= fun r =>
    ckE (r.1 == K3.horner πF.pfinal (K3.ofG (yAt X (k + 1) r.2))) s!"fix: FRI final polynomial mismatch, query {q}")
theorem verifyFix_eq : verifyFix = verifyFixT := rfl

def verifyOnlineET (vk : VK) (H : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) : Except String Unit :=
  let X := vk.X
  let nB := 4
  let k := X.k
  let ncq := X.nc + X.nq
  let lay := fixLayout' X vk.cols
  ckE (allCanonOnline' z π) "non-canonical limb (>= p)" >>= fun _ =>
  ckE (π.roots.size == nB + k && π.vals.size == nB + k && π.sibs.size == nB + k) "tree count" >>= fun _ =>
  ckE (π.vT.size == X.nc && π.vQ.size == X.nq && π.pfinal.size == X.d && π.pos.size == X.l) "proof shape" >>= fun _ =>
  (lp 1 (List.range X.nc)).forM (fun c =>
    ckE (π.vT[c]!.size == vTLen X c) "vT shape") >>= fun _ =>
  ckE ((lpA 2 π.pos).all (· < 2 ^ X.nD)) "position range" >>= fun _ =>
  let pfEnc := (lp 3 π.pfinal.toList).flatMap K3.limbs
  let msgs : Array (List Nat) :=
    #[[], π.roots[0]!, π.roots[1]!, π.roots[2]!, π.roots[3]!, deepMsg' π.vT π.vQ, [], []] ++ π.roots.extract nB (nB + k) ++ #[pfEnc]
  let nlOf := roundNl X
  let chals : Array (List Nat) := chalsOnline X FS z msgs
  ckE ((lpA 5 chals).all (fun a => (lp 6 a).all based)) "non-canonical Fiat-Shamir challenge limb" >>= fun _ =>
  let coins0 := k3s' chals[1]! X.nCoins[0]!
  let coins1 := k3s' chals[2]! X.nCoins[1]!
  let alpha := K3.ofLimbs chals[3]!
  let zeta := K3.ofLimbs chals[4]!
  let cs := K3.ofLimbs chals[6]!
  let alphas : Array K3 := (lpA 7 (Array.range (k + 1))).map fun w => K3.ofLimbs chals[7 + w]!
  let xs : Array Nat := (lpA 8 chals[8 + k]!.toArray).map (· % 2 ^ X.nD)
  ckE (π.pos == xs) "positions differ from the FS query challenge" >>= fun _ =>
  verifyFixT vk H FSf z (fixCtx π zeta) zeta πF >>= fun _ =>
  let vF := πF.vF
  let half0 := 2 ^ (X.nD - 1)
  let (W, rank) := blockLayout' X
  let sels : Array (Array Nat) := (lpA 9 (Array.range (nB + k))).map fun j => treeSel' X (W.getD j 0) j π.pos
  (lp 90 (List.range (nB + k))).forM (treeCheck X H π W half0 sels) >>= fun _ =>
  let slots : Array K3 := (lp 91 X.derived.toList).foldl (fun (slots : Array K3) (be : Nat × Nat) => slots.push (K3.pow slots[be.1]! be.2)) (coins0 ++ coins1)
  let zh := vF[lay.zh]![0]!
  let curNxt := (lp 92 (List.range X.nc)).foldl
    (fun (st : Array K3 × Array K3) c =>
      match X.colKind[c]! with
      | 0 => (st.1.set! c π.vT[c]![0]!, st.2.set! c (if X.r ≥ 2 then π.vT[c]![1]! else K3.zero))
      | 1 => (st.1.set! c vF[lay.pre[c]!]![0]!, st.2.set! c vF[lay.pre[c]!]![1]!)
      | _ => st)
    (Array.replicate ncq K3.zero, Array.replicate ncq K3.zero)
  (lp 93 X.pubOf.toList).forM (fun c =>
    ckE (c < X.nc && X.colKind[c]! == 2) "pubOf" >>= fun _ =>
    ckE (π.vT[c]![0]!).isBase "public value not in the base field") >>= fun _ =>
  let pub : Array G := (lpA 94 X.pubOf).map fun c => (π.vT[c]![0]!).c0
  ckE (!zh.isZero) "zeta in H" >>= fun _ =>
  let lhs := ((lpA 95 X.tabs).foldl (fun (st : K3 × K3 × Nat) t =>
    let cur := curNxt.1.extract t.col0 (t.col0 + t.nc)
    let nxt := curNxt.2.extract t.col0 (t.col0 + t.nc)
    let cvals := evalDag' t.chip { cur := cur, next := nxt, pub := pub.extract t.pubBase (t.pubBase + t.npub), chal := slots,
                                   bc := t.chip.baseCols }
    let (s, pw) := (lpA 96 cvals).foldl (fun (a : K3 × K3) v => (K3.add a.1 (K3.mul a.2 v), K3.mul a.2 alpha)) (K3.zero, st.2.1)
    let mult := if t.hN < X.hN then vF[lay.zout[st.2.2]!]![0]! else K3.one
    (K3.add st.1 (K3.mul s mult), pw, st.2.2 + 1)) (K3.zero, K3.one, 0)).1
  let zN := K3.pow zeta X.hN
  let qsum := (lp 97 (List.range X.nq)).foldl
    (fun qs j => K3.add qs (K3.mul (K3.mul (K3.pow K3.gen (j % 3)) (K3.pow zN (j / 3))) π.vQ[j]!)) K3.zero
  ckE (lhs == K3.mul zh qsum) "DeepCheck fails" >>= fun _ =>
  let pts := openPts' X zeta
  let dN := 2 ^ X.nD
  (lp 98 pts.toList).forM (fun pt => ckE (pt.pow dN != K3.ofG (VF.pow X.dShift dN)) "OffDom fails") >>= fun _ =>
  ckE (X.pubCheck slots pub) "public relation fails" >>= fun _ =>
  (lp 99 (List.range X.nc)).forM (fun c =>
    ckE (X.colKind[c]! != 1 || (lp 100 (List.range X.r)).all (fun o => π.vT[c]![o]! == vF[lay.pre[c]!]![o]!)) "pre opening mismatch") >>= fun _ =>
  let ops := openingList' X cs π.vT π.vQ
  let baseAt (c idx : Nat) : G :=
    let b := X.blockOf[c]!
    let leafPos := (idx % half0) * 2 * W[b]! + (idx / half0) * W[b]! + rank[c]!
    UInt64.ofNat π.vals[b]![lb sels[b]! leafPos]!
  let word0 := deepWord' X pts ops baseAt
  (lp 101 π.pos.toList).forM (fun q =>
    let g0 := q % half0
    friSteps X π.vals sels alphas q (lp 102 (List.range' 1 k))
      (foldK3 (word0 g0) (word0 (g0 + half0)) (yAt X 0 g0) alphas[0]!) g0 >>= fun r =>
    ckE (r.1 == K3.horner π.pfinal (K3.ofG (yAt X (k + 1) r.2))) s!"FRI final polynomial mismatch, query {q}")

/-- **the real program is the tagged program** (kernel `rfl`): every loop list of `verifyOnlineE` is the tagged one in `verifyOnlineET` -/
theorem verifyOnlineE_eq : verifyOnlineE = verifyOnlineET := rfl
theorem verifyOnline_eq (vk : VK) (H : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) :
    verifyOnline vk H FS FSf z π πF = (match verifyOnlineET vk H FS FSf z π πF with | .ok _ => true | .error _ => false) := rfl

theorem sum_map_ge {α : Type} (g : α → Nat) (B : Nat) : ∀ xs : List α, (∀ x ∈ xs, B ≤ g x) → xs.length * B ≤ (xs.map g).sum
  | [], _ => by simp
  | x :: xs, h => by
    have h1 := h x (by simp)
    have h2 := sum_map_ge g B xs (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-! ### G. every loop of the pinned programs is bounded (`verifyOnline_loops_bounded`) -/

theorem le_sum_of_mem {α : Type} (g : α → Nat) : ∀ (xs : List α) (x : α), x ∈ xs → g x ≤ (xs.map g).sum
  | [], x, h => by simp at h
  | y :: ys, x, h => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := le_sum_of_mem g ys x h; omega


theorem arr2_le {α : Type} (xs : Array (Array α)) (T : Nat) (h : (xs.toList.map (·.size)).sum ≤ T) : ∀ a ∈ xs.toList, a.size ≤ T := by
  intro a ha; have := le_sum_of_mem (fun a : Array α => a.size) xs.toList a ha; omega

theorem limbs_le (a : Array (List Nat)) (T : Nat) (h : limbsOf a ≤ T) : ∀ l ∈ a.toList, l.length ≤ T := by
  intro l hl; have := le_sum_of_mem List.length a.toList l hl; unfold limbsOf at h; omega

theorem sibs_le (sibs : Array (Array (List Nat))) (T : Nat) (h : (sibs.toList.map (fun a => a.size + limbsOf a)).sum ≤ T) :
    (∀ a ∈ sibs.toList, a.size ≤ T) ∧ (∀ a ∈ sibs.toList, ∀ l ∈ a.toList, l.length ≤ T) := by
  have key : ∀ a ∈ sibs.toList, a.size + limbsOf a ≤ T := by
    intro a ha; have := le_sum_of_mem (fun a : Array (List Nat) => a.size + limbsOf a) sibs.toList a ha; omega
  exact ⟨fun a ha => by have := key a ha; omega, fun a ha l hl => by
    have := key a ha; have := limbs_le a T (by omega) l hl; omega⟩

theorem sum_take_le {α : Type} (g : α → Nat) : ∀ (xs : List α) (n : Nat), ((xs.take n).map g).sum ≤ (xs.map g).sum
  | [], n => by simp
  | x :: xs, 0 => by simp
  | x :: xs, n + 1 => by
    have := sum_take_le g xs n
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons]; omega

theorem exSize_pos (e : Tr.Ex) : 1 ≤ exSize e := by cases e <;> simp [exSize] <;> omega

theorem chip_len_le_dag (X : ExecInst) (t : TabInst) (ht : t ∈ X.tabs.toList) :
    t.chip.shared.size ≤ dagSize X ∧ t.chip.cons.size ≤ dagSize X := by
  have h := le_sum_of_mem (fun t : TabInst => 1 + t.nc + t.npub + (t.chip.shared.toList.map exSize).sum +
    (t.chip.cons.toList.map (fun c => exSize c.e)).sum) X.tabs.toList t ht
  have s1 : t.chip.shared.size ≤ (t.chip.shared.toList.map exSize).sum := by
    have := sum_map_ge exSize 1 t.chip.shared.toList (fun x _ => exSize_pos x); simpa using this
  have s2 : t.chip.cons.size ≤ (t.chip.cons.toList.map (fun c => exSize c.e)).sum := by
    have := sum_map_ge (fun c : Tr.Con => exSize c.e) 1 t.chip.cons.toList (fun x _ => exSize_pos x.e); simpa using this
  unfold dagSize
  omega

/-- the Fiat-Shamir oracles return what was asked for (`tip5FS` squeezes exactly `n` limbs) -/
def FSLen (FS : FSFn) : Prop := ∀ ctx n, (FS ctx n).length = n

theorem roundNl_le (X : ExecInst) (i : Nat) : roundNl X i ≤ 3 * (X.nCoins[0]! + X.nCoins[1]!) + X.l + 3 := by
  unfold roundNl; split <;> try omega
  all_goals split <;> try omega
  all_goals split <;> try omega
  all_goals split <;> try omega
  all_goals split <;> try omega
  all_goals split <;> omega

theorem fixNl_le (k l i : Nat) : fixNl k l i ≤ l + 3 := by
  unfold fixNl; split <;> try omega
  all_goals split <;> try omega
  all_goals split <;> omega

/-- element of a mapped `Array.range` (default `[]` out of range) -/
theorem range_map_getElem_len (n B : Nat) (f : Nat → List Nat) (hf : ∀ i, (f i).length ≤ B) (i : Nat) :
    ((Array.range n).map f)[i]!.length ≤ B := by
  by_cases h : i < n
  · rw [getElem!_pos _ i (by simpa using h)]; simp [hf]
  · have : ((Array.range n).map f)[i]? = none := by simp; omega
    have hd : (default : List Nat) = [] := rfl
    simp [getElem!_def, this, hd]

theorem K3_pow_T (x : K3) (e : Nat) : K3.pow x e = (K3.powAuxT (e + 1) x e K3.one).1 := ((K3_powAuxT_spec _ _ _ _).1).symm
theorem VF_pow_T (x : G) (e : Nat) : VF.pow x e = (VF.powAuxT (e + 1) x e 1).1 := ((VF_powAuxT_spec _ _ _ _).1).symm
theorem K3_pow_cnt (x : K3) (e : Nat) : (K3.powAuxT (e + 1) x e K3.one).2 ≤ Nat.log2 e + 2 := by
  rw [(K3_powAuxT_spec _ _ _ _).2]; exact pow_iters e
theorem VF_pow_cnt (x : G) (e : Nat) : (VF.powAuxT (e + 1) x e 1).2 ≤ Nat.log2 e + 2 := by
  rw [(VF_powAuxT_spec _ _ _ _).2]; exact pow_iters e

theorem log2_le_of_lt_pow {e nD : Nat} (h : e < 2 ^ nD) : Nat.log2 e ≤ nD := by
  by_cases h0 : e = 0
  · subst h0; simp
  · have := (Nat.log2_lt h0).2 h; omega

/-- the shape facts the gates of `verifyOnlineE` / `verifyFix` establish before the loops after them run -/
structure OnlineShape (vk : VK) (π : FlatProof) (πF : FixProof) : Prop where
  roots : π.roots.size = vk.X.k + 4
  vT : π.vT.size = vk.X.nc
  vQ : π.vQ.size = vk.X.nq
  pf : π.pfinal.size = vk.X.d
  pos : π.pos.size = vk.X.l
  fvF : πF.vF.size = vk.cols.size
  fpf : πF.pfinal.size = vk.X.d
  fpos : πF.pos.size = vk.X.l
  froots : πF.roots.size = vk.X.k
  hk : vk.X.k < vk.X.nD
  hN : vk.X.hN ≤ 2 ^ vk.X.nD

/-- **Every loop of `verifyOnlineET` (= `verifyOnlineE`, `verifyOnlineE_eq`) and `verifyFixT` (= `verifyFix`, `verifyFix_eq`) and of the helpers
they call ranges over a list of at most the stated length.**  Field `lNN` is the loop tagged `NN` in §F (table in the report).
`c = nc + nq`, `F = |vk.cols|`, `Z = zLen`, `P = proofSize π`, `PF = fixSize πF`. -/
structure LoopBounds (vk : VK) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) : Prop where
  -- verifyOnlineET: range loops
  l1_92_99 : (List.range vk.X.nc).length ≤ vk.X.nc + vk.X.nq
  l9_90 : (List.range (4 + vk.X.k)).length = 4 + vk.X.k
  l7 : (List.range (vk.X.k + 1)).length = vk.X.k + 1
  l91 : vk.X.derived.toList.length = vk.X.derived.size
  l93_94 : vk.X.pubOf.toList.length = vk.X.pubOf.size
  l95 : vk.X.tabs.size = vk.X.tabs.size
  l96_26_27 : ∀ t ∈ vk.X.tabs.toList, ∀ env, (evalDag' t.chip env).size ≤ dagSize vk.X ∧ t.chip.shared.toList.length ≤ dagSize vk.X ∧
      t.chip.cons.size ≤ dagSize vk.X
  l97 : (List.range vk.X.nq).length = vk.X.nq
  l98_20 : ∀ ζ, (openPts' vk.X ζ).toList.length = vk.X.r + 2
  l100_22 : (List.range vk.X.r).length = vk.X.r
  l24 : (List.range (vk.X.r + 2)).length = vk.X.r + 2
  l101_80_2_3 : π.pos.toList.length = vk.X.l ∧ πF.pos.toList.length = vk.X.l ∧ π.pfinal.toList.length = vk.X.d
  l102_81 : (List.range' 1 vk.X.k).length = vk.X.k
  l23 : ∀ cs vT vQ, (openingList' vk.X cs vT vQ).toList.length ≤ (vk.X.nc + vk.X.nq) * (vk.X.r + 1)
  l4 : ∀ (a b c d e f : List Nat), (#[[], a, b, c, d, e, [], []] ++ π.roots.extract 4 (4 + vk.X.k) ++ #[f] : Array (List Nat)).size = vk.X.k + 9
  l5_6_8 : FSLen FS → ∀ (ms : Array (List Nat)), (chalsOnline vk.X FS z ms).size = ms.size ∧
      ∀ i : Nat, List.length ((chalsOnline vk.X FS z ms)[i]!) ≤ 3 * (vk.X.nCoins[0]! + vk.X.nCoins[1]!) + vk.X.l + 3
  l13 : ∀ n, n ≤ vk.X.nCoins[0]! + vk.X.nCoins[1]! → (Array.range n).size ≤ vk.X.nCoins[0]! + vk.X.nCoins[1]!
  -- helpers
  l14_21_29_60_28 : (List.range (vk.X.nc + vk.X.nq)).length = vk.X.nc + vk.X.nq ∧ (List.range vk.cols.size).length = vk.cols.size
  l15_16_18_17 : ∀ (Wb j : Nat) (f : Nat → Nat), (∀ x, f x = x % 2 ^ (vk.X.nD - 1) ∨ f x = x % 2 ^ (vk.X.nD - (j - 3) - 1)) →
      π.pos.size = vk.X.l → (π.pos.map f).toList.length = vk.X.l ∧ (sortedDistinct (π.pos.map f)).size ≤ vk.X.l ∧
        (Array.range (2 * Wb)).size = 2 * Wb
  l_insertD : ∀ x (l : List Nat), (insertD x l).length ≤ l.length + 1
  l_treeSel : ∀ Wb j, (treeSel' vk.X Wb j π.pos).size ≤ 2 * (Wb + 1) * vk.X.l
  l_fixOps : ∀ cs vF, (fixOps' vk.X vk.cols cs vF).size ≤ vk.cols.size * (vk.X.r + 1) ∧
      ∀ c ∈ vk.cols.toList, (List.range (fixLen vk.X c)).length ≤ vk.X.r + 1
  l10_11_12 : π.vT.toList.length ≤ proofSize π ∧ (∀ a ∈ π.vT.toList, a.toList.length ≤ proofSize π) ∧ π.vQ.toList.length ≤ proofSize π
  -- allCanonOnline'
  l40_49 : z.length ≤ z.length ∧ π.roots.size ≤ proofSize π ∧ (∀ l ∈ π.roots.toList, l.length ≤ proofSize π) ∧ π.vT.size ≤ proofSize π ∧
      (∀ a ∈ π.vT.toList, a.size ≤ proofSize π) ∧ π.vQ.size ≤ proofSize π ∧ π.pfinal.size ≤ proofSize π ∧ π.vals.size ≤ proofSize π ∧
      (∀ a ∈ π.vals.toList, a.size ≤ proofSize π) ∧ π.sibs.size ≤ proofSize π ∧ (∀ a ∈ π.sibs.toList, a.size ≤ proofSize π) ∧
      (∀ a ∈ π.sibs.toList, ∀ l ∈ a.toList, l.length ≤ proofSize π)
  -- verifyFixT
  l61_68 : πF.vF.size ≤ fixSize πF ∧ (∀ a ∈ πF.vF.toList, a.size ≤ fixSize πF) ∧ πF.pfinal.size ≤ fixSize πF ∧ πF.roots.size ≤ fixSize πF ∧
      (∀ l ∈ πF.roots.toList, l.length ≤ fixSize πF) ∧ πF.vals.size ≤ fixSize πF ∧ (∀ a ∈ πF.vals.toList, a.size ≤ fixSize πF) ∧
      πF.sibs.size ≤ fixSize πF ∧ (∀ a ∈ πF.sibs.toList, a.size ≤ fixSize πF) ∧ (∀ a ∈ πF.sibs.toList, ∀ l ∈ a.toList, l.length ≤ fixSize πF)
  l70 : ∀ ζ, (fixCtx π ζ).length ≤ proofSize π + 3
  l72 : ∀ ctx vF pf, (fixMsgs vk.X.k ctx vF πF.roots pf).size = vk.X.k + 4
  l73_74_76 : FSLen FSf → ∀ (ms : Array (List Nat)), (chalsFix vk.X FSf z ms).size = ms.size ∧
      ∀ i : Nat, List.length ((chalsFix vk.X FSf z ms)[i]!) ≤ vk.X.l + 3
  -- structural recursion / pow
  pow_hN : powCnt (vk.X.hN + 1) vk.X.hN ≤ vk.X.nD + 2
  pow_dN : powCnt (2 ^ vk.X.nD + 1) (2 ^ vk.X.nD) ≤ vk.X.nD + 2
  pow_idx : ∀ e, e < 2 ^ vk.X.nD → powCnt (e + 1) e ≤ vk.X.nD + 2
  pow_gen : ∀ j, j < vk.X.nq → powCnt (j / 3 + 1) (j / 3) ≤ vk.X.nq + 2 ∧ powCnt (j % 3 + 1) (j % 3) ≤ 4
  pow_any : ∀ e, powCnt (e + 1) e ≤ Nat.log2 e + 2
  pow_yAt : ∀ w, w ≤ vk.X.k + 1 → powCnt (2 ^ w + 1) (2 ^ w) ≤ vk.X.nD + 2

theorem verifyOnline_loops_bounded (vk : VK) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof)
    (hs : OnlineShape vk π πF) : LoopBounds vk FS FSf z π πF := by
  have hsize_roots := hs.roots
  refine
    { l1_92_99 := by simp
      l9_90 := by simp
      l7 := by simp
      l91 := by simp
      l93_94 := by simp
      l95 := rfl
      l96_26_27 := ?_
      l97 := by simp
      l98_20 := ?_
      l100_22 := by simp
      l24 := by simp
      l101_80_2_3 := ?_
      l102_81 := by simp
      l23 := ?_
      l4 := ?_
      l5_6_8 := ?_
      l13 := fun n h => by simpa using h
      l14_21_29_60_28 := by simp
      l15_16_18_17 := ?_
      l_insertD := insertD_length
      l_treeSel := ?_
      l_fixOps := ?_
      l10_11_12 := ?_
      l40_49 := ?_
      l61_68 := ?_
      l70 := ?_
      l72 := ?_
      l73_74_76 := ?_
      pow_hN := ?_
      pow_dN := ?_
      pow_idx := ?_
      pow_gen := ?_
      pow_any := pow_iters
      pow_yAt := ?_ }
  · intro t ht env
    have := chip_len_le_dag vk.X t ht
    refine ⟨?_, ?_, this.2⟩
    · simp only [evalDag', lpA, Array.size_map]; exact this.2
    · simpa using this.1
  · intro ζ; rw [Array.length_toList]; exact openPts_size vk.X ζ
  · simp [hs.pos, hs.fpos, hs.pf]
  · intro cs vT vQ; rw [Array.length_toList]; exact openingList_size_le vk.X cs vT vQ
  · intro a b c d e f
    simp only [Array.size_append, Array.size_extract, hs.roots]
    simp; omega
  · intro hfs ms
    refine ⟨by simp [chalsOnline, lpA], ?_⟩
    intro i
    unfold chalsOnline lpA
    refine range_map_getElem_len _ _ _ ?_ i
    intro i
    split
    · simp
    · rw [hfs]; exact roundNl_le vk.X i
  · intro Wb j f hf hp
    have := sortedDistinct_size (π.pos.map f)
    simp only [Array.size_map] at this
    refine ⟨by simp [hp], by omega, by simp⟩
  · intro Wb j
    have := treeSel_size_le vk.X Wb j π.pos
    rw [hs.pos] at this; exact this
  · intro cs vF
    exact ⟨fixOps_size_le vk.X vk.cols cs vF, fun c _ => by simpa using fixLen_le vk.X c⟩
  · have h0 : π.vT.size ≤ proofSize π := by unfold proofSize; omega
    refine ⟨by simpa using h0, ?_, by unfold proofSize; simp; omega⟩
    intro a ha
    have := arr2_le π.vT (proofSize π) (by unfold proofSize; omega) a ha
    simpa using this
  · have hsb := sibs_le π.sibs (proofSize π) (by unfold proofSize; omega)
    refine ⟨Nat.le_refl _, by unfold proofSize; omega, limbs_le _ _ (by unfold proofSize; omega), by unfold proofSize; omega,
      arr2_le π.vT _ (by unfold proofSize; omega), by unfold proofSize; omega, by unfold proofSize; omega,
      by unfold proofSize; omega, arr2_le π.vals _ (by unfold proofSize; omega), by unfold proofSize; omega, hsb.1, hsb.2⟩
  · have hsb := sibs_le πF.sibs (fixSize πF) (by unfold fixSize; omega)
    refine ⟨by unfold fixSize; omega, arr2_le πF.vF _ (by unfold fixSize; omega), by unfold fixSize; omega,
      by unfold fixSize; omega, limbs_le _ _ (by unfold fixSize; omega), by unfold fixSize; omega,
      arr2_le πF.vals _ (by unfold fixSize; omega), by unfold fixSize; omega, hsb.1, hsb.2⟩
  · intro ζ
    have e1 : ((π.roots.extract 0 4).toList.flatMap id).length ≤ limbsOf π.roots := by
      rw [Array.toList_extract, List.length_flatMap]
      have := sum_take_le List.length π.roots.toList 4
      unfold limbsOf; simpa using this
    have : (fixCtx π ζ).length = ((π.roots.extract 0 4).toList.flatMap id).length + 3 := by
      simp [fixCtx, K3.limbs]
    unfold proofSize; omega
  · intro ctx vF pf
    simp only [fixMsgs, Array.size_append, Array.size_extract, hs.froots]
    simp; omega
  · intro hfs ms
    refine ⟨by simp [chalsFix, lpA], ?_⟩
    intro i
    unfold chalsFix lpA
    refine range_map_getElem_len _ _ _ ?_ i
    intro i
    split
    · simp
    · rw [hfs]; exact fixNl_le _ _ i
  · have := bits_hN_le vk.X.hN vk.X.nD hs.hN
    have h2 := pow_iters vk.X.hN
    omega
  · have h2 := pow_iters (2 ^ vk.X.nD)
    simp at h2; omega
  · intro e he; have := pow_iters e; have := log2_le_of_lt_pow he; omega
  · intro j hj
    have a1 := pow_iters (j / 3)
    have a2 := pow_iters (j % 3)
    have b1 : j / 3 < 2 ^ (j / 3) := Nat.lt_two_pow_self
    have b2 : j % 3 < 2 ^ 2 := by have := Nat.mod_lt j (show 3 > 0 by omega); omega
    have c1 := log2_le_of_lt_pow b1
    have c2 := log2_le_of_lt_pow b2
    omega
  · intro w hw
    have := pow_iters (2 ^ w)
    simp at this; have := hs.hk; omega

#print axioms verifyOnline_loops_bounded
#print axioms verifyOnlineE_eq
#print axioms verifyFix_eq
#print axioms K3_powAuxT_spec
#print axioms powCnt_le
#print axioms goRootT_fst
#print axioms goRoot_calls_le
#print axioms costModel_le
#print axioms verifyOnline_cost_of_lb
#print axioms verifyOnline_cost
#print axioms lbWell_of_sorted
#print axioms treeSel_sorted
#print axioms blockLayout_le
#print axioms treeSel_size_le
#print axioms openingList_size_le

end NockvmE2E.Exec.V
