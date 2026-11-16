import Nock.Framework.Core
import Nock.Walk

/-!
Traversability in the framework: the `Traversable` structure (bijections from the compute and memory languages to products of recursively-verifiable-tree languages), the Fibonacci example (`slt`, `FG`, forward inclusion `fib_slt_RVT` and the reverse inclusion `RVT_FG_unique` over proper-binary trees), and `Nock.Walk.RVTWithArity` for exact arity-`n` RVT membership.
-/

namespace Nock.Framework

/-! ## `Def:traversable` — `(F,F*)`-traversable -/

open Nock.Walk in
/-- **`Def:traversable`.**  A uniquely memory-execution separable language is
    *execution traversable over `F`* if there is a bijection `φ_comp` from its compute-language
    `L_Lang^comp` to a product `∏_{i=1}^{k_comp} L_RVT^{F_i,n}` of recursively-verifiable-tree
    languages, and *memory traversable over `F*`* if likewise `φ_mem` to `∏ L_RVT^{F*_i,n}`; it is
    `(F,F*)`-traversable if both hold.  `L_RVT^{F_i,n}` is `{t // RVT F_i t}`
    (`Nock.Walk.RVT`). -/
structure Traversable {LTc LTm : Type*} {nc nm kc km : ℕ}
    (Lcomp Lmem : Type*)
    (Fc : Fin kc → LTc → (Fin nc → Option LTc) → Prop)
    (Fm : Fin km → LTm → (Fin nm → Option LTm) → Prop) where
  /-- Execution-traversal bijection `φ_comp`. -/
  φcomp : Lcomp ≃ (Π i : Fin kc, {t : NTree LTc // RVT (Fc i) t})
  /-- Memory-traversal bijection `φ_mem`. -/
  φmem : Lmem ≃ (Π i : Fin km, {t : NTree LTm // RVT (Fm i) t})

/-! ## `Example:fibonacci` — Fibonacci as an RVT sanity instance -/

namespace Fib

/-- The two Fibonacci states `𝒮 = {decompose, halt}`. -/
inductive FibState where
  | decompose
  | halt
deriving DecidableEq, Repr

/-- The Fibonacci label space `𝓛𝓣_f = 𝒮 × 𝒢` where `𝒢 = {(n, f(n))}` is the graph of the
    Fibonacci function `f = Nat.fib`. -/
abbrev LTf : Type := FibState × (ℕ × ℕ)

open Nock.Walk

/-- **`slt(n)`.**  The stateful labeled proper binary tree for `n`: leaves
    `(halt, (n, f(n)))` at `n ∈ {1,2}`; otherwise `(decompose, (n, f(n)))` with children
    `slt(n-1)`, `slt(n-2)`.  (`n = 0` is a dummy leaf, unused; the language is `n ≥ 1`.) -/
def slt : ℕ → NTree LTf
  | 0 => NTree.node (FibState.halt, (0, 0)) []
  | 1 => NTree.node (FibState.halt, (1, Nat.fib 1)) []
  | 2 => NTree.node (FibState.halt, (2, Nat.fib 2)) []
  | (n + 3) => NTree.node (FibState.decompose, (n + 3, Nat.fib (n + 3)))
      [slt (n + 2), slt (n + 1)]

/-- **`𝓛(G,2)` — the Fibonacci labeling verifier `V_G`.**  Accepts
    `(parent, (lc, rc))` iff one of the four cases holds: (1) a `halt` leaf at `(1,1)`/`(2,1)`;
    (2) `(decompose,(3,2))` with `halt`-children `(2,1),(1,1)`; (3) `(decompose,(4,3))` with
    children `(decompose,(3,2)),(halt,(2,1))`; (4) all three states `decompose`, `n ≥ 5`,
    `n_L = n-1`, `n_R = n-2`, `F = F_L + F_R`. -/
def FG : LTf → (Fin 2 → Option LTf) → Prop := fun lbl xout =>
  ((lbl = (FibState.halt, (1, 1)) ∨ lbl = (FibState.halt, (2, 1)))
      ∧ xout 0 = none ∧ xout 1 = none)
  ∨ (lbl = (FibState.decompose, (3, 2))
      ∧ xout 0 = some (FibState.halt, (2, 1)) ∧ xout 1 = some (FibState.halt, (1, 1)))
  ∨ (lbl = (FibState.decompose, (4, 3))
      ∧ xout 0 = some (FibState.decompose, (3, 2)) ∧ xout 1 = some (FibState.halt, (2, 1)))
  ∨ (lbl.1 = FibState.decompose ∧ 5 ≤ lbl.2.1 ∧
      ∃ nL FL nR FR, xout 0 = some (FibState.decompose, (nL, FL))
        ∧ xout 1 = some (FibState.decompose, (nR, FR))
        ∧ nL = lbl.2.1 - 1 ∧ nR = lbl.2.1 - 2 ∧ lbl.2.2 = FL + FR)

theorem slt1_eq : slt 1 = NTree.node (FibState.halt, (1, 1)) [] := by
  simp only [slt, Nat.fib_one]
theorem slt2_eq : slt 2 = NTree.node (FibState.halt, (2, 1)) [] := by
  simp only [slt, Nat.fib_two]
theorem slt_ge3_eq (k : ℕ) :
    slt (k + 3) = NTree.node (FibState.decompose, (k + 3, Nat.fib (k + 3)))
      [slt (k + 2), slt (k + 1)] := by
  simp only [slt]

theorem fib3 : Nat.fib 3 = 2 := by decide
theorem fib4 : Nat.fib 4 = 3 := by decide

theorem label_slt1 : (slt 1).label = (FibState.halt, (1, 1)) := by
  rw [slt1_eq, NTree.label_node]
theorem label_slt2 : (slt 2).label = (FibState.halt, (2, 1)) := by
  rw [slt2_eq, NTree.label_node]
/-- The label of `slt n` for `n ≥ 3` is `(decompose, (n, f(n)))`. -/
theorem label_slt_ge (n : ℕ) (h : 3 ≤ n) :
    (slt n).label = (FibState.decompose, (n, Nat.fib n)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [slt_ge3_eq, NTree.label_node]

@[simp] theorem childLabel_zero (l : LTf) (a b : NTree LTf) :
    (NTree.node l [a, b]).childLabel 0 = some a.label := by
  simp [NTree.childLabel, NTree.childOpt]
@[simp] theorem childLabel_one (l : LTf) (a b : NTree LTf) :
    (NTree.node l [a, b]).childLabel 1 = some b.label := by
  simp [NTree.childLabel, NTree.childOpt]

/-- A `decompose`-labeled node with `n ≥ 3` is never accepted by `V_G` with no children — so it
    is not a leaf (needed for the RVT leaf-iff clause). -/
theorem not_FG_decompose_none (k : ℕ) :
    ¬ FG (FibState.decompose, (k + 3, Nat.fib (k + 3))) (fun _ => none) := by
  rintro (⟨h, _, _⟩ | ⟨h, h0, _⟩ | ⟨h, h0, _⟩ | ⟨-, -, nL, FL, nR, FR, h0, _⟩) <;>
    simp_all

/-- **`Example:fibonacci` — forward inclusion `L_Fib ⊆ L_RVT^{G,2}`.**  Every
    Fibonacci stateful tree `slt(n)` (`n ≥ 1`) is a recursively-verifiable tree over `𝓛(G,2)`:
    the *a priori* weaker `V_G` constraint `F = F_L + F_R` is satisfied by the genuine Fibonacci
    decomposition (`Nat.fib_add_two`).  This is the substantive direction of the paper's
    `L_Fib ≡ L_RVT^{G,2}`. -/
theorem fib_slt_RVT : ∀ n, 1 ≤ n → RVT FG (slt n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => intro h; omega
    | 1 =>
      intro _
      rw [slt1_eq, RVT]
      exact ⟨Or.inl ⟨Or.inl rfl, rfl, rfl⟩, by simp, iff_of_true rfl (Or.inl ⟨Or.inl rfl, rfl, rfl⟩)⟩
    | 2 =>
      intro _
      rw [slt2_eq, RVT]
      exact ⟨Or.inl ⟨Or.inr rfl, rfl, rfl⟩, by simp, iff_of_true rfl (Or.inl ⟨Or.inr rfl, rfl, rfl⟩)⟩
    | (m + 3) =>
      intro _
      have hchild : ∀ c ∈ [slt (m + 2), slt (m + 1)], RVT FG c := by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with h | h
        · subst h; exact ih (m + 2) (by omega) (by omega)
        · subst h; exact ih (m + 1) (by omega) (by omega)
      rw [slt_ge3_eq, RVT]
      refine ⟨?_, hchild, iff_of_false (by simp [NTree.isLeaf]) (not_FG_decompose_none m)⟩
      -- FG holds at the node with its actual child-labels
      match m with
      | 0 =>
        exact Or.inr (Or.inl ⟨by decide, by simp [label_slt2], by simp [label_slt1]⟩)
      | 1 =>
        refine Or.inr (Or.inr (Or.inl ⟨by decide, ?_, by simp [label_slt2]⟩))
        simp [label_slt_ge 3 (by norm_num), fib3]
      | (j + 2) =>
        refine Or.inr (Or.inr (Or.inr ⟨rfl, by show 5 ≤ j + 2 + 3; omega,
          j + 2 + 2, Nat.fib (j + 2 + 2), j + 2 + 1, Nat.fib (j + 2 + 1), ?_, ?_,
          by show j + 2 + 2 = j + 2 + 3 - 1; omega, by show j + 2 + 1 = j + 2 + 3 - 2; omega, ?_⟩))
        · simp [label_slt_ge (j + 2 + 2) (by omega)]
        · simp [label_slt_ge (j + 2 + 1) (by omega)]
        · show Nat.fib (j + 2 + 3) = Nat.fib (j + 2 + 2) + Nat.fib (j + 2 + 1)
          rw [show j + 2 + 3 = (j + 2 + 1) + 2 by omega, Nat.fib_add_two]; ring

/-! ### `Def:state_data_separation` instance for Fibonacci -/

/-- **`fanout` for `𝓛(G,2)`**: the branching `decompose` state has
    `fanout = 2`, the terminal `halt` state has `fanout = 0`. -/
def fibFanout : FibState → ℕ
  | FibState.decompose => 2
  | FibState.halt => 0

/-- **`Def:state_data_separation` INSTANCE — the Fibonacci Remark.**  `𝓛(G,2)` is a
    *solely state-traversable* and *state-defined dynamic labeling* language with
    `S_leaf = {halt}` and `fanout(decompose) = 2`, `fanout(halt) = 0` — exactly the paper's Remark
    following `Def:state_data_separation`, matching the `FG` verifier of this section. -/
noncomputable def FG_stateSep : StateSep FG where
  Sleaf := fun s => s = FibState.halt
  fanout := fibFanout
  fanout_le := by intro s; cases s <;> simp [fibFanout]
  fanout_leaf := by intro s h; subst h; rfl
  dynamic := by
    intro s d xout hF i
    have key : (s = FibState.halt ∧ xout 0 = none ∧ xout 1 = none)
             ∨ (s = FibState.decompose ∧ xout 0 ≠ none ∧ xout 1 ≠ none) := by
      rcases hF with ⟨hlbl, h0, h1⟩ | ⟨hlbl, h0, h1⟩ | ⟨hlbl, h0, h1⟩
                   | ⟨hd, _, nL, FL, nR, FR, h0, h1, _⟩
      · exact Or.inl ⟨by rcases hlbl with h | h <;> exact congrArg Prod.fst h, h0, h1⟩
      · exact Or.inr ⟨congrArg Prod.fst hlbl, by rw [h0]; exact Option.some_ne_none _,
                      by rw [h1]; exact Option.some_ne_none _⟩
      · exact Or.inr ⟨congrArg Prod.fst hlbl, by rw [h0]; exact Option.some_ne_none _,
                      by rw [h1]; exact Option.some_ne_none _⟩
      · exact Or.inr ⟨hd, by rw [h0]; exact Option.some_ne_none _,
                      by rw [h1]; exact Option.some_ne_none _⟩
    rcases key with ⟨hs, h0, h1⟩ | ⟨hs, h0, h1⟩ <;> subst hs <;> fin_cases i <;>
      simp_all [fibFanout]
  solely := by
    rintro ⟨l, ch⟩ hrvt
    rw [RVT] at hrvt
    obtain ⟨hF, _, hleaf⟩ := hrvt
    simp only [NTree.label_node]
    constructor
    · intro hs
      rw [hleaf]
      rcases hF with ⟨hlbl, _, _⟩ | ⟨hlbl, _, _⟩ | ⟨hlbl, _, _⟩ | ⟨hd, _⟩
      · exact Or.inl ⟨hlbl, rfl, rfl⟩
      · rw [hlbl] at hs; exact absurd hs (by decide)
      · rw [hlbl] at hs; exact absurd hs (by decide)
      · rw [hd] at hs; exact absurd hs (by decide)
    · intro hil
      rw [hleaf] at hil
      rcases hil with ⟨hlbl, _, _⟩ | ⟨hlbl, h0, _⟩ | ⟨hlbl, h0, _⟩ | ⟨hd, _, nL, FL, nR, FR, h0, _⟩
      · rcases hlbl with h | h <;> simp [h]
      · exact absurd h0 (by simp)
      · exact absurd h0 (by simp)
      · exact absurd h0 (by simp)

/-! ### Reverse inclusion `L_RVT^{G,2} ⊆ L_Fib`

  **Faithfulness note (arity).**  The paper's `L_RVT^{F,n}` is over `L_SLT^n`, the *n-ary* (here
  proper-binary) stateful trees.  The Lean `Nock.Walk.RVT` predicate constrains only
  child indices `0,…,n−1` and does *not* bound the number of children, so `{t // RVT FG t}` is
  strictly larger than the paper's language: e.g. a node with a third child that is itself a valid
  `RVT FG` Fibonacci subtree satisfies `RVT FG` but equals no `slt n`.  The reverse inclusion is
  therefore proved over exactly the paper's object — *proper-binary* trees (`properBinary`, matching
  `L_SLT^2`) — which is the faithful reading of `L_RVT^{G,2}`.  (That `RVT` alone omits the arity
  bound is a separate observation about the `L_SLT^n` encoding.) -/

/-- Proper-binary stateful trees: each node has either no children (a
    leaf) or exactly two children, each itself proper-binary. -/
def properBinary : NTree LTf → Prop
  | .node _ []      => True
  | .node _ [a, b]  => properBinary a ∧ properBinary b
  | _               => False

/-- Inversion of the `slt` label: for `n ≥ 1`, the root label of `slt n` pins `n`. -/
theorem slt_label_cases (n : ℕ) (h1 : 1 ≤ n) :
    (n = 1 ∧ (slt n).label = (FibState.halt, (1, 1)))
      ∨ (n = 2 ∧ (slt n).label = (FibState.halt, (2, 1)))
      ∨ (3 ≤ n ∧ (slt n).label = (FibState.decompose, (n, Nat.fib n))) := by
  match n with
  | 0 => omega
  | 1 => exact Or.inl ⟨rfl, label_slt1⟩
  | 2 => exact Or.inr (Or.inl ⟨rfl, label_slt2⟩)
  | (k + 3) => exact Or.inr (Or.inr ⟨by omega, label_slt_ge (k + 3) (by omega)⟩)

/-- If `slt n` (`n ≥ 1`) has a `halt`-`(2,1)` label then `n = 2`; similarly the other leaf. -/
theorem slt_eq_two_of_label {n : ℕ} (h1 : 1 ≤ n)
    (hl : (slt n).label = (FibState.halt, (2, 1))) : n = 2 := by
  rcases slt_label_cases n h1 with ⟨_, h⟩ | ⟨hn, _⟩ | ⟨_, h⟩ <;> simp_all

theorem slt_eq_one_of_label {n : ℕ} (h1 : 1 ≤ n)
    (hl : (slt n).label = (FibState.halt, (1, 1))) : n = 1 := by
  rcases slt_label_cases n h1 with ⟨hn, _⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> simp_all

/-- If `slt n` (`n ≥ 1`) has a `decompose`-`(m,F)` label then `n = m ≥ 3` and `F = fib m`. -/
theorem slt_decompose_label {n m F : ℕ} (h1 : 1 ≤ n)
    (hl : (slt n).label = (FibState.decompose, (m, F))) : n = m ∧ 3 ≤ m ∧ F = Nat.fib m := by
  rcases slt_label_cases n h1 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨hn, h⟩
  · rw [h] at hl; simp at hl
  · rw [h] at hl; simp at hl
  · rw [h] at hl
    rw [Prod.mk.injEq, Prod.mk.injEq] at hl
    obtain ⟨-, hnm, hFF⟩ := hl
    subst hnm
    exact ⟨rfl, hn, hFF.symm⟩

theorem slt3_eq : slt 3 = NTree.node (FibState.decompose, (3, 2)) [slt 2, slt 1] := by
  have := slt_ge3_eq 0; simpa [fib3] using this
theorem slt4_eq : slt 4 = NTree.node (FibState.decompose, (4, 3)) [slt 3, slt 2] := by
  have := slt_ge3_eq 1; simpa [fib4] using this

/-- The child-label vector of `node l [a, b]` (`n = 2`) is `![some a.label, some b.label]`. -/
theorem childLabel_pair (l : LTf) (a b : NTree LTf) :
    (fun i : Fin 2 => (NTree.node l [a, b]).childLabel (i : ℕ))
      = ![some a.label, some b.label] := by
  funext i; fin_cases i <;> simp [NTree.childLabel, NTree.childOpt]

/-- **Reverse inclusion / uniqueness.**  Every proper-binary tree recognised by
    the Fibonacci verifier `V_G` (`𝓛(G,2)`) is a Fibonacci stateful tree `slt n` (`n ≥ 1`).  With
    `fib_slt_RVT` this closes `L_Fib ≡ L_RVT^{G,2}` (over proper-binary trees). -/
theorem RVT_FG_unique (t : NTree LTf) (hb : properBinary t) (hrvt : RVT FG t) :
    ∃ n, 1 ≤ n ∧ t = slt n := by
  -- strong induction on the tree size
  suffices H : ∀ s (t : NTree LTf), t.size ≤ s → properBinary t → RVT FG t →
      ∃ n, 1 ≤ n ∧ t = slt n by
    exact H t.size t le_rfl hb hrvt
  intro s
  induction s with
  | zero =>
    intro t ht
    cases t with
    | node l ch => simp only [NTree.size] at ht; omega
  | succ s ih =>
    intro t ht hbt hrt
    cases t with
    | node l ch =>
      -- proper-binary: `ch = []` (leaf) or `ch = [a, b]`
      cases ch with
      | nil =>
        -- leaf: the RVT leaf-iff gives `FG l (fun _ ↦ ⊥)` ⇒ `l` is a `halt` leaf `(1,1)`/`(2,1)`
        rw [RVT] at hrt
        obtain ⟨_, _, hleaf⟩ := hrt
        have hFG : FG l (fun _ : Fin 2 => (none : Option LTf)) := hleaf.mp rfl
        rcases hFG with ⟨(hl | hl), _, _⟩ | ⟨_, h0, _⟩ | ⟨_, h0, _⟩ | ⟨_, _, _, _, _, _, h0, _⟩
        · exact ⟨1, by norm_num, by rw [slt1_eq, hl]⟩
        · exact ⟨2, by norm_num, by rw [slt2_eq, hl]⟩
        all_goals simp at h0
      | cons a tl =>
        cases tl with
        | nil => exact absurd hbt (by simp [properBinary])
        | cons b tl2 =>
          cases tl2 with
          | cons c tl3 => exact absurd hbt (by simp [properBinary])
          | nil =>
            obtain ⟨hba, hbb⟩ := hbt
            rw [RVT] at hrt
            obtain ⟨hFG, hch, _⟩ := hrt
            have hra : RVT FG a := hch a (by simp)
            have hrb : RVT FG b := hch b (by simp)
            have hsz : (NTree.node l [a, b]).size = 1 + a.size + b.size := by
              simp [NTree.size]; ring
            obtain ⟨na, hna1, rfl⟩ := ih a (by omega) hba hra
            obtain ⟨nb, hnb1, rfl⟩ := ih b (by omega) hbb hrb
            rw [childLabel_pair] at hFG
            rcases hFG with ⟨_, h0, _⟩ | ⟨hl, h0, h1⟩ | ⟨hl, h0, h1⟩
              | ⟨hld, hge5, nL, FL, nR, FR, h0, h1, hnL, hnR, hFsum⟩
            · -- case 1 (halt leaf): impossible, `xout 0 = ⊥`
              simp at h0
            · -- case 2: l = (decompose,(3,2)); children (halt,(2,1)),(halt,(1,1))
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
                Option.some.injEq] at h0 h1
              obtain rfl := slt_eq_two_of_label hna1 h0
              obtain rfl := slt_eq_one_of_label hnb1 h1
              exact ⟨3, by norm_num, by rw [hl, slt3_eq]⟩
            · -- case 3: l = (decompose,(4,3)); children (decompose,(3,2)),(halt,(2,1))
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
                Option.some.injEq] at h0 h1
              obtain ⟨rfl, _, _⟩ := slt_decompose_label hna1 h0
              obtain rfl := slt_eq_two_of_label hnb1 h1
              exact ⟨4, by norm_num, by rw [hl, slt4_eq]⟩
            · -- case 4: general decompose, `l.2.1 ≥ 5`
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
                Option.some.injEq] at h0 h1
              obtain ⟨hna_eq, -, hFL⟩ := slt_decompose_label hna1 h0
              obtain ⟨hnb_eq, -, hFR⟩ := slt_decompose_label hnb1 h1
              refine ⟨l.2.1, by omega, ?_⟩
              have hF : l.2.2 = Nat.fib l.2.1 := by
                rw [hFsum, hFL, hFR, hnL, hnR]
                conv_rhs => rw [show l.2.1 = (l.2.1 - 2) + 2 by omega]
                rw [Nat.fib_add_two, show l.2.1 - 1 = (l.2.1 - 2) + 1 by omega]
                ring
              conv_rhs => rw [show l.2.1 = (l.2.1 - 3) + 3 by omega, slt_ge3_eq]
              rw [show (l.2.1 - 3) + 3 = l.2.1 by omega,
                  show (l.2.1 - 3) + 2 = l.2.1 - 1 by omega,
                  show (l.2.1 - 3) + 1 = l.2.1 - 2 by omega,
                  hna_eq, hnb_eq, hnL, hnR, NTree.node.injEq]
              exact ⟨Prod.ext hld (Prod.ext rfl hF), rfl⟩

end Fib

end Nock.Framework

namespace Nock.Walk

/-- **`RVTWithArity F n t` — `t ∈ L_RVT^{F,n}` exactly.**  The faithful arity-`n`
    recursively-verifiable-tree language: `RVT F t` (every node verifies against `F`) **and**
    `ProperArity n t` (every node has `≤ n` children).  `{t // RVT F t}` alone strictly overshoots
    `L_RVT^{F,n}` (see the `ProperArity` docstring); pairing in `ProperArity n` restores the exact
    paper target.  Existing `RVT`/`ProperArity` theorems stay reusable through the `.rvt`/`.arity`
    projections, and `.mk'` lifts any `RVT`+`ProperArity` pair. -/
def RVTWithArity {LT : Type*} {n : ℕ} (F : LT → (Fin n → Option LT) → Prop)
    (t : NTree LT) : Prop :=
  RVT F t ∧ ProperArity n t

/-- Project to bare `RVT` membership (so `RVT` theorems apply). -/
theorem RVTWithArity.rvt {LT : Type*} {n : ℕ} {F : LT → (Fin n → Option LT) → Prop}
    {t : NTree LT} (h : RVTWithArity F t) : RVT F t := h.1

/-- Project to the arity bound. -/
theorem RVTWithArity.arity {LT : Type*} {n : ℕ} {F : LT → (Fin n → Option LT) → Prop}
    {t : NTree LT} (h : RVTWithArity F t) : ProperArity n t := h.2

/-- Constructor bridge: assemble exact arity-`n` RVT membership from its two legs. -/
theorem RVTWithArity.mk' {LT : Type*} {n : ℕ} {F : LT → (Fin n → Option LT) → Prop}
    {t : NTree LT} (hr : RVT F t) (ha : ProperArity n t) : RVTWithArity F t := ⟨hr, ha⟩

end Nock.Walk
