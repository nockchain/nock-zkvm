/-
  Nock/NockVMROM/Thm54/P8Core/VclL/DecodeTree.lean

  ADDITIVE: new module; `Table.lean` is not edited.

  `decodeB0` (T1's decoder) follows every weighted child.  At J-8 a weighted child of rank `(0, 0)` is a
  big atom served by the atom table (SPEC §2.1, F1), so the decoder is made generic in a LEAF RULE
  `leaf : CellRowB0 q → Side → Option (Option Noun)`: `some r` makes the child a leaf denoting `r`,
  `none` follows its serial into the cell table.

  * `decodeTree`, `decodeTree_leaf1 : decodeTree t (leaf1 q) = decodeB0 t` (instance 1, by induction with
    `rfl` steps);
  * **`decodeTree_sound`** — under `TreeOK` (serial gate, `RowOK`, and per child the generic condition
    `ChildOK`: a leaf with a genuine noun of the right size, or a non-leaf weighted child served by a cell row),
    every row decodes to `[L R]` with `l = enc L`, `r = enc R`, `p = enc [L R]`, `|[L R]| = μ + 1`;
  * **`decode_sound_of_generic`** — T1's `decode_sound` re-derived as the instance `leaf1` (the generic lemma
    absorbs its proof: no second copy of the induction);
  * the two-provider instance: `leaf2 ext` (a weighted rank-`(0, 0)` child is the atom `ext idx` named by the
    external provider), `ValidityServed2` (each weighted child is served by a cell row OR by an external
    provider `vp`), `AtomLeaves` (each external key is `(E (atom v), 0, 0, idx)` with `ext idx = atom v`),
    **`row_genuine2`** — the two-provider `row_genuine`: a rank-`(0, 0)` weighted child is the atom of its atom-
    table serial (F1: never a cell row, `no_cell_provides_rank0`), any other weighted child is the decoded noun
    of its cell serial, a zero-weight child is its inline atom.
-/
import Nock.NockVMROM.Thm54.P8Core.VclL.Table

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL

open Nock
open Nock.ComputeTable (FP)

/-! ## 1. The generic decoder -/

section Decode
variable {q : ℕ}

/-- A child side. -/
inductive Side | L | R
deriving DecidableEq

namespace CellRowB0
/-- The side's weight, child serial, inline atom and rank limbs. -/
def wS (c : CellRowB0 q) : Side → Bool | .L => c.wL | .R => c.wR
def idS (c : CellRowB0 q) : Side → ℕ | .L => c.idL | .R => c.idR
def aS (c : CellRowB0 q) : Side → ZMod q | .L => c.aL | .R => c.aR
def hiS (c : CellRowB0 q) : Side → ℕ | .L => c.hiL | .R => c.hiR
def loS (c : CellRowB0 q) : Side → ℕ | .L => c.loL | .R => c.loR
def muS (c : CellRowB0 q) (s : Side) : ℕ := c.hiS s * 2 ^ 62 + c.loS s
end CellRowB0

/-- **The generic decoder.**  `leaf c s = some r`: the child on side `s` is a leaf denoting `r`;
`none`: follow the child serial. -/
def decodeTree (t : List (CellRowB0 q)) (leaf : CellRowB0 q → Side → Option (Option Noun)) :
    ℕ → ℕ → Option Noun
  | 0, _ => none
  | fuel + 1, i =>
    (t[i]?).bind fun c =>
      (match leaf c .L with
        | some r => r
        | none => decodeTree t leaf fuel (c.idS .L)).bind fun a =>
      (match leaf c .R with
        | some r => r
        | none => decodeTree t leaf fuel (c.idS .R)).bind fun b =>
        some (.cell a b)

/-- The child a row names on side `s` under the leaf rule. -/
def childT (t : List (CellRowB0 q)) (leaf : CellRowB0 q → Side → Option (Option Noun)) (f : ℕ)
    (c : CellRowB0 q) (s : Side) : Option Noun :=
  match leaf c s with
  | some r => r
  | none => decodeTree t leaf f (c.idS s)

theorem decodeTree_succ (t : List (CellRowB0 q)) (leaf : CellRowB0 q → Side → Option (Option Noun))
    (f i : ℕ) :
    decodeTree t leaf (f + 1) i =
      (t[i]?).bind fun c => (childT t leaf f c .L).bind fun a => (childT t leaf f c .R).bind fun b =>
        some (.cell a b) := rfl

/-- **Instance 1**: `decodeB0`'s rule — inline atoms are leaves, every weighted child is followed. -/
def leaf1 (q : ℕ) : CellRowB0 q → Side → Option (Option Noun) :=
  fun c s => if c.wS s then none else some (some (.atom (c.aS s).val))

/-- **`decodeTree` at `leaf1` is `decodeB0`** (induction on fuel, `rfl` steps). -/
theorem decodeTree_leaf1 (t : List (CellRowB0 q)) : ∀ f i, decodeTree t (leaf1 q) f i = decodeB0 t f i
  | 0, _ => rfl
  | f + 1, i => by
    rw [decodeTree_succ, decodeB0]
    congr 1; funext c
    have hL : childT t (leaf1 q) f c .L = if c.wL then decodeB0 t f c.idL else some (.atom c.aL.val) := by
      unfold childT
      cases hw : c.wL
      · simp [leaf1, CellRowB0.wS, CellRowB0.aS, hw]
      · have hl : leaf1 q c .L = none := by simp [leaf1, CellRowB0.wS, hw]
        rw [hl]; simp [CellRowB0.idS, decodeTree_leaf1 t f]
    have hR : childT t (leaf1 q) f c .R = if c.wR then decodeB0 t f c.idR else some (.atom c.aR.val) := by
      unfold childT
      cases hw : c.wR
      · simp [leaf1, CellRowB0.wS, CellRowB0.aS, hw]
      · have hl : leaf1 q c .R = none := by simp [leaf1, CellRowB0.wS, hw]
        rw [hl]; simp [CellRowB0.idS, decodeTree_leaf1 t f]
    rw [hL, hR]

theorem decodeTree_mono (t : List (CellRowB0 q)) (leaf : CellRowB0 q → Side → Option (Option Noun)) :
    ∀ f f' i n, f ≤ f' → decodeTree t leaf f i = some n → decodeTree t leaf f' i = some n
  | 0, _, _, _, _, h => by simp [decodeTree] at h
  | f + 1, f', i, n, hle, h => by
    obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    have hfg : f ≤ g := by omega
    rw [decodeTree_succ] at h ⊢
    simp only [Option.bind_eq_some_iff] at h ⊢
    obtain ⟨c, hc, a, ha, b, hb, hn⟩ := h
    have hch : ∀ s x, childT t leaf f c s = some x → childT t leaf g c s = some x := by
      intro s x hx
      unfold childT at hx ⊢
      cases hl : leaf c s with
      | some r => rw [hl] at hx; exact hx
      | none => rw [hl] at hx; exact decodeTree_mono t leaf f g _ x hfg hx
    exact ⟨c, hc, a, hch _ _ ha, b, hch _ _ hb, hn⟩

end Decode

/-! ## 2. Generic soundness -/

section Sound
variable {q : ℕ} {Kfp : Type*} [Field Kfp] [Algebra (ZMod q) Kfp]

namespace CellRow
/-- The side's child fingerprint. -/
def fpS (c : CellRow q Kfp) : Side → FP Kfp | .L => c.l | .R => c.r
end CellRow

/-- **The generic per-child condition**: either the leaf rule names a genuine noun of the child's certified
size, or the child is weighted, not a leaf, and its key is a cell row's validity key. -/
def ChildOK (E : Noun → FP Kfp) (t : List (CellRow q Kfp))
    (leaf : CellRowB0 q → Side → Option (Option Noun)) (c : CellRow q Kfp) (s : Side) : Prop :=
  (∃ n, leaf c.b0 s = some (some n) ∧ c.fpS s = E n ∧
      n.leaves = c.b0.muS s + 1) ∨
  (leaf c.b0 s = none ∧ ∃ c' ∈ t, c.fpS s = c'.p ∧ c.b0.hiS s = c'.b0.hi ∧ c.b0.loS s = c'.b0.lo ∧
      c.b0.idS s = c'.b0.idx)

/-- **What the generic decoder reads of an accepted table**: serial gate, row gates, every child `ChildOK`. -/
structure TreeOK (z : Kfp) (E : Noun → FP Kfp) (t : List (CellRow q Kfp))
    (leaf : CellRowB0 q → Side → Option (Option Noun)) : Prop where
  serial : SerialOK (t.map (·.b0))
  rows : ∀ c ∈ t, RowOK z c
  child : ∀ c ∈ t, ∀ s, ChildOK E t leaf c s

theorem muS_L (c : CellRowB0 q) : c.muS .L = c.muL := rfl
theorem muS_R (c : CellRowB0 q) : c.muS .R = c.muR := rfl

/-- **`decodeTree_sound`** — T1 for any leaf rule and any encoder `E` that is the cons gate on cells
(`E [a b] = FP.cons z (E a) (E b)`; `enc z` at instance 1, the bivariate `(z, y)` encoder with
`leafVal` atoms at J-8): on a `TreeOK` table every row of rank `n` decodes (at any fuel `> n`) to
`[L R]` with `l = E L`, `r = E R`, `p = E [L R]`, `|[L R]| = n + 1`.  Strong induction on the certified
rank. -/
theorem decodeTree_sound [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} {E : Noun → FP Kfp}
    (hcons : ∀ a b, E (.cell a b) = FP.cons z (E a) (E b))
    {t : List (CellRow q Kfp)} {leaf : CellRowB0 q → Side → Option (Option Noun)}
    (h : TreeOK z E t leaf) :
    ∀ n, ∀ c ∈ t, c.b0.mu = n → ∀ fuel, n < fuel →
      ∃ L R, decodeTree (t.map (·.b0)) leaf fuel c.b0.idx = some (.cell L R) ∧
        childT (t.map (·.b0)) leaf (fuel - 1) c.b0 .L = some L ∧
        childT (t.map (·.b0)) leaf (fuel - 1) c.b0 .R = some R ∧
        c.l = E L ∧ c.r = E R ∧ c.p = E (.cell L R) ∧ (Noun.cell L R).leaves = n + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hc hn fuel hf
  obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  have hok := h.rows c hc
  have hrank := rowOK_mu hq hok
  have hside : ∀ s, ∃ a, childT (t.map (·.b0)) leaf fuel c.b0 s = some a ∧
      c.fpS s = E a ∧ a.leaves = c.b0.muS s + 1 := by
    intro s
    have hms : c.b0.muS s < n := by
      cases s
      · rw [muS_L, ← hn, hrank]; omega
      · rw [muS_R, ← hn, hrank]; omega
    rcases h.child c hc s with ⟨a, hl, hfp, hlv⟩ | ⟨hl, c', hc', hfp, hhi, hlo, hid⟩
    · exact ⟨a, by unfold childT; rw [hl], hfp, hlv⟩
    · have hmu : c'.b0.mu = c.b0.muS s := by simp [CellRowB0.mu, CellRowB0.muS, hhi, hlo]
      obtain ⟨L, R, hd, -, -, -, -, hp, hlv⟩ := ih _ (by omega) c' hc' rfl fuel (by omega)
      refine ⟨.cell L R, ?_, by rw [hfp, hp], by rw [hlv, hmu]⟩
      unfold childT; rw [hl, hid]; exact hd
  obtain ⟨a, hda, hpa, hla⟩ := hside .L
  obtain ⟨b, hdb, hpb, hlb⟩ := hside .R
  have hmem : c.b0 ∈ t.map (·.b0) := List.mem_map_of_mem hc
  refine ⟨a, b, ?_, by simpa using hda, by simpa using hdb, hpa, hpb, ?_, ?_⟩
  · rw [decodeTree_succ, serial_lookup h.serial hmem, Option.bind_some, hda, Option.bind_some, hdb,
      Option.bind_some]
  · rw [hok.cons, show c.l = c.fpS .L from rfl, show c.r = c.fpS .R from rfl, hpa, hpb, hcons]
  · simp only [Noun.leaves] at hla hlb ⊢; rw [hla, hlb, ← hn, hrank, muS_L, muS_R]; ring

/-! ### Instance 1: T1 (`decode_sound`) is the generic lemma at `leaf1` -/

/-- An accepted table is `TreeOK` at `leaf1`. -/
theorem treeOK_leaf1 [NeZero q] {z : Kfp} {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)}
    (h : TableAccepts z t vl) : TreeOK z (GlobalCarryRecognizer.enc z) t (leaf1 q) := by
  refine ⟨h.serial, h.rows, fun c hc s => ?_⟩
  have hok := h.rows c hc
  cases s with
  | L =>
    cases hw : c.b0.wL with
    | false =>
      obtain ⟨hla, hlo, hhi⟩ := hok.atomL hw
      refine Or.inl ⟨.atom c.b0.aL.val, by simp [leaf1, CellRowB0.wS, CellRowB0.aS, hw], ?_, ?_⟩
      · show c.l = _; rw [hla, atom_enc]
      · simp [Noun.leaves, CellRowB0.muS, CellRowB0.hiS, CellRowB0.loS, hlo, hhi]
    | true =>
      obtain ⟨c', hc', hl, hhi, hlo, hid⟩ := consumed_left h.served hc hw
      exact Or.inr ⟨by simp [leaf1, CellRowB0.wS, hw], c', hc', hl, hhi, hlo, hid⟩
  | R =>
    cases hw : c.b0.wR with
    | false =>
      obtain ⟨hra, hlo, hhi⟩ := hok.atomR hw
      refine Or.inl ⟨.atom c.b0.aR.val, by simp [leaf1, CellRowB0.wS, CellRowB0.aS, hw], ?_, ?_⟩
      · show c.r = _; rw [hra, atom_enc]
      · simp [Noun.leaves, CellRowB0.muS, CellRowB0.hiS, CellRowB0.loS, hlo, hhi]
    | true =>
      obtain ⟨c', hc', hr, hhi, hlo, hid⟩ := consumed_right h.served hc hw
      exact Or.inr ⟨by simp [leaf1, CellRowB0.wS, hw], c', hc', hr, hhi, hlo, hid⟩

theorem childT_leaf1_L (t : List (CellRowB0 q)) (f : ℕ) (c : CellRowB0 q) :
    childT t (leaf1 q) f c .L = childL t f c := by
  unfold childT childL
  cases hw : c.wL
  · simp [leaf1, CellRowB0.wS, CellRowB0.aS, hw]
  · have hl : leaf1 q c .L = none := by simp [leaf1, CellRowB0.wS, hw]
    rw [hl]; simp [CellRowB0.idS, decodeTree_leaf1]

theorem childT_leaf1_R (t : List (CellRowB0 q)) (f : ℕ) (c : CellRowB0 q) :
    childT t (leaf1 q) f c .R = childR t f c := by
  unfold childT childR
  cases hw : c.wR
  · simp [leaf1, CellRowB0.wS, CellRowB0.aS, hw]
  · have hl : leaf1 q c .R = none := by simp [leaf1, CellRowB0.wS, hw]
    rw [hl]; simp [CellRowB0.idS, decodeTree_leaf1]

/-- **`decode_sound` re-derived from the generic lemma** (statement of `Table.lean::decode_sound`,
verbatim): the generic induction absorbs T1's proof. -/
theorem decode_sound_of_generic [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0)
    {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z t vl) :
    ∀ n, ∀ c ∈ t, c.b0.mu = n → ∀ fuel, n < fuel →
      ∃ L R, decodeB0 (t.map (·.b0)) fuel c.b0.idx = some (.cell L R) ∧
        childL (t.map (·.b0)) (fuel - 1) c.b0 = some L ∧
        childR (t.map (·.b0)) (fuel - 1) c.b0 = some R ∧
        c.l = GlobalCarryRecognizer.enc z L ∧ c.r = GlobalCarryRecognizer.enc z R ∧
        c.p = GlobalCarryRecognizer.enc z (.cell L R) ∧ (Noun.cell L R).leaves = n + 1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  intro n c hc hn fuel hf
  obtain ⟨L, R, hd, hL, hR, rest⟩ := decodeTree_sound hq (GlobalCarryRecognizer.enc_cons hz) (treeOK_leaf1 h) n c hc hn fuel hf
  rw [decodeTree_leaf1] at hd
  rw [childT_leaf1_L] at hL
  rw [childT_leaf1_R] at hR
  exact ⟨L, R, hd, hL, hR, rest⟩

/-! ## 3. The two-provider instance (atom-table references) -/

/-- **Instance 2**: a weighted child of rank `(0, 0)` is a leaf denoting `ext idx` (the atom table's value at
the child serial); any other weighted child is followed; an inline atom is a leaf. -/
def leaf2 (q : ℕ) (ext : ℕ → Option Noun) : CellRowB0 q → Side → Option (Option Noun) :=
  fun c s => if c.wS s then (if c.hiS s = 0 ∧ c.loS s = 0 then some (ext (c.idS s)) else none)
    else some (some (.atom (c.aS s).val))

/-- **The two-provider served form**: every weighted child's key is a cell row's validity key OR an
external provider's key. -/
def ValidityServed2 (t : List (CellRow q Kfp)) (vp : List (VKey Kfp)) : Prop :=
  ∀ c ∈ t, ∀ s, c.b0.wS s = true →
    (∃ c' ∈ t, c.fpS s = c'.p ∧ c.b0.hiS s = c'.b0.hi ∧ c.b0.loS s = c'.b0.lo ∧ c.b0.idS s = c'.b0.idx) ∨
    (c.fpS s, c.b0.hiS s, c.b0.loS s, c.b0.idS s) ∈ vp

/-- **An accepted two-provider table** (what the generic decoder reads; the chip-level balance gives
`served`). -/
structure TableAccepts2 (z : Kfp) (t : List (CellRow q Kfp)) (vp : List (VKey Kfp)) : Prop where
  serial : SerialOK (t.map (·.b0))
  rows : ∀ c ∈ t, RowOK z c
  served : ValidityServed2 t vp

/-- **The external providers are atom roots** (g5's key `(⟨z, 0, A_n(y)⟩, 0 + 0√δ, idx)` with the atom
table's T1 at `y`): every external key has rank `(0, 0)` and fingerprint `E (atom v)` with `ext idx = atom v`. -/
def AtomLeaves (E : Noun → FP Kfp) (vp : List (VKey Kfp)) (ext : ℕ → Option Noun) : Prop :=
  ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ ∃ v, ext k.2.2.2 = some (.atom v) ∧ k.1 = E (.atom v)

/-- **The encoder agrees with the cell table's inline-atom gate** on small atoms (`enc z`: `atom_enc`;
the bivariate encoder: `leafVal_small`). -/
def InlineAtoms (q : ℕ) [Algebra (ZMod q) Kfp] (z : Kfp) (E : Noun → FP Kfp) : Prop :=
  ∀ a : ZMod q, E (.atom a.val) = FP.atomFP z (algebraMap (ZMod q) Kfp a)

/-- **F1 at the table**: a cell row's key never has rank `(0, 0)`. -/
theorem cell_key_rank_pos [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} {t : List (CellRow q Kfp)}
    (hrows : ∀ c ∈ t, RowOK z c) {c' : CellRow q Kfp} (hc' : c' ∈ t) : ¬ (c'.b0.hi = 0 ∧ c'.b0.lo = 0) := by
  have := rowOK_mu hq (hrows c' hc')
  unfold CellRowB0.mu CellRowB0.muL CellRowB0.muR at this
  omega

/-- A two-provider accepted table with atom-root external providers is `TreeOK` at `leaf2`. -/
theorem treeOK_leaf2 [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} {t : List (CellRow q Kfp)}
    {E : Noun → FP Kfp} (hE : InlineAtoms q z E)
    {vp : List (VKey Kfp)} {ext : ℕ → Option Noun} (h : TableAccepts2 z t vp) (hvp : AtomLeaves E vp ext) :
    TreeOK z E t (leaf2 q ext) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  refine ⟨h.serial, h.rows, fun c hc s => ?_⟩
  have hok := h.rows c hc
  cases hw : c.b0.wS s with
  | false =>
    have hatom : c.fpS s = FP.atomFP z (algebraMap (ZMod q) Kfp (c.b0.aS s)) ∧ c.b0.loS s = 0 ∧
        c.b0.hiS s = 0 := by
      cases s
      · exact hok.atomL hw
      · exact hok.atomR hw
    obtain ⟨hfa, hlo, hhi⟩ := hatom
    refine Or.inl ⟨.atom (c.b0.aS s).val, by simp [leaf2, hw], by rw [hfa, hE], ?_⟩
    simp [Noun.leaves, CellRowB0.muS, hlo, hhi]
  | true =>
    by_cases h0 : c.b0.hiS s = 0 ∧ c.b0.loS s = 0
    · -- F1: rank `(0, 0)` is never a cell row's key, so the external provider serves it.
      rcases h.served c hc s hw with ⟨c', hc', -, hhi, hlo, -⟩ | hv
      · exact absurd ⟨hhi ▸ h0.1, hlo ▸ h0.2⟩ (cell_key_rank_pos hq h.rows hc')
      · obtain ⟨-, -, v, hext, hfp⟩ := hvp _ hv
        refine Or.inl ⟨.atom v, by simp [leaf2, hw, h0, hext], hfp, ?_⟩
        simp [Noun.leaves, CellRowB0.muS, h0.1, h0.2]
    · rcases h.served c hc s hw with ⟨c', hc', hfp, hhi, hlo, hid⟩ | hv
      · exact Or.inr ⟨by simp [leaf2, hw, h0], c', hc', hfp, hhi, hlo, hid⟩
      · obtain ⟨h1, h2, -⟩ := hvp _ hv
        exact absurd ⟨h1, h2⟩ h0

/-- The decoded noun at serial `i` under the two-provider rule (fuel `Λ_chip`). -/
def preZNounOfTable2 (t : List (CellRowB0 q)) (ext : ℕ → Option Noun) (i : ℕ) : Option Noun :=
  decodeTree t (leaf2 q ext) fuelChip i

/-- **`row_genuine2` — the two-provider `row_genuine`.**  On a two-provider accepted table whose external
providers are atom roots: every row decodes to `[L R]` with `p = enc [L R]`, `l = enc L`, `r = enc R`; a
weighted rank-`(0, 0)` child is the atom `ext idx` of its atom-table serial; any other weighted child is the
decoded noun of its cell serial; a zero-weight child is its inline atom. -/
theorem row_genuine2 [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} {E : Noun → FP Kfp}
    (hcons : ∀ a b, E (.cell a b) = FP.cons z (E a) (E b)) (hE : InlineAtoms q z E)
    {t : List (CellRow q Kfp)} {vp : List (VKey Kfp)} {ext : ℕ → Option Noun}
    (h : TableAccepts2 z t vp) (hvp : AtomLeaves E vp ext) {c : CellRow q Kfp} (hc : c ∈ t) :
    ∃ L R, preZNounOfTable2 (t.map (·.b0)) ext c.b0.idx = some (.cell L R) ∧
      c.p = E (.cell L R) ∧ c.l = E L ∧ c.r = E R ∧
      (∀ s, c.b0.wS s = true → c.b0.hiS s = 0 ∧ c.b0.loS s = 0 →
        ext (c.b0.idS s) = some (if s = .L then L else R) ∧ ∃ v, ext (c.b0.idS s) = some (.atom v)) ∧
      (∀ s, c.b0.wS s = true → ¬ (c.b0.hiS s = 0 ∧ c.b0.loS s = 0) →
        preZNounOfTable2 (t.map (·.b0)) ext (c.b0.idS s) = some (if s = .L then L else R)) ∧
      (c.b0.wL = false → L = .atom c.b0.aL.val) ∧ (c.b0.wR = false → R = .atom c.b0.aR.val) := by
  have hT := treeOK_leaf2 hq hE h hvp
  have hlt := rowOK_mu_lt (h.rows c hc)
  obtain ⟨L, R, hd, hL, hR, hl, hr, hp, -⟩ := decodeTree_sound hq hcons hT _ c hc rfl fuelChip hlt
  have hside : ∀ s, childT (t.map (·.b0)) (leaf2 q ext) (fuelChip - 1) c.b0 s =
      some (if s = .L then L else R) := by
    intro s; cases s
    · simpa using hL
    · simpa using hR
  refine ⟨L, R, hd, hp, hl, hr, ?_, ?_, ?_, ?_⟩
  · intro s hw h0
    have hs := hside s
    unfold childT leaf2 at hs
    simp only [hw, h0, and_self, if_true] at hs
    refine ⟨hs, ?_⟩
    rcases h.served c hc s hw with ⟨c', hc', -, hhi, hlo, -⟩ | hv
    · exact absurd ⟨hhi ▸ h0.1, hlo ▸ h0.2⟩ (cell_key_rank_pos hq h.rows hc')
    · obtain ⟨-, -, v, hext, -⟩ := hvp _ hv
      exact ⟨v, hext⟩
  · intro s hw h0
    have hs := hside s
    unfold childT leaf2 at hs
    simp only [hw, h0, if_false, if_true] at hs
    exact decodeTree_mono _ _ _ _ _ _ (Nat.sub_le _ _) hs
  · intro hw
    have hs := hside .L
    unfold childT leaf2 at hs
    simp [CellRowB0.wS, CellRowB0.aS, hw] at hs
    exact hs.symm
  · intro hw
    have hs := hside .R
    unfold childT leaf2 at hs
    simp [CellRowB0.wS, CellRowB0.aS, hw] at hs
    exact hs.symm


/-! ## 4. The wire kind `k = w + kb` and the claim records on both tables -/

/-- A wire handle `(k, v)`: `k = 0` small atom `v`, `k = 1` cell serial, `k = 2` big atom (atom-table serial). -/
abbrev KHandle := ℕ × ℕ

/-- **`denK`**: `(0, v) ↦ atom v`, `(1, i) ↦` the two-provider decode of cell serial `i`, `(2, i) ↦ ext i`. -/
def denK (t : List (CellRowB0 q)) (ext : ℕ → Option Noun) : KHandle → Option Noun
  | (0, v) => some (.atom v)
  | (1, i) => preZNounOfTable2 t ext i
  | (2, i) => ext i
  | _ => none

/-- The wire kind of a child: `w + kb` with `kb = 1 ⇔ (w = 1 ∧ rank = (0, 0))` (`CellTwinK.sideGates_kind`). -/
def kindS (c : CellRowB0 q) (s : Side) : ℕ :=
  if c.wS s then (if c.hiS s = 0 ∧ c.loS s = 0 then 2 else 1) else 0

/-- The wire handle of a child. -/
def hK (c : CellRowB0 q) (s : Side) : KHandle := (kindS c s, if c.wS s then c.idS s else (c.aS s).val)

/-- **The export record at the wire kind**: `(idx, hK L, hK R)` (the 1-entry edit of `keyH`'s kinds). -/
def exportRecK (c : CellRowB0 q) : ℕ × KHandle × KHandle := (c.idx, hK c .L, hK c .R)

/-- **`exportRecK_grounded`** (the table form of `exportH_genuine` at `k = w + kb`): on a two-provider accepted
table with atom-root external keys, a row's export record is grounded — `denK (1, idx) = [L R]` with
`denK (hK L) = L`, `denK (hK R) = R`, whichever of the three kinds each child has. -/
theorem exportRecK_grounded [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} {E : Noun → FP Kfp}
    (hcons : ∀ a b, E (.cell a b) = FP.cons z (E a) (E b)) (hE : InlineAtoms q z E)
    {t : List (CellRow q Kfp)} {vp : List (VKey Kfp)} {ext : ℕ → Option Noun}
    (h : TableAccepts2 z t vp) (hvp : AtomLeaves E vp ext) {c : CellRow q Kfp} (hc : c ∈ t) :
    ∃ L R, denK (t.map (·.b0)) ext (1, (exportRecK c.b0).1) = some (.cell L R) ∧
      denK (t.map (·.b0)) ext (exportRecK c.b0).2.1 = some L ∧
      denK (t.map (·.b0)) ext (exportRecK c.b0).2.2 = some R := by
  obtain ⟨L, R, hd, -, -, -, h0, h1, haL, haR⟩ := row_genuine2 hq hcons hE h hvp hc
  have side : ∀ s, denK (t.map (·.b0)) ext (hK c.b0 s) = some (if s = .L then L else R) := by
    intro s
    unfold hK kindS
    cases hw : c.b0.wS s with
    | true =>
      by_cases hr : c.b0.hiS s = 0 ∧ c.b0.loS s = 0
      · simp only [hr, and_self, if_true, denK]; exact (h0 s hw hr).1
      · simp only [hr, if_false, if_true, denK]; exact h1 s hw hr
    | false =>
      cases s
      · simp only [denK, if_true]
        exact congrArg some (haL hw).symm
      · simp only [denK]
        exact congrArg some (haR hw).symm
  refine ⟨L, R, hd, ?_, ?_⟩
  · have := side .L; simpa [exportRecK] using this
  · have := side .R; simpa [exportRecK] using this

/-- The decoded nouns of a two-provider table. -/
def decodedNouns2 (t : List (CellRowB0 q)) (ext : ℕ → Option Noun) : List Noun :=
  (List.range t.length).filterMap (preZNounOfTable2 t ext)

theorem claimK_genuine_cell [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} {E : Noun → FP Kfp}
    (hcons : ∀ a b, E (.cell a b) = FP.cons z (E a) (E b)) (hE : InlineAtoms q z E)
    {t : List (CellRow q Kfp)} {vp : List (VKey Kfp)} {ext : ℕ → Option Noun}
    (h : TableAccepts2 z t vp) (hvp : AtomLeaves E vp ext) {x : Noun}
    (hinj : ∀ d ∈ decodedNouns2 (t.map (·.b0)) ext, E x = E d → x = d) {hi lo idx : ℕ}
    (hprov : ∃ c ∈ t, (E x, hi, lo, idx) = (c.p, c.b0.hi, c.b0.lo, c.b0.idx)) :
    denK (t.map (·.b0)) ext (1, idx) = some x := by
  obtain ⟨c, hc, heq⟩ := hprov
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hfp, -, -, hidx⟩ := heq
  obtain ⟨L, R, hdec, hp, -⟩ := row_genuine2 hq hcons hE h hvp hc
  have hmem : Noun.cell L R ∈ decodedNouns2 (t.map (·.b0)) ext := by
    refine List.mem_filterMap.mpr ⟨c.b0.idx, ?_, hdec⟩
    have hs := serial_lookup h.serial (List.mem_map_of_mem hc)
    exact List.mem_range.mpr (List.getElem?_eq_some_iff.mp hs).1
  have hx := hinj _ hmem (by rw [hfp]; exact hp)
  rw [denK, hidx, hx]; exact hdec

/-- **`claimK_genuine` on the atom table** (kind `2`): a claim record `(E x, 0, 0, idx)` provided by an atom
root (an external key) gives `denK (2, idx) = x`, under the census conclusion on atoms `hinjA`. -/
theorem claimK_genuine_atom {E : Noun → FP Kfp} {vp : List (VKey Kfp)} {ext : ℕ → Option Noun}
    (hvp : AtomLeaves E vp ext) (t : List (CellRowB0 q)) {x : Noun}
    (hinjA : ∀ v, E x = E (.atom v) → x = .atom v) {idx : ℕ}
    (hprov : (E x, 0, 0, idx) ∈ vp) :
    denK t ext (2, idx) = some x := by
  obtain ⟨-, -, v, hext, hfp⟩ := hvp _ hprov
  rw [denK, hext, hinjA v hfp]

end Sound

end Nock.NockVMROM.Thm54.VclL
