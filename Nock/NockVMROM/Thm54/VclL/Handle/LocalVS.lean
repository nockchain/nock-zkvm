/-
  Nock/NockVMROM/Thm54/VclL/Handle/LocalVS.lean

  Additive; pure noun logic,
  no chip, no coin.

  * `RowVS` — a decoded compute row: its one-hot state and its twelve handles (`ChipH.hd 0.. 11`);
    `kids` — the child labels `(s, f, e)` per state, exactly `ChipH.children`.
  * `RowSem q D r` — what the chip's gates and its SERVED, GENUINE lookups say about a row, stated on
    a denotation `D : VHandle → Option Noun` (instantiated by `denH` of the decoded cell table):
    L1 `f = [f_h f_t]` every row; per state the opcode's local facts (OP0/OP9 axis reads through the
    walk records, OP3 `?`, OP4 `+` mod `q` on atoms, OP5 (item 6), OP6 hosted branch, OP8 built
    subject, cons).  **OP5 (item 6)**: "=" only from handle EQUALITY; "≠" only from a kind difference,
    an atom-value difference, or the first-difference walk pair at a common axis (`Op5Sem`) — never
    from serial inequality.
  * `defined_all` — every row's subject and evaluation denote (top-down subjects, bottom-up results)
    once the root subject does.
  * **`local_all`** — `LocalOK q (skel D ∘ rw) u` at every node of a tree whose nodes satisfy
    `RowSem` and whose children carry the parent's `kids` labels; **`holdsF_of_rowsVS`** — the claim
    holds when the root's `(s, f, e)` denote it (through `genuine_of_local` / `holdsF_of_local`).
  * **Item 8 (tag-free labels)**: the tree links children by `(s, f, e)` only; each node's state is its
    own row's, and `state_of_formula` shows it is a function of the denoted formula (`FormulaShape`
    determines the state), so no state tag is needed in the walk label.
-/
import Nock.NockVMROM.Thm54.P8Core.SVFrameG.Ground
import Nock.NockVMROM.Thm54.VclL.Handle.Serial

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.LocalVS

open Nock Nock.Walk Nock.ComputeTable
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SVGenuineF (HoldsF GenuineSkelF RowOutputF)
open Nock.NockVMROM.Thm54.ComputedWindow (FormulaShape KidInputs op0Axis op9Axis condBit hd tl)
open Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL.Handle (VHandle)

/-! ## 1. Rows, child labels, the row semantics -/

/-- **A decoded VS compute row**: its state and its twelve handles (`ChipH.hd 0.. 11`). -/
structure RowVS where
  st : State
  s : VHandle
  f : VHandle
  e : VHandle
  sf1 : VHandle
  sf2 : VHandle
  fh : VHandle
  ft : VHandle
  fth : VHandle
  ftt : VHandle
  ftth : VHandle
  fttt : VHandle
  m : VHandle

abbrev Trip := VHandle × VHandle × VHandle

/-- The walk label of a row: its `(s, f, e)` handles (no state tag). -/
def RowVS.trip (r : RowVS) : Trip := (r.s, r.f, r.e)

/-- **The child labels per state** (`ChipH.children`, EC table). -/
def kids (r : RowVS) : List Trip :=
  match r.st with
  | .s2 => [(r.s, r.fth, r.sf1), (r.s, r.ftt, r.sf2), (r.sf1, r.sf2, r.e)]
  | .s3 => [(r.s, r.ft, r.sf1)]
  | .s4 => [(r.s, r.ft, r.sf1)]
  | .s5 => [(r.s, r.fth, r.sf1), (r.s, r.ftt, r.sf2)]
  | .s6 => [(r.s, r.m, r.sf1), (r.s, r.fth, r.sf2)]
  | .s7 => [(r.sf2, r.ftt, r.sf1), (r.s, r.fth, r.sf2)]
  | .s8 => [(r.m, r.ftt, r.sf1), (r.s, r.fth, r.sf2)]
  | .s9 => [(r.s, r.ftt, r.sf1), (r.sf1, r.m, r.sf2)]
  | .cons => [(r.s, r.fh, r.sf1), (r.s, r.ft, r.sf2)]
  | _ => []

section Sem
variable (D : VHandle → Option Noun)

/-- A served cell-export record `(a, b, c)`: `D a = [D b, D c]`. -/
def Cell3 (a b c : VHandle) : Prop := ∃ A B, D a = some (.cell A B) ∧ D b = some A ∧ D c = some B

/-- Two handles certainly name different nouns: different kinds, or two atoms of different values
(the chip's `neGate`). -/
def Differ (a b : VHandle) : Prop := a.1 ≠ b.1 ∨ (a.1 = false ∧ b.1 = false ∧ a.2 ≠ b.2)

/-- **OP5 (item 6)**: "=" by handle equality; "≠" by `Differ` of the operands' results, or of the
first-difference leaves `f_tth`, `f_ttt` read by the walk at a common axis of both. -/
def Op5Sem (r : RowVS) : Prop :=
  (r.sf1 = r.sf2 ∧ r.e = (false, 0)) ∨
  (r.e = (false, 1) ∧
    (Differ r.sf1 r.sf2 ∨
     ∃ (ax : ℕ) (X1 X2 A1 A2 : Noun), D r.sf1 = some X1 ∧ D r.sf2 = some X2 ∧
       Noun.slot ax X1 = some A1 ∧ Noun.slot ax X2 = some A2 ∧ D r.ftth = some A1 ∧
       D r.fttt = some A2 ∧ Differ r.ftth r.fttt))

/-- **The row semantics on denotations** (what the gates and the served, genuine lookups give). -/
def RowSem (q : ℕ) (r : RowVS) : Prop :=
  Cell3 D r.f r.fh r.ft ∧
  match r.st with
  | .s0 => r.fh = (false, 0) ∧ ∃ ax : ℕ, r.ft = (false, ax) ∧
      ((ax = 1 ∧ r.e = r.s) ∨ ∃ S E, D r.s = some S ∧ D r.e = some E ∧ Noun.slot ax S = some E)
  | .s1 => r.fh = (false, 1) ∧ r.e = r.ft
  | .s2 => r.fh = (false, 2) ∧ Cell3 D r.ft r.fth r.ftt
  | .s3 => r.fh = (false, 3) ∧ ∃ N, D r.sf1 = some N ∧ D r.e = some (Noun.wut N)
  | .s4 => r.fh = (false, 4) ∧ ∃ n : ℕ, D r.sf1 = some (.atom n) ∧ D r.e = some (.atom ((n + 1) % q))
  | .s5 => r.fh = (false, 5) ∧ Cell3 D r.ft r.fth r.ftt ∧ Op5Sem D r
  | .s6 => r.fh = (false, 6) ∧ Cell3 D r.ft r.fth r.ftt ∧ Cell3 D r.ftt r.ftth r.fttt ∧
      ∃ c : ℕ, (c = 0 ∨ c = 1) ∧ r.sf2 = (false, c) ∧ r.m = (if c = 0 then r.ftth else r.fttt) ∧
        r.e = r.sf1
  | .s7 => r.fh = (false, 7) ∧ Cell3 D r.ft r.fth r.ftt ∧ r.e = r.sf1
  | .s8 => r.fh = (false, 8) ∧ Cell3 D r.ft r.fth r.ftt ∧ Cell3 D r.m r.sf2 r.s ∧ r.e = r.sf1
  | .s9 => r.fh = (false, 9) ∧ Cell3 D r.ft r.fth r.ftt ∧ (∃ ax : ℕ, r.fth = (false, ax) ∧
      ((ax = 1 ∧ r.m = r.sf1) ∨ ∃ C A, D r.sf1 = some C ∧ D r.m = some A ∧ Noun.slot ax C = some A)) ∧
      r.e = r.sf2
  | .cons => r.fh.1 = true ∧ Cell3 D r.e r.sf1 r.sf2

/-- The noun a handle names (junk `atom 0` where it names none; only read where it does). -/
def nd (h : VHandle) : Noun := (D h).getD (.atom 0)

/-- **The denotation of a row** (`decomposition` / `subformula` / `memoryRecord` junk: `GenuineSkelF`
reads only state, subject, formula, evaluation). -/
def skel (r : RowVS) : ComputeRowSkeleton where
  state := r.st
  subject := nd D r.s
  formula := nd D r.f
  evaluation := nd D r.e
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 0⟩

end Sem

/-! ## 2. Local lemmas -/

section Local
variable {D : VHandle → Option Noun}

theorem nd_of {h : VHandle} {X : Noun} (hX : D h = some X) : nd D h = X := by simp [nd, hX]

/-- What `D` must satisfy (as `denH` does): atoms denote themselves, serials denote cells. -/
structure DenOK (D : VHandle → Option Noun) : Prop where
  atom : ∀ v, D (false, v) = some (.atom v)
  cell : ∀ i X, D (true, i) = some X → ∃ a b, X = .cell a b

theorem differ_ne (hD : DenOK D) {a b : VHandle} {X Y : Noun} (hX : D a = some X) (hY : D b = some Y)
    (h : Differ a b) : X ≠ Y := by
  obtain ⟨ka, va⟩ := a
  obtain ⟨kb, vb⟩ := b
  rcases h with h | ⟨h1, h2, h3⟩
  · intro hXY
    subst hXY
    cases ka <;> cases kb
    · exact h rfl
    · rw [hD.atom] at hX
      obtain ⟨p, q, hpq⟩ := hD.cell _ _ hY
      rw [← Option.some.inj hX] at hpq
      cases hpq
    · rw [hD.atom] at hY
      obtain ⟨p, q, hpq⟩ := hD.cell _ _ hX
      rw [← Option.some.inj hY] at hpq
      cases hpq
    · exact h rfl
  · simp only at h1 h2 h3
    subst h1; subst h2
    rw [hD.atom] at hX hY
    rw [← Option.some.inj hX, ← Option.some.inj hY]
    intro hc
    exact h3 (Noun.atom.inj hc)

theorem slot_ne {ax : ℕ} {X1 X2 A1 A2 : Noun} (h1 : Noun.slot ax X1 = some A1)
    (h2 : Noun.slot ax X2 = some A2) (hne : A1 ≠ A2) : X1 ≠ X2 := by
  intro h
  subst h
  rw [h1] at h2
  exact hne (Option.some.inj h2)

theorem cell3_of {a b c : VHandle} (h : Cell3 D a b c) :
    nd D a = .cell (nd D b) (nd D c) := by
  obtain ⟨A, B, ha, hb, hc⟩ := h
  rw [nd_of ha, nd_of hb, nd_of hc]

theorem atom_nd (hD : DenOK D) (v : ℕ) : nd D (false, v) = .atom v := nd_of (hD.atom v)

theorem ne_none_of {h : VHandle} {X : Noun} (hX : D h = some X) : D h ≠ none := by simp [hX]

theorem cell3_ne {a b c : VHandle} (h : Cell3 D a b c) : D a ≠ none ∧ D b ≠ none ∧ D c ≠ none := by
  obtain ⟨A, B, ha, hb, hc⟩ := h
  exact ⟨ne_none_of ha, ne_none_of hb, ne_none_of hc⟩

/-- **The per-row definedness step**: if the row's subject denotes and every child whose subject
denotes has a denoting result, then every child subject and the row's result denote. -/
theorem defined_step {q : ℕ} (hD : DenOK D) (r : RowVS) (hsem : RowSem D q r) (hs : D r.s ≠ none)
    (hch : ∀ x ∈ kids r, D x.1 ≠ none → D x.2.2 ≠ none) :
    (∀ x ∈ kids r, D x.1 ≠ none) ∧ D r.e ≠ none := by
  obtain ⟨hf3, hrest⟩ := hsem
  cases hst : r.st <;> rw [hst] at hrest <;> simp only [kids, hst] at hch ⊢ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      IsEmpty.forall_iff, implies_true, true_and] at hch ⊢
  · obtain ⟨-, ax, -, h | ⟨S, E, -, hE, -⟩⟩ := hrest
    · exact h.2 ▸ hs
    · exact ne_none_of hE
  · rw [hrest.2]; exact (cell3_ne hf3).2.2
  · have h1 := hch.1 hs
    exact ⟨⟨hs, hs, h1⟩, hch.2.2 h1⟩
  · obtain ⟨-, N, -, hN⟩ := hrest; exact ⟨hs, ne_none_of hN⟩
  · obtain ⟨-, n, -, hN⟩ := hrest; exact ⟨hs, ne_none_of hN⟩
  · refine ⟨⟨hs, hs⟩, ?_⟩
    obtain ⟨-, -, ⟨-, he⟩ | ⟨he, -⟩⟩ := hrest <;> rw [he, hD.atom] <;> simp
  · obtain ⟨-, -, -, c, -, -, -, he⟩ := hrest
    exact ⟨⟨hs, hs⟩, he ▸ hch.1 hs⟩
  · obtain ⟨-, -, he⟩ := hrest
    have h2 := hch.2 hs
    exact ⟨⟨h2, hs⟩, he ▸ hch.1 h2⟩
  · obtain ⟨-, -, hm, he⟩ := hrest
    have hm' := (cell3_ne hm).1
    exact ⟨⟨hm', hs⟩, he ▸ hch.1 hm'⟩
  · obtain ⟨-, -, -, he⟩ := hrest
    have h1 := hch.1 hs
    exact ⟨⟨hs, h1⟩, he ▸ hch.2 h1⟩
  · obtain ⟨-, he⟩ := hrest
    exact ⟨⟨hs, hs⟩, (cell3_ne he).1⟩

theorem slot_one (X : Noun) : Noun.slot 1 X = some X := by simp [Noun.slot]

/-- **The local step** (item 5 per state, item 6 at OP5): a row satisfying `RowSem`, whose children
carry its `kids` labels and have denoting results, obeys `FormulaShape`, `KidInputs` and
`RowOutputF q` on denotations. -/
theorem local_step {q : ℕ} (hD : DenOK D) (r : RowVS) (hsem : RowSem D q r) (ks : List RowVS)
    (hk : ks.map RowVS.trip = kids r) (hdef : ∀ k ∈ ks, D k.e ≠ none) :
    FormulaShape r.st (nd D r.f) ∧ KidInputs r.st (nd D r.s) (nd D r.f) (ks.map (skel D)) ∧
      RowOutputF q r.st (nd D r.s) (nd D r.f) (ks.map (skel D)) (nd D r.e) := by
  obtain ⟨hf3, hrest⟩ := hsem
  have hF := cell3_of hf3
  cases hst : r.st <;> rw [hst] at hrest <;> simp only [kids, hst] at hk <;>
    rcases ks with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, ks⟩⟩⟩⟩ <;>
    simp only [List.map_nil, List.map_cons, List.cons.injEq, reduceCtorEq, and_false, false_and,
      List.nil_eq, List.cons_ne_nil, RowVS.trip, Prod.mk.injEq, and_true] at hk
  · -- s0
    obtain ⟨hfh, ax, hft, hcase⟩ := hrest
    rw [hfh, atom_nd hD, hft, atom_nd hD] at hF
    refine ⟨⟨ax, hF⟩, rfl, ?_⟩
    simp only [RowOutputF, hF, op0Axis]
    rcases hcase with ⟨rfl, he⟩ | ⟨S, E, hS, hE, hsl⟩
    · rw [he]; exact slot_one _
    · rw [nd_of hS, nd_of hE]; exact hsl
  · -- s1
    obtain ⟨hfh, he⟩ := hrest
    rw [hfh, atom_nd hD] at hF
    refine ⟨⟨_, hF⟩, rfl, ?_⟩
    simp only [RowOutputF, hF, he, tl, StrategyOfTraces.nounTail]
  · -- s2
    obtain ⟨⟨h0s, h0f, h0e⟩, ⟨h1s, h1f, h1e⟩, ⟨h2s, h2f, h2e⟩⟩ := hk
    obtain ⟨hfh, ht3⟩ := hrest
    have hT := cell3_of ht3
    rw [hfh, atom_nd hD, hT] at hF
    refine ⟨⟨_, _, hF⟩, ?_, ?_⟩
    · simp only [KidInputs, List.map_cons, List.map_nil, skel, hF, h0s, h0f, h0e, h1s, h1f, h1e, h2s, h2f, h2e, hd, tl,
        StrategyOfTraces.nounHead, StrategyOfTraces.nounTail, and_self]
    · simp only [RowOutputF, List.map_cons, List.map_nil, skel, h2e]
  · -- s3
    obtain ⟨h0s, h0f, h0e⟩ := hk
    obtain ⟨hfh, N, hN, he⟩ := hrest
    rw [hfh, atom_nd hD] at hF
    refine ⟨⟨_, hF⟩, ?_, ?_⟩
    · simp only [KidInputs, List.map_cons, List.map_nil, skel, hF, h0s, h0f, tl, StrategyOfTraces.nounTail, and_self]
    · simp only [RowOutputF, List.map_cons, List.map_nil, skel, h0e, nd_of hN, nd_of he]
  · -- s4
    obtain ⟨h0s, h0f, h0e⟩ := hk
    obtain ⟨hfh, n, hN, he⟩ := hrest
    rw [hfh, atom_nd hD] at hF
    refine ⟨⟨_, hF⟩, ?_, ?_⟩
    · simp only [KidInputs, List.map_cons, List.map_nil, skel, hF, h0s, h0f, tl, StrategyOfTraces.nounTail, and_self]
    · simp only [RowOutputF, List.map_cons, List.map_nil, skel, h0e, nd_of hN, nd_of he, FieldEmbedding.lusFBy]
  · -- s5 (item 6)
    obtain ⟨⟨h0s, h0f, h0e⟩, ⟨h1s, h1f, h1e⟩⟩ := hk
    obtain ⟨hfh, ht3, hop⟩ := hrest
    have hT := cell3_of ht3
    rw [hfh, atom_nd hD, hT] at hF
    refine ⟨⟨_, _, hF⟩, ?_, ?_⟩
    · simp only [KidInputs, List.map_cons, List.map_nil, skel, hF, h0s, h0f, h1s, h1f, hd, tl,
        StrategyOfTraces.nounHead, StrategyOfTraces.nounTail, and_self]
    · simp only [RowOutputF, List.map_cons, List.map_nil, skel, h0e, h1e]
      rcases hop with ⟨heq, he⟩ | ⟨he, hne⟩
      · rw [heq, he, atom_nd hD]; simp [Noun.tis]
      · have d1 := hdef k0 (List.mem_cons_self ..)
        have d2 := hdef k1 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        rw [h0e] at d1; rw [h1e] at d2
        obtain ⟨X1, hX1⟩ := Option.ne_none_iff_exists'.mp d1
        obtain ⟨X2, hX2⟩ := Option.ne_none_iff_exists'.mp d2
        have hX : X1 ≠ X2 := by
          rcases hne with hd' | ⟨ax, Y1, Y2, A1, A2, hY1, hY2, hs1, hs2, hA1, hA2, hdA⟩
          · exact differ_ne hD hX1 hX2 hd'
          · rw [hX1] at hY1; rw [hX2] at hY2
            cases Option.some.inj hY1; cases Option.some.inj hY2
            exact slot_ne hs1 hs2 (differ_ne hD hA1 hA2 hdA)
        rw [he, atom_nd hD, nd_of hX1, nd_of hX2]
        simp [Noun.tis, hX]
  · -- s6
    obtain ⟨⟨h0s, h0f, h0e⟩, ⟨h1s, h1f, h1e⟩⟩ := hk
    obtain ⟨hfh, ht3, htt3, c, hc, hsf2, hm, he⟩ := hrest
    have hT := cell3_of ht3
    have hTT := cell3_of htt3
    rw [hTT] at hT
    rw [hfh, atom_nd hD, hT] at hF
    refine ⟨⟨_, _, _, hF⟩, ?_, ?_⟩
    · simp only [KidInputs, List.map_cons, List.map_nil, skel, hF, h0s, h0f, h1s, h1f, h1e, hsf2, atom_nd hD, condBit, hm, hd,
        tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail, true_and]
      rcases hc with rfl | rfl <;> simp
    · simp only [RowOutputF, List.map_cons, List.map_nil, skel, h0e, h1e, hsf2, atom_nd hD, he]
      rcases hc with rfl | rfl <;> simp
  · -- s7
    obtain ⟨⟨h0s, h0f, h0e⟩, ⟨h1s, h1f, h1e⟩⟩ := hk
    obtain ⟨hfh, ht3, he⟩ := hrest
    have hT := cell3_of ht3
    rw [hfh, atom_nd hD, hT] at hF
    refine ⟨⟨_, _, hF⟩, ?_, ?_⟩
    · simp only [KidInputs, List.map_cons, List.map_nil, skel, hF, h0s, h0f, h1s, h1f, h1e, hd, tl,
        StrategyOfTraces.nounHead, StrategyOfTraces.nounTail, and_self]
    · simp only [RowOutputF, List.map_cons, List.map_nil, skel, h0e, he]
  · -- s8
    obtain ⟨⟨h0s, h0f, h0e⟩, ⟨h1s, h1f, h1e⟩⟩ := hk
    obtain ⟨hfh, ht3, hm3, he⟩ := hrest
    have hT := cell3_of ht3
    have hM := cell3_of hm3
    rw [hfh, atom_nd hD, hT] at hF
    refine ⟨⟨_, _, hF⟩, ?_, ?_⟩
    · simp only [KidInputs, List.map_cons, List.map_nil, skel, hF, h0s, h0f, h1s, h1f, h1e, hM, hd, tl,
        StrategyOfTraces.nounHead, StrategyOfTraces.nounTail, and_self]
    · simp only [RowOutputF, List.map_cons, List.map_nil, skel, h0e, he]
  · -- s9
    obtain ⟨⟨h0s, h0f, h0e⟩, ⟨h1s, h1f, h1e⟩⟩ := hk
    obtain ⟨hfh, ht3, ⟨ax, hth, hcase⟩, he⟩ := hrest
    have hT := cell3_of ht3
    rw [hth, atom_nd hD] at hT
    rw [hfh, atom_nd hD, hT] at hF
    refine ⟨⟨_, _, hF⟩, ?_, ?_⟩
    · simp only [KidInputs, List.map_cons, List.map_nil, skel, hF, h0s, h0f, h0e, h1s, h1f, op9Axis, tl,
        StrategyOfTraces.nounTail, true_and]
      rcases hcase with ⟨rfl, hm⟩ | ⟨C, A, hC, hA, hsl⟩
      · rw [hm]; exact slot_one _
      · rw [nd_of hC, nd_of hA]; exact hsl
    · simp only [RowOutputF, List.map_cons, List.map_nil, skel, h1e, he]
  · -- cons
    obtain ⟨⟨h0s, h0f, h0e⟩, ⟨h1s, h1f, h1e⟩⟩ := hk
    obtain ⟨hk1, he3⟩ := hrest
    have hE := cell3_of he3
    obtain ⟨a, b, hab⟩ : ∃ a b, nd D r.fh = .cell a b := by
      obtain ⟨Fh, Ft, -, hfhD, -⟩ := hf3
      have hfe : r.fh = (true, r.fh.2) := Prod.ext hk1 rfl
      rw [hfe] at hfhD
      obtain ⟨a, b, rfl⟩ := hD.cell _ _ hfhD
      exact ⟨a, b, by rw [hfe]; exact nd_of hfhD⟩
    refine ⟨⟨a, b, _, by rw [hF, hab]⟩, ?_, ?_⟩
    · simp only [KidInputs, List.map_cons, List.map_nil, skel, hF, h0s, h0f, h1s, h1f, hd, tl,
        StrategyOfTraces.nounHead, StrategyOfTraces.nounTail, and_self]
    · simp only [RowOutputF, List.map_cons, List.map_nil, skel, h0e, h1e, hE]

end Local

/-! ## 3. The tree -/

section Tree
variable {D : VHandle → Option Noun} {L : Type} (rw : L → RowVS)

theorem inTree_trans {t u w : NTree L} (h1 : InTree t u) (h2 : InTree u w) : InTree t w := by
  induction h1 with
  | here => exact h2
  | sub hs _ ih => exact InTree.sub hs (ih h2)

/-- **The tree hypotheses**: every node satisfies `RowSem`, and its children carry exactly its
`kids` labels (`(s, f, e)` only: tag-free). -/
structure RowsOK (q : ℕ) (D : VHandle → Option Noun) (t : NTree L) : Prop where
  sem : ∀ u, InTree t u → RowSem D q (rw u.label)
  link : ∀ u, InTree t u → u.children.map (fun c => (rw c.label).trip) = kids (rw u.label)

theorem RowsOK.sub {q : ℕ} {t : NTree L} (h : RowsOK rw q D t) {c : NTree L} (hc : c ∈ t.children) :
    RowsOK rw q D c :=
  ⟨fun u hu => h.sem u (InTree.sub hc hu), fun u hu => h.link u (InTree.sub hc hu)⟩

/-- **Definedness**: once the root subject denotes, every node's subject and result denote. -/
theorem defined_tree {q : ℕ} (hD : DenOK D) : ∀ t : NTree L, RowsOK rw q D t →
    D (rw t.label).s ≠ none → ∀ u, InTree t u → D (rw u.label).s ≠ none ∧ D (rw u.label).e ≠ none
  | .node l cs, h, hs => by
    have ih : ∀ c ∈ cs, D (rw c.label).s ≠ none →
        ∀ u, InTree c u → D (rw u.label).s ≠ none ∧ D (rw u.label).e ≠ none :=
      fun c hc => defined_tree hD c (h.sub rw (by simpa [NTree.children] using hc))
    have hl := h.link _ (InTree.here _)
    have hsem := h.sem _ (InTree.here _)
    simp only [NTree.label, NTree.children] at hl hsem hs
    obtain ⟨hk, he⟩ := defined_step hD (rw l) hsem hs (by
      rw [← hl]
      intro x hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact fun h1 => (ih c hc h1 c (InTree.here _)).2)
    intro u hu
    cases hu with
    | here => exact ⟨hs, he⟩
    | sub hc hu' =>
      refine ih _ hc ?_ u hu'
      exact hk _ (by rw [← hl]; exact List.mem_map_of_mem hc)

/-- **Item 5 (local half), with items 6 and 8: `LocalOK` at every node.** -/
theorem local_all {q : ℕ} (hD : DenOK D) (t : NTree L) (h : RowsOK rw q D t)
    (hs : D (rw t.label).s ≠ none) :
    ∀ u, InTree t u → LocalOK q (fun l => skel D (rw l)) u := by
  intro u hu
  have hk : (u.children.map (fun c => rw c.label)).map RowVS.trip = kids (rw u.label) := by
    rw [List.map_map]; exact h.link u hu
  have hdef : ∀ k ∈ u.children.map (fun c => rw c.label), D k.e ≠ none := by
    intro k hk'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk'
    exact (defined_tree rw hD t h hs c (inTree_trans hu (InTree.sub hc (InTree.here _)))).2
  have key := local_step hD (rw u.label) (h.sem u hu) _ hk hdef
  rw [List.map_map] at key
  exact key

/-- **The VS claim from a grounded row tree**: if the root's `(s, f, e)` handles denote the claim's
nouns, the claim holds in the field language. -/
theorem holdsF_of_rowsVS {q : ℕ} (hD : DenOK D) (t : NTree L) (h : RowsOK rw q D t)
    (x : P8PublicClaim) (hs : D (rw t.label).s = some x.subject)
    (hf : D (rw t.label).f = some x.formula) (he : D (rw t.label).e = some x.result) : HoldsF q x :=
  holdsF_of_local q (fun l => skel D (rw l)) t (local_all rw hD t h (by simp [hs])) x
    (nd_of hs) (nd_of hf) (nd_of he)

end Tree

/-! ## 4. Item 6 controls: serial inequality is not a difference -/

theorem serials_never_differ (i j : ℕ) : ¬ Differ (true, i) (true, j) := by
  simp [Differ]

/-- Positive control: kinds differ, and two distinct atom values, are differences. -/
theorem differ_controls : Differ (false, 3) (true, 3) ∧ Differ (false, 3) (false, 4) := by
  simp [Differ]

/-- **Negative control for `DenOK.cell`**: without "serials denote cells", a kind difference would
not certify noun inequality — a denotation sending `(true, 0)` to `atom 7` makes `(false, 7)` and
`(true, 0)` `Differ` while naming the same noun. -/
theorem differ_needs_cell_meaning :
    let D : VHandle → Option Noun := fun h => some (.atom (if h.1 then 7 else h.2))
    Differ (false, 7) (true, 0) ∧ D (false, 7) = D (true, 0) := by
  simp [Differ]

/-! ## 5. Item 8: the state is a function of the denoted formula -/

/-- **Tag-free labels (item 8)**: `FormulaShape` determines the state, so a row's state is fixed by
its own (denoted) formula and the walk label needs no state tag. -/
theorem state_of_formula {st1 st2 : State} {f : Noun} (h1 : FormulaShape st1 f)
    (h2 : FormulaShape st2 f) : st1 = st2 := by
  cases st1 <;> cases st2 <;> simp only [FormulaShape] at h1 h2 <;> first
    | rfl
    | (obtain ⟨_, rfl⟩ := h1; simp at h2)
    | (obtain ⟨_, _, rfl⟩ := h1; simp at h2)
    | (obtain ⟨_, _, _, rfl⟩ := h1; simp at h2)

/-- A row's denotation determines its state (from `local_step`'s `FormulaShape`). -/
theorem rowState_determined {D : VHandle → Option Noun} {q : ℕ} (hD : DenOK D) {r r' : RowVS}
    (h : RowSem D q r) (h' : RowSem D q r') (ks ks' : List RowVS) (hk : ks.map RowVS.trip = kids r)
    (hk' : ks'.map RowVS.trip = kids r') (hd : ∀ k ∈ ks, D k.e ≠ none) (hd' : ∀ k ∈ ks', D k.e ≠ none)
    (hf : nd D r.f = nd D r'.f) : r.st = r'.st :=
  state_of_formula (local_step hD r h ks hk hd).1 (hf ▸ (local_step hD r' h' ks' hk' hd').1)


end Nock.NockVMROM.Thm54.VclL.Handle.LocalVS
