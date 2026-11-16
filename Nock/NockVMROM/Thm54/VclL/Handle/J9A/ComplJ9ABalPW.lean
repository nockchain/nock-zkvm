/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalPW.lean

  **J-9 A L7: the walk side of `hGp`** (work in progress: partial).

  * `chainWalk_mem`, `slot_mem_cells`: a defined cell slot of a cell of a child-closed list is in the list.
  * `Tw_eq_Wp_of_root`: `Tw` at a read whose root is a cell of `D.cells` with a defined slot and `axis < p` is the
    read-indexed path weight `Wp` of `readRecH D.cells` (copy of the tail of `ComplJ8OfBalG.pSum_run`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalPAx
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ADataRec
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AReads
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfMem

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalPW

noncomputable section

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG (Wp Wp_eq Wp_third)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalPAx (Tw)
open Nock.Walk Nock.Edit Nock.Edit.GenX

/-! ## 1. Cells of a child-closed list are closed under slots -/

theorem chainWalk_mem {cells : List Noun} (hcl : ComplJ8Data.ClP cells []) :
    ∀ (bs : List Bool) (X Y : Noun), X ∈ cells → chainWalk X bs = some Y → (∃ c d, Y = .cell c d) →
      Y ∈ cells
  | [], X, Y, hX, h, _ => by
    have : X = Y := by simpa [chainWalk] using h
    subst this; exact hX
  | b :: bs, X, Y, hX, h, hY => by
    cases X with
    | atom a => simp [chainWalk] at h
    | cell l r =>
      have hc := hcl l r hX (by simp)
      simp only [chainWalk] at h
      have hZ : ∀ Z : Noun, chainWalk Z bs = some Y → (∀ x y, Z = .cell x y → Z ∈ cells) → Z ∈ cells := by
        intro Z hZ hcz
        cases Z with
        | atom a =>
          cases bs with
          | nil =>
            have : Noun.atom a = Y := by simpa [chainWalk] using hZ
            obtain ⟨c, d, hcd⟩ := hY
            rw [← this] at hcd; cases hcd
          | cons b' bs' => simp [chainWalk] at hZ
        | cell x y => exact hcz x y rfl
      have hmem : (if b then r else l) ∈ cells := by
        cases b
        · exact hZ _ h hc.1
        · exact hZ _ h hc.2
      exact chainWalk_mem hcl bs _ Y hmem h hY

/-- **A defined cell slot of a cell of a child-closed list is in the list.** -/
theorem slot_mem_cells {cells : List Noun} (hcl : ComplJ8Data.ClP cells []) {a : ℕ} (ha : 1 ≤ a) {X Y : Noun}
    (hX : X ∈ cells) (hs : Noun.slot a X = some Y) (hY : ∃ c d, Y = .cell c d) : Y ∈ cells := by
  rw [Nock.NockVMROM.Thm54.VclL.slot_eq_chainWalk a ha] at hs
  exact chainWalk_mem hcl _ X Y hX hs hY

/-! ## 2. `Tw` is `Wp` at a read with a well-placed root -/

section Bridge
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- **`Tw` is `Wp` at a read** whose root is a cell of the table with a defined slot of axis `< p`, at a record
whose handle map is the table's (`hidx`: the root's handle serial is its index). -/
theorem Tw_eq_Wp_of_root (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) (x : Noun × ℕ)
    (hmem : x.1 ∈ D.cells) (hidx : ((D.H x.1).2 : ℕ) = D.cells.idxOf x.1) (hlen : D.cells.length < p)
    (hax : x.2 < p) {ch : Noun} (hsl : Noun.slot x.2 x.1 = some ch) :
    Tw δ D.H χ x = Wp δ D χ (readRecH D.cells x) := by
  unfold Tw readRecH
  rw [Wp_third δ D χ _ _ _ (0, 0), Wp_eq δ D χ x.1 ch _ _ hmem rfl hlen hax hsl, hidx, hsl]
  rfl

end Bridge

/-! ## 3. Roots of the J-9 A reads lie in the cell table -/

section Roots
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen
open Nock.J9A.NounAx (top segAx segRd segAx_top segAx_next segRd_pos)

/-- `X` is an atom or a cell of the table. -/
def Gd (cells : List Noun) (X : Noun) : Prop := X.isCell = true → X ∈ cells

theorem gd_segX {cells : List Noun} (hcl : ComplJ8Data.ClP cells []) {n m : ℕ} {s : Noun} (hs : Gd cells s) :
    Gd cells (segX n m s) := by
  unfold Gd segX
  intro hY
  cases hsl : Noun.slot (segRd n m) s with
  | none => simp [hsl, Noun.isCell] at hY
  | some Y =>
    simp only [hsl, Option.getD_some] at hY ⊢
    have hY' : ∃ c d, Y = .cell c d := by
      cases Y with
      | atom _ => simp [Noun.isCell] at hY
      | cell c d => exact ⟨c, d, rfl⟩
    by_cases ha : 1 ≤ segRd n m
    · cases s with
      | atom v =>
        exfalso
        rcases (by omega : segRd n m = 1 ∨ 2 ≤ segRd n m) with h | h
        · rw [h] at hsl
          simp [Noun.slot] at hsl
          subst hsl
          obtain ⟨c, d, h⟩ := hY'
          cases h
        · rw [ComplJ8OfBalG.slot_atom_two h] at hsl; cases hsl
      | cell a b => exact slot_mem_cells hcl ha (hs rfl) hsl hY'
    · have h0 : segRd n m = 0 := by omega
      rw [h0] at hsl
      simp [Noun.slot] at hsl

/-- **The node classes of the J-9 A tree, with provenance of the segment and chain roots.** -/
def Q9 (R : Nock.Jet.Registry) (t : NTree SkelX) (cells : List Noun) (u : NTree LX9) : Prop :=
  (∃ v, InTree t v ∧ GenNode R v ∧ u = genX9T v) ∨
  (∃ v, ChainNode v ∧ chainAxis v.label.formula < 2 ^ 62 ∧ Gd cells v.label.subject ∧
      Gd cells v.label.evaluation ∧ u = liftT v) ∨
  (∃ n m s e new, n ≠ 0 ∧ m ≤ top n ∧ Noun.edit (segAx n m) new s = some e ∧ Gd cells s ∧ Gd cells e ∧
      u = segT n m s e) ∨
  (∃ X Y, u = tNode X Y)

theorem q9_node9 {R : Nock.Jet.Registry} {t : NTree SkelX} {cells : List Noun} {u : NTree LX9}
    (hu : Q9 R t cells u) : Node9 R t u := by
  rcases hu with h | ⟨v, hv, hax, -, -, rfl⟩ | ⟨n, m, s, e, new, hn, hm, he, -, -, rfl⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨v, hv, hax, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, m, s, e, new, hn, hm, he, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr h))

theorem chainNode_child_roots {v w : NTree SkelX} (hv : ChainNode v) (hw : w ∈ v.children) :
    w.label.subject = v.label.subject ∧ w.label.evaluation = v.label.evaluation := by
  obtain ⟨old, e, k, a, rfl, -⟩ := hv
  cases k with
  | zero => simp [genChainF] at hw
  | succ k =>
    by_cases h2 : 2 ≤ a
    · simp only [genChainF, h2, ite_true, mkX_children, List.mem_singleton] at hw
      subst hw
      rw [(genChainF_label _ _ _ _).1, (genChainF_label _ _ _ _).1, (genChainF_label _ _ _ _).2.1,
        (genChainF_label _ _ _ _).2.1]
      exact ⟨rfl, rfl⟩
    · simp [genChainF, h2] at hw

/-- **The chain child of a generated `s10` run** is the chain of `kidE 1 ⇝ evaluation`. -/
theorem genX_s10_chain_roots {R : Nock.Jet.Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) : t.label.state = .s10 → ∀ c ∈ t.children, ChainNode c →
      c.label.subject = kidE t.label 1 ∧ c.label.evaluation = t.label.evaluation := by
  induction n, s, f using genComputeSkeletonX.induct R generalizing t r
  all_goals first | (simp_all [genComputeSkeletonX]; done) | skip
  case case3 n s b c d tl l tr r' hd hbc ih1 ih2 =>
    simp only [genComputeSkeletonX, hd, hbc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [mkX_label]
  case case5 n s ax r' hs =>
    simp only [genComputeSkeletonX, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [mkX_label]
  case case7 n s u =>
    simp only [genComputeSkeletonX, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [mkX_label]
  case case8 n s b c tl l tr r1 hc hb t2 r2 hm ih1 ih2 ih3 =>
    simp only [genComputeSkeletonX, hb, hc, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [mkX_label]
  case case11 n s u t2 v hx ih =>
    simp only [genComputeSkeletonX, hx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [mkX_label]
  case case13 n s u t0 v hx ih =>
    simp only [genComputeSkeletonX, hx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [mkX_label]
  case case15 n s b c tl l tr r1 hc hb ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [mkX_label]
  case case17 n s b c d tC hb t2 r1 hc ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [mkX_label]
  case case19 n s b c d tC hb t2 r1 hc ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [mkX_label]
  case case22 n s b c t1 r1 hb t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [mkX_label]
  case case25 n s b c t1 r1 hb t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [mkX_label]
  case case28 n s ax c t1 core hc arm harm t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hc, harm, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [mkX_label]
  case case32 n s ax c d tl new tr old hd hc e he ih1 ih2 =>
    simp only [genComputeSkeletonX, hc, hd, he, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro _ k hk hch
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · exact absurd (chainNode_isChain hch) (by simp [(genX_label hc).2.2.2])
    · exact absurd (chainNode_isChain hch) (by simp [(genX_label hd).2.2.2])
    · rw [genChain, (genChainF_label _ _ _ _).1, (genChainF_label _ _ _ _).2.1]
      refine ⟨?_, rfl⟩
      have := (genX_label hd).2.2.1
      simp [kidE, mkX_label, SkelX.row, this]
  case case35 n s b clue body t1 v hcl r1 hj ih1 =>
    simp only [genComputeSkeletonX, hcl, hj, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [mkX_label]
  case case36 n s b clue body t1 v hcl hj t2 r1 hB ih1 ih2 =>
    simp only [genComputeSkeletonX, hcl, hj, hB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [mkX_label]
  case case39 n s b body t2 r1 hB ih1 =>
    simp only [genComputeSkeletonX, hB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [mkX_label]

/-- **Provenance of the generated `s10` nodes' roots**: the second kid evaluation and the evaluation of every
generated `s10` node of `t` are atoms or table cells. -/
def GenGd (R : Nock.Jet.Registry) (t : NTree SkelX) (cells : List Noun) : Prop :=
  ∀ v, InTree t v → GenNode R v → v.label.state = .s10 →
    Gd cells (kidE v.label 1) ∧ Gd cells v.label.evaluation

/-- **The provenance classes are closed under children.** -/
theorem q9_children {R : Nock.Jet.Registry} {t : NTree SkelX} {cells : List Noun}
    (hcl : ComplJ8Data.ClP cells []) (hGt : GenGd R t cells) {u : NTree LX9} (hu : Q9 R t cells u) :
    ∀ c ∈ u.children, Q9 R t cells c := by
  rcases hu with ⟨v, hvt, hv, rfl⟩ | ⟨v, hv, hax, hs, he, rfl⟩ | ⟨n, m, s, e, new, hn, hm, hed, hs, he, rfl⟩ | h
  · obtain ⟨m, hm⟩ := hv
    have hkids := genX_children9 hm
    have hGg := hGt v hvt ⟨m, hm⟩
    intro c' hc'
    rw [genX9T_children] at hc'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    rcases hkids c hc with hg | ⟨hch, hfc, hst⟩
    · have hnc := genNode_not_chain hg
      have : kid9 v.label c (genX9T c) = genX9T c := by simp [kid9, hnc]
      rw [this]
      exact Or.inl ⟨c, inTree_child hvt hc, hg, rfl⟩
    · have hic := chainNode_isChain hch
      obtain ⟨hG1, hGe⟩ := hGg hst
      by_cases hB : (chipOf v.label).1 = .s10B
      · have : kid9 v.label c (genX9T c) =
            segT (chipOf v.label).2 (top (chipOf v.label).2) (kidE v.label 1) v.label.evaluation := by
          simp [kid9, hB, hic]
        rw [this]
        obtain ⟨-, hn, hbig⟩ := chipOf_s10B hB
        refine Or.inr (Or.inr (Or.inl ⟨_, _, _, _, kidE v.label 0, ?_, le_rfl, ?_, hG1, hGe, rfl⟩))
        · rw [hn]; omega
        · rw [segAx_top, hn]; exact genNode_s10_edit ⟨m, hm⟩ hst
      · have : kid9 v.label c (genX9T c) = genX9T c := by simp [kid9, hB]
        rw [this, genX9T_chain hch]
        obtain ⟨hcs, hce⟩ := genX_s10_chain_roots hm hst c hc hch
        refine Or.inr (Or.inl ⟨c, hch, ?_, by rw [hcs]; exact hG1, by rw [hce]; exact hGe, rfl⟩)
        rw [hfc]
        exact small_of_not_s10B hst hB
  · intro c hc
    simp only [liftT, mapNTree_children] at hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
    obtain ⟨h1, h2⟩ := chainNode_child_roots hv hw
    exact Or.inr (Or.inl ⟨w, chainNode_children hv w hw,
      lt_of_le_of_lt (chainNode_child_axis hv hw) hax, by rw [h1]; exact hs, by rw [h2]; exact he, rfl⟩)
  · obtain ⟨X, Y, hX, hY, hc, hnx⟩ := seg_split hn hm hed
    have hch : ChainNode (genChain s e (segRd n m)) :=
      ⟨s, e, segRd n m, segRd n m, rfl, hc, segRd_pos hn m hm, by omega⟩
    have hax : chainAxis (genChain s e (segRd n m)).label.formula < 2 ^ 62 := by
      rw [genChain, (genChainF_label _ _ _ _).2.2.1, chainAxis_atom]
      have := Nock.J9A.NounAx.segRd_lt n m
      omega
    have hs' : Gd cells (genChain s e (segRd n m)).label.subject := by
      rw [genChain, (genChainF_label _ _ _ _).1]; exact hs
    have he' : Gd cells (genChain s e (segRd n m)).label.evaluation := by
      rw [genChain, (genChainF_label _ _ _ _).2.1]; exact he
    cases m with
    | zero =>
      intro c hc'
      simp only [segT, segNode, NTree.children, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hc'
      rcases hc' with rfl | rfl
      · exact Or.inr (Or.inl ⟨_, hch, hax, hs', he', rfl⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩))
    | succ m =>
      intro c hc'
      simp only [segT, segNode, NTree.children, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hc'
      rcases hc' with rfl | rfl
      · exact Or.inr (Or.inl ⟨_, hch, hax, hs', he', rfl⟩)
      · have hnext : Noun.edit (segAx n m) new X = some Y := by
          have := segAx_next n (m + 1) hm (by omega)
          simp only [Nat.add_sub_cancel] at this
          rw [this]; exact hnx
        refine Or.inr (Or.inr (Or.inl ⟨n, m, _, _, new, hn, by omega, ?_, gd_segX hcl hs, gd_segX hcl he, rfl⟩))
        simpa [segX, hX, hY] using hnext
  · rcases h with ⟨X, Y, rfl⟩
    intro c hc'
    simp [tNode, NTree.children] at hc'

/-- The handle nouns of a chain row with guarded roots are guarded. -/
theorem gd_chain_handles {cells : List Noun} {v : NTree SkelX} (hv : ChainNode v) (hs : Gd cells v.label.subject)
    (he : Gd cells v.label.evaluation) : ∀ n ∈ handleNounsX (rowOfSkelX v.label), Gd cells n := by
  obtain ⟨old, e, k, a, hv', -⟩ := hv
  have hs' : Gd cells old := by rw [hv', (genChainF_label _ _ _ _).1] at hs; exact hs
  have he' : Gd cells e := by rw [hv', (genChainF_label _ _ _ _).2.1] at he; exact he
  subst hv'
  have hat : ∀ w : ℕ, Gd cells (.atom w) := fun w h => by simp [Noun.isCell] at h
  intro n hn
  cases k with
  | zero =>
    simp only [handleNounsX, rowOfSkelX, genChainF, mkX_label, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hs' | exact he' | exact hat _
  | succ k =>
    by_cases h2 : 2 ≤ a
    · simp only [handleNounsX, rowOfSkelX, genChainF, h2, ite_true, mkX_label, List.mem_cons, List.not_mem_nil,
        or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hs' | exact he' | exact hat _
    · simp only [handleNounsX, rowOfSkelX, genChainF, h2, ite_false, mkX_label, List.mem_cons, List.not_mem_nil,
        or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hs' | exact he' | exact hat _

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads (consEntriesX9 walkReadsX9) in
/-- **The roots of the J-9 A walk reads** (ordinary, chain and segment rows): the axis is `≥ 2`, the slot is
defined and the root is an atom or a table cell. -/
theorem walkReadsX9_roots {R : Nock.Jet.Registry} {t : NTree SkelX} {cells : List Noun} {n : ℕ} {s f : Noun}
    {r : Noun} (h : genX R n s f = some (t, r))
    (hQ : ∀ u, InTree (genX9T t) u → Q9 R t cells u)
    (hOld : ∀ v, InTree t v → ∀ w ∈ handleNounsX (rowOfSkelX v.label), Gd cells w) :
    ∀ x ∈ walkReadsX9 (rowsOfT9 t), 2 ≤ x.2 ∧ (∃ ch, Noun.slot x.2 x.1 = some ch) ∧ Gd cells x.1 := by
  intro x hx
  simp only [walkReadsX9, List.mem_filter, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨⟨l, hl, y, hy, rfl⟩, h2⟩ := hx
  simp only [rowsOfT9, List.toList_toArray, List.mem_map] at hl
  obtain ⟨u, hu, rfl⟩ := hl
  obtain ⟨c, hc, hcu⟩ := (mem_bfsForest _ _).1 hu
  simp only [List.mem_singleton] at hc
  subst hc
  have hq := hQ u hcu
  have hsem := semN9_of_node9 (q9_node9 hq)
  simp only at h2 ⊢
  rcases hq with ⟨v, hvt, hv, rfl⟩ | ⟨v, hv, hax, hs, he, rfl⟩ | ⟨nn, m, s0, e0, new, hn, hm, hed, hs, he, rfl⟩ | ⟨X, Y, rfl⟩
  · rw [genX9T_label] at hy hsem
    unfold SemN9 at hsem
    unfold consEntriesX9 at hy
    simp only at hy hsem
    cases hch : (chipOf v.label).1 <;> simp only [hch] at hy hsem
    · obtain ⟨hs, -, -⟩ := hsem
      obtain ⟨h2', hsl⟩ := consEntriesX_sound _ hs y hy
      exact ⟨h2', ⟨_, hsl⟩, hOld v hvt _ (consEntriesX_root _ y hy)⟩
    · simp at hy
    · simp at hy
    · exact absurd hch (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads.chipOf_ne_s10S _)
  · rw [liftT_label] at hy hsem
    simp only [consEntriesX9, liftL] at hy
    unfold SemN9 at hsem
    simp only [liftL] at hsem
    obtain ⟨hs0, -, -⟩ := hsem
    obtain ⟨h2', hsl⟩ := consEntriesX_sound _ hs0 y hy
    exact ⟨h2', ⟨_, hsl⟩, gd_chain_handles hv hs he _ (consEntriesX_root _ y hy)⟩
  · rw [segT_label] at hy hsem
    unfold SemN9 at hsem
    simp only at hsem
    obtain ⟨-, -, -, -, -, h1, h1'⟩ := hsem
    simp only [consEntriesX9, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact ⟨of_decide_eq_true h2, ⟨_, h1⟩, hs⟩
    · exact ⟨of_decide_eq_true h2, ⟨_, h1'⟩, he⟩
  · simp [tNode, consEntriesX9, tRow, consEntriesX] at hy

theorem gd_curG {cells : List Noun} (hcl : ComplJ8Data.ClP cells []) (n m : ℕ) {s : Noun} (hs : Gd cells s) :
    ∀ j, Gd cells (ComplJ9ABalPAx.curG n m s j)
  | 0 => hs
  | j + 1 => gd_segX hcl (gd_curG hcl n m hs j)

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun (axKeys9 axChainReadsK9 axKeys9_read mem_axKeys9 axKey9) in
/-- **The keys of the axis chains are guarded**: the key noun of an `s0B` / `s10B` row is a handle noun of its J-8
row. -/
theorem axKeys9_gd {R : Nock.Jet.Registry} {t : NTree SkelX} {cells : List Noun}
    (hQ : ∀ u, InTree (genX9T t) u → Q9 R t cells u)
    (hOld : ∀ v, InTree t v → ∀ w ∈ handleNounsX (rowOfSkelX v.label), Gd cells w) :
    ∀ k ∈ axKeys9 (rowsOfT9 t), Gd cells k.1 := by
  intro k hk
  obtain ⟨l, hl, hlk⟩ := mem_axKeys9.1 hk
  simp only [rowsOfT9, List.toList_toArray, List.mem_map] at hl
  obtain ⟨u, hu, rfl⟩ := hl
  obtain ⟨c, hc, hcu⟩ := (mem_bfsForest _ _).1 hu
  simp only [List.mem_singleton] at hc
  subst hc
  have hq := hQ u hcu
  rcases hq with ⟨v, hvt, hv, rfl⟩ | ⟨v, hv, hax, hs, he, rfl⟩ | ⟨nn, m, s0, e0, new, hn, hm, hed, hs, he, rfl⟩ | ⟨X, Y, rfl⟩
  · rw [genX9T_label] at hlk
    simp only [axKey9] at hlk
    cases hch : (chipOf v.label).1 <;> simp only [hch] at hlk <;> first | (simp at hlk; done) | skip
    · have := Option.some.inj hlk
      subst this
      exact hOld v hvt _ (by simp [handleNounsX])
    · have := Option.some.inj hlk
      subst this
      exact hOld v hvt _ (by simp [handleNounsX])
  · rw [liftT_label] at hlk
    simp [axKey9, liftL] at hlk
  · rw [segT_label] at hlk
    simp [axKey9] at hlk
  · simp [tNode, axKey9] at hlk

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun (axKeys9 axChainReadsK9 axKeys9_read) in
/-- **The roots of the axis-chain reads.** -/
theorem axChainReadsK9_roots {R : Nock.Jet.Registry} {t : NTree SkelX} {cells : List Noun} {n : ℕ} {s f : Noun}
    {r : Noun} (h : genX R n s f = some (t, r)) (hcl : ComplJ8Data.ClP cells [])
    (hKg : ∀ k ∈ axKeys9 (rowsOfT9 t), Gd cells k.1) :
    ∀ x ∈ axChainReadsK9 (rowsOfT9 t), 2 ≤ x.2 ∧ (∃ ch, Noun.slot x.2 x.1 = some ch) ∧ Gd cells x.1 := by
  intro x hx
  simp only [axChainReadsK9, List.mem_filter, List.mem_flatMap] at hx
  obtain ⟨⟨k, hk, hxk⟩, h2⟩ := hx
  obtain ⟨hbig, Y, hY⟩ := axKeys9_read h hk
  have hn : k.2 ≠ 0 := by omega
  rw [ComplJ9ABalPAx.segReads_eq] at hxk
  simp only [List.mem_map, List.mem_range] at hxk
  obtain ⟨j, hj, rfl⟩ := hxk
  have hjt : j ≤ top k.2 := by omega
  refine ⟨of_decide_eq_true h2, ?_, gd_curG hcl _ _ (hKg k hk) j⟩
  have hinv := ComplJ9AChains.chain_inv k.2 k.1 Y hn hY j hjt
  rw [ComplJ9ABalPAx.curN_curG, ComplJ9AChains.slot_seg k.2 (top k.2 - j) _ hn (by omega)] at hinv
  cases hs : Noun.slot (segRd k.2 (top k.2 - j)) (ComplJ9ABalPAx.curG k.2 (top k.2) k.1 j) with
  | none => rw [hs] at hinv; simp at hinv
  | some Z => exact ⟨Z, rfl⟩

/-- **Every J-9 A read has a root in the table with a defined slot** (the hypotheses are the node provenance
`hQ` and the J-8 handle provenance `hOld`). -/
theorem readsA_roots {R : Nock.Jet.Registry} {t : NTree SkelX} {cells : List Noun} {n : ℕ} {s f : Noun}
    {r : Noun} (h : genX R n s f = some (t, r)) (hcl : ComplJ8Data.ClP cells [])
    (hQ : ∀ u, InTree (genX9T t) u → Q9 R t cells u)
    (hOld : ∀ v, InTree t v → ∀ w ∈ handleNounsX (rowOfSkelX v.label), Gd cells w) :
    ∀ x ∈ Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec.readsA t, 2 ≤ x.2 ∧
      (∃ ch, Noun.slot x.2 x.1 = some ch) ∧ x.1 ∈ cells ∧ ∃ a b, x.1 = .cell a b := by
  intro x hx
  unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec.readsA at hx
  have hall : 2 ≤ x.2 ∧ (∃ ch, Noun.slot x.2 x.1 = some ch) ∧ Gd cells x.1 := by
    rcases List.mem_append.1 hx with hx | hx
    · exact walkReadsX9_roots h hQ hOld x hx
    · exact axChainReadsK9_roots h hcl (axKeys9_gd hQ hOld) x hx
  obtain ⟨h2, ⟨ch, hsl⟩, hg⟩ := hall
  have hcell : ∃ a b, x.1 = .cell a b := by
    cases hx1 : x.1 with
    | atom v => rw [hx1, ComplJ8OfBalG.slot_atom_two h2] at hsl; cases hsl
    | cell a b => exact ⟨a, b, rfl⟩
  obtain ⟨a, b, hab⟩ := hcell
  exact ⟨h2, ⟨ch, hsl⟩, hg (by rw [hab]; rfl), a, b, hab⟩

open Nock.Jet.Autogen (Tpl) in
/-- **The generated `s10` nodes' roots are in the table**: they are handle nouns of the node's J-8 row. -/
theorem genGd_of_gen (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ}
    {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) :
    GenGd Rg.R t (j8DataOf p Rg Rt hgen).cells := by
  intro v hv hgv hst
  have hmem : v ∈ bfsForest [t] := (mem_bfsForest [t] v).2 ⟨t, by simp, hv⟩
  have hrowm : rowOfSkelX v.label ∈ (j8DataOf p Rg Rt hgen).rows.toList := by
    simp only [j8DataOf, ComplJ8Data.rowsOfT, List.toList_toArray]
    exact List.mem_map_of_mem hmem
  have hG : ∀ n ∈ handleNounsX (rowOfSkelX v.label), Gd (j8DataOf p Rg Rt hgen).cells n := by
    intro n hn hcell
    rcases ComplJ8Data.handle_noun_cases p Rg Rt hgen hrowm hn with ⟨-, hm⟩ | ⟨w, rfl, _⟩ | ⟨w, rfl, _⟩
    · exact hm
    · simp [Noun.isCell] at hcell
    · simp [Noun.isCell] at hcell
  have he : (rowOfSkelX v.label).e = v.label.evaluation := by
    unfold rowOfSkelX; cases v.label.state <;> rfl
  have h1 : (rowOfSkelX v.label).sf2 = kidE v.label 1 := by
    simp [rowOfSkelX, hst]
  refine ⟨?_, ?_⟩
  · rw [← h1]; exact hG _ (by simp [handleNounsX])
  · rw [← he]; exact hG _ (by simp [handleNounsX])

end Roots

/-! ## 4. `Tw = Wp` at every J-9 A read -/

section Final
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf readsA)
open Nock.Jet.Autogen (Tpl)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}

/-- **`Tw` is `Wp` at every J-9 A read** (`hlen`: the table is shorter than `p`; `hwalk9`: the J-9 A walk
binder). -/
theorem Tw_eq_Wp (hgen : genX Rg.R fuel s f = some (t, r))
    (hlen : (j9aDataOf p Rg Rt hgen).cells.length < p) (hp62 : 2 ^ 62 < p)
    (hwalk9 : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (χ : Coins frameJ8 K) (x : Noun × ℕ) (hx : x ∈ (j9aDataOf p Rg Rt hgen).reads) :
    Tw δ (j9aDataOf p Rg Rt hgen).H χ x =
      Wp δ (j9aDataOf p Rg Rt hgen) χ (readRecH (j9aDataOf p Rg Rt hgen).cells x) := by
  have hcl : ComplJ8Data.ClP (j8DataOf p Rg Rt hgen).cells [] := ComplJ8Data.cells_closed _
  have hQ : ∀ u, InTree (genX9T t) u → Q9 Rg.R t (j8DataOf p Rg Rt hgen).cells u := by
    have hG := genGd_of_gen p Rg Rt hgen
    have key : ∀ {c u : NTree LX9}, InTree c u → Q9 Rg.R t (j8DataOf p Rg Rt hgen).cells c →
        Q9 Rg.R t (j8DataOf p Rg Rt hgen).cells u := by
      intro c u hcu
      induction hcu with
      | here => exact id
      | sub hs _ ih => exact fun hc => ih (q9_children hcl hG hc _ hs)
    exact fun u hu => key hu (Or.inl ⟨t, .here t, genNode_of hgen, rfl⟩)
  have hOld : ∀ v, InTree t v → ∀ w ∈ handleNounsX (rowOfSkelX v.label),
      Gd (j8DataOf p Rg Rt hgen).cells w := by
    intro v hv w hw hcell
    have hmem : v ∈ bfsForest [t] := (mem_bfsForest [t] v).2 ⟨t, by simp, hv⟩
    have hrowm : rowOfSkelX v.label ∈ (j8DataOf p Rg Rt hgen).rows.toList := by
      simp only [j8DataOf, ComplJ8Data.rowsOfT, List.toList_toArray]
      exact List.mem_map_of_mem hmem
    rcases ComplJ8Data.handle_noun_cases p Rg Rt hgen hrowm hw with ⟨-, hm⟩ | ⟨w, rfl, _⟩ | ⟨w, rfl, _⟩
    · exact hm
    · simp [Noun.isCell] at hcell
    · simp [Noun.isCell] at hcell
  obtain ⟨h2, ⟨ch, hsl⟩, hmem, a, c, hac⟩ := readsA_roots hgen hcl hQ hOld x hx
  have hax : x.2 < p := by
    have hpr : x ∈ VclL.pathReads (j9aDataOf p Rg Rt hgen).reads := by
      unfold VclL.pathReads
      exact List.mem_dedup.mpr (List.mem_filter.mpr ⟨hx, ComplJ8OfBal.isPathAx_of_two_le h2⟩)
    exact (ComplJ8OfBalG.ax_lt_of_depth (by omega)
      (ComplJ9ADataRec.walkDepthOK_readsA Rt hgen hwalk9 _ hpr)).trans hp62
  have hidx : (((j9aDataOf p Rg Rt hgen).H x.1).2 : ℕ) = (j9aDataOf p Rg Rt hgen).cells.idxOf x.1 := by
    show (ComplJ8Data.hdlP p (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).acs x.1).2 = _
    rw [hac]
    simp only [ComplJ8Data.hdlP]
    rw [← hac, ComplJ8OfBal.genIdxOf_eq _ _ hmem]
    rfl
  exact Tw_eq_Wp_of_root δ (j9aDataOf p Rg Rt hgen) χ x hmem hidx hlen hax hsl

end Final

/-! ## 2. The walk side -/

section WalkA
open Module
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf readsA)
open Nock.Jet.Autogen (Tpl)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}

/-- **Every J-9 A read is a defined slot at an axis `≥ 2` of a cell of the table.** -/
theorem readsA_facts (hgen : genX Rg.R fuel s f = some (t, r)) :
    ∀ x ∈ (j9aDataOf p Rg Rt hgen).reads,
      2 ≤ x.2 ∧ (Noun.slot x.2 x.1).isSome ∧ x.1 ∈ (j9aDataOf p Rg Rt hgen).cells := by
  have hcl : ComplJ8Data.ClP (j8DataOf p Rg Rt hgen).cells [] := ComplJ8Data.cells_closed _
  have hQ : ∀ u, InTree (genX9T t) u → Q9 Rg.R t (j8DataOf p Rg Rt hgen).cells u := by
    have hG := genGd_of_gen p Rg Rt hgen
    have key : ∀ {c u : NTree LX9}, InTree c u → Q9 Rg.R t (j8DataOf p Rg Rt hgen).cells c →
        Q9 Rg.R t (j8DataOf p Rg Rt hgen).cells u := by
      intro c u hcu
      induction hcu with
      | here => exact id
      | sub hs _ ih => exact fun hc => ih (q9_children hcl hG hc _ hs)
    exact fun u hu => key hu (Or.inl ⟨t, .here t, genNode_of hgen, rfl⟩)
  have hOld : ∀ v, InTree t v → ∀ w ∈ handleNounsX (rowOfSkelX v.label),
      Gd (j8DataOf p Rg Rt hgen).cells w := by
    intro v hv w hw hcell
    have hmem : v ∈ bfsForest [t] := (mem_bfsForest [t] v).2 ⟨t, by simp, hv⟩
    have hrowm : rowOfSkelX v.label ∈ (j8DataOf p Rg Rt hgen).rows.toList := by
      simp only [j8DataOf, ComplJ8Data.rowsOfT, List.toList_toArray]
      exact List.mem_map_of_mem hmem
    rcases ComplJ8Data.handle_noun_cases p Rg Rt hgen hrowm hw with ⟨-, hm⟩ | ⟨w, rfl, _⟩ | ⟨w, rfl, _⟩
    · exact hm
    · simp [Noun.isCell] at hcell
    · simp [Noun.isCell] at hcell
  intro x hx
  obtain ⟨h2, ⟨ch, hsl⟩, hmem, -⟩ := readsA_roots hgen hcl hQ hOld x hx
  exact ⟨h2, by rw [hsl]; rfl, hmem⟩

/-- **The `whP` twin, generic in the data** (the proof of `ComplJ8OfBalG.whP_eq`; the two facts about the table it
takes from the run are hypotheses). -/
theorem whP_eq_gen (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjW : Function.Injective (powN o (walkRows D.cells D.reads).length))
    (χ : Coins frameJ8 K) (hlen : D.cells.length < p)
    (hwcell : ∀ u ∈ walkRows D.cells D.reads, u.label.node ∈ D.cells)
    (hkids : ∀ c ∈ D.cells, ∃ x y, c = Noun.cell x y)
    (hpre : ∀ u ∈ walkRows D.cells D.reads, 2 * axisFold u.label.bits + 1 < p) :
    whP δ b D o χ = ((walkRows D.cells D.reads).map fun u => provH (Wp δ D χ) D.cells u.label).sum := by
  unfold whP
  rw [← ComplJ8OfBal.sum_range_getD' (trie (.atom 0) (.atom 0) [] [])
    (fun u => provH (Wp δ D χ) D.cells u.label)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [show (walkRows D.cells D.reads).getD k (trie (.atom 0) (.atom 0) [] []) = wTrie D.cells D.reads k from rfl]
  obtain ⟨-, eL, eR⟩ := walk_dRow_split δ b D o hinjW χ (pubsW0 δ D χ) ⟨k, hk'⟩
  simp only [wdN, WalkTraceHQ.dN, WalkTraceH.cN, dif_pos hk', eL, eR]
  have hu : wTrie D.cells D.reads k ∈ walkRows D.cells D.reads := wTrie_mem _ _ hk'
  obtain ⟨hch, hroot⟩ := walk_row_chain D.cells D.reads hwcell _ hu
  obtain ⟨l, rr, hlr⟩ := hkids _ (hwcell _ hu)
  have hp2 := hpre _ hu
  set w := (wTrie D.cells D.reads k).label with hw
  have hmL : wCol δ b D χ WChip.mL ⟨k, hk'⟩ = ((w.mL : ℕ) : ZMod p) := rfl
  have hmR : wCol δ b D χ WChip.mR ⟨k, hk'⟩ = ((w.mR : ℕ) : ZMod p) := rfl
  rw [hmL, hmR]
  have hsL : Noun.slot (2 * axisFold w.bits) w.root = some l := by
    rw [show 2 * axisFold w.bits = axisFold (w.bits ++ [false]) by rw [axisFold_append]; simp, chain_slot,
      chainWalk_append, hch, hlr]
    rfl
  have hsR : Noun.slot (2 * axisFold w.bits + 1) w.root = some rr := by
    rw [show 2 * axisFold w.bits + 1 = axisFold (w.bits ++ [true]) by rw [axisFold_append]; simp, chain_slot,
      chainWalk_append, hch, hlr]
    rfl
  have eWL : Wp δ D χ (recLH D.cells w) = (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ)
      (((D.cells.idxOf w.root : ℕ) : ZMod p), ((2 * axisFold w.bits : ℕ) : ZMod p),
        ((((D.H l).1 : ℕ) : ZMod p), (((D.H l).2 : ℕ) : ZMod p))))⁻¹ := by
    rw [recLH, Wp_third δ D χ _ _ _ (0, 0)]
    exact Wp_eq δ D χ w.root l _ _ hroot rfl hlen (by omega) hsL
  have eWR : Wp δ D χ (recRH D.cells w) = (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ)
      (((D.cells.idxOf w.root : ℕ) : ZMod p), ((2 * axisFold w.bits + 1 : ℕ) : ZMod p),
        ((((D.H rr).1 : ℕ) : ZMod p), (((D.H rr).2 : ℕ) : ZMod p))))⁻¹ := by
    rw [recRH, Wp_third δ D χ _ _ _ (0, 0)]
    exact Wp_eq δ D χ w.root rr _ _ hroot rfl hlen hp2 hsR
  rw [provH, nsmul_eq_mul, nsmul_eq_mul, eWL, eWR]
  have hkl : kLW D ⟨k, hk'⟩ = (((D.H l).1 : ℕ) : ZMod p) ∧ vLW D ⟨k, hk'⟩ = (((D.H l).2 : ℕ) : ZMod p) ∧
      kRW D ⟨k, hk'⟩ = (((D.H rr).1 : ℕ) : ZMod p) ∧ vRW D ⟨k, hk'⟩ = (((D.H rr).2 : ℕ) : ZMod p) := by
    simp only [kLW, vLW, kRW, vRW, wNode, ← hw, hlr]
    exact ⟨rfl, rfl, rfl, rfl⟩
  rw [hkl.1, hkl.2.1, hkl.2.2.1, hkl.2.2.2]
  have hri : (wValsC δ D χ ⟨k, hk'⟩).ridx = ((D.cells.idxOf w.root : ℕ) : ZMod p) := rfl
  have hpr : (wValsC δ D χ ⟨k, hk'⟩).pre = ((axisFold w.bits : ℕ) : ZMod p) := rfl
  rw [hri, hpr]
  push_cast
  simp [liftQ, map_natCast]

/-- **Every J-9 A walk node is a cell of the table** (twin of `ComplJ8OfBal.walkRows_node_cells`, with the read facts
from `readsA_facts`). -/
theorem walkRowsA_node_cells (hgen : genX Rg.R fuel s f = some (t, r)) :
    ∀ u ∈ walkRows (j9aDataOf p Rg Rt hgen).cells (j9aDataOf p Rg Rt hgen).reads,
      u.label.node ∈ (j9aDataOf p Rg Rt hgen).cells := by
  set D := j9aDataOf p Rg Rt hgen with hD
  have hfacts := readsA_facts (p := p) Rt hgen
  have hclosed : ComplJ8Data.ClP D.cells [] := ComplJ8Data.cells_closed _
  have htok : ∀ r, ∀ s ∈ targetsOf D.reads r, s ≠ [] ∧ (chainWalk r s).isSome := by
    intro r s hs
    refine ⟨targetsOf_ne _ r s hs, ?_⟩
    unfold targetsOf at hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hxk, hxr⟩ := List.mem_filter.mp hx
    have hxr : x.1 = r := of_decide_eq_true hxr
    have hpk := mem_pathKind.mp hxk
    have hsl := (hfacts x hpk.1).2.1
    rw [slot_eq_chainWalk _ (by have := two_le_of_path hpk.2; omega), hxr] at hsl
    exact hsl
  intro u hu
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp hu
  let Q : Noun → List Bool → List (List Bool) → Prop := fun n _ T =>
    n ∈ D.cells ∧ ∀ s ∈ T, s ≠ [] ∧ (chainWalk n s).isSome
  have hQ : ∀ l r bs T (b : Bool), Q (.cell l r) bs T → cont b T = true →
      Q (if b then r else l) (bs ++ [b]) (contT b T) := by
    intro l r bs T b hq hcont
    obtain ⟨hmem, hT⟩ := hq
    have hT' : ∀ s ∈ contT b T, s ≠ [] ∧ (chainWalk (if b then r else l) s).isSome := by
      intro s hs
      obtain ⟨hbs, hne⟩ := mem_contT hs
      exact ⟨hne, by simpa [chainWalk] using (hT _ hbs).2⟩
    refine ⟨?_, hT'⟩
    obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ (contT_ne_nil hcont)
    obtain ⟨hne, hsome⟩ := hT' s hs
    obtain ⟨b', s', rfl⟩ : ∃ b' s', s = b' :: s' := by
      cases s with
      | nil => exact absurd rfl hne
      | cons b' s' => exact ⟨b', s', rfl⟩
    obtain ⟨x, y, hxy⟩ := chainWalk_cons_cell hsome
    have hcl := hclosed l r hmem (by simp)
    cases b
    · simp only [Bool.false_eq_true, if_false] at hxy ⊢; exact hcl.1 x y hxy
    · simp only [if_true] at hxy ⊢; exact hcl.2 x y hxy
  rcases mem_walkForest hc with ⟨-, rfl⟩ | ⟨r, hr, rfl⟩
  · have hq : Q (D.cells.headD (.atom 0)) [] [] := by
      refine ⟨?_, by simp⟩
      have : 0 < D.cells.length := cells_pos (p := p) Rt hgen
      cases h : D.cells with
      | nil => rw [h] at this; simp at this
      | cons a l => simp
    obtain ⟨n', bs', T', rfl, hq'⟩ := inTree_trie_inv _ Q hQ hin _ _ _ rfl hq
    rw [(trie_label _ _ _ _).1]; exact hq'.1
  · have hrc : r ∈ D.cells := by
      unfold walkRoots at hr
      obtain ⟨z0, hz0, hz0r⟩ := List.mem_map.mp (List.mem_dedup.mp hr)
      rw [← hz0r]
      exact (hfacts z0 (mem_pathKind.mp hz0).1).2.2
    have hq : Q r [] (targetsOf D.reads r) := ⟨hrc, htok r⟩
    obtain ⟨n', bs', T', rfl, hq'⟩ := inTree_trie_inv _ Q hQ hin _ _ _ rfl hq
    rw [(trie_label _ _ _ _).1]; exact hq'.1

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (BRun9A hF_run) in
set_option maxHeartbeats 2000000 in
/-- **The J-9 A walk side of `hGp`.** The walk's handle provide (`pubsW` 6/7 of the J-9 A run) is the sum of
`Wp` over the J-9 A reads. -/
theorem walkA_run (hgen : genX Rg.R fuel s f = some (t, r)) (hpG : p = Nock.Atoms.p)
    (h31A : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.Rows31A (j9aDataOf p Rg Rt hgen))
    (hlen : (j9aDataOf p Rg Rt hgen).cells.length < p) (hp62 : 2 ^ 62 < p)
    (hwalk9 : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ)
        (((BRun9A δ b Rt hgen hpG h31A).M χ).pubsW WalkHQ.pubPQ)
        (((BRun9A δ b Rt hgen hpG h31A).M χ).pubsW (WalkHQ.pubPQ + 1)) =
      (((j9aDataOf p Rg Rt hgen).reads).map fun x =>
        Wp δ (j9aDataOf p Rg Rt hgen) χ (readRecH (j9aDataOf p Rg Rt hgen).cells x)).sum := by
  set D := j9aDataOf p Rg Rt hgen with hD
  set o := orbJ8 D (hF_run Rt hgen hpG h31A)
  have hfacts := readsA_facts (p := p) Rt hgen
  have hmW : (walkRows D.cells D.reads).length ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjW := (powN_ok o (le_two_pow_ht D hmW)).1
  have eW : Quad.mk (algebraMap (ZMod p) K δ) (((BRun9A δ b Rt hgen hpG h31A).M χ).pubsW WalkHQ.pubPQ)
      (((BRun9A δ b Rt hgen hpG h31A).M χ).pubsW (WalkHQ.pubPQ + 1)) = whP δ b D o χ := by
    show Quad.mk _ (pubsWOf δ b D o χ WalkHQ.pubPQ) (pubsWOf δ b D o χ (WalkHQ.pubPQ + 1)) = _
    have h6 : pubsWOf δ b D o χ WalkHQ.pubPQ = pub2 δ (whP δ b D o χ) 6 := by simp [pubsWOf, WalkHQ.pubPQ]
    have h7 : pubsWOf δ b D o χ (WalkHQ.pubPQ + 1) = pub2 δ (whP δ b D o χ) 7 := by simp [pubsWOf, WalkHQ.pubPQ]
    rw [h6, h7, pub2_mk2 δ _ 6 rfl]
  rw [eW]
  have hwalk : ComplJ8Walk.WalkDepthOK D.reads := ComplJ9ADataRec.walkDepthOK_readsA Rt hgen hwalk9
  have hpre : ∀ u ∈ walkRows D.cells D.reads, 2 * axisFold u.label.bits + 1 < p := by
    intro u hu
    have h60 := ComplJ8Walk.walkRows_len_le60 hwalk hu
    have h1 := axisFold_lt u.label.bits
    have h2 : 2 ^ (u.label.bits.length + 1) ≤ 2 ^ 61 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 62 = 2 * 2 ^ 61 := by norm_num
    omega
  have hwcell := walkRowsA_node_cells (p := p) Rt hgen
  have hkids : ∀ c ∈ D.cells, ∃ x y, c = Noun.cell x y := fun c hc => by
    obtain ⟨x, y, h, -, -⟩ := cells_kids Rt hgen c hc
    exact ⟨x, y, h⟩
  have hall : ∀ x ∈ D.reads, VclL.isPathAx x.2 = true := fun x hx =>
    ComplJ8OfBal.isPathAx_of_two_le (hfacts x hx).1
  have hslot : ∀ x ∈ VclL.pathReads D.reads, (Noun.slot x.2 x.1).isSome := fun x hx =>
    (hfacts x (List.mem_filter.mp (List.mem_dedup.mp hx)).1).2.1
  rw [whP_eq_gen δ b D o hinjW χ hlen hwcell hkids hpre,
    walk_provide_total (Wp δ D χ) D.cells D.reads hslot (fun _ => rfl), ComplJ8OfBal.pathKind_of_all hall]

end WalkA

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalPW
