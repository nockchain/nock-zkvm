/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ARunFacts.lean

  **J-9 A L7: the run facts `hsub` (`Sub9`), `hrowsA`, `hlen`** that `ComplJ9ABalO.hGx_A` and `ComplJ9ABalP.hGpA`
  take as binders, derived from the run (binders `hgen hpG hax9 hop5 h31A` only).

  * `sub9_run`        : `ComplJ9ABalCR.Sub9 Rt hgen`.
  * `hrowsA_run`      : the `hrowsA` binder of `ComplJ9ABalR.hrangeA_of` / `ComplJ9ABalO.hGx_A`.
  * `hlen_run`        : `(j9aDataOf p Rg Rt hgen).cells.length < p`.

  Method: the provenance invariant `Q9'` (`ComplJ9ABalPW.Q9` with the closing `s10T` row's roots recorded) holds at
  every node of the twin tree; every handle noun of every twin row is then an atom or a table cell (`Gd`), and the
  table is child-closed (`ComplJ8Data.cells_closed`). -/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalO
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalPW
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalCR
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalR
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABase

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARunFacts

noncomputable section

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of (sizesJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalPW
open Nock.J9A.NounAx (top segAx segRd segAx_top segAx_next segRd_pos)

/-! ## 1. Guarded nouns of a child-closed list -/

theorem gd_atom {cs : List Noun} (w : ℕ) : Gd cs (.atom w) := fun h => by simp [Noun.isCell] at h

theorem gd_children {cs : List Noun} (hcl : ComplJ8Data.ClP cs []) {a b : Noun} (h : Gd cs (.cell a b)) :
    Gd cs a ∧ Gd cs b := by
  have hh := hcl a b (h rfl) (by simp)
  have key : ∀ z : Noun, (∀ x y, z = .cell x y → z ∈ cs) → Gd cs z := by
    intro z hz hc
    cases z with
    | atom _ => simp [Noun.isCell] at hc
    | cell x y => exact hz x y rfl
  exact ⟨key _ hh.1, key _ hh.2⟩

theorem gd_hd {cs : List Noun} (hcl : ComplJ8Data.ClP cs []) {y : Noun} (hy : Gd cs y) : Gd cs (hdN y) := by
  cases y with
  | atom v => intro h; simp [hdN, Noun.isCell] at h
  | cell a b => simpa [hdN] using (gd_children hcl hy).1

theorem gd_tl {cs : List Noun} (hcl : ComplJ8Data.ClP cs []) {y : Noun} (hy : Gd cs y) : Gd cs (tlN y) := by
  cases y with
  | atom v => intro h; simp [tlN, Noun.isCell] at h
  | cell a b => simpa [tlN] using (gd_children hcl hy).2

theorem gd_fd {cs : List Noun} (hcl : ComplJ8Data.ClP cs []) :
    ∀ a b : Noun, Gd cs a → Gd cs b → Gd cs (fdN a b).2.1 ∧ Gd cs (fdN a b).2.2
  | .atom x, .atom y => fun ha hb => by simp only [fdN]; exact ⟨ha, hb⟩
  | .atom x, .cell y z => fun ha hb => by simp only [fdN]; exact ⟨ha, hb⟩
  | .cell x y, .atom z => fun ha hb => by simp only [fdN]; exact ⟨ha, hb⟩
  | .cell a1 a2, .cell b1 b2 => fun ha hb => by
    have hA := gd_children hcl ha
    have hB := gd_children hcl hb
    by_cases h1 : a1 = b1
    · simp only [fdN, h1, ite_true]
      exact gd_fd hcl a2 b2 hA.2 hB.2
    · simp only [fdN, h1, ite_false]
      exact gd_fd hcl a1 b1 hA.1 hB.1

theorem gd_slot {cs : List Noun} (hcl : ComplJ8Data.ClP cs []) (a : ℕ) {s : Noun} (hs : Gd cs s) :
    Gd cs ((Noun.slot a s).getD (.atom 0)) := by
  intro hY
  cases hsl : Noun.slot a s with
  | none => simp [hsl, Noun.isCell] at hY
  | some Y =>
    simp only [hsl, Option.getD_some] at hY ⊢
    have hY' : ∃ c d, Y = .cell c d := by
      cases Y with
      | atom _ => simp [Noun.isCell] at hY
      | cell c d => exact ⟨c, d, rfl⟩
    by_cases ha : 1 ≤ a
    · cases s with
      | atom v =>
        exfalso
        rcases (by omega : a = 1 ∨ 2 ≤ a) with h | h
        · rw [h] at hsl
          simp [Noun.slot] at hsl
          subst hsl
          obtain ⟨c, d, h⟩ := hY'
          cases h
        · rw [ComplJ8OfBalG.slot_atom_two h] at hsl; cases hsl
      | cell x y => exact slot_mem_cells hcl ha (hs rfl) hsl hY'
    · have h0 : a = 0 := by omega
      rw [h0] at hsl
      simp [Noun.slot] at hsl

/-! ## 2. The twelve handles of a row -/

theorem rowGd12 {cs : List Noun} (hcl : ComplJ8Data.ClP cs []) (sk : SkelX)
    (hH : ∀ n ∈ handleNounsX (rowOfSkelX sk), Gd cs n) :
    ∀ k < 12, Gd cs (HonestCompX.hN (rowOfSkelX sk) k) := by
  have gs : Gd cs (rowOfSkelX sk).s := hH _ (by simp [handleNounsX])
  have gf : Gd cs (rowOfSkelX sk).f := hH _ (by simp [handleNounsX])
  have ge : Gd cs (rowOfSkelX sk).e := hH _ (by simp [handleNounsX])
  have g1 : Gd cs (rowOfSkelX sk).sf1 := hH _ (by simp [handleNounsX])
  have g2 : Gd cs (rowOfSkelX sk).sf2 := hH _ (by simp [handleNounsX])
  have gm : Gd cs (rowOfSkelX sk).m := hH _ (by simp [handleNounsX])
  have key : Gd cs (rowOfSkelX sk).fh ∧ Gd cs (rowOfSkelX sk).ft ∧ Gd cs (rowOfSkelX sk).fth ∧
      Gd cs (rowOfSkelX sk).ftt ∧ Gd cs (rowOfSkelX sk).ftth ∧ Gd cs (rowOfSkelX sk).fttt := by
    cases hst : sk.state <;> simp only [rowOfSkelX, hst] at gs gf ge g1 g2 ⊢ <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      repeat' (first
        | exact gd_atom _
        | assumption
        | exact (gd_fd hcl _ _ g1 g2).1
        | exact (gd_fd hcl _ _ g1 g2).2
        | exact gd_slot hcl _ gs
        | exact gd_slot hcl _ ge
        | apply gd_hd hcl
        | apply gd_tl hcl)
  intro k hk
  interval_cases k <;> simp only [HonestCompX.hN]
  · exact gs
  · exact gf
  · exact ge
  · exact g1
  · exact g2
  · exact key.1
  · exact key.2.1
  · exact key.2.2.1
  · exact key.2.2.2.1
  · exact key.2.2.2.2.1
  · exact key.2.2.2.2.2
  · exact gm

theorem six_of_twelve {cs : List Noun} {r : RowNX} (h : ∀ k < 12, Gd cs (HonestCompX.hN r k)) :
    ∀ n ∈ handleNounsX r, Gd cs n := by
  intro n hn
  simp only [handleNounsX, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h 0 (by norm_num)
  · exact h 1 (by norm_num)
  · exact h 2 (by norm_num)
  · exact h 3 (by norm_num)
  · exact h 4 (by norm_num)
  · exact h 11 (by norm_num)

/-! ## 3. The provenance invariant with the closing row's roots -/

/-- `Q9` with the roots of the closing `s10T` row recorded. -/
def Q9' (R : Nock.Jet.Registry) (t : NTree SkelX) (cells : List Noun) (u : NTree LX9) : Prop :=
  (∃ v, InTree t v ∧ GenNode R v ∧ u = genX9T v) ∨
  (∃ v, ChainNode v ∧ chainAxis v.label.formula < 2 ^ 62 ∧ Gd cells v.label.subject ∧
      Gd cells v.label.evaluation ∧ u = liftT v) ∨
  (∃ n m s e new, n ≠ 0 ∧ m ≤ top n ∧ Noun.edit (segAx n m) new s = some e ∧ Gd cells s ∧ Gd cells e ∧
      u = segT n m s e) ∨
  (∃ X Y, Gd cells X ∧ Gd cells Y ∧ u = tNode X Y)

theorem q9'_children {R : Nock.Jet.Registry} {t : NTree SkelX} {cells : List Noun}
    (hcl : ComplJ8Data.ClP cells []) (hGt : GenGd R t cells) {u : NTree LX9} (hu : Q9' R t cells u) :
    ∀ c ∈ u.children, Q9' R t cells c := by
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
      · exact Or.inr (Or.inr (Or.inr ⟨_, _, gd_segX hcl hs, gd_segX hcl he, rfl⟩))
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
  · rcases h with ⟨X, Y, -, -, rfl⟩
    intro c hc'
    simp [tNode, NTree.children] at hc'

/-- The twelve handles of every `Q9'` node are atoms or table cells. -/
theorem q9'_gd12 {R : Nock.Jet.Registry} {t : NTree SkelX} {cells : List Noun}
    (hcl : ComplJ8Data.ClP cells [])
    (hOld : ∀ v, InTree t v → ∀ w ∈ handleNounsX (rowOfSkelX v.label), Gd cells w) {u : NTree LX9}
    (hu : Q9' R t cells u) : ∀ k < 12, Gd cells (HonestCompX.hN u.label.rn k) := by
  rcases hu with ⟨v, hvt, hv, rfl⟩ | ⟨v, hv, hax, hs, he, rfl⟩ | ⟨n, m, s, e, new, hn, hm, hed, hs, he, rfl⟩ |
    ⟨X, Y, hX, hY, rfl⟩
  · rw [genX9T_label]
    exact rowGd12 hcl _ (hOld v hvt)
  · simp only [liftT_label]
    exact rowGd12 hcl _ (gd_chain_handles hv hs he)
  · rw [segT_label]
    intro k hk
    interval_cases k <;> simp only [HonestCompX.hN, segRow] <;>
      first | exact gd_atom _ | assumption | exact gd_segX hcl hs | exact gd_segX hcl he
  · simp only [tNode, tRow, NTree.label]
    intro k hk
    interval_cases k <;> simp only [HonestCompX.hN] <;>
      first | exact gd_atom _ | assumption

/-! ## 4. The run facts -/

section Run
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DA" => j9aDataOf p Rg Rt hgen

/-- Every node of the twin tree is in `Q9'`. -/
theorem q9'_all {u : NTree LX9} (hu : InTree (genX9T t) u) :
    Q9' Rg.R t (j8DataOf p Rg Rt hgen).cells u := by
  have hcl : ComplJ8Data.ClP (j8DataOf p Rg Rt hgen).cells [] := ComplJ8Data.cells_closed _
  have hG := genGd_of_gen p Rg Rt hgen
  have key : ∀ {c u : NTree LX9}, InTree c u → Q9' Rg.R t (j8DataOf p Rg Rt hgen).cells c →
      Q9' Rg.R t (j8DataOf p Rg Rt hgen).cells u := by
    intro c u hcu
    induction hcu with
    | here => exact id
    | sub hs _ ih => exact fun hc => ih (q9'_children hcl hG hc _ hs)
  exact key hu (Or.inl ⟨t, .here t, genNode_of hgen, rfl⟩)

theorem hOld_run : ∀ v, InTree t v → ∀ w ∈ handleNounsX (rowOfSkelX v.label),
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

theorem inTree_of_W9 {u : NTree LX9} (hu : u ∈ ComplJ9ARun.W9 t) : InTree (genX9T t) u := by
  obtain ⟨c, hc, hcu⟩ := (mem_bfsForest _ _).1 hu
  simp only [List.mem_singleton] at hc
  subst hc; exact hcu

/-- **(1) `Sub9` from the run**: every cell sub-noun of a handle root of a twin row is a cell of the table. -/
theorem sub9_run : ComplJ9ABalCR.Sub9 (p := p) Rt hgen := by
  intro u hu n hn z hz
  have hcl : ComplJ8Data.ClP (j8DataOf p Rg Rt hgen).cells [] := ComplJ8Data.cells_closed _
  have h12 := q9'_gd12 hcl (hOld_run Rt hgen) (q9'_all Rt hgen (inTree_of_W9 hu))
  have hGd := six_of_twelve h12 n hn
  rw [ComplJ9ADataRec.j9aDataOf_cells] at *
  exact ComplJ8Data.subs_mem_of_closed hcl n (fun x y e => hGd (by rw [e]; rfl)) z hz

/-- **(2) `hrowsA` from the run** (the `hrowsA` binder of `ComplJ9ABalR.hrangeA_of`). -/
theorem hrowsA_run [Fact (ringChar (ZMod p)).Prime] (hpG : p = Nock.Atoms.p) (hax9 : ProgAxOK9A p t) (hop5 : ComplJ8.ProgOp5OK p t) :
    ∀ l ∈ (rowsOfT9 t).toList,
      (l.chip = .old → HonestCompX.RowOKX p l.rn) ∧
      (l.chip = .old → l.rn.st = .s3 → l.rn.sf1.isCell = true → l.rn.sf1 = .cell l.rn.ftth l.rn.fttt) ∧
      ∀ k < 12, (HonestCompX.hN l.rn k).isCell = true → HonestCompX.hN l.rn k ∈ (DA).cells := by
  intro l hl
  simp only [rowsOfT9, List.toList_toArray, List.mem_map] at hl
  obtain ⟨u, hu, rfl⟩ := hl
  have hin : InTree (genX9T t) u := inTree_of_W9 (t := t) hu
  have hnode := genX9T_inTree hgen hin
  have hcl : ComplJ8Data.ClP (j8DataOf p Rg Rt hgen).cells [] := ComplJ8Data.cells_closed _
  refine ⟨fun hc => ?_, fun hc => ComplJ9ABalCR.hs3_node9 hnode hc, fun k hk hcell => ?_⟩
  · exact (ComplJ9ABase.old_facts hpG hgen hax9 hop5 (DA).H (DA).pd
      (ComplJ9AOfComp.hpairA Rt hgen hpG hop5) hnode hc).1
  · have h12 := q9'_gd12 hcl (hOld_run Rt hgen) (q9'_all Rt hgen hin) k hk hcell
    rw [ComplJ9ADataRec.j9aDataOf_cells]
    exact h12

/-- **(3) `hlen` from the run**: `cells ≤ 2^31 < p`. -/
theorem hlen_run (hpG : p = Nock.Atoms.p) (h31A : Rows31A (DA)) : (DA).cells.length < p := by
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have hmC : (DA).cells.length ∈ sizesJ8 (DA) := by simp [sizesJ8]
  have h1 := rows31_of_A h31A (DA).cells.length hmC
  have : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
  omega

end Run

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARunFacts

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARunFacts
#print axioms sub9_run
#print axioms hrowsA_run
#print axioms hlen_run
end Axioms
