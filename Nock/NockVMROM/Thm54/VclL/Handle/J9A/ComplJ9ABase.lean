/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABase.lean

`hbase9`: for the honest J-9 A tree `genX9T t` of a run `genX R fuel s f = some (t, r)` at Goldilocks, every
  arithmetic and every equality base gate of the twin vanishes at the honest environment `hEnvX9` of every BFS
  row.  Case split on the chip state of the row (`old`: `ComplJ9ACompRow.old_gates` on J-8's `RowOKX`; `s0B`,
  `s10B`, `s10S`: the three new gate lemmas of `ComplJ9ACompRow`).

  * `old_facts`: `RowOKX` and `PairOK` on the old rows (a generated node, a lifted chain node at an axis below
    `2^62`, or the closing `s10T` row).
  * `s10B_cells`: the two cell facts `fttt`, `ftt` of an `s10B` row, from the generated run (`genX_rowOK` at the
    row's own axis bound `a + 1`).
  * `s10S_axis` / `s10S_m_lt`: the segment index of an `s10S` row is below `63`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.HonestSatX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ACompRow
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AData
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AChains
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABinders

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABase

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestRowX (SmallX genX_rowOK chain_rowOK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChains
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders
open Nock.NockVMROM.Thm54.VclL.HonestWalkX9 (rowAt9 fl1 llW)
open Nock.J9A.NounAx (top)

noncomputable section

/-! ## 1. Small facts -/

theorem rowOfSkelX_s (k : SkelX) : (rowOfSkelX k).s = k.subject := by
  unfold rowOfSkelX; cases k.state <;> rfl

theorem rowOfSkelX_e (k : SkelX) : (rowOfSkelX k).e = k.evaluation := by
  unfold rowOfSkelX; cases k.state <;> rfl

theorem chipOf_ne_s10S (k : SkelX) : (chipOf k).1 ≠ .s10S := by
  unfold chipOf
  cases k.state <;> simp <;> split <;> simp

theorem chain_state {s : StateX} (h : s.isChain = true) : s = .s10L ∨ s = .s10T := by
  cases s <;> simp_all [StateX.isChain]

theorem smallX_chain {p : ℕ} {r : RowNX} (hs : r.st = .s10L ∨ r.st = .s10T)
    (hf : ∀ a, r.f = .atom a → a + 1 < p) : SmallX p r := by
  unfold SmallX
  rcases hs with hs | hs <;> simp only [hs] <;> first | exact hf | trivial

/-! ## 2. Old rows -/

section Old
variable {p : ℕ} [Fact p.Prime] {R : Nock.Jet.Registry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}

/-- **`RowOKX` and `PairOK` at every old row** of the J-9 A tree. -/
theorem old_facts (hpG : p = Nock.Atoms.p) (h : genX R fuel s f = some (t, r))
    (hax9 : ProgAxOK9A p t) (hop5 : ComplJ8.ProgOp5OK p t) (H : Noun → ℕ × ℕ)
    (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
    (hpair : ∀ u, InTree t u → isPair H (rowOfSkelX u.label) → PairOK (F := ZMod p) (pd (rowOfSkelX u.label)))
    {u : NTree LX9} (hu : Node9 R t u) (hchip : u.label.chip = .old) :
    RowOKX p u.label.rn ∧ (isPair H u.label.rn → PairOK (F := ZMod p) (pd u.label.rn)) := by
  have hp63 := hp63_of_G hpG
  have hsem := semN9_of_node9 hu
  rcases hu with ⟨v, hvt, hv, rfl⟩ | ⟨v, hv, hax, rfl⟩ | hseg
  · simp only [genX9T_label] at hchip hsem ⊢
    simp only [SemN9, hchip] at hsem
    obtain ⟨-, h0, h10⟩ := hsem
    obtain ⟨m, hm⟩ := hv
    have hsm : SmallX p (rowOfSkelX v.label) := by
      have hax' := hax9 v hvt
      have hop' := hop5 v hvt
      have hnc := genNode_not_chain ⟨m, hm⟩
      have hst := rowOfSkelX_st v.label
      unfold AxRowX9A at hax'
      unfold ComplJ8.Op5RowX at hop'
      unfold SmallX
      cases hs : (rowOfSkelX v.label).st <;> simp only [hs] at hax' hop' ⊢ <;>
        first
        | trivial
        | exact fun ax hx => lt_trans (h0 hs ax hx) (by omega)
        | exact fun a ha => lt_trans (h10 hs a ha) (by omega)
        | exact hax'
        | exact hop' trivial
        | (exfalso
           have h' : v.label.state = (rowOfSkelX v.label).st := hst.symm
           rw [hs] at h'
           rw [h'] at hnc
           simp [StateX.isChain] at hnc)
    exact ⟨genX_rowOK hm hsm, hpair v hvt⟩
  · have hst := rowOfSkelX_st v.label
    have hc := chain_state (chainNode_isChain hv)
    have hcs : (rowOfSkelX v.label).st = .s10L ∨ (rowOfSkelX v.label).st = .s10T := by rw [hst]; exact hc
    have hsm : SmallX p (rowOfSkelX v.label) := by
      refine smallX_chain hcs fun a ha => ?_
      rw [rowOfSkelX_f] at ha
      rw [ha, chainAxis_atom] at hax
      omega
    have hrn : (liftT v).label.rn = rowOfSkelX v.label := by rw [liftT_label]; rfl
    rw [hrn]
    refine ⟨chain_rowOK hv hsm, fun hp => ?_⟩
    exfalso
    have h5 := hp.1
    rcases hcs with hcs | hcs <;> rw [hcs] at h5 <;> cases h5
  · rcases hseg with ⟨n, m, s', e, new, -, -, -, rfl⟩ | ⟨X, Y, rfl⟩
    · rw [segT_label] at hchip; simp at hchip
    · refine ⟨?_, fun hp => ?_⟩
      · simp [tNode, tRow, RowOKX]
      · have h5 := hp.1
        simp [tNode, tRow] at h5

/-- **The cell facts of an `s10B` row**: `fttt` and `ftt` are cells (a generated op-10 row's two formulas are
cells; `genX_rowOK` at the row's own axis bound). -/
theorem s10B_cells {v : NTree SkelX} (hv : GenNode R v) {a : ℕ} (hst : (rowOfSkelX v.label).st = .s10)
    (hftth : (rowOfSkelX v.label).ftth = .atom a) :
    (rowOfSkelX v.label).fttt.isCell = true ∧ (rowOfSkelX v.label).ftt.isCell = true := by
  obtain ⟨m, hm⟩ := hv
  have hsm : SmallX (a + 1) (rowOfSkelX v.label) := by
    simp only [SmallX, hst]
    intro a' ha'; rw [hftth] at ha'; cases ha'; omega
  have hok := genX_rowOK hm hsm
  simp only [RowOKX, hst] at hok
  exact ⟨hok.2.2.2.2.2.1, hok.2.2.2.2.2.2⟩

/-- A big (`s0B` / `s10B`) node of the J-9 A tree is a reclassified generated node. -/
theorem big_node_gen {u : NTree LX9} (hu : Node9 R t u) (hch : u.label.chip = .s0B ∨ u.label.chip = .s10B) :
    ∃ v, GenNode R v ∧ u.label.rn = rowOfSkelX v.label := by
  rcases hu with ⟨v, -, hv, rfl⟩ | ⟨v, -, -, rfl⟩ | ⟨n', m, s', e, new, -, -, -, rfl⟩ | ⟨X, Y, rfl⟩
  · exact ⟨v, hv, by rw [genX9T_label]⟩
  · rw [liftT_label] at hch; simp [liftL] at hch
  · rw [segT_label] at hch; simp at hch
  · simp [tNode] at hch

end Old

/-! ## 3. The segment index of an `s10S` row -/

section Seg
variable {p : ℕ} {R : Nock.Jet.Registry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}

/-- The invariant of the J-9 A tree: a node class, in the tree, and an `s10S` node's axis is the axis of an
`s10B` node of the tree. -/
def Good (R : Nock.Jet.Registry) (t : NTree SkelX) (w : NTree LX9) : Prop :=
  InTree (genX9T t) w ∧ Node9 R t w ∧ (w.label.chip = .s10S →
    ∃ u', InTree (genX9T t) u' ∧ u'.label.chip = .s10B ∧ u'.label.n = w.label.n)

theorem good_step {u c : NTree LX9} (hg : Good R t u) (hc : c ∈ u.children) : Good R t c := by
  obtain ⟨hin, hnode, hw⟩ := hg
  refine ⟨InTree_trans hin (.sub hc (.here c)), node9_children hnode c hc, fun hS => ?_⟩
  rcases hnode with ⟨v, hvt, hv, rfl⟩ | ⟨v, hv, hax, rfl⟩ | hseg
  · rw [genX9T_children] at hc
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
    by_cases hB : (chipOf v.label).1 = .s10B ∧ c0.label.state.isChain = true
    · have hk : kid9 v.label c0 (genX9T c0) =
          segT (chipOf v.label).2 (top (chipOf v.label).2) (kidE v.label 1) v.label.evaluation := by
        simp [kid9, hB.1, hB.2]
      rw [hk] at hS ⊢
      refine ⟨genX9T v, hin, ?_, ?_⟩
      · rw [genX9T_label]; exact hB.1
      · rw [genX9T_label, segT_label]
    · have hk : kid9 v.label c0 (genX9T c0) = genX9T c0 := by
        unfold kid9; simp [hB]
      rw [hk, genX9T_label] at hS
      exact absurd hS (chipOf_ne_s10S _)
  · simp only [liftT, mapNTree_children] at hc
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hc
    simp [mapNTree_label, liftL] at hS
  · rcases hseg with ⟨n, m, s', e, new, hn, hm, he, rfl⟩ | ⟨X, Y, rfl⟩
    · have hu1 : (segT n m s' e).label.chip = .s10S := by rw [segT_label]
      obtain ⟨u', hu', hB, hn'⟩ := hw hu1
      have key : ∀ c' ∈ (segT n m s' e).children, c'.label.chip = .s10S → c'.label.n = n := by
        intro c' hc' hS'
        cases m with
        | zero =>
          simp only [segT, segNode, NTree.children, List.mem_cons, List.mem_singleton, List.not_mem_nil,
            or_false] at hc'
          rcases hc' with rfl | rfl
          · simp [liftT_label, liftL] at hS'
          · simp [tNode] at hS'
        | succ m =>
          simp only [segT, segNode, NTree.children, List.mem_cons, List.mem_singleton, List.not_mem_nil,
            or_false] at hc'
          rcases hc' with rfl | rfl
          · simp [liftT_label, liftL] at hS'
          · rw [segT_label]
      refine ⟨u', hu', hB, ?_⟩
      rw [hn', key c hc hS, segT_label]
    · simp [tNode, NTree.children] at hc

/-- **Every `s10S` node of the J-9 A tree is at the axis of an `s10B` node of the tree.** -/
theorem s10S_axis (h : genX R fuel s f = some (t, r)) {u : NTree LX9} (hu : InTree (genX9T t) u)
    (hS : u.label.chip = .s10S) :
    ∃ u', InTree (genX9T t) u' ∧ u'.label.chip = .s10B ∧ u'.label.n = u.label.n := by
  have hroot : Good R t (genX9T t) :=
    ⟨.here _, Or.inl ⟨t, .here t, genNode_of h, rfl⟩, fun hS' => by
      rw [genX9T_label] at hS'; exact absurd hS' (chipOf_ne_s10S _)⟩
  have key : ∀ {c w : NTree LX9}, InTree c w → Good R t c → Good R t w := by
    intro c w hcw
    induction hcw with
    | here => exact id
    | sub hs _ ih => exact fun hg => ih (good_step hg hs)
  exact (key hu hroot).2.2 hS

/-- **The segment index of an `s10S` row is below `63`** (the axis is within the cap, or a field element and
then it has at most two limbs). -/
theorem s10S_m_lt (hpG : p = Nock.Atoms.p) (h : genX R fuel s f = some (t, r)) (hax9 : ProgAxOK9A p t)
    {u : NTree LX9} (hu : InTree (genX9T t) u) (hS : u.label.chip = .s10S) (hsem : SemN9 R u.label) :
    u.label.m < 63 := by
  obtain ⟨u', hu', hB, hn⟩ := s10S_axis h hu hS
  have hmem : u'.label.n ∈ axAtoms9 (rowsOfT9 t) := by
    refine mem_axAtoms9.2 ⟨u'.label, ?_, Or.inr hB, rfl⟩
    simp only [rowsOfT9, List.toList_toArray, List.mem_map]
    exact ⟨u', (mem_bfsForest _ _).2 ⟨_, List.mem_singleton_self _, hu'⟩, rfl⟩
  obtain ⟨-, hc⟩ := axAtoms9_cap h hax9 _ hmem
  rw [hn] at hc
  simp only [SemN9, hS] at hsem
  obtain ⟨hn0, hm, -⟩ := hsem
  rcases hc with hlt | hcap
  · have h64 := lt64_of_G hpG hlt
    have : top u.label.n < 2 := by
      unfold top
      exact Nat.log_lt_of_lt_pow hn0 (by norm_num at h64 ⊢; omega)
    omega
  · exact le_top_lt_63 hcap hn0 hm

end Seg

/-! ## 4. The base gates at one node -/

section Node
variable {p : ℕ} [Fact p.Prime] {R : Nock.Jet.Registry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}

/-- The publics of the claim read as the root row's handle columns. -/
theorem pubOK9_of (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (l : LX9)
    (fst lst : ZMod p) (pub : ℕ → ZMod p)
    (hfst : fst = 0 ∨ (l.chip ≠ .s10S ∧ pub 0 = hk H l.rn.s ∧ pub 1 = hv H l.rn.s ∧ pub 2 = hk H l.rn.f ∧
      pub 3 = hv H l.rn.f ∧ pub 4 = hk H l.rn.e ∧ pub 5 = hv H l.rn.e)) :
    PubOK9 (colX9 H pd idOf l fst lst) pub := by
  rcases hfst with h0 | ⟨hne, q0, q1, q2, q3, q4, q5⟩
  · left
    cases hch : l.chip <;> simp [colX9, hch, colS0B, colS10B, colS10S, colX, h0]
  · right
    cases hch : l.chip
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [colX9, hch, colX, hN, q0, q1, q2, q3, q4, q5]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [colX9, hch, colS0B, colX, hN, q0, q1, q2, q3, q4, q5]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [colX9, hch, colS10B, colX, hN, q0, q1, q2, q3, q4, q5]
    · exact absurd hch hne

/-- **The base gates at one node of the J-9 A tree** (`fst` is `0`, or the root's flag `1`). -/
theorem base_node (hpG : p = Nock.Atoms.p) (h : genX R fuel s f = some (t, r))
    (hax9 : ProgAxOK9A p t) (hop5 : ComplJ8.ProgOp5OK p t) (H : Noun → ℕ × ℕ)
    (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (hH : HdlOK (ringChar (ZMod p)) H)
    (hpair : ∀ u, InTree t u → isPair H (rowOfSkelX u.label) → PairOK (F := ZMod p) (pd (rowOfSkelX u.label)))
    (pubVal : ℕ → ZMod p)
    (hpub : pubVal 0 = hk H s ∧ pubVal 1 = hv H s ∧ pubVal 2 = hk H f ∧ pubVal 3 = hv H f ∧
      pubVal 4 = hk H r ∧ pubVal 5 = hv H r)
    {u : NTree LX9} (hu : InTree (genX9T t) u) {fst lst : ZMod p}
    (hfst : fst = 0 ∨ (u = genX9T t ∧ fst = 1)) :
    (∀ g ∈ arithGatesX9, evalQX g (hEnvX9 H pd idOf u.label fst lst pubVal) = 0) ∧
      (∀ g ∈ (eqGatesX9 (F := ℚ)), evalQX g.gate (hEnvX9 H pd idOf u.label fst lst pubVal) = 0) := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp63 := hp63_of_G hpG
  have hp16 : 16 ≤ ringChar (ZMod p) := by rw [hrc]; omega
  have hnode := genX9T_inTree h hu
  have hsem := semN9_of_node9 hnode
  -- the publics
  have hlab := genX_label h
  have hP : fst = 0 ∨ (u.label.chip ≠ .s10S ∧ pubVal 0 = hk H u.label.rn.s ∧ pubVal 1 = hv H u.label.rn.s ∧
      pubVal 2 = hk H u.label.rn.f ∧ pubVal 3 = hv H u.label.rn.f ∧ pubVal 4 = hk H u.label.rn.e ∧
      pubVal 5 = hv H u.label.rn.e) := by
    rcases hfst with h0 | ⟨rfl, h1⟩
    · exact Or.inl h0
    · right
      have hrn : (genX9T t).label.rn = rowOfSkelX t.label := by rw [genX9T_label]
      rw [hrn, rowOfSkelX_s, rowOfSkelX_f, rowOfSkelX_e, hlab.1, hlab.2.1, hlab.2.2.1]
      rw [genX9T_label]
      exact ⟨chipOf_ne_s10S _, hpub⟩
  have hPold : PubOK H u.label.rn fst pubVal := by
    rcases hP with h0 | ⟨-, hp⟩
    · exact Or.inl h0
    · exact Or.inr hp
  cases hchip : u.label.chip
  · obtain ⟨hok, hpr⟩ := old_facts hpG h hax9 hop5 H pd hpair hnode hchip
    exact old_gates H pd idOf u.label fst lst pubVal hchip hH hp16 (by rw [hrc]; exact hok) hpr hPold
  · exact s0B_gates H pd idOf u.label fst lst pubVal hchip hsem hH hp16 (pubOK9_of H pd idOf _ _ _ _ hP)
  · obtain ⟨v, hv, hrn⟩ := big_node_gen hnode (Or.inr hchip)
    have hsem' := hsem
    simp only [SemN9, hchip] at hsem'
    obtain ⟨-, hst, hftth, -⟩ := hsem'
    rw [hrn] at hst hftth
    obtain ⟨hk1, hk2⟩ := s10B_cells hv hst hftth
    rw [← hrn] at hk1 hk2
    exact s10B_gates H pd idOf u.label fst lst pubVal hchip hsem hH hp16 hk1 hk2
      (pubOK9_of H pd idOf _ _ _ _ hP)
  · exact s10S_gates H pd idOf u.label fst lst pubVal hchip hsem hH (by rw [hrc]; exact hp63)
      (s10S_m_lt hpG h hax9 hu hchip hsem) (pubOK9_of H pd idOf _ _ _ _ hP)

end Node

/-! ## 5. `hbase9` -/

section Main
variable {p : ℕ} [Fact p.Prime] {R : Nock.Jet.Registry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}

/-- **`hbase` of `HonestSatX9.computeChipVCLHX9_honest_sat`, discharged for the honest J-9 A tree of a run**
(`t9 := genX9T t`, `idOf := idOf9 p nA H (fieldAx9 p (rowsOfT9 t))`).  Binders: the J-9 A axis binder `hax9` and
J-9 B's op-5 binder `hop5` (together the `SmallX` the old rows need); `hH`, `hpair` as in J-8 / J-9 B
(`hpair` over the nodes of `t`: the old rows are `rowOfSkelX` of nodes of `t`, chain rows are never pairs);
`hpub`: the claim publics (as `computeChipVCLHX_honest_sat`). -/
theorem hbase9 (hpG : p = Nock.Atoms.p) (h : genX R fuel s f = some (t, r))
    (hax9 : ProgAxOK9A p t) (hop5 : ComplJ8.ProgOp5OK p t) (H : Noun → ℕ × ℕ)
    (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (nA : ℕ)
    (hH : HdlOK (ringChar (ZMod p)) H)
    (hpair : ∀ u, InTree t u → isPair H (rowOfSkelX u.label) → PairOK (F := ZMod p) (pd (rowOfSkelX u.label)))
    {n : ℕ} (hN : n = (bfsForest [genX9T t]).length) (pubVal : ℕ → ZMod p)
    (hpub : pubVal 0 = hk H s ∧ pubVal 1 = hv H s ∧ pubVal 2 = hk H f ∧ pubVal 3 = hv H f ∧
      pubVal 4 = hk H r ∧ pubVal 5 = hv H r) :
    ∀ j < n,
      (∀ g ∈ arithGatesX9, evalQX g (hEnvX9 H pd (idOf9 p nA H (fieldAx9 p (rowsOfT9 t)))
        (rowAt9 (bfsForest [genX9T t]) (j + 1)) (fl1 (j + 1)) (llW (bfsForest [genX9T t]) (j + 1)) pubVal) = 0) ∧
      (∀ g ∈ (eqGatesX9 (F := ℚ)), evalQX g.gate (hEnvX9 H pd (idOf9 p nA H (fieldAx9 p (rowsOfT9 t)))
        (rowAt9 (bfsForest [genX9T t]) (j + 1)) (fl1 (j + 1)) (llW (bfsForest [genX9T t]) (j + 1)) pubVal) = 0) := by
  intro j hj
  have hjW : j < (bfsForest [genX9T t]).length := hN ▸ hj
  have hrow : rowAt9 (bfsForest [genX9T t]) (j + 1) = ((bfsForest [genX9T t])[j]'hjW).label := by
    simp [rowAt9, List.getElem?_eq_getElem hjW]
  have hmem : (bfsForest [genX9T t])[j]'hjW ∈ bfsForest [genX9T t] := List.getElem_mem hjW
  have hu : InTree (genX9T t) ((bfsForest [genX9T t])[j]'hjW) := by
    obtain ⟨c, hc, hcu⟩ := (mem_bfsForest _ _).1 hmem
    simp only [List.mem_singleton] at hc
    subst hc; exact hcu
  rw [hrow]
  refine base_node hpG h hax9 hop5 H pd _ hH hpair pubVal hpub hu ?_
  by_cases hj0 : j = 0
  · right
    subst hj0
    refine ⟨?_, by simp [fl1]⟩
    have := bfsForest_cons_eq [genX9T t] (List.cons_ne_nil _ _)
    simp only [this]
    simp
  · left
    simp [fl1]
    omega

end Main

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABase

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABase
#print axioms old_facts
#print axioms s10B_cells
#print axioms big_node_gen
#print axioms good_step
#print axioms s10S_axis
#print axioms s10S_m_lt
#print axioms pubOK9_of
#print axioms base_node
#print axioms hbase9
end Axioms
