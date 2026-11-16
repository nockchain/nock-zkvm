/-
J-9 A L7 balance (PARTIAL): the read facts of the J-9 A cell walk, `hslotA` / `hrootA`.

Done here: `segReads_slot`, the segment-chain part of `hslotA`: if the axis `n` (≠ 0) is a defined slot of `X`, every
segment read `(X_m, segRd n m)` of the chain `segReads n m X` is a defined slot.  (Used for `axChainReadsK9`, whose
chains start at an `s0B` row's subject / `s10B` row's result, a defined slot of the big axis `n`.)

Not done here: the case analysis of `walkReadsX9` over `Node9`
(`genX9T_inTree`, as in `ComplJ9AReads.walkDepthOK_X9`) for `hslotA`, and the whole of `hrootA`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ADataRec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalW

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.J9A.NounAx (top segAx segRd nxtAx segAx_decomp segAx_next segRd_pos nxtAx_lt_pow)
open Nock.J9A.NounComp (slot_comp)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData (segReads)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (segX)

/-- **Every segment read of a chain on a defined slot is a defined slot.** -/
theorem segReads_slot (n : ℕ) (hn : n ≠ 0) :
    ∀ m, m ≤ top n → ∀ X : Noun, (Noun.slot (segAx n m) X).isSome →
      ∀ x ∈ segReads n m X, (Noun.slot x.2 x.1).isSome := by
  intro m
  induction m with
  | zero =>
    intro hm X hs x hx
    simp only [segReads, List.mem_singleton] at hx
    subst hx
    have h0 := segAx_decomp n 0 hm
    simp only [Nat.mul_zero, pow_zero, mul_one, Nat.mod_one, add_zero] at h0
    show (Noun.slot (segRd n 0) X).isSome
    rw [← h0]
    exact hs
  | succ m ih =>
    intro hm X hs x hx
    have hdec := segAx_decomp n (m + 1) hm
    have hrd := segRd_pos hn (m + 1) hm
    have hr : n % 2 ^ (32 * (m + 1)) < 2 ^ (32 * (m + 1)) := nxtAx_lt_pow n (m + 1)
    have hcomp := slot_comp (segRd n (m + 1)) (32 * (m + 1)) (n % 2 ^ (32 * (m + 1))) X hrd hr
    rw [hdec, hcomp] at hs
    obtain ⟨y, hy⟩ : ∃ y, Noun.slot (segRd n (m + 1)) X = some y := by
      cases h : Noun.slot (segRd n (m + 1)) X with
      | none => simp [h] at hs
      | some y => exact ⟨y, rfl⟩
    have hnx := segAx_next n (m + 1) hm (by omega)
    simp only [Nat.add_sub_cancel] at hnx
    have hs2 : (Noun.slot (segAx n m) y).isSome := by
      rw [hnx]
      unfold nxtAx
      simpa [hy] using hs
    simp only [segReads, List.mem_cons] at hx
    rcases hx with rfl | hx
    · show (Noun.slot (segRd n (m + 1)) X).isSome
      rw [hy]; rfl
    · have hsegx : segX n (m + 1) X = y := by simp [segX, hy]
      rw [hsegx] at hx
      exact ih (by omega) y hs2 x hx

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads (walkReadsX9 consEntriesX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun (axChainReadsK9 axKeys9 axKeys9_read)

/-- **Every J-9 A walk read is a defined slot** (case split over the node classes of the J-9 A tree). -/
theorem walkReadsX9_slot {R : Nock.Jet.Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) :
    ∀ x ∈ walkReadsX9 (rowsOfT9 t), (Noun.slot x.2 x.1).isSome := by
  intro x hx
  simp only [walkReadsX9, List.mem_filter, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨⟨l, hl, y, hy, rfl⟩, -⟩ := hx
  simp only [rowsOfT9, List.toList_toArray, List.mem_map] at hl
  obtain ⟨u, hu, rfl⟩ := hl
  obtain ⟨c, hc, hcu⟩ := (mem_bfsForest _ _).1 hu
  simp only [List.mem_singleton] at hc
  subst hc
  have hnode := genX9T_inTree h hcu
  have hsem := semN9_of_node9 hnode
  simp only
  rcases hnode with ⟨v, hvt, hv, rfl⟩ | ⟨v, hv, hax, rfl⟩ | ⟨nn, m, s0, e0, new, hn, hm, he, rfl⟩ | ⟨X, Y, rfl⟩
  · rw [genX9T_label] at hy hsem
    unfold SemN9 at hsem
    unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads.consEntriesX9 at hy
    simp only at hy hsem
    cases hch : (chipOf v.label).1 <;> simp only [hch] at hy hsem
    · have := (Nock.Edit.GenX.consEntriesX_sound v.label hsem.1 y hy).2
      simp [this]
    · simp at hy
    · simp at hy
    · exact absurd hch (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads.chipOf_ne_s10S _)
  · rw [liftT_label] at hy
    simp only [Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads.consEntriesX9, liftL] at hy
    have := (Nock.Edit.GenX.consEntriesX_sound v.label (chainNode_rowSem R hv) y hy).2
    simp [this]
  · rw [segT_label] at hy hsem
    unfold SemN9 at hsem
    simp only [Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads.consEntriesX9, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] at hy hsem
    obtain ⟨-, -, -, -, -, h1, h2⟩ := hsem
    rcases hy with rfl | rfl
    · simp [h1]
    · simp [h2]
  · simp [tNode, Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads.consEntriesX9, tRow,
      Nock.Edit.GenX.consEntriesX] at hy

/-- **Every axis-chain segment read is a defined slot** (each key `(X, n)` has `n` a defined slot of `X`). -/
theorem axChainReadsK9_slot {R : Nock.Jet.Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) :
    ∀ x ∈ axChainReadsK9 (rowsOfT9 t), (Noun.slot x.2 x.1).isSome := by
  intro x hx
  simp only [axChainReadsK9, List.mem_filter, List.mem_flatMap] at hx
  obtain ⟨⟨k, hk, hl⟩, -⟩ := hx
  obtain ⟨hbig, Y, hY⟩ := axKeys9_read h hk
  have hn0 : k.2 ≠ 0 := by
    have : (2 : ℕ) ^ 62 > 0 := by positivity
    omega
  exact segReads_slot k.2 hn0 (top k.2) le_rfl k.1 (by rw [Nock.J9A.NounAx.segAx_top, hY]; rfl) x hl

/-- **`hslotA`**: every J-9 A cell-walk read is a defined slot. -/
theorem hslotA {R : Nock.Jet.Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) :
    ∀ x ∈ ComplJ9ADataRec.readsA t, (Noun.slot x.2 x.1).isSome := by
  intro x hx
  unfold ComplJ9ADataRec.readsA at hx
  rcases List.mem_append.1 hx with hx | hx
  · exact walkReadsX9_slot h x hx
  · exact axChainReadsK9_slot h x hx

/-! ## `hrootA`: the roots of the J-9 A cell-walk reads are cells of the table -/

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (j8DataOf ClP)

/-- `y` is an atom or a member of `C`. -/
def PQ (C : List Noun) (y : Noun) : Prop := y.isCell = true → y ∈ C

/-- The four noun fields a read root can be (`s`, `e`, `sf1`, `sf2`) are `PQ`. -/
def QR (C : List Noun) (r : RowNX) : Prop := PQ C r.s ∧ PQ C r.e ∧ PQ C r.sf1 ∧ PQ C r.sf2

theorem PQ_atom (C : List Noun) (v : ℕ) : PQ C (.atom v) := fun h => by simp [Noun.isCell] at h

/-- **A table closed under children is closed under slots.** -/
theorem PQ_slot {C : List Noun} (hcl : ClP C []) (a : ℕ) :
    ∀ {y c : Noun}, PQ C c → Noun.slot a c = some y → PQ C y := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro y c hc h
  rcases Nat.lt_or_ge a 2 with ha | ha
  · interval_cases a
    · simp [slot_zero] at h
    · simp only [Noun.slot, Option.some.injEq] at h; subst h; exact hc
  · obtain ⟨l, r, hp, rfl⟩ := (slot_some_iff ha c y).1 h
    have hb := ih (a / 2) (by omega) hc hp
    have hlr : Noun.cell l r ∈ C := hb rfl
    have hcl' := hcl l r hlr (by simp)
    intro hy
    split_ifs at hy ⊢
    · cases l with
      | atom _ => simp [Noun.isCell] at hy
      | cell x y => exact hcl'.1 x y rfl
    · cases r with
      | atom _ => simp [Noun.isCell] at hy
      | cell x y => exact hcl'.2 x y rfl

theorem PQ_segX {C : List Noun} (hcl : ClP C []) (n m : ℕ) {s : Noun} (hs : PQ C s) : PQ C (segX n m s) := by
  unfold segX
  cases h : Noun.slot (segRd n m) s with
  | none => exact PQ_atom C 0
  | some y => exact PQ_slot hcl _ hs h

theorem segReads_PQ {C : List Noun} (hcl : ClP C []) (n : ℕ) :
    ∀ m (X : Noun), PQ C X → ∀ x ∈ segReads n m X, PQ C x.1 := by
  intro m
  induction m with
  | zero =>
    intro X hX x hx
    simp only [segReads, List.mem_singleton] at hx
    subst hx; exact hX
  | succ m ih =>
    intro X hX x hx
    simp only [segReads, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hX
    · exact ih _ (PQ_segX hcl n (m + 1) hX) x hx

theorem rowOfSkelX_s (sk : SkelX) : (rowOfSkelX sk).s = sk.subject := by
  unfold rowOfSkelX; split <;> rfl

theorem rowOfSkelX_e (sk : SkelX) : (rowOfSkelX sk).e = sk.evaluation := by
  unfold rowOfSkelX; split <;> rfl

theorem chain_child {old e : Noun} {k a : ℕ} {w : NTree SkelX} (hw : w ∈ (genChainF old e k a).children) :
    ∃ k' a', w = genChainF old e k' a' := by
  cases k with
  | zero => simp [genChainF] at hw
  | succ k =>
    unfold genChainF at hw
    split_ifs at hw
    · simp only [mkX_children, List.mem_singleton] at hw
      exact ⟨k, a / 2, hw⟩
    · simp at hw

theorem chain_QR {C : List Noun} {old e : Noun} (h1 : PQ C old) (h2 : PQ C e) (k a : ℕ) :
    QR C (rowOfSkelX (genChainF old e k a).label) := by
  have key : ∀ st : StateX, (st = .s10L ∨ st = .s10T) →
      QR C (rowOfSkelX (mkX st old (.atom a) e []).label) := by
    intro st hst
    rcases hst with rfl | rfl
    · exact ⟨h1, h2, h1, h2⟩
    · exact ⟨h1, h2, PQ_atom C 0, PQ_atom C 0⟩
  cases k with
  | zero => exact key .s10T (Or.inr rfl)
  | succ k =>
    unfold genChainF
    split_ifs
    · exact key .s10L (Or.inl rfl)
    · exact key .s10T (Or.inr rfl)

/-- **The `QR` invariant is closed under the children of the J-9 A node classes.** -/
theorem good9_children {R : Nock.Jet.Registry} {t : NTree SkelX} {u : NTree LX9} {C : List Noun}
    (hcl : ClP C []) (hall : ∀ w, InTree t w → QR C (rowOfSkelX w.label))
    (hu : Node9 R t u) (hg : QR C u.label.rn) : ∀ c ∈ u.children, QR C c.label.rn := by
  rcases hu with ⟨v, hvt, hv, rfl⟩ | ⟨v, hv, hax, rfl⟩ | hseg
  · intro c' hc'
    rw [genX9T_children] at hc'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    have hct := inTree_child hvt hc
    unfold kid9
    split_ifs with hB
    · rw [segT_label]
      obtain ⟨hst, -, -⟩ := chipOf_s10B hB.1
      have h4 := hall v hvt
      have hs2 : (rowOfSkelX v.label).sf2 = kidE v.label 1 := by simp [rowOfSkelX, hst]
      have a1 : PQ C (kidE v.label 1) := hs2 ▸ h4.2.2.2
      have a2 : PQ C v.label.evaluation := (rowOfSkelX_e v.label) ▸ h4.2.1
      exact ⟨a1, a2, a1, a2⟩
    · rw [genX9T_label]
      exact hall c hct
  · obtain ⟨old, e, k, a, rfl, -⟩ := hv
    have hg' : QR C (rowOfSkelX (genChainF old e k a).label) := by
      rw [liftT_label] at hg; exact hg
    have h1 : PQ C old := by
      have := hg'.1; rwa [rowOfSkelX_s, (genChainF_label old e k a).1] at this
    have h2 : PQ C e := by
      have := hg'.2.1; rwa [rowOfSkelX_e, (genChainF_label old e k a).2.1] at this
    intro c hc
    simp only [liftT, mapNTree_children] at hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
    obtain ⟨k', a', rfl⟩ := chain_child hw
    rw [mapNTree_label]
    exact chain_QR h1 h2 k' a'
  · rcases hseg with ⟨n, m, s, e, new, hn, hm, he, rfl⟩ | ⟨X, Y, rfl⟩
    · rw [segT_label] at hg
      obtain ⟨h1, h2, -, -⟩ := hg
      have h1' : PQ C s := h1
      have h2' : PQ C e := h2
      cases m with
      | zero =>
        intro c hc
        simp only [segT, segNode, NTree.children, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl
        · rw [liftT_label]
          exact chain_QR h1' h2' _ _
        · exact ⟨PQ_segX hcl _ _ h1', PQ_segX hcl _ _ h2', PQ_atom C 0, PQ_atom C 0⟩
      | succ m =>
        intro c hc
        simp only [segT, segNode, NTree.children, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl
        · rw [liftT_label]
          exact chain_QR h1' h2' _ _
        · rw [segT_label]
          exact ⟨PQ_segX hcl _ _ h1', PQ_segX hcl _ _ h2', PQ_segX hcl _ _ h1', PQ_segX hcl _ _ h2'⟩
    · intro c hc
      simp [tNode, NTree.children] at hc

/-- **Every row of the J-9 A tree satisfies `QR`.** -/
theorem good9_all {R : Nock.Jet.Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun} {C : List Noun}
    (h : genX R n s f = some (t, r)) (hcl : ClP C []) (hall : ∀ w, InTree t w → QR C (rowOfSkelX w.label))
    {u : NTree LX9} (hu : InTree (genX9T t) u) : Node9 R t u ∧ QR C u.label.rn := by
  have key : ∀ {c u : NTree LX9}, InTree c u → Node9 R t c ∧ QR C c.label.rn → Node9 R t u ∧ QR C u.label.rn := by
    intro c u hcu
    induction hcu with
    | here => exact id
    | sub hs _ ih => exact fun hc => ih ⟨node9_children hc.1 _ hs, good9_children hcl hall hc.1 hc.2 _ hs⟩
  refine key hu ⟨Or.inl ⟨t, .here t, genNode_of h, rfl⟩, ?_⟩
  rw [genX9T_label]
  exact hall t (.here t)

theorem good9_rows {R : Nock.Jet.Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun} {C : List Noun}
    (h : genX R n s f = some (t, r)) (hcl : ClP C []) (hall : ∀ w, InTree t w → QR C (rowOfSkelX w.label)) :
    ∀ l ∈ (rowsOfT9 t).toList, QR C l.rn := by
  intro l hl
  simp only [rowsOfT9, List.toList_toArray, List.mem_map] at hl
  obtain ⟨u, hu, rfl⟩ := hl
  obtain ⟨c, hc, hcu⟩ := (mem_bfsForest _ _).1 hu
  simp only [List.mem_singleton] at hc
  subst hc
  exact (good9_all h hcl hall hcu).2

theorem consEntriesX_root4 (r : RowNX) : ∀ x ∈ consEntriesX r, x.1 = r.s ∨ x.1 = r.e ∨ x.1 = r.sf1 ∨ x.1 = r.sf2 := by
  intro x hx
  simp only [consEntriesX, List.mem_append] at hx
  rcases hx with (((h | h) | h) | h) | h <;> split_ifs at h <;>
    simp at h <;> rcases h with rfl | rfl <;> simp

/-- **`hrootA`**: the root of every J-9 A cell-walk read, when a cell, is in the table. -/
theorem hrootA {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {Rt : ℕ → Nock.Jet.Autogen.Tpl}
    {fuel : ℕ} {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) :
    ∀ x ∈ ComplJ9ADataRec.readsA t, x.1.isCell = true → x.1 ∈ (j8DataOf p Rg Rt hgen).cells := by
  have hcl : ClP (j8DataOf p Rg Rt hgen).cells [] := Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data.cells_closed _
  have hall : ∀ w, InTree t w → QR (j8DataOf p Rg Rt hgen).cells (rowOfSkelX w.label) := by
    intro w hw
    have hrow : rowOfSkelX w.label ∈ (j8DataOf p Rg Rt hgen).rows.toList :=
      Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads.rowOfSkelX_mem_rowsOfT hw
    have hP : ∀ y ∈ handleNounsX (rowOfSkelX w.label), PQ (j8DataOf p Rg Rt hgen).cells y := by
      intro y hy hc
      rcases Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data.handle_noun_cases p Rg Rt hgen hrow hy with
        ⟨_, hm⟩ | ⟨v, ev, _⟩ | ⟨v, ev, _⟩
      · exact hm
      · simp [ev, Noun.isCell] at hc
      · simp [ev, Noun.isCell] at hc
    exact ⟨hP _ (by simp [handleNounsX]), hP _ (by simp [handleNounsX]), hP _ (by simp [handleNounsX]),
      hP _ (by simp [handleNounsX])⟩
  have hrows := good9_rows hgen hcl hall
  intro x hx hc
  unfold ComplJ9ADataRec.readsA at hx
  rcases List.mem_append.1 hx with hx | hx
  · simp only [walkReadsX9, List.mem_filter, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨⟨l, hl, y, hy, rfl⟩, -⟩ := hx
    have hq := hrows l hl
    obtain ⟨q1, q2, q3, q4⟩ := hq
    simp only at hc ⊢
    unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads.consEntriesX9 at hy
    cases hch : l.chip <;> rw [hch] at hy
    · rcases consEntriesX_root4 _ y hy with h | h | h | h <;> rw [h] at hc ⊢
      · exact q1 hc
      · exact q2 hc
      · exact q3 hc
      · exact q4 hc
    · simp at hy
    · simp at hy
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact q1 hc
      · exact q2 hc
  · simp only [ComplJ9AChainsRun.axChainReadsK9, List.mem_filter, List.mem_flatMap] at hx
    obtain ⟨⟨k, hk, hl⟩, -⟩ := hx
    obtain ⟨l, hl', hlk⟩ := ComplJ9AChainsRun.mem_axKeys9.1 hk
    obtain ⟨q1, q2, q3, q4⟩ := hrows l hl'
    have hk1 : PQ (j8DataOf p Rg Rt hgen).cells k.1 := by
      unfold ComplJ9AChainsRun.axKey9 at hlk
      cases hch : l.chip <;> rw [hch] at hlk <;> simp at hlk
      · subst hlk; exact q1
      · subst hlk; exact q2
    exact segReads_PQ hcl k.2 (top k.2) k.1 hk1 x hl hc

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalW

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalW
#print axioms segReads_slot
#print axioms hslotA
#print axioms hrootA
end Axioms
