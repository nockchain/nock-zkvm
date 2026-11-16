/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/WalkTreeX9.lean

  Labels are `CSt × RowVSX9`.

  One addition over the J-8 shape: `WF9 r` (an old chip state agrees with the base row's state),
  needed because `kidsX9 (.old st)` reads `r.base.st`, not `st`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.LocalVSX9
import Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeX9

open Nock Nock.Walk
open Nock.Edit (StateX)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX

noncomputable section

/-! ## 1. The label language -/

/-- **The fanout of a chip state.** -/
def fanS9 : CSt → ℕ
  | .old st => WalkLblVSX.fanS st
  | .s0B => 0
  | .s10B => 3
  | .s10S => 2

theorem fanS9_le (c : CSt) : fanS9 c ≤ 3 := by
  cases c with
  | old st => exact WalkLblVSX.fanS_le st
  | s0B => simp [fanS9]
  | s10B => simp [fanS9]
  | s10S => simp [fanS9]

/-- **Well-formedness**: an old chip state agrees with the base row's state. -/
def WF9 (r : RowVSX9) : Prop := ∀ st, r.cs = .old st → r.base.st = st

theorem kidsX9_length (r : RowVSX9) (h : WF9 r) : (kidsX9 r).length = fanS9 r.cs := by
  obtain ⟨cs, b, l⟩ := r
  cases cs with
  | old st =>
    have hs : b.st = st := h st rfl
    simp only [kidsX9, fanS9]
    rw [WalkLblVSX.kidsX_length, hs]
  | s0B => simp [kidsX9, fanS9]
  | s10B => simp [kidsX9, fanS9]
  | s10S => simp [kidsX9, fanS9]

/-- A child row. -/
def childRow9 (t : TripX) : RowVSX9 := ⟨.old .s0, WalkLblVSX.childRow t, (0, 0)⟩

@[simp] theorem childRow9_trip (t : TripX) : (childRow9 t).trip = t := by
  simp [childRow9, RowVSX9.trip]

section Enc
variable {K : Type} [Field K]

/-- **The encoding of a walk label**: its own `(s, f, e)`. -/
def enc9 (a : CSt × RowVSX9) : Fin 6 → K := encT a.2.trip

/-- **The commit relation of the compute walk at J-9 A.** -/
def FV9 (a : CSt × RowVSX9) (xout : Fin 3 → Option (CSt × RowVSX9)) : Prop :=
  a.1 = a.2.cs ∧ ∀ j : Fin 3, ((j : ℕ) < fanS9 a.1 ↔ xout j ≠ none) ∧
    ∀ c, xout j = some c → enc9 (K := K) c = encT ((kidsX9 a.2).getD j trip0)

end Enc

/-- Every handle value of a row (and its routed label) is below `p`. -/
def SmallR9 (p : ℕ) (r : RowVSX9) : Prop := SmallR p r.base ∧ r.lab.1 < p ∧ r.lab.2 < p

section Rows
variable (rows : ℕ → RowVSX9)

def lblOf9 (i : ℕ) : CSt × RowVSX9 := ((rows i).cs, rows i)

def foOf9 (i : ℕ) : ℕ := fanS9 (rows i).cs

def clabOf9 (i l : ℕ) : CSt × RowVSX9 :=
  (CSt.old .s0, childRow9 ((kidsX9 (rows i)).getD (l - 1) trip0))

theorem foOf9_le (i : ℕ) : foOf9 rows i ≤ 3 := fanS9_le _

theorem fv_commit9 {K : Type} [Field K] (i : ℕ) :
    FV9 (K := K) (lblOf9 rows i)
      (fun j : Fin 3 => if (j : ℕ) < foOf9 rows i then some (clabOf9 rows i (j + 1)) else none) := by
  refine ⟨rfl, fun j => ⟨?_, ?_⟩⟩
  · by_cases h : (j : ℕ) < fanS9 (rows i).cs <;> simp [lblOf9, foOf9, h]
  · intro c hc
    simp only [foOf9] at hc
    by_cases hj : (j : ℕ) < fanS9 (rows i).cs
    · simp only [hj, if_true, Option.some.injEq] at hc
      subst hc
      simp [enc9, clabOf9, lblOf9]
    · simp [hj] at hc

end Rows

/-! ## 2. The state separation and the event -/

section Sep
variable (K : Type) [Field K]

theorem fv_none_iff9 (a : CSt × RowVSX9) :
    FV9 (K := K) a (fun _ => none) ↔ a.1 = a.2.cs ∧ fanS9 a.1 = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := (h2 ⟨0, by decide⟩).1
    simp only [ne_eq, not_true_eq_false, iff_false, not_lt, Nat.le_zero] at this
    exact this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j => ⟨?_, fun c hc => by cases hc⟩⟩
    simp [h2]

/-- **The `StateSep` of the compute walk at J-9 A.** -/
def stVS9 : StateSep (FV9 (K := K)) where
  Sleaf s := fanS9 s = 0
  fanout := fanS9
  fanout_le := fanS9_le
  fanout_leaf _ h := h
  solely := by
    intro t ht
    obtain ⟨l, ch⟩ := t
    simp only [RVT] at ht
    obtain ⟨hF, -, hleaf⟩ := ht
    rw [hleaf, fv_none_iff9]
    exact ⟨fun h => ⟨hF.1, h⟩, fun h => h.2⟩
  dynamic := by
    intro s d xout hF i
    exact (hF.2 i).1

theorem fv_respects9 : RespectsChildLabels (FV9 (K := K)) (enc9 (K := K)) := by
  intro a xout xout' hmap hF
  refine ⟨hF.1, fun j => ⟨?_, ?_⟩⟩
  · rw [(hF.2 j).1]
    have hj := hmap j
    constructor
    · intro hne hn; rw [hn] at hj; apply hne
      cases hx : xout j with
      | none => rfl
      | some c => rw [hx] at hj; simp at hj
    · intro hne hn; rw [hn] at hj; apply hne
      cases hx : xout' j with
      | none => rfl
      | some c => rw [hx] at hj; simp at hj
  · intro c' hc'
    have hj := hmap j
    rw [hc'] at hj
    cases hx : xout j with
    | none => rw [hx] at hj; simp at hj
    | some c =>
      rw [hx] at hj
      simp only [Option.map_some, Option.some.injEq] at hj
      rw [← hj]
      exact (hF.2 j).2 c hx

end Sep

section Event
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

open scoped Classical in
/-- **The compute walk event at J-9 A** (`kroots = 1`). -/
def cwEvent9 (rows : ℕ → RowVSX9) (h : ℕ) : Finset (K × K) :=
  Finset.univ.filter fun p : K × K =>
    (1 + Sf (foOf9 rows) h = h ∧ BFSValidF 1 (foOf9 rows) h) ∧
    (∃ ln count acc : ℕ → K,
      WalkSat (fun i => rlc p.2 (enc9 (lblOf9 rows i))) (fun i l => rlc p.2 (enc9 (clabOf9 rows i l)))
        (foOf9 rows) ln count acc p.1
        (∑ i ∈ Finset.Icc 1 1, rlc p.2 (enc9 (lblOf9 rows i)) * p.1 ^ i) (p.1 ^ 1) h ∧ acc h = 0) ∧
    ¬ ForestReconGoal (stVS9 K) (lblOf9 rows) 1 h

open scoped Classical in
theorem cwEvent9_card (rows : ℕ → RowVSX9) (h : ℕ) :
    (cwEvent9 (K := K) rows h).card ≤ Fintype.card K * h + Fintype.card K * (h * (6 - 1)) := by
  by_cases hyp : 1 + Sf (foOf9 rows) h = h ∧ BFSValidF 1 (foOf9 rows) h
  · have hc := Walk_IOP_forest_final_card_of_label (stVS9 K) (enc9 (K := K)) (fv_respects9 K)
      (enc9 (K := K)) (fun _ _ h => h) (lblOf9 rows) (clabOf9 rows) (foOf9 rows) (kroots := 1) (h := h)
      le_rfl hyp.1 hyp.2 (foOf9_le rows) (fun _ _ _ => rfl) (fun i _ _ => fv_commit9 rows i)
    refine le_trans (Finset.card_le_card ?_) hc
    intro p hp
    simp only [cwEvent9, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.2.1, hp.2.2⟩
  · have : cwEvent9 (K := K) rows h = ∅ := by
      ext p; simp [cwEvent9, hyp]
    rw [this]; simp

theorem cwEvent9_card_le (rows : ℕ → RowVSX9) {h H : ℕ} (hH : h ≤ H) :
    (cwEvent9 (K := K) rows h).card ≤ Fintype.card K * (6 * H) := by
  refine (cwEvent9_card rows h).trans ?_
  have : Fintype.card K * h + Fintype.card K * (h * (6 - 1)) = Fintype.card K * (6 * h) := by ring_nf
  rw [this]
  exact Nat.mul_le_mul_left _ (by omega)

open scoped Classical in
theorem goal_of_not_mem9 (rows : ℕ → RowVSX9) {h : ℕ} (htile : 1 + Sf (foOf9 rows) h = h)
    (hval : BFSValidF 1 (foOf9 rows) h) {α γ : K}
    (hw : ∃ ln count acc : ℕ → K,
      WalkSat (fun i => rlc γ (enc9 (lblOf9 rows i))) (fun i l => rlc γ (enc9 (clabOf9 rows i l)))
        (foOf9 rows) ln count acc α
        (∑ i ∈ Finset.Icc 1 1, rlc γ (enc9 (lblOf9 rows i)) * α ^ i) (α ^ 1) h ∧ acc h = 0)
    (hout : (α, γ) ∉ cwEvent9 (K := K) rows h) :
    ForestReconGoal (stVS9 K) (lblOf9 rows) 1 h := by
  by_contra hng
  exact hout (by simp only [cwEvent9, Finset.mem_filter, Finset.mem_univ, true_and]
                 exact ⟨⟨htile, hval⟩, hw, hng⟩)

end Event

/-! ## 3. The tree -/

section Tree
variable {K : Type} [Field K]

theorem smallT_trip9 {p : ℕ} {r : RowVSX9} (h : SmallR9 p r) : SmallT p r.trip :=
  smallT_trip h.1

theorem smallT_kids9 {p : ℕ} (hp : 0 < p) {r : RowVSX9} (h : SmallR9 p r) :
    ∀ t ∈ kidsX9 r, SmallT p t := by
  obtain ⟨hb, hl1, hl2⟩ := h
  have g : ∀ x ∈ [r.base.s, r.base.f, r.base.e, r.base.sf1, r.base.sf2, r.base.fh, r.base.ft,
      r.base.fth, r.base.ftt, r.base.ftth, r.base.fttt, r.base.m], x.1 < p ∧ x.2 < p := hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
  obtain ⟨hs, hf, he, h1, h2, hfh, hft, hfth, hftt, hftth, hfttt, hm⟩ := g
  intro t ht
  unfold kidsX9 at ht
  split at ht
  · exact smallT_kids hp hb t ht
  · simp at ht
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨hs, hfttt, h1⟩
    · exact ⟨hs, hftt, h2⟩
    · exact ⟨h2, ⟨hl1, hl2⟩, he⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨hs, hm, he⟩
    · exact ⟨hftth, ⟨hl1, hl2⟩, hfttt⟩

theorem rvt_child9 {F : (CSt × RowVSX9) → (Fin 3 → Option (CSt × RowVSX9)) → Prop}
    {c s : NTree (CSt × RowVSX9)} (ht : RVT F c) (hs : s ∈ c.children) : RVT F s := by
  obtain ⟨l, ch⟩ := c
  simp only [RVT] at ht
  exact ht.2.1 s hs

theorem rvt_sub9 {F : (CSt × RowVSX9) → (Fin 3 → Option (CSt × RowVSX9)) → Prop}
    {t u : NTree (CSt × RowVSX9)} (ht : RVT F t) (hu : InTree t u) : RVT F u := by
  induction hu with
  | here => exact ht
  | sub hs _ ih => exact ih (rvt_child9 ht hs)

/-- **The tree of the compute walk at J-9 A** (`kroots = 1`). -/
theorem tree_of_goal9 (p : ℕ) [CharP K p] (hp0 : 0 < p) (rows : ℕ → RowVSX9) {h : ℕ} (hh : 1 ≤ h)
    (hsmall : ∀ i, 1 ≤ i → i ≤ h → SmallR9 p (rows i) ∧ WF9 (rows i))
    (hG : ForestReconGoal (stVS9 K) (lblOf9 rows) 1 h) :
    ∃ t : NTree (CSt × RowVSX9), t.label = lblOf9 rows 1 ∧
      (∀ u, InTree t u → ∃ i, 1 ≤ i ∧ i ≤ h ∧ u.label = lblOf9 rows i) ∧
      (∀ u, InTree t u → u.children.map (fun c => c.label.2.trip) = kidsX9 u.label.2) := by
  obtain ⟨ts, hlen, hrvt, hlab, hfan, -⟩ := hG
  obtain ⟨t, rfl⟩ : ∃ t, ts = [t] := by
    match ts, hlen with
    | [t], _ => exact ⟨t, rfl⟩
  have hmem : ∀ u, InTree t u → u ∈ bfsForest [t] := fun u hu =>
    (mem_bfsForest [t] u).mpr ⟨t, List.mem_singleton_self _, hu⟩
  have hrow : ∀ u, InTree t u → ∃ i, 1 ≤ i ∧ i ≤ h ∧ u.label = lblOf9 rows i := by
    intro u hu
    have hl : u.label ∈ (bfsForest [t]).map NTree.label := List.mem_map_of_mem (hmem u hu)
    rw [hlab] at hl
    obtain ⟨i, hi, hie⟩ := List.mem_map.mp hl
    rw [List.mem_range'_1] at hi
    exact ⟨i, hi.1, by omega, hie.symm⟩
  refine ⟨t, ?_, hrow, ?_⟩
  · have hb : bfsForest [t] = [t] ++ bfsForest ([t].flatMap NTree.children) :=
      bfsForest_cons_eq [t] (List.cons_ne_nil _ _)
    have hr : List.range' 1 h = 1 :: List.range' 2 (h - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
      rw [List.range'_succ]; rfl
    rw [hb, hr] at hlab
    simp only [List.singleton_append, List.map_cons, List.cons.injEq] at hlab
    exact hlab.1
  · intro u hu
    have hR : RVT (FV9 (K := K)) u := rvt_sub9 (hrvt t (List.mem_singleton_self _)) hu
    obtain ⟨i, hi1, hih, hui⟩ := hrow u hu
    have hfo : fanS9 u.label.1 = u.children.length := hfan u (hmem u hu)
    obtain ⟨l, ch⟩ := u
    simp only [RVT] at hR
    obtain ⟨hF, -, -⟩ := hR
    simp only [NTree.label, NTree.children] at hfo hui ⊢
    have hst : l.1 = l.2.cs := hF.1
    have hwf : WF9 l.2 := by rw [hui]; exact (hsmall i hi1 hih).2
    have hlen : ch.length = (kidsX9 l.2).length := by rw [kidsX9_length _ hwf, ← hst, hfo]
    have hsl : SmallR9 p l.2 := by rw [hui]; exact (hsmall i hi1 hih).1
    refine List.ext_getElem (by rw [List.length_map, hlen]) ?_
    intro j hj1 hj2
    rw [List.length_map] at hj1
    have hj3 : j < 3 := by have := fanS9_le l.1; omega
    have hc := (hF.2 ⟨j, hj3⟩).2 (ch[j]).label (by
      simp [NTree.childLabel, NTree.childOpt, NTree.children, hj1])
    have hcin : InTree (NTree.node l ch) ch[j] := InTree.sub (List.getElem_mem hj1) (InTree.here _)
    obtain ⟨i', hi1', hih', hci⟩ := hrow _ (inTree_trans hu hcin)
    have hcs : SmallR9 p (ch[j]).label.2 := by rw [hci]; exact (hsmall i' hi1' hih').1
    have hk : (kidsX9 l.2).getD j trip0 = (kidsX9 l.2)[j] := by
      rw [List.getD_eq_getElem]
    rw [hk] at hc
    simp only [List.getElem_map]
    exact encT_inj (smallT_trip9 hcs) (smallT_kids9 hp0 hsl _ (List.getElem_mem _)) hc

end Tree

end

#print axioms tree_of_goal9
#print axioms goal_of_not_mem9
#print axioms cwEvent9_card
#print axioms fv_respects9

end Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeX9
