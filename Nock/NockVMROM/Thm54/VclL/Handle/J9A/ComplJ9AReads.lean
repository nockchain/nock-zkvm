/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AReads.lean

* `consEntriesX9`: the path reads of a J-9 A row: J-8's on old rows; none on `s0B` / `s10B` (the axis chip
    serves them through the `TAG_ax` consume); the segment pair `(s, seg)`, `(e, seg)` on `s10S` (the
    `slot2X` pair).
  * `walkReadsX9 rows`: the J-9 A walk read list (axis `≥ 2`).
  * **`walkDepthOK_X9`**: on a generated run, the J-9 A binder `WalkDepthOK9A (rowsOfT t)` gives `WalkDepthOK` on EVERY J-9 A
    walk read: old `s0` / `s10` rows read below `2^62` (`SemN9`), old chain rows sit at axes `< 2^62` (`Node9`),
    segment reads at `segRd < 2^33`; only the `s9` / `s5` reads of `t`'s own rows use the binder. -/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABinders
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AGen

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen
open Nock.J9A.NounAx (top segAx segRd)

/-- The path reads of a J-9 A row. -/
def consEntriesX9 (l : LX9) : List PEnt :=
  match l.chip with
  | .old => consEntriesX l.rn
  | .s0B => []
  | .s10B => []
  | .s10S => [(l.rn.s, segRd l.n l.m, l.rn.ftth), (l.rn.e, segRd l.n l.m, l.rn.fttt)]

/-- **The J-9 A walk read list.** -/
def walkReadsX9 (rows : Array LX9) : List (Noun × ℕ) :=
  (rows.toList.flatMap fun l => (consEntriesX9 l).map fun x => (x.1, x.2.1)).filter fun q => 2 ≤ q.2

theorem depthOf_le : ∀ (k a : ℕ), a < 2 ^ (k + 1) → depthOf a ≤ k := by
  intro k
  induction k with
  | zero =>
    intro a ha
    rw [depthOf, axisBits_of_lt_two (by simpa using ha)]; rfl
  | succ k ih =>
    intro a ha
    by_cases h2 : 2 ≤ a
    · rw [depthOf, axisBits_of_two_le h2, List.length_append, List.length_singleton]
      have := ih (a / 2) (by rw [pow_succ] at ha; omega)
      simp only [depthOf] at this
      omega
    · rw [depthOf, axisBits_of_lt_two (by omega)]; simp

theorem depthOf_le61 {a : ℕ} (h : a < 2 ^ 62) : depthOf a ≤ 61 := depthOf_le 61 a h

theorem xor_one_lt {a k : ℕ} (h : a < 2 ^ (k + 1)) : a ^^^ 1 < 2 ^ (k + 1) := by
  rw [Nock.Edit.xor_one_eq]
  have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  split <;> omega

theorem rowOfSkelX_mem_rowsOfT {t v : NTree SkelX} (hv : InTree t v) :
    rowOfSkelX v.label ∈ (ComplJ8Data.rowsOfT t).toList := by
  simp only [ComplJ8Data.rowsOfT, List.toList_toArray, List.mem_map]
  exact ⟨v, (mem_bfsForest _ _).2 ⟨t, List.mem_singleton_self _, hv⟩, rfl⟩

theorem consEntriesX_s10T (r : RowNX) (h : r.st = .s10T) : consEntriesX r = [] := by
  simp [consEntriesX, h]

theorem chipOf_ne_s10S (k : SkelX) : (chipOf k).1 ≠ .s10S := by
  unfold chipOf
  split
  · split <;> simp
  · split <;> simp
  · simp

/-- An old row with its op-0 / op-10 axis below `2^62` and not a chain row has no routed read. -/
theorem notRouted_old {R : Nock.Jet.Registry} {r : RowNX} (hsem : r.SemN R)
    (h0 : r.st = .s0 → ∀ ax, r.ft = .atom ax → ax < 2 ^ 62)
    (h10 : r.st = .s10 → ∀ a, r.ftth = .atom a → a < 2 ^ 62) (hL : r.st ≠ .s10L) :
    ∀ y ∈ consEntriesX r, routedX r y.2.1 = false := by
  intro y hy
  cases hst : r.st
  case s0 =>
    have hs := hsem
    simp only [RowNX.SemN, hst] at hs
    obtain ⟨-, -, ax, hax, -⟩ := hs
    simp only [consEntriesX, hst, true_and, List.mem_append, reduceCtorEq, false_and, ite_false,
      List.not_mem_nil, or_false] at hy
    split at hy
    · simp only [List.mem_singleton] at hy; subst hy
      have := h0 hst ax hax
      simp [routedX, hst, hax, atomVal]
      omega
    · simp at hy
  case s10 =>
    have hs := hsem
    simp only [RowNX.SemN, hst] at hs
    obtain ⟨-, -, -, -, a, ha, -⟩ := hs
    simp only [consEntriesX, hst, true_and, List.mem_append, reduceCtorEq, false_and, ite_false,
      List.not_mem_nil, or_false, false_or] at hy
    split at hy
    · simp only [List.mem_singleton] at hy; subst hy
      have := h10 hst a ha
      simp [routedX, hst, ha, atomVal]
      omega
    · simp at hy
  case s10L => exact absurd hst hL
  all_goals simp [routedX, hst]

/-- **The J-9 A walk binder covers every J-9 A walk read.** -/
theorem walkDepthOK_X9 {R : Nock.Jet.Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) (hw : WalkDepthOK9A (ComplJ8Data.rowsOfT t)) :
    ComplJ8Walk.WalkDepthOK (walkReadsX9 (rowsOfT9 t)) := by
  intro x hx
  simp only [pathReads, List.mem_dedup, List.mem_filter] at hx
  obtain ⟨hx, hpath⟩ := hx
  simp only [walkReadsX9, List.mem_filter, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨⟨l, hl, y, hy, rfl⟩, h2⟩ := hx
  simp only [rowsOfT9, List.toList_toArray, List.mem_map] at hl
  obtain ⟨u, hu, rfl⟩ := hl
  obtain ⟨c, hc, hcu⟩ := (mem_bfsForest _ _).1 hu
  simp only [List.mem_singleton] at hc
  subst hc
  have hnode := genX9T_inTree h hcu
  have hsem := semN9_of_node9 hnode
  simp only at h2 hpath ⊢
  rcases hnode with ⟨v, hvt, hv, rfl⟩ | ⟨v, hv, hax, rfl⟩ | ⟨nn, m, s0, e0, new, hn, hm, he, rfl⟩ | ⟨X, Y, rfl⟩
  · -- a reclassified generated row: an old one is a non-routed J-8 read of `t`'s own row
    rw [genX9T_label] at hy hsem
    unfold SemN9 at hsem
    unfold consEntriesX9 at hy
    simp only at hy hsem
    cases hch : (chipOf v.label).1 <;> simp only [hch] at hy hsem
    · obtain ⟨hs, h0, h10⟩ := hsem
      have hL : (rowOfSkelX v.label).st ≠ .s10L := by
        intro hL
        have hnc := genNode_not_chain hv
        rw [rowOfSkelX_st] at hL
        rw [hL] at hnc; cases hnc
      have hrt := notRouted_old hs h0 h10 hL y hy
      apply hw (y.1, y.2.1)
      simp only [pathReads, List.mem_dedup, List.mem_filter]
      refine ⟨?_, hpath⟩
      simp only [walkReads9, List.mem_filter, List.mem_flatMap, List.mem_map]
      exact ⟨⟨_, rowOfSkelX_mem_rowsOfT hvt, y, ⟨hy, by simp [hrt]⟩, rfl⟩, h2⟩
    · simp at hy
    · simp at hy
    · exact absurd hch (chipOf_ne_s10S _)
  · -- a lifted chain row: its sibling read sits below `2^62`
    rw [liftT_label] at hy
    simp only [consEntriesX9, liftL] at hy
    obtain ⟨old, e, k, a, rfl, -⟩ := hv
    rw [(genChainF_label _ _ _ _).2.2.1, chainAxis_atom] at hax
    cases k with
    | zero => simp [genChainF, rowOfSkelX, consEntriesX] at hy
    | succ k =>
      by_cases h2a : 2 ≤ a
      · simp only [genChainF, h2a, ite_true, mkX_label, rowOfSkelX, consEntriesX, chainAxis, atomVal] at hy
        simp at hy
        rcases hy with rfl | rfl <;>
          exact depthOf_le61 (xor_one_lt (k := 61) hax)
      · simp [genChainF, h2a, rowOfSkelX, consEntriesX] at hy
  · -- a segment row: the read sits at `segRd < 2^33`
    rw [segT_label] at hy
    simp only [consEntriesX9, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
    have hlt := Nock.J9A.NounAx.segRd_lt nn m
    rcases hy with rfl | rfl <;> exact depthOf_le61 (by simp only; omega)
  · simp [tNode, consEntriesX9, tRow, consEntriesX] at hy

/-- A field axis (`2^62 ≤ v < 2^64`) has exactly two limbs: its top segment is `m = 1`, matching `s10BG`'s field
route `vR = 64·id + 1`. -/
theorem top_field {v : ℕ} (h1 : 2 ^ 62 ≤ v) (h2 : v < 2 ^ 64) : top v = 1 := by
  unfold top
  rw [Nat.log_eq_iff (Or.inl one_ne_zero)]
  constructor <;> norm_num <;> omega

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads
#print axioms walkDepthOK_X9
#print axioms top_field
end Axioms
