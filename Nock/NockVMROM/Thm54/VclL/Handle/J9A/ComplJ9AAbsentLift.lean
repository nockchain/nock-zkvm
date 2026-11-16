/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AAbsentLift.lean

When the axis chip is absent (`axOnA t = false`: no `s0B` / `s10B` row in the J-9 A rows), every op-0 / op-10
  axis of the generated tree, and every `s10L` chain level, is `< 2^62`.  Hence:

  * `progAxOK_of_absent`    : `ProgAxOK9A p t → ProgAxOK p t`       (needs `hgen`, `hA`, `p = Goldilocks`)
  * `walkDepthOK_of_absent` : `WalkDepthOK9A (rowsOfT t) → WalkDepthOK (pathReads (rowsOfT t))`
  * `rows31_of_rows31A`     : `Rows31A (DA) → Rows31 (DD)`           (no presence hypothesis)
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ARun
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABinders
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AAbsent

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAbsentLift

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun (axKeys9 mem_axKeys9 axKey9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (axOnA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (AxRowX ProgAxOK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (rowsOfT)

/-! ## 1. Chain descendants and generated descendants -/

theorem chain_desc {c v : NTree SkelX} (hc : ChainNode c) (h : InTree c v) :
    ChainNode v ∧ chainAxis v.label.formula ≤ chainAxis c.label.formula := by
  induction h with
  | here => exact ⟨hc, le_rfl⟩
  | @sub c s t hs h ih =>
    have hs' := chainNode_children hc s hs
    have := ih hs'
    exact ⟨this.1, le_trans this.2 (chainNode_child_axis hc hs)⟩

theorem gen_desc {R : Nock.Jet.Registry} {w v : NTree SkelX} (hw : GenNode R w) (h : InTree w v) :
    (GenNode R v ∧ InTree (genX9T w) (genX9T v)) ∨
    (ChainNode v ∧ ∃ g, GenNode R g ∧ g.label.state = .s10 ∧ InTree (genX9T w) (genX9T g) ∧
      chainAxis v.label.formula ≤ op10Axis g.label.formula) := by
  induction h with
  | here => exact Or.inl ⟨hw, InTree.here _⟩
  | @sub c s t hs h ih =>
    obtain ⟨m, hm⟩ := hw
    rcases genX_children9 hm s hs with hg | ⟨hch, hfc, hst⟩
    · have hmem : genX9T s ∈ (genX9T c).children := by
        rw [genX9T_children]
        exact List.mem_map.mpr ⟨s, hs, by simp [kid9, genNode_not_chain hg]⟩
      rcases ih hg with ⟨a, b⟩ | ⟨a, g, b1, b2, b3, b4⟩
      · exact Or.inl ⟨a, InTree.sub hmem b⟩
      · exact Or.inr ⟨a, g, b1, b2, InTree.sub hmem b3, b4⟩
    · obtain ⟨hchT, hle⟩ := chain_desc hch h
      refine Or.inr ⟨hchT, c, ⟨m, hm⟩, hst, InTree.here _, ?_⟩
      rw [hfc, chainAxis_atom] at hle
      exact hle

/-! ## 2. Absence -/

theorem chip_ne_of_absent {t : NTree SkelX} (hA : axOnA t = false) :
    ∀ l ∈ (rowsOfT9 t).toList, l.chip ≠ .s0B ∧ l.chip ≠ .s10B := by
  intro l hl
  have hA' : axKeys9 (rowsOfT9 t) = [] := by
    unfold axOnA at hA
    simpa using hA
  constructor
  · intro hc
    have : (l.rn.s, l.n) ∈ axKeys9 (rowsOfT9 t) :=
      mem_axKeys9.2 ⟨l, hl, by simp [axKey9, hc]⟩
    rw [hA'] at this; simp at this
  · intro hc
    have : (l.rn.e, l.n) ∈ axKeys9 (rowsOfT9 t) :=
      mem_axKeys9.2 ⟨l, hl, by simp [axKey9, hc]⟩
    rw [hA'] at this; simp at this

theorem chipOf_old {k : SkelX} (h0 : (chipOf k).1 ≠ .s0B) (h1 : (chipOf k).1 ≠ .s10B) :
    (chipOf k).1 = .old := by
  unfold chipOf at h0 h1 ⊢
  split <;> simp_all <;> split_ifs at * <;> simp_all

theorem row_mem {t : NTree SkelX} {u : NTree LX9} (h : InTree (genX9T t) u) : u.label ∈ (rowsOfT9 t).toList := by
  simp only [rowsOfT9, List.toList_toArray, List.mem_map]
  exact ⟨u, (mem_bfsForest _ _).2 ⟨genX9T t, by simp, h⟩, rfl⟩

/-- **Chip of a node in the tree is `old` when the axis chip is absent.** -/
theorem chipOld_of_absent {t g : NTree SkelX} (hA : axOnA t = false) (h : InTree (genX9T t) (genX9T g)) :
    (chipOf g.label).1 = .old := by
  have hno := chip_ne_of_absent hA _ (row_mem h)
  rw [genX9T_label] at hno
  exact chipOf_old hno.1 hno.2

/-! ## 3. Every op-0 / op-10 / chain axis is below `2^62` -/

theorem axes_small {R : Nock.Jet.Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) (hA : axOnA t = false) {u : NTree SkelX} (hu : InTree t u) :
    ((rowOfSkelX u.label).st = .s0 → ∀ ax, (rowOfSkelX u.label).ft = .atom ax → ax < 2 ^ 62) ∧
    ((rowOfSkelX u.label).st = .s10 → ∀ a, (rowOfSkelX u.label).ftth = .atom a → a < 2 ^ 62) ∧
    ((rowOfSkelX u.label).st = .s10L → ∀ a, (rowOfSkelX u.label).f = .atom a → a < 2 ^ 62) := by
  have hst := rowOfSkelX_st u.label
  have hf := rowOfSkelX_f u.label
  rcases gen_desc (genNode_of h) hu with ⟨hg, hT⟩ | ⟨hch, g, hgg, hgst, hgT, hle⟩
  · have hold := chipOld_of_absent hA hT
    have hsem := semN9_gen hg
    rw [genX9T_label] at hsem
    unfold SemN9 at hsem
    dsimp only at hsem
    rw [hold] at hsem
    dsimp only at hsem
    obtain ⟨-, h0, h10⟩ := hsem
    refine ⟨h0, h10, ?_⟩
    intro hs
    exfalso
    have := genNode_not_chain hg
    rw [← hst, hs] at this
    simp [StateX.isChain] at this
  · have hgold := chipOld_of_absent hA hgT
    have hlt := small_of_not_s10B hgst (by rw [hgold]; simp)
    have hc := chainNode_isChain hch
    refine ⟨fun hs => ?_, fun hs => ?_, fun hs a ha => ?_⟩
    · exfalso; rw [← hst, hs] at hc; simp [StateX.isChain] at hc
    · exfalso; rw [← hst, hs] at hc; simp [StateX.isChain] at hc
    · rw [hf] at ha
      have : chainAxis u.label.formula = a := by rw [ha]; rfl
      omega

/-! ## 4. The lifts -/

section Lifts
variable {R : Nock.Jet.Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}

/-- **Item 1**: `hax9 → hax` in the absent case. -/
theorem progAxOK_of_absent {p : ℕ} (hpG : p = Nock.Atoms.p) (h : genX R n s f = some (t, r))
    (hA : axOnA t = false) (hax9 : ProgAxOK9A p t) : ProgAxOK p t := by
  have h63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have hp : 2 ^ 62 < p := by
    have : 2 ^ 62 < 2 ^ 63 := by norm_num
    omega
  intro u hu
  obtain ⟨h0, h10, hL⟩ := axes_small h hA hu
  have h9 := hax9 u hu
  unfold AxRowX
  unfold AxRowX9A at h9
  generalize rowOfSkelX u.label = r at *
  cases hs : r.st <;> simp only [hs] at h9 ⊢
  all_goals first
    | trivial
    | exact h9
    | exact fun ax hax => lt_trans (h0 hs ax hax) hp
    | exact fun a ha => lt_trans (h10 hs a ha) hp
    | exact fun a ha => by have := hL hs a ha; omega

/-- **Item 2**: `hwalk9 → hwalk` in the absent case (stated on `pathReads (rowsOfT t)`, which is `(DD).reads`). -/
theorem walkDepthOK_of_absent (h : genX R n s f = some (t, r)) (hA : axOnA t = false)
    (hw : WalkDepthOK9A (rowsOfT t)) :
    ComplJ8Walk.WalkDepthOK (Nock.V1J8.Gen.pathReads (rowsOfT t)) := by
  refine walkDepthOK_mono (fun x hx => ?_) hw
  simp only [Nock.V1J8.Gen.pathReads, walkReads9, List.mem_filter, List.mem_flatMap, List.mem_map] at hx ⊢
  obtain ⟨⟨r0, hr0, y, hy, rfl⟩, h2⟩ := hx
  refine ⟨⟨r0, hr0, y, ⟨hy, ?_⟩, rfl⟩, h2⟩
  simp only [rowsOfT, List.toList_toArray, List.mem_map] at hr0
  obtain ⟨u, hu', rfl⟩ := hr0
  obtain ⟨c, hc, hcu⟩ := (mem_bfsForest _ _).1 hu'
  simp only [List.mem_singleton] at hc
  subst hc
  obtain ⟨h0, h10, hL⟩ := axes_small h hA hcu
  have hsem := inTree_rowSem h hcu
  have hav : ∀ (m : Noun) (B : ℕ), (∀ a, m = .atom a → a < B) → 0 < B → atomVal m < B := by
    intro m B hm hB
    cases m with
    | atom a => exact hm a rfl
    | cell _ _ => simpa [atomVal] using hB
  have hlt : ((rowOfSkelX u.label).st = .s0 ∨ (rowOfSkelX u.label).st = .s10 ∨
      (rowOfSkelX u.label).st = .s10L) → y.2.1 < 2 ^ 62 := by
    intro hst
    rcases hst with hs | hs | hs
    · simp [consEntriesX, hs] at hy
      obtain ⟨-, rfl⟩ := hy
      exact hav _ _ (h0 hs) (by norm_num)
    · simp [consEntriesX, hs] at hy
      obtain ⟨-, rfl⟩ := hy
      exact hav _ _ (h10 hs) (by norm_num)
    · simp only [RowNX.SemN, hs] at hsem
      obtain ⟨a, ha, -, -, -, hm, -⟩ := hsem
      have hal := hL hs a ha
      have hx : a ^^^ 1 < 2 ^ 62 := Nat.xor_lt_two_pow hal (by norm_num)
      simp [consEntriesX, hs] at hy
      rcases hy with rfl | rfl <;>
        (show atomVal (rowOfSkelX u.label).m < 2 ^ 62; rw [hm]; exact hx)
  unfold routedX
  by_cases hh : ((rowOfSkelX u.label).st = .s0 ∨ (rowOfSkelX u.label).st = .s10 ∨
      (rowOfSkelX u.label).st = .s10L)
  · have h1 := hlt hh
    have : ¬ (2 ^ 62 ≤ y.2.1) := by omega
    simp [this] <;> omega
  · simp only [not_or] at hh
    obtain ⟨a, b, c⟩ := hh
    simp [a, b, c]

/-- Item 2 at the J-8 data record: `(DD).reads` is `pathReads (rowsOfT t)` by definition of `j8DataOf`. -/
theorem walkDepthOK_of_absent_DD {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry}
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f : Noun} {r : Noun} {t : NTree SkelX}
    (hgen : genX Rg.R fuel s f = some (t, r)) (hA : axOnA t = false)
    (hw : WalkDepthOK9A (rowsOfT t)) :
    ComplJ8Walk.WalkDepthOK (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data.j8DataOf p Rg Rt hgen).reads :=
  walkDepthOK_of_absent hgen hA hw

end Lifts

/-- **Item 3**: `Rows31A → Rows31` (no presence hypothesis). -/
theorem rows31_of_rows31A {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
    {D : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data.J8Data p Rg fuel s f r}
    (h : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.Rows31A D) :
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of.Rows31 D :=
  Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.rows31_of_A h

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAbsentLift

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAbsentLift
#print axioms progAxOK_of_absent
#print axioms walkDepthOK_of_absent
#print axioms rows31_of_rows31A
end Axioms
