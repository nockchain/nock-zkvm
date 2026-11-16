/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestDemand.lean

  Additive; no `Gen.lean` edit, no existing module edited.

  `demandH rows` replaces `rowBinds = [subject, formula]` by the handle nouns of every row
  (`s f e sf1 sf2 m`) and keeps the walk reads (`rowPathKeys`); the export reads are dropped (VS
  decodes by serial lookups).  Hash-consing is `honest_one_row_per_noun` (generic in the demand).
  * `handle_cells_mem`: every cell among the twelve handles of every honest row (`hn` of
    `rowOfSkel`) is a row of `(demandH rows).cells`;
  * `demandH_one_row`: one row per noun.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestRun

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.SemanticStrategy

noncomputable section

section Demand
variable {K : Type} [Field K]

/-- The nouns a VS compute row names through its handles (the six independent ones). -/
def handleNouns (g : GenComputeRow K) : List Noun :=
  [(rowOfSkel g.skel).s, (rowOfSkel g.skel).f, (rowOfSkel g.skel).e, (rowOfSkel g.skel).sf1,
    (rowOfSkel g.skel).sf2, (rowOfSkel g.skel).m]

/-- **The VS demand**: handle nouns as binds (replacing `rowBinds`), no export reads, the walk
reads of the rows unchanged. -/
def demandH (rows : List (GenComputeRow K)) : Demand :=
  ⟨rows.flatMap handleNouns, [], rows.flatMap rowPathKeys⟩

/-- The twelve handle nouns of an effective row. -/
def rowHandleNouns (r : RowN) : List Noun :=
  [r.s, r.f, r.e, r.sf1, r.sf2, r.fh, r.ft, r.fth, r.ftt, r.ftth, r.fttt, r.m]

theorem cell_mem_closure_of_root {ns : List Noun} {n : Noun} (hn : n ∈ ns) (hc : n.isCell = true) :
    n ∈ closureOf ns := by
  cases n with
  | atom _ => simp [Noun.isCell] at hc
  | cell x y => exact mem_closureOf.mpr ⟨_, hn, mem_cellsOf_self⟩

theorem cell_mem_cellsOf_of_sub {a c : Noun} (h : c ∈ cellsOf a) {d : Noun} (hd : d ∈ cellsOf c) :
    d ∈ cellsOf a := mem_cellsOf_trans h hd

theorem hdN_cells {a : Noun} (h : (hdN a).isCell = true) : hdN a ∈ cellsOf a := by
  cases a with
  | atom _ => simp [hdN, Noun.isCell] at h
  | cell x y =>
    simp only [hdN] at h ⊢
    cases x with
    | atom _ => simp [Noun.isCell] at h
    | cell u v => simp [cellsOf]

theorem tlN_cells {a : Noun} (h : (tlN a).isCell = true) : tlN a ∈ cellsOf a := by
  cases a with
  | atom _ => simp [tlN, Noun.isCell] at h
  | cell x y =>
    simp only [tlN] at h ⊢
    cases y with
    | atom _ => simp [Noun.isCell] at h
    | cell u v => simp [cellsOf]

theorem fdN_cells : ∀ (a b : Noun),
    ((fdN a b).2.1.isCell = true → (fdN a b).2.1 ∈ cellsOf a) ∧
    ((fdN a b).2.2.isCell = true → (fdN a b).2.2 ∈ cellsOf b)
  | .atom x, .atom y => by simp [fdN, Noun.isCell]
  | .atom x, .cell y z => by simp [fdN, Noun.isCell, cellsOf]
  | .cell x y, .atom z => by simp [fdN, Noun.isCell, cellsOf]
  | .cell a1 a2, .cell b1 b2 => by
    by_cases h1 : a1 = b1
    · have ih := fdN_cells a2 b2
      simp only [fdN, h1, if_true]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih.1 h))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih.2 h))
    · have ih := fdN_cells a1 b1
      simp only [fdN, h1, if_false]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ih.1 h))
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ih.2 h))

theorem isCell_of_hdN {a : Noun} (h : (hdN a).isCell = true) : a.isCell = true := by
  cases a with
  | atom _ => simp [hdN, Noun.isCell] at h
  | cell _ _ => rfl

theorem isCell_of_tlN {a : Noun} (h : (tlN a).isCell = true) : a.isCell = true := by
  cases a with
  | atom _ => simp [tlN, Noun.isCell] at h
  | cell _ _ => rfl

/-- "cells among `x` are cells of `f`". -/
def FSub (f x : Noun) : Prop := x.isCell = true → x ∈ cellsOf f

theorem fsub_zero (f : Noun) : FSub f (.atom 0) := by intro h; simp [Noun.isCell] at h
theorem fsub_hd (f : Noun) : FSub f (hdN f) := fun h => hdN_cells h
theorem fsub_tl (f : Noun) : FSub f (tlN f) := fun h => tlN_cells h
theorem fsub_hd_tl (f : Noun) : FSub f (hdN (tlN f)) := fun h =>
  mem_cellsOf_trans (tlN_cells (isCell_of_hdN h)) (hdN_cells h)
theorem fsub_tl_tl (f : Noun) : FSub f (tlN (tlN f)) := fun h =>
  mem_cellsOf_trans (tlN_cells (isCell_of_tlN h)) (tlN_cells h)
theorem fsub_hd_tl_tl (f : Noun) : FSub f (hdN (tlN (tlN f))) := fun h =>
  mem_cellsOf_trans (tlN_cells (isCell_of_tlN (isCell_of_hdN h)))
    (mem_cellsOf_trans (tlN_cells (isCell_of_hdN h)) (hdN_cells h))
theorem fsub_tl_tl_tl (f : Noun) : FSub f (tlN (tlN (tlN f))) := fun h =>
  mem_cellsOf_trans (tlN_cells (isCell_of_tlN (isCell_of_tlN h)))
    (mem_cellsOf_trans (tlN_cells (isCell_of_tlN h)) (tlN_cells h))

theorem rowOfSkel_f (sk : ComputeRowSkeleton) : (rowOfSkel sk).f = sk.formula := by
  unfold rowOfSkel
  cases sk.state <;> rfl

/-- The six decode fields of an honest row are zero or head/tail chains of the formula. -/
theorem fieldsSub (sk : ComputeRowSkeleton) :
    FSub sk.formula (rowOfSkel sk).fh ∧ FSub sk.formula (rowOfSkel sk).ft ∧
    FSub sk.formula (rowOfSkel sk).fth ∧ FSub sk.formula (rowOfSkel sk).ftt ∧
    FSub sk.formula (rowOfSkel sk).ftth ∧ FSub sk.formula (rowOfSkel sk).fttt := by
  unfold rowOfSkel
  cases sk.state <;> simp only <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | exact fsub_zero _ | exact fsub_hd _ | exact fsub_tl _ | exact fsub_hd_tl _
    | exact fsub_tl_tl _ | exact fsub_hd_tl_tl _ | exact fsub_tl_tl_tl _

/-- **Every cell among the twelve handles of every honest row is a row of the demand's table.** -/
theorem handle_cells_mem (rows : List (GenComputeRow K)) {g : GenComputeRow K} (hg : g ∈ rows) :
    ∀ n ∈ rowHandleNouns (hn (rowOfSkel g.skel)), n.isCell = true →
      n ∈ (demandH rows).cells := by
  intro n hn' hc
  have hsub : ∀ a ∈ handleNouns g, ∀ x, x ∈ cellsOf a → x ∈ (demandH rows).cells := by
    intro a ha x hx
    refine mem_closureOf.mpr ⟨a, ?_, hx⟩
    simp only [Demand.roots, demandH, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl ⟨g, hg, ha⟩)
  have hroot : ∀ x ∈ handleNouns g, x.isCell = true → x ∈ (demandH rows).cells := by
    intro x hx hc
    exact cell_mem_closure_of_root (by
      simp only [Demand.roots, demandH, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inl ⟨g, hg, hx⟩)) hc
  have hF := fieldsSub g.skel
  have hH : handleNouns g = [(rowOfSkel g.skel).s, (rowOfSkel g.skel).f, (rowOfSkel g.skel).e,
      (rowOfSkel g.skel).sf1, (rowOfSkel g.skel).sf2, (rowOfSkel g.skel).m] := rfl
  have hf : (rowOfSkel g.skel).f = g.skel.formula := rowOfSkel_f g.skel
  have hfm : (rowOfSkel g.skel).f ∈ handleNouns g := by simp [hH]
  have hs1 : (rowOfSkel g.skel).sf1 ∈ handleNouns g := by simp [hH]
  have hs2 : (rowOfSkel g.skel).sf2 ∈ handleNouns g := by simp [hH]
  have hF' : ∀ x, FSub g.skel.formula x → x.isCell = true → x ∈ (demandH rows).cells := by
    intro x hx hcx
    exact hsub _ hfm x (hf ▸ hx hcx)
  generalize rowOfSkel g.skel = r at *
  simp only [rowHandleNouns, List.mem_cons, List.not_mem_nil, or_false] at hn'
  by_cases h5 : r.op = 5
  · simp only [hn, h5, if_true] at hn'
    rcases hn' with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at hc ⊢
    · exact hroot _ (by simp [hH]) hc
    · exact hroot _ hfm hc
    · exact hroot _ (by simp [hH]) hc
    · exact hroot _ hs1 hc
    · exact hroot _ hs2 hc
    · exact hF' _ hF.1 hc
    · exact hF' _ hF.2.1 hc
    · exact hF' _ hF.2.2.1 hc
    · exact hF' _ hF.2.2.2.1 hc
    · exact hsub _ hs1 _ ((fdN_cells _ _).1 hc)
    · exact hsub _ hs2 _ ((fdN_cells _ _).2 hc)
    · simp [Noun.isCell] at hc
  · simp only [hn, h5, if_false] at hn'
    rcases hn' with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at hc ⊢
    · exact hroot _ (by simp [hH]) hc
    · exact hroot _ hfm hc
    · exact hroot _ (by simp [hH]) hc
    · exact hroot _ hs1 hc
    · exact hroot _ hs2 hc
    · exact hF' _ hF.1 hc
    · exact hF' _ hF.2.1 hc
    · exact hF' _ hF.2.2.1 hc
    · exact hF' _ hF.2.2.2.1 hc
    · exact hF' _ hF.2.2.2.2.1 hc
    · exact hF' _ hF.2.2.2.2.2 hc
    · exact hroot _ (by simp [hH]) hc

/-- **One row per noun** of the VS honest cell table (generic in the demand). -/
theorem demandH_one_row (rows : List (GenComputeRow K)) :
    ∀ n ∈ (demandH rows).cells, (demandH rows).cells.count n = 1 :=
  honest_one_row_per_noun _

end Demand

end

end Nock.NockVMROM.Thm54.VclL.Handle
