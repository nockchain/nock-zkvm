/-
  Nock/NockVMROM/Thm54/TraceGen/GenSlotKeys.lean

  At the repaired chip record `0` is NOT inline: slot `0` is the export lookup of the formula cell
  `(f, f_h, f_t, fIdx)` on every row, and slots `1`, `2` are the state-multiplexed remaining
  records (`FormulaLookup.slotAcc`).  The generator's `requests` list is already in slot order
  (record `0` = `⟨formula, tail, 3⟩` at every state, incl. the autocons root whose record is
  `⟨[leftF rightF], rightF, 3⟩`), so the 3-slot keys are the requests themselves.

  * `rowSlotKeys` / `demandOfRowsD`: ALL of a row's requests as `(root, axis)` keys, `≤ 3` per row
    (`rowSlotKeys_length`, `demandOfRowsD_reads_le`: `≤ 3N`); `rowSlotKeys_eq_inline_append` is the
    relation to the pre-repair `rowLookups` (the inline record `0` is prepended again);
  * `genComputeSkeleton_slot0`: at EVERY emitted row slot `0`'s key is `(formula, 3)` and the formula
    is a cell (`skelRows_slot0`); `3` is depth 1 so slot `0` is a shallow (export) lookup;
  * `fIdxOf d g` = the cell-table serial of the row's formula cell; `fIdx_mem_table`: the formula is
    in the hash-consed closure, `fIdx < D` and the table row at `fIdx` IS the formula
    (`fIdx_getElem`); `genVclL_decode` then reads it back (`fIdx_decode`);
  * multiplicities stay counts: `mx` of a cell = its occurrences in `exportConsumers d.reads`, which
    now includes the slot-`0` lookups (`slot0_in_shallowLookups`);
  * **honest agreement** `formula_key_clause_generated`: on a trace whose B0 column `fIdx = 222`
    holds the generator's `fIdxOf`, `FormulaLookup.formula_key_clause`'s record key is
    `(fIdxOf, false)`, the serial component of the table provider's `xkeyOf` of the formula
    (`xkeyOf_idx`).
-/
import Nock.NockVMROM.Thm54.TraceGen.GenPathRows
import Nock.NockVMROM.Thm54.VclL.Compute.FormulaLookup

set_option autoImplicit false
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL

open Nock Nock.NockVMROM.Thm54.TraceGen Nock.Walk
open Nock.NockVMROM.Thm54.VclL.Compute
open Nock Nock.Framework Nock.Reified Module
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.RecordCarrier
open scoped Polynomial

/-! ## 1. The three slots of a row -/

/-- **Slots are a prefix**: slot `j` of a state is active exactly when `j < recordCount`. -/
theorem slot_active_iff (s : Nock.ComputeTable.State) (j : Fin 3) :
    (slotAcc s j).isSome = true ↔ (j : ℕ) < Nock.Framework.recordCount s := by
  revert j; cases s <;> decide

section Rows
variable {K : Type} [Field K]

/-- **All of a row's lookup keys, in slot order** (`slotAcc`): the request list as `(root, axis)`.
Slot `0` is the formula cell; there is no inline record. -/
def rowSlotKeys (g : GenComputeRow K) : List (Noun × ℕ) :=
  g.requests.map fun r => (r.root, r.axis)

/-- **SHD-A: a row's keys at the slots of accumulator `acc`** (`slotAcc` of the row's state): the
kind comes from the slot, not from the axis's depth. -/
def rowKeysAt (acc : AccVCL) (g : GenComputeRow K) : List (Noun × ℕ) :=
  ((List.finRange 3).filter fun j => slotAcc g.skel.state j = some acc).filterMap fun (j : Fin 3) =>
    (rowSlotKeys g)[j.val]?

/-- The row's export-kind keys (slots whose accumulator is `.export`). -/
def rowExportKeys (g : GenComputeRow K) : List (Noun × ℕ) := rowKeysAt .export g

/-- The row's path-kind keys (slots whose accumulator is `.path`: `s0` slot 1, `s9` slot 2). -/
def rowPathKeys (g : GenComputeRow K) : List (Noun × ℕ) := rowKeysAt .path g

/-- **The VCL-L demand at the repaired chip**: the same root bindings; the request keys split by
slot kind into export reads and path reads (SHD-A). -/
def demandOfRowsD (rows : List (GenComputeRow K)) : Demand :=
  ⟨rows.flatMap rowBinds, rows.flatMap rowExportKeys, rows.flatMap rowPathKeys⟩

theorem exportSlots_add_pathSlots_le (s : Nock.ComputeTable.State) :
    exportSlots s + pathSlots s ≤ 3 := by
  cases s <;> decide

/-- A row's export and path keys together number at most three. -/
theorem rowKeys_length_le (g : GenComputeRow K) :
    (rowExportKeys g).length + (rowPathKeys g).length ≤ 3 := by
  have h1 : (rowExportKeys g).length ≤ exportSlots g.skel.state :=
    List.length_filterMap_le _ _
  have h2 : (rowPathKeys g).length ≤ pathSlots g.skel.state :=
    List.length_filterMap_le _ _
  have := exportSlots_add_pathSlots_le g.skel.state
  omega

/-- The repaired demand's row keys are the active slots: `activeSlots` many. -/
theorem rowSlotKeys_length (g : GenComputeRow K)
    (hlen : g.requests.length = Nock.Framework.recordCount g.skel.state) :
    (rowSlotKeys g).length = activeSlots g.skel.state := by
  simp only [rowSlotKeys, List.length_map, hlen]
  exact ((activeSlots_eq_recordCount _).1).symm

theorem rowSlotKeys_length_le_three (g : GenComputeRow K)
    (hlen : g.requests.length = Nock.Framework.recordCount g.skel.state) :
    (rowSlotKeys g).length ≤ 3 := by
  rw [rowSlotKeys_length g hlen]; exact kc_eq_three.1 _

/-- **The repaired reads number at most `3N`** (`kc = 3`). -/
theorem demandOfRowsD_reads_le (rows : List (GenComputeRow K))
    (_hlen : ∀ g ∈ rows, g.requests.length = Nock.Framework.recordCount g.skel.state) :
    (demandOfRowsD rows).reads.length + (demandOfRowsD rows).preads.length ≤ 3 * rows.length := by
  simp only [demandOfRowsD, List.length_flatMap]
  induction rows with
  | nil => simp
  | cons g rs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := rowKeys_length_le g
    have h2 := ih (fun g' hg' => _hlen g' (by simp [hg']))
    omega

/-- The binds are unchanged. -/
theorem demandOfRowsD_binds (rows : List (GenComputeRow K)) :
    (demandOfRowsD rows).binds = (demandOfRows rows).binds := rfl

/-- **Relation to the pre-repair lookups**: the pre-repair `rowLookups` is the slot keys with the
first `inlineRecords` dropped; the repaired demand restores them. -/
theorem rowSlotKeys_eq_inline_append (g : GenComputeRow K) :
    rowSlotKeys g =
      (rowSlotKeys g).take (inlineRecords g.skel.state) ++ rowLookups g := by
  simp only [rowSlotKeys, rowLookups, ← List.map_take, ← List.map_append, List.take_append_drop]

/-- **Slot keys are export keys or path keys** (every active slot is one of the two). -/
theorem rowSlotKeys_sub (g : GenComputeRow K)
    (hlen : g.requests.length = Nock.Framework.recordCount g.skel.state) :
    ∀ r ∈ rowSlotKeys g, r ∈ rowExportKeys g ∨ r ∈ rowPathKeys g := by
  intro r hr
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
  have hl : (rowSlotKeys g).length = Nock.Framework.recordCount g.skel.state := by
    simp [rowSlotKeys, hlen]
  have h3 : Nock.Framework.recordCount g.skel.state ≤ 3 := by
    rw [← (activeSlots_eq_recordCount g.skel.state).1]; exact kc_eq_three.1 _
  have hj3 : j < 3 := by omega
  have hsome := (slot_active_iff g.skel.state ⟨j, hj3⟩).2 (by simp only; omega)
  have hget : (rowSlotKeys g)[j]? = some (rowSlotKeys g)[j] := List.getElem?_eq_getElem hj
  cases hacc : slotAcc g.skel.state ⟨j, hj3⟩ with
  | none => simp [hacc] at hsome
  | some a =>
    cases a
    · left
      simp only [rowExportKeys, rowKeysAt, List.mem_filterMap, List.mem_filter]
      exact ⟨⟨j, hj3⟩, ⟨List.mem_finRange _, by simp [hacc]⟩, hget⟩
    · right
      simp only [rowPathKeys, rowKeysAt, List.mem_filterMap, List.mem_filter]
      exact ⟨⟨j, hj3⟩, ⟨List.mem_finRange _, by simp [hacc]⟩, hget⟩

/-- The repaired reads (export and path kinds together) contain every pre-repair read. -/
theorem demandOfRows_reads_sub (rows : List (GenComputeRow K))
    (hlen : ∀ g ∈ rows, g.requests.length = Nock.Framework.recordCount g.skel.state) :
    ∀ r ∈ (demandOfRows rows).reads,
      r ∈ (demandOfRowsD rows).reads ∨ r ∈ (demandOfRowsD rows).preads := by
  intro r hr
  simp only [demandOfRows, demandOfRowsD, List.mem_flatMap] at hr ⊢
  obtain ⟨g, hg, hr⟩ := hr
  simp only [rowLookups, rowSlotKeys, List.mem_map] at hr
  obtain ⟨q, hq, rfl⟩ := hr
  rcases rowSlotKeys_sub g (hlen g hg) _ (by
    simp only [rowSlotKeys, List.mem_map]; exact ⟨q, List.mem_of_mem_drop hq, rfl⟩) with h | h
  · exact Or.inl ⟨g, hg, h⟩
  · exact Or.inr ⟨g, hg, h⟩

end Rows

/-! ## 2. Slot `0` is the formula cell, at every row the generator emits -/

section Skeleton
variable {K : Type} [Field K]

/-- **Slot `0` of every emitted row**: the formula is a cell and the first request is the formula at
axis `3` (`mr1 = ⟨formula, tail, 3⟩`; at the autocons root the formula `[leftF rightF]`).  Proof by
fuel induction over the emission arms, as `genComputeSkeleton_requests_length`. -/
theorem genComputeSkeleton_slot0 (fuel : ℕ) :
    ∀ (s f : Noun) (ct : NTree (GenComputeRow K)) (res : Noun),
      genComputeSkeleton fuel s f = .ok (ct, res) →
      ∀ t, InTree ct t →
        t.label.skel.formula.isCell = true ∧
          (rowSlotKeys t.label).head? = some (t.label.skel.formula, 3) := by
  induction fuel with
  | zero => intro s f ct res h; simp [genComputeSkeleton] at h
  | succ n ih =>
    intro s f ct res h t ht
    unfold genComputeSkeleton at h
    repeat' (split at h)
    all_goals first
      | (exfalso; simp at h; done)
      | skip
    all_goals
      (simp only [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       cases ht with
       | here =>
         simp [rowSlotKeys, skelNode, Noun.isCell, genSkelOp0, genSkelOp1, genSkelOp2, genSkelOp3,
           genSkelOp4, genSkelOp5, genSkelOp6, genSkelOp7, genSkelOp8, genSkelOp9, genSkelCons]
       | sub hs hst =>
         simp only [NTree.children_node, List.mem_cons, List.not_mem_nil, or_false] at hs <;>
         first
           | exact hs.elim
           | (subst hs; exact ih _ _ _ _ (by assumption) _ hst)
           | (rcases hs with rfl | rfl <;> exact ih _ _ _ _ (by assumption) _ hst)
           | (rcases hs with rfl | rfl | rfl <;> exact ih _ _ _ _ (by assumption) _ hst))

/-- Every row of the generator's compute tree has slot `0` = the formula cell. -/
theorem skelRows_slot0 (fuel : ℕ) (subj f res : Noun) (ct : NTree (GenComputeRow K))
    (h : genComputeSkeleton fuel subj f = .ok (ct, res)) :
    ∀ g ∈ skelRows ct, g.skel.formula.isCell = true ∧
      (rowSlotKeys g).head? = some (g.skel.formula, 3) := by
  intro g hg
  simp only [skelRows, List.mem_map] at hg
  obtain ⟨t, ht, rfl⟩ := hg
  obtain ⟨c, hc, hct⟩ := (mem_bfsForest _ _).mp ht
  have : c = ct := by simpa using hc
  subst this
  exact genComputeSkeleton_slot0 fuel subj f c res h t hct

end Skeleton

/-! ## 3. `fIdx`: the cell-table serial of the row's formula -/

/-- Axis `3` is depth `1`: slot `0` is a shallow (export) lookup, not a path row. -/
theorem depthOf_three : depthOf 3 = 1 := by decide

section FIdx
variable {K : Type} [Field K]

/-- **`fIdx`**: the serial of the row's formula cell in the demand's hash-consed table. -/
def fIdxOf (d : Demand) (g : GenComputeRow K) : ℕ := d.cells.idxOf g.skel.formula

/-- The formula is bound by its row. -/
theorem formula_mem_binds (rows : List (GenComputeRow K)) {g : GenComputeRow K} (hg : g ∈ rows) :
    g.skel.formula ∈ (demandOfRowsD rows).binds := by
  simp only [demandOfRowsD, List.mem_flatMap, rowBinds, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨g, hg, Or.inr rfl⟩

/-- **The formula is in the hash-consed closure** (a cell, bound by its row). -/
theorem formula_mem_cells (rows : List (GenComputeRow K)) {g : GenComputeRow K} (hg : g ∈ rows)
    (hc : g.skel.formula.isCell = true) : g.skel.formula ∈ (demandOfRowsD rows).cells :=
  bind_cell_mem_cells _ (formula_mem_binds rows hg) hc

/-- **`fIdx_mem_table`**: `fIdx` is a row index of the cell table and the row there is the formula. -/
theorem fIdx_mem_table (rows : List (GenComputeRow K)) {g : GenComputeRow K} (hg : g ∈ rows)
    (hc : g.skel.formula.isCell = true) :
    fIdxOf (demandOfRowsD rows) g < (demandOfRowsD rows).cells.length ∧
      (demandOfRowsD rows).cells[fIdxOf (demandOfRowsD rows) g]? = some g.skel.formula := by
  have hm := formula_mem_cells rows hg hc
  refine ⟨List.idxOf_lt_length_iff.mpr hm, ?_⟩
  simp only [fIdxOf]
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr hm)]
  simp

/-- **The table row at `fIdx` decodes to the formula** (the table's decode at the closure's
certified fuel). -/
theorem fIdx_decode {q : ℕ} [NeZero q] (rows : List (GenComputeRow K)) {g : GenComputeRow K}
    (hg : g ∈ rows) (hc : g.skel.formula.isCell = true)
    (hrank : ∀ r ∈ (demandOfRowsD rows).roots, rankOf r < 2 ^ 110)
    (hatoms : ∀ r ∈ (demandOfRowsD rows).roots, AtomsLt q r) (vcs xcs : List Noun) :
    preZNounOfTable (tableB0 q (demandOfRowsD rows).cells vcs xcs)
      (fIdxOf (demandOfRowsD rows) g) = some g.skel.formula :=
  genVclL_decode _ hrank hatoms vcs xcs (formula_mem_cells rows hg hc)

/-- **Slot `0` is one of the table's export consumers**: the formula cell occurs in
`exportConsumers`, so its `mx` counts the slot-`0` lookup. -/
theorem slot0_in_shallowLookups (rows : List (GenComputeRow K)) {g : GenComputeRow K}
    (hg : g ∈ rows) (hc : g.skel.formula.isCell = true)
    (hhead : (rowSlotKeys g).head? = some (g.skel.formula, 3)) :
    g.skel.formula ∈ shallowLookups (demandOfRowsD rows).reads := by
  have hget : (rowSlotKeys g)[(0 : ℕ)]? = some (g.skel.formula, 3) := by
    rcases hk : rowSlotKeys g with _ | ⟨x, xs⟩
    · rw [hk] at hhead; simp at hhead
    · rw [hk] at hhead; simp at hhead; simp [hhead]
  have hmem0 : (g.skel.formula, 3) ∈ rowExportKeys g := by
    simp only [rowExportKeys, rowKeysAt, List.mem_filterMap, List.mem_filter]
    exact ⟨0, ⟨List.mem_finRange _, by simp [slot0_export]⟩, hget⟩
  have hmem : (g.skel.formula, 3) ∈ (demandOfRowsD rows).reads := by
    simp only [demandOfRowsD, List.mem_flatMap]
    exact ⟨g, hg, hmem0⟩
  simp only [shallowLookups, shallowReads, List.mem_flatMap, List.mem_filter]
  refine ⟨(g.skel.formula, 3), ⟨hmem, by simp [depthOf_three]⟩, ?_⟩
  cases hf : g.skel.formula with
  | atom a => rw [hf] at hc; simp [Noun.isCell] at hc
  | cell x y => simp [selfCell]

end FIdx


/-! ## 4. Honest agreement with `formula_key_clause` -/

section Agree
/-- The serial component of the table provider's export key of a cell is its closure position. -/
theorem xkeyOf_idx {q : ℕ} {Kf : Type} [Field Kf] [Algebra (ZMod q) Kf] (z : Kf)
    (cells : List Noun) (n : Noun) : (xkeyOf z cells n).2.2.2 = cells.idxOf n := rfl

end Agree

section AgreeChip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **The emitted `fIdx` satisfies `formula_key_clause`**: on any trace whose B0 column `fIdx`
(`222`) holds the generator's serial `n` (below the characteristic), the slot-0 record's key is
`(n, false)`: the serial component of the provider's `xkeyOf` of the formula when `n = fIdxOf`. -/
theorem formula_key_clause_generated {h : ℕ} (b : Basis (Fin 3) F K)
    (Q : Fin (tableVCLD h).width → Polynomial F) (ω x : F) (chal pub : ℕ → F) (n : ℕ)
    (hcol : (Q (fIdxB0 h).1).eval x = (n : F)) (hlt : n < ringChar K) :
    keyOfFormulaRec (recVal b (Reify.envOfTrace Q ω x chal pub) formulaRec) = (n, false) := by
  rw [formula_key_clause b Q ω x chal pub]
  have : (b0 (T := tableVCLD h) Q (fIdxB0 h)).eval x = (n : F) := hcol
  simp only [recKeyFormula, this, map_natCast]
  rw [natLift_natCast hlt]

end AgreeChip

end Nock.NockVMROM.Thm54.VclL
