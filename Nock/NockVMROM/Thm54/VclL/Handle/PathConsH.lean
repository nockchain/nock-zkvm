/-
  Nock/NockVMROM/Thm54/VclL/Handle/PathConsH.lean

  Additive; no existing module changed.

  The compute twin consumes walk-handle records `(rootIdx, axis, child kind, child val)` at three
  places (`ChipH.slot1` OP0, `slot2` OP9, and the `slot2` OP5 first-difference PAIR).  At noun level
  (`consEntries`, on the effective row `hn (rowOfSkelH _)`):
  * OP0 with `f_t ≠ atom 1`: `(s, axis, e)`;
  * OP9 with `f_th ≠ atom 1`: `(sf1, axis, m)`;
  * OP5 "≠" with a non-root first difference: `(sf1, A, f_tth)` and `(sf2, A, f_ttt)`, `A` the axis of
    the first-difference path.
  * `fdN_chain` / `fdN_slot`: the first-difference hosts are the slots at the path's axis;
  * `row_cons_eq`: every consumed entry of a semantically valid row is `readRecH` of its (root, axis);
  * `compute_walk_balance`: for ANY weight `W` (in particular `1/(rho + RLC_gamma)`), the compute side's
    consumed total equals the walk rows' provided total (`WalkRecH.provH`), the walk being built from
    `walkReadsH rows`.

  **FINDING (kernel-checked structure, relation UNCONFIRMED):** `demandH`'s `preads` is
  `rows.flatMap rowPathKeys`, which are the OP0 / OP9 slot keys only.  The OP5 pair reads are NOT in it,
  so the walk built from `demandH.preads` provides nothing for them and the pair consumes of
  `computeChipVCLH` would be unbalanced.  The balanced walk is built from `walkReadsH rows` (the cells
  list is unchanged: `walkRows` takes `cells` and `preads` separately).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkRecH
import Nock.NockVMROM.Thm54.VclL.Handle.HonestRowsH

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.SemanticStrategy

noncomputable section

/-! ## 1. The first difference hosts are slots -/

theorem fdN_chain : ∀ (a b : Noun),
    chainWalk a (fdN a b).1 = some (fdN a b).2.1 ∧ chainWalk b (fdN a b).1 = some (fdN a b).2.2
  | .atom x, .atom y => by simp [fdN, chainWalk]
  | .atom x, .cell y z => by simp [fdN, chainWalk]
  | .cell x y, .atom z => by simp [fdN, chainWalk]
  | .cell a1 a2, .cell b1 b2 => by
    by_cases h1 : a1 = b1
    · have ih := fdN_chain a2 b2
      simp only [fdN, h1, if_true, chainWalk]
      exact ih
    · have ih := fdN_chain a1 b1
      simp only [fdN, h1, if_false, chainWalk]
      exact ih

theorem axisOfPath_eq (p : List Bool) : axisOfPath p = axisFold p := rfl

theorem fdN_slot (a b : Noun) :
    Noun.slot (axisOfPath (fdN a b).1) a = some (fdN a b).2.1 ∧
    Noun.slot (axisOfPath (fdN a b).1) b = some (fdN a b).2.2 := by
  rw [axisOfPath_eq, chain_slot, chain_slot]
  exact fdN_chain a b

theorem two_le_axisOfPath {p : List Bool} (hp : p ≠ []) : 2 ≤ axisOfPath p := by
  rw [axisOfPath_eq]
  obtain ⟨bs, b, rfl⟩ : ∃ bs b, p = bs ++ [b] := by
    obtain ⟨l, b, h⟩ := (List.eq_nil_or_concat p).resolve_left hp
    exact ⟨l, b, by simpa [List.concat_eq_append] using h⟩
  rw [axisFold_append]
  have := axisFold_pos bs
  split <;> omega

/-! ## 2. The consumed entries of a row -/

/-- A consumed path entry `(root, axis, child)`. -/
abbrev PEnt := Noun × ℕ × Noun

/-- The path-record consumes of an EFFECTIVE row (`hn _`): OP0, OP9, and the OP5 first-difference pair. -/
def consEntries (r : RowN) : List PEnt :=
  (if r.op = 0 ∧ r.ft ≠ .atom 1 then [(r.s, atomVal r.ft, r.e)] else []) ++
  (if r.op = 9 ∧ r.fth ≠ .atom 1 then [(r.sf1, atomVal r.fth, r.m)] else []) ++
  (if r.op = 5 ∧ r.e = .atom 1 ∧ (fdN r.sf1 r.sf2).1 ≠ [] then
    [(r.sf1, atomVal r.m, r.ftth), (r.sf2, atomVal r.m, r.fttt)] else [])

/-- The consumed record of an entry, in the walk-record form. -/
def entRecP {F : Type} [Field F] (cells : List Noun) (x : PEnt) : F × F × (F × F) :=
  ((cells.idxOf x.1 : ℕ), (x.2.1 : F), hdl cells x.2.2)

section Rows
variable {K : Type} [Field K]

def consEntriesAll (rows : List (GenComputeRow K)) : List PEnt :=
  rows.flatMap fun g => consEntries (hn (rowOfSkelH g.skel))

/-- **The walk's reads**: the roots and axes of every consumed entry (OP0, OP9 AND the OP5 pair). -/
def walkReadsH (rows : List (GenComputeRow K)) : List (Noun × ℕ) :=
  (consEntriesAll rows).map fun x => (x.1, x.2.1)

theorem slot_zero_none (n : Noun) : Noun.slot 0 n = none := by simp [Noun.slot]

/-- **Each consumed entry of a semantically valid row is a defined slot read at axis `≥ 2`, and its
child is that slot.** -/
theorem row_cons_eq (r : RowN) (hs : r.Sem) :
    ∀ x ∈ consEntries (hn r), 2 ≤ x.2.1 ∧ Noun.slot x.2.1 x.1 = some x.2.2 := by
  intro x hx
  by_cases h5 : r.op = 5
  · have hop : (hn r).op = 5 := by simp [hn, h5]
    have hE : (hn r).e = r.e := by simp [hn, h5]
    have h1 : (hn r).sf1 = r.sf1 := by simp [hn, h5]
    have h2 : (hn r).sf2 = r.sf2 := by simp [hn, h5]
    have hm : (hn r).m = .atom (axisOfPath (fdN r.sf1 r.sf2).1) := by simp [hn, h5]
    have ht1 : (hn r).ftth = (fdN r.sf1 r.sf2).2.1 := by simp [hn, h5]
    have ht2 : (hn r).fttt = (fdN r.sf1 r.sf2).2.2 := by simp [hn, h5]
    unfold consEntries at hx
    rw [hop, hE, h1, h2, hm, ht1, ht2] at hx
    have h0 : ¬ ((5 : ℕ) = 0) := by omega
    have h9 : ¬ ((5 : ℕ) = 9) := by omega
    simp only [h0, h9, false_and, if_false, List.nil_append, List.append_nil, true_and] at hx
    by_cases hc : r.e = .atom 1 ∧ (fdN r.sf1 r.sf2).1 ≠ []
    · rw [if_pos hc] at hx
      have hax := two_le_axisOfPath hc.2
      have hsl := fdN_slot r.sf1 r.sf2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨by simpa [atomVal] using hax, by simpa [atomVal] using hsl.1⟩
      · exact ⟨by simpa [atomVal] using hax, by simpa [atomVal] using hsl.2⟩
    · rw [if_neg (by tauto)] at hx
      simp at hx
  · rw [hn_of_ne r h5] at *
    unfold consEntries at hx
    have h5' : ¬ (r.op = 5 ∧ r.e = .atom 1 ∧ (fdN r.sf1 r.sf2).1 ≠ []) := fun h => h5 h.1
    rw [if_neg h5', List.append_nil] at hx
    rcases List.mem_append.mp hx with hx | hx
    · by_cases hc : r.op = 0 ∧ r.ft ≠ .atom 1
      · rw [if_pos hc] at hx
        simp only [List.mem_singleton] at hx
        subst hx
        have hsem := hs
        simp only [RowN.Sem, hc.1] at hsem
        obtain ⟨-, -, ax, hft, hsl⟩ := hsem
        rw [hft] at hc
        have hne1 : ax ≠ 1 := fun h => hc.2 (by rw [h])
        have hne0 : ax ≠ 0 := fun h => by rw [h, slot_zero_none] at hsl; cases hsl
        simp only [hft, atomVal]
        exact ⟨by omega, hsl⟩
      · rw [if_neg hc] at hx; simp at hx
    · by_cases hc : r.op = 9 ∧ r.fth ≠ .atom 1
      · rw [if_pos hc] at hx
        simp only [List.mem_singleton] at hx
        subst hx
        have hsem := hs
        simp only [RowN.Sem, hc.1] at hsem
        obtain ⟨-, -, -, -, ax, hft, hsl⟩ := hsem
        rw [hft] at hc
        have hne1 : ax ≠ 1 := fun h => hc.2 (by rw [h])
        have hne0 : ax ≠ 0 := fun h => by rw [h, slot_zero_none] at hsl; cases hsl
        simp only [hft, atomVal]
        exact ⟨by omega, hsl⟩
      · rw [if_neg hc] at hx; simp at hx

/-- **The balance.**  If every row is semantically valid, then for ANY weight `W` (into any additive
monoid), the compute side's consumed walk-handle total equals the walk rows' provided total, the walk
being built from `walkReadsH rows`. -/
theorem compute_walk_balance {F : Type} [Field F] {M : Type} [AddCommMonoid M]
    (W : F × F × (F × F) → M) (cells : List Noun) (rows : List (GenComputeRow K))
    (hsem : ∀ g ∈ rows, (rowOfSkel g.skel).Sem) :
    (((consEntriesAll rows).map fun x => W (entRecP cells x))).sum =
      (((walkRows cells (walkReadsH rows)).map fun t => provH W cells t.label)).sum := by
  have hall : ∀ x ∈ consEntriesAll rows, 2 ≤ x.2.1 ∧ Noun.slot x.2.1 x.1 = some x.2.2 := by
    intro x hx
    obtain ⟨g, hg, hxg⟩ := List.mem_flatMap.mp hx
    exact row_cons_eq _ (rowOfSkelH_sem _ (hsem g hg)) x hxg
  have hpk : pathKind (walkReadsH rows) = walkReadsH rows := by
    unfold pathKind
    refine List.filter_eq_self.mpr ?_
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    have h2 := (hall x hx).1
    simp only [isPathAx, decide_eq_true_eq]
    rw [show depthOf x.2.1 = (axisBits x.2.1).length from rfl, axisBits_of_two_le h2]
    simp
  have hslot : ∀ r ∈ pathReads (walkReadsH rows), (Noun.slot r.2 r.1).isSome := by
    intro r hr
    have hr' : r ∈ walkReadsH rows := by
      unfold pathReads at hr
      exact (List.mem_filter.mp (List.mem_dedup.mp hr)).1
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr'
    simp [(hall x hx).2]
  rw [walk_provide_total W cells _ hslot (fun _ => rfl), hpk]
  unfold walkReadsH
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  congr 1
  have hs := (hall x hx).2
  unfold entRecP readRecH
  simp [hs]

end Rows

end

end Nock.NockVMROM.Thm54.VclL.Handle
