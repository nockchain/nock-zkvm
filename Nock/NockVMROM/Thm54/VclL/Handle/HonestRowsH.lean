/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestRowsH.lean

  Additive: a NEW row
  builder `rowOfSkelH` beside `rowOfSkel` (not an edit).  No base gate reads those columns on OP3, so `honest_row_base_gates` is
  re-proved at `rowOfSkelH` (`honest_row_base_gatesH`), and the demand covers the hosted cells
  (`handle_cells_memH`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestDemand
import Nock.NockVMROM.Thm54.VclL.Handle.HonestLookups

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Walk Nock.Reified
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.SemanticStrategy ComputeTable

noncomputable section

/-- **The honest row with the OP3 witness hosted.** -/
def rowOfSkelH (sk : ComputeRowSkeleton) : RowN :=
  let r := rowOfSkel sk
  if r.op = 3 then { r with ftth := VclL.hdN r.sf1, fttt := VclL.tlN r.sf1 } else r

theorem rowOfSkelH_of_ne (sk : ComputeRowSkeleton) (h : (rowOfSkel sk).op ≠ 3) :
    rowOfSkelH sk = rowOfSkel sk := by simp [rowOfSkelH, h]

theorem rowOfSkelH_op (sk : ComputeRowSkeleton) : (rowOfSkelH sk).op = (rowOfSkel sk).op := by
  by_cases h : (rowOfSkel sk).op = 3 <;> simp [rowOfSkelH, h]

theorem rowOfSkelH_sem (sk : ComputeRowSkeleton) (h : (rowOfSkel sk).Sem) : (rowOfSkelH sk).Sem := by
  unfold rowOfSkelH
  by_cases h3 : (rowOfSkel sk).op = 3
  · simp only [h3, if_true]
    revert h
    generalize rowOfSkel sk = r at h3 ⊢
    intro h
    simp only [RowN.Sem, h3] at h ⊢
    exact h
  · simp [h3, h]

section Run
variable {K F : Type} [Field K] [Field F]

/-- **Gate satisfaction at every honest row of a run, at the OP3-hosted row.** -/
theorem honest_row_base_gatesH
    {fuel : ℕ} {subject formula result : Noun} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    {g : GenComputeRow K} (hg : g ∈ bfsRows (airReorder t))
    (cells : List Noun) (fst lst : F) (r0 : RowN)
    (hat : AtomsLt (ringChar F) (rowOfSkelH g.skel).sf1 ∧ AtomsLt (ringChar F) (rowOfSkelH g.skel).sf2)
    (hroot : fst = 0 ∨ ((rowOfSkelH g.skel).s = r0.s ∧ (rowOfSkelH g.skel).f = r0.f ∧
      (rowOfSkelH g.skel).e = r0.e)) :
    ∀ gate ∈ (arithGates : List (CoeffExpr ℚ)) ++ (eqGates : List (EqG ℚ)).map EqG.gate,
      (mapC (fun q : ℚ => (q : F)) gate).eval
        (hEnv cells (rowOfSkelH g.skel) fst lst (pubVec cells r0)) = 0 := by
  have hsem : (rowOfSkelH g.skel).Sem := rowOfSkelH_sem _ (run_rows_sem h g hg)
  refine base_gates_hold cells _ fst lst _ hsem hat ?_
  rcases hroot with h0 | ⟨e1, e2, e3⟩
  · exact Or.inl h0
  · right
    simp [pubVec, e1, e2, e3]

end Run

/-- **The OP3 witness is hosted**: the record read from the hosted columns of an OP3 row with a cell
operand is exactly the consumed export entry (`entryRec`), hence the export key of `sf1`. -/
theorem op3_witness_hosted {F : Type} [Field F] (sk : ComputeRowSkeleton) (cells : List Noun)
    (fst lst : F) (h3 : (rowOfSkel sk).op = 3) (_hs : (rowOfSkel sk).Sem)
    (hc : (rowOfSkel sk).sf1.isCell = true) :
    ((colVal cells (rowOfSkelH sk) fst lst 26,
      (colVal cells (rowOfSkelH sk) fst lst 37, colVal cells (rowOfSkelH sk) fst lst 38),
      (colVal cells (rowOfSkelH sk) fst lst 39, colVal cells (rowOfSkelH sk) fst lst 40)) :
        F × (F × F) × (F × F)) = expKey cells (rowOfSkel sk).sf1 := by
  have hop : (rowOfSkelH sk).op ≠ 5 := by rw [rowOfSkelH_op, h3]; omega
  have hn' : hn (rowOfSkelH sk) = rowOfSkelH sk := hn_of_ne _ hop
  have e1 : (rowOfSkelH sk).sf1 = (rowOfSkel sk).sf1 := by simp [rowOfSkelH, h3]
  have e2 : (rowOfSkelH sk).ftth = VclL.hdN (rowOfSkel sk).sf1 := by simp [rowOfSkelH, h3]
  have e3 : (rowOfSkelH sk).fttt = VclL.tlN (rowOfSkel sk).sf1 := by simp [rowOfSkelH, h3]
  simp only [cv26, cv37, cv38, cv39, cv40, hn', e1, e2, e3, expKey]
  obtain ⟨a, b, hab⟩ : ∃ a b, (rowOfSkel sk).sf1 = Noun.cell a b := by
    revert hc; generalize (rowOfSkel sk).sf1 = x
    cases x with
    | atom _ => intro hc; simp [Noun.isCell] at hc
    | cell a b => intro _; exact ⟨a, b, rfl⟩
  rw [hab]
  simp [hdl, VclL.hdN, VclL.tlN]

/-- **The demand covers the hosted cells**: the twelve handle nouns of `rowOfSkelH` that are cells are
rows of `demandH`'s table. -/
theorem handle_cells_memH {K : Type} [Field K] (rows : List (GenComputeRow K)) {g : GenComputeRow K}
    (hg : g ∈ rows) :
    ∀ n ∈ rowHandleNouns (hn (rowOfSkelH g.skel)), n.isCell = true → n ∈ (demandH rows).cells := by
  by_cases h3 : (rowOfSkel g.skel).op = 3
  · intro n hn' hc
    have hop : (rowOfSkelH g.skel).op ≠ 5 := by rw [rowOfSkelH_op, h3]; omega
    rw [hn_of_ne _ hop] at hn'
    have hs1 : (rowOfSkel g.skel).sf1 ∈ handleNouns g := by simp [handleNouns]
    have hsub : ∀ x, x ∈ cellsOf (rowOfSkel g.skel).sf1 → x ∈ (demandH rows).cells := by
      intro x hx
      refine mem_closureOf.mpr ⟨_, ?_, hx⟩
      simp only [Demand.roots, demandH, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inl ⟨g, hg, hs1⟩)
    have hold := handle_cells_mem rows hg
    have hrow : rowOfSkelH g.skel = { rowOfSkel g.skel with ftth := VclL.hdN (rowOfSkel g.skel).sf1, fttt := VclL.tlN (rowOfSkel g.skel).sf1 } := by
      simp [rowOfSkelH, h3]
    have hop0 : (rowOfSkel g.skel).op ≠ 5 := by omega
    simp only [hrow, rowHandleNouns, List.mem_cons, List.not_mem_nil, or_false] at hn'
    rcases hn' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (refine hold _ ?_ hc; rw [hn_of_ne _ hop0]; simp [rowHandleNouns]; done)
      | skip
    · exact hsub _ (hdN_cells hc)
    · exact hsub _ (tlN_cells hc)
  · rw [rowOfSkelH_of_ne _ h3]
    exact handle_cells_mem rows hg

end

end Nock.NockVMROM.Thm54.VclL.Handle
