/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestRun.lean

  Additive; `Gen.lean` is read only.

  The honest row of a generated BFS row `g` of the AIR-reordered tree is `rowOfSkel g.skel`
  (`HonestShape`), with handles over the honest cell-row list `cells` (`HonestRows`).  Generic over the
  run: the only hypotheses are the atom bound on the two operands of the row (needed for the OP5
  atom-value inverse `w`; discharged concretely on the toys, `HonestToys`) and the first-row
  publics (the claim handles are the root row's).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestRows
import Nock.NockVMROM.Thm54.VclL.Handle.HonestLink

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Walk Nock.Reified
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.VclL

noncomputable section

section Run
variable {K F : Type} [Field K] [Field F]

/-- **Gate satisfaction at every honest row of a run.** -/
theorem honest_row_base_gates
    {fuel : ℕ} {subject formula result : Noun} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    {g : GenComputeRow K} (hg : g ∈ bfsRows (airReorder t))
    (cells : List Noun) (fst lst : F) (r0 : RowN)
    (hat : AtomsLt (ringChar F) (rowOfSkel g.skel).sf1 ∧ AtomsLt (ringChar F) (rowOfSkel g.skel).sf2)
    (hroot : fst = 0 ∨ ((rowOfSkel g.skel).s = r0.s ∧ (rowOfSkel g.skel).f = r0.f ∧
      (rowOfSkel g.skel).e = r0.e)) :
    ∀ gate ∈ (arithGates : List (CoeffExpr ℚ)) ++ (eqGates : List (EqG ℚ)).map EqG.gate,
      (mapC (fun q : ℚ => (q : F)) gate).eval
        (hEnv cells (rowOfSkel g.skel) fst lst (pubVec cells r0)) = 0 := by
  have hsem : (rowOfSkel g.skel).Sem := by
    unfold bfsRows at hg
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
    obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ u).mp hu
    simp only [List.mem_singleton] at hc
    subst hc
    exact airReorder_rowShape h u hin
  refine base_gates_hold cells _ fst lst _ hsem hat ?_
  rcases hroot with h0 | ⟨e1, e2, e3⟩
  · exact Or.inl h0
  · right
    simp [pubVec, e1, e2, e3]

end Run

end

end Nock.NockVMROM.Thm54.VclL.Handle
