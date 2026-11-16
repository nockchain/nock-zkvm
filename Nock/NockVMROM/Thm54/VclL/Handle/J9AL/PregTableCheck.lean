/-
 Nock/NockVMROM/Thm54/VclL/Handle/J9AL/PregTableCheck.lean

 **A Bool check on a table of the ALU's `preg` columns implies `PregOK`.**

 `pregTableOK nL prims tbl` is a computable check on a table `tbl : Fin 3 → Fin nL → ZMod p` (column `k` at row
 `i`, with `k = 0, 1, 2` the layout columns `sP, pId, pOp`): the primitive list fits in the `nL` rows and every
 entry equals `CheckJ9AL.pregCol prims k i`.

 * `pregOK_of_tableCheck`: if a polynomial triple `preL` evaluates at the row nodes to the table and the
 check passes, then `AcceptsJ9AL.PregOK nodesL prims preL` (the pre-column spec consumed by `ALChipOK`).
 * `pregOK_of_tableCheck_interp`: the same for the Lagrange interpolant of the table over the row nodes.
 * `pregTableOK_iff`: the check is equivalent to the length bound together with the pointwise equations.
-/
import Nock.V1J9AL.CheckJ9AL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE

open Nock Nock.Field Polynomial
open Nock.Jet.Prim (PrimOp)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL (PregOK)
open Nock.V1J9AL.CheckJ9AL (pregCol)

section

/-- The executable check: `prims` fits in `nL` rows and each of the three columns of `tbl` equals `pregCol`. -/
def pregTableOK (nL : ℕ) (prims : List (ℕ × PrimOp)) (tbl : Fin 3 → Fin nL → ZMod p) : Bool :=
  decide (prims.length ≤ nL) &&
    (List.finRange nL).all fun i => (List.finRange 3).all fun k => tbl k i == pregCol prims (k : ℕ) (i : ℕ)

theorem pregTableOK_iff (nL : ℕ) (prims : List (ℕ × PrimOp)) (tbl : Fin 3 → Fin nL → ZMod p) :
    pregTableOK nL prims tbl = true ↔
      prims.length ≤ nL ∧ ∀ (k : Fin 3) (i : Fin nL), tbl k i = pregCol prims (k : ℕ) (i : ℕ) := by
  simp [pregTableOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  tauto

/-- **A passing table check gives `PregOK`** for any `preL` that evaluates to the table at the row nodes. -/
theorem pregOK_of_tableCheck {nL : ℕ} (nodesL : Fin nL → ZMod p) (prims : List (ℕ × PrimOp))
    (tbl : Fin 3 → Fin nL → ZMod p) (preL : Fin 3 → (ZMod p)[X])
    (hev : ∀ (k : Fin 3) (i : Fin nL), (preL k).eval (nodesL i) = tbl k i)
    (hchk : pregTableOK nL prims tbl = true) : PregOK nodesL prims preL := by
  obtain ⟨hlen, h⟩ := (pregTableOK_iff nL prims tbl).mp hchk
  refine ⟨hlen, fun i => ⟨?_, ?_, ?_⟩⟩
  · rw [hev 0 i, h 0 i]; simp [pregCol]
  · rw [hev 1 i, h 1 i]; simp [pregCol]
  · rw [hev 2 i, h 2 i]; simp [pregCol]

/-- The same for the Lagrange interpolant of the table over injective nodes. -/
theorem pregOK_of_tableCheck_interp {nL : ℕ} (nodesL : Fin nL → ZMod p) (hinj : Function.Injective nodesL)
    (prims : List (ℕ × PrimOp)) (tbl : Fin 3 → Fin nL → ZMod p)
    (hchk : pregTableOK nL prims tbl = true) :
    PregOK nodesL prims (fun k => Lagrange.interpolate Finset.univ nodesL (tbl k)) :=
  pregOK_of_tableCheck nodesL prims tbl _
    (fun k i => Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)) hchk

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE
#print axioms pregTableOK_iff
#print axioms pregOK_of_tableCheck
#print axioms pregOK_of_tableCheck_interp
end Axioms
