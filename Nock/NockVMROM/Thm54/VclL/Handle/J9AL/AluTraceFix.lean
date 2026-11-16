/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AluTraceFix.lean

  **The virtual zero successor of the
  ALU's last row.** Pure polynomial facts.

  Unmasked, the ALU's next-row gates are not guarded by `1 − isLT` (`AluHonestRows` module note; the last-row mask of
  `docs/j8/SPEC.md` §15.2 now guards them, and this construction does not rely on it), so the honest trace must
  make `sL` vanish at the successor `x* = nodes (n−1)·ω` of the last node.  `RAP.Satisfies` has no degree bound,
  so the honest `sL` polynomial is `fixAt P Z x*` with `Z = ∏ (X − nodes i)`:
  * `fixAt_eval_node`: unchanged at every row node;
  * `fixAt_eval_x`: `0` at `x*` when `x*` is not a node;
  * `succ_last_mem_node`: when `x*` IS a node (`Z x* = 0`), it is `nodes 0` (adjacency + injectivity + `ω ≠ 0`),
    so the successor of the last row is row `0` (a preg or padding row, `sL = 0`).
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluTraceFix

open Polynomial

variable {F : Type} [Field F] [DecidableEq F]

/-- The vanishing polynomial of the row nodes. -/
noncomputable def zNodes {n : ℕ} (nodes : Fin n → F) : F[X] := ∏ i, (X - C (nodes i))

theorem zNodes_eval_node {n : ℕ} (nodes : Fin n → F) (i : Fin n) : (zNodes nodes).eval (nodes i) = 0 := by
  rw [zNodes, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem zNodes_eval_eq_zero {n : ℕ} (nodes : Fin n → F) {x : F} (h : (zNodes nodes).eval x = 0) :
    ∃ i, x = nodes i := by
  rw [zNodes, eval_prod, Finset.prod_eq_zero_iff] at h
  obtain ⟨i, -, hi⟩ := h
  exact ⟨i, by simpa [sub_eq_zero] using hi⟩

/-- **`P` corrected to vanish at `x`** by a multiple of `Z` (unchanged if `Z x = 0`). -/
noncomputable def fixAt (P Z : F[X]) (x : F) : F[X] :=
  if Z.eval x = 0 then P else P - C (P.eval x / Z.eval x) * Z

theorem fixAt_eval_node (P Z : F[X]) (x : F) {z : F} (hz : Z.eval z = 0) : (fixAt P Z x).eval z = P.eval z := by
  unfold fixAt; split_ifs <;> simp [hz]

theorem fixAt_eval_x (P Z : F[X]) {x : F} (hx : Z.eval x ≠ 0) : (fixAt P Z x).eval x = 0 := by
  unfold fixAt; simp [hx, div_mul_cancel₀ _ hx]

/-- **The last node's successor, if a node, is node `0`.** -/
theorem succ_last_mem_node {n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (hinj : Function.Injective nodes) (ω : F)
    (hω : ω ≠ 0) (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (h : (zNodes nodes).eval (nodes ⟨n - 1, by omega⟩ * ω) = 0) :
    nodes ⟨n - 1, by omega⟩ * ω = nodes ⟨0, hn⟩ := by
  obtain ⟨⟨i, hi⟩, hx⟩ := zNodes_eval_eq_zero nodes h
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact hx
  · exfalso
    have hprev := hadj ⟨i - 1, by omega⟩ (by simp; omega)
    have e : (⟨i - 1 + 1, by omega⟩ : Fin n) = ⟨i, hi⟩ := Fin.ext (by simp; omega)
    rw [e] at hprev
    rw [hprev] at hx
    have := hinj (mul_right_cancel₀ hω hx)
    have := congrArg Fin.val this
    simp at this
    omega

end Nock.NockVMROM.Thm54.VclL.Handle.AluTraceFix

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.AluTraceFix
#print axioms fixAt_eval_node
#print axioms fixAt_eval_x
#print axioms succ_last_mem_node
end Axioms
