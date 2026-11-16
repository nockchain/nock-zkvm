/-
  Nock/Jet/ChipJ8RToy.lean

  **The honest `n = 2` toy re-checked at `J8R`.**  New module, additive.
  J-3b's honest trace (`toyRowsJ`, `p = 1009`, `R = matmulT 2`, one call) meets `J8R`'s base gates
  (`baseGatesJR` = `baseGatesJ` + `regKindGate`): the registry row's handle is the cell handle
  `(1, idx)` of `compile 1009 (matmulT 2)` in the list memory, which denotes the formula (`toy_reg`).
  The call row has weight `m = 1 ≠ 0` and its subject denotes (`toyCall_subject`), so the weighted
  `hSubW` obligation is met at the toy.

  NOT built here (U): the honest fill of `J8R`'s new `𝕂′` columns (the registry consume inverse, its
  accumulator, `A`) and the cell table serving the registry claim key (the toy's memory is a list).
-/
import Nock.Jet.ChipJ8Toy
import Nock.Jet.RegJ8R

set_option autoImplicit false

namespace Nock.Jet.ChipJ8

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen Nock.Jet.Interp
open Nock.NockVMROM.Thm54.CoordinateCompiler

/-- The toy's registry rows carry kind `1`. -/
theorem toy_regRows_kN :
    (toyRowsJ.filter fun r => r.pre.kd == .reg).all (fun r => r.w.kN == 1) = true := by decide +kernel

/-- **`regKindGate` on every honest row.** -/
theorem toy_regKind : ∀ r ∈ toyRowsJ, (regKindGate : CoeffExpr (ZMod 1009)).eval (envOf r) = 0 := by
  intro r hr
  by_cases hk : r.pre.kd = .reg
  · refine RegJ8R.regKind_on ?_
    have := List.all_eq_true.mp toy_regRows_kN r (List.mem_filter.mpr ⟨hr, by simp [hk]⟩)
    simpa using this
  · exact RegJ8R.regKind_off hk

/-- **The honest toy meets `J8R`'s base gates.** -/
theorem toy_gatesR : ∀ r ∈ toyRowsJ, ∀ g ∈ (baseGatesJR : List (CoeffExpr (ZMod 1009))),
    g.eval (envOf r) = 0 := by
  intro r hr g hg
  rcases List.mem_append.mp hg with h | h
  · exact toy_gates r hr g h
  · simp only [List.mem_singleton] at h; subst h; exact toy_regKind r hr

/-- The toy call is weighted (`m = 1`) and its subject denotes: the weighted `hSubW` at the toy. -/
theorem toyCall_weighted : toyCall.w.m ≠ 0 ∧ toyDen (toyCall.w.kL, toyCall.w.vL) = some toyS :=
  ⟨by decide, toyCall_subject⟩

/-- **The registry handle is a cell handle denoting the formula** (`regKindGate` + `toy_reg`). -/
theorem toy_reg_cell : ∀ r ∈ toyRowsJ, r.pre.kd = .reg →
    r.w.kN = 1 ∧ toyDen (r.w.kN, r.w.vN) = some (compile 1009 (toyR r.pre.id)) := fun r hr hk =>
  ⟨RegJ8R.kN_of_regKind hk (toy_regKind r hr), toy_reg r hr hk⟩

end Nock.Jet.ChipJ8
