/-
  Nock/NockVMROM/Thm54/CoordinateBasis.lean

  Packet 1 of the Theorem 5.4 north star: the coordinate-basis / `Expr`-substitution pilot.

  Composing the segmented `K`-valued AIRs into the paper's base-field monolithic RAP requires
  *coordinate expansion*: representing each `K = 𝔽_{q^e}` column as `e` base-field `𝔽_q` columns
  against a fixed `𝔽_q`-basis of `K`.  This module pilots that expansion for the **linear fragment**,
  which is what the row-linking / topology / one-hot constraints live in, and states exactly where the
  nonlinear case is deferred.

  Value side (`CoordinateBasis`):

  * `stdCoordBasis` — an `𝔽_q`-basis of `K` with exactly `e = finrank` elements.
  * `coord` / `reconstruct` and `reconstruct_coord` — a `K`-value is the basis combination of its
    coordinates.
  * `eq_iff_coords_eq` — **one `K`-equality is equivalent to `e` coordinate equalities.**  This is the
    load-bearing fact: a single `K`-valued linear constraint expands to `e` base-field constraints.
  * `coord_add` / `coord_smul` — coordinates are `𝔽_q`-linear, so *linear* constraints expand to
    *linear* coordinate constraints (degree preserved).

  Column side (re-exported from `ExprReindex`):

  * `Expr.eval_shiftTrace` / `Expr.degree_shiftTrace` — laying the `e` coordinate columns at disjoint
    offsets preserves evaluation and, crucially, **degree**.

  Deferred (honest boundary): `Expr.Const` carries `ℤ` coefficients, so a basis element `b i ∈ K \ ℤ`
  cannot be an `Expr` constant.  Hence *nonlinear* (`Mul`) coordinate expansion needs the extension's
  structure constants and a base-field `Expr` type; that is Packet 5, not this pilot.
-/

import Nock.NockVMROM.Thm54.ExtensionField
import Nock.NockVMROM.Thm54.ExprReindex
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Free

namespace Nock.NockVMROM.Thm54
namespace CoordinateBasis

open scoped Classical
open Module

noncomputable section

variable (F K : Type*) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- A coordinate basis of `K` over `F` with exactly `e` elements, when `finrank F K = e`. -/
noncomputable def stdCoordBasis (e : ℕ) (he : Module.finrank F K = e) :
    Basis (Fin e) F K :=
  Module.finBasisOfFinrankEq F K he

variable {F K}

/-- The `i`-th `F`-coordinate of a `K`-value against a coordinate basis. -/
def coord {e : ℕ} (b : Basis (Fin e) F K) (x : K) (i : Fin e) : F := b.repr x i

/-- Reconstruct a `K`-value from its `F`-coordinates. -/
def reconstruct {e : ℕ} (b : Basis (Fin e) F K) (c : Fin e → F) : K :=
  ∑ i, c i • b i

/-- **A `K`-value is the basis combination of its own coordinates.** -/
theorem reconstruct_coord {e : ℕ} (b : Basis (Fin e) F K) (x : K) :
    reconstruct b (coord b x) = x := by
  simp only [reconstruct, coord]
  exact b.sum_repr x

/-- **One `K`-equality is equivalent to `e` coordinate equalities.**  A single `K`-valued constraint
therefore expands to exactly `e` base-field coordinate constraints. -/
theorem eq_iff_coords_eq {e : ℕ} (b : Basis (Fin e) F K) (x y : K) :
    x = y ↔ ∀ i, coord b x i = coord b y i := by
  constructor
  · rintro rfl i; rfl
  · intro h
    apply b.repr.injective
    ext i
    exact h i

/-- Coordinates are additive: expanding `x + y` gives the coordinatewise sum. -/
theorem coord_add {e : ℕ} (b : Basis (Fin e) F K) (x y : K) (i : Fin e) :
    coord b (x + y) i = coord b x i + coord b y i := by
  simp only [coord, map_add, Finsupp.add_apply]

/-- Coordinates are `F`-linear: expanding `a • x` scales each coordinate by `a`. -/
theorem coord_smul {e : ℕ} (b : Basis (Fin e) F K) (a : F) (x : K) (i : Fin e) :
    coord b (a • x) i = a • coord b x i := by
  simp only [coord, map_smul, Finsupp.smul_apply]

/-! ## Column side: laying coordinate columns preserves evaluation and degree -/

/-- **Laying the `e` coordinate columns at a disjoint offset preserves degree** (re-export of the
kernel-clean `ExprReindex` shift). -/
theorem coordColumn_degree_preserved (off : ℕ) (e : Nock.Reified.Expr) :
    (e.shiftTrace off).degree = e.degree :=
  Nock.Reified.Expr.degree_shiftTrace off e

/-- **Laying the `e` coordinate columns at a disjoint offset preserves evaluation.** -/
theorem coordColumn_eval_preserved {L : Type*} [Field L] (off : ℕ)
    (e : Nock.Reified.Expr) (env : Nock.Reified.Env L) :
    (e.shiftTrace off).eval env =
      e.eval { env with
        trace := fun i => env.trace (i + off)
        traceNext := fun i => env.traceNext (i + off) } :=
  Nock.Reified.Expr.eval_shiftTrace off e env

/-! ## Instantiation over the strict extension field -/

/-- The strict extension field `𝔽_{(pS n)^e}` carries a coordinate basis of `e` elements over its
prime base field. -/
noncomputable def strictCoordBasis
    (e : ℕ) [NeZero e] (Ksz h : ℕ → ℕ) (kroots : ℕ) (n : ℕ) :
    Basis (Fin e) (ZMod (StrictExtension.pS e Ksz h kroots n))
      (StrictExtension.StrictExtensionField e Ksz h kroots n) :=
  stdCoordBasis _ _ e
    (StrictExtension.extensionFieldAt_finrank e (StrictExtension.pS e Ksz h kroots)
      (NeZero.ne e) n)

end

end CoordinateBasis
end Nock.NockVMROM.Thm54
