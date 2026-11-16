/-
  Nock/RedTeam/Batch27Thm54CoordinateCompiler.lean

  Locked facts:

  1. **`e = 1` round-trip.**  Over the degenerate extension `K = F` the compiler is the identity:
     the compiled coordinate expression evaluates to the original `K`-value.  So the compiler is not
     an arbitrary re-encoding — it specializes correctly.
  2. **A genuine `e = 3` `Mul` receipt over `𝔽_{2^3}`.**  The tensor expansion holds at `e = 3`;
     the structure constants are *not* all zero; and coordinatewise multiplication is provably the
     *wrong* rule (`coord (b₀·b₁) ≠ coord b₀ · coord b₁` in some coordinate), which is exactly why a
     multiplication tensor is required rather than the linear pilot.
  3. **Degree is not increased on a `Mul` node.**  The compiled coordinates of the degree-`2` node
     `x₀ · x₁` still have degree at most `2`.
  4. **Width sanity.**  One `K`-column expands to exactly `e` base columns (`stdCol0` blocks), and
     `Batch17.expandedWidth 13 62 3 = 199` — the paper's `e = 3` compute width.  This is a width
     receipt only: **no RAP is claimed to be built here.**
-/

import Nock.NockVMROM.Thm54.CoordinateCompiler
import Nock.RedTeam.Batch17Thm54ColumnCensus
import Mathlib.FieldTheory.Finite.GaloisField

namespace Nock.RedTeam.Batch27

open Nock.Reified
open Module
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler

noncomputable section

/-! ## 1. The `e = 1` round-trip -/

variable {F : Type*} [Field F]

/-- The degenerate coordinate basis of `F` over itself. -/
noncomputable def oneBasis (F : Type*) [Field F] : Basis (Fin 1) F F :=
  Basis.singleton (Fin 1) F

/-- At `e = 1` the coordinate map is the identity. -/
theorem b27_e1_coord_id (x : F) (k : Fin 1) : coord (oneBasis F) x k = x := by
  simp [coord, oneBasis, Basis.singleton_repr]

/-- **`e = 1` round-trip.**  The compiled single coordinate of any constraint expression evaluates
back to the original `K`-value, so the compiler specializes to the identity on the degenerate
extension. -/
theorem b27_e1_roundtrip (E : Expr) (envK : Env F) :
    E.eval envK =
      (coordinateCompile (oneBasis F) (stdCol0 1) E 0).eval (stdCoordEnv (oneBasis F) envK) := by
  have h := coordinateCompile_eval (oneBasis F) (stdCol0 1)
    (isCoordEnv_std (oneBasis F) envK) E 0
  rwa [b27_e1_coord_id] at h

/-! ## 2. A genuine `e = 3` `Mul` receipt over `𝔽_{2^3}` -/

/-- The base field `𝔽_2`. -/
abbrev F2 : Type := ZMod 2

/-- The degree-`3` extension `𝔽_{2^3}`. -/
abbrev K8 : Type := GaloisField 2 3

/-- A three-element coordinate basis of `𝔽_{2^3}` over `𝔽_2`. -/
noncomputable def b3 : Basis (Fin 3) F2 K8 :=
  stdCoordBasis F2 K8 3 (GaloisField.finrank 2 (by norm_num))

/-- **The tensor expansion at `e = 3`.**  Every product's coordinate is the contraction of the
factors' coordinates against the structure constants of `𝔽_{2^3}/𝔽_2`. -/
theorem b27_e3_coord_mul (x y : K8) (k : Fin 3) :
    coord b3 (x * y) k = ∑ i, ∑ j, coord b3 x i * coord b3 y j * mulTensor b3 i j k :=
  coord_mul b3 x y k

/-- **The structure constants are not all zero** for the concrete pair `(b₀, b₁)`, so the `Mul` case
of the compiler contracts against nontrivial data. -/
theorem b27_e3_mulTensor_nontrivial : ∃ k, mulTensor b3 0 1 k ≠ 0 :=
  mulTensor_not_all_zero b3 0 1

/-- **Coordinatewise multiplication is the wrong rule at `e = 3`.**  For the concrete pair
`x = b₀`, `y = b₁` the true product has a nonzero coordinate while the coordinatewise product is
identically zero — the tensor is genuinely needed, the linear pilot does not suffice. -/
theorem b27_e3_pointwise_mul_is_wrong :
    ∃ k, coord b3 (b3 0 * b3 1) k ≠ coord b3 (b3 0) k * coord b3 (b3 1) k := by
  obtain ⟨k, hk⟩ := b27_e3_mulTensor_nontrivial
  refine ⟨k, ?_⟩
  have hzero : coord b3 (b3 0) k * coord b3 (b3 1) k = 0 := by
    rcases eq_or_ne k 0 with rfl | hk0
    · have : coord b3 (b3 1) 0 = 0 := by
        simp [coord, Basis.repr_self]
      simp [this]
    · have : coord b3 (b3 0) k = 0 := by
        simp [coord, Basis.repr_self, Ne.symm hk0]
      simp [this]
  rw [hzero]
  exact fun hcontra => hk (by rw [← hcontra]; rfl)

/-- The concrete degree-`2` `Mul` node `x₀ · x₁`. -/
def mulNode : Expr := .Mul (.Var .traceCur 0) (.Var .traceCur 1)

theorem b27_mulNode_degree : mulNode.degree = 2 := by
  simp [mulNode, Expr.degree]

/-- **The `e = 3` `Mul` evaluation regression.**  On the concrete node `x₀ · x₁`, each of the three
compiled base-field coordinate expressions evaluates to the corresponding coordinate of the
`K`-valued product, in the canonically expanded environment. -/
theorem b27_e3_mulNode_eval (envK : Env K8) (k : Fin 3) :
    coord b3 (mulNode.eval envK) k =
      (coordinateCompile b3 (stdCol0 3) mulNode k).eval (stdCoordEnv b3 envK) :=
  coordinateCompile_eval b3 (stdCol0 3) (isCoordEnv_std b3 envK) mulNode k

/-- **One `K`-equation ⟺ three base-field equations** on the concrete `Mul` node. -/
theorem b27_e3_mulNode_zero_iff (envK : Env K8) :
    mulNode.eval envK = 0 ↔
      ∀ k, (coordinateCompile b3 (stdCol0 3) mulNode k).eval (stdCoordEnv b3 envK) = 0 :=
  coordinateCompile_zero_iff_std b3 envK mulNode

/-! ## 3. Degree preservation on a `Mul` node -/

/-- **Degree preservation regression.**  The compiled coordinates of the degree-`2` `Mul` node have
degree at most `2`: nonlinear coordinate expansion does not inflate the AIR degree budget. -/
theorem b27_e3_mulNode_degree_le (k : Fin 3) :
    (coordinateCompile b3 (stdCol0 3) mulNode k).degree ≤ 2 := by
  have h := coordinateCompile_degree_le b3 (stdCol0 3) mulNode k
  rwa [b27_mulNode_degree] at h

/-- The general degree bound, instantiated at `e = 3` over `𝔽_{2^3}`. -/
theorem b27_e3_degree_le (E : Expr) (k : Fin 3) :
    (coordinateCompile b3 (stdCol0 3) E k).degree ≤ E.degree :=
  coordinateCompile_degree_le b3 (stdCol0 3) E k

/-! ## 4. Width sanity (receipt only — no RAP is built here) -/

/-- Consecutive `K`-columns occupy disjoint blocks of exactly `e` base columns. -/
theorem b27_block_width (e : ℕ) (kind : VarKind) (idx : ℕ) :
    stdCol0 e kind (idx + 1) = stdCol0 e kind idx + e :=
  stdCol0_succ e kind idx

/-- **Width receipt.**  A `(13, 62)` base/extension column split expands to `13 + 62·3 = 199` base
columns at `e = 3` — the paper's compute width.  This records the arithmetic the compiler's
`e`-column blocks feed into; it does **not** claim the monolithic RAP is constructed. -/
theorem b27_expanded_width_e3 : Batch17.expandedWidth 13 62 3 = 199 := by
  decide

end

end Nock.RedTeam.Batch27

#print axioms Nock.RedTeam.Batch27.b27_e1_roundtrip
#print axioms Nock.RedTeam.Batch27.b27_e3_coord_mul
#print axioms Nock.RedTeam.Batch27.b27_e3_mulTensor_nontrivial
#print axioms Nock.RedTeam.Batch27.b27_e3_pointwise_mul_is_wrong
#print axioms Nock.RedTeam.Batch27.b27_e3_mulNode_eval
#print axioms Nock.RedTeam.Batch27.b27_e3_mulNode_zero_iff
#print axioms Nock.RedTeam.Batch27.b27_e3_mulNode_degree_le
#print axioms Nock.RedTeam.Batch27.b27_expanded_width_e3
