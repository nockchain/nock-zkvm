/-
  Nock/NockVMROM/Thm54/TraceGen/CubicField97.lean

  A self-contained **computable** cubic field extension `K3` of `ZMod 97`.

  The Theorem-5.4 capstone requires a degree-3 base field (`Basis (Fin 3) F K`,
  i.e. `finrank = 3`, see the paper for the degree-3 extension role), but
  the existing `K97cubic = GaloisField 97 3` is noncomputable, which blocks reaching a
  *generated-AND-executable* statement.  This module provides a concrete, `#eval`-able
  model of `𝔽_{97^3}` as `ZMod 97[X]/(X^3 - 5)` with all operations in closed form.

  Because `3 ∣ 96 = 97 - 1` and `5` is a non-cube mod 97 (`5^32 ≠ 1`), the polynomial
  `X^3 - 5` is irreducible over `ZMod 97`, so the quotient is a field of cardinality
  `97^3`.  Multiplication, the norm, the cofactor and the inverse are all polynomial in
  the coordinates, hence computable.  Field soundness (`norm3 a ≠ 0` for `a ≠ 0`) is
  proved by transporting `IsDomain` from `AdjoinRoot (X^3 - C 5)`; those proofs are
  `Prop`-valued and do not affect computability of the operations.
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases

namespace Nock.NockVMROM.Thm54.TraceGen
namespace CubicField97

/-- `97` is prime, so `ZMod 97` is a field (the coefficient field of the extension). -/
instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- The concrete cubic extension `ZMod 97[X]/(X^3 - 5)`, represented as its coordinate
triple in the power basis `1, X, X^2`. -/
@[ext]
structure K3 where
  c0 : ZMod 97
  c1 : ZMod 97
  c2 : ZMod 97
deriving DecidableEq, Repr

namespace K3

/-! ## Ring operations (closed form, computable) -/

instance : Zero K3 := ⟨⟨0, 0, 0⟩⟩
instance : One K3 := ⟨⟨1, 0, 0⟩⟩
instance : Add K3 := ⟨fun a b => ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩⟩
instance : Neg K3 := ⟨fun a => ⟨-a.c0, -a.c1, -a.c2⟩⟩
instance : Sub K3 := ⟨fun a b => ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2⟩⟩

/-- Multiplication in `ZMod 97[X]/(X^3 - 5)`: with `c = 5`,
`r0 = a0 b0 + c (a1 b2 + a2 b1)`, `r1 = a0 b1 + a1 b0 + c a2 b2`,
`r2 = a0 b2 + a1 b1 + a2 b0`. -/
instance : Mul K3 :=
  ⟨fun a b =>
    ⟨a.c0 * b.c0 + 5 * (a.c1 * b.c2 + a.c2 * b.c1),
     a.c0 * b.c1 + a.c1 * b.c0 + 5 * (a.c2 * b.c2),
     a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0⟩⟩

@[simp] theorem zero_c0 : (0 : K3).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : K3).c1 = 0 := rfl
@[simp] theorem zero_c2 : (0 : K3).c2 = 0 := rfl
@[simp] theorem one_c0 : (1 : K3).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : K3).c1 = 0 := rfl
@[simp] theorem one_c2 : (1 : K3).c2 = 0 := rfl
@[simp] theorem add_c0 (a b : K3) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : K3) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem add_c2 (a b : K3) : (a + b).c2 = a.c2 + b.c2 := rfl
@[simp] theorem neg_c0 (a : K3) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : K3) : (-a).c1 = -a.c1 := rfl
@[simp] theorem neg_c2 (a : K3) : (-a).c2 = -a.c2 := rfl
@[simp] theorem sub_c0 (a b : K3) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : K3) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem sub_c2 (a b : K3) : (a - b).c2 = a.c2 - b.c2 := rfl
@[simp] theorem mul_c0 (a b : K3) :
    (a * b).c0 = a.c0 * b.c0 + 5 * (a.c1 * b.c2 + a.c2 * b.c1) := rfl
@[simp] theorem mul_c1 (a b : K3) :
    (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 + 5 * (a.c2 * b.c2) := rfl
@[simp] theorem mul_c2 (a b : K3) :
    (a * b).c2 = a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 := rfl

/-! ## Commutative ring instance -/

instance commRing : CommRing K3 where
  add := (· + ·)
  mul := (· * ·)
  neg := (-·)
  sub := (· - ·)
  zero := 0
  one := 1
  nsmul n a := ⟨n • a.c0, n • a.c1, n • a.c2⟩
  zsmul n a := ⟨n • a.c0, n • a.c1, n • a.c2⟩
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  neg_add_cancel a := by ext <;> simp
  mul_comm a b := by ext <;> simp <;> ring
  sub_eq_add_neg a b := by ext <;> simp <;> ring
  nsmul_zero a := by ext <;> exact zero_nsmul _
  nsmul_succ n a := by ext <;> exact succ_nsmul _ _
  zsmul_zero' a := by ext <;> exact zero_zsmul _
  zsmul_succ' n a := by ext <;> exact (by push_cast; exact (add_one_zsmul _ _))
  zsmul_neg' n a := by ext <;> exact negSucc_zsmul _ _

/-! ## Algebra structure over `ZMod 97` (the coefficient embedding `x ↦ ⟨x, 0, 0⟩`) -/

/-- The coefficient embedding `ZMod 97 →+* K3`, `x ↦ ⟨x, 0, 0⟩`. -/
def coeHom : ZMod 97 →+* K3 where
  toFun x := ⟨x, 0, 0⟩
  map_one' := rfl
  map_mul' x y := by ext <;> simp
  map_zero' := rfl
  map_add' x y := by ext <;> simp

@[simp] theorem coeHom_c0 (x : ZMod 97) : (coeHom x).c0 = x := rfl
@[simp] theorem coeHom_c1 (x : ZMod 97) : (coeHom x).c1 = 0 := rfl
@[simp] theorem coeHom_c2 (x : ZMod 97) : (coeHom x).c2 = 0 := rfl

instance algebra : Algebra (ZMod 97) K3 := coeHom.toAlgebra

theorem algebraMap_eq : algebraMap (ZMod 97) K3 = coeHom := rfl

@[simp] theorem smul_c0 (r : ZMod 97) (a : K3) : (r • a).c0 = r * a.c0 := by
  show (coeHom r * a).c0 = r * a.c0; simp
@[simp] theorem smul_c1 (r : ZMod 97) (a : K3) : (r • a).c1 = r * a.c1 := by
  show (coeHom r * a).c1 = r * a.c1; simp
@[simp] theorem smul_c2 (r : ZMod 97) (a : K3) : (r • a).c2 = r * a.c2 := by
  show (coeHom r * a).c2 = r * a.c2; simp

/-! ## Norm, cofactor and the `a · cof a = norm3 a` identity -/

/-- The field norm `N(a) = a0^3 + c a1^3 + c^2 a2^3 - 3 c a0 a1 a2` (with `c = 5`), the
determinant of multiplication-by-`a`.  Polynomial, hence computable. -/
def norm3 (a : K3) : ZMod 97 :=
  a.c0 ^ 3 + 5 * a.c1 ^ 3 + 25 * a.c2 ^ 3 - 15 * (a.c0 * a.c1 * a.c2)

/-- The cofactor (adjugate) of `a`, so that `a · cof a = N(a)`. -/
def cof (a : K3) : K3 :=
  ⟨a.c0 ^ 2 - 5 * (a.c1 * a.c2), 5 * a.c2 ^ 2 - a.c0 * a.c1, a.c1 ^ 2 - a.c0 * a.c2⟩

/-- **`a · cof a = algebraMap (norm3 a)`.**  The core adjugate identity (`ext; ring`). -/
theorem mul_cof (a : K3) : a * cof a = coeHom (norm3 a) := by
  ext <;>
    simp only [mul_c0, mul_c1, mul_c2, cof, coeHom_c0, coeHom_c1, coeHom_c2, norm3] <;>
    ring

/-- `5` is not a cube in `ZMod 97` (checked by `decide`); this is why `X^3 - 5` is
irreducible. -/
theorem no_cube_root : ∀ x : ZMod 97, x ^ 3 ≠ 5 := by decide

/-- **The norm form is anisotropic:** `cof a = 0` forces `a = 0`.  If `a.c0 ≠ 0` and
`a.c1 ≠ 0`, the equations force `(a.c0 / a.c1)^3 = 5`, contradicting `no_cube_root`. -/
theorem eq_zero_of_cof_eq_zero {a : K3} (h : cof a = 0) : a = 0 := by
  have e0 : a.c0 ^ 2 - 5 * (a.c1 * a.c2) = 0 := by
    have := congrArg K3.c0 h; simpa [cof] using this
  have e1 : 5 * a.c2 ^ 2 - a.c0 * a.c1 = 0 := by
    have := congrArg K3.c1 h; simpa [cof] using this
  have e2 : a.c1 ^ 2 - a.c0 * a.c2 = 0 := by
    have := congrArg K3.c2 h; simpa [cof] using this
  have h5 : (5 : ZMod 97) ≠ 0 := by decide
  by_cases hx : a.c0 = 0
  · -- a.c0 = 0 ⟹ a.c2 = 0 (from e1) ⟹ a.c1 = 0 (from e2)
    have hz2 : a.c2 ^ 2 = 0 := by
      have : (5 : ZMod 97) * a.c2 ^ 2 = 0 := by rw [hx] at e1; linear_combination e1
      exact (mul_eq_zero.mp this).resolve_left h5
    have hz : a.c2 = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz2; exact this
    have hy : a.c1 = 0 := by
      have : a.c1 ^ 2 = 0 := by rw [hx, hz] at e2; linear_combination e2
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    ext <;> simp [hx, hy, hz]
  · -- a.c0 ≠ 0
    by_cases hy : a.c1 = 0
    · -- then a.c2 = 0 (e2) then a.c0 = 0 (e0), contradiction
      have hz : a.c2 = 0 := by
        have : a.c0 * a.c2 = 0 := by rw [hy] at e2; linear_combination -e2
        exact (mul_eq_zero.mp this).resolve_left hx
      exact absurd (by
        have : a.c0 ^ 2 = 0 := by rw [hy, hz] at e0; linear_combination e0
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this) hx
    · -- a.c0 ≠ 0, a.c1 ≠ 0: derive (a.c0 / a.c1)^3 = 5, contradiction
      exfalso
      have hxy : a.c0 ^ 3 - 5 * a.c1 ^ 3 = 0 := by
        have hid : a.c0 ^ 3 - 5 * a.c1 ^ 3
            = a.c0 * (a.c0 ^ 2 - 5 * (a.c1 * a.c2))
              - 5 * a.c1 * (a.c1 ^ 2 - a.c0 * a.c2) := by ring
        rw [hid, e0, e2]; ring
      have hcube : (a.c0 * a.c1⁻¹) ^ 3 = 5 := by
        field_simp
        linear_combination hxy
      exact no_cube_root _ hcube

/-! ## Soundness via the `AdjoinRoot (X^3 - 5)` bridge

`K3` is isomorphic to `AdjoinRoot (X^3 - C 5)`, which is a field because `X^3 - C 5` is
irreducible.  Transporting `IsDomain` back to `K3` lets us conclude `norm3 a ≠ 0` for
`a ≠ 0`.  These are all `Prop`-level facts and do not touch the computable operations. -/

open Polynomial

/-- The modulus polynomial `X^3 - 5 ∈ (ZMod 97)[X]`. -/
noncomputable abbrev modPoly : (ZMod 97)[X] := X ^ 3 - C 5

theorem modPoly_natDegree : modPoly.natDegree = 3 := by
  simp [modPoly]

/-- `X^3 - 5` is irreducible over `ZMod 97` (degree 3, no root, `5` a non-cube). -/
theorem modPoly_irreducible : Irreducible modPoly := by
  apply irreducible_of_degree_le_three_of_not_isRoot (p := modPoly)
  · rw [modPoly_natDegree]; decide
  · intro x hroot
    rw [IsRoot.def, modPoly, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hroot
    exact no_cube_root x hroot

noncomputable instance : Fact (Irreducible modPoly) := ⟨modPoly_irreducible⟩

/-- The residue field `L = (ZMod 97)[X]/(X^3 - 5)`. -/
abbrev L : Type := AdjoinRoot modPoly

/-- The distinguished root `X ↦ ⟨0, 1, 0⟩` in `K3`. -/
def Xelt : K3 := ⟨0, 1, 0⟩

@[simp] theorem Xelt_c0 : Xelt.c0 = 0 := rfl
@[simp] theorem Xelt_c1 : Xelt.c1 = 1 := rfl
@[simp] theorem Xelt_c2 : Xelt.c2 = 0 := rfl

/-- `Xelt` satisfies the modulus: `Xelt^3 = 5`. -/
theorem Xelt_cube : Xelt ^ 3 = coeHom 5 := by decide

theorem Xelt_sq : Xelt ^ 2 = ⟨0, 0, 1⟩ := by decide

/-- `Xelt` is a root of the modulus, so `AdjoinRoot.lift` gives a ring hom `L →+* K3`. -/
theorem Xelt_isRoot : modPoly.eval₂ coeHom Xelt = 0 := by
  have : modPoly.eval₂ coeHom Xelt = Xelt ^ 3 - coeHom 5 := by
    simp [modPoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  rw [this, Xelt_cube, sub_self]

/-- The evaluation ring hom `L = (ZMod 97)[X]/(X^3-5) →+* K3` sending the root to `Xelt`. -/
noncomputable def fromL : L →+* K3 :=
  AdjoinRoot.lift coeHom Xelt Xelt_isRoot

theorem fromL_root : fromL (AdjoinRoot.root modPoly) = Xelt :=
  AdjoinRoot.lift_root _

theorem fromL_surjective : Function.Surjective fromL := by
  intro a
  refine ⟨AdjoinRoot.mk modPoly (C a.c0 + C a.c1 * X + C a.c2 * X ^ 2), ?_⟩
  show AdjoinRoot.lift coeHom Xelt Xelt_isRoot _ = a
  rw [AdjoinRoot.lift_mk]
  simp only [eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow]
  rw [Xelt_sq]
  ext <;> simp

instance : Nontrivial K3 := ⟨0, 1, by decide⟩

theorem fromL_injective : Function.Injective fromL :=
  RingHom.injective fromL

theorem fromL_bijective : Function.Bijective fromL :=
  ⟨fromL_injective, fromL_surjective⟩

/-- The ring isomorphism `L ≃+* K3`. -/
noncomputable def equivL : L ≃+* K3 :=
  RingEquiv.ofBijective fromL fromL_bijective

/-- **`K3` is an integral domain** (transported from the field `L`). -/
instance : IsDomain K3 :=
  Function.Injective.isDomain equivL.symm.toRingHom equivL.symm.injective

/-- **The norm is nonzero on nonzero elements.**  Combined with `mul_cof`, this is exactly
what makes `inv` a genuine two-sided inverse. -/
theorem norm3_ne_zero {a : K3} (ha : a ≠ 0) : norm3 a ≠ 0 := by
  intro hn
  have hz : a * cof a = 0 := by rw [mul_cof, hn]; exact map_zero coeHom
  have hcof : cof a = 0 := (mul_eq_zero.mp hz).resolve_left ha
  exact ha (eq_zero_of_cof_eq_zero hcof)

/-! ## The computable inverse and the `Field` instance -/

/-- The closed-form inverse `a⁻¹ = (norm3 a)⁻¹ • cof a`, computable via the coordinate
formulas for `norm3` and `cof`. -/
instance : Inv K3 := ⟨fun a => (norm3 a)⁻¹ • cof a⟩

theorem inv_def (a : K3) : a⁻¹ = (norm3 a)⁻¹ • cof a := rfl

/-- **`K3` is a field** with the computable closed-form inverse. -/
instance field : Field K3 where
  __ := commRing
  inv := Inv.inv
  mul_inv_cancel a ha := by
    show a * ((norm3 a)⁻¹ • cof a) = 1
    rw [mul_smul_comm, mul_cof]
    ext <;> simp [inv_mul_cancel₀ (norm3_ne_zero ha)]
  inv_zero := by
    show (norm3 (0 : K3))⁻¹ • cof (0 : K3) = 0
    simp [norm3]
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-! ## `Fintype` (computable, cardinality `97^3`) and characteristic -/

/-- The coordinate equivalence `K3 ≃ (ZMod 97)^3`. -/
def equivProd : K3 ≃ (ZMod 97 × ZMod 97 × ZMod 97) where
  toFun a := (a.c0, a.c1, a.c2)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv a := by cases a; rfl
  right_inv p := rfl

instance : Fintype K3 := Fintype.ofEquiv _ equivProd.symm

theorem card_eq : Fintype.card K3 = 97 ^ 3 := by
  rw [Fintype.card_congr equivProd]
  simp [ZMod.card]

instance : CharP K3 97 :=
  charP_of_injective_algebraMap (RingHom.injective (algebraMap (ZMod 97) K3)) 97

/-! ## The power basis `1, X, X^2` and `finrank = 3` (the degree-3 capstone datum) -/

/-- The coordinate `ZMod 97`-linear equivalence `K3 ≃ₗ (Fin 3 → ZMod 97)`. -/
def toFin3 : K3 ≃ₗ[ZMod 97] (Fin 3 → ZMod 97) where
  toFun a := ![a.c0, a.c1, a.c2]
  invFun f := ⟨f 0, f 1, f 2⟩
  map_add' a b := by funext i; fin_cases i <;> simp
  map_smul' r a := by funext i; fin_cases i <;> simp
  left_inv a := by ext <;> simp
  right_inv f := by
    funext i; fin_cases i <;> simp

/-- The standard power basis `1, X, X^2` of `K3` over `ZMod 97`. -/
noncomputable def basis : Module.Basis (Fin 3) (ZMod 97) K3 :=
  Module.Basis.ofEquivFun toFin3

/-- **`K3` has dimension `3` over `ZMod 97`** — the degree-3 datum the Theorem-5.4
capstone requires. -/
theorem finrank_eq : Module.finrank (ZMod 97) K3 = 3 := by
  rw [Module.finrank_eq_card_basis basis]
  simp

/-- `2` in `K3` has order `48` (same as in `𝔽₉₇`). Discharges `computeWalkOrder`
on the 3- and 4-row K3 opcode fixtures. -/
theorem two_order : orderOf (2 : K3) = 48 := by
  have hbase : orderOf (2 : ZMod 97) = 48 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hpos
    interval_cases m <;> decide
  have hcast : (2 : K3) = algebraMap (ZMod 97) K3 (2 : ZMod 97) :=
    (map_natCast (algebraMap (ZMod 97) K3) 2).symm
  rw [hcast]
  change orderOf ((algebraMap (ZMod 97) K3).toMonoidHom (2 : ZMod 97)) = 48
  exact (orderOf_injective (algebraMap (ZMod 97) K3).toMonoidHom
    (algebraMap (ZMod 97) K3).injective (2 : ZMod 97)).trans hbase

/-- `3` in `K3` also has order `48`. Discharges `memoryWalkOrder` on the K3 opcode fixtures. -/
theorem three_order : orderOf (3 : K3) = 48 := by
  have hbase : orderOf (3 : ZMod 97) = 48 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hpos
    interval_cases m <;> decide
  have hcast : (3 : K3) = algebraMap (ZMod 97) K3 (3 : ZMod 97) :=
    (map_natCast (algebraMap (ZMod 97) K3) 3).symm
  rw [hcast]
  change orderOf ((algebraMap (ZMod 97) K3).toMonoidHom (3 : ZMod 97)) = 48
  exact (orderOf_injective (algebraMap (ZMod 97) K3).toMonoidHom
    (algebraMap (ZMod 97) K3).injective (3 : ZMod 97)).trans hbase

/-! ## Bridge to `GaloisField 97 3`

`K3` is a finite field of cardinality `97^3`, hence `ZMod 97`-algebra isomorphic to the
production field `GaloisField 97 3`.  This is the equivalence a later re-basing of the OP1
slice would use to slot `K3` wherever the Thm54 stack expects `GaloisField 97 3`. -/


noncomputable def algEquivGaloisField97 : K3 ≃ₐ[ZMod 97] GaloisField 97 3 :=
  GaloisField.algEquivGaloisFieldOfFintype (p := 97) (n := 3) card_eq

/-- `K3` is `ZMod 97`-algebra isomorphic to `AdjoinRoot (X^3 - 5)` (its defining quotient),
recovered from the ring isomorphism `equivL`. -/
noncomputable def ringEquivAdjoinRoot : K3 ≃+* L := equivL.symm

end K3

end CubicField97
end Nock.NockVMROM.Thm54.TraceGen
