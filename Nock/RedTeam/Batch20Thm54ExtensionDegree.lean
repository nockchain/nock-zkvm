/-
  Nock/RedTeam/Batch20Thm54ExtensionDegree.lean

  Locked facts:

  1. **Extension degree `e` is a real field parameter.**  `card = p^e`, `finrank = e`, `char = p`.
     At `e = 3` this is the production cubic denominator; at `e = 1` the base prime field.
  2. **`e` (a field dimension) is not `ExactConfig.eDeg` (a coordinate width).**  At `e = 3`,
     `finrank = 3 ≠ 1`.
  3. **The strict orbit has order `e·2^h`, not `2^h`.**  For `e = 3` the generator's order is
     `3·2^h`, which strictly exceeds `2^h`.
  4. **Coordinate-expansion pilot (linear fragment).**  One `K`-equality is equivalent to `e`
     base-field coordinate equalities, a `K`-value equals the basis combination of its coordinates,
     coordinates are additive, and laying coordinate columns at disjoint offsets preserves degree.
-/

import Nock.NockVMROM.Thm54.ExtensionField
import Nock.NockVMROM.Thm54.CoordinateBasis

namespace Nock.RedTeam.Batch20

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.CoordinateBasis
open Module

/-! ## 1-2. Extension degree is a field parameter, distinct from eDeg -/

/-- **Extension field cardinality is `p^e`.** -/
theorem b20_ext_card_is_prime_pow (e : ℕ) (q : ℕ → ℕ) [∀ n, Fact (Nat.Prime (q n))]
    (he : e ≠ 0) (n : ℕ) :
    Fintype.card (ExtensionFieldAt e q n) = (q n) ^ e :=
  extensionFieldAt_card e q he n

/-- **Extension `𝔽_p`-dimension is exactly `e`.** -/
theorem b20_ext_finrank_is_e (e : ℕ) (q : ℕ → ℕ) [∀ n, Fact (Nat.Prime (q n))]
    (he : e ≠ 0) (n : ℕ) :
    Module.finrank (ZMod (q n)) (ExtensionFieldAt e q n) = e :=
  extensionFieldAt_finrank e q he n

/-- **At `e = 3` the field dimension is `3`, distinct from the coordinate-width `eDeg = 1`.** -/
theorem b20_finrank_three_ne_eDeg_one (q : ℕ → ℕ) [∀ n, Fact (Nat.Prime (q n))] (n : ℕ) :
    Module.finrank (ZMod (q n)) (ExtensionFieldAt 3 q n) ≠ 1 := by
  rw [b20_ext_finrank_is_e 3 q (by norm_num) n]
  decide

theorem b20_ext_card_e_one (q : ℕ → ℕ) [∀ n, Fact (Nat.Prime (q n))] (n : ℕ) :
    Fintype.card (ExtensionFieldAt 1 q n) = q n := by
  rw [b20_ext_card_is_prime_pow 1 q (by norm_num) n, pow_one]

/-! ## 3. The strict orbit has order `e·2^h`, not `2^h` -/

/-- **The strict generator has exact order `e·2^h`.** -/
theorem b20_strict_orbit_order (e : ℕ) [NeZero e] (Ksz h : ℕ → ℕ) (kroots n : ℕ) (hh : 1 ≤ h n) :
    orderOf (strictOrbitDomain e Ksz h kroots n hh).ω = e * 2 ^ (h n) :=
  (strictOrbitDomain e Ksz h kroots n hh).order_ω

/-- **The strict order strictly exceeds `2^h` for `e = 3`.** -/
theorem b20_strict_order_ne_two_pow (Ksz h : ℕ → ℕ) (kroots n : ℕ) (hh : 1 ≤ h n) :
    orderOf (strictOrbitDomain 3 Ksz h kroots n hh).ω ≠ 2 ^ (h n) := by
  rw [b20_strict_orbit_order]
  have : 0 < 2 ^ (h n) := pow_pos (by norm_num) _
  omega

/-! ## 4. Coordinate-expansion pilot (linear fragment) -/

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **One `K`-equality ⟺ `e` base-field coordinate equalities.** -/
theorem b20_one_K_eq_iff_e_coord_eqs {e : ℕ} (b : Basis (Fin e) F K) (x y : K) :
    x = y ↔ ∀ i, coord b x i = coord b y i :=
  eq_iff_coords_eq b x y

/-- **A `K`-value is the basis combination of its coordinates.** -/
theorem b20_reconstruct_coord {e : ℕ} (b : Basis (Fin e) F K) (x : K) :
    reconstruct b (coord b x) = x :=
  reconstruct_coord b x

/-- **Coordinates are additive** (linear constraints expand to linear coordinate constraints). -/
theorem b20_coord_add {e : ℕ} (b : Basis (Fin e) F K) (x y : K) (i : Fin e) :
    coord b (x + y) i = coord b x i + coord b y i :=
  coord_add b x y i

/-- **Laying coordinate columns at a disjoint offset preserves AIR degree.** -/
theorem b20_coordColumn_degree_preserved (off : ℕ) (e : Nock.Reified.Expr) :
    (e.shiftTrace off).degree = e.degree :=
  coordColumn_degree_preserved off e

end Nock.RedTeam.Batch20

#print axioms Nock.RedTeam.Batch20.b20_ext_card_is_prime_pow
#print axioms Nock.RedTeam.Batch20.b20_finrank_three_ne_eDeg_one
#print axioms Nock.RedTeam.Batch20.b20_strict_order_ne_two_pow
#print axioms Nock.RedTeam.Batch20.b20_one_K_eq_iff_e_coord_eqs
#print axioms Nock.RedTeam.Batch20.b20_coordColumn_degree_preserved
