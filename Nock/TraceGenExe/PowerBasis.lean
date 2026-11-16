/-
  Nock/TraceGenExe/PowerBasis.lean

  **The power basis of `KC` and the coordinates of `K3.toK`.**
  `powerBasis3 : Basis (Fin 3) (ZMod p) KC` is `1, x, x²`;
  `coord_powerBasis3_toK`: `coord powerBasis3 (toK a) k` is the `k`-th limb of `a` (the raw output limb).
-/
import Nock.TraceGenExe.K6
import Nock.NockVMROM.Thm54.CoordinateBasis

set_option autoImplicit false

namespace Nock.TraceGenExe

open Nock.Field Nock.NockVMROM.Thm54.CoordinateBasis

/-- The power basis `1, x, x²` of `KC` over `ZMod p`, indexed by `Fin 3`. -/
noncomputable def powerBasis3 : Module.Basis (Fin 3) (ZMod p) KC :=
  (AdjoinRoot.powerBasis cubicPoly_ne_zero).basis.reindex
    (finCongr (by rw [AdjoinRoot.powerBasis_dim, cubicPoly_natDegree]))

theorem powerBasis3_apply (i : Fin 3) : powerBasis3 i = xr ^ (i : ℕ) := by
  unfold powerBasis3
  rw [Module.Basis.reindex_apply]
  simp [AdjoinRoot.powerBasis_gen, xr]

/-- **The coordinates of `toK a` against the power basis are the limbs of `a`.** -/
theorem coord_powerBasis3_toK (a : K3) (k : Fin 3) :
    coord powerBasis3 (K3.toK a) k = ![a.c0.toZ, a.c1.toZ, a.c2.toZ] k := by
  have h : K3.toK a = ∑ i : Fin 3, (![a.c0.toZ, a.c1.toZ, a.c2.toZ] i) • powerBasis3 i := by
    simp only [Fin.sum_univ_three, powerBasis3_apply, K3.toK, Algebra.smul_def]
    simp
  unfold coord
  rw [h, Module.Basis.repr_sum_self]

end Nock.TraceGenExe
