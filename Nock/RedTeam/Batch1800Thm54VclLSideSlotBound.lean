/-
  Nock/RedTeam/Batch1800Thm54VclLSideSlotBound.lean

  **The bound and `ε` at the side slot.**

  The export accumulator's providers are `2D` at the side slot (two records per cell row,
  `ChipRAP.cellXRecords`), so the export total is `3N + P + 2D` (`totVCLS`), not `3N + P + D`.
  Figures (kernel `decide`): `< 2^-155` at `2^31`, `< 2^-154` at `2^32`, `< 2^-164` at the kernel,
  `< 2^-155` bench-worst, `¬ ≤ 2^-156` at `2^31` — unchanged from `boundVCL'`.
-/
import Nock.RedTeam.Batch1744Thm54VclLIOFieldQuad

namespace Nock.RedTeam.Batch1800

open Nock.NockVMROM.Thm54.VclL.Events
open Nock.NockVMROM.Thm54.FiniteIO

/-- The side slot costs IO work (wider record, more providers) but no figure bit. -/
theorem ioWork_side_ge (N D P : ℕ) : ioWorkKp 5 10 8 3 N D P ≤ ioWorkKpS 5 11 8 3 N D P := by
  unfold ioWorkKp ioWorkKpS
  have h1 := ioFailureUnionBound_mono_tot 10 1
    (t := 3 * N + P + D) (t' := 3 * N + P + 2 * D) (by omega)
  have h2 : ioFailureUnionBound 10 0 (3 * N + P + 2 * D) 1 ≤ ioFailureUnionBound 11 0 (3 * N + P + 2 * D) 1 := by
    unfold ioFailureUnionBound; gcongr; omega
  omega

#print axioms boundVCL''
#print axioms figVCL''_two_pow_31
#print axioms figVCL''_two_pow_32
#print axioms figVCL''_kernel
#print axioms figVCL''_bench
#print axioms figVCL''_not_156
#print axioms epsilon_vcll_eq
#print axioms epsilon_vcll_eq_w10
#print axioms Nock.RedTeam.Batch1744.epsilon_vcll_eq_quad
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.Cell.widthT_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.record_widths_tower
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.mVCL_eq_tower
#print axioms ioWork_side_ge

end Nock.RedTeam.Batch1800
