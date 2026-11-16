/-
  Nock/NockVMROM/Thm54/VclL/Handle/RepriceJ9A.lean

  `numJ9AX` is `numJ8X` with that one term replaced (`numJ9AX_zero`: at `AX = SP = 0` it IS `numJ8X`). `numJ9AX_census32` / `numJ9AX_not_156` (kernel `decide`): `< 2^-155` and not `≤ 2^-156` at `cornerC9`,
  `P = 2^66`, `g' = 2^32`. -/
import Nock.NockVMROM.Thm54.VclL.Handle.RepriceJ8
import Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.RepriceJ9A

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 Nock.NockVMROM.Thm54.VclL.Handle.WeightsPinJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8 (cornerC)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A

noncomputable section

/-- **The J-9 A numerator over `|𝕂|⁴`** (`|𝕂′| = |𝕂|²`): `numJ8X` with summand #6 re-priced at the axis / split rows. -/
def numJ9AX (c : ℕ) (r : RowsJ9A) (P g : ℕ) : ℕ :=
  numHQ c r.N r.D r.W r.Λ +
  (ioFailureUnionBound 5 (3 + 2 * r.D + g) (r.D + r.mb) (c ^ 2) +
    ioFailureUnionBound 5 (3 + 2 * r.A) r.A (c ^ 2) +
    ioFailureUnionBound 5 (r.A + r.inc + r.AW) r.A (c ^ 2) +
    ioFailureUnionBound 5 (3 * r.N + r.W + r.rd) r.D (c ^ 2) +
    ioFailureUnionBound 8 (r.N + 2 * r.J + g + r.AX)
      (r.calls + r.heads + r.blocks + r.J + r.AX + 2 * r.SP) (c ^ 2)) +
  c ^ 2 * (r.A * (2 * fuelChip - 1) + pairCount (r.A + 3) * (2 * r.Λ - 1) + 1) +
  c ^ 3 * (15 * r.AW) +
  P * (c ^ 2 * (r.leaves - 1) + c ^ 2 * (r.maxlen - 1)) +
  ioFailureUnionBound 11 r.AW (2 * r.A) (c ^ 2)

/-- Without axis and split rows the J-9 A numerator is the J-8 one. -/
theorem numJ9AX_zero (c : ℕ) (r : RowsJ8) (P g : ℕ) :
    numJ9AX c { toRowsJ8 := r, AX := 0, SP := 0 } P g = numJ8X c r P g := by
  simp [numJ9AX, numJ8X, numJ8Pin]

theorem numJ9AX_census32 (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    numJ9AX c cornerC9 (2 ^ 66) (2 ^ 32) * 2 ^ 155 < c ^ 4 := by
  subst hc
  unfold numJ9AX cornerC9 numHQ cornerC corner31 fuelChip pairCount ioFailureUnionBound
  decide +kernel

theorem numJ9AX_not_156 (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    c ^ 4 < numJ9AX c cornerC9 (2 ^ 66) (2 ^ 32) * 2 ^ 156 := by
  subst hc
  unfold numJ9AX cornerC9 numHQ cornerC corner31 fuelChip pairCount ioFailureUnionBound
  decide +kernel

end

end Nock.NockVMROM.Thm54.VclL.Handle.RepriceJ9A

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.RepriceJ9A
#print axioms numJ9AX_zero
#print axioms numJ9AX_census32
#print axioms numJ9AX_not_156
end Axioms
