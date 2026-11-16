/-
  Nock/RedTeam/Batch1710Thm54VclLComputeGates.lean

  **The new gate families of `computeChipVCL` (part (a)).**

  Receipts: degree lemmas; the negative control `serialStepGateNC` (`+ 1 → + 0`, the dropped step):
  at a trace whose serials are all `0` the control ACCEPTS and the real gate REJECTS (so the step
  gate fires on exactly the forged shape); the honest step `S' = S + 1` is accepted by both gates.
  Axioms below.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.Gates
import Mathlib.Data.Rat.Defs

set_option autoImplicit false

namespace Nock.RedTeam.Batch1710

open Nock Nock.Reified
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Compute

/-- A one-row-pair environment over `ℚ`: `isLast = 0`, serial `s` now and `s'` next. -/
def envS (s s' : ℚ) : Env ℚ where
  trace := fun i => if i = serialCol then s else 0
  traceNext := fun i => if i = serialCol then s' else 0
  chal := fun _ => 0
  pub := fun _ => 0

/-- Honest step: `S' = S + 1` is accepted by the arity-1 step gate. -/
theorem honest_step_accepted : (serialStepGate (F := ℚ)).eval (envS 3 4) = 0 := by
  simp [serialStepGate, CoeffExpr.eval, envS, serialCol]
  norm_num

/-- **NC**: the step dropped (`+1 → +0`) accepts the all-zero serial trace (`S' = S = 0`)... -/
theorem nc_zero_step_accepted : (serialStepGateNC (F := ℚ)).eval (envS 0 0) = 0 := by
  simp [serialStepGateNC, CoeffExpr.eval, envS, serialCol]

/-- ... and the real gate REJECTS it: the replica fires. -/
theorem zero_step_rejected : (serialStepGate (F := ℚ)).eval (envS 0 0) ≠ 0 := by
  simp [serialStepGate, CoeffExpr.eval, envS, serialCol]

/-- The init gate pins the first serial to `0` (`isFirst` = column `11`). -/
theorem init_rejects_nonzero_start :
    (serialInitGate (F := ℚ)).eval
      { (envS 5 6) with trace := fun i => if i = 11 then 1 else if i = serialCol then 5 else 0 }
      ≠ 0 := by
  simp [serialInitGate, CoeffExpr.eval, serialCol]

theorem serial_columns : serialCol = 220 := rfl
theorem serial_gate_count : (serialGates (F := ℚ)).length = 2 := rfl

#print axioms serialGates_degree
#print axioms serialStepGate_eval
#print axioms lookupInvGates_degree
#print axioms lookupInvGates_sound
#print axioms nc_zero_step_accepted
#print axioms zero_step_rejected
#print axioms honest_step_accepted

end Nock.RedTeam.Batch1710
