/-
  Nock/RedTeam/Batch1795Thm54VclLPathModel.lean

  Production: `Thm54/VclL/Chips/PathModel.lean`.

  Step (2): `chain_invariant`, `chain_start`, `chain_record`, `pathLocal_of_chip`,
  `pathStep_of_chip`, `path_records_of_chip` (every record row closes a chain: `k + 1 ≤ 62`,
  `acc` = the natural axis fold, root / rootIdx from the start row, `chainEnd` to the child).

  The atom-child keys are not in `reqs ++ internal ++ responses`, so the
  frame's `IOFailureEventW` (pole hits over those records only) does not price the hit.
  `consumer_gate_free_inv` is the compiled receipt: at `wL = 0` and `den(vKeyL) = 0` the gate holds
  whatever the inverse column holds.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.PathModel
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1795

open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Chips.PathModel

#print axioms chain_invariant
#print axioms chain_start
#print axioms chain_record
#print axioms pathLocal_of_chip
#print axioms pathStep_of_chip
#print axioms path_records_of_chip

/-- The cell table's left consumer inverse gate is one of its `𝕂′` equations. -/
theorem consL_gate_mem {F : Type} [Field F] (δF : F) :
    QE.sub (QE.mul δF (QE.var Cell.consLInv) (den δF Cell.vKeyL)) (QE.base (cv Cell.wL)) ∈
      Cell.qEqs δF := by
  simp [Cell.qEqs]

theorem consumer_gate_free_inv {F K : Type} [Field F] [Field K] [Algebra F K] (δF : F)
    (eK : Env K) (eF : Env F) (hw : eF.trace Cell.wL = 0)
    (hden : (den δF Cell.vKeyL : QE F).ev δF eK eF = 0) :
    (QE.sub (QE.mul δF (QE.var Cell.consLInv) (den δF Cell.vKeyL)) (QE.base (cv Cell.wL)) :
      QE F).ev δF eK eF = 0 := by
  rw [ev_sub, ev_mul, hden, ev_base]
  simp [CoeffExpr.eval, hw, liftQ]

#print axioms consL_gate_mem
#print axioms consumer_gate_free_inv

end Nock.RedTeam.Batch1795
