/-
  Nock/NockVMROM/Thm54/P8Core/Batch438Thm54InGateWalkReceipts.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch438Thm54InGateWalkReceipts`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch438Thm54InGateWalkReceipts.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.ComputeEnvAgreement
import Nock.NockVMROM.Thm54.ComputeWalkLabel
import Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
import Nock.NockVMROM.Thm54.OptimizedComputeGateBasis

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch438

open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open OptimizedComputeSubstitution
open OptimizedComputeGateBasis
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- `walkAccStep` through the deployed subst, with its four operands named. -/
theorem walkAccStep_inGate_eval (env : Env K) :
    (Trans.walkAccStep.subst finalWalkSubstInGate).eval env =
      (finalWalkLine .traceNext).eval env * (labelRLC nextReader).eval env +
          (overlayCoord .traceNext 1).eval env -
        (overlayCoord .traceCur 1).eval env -
        (overlayCoord .traceCur 0).eval env * (childSumCC nextReader).eval env := by
  rw [Expr.eval_subst]
  rfl

/-- The decoded source environment's fingerprint column `11 + 3·role + c` is `semanticPub`. -/
theorem decoded_source_trace (E : Env K) (role : Fin 12) (c : Fin 3) :
    (Env.ofSubst computeSubst E).trace (11 + 3 * (role : ℕ) + (c : ℕ)) =
      (semanticPub .traceCur role c).eval E := by
  fin_cases role <;> fin_cases c <;>
    simp [Env.ofSubst, computeSubst, computeTraceSubst]

theorem pubFingerprint_pubOfState (E : Env K) (st : State) (role : Fin 12) :
    OptimizedComputeCodec.pubFingerprint (pubOfState E st) role = fpOf E (11 + 3 * (role : ℕ)) := by
  fin_cases role <;> rfl

theorem fpCoordinate_fpOf (E : Env K) (b : ℕ) (c : Fin 3) :
    OptimizedComputeCodec.fpCoordinate (fpOf E b) c = E.trace (b + (c : ℕ)) := by
  fin_cases c <;> simp [fpOf, OptimizedComputeCodec.fpCoordinate]

end Nock.RedTeam.Batch438
