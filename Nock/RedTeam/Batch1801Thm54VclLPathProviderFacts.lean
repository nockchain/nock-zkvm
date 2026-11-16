/-
  Nock/RedTeam/Batch1801Thm54VclLPathProviderFacts.lean

  **The path accumulator's own provider IO facts.**
  Production: `VclL/Chips/ExportTelescope.lean` §4.

  * `path_provider_telescope`: `Σ_j m_j·inv_j = ρ_P` (path public slots `2 / 3`).
  * `path_pinv`: `last ∈ {0,1}`; `last = 0 ⇒ m = 0` (gate `(1 − last)·m`); `last = 1 ⇒ inv = den(pRec)⁻¹ ≠ 0`.
  * `pathProviderFacts`: the frame's `IOFacts` at `m = 8`, providers = the record (`last`) rows only
    (`≤ P` rows), no internal consumer.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.ExportTelescope
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1801

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.Reified in
/-- **NC**: a mid-chain row (`last = 0`) carrying a provider weight `m ≠ 0` fails a path base gate. -/
theorem midchain_record_rejected {F : Type} [Field F] (env : Env F) (hl : env.trace Path.last = 0)
    (hm : env.trace Path.m ≠ 0) :
    (CoeffExpr.mul (notE (cv Path.last)) (cv Path.m) : CoeffExpr F) ∈ Path.baseGates ∧
      (CoeffExpr.mul (notE (cv Path.last)) (cv Path.m) : CoeffExpr F).eval env ≠ 0 := by
  refine ⟨by simp [Path.baseGates], ?_⟩
  simpa [CoeffExpr.eval, cv, notE, hl] using hm

open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.Reified in
/-- The masked provider-inverse gate alone says nothing on a mid-chain row (any inverse, any key). -/
theorem masked_inv_gate_silent {F : Type} [Field F] (env : Env F) (hl : env.trace Path.last = 0) :
    (cv Path.last : CoeffExpr F).eval env = 0 := by
  simpa [CoeffExpr.eval, cv] using hl

#print axioms path_provider_telescope
#print axioms path_pinv
#print axioms pathProviderFacts
#print axioms midchain_record_rejected
#print axioms masked_inv_gate_silent

end Nock.RedTeam.Batch1801
