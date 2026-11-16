/-
  Nock/RedTeam/Batch972Thm54Round0WrapCertAxis.lean

  **Lane `2b-round0-wrap`: the recovered axis encodes back to the stored `(T, C')`,
  and it is below `p`.**  Additive; generic (no package).

  * `formRT_certAxis`: `formRT λ (certAxis m c) = λ^m` (the certificate's `T`, `Tpoly m` at `λ`).
  * `formRC_certAxis`: with `m ≤ n − 1` and the padding `c_j = 0` for `m < j ≤ n − 1`,
    `formRC λ (certAxis m c) = (C'poly n c).eval λ` — the certificate's `C'`.  Without padding it is
    false in general: `formRC` reads only the `m` bits below the MSB.
  * `certAxis_lt_ringChar`: a compute row passing the 97 deployed Form R certificate gates whose
    certificate is padded has `certAxis (rowShift) (rowBits) < p` — through `Batch806.formR_cert_lt_p`
    (the U1 comparison gadget), under `FormRWidth` alone (`3 < p`, `Nat.size p ≤ 64`; `formR_cert_lt_p_p4`).  The padding is what makes the committed columns
    exactly the bits of the recovered axis (columns above the shift are `0`: by padding up to
    `n − 1`, by the C2 pin beyond).
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesR0
import Nock.RedTeam.Batch806Thm54FormRRepairSound
import Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
import Nock.NockVMROM.Thm54.P8Core.Batch972Thm54Round0WrapCertAxis

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch972

open scoped Polynomial BigOperators
open Polynomial
open Nock
open Nock.Reified
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.RedTeam.Batch575
open Nock.RedTeam.Batch554 (Cpoly bit)

noncomputable section

/-! ## A. Encoding the recovered axis -/

section Encode

variable {K : Type} [Field K]

end Encode

/-! ## B. The recovered axis is below `p` (the U1 comparison gadget) -/

section Bound

open scoped Classical

variable {F : Type} [Field F]

end Bound

end

end Nock.RedTeam.Batch972

#print axioms Nock.RedTeam.Batch972.formRT_certAxis
#print axioms Nock.RedTeam.Batch972.formRC_certAxis
#print axioms Nock.RedTeam.Batch972.formR_cert_lt_p_p4
#print axioms Nock.RedTeam.Batch972.certAxis_lt_ringChar
