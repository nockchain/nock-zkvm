/-
  Nock/RedTeam/Batch861Thm54ReviewU1Controls.lean

  Notes only; no production edit.

* **Own control on a newly watched name, `csum`** (`csumAcc 63`): a verbatim replica reproduces
    the pin `7712084843524472529`; the perturbation `csumAcc 63 → csumAcc 62` fires.
  * `termAt` / `helperPinAt` / `eqmAt` / `lm` / `csumAcc` / `rangeTerms` sit at their pre-edit
    fingerprints (unmoved by the move).
-/
import Lean
import Nock.RedTeam.Batch807Thm54FormRRepairNegativeControls

set_option autoImplicit false

namespace Nock.RedTeam.Batch861

open Lean
open Nock.Reified
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.CoordinateCompiler

variable {F : Type*} [Field F]

/-- Verbatim `csum`. -/
def csumVerbatim : CoeffExpr F := csumAcc 63
/-- `csum` reading one column fewer (signature-preserving perturbation). -/
def csumShort : CoeffExpr F := csumAcc 62

/-- `Batch785.fpHash`. -/
def fp (env : Environment) (n : Name) : String := toString (Nock.RedTeam.Batch785.fpHash env n)

run_cmd do
  let env ← getEnv
  let ns := `Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
  let me := `Nock.RedTeam.Batch861
  let f := fp env
  let checks : List (Name × String) := [
    (`Nock.RedTeam.Batch785.topPinVerbatim, "7881170531472581138"),
    (`Nock.RedTeam.Batch782.topPinU1, "17115654872064556545"),
    (ns ++ `topPin, "17115654872064556545"),
    (`Nock.RedTeam.Batch807.linColVerbatim, "12589611116429724274"),
    (`Nock.RedTeam.Batch807.linColShifted, "8256893704266745194"),
    (ns ++ `linCol, "8256893704266745194"),
    (`Nock.RedTeam.Batch807.booleanGatesVerbatim, "2113340128644410922"),
    (ns ++ `booleanGates, "10580594555426943047"),
    (`Nock.RedTeam.Batch807.comparisonTermsVerbatim, "4675658304727589741"),
    (ns ++ `comparisonTerms, "16756167310402344960"),
    (me ++ `csumVerbatim, "7712084843524472529"),
    (ns ++ `csum, "7712084843524472529"),
    (ns ++ `termAt, "14572518457576761585"),
    (ns ++ `helperPinAt, "3174691776141297282"),
    (ns ++ `csumAcc, "5228615660700191296"),
    (ns ++ `lm, "15194979467431741702"),
    (ns ++ `eqmAt, "4665015395111970282"),
    (ns ++ `rangeTerms, "6368766084615831552")]
  for (n, want) in checks do
    let got := f n
    logInfo m!"{n}: {got}"
    unless got == want do throwError m!"{n}: expected {want}, got {got}"
  let swap := f `Nock.RedTeam.Batch807.booleanGatesSwapOne
  logInfo m!"booleanGatesSwapOne: {swap}"
  if swap == "2113340128644410922" then throwError "booleanGates swap-one does not fire"
  let short := f (me ++ `csumShort)
  logInfo m!"csumShort (own control): {short}"
  if short == "7712084843524472529" then throwError "csum perturbation does not fire"

end Nock.RedTeam.Batch861
