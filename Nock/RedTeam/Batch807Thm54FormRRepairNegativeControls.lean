/-
  Nock/RedTeam/Batch807Thm54FormRRepairNegativeControls.lean

  **U1+C1+C2 negative controls by replica fingerprint (standing rule 6), lane
  `u1-formr-repair`.**

  * `topPin`: verbatim `7881170531472581138` → U1 `17115654872064556545`;
  * `booleanGates`: verbatim `2113340128644410922` → one `bbool` swapped for the pin
    (column `62`) fires; the production (C2) value is `10580594555426943047`;
  * `comparisonTerms`: verbatim `4675658304727589741` → production `16756167310402344960`.

  The production constants are unchanged by this file (replicas only).
-/
import Lean
import Nock.RedTeam.Batch785Thm54U1Fingerprints

set_option autoImplicit false

namespace Nock.RedTeam.Batch807

open Lean
open Nock.Reified
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.CoordinateCompiler

variable {F : Type*} [Field F]

/-- Pre-repair `linCol`, verbatim (`p_{n−1−j}`). -/
noncomputable def linColVerbatim (j : ℕ) : CoeffExpr F :=
  if pBit F (formRN F - 1 - j) then colC j else .sub (.const 1) (colC j)

/-- `linCol` with the index `− 1 → − 2` (the C1 perturbation). -/
noncomputable def linColShifted (j : ℕ) : CoeffExpr F :=
  if pBit F (formRN F - 2 - j) then colC j else .sub (.const 1) (colC j)

/-- Pre-repair `booleanGates`, verbatim. -/
def booleanGatesVerbatim : List (CoeffExpr F) :=
  (List.range 63).map (fun j => bbool (colC j)) ++
    (List.range 6).map (fun k => bbool (colM k))

/-- One `bbool` (column `62`) swapped for the pin `c = 0` (the C2 perturbation). -/
def booleanGatesSwapOne : List (CoeffExpr F) :=
  (List.range 63).map (fun j => if j = 62 then colC j else bbool (colC j)) ++
    (List.range 6).map (fun k => bbool (colM k))

/-- Pre-repair `comparisonTerms`, verbatim. -/
noncomputable def comparisonTermsVerbatim : List (CoeffExpr F) :=
  (List.range 63).map fun k => .mul (bitCoeff (pBit F (formRN F - 1 - k))) (termAt k)

run_cmd do
  let env ← getEnv
  let ns := `Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
  let me := `Nock.RedTeam.Batch807
  let h := Nock.RedTeam.Batch785.fpHash env
  let linV := h (me ++ `linColVerbatim)
  let linS := h (me ++ `linColShifted)
  let linP := h (ns ++ `linCol)
  let boolV := h (me ++ `booleanGatesVerbatim)
  let boolS := h (me ++ `booleanGatesSwapOne)
  let boolP := h (ns ++ `booleanGates)
  let cmpV := h (me ++ `comparisonTermsVerbatim)
  let cmpP := h (ns ++ `comparisonTerms)
  logInfo m!"linCol: verbatim {linV}, shifted {linS}, production {linP}"
  logInfo m!"booleanGates: verbatim {boolV}, swap-one {boolS}, production {boolP}"
  logInfo m!"comparisonTerms: verbatim {cmpV}, production {cmpP}"
  unless linV == 12589611116429724274 do throwError "linCol verbatim replica off its pre-edit pin"
  unless boolV == 2113340128644410922 do
    throwError "booleanGates verbatim replica off its pre-edit pin"
  unless cmpV == 4675658304727589741 do
    throwError "comparisonTerms verbatim replica off its pre-edit pin"
  if linS == linV then throwError "linCol index perturbation does not fire"
  if boolS == boolV then throwError "booleanGates swap-one does not fire"
  unless linS == linP do throwError "the shifted replica is not the production linCol"
  unless linP == 8256893704266745194 do throwError "production linCol off its re-pin"
  unless boolP == 10580594555426943047 do throwError "production booleanGates off its re-pin"
  unless cmpP == 16756167310402344960 do throwError "production comparisonTerms off its re-pin"
  if boolP == boolV then throwError "C2 does not fire"
  if cmpP == cmpV then throwError "C1 comparisonTerms does not fire"

end Nock.RedTeam.Batch807
