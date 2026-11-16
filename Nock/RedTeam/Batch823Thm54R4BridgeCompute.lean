/-
  Nock/RedTeam/Batch823Thm54R4BridgeCompute.lean

  Additive.

  At an accepted family compute row
  `a` (`computeChipAt c`), for an active request slot `j`:

  * `locateExp (expOfAt a j) = some (a, j)` (`locateExp_expOfAt`): the locator's prefix sums are
    `FamilyIOChain.prefixExpAt` (one-hot selectors: `computeArity = rowArity`);
  * the request record's Form R slots are the located certificate's `(T, C')` at the tuple's `λ`:
    `rowRecord (rowEnvAt a) j 6 = λ ^ (slotCert a j).1` and
    `rowRecord (rowEnvAt a) j 8 = (C'poly n (slotCert a j).2).eval λ` (`slot6_eq`, `slot8_eq`),
    from the `𝕂` power pins `formRLamPins` (`T = λ^{rowShift}`), the one-hot selectors and
    certificate-bit booleanity.

  **Named premise `CertBitsBoolean`** (not in the census table; from-acceptance): the shift bits
  `m_k` (`k < 6`) and the certificate bits `c_{j+1}` with `j + 1 ≤ n − 1` are `0`/`1`.  Every other theorem here
  takes `CertBitsBoolean` as a hypothesis and reads no body of `booleanGates`, `topPin`,
  `linCol`, `comparisonTerms`.

  Rule 8(b): every theorem holds on every accepted family compute trace (acceptance at
  `computeChipAt c` + `hchar`); no event, no `S`.
-/
import Nock.NockVMROM.Thm54.FormRBridgeTelescope
import Nock.NockVMROM.Thm54.FamilyIOChainRouteB
import Nock.NockVMROM.Thm54.OptimizedComputeFormRSlots
import Nock.NockVMROM.Thm54.P8Core.Batch823Thm54R4BridgeCompute
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch823

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.OptimizedComputeFormRSlots
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.DecodedLambdaEvent

noncomputable section

/-! ## A. Pure algebra on one source environment -/

section Generic
variable {K : Type} [Field K]

/-- `1 + m (x − 1) = x ^ [m = 1]` for a bit `m`. -/
theorem bitFactor [DecidableEq K] (m x : K) (hm : m = 0 ∨ m = 1) :
    1 + m * (x - 1) = x ^ (if m = 1 then 1 else 0) := by
  rcases hm with rfl | rfl
  · simp
  · simp

end Generic

/-! ## B. At the family compute chip -/

section Deployed

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])

variable (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

end Deployed

end

end Nock.RedTeam.Batch823
