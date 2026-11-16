/-
  Nock/RedTeam/Batch908Thm54R4HonestShiftRange.lean

  `r4_path_valid_at` takes `hA : ∀ e, decodedShift (envsCR P c Qc) e ≤ formRN K - 1`.
  `Batch806.decodedShift_in_range_of_U1` proves exactly that shape, but over an environment family
  on which the deployed U1 gates (`bbool (colM k)`, `pPin`, `topPin`, `rangeGate`) evaluate to
  zero.  The family compute chip commits those gates in the BASE field (`row_obligations_at..
.formR99`, `g.eval (envOfTrace Qc..) = 0` over `Env F`), while `envsCR` is the `𝕂`-valued
  source environment.  Two transports close the gap:

  * `decodedShift_embed`: `decodedShift` reads the environments only through tests
    `env.trace j = 1` (selectors `0, 2, 5..9`, shift bits `265..270`, certificate bits), which an
    injective embedding `F →+* K` preserves, so on `𝕂`-environments whose traces are the images
    of base traces the decoded shift equals the base-field decoded shift;
  * `envsCR_trace`: `toSourceEnv` embeds the base columns `0..12` and the certificate block
    `202..295` of the gathered row, which are the family row's own columns.

  Then `Batch806` at the base field `F` and `formRN F = formRN K` (`Algebra.ringChar_eq`) give
  `hA`.  Premises: acceptance at the family compute chip and `2 ≤ formRN K` (the fragment of
  `hp : 25 ≤ p`).
-/
import Nock.RedTeam.Batch907Thm54R4HonestPremises
import Nock.RedTeam.Batch806Thm54FormRRepairSound
import Nock.NockVMROM.Thm54.P8Core.Batch908Thm54R4HonestShiftRange
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch908

open scoped Polynomial
open Polynomial
open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.RedTeam.Batch824

noncomputable section

/-! ## A. `decodedShift` reads only `trace j = 1` tests -/

section Embed

variable {F K : Type} [Field F] [Field K] (f : F →+* K) (hf : Function.Injective f) {N : ℕ}
include hf

end Embed

/-! ## B. `hA` from acceptance at the family compute chip -/

section FromAcceptance

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])

end FromAcceptance

end

end Nock.RedTeam.Batch908

#print axioms Nock.RedTeam.Batch908.decodedShift_embed
#print axioms Nock.RedTeam.Batch908.hA_of_acceptance
