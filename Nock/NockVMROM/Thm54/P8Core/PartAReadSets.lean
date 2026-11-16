/-
  Nock/NockVMROM/Thm54/P8Core/PartAReadSets.lean

  **The read-set instruments the Part A modules need, split out
  BELOW the statement half.**

  The Part A modules read exactly four constants of that file
  (measured over the elaborated environment: `coeffChals`, `mixedSlots`, `mixedRawChals`,
  `memoryMixed_noRawChallenge`).  They are restated here verbatim, over the same syntax, importing
  only the gate basis; `PartAReadSets.*_eq_deployedStaging` (RedTeam `Batch1440`) proves each copy
  equal to its original.
-/
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.PartAReadSets

open Nock
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Module

/-- Raw challenge slots of a `CoeffExpr` (verbatim `DeployedStaging.coeffChals`). -/
def coeffChals {F : Type*} : CoeffExpr F → List ℕ
  | .const _ => []
  | .var .challenge i => [i]
  | .var _ _ => []
  | .add a b => coeffChals a ++ coeffChals b
  | .sub a b => coeffChals a ++ coeffChals b
  | .mul a b => coeffChals a ++ coeffChals b
  | .neg a => coeffChals a
  | .pow a _ => coeffChals a

/-- `𝕂` challenge slots of a memory mixed source (verbatim `DeployedStaging.mixedSlots`). -/
def mixedSlots {F : Type*} : MixedExpr F → List ℕ
  | .Var .challenge i => [i]
  | .Var _ _ => []
  | .Lift _ => []
  | .Scale _ m => mixedSlots m
  | .Const _ => []
  | .Add a b => mixedSlots a ++ mixedSlots b
  | .Sub a b => mixedSlots a ++ mixedSlots b
  | .Mul a b => mixedSlots a ++ mixedSlots b
  | .Neg a => mixedSlots a
  | .Pow a _ => mixedSlots a

/-- Raw base-field challenge slots inside `Lift` / `Scale` (verbatim
`DeployedStaging.mixedRawChals`). -/
def mixedRawChals {F : Type*} : MixedExpr F → List ℕ
  | .Lift c => coeffChals c
  | .Scale c m => coeffChals c ++ mixedRawChals m
  | .Add a b => mixedRawChals a ++ mixedRawChals b
  | .Sub a b => mixedRawChals a ++ mixedRawChals b
  | .Mul a b => mixedRawChals a ++ mixedRawChals b
  | .Neg a => mixedRawChals a
  | .Pow a _ => mixedRawChals a
  | _ => []

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- No deployed mixed gate hides a raw base-field challenge inside a `Lift` / `Scale`
(verbatim `DeployedStaging.memoryMixed_noRawChallenge`). -/
theorem memoryMixed_noRawChallenge (b : Basis (Fin 3) F K) :
    (OptimizedMemoryGateBasis.mixedTransitionGates b).map mixedRawChals =
      List.replicate 50 [] := rfl

end Nock.NockVMROM.Thm54.PartAReadSets
