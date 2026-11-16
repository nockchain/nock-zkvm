import Nock.NockVMROM.Thm54.DeployedStaging
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.P8Core.PartAStaged12
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1440Thm54PartARelocation.lean

  **The relocation below the statement half.**

  Measured
  over the elaborated environment, the Part A modules use exactly four constants of that file;
  they are restated verbatim in the new module `P8Core/PartAReadSets.lean` (imports only the gate
  basis), `PartAMemoryChip12` reads them there, and `PartAB0Locality` imports
  `P8Core.DeployedStaging` (below the statement) instead.  No existing production file is edited.

  * §A `coeffChals_eq`, `mixedSlots_eq`, `mixedRawChals_eq`: the copies ARE the originals
    (function equality).
  * §B the import-graph receipt: `#eval` over the environment's module headers — every Part A /
    L2 module's transitive import closure omits `Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage`
    (the run throws otherwise); positive control: `Nock.NockVMROM.Thm54.DeployedStaging`'s closure
    DOES contain it (the instrument finds the statement where it is).
-/

set_option autoImplicit false

namespace Nock.RedTeam.Batch1440

open Nock Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler

/-! ## §A. The split-out read sets are the originals -/

theorem coeffChals_eq {F : Type*} :
    (PartAReadSets.coeffChals : CoeffExpr F → List ℕ) = DeployedStaging.coeffChals := by
  funext e
  induction e with
  | const _ => rfl
  | var k i => cases k <;> rfl
  | add a b iha ihb => simp only [PartAReadSets.coeffChals, DeployedStaging.coeffChals, iha, ihb]
  | sub a b iha ihb => simp only [PartAReadSets.coeffChals, DeployedStaging.coeffChals, iha, ihb]
  | mul a b iha ihb => simp only [PartAReadSets.coeffChals, DeployedStaging.coeffChals, iha, ihb]
  | neg a iha => simp only [PartAReadSets.coeffChals, DeployedStaging.coeffChals, iha]
  | pow a n iha => simp only [PartAReadSets.coeffChals, DeployedStaging.coeffChals, iha]

theorem mixedSlots_eq {F : Type*} :
    (PartAReadSets.mixedSlots : MixedExpr F → List ℕ) = DeployedStaging.mixedSlots := by
  funext e
  induction e with
  | Var k i => cases k <;> rfl
  | Lift _ => rfl
  | Scale c m ih => simp only [PartAReadSets.mixedSlots, DeployedStaging.mixedSlots, ih]
  | Const _ => rfl
  | Add a b iha ihb => simp only [PartAReadSets.mixedSlots, DeployedStaging.mixedSlots, iha, ihb]
  | Sub a b iha ihb => simp only [PartAReadSets.mixedSlots, DeployedStaging.mixedSlots, iha, ihb]
  | Mul a b iha ihb => simp only [PartAReadSets.mixedSlots, DeployedStaging.mixedSlots, iha, ihb]
  | Neg a iha => simp only [PartAReadSets.mixedSlots, DeployedStaging.mixedSlots, iha]
  | Pow a n iha => simp only [PartAReadSets.mixedSlots, DeployedStaging.mixedSlots, iha]

theorem mixedRawChals_eq {F : Type*} :
    (PartAReadSets.mixedRawChals : MixedExpr F → List ℕ) = DeployedStaging.mixedRawChals := by
  funext e
  induction e with
  | Var k i => rfl
  | Lift c => simp only [PartAReadSets.mixedRawChals, DeployedStaging.mixedRawChals,
      congrFun coeffChals_eq c]
  | Scale c m ih => simp only [PartAReadSets.mixedRawChals, DeployedStaging.mixedRawChals, ih,
      congrFun coeffChals_eq c]
  | Const _ => rfl
  | Add a b iha ihb => simp only [PartAReadSets.mixedRawChals, DeployedStaging.mixedRawChals, iha, ihb]
  | Sub a b iha ihb => simp only [PartAReadSets.mixedRawChals, DeployedStaging.mixedRawChals, iha, ihb]
  | Mul a b iha ihb => simp only [PartAReadSets.mixedRawChals, DeployedStaging.mixedRawChals, iha, ihb]
  | Neg a iha => simp only [PartAReadSets.mixedRawChals, DeployedStaging.mixedRawChals, iha]
  | Pow a n iha => simp only [PartAReadSets.mixedRawChals, DeployedStaging.mixedRawChals, iha]

/-! ## §B. The import-graph receipt -/

open Lean in
/-- The transitive import closure of a module, from the environment's module headers. -/
def importClosure (env : Environment) (m : Name) : NameSet := Id.run do
  let names := env.header.moduleNames
  let mut idx : Std.HashMap Name Nat := {}
  for i in [:names.size] do
    idx := idx.insert names[i]! i
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[m]
  let mut fuel := names.size * names.size + 1
  while stack.size > 0 && fuel > 0 do
    fuel := fuel - 1
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    match idx.get? n with
    | some i =>
      for im in env.header.moduleData[i]!.imports do
        if !seen.contains im.module then stack := stack.push im.module
    | none => pure ()
  return seen

/-- The Part A modules (L1, L2, L3, L4, L4b) that L5 must be able to name from the statement. -/
def partAModules : List Lean.Name :=
  [`Nock.NockVMROM.Thm54.P8Core.RepartitionedStaging,
   `Nock.NockVMROM.Thm54.P8Core.PartAReadSets,
   `Nock.NockVMROM.Thm54.P8Core.PartATuple12,
   `Nock.NockVMROM.Thm54.P8Core.PartAMemoryChip12,
   `Nock.NockVMROM.Thm54.P8Core.PartAPackage12,
   `Nock.NockVMROM.Thm54.P8Core.PartAEvents12,
   `Nock.NockVMROM.Thm54.P8Core.PartAColumnsToEnvs,
   `Nock.NockVMROM.Thm54.P8Core.PartAB0Locality,
   `Nock.NockVMROM.Thm54.P8Core.PartASummandsB0,
   `Nock.NockVMROM.Thm54.P8Core.PartASummandsM2,
   `Nock.NockVMROM.Thm54.P8Core.PartATopology12,
   `Nock.NockVMROM.Thm54.P8Core.PartAStaged12,
   `Nock.NockVMROM.Thm54.Unhosted309Chip,
   `Nock.NockVMROM.Thm54.Unhosted309Semantics,
   `Nock.NockVMROM.Thm54.Unhosted309Codec,
   `Nock.NockVMROM.Thm54.Unhosted309Insensitive,
   `Nock.NockVMROM.Thm54.Unhosted309Canonical,
   `Nock.NockVMROM.Thm54.Unhosted309Realization,
   `Nock.NockVMROM.Thm54.Unhosted309Events]

/-! **The import-graph proof line.**  Throws unless (i) the positive control's closure contains
the statement and (ii) no Part A module's closure does. -/
open Lean in
run_cmd do
  let env ← getEnv
  let stmt := `Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
  let ctrl := importClosure env `Nock.NockVMROM.Thm54.DeployedStaging
  unless ctrl.contains stmt do
    throwError "Batch1440 control: DeployedStaging closure does not contain the statement"
  let mut above : Array Name := #[]
  for m in partAModules do
    unless env.header.moduleNames.contains m do
      throwError s!"Batch1440: module {m} not in the environment"
    if (importClosure env m).contains stmt then above := above.push m
  unless above.isEmpty do
    throwError s!"Batch1440: modules above the statement: {above}"
  logInfo m!"Batch1440 IMPORT-GRAPH: {partAModules.length} Part A modules, 0 import \
    {stmt}; control DeployedStaging imports it: true"

end Nock.RedTeam.Batch1440

#print axioms Nock.RedTeam.Batch1440.coeffChals_eq
#print axioms Nock.RedTeam.Batch1440.mixedSlots_eq
#print axioms Nock.RedTeam.Batch1440.mixedRawChals_eq
