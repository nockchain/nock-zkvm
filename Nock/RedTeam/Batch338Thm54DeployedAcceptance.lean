/-
  Nock/RedTeam/Batch338Thm54DeployedAcceptance.lean

  `DeployedAcceptance`'s field types reach none of `P.strategy`,
  `P.objects`, `P.optimized.census`, `P.optimized.sampled.sampled.records`.
  Positive control: the same walk over `OptimizedProductionAcceptanceAt` reaches
  `P.strategy`.

  Instrument: `value? Named `typeReach`.
-/
import Lean
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.FiniteFieldIOSoundness
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch338

open Lean Meta Elab Command
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.FiniteIO

/-- Direct constants of a declaration's TYPE. -/
def typeOf (env : Environment) (root : Name) : Array Name :=
  match env.find? root with
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- Transitive `Nock.*` walk of TYPES, not proof terms.  Reachability, not
dependence.  Constructors are not entered, so a package structure's field
list is invisible. -/
def typeReach (env : Environment) (roots : Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := roots
  while stack.size > 0 do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if (`Nock).isPrefixOf c then
      for d in typeOf env c do
        unless seen.contains d do stack := stack.push d
  return seen

/-- Projection names of a structure, as fully-qualified constants. -/
def projNames (env : Environment) (S : Name) : Array Name :=
  (getStructureFields env S).filterMap fun f => getProjFnForField? env S f

def FORBIDDEN : List Name :=
  [``OptimizedFullStrictNockVMROMPackage.strategy,
   ``OptimizedFullStrictNockVMROMPackage.objects,
   ``OptimizedStrictNockVMROMPackage.census,
   ``FiniteIOStrategy.records]

/-! §1 — `DeployedAcceptance` field types miss the four honest-side marks. -/
run_cmd do
  let env ← getEnv
  let S : Name := ``DeployedAcceptance
  unless (getStructureFields env S).size == 5 do
    throwError "DeployedAcceptance field count"
  let roots := projNames env S
  let r := typeReach env roots
  for n in FORBIDDEN do
    if r.contains n then
      throwError m!"DeployedAcceptance type-walk reaches forbidden {n}"
  -- positive: the walk is not empty and does reach the chips
  unless r.contains ``OptimizedFullStrictNockVMROMPackage.computeChip do
    throwError "DeployedAcceptance does not reach computeChip (walk too weak)"
  unless r.contains ``OptimizedFullStrictNockVMROMPackage.memoryChip do
    throwError "DeployedAcceptance does not reach memoryChip (walk too weak)"
  logInfo m!"Batch338 DeployedAcceptance typeReach={r.size} fields={roots.size} (no strategy/objects/census/records)"

run_cmd do
  let env ← getEnv
  let S : Name := ``OptimizedFullStrictNockVMROMPackage.OptimizedProductionAcceptanceAt
  let roots := projNames env S
  let r := typeReach env roots
  if r.contains ``OptimizedFullStrictNockVMROMPackage.strategy then
    throwError "OptimizedProductionAcceptanceAt still reaches P.strategy (2a deleted p8/same_problem)"
  logInfo m!"Batch338 OptimizedProductionAcceptanceAt typeReach={r.size} (strategy ABSENT since 2a)"

/-- §3 — public equality checks are already gates of the compute chip. -/
theorem b338_endpoint_checks_are_gates
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {n : ℕ} (b : Module.Basis (Fin 3) F K) :
    ∀ g ∈ OptimizedComputeFinal.finalEndpointEqualityChecks (F := F),
      g ∈ OptimizedComputeCorrectedFinal.correctedFinalComputeAllGates n b :=
  finalEndpointEqualityChecks_mem_allGates b

end Nock.RedTeam.Batch338

#print axioms Nock.RedTeam.Batch338.b338_endpoint_checks_are_gates
