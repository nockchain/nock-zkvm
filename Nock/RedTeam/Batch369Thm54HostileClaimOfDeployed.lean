/-
  Nock/RedTeam/Batch369Thm54HostileClaimOfDeployed.lean

  **Semantic conclusion at the built strategy.**

  Do not quote `same_problem_claim` (vacuous `rfl`) as this theorem.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.ProductionP8AcceptedContent
import Nock.NockVMROM.Thm54.StrategyOfTraces
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfigGoldilocks
import Nock.RedTeam.Batch367Thm54FamilyOfTraces
import Nock.RedTeam.Batch368Thm54AcceptedContentDischarge
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch369

open scoped Polynomial
open Polynomial
open Nock
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.RedTeam.Batch367
open Nock.RedTeam.Batch368

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Public claim of the *decoded* traces
holds mod `q`, at a strategy built from those traces.  Uninhabited
until `strategyOfTraces : ProductionStrategy` and the 20 open
conjuncts land. -/
def HostileClaimHoldsOfDeployed
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) : Prop :=
  (publicClaimOf P Qc Qm).HoldsMod (ringChar K)

/-- Shape at a Goldilocks-typed package: the conclusion type is
well-formed.  Not a literal at a named `(Qc, Qm)`. -/
abbrev GF := Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.F
abbrev GK := Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.K

def matmulHostileClaimType {h : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage GF GK h)
    (Qc : Fin P.computeChip.rap.w → GF[X])
    (Qm : Fin P.memoryChip.rap.w → GF[X]) : Prop :=
  HostileClaimHoldsOfDeployed P Qc Qm

/-- `accepted_outside_failureUnion_content` is the spine this
conclusion will apply.  Reached by name; not applied (no
`ProductionStrategy`). -/
def spine :=
  @accepted_outside_failureUnion_content

end

end Nock.RedTeam.Batch369

#print axioms Nock.RedTeam.Batch369.spine
