/-
  Nock/NockVMROM/Thm54/P8Core/EvOnly/Batch1090Thm54C2ReadyFuelEv.lean

  The originals are untouched.  Imports P8Core only; never the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PlacementABridge
import Nock.NockVMROM.Thm54.P8Core.EvOnly.OptimizedHostileTimestampsEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch465Thm54DeployedRootLabelEqClaimEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch489Thm54FoOfEqFoWEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch490Thm54TopologyAssemblyEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch500Thm54GammaTransportEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch501Thm54MemoryTopologyEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch822Thm54R4BridgeMemoryEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.FamilyIOChainRouteBEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch824Thm54R4BridgeEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.UniqueExponentsBridgeEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch973Thm54Round0WrapJoinEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch974Thm54Round0WrapJoinForestEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch1011Thm54AxisViewBindsAtCoinEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch1024Thm54C2BindsAtCoinEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch1090

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch1021
open Nock.RedTeam.Batch525
open Nock.GlobalCarryRecognizer
variable {K : Type} [Field K] [DecidableEq K]
variable {sv : MState → ℕ → Noun} {ax : ℕ → ℕ}
set_option quotPrecheck false
local notation "J" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) sv ax

section AtFamily

open scoped Polynomial
open Polynomial
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0A
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.RedTeam.Batch1024
variable {F K' : Type} [Field F] [Field K'] [Algebra F K']
  [Fintype F] [DecidableEq F]
  [Fintype K'] [DecidableEq K'] [CharP K' (ringChar K')] [FiniteDimensional F K']
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K' hOrb)
  (c : OptimizedProductionChallengeTuple K' F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)

theorem bindsAtCoin_C2_of_chipReady_ev
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x)
    (hα0 : alphaM c.1 ≠ 0) {q : ℕ}
    (hC : C2ChipReady (sv := svF P c Qm) (ax := axF P c Qc) (nprSeed c.1) q (treeS P c Qc)
      P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula)
    (hsRoot : bindFP (nprSeed c.1) P.optimized.verifier.raw.claim.subject
      (treeS P c Qc).label.1.2.2.1.s) :
    (TC P c Qc Qm h).BindsAtCoin c.1 c.2.2.2.lambda := by
  intro hz
  exact BindsAt.ofTreeBindings rfl (hcomp_C2_of_chipReady P c Qc Qm h hz hC hsRoot)
    (memoryForestBinds_C2_ev P c Qc Qm h hacc hgood hax hbasis hwidth hz hF hα0)

end AtFamily

end Nock.RedTeam.Batch1090

