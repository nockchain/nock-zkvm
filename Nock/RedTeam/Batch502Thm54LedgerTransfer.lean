/-
  Nock/RedTeam/Batch502Thm54LedgerTransfer.lean

  Ledger transfer of
  `computeTopology` / `memoryTopology` onto `AcceptedContent` wants
  those conjuncts at `T.specializedExec`.  `specializedExec` is the wrap-then-specialize of
  that execution (`AcceptedContentOfTracesFill.specializedExec_eq`,
  `WrapMemoryConjuncts.specialized_memoryRows_map`).  `pt` is
  recovered (`wrapMemoryLabel_specialize_pt`); Fmem / RVT transport
  through the wrap is the remaining join.

  Ledger stays **7**.  Dropping the names would be a lie.

  Seed slots 9..11: `memoryPublicOfTuple` already pass-throughs them
  (`memoryPublicOfTuple_eq_pkg`).  `walkSeed` pin kept (canonical
  subst still names public role 1).
-/
import Nock.NockVMROM.Thm54.ExactTraversal
import Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
import Nock.NockVMROM.Thm54.WrapMemoryConjuncts
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch500Thm54GammaTransport
import Nock.RedTeam.Batch501Thm54MemoryTopology
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch502

open scoped Polynomial
open Polynomial
open Nock
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Module
open Nock.RedTeam.Batch448

/-! ## Ledger: 7 until wrap-specialize RVT lands -/

def openAfterLedgerTransfer : List String :=
  openConjunctsAfterVer

theorem openAfterLedgerTransfer_length :
    openAfterLedgerTransfer.length = 7 :=
  openConjunctsAfterVer_length

theorem topology_names_still_on_ledger :
    "computeTopology" ∈ openAfterLedgerTransfer ∧
      "memoryTopology" ∈ openAfterLedgerTransfer := by
  decide

/-- The wrap-specialize RVT join. -/
def remainingJoin : String :=
  "RVTWithArity transport through wrapMemoryLabel.specialize / wrapComputeLabel.specialize"

theorem remainingJoin_nonempty : remainingJoin ≠ "" := by
  decide

/-- Receipt already compiled as `memoryPublicOfTuple_eq_pkg`
    (slots outside `6..8` are `pkgPub`, including 9..11). -/
def seedPublicDeletionStatus : String :=
  "memoryPublicOfTuple 9..11 = pkgPub (receipt); ExactMemoryCoordinatePins.walkSeed kept; digest unmoved"

theorem seedPublicDeletionStatus_nonempty :
    seedPublicDeletionStatus ≠ "" := by
  decide

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (h : TracesWalkHyps P Qc₀ Qm₀ c)
  (hz : nprSeed c.1 ≠ 0)

/-- **Exact remaining statement.**  `AcceptedContent.memoryTopology` at
    the traces strategy, i.e. topology of `specializedExec`. -/
def specializedMemoryTopology : Prop :=
  MemoryExactTopology
    ((strategyOfTraces P Qc₀ Qm₀ c h).specializedExec
      (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda)

/-- **Exact remaining statement.**  `AcceptedContent.computeTopology`. -/
def specializedComputeTopology : Prop :=
  ComputeExactTopology
    ((strategyOfTraces P Qc₀ Qm₀ c h).specializedExec
      (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda)

theorem exec_memoryTopology_is_not_specialized
    (htop : MemoryExactTopology (execOfTraces P Qc₀ Qm₀ c h)) :
    MemoryExactTopology (execOfTraces P Qc₀ Qm₀ c h) ∧
      specializedMemoryTopology P c Qc₀ Qm₀ h hz =
        MemoryExactTopology
          ((strategyOfTraces P Qc₀ Qm₀ c h).specializedExec
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda) :=
  ⟨htop, rfl⟩

end

end Nock.RedTeam.Batch502

#print axioms Nock.RedTeam.Batch502.openAfterLedgerTransfer_length
#print axioms Nock.RedTeam.Batch502.exec_memoryTopology_is_not_specialized
