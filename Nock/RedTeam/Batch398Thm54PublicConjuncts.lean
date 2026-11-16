/-
  Nock/RedTeam/Batch398Thm54PublicConjuncts.lean

  **Close `public_subject/formula/result`.**

  Transfer is `WrapPublicConjuncts.specialized_public_*` from
  `BindsAt.root_bindings` under `TracesBindsHyps` (named hyp).  Not from
  `finalEndpointEqualityChecks` (those pin F-side state one-hots; claim
  fingerprints are K-side `fpOf` 11/14/17 — `Batch392`).

  `openConjuncts` shrinks by the three public names: **8 → 11** closed.
-/
import Lean
import Nock.GlobalCarryRecognizer
import Nock.NockVMROM.Thm54.WrapPublicConjuncts
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.NockVMROM.Thm54.JointSoundness
import Nock.RedTeam.Batch388Thm54OpenConjunctsTransfer
import Nock.RedTeam.Batch397Thm54FamilyPublics
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch398

open Lean Meta Elab Command
open scoped Polynomial
open Polynomial
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WrapPublicConjuncts
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.Framework
open MonolithicRAP
open Module
open Nock.RedTeam.Batch388

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Count 10. -/
def openConjuncts : List String :=
  ["memoryRows", "vmem", "mem_first_counts", "mem_first_indicator",
    "io", "computeTopology", "memoryTopology", "axisStructural",
    "rootBoundary", "structuralChecks"]

theorem openConjuncts_length : openConjuncts.length = 10 := by decide

theorem closed_count : 21 - openConjuncts.length = 11 := by decide

def newlyClosed : List String :=
  ["public_subject", "public_formula", "public_result"]

theorem newlyClosed_length : newlyClosed.length = 3 := by decide

theorem closed_count_after_lane_b : 8 + newlyClosed.length = 11 := by decide

/-- The three public conjuncts of `AcceptedContent` at the built strategy. -/
structure ClosedPublicConjuncts
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0) : Prop where
  public_subject :
    (((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computePubAt
      ⟨0, ((strategyOfTraces P Qc Qm c h).specializedCfg
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).compRows_pos⟩).s =
      GlobalCarryRecognizer.enc (nprSeed c.1)
        (strategyOfTraces P Qc Qm c h).verifier.raw.claim.subject
  public_formula :
    (((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computePubAt
      ⟨0, ((strategyOfTraces P Qc Qm c h).specializedCfg
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).compRows_pos⟩).f =
      GlobalCarryRecognizer.enc (nprSeed c.1)
        (strategyOfTraces P Qc Qm c h).verifier.raw.claim.formula
  public_result :
    (((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computePubAt
      ⟨0, ((strategyOfTraces P Qc Qm c h).specializedCfg
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).compRows_pos⟩).e =
      GlobalCarryRecognizer.enc (nprSeed c.1)
        (strategyOfTraces P Qc Qm c h).verifier.raw.claim.result

theorem closedPublicConjuncts_of_binds
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hbinds : (strategyOfTraces P Qc Qm c h).BindsAtCoin c.1 c.2.2.2.lambda)
    (hz : nprSeed c.1 ≠ 0) :
    ClosedPublicConjuncts P Qc Qm c h hz where
  public_subject := specialized_public_subject P Qc Qm c h hbinds hz
  public_formula := specialized_public_formula P Qc Qm c h hbinds hz
  public_result := specialized_public_result P Qc Qm c h hbinds hz

theorem public_names_left_open :
    newlyClosed.Sublist Nock.RedTeam.Batch388.openConjuncts := by
  decide

theorem public_names_not_open :
    ∀ name ∈ newlyClosed, name ∉ openConjuncts := by
  decide

end

/-- Off the walk block `0..5`, family publics are still the package map. -/
theorem readSet_independent_of_seed
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [Fintype F] [DecidableEq K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (claim : P8PublicClaim)
    (pkgPub : ℕ → F)
    (c c' : OptimizedProductionChallengeTuple K F)
    (j : ℕ) (hj : j ∈ computePublicReadSet) (hseed : ¬ j < 6) :
    computePublicOfTuple b claim pkgPub c j =
      computePublicOfTuple b claim pkgPub c' j := by
  rw [computePublicOfTuple_eq_pkg_on_readSet b claim pkgPub c j hj hseed,
    computePublicOfTuple_eq_pkg_on_readSet b claim pkgPub c' j hj hseed]

end Nock.RedTeam.Batch398

#print axioms Nock.RedTeam.Batch398.closed_count
#print axioms Nock.RedTeam.Batch398.closedPublicConjuncts_of_binds
#print axioms Nock.RedTeam.Batch398.readSet_independent_of_seed
