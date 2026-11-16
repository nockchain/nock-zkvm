/-
  Nock/RedTeam/Batch403Thm54PublicFromSeedBlocked.lean

  **`public_*` from walk seed BLOCKED.**

  Brief asked to replace `` `Batch398.closedPublicConjuncts_of_binds` ``
  by `closedPublicConjuncts_of_deployed` with **no** `hbinds`, closing
  `public_subject/formula/result` from `finalMaskedWalkAccInit` +
  verifier-computed seed outside the RLC-collision event.

  The deployed seed is not claim-computable
  (`verifier_seed_stop_mr1_not_in_claim`).  Without wiring a
  verifier seed into slots `3..5`, the walk-init gate only forces
  `acc(0)` against a **prover-committed** seed and does not mention
  the claim.  Chip-close of the three publics is therefore blocked.

  Count stays **11/21**.  NU's three `public_*` remain
  **hypothesis-closed** under `TracesBindsHyps` (not chip-closed).
  This file records that classification and the blocked proof shape.
-/
import Lean
import Nock.NockVMROM.Thm54.WrapPublicConjuncts
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
import Nock.NockVMROM.Thm54.NodeEncoding
import Nock.RedTeam.Batch398Thm54PublicConjuncts
import Nock.RedTeam.Batch402Thm54VerifierSeedStop
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch403

open Lean Meta Elab Command
open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified (Expr)
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WrapPublicConjuncts
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.RedTeam.Batch398
open Nock.RedTeam.Batch402
open Module

/-! ## Closed-count classification (chip vs hypothesis) -/

/-- Still 11. -/
theorem closed_count_unchanged : 21 - openConjuncts.length = 11 :=
  Batch398.closed_count

/-- The three `public_*` names NU closed. -/
def publicNames : List String := newlyClosed

theorem publicNames_length : publicNames.length = 3 :=
  newlyClosed_length

def chipClosedPublics : ℕ := 0

/-- Hypothesis-closed among the three publics: **3** (NU / `TracesBindsHyps`). -/
def hypothesisClosedPublics : ℕ := 3

/-- Total closed AcceptedContent conjuncts: **11**. -/
def totalClosed : ℕ := 11

theorem publicCloseClassification_ok :
    chipClosedPublics = 0 ∧
      hypothesisClosedPublics = 3 ∧
      totalClosed = 11 ∧
      21 - openConjuncts.length = totalClosed := by
  decide

theorem closedPublicConjuncts_still_needs_binds
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hbinds : (strategyOfTraces P Qc Qm c h).BindsAtCoin c.1 c.2.2.2.lambda)
    (hz : nprSeed c.1 ≠ 0) :
    ClosedPublicConjuncts P Qc Qm c h hz :=
  closedPublicConjuncts_of_binds P Qc Qm c h hbinds hz

/-! ## Blocked chip-close path (receipt of shape, not a discharge) -/

/-- The walk-init gate that would carry the seed bind
    (`` `OptimizedComputeFinalTypedLowering.lean::finalMaskedWalkAccInit` ``). -/
def walkInitGate : Nock.Reified.Expr := finalMaskedWalkAccInit

def FINAL_MASKED_WALK_ACC_INIT : Name :=
  ``Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering.finalMaskedWalkAccInit

def TRACES_BINDS_HYPS : Name :=
  ``Nock.NockVMROM.Thm54.ProductionP8Containment.ProductionStrategy.BindsAtCoin

def CLOSED_OF_BINDS : Name :=
  ``Nock.RedTeam.Batch398.closedPublicConjuncts_of_binds

def valueDirect (env : Environment) (root : Name) : Array Name :=
  match env.find? root with
  | some ci =>
    match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants
    | none => #[]
  | none => #[]

elab "#batch403_binds_path_reaches_hbinds" : command => do
  let env ← getEnv
  let used := valueDirect env CLOSED_OF_BINDS
  unless used.contains TRACES_BINDS_HYPS do
    throwError "closedPublicConjuncts_of_binds does not reach BindsAtCoin"
  if used.contains FINAL_MASKED_WALK_ACC_INIT then
    throwError "binds path unexpectedly reaches finalMaskedWalkAccInit"
  logInfo m!"Batch403: NU public_* close reaches BindsAtCoin, \
    not finalMaskedWalkAccInit"

#batch403_binds_path_reaches_hbinds

/-- Width receipt after the `mr1` obstruction lifted (`Batch402.verifier_seed_stop_lifted`):
the deployed walk label is the ten-coordinate `LT_comp` projection. -/
theorem chip_close_blocked_by_verifier_seed_stop :
    NodeEncoding.computeNodeWidth = 10 :=
  Batch402.computeNodeWidth_eq_ten

end Nock.RedTeam.Batch403

#print axioms Nock.RedTeam.Batch403.closed_count_unchanged
#print axioms Nock.RedTeam.Batch403.publicCloseClassification_ok
#print axioms Nock.RedTeam.Batch403.closedPublicConjuncts_still_needs_binds
#print axioms Nock.RedTeam.Batch403.chip_close_blocked_by_verifier_seed_stop
