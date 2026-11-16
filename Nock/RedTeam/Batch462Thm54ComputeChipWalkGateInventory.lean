/-
  Nock/RedTeam/Batch462Thm54ComputeChipWalkGateInventory.lean

  But `Walk.QGate` is a `Prop` structure over
  `ℕ → K` functions — a soundness-side object.  A chip that HAD a queue-length gate would
  express it as a reified `Expr` under `Nock.Reified.Trans.*` (as the walk gates are:
  `Trans.walkLnStep`, `walkCountStep`, `walkAccStep`, `walkLn1`, `walkCount1`,
  `walkAccInit`, `walkOut`, `Nock/AIR.lean`), and would never mention `Walk.QGate`.  So
  "`QGate` not reached" is consistent with the chip carrying such a gate under another
  name; the absence has to be measured on the gate names the chip does reach.

  This file runs the same reach instrument (`Batch337.reachSet`, values with
  `allowOpaque`) and
  * prints every `Nock.Reified.Trans.*` name reached from `computeChipAt` (the chip's
    reified gate inventory);
  * Throws if NO reached name is queue-shaped — the deployed chip now hosts
    `walkQueueNonEmpty` / `walkQueueTiling` / `queueWitnessGates`;
  * positive controls: all seven `Trans.walk*` gate names are reached (the instrument sees
    the walk gates), and the same filter applied to the reach set of
    `Walk.Sf_tiling_of_qgate` is NON-empty (the filter catches queue names where they are).

  Limit, stated: this is a NAME instrument.  A queue-length gate under a name matching
  none of these patterns would not be seen.
-/
import Lean
import Nock.Walk
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.RedTeam.Batch337Thm54HostileGapAudit
import Nock.RedTeam.Batch459Thm54ComputeTopologyStop

set_option autoImplicit false

namespace Nock.RedTeam.Batch462

open Lean Meta Elab Command

def CHIP : Name := ``Nock.NockVMROM.Thm54.DeployedChipFamily.computeChipAt
def TILING_THM : Name := ``Nock.Walk.Sf_tiling_of_qgate

/-- The seven reified walk gates of `Nock/AIR.lean`. -/
def walkGateNames : List Name :=
  [``Nock.Reified.Trans.walkLnStep, ``Nock.Reified.Trans.walkCountStep,
   ``Nock.Reified.Trans.walkAccStep, ``Nock.Reified.Trans.walkLn1,
   ``Nock.Reified.Trans.walkCount1, ``Nock.Reified.Trans.walkAccInit,
   ``Nock.Reified.Trans.walkOut]

/-- Queue-shaped name components, lower-cased. -/
def queuePatterns : List String := ["queue", "qgate", "qinv", "qlen"]

def componentHasPattern (s : String) : Bool :=
  let l := s.toLower
  queuePatterns.any fun p => (l.splitOn p).length > 1

/-- A name is queue-shaped if any component of it contains a queue pattern. -/
def isQueueShaped (n : Name) : Bool :=
  n.components.any fun c => componentHasPattern c.toString

def isTransName (n : Name) : Bool := (`Nock.Reified.Trans).isPrefixOf n

run_cmd do
  let env ← getEnv
  let rChip := Batch337.reachSet env CHIP
  let rTiling := Batch337.reachSet env TILING_THM
  let transNames := (rChip.toList.filter isTransName).mergeSort (fun a b => a.toString ≤ b.toString)
  let chipQueue := rChip.toList.filter isQueueShaped
  let tilingQueue := rTiling.toList.filter isQueueShaped
  let missingWalk := walkGateNames.filter fun n => !rChip.contains n
  logInfo m!"computeChipAt reach={rChip.size}; Trans.* names reached ({transNames.length}): {transNames}"
  logInfo m!"computeChipAt queue-shaped names reached: {chipQueue}"
  logInfo m!"Sf_tiling_of_qgate reach={rTiling.size}; queue-shaped names reached: {tilingQueue}"
  unless !chipQueue.isEmpty do
    throwError "deployed compute chip reaches no queue-shaped name (Batch482 expected walkQueue*)"
  unless missingWalk.isEmpty do
    throwError "positive control failed: walk gate(s) not reached from computeChipAt: {missingWalk}"
  unless !tilingQueue.isEmpty do
    throwError "positive control failed: the queue filter catches nothing on Sf_tiling_of_qgate"

/-- The compute chip now reaches the ratio-form
queue-witness names.  All seven `Trans.walk*` remain reached. -/
def instrument_reading : String :=
  "queue-shaped gate names reached from computeChipAt (walkQueue*); all seven Trans.walk* reached"

end Nock.RedTeam.Batch462
