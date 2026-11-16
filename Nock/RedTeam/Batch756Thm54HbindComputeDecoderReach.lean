/-
  Nock/RedTeam/Batch756Thm54HbindComputeDecoderReach.lean

  * **(A) Decoder reach census (compiled, `run_cmd`).**  A constant walk over types AND values
    (`ConstantInfo.value?
    - **All 22 of `Batch525.computeTreeBinds_*` / `bindComputeRow_*`, and `ComputeTreeBinds` /
      `BindComputeRow` themselves, reach none of them.**  They take every skeleton noun as a free
      parameter; there is nothing to "re-prove against a `reqIdx`-indexed decoder".
    - **Positive controls (same instrument):** `StrategyOfTraces.decodedSkeletonOf` reaches
      `StrategyOfTraces.nounByFP`; `Batch530.computeTreeBinds_of_ready` reaches
      `mapComputeJoinInFuel` and `nounByFP`.
    - **Per constructor of `Batch530.ComputeJoinReady`** (the deployed assembly's per-node
      premises, recursion through `ComputeJoinReady` itself cut): `cons` and `op1` are
      decoder-free; `op0` (`he`), `op9` (`harm`, `hInv`), and every constructor that reads a
      child's decoded evaluation through `mapComputeJoinInFuel` (`op2` `h3`, `op3` `hwin`, `op4`
      `hke`, `op5` `hfaith`, `op6` `hcondE`, `op7`/`op8` `hCons`) reach `nounByFP`.
    - **Route B's own target is decoder-free:** `Batch742.reqTgt`,
      `PreSeedCensus.requestTargets`, `PreSeedCensus.reqTgtOfEnvs` reach none of the names.
  * **(B) Feasibility probe, OP0 "re-based".**  `op0_rebased`: `Batch525.computeTreeBinds_op0`
    applied verbatim with the OP0 result supplied by an arbitrary lookup `look k` (e.g. a
    `reqIdx`-indexed pre-`z` decode, or `requestTargets S.verify_child k`).  Zero re-proof.
    `op0_rebased_record`: the request-record half of (iii) at that row is a projection of the
    row binding (`BindMemRec` of slot `1` is `⟨subj, look k, ax⟩`).
-/
import Nock.RedTeam.Batch530Thm54ComputeTreeBindsDeployed
import Nock.RedTeam.Batch742Thm54RouteBCensus

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch756

section Meta

open Lean Meta Elab Command

/-! ## (A) Decoder reach census -/

/-- Constants reachable from `roots` through types and values (theorem proofs included,
`allowOpaque := true`), descending only into `Nock.*` constants and never into `stop`. -/
def nockReach (env : Environment) (roots : List Name) (stop : NameSet := {}) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  let mut fuel := 5000000
  while fuel > 0 do
    fuel := fuel - 1
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      if stop.contains n then continue
      if n.getRoot != `Nock then continue
      match env.find? n with
      | none => continue
      | some ci =>
        let mut deps := ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          deps := deps ++ v.getUsedConstants
        if let .inductInfo ii := ci then
          deps := deps ++ ii.ctors.toArray
        for d in deps do
          if !seen.contains d then stack := d :: stack
  return seen

/-- The post-`z` decoder names (all select a memory node by the round-1 `pt.noun`). -/
def decoderNames : List Name :=
  [``Nock.NockVMROM.Thm54.StrategyOfTraces.nounByFP,
   ``Nock.NockVMROM.Thm54.StrategyOfTraces.joinNoun,
   ``Nock.NockVMROM.Thm54.StrategyOfTraces.memRecJoin,
   ``Nock.NockVMROM.Thm54.StrategyOfTraces.joinEvaluation,
   ``Nock.NockVMROM.Thm54.StrategyOfTraces.joinFormulaDeep,
   ``Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinInFuel,
   ``Nock.NockVMROM.Thm54.HostileSkeletonDecoding.nounByFP,
   ``Nock.NockVMROM.Thm54.HostileSkeletonDecoding.decodeMemoryRowIn]

def hitsOf (env : Environment) (roots : List Name) (stop : NameSet := {}) : List Name :=
  let r := nockReach env roots stop
  decoderNames.filter r.contains

/-- `Batch525`'s per-opcode lemmas (row binding and tree step), plus the binding predicates. -/
def batch525Names : List Name :=
  [``Nock.RedTeam.Batch525.bindComputeRow_cons, ``Nock.RedTeam.Batch525.bindComputeRow_op0,
   ``Nock.RedTeam.Batch525.bindComputeRow_op1, ``Nock.RedTeam.Batch525.bindComputeRow_op2,
   ``Nock.RedTeam.Batch525.bindComputeRow_op3, ``Nock.RedTeam.Batch525.bindComputeRow_op4,
   ``Nock.RedTeam.Batch525.bindComputeRow_op5, ``Nock.RedTeam.Batch525.bindComputeRow_op6,
   ``Nock.RedTeam.Batch525.bindComputeRow_op7, ``Nock.RedTeam.Batch525.bindComputeRow_op8,
   ``Nock.RedTeam.Batch525.bindComputeRow_op9,
   ``Nock.RedTeam.Batch525.computeTreeBinds_cons, ``Nock.RedTeam.Batch525.computeTreeBinds_op0,
   ``Nock.RedTeam.Batch525.computeTreeBinds_op1, ``Nock.RedTeam.Batch525.computeTreeBinds_op2,
   ``Nock.RedTeam.Batch525.computeTreeBinds_op3, ``Nock.RedTeam.Batch525.computeTreeBinds_op4,
   ``Nock.RedTeam.Batch525.computeTreeBinds_op5, ``Nock.RedTeam.Batch525.computeTreeBinds_op6,
   ``Nock.RedTeam.Batch525.computeTreeBinds_op7, ``Nock.RedTeam.Batch525.computeTreeBinds_op8,
   ``Nock.RedTeam.Batch525.computeTreeBinds_op9,
   ``Nock.NockVMROM.Thm54.SemanticStrategy.ComputeTreeBinds,
   ``Nock.NockVMROM.Thm54.SemanticStrategy.BindComputeRow]

run_cmd do
  let env ← getEnv
  -- positive controls first: the instrument must find the decoder where it really is
  let pc1 := hitsOf env [``Nock.NockVMROM.Thm54.StrategyOfTraces.decodedSkeletonOf]
  unless pc1.contains ``Nock.NockVMROM.Thm54.StrategyOfTraces.nounByFP do
    throwError "positive control 1 failed: decodedSkeletonOf does not reach nounByFP ({pc1})"
  let pc2 := hitsOf env [``Nock.RedTeam.Batch530.computeTreeBinds_of_ready]
  unless pc2.contains ``Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinInFuel &&
      pc2.contains ``Nock.NockVMROM.Thm54.StrategyOfTraces.nounByFP do
    throwError "positive control 2 failed: computeTreeBinds_of_ready ({pc2})"
  let mut bad : Array (Name × List Name) := #[]
  for n in batch525Names do
    let h := hitsOf env [n]
    unless h.isEmpty do bad := bad.push (n, h)
  unless bad.isEmpty do
    throwError "Batch525 reaches the decoder: {bad}"
  logInfo m!"A1: {batch525Names.length} Batch525 / binding names reach no decoder name; positive controls: decodedSkeletonOf → {pc1}; computeTreeBinds_of_ready → {pc2}"

-- (A2) Which `ComputeJoinReady` premises go through the decoder (recursion through the
-- inductive itself is cut, so each constructor is judged on its own premises).
run_cmd do
  let env ← getEnv
  let ind := ``Nock.RedTeam.Batch530.ComputeJoinReady
  let some (.inductInfo ii) := env.find? ind | throwError "ComputeJoinReady missing"
  let stop : NameSet := ({} : NameSet).insert ind
  let mut free : List Name := []
  let mut hit : List (Name × List Name) := []
  for ctor in ii.ctors do
    let h := hitsOf env [ctor] stop
    if h.isEmpty then free := free ++ [ctor] else hit := hit ++ [(ctor, h)]
  let expectFree : List Name :=
    [``Nock.RedTeam.Batch530.ComputeJoinReady.op1, ``Nock.RedTeam.Batch530.ComputeJoinReady.cons]
  unless free.length = expectFree.length && expectFree.all free.contains do
    throwError "unexpected decoder-free constructors: {free}"
  for (c, h) in hit do
    unless h.contains ``Nock.NockVMROM.Thm54.StrategyOfTraces.nounByFP do
      throwError "{c} reaches the decoder but not nounByFP: {h}"
  logInfo m!"A2: decoder-free constructors {free}; through nounByFP: {hit.map (·.1)}"

-- (A3) Route B's target and the lifted core are decoder-free.
run_cmd do
  let env ← getEnv
  let roots : List Name :=
    [``Nock.RedTeam.Batch742.reqTgt, ``Nock.RedTeam.Batch742.reqPairEvent,
     ``Nock.NockVMROM.Thm54.PreSeedCensus.requestTargets,
     ``Nock.NockVMROM.Thm54.PreSeedCensus.reqTgtOfEnvs,
     ``Nock.NockVMROM.Thm54.PreSeedCensus.reqPairEventOfEnvs]
  for n in roots do
    let h := hitsOf env [n]
    unless h.isEmpty do throwError "{n} reaches the decoder: {h}"
  logInfo m!"A3: {roots} reach no decoder name"

end Meta

/-! ## (B) Feasibility probe: OP0 with a re-based result -/

section Probe

open Nock Nock.ComputeTable Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.RedTeam.Batch525

variable {K : Type} [Field K] [DecidableEq K]

/-- **OP0 re-based, zero re-proof**: the result noun is any lookup `look k` (a `reqIdx`-indexed
pre-`z` decode, or a fixed target map); `Batch525.computeTreeBinds_op0` applies verbatim. -/
theorem op0_rebased {z : K} (hz : z ≠ 0) (look : ℕ → Noun) (k : ℕ)
    (subj tail : Noun) (ax : ℕ) (row : State × DTcomp K)
    (hstate : row.1 = .s0) (hzRow : row.2.1.z = z) (hpubSt : row.2.2.1.state = .s0)
    (hs : bindFP z subj row.2.2.1.s) (hh : bindFP z (.atom 0) row.2.2.2.f_h)
    (ht : bindFP z tail row.2.2.2.f_t) (he : bindFP z (look k) row.2.2.1.e)
    (hax : (ax : K) = row.2.2.2.f_t.leaf) (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    ComputeTreeBinds z (.node (skelOp0 subj tail (look k) ax) []) (.node row []) :=
  computeTreeBinds_op0 hz subj tail (look k) ax row hstate hzRow hpubSt hs hh ht he hax hV

/-- **(iii) at an OP0 row is a projection of the row binding**: the served record (slot `1`) binds
`⟨subj, look k, ax⟩`, i.e. its root fingerprint is `enc z subj` and its child `enc z (look k)`. -/
theorem op0_rebased_record {z : K} (hz : z ≠ 0) (look : ℕ → Noun) (k : ℕ)
    (subj tail : Noun) (ax : ℕ) (row : State × DTcomp K)
    (hstate : row.1 = .s0) (hzRow : row.2.1.z = z) (hpubSt : row.2.2.1.state = .s0)
    (hs : bindFP z subj row.2.2.1.s) (hh : bindFP z (.atom 0) row.2.2.2.f_h)
    (ht : bindFP z tail row.2.2.2.f_t) (he : bindFP z (look k) row.2.2.1.e)
    (hax : (ax : K) = row.2.2.2.f_t.leaf) (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    BindMemRec z ⟨subj, look k, ax⟩ (computeMemRec row.2.2.1 1) := by
  have hB := (bindComputeRow_op0 hz subj tail (look k) ax row hstate hzRow hpubSt hs hh ht he
    hax hV).2.2.2.2.2.2.2.2 1
  simpa [skelOp0, Nock.Framework.recordCount] using hB

end Probe

end Nock.RedTeam.Batch756

#print axioms Nock.RedTeam.Batch756.op0_rebased
#print axioms Nock.RedTeam.Batch756.op0_rebased_record
