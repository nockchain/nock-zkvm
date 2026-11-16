/-
  Nock/RedTeam/Batch1650Thm54VclLEventsFigures.lean

  **1651: receipts for the VCL-L events and figures.**
  Production: `Thm54/VclL/Events/{Bound, Summands}.lean`.

  (allowOpaque := true)`) asserts that the closures of
      `epsilon_vcll_eq`, `vclMemSummands`, `boundVCL` and the four figures contain no constant of
      the walk instance's memory summands (memory topology / tiling, the forest α-event, the forest
      prefix-γ set, the axis share, Form R, `tsColl`, summand 15, the `intermediate` LogUp,
      `…Bound15`, `p8WorkEv`).  Positive controls, same instrument, opposite assertion:
      `Pkg12.summand15` and `TightWindow.p8WorkEvK`.
  The NC values (exact rationals at the closed form, lane scratch `eps5.py`): `kc = 3` 121.78,
  one tagged accumulator 120.83, `m_x = 12` 122.04, validity per chain 122.02; the theorems
  compile which side of 122 each lands on.
-/
import Lean
import Nock.NockVMROM.Thm54.VclL.Events.Summands
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.TightWindow

set_option autoImplicit false

namespace Nock.RedTeam.Batch1650

open Lean Meta Elab Command
open Nock.NockVMROM.Thm54.VclL.Events

/-! ## §A  Axioms -/

#print axioms figVCL_two_pow_31
#print axioms figVCL_two_pow_32
#print axioms figVCL_kernel
#print axioms figVCL_bench
#print axioms figVCL_not_123
#print axioms figVCL_not_121_at_32
#print axioms figVCL_kc3_fails
#print axioms figVCL_oneAcc_fails
#print axioms figVCL_mx12_holds
#print axioms figVCL_kvP_holds
#print axioms epsilon_vcll_eq
#print axioms epsilonOf_vclMemSummands
#print axioms ioFailureUnionBound_eq_zero_add
#print axioms two_mul_sizeWindowRootBound
#check @epsilon_vcll_eq
#check @figVCL_two_pow_31
#check @vclMemSummands

/-! ## §B  The deleted summands are not read at the new roots -/

/-- Every `Nock.*` constant reachable from `root` through types and values (theorems included). -/
partial def walkReach (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      let mut es : Array Expr := #[ci.type]
      if let some v := ci.value? (allowOpaque := true) then es := es.push v
      for e in es do
        for c in e.getUsedConstants do
          if (`Nock).isPrefixOf c && !seen.contains c then todo := todo.push c
  return seen

/-- The walk instance's memory summands, deleted at VCL-L. -/
def deletedMarkers : List String :=
  ["memoryTilingEvent", "memoryForestAlpha", "forestPrefixBadGammas", "TimestampCollision",
   "timestampCollisionBound", "axisUniformWorkload", "formRUniform", "formRLambda", "summand15",
   "interWork", "interFailure", "Bound15", "p8WorkEv", "MemoryWalk", "memoryWalk", "memoryChipAt12"]

def hits (s : NameSet) : List Name :=
  s.toList.filter fun n => deletedMarkers.any fun m => (n.toString.splitOn m).length > 1

elab "#assertNoDeleted " id:ident : command => do
  let env ← getEnv
  let root := id.getId
  unless env.contains root do throwError "missing root {root}"
  let s := walkReach env root
  let h := hits s
  unless h.isEmpty do throwError "{root}: deleted summands reached: {h.take 20}"
  logInfo m!"{root}: proof closure {s.size}; deleted summands reached: []"

elab "#assertReachesDeleted " id:ident : command => do
  let env ← getEnv
  let root := id.getId
  unless env.contains root do throwError "missing root {root}"
  let s := walkReach env root
  let h := hits s
  if h.isEmpty then throwError "{root}: positive control FAILED (nothing reached)"
  logInfo m!"{root}: proof closure {s.size}; positive control reaches {h.length}: {h.take 6}"

#assertNoDeleted Nock.NockVMROM.Thm54.VclL.Events.epsilon_vcll_eq
#assertNoDeleted Nock.NockVMROM.Thm54.VclL.Events.vclMemSummands
#assertNoDeleted Nock.NockVMROM.Thm54.VclL.Events.boundVCL
#assertNoDeleted Nock.NockVMROM.Thm54.VclL.Events.figVCL_two_pow_31
#assertNoDeleted Nock.NockVMROM.Thm54.VclL.Events.figVCL_two_pow_32
#assertNoDeleted Nock.NockVMROM.Thm54.VclL.Events.figVCL_kernel
#assertNoDeleted Nock.NockVMROM.Thm54.VclL.Events.figVCL_bench
-- positive controls
#assertReachesDeleted Nock.NockVMROM.Thm54.PartA12.Pkg12.summand15
#assertReachesDeleted Nock.NockVMROM.Thm54.TightWindow.p8WorkEvK

end Nock.RedTeam.Batch1650
