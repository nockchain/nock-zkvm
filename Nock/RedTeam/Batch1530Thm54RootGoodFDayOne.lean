/-
  Nock/RedTeam/Batch1530Thm54RootGoodFDayOne.lean

  Receipts here:
  * §A `#print axioms` of every new theorem.
  * §B the honest-free walker (proof terms traversed with `value? (allowOpaque := true)`): the new
    theorems reach none of `HonestCall`, `evalGBy`, `honestCall_kid`, `honestCall_inputs_le`,
    `c2_aligned_genuine`, `c2_aligned_eval`, `Batch1171.Inp`, `Batch1171.Ctx.hΛG`,
    `programLeafBound`, `genComputeSkeleton`; positive control: `Batch1171.root_good` and
    `Batch1173.ctx_of_traces_ev` reach them.
  * §C the window entry points as statements: `CtxF`'s window fields and `ctxF_of_traces_ev`'s
    premises (`#check`).
-/
import Nock.NockVMROM.Thm54.P8Core.RootGoodF
import Nock.NockVMROM.Thm54.P8Core.EvOnly.RootGoodFTracesEv

set_option autoImplicit false

namespace Nock.RedTeam.Batch1530

/-! ## §A  Axioms -/

#print axioms Nock.NockVMROM.Thm54.RootGoodF.lowOrderFree_of_not_mem
#print axioms Nock.NockVMROM.Thm54.RootGoodF.not_mem_of_lowOrderFree
#print axioms Nock.NockVMROM.Thm54.RootGoodF.window_lt_orderOf
#print axioms Nock.NockVMROM.Thm54.RootGoodF.sizeWindow_of_lowOrderFree
#print axioms Nock.NockVMROM.Thm54.RootGoodF.atom_of_size_z
#print axioms Nock.NockVMROM.Thm54.RootGoodF.CtxF.window
#print axioms Nock.NockVMROM.Thm54.RootGoodF.CtxF.of_ctx
#print axioms Nock.NockVMROM.Thm54.RootGoodF.slot0F
#print axioms Nock.NockVMROM.Thm54.RootGoodF.head_atomF
#print axioms Nock.NockVMROM.Thm54.RootGoodF.tail_bind2F
#print axioms Nock.NockVMROM.Thm54.RootGoodF.tail_cellF
#print axioms Nock.NockVMROM.Thm54.RootGoodF.step_s0F
#print axioms Nock.NockVMROM.Thm54.RootGoodF.step_s1F
#print axioms Nock.NockVMROM.Thm54.RootGoodF.leaf_goodF
#print axioms Nock.NockVMROM.Thm54.RootGoodF.leaf_eval_win
#print axioms Nock.NockVMROM.Thm54.RootGoodF.root_goodF_s2_twoLevel
#print axioms Nock.NockVMROM.Thm54.RootGoodF.root_goodF_s4_oneLevel
#print axioms Nock.NockVMROM.Thm54.RootGoodF.ctxF_of_traces_ev

/-! ## §B  The honest-free walker -/

open Lean Meta Elab Command

/-- The honest-tree constants the package-free route must not reach. -/
def honestNames : List Name := [`Nock.NockVMROM.Thm54.ComputedWindow.HonestCall,
  `Nock.FieldEmbedding.evalGBy, `Nock.NockVMROM.Thm54.ComputedWindow.honestCall_kid,
  `Nock.NockVMROM.Thm54.ComputedWindow.honestCall_inputs_le,
  `Nock.RedTeam.Batch1091.c2_aligned_genuine, `Nock.RedTeam.Batch1091.c2_aligned_eval,
  `Nock.RedTeam.Batch1171.Inp, `Nock.RedTeam.Batch1171.Ctx.hΛG,
  `Nock.NockVMROM.Thm54.TraceGen.programLeafBound,
  `Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton]

def nockReach (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      let mut es : Array Expr := #[ci.type]
      if let some v := ci.value? (allowOpaque := true) then es := es.push v
      for e in es do
        for c in e.getUsedConstants do
          if (`Nock).isPrefixOf c && !seen.contains c then todo := todo.push c
  return seen

/-- Fails unless the constant's closure reaches NONE of `honestNames`. -/
elab "#assertHonestFree " id:ident : command => do
  let seen := nockReach (← getEnv) id.getId
  let hit := honestNames.filter seen.contains
  unless hit.isEmpty do throwError m!"{id.getId} reaches honest constants {hit}"
  logInfo m!"{id.getId}: proof closure {seen.size}; honest constants reached: []"

/-- Positive control: fails unless the constant's closure reaches SOME of `honestNames`. -/
elab "#assertHonestReached " id:ident : command => do
  let seen := nockReach (← getEnv) id.getId
  let hit := honestNames.filter seen.contains
  if hit.isEmpty then throwError m!"{id.getId}: positive control reached no honest constant"
  logInfo m!"{id.getId}: proof closure {seen.size}; honest constants reached: {hit}"

#assertHonestFree Nock.NockVMROM.Thm54.RootGoodF.root_goodF_s2_twoLevel
#assertHonestFree Nock.NockVMROM.Thm54.RootGoodF.root_goodF_s4_oneLevel
#assertHonestFree Nock.NockVMROM.Thm54.RootGoodF.ctxF_of_traces_ev
#assertHonestFree Nock.NockVMROM.Thm54.RootGoodF.CtxF
#assertHonestFree Nock.NockVMROM.Thm54.RootGoodF.InpF
-- positive controls: the honest-tree routes reach them
#assertHonestReached Nock.RedTeam.Batch1171.root_good
#assertHonestReached Nock.RedTeam.Batch1173.ctx_of_traces_ev

/-! ## §C  The window entry points -/

#check @Nock.NockVMROM.Thm54.RootGoodF.LowOrderFree
#check @Nock.NockVMROM.Thm54.RootGoodF.CtxF.hW1
#check @Nock.NockVMROM.Thm54.RootGoodF.CtxF.hlow
#check @Nock.NockVMROM.Thm54.RootGoodF.InpF.win
#check @Nock.NockVMROM.Thm54.RootGoodF.ctxF_of_traces_ev

end Nock.RedTeam.Batch1530
