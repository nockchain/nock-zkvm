import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.FamilyMemoryRows
import Nock.NockVMROM.Thm54.AxisSoundness
import Nock.NockVMROM.Thm54.ExactCanonicalRAP

/-!
Meta-program that computes the set of `Nock`-prefixed constants reachable from `nockCompiles_zmod`, `nockCompiles_p76` and `optimizedFullStrictNockVMROM_of_package`, and reports which memory-transfer, mirror, topology and reflected-AIR declarations each root reaches, with positive controls that must be reached.
-/
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
open Lean Elab Command

namespace Nock.RedTeam.Batch727

partial def reach (env : Environment) (roots : Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut work := roots.toList
  while true do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      if !(`Nock).isPrefixOf n then continue
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
        for c in cs do
          unless seen.contains c do work := c :: work
  return seen

def shiftedBeta : Array Name := #[
  ``Nock.NockVMROM.Thm54.FamilyMemoryRows.deployed_row_vmem_at,
  ``Nock.NockVMROM.Thm54.FamilyMemoryRows.deployed_row_interV_at,
  ``Nock.NockVMROM.Thm54.FamilyMemoryRows.expShiftInputs,
  ``Nock.NockVMROM.Thm54.FamilyMemoryRows.rowExpTerm]

def mirror : Array Name := #[``Nock.MemoryTable.Fmem, ``Nock.MemoryTable.Vmem,
  ``Nock.MemoryTable.interV, ``Nock.MemoryTable.interR, ``Nock.MemoryTable.pole,
  ``Nock.MemoryTable.recRLC, ``Nock.MemoryTable.eqBlk, ``Nock.MemoryTable.Pub,
  ``Nock.MemoryTable.Inputs, ``Nock.ComputeTable.MemRec]

def topology : Array Name := #[``Nock.NockVMROM.Thm54.MemoryExactTopology,
  ``Nock.NockVMROM.Thm54.TraversableChainedSemanticExactLanguage,
  ``Nock.NockVMROM.Thm54.TraversableChainedSemanticExactLanguage.exactAxisBridgeLocal,
  ``Nock.NockVMROM.Thm54.MemoryExactTopology.fanout_binding]

def reflected : Array Name := #[``Nock.Reified.poleExpr, ``Nock.Reified.Trans.memoryAIRchained,
  ``Nock.NockVMROM.Thm54.exactChainedHasCanonicalRAP2]

def controls : Array Name := #[``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.reqIdxCol,
  ``Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal.computeExpGates,
  ``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.reqIdxRLCTerm]

def report (env : Environment) (tag : String) (root : Name) : CommandElabM Unit := do
  unless (env.find? root).isSome do throwError m!"missing root {root}"
  let cl := reach env #[root]
  let f (a : Array Name) := a.filter cl.contains
  for n in controls do
    unless cl.contains n do throwError m!"positive control failed at {tag}: {n}"
  logInfo m!"{tag}: {cl.size} constants\n  shifted-β transfer reached: {f shiftedBeta}\n  mirror reached: {f mirror}\n  topology / axis bridge reached: {f topology}\n  reflected AIR reached: {f reflected}\n  controls reached: {f controls}"

run_cmd do
  let env ← getEnv
  report env "nockCompiles_zmod" ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
  report env "nockCompiles_p76" ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76
  report env "of_package"
    ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end Nock.RedTeam.Batch727
