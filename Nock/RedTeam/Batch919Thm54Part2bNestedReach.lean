/-
  Nock/RedTeam/Batch919Thm54Part2bNestedReach.lean

  Nothing consumes this.

  (2) proof-term reach
  (`allowOpaque := true`) from `of_package` and the spines `containment` / `acceptance_outside_failure_implies_target`
  to the Nested names.  (3) the DIRECT consumers in the capstone's proof closure: 16 at the 2a tip.
-/
import Lean
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedCanonicalTraces
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

open Lean

namespace Nock.RedTeam.Batch919

def isNock (n : Name) : Bool := (`Nock).isPrefixOf n

partial def reachGen (env : Environment) (useProofs : Bool) (queue : List Name) (seen : NameSet)
    : NameSet :=
  match queue with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reachGen env useProofs rest seen
    else
      match env.find? n with
      | none => reachGen env useProofs rest seen
      | some ci =>
        let vals : Array Expr :=
          match ci with
          | .thmInfo t => if useProofs then #[t.value] else #[]
          | _ => match ci.value? (allowOpaque := true) with | some v => #[v] | none => #[]
        let ctors : Array Expr := match ci with
          | .inductInfo iv => iv.ctors.foldl (init := #[]) fun acc c =>
              match env.find? c with | some cci => acc.push cci.type | none => acc
          | _ => #[]
        let es := #[ci.type] ++ ctors ++ vals
        let next := (es.foldl (init := #[]) fun acc e => acc ++ e.getUsedConstants).filter isNock
        reachGen env useProofs (next.toList ++ rest) (seen.insert n)

def nestedNames : List Name := [
  `Nock.AxisBridge.ReadVerifyNested,
  `Nock.AxisBridge.HonestRecon,
  `Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.readVerifyNestedCheck,
  `Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.AlphaFreeAxisStructure,
  `Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.structuralChecksAt,
  `Nock.AxisBridge.nested_of_readVerifyNested,
  `Nock.MemoryTable.interV,
  `Nock.MemoryTable.Vmem]

def mentions (env : Environment) (n : Name) (targets : List Name) : Bool :=
  match env.find? n with
  | none => false
  | some ci =>
    let es : Array Expr := #[ci.type] ++ (match ci with
      | .thmInfo t => #[t.value]
      | _ => match ci.value? (allowOpaque := true) with | some v => #[v] | none => #[])
    let used := es.foldl (init := #[]) fun acc e => acc ++ e.getUsedConstants
    targets.any fun t => used.contains t

end Nock.RedTeam.Batch919

open Nock.RedTeam.Batch919 in
run_cmd do
  let env ← Lean.getEnv
  let S := `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
  -- (1) type/definition-level reach from the statement (no proof terms)
  let typeReach := reachGen env false [S] {}
  Lean.logInfo s!"(1) type-level reach from the statement: {typeReach.size} constants"
  for t in nestedNames do
    Lean.logInfo s!"(1) statement meaning reaches {t}: {typeReach.contains t}"
  -- (2) proof-term reach from the capstone constructor and the two spines
  let roots : List Name := [
    `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package,
    `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.containment,
    `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.memory_source_gate_facts,
    `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.acceptance_outside_failure_implies_target]
  for r in roots do
    unless (env.find? r).isSome do
      Lean.logInfo s!"(2) MISSING root {r}"
      continue
    let pr := reachGen env true [r] {}
    Lean.logInfo s!"(2) proof reach from {r}: {pr.size} constants"
    for t in nestedNames do
      Lean.logInfo s!"(2)   {r} reaches {t}: {pr.contains t}"
  -- (3) direct consumers inside the capstone's proof closure
  let cap := reachGen env true
    [`Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package] {}
  let targets := [`Nock.AxisBridge.ReadVerifyNested, `Nock.AxisBridge.HonestRecon,
    `Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.AlphaFreeAxisStructure,
    `Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.readVerifyNestedCheck]
  let mut consumers : Array Name := #[]
  for n in cap.toList do
    if mentions env n targets && !n.isInternal then consumers := consumers.push n
  Lean.logInfo s!"(3) direct Nested consumers inside the capstone proof closure: {consumers.size}"
  for n in consumers.qsort (fun a b => a.toString < b.toString) do
    Lean.logInfo s!"(3)   {n}"
  -- positive controls
  let pc1 := reachGen env true [`Nock.AxisBridge.nested_of_readVerifyNested] {}
  unless pc1.contains `Nock.AxisBridge.ReadVerifyNested do throwError "positive control 1 failed"
  let pc2 := reachGen env false [`Nock.AxisBridge.HonestRecon] {}
  unless pc2.contains `Nock.AxisBridge.ReadVerifyNested do throwError "positive control 2 failed"
  let pc3 := reachGen env false
    [`Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.alphaFreeRootStructureCheck_eq_true_iff] {}
  unless pc3.contains `Nock.AxisBridge.ReadVerifyNested do throwError "positive control 3 failed"
  Lean.logInfo "positive controls 1-3 pass"
