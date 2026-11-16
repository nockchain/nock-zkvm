/-
  Nock/RedTeam/Batch819Thm54H13ConsumeReach.lean

  Instruments with positive controls; no production edit.**

  * **Q3 read set.** The event reads memory base columns `0, 1, 2` (selectors), `180` (`atom`),
    `181` (`reqIdx`) only; all five are round 0 in `DeployedStaging.memoryColRound` (`decide`).
    `Batch742.reqPairEvent_preZReads` / `Batch796.reqPairEvent_preZReads_both` are the compiled
    trace-side cylinders (imported here).
  * **Q4 U1 overlap.**
  * **Rule 4g-(i).**
-/
import Lean
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.PreZCensusCore
import Nock.RedTeam.Batch742Thm54RouteBCensus
import Nock.RedTeam.Batch796Thm54PreZComputeReads
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

open Lean Elab Command

namespace Nock.RedTeam.Batch819

open Nock.NockVMROM.Thm54

/-- Q3: the five columns the event reads are round 0. -/
theorem event_columns_round_zero :
    DeployedStaging.memoryColRound 0 = 0 ∧ DeployedStaging.memoryColRound 1 = 0 ∧
    DeployedStaging.memoryColRound 2 = 0 ∧
    DeployedStaging.memoryColRound OptimizedMemoryGateBasis.atomCol = 0 ∧
    DeployedStaging.memoryColRound OptimizedMemoryGateBasis.reqIdxCol = 0 := by
  decide

/-- Positive control of the instrument: a role column of round 1 is not round 0. -/
theorem role0_not_round_zero : DeployedStaging.memoryColRound 6 ≠ 0 := by decide

partial def reachSet (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut work := roots
  while true do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        match ci.value? (allowOpaque := true) with
        | some v => cs := cs ++ v.getUsedConstants
        | none => pure ()
        if let .inductInfo iv := ci then cs := cs ++ iv.ctors.toArray
        work := cs.toList ++ work
  return seen

def eventNames : List Name :=
  [`Nock.NockVMROM.Thm54.PreSeedCensus.reqPairEventOfEnvs,
   `Nock.NockVMROM.Thm54.PreSeedCensus.requestTargets,
   `Nock.NockVMROM.Thm54.PreSeedCensus.pairBadSeeds,
   `Nock.NockVMROM.Thm54.PreSeedCensus.decodePre,
   `Nock.NockVMROM.Thm54.StrategyOfTraces.memoryStateOf]

def u1Names : List Name :=
  [`Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate.topPin,
   `Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate.linCol,
   `Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate.comparisonTerms,
   `Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate.booleanGates]

def slot32 : Name := `Nock.NockVMROM.Thm54.DecodedLambdaEvent.decodedLambdaEventOfEnvs

run_cmd do
  let env ← getEnv
  for n in eventNames ++ u1Names ++ [slot32] do
    unless (env.find? n).isSome do throwError m!"target missing: {n}"
  let cl := reachSet env eventNames
  for u in u1Names do
    if cl.contains u then throwError m!"event reaches U1 name {u}"
  if cl.contains slot32 then throwError m!"event reaches the 32nd's slot {slot32}"
  -- positive controls
  let pc := reachSet env [`Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate.formRCertificateGates]
  unless pc.contains u1Names[0]! do throwError "positive control: formRCertificateGates does not reach topPin"
  let pd := reachSet env
    [`Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.decodedLambdaEventOf]
  unless pd.contains slot32 do throwError "positive control: decodedLambdaEventOf does not reach decodedLambdaEventOfEnvs"
  logInfo m!"u1_overlap: the event's {eventNames.length} constants reach {cl.size} constants, none of U1's four names and not the 32nd's slot; both positive controls pass"

run_cmd do
  let env ← getEnv
  let pinned := `Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
  let pw := `Nock.NockVMROM.Thm54.OptimizedStrictPackage.pricedWalkWork
  let wl := `Nock.NockVMROM.Thm54.ProductionP8Containment.workload
  let hpfe := `Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedHostileProductionFailureEvent
  let some idx := env.getModuleIdxFor? `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.optimizedFailureEvent
    | throwError "pinned module index missing"
  let _ := pinned
  let mut namesPW : Array Name := #[]
  let mut namesWL : Array Name := #[]
  let mut namesHPFE : Array Name := #[]
  let mut unfolders : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n != some idx then continue
    if n.isInternal then continue
    let mut cs := ci.type.getUsedConstants
    match ci.value? (allowOpaque := true) with
    | some v => cs := cs ++ v.getUsedConstants
    | none => pure ()
    if cs.contains pw then namesPW := namesPW.push n
    if cs.contains wl then namesWL := namesWL.push n
    if cs.contains hpfe then namesHPFE := namesHPFE.push n
    if cs.any (fun c => (pw.isPrefixOf c ∧ c != pw) ∨ (wl.isPrefixOf c ∧ c != wl)) then
      unfolders := unfolders.push n
  unless unfolders.isEmpty do throwError m!"pinned proofs unfold pricedWalkWork/workload: {unfolders}"
  unless namesHPFE.size ≥ 3 do throwError m!"expected the slot sites to name the hostile event: {namesHPFE}"
  logInfo m!"rule4g_i: pinned declarations naming pricedWalkWork: {namesPW.size} {namesPW}; naming workload: {namesWL.size}; naming OptimizedHostileProductionFailureEvent: {namesHPFE}; unfolding either value: 0"

end Nock.RedTeam.Batch819

#print axioms Nock.RedTeam.Batch819.event_columns_round_zero
#print axioms Nock.RedTeam.Batch742.reqPairEvent_preZReads
#print axioms Nock.RedTeam.Batch796.reqPairEvent_preZReads_both
