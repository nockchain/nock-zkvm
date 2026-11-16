/-
  Nock/RedTeam/Batch1001Thm54HonestPathValidityReach.lean

  Nothing consumes this.

  * **(A) absence.**  From the honest path-validity theorems and component 11
    (`Batch999.decoded_eq_axisTree`, `honest_uniqueExponents`, `honest_formRPathValid`,
    `decodedCert_eq`, `honest_lam`; `Batch1000.honest_lam_generated`, `honest_lam_of_fill`,
    `decoded_eq_honestTemplateAxisTree`) the walk
    reaches NONE of: `optimizedFailureEvent` (so no `hgood : c ∉ optimizedFailureEvent …` premise
    can occur anywhere in the closure), the hostile failure-event structure, `r4_path_valid_at`,
    `r4_bridge_at`, `expLe_at`, `roots_zero_of_not_event`, `uniqueExponents_decoded_pkg` /
    `_at`, `decodedRootPoly_eq_zero_of_not_bad`, `Batch961.rootPoly_zero_of_lam`, the assembled
    `hgood` theorems (`Batch909.hgood_honest`, `Batch963.hgood_of_open`, `hgood_zero_built`) and
    the residual structures (`HonestEventResidual`, `HonestEventOpen`).  Moreover no constant in
    the closure has `optimizedFailureEvent` in its type.
  * **(B) positive controls.**  The same walk from `Batch824.r4_path_valid_at` reaches
    `optimizedFailureEvent` and `r4_bridge_at`; from `Batch963.hgood_zero_built` it reaches
    `optimizedFailureEvent` and `hgood_of_open`; from `Batch1000.hgood_zero_built_lam` (the consumer
    that DOES conclude `hgood`) it reaches `hgood_zero_built`; and from `Batch999.honest_lam` it
    reaches its genuine targets `decodedLambdaEventOf` and `Batch961.lam_of_rootPolys_zero`.
  Every check throws on failure, so the module builds only if all hold.
-/
import Lean
import Nock.RedTeam.Batch1000Thm54HonestLambdaGenerated
import Nock.RedTeam.Batch941Thm54LiftStrategyReach
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

open Lean

namespace Nock.RedTeam.Batch1001

def OFE : Name :=
  `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.optimizedFailureEvent

def roots : List Name := [
  `Nock.RedTeam.Batch999.decoded_eq_axisTree,
  `Nock.RedTeam.Batch999.honest_uniqueExponents,
  `Nock.RedTeam.Batch999.honest_formRPathValid,
  `Nock.RedTeam.Batch999.decodedCert_eq,
  `Nock.RedTeam.Batch999.honest_lam,
  `Nock.RedTeam.Batch1000.honest_lam_generated,
  `Nock.RedTeam.Batch1000.honest_lam_of_fill,
  `Nock.RedTeam.Batch1000.decoded_eq_honestTemplateAxisTree]

def forbidden : List Name := [
  OFE,
  `Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedHostileProductionFailureEvent,
  `Nock.RedTeam.Batch824.r4_path_valid_at,
  `Nock.RedTeam.Batch824.r4_bridge_at,
  `Nock.RedTeam.Batch824.r4_bridge_at_current,
  `Nock.RedTeam.Batch824.expLe_at,
  `Nock.NockVMROM.Thm54.FormRBridge.roots_zero_of_not_event,
  `Nock.NockVMROM.Thm54.UniqueExponentsBridge.uniqueExponents_decoded_pkg,
  `Nock.NockVMROM.Thm54.UniqueExponentsBridge.uniqueExponents_decoded_at,
  `Nock.NockVMROM.Thm54.FormRBridge.decodedRootPoly_eq_zero_of_not_bad,
  `Nock.RedTeam.Batch961.rootPoly_zero_of_lam,
  `Nock.RedTeam.Batch909.hgood_honest,
  `Nock.RedTeam.Batch909.HonestEventResidual,
  `Nock.RedTeam.Batch963.hgood_of_open,
  `Nock.RedTeam.Batch963.hgood_zero_built,
  `Nock.RedTeam.Batch963.HonestEventOpen]

end Nock.RedTeam.Batch1001

open Nock.RedTeam.Batch941 Nock.RedTeam.Batch1001 in
run_cmd do
  let env ← getEnv
  -- every name must exist, or a typo would make an absence vacuous
  for n in roots ++ forbidden do
    unless env.contains n do throwError s!"unknown constant {n}"
  -- (A) absence
  let s := constReach env roots {}
  for f in forbidden do
    if s.contains f then throwError s!"(A) FORBIDDEN constant reached: {f}"
  let mut hits : Array Name := #[]
  for n in s.toList do
    match env.find? n with
    | some ci => if ci.type.getUsedConstants.contains OFE then hits := hits.push n
    | none => pure ()
  unless hits.isEmpty do throwError s!"(A) constants with optimizedFailureEvent in their type: {hits}"
  logInfo s!"(A) closure of the honest theorems: {s.size} constants; forbidden reached: 0 of {forbidden.length}; types mentioning optimizedFailureEvent: 0"
  -- (B) positive controls
  let pc1 := constReach env [`Nock.RedTeam.Batch824.r4_path_valid_at] {}
  unless pc1.contains OFE && pc1.contains `Nock.RedTeam.Batch824.r4_bridge_at do
    throwError "(B) positive control FAILED at r4_path_valid_at"
  logInfo s!"(B) r4_path_valid_at: {pc1.size} constants; optimizedFailureEvent and r4_bridge_at PRESENT"
  let pc2 := constReach env [`Nock.RedTeam.Batch963.hgood_zero_built] {}
  unless pc2.contains OFE && pc2.contains `Nock.RedTeam.Batch963.hgood_of_open do
    throwError "(B) positive control FAILED at hgood_zero_built"
  logInfo s!"(B) hgood_zero_built: {pc2.size} constants; optimizedFailureEvent and hgood_of_open PRESENT"
  let pc3 := constReach env [`Nock.RedTeam.Batch1000.hgood_zero_built_lam] {}
  unless pc3.contains `Nock.RedTeam.Batch963.hgood_zero_built && pc3.contains OFE do
    throwError "(B) positive control FAILED at hgood_zero_built_lam"
  logInfo s!"(B) hgood_zero_built_lam: {pc3.size} constants; hgood_zero_built PRESENT"
  let pc4 := constReach env [`Nock.RedTeam.Batch999.honest_lam] {}
  unless pc4.contains
      `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.decodedLambdaEventOf &&
      pc4.contains `Nock.RedTeam.Batch961.lam_of_rootPolys_zero do
    throwError "(B) positive control FAILED at honest_lam"
  logInfo s!"(B) honest_lam: {pc4.size} constants; decodedLambdaEventOf and lam_of_rootPolys_zero PRESENT"
