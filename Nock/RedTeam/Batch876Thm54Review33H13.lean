/-
  Nock/RedTeam/Batch876Thm54Review33H13.lean

The nine new/moved pins are read back.
  * **B.** Reach from the three capstone roots: the consumed path (`reqPairEventOf`,
    `reqPairEventOf_card_le`, `reqPairWorkload`, `reqPairEventOfEnvs(_card_le)`, `pairBadSeeds`,
    `requestTargets`) IS reached; the three `_prePair` copies, the legacy 119-bit
    `RealProgramAxisWorkload.soundness_for_production*`, `productionWorkloadGrowth` and every
    `hpair`-carrier module are NOT.
  * **C.** `nockCompiles_zmod` 26/13, `nockCompiles_p76` 28/13.

-- the paper
-/
import Lean
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.PreZCensusCore
import Nock.NockVMROM.Thm54.RealProgramSoundness
import Nock.NockVMROM.Thm54.HostileWorkloadMajorant
import Nock.NockVMROM.Thm54.RealProgramAxisWorkload
import Nock.NockVMROM.Thm54.OptimizedStrictFullPackageConcrete
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.RedTeam.Batch818Thm54H13ConsumeFigures

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

open Lean Elab Command

namespace Nock.RedTeam.Batch876

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.NockVMROM.Thm54.GoldilocksParameters

/-! ## A. Own negative control: `pairBadSeeds` -/

noncomputable section Replica
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Verbatim `pairBadSeeds`. -/
def pbsLive (Λ : ℕ) (pairs : List (Noun × Noun)) : Finset K :=
  (guardedCensus Λ pairs).badSeeds (K := K)

/-- Perturbation: census at window `Λ + 1`. -/
def pbsPert (Λ : ℕ) (pairs : List (Noun × Noun)) : Finset K :=
  (guardedCensus (Λ + 1) pairs).badSeeds (K := K)

end Replica

def meaningExprs (env : Environment) (n : Name) : Array Lean.Expr :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let ctorTys : Array Lean.Expr := match ci with
      | .inductInfo iv => iv.ctors.foldl (init := #[]) fun acc c =>
          match env.find? c with
          | some cci => acc.push cci.type
          | none => acc
      | _ => #[]
    let base := #[ci.type] ++ ctorTys
    match ci with
    | .thmInfo _ => base
    | .axiomInfo _ => base
    | _ => match ci.value? (allowOpaque := true) with
           | some v => base.push v
           | none => base

def fp (env : Environment) (n : Name) : UInt64 :=
  (meaningExprs env n).foldl (init := (17 : UInt64)) fun acc e => mixHash acc e.hash

run_cmd do
  let env ← getEnv
  let PS := `Nock.NockVMROM.Thm54.PreSeedCensus
  let R := `Nock.RedTeam.Batch876
  let live := fp env (PS ++ `pairBadSeeds)
  logInfo m!"pairBadSeeds live {live}; pbsLive {fp env (R ++ `pbsLive)}; pbsPert {fp env (R ++ `pbsPert)}"
  unless live == 8523380660461741701 do throwError "pairBadSeeds pin moved"
  unless fp env (R ++ `pbsLive) == live do throwError "verbatim replica does not reproduce the pin"
  unless fp env (R ++ `pbsPert) != live do throwError "own control did not fire"
  -- byte-pin gap: `reqPairEventOfEnvs` names `pairBadSeeds` as a const and does not carry its body
  let rs := (meaningExprs env (PS ++ `reqPairEventOfEnvs)).foldl (init := ({} : NameSet))
    fun acc e => e.getUsedConstants.foldl (fun a c => a.insert c) acc
  unless rs.contains (PS ++ `pairBadSeeds) do throwError "reqPairEventOfEnvs does not name pairBadSeeds"
  if rs.contains ``ComparisonCensus.badSeeds then throwError "reqPairEventOfEnvs carries pairBadSeeds' body"
  -- the other new pins, read back
  for (n, h) in [(PS ++ `guardedPairs, 3423436599348089555), (PS ++ `reqTgtOfEnvs, 3312615697292535736),
      (PS ++ `reqPairEventOfEnvs, 6264743203847467740), (PS ++ `requestTargets, 2260074138106044861),
      (`Nock.NockVMROM.Thm54.ProductionP8Containment.reqPairWorkload, 16685327008963352002),
      (`Nock.NockVMROM.Thm54.ProductionP8Containment.ProductionStrategy.skeleton, 2896913345513872695),
      (`Nock.NockVMROM.Thm54.ProductionP8Containment.workload, 15921568493750301756),

      (`Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedHostileProductionFailureEvent, 8307282949885789412),
      (`Nock.NockVMROM.Thm54.OptimizedStrictPackage.pricedWalkWork, 18169742864994646756)] do
    unless fp env n == h do throwError m!"fingerprint of {n} = {fp env n} ≠ recorded {h}"
  logInfo "A. own control (pairBadSeeds) + nine pins read back: OK"

/-! ## B. Reach from the capstone roots -/

partial def reach (env : Environment) (roots : Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut work := roots.toList
  while true do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      unless (`Nock).isPrefixOf n do continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
        for c in cs do
          unless seen.contains c do work := c :: work
  return seen

run_cmd do
  let env ← getEnv
  let roots := #[``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod,
    ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76,
    ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package]
  let FP := `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage
  let RS := `Nock.NockVMROM.Thm54.RealProgramSoundness
  let HM := `Nock.NockVMROM.Thm54.HostileWorkloadMajorant
  let RA := `Nock.NockVMROM.Thm54.RealProgramAxisWorkload

  -- the pre-36th `reqPairEventOf` stays in Defs, unread by the statement.
  let _ := FP
  let mustReach : Array Name := #[`Nock.NockVMROM.Thm54.OptimizedFailureEventEv.reqPairEv,

    -- the landed `optimizedFalseAcceptance_card_le_records` is pinned proof infrastructure, unread.
    `Nock.NockVMROM.Thm54.PartAStaged.staged_consumed_card_le,
    `Nock.NockVMROM.Thm54.ProductionP8Containment.reqPairWorkload,
    `Nock.NockVMROM.Thm54.PreSeedCensus.reqPairEventOfEnvs,
    `Nock.NockVMROM.Thm54.PreSeedCensus.reqPairEventOfEnvs_card_le,
    `Nock.NockVMROM.Thm54.PreSeedCensus.pairBadSeeds,
    `Nock.NockVMROM.Thm54.PreSeedCensus.requestTargets]
  let mustNot : Array Name := #[RS ++ `two_hostileTotalWork_le_of_size_formR_prePair,
    RS ++ `hostileSizeWorkFormR_not_lt_cardK_prePair, HM ++ `two_hostileTotalWork_le_p8WorkHostile_prePair,
    RA ++ `soundness_for_production, RA ++ `soundness_for_production_of_axisBound,
    RA ++ `soundness_for_production_of_window, RA ++ `soundness_for_generated,
    `Nock.NockVMROM.Thm54.ProductionAsymptotic.productionWorkloadGrowth]
  let carriers : Array Name := #[`Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance,
    `Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance, `Nock.NockVMROM.Thm54.ProductionAsymptotic,
    `Nock.NockVMROM.Thm54.StrictAsymptoticSecurity, `Nock.NockVMROM.Thm54.DistinctCensusFold2,
    `Nock.NockVMROM.Thm54.IOCapstoneRedundancy, `Nock.NockVMROM.Thm54.OptimizedHostileConfiguration,
    `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageConcrete]
  for n in mustReach ++ mustNot do
    unless (env.find? n).isSome do throwError m!"missing: {n}"
  for r in roots do
    let cl := reach env #[r]
    for n in mustReach do
      unless cl.contains n do throwError m!"{r} does not reach consumed name {n}"
    for n in mustNot do
      if cl.contains n then throwError m!"{r} reaches {n}"
    let hits := cl.toArray.filter fun n =>
      match env.getModuleFor? n with
      | some m => carriers.contains m
      | none => false
    unless hits.isEmpty do throwError m!"carrier constants reached from {r}: {hits}"
    logInfo m!"{r}: closure {cl.size}; consumed path reached; _prePair / legacy / carriers not reached"

/-! ## C. 26/13 and 28/13 -/

partial def binderCount : Lean.Expr → ℕ
  | .forallE _ _ b _ => 1 + binderCount b
  | _ => 0


partial def explicitCount : Lean.Expr → ℕ
  | .forallE _ _ b bi => (if bi == .default then 1 else 0) + explicitCount b
  | _ => 0

run_cmd do
  let env ← getEnv
  for (n, hb, hc) in [(``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod, 27, 14),
      -- S2: + the explicit walk coin `αW` (both +1/+1).
      -- H1.5b Part 2a: p76 gained `hrows` (28/13 → 29/14).
      -- the 36th: p76 gained `hFprime` (29/14 → 30/15).
      (``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76, 31, 16)] do
    let some ci := env.find? n | throwError m!"missing {n}"
    let b := binderCount ci.type
    let c := explicitCount ci.type
    logInfo m!"{n}: {b} binders / {c} explicit"
    unless b == hb ∧ c == hc do throwError m!"{n}: expected {hb}/{hc}"

/-! ## D. Arithmetic -/

-- 122 at 2^31, 120 at 2^32, numerator 457S² + 404S + 28 (row budget)
example : (457 * (2 ^ 31 * 2 ^ 31) + 404 * 2 ^ 31 + 28) * 2 ^ 122 < 2 * cardKGold := by norm_num
example : (457 * (2 ^ 32 * 2 ^ 32) + 404 * 2 ^ 32 + 28) * 2 ^ 120 < 2 * cardKGold := by norm_num
-- tight: 123 at 2^31 / 121 at 2^32 do not follow from this numerator
example : ¬ ((457 * (2 ^ 31 * 2 ^ 31) + 404 * 2 ^ 31 + 28) * 2 ^ 123 < 2 * cardKGold) := by norm_num
example : ¬ ((457 * (2 ^ 32 * 2 ^ 32) + 404 * 2 ^ 32 + 28) * 2 ^ 121 < 2 * cardKGold) := by norm_num
-- hostile majorant 457S² + 150S + 288
example : (457 * (2 ^ 31 * 2 ^ 31) + 150 * 2 ^ 31 + 288) * 2 ^ 122 < 2 * cardKGold := by norm_num
-- the pair summand at the paper configuration: M(2(M⊔Λ)−1) at 2^31/2^31 ≤ 2^63
example : 2 ^ 31 * (2 * (2 ^ 31 ⊔ 2 ^ 31) - 1) ≤ 2 ^ 63 := by simp only [max_self]; norm_num
-- legacy 119-bit path premise `reqPairWorkload ≤ 2^64`: FALSE at full 2^32 rows, true at ≤ 2^31
example : ¬ (2 ^ 32 * (2 * (2 ^ 32 ⊔ 2 ^ 32) - 1) ≤ 2 ^ 32 * 2 ^ 32) := by simp only [max_self]; norm_num
example : 2 ^ 31 * (2 * (2 ^ 31 ⊔ 2 ^ 31) - 1) ≤ 2 ^ 32 * 2 ^ 32 := by simp only [max_self]; norm_num

example : 227 * (2 * (227 ⊔ 22) - 1) = 102831 := by norm_num
example : (16914 + 28829 + 102831) * 2 ^ 11 ≤ 769 ^ 3 := by norm_num
example : ¬ ((16914 + 28829 + 102831) * 2 ^ 12 ≤ 769 ^ 3) := by norm_num

/-! ## E. The compiled figure theorems, their statements and axioms -/

#check @RealProgramSoundness.hostile_soundness_formR_at_two_pow_31
#check @RealProgramSoundness.hostile_soundness_formR_at_two_pow_32
#check @HostileWorkloadMajorant.hostile_soundness_for_real_programs_at_two_pow_31_majorant
#check @Nock.RedTeam.Batch818.hostile_soundness_W_at_paper_configuration
#check @OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.reqPairEventOf_card_le
#print axioms RealProgramSoundness.hostile_soundness_formR_at_two_pow_31
#print axioms RealProgramSoundness.hostile_soundness_formR_at_two_pow_32
#print axioms Nock.RedTeam.Batch818.hostile_soundness_W_at_paper_configuration
#print axioms OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.reqPairEventOf_card_le
#print axioms OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.optimizedFalseAcceptance_card_le_records
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod

end Nock.RedTeam.Batch876
