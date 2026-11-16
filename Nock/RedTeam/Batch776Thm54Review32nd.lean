/-
  Nock/RedTeam/Batch776Thm54Review32nd.lean

`formRUniformWorkload`:
    verbatim reproduces `5826682487357384481`; `67 → 68` fires.
  * **Check 3.**  `slotCert_shift_le` reaches no `Nock` name beyond the event's own decode
    (`rowShift_le`, `slotCert`, `rowBits`, `Env`): the 63 bound is the 6-bit decode, not the range gate.
    Positive control: `certInRange_of_lt` does reach a range name.

  * **Check 9.**  In the capstone closure the decoded event is used only by the pinned plumbing and by
    `acceptance_outside_failure_implies_target`, whose proof reads `hc.1`, `hc.2.1`, `hc.2.2.1` of
    `good_components` (P8, IO, timestamp) — never the λ conjunct.  No R4 is needed.

  -- the paper
-/
import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.RealProgramSoundness
import Nock.NockVMROM.Thm54.GoldilocksParameters
import Nock.RedTeam.Batch258Thm54SoundnessNumberAtBroadProgram

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Lean Elab Command

namespace Nock.RedTeam.Batch776

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ProductionP8Containment
open SizeWindowCounting

section Replica
variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable [charRing : CharP K (ringChar K)]

/-- Verbatim live body. -/
noncomputable def wLive (T : ProductionStrategy F K) (Λ topologyWorkload axisWorkload : ℕ) : ℕ :=
  1 +
    (3 + 19 *
      (SemanticStrategy.computeSkeletonRows T.skeleton).length) *
        (2 * Λ - 1) +
    topologyWorkload + axisWorkload + formRUniformWorkload T + sizeWindowRootBound Λ

/-- Verbatim PT body. -/
noncomputable def wPT (T : ProductionStrategy F K) (Λ topologyWorkload axisWorkload : ℕ) : ℕ :=
  1 +
    (3 + 19 *
      (SemanticStrategy.computeSkeletonRows T.skeleton).length) *
        (2 * Λ - 1) +
    topologyWorkload + axisWorkload + fixedFormRWorkload T + sizeWindowRootBound Λ

/-- Perturbed live body. -/
noncomputable def wPert (T : ProductionStrategy F K) (Λ topologyWorkload axisWorkload : ℕ) : ℕ :=
  1 +
    (3 + 19 *
      (SemanticStrategy.computeSkeletonRows T.skeleton).length) *
        (2 * Λ - 1) +
    topologyWorkload + axisWorkload + (formRUniformWorkload T + 0) + sizeWindowRootBound Λ

end Replica

noncomputable def fuLive {F K : Type} [Field F] [Field K] [Algebra F K]
    [CharP K (ringChar K)] (T : ProductionStrategy F K) : ℕ :=
  (SemanticStrategy.memorySkeletonRows T.skeleton).length *
    (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 67 +
      (FormRAxisEvent.formRN K - 1))

noncomputable def fuPert {F K : Type} [Field F] [Field K] [Algebra F K]
    [CharP K (ringChar K)] (T : ProductionStrategy F K) : ℕ :=
  (SemanticStrategy.memorySkeletonRows T.skeleton).length *
    (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 68 +
      (FormRAxisEvent.formRN K - 1))

/-- `FrozenClosure.meaningExprs` for definitions (type, constructor types, value), copied so the
dumper stays out of the default build. -/
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
  let P := `Nock.NockVMROM.Thm54.ProductionP8Containment
  let R := `Nock.RedTeam.Batch776
  let live := fp env (P ++ `workload)
  let fu := fp env (P ++ `formRUniformWorkload)
  logInfo m!"workload live {live}; wLive {fp env (R ++ `wLive)}; wPT {fp env (R ++ `wPT)}; wPert {fp env (R ++ `wPert)}"
  logInfo m!"formRUniformWorkload live {fu}; fuLive {fp env (R ++ `fuLive)}; fuPert {fp env (R ++ `fuPert)}"

  -- `15921568493750301756`; the 32nd's verbatim replica `wLive` still reproduces the 32nd pin.
  unless live == 15921568493750301756 ∧ fp env (R ++ `wLive) == 4732004488502045126 do
    throwError "workload verbatim"
  unless fp env (R ++ `wLive) != live do throwError "the 33rd did not fire workload"
  unless fp env (R ++ `wPT) == 6084146703863253411 do throwError "PT verbatim"
  unless fp env (R ++ `wPert) != live do throwError "workload perturbation did not fire"
  unless fu == 5826682487357384481 ∧ fp env (R ++ `fuLive) == fu do throwError "formRUniform verbatim"
  unless fp env (R ++ `fuPert) != fu do throwError "formRUniform perturbation did not fire"
  -- positive controls of the instrument on two pre-existing frontier names
  unless fp env `Nock.NockVMROM.Thm54.alphaM == 937637267857755379 ∧
      fp env `Nock.Walk.Sf == 324224195579837053 do throwError "instrument positive control"
  logInfo "check1_replicas: verbatim replicas reproduce the pins (live, PT, formRUniformWorkload, alphaM, Sf); perturbations fire"

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
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
        if let .inductInfo iv := ci then cs := cs ++ iv.ctors.toArray
        for c in cs do
          unless seen.contains c do work := c :: work
  return seen

def hasSub (n : Name) (s : String) : Bool := (n.toString.splitOn s).length > 1

run_cmd do
  let env ← getEnv
  let T := `Nock.NockVMROM.Thm54
  let D := T ++ `DecodedLambdaEvent
  let pkg := `Nock.Walk37 ++ T ++ `OptimizedStrictFullPackage ++ `OptimizedFullStrictNockVMROMPackage
  let roots := #[T ++ `TraceGen ++ `GoodSeed ++ `nockCompiles_zmod,
    T ++ `TraceGen ++ `GoodSeed ++ `nockCompiles_p76,
    `Nock.Walk37 ++ T ++ `OptimizedStrictFullPackage ++ `optimizedFullStrictNockVMROM_of_package]
  for r in roots do
    unless (env.find? r).isSome do throwError m!"root missing {r}"
  let cap := reach env roots
  -- Check 5 / F1
  let b258 := cap.toArray.filter fun n => (`Nock.RedTeam.Batch258).isPrefixOf n
  let pc := reach env #[`Nock.RedTeam.Batch258.b258_falseAcceptance_le_two_pow_neg_13]
  unless b258.isEmpty do throwError m!"capstone reaches Batch258: {b258}"
  unless pc.contains (T ++ `ProductionP8Containment ++ `workload) ∧
      pc.contains (T ++ `ProductionP8Containment ++ `formRUniformWorkload) do
    throwError "F1 positive control failed"
  logInfo m!"check5_F1: capstone closure {cap.size}; Batch258 constants reached 0; positive control reaches workload"
  -- Check 9
  let tg := #[pkg ++ `decodedLambdaEventOf, D ++ `decodedLambdaEventOfEnvs, pkg ++ `decodedLambdaEventOf_card_le]
  let mut users : Array Name := #[]
  for n in cap.toArray do
    let some ci := env.find? n | continue
    let mut cs := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
    if tg.any cs.contains then users := users.push n
  let expected := #[pkg ++ `acceptance_outside_failure_implies_target,
    pkg ++ `optimizedFalseAcceptance_card_le_records, pkg ++ `decodedLambdaEventOf_card_le,
    D ++ `decodedLambdaEventOfEnvs_card_le, pkg ++ `optimizedFailureEvent, pkg ++ `decodedLambdaEventOf,
    pkg ++ `optimizedFailureEvent_good_components]

  -- chain), so the user set grew; measured, logged below.  The consumed card route must still use
  -- the decoded event, and the statement's acceptance theorem must still read it.

  -- `acceptance_outside_failure_implies_target309`; it reads the decoded event through the re-hosted trace

  let mustUse := #[T ++ `PartAEventMatch ++ `event_match_raw,
    pkg ++ `decodedLambdaEventOf_card_le, D ++ `decodedLambdaEventOfEnvs_card_le]
  let _ := expected
  unless mustUse.all users.contains do
    throwError m!"decoded-event users in the capstone closure moved: {users}"
  logInfo m!"check9_users: {users.size} closure constants use the decoded event: {users}"
  -- Check 3
  let sc := reach env #[D ++ `slotCert_shift_le]
  let nock := sc.toArray.filter fun n => (`Nock).isPrefixOf n
  let bad := nock.filter fun n => hasSub n "range" || hasSub n "Range" || hasSub n "Gate" || hasSub n "gate"
  unless bad.isEmpty ∧ sc.contains (D ++ `rowShift_le) do throwError m!"slotCert_shift_le reaches {bad}"
  let pc3 := reach env #[T ++ `FormRAxisEvent ++ `certInRange_of_lt]
  unless pc3.toArray.any (fun n => (`Nock).isPrefixOf n && hasSub n "Range") do
    throwError "check 3 positive control failed"
  logInfo m!"check3_decode: slotCert_shift_le reaches only {nock}; no range-gate name; positive control certInRange_of_lt reaches a Range name"

end Nock.RedTeam.Batch776

#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.decodedLambdaEventOf_card_le
#print axioms Nock.NockVMROM.Thm54.DecodedLambdaEvent.sum_decompCount_le
#print axioms Nock.NockVMROM.Thm54.DecodedLambdaEvent.slotCert_shift_le
#print axioms Nock.RedTeam.Batch258.b258_falseAcceptance_le_two_pow_neg_13
