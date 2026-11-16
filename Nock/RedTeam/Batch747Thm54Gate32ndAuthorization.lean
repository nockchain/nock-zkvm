/-
  Nock/RedTeam/Batch747Thm54Gate32ndAuthorization.lean

* **Check 3 (verify's `a`).**  `formRCounts` ignores the verify node's `K` argument on every tree
    (`formRCounts_verify_ignores_a`, rfl), so writing `0` there loses nothing the event reads.
  * **Check 8 (the slot→certificate map).**  The deployed request records read the row's certificate
    in exactly two places: slot `1` (base `75`) under selector `0` (OP0) and slot `2` (base `83`) under
    selector `9`; slot `0` (base `67`) is the constant `(λ, 1 + λ)`; slot `2` under selector `6` is
    constant (`sampledSlotT_structure`, `sampledSlotC_structure`, rfl).  The earlier `slotCert` gave
    every slot the row's certificate — fine for the card bound, WRONG for the event R4 must match.
    The text must pin the map to this structure.
  * **Check 5 / 13 (figures).**  The figure theorems reach none of `workload`, `fixedFormRWorkload`,
    `formRLambdaEvent` (`figures_avoid_workload`); the joint doubled numerator after the 32nd (no
    coefficient change) and H1.3 route B (`+4S²`) is `457S² + 404S + 28`: `122` at `2^31`, `120` at
    `2^32` hold (`joint_122`, `joint_120`); margin to the next failing coefficient `512` is `55S²`.
  * **Check 4 (`workload` replica).**  A verbatim replica reproduces the pin `6084146703863253411`;
    the (b)-modified replica (summand swapped for a uniform `M·(3N+67+(n−1))`) fires.
  * **Check 9 (route B's exclusions vs the swap).**  `Batch742.ver_reqIdx_injective` and
    `request_named_by_row` are not on this tree (branch `redteam/h13-route-b`); their stated route is
    `hostile_LIO'` + `expOf_injective` + `IO.LIO` nodup — all from the IO/timestamp/inter-pole
    components of `hgood`, which the 32nd's swap of the λ-slot does not touch
    (`good_components_keep_io`: the IO exclusions are conjuncts independent of the last slot).

  -- the paper
-/
import Lean
import Nock.NockVMROM.Thm54.FormRAxisEvent
import Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.RealProgramSoundness
import Nock.NockVMROM.Thm54.GoldilocksParameters

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Lean Elab Command

namespace Nock.RedTeam.Batch747

open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54 Nock.RedTeam.Batch575
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.Reified

noncomputable section

/-! ## Check 3 -/

theorem formRCounts_verify_ignores_a {K : Type} [Field K] (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool)
    (e : ℕ) (a a' : K) (t : MTree K) :
    formRCounts n mm cc (.verify e a t) = formRCounts n mm cc (.verify e a' t) := rfl

/-! ## Check 8 — the slot→certificate structure of the deployed records -/

theorem sampledSlotT_structure (kind : VarKind) :
    sampledSlotT kind 67 = sampledLam ∧
    sampledSlotT kind 75 = .Add (.Mul (.Var kind 0) (certTVar kind)) (.Mul (sampledGSel kind) sampledLam) ∧
    sampledSlotT kind 83 = .Add (.Mul (.Var kind 6) sampledLam) (.Mul (.Var kind 9) (certTVar kind)) :=
  ⟨rfl, rfl, rfl⟩

theorem sampledSlotC_structure (kind : VarKind) :
    sampledSlotC kind 67 = .Add (lamPowVar 0) (lamPowVar 1) ∧
    sampledSlotC kind 75 = .Add (.Mul (.Var kind 0) (sampledCprime kind)) (.Mul (sampledGSel kind) (lamPowVar 0)) ∧
    sampledSlotC kind 83 = .Add (.Mul (.Var kind 6) (lamPowVar 0)) (.Mul (.Var kind 9) (sampledCprime kind)) :=
  ⟨rfl, rfl, rfl⟩

/-! ## Check 13 — joint figures -/

theorem joint_numerator (S : ℕ) :
    453 * (S * S) + 404 * S + 28 + 4 * (S * S) = 457 * (S * S) + 404 * S + 28 := by ring

theorem joint_122 : (457 * 2 ^ 62 + 404 * 2 ^ 31 + 28) * 2 ^ 122 < 2 * cardKGold := by
  norm_num [cardKGold]

theorem joint_120 : (457 * 2 ^ 64 + 404 * 2 ^ 32 + 28) * 2 ^ 120 < 2 * cardKGold := by
  norm_num [cardKGold]

/-- The first coefficient at which `2^31`/`2^122` fails: `512`. -/
theorem margin_512 : ¬ ((512 * 2 ^ 62) * 2 ^ 122 < 2 * cardKGold) := by
  norm_num [cardKGold]

end

/-! ## Check 5 — the figures do not read the workload names; Check 9 — the IO exclusions -/

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

run_cmd do
  let env ← getEnv
  let figs := #[``Nock.NockVMROM.Thm54.RealProgramSoundness.hostile_soundness_formR_at_two_pow_31,
    ``Nock.NockVMROM.Thm54.RealProgramSoundness.hostile_soundness_formR_at_two_pow_32,
    ``Nock.NockVMROM.Thm54.GoldilocksParameters.hostile_soundness_at_paper_configuration]
  let cl := reach env figs
  for n in [``Nock.NockVMROM.Thm54.ProductionP8Containment.workload,
      ``Nock.NockVMROM.Thm54.ProductionP8Containment.fixedFormRWorkload,
      ``Nock.NockVMROM.Thm54.FormRAxisEvent.formRLambdaEvent] do
    if cl.contains n then throwError m!"figure theorems reach {n}"
  logInfo m!"figures_avoid_workload: {cl.size} constants; none of workload/fixedFormRWorkload/formRLambdaEvent"
  -- the IO exclusions in good_components are independent of the λ-slot: the components theorem's TYPE
  -- names the IO/timestamp/inter events and the λ event as separate conjuncts
  let some ci := env.find? ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.optimizedFailureEvent_good_components
    | throwError "optimizedFailureEvent_good_components missing"
  let used := ci.type.getUsedConstants
  -- H1.5b Part 2a: the IO exclusion is the family IO event `famIOEventOf` (a pinned abbrev over
  -- `FiniteIO.IOFailureEvent`).
  unless used.contains ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.famIOEventOf ∧
      used.contains ``Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.TimestampCollisionEvent ∧
      -- the λ exclusion's event: `formRLambdaEvent` at the gate (PT); since the thirty-second move
      -- the pinned decoded event `decodedLambdaEventOf`
      used.contains ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.decodedLambdaEventOf do
    throwError "good_components does not expose the IO/timestamp/λ exclusions as separate conjuncts"
  logInfo "good_components_keep_io: IO, timestamp and λ exclusions are separate conjuncts of good_components"

/-! ## Check 4 — `workload` replica -/

section Replica
open Nock.NockVMROM.Thm54.ProductionP8Containment Nock.NockVMROM.Thm54.SizeWindowCounting
variable {F K : Type} [Field F] [Field K] [Algebra F K] [CharP K (ringChar K)]

/-- Verbatim replica of `workload` (binders as in the source). -/
noncomputable def workloadA (T : ProductionStrategy F K) (Λ topologyWorkload axisWorkload : ℕ) : ℕ :=
  1 +
    (3 + 19 *
      (SemanticStrategy.computeSkeletonRows T.skeleton).length) *
        (2 * Λ - 1) +
    topologyWorkload + axisWorkload + fixedFormRWorkload T + sizeWindowRootBound Λ

noncomputable def formRUniformWorkloadR (T : ProductionStrategy F K) : ℕ :=
  (SemanticStrategy.memorySkeletonRows T.skeleton).length *
    (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 67 + (FormRAxisEvent.formRN K - 1))

/-- The (b)-modified replica. -/
noncomputable def workloadB (T : ProductionStrategy F K) (Λ topologyWorkload axisWorkload : ℕ) : ℕ :=
  1 +
    (3 + 19 *
      (SemanticStrategy.computeSkeletonRows T.skeleton).length) *
        (2 * Λ - 1) +
    topologyWorkload + axisWorkload + formRUniformWorkloadR T + sizeWindowRootBound Λ

end Replica

def meaningExprs (env : Environment) (n : Name) : Array Lean.Expr :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let base := #[ci.type]
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
  let live := fp env ``Nock.NockVMROM.Thm54.ProductionP8Containment.workload
  let a := fp env ``Nock.RedTeam.Batch747.workloadA
  let b := fp env ``Nock.RedTeam.Batch747.workloadB
  logInfo m!"workload live {live}; replica A {a}; replica B {b}"
  -- At the gate (PT) `live` was the pin `6084146703863253411` and replica A reproduced it.  Since the
  -- thirty-second move `workload` sums `formRUniformWorkload`: the

  -- value, and neither replica equals it (B names this file's `formRUniformWorkloadR`).
  unless a == 6084146703863253411 do throwError "verbatim replica does not reproduce the PT pin"

  -- `workload` sums `reqPairWorkload` too, so live moved `5538245203494781706 → 15921568493750301756`.
  unless live == 15921568493750301756 do throwError m!"live workload fingerprint {live} ≠ 33rd pin"
  unless a != live do throwError "the move did not fire workload"
  unless b != live do throwError "the (b)-modified replica does not fire"

end Nock.RedTeam.Batch747
