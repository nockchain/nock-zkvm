/-
  Nock/RedTeam/Batch666Thm54ThirtyFirstPregreenlight.lean

  * The guarded
    clause `∃ k ≤ E', coeff k ≠ 0` is required, as in the thirtieth.
  * **Q7 — the slot count.**  The IO and `intermediate` record RLCs are `Walk.rlc γ v = Σ γ^k v_k`
    over `m` slots with per-pair collision bound `m − 1` (`IORLCCollisionEvent_card_le`), and
    `hostileTotalWork` hard-codes `m = 9` (`8·(3N+M)² + 2(3N+M)` and `8·(2M)² + 2(2M)`).  With
    `m = 10` the factor is `9`: doubled numerator `453S² + 404S + 28` (`numerator_ten`: the thirtieth's
    `413S² + 404S + 28` plus `2·((4S)² + (2S)²) = 40S²`), and `(453·2^{62} + 404·2^{31} + 28)·2^{122} <
    2|𝕂|`, `(453·2^{64} + 404·2^{32} + 28)·2^{120} < 2|𝕂|` (`figure_122_ten`, `figure_120_ten`): 122/120
    HOLD; 123's proof reads `ioFailureUnionBound 9` for the inter term and must be re-proved at `10`
    (`inter_ten_negligible`: the extra `2^{64}/|𝕂|^2 < 2^{−127}`).
-/
import Lean
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.FormRAxisEvent
import Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Lean Elab Command

namespace Nock.RedTeam.Batch666

open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.FormRAxisEvent Nock.RedTeam.Batch575
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Polynomial
open scoped Classical

noncomputable section

/-! ## Q1 -/

section Guard
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- An atom-rooted decoded tree (a lone `halt`) has the zero Form R polynomial. -/
theorem decoded_halt_poly_zero (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) :
    formRCounts n mm cc (MTree.halt : MTree K) = 0 := by
  simp [formRCounts]

/-- A zero polynomial's root set is every `(α, λ)` pair. -/
theorem rootBad_zero_univ (E : ℕ) :
    formRRootBad (0 : Polynomial (Polynomial K)) E = (Finset.univ : Finset (K × K)) := by
  ext p
  simp [formRRootBad, formREnvelope, Nock.RedTeam.Batch556.F]

/-- Hence an unguarded hostile-decoded event is `univ` on a forest with an atom-rooted tree: the
event must carry `formRGuard` per root, as the thirtieth does. -/
theorem unguarded_is_univ (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) (E : ℕ) :
    formRRootBad (formRCounts n mm cc (MTree.halt : MTree K)) E = Finset.univ := by
  rw [decoded_halt_poly_zero, rootBad_zero_univ]

end Guard

/-! ## Q7 -/

theorem numerator_ten (S : ℕ) :
    413 * (S * S) + 404 * S + 28 + 2 * ((4 * S) * (4 * S) + (2 * S) * (2 * S)) =
      453 * (S * S) + 404 * S + 28 := by ring

theorem figure_122_ten : (453 * 2 ^ 62 + 404 * 2 ^ 31 + 28) * 2 ^ 122 < 2 * cardKGold := by
  norm_num [cardKGold]

theorem figure_120_ten : (453 * 2 ^ 64 + 404 * 2 ^ 32 + 28) * 2 ^ 120 < 2 * cardKGold := by
  norm_num [cardKGold]

/-- The inter term's growth at the paper configuration, `(9 − 8)·(2^{32})² = 2^{64}` over `|𝕂|²`,
is below `2^{−127}`: 123 survives, with a re-proof. -/
theorem inter_ten_negligible : ((2 : ℚ) ^ 64) / ((cardKGold : ℚ) ^ 2) < 1 / (2 : ℚ) ^ 127 := by
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  norm_num [cardKGold]

/-- `IORLCCollisionEvent_card_le`'s factor is `m − 1`: `8` at nine slots, `9` at ten. -/
theorem rlc_factor : (9 : ℕ) - 1 = 8 ∧ (10 : ℕ) - 1 = 9 := by norm_num

end

/-! ## Q2 — the import graph -/

def pinnedMod : Name := `Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage

partial def closureOf (env : Environment) (root : Name) : Std.HashSet Name := Id.run do
  let mods := env.header.moduleNames
  let data := env.header.moduleData
  let mut idx : Std.HashMap Name Nat := {}
  for i in [0:mods.size] do idx := idx.insert mods[i]! i
  let mut seen : Std.HashSet Name := {}
  let mut work := [root]
  while true do
    match work with
    | [] => break
    | m :: rest =>
      work := rest
      if seen.contains m then continue
      seen := seen.insert m
      match idx[m]? with
      | some i => for imp in data[i]!.imports do work := imp.module :: work
      | none => pure ()
  return seen

run_cmd do
  let env ← getEnv
  let pin := closureOf env pinnedMod
  unless pin.contains `Nock.NockVMROM.Thm54.HostileSkeletonDecoding do
    throwError "HostileSkeletonDecoding expected below the pinned file since the 33rd move"
  let above : Array Name := #[`Nock.NockVMROM.Thm54.ExecOfTraces,
    `Nock.NockVMROM.Thm54.MemoryHaltAtomDecode, `Nock.NockVMROM.Thm54.OptimizedHostileTimestamps,
    `Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator, `Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator]
  let below : Array Name := #[`Nock.NockVMROM.Thm54.HostileRecordLists, `Nock.NockVMROM.Thm54.FormRCore,
    `Nock.NockVMROM.Thm54.FormRAxisEvent, `Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents,
    `Nock.NockVMROM.Thm54.FiniteFieldIOSoundness]
  for m in above do
    if pin.contains m then throwError m!"{m} is below the pinned file (expected above)"
  for m in below do
    unless pin.contains m do throwError m!"{m} is above the pinned file (expected below)"
  let ht := closureOf env `Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
  unless ht.contains pinnedMod do throwError "OptimizedHostileTimestamps does not reach the pinned file?"
  logInfo m!"Q2: the named decoders and hostile_LIO' sit ABOVE the pinned file; \
    HostileRecordLists / FormRCore / FormRAxisEvent / WalkForestPrefixAlphaEvents / FiniteFieldIOSoundness below; \
    OptimizedHostileTimestamps reaches the pinned file ({ht.size} modules)"

end Nock.RedTeam.Batch666
