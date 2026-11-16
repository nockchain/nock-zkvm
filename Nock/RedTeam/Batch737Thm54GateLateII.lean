/-
  Nock/RedTeam/Batch737Thm54GateLateII.lean

  Notes only, no `passed`
  flip.

  * **A — the `chalVal` pin pins the honest record coin.**  `pin_forces_gamma` (generic in the
    package): the `chalVal` pin that M′'s non-vacuity receipt (`Batch728.fmemTopo_at_honest_tuple`)
    assumes forces the honest tuple's record coin `γ = c.2.1.1` — the coin `rowExpTerm` reads — to
    equal the configuration's memory-input `γ`; `pin_forces_beta_zero` likewise forces the memory
    `β` to `0`.  The compiler's configuration has `γ = β = 0` (`compiler_cfg_gamma_beta_zero`), so at
    every compiler-built package the pin either forces `γ = 0` at the honest tuple (where the
    withdrawn `hexp0` also held: `hexp0_at_honest_of_pin_cfg_gamma_zero`) or is false.  M′'s receipt
    therefore does not witness satisfiability at `γ ≠ 0`; M′'s gain is the consumer direction (no
    γ-dependent premise at an accepted `c ∉ event`).
  * **B — the receipt's two other hypotheses are generic.**  `memStateTagChar_of_package`
    (`stateTagChar` + `hchar_of_package` + injectivity of `algebraMap F K`) and
    `honest_seed_ne_zero` (`hz0_of_package` + `family_cfg`).
-/
import Lean
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedHostileConfiguration
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.RedTeam.Batch679Thm54ThirtyFirstReview
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch737

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
  Nock.NockVMROM.Thm54.OptimizedStrictPackage

/-! ## A. The `chalVal` pin pins `γ` -/

section Pin

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The `chalVal` pin forces the honest tuple's record coin to be the configuration's memory `γ`. -/
theorem pin_forces_gamma
    (h : DeployedChipFamily.memoryChalValOfTuple P.optimized.basis P.honestTuple =
      P.optimized.memoryChallenge) :
    P.honestTuple.2.1.1 =
      P.optimized.family.problem.cfg.challenges.memoryInputs.γ := by
  have hpin := P.optimized.memoryCoordinatePins.memoryChallenge ⟨2, by decide⟩
  have hslot : ∀ k : Fin 3,
      P.optimized.memoryChallenge (6 + 3 * 2 + (k : ℕ)) =
        CoordinateBasis.coord P.optimized.basis (P.honestTuple.2.1.1) k := by
    intro k
    rw [← h]
    exact DeployedChipFamily.memoryChalValOfTuple_slot P.optimized.basis P.honestTuple
      ⟨2, by decide⟩ k
  have hrec : (∑ k : Fin 3, P.optimized.memoryChallenge (6 + 3 * 2 + (k : ℕ)) •
      P.optimized.basis k) = P.honestTuple.2.1.1 := by
    simp only [hslot]
    exact CoordinateBasis.reconstruct_coord P.optimized.basis _
  rw [← hrec]
  simpa [OptimizedMemorySemanticRealization.exactMemoryRowEnv, Nock.Reified.memoryEnvFull]
    using hpin

/-- The same pin forces the configuration's memory `β` to `0` (`memoryKOfTuple` slot `1` is `0`). -/
theorem pin_forces_beta_zero
    (h : DeployedChipFamily.memoryChalValOfTuple P.optimized.basis P.honestTuple =
      P.optimized.memoryChallenge) :
    P.optimized.family.problem.cfg.challenges.memoryInputs.β = 0 := by
  have hpin := P.optimized.memoryCoordinatePins.memoryChallenge ⟨1, by decide⟩
  have hslot : ∀ k : Fin 3,
      P.optimized.memoryChallenge (6 + 3 * 1 + (k : ℕ)) =
        CoordinateBasis.coord P.optimized.basis (0 : K) k := by
    intro k
    rw [← h]
    exact DeployedChipFamily.memoryChalValOfTuple_slot P.optimized.basis P.honestTuple
      ⟨1, by decide⟩ k
  have hrec : (∑ k : Fin 3, P.optimized.memoryChallenge (6 + 3 * 1 + (k : ℕ)) •
      P.optimized.basis k) = 0 := by
    simp only [hslot]
    exact CoordinateBasis.reconstruct_coord P.optimized.basis _
  rw [← hrec]
  simpa [OptimizedMemorySemanticRealization.exactMemoryRowEnv, Nock.Reified.memoryEnvFull]
    using hpin.symm

/-- Under the pin and a configuration `γ = 0`, the withdrawn `hexp0` holds at the honest tuple. -/
theorem hexp0_at_honest_of_pin_cfg_gamma_zero
    (h : DeployedChipFamily.memoryChalValOfTuple P.optimized.basis P.honestTuple =
      P.optimized.memoryChallenge)
    (hγ : P.optimized.family.problem.cfg.challenges.memoryInputs.γ = 0)
    (Qm : Fin P.memoryChip.rap.w → Polynomial F) :
    ∀ i, FamilyMemoryRows.rowExpTerm P P.honestTuple Qm i = 0 := by
  intro i
  rw [Nock.RedTeam.Batch679.rowExpTerm_eq_zero_iff]
  exact Or.inl ((pin_forces_gamma P h).trans hγ)

/-! ## B. The receipt's other two hypotheses are generic -/

include P in
theorem memStateTagChar_of_package : FamilyMemoryRows.MemStateTagChar F := by
  intro n hn heq
  have hK := OptimizedHostileConfiguration.hchar_of_package P n (by omega)
  apply hK
  have := congrArg (algebraMap F K) heq
  simpa using this

theorem honest_seed_ne_zero : nprSeed P.honestTuple.1 ≠ 0 := by
  have h := OptimizedHostileTimestamps.hz0_of_package P
  have hcfg := congrArg ExactConfig.challenges P.optimized.family_cfg
  simp only [OptimizedFullStrictNockVMROMPackage.honestTuple,
    OptimizedFullStrictNockVMROMPackage.honestProductionTuple,
    OptimizedFullStrictNockVMROMPackage.honestJointCoins, nprSeed]
  rw [← hcfg]; exact h

end Pin

/-- The compiler's configuration: memory-input `γ = β = 0`. -/
theorem compiler_cfg_gamma_beta_zero {K : Type} [Field K] (α z a b c lmb : K) :
    (TraceGen.compilerChallengeVector α z a b c lmb).memoryInputs.γ = 0 ∧
    (TraceGen.compilerChallengeVector α z a b c lmb).memoryInputs.β = 0 := ⟨rfl, rfl⟩

end Nock.RedTeam.Batch737

/-! ## C. -/

open Lean Elab Command in
/-- Proof-term reach (type + `value? (allowOpaque := true)`, `Nock.*` expanded). -/
partial def Nock.RedTeam.Batch737.gateReach (env : Environment) (roots : List Name) :
    Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut work := roots
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

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some pidx := env.getModuleIdx? `Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
    | throwError "pinned module missing"
  let mut seenM : Std.HashSet Name := {}
  let mut work : List Name := [`Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage]
  while true do
    match work with
    | [] => break
    | m :: rest =>
      work := rest
      if seenM.contains m then continue
      seenM := seenM.insert m
      match env.getModuleIdx? m with
      | none => pure ()
      | some i =>
        for imp in env.header.moduleData[i.toNat]!.imports do
          unless seenM.contains imp.module do work := imp.module :: work
  for m in [`Nock.NockVMROM.Thm54.ExactTraversal, `Nock.NockVMROM.Thm54.AxisSoundness] do
    unless seenM.contains m do throwError m!"{m} is not below the pinned module"
  unless seenM.contains `Nock.NockVMROM.Thm54.HostileSkeletonDecoding do
    throwError "HostileSkeletonDecoding expected below the pinned module since the 33rd move"
  -- positive control for the module walk
  unless seenM.contains `Nock.NockVMROM.Thm54.FormRAxisEvent do
    throwError "control failed: FormRAxisEvent not found below the pinned module"
  let pinned := env.constants.toList.filterMap fun (n, _) =>
    if env.getModuleIdxFor? n == some pidx then some n else none
  let cl := Nock.RedTeam.Batch737.gateReach env pinned
  unless cl.contains `Nock.MemoryTable.Fmem do throwError "control failed: Fmem not reached"
  unless cl.contains `Nock.NockVMROM.Thm54.MemoryExactTopology do
    throwError "MemoryExactTopology not reached from the pinned file's declarations"
  logInfo m!"Batch737 C: {pinned.length} pinned declarations; proof-term closure {cl.size}; reaches MemoryExactTopology and (control) MemoryTable.Fmem; ExactTraversal/AxisSoundness below the pinned module, HostileSkeletonDecoding not"

#print axioms Nock.RedTeam.Batch737.pin_forces_gamma
#print axioms Nock.RedTeam.Batch737.pin_forces_beta_zero
#print axioms Nock.RedTeam.Batch737.hexp0_at_honest_of_pin_cfg_gamma_zero
#print axioms Nock.RedTeam.Batch737.memStateTagChar_of_package
#print axioms Nock.RedTeam.Batch737.honest_seed_ne_zero
#print axioms Nock.RedTeam.Batch737.compiler_cfg_gamma_beta_zero
