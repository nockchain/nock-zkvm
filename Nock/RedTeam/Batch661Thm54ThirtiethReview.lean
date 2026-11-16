/-
  Nock/RedTeam/Batch661Thm54ThirtiethReview.lean

  * **Check 1 (the authorized form).**
  * **Check 3 (slack).**
  * **Check 5 (figures, re-derived).**  The `2^{−123}` `𝕂²` figure
    does not read the walk work (its theorem's statement names only `p8Work`, `ioWork`).
  * **Check 6 (`htime`).**  Dischargeable: `(packageOf D …).strategy.verifier.raw.timestamp =
    D.timestampStrategy` by `packageOf_strategy_verifier` then `rfl` (`htime_discharged`, ~1 s).
    So `Batch639.honest_fixedFormRWorkload_le`'s premise is a theorem; the letter can drop it.
  * **Check 7 (reach).**
-/
import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.RealProgramSoundness
import Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance
import Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
import Nock.NockVMROM.Thm54.StrictAsymptoticSecurity
import Nock.NockVMROM.Thm54.OptimizedStrictFullPackageConcrete
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
open Lean Elab Command Meta

namespace Nock.RedTeam.Batch661

open scoped Polynomial
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FormRAxisEvent
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open scoped Classical

noncomputable section

/-! ## Check 1 -/

section Form
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [Fintype F] [CharP K (ringChar K)]

theorem guard_def (P : Polynomial (Polynomial K)) (E' : ℕ) :
    formRGuard P E' ↔ ∃ k ≤ E', P.coeff k ≠ 0 := Iff.rfl

theorem guardedBad_def {T : SemanticTimestampStrategy.ExactConfigTemplate F K}
    (E : SemanticTimestampStrategy.ExactExecutionTemplate T) (i : Fin T.kMem) (E' : ℕ) :
    formRGuardedBad E i E' =
      if formRGuard (formRTemplatePolynomial E i) E' then formRGuardedAxisFailureEvent E i E' else ∅ :=
  rfl

/-- Membership in the λ-event, unfolded at a seed proof. -/
theorem lambdaEvent_mem_iff (T : ProductionStrategy F K) (c : OptimizedProductionChallengeTuple K F)
    (hz : nprSeed c.1 ≠ 0) :
    c ∈ formRLambdaEvent T ↔
      ∃ i : Fin (T.verifier.raw.timestamp.afterSeed ⟨nprSeed c.1, hz⟩).configTemplate.kMem,
        formRGuard (formRTemplatePolynomial
            (ProductionAxisStructureVerifier.committedTemplate T.verifier (nprSeed c.1) hz) i)
          (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 3) ∧
        (alphaM c.1, c.2.2.2.lambda) ∈ formRRootBad (formRTemplatePolynomial
            (ProductionAxisStructureVerifier.committedTemplate T.verifier (nprSeed c.1) hz) i)
          (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 3) := by
  constructor
  · intro hc
    obtain ⟨hz', hmem⟩ := (Finset.mem_filter.mp hc).2
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hmem
    refine ⟨i, ?_⟩
    unfold formRGuardedBad at hi
    split_ifs at hi with hg
    · refine ⟨hg, ?_⟩
      have hi' := (Finset.mem_filter.mp hi).2
      rw [formRBadAt_eq_template] at hi'
      exact hi'
    · exact absurd hi (Finset.notMem_empty _)
  · rintro ⟨i, hg, hmem⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩⟩
    unfold formRGuardedBad
    rw [if_pos hg]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [formRBadAt_eq_template]
    exact hmem

/-- The λ-event reads a tuple only through `(z, αM, λ)`: two tuples agreeing on those three
coordinates are members together. -/
theorem lambdaEvent_reads_three (T : ProductionStrategy F K)
    (c c' : OptimizedProductionChallengeTuple K F)
    (hz : nprSeed c.1 = nprSeed c'.1) (hα : alphaM c.1 = alphaM c'.1)
    (hl : c.2.2.2.lambda = c'.2.2.2.lambda) :
    c ∈ formRLambdaEvent T → c' ∈ formRLambdaEvent T := by
  intro hc
  obtain ⟨hz0, -⟩ := (Finset.mem_filter.mp hc).2
  have hz0' : nprSeed c'.1 ≠ 0 := hz ▸ hz0
  have key := (lambdaEvent_mem_iff T c hz0).1 hc
  refine (lambdaEvent_mem_iff T c' hz0').2 ?_
  revert key hz0 hz0'
  generalize nprSeed c.1 = z₁ at hz ⊢
  generalize nprSeed c'.1 = z₂ at hz ⊢
  generalize alphaM c.1 = a₁ at hα ⊢
  generalize alphaM c'.1 = a₂ at hα ⊢
  generalize c.2.2.2.lambda = l₁ at hl ⊢
  generalize c'.2.2.2.lambda = l₂ at hl ⊢
  subst hz hα hl
  intro hz0 hz0' key
  exact key

end Form

section Pinned
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- (Retyped at the
thirty-second move, lane `lambda-consumer-32nd`: the instance is the decoded event
`decodedLambdaEventOf`; it was `formRLambdaEvent P.strategy`.) -/
theorem lambdaEvent_in_pinned (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    P.decodedLambdaEventOf Qc Qm ⊆ P.optimizedFailureEvent Qc Qm := by
  intro c hc
  unfold OptimizedFullStrictNockVMROMPackage.optimizedFailureEvent OptimizedHostileProductionFailureEvent
  exact Finset.mem_union_left _ (Finset.mem_union_right _ hc)

end Pinned

section Bodies
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [CharP K (ringChar K)]

theorem workload_body (T : ProductionStrategy F K) (Λ top ax : ℕ) :
    workload T Λ top ax =
      1 + (3 + 19 * (SemanticStrategy.computeSkeletonRows T.skeleton).length) * (2 * Λ - 1) +
        top + ax + formRUniformWorkload T + reqPairWorkload T Λ + sizeWindowRootBound Λ := rfl

/-- `workload = (the pre-30th workload) + formRUniformWorkload` (`fixedFormRWorkload` until the
thirty-second move; `+ reqPairWorkload T Λ` since the thirty-third). -/
theorem workload_split (T : ProductionStrategy F K) (Λ top ax : ℕ) :
    workload T Λ top ax =
      (1 + (3 + 19 * (SemanticStrategy.computeSkeletonRows T.skeleton).length) * (2 * Λ - 1) +
        top + ax + sizeWindowRootBound Λ) + formRUniformWorkload T + reqPairWorkload T Λ := by
  rw [workload_body]; ring

theorem failureUnion_body {Λ : ℕ} (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K) :
    FailureUnion T C lmb =
      (((zeroSeedFailureEvent ∪ collisionFailureEvent C.census) ∪
        specializedTopologyFailureEvent T.verifier.raw lmb) ∪ guardedAxisFailureEvent T lmb) ∪
        SizeWindowFailure T.skeleton := rfl

theorem pricedWalkWork_body (N M : ℕ) :
    pricedWalkWork N M =
      ComputeWalkRootEvents.walkRootBound N + WalkTilingEvents.computeTilingBound N +
        WalkTilingEvents.memoryTilingBound M + WalkPrefixGammaEvents.computePrefixGammaBound N +
        WalkPrefixGammaEvents.memoryPrefixGammaBound M +
        WalkForestPrefixAlphaEvents.memoryForestAlphaBound M := rfl

end Bodies

/-! ## Check 5 — figures -/

theorem numerator_identity (S : ℕ) (hS : 1 ≤ S) :
    407 * (S * S) + 152 * S + 288 - (8 * S + 260) + (6 * (S * S) + 260 * S) =
      413 * (S * S) + 404 * S + 28 := by
  have h : 8 * S + 260 ≤ 407 * (S * S) + 152 * S + 288 := by nlinarith
  omega

theorem figure_122 : (413 * 2 ^ 62 + 404 * 2 ^ 31 + 28) * 2 ^ 122 < 2 * cardKGold := by
  norm_num [cardKGold]

theorem figure_120 : (413 * 2 ^ 64 + 404 * 2 ^ 32 + 28) * 2 ^ 120 < 2 * cardKGold := by
  norm_num [cardKGold]

/-- The worst-case summand at `S` rows is below the slack it replaces plus `6S² + 252S`. -/
theorem summand_at_S (S : ℕ) : 2 * (S * (3 * S + 130)) = 6 * (S * S) + 260 * S := by ring

/-! ## Check 6 — `htime` is a theorem -/

section Htime
open Nock.NockVMROM.Thm54.GenericHonestPackage Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips Nock.NockVMROM.Thm54.BuildablePackage
variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

theorem htime_discharged {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E) (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier.raw.timestamp = D.timestampStrategy := by
  rw [packageOf_strategy_verifier]
  rfl

end Htime

end

/-! ## Check 7 — reach -/

partial def reach (env : Environment) (roots : Array Name) (stop : Name → Bool) :
    Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut work := roots.toList
  while true do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      if stop n then continue
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
  let stop : Name → Bool := fun n => !(`Nock).isPrefixOf n
  let roots := #[``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod,
    ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76,
    ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package]
  -- Positive controls retargeted at the thirty-second move (they were `formRLambdaEvent`,
  -- `fixedFormRWorkload`, `formRGuardedBad`, which the move takes out of the capstone's reach):
  -- the decoded event, its summand and the guard it applies.
  let positive := #[``Nock.NockVMROM.Thm54.DecodedLambdaEvent.decodedLambdaEventOfEnvs,
    ``Nock.NockVMROM.Thm54.ProductionP8Containment.formRUniformWorkload,
    ``Nock.NockVMROM.Thm54.FormRAxisEvent.formRGuard]
  let carriers : Array Name := #[`Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance,
    `Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance, `Nock.NockVMROM.Thm54.ProductionAsymptotic,
    `Nock.NockVMROM.Thm54.StrictAsymptoticSecurity, `Nock.NockVMROM.Thm54.DistinctCensusFold2,
    `Nock.NockVMROM.Thm54.IOCapstoneRedundancy, `Nock.NockVMROM.Thm54.OptimizedHostileConfiguration,
    -- The concrete F73 fixture module
    `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageConcrete]
  for r in roots do
    let cl := reach env #[r] stop
    for p in positive do
      unless cl.contains p do throwError m!"positive control: {p} not reached from {r}"
    let hits := cl.toArray.filter fun n =>
      match env.getModuleFor? n with
      | some m => carriers.contains m
      | none => false
    logInfo m!"{r}: closure {cl.size}; constants from hlamEv/hformR carrier modules reached: {hits.size}"
    unless hits.isEmpty do throwError m!"carrier-module constants reached from {r}: {hits}"

end Nock.RedTeam.Batch661
