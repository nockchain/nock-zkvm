/-
  Nock/RedTeam/Batch573Thm54SeedLocal.lean

Sections:
  * §A  `∀ z` is not merely unprovable for the hostile traces — it is REFUTED, with no
        collision: `execTemplateOfTraces` ignores its seed argument, every memory row of the
        `(z, α)`-specialized hostile exec carries `.2.1.z = nprSeed c.1` (`lblMAt`), and
        `BindMemoryRow z` demands `row.2.1.z = z`.  So `BindsAt z … → z = nprSeed c.1`
        (`bindsAt_traces_forces_seed`), and `TracesBindsHyps` (since H1.5b Part 1:
        `(strategyOfTraces …).BindsAll`) is unsatisfiable whenever
        `3 ≤ |K|` (`tracesBindsAll_unsat`).  Every theorem taking `hbinds : TracesBindsHyps`
        is therefore vacuous at every field with three or more elements.
  * §B  the plan's item-5 claim ("`remainingActiveMemPower_of_deployed` reads only chip facts")
        measured by a proof-term walk (`value?
  * §C  where the NPR-collision event lives today: `collisionFailureEvent C.census` is a
        summand of `FailureUnion` (membership lemma) and a seed-coordinate cylinder
        (`RoundFibred.collisionFailureEvent_eq_cylinder`, cited); the consumed
        `optimizedFailureEvent` reaches the HONEST `P.strategy` and no `decodedSkeletonOf`
        (walk, with `strategyOfTraces` as positive control).
  * §D  blast radius: the pinned statement's fields whose TYPE mentions `ProductionStrategy`,
        `nockCompiles_zmod`'s type does not, and the count of `Nock.*` declarations whose type
        mentions the structure.

  -- the paper
-/
import Lean
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.RoundFibredSoundness
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.RedTeam.Batch522Thm54RemainingActiveMemPower
import Nock.RedTeam.Batch531Thm54MemFirstAndReady

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch573

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X])
  (Qm : Fin P.memoryChip.rap.w → F[X])
  (c : OptimizedProductionChallengeTuple K F)
  (h : TracesWalkHyps P Qc Qm c)

/-! ## §A — `∀ z` is refuted for the traces, with no collision -/

/-- Every memory-forest root label of the `(z, α, λ)`-specialized hostile exec carries the
SAMPLED seed, whatever `z`, `α` and `λ` are: `execTemplateOfTraces` never reads its seed
argument, `wrapMemoryLabel` and `MemoryRowTemplate.specialize` preserve `placeholder.2.1`,
and `lblMAt` writes `z := nprSeed c.1`.  (`λ` threaded since the 28th.) -/
theorem specialized_memory_label_z (z : K) (hz : z ≠ 0) (α lmb : K) :
    ∀ t ∈ (specializedProblem (timestampOfTraces P Qc Qm c h) z hz α lmb).exec.memoryForest,
      t.label.2.1.z = nprSeed c.1 := by
  intro t ht
  change t ∈ ((execOfTraces P Qc Qm c h).memoryForest.map
      (mapNTree (wrapMemoryLabel (alphaM c.1)))).map
      (mapNTree (fun row => MemoryRowTemplate.specialize row α lmb)) at ht
  rw [List.mem_map] at ht
  obtain ⟨t1, ht1, rfl⟩ := ht
  rw [List.mem_map] at ht1
  obtain ⟨t0, ht0, rfl⟩ := ht1
  change t0 ∈ reconForest P.optimized.family.problem.cfg.kMem (foM P Qm c) (lblM P Qm c)
      P.optimized.family.problem.cfg.memRows at ht0
  unfold reconForest at ht0
  rw [List.mem_map] at ht0
  obtain ⟨i, _, rfl⟩ := ht0
  rw [mapNTree_label, mapNTree_label, buildTF_label]
  show (lblM P Qm c i).2.1.z = nprSeed c.1
  unfold lblM
  split <;> rfl

/-- **`BindsAt` at the traces forces the seed.**  Any skeleton, any `z ≠ 0`, any `α`, any `λ`:
binding the `(z, α, λ)`-specialized hostile exec is possible only at `z = nprSeed c.1`.  The
witness is the first memory root's `row.2.1.z = z` conjunct of `BindMemoryRow`.  (`λ`
threaded since the 28th.) -/
theorem bindsAt_traces_forces_seed (S : SemanticSkeleton) (z : K) (hz : z ≠ 0) (α lmb : K)
    (hb : BindsAt z S (specializedProblem (timestampOfTraces P Qc Qm c h) z hz α lmb).cfg
      (specializedProblem (timestampOfTraces P Qc Qm c h) z hz α lmb).exec) :
    z = nprSeed c.1 := by
  have hne :=
    (specializedProblem (timestampOfTraces P Qc Qm c h) z hz α lmb).exec.memoryForest_nonempty
  have hmf := hb.memoryForest
  obtain ⟨t, ts, hF⟩ := List.exists_cons_of_ne_nil hne
  rw [hF] at hmf
  obtain ⟨s, ss, hhead, _, _⟩ := List.forall₂_cons_right_iff.1 hmf
  have hzrow : t.label.2.1.z = z := hhead.root.2.1
  have hlbl := specialized_memory_label_z P Qc Qm c h z hz α lmb t
    (by rw [hF]; exact List.mem_cons_self)
  exact hzrow.symm.trans hlbl

/-- **Binding the traces at every seed is unsatisfiable at every field with three or more
elements.**  Pick `z ∉ {0, nprSeed c.1}`; `∀ z` would bind the exec at that `z`, contradicting
`bindsAt_traces_forces_seed`.  No collision event is involved: the refutation is
definitional (the hostile exec ignores the specialization seed).

Restated at H1.5b Part 1 on the `hbinds`-free strategy: `(strategyOfTraces …).BindsAll` is the
retired `TracesBindsHyps`. -/
theorem tracesBindsAll_unsat (h3 : 3 ≤ Fintype.card K) :
    ¬ (strategyOfTraces P Qc Qm c h).BindsAll := by
  intro hb
  have hex : ∃ z : K, z ≠ 0 ∧ z ≠ nprSeed c.1 := by
    by_contra hcon
    have hsub : (Finset.univ : Finset K) ⊆ ({0, nprSeed c.1} : Finset K) := by
      intro z _
      by_cases h0 : z = 0
      · simp [h0]
      · by_cases h1 : z = nprSeed c.1
        · simp [h1]
        · exact absurd ⟨z, h0, h1⟩ hcon
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_univ] at hcard
    have h2 : ({0, nprSeed c.1} : Finset K).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨z, hz, hzne⟩ := hex
  exact hzne (bindsAt_traces_forces_seed P Qc Qm c h _ z hz (alphaM c.1) c.2.2.2.lambda
    (hb z hz (alphaM c.1) c.2.2.2.lambda))

/-- Consequence, as measured before H1.5b Part 1: every theorem parametrized by
`hbinds : TracesBindsHyps …` was vacuous at `3 ≤ |K|`.  Since the split `strategyOfTraces` takes no
binding hypothesis and those theorems are stated on it directly; any theorem that still assumed
`BindsAll` of the traces would be vacuous for this reason, and the seed-local
`BindsAtCoin` (`strategyOfTraces_bindsAtCoin`) is what replaces it. -/
theorem strategyOfTraces_hyp_vacuous (h3 : 3 ≤ Fintype.card K)
    (hbinds : (strategyOfTraces P Qc Qm c h).BindsAll) : False :=
  tracesBindsAll_unsat P Qc Qm c h h3 hbinds

/-- Positive control for §A: the seed-local form is NOT refuted by the forcing lemma — at
`z = nprSeed c.1` the forced equation is trivially satisfied.  (`TracesBindsAtSeed` is a
theorem from the tree bindings, `Batch531.tracesBindsAtSeed_of_tree`.) -/
theorem forcing_consistent_with_seed_local (hz : nprSeed c.1 ≠ 0) (α lmb : K)
    (S : SemanticSkeleton)
    (hb : BindsAt (nprSeed c.1) S
      (specializedProblem (timestampOfTraces P Qc Qm c h) (nprSeed c.1) hz α lmb).cfg
      (specializedProblem (timestampOfTraces P Qc Qm c h) (nprSeed c.1) hz α lmb).exec) :
    nprSeed c.1 = nprSeed c.1 :=
  bindsAt_traces_forces_seed P Qc Qm c h S (nprSeed c.1) hz α lmb hb

/-! ## §C (compiled half) — where the collision event lives today -/

/-- `collisionFailureEvent C.census` is a summand of `FailureUnion T C lmb` (the second of
five; `lmb` threaded since the 28th). -/
theorem collision_mem_failureUnion {Λ : ℕ} (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K) (ω : JointCoins K)
    (hω : ω ∈ collisionFailureEvent (K := K) C.census) :
    ω ∈ ProductionP8Containment.FailureUnion T C lmb := by
  simp [ProductionP8Containment.FailureUnion, hω]

/-- `zeroSeedFailureEvent` is the first summand (`lmb` threaded since the 28th). -/
theorem zeroSeed_mem_failureUnion {Λ : ℕ} (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K) (ω : JointCoins K)
    (hω : ω ∈ (zeroSeedFailureEvent : Finset (JointCoins K))) :
    ω ∈ ProductionP8Containment.FailureUnion T C lmb := by
  simp [ProductionP8Containment.FailureUnion, hω]

/-- Both are seed-coordinate cylinders with a pre-coin bad set (`RoundFibredSoundness`). -/
theorem collision_is_seed_cylinder {Λ : ℕ} (C : ComparisonCensus Λ) :
    collisionFailureEvent (K := K) C =
      (RoundFibred.cylinder (3 : Fin 4) (fun _ : Fin 4 → K => C.badSeeds (K := K))).map
        RoundFibred.jointVecEquiv.toEmbedding :=
  RoundFibred.collisionFailureEvent_eq_cylinder C

end

/-! ## §B / §C / §D — proof-term and type walks -/

open Lean Meta Elab Command

/-- Direct constants of a declaration's value. -/
def directOf (env : Environment) (root : Name) : Array Name :=
  match env.find? root with
  | some ci =>
    match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants
    | none => #[]
  | none => #[]

/-- Transitive constants of a declaration's proof/definition term, restricted to `Nock.*`.
Reachability, not dependence. -/
def reachSet (env : Environment) (root : Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := directOf env root
  while stack.size > 0 do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if (`Nock).isPrefixOf c then
      for d in directOf env c do
        unless seen.contains d do stack := stack.push d
  return seen

def ACC : Name :=
  ``OptimizedFullStrictNockVMROMPackage.OptimizedHistoricalAcceptanceAt  -- H1.5b Part 2a: the pre-2a acceptance

def accFields : List Name :=
  [`p8, `same_problem, `sampled_io_coins, `memory_sampled_coins,
   `memory_intermediate_pole, `compute_satisfies, `memory_satisfies]

def STMT : Name := ``OptimizedFullStrictThm54Statement

def stmtFields : List Name :=
  [`structural, `optimized_chips, `shared_io, `perfect_completeness, `containment,
   `walk_bounds, `p8_fixed_field_soundness, `p8_fixed_field_bits, `acceptance_to_target,
   `complete_false_acceptance_bound, `complete_false_acceptance_bits, `exact_resources,
   `row_budgets, `shared_forest_axis]

/-- Does a name have `ProductionStrategy` as a component (the structure, its namespace, or the
package projection `strategy`)? -/
def mentionsStrategy (n : Name) : Bool :=
  n.components.contains `ProductionStrategy ∨
    n == ``OptimizedFullStrictNockVMROMPackage.strategy ∨
    n == ``OptimizedStrictNockVMROMPackage.strategy

/-- Constants a declaration's TYPE mentions that involve `ProductionStrategy`. -/
def strategyInType (env : Environment) (n : Name) : List Name :=
  match env.find? n with
  | some ci => (ci.type.getUsedConstants.filter mentionsStrategy).toList
  | none => []


run_cmd do
  let env ← getEnv
  -- §B
  let root := ``Nock.RedTeam.Batch522.remainingActiveMemPower_of_deployed
  let r := reachSet env root
  let rIff := reachSet env ``OptimizedFullStrictNockVMROMPackage.optimizedHistoricalAcceptanceAt_iff
  for f in accFields do
    let n := ACC ++ f
    logInfo m!"B remainingActiveMemPower_of_deployed reaches {n}: {r.contains n}"
  -- positive control: the iff projects every field
  for f in accFields do
    unless rIff.contains (ACC ++ f) do
      throwError m!"positive control: optimizedProductionAcceptanceAt_iff does not reach {f}"
  -- the hand-read chain: hz0_of_good / chipAlpha_eq_alphaM read `same_problem`;
  -- optimizedFullStrict_paired_records reads the two memory pins
  unless r.contains (ACC ++ `same_problem) do
    throwError "B: same_problem NOT reached — the hand reading of hz0_of_good is wrong"
  unless r.contains (ACC ++ `memory_intermediate_pole) do
    throwError "B: memory_intermediate_pole NOT reached"
  unless r.contains (ACC ++ `memory_sampled_coins) do
    throwError "B: memory_sampled_coins NOT reached"
  unless r.contains ``OptimizedHostileTimestamps.hz0_of_good do
    throwError "B: hz0_of_good NOT reached"
  unless r.contains ``OptimizedHostileTimestamps.chipAlpha_eq_alphaM do
    throwError "B: chipAlpha_eq_alphaM NOT reached"
  unless r.contains (ACC ++ `sampled_io_coins) do
    throwError "B: sampled_io_coins NOT reached"
  if r.contains (ACC ++ `p8) then
    throwError "B: p8 reached — the measurement of 2026-09-28 has moved"
  for f in stmtFields do
    if r.contains (STMT ++ f) then
      throwError m!"B: Statement.{f} reached — `S` is no longer a dead binder"
  logInfo m!"B reach={r.size}: p8 ABSENT; same_problem / sampled_io_coins / memory_sampled_coins / memory_intermediate_pole / compute_satisfies / memory_satisfies PRESENT; no Statement field reached"
  -- §C
  let rEv := reachSet env ``OptimizedFullStrictNockVMROMPackage.optimizedFailureEvent
  let rSoT := reachSet env ``StrategyOfTracesCore.strategyOfTraces
  unless rEv.contains ``OptimizedFullStrictNockVMROMPackage.strategy do
    throwError "C: optimizedFailureEvent does not reach the honest P.strategy"
  if rEv.contains ``StrategyOfTraces.decodedSkeletonOf then
    throwError "C: optimizedFailureEvent reaches decodedSkeletonOf (a hostile census IS priced)"
  unless rSoT.contains ``StrategyOfTraces.decodedSkeletonOf do
    throwError "C positive control: strategyOfTraces does not reach decodedSkeletonOf"
  logInfo m!"C optimizedFailureEvent reach={rEv.size}: honest P.strategy PRESENT, decodedSkeletonOf ABSENT (control: strategyOfTraces reach={rSoT.size} has it)"
  -- §D
  let mut pinned : List Name := []
  for f in stmtFields do
    let hits := strategyInType env (STMT ++ f)
    if !hits.isEmpty then pinned := pinned ++ [f]
    logInfo m!"D Statement.{f} type mentions strategy via: {hits}"
  unless pinned.contains `containment do throwError "D: containment expected to mention strategy"
  if pinned.contains `shared_io then throwError "D: shared_io must not mention strategy"
  logInfo m!"D pinned fields naming ProductionStrategy ({pinned.length}/{stmtFields.length}): {pinned}"
  let nz := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
  let hitsZ := strategyInType env nz
  unless hitsZ.isEmpty do throwError m!"D: nockCompiles_zmod type mentions strategy: {hitsZ}"
  let some ciZ := env.find? nz | throwError "nockCompiles_zmod missing"
  unless ciZ.type.getUsedConstants.contains STMT do
    throwError "D: nockCompiles_zmod type does not mention the Statement"
  logInfo "D nockCompiles_zmod: type mentions OptimizedFullStrictThm54Statement and no ProductionStrategy name"
  -- count of Nock.* declarations whose type mentions the structure itself
  let strct := ``ProductionP8Containment.ProductionStrategy
  let mut cnt : Nat := 0
  let mut files : Std.HashSet Name := {}
  for (n, ci) in env.constants.toList do
    if (`Nock).isPrefixOf n && !n.isInternal then
      if ci.type.getUsedConstants.contains strct then
        cnt := cnt + 1
        match env.getModuleFor? n with
        | some m => files := files.insert m
        | none => pure ()
  logInfo m!"D declarations under Nock whose TYPE mentions ProductionStrategy: {cnt} across {files.size} modules"

end Nock.RedTeam.Batch573

#print axioms Nock.RedTeam.Batch573.specialized_memory_label_z
#print axioms Nock.RedTeam.Batch573.bindsAt_traces_forces_seed
#print axioms Nock.RedTeam.Batch573.tracesBindsAll_unsat
#print axioms Nock.RedTeam.Batch573.strategyOfTraces_hyp_vacuous
#print axioms Nock.RedTeam.Batch573.collision_mem_failureUnion
#print axioms Nock.RedTeam.Batch573.zeroSeed_mem_failureUnion
#print axioms Nock.RedTeam.Batch573.collision_is_seed_cylinder
