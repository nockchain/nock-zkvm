/-
  Nock/RedTeam/Batch574Thm54FamilyChain.lean

  Sections:
  * §A  the five acceptance pins are THEOREMS of the family chip (no hypothesis at all):
        `rowEnvAt` reads `alphaM c.1` at slot `0`, `nprSeed c.1` at `1`, the IO coins at
        `7`/`8`; `memorySourceEnvAt` reads the IO coins at `4`/`5` and `interPole` at `6`.
        The activity masks and seven of the eight record coordinates are trace-only
        (`eval_congr_of_traceOnly`) and equal their constant-chip values; the EIGHTH — the
        request timestamp — reads challenge slot `0` (`subst_tc74`: `ln_prev · α`), so
        `hostileRequests P Qc` carries the compiler's `α` and must be re-pointed at the
        family (its LENGTH is chalVal-free).  So part 2 is a PARAMETRIZATION of the `_at`
        layer of the timestamp chain plus one re-pointed list.
  * §B  proof-term walk (`value?
  * §C  the union reads the census through ONE summand (`collisionFailureEvent`), and
        reads its `pair` list (the nouns), not a count: a "union on row counts" is not a
        set.  `decodedSkeletonOf` is `c`-free; `strategyOfTraces` / `execOfTraces` are not,
        and the decoded label INPUTS are the tuple's coins (compiled), so the hostile
        union's topology/axis summands are `c`-indexed as things stand.
  * §E  `strategyOfTraces` reaches the honest `P.objects`; the honest containment carries
        `SkeletonOperationalCore` in its type.
-/
import Lean
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.NockVMROM.Thm54.HostilePoleAlignment
import Nock.NockVMROM.Thm54.ResponseTsMemPowers
import Nock.NockVMROM.Thm54.MemoryInternalPole
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.RealProgramSoundness
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.RedTeam.Batch465Thm54DeployedRootLabelEqClaim
import Nock.RedTeam.Batch522Thm54RemainingActiveMemPower
import Nock.RedTeam.Batch533Thm54WrapClose
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch574

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.HostilePoleAlignment
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.RedTeam.Batch465
open Module

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)

/-! ## §A — the pins are family-chip slot lemmas; the records are chalVal-free -/

section ComputeSlots
variable (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (i : Fin P.optimized.family.problem.cfg.compRows)

/-- **`chipAlpha_eq_alphaM` at the family chip needs no `same_problem`**: compute slot `0`
of `rowEnvAt` IS `alphaM c.1` (`computeKOfTuple c 0`), for every trace and every row.
This replaces `OptimizedHostileTimestamps.chipAlpha_eq_alphaM`, whose proof reads
`hacc.same_problem.specialized_cfg_eq_family` (§B). -/
theorem rowEnvAt_alphaM :
    (rowEnvAt P c Qc i).toSourceEnv.chal 0 = alphaM c.1 :=
  (rowEnvAt_chal P c Qc i ⟨0, by decide⟩).trans (computeKOfTuple_alphaM c)

/-- **`hz0_of_good` at the family chip needs no `same_problem`**: slot `1` IS `nprSeed c.1`,
so `cfg.challenges.z ≠ 0` is replaced by `nprSeed c.1 ≠ 0`, which
`OptimizedHostileTimestamps.nprSeed_ne_of_good` gives from `hgood` alone. -/
theorem rowEnvAt_seed :
    (rowEnvAt P c Qc i).toSourceEnv.chal 1 = nprSeed c.1 :=
  (rowEnvAt_chal P c Qc i ⟨1, by decide⟩).trans (computeKOfTuple_seed c)

/-- **`sampled_io_coins` is a theorem of the family compute chip**: the row's IO coins
(`rowCoins`, challenge slots `7`/`8`) are the tuple's `c.2.1`, i.e. `sampledCoins c` —
what `OptimizedHostileIOAssembly.sampled_eq_sampledCoins` needed the pin for. -/
theorem rowCoinsAt_eq_sampledCoins :
    rowCoins (rowEnvAt P c Qc i) = sampledCoins c := by
  have h7 := (rowEnvAt_chal P c Qc i ⟨7, by decide⟩).trans (computeKOfTuple_ioGamma c)
  have h8 := (rowEnvAt_chal P c Qc i ⟨8, by decide⟩).trans (computeKOfTuple_ioPole c)
  simp only [rowCoins, sampledCoins, h7, h8]

end ComputeSlots

section MemorySlots
variable (Qm : Fin P.memoryChip.rap.w → F[X])
  (i : Fin P.optimized.family.problem.cfg.memRows)

private theorem gather_chal_of_tuple (q : Fin 9) :
    (memorySourceEnvAt P c Qm i).chal q = memoryKOfTuple c q := by
  have hcol :
      (memorySourceTemplate P.optimized.basis).col0 3 = memoryCol0 :=
    memorySourceTemplate_col0 P.optimized.basis
  simp only [memorySourceEnvAt, hcol, gatherEnv, memoryCol0, memoryBaseEnvAt, envOfTrace]
  simp_rw [memoryChalValOfTuple_slot P.optimized.basis c q]
  change reconstruct P.optimized.basis (coord P.optimized.basis (memoryKOfTuple c q)) =
    memoryKOfTuple c q
  exact reconstruct_coord P.optimized.basis (memoryKOfTuple c q)

/-- Memory `𝕂` slot `5` at the family chip is the IO pole (`memoryKOfTuple c 5`). -/
theorem memorySourceEnvAt_chal5 :
    (memorySourceEnvAt P c Qm i).chal 5 = c.2.1.2 := by
  rw [gather_chal_of_tuple P c Qm i ⟨5, by decide⟩]
  rfl

/-- **`memory_sampled_coins` and `memory_intermediate_pole` are theorems of the family memory
chip, with no hypothesis** — not even satisfaction. -/
theorem family_memory_pins :
    ((memorySourceEnvAt P c Qm i).chal 4 = c.2.1.1 ∧
        (memorySourceEnvAt P c Qm i).chal 5 = c.2.1.2) ∧
      (memorySourceEnvAt P c Qm i).chal 6 = c.2.2.2.interPole :=
  ⟨⟨memorySourceEnvAt_chal4 P c Qm i, memorySourceEnvAt_chal5 P c Qm i⟩,
    memorySourceEnvAt_chal6 P c Qm i⟩

end MemorySlots

section Records
variable (Qc : Fin P.computeChip.rap.w → F[X])
  (i : Fin P.optimized.family.problem.cfg.compRows)

/-- The family gather of the remapped trace and the constant-chip gather agree on every
source trace column (`Batch465::familyRow_trace_eq`; `computeSourceEnv_eq` is `rfl`). -/
theorem sourceTrace_at_eq :
    (rowEnvAt P c (familyQc P c Qc) i).toSourceEnv.trace = (rowEnv P Qc i).toSourceEnv.trace :=
  familyRow_trace_eq P c Qc i

theorem sourceTraceNext_at_eq :
    (rowEnvAt P c (familyQc P c Qc) i).toSourceEnv.traceNext =
      (rowEnv P Qc i).toSourceEnv.traceNext :=
  familyRow_traceNext_eq P c Qc i

/-- The activity mask of slot `j` is a trace-only expression: it does not move between the
family and the constant chip. -/
theorem activeMask_at_eq (j : Fin 3) :
    activeMask (rowEnvAt P c (familyQc P c Qc) i) j = activeMask (rowEnv P Qc i) j := by
  unfold activeMask
  refine eval_congr_of_traceOnly _ ?_ (sourceTrace_at_eq P c Qc i)
    (sourceTraceNext_at_eq P c Qc i)
  fin_cases j <;> decide

theorem rowRecord_at_eq (j : Fin 3) (k : Fin 10) (hk : (k : ℕ) < 6) :
    rowRecord (rowEnvAt P c (familyQc P c Qc) i) j k = rowRecord (rowEnv P Qc i) j k := by
  unfold rowRecord
  have h9 : ¬ (k : ℕ) = 9 := by omega
  have h6 : ¬ (k : ℕ) = 6 := by omega
  have h8 : ¬ (k : ℕ) = 8 := by omega
  simp only [if_neg h9, if_neg h6, if_neg h8]
  refine eval_congr_of_traceOnly _ ?_ (sourceTrace_at_eq P c Qc i)
    (sourceTraceNext_at_eq P c Qc i)
  fin_cases j <;> fin_cases k <;> first | decide | exact absurd hk (by decide)

theorem slotT_coordinate_not_traceOnly :
    traceOnly ((sampledSlotT .traceCur 67).subst finalSampledNamespace) = false := by
  decide

theorem slotC_coordinate_not_traceOnly :
    traceOnly ((sampledSlotC .traceCur 67).subst finalSampledNamespace) = false := by
  decide

/-- **The eighth coordinate — the timestamp — is NOT trace-only: it reads challenge slot `0`.**
`mem_record₁`'s timestamp is decoded as `ln_prev · α`, so
at the family chip it is `ln_prev · alphaM c.1` while at the constant chip it is
`ln_prev · cfg.challenges.α` (`chipAlpha_eq_cfg`).  `hostileRequests P Qc` therefore carries
the COMPILER's `α` in its timestamps; the family restatement must re-point it. -/
theorem rowRecord_ts_at_reads_tuple_alpha :
    rowRecord (rowEnvAt P c (familyQc P c Qc) i) 0 7 =
      OptimizedHostileTimestamps.lnPrevAt (rowEnvAt P c (familyQc P c Qc) i) * alphaM c.1 := by
  rw [OptimizedHostileTimestamps.rowRecord_ts_zero]
  congr 1
  exact rowEnvAt_alphaM P c (familyQc P c Qc) i

/-- Negative control for the previous theorem: the timestamp expression is measured NOT
trace-only, so `eval_congr_of_traceOnly` cannot be applied to it. -/
theorem ts_coordinate_not_traceOnly :
    traceOnly ((computeTraceSubst .traceCur (67 + 8 * 0 + 7)).subst finalSampledNamespace) =
      false := by
  decide

/-- **The request COUNT is chalVal-free** (only the activity masks decide it), which is what
the α-collision event `TimestampCollisionEvent |hostileRequests|` and the range premises
read. -/
theorem rowRequests_length_at_eq :
    (rowRequests (rowEnvAt P c (familyQc P c Qc) i)).length =
      (rowRequests (rowEnv P Qc i)).length := by
  simp only [rowRequests, activeMask_at_eq]
  have h3 : (List.finRange 3 : List (Fin 3)) = [0, 1, 2] := by decide
  rw [h3]
  simp only [List.filterMap_cons, List.filterMap_nil]
  split_ifs <;> simp

end Records

/-! ## §C (compiled half) — the decoded label INPUTS are the tuple's coins -/

/-- Every decoded memory label's `z` input is `nprSeed c.1` by definition (`lblMAt`): the
decoded exec is a `c`-indexed object.  (`Batch573.specialized_memory_label_z` carries this
through the specialization.) -/
theorem lblMAt_z_is_tuple
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (lblMAt P Qm c i).2.1.z = nprSeed c.1 :=
  rfl

/-- The decoded compute label's timestamp input is `alphaM c.1`: `decodeInputs` reads
challenge slot `0` of the family gather (`inpOf`, `computeSubst`), which is the tuple's
coin.  So `execOfTraces` — hence `strategyOfTraces`' verifier — depends on `c` in VALUE, not
only in its binder. -/
theorem lblCAt_alpha_is_tuple
    (Qc : Fin P.computeChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    (lblCAt P Qc c i).2.1.α = alphaM c.1 := by
  -- `lblCAt ….2.1.α` unfolds (`decodeInputs`, `inpOf`, `Env.ofSubst computeSubst`, `chl 0`)
  -- to challenge slot `0` of the family gather.
  exact rowEnvAt_alphaM P c (familyQc P c Qc) i

/-! `strategyOfTraces` is `c`-indexed while `decodedSkeletonOf` is not (type-level check in
the `run_cmd` below); the value-level half is `lblCAt_alpha_is_tuple` / `lblMAt_z_is_tuple`. -/

end

/-! ## §B / §C / §D / §E — proof-term and type walks -/

open Lean Meta Elab Command

def directOf (env : Environment) (root : Name) : Array Name :=
  match env.find? root with
  | some ci =>
    match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants
    | none => #[]
  | none => #[]

/-- Transitive constants of a declaration's proof/definition term, restricted to `Nock.*`
(reachability, `Batch337`/`Batch573`). -/
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

def typeMentions (env : Environment) (n target : Name) : Bool :=
  match env.find? n with
  | some ci => ci.type.getUsedConstants.contains target
  | none => false

def need (env : Environment) (n : Name) : CommandElabM Unit := do
  unless (env.find? n).isSome do throwError m!"name does not resolve: {n}"

def ACC : Name :=
  ``OptimizedFullStrictNockVMROMPackage.OptimizedHistoricalAcceptanceAt  -- The pre-2a acceptance
def DEP : Name := ``Nock.NockVMROM.Thm54.DeployedAcceptanceAt
def STMT : Name := ``OptimizedFullStrictThm54Statement

def accFields : List Name :=
  [`p8, `same_problem, `sampled_io_coins, `memory_sampled_coins,
   `memory_intermediate_pole, `compute_satisfies, `memory_satisfies]

/-- Honest package fields a family-chip restatement must NOT read (the coins of the
compiler); plus the honest strategy / objects / containment. -/
def honestNames : List Name :=
  [``OptimizedStrictNockVMROMPackage.computeChallengePins,
   ``OptimizedStrictNockVMROMPackage.memoryCoordinatePins,
   ``OptimizedStrictNockVMROMPackage.family_cfg,
   ``OptimizedFullStrictNockVMROMPackage.honestSeed_ne,
   ``OptimizedFullStrictNockVMROMPackage.honest_specialization,
   ``OptimizedFullStrictNockVMROMPackage.strategy,
   ``OptimizedFullStrictNockVMROMPackage.objects,
   ``OptimizedFullStrictNockVMROMPackage.containment]

def chain : List Name :=
  [``OptimizedHostileTimestamps.hz0_of_good,
   ``OptimizedHostileTimestamps.chipAlpha_eq_alphaM,
   ``OptimizedHostileTimestamps.hostile_LIO',
   ``OptimizedHostileTimestamps.optimizedFullStrict_hostile_LIO_historical,
   ``ResponseTsMemPowers.response_ts_mem_powers,
   ``MemoryInternalPole.optimizedFullStrict_paired_records,
   ``Nock.RedTeam.Batch522.remainingActiveMemPower_of_deployed]

def stmtFields : List Name :=
  [`structural, `optimized_chips, `shared_io, `perfect_completeness, `containment,
   `walk_bounds, `p8_fixed_field_soundness, `p8_fixed_field_bits, `acceptance_to_target,
   `complete_false_acceptance_bound, `complete_false_acceptance_bits,
   `staged_false_acceptance_bound, `exact_resources,
   `row_budgets, `shared_forest_axis]

def pinnedTargets : List (String × Name) :=
  [("AcceptanceAt", ``OptimizedFullStrictNockVMROMPackage.OptimizedProductionAcceptanceAt),
   ("GenuineTargetAt", ``OptimizedFullStrictNockVMROMPackage.OptimizedProductionGenuineTargetAt),
   ("optimizedFailureEvent", ``OptimizedFullStrictNockVMROMPackage.optimizedFailureEvent),
   ("consumedFailureEvent", ``OptimizedFullStrictNockVMROMPackage.consumedFailureEvent),
   ("AcceptanceAt309", ``PartAStaged.AcceptanceAt309),
   ("GenuineTargetAt309", ``OptimizedFullStrictNockVMROMPackage.OptimizedProductionGenuineTargetAt309),
   ("consumedFailureEvent309", ``PartAStaged.consumedFailureEvent309),
   ("StagedTraces12", ``PartAStaged.StagedTraces12),
   ("workloadEv", ``OptimizedFailureEventEv.workloadEv),
   ("OptimizedFalseAcceptanceSet", ``OptimizedFullStrictNockVMROMPackage.OptimizedFalseAcceptanceSet),
   ("computeChip", ``OptimizedFullStrictNockVMROMPackage.computeChip),
   ("memoryChip", ``OptimizedFullStrictNockVMROMPackage.memoryChip),
   ("strategy", ``OptimizedFullStrictNockVMROMPackage.strategy),
   ("census", ``OptimizedStrictNockVMROMPackage.census),
   ("workload", ``ProductionP8Containment.workload),
   ("FailureUnion", ``ProductionP8Containment.FailureUnion)]

def unionSummands : List Name :=
  [``Nock.NockVMROM.Thm54.zeroSeedFailureEvent,
   ``Nock.NockVMROM.Thm54.collisionFailureEvent,
   ``TemplateRawJointSoundness.specializedTopologyFailureEvent,
   ``ProductionP8Containment.guardedAxisFailureEvent,
   ``SizeWindowCounting.SizeWindowFailure]

run_cmd do
  let env ← getEnv
  for n in honestNames ++ chain ++ unionSummands ++ (pinnedTargets.map (·.2)) do need env n
  need env DEP
  -- §B
  let rIff := reachSet env ``OptimizedFullStrictNockVMROMPackage.optimizedHistoricalAcceptanceAt_iff
  for f in accFields do
    unless rIff.contains (ACC ++ f) do
      throwError m!"positive control: optimizedProductionAcceptanceAt_iff does not reach {f}"
  let rPkg := reachSet env ``OptimizedHostileTimestamps.hz0_of_package
  unless rPkg.contains ``OptimizedFullStrictNockVMROMPackage.honestSeed_ne do
    throwError "positive control: hz0_of_package does not reach honestSeed_ne"
  for t in chain do
    let r := reachSet env t
    let pins := accFields.filter fun f => r.contains (ACC ++ f)
    let hon := honestNames.filter fun h => r.contains h
    let typedAtConst := typeMentions env t ACC
    let typedAtFamily := typeMentions env t DEP
    logInfo m!"B {t}: type@AcceptanceAt={typedAtConst} type@DeployedAcceptanceAt={typedAtFamily} pins={pins} honest={hon} reach={r.size}"
    unless typedAtConst do throwError m!"B: {t} is not typed at OptimizedProductionAcceptanceAt"
    if typedAtFamily then throwError m!"B: {t} is typed at DeployedAcceptanceAt — measurement moved"
  -- the hand-read pin reads
  let rA := reachSet env ``OptimizedHostileTimestamps.chipAlpha_eq_alphaM
  unless rA.contains (ACC ++ `same_problem) do throwError "B: chipAlpha_eq_alphaM lost same_problem"
  unless rA.contains ``OptimizedStrictNockVMROMPackage.computeChallengePins do
    throwError "B: chipAlpha_eq_alphaM does not reach computeChallengePins"
  let rZ := reachSet env ``OptimizedHostileTimestamps.hz0_of_good
  unless rZ.contains (ACC ++ `same_problem) do throwError "B: hz0_of_good lost same_problem"
  let rL := reachSet env ``OptimizedHostileTimestamps.hostile_LIO'
  unless rL.contains (ACC ++ `sampled_io_coins) do throwError "B: hostile_LIO' lost sampled_io_coins"
  unless rL.contains ``OptimizedStrictNockVMROMPackage.computeChallengePins do
    throwError "B: hostile_LIO' does not reach computeChallengePins"
  let rP := reachSet env ``MemoryInternalPole.optimizedFullStrict_paired_records
  unless rP.contains (ACC ++ `memory_sampled_coins) do throwError "B: paired_records lost memory_sampled_coins"
  unless rP.contains (ACC ++ `memory_intermediate_pole) do throwError "B: paired_records lost memory_intermediate_pole"
  let rF := reachSet env ``OptimizedHostileTimestamps.optimizedFullStrict_hostile_LIO_historical
  logInfo m!"B optimizedFullStrict_hostile_LIO reaches p8={rF.contains (ACC ++ `p8)} (it consumes the opaque Statement field acceptance_to_target, so the honest p8 conjunct is behind a projection)"
  -- global scan: does ANY Nock.* theorem conclude LIO / MemPower / paired records from DeployedAcceptanceAt?
  let goals : List Name := [``Nock.IO.LIO, ``ResponseTsMemPowers.MemPower,
    ``MemoryInternalPole.hostileReads]
  for g in goals do need env g
  let mut fromDeployed : List Name := []
  let mut deployedConsumers : Nat := 0
  for (n, ci) in env.constants.toList do
    if (`Nock).isPrefixOf n && !n.isInternal then
      let used := ci.type.getUsedConstants
      if used.contains DEP then
        deployedConsumers := deployedConsumers + 1
        if goals.any used.contains then fromDeployed := fromDeployed ++ [n]
  logInfo m!"B DeployedAcceptanceAt appears in the type of {deployedConsumers} Nock.* declarations; those also mentioning IO.LIO / MemPower / hostileReads: {fromDeployed}"
  unless fromDeployed.isEmpty do
    logInfo m!"B (36th): theorems concluding LIO/MemPower from DeployedAcceptanceAt: {fromDeployed}"
  unless typeMentions env ``OptimizedHostileTimestamps.optimizedFullStrict_hostile_LIO_historical ``Nock.IO.LIO do
    throwError "B positive control: optimizedFullStrict_hostile_LIO type does not mention IO.LIO"
  unless typeMentions env ``Nock.RedTeam.Batch489.tracesWalkHyps_of_deployed DEP do
    throwError "B positive control: Batch489.tracesWalkHyps_of_deployed is not typed at DeployedAcceptanceAt"
  -- §C: which summands of FailureUnion read the census, and what of it
  let badSeeds := ``Nock.NockVMROM.Thm54.ComparisonCensus.badSeeds
  let pairs := ``Nock.NockVMROM.Thm54.ComparisonCensus.pair
  let count := ``Nock.NockVMROM.Thm54.ComparisonCensus.count
  need env badSeeds; need env pairs; need env count
  let rU := reachSet env ``ProductionP8Containment.FailureUnion
  for s in unionSummands do
    unless rU.contains s do throwError m!"C: FailureUnion does not reach summand {s}"
    let r := reachSet env s
    logInfo m!"C summand {s}: badSeeds={r.contains badSeeds} pair={r.contains pairs} count={r.contains count}"
  let rColl := reachSet env ``Nock.NockVMROM.Thm54.collisionFailureEvent
  unless rColl.contains badSeeds do throwError "C: collisionFailureEvent does not reach badSeeds"
  unless rColl.contains pairs do throwError "C: collisionFailureEvent does not reach the census pair list"
  for s in unionSummands do
    if s != ``Nock.NockVMROM.Thm54.collisionFailureEvent then
      if (reachSet env s).contains badSeeds then
        throwError m!"C: summand {s} reads the census — measurement moved"
  -- c-freeness at the type level
  let tuple := ``OptimizedStrictPackage.OptimizedProductionChallengeTuple
  need env tuple
  if typeMentions env ``StrategyOfTraces.decodedSkeletonOf tuple then
    throwError "C: decodedSkeletonOf mentions the tuple"
  unless typeMentions env ``StrategyOfTracesCore.strategyOfTraces tuple do
    throwError "C: strategyOfTraces does not mention the tuple"
  unless typeMentions env ``StrategyOfTracesCore.verifierOfTraces tuple do
    throwError "C: verifierOfTraces does not mention the tuple"
  unless typeMentions env ``ExecOfTraces.execOfTraces tuple do
    throwError "C: execOfTraces does not mention the tuple"
  logInfo "C decodedSkeletonOf is c-free (type); strategyOfTraces / verifierOfTraces / execOfTraces take c"
  let rEv := reachSet env ``OptimizedFullStrictNockVMROMPackage.optimizedFailureEvent
  unless rEv.contains ``OptimizedFullStrictNockVMROMPackage.strategy do
    throwError "C: optimizedFailureEvent does not reach the honest P.strategy"
  if rEv.contains ``StrategyOfTraces.decodedSkeletonOf then
    throwError "C: optimizedFailureEvent reaches decodedSkeletonOf"
  let mut hits : List (Name × List String) := []
  for f in stmtFields do
    let names := (pinnedTargets.filter fun (_, t) => typeMentions env (STMT ++ f) t).map (·.1)
    hits := hits ++ [(f, names)]
    logInfo m!"D Statement.{f} type mentions: {names}"
  let want (f : Name) (s : String) : CommandElabM Unit := do
    match hits.find? (·.1 == f) with
    | some (_, names) => unless names.contains s do throwError m!"D: Statement.{f} does not mention {s}"
    | none => throwError m!"D: field {f} missing"
  want `acceptance_to_target "AcceptanceAt309"
  want `acceptance_to_target "GenuineTargetAt309"
  want `acceptance_to_target "consumedFailureEvent309"
  want `complete_false_acceptance_bound "AcceptanceAt309"
  want `complete_false_acceptance_bound "GenuineTargetAt309"
  want `staged_false_acceptance_bound "StagedTraces12"
  want `staged_false_acceptance_bound "GenuineTargetAt309"
  want `complete_false_acceptance_bound "workloadEv"
  want `complete_false_acceptance_bits "GenuineTargetAt309"
  want `containment "census"
  want `containment "FailureUnion"
  want `row_budgets "computeChip"
  let nAcc := (hits.filter fun (_, ns) => ns.contains "AcceptanceAt").length
  let nEv := (hits.filter fun (_, ns) => ns.contains "optimizedFailureEvent").length
  let nChip := (hits.filter fun (_, ns) => ns.contains "computeChip").length
  let nStrat := (hits.filter fun (_, ns) => ns.contains "strategy").length
  let nCensus := (hits.filter fun (_, ns) => ns.contains "census").length
  logInfo m!"D counts over 15 pinned fields: AcceptanceAt={nAcc} optimizedFailureEvent={nEv} computeChip={nChip} strategy={nStrat} census={nCensus}"
  let nz := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
  need env nz
  for (s, t) in pinnedTargets do
    if s != "strategy" && typeMentions env nz t then
      throwError m!"D: nockCompiles_zmod type mentions {s} directly"
  unless typeMentions env nz STMT do throwError "D: nockCompiles_zmod does not mention the Statement"
  logInfo "D nockCompiles_zmod: type names the Statement and none of the pinned-field internals directly"
  -- §E
  let rS := reachSet env ``StrategyOfTracesCore.strategyOfTraces
  let objs := ``OptimizedFullStrictNockVMROMPackage.objects
  let rootPos := ``Nock.NockVMROM.Thm54.ExactExecution.memoryRootCount_pos
  need env rootPos
  logInfo m!"E strategyOfTraces reaches P.objects={rS.contains objs} memoryRootCount_pos={rS.contains rootPos} P.strategy={rS.contains ``OptimizedFullStrictNockVMROMPackage.strategy}"
  unless rS.contains objs do throwError "E: strategyOfTraces does not reach P.objects — measurement moved"
  if rS.contains ``OptimizedFullStrictNockVMROMPackage.strategy then
    throwError "E: strategyOfTraces reaches the honest P.strategy"
  let hop := ``Nock.NockVMROM.Thm54.BoundSemanticTrace.SkeletonOperationalCore
  need env hop
  unless typeMentions env ``ProductionP8Containment.accepted_outside_failureUnion_at hop do
    throwError "E: accepted_outside_failureUnion_at type does not mention SkeletonOperationalCore"
  let rWrap := reachSet env ``Nock.RedTeam.Batch533.templateAxisPolynomial_eval_of_remaining
  logInfo m!"E Batch533.templateAxisPolynomial_eval_of_remaining reaches SkeletonOperationalCore={rWrap.contains hop} P.strategy={rWrap.contains ``OptimizedFullStrictNockVMROMPackage.strategy}"

end Nock.RedTeam.Batch574

#print axioms Nock.RedTeam.Batch574.rowEnvAt_alphaM
#print axioms Nock.RedTeam.Batch574.rowEnvAt_seed
#print axioms Nock.RedTeam.Batch574.rowCoinsAt_eq_sampledCoins
#print axioms Nock.RedTeam.Batch574.family_memory_pins
#print axioms Nock.RedTeam.Batch574.activeMask_at_eq
#print axioms Nock.RedTeam.Batch574.rowRecord_at_eq
#print axioms Nock.RedTeam.Batch574.rowRecord_ts_at_reads_tuple_alpha
#print axioms Nock.RedTeam.Batch574.ts_coordinate_not_traceOnly
#print axioms Nock.RedTeam.Batch574.rowRequests_length_at_eq
#print axioms Nock.RedTeam.Batch574.lblMAt_z_is_tuple
#print axioms Nock.RedTeam.Batch574.lblCAt_alpha_is_tuple
