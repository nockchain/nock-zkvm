/-
  Nock/RedTeam/Batch817Thm54H13ConsumeReplicas.lean

* Verbatim replicas reproduce the live pins of `pricedWalkWork` (`18169742864994646756`) and
    `workload` (`4732004488502045126`); the `OptimizedHostileProductionFailureEvent` replica does
    NOT reproduce its pin (`5727737878319466766`; instance-path difference — reported, not hidden),
    so its arity control is replica-vs-replica.
  * Both candidate homes for the summand fire: Option P (`pricedWalkWork` gains `Λg`, arity) and
    Option W (`workload` gains `reqPairWorkload T Λ`, value).
  * The draft text's three negative controls fire on the constants they name: (i) the guard
    `Λ → Λ + 1` fires `guardedPairs` (NOT `pairBadSeeds`, whose body names `guardedCensus` by name);
    (ii) `natLift reqIdx + 1` fires `reqTgtOfEnvs`; (iii) `+ 0` fires `reqPairWorkload`.
  * **Rule 4(c) at the base:**
    adding the nine existing proposed watchlist names gives exactly those nine `UNPINNED`, 483
    unchanged, nothing fired, 492 total. (`FrozenClosure.lean` needs
    `import Nock.NockVMROM.Thm54.PreZCensusCore` for the watchlist step BEFORE the pinned file
    imports it.)

  -- the paper
-/
import Lean
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.PreZCensusCore
import Nock.NockVMROM.Thm54.PreSeedCensusFigures
import Nock.NockVMROM.Thm54.HostileWorkloadMajorant
import Nock.RedTeam.Batch742Thm54RouteBCensus
import Nock.RedTeam.Batch752Thm54PreZCensusCoreLift
import Nock.RedTeam.Batch816Thm54H13ConsumeSlot

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

open Lean Elab Command

namespace Nock.RedTeam.Batch817

open Nock
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.PreSeedCensusFigures
open Nock.NockVMROM.Thm54.HostileWorkloadMajorant
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.Reified
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound

noncomputable section
open Nock.RedTeam.Batch816 (reqPairWorkload reqPairWorkloadPert)

/-! ## C. Replica fingerprints (rule 6) -/

section Replicas
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
  [DecidableEq F] [DecidableEq K] [CharP K (ringChar K)]

/-- Verbatim live `pricedWalkWork`. -/
def pwLive (N M : ℕ) : ℕ :=
  ComputeWalkRootEvents.walkRootBound N +
    WalkTilingEvents.computeTilingBound N +
    WalkTilingEvents.memoryTilingBound M +
    WalkPrefixGammaEvents.computePrefixGammaBound N +
    WalkPrefixGammaEvents.memoryPrefixGammaBound M +
    WalkForestPrefixAlphaEvents.memoryForestAlphaBound M

/-- Option P: `pricedWalkWork` gains the window argument (arity change). -/
def pwLam (N M Λg : ℕ) : ℕ :=
  ComputeWalkRootEvents.walkRootBound N +
    WalkTilingEvents.computeTilingBound N +
    WalkTilingEvents.memoryTilingBound M +
    WalkPrefixGammaEvents.computePrefixGammaBound N +
    WalkPrefixGammaEvents.memoryPrefixGammaBound M +
    WalkForestPrefixAlphaEvents.memoryForestAlphaBound M +
    M * (2 * Λg - 1)

/-- Verbatim live `workload`. -/
def wLive (T : ProductionStrategy F K) (Λ topologyWorkload axisWorkload : ℕ) : ℕ :=
  1 +
    (3 + 19 *
      (SemanticStrategy.computeSkeletonRows T.skeleton).length) *
        (2 * Λ - 1) +
    topologyWorkload + axisWorkload + formRUniformWorkload T + sizeWindowRootBound Λ

/-- Option W: `workload` gains the pair summand (value change, same arity). -/
def wPair (T : ProductionStrategy F K) (Λ topologyWorkload axisWorkload : ℕ) : ℕ :=
  1 +
    (3 + 19 *
      (SemanticStrategy.computeSkeletonRows T.skeleton).length) *
        (2 * Λ - 1) +
    topologyWorkload + axisWorkload + formRUniformWorkload T +
    ProductionP8Containment.reqPairWorkload T Λ +
    sizeWindowRootBound Λ

end Replicas

section ReplicasHPFE
open scoped Classical
open Nock.Framework Nock.NockVMROM
/-- Live `OptimizedHostileProductionFailureEvent`, restated at the H1.5b Part 2a shape (the IO
records argument replaced by the family IO Finset `famIO`, unioned after the P8 lift; binders as live; the
`CharP` instance is Mathlib's `ringChar.charP`, not a section variable). -/
def hpeLive
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M : ℕ}
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (famIO : Finset (OptimizedProductionChallengeTuple K F)) (D : ℕ)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F)
    (interRecords : FiniteIO.PreChallengeRecords K 10)
    (memoryEnvF : Fin M → Env F)
    (walkRoot : Finset (JointCoins K))
    (tilingC : Finset (JointCoins K))
    (tilingM : Finset (JointCoins K))
    (gammaC : Finset (JointCoins K))
    (gammaM : Finset (JointCoins K))
    (forestAlpha : Finset (JointCoins K))
    (formRLambda : Finset (OptimizedProductionChallengeTuple K F)) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
      memoryEnvK memoryFamilies ∪
    famIO ∪
    liftTimestampFailure (OptimizedHostileTimestamps.TimestampCollisionEvent D) ∪
    liftInterPoleFailure (interFailurePairs interRecords memoryEnvK memoryEnvF) ∪
    liftP8Failure walkRoot ∪
    liftP8Failure tilingC ∪
    liftP8Failure tilingM ∪
    liftP8Failure gammaC ∪
    liftP8Failure gammaM ∪
    liftP8Failure forestAlpha ∪
    formRLambda

/-- With the pair parameter (both options). -/
def hpePair
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M : ℕ}
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (famIO : Finset (OptimizedProductionChallengeTuple K F)) (D : ℕ)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F)
    (interRecords : FiniteIO.PreChallengeRecords K 10)
    (memoryEnvF : Fin M → Env F)
    (walkRoot : Finset (JointCoins K))
    (tilingC : Finset (JointCoins K))
    (tilingM : Finset (JointCoins K))
    (gammaC : Finset (JointCoins K))
    (gammaM : Finset (JointCoins K))
    (forestAlpha : Finset (JointCoins K))
    (formRLambda : Finset (OptimizedProductionChallengeTuple K F))
    (pairSeeds : Finset (JointCoins K)) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
      memoryEnvK memoryFamilies ∪
    famIO ∪
    liftTimestampFailure (OptimizedHostileTimestamps.TimestampCollisionEvent D) ∪
    liftInterPoleFailure (interFailurePairs interRecords memoryEnvK memoryEnvF) ∪
    liftP8Failure walkRoot ∪
    liftP8Failure tilingC ∪
    liftP8Failure tilingM ∪
    liftP8Failure gammaC ∪
    liftP8Failure gammaM ∪
    liftP8Failure forestAlpha ∪
    formRLambda ∪
    liftP8Failure pairSeeds

end ReplicasHPFE

section ReplicasGP
/-- Verbatim `guardedPairs`. -/
def gpLive (Λ : ℕ) (pairs : List (Noun × Noun)) : List (Noun × Noun) :=
  pairs.filter fun p => decide (p.1.leaves ≤ Λ ∧ p.2.leaves ≤ Λ)

/-- Negative control (i): guard `Λ → Λ + 1`. -/
def gpPert (Λ : ℕ) (pairs : List (Noun × Noun)) : List (Noun × Noun) :=
  pairs.filter fun p => decide (p.1.leaves ≤ Λ + 1 ∧ p.2.leaves ≤ Λ + 1)

end ReplicasGP

section ReplicasEnv
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {M : ℕ}

/-- Verbatim `reqTgtOfEnvs`. -/
def rtLive (envs : Fin M → Env F) (hM : 0 < M) (T : MState → ℕ → Noun) : ℕ → Noun :=
  fun j => T (preLblOfEnvs envs hM j).1 (RecordCarrier.natLift (preReqIdxOfEnvs envs hM j))

/-- Negative control (ii): index `+ 1`. -/
def rtPert (envs : Fin M → Env F) (hM : 0 < M) (T : MState → ℕ → Noun) : ℕ → Noun :=
  fun j => T (preLblOfEnvs envs hM j).1 (RecordCarrier.natLift (preReqIdxOfEnvs envs hM j) + 1)

end ReplicasEnv

/-- `FrozenClosure.meaningExprs`, copied (the dumper stays out of the build). -/
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
  let R := `Nock.RedTeam.Batch817
  let SP := `Nock.NockVMROM.Thm54.OptimizedStrictPackage
  let PP := `Nock.NockVMROM.Thm54.ProductionP8Containment
  let PS := `Nock.NockVMROM.Thm54.PreSeedCensus
  let pw := fp env (SP ++ `pricedWalkWork)
  let w := fp env (PP ++ `workload)
  let hpe := fp env (SP ++ `OptimizedHostileProductionFailureEvent)
  logInfo m!"pricedWalkWork live {pw}; pwLive {fp env (R ++ `pwLive)}; pwLam {fp env (R ++ `pwLam)}"
  logInfo m!"workload live {w}; wLive {fp env (R ++ `wLive)}; wPair {fp env (R ++ `wPair)}"
  logInfo m!"OptimizedHostileProductionFailureEvent live {hpe}; hpeLive {fp env (R ++ `hpeLive)}; hpePair {fp env (R ++ `hpePair)}"
  logInfo m!"guardedPairs live {fp env (PS ++ `guardedPairs)}; gpLive {fp env (R ++ `gpLive)}; gpPert {fp env (R ++ `gpPert)}"
  logInfo m!"reqTgtOfEnvs live {fp env (PS ++ `reqTgtOfEnvs)}; rtLive {fp env (R ++ `rtLive)}; rtPert {fp env (R ++ `rtPert)}"
  logInfo m!"reqPairWorkload {fp env `Nock.RedTeam.Batch816.reqPairWorkload}; reqPairWorkloadPert {fp env `Nock.RedTeam.Batch816.reqPairWorkloadPert}"
  logInfo m!"pairBadSeeds live {fp env (PS ++ `pairBadSeeds)}; guardedCensus live {fp env (PS ++ `guardedCensus)}"
  unless pw == 18169742864994646756 ∧ fp env (R ++ `pwLive) == pw do throwError "pricedWalkWork verbatim"
  unless fp env (R ++ `pwLam) != pw do throwError "Option P arity perturbation did not fire"

  -- `5538245203494781706 → 12234146441259373986`; the pre-move body `wLive` still reproduces the old
  -- pin, and `wPair` (now naming the production `reqPairWorkload`) reproduces the new one (NC (iv)).
  unless fp env (R ++ `wLive) == 4732004488502045126 do throwError "workload pre-move verbatim"
  unless w == 15921568493750301756 ∧ fp env (R ++ `wPair) == w do throwError "workload re-pin verbatim"
  unless fp env (R ++ `wLive) != w do throwError "the move did not fire workload"

  unless hpe == 8307282949885789412 do throwError "HPFE re-pinned value"
  if fp env (R ++ `hpeLive) == hpe then logInfo "hpeLive reproduces the live pin" else logInfo "hpeLive does NOT reproduce the live pin (instance-path difference; arity control below is replica-vs-replica)"
  unless fp env (R ++ `hpePair) != fp env (R ++ `hpeLive) do throwError "HPFE parameter did not fire (replica pair)"
  unless fp env (R ++ `gpLive) == fp env (PS ++ `guardedPairs) do throwError "guardedPairs verbatim"
  unless fp env (R ++ `gpPert) != fp env (PS ++ `guardedPairs) do throwError "control (i) did not fire"
  unless fp env (R ++ `rtLive) == fp env (PS ++ `reqTgtOfEnvs) do throwError "reqTgtOfEnvs verbatim"
  unless fp env (R ++ `rtPert) != fp env (PS ++ `reqTgtOfEnvs) do throwError "control (ii) did not fire"
  unless fp env `Nock.RedTeam.Batch816.reqPairWorkloadPert != fp env `Nock.RedTeam.Batch816.reqPairWorkload do throwError "control (iii) did not fire"

  unless fp env (PP ++ `reqPairWorkload) == 16685327008963352002 ∧
      fp env `Nock.RedTeam.Batch816.reqPairWorkload == 16685327008963352002 do
    throwError "production reqPairWorkload is not the Batch816 replica"
  -- instrument positive controls (two pre-existing frontier pins)
  unless fp env `Nock.NockVMROM.Thm54.alphaM == 937637267857755379 ∧
      fp env `Nock.Walk.Sf == 324224195579837053 do throwError "instrument positive control"
  logInfo "replicas: verbatim replicas reproduce the pricedWalkWork and workload pins (the hostile-event replica does not); both design perturbations and the three negative controls fire"


/-! So the watchlist entry is what catches it. -/
run_cmd do
  let env ← getEnv
  let PP := `Nock.NockVMROM.Thm54.ProductionP8Containment
  let ws := (meaningExprs env (PP ++ `workload)).foldl (init := ({} : NameSet)) fun acc e =>
    e.getUsedConstants.foldl (init := acc) fun a c => a.insert c
  unless ws.contains (PP ++ `reqPairWorkload) do throwError "workload does not name reqPairWorkload"
  if ws.contains ``Max.max then throwError "workload's own exprs contain reqPairWorkload's body"
  let rs := (meaningExprs env (PP ++ `reqPairWorkload)).foldl (init := ({} : NameSet)) fun acc e =>
    e.getUsedConstants.foldl (init := acc) fun a c => a.insert c
  unless rs.contains ``Max.max do throwError "positive control: reqPairWorkload body lacks Max.max"
  logInfo "NC (iii): workload names reqPairWorkload by constant only; its body (Max.max) is not hashed into workload"


run_cmd do
  let env ← getEnv
  let PS := `Nock.NockVMROM.Thm54.PreSeedCensus
  let expected : Array (Name × UInt64) := #[
    (PS ++ `decodePre, 11249868532285631401),
    (PS ++ `guardedCensus, 11214531059870353042),
    (PS ++ `guardedPairs, 3423436599348089555),
    (PS ++ `pairBadSeeds, 8523380660461741701),
    (PS ++ `preZNounOfEnvs, 7205641367958600191),
    (PS ++ `reqPairEventOfEnvs, 6264743203847467740),
    (PS ++ `reqTgtOfEnvs, 3312615697292535736),
    (PS ++ `requestTargets, 2260074138106044861),
    (`Nock.NockVMROM.Thm54.StrategyOfTraces.memoryStateOf, 13906310903953858646)]
  for (n, h) in expected do
    unless fp env n == h do throwError m!"rule-4(c) base fingerprint moved: {n} = {fp env n}, recorded {h}"
  -- the frontier pins this move's two candidate designs touch, at the base
  unless fp env `Nock.NockVMROM.Thm54.OptimizedStrictPackage.optimizedHostileProductionFailureProbabilityBound
      == 4151372547021390543 do throwError "ProbabilityBound base pin"
  logInfo "rule4c_base: the nine proposed watchlist names and the ProbabilityBound frontier pin are at their 137d1528 values"

end

end Nock.RedTeam.Batch817
