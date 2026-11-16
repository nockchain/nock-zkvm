import Nock.RedTeam.Batch817Thm54H13ConsumeReplicas

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!

Standing rule 6: negative controls by replica fingerprint, never by perturbing production and
rebuilding above the pinned file.

**A. `hostileRecords` / `hostileInterRecords` are WATCHLISTED (`FrozenClosure.lean`), so — contrary
to the scoping draft's prediction — `hostileRecords` does NOT leave the frontier when the
event stops reading it; it stays pinned at its current value.

**B. Replica pairs for the two ring-one constants 2a changes.**
* `opfeLive` is a verbatim replica of `OptimizedProductionFailureEvent`; `opfeNoIO` is the same
  without the `liftIOFailure (IOFailureEvent records)` summand and the `records` parameter
  (the 2a shape: the IO lift LEAVES this union).  Replica-vs-replica: they differ.
* `hpeLive` is a verbatim replica of `OptimizedHostileProductionFailureEvent` (binders exactly as
  live at QD); `hpeFam` is the 2a shape: `records` gone, a new `famIO: Finset tuple` parameter
  unioned in its place; `hpeFamPert` is the signature-preserving `famIO ∪ ∅` perturbation. Replica-vs-replica: `hpeFam ≠ hpeLive` (the design change fires) and `hpeFamPert ≠ hpeFam`
  (the famIO slot is itself guarded). -/

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean Elab Command

namespace Nock.RedTeam.Batch882

open Nock
open Nock.NockVMROM.Thm54
open Nock.Reified
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.RedTeam.Batch817 (fp)

noncomputable section

section Replicas
open scoped Classical
open Nock.Framework Nock.NockVMROM

/-- Verbatim replica of `OptimizedProductionFailureEvent` at QD. -/
def opfeLive
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M m : ℕ}
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (records : FiniteIO.PreChallengeRecords K m)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (_computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (_memoryFamilies : Fin M → Fin 7 → Fin 3 → F) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  liftP8Failure (ProductionP8Containment.FailureUnion T C lmb) ∪
    liftIOFailure (FiniteIO.IOFailureEvent records)

/-- The 2a shape: the package-chip IO lift LEAVES the union (`records` parameter deleted). -/
def opfeNoIO
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M : ℕ}
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (_computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (_memoryFamilies : Fin M → Fin 7 → Fin 3 → F) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  liftP8Failure (ProductionP8Containment.FailureUnion T C lmb)

/-- Verbatim replica of `OptimizedHostileProductionFailureEvent` at QD. -/
def hpeLive
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M m : ℕ}
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (records : FiniteIO.PreChallengeRecords K m) (D : ℕ)
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
  opfeLive T C lmb records computeEnvK computeWalkEnv computeEnvF
      memoryEnvK memoryFamilies ∪
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

/-- The 2a shape: `records` gone, the family IO event `famIO` unioned in its place. -/
def hpeFam
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
  opfeNoIO T C lmb computeEnvK computeWalkEnv computeEnvF memoryEnvK memoryFamilies ∪
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

/-- Signature-preserving perturbation of the `famIO` slot: `famIO ∪ ∅`. -/
def hpeFamPert
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
  opfeNoIO T C lmb computeEnvK computeWalkEnv computeEnvF memoryEnvK memoryFamilies ∪
    (famIO ∪ ∅) ∪
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

end Replicas

end

/-! ## A. The rule-4(c) base at QD: the must-not-fire list -/

run_cmd do
  let env ← getEnv
  let SP := `Nock.NockVMROM.Thm54.OptimizedStrictPackage
  let PP := `Nock.NockVMROM.Thm54.ProductionP8Containment
  let SF := `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage
  let IO := `Nock.NockVMROM.Thm54.FiniteIO
  let CA := `Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
  let MA := `Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator

  let base : List (Name × UInt64) :=
    [ (SP ++ `pricedWalkWork, 18169742864994646756),
      (PP ++ `workload, 15921568493750301756),

      -- HPFE 217319820750748878 → 10885927128798943981, OPFE 6386915887416652064 → 912960407023990049.
      (SP ++ `OptimizedHostileProductionFailureEvent, 8307282949885789412),
      (SP ++ `OptimizedProductionFailureEvent, 7375876556367992980),
      (SP ++ `optimizedHostileProductionFailureProbabilityBound, 4151372547021390543),
      (SP ++ `optimizedTrimmedProductionFailureProbabilityBound, 17496478639357101379),
      (SP ++ `liftTimestampFailure, 2867682284276148602),
      (SP ++ `OptimizedProductionChallengeTuple, 16850678248062519848),
      (CA ++ `rowRecord, 9901740391636565785),
      (CA ++ `rowRequests, 8012589053453106658),
      (MA ++ `rowRecord, 17753608400835885598),
      (MA ++ `rowResponses, 15636281122160784598),
      (SF ++ `hostileRecords, 15352673378135290329),
      (SF ++ `hostileInterRecords, 7508517569764433093),
      (IO ++ `IOFailureEvent, 8700560956119216828),
      (IO ++ `ioFailureUnionBound, 9536893440702375137),
      (IO ++ `FiniteIOStrategy.coins, 8694620852118388483),
      (`Nock.NockVMROM.Thm54.PreSeedCensus.reqPairEventOfEnvs, 6264743203847467740),
      (`Nock.NockVMROM.Thm54.DecodedLambdaEvent.decodedLambdaEventOfEnvs, 2686192200415174578),
      (`Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.TimestampCollisionEvent, 15293326475303509693),
      (PP ++ `ProductionStrategy.Accepts, 15304029928102155659),
      (PP ++ `GenuineTargetAt, 1902367073877427371) ]
  for (n, h) in base do
    unless fp env n == h do
      throwError m!"rule-4(c) base fingerprint moved: {n} = {fp env n}, recorded {h}"
  logInfo m!"rule-4(c) base (QD, two re-pinned at 2a): all {base.length} recorded fingerprints reproduce"

/-! ## B. The replica pairs -/

run_cmd do
  let env ← getEnv
  let R := `Nock.RedTeam.Batch882
  let SP := `Nock.NockVMROM.Thm54.OptimizedStrictPackage
  let opfe := fp env (SP ++ `OptimizedProductionFailureEvent)
  let hpe := fp env (SP ++ `OptimizedHostileProductionFailureEvent)
  logInfo m!"OptimizedProductionFailureEvent live {opfe}; opfeLive {fp env (R ++ `opfeLive)}; opfeNoIO {fp env (R ++ `opfeNoIO)}"
  logInfo m!"OptimizedHostileProductionFailureEvent live {hpe}; hpeLive {fp env (R ++ `hpeLive)}; hpeFam {fp env (R ++ `hpeFam)}; hpeFamPert {fp env (R ++ `hpeFamPert)}"
  if fp env (R ++ `opfeLive) == opfe then logInfo "opfeLive reproduces the live pin"
    else logInfo "opfeLive does NOT reproduce the live pin (instance-path difference; controls are replica-vs-replica)"
  if fp env (R ++ `hpeLive) == hpe then logInfo "hpeLive reproduces the live pin"
    else logInfo "hpeLive does NOT reproduce the live pin (instance-path difference, as Batch817 N3; controls are replica-vs-replica)"
  unless fp env (R ++ `opfeNoIO) != fp env (R ++ `opfeLive) do
    throwError "removing the IO lift from OptimizedProductionFailureEvent did not fire (replica pair)"
  unless fp env (R ++ `hpeFam) != fp env (R ++ `hpeLive) do
    throwError "the famIO parameter did not fire OptimizedHostileProductionFailureEvent (replica pair)"
  unless fp env (R ++ `hpeFamPert) != fp env (R ++ `hpeFam) do
    throwError "the famIO slot perturbation did not fire (replica pair)"
  logInfo "replica controls: IO-lift removal fires OPFE; famIO parameter fires HPFE; famIO ∪ ∅ fires HPFE"

end Nock.RedTeam.Batch882
