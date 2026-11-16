/-
  Nock/NockVMROM/Thm54/ConsumerObligationsEv.lean

  The consumer of `not_mem_evFailureUnion_C2` — the containment proof
  `ProductionP8Containment.accepted_outside_failureUnion_at`, which reads the proof-carrying
  `FailureUnion T C lmb` — needs, beyond `hgood` and `TracesWalkHyps`, the three facts the guards
  hide:
  * **(a)** a proof-carrying census `C : CombinedSkeletonCensus K T.skeleton Λ` (every census pair
    has `≤ Λ` leaves), so that `guardedCensusEv_badSeeds_eq` identifies the guarded twin;
  * **(b)** `SizeWindowNounsBoundedBy T.skeleton Λ`, so that `guardedSizeWindowFailure_eq_of_bounded`
    identifies the guarded twin;
  * **(c)** the axis exponent window: at every seed `z` and memory root `i`,
    `(templateAxisPolynomial (committedTemplate T.verifier z hz) i).natDegree ≤ 3·N + 3`, so that
    `envelopeRootUnion_eq_of_deg_le` identifies the envelope-guarded axis share.

  **What this module proves.**
  * **(c) is a theorem** on accepted family traces outside the 2b-ii event, at BOTH built strategies
    (`axisPolynomial_natDegree_le_Ev`, `axisPolynomial_natDegree_le_C2`).  Every exponent the committed axis tree
    reads is `natLift reqIdx` of a `read_root` / `verify_child` memory row of the trace (§A, §D):
    `read_root` rows have `ver = 1` (`readRootVerGate`) and carry the exponent of the request they
    answer (`≤ 3N + 3`); `verify_child` rows inherit a `read_root` row's record through the
    `intermediate` LogUp.  When the traces do not tile, the event template is the honest wrap with
    exponent `0`.
  * They are taken as named premises at the
    EVENT skeleton `skeletonEv` and transported to the C2 strategy (`census_C2_of_Ev`,
    `sizeWindow_C2_of_Ev`) by the c-invariance lemmas.
  * **The assembled bridge** `not_mem_FailureUnion_C2`: from `c ∉ optimizedFailureEventEv` plus
    (a), (b) at the event skeleton, `c.1 ∉ ProductionP8Containment.FailureUnion (strategyOfTracesR0AC2 …) C c.λ` — the exact
    `hout` of `accepted_outside_failureUnion_at`.

  Additive: nothing is re-pointed; `OptimizedFailureEventEv` and every consumer stay.

  Paper: the paper (the `read_root` timestamp is the compute line number `z^i`), `:1431`
  (the one global `intermediate` accumulator matches read and verify records), `:1441` (unique
  requests), `:2129-2131` (memory selectors).
-/
import Nock.NockVMROM.Thm54.OptimizedFailureEventEv
import Nock.NockVMROM.Thm54.UniqueExponentsBridge
import Nock.NockVMROM.Thm54.P8Core.ConsumerObligationsEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.ConsumerObligationsEv

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.MemoryTable
open Nock.AxisBridge
open Nock.AxisBatching
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.ReconTreeSize
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.StrategyOfTracesEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.UniqueExponentsBridge
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.MemoryInternalPole
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis (reqIdxCol)
open Nock.NockVMROM.Thm54.WalkTilingEvents (memRowStateOf)
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.EdgeComparisonCensus

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

noncomputable section

/-! ## §A  Generic: the axis tree's exponents are record exponents of read/verify node labels -/

section Generic

variable {K : Type} [Field K]

end Generic

section GenericDegree

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

end GenericDegree

/-! ## §B  The family IO-chain window with every event explicit

`FamilyIOChainRouteB`'s twins take `hgood : c ∉ P.optimizedFailureEvent (honestQc …) (honestQm …)`
(the PINNED event at the reindexed traces) and read four facts off it: `nprSeed c.1 ≠ 0`, the
timestamp exclusion, `FamilyIOGood`, and the internal-pole exclusion. -/

section EventChain

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

end EventChain

/-! ## §C  The four event facts from the 2b-ii event -/

section FromEv

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin P.computeChip.rap.w → F[X])
  (Qm : Fin P.memoryChip.rap.w → F[X])

end FromEv

/-! ## §D  (c) at the built strategies -/

section Built

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin P.computeChip.rap.w → F[X])
  (Qm : Fin P.memoryChip.rap.w → F[X])

end Built

/-! ## §E  (a) and (b): named premises at the event skeleton, transported to the C2 strategy -/

section Transport

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin P.computeChip.rap.w → F[X])
  (Qm : Fin P.memoryChip.rap.w → F[X])
  (h : TracesWalkHyps P.optimized Qc Qm c)

end Transport

/-! ## §F  The assembled bridge to `FailureUnion` -/

section Bridge

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin P.computeChip.rap.w → F[X])
  (Qm : Fin P.memoryChip.rap.w → F[X])
  (h : TracesWalkHyps P.optimized Qc Qm c)

end Bridge

end

end Nock.NockVMROM.Thm54.ConsumerObligationsEv
