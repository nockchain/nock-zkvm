/-
  Nock/RedTeam/Batch1172Thm54ServedRecordsAtTraces.lean

  The chain, per active record `j` of BFS row `a`:
  * position (`pos_of_pr`): the pair sits at row `a` of both BFS lists;
  * (ii) the exponent twin (`requestTargets_at`): `requestTargets skeletonEv` at `expOfAt a j` is
    row `a`'s record (`states_eq`, `activeMask_eq`, `prefix_eq`);
  * (i) the responders (`served_rows`): a `read_root` row `k` and a `verify_child` row `k'` at
    `expOfAt a j`, both with the request's full ten-slot record;
  * fingerprints in all three `𝕂` coordinates (`traceRec_fp`, `enc_NN`, `eqBlk`);
  * (iii) the pair-event separation (`sep_eq`, `reqPairEv` of the 2b-ii event): the structural
    root IS the read row's pre-`z` noun;
  * (iv) at the traces (`slot_at`, R4's path equation through `Batch1170.slot_of_paths`) and the
    served lookup (`svF_eq`);
  * per record (`axis_child`): structural axes `3` / `2`, OP0 / OP9 served axes `axF`.
  Sources: `hacc`, `hgood`, `hgoodEv`, `hax`, `hbasis`, `hwidth`, `h`, `hF`.
-/
import Nock.RedTeam.Batch1170Thm54ServedPathSlot
import Nock.RedTeam.Batch1142Thm54C2CombinedCertAxes0
import Nock.RedTeam.Batch1011Thm54AxisViewBindsAtCoin
import Nock.RedTeam.Batch971Thm54Round0WrapForestCover
import Nock.RedTeam.Batch772Thm54RequestIndex
import Nock.RedTeam.Batch773Thm54ExpOfRequestList
import Nock.NockVMROM.Thm54.PreSeedCensus
import Nock.NockVMROM.Thm54.BuildTFWindow
import Nock.NockVMROM.Thm54.P8Core.Batch1172Thm54ServedRecordsAtTraces
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace Nock.RedTeam.Batch1172

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.StrategyOfTracesEv
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.UniqueExponentsBridge
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis (reqIdxCol)
open Nock.NockVMROM.Thm54.WalkTilingEvents (memRowStateOf foOfMem)
open Nock.RedTeam.Batch1024 (treeS axF svF)
open Nock.RedTeam.Batch973 (expR)
open Nock.GlobalCarryRecognizer
open Nock.AxisBatching.MTree (readCount verifyCount)
open Nock.RedTeam.Batch575 (UniqueExponents)
open Nock.FieldEmbedding

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

set_option quotPrecheck false

local notation "NN" => preZNounOfEnvs K (ringChar K) P.optimized.family.problem.cfg.kMem
  (Batch824.envsFR P c Qm) P.optimized.family.problem.cfg.memRows_pos

/-! ## §0  The served lookup's row set -/

/-! ## §A  The memory side -/

section Memory

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hacc hgood hax hbasis hwidth

end Memory

/-! ## §C  Record bridges, the served lookup, the pair-event separation, link (iv) at the traces -/

section Bridges

end Bridges

/-! ## §B  The compute side: position, states, prefix, request targets -/

section Compute

/-- The C2 join on the family traces at `c`, rooted at the package claim. -/
local notation "JT" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) (svF P c Qm) (axF P c Qc)
  (treeS P c Qc).size (treeS P c Qc)
  P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula

local notation "SK" => skeletonEv P.optimized (honestQc P c Qc) (honestQm P c Qm)

local notation "NC" => P.optimized.family.problem.cfg.compRows

variable (hsat : Framework.RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

end Compute

/-! ## §D  Link (iv) at the traces, the served lookup, the pair-event separation -/

section AtTraces

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hwidth : FormRWidth F)
  (hbasis : FormRBasis P.optimized.basis)
include hacc hgood

end AtTraces

/-! ## §E  The served-record oracle at positional pairs -/

section Main

/-- The C2 join on the family traces at `c` (generic fuel / node / inputs). -/
local notation "JJ" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) (svF P c Qm) (axF P c Qc)

/-- The C2 join on the family traces at `c`, rooted at the package claim. -/
local notation "JT" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) (svF P c Qm) (axF P c Qc)
  (treeS P c Qc).size (treeS P c Qc)
  P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
  (hα0 : alphaM c.1 ≠ 0)

end Main

end

end Nock.RedTeam.Batch1172

#print axioms Nock.RedTeam.Batch1172.servedRecordsPos_of_traces
#print axioms Nock.RedTeam.Batch1172.slot_at
#print axioms Nock.RedTeam.Batch1172.sep_eq
#print axioms Nock.RedTeam.Batch1172.served_rows
#print axioms Nock.RedTeam.Batch1172.requestTargets_at
#print axioms Nock.RedTeam.Batch1172.enc_NN
