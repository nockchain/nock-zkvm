/-
  Nock/RedTeam/Batch822Thm54R4BridgeMemory.lean

  Additive.

  At `memoryChipAt c` (the family chip; the trace is the package-width `Qm₀` reindexed by
  `familyQm`, the `Batch501` convention), with the decoded rows `pub i := (lblM P Qm₀ c i).2.2`:

  * the decoded state is `memRowStateOf` of the committed base row (`pub_st`);
  * every row is `eqBlk` (`Batch490.deployed_lblM_eqBlk`, β-free: acceptance, `MemStateTagChar`,
    `nprSeed c.1 ≠ 0`; no `Vmem`, `interV`, `pole`);
  * the row's `λ` is the tuple's `c.λ` (`FamilyMemoryRows.decode_lambda_eq_sampled`, A6);
  * the followed child slot `ℓ` of row `i` is row `childIdx i ℓ` and its `lc` / `rc` cell is that
    row's `pt` (`Batch501.deployed_forestVecBFT_pt` + `Walk.ForestVecBFT_layout` +
    `Batch501.encPT_label`), with `BFSValidF` and the tiling placing children strictly later and
    inside the table (`WalkQueueDeployed.deployed_bfsValid_memory`, `deployed_tiling_memory`);
  * the masked roots `1..kMem` carry `pt.counts = 0` (`Batch409.deployed_root_accumulators_zero`).

  The `α`-forest, `γ`-prefix
  and tiling exclusions come from `c ∉ optimizedFailureEvent` (`Batch501.hαM_of_good`,
  `hγM_of_good`, `htileαM_of_good`).
-/
import Nock.NockVMROM.Thm54.FormRBridgeTelescope
import Nock.RedTeam.Batch501Thm54MemoryTopology
import Nock.RedTeam.Batch409Thm54SeedBoundaryKside
import Nock.NockVMROM.Thm54.P8Core.Batch822Thm54R4BridgeMemory
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch822

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.MemoryTable
open Nock.AxisBatching
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.FormRBridge
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.Framework
open Nock.Framework.Reify
open Nock.RedTeam.Batch490
open Nock.RedTeam.Batch501

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])

/-! ## A. Row identities at every trace -/

/-! ## B. The accepted-trace facts -/

section Accepted

variable (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hchar : MemStateTagChar F)
  (hz : nprSeed c.1 ≠ 0)
  (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀)

include hsatM hchar

end Accepted

end

end Nock.RedTeam.Batch822

#print axioms Nock.RedTeam.Batch822.telescopeRows_of_memory
#print axioms Nock.RedTeam.Batch822.root_counts_zero
#print axioms Nock.RedTeam.Batch822.link_of_deployed
