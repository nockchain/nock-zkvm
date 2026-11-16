/-
  Nock/RedTeam/Batch490Thm54TopologyAssembly.lean

  Whole-table topology assembly.**

  At the
  deployed chip:

  * `hFcommit` is per-row `V_comp` + decoding.  `Fcomp`'s child link reads
    only the child's `(s, f, e)`, which `clabC` supplies by construction;
    the `V_comp` conjunct is `FamilyComputeRows.deployed_row_vcomp_at`
    through `WrapFixesVcomp.lblCAt_vcomp_of_vcompAt`; fanout and state by
    decoding.  Memory twin (M′): the β-free `FmemTopo` via `eqBlk_of_paper_classes` and `clabM`.
  * Whole-table `VecBFT` is `Batch471::deployed_prefixBFT` plus
    `deployed_bfsValid` (so `prefixLen = rows P`) and `deployed_tiling`,
    transported to the `(s, f, e)` projection by `vecBFT_map`.  Do not
    align `clabC`'s state with the hosted child tag.

  `hFcommit` and whole-table `VecBFT` LAND at the deployed chip (no
  residual).  `hseed` and the prefix `α`-event discharge from the priced
  walk-root event after tiling.  `computeTopology_of_deployed` is the exact failing statement.
  `openConjunctsAfterVer` stays **7** (dropping names would be a ledger
  lie).  K-side topology RAPs kept.
-/
import Nock.WalkPrefix
import Nock.NockVMROM.Thm54.RawTopologySoundness
import Nock.NockVMROM.Thm54.WrapFixesVcomp
import Nock.NockVMROM.Thm54.WalkQueueDeployed
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.FamilyMemoryRows
import Nock.NockVMROM.Thm54.WrapMemoryConjuncts
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.MemoryTopoBetaFree
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch455Thm54ComputeTopology
import Nock.RedTeam.Batch465Thm54DeployedRootLabelEqClaim
import Nock.RedTeam.Batch471Thm54ComputeTopologyPrefix
import Nock.RedTeam.Batch489Thm54FoOfEqFoW
import Nock.NockVMROM.Thm54.P8Core.Batch490Thm54TopologyAssembly
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch490

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.WrapFixesVcomp
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.Framework
open Nock.Framework.Reify
open MonolithicRAP
open Nock.RedTeam.Batch448
open Nock.RedTeam.Batch455
open Nock.RedTeam.Batch465
open Nock.RedTeam.Batch471
open Nock.RedTeam.Batch489
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

/-! ## Ledger: target 5; live list stays 7 (`prefixBadGammas` unpriced) -/

/-- Target names if both topology conjuncts discharged from the chips +
priced events.  Not the live list. -/
def targetAfterTopology : List String :=
  ["mem_first_counts", "mem_first_indicator",
    "axisStructural", "rootBoundary", "structuralChecks"]

theorem targetAfterTopology_length :
    targetAfterTopology.length = 5 := by
  decide

/-- Live open list: topology names stay until
`computeTopology_of_deployed` loses its `hγ`. -/
def openConjunctsAfterAssembly : List String :=
  openConjunctsAfterVer

theorem openConjunctsAfterAssembly_length :
    openConjunctsAfterAssembly.length = 7 :=
  openConjunctsAfterVer_length

theorem topology_still_open :
    "computeTopology" ∈ openConjunctsAfterAssembly ∧
      "memoryTopology" ∈ openConjunctsAfterAssembly := by
  decide

/-- K-side topology RAP consumers, still live. -/
def ksideConsumersKept : List String :=
  ksideComputeTopologyConsumers

theorem ksideConsumersKept_eq :
    ksideConsumersKept = ksideComputeTopologyConsumers :=
  rfl

/-- The unpriced event blocking `computeTopology_of_deployed`. -/
def remainingEvent : String := "WalkPrefix.prefixBadGammas"

theorem remainingEvent_name :
    remainingEvent = "WalkPrefix.prefixBadGammas" :=
  rfl

def pipelineAfter490 : List (String × String) :=
  [("1 WalkSat at lblC/foC", "landed: Batch459/471 deployed_walkSat_lblC"),
    ("2 TracesWalkHyps", "landed: Batch489 tracesWalkHyps_of_failureEvent"),
    ("3 VecBFT_reconstruct_of_label",
      "landed: hFcommit from Vcomp+clabC; VecBFT from prefix+queue"),
    ("4 reconForest_ForestReconGoal_of_label",
      "STOP: memory seedW prover-committed; forestPrefixBadGammas unpriced"),
    ("5 AcceptedContent.computeTopology",
      "STOP: prefixBadGammas (priced γ is root/claim only)"),
    ("6 AcceptedContent.memoryTopology", "open (needs 4)")]

theorem pipelineAfter490_length : pipelineAfter490.length = 6 := by
  decide

/-! ## A. `hFcommit` at the deployed compute chip (no residual) -/

section ComputeFcommit

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hz : nprSeed c.1 ≠ 0)

include hsat hz

end ComputeFcommit

/-! ## B. Whole-table `VecBFT` from prefix + queue (no residual) -/

section ComputeVecBFT

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)

include hsat
include hax hbasis hwidth

end ComputeVecBFT

/-! ## C. `ReconGoal` / `ComputeExactTopology` of `execOfTraces` -/

section ComputeTopology

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hz : nprSeed c.1 ≠ 0)
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)

include hsatC hz
include hax hbasis hwidth

/-- Whole-table `ReconGoal` at `lblC`. -/
theorem deployed_reconGoal
    (hseed : seedOfClaim P.optimized.verifier.raw.claim c =
      rlc (gamma c.1) (Vd P c Qc₀ 1) * alphaC c.1)
    (hα : alphaC c.1 ∉ walkPrefixAlphaEvent
      (fun i => rlc (gamma c.1) (Vd P c Qc₀ i))
      (fun i l => rlc (gamma c.1) (Cvd P c Qc₀ hsatC i l))
      (foC P Qc₀ c) (rows P))
    (hγ : gamma c.1 ∉ prefixBadGammas (Vd P c Qc₀) (Cvd P c Qc₀ hsatC)
      (foC P Qc₀ c) (rows P))
    (htileα : c.1 ∉ WalkTilingEvents.computeTilingEvent
      (Batch459.foW P c (familyQc P c Qc₀) hsatC) (rows P)) :
    ReconGoal (comp_stateSep (K := K)) (lblC P Qc₀ c) (rows P) := by
  have hfo := foW_eq_foC_all P c Qc₀ hsatC
  have hv : BFSValid (foC P Qc₀ c) (rows P) := by
    simpa [hfo] using deployed_bfsValid P c (familyQc P c Qc₀) hsatC hax hbasis hwidth
  have htile : Sf (foC P Qc₀ c) (rows P) + 1 = rows P := by
    simpa [hfo] using deployed_tiling P c (familyQc P c Qc₀) hsatC hax hbasis hwidth htileα
  have hb' := deployed_vecBFT_sfe P c Qc₀ hsatC hax hbasis hwidth hseed hα hγ htileα
  have harity : ∀ i, foC P Qc₀ c i ≤ 3 :=
    fun i => (comp_stateSep (K := K)).fanout_le _
  refine reconTree_ReconGoal_of_label (comp_stateSep (K := K)) sfeOf respects_sfe
    encSFE encSFE_label (lblC P Qc₀ c) (clabOf (lblC P Qc₀ c)) (foC P Qc₀ c)
    htile hv harity (fun i _ _ => rfl)
    (fun i hi1 hih => hFcommit_deployed P c Qc₀ hsatC hz i hi1 hih) hb'

end ComputeTopology

/-! ## D₀. Prefix `α`-event = priced `alphaBadOf` after the root pin -/

section AlphaEventEq
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

end AlphaEventEq

/-! ## D. Priced-event discharge; exact failing statement -/

section PricedDischarge

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hz : nprSeed c.1 ≠ 0)
  (hchar : MemStateTagChar F)
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)

include hsatC
include hax hbasis hwidth

include hz hchar hsatM

end PricedDischarge

/-! ## E. Memory `hFcommit` at the deployed chip (no residual) -/

section MemoryFcommit

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hchar : MemStateTagChar F)
  (hz : nprSeed c.1 ≠ 0)

include hsatM hchar hz

end MemoryFcommit

end Nock.RedTeam.Batch490

#print axioms Nock.RedTeam.Batch490.hFcommit_deployed
#print axioms Nock.RedTeam.Batch490.hFcommit_memory
#print axioms Nock.RedTeam.Batch490.deployed_lblM_eqBlk
#print axioms Nock.RedTeam.Batch490.deployed_vecBFT
#print axioms Nock.RedTeam.Batch490.execOfTraces_computeTopology
#print axioms Nock.RedTeam.Batch490.computeTopology_of_deployed
#print axioms Nock.RedTeam.Batch490.hseed_of_good
#print axioms Nock.RedTeam.Batch490.openConjunctsAfterAssembly_length
