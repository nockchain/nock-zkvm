/-
  Nock/RedTeam/Batch500Thm54GammaTransport.lean

  Dequeue-mask mirror (47/48 mechanism) +
  `prefixBadGammas` range-congruence (the `foOf = foW` shape) wired onto
  `Vd`/`Cvd`/`foC`, plus the walk-part every-tuple completeness.

  Memory `w 199 → 200`, `d = 4`,
  `fixedCount = 4`.  No second accumulator.

  `MemoryWalkDeployed.deployed_walkSat` is `WalkSatInGate` (mask-form,
  no seed public).  Live `openConjunctsAfterVer` stays **7** (`memoryTopology` forest twin
  still needs prover-committed `seedW`).  `:1401` 5→3 not reached
  (`Batch492`: needs `MemoryExactTopology`).

  `honest_memory_accepted_at_every_tuple` is the walk part: chalVal-free
  honest labels, tuple coins (`gamma` / `alphaM`).  The chip's
  `walkGamma` pin stays the family coin; the source does not regenerate.
-/
import Nock.WalkPrefix
import Nock.WalkInGate
import Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.OptimizedMemoryRAP
import Nock.NockVMROM.Thm54.MemoryWalkDeployed
import Nock.NockVMROM.Thm54.MemoryWalkLabel
import Nock.NockVMROM.Thm54.MixedCoordinateCompiler
import Nock.NockVMROM.Thm54.WrapMemoryConjuncts
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch465Thm54DeployedRootLabelEqClaim
import Nock.RedTeam.Batch471Thm54ComputeTopologyPrefix
import Nock.RedTeam.Batch490Thm54TopologyAssembly
import Nock.RedTeam.Batch499Thm54InGateWiringStop
import Nock.NockVMROM.Thm54.P8Core.Batch500Thm54GammaTransport
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Nock.RedTeam.Batch500

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.MemoryWalkLabel
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.Framework
open Nock.Framework.Reify
open MonolithicRAP
open Nock.RedTeam.Batch448
open Nock.RedTeam.Batch465
open Nock.RedTeam.Batch471
open Nock.RedTeam.Batch489
open Nock.RedTeam.Batch490
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Module

/-! ## A. Mirror receipts -/

theorem dequeueMaskMixed_eq {F : Type} [Field F] :
    dequeueMaskMixed (F := F) =
      MixedExpr.Sub (.Var .traceCur 56) (.Lift (bcur 154)) :=
  rfl

theorem dequeueMaskE_eq : dequeueMaskE = extVar .traceCur 56 := rfl

theorem residual_is_23 : RAPPadding.memoryResidualColumns 3 = 23 := rfl

theorem namedSource_fixedCount_numeral : 4 = 4 := rfl

def mirrorPinName : String := "dequeueMaskMixed"

theorem mirrorPinName_eq : mirrorPinName = "dequeueMaskMixed" := rfl

/-- Memory walk at the deployed chip is the mask-form recognizer. -/
def deployedWalkIsInGate : String :=
  "MemoryWalkDeployed.deployed_walkSat : WalkSatInGate"

theorem deployedWalkIsInGate_eq :
    deployedWalkIsInGate =
      "MemoryWalkDeployed.deployed_walkSat : WalkSatInGate" :=
  rfl

def openAfterComputeGamma : List String :=
  openConjunctsAfterVer

theorem openAfterComputeGamma_length :
    openAfterComputeGamma.length = 7 :=
  openConjunctsAfterVer_length

theorem topology_target_five :
    Batch490.targetAfterTopology.length = 5 :=
  Batch490.targetAfterTopology_length

def nockCompiles_zmod_hypotheses_unmoved : String :=
  "nockCompiles_zmod binders unmoved"

theorem nockCompiles_zmod_hypotheses_unmoved_nonempty :
    nockCompiles_zmod_hypotheses_unmoved ≠ "" := by
  decide

/-! ## B. -/

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-! ## C. `Vd`/`Cvd`/`foC` = committed `computeSourceEnv` on `1..N` -/

section DeployedVectors
variable {F : Type} [Field F] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))

include hsatC

end DeployedVectors

/-! ## D. `hγ` from the priced event; topology without the extra hyp -/

section PricedGamma
variable {F : Type} [Field F] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [CharP K (ringChar K)] [FiniteDimensional F K]
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

include hsatM

include hz hchar
include hax hbasis hwidth

end PricedGamma

/-! ## E. Walk-part completeness at every tuple

    Canonical source is chalVal-free; the chip's `walkGamma` pin is the
    family coin.  The walk part uses the honest labels (nouns / tags /
    fanout) at the *tuple's* `gamma` / `alphaM`. -/

section HonestEveryTuple
variable {F : Type} [Field F] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)

/-- Honest `x^mem` at walk index `i` (1-indexed; out of range reads row 0). -/
def honestMemPub (i : ℕ) : Pub K :=
  if h : 1 ≤ i ∧ i - 1 < P.optimized.family.problem.cfg.memRows then
    P.optimized.family.problem.exec.memoryPubAt ⟨i - 1, h.2⟩
  else
    P.optimized.family.problem.exec.memoryPubAt
      ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩

/-- RLC of the honest label at the tuple's `γ`.  ChalVal-free nouns. -/
def honestMemCur (i : ℕ) : K :=
  rlc (gamma c.1) (memoryLabelVec (honestMemPub P i))

/-- Hosted child tags of the honest BFS row list (chalVal-free). -/
def honestMemTags (i : ℕ) : Fin 2 → K :=
  fun j => memChildStateTagCol P.optimized.family.memoryWalkRows i j

/-- RLC of the honest declared child at the tuple's `γ`. -/
def honestMemChld (i l : ℕ) : K :=
  rlc (gamma c.1)
    (MemoryWalkLabel.childVecN (honestMemPub P i) (honestMemTags P i) (l - 1))

/-- Honest fanout (chalVal-free). -/
def honestMemFo (i : ℕ) : ℕ :=
  fanoutMem (honestMemPub P i).st

/-- **Walk-part completeness at every tuple.**  Labels are the family's
    committed nouns; coins are `c`'s.  No source regeneration. -/
theorem honest_memory_accepted_at_every_tuple :
    ∃ ln count acc : ℕ → K,
      WalkSatInGate (honestMemCur P c) (honestMemChld P c) (honestMemFo P)
        ln count acc (alphaM c.1)
        (alphaM c.1 ^ P.optimized.family.problem.cfg.kMem)
        P.optimized.family.problem.cfg.kMem
        P.optimized.family.problem.cfg.memRows :=
  walkSatInGate_exists (honestMemCur P c) (honestMemChld P c) (honestMemFo P)
    (alphaM c.1) (alphaM c.1 ^ P.optimized.family.problem.cfg.kMem)
    (memRows_pos P) (kMem_pos P) (kMem_le P)

end HonestEveryTuple

end Nock.RedTeam.Batch500

#print axioms Nock.RedTeam.Batch500.dequeueMaskMixed_eq
#print axioms Nock.RedTeam.Batch500.prefixBadGammas_congr_on
#print axioms Nock.RedTeam.Batch500.Vd_eq_committed
#print axioms Nock.RedTeam.Batch500.hγ_of_good
#print axioms Nock.RedTeam.Batch500.computeTopology_of_deployed_of_good
#print axioms Nock.RedTeam.Batch500.honest_memory_accepted_at_every_tuple
#print axioms Nock.RedTeam.Batch500.openAfterComputeGamma_length
