/-
  Nock/RedTeam/Batch465Thm54DeployedRootLabelEqClaim.lean

  **`deployed_root_label_eq_claim`: outside the walk's root events,
  the row-0 decoded `(s, f, e)` of every trace accepted at `computeChipAt c` are the claim's
  fingerprints at the sampled seed.**

  `ComputeWalkRootEvents.cur_one_eq_root_of_walkSat` then gives `cur(1) = RLC^γ(rvt_root)`
  outside the `α`-event, and `eq_of_rlc_eq_of_not_mem` gives label equality outside the
  `γ`-event; `Batch458::bindFP_of_labelVec_eq` reads the three `bindFP`s off coordinates `1..9`.
  (The `Batch458` lemma itself is not used: its `hγ` is stated on
  `rootClaimBadGammas`, which is `univ` when the labels agree — `gammaBadOf` is the corrected
  shape, `∅` on equal labels.)

  **Bridge.**  The events are defined on the `c`-free `computeSourceEnv Qc₀` (honest-width trace);
  the chip theorems are at `rowEnvAt P c (familyQc P c Qc₀)`.  §A shows the two environments
  have the same trace columns (`familyQc` is a `Fin.cast` reindex of the same polynomials at the
  same node), so the decoded labels, child payloads and fanouts agree
  (`ComputeWalkRootEvents.rowLabelVec_congr` etc.); §B transports the polynomial `rootDiffP`
  along that agreement (it reads rows `1..h` only).
-/
import Nock.NockVMROM.Thm54.ComputeWalkRootEvents
import Nock.RedTeam.Batch458Thm54StrategyBindsStop
import Nock.RedTeam.Batch459Thm54ComputeTopologyStop
import Nock.RedTeam.Batch463Thm54WalkAlphaInitialCount
import Nock.NockVMROM.Thm54.P8Core.Batch465Thm54DeployedRootLabelEqClaim
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch465

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Walk
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.RedTeam.Batch457
open Nock.RedTeam.Batch458
open Nock.RedTeam.Batch459
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.Framework
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.Framework.Reify
open MonolithicRAP
open OptimizedHostileTimestamps
open Module

noncomputable section

/-! ## B. Transport of `rootDiffP` along row-wise agreement on `1..h` -/

section Congr
variable {K : Type} [Field K] [DecidableEq K]

end Congr

/-! ## A. The family row at `familyQc` has the trace columns of the honest-width row -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])

/-! ### The trace-only row decoders agree with `Batch459`'s chip-side decoders -/

variable (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hsat
include hax hbasis hwidth

/-! ### The `ℕ`-indexed operands agree on `1..rows P` -/

/-! ## C. The theorem -/

/-! ## D. Status -/

omit hsat in
def bindsDropBlockersAfter : List String :=
  ["compute BindComputeRow rows: decoded_binds_compute needs ComputeJoinSound (H1.4 join)",
    "memory MemoryTreeBinds: RecordHalfJoin + decode_fingerprint (H1.4)",
    "∀ z quantifier: SemanticSupportAt exit exists, strategyOfTraces not restated at it"]

theorem bindsDropBlockersAfter_length : bindsDropBlockersAfter.length = 3 := by decide

theorem blockers_are_the_old_tail :
    bindsDropBlockersAfter = Batch458.bindsDropBlockers.tail := by decide

theorem chipClosedPublics_still_zero : Batch403.chipClosedPublics = 0 := rfl

def CHIP_SFE_REMAINING_BEFORE_H15B : List String := ["strategyOfTraces takes TracesBindsHyps"]

/-- The last item closed when
`strategyOfTraces` stopped taking `TracesBindsHyps` (the split retype: no binding field on
`ProductionStrategy`; the seed-local binding is `StrategyOfTracesCore.strategyOfTraces_bindsAtCoin`,
a theorem given the tree bindings). -/
def CHIP_SFE_REMAINING : List String := []

theorem chip_sfe_remaining_length : CHIP_SFE_REMAINING.length = 0 := by decide

theorem chip_sfe_remaining_eq_nil : CHIP_SFE_REMAINING = [] := rfl

theorem chip_sfe_remaining_before_length : CHIP_SFE_REMAINING_BEFORE_H15B.length = 1 := by decide

theorem chip_sfe_remaining_sublist :
    CHIP_SFE_REMAINING_BEFORE_H15B.Sublist Batch457.CHIP_SFE_REMAINING := by decide

end

end Nock.RedTeam.Batch465

#print axioms Nock.RedTeam.Batch465.rootDiffP_congr
#print axioms Nock.RedTeam.Batch465.familyRow_trace_eq
#print axioms Nock.RedTeam.Batch465.rootDiffP_family
#print axioms Nock.RedTeam.Batch465.deployed_root_cur_eq_claim
#print axioms Nock.RedTeam.Batch465.deployed_root_label_eq_claim
#print axioms Nock.RedTeam.Batch465.deployed_root_label_eq_claim_of_good
