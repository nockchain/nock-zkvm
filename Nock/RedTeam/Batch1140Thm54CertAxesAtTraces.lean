import Nock.RedTeam.Batch1111Thm54C2CombinedAtTraces
import Nock.RedTeam.Batch972Thm54Round0WrapCertAxis
import Nock.RedTeam.Batch808Thm54FormRRepairComplete
import Nock.RedTeam.Batch783Thm54U1Complete
import Nock.NockVMROM.Thm54.P8Core.Batch1140Thm54CertAxesAtTraces

/-!
Certificate axes at the traces of an optimized strict package. Shows that every active request is answered by a `read_root` row at its exponent, recovers the certificate axis of an OP0 / OP9 family row (`leaf136_eq_certAxis`, `leaf145_eq_certAxis`), and derives `CertAxesOK0` from the traces (`certAxesOK0_of_traces`). `nonvacuous_honest_row768` checks the hypotheses on the honest row at `p = 769`.
-/
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace Nock.RedTeam.Batch1140

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.MemoryTable
open Nock.ComputeTable (MemRec)
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis (reqIdxCol)
open Nock.RedTeam.Batch575 (Padding)
open Nock.ComputeTable (State DTcomp)
open Nock.NockVMROM.Thm54.DeployedComputeRows (pkgHchar)

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

/-! ## §0  The axis value of a padded certificate (generic, one row) -/

section Generic

open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.RedTeam.Batch575
open scoped Classical

variable {F : Type} [Field F]

end Generic

/-! ## §A  Every active request is answered by a `read_root` row at its exponent -/

section Request

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
  (hα0 : alphaM c.1 ≠ 0)
include hacc hgood hax hbasis hwidth hα0

end Request

/-! ## §B  The certificate axis of an OP0 / OP9 family row -/

section Rows

variable (hsat : Framework.RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

end Rows

section RowsAcc

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
  (hα0 : alphaM c.1 ≠ 0)
include hacc hgood hax hbasis hwidth hα0

end RowsAcc

/-! ## §C  At the S-carrying tree -/

section Tree

open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch1024 (treeS axF svF)

end Tree

/-! ## §D  `CertAxesOK0`: the certificate axes at the traces -/

section CertAxes

open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch1024 (treeS axF svF)

variable (hsat : Framework.RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

end CertAxes

section CertAxesAcc

open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch1024 (treeS axF svF)

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
  (hα0 : alphaM c.1 ≠ 0)
include hacc hgood hax hbasis hwidth hα0

end CertAxesAcc

/-! ## §E  Non-vacuity on an honest row -/

section NonVacuity

open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.RedTeam.Batch781 (F769 rowEnv_leaf rowEnv_op0 rowEnv_op9 formRN_769)

/-- **Non-vacuity of `leaf136_eq_certAxis` on the honest `p − 1` row at `p = 769`** (the hardest
honest row, `top = 1`, shift `n − 1 = 9`; `Batch808.row768`): every hypothesis holds (all 97 gates,
`FormRWidth`, the padding, `op₀ = 1`, `op₉ = 0`), and the recovered axis is the honest leaf `768`. -/
theorem nonvacuous_honest_row768 :
    Batch808.row768.trace 136 = (768 : F769) ∧
      Batch808.row768.trace 136 =
        ((certAxis (DecodedLambdaEvent.rowShift Batch808.row768)
          (DecodedLambdaEvent.rowBits Batch808.row768) : ℕ) : F769) := by
  have hm : DecodedLambdaEvent.rowShift Batch808.row768 ≤ 63 := DecodedLambdaEvent.rowShift_le _
  have hpad : Padding (formRN F769) (DecodedLambdaEvent.rowShift Batch808.row768)
      (DecodedLambdaEvent.rowBits Batch808.row768) := by
    intro j hj hjn
    have hk : ∀ k, k < 6 → Batch808.row768.trace (265 + k) = bit01 ((9 : ℕ).testBit k) := by
      intro k hk
      rw [show 265 + k = col0 + 63 + k by simp [col0], Batch808.row768,
        Batch781.rowEnv_m _ _ _ _ _ _ k hk, Batch781.nMinus1Low_769]
    have hshift : DecodedLambdaEvent.rowShift Batch808.row768 = 9 := by
      unfold DecodedLambdaEvent.rowShift
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, hk 0 (by decide), hk 1 (by decide),
        hk 2 (by decide), hk 3 (by decide), hk 4 (by decide), hk 5 (by decide)]
      decide
    rw [formRN_769] at hjn
    omega
  refine ⟨by rw [Batch808.row768, rowEnv_leaf]; norm_num, ?_⟩
  exact leaf136_eq_certAxis Batch808.row768 Batch783.width_769 Batch808.honest_768_at_769 hpad
    (by rw [Batch808.row768, rowEnv_op0]) (by rw [Batch808.row768, rowEnv_op9])

end NonVacuity

end

end Nock.RedTeam.Batch1140

#print axioms Nock.RedTeam.Batch1140.read_row_of_request
#print axioms Nock.RedTeam.Batch1140.leaf136_eq_certAxis
#print axioms Nock.RedTeam.Batch1140.leaf145_eq_certAxis
#print axioms Nock.RedTeam.Batch1140.request_axis
#print axioms Nock.RedTeam.Batch1140.certAxesOK0_of_traces
#print axioms Nock.RedTeam.Batch1140.nonvacuous_honest_row768
