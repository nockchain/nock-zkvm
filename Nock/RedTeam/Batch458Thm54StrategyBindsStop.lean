/-
  Nock/RedTeam/Batch458Thm54StrategyBindsStop.lean

  Brief step 2 asked to drop `TracesBindsHyps` from `strategyOfTraces`'s compute half and
  close `public_subject/formula/result` from the chip (`Batch403.chipClosedPublics 0 → 3`).
  Not done, and the reason is compiled rather than asserted:

  * The compute half of `BindsAt` is `ComputeTreeBinds`, whose root clause is
    `root_bindings` — `bindFP z claim.{subject,formula,result} (row-0 s/f/e)`.  On the chip
    side the only row-0 fact the gates give is the walk identity of `Batch457`
    (`walkAccInit_row0_decoded`), one equation in `𝕂`.  Turning it into `bindFP` needs
    exactly two inputs — `cur(1) = RLC^γ(claimLabelVec)` and `γ` outside the root/claim
    collision — and `chipRootBinding_of_two_inputs` shows the rest is a theorem.  Both
    inputs are `Batch457`'s compiled STOPs (`initial_count` unwired, `h/|𝕂|` root event
    and the `Fin 10` collision unpriced).
  * `TracesBindsHyps` quantifies `∀ z`; the M2b exit `SemanticSupportAt` (binds at the
    sampled seed only) exists but `strategyOfTraces : ProductionStrategy` still carries
    `BareSemanticSupport.binds` — a type-level fact, unchanged here.
-/
import Nock.NockVMROM.Thm54.WrapPublicConjuncts
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.HostileSkeletonDecoding
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.RedTeam.Batch398Thm54PublicConjuncts
import Nock.RedTeam.Batch403Thm54PublicFromSeedBlocked
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch457Thm54RootLabelFromChip
import Nock.NockVMROM.Thm54.P8Core.Batch458Thm54StrategyBindsStop
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch458

open scoped Polynomial
open Polynomial
open Nock
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.RedTeam.Batch457
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.Framework
open MonolithicRAP
open OptimizedComputeHostileAccumulator
open Module

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## A. What `strategyOfTraces` carries -/

/- `strategyOfTraces_binds_is_hyp` — "`strategyOfTraces`'s `binds`
field IS the constructor argument `hbinds : TracesBindsHyps`" — is unstatable after the split
(`ProductionStrategy` has no `binds` field; `TracesBindsHyps` is retired).  That hypothesis was refuted at `3 ≤ |K|` (`Batch573.tracesBindsAll_unsat`). -/

theorem tracesBindsHyps_root_at_seed
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hbinds : (strategyOfTraces P Qc Qm c h).BindsAtCoin c.1 c.2.2.2.lambda)
    (hz : nprSeed c.1 ≠ 0) :
    bindFP (nprSeed c.1) (publicClaimOf P Qc Qm).subject
        (specializedProblem (timestampOfTraces P Qc Qm c h) (nprSeed c.1) hz
          (alphaM c.1) c.2.2.2.lambda).exec.computeTree.label.2.2.1.s ∧
      bindFP (nprSeed c.1) (publicClaimOf P Qc Qm).formula
        (specializedProblem (timestampOfTraces P Qc Qm c h) (nprSeed c.1) hz
          (alphaM c.1) c.2.2.2.lambda).exec.computeTree.label.2.2.1.f ∧
      bindFP (nprSeed c.1) (publicClaimOf P Qc Qm).result
        (specializedProblem (timestampOfTraces P Qc Qm c h) (nprSeed c.1) hz
          (alphaM c.1) c.2.2.2.lambda).exec.computeTree.label.2.2.1.e :=
  BindsAt.root_bindings (hbinds hz)

/-! ## B. The chip-level target and its exact residual -/

variable (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])

omit [Fintype F] [DecidableEq F] [CharP K (ringChar K)] [FiniteDimensional F K] in
/-- Outside the root/claim collision set, equal `RLC^γ` means equal ten-vectors. -/
theorem labelVec_eq_of_rlc_eq_outside {u v : Fin 10 → K} {γ : K}
    (h : Walk.rlc γ u = Walk.rlc γ v) (hγ : γ ∉ rootClaimBadGammas u v) : u = v := by
  by_contra hne
  apply hγ
  simp only [rootClaimBadGammas, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h

/-- **The residual, exactly.**  Nothing else
is missing. -/
theorem chipRootBinding_of_two_inputs
    (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (hcur : ∀ st0, OneHotSelector (rowEnvAt P c Qc (firstRow P)).toSourceEnv st0 →
      Walk.rlc (gamma c.1) (labelVecOfPub (decodePub (rowEnvAt P c Qc (firstRow P)) st0)) =
        Walk.rlc (gamma c.1)
          (claimLabelVec (nprSeed c.1) P.optimized.verifier.raw.claim))
    (hγ : ∀ st0, OneHotSelector (rowEnvAt P c Qc (firstRow P)).toSourceEnv st0 →
      gamma c.1 ∉ rootClaimBadGammas
        (labelVecOfPub (decodePub (rowEnvAt P c Qc (firstRow P)) st0))
        (claimLabelVec (nprSeed c.1) P.optimized.verifier.raw.claim)) :
    ChipRootBinding P c Qc := by
  obtain ⟨st0, hone, _⟩ := root_cur_is_decoded_label P c Qc hsat hax hbasis hwidth
  refine ⟨st0, hone, ?_⟩
  have hvec := labelVec_eq_of_rlc_eq_outside (hcur st0 hone) (hγ st0 hone)
  exact bindFP_of_labelVec_eq _ _ _ hvec

theorem row0_equation_shape
    (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    ∃ st0 : State,
      OneHotSelector (rowEnvAt P c Qc (firstRow P)).toSourceEnv st0 ∧
      alphaC c.1 * (Walk.rlc (gamma c.1)
            (labelVecOfPub (decodePub (rowEnvAt P c Qc (firstRow P)) st0)) -
          Walk.rlc (gamma c.1)
            (claimLabelVec (nprSeed c.1) P.optimized.verifier.raw.claim)) =
        alphaC c.1 *
            (childSumCC firstReader).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv -
          (initialOverlayCoord 1).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv := by
  obtain ⟨st0, hone, h⟩ := walkAccInit_row0_decoded P c Qc hsat hax hbasis hwidth
  refine ⟨st0, hone, ?_⟩
  simp only [seedOfClaim] at h
  linear_combination h

/-! ## C. Status -/

/-- Why `TracesBindsHyps` is not dropped, by clause. -/
def bindsDropBlockers : List String :=
  ["compute root_bindings: Batch457 STOP 1-3 (initial_count, alphaC root event, Fin 10 collision)",
    "compute BindComputeRow rows: decoded_binds_compute needs ComputeJoinSound (H1.4 join)",
    "memory MemoryTreeBinds: RecordHalfJoin + decode_fingerprint (H1.4)",
    "∀ z quantifier: SemanticSupportAt exit exists, strategyOfTraces not restated at it"]

theorem bindsDropBlockers_length : bindsDropBlockers.length = 4 := by decide

/-- `0` chip-closed, `3` hypothesis-closed, `11` total. -/
theorem publicClassification_unchanged :
    Batch403.chipClosedPublics = 0 ∧ Batch403.hypothesisClosedPublics = 3 ∧
      Batch403.totalClosed = 11 := by
  decide

theorem public_names_still_not_open :
    ∀ name ∈ Batch398.newlyClosed, name ∉ Batch398.openConjuncts := by
  decide

theorem openConjuncts_unmoved : Batch398.openConjuncts.length = 10 :=
  Batch398.openConjuncts_length

end

end Nock.RedTeam.Batch458

#print axioms Nock.RedTeam.Batch458.tracesBindsHyps_root_at_seed
#print axioms Nock.RedTeam.Batch458.chipRootBinding_of_two_inputs
#print axioms Nock.RedTeam.Batch458.row0_equation_shape
#print axioms Nock.RedTeam.Batch458.bindFP_of_labelVec_eq
