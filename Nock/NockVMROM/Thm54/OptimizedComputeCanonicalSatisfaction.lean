import Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
import Nock.NockVMROM.Thm54.ComputePaperPacking
import Nock.RedTeam.Batch478Thm54QueueGateRatioForm

/-!
# Canonical corrected compute satisfaction from one sampled assignment

This module assembles the exact non-IO and sampled-IO transition sources, endpoint sources,
canonical trace evaluation, and the corrected `199/98` fixed-preprocessing RAP.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeCanonicalSatisfaction

open Nock
open Nock.Reified
open Nock.Framework Reify
open Module
open OptimizedComputeGateBasis
open OptimizedComputeCorrectedFinal
open OptimizedComputeFinal hiding residualWitnessRole ResidualWitnessId FinalExtensionColumn
open OptimizedComputeFinalTypedLowering
open OptimizedComputeFinalTrace
open OptimizedComputeSemanticRealization
open OptimizedComputeSameExecution
open OptimizedComputeSubstitution
open OptimizedComputeSampledTrace
open OptimizedComputeOverlay
open OptimizedComputeTemplate
open OptimizedComputeCodec (decodeState)
open StrictExtension
open CoordinateBasis
open CoordinateCompiler
open OptimizedComputeBaseGates
open MonolithicRAP
open ComputePaperPacking

set_option maxRecDepth 20000

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K] [DecidableEq F]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-- Base-field challenge coordinates encode the exact table, walk, and sampled-IO challenges.
Slots not used by the exact source object retain the canonical zero value. -/
def ExactFinalChallengeCoordinates [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (A : SampledIOSameExecutionAssignment R p)
    (chalVal : ℕ → F) : Prop :=
  ∀ q : Fin 12, ∀ k : Fin 3,
    chalVal (3 * (q : ℕ) + (k : ℕ)) = coord b (exactFinalChallenge A q) k

/-- Exact verifier-parameterized compute coordinates: the cubic block carries challenges
`0..11`. -/
def ExactFinalChallengeCoordinatesWith [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (A : SampledIOSameExecutionAssignment R p)
    (c : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K)
    (chalVal : ℕ → F) : Prop :=
  ∀ q : Fin 12, ∀ k : Fin 3,
    chalVal (3 * (q : ℕ) + (k : ℕ)) = coord b (exactFinalChallengeWith A c q) k

/-- Fixed public coordinates consumed by the compute endpoints: extension publics `α, seed`
and the initial/terminal one-hot selector banks. -/
def ExactFinalPublicCoordinates [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (R : PlusIOSegmentedFamily F K)
    (hn : 0 < R.problem.cfg.compRows) (pubVal : ℕ → F) : Prop :=
  (∀ q : Fin 2, ∀ k : Fin 3,
    pubVal (3 * (q : ℕ) + (k : ℕ)) =
      coord b (if q = 0 then R.computeWalkAlpha else R.computeWalkSeed) k) ∧
  (∀ j : Fin 11,
    pubVal (20 + (j : ℕ)) =
      if j = OptimizedComputeCodec.stateIndex
          (R.problem.exec.computePubAt ⟨0, hn⟩).state then 1 else 0) ∧
  (∀ j : Fin 11,
    pubVal (31 + (j : ℕ)) =
      if j = OptimizedComputeCodec.stateIndex
          (R.problem.exec.computePubAt
            ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩).state then 1 else 0)

/-- The same exact row and successor discharge the 76 core packed non-IO gates and
the four sampled-IO gates. -/
theorem exact_finalExtTransitionGates
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (hsmall : OptimizedComputeFormRDenoms.FormRAxisSmall A) (hwidth : FormRWidth F) :
    ∀ g ∈ paperPackingCoreGates ++ finalSampledIOTransitionGates,
      g.eval (exactFinalTransitionEnv A i hi).toSourceEnv = 0 := by
  intro g hg
  rcases List.mem_append.mp hg with hcore | hio
  · have hsrc := exact_finalNonIOSourceFamilies17 A h i hi
    exact (paperPacking_iff_sources _
        (R.problem.exec.computePubAt i).state
        (fun s => exactFinalTransitionEnv_selectors A i hi s)
        (hsrc _ ComputePaperPacking.zZinv_mem_finalNonIO)).2 hsrc g hcore
  · exact exact_finalSampledIOTransitionGates A h i hi hsmall hwidth g hio

/-- The exact honest transition object is already in the decoded packed source language; no
collision premise is needed in the completeness direction. -/
theorem exact_correctedDecodedTransitionSources
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (hsmall : OptimizedComputeFormRDenoms.FormRAxisSmall A) (hwidth : FormRWidth F) :
    CorrectedDecodedTransitionSources (exactFinalTransitionEnv A i hi) where
  nonIO := by
    have hsrc := exact_finalNonIOSourceFamilies17 A h i hi
    exact (paperPacking_iff_sources _
        (R.problem.exec.computePubAt i).state
        (fun s => exactFinalTransitionEnv_selectors A i hi s)
        (hsrc _ ComputePaperPacking.zZinv_mem_finalNonIO)).2 hsrc
  sampledIOSafe4 := exact_finalSampledIOTransitionGates A h i hi hsmall hwidth

/-- Every non-residual extension role of the canonical polynomial trace reconstructs the exact
co-resident encoded row value at the same node. -/
theorem preliminaryCell_coord_formRLeaf
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (b : Basis (Fin 3) F K)
    (i : Fin R.problem.cfg.compRows)
    (role : Fin 58) (k : Fin 3) :
    preliminaryCell A hn b i ⟨13 + 3 * (role : ℕ) + (k : ℕ), by
      have hrole := role.isLt
      have hk := k.isLt
      omega⟩ =
      coord b (formRLeafCore b (encodedRowAt A i) role) k := by
  rw [coord_formRLeafCore]
  have hdiv : (13 + 3 * (role : ℕ) + (k : ℕ) - 13) / 3 = (role : ℕ) := by omega
  have hmod : (13 + 3 * (role : ℕ) + (k : ℕ) - 13) % 3 = (k : ℕ) := by omega
  have hrole58 : (role : ℕ) < 58 := role.isLt
  have hnotResidual : ¬ 58 ≤ (role : ℕ) := by omega
  have hnotBase : ¬ 13 + 3 * (role : ℕ) + (k : ℕ) < 13 := by omega
  simp [preliminaryCell, hdiv, hmod, hrole58, hnotResidual, hnotBase, formRLeafCore]

theorem formR_trace
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (i : Fin R.problem.cfg.compRows) (off : ℕ) (hoff : off < 100) :
    (envOfTrace (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal).trace (202 + off) =
      if hH : 94 ≤ off ∧ off < 97 then
        coord b (formRLamHK (axisLeafCoord A b i) (formRLamOfChal b chalVal))
          ⟨off - 94, by omega⟩
      else if hT : 97 ≤ off then
        coord b (formRLamTK (axisLeafCoord A b i) (formRLamOfChal b chalVal))
          ⟨off - 97, by omega⟩
      else formROff (axisLeafCoord A b i) off := by
  have hj : 202 + off < 303 := by omega
  have hge : 202 ≤ 202 + off := by omega
  simp only [envOfTrace, dif_pos hj]
  rw [correctedCanonicalFinalTrace_eval A hn nodes hnodes]
  by_cases hH : 94 ≤ off ∧ off < 97
  · have h1 : 296 ≤ 202 + off ∧ 202 + off < 299 := by omega
    rw [dif_pos h1, dif_pos hH]
    congr 1
    exact Fin.ext (by simp; omega)
  by_cases hT : 97 ≤ off
  · have h1 : ¬ (296 ≤ 202 + off ∧ 202 + off < 299) := by omega
    have h2 : 299 ≤ 202 + off := by omega
    rw [dif_neg h1, dif_pos h2, dif_neg (show ¬ (202 + off = 302) by omega), dif_neg hH,
      dif_pos hT]
    congr 1
    exact Fin.ext (by simp; omega)
  have hnH : ¬ (296 ≤ 202 + off ∧ 202 + off < 299) := by omega
  have hnT : ¬ (299 ≤ 202 + off) := by omega
  have hnotRes : ¬ (13 ≤ 202 + off ∧
      (202 + off - 13) / 3 < 60 ∧ 58 ≤ (202 + off - 13) / 3) := by omega
  rw [dif_neg hnH, dif_neg hnT, dif_neg hnotRes, dif_neg hH, dif_neg hT]
  rw [preliminaryCell_formR A hn b i ⟨202 + off, by omega⟩ hge]
  have hoff' : 202 + off - 202 = off := by omega
  simp [hoff']

/-- The gathered `𝕂` helpers `H` / `T` of the canonical row are the leftover certificate powers
of the `𝕂` coin `λ` reassembled from the raw slots `27..29`. -/
theorem canonical_gather_certExt_val
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (i : Fin R.problem.cfg.compRows) :
    (gatherCorrectedFinalTypedEnv b
        (envOfTrace (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal)).certExt 0 =
        formRLamHK (axisLeafCoord A b i) (formRLamOfChal b chalVal) ∧
      (gatherCorrectedFinalTypedEnv b
        (envOfTrace (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal)).certExt 1 =
        formRLamTK (axisLeafCoord A b i) (formRLamOfChal b chalVal) := by
  constructor
  · simp only [gatherCorrectedFinalTypedEnv]
    conv_rhs => rw [← b.sum_repr (formRLamHK (axisLeafCoord A b i) (formRLamOfChal b chalVal))]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := formR_trace A hn nodes hnodes b chalVal pubVal orbit i (94 + (k : ℕ)) (by omega)
    rw [dif_pos (by omega : 94 ≤ 94 + (k : ℕ) ∧ 94 + (k : ℕ) < 97)] at h
    rw [show 296 + 3 * ((0 : Fin 2) : ℕ) + (k : ℕ) = 202 + (94 + (k : ℕ)) by simp; omega, h]
    congr 1
    simp only [coord]
    congr 1
    apply Fin.ext; simp
  · simp only [gatherCorrectedFinalTypedEnv]
    conv_rhs => rw [← b.sum_repr (formRLamTK (axisLeafCoord A b i) (formRLamOfChal b chalVal))]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := formR_trace A hn nodes hnodes b chalVal pubVal orbit i (97 + (k : ℕ)) (by omega)
    rw [dif_neg (by omega : ¬ (94 ≤ 97 + (k : ℕ) ∧ 97 + (k : ℕ) < 97)),
      dif_pos (by omega : 97 ≤ 97 + (k : ℕ))] at h
    rw [show 296 + 3 * ((1 : Fin 2) : ℕ) + (k : ℕ) = 202 + (97 + (k : ℕ)) by simp; omega, h]
    congr 1
    simp only [coord]
    congr 1
    apply Fin.ext; simp

/-- The gathered certificate base columns of the canonical row are the leftover certificate. -/
theorem canonical_gather_certBase_val
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (i : Fin R.problem.cfg.compRows) (q : Fin 94) :
    (gatherCorrectedFinalTypedEnv b
        (envOfTrace (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal)).certBase q =
      formROff (axisLeafCoord A b i) q := by
  simp only [gatherCorrectedFinalTypedEnv]
  have h := formR_trace A hn nodes hnodes b chalVal pubVal orbit i q (by omega)
  rw [dif_neg (by omega), dif_neg (by omega)] at h
  exact h

/-- The `𝕂` coin `λ` reassembled from the honest raw slots is the honest compute challenge `9`. -/
theorem formRLamOfChal_eq
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (b : Basis (Fin 3) F K) (chalVal : ℕ → F)
    (hchal9 : ∀ k : Fin 3,
      chalVal (3 * 9 + (k : ℕ)) = coord b (exactFinalChallenge A 9) k) :
    formRLamOfChal b chalVal = exactFinalChallenge A 9 := by
  unfold formRLamOfChal
  conv_rhs => rw [← b.sum_repr (exactFinalChallenge A 9)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show 27 + (k : ℕ) = 3 * 9 + (k : ℕ) by omega, hchal9 k]
  rfl

/-- Under `FormRAxisBound`, the gathered certificate base columns are the honest typed row's. -/
theorem canonical_gather_certBase
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hax : FormRAxisBound A b)
    (i : Fin R.problem.cfg.compRows) (q : Fin 94) :
    (gatherCorrectedFinalTypedEnv b
        (envOfTrace (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal)).certBase q =
      OptimizedComputeFormRDenoms.exactFinalCertBase A i q := by
  rw [canonical_gather_certBase_val A hn nodes hnodes b chalVal pubVal orbit i q]
  simp only [formROff, OptimizedComputeFormRDenoms.exactFinalCertBase,
    axisNat_axisLeafCoord_eq A b hax i]

/-- Under `FormRAxisBound` and the honest coin coordinates, the gathered `𝕂` helpers are the
honest typed row's. -/
theorem canonical_gather_certExt
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hax : FormRAxisBound A b)
    (hchal9 : ∀ k : Fin 3,
      chalVal (3 * 9 + (k : ℕ)) = coord b (exactFinalChallenge A 9) k)
    (i : Fin R.problem.cfg.compRows) (q : Fin 2) :
    (gatherCorrectedFinalTypedEnv b
        (envOfTrace (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal)).certExt q =
      OptimizedComputeFormRDenoms.exactFinalCertExt A i (exactFinalChallenge A 9) q := by
  have hv := canonical_gather_certExt_val A hn nodes hnodes b chalVal pubVal orbit i
  have hlam := formRLamOfChal_eq A b chalVal hchal9
  fin_cases q
  · rw [show ((fun i => i) ⟨0, by decide⟩ : Fin 2) = 0 from rfl, hv.1, hlam]
    simp [OptimizedComputeFormRDenoms.exactFinalCertExt, formRLamHK,
      axisNat_axisLeafCoord_eq A b hax i]
  · rw [show ((fun i => i) ⟨1, by decide⟩ : Fin 2) = 1 from rfl, hv.2, hlam]
    simp [OptimizedComputeFormRDenoms.exactFinalCertExt, formRLamTK,
      axisNat_axisLeafCoord_eq A b hax i]

theorem canonical_gather_ext_core
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (i : Fin R.problem.cfg.compRows) (role : Fin 58) :
    (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)).extTrace ⟨role, by omega⟩ =
      formRLeafCore b (OptimizedComputeSampledTrace.encodedRowAt A i) role := by
  rw [eq_iff_coords_eq b]
  intro k
  change coord b
    (∑ q : Fin 3,
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal).trace
          (correctedFinalExtCoordIndex ⟨role, by omega⟩ q) • b q) k =
    coord b (formRLeafCore b
      (OptimizedComputeSampledTrace.encodedRowAt A i) role) k
  rw [coord_sum_smul]
  simp only [envOfTrace]
  rw [dif_pos (show correctedFinalExtCoordIndex ⟨role, by omega⟩ k < 303 by
    simp [correctedFinalExtCoordIndex]
    omega)]
  rw [correctedCanonicalFinalTrace_eval_preFormR A hn nodes hnodes (hlt := by simp [correctedFinalExtCoordIndex]; omega)]
  simp only [correctedFinalExtCoordIndex]
  exact (dif_neg (by omega)).trans (preliminaryCell_coord_formRLeaf A hn b i role k)

/-- On an adjacent orbit node, the canonical polynomial trace's next-row core is the exact
successor encoded row. -/
theorem canonical_gather_ext_core_next
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (role : Fin 58) :
    (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)).extTraceNext ⟨role, by omega⟩ =
      formRLeafCore b
        (OptimizedComputeSampledTrace.encodedRowAt A ⟨(i : ℕ) + 1, hi⟩) role := by
  rw [eq_iff_coords_eq b]
  intro k
  change coord b
    (∑ q : Fin 3,
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal).traceNext
          (correctedFinalExtCoordIndex ⟨role, by omega⟩ q) • b q) k =
    coord b (formRLeafCore b
      (OptimizedComputeSampledTrace.encodedRowAt A ⟨(i : ℕ) + 1, hi⟩) role) k
  rw [coord_sum_smul]
  simp only [envOfTrace]
  rw [dif_pos (show correctedFinalExtCoordIndex ⟨role, by omega⟩ k < 303 by
    simp [correctedFinalExtCoordIndex]
    omega)]
  have hsucc' : nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i := by
    simpa [mul_comm] using hsucc
  rw [← hsucc']
  rw [correctedCanonicalFinalTrace_eval_preFormR A hn nodes hnodes (hlt := by simp [correctedFinalExtCoordIndex]; omega)]
  simp only [correctedFinalExtCoordIndex]
  exact (dif_neg (by omega)).trans
    (preliminaryCell_coord_formRLeaf A hn b ⟨(i : ℕ) + 1, hi⟩ role k)

theorem canonical_gather_base_current
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (i : Fin R.problem.cfg.compRows) (j : Fin 13) :
    (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)).baseTrace j =
      finalBaseCell A hn i j :=
  correctedCanonicalFinalTrace_base_eval
    A hn nodes hnodes b chalVal pubVal orbit i j

/-- **The 31st:** the gathered canonical row's exponent carrier is the honest `S(i)`. -/
theorem canonical_gather_expCol
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (i : Fin R.problem.cfg.compRows) :
    (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)).expCol =
      ((OptimizedComputeFinalTrace.honestS R i : ℕ) : F) := by
  simp only [gatherCorrectedFinalTypedEnv, envOfTrace, dif_pos (show (302 : ℕ) < 303 by omega)]
  exact correctedCanonicalFinalTrace_eval_S A hn nodes hnodes b chalVal pubVal orbit i

theorem canonical_gather_base_next
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (j : Fin 13) :
    (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)).baseTraceNext j =
      finalBaseCell A hn ⟨(i : ℕ) + 1, hi⟩ j := by
  change (envOfTrace
    (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
    orbit.ω (nodes i) chalVal pubVal).traceNext j = _
  simp only [envOfTrace, dif_pos (show (j : ℕ) < 303 by omega)]
  have hsucc' : nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i := by
    simpa [mul_comm] using hsucc
  rw [← hsucc']
  rw [correctedCanonicalFinalTrace_eval_preFormR A hn nodes hnodes (hlt := by simp [correctedFinalExtCoordIndex]; omega)]
  simp [preliminaryCell]

theorem canonical_gather_challenge
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hchal : ExactFinalChallengeCoordinates b A chalVal)
    (i : Fin R.problem.cfg.compRows) (q : Fin 12) :
    (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)).chal q =
      exactFinalChallenge A q := by
  rw [eq_iff_coords_eq b]
  intro k
  change coord b
    (∑ r : Fin 3, chalVal (3 * (q : ℕ) + (r : ℕ)) • b r) k =
      coord b (exactFinalChallenge A q) k
  rw [coord_sum_smul, hchal q k]

theorem canonical_gather_challenge_of_coordinates
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (q : Fin 12) (target : K)
    (hchal : ∀ k : Fin 3,
      chalVal (3 * (q : ℕ) + (k : ℕ)) = coord b target k)
    (i : Fin R.problem.cfg.compRows) :
    (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)).chal q = target := by
  rw [eq_iff_coords_eq b]
  intro k
  change coord b
    (∑ r : Fin 3, chalVal (3 * (q : ℕ) + (r : ℕ)) • b r) k =
      coord b target k
  rw [coord_sum_smul, hchal k]

theorem canonical_gather_extensionPublic
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hpub : ExactFinalPublicCoordinates b R hn pubVal)
    (i : Fin R.problem.cfg.compRows) (q : Fin 3) (hq : (q : ℕ) < 2) :
    (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)).extensionPublic q =
      if (q : ℕ) = 0 then R.computeWalkAlpha else R.computeWalkSeed := by
  rw [eq_iff_coords_eq b]
  intro k
  change coord b
    (∑ r : Fin 3, pubVal (3 * (q : ℕ) + (r : ℕ)) • b r) k = _
  rw [coord_sum_smul]
  have := hpub.1 ⟨q, hq⟩ k
  simp only [Fin.val_mk] at this
  rw [this]
  by_cases h0 : (q : ℕ) = 0
  · simp [h0, show (⟨(q : ℕ), hq⟩ : Fin 2) = 0 from Fin.ext h0]
  · have : (⟨(q : ℕ), hq⟩ : Fin 2) ≠ 0 := fun e => h0 (congrArg Fin.val e)
    simp [h0, this]

/-- **The post-challenge public `requests`** (compute extension public role `2`, base publics
`6..8`) is the sampled IO terminal: the RAP output `requests = acc_prog(h₁)` of
the paper, which the IO consistency check `requests = responses` (`:597`) shares with the
memory chip. -/
def ExactFinalRequestsCoordinate [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (A : SampledIOSameExecutionAssignment R p) (pubVal : ℕ → F) : Prop :=
  ∀ k : Fin 3, pubVal (6 + (k : ℕ)) = coord b A.witness10.terminal k

theorem canonical_gather_requests
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hreq : ExactFinalRequestsCoordinate b A pubVal)
    (i : Fin R.problem.cfg.compRows) :
    (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)).extensionPublic 2 =
      A.witness10.terminal := by
  rw [eq_iff_coords_eq b]
  intro k
  change coord b
    (∑ r : Fin 3, pubVal (3 * 2 + (r : ℕ)) • b r) k = _
  rw [coord_sum_smul]
  exact hreq k

/-- Role `60` of the gathered canonical row is `acc_after(i)`. -/
theorem canonical_gather_accAfter
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (i : Fin R.problem.cfg.compRows) :
    (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)).extTrace 60 =
      ComputeSampledIO.coResidentAccC A.compress10 R.problem.cfg.challenges.lam R.problem.exec.computeRows
        ((i : ℕ) + 1) := by
  rw [eq_iff_coords_eq b]
  intro k
  change coord b
    (∑ q : Fin 3,
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal).trace
          (correctedFinalExtCoordIndex (60 : Fin 63) q) • b q) k = _
  rw [coord_sum_smul]
  simp only [envOfTrace]
  rw [dif_pos (show correctedFinalExtCoordIndex (60 : Fin 63) k < 303 by
    simp [correctedFinalExtCoordIndex]; omega)]
  exact correctedCanonicalFinalTrace_accAfter_eval A hn nodes hnodes b chalVal pubVal orbit i k

/-- **The honest compute line starts at `1`**: the execution's
first-row `ln_prev` — `W_comp`'s first witness column, "the total number of
memory accesses requested until that row" (`:1884`), whose closed form the paper's uniqueness
argument reads as `z^i` with `i` the line number (`:1413`, `:1441`) — is `1`.  This is the value
the endpoint gate `OptimizedComputeCorrectedFinal.finalLnInit` pins, so it is the completeness
obligation of the honest prover; the paper's `V_comp` (`:1728-1742`) does not check it, and the
honest generator supplies it as `α ^ 0` (`Gen.lean` `renderOp*Row`, `ComputeLineStartsAtZero`).
Definitionally `GenericHonestCommitment.FirstLineStartsAtOne R.problem.exec` (the row-`0`
positivity proof is irrelevant), restated here because that module sits above this one. -/
def ExactFinalLineOrigin (R : PlusIOSegmentedFamily F K) (hn : 0 < R.problem.cfg.compRows) :
    Prop :=
  (R.problem.exec.computePubAt ⟨0, hn⟩).ln_prev = 1

/-- Extension role `54` of the encoded row is the execution's `ln_prev`. -/
theorem coreExtensionValue_lnPrev
    (A : SampledIOSameExecutionAssignment R p) (i : Fin R.problem.cfg.compRows) :
    coreExtensionValue (encodedRowAt A i) 54 = (R.problem.exec.computePubAt i).ln_prev := by
  have h := exactFinalCurrentEnv_lnPrev A i
  simpa [lnPrev, ext0, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, exactFinalCurrentEnv,
    exactFinalExtensionRow] using h

/-- Extension role `32` of the encoded row is the co-resident accumulator before the row. -/
theorem coreExtensionValue_sampledAcc
    (A : SampledIOSameExecutionAssignment R p) (i : Fin R.problem.cfg.compRows) :
    coreExtensionValue (encodedRowAt A i) 32 =
      ComputeSampledIO.coResidentAccC A.compress10 R.problem.cfg.challenges.lam R.problem.exec.computeRows i := by
  have h := exactFinalCurrentEnv_sampledAcc A i
  simpa [sampledIOSubst, overlayCoord, pubFP, ext0, Expr.eval,
    CorrectedFinalTypedEnv.toSourceEnv, exactFinalCurrentEnv, exactFinalExtensionRow] using h

theorem canonical_gather_initialSelectorPublic
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hpub : ExactFinalPublicCoordinates b R hn pubVal)
    (i : Fin R.problem.cfg.compRows) (j : Fin 11) :
    (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)).scalarPublic ⟨j, by omega⟩ =
      if j = OptimizedComputeCodec.stateIndex
          (R.problem.exec.computePubAt ⟨0, hn⟩).state then 1 else 0 :=
  hpub.2.1 j

theorem canonical_gather_terminalSelectorPublic
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hpub : ExactFinalPublicCoordinates b R hn pubVal)
    (i : Fin R.problem.cfg.compRows) (j : Fin 11) :
    (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)).scalarPublic ⟨11 + (j : ℕ), by omega⟩ =
      if j = OptimizedComputeCodec.stateIndex
          (R.problem.exec.computePubAt
            ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩).state then 1 else 0 := by
  change pubVal (20 + (11 + (j : ℕ))) = _
  simpa only [show 20 + (11 + (j : ℕ)) = 31 + (j : ℕ) by omega] using hpub.2.2 j

theorem canonical_gather_walkLine
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (i : Fin R.problem.cfg.compRows) :
    (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)).extTrace 61 =
      A.exact.computeWalk.ln ((i : ℕ) + 1) := by
  rw [eq_iff_coords_eq b]
  intro k
  change coord b
    (∑ q : Fin 3,
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal).trace
          (correctedFinalExtCoordIndex 61 q) • b q) k =
    coord b (A.exact.computeWalk.ln ((i : ℕ) + 1)) k
  rw [coord_sum_smul]
  simp only [envOfTrace, dif_pos (show correctedFinalExtCoordIndex 61 k < 303 by
    simp [correctedFinalExtCoordIndex]
    omega)]
  rw [correctedCanonicalFinalTrace_eval_preFormR A hn nodes hnodes (hlt := by simp [correctedFinalExtCoordIndex]; omega)]
  fin_cases k <;> norm_num [correctedFinalExtCoordIndex, preliminaryCell]

theorem canonical_gather_walkLine_next
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)).extTraceNext 61 =
      A.exact.computeWalk.ln ((i : ℕ) + 2) := by
  rw [eq_iff_coords_eq b]
  intro k
  change coord b
    (∑ q : Fin 3,
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal).traceNext
          (correctedFinalExtCoordIndex 61 q) • b q) k =
    coord b (A.exact.computeWalk.ln ((i : ℕ) + 2)) k
  rw [coord_sum_smul]
  simp only [envOfTrace, dif_pos (show correctedFinalExtCoordIndex 61 k < 303 by
    simp [correctedFinalExtCoordIndex]
    omega)]
  have hsucc' : nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i := by
    simpa [mul_comm] using hsucc
  rw [← hsucc']
  rw [correctedCanonicalFinalTrace_eval_preFormR A hn nodes hnodes (hlt := by simp [correctedFinalExtCoordIndex]; omega)]
  fin_cases k <;> norm_num [correctedFinalExtCoordIndex, preliminaryCell]

/-- Canonical current row exposes the exact walk-queue inverse at role `62`. -/
theorem canonical_gather_walkInv
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (i : Fin R.problem.cfg.compRows) :
    (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)).extTrace 62 =
      let c := A.exact.computeWalk.count ((i : ℕ) + 1)
      let l := A.exact.computeWalk.ln ((i : ℕ) + 1)
      if c = l then 0 else (c - l)⁻¹ := by
  rw [eq_iff_coords_eq b]
  intro k
  change coord b
    (∑ q : Fin 3,
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal).trace
          (correctedFinalExtCoordIndex 62 q) • b q) k =
    coord b
      (let c := A.exact.computeWalk.count ((i : ℕ) + 1)
       let l := A.exact.computeWalk.ln ((i : ℕ) + 1)
       if c = l then 0 else (c - l)⁻¹) k
  rw [coord_sum_smul]
  simp only [envOfTrace, dif_pos (show correctedFinalExtCoordIndex 62 k < 303 by
    simp [correctedFinalExtCoordIndex]
    omega)]
  rw [correctedCanonicalFinalTrace_eval_preFormR A hn nodes hnodes (hlt := by simp [correctedFinalExtCoordIndex]; omega)]
  fin_cases k <;> norm_num [correctedFinalExtCoordIndex, preliminaryCell]

theorem canonical_gather_walkInv_next
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)).extTraceNext 62 =
      let c := A.exact.computeWalk.count ((i : ℕ) + 2)
      let l := A.exact.computeWalk.ln ((i : ℕ) + 2)
      if c = l then 0 else (c - l)⁻¹ := by
  rw [eq_iff_coords_eq b]
  intro k
  change coord b
    (∑ q : Fin 3,
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal).traceNext
          (correctedFinalExtCoordIndex 62 q) • b q) k =
    coord b
      (let c := A.exact.computeWalk.count ((i : ℕ) + 2)
       let l := A.exact.computeWalk.ln ((i : ℕ) + 2)
       if c = l then 0 else (c - l)⁻¹) k
  rw [coord_sum_smul]
  simp only [envOfTrace, dif_pos (show correctedFinalExtCoordIndex 62 k < 303 by
    simp [correctedFinalExtCoordIndex]
    omega)]
  have hsucc' : nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i := by
    simpa [mul_comm] using hsucc
  rw [← hsucc']
  rw [correctedCanonicalFinalTrace_eval_preFormR A hn nodes hnodes (hlt := by simp [correctedFinalExtCoordIndex]; omega)]
  fin_cases k <;> norm_num [correctedFinalExtCoordIndex, preliminaryCell]

/-- WalkSat + BFS tiling: last-row `count = ln` with no order hypothesis
(`1 + Sf = h` so the powers agree). Compute forest is a singleton root. -/
theorem exact_compute_last_count_eq_ln
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations) :
    A.exact.computeWalk.count R.problem.cfg.compRows =
      A.exact.computeWalk.ln R.problem.cfg.compRows := by
  have hsat : Walk.WalkSat
      (Walk.curCol R.computeNodeVal R.computeWalkRows)
      (Walk.chldCol R.computeNodeVal R.computeWalkRows)
      (Walk.foCol R.computeWalkRows)
      A.exact.computeWalk.ln A.exact.computeWalk.count A.exact.computeWalk.acc
      R.computeWalkAlpha R.computeWalkSeed R.computeWalkAlpha
      R.problem.cfg.compRows := hA.2.1.1
  have hn : 0 < R.problem.cfg.compRows := R.problem.cfg.compRows_pos
  have hln := Walk.ln_closed hsat R.problem.cfg.compRows (by omega) le_rfl
  have hcnt := Walk.count_closed hsat R.problem.cfg.compRows (by omega) le_rfl
  have hlen : R.computeWalkRows.length = R.problem.cfg.compRows := by
    have := R.problem.exec.computeRows_length
    simpa [ExactExecution.computeRows, PlusIOSegmentedFamily.computeWalkRows,
      List.length_map] using this
  have htile := Walk.foCol_Sf_tilingF [R.problem.exec.computeTree] (List.cons_ne_nil _ _)
  have hSf : 1 + Walk.Sf (Walk.foCol R.computeWalkRows) R.problem.cfg.compRows =
      R.problem.cfg.compRows := by
    change 1 + Walk.Sf (Walk.foCol (Walk.bfsForest [R.problem.exec.computeTree]))
        (Walk.bfsForest [R.problem.exec.computeTree]).length =
      (Walk.bfsForest [R.problem.exec.computeTree]).length at htile
    rw [← show R.computeWalkRows = Walk.bfsForest [R.problem.exec.computeTree] from rfl] at htile
    rwa [hlen] at htile
  rw [hcnt, hln]
  rw [← pow_succ', Nat.add_comm, hSf]

/-- Packed IDs `0..75` and sampled IDs `78..81` inhabit the 76-core ++ 4-sampled list. -/
theorem mem_core_sampled_of_not_queue (gate : CorrectedCoreExtGateId)
    (h : (gate : ℕ) ≠ 76 ∧ (gate : ℕ) ≠ 77) :
    finalExtTransitionGates.get ⟨gate, by simp⟩ ∈
      paperPackingCoreGates ++ finalSampledIOTransitionGates := by
  have hcore : paperPackingCoreGates.length = 76 := paperPackingCoreGates_length
  have hnonIO : OptimizedComputeGateBasis.paperPackingNonIOGates.length = 78 :=
    OptimizedComputeGateBasis.paperPackingNonIOGates_length
  change (OptimizedComputeGateBasis.paperPackingNonIOGates ++
      finalSampledIOTransitionGates)[(gate : ℕ)] ∈
    paperPackingCoreGates ++ finalSampledIOTransitionGates
  by_cases hlt : (gate : ℕ) < 76
  · have hj : (gate : ℕ) < paperPackingCoreGates.length := by
      rw [hcore]; exact hlt
    have hmid : (gate : ℕ) < OptimizedComputeGateBasis.paperPackingNonIOGates.length := by
      rw [hnonIO]; omega
    have hget :
        (OptimizedComputeGateBasis.paperPackingNonIOGates ++
          finalSampledIOTransitionGates)[(gate : ℕ)] =
          paperPackingCoreGates[(gate : ℕ)]'hj := by
      rw [List.getElem_append_left hmid]
      change (paperPackingCoreGates ++
          OptimizedComputeGateBasis.queueWitnessGates)[(gate : ℕ)] = _
      exact List.getElem_append_left hj
    rw [hget]
    exact List.mem_append_left _ (List.getElem_mem hj)
  · have hge : 78 ≤ (gate : ℕ) := by omega
    have hle : OptimizedComputeGateBasis.paperPackingNonIOGates.length ≤ (gate : ℕ) := by
      rw [hnonIO]; exact hge
    have hidx : (gate : ℕ) - OptimizedComputeGateBasis.paperPackingNonIOGates.length <
        finalSampledIOTransitionGates.length := by
      rw [hnonIO]
      simp [finalSampledIOTransitionGates]
      omega
    have hget :
        (OptimizedComputeGateBasis.paperPackingNonIOGates ++
          finalSampledIOTransitionGates)[(gate : ℕ)] =
          finalSampledIOTransitionGates[(gate : ℕ) -
            OptimizedComputeGateBasis.paperPackingNonIOGates.length]'hidx :=
      List.getElem_append_right hle
    rw [hget]
    exact List.mem_append_right _ (List.getElem_mem hidx)

set_option maxRecDepth 300000 in
theorem packedQueueNonEmpty_source :
    finalExtTransitionGates.get ⟨76, by simp⟩ =
      OptimizedComputeGateBasis.walkQueueNonEmpty := by
  decide

set_option maxRecDepth 300000 in
theorem packedQueueTiling_source :
    finalExtTransitionGates.get ⟨77, by simp⟩ =
      OptimizedComputeGateBasis.walkQueueTiling := by
  decide

/-- Nonterminal tiling is `isLast`-masked (`isLast = 0`). -/
theorem exact_queueTiling_transition
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    OptimizedComputeGateBasis.walkQueueTiling.eval
      (exactFinalTransitionEnv A i hi).toSourceEnv = 0 := by
  have hlast : (exactFinalTransitionEnv A i hi).baseTrace 12 = 0 := by
    have hne : i ≠ ⟨R.problem.cfg.compRows - 1,
        Nat.sub_lt R.problem.cfg.compRows_pos (by omega)⟩ := by
      intro heq
      have hv : (i : ℕ) = R.problem.cfg.compRows - 1 := by
        simpa using congrArg Fin.val heq
      omega
    simp [exactFinalTransitionEnv, finalBaseCell, hne]
  simp [OptimizedComputeGateBasis.walkQueueTiling, Expr.eval,
    CorrectedFinalTypedEnv.toSourceEnv, hlast]

/-- Last-row nonempty is `notLast`-masked (`isLast = 1`). -/
theorem exact_queueNonEmpty_last
    (env : CorrectedFinalTypedEnv F K)
    (hlast : env.baseTrace 12 = 1) :
    OptimizedComputeGateBasis.walkQueueNonEmpty.eval env.toSourceEnv = 0 := by
  simp [OptimizedComputeGateBasis.walkQueueNonEmpty, Expr.eval,
    CorrectedFinalTypedEnv.toSourceEnv, hlast]

/-- WalkSat + BFS-valid + `h ≤ orderOf α`: nonterminal `count ≠ ln`. -/
theorem exact_compute_nonterminal_count_ne_ln
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hord : 2 ≤ R.problem.cfg.compRows →
      R.problem.cfg.compRows ≤ orderOf R.computeWalkAlpha)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    A.exact.computeWalk.count ((i : ℕ) + 1) ≠
      A.exact.computeWalk.ln ((i : ℕ) + 1) := by
  have hsat : Walk.WalkSat
      (Walk.curCol R.computeNodeVal R.computeWalkRows)
      (Walk.chldCol R.computeNodeVal R.computeWalkRows)
      (Walk.foCol R.computeWalkRows)
      A.exact.computeWalk.ln A.exact.computeWalk.count A.exact.computeWalk.acc
      R.computeWalkAlpha R.computeWalkSeed R.computeWalkAlpha
      R.problem.cfg.compRows := hA.2.1.1
  have hlen : R.computeWalkRows.length = R.problem.cfg.compRows := by
    have := R.problem.exec.computeRows_length
    simpa [ExactExecution.computeRows, PlusIOSegmentedFamily.computeWalkRows,
      List.length_map] using this
  have hv : Walk.BFSValidF 1 (Walk.foCol R.computeWalkRows) R.problem.cfg.compRows := by
    have this := Walk.foCol_BFSValidF [R.problem.exec.computeTree] (List.cons_ne_nil _ _)
    change Walk.BFSValidF 1
        (Walk.foCol (Walk.bfsForest [R.problem.exec.computeTree]))
        (Walk.bfsForest [R.problem.exec.computeTree]).length at this
    rw [← show R.computeWalkRows = Walk.bfsForest [R.problem.exec.computeTree] from rfl] at this
    rwa [hlen] at this
  have ht : 1 + Walk.Sf (Walk.foCol R.computeWalkRows) R.problem.cfg.compRows =
      R.problem.cfg.compRows := by
    have this := Walk.foCol_Sf_tilingF [R.problem.exec.computeTree] (List.cons_ne_nil _ _)
    change 1 + Walk.Sf (Walk.foCol (Walk.bfsForest [R.problem.exec.computeTree]))
        (Walk.bfsForest [R.problem.exec.computeTree]).length =
      (Walk.bfsForest [R.problem.exec.computeTree]).length at this
    rw [← show R.computeWalkRows = Walk.bfsForest [R.problem.exec.computeTree] from rfl] at this
    rwa [hlen] at this
  have hord' : R.problem.cfg.compRows ≤ orderOf R.computeWalkAlpha :=
    hord (by omega)
  have hneq := (Nock.RedTeam.Batch478.honest_ratio_gate (K := K) hv ht hord').1
    ((i : ℕ) + 1) (Nat.succ_le_succ (Nat.zero_le _)) hi
  have hln := Walk.ln_closed hsat ((i : ℕ) + 1) (by omega) (Nat.le_of_lt hi)
  have hcnt := Walk.count_closed hsat ((i : ℕ) + 1) (by omega) (Nat.le_of_lt hi)
  rw [hcnt, hln]
  convert hneq using 1
  rw [← pow_succ', Nat.add_comm]

theorem walkQueueNonEmpty_eval (env : Env K) :
    OptimizedComputeGateBasis.walkQueueNonEmpty.eval env =
      (((1 : ℤ) : K) - env.trace 12) *
        ((walkInv .traceCur).eval env *
          ((overlayCoord .traceCur 0).eval env -
            (finalWalkLine .traceCur).eval env) - ((1 : ℤ) : K)) := by
  unfold OptimizedComputeGateBasis.walkQueueNonEmpty
  simp only [Expr.eval]

theorem exact_queueNonEmpty_transition
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hord : 2 ≤ R.problem.cfg.compRows →
      R.problem.cfg.compRows ≤ orderOf R.computeWalkAlpha)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    OptimizedComputeGateBasis.walkQueueNonEmpty.eval
      (exactFinalTransitionEnv A i hi).toSourceEnv = 0 := by
  have hne := exact_compute_nonterminal_count_ne_ln A hA hord i hi
  have hlast : (exactFinalTransitionEnv A i hi).baseTrace 12 = 0 := by
    have hne' : i ≠ ⟨R.problem.cfg.compRows - 1,
        Nat.sub_lt R.problem.cfg.compRows_pos (by omega)⟩ := by
      intro heq
      have hv : (i : ℕ) = R.problem.cfg.compRows - 1 := by
        simpa using congrArg Fin.val heq
      omega
    simp [exactFinalTransitionEnv, finalBaseCell, hne']
  have h12 : (exactFinalTransitionEnv A i hi).toSourceEnv.trace 12 = 0 := by
    simp [CorrectedFinalTypedEnv.toSourceEnv, hlast]
  have hinv :
      (walkInv .traceCur).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
        (A.exact.computeWalk.count ((i : ℕ) + 1) -
          A.exact.computeWalk.ln ((i : ℕ) + 1))⁻¹ := by
    simp [walkInv, walkInvIndex, walkInvRole, ext0, exactFinalTransitionEnv,
      CorrectedFinalTypedEnv.toSourceEnv, exactFinalExtensionRow, Expr.eval, hne]
  have hcount :
      (overlayCoord .traceCur 0).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
        A.exact.computeWalk.count ((i : ℕ) + 1) :=
    exactFinalTransitionEnv_walkOverlay_current A i hi 0
  have hln :
      (finalWalkLine .traceCur).eval (exactFinalTransitionEnv A i hi).toSourceEnv =
        A.exact.computeWalk.ln ((i : ℕ) + 1) :=
    exactFinalTransitionEnv_walkLine_current A i hi
  rw [walkQueueNonEmpty_eval, h12, hinv, hcount, hln]
  simp [Int.cast_one, inv_mul_cancel₀ (sub_ne_zero.mpr hne)]

set_option maxHeartbeats 8000000 in
/-- Every canonical current row exposes the five exact walk-overlay values, including endpoint
rows where no successor is available. -/
theorem canonical_gather_walkOverlay_current
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (i : Fin R.problem.cfg.compRows) (c : Fin 5) :
    (overlayCoord .traceCur c).eval
      (gatherCorrectedFinalTypedEnv b
        (envOfTrace
          (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal)).toSourceEnv =
      match c with
      | 0 => A.exact.computeWalk.count ((i : ℕ) + 1)
      | 1 => A.exact.computeWalk.acc ((i : ℕ) + 1)
      | 2 => ComputeTable.childStateTagCol R.computeWalkRows ((i : ℕ) + 1) 0
      | 3 => ComputeTable.childStateTagCol R.computeWalkRows ((i : ℕ) + 1) 1
      | 4 => ComputeTable.childStateTagCol R.computeWalkRows ((i : ℕ) + 1) 2 := by
  have hbase : ∀ j : Fin 13,
      (gatherCorrectedFinalTypedEnv b
        (envOfTrace
          (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal)).baseTrace j =
        finalBaseCell A hn i j :=
    canonical_gather_base_current A hn nodes hnodes b chalVal pubVal orbit i
  have hsel : ∀ j : Fin 11,
      (gatherCorrectedFinalTypedEnv b
        (envOfTrace
          (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal)).baseTrace ⟨j, by omega⟩ =
        if j = OptimizedComputeCodec.stateIndex
            (R.problem.exec.computePubAt i).state then 1 else 0 := by
    intro j
    exact (canonical_gather_base_current A hn nodes hnodes b chalVal pubVal orbit i
      ⟨j, by omega⟩).trans (finalBaseCell_selector A hn i j)
  have hext : ∀ role : Fin 58,
      (gatherCorrectedFinalTypedEnv b
        (envOfTrace
          (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal)).extTrace ⟨role, by omega⟩ =
        formRLeafCore b (encodedRowAt A i) role :=
    canonical_gather_ext_core A hn nodes hnodes b chalVal pubVal orbit i
  have hextNat : ∀ (r : ℕ) (hr : r < 58),
      (gatherCorrectedFinalTypedEnv b
        (envOfTrace
          (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal)).extTrace ⟨r, by omega⟩ =
        formRLeafCore b (encodedRowAt A i) ⟨r, hr⟩ := by
    intro r hr
    simpa only using hext ⟨r, hr⟩
  have hextSmall : ∀ (r : ℕ) (hr : r < 41),
      (gatherCorrectedFinalTypedEnv b
        (envOfTrace
          (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal)).extTrace ⟨r, by omega⟩ =
        coreExtensionValue (encodedRowAt A i) ⟨r, by omega⟩ := by
    intro r hr
    have h58 : r < 58 := Nat.lt_trans hr (by decide)
    rw [hext ⟨r, h58⟩]
    exact formRLeafCore_eq_core b _ ⟨r, h58⟩
      ⟨Nat.ne_of_lt hr, Nat.ne_of_lt (Nat.lt_trans hr (by decide))⟩
  fin_cases c <;>
    cases hs : (R.problem.exec.computePubAt i).state <;>
    norm_num [overlayCoord, Nock.Reified.allStates, Nock.Reified.opCol, Expr.eval,
      Fin.ext_iff, pubFP, ext0, CorrectedFinalTypedEnv.toSourceEnv,
      hbase, hsel, hextSmall,
      exactFinalExtensionRow, coreExtensionValue, encodedRowAt, sampledEncode,
      sampledEncodeExtension, sampledOverlayA, OptimizedComputeCodec.fpCoordinate,
      OptimizedComputeCodec.encodeBase, OptimizedComputeCodec.stateIndex, finalBaseCell,
      overlayRoleA, overlayRoleB, overlayANat, overlayBNat, overlayAt, hs]

/-- On the canonical first row the public initial-state masks are the row's trace selectors
(H1.W: the `firstReader` selectors of the in-gate walk boundary). -/
theorem canonical_initialMask_eq_selector
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hpub : ExactFinalPublicCoordinates b R hn pubVal) (st : ComputeTable.State) :
    let env := (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes ⟨0, hn⟩) chalVal pubVal)).toSourceEnv
    (initialMask st).eval env = env.trace (Nock.Reified.opCol st) := by
  dsimp only
  have hsel := fun j : Fin 11 =>
    canonical_gather_initialSelectorPublic A hn nodes b chalVal pubVal orbit hpub
      (⟨0, hn⟩ : Fin _) j
  have hbase := fun j : Fin 11 =>
    (canonical_gather_base_current A hn nodes hnodes b chalVal pubVal orbit
      (⟨0, hn⟩ : Fin _) ⟨j, by omega⟩).trans
      (finalBaseCell_selector A hn (⟨0, hn⟩ : Fin _) j)
  have hop : Nock.Reified.opCol st = (OptimizedComputeCodec.stateIndex st : ℕ) := by
    cases st <;> rfl
  have hj := (OptimizedComputeCodec.stateIndex st).isLt
  have hnot2 : ¬ 20 + (OptimizedComputeCodec.stateIndex st : ℕ) < 3 := by omega
  have hpubRange : 20 ≤ 20 + (OptimizedComputeCodec.stateIndex st : ℕ) ∧
      20 + (OptimizedComputeCodec.stateIndex st : ℕ) < 42 := by omega
  have htrace : (OptimizedComputeCodec.stateIndex st : ℕ) < 13 := by omega
  simp only [initialMask, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, hop]
  simp only [dif_neg hnot2, dif_pos hpubRange, dif_pos htrace,
    Nat.add_sub_cancel_left]
  rw [hsel (OptimizedComputeCodec.stateIndex st),
    hbase (OptimizedComputeCodec.stateIndex st)]

theorem canonical_initialOverlayCoord_first
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hpub : ExactFinalPublicCoordinates b R hn pubVal) (c : Fin 5) :
    let env := (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes ⟨0, hn⟩) chalVal pubVal)).toSourceEnv
    (initialOverlayCoord c).eval env = (overlayCoord .traceCur c).eval env := by
  dsimp only
  let env := (gatherCorrectedFinalTypedEnv b
    (envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes ⟨0, hn⟩) chalVal pubVal)).toSourceEnv
  have hsel := fun j : Fin 11 =>
    canonical_gather_initialSelectorPublic A hn nodes b chalVal pubVal orbit hpub
      (⟨0, hn⟩ : Fin _) j
  have hbase := fun j : Fin 11 =>
    (canonical_gather_base_current A hn nodes hnodes b chalVal pubVal orbit
      (⟨0, hn⟩ : Fin _) ⟨j, by omega⟩).trans
      (finalBaseCell_selector A hn (⟨0, hn⟩ : Fin _) j)
  have hmask : ∀ st : ComputeTable.State,
      (initialMask st).eval env =
        (Expr.Var .traceCur (Nock.Reified.opCol st)).eval env := by
    intro st
    have hop : Nock.Reified.opCol st = (OptimizedComputeCodec.stateIndex st : ℕ) := by
      cases st <;> rfl
    have hj := (OptimizedComputeCodec.stateIndex st).isLt
    have hnot2 : ¬ 20 + (OptimizedComputeCodec.stateIndex st : ℕ) < 3 := by omega
    have hpubRange : 20 ≤ 20 + (OptimizedComputeCodec.stateIndex st : ℕ) ∧
        20 + (OptimizedComputeCodec.stateIndex st : ℕ) < 42 := by omega
    have htrace : (OptimizedComputeCodec.stateIndex st : ℕ) < 13 := by omega
    simp only [env, initialMask, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, hop]
    simp only [dif_neg hnot2, dif_pos hpubRange, dif_pos htrace,
      Nat.add_sub_cancel_left]
    rw [hsel (OptimizedComputeCodec.stateIndex st),
      hbase (OptimizedComputeCodec.stateIndex st)]
  have hfold : ∀ (xs : List ComputeTable.State) (f : ComputeTable.State → Expr),
      (xs.foldr (fun st acc => Expr.Add (Expr.Mul (initialMask st) (f st)) acc)
        (Expr.Const 0)).eval env =
      (xs.foldr (fun st acc =>
        Expr.Add (Expr.Mul (Expr.Var .traceCur (Nock.Reified.opCol st)) (f st)) acc)
        (Expr.Const 0)).eval env := by
    intro xs f
    induction xs with
    | nil => rfl
    | cons st xs ih => simp only [List.foldr, Expr.eval, hmask st, ih]
  fin_cases c <;> norm_num [initialOverlayCoord, overlayCoord] <;>
    apply hfold

theorem canonical_terminalOverlayCoord_last
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hpub : ExactFinalPublicCoordinates b R hn pubVal) (c : Fin 5) :
    let last : Fin R.problem.cfg.compRows :=
      ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
    let env := (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes last) chalVal pubVal)).toSourceEnv
    (terminalOverlayCoord c).eval env = (overlayCoord .traceCur c).eval env := by
  dsimp only
  let last : Fin R.problem.cfg.compRows :=
    ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
  let env := (gatherCorrectedFinalTypedEnv b
    (envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes last) chalVal pubVal)).toSourceEnv
  have hsel := fun j : Fin 11 =>
    canonical_gather_terminalSelectorPublic A hn nodes b chalVal pubVal orbit hpub last j
  have hbase := fun j : Fin 11 =>
    (canonical_gather_base_current A hn nodes hnodes b chalVal pubVal orbit
      last ⟨j, by omega⟩).trans (finalBaseCell_selector A hn last j)
  have hmask : ∀ st : ComputeTable.State,
      (terminalMask st).eval env =
        (Expr.Var .traceCur (Nock.Reified.opCol st)).eval env := by
    intro st
    have hop : Nock.Reified.opCol st = (OptimizedComputeCodec.stateIndex st : ℕ) := by
      cases st <;> rfl
    have hj := (OptimizedComputeCodec.stateIndex st).isLt
    have hnot2 : ¬ 31 + (OptimizedComputeCodec.stateIndex st : ℕ) < 3 := by omega
    have hpubRange : 20 ≤ 31 + (OptimizedComputeCodec.stateIndex st : ℕ) ∧
        31 + (OptimizedComputeCodec.stateIndex st : ℕ) < 42 := by omega
    have htrace : (OptimizedComputeCodec.stateIndex st : ℕ) < 13 := by omega
    simp only [env, terminalMask, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, hop]
    simp only [dif_neg hnot2, dif_pos hpubRange, dif_pos htrace]
    have hsub : 31 + (OptimizedComputeCodec.stateIndex st : ℕ) - 20 =
        11 + (OptimizedComputeCodec.stateIndex st : ℕ) := by omega
    have hfin :
        (⟨31 + (OptimizedComputeCodec.stateIndex st : ℕ) - 20,
          by omega⟩ : Fin 22) =
        ⟨11 + (OptimizedComputeCodec.stateIndex st : ℕ), by omega⟩ :=
      Fin.ext hsub
    rw [hfin, hsel (OptimizedComputeCodec.stateIndex st),
      hbase (OptimizedComputeCodec.stateIndex st)]
  have hfold : ∀ (xs : List ComputeTable.State) (f : ComputeTable.State → Expr),
      (xs.foldr (fun st acc => Expr.Add (Expr.Mul (terminalMask st) (f st)) acc)
        (Expr.Const 0)).eval env =
      (xs.foldr (fun st acc =>
        Expr.Add (Expr.Mul (Expr.Var .traceCur (Nock.Reified.opCol st)) (f st)) acc)
        (Expr.Const 0)).eval env := by
    intro xs f
    induction xs with
    | nil => rfl
    | cons st xs ih => simp only [List.foldr, Expr.eval, hmask st, ih]
  fin_cases c <;> norm_num [terminalOverlayCoord, overlayCoord] <;>
    apply hfold

/-- Roles `41` (`f_t.leaf`) and `44` (`f_th.leaf`).  Gather stores `formRLeafCore` there. -/
def readsLeafRole : CorrectedFinalTypedExpr → Bool
  | .extCur i | .extNext i => decide ((i : ℕ) = 41 ∨ (i : ℕ) = 44)
  | .add x y | .sub x y | .mul x y => readsLeafRole x || readsLeafRole y
  | .neg x | .pow x _ => readsLeafRole x
  | _ => false

def terminalAvoidsLeaf (e : Expr) : Bool :=
  match correctedLowerFinal e with
  | none => false
  | some t => !readsLeafRole t

/-- Form R put roles `41` and `44` into the terminal family, so
`terminalAvoidsLeaf e = true` is not true of every member.  A gate still
transports when it does not read those roles, or when both environments store
the same `formRLeafCore` there. -/
def readsExactRoleCur (n : ℕ) : CorrectedFinalTypedExpr → Bool
  | .extCur i => decide ((i : ℕ) = n)
  | .add x y | .sub x y | .mul x y => readsExactRoleCur n x || readsExactRoleCur n y
  | .neg x | .pow x _ => readsExactRoleCur n x
  | _ => false

def readsExactRoleNext (n : ℕ) : CorrectedFinalTypedExpr → Bool
  | .extNext i => decide ((i : ℕ) = n)
  | .add x y | .sub x y | .mul x y => readsExactRoleNext n x || readsExactRoleNext n y
  | .neg x | .pow x _ => readsExactRoleNext n x
  | _ => false

/-- Exact row whose extension roles below `58` are `formRLeafCore`.  Roles `60..62`
stay the exact accumulator, walk line, and queue inverse.  At roles `41` and `44`
this is the encoded core the canonical gather reads. -/
def withFormRLeaf (b : Basis (Fin 3) F K)
    (rowCur rowNext : OptimizedComputeCodec.Row F K)
    (env : CorrectedFinalTypedEnv F K) : CorrectedFinalTypedEnv F K where
  baseTrace := env.baseTrace
  baseTraceNext := env.baseTraceNext
  extTrace role :=
    if h : role.val < 58 then formRLeafCore b rowCur ⟨role.val, h⟩ else env.extTrace role
  extTraceNext role :=
    if h : role.val < 58 then formRLeafCore b rowNext ⟨role.val, h⟩ else env.extTraceNext role
  chal := env.chal
  extensionPublic := env.extensionPublic
  scalarPublic := env.scalarPublic
  certBase := env.certBase
  certExt := env.certExt
  certBaseNext := env.certBaseNext
  certExtNext := env.certExtNext
  expCol := env.expCol
  expColNext := env.expColNext

theorem withFormRLeaf_ext_formR (b : Basis (Fin 3) F K)
    (rowCur rowNext : OptimizedComputeCodec.Row F K)
    (env : CorrectedFinalTypedEnv F K) (role : Fin 63) (h : role.val < 58) :
    (withFormRLeaf b rowCur rowNext env).extTrace role =
      formRLeafCore b rowCur ⟨role.val, h⟩ := by
  simp [withFormRLeaf, h]

theorem withFormRLeaf_extNext_formR (b : Basis (Fin 3) F K)
    (rowCur rowNext : OptimizedComputeCodec.Row F K)
    (env : CorrectedFinalTypedEnv F K) (role : Fin 63) (h : role.val < 58) :
    (withFormRLeaf b rowCur rowNext env).extTraceNext role =
      formRLeafCore b rowNext ⟨role.val, h⟩ := by
  simp [withFormRLeaf, h]

theorem withFormRLeaf_ext_high (b : Basis (Fin 3) F K)
    (rowCur rowNext : OptimizedComputeCodec.Row F K)
    (env : CorrectedFinalTypedEnv F K) (role : Fin 63) (h : ¬ role.val < 58) :
    (withFormRLeaf b rowCur rowNext env).extTrace role = env.extTrace role := by
  simp [withFormRLeaf, h]

theorem withFormRLeaf_extNext_high (b : Basis (Fin 3) F K)
    (rowCur rowNext : OptimizedComputeCodec.Row F K)
    (env : CorrectedFinalTypedEnv F K) (role : Fin 63) (h : ¬ role.val < 58) :
    (withFormRLeaf b rowCur rowNext env).extTraceNext role = env.extTraceNext role := by
  simp [withFormRLeaf, h]

private theorem not_leaf_role_of_reads (i : ℕ) (h : decide ((i = 41 ∨ i = 44)) = false) :
    i ≠ 41 ∧ i ≠ 44 := by
  have hnot : ¬ (i = 41 ∨ i = 44) := of_decide_eq_false h
  exact ⟨fun h41 => hnot (Or.inl h41), fun h44 => hnot (Or.inr h44)⟩


theorem canonical_walk_endpoint_sources
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hchal6 : ∀ k : Fin 3,
      chalVal (3 * 6 + (k : ℕ)) = coord b (exactFinalChallenge A 6) k)
    (hchal10 : ∀ k : Fin 3,
      chalVal (3 * 10 + (k : ℕ)) = coord b (exactFinalChallenge A 10) k)
    (hpub : ExactFinalPublicCoordinates b R hn pubVal) :
    let first : Fin R.problem.cfg.compRows := ⟨0, hn⟩
    let last : Fin R.problem.cfg.compRows :=
      ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
    let firstEnv := (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes first) chalVal pubVal)).toSourceEnv
    let lastEnv := (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes last) chalVal pubVal)).toSourceEnv
    finalOptimizedWalkLn1.eval firstEnv = 0 ∧
      finalOptimizedWalkCount1.eval firstEnv = 0 ∧
      finalOptimizedWalkAccInit.eval firstEnv = 0 ∧
      finalOptimizedWalkOut.eval lastEnv = 0 := by
  dsimp only
  let first : Fin R.problem.cfg.compRows := ⟨0, hn⟩
  let last : Fin R.problem.cfg.compRows :=
    ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
  let firstTyped := gatherCorrectedFinalTypedEnv b
    (envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes first) chalVal pubVal)
  let lastTyped := gatherCorrectedFinalTypedEnv b
    (envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes last) chalVal pubVal)
  have hline :
      (finalWalkLine .traceCur).eval firstTyped.toSourceEnv =
        A.exact.computeWalk.ln 1 := by
    simpa [first, firstTyped, finalWalkLine, finalWalkLineIndex, finalWalkLineRole,
      ext0, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv] using
      canonical_gather_walkLine A hn nodes hnodes b chalVal pubVal orbit first
  have hchallenge :
      (walkChallenge 0).eval firstTyped.toSourceEnv = R.computeWalkAlpha := by
    simpa [firstTyped, walkChallenge, walkChallengeBase, Expr.eval,
      CorrectedFinalTypedEnv.toSourceEnv, exactFinalChallenge] using
      canonical_gather_challenge_of_coordinates A hn nodes b chalVal pubVal orbit
        (6 : Fin 12) (exactFinalChallenge A 6) hchal6 first
  have hgamma :
      ComputeWalkLabel.walkGammaChallenge.eval firstTyped.toSourceEnv = R.walkGamma := by
    simpa [firstTyped, ComputeWalkLabel.walkGammaChallenge,
      ComputeWalkLabel.walkGammaChallengeIndex, Expr.eval,
      CorrectedFinalTypedEnv.toSourceEnv, exactFinalChallenge] using
      canonical_gather_challenge_of_coordinates A hn nodes b chalVal pubVal orbit
        (10 : Fin 12) (exactFinalChallenge A 10) hchal10 first
  have hepub0 :
      firstTyped.extensionPublic 0 = R.computeWalkAlpha := by
    simpa [firstTyped] using
      canonical_gather_extensionPublic A hn nodes b chalVal pubVal orbit hpub first (0 : Fin 3)
        (by decide)
  have hinit (c : Fin 5) :
      (initialOverlayCoord c).eval firstTyped.toSourceEnv =
        (overlayCoord .traceCur c).eval firstTyped.toSourceEnv := by
    simpa [first, firstTyped] using
      canonical_initialOverlayCoord_first A hn nodes hnodes b chalVal pubVal orbit hpub c
  have hoverFirst (c : Fin 5) :
      (overlayCoord .traceCur c).eval firstTyped.toSourceEnv =
        match c with
        | 0 => A.exact.computeWalk.count 1
        | 1 => A.exact.computeWalk.acc 1
        | 2 => ComputeTable.childStateTagCol R.computeWalkRows 1 0
        | 3 => ComputeTable.childStateTagCol R.computeWalkRows 1 1
        | 4 => ComputeTable.childStateTagCol R.computeWalkRows 1 2 := by
    simpa [first, firstTyped] using
      canonical_gather_walkOverlay_current A hn nodes hnodes b chalVal pubVal orbit first c
  have hoverLast (c : Fin 5) :
      (overlayCoord .traceCur c).eval lastTyped.toSourceEnv =
        match c with
        | 0 => A.exact.computeWalk.count R.problem.cfg.compRows
        | 1 => A.exact.computeWalk.acc R.problem.cfg.compRows
        | 2 => ComputeTable.childStateTagCol R.computeWalkRows R.problem.cfg.compRows 0
        | 3 => ComputeTable.childStateTagCol R.computeWalkRows R.problem.cfg.compRows 1
        | 4 => ComputeTable.childStateTagCol R.computeWalkRows R.problem.cfg.compRows 2 := by
    have hlast : (last : ℕ) + 1 = R.problem.cfg.compRows := by
      simp [last, Nat.sub_add_cancel hn]
    simpa [lastTyped, hlast] using
      canonical_gather_walkOverlay_current A hn nodes hnodes b chalVal pubVal orbit last c
  -- H1.W: the canonical first row agrees with its current-row environment on every trace
  -- column the in-gate label reads.
  have hbase : ∀ j : Fin 13, firstTyped.baseTrace j = finalBaseCell A hn first j := fun j => by
    simpa [first, firstTyped] using
      canonical_gather_base_current A hn nodes hnodes b chalVal pubVal orbit first j
  have hext : ∀ role : Fin 58,
      firstTyped.extTrace ⟨role, by omega⟩ =
        formRLeafCore b (OptimizedComputeSampledTrace.encodedRowAt A first) role := fun role => by
    simpa [first, firstTyped] using
      canonical_gather_ext_core A hn nodes hnodes b chalVal pubVal orbit first role
  let exR := withFormRLeaf b (encodedRowAt A first) (encodedRowAt A first)
    (exactFinalCurrentEnv A first)
  have htrace : ∀ j, j < 71 →
      firstTyped.toSourceEnv.trace j = exR.toSourceEnv.trace j := by
    intro j hj
    by_cases h13 : j < 13
    · simp only [CorrectedFinalTypedEnv.toSourceEnv, dif_pos h13, exR, withFormRLeaf,
        exactFinalCurrentEnv]
      rw [hbase ⟨j, h13⟩]
    · have h76 : j < 76 := Nat.lt_trans hj (by decide)
      have h58 : j - 13 < 58 := by omega
      simp only [CorrectedFinalTypedEnv.toSourceEnv, dif_neg h13, dif_pos h76, exR]
      exact (hext ⟨j - 13, h58⟩).trans
        (withFormRLeaf_ext_formR b _ _ _ ⟨j - 13, by omega⟩ h58).symm
  have hmask : ∀ st, (initialMask st).eval firstTyped.toSourceEnv =
      firstTyped.toSourceEnv.trace (Nock.Reified.opCol st) := fun st => by
    simpa [first, firstTyped] using
      canonical_initialMask_eq_selector A hn nodes hnodes b chalVal pubVal orbit hpub st
  have hselF : ∀ st, (ComputeWalkLabel.firstReader.sel st).eval firstTyped.toSourceEnv =
      if st = (R.problem.exec.computePubAt first).state then 1 else 0 := by
    intro st
    have hop : Nock.Reified.opCol st < 71 := by cases st <;> decide
    have hop13 : Nock.Reified.opCol st < 13 := by cases st <;> decide
    show (initialMask st).eval firstTyped.toSourceEnv = _
    rw [hmask st, htrace _ hop]
    have hcol : exR.toSourceEnv.trace (Nock.Reified.opCol st) =
        (exactFinalCurrentEnv A first).toSourceEnv.trace (Nock.Reified.opCol st) := by
      simp [exR, withFormRLeaf, CorrectedFinalTypedEnv.toSourceEnv, exactFinalCurrentEnv, hop13]
    rw [hcol]
    exact exactFinalCurrentEnv_selectors A first st
  have hagree : ∀ k, k < 71 → k ≠ 54 → k ≠ 57 →
      exR.toSourceEnv.trace k = (exactFinalCurrentEnv A first).toSourceEnv.trace k := by
    intro k hk h54 h57
    by_cases h13 : k < 13
    · simp [exR, withFormRLeaf, CorrectedFinalTypedEnv.toSourceEnv, exactFinalCurrentEnv, h13]
    · have h76 : k < 76 := Nat.lt_trans hk (by decide)
      have h58 : k - 13 < 58 := by omega
      have hne : k - 13 ≠ 41 ∧ k - 13 ≠ 44 := by
        constructor <;> intro hkrole <;> omega
      simp [exR, withFormRLeaf, CorrectedFinalTypedEnv.toSourceEnv, exactFinalCurrentEnv,
        exactFinalExtensionRow, h13, h76, h58]
      exact formRLeafCore_eq_core b _ ⟨k - 13, h58⟩ hne
  have hsrcF : ∀ (r c : ℕ) (hr : r < 12) (hc : c < 3),
      (ComputeWalkLabel.sourcePubAtR ComputeWalkLabel.firstReader
          (R.problem.exec.computePubAt first).state r c).eval firstTyped.toSourceEnv =
        OptimizedComputeCodec.fpCoordinate
          (OptimizedComputeCodec.pubFingerprint (R.problem.exec.computePubAt first) ⟨r, hr⟩)
          ⟨c, hc⟩ := by
    intro r c hr hc
    rw [ComputeWalkLabel.sourcePubAtR_first,
      ComputeWalkLabel.sourcePubAtR_cur_eval_congr htrace _ r c hr hc]
    have hmove : (ComputeWalkLabel.sourcePubAtR ComputeWalkLabel.curReader
        (R.problem.exec.computePubAt first).state r c).eval exR.toSourceEnv =
      (ComputeWalkLabel.sourcePubAtR ComputeWalkLabel.curReader
        (R.problem.exec.computePubAt first).state r c).eval
        (exactFinalCurrentEnv A first).toSourceEnv := by
      by_cases hread : (R.problem.exec.computePubAt first).state = .s1 ∧ r = 2 ∧ c = 2
      · -- Column `54` is role `41`. `formRLeafCore` is the encoded core at every role.
        refine ComputeWalkLabel.sourcePubAtR_cur_eval_congr ?_ _ r c hr hc
        intro j hj
        by_cases h54 : j = 54
        · have h58 : j - 13 < 58 := by omega
          simp [exR, withFormRLeaf, CorrectedFinalTypedEnv.toSourceEnv, exactFinalCurrentEnv,
            exactFinalExtensionRow, h54, h58, formRLeafCore_eq_core_all]
        · by_cases h57 : j = 57
          · have h58 : j - 13 < 58 := by omega
            simp [exR, withFormRLeaf, CorrectedFinalTypedEnv.toSourceEnv, exactFinalCurrentEnv,
              exactFinalExtensionRow, h57, h58, formRLeafCore_eq_core_all]
          · exact hagree j hj h54 h57
      · refine ComputeWalkLabel.sourcePubAtR_cur_eval_congr_offLeaf
          (fun j hj h54 h57 => hagree j hj h54 h57) _ r c hr hc ?_
        by_contra hcon
        exact hread (by simpa [not_or, not_not] using hcon)
    rw [hmove]
    exact exactFinalCurrentEnv_sourcePubAtR A hA first r c hr hc
  have htagF : ∀ j, (ComputeWalkLabel.childTagHost ComputeWalkLabel.firstReader
        (R.problem.exec.computePubAt first).state j).eval firstTyped.toSourceEnv =
      ComputeTable.childStateTagCol R.computeWalkRows 1 j := by
    intro j
    rw [ComputeWalkLabel.childTagHost_first, ComputeWalkLabel.childTagHost_cur_eval_congr htrace]
    rw [ComputeWalkLabel.childTagHost_cur_eval_congr_offLeaf hagree]
    simpa [first] using exactFinalCurrentEnv_childTagHost A first j
  have hα : ComputeWalkLabel.walkAlphaChallenge.eval firstTyped.toSourceEnv =
      R.computeWalkAlpha := hchallenge
  have hcurF := ComputeWalkLabel.labelRLC_eval ComputeWalkLabel.firstReader
    firstTyped.toSourceEnv (R.problem.exec.computePubAt first) R.walkGamma hselF hsrcF hgamma
  have hccF := ComputeWalkLabel.childSumCC_eval ComputeWalkLabel.firstReader
    firstTyped.toSourceEnv (R.problem.exec.computePubAt first) R.computeWalkAlpha R.walkGamma
    (fun j => ComputeTable.childStateTagCol R.computeWalkRows 1 j) hselF hsrcF hα hgamma htagF
  have hcmF := ComputeWalkLabel.selectorCM_eval ComputeWalkLabel.firstReader
    firstTyped.toSourceEnv (R.problem.exec.computePubAt first) R.computeWalkAlpha hselF hα
  have hlabel := hA.2.2.2
  have hcurW := curCol_eq_rlc_label hlabel.1 first
  have hccW := walkCC_eq_childSum hlabel.1 hlabel.2 first
  have hcmW := walkCM_eq_pow hlabel.2 first
  simp only [first, Fin.val_mk, Nat.zero_add] at hcurW hccW hcmW
  have hw := hA.2.1.1
  have hterminal := hA.2.1.2
  have hpub0source : firstTyped.toSourceEnv.pub 0 = R.computeWalkAlpha := by
    simpa [CorrectedFinalTypedEnv.toSourceEnv] using hepub0
  constructor
  · simp only [finalOptimizedWalkLn1, Expr.eval_subst, Trans.walkLn1, Reified.tc,
      Reified.chl, Expr.eval, Env.ofSubst, finalWalkInitialSubst]
    rw [hline, hchallenge, hw.ln1]
    simp
  constructor
  · simp only [finalOptimizedWalkCount1, Expr.eval_subst, Trans.walkCount1,
      Reified.tc, Trans.pubv, Expr.eval, Env.ofSubst, finalWalkInitialSubst]
    rw [show (initialOverlayCoord 0).eval _ =
          (overlayCoord .traceCur 0).eval _ by simpa using hinit (0 : Fin 5)]
    rw [show (overlayCoord .traceCur 0).eval _ =
          A.exact.computeWalk.count 1 by simpa using hoverFirst (0 : Fin 5)]
    rw [hpub0source, hcmF, ← hcmW, hw.count1]
    simp [Nock.Reified.Trans.walkCM]
  constructor
  · simp only [finalOptimizedWalkAccInit, Expr.eval_subst, Trans.walkAccInit,
      Reified.tc, Trans.pubv, Expr.eval, Env.ofSubst, finalWalkInitialSubst]
    rw [hline, hcurF, ← hcurW]
    rw [show (initialOverlayCoord 1).eval _ =
          (overlayCoord .traceCur 1).eval _ by simpa using hinit (1 : Fin 5)]
    rw [show (overlayCoord .traceCur 1).eval _ =
          A.exact.computeWalk.acc 1 by simpa using hoverFirst (1 : Fin 5)]
    rw [hpub0source, hccF, ← hccW]
    have hepub1 :
        firstTyped.extensionPublic 1 = R.computeWalkSeed := by
      simpa [firstTyped] using
        canonical_gather_extensionPublic A hn nodes b chalVal pubVal orbit hpub first (1 : Fin 3)
          (by decide)
    have hpub1source : firstTyped.toSourceEnv.pub 1 = R.computeWalkSeed := by
      simpa [CorrectedFinalTypedEnv.toSourceEnv] using hepub1
    rw [hpub1source]
    apply sub_eq_zero.mpr
    rw [Nock.Reified.Trans.c_mul_walkCC]
    exact hw.accInit
  · simp only [finalOptimizedWalkOut, Expr.eval_subst, Trans.walkOut, Reified.tc,
      Expr.eval, Env.ofSubst, finalWalkTerminalSubst]
    have hterm := canonical_terminalOverlayCoord_last
      A hn nodes hnodes b chalVal pubVal orbit hpub (1 : Fin 5)
    rw [show (terminalOverlayCoord 1).eval lastTyped.toSourceEnv =
        (overlayCoord .traceCur 1).eval lastTyped.toSourceEnv by
      simpa [last, lastTyped] using hterm]
    have hl :
        (overlayCoord .traceCur 1).eval lastTyped.toSourceEnv =
          A.exact.computeWalk.acc R.problem.cfg.compRows := by
      simpa using hoverLast (1 : Fin 5)
    exact hl.trans hterminal

/-- The two source values used by the complete walk-init collision event vanish on the exact
canonical first row. -/
theorem canonical_masked_walk_init_sources
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hchal : ExactFinalChallengeCoordinates b A chalVal)
    (hpub : ExactFinalPublicCoordinates b R hn pubVal) :
    let first : Fin R.problem.cfg.compRows := ⟨0, hn⟩
    let env := (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes first) chalVal pubVal)).toSourceEnv
    finalMaskedWalkLn1.eval env = 0 ∧ finalMaskedWalkCount1.eval env = 0 := by
  dsimp only
  have h := canonical_walk_endpoint_sources A hA hn nodes hnodes b chalVal pubVal
    orbit (fun k => hchal 6 k) (fun k => hchal 10 k) hpub
  constructor
  · simp [finalMaskedWalkLn1, Expr.eval, h.1]
  · simp [finalMaskedWalkCount1, Expr.eval, h.2.1]

theorem canonical_endpoint_obligations
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hchal6 : ∀ k : Fin 3,
      chalVal (3 * 6 + (k : ℕ)) = coord b (exactFinalChallenge A 6) k)
    (hchal10 : ∀ k : Fin 3,
      chalVal (3 * 10 + (k : ℕ)) = coord b (exactFinalChallenge A 10) k)
    (hpub : ExactFinalPublicCoordinates b R hn pubVal)
    (hreq : ExactFinalRequestsCoordinate b A pubVal)
    (hln : ExactFinalLineOrigin R hn)
    (i : Fin R.problem.cfg.compRows) :
    let envF := envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal
    let env := gatherCorrectedFinalTypedEnv b envF
    (∀ t ∈ correctedEndpoint2, t.eval env = 0) ∧
      (∀ t ∈ correctedEndpoint4, t.eval env = 0) := by
  dsimp only
  let envF := envOfTrace
    (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
    orbit.ω (nodes i) chalVal pubVal
  let env := gatherCorrectedFinalTypedEnv b envF
  have hend := canonical_walk_endpoint_sources
    A hA hn nodes hnodes b chalVal pubVal orbit hchal6 hchal10 hpub
  have hb11 := canonical_gather_base_current
    A hn nodes hnodes b chalVal pubVal orbit i (11 : Fin 13)
  have hb12 := canonical_gather_base_current
    A hn nodes hnodes b chalVal pubVal orbit i (12 : Fin 13)
  have hwalkLn1 : finalMaskedWalkLn1.eval env.toSourceEnv = 0 := by
    by_cases hi0 : (i : ℕ) = 0
    · have hiEq : i = ⟨0, hn⟩ := Fin.ext hi0
      subst i
      have hb1 : env.baseTrace 11 = 1 := by
        have hx := hb11
        simpa [env, finalBaseCell] using hx
      have hm : fixedIsFirst.eval env.toSourceEnv = 1 := by
        simp [fixedIsFirst, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, hb1]
      simp only [finalMaskedWalkLn1, Expr.eval]
      rw [hm, hend.1]
      ring
    · have hb0 : env.baseTrace 11 = 0 := by
        simpa [env, finalBaseCell, hi0] using hb11
      simp [finalMaskedWalkLn1, fixedIsFirst, Expr.eval,
        CorrectedFinalTypedEnv.toSourceEnv, hb0]
  have hwalkCount1 : finalMaskedWalkCount1.eval env.toSourceEnv = 0 := by
    by_cases hi0 : (i : ℕ) = 0
    · have hiEq : i = ⟨0, hn⟩ := Fin.ext hi0
      subst i
      have hb1 : env.baseTrace 11 = 1 := by
        have hx := hb11
        simpa [env, finalBaseCell] using hx
      have hm : fixedIsFirst.eval env.toSourceEnv = 1 := by
        simp [fixedIsFirst, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, hb1]
      simp only [finalMaskedWalkCount1, Expr.eval]
      rw [hm, hend.2.1]
      ring
    · have hb0 : env.baseTrace 11 = 0 := by
        simpa [env, finalBaseCell, hi0] using hb11
      simp [finalMaskedWalkCount1, fixedIsFirst, Expr.eval,
        CorrectedFinalTypedEnv.toSourceEnv, hb0]
  have hterminal : finalMaskedWalkOut.eval env.toSourceEnv = 0 := by
    let last : Fin R.problem.cfg.compRows :=
      ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
    by_cases hilast : i = last
    · subst i
      have hb1 : env.baseTrace 12 = 1 := by
        have hx := hb12
        simpa [env, finalBaseCell, last] using hx
      have hm : fixedIsLast.eval env.toSourceEnv = 1 := by
        simp [fixedIsLast, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, hb1]
      simp only [finalMaskedWalkOut, Expr.eval]
      rw [hm, hend.2.2.2]
      ring
    · have hb0 : env.baseTrace 12 = 0 := by
        simpa [env, finalBaseCell, last, hilast] using hb12
      simp [finalMaskedWalkOut, fixedIsLast, Expr.eval,
        CorrectedFinalTypedEnv.toSourceEnv, hb0]
  have hacc : finalMaskedWalkAccInit.eval env.toSourceEnv = 0 := by
    by_cases hi0 : (i : ℕ) = 0
    · have hiEq : i = ⟨0, hn⟩ := Fin.ext hi0
      subst i
      have hb1 : env.baseTrace 11 = 1 := by
        have hx := hb11
        simpa [env, finalBaseCell] using hx
      have hm : fixedIsFirst.eval env.toSourceEnv = 1 := by
        simp [fixedIsFirst, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, hb1]
      simp only [finalMaskedWalkAccInit, Expr.eval]
      rw [hm, hend.2.2.1]
      ring
    · have hb0 : env.baseTrace 11 = 0 := by
        simpa [env, finalBaseCell, hi0] using hb11
      simp [finalMaskedWalkAccInit, fixedIsFirst, Expr.eval,
        CorrectedFinalTypedEnv.toSourceEnv, hb0]
  -- A-comp anchoring: `isFirst · acc = 0`
  have haccInit : finalAccInit.eval env.toSourceEnv = 0 := by
    have h45 : env.toSourceEnv.trace 45 = env.extTrace 32 := by
      simp [CorrectedFinalTypedEnv.toSourceEnv]
    by_cases hi0 : (i : ℕ) = 0
    · have hiEq : i = ⟨0, hn⟩ := Fin.ext hi0
      subst i
      have h32 := canonical_gather_ext_core A hn nodes hnodes b chalVal pubVal orbit ⟨0, hn⟩
        (32 : Fin 58)
      rw [formRLeafCore_eq_core b _ (32 : Fin 58) ⟨by decide, by decide⟩] at h32
      rw [coreExtensionValue_sampledAcc] at h32
      have hacc0 : env.extTrace 32 = 0 := by
        have h32' : env.extTrace 32 = ComputeSampledIO.coResidentAccC A.compress10
            R.problem.cfg.challenges.lam R.problem.exec.computeRows ((⟨0, hn⟩ : Fin R.problem.cfg.compRows) : ℕ) := h32
        rw [h32']
        exact ComputeSampledIO.coResidentAccC_zero _ _ _
      simp [finalAccInit, Expr.eval, h45, hacc0]
    · have hb0 : env.baseTrace 11 = 0 := by
        simpa [env, finalBaseCell, hi0] using hb11
      simp [finalAccInit, fixedIsFirst, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, hb0]
  -- A-comp anchoring: `isLast · (acc_after − requests) = 0`
  have haccTerminal : finalAccTerminal.eval env.toSourceEnv = 0 := by
    let last : Fin R.problem.cfg.compRows :=
      ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
    have h73 : env.toSourceEnv.trace OptimizedComputeFiniteIOGates.accAfterIndex =
        env.extTrace 60 := by
      simp [CorrectedFinalTypedEnv.toSourceEnv, OptimizedComputeFiniteIOGates.accAfterIndex]
    have hpub2 : env.toSourceEnv.pub 2 = env.extensionPublic 2 := by
      simp [CorrectedFinalTypedEnv.toSourceEnv]
    by_cases hilast : i = last
    · subst i
      have hb1 : env.baseTrace 12 = 1 := by
        have hx := hb12
        simpa [env, finalBaseCell, last] using hx
      have h60 : env.extTrace 60 = A.witness10.terminal := by
        have h60' := canonical_gather_accAfter A hn nodes hnodes b chalVal pubVal orbit last
        have hlen : ((last : ℕ) + 1) = R.problem.exec.computeRows.length := by
          simp only [last]
          have := R.problem.exec.computeRows_length
          omega
        have h60'' : env.extTrace 60 = ComputeSampledIO.coResidentAccC A.compress10
            R.problem.cfg.challenges.lam R.problem.exec.computeRows ((last : ℕ) + 1) := h60'
        rw [h60'', hlen,
          show A.compress10 = fun v => FiniteIO.compress A.sampled.coins
            (RecordCarrier.extRec R.problem.exec.derivedRequestIO v) from rfl,
          ComputeSampledIO.coResidentAccC_terminal_eq_requestAcc R.problem.exec
            A.witness10_accepts (RecordCarrier.extRec R.problem.exec.derivedRequestIO) rfl]
        exact A.witness10_accepts.requestTerm
      have hreq2 : env.extensionPublic 2 = A.witness10.terminal :=
        canonical_gather_requests A hn nodes b chalVal pubVal orbit hreq last
      simp only [finalAccTerminal, fixedIsLast, Expr.eval, h73, hpub2, h60, hreq2, sub_self,
        mul_zero]
    · have hb0 : env.baseTrace 12 = 0 := by
        simpa [env, finalBaseCell, last, hilast] using hb12
      simp [finalAccTerminal, fixedIsLast, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, hb0]
  -- W6.1 stage 2A: `isFirst · (ln_prev − 1) = 0` (the paper, `:1884`; the origin of the
  -- compute line, which `V_comp` at `:1728-1742` does not check)
  have hlnInit : finalLnInit.eval env.toSourceEnv = 0 := by
    have h67 : env.toSourceEnv.trace 67 = env.extTrace 54 := by
      simp [CorrectedFinalTypedEnv.toSourceEnv]
    by_cases hi0 : (i : ℕ) = 0
    · have hiEq : i = ⟨0, hn⟩ := Fin.ext hi0
      subst i
      have h54 := canonical_gather_ext_core A hn nodes hnodes b chalVal pubVal orbit ⟨0, hn⟩
        (54 : Fin 58)
      rw [formRLeafCore_eq_core b _ (54 : Fin 58) ⟨by decide, by decide⟩] at h54
      rw [coreExtensionValue_lnPrev] at h54
      have hln1 : env.extTrace 54 = 1 := by
        have h54' : env.extTrace 54 =
            (R.problem.exec.computePubAt (⟨0, hn⟩ : Fin R.problem.cfg.compRows)).ln_prev := h54
        rw [h54']
        exact hln
      simp [finalLnInit, OptimizedComputeSubstitution.lnPrev, OptimizedComputeSubstitution.ext0,
        Expr.eval, h67, hln1]
    · have hb0 : env.baseTrace 11 = 0 := by
        simpa [env, finalBaseCell, hi0] using hb11
      simp [finalLnInit, fixedIsFirst, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, hb0]
  constructor
  · intro t ht
    rw [correctedEndpoint2] at ht
    obtain ⟨e, he, hlower⟩ := List.mem_filterMap.mp ht
    rw [← correctedLowerFinal_eval env e t hlower]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hwalkLn1
    · exact hwalkCount1
    · exact hterminal
    · exact haccInit
    · exact haccTerminal
    · exact hlnInit
  · intro t ht
    rw [correctedEndpoint4] at ht
    obtain ⟨e, he, hlower⟩ := List.mem_filterMap.mp ht
    rw [← correctedLowerFinal_eval env e t hlower]
    simp only [List.mem_singleton] at he
    subst e
    exact hacc

/-- **Honest satisfaction of the twenty-two de-compressed endpoint equality checks**
.  It was two compressed gates until stage 3e; the proof got *shorter*, because
the first/last-row coordinate agreements `hcoord` were already what the compressed proof had to
establish before summing them against powers of `challenge36`.  Off the endpoint rows the mask
column is `0` and the product vanishes for every `i` at once. -/
theorem canonical_selectorEquality2
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hpub : ExactFinalPublicCoordinates b R hn pubVal)
    (i : Fin R.problem.cfg.compRows) :
    let envF := envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal
    ∀ g ∈ finalEndpointEqualityChecks, g.eval envF = 0 := by
  dsimp only
  intro g hg
  simp only [finalEndpointEqualityChecks, List.mem_append, List.mem_map,
    List.mem_range] at hg
  rcases hg with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · by_cases hi0 : (i : ℕ) = 0
    · have hiEq : i = ⟨0, hn⟩ := Fin.ext hi0
      subst i
      have hcoord : ∀ jj : Fin 11,
          (envOfTrace
            (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
            orbit.ω (nodes ⟨0, hn⟩) chalVal pubVal).trace jj =
          pubVal (20 + (jj : ℕ)) := by
        intro jj
        rw [correctedCanonicalFinalTrace_base_eval
          A hn nodes hnodes b chalVal pubVal orbit (⟨0, hn⟩ : Fin _) ⟨jj, by omega⟩]
        rw [finalBaseCell_selector, hpub.2.1]
      have hcoord' := hcoord ⟨j, hj⟩
      simp only [Fin.val_mk] at hcoord'
      simp only [endpointEqualityCheck, CoeffExpr.eval, hcoord',
        show (envOfTrace (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes _) chalVal pubVal).pub (20 + j) = pubVal (20 + j) from rfl,
        sub_self, mul_zero]
    · have hm := correctedCanonicalFinalTrace_base_eval
        A hn nodes hnodes b chalVal pubVal orbit i (11 : Fin 13)
      have hm0 :
          (envOfTrace
            (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
            orbit.ω (nodes i) chalVal pubVal).trace 11 = 0 := by
        simpa [finalBaseCell, hi0] using hm
      simp [endpointEqualityCheck, CoeffExpr.eval, isFirstVar, bv, hm0]
  · let last : Fin R.problem.cfg.compRows :=
      ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
    by_cases hilast : i = last
    · subst i
      have hcoord : ∀ jj : Fin 11,
          (envOfTrace
            (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
            orbit.ω (nodes last) chalVal pubVal).trace jj =
          pubVal (31 + (jj : ℕ)) := by
        intro jj
        rw [correctedCanonicalFinalTrace_base_eval
          A hn nodes hnodes b chalVal pubVal orbit last ⟨jj, by omega⟩]
        rw [finalBaseCell_selector, hpub.2.2]
      have hcoord' := hcoord ⟨j, hj⟩
      simp only [Fin.val_mk] at hcoord'
      simp only [endpointEqualityCheck, CoeffExpr.eval, hcoord',
        show (envOfTrace (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes _) chalVal pubVal).pub (31 + j) = pubVal (31 + j) from rfl,
        sub_self, mul_zero]
    · have hm := correctedCanonicalFinalTrace_base_eval
        A hn nodes hnodes b chalVal pubVal orbit i (12 : Fin 13)
      have hm0 :
          (envOfTrace
            (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
            orbit.ω (nodes i) chalVal pubVal).trace 12 = 0 := by
        simpa [finalBaseCell, last, hilast] using hm
      simp [endpointEqualityCheck, CoeffExpr.eval, isLastVar, bv, hm0]

def CorrectedPublicFree : CorrectedFinalTypedExpr → Prop
  | .extensionPublic _ | .scalarPublic _ => False
  | .baseCur _ | .baseNext _ | .extCur _ | .extNext _ | .challenge _ | .const _ => True
  | .certBase _ | .certExt _ | .expCur | .lamPow _ => True
  | .add x y | .sub x y | .mul x y => CorrectedPublicFree x ∧ CorrectedPublicFree y
  | .neg x | .pow x _ => CorrectedPublicFree x

def correctedPublicFreeB : CorrectedFinalTypedExpr → Bool
  | .extensionPublic _ | .scalarPublic _ => false
  | .baseCur _ | .baseNext _ | .extCur _ | .extNext _ | .challenge _ | .const _ => true
  | .certBase _ | .certExt _ | .expCur | .lamPow _ => true
  | .add x y | .sub x y | .mul x y => correctedPublicFreeB x && correctedPublicFreeB y
  | .neg x | .pow x _ => correctedPublicFreeB x

theorem correctedPublicFreeB_iff (t : CorrectedFinalTypedExpr) :
    correctedPublicFreeB t ↔ CorrectedPublicFree t := by
  induction t <;> simp [correctedPublicFreeB, CorrectedPublicFree, *]

/-- Typed support predicate for terminal-current gates: current base columns, normalized
extension roles `0..57`, challenges, and fixed publics only. -/
def CorrectedTerminalCurrentOnly : CorrectedFinalTypedExpr → Prop
  | .baseCur _ | .challenge _ | .extensionPublic _ | .scalarPublic _ | .const _ => True
  | .lamPow _ => True
  | .extCur i => (i : ℕ) < 58
  | .baseNext _ | .extNext _ => False
  | .certBase _ | .certExt _ | .expCur => False
  | .add x y | .sub x y | .mul x y =>
      CorrectedTerminalCurrentOnly x ∧ CorrectedTerminalCurrentOnly y
  | .neg x | .pow x _ => CorrectedTerminalCurrentOnly x

def correctedTerminalCurrentOnlyB : CorrectedFinalTypedExpr → Bool
  | .baseCur _ | .challenge _ | .extensionPublic _ | .scalarPublic _ | .const _ => true
  | .lamPow _ => true
  | .extCur i => decide ((i : ℕ) < 58)
  | .baseNext _ | .extNext _ => false
  | .certBase _ | .certExt _ | .expCur => false
  | .add x y | .sub x y | .mul x y =>
      correctedTerminalCurrentOnlyB x && correctedTerminalCurrentOnlyB y
  | .neg x | .pow x _ => correctedTerminalCurrentOnlyB x

theorem correctedTerminalCurrentOnlyB_iff (t : CorrectedFinalTypedExpr) :
    correctedTerminalCurrentOnlyB t ↔ CorrectedTerminalCurrentOnly t := by
  induction t <;>
    simp [correctedTerminalCurrentOnlyB, CorrectedTerminalCurrentOnly, *]

/-- Terminal-current support that also admits the current row's Form R certificate columns
(the deployed sampled request slots read them). -/
def CorrectedTerminalCurrentOnlyC : CorrectedFinalTypedExpr → Prop
  | .baseCur _ | .challenge _ | .extensionPublic _ | .scalarPublic _ | .const _ => True
  | .lamPow _ | .certBase _ | .certExt _ | .expCur => True
  | .extCur i => (i : ℕ) < 58
  | .baseNext _ | .extNext _ => False
  | .add x y | .sub x y | .mul x y =>
      CorrectedTerminalCurrentOnlyC x ∧ CorrectedTerminalCurrentOnlyC y
  | .neg x | .pow x _ => CorrectedTerminalCurrentOnlyC x

def correctedTerminalCurrentOnlyCB : CorrectedFinalTypedExpr → Bool
  | .baseCur _ | .challenge _ | .extensionPublic _ | .scalarPublic _ | .const _ => true
  | .lamPow _ | .certBase _ | .certExt _ | .expCur => true
  | .extCur i => decide ((i : ℕ) < 58)
  | .baseNext _ | .extNext _ => false
  | .add x y | .sub x y | .mul x y =>
      correctedTerminalCurrentOnlyCB x && correctedTerminalCurrentOnlyCB y
  | .neg x | .pow x _ => correctedTerminalCurrentOnlyCB x

theorem correctedTerminalCurrentOnlyCB_iff (t : CorrectedFinalTypedExpr) :
    correctedTerminalCurrentOnlyCB t ↔ CorrectedTerminalCurrentOnlyC t := by
  induction t <;>
    simp [correctedTerminalCurrentOnlyCB, CorrectedTerminalCurrentOnlyC, *]

/-- Residual-free support that also admits the Form R certificate columns. -/
def CorrectedResidualFreeC : CorrectedFinalTypedExpr → Prop
  | .extCur i | .extNext i => (i : ℕ) < 58 ∨ (i : ℕ) = 61 ∨ (i : ℕ) = 62
  | .baseCur _ | .baseNext _ | .challenge _ | .extensionPublic _
  | .scalarPublic _ | .const _ | .lamPow _ | .certBase _ | .certExt _ | .expCur => True
  | .add x y | .sub x y | .mul x y =>
      CorrectedResidualFreeC x ∧ CorrectedResidualFreeC y
  | .neg x | .pow x _ => CorrectedResidualFreeC x

def correctedResidualFreeCB : CorrectedFinalTypedExpr → Bool
  | .extCur i | .extNext i => (i : ℕ) < 58 || (i : ℕ) == 61 || (i : ℕ) == 62
  | .baseCur _ | .baseNext _ | .challenge _ | .extensionPublic _
  | .scalarPublic _ | .const _ | .lamPow _ | .certBase _ | .certExt _ | .expCur => true
  | .add x y | .sub x y | .mul x y =>
      correctedResidualFreeCB x && correctedResidualFreeCB y
  | .neg x | .pow x _ => correctedResidualFreeCB x

theorem correctedResidualFreeCB_iff (t : CorrectedFinalTypedExpr) :
    correctedResidualFreeCB t ↔ CorrectedResidualFreeC t := by
  induction t <;>
    simp [correctedResidualFreeCB, CorrectedResidualFreeC, or_assoc, *]

def terminalCurrentSourceGood (e : Expr) : Bool :=
  match correctedLowerFinal e with
  | none => false
  | some t => correctedTerminalCurrentOnlyB t && correctedPublicFreeB t

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
theorem terminalCurrentSourceGood_receipt :
    ∀ e ∈ terminalCurrentNonIOSourceFamilies.flatten,
      terminalCurrentSourceGood e = true := by
  decide

/-- Every expression in the thirteen successor-free non-IO families lowers to a typed expression
that observes only current semantic columns and no public input. -/
theorem terminalCurrentNonIOSource_lower_receipt
    (e : Expr) (he : e ∈ terminalCurrentNonIOSourceFamilies.flatten) :
    ∃ t, correctedLowerFinal e = some t ∧
      CorrectedTerminalCurrentOnly t ∧ CorrectedPublicFree t := by
  have hg := terminalCurrentSourceGood_receipt e he
  cases ht : correctedLowerFinal e with
  | none => simp [terminalCurrentSourceGood, ht] at hg
  | some t =>
      simp [terminalCurrentSourceGood, ht] at hg
      refine ⟨t, rfl, ?_, ?_⟩
      · rw [← correctedTerminalCurrentOnlyB_iff]
        exact hg.1
      · rw [← correctedPublicFreeB_iff]
        exact hg.2

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
/-- Compiled typed support for the 76 terminal-current production IDs. -/
theorem correctedFinalExtGate_terminalCurrentOnly
    (gate : CorrectedCoreExtGateId) (hgate : gate ∈ terminalCurrentExtGateIds) :
    CorrectedTerminalCurrentOnlyC (correctedFinalExtGate gate) := by
  rw [← correctedTerminalCurrentOnlyCB_iff]
  have hall : ∀ t ∈ terminalCurrentExtGateIds.map correctedFinalExtGate,
      correctedTerminalCurrentOnlyCB t = true := by decide
  exact hall _ (List.mem_map.mpr ⟨gate, hgate, rfl⟩)

theorem CorrectedFinalTypedExpr.eval_eq_of_terminalCurrentOnly
    {a b : CorrectedFinalTypedEnv F K}
    (hbase : ∀ i, a.baseTrace i = b.baseTrace i)
    (hext : ∀ i : Fin 63, (i : ℕ) < 58 → a.extTrace i = b.extTrace i)
    (hchal : ∀ i, a.chal i = b.chal i)
    (hextPub : ∀ i, a.extensionPublic i = b.extensionPublic i)
    (hscalarPub : ∀ i, a.scalarPublic i = b.scalarPublic i)
    (t : CorrectedFinalTypedExpr) (ht : CorrectedTerminalCurrentOnly t) :
    t.eval a = t.eval b := by
  revert ht
  induction t with
  | baseCur i => intro; simp [CorrectedFinalTypedExpr.eval, hbase]
  | baseNext i => intro h; contradiction
  | extCur i => intro ht; simpa [CorrectedFinalTypedExpr.eval] using hext i ht
  | extNext i => intro h; contradiction
  | challenge i => intro; simp [CorrectedFinalTypedExpr.eval, hchal]
  | extensionPublic i => intro; simp [CorrectedFinalTypedExpr.eval, hextPub]
  | scalarPublic i => intro; simp [CorrectedFinalTypedExpr.eval, hscalarPub]
  | const c => intro; rfl
  | certBase i => intro h; contradiction
  | expCur => intro h; contradiction
  | certExt i => intro h; contradiction
  | lamPow d => intro; simp [CorrectedFinalTypedExpr.eval, hchal]
  | add x y ihx ihy =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· + ·)
        (ihx ht.1) (ihy ht.2)
  | sub x y ihx ihy =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· - ·)
        (ihx ht.1) (ihy ht.2)
  | mul x y ihx ihy =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· * ·)
        (ihx ht.1) (ihy ht.2)
  | neg x ih =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg Neg.neg (ih ht)
  | pow x n ih =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg (fun z => z ^ n) (ih ht)

theorem CorrectedFinalTypedExpr.eval_eq_of_terminalCurrentOnly_skipLeaf
    {a b : CorrectedFinalTypedEnv F K}
    (hbase : ∀ i, a.baseTrace i = b.baseTrace i)
    (hext : ∀ i : Fin 63, (i : ℕ) < 58 → (i : ℕ) ≠ 41 → (i : ℕ) ≠ 44 →
      a.extTrace i = b.extTrace i)
    (hchal : ∀ i, a.chal i = b.chal i)
    (hextPub : ∀ i, a.extensionPublic i = b.extensionPublic i)
    (hscalarPub : ∀ i, a.scalarPublic i = b.scalarPublic i)
    (t : CorrectedFinalTypedExpr) (ht : CorrectedTerminalCurrentOnly t)
    (h41 : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨
      readsExactRoleCur 41 t = false)
    (h44 : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨
      readsExactRoleCur 44 t = false) :
    t.eval a = t.eval b := by
  revert ht h41 h44
  induction t with
  | baseCur i => intro _ _ _; simp [CorrectedFinalTypedExpr.eval, hbase]
  | baseNext i => intro h; contradiction
  | extCur i =>
      intro ht h41 h44
      by_cases h41r : (i : ℕ) = 41
      · have hi : i = ⟨41, by decide⟩ := Fin.ext h41r
        subst hi
        rcases h41 with hv | hr
        · simpa [CorrectedFinalTypedExpr.eval] using hv
        · simp [readsExactRoleCur] at hr
      · by_cases h44r : (i : ℕ) = 44
        · have hi : i = ⟨44, by decide⟩ := Fin.ext h44r
          subst hi
          rcases h44 with hv | hr
          · simpa [CorrectedFinalTypedExpr.eval] using hv
          · simp [readsExactRoleCur] at hr
        · simpa [CorrectedFinalTypedExpr.eval] using hext i ht h41r h44r
  | extNext i => intro h; contradiction
  | challenge i => intro _ _ _; simp [CorrectedFinalTypedExpr.eval, hchal]
  | extensionPublic i => intro _ _ _; simp [CorrectedFinalTypedExpr.eval, hextPub]
  | scalarPublic i => intro _ _ _; simp [CorrectedFinalTypedExpr.eval, hscalarPub]
  | const c => intro _ _ _; rfl
  | certBase i => intro h; contradiction
  | expCur => intro h; contradiction
  | certExt i => intro h; contradiction
  | lamPow d => intro _ _ _; simp [CorrectedFinalTypedExpr.eval, hchal]
  | add x y ihx ihy =>
      intro ht h41 h44
      have h41x : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨ readsExactRoleCur 41 x
          = false := by
        rcases h41 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.1
      have h41y : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨ readsExactRoleCur 41 y
          = false := by
        rcases h41 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.2
      have h44x : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨ readsExactRoleCur 44 x
          = false := by
        rcases h44 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.1
      have h44y : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨ readsExactRoleCur 44 y
          = false := by
        rcases h44 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.2
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· + ·)
        (ihx ht.1 h41x h44x) (ihy ht.2 h41y h44y)
  | sub x y ihx ihy =>
      intro ht h41 h44
      have h41x : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨ readsExactRoleCur 41 x
          = false := by
        rcases h41 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.1
      have h41y : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨ readsExactRoleCur 41 y
          = false := by
        rcases h41 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.2
      have h44x : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨ readsExactRoleCur 44 x
          = false := by
        rcases h44 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.1
      have h44y : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨ readsExactRoleCur 44 y
          = false := by
        rcases h44 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.2
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· - ·)
        (ihx ht.1 h41x h44x) (ihy ht.2 h41y h44y)
  | mul x y ihx ihy =>
      intro ht h41 h44
      have h41x : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨ readsExactRoleCur 41 x
          = false := by
        rcases h41 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.1
      have h41y : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨ readsExactRoleCur 41 y
          = false := by
        rcases h41 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.2
      have h44x : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨ readsExactRoleCur 44 x
          = false := by
        rcases h44 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.1
      have h44y : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨ readsExactRoleCur 44 y
          = false := by
        rcases h44 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.2
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· * ·)
        (ihx ht.1 h41x h44x) (ihy ht.2 h41y h44y)
  | neg x ih =>
      intro ht h41 h44
      have h41x : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨ readsExactRoleCur 41 x
          = false := by
        rcases h41 with hv | hr
        · exact Or.inl hv
        · exact Or.inr (by simpa [readsExactRoleCur] using hr)
      have h44x : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨ readsExactRoleCur 44 x
          = false := by
        rcases h44 with hv | hr
        · exact Or.inl hv
        · exact Or.inr (by simpa [readsExactRoleCur] using hr)
      simpa [CorrectedFinalTypedExpr.eval] using congrArg Neg.neg (ih ht h41x h44x)
  | pow x n ih =>
      intro ht h41 h44
      have h41x : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨ readsExactRoleCur 41 x
          = false := by
        rcases h41 with hv | hr
        · exact Or.inl hv
        · exact Or.inr (by simpa [readsExactRoleCur] using hr)
      have h44x : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨ readsExactRoleCur 44 x
          = false := by
        rcases h44 with hv | hr
        · exact Or.inl hv
        · exact Or.inr (by simpa [readsExactRoleCur] using hr)
      simpa [CorrectedFinalTypedExpr.eval] using congrArg (fun z => z ^ n) (ih ht h41x h44x)

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
theorem CorrectedFinalTypedExpr.eval_eq_of_terminalCurrentOnlyC_skipLeaf
    {a b : CorrectedFinalTypedEnv F K}
    (hbase : ∀ i, a.baseTrace i = b.baseTrace i)
    (hext : ∀ i : Fin 63, (i : ℕ) < 58 → (i : ℕ) ≠ 41 → (i : ℕ) ≠ 44 →
      a.extTrace i = b.extTrace i)
    (hchal : ∀ i, a.chal i = b.chal i)
    (hextPub : ∀ i, a.extensionPublic i = b.extensionPublic i)
    (hscalarPub : ∀ i, a.scalarPublic i = b.scalarPublic i)
    (t : CorrectedFinalTypedExpr) (ht : CorrectedTerminalCurrentOnlyC t)
    (h41 : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨
      readsExactRoleCur 41 t = false)
    (h44 : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨
      readsExactRoleCur 44 t = false)
    (hcb : ∀ i, a.certBase i = b.certBase i) (hce : ∀ i, a.certExt i = b.certExt i)
    (hexp : a.expCol = b.expCol) :
    t.eval a = t.eval b := by
  revert ht h41 h44
  induction t with
  | baseCur i => intro _ _ _; simp [CorrectedFinalTypedExpr.eval, hbase]
  | baseNext i => intro h; contradiction
  | extCur i =>
      intro ht h41 h44
      by_cases h41r : (i : ℕ) = 41
      · have hi : i = ⟨41, by decide⟩ := Fin.ext h41r
        subst hi
        rcases h41 with hv | hr
        · simpa [CorrectedFinalTypedExpr.eval] using hv
        · simp [readsExactRoleCur] at hr
      · by_cases h44r : (i : ℕ) = 44
        · have hi : i = ⟨44, by decide⟩ := Fin.ext h44r
          subst hi
          rcases h44 with hv | hr
          · simpa [CorrectedFinalTypedExpr.eval] using hv
          · simp [readsExactRoleCur] at hr
        · simpa [CorrectedFinalTypedExpr.eval] using hext i ht h41r h44r
  | extNext i => intro h; contradiction
  | challenge i => intro _ _ _; simp [CorrectedFinalTypedExpr.eval, hchal]
  | extensionPublic i => intro _ _ _; simp [CorrectedFinalTypedExpr.eval, hextPub]
  | scalarPublic i => intro _ _ _; simp [CorrectedFinalTypedExpr.eval, hscalarPub]
  | const c => intro _ _ _; rfl
  | certBase i => intro _ _ _; simp [CorrectedFinalTypedExpr.eval, hcb]
  | expCur => intro _ _ _; simp [CorrectedFinalTypedExpr.eval, hexp]
  | certExt i => intro _ _ _; simp [CorrectedFinalTypedExpr.eval, hce]
  | lamPow d => intro _ _ _; simp [CorrectedFinalTypedExpr.eval, hchal]
  | add x y ihx ihy =>
      intro ht h41 h44
      have h41x : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨ readsExactRoleCur 41 x = false := by
        rcases h41 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.1
      have h41y : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨ readsExactRoleCur 41 y = false := by
        rcases h41 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.2
      have h44x : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨ readsExactRoleCur 44 x = false := by
        rcases h44 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.1
      have h44y : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨ readsExactRoleCur 44 y = false := by
        rcases h44 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.2
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· + ·)
        (ihx ht.1 h41x h44x) (ihy ht.2 h41y h44y)
  | sub x y ihx ihy =>
      intro ht h41 h44
      have h41x : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨ readsExactRoleCur 41 x = false := by
        rcases h41 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.1
      have h41y : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨ readsExactRoleCur 41 y = false := by
        rcases h41 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.2
      have h44x : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨ readsExactRoleCur 44 x = false := by
        rcases h44 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.1
      have h44y : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨ readsExactRoleCur 44 y = false := by
        rcases h44 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.2
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· - ·)
        (ihx ht.1 h41x h44x) (ihy ht.2 h41y h44y)
  | mul x y ihx ihy =>
      intro ht h41 h44
      have h41x : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨ readsExactRoleCur 41 x = false := by
        rcases h41 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.1
      have h41y : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨ readsExactRoleCur 41 y = false := by
        rcases h41 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.2
      have h44x : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨ readsExactRoleCur 44 x = false := by
        rcases h44 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.1
      have h44y : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨ readsExactRoleCur 44 y = false := by
        rcases h44 with hv | hr
        · exact Or.inl hv
        · right; simp [readsExactRoleCur, Bool.or_eq_false_iff] at hr; exact hr.2
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· * ·)
        (ihx ht.1 h41x h44x) (ihy ht.2 h41y h44y)
  | neg x ih =>
      intro ht h41 h44
      have h41x : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨ readsExactRoleCur 41 x = false := by
        rcases h41 with hv | hr
        · exact Or.inl hv
        · exact Or.inr (by simpa [readsExactRoleCur] using hr)
      have h44x : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨ readsExactRoleCur 44 x = false := by
        rcases h44 with hv | hr
        · exact Or.inl hv
        · exact Or.inr (by simpa [readsExactRoleCur] using hr)
      simpa [CorrectedFinalTypedExpr.eval] using congrArg Neg.neg (ih ht h41x h44x)
  | pow x n ih =>
      intro ht h41 h44
      have h41x : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨ readsExactRoleCur 41 x = false := by
        rcases h41 with hv | hr
        · exact Or.inl hv
        · exact Or.inr (by simpa [readsExactRoleCur] using hr)
      have h44x : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨ readsExactRoleCur 44 x = false := by
        rcases h44 with hv | hr
        · exact Or.inl hv
        · exact Or.inr (by simpa [readsExactRoleCur] using hr)
      simpa [CorrectedFinalTypedExpr.eval] using congrArg (fun z => z ^ n) (ih ht h41x h44x)

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
theorem correctedFinalExtGate_publicFree :
    ∀ i : CorrectedCoreExtGateId, CorrectedPublicFree (correctedFinalExtGate i) := by
  intro i
  rw [← correctedPublicFreeB_iff]
  have hall : ∀ t ∈ correctedLoweredExt, correctedPublicFreeB t = true := by decide
  have hi : (i : ℕ) < correctedLoweredExt.length := by
    rw [corrected_lowered_counts.1]; exact i.isLt
  simpa [correctedFinalExtGate] using
    hall _ (List.get_mem correctedLoweredExt ⟨i.val, hi⟩)

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
theorem correctedFinalExtGate_residualFree :
    ∀ i : CorrectedCoreExtGateId, CorrectedResidualFreeC (correctedFinalExtGate i) := by
  intro i
  rw [← correctedResidualFreeCB_iff]
  have hall : ∀ t ∈ correctedLoweredExt, correctedResidualFreeCB t = true := by decide
  have hi : (i : ℕ) < correctedLoweredExt.length := by
    rw [corrected_lowered_counts.1]; exact i.isLt
  simpa [correctedFinalExtGate] using
    hall _ (List.get_mem correctedLoweredExt ⟨i.val, hi⟩)

theorem splitLeafOr {p : Prop} {hx hy : Bool}
    (h : p ∨ (hx || hy) = false) :
    (p ∨ hx = false) ∧ (p ∨ hy = false) := by
  rcases h with hv | hr
  · exact ⟨Or.inl hv, Or.inl hv⟩
  · simp [Bool.or_eq_false_iff] at hr
    exact ⟨Or.inr hr.1, Or.inr hr.2⟩

theorem CorrectedFinalTypedExpr.eval_eq_of_residualFree_skipLeaf
    {a b : CorrectedFinalTypedEnv F K}
    (hbase : ∀ i, a.baseTrace i = b.baseTrace i)
    (hbaseNext : ∀ i, a.baseTraceNext i = b.baseTraceNext i)
    (hext : ∀ i : Fin 63, (i : ℕ) < 58 ∨ (i : ℕ) = 61 ∨ (i : ℕ) = 62 →
      (i : ℕ) ≠ 41 → (i : ℕ) ≠ 44 → a.extTrace i = b.extTrace i)
    (hextNext : ∀ i : Fin 63, (i : ℕ) < 58 ∨ (i : ℕ) = 61 ∨ (i : ℕ) = 62 →
      (i : ℕ) ≠ 41 → (i : ℕ) ≠ 44 → a.extTraceNext i = b.extTraceNext i)
    (hchal : ∀ i, a.chal i = b.chal i)
    (hextPub : ∀ i, a.extensionPublic i = b.extensionPublic i)
    (hscalarPub : ∀ i, a.scalarPublic i = b.scalarPublic i)
    (t : CorrectedFinalTypedExpr) (ht : CorrectedResidualFreeC t)
    (h41 : a.extTrace ⟨41, by decide⟩ = b.extTrace ⟨41, by decide⟩ ∨
      readsExactRoleCur 41 t = false)
    (h44 : a.extTrace ⟨44, by decide⟩ = b.extTrace ⟨44, by decide⟩ ∨
      readsExactRoleCur 44 t = false)
    (h41n : a.extTraceNext ⟨41, by decide⟩ = b.extTraceNext ⟨41, by decide⟩ ∨
      readsExactRoleNext 41 t = false)
    (h44n : a.extTraceNext ⟨44, by decide⟩ = b.extTraceNext ⟨44, by decide⟩ ∨
      readsExactRoleNext 44 t = false)
    (hcb : ∀ i, a.certBase i = b.certBase i) (hce : ∀ i, a.certExt i = b.certExt i)
    (hexp : a.expCol = b.expCol) :
    t.eval a = t.eval b := by
  revert ht h41 h44 h41n h44n
  induction t with
  | baseCur i => intro _ _ _ _ _; simp [CorrectedFinalTypedExpr.eval, hbase]
  | baseNext i => intro _ _ _ _ _; simp [CorrectedFinalTypedExpr.eval, hbaseNext]
  | extCur i =>
      intro ht h41 h44 _ _
      by_cases h41r : (i : ℕ) = 41
      · have hi : i = ⟨41, by decide⟩ := Fin.ext h41r
        subst hi
        rcases h41 with hv | hr
        · simpa [CorrectedFinalTypedExpr.eval] using hv
        · simp [readsExactRoleCur] at hr
      · by_cases h44r : (i : ℕ) = 44
        · have hi : i = ⟨44, by decide⟩ := Fin.ext h44r
          subst hi
          rcases h44 with hv | hr
          · simpa [CorrectedFinalTypedExpr.eval] using hv
          · simp [readsExactRoleCur] at hr
        · simpa [CorrectedFinalTypedExpr.eval] using hext i ht h41r h44r
  | extNext i =>
      intro ht _ _ h41n h44n
      by_cases h41r : (i : ℕ) = 41
      · have hi : i = ⟨41, by decide⟩ := Fin.ext h41r
        subst hi
        rcases h41n with hv | hr
        · simpa [CorrectedFinalTypedExpr.eval] using hv
        · simp [readsExactRoleNext] at hr
      · by_cases h44r : (i : ℕ) = 44
        · have hi : i = ⟨44, by decide⟩ := Fin.ext h44r
          subst hi
          rcases h44n with hv | hr
          · simpa [CorrectedFinalTypedExpr.eval] using hv
          · simp [readsExactRoleNext] at hr
        · simpa [CorrectedFinalTypedExpr.eval] using hextNext i ht h41r h44r
  | challenge i => intro _ _ _ _ _; simp [CorrectedFinalTypedExpr.eval, hchal]
  | extensionPublic i => intro _ _ _ _ _; simp [CorrectedFinalTypedExpr.eval, hextPub]
  | scalarPublic i => intro _ _ _ _ _; simp [CorrectedFinalTypedExpr.eval, hscalarPub]
  | const c => intro _ _ _ _ _; rfl
  | certBase i => intro _ _ _ _ _; simp [CorrectedFinalTypedExpr.eval, hcb]
  | expCur => intro _ _ _ _ _; simp [CorrectedFinalTypedExpr.eval, hexp]
  | certExt i => intro _ _ _ _ _; simp [CorrectedFinalTypedExpr.eval, hce]
  | lamPow d => intro _ _ _ _ _; simp [CorrectedFinalTypedExpr.eval, hchal]
  | add x y ihx ihy =>
      intro ht h41 h44 h41n h44n
      have h41s := splitLeafOr (by simpa [readsExactRoleCur] using h41)
      have h44s := splitLeafOr (by simpa [readsExactRoleCur] using h44)
      have h41ns := splitLeafOr (by simpa [readsExactRoleNext] using h41n)
      have h44ns := splitLeafOr (by simpa [readsExactRoleNext] using h44n)
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· + ·)
        (ihx ht.1 h41s.1 h44s.1 h41ns.1 h44ns.1)
        (ihy ht.2 h41s.2 h44s.2 h41ns.2 h44ns.2)
  | sub x y ihx ihy =>
      intro ht h41 h44 h41n h44n
      have h41s := splitLeafOr (by simpa [readsExactRoleCur] using h41)
      have h44s := splitLeafOr (by simpa [readsExactRoleCur] using h44)
      have h41ns := splitLeafOr (by simpa [readsExactRoleNext] using h41n)
      have h44ns := splitLeafOr (by simpa [readsExactRoleNext] using h44n)
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· - ·)
        (ihx ht.1 h41s.1 h44s.1 h41ns.1 h44ns.1)
        (ihy ht.2 h41s.2 h44s.2 h41ns.2 h44ns.2)
  | mul x y ihx ihy =>
      intro ht h41 h44 h41n h44n
      have h41s := splitLeafOr (by simpa [readsExactRoleCur] using h41)
      have h44s := splitLeafOr (by simpa [readsExactRoleCur] using h44)
      have h41ns := splitLeafOr (by simpa [readsExactRoleNext] using h41n)
      have h44ns := splitLeafOr (by simpa [readsExactRoleNext] using h44n)
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· * ·)
        (ihx ht.1 h41s.1 h44s.1 h41ns.1 h44ns.1)
        (ihy ht.2 h41s.2 h44s.2 h41ns.2 h44ns.2)
  | neg x ih =>
      intro ht h41 h44 h41n h44n
      simpa [CorrectedFinalTypedExpr.eval] using congrArg Neg.neg
        (ih ht (by simpa [readsExactRoleCur] using h41) (by simpa [readsExactRoleCur] using h44)
          (by simpa [readsExactRoleNext] using h41n) (by simpa [readsExactRoleNext] using h44n))
  | pow x n ih =>
      intro ht h41 h44 h41n h44n
      simpa [CorrectedFinalTypedExpr.eval] using congrArg (fun z => z ^ n)
        (ih ht (by simpa [readsExactRoleCur] using h41) (by simpa [readsExactRoleCur] using h44)
          (by simpa [readsExactRoleNext] using h41n) (by simpa [readsExactRoleNext] using h44n))

theorem CorrectedFinalTypedExpr.eval_eq_of_publicFree
    {a b : CorrectedFinalTypedEnv F K}
    (hbase : ∀ i, a.baseTrace i = b.baseTrace i)
    (hbaseNext : ∀ i, a.baseTraceNext i = b.baseTraceNext i)
    (hext : ∀ i, a.extTrace i = b.extTrace i)
    (hextNext : ∀ i, a.extTraceNext i = b.extTraceNext i)
    (hchal : ∀ i, a.chal i = b.chal i)
    (t : CorrectedFinalTypedExpr) (ht : CorrectedPublicFree t)
    (hcb : ∀ i, a.certBase i = b.certBase i) (hce : ∀ i, a.certExt i = b.certExt i)
    (hexp : a.expCol = b.expCol) :
    t.eval a = t.eval b := by
  revert ht
  induction t with
  | baseCur i => intro; simp [CorrectedFinalTypedExpr.eval, hbase]
  | baseNext i => intro; simp [CorrectedFinalTypedExpr.eval, hbaseNext]
  | extCur i => intro; simp [CorrectedFinalTypedExpr.eval, hext]
  | extNext i => intro; simp [CorrectedFinalTypedExpr.eval, hextNext]
  | challenge i => intro; simp [CorrectedFinalTypedExpr.eval, hchal]
  | extensionPublic i => intro h; contradiction
  | scalarPublic i => intro h; contradiction
  | const c => intro; rfl
  | certBase i => intro; simp [CorrectedFinalTypedExpr.eval, hcb]
  | expCur => intro; simp [CorrectedFinalTypedExpr.eval, hexp]
  | certExt i => intro; simp [CorrectedFinalTypedExpr.eval, hce]
  | lamPow d => intro; simp [CorrectedFinalTypedExpr.eval, hchal]
  | add x y ihx ihy =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· + ·)
        (ihx ht.1) (ihy ht.2)
  | sub x y ihx ihy =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· - ·)
        (ihx ht.1) (ihy ht.2)
  | mul x y ihx ihy =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· * ·)
        (ihx ht.1) (ihy ht.2)
  | neg x ih =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg Neg.neg (ih ht)
  | pow x n ih =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg (fun z => z ^ n) (ih ht)

/-! ### The anchored accumulator on the canonical trace

Witness role `60` is `acc_after(i)`; `aux[2]` is the unmasked step `correctedAccAfterStep` and
`core[20]` the chain `accAfterChain` (`OptimizedComputeCorrectedFinal`).  Both hold on every
canonical row from the co-resident accumulator's row-local identity
`ComputeSampledIO.coResidentAcc_succ`. -/

/-- Footprint of the anchored step: current-row base, current-row extension roles below `58`
or `60`, and the semantic challenges `0..8`; no next row and no public. -/
def StepFootprint : CorrectedFinalTypedExpr → Prop
  | .baseCur _ | .const _ => True
  | .extCur i => (i : ℕ) < 58 ∨ (i : ℕ) = 60
  | .challenge q => (q : ℕ) < 9
  | .baseNext _ | .extNext _ | .extensionPublic _ | .scalarPublic _ => False
  | .certBase _ | .certExt _ | .expCur | .lamPow _ => False
  | .add x y | .sub x y | .mul x y => StepFootprint x ∧ StepFootprint y
  | .neg x | .pow x _ => StepFootprint x

def stepFootprintB : CorrectedFinalTypedExpr → Bool
  | .baseCur _ | .const _ => true
  | .extCur i => decide ((i : ℕ) < 58 ∨ (i : ℕ) = 60)
  | .challenge q => decide ((q : ℕ) < 9)
  | .baseNext _ | .extNext _ | .extensionPublic _ | .scalarPublic _ => false
  | .certBase _ | .certExt _ | .expCur | .lamPow _ => false
  | .add x y | .sub x y | .mul x y => stepFootprintB x && stepFootprintB y
  | .neg x | .pow x _ => stepFootprintB x

theorem stepFootprintB_iff (t : CorrectedFinalTypedExpr) :
    stepFootprintB t ↔ StepFootprint t := by
  induction t <;> simp [stepFootprintB, StepFootprint, *]

theorem correctedAccAfterStep_footprint : StepFootprint correctedAccAfterStep := by
  rw [← stepFootprintB_iff]
  set_option maxRecDepth 300000 in decide

theorem CorrectedFinalTypedExpr.eval_eq_of_stepFootprint
    {a b : CorrectedFinalTypedEnv F K}
    (hbase : ∀ i, a.baseTrace i = b.baseTrace i)
    (hext : ∀ i : Fin 63, (i : ℕ) < 58 ∨ (i : ℕ) = 60 → a.extTrace i = b.extTrace i)
    (hchal : ∀ q : Fin 12, (q : ℕ) < 9 → a.chal q = b.chal q)
    (t : CorrectedFinalTypedExpr) (ht : StepFootprint t) :
    t.eval a = t.eval b := by
  revert ht
  induction t with
  | baseCur i => intro; simp [CorrectedFinalTypedExpr.eval, hbase]
  | baseNext i => intro h; contradiction
  | extCur i => intro ht; simpa [CorrectedFinalTypedExpr.eval] using hext i ht
  | extNext i => intro h; contradiction
  | challenge q => intro hq; simpa [CorrectedFinalTypedExpr.eval] using hchal q hq
  | extensionPublic i => intro h; contradiction
  | scalarPublic i => intro h; contradiction
  | const c => intro; rfl
  | certBase i => intro h; contradiction
  | expCur => intro h; contradiction
  | certExt i => intro h; contradiction
  | lamPow d => intro h; contradiction
  | add x y ihx ihy =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· + ·) (ihx ht.1) (ihy ht.2)
  | sub x y ihx ihy =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· - ·) (ihx ht.1) (ihy ht.2)
  | mul x y ihx ihy =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· * ·) (ihx ht.1) (ihy ht.2)
  | neg x ih =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg Neg.neg (ih ht)
  | pow x n ih =>
      intro ht
      simpa [CorrectedFinalTypedExpr.eval] using congrArg (fun z => z ^ n) (ih ht)

theorem CorrectedFinalTypedExpr.eval_eq_of_stepFootprint_skipLeaf
    {a b : CorrectedFinalTypedEnv F K}
    (hbase : ∀ i, a.baseTrace i = b.baseTrace i)
    (hext : ∀ i : Fin 63, (i : ℕ) < 58 ∨ (i : ℕ) = 60 →
      (i : ℕ) ≠ 41 → (i : ℕ) ≠ 44 → a.extTrace i = b.extTrace i)
    (hchal : ∀ q : Fin 12, (q : ℕ) < 9 → a.chal q = b.chal q)
    (t : CorrectedFinalTypedExpr) (ht : StepFootprint t) (havoid : readsLeafRole t = false) :
    t.eval a = t.eval b := by
  revert ht havoid
  induction t with
  | baseCur i => intro _ _; simp [CorrectedFinalTypedExpr.eval, hbase]
  | baseNext i => intro h; contradiction
  | extCur i =>
      intro ht havoid
      have hne := not_leaf_role_of_reads (i : ℕ) (by simpa [readsLeafRole] using havoid)
      simpa [CorrectedFinalTypedExpr.eval] using hext i ht hne.1 hne.2
  | extNext i => intro h; contradiction
  | challenge q => intro hq _; simpa [CorrectedFinalTypedExpr.eval] using hchal q hq
  | extensionPublic i => intro h; contradiction
  | scalarPublic i => intro h; contradiction
  | const c => intro _ _; rfl
  | certBase i => intro h; contradiction
  | expCur => intro h; contradiction
  | certExt i => intro h; contradiction
  | lamPow d => intro h; contradiction
  | add x y ihx ihy =>
      intro ht havoid
      simp only [readsLeafRole, Bool.or_eq_false_iff] at havoid
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· + ·)
        (ihx ht.1 havoid.1) (ihy ht.2 havoid.2)
  | sub x y ihx ihy =>
      intro ht havoid
      simp only [readsLeafRole, Bool.or_eq_false_iff] at havoid
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· - ·)
        (ihx ht.1 havoid.1) (ihy ht.2 havoid.2)
  | mul x y ihx ihy =>
      intro ht havoid
      simp only [readsLeafRole, Bool.or_eq_false_iff] at havoid
      simpa [CorrectedFinalTypedExpr.eval] using congrArg₂ (· * ·)
        (ihx ht.1 havoid.1) (ihy ht.2 havoid.2)
  | neg x ih =>
      intro ht havoid
      simpa [CorrectedFinalTypedExpr.eval, readsLeafRole] using congrArg Neg.neg (ih ht havoid)
  | pow x n ih =>
      intro ht havoid
      simpa [CorrectedFinalTypedExpr.eval, readsLeafRole] using
        congrArg (fun z => z ^ n) (ih ht havoid)

theorem correctedAccAfterStep_avoids_leaf : readsLeafRole correctedAccAfterStep = false := by
  set_option maxRecDepth 300000 in decide

/-- **Honest step.**  On every canonical row — the last included — the unmasked anchored step
vanishes. -/
theorem canonical_accAfterStep
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hchal9 : ∀ q : Fin 12, (q : ℕ) < 9 → ∀ k : Fin 3,
      chalVal (3 * (q : ℕ) + (k : ℕ)) = coord b (exactFinalChallenge A q) k)
    (i : Fin R.problem.cfg.compRows) :
    let envF := envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal
    let env := gatherCorrectedFinalTypedEnv b envF
    correctedAccAfterStep.eval env = 0 := by
  dsimp only
  let can := gatherCorrectedFinalTypedEnv b
    (envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal)
  let ex := exactFinalCurrentEnv A i
  have hsame : correctedAccAfterStep.eval can = correctedAccAfterStep.eval ex := by
    apply CorrectedFinalTypedExpr.eval_eq_of_stepFootprint_skipLeaf
    · intro q
      simpa [can, ex, exactFinalCurrentEnv] using
        canonical_gather_base_current A hn nodes hnodes b chalVal pubVal orbit i q
    · intro role hrole h41 h44
      rcases hrole with hlt | h60
      · let r : Fin 58 := ⟨role, hlt⟩
        have hc := canonical_gather_ext_core A hn nodes hnodes b chalVal pubVal orbit i r
        have he : ex.extTrace role = coreExtensionValue (encodedRowAt A i) r := by
          simp [ex, exactFinalCurrentEnv, exactFinalExtensionRow, hlt, r]
        have hc' : can.extTrace role = formRLeafCore b (encodedRowAt A i) r := by
          simpa [can, r] using hc
        exact hc'.trans ((formRLeafCore_eq_core b _ r ⟨h41, h44⟩).trans he.symm)
      · have hr : role = (60 : Fin 63) := Fin.ext h60
        subst role
        have hc := canonical_gather_accAfter A hn nodes hnodes b chalVal pubVal orbit i
        have he : ex.extTrace 60 =
            ComputeSampledIO.coResidentAccC A.compress10 R.problem.cfg.challenges.lam R.problem.exec.computeRows
              ((i : ℕ) + 1) := by
          simp [ex, exactFinalCurrentEnv, exactFinalExtensionRow]
        have hc' : can.extTrace 60 =
            ComputeSampledIO.coResidentAccC A.compress10 R.problem.cfg.challenges.lam R.problem.exec.computeRows
              ((i : ℕ) + 1) := hc
        exact hc'.trans he.symm
    · intro q hq
      have hq' := canonical_gather_challenge_of_coordinates A hn nodes b chalVal pubVal orbit q
        (exactFinalChallenge A q) (hchal9 q hq) i
      simpa [can, ex, exactFinalCurrentEnv] using hq'
    · exact correctedAccAfterStep_footprint
    · exact correctedAccAfterStep_avoids_leaf
  rw [hsame, ← correctedLowerFinal_eval ex _ _ correctedLowerFinal_accAfterStep]
  exact exact_accAfterStep_current A i

/-- **Honest chain.**  Off the last row `acc_after(i)` is the next row's accumulator; at the
last row the `(1 - last)` mask vanishes. -/
theorem canonical_accAfterChain
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hstep : ∀ (i : Fin R.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < R.problem.cfg.compRows),
      nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (i : Fin R.problem.cfg.compRows) :
    let envF := envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal
    let env := gatherCorrectedFinalTypedEnv b envF
    accAfterChain.eval env = 0 := by
  dsimp only
  have hb12 := canonical_gather_base_current A hn nodes hnodes b chalVal pubVal orbit i (12 : Fin 13)
  simp only [accAfterChain, CorrectedFinalTypedExpr.eval]
  by_cases hi : (i : ℕ) + 1 < R.problem.cfg.compRows
  · have h60 := canonical_gather_accAfter A hn nodes hnodes b chalVal pubVal orbit i
    have h32 := canonical_gather_ext_core_next A hn nodes hnodes b chalVal pubVal orbit i hi
      (by simpa [mul_comm] using hstep i hi) (32 : Fin 58)
    rw [formRLeafCore_eq_core b _ (32 : Fin 58) ⟨by decide, by decide⟩] at h32
    rw [coreExtensionValue_sampledAcc] at h32
    have h32' : (gatherCorrectedFinalTypedEnv b
        (envOfTrace (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal)).extTraceNext 32 =
        ComputeSampledIO.coResidentAccC A.compress10 R.problem.cfg.challenges.lam R.problem.exec.computeRows
          ((i : ℕ) + 1) := h32
    rw [h60, h32', sub_self, mul_zero]
  · have hilast : i = ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩ := by
      apply Fin.ext; simp only; omega
    have hb1 : (gatherCorrectedFinalTypedEnv b
        (envOfTrace (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal)).baseTrace 12 = 1 := by
      simpa [finalBaseCell, hilast] using hb12
    rw [hb1]
    simp

set_option maxRecDepth 300000 in
theorem canonical_ext_gate_nonterminal_zero
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hstep : ∀ (i : Fin R.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < R.problem.cfg.compRows),
      nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hchal : ExactFinalChallengeCoordinates b A chalVal)
    (hax : FormRAxisBound A b) (hwidth : FormRWidth F)
    (hord : 2 ≤ R.problem.cfg.compRows →
      R.problem.cfg.compRows ≤ orderOf R.computeWalkAlpha)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (gate : CorrectedCoreExtGateId) :
    let envF := envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal
    (correctedFinalExtGate gate).eval (gatherCorrectedFinalTypedEnv b envF) = 0 := by
  dsimp only
  let can := gatherCorrectedFinalTypedEnv b
    (envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal)
  let ex := exactFinalTransitionEnv A i hi
  let exPub : CorrectedFinalTypedEnv F K :=
    { ex with
      extensionPublic := can.extensionPublic
      scalarPublic := can.scalarPublic }
  have hex : (correctedFinalExtGate gate).eval ex = 0 := by
    rw [← correctedFinalExtGate_eval_source]
    by_cases hq0 : gate = packedQueueNonEmptyId
    · subst gate
      rw [packedQueueNonEmpty_source]
      exact exact_queueNonEmpty_transition A hA hord i hi
    · by_cases hq1 : gate = packedQueueTilingId
      · subst gate
        rw [packedQueueTiling_source]
        exact exact_queueTiling_transition A i hi
      · exact exact_finalExtTransitionGates A hA i hi
          (OptimizedComputeFormRDenoms.formRAxisSmall_of_bound A b hax) hwidth _
          (mem_core_sampled_of_not_queue gate ⟨by
            intro h; exact hq0 (Fin.eq_of_val_eq h), by
            intro h; exact hq1 (Fin.eq_of_val_eq h)⟩)
  have hpub : (correctedFinalExtGate gate).eval exPub =
      (correctedFinalExtGate gate).eval ex := by
    apply CorrectedFinalTypedExpr.eval_eq_of_publicFree (hexp := by rfl)
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · exact correctedFinalExtGate_publicFree gate
    · intro q; rfl
    · intro q; rfl
  have hsame : (correctedFinalExtGate gate).eval can =
      (correctedFinalExtGate gate).eval exPub := by
    apply CorrectedFinalTypedExpr.eval_eq_of_residualFree_skipLeaf
      (hexp := by first
      | exact canonical_gather_expCol A hn nodes hnodes b chalVal pubVal orbit i
      | exact canonical_gather_expCol A hn nodes hnodes b chalVal pubVal orbit last)
    · intro q
      simpa [can, exPub, ex, exactFinalTransitionEnv] using
        canonical_gather_base_current A hn nodes hnodes b chalVal pubVal orbit i q
    · intro q
      simpa [can, exPub, ex, exactFinalTransitionEnv] using
        canonical_gather_base_next A hn nodes hnodes b chalVal pubVal orbit i hi
          (by simpa [mul_comm] using hstep i hi) q
    · intro role hrole h41 h44
      rcases hrole with hlt | h61 | h62
      · let r : Fin 58 := ⟨role, hlt⟩
        have hc := canonical_gather_ext_core
          A hn nodes hnodes b chalVal pubVal orbit i r
        have he : exPub.extTrace role = coreExtensionValue (encodedRowAt A i) r := by
          simp [exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow, hlt, r]
        have hc' : can.extTrace role = formRLeafCore b (encodedRowAt A i) r := by
          simpa [can, r] using hc
        exact hc'.trans ((formRLeafCore_eq_core b _ r ⟨h41, h44⟩).trans he.symm)
      · have hr : role = (61 : Fin 63) := Fin.ext h61
        subst role
        simpa [can, exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow] using
          canonical_gather_walkLine A hn nodes hnodes b chalVal pubVal orbit i
      · have hr : role = (62 : Fin 63) := Fin.ext h62
        subst role
        simpa [can, exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow] using
          canonical_gather_walkInv A hn nodes hnodes b chalVal pubVal orbit i
    · intro role hrole h41 h44
      rcases hrole with hlt | h61 | h62
      · let r : Fin 58 := ⟨role, hlt⟩
        have hc := canonical_gather_ext_core_next
          A hn nodes hnodes b chalVal pubVal orbit i hi
            (by simpa [mul_comm] using hstep i hi) r
        have he : exPub.extTraceNext role =
            coreExtensionValue (encodedRowAt A ⟨(i : ℕ) + 1, hi⟩) r := by
          simp [exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow, hlt, r]
        have hc' : can.extTraceNext role =
            formRLeafCore b (encodedRowAt A ⟨(i : ℕ) + 1, hi⟩) r := by
          simpa [can, r] using hc
        exact hc'.trans ((formRLeafCore_eq_core b _ r ⟨h41, h44⟩).trans he.symm)
      · have hr : role = (61 : Fin 63) := Fin.ext h61
        subst role
        simpa [can, exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow,
          Nat.add_assoc] using canonical_gather_walkLine_next
            A hn nodes hnodes b chalVal pubVal orbit i hi
              (by simpa [mul_comm] using hstep i hi)
      · have hr : role = (62 : Fin 63) := Fin.ext h62
        subst role
        simpa [can, exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow,
          Nat.add_assoc] using canonical_gather_walkInv_next
            A hn nodes hnodes b chalVal pubVal orbit i hi
              (by simpa [mul_comm] using hstep i hi)
    · intro q
      simpa [can, exPub, ex, exactFinalTransitionEnv] using
        canonical_gather_challenge A hn nodes b chalVal pubVal orbit hchal i q
    · intro q; rfl
    · intro q; rfl
    · exact correctedFinalExtGate_residualFree gate
    · left
      have hc := canonical_gather_ext_core
        A hn nodes hnodes b chalVal pubVal orbit i ⟨41, by decide⟩
      have he : exPub.extTrace ⟨41, by decide⟩ =
          coreExtensionValue (encodedRowAt A i) ⟨41, by decide⟩ := by
        simp [exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow]
      have hc' := by simpa [can] using hc
      exact hc'.trans
        ((formRLeafCore_eq_core_all b _ _).trans he.symm)
    · left
      have hc := canonical_gather_ext_core
        A hn nodes hnodes b chalVal pubVal orbit i ⟨44, by decide⟩
      have he : exPub.extTrace ⟨44, by decide⟩ =
          coreExtensionValue (encodedRowAt A i) ⟨44, by decide⟩ := by
        simp [exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow]
      have hc' := by simpa [can] using hc
      exact hc'.trans
        ((formRLeafCore_eq_core_all b _ _).trans he.symm)
    · left
      have hc := canonical_gather_ext_core_next
        A hn nodes hnodes b chalVal pubVal orbit i hi
          (by simpa [mul_comm] using hstep i hi) ⟨41, by decide⟩
      have he : exPub.extTraceNext ⟨41, by decide⟩ =
          coreExtensionValue (encodedRowAt A ⟨(i : ℕ) + 1, hi⟩) ⟨41, by decide⟩ := by
        simp [exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow]
      have hc' := by simpa [can] using hc
      exact hc'.trans
        ((formRLeafCore_eq_core_all b _ _).trans he.symm)
    · left
      have hc := canonical_gather_ext_core_next
        A hn nodes hnodes b chalVal pubVal orbit i hi
          (by simpa [mul_comm] using hstep i hi) ⟨44, by decide⟩
      have he : exPub.extTraceNext ⟨44, by decide⟩ =
          coreExtensionValue (encodedRowAt A ⟨(i : ℕ) + 1, hi⟩) ⟨44, by decide⟩ := by
        simp [exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow]
      have hc' := by simpa [can] using hc
      exact hc'.trans
        ((formRLeafCore_eq_core_all b _ _).trans he.symm)
    · intro q; exact canonical_gather_certBase A hn nodes hnodes b chalVal pubVal orbit hax i q
    · intro q; exact canonical_gather_certExt A hn nodes hnodes b chalVal pubVal orbit hax (fun k
        => hchal 9 k) i q
  rw [hsame, hpub, hex]

set_option maxRecDepth 300000 in
theorem canonical_ext_gate_nonterminal_zero_with
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (c : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hstep : ∀ (i : Fin R.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < R.problem.cfg.compRows),
      nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hchal : ExactFinalChallengeCoordinatesWith b A c chalVal)
    (hax : FormRAxisBound A b) (hwidth : FormRWidth F)
    (hord : 2 ≤ R.problem.cfg.compRows →
      R.problem.cfg.compRows ≤ orderOf R.computeWalkAlpha)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (gate : CorrectedCoreExtGateId) :
    let envF := envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal
    (correctedFinalExtGate gate).eval (gatherCorrectedFinalTypedEnv b envF) = 0 := by
  dsimp only
  let can := gatherCorrectedFinalTypedEnv b
    (envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal)
  let ex := exactFinalTransitionEnvWith A c i hi
  let exPub : CorrectedFinalTypedEnv F K :=
    { ex with extensionPublic := can.extensionPublic, scalarPublic := can.scalarPublic }
  have hex : (correctedFinalExtGate gate).eval ex = 0 := by
    rw [← correctedFinalExtGate_eval_source]
    by_cases hq0 : gate = packedQueueNonEmptyId
    · subst gate
      rw [packedQueueNonEmpty_source]
      change OptimizedComputeGateBasis.walkQueueNonEmpty.eval
          (withFinalComputeChallenges A (exactFinalTransitionEnv A i hi) c).toSourceEnv = 0
      rw [eval_withFinalComputeChallenges_of_free A (exactFinalTransitionEnv A i hi) c
          OptimizedComputeGateBasis.walkQueueNonEmpty
          (queueWitnessGates_compilerInputFree _
            (by simp [OptimizedComputeGateBasis.queueWitnessGates]))]
      exact exact_queueNonEmpty_transition A hA hord i hi
    · by_cases hq1 : gate = packedQueueTilingId
      · subst gate
        rw [packedQueueTiling_source]
        change OptimizedComputeGateBasis.walkQueueTiling.eval
            (withFinalComputeChallenges A (exactFinalTransitionEnv A i hi) c).toSourceEnv = 0
        rw [eval_withFinalComputeChallenges_of_free A (exactFinalTransitionEnv A i hi) c
            OptimizedComputeGateBasis.walkQueueTiling
            (queueWitnessGates_compilerInputFree _
              (by simp [OptimizedComputeGateBasis.queueWitnessGates]))]
        exact exact_queueTiling_transition A i hi
      · exact exact_finalExtTransitionGatesWith A hA c i hi
          (OptimizedComputeFormRDenoms.formRAxisSmall_of_bound A b hax) hwidth _
          (mem_core_sampled_of_not_queue gate ⟨by
            intro h; exact hq0 (Fin.eq_of_val_eq h), by
            intro h; exact hq1 (Fin.eq_of_val_eq h)⟩)
  have hpub : (correctedFinalExtGate gate).eval exPub =
      (correctedFinalExtGate gate).eval ex := by
    apply CorrectedFinalTypedExpr.eval_eq_of_publicFree (hexp := by rfl)
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · exact correctedFinalExtGate_publicFree gate
    · intro q; rfl
    · intro q; rfl
  have hsame : (correctedFinalExtGate gate).eval can =
      (correctedFinalExtGate gate).eval exPub := by
    apply CorrectedFinalTypedExpr.eval_eq_of_residualFree_skipLeaf
      (hexp := by first
      | exact canonical_gather_expCol A hn nodes hnodes b chalVal pubVal orbit i
      | exact canonical_gather_expCol A hn nodes hnodes b chalVal pubVal orbit last)
    · intro q
      simpa [can, exPub, ex, exactFinalTransitionEnvWith, withFinalComputeChallenges,
        exactFinalTransitionEnv] using
        canonical_gather_base_current A hn nodes hnodes b chalVal pubVal orbit i q
    · intro q
      simpa [can, exPub, ex, exactFinalTransitionEnvWith, withFinalComputeChallenges,
        exactFinalTransitionEnv] using
        canonical_gather_base_next A hn nodes hnodes b chalVal pubVal orbit i hi
          (by simpa [mul_comm] using hstep i hi) q
    · intro role hrole h41 h44
      rcases hrole with hlt | h61 | h62
      · let r : Fin 58 := ⟨role, hlt⟩
        have hc := canonical_gather_ext_core
          A hn nodes hnodes b chalVal pubVal orbit i r
        have he : exPub.extTrace role = coreExtensionValue (encodedRowAt A i) r := by
          simp [exPub, ex, exactFinalTransitionEnvWith, withFinalComputeChallenges,
            exactFinalTransitionEnv, exactFinalExtensionRow, hlt, r]
        have hc' : can.extTrace role = formRLeafCore b (encodedRowAt A i) r := by
          simpa [can, r] using hc
        exact hc'.trans ((formRLeafCore_eq_core b _ r ⟨h41, h44⟩).trans he.symm)
      · have hr : role = (61 : Fin 63) := Fin.ext h61
        subst role
        simpa [can, exPub, ex, exactFinalTransitionEnvWith, withFinalComputeChallenges,
          exactFinalTransitionEnv, exactFinalExtensionRow] using
          canonical_gather_walkLine A hn nodes hnodes b chalVal pubVal orbit i
      · have hr : role = (62 : Fin 63) := Fin.ext h62
        subst role
        simpa [can, exPub, ex, exactFinalTransitionEnvWith, withFinalComputeChallenges,
          exactFinalTransitionEnv, exactFinalExtensionRow] using
          canonical_gather_walkInv A hn nodes hnodes b chalVal pubVal orbit i
    · intro role hrole h41 h44
      rcases hrole with hlt | h61 | h62
      · let r : Fin 58 := ⟨role, hlt⟩
        have hc := canonical_gather_ext_core_next
          A hn nodes hnodes b chalVal pubVal orbit i hi
            (by simpa [mul_comm] using hstep i hi) r
        have he : exPub.extTraceNext role =
            coreExtensionValue (encodedRowAt A ⟨(i : ℕ) + 1, hi⟩) r := by
          simp [exPub, ex, exactFinalTransitionEnvWith, withFinalComputeChallenges,
            exactFinalTransitionEnv, exactFinalExtensionRow, hlt, r]
        have hc' : can.extTraceNext role =
            formRLeafCore b (encodedRowAt A ⟨(i : ℕ) + 1, hi⟩) r := by
          simpa [can, r] using hc
        exact hc'.trans ((formRLeafCore_eq_core b _ r ⟨h41, h44⟩).trans he.symm)
      · have hr : role = (61 : Fin 63) := Fin.ext h61
        subst role
        simpa [can, exPub, ex, exactFinalTransitionEnvWith, withFinalComputeChallenges,
          exactFinalTransitionEnv, exactFinalExtensionRow, Nat.add_assoc] using
          canonical_gather_walkLine_next A hn nodes hnodes b chalVal pubVal orbit i hi
            (by simpa [mul_comm] using hstep i hi)
      · have hr : role = (62 : Fin 63) := Fin.ext h62
        subst role
        simpa [can, exPub, ex, exactFinalTransitionEnvWith, withFinalComputeChallenges,
          exactFinalTransitionEnv, exactFinalExtensionRow, Nat.add_assoc] using
          canonical_gather_walkInv_next A hn nodes hnodes b chalVal pubVal orbit i hi
            (by simpa [mul_comm] using hstep i hi)
    · intro q
      have hr : exPub.chal q = exactFinalChallengeWith A c q := by
        fin_cases q <;>
          rfl
      rw [hr]
      simpa [can] using canonical_gather_challenge_of_coordinates
        A hn nodes b chalVal pubVal orbit q
          (exactFinalChallengeWith A c q) (hchal q) i
    · intro q; rfl
    · intro q; rfl
    · exact correctedFinalExtGate_residualFree gate
    · left
      have hc := canonical_gather_ext_core
        A hn nodes hnodes b chalVal pubVal orbit i ⟨41, by decide⟩
      have he : exPub.extTrace ⟨41, by decide⟩ =
          coreExtensionValue (encodedRowAt A i) ⟨41, by decide⟩ := by
        simp [exPub, ex, exactFinalTransitionEnvWith, withFinalComputeChallenges,
          exactFinalTransitionEnv, exactFinalExtensionRow]
      have hc' := by simpa [can] using hc
      exact hc'.trans
        ((formRLeafCore_eq_core_all b _ _).trans he.symm)
    · left
      have hc := canonical_gather_ext_core
        A hn nodes hnodes b chalVal pubVal orbit i ⟨44, by decide⟩
      have he : exPub.extTrace ⟨44, by decide⟩ =
          coreExtensionValue (encodedRowAt A i) ⟨44, by decide⟩ := by
        simp [exPub, ex, exactFinalTransitionEnvWith, withFinalComputeChallenges,
          exactFinalTransitionEnv, exactFinalExtensionRow]
      have hc' := by simpa [can] using hc
      exact hc'.trans
        ((formRLeafCore_eq_core_all b _ _).trans he.symm)
    · left
      have hc := canonical_gather_ext_core_next
        A hn nodes hnodes b chalVal pubVal orbit i hi
          (by simpa [mul_comm] using hstep i hi) ⟨41, by decide⟩
      have he : exPub.extTraceNext ⟨41, by decide⟩ =
          coreExtensionValue (encodedRowAt A ⟨(i : ℕ) + 1, hi⟩) ⟨41, by decide⟩ := by
        simp [exPub, ex, exactFinalTransitionEnvWith, withFinalComputeChallenges,
          exactFinalTransitionEnv, exactFinalExtensionRow]
      have hc' := by simpa [can] using hc
      exact hc'.trans
        ((formRLeafCore_eq_core_all b _ _).trans he.symm)
    · left
      have hc := canonical_gather_ext_core_next
        A hn nodes hnodes b chalVal pubVal orbit i hi
          (by simpa [mul_comm] using hstep i hi) ⟨44, by decide⟩
      have he : exPub.extTraceNext ⟨44, by decide⟩ =
          coreExtensionValue (encodedRowAt A ⟨(i : ℕ) + 1, hi⟩) ⟨44, by decide⟩ := by
        simp [exPub, ex, exactFinalTransitionEnvWith, withFinalComputeChallenges,
          exactFinalTransitionEnv, exactFinalExtensionRow]
      have hc' := by simpa [can] using hc
      exact hc'.trans
        ((formRLeafCore_eq_core_all b _ _).trans he.symm)
    · intro q; exact canonical_gather_certBase A hn nodes hnodes b chalVal pubVal orbit hax i q
    · intro q; exact canonical_gather_certExt A hn nodes hnodes b chalVal pubVal orbit hax (fun k
        => hchal 9 k) i q
  rw [hsame, hpub, hex]

theorem canonical_extensionCore_nonterminal_with
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (c : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hstep : ∀ (i : Fin R.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < R.problem.cfg.compRows),
      nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hchal : ExactFinalChallengeCoordinatesWith b A c chalVal)
    (hax : FormRAxisBound A b) (hwidth : FormRWidth F)
    (hord : 2 ≤ R.problem.cfg.compRows →
      R.problem.cfg.compRows ≤ orderOf R.computeWalkAlpha)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    let envF := envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal
    let env := gatherCorrectedFinalTypedEnv b envF
    ∀ gate : CorrectedCoreExtGateId, correctedCoreSemanticValue env gate = 0 := by
  dsimp only
  let envF := envOfTrace
    (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
    orbit.ω (nodes i) chalVal pubVal
  let env := gatherCorrectedFinalTypedEnv b envF
  have hgate : ∀ gate : CorrectedCoreExtGateId,
      (correctedFinalExtGate gate).eval env = 0 := fun gate =>
    canonical_ext_gate_nonterminal_zero_with
      A hA c hn nodes hnodes b chalVal pubVal orbit hstep hchal hax hwidth hord i hi gate
  have hnotLast : env.baseTrace 12 = 0 := by
    have hb := canonical_gather_base_current
      A hn nodes hnodes b chalVal pubVal orbit i (12 : Fin 13)
    have hne : i ≠
        ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩ := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only at hv
      omega
    simpa [env, finalBaseCell, hne] using hb
  have haux := correctedCanonical_residualAux01
    A hn nodes hnodes b chalVal pubVal orbit i
  have hres : ∀ j : CorrectedResidualWitnessId, j ≠ 2 →
      env.extTrace (residualWitnessRole j) = 0 := by
    intro j hj
    have heq :
        env.extTrace (residualWitnessRole j) =
          (correctedFinalResidualSource j).eval env := by
      exact sub_eq_zero.mp (by
        simpa [env, envF, correctedAuxSemanticValue, hj] using haux j hj)
    rw [heq]
    fin_cases j
    · exact hgate packedWalkCountId
    · exact hgate packedWalkAccId
    · exact absurd rfl hj
  have hchain := canonical_accAfterChain A hn nodes hnodes b chalVal pubVal orbit hstep i
  have hnl : notLastScalar env = 1 := by simp [notLastScalar, hnotLast]
  intro gate
  by_cases h10 : gate = packedWalkCountId
  · subst gate
    simp only [correctedCoreSemanticValue, ↓reduceIte]
    rw [hnl, hres 0 (by decide)]
    simp
  by_cases h11 : gate = packedWalkAccId
  · subst gate
    simp only [correctedCoreSemanticValue, packedWalkCountId, h10, ↓reduceIte]
    rw [hnl, hres 1 (by decide)]
    simp
  by_cases h20 : gate = packedChainId
  · subst gate
    simp only [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId, h10, h11,
      ↓reduceIte]
    simpa [env, envF] using hchain
  by_cases h89 : gate = packedLnChainId ∨ gate = packedWalkLnId
  · simp only [correctedCoreSemanticValue, h10, h11, h20, h89, ↓reduceIte]
    rw [hnl]
    simpa using hgate gate
  · simp only [correctedCoreSemanticValue, h10, h11, h20, h89, ↓reduceIte]
    exact hgate gate

theorem canonical_extensionCore_nonterminal
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hstep : ∀ (i : Fin R.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < R.problem.cfg.compRows),
      nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hchal : ExactFinalChallengeCoordinates b A chalVal)
    (hax : FormRAxisBound A b) (hwidth : FormRWidth F)
    (hord : 2 ≤ R.problem.cfg.compRows →
      R.problem.cfg.compRows ≤ orderOf R.computeWalkAlpha)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    let envF := envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal
    let env := gatherCorrectedFinalTypedEnv b envF
    ∀ gate : CorrectedCoreExtGateId,
      correctedCoreSemanticValue env gate = 0 := by
  dsimp only
  let envF := envOfTrace
    (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
    orbit.ω (nodes i) chalVal pubVal
  let env := gatherCorrectedFinalTypedEnv b envF
  have hgate : ∀ gate : CorrectedCoreExtGateId,
      (correctedFinalExtGate gate).eval env = 0 := by
    intro gate
    exact canonical_ext_gate_nonterminal_zero
      A hA hn nodes hnodes b chalVal pubVal orbit hstep hchal hax hwidth hord i hi gate
  have hnotLast : env.baseTrace 12 = 0 := by
    have hb := canonical_gather_base_current
      A hn nodes hnodes b chalVal pubVal orbit i (12 : Fin 13)
    have hne : i ≠
        ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩ := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only at hv
      omega
    simpa [env, finalBaseCell, hne] using hb
  have haux := correctedCanonical_residualAux01
    A hn nodes hnodes b chalVal pubVal orbit i
  have hres : ∀ j : CorrectedResidualWitnessId, j ≠ 2 →
      env.extTrace (residualWitnessRole j) = 0 := by
    intro j hj
    have heq :
        env.extTrace (residualWitnessRole j) =
          (correctedFinalResidualSource j).eval env := by
      exact sub_eq_zero.mp (by
        simpa [env, envF, correctedAuxSemanticValue, hj] using haux j hj)
    rw [heq]
    fin_cases j
    · exact hgate packedWalkCountId
    · exact hgate packedWalkAccId
    · exact absurd rfl hj
  have hchain := canonical_accAfterChain A hn nodes hnodes b chalVal pubVal orbit hstep i
  have hnl : notLastScalar env = 1 := by
    simp [notLastScalar, hnotLast]
  intro gate
  by_cases h10 : gate = packedWalkCountId
  · subst gate
    simp only [correctedCoreSemanticValue, ↓reduceIte]
    rw [hnl, hres 0 (by decide)]
    simp
  by_cases h11 : gate = packedWalkAccId
  · subst gate
    simp only [correctedCoreSemanticValue, packedWalkCountId, h10, ↓reduceIte]
    rw [hnl, hres 1 (by decide)]
    simp
  by_cases h20 : gate = packedChainId
  · subst gate
    simp only [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId, h10, h11,
      ↓reduceIte]
    simpa [env, envF] using hchain
  by_cases h89 : gate = packedLnChainId ∨ gate = packedWalkLnId
  · simp only [correctedCoreSemanticValue, h10, h11, h20, h89, ↓reduceIte]
    rw [hnl]
    simpa using hgate gate
  · simp only [correctedCoreSemanticValue, h10, h11, h20, h89, ↓reduceIte]
    exact hgate gate

/-- Exact residual after the adjacent-row proof: 75 row-local gates remain active on the
terminal row; the five genuinely transitional/residual IDs are killed by `notLast`.
Queue-witness IDs `76`/`77` are last-row tiling, not this residual. -/
def terminalCurrentGateIds : List CorrectedCoreExtGateId :=
  terminalCurrentExtGateIds

theorem terminalCurrentGateIds_length : terminalCurrentGateIds.length = 75 :=
  terminalCurrentExtGateIds_length

theorem mem_terminalCurrentGateIds_of_unmasked (gate : CorrectedCoreExtGateId)
    (h : gate ≠ packedLnChainId ∧ gate ≠ packedWalkLnId ∧ gate ≠ packedWalkCountId ∧
      gate ≠ packedWalkAccId ∧ gate ≠ packedChainId ∧
      gate ≠ packedQueueNonEmptyId ∧ gate ≠ packedQueueTilingId) :
    gate ∈ terminalCurrentGateIds := by
  simp only [terminalCurrentGateIds, terminalCurrentExtGateIds, List.mem_append]
  have hv : (gate : ℕ) < 82 := gate.isLt
  have h72 : (gate : ℕ) ≠ 72 := by
    intro heq; exact h.1 (Fin.eq_of_val_eq heq)
  have h73 : (gate : ℕ) ≠ 73 := by
    intro heq; exact h.2.1 (Fin.eq_of_val_eq heq)
  have h74 : (gate : ℕ) ≠ 74 := by
    intro heq; exact h.2.2.1 (Fin.eq_of_val_eq heq)
  have h75 : (gate : ℕ) ≠ 75 := by
    intro heq; exact h.2.2.2.1 (Fin.eq_of_val_eq heq)
  have h81 : (gate : ℕ) ≠ 81 := by
    intro heq; exact h.2.2.2.2.1 (Fin.eq_of_val_eq heq)
  have h76 : (gate : ℕ) ≠ 76 := by
    intro heq; exact h.2.2.2.2.2.1 (Fin.eq_of_val_eq heq)
  have h77 : (gate : ℕ) ≠ 77 := by
    intro heq; exact h.2.2.2.2.2.2 (Fin.eq_of_val_eq heq)
  by_cases hlt : (gate : ℕ) < 72
  · refine Or.inl (List.mem_ofFn.mpr ⟨⟨gate.val, hlt⟩, Fin.eq_of_val_eq (by simp)⟩)
  · refine Or.inr ?_
    have : (gate : ℕ) = 78 ∨ (gate : ℕ) = 79 ∨ (gate : ℕ) = 80 := by omega
    rcases this with h78 | h79 | h80
    · have heq : gate = ⟨78, by omega⟩ := Fin.eq_of_val_eq h78
      simp [heq]
    · have heq : gate = ⟨79, by omega⟩ := Fin.eq_of_val_eq h79
      simp [heq]
    · have heq : gate = ⟨80, by omega⟩ := Fin.eq_of_val_eq h80
      simp [heq]

set_option maxRecDepth 300000 in
theorem terminal_extensionCore_of_current_gates
    (env : CorrectedFinalTypedEnv F K)
    (hlast : env.baseTrace 12 = 1)
    (hcurrent : ∀ gate ∈ terminalCurrentGateIds,
      (correctedFinalExtGate gate).eval env = 0)
    (htile : (correctedFinalExtGate packedQueueTilingId).eval env = 0)
    (hnonempty : (correctedFinalExtGate packedQueueNonEmptyId).eval env = 0) :
    ∀ gate : CorrectedCoreExtGateId,
      correctedCoreSemanticValue env gate = 0 := by
  intro gate
  have hnl0 : notLastScalar env = 0 := by simp [notLastScalar, hlast]
  by_cases h75 : gate = packedWalkCountId
  · subst gate
    simp only [correctedCoreSemanticValue, ↓reduceIte]
    rw [hnl0]
    simp
  by_cases h76 : gate = packedWalkAccId
  · subst gate
    simp only [correctedCoreSemanticValue, packedWalkCountId, h75, ↓reduceIte]
    rw [hnl0]
    simp
  by_cases h80 : gate = packedChainId
  · subst gate
    simp only [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId, h75, h76,
      ↓reduceIte]
    simp [accAfterChain, CorrectedFinalTypedExpr.eval, hlast]
  by_cases h89 : gate = packedLnChainId ∨ gate = packedWalkLnId
  · simp only [correctedCoreSemanticValue, h75, h76, h80, h89, ↓reduceIte]
    rw [hnl0]
    simp
  by_cases hq0 : gate = packedQueueNonEmptyId
  · subst gate
    simp only [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId, packedChainId,
      packedLnChainId, packedWalkLnId, packedQueueNonEmptyId, h75, h76, h80, h89, ↓reduceIte]
    exact hnonempty
  by_cases hq1 : gate = packedQueueTilingId
  · subst gate
    simp only [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId, packedChainId,
      packedLnChainId, packedWalkLnId, packedQueueNonEmptyId, packedQueueTilingId,
      h75, h76, h80, h89, hq0, ↓reduceIte]
    exact htile
  · have hmem := mem_terminalCurrentGateIds_of_unmasked gate ⟨by
      intro h; exact h89 (Or.inl h), by
      intro h; exact h89 (Or.inr h), h75, h76, h80, hq0, hq1⟩
    simp only [correctedCoreSemanticValue, h75, h76, h80, h89, hq0, hq1, ↓reduceIte]
    exact hcurrent _ hmem

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
/-- The canonical final row satisfies all sixteen row-local extension gates directly from its
Vcomp/AIR row and sampled denominator pins.  No successor hypothesis is introduced. -/
theorem canonical_extensionCore_terminal
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hchal : ExactFinalChallengeCoordinates b A chalVal)
    (hax : FormRAxisBound A b) (hwidth : FormRWidth F) :
    let last : Fin R.problem.cfg.compRows :=
      ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
    let envF := envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes last) chalVal pubVal
    let env := gatherCorrectedFinalTypedEnv b envF
    ∀ gate : CorrectedCoreExtGateId,
      correctedCoreSemanticValue env gate = 0 := by
  dsimp only
  let last : Fin R.problem.cfg.compRows :=
    ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
  let can := gatherCorrectedFinalTypedEnv b
    (envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes last) chalVal pubVal)
  let ex := exactFinalCurrentEnv A last
  let exPub : CorrectedFinalTypedEnv F K :=
    { ex with
      extensionPublic := can.extensionPublic
      scalarPublic := can.scalarPublic }
  have hlast : can.baseTrace 12 = 1 := by
    have hb := canonical_gather_base_current
      A hn nodes hnodes b chalVal pubVal orbit last (12 : Fin 13)
    simpa [can, last, finalBaseCell] using hb
  have hnonempty : (correctedFinalExtGate packedQueueNonEmptyId).eval can = 0 := by
    rw [← correctedFinalExtGate_eval_source, packedQueueNonEmpty_source]
    exact exact_queueNonEmpty_last can hlast
  have htile : (correctedFinalExtGate packedQueueTilingId).eval can = 0 := by
    rw [← correctedFinalExtGate_eval_source, packedQueueTiling_source]
    have hover := canonical_gather_walkOverlay_current
      A hn nodes hnodes b chalVal pubVal orbit last (0 : Fin 5)
    have hwalk := canonical_gather_walkLine
      A hn nodes hnodes b chalVal pubVal orbit last
    have heq := exact_compute_last_count_eq_ln A hA
    have h12 : can.toSourceEnv.trace 12 = 1 := by
      simp [CorrectedFinalTypedEnv.toSourceEnv, hlast]
    have hline : (finalWalkLine .traceCur).eval can.toSourceEnv =
        A.exact.computeWalk.ln R.problem.cfg.compRows := by
      have hsrc : (finalWalkLine .traceCur).eval can.toSourceEnv = can.extTrace 61 := by
        simp [finalWalkLine, finalWalkLineIndex, finalWalkLineRole, ext0,
          CorrectedFinalTypedEnv.toSourceEnv, Expr.eval]
      rw [hsrc]
      have : (last : ℕ) + 1 = R.problem.cfg.compRows := by
        simp [last]; omega
      simpa [can, this] using hwalk
    have hcount : (overlayCoord .traceCur 0).eval can.toSourceEnv =
        A.exact.computeWalk.count R.problem.cfg.compRows := by
      have : (last : ℕ) + 1 = R.problem.cfg.compRows := by
        simp [last]; omega
      simpa [can, this] using hover
    simp [OptimizedComputeGateBasis.walkQueueTiling, Expr.eval, h12, hcount, hline, heq]
  refine terminal_extensionCore_of_current_gates can hlast ?_ htile hnonempty
  intro gate hgate
  have hex : (correctedFinalExtGate gate).eval ex = 0 := by
    exact exact_correctedFinalExtGate_current A hA last
      (OptimizedComputeFormRDenoms.formRAxisSmall_of_bound A b hax) hwidth gate
      (by simpa [terminalCurrentGateIds] using hgate)
  have hpub : (correctedFinalExtGate gate).eval exPub =
      (correctedFinalExtGate gate).eval ex := by
    apply CorrectedFinalTypedExpr.eval_eq_of_publicFree (hexp := by rfl)
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · exact correctedFinalExtGate_publicFree gate
    · intro q; rfl
    · intro q; rfl
  have hsame : (correctedFinalExtGate gate).eval can =
      (correctedFinalExtGate gate).eval exPub := by
    apply CorrectedFinalTypedExpr.eval_eq_of_terminalCurrentOnlyC_skipLeaf
      (hexp := by first
      | exact canonical_gather_expCol A hn nodes hnodes b chalVal pubVal orbit i
      | exact canonical_gather_expCol A hn nodes hnodes b chalVal pubVal orbit last)
    · intro q
      simpa [can, exPub, ex, exactFinalCurrentEnv] using
        canonical_gather_base_current A hn nodes hnodes b chalVal pubVal orbit last q
    · intro role hrole h41 h44
      let r : Fin 58 := ⟨role, hrole⟩
      have hc := canonical_gather_ext_core
        A hn nodes hnodes b chalVal pubVal orbit last r
      have he : exPub.extTrace role = coreExtensionValue (encodedRowAt A last) r := by
        simp [exPub, ex, exactFinalCurrentEnv, exactFinalExtensionRow, hrole, r]
      have hc' : can.extTrace role = formRLeafCore b (encodedRowAt A last) r := by
        simpa [can, r] using hc
      exact hc'.trans ((formRLeafCore_eq_core b _ r ⟨h41, h44⟩).trans he.symm)
    · intro q
      simpa [can, exPub, ex, exactFinalCurrentEnv] using
        canonical_gather_challenge A hn nodes b chalVal pubVal orbit hchal last q
    · intro q; rfl
    · intro q; rfl
    · exact correctedFinalExtGate_terminalCurrentOnly gate
        (by simpa [terminalCurrentGateIds] using hgate)
    · left
      have hc := canonical_gather_ext_core
        A hn nodes hnodes b chalVal pubVal orbit last ⟨41, by decide⟩
      have he : exPub.extTrace ⟨41, by decide⟩ =
          coreExtensionValue (encodedRowAt A last) ⟨41, by decide⟩ := by
        simp [exPub, ex, exactFinalCurrentEnv, exactFinalExtensionRow]
      have hc' := by simpa [can] using hc
      exact hc'.trans
        ((formRLeafCore_eq_core_all b _ _).trans he.symm)
    · left
      have hc := canonical_gather_ext_core
        A hn nodes hnodes b chalVal pubVal orbit last ⟨44, by decide⟩
      have he : exPub.extTrace ⟨44, by decide⟩ =
          coreExtensionValue (encodedRowAt A last) ⟨44, by decide⟩ := by
        simp [exPub, ex, exactFinalCurrentEnv, exactFinalExtensionRow]
      have hc' := by simpa [can] using hc
      exact hc'.trans
        ((formRLeafCore_eq_core_all b _ _).trans he.symm)
    · intro q; exact canonical_gather_certBase A hn nodes hnodes b chalVal pubVal orbit hax last q
    · intro q; exact canonical_gather_certExt A hn nodes hnodes b chalVal pubVal orbit hax (fun k
        => hchal 9 k) last q
  rw [hsame, hpub, hex]

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
theorem canonical_extensionCore_terminal_with
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (c : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hchal : ExactFinalChallengeCoordinatesWith b A c chalVal)
    (hax : FormRAxisBound A b) (hwidth : FormRWidth F) :
    let last : Fin R.problem.cfg.compRows :=
      ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
    let envF := envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes last) chalVal pubVal
    let env := gatherCorrectedFinalTypedEnv b envF
    ∀ gate : CorrectedCoreExtGateId, correctedCoreSemanticValue env gate = 0 := by
  dsimp only
  let last : Fin R.problem.cfg.compRows :=
    ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
  let can := gatherCorrectedFinalTypedEnv b
    (envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes last) chalVal pubVal)
  let ex := exactFinalCurrentEnvWith A c last
  let exPub : CorrectedFinalTypedEnv F K :=
    { ex with extensionPublic := can.extensionPublic, scalarPublic := can.scalarPublic }
  have hlast : can.baseTrace 12 = 1 := by
    have hb := canonical_gather_base_current
      A hn nodes hnodes b chalVal pubVal orbit last (12 : Fin 13)
    simpa [can, last, finalBaseCell] using hb
  have hnonempty : (correctedFinalExtGate packedQueueNonEmptyId).eval can = 0 := by
    rw [← correctedFinalExtGate_eval_source, packedQueueNonEmpty_source]
    exact exact_queueNonEmpty_last can hlast
  have htile : (correctedFinalExtGate packedQueueTilingId).eval can = 0 := by
    rw [← correctedFinalExtGate_eval_source, packedQueueTiling_source]
    have hover := canonical_gather_walkOverlay_current
      A hn nodes hnodes b chalVal pubVal orbit last (0 : Fin 5)
    have hwalk := canonical_gather_walkLine
      A hn nodes hnodes b chalVal pubVal orbit last
    have heq := exact_compute_last_count_eq_ln A hA
    have h12 : can.toSourceEnv.trace 12 = 1 := by
      simp [CorrectedFinalTypedEnv.toSourceEnv, hlast]
    have hline : (finalWalkLine .traceCur).eval can.toSourceEnv =
        A.exact.computeWalk.ln R.problem.cfg.compRows := by
      have hsrc : (finalWalkLine .traceCur).eval can.toSourceEnv = can.extTrace 61 := by
        simp [finalWalkLine, finalWalkLineIndex, finalWalkLineRole, ext0,
          CorrectedFinalTypedEnv.toSourceEnv, Expr.eval]
      rw [hsrc]
      have : (last : ℕ) + 1 = R.problem.cfg.compRows := by
        simp [last]; omega
      simpa [can, this] using hwalk
    have hcount : (overlayCoord .traceCur 0).eval can.toSourceEnv =
        A.exact.computeWalk.count R.problem.cfg.compRows := by
      have : (last : ℕ) + 1 = R.problem.cfg.compRows := by
        simp [last]; omega
      simpa [can, this] using hover
    simp [OptimizedComputeGateBasis.walkQueueTiling, Expr.eval, h12, hcount, hline, heq]
  refine terminal_extensionCore_of_current_gates can hlast ?_ htile hnonempty
  intro gate hgate
  have hex : (correctedFinalExtGate gate).eval ex = 0 := by
    exact exact_correctedFinalExtGate_currentWith A hA c last
      (OptimizedComputeFormRDenoms.formRAxisSmall_of_bound A b hax) hwidth gate
      (by simpa [terminalCurrentGateIds] using hgate)
  have hpub : (correctedFinalExtGate gate).eval exPub =
      (correctedFinalExtGate gate).eval ex := by
    apply CorrectedFinalTypedExpr.eval_eq_of_publicFree (hexp := by rfl)
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · exact correctedFinalExtGate_publicFree gate
    · intro q; rfl
    · intro q; rfl
  have hsame : (correctedFinalExtGate gate).eval can =
      (correctedFinalExtGate gate).eval exPub := by
    apply CorrectedFinalTypedExpr.eval_eq_of_terminalCurrentOnlyC_skipLeaf
      (hexp := by first
      | exact canonical_gather_expCol A hn nodes hnodes b chalVal pubVal orbit i
      | exact canonical_gather_expCol A hn nodes hnodes b chalVal pubVal orbit last)
    · intro q
      simpa [can, exPub, ex, exactFinalCurrentEnvWith, withFinalComputeChallenges,
        exactFinalCurrentEnv] using
        canonical_gather_base_current A hn nodes hnodes b chalVal pubVal orbit last q
    · intro role hrole h41 h44
      let r : Fin 58 := ⟨role, hrole⟩
      have hc := canonical_gather_ext_core
        A hn nodes hnodes b chalVal pubVal orbit last r
      have he : exPub.extTrace role = coreExtensionValue (encodedRowAt A last) r := by
        simp [exPub, ex, exactFinalCurrentEnvWith, withFinalComputeChallenges,
          exactFinalCurrentEnv, exactFinalExtensionRow, hrole, r]
      have hc' : can.extTrace role = formRLeafCore b (encodedRowAt A last) r := by
        simpa [can, r] using hc
      exact hc'.trans ((formRLeafCore_eq_core b _ r ⟨h41, h44⟩).trans he.symm)
    · intro q
      have hr : exPub.chal q = exactFinalChallengeWith A c q := by
        fin_cases q <;>
          rfl
      rw [hr]
      simpa [can] using canonical_gather_challenge_of_coordinates
        A hn nodes b chalVal pubVal orbit q
          (exactFinalChallengeWith A c q) (hchal q) last
    · intro q; rfl
    · intro q; rfl
    · exact correctedFinalExtGate_terminalCurrentOnly gate
        (by simpa [terminalCurrentGateIds] using hgate)
    · left
      have hc := canonical_gather_ext_core
        A hn nodes hnodes b chalVal pubVal orbit last ⟨41, by decide⟩
      have he : exPub.extTrace ⟨41, by decide⟩ =
          coreExtensionValue (encodedRowAt A last) ⟨41, by decide⟩ := by
        simp [exPub, ex, exactFinalCurrentEnvWith, withFinalComputeChallenges,
          exactFinalCurrentEnv, exactFinalExtensionRow]
      have hc' := by simpa [can] using hc
      exact hc'.trans
        ((formRLeafCore_eq_core_all b _ _).trans he.symm)
    · left
      have hc := canonical_gather_ext_core
        A hn nodes hnodes b chalVal pubVal orbit last ⟨44, by decide⟩
      have he : exPub.extTrace ⟨44, by decide⟩ =
          coreExtensionValue (encodedRowAt A last) ⟨44, by decide⟩ := by
        simp [exPub, ex, exactFinalCurrentEnvWith, withFinalComputeChallenges,
          exactFinalCurrentEnv, exactFinalExtensionRow]
      have hc' := by simpa [can] using hc
      exact hc'.trans
        ((formRLeafCore_eq_core_all b _ _).trans he.symm)
    · intro q; exact canonical_gather_certBase A hn nodes hnodes b chalVal pubVal orbit hax last q
    · intro q; exact canonical_gather_certExt A hn nodes hnodes b chalVal pubVal orbit hax (fun k
        => hchal 9 k) last q
  rw [hsame, hpub, hex]

/-- Every source in the thirteen successor-free families vanishes on the canonical terminal row. -/
theorem canonical_terminalCurrentNonIOSourceFamilies
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hchal : ExactFinalChallengeCoordinates b A chalVal)
    (e : Expr) (he : e ∈ terminalCurrentNonIOSourceFamilies.flatten) :
    let last : Fin R.problem.cfg.compRows :=
      ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
    let can := gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes last) chalVal pubVal)
    e.eval can.toSourceEnv = 0 := by
  dsimp only
  let last : Fin R.problem.cfg.compRows :=
    ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
  let can := gatherCorrectedFinalTypedEnv b
    (envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes last) chalVal pubVal)
  let ex := exactFinalCurrentEnv A last
  let exPub : CorrectedFinalTypedEnv F K :=
    { ex with
      extensionPublic := can.extensionPublic
      scalarPublic := can.scalarPublic }
  obtain ⟨t, htLower, htCurrent, htPublic⟩ :=
    terminalCurrentNonIOSource_lower_receipt e he
  rw [correctedLowerFinal_eval can e t htLower]
  have hsame : t.eval can = t.eval exPub := by
    apply CorrectedFinalTypedExpr.eval_eq_of_terminalCurrentOnly_skipLeaf
    · intro q
      simpa [can, exPub, ex, exactFinalCurrentEnv] using
        canonical_gather_base_current A hn nodes hnodes b chalVal pubVal orbit last q
    · intro role hrole h41 h44
      let r : Fin 58 := ⟨role, hrole⟩
      have hc := canonical_gather_ext_core
        A hn nodes hnodes b chalVal pubVal orbit last r
      have heq : exPub.extTrace role = coreExtensionValue (encodedRowAt A last) r := by
        simp [exPub, ex, exactFinalCurrentEnv, exactFinalExtensionRow, hrole, r]
      have hc' : can.extTrace role = formRLeafCore b (encodedRowAt A last) r := by
        simpa [can, r] using hc
      exact hc'.trans ((formRLeafCore_eq_core b _ r ⟨h41, h44⟩).trans heq.symm)
    · intro q
      simpa [can, exPub, ex, exactFinalCurrentEnv] using
        canonical_gather_challenge A hn nodes b chalVal pubVal orbit hchal last q
    · intro q; rfl
    · intro q; rfl
    · exact htCurrent
    · left
      have hc := canonical_gather_ext_core
        A hn nodes hnodes b chalVal pubVal orbit last ⟨41, by decide⟩
      have he : exPub.extTrace ⟨41, by decide⟩ =
          coreExtensionValue (encodedRowAt A last) ⟨41, by decide⟩ := by
        simp [exPub, ex, exactFinalCurrentEnv, exactFinalExtensionRow]
      have hc' := by simpa [can] using hc
      exact hc'.trans
        ((formRLeafCore_eq_core_all b _ _).trans he.symm)
    · left
      have hc := canonical_gather_ext_core
        A hn nodes hnodes b chalVal pubVal orbit last ⟨44, by decide⟩
      have he : exPub.extTrace ⟨44, by decide⟩ =
          coreExtensionValue (encodedRowAt A last) ⟨44, by decide⟩ := by
        simp [exPub, ex, exactFinalCurrentEnv, exactFinalExtensionRow]
      have hc' := by simpa [can] using hc
      exact hc'.trans
        ((formRLeafCore_eq_core_all b _ _).trans he.symm)
  have hpub : t.eval exPub = t.eval ex := by
    apply CorrectedFinalTypedExpr.eval_eq_of_publicFree (hexp := by rfl)
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · exact htPublic
    · intro q; rfl
    · intro q; rfl
  rw [hsame, hpub, ← correctedLowerFinal_eval ex e t htLower]
  exact exact_terminalCurrentNonIOSourceFamilies A hA last e he

/-- The concrete-coordinate zero fold challenge makes the full terminal family collision-free:
the thirteen current-row families vanish and the four successor families are singletons. -/
theorem canonical_terminal_finalComputeCollisionFree
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hchal : ExactFinalChallengeCoordinates b A chalVal) :
    let last : Fin R.problem.cfg.compRows :=
      ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
    FinalComputeCollisionFree
      (gatherCorrectedFinalTypedEnv b
        (envOfTrace
          (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes last) chalVal pubVal)).toSourceEnv := by
  dsimp only
  let last : Fin R.problem.cfg.compRows :=
    ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
  let env := (gatherCorrectedFinalTypedEnv b
    (envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes last) chalVal pubVal)).toSourceEnv
  intro es hes hfold e he
  have hterminal (es : List Expr) (hes : es ∈ terminalCurrentNonIOSourceFamilies)
      (e : Expr) (he : e ∈ es) : e.eval env = 0 := by
    exact canonical_terminalCurrentNonIOSourceFamilies A hA hn nodes hnodes b
      chalVal pubVal orbit hchal e (List.mem_flatten.mpr ⟨es, hes, he⟩)
  simp only [finalNonIOSourceFamilies17, nonIOSourceFamilies17With,
    List.mem_cons, List.not_mem_nil, or_false] at hes
  rcases hes with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hterminal _ (by simp [terminalCurrentNonIOSourceFamilies]) e he
  · exact hterminal _ (by simp [terminalCurrentNonIOSourceFamilies]) e he
  · exact hterminal _ (by simp [terminalCurrentNonIOSourceFamilies]) e he
  · exact hterminal _ (by simp [terminalCurrentNonIOSourceFamilies]) e he
  · exact hterminal _ (by simp [terminalCurrentNonIOSourceFamilies]) e he
  · exact hterminal _ (by simp [terminalCurrentNonIOSourceFamilies]) e he
  · exact hterminal _ (by simp [terminalCurrentNonIOSourceFamilies]) e he
  · exact hterminal _ (by simp [terminalCurrentNonIOSourceFamilies]) e he
  · simp only [List.mem_singleton] at he
    subst e
    simpa [finalRlcFold, Expr.eval] using hfold
  · simp only [List.mem_singleton] at he
    subst e
    simpa [finalRlcFold, Expr.eval] using hfold
  · simp only [List.mem_singleton] at he
    subst e
    simpa [finalRlcFold, Expr.eval] using hfold
  · simp only [List.mem_singleton] at he
    subst e
    simpa [finalRlcFold, Expr.eval] using hfold
  · exact hterminal _ (by simp [terminalCurrentNonIOSourceFamilies]) e he
  · exact hterminal _ (by simp [terminalCurrentNonIOSourceFamilies]) e he
  · exact hterminal _ (by simp [terminalCurrentNonIOSourceFamilies]) e he
  · exact hterminal _ (by simp [terminalCurrentNonIOSourceFamilies]) e he
  · exact hterminal _ (by simp [terminalCurrentNonIOSourceFamilies]) e he

/-- A strict orbit has even order, so the base field is not characteristic 2. -/
private theorem two_ne_zero_of_strict_orbit {hgt : ℕ}
    (orbit : StrictOrbitDomain F 3 hgt) : (2 : F) ≠ 0 := by
  intro hchar
  have hord : orderOf orbit.ω = 3 * 2 ^ hgt := orbit.order_ω
  have hdvd : 2 ∣ orderOf orbit.ω := by
    rw [hord]
    refine ⟨3 * 2 ^ (hgt - 1), ?_⟩
    have hh : hgt - 1 + 1 = hgt := Nat.sub_add_cancel orbit.h_pos
    calc
      3 * 2 ^ hgt = 3 * 2 ^ (hgt - 1 + 1) := by rw [hh]
      _ = 3 * (2 ^ (hgt - 1) * 2) := by rw [pow_succ]
      _ = 2 * (3 * 2 ^ (hgt - 1)) := by ring
  set n := orderOf orbit.ω
  have hpow : (orbit.ω ^ (n / 2)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel hdvd, pow_orderOf_eq_one]
  have hne1 : orbit.ω ^ (n / 2) ≠ 1 := by
    intro h1
    have hd := (orderOf_dvd_iff_pow_eq_one).mpr h1
    obtain ⟨k, hk⟩ := hd
    have hnge : 2 ≤ n := by
      rw [show n = 3 * 2 ^ hgt from hord]
      have : 1 ≤ 2 ^ hgt := Nat.one_le_pow hgt 2 (by decide)
      omega
    cases k with
    | zero =>
      simp at hk
      omega
    | succ k =>
      have hle : n ≤ n / 2 := by
        have hmul : n * 1 ≤ n * (k + 1) := Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le k))
        simpa [hk, Nat.mul_comm, Nat.one_mul] using hmul
      have hlt : n / 2 < n := Nat.div_lt_self (by omega : 0 < n) (by decide : 1 < 2)
      omega
  have hfac : (orbit.ω ^ (n / 2) - 1) * (orbit.ω ^ (n / 2) + 1) = 0 := by
    calc
      (orbit.ω ^ (n / 2) - 1) * (orbit.ω ^ (n / 2) + 1)
          = (orbit.ω ^ (n / 2)) ^ 2 - 1 := by ring
      _ = 0 := by rw [hpow, sub_self]
  rcases mul_eq_zero.mp hfac with h | h
  · exact hne1 (sub_eq_zero.mp h)
  · have hx : orbit.ω ^ (n / 2) = -1 := eq_neg_of_add_eq_zero_left h
    have hneg1 : (-1 : F) = 1 := by
      have h11 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two, hchar]
      calc
        (-1 : F) = -1 + (1 + 1) := by rw [h11, add_zero]
        _ = (-1 + 1) + 1 := by rw [add_assoc]
        _ = 1 := by rw [neg_add_cancel, zero_add]
    exact hne1 (hx.trans hneg1)


open OptimizedComputeRangeCertificate

/-- Local leftover SAT lemmas.  Dummy-T / window arms deleted. -/

private theorem pow_csum_cert64 (env : Env F) (a : ℕ) (ha0 : 0 < a) (ha : a < 2 ^ 64)
    (h2 : (2 : F) ≠ 0)
    (hC : ∀ j, j < 63 →
      env.trace (col0 + j) = if certCBit a j then (1 : F) else 0) :
    (2 : F) ^ certShift a * (csum (F := F)).eval env = (a : F) := by
  set m := certShift a with hm
  have hm63 : m ≤ 63 := certShift_le_63_of_lt_64 a ha
  have htwo (k : ℕ) (hk : k ≤ m) :
      (2 : F) ^ m * twoInv ^ k = (2 : F) ^ (m - k) := by
    have hkpow : (2 : F) ^ k ≠ 0 := pow_ne_zero k h2
    have hn : (2 : F) ^ m = (2 : F) ^ (m - k) * (2 : F) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    calc (2 : F) ^ m * twoInv ^ k
        = (2 : F) ^ m * ((2 : F) ^ k)⁻¹ := by rw [twoInv, inv_pow]
      _ = ((2 : F) ^ (m - k) * (2 : F) ^ k) * ((2 : F) ^ k)⁻¹ := by rw [hn]
      _ = (2 : F) ^ (m - k) * ((2 : F) ^ k * ((2 : F) ^ k)⁻¹) := by ring
      _ = (2 : F) ^ (m - k) := by rw [mul_inv_cancel₀ hkpow, mul_one]
  have hacc : ∀ n, n ≤ 63 →
      (2 : F) ^ m * (csumAcc (F := F) n).eval env =
        (2 : F) ^ m +
          ∑ i ∈ Finset.range (min n m),
            (if a.testBit (m - 1 - i) then (2 : F) ^ (m - 1 - i) else 0) := by
    intro n hn
    induction n with
    | zero => simp [csumAcc, CoeffExpr.eval]
    | succ n ih =>
        have ihn := ih (Nat.le_of_succ_le hn)
        simp only [csumAcc, CoeffExpr.eval, colC, bcur]
        have hc := hC n (by omega)
        by_cases hnm : n < m
        · have hbit : certCBit a n = a.testBit (m - 1 - n) := by
            have hlt : n < certShift a := by simpa [hm] using hnm
            simp [certCBit, hlt, hm]
          rw [hc, hbit]
          have hadd := htwo (n + 1) (by omega)
          have hexp : m - (n + 1) = m - 1 - n := by omega
          calc (2 : F) ^ m *
                ((csumAcc (F := F) n).eval env +
                  (if a.testBit (m - 1 - n) then (1 : F) else 0) * twoInv ^ (n + 1))
              = (2 : F) ^ m * (csumAcc (F := F) n).eval env +
                  (if a.testBit (m - 1 - n) then (1 : F) else 0) *
                    ((2 : F) ^ m * twoInv ^ (n + 1)) := by ring
            _ = (2 : F) ^ m +
                  ∑ i ∈ Finset.range (min n m),
                    (if a.testBit (m - 1 - i) then (2 : F) ^ (m - 1 - i) else 0) +
                  (if a.testBit (m - 1 - n) then (2 : F) ^ (m - 1 - n) else 0) := by
                    rw [ihn, hadd, hexp]
                    by_cases hb : a.testBit (m - 1 - n) <;> simp [hb]
            _ = (2 : F) ^ m +
                  ∑ i ∈ Finset.range (min (n + 1) m),
                    (if a.testBit (m - 1 - i) then (2 : F) ^ (m - 1 - i) else 0) := by
                  have hmin : min n m = n := min_eq_left (Nat.le_of_lt hnm)
                  have hmin' : min (n + 1) m = n + 1 := min_eq_left hnm
                  rw [hmin, hmin', Finset.sum_range_succ]
                  ring
        · have hge : m ≤ n := by omega
          have hc0 : certCBit a n = false := by
            have hge' : ¬ n < certShift a := by simpa [hm] using hnm
            simp [certCBit, hge']
          rw [hc, hc0]
          have hmin : min n m = m := min_eq_right hge
          have hmin' : min (n + 1) m = m := min_eq_right (Nat.le_trans hge (Nat.le_succ n))
          simp [ihn, hmin, hmin']
  have h63 := hacc 63 (by omega)
  have hmin : min 63 m = m := min_eq_right hm63
  rw [hmin] at h63
  have hreidx :
      ∑ i ∈ Finset.range m, (if a.testBit (m - 1 - i) then (2 : F) ^ (m - 1 - i) else 0) =
        ∑ i ∈ Finset.range m, (if a.testBit i then (2 : F) ^ i else 0) := by
    refine Finset.sum_nbij' (fun i => m - 1 - i) (fun j => m - 1 - j) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      omega
    · intro i hi
      rfl
  have hcast :
      (2 : F) ^ m + ∑ i ∈ Finset.range m, (if a.testBit i then (2 : F) ^ i else 0) = (a : F) := by
    have hnat := nat_eq_certBits a ha0
    rw [← hm] at hnat
    conv_rhs => rw [hnat]
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_sum]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    by_cases hb : a.testBit i <;> simp [hb, Nat.cast_pow]
  simpa [csum, hreidx, hcast] using h63


private theorem leftoverTop_mul_sub (m : ℕ) :
    leftoverBitMatchedTop (F := F) m *
      (leftoverBitMatchedTop (F := F) m - 1) = 0 := by
  unfold leftoverBitMatchedTop
  split_ifs <;> simp

private theorem leftoverHelper_eq_top (m : ℕ) :
    leftoverHelperMask (F := F) m = leftoverBitMatchedTop (F := F) m := by
  simp [leftoverHelperMask, leftoverBitMatchedTop]

private theorem certShift_le_nMinus1 {a p : ℕ}
    (hap : a < p) : certShift a ≤ Nat.size p - 1 := by
  have := Nat.size_le_size (Nat.le_of_lt hap)
  simp only [certShift]
  omega

private theorem leftoverGt_unsat_of_width {a : ℕ}
    (hwidth : FormRWidth F) (h64 : a < 2 ^ 64) (hap : a < ringChar F) :
    ¬ leftoverGtTop (F := F) (certShift a) := by
  intro hgt
  have hm64 : certShift a < 64 :=
    Nat.lt_succ_of_le (certShift_le_63_of_lt_64 a h64)
  have hchar : ringChar F ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt hap)
  have hn : 1 ≤ formRN F :=
    Nat.one_le_of_lt (Nat.size_pos.mpr (Nat.pos_of_ne_zero hchar))
  have hleN : formRN F ≤ 64 := hwidth.1
  have hN : nMinus1Low F = formRN F - 1 :=
    Nat.mod_eq_of_lt (by omega)
  have hle : certShift a ≤ formRN F - 1 :=
    certShift_le_nMinus1 (p := ringChar F) hap
  have hexp : leftoverHornerExp (F := F) (certShift a) = certShift a :=
    leftoverHornerExp_of_lt (F := F) hm64
  have : nMinus1Low F < leftoverHornerExp (F := F) (certShift a) := hgt.2
  omega

private theorem nMinus1Low_ne_zero_of_width (hwidth : FormRWidth F) :
    nMinus1Low F ≠ 0 := by
  have hle : formRN F ≤ 64 := hwidth.1
  have hpos : 0 < formRN F := hwidth.2.1
  simp only [formRN] at hle hpos
  have hN : nMinus1Low F = Nat.size (ringChar F) - 1 := by
    simp only [nMinus1Low, formRN]
    exact Nat.mod_eq_of_lt (by omega)
  intro hz
  have hsz : Nat.size (ringChar F) = 1 := by omega
  have hr1 : ringChar F = 1 := by
    revert hsz
    cases ringChar F with
    | zero =>
        intro hsz
        simp at hsz
    | succ n =>
        cases n with
        | zero => intro; rfl
        | succ n =>
            intro hsz
            have hge : 2 ≤ Nat.size (n.succ.succ) :=
              le_trans (by decide : 2 ≤ Nat.size 2)
                (Nat.size_le_size (Nat.le_add_left 2 n))
            rw [hsz] at hge
            exact (Nat.not_succ_le_self 1 hge).elim
  have : (1 : F) = 0 := by
    simpa using (CharP.cast_eq_zero_iff F (ringChar F) 1).mpr (by simp [hr1])
  exact one_ne_zero this

private theorem leftoverMatch_shift_eq {a : ℕ}
    (hwidth : FormRWidth F) (h64 : a < 2 ^ 64) (_hap : a < ringChar F)
    (hchar : ringChar F ≠ 0)
    (hm : leftoverMatch (F := F) (certShift a)) :
    certShift a = formRN F - 1 := by
  have hm64 : certShift a < 64 :=
    Nat.lt_succ_of_le (certShift_le_63_of_lt_64 a h64)
  exact leftoverMatch_eq_nMinus1_of_le64 (F := F) hchar hm hm64
    (show formRN F ≤ 64 from hwidth.1)

private theorem leftoverTop_eq_one_of_ne_zero {m : ℕ}
    (hz : leftoverBitMatchedTop (F := F) m ≠ 0) :
    leftoverBitMatchedTop (F := F) m = 1 := by
  have hmul := leftoverTop_mul_sub (F := F) m
  rcases mul_eq_zero.mp hmul with h0 | hs
  · exact absurd h0 hz
  · exact sub_eq_zero.mp hs

private theorem pPin_eval_of_matched
    (env : Env F) (m : ℕ)
    (hM : ∀ k, k < 6 →
      env.trace (col0 + 63 + k) =
        bit01 ((rangeShiftExp (F := F) m).testBit k))
    (hP : env.trace (col0 + 71) = matchedP (F := F) (rangeShiftExp (F := F) m)) :
    (pPin (F := F)).eval env = 0 := by
  have hlm (k : ℕ) (_hk : k < 6) :
      (lm (F := F) k).eval env = matchedLm (F := F) (rangeShiftExp (F := F) m) k := by
    rw [lm_eval env k, hM k _hk]
    unfold matchedLm
    split_ifs <;> rfl
  change env.trace (col0 + 71) - ((lm (F := F) 5).eval env *
      (lm (F := F) 4).eval env * (lm (F := F) 3).eval env) = 0
  rw [hP, hlm 5 (by decide), hlm 4 (by decide), hlm 3 (by decide)]
  simp [matchedP]

private theorem topPin_eval_of_fill (env : Env F) (m : ℕ) (hm : m ≤ nMinus1Low F)
    (hM : ∀ k, k < 6 →
      env.trace (col0 + 63 + k) = bit01 ((rangeShiftExp (F := F) m).testBit k))
    (hP : env.trace (col0 + 71) = matchedP (F := F) (rangeShiftExp (F := F) m))
    (hTop : env.trace (col0 + 72) = leftoverBitMatchedTop (F := F) m) :
    (topPin (F := F)).eval env = 0 := by
  have hN : nMinus1Low F < 64 := Nat.mod_lt _ (by decide)
  have hm64 : m < 64 := lt_of_le_of_lt hm hN
  have he : rangeShiftExp (F := F) m = m := by
    rw [rangeShiftExp_of_lt64 (F := F) hm64, leftoverHornerExp_of_lt (F := F) hm64]
  rw [he] at hM hP
  have hlm : ∀ k, k < 6 → (lm (F := F) k).eval env = matchedLm F m k := by
    intro k hk; rw [lm_eval, hM k hk]; unfold matchedLm; split_ifs <;> rfl
  rw [topPin_eval, hlm 2 (by decide), hlm 1 (by decide), hlm 0 (by decide), hP, hTop]
  rcases Nat.lt_or_eq_of_le hm with hlt | heq
  · have hne : ¬ leftoverMatch (F := F) m := fun h =>
      by have := (leftoverMatch_of_lt (F := F) hm64).mp h; omega
    have hng : ¬ leftoverGtTop (F := F) m := fun h => by
      have := h.2; rw [leftoverHornerExp_of_lt (F := F) hm64] at this; omega
    have h0 : matchedTop F m = 0 := matchedTop_eq_zero_of_ne m fun hall => by
      have : m = nMinus1Low F := eq_of_low6_testBit hm64 hN fun k hk => by
        rw [hall k hk, nMinus1Low_testBit k hk]
      omega
    rw [leftoverBitMatchedTop_of_lt (F := F) hne hng hm64]
    unfold matchedTop at h0; rw [h0]; ring
  · subst heq
    rw [leftoverBitMatchedTop_nMinus1]
    have h1 := matchedTop_nMinus1 (F := F)
    unfold matchedTop at h1; rw [h1]; ring

private theorem fill_shift_le_u1 (leaf : Option F) (hw : FormRWidth F)
    (hleaf : ∀ L, leaf = some L → ∃ a : ℕ, 0 < a ∧ a < ringChar F ∧ (a : F) = L) :
    axisCertM (axisNat leaf) ≤ nMinus1Low F := by
  have hN : nMinus1Low F = formRN F - 1 := Nat.mod_eq_of_lt (by have := hw.1; omega)
  rw [hN]
  cases leaf with
  | none => simp [axisCertM, axisNat_none, certShift]
  | some L =>
      obtain ⟨a, ha0, hap, haL⟩ := hleaf L rfl
      have hmem := axisNat_of_mem L ha0 haL
      have hsz : Nat.size (axisNat (some L)) ≤ Nat.size (ringChar F) :=
        Nat.size_le_size (le_trans hmem.2.1 (le_of_lt hap))
      simp only [axisCertM, certShift, formRN]
      omega

private theorem helperPinAt_eval_of_leftover
    (env : Env F) (a : ℕ) (k : ℕ) (hk : k < 21)
    (hC : ∀ j, j < 63 → env.trace (col0 + j) = bit01 (certCBit a j))
    (hE : ∀ t, t < 21 →
      env.trace (col0 + 73 + t) =
        leftoverHelperMask (F := F) (certShift a) * certEqRun a (3 * (t + 1)))
    (hTop : env.trace (col0 + 72) = leftoverBitMatchedTop (F := F) (certShift a))
    (htr : env.trace (col0 + 73 + k) =
      leftoverHelperMask (F := F) (certShift a) * certEqRun a (3 * (k + 1))) :
    (helperPinAt (F := F) k).eval env = 0 := by
  have hmask : leftoverHelperMask (F := F) (certShift a) =
      leftoverBitMatchedTop (F := F) (certShift a) := leftoverHelper_eq_top _
  by_cases hz : leftoverBitMatchedTop (F := F) (certShift a) = 0
  · have hE0 : ∀ t, t < 21 → env.trace (col0 + 73 + t) = 0 := by
      intro t ht
      rw [hE t ht, hmask, hz, zero_mul]
    exact helperPinAt_eval_of_top0 env (hTop.trans hz) hE0 k hk
  · have h1 : leftoverBitMatchedTop (F := F) (certShift a) = 1 :=
      leftoverTop_eq_one_of_ne_zero hz
    have hE1 : ∀ t, t < 21 → env.trace (col0 + 73 + t) = certEqRun a (3 * (t + 1)) := by
      intro t ht
      rw [hE t ht, hmask, h1, one_mul]
    exact helperPinAt_eval_of_certRun env a (hTop.trans h1) hC hE1 k hk

private theorem comparisonGate_eval_of_leftover
    (env : Env F) (a : ℕ)
    (hC : ∀ j, j < 63 → env.trace (col0 + j) = bit01 (certCBit a j))
    (hE : ∀ k, k < 21 →
      env.trace (col0 + 73 + k) =
        leftoverHelperMask (F := F) (certShift a) * certEqRun a (3 * (k + 1)))
    (hTop : env.trace (col0 + 72) = leftoverBitMatchedTop (F := F) (certShift a))
    (hwidth : FormRWidth F) (h64 : a < 2 ^ 64) (hap : a < ringChar F)
    (ha0 : 0 < a) (hchar : ringChar F ≠ 0) :
    (comparisonGate (F := F)).eval env = 0 := by
  have hmask : leftoverHelperMask (F := F) (certShift a) =
      leftoverBitMatchedTop (F := F) (certShift a) := leftoverHelper_eq_top _
  by_cases hz : leftoverBitMatchedTop (F := F) (certShift a) = 0
  · have hE0 : ∀ k, k < 21 → env.trace (col0 + 73 + k) = 0 := by
      intro k hk
      rw [hE k hk, hmask, hz, zero_mul]
    exact comparisonGate_eval_of_top0 env (hTop.trans hz) hE0
  · have h1 : leftoverBitMatchedTop (F := F) (certShift a) = 1 :=
      leftoverTop_eq_one_of_ne_zero hz
    have hgt := leftoverGt_unsat_of_width (F := F) hwidth h64 hap
    have hm64 : certShift a < 64 :=
      Nat.lt_succ_of_le (certShift_le_63_of_lt_64 a h64)
    have hmatch : leftoverMatch (F := F) (certShift a) := by
      by_cases hA : leftoverMatch (F := F) (certShift a)
      · exact hA
      · by_cases hB : leftoverGtTop (F := F) (certShift a)
        · exact (hgt hB).elim
        · exact (zero_ne_one
            ((leftoverBitMatchedTop_of_lt (F := F) hA hB hm64).symm.trans h1)).elim
    have hm : certShift a = formRN F - 1 :=
      leftoverMatch_shift_eq (F := F) hwidth h64 hap hchar hmatch
    have hlt : certLt (F := F) a 63 = 1 :=
      certLt_one_of_window (F := F) a hchar hwidth.1 hm ha0 hap
    have hE1 : ∀ k, k < 21 → env.trace (col0 + 73 + k) = certEqRun a (3 * (k + 1)) := by
      intro k hk
      rw [hE k hk, hmask, h1, one_mul]
    exact comparisonGate_eval_of_certRun env a (hTop.trans h1) hC hE1 hlt

private theorem rangeGate_eval_of_leftover
    (env : Env F) (m : ℕ)
    (hM : ∀ k, k < 6 →
      env.trace (col0 + 63 + k) =
        bit01 ((rangeShiftExp (F := F) m).testBit k))
    (hP : env.trace (col0 + 71) = matchedP (F := F) (rangeShiftExp (F := F) m))
    (hTop : env.trace (col0 + 72) = leftoverBitMatchedTop (F := F) m)
    (hm64 : m < 64) :
    (rangeGate (F := F)).eval env = 0 := by
  have hN : nMinus1Low F < 64 := Nat.mod_lt _ (by decide)
  have hexp : leftoverHornerExp (F := F) m = m := leftoverHornerExp_of_lt (F := F) hm64
  by_cases hz : leftoverBitMatchedTop (F := F) m = 0
  · have hne : ¬ leftoverMatch (F := F) m := by
      intro hm
      exact zero_ne_one (hz.symm.trans (leftoverBitMatchedTop_of_match (F := F) hm))
    have hng : ¬ leftoverGtTop (F := F) m := by
      intro hg
      exact zero_ne_one (hz.symm.trans (leftoverBitMatchedTop_of_gt (F := F) hne hg))
    have hlt : m < nMinus1Low F := by
      have : nMinus1Low F = m ∨ nMinus1Low F < m ∨ m < nMinus1Low F := by omega
      rcases this with hEq | hGt | hLt
      · exact (hne ((leftoverMatch_of_lt (F := F) hm64).mpr hEq)).elim
      · have : leftoverGtTop (F := F) m := ⟨by omega, by simpa [hexp] using hGt⟩
        exact (hng this).elim
      · exact hLt
    have he : rangeShiftExp (F := F) m = m := by
      rw [rangeShiftExp_of_lt64 (F := F) hm64, hexp]
    have hM' : ∀ k, k < 6 →
        env.trace (col0 + 63 + k) = bit01 (m.testBit k) := by
      intro k hk
      simpa [he] using hM k hk
    have hP' : env.trace (col0 + 71) = matchedP (F := F) m := by
      simpa [he] using hP
    exact rangeGate_eval_of_lt env m hm64 hN hlt hM' hP' (hTop.trans hz)
  · have hnarrow : ¬ (m < 64 ∧ leftoverHornerExp (F := F) m % 64 < nMinus1Low F) := by
      intro ⟨_, hsnap⟩
      have : m < nMinus1Low F := by
        simpa [hexp, Nat.mod_eq_of_lt hm64] using hsnap
      have hne : ¬ leftoverMatch (F := F) m := by
        intro hm
        have hEq : nMinus1Low F = m := (leftoverMatch_of_lt (F := F) hm64).mp hm
        omega
      have hng : ¬ leftoverGtTop (F := F) m := by
        intro hg
        have : nMinus1Low F < m := by simpa [leftoverGtTop, hexp] using hg.2
        omega
      exact hz (leftoverBitMatchedTop_of_lt (F := F) hne hng hm64)
    have h1 : leftoverBitMatchedTop (F := F) m = 1 :=
      leftoverTop_eq_one_of_ne_zero hz
    exact rangeGate_eval_of_rangeShift env m hM hP (hTop.trans h1) hnarrow

private theorem formR_pre_col
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (i : Fin R.problem.cfg.compRows) (j : ℕ) (hj : j < 202)
    (hpre : j < 13 ∨ (13 ≤ j ∧ (j - 13) / 3 < 58)) :
    (envOfTrace (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal).trace j =
      (if hj13 : j < 13 then
        finalBaseCell A hn i ⟨j, hj13⟩
      else if hrole : (j - 13) / 3 < 58 then
        coord b (coreExtensionValue (encodedRowAt A i) ⟨(j - 13) / 3, hrole⟩)
          ⟨(j - 13) % 3, Nat.mod_lt _ (by decide : 0 < 3)⟩
      else 0) := by
  have hj302 : j < 303 := Nat.lt_trans hj (by decide)
  have h := correctedCanonicalFinalTrace_eval_preFormR (A := A) hn nodes hnodes
    b chalVal pubVal orbit i ⟨j, hj302⟩ hj
  have hres : ¬ (13 ≤ j ∧ (j - 13) / 3 < 60 ∧ 58 ≤ (j - 13) / 3) := by
    rcases hpre with hj13 | ⟨hj13, hrole⟩
    · omega
    · omega
  simp only [envOfTrace, dif_pos hj302] at h ⊢
  rw [h, dif_neg hres]
  simp [preliminaryCell, hj]
  rcases hpre with hj13 | ⟨hj13, hrole⟩
  · simp [hj13, finalBaseCell]
  · have hn13 : ¬ j < 13 := Nat.not_lt.mpr hj13
    simp [hn13, hrole]

private theorem encodedRowAt_base_encode
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) :
    (encodedRowAt A i).base =
      OptimizedComputeCodec.encodeBase (F := F)
        (decodeState (encodedRowAt A i).base) := by
  simp [encodedRowAt, sampledEncode]
  rw [OptimizedComputeCodec.decodeState_encodeBase]

private theorem axisEquation_eval_of_leftover
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hax : FormRAxisBound A b)
    (hwidth : FormRWidth F)
    (i : Fin R.problem.cfg.compRows)
    (envF : Env F)
    (henv : envF = envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal)
    (hC : ∀ j, j < 63 → envF.trace (col0 + j) = bit01 (certCBit (axisNat (axisLeafCoord A b i)) j))
    (hT : envF.trace (col0 + 70) =
      powBits (2 : F) (rangeShiftExp (F := F) (axisCertM (axisNat (axisLeafCoord A b i)))) 6)
    (h2 : (2 : F) ≠ 0) :
    (axisEquation (F := F)).eval envF = 0 := by
  have hcol := fun j hj hpre =>
    formR_pre_col (A := A) hn nodes hnodes b chalVal pubVal orbit i j hj hpre
  have h0 : envF.trace 0 = (encodedRowAt A i).base (.inl ⟨0, by decide⟩) := by
    rw [henv, hcol 0 (by decide) (Or.inl (by decide))]
    simp [finalBaseCell]
  have h9 : envF.trace 9 = (encodedRowAt A i).base (.inl ⟨9, by decide⟩) := by
    rw [henv, hcol 9 (by decide) (Or.inl (by decide))]
    simp [finalBaseCell]
  have h136 : envF.trace 136 =
      coord b (coreExtensionValue (encodedRowAt A i) ⟨41, by decide⟩) 0 := by
    rw [henv, hcol 136 (by decide) (Or.inr ⟨by decide, by decide⟩)]
    simp
  have h145 : envF.trace 145 =
      coord b (coreExtensionValue (encodedRowAt A i) ⟨44, by decide⟩) 0 := by
    rw [henv, hcol 145 (by decide) (Or.inr ⟨by decide, by decide⟩)]
    simp
  cases hst : decodeState (encodedRowAt A i).base with
  | s0 =>
      have hL : axisLeafCoord A b i =
          some (coord b (coreExtensionValue (encodedRowAt A i) ⟨41, by decide⟩) 0) := by
        simp [axisLeafCoord, hst]
      obtain ⟨a, ha0, hap, h64, he, -⟩ := hax i _ hL
      set L := coord b (coreExtensionValue (encodedRowAt A i) ⟨41, by decide⟩) 0
      have hspec : 0 < axisNat (some L) ∧ axisNat (some L) ≤ a ∧
          ((axisNat (some L) : F) = L) :=
        axisNat_of_mem L ha0 he
      have ha'eq : axisNat (axisLeafCoord A b i) = axisNat (some L) := by
        simp [hL]
      set a' := axisNat (axisLeafCoord A b i)
      have ha0' : 0 < a' := by rw [ha'eq]; exact hspec.1
      have he' : (a' : F) = L := by rw [ha'eq]; exact hspec.2.2
      have h64' : a' < 2 ^ 64 := by
        rw [ha'eq]; exact lt_of_le_of_lt hspec.2.1 h64
      have hm64 : certShift a' < 64 :=
        Nat.lt_succ_of_le (certShift_le_63_of_lt_64 a' h64')
      have hTpow : envF.trace (col0 + 70) = (2 : F) ^ certShift a' := by
        have heq : rangeShiftExp (F := F) (axisCertM a') = certShift a' := by
          simp [axisCertM]
          rw [rangeShiftExp_of_lt64 (F := F) hm64, leftoverHornerExp_of_lt (F := F) hm64]
        rw [hT, powBits_six_eq _ _ (by omega), heq]
      have hcsum : (2 : F) ^ certShift a' * (csum (F := F)).eval envF = (a' : F) := by
        have hC' : ∀ j, j < 63 →
            envF.trace (col0 + j) = if certCBit a' j then (1 : F) else 0 := by
          intro j hj
          simpa [bit01] using hC j hj
        exact pow_csum_cert64 envF a' ha0' h64' h2 hC'
      have hsel0 : envF.trace 0 = 1 := by
        rw [h0, encodedRowAt_base_encode (A := A) i, hst]
        simp [OptimizedComputeCodec.encodeBase, OptimizedComputeCodec.stateIndex]
      have hsel9 : envF.trace 9 = 0 := by
        rw [h9, encodedRowAt_base_encode (A := A) i, hst]
        simp [OptimizedComputeCodec.encodeBase, OptimizedComputeCodec.stateIndex]
      refine axisEquation_eval_of_products envF ?_ ?_
      · rw [hsel0, one_mul, h136, hTpow, hcsum, he', sub_self]
      · rw [hsel9, zero_mul]
  | s9 =>
      have hL : axisLeafCoord A b i =
          some (coord b (coreExtensionValue (encodedRowAt A i) ⟨44, by decide⟩) 0) := by
        simp [axisLeafCoord, hst]
      obtain ⟨a, ha0, hap, h64, he, -⟩ := hax i _ hL
      set L := coord b (coreExtensionValue (encodedRowAt A i) ⟨44, by decide⟩) 0
      have hspec : 0 < axisNat (some L) ∧ axisNat (some L) ≤ a ∧
          ((axisNat (some L) : F) = L) :=
        axisNat_of_mem L ha0 he
      have ha'eq : axisNat (axisLeafCoord A b i) = axisNat (some L) := by
        simp [hL]
      set a' := axisNat (axisLeafCoord A b i)
      have ha0' : 0 < a' := by rw [ha'eq]; exact hspec.1
      have he' : (a' : F) = L := by rw [ha'eq]; exact hspec.2.2
      have h64' : a' < 2 ^ 64 := by
        rw [ha'eq]; exact lt_of_le_of_lt hspec.2.1 h64
      have hm64 : certShift a' < 64 :=
        Nat.lt_succ_of_le (certShift_le_63_of_lt_64 a' h64')
      have hTpow : envF.trace (col0 + 70) = (2 : F) ^ certShift a' := by
        have heq : rangeShiftExp (F := F) (axisCertM a') = certShift a' := by
          simp [axisCertM]
          rw [rangeShiftExp_of_lt64 (F := F) hm64, leftoverHornerExp_of_lt (F := F) hm64]
        rw [hT, powBits_six_eq _ _ (by omega), heq]
      have hC' : ∀ j, j < 63 →
          envF.trace (col0 + j) = if certCBit a' j then (1 : F) else 0 := by
        intro j hj
        simpa [bit01] using hC j hj
      have hcsum : (2 : F) ^ certShift a' * (csum (F := F)).eval envF = (a' : F) :=
        pow_csum_cert64 envF a' ha0' h64' h2 hC'
      have hsel0 : envF.trace 0 = 0 := by
        rw [h0, encodedRowAt_base_encode (A := A) i, hst]
        simp [OptimizedComputeCodec.encodeBase, OptimizedComputeCodec.stateIndex]
      have hsel9 : envF.trace 9 = 1 := by
        rw [h9, encodedRowAt_base_encode (A := A) i, hst]
        simp [OptimizedComputeCodec.encodeBase, OptimizedComputeCodec.stateIndex]
      refine axisEquation_eval_of_products envF ?_ ?_
      · rw [hsel0, zero_mul]
      · rw [hsel9, one_mul, h145, hTpow, hcsum, he', sub_self]
  | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | cons =>
      have hsel0 : envF.trace 0 = 0 := by
        rw [h0, encodedRowAt_base_encode (A := A) i, hst]
        simp [OptimizedComputeCodec.encodeBase, OptimizedComputeCodec.stateIndex]
      have hsel9 : envF.trace 9 = 0 := by
        rw [h9, encodedRowAt_base_encode (A := A) i, hst]
        simp [OptimizedComputeCodec.encodeBase, OptimizedComputeCodec.stateIndex]
      refine axisEquation_eval_of_products envF ?_ ?_
      · rw [hsel0, zero_mul]
      · rw [hsel9, zero_mul]

set_option maxHeartbeats 4000000 in
private theorem comparisonGate_eval_of_axisFill
    (envF : Env F) (leaf : Option F)
    (hC : ∀ j, j < 63 → envF.trace (col0 + j) = formROff leaf j)
    (hE : ∀ k, k < 21 → envF.trace (col0 + 73 + k) = formROff leaf (73 + k))
    (hTop : envF.trace (col0 + 72) = formROff leaf 72)
    (haxL : ∀ L, leaf = some L →
      ∃ a : ℕ, 0 < a ∧ a < ringChar F ∧ a < 2 ^ 64 ∧ (a : F) = L)
    (hwidth : FormRWidth F) :
    (comparisonGate (F := F)).eval envF = 0 := by
  cases hleaf : leaf with
  | none =>
      have hng : ¬ leftoverGtTop (F := F) 0 := by
        simp [leftoverGtTop, leftoverHornerExp]
      by_cases hne : leftoverMatch (F := F) 0
      · have hN : nMinus1Low F = 0 :=
          (leftoverMatch_of_lt (F := F) (by decide)).mp hne
        exact (nMinus1Low_ne_zero_of_width hwidth hN).elim
      · have hTop0 : leftoverBitMatchedTop (F := F) 0 = 0 :=
          leftoverBitMatchedTop_of_lt (F := F) hne hng (by decide)
        have hE0 : ∀ k, k < 21 → envF.trace (col0 + 73 + k) = 0 := by
          intro k hk
          have := hE k hk
          rw [hleaf, formROff_helper none k hk] at this
          simp only [axisNat_none, leftoverHelper_eq_top] at this
          have hm0 : axisCertM 0 = 0 := by
            simp [axisCertM, certShift, Nat.size_zero]
          rw [hm0, hTop0, zero_mul] at this
          exact this
        exact comparisonGate_eval_of_top0 envF
          (by
            have := hTop.trans (formROff_top leaf)
            simpa [hleaf, axisNat_none, axisCertM, certShift, Nat.size_zero, hTop0] using this)
          hE0
  | some L =>
      obtain ⟨a, ha0, hap, h64, he⟩ := haxL L hleaf
      have hspec := axisNat_of_mem L ha0 he
      set a' := axisNat (some L)
      have hchar : ringChar F ≠ 0 := Nat.ne_of_gt (lt_trans ha0 hap)
      refine comparisonGate_eval_of_leftover envF a' ?_ ?_ ?_ hwidth
        (lt_of_le_of_lt hspec.2.1 h64) (lt_of_le_of_lt hspec.2.1 hap) hspec.1 hchar
      · intro j hj
        have := hC j hj
        rw [formROff_c leaf j hj, hleaf] at this
        exact this
      · intro k hk
        have := hE k hk
        rw [formROff_helper leaf k hk, hleaf] at this
        simpa [axisCertM] using this
      · have := hTop.trans (formROff_top leaf)
        simpa [hleaf, axisCertM] using this

set_option maxHeartbeats 4000000
private theorem rangeGate_eval_of_axisFill
    (envF : Env F) (leaf : Option F)
    (hM : ∀ k, k < 6 → envF.trace (col0 + 63 + k) = formROff leaf (63 + k))
    (hP : envF.trace (col0 + 71) = formROff leaf 71)
    (hTop : envF.trace (col0 + 72) = formROff leaf 72)
    (haxL : ∀ L, leaf = some L →
      ∃ a : ℕ, 0 < a ∧ a < ringChar F ∧ a < 2 ^ 64 ∧ (a : F) = L) :
    (rangeGate (F := F)).eval envF = 0 := by
  have hm64 : axisCertM (axisNat leaf) < 64 := by
    cases hleaf : leaf with
    | none =>
        simp [hleaf, axisNat_none, axisCertM, certShift, Nat.size_zero]
    | some L =>
        obtain ⟨a, ha0, hap, h64, he⟩ := haxL L hleaf
        have h64' := axisNat_lt_64 L ha0 h64 he
        simpa [hleaf, axisCertM] using
          Nat.lt_succ_of_le (certShift_le_63_of_lt_64 _ h64')
  refine rangeGate_eval_of_leftover envF (axisCertM (axisNat leaf)) ?_ ?_ ?_ hm64
  · intro k hk
    have := hM k hk
    rw [formROff_m leaf k hk] at this
    exact this
  · exact hP.trans (formROff_p leaf)
  · exact hTop.trans (formROff_top leaf)

set_option maxHeartbeats 8000000

/-- Form R 99: leftover certificate of the natural axis, or the zero certificate.
    SAT-facing fragment of `RunAxesBoundedBy` is `FormRAxisBound`
    (`A` stores no formula noun). -/
theorem canonical_formR99
    [FiniteDimensional F K] [DecidableEq F]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hax : FormRAxisBound A b)
    (hbasis : FormRBasis b)
    (hwidth : FormRWidth F)
    (i : Fin R.problem.cfg.compRows)
    (g : CoeffExpr F)
    (hg : g ∈ OptimizedComputeRangeCertificate.formRCertificateGates) :
    g.eval
      (envOfTrace (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal) = 0 := by
  let envF := envOfTrace
    (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
    orbit.ω (nodes i) chalVal pubVal
  have ht := fun off hoff =>
    formR_trace A hn nodes hnodes b chalVal pubVal orbit i off hoff
  have hC : ∀ j, j < 63 →
      envF.trace (202 + j) = formROff (axisLeafCoord A b i) j := by
    intro j hj
    have h := ht j (by omega)
    rw [dif_neg (by omega : ¬ (94 ≤ j ∧ j < 97)), dif_neg (by omega : ¬ 97 ≤ j)] at h
    exact h
  have hM : ∀ k, k < 6 →
      envF.trace (202 + 63 + k) = formROff (axisLeafCoord A b i) (63 + k) := by
    intro k hk
    have h := ht (63 + k) (by omega)
    rw [dif_neg (by omega : ¬ (94 ≤ 63 + k ∧ 63 + k < 97)), dif_neg (by omega : ¬ 97 ≤ 63 + k)]
      at h
    simpa [show 202 + (63 + k) = 202 + 63 + k by omega] using h
  have hH : envF.trace 271 = formROff (axisLeafCoord A b i) 69 := by
    simpa using ht 69 (by omega)
  have hT : envF.trace 272 = formROff (axisLeafCoord A b i) 70 := by
    simpa using ht 70 (by omega)
  have hP : envF.trace 273 = formROff (axisLeafCoord A b i) 71 := by
    simpa using ht 71 (by omega)
  have hTop : envF.trace 274 = formROff (axisLeafCoord A b i) 72 := by
    simpa using ht 72 (by omega)
  have hE : ∀ k, k < 21 →
      envF.trace (202 + 73 + k) = formROff (axisLeafCoord A b i) (73 + k) := by
    intro k hk
    have h := ht (73 + k) (by omega)
    rw [dif_neg (by omega : ¬ (94 ≤ 73 + k ∧ 73 + k < 97)), dif_neg (by omega : ¬ 97 ≤ 73 + k)]
      at h
    simpa [show 202 + (73 + k) = 202 + 73 + k by omega] using h
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_strict_orbit orbit
  -- Boolean, power, pin, helper, and named gates of the leftover fill.
  -- Window / dummy-T arms deleted (they contained the false goals).
  simp only [OptimizedComputeRangeCertificate.formRCertificateGates] at hg
  rcases List.mem_append.mp hg with h | hnamed
  · rcases List.mem_append.mp h with h | hhelp
    · rcases List.mem_append.mp h with h | hpins
      · rcases List.mem_append.mp h with hbool | hpow
        · simp only [OptimizedComputeRangeCertificate.booleanGates,
            List.mem_append, List.mem_map] at hbool
          rcases hbool with ⟨j, hj, rfl⟩ | ⟨k, hk, rfl⟩
          · have hj' := List.mem_range.mp hj
            have htr := hC j hj'
            rw [formROff_c (axisLeafCoord A b i) j hj'] at htr
            have hbb := OptimizedComputeRangeCertificate.bit01_mul_sub (F := F)
              (OptimizedComputeRangeCertificate.certCBit (axisNat (axisLeafCoord A b i)) j)
            -- C2: columns `j + 1 > n − 1` are pinned `0`; the honest shift is `≤ n − 1`.
            have hsh := fill_shift_le_u1 (axisLeafCoord A b i) hwidth
              (fun L hL => let ⟨a, h0, h1, _, h3, _⟩ := hax i L hL; ⟨a, h0, h1, h3⟩)
            have hN : nMinus1Low F = formRN F - 1 :=
              Nat.mod_eq_of_lt (by have := hwidth.1; omega)
            split_ifs with hjn
            · have hcf : OptimizedComputeRangeCertificate.certCBit
                  (axisNat (axisLeafCoord A b i)) j = false := by
                unfold OptimizedComputeRangeCertificate.certCBit
                rw [if_neg (by simp only [axisCertM] at hsh; omega)]
              simp [OptimizedComputeRangeCertificate.colC,
                OptimizedComputeRangeCertificate.col0,
                OptimizedComputeRangeCertificate.bcur, CoeffExpr.eval, envF, htr, hcf]
            simp [OptimizedComputeRangeCertificate.bbool,
              OptimizedComputeRangeCertificate.colC,
              OptimizedComputeRangeCertificate.col0,
              OptimizedComputeRangeCertificate.bcur, CoeffExpr.eval, envF, htr, hbb]
          · have hk' := List.mem_range.mp hk
            have htr := hM k hk'
            rw [formROff_m (axisLeafCoord A b i) k hk'] at htr
            have hbb := OptimizedComputeRangeCertificate.bit01_mul_sub (F := F)
              ((OptimizedComputeRangeCertificate.rangeShiftExp (F := F)
                (axisCertM (axisNat (axisLeafCoord A b i)))).testBit k)
            have hidx : envF.trace (202 + (63 + k)) = envF.trace (202 + 63 + k) :=
              congrArg envF.trace (by omega)
            simp [OptimizedComputeRangeCertificate.bbool,
              OptimizedComputeRangeCertificate.colM,
              OptimizedComputeRangeCertificate.col0,
              OptimizedComputeRangeCertificate.bcur, CoeffExpr.eval, envF,
              hidx, htr, hbb]
        · -- power pins: leftover Horner powers of the axis shift
          let leaf := axisLeafCoord A b i
          let mFill := OptimizedComputeRangeCertificate.rangeShiftExp (F := F)
            (axisCertM (axisNat leaf))
          have hMk : ∀ k, k < 6 →
              envF.trace (202 + 63 + k) = OptimizedComputeRangeCertificate.bit01
                (mFill.testBit k) := by
            intro k hk
            have htr := hM k hk
            rw [formROff_m leaf k hk] at htr
            exact htr
          have hfac (k : ℕ) (hk : k < 6) (x : F) :
              (1 : F) + envF.trace (202 + 63 + k) * (x - 1) =
                if mFill.testBit k then x else 1 := by
            rw [hMk k hk, OptimizedComputeRangeCertificate.bit_switch]
          have hchal : envF.chal = chalVal := rfl
          simp only [envF] at hchal
          simp only [OptimizedComputeRangeCertificate.powerPins,
            List.mem_cons, List.not_mem_nil, or_false] at hpow
          rcases hpow with h | h
          · subst g
            have hf0 := hfac 0 (by decide) ((2 : F) ^ 2 ^ 0)
            have hf1 := hfac 1 (by decide) ((2 : F) ^ 2 ^ 1)
            have hf2 := hfac 2 (by decide) ((2 : F) ^ 2 ^ 2)
            have hHcol : envF.trace 271 = OptimizedComputeRangeCertificate.powBits (2 : F) mFill 3 :=
              (formROff_h leaf ▸ hH)
            simp only [OptimizedComputeRangeCertificate.hPin,
              OptimizedComputeRangeCertificate.factor2,
              OptimizedComputeRangeCertificate.colHbase,
              OptimizedComputeRangeCertificate.colM,
              OptimizedComputeRangeCertificate.col0,
              OptimizedComputeRangeCertificate.bcur, CoeffExpr.eval, envF, hHcol]
            rw [hf0, hf1, hf2, OptimizedComputeRangeCertificate.powBits_three]
            ring
          · subst g
            have hf3 := hfac 3 (by decide) ((2 : F) ^ 2 ^ 3)
            have hf4 := hfac 4 (by decide) ((2 : F) ^ 2 ^ 4)
            have hf5 := hfac 5 (by decide) ((2 : F) ^ 2 ^ 5)
            have hHcol : envF.trace 271 = OptimizedComputeRangeCertificate.powBits (2 : F) mFill 3
                :=
              (formROff_h leaf ▸ hH)
            have hTcol : envF.trace 272 = OptimizedComputeRangeCertificate.powBits (2 : F) mFill 6
                :=
              (formROff_t leaf ▸ hT)
            simp only [OptimizedComputeRangeCertificate.tPin,
              OptimizedComputeRangeCertificate.factor2,
              OptimizedComputeRangeCertificate.colHbase,
              OptimizedComputeRangeCertificate.colTbase,
              OptimizedComputeRangeCertificate.colM,
              OptimizedComputeRangeCertificate.col0,
              OptimizedComputeRangeCertificate.bcur, CoeffExpr.eval, envF, hHcol, hTcol]
            rw [hf3, hf4, hf5, OptimizedComputeRangeCertificate.powBits_high]
            ring
      · -- pPin / topPin
        simp only [OptimizedComputeRangeCertificate.formRPins,
          List.mem_cons, List.not_mem_nil, or_false] at hpins
        rcases hpins with rfl | rfl
        · exact pPin_eval_of_matched envF
            (axisCertM (axisNat (axisLeafCoord A b i)))
            (fun k hk => by
              have := hM k hk
              rw [formROff_m (axisLeafCoord A b i) k hk] at this
              simpa [OptimizedComputeRangeCertificate.col0] using this)
            (by simpa [OptimizedComputeRangeCertificate.col0] using
              hP.trans (formROff_p (axisLeafCoord A b i)))
        · exact topPin_eval_of_fill envF
            (axisCertM (axisNat (axisLeafCoord A b i)))
            (fill_shift_le_u1 _ hwidth
              (fun L hL => let ⟨a, h0, h1, _, h3, _⟩ := hax i L hL; ⟨a, h0, h1, h3⟩))
            (fun k hk => by
              have := hM k hk
              rw [formROff_m (axisLeafCoord A b i) k hk] at this
              simpa [OptimizedComputeRangeCertificate.col0] using this)
            (by simpa [OptimizedComputeRangeCertificate.col0] using
              hP.trans (formROff_p (axisLeafCoord A b i)))
            (by simpa [OptimizedComputeRangeCertificate.col0] using
              hTop.trans (formROff_top (axisLeafCoord A b i)))
    · -- helper pins
      simp only [OptimizedComputeRangeCertificate.helperPins, List.mem_map] at hhelp
      obtain ⟨k, hk, rfl⟩ := hhelp
      have hk' := List.mem_range.mp hk
      have htr := hE k hk'
      rw [formROff_helper (axisLeafCoord A b i) k hk'] at htr
      exact helperPinAt_eval_of_leftover envF (axisNat (axisLeafCoord A b i)) k hk'
        (fun j hj => by
          have := hC j hj
          rw [formROff_c (axisLeafCoord A b i) j hj] at this
          simpa [OptimizedComputeRangeCertificate.col0] using this)
        (fun t ht => by
          have := hE t ht
          rw [formROff_helper (axisLeafCoord A b i) t ht] at this
          simpa [OptimizedComputeRangeCertificate.col0, axisCertM] using this)
        (by simpa [OptimizedComputeRangeCertificate.col0, axisCertM] using
          hTop.trans (formROff_top (axisLeafCoord A b i)))
        (by simpa [OptimizedComputeRangeCertificate.col0, axisCertM] using htr)
  · -- named: comparison, range, axis
    simp only [OptimizedComputeRangeCertificate.formRNamed,
      List.mem_cons, List.not_mem_nil, or_false] at hnamed
    rcases hnamed with rfl | h
    · exact comparisonGate_eval_of_axisFill envF (axisLeafCoord A b i)
        (fun j hj => by simpa [OptimizedComputeRangeCertificate.col0] using hC j hj)
        (fun k hk => by simpa [OptimizedComputeRangeCertificate.col0] using hE k hk)
        (by simpa [OptimizedComputeRangeCertificate.col0] using hTop)
        (fun L hL => let ⟨a, h0, h1, h2, h3, _⟩ := hax i L hL; ⟨a, h0, h1, h2, h3⟩) hwidth
    · rcases h with rfl | rfl
      · exact rangeGate_eval_of_axisFill envF (axisLeafCoord A b i)
          (fun k hk => by simpa [OptimizedComputeRangeCertificate.col0] using hM k hk)
          (by simpa [OptimizedComputeRangeCertificate.col0] using hP)
          (by simpa [OptimizedComputeRangeCertificate.col0] using hTop)
          (fun L hL => let ⟨a, h0, h1, h2, h3, _⟩ := hax i L hL; ⟨a, h0, h1, h2, h3⟩)
      · simpa [envF] using
          axisEquation_eval_of_leftover A hn nodes hnodes b chalVal pubVal orbit
            hax hwidth i envF rfl
            (fun j hj => by
              have := hC j hj
              rw [formROff_c (axisLeafCoord A b i) j hj] at this
              simpa [OptimizedComputeRangeCertificate.col0] using this)
            (by simpa [OptimizedComputeRangeCertificate.col0] using
              hT.trans (formROff_t (axisLeafCoord A b i)))
            h2

/-- The two Form R `𝕂` power pins at the `𝕂` coin `λ` (all three limbs) hold on every
canonical row: the honest `H`, `T` are `λ` to the leftover shift's low / full bits
. -/
theorem canonical_formRLam
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (i : Fin R.problem.cfg.compRows) :
    ∀ t ∈ formRLamPins,
      t.eval (gatherCorrectedFinalTypedEnv b
        (envOfTrace (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal)) = 0 := by
  set env := gatherCorrectedFinalTypedEnv b
    (envOfTrace (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal) with henv
  set leaf := axisLeafCoord A b i
  set lam := formRLamOfChal b chalVal
  set mF := rangeShiftExp (F := F) (axisCertM (axisNat leaf))
  have hv := canonical_gather_certExt_val A hn nodes hnodes b chalVal pubVal orbit i
  have hchal9 : env.chal 9 = lam := by
    simp [henv, gatherCorrectedFinalTypedEnv, envOfTrace, lam, formRLamOfChal]
  have hm : ∀ k (hk : k < 6),
      algebraMap F K (env.certBase ⟨63 + k, by omega⟩) =
        if mF.testBit k then (1 : K) else 0 := by
    intro k hk
    rw [henv, canonical_gather_certBase_val A hn nodes hnodes b chalVal pubVal orbit i,
      show ((⟨63 + k, by omega⟩ : Fin 94) : ℕ) = 63 + k from rfl, formROff_m leaf k hk]
    cases mF.testBit k <;> simp [bit01, mF, leaf]
  have hfac : ∀ k (hk : k < 6),
      (formRLamFactor ⟨k, hk⟩).eval env = if mF.testBit k then lam ^ 2 ^ k else 1 := by
    intro k hk
    simp only [formRLamFactor, CorrectedFinalTypedExpr.eval, hchal9]
    rw [hm k hk]
    split_ifs <;> simp
  intro t ht
  simp only [formRLamPins, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · simp only [formRLamHPin, CorrectedFinalTypedExpr.eval]
    rw [hv.1]
    erw [hfac 0 (by decide), hfac 1 (by decide), hfac 2 (by decide)]
    simp only [formRLamHK, formRLamHNat, OptimizedComputeRangeCertificate.powBits_three]
    ring
  · simp only [formRLamTPin, CorrectedFinalTypedExpr.eval]
    rw [hv.1, hv.2]
    erw [hfac 3 (by decide), hfac 4 (by decide), hfac 5 (by decide)]
    simp only [formRLamHK, formRLamHNat, formRLamTK, formRLamTNat,
      OptimizedComputeRangeCertificate.powBits_high]
    ring

/-! ### The 31st: the exponent carrier `S` on canonical rows -/

/-- The number of requests a state opens is its arity coefficient. -/
theorem activeRequestRecords_length_eq_arityCoeff (pub : ComputeTable.Pub K) :
    (NockVM.activeRequestRecords pub).length =
      arityCoeff (OptimizedComputeCodec.stateIndex pub.state) := by
  cases h : pub.state <;> simp [NockVM.activeRequestRecords, h, arityCoeff,
    OptimizedComputeCodec.stateIndex]

/-- At one-hot state selectors the arity form reads the state's arity coefficient. -/
theorem arityForm_eval_of_onehot (env : Env F) (st : ComputeTable.State)
    (hsel : ∀ c : ℕ, c < 11 →
      env.trace c = if c = (OptimizedComputeCodec.stateIndex st : ℕ) then 1 else 0) :
    (arityForm (F := F)).eval env = ((arityCoeff (OptimizedComputeCodec.stateIndex st) : ℕ) : F) := by
  simp only [arityForm, List.range, List.range.loop, List.foldr, CoeffExpr.eval]
  rw [hsel 0 (by omega), hsel 1 (by omega), hsel 2 (by omega), hsel 3 (by omega),
    hsel 4 (by omega), hsel 5 (by omega), hsel 6 (by omega), hsel 7 (by omega),
    hsel 8 (by omega), hsel 9 (by omega), hsel 10 (by omega)]
  cases st <;> simp [OptimizedComputeCodec.stateIndex, arityCoeff] <;> norm_num

/-- `S(i + 1) = S(i) + arity(i)` for the honest carrier. -/
theorem honestS_succ (i : Fin R.problem.cfg.compRows) :
    OptimizedComputeFinalTrace.honestS R ((i : ℕ) + 1) =
      OptimizedComputeFinalTrace.honestS R i +
        (NockVM.activeRequestRecords (R.problem.exec.computePubAt i)).length := by
  have hi : (i : ℕ) < R.problem.exec.computeRows.length := by
    rw [R.problem.exec.computeRows_length]; exact i.isLt
  simp only [OptimizedComputeFinalTrace.honestS]
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp [ExactExecution.computePubAt, ExactExecution.computeRowAt, List.get_eq_getElem]

/-- **The two carrier gates hold on every canonical row**: `S(0) = 0` and
`S(i+1) = S(i) + arity(i)` off the last row (honest `S = honestS`, the prefix of arities). -/
theorem canonical_expGates
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hstep : ∀ (i : Fin R.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < R.problem.cfg.compRows),
      nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (i : Fin R.problem.cfg.compRows) :
    ∀ g ∈ computeExpGates (F := F),
      g.eval (envOfTrace (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal) = 0 := by
  set envF := envOfTrace (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
    orbit.ω (nodes i) chalVal pubVal with henvF
  have hS : envF.trace 302 = ((OptimizedComputeFinalTrace.honestS R i : ℕ) : F) := by
    simp only [henvF, envOfTrace, dif_pos (show (302 : ℕ) < 303 by omega)]
    exact correctedCanonicalFinalTrace_eval_S A hn nodes hnodes b chalVal pubVal orbit i
  have hbase : ∀ j : Fin 13, envF.trace j = finalBaseCell A hn i j := fun j =>
    correctedCanonicalFinalTrace_base_eval A hn nodes hnodes b chalVal pubVal orbit i j
  have hsel : ∀ c : ℕ, c < 11 → envF.trace c =
      if c = (OptimizedComputeCodec.stateIndex (R.problem.exec.computePubAt i).state : ℕ)
      then 1 else 0 := by
    intro c hc
    have h := hbase ⟨c, by omega⟩
    rw [show ((⟨c, by omega⟩ : Fin 13) : ℕ) = c from rfl] at h
    rw [h]
    have h2 := finalBaseCell_selector A hn i ⟨c, hc⟩
    simp only at h2
    rw [h2]
    simp [Fin.ext_iff]
  intro g hg
  simp only [computeExpGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · simp only [expInitGate, computeExpCol, CoeffExpr.eval, hS]
    have h11 := hbase 11
    simp only [show ((11 : Fin 13) : ℕ) = 11 from rfl] at h11
    rw [h11]
    by_cases hi0 : (i : ℕ) = 0
    · have : OptimizedComputeFinalTrace.honestS R i = 0 := by
        simp [OptimizedComputeFinalTrace.honestS, hi0]
      simp [this]
    · simp [finalBaseCell, hi0]
  · simp only [expStepGate, computeExpCol, CoeffExpr.eval, hS]
    have h12 := hbase 12
    simp only [show ((12 : Fin 13) : ℕ) = 12 from rfl] at h12
    rw [h12]
    by_cases hi : (i : ℕ) + 1 < R.problem.cfg.compRows
    · have hne : i ≠ ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩ := by
        intro h; rw [h] at hi; simp at hi; omega
      have hnext : envF.traceNext 302 =
          ((OptimizedComputeFinalTrace.honestS R ((i : ℕ) + 1) : ℕ) : F) := by
        simp only [henvF, envOfTrace, dif_pos (show (302 : ℕ) < 303 by omega)]
        rw [← hstep i hi]
        rw [correctedCanonicalFinalTrace_eval_S A hn nodes hnodes b chalVal pubVal orbit
          ⟨(i : ℕ) + 1, hi⟩]
      rw [hnext, arityForm_eval_of_onehot envF _ hsel, honestS_succ i,
        activeRequestRecords_length_eq_arityCoeff]
      simp [finalBaseCell, hne]
    · have heq : i = ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩ := by
        apply Fin.ext; simp only; omega
      simp [finalBaseCell, heq]

/-- All seven corrected source buckets hold on every canonical row. -/
theorem canonical_corrected_source_obligations
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hstep : ∀ (i : Fin R.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < R.problem.cfg.compRows),
      nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hchal : ExactFinalChallengeCoordinates b A chalVal)
    (hpub : ExactFinalPublicCoordinates b R hn pubVal)
    (hreq : ExactFinalRequestsCoordinate b A pubVal)
    (hln : ExactFinalLineOrigin R hn)
    (hord : 2 ≤ R.problem.cfg.compRows →
      R.problem.cfg.compRows ≤ orderOf R.computeWalkAlpha)
    (hax : FormRAxisBound A b)
    (hbasis : FormRBasis b)
    (hwidth : FormRWidth F)
    (i : Fin R.problem.cfg.compRows) :
    let envF := envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal
    let env := gatherCorrectedFinalTypedEnv b envF
    CorrectedComputeSourceObligations R.problem.cfg.compRows env envF := by
  dsimp only
  let envF := envOfTrace
    (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
    orbit.ω (nodes i) chalVal pubVal
  let env := gatherCorrectedFinalTypedEnv b envF
  refine
    { base15 := ?_
      extensionCore21 := ?_
      residualAux3 := ?_
      endpointDegreeTwo2 := ?_
      endpointDegreeFour1 := ?_
      selectorEquality2 := ?_
      formR99 := ?_
      formRLam := ?_
      expGates := canonical_expGates A hn nodes hnodes b chalVal pubVal orbit hstep i }
  · simpa [envF] using correctedCanonicalFinalTrace_base15
      A hn nodes hnodes b chalVal pubVal orbit i
  · by_cases hi : (i : ℕ) + 1 < R.problem.cfg.compRows
    · simpa [env, envF] using canonical_extensionCore_nonterminal
        A hA hn nodes hnodes b chalVal pubVal orbit hstep hchal hax hwidth hord i hi
    · let last : Fin R.problem.cfg.compRows :=
        ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
      have hilast : i = last := by
        apply Fin.ext
        simp only [last]
        omega
      simpa [env, envF, hilast, last] using canonical_extensionCore_terminal
        A hA hn nodes hnodes b chalVal pubVal orbit hchal hax hwidth
  · intro j
    by_cases hj : j = 2
    · subst j
      simpa [env, envF, correctedAuxSemanticValue] using canonical_accAfterStep
        A hn nodes hnodes b chalVal pubVal orbit (fun q _ k => hchal q k) i
    · simpa [env, envF] using correctedCanonical_residualAux01
        A hn nodes hnodes b chalVal pubVal orbit i j hj
  · exact (canonical_endpoint_obligations
      A hA hn nodes hnodes b chalVal pubVal orbit (fun k => hchal 6 k) (fun k => hchal 10 k)
      hpub hreq hln i).1
  · exact (canonical_endpoint_obligations
      A hA hn nodes hnodes b chalVal pubVal orbit (fun k => hchal 6 k) (fun k => hchal 10 k)
      hpub hreq hln i).2
  · simpa [envF] using canonical_selectorEquality2
      A hn nodes hnodes b chalVal pubVal orbit hpub i
  · intro g hg
    exact canonical_formR99 A hn nodes hnodes b chalVal pubVal orbit hax hbasis hwidth i g hg
  · exact canonical_formRLam A hn nodes hnodes b chalVal pubVal orbit i

/-- Canonical final satisfaction for the corrected `199/98` production compute RAP. -/
theorem correctedCanonicalFinalTrace_satisfies
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hstep : ∀ (i : Fin R.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < R.problem.cfg.compRows),
      nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hchal : ExactFinalChallengeCoordinates b A chalVal)
    (hpub : ExactFinalPublicCoordinates b R hn pubVal)
    (hreq : ExactFinalRequestsCoordinate b A pubVal)
    (hln : ExactFinalLineOrigin R hn)
    (hord : 2 ≤ R.problem.cfg.compRows →
      R.problem.cfg.compRows ≤ orderOf R.computeWalkAlpha)
    (hax : FormRAxisBound A b)
    (hbasis : FormRBasis b)
    (hwidth : FormRWidth F) :
    RAP.SatisfiesWithPreprocessing
      (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit)
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit) := by
  apply correctedCanonicalFinalTrace_satisfies_of_source
  intro i
  exact canonical_corrected_source_obligations
    A hA hn nodes hnodes b chalVal pubVal orbit hstep hchal hpub hreq hln hord hax hbasis hwidth i

/-- All six corrected source buckets hold for arbitrary verifier-selected challenges `9`, `11`,
and `36`.  Forward completeness uses only vanishing source families; no collision-good premise is
assumed. -/
theorem canonical_corrected_source_obligations_with
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (c : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hstep : ∀ (i : Fin R.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < R.problem.cfg.compRows),
      nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hchal : ExactFinalChallengeCoordinatesWith b A c chalVal)
    (hpub : ExactFinalPublicCoordinates b R hn pubVal)
    (hreq : ExactFinalRequestsCoordinate b A pubVal)
    (hln : ExactFinalLineOrigin R hn)
    (hord : 2 ≤ R.problem.cfg.compRows →
      R.problem.cfg.compRows ≤ orderOf R.computeWalkAlpha)
    (hax : FormRAxisBound A b)
    (hbasis : FormRBasis b)
    (hwidth : FormRWidth F)
    (i : Fin R.problem.cfg.compRows) :
    let envF := envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal
    let env := gatherCorrectedFinalTypedEnv b envF
    CorrectedComputeSourceObligations R.problem.cfg.compRows env envF := by
  dsimp only
  let envF := envOfTrace
    (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
    orbit.ω (nodes i) chalVal pubVal
  let env := gatherCorrectedFinalTypedEnv b envF
  refine
    { base15 := ?_
      extensionCore21 := ?_
      residualAux3 := ?_
      endpointDegreeTwo2 := ?_
      endpointDegreeFour1 := ?_
      selectorEquality2 := ?_
      formR99 := ?_
      formRLam := ?_
      expGates := canonical_expGates A hn nodes hnodes b chalVal pubVal orbit hstep i }
  · simpa [envF] using correctedCanonicalFinalTrace_base15
      A hn nodes hnodes b chalVal pubVal orbit i
  · by_cases hi : (i : ℕ) + 1 < R.problem.cfg.compRows
    · simpa [env, envF] using canonical_extensionCore_nonterminal_with
        A hA c hn nodes hnodes b chalVal pubVal orbit hstep hchal hax hwidth hord i hi
    · let last : Fin R.problem.cfg.compRows :=
        ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
      have hilast : i = last := by
        apply Fin.ext
        simp only [last]
        omega
      simpa [env, envF, hilast, last] using canonical_extensionCore_terminal_with
        A hA c hn nodes hnodes b chalVal pubVal orbit hchal hax hwidth
  · intro j
    by_cases hj : j = 2
    · subst j
      have hchal9 : ∀ q : Fin 12, (q : ℕ) < 9 → ∀ k : Fin 3,
          chalVal (3 * (q : ℕ) + (k : ℕ)) = coord b (exactFinalChallenge A q) k := by
        intro q hq k
        have h := hchal q k
        rwa [show exactFinalChallengeWith A c q = exactFinalChallenge A q by
          fin_cases q <;> simp at hq <;> rfl] at h
      simpa [env, envF, correctedAuxSemanticValue] using canonical_accAfterStep
        A hn nodes hnodes b chalVal pubVal orbit hchal9 i
    · simpa [env, envF] using correctedCanonical_residualAux01
        A hn nodes hnodes b chalVal pubVal orbit i j hj
  · have h6 : ∀ k : Fin 3,
        chalVal (3 * 6 + (k : ℕ)) = coord b (exactFinalChallenge A 6) k := by
      intro k
      simpa [exactFinalChallengeWith] using hchal (6 : Fin 12) k
    have h10 : ∀ k : Fin 3,
        chalVal (3 * 10 + (k : ℕ)) = coord b (exactFinalChallenge A 10) k := by
      intro k
      simpa [exactFinalChallengeWith] using hchal (10 : Fin 12) k
    exact (canonical_endpoint_obligations
      A hA hn nodes hnodes b chalVal pubVal orbit h6 h10 hpub hreq hln i).1
  · have h6 : ∀ k : Fin 3,
        chalVal (3 * 6 + (k : ℕ)) = coord b (exactFinalChallenge A 6) k := by
      intro k
      simpa [exactFinalChallengeWith] using hchal (6 : Fin 12) k
    have h10 : ∀ k : Fin 3,
        chalVal (3 * 10 + (k : ℕ)) = coord b (exactFinalChallenge A 10) k := by
      intro k
      simpa [exactFinalChallengeWith] using hchal (10 : Fin 12) k
    exact (canonical_endpoint_obligations
      A hA hn nodes hnodes b chalVal pubVal orbit h6 h10 hpub hreq hln i).2
  · simpa [envF] using canonical_selectorEquality2
      A hn nodes hnodes b chalVal pubVal orbit hpub i
  · intro g hg
    exact canonical_formR99 A hn nodes hnodes b chalVal pubVal orbit hax hbasis hwidth i g hg
  · exact canonical_formRLam A hn nodes hnodes b chalVal pubVal orbit i

/-- Arbitrary-challenge canonical satisfaction for the physical corrected `199/98` compute RAP. -/
theorem correctedCanonicalFinalTrace_satisfies_with
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (c : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hstep : ∀ (i : Fin R.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < R.problem.cfg.compRows),
      nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hchal : ExactFinalChallengeCoordinatesWith b A c chalVal)
    (hpub : ExactFinalPublicCoordinates b R hn pubVal)
    (hreq : ExactFinalRequestsCoordinate b A pubVal)
    (hln : ExactFinalLineOrigin R hn)
    (hord : 2 ≤ R.problem.cfg.compRows →
      R.problem.cfg.compRows ≤ orderOf R.computeWalkAlpha)
    (hax : FormRAxisBound A b)
    (hbasis : FormRBasis b)
    (hwidth : FormRWidth F) :
    RAP.SatisfiesWithPreprocessing
      (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit)
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit) := by
  apply correctedCanonicalFinalTrace_satisfies_of_source
  intro i
  exact canonical_corrected_source_obligations_with
    A hA c hn nodes hnodes b chalVal pubVal orbit hstep hchal hpub hreq hln hord hax hbasis hwidth i

#print axioms exact_finalExtTransitionGates
#print axioms exact_correctedDecodedTransitionSources
#print axioms canonical_gather_ext_core
#print axioms canonical_gather_ext_core_next
#print axioms canonical_gather_base_current
#print axioms canonical_gather_base_next
#print axioms canonical_gather_challenge
#print axioms canonical_gather_extensionPublic
#print axioms canonical_gather_initialSelectorPublic
#print axioms canonical_gather_terminalSelectorPublic
#print axioms canonical_gather_walkLine
#print axioms canonical_gather_walkLine_next
#print axioms canonical_gather_walkOverlay_current
#print axioms canonical_initialOverlayCoord_first
#print axioms canonical_terminalOverlayCoord_last
#print axioms canonical_walk_endpoint_sources
#print axioms canonical_endpoint_obligations
#print axioms canonical_selectorEquality2
#print axioms canonical_ext_gate_nonterminal_zero
#print axioms canonical_extensionCore_nonterminal
#print axioms canonical_accAfterStep
#print axioms canonical_accAfterChain
#print axioms terminal_extensionCore_of_current_gates
#print axioms canonical_extensionCore_terminal
#print axioms canonical_corrected_source_obligations
#print axioms correctedCanonicalFinalTrace_satisfies
#print axioms correctedCanonicalFinalTrace_satisfies_with

end
end OptimizedComputeCanonicalSatisfaction
end Nock.NockVMROM.Thm54
