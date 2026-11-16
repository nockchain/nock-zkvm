/-
  Nock/NockVMROM/Thm54/P8Core/SVCompute/RootTwins.lean

  Over the honest trace `Qh : Fin L.w → F[X]` with the family trace
  `famQ D L c Qh` and the row facts `RF : RowFacts D L c (famQ D L c Qh)`:
  * `familyRow_trace_eqD` / `familyRow_traceNext_eqD` — the family row's source columns are the
    `c`-free `computeSourceEnvD`'s;
  * `curOf_eq_curWD`, `chldOf_eq_chldWD`, `foOf_eq_foWD` — the event's operands are the chip's walk
    operands;
  * `lblC_stateD`-shape (`lblC_state'`D), `VdD` / `CvdD`, `stAt_rowOfD`, `pubAt_rowOfD`,
    `foW_eq_foC_allD`, `deployed_walkSat_lblCD`;
-/
import Nock.NockVMROM.Thm54.P8Core.SVCompute.WalkTwins
import Nock.NockVMROM.Thm54.P8Core.Batch465Thm54DeployedRootLabelEqClaim
import Nock.NockVMROM.Thm54.P8Core.Batch471Thm54ComputeTopologyPrefix
import Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
import Nock.NockVMROM.Thm54.P8Core.Batch500Thm54GammaTransport
import Nock.NockVMROM.Thm54.P8Core.FamilyIOChainRouteB
import Nock.NockVMROM.Thm54.P8Core.SVCompute.PkgBridges
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.SVCompute

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.Reified Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.Framework Nock.Framework.Reify
open Nock.RedTeam.Batch465
open Nock.RedTeam.Batch471

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {h : ℕ}
  (D : ChipData F K h) (L : ChipLayout F K h)
  (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X])

/-- `OptimizedFullStrictNockVMROMPackage.computeSourceEnv`: the `c`-free source row. -/
def computeSourceEnvD {w : ℕ} (D : ChipData F K h) (Qh : Fin w → F[X]) (i : Fin D.N) : Env K :=
  (rowEnvD D Qh i).toSourceEnv

/-! ## 1. The family row's columns are the honest row's -/

theorem envOfTrace_famQ_trace (x : F) (chal pub chal' pub' : ℕ → F) (j : ℕ) :
    (envOfTrace (famQ D L c Qh) D.orbit.ω x chal pub).trace j =
      (envOfTrace Qh D.orbit.ω x chal' pub').trace j := by
  simp only [envOfTrace]
  by_cases hj : j < L.w
  · have h' : j < (chipOf D L c).rap.w := by rw [chipOf_w]; exact hj
    rw [dif_pos h', dif_pos hj]
    rfl
  · have h' : ¬ j < (chipOf D L c).rap.w := by rw [chipOf_w]; exact hj
    rw [dif_neg h', dif_neg hj]

theorem envOfTrace_famQ_traceNext (x : F) (chal pub chal' pub' : ℕ → F) (j : ℕ) :
    (envOfTrace (famQ D L c Qh) D.orbit.ω x chal pub).traceNext j =
      (envOfTrace Qh D.orbit.ω x chal' pub').traceNext j := by
  simp only [envOfTrace]
  by_cases hj : j < L.w
  · have h' : j < (chipOf D L c).rap.w := by rw [chipOf_w]; exact hj
    rw [dif_pos h', dif_pos hj]
    rfl
  · have h' : ¬ j < (chipOf D L c).rap.w := by rw [chipOf_w]; exact hj
    rw [dif_neg h', dif_neg hj]

set_option maxRecDepth 4000 in
/-- **Trace columns of the family row are those of the `c`-free `computeSourceEnvD`.** -/
theorem familyRow_trace_eqD (i : Fin D.N) :
    (rowEnvAtD D c (famQ D L c Qh) i).toSourceEnv.trace = (computeSourceEnvD D Qh i).trace := by
  funext j
  simp only [rowEnvAtD, computeSourceEnvD, rowEnvD, CorrectedFinalTypedEnv.toSourceEnv,
    gatherCorrectedFinalTypedEnv]
  split_ifs with h13 h76 hcb h296 h299 h302
  · rw [envOfTrace_famQ_trace]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [envOfTrace_famQ_trace]
  · rw [envOfTrace_famQ_trace]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [envOfTrace_famQ_trace]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [envOfTrace_famQ_trace]
  · rw [envOfTrace_famQ_trace]
  · rfl

set_option maxRecDepth 4000 in
theorem familyRow_traceNext_eqD (i : Fin D.N) :
    (rowEnvAtD D c (famQ D L c Qh) i).toSourceEnv.traceNext =
      (computeSourceEnvD D Qh i).traceNext := by
  funext j
  simp only [rowEnvAtD, computeSourceEnvD, rowEnvD, CorrectedFinalTypedEnv.toSourceEnv,
    gatherCorrectedFinalTypedEnv]
  split_ifs with h13 h76 hcb h296 h299 h302
  · rw [envOfTrace_famQ_traceNext]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [envOfTrace_famQ_traceNext]
  · rw [envOfTrace_famQ_traceNext]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [envOfTrace_famQ_traceNext]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [envOfTrace_famQ_traceNext]
  · rw [envOfTrace_famQ_traceNext]
  · rfl

/-! ## 2. The decoded walk operands -/

variable (RF : RowFacts D L c (famQ D L c Qh))
  (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)

section Operands

include RF hchar

/-- `rowStateOf` of the family row is the chosen one-hot state. -/
theorem rowStateOf_envRD (i : Fin D.N) :
    rowStateOf (rowEnvAtD D c (famQ D L c Qh) i).toSourceEnv =
      stAtD D L c (famQ D L c Qh) RF hchar i := by
  rw [rowStateOf_eq_computeStateOf, ← computeStateOf_ofSubst]
  exact stAt_eq_computeStateOfD D L c (famQ D L c Qh) RF hchar i

theorem rowLabelVec_familyD (i : Fin D.N) :
    rowLabelVec (computeSourceEnvD D Qh i) =
      labelVecOfPub (pubAtD D L c (famQ D L c Qh) RF hchar i) := by
  rw [← rowLabelVec_congr (familyRow_trace_eqD D L c Qh i) (familyRow_traceNext_eqD D L c Qh i)]
  show labelVecOfPub (pubOfState _ (rowStateOf (rowEnvAtD D c (famQ D L c Qh) i).toSourceEnv)) = _
  rw [rowStateOf_envRD D L c Qh RF hchar i]
  rfl

theorem rowChildVec_familyD (i : Fin D.N) (l : ℕ) :
    rowChildVec (computeSourceEnvD D Qh i) l =
      childVecN (pubAtD D L c (famQ D L c Qh) RF hchar i)
        (tagsAtD D L c (famQ D L c Qh) RF hchar i) l := by
  rw [← rowChildVec_congr (familyRow_trace_eqD D L c Qh i) (familyRow_traceNext_eqD D L c Qh i)]
  show childVecN (pubOfState _ (rowStateOf (rowEnvAtD D c (famQ D L c Qh) i).toSourceEnv))
    (fun j => (childTagHost curReader
      (rowStateOf (rowEnvAtD D c (famQ D L c Qh) i).toSourceEnv) j).eval _) l = _
  rw [rowStateOf_envRD D L c Qh RF hchar i]
  rfl

theorem rowFanout_familyD (i : Fin D.N) :
    rowFanout (computeSourceEnvD D Qh i) = fanoutComp (stAtD D L c (famQ D L c Qh) RF hchar i) := by
  rw [rowFanout, rowStateOf_congr (familyRow_trace_eqD D L c Qh i).symm, rowStateOf_envRD]

theorem curOf_eq_curWD (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ D.N) :
    curOf (computeSourceEnvD D Qh) (gamma c.1) i = curWD D L c (famQ D L c Qh) RF hchar i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < D.N := by omega
  rw [curOf_succ _ _ k hk, curWD, rowOf_succD D k hk, rowLabelVec_familyD D L c Qh RF hchar ⟨k, hk⟩]

theorem chldOf_eq_chldWD (i l : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ D.N) :
    chldOf (computeSourceEnvD D Qh) (gamma c.1) i l =
      chldWD D L c (famQ D L c Qh) RF hchar i l := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < D.N := by omega
  rw [chldOf_succ _ _ k l hk, chldWD, rowOf_succD D k hk,
    rowChildVec_familyD D L c Qh RF hchar ⟨k, hk⟩]

theorem foOf_eq_foWD (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ D.N) :
    foOf (computeSourceEnvD D Qh) i = foWD D L c (famQ D L c Qh) RF hchar i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < D.N := by omega
  rw [foOf_succ _ k hk, foWD, rowOf_succD D k hk, rowFanout_familyD D L c Qh RF hchar ⟨k, hk⟩]

end Operands

/-! ## 3. The topology at `lblC` / `foC` -/

theorem lblC_state'D (i : ℕ) : (lblCD D L c Qh i).2.2.1.state = (lblCD D L c Qh i).1 := by
  unfold lblCD
  split <;> rfl

section Topology

include RF hchar

theorem stAt_rowOfD (i : ℕ) :
    stAtD D L c (famQ D L c Qh) RF hchar (rowOfD D i) = (lblCD D L c Qh i).1 := by
  by_cases hi : i - 1 < D.N
  · simp only [rowOfD, lblCD, dif_pos hi]
    exact (stAt_eq_computeStateOfD D L c (famQ D L c Qh) RF hchar _).symm
  · simp only [rowOfD, lblCD, dif_neg hi]
    exact (stAt_eq_computeStateOfD D L c (famQ D L c Qh) RF hchar _).symm

theorem pubAt_rowOfD (i : ℕ) :
    pubAtD D L c (famQ D L c Qh) RF hchar (rowOfD D i) = (lblCD D L c Qh i).2.2.1 := by
  have hst := stAt_rowOfD D L c Qh RF hchar i
  by_cases hi : i - 1 < D.N
  · simp only [rowOfD, dif_pos hi] at hst ⊢
    simp only [pubAtD, lblCD, dif_pos hi, lblCAtD]
    simp only [lblCD, dif_pos hi, lblCAtD] at hst
    rw [hst]
    rfl
  · simp only [rowOfD, dif_neg hi] at hst ⊢
    simp only [pubAtD, lblCD, dif_neg hi, lblCAtD]
    simp only [lblCD, dif_neg hi, lblCAtD] at hst
    rw [hst]
    rfl

def VdD (D : ChipData F K h) (L : ChipLayout F K h)
    (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X]) (i : ℕ) : Fin 10 → K :=
  labelVecOfPub (lblCD D L c Qh i).2.2.1

def CvdD (i l : ℕ) : Fin 10 → K :=
  childVecN (lblCD D L c Qh i).2.2.1
    (tagsAtD D L c (famQ D L c Qh) RF hchar (rowOfD D i)) (l - 1)

theorem foW_eq_foC_allD :
    foWD D L c (famQ D L c Qh) RF hchar = foCD D L c Qh := by
  funext i
  simp only [foWD, foCD]
  rw [stAt_rowOfD D L c Qh RF hchar i]

/-- **`Batch459::deployed_walkSat` at `lblC` / `foC`, all indices**. -/
theorem deployed_walkSat_lblCD (hadj : D.Adjacent) :
    WalkSat (fun i => rlc (gamma c.1) (VdD D L c Qh i))
      (fun i l => rlc (gamma c.1) (CvdD D L c Qh RF hchar i l)) (foCD D L c Qh)
      (lnWD D L c (famQ D L c Qh)) (countWD D L c (famQ D L c Qh))
      (accWD D L c (famQ D L c Qh)) (alphaC c.1)
      (seedOfClaim D.claim c) (alphaC c.1) D.N := by
  have hw := deployed_walkSatD D L c (famQ D L c Qh) RF hchar hadj
  have hcur : curWD D L c (famQ D L c Qh) RF hchar =
      fun i => rlc (gamma c.1) (VdD D L c Qh i) := by
    funext i; simp only [curWD, VdD]; rw [pubAt_rowOfD D L c Qh RF hchar i]
  have hch : chldWD D L c (famQ D L c Qh) RF hchar =
      fun i l => rlc (gamma c.1) (CvdD D L c Qh RF hchar i l) := by
    funext i l; simp only [chldWD, CvdD]; rw [pubAt_rowOfD D L c Qh RF hchar i]
  rw [hcur, hch, foW_eq_foC_allD D L c Qh RF hchar] at hw
  exact hw

/-! ## 4. -/

/-- Committed node vector at walk index `i ∈ 1..N` is `VdD i`. -/
theorem Vd_eq_committedD (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ D.N) :
    committedComputeV (computeSourceEnvD D Qh) i = VdD D L c Qh i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < D.N := by omega
  have hpos : 1 ≤ k + 1 ∧ k < D.N := ⟨by omega, hk⟩
  have hpub := pubAt_rowOfD D L c Qh RF hchar (k + 1)
  rw [rowOf_succD D k hk] at hpub
  simp only [committedComputeV, VdD, dif_pos hpos, Nat.add_sub_cancel]
  rw [rowLabelVec_familyD D L c Qh RF hchar ⟨k, hk⟩, hpub]

/-- Committed child vector at walk index `i ∈ 1..N` is `CvdD i l`. -/
theorem Cvd_eq_committedD (i l : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ D.N) :
    committedComputeCv (computeSourceEnvD D Qh) i l = CvdD D L c Qh RF hchar i l := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < D.N := by omega
  have hpos : 1 ≤ k + 1 ∧ k < D.N := ⟨by omega, hk⟩
  have hpub := pubAt_rowOfD D L c Qh RF hchar (k + 1)
  rw [rowOf_succD D k hk] at hpub
  simp only [committedComputeCv, CvdD, dif_pos hpos, Nat.add_sub_cancel]
  rw [rowChildVec_familyD D L c Qh RF hchar ⟨k, hk⟩]
  simp only [rowOf_succD D k hk, hpub]

/-- Committed fanout at walk index `i ∈ 1..N` is `foCD i`. -/
theorem foC_eq_committedD (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ D.N) :
    foOf (computeSourceEnvD D Qh) i = foCD D L c Qh i := by
  have hfoW := foOf_eq_foWD D L c Qh RF hchar i hi1 hih
  have hAll := foW_eq_foC_allD D L c Qh RF hchar
  rw [hfoW, hAll]

/-- The priced event's `prefixBadGammas` is the topology statement's. -/
theorem prefixBadGammas_Vd_eq_committedD :
    prefixBadGammas (committedComputeV (computeSourceEnvD D Qh))
        (committedComputeCv (computeSourceEnvD D Qh))
        (foOf (computeSourceEnvD D Qh)) D.N =
      prefixBadGammas (VdD D L c Qh) (CvdD D L c Qh RF hchar) (foCD D L c Qh) D.N := by
  have hV : ∀ i, 1 ≤ i → i ≤ D.N →
      committedComputeV (computeSourceEnvD D Qh) i = VdD D L c Qh i :=
    fun i h1 h2 => Vd_eq_committedD D L c Qh RF hchar i h1 h2
  have hC : ∀ i l, 1 ≤ i → i ≤ D.N →
      committedComputeCv (computeSourceEnvD D Qh) i l = CvdD D L c Qh RF hchar i l :=
    fun i l h1 h2 => Cvd_eq_committedD D L c Qh RF hchar i l h1 h2
  have hF : ∀ i, 1 ≤ i → i ≤ D.N →
      foOf (computeSourceEnvD D Qh) i = foCD D L c Qh i :=
    fun i h1 h2 => foC_eq_committedD D L c Qh RF hchar i h1 h2
  exact Nock.RedTeam.Batch500.prefixBadGammas_congr_on hV hC hF

end Topology

end

end Nock.NockVMROM.Thm54.SVCompute
