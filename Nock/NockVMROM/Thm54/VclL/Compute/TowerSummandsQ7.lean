import Nock.NockVMROM.Thm54.VclL.Compute.TowerNodeRecQ7
import Nock.NockVMROM.Thm54.VclL.Compute.SummandsQ7
import Nock.NockVMROM.Thm54.VclL.Chips.MemSoundVCL

/-!
# The tower summands (`SummandsQ7` at the tower gather)

The tower decoders read
only `goodSrc` source indices: Re columns as at 309, Im columns inside `232.. 393` (round 1 of
`tableVCLT`), so the five events read only `B0 ∪ B1` (`srcVT_good`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Walk Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7
open Nock.NockVMROM.Thm54.VclL.Compute.NodeRecQ7
open Nock.ComputeTable (State DTcomp FP Pub fanoutComp labelVecOfPub)
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.Unhosted309 (goodSrc physOf physOf_good_round varVal)
open Nock.NockVMROM.Thm54.ComputeWalkLabel Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.SVWalk
open Nock.NockVMROM.Thm54.VclL.Compute.CoreQ7
open Nock.NockVMROM.Thm54.VclL.Compute.SummandsQ7
open Nock.NockVMROM.Thm54.ComputePaperPacking (OneHotSelector)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (seedSpecVCL)

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The tower decoders read round `≤ 1` columns only -/

/-- Two traces agree on every column of round `≤ 1` of the table `T`. -/
def AgreeT {F : Type} [Field F] {T : TableSpec} (Q Q' : Fin T.width → F[X]) : Prop :=
  ∀ j : Fin T.width, T.colRound j ≤ 1 → Q j = Q' j

/-- Every Im triple of a `goodSrc` role ends below `388` (VCL; source `483`), i.e. in round `1` of
`tableVCLT` (the walk-accumulator Im columns `388.. 393` are round `2`). -/
theorem towerM_ext_round : ∀ r : Fin 63, (r : ℕ) < 58 → ¬ (32 ≤ (r : ℕ) ∧ (r : ℕ) ≤ 35) →
    ∀ c, towerM.ext r = some c → c + 2 < 483 := by
  have h : ∀ r : Fin 63, (r : ℕ) < 58 → ¬ (32 ≤ (r : ℕ) ∧ (r : ℕ) ≤ 35) →
      (towerM.ext r).elim true (fun c => decide (c + 2 < 483)) = true := by decide +kernel
  intro r h1 h2 c hc
  have := h r h1 h2
  rw [hc] at this
  simpa using this

section Reads
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **The tower source-env trace at a source index depends only on its Re window and its Im triple.** -/
theorem towerSrc_trace_congr (b : Basis (Fin 3) F K) {e₁ e₂ : Env F} (j : ℕ) (hj : j < 76)
    (hRe : ∀ c, physOf j c → e₁.trace c = e₂.trace c)
    (hIm : ∀ r : Fin 63, 13 + (r : ℕ) = j → ∀ c, towerM.ext r = some c → ∀ k < 3,
      e₁.trace (c + k) = e₂.trace (c + k)) :
    (towerEnv δ towerM (gatherEnv b e₁) e₁).toSourceEnv.trace j =
      (towerEnv δ towerM (gatherEnv b e₂) e₂).toSourceEnv.trace j := by
  by_cases h13 : j < 13
  · simp only [CorrectedFinalTypedEnv.toSourceEnv, towerEnv, dif_pos h13]
    rw [hRe j (Or.inl ⟨h13, rfl⟩)]
  · simp only [CorrectedFinalTypedEnv.toSourceEnv, towerEnv, dif_neg h13, dif_pos hj]
    have hre : (gatherEnv b e₁).trace (13 + 3 * (j - 13)) = (gatherEnv b e₂).trace (13 + 3 * (j - 13)) := by
      simp only [gatherEnv, LogUp.limbVal]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := k.isLt
      rw [hRe (13 + 3 * (j - 13) + k) (Or.inr (Or.inl ⟨by omega, hj, by omega, by omega⟩))]
    have him : imVal (gatherEnv b e₁).trace (towerM.ext ⟨j - 13, by omega⟩) =
        imVal (gatherEnv b e₂).trace (towerM.ext ⟨j - 13, by omega⟩) := by
      cases hx : towerM.ext ⟨j - 13, by omega⟩ with
      | none => rfl
      | some c =>
        simp only [imVal, gatherEnv, LogUp.limbVal]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hIm ⟨j - 13, by omega⟩ (by simp; omega) c hx k k.isLt]
    rw [hre, him]

theorem tableVCLT_colRound_lt (hC c : ℕ) (hc : c < 232) (hw : c < (tableVCLT hC).width) :
    (tableVCLT hC).colRound ⟨c, hw⟩ = colRoundVCLE c := by
  simp [tableVCLT, hc]

theorem tableVCLT_colRound_im (hC c : ℕ) (hc : 232 ≤ c) (hc' : c < 388) (hw : c < (tableVCLT hC).width) :
    (tableVCLT hC).colRound ⟨c, hw⟩ = 1 := by
  show (if c < 232 then colRoundVCLE c else if c < 388 then 1 else if c = z1Col then 1 else 2) = 1
  rw [if_neg (by omega), if_pos hc']

/-- The `z1` column is a round-1 column. -/
theorem tableVCLT_colRound_z1 (hC : ℕ) (hw : z1Col < (tableVCLT hC).width) :
    (tableVCLT hC).colRound ⟨z1Col, hw⟩ = 1 := by
  show (if z1Col < 232 then colRoundVCLE z1Col else if z1Col < 388 then 1
    else if z1Col = z1Col then 1 else 2) = 1
  simp [z1Col]

variable {hC : ℕ} {S : MemShape} [DecidableEq F] [DecidableEq K]

/-- The decoded tower source env of compute row `i` (RF-free). -/
def srcVT (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin (tableVCLT hC).width → F[X])
    (i : Fin V.N) : Env (Quad (algebraMap F K δ)) :=
  (envsVG (towerGather δ V.basis) V chalV pubVal Q i).toSourceEnv

/-- **The tower decoders' reads agree** on traces agreeing on `B0 ∪ B1`, at ANY challenge / public maps. -/
theorem srcVT_good (V : VerifierData F K hC S) {Q Q' : Fin (tableVCLT hC).width → F[X]}
    (h : AgreeT Q Q') (chalV pubVal chalV' pubVal' : ℕ → F) (i : Fin V.N) :
    ∀ q, goodSrc q = true →
      varVal (srcVT δ V chalV pubVal Q i) q.1 q.2 = varVal (srcVT δ V chalV' pubVal' Q' i) q.1 q.2 := by
  rintro ⟨k, j⟩ hq
  cases k
  · have hj : j < 76 := by simp only [goodSrc, decide_eq_true_eq] at hq; omega
    show (towerEnv δ towerM (gatherEnv V.basis _) _).toSourceEnv.trace j =
      (towerEnv δ towerM (gatherEnv V.basis _) _).toSourceEnv.trace j
    apply towerSrc_trace_congr δ V.basis j hj
    · intro c hc
      have hc202 : c < 202 := by unfold physOf at hc; omega
      obtain ⟨-, hr⟩ := physOf_good_round j c hq hc
      rw [pullEnv_trace_lt _ c hc202, pullEnv_trace_lt _ c hc202]
      have hw : c < (tableVCLT hC).width := by simp [tableVCLT, vclWidthT]; omega
      simp only [envOfTrace, hw, dif_pos]
      rw [h ⟨c, hw⟩ (by rw [tableVCLT_colRound_lt hC c (by omega) hw, colRoundVCLE_lt202 c hc202]; exact hr)]
    · intro r hr c hc k hk
      have hrr : (r : ℕ) < 58 ∧ ¬ (32 ≤ (r : ℕ) ∧ (r : ℕ) ≤ 35) := by
        simp only [goodSrc, decide_eq_true_eq] at hq
        omega
      have hge := towerM_ext_ge r c hc
      have hlt := towerM_ext_round r hrr.1 hrr.2 c hc
      have hp : c + k - 95 < (tableVCLT hC).width := by simp [tableVCLT, vclWidthT]; omega
      have hv : ∀ (e : Env F), (pullEnv e).trace (c + k) = e.trace (c + k - 95) := by
        intro e
        have := vclCol_im (c + k - 95) (by omega)
        simp only [pullEnv]
        rw [show c + k = (c + k - 95) + 95 by omega, this]
        rfl
      rw [hv, hv]
      simp only [envOfTrace, hp, dif_pos]
      rw [h ⟨c + k - 95, hp⟩ (by rw [tableVCLT_colRound_im hC _ (by omega) (by omega) hp])]
  all_goals simp [goodSrc] at hq

end Reads

/-! ## 2. Pull-back of a `𝕂′` event set to `𝕂` coins -/

section pull
variable {K K' : Type} [Field K] [Fintype K] [Field K'] [Algebra K K']

open Classical in
/-- The `𝕂` coins whose image in `𝕂′` lies in `s`. -/
def pullSet (s : Finset K') : Finset K := Finset.univ.filter fun a => algebraMap K K' a ∈ s

theorem mem_pullSet (s : Finset K') (a : K) : a ∈ pullSet s ↔ algebraMap K K' a ∈ s := by
  classical
  simp [pullSet]

theorem pullSet_card_le (s : Finset K') : (pullSet (K := K) s).card ≤ s.card := by
  classical
  refine Finset.card_le_card_of_injOn (algebraMap K K') ?_ (algebraMap K K').injective.injOn
  intro a ha
  have := (mem_pullSet s a).1 (by simpa using ha)
  simpa using this

end pull

/-! ## 3. The summands at the tower -/

section summands
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [DecidableEq F] [Fintype K] [DecidableEq K] {hC : ℕ} {S : MemShape}
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- Along a staged tower strategy, coins agreeing on `depB1` give traces agreeing on `B0 ∪ B1`. -/
theorem agree_of_depB1_T {T : TableSpec} {Q : Coins frameVCL K → Traces F T S}
    (hQ : TracesStaged frameVCL T S Q) {χ χ' : Coins frameVCL K}
    (h : ∀ j ∈ depB1, χ j = χ' j) : AgreeT (Q χ).1 (Q χ').1 := by
  intro j hj
  exact hQ.1 j χ χ' (fun i hi => h i (block0_mem i (by omega)))

/-- The committed decoded tower rows at the zero challenge / public maps. -/
def srcZT (V : VerifierData F K hC S) (Q : Fin (tableVCLT hC).width → F[X]) : Fin V.N → Env (Quad (algebraMap F K δ)) :=
  srcVT δ V (fun _ => 0) (fun _ => 0) Q

theorem srcZT_staged (V : VerifierData F K hC S)
    {Q : Coins frameVCL K → Traces F (tableVCLT hC) S}
    (hQ : TracesStaged frameVCL (tableVCLT hC) S Q) {χ χ' : Coins frameVCL K}
    (h : ∀ j ∈ depB1, χ j = χ' j) :
    ∀ i q, goodSrc q = true →
      varVal (srcZT δ V (Q χ).1 i) q.1 q.2 = varVal (srcZT δ V (Q χ').1 i) q.1 q.2 :=
  fun i => srcVT_good δ V (agree_of_depB1_T hQ h) _ _ _ _ i

local notation "c0" => (⟨0, by decide⟩ : Fin frameVCL.n)
local notation "c1" => (⟨1, by decide⟩ : Fin frameVCL.n)
local notation "c2" => (⟨2, by decide⟩ : Fin frameVCL.n)

abbrev TSummand (F K : Type) [Field F] [Field K] [Fintype K] [DecidableEq K] (hC : ℕ) (S : MemShape) :=
  BadSummand frameVCL K (Traces F (tableVCLT hC) S) (TracesStaged frameVCL (tableVCLT hC) S)

/-- `z′ = (χ2, χ3) = 0` (the joint list's own `zeroSummand` at `seedSpecVCL`; coins `{2,3}`, `|𝕂|²`). -/
def sumZeroT : TSummand F K hC S :=
  zeroSummand (F := F) (C := tableVCLT hC) (S := S) (Z := seedSpecVCL (algebraMap F K δ))

/-- The `α`-tiling event (coin 0, a `𝕂` coin), pulled back from the `𝕂′` decoders. -/
def sumTilingT (V : VerifierData F K hC S) : TSummand F K hC S :=
  coinSummand c0 depB1 (by decide)
    (fun tr _ => pullSet (K := K) (tilingSetE (srcZT δ V tr.1) V.hN))
    (WalkTilingEvents.computeTilingBound V.N)
    (fun tr _ => (pullSet_card_le _).trans (tilingSetE_card _ _))
    (fun _ hQ _ _ h => by
      simp only
      rw [tilingSetE_congr V.hN (srcZT_staged δ V hQ h)])

/-- The `α`-root event (coin 0; reads `γ = χ1` (𝕂) and the seed `z′`). -/
def sumAlphaRootT (V : VerifierData F K hC S) : TSummand F K hC S :=
  coinSummand c0 depA (by decide)
    (fun tr χ => pullSet (K := K) (alphaSetE (srcZT δ V tr.1) V.hN
      (algebraMap K (Quad (algebraMap F K δ)) (χ c1)) (claimLabelVec (zQuad δ χ) V.claim)))
    V.N (fun _ _ => (pullSet_card_le _).trans (alphaSetE_card _ _ _ _))
    (fun _ hQ χ χ' h => by
      have hB : ∀ j ∈ depB1, χ j = χ' j := fun j hj => h j (Finset.mem_insert_of_mem hj)
      have h1 : χ c1 = χ' c1 := h _ (Finset.mem_insert_self _ _)
      have h2 : χ c2 = χ' c2 := hB _ (by decide)
      have h3 : χ ⟨3, by decide⟩ = χ' ⟨3, by decide⟩ := hB _ (by decide)
      have hz : zQuad δ χ = zQuad δ χ' := by unfold zQuad; rw [h2, h3]
      simp only
      rw [alphaSetE_congr V.hN (srcZT_staged δ V hQ hB), h1, hz])

/-- The `γ`-root event (coin 1; reads the seed `z′`). -/
def sumGammaRootT (V : VerifierData F K hC S) : TSummand F K hC S :=
  coinSummand c1 depB1 (by decide)
    (fun tr χ => pullSet (K := K) (gammaSetE (srcZT δ V tr.1) V.hN (claimLabelVec (zQuad δ χ) V.claim)))
    9 (fun _ _ => (pullSet_card_le _).trans (gammaSetE_card _ _ _))
    (fun _ hQ χ χ' h => by
      have h2 : χ c2 = χ' c2 := h _ (by decide)
      have h3 : χ ⟨3, by decide⟩ = χ' ⟨3, by decide⟩ := h _ (by decide)
      have hz : zQuad δ χ = zQuad δ χ' := by unfold zQuad; rw [h2, h3]
      simp only
      rw [gammaSetE_congr V.hN (srcZT_staged δ V hQ h), hz])

/-- The prefix-`γ` event (coin 1). -/
def sumPrefixT (V : VerifierData F K hC S) : TSummand F K hC S :=
  coinSummand c1 depB1 (by decide)
    (fun tr _ => pullSet (K := K) (prefixSetE (srcZT δ V tr.1) V.hN))
    (V.N * 9) (fun _ _ => (pullSet_card_le _).trans (prefixSetE_card _ _))
    (fun _ hQ _ _ h => by
      simp only
      rw [prefixSetE_congr V.hN (srcZT_staged δ V hQ h)])

/-- **The compute family's summands at the tower.** -/
def summandsQ7T (V : VerifierData F K hC S) : List (TSummand F K hC S) :=
  [sumZeroT δ, sumTilingT δ V, sumAlphaRootT δ V, sumGammaRootT δ V, sumPrefixT δ V]

theorem summandsQ7T_weights (V : VerifierData F K hC S) :
    (summandsQ7T δ V).map BadSummand.weight = [1, WalkTilingEvents.computeTilingBound V.N, V.N, 9, V.N * 9] := rfl

end summands


/-! ## 4. Outside the summands, at any gather -/

section outside
variable {F K K' : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [DecidableEq K]
  [Field K'] [Algebra F K'] [FiniteDimensional F K'] [Fintype K'] [DecidableEq K'] [CharP K' (ringChar K')]
  {hC : ℕ} {S : MemShape} {w : ℕ} (G : CoordGather F K')

/-- Under `RowFactsQ7`, the RF decoders are the RF-free ones, at any gather. -/
theorem decoders_eq_RFG (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X])
    (RF : RowFactsQ7 (cdOfGG G V chalV pubVal) chalV pubVal Q)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K') = 1 → n = 1) (r : Fin V.N) :
    rowLabelVec (envsVG G V chalV pubVal Q r).toSourceEnv =
        labelVecOfPub (pubAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar r) ∧
      (∀ l, rowChildVec (envsVG G V chalV pubVal Q r).toSourceEnv l =
        childVecN (pubAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar r)
          (tagsAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar r) l) ∧
      rowFanout (envsVG G V chalV pubVal Q r).toSourceEnv =
        fanoutComp (stAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar r) := by
  have hst : rowStateOf (envsVG G V chalV pubVal Q r).toSourceEnv =
      stAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar r :=
    rowStateOf_of_oneHot (stAt_spec (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar r)
  have hpub : rowPub (envsVG G V chalV pubVal Q r).toSourceEnv =
      pubAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar r := by
    unfold rowPub pubAt; rw [hst]; rfl
  refine ⟨by unfold rowLabelVec; rw [hpub], fun l => ?_, by unfold rowFanout; rw [hst]⟩
  unfold rowChildVec rowTags
  rw [hpub, hst]
  rfl

/-- **The first row's decoded `(s, f, e)` bind the claim at `z`**, outside the three `𝕂′`-valued
events at the walk coins `a0` (α), `g1` (γ), at any gather.  The event sets are the coin-map-free
`tilingSetE` / `alphaSetE` / `gammaSetE` over decoders `E0` that agree with the row decoders on
`goodSrc` indices. -/
theorem root_binds_outsideG (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X])
    (hadj : V.AdjacentC) (RF : RowFactsQ7 (cdOfGG G V chalV pubVal) chalV pubVal Q)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K') = 1 → n = 1)
    (E0 : Fin V.N → Env K')
    (hcg : ∀ i q, goodSrc q = true → varVal (E0 i) q.1 q.2 =
      varVal (envsVG G V chalV pubVal Q i).toSourceEnv q.1 q.2)
    (a0 g1 z : K')
    (hα0 : alphaQ (cdOfGG G V chalV pubVal) chalV = a0)
    (hγ1 : gammaQ (cdOfGG G V chalV pubVal) chalV = g1)
    (hinit : initQ (cdOfGG G V chalV pubVal) pubVal = a0)
    (hseed : seedQ (cdOfGG G V chalV pubVal) pubVal = Walk.rlc g1 (claimLabelVec z V.claim) * a0)
    (nT : a0 ∉ tilingSetE E0 V.hN)
    (nA : a0 ∉ alphaSetE E0 V.hN g1 (claimLabelVec z V.claim))
    (nG : g1 ∉ gammaSetE E0 V.hN (claimLabelVec z V.claim)) :
    ∃ st0 : State, OneHotSelector (SB (cdOfGG G V chalV pubVal) chalV pubVal Q
        (firstRowG (cdOfGG G V chalV pubVal))) st0 ∧
      SemanticStrategy.bindFP z V.claim.subject
        (StrategyOfTracesLift.decodePub (BV (cdOfGG G V chalV pubVal) chalV pubVal Q
          (firstRowG (cdOfGG G V chalV pubVal))) st0).s ∧
      SemanticStrategy.bindFP z V.claim.formula
        (StrategyOfTracesLift.decodePub (BV (cdOfGG G V chalV pubVal) chalV pubVal Q
          (firstRowG (cdOfGG G V chalV pubVal))) st0).f ∧
      SemanticStrategy.bindFP z V.claim.result
        (StrategyOfTracesLift.decodePub (BV (cdOfGG G V chalV pubVal) chalV pubVal Q
          (firstRowG (cdOfGG G V chalV pubVal))) st0).e := by
  obtain ⟨hl, hc, hf⟩ := sets_congr V.hN hcg
  have hRl : lblE (fun i => (envsVG G V chalV pubVal Q i).toSourceEnv) V.hN = fun i =>
      labelVecOfPub (pubAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar
        (rowOfG (cdOfGG G V chalV pubVal) i)) :=
    funext fun i => (decoders_eq_RFG G V chalV pubVal Q RF hchar _).1
  have hRc : chE (fun i => (envsVG G V chalV pubVal Q i).toSourceEnv) V.hN = fun i l =>
      childVecN (pubAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfGG G V chalV pubVal) i))
        (tagsAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfGG G V chalV pubVal) i)) (l - 1) :=
    funext fun i => funext fun l => (decoders_eq_RFG G V chalV pubVal Q RF hchar _).2.1 _
  have hRf : foE (fun i => (envsVG G V chalV pubVal Q i).toSourceEnv) V.hN =
      foW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar :=
    funext fun i => (decoders_eq_RFG G V chalV pubVal Q RF hchar _).2.2
  have hcur : curW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar = fun i =>
      Walk.rlc g1 (labelVecOfPub (pubAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar
        (rowOfG (cdOfGG G V chalV pubVal) i))) := by
    funext i; rw [curW, hγ1]
  have hchl : chldW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar = fun i l =>
      Walk.rlc g1 (childVecN (pubAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar
          (rowOfG (cdOfGG G V chalV pubVal) i))
        (tagsAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfGG G V chalV pubVal) i)) (l - 1)) := by
    funext i l; rw [chldW, hγ1]
  have htα : ¬ (alphaQ (cdOfGG G V chalV pubVal) chalV ^
        (1 + Sf (foW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar) V.N) =
      alphaQ (cdOfGG G V chalV pubVal) chalV ^ V.N ∧
        1 + Sf (foW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar) V.N ≠ V.N) := by
    rw [hα0, ← hRf, ← hf]
    simpa [tilingSetE] using nT
  have htile := q7_tiling (cdOfGG G V chalV pubVal) chalV pubVal Q hadj RF hchar (hinit.trans hα0.symm) htα
  have hα : alphaQ (cdOfGG G V chalV pubVal) chalV ∉ alphaBadOf (rootDiffP
      (curW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar)
      (chldW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar)
      (foW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar)
      (Walk.rlc (gammaQ (cdOfGG G V chalV pubVal) chalV) (claimLabelVec z V.claim)) V.N) := by
    have hs : Sf (foE E0 V.hN) V.N + 1 = V.N := by rw [hf, hRf]; exact htile
    simp only [alphaSetE, hs, if_true] at nA
    rw [hl, hc, hf, hRl, hRc, hRf] at nA
    rw [hcur, hchl, hα0, hγ1]
    exact nA
  have hγ : gammaQ (cdOfGG G V chalV pubVal) chalV ∉ gammaBadOf (claimLabelVec z V.claim)
      (labelVecOfPub (pubAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar
        (firstRowG (cdOfGG G V chalV pubVal)))) := by
    unfold gammaSetE at nG
    rw [hl, hRl] at nG
    rw [hγ1, ← rowOf_oneG (cdOfGG G V chalV pubVal)]
    exact nG
  have hseed' : seedQ (cdOfGG G V chalV pubVal) pubVal =
      Walk.rlc (gammaQ (cdOfGG G V chalV pubVal) chalV) (claimLabelVec z V.claim) *
        alphaQ (cdOfGG G V chalV pubVal) chalV := by
    rw [hseed, hγ1, hα0]
  exact q7_root_binds (cdOfGG G V chalV pubVal) chalV pubVal Q hadj RF hchar (hinit.trans hα0.symm)
    hseed' hα hγ

end outside


/-! ## 5. The tower coin map and publics, and the family's `hz` / `root_binds` outside the summands -/

section TowerCoins
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K) (χ : Coins frameVCL K)

theorem towerChal_one : towerM.chal ⟨1, by norm_num⟩ = some 36 := rfl
theorem towerChal_five : towerM.chal ⟨5, by norm_num⟩ = some 39 := rfl
theorem towerChal_six : towerM.chal ⟨6, by norm_num⟩ = none := rfl
theorem towerChal_ten : towerM.chal ⟨10, by norm_num⟩ = none := rfl

theorem chalSlot_one_T :
    (towerGather δ b).chalSlot (chalVQ7T δ b χ) 1 = zQuad δ χ := by
  have h1 := limbVal_chalVQ7T δ b χ 1 (by norm_num)
  have h2 := limbVal_chalVQ7T δ b χ 12 (by norm_num)
  simp only [towerGather, show (1 : ℕ) < 12 by norm_num, dite_true, towerChal_one, imVal]
  norm_num at h1 h2
  rw [h1, h2]
  simp [chalKQ7T, chalKQ7, zQuad]

theorem chalSlot_five_T :
    (towerGather δ b).chalSlot (chalVQ7T δ b χ) 5 = (zQuad δ χ)⁻¹ := by
  have h1 := limbVal_chalVQ7T δ b χ 5 (by norm_num)
  have h2 := limbVal_chalVQ7T δ b χ 13 (by norm_num)
  simp only [towerGather, show (5 : ℕ) < 12 by norm_num, dite_true, towerChal_five, imVal]
  norm_num at h1 h2
  rw [h1, h2]
  exact (chalKQ7T_tower δ χ).2.2.2

theorem chalSlot_six_T :
    (towerGather δ b).chalSlot (chalVQ7T δ b χ) 6 = algebraMap K (Quad (algebraMap F K δ)) (χ ⟨0, by decide⟩) := by
  have h1 := limbVal_chalVQ7T δ b χ 6 (by norm_num)
  simp only [towerGather, show (6 : ℕ) < 12 by norm_num, dite_true, towerChal_six, imVal]
  norm_num at h1
  have e : chalKQ7T δ χ 6 = χ ⟨0, by decide⟩ := by simp [chalKQ7T, chalKQ7]
  rw [h1, e]
  exact Quad.mk_base _ _

theorem chalSlot_ten_T :
    (towerGather δ b).chalSlot (chalVQ7T δ b χ) 10 = algebraMap K (Quad (algebraMap F K δ)) (χ ⟨1, by decide⟩) := by
  have h1 := limbVal_chalVQ7T δ b χ 10 (by norm_num)
  simp only [towerGather, show (10 : ℕ) < 12 by norm_num, dite_true, towerChal_ten, imVal]
  norm_num at h1
  have e : chalKQ7T δ χ 10 = χ ⟨1, by decide⟩ := by simp [chalKQ7T, chalKQ7]
  rw [h1, e]
  exact Quad.mk_base _ _

/-- **The tower compute publics of the CF chip**: `pubVQ7T` with the export / path terminals `ρ 1`, `ρ 2`
(`𝕂′`) at the Re / Im terminal publics `42, 51` / `45, 54`. -/
def pubCFT {hC : ℕ} {S : MemShape} (V : VerifierData F K hC S) (x : ℕ → F)
    (ρ : Fin 3 → Quad (algebraMap F K δ)) (χ : Coins frameVCL K) : ℕ → F :=
  fun j =>
    if h1 : rhoExportPub ≤ j ∧ j < rhoExportPub + 3 then
      coord V.basis (Quad.re _ (ρ 1)) ⟨j - rhoExportPub, by omega⟩
    else if h2 : rhoExportImPub ≤ j ∧ j < rhoExportImPub + 3 then
      coord V.basis (Quad.im _ (ρ 1)) ⟨j - rhoExportImPub, by omega⟩
    else if h3 : rhoPathPub ≤ j ∧ j < rhoPathPub + 3 then
      coord V.basis (Quad.re _ (ρ 2)) ⟨j - rhoPathPub, by omega⟩
    else if h4 : rhoPathImPub ≤ j ∧ j < rhoPathImPub + 3 then
      coord V.basis (Quad.im _ (ρ 2)) ⟨j - rhoPathImPub, by omega⟩
    else pubVQ7T δ V.basis V.claim x χ j

theorem pubCFT_lt {hC : ℕ} {S : MemShape} (V : VerifierData F K hC S) (x : ℕ → F)
    (ρ : Fin 3 → Quad (algebraMap F K δ)) (j : ℕ) (hj : j < 42 ∨ (48 ≤ j ∧ j < 51)) :
    pubCFT δ V x ρ χ j = pubVQ7T δ V.basis V.claim x χ j := by
  unfold pubCFT
  rw [dif_neg (by unfold rhoExportPub; omega), dif_neg (by unfold rhoExportImPub; omega),
    dif_neg (by unfold rhoPathPub; omega), dif_neg (by unfold rhoPathImPub; omega)]

theorem limbVal_congr_T (p p' : ℕ → F) (base : ℕ) (h : ∀ k < 3, p (base + k) = p' (base + k)) :
    LogUp.limbVal b p base = LogUp.limbVal b p' base := by
  unfold LogUp.limbVal
  exact Finset.sum_congr rfl fun k _ => by rw [h k k.isLt]

theorem limbVal_pubCFT_export {hC : ℕ} {S : MemShape} (V : VerifierData F K hC S) (x : ℕ → F)
    (ρ : Fin 3 → Quad (algebraMap F K δ)) :
    Quad.mk _ (LogUp.limbVal V.basis (pubCFT δ V x ρ χ) rhoExportPub)
      (LogUp.limbVal V.basis (pubCFT δ V x ρ χ) rhoExportImPub) = ρ 1 := by
  have hr : LogUp.limbVal V.basis (pubCFT δ V x ρ χ) rhoExportPub = Quad.re _ (ρ 1) := by
    unfold LogUp.limbVal
    have hc : ∀ k : Fin 3, pubCFT δ V x ρ χ (rhoExportPub + (k : ℕ)) = coord V.basis (Quad.re _ (ρ 1)) k := by
      intro k
      have hk := k.isLt
      unfold pubCFT
      rw [dif_pos ⟨by omega, by omega⟩]
      exact congrArg _ (Fin.ext (by simp))
    simp_rw [hc]
    exact reconstruct_coord V.basis _
  have hi : LogUp.limbVal V.basis (pubCFT δ V x ρ χ) rhoExportImPub = Quad.im _ (ρ 1) := by
    unfold LogUp.limbVal
    have hc : ∀ k : Fin 3, pubCFT δ V x ρ χ (rhoExportImPub + (k : ℕ)) = coord V.basis (Quad.im _ (ρ 1)) k := by
      intro k
      have hk := k.isLt
      unfold pubCFT
      rw [dif_neg (by unfold rhoExportPub rhoExportImPub; omega),
        dif_pos ⟨by omega, by omega⟩]
      exact congrArg _ (Fin.ext (by simp))
    simp_rw [hc]
    exact reconstruct_coord V.basis _
  rw [hr, hi, Quad.mk_re_im]

theorem limbVal_pubCFT_path {hC : ℕ} {S : MemShape} (V : VerifierData F K hC S) (x : ℕ → F)
    (ρ : Fin 3 → Quad (algebraMap F K δ)) :
    Quad.mk _ (LogUp.limbVal V.basis (pubCFT δ V x ρ χ) rhoPathPub)
      (LogUp.limbVal V.basis (pubCFT δ V x ρ χ) rhoPathImPub) = ρ 2 := by
  have hr : LogUp.limbVal V.basis (pubCFT δ V x ρ χ) rhoPathPub = Quad.re _ (ρ 2) := by
    unfold LogUp.limbVal
    have hc : ∀ k : Fin 3, pubCFT δ V x ρ χ (rhoPathPub + (k : ℕ)) = coord V.basis (Quad.re _ (ρ 2)) k := by
      intro k
      have hk := k.isLt
      unfold pubCFT
      rw [dif_neg (by unfold rhoExportPub rhoPathPub; omega),
        dif_neg (by unfold rhoExportImPub rhoPathPub; omega), dif_pos ⟨by omega, by omega⟩]
      exact congrArg _ (Fin.ext (by simp))
    simp_rw [hc]
    exact reconstruct_coord V.basis _
  have hi : LogUp.limbVal V.basis (pubCFT δ V x ρ χ) rhoPathImPub = Quad.im _ (ρ 2) := by
    unfold LogUp.limbVal
    have hc : ∀ k : Fin 3, pubCFT δ V x ρ χ (rhoPathImPub + (k : ℕ)) = coord V.basis (Quad.im _ (ρ 2)) k := by
      intro k
      have hk := k.isLt
      unfold pubCFT
      rw [dif_neg (by unfold rhoExportPub rhoPathImPub; omega),
        dif_neg (by unfold rhoExportImPub rhoPathImPub; omega),
        dif_neg (by unfold rhoPathPub rhoPathImPub; omega), dif_pos ⟨by omega, by omega⟩]
      exact congrArg _ (Fin.ext (by simp))
    simp_rw [hc]
    exact reconstruct_coord V.basis _
  rw [hr, hi, Quad.mk_re_im]

theorem pubSlot_zero_T {hC : ℕ} {S : MemShape} (V : VerifierData F K hC S) (x : ℕ → F)
    (ρ : Fin 3 → Quad (algebraMap F K δ)) :
    (towerGather δ V.basis).pubSlot (pubCFT δ V x ρ χ) 0 =
      algebraMap K (Quad (algebraMap F K δ)) (χ ⟨0, by decide⟩) := by
  simp only [towerGather, show (0 : ℕ) < 3 by norm_num, dite_true, towerM_pub]
  have : fullImMap.extPub ⟨0, by norm_num⟩ = none := by decide
  rw [this]
  have e : LogUp.limbVal V.basis (pubCFT δ V x ρ χ) (3 * 0) = χ ⟨0, by decide⟩ := by
    rw [limbVal_congr_T V.basis _ (pubVQ7T δ V.basis V.claim x χ) (3 * 0)
      (fun k hk => pubCFT_lt δ χ V x ρ _ (Or.inl (by omega)))]
    exact limbVal_pubVQ7T_zero δ V.basis V.claim x χ
  rw [e]
  simp only [imVal]
  exact Quad.mk_base _ _

theorem pubSlot_one_T {hC : ℕ} {S : MemShape} (V : VerifierData F K hC S) (x : ℕ → F)
    (ρ : Fin 3 → Quad (algebraMap F K δ)) :
    (towerGather δ V.basis).pubSlot (pubCFT δ V x ρ χ) 1 = seedVCLT δ V.claim χ := by
  simp only [towerGather, show (1 : ℕ) < 3 by norm_num, dite_true, towerM_pub]
  have : fullImMap.extPub ⟨1, by norm_num⟩ = some 48 := by decide
  rw [this]
  have e1 : LogUp.limbVal V.basis (pubCFT δ V x ρ χ) (3 * 1) = LogUp.limbVal V.basis (pubVQ7T δ V.basis V.claim x χ) 3 :=
    limbVal_congr_T V.basis _ _ (3 * 1) (fun k hk => pubCFT_lt δ χ V x ρ _ (Or.inl (by omega)))
  have e2 : LogUp.limbVal V.basis (pubCFT δ V x ρ χ) 48 = LogUp.limbVal V.basis (pubVQ7T δ V.basis V.claim x χ) 48 :=
    limbVal_congr_T V.basis _ _ 48 (fun k hk => pubCFT_lt δ χ V x ρ _ (Or.inr (by omega)))
  simp only [imVal]
  rw [e1, e2]
  exact seedQuad_pubVQ7T δ V.basis V.claim x χ

end TowerCoins

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54