import Nock.NockVMROM.Thm54.VclL.Compute.NodeRecQ7

/-!
# V4T6: the VCL compute summands, round-local, and the facts they buy

The compute family's own `summands` at `frameVCL` (coins `χ0 = αC`, `χ1 = γ`, `χ2 = z`; `χ0, χ1`
sampled after block 1, `χ2, χ3, χ8..10` after block 0).  Every bad set is computed from RF-free
decoders of the committed rows (`ComputeWalkRootEvents.rowLabelVec` / `rowChildVec` /
`rowFanout` over `envsV … .toSourceEnv`), which read only selectors and `𝕂`-roles `< 58` other
than `32..35` (`Unhosted309.goodSrc`) — all of round `≤ 1` (`colRoundVCLE`), independent of the
challenge / public maps:

* `sumZero` — `z = 0` (coin `2`, dep `∅`, weight `1`);
* `sumTiling` — the `α`-tiling event (coin `0`, weight `2N + 2`);
* `sumAlphaRoot` — the `α`-root event, empty off the tiling (coin `0`, weight `N`; reads `γ`, `z`);
* `sumGammaRoot` — the `γ`-root event (coin `1`, weight `9`; reads `z`);
* `sumPrefix` — the prefix-`γ` event the topology needs (coin `1`, weight `9N`).

`readsOn` is compiled for each (`coinSummand`, `AgreeV`, `srcV_good`): **all five are
round-local**.  The census is the JOINT `censusSummand` (`JointSummands`, B0 join,
`dep = ∅`), not a compute-family summand.

**`rowFacts_outside_Q7`**: acceptance at `computeChipVCLQ7S` at the frame coin map
(`chalVQ7`, `pubVQ7`) outside `summandsQ7` gives `Batch1171.RowFacts` at every node of `treeV`
(the frame's `rowFactsAt`) and the `z ≠ 0` / `z·z⁻¹` facts `node_records_Q7` takes;
**`root_binds_outside_Q7`** the claim binding at the first row.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace SummandsQ7

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.Reified Nock.Framework Nock.Framework.Reify Module
open Nock.ComputeTable (State DTcomp FP Pub fanoutComp labelVecOfPub)
open Nock.NockVMROM.Thm54.SVCompute (rowOfD firstRowD)
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.ComputePaperPacking (OneHotSelector)
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.Unhosted309 (goodSrc physOf physOf_good_round decoders_congr_good varVal)
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.SVWalk
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7
open Nock.NockVMROM.Thm54.VclL.Compute.CoreQ7

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. A single-coin summand -/

section coin
variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] {Tr : Type}
  {Staged : (Coins Φ K → Tr) → Prop}

/-- **A one-coin cylinder**: coin `i` lands in a bad set that reads only the coins `D ∌ i`. -/
def coinSummand (i : Fin Φ.n) (D : Finset (Fin Φ.n)) (hi : i ∉ D)
    (bad : Tr → Coins Φ K → Finset K) (w : ℕ) (hw : ∀ tr χ, (bad tr χ).card ≤ w)
    (hr : ∀ Q : Coins Φ K → Tr, Staged Q → ReadsOnC Φ D (fun χ => bad (Q χ) χ)) :
    BadSummand Φ K Tr Staged where
  coins := {i}
  dep := D
  disj := Finset.disjoint_singleton_left.2 hi
  badSet tr χ := Finset.univ.filter fun f : ({i} : Finset (Fin Φ.n)) → K =>
    f ⟨i, Finset.mem_singleton_self i⟩ ∈ bad tr χ
  weight := w
  card_le tr χ := by
    refine le_trans (Finset.card_le_card_of_injOn
      (fun f : ({i} : Finset (Fin Φ.n)) → K => f ⟨i, Finset.mem_singleton_self i⟩) ?_ ?_) (hw tr χ)
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf
      exact hf
    · intro f _ f' _ h
      funext ⟨j, hj⟩
      rw [Finset.mem_singleton] at hj
      subst hj
      exact h
  readsOn Q hQ χ χ' h := by
    have e := hr Q hQ χ χ' h
    simp only at e ⊢
    rw [e]

theorem coinSummand_mem (i : Fin Φ.n) (D : Finset (Fin Φ.n)) (hi : i ∉ D)
    (bad : Tr → Coins Φ K → Finset K) (w : ℕ) (hw : ∀ tr χ, (bad tr χ).card ≤ w)
    (hr : ∀ Q : Coins Φ K → Tr, Staged Q → ReadsOnC Φ D (fun χ => bad (Q χ) χ))
    (tr : Tr) (χ : Coins Φ K) :
    (coinSummand i D hi bad w hw hr).mem tr χ ↔ χ i ∈ bad tr χ := by
  unfold BadSummand.mem
  show (fun j : ({i} : Finset (Fin Φ.n)) => χ j) ∈ Finset.univ.filter _ ↔ _
  rw [Finset.mem_filter]
  simp

end coin

/-! ## 2. The RF-free decoders read `B0 ∪ B1` only -/

section src
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem srcB_trace_congr (b : Basis (Fin 3) F K) {E₁ E₂ : Env F} (j : ℕ) (hj : j < 76)
    (h : ∀ c, physOf j c → E₁.trace c = E₂.trace c) :
    (gatherCorrectedFinalTypedEnv b E₁).toSourceEnv.trace j =
      (gatherCorrectedFinalTypedEnv b E₂).toSourceEnv.trace j := by
  simp only [CorrectedFinalTypedEnv.toSourceEnv, gatherCorrectedFinalTypedEnv,
    correctedFinalExtCoordIndex]
  split_ifs <;>
    first
    | rfl
    | (rw [h j (by unfold physOf; omega)])
    | (apply Finset.sum_congr rfl; intro k _; rw [h _ (by unfold physOf; have := k.isLt; omega)])
    | (rw [h _ (by unfold physOf; omega)])

theorem rowStateOf_of_oneHot {E : Env K} {st : State} (h : OneHotSelector E st) :
    rowStateOf E = st := by
  have h1 := h .s1; have h2 := h .s2; have h3 := h .s3; have h4 := h .s4; have h5 := h .s5
  have h6 := h .s6; have h7 := h .s7; have h8 := h .s8; have h9 := h .s9; have hc := h .cons
  cases st <;> simp [Nock.Reified.opCol] at h1 h2 h3 h4 h5 h6 h7 h8 h9 hc <;>
    simp [rowStateOf, h1, h2, h3, h4, h5, h6, h7, h8, h9, hc]

end src

section srcV
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [DecidableEq F] [DecidableEq K] {hC : ℕ} {S : MemShape}

/-- The decoded source env of compute row `i` (RF-free). -/
def srcV (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X]) (i : Fin V.N) :
    Env K :=
  (envsV V chalV pubVal Q i).toSourceEnv

/-- Two compute traces agree on every column of round `≤ 1`. -/
def AgreeV (Q Q' : Fin 232 → F[X]) : Prop :=
  ∀ j : Fin 232, colRoundVCLE j ≤ 1 → Q j = Q' j

theorem colRoundVCLE_lt202 (c : ℕ) (hc : c < 202) :
    colRoundVCLE c = RepartitionedStaging.newComputeColRound c := by
  simp [colRoundVCLE, colRoundVCL, show c < 222 by omega, hc, show ¬ (214 ≤ c ∧ c < 220) by omega]

/-- **The decoders' reads agree** on traces agreeing on `B0 ∪ B1`, at ANY challenge / public maps. -/
theorem srcV_good (V : VerifierData F K hC S) {Q Q' : Fin 232 → F[X]} (h : AgreeV Q Q')
    (chalV pubVal chalV' pubVal' : ℕ → F) (i : Fin V.N) :
    ∀ q, goodSrc q = true →
      varVal (srcV V chalV pubVal Q i) q.1 q.2 = varVal (srcV V chalV' pubVal' Q' i) q.1 q.2 := by
  rintro ⟨k, j⟩ hq
  cases k
  · have hj : j < 76 := by simp only [goodSrc, decide_eq_true_eq] at hq; omega
    apply srcB_trace_congr V.basis j hj
    intro c hc
    have hc202 : c < 202 := by unfold physOf at hc; omega
    obtain ⟨-, hr⟩ := physOf_good_round j c hq hc
    rw [pullEnv_trace_lt _ c hc202, pullEnv_trace_lt _ c hc202]
    simp only [envOfTrace, show c < 232 by omega, dif_pos]
    rw [h ⟨c, by omega⟩ (by rw [show ((⟨c, by omega⟩ : Fin 232) : ℕ) = c from rfl,
      colRoundVCLE_lt202 c hc202]; exact hr)]
  all_goals simp [goodSrc] at hq

end srcV

/-! ## 3. The event sets over a decoded row family -/

section events
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {N : ℕ}

/-- The 1-indexed walk position `i` as a row (`rowOfG`'s body). -/
def rIdx (hN : 0 < N) (i : ℕ) : Fin N := if h : i - 1 < N then ⟨i - 1, h⟩ else ⟨0, hN⟩

def lblE (E : Fin N → Env K) (hN : 0 < N) (i : ℕ) : Fin 10 → K := rowLabelVec (E (rIdx hN i))
def chE (E : Fin N → Env K) (hN : 0 < N) (i l : ℕ) : Fin 10 → K := rowChildVec (E (rIdx hN i)) (l - 1)
def foE (E : Fin N → Env K) (hN : 0 < N) (i : ℕ) : ℕ := rowFanout (E (rIdx hN i))

theorem foE_le (E : Fin N → Env K) (hN : 0 < N) (i : ℕ) : foE E hN i ≤ 3 := rowFanout_le_three _

/-- The `α`-tiling set (the coin-map-free `computeTilingEvent` fibre). -/
def tilingSetE (E : Fin N → Env K) (hN : 0 < N) : Finset K :=
  Finset.univ.filter fun a : K =>
    a ^ (1 + Sf (foE E hN) N) = a ^ N ∧ 1 + Sf (foE E hN) N ≠ N

open Classical in
/-- The `α`-root set at `(γ, root label)`, empty off the tiling (the tiling set carries those). -/
def alphaSetE (E : Fin N → Env K) (hN : 0 < N) (g : K) (root : Fin 10 → K) : Finset K :=
  if Sf (foE E hN) N + 1 = N then
    alphaBadOf (rootDiffP (fun i => rlc g (lblE E hN i)) (fun i l => rlc g (chE E hN i l))
      (foE E hN) (rlc g root) N)
  else ∅

/-- The `γ`-root set at a root label. -/
def gammaSetE (E : Fin N → Env K) (hN : 0 < N) (root : Fin 10 → K) : Finset K :=
  gammaBadOf root (lblE E hN 1)

/-- The prefix-`γ` set (the topology's `γ`-event). -/
def prefixSetE (E : Fin N → Env K) (hN : 0 < N) : Finset K :=
  prefixBadGammas (lblE E hN) (chE E hN) (foE E hN) N

theorem tilingSetE_card (E : Fin N → Env K) (hN : 0 < N) :
    (tilingSetE E hN).card ≤ WalkTilingEvents.computeTilingBound N :=
  WalkTilingEvents.card_computeTilingAlphas_le _ (foE_le E hN) N

theorem alphaSetE_card (E : Fin N → Env K) (hN : 0 < N) (g : K) (root : Fin 10 → K) :
    (alphaSetE E hN g root).card ≤ N := by
  unfold alphaSetE
  split_ifs with ht
  · exact alphaBadOf_card_le (rootDiffP_natDegree_le_of_tiling _ _ _ _ ht)
  · simp

theorem gammaSetE_card (E : Fin N → Env K) (hN : 0 < N) (root : Fin 10 → K) :
    (gammaSetE E hN root).card ≤ 9 := gammaBadOf_card_le _ _

theorem prefixSetE_card (E : Fin N → Env K) (hN : 0 < N) : (prefixSetE E hN).card ≤ N * 9 :=
  prefixBadGammas_card_le _ _ _ _

/-- **All four sets are functions of the decoders' `goodSrc` reads.** -/
theorem sets_congr {E E' : Fin N → Env K} (hN : 0 < N)
    (h : ∀ i q, goodSrc q = true → varVal (E i) q.1 q.2 = varVal (E' i) q.1 q.2) :
    lblE E hN = lblE E' hN ∧ chE E hN = chE E' hN ∧ foE E hN = foE E' hN := by
  refine ⟨funext fun i => (decoders_congr_good (h _)).1, funext fun i => funext fun l =>
    (decoders_congr_good (h _)).2.1 _, funext fun i => (decoders_congr_good (h _)).2.2⟩

theorem tilingSetE_congr {E E' : Fin N → Env K} (hN : 0 < N)
    (h : ∀ i q, goodSrc q = true → varVal (E i) q.1 q.2 = varVal (E' i) q.1 q.2) :
    tilingSetE E hN = tilingSetE E' hN := by
  unfold tilingSetE; rw [(sets_congr hN h).2.2]

theorem alphaSetE_congr {E E' : Fin N → Env K} (hN : 0 < N)
    (h : ∀ i q, goodSrc q = true → varVal (E i) q.1 q.2 = varVal (E' i) q.1 q.2) (g : K)
    (root : Fin 10 → K) : alphaSetE E hN g root = alphaSetE E' hN g root := by
  obtain ⟨h1, h2, h3⟩ := sets_congr hN h
  unfold alphaSetE; rw [h1, h2, h3]

theorem gammaSetE_congr {E E' : Fin N → Env K} (hN : 0 < N)
    (h : ∀ i q, goodSrc q = true → varVal (E i) q.1 q.2 = varVal (E' i) q.1 q.2)
    (root : Fin 10 → K) : gammaSetE E hN root = gammaSetE E' hN root := by
  unfold gammaSetE; rw [(sets_congr hN h).1]

theorem prefixSetE_congr {E E' : Fin N → Env K} (hN : 0 < N)
    (h : ∀ i q, goodSrc q = true → varVal (E i) q.1 q.2 = varVal (E' i) q.1 q.2) :
    prefixSetE E hN = prefixSetE E' hN := by
  obtain ⟨h1, h2, h3⟩ := sets_congr hN h
  unfold prefixSetE; rw [h1, h2, h3]

end events

/-! ## 4. The five summands at `frameVCL` -/

section summands
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [DecidableEq F] [Fintype K] [DecidableEq K] {hC : ℕ} {S : MemShape}

/-- The coins sampled after block 0 (what a round-`≤ 1` column may read). -/
def depB1 : Finset (Fin frameVCL.n) := {⟨2, by decide⟩, ⟨3, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩,
  ⟨10, by decide⟩}

/-- `depB1` plus `γ` (coin 1), for the `α`-coin summands. -/
def depA : Finset (Fin frameVCL.n) := insert ⟨1, by decide⟩ depB1

theorem block0_mem (i : Fin frameVCL.n) (h : frameVCL.sampledAfter i < 1) : i ∈ depB1 := by
  revert i; decide

/-- Along a staged strategy, coins agreeing on `depB1` give compute traces agreeing on `B0 ∪ B1`. -/
theorem agree_of_depB1 {Q : Coins frameVCL K → Traces F (tableVCLE hC) S}
    (hQ : TracesStaged frameVCL (tableVCLE hC) S Q) {χ χ' : Coins frameVCL K}
    (h : ∀ j ∈ depB1, χ j = χ' j) : AgreeV (Q χ).1 (Q χ').1 := by
  intro j hj
  exact hQ.1 j χ χ' (fun i hi => h i (block0_mem i (by
    have : (tableVCLE hC).colRound j = colRoundVCLE j := rfl
    omega)))

/-- The committed decoded rows at the zero challenge / public maps (the decoders read neither). -/
def srcZ (V : VerifierData F K hC S) (Q : Fin 232 → F[X]) : Fin V.N → Env K :=
  srcV V (fun _ => 0) (fun _ => 0) Q

theorem srcZ_staged (V : VerifierData F K hC S) {Q : Coins frameVCL K → Traces F (tableVCLE hC) S}
    (hQ : TracesStaged frameVCL (tableVCLE hC) S Q) {χ χ' : Coins frameVCL K}
    (h : ∀ j ∈ depB1, χ j = χ' j) :
    ∀ i q, goodSrc q = true →
      varVal (srcZ V (Q χ).1 i) q.1 q.2 = varVal (srcZ V (Q χ').1 i) q.1 q.2 :=
  fun i => srcV_good V (agree_of_depB1 hQ h) _ _ _ _ i

local notation "c0" => (⟨0, by decide⟩ : Fin frameVCL.n)
local notation "c1" => (⟨1, by decide⟩ : Fin frameVCL.n)
local notation "c2" => (⟨2, by decide⟩ : Fin frameVCL.n)

/-- `z = 0` (coin 2). -/
def sumZero : BadSummand frameVCL K (Traces F (tableVCLE hC) S) (TracesStaged frameVCL (tableVCLE hC) S) :=
  coinSummand c2 ∅ (by simp) (fun _ _ => ({0} : Finset K)) 1 (fun _ _ => by simp)
    (fun _ _ _ _ _ => rfl)

/-- The `α`-tiling event (coin 0). -/
def sumTiling (V : VerifierData F K hC S) :
    BadSummand frameVCL K (Traces F (tableVCLE hC) S) (TracesStaged frameVCL (tableVCLE hC) S) :=
  coinSummand c0 depB1 (by decide) (fun tr _ => tilingSetE (srcZ V tr.1) V.hN)
    (WalkTilingEvents.computeTilingBound V.N) (fun tr _ => tilingSetE_card _ _)
    (fun _ hQ _ _ h => tilingSetE_congr V.hN (srcZ_staged V hQ h))

/-- The `α`-root event (coin 0; reads `γ = χ1`, `z = χ2`). -/
def sumAlphaRoot (V : VerifierData F K hC S) :
    BadSummand frameVCL K (Traces F (tableVCLE hC) S) (TracesStaged frameVCL (tableVCLE hC) S) :=
  coinSummand c0 depA (by decide)
    (fun tr χ => alphaSetE (srcZ V tr.1) V.hN (χ c1) (claimLabelVec (χ c2) V.claim))
    V.N (fun _ _ => alphaSetE_card _ _ _ _)
    (fun _ hQ χ χ' h => by
      have hB : ∀ j ∈ depB1, χ j = χ' j := fun j hj => h j (Finset.mem_insert_of_mem hj)
      have h1 : χ c1 = χ' c1 := h _ (Finset.mem_insert_self _ _)
      have h2 : χ c2 = χ' c2 := hB _ (by decide)
      simp only
      rw [alphaSetE_congr V.hN (srcZ_staged V hQ hB), h1, h2])

/-- The `γ`-root event (coin 1; reads `z = χ2`). -/
def sumGammaRoot (V : VerifierData F K hC S) :
    BadSummand frameVCL K (Traces F (tableVCLE hC) S) (TracesStaged frameVCL (tableVCLE hC) S) :=
  coinSummand c1 depB1 (by decide)
    (fun tr χ => gammaSetE (srcZ V tr.1) V.hN (claimLabelVec (χ c2) V.claim))
    9 (fun _ _ => gammaSetE_card _ _ _)
    (fun _ hQ χ χ' h => by
      have h2 : χ c2 = χ' c2 := h _ (by decide)
      simp only
      rw [gammaSetE_congr V.hN (srcZ_staged V hQ h), h2])

/-- The prefix-`γ` event (coin 1). -/
def sumPrefix (V : VerifierData F K hC S) :
    BadSummand frameVCL K (Traces F (tableVCLE hC) S) (TracesStaged frameVCL (tableVCLE hC) S) :=
  coinSummand c1 depB1 (by decide) (fun tr _ => prefixSetE (srcZ V tr.1) V.hN)
    (V.N * 9) (fun _ _ => prefixSetE_card _ _)
    (fun _ hQ _ _ h => prefixSetE_congr V.hN (srcZ_staged V hQ h))

/-- **The compute family's summands at VCL** (the census is the joint `censusSummand`). -/
def summandsQ7 (V : VerifierData F K hC S) :
    List (BadSummand frameVCL K (Traces F (tableVCLE hC) S) (TracesStaged frameVCL (tableVCLE hC) S)) :=
  [sumZero, sumTiling V, sumAlphaRoot V, sumGammaRoot V, sumPrefix V]

/-- The price: `(1 + (2N+2) + N) / |𝕂|` on `αC`/`z` and `(9 + 9N) / |𝕂|` on `γ`. -/
theorem summandsQ7_weights (V : VerifierData F K hC S) :
    (summandsQ7 (F := F) (K := K) (S := S) V).map BadSummand.weight =
      [1, 2 * V.N + 2, V.N, 9, V.N * 9] := rfl

end summands

/-! ## 5. Outside the summands: the coin events `rowFacts_Q7` / `q7_root_binds` take -/

section bridge
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  {hC : ℕ} {S : MemShape}

theorem rowOfD_cdOf (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (i : ℕ) :
    rowOfG (cdOfG V chalV pubVal) i = rIdx V.hN i := rfl

/-- Under `RowFactsQ7`, the RF decoders are the RF-free ones (`stAt` is the selector state). -/
theorem decoders_eq_RF (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
    (RF : RowFactsQ7 (cdOfG V chalV pubVal) chalV pubVal Q)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (r : Fin V.N) :
    rowLabelVec (srcV V chalV pubVal Q r) =
        labelVecOfPub (pubAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar r) ∧
      (∀ l, rowChildVec (srcV V chalV pubVal Q r) l =
        childVecN (pubAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar r)
          (tagsAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar r) l) ∧
      rowFanout (srcV V chalV pubVal Q r) =
        fanoutComp (stAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar r) := by
  have hst : rowStateOf (srcV V chalV pubVal Q r) = stAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar r :=
    rowStateOf_of_oneHot (stAt_spec (cdOfG V chalV pubVal) chalV pubVal Q RF hchar r)
  have hpub : rowPub (srcV V chalV pubVal Q r) = pubAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar r := by
    unfold rowPub pubAt; rw [hst]; rfl
  refine ⟨by unfold rowLabelVec; rw [hpub], fun l => ?_, by unfold rowFanout; rw [hst]⟩
  unfold rowChildVec rowTags
  rw [hpub, hst]
  rfl

variable (V : VerifierData F K hC S) (γc ρc : ℕ) (pkgPub : ℕ → F) (χ : Coins frameVCL K)
  (Q : Fin 232 → F[X])

/-- The frame coin / public maps' facts at `cdOf` (`WalkQ7.frame_coins`). -/
theorem coins_cdOf :
    alphaQ (cdOfG V (chalVQ7 V.basis χ) (pubVQ7 V.basis V.claim pkgPub χ)) (chalVQ7 V.basis χ) =
        χ ⟨0, by decide⟩ ∧
      gammaQ (cdOfG V (chalVQ7 V.basis χ) (pubVQ7 V.basis V.claim pkgPub χ)) (chalVQ7 V.basis χ) =
        χ ⟨1, by decide⟩ ∧
      zQ (cdOfG V (chalVQ7 V.basis χ) (pubVQ7 V.basis V.claim pkgPub χ)) (chalVQ7 V.basis χ) =
        χ ⟨2, by decide⟩ ∧
      slotK V.basis (chalVQ7 V.basis χ) 5 = (χ ⟨2, by decide⟩)⁻¹ ∧
      initQ (cdOfG V (chalVQ7 V.basis χ) (pubVQ7 V.basis V.claim pkgPub χ))
          (pubVQ7 V.basis V.claim pkgPub χ) = χ ⟨0, by decide⟩ ∧
      seedQ (cdOfG V (chalVQ7 V.basis χ) (pubVQ7 V.basis V.claim pkgPub χ))
          (pubVQ7 V.basis V.claim pkgPub χ) = seedVCL V.claim χ :=
  frame_coins (cdOf V (chalVQ7 V.basis χ) pkgPub) χ

/-- The core of `rowFacts_outside_Q7`, at abstract challenge / public maps carrying the frame's coin
facts (no `set`, so no unfolding of `chalVQ7`). -/
theorem rowFacts_outside_core (chalV pubVal : ℕ → F) (hadj : V.AdjacentC)
    (hinj : Function.Injective V.computeNodes)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hsat : RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7S V.hN V.computeNodes V.basis γc ρc chalV pubVal V.orbitC) Q)
    (hNp : V.N ≤ ringChar K)
    (hα0 : alphaQ (cdOfG V chalV pubVal) chalV = χ ⟨0, by decide⟩)
    (hγ1 : gammaQ (cdOfG V chalV pubVal) chalV = χ ⟨1, by decide⟩)
    (hz2 : zQ (cdOfG V chalV pubVal) chalV = χ ⟨2, by decide⟩)
    (hzi5 : slotK V.basis chalV 5 = (χ ⟨2, by decide⟩)⁻¹)
    (hinit : initQ (cdOfG V chalV pubVal) pubVal = χ ⟨0, by decide⟩)
    (hseed : seedQ (cdOfG V chalV pubVal) pubVal = seedVCL V.claim χ)
    (Qm : ∀ t : Fin S.k, Fin (S.table t).width → F[X])
    (hout : ∀ s ∈ summandsQ7 (F := F) (K := K) (S := S) V, ¬ s.mem (Q, Qm) χ) :
    zQ (cdOfG V chalV pubVal) chalV ≠ 0 ∧
      slotK V.basis chalV 5 = (zQ (cdOfG V chalV pubVal) chalV)⁻¹ ∧
      ∀ u, InTree (treeV V chalV pubVal Q) u →
        Nock.RedTeam.Batch1171.RowFacts (ax := axB0Q7 V (b0 (T := tableVCLE hC) Q))
          (zQ (cdOfG V chalV pubVal) chalV) (ringChar K) u := by
  have RF := RowFactsQ7.of_satS (cdOf V chalV pubVal) chalV pubVal Q γc ρc hinj hsat
  have nZ := hout sumZero (by simp [summandsQ7])
  have nT := hout (sumTiling V) (by simp [summandsQ7])
  have nA := hout (sumAlphaRoot V) (by simp [summandsQ7])
  have nP := hout (sumPrefix V) (by simp [summandsQ7])
  erw [sumZero, coinSummand_mem] at nZ
  erw [sumTiling, coinSummand_mem] at nT
  erw [sumAlphaRoot, coinSummand_mem] at nA
  erw [sumPrefix, coinSummand_mem] at nP
  have hz : χ ⟨2, by decide⟩ ≠ 0 := by simpa using nZ
  have hcg : ∀ i q, goodSrc q = true → varVal (srcZ V Q i) q.1 q.2 =
      varVal (srcV V chalV pubVal Q i) q.1 q.2 :=
    fun i => srcV_good V (fun _ _ => rfl) _ _ _ _ i
  obtain ⟨hl, hc, hf⟩ := sets_congr V.hN hcg
  have hRl : lblE (srcV V chalV pubVal Q) V.hN = fun i =>
      labelVecOfPub (pubAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfG V chalV pubVal) i)) :=
    funext fun i => (decoders_eq_RF V chalV pubVal Q RF hchar _).1
  have hRc : chE (srcV V chalV pubVal Q) V.hN = fun i l =>
      childVecN (pubAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfG V chalV pubVal) i))
        (tagsAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfG V chalV pubVal) i)) (l - 1) :=
    funext fun i => funext fun l => (decoders_eq_RF V chalV pubVal Q RF hchar _).2.1 _
  have hRf : foE (srcV V chalV pubVal Q) V.hN = foW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar :=
    funext fun i => (decoders_eq_RF V chalV pubVal Q RF hchar _).2.2
  have hcur : curW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar = fun i =>
      Walk.rlc (χ ⟨1, by decide⟩) (labelVecOfPub (pubAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar
        (rowOfG (cdOfG V chalV pubVal) i))) := by
    funext i; simp only [curW, hγ1]
  have hchl : chldW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar = fun i l =>
      Walk.rlc (χ ⟨1, by decide⟩) (childVecN (pubAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar
          (rowOfG (cdOfG V chalV pubVal) i))
        (tagsAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfG V chalV pubVal) i)) (l - 1)) := by
    funext i l; simp only [chldW, hγ1]
  have htα : ¬ (alphaQ (cdOfG V chalV pubVal) chalV ^
        (1 + Sf (foW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar) V.N) =
      alphaQ (cdOfG V chalV pubVal) chalV ^ V.N ∧
        1 + Sf (foW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar) V.N ≠ V.N) := by
    rw [hα0, ← hRf, ← hf]
    simpa [tilingSetE] using nT
  have htile := q7_tiling (cdOfG V chalV pubVal) chalV pubVal Q hadj RF hchar (hinit.trans hα0.symm) htα
  have hα : alphaQ (cdOfG V chalV pubVal) chalV ∉ alphaBadOf (rootDiffP
      (curW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar)
      (chldW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar)
      (foW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar)
      (Walk.rlc (gammaQ (cdOfG V chalV pubVal) chalV)
        (claimLabelVec (χ ⟨2, by decide⟩) V.claim)) V.N) := by
    have hs : Sf (foE (srcZ V Q) V.hN) V.N + 1 = V.N := by rw [hf, hRf]; exact htile
    simp only [alphaSetE, hs, if_true] at nA
    rw [hl, hc, hf, hRl, hRc, hRf] at nA
    rw [hcur, hchl, hα0, hγ1]
    exact nA
  have hγ : gammaQ (cdOfG V chalV pubVal) chalV ∉ prefixBadGammas
      (fun i => labelVecOfPub (pubAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar
        (rowOfG (cdOfG V chalV pubVal) i)))
      (fun i l => childVecN (pubAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar
          (rowOfG (cdOfG V chalV pubVal) i))
        (tagsAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfG V chalV pubVal) i)) (l - 1))
      (foW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar) V.N := by
    unfold prefixSetE at nP
    rw [hl, hc, hf, hRl, hRc, hRf] at nP
    rw [hγ1]
    exact nP
  have hseed' : seedQ (cdOfG V chalV pubVal) pubVal =
      Walk.rlc (gammaQ (cdOfG V chalV pubVal) chalV) (claimLabelVec (χ ⟨2, by decide⟩) V.claim) *
        alphaQ (cdOfG V chalV pubVal) chalV := by
    rw [hseed, hγ1, hα0]; rfl
  refine ⟨hz2 ▸ hz, hz2 ▸ hzi5, ?_⟩
  exact rowFacts_Q7 V chalV pubVal Q γc ρc hadj hinj hchar hsat hNp (z := χ ⟨2, by decide⟩)
    (hinit.trans hα0.symm) hseed' (hz2 ▸ hz) (hz2 ▸ hzi5) hα hγ htα

/-- **`root_binds` outside `summandsQ7`** (`WalkQ7.q7_root_binds`): the first row's decoded
`(s, f, e)` bind the claim at `z = χ2`. -/
theorem root_binds_outside_core (chalV pubVal : ℕ → F) (hadj : V.AdjacentC)
    (hinj : Function.Injective V.computeNodes)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hsat : RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7S V.hN V.computeNodes V.basis γc ρc chalV pubVal V.orbitC) Q)
    (hα0 : alphaQ (cdOfG V chalV pubVal) chalV = χ ⟨0, by decide⟩)
    (hγ1 : gammaQ (cdOfG V chalV pubVal) chalV = χ ⟨1, by decide⟩)
    (hinit : initQ (cdOfG V chalV pubVal) pubVal = χ ⟨0, by decide⟩)
    (hseed : seedQ (cdOfG V chalV pubVal) pubVal = seedVCL V.claim χ)
    (Qm : ∀ t : Fin S.k, Fin (S.table t).width → F[X])
    (hout : ∀ s ∈ summandsQ7 (F := F) (K := K) (S := S) V, ¬ s.mem (Q, Qm) χ) :
    ∃ st0 : State, OneHotSelector (SB (cdOfG V chalV pubVal) chalV pubVal Q
        (firstRowG (cdOfG V chalV pubVal))) st0 ∧
      SemanticStrategy.bindFP (χ ⟨2, by decide⟩) V.claim.subject
        (StrategyOfTracesLift.decodePub (BV (cdOfG V chalV pubVal) chalV pubVal Q
          (firstRowG (cdOfG V chalV pubVal))) st0).s ∧
      SemanticStrategy.bindFP (χ ⟨2, by decide⟩) V.claim.formula
        (StrategyOfTracesLift.decodePub (BV (cdOfG V chalV pubVal) chalV pubVal Q
          (firstRowG (cdOfG V chalV pubVal))) st0).f ∧
      SemanticStrategy.bindFP (χ ⟨2, by decide⟩) V.claim.result
        (StrategyOfTracesLift.decodePub (BV (cdOfG V chalV pubVal) chalV pubVal Q
          (firstRowG (cdOfG V chalV pubVal))) st0).e := by
  have RF := RowFactsQ7.of_satS (cdOf V chalV pubVal) chalV pubVal Q γc ρc hinj hsat
  have nT := hout (sumTiling V) (by simp [summandsQ7])
  have nA := hout (sumAlphaRoot V) (by simp [summandsQ7])
  have nG := hout (sumGammaRoot V) (by simp [summandsQ7])
  erw [sumTiling, coinSummand_mem] at nT
  erw [sumAlphaRoot, coinSummand_mem] at nA
  erw [sumGammaRoot, coinSummand_mem] at nG
  have hcg : ∀ i q, goodSrc q = true → varVal (srcZ V Q i) q.1 q.2 =
      varVal (srcV V chalV pubVal Q i) q.1 q.2 :=
    fun i => srcV_good V (fun _ _ => rfl) _ _ _ _ i
  obtain ⟨hl, hc, hf⟩ := sets_congr V.hN hcg
  have hRl : lblE (srcV V chalV pubVal Q) V.hN = fun i =>
      labelVecOfPub (pubAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfG V chalV pubVal) i)) :=
    funext fun i => (decoders_eq_RF V chalV pubVal Q RF hchar _).1
  have hRc : chE (srcV V chalV pubVal Q) V.hN = fun i l =>
      childVecN (pubAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfG V chalV pubVal) i))
        (tagsAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfG V chalV pubVal) i)) (l - 1) :=
    funext fun i => funext fun l => (decoders_eq_RF V chalV pubVal Q RF hchar _).2.1 _
  have hRf : foE (srcV V chalV pubVal Q) V.hN = foW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar :=
    funext fun i => (decoders_eq_RF V chalV pubVal Q RF hchar _).2.2
  have hcur : curW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar = fun i =>
      Walk.rlc (χ ⟨1, by decide⟩) (labelVecOfPub (pubAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar
        (rowOfG (cdOfG V chalV pubVal) i))) := by
    funext i; simp only [curW, hγ1]
  have hchl : chldW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar = fun i l =>
      Walk.rlc (χ ⟨1, by decide⟩) (childVecN (pubAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar
          (rowOfG (cdOfG V chalV pubVal) i))
        (tagsAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfG V chalV pubVal) i)) (l - 1)) := by
    funext i l; simp only [chldW, hγ1]
  have htα : ¬ (alphaQ (cdOfG V chalV pubVal) chalV ^
        (1 + Sf (foW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar) V.N) =
      alphaQ (cdOfG V chalV pubVal) chalV ^ V.N ∧
        1 + Sf (foW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar) V.N ≠ V.N) := by
    rw [hα0, ← hRf, ← hf]
    simpa [tilingSetE] using nT
  have htile := q7_tiling (cdOfG V chalV pubVal) chalV pubVal Q hadj RF hchar (hinit.trans hα0.symm) htα
  have hα : alphaQ (cdOfG V chalV pubVal) chalV ∉ alphaBadOf (rootDiffP
      (curW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar)
      (chldW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar)
      (foW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar)
      (Walk.rlc (gammaQ (cdOfG V chalV pubVal) chalV)
        (claimLabelVec (χ ⟨2, by decide⟩) V.claim)) V.N) := by
    have hs : Sf (foE (srcZ V Q) V.hN) V.N + 1 = V.N := by rw [hf, hRf]; exact htile
    simp only [alphaSetE, hs, if_true] at nA
    rw [hl, hc, hf, hRl, hRc, hRf] at nA
    rw [hcur, hchl, hα0, hγ1]
    exact nA
  have hγ : gammaQ (cdOfG V chalV pubVal) chalV ∉ gammaBadOf (claimLabelVec (χ ⟨2, by decide⟩) V.claim)
      (labelVecOfPub (pubAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar
        (firstRowG (cdOfG V chalV pubVal)))) := by
    unfold gammaSetE at nG
    rw [hl, hRl] at nG
    rw [hγ1, ← rowOf_oneG (cdOfG V chalV pubVal)]
    exact nG
  have hseed' : seedQ (cdOfG V chalV pubVal) pubVal =
      Walk.rlc (gammaQ (cdOfG V chalV pubVal) chalV) (claimLabelVec (χ ⟨2, by decide⟩) V.claim) *
        alphaQ (cdOfG V chalV pubVal) chalV := by
    rw [hseed, hγ1, hα0]; rfl
  exact q7_root_binds (cdOfG V chalV pubVal) chalV pubVal Q hadj RF hchar (hinit.trans hα0.symm)
    hseed' hα hγ

/-- **The frame's `rowFactsAt` body at VCL, outside `summandsQ7`**: acceptance at
`computeChipVCLQ7S` at the frame coin map gives `Batch1171.RowFacts` at `axB0Q7` at every node of
`treeV`, plus the `z` facts (`z = χ2 ≠ 0`, `z⁻¹` at slot 5) `node_records_Q7` takes. -/
theorem rowFacts_outside_Q7 (hadj : V.AdjacentC) (hinj : Function.Injective V.computeNodes)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hsat : RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7S V.hN V.computeNodes V.basis γc ρc (chalVQ7 V.basis χ)
        (pubVQ7 V.basis V.claim pkgPub χ) V.orbitC) Q)
    (hNp : V.N ≤ ringChar K) (Qm : ∀ t : Fin S.k, Fin (S.table t).width → F[X])
    (hout : ∀ s ∈ summandsQ7 (F := F) (K := K) (S := S) V, ¬ s.mem (Q, Qm) χ) :
    zQ (cdOfG V (chalVQ7 V.basis χ) (pubVQ7 V.basis V.claim pkgPub χ)) (chalVQ7 V.basis χ) ≠ 0 ∧
      slotK V.basis (chalVQ7 V.basis χ) 5 =
        (zQ (cdOfG V (chalVQ7 V.basis χ) (pubVQ7 V.basis V.claim pkgPub χ)) (chalVQ7 V.basis χ))⁻¹ ∧
      ∀ u, InTree (treeV V (chalVQ7 V.basis χ) (pubVQ7 V.basis V.claim pkgPub χ) Q) u →
        Nock.RedTeam.Batch1171.RowFacts (ax := axB0Q7 V (b0 (T := tableVCLE hC) Q))
          (zQ (cdOfG V (chalVQ7 V.basis χ) (pubVQ7 V.basis V.claim pkgPub χ)) (chalVQ7 V.basis χ))
          (ringChar K) u := by
  obtain ⟨hα0, hγ1, hz2, hzi5, hinit, hseed⟩ := coins_cdOf V pkgPub χ
  exact rowFacts_outside_core V γc ρc χ Q _ _ hadj hinj hchar hsat hNp hα0 hγ1 hz2 hzi5 hinit hseed
    Qm hout

end bridge

end

end SummandsQ7
end VclL.Compute
end Nock.NockVMROM.Thm54
