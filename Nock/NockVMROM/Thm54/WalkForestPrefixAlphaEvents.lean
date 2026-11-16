/-
  Nock/NockVMROM/Thm54/WalkForestPrefixAlphaEvents.lean

  Consumed under the
  memory tiling `kMem + Sf = M` so the card is `≤ M` (the paper's `h`);
  off a non-tiling table the event is empty (the tiling event already
  carries those coins).

  `cur` / `chld` are `RLC^γ` of the committed `x^mem` vectors
  (`committedMemoryV` / `committedMemoryCv`); `fo` is `foOfMem`.  The
  Finset is a function of the TRACE and of `γ` (RLC), not of `αm`.

  -- the paper
-/
import Nock.Walk
import Nock.WalkPrefix
import Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
import Nock.NockVMROM.Thm54.WalkTilingEvents
import Nock.NockVMROM.Thm54.ComputeWalkRootEvents

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents

open scoped Classical
open Nock
open Nock.Walk
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents

noncomputable section

/-- Paper `:1008` `h` under tiling. -/
def memoryForestAlphaBound (M : ℕ) : ℕ := M

theorem memoryForestAlphaBound_eq (M : ℕ) : memoryForestAlphaBound M = M := rfl

section Lift
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- `cur(i) = RLC^γ(V i)` of a committed `x^mem` vector. -/
def curOfMem (V : ℕ → Fin 6 → K) (g : K) (i : ℕ) : K :=
  rlc (node_size := 6) g (V i)

/-- `chld(i,l) = RLC^γ(Cv i l)`. -/
def chldOfMem (Cv : ℕ → ℕ → Fin 6 → K) (g : K) (i l : ℕ) : K :=
  rlc (node_size := 6) g (Cv i l)

/-- A filter on the `αm` coordinate whose fibre over `(αc, γ, z)` has card `≤ d`. -/
theorem card_filter_alphaM_gamma_le (bad : K → Finset K) (d : ℕ)
    (hb : ∀ g, (bad g).card ≤ d) :
    (Finset.univ.filter (fun ω : JointCoins K => alphaM ω ∈ bad (gamma ω))).card ≤
      d * Fintype.card K ^ 3 := by
  have hsub : Finset.univ.filter (fun ω : JointCoins K => alphaM ω ∈ bad (gamma ω)) ⊆
      (Finset.univ : Finset (K × K × K)).biUnion
        (fun t => (bad t.2.1).image (fun m => ((t.1, t.2.1), (m, t.2.2)))) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    refine Finset.mem_biUnion.mpr ⟨(ω.1.1, ω.1.2, ω.2.2), Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨ω.2.1, hω, rfl⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine Finset.card_biUnion_le.trans ?_
  refine (Finset.sum_le_sum (fun t _ => Finset.card_image_le.trans (hb t.2.1))).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul]
  ring_nf
  exact le_rfl

/-- The `αm`-bad set at `γ`: `walkForestPrefixAlphaEvent` of the RLC'd committed table. -/
def alphaBadAt (V : ℕ → Fin 6 → K) (Cv : ℕ → ℕ → Fin 6 → K) (fo : ℕ → ℕ)
    (kroots h : ℕ) (g : K) : Finset K :=
  walkForestPrefixAlphaEvent (curOfMem V g) (chldOfMem Cv g) fo kroots h

theorem alphaBadAt_card_le (V : ℕ → Fin 6 → K) (Cv : ℕ → ℕ → Fin 6 → K)
    (fo : ℕ → ℕ) (kroots h : ℕ) (g : K) :
    (alphaBadAt V Cv fo kroots h g).card ≤ max h (kroots + Sf fo h) :=
  walkForestPrefixAlphaEvent_card_le _ _ _ _ _

theorem alphaBadAt_card_le_of_tiling (V : ℕ → Fin 6 → K) (Cv : ℕ → ℕ → Fin 6 → K)
    (fo : ℕ → ℕ) (kroots h : ℕ) (g : K) (htile : kroots + Sf fo h = h) :
    (alphaBadAt V Cv fo kroots h g).card ≤ memoryForestAlphaBound h := by
  have := alphaBadAt_card_le V Cv fo kroots h g
  simp only [memoryForestAlphaBound, htile, max_self] at this ⊢
  exact this

theorem nodeListP_congr_on {cur cur' : ℕ → K} {k : ℕ}
    (h : ∀ i, 1 ≤ i → i ≤ k → cur i = cur' i) :
    nodeListP cur k = nodeListP cur' k := by
  unfold nodeListP
  refine Finset.sum_congr rfl fun i hi => ?_
  have ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
  rw [h i h1 h2]

theorem Sf_congr_on {fo fo' : ℕ → ℕ} {k : ℕ}
    (h : ∀ i, 1 ≤ i → i ≤ k → fo i = fo' i) :
    Sf fo k = Sf fo' k := by
  unfold Sf
  refine Finset.sum_congr rfl fun i hi => ?_
  have ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
  exact h i h1 h2

theorem childSumP_congr_on {chld chld' : ℕ → ℕ → K} {fo fo' : ℕ → ℕ} {i : ℕ}
    (hfo_i : fo i = fo' i)
    (hfo_pre : ∀ j, 1 ≤ j → j ≤ i - 1 → fo j = fo' j)
    (hch : ∀ l, 1 ≤ l → l ≤ fo i → chld i l = chld' i l) :
    childSumP chld fo i = childSumP chld' fo' i := by
  unfold childSumP
  have hSf : Sf fo (i - 1) = Sf fo' (i - 1) := Sf_congr_on hfo_pre
  rw [hfo_i]
  refine Finset.sum_congr rfl fun l hl => ?_
  have ⟨hl1, hl2⟩ := Finset.mem_Icc.mp hl
  have hl2' : l ≤ fo i := by rw [hfo_i]; exact hl2
  rw [hch l hl1 hl2', hSf]

theorem forestQueueP_congr_on {cur cur' : ℕ → K} {chld chld' : ℕ → ℕ → K}
    {fo fo' : ℕ → ℕ} {kroots h : ℕ} (hkh : kroots ≤ h)
    (hcur : ∀ i, 1 ≤ i → i ≤ h → cur i = cur' i)
    (hchld : ∀ i l, 1 ≤ i → i ≤ h → chld i l = chld' i l)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = fo' i) :
    forestQueueP cur chld fo kroots h = forestQueueP cur' chld' fo' kroots h := by
  unfold forestQueueP
  congr 1
  · exact nodeListP_congr_on (fun i h1 h2 => hcur i h1 (le_trans h2 hkh))
  · congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have ⟨hi1, hih⟩ := Finset.mem_Icc.mp hi
    refine childSumP_congr_on (hfo i hi1 hih)
      (fun j hj1 hj2 => hfo j hj1 (le_trans hj2 (Nat.sub_le i 1 |>.trans hih)))
      (fun l _ _ => hchld i l hi1 hih)

/-- The forest α-event depends only on `cur`/`chld`/`fo` at indices `1..h`. -/
theorem walkForestPrefixAlphaEvent_congr_on {cur cur' : ℕ → K}
    {chld chld' : ℕ → ℕ → K} {fo fo' : ℕ → ℕ} {kroots h : ℕ}
    (hkh : kroots ≤ h)
    (hcur : ∀ i, 1 ≤ i → i ≤ h → cur i = cur' i)
    (hchld : ∀ i l, 1 ≤ i → i ≤ h → chld i l = chld' i l)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = fo' i) :
    walkForestPrefixAlphaEvent cur chld fo kroots h =
      walkForestPrefixAlphaEvent cur' chld' fo' kroots h := by
  have hnl := nodeListP_congr_on (k := h) hcur
  have hq := forestQueueP_congr_on hkh hcur hchld hfo
  unfold walkForestPrefixAlphaEvent
  have hbft : IsForestFullBFT cur chld fo kroots h ↔
      IsForestFullBFT cur' chld' fo' kroots h := by
    simp only [IsForestFullBFT, hnl, hq]
  by_cases hfull : IsForestFullBFT cur chld fo kroots h
  · simp [hfull, hbft.mp hfull]
  · have hfull' : ¬ IsForestFullBFT cur' chld' fo' kroots h := fun h' => hfull (hbft.mpr h')
    simp only [hfull, hfull', ↓reduceIte]
    apply Finset.filter_congr
    intro r _
    simp [hnl, hq]

/-- **The forest `α`-event on `alphaM`** of committed vectors. -/
def memoryForestAlphaEvent (V : ℕ → Fin 6 → K) (Cv : ℕ → ℕ → Fin 6 → K)
    (fo : ℕ → ℕ) (kroots h : ℕ) : Finset (JointCoins K) :=
  Finset.univ.filter (fun ω : JointCoins K =>
    alphaM ω ∈ alphaBadAt V Cv fo kroots h (gamma ω))

theorem mem_memoryForestAlphaEvent_iff (V : ℕ → Fin 6 → K) (Cv : ℕ → ℕ → Fin 6 → K)
    (fo : ℕ → ℕ) (kroots h : ℕ) (ω : JointCoins K) :
    ω ∈ memoryForestAlphaEvent V Cv fo kroots h ↔
      alphaM ω ∈ walkForestPrefixAlphaEvent
        (curOfMem V (gamma ω)) (chldOfMem Cv (gamma ω)) fo kroots h := by
  simp only [memoryForestAlphaEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/-- Priced under tiling: empty on a non-tiling table. -/
def memoryForestAlphaEventConsumed (V : ℕ → Fin 6 → K) (Cv : ℕ → ℕ → Fin 6 → K)
    (fo : ℕ → ℕ) (kroots h : ℕ) : Finset (JointCoins K) :=
  if kroots + Sf fo h = h then memoryForestAlphaEvent V Cv fo kroots h else ∅

theorem card_memoryForestAlphaEventConsumed_le (V : ℕ → Fin 6 → K)
    (Cv : ℕ → ℕ → Fin 6 → K) (fo : ℕ → ℕ) (kroots h : ℕ) :
    (memoryForestAlphaEventConsumed V Cv fo kroots h).card ≤
      memoryForestAlphaBound h * Fintype.card K ^ 3 := by
  unfold memoryForestAlphaEventConsumed
  split_ifs with htile
  · unfold memoryForestAlphaEvent
    exact card_filter_alphaM_gamma_le
      (fun g => alphaBadAt V Cv fo kroots h g)
      (memoryForestAlphaBound h)
      (fun g => alphaBadAt_card_le_of_tiling V Cv fo kroots h g htile)
  · simp

end Lift

section Committed
variable {F K : Type} [Field F] [Field K] [Fintype K] [DecidableEq K] [DecidableEq F]
  {M : ℕ}

/-- Committed-table wrapper: `V`/`Cv`/`fo` from `memorySourceEnv` / `memoryBaseEnv`. -/
def memoryForestAlphaEventOfEnvs (envsK : Fin M → Env K) (envsF : Fin M → Env F)
    (kroots : ℕ) : Finset (JointCoins K) :=
  memoryForestAlphaEventConsumed
    (committedMemoryV envsK envsF) (committedMemoryCv envsK)
    (foOfMem envsF) kroots M

theorem card_memoryForestAlphaEventOfEnvs_le (envsK : Fin M → Env K)
    (envsF : Fin M → Env F) (kroots : ℕ) :
    (memoryForestAlphaEventOfEnvs envsK envsF kroots).card ≤
      memoryForestAlphaBound M * Fintype.card K ^ 3 :=
  card_memoryForestAlphaEventConsumed_le _ _ _ _ _

theorem mem_memoryForestAlphaEventOfEnvs_of_tiling
    (envsK : Fin M → Env K) (envsF : Fin M → Env F) (kroots : ℕ)
    (htile : kroots + Sf (foOfMem envsF) M = M) (ω : JointCoins K) :
    ω ∈ memoryForestAlphaEventOfEnvs envsK envsF kroots ↔
      alphaM ω ∈ walkForestPrefixAlphaEvent
        (curOfMem (committedMemoryV envsK envsF) (gamma ω))
        (chldOfMem (committedMemoryCv envsK) (gamma ω))
        (foOfMem envsF) kroots M := by
  simp [memoryForestAlphaEventOfEnvs, memoryForestAlphaEventConsumed, htile,
    mem_memoryForestAlphaEvent_iff]

end Committed

end

end Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
