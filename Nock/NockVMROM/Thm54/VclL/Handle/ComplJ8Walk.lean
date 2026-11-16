/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Walk.lean

  **The J-8 walk at an ARBITRARY cell list and
  read list.**

  * `WalkDepthOK preads` states exactly that; `walkRows_len_le60` gives
    `len ≤ 60` on every honest row.  (`hax` / `hop5` give only `< p`.)
  * `walkChipHQK_honest_list`: the handle twin accepts `WalkTraceHQ.walkTraceHQ` at those columns;
  * **Staging** (`cellTrM_staged`, `walkTrW_staged`): the honest cell / J-8 walk trace maps `χ ↦ …` are
    `StagedCols frameJ8 crM` / `crW` whenever the fingerprint seed `z χ` reads only round-0 coins (base columns are
    coin-free, round-1 columns are the `z`-fingerprints, every round-2 column is free).
  * **`walkChipJ8_honest_list`**: the J-8 walk chip accepts, with its preprocessing (`isFirst isLast isRoot`), the
    certificate-updated trace (`HonestK8.certUp`), in the `Fin.cast` form `AcceptsJ8.qW` reads.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestK8
import Nock.NockVMROM.Thm54.VclL.Chips.HonestWalkGen
import Nock.NockVMROM.Thm54.VclL.Chips.HonestWalkAccept
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Cell
import Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Walk

open Nock Nock.Walk Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8

noncomputable section

/-! ## 1. The walk-depth binder and the honest length bound -/

/-- **`hwalk`**: every path read has depth `≤ 61` (axis `< 2^62`): the honest walk rows then have `len ≤ 60`,
the range the J-8 depth certificate covers (`HalvingJ8`). -/
def WalkDepthOK (preads : List (Noun × ℕ)) : Prop := ∀ r ∈ pathReads preads, depthOf r.2 ≤ 61

/-- The depth invariant at `60`: the node is at depth `≤ 60`, every remaining target ends at depth `≤ 61`. -/
def DepthInv60 (_n : Noun) (bs : List Bool) (T : List (List Bool)) : Prop :=
  bs.length ≤ 60 ∧ ∀ s ∈ T, s ≠ [] ∧ bs.length + s.length ≤ 61

theorem depthInv60_step : ∀ l r bs T (b : Bool), DepthInv60 (.cell l r) bs T → cont b T = true →
    DepthInv60 (if b then r else l) (bs ++ [b]) (contT b T) := by
  intro l r bs T b hI hc
  obtain ⟨-, hT⟩ := hI
  have hne : contT b T ≠ [] := by
    intro h; simp [cont, h] at hc
  obtain ⟨s0, hs0⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨hm0, hn0⟩ := mem_contT hs0
  have h0 := (hT _ hm0).2
  have hl0 : 1 ≤ s0.length := List.length_pos_iff.mpr hn0
  simp only [List.length_cons] at h0
  refine ⟨by simp; omega, fun s hs => ?_⟩
  obtain ⟨hm, hn⟩ := mem_contT hs
  have := (hT _ hm).2
  simp only [List.length_cons] at this
  exact ⟨hn, by simp; omega⟩

theorem targetsOf_depth60 {preads : List (Noun × ℕ)} (h61 : WalkDepthOK preads) (r : Noun) :
    DepthInv60 r [] (targetsOf preads r) := by
  refine ⟨by simp, fun s hs => ?_⟩
  unfold targetsOf at hs
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
  have hx1 := (List.mem_filter.mp hx).1
  have hpk : isPathAx x.2 = true := (List.mem_filter.mp hx1).2
  have hpr : x ∈ pathReads preads := by unfold pathReads; exact List.mem_dedup.mpr hx1
  have hd := h61 x hpr
  have h1 : 1 ≤ depthOf x.2 := by simpa [isPathAx] using hpk
  refine ⟨fun h => ?_, by simpa using hd⟩
  have : depthOf x.2 = 0 := by simp [depthOf, h]
  omega

/-- **Every honest walk row has `len ≤ 60`** under `hwalk`. -/
theorem walkRows_len_le60 {cells : List Noun} {preads : List (Noun × ℕ)} (h61 : WalkDepthOK preads)
    {t : NTree WN} (ht : t ∈ walkRows cells preads) : t.label.bits.length ≤ 60 := by
  obtain ⟨c, hc, hct⟩ := (mem_bfsForest _ t).mp ht
  rcases mem_walkForest hc with ⟨-, rfl⟩ | ⟨r, -, rfl⟩
  · obtain ⟨n', bs', T', rfl, hI⟩ := inTree_trie_inv _ DepthInv60 depthInv60_step hct _ _ _ rfl
      ⟨by simp, by simp⟩
    rw [(trie_label _ n' bs' T').2.1]; exact hI.1
  · obtain ⟨n', bs', T', rfl, hI⟩ := inTree_trie_inv _ DepthInv60 depthInv60_step hct _ _ _ rfl
      (targetsOf_depth60 h61 r)
    rw [(trie_label _ n' bs' T').2.1]; exact hI.1

theorem walkDepth62 {preads : List (Noun × ℕ)} (h61 : WalkDepthOK preads) :
    ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62 := fun r hr => (h61 r hr).trans (by norm_num)


/-! ## 3. Staging of the honest cell and J-8 walk traces (`StJ8`'s `M` and `W` components) -/

section Stage

theorem sampled_le_one (i : Fin frameJ8.n) : frameJ8.sampledAfter i ≤ 1 := by
  revert i; decide

theorem coins_eq_of_two {K : Type} (χ χ' : Coins frameJ8 K) (r : ℕ) (hr : 2 ≤ r)
    (h : ∀ i : Fin frameJ8.n, frameJ8.sampledAfter i < r → χ i = χ' i) : χ = χ' :=
  funext fun i => h i (lt_of_le_of_lt (sampled_le_one i) (by omega))

theorem round0_of_one {K : Type} (χ χ' : Coins frameJ8 K) (r : ℕ) (hr : r = 1)
    (h : ∀ i : Fin frameJ8.n, frameJ8.sampledAfter i < r → χ i = χ' i) :
    ∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → χ i = χ' i :=
  fun i hi => h i (by omega)

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {n : ℕ}

set_option maxHeartbeats 1000000 in
/-- `cellChipHQKW`'s column function at `j < 188` reads `col` only at base columns `< 129` and at `j − 5`. -/
theorem colW_cong (col col' : ℕ → Fin n → F) (mhv kbLv kbRv : Fin n → F)
    (iv av iv' av' : Fin n → Quad (algebraMap F K δF))
    (j : ℕ) (hj : j < 188) (hb : ∀ k < 129, col k = col' k) (hr : 134 ≤ j → col (j - 5) = col' (j - 5)) :
    HonestKW.colW δF b col mhv kbLv kbRv iv av j = HonestKW.colW δF b col' mhv kbLv kbRv iv' av' j := by
  have hW : (cellTemplate δF).width 3 = 225 := CellTraceH.cellTemplate_width δF
  funext i
  simp only [HonestKW.colW, extColF, hW]
  by_cases h1 : j < 129
  · simp only [if_pos h1, hb j h1]
  · simp only [if_neg h1]
    by_cases h2 : j < 134
    · simp only [if_pos h2, HonestKW.newW]
      rw [hb Cell.loL (by decide), hb Cell.hiL (by decide), hb Cell.loR (by decide), hb Cell.hiR (by decide)]
      split_ifs <;> first | rfl | omega
    · have h3 : j < 225 + (134 - 129) := by omega
      simp only [if_neg h2, if_pos h3, hr (by omega)]

set_option maxHeartbeats 1000000 in
/-- The J-8 walk twin's column function at `j < 97` reads `col` only at `j` (`j < 21`) or `j − 4` (`j ≥ 25`). -/
theorem walkColHQ_cong (kr : ℕ) (col col' : ℕ → Fin n → F) (kLv vLv kRv vRv : Fin n → F)
    (R R' : WalkTraceH.Roles n (Quad (algebraMap F K δF))) (j : ℕ) (hj : j < 97)
    (hb : j < 21 → col j = col' j) (hr : 25 ≤ j → col (j - 4) = col' (j - 4)) :
    WalkTraceHQ.colHQ δF kr b col kLv vLv kRv vRv R j = WalkTraceHQ.colHQ δF kr b col' kLv vLv kRv vRv R' j := by
  have hW : (walkTemplate δF kr).width 3 = 132 := WalkTraceH.walkTemplate_width δF kr
  funext i
  simp only [WalkTraceHQ.colHQ, extColF, hW]
  by_cases h1 : j < 21
  · simp only [if_pos h1, hb h1]
  · simp only [if_neg h1]
    by_cases h2 : j < 25
    · simp only [if_pos h2, WalkTraceHQ.new]
      split_ifs <;> first | rfl | omega
    · have h3 : j < 132 + (25 - 21) := by omega
      simp only [if_neg h2, if_pos h3, hr (by omega)]

end Stage

section StageM
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)

/-- **The honest cell trace at a coin vector** (`ComplJ8Cell.cellTraceB` at `242` columns). -/
def cellTrM (chalsF pubsF : Coins frameJ8 K → ℕ → K) (γF ρF zF : Coins frameJ8 K → Quad (algebraMap F K δF))
    (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 mh : ℕ → ℕ) (χ : Coins frameJ8 K) : Fin 242 → F[X] :=
  honestQ hn nodes (HonestKW.colW δF b (cellCol δF b (ComplJ8Cell.valsB δF (γF χ) (ρF χ) (zF χ) big cells mv mx mx1))
    (fun i : Fin n => (mh i : F)) (ComplJ8Cell.kbLB big cells) (ComplJ8Cell.kbRB big cells)
    (HonestKW.ivW δF b hn nodes orbit (chalsF χ) (pubsF χ)
      (cellCol δF b (ComplJ8Cell.valsB δF (γF χ) (ρF χ) (zF χ) big cells mv mx mx1))
      (fun i : Fin n => (mh i : F)) (ComplJ8Cell.kbLB big cells) (ComplJ8Cell.kbRB big cells))
    (HonestKW.avW δF b hn nodes orbit (chalsF χ) (pubsF χ)
      (cellCol δF b (ComplJ8Cell.valsB δF (γF χ) (ρF χ) (zF χ) big cells mv mx mx1))
      (fun i : Fin n => (mh i : F)) (ComplJ8Cell.kbLB big cells) (ComplJ8Cell.kbRB big cells))) 242

theorem cellTrM_eq (chalsF pubsF : Coins frameJ8 K → ℕ → K) (γF ρF zF : Coins frameJ8 K → Quad (algebraMap F K δF))
    (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 mh : ℕ → ℕ) (χ : Coins frameJ8 K) :
    cellTrM δF b hn nodes orbit chalsF pubsF γF ρF zF big cells mv mx mx1 mh χ =
      ComplJ8Cell.cellTraceB δF b hn nodes orbit (chalsF χ) (pubsF χ) (γF χ) (ρF χ) (zF χ) big cells mv mx mx1 mh :=
  rfl

theorem rowsB_base (z z' : Quad (algebraMap F K δF)) (big : Noun → Option ℕ) (cells : List Noun)
    (mv mx mx1 : ℕ → ℕ) (j k : ℕ) :
    (ComplJ8Cell.cellRowsB δF z big cells mv mx mx1 j).base k =
      (ComplJ8Cell.cellRowsB δF z' big cells mv mx mx1 j).base k := by
  simp only [ComplJ8Cell.cellRowsB, ComplJ8Cell.cellRowB, CellVals.base, cellRow0]

/-- **The honest cell trace map is staged** (`StJ8`'s `M`), when the fingerprint seed reads only round-0 coins. -/
theorem cellTrM_staged (chalsF pubsF : Coins frameJ8 K → ℕ → K) (γF ρF zF : Coins frameJ8 K → Quad (algebraMap F K δF))
    (big : Noun → Option ℕ) (cells : List Noun) (mv mx mx1 mh : ℕ → ℕ)
    (hz : ∀ χ χ' : Coins frameJ8 K, (∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → χ i = χ' i) → zF χ = zF χ') :
    StagedCols frameJ8 crM (cellTrM δF b hn nodes orbit chalsF pubsF γF ρF zF big cells mv mx mx1 mh) := by
  intro j χ χ' hχ
  by_cases h2 : 188 ≤ (j : ℕ)
  · rw [coins_eq_of_two χ χ' (crM j) (by simp only [crM]; split_ifs <;> omega) hχ]
  · unfold cellTrM
    refine honestQ_congr _ _ _ _ _ _ ?_
    have hcol : ∀ k, k < 183 → (129 ≤ k → zF χ = zF χ') →
        cellCol δF b (ComplJ8Cell.valsB (n := n) δF (γF χ) (ρF χ) (zF χ) big cells mv mx mx1) k =
          cellCol δF b (ComplJ8Cell.valsB (n := n) δF (γF χ') (ρF χ') (zF χ') big cells mv mx mx1) k := by
      intro k hk hzk
      funext i
      exact cellCol_round1 b _ _ _ _ _ _ k (fun i k => rowsB_base δF _ _ big cells mv mx mx1 i k)
        (fun h1 _ _ _ => by rw [hzk h1]) i hk
    refine colW_cong δF b _ _ _ _ _ _ _ _ _ _ (by omega) (fun k hk => hcol k (by omega)
      (fun h => absurd h (by omega))) (fun hj => hcol _ (by omega) (fun _ => ?_))
    exact hz χ χ' (round0_of_one χ χ' (crM j) (by simp only [crM]; split_ifs <;> omega) hχ)

end StageM

/-! ## 2. The three walk chips at the honest rows -/

section Walk
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The honest (unfilled) walk rows at the chip's walk coins `(chals 0, chals 1)`. -/
abbrev wRowsB (z : Quad (algebraMap F K δF)) (cells : List Noun) (preads : List (Noun × ℕ)) :
    ℕ → WalkVals F K (Quad (algebraMap F K δF)) :=
  walkRow0 δF z cells preads (chals 0) (chals 1)

/-- The honest filled walk rows. -/
abbrev wValsB (z γ ρ : Quad (algebraMap F K δF)) (cells : List Noun) (preads : List (Noun × ℕ)) :
    Fin n → WalkVals F K (Quad (algebraMap F K δF)) :=
  fun i => walkFill δF γ ρ (wRowsB δF chals z cells preads) i

/-- The honest 132-column walk column function. -/
abbrev wColB (z γ ρ : Quad (algebraMap F K δF)) (cells : List Noun) (preads : List (Noun × ℕ)) :
    ℕ → Fin n → F :=
  walkCol δF b (krW cells preads) (wValsB δF chals z γ ρ cells preads)

/-- The honest row lengths. -/
abbrev lenB (cells : List Noun) (preads : List (Noun × ℕ)) : Fin n → ℕ :=
  fun i => (wTrie cells preads i).label.bits.length

theorem wRowsB_root (z : 𝕂′) (cells : List Noun) (preads : List (Noun × ℕ)) {j : ℕ}
    (hj : j < (walkRows cells preads).length) (hk : j < krW cells preads) :
    (wRowsB δF chals z cells preads j).root = (wRowsB δF chals z cells preads j).p := by
  obtain ⟨t, ht, -, hnr⟩ := walkRows_root cells preads j hk
  have : wTrie cells preads j = t := by
    unfold wTrie; rw [List.getD_eq_getElem _ _ hj]
    exact Option.some_injective _ ((List.getElem?_eq_getElem hj).symm.trans ht)
  show GlobalCarryRecognizer.enc z (wTrie cells preads j).label.root =
    GlobalCarryRecognizer.enc z (wTrie cells preads j).label.node
  rw [this, hnr]

/-- The `ok`-gated walk chip at the honest rows (`walkOk_sat` at `walkRow0`). -/
theorem walkOk_honest_list (z γ ρ : 𝕂′) (cells : List Noun) (preads : List (Noun × ℕ))
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F)
    (h61 : WalkDepthOK preads) (hkp : krW cells preads + (walkRows cells preads).length < ringChar F)
    (hN : n = (walkRows cells preads).length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11)
    (hx : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF (wRowsB δF chals z cells preads j)) ≠ 0)
    (hL : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF (wRowsB δF chals z cells preads j)) ≠ 0)
    (hR : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF (wRowsB δF chals z cells preads j)) ≠ 0)
    (hXt : ∑ k ∈ Finset.range n, (walkFillInv δF γ ρ (wRowsB δF chals z cells preads k)).xInv =
      Quad.mk _ (pubs 0) (pubs 1))
    (hPt : ∑ k ∈ Finset.range n, wpTermV δF (walkFillInv δF γ ρ (wRowsB δF chals z cells preads k)) =
      Quad.mk _ (pubs 2) (pubs 3)) :
    RAP.SatisfiesWithPreprocessing (walkChipOk δF (krW cells preads) b hn nodes orbit chals pubs true)
      (fun j => honestQ hn nodes (wColB δF b chals z γ ρ cells preads) 132
        (Fin.cast (walkChipOk_w δF (krW cells preads) b hn nodes orbit chals pubs true) j)) := by
  have h62 := walkDepth62 h61
  exact walkOk_sat δF (krW cells preads) b hn nodes orbit chals pubs (wValsB δF chals z γ ρ cells preads) hF
    hinj hadj γ ρ hok
    (fun i => walkBaseFacts_fill δF γ ρ (wRowsB δF chals z cells preads) (krW cells preads) i
      (walkRow0_base δF z cells preads (chals 0) (chals 1) h62 hkp hN i))
    (fun i => walkKFacts_fill δF γ ρ (wRowsB δF chals z cells preads) (krW cells preads) _ _ i
      (walkRow0_K δF z cells preads (chals 0) (chals 1) hF hq hcells h62 hN i))
    (fun i => walkFill_mixed δF γ ρ (wRowsB δF chals z cells preads) (krW cells preads) pubs i
      (fun j hj hk => wRowsB_root δF chals z cells preads (hN ▸ hj) hk) hx hL hR hXt hPt)

theorem walkChip_honest_list (z γ ρ : 𝕂′) (cells : List Noun) (preads : List (Noun × ℕ))
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F)
    (h61 : WalkDepthOK preads) (hkp : krW cells preads + (walkRows cells preads).length < ringChar F)
    (hN : n = (walkRows cells preads).length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11)
    (hx : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF (wRowsB δF chals z cells preads j)) ≠ 0)
    (hL : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF (wRowsB δF chals z cells preads j)) ≠ 0)
    (hR : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF (wRowsB δF chals z cells preads j)) ≠ 0)
    (hXt : ∑ k ∈ Finset.range n, (walkFillInv δF γ ρ (wRowsB δF chals z cells preads k)).xInv =
      Quad.mk _ (pubs 0) (pubs 1))
    (hPt : ∑ k ∈ Finset.range n, wpTermV δF (walkFillInv δF γ ρ (wRowsB δF chals z cells preads k)) =
      Quad.mk _ (pubs 2) (pubs 3)) :
    (walkChip δF (krW cells preads) b hn nodes orbit chals pubs).rap.Satisfies
      (honestQ hn nodes (wColB δF b chals z γ ρ cells preads) _) := by
  exact (walkChipOk_sat δF (krW cells preads) b hn nodes orbit chals pubs true _
    (walkOk_honest_list δF b hn nodes orbit chals pubs z γ ρ cells preads hF hq hcells h61 hkp hN hinj hadj hok
      hx hL hR hXt hPt)).2.1

/-- **`walkChipHQK_honest_list`: the ternary-kind handle walk twin accepts `walkTraceHQ`** at the honest walk
columns and ANY child handle columns with kinds in `{0, 1, 2}`, given the three handle poles and the two `𝕂′`
publics equal to the totals. -/
theorem walkChipHQK_honest_list (z γ ρ : 𝕂′) (cells : List Noun) (preads : List (Noun × ℕ))
    (kLv vLv kRv vRv : Fin n → F)
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F)
    (h61 : WalkDepthOK preads) (hkp : krW cells preads + (walkRows cells preads).length < ringChar F)
    (hN : n = (walkRows cells preads).length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11)
    (hx : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF (wRowsB δF chals z cells preads j)) ≠ 0)
    (hL : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF (wRowsB δF chals z cells preads j)) ≠ 0)
    (hR : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF (wRowsB δF chals z cells preads j)) ≠ 0)
    (hXt : ∑ k ∈ Finset.range n, (walkFillInv δF γ ρ (wRowsB δF chals z cells preads k)).xInv =
      Quad.mk _ (pubs 0) (pubs 1))
    (hPt : ∑ k ∈ Finset.range n, wpTermV δF (walkFillInv δF γ ρ (wRowsB δF chals z cells preads k)) =
      Quad.mk _ (pubs 2) (pubs 3))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1 ∨ kLv i = 2) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1 ∨ kRv i = 2)
    (hpX : ∀ i, WalkTraceHQ.dRow δF (krW cells preads) b hn nodes orbit chals pubs WalkHC.xKeyH
      (wColB δF b chals z γ ρ cells preads) kLv vLv kRv vRv i ≠ 0)
    (hpL : ∀ i, WalkTraceHQ.dRow δF (krW cells preads) b hn nodes orbit chals pubs WalkHC.recLH
      (wColB δF b chals z γ ρ cells preads) kLv vLv kRv vRv i ≠ 0)
    (hpR : ∀ i, WalkTraceHQ.dRow δF (krW cells preads) b hn nodes orbit chals pubs WalkHC.recRH
      (wColB δF b chals z γ ρ cells preads) kLv vLv kRv vRv i ≠ 0)
    (hpubX : Quad.mk _ (pubs WalkHQ.pubXQ) (pubs (WalkHQ.pubXQ + 1)) = ∑ j ∈ Finset.range n,
      (WalkTraceHQ.dN δF (krW cells preads) b hn nodes orbit chals pubs (wColB δF b chals z γ ρ cells preads)
        kLv vLv kRv vRv WalkHC.xKeyH j)⁻¹)
    (hpubP : Quad.mk _ (pubs WalkHQ.pubPQ) (pubs (WalkHQ.pubPQ + 1)) = ∑ j ∈ Finset.range n,
      (liftQ δF (WalkTraceH.cN j (wColB (n := n) δF b chals z γ ρ cells preads WChip.mL)) *
          (WalkTraceHQ.dN δF (krW cells preads) b hn nodes orbit chals pubs (wColB δF b chals z γ ρ cells preads)
            kLv vLv kRv vRv WalkHC.recLH j)⁻¹ +
        liftQ δF (WalkTraceH.cN j (wColB (n := n) δF b chals z γ ρ cells preads WChip.mR)) *
          (WalkTraceHQ.dN δF (krW cells preads) b hn nodes orbit chals pubs (wColB δF b chals z γ ρ cells preads)
            kLv vLv kRv vRv WalkHC.recRH j)⁻¹)) :
    (CellTwinK.walkChipHQK δF (krW cells preads) b hn nodes orbit chals pubs).rap.Satisfies
      (WalkTraceHQ.walkTraceHQ δF (krW cells preads) b hn nodes orbit chals pubs
        (wColB δF b chals z γ ρ cells preads) kLv vLv kRv vRv) :=
  WalkTraceHQ.walkChipHQK_accepts_honest δF (krW cells preads) b hn nodes orbit chals pubs _ kLv vLv kRv vRv hinj hadj
    (walkChip_honest_list δF b hn nodes orbit chals pubs z γ ρ cells preads hF hq hcells h61 hkp hN hinj hadj hok
      hx hL hR hXt hPt)
    hkL hkR hpX hpL hpR hpubX hpubP

/-- The 166-column handle-twin column function (`walkTraceHQ`'s columns). -/
abbrev wColHQB (z γ ρ : 𝕂′) (cells : List Noun) (preads : List (Noun × ℕ)) (kLv vLv kRv vRv : Fin n → F) :
    ℕ → Fin n → F :=
  WalkTraceHQ.colHQ δF (krW cells preads) b (wColB δF b chals z γ ρ cells preads) kLv vLv kRv vRv
    (WalkTraceHQ.rolesF δF (krW cells preads) b hn nodes orbit chals pubs (wColB δF b chals z γ ρ cells preads)
      kLv vLv kRv vRv)

/-- **`walkChipJ8_honest_list`: the J-8 walk chip accepts the honest J-8 walk trace** of any cell list and read
list under `hwalk`, with the hypotheses of `walkChipHQK_honest_list`. -/
theorem walkChipJ8_honest_list (z γ ρ : 𝕂′) (cells : List Noun) (preads : List (Noun × ℕ))
    (kLv vLv kRv vRv : Fin n → F)
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F) (hcells : cells.length < ringChar F)
    (h61 : WalkDepthOK preads) (hkp : krW cells preads + (walkRows cells preads).length < ringChar F)
    (hN : n = (walkRows cells preads).length)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hok : ChalsOK δF chals γ ρ 11)
    (hx : ∀ j < n, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF (wRowsB δF chals z cells preads j)) ≠ 0)
    (hL : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF (wRowsB δF chals z cells preads j)) ≠ 0)
    (hR : ∀ j < n, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF (wRowsB δF chals z cells preads j)) ≠ 0)
    (hXt : ∑ k ∈ Finset.range n, (walkFillInv δF γ ρ (wRowsB δF chals z cells preads k)).xInv =
      Quad.mk _ (pubs 0) (pubs 1))
    (hPt : ∑ k ∈ Finset.range n, wpTermV δF (walkFillInv δF γ ρ (wRowsB δF chals z cells preads k)) =
      Quad.mk _ (pubs 2) (pubs 3))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1 ∨ kLv i = 2) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1 ∨ kRv i = 2)
    (hpX : ∀ i, WalkTraceHQ.dRow δF (krW cells preads) b hn nodes orbit chals pubs WalkHC.xKeyH
      (wColB δF b chals z γ ρ cells preads) kLv vLv kRv vRv i ≠ 0)
    (hpL : ∀ i, WalkTraceHQ.dRow δF (krW cells preads) b hn nodes orbit chals pubs WalkHC.recLH
      (wColB δF b chals z γ ρ cells preads) kLv vLv kRv vRv i ≠ 0)
    (hpR : ∀ i, WalkTraceHQ.dRow δF (krW cells preads) b hn nodes orbit chals pubs WalkHC.recRH
      (wColB δF b chals z γ ρ cells preads) kLv vLv kRv vRv i ≠ 0)
    (hpubX : Quad.mk _ (pubs WalkHQ.pubXQ) (pubs (WalkHQ.pubXQ + 1)) = ∑ j ∈ Finset.range n,
      (WalkTraceHQ.dN δF (krW cells preads) b hn nodes orbit chals pubs (wColB δF b chals z γ ρ cells preads)
        kLv vLv kRv vRv WalkHC.xKeyH j)⁻¹)
    (hpubP : Quad.mk _ (pubs WalkHQ.pubPQ) (pubs (WalkHQ.pubPQ + 1)) = ∑ j ∈ Finset.range n,
      (liftQ δF (WalkTraceH.cN j (wColB (n := n) δF b chals z γ ρ cells preads WChip.mL)) *
          (WalkTraceHQ.dN δF (krW cells preads) b hn nodes orbit chals pubs (wColB δF b chals z γ ρ cells preads)
            kLv vLv kRv vRv WalkHC.recLH j)⁻¹ +
        liftQ δF (WalkTraceH.cN j (wColB (n := n) δF b chals z γ ρ cells preads WChip.mR)) *
          (WalkTraceHQ.dN δF (krW cells preads) b hn nodes orbit chals pubs (wColB δF b chals z γ ρ cells preads)
            kLv vLv kRv vRv WalkHC.recRH j)⁻¹)) :
    RAP.SatisfiesWithPreprocessing (WalkJ8.walkChipJ8 δF (krW cells preads) b hn nodes orbit chals pubs)
      (fun j => honestQ hn nodes
        (HonestK8.certUp (wColHQB δF b hn nodes orbit chals pubs z γ ρ cells preads kLv vLv kRv vRv) (lenB cells preads))
        166 (Fin.cast (WalkJ8.walkChipJ8_width δF (krW cells preads) b hn nodes orbit chals pubs) j)) :=
  HonestK8.walkTwinJ8_accepted δF (krW cells preads) b hn nodes orbit chals pubs _ kLv vLv kRv vRv hinj hadj
    (walkOk_honest_list δF b hn nodes orbit chals pubs z γ ρ cells preads hF hq hcells h61 hkp hN hinj hadj hok
      hx hL hR hXt hPt)
    hkL hkR hpX hpL hpR hpubX hpubP (lenB cells preads)
    (fun i => by simp [walkCol, WalkVals.base, WalkVals.named, WChip.len, walkFill, walkFillInv, walkRow0])
    (fun i => walkRows_len_le60 h61 (wTrie_mem cells preads (hN ▸ i.isLt)))

end Walk


/-! ## 4. Staging of the honest J-8 walk trace (`StJ8`'s `W` component) -/

theorem fpSlot_congr' {F K Q : Type} (v v' : WalkVals F K Q) (hp : v.p = v'.p) (hl : v.l = v'.l)
    (hr : v.r = v'.r) (hroot : v.root = v'.root) (s : ℕ) : v.fpSlot s = v'.fpSlot s := by
  cases v; cases v'
  simp only at hp hl hr hroot
  subst hp hl hr hroot
  rfl

section StageW
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)

/-- The honest walk columns `< 93`: base coin-free, fingerprint roles read `z` only. -/
theorem wColB_cong (chals chals' : ℕ → K) (z z' γ ρ γ' ρ' : Quad (algebraMap F K δF)) (cells : List Noun)
    (preads : List (Noun × ℕ)) (k : ℕ) (hk : k < 93) (hz : 21 ≤ k → z = z') :
    wColB (n := n) δF b chals z γ ρ cells preads k = wColB (n := n) δF b chals' z' γ' ρ' cells preads k := by
  funext i
  unfold wColB walkCol
  by_cases h1 : k < 21
  · simp only [if_pos h1]
    simp only [wValsB, wRowsB, walkFill, walkFillInv, walkRow0, WalkVals.base, WalkVals.named]
  · simp only [if_neg h1]
    obtain rfl := hz (by omega)
    congr 1
    unfold wroleVal
    have hρ : (k - 21) / 3 < 24 := by omega
    simp only [hρ, if_true]
    have e : ∀ s, (wValsB (n := n) δF chals z γ ρ cells preads i).fpSlot s =
        (wValsB (n := n) δF chals' z γ' ρ' cells preads i).fpSlot s := fun s => fpSlot_congr' _ _ rfl rfl rfl rfl s
    rw [e]

/-- **The honest J-8 walk trace at a coin vector** (166 columns). -/
def walkTrW (chalsF pubsF : Coins frameJ8 K → ℕ → K) (γF ρF zF : Coins frameJ8 K → Quad (algebraMap F K δF))
    (cells : List Noun) (preads : List (Noun × ℕ)) (kLv vLv kRv vRv : Fin n → F) (χ : Coins frameJ8 K) :
    Fin 166 → F[X] :=
  honestQ hn nodes (HonestK8.certUp (wColHQB δF b hn nodes orbit (chalsF χ) (pubsF χ) (zF χ) (γF χ) (ρF χ) cells preads
    kLv vLv kRv vRv) (lenB cells preads)) 166

/-- **The honest J-8 walk trace map is staged** (`StJ8`'s `W`), when the fingerprint seed reads only round-0
coins. -/
theorem walkTrW_staged (chalsF pubsF : Coins frameJ8 K → ℕ → K) (γF ρF zF : Coins frameJ8 K → Quad (algebraMap F K δF))
    (cells : List Noun) (preads : List (Noun × ℕ)) (kLv vLv kRv vRv : Fin n → F)
    (hz : ∀ χ χ' : Coins frameJ8 K, (∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → χ i = χ' i) → zF χ = zF χ') :
    StagedCols frameJ8 crW (walkTrW δF b hn nodes orbit chalsF pubsF γF ρF zF cells preads kLv vLv kRv vRv) := by
  intro j χ χ' hχ
  by_cases h2 : 97 ≤ (j : ℕ)
  · rw [coins_eq_of_two χ χ' (crW j) (by simp only [crW]; split_ifs <;> omega) hχ]
  · unfold walkTrW
    refine honestQ_congr _ _ _ _ _ _ ?_
    funext i
    unfold HonestK8.certUp
    split_ifs with hc
    · rfl
    · refine congrFun (walkColHQ_cong δF b (krW cells preads) _ _ _ _ _ _ _ _ j (by omega)
        (fun hj => wColB_cong δF b _ _ _ _ _ _ _ _ cells preads j (by omega) (fun h' => absurd h' (by omega)))
        (fun hj => wColB_cong δF b _ _ _ _ _ _ _ _ cells preads _ (by omega) (fun _ => ?_))) i
      exact hz χ χ' (round0_of_one χ χ' (crW j) (by simp only [crW]; split_ifs <;> omega) hχ)

end StageW


/-! ## 5. The J-8 instance: the leaf binder over the demand roots gives the cell-list facts -/

section J8Inst
open Nock.V1J8.Gen (addCells cellsOfRoots)

def RootsLeafOK (roots : List Noun) : Prop := ∀ r ∈ roots, r.leaves ≤ 2 ^ 109

theorem internal_lt_leaves : ∀ n : Noun, n.internal < n.leaves
  | .atom _ => by simp [Noun.internal, Noun.leaves]
  | .cell a b => by
    have := internal_lt_leaves a; have := internal_lt_leaves b
    simp only [Noun.internal, Noun.leaves]; omega

theorem addCells_mem : ∀ (n : Noun) (acc : List Noun), ∀ x ∈ addCells n acc,
    x ∈ acc ∨ (x.isCell = true ∧ x.internal ≤ n.internal)
  | .atom _, acc, x, hx => Or.inl (by simpa [addCells] using hx)
  | .cell a b, acc, x, hx => by
    unfold addCells at hx
    split_ifs at hx with hm
    · exact Or.inl hx
    · rcases addCells_mem b _ x hx with h1 | ⟨hc, hi⟩
      · rcases addCells_mem a _ x h1 with h2 | ⟨hc, hi⟩
        · rcases List.mem_append.mp h2 with h3 | h3
          · exact Or.inl h3
          · simp only [List.mem_singleton] at h3
            subst h3
            exact Or.inr ⟨rfl, le_rfl⟩
        · exact Or.inr ⟨hc, by simp only [Noun.internal]; omega⟩
      · exact Or.inr ⟨hc, by simp only [Noun.internal]; omega⟩

/-- Every element of `cellsOfRoots roots` is a cell no larger than some root. -/
theorem cellsOfRoots_mem (roots : List Noun) :
    ∀ x ∈ cellsOfRoots roots, x.isCell = true ∧ ∃ r ∈ roots, x.internal ≤ r.internal := by
  have key : ∀ l : List Noun, (∀ r ∈ l, r ∈ roots) → ∀ acc : List Noun,
      (∀ x ∈ acc, x.isCell = true ∧ ∃ r ∈ roots, x.internal ≤ r.internal) →
      ∀ x ∈ l.foldl (fun acc n => addCells n acc) acc, x.isCell = true ∧ ∃ r ∈ roots, x.internal ≤ r.internal := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons k ks ih =>
      intro hl acc h
      refine ih (fun r hr => hl r (List.mem_cons_of_mem _ hr)) _ fun x hx => ?_
      rcases addCells_mem k acc x hx with h1 | ⟨hc, hi⟩
      · exact h x h1
      · exact ⟨hc, k, hl k List.mem_cons_self, hi⟩
  exact key roots (fun r hr => hr) [] (by simp)

/-- **The cell-list facts of `cellChip_honest_list` from `hleaf`.** -/
theorem cells_ok_of_leaf (roots : List Noun) (hleaf : RootsLeafOK roots) :
    (∀ c ∈ cellsOfRoots roots, c.isCell = true) ∧ ∀ c ∈ cellsOfRoots roots, rankOf c < 2 ^ 110 := by
  refine ⟨fun c hc => (cellsOfRoots_mem roots c hc).1, fun c hc => ?_⟩
  obtain ⟨-, r, hr, hi⟩ := cellsOfRoots_mem roots c hc
  have h1 := internal_lt_leaves r
  have h2 := hleaf r hr
  show c.internal < 2 ^ 110
  calc c.internal ≤ r.internal := hi
    _ < 2 ^ 109 := lt_of_lt_of_le h1 h2
    _ ≤ 2 ^ 110 := by norm_num

/-- **J-8 instance**: at the run's data (`ComplJ8Data.j8DataOf`), `hleaf` over the demand roots gives every cell of
the cell table a cell of rank `< 2^110`. -/
theorem j8_cells_ok (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl)
    {fuel : ℕ} {s f r : Noun} {t : NTree Nock.Edit.GenX.SkelX} (hgen : Nock.Edit.GenX.genX Rg.R fuel s f = some (t, r))
    (hleaf : RootsLeafOK (ComplJ8Data.j8DataOf p Rg Rt hgen).roots) :
    (∀ c ∈ (ComplJ8Data.j8DataOf p Rg Rt hgen).cells, c.isCell = true) ∧
      ∀ c ∈ (ComplJ8Data.j8DataOf p Rg Rt hgen).cells, rankOf c < 2 ^ 110 :=
  cells_ok_of_leaf _ hleaf

end J8Inst

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Walk
