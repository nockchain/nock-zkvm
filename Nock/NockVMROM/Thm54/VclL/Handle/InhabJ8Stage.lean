/-
  Nock/NockVMROM/Thm54/VclL/Handle/InhabJ8Stage.lean

* **`trJ0_staged`**: `StJ8 (fun χ => trJ0 δ b hdvd Rt χ)`: every column of every chip of the honest traces of
    `*[[0 0] [0 1]] = [0 0]` reads only the coins sampled before its round.
    - compute (`stC`): columns `< 69` are coin-free (`trX_base`); columns `69..122` read `chalVJ8` (coins `11..16`),
      `αW = χ₁₃`, `γW = χ₁₄`, all sampled after round `0`, and NOT the public vector (`trX_pub`: the slot inverses and
      accumulators do not read it, `preT_pub` / `accV_pub`);
    - cell (`stM`): columns `< 134` coin-free (base fields of `crow`, the handle multiplicity, the kind bits and the
      two limb inverses read only base columns); columns `134..187` (the fingerprint roles) read `z′ = (χ₂, χ₃)`;
    - J-8 walk (`stW`): columns `< 25` coin-free (base, the re-chosen certificate, `kL vL kR vR`); `25..96` (the
      fingerprint roles) read `z′`;
    - atom table (`stA`): columns `< 205` coin-free (the pad row's base, `mh = 0`, the inert pad columns);
      `205..258` (the pad row's fingerprint roles) read `y = (χ₁₇, χ₁₈)`;
    - J and atom walk: the zero traces;
    - every round-`2` column: all coins are sampled after round `≤ 1`.
  * **`inhabitant_staged_complete`**: the staged honest trace map, the bad-set card bound `|badJ0| ≤ 25 · |K|^18`
    and acceptance outside `badJ0` (`InhabJ8Good.inhabitant_outside_bad`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Good

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Stage

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Static
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemDom
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemCell
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemWalk
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemMain
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Atom
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomCell
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomChip
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Main

noncomputable section

/-! ## 1. Round tools -/

theorem frameJ8_sampled_le_one (i : Fin frameJ8.n) : frameJ8.sampledAfter i ≤ 1 := by
  revert i; decide

/-- A round-`≥ 2` column: agreement below its round is agreement everywhere. -/
theorem all_of_two {K : Type} (χ χ' : Coins frameJ8 K) (r : ℕ) (hr : 2 ≤ r)
    (h : ∀ i : Fin frameJ8.n, frameJ8.sampledAfter i < r → χ i = χ' i) : χ = χ' :=
  funext fun i => h i (lt_of_le_of_lt (frameJ8_sampled_le_one i) (by omega))

/-- A round-`1` column: agreement on every coin sampled after round `0`. -/
theorem zero_of_one {K : Type} (χ χ' : Coins frameJ8 K) (r : ℕ) (hr : r = 1)
    (h : ∀ i : Fin frameJ8.n, frameJ8.sampledAfter i < r → χ i = χ' i) :
    ∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → χ i = χ' i :=
  fun i hi => h i (by omega)

section Readers
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K] (δ : ZMod p)

theorem zJ_agree (χ χ' : Coins frameJ8 K) (h0 : ∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → χ i = χ' i) :
    zJ δ χ = zJ δ χ' := by
  show Quad.mk _ (χ c2) (χ c3) = Quad.mk _ (χ' c2) (χ' c3)
  rw [h0 c2 rfl, h0 c3 rfl]

theorem yA_agree (χ χ' : Coins frameJ8 K) (h0 : ∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → χ i = χ' i) :
    yA δ χ = yA δ χ' := by
  show Quad.mk _ (χ cY1) (χ cY2) = Quad.mk _ (χ' cY1) (χ' cY2)
  rw [h0 cY1 rfl, h0 cY2 rfl]

end Readers

/-! ## 2. The compute trace -/

section Comp
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

open Nock.Edit.GenX in
/-- **The honest compute trace does not read the public vector.** -/
theorem trX_pub (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (Nock.Walk.NTree SkelX))
    (chalV pub1 pub2 : ℕ → ZMod p) (ln cnt acc : ℕ → K) (j c : ℕ) :
    HonestTraceX.trX b δ H pd W chalV pub1 ln cnt acc j c = HonestTraceX.trX b δ H pd W chalV pub2 ln cnt acc j c := by
  unfold HonestTraceX.trX
  rw [InhabJ8Comp.preT_pub δ b H pd W chalV pub1 pub2,
    InhabJ8Comp.accV_pub δ b H pd W chalV pub1 pub2]

theorem chalVJ8_agree (χ χ' : Coins frameJ8 K) (h0 : ∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → χ i = χ' i) :
    chalVJ8 b χ = chalVJ8 b χ' := by
  have e : ∀ k (hk : k < 19), 11 ≤ k → k < 17 → χ ⟨k, hk⟩ = χ' ⟨k, hk⟩ := by
    intro k hk h11 h17
    exact h0 _ (by interval_cases k <;> rfl)
  have hc : coinHQ (toVSQ χ) = coinHQ (toVSQ χ') := by
    funext q
    unfold coinHQ coinH
    split_ifs
    · exact e 11 (by decide) (by decide) (by decide)
    · exact e 12 (by decide) (by decide) (by decide)
    · exact e 13 (by decide) (by decide) (by decide)
    · exact e 14 (by decide) (by decide) (by decide)
    · exact e 15 (by decide) (by decide) (by decide)
    · exact e 16 (by decide) (by decide) (by decide)
  funext j
  unfold chalVJ8 chalVHQ
  rw [hc]

/-- **The compute trace is staged.** -/
theorem stC (hdvd : 3 * 2 ^ 1 ∣ p - 1) (Rt : ℕ → Nock.Jet.Autogen.Tpl) :
    StagedCols frameJ8 crC (fun χ => (trJ0 δ b hdvd Rt χ : TrJ8 (ZMod p)).C) := by
  intro j χ χ' h
  show InhabJ8Comp.trC0 δ b (H0 p) χ (PbJ hdvd Rt).nodes 123 j = InhabJ8Comp.trC0 δ b (H0 p) χ' (PbJ hdvd Rt).nodes 123 j
  unfold InhabJ8Comp.trC0 HonestTraceX.polyX
  refine congrArg (fun f => Lagrange.interpolate Finset.univ (PbJ hdvd Rt).nodes f) (funext fun i => ?_)
  by_cases hj : (j : ℕ) < 69
  · rw [HonestTraceX.trX_base _ _ _ _ _ _ _ _ _ _ _ _ hj, HonestTraceX.trX_base _ _ _ _ _ _ _ _ _ _ _ _ hj]
  · have h0 := zero_of_one χ χ' (crC j) (by simp [crC, hj]) h
    have hcv := chalVJ8_agree b χ χ' h0
    have hα : InhabJ8Comp.αC0 b χ = InhabJ8Comp.αC0 b χ' := by
      rw [InhabJ8Comp.αC0_eq, InhabJ8Comp.αC0_eq, h0 _ rfl]
    have hγ : InhabJ8Comp.γC0 b χ = InhabJ8Comp.γC0 b χ' := by
      rw [InhabJ8Comp.γC0_eq, InhabJ8Comp.γC0_eq, h0 _ rfl]
    rw [trX_pub δ b _ _ _ _ (InhabJ8Comp.pubC0 δ b (H0 p) χ) (InhabJ8Comp.pubC0 δ b (H0 p) χ'), hcv, hα, hγ]

end Comp

/-! ## 3. Column-function congruences of the three memory twins -/

section ColCong
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {n : ℕ}

/-- `cellChipHQKW`'s column function at `j < 188` reads `col` only at base columns `< 129` and (for `j ≥ 134`) at
`j − 5`; never the handle inverse / accumulator fills. -/
theorem colW_cong (col col' : ℕ → Fin n → F) (mhv kbLv kbRv : Fin n → F) (iv av iv' av' : Fin n → Quad (algebraMap F K δF))
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

/-- `cellTraceHQ`'s column function at `j < 184` reads `col` only at `j` (`j < 129`) or `j − 1` (`j ≥ 130`). -/
theorem colHQ_cong (col col' : ℕ → Fin n → F) (mhv : Fin n → F) (iv av iv' av' : Fin n → Quad (algebraMap F K δF))
    (j : ℕ) (hj : j < 184) (hb : j < 129 → col j = col' j) (hr : 130 ≤ j → col (j - 1) = col' (j - 1)) :
    CellTraceHQ.colHQ δF b col mhv iv av j = CellTraceHQ.colHQ δF b col' mhv iv' av' j := by
  have hW : (cellTemplate δF).width 3 = 225 := CellTraceH.cellTemplate_width δF
  funext i
  simp only [CellTraceHQ.colHQ, extColF, hW]
  by_cases h1 : j < 129
  · simp only [if_pos h1, hb h1]
  · simp only [if_neg h1]
    by_cases h2 : j < 130
    · simp only [if_pos h2, CellTraceHQ.new]
      split_ifs <;> first | rfl | omega
    · have h3 : j < 225 + (130 - 129) := by omega
      simp only [if_neg h2, if_pos h3, hr (by omega)]

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

end ColCong

/-! ## 4. The cell, walk and atom traces are staged -/

section Mem
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The honest cell rows' columns `< 183`: base columns coin-free, fingerprint roles read `z′` only. -/
theorem cvalsCol (γ ρ γ' ρ' z z' : 𝕂′) (k : ℕ) (hk : k < 183) (hz : 129 ≤ k → z = z') :
    cellCol δ b (cvals δ γ ρ z μ0.mv μ0.mx μ0.mx1) k = cellCol δ b (cvals δ γ' ρ' z' μ0.mv μ0.mx μ0.mx1) k := by
  funext i
  exact cellCol_round1 b γ ρ γ' ρ' (crow δ z μ0.mv μ0.mx μ0.mx1) (crow δ z' μ0.mv μ0.mx μ0.mx1) k
    (fun _ _ => rfl) (fun h _ _ _ => by rw [hz h]) i hk

/-- **The cell trace is staged.** -/
theorem stM (hdvd : 3 * 2 ^ 1 ∣ p - 1) (Rt : ℕ → Nock.Jet.Autogen.Tpl) :
    StagedCols frameJ8 crM (fun χ => (trJ0 δ b hdvd Rt χ : TrJ8 (ZMod p)).M) := by
  intro j χ χ' h
  by_cases h2 : 188 ≤ (j : ℕ)
  · rw [all_of_two χ χ' (crM j) (by simp only [crM]; split_ifs <;> omega) h]
  · show trMJ δ b hdvd χ μ0 j = trMJ δ b hdvd χ' μ0 j
    unfold trMJ InhabJ8MemCell.trM0 HonestKW.cellTraceHQKW
    refine honestQ_congr _ _ _ _ _ _ ?_
    refine colW_cong δ b _ _ _ _ _ _ _ _ _ _ (by omega) (fun k hk => cvalsCol δ b _ _ _ _ _ _ k (by omega)
      (fun h => absurd h (by omega))) (fun hj => cvalsCol δ b _ _ _ _ _ _ _ (by omega) (fun _ => ?_))
    exact zJ_agree δ χ χ' (zero_of_one χ χ' (crM j) (by simp only [crM]; split_ifs <;> omega) h)

/-- The honest walk row's columns `< 93`: base coin-free, fingerprint roles read `z′` only. -/
theorem wcolCol (chals chals' : ℕ → K) (γ ρ γ' ρ' z z' : 𝕂′) (k : ℕ) (hk : k < 93) (hz : 21 ≤ k → z = z') :
    wcol δ b chals γ ρ z μ0.mL μ0.mR k = wcol δ b chals' γ' ρ' z' μ0.mL μ0.mR k := by
  funext i
  unfold wcol walkCol
  by_cases h1 : k < 21
  · simp only [if_pos h1]; rfl
  · simp only [if_neg h1]
    obtain rfl := hz (by omega)
    congr 1
    unfold wroleVal
    have hρ : (k - 21) / 3 < 24 := by omega
    simp only [hρ, if_true]
    have e : ∀ s, (wvals δ γ ρ (chals 0) z μ0.mL μ0.mR i).fpSlot s =
        (wvals δ γ' ρ' (chals' 0) z μ0.mL μ0.mR i).fpSlot s := fun s => fpSlot_congr _ _ rfl rfl rfl rfl s
    rw [e]

/-- **The J-8 walk trace is staged.** -/
theorem stW (hdvd : 3 * 2 ^ 1 ∣ p - 1) (Rt : ℕ → Nock.Jet.Autogen.Tpl) :
    StagedCols frameJ8 crW (fun χ => (trJ0 δ b hdvd Rt χ : TrJ8 (ZMod p)).W) := by
  intro j χ χ' h
  by_cases h2 : 97 ≤ (j : ℕ)
  · rw [all_of_two χ χ' (crW j) (by simp only [crW]; split_ifs <;> omega) h]
  · show trWJ δ b hdvd χ μ0 j = trWJ δ b hdvd χ' μ0 j
    unfold trWJ trW0
    refine honestQ_congr _ _ _ _ _ _ ?_
    funext i
    unfold HonestK8.certUp
    split_ifs with hc
    · rfl
    · refine congrFun (walkColHQ_cong δ b 1 _ _ _ _ _ _ _ _ j (by omega)
        (fun hj => wcolCol δ b _ _ _ _ _ _ _ _ j (by omega) (fun h' => absurd h' (by omega)))
        (fun hj => wcolCol δ b _ _ _ _ _ _ _ _ _ (by omega) (fun _ => ?_))) i
      exact zJ_agree δ χ χ' (zero_of_one χ χ' (crW j) (by simp only [crW]; split_ifs <;> omega) h)

/-- The pad row's cell columns `< 183`: base coin-free, fingerprint roles read the seed only. -/
theorem padColCol {n : ℕ} (γ ρ γ' ρ' z z' : 𝕂′) (k : ℕ) (hk : k < 183) (hz : 129 ≤ k → z = z') :
    (padCol δ b γ ρ z : ℕ → Fin n → ZMod p) k = padCol δ b γ' ρ' z' k := by
  funext i
  exact cellCol_round1 b γ ρ γ' ρ' (fun _ => padRow δ z) (fun _ => padRow δ z') k
    (fun _ _ => rfl) (fun h _ _ _ => by rw [hz h]) i hk

/-- **The atom-table trace is staged.** -/
theorem stA (hdvd : 3 * 2 ^ 1 ∣ p - 1) (Rt : ℕ → Nock.Jet.Autogen.Tpl) :
    StagedCols frameJ8 crA (fun χ => (trJ0 δ b hdvd Rt χ : TrJ8 (ZMod p)).A) := by
  intro j χ χ' h
  by_cases h2 : 259 ≤ (j : ℕ)
  · rw [all_of_two χ χ' (crA j) (by simp only [crA]; split_ifs <;> omega) h]
  · show trA0 δ b (PbJ hdvd Rt).hnA (PbJ hdvd Rt).nodesA (PbJ hdvd Rt).orbitA χ j =
      trA0 δ b (PbJ hdvd Rt).hnA (PbJ hdvd Rt).nodesA (PbJ hdvd Rt).orbitA χ' j
    unfold trA0 padTraceA HonestA8.atomTraceHQ
    refine honestQ_congr _ _ _ _ _ _ ?_
    have hW : (cellTemplateHQ δ).width 3 = 238 := CellTraceHQ.cellTemplateHQ_width δ
    funext i
    simp only [HonestA8.colA, extColF, hW, Fin.val_cast]
    by_cases h1 : (j : ℕ) < 130
    · simp [h1]
      refine congrFun (colHQ_cong δ b _ _ _ _ _ _ _ _ (by omega)
        (fun hj => padColCol δ b _ _ _ _ _ _ _ (by omega) (fun h' => absurd h' (by omega)))
        (fun hj => absurd hj (by omega))) i
    · simp [h1]
      by_cases h3 : (j : ℕ) < 205
      · simp only [if_pos h3, HonestA8.newFull, if_pos (show (j : ℕ) < 313 by omega)]
      · have h4 : (j : ℕ) < 238 + (205 - 130) := by omega
        simp only [if_neg h3, if_pos h4]
        refine congrFun (colHQ_cong δ b _ _ _ _ _ _ _ _ (by omega)
          (fun hj => absurd hj (by omega))
          (fun hj => padColCol δ b _ _ _ _ _ _ _ (by omega) (fun _ => ?_))) i
        exact yA_agree δ χ χ' (zero_of_one χ χ' (crA j) (by simp only [crA]; split_ifs <;> omega) h)

/-- **THE HONEST TRACE MAP IS STAGED**: `StJ8 (χ ↦ trJ0 χ)`. -/
theorem trJ0_staged (hdvd : 3 * 2 ^ 1 ∣ p - 1) (Rt : ℕ → Nock.Jet.Autogen.Tpl) :
    StJ8 (fun χ : Coins frameJ8 K => (trJ0 δ b hdvd Rt χ : TrJ8 (ZMod p))) :=
  ⟨stC δ b hdvd Rt, stM δ b hdvd Rt, stW δ b hdvd Rt, stagedCols_const _ _ _, stA δ b hdvd Rt,
    stagedCols_const _ _ _⟩

end Mem

/-! ## 5. Full completeness of the inhabitant -/

section Complete
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **FULL COMPLETENESS OF THE INHABITANT** (`*[[0 0] [0 1]] = [0 0]`, no jets, no big atoms): the honest trace
map `χ ↦ trJ0 χ` is staged (`StJ8`), the honest bad set `badJ0` is a union of `25` events with
`|badJ0| ≤ 25 · |K|^18` (out of `|K|^19` coins), and at every coin outside it `AcceptsJ8V` holds with the honest
message `MJ0 χ` and traces `trJ0 χ` (J chip absent, atom walk absent `krootsV = 0`). -/
theorem inhabitant_staged_complete (hB : Nock.Atoms.B ≤ p) (hdvd : 3 * 2 ^ 1 ∣ p - 1)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) :
    StJ8 (fun χ : Coins frameJ8 K => (trJ0 δ b hdvd Rt χ : TrJ8 (ZMod p))) ∧
      (InhabJ8Good.badJ0 (K := K) δ).card ≤ 25 * Fintype.card K ^ 18 ∧
      Fintype.card (Coins frameJ8 K) = Fintype.card K ^ 19 ∧
      ∀ χ : Coins frameJ8 K, χ ∉ InhabJ8Good.badJ0 δ →
        AcceptsJ8V δ b (PbJ hdvd Rt) R0 c0 χ (MJ0 δ b χ) (trJ0 δ b hdvd Rt χ) rJ0 0 :=
  ⟨trJ0_staged δ b hdvd Rt, (InhabJ8Good.inhabitant_outside_bad δ b hB hdvd Rt).1, InhabJ8Good.card_coins,
    (InhabJ8Good.inhabitant_outside_bad δ b hB hdvd Rt).2⟩

/-- **At Goldilocks** (`p = Nock.Atoms.p`), with the atom walk absent, the J chip absent and the claim true. -/
theorem inhabitant_staged_complete_goldilocks (hpG : p = Nock.Atoms.p) (Rt : ℕ → Nock.Jet.Autogen.Tpl) :
    ∃ (Pb : PubJ8 p) (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (M : Coins frameJ8 K → MsgJ8' p K δ)
      (bad : Finset (Coins frameJ8 K)),
      StJ8 Q ∧ bad.card ≤ 25 * Fintype.card K ^ 18 ∧
      (∀ χ, χ ∉ bad → AcceptsJ8V δ b Pb R0 c0 χ (M χ) (Q χ) rJ0 0) ∧
      Pb.krootsV = 0 ∧ Pb.nJ = 0 ∧ Pb.regs = [] ∧ Nock.Jet.HoldsN c0 := by
  have hB : Nock.Atoms.B ≤ p := by
    rw [hpG, show Nock.Atoms.B = 2 ^ 32 from rfl, show Nock.Atoms.p = Nock.Field.p from rfl, Nock.Field.p_eq]
    norm_num
  have hdvd : 3 * 2 ^ 1 ∣ p - 1 := by
    rw [hpG, show Nock.Atoms.p = Nock.Field.p from rfl, Nock.Field.p_eq, Nat.dvd_iff_mod_eq_zero]
    norm_num
  obtain ⟨hst, hcard, -, hacc⟩ := inhabitant_staged_complete δ b hB hdvd Rt
  exact ⟨PbJ hdvd Rt, fun χ => trJ0 δ b hdvd Rt χ, fun χ => MJ0 δ b χ, InhabJ8Good.badJ0 δ, hst, hcard, hacc,
    rfl, rfl, rfl, ⟨1, evalN0⟩⟩

end Complete

end

end Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Stage
