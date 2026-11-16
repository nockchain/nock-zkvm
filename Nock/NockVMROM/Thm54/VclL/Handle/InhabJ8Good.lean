/-
  Nock/NockVMROM/Thm54/VclL/Handle/InhabJ8Good.lean

  **Completeness of THE inhabitant at EVERY good coin.**

  NV3b (`InhabJ8Main.inhabitant`) proved `AcceptsJ8V` for the honest run of `*[[0 0] [0 1]] = [0 0]` at ONE coin
  `χ0`.  Here the coin is arbitrary:

  * **`GoodJ0 χ`**: the twenty-five honest non-vanishing conditions, every one named (compute `2`, cell `9`, walk `6`,
    atom table `8`): `αW ≠ 0`, `z′ ≠ 0`, `y ≠ 0`, `ρH′ ≠ 0`, and twenty-one LogUp denominators `pole + (pole-free)`.
  * **`inhabitant_of_good`**: `GoodJ0 χ → AcceptsJ8V … χ (MJ0 χ) (trJ0 χ) …` (the inhabitant's proof with `χ0`'s
    `SimpleCoins` / `CoinsA` replaced by the general per-chip denominator hypotheses).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Main

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Good

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Static
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemDom
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemCell
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemWalk
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemMain
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Atom
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Main
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)

noncomputable section

/-! ## 1. The good coins and acceptance at every good coin -/

section Good
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The honest good-coin conditions** (every denominator of the honest run that the per-chip acceptance
theorems need non-zero). -/
structure GoodJ0 (χ : Coins frameJ8 K) : Prop where
  -- compute
  hα : χ ⟨13, by decide⟩ ≠ 0
  hdn : compress (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′)
    (liftRec (L := 𝕂′) (InhabJ8Comp.recF0 (p := p) (K := K) (H0 p))) ≠ 0
  -- cell
  hz : zJ δ χ ≠ 0
  hv : ∀ j < 2, compress (m := 5) ⟨γV δ χ, ρV δ χ⟩ (vKeyOf δ (crow δ (zJ δ χ) μ0.mv μ0.mx μ0.mx1 j)) ≠ 0
  hx0 : ∀ j < 2, compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (xKeyOf δ (crow δ (zJ δ χ) μ0.mv μ0.mx μ0.mx1 j) 0) ≠ 0
  hx1 : ∀ j < 2, compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (xKeyOf δ (crow δ (zJ δ χ) μ0.mv μ0.mx μ0.mx1 j) 1) ≠ 0
  hH : ∀ j < 2, dKW δ (chalsMJ8 δ χ) j ≠ 0
  -- walk
  hwx : compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (wxKeyV δ (wrow δ (chalsMJ8 δ χ 0) (zJ δ χ) μ0.mL μ0.mR)) ≠ 0
  hwL : compress (m := 8) ⟨γV δ χ, ρV δ χ⟩ (wrecLV δ (wrow δ (chalsMJ8 δ χ 0) (zJ δ χ) μ0.mL μ0.mR)) ≠ 0
  hwR : compress (m := 8) ⟨γV δ χ, ρV δ χ⟩ (wrecRV δ (wrow δ (chalsMJ8 δ χ 0) (zJ δ χ) μ0.mL μ0.mR)) ≠ 0
  hpX : hden δ (chalsMJ8 δ χ) 5 vX ≠ 0
  hpL : hden δ (chalsMJ8 δ χ) 4 vPL ≠ 0
  hpR : hden δ (chalsMJ8 δ χ) 4 vPR ≠ 0
  -- atom table
  hA : CoinsA δ χ

variable [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **THE INHABITANT AT EVERY GOOD COIN**: the honest run of `*[[0 0] [0 1]] = [0 0]` (no jets, no big atoms) is
ACCEPTED by `AcceptsJ8V` at every coin `χ` with `GoodJ0 χ`, with the honest message `MJ0 χ` and the honest traces
`trJ0 χ` (J chip and atom walk absent, the atom table one inert pad row). -/
theorem inhabitant_of_good (hB : Nock.Atoms.B ≤ p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) (Rt : ℕ → Nock.Jet.Autogen.Tpl)
    (χ : Coins frameJ8 K) (hg : GoodJ0 δ χ) :
    AcceptsJ8V δ b (PbJ hdvd Rt) R0 c0 χ (MJ0 δ b χ) (trJ0 δ b hdvd Rt χ) rJ0 0 := by
  have hBp : 2 ^ 32 ≤ p := hB
  have hp2 : 2 ≤ p := le_trans (by norm_num) hBp
  exact
  { hsatX := InhabJ8Comp.hsatX_c0_qX δ b (H0 p) (hdlOK_H0 p) hB χ hg.hα hg.hdn (PbJ hdvd Rt)
      (trJ0 δ b hdvd Rt χ) rfl rfl
    hinjX := fun a c _ => Fin.ext (by
      have h1 : (a : ℕ) < 1 := a.isLt
      have h2 : (c : ℕ) < 1 := c.isLt
      omega)
    hadjX := fun i hi => absurd (show (i : ℕ) + 1 < 1 from hi) (by omega)
    hsatC := memC_sat δ b (PbBase hdvd Rt) hdvd _ χ μ0 _ rfl rfl hg.hz hg.hv hg.hx0 hg.hx1 hg.hH
    hbindC := memC_bind δ b (PbBase hdvd Rt) hdvd _ χ μ0 _ rfl rfl
    hinjC := memC_inj (PbBase hdvd Rt) hdvd
    hadjC := memC_adj (PbBase hdvd Rt) hdvd
    hnpC := memC_np (PbBase hdvd Rt) hdvd
    hsatW := memW_sat δ b (PbBase hdvd Rt) hdvd _ χ μ0 _ rfl rfl hg.hwx hg.hwL hg.hwR hg.hpX hg.hpL hg.hpR
    hbindW := memW_bind δ b (PbBase hdvd Rt) hdvd _ χ μ0 _ rfl rfl hg.hwx hg.hwL hg.hwR hg.hpX hg.hpL hg.hpR
    hinjW := memW_inj (PbBase hdvd Rt) hdvd
    hadjW := memW_adj (PbBase hdvd Rt) hdvd
    hkW := memW_k (PbBase hdvd Rt) hdvd
    hknW := memW_kn (PbBase hdvd Rt) hdvd
    hkpW := memW_kp (PbBase hdvd Rt) hdvd
    hJk := jchip_absent δ b _ _ _ _ _ _ rfl ⟨rfl, rfl, rfl, rfl⟩
    hsatA := hsatA_A0 (PbJ hdvd Rt) rfl _ χ rfl hg.hA _ rfl
    hbindA := hbindA_A0 (PbJ hdvd Rt) _ χ rfl _ rfl
    hinjA := hinjA_A0 (PbJ hdvd Rt) rfl
    hadjA := hadjA_A0 (PbJ hdvd Rt) rfl
    hnpA := hnpA_A0 (PbJ hdvd Rt) rfl
    hVk := Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    hGx := hGx0 δ b hp2 χ
    hGp := hGp0 δ b χ
    hGS := by
      show InhabJ8Comp.ρSC0 δ b (H0 p) χ + _ + _ = _
      rw [InhabJ8Comp.ρSC0_eq]
      simp [PbJ, PbBase, withMem, MJ0, Nock.Jet.PinJ8.pinCons, pubsA0, Quad.mk_zero']
    hlay := hlay0 (PbJ hdvd Rt) rfl rfl rfl
    hsmall := hsmall0 (PbJ hdvd Rt) rfl rfl
    huniq := huniq0 (PbJ hdvd Rt) rfl rfl
    hTpl := regs_vacuous (PbJ hdvd Rt) rfl
    hnd := hnd0 (PbJ hdvd Rt) rfl
    hidx := regs_vacuous (PbJ hdvd Rt) rfl
    hrk := regs_vacuous (PbJ hdvd Rt) rfl
    hlt := regs_vacuous (PbJ hdvd Rt) rfl
    hsumC' := by
      rw [show (MJ0 δ b χ).m = InhabJ8Comp.mC0 (H0 p) from rfl, show (MJ0 δ b χ).pubsC = pubsC0 δ χ μ0 from rfl,
        show (MJ0 δ b (K := K) χ).pubsA = pubsA0 from rfl,
        claimSum0 δ χ μ0 (InhabJ8Comp.mC0 (H0 p)) (fun k => rfl) rfl rfl (PbJ hdvd Rt) rfl]
      simp [pubsA0, Quad.mk_zero']
    hbalA' := by simp [MJ0, pubsA0, Quad.mk_zero']
    hvalA0 := hvalA0_A0
    hfxC := hfxC0 δ χ μ0 rfl rfl rfl rfl
    hfxA := ⟨rfl, rfl⟩
    hclA := hclA0 p
    hclI := fun k _ => by
      show (H0 p (claimNoun c0 k)).2 < p
      rw [claimNoun_c0]
      split_ifs
      · rw [H0_f0]; omega
      · rw [H0_s0]; omega
    hclR := hclR0 p (by omega)
    hcen := hcen0 (PbJ hdvd Rt) rfl hp2
    hlenC := by show 3 + 0 + 2 * 2 < p; omega
    hlenA := by show 1 + 1 < p; omega
    hcellF := hcellF0
    hnA62 := by show 1 ≤ 2 ^ 62; norm_num
    hbud := hbud0 (PbJ hdvd Rt) rJ0 _ rfl rfl (by simp [PbJ, PbBase, withMem, rJ0])
      (by simp [PbJ, PbBase, withMem, rJ0]) (by simp [PbJ, PbBase, withMem, rJ0])
      (by simp [PbJ, PbBase, withMem, rJ0]) (by simp [PbJ, PbBase, withMem, rJ0])
      (by simp [PbJ, PbBase, withMem, rJ0])
    hbudV := ⟨le_refl _, by simp [PbJ, PbBase, withMem, rJ0], by simp [PbJ, PbBase, withMem, rJ0],
      by simp [PbJ, PbBase, withMem, rJ0]⟩
    hsatL := hsatL_A0 (PbJ hdvd Rt) rfl _ χ rfl hg.hA _ rfl
    hbindL := hbindL_A0 (PbJ hdvd Rt) _ χ rfl _ rfl }

end Good

/-! ## 2. -/

section Card
variable {K : Type} [Fintype K] [DecidableEq K]

theorem card_pin [Zero K] (i : Fin frameJ8.n) (g : Coins frameJ8 K → K)
    (hg : ∀ χ χ' : Coins frameJ8 K, (∀ k, k ≠ i → χ k = χ' k) → g χ = g χ') :
    (Finset.univ.filter fun χ : Coins frameJ8 K => χ i = g χ).card ≤ Fintype.card K ^ 18 := by
  let i' : Fin (18 + 1) := i
  let φ : Coins frameJ8 K → (Fin 18 → K) := fun χ k => χ (i'.succAbove k)
  have hinj : Set.InjOn φ ↑(Finset.univ.filter fun χ : Coins frameJ8 K => χ i = g χ) := by
    intro χ hχ χ' hχ' he
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hχ hχ'
    have hoff : ∀ k, k ≠ i → χ k = χ' k := by
      intro k hk
      obtain ⟨k', hk'⟩ := Fin.exists_succAbove_eq (x := (k : Fin (18 + 1))) (y := i') hk
      have := congrFun he k'
      simp only [φ] at this
      rw [hk'] at this
      exact this
    funext k
    by_cases hk : k = i
    · subst hk; rw [hχ, hχ', hg χ χ' hoff]
    · exact hoff k hk
  have h := Finset.card_le_card_of_injOn φ (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h
  exact h

theorem card_coins : Fintype.card (Coins frameJ8 K) = Fintype.card K ^ 19 := by
  rw [Fintype.card_fun, Fintype.card_fin]; rfl

theorem card_foldr_le {α : Type} [DecidableEq α] (L : List (Finset α)) (B : ℕ) (h : ∀ s ∈ L, s.card ≤ B) :
    (L.foldr (· ∪ ·) ∅).card ≤ L.length * B := by
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.foldr_cons, List.length_cons]
    have h1 := h s (List.mem_cons_self ..)
    have h2 := ih fun t ht => h t (List.mem_cons_of_mem _ ht)
    calc (s ∪ L.foldr (· ∪ ·) ∅).card ≤ s.card + (L.foldr (· ∪ ·) ∅).card := Finset.card_union_le _ _
      _ ≤ B + L.length * B := Nat.add_le_add h1 h2
      _ = (L.length + 1) * B := by ring

theorem mem_foldr {α : Type} [DecidableEq α] (L : List (Finset α)) (x : α) (s : Finset α) (hs : s ∈ L)
    (hx : x ∈ s) : x ∈ L.foldr (· ∪ ·) ∅ := by
  induction L with
  | nil => simp at hs
  | cons t L ih =>
    simp only [List.foldr_cons, Finset.mem_union]
    rcases List.mem_cons.mp hs with rfl | hs
    · exact Or.inl hx
    · exact Or.inr (ih hs)

end Card

section Bad
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The coin `χ₁₂` (real part of the handle pole `ρH′`). -/
abbrev c12 : Fin frameJ8.n := ⟨12, by decide⟩

/-- The validity-pole event of a pole-free part `x`: `χ₅ = −Re x` (i.e. the real part of `ρ′ + x` vanishes). -/
def evV (x : Coins frameJ8 K → 𝕂′) : Finset (Coins frameJ8 K) :=
  Finset.univ.filter fun χ => χ c5 = -(Quad.re _ (x χ))

/-- The handle-pole event of a pole-free part `x`: `χ₁₂ = −Re x`. -/
def evH (x : Coins frameJ8 K → 𝕂′) : Finset (Coins frameJ8 K) :=
  Finset.univ.filter fun χ => χ c12 = -(Quad.re _ (x χ))

/-- A coin-vanishing event `χ_i = 0`. -/
def evC (i : Fin frameJ8.n) : Finset (Coins frameJ8 K) :=
  Finset.univ.filter fun χ => χ i = 0

theorem pole_pin (a r : K) (x : 𝕂′) (h : Quad.mk _ a r + x = 0) : a = -(Quad.re _ x) := by
  rw [← Quad.mk_re_im _ x, Quad.mk_add, Quad.mk_eq_zero_iff] at h
  exact eq_neg_of_add_eq_zero_left h.1

theorem compress_split {m : ℕ} (γ ρ : 𝕂′) (v : Fin m → 𝕂′) :
    compress (⟨γ, ρ⟩ : IOCoins 𝕂′) v = ρ + compress (⟨γ, 0⟩ : IOCoins 𝕂′) v := by
  simp [compress]

theorem card_evV (x : Coins frameJ8 K → 𝕂′)
    (hx : ∀ χ χ' : Coins frameJ8 K, (∀ k, k ≠ c5 → χ k = χ' k) → x χ = x χ') :
    (evV δ x).card ≤ Fintype.card K ^ 18 :=
  card_pin c5 (fun χ => -(Quad.re _ (x χ))) fun χ χ' h => by simp only [hx χ χ' h]

theorem card_evH (x : Coins frameJ8 K → 𝕂′)
    (hx : ∀ χ χ' : Coins frameJ8 K, (∀ k, k ≠ c12 → χ k = χ' k) → x χ = x χ') :
    (evH δ x).card ≤ Fintype.card K ^ 18 :=
  card_pin c12 (fun χ => -(Quad.re _ (x χ))) fun χ χ' h => by simp only [hx χ χ' h]

theorem card_evC (i : Fin frameJ8.n) : (evC (K := K) i).card ≤ Fintype.card K ^ 18 :=
  card_pin i (fun _ => 0) fun _ _ _ => rfl


theorem chalsMJ8_zero (χ : Coins frameJ8 K) : chalsMJ8 δ χ 0 = χ ⟨0, by decide⟩ := by
  rw [ProbJ8.chalsMJ8_lo δ χ 0 (by norm_num)]
  simp [chalsVS, chalsVCL, toVCL, toVS, toVSQ, CellH.hGam, CellH.hRho]

theorem mk_agree (χ χ' : Coins frameJ8 K) (i a c : Fin frameJ8.n) (ha : a ≠ i) (hc : c ≠ i)
    (h : ∀ k, k ≠ i → χ k = χ' k) :
    Quad.mk (algebraMap (ZMod p) K δ) (χ a) (χ c) = Quad.mk _ (χ' a) (χ' c) := by
  rw [h a ha, h c hc]

/-- Off `χ₅`: every reader of the validity-pole-free parts agrees. -/
theorem agree5 (χ χ' : Coins frameJ8 K) (h : ∀ k, k ≠ c5 → χ k = χ' k) :
    γV δ χ = γV δ χ' ∧ zJ δ χ = zJ δ χ' ∧ chalsMJ8 δ χ 0 = chalsMJ8 δ χ' 0 ∧ yA δ χ = yA δ χ' ∧
      γA δ χ = γA δ χ' ∧ zA δ χ = zA δ χ' := by
  refine ⟨mk_agree δ χ χ' c5 c4 c6 (by decide) (by decide) h, mk_agree δ χ χ' c5 c2 c3 (by decide) (by decide) h,
    ?_, mk_agree δ χ χ' c5 cY1 cY2 (by decide) (by decide) h, mk_agree δ χ χ' c5 c4 c6 (by decide) (by decide) h,
    mk_agree δ χ χ' c5 c2 c3 (by decide) (by decide) h⟩
  rw [chalsMJ8_zero, chalsMJ8_zero, h _ (by decide)]

/-- Off `χ₁₂`: the handle RLC coin agrees. -/
theorem agree12 (χ χ' : Coins frameJ8 K) (h : ∀ k, k ≠ c12 → χ k = χ' k) :
    gamHQ δ (toVSQ χ) = gamHQ δ (toVSQ χ') := by
  show Quad.mk _ (χ ⟨11, by decide⟩) (χ ⟨15, by decide⟩) = Quad.mk _ (χ' ⟨11, by decide⟩) (χ' ⟨15, by decide⟩)
  rw [h _ (by decide), h _ (by decide)]

/-! ### The twenty-one pole-free parts -/

/-- Cell validity key of row `j`. -/
def xv (j : ℕ) (χ : Coins frameJ8 K) : 𝕂′ :=
  compress (⟨γV δ χ, 0⟩ : IOCoins 𝕂′) (vKeyOf δ (crow δ (zJ δ χ) μ0.mv μ0.mx μ0.mx1 j))
/-- Cell export key of row `j`, selector `s`. -/
def xx (j : ℕ) (s : ZMod p) (χ : Coins frameJ8 K) : 𝕂′ :=
  compress (⟨γV δ χ, 0⟩ : IOCoins 𝕂′) (xKeyOf δ (crow δ (zJ δ χ) μ0.mv μ0.mx μ0.mx1 j) s)
/-- Walk import key. -/
def xwx (χ : Coins frameJ8 K) : 𝕂′ :=
  compress (⟨γV δ χ, 0⟩ : IOCoins 𝕂′) (wxKeyV δ (wrow δ (chalsMJ8 δ χ 0) (zJ δ χ) μ0.mL μ0.mR))
def xwL (χ : Coins frameJ8 K) : 𝕂′ :=
  compress (⟨γV δ χ, 0⟩ : IOCoins 𝕂′) (wrecLV δ (wrow δ (chalsMJ8 δ χ 0) (zJ δ χ) μ0.mL μ0.mR))
def xwR (χ : Coins frameJ8 K) : 𝕂′ :=
  compress (⟨γV δ χ, 0⟩ : IOCoins 𝕂′) (wrecRV δ (wrow δ (chalsMJ8 δ χ 0) (zJ δ χ) μ0.mL μ0.mR))
/-- Atom-table pad-row keys (`CoinsA.hV hX0 hX1 hMB`). -/
def xaV (χ : Coins frameJ8 K) : 𝕂′ :=
  yA δ χ ^ 2 + (γA δ χ * yA δ χ + (γA δ χ ^ 2 * yA δ χ + γA δ χ ^ 3))
def xaX0 (χ : Coins frameJ8 K) : 𝕂′ :=
  yA δ χ ^ 2 + (γA δ χ * yA δ χ + (γA δ χ ^ 2 * yA δ χ + (γA δ χ ^ 3 * yA δ χ +
    (γA δ χ ^ 6 * yA δ χ + γA δ χ ^ 8))))
def xaX1 (χ : Coins frameJ8 K) : 𝕂′ :=
  yA δ χ ^ 2 + (γA δ χ * yA δ χ + (γA δ χ ^ 2 * yA δ χ + (γA δ χ ^ 3 * yA δ χ +
    (γA δ χ ^ 6 * yA δ χ + (γA δ χ ^ 8 + γA δ χ ^ 10)))))
def xaMB (χ : Coins frameJ8 K) : 𝕂′ := zA δ χ + γA δ χ ^ 2 * yA δ χ
/-- The compute row's handle key. -/
def xhC (χ : Coins frameJ8 K) : 𝕂′ :=
  compress (⟨gamHQ δ (toVSQ χ), 0⟩ : IOCoins 𝕂′) (liftRec (L := 𝕂′) (InhabJ8Comp.recF0 (p := p) (K := K) (H0 p)))
/-- The cell handle key of row `j`. -/
def xhK (j : ℕ) (χ : Coins frameJ8 K) : 𝕂′ :=
  compress (⟨gamHQ δ (toVSQ χ), 0⟩ : IOCoins 𝕂′)
    (liftRec (K := K) (L := 𝕂′) fun c => algebraMap (ZMod p) K (kRow (F := ZMod p) j c))
/-- A walk handle key of length `m`. -/
def xhW (m : ℕ) (v : ℕ → ZMod p) (χ : Coins frameJ8 K) : 𝕂′ :=
  compress (⟨gamHQ δ (toVSQ χ), 0⟩ : IOCoins 𝕂′) (liftRec (K := K) (L := 𝕂′) fun c : Fin m => algebraMap (ZMod p) K (v c))
/-- Atom-table handle keys (`CoinsA.hH hMI`). -/
def xaH (χ : Coins frameJ8 K) : 𝕂′ := gamHQ δ (toVSQ χ) ^ 4
def xaMI (χ : Coins frameJ8 K) : 𝕂′ := 2 + (2 * gamHQ δ (toVSQ χ) ^ 2 + 4 * gamHQ δ (toVSQ χ) ^ 4)

/-- The thirteen validity-pole-free parts. -/
def xsV : List (Coins frameJ8 K → 𝕂′) :=
  [xv δ 0, xv δ 1, xx δ 0 0, xx δ 1 0, xx δ 0 1, xx δ 1 1, xwx δ, xwL δ, xwR δ, xaV δ, xaX0 δ, xaX1 δ, xaMB δ]

/-- The eight handle-pole-free parts. -/
def xsH : List (Coins frameJ8 K → 𝕂′) :=
  [xhC δ, xhK δ 0, xhK δ 1, xhW δ 5 vX, xhW δ 4 vPL, xhW δ 4 vPR, xaH δ, xaMI δ]

/-- The four coin-vanishing coordinates: `αW = χ₁₃`, `Re z′ = χ₂`, `Re y = χ₁₇`, `Re ρH′ = χ₁₂`. -/
def csJ0 : List (Fin frameJ8.n) := [⟨13, by decide⟩, c2, cY1, c12]

/-- **The honest bad events of the inhabitant**: `25` sets. -/
def badList : List (Finset (Coins frameJ8 K)) :=
  (xsV δ).map (evV δ) ++ (xsH δ).map (evH δ) ++ csJ0.map evC

/-- **The honest bad set**: the union of `badList`. -/
def badJ0 : Finset (Coins frameJ8 K) := (badList δ).foldr (· ∪ ·) ∅

theorem badList_length : (badList (K := K) δ).length = 25 := rfl

theorem xsV_reads : ∀ x ∈ xsV δ, ∀ χ χ' : Coins frameJ8 K, (∀ k, k ≠ c5 → χ k = χ' k) → x χ = x χ' := by
  simp only [xsV, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro χ χ' h <;>
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := agree5 δ χ χ' h
  · unfold xv; rw [e1, e2]
  · unfold xv; rw [e1, e2]
  · unfold xx; rw [e1, e2]
  · unfold xx; rw [e1, e2]
  · unfold xx; rw [e1, e2]
  · unfold xx; rw [e1, e2]
  · unfold xwx; rw [e1, e2, e3]
  · unfold xwL; rw [e1, e2, e3]
  · unfold xwR; rw [e1, e2, e3]
  · unfold xaV; rw [e4, e5]
  · unfold xaX0; rw [e4, e5]
  · unfold xaX1; rw [e4, e5]
  · unfold xaMB; rw [e4, e5, e6]

theorem xsH_reads : ∀ x ∈ xsH δ, ∀ χ χ' : Coins frameJ8 K, (∀ k, k ≠ c12 → χ k = χ' k) → x χ = x χ' := by
  simp only [xsH, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro χ χ' h <;> have e := agree12 δ χ χ' h
  · unfold xhC; rw [e]
  · unfold xhK; rw [e]
  · unfold xhK; rw [e]
  · unfold xhW; rw [e]
  · unfold xhW; rw [e]
  · unfold xhW; rw [e]
  · unfold xaH; rw [e]
  · unfold xaMI; rw [e]

theorem card_badJ0 : (badJ0 (K := K) δ).card ≤ 25 * Fintype.card K ^ 18 := by
  rw [← badList_length (K := K) δ]
  refine card_foldr_le _ _ fun s hs => ?_
  simp only [badList, List.mem_append, List.mem_map] at hs
  rcases hs with (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨i, -, rfl⟩
  · exact card_evV δ x (xsV_reads δ x hx)
  · exact card_evH δ x (xsH_reads δ x hx)
  · exact card_evC i

/-! ### Outside the bad set every honest denominator is non-zero -/

theorem mem_badJ0 {χ : Coins frameJ8 K} {s : Finset (Coins frameJ8 K)} (hs : s ∈ badList δ) (hχ : χ ∈ s) :
    χ ∈ badJ0 δ :=
  mem_foldr _ χ s hs hχ

theorem inV {χ : Coins frameJ8 K} {x : Coins frameJ8 K → 𝕂′} (hx : x ∈ xsV δ) (h : ρV δ χ + x χ = 0) :
    χ ∈ badJ0 δ :=
  mem_badJ0 δ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hx)))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, pole_pin δ _ _ _ h⟩)

theorem inH {χ : Coins frameJ8 K} {x : Coins frameJ8 K → 𝕂′} (hx : x ∈ xsH δ)
    (h : rhoHQ δ (toVSQ χ) + x χ = 0) : χ ∈ badJ0 δ :=
  mem_badJ0 δ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hx)))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, pole_pin δ _ _ _ h⟩)

theorem inC {χ : Coins frameJ8 K} {i : Fin frameJ8.n} (hi : i ∈ csJ0) (h : χ i = 0) : χ ∈ badJ0 δ :=
  mem_badJ0 δ (List.mem_append_right _ (List.mem_map_of_mem hi)) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

/-- **Outside `badJ0` the coin is good.** -/
theorem good_of_not_bad (χ : Coins frameJ8 K) (hχ : χ ∉ badJ0 δ) : GoodJ0 δ χ := by
  have mV : ∀ x ∈ xsV δ, ρV δ χ + x χ ≠ 0 := fun x hx h => hχ (inV δ hx h)
  have mH : ∀ x ∈ xsH δ, rhoHQ δ (toVSQ χ) + x χ ≠ 0 := fun x hx h => hχ (inH δ hx h)
  have mC : ∀ i ∈ csJ0, χ i ≠ 0 := fun i hi h => hχ (inC δ hi h)
  have cV : ∀ {m : ℕ} (v : Fin m → 𝕂′) (x : Coins frameJ8 K → 𝕂′), x ∈ xsV δ →
      compress (⟨γV δ χ, 0⟩ : IOCoins 𝕂′) v = x χ → compress (⟨γV δ χ, ρV δ χ⟩ : IOCoins 𝕂′) v ≠ 0 := by
    intro m v x hx he
    rw [compress_split, he]; exact mV x hx
  have cH : ∀ {m : ℕ} (v : Fin m → 𝕂′) (x : Coins frameJ8 K → 𝕂′), x ∈ xsH δ →
      compress (⟨gamHQ δ (toVSQ χ), 0⟩ : IOCoins 𝕂′) v = x χ →
        compress (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′) v ≠ 0 := by
    intro m v x hx he
    rw [compress_split, he]; exact mH x hx
  have j2 : ∀ j < 2, j = 0 ∨ j = 1 := fun j hj => by omega
  refine
  { hα := mC _ (by simp [csJ0])
    hdn := cH _ (xhC δ) (by simp [xsH]) rfl
    hz := fun h => mC c2 (by simp [csJ0]) ((Quad.mk_eq_zero_iff _ _ _).mp h).1
    hv := fun j hj => ?_
    hx0 := fun j hj => ?_
    hx1 := fun j hj => ?_
    hH := fun j hj => ?_
    hwx := cV _ (xwx δ) (by simp [xsV]) rfl
    hwL := cV _ (xwL δ) (by simp [xsV]) rfl
    hwR := cV _ (xwR δ) (by simp [xsV]) rfl
    hpX := by unfold hden; rw [hcoins_J8]; exact cH _ (xhW δ 5 vX) (by simp [xsH]) rfl
    hpL := by unfold hden; rw [hcoins_J8]; exact cH _ (xhW δ 4 vPL) (by simp [xsH]) rfl
    hpR := by unfold hden; rw [hcoins_J8]; exact cH _ (xhW δ 4 vPR) (by simp [xsH]) rfl
    hA := ?_ }
  · rcases j2 j hj with rfl | rfl
    · exact cV _ (xv δ 0) (by simp [xsV]) rfl
    · exact cV _ (xv δ 1) (by simp [xsV]) rfl
  · rcases j2 j hj with rfl | rfl
    · exact cV _ (xx δ 0 0) (by simp [xsV]) rfl
    · exact cV _ (xx δ 1 0) (by simp [xsV]) rfl
  · rcases j2 j hj with rfl | rfl
    · exact cV _ (xx δ 0 1) (by simp [xsV]) rfl
    · exact cV _ (xx δ 1 1) (by simp [xsV]) rfl
  · unfold dKW; rw [hcoins_J8]
    rcases j2 j hj with rfl | rfl
    · exact cH _ (xhK δ 0) (by simp [xsH]) rfl
    · exact cH _ (xhK δ 1) (by simp [xsH]) rfl
  · refine ⟨fun h => mC cY1 (by simp [csJ0]) ((Quad.mk_eq_zero_iff _ _ _).mp h).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [add_assoc]; exact mV (xaV δ) (by simp [xsV])
    · simp only [add_assoc]; exact mV (xaX0 δ) (by simp [xsV])
    · simp only [add_assoc]; exact mV (xaX1 δ) (by simp [xsV])
    · exact mH (xaH δ) (by simp [xsH])
    · simp only [add_assoc]; exact mV (xaMB δ) (by simp [xsV])
    · intro h; exact mC c12 (by simp [csJ0]) ((Quad.mk_eq_zero_iff _ _ _).mp h).1
    · simp only [add_assoc]; exact mH (xaMI δ) (by simp [xsH])

end Bad

/-! ## 3. Completeness of the inhabitant -/

section Complete
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **Completeness of THE inhabitant**: outside the honest bad set `badJ0` (`|badJ0| ≤ 25 · |K|^18`), the honest
run of `*[[0 0] [0 1]] = [0 0]` is accepted by `AcceptsJ8V` with the honest message and traces at that coin. -/
theorem inhabitant_outside_bad (hB : Nock.Atoms.B ≤ p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) (Rt : ℕ → Nock.Jet.Autogen.Tpl) :
    (badJ0 (K := K) δ).card ≤ 25 * Fintype.card K ^ 18 ∧
      ∀ χ : Coins frameJ8 K, χ ∉ badJ0 δ →
        AcceptsJ8V δ b (PbJ hdvd Rt) R0 c0 χ (MJ0 δ b χ) (trJ0 δ b hdvd Rt χ) rJ0 0 :=
  ⟨card_badJ0 δ, fun χ hχ => inhabitant_of_good δ b hB hdvd Rt χ (good_of_not_bad δ χ hχ)⟩

end Complete

end

end Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Good
