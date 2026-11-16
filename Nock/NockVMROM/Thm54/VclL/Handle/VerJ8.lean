/-
  Nock/NockVMROM/Thm54/VclL/Handle/VerJ8.lean

  New module, additive.

  * Challenge vectors at `χ : Coins frameJ8 K`: the compute's `chalVJ8 = chalVHQ ∘ toVSQ`, the memory chips'
    `chalsMJ8 = chalsVSQ ∘ toVSQ`, and the J chip's `chalsJJ8` (leaves `0..3` and `4..7` both carry
    `(Re γH, Re ρH, Im γH, Im ρH)`).
  * **Coin identification**: `coinsCV_J8` (compute), `mcoins_J8` (cell / walk), `coinsJX_J8` / `coinsJ_J8` (J export /
    tagged) all equal `(γH′, ρH′) = (gamHQ, rhoHQ)` at `toVSQ χ`; `mcoins_of_agree` for any memory vector that agrees
    with `chalsMJ8` at leaves `33..36`.
  * The compute publics `pubVJ8` (`pubVHQ` on `0..26`, `Re ρ_s` at `27..29`, `Im ρ_s` at `30..32`) and its balance
    publics: `rhoX.x = ρ₃`, `rhoX.p = ρ₄`, `rhoX.s = ρ_s` (`rhoX_x_J8`, `rhoX_p_J8`, `rhoX_s_J8`).
  * **`goodCJ8_iff`**: `GoodCJ8 (TprovJ8 …) (TextJ8 …)` at `pubVJ8` is the three concrete equations
    `ρ₃ + (pubW₄, pubW₅) + (pubJ₂, pubJ₃) = (pubC₄, pubC₅)`, `ρ₄ = (pubW₆, pubW₇)`, `ρ_s + TextS = TprovS`.
  * **`balJ8_frameJ8`**: `BalXJ8.balJ8_of_goodJ8` at the frame's vectors, the coin identifications discharged.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.BalXJ8
import Nock.NockVMROM.Thm54.VclL.Handle.BalanceVSQ
import Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.VerJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8 toVSQ)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal computeChipVCLHX pubRhoSX pubRhoSXi)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (balCols)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceVSQ (mcoins coinsCV_VSQ pubX_VSQ pubP_VSQ chalsVSQ_coins)
open Nock.NockVMROM.Thm54.VclL.Handle.BalXJ8 (TprovJ8 TextJ8)
open Nock.Jet.RapJetJ8 (coinsJ coinsJX)

noncomputable section

/-! ## 1. Challenge vectors and coin identification -/

section Coins
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K)

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The compute challenge vector at `frameJ8`. -/
def chalVJ8 (χ : Coins frameJ8 K) : ℕ → F := chalVHQ b (toVSQ χ)

/-- The memory chips' challenge vector at `frameJ8`. -/
def chalsMJ8 (χ : Coins frameJ8 K) : ℕ → K := chalsVSQ δF (toVSQ χ)

/-- **The J chip's challenge vector**: leaves `0..3` (tagged service coins) and `4..7` (export coins) both carry
`(Re γH, Re ρH, Im γH, Im ρH)`; every other leaf is `0`. -/
def chalsJJ8 (χ : Coins frameJ8 K) (j : ℕ) : K :=
  if j < 8 then
    (if j % 4 = 0 then toVSQ χ ⟨11, by decide⟩ else if j % 4 = 1 then toVSQ χ ⟨12, by decide⟩
      else if j % 4 = 2 then toVSQ χ cGamHi else toVSQ χ cRhoHi)
  else 0

theorem coinsCV_J8 (χ : Coins frameJ8 K) :
    TeleCQ.coinsCV b δF (chalVJ8 b χ) = (⟨gamHQ δF (toVSQ χ), rhoHQ δF (toVSQ χ)⟩ : IOCoins 𝕂′) :=
  coinsCV_VSQ δF b (toVSQ χ)

theorem mcoins_J8 (χ : Coins frameJ8 K) :
    mcoins δF (chalsMJ8 δF χ) = (⟨gamHQ δF (toVSQ χ), rhoHQ δF (toVSQ χ)⟩ : IOCoins 𝕂′) :=
  chalsVSQ_coins δF (toVSQ χ)

/-- Any memory vector that agrees with `chalsMJ8` at the handle leaves `33..36` has the handle coins. -/
theorem mcoins_of_agree (χ : Coins frameJ8 K) (chals : ℕ → K)
    (h : ∀ j, 33 ≤ j → j ≤ 36 → chals j = chalsMJ8 δF χ j) :
    mcoins δF chals = (⟨gamHQ δF (toVSQ χ), rhoHQ δF (toVSQ χ)⟩ : IOCoins 𝕂′) := by
  rw [← mcoins_J8 δF χ]
  simp only [mcoins, h 33 (by norm_num) (by norm_num), h 34 (by norm_num) (by norm_num),
    h 35 (by norm_num) (by norm_num), h 36 (by norm_num) (by norm_num)]

end Coins

section CoinsJ
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K]
  (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem coinsJX_J8 (χ : Coins frameJ8 K) :
    coinsJX δ (chalsJJ8 χ) = (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′) := by
  simp [coinsJX, chalsJJ8, gamHQ, rhoHQ]

theorem coinsJ_J8 (χ : Coins frameJ8 K) :
    coinsJ δ (chalsJJ8 χ) = (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′) := by
  simp [coinsJ, chalsJJ8, gamHQ, rhoHQ]

end CoinsJ

/-! ## 2. The compute publics and the balance publics -/

section Pubs
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K)

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- **The J-8 compute publics**: `pubVHQ` on `0..26`, `Re ρ_s` at `27..29`, `Im ρ_s` at `30..32`. -/
def pubVJ8 (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′) (χ : Coins frameJ8 K) : ℕ → F :=
  fun j =>
    if j < 27 then pubVHQ δF b c m ρ (toVSQ χ) j
    else if h1 : j < 30 then coord b (Quad.re _ ρS) ⟨j - 27, by omega⟩
    else if h2 : j < 33 then coord b (Quad.im _ ρS) ⟨j - 30, by omega⟩
    else 0

theorem limbVal_pubVJ8_low (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′)
    (χ : Coins frameJ8 K) (k : ℕ) (hk : k + 3 ≤ 27) :
    limbVal b (pubVJ8 δF b c m ρ ρS χ) k = limbVal b (pubVHQ δF b c m ρ (toVSQ χ)) k := by
  unfold limbVal
  refine Finset.sum_congr rfl fun i _ => ?_
  have : k + (i : ℕ) < 27 := by have := i.isLt; omega
  simp only [pubVJ8, if_pos this]

end Pubs

section Rho
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] {b : Basis (Fin 3) (ZMod p) K}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem rhoX_x_J8 (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′) (χ : Coins frameJ8 K) :
    ServedJ8.rhoX (b := b) (δ := δ) (pubVal := pubVJ8 δ b c m ρ ρS χ) .x = ρ 3 := by
  simp only [ServedJ8.rhoX, balCols]
  rw [limbVal_pubVJ8_low δ b c m ρ ρS χ _ (by decide), limbVal_pubVJ8_low δ b c m ρ ρS χ _ (by decide)]
  exact pubX_VSQ δ b c m ρ (toVSQ χ)

theorem rhoX_p_J8 (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′) (χ : Coins frameJ8 K) :
    ServedJ8.rhoX (b := b) (δ := δ) (pubVal := pubVJ8 δ b c m ρ ρS χ) .p = ρ 4 := by
  simp only [ServedJ8.rhoX, balCols]
  rw [limbVal_pubVJ8_low δ b c m ρ ρS χ _ (by decide), limbVal_pubVJ8_low δ b c m ρ ρS χ _ (by decide)]
  exact pubP_VSQ δ b c m ρ (toVSQ χ)

theorem rhoX_s_J8 (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′) (χ : Coins frameJ8 K) :
    ServedJ8.rhoX (b := b) (δ := δ) (pubVal := pubVJ8 δ b c m ρ ρS χ) .s = ρS := by
  simp only [ServedJ8.rhoX, balCols]
  have h1 : limbVal b (pubVJ8 δ b c m ρ ρS χ) pubRhoSX = Quad.re _ ρS := by
    refine limbVal_eq_of_coords b _ _ _ fun k => ?_
    fin_cases k <;> simp [pubVJ8, pubRhoSX]
  have h2 : limbVal b (pubVJ8 δ b c m ρ ρS χ) pubRhoSXi = Quad.im _ ρS := by
    refine limbVal_eq_of_coords b _ _ _ fun k => ?_
    fin_cases k <;> simp [pubVJ8, pubRhoSXi]
  rw [h1, h2, Quad.mk_re_im]

/-- **The verifier's check on the concrete terminals**: `GoodCJ8` at `pubVJ8` is the three equations
`ρ₃ + (pubW₄, pubW₅) + (pubJ₂, pubJ₃) = (pubC₄, pubC₅)`, `ρ₄ = (pubW₆, pubW₇)`, `ρ_s + TextS = TprovS`. -/
theorem goodCJ8_iff (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′) (χ : Coins frameJ8 K)
    (pubsC pubsW pubsJ : ℕ → K) (TprovS TextS : 𝕂′) :
    ServedJ8.GoodCJ8 (b := b) (δ := δ) (pubVal := pubVJ8 δ b c m ρ ρS χ) (TprovJ8 pubsC pubsW TprovS)
        (TextJ8 pubsW pubsJ TextS) ↔
      (ρ 3 + (Quad.mk _ (pubsW WalkHQ.pubXQ) (pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (pubsJ 2) (pubsJ 3)) =
          Quad.mk _ (pubsC CellHQ.pubHQ) (pubsC (CellHQ.pubHQ + 1))) ∧
        ρ 4 = Quad.mk _ (pubsW WalkHQ.pubPQ) (pubsW (WalkHQ.pubPQ + 1)) ∧
        ρS + TextS = TprovS := by
  constructor
  · intro hG
    have hx := hG .x
    have hp := hG .p
    have hs := hG .s
    rw [rhoX_x_J8] at hx
    rw [rhoX_p_J8] at hp
    rw [rhoX_s_J8] at hs
    simp only [TprovJ8, TextJ8, add_zero] at hx hp hs
    exact ⟨hx, hp, hs⟩
  · rintro ⟨hx, hp, hs⟩ bl
    cases bl with
    | x => rw [rhoX_x_J8]; exact hx
    | p => rw [rhoX_p_J8]; simpa [TprovJ8, TextJ8] using hp
    | s => rw [rhoX_s_J8]; exact hs

end Rho


/-! ## 3. `BalJ8` at the frame's verifier data -/

section Frame
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (BalJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow)
open Nock.Jet.RapJetJ8 (jRd)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))] {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`BalJ8` at `frameJ8`'s verifier data**: compute challenge vector `chalVJ8`, publics `pubVJ8`; the cell and
walk vectors agree with `chalsMJ8` at the handle leaves `33..36`; the J vector is `chalsJJ8`.  The verifier's three
equations (`goodCJ8_iff`) and the `s` telescopes give the balance identity. -/
theorem balJ8_frameJ8 (χ : Coins frameJ8 K) (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → ZMod p)
    (orbitC : StrictOrbitDomain (ZMod p) 3 hC) (chalsC pubsC : ℕ → K)
    (QC : Fin (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.w → (ZMod p)[X])
    (hsatC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.Satisfies QC)
    (hbindC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    (hchC : ∀ j, 33 ≤ j → j ≤ 36 → chalsC j = chalsMJ8 δ χ j)
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hsatW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hF : GeneratedField.PrimeFieldElems (ZMod p)) (hp64 : 64 ≤ ringChar (ZMod p))
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    (hchW : ∀ j, 33 ≤ j → j ≤ 36 → chalsW j = chalsMJ8 δ χ j)
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).rap.w → (ZMod p)[X])
    (hsatJ : (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).rap.Satisfies PJ)
    (hbindJ : (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).BindsPreprocessing PJ)
    (hinjJ : Function.Injective nodesJ) (hnJ : 0 < nJ)
    (hadjJ : ∀ (i : Fin nJ) (hi : (i : ℕ) + 1 < nJ), nodesJ ⟨(i : ℕ) + 1, hi⟩ = nodesJ i * orbitJ.ω)
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    (hextX : ext .x = ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++
      jRd b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (hprovP : provs .p = ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW)
    (hextP : ext .p = [])
    (TprovS TextS : 𝕂′)
    (hS_prov : ((provs .s).map fun q => algebraMap K 𝕂′ q.2 *
      (compress (TeleCQ.coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) q.1))⁻¹).sum = TprovS)
    (hS_ext : ((ext .s).map fun r =>
      (compress (TeleCQ.coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum = TextS)
    (hGx : ρ 3 + (Quad.mk _ (pubsW WalkHQ.pubXQ) (pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (pubsJ 2) (pubsJ 3)) =
      Quad.mk _ (pubsC CellHQ.pubHQ) (pubsC (CellHQ.pubHQ + 1)))
    (hGp : ρ 4 = Quad.mk _ (pubsW WalkHQ.pubPQ) (pubsW (WalkHQ.pubPQ + 1)))
    (hGs : ρS + TextS = TprovS) :
    BalJ8 (b := b) (δ := δ) (chalV := chalVJ8 b χ) (pubVal := pubVJ8 δ b c m ρ ρS χ) provs ext := by
  have hcv := coinsCV_J8 δ b χ
  refine BalXJ8.balJ8_of_goodJ8 hnC nodesC orbitC chalsC pubsC QC hsatC hbindC hinjC hadjC
    ((mcoins_of_agree δ χ chalsC hchC).trans hcv.symm)
    kroots hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW
    ((mcoins_of_agree δ χ chalsW hchW).trans hcv.symm)
    nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ hsatJ hbindJ hinjJ hnJ hadjJ ((coinsJX_J8 δ χ).trans hcv.symm)
    hprovX hextX hprovP hextP TprovS TextS hS_prov hS_ext ?_
  exact (goodCJ8_iff c m ρ ρS χ pubsC pubsW pubsJ TprovS TextS).2 ⟨hGx, hGp, hGs⟩

end Frame

end

end Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
