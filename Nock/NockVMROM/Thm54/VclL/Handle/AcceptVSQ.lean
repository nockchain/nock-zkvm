/-
  Nock/NockVMROM/Thm54/VclL/Handle/AcceptVSQ.lean

* `chiK χ γ ρ`: the first fifteen coins of `χ` with the handle coins `11 / 12` replaced by `(γ, ρ)`;
  * the re-filled message `msgK` (constant in the coin): compute `refillP` at `chalVH / pubVH` of `chiK`,
    cell `refillC`, walk `refillW`, requests `rhoK` (`ρ₃ / ρ₄` = the two `𝕂` totals, Im `0`), memory
    message `(y, yHK)` with `yHK` the walk export total;
  * **`acceptsK`**: `AcceptsG (toVSV V) msgK (chiK χ γ ρ)` at every accepted VSQ coin outside the two `𝕂′`
    handle summands, for every `(γ, ρ)` at which the four round-0 handle lists of the projection are
    pole-free (`DescentVSQ.exists_pair_poleFreeQ` supplies one).  The terminals are
    `DescentVSQ.kX_identity` / `kP_identity` at `f = (compress ⟨γ, ρ⟩ ·)⁻¹`.
  * `tracesK_off`: the re-fill agrees with the projection off the handle blocks (`CongrVSQ.OffHandle`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.SumsVSQ
import Nock.NockVMROM.Thm54.VclL.Handle.HonestAssembleVS
import Nock.NockVMROM.Thm54.VclL.Handle.CongrVSQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AcceptVSQ

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.NockVMROM.Thm54.VclL.Handle.ServeH
open Nock.NockVMROM.Thm54.VclL.Handle.RefillCQ Nock.NockVMROM.Thm54.VclL.Handle.RefillMQ
open Nock.NockVMROM.Thm54.VclL.Handle.RefillWQ Nock.NockVMROM.Thm54.VclL.Handle.DescentVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.ChoiceQ Nock.NockVMROM.Thm54.VclL.Handle.SummandsHQ
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceVSQ Nock.NockVMROM.Thm54.VclL.Handle.PathVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.SumsVSQ Nock.NockVMROM.Thm54.VclL.Handle.CongrVSQ
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp

noncomputable section

/-! ## 1. The coins -/

section Coins
variable {K : Type}

/-- The first fifteen coins with the handle coins `11 / 12` replaced by `(γ, ρ)`. -/
def chiK (χ : Coins frameVSQ K) (γ ρ : K) : Coins frameVS K :=
  fun i => if (i : ℕ) = 11 then γ else if (i : ℕ) = 12 then ρ else toVS χ i

theorem chiK_off (χ : Coins frameVSQ K) (γ ρ : K) (i : Fin frameVS.n) (h11 : (i : ℕ) ≠ 11)
    (h12 : (i : ℕ) ≠ 12) : chiK χ γ ρ i = toVS χ i := by
  simp only [chiK, if_neg h11, if_neg h12]

theorem chiK_gam (χ : Coins frameVSQ K) (γ ρ : K) : chiK χ γ ρ cGamH = γ := by simp [chiK, cGamH]
theorem chiK_rho (χ : Coins frameVSQ K) (γ ρ : K) : chiK χ γ ρ cRhoH = ρ := by simp [chiK, cRhoH]

end Coins

section CoinFacts
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (χ : Coins frameVSQ K) (γ ρ : K)

theorem coin_off (i : ℕ) (hi : i < 15) (h11 : i ≠ 11) (h12 : i ≠ 12) :
    chiK χ γ ρ ⟨i, hi⟩ = toVS χ ⟨i, hi⟩ := chiK_off χ γ ρ ⟨i, hi⟩ h11 h12

theorem claimValSum_chiK (c : P8PublicClaim) (m : ClaimMsgVS) :
    claimValSum δF c m (chiK χ γ ρ) = claimValSum δF c m (toVS χ) := by
  unfold claimValSum
  rw [claimRecs_congr δF c m _ _ (coin_off χ γ ρ 2 (by decide) (by decide) (by decide))
    (coin_off χ γ ρ 3 (by decide) (by decide) (by decide))]
  unfold ioCoinsVS
  rw [coin_off χ γ ρ 4 (by decide) (by decide) (by decide), coin_off χ γ ρ 5 (by decide) (by decide) (by decide),
    coin_off χ γ ρ 6 (by decide) (by decide) (by decide), coin_off χ γ ρ 7 (by decide) (by decide) (by decide)]

theorem chalsVS_chiK (i : ℕ) (hi : i < 33) : chalsVS δF (chiK χ γ ρ) i = chalsVSQ δF χ i := by
  have h35 : i ≠ 35 := by omega
  have h36 : i ≠ 36 := by omega
  rw [chalsVS_old _ _ _ hi]
  simp only [chalsVSQ, if_neg h35, if_neg h36]
  rw [chalsVS_old _ _ _ hi]
  congr 1
  funext j
  have hj : (j : ℕ) < 11 := j.isLt
  exact coin_off χ γ ρ j (by omega) (by omega) (by omega)

theorem chalVH_chiK (b : Basis (Fin 3) F K) (j : ℕ) (h6 : 6 ≤ j) (h12 : j < 12) :
    chalVH b (chiK χ γ ρ) j = chalVHQ b χ j := by
  rw [chalVHQ_old b χ j h12]
  simp only [chalVH, if_pos h12]
  have hq : coinH (chiK χ γ ρ) (j / 3) = coinH (toVS χ) (j / 3) := by
    have h0 : j / 3 ≠ 0 := by omega
    have h1 : j / 3 ≠ 1 := by omega
    simp only [coinH, if_neg h0, if_neg h1]
    split_ifs
    · exact coin_off χ γ ρ 13 (by decide) (by decide) (by decide)
    · exact coin_off χ γ ρ 14 (by decide) (by decide) (by decide)
  rw [hq]

theorem pubVH_low (b : Basis (Fin 3) F K) (c : P8PublicClaim) (m : ClaimMsgVS)
    (ρ₁ ρ₂ : Fin 5 → Quad (algebraMap F K δF)) (χ₁ χ₂ : Coins frameVS K)
    (hA : χ₁ cAlphaW = χ₂ cAlphaW) (hG : χ₁ cGamW = χ₂ cGamW) (j : ℕ) (hj : j < 15) :
    pubVH δF b c m ρ₁ χ₁ j = pubVH δF b c m ρ₂ χ₂ j := by
  have hs : seedVS (F := F) c m χ₁ = seedVS (F := F) c m χ₂ := by unfold seedVS; rw [hA, hG]
  unfold pubVH
  rw [hA, hs]
  split_ifs <;> rfl

end CoinFacts

/-! ## 2. The re-filled message -/

section Msg
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] {hT hP kr hC : ℕ}
  {sumC : VerifierData F K hC (shapeVSQ hT hP) → ClaimMsgVS → SummandsVSQ (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVSQ hT hP) → Unit → SummandsVSQ (F := F) (K := K) hT hP hC}
  (V : VerifierData F K hC (shapeVSQ hT hP))
  (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM))
  (χ : Coins frameVSQ K) (γ ρ : K)

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The VS compute coin vector of the re-fill. -/
abbrev chalK : ℕ → F := chalVH V.basis (chiK χ γ ρ)

/-- The VS compute publics at the VSQ requests (used only to state the totals; the row terms ignore them). -/
abbrev pub0 : ℕ → F := pubVH δF V.basis V.claim msg.msg0C (msg.requests χ) (chiK χ γ ρ)

/-- The `𝕂` compute export / path totals. -/
def totX : K :=
  ∑ j ∈ Finset.range V.N, termXV V.computeNodes V.basis (chalK V χ γ ρ) (pub0 δF V msg χ γ ρ) V.orbitC (msg.Qc χ) j

def totP : K :=
  ∑ j ∈ Finset.range V.N, termPV V.computeNodes V.basis (chalK V χ γ ρ) (pub0 δF V msg χ γ ρ) V.orbitC (msg.Qc χ) j

/-- The re-fill's requests: `ρ₃ / ρ₄` the `𝕂` totals (Im `0`), the rest the VSQ requests. -/
def rhoK : Fin 5 → 𝕂′ := fun a =>
  if (a : ℕ) = 3 then Quad.mk _ (totX δF V msg χ γ ρ) 0
  else if (a : ℕ) = 4 then Quad.mk _ (totP δF V msg χ γ ρ) 0 else msg.requests χ a

abbrev pubK : ℕ → F := pubVH δF V.basis V.claim msg.msg0C (rhoK δF V msg χ γ ρ) (chiK χ γ ρ)

/-- **The re-filled compute trace.** -/
abbrev QcK : Fin 70 → F[X] :=
  refillP V.computeNodes V.basis (chalK V χ γ ρ) (pubK δF V msg χ γ ρ) V.orbitC (msg.Qc χ)

abbrev chalsK : ℕ → K := chalsVS δF (chiK χ γ ρ)
abbrev pubsCQ : ℕ → K := pubsCHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2
abbrev pubsWQ : ℕ → K := pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2

/-- The VSQ cell twin trace, at the chip's own width. -/
abbrev QC : Fin (cellChipHQ δF V.basis (V.hM (tCQ hT hP)) (V.memNodes (tCQ hT hP)) (V.orbitM (tCQ hT hP))
    (chalsVSQ δF χ) (pubsCQ δF msg χ)).rap.w → F[X] :=
  fun j => msg.Qm χ (tCQ hT hP) (Fin.cast (by rw [cellChipHQ_width]; rfl) j)

/-- The VSQ walk twin trace, at the chip's own width. -/
abbrev QW : Fin (walkChipHQ δF kr V.basis (V.hM (tWQ hT hP)) (V.memNodes (tWQ hT hP)) (V.orbitM (tWQ hT hP))
    (chalsVSQ δF χ) (pubsWQ δF msg χ)).rap.w → F[X] :=
  fun j => msg.Qm χ (tWQ hT hP) (Fin.cast (by rw [walkChipHQ_width]; rfl) j)

/-- The `𝕂` walk export total. -/
def yHK : K :=
  ∑ j ∈ Finset.range (V.memRows (tWQ hT hP)),
    (dW δF kr V.basis (V.hM (tWQ hT hP)) (V.memNodes (tWQ hT hP)) (V.orbitM (tWQ hT hP)) (chalsVSQ δF χ)
      (pubsWQ δF msg χ) (chalsK δF χ γ ρ) (fun _ => 0) (QW δF V msg χ) WalkHC.xKeyH j)⁻¹

abbrev pubsCK : ℕ → K := pubsCH δF (rhoK δF V msg χ γ ρ) (msg.msg2M χ).1 (yHK δF V msg χ γ ρ)
abbrev pubsWK : ℕ → K := pubsWH δF (rhoK δF V msg χ γ ρ) (msg.msg2M χ).1 (yHK δF V msg χ γ ρ)

/-- **The re-filled cell twin trace.** -/
abbrev QCK := refillC δF V.basis (V.hM (tCQ hT hP)) (V.memNodes (tCQ hT hP)) (V.orbitM (tCQ hT hP))
  (chalsVSQ δF χ) (pubsCQ δF msg χ) (chalsK δF χ γ ρ) (pubsCK δF V msg χ γ ρ) (QC δF V msg χ)

/-- **The re-filled walk twin trace.** -/
abbrev QWK := refillW δF kr V.basis (V.hM (tWQ hT hP)) (V.memNodes (tWQ hT hP)) (V.orbitM (tWQ hT hP))
  (chalsVSQ δF χ) (pubsWQ δF msg χ) (chalsK δF χ γ ρ) (pubsWK δF V msg χ γ ρ) (QW δF V msg χ)

theorem wC (t : Fin (shapeVS hT hP).k) (ht : (t : ℕ) = 0) :
    ((shapeVS hT hP).table t).width = (cellChipH δF V.basis (V.hM (tCQ hT hP)) (V.memNodes (tCQ hT hP))
      (V.orbitM (tCQ hT hP)) (chalsK δF χ γ ρ) (pubsCK δF V msg χ γ ρ)).rap.w := by
  obtain rfl : t = tCS hT hP := Fin.ext ht
  rw [cellChipH_width]; rfl

theorem wW (t : Fin (shapeVS hT hP).k) (ht : ¬ (t : ℕ) = 0) :
    ((shapeVS hT hP).table t).width = (walkChipH δF kr V.basis (V.hM (tWQ hT hP)) (V.memNodes (tWQ hT hP))
      (V.orbitM (tWQ hT hP)) (chalsK δF χ γ ρ) (pubsWK δF V msg χ γ ρ)).rap.w := by
  obtain rfl : t = tWS hT hP := Fin.ext (by have h2 : (t : ℕ) < 2 := t.2; show (t : ℕ) = 1; omega)
  rw [walkChipH_width]; rfl

/-- The re-filled memory traces, by table. -/
def QmK : ∀ t : Fin (shapeVS hT hP).k, Fin ((shapeVS hT hP).table t).width → F[X] := fun t =>
  if ht : (t : ℕ) = 0 then fun j => QCK δF V msg χ γ ρ (Fin.cast (wC δF V msg χ γ ρ t ht) j)
  else fun j => QWK δF V msg χ γ ρ (Fin.cast (wW δF V msg χ γ ρ t ht) j)

variable {sumCV : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
  {sumMV : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}

/-- **The re-filled VS message** (constant in the coin). -/
def msgK : MessagesG (compCoreVS δF hT hP hC sumCV) (memCoreVS δF hT hP kr hC sumMV) where
  Qc _ := QcK δF V msg χ γ ρ
  Qm _ := QmK δF V msg χ γ ρ
  msg0C := msg.msg0C
  msg0M := ()
  requests _ := rhoK δF V msg χ γ ρ
  msg2M _ := ((msg.msg2M χ).1, yHK δF V msg χ γ ρ)

end Msg

/-! ## 3. Acceptance of the re-fill -/

section Accept
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] {hT hP kr hC : ℕ}
  {sumC : VerifierData F K hC (shapeVSQ hT hP) → ClaimMsgVS → SummandsVSQ (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVSQ hT hP) → Unit → SummandsVSQ (F := F) (K := K) hT hP hC}
  (V : VerifierData F K hC (shapeVSQ hT hP))
  (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM))
  (χ : Coins frameVSQ K) (γ ρ : K)
  {sumCV : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
  {sumMV : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}

theorem orbitC_eq : (toVSV hT hP hC V).orbitM (tCS hT hP) = V.orbitM (tCQ hT hP) := rfl
theorem orbitW_eq : (toVSV hT hP hC V).orbitM (tWS hT hP) = V.orbitM (tWQ hT hP) := rfl

theorem rhoK_3 : rhoK δF V msg χ γ ρ 3 = Quad.mk _ (totX δF V msg χ γ ρ) 0 := if_pos rfl
theorem rhoK_4 : rhoK δF V msg χ γ ρ 4 = Quad.mk _ (totP δF V msg χ γ ρ) 0 :=
  (if_neg (by decide)).trans (if_pos rfl)

theorem rho3_K : rho3 δF (rhoK δF V msg χ γ ρ) = rho3 δF (msg.requests χ) := by
  funext a
  have ha : (a : ℕ) < 3 := a.isLt
  simp only [rho3, rhoK, if_neg (show (a : ℕ) ≠ 3 by omega), if_neg (show (a : ℕ) ≠ 4 by omega)]

theorem goodC_K (hg : GoodCVSQ δF V msg.msg0C (msg.requests χ) χ) :
    GoodCVS δF (toVSV hT hP hC V) msg.msg0C (rhoK δF V msg χ γ ρ) (chiK χ γ ρ) := by
  refine ⟨hg.1, hg.2.1, hg.2.2.1, ?_, ?_, by rw [rhoK_3, Quad.im_mk], by rw [rhoK_4, Quad.im_mk]⟩
  · show msg.requests χ 0 = _
    erw [hg.2.2.2.1, claimValSum_chiK]
  · show msg.requests χ 1 = 0
    exact hg.2.2.2.2

theorem goodM_K (hg : GoodM V (tCQ hT hP)) : GoodM (toVSV hT hP hC V) (tCS hT hP) := hg
theorem goodW_K (hg : GoodW V (tWQ hT hP) kr) : GoodW (toVSV hT hP hC V) (tWS hT hP) kr := hg

theorem coinsK : coinsC V.basis (chalK V χ γ ρ) = (⟨γ, ρ⟩ : IOCoins K) := by
  rw [coinsC_VS, chiK_gam, chiK_rho]

theorem chalsK_coins :
    (⟨chalsK δF χ γ ρ CellH.hGam, chalsK δF χ γ ρ CellH.hRho⟩ : IOCoins K) = ⟨γ, ρ⟩ := by
  show (⟨chalsVS δF (chiK χ γ ρ) CellH.hGam, chalsVS δF (chiK χ γ ρ) CellH.hRho⟩ : IOCoins K) = _
  rw [chalsVS_hGam, chalsVS_hRho, chiK_gam, chiK_rho]

theorem totX_eq : totX δF V msg χ γ ρ =
    ((cXQ δF hT hP kr hC V msg χ).map fun r => (compress (⟨γ, ρ⟩ : IOCoins K) r)⁻¹).sum := by
  rw [← coinsK V χ γ ρ]
  exact sumX_eq V.computeNodes V.basis (chalK V χ γ ρ) V.orbitC (msg.Qc χ) (pub0 δF V msg χ γ ρ) (msg.Qc χ)
    (chalVHQ V.basis χ) (pubVHQ δF V.basis V.claim msg.msg0C (msg.requests χ) χ) (by show 43 ≤ 85; norm_num)
    (fun _ _ _ _ => rfl)

theorem totP_eq : totP δF V msg χ γ ρ =
    ((cPQ δF hT hP kr hC V msg χ).map fun r => (compress (⟨γ, ρ⟩ : IOCoins K) r)⁻¹).sum := by
  rw [← coinsK V χ γ ρ]
  exact sumP_eq V.computeNodes V.basis (chalK V χ γ ρ) V.orbitC (msg.Qc χ) (pub0 δF V msg χ γ ρ) (msg.Qc χ)
    (chalVHQ V.basis χ) (pubVHQ δF V.basis V.claim msg.msg0C (msg.requests χ) χ) (by show 43 ≤ 85; norm_num)
    (fun _ _ _ _ => rfl)

theorem yHK_eq : yHK δF V msg χ γ ρ =
    ((wXQ δF hT hP kr hC V msg χ).map fun r => (compress (⟨γ, ρ⟩ : IOCoins K) r)⁻¹).sum := by
  rw [← chalsK_coins δF χ γ ρ]
  exact sumWX_eq δF kr V.basis (V.hM (tWQ hT hP)) (V.memNodes (tWQ hT hP)) (V.orbitM (tWQ hT hP))
    (chalsVSQ δF χ) (pubsWQ δF msg χ) (chalsK δF χ γ ρ) (fun _ => 0) (QW δF V msg χ) (msg.Qm χ (tWQ hT hP))
    (chalsVSQ δF χ) (pubsWQ δF msg χ) (by show 25 ≤ 166; norm_num) (fun _ _ _ _ => rfl)

/-- **The re-fill is accepted by the VS chips at the transported datum**. -/
theorem acceptsK
    (hV : V.Checks (fun a => reqBoundVSQ hT hP hC V a + internalBoundVSQ hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (h : AcceptsG V msg χ)
    (hXq : ¬ (ioSummandHXQ δF hT hP hC V).mem (msg.traces χ) χ)
    (hPq : ¬ (ioSummandHPQ δF hT hP hC V).mem (msg.traces χ) χ)
    (hX : ∀ r ∈ reqX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ)), compress ⟨γ, ρ⟩ r ≠ 0)
    (hXp : ∀ q ∈ provX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ)), compress ⟨γ, ρ⟩ q.1 ≠ 0)
    (hPr : ∀ r ∈ reqP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ)), compress ⟨γ, ρ⟩ r ≠ 0)
    (hPp : ∀ q ∈ provP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (msg.traces χ)), compress ⟨γ, ρ⟩ q.1 ≠ 0) :
    AcceptsG (toVSV hT hP hC V) (msgK (sumCV := sumCV) (sumMV := sumMV) δF V msg χ γ ρ) (chiK χ γ ρ) := by
  obtain ⟨hg, hsatC⟩ := compute_factsQ δF hT hP kr hC V msg χ h
  obtain ⟨hGM, hwC, hsatM⟩ := cell_factsQ δF hT hP kr hC V msg χ h
  obtain ⟨hGW, hwW, hsatW⟩ := walk_factsQ δF hT hP kr hC V msg χ h
  obtain ⟨e1, e2, e3, e4⟩ := listsQ_at δF hT hP kr hC V msg χ
  have kX := kX_identity δF hT hP kr hC V hV msg χ h hXq hPq fun r => (compress (⟨γ, ρ⟩ : IOCoins K) r)⁻¹
  have kP := kP_identity δF hT hP kr hC V hV msg χ h hPq fun r => (compress (⟨γ, ρ⟩ : IOCoins K) r)⁻¹
  rw [e1, e2, List.map_append, List.sum_append] at kX
  rw [e3, e4] at kP
  have hc11 : 11 < ringChar F := lt_trans (by norm_num) hg.2.2.1
  have hadjC : ∀ (i : Fin V.N) (hi : (i : ℕ) + 1 < V.N),
      V.computeNodes ⟨(i : ℕ) + 1, hi⟩ = V.computeNodes i * V.orbitC.ω := fun i hi => by
    rw [hg.1 i hi, mul_comm]
  -- the compute chip
  have hre3 : Quad.re _ (rhoK δF V msg χ γ ρ 3) = ∑ j ∈ Finset.range V.N,
      termXV V.computeNodes V.basis (chalK V χ γ ρ) (pubK δF V msg χ γ ρ) V.orbitC (msg.Qc χ) j := by
    rw [rhoK_3, Quad.re_mk]
    exact Finset.sum_congr rfl fun j _ => termXV_pub _ _ _ _ _ _ _ j
  have hre4 : Quad.re _ (rhoK δF V msg χ γ ρ 4) = ∑ j ∈ Finset.range V.N,
      termPV V.computeNodes V.basis (chalK V χ γ ρ) (pubK δF V msg χ γ ρ) V.orbitC (msg.Qc χ) j := by
    rw [rhoK_4, Quad.re_mk]
    exact Finset.sum_congr rfl fun j _ => termPV_pub _ _ _ _ _ _ _ j
  have hcomp := computeChipVCLH_of_HQ V.hN V.computeNodes V.basis δF (chalVHQ V.basis χ)
    (pubVHQ δF V.basis V.claim msg.msg0C (msg.requests χ) χ) (chalK V χ γ ρ) (pubK δF V msg χ γ ρ) V.orbitC
    (msg.Qc χ) hsatC hg.2.1 hadjC hc11 (fun j h6 h12 => chalVH_chiK χ γ ρ V.basis j h6 h12)
    (fun j hj => by
      show _ = pubVHQ δF V.basis V.claim msg.msg0C (msg.requests χ) χ j
      simp only [pubVHQ, if_pos (show j < 21 by omega)]
      exact pubVH_low δF V.basis V.claim msg.msg0C _ _ _ _
        (coin_off χ γ ρ 13 (by decide) (by decide) (by decide))
        (coin_off χ γ ρ 14 (by decide) (by decide) (by decide)) j hj)
    (fun i r hr => by
      rw [coinsK]
      rcases memXP (K := K) V.computeNodes (chalK V χ γ ρ) V.orbitC (msg.Qc χ) (pubK δF V msg χ γ ρ)
          (projQ hT hP hC (msg.traces χ)).1 (fun _ => 0) (fun _ => 0) (by show 43 ≤ 70; norm_num)
          (fun _ _ _ _ => rfl) i r hr with h1 | h1
      · exact hX r (List.mem_append_left _ h1)
      · exact hPr r h1)
    (fun k => by
      rw [← hre3, ← pubX_VS δF V.basis V.claim msg.msg0C (rhoK δF V msg χ γ ρ) (chiK χ γ ρ), coord_limbVal])
    (fun k => by
      rw [← hre4, ← pubP_VS δF V.basis V.claim msg.msg0C (rhoK δF V msg χ γ ρ) (chiK χ γ ρ), coord_limbVal])
  refine acceptsG_of_chips δF hT hP kr hC (toVSV hT hP hC V) _ (chiK χ γ ρ) (goodC_K δF V msg χ γ ρ hg) hcomp
    (goodM_K V hGM) (goodW_K V hGW) (fun hw => ?_) (fun hw => ?_)
  · -- the cell twin
    have hfun : (fun j => (msgK (sumCV := sumCV) (sumMV := sumMV) δF V msg χ γ ρ).Qm (chiK χ γ ρ) (tCS hT hP)
        (Fin.cast hw j)) = QCK δF V msg χ γ ρ := by
      funext j
      show QmK δF V msg χ γ ρ (tCS hT hP) (Fin.cast hw j) = _
      simp only [QmK, dif_pos (show ((tCS hT hP : Fin (shapeVS hT hP).k) : ℕ) = 0 from rfl)]
      rfl
    rw [hfun]
    refine cellChipH_of_HQ δF V.basis (V.hM (tCQ hT hP)) (V.memNodes (tCQ hT hP)) (V.orbitM (tCQ hT hP))
      (chalsVSQ δF χ) (pubsCQ δF msg χ) (chalsK δF χ γ ρ) (pubsCK δF V msg χ γ ρ) (QC δF V msg χ) hsatM hGM.2.1
      hGM.1 (fun i hi => (chalsVS_chiK δF χ γ ρ i hi).symm) (fun i hi => ?_) (fun j hj => ?_) ?_
    · have h4 : i ≠ 4 := by omega
      have h5 : i ≠ 5 := by omega
      simp only [pubsCQ, pubsCK, pubsCHQ, pubsCH, CellH.pubH, if_neg h4, if_neg h5, rho3_K]
    · obtain ⟨q, hq, hd⟩ := memC δF V.basis (V.hM (tCQ hT hP)) (V.memNodes (tCQ hT hP)) (V.orbitM (tCQ hT hP))
        (chalsVSQ δF χ) (pubsCQ δF msg χ) (chalsK δF χ γ ρ) (pubsCK δF V msg χ γ ρ) (QC δF V msg χ)
        (msg.Qm χ (tCQ hT hP)) (chalsVSQ δF χ) (pubsCQ δF msg χ) (by show 130 ≤ 238; norm_num)
        (fun _ _ _ _ => rfl) j hj
      rw [hd, chalsK_coins]
      exact hXp q (by rw [e2]; exact hq)
    · rw [sumC_eq δF V.basis (V.hM (tCQ hT hP)) (V.memNodes (tCQ hT hP)) (V.orbitM (tCQ hT hP))
        (chalsVSQ δF χ) (pubsCQ δF msg χ) (chalsK δF χ γ ρ) (pubsCK δF V msg χ γ ρ) (QC δF V msg χ)
        (msg.Qm χ (tCQ hT hP)) (chalsVSQ δF χ) (pubsCQ δF msg χ) (by show 130 ≤ 238; norm_num)
        (fun _ _ _ _ => rfl), chalsK_coins, ← kX, ← totX_eq, ← yHK_eq]
      show Quad.re _ (rhoK δF V msg χ γ ρ 3) + yHK δF V msg χ γ ρ = _
      rw [rhoK_3, Quad.re_mk]
  · -- the walk twin
    have hfun : (fun j => (msgK (sumCV := sumCV) (sumMV := sumMV) δF V msg χ γ ρ).Qm (chiK χ γ ρ) (tWS hT hP)
        (Fin.cast hw j)) = QWK δF V msg χ γ ρ := by
      funext j
      show QmK δF V msg χ γ ρ (tWS hT hP) (Fin.cast hw j) = _
      simp only [QmK, dif_neg (show ¬ ((tWS hT hP : Fin (shapeVS hT hP).k) : ℕ) = 0 from Nat.one_ne_zero)]
      rfl
    rw [hfun]
    have hmW := fun j hj => memWP δF kr V.basis (V.hM (tWQ hT hP)) (V.memNodes (tWQ hT hP)) (V.orbitM (tWQ hT hP))
        (chalsVSQ δF χ) (pubsWQ δF msg χ) (chalsK δF χ γ ρ) (pubsWK δF V msg χ γ ρ) (QW δF V msg χ)
        (msg.Qm χ (tWQ hT hP)) (chalsVSQ δF χ) (pubsWQ δF msg χ) (by show 25 ≤ 166; norm_num)
        (fun _ _ _ _ => rfl) j hj
    refine walkChipH_of_HQ δF kr V.basis (V.hM (tWQ hT hP)) (V.memNodes (tWQ hT hP)) (V.orbitM (tWQ hT hP))
      (chalsVSQ δF χ) (pubsWQ δF msg χ) (chalsK δF χ γ ρ) (pubsWK δF V msg χ γ ρ) (QW δF V msg χ) hsatW
      hGW.1.2.1 hGW.1.1 (fun i hi => (chalsVS_chiK δF χ γ ρ i hi).symm) (fun i hi => ?_) (fun j hj => ?_)
      (fun j hj => ?_) (fun j hj => ?_) ?_ ?_
    · have h4 : i ≠ 4 := by omega
      have h5 : i ≠ 5 := by omega
      have h6 : i ≠ 6 := by omega
      have h7 : i ≠ 7 := by omega
      simp only [pubsWQ, pubsWK, pubsWHQ, pubsWH, WalkHC.pubX, WalkHC.pubP, if_neg h4, if_neg h5, if_neg h6,
        if_neg h7, rho3_K]
    · obtain ⟨r, hr, hd⟩ := memWX δF kr V.basis (V.hM (tWQ hT hP)) (V.memNodes (tWQ hT hP)) (V.orbitM (tWQ hT hP))
        (chalsVSQ δF χ) (pubsWQ δF msg χ) (chalsK δF χ γ ρ) (pubsWK δF V msg χ γ ρ) (QW δF V msg χ)
        (msg.Qm χ (tWQ hT hP)) (chalsVSQ δF χ) (pubsWQ δF msg χ) (by show 25 ≤ 166; norm_num)
        (fun _ _ _ _ => rfl) j hj
      rw [hd, chalsK_coins]
      exact hX r (by rw [e1]; exact List.mem_append_right _ hr)
    · obtain ⟨q, hq, hd⟩ := (hmW j hj).1
      rw [hd, chalsK_coins]
      exact hPp q (by rw [e4]; exact hq)
    · obtain ⟨q, hq, hd⟩ := (hmW j hj).2
      rw [hd, chalsK_coins]
      exact hPp q (by rw [e4]; exact hq)
    · show yHK δF V msg χ γ ρ = _
      unfold yHK
      exact Finset.sum_congr rfl fun j _ => by
        rw [dW_pub δF kr V.basis (V.hM (tWQ hT hP)) (V.memNodes (tWQ hT hP)) (V.orbitM (tWQ hT hP))
          (chalsVSQ δF χ) (pubsWQ δF msg χ) (chalsK δF χ γ ρ) (fun _ => 0) (QW δF V msg χ) _ xKeyH_read
          (pubsWK δF V msg χ γ ρ) j]
    · rw [sumWP_eq δF kr V.basis (V.hM (tWQ hT hP)) (V.memNodes (tWQ hT hP)) (V.orbitM (tWQ hT hP))
        (chalsVSQ δF χ) (pubsWQ δF msg χ) (chalsK δF χ γ ρ) (pubsWK δF V msg χ γ ρ) (QW δF V msg χ)
        (msg.Qm χ (tWQ hT hP)) (chalsVSQ δF χ) (pubsWQ δF msg χ) (by show 25 ≤ 166; norm_num)
        (fun _ _ _ _ => rfl), chalsK_coins, ← kP, ← totP_eq]
      show Quad.re _ (rhoK δF V msg χ γ ρ 4) = _
      rw [rhoK_4, Quad.re_mk]

/-- **The re-fill agrees with the projection off the handle blocks** (`CongrVSQ.OffHandle`). -/
theorem tracesK_off :
    OffHandle hT hP hC (projQ hT hP hC (msg.traces χ))
      ((msgK (sumCV := sumCV) (sumMV := sumMV) δF V msg χ γ ρ).traces (chiK χ γ ρ)) (toVS χ) (chiK χ γ ρ) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun i h11 h12 => chiK_off χ γ ρ i h11 h12⟩
  · show refillP _ _ _ _ _ _ j = _
    unfold refillP
    split_ifs with hc
    · exact absurd hc.1 (by omega)
    · rfl
  · show QmK δF V msg χ γ ρ (tCS hT hP) j = _
    simp only [QmK, dif_pos (show ((tCS hT hP : Fin (shapeVS hT hP).k) : ℕ) = 0 from rfl)]
    show refillC _ _ _ _ _ _ _ _ _ _ _ = _
    unfold refillC
    split_ifs with hc
    · rfl
    · exact absurd hj hc
  · show QmK δF V msg χ γ ρ (tWS hT hP) j = _
    simp only [QmK, dif_neg (show ¬ ((tWS hT hP : Fin (shapeVS hT hP).k) : ℕ) = 0 from Nat.one_ne_zero)]
    show refillW _ _ _ _ _ _ _ _ _ _ _ _ = _
    unfold refillW
    split_ifs with hc
    · rfl
    · exact absurd hj hc

end Accept

/-! ## 4. The handle events of the re-fill are the projection's -/

section Handle
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] {hT hP hC : ℕ} (V : VerifierData F K hC (shapeVS hT hP))
  {T T' : TrVS F hT hP hC} {χ χ' : Coins frameVS K}

theorem lists0_congr (h : OffHandle hT hP hC T T' χ χ') :
    reqX0 hT hP hC V T' = reqX0 hT hP hC V T ∧ provX0 hT hP hC V T' = provX0 hT hP hC V T ∧
      reqP0 hT hP hC V T' = reqP0 hT hP hC V T ∧ provP0 hT hP hC V T' = provP0 hT hP hC V T := by
  have hc := compReqs_congr (K := K) V.computeNodes V.orbitC (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) _ _ h.comp
  have hw := walkLists_congr V.basis (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP)) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) _ _ (fun j hj => h.walk j (by omega))
  have ht := cellProvs_congr V.basis (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP)) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) _ _ (fun j hj => h.cell j (by omega))
  refine ⟨?_, ht, hc.2, hw.2⟩
  unfold reqX0; rw [hc.1, hw.1]

theorem evX_congr (h : OffHandle hT hP hC T T' χ χ') : evX hT hP hC V T' = evX hT hP hC V T := by
  obtain ⟨e1, e2, -, -⟩ := lists0_congr V h
  unfold evX; rw [e1, e2]

theorem evP_congr (h : OffHandle hT hP hC T T' χ χ') : evP hT hP hC V T' = evP hT hP hC V T := by
  obtain ⟨-, -, e3, e4⟩ := lists0_congr V h
  unfold evP; rw [e3, e4]

end Handle

end

end Nock.NockVMROM.Thm54.VclL.Handle.AcceptVSQ
