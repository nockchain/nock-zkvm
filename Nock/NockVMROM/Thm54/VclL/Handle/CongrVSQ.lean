/-
  Nock/NockVMROM/Thm54/VclL/Handle/CongrVSQ.lean

  Additive.

  Two VS trace pairs `T, T'` that agree on the compute columns `< 43`, the cell twin columns `< 226` and the
  walk twin columns `< 136` (everything except the re-filled handle blocks `43..57`, `226..231`, `136..150`),
  at two coin vectors that agree off the handle coins `11, 12`: every one of the eight non-handle VS summands
  (`cwalkVS`, `ctileVS`, `dyckVS`, `walkChainVS`, `fpExportIOVS`, `zeroVS`, `censusVS`, `valSummand`) has the
  same membership at `(T', χ')` as at `(T, χ)`.

  The check Q4 flagged: `valSummand` and `fpExportIOVS` have `dep ∋ 11, 12`, but their `mem` reads the coins
  `4..7` (and `valEv` the coins `2, 3` through `claimRecs`) and the trace through `qrC` (cell columns
  `shiftCol 129 130 j < 226`) and `qrW` (walk columns `shiftCol 21 25 j < 136`) only — `qrC_congr`,
  `qrW_congr`, `valEv_congr`, `fpEv_congr`.  It holds.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.SoundVS

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.CongrVSQ

open Nock Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.IOVS Nock.NockVMROM.Thm54.VclL.Handle.SoundVS
open Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS Nock.NockVMROM.Thm54.VclL.Handle.CensusVS
open Nock.NockVMROM.Thm54.VclL.Handle.WalkChainSumVS Nock.NockVMROM.Thm54.VclL.Handle.CWalkChipVS
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Module
open scoped Polynomial

noncomputable section

section Congr
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)

attribute [local instance] ClaimDenVS.quadCharF

/-- **The agreement of a re-fill with the original** (traces off the handle blocks, coins off `11, 12`). -/
structure OffHandle (T T' : TrVS F hT hP hC) (χ χ' : Coins frameVS K) : Prop where
  comp : ∀ j : Fin (tableVS hC).width, (j : ℕ) < 43 → T'.1 j = T.1 j
  cell : ∀ j : Fin ((shapeVS hT hP).table (tCS hT hP)).width, (j : ℕ) < 226 → T'.2 (tCS hT hP) j = T.2 (tCS hT hP) j
  walk : ∀ j : Fin ((shapeVS hT hP).table (tWS hT hP)).width, (j : ℕ) < 136 → T'.2 (tWS hT hP) j = T.2 (tWS hT hP) j
  coins : ∀ i : Fin frameVS.n, (i : ℕ) ≠ 11 → (i : ℕ) ≠ 12 → χ' i = χ i

variable {hT hP hC} {T T' : TrVS F hT hP hC} {χ χ' : Coins frameVS K}

theorem qrC_congr (h : OffHandle hT hP hC T T' χ χ') :
    qrC (T'.2 (tCS hT hP)) = qrC (T.2 (tCS hT hP)) := by
  funext j
  have hj : (j : ℕ) < 225 := j.isLt
  exact h.cell _ (by show shiftCol 129 130 j < 226; unfold shiftCol; split_ifs <;> omega)

theorem qrW_congr (h : OffHandle hT hP hC T T' χ χ') :
    qrW (T'.2 (tWS hT hP)) = qrW (T.2 (tWS hT hP)) := by
  funext j
  have hj : (j : ℕ) < 132 := j.isLt
  exact h.walk _ (by show shiftCol 21 25 j < 136; unfold shiftCol; split_ifs <;> omega)

theorem coin_eq (h : OffHandle hT hP hC T T' χ χ') (i : ℕ) (hi : i < 15) (h11 : i ≠ 11) (h12 : i ≠ 12) :
    χ' ⟨i, hi⟩ = χ ⟨i, hi⟩ := h.coins _ h11 h12

theorem zVS_congr (h : OffHandle hT hP hC T T' χ χ') : zVS δF χ' = zVS δF χ := by
  unfold zVS; rw [coin_eq h 2 (by decide) (by decide) (by decide), coin_eq h 3 (by decide) (by decide) (by decide)]

variable (V : VerifierData F K hC (shapeVS hT hP))

theorem rowsVS_congr (h : OffHandle hT hP hC T T' χ χ') : rowsVS hT hP hC V T' = rowsVS hT hP hC V T := by
  unfold rowsVS; rw [qrC_congr h]

theorem cwalk_congr (h : OffHandle hT hP hC T T' χ χ') :
    (cwalkVS hT hP hC V).mem T' χ' ↔ (cwalkVS hT hP hC V).mem T χ := by
  rw [mem_cwalkVS, mem_cwalkVS, rowsC_congr hT hP hC V h.comp]
  show (χ' ⟨13, _⟩, χ' ⟨14, _⟩) ∈ _ ↔ (χ ⟨13, _⟩, χ ⟨14, _⟩) ∈ _
  rw [coin_eq h 13 (by decide) (by decide) (by decide), coin_eq h 14 (by decide) (by decide) (by decide)]

theorem ctile_congr (h : OffHandle hT hP hC T T' χ χ') :
    (ctileVS hT hP hC V).mem T' χ' ↔ (ctileVS hT hP hC V).mem T χ := by
  rw [mem_ctileVS, mem_ctileVS, rowsC_congr hT hP hC V h.comp]
  show χ' ⟨13, _⟩ ∈ _ ↔ χ ⟨13, _⟩ ∈ _
  rw [coin_eq h 13 (by decide) (by decide) (by decide)]

theorem dyck_congr (h : OffHandle hT hP hC T T' χ χ') :
    (dyckVS δF hT hP hC V).mem T' χ' ↔ (dyckVS δF hT hP hC V).mem T χ := by
  rw [mem_dyckVS, mem_dyckVS, rowsVS_congr V h, zVS_congr δF h]

theorem zero_congr (h : OffHandle hT hP hC T T' χ χ') :
    (zeroVS δF hT hP hC).mem T' χ' ↔ (zeroVS δF hT hP hC).mem T χ := by
  rw [mem_zeroVS, mem_zeroVS, zVS_congr δF h]

theorem census_congr (h : OffHandle hT hP hC T T' χ χ') :
    (censusVS δF hT hP hC V).mem T' χ' ↔ (censusVS δF hT hP hC V).mem T χ := by
  rw [mem_censusVS, mem_censusVS, rowsVS_congr V h, zVS_congr δF h]

theorem valEv_congr (m : ClaimMsgVS) (h : OffHandle hT hP hC T T' χ χ') :
    valEv δF hT hP hC V m T' χ' = valEv δF hT hP hC V m T χ := by
  unfold valEv valReqs valProvs
  rw [qrC_congr h, claimRecs_congr δF V.claim m χ' χ (coin_eq h 2 (by decide) (by decide) (by decide))
    (coin_eq h 3 (by decide) (by decide) (by decide))]

theorem val_congr (m : ClaimMsgVS) (h : OffHandle hT hP hC T T' χ χ') :
    (valSummand δF hT hP hC V m).mem T' χ' ↔ (valSummand δF hT hP hC V m).mem T χ := by
  rw [mem_valSummand, mem_valSummand, valEv_congr δF V m h,
    coin_eq h 4 (by decide) (by decide) (by decide), coin_eq h 5 (by decide) (by decide) (by decide),
    coin_eq h 6 (by decide) (by decide) (by decide), coin_eq h 7 (by decide) (by decide) (by decide)]

variable [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]

theorem walkChain_congr (h : OffHandle hT hP hC T T' χ χ') :
    (walkChainVS δF hT hP kr hC V).mem T' χ' ↔ (walkChainVS δF hT hP kr hC V).mem T χ := by
  have hw : wOfTrVS δF hT hP kr hC V T' = wOfTrVS δF hT hP kr hC V T := by
    unfold wOfTrVS; rw [qrW_congr h]
  rw [mem_walkChainVS, mem_walkChainVS, hw, coin_eq h 0 (by decide) (by decide) (by decide),
    coin_eq h 1 (by decide) (by decide) (by decide)]

theorem fpEv_congr (h : OffHandle hT hP hC T T' χ χ') :
    fpEv δF hT hP kr hC V T' = fpEv δF hT hP kr hC V T := by
  unfold fpEv fpReqs fpProvs
  rw [qrW_congr h, qrC_congr h]

theorem fp_congr (h : OffHandle hT hP hC T T' χ χ') :
    (fpExportIOVS δF hT hP kr hC V).mem T' χ' ↔ (fpExportIOVS δF hT hP kr hC V).mem T χ := by
  rw [mem_fpExportIOVS, mem_fpExportIOVS, fpEv_congr δF kr V h,
    coin_eq h 4 (by decide) (by decide) (by decide), coin_eq h 5 (by decide) (by decide) (by decide),
    coin_eq h 6 (by decide) (by decide) (by decide), coin_eq h 7 (by decide) (by decide) (by decide)]

end Congr

end

end Nock.NockVMROM.Thm54.VclL.Handle.CongrVSQ
