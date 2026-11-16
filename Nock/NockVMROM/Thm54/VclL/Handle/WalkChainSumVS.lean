/-
  Nock/NockVMROM/Thm54/VclL/Handle/WalkChainSumVS.lean

* `dyckVS` (coins `{2, 3}`, `dep = ∅`): the dyck-root seeds of the decoded cell table;
    `dyck_VS` : outside the summand, `hdy`.
  * `walkChainVS` (coins `{0, 1}`, `dep = coinsBelow frameVS 1`): W1's `walkEvent` at the coin-free walk
    data `wOfTrVS`; `walkChain_VS` : outside the summand, `hout`.
  * `fpExportIOVS` (coins `{4, 5, 6, 7}`, `dep = coinsBelow frameVS 1`): the fingerprint-export IO event
    with the walk's consumed keys as requests and `cXRec` as providers (coin-free lists);
    `keysExported_VS` : outside the summand (and `hV`, `AcceptsG`), `hKX`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkGenVS
import Nock.NockVMROM.Thm54.VclL.Chips.ExportTelescopeW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.WalkChainSumVS

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Module
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH Nock.NockVMROM.Thm54.VclL.Handle.ServeH
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVS
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVS Nock.NockVMROM.Thm54.VclL.Handle.ServedVS
open Nock.NockVMROM.Thm54.VclL.Handle.ServedPVS
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS Nock.NockVMROM.Thm54.VclL.Handle.CensusVS
open Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS Nock.NockVMROM.Thm54.VclL.Handle.ClaimVS
open Nock.NockVMROM.Thm54.VclL.Handle.WalkGenVS
open scoped Polynomial

noncomputable section

theorem shiftW_lt (j : Fin 132) : shiftCol 21 25 j < 151 := by
  have := j.isLt; unfold shiftCol; split_ifs <;> omega

theorem shiftW_lt93 (j : ℕ) (hj : j < 93) : shiftCol 21 25 j < 151 := by
  unfold shiftCol; split_ifs <;> omega

/-- The restriction of the walk twin trace to the original walk chip's `132` columns (as `restrictWalk`). -/
def qrW {F : Type} [Field F] (q : Fin 151 → F[X]) : Fin 132 → F[X] :=
  fun j => q ⟨shiftCol 21 25 j, shiftW_lt j⟩

section VS
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)
  {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}

attribute [local instance] ClaimDenVS.quadCharF

/-! ## 1. The dyck-root summand -/

/-- **The dyck-root summand at VS** (coins `{2, 3}`, `dep = ∅`, weight `T · (2·fuelChip − 1)`). -/
def dyckVS (V : VerifierData F K hC (shapeVS hT hP)) :
    BadSummand frameVS K (TrVS F hT hP hC) (TracesStaged frameVS (tableVS hC) (shapeVS hT hP)) :=
  cellDyckRootSummand (algebraMap F K δF) frameVS ⟨2, by decide⟩ ⟨3, by decide⟩
    (TracesStaged frameVS (tableVS hC) (shapeVS hT hP)) (rowsVS hT hP hC V) (V.memRows (tCS hT hP)) fuelChip
    (fun tr => (rowsVS_length hT hP hC V tr).le)
    (fun Q hQ χ χ' => rowsVS_const hT hP hC V Q hQ χ χ')

theorem mem_dyckVS (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) (χ : Coins frameVS K) :
    (dyckVS δF hT hP hC V).mem tr χ ↔
      zVS δF χ ∈ cellDyckRootSeeds (Kfp := Quad (algebraMap F K δF)) fuelChip (rowsVS hT hP hC V tr) := by
  unfold dyckVS cellDyckRootSummand
  refine (towerSeedSummand_mem_iff (algebraMap F K δF) frameVS ⟨2, by decide⟩ ⟨3, by decide⟩ _ _ _ _ _ tr χ).trans ?_
  unfold zVS
  convert Iff.rfl

/-- **Outside the dyck summand, `hdy`.** -/
theorem dyck_VS (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : ¬ (dyckVS δF hT hP hC V).mem (msg.traces χ) χ) :
    zVS δF χ ∉ cellDyckRootSeeds (Kfp := Quad (algebraMap F K δF)) fuelChip
      ((tVS δF hT hP kr hC V msg χ).map (·.b0)) := by
  rw [mem_dyckVS, rowsVS_at] at h
  exact h

/-! ## 2. The walk summand -/

/-- Walk-twin columns `< 21 + ...` hit by `qrW` of a column `< 93` are of round `≤ 1`. -/
theorem colRound_shiftW_le (j : ℕ) (hj : j < 93) :
    ((shapeVS hT hP).table (tWS hT hP)).colRound ⟨shiftCol 21 25 j, shiftW_lt93 j hj⟩ ≤ 1 := by
  change colRoundWH ⟨shiftCol 21 25 j, shiftW_lt93 j hj⟩ ≤ 1
  simp only [colRoundWH, shiftCol]
  split_ifs <;> omega

/-- **The coin-free walk data of a trace pair** (coins and publics `0`, the restricted walk columns). -/
def wOfTrVS (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) :
    WalkVCL.WalkData (ringChar F) (Quad (algebraMap F K δF)) :=
  walkDataOf δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
    (fun _ => 0) (fun _ => 0) (qrW (tr.2 (tWS hT hP)))

theorem wOfTrVS_h (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) :
    (wOfTrVS δF hT hP kr hC V tr).h ≤ V.memRows (tWS hT hP) := le_refl _

theorem wOfTrVS_readsOn (V : VerifierData F K hC (shapeVS hT hP))
    (Q : Coins frameVS K → TrVS F hT hP hC)
    (hQ : TracesStaged frameVS (tableVS hC) (shapeVS hT hP) Q) :
    ReadsOnC frameVS (coinsBelow frameVS 1) (fun χ => wOfTrVS δF hT hP kr hC V (Q χ)) := by
  intro χ χ' hχ
  have hin : ∀ i : Fin frameVS.n, frameVS.sampledAfter i < 1 → χ i = χ' i := fun i hi =>
    hχ i (by simp only [coinsBelow, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi)
  refine walkDataOf_congr δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP))
    (V.orbitM (tWS hT hP)) _ _ (show 93 ≤ 132 by omega) (show 93 ≤ 132 by omega) ?_ _ _ _ _
  intro j hj
  exact hQ.2 (tWS hT hP) ⟨shiftCol 21 25 j, shiftW_lt93 j hj⟩ χ χ' fun i hi =>
    hin i (lt_of_lt_of_le hi (colRound_shiftW_le hT hP j hj))

theorem walkCoins_disj :
    Disjoint ({⟨0, by decide⟩, ⟨1, by decide⟩} : Finset (Fin frameVS.n)) (coinsBelow frameVS 1) := by
  decide

variable [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]

/-- **The walk-chain summand at VS** (coins `{0, 1}`, reading `coinsBelow frameVS 1`, weight
`|𝕂| · 15 · W`). -/
def walkChainVS (V : VerifierData F K hC (shapeVS hT hP)) :
    BadSummand frameVS K (TrVS F hT hP hC) (TracesStaged frameVS (tableVS hC) (shapeVS hT hP)) :=
  pairCoinSummand frameVS ⟨0, by decide⟩ ⟨1, by decide⟩ (coinsBelow frameVS 1) walkCoins_disj
    (TracesStaged frameVS (tableVS hC) (shapeVS hT hP))
    (fun tr => walkEvent (algebraMap F K δF) (wOfTrVS δF hT hP kr hC V tr))
    (Fintype.card K * (15 * V.memRows (tWS hT hP)))
    (fun tr => walkEvent_card _ _ (wOfTrVS_h δF hT hP kr hC V tr))
    (fun Q hQ χ χ' hχ => by simp only [wOfTrVS_readsOn δF hT hP kr hC V Q hQ χ χ' hχ])

theorem mem_walkChainVS (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC)
    (χ : Coins frameVS K) :
    (walkChainVS δF hT hP kr hC V).mem tr χ ↔
      (χ ⟨0, by decide⟩, χ ⟨1, by decide⟩) ∈ walkEvent (algebraMap F K δF) (wOfTrVS δF hT hP kr hC V tr) := by
  show _ ∈ Finset.univ.filter _ ↔ _
  erw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem wOfTrVS_at (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K) :
    wOfTrVS δF hT hP kr hC V (msg.traces χ) = wDataVS δF hT hP kr hC V msg χ :=
  walkDataOf_congr δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP)) _ _
    (show 93 ≤ 132 by omega) (show 93 ≤ 132 by omega) (fun j hj => rfl) _ _ _ _

/-- **Outside the walk-chain summand, `hout`.** -/
theorem walkChain_VS (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : ¬ (walkChainVS δF hT hP kr hC V).mem (msg.traces χ) χ) :
    (χ ⟨0, by decide⟩, χ ⟨1, by decide⟩) ∉ walkEvent (algebraMap F K δF) (wDataVS δF hT hP kr hC V msg χ) := by
  rw [mem_walkChainVS, wOfTrVS_at] at h
  exact h

/-! ## 3. The fingerprint-export IO summand -/

/-- **Consumers of the fingerprint export lookup**: the walk's consumed keys (zero coins, publics). -/
def fpReqs (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) :
    List (Fin 11 → Quad (algebraMap F K δF)) :=
  walkXInternal δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
    (fun _ => 0) (fun _ => 0) (qrW (tr.2 (tWS hT hP)))

/-- **Providers of the fingerprint export lookup**: two per cell row. -/
def fpProvs (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) :
    List ((Fin 11 → Quad (algebraMap F K δF)) × F) :=
  cXRec δF V.basis (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP)) (fun _ => 0) (fun _ => 0)
    (qrC (tr.2 (tCS hT hP)))

theorem fpReqs_length (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) :
    (fpReqs δF hT hP kr hC V tr).length = V.memRows (tWS hT hP) :=
  walkXInternal_length δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP))
    (V.orbitM (tWS hT hP)) _ _ _

theorem fpProvs_length (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) :
    (fpProvs δF hT hP hC V tr).length ≤ 2 * V.memRows (tCS hT hP) :=
  cXRec_length δF V.basis (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP)) _ _ _

def fpEv (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) :
    Finset (Quad (algebraMap F K δF) × Quad (algebraMap F K δF)) :=
  FiniteIO.IOFailureEventW (fpReqs δF hT hP kr hC V tr) (liftWts (fpProvs δF hT hP hC V tr))

theorem fpEv_card (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) :
    (fpEv δF hT hP kr hC V tr).card ≤
      FiniteIO.ioFailureUnionBound 11 (V.memRows (tWS hT hP)) (2 * V.memRows (tCS hT hP))
        (Fintype.card (Quad (algebraMap F K δF))) := by
  unfold fpEv
  refine (FiniteIO.IOFailureEventW_card_le _ _).trans (ioUB_mono _ _ _ _ _ _
    (fpReqs_length δF hT hP kr hC V tr).le ?_)
  rw [liftWts_length]
  exact fpProvs_length δF hT hP hC V tr

theorem fpLists_staged (V : VerifierData F K hC (shapeVS hT hP))
    (Q : Coins frameVS K → TrVS F hT hP hC)
    (hQ : TracesStaged frameVS (tableVS hC) (shapeVS hT hP) Q) (χ χ' : Coins frameVS K)
    (hdep : ∀ j ∈ coinsBelow frameVS 1, χ j = χ' j) :
    fpReqs δF hT hP kr hC V (Q χ) = fpReqs δF hT hP kr hC V (Q χ') ∧
      fpProvs δF hT hP hC V (Q χ) = fpProvs δF hT hP hC V (Q χ') := by
  have hin : ∀ i : Fin frameVS.n, frameVS.sampledAfter i < 1 → χ i = χ' i := fun i hi =>
    hdep i (by simp only [coinsBelow, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi)
  refine ⟨?_, ?_⟩
  · unfold fpReqs
    refine wXInt_congr δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP))
      (V.orbitM (tWS hT hP)) _ _ _ _ _ _ (by norm_num) (by norm_num) fun j hj => ?_
    exact hQ.2 (tWS hT hP) ⟨shiftCol 21 25 j, shiftW_lt93 j hj⟩ χ χ' fun i hi =>
      hin i (lt_of_lt_of_le hi (colRound_shiftW_le hT hP j hj))
  · unfold fpProvs
    refine cXRec_congr δF V.basis (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP)) _ _ _ _ _ _
      (by norm_num) (by norm_num) fun j hj => ?_
    exact hQ.2 (tCS hT hP) _ χ χ' fun i hi =>
      hin i (lt_of_lt_of_le hi (colRound_shift_le hT hP ⟨j, by omega⟩ hj))

/-- **The fingerprint-export IO summand** (coins `{4, 5, 6, 7}`, reading `coinsBelow frameVS 1`). -/
def fpExportIOVS (V : VerifierData F K hC (shapeVS hT hP)) :
    BadSummand frameVS K (TrVS F hT hP hC) (TracesStaged frameVS (tableVS hC) (shapeVS hT hP)) where
  coins := (ioSpecVS (algebraMap F K δF)).dep
  dep := coinsBelow frameVS 1
  disj := ioSpecVS_disj _
  badSet tr χ := Finset.univ.filter fun v =>
    (ioSpecVS (algebraMap F K δF)).pair (extIO (ioSpecVS (algebraMap F K δF)) v) ∈ fpEv δF hT hP kr hC V tr
  weight := FiniteIO.ioFailureUnionBound 11 (V.memRows (tWS hT hP)) (2 * V.memRows (tCS hT hP))
    (Fintype.card (Quad (algebraMap F K δF)))
  card_le tr χ := by
    refine le_trans (Finset.card_le_card_of_injOn
      (fun v => (ioSpecVS (algebraMap F K δF)).pair (extIO (ioSpecVS (algebraMap F K δF)) v)) ?_ ?_)
      (fpEv_card δF hT hP kr hC V tr)
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
      exact hv
    · intro v _ v' _ h; exact extIO_inj _ h
  readsOn Q hQ χ χ' hdep := by
    obtain ⟨e1, e2⟩ := fpLists_staged δF hT hP kr hC V Q hQ χ χ' hdep
    show (Finset.univ.filter fun v => _ ∈ fpEv δF hT hP kr hC V (Q χ)) =
      Finset.univ.filter fun v => _ ∈ fpEv δF hT hP kr hC V (Q χ')
    unfold fpEv
    rw [e1, e2]

theorem mem_fpExportIOVS (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC)
    (χ : Coins frameVS K) :
    (fpExportIOVS δF hT hP kr hC V).mem tr χ ↔
      (Quad.mk (algebraMap F K δF) (χ ⟨4, by decide⟩) (χ ⟨6, by decide⟩),
        Quad.mk (algebraMap F K δF) (χ ⟨5, by decide⟩) (χ ⟨7, by decide⟩)) ∈ fpEv δF hT hP kr hC V tr := by
  unfold BadSummand.mem
  show (fun i : (ioSpecVS (algebraMap F K δF)).dep => χ i) ∈
      (Finset.univ.filter fun v : (ioSpecVS (algebraMap F K δF)).dep → K =>
        (ioSpecVS (algebraMap F K δF)).pair (extIO (ioSpecVS (algebraMap F K δF)) v) ∈
          fpEv δF hT hP kr hC V tr) ↔ _
  rw [Finset.mem_filter, pair_extIO, ioSpecVS_pair]
  simp

theorem fpLists_at (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K) :
    fpReqs δF hT hP kr hC V (msg.traces χ) =
        walkXInternal δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
          (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
          (restrictWalk δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
            (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
            (qWVS δF hT hP kr hC V msg χ)) ∧
      fpProvs δF hT hP hC V (msg.traces χ) =
        cellXRecords δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP))
          (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
          (qCellVS δF hT hP kr hC V msg χ) := by
  refine ⟨?_, ?_⟩
  · unfold fpReqs
    exact wXInt_congr δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP))
      (V.orbitM (tWS hT hP)) _ _ _ _ _ _ (by norm_num) (by rw [walk_w]; norm_num) fun j hj => rfl
  · unfold fpProvs
    rw [cXRec_chip]
    exact cXRec_congr δF V.basis (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP)) _ _ _ _ _ _
      (by norm_num) (by rw [cell_w]; norm_num) fun j hj => rfl

/-- **`KeysExported` outside the fingerprint-export IO summand.** -/
theorem keysExported_VS (V : VerifierData F K hC (shapeVS hT hP))
    (hV : V.Checks (fun a => reqBoundVS hT hP hC V a + internalBoundVS hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : AcceptsG V msg χ)
    (hfp : ¬ (fpExportIOVS δF hT hP kr hC V).mem (msg.traces χ) χ) :
    KeysExported (tVS δF hT hP kr hC V msg χ) (wDataVS δF hT hP kr hC V msg χ).X := by
  obtain ⟨hg, -⟩ := compute_facts δF hT hP kr hC V msg χ h
  obtain ⟨-, hwT, hsatT⟩ := cell_facts δF hT hP kr hC V msg χ h
  obtain ⟨-, hwW, hsatW⟩ := walk_facts δF hT hP kr hC V msg χ h
  have hsatC := cellChipH_restrict_sat δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
    (V.orbitM (tCS hT hP)) (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    _ hsatT.1
  have hbindC := cellChipH_restrict_bind δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
    (V.orbitM (tCS hT hP)) (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    _ hsatT.2
  have hsatP := walkChipH_restrict_sat δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP))
    (V.orbitM (tWS hT hP)) (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    _ hsatW.1
  have hbindP := walkChipH_restrict_bind δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP))
    (V.orbitM (tWS hT hP)) (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    _ hsatW.2
  have hchar : ringChar (Quad (algebraMap F K δF)) = ringChar F := ringChar_quad_eq δF
  haveI : CharP (Quad (algebraMap F K δF)) (ringChar F) := by rw [← hchar]; exact ringChar.charP _
  have hcons1 := hV.hcons 1
  simp [reqBoundVS, internalBoundVS, hchar] at hcons1
  obtain ⟨e1, e2⟩ := fpLists_at δF hT hP kr hC V msg χ
  rw [mem_fpExportIOVS] at hfp
  unfold fpEv at hfp
  rw [e1, e2] at hfp
  have hρ1 : msg.requests χ 1 = 0 := hg.2.2.2.2.1
  refine walk_keys_exported δF kr V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
    (V.orbitM (tCS hT hP)) (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
    (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) _ _
    hsatC hbindC (hV.memNodes_injective _) (hV.hadjM _) hsatP hbindP (hV.memNodes_injective _)
    (hV.hadjM _) _ _ (chalsOK_VS δF χ) 0 ?_ (p := ringChar F) [] (by simp) (by simp)
    (fun hc => hfp (FiniteIO.mem_IOFailureEventW_iff.mpr (Or.inl hc)))
    (fun hc => hfp (FiniteIO.mem_IOFailureEventW_iff.mpr (Or.inr (Or.inr hc)))) ?_
  · rw [show (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2 2) =
        pubsC δF (rho3 δF (msg.requests χ)) (msg.msg2M χ).1 2 by simp [pubsCH, CellH.pubH],
      show (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2 3) =
        pubsC δF (rho3 δF (msg.requests χ)) (msg.msg2M χ).1 3 by simp [pubsCH, CellH.pubH],
      show (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2 0) =
        pubsP δF (rho3 δF (msg.requests χ)) (msg.msg2M χ).1 0 by simp [pubsWH, WalkHC.pubX, WalkHC.pubP],
      show (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2 1) =
        pubsP δF (rho3 δF (msg.requests χ)) (msg.msg2M χ).1 1 by simp [pubsWH, WalkHC.pubX, WalkHC.pubP],
      pubsC_23, pubsP_01, zero_add]
    show (msg.requests χ 1) + _ = _
    rw [hρ1, zero_add]
  · rw [List.nil_append, walkXInternal_length]
    exact hcons1

end VS

end

end Nock.NockVMROM.Thm54.VclL.Handle.WalkChainSumVS
