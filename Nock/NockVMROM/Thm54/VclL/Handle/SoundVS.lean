/-
  Nock/NockVMROM/Thm54/VclL/Handle/SoundVS.lean

* `cwalkVS` — the compute walk event `WalkTreeVS.cwEvent` of the decoded compute rows `rowsC` at
    coins `{13, 14} = (αW, γW)`, `dep = ∅` (the rows read round-0 columns only), weight `|𝕂|·6N`;
    `ctileVS` — the `α`-tiling set at coin `{13}`, `dep = ∅`, weight `2N + 2`.
  * the lists `sumCVS = [cwalkVS, ctileVS]`, `sumMVS = [dyckVS, walkChainVS, fpExportIOVS]`,
    `jointVS = [zeroVS, censusVS, valSummand, ioSummandHX, ioSummandHP]`.
  * **`hsoundVS`**: `V.Checks → AcceptsG → outside allSummandsG → HoldsF (ringChar K) V.claim`, and
    **`standaloneVS_sound`**: the soundness half of `StandaloneG` at VS via `standaloneG_of_sound`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CWalkChipVS
import Nock.NockVMROM.Thm54.VclL.Handle.WalkChainSumVS
import Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVS
import Nock.NockVMROM.Thm54.VclL.Compute.SummandsQ7

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.SoundVS

open Nock Nock.Walk Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Module
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVS
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVS Nock.NockVMROM.Thm54.VclL.Handle.ServedVS
open Nock.NockVMROM.Thm54.VclL.Handle.ServedPVS Nock.NockVMROM.Thm54.VclL.Handle.WalkGenVS
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS Nock.NockVMROM.Thm54.VclL.Handle.CensusVS
open Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVS Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVS
open Nock.NockVMROM.Thm54.VclL.Handle.WalkChainSumVS Nock.NockVMROM.Thm54.VclL.Handle.CWalkChipVS
open Nock.NockVMROM.Thm54.SVGenuineF (HoldsF)
open scoped Polynomial

noncomputable section

section VS
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)

attribute [local instance] ClaimDenVS.quadCharF

/-! ## 1. The compute-walk summands -/

/-- Along a staged strategy the decoded compute rows are coin-independent (round-0 columns). -/
theorem rowsC_staged (V : VerifierData F K hC (shapeVS hT hP)) (Q : Coins frameVS K → TrVS F hT hP hC)
    (hQ : TracesStaged frameVS (tableVS hC) (shapeVS hT hP) Q) (χ χ' : Coins frameVS K) :
    rowsC hT hP hC V (Q χ).1 = rowsC hT hP hC V (Q χ').1 := by
  apply rowsC_congr
  intro j hj
  exact hQ.1 j χ χ' fun i hi => absurd hi (by
    show ¬ frameVS.sampledAfter i < (if (j : ℕ) < ChipH.round0W then 0 else 1)
    rw [if_pos (by simp only [ChipH.round0W]; omega)]; omega)

theorem cwalkCoins_disj : Disjoint ({cAlphaW, cGamW} : Finset (Fin frameVS.n)) ∅ :=
  Finset.disjoint_empty_right _

/-- **The compute-walk summand** (coins `{13, 14} = (αW, γW)`, `dep = ∅`, weight `|𝕂|·6N`). -/
def cwalkVS (V : VerifierData F K hC (shapeVS hT hP)) :
    BadSummand frameVS K (TrVS F hT hP hC) (TracesStaged frameVS (tableVS hC) (shapeVS hT hP)) :=
  pairCoinSummand frameVS cAlphaW cGamW ∅ cwalkCoins_disj _
    (fun tr => cwEvent (K := K) (rowsC hT hP hC V tr.1) V.N) (Fintype.card K * (6 * V.N))
    (fun tr => cwEvent_card_le _ le_rfl)
    (fun Q hQ χ χ' _ => by simp only [rowsC_staged hT hP hC V Q hQ χ χ'])

theorem mem_cwalkVS (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) (χ : Coins frameVS K) :
    (cwalkVS hT hP hC V).mem tr χ ↔ (χ cAlphaW, χ cGamW) ∈ cwEvent (K := K) (rowsC hT hP hC V tr.1) V.N := by
  show _ ∈ Finset.univ.filter _ ↔ _
  exact ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩

theorem cAlphaW_not_mem : cAlphaW ∉ (∅ : Finset (Fin frameVS.n)) := Finset.notMem_empty _

/-- **The `αW`-tiling summand** (coin `{13}`, `dep = ∅`, weight `2N + 2`). -/
def ctileVS (V : VerifierData F K hC (shapeVS hT hP)) :
    BadSummand frameVS K (TrVS F hT hP hC) (TracesStaged frameVS (tableVS hC) (shapeVS hT hP)) :=
  VclL.Compute.SummandsQ7.coinSummand cAlphaW ∅ cAlphaW_not_mem
    (fun tr _ => tileSet (K := K) (foOf (rowsC hT hP hC V tr.1)) V.N) (2 * V.N + 2)
    (fun tr _ => tileSet_card _ (foOf_le _) _)
    (fun Q hQ χ χ' _ => by simp only [rowsC_staged hT hP hC V Q hQ χ χ'])

theorem mem_ctileVS (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) (χ : Coins frameVS K) :
    (ctileVS hT hP hC V).mem tr χ ↔ χ cAlphaW ∈ tileSet (K := K) (foOf (rowsC hT hP hC V tr.1)) V.N :=
  VclL.Compute.SummandsQ7.coinSummand_mem _ _ _ _ _ _ _ tr χ

theorem ringChar_KF : ringChar K = ringChar F := (Algebra.ringChar_eq F K).symm

/-! ## 2. The summand lists -/

variable [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]

/-- **The compute summands**: the compute walk and its tiling. -/
def sumCVS (V : VerifierData F K hC (shapeVS hT hP)) (_x : ClaimMsgVS) : SummandsVS (F := F) (K := K) hT hP hC :=
  [cwalkVS hT hP hC V, ctileVS hT hP hC V]

/-- **The memory summands**: the dyck-root seeds, W1's walk chain, the fingerprint export. -/
def sumMVS (V : VerifierData F K hC (shapeVS hT hP)) (_y : Unit) : SummandsVS (F := F) (K := K) hT hP hC :=
  [dyckVS δF hT hP hC V, walkChainVS δF hT hP kr hC V, fpExportIOVS δF hT hP kr hC V]

/-- **The joint summands**: zero seed, T2 + claim census, validity IO, handle IO (export, path). -/
def jointVS (V : VerifierData F K hC (shapeVS hT hP)) (x : ClaimMsgVS) (_y : Unit) :
    SummandsVS (F := F) (K := K) hT hP hC :=
  [zeroVS δF hT hP hC, censusVS δF hT hP hC V, valSummand δF hT hP hC V x, ioSummandHX hT hP hC V,
    ioSummandHP hT hP hC V]

/-! ## 3. Soundness -/

/-- **`hsound` at VS**: an accepted VS trace outside every summand proves the claim. -/
theorem hsoundVS (V : VerifierData F K hC (shapeVS hT hP))
    (hV : V.Checks (fun a => (compCoreVS δF hT hP hC (sumCVS hT hP hC)).reqBound V a +
      (memCoreVS δF hT hP kr hC (sumMVS δF hT hP kr hC)).internalBound V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVS δF hT hP hC (sumCVS hT hP hC)) (memCoreVS δF hT hP kr hC (sumMVS δF hT hP kr hC)))
    (χ : Coins frameVS K) (h : AcceptsG V msg χ)
    (hout : ∀ s ∈ allSummandsG (CC := compCoreVS δF hT hP hC (sumCVS hT hP hC))
        (MC := memCoreVS δF hT hP kr hC (sumMVS δF hT hP kr hC)) V msg.msg0C msg.msg0M (jointVS δF hT hP hC),
      ¬ s.mem (msg.traces χ) χ) :
    HoldsF (ringChar K) V.claim := by
  have hin : ∀ s, s ∈ allSummandsG (CC := compCoreVS δF hT hP hC (sumCVS hT hP hC))
      (MC := memCoreVS δF hT hP kr hC (sumMVS δF hT hP kr hC)) V msg.msg0C msg.msg0M (jointVS δF hT hP hC) →
      ¬ s.mem (msg.traces χ) χ := hout
  simp only [allSummandsG, compCoreVS, memCoreVS, sumCVS, sumMVS, jointVS, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hin
  have hCW := hin (cwalkVS hT hP hC V) (by simp)
  have hCT := hin (ctileVS hT hP hC V) (by simp)
  have hDy := hin (dyckVS δF hT hP hC V) (by simp)
  have hWC := hin (walkChainVS δF hT hP kr hC V) (by simp)
  have hFP := hin (fpExportIOVS δF hT hP kr hC V) (by simp)
  have h0 := hin (zeroVS δF hT hP hC) (by simp)
  have hc := hin (censusVS δF hT hP hC V) (by simp)
  have hval := hin (valSummand δF hT hP hC V msg.msg0C) (by simp)
  have hX := hin (ioSummandHX hT hP hC V) (by simp)
  have hPm := hin (ioSummandHP hT hP hC V) (by simp)
  -- the row semantics
  have hrow := fun i => rowSem_VS δF hT hP kr hC V hV msg χ h hX hPm hval h0 hc
    (dyck_VS δF hT hP kr hC V msg χ hDy) (keysExported_VS δF hT hP kr hC V hV msg χ h hFP)
    (walkChain_VS δF hT hP kr hC V msg χ hWC) i
  -- the compute walk
  set rows := rowsC hT hP hC V (msg.Qc χ) with hrows
  obtain ⟨ln, cnt, acc, hw, hacc, hne, hterm⟩ := cwalk_sat δF hT hP kr hC V hV msg χ h
  have hval1 : BFSValidF 1 (foOf rows) V.N := bfs_of_walk hw hne
  have htile : 1 + Sf (foOf rows) V.N = V.N := tile_of_walk hw hterm (by
    intro hm; exact hCT ((mem_ctileVS hT hP hC V (msg.traces χ) χ).mpr hm))
  have hG : ForestReconGoal (stVS K) (lblOf rows) 1 V.N :=
    goal_of_not_mem rows htile hval1 ⟨ln, cnt, acc, hw, hacc⟩ (by
      intro hm; exact hCW ((mem_cwalkVS hT hP hC V (msg.traces χ) χ).mpr hm))
  haveI : CharP K (ringChar F) := by rw [← ringChar_KF (F := F) (K := K)]; exact ringChar.charP K
  obtain ⟨t, hroot, hnode, hlink⟩ := tree_of_goal (K := K) (ringChar F) rows V.hN
    (fun i _ _ => rowsC_small hT hP hC hV.hF V (msg.Qc χ) i) hG
  -- the row tree
  have hOK : RowsOK Prod.snd (ringChar F) (denVS δF hT hP kr hC V msg χ) t := by
    refine ⟨fun u hu => ?_, fun u hu => hlink u hu⟩
    obtain ⟨i, hi1, hih, hui⟩ := hnode u hu
    obtain ⟨j0, hs, hsem⟩ := hrow ⟨i - 1, by omega⟩
    rw [hui]
    show RowSem _ _ (rowsC hT hP hC V (msg.Qc χ) i)
    have := rowsC_eq δF hT hP kr hC V msg χ ⟨i - 1, by omega⟩ hs
    rw [show i - 1 + 1 = i by omega] at this
    rw [this]; exact hsem
  obtain ⟨hrs, hrf, hre⟩ := rowsC_root δF hT hP kr hC V hV msg χ h
  have hcl := claim_handles_VS' δF hT hP kr hC V hV msg χ h hval h0 hc
  rw [ringChar_KF (F := F) (K := K)]
  refine holdsF_of_rowsVS Prod.snd (denOK_denH _) t hOK V.claim ?_ ?_ ?_
  · rw [hroot]; show denVS δF hT hP kr hC V msg χ (rows 1).s = _; rw [hrs]; exact hcl 0
  · rw [hroot]; show denVS δF hT hP kr hC V msg χ (rows 1).f = _; rw [hrf]; exact hcl 1
  · rw [hroot]; show denVS δF hT hP kr hC V msg χ (rows 1).e = _; rw [hre]; exact hcl 2

/-- **`StandaloneG` at the VS instance, through its soundness half** (`standaloneG_of_sound`; the
completeness half is vacuous here: `Honest := Empty` in `compCoreVS` / `memCoreVS`). -/
theorem standaloneVS_sound :
    StandaloneG (compCoreVS δF hT hP hC (sumCVS (F := F) (K := K) hT hP hC)) (memCoreVS δF hT hP kr hC (sumMVS (F := F) (K := K) δF hT hP kr hC))
      (jointVS (F := F) (K := K) δF hT hP hC) :=
  standaloneG_of_sound (CC := compCoreVS δF hT hP hC (sumCVS (F := F) (K := K) hT hP hC))
    (MC := memCoreVS δF hT hP kr hC (sumMVS (F := F) (K := K) δF hT hP kr hC)) (jointVS (F := F) (K := K) δF hT hP hC)
    (fun V hV msg χ h hout => hsoundVS δF hT hP kr hC V hV msg χ h hout)

end VS

end

end Nock.NockVMROM.Thm54.VclL.Handle.SoundVS
