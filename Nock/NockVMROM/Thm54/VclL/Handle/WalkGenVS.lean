/-
  Nock/NockVMROM/Thm54/VclL/Handle/WalkGenVS.lean

  Additive.

  `hHX` comes from `walk_hHX_of_served` + the served handle-export lookup; the T2 census from
  `census_good`.
  `denOK_denH`: `denH` atoms denote themselves, serials decode to cells.
  **`rowSem_VS`**: with `xok_VS` / `pok_VS` / `rowSem_of_chip`, every compute row of an accepted VS
  trace satisfies `RowSem (denH tb) (char 𝔽) (rowOf eF j₀)` at its one-hot state, under the same
  exclusions (the three walk-chain ones still HYPOTHESES, to be priced by item 9 summands).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ServedPVS

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.WalkGenVS

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Module
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH Nock.NockVMROM.Thm54.VclL.Handle.ServeH
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVS
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVS Nock.NockVMROM.Thm54.VclL.Handle.ServedVS
open Nock.NockVMROM.Thm54.VclL.Handle.ServedPVS
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS Nock.NockVMROM.Thm54.VclL.Handle.CensusVS
open Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS
open scoped Polynomial

noncomputable section

/-- `denH` is a `DenOK` denotation (atoms denote themselves; serials decode to cells). -/
theorem denOK_denH {q : ℕ} (t : List (CellRowB0 q)) : DenOK (denH t) := by
  refine ⟨fun v => rfl, fun i X hX => ?_⟩
  simp only [denH, preZNounOfTable, fuelChip] at hX
  rw [show 2 ^ 110 = (2 ^ 110 - 1) + 1 by norm_num, decodeB0] at hX
  cases hc : t[i]? with
  | none => rw [hc] at hX; simp at hX
  | some c =>
    rw [hc] at hX
    simp only [Option.bind_some] at hX
    cases h1 : (if c.wL then decodeB0 t (2 ^ 110 - 1) c.idL else some (.atom c.aL.val)) with
    | none => rw [h1] at hX; simp at hX
    | some a =>
      rw [h1] at hX
      simp only [Option.bind_some] at hX
      cases h2 : (if c.wR then decodeB0 t (2 ^ 110 - 1) c.idR else some (.atom c.aR.val)) with
      | none => rw [h2] at hX; simp at hX
      | some b' =>
        rw [h2] at hX
        simp only [Option.bind_some, Option.some.injEq] at hX
        exact ⟨a, b', hX.symm⟩

section VS
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)
  {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}

attribute [local instance] ClaimDenVS.quadCharF

/-- The walk twin's trace at VS, at the chip's width. -/
abbrev qWVS (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K) :
    Fin (walkChipH δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
      (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)).rap.w → F[X] :=
  fun j => msg.Qm χ (tWS hT hP) (Fin.cast (TeleC.walkW δF hT hP kr V.basis _ _ _ _ _) j)

/-- The walk data of the restricted walk twin at VS. -/
abbrev wDataVS (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K) :=
  walkDataOf δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
    (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    (restrictWalk δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
      (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) (qWVS δF hT hP kr hC V msg χ))

set_option maxHeartbeats 1600000 in
/-- **`GenuineWalk` at VS.** -/
theorem genuineWalk_VS [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K] (V : VerifierData F K hC (shapeVS hT hP))
    (hV : V.Checks (fun a => reqBoundVS hT hP hC V a + internalBoundVS hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : AcceptsG V msg χ)
    (hX : ¬ (ioSummandHX hT hP hC V).mem (msg.traces χ) χ)
    (hPm : ¬ (ioSummandHP hT hP hC V).mem (msg.traces χ) χ)
    (hval : ¬ (valSummand δF hT hP hC V msg.msg0C).mem (msg.traces χ) χ)
    (h0 : ¬ (zeroVS δF hT hP hC).mem (msg.traces χ) χ)
    (hc : ¬ (censusVS δF hT hP hC V).mem (msg.traces χ) χ)
    (hdy : zVS δF χ ∉ cellDyckRootSeeds (Kfp := Quad (algebraMap F K δF)) fuelChip
      ((tVS δF hT hP kr hC V msg χ).map (·.b0)))
    (hKX : KeysExported (tVS δF hT hP kr hC V msg χ) (wDataVS δF hT hP kr hC V msg χ).X)
    (hout : (χ ⟨0, by decide⟩, χ ⟨1, by decide⟩) ∉ walkEvent (algebraMap F K δF) (wDataVS δF hT hP kr hC V msg χ)) :
    GenuineWalk (denVS δF hT hP kr hC V msg χ) (wEnvVS δF hT hP kr hC V msg χ) := by
  obtain ⟨hgW, hw, hsatW⟩ := walk_facts δF hT hP kr hC V msg χ h
  obtain ⟨hgM, hwT, hsatT⟩ := cell_facts δF hT hP kr hC V msg χ h
  obtain ⟨hz, -, hT2⟩ := census_good δF hT hP kr hC V msg χ h0 hc
  have hq : 2 ^ 63 < ringChar F := hgM.2.2.2.1
  have htab := claim_table_VS δF hT hP kr hC V hV msg χ h hval hz
  have hsrvX := (served_of_not_mem δF hT hP kr hC V hV msg χ h hX hPm).1
  have hHX : ∀ j < V.memRows (tWS hT hP), ∃ c ∈ tVS δF hT hP kr hC V msg χ,
      (natOf ((walkEnvFH δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
          (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
          (qWVS δF hT hP kr hC V msg χ) j).trace WChip.idx),
        childHOf (walkEnvFH δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
          (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
          (qWVS δF hT hP kr hC V msg χ) j) false,
        childHOf (walkEnvFH δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
          (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
          (qWVS δF hT hP kr hC V msg χ) j) true) = exportRec c.b0 := by
    intro j hj
    have hE : walkEnvFH δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
        (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
        (qWVS δF hT hP kr hC V msg χ) j =
        wEF V.basis (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP)) (chalsVS δF χ)
          (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) (qWVS δF hT hP kr hC V msg χ) ⟨j, hj⟩ := by
      simp [walkEnvFH, wEF, hj]
    rw [hE]
    exact DecodeH.walk_hHX_of_served δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
      (V.orbitM (tCS hT hP)) kr (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
      (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
      (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
      (fun j => msg.Qm χ (tCS hT hP) (Fin.cast hwT j)) (qWVS δF hT hP kr hC V msg χ) hgM.2.2.1 hsatT.1
      ⟨j, hj⟩ (hsrvX _ (List.mem_append_right _ (List.mem_map.mpr ⟨⟨j, hj⟩, List.mem_finRange _, rfl⟩)))
  have hs1 : (walkChipH δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
      (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)).rap.Satisfies
      (qWVS δF hT hP kr hC V msg χ) := hsatW.1
  have hs2 : (walkChipH δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
      (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)).BindsPreprocessing
      (qWVS δF hT hP kr hC V msg χ) := hsatW.2
  have hout' : (chalsVS δF χ 0, chalsVS δF χ 1) ∉ walkEvent (algebraMap F K δF) (wDataVS δF hT hP kr hC V msg χ) := by
    rw [chalsVS_old δF χ 0 (by norm_num), chalsVS_old δF χ 1 (by norm_num)]
    exact hout
  have hR := walkH_records_genuine (tb := tVS δF hT hP kr hC V msg χ) (vl := []) δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP))
    (V.orbitM (tWS hT hP)) (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    (qWVS δF hT hP kr hC V msg χ) hs1 hs2 (hV.memNodes_injective _) (hV.hadjM _) hgW.1.2.2.1
    hgW.2.1 hgW.2.2.1 hgW.2.2.2 hq hz (by convert htab; exact Subsingleton.elim _ _) (by convert hT2) (by convert hdy) (by convert hKX) hHX (by convert hout')
  exact genuineWalk_of_records δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP))
    (V.orbitM (tWS hT hP)) (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    (qWVS δF hT hP kr hC V msg χ) _ hR

/-- **Every compute row of an accepted VS trace satisfies `RowSem`** (item 5 per row, assembled):
outside `ioSummandHX`, `ioSummandHP`, `valSummand`, `zeroVS`, `censusVS` and the three walk-chain
exclusions. -/
theorem rowSem_VS [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
    (V : VerifierData F K hC (shapeVS hT hP))
    (hV : V.Checks (fun a => reqBoundVS hT hP hC V a + internalBoundVS hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : AcceptsG V msg χ)
    (hX : ¬ (ioSummandHX hT hP hC V).mem (msg.traces χ) χ)
    (hPm : ¬ (ioSummandHP hT hP hC V).mem (msg.traces χ) χ)
    (hval : ¬ (valSummand δF hT hP hC V msg.msg0C).mem (msg.traces χ) χ)
    (h0 : ¬ (zeroVS δF hT hP hC).mem (msg.traces χ) χ)
    (hc : ¬ (censusVS δF hT hP hC V).mem (msg.traces χ) χ)
    (hdy : zVS δF χ ∉ cellDyckRootSeeds (Kfp := Quad (algebraMap F K δF)) fuelChip
      ((tVS δF hT hP kr hC V msg χ).map (·.b0)))
    (hKX : KeysExported (tVS δF hT hP kr hC V msg χ) (wDataVS δF hT hP kr hC V msg χ).X)
    (hout : (χ ⟨0, by decide⟩, χ ⟨1, by decide⟩) ∉ walkEvent (algebraMap F K δF) (wDataVS δF hT hP kr hC V msg χ))
    (i : Fin V.N) :
    ∃ j0, RowSel (cEnvVS δF hT hP kr hC V msg χ i) j0 ∧
      RowSem (denVS δF hT hP kr hC V msg χ) (ringChar F) (rowOf (cEnvVS δF hT hP kr hC V msg χ i) j0) := by
  obtain ⟨hg, hsat⟩ := compute_facts δF hT hP kr hC V msg χ h
  obtain ⟨hgM, -, -⟩ := cell_facts δF hT hP kr hC V msg χ h
  have hcF : 11 < ringChar F := lt_trans (by norm_num) hg.2.2.1
  have hbase := base_of_sat V.hN V.computeNodes V.basis _ _ V.orbitC _ hsat (V.computeNodes i)
    (mem_rowNodeSet _ i)
  obtain ⟨j0, hs⟩ := rowSel_of_base hbase hcF
  have hG := genuineWalk_VS δF hT hP kr hC V hV msg χ h hX hPm hval h0 hc hdy hKX hout
  exact ⟨j0, hs, rowSem_of_chip _ (denOK_denH _) hgM.2.2.1 hcF hbase hs
    (xok_VS δF hT hP kr hC V hV msg χ h hX hPm hval (census_good δF hT hP kr hC V msg χ h0 hc).1 i)
    (pok_VS δF hT hP kr hC V hV msg χ h hX hPm hG i)⟩

end VS

end

end Nock.NockVMROM.Thm54.VclL.Handle.WalkGenVS
