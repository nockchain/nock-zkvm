/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestTwinVSB.lean

  **The cell twin accepts the binds-generic honest trace**
  (twin of `HonestOrigAcceptH.cell_acceptedW_gen` / `HonestTwinVS.cellTwin_accepted_VS`, with the cell rows
  `cellRowsB H bs` over the validity consumers `vcsOf cells bs`; `bs` = the claim's nouns).  Additive.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestTwinVS
import Nock.NockVMROM.Thm54.VclL.Handle.HonestBindsH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.TraceGen
open Module
open scoped Polynomial

noncomputable section

section TwinB
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] {hT hP hC kr : ℕ}
  (H : HonestVCLW (K := K) δF hT hP hC kr) (bs : List Noun)

theorem cell_acceptedW_genB (χ : Coins frameVCL K)
    (chals' pubs' : ℕ → K) (hch : ∀ j < 33, chals' j = chalsVCL δF χ j)
    (ρ : Fin 3 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF))
    (hp : ∀ i < 4, pubs' i = pubsC δF ρ y i)
    (hz : zC (δF := δF) χ ≠ 0)
    (h0 : ∀ v ∈ H.keys0 χ, FiniteIO.compress (m := 5) ⟨γC χ, ρC χ⟩ v ≠ 0)
    (h1 : ∀ v ∈ H.keys1 χ, FiniteIO.compress (m := 11) ⟨γC χ, ρC χ⟩ v ≠ 0)
    (hρ0 : ρ 0 = vTotB H bs χ) (hρ1 : ρ 1 + y = xTotB H bs χ) :
    RAP.SatisfiesWithPreprocessing
      (cellChipOk δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP))
        chals' pubs' true)
      (fun j => honestQ (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
        (cellCol δF H.V.basis (fun i' : Fin (H.V.memRows (tCW hT hP)) =>
          cellFill δF (γC χ) (ρC χ) (cellRowsB H bs (zC χ)) i')) 225
        (Fin.cast (cellChipOk_w δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
          (H.V.orbitM (tCW hT hP)) chals' pubs' true) j)) := by
  have hN : H.V.memRows (tCW hT hP) = H.d.cells.length := H.hC0
  have hnd := closureOf_nodup H.d.roots
  have hcell : ∀ n ∈ H.d.cells, n.isCell = true := fun n hn => closureOf_isCell hn
  have hz' : Quad.mk (algebraMap F K δF) (chals' 2) (chals' 3) = zC (δF := δF) χ := by
    rw [hch 2 (by omega), hch 3 (by omega)]; rfl
  refine cellOk_sat δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP))
    chals' pubs' _ (H.hinj _) (H.hadj _) (γC χ) (ρC χ) (zC χ)
    (chalsOK_of_agree χ chals' hch) hz' (fun i => ?_) (fun i => ?_)
  · exact cellBaseFacts_fill δF _ _ (cellRowsB H bs (zC χ)) i
      (cellRows0_baseFacts (δF := δF) (zC χ) H.d.cells (vcsOf H.d.cells bs) (xs0W H.d) (xs1W H.d)
        hcell hnd H.hrank hN i)
  · have hlt : ∀ j < H.V.memRows (tCW hT hP), j < H.d.cells.length := fun j hj => hN ▸ hj
    refine cellFill_facts (γC χ) (ρC χ) (cellRowsB H bs (zC χ)) (zC χ) pubs' i hz
      (fun j hj => cellRows0_cons (δF := δF) (zC χ) H.d.cells _ _ _ hcell hz (hlt j hj))
      (fun j hj => cellRows0_atomL (δF := δF) (zC χ) H.d.cells _ _ _ hcell (hlt j hj))
      (fun j hj => cellRows0_atomR (δF := δF) (zC χ) H.d.cells _ _ _ hcell (hlt j hj))
      (fun j hj => h0 _ ?_) (fun j hj _ => h0 _ ?_) (fun j hj _ => h0 _ ?_)
      (fun j hj => h1 _ ?_) (fun j hj => h1 _ ?_) ?_ ?_
    · simp only [HonestVCLW.keys0, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl ⟨j, hj, rfl⟩)
    · simp only [HonestVCLW.keys0, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
    · simp only [HonestVCLW.keys0, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨j, hj, rfl⟩
    · simp only [HonestVCLW.keys1, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl ⟨j, hj, rfl⟩)
    · simp only [HonestVCLW.keys1, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
    · rw [hp 0 (by omega), hp 1 (by omega), pubsC_01, hρ0]; rfl
    · rw [hp 2 (by omega), hp 3 (by omega), pubsC_23, hρ1]; rfl

/-- **The cell twin accepts the honest 232-column trace at the `frameVS` coins.** -/
theorem cellTwin_accepted_VSB (χ : Coins frameVS K)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF)) (yH : K)
    (mhv : Fin (H.V.memRows (tCW hT hP)) → F)
    (hz : zC (δF := δF) (toVCL χ) ≠ 0)
    (h0 : ∀ v ∈ H.keys0 (toVCL χ), FiniteIO.compress (m := 5) ⟨γC (toVCL χ), ρC (toVCL χ)⟩ v ≠ 0)
    (h1 : ∀ v ∈ H.keys1 (toVCL χ), FiniteIO.compress (m := 11) ⟨γC (toVCL χ), ρC (toVCL χ)⟩ v ≠ 0)
    (hρ0 : rho3 δF ρ 0 = vTotB H bs (toVCL χ)) (hρ1 : rho3 δF ρ 1 + y = xTotB H bs (toVCL χ))
    (hpole : ∀ i, CellTraceH.dRow δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
      (H.V.orbitM (tCW hT hP)) (chalsVS δF χ) (pubsCH δF ρ y yH)
      (cellCol δF H.V.basis (fun i' : Fin (H.V.memRows (tCW hT hP)) =>
        cellFill δF (γC (toVCL χ)) (ρC (toVCL χ)) (cellRowsB H bs (zC (toVCL χ))) i')) mhv i ≠ 0)
    (hpub : pubsCH δF ρ y yH CellH.pubH = ∑ j ∈ Finset.range (H.V.memRows (tCW hT hP)),
      algebraMap F K (CellTraceH.mN mhv j) * (CellTraceH.dN δF H.V.basis (H.V.hM (tCW hT hP))
        (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP)) (chalsVS δF χ) (pubsCH δF ρ y yH)
        (cellCol δF H.V.basis (fun i' : Fin (H.V.memRows (tCW hT hP)) =>
          cellFill δF (γC (toVCL χ)) (ρC (toVCL χ)) (cellRowsB H bs (zC (toVCL χ))) i')) mhv j)⁻¹) :
    RAP.SatisfiesWithPreprocessing
      (cellChipH δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP))
        (chalsVS δF χ) (pubsCH δF ρ y yH))
      (fun j => CellTraceH.cellTraceH δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
        (H.V.orbitM (tCW hT hP)) (chalsVS δF χ) (pubsCH δF ρ y yH)
        (cellCol δF H.V.basis (fun i' : Fin (H.V.memRows (tCW hT hP)) =>
          cellFill δF (γC (toVCL χ)) (ρC (toVCL χ)) (cellRowsB H bs (zC (toVCL χ))) i')) mhv
        (Fin.cast (cellChipH_width δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
          (H.V.orbitM (tCW hT hP)) (chalsVS δF χ) (pubsCH δF ρ y yH)) j)) := by
  refine cellTwin_accepted δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
    (H.V.orbitM (tCW hT hP)) (chalsVS δF χ) (pubsCH δF ρ y yH) _ mhv (H.hinj _) (H.hadj _) ?_ hpole hpub
  refine cell_acceptedW_genB H bs (toVCL χ) (chalsVS δF χ) (pubsCH δF ρ y yH)
    (fun j hj => chalsVS_old δF χ j hj) (rho3 δF ρ) y (fun i hi => ?_) hz h0 h1 hρ0 hρ1
  have h4 : i ≠ CellH.pubH := by simp only [CellH.pubH]; omega
  simp [pubsCH, h4]


end TwinB

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
