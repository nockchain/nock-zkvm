/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestOrigAcceptH.lean

  Additive.

  The twin chips (`cellChipH` / `walkChipH`) are built over `chalsVS` (leaves 33 / 34 = the handle coins) and
  `pubsCH` / `pubsWH` (terminals 4 / 5 added), so the `ok`-gated original acceptance (`cell_acceptedW` /
  `walk_acceptedW`, stated at `chalsVCL` / `pubsC`) must be re-stated at those vectors before
  `cellTwin_accepted` / `walkTwin_accepted` can consume it.  The proofs are those of `cell_acceptedW` /
  `walk_acceptedW` with `chalsVCL δF χ` / `pubsC δF ρ y` replaced by `chals'` / `pubs'` (the generic
  `cellOk_sat` / `walkOk_sat` already take them as parameters); the agreement hypotheses discharge the
  leaf facts they read (`ChalsOK`, leaves 0 / 1 / 2 / 3, publics 0..3).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestVCLW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Module
open scoped Polynomial

noncomputable section

section Accepted
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] {hT hP hC kr : ℕ} {C : TableSpec}
  (H : HonestVCLW (K := K) δF hT hP hC kr)

/-- `ChalsOK` transfers along agreement below `33` with `chalsVCL`. -/
theorem chalsOK_of_agree (χ : Coins frameVCL K) (chals' : ℕ → K)
    (hch : ∀ j < 33, chals' j = chalsVCL δF χ j) :
    ChalsOK δF chals' (Quad.mk _ (χ ⟨4, by decide⟩) (χ ⟨6, by decide⟩))
      (Quad.mk _ (χ ⟨5, by decide⟩) (χ ⟨7, by decide⟩)) 11 := by
  have h := chalsVCL_ok δF χ 11
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hch 5 (by omega), hch 7 (by omega)]; exact h.1
  · rw [hch _ (by omega), hch _ (by omega)]; exact h.2 i hi

theorem cell_acceptedW_gen (χ : Coins frameVCL K)
    (chals' pubs' : ℕ → K) (hch : ∀ j < 33, chals' j = chalsVCL δF χ j)
    (ρ : Fin 3 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF))
    (hp : ∀ i < 4, pubs' i = pubsC δF ρ y i)
    (hz : zC (δF := δF) χ ≠ 0)
    (h0 : ∀ v ∈ H.keys0 χ, FiniteIO.compress (m := 5) ⟨γC χ, ρC χ⟩ v ≠ 0)
    (h1 : ∀ v ∈ H.keys1 χ, FiniteIO.compress (m := 11) ⟨γC χ, ρC χ⟩ v ≠ 0)
    (hρ0 : ρ 0 = H.vTot χ) (hρ1 : ρ 1 + y = H.xTot χ) :
    RAP.SatisfiesWithPreprocessing
      (cellChipOk δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP))
        chals' pubs' true)
      (fun j => honestQ (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
        (cellCol δF H.V.basis (fun i' : Fin (H.V.memRows (tCW hT hP)) =>
          cellFill δF (γC χ) (ρC χ) (H.cellRows (zC χ)) i')) 225
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
  · exact cellBaseFacts_fill δF _ _ (H.cellRows (zC χ)) i
      (cellRows0_baseFacts (δF := δF) (zC χ) H.d.cells (vcsOf H.d.cells []) (xs0W H.d) (xs1W H.d)
        hcell hnd H.hrank hN i)
  · have hlt : ∀ j < H.V.memRows (tCW hT hP), j < H.d.cells.length := fun j hj => hN ▸ hj
    refine cellFill_facts (γC χ) (ρC χ) (H.cellRows (zC χ)) (zC χ) pubs' i hz
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

theorem walk_acceptedW_gen (χ : Coins frameVCL K)
    (chals' pubs' : ℕ → K) (hch : ∀ j < 33, chals' j = chalsVCL δF χ j)
    (ρ : Fin 3 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF))
    (hp : ∀ i < 4, pubs' i = pubsP δF ρ y i)
    (h1 : ∀ v ∈ H.keys1 χ, FiniteIO.compress (m := 11) ⟨γC χ, ρC χ⟩ v ≠ 0)
    (h2 : ∀ v ∈ H.keys2 χ, FiniteIO.compress (m := 8) ⟨γC χ, ρC χ⟩ v ≠ 0)
    (hy : y = H.yTot χ) (hρ2 : ρ 2 = H.pTot χ) :
    RAP.SatisfiesWithPreprocessing
      (walkChipOk δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP))
        chals' pubs' true)
      (fun j => honestQ (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
        (walkCol δF H.V.basis kr (fun i' : Fin (H.V.memRows (tWW hT hP)) => H.wVals χ i')) 132
        (Fin.cast (walkChipOk_w δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
          (H.V.orbitM (tWW hT hP)) chals' pubs' true) j)) := by
  have hN := H.hW0
  have hkp : krW H.d.cells H.d.preads + (walkRows H.d.cells H.d.preads).length < ringChar F := by
    rw [H.hkr, ← hN]; exact H.hkp
  have hcells : H.d.cells.length < ringChar F := by
    have := H.hrows (tCW hT hP); rw [H.hC0] at this; omega
  refine walkOk_sat δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP))
    chals' pubs' _ H.hF (H.hinj _) (H.hadj _) (γC χ) (ρC χ)
    (chalsOK_of_agree χ chals' hch) (fun i => ?_) (fun i => ?_) (fun i => ?_)
  · have hb := walkRow0_base δF (zC χ) H.d.cells H.d.preads (chalsVCL δF χ 0) (chalsVCL δF χ 1) H.h62 hkp hN i
    rw [H.hkr] at hb
    exact walkBaseFacts_fill δF (γC χ) (ρC χ) (H.wRows χ) kr i hb
  · have hk := walkRow0_K δF (zC χ) H.d.cells H.d.preads (chalsVCL δF χ 0) (chalsVCL δF χ 1) H.hF H.hq hcells
      H.h62 hN i
    rw [H.hkr] at hk
    rw [hch 0 (by omega), hch 1 (by omega)]
    exact walkKFacts_fill δF (γC χ) (ρC χ) (H.wRows χ) kr _ _ i hk
  · refine walkFill_mixed δF (γC χ) (ρC χ) (H.wRows χ) kr pubs' i
      (fun j hj hk => wRows_root H χ (hN ▸ hj) (by rw [H.hkr]; exact hk))
      (fun j hj => h1 _ ?_) (fun j hj => h2 _ ?_) (fun j hj => h2 _ ?_) ?_ ?_
    · simp only [HonestVCLW.keys1, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨j, hj, rfl⟩
    · simp only [HonestVCLW.keys2, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl ⟨j, hj, rfl⟩
    · simp only [HonestVCLW.keys2, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨j, hj, rfl⟩
    · rw [hp 0 (by omega), hp 1 (by omega), pubsP_01, hy]; rfl
    · rw [hp 2 (by omega), hp 3 (by omega), pubsP_23, hρ2]; rfl

end Accepted

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
