/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestTwinVS.lean

  Additive.

  * `vsOf`: the VS verifier data of an honest `HonestVCLW` verifier data (same nodes, orbits, row counts;
    only the table widths differ), with `rfl` bridges at both tables.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TraceAcceptH
import Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
import Nock.NockVMROM.Thm54.VclL.Handle.HonestOrigAcceptH

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
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module
open scoped Polynomial

noncomputable section

section VsOf
variable {F K : Type} [Field F] [Field K] [Algebra F K] {hT hP hC : ℕ}

theorem height_eq_VS (t : Fin 2) :
    ((shapeVS hT hP).table t).height = ((shapeVW hT hP).table t).height := by
  simp only [shapeVS, shapeVW, shapeVCL]; split_ifs <;> rfl

/-- **The VS verifier data of an honest `shapeVW` verifier data**: the same claim, rows, nodes and orbits
(the table heights agree: `height_eq_VS`); only the table widths differ. -/
def vsOf (V : VerifierData F K hC (shapeVW hT hP)) : VerifierData F K hC (shapeVS hT hP) :=
  ⟨V.claim, V.N, V.hN, V.Ksz, V.basis, V.orbitC, V.computeNodes, V.memRows, V.hM,
    fun t => (height_eq_VS (hT := hT) (hP := hP) t).symm ▸ V.orbitM t, V.memNodes⟩

theorem vsOf_hM_C (V : VerifierData F K hC (shapeVW hT hP)) : (vsOf V).hM (tCS hT hP) = V.hM (tCW hT hP) := rfl
theorem vsOf_hM_W (V : VerifierData F K hC (shapeVW hT hP)) : (vsOf V).hM (tWS hT hP) = V.hM (tWW hT hP) := rfl
theorem vsOf_nodes_C (V : VerifierData F K hC (shapeVW hT hP)) :
    (vsOf V).memNodes (tCS hT hP) = V.memNodes (tCW hT hP) := rfl
theorem vsOf_nodes_W (V : VerifierData F K hC (shapeVW hT hP)) :
    (vsOf V).memNodes (tWS hT hP) = V.memNodes (tWW hT hP) := rfl
theorem vsOf_orbit_C (V : VerifierData F K hC (shapeVW hT hP)) :
    (vsOf V).orbitM (tCS hT hP) = V.orbitM (tCW hT hP) := rfl
theorem vsOf_orbit_W (V : VerifierData F K hC (shapeVW hT hP)) :
    (vsOf V).orbitM (tWS hT hP) = V.orbitM (tWW hT hP) := rfl

end VsOf

section Twins
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] {hT hP hC kr : ℕ}
  (H : HonestVCLW (K := K) δF hT hP hC kr)

/-- **The cell twin accepts the honest 232-column trace at the `frameVS` coins.** -/
theorem cellTwin_accepted_VS (χ : Coins frameVS K)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF)) (yH : K)
    (mhv : Fin (H.V.memRows (tCW hT hP)) → F)
    (hz : zC (δF := δF) (toVCL χ) ≠ 0)
    (h0 : ∀ v ∈ H.keys0 (toVCL χ), FiniteIO.compress (m := 5) ⟨γC (toVCL χ), ρC (toVCL χ)⟩ v ≠ 0)
    (h1 : ∀ v ∈ H.keys1 (toVCL χ), FiniteIO.compress (m := 11) ⟨γC (toVCL χ), ρC (toVCL χ)⟩ v ≠ 0)
    (hρ0 : rho3 δF ρ 0 = H.vTot (toVCL χ)) (hρ1 : rho3 δF ρ 1 + y = H.xTot (toVCL χ))
    (hpole : ∀ i, CellTraceH.dRow δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
      (H.V.orbitM (tCW hT hP)) (chalsVS δF χ) (pubsCH δF ρ y yH)
      (cellCol δF H.V.basis (fun i' : Fin (H.V.memRows (tCW hT hP)) =>
        cellFill δF (γC (toVCL χ)) (ρC (toVCL χ)) (H.cellRows (zC (toVCL χ))) i')) mhv i ≠ 0)
    (hpub : pubsCH δF ρ y yH CellH.pubH = ∑ j ∈ Finset.range (H.V.memRows (tCW hT hP)),
      algebraMap F K (CellTraceH.mN mhv j) * (CellTraceH.dN δF H.V.basis (H.V.hM (tCW hT hP))
        (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP)) (chalsVS δF χ) (pubsCH δF ρ y yH)
        (cellCol δF H.V.basis (fun i' : Fin (H.V.memRows (tCW hT hP)) =>
          cellFill δF (γC (toVCL χ)) (ρC (toVCL χ)) (H.cellRows (zC (toVCL χ))) i')) mhv j)⁻¹) :
    RAP.SatisfiesWithPreprocessing
      (cellChipH δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP))
        (chalsVS δF χ) (pubsCH δF ρ y yH))
      (fun j => CellTraceH.cellTraceH δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
        (H.V.orbitM (tCW hT hP)) (chalsVS δF χ) (pubsCH δF ρ y yH)
        (cellCol δF H.V.basis (fun i' : Fin (H.V.memRows (tCW hT hP)) =>
          cellFill δF (γC (toVCL χ)) (ρC (toVCL χ)) (H.cellRows (zC (toVCL χ))) i')) mhv
        (Fin.cast (cellChipH_width δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
          (H.V.orbitM (tCW hT hP)) (chalsVS δF χ) (pubsCH δF ρ y yH)) j)) := by
  refine cellTwin_accepted δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
    (H.V.orbitM (tCW hT hP)) (chalsVS δF χ) (pubsCH δF ρ y yH) _ mhv (H.hinj _) (H.hadj _) ?_ hpole hpub
  refine cell_acceptedW_gen H (toVCL χ) (chalsVS δF χ) (pubsCH δF ρ y yH)
    (fun j hj => chalsVS_old δF χ j hj) (rho3 δF ρ) y (fun i hi => ?_) hz h0 h1 hρ0 hρ1
  have h4 : i ≠ CellH.pubH := by simp only [CellH.pubH]; omega
  simp [pubsCH, h4]

/-- **The walk twin accepts the honest 151-column trace at the `frameVS` coins.**  The handle columns
`kL vL kR vR` are parameters (the honest values are the child rows' (s, f, e) handles, `childrenMatchSf`). -/
theorem walkTwin_accepted_VS (χ : Coins frameVS K)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF)) (yH : K)
    (kLv vLv kRv vRv : Fin (H.V.memRows (tWW hT hP)) → F)
    (h1 : ∀ v ∈ H.keys1 (toVCL χ), FiniteIO.compress (m := 11) ⟨γC (toVCL χ), ρC (toVCL χ)⟩ v ≠ 0)
    (h2 : ∀ v ∈ H.keys2 (toVCL χ), FiniteIO.compress (m := 8) ⟨γC (toVCL χ), ρC (toVCL χ)⟩ v ≠ 0)
    (hy : y = H.yTot (toVCL χ)) (hρ2 : rho3 δF ρ 2 = H.pTot (toVCL χ))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1)
    (hpX : ∀ i, WalkTraceH.dRow δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
      (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH) WalkHC.xKeyH
      (walkCol δF H.V.basis kr (fun i' : Fin (H.V.memRows (tWW hT hP)) => H.wVals (toVCL χ) i'))
      kLv vLv kRv vRv i ≠ 0)
    (hpL : ∀ i, WalkTraceH.dRow δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
      (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH) WalkHC.recLH
      (walkCol δF H.V.basis kr (fun i' : Fin (H.V.memRows (tWW hT hP)) => H.wVals (toVCL χ) i'))
      kLv vLv kRv vRv i ≠ 0)
    (hpR : ∀ i, WalkTraceH.dRow δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
      (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH) WalkHC.recRH
      (walkCol δF H.V.basis kr (fun i' : Fin (H.V.memRows (tWW hT hP)) => H.wVals (toVCL χ) i'))
      kLv vLv kRv vRv i ≠ 0)
    (hpubX : pubsWH δF ρ y yH WalkHC.pubX = ∑ j ∈ Finset.range (H.V.memRows (tWW hT hP)),
      (WalkTraceH.dN δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
        (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH)
        (walkCol δF H.V.basis kr (fun i' : Fin (H.V.memRows (tWW hT hP)) => H.wVals (toVCL χ) i'))
        kLv vLv kRv vRv WalkHC.xKeyH j)⁻¹)
    (hpubP : pubsWH δF ρ y yH WalkHC.pubP = ∑ j ∈ Finset.range (H.V.memRows (tWW hT hP)),
      (algebraMap F K (WalkTraceH.cN j ((walkCol δF H.V.basis kr
          (fun i' : Fin (H.V.memRows (tWW hT hP)) => H.wVals (toVCL χ) i')) WChip.mL)) *
          (WalkTraceH.dN δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
            (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH)
            (walkCol δF H.V.basis kr (fun i' : Fin (H.V.memRows (tWW hT hP)) => H.wVals (toVCL χ) i'))
            kLv vLv kRv vRv WalkHC.recLH j)⁻¹ +
        algebraMap F K (WalkTraceH.cN j ((walkCol δF H.V.basis kr
          (fun i' : Fin (H.V.memRows (tWW hT hP)) => H.wVals (toVCL χ) i')) WChip.mR)) *
          (WalkTraceH.dN δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
            (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH)
            (walkCol δF H.V.basis kr (fun i' : Fin (H.V.memRows (tWW hT hP)) => H.wVals (toVCL χ) i'))
            kLv vLv kRv vRv WalkHC.recRH j)⁻¹)) :
    RAP.SatisfiesWithPreprocessing
      (walkChipH δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP))
        (chalsVS δF χ) (pubsWH δF ρ y yH))
      (fun j => WalkTraceH.walkTraceH δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
        (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH)
        (walkCol δF H.V.basis kr (fun i' : Fin (H.V.memRows (tWW hT hP)) => H.wVals (toVCL χ) i'))
        kLv vLv kRv vRv
        (Fin.cast (walkChipH_width δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
          (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH)) j)) := by
  refine walkTwin_accepted δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
    (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH) _ kLv vLv kRv vRv (H.hinj _) (H.hadj _) ?_
    hkL hkR hpX hpL hpR hpubX hpubP
  refine walk_acceptedW_gen H (toVCL χ) (chalsVS δF χ) (pubsWH δF ρ y yH)
    (fun j hj => chalsVS_old δF χ j hj) (rho3 δF ρ) y (fun i hi => ?_) h1 h2 hy hρ2
  have h4 : i ≠ WalkHC.pubX := by simp only [WalkHC.pubX]; omega
  have h5 : i ≠ WalkHC.pubP := by simp only [WalkHC.pubP]; omega
  simp [pubsWH, h4, h5]

end Twins

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
