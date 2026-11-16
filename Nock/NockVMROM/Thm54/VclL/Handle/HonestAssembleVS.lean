/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestAssembleVS.lean

  Additive.

  * `acceptsG_of_chips`: the converse of `compute_facts` / `cell_facts` / `walk_facts`: `AcceptsG` at the VS
    cores follows from the three chips' acceptance plus `GoodCVS`, `GoodM`, `GoodW`.
  * `goodM_vsOf` / `goodW_vsOf`: the memory `Good` conditions of `vsOf H.V` from `HonestVCLW`'s fields.
  * UNCONFIRMED / not proved here: the compute chip's acceptance at the honest rows (the `mixedCompile`
  lowering of its 𝕂 gates) is a HYPOTHESIS `hcomp`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestTwinVS

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
open Nock.NockVMROM.Thm54.VclL.GenWalk Nock.NockVMROM.Thm54.TraceGen
open Module
open scoped Polynomial

noncomputable section

section Cores
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)
variable {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}

open Classical in
/-- **`AcceptsG` at the VS cores from the three chips** (the converse of `compute_facts` / `cell_facts` /
`walk_facts`). -/
theorem acceptsG_of_chips (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (hGC : GoodCVS δF V msg.msg0C (msg.requests χ) χ)
    (hc : RAP.SatisfiesWithPreprocessing
        (ChipH.computeChipVCLH V.hN V.computeNodes V.basis (chalVH V.basis χ)
          (pubVH δF V.basis V.claim msg.msg0C (msg.requests χ) χ) V.orbitC)
        (fun j => msg.Qc χ (Fin.cast rfl j)))
    (hGM : GoodM V (tCS hT hP)) (hGW : GoodW V (tWS hT hP) kr)
    (hcell : ∀ hw : (cellChipH δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
        (V.orbitM (tCS hT hP)) (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1
          (msg.msg2M χ).2)).rap.w = ((shapeVS hT hP).table (tCS hT hP)).width,
      RAP.SatisfiesWithPreprocessing
        (cellChipH δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP))
          (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2))
        (fun j => msg.Qm χ (tCS hT hP) (Fin.cast hw j)))
    (hwalk : ∀ hw : (walkChipH δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP))
        (V.orbitM (tWS hT hP)) (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1
          (msg.msg2M χ).2)).rap.w = ((shapeVS hT hP).table (tWS hT hP)).width,
      RAP.SatisfiesWithPreprocessing
        (walkChipH δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
          (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2))
        (fun j => msg.Qm χ (tWS hT hP) (Fin.cast hw j))) :
    AcceptsG V msg χ := by
  refine ⟨?_, fun t => ?_⟩
  · change RAP.SatisfiesWithPreprocessing (chipCVS δF V msg.msg0C (msg.requests χ) χ)
      (fun j => msg.Qc χ (Fin.cast (chipCVS_width δF V msg.msg0C (msg.requests χ) χ) j))
    have he : chipCVS δF V msg.msg0C (msg.requests χ) χ =
        ChipH.computeChipVCLH V.hN V.computeNodes V.basis (chalVH V.basis χ)
          (pubVH δF V.basis V.claim msg.msg0C (msg.requests χ) χ) V.orbitC := by
      unfold chipCVS; exact if_pos hGC
    exact sat_cast_eq he.symm rfl _ _ hc
  · change RAP.SatisfiesWithPreprocessing (chipMVS δF hT hP kr V t (msg.requests χ) (msg.msg2M χ) χ)
      (fun j => msg.Qm χ t
        (Fin.cast (chipMVS_width δF hT hP kr V t (msg.requests χ) (msg.msg2M χ) χ) j))
    by_cases h0 : (t : ℕ) = 0
    · obtain rfl : t = tCS hT hP := Fin.ext h0
      have he : chipMVS δF hT hP kr V (tCS hT hP) (msg.requests χ) (msg.msg2M χ) χ =
          cellChipH δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP))
            (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) := by
        unfold chipMVS; rw [if_pos h0, if_pos hGM]
      have hw : (cellChipH δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
          (V.orbitM (tCS hT hP)) (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1
            (msg.msg2M χ).2)).rap.w = ((shapeVS hT hP).table (tCS hT hP)).width := by
        rw [← he]; exact chipMVS_width δF hT hP kr V _ _ _ _
      exact sat_cast_eq he.symm hw _ _ (hcell hw)
    · have ht1 : t = tWS hT hP := Fin.ext (by have h2 : (t : ℕ) < 2 := t.2; show (t : ℕ) = 1; omega)
      subst ht1
      have h1 : ¬ ((tWS hT hP : Fin (shapeVS hT hP).k) : ℕ) = 0 := Nat.one_ne_zero
      have he : chipMVS δF hT hP kr V (tWS hT hP) (msg.requests χ) (msg.msg2M χ) χ =
          walkChipH δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
            (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) := by
        unfold chipMVS; rw [if_neg h1, if_pos hGW]
      have hw : (walkChipH δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP))
          (V.orbitM (tWS hT hP)) (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1
            (msg.msg2M χ).2)).rap.w = ((shapeVS hT hP).table (tWS hT hP)).width := by
        rw [← he]; exact chipMVS_width δF hT hP kr V _ _ _ _
      exact sat_cast_eq he.symm hw _ _ (hwalk hw)

end Cores

section Good
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] {hT hP hC kr : ℕ}
  (H : HonestVCLW (K := K) δF hT hP hC kr)

theorem goodM_vsOf_C : GoodM (vsOf H.V) (tCS hT hP) :=
  ⟨H.hadj (tCW hT hP), H.hinj (tCW hT hP), H.hF, H.hq, H.hrows (tCW hT hP)⟩

theorem goodW_vsOf : GoodW (vsOf H.V) (tWS hT hP) kr :=
  ⟨⟨H.hadj (tWW hT hP), H.hinj (tWW hT hP), H.hF, H.hq, H.hrows (tWW hT hP)⟩,
    by have := one_le_krW H.d.cells H.d.preads; rw [H.hkr] at this; exact this,
    by have := krW_le_rows H.d.cells H.d.preads; rw [H.hkr, ← H.hW0] at this; exact this,
    H.hkp⟩

end Good

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
