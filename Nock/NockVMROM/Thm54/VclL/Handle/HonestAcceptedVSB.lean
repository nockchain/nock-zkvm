/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestAcceptedVSB.lean

  Additive.

  * `HonestBadFreeVSB`: the bad-event list at the B rows (same events; the cell twin pole is over `cellColB`).
  * `goodCVS_of_honest`: `GoodCVS` for the honest message from its constituents: the claim validity
    conjunct `ρ 0 = claimValSum` is NOW DERIVED (`vTotB_eq_claimValSum`), `ρ 1 = 0` from `xTot - yTot = 0`
    (no depth-1 fingerprint reads), the compute-table well-formedness and `Im ρ₃ = Im ρ₄ = 0`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestAcceptedVS
import Nock.NockVMROM.Thm54.VclL.Handle.HonestTwinVSB

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

section AcceptedB
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC kr : ℕ} (H : HonestVCLW (K := K) δF hT hP hC kr) (bs : List Noun)

/-- **The honest bad events NOT occurring** (the completeness half's summand list, as a Prop on the coins and
the honest messages `ρ y yH`, the cell multiplicities `mhv` and the walk handle columns). -/
structure HonestBadFreeVSB (bs : List Noun) (χ : Coins frameVS K)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF)) (yH : K)
    (mhv : Fin (H.V.memRows (tCW hT hP)) → F)
    (kLv vLv kRv vRv : Fin (H.V.memRows (tWW hT hP)) → F) : Prop where
  hz : zC (δF := δF) (toVCL χ) ≠ 0
  h0 : ∀ v ∈ H.keys0 (toVCL χ), FiniteIO.compress (m := 5) ⟨γC (toVCL χ), ρC (toVCL χ)⟩ v ≠ 0
  h1 : ∀ v ∈ H.keys1 (toVCL χ), FiniteIO.compress (m := 11) ⟨γC (toVCL χ), ρC (toVCL χ)⟩ v ≠ 0
  h2 : ∀ v ∈ H.keys2 (toVCL χ), FiniteIO.compress (m := 8) ⟨γC (toVCL χ), ρC (toVCL χ)⟩ v ≠ 0
  hpoleC : ∀ i, CellTraceH.dRow δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
      (H.V.orbitM (tCW hT hP)) (chalsVS δF χ) (pubsCH δF ρ y yH) (cellColB H bs (toVCL χ)) mhv i ≠ 0
  hpoleX : ∀ i, WalkTraceH.dRow δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
      (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH) WalkHC.xKeyH (walkColVS H χ)
      kLv vLv kRv vRv i ≠ 0
  hpoleL : ∀ i, WalkTraceH.dRow δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
      (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH) WalkHC.recLH (walkColVS H χ)
      kLv vLv kRv vRv i ≠ 0
  hpoleR : ∀ i, WalkTraceH.dRow δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
      (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH) WalkHC.recRH (walkColVS H χ)
      kLv vLv kRv vRv i ≠ 0

/-- **`GoodCVS` of the honest message**, with the claim-validity conjunct derived from the binds-generic
datum (`bs` = the claim's nouns, honest claim message). -/
theorem goodCVS_of_honest (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome)
    (hreads : H.d.reads = [])
    (hadj : (vsOf H.V).AdjacentC) (hinj : Function.Injective (vsOf H.V).computeNodes)
    (hbs : ∀ b ∈ (claimBinds H.V.claim).flatMap selfCell, b ∈ H.d.cells)
    (m : ClaimMsgVS) (hm : HonestClaimMsgFull H.d.cells H.V.claim m)
    (χ : Coins frameVS K) (ρ : Fin 5 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF))
    (hρ0 : rho3 δF ρ 0 = vTotB H (claimBinds H.V.claim) (toVCL χ))
    (hρ1 : rho3 δF ρ 1 + y = H.xTot (toVCL χ)) (hyT : y = H.yTot (toVCL χ))
    (him3 : Quad.im _ (ρ 3) = 0) (him4 : Quad.im _ (ρ 4) = 0) :
    GoodCVS δF (vsOf H.V) m ρ χ := by
  refine ⟨hadj, hinj, H.hq, ?_, ?_, him3, him4⟩
  · exact hρ0.trans (vTotB_eq_claimValSum H hbs m hm χ)
  · have h := H.xTot_sub_yTot_eq (toVCL χ) hslot
    rw [hreads] at h
    have : rho3 δF ρ 1 = H.xTot (toVCL χ) - H.yTot (toVCL χ) := by
      rw [← hyT]; exact eq_sub_of_add_eq hρ1
    exact this.trans (h.trans (by simp [shallowSided, shallowReads]))

theorem honest_accepted_VS'
    {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
    {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF)) (yH : K)
    (mhv : Fin (H.V.memRows (tCW hT hP)) → F)
    (kLv vLv kRv vRv : Fin (H.V.memRows (tWW hT hP)) → F)
    (hρ : msg.requests χ = ρ) (hy : msg.msg2M χ = (y, yH))
    (hQC : ∀ j : Fin 232, msg.Qm χ (tCS hT hP) j = CellTraceH.cellTraceH δF H.V.basis
      (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP)) (chalsVS δF χ)
      (pubsCH δF ρ y yH) (cellColB H (claimBinds H.V.claim) (toVCL χ)) mhv j)
    (hQW : ∀ j : Fin 151, msg.Qm χ (tWS hT hP) j = WalkTraceH.walkTraceH δF kr H.V.basis
      (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP)) (chalsVS δF χ)
      (pubsWH δF ρ y yH) (walkColVS H χ) kLv vLv kRv vRv j)
    (hbf : HonestBadFreeVSB H (claimBinds H.V.claim) χ ρ y yH mhv kLv vLv kRv vRv)
    (hρ0 : rho3 δF ρ 0 = vTotB H (claimBinds H.V.claim) (toVCL χ)) (hρ1 : rho3 δF ρ 1 + y = H.xTot (toVCL χ))
    (hyT : y = H.yTot (toVCL χ)) (hρ2 : rho3 δF ρ 2 = H.pTot (toVCL χ))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1)
    (hpubC : pubsCH δF ρ y yH CellH.pubH = ∑ j ∈ Finset.range (H.V.memRows (tCW hT hP)),
      algebraMap F K (CellTraceH.mN mhv j) * (CellTraceH.dN δF H.V.basis (H.V.hM (tCW hT hP))
        (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP)) (chalsVS δF χ) (pubsCH δF ρ y yH)
        (cellColB H (claimBinds H.V.claim) (toVCL χ)) mhv j)⁻¹)
    (hpubX : pubsWH δF ρ y yH WalkHC.pubX = ∑ j ∈ Finset.range (H.V.memRows (tWW hT hP)),
      (WalkTraceH.dN δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
        (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH) (walkColVS H χ)
        kLv vLv kRv vRv WalkHC.xKeyH j)⁻¹)
    (hpubP : pubsWH δF ρ y yH WalkHC.pubP = ∑ j ∈ Finset.range (H.V.memRows (tWW hT hP)),
      (algebraMap F K (WalkTraceH.cN j (walkColVS H χ WChip.mL)) *
          (WalkTraceH.dN δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
            (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH) (walkColVS H χ)
            kLv vLv kRv vRv WalkHC.recLH j)⁻¹ +
        algebraMap F K (WalkTraceH.cN j (walkColVS H χ WChip.mR)) *
          (WalkTraceH.dN δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
            (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH) (walkColVS H χ)
            kLv vLv kRv vRv WalkHC.recRH j)⁻¹))
    (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome) (hreads : H.d.reads = [])
    (hadj : (vsOf H.V).AdjacentC) (hinj : Function.Injective (vsOf H.V).computeNodes)
    (hbs : ∀ b ∈ (claimBinds H.V.claim).flatMap selfCell, b ∈ H.d.cells)
    (hm : HonestClaimMsgFull H.d.cells H.V.claim msg.msg0C)
    (him3 : Quad.im _ (ρ 3) = 0) (him4 : Quad.im _ (ρ 4) = 0)
    (hcomp : RAP.SatisfiesWithPreprocessing
        (ChipH.computeChipVCLH (vsOf H.V).hN (vsOf H.V).computeNodes (vsOf H.V).basis (chalVH (vsOf H.V).basis χ)
          (pubVH δF (vsOf H.V).basis (vsOf H.V).claim msg.msg0C (msg.requests χ) χ) (vsOf H.V).orbitC)
        (fun j => msg.Qc χ (Fin.cast rfl j))) :
    AcceptsG (vsOf H.V) msg χ := by
  have hy1 : y = (msg.msg2M χ).1 := by rw [hy]
  have hy2 : yH = (msg.msg2M χ).2 := by rw [hy]
  have hGC : GoodCVS δF (vsOf H.V) msg.msg0C ρ χ :=
    goodCVS_of_honest H hslot hreads hadj hinj hbs msg.msg0C hm χ ρ y hρ0 hρ1 hyT him3 him4
  subst hρ hy1 hy2
  have hcell := cellTwin_accepted_VSB H (claimBinds H.V.claim) χ _ _ _ mhv hbf.hz hbf.h0 hbf.h1 hρ0 hρ1 hbf.hpoleC hpubC
  have hwalk := walkTwin_accepted_VS H χ _ _ _ kLv vLv kRv vRv hbf.h1 hbf.h2 hyT hρ2 hkL hkR
    hbf.hpoleX hbf.hpoleL hbf.hpoleR hpubX hpubP
  refine acceptsG_of_chips δF hT hP kr hC (vsOf H.V) msg χ hGC hcomp (goodM_vsOf_C H) (goodW_vsOf H)
    (fun hw => ?_) (fun hw => ?_)
  · have hfun : (fun j => msg.Qm χ (tCS hT hP) (Fin.cast hw j)) = fun j => CellTraceH.cellTraceH δF H.V.basis
        (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP)) (chalsVS δF χ)
        (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) (cellColB H (claimBinds H.V.claim) (toVCL χ)) mhv
        (Fin.cast (cellChipH_width δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
          (H.V.orbitM (tCW hT hP)) (chalsVS δF χ)
          (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)) j) :=
      funext fun j => hQC _
    rw [hfun]; exact hcell
  · have hfun : (fun j => msg.Qm χ (tWS hT hP) (Fin.cast hw j)) = fun j => WalkTraceH.walkTraceH δF kr H.V.basis
        (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP)) (chalsVS δF χ)
        (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) (walkColVS H χ) kLv vLv kRv vRv
        (Fin.cast (walkChipH_width δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
          (H.V.orbitM (tWW hT hP)) (chalsVS δF χ)
          (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)) j) :=
      funext fun j => hQW _
    rw [hfun]; exact hwalk

end AcceptedB

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
