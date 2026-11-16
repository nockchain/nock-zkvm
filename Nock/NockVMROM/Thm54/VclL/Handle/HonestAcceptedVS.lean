/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestAcceptedVS.lean

  Additive.

  `HonestBadFreeVS` is the completeness half's summand list as a Prop: the coin events the honest traces
  must avoid (each is a priced event of the cited kind, none an assumption about the prover):
  * `hpoleC`: the cell twin's denominators nonzero (handle coins 11 / 12; at most one coin per row-record,
    `den_bad_card`);
  * `hpoleX/L/R`: the walk twin's three denominators nonzero (same pricing, 3 per walk row);
  * the twin terminals `hpubC`, `hpubX`, `hpubP` (the honest `y`, `yH` and `ρ₃ ρ₄` are the honest totals: an
    equation about the honest message, not a coin event);
  * the compute-side events (`NotBadRow`, `poleRow_card`: at most `|polesOf|` coins per compute row; the
    `SlotBad` event of `PoleFree`; the walk coin order event, `walk_coin_order_few`) enter through `hcomp`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestAssembleVS

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

section Accepted
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC kr : ℕ} (H : HonestVCLW (K := K) δF hT hP hC kr)

def cellColVS (χ : Coins frameVS K) : ℕ → Fin (H.V.memRows (tCW hT hP)) → F :=
  cellCol δF H.V.basis (fun i' : Fin (H.V.memRows (tCW hT hP)) =>
    cellFill δF (γC (toVCL χ)) (ρC (toVCL χ)) (H.cellRows (zC (toVCL χ))) i')

def walkColVS (χ : Coins frameVS K) : ℕ → Fin (H.V.memRows (tWW hT hP)) → F :=
  walkCol δF H.V.basis kr (fun i' : Fin (H.V.memRows (tWW hT hP)) => H.wVals (toVCL χ) i')

/-- **The honest bad events NOT occurring** (the completeness half's summand list, as a Prop on the coins and
the honest messages `ρ y yH`, the cell multiplicities `mhv` and the walk handle columns). -/
structure HonestBadFreeVS (χ : Coins frameVS K)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF)) (yH : K)
    (mhv : Fin (H.V.memRows (tCW hT hP)) → F)
    (kLv vLv kRv vRv : Fin (H.V.memRows (tWW hT hP)) → F) : Prop where
  hz : zC (δF := δF) (toVCL χ) ≠ 0
  h0 : ∀ v ∈ H.keys0 (toVCL χ), FiniteIO.compress (m := 5) ⟨γC (toVCL χ), ρC (toVCL χ)⟩ v ≠ 0
  h1 : ∀ v ∈ H.keys1 (toVCL χ), FiniteIO.compress (m := 11) ⟨γC (toVCL χ), ρC (toVCL χ)⟩ v ≠ 0
  h2 : ∀ v ∈ H.keys2 (toVCL χ), FiniteIO.compress (m := 8) ⟨γC (toVCL χ), ρC (toVCL χ)⟩ v ≠ 0
  hpoleC : ∀ i, CellTraceH.dRow δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
      (H.V.orbitM (tCW hT hP)) (chalsVS δF χ) (pubsCH δF ρ y yH) (cellColVS H χ) mhv i ≠ 0
  hpoleX : ∀ i, WalkTraceH.dRow δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
      (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH) WalkHC.xKeyH (walkColVS H χ)
      kLv vLv kRv vRv i ≠ 0
  hpoleL : ∀ i, WalkTraceH.dRow δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
      (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH) WalkHC.recLH (walkColVS H χ)
      kLv vLv kRv vRv i ≠ 0
  hpoleR : ∀ i, WalkTraceH.dRow δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
      (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH) WalkHC.recRH (walkColVS H χ)
      kLv vLv kRv vRv i ≠ 0

/-- **The honest VS assembly.**  Compute side: `GoodCVS` (honest claim / terminal values) and the honest compute-chip
acceptance `hcomp` (UNCONFIRMED: the `mixedCompile` lowering of the 𝕂 gates). -/
theorem honest_accepted_VS
    {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
    {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF)) (yH : K)
    (mhv : Fin (H.V.memRows (tCW hT hP)) → F)
    (kLv vLv kRv vRv : Fin (H.V.memRows (tWW hT hP)) → F)
    (hρ : msg.requests χ = ρ) (hy : msg.msg2M χ = (y, yH))
    (hQC : ∀ j : Fin 232, msg.Qm χ (tCS hT hP) j = CellTraceH.cellTraceH δF H.V.basis
      (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP)) (chalsVS δF χ)
      (pubsCH δF ρ y yH) (cellColVS H χ) mhv j)
    (hQW : ∀ j : Fin 151, msg.Qm χ (tWS hT hP) j = WalkTraceH.walkTraceH δF kr H.V.basis
      (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP)) (chalsVS δF χ)
      (pubsWH δF ρ y yH) (walkColVS H χ) kLv vLv kRv vRv j)
    (hbf : HonestBadFreeVS H χ ρ y yH mhv kLv vLv kRv vRv)
    (hρ0 : rho3 δF ρ 0 = H.vTot (toVCL χ)) (hρ1 : rho3 δF ρ 1 + y = H.xTot (toVCL χ))
    (hyT : y = H.yTot (toVCL χ)) (hρ2 : rho3 δF ρ 2 = H.pTot (toVCL χ))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1)
    (hpubC : pubsCH δF ρ y yH CellH.pubH = ∑ j ∈ Finset.range (H.V.memRows (tCW hT hP)),
      algebraMap F K (CellTraceH.mN mhv j) * (CellTraceH.dN δF H.V.basis (H.V.hM (tCW hT hP))
        (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP)) (chalsVS δF χ) (pubsCH δF ρ y yH)
        (cellColVS H χ) mhv j)⁻¹)
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
    (hGC : GoodCVS δF (vsOf H.V) msg.msg0C (msg.requests χ) χ)
    (hcomp : RAP.SatisfiesWithPreprocessing
        (ChipH.computeChipVCLH (vsOf H.V).hN (vsOf H.V).computeNodes (vsOf H.V).basis (chalVH (vsOf H.V).basis χ)
          (pubVH δF (vsOf H.V).basis (vsOf H.V).claim msg.msg0C (msg.requests χ) χ) (vsOf H.V).orbitC)
        (fun j => msg.Qc χ (Fin.cast rfl j))) :
    AcceptsG (vsOf H.V) msg χ := by
  have hy1 : y = (msg.msg2M χ).1 := by rw [hy]
  have hy2 : yH = (msg.msg2M χ).2 := by rw [hy]
  subst hρ hy1 hy2
  have hcell := cellTwin_accepted_VS H χ _ _ _ mhv hbf.hz hbf.h0 hbf.h1 hρ0 hρ1 hbf.hpoleC hpubC
  have hwalk := walkTwin_accepted_VS H χ _ _ _ kLv vLv kRv vRv hbf.h1 hbf.h2 hyT hρ2 hkL hkR
    hbf.hpoleX hbf.hpoleL hbf.hpoleR hpubX hpubP
  refine acceptsG_of_chips δF hT hP kr hC (vsOf H.V) msg χ hGC hcomp (goodM_vsOf_C H) (goodW_vsOf H)
    (fun hw => ?_) (fun hw => ?_)
  · have hfun : (fun j => msg.Qm χ (tCS hT hP) (Fin.cast hw j)) = fun j => CellTraceH.cellTraceH δF H.V.basis
        (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP)) (chalsVS δF χ)
        (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) (cellColVS H χ) mhv
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

end Accepted

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
