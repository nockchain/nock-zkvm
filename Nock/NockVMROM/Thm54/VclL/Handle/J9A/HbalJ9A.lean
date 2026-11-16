/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/HbalJ9A.lean

* `extAC`, `provsAC`: the S8 wiring lists at the coins and the message (the J-8 lists of `AcceptsJ8.extJ8` /
    `provsJ8` at the J-8 projections, + the flag-gated axis / split lists and the root-gated atom walk of
    `ShareJ9A`), exactly in `HokJ9AG9.acceptsJ9A_holdsN_finalLGG`'s order (`hprovX … hextS` are `rfl`).
  * `extAC_eq`, `provsAC_eq`: they ARE `RR49A`'s coin-free `extA` / `provsA` at `gA := axOn`, `gS := spOn` (the
    readout bridge for F1).
  * **`hbalA`**: S8's `hbal : BalJ8 … (pubVJ9 …) provsAC extAC` from the `AcceptsJ9A` fields alone
    (`BalJ9A.balJ9A_frame`; `.p` by `ShareJ9A.axShare_sumP` + `hGp`; `.s` by `ShareJ9A.balS_J9A` + `hGS` with the J,
    inc, atom-walk, axis and split sums).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ShareJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.RR49A

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.HbalJ9A

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (BalJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 pad8_sum atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (byBal)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z chalsAJ8Z_agree)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (pubVJ9)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AcceptsJ9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ShareJ9A
open Nock.Jet.RapJetJ8 (jRd jProv jCons)
open Nock.Jet.PinJ8 (pinCons)

noncomputable section

section Lists
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The S8 externals at the coins and the message.** -/
def extAC (Pb : PubJ9A p) (χ : Coins frameJ8 K) (M : MsgJ9A' p K δ) (tr : TrJ9A (ZMod p)) :
    (bl : Bal) → List (Fin (mOf bl) → K) :=
  byBal (β := fun bl => List (Fin (mOf bl) → K))
    (ServeH.walkXReqs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (qW δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsW) ++
      jRd b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ))
    (if Pb.axOn then AxisChipJ9.axPathReqs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
      (qAX δ b Pb tr (chalsMJ8 δ χ) M.pubsX) else [])
    (pinCons (p := p) (K := K) Pb.regs Pb.idx ++
      (if Pb.axOn then AxisChipJ9.axLimbReqs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
        (qAX δ b Pb tr (chalsMJ8 δ χ) M.pubsX) else []) ++
      jCons b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ))

/-- **The S8 providers at the coins and the message.** -/
def provsAC (Pb : PubJ9A p) (χ : Coins frameJ8 K) (M : MsgJ9A' p K δ) (tr : TrJ9A (ZMod p)) :
    (bl : Bal) → List ((Fin (mOf bl) → K) × K) :=
  byBal (β := fun bl => List ((Fin (mOf bl) → K) × K))
    (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC))
    (ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsW))
    (jProv b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ) ++
      (pad8 (atomIncProvs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
          (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)) ++
        pWA Pb.krootsV (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
          (qV δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsV)) ++
        (if Pb.axOn then AxisChipJ9.axTagProvs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
          (qAX δ b Pb tr (chalsMJ8 δ χ) M.pubsX) else []) ++
        pSA Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS (qSP δ b Pb tr (chalsMJ8 δ χ) M.pubsS)))

/-- **`extAC` is `RR49A.extA`** at `gA := axOn`. -/
theorem extAC_eq (Pb : PubJ9A p) (χ : Coins frameJ8 K) (M : MsgJ9A' p K δ) (tr : TrJ9A (ZMod p)) (bl : Bal) :
    extAC δ b Pb χ M tr bl = RR49A.extA b Pb.axOn Pb tr bl := by
  obtain ⟨hL, hP, hT⟩ := axLists_qAX δ b Pb tr (chalsMJ8 δ χ) M.pubsX
  have hJ := ReadIOJ8.jLists_congr b Pb.nodesJ Pb.orbitJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ (fun _ => (0 : K)) (fun _ => 0)
    (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ) tr.J Pb.lay
    (by simp only [TraceJ8.widthW_eq, TraceJ8.widthJ_eq, TraceJ8.widthA_eq, TraceJ8.widthV_eq, TraceJ8.widthM_eq]; omega)
    (by norm_num) (fun _ _ _ _ => rfl)
  cases bl
  · show _ ++ _ = _ ++ _
    rw [(DescentVSQ.walkLists_congrW b Pb.nodesW Pb.orbitW Pb.orbitW _ _ (fun _ => (0 : K)) (fun _ => 0)
      (qW δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsW) tr.W
      (by simp only [TraceJ8.widthW_eq, TraceJ8.widthJ_eq, TraceJ8.widthA_eq, TraceJ8.widthV_eq, TraceJ8.widthM_eq]; omega)
      (by norm_num) (fun _ _ _ _ => rfl)).1, hJ.1]
    rfl
  · show (if Pb.axOn then AxisChipJ9.axPathReqs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
      (qAX δ b Pb tr (chalsMJ8 δ χ) M.pubsX) else []) = (if Pb.axOn then axPathReqsOf b Pb tr else [])
    rw [hP]
  · show _ ++ (if Pb.axOn then AxisChipJ9.axLimbReqs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
        (qAX δ b Pb tr (chalsMJ8 δ χ) M.pubsX) else []) ++ _ =
      _ ++ (if Pb.axOn then axLimbReqsOf b Pb tr else []) ++ _
    rw [hL, hJ.2.1]

/-- **`provsAC` is `RR49A.provsA`** at `gA := axOn`, `gS := spOn`. -/
theorem provsAC_eq (Pb : PubJ9A p) (χ : Coins frameJ8 K) (M : MsgJ9A' p K δ) (tr : TrJ9A (ZMod p)) (bl : Bal) :
    provsAC δ b Pb χ M tr bl = RR49A.provsA b Pb.axOn Pb.spOn Pb tr bl := by
  obtain ⟨hL, hP, hT⟩ := axLists_qAX δ b Pb tr (chalsMJ8 δ χ) M.pubsX
  cases bl
  · exact ReadIOJ8.cellProvsW_congr b Pb.nodesC Pb.orbitC Pb.orbitC _ _ (fun _ => (0 : K)) (fun _ => 0)
      (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC) tr.M (by rw [TraceJ8.widthM_eq]; omega) (by norm_num)
      (fun _ _ _ _ => rfl)
  · exact (DescentVSQ.walkLists_congrW b Pb.nodesW Pb.orbitW Pb.orbitW _ _ (fun _ => (0 : K)) (fun _ => 0)
      (qW δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsW) tr.W
      (by simp only [TraceJ8.widthW_eq, TraceJ8.widthJ_eq, TraceJ8.widthA_eq, TraceJ8.widthV_eq, TraceJ8.widthM_eq]; omega)
      (by norm_num) (fun _ _ _ _ => rfl)).2
  · have hS' : pSA Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS (qSP δ b Pb tr (chalsMJ8 δ χ) M.pubsS) =
        (if Pb.spOn then splitProvsOf b Pb tr else []) := by
      unfold pSA; rw [splitProvs_qSP]
    show _ ++ (pad8 _ ++ pWA _ _ ++ _ ++ pSA _ _ _ _ _ _ _ _) = _ ++ (pad8 _ ++ _ ++ _ ++ _)
    rw [hS', hT,
      (ReadIOJ8.jLists_congr b Pb.nodesJ Pb.orbitJ Pb.orbitJ _ _ (fun _ => (0 : K)) (fun _ => 0)
        (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ) tr.J Pb.lay
        (by simp only [TraceJ8.widthW_eq, TraceJ8.widthJ_eq, TraceJ8.widthA_eq, TraceJ8.widthV_eq, TraceJ8.widthM_eq]; omega)
        (by norm_num) (fun _ _ _ _ => rfl)).2.2,
      ReadIOJ8.atomIncProvs_congr b Pb.nodesA Pb.orbitA Pb.orbitA _ _ (fun _ => (0 : K)) (fun _ => 0)
        (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA) tr.A
        (by simp only [TraceJ8.widthW_eq, TraceJ8.widthJ_eq, TraceJ8.widthA_eq, TraceJ8.widthV_eq, TraceJ8.widthM_eq]; omega)
        (by norm_num) (fun _ _ _ _ => rfl),
      (DescentVSQ.walkLists_congrW b Pb.nodesV Pb.orbitV Pb.orbitV _ _ (fun _ => (0 : K)) (fun _ => 0)
        (qV δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsV) tr.V
        (by simp only [TraceJ8.widthW_eq, TraceJ8.widthJ_eq, TraceJ8.widthA_eq, TraceJ8.widthV_eq, TraceJ8.widthM_eq]; omega)
        (by norm_num) (fun _ _ _ _ => rfl)).2]

end Lists

section Bal
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **S8's `hbal` from `AcceptsJ9A`.** -/
theorem hbalA {Pb : PubJ9A p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9A' p K δ} {tr : TrJ9A (ZMod p)} {r : RowsJ9A} {g : ℕ}
    (hacc : AcceptsJ9A δ b Pb Rg c χ M tr r g) (hp64 : 64 ≤ ringChar (ZMod p)) :
    BalJ8 (b := b) (δ := δ) (chalV := chalVJ8 b χ) (pubVal := pubVJ9 δ b c M.m M.ρ M.ρS χ)
      (provsAC δ b Pb χ M tr) (extAC δ b Pb χ M tr) := by
  have hcv := coinsCV_J8 δ b χ
  have hcM : (⟨Quad.mk _ (chalsMJ8 δ χ 33) (chalsMJ8 δ χ 35), Quad.mk _ (chalsMJ8 δ χ 34) (chalsMJ8 δ χ 36)⟩ :
      IOCoins 𝕂′) = TeleCQ.coinsCV b δ (chalVJ8 b χ) :=
    (mcoins_of_agree δ χ (chalsMJ8 δ χ) (fun _ _ _ => rfl)).trans hcv.symm
  have hcA : (⟨Quad.mk _ (chalsAJ8Z δ χ 33) (chalsAJ8Z δ χ 35), Quad.mk _ (chalsAJ8Z δ χ 34) (chalsAJ8Z δ χ 36)⟩ :
      IOCoins 𝕂′) = TeleCQ.coinsCV b δ (chalVJ8 b χ) :=
    (mcoins_of_agree δ χ (chalsAJ8Z δ χ) (chalsAJ8Z_agree δ χ)).trans hcv.symm
  have hcJ : Nock.Jet.RapJetJ8.coinsJ δ (chalsJJ8 χ) = TeleCQ.coinsCV b δ (chalVJ8 b χ) :=
    (coinsJ_J8 δ χ).trans hcv.symm
  -- the five share sums at the compute coins
  have h3 := JGenJ8.jet_tagged_sumG hacc.hJk
  rw [hcJ] at h3
  have hI := ServiceJ8.atomIncProvs_sum δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _
    hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA
  have hI8 := pad8_sum (TeleCQ.coinsCV b δ (chalVJ8 b χ)) (atomIncProvs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ)
    M.pubsA (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA))
  have hcA' : AtomServedQ.acoins δ (chalsAJ8Z δ χ) = TeleCQ.coinsCV b δ (chalVJ8 b χ) := hcA
  rw [hcA'] at hI
  rw [hI] at hI8
  have hW := awShare_sum hacc.hVk
  rw [hcA] at hW
  have hX := axShare_sumS hacc.hAXk
  rw [hcM] at hX
  have hXP := axShare_sumP hacc.hAXk
  rw [hcM] at hXP
  have hS := spShare_sum hacc.hSPk
  rw [hcM] at hS
  have hGs := balS_J9A (TeleCQ.coinsCV b δ (chalVJ8 b χ)) M.ρS _ _ _ _ _ _ _ _ _ _ _ _ _ hacc.hGS h3 hI8 hW hX hS
  exact BalJ9A.balJ9A_frame χ c M.m M.ρ M.ρS Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _
    hacc.hsatC hacc.hbindC hacc.hinjC hacc.hadjC (fun _ _ _ => rfl)
    Pb.kroots Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _ hacc.hsatW hacc.hbindW
    (GeneratedField.primeFieldElems_zmod p) hp64 hacc.hinjW hacc.hadjW (fun _ _ _ => rfl)
    Pb.nodesJ Pb.orbitJ M.pubsJ Pb.lay _ hacc.hJk rfl rfl rfl _ hXP _ _ rfl rfl hacc.hGx hacc.hGp hGs

end Bal

end

end Nock.NockVMROM.Thm54.VclL.Handle.HbalJ9A

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.HbalJ9A
#print axioms extAC_eq
#print axioms provsAC_eq
#print axioms hbalA
end Axioms
