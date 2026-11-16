/-
  Nock/NockVMROM/Thm54/VclL/Handle/LinkJ8NV.lean

  The soundness chain of R5 restated over `AcceptsJ8''''` / `AcceptsJ8ZG`: `claimRecsT_eqG`, `rdV_viewG`,
  `hXW_of_ioG` (RealVJ8), `hHXV_ofZG` (LinkJ8R4), `hsoundJ8ZUG` / `hsoundJ8XUG` (AcceptsJ8L; the compute assembly at
  `HokLJ8G.acceptsJ8_holdsN_finalLG`, the J chip as `hJk`), `linkXUG_of_R5` and **`probJ8NV_final`**:
  `Pr_χ[(∃ M, AcceptsJ8'''') ∧ ¬ HoldsN c] < 2^-155` at the same binders as `LinkJ8R5.probJ8R5_final`.  The events,
  the readout data `RR4 … R0d` / `LL4 … L0d` and the figure are R5's, unchanged: the J lists in the events are read off
  the trace and are empty when `nJ = 0`.  Proof texts are R5's with the J chip's five conjuncts replaced by `hJk`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R5
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZBG
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZWG
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZXG
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZHG
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZLG
import Nock.NockVMROM.Thm54.VclL.Handle.HokLJ8G

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8NV

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Reads)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA restrictWalkK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8 (AWSeedsOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.FibreJ8 (effP)
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL.Handle.CorJ8F (denJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_agree chalsOK_J8 chalsAJ8_ok)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY encZY_cell inlineAtoms_encZY)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC outside40C outside_sumJ8_D)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 wchain_out v0 v1)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8 (OutJ8 outJ8_of_outside chalsMJ8_z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.Atoms (lenL)
open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 LayLe realize40 realizeJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3
open Nock.NockVMROM.Thm54.VclL.Handle.LinkQ2J8 (valReader)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (rowsMJ8 rowsB0 crA)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8 (censusList2)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3G
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z atomTZ)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z chalsAJ8Z_of_ne chalsAJ8Z_ok chalsAJ8Z_agree)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R4 (RR4 LL4 hHXV_ofZ)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL toHQ)
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun claimH isCellN)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crA crM crW crC staged_eq below_of_mem shV)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (mbXs claimCells claimRecsJ8 pinRecsJ8 rkC MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z chalsAJ8Z_zAt)
open Nock.NockVMROM.Thm54.VclL.Handle.RealVJ8
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R4
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R5
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G

noncomputable section

section Val
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (xS xF xE)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (envCJ8)

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP (toMsgJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)

/-- **The claim serials off row 0** (on an `AcceptsJ8Z` trace, `row0_hdZ`): the readout's claim records are
`toMsgJ8Z`'s. -/
theorem claimRecsT_eqG (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (hp : 17 < p)
    (hacc : AcceptsJ8ZG δ b Pb Rg c χ (toMsgJ8Z δ b Pb c χ M tr) tr) :
    claimRecsT δ Pb c χ tr = claimRecsJ8 δ χ c M.m := by
  unfold claimRecsT claimRecsJ8
  refine List.map_congr_left fun k hk => ?_
  have hc : isCellN (claimNoun c k) = true := (List.mem_filter.mp hk).2
  have hd := AcceptsJ8ZLG.row0_hdZ δ b Pb Rg c χ (toMsgJ8Z δ b Pb c χ M tr) tr hp hacc k
  have htr : (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C 0).trace =
      (envX δ b Pb c χ (toMsgJ8Z δ b Pb c χ M tr) tr 0).trace := by
    simp only [envCJ8, envX, TeleC.envsN]
    split_ifs <;> rfl
  have h2 := congrArg Prod.snd hd
  simp only [hdV] at h2
  have hv := ZMod.val_injective p h2
  have hm : (toMsgJ8Z δ b Pb c χ M tr).m = M.m := rfl
  rw [htr, hv, hm]
  congr 2
  unfold claimH
  cases hx : claimNoun c k with
  | atom v => rw [hx] at hc; simp [isCellN] at hc
  | cell a b' => rfl

/-- **#2 at an accepted trace**: the readout IS `LinkJ8X''.rdV`'s pair at `toMsgJ8Z`. -/
theorem rdV_viewG (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (hp : 17 < p)
    (hacc : AcceptsJ8ZG δ b Pb Rg c χ (toMsgJ8Z δ b Pb c χ M tr) tr) :
    valReqsJ8 δ b Pb c tr χ = (toMsgJ8Z δ b Pb c χ M tr).reqsC ++
      cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) (toMsgJ8Z δ b Pb c χ M tr).pubsC
        (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) (toMsgJ8Z δ b Pb c χ M tr).pubsC
          (qM δ b Pb tr (chalsMJ8 δ χ) (toMsgJ8Z δ b Pb c χ M tr).pubsC)) ∧
    valProvsJ8 δ b Pb tr χ = SVFrame.liftWts (cellVRecords δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ)
      (toMsgJ8Z δ b Pb c χ M tr).pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) (toMsgJ8Z δ b Pb c χ M tr).pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) (toMsgJ8Z δ b Pb c χ M tr).pubsC))) ++ (toMsgJ8Z δ b Pb c χ M tr).xsC := by
  have hw : 183 ≤ (cellChip δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.w := by
    rw [cell_w]; norm_num
  refine ⟨?_, ?_⟩
  · show (claimRecsT δ Pb c χ tr ++ pinRecsJ8 δ Pb χ) ++ _ = (claimRecsJ8 δ χ c M.m ++ pinRecsJ8 δ Pb χ) ++ _
    rw [claimRecsT_eqG δ b Pb Rg c χ M tr hp hacc, cVInt_chip]
    refine congrArg ((claimRecsJ8 δ χ c M.m ++ pinRecsJ8 δ Pb χ) ++ ·) ?_
    exact cVInt_congr δ b Pb.nodesC Pb.orbitC _ _ _ _ _ _ (by norm_num) hw fun j hj => congrArg tr.M (Fin.ext rfl)
  · show liftWts _ ++ mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) (fun _ => 0) tr.A =
      liftWts _ ++ mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
    rw [cVRec_chip]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · exact congrArg liftWts
        (cVRec_congr δ b Pb.nodesC Pb.orbitC _ _ _ _ _ _ (by norm_num) hw fun j hj => congrArg tr.M (Fin.ext rfl))
    · exact mbXs_congr δ b Pb.nodesA Pb.orbitA _ _ _ _ _ _ (by norm_num)
        (by rw [AtomChipHQ.atomChipHQ_width]; norm_num) (fun j hj => rfl) rfl rfl

end Val


section FxR
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))] {r : RowsJ8}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 St40 sum40 fpx_out v4 v5 v6 v7)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (extY_below shV_round)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z)


/-- **`LinkJ8.hXW` from the fingerprint-export lookup** (the class of `LinkJ8R2V.hXV_of_io`): on an `AcceptsJ8Z`
trace, with `pubsC(2,3) = pubsW(0,1)` and the validity pair outside the IO failure event of the J-8 walk's keys
(at the `bitFix` view) against the cell table's export records, every key the J-8 walk consumes is a decoded cell
row. -/
theorem hXW_of_ioG [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8ZG δ b Pb Rg c χ M tr) (hp : 64 ≤ p)
    (hWC : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsC 2) (M.pubsC 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsW 0) (M.pubsW 1))
    (hout : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr) (fxProvsJ8 δ b Pb.nodesC Pb.orbitC tr)) :
    WalkVCL.KeysExported (cellT δ b Pb χ M tr)
      (walkDataOf δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (AtomWalkAW.restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)))).X := by
  have hF := GeneratedField.primeFieldElems_zmod p
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp64 : 64 ≤ ringChar (ZMod p) := by rw [hrc]; exact hp
  have hsatC := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _
    hacc.hsatC
  have hbindC := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _
    hacc.hbindC
  have hsatP := AtomWalkAW.walkChipHQK_restrict_sat δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _
    (WalkJ8.walkChipJ8_bitFix_sat δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _ hF hp64 hacc.hsatW)
  have hbindP := AtomWalkAW.walkChipHQK_restrict_bind δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ)
    M.pubsW _ (WalkJ8.walkChipJ8_bitFix_bind δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _
      hacc.hbindW)
  have hrq : walkXInternal δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (AtomWalkAW.restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW))) = fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr :=
    wXInt_bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW _ _ _ _ tr.W
  have hpv : liftWts (cellXRecords δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))) = fxProvsJ8 δ b Pb.nodesC Pb.orbitC tr := by
    have hw : 183 ≤ (cellChip δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.w := by
      rw [cell_w]; norm_num
    rw [cXRec_chip]
    exact congrArg liftWts
      (cXRec_congr δ b Pb.nodesC Pb.orbitC _ _ _ _ _ _ hw (by norm_num) fun j hj => congrArg tr.M (Fin.ext rfl))
  rw [← hrq, ← hpv] at hout
  have hcnt : (walkXInternal δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (AtomWalkAW.restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)))).length < p := by
    rw [walkXInternal_length]
    have h := hacc.hkpW
    rw [hrc] at h
    omega
  exact walk_keys_exported δ Pb.kroots b Pb.hnC Pb.nodesC Pb.orbitC Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ)
    M.pubsC M.pubsW _ _ hsatC hbindC hacc.hinjC hacc.hadjC hsatP hbindP hacc.hinjW hacc.hadjW _ _
    (ProbJ8.chalsOK_J8 δ χ) 0 (by rw [zero_add]; exact hWC) (p := p) [] (by simp) (by simp)
    (fun hc => hout (mem_IOFailureEventW_iff.mpr (Or.inl hc)))
    (fun hc => hout (mem_IOFailureEventW_iff.mpr (Or.inr (Or.inr hc)))) (by simpa using hcnt)

end FxR

section HXV
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`LinkJ8.hHXV`, derived**: on an `AcceptsJ8Z` trace whose `wreqs` are the atom walk's reads, outside the atom
export event (#4, `houtA`) with the count `< p`, every atom-walk row's read names a decoded atom-table row. -/
theorem hHXV_ofZG [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8ZG δ b Pb Rg c χ M tr)
    (hwr : M.wreqs = ServeH.walkXReqs b Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
      (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV))
    (houtA : ((AtomServedQ.acoins δ (chalsAJ8Z δ χ)).gamma, (AtomServedQ.acoins δ (chalsAJ8Z δ χ)).pole) ∉
      IOFailureEventW ((AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
          (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA) ++ M.wreqs).map (BalanceQ.liftRec (K := K) (L := 𝕂′)))
        (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
          (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA))))
    (hcountA : (AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
      (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA) ++ M.wreqs).length < p) :
    ∀ j < Pb.nV, ∃ c' ∈ atomTZ δ b Pb χ M tr,
      (natOf ((AtomWalkAW.walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
          (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV) j).trace WChip.idx),
        childHOf (AtomWalkAW.walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
          (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV) j) false,
        childHOf (AtomWalkAW.walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
          (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV) j) true) = exportRec c'.b0 := by
  have hF := GeneratedField.primeFieldElems_zmod p
  have hs := AtomServedQ.atom_consume_served δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ hacc.hsatA
    hacc.hbindA hacc.hinjA hacc.hadjA M.wreqs hacc.hbalA houtA hcountA
  intro j hj
  have hm := hs _ (List.mem_append_right _ (by rw [hwr]; exact List.mem_map_of_mem (List.mem_finRange ⟨j, hj⟩)))
  obtain ⟨c', hc', he⟩ := HxvJ8.atom_hHX_of_served δ b Pb.hnA Pb.nodesA Pb.orbitA Pb.krootsV Pb.hnV Pb.nodesV
    Pb.orbitV (chalsAJ8Z δ χ) M.pubsA M.pubsV _ _ hF hacc.hsatA ⟨j, hj⟩ hm
  refine ⟨c', hc', ?_⟩
  rw [show j = ((⟨j, hj⟩ : Fin Pb.nV) : ℕ) from rfl, AtomWalkProvJ8.walkEnvFA_eq_wEF]
  exact he

end HXV

section SoundZ
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

/-- **`hsoundJ8ZU`**: `hsoundJ8Z` with the atom table ALSO accepted by the variant chip `atomChipHQL` on the same
columns (`qAL`, `toHQ (qAL …) = qA …`), through `HokLJ8.acceptsJ8_holdsN_finalL` (`SmallU`, no `hok`). -/
theorem hsoundJ8ZUG [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    (hacc : AcceptsJ8ZG δ b Pb Rg c χ M tr)
    (hsatL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
      (qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA))
    (hbindL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
      (qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA))
    (hout : ∀ s ∈ allJ8C (withLiftC R L), ¬ s.mem tr χ)
    (hWV : R.wdC tr χ = walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
      (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV)))
    {rA : ℕ → ARow} (hl : LinkJ8ZU δ b Pb c χ M tr R L rA) :
    Nock.Jet.HoldsN c := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp : 2 ^ 63 + 1 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [hrc]; omega
  have hF' := GeneratedField.primeFieldElems_zmod p
  have O := outJ8_of_outside R L b hout
  have hz2 : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) := by
    rw [(chalsMJ8_z (δ := δ) χ).1, (chalsMJ8_z (δ := δ) χ).2]
  have hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0 := by
    rw [hz2]; exact O.z_ne
  -- (b) the IO events, read at the trace's lists (L1)
  have houtC : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (R.D.valReqs tr χ) (R.D.valProvs tr χ) := O.valid hl.budV.1 hl.budV.2
  rw [hl.rdV.1, hl.rdV.2] at houtC
  have hx : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (R.D.cxReqs tr χ) (R.D.cxProvs tr χ) := O.hout_x hl.budX.1 hl.budX.2
  rw [hl.rdX.1, hl.rdX.2] at hx
  have hpp : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (L.pReqs tr (toVSQ χ)) (L.pProvs tr (toVSQ χ)) := O.hout_p hl.budP.1 hl.budP.2
  rw [hl.rdP.1, hl.rdP.2] at hpp
  have hs : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (R.D.svReqs tr χ) (R.D.svProvs tr χ) := O.hout_s hl.budS.1 hl.budS.2
  rw [hl.rdS.1, hl.rdS.2] at hs
  have hV : (chalsAJ8Z δ χ 0, chalsAJ8Z δ χ 1) ∉ WalkVCL.walkEvent (algebraMap (ZMod p) K δ) (R.wdC tr χ) :=
    by rw [(chalsAJ8Z_01 δ χ).1, (chalsAJ8Z_01 δ χ).2]; exact O.houtV
  rw [hWV] at hV
  have hW := wchain_out L (outside40C R L hout)
  rw [hl.rdWW, ← (coinW_J8 δ χ).1, ← (coinW_J8 δ χ).2] at hW
  have hw0 : (limbVal b (chalVJ8 b χ) chalAlphaW, limbVal b (chalVJ8 b χ) chalGammaW) ∉
      cwEvent (K := K) (L.cRows tr) (L.cH tr) := O.hw rfl rfl
  rw [hl.rdWC.1, hl.rdWC.2] at hw0
  have hα0 : limbVal b (chalVJ8 b χ) chalAlphaW ∉ tileSet (K := K) (foOf (L.cRows tr)) (L.cH tr) := O.hα rfl
  rw [hl.rdWC.1, hl.rdWC.2] at hα0
  have hsatC0 := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hsatC
  have hbindC0 := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hbindC
  have htabC := TwoProviderQ.cellTable_accepts2 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _ hF' hq'
    hzC hsatC0 hbindC0 hacc.hinjC hacc.hadjC hacc.hnpC _ _ (chalsOK_J8 (δ := δ) χ) M.reqsC M.xsC hacc.hsumC houtC
    hacc.hxneC hl.hcountC M.vp hacc.hxC hacc.hvp0
  rw [hz2] at htabC
  have hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (encJ8 δ χ) :=
    inlineAtoms_encZY (by rw [hrc]; exact hpG) _ _
  have hEinj := EncInjJ8.encInj2_of_outside (withLiftC R L).D
    (outside_sumJ8_D (withLiftC R L) hout .bivariateCensus (by decide) (by decide) (by decide)) hq' O.z_ne hE
    htabC hl.hvp hl.hext hqM hk hl.hprs
  -- (c) the compute context
  have XC : XCtx Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb.orbit
      (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ))
      (limbVal b (chalVJ8 b χ) chalAlphaW) (limbVal b (chalVJ8 b χ) chalGammaW)
      (limbVal b (pubVJ8 δ b c M.m M.ρ M.ρS χ) pubSeed) :=
    ⟨by omega, hacc.hsatX, hacc.hinjX, hacc.hadjX, rfl, rfl, pubVJ8_IC δ b c M.m M.ρ M.ρS χ, rfl,
      pubVJ8_out δ b c M.m M.ρ M.ρS χ⟩
  exact HokLJ8G.acceptsJ8_holdsN_finalLG (χ := χ) (c := c) (m := M.m) (ρ := M.ρ) (ρS := M.ρS) (C := XC) (hp := hp)
    (provs := provsJ8 δ b Pb χ M tr) (ext := extJ8 δ b Pb c χ M tr)
    (hnC := Pb.hnC) (nodesC := Pb.nodesC) (orbitC := Pb.orbitC) (chalsC := chalsMJ8 δ χ) (pubsC := M.pubsC)
    (QC := qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) (hsatC := hacc.hsatC) (hbindC := hacc.hbindC)
    (hinjC := hacc.hinjC) (hadjC := hacc.hadjC) (hchC := fun _ _ _ => rfl)
    (kroots := Pb.kroots) (hnW := Pb.hnW) (nodesW := Pb.nodesW) (orbitW := Pb.orbitW) (chalsW := chalsMJ8 δ χ)
    (pubsW := M.pubsW) (QW := qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) (hsatW := hacc.hsatW) (hbindW := hacc.hbindW)
    (hF := hF') (hp64 := by rw [hrc]; omega) (hinjW := hacc.hinjW) (hadjW := hacc.hadjW)
    (hchW := fun _ _ _ => rfl)
    (nodesJ := Pb.nodesJ) (orbitJ := Pb.orbitJ) (pubsJ := M.pubsJ) (lay := Pb.lay)
    (PJ := qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ) (hJk := hacc.hJk)
    (Rt := Pb.Rt) (regs := Pb.regs) (ids := Pb.ids) (idx := Pb.idx) (rk := Pb.rk)
    (hnA := Pb.hnA) (nodesA := Pb.nodesA) (orbitA := Pb.orbitA) (chalsA := chalsAJ8Z δ χ) (pubsA := M.pubsA)
    (QA := qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA) (QL := qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
    (hQA := (qAL_toHQ δ b Pb tr _ _).symm) (hsatL := hsatL) (hbindL := hbindL)
    (hinjA := hacc.hinjA) (hadjA := hacc.hadjA) (hchA := fun j h1 h2 => chalsAJ8Z_agree δ χ j h1 h2)
    (krootsV := Pb.krootsV) (hnV := Pb.hnV) (nodesV := Pb.nodesV) (orbitV := Pb.orbitV) (chalsV := chalsAJ8Z δ χ)
    (pubsV := M.pubsV) (QV := qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV) (hsatV := hacc.hsatV) (hbindV := hacc.hbindV)
    (hinjV := hacc.hinjV) (hadjV := hacc.hadjV) (hchV := fun j h1 h2 => chalsAJ8Z_agree δ χ j h1 h2)
    (hprovX := rfl) (hextX := rfl) (hprovP := rfl) (hextP := rfl) (hprovS := provsJ8_sZ δ b Pb χ M tr) (hextS := rfl)
    (hGx := hacc.hGx) (hGp := hacc.hGp) (hGS := hacc.hGS)
    (hout := fun bl hbl => by cases bl with | x => exact hx | p => exact hpp | s => exact absurd rfl hbl)
    (houtS := hs) (hcount := hl.hcount)
    (hnpC := hacc.hnpC) (hzC := hzC) (γV := _) (ρV := _) (hokC := chalsOK_J8 (δ := δ) χ)
    (reqsC := M.reqsC) (xsC := M.xsC) (hsumC := hacc.hsumC) (houtC := houtC) (hxneC := hacc.hxneC)
    (hcountC := hl.hcountC) (vp := M.vp) (hxC := hacc.hxC) (hvp0 := hacc.hvp0)
    (E := encJ8 δ χ) (hconsE := fun a b' => by rw [hz2]; rfl) (hE := by rw [hz2]; exact hE)
    (rA := rA) (hvp := hl.hvp) (hEinj := hEinj)
    (hkW := hacc.hkW) (hknW := hacc.hknW) (hkpW := hacc.hkpW) (hXW := hl.hXW) (hHXW := hl.hHXW) (houtW := hW)
    (hRg := hRg) (hlay := hacc.hlay) (hsmall := hacc.hsmall) (huniq := hacc.huniq) (hTpl := hacc.hTpl)
    (hnd := hacc.hnd) (hidx := hacc.hidx) (hrk := hacc.hrk) (hlt := hacc.hlt) (hpinC := hacc.hpinC)
    (hinjE := hl.hinjE)
    (hRA := hl.hRA) (hsA := hl.hsA) (hidxA := hl.hidxA) (hpG := hpG) (hrn := hl.hrn) (hB := hl.hB)
    (hwRA := hl.hwRA) (wreqs := M.wreqs) (hbalA := hacc.hbalA) (houtA := hl.houtA)
    (hcountA := hl.hcountA) (hnpA := hacc.hnpA) (hzA := by rw [chalsAJ8Z_of_ne δ χ (by omega) (by omega), chalsAJ8Z_of_ne δ χ (by omega) (by omega)]; exact O.atom_hz) (hservedA := hl.hservedA)
    (hyV := ⟨rfl, rfl⟩) (hkV := hacc.hkV) (hknV := hacc.hknV) (hkpV := hacc.hkpV) (hseedsV := hl.hseedsV)
    (hXV := hl.hXV) (hHXV := hl.hHXV) (houtV := hV)
    (hseed := hl.hseed) (hα := hα0) (hw := hw0) (hreal := hl.hreal) (x := c) (hs := hl.hs) (hf := hl.hf)
    (he := hl.he)
end SoundZ

section SoundX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
variable {r : RowsJ8} {P g : ℕ}

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)


/-- **`hsoundJ8XU`**: accepted by `AcceptsJ8'''` (the atom table at the variant chip), outside `allJ8X (withFpxV … (withLiftC R L) …)`, at the
statement binders and under `LinkJ8XU` at `toMsgJ8Z`, the claim holds (`hXV` from `hfxA`, `hreal` from
`hcellF`, the claim binding and `hinjE` as in `hsoundJ8'`). -/
theorem hsoundJ8XUG [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    {r0 : RowsJ8} {g0 : ℕ} (hacc3 : AcceptsJ8'''' δ b Pb Rg c χ M tr r0 g0)
    (hout : ∀ s ∈ AtomFpxJ8.allJ8X (AtomFpxJ8.withFpxV δ b (withLiftC R L) Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV
      Pb.nodesA Pb.orbitA), ¬ s.mem tr χ)
    (hbV : Pb.nV ≤ r.AW) (hbA : Pb.nA ≤ r.A)
    (hWV : R.wdC tr χ = walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
      (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV)))
    {rA : ℕ → ARow} (hl : LinkJ8XU δ b Pb c χ (toMsgJ8Z δ b Pb c χ M tr) tr R L rA) :
    Nock.Jet.HoldsN c := by
  have hacc' := hacc3
  have hacc := acceptsJ8ZG_of'''' δ b hacc'
  have hAV : Quad.mk (algebraMap (ZMod p) K δ) ((toMsgJ8Z δ b Pb c χ M tr).pubsA 2)
      ((toMsgJ8Z δ b Pb c χ M tr).pubsA 3) =
      Quad.mk (algebraMap (ZMod p) K δ) ((toMsgJ8Z δ b Pb c χ M tr).pubsV 0) ((toMsgJ8Z δ b Pb c χ M tr).pubsV 1) := by
    show Quad.mk _ (M.pubsA 2) (M.pubsA 3) = Quad.mk _ (M.pubsV 0) (M.pubsV 1)
    rw [hacc'.hfxA.1, hacc'.hfxA.2]
  have hXV := AcceptsJ8ZXG.hXV_withFpxVZ δ b Pb c χ (toMsgJ8Z δ b Pb c χ M tr) tr hacc (withLiftC R L) hout hbV hbA hAV
  replace hout := AtomFpxJ8.outsideC_of_outsideX _ hout
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp : 2 ^ 63 + 1 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [hrc]; omega
  have hF' := GeneratedField.primeFieldElems_zmod p
  have O := outJ8_of_outside R L b hout
  have hz2 : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) := by
    rw [(chalsMJ8_z (δ := δ) χ).1, (chalsMJ8_z (δ := δ) χ).2]
  have hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0 := by
    rw [hz2]; exact O.z_ne
  have houtC : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (R.D.valReqs tr χ) (R.D.valProvs tr χ) := O.valid hl.budV.1 hl.budV.2
  rw [hl.rdV.1, hl.rdV.2] at houtC
  have hcountC := hcountC_of' δ b Pb c χ M tr hacc'.hlenC
  have hsatC0 := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hsatC
  have hbindC0 := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hbindC
  have htabC := TwoProviderQ.cellTable_accepts2 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _ hF' hq'
    hzC hsatC0 hbindC0 hacc.hinjC hacc.hadjC hacc.hnpC _ _ (chalsOK_J8 (δ := δ) χ) _ _ hacc.hsumC houtC
    hacc.hxneC hcountC _ hacc.hxC hacc.hvp0
  rw [hz2] at htabC
  have hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (encJ8 δ χ) :=
    inlineAtoms_encZY (by rw [hrc]; exact hpG) _ _
  -- the census at the registered and claim cell nouns (Q2)
  have hG := LinkQ2J8.hinjE_of_outside (withLiftC R L) hout hq' O.z_ne hE htabC hl.hvp hl.hext hqM hk
    (G := censusG Pb c)
    (fun x hx => ⟨(hacc'.hcen x hx).1, fun v hv => hqM v (by rw [hrc]; exact (hacc'.hcen x hx).2 v hv)⟩) hl.hprsG
  have hinjE : ∀ id ∈ Pb.regs, ∀ d ∈ decodedNouns2 ((cellT δ b Pb χ (toMsgJ8Z δ b Pb c χ M tr) tr).map (·.b0))
      (extB p rA), encJ8 δ χ (Nock.Jet.Autogen.compile p (Pb.Rt id)) = encJ8 δ χ d →
        Nock.Jet.Autogen.compile p (Pb.Rt id) = d :=
    fun id hid d hd he => hG _ (List.mem_append_left _ (List.mem_map_of_mem hid)) d hd he
  -- the claim's cell records are served
  have hvpr : ∀ k ∈ (toMsgJ8Z δ b Pb c χ M tr).vp,
      k.2.1 < ringChar (ZMod p) ∧ k.2.2.1 < ringChar (ZMod p) ∧ k.2.2.2 < ringChar (ZMod p) := by
    intro k hk
    obtain ⟨h1, h2, h3⟩ := hacc.hvp0 k hk
    exact ⟨by omega, by omega, h3⟩
  have hcell : ∀ k : Fin 3, isCellN (claimNoun c k) = true →
      denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA
        (1, (M.m k).1) = some (claimNoun c k) := by
    intro k hkc
    have hprov := Nock.Jet.PinJ8.regClaims_provided δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) hF' hsatC0 hbindC0 hacc.hinjC hacc.hadjC _ _ (chalsOK_J8 (δ := δ) χ)
      _ _ hacc.hsumC houtC hacc.hxneC hcountC _ hacc.hxC hvpr (regs := [0])
      (Ef := fun _ => encJ8 δ χ (claimNoun c k)) (rk := fun _ => rkC (claimNoun c k)) (idx := fun _ => (M.m k).1)
      (fun _ _ => List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkc⟩, rfl⟩))
      (fun _ _ => by
        have h62 : (rkC (claimNoun c k)).2 < 2 ^ 62 := Nat.mod_lt _ (by positivity)
        rw [hrc]
        exact ⟨hacc'.hclR k hkc, by omega, hacc'.hclI k hkc⟩) 0 (List.mem_singleton_self 0)
    rcases hprov with hc | hv
    · exact claimK_genuine_cell hq' (fun a b' => rfl) hE htabC hl.hvp
        (fun d hd he => hG _ (List.mem_append_right _ (List.mem_map_of_mem
          (List.mem_filter.mpr ⟨List.mem_finRange k, hkc⟩))) d hd he) hc
    · exfalso
      obtain ⟨h1, h2, -⟩ := hl.hvp _ hv
      exact rkC_ne hkc (Prod.ext h1 h2)
  have hden : ∀ k : Fin 3, denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA
      (hdV (envX δ b Pb c χ (toMsgJ8Z δ b Pb c χ M tr) tr 0) (![xS, xF, xE] k)) = some (claimNoun c k) := by
    intro k
    rw [AcceptsJ8ZLG.row0_hdZ δ b Pb Rg c χ _ tr (by omega) hacc k]
    exact den_claim _ _ c M.m k (hacc'.hclA k) (hacc'.hclI k) (hcell k)
  have hreal : (stX (envX δ b Pb c χ (toMsgJ8Z δ b Pb c χ M tr) tr 0)).isChain = false :=
    AcceptsJ8ZLG.hrealJ8Z δ b Pb Rg c χ _ tr (by omega) hacc hacc'.hcellF
  exact hsoundJ8ZUG δ b Pb hRg c χ (toMsgJ8Z δ b Pb c χ M tr) tr R L hpG hqM hk hacc hacc3.hsatL hacc3.hbindL hout hWV
    { rdX := hl.rdX, budX := hl.budX, rdP := hl.rdP, budP := hl.budP, rdS := hl.rdS, budS := hl.budS, hcount := hl.hcount, rdV := hl.rdV, budV := hl.budV, rdWC := hl.rdWC, rdWW := hl.rdWW, hext := hl.hext, hprs := hl.hprs, hvp := hl.hvp, hXW := hl.hXW, hHXW := hl.hHXW, hRA := hl.hRA, hsA := hl.hsA, hidxA := hl.hidxA, hrn := hl.hrn, hB := hl.hB, hwRA := hl.hwRA, houtA := hl.houtA, hservedA := hl.hservedA, hseedsV := hl.hseedsV, hHXV := hl.hHXV, hXV := hXV,
      hcountC := hcountC, hcountA := hcountA_ofZ'' δ b Pb c χ M tr hacc'.hlenA, hinjE := hinjE,
      hseed := AcceptsJ8ZLG.hseedJ8Z δ b Pb Rg c χ _ tr (by omega) hacc, hreal := hreal,
      hs := hden 0, hf := hden 1, he := hden 2 }

end SoundX

section Final
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

/-- **`LinkJ8XU` at the R4 real data from `AcceptsJ8'''` alone**: every field derived — R4a's `linkX_of_R4` with
`hsA` now DERIVED (`SmallU` at the reader, R3b's `smallU_valReader`, from `nA ≤ 2^62`, `hservedA` and the export
consume `ConsumeServedQ` of the #4 balance), `hvp` through the `SmallU` twin `hvp_of_mbU`, and no `hok` (derived
downstream at the variant chip). -/
theorem linkXUG_of_R5 [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31)
    (hpG : p = Nock.Atoms.p) (hr : RowsLe r EncInjJ8.cornerC) (hg : g ≤ 2 ^ 31) (hmax : Pb.nA + 2 ≤ r.maxlen)
    (hacc3 : AcceptsJ8'''' δ b Pb Rg c χ M tr r g)
    (hout : ∀ s ∈ AtomFpxJ8.allJ8X (AtomFpxJ8.withFpxV δ b
      (withLiftC (RR4 δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg) (LL4 δ b L0 Pb skel hs hL))
      Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA), ¬ s.mem tr χ)
 :
    LinkJ8XU δ b Pb c χ (toMsgJ8Z δ b Pb c χ M tr) tr (RR4 δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg)
      (LL4 δ b L0 Pb skel hs hL) (rAT b Pb tr) := by
  have hacc' := hacc3
  have hacc := acceptsJ8ZG_of'''' δ b hacc'
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp17 : 17 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hp64 : 64 ≤ p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hp32 : 2 ^ 32 ≤ p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hq : 2 ^ 63 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hcap := RepriceJ8.hcap_corner32 hr hg hpG
  have hB := hacc'.hbud
  have hΛ : fuelChip ≤ r.Λ := by rw [hr.2.2.2.1]; exact le_refl _
  have hoC := AtomFpxJ8.outsideC_of_outsideX _ hout
  set M' := toMsgJ8Z δ b Pb c χ M tr with hM'
  -- L1: the handle balances
  have rX := rdX_realIO δ b (realizeG δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg) Pb c χ M' tr
  have rS := rdS_realIO δ b (realizeG δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg) Pb c χ M' tr
  have rP := rdP_real40 δ b (realize40 δ b L0 (layPb Pb skel hs) hL) Pb c χ M' tr
  have bX := AcceptsJ8ZBG.budX_ofZ δ b Pb c χ M' tr hacc hp17 hB
  have bP := AcceptsJ8ZBG.budP_ofZ δ b Pb c χ M' tr hacc hp17 hB
  have bS := AcceptsJ8ZBG.budS_ofZ δ b Pb c χ M' tr hacc hp17 hB
  have L2 := AcceptsJ8ZWG.linkJ8_L2Z δ b Pb skel hs L0 hL c χ M' tr hacc hp17
  have hx := ListJ8C.hout_x_of_outsideC _ b hoC _ _ rX.1 rX.2 bX.1 bX.2
  have hpp := ListJ8C.hout_p_of_outside40C _ _ b hoC _ _ rP.1 rP.2 bP.1 bP.2
  have hss := ListJ8C.hout_s_of_outsideC _ b hoC _ _ rS.1 rS.2 bS.1 bS.2
  have hcnt := AcceptsJ8ZBG.hcount_ofZ δ b Pb c χ M' tr hacc hp17 hB hcap
  -- #2
  have rV := rdV_viewG δ b Pb Rg c χ M tr hp17 hacc
  have lV := RealVJ8.valJ8_length δ b Pb c tr χ
  -- the reader at chalsAJ8Z
  have hE := rAT_eq δ b Pb tr (chalsAJ8Z δ χ) M.pubsA
  have hRA : ∀ k : Fin Pb.nA, AtomChipHQ.Reads (AtomServedQ.aEF b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
      (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA) k) (rAT b Pb tr k) := by
    rw [← hE]; exact LinkQ2J8.hRA_valReader _
  have hwRA : ∀ j, (rAT (K := K) b Pb tr j).wR ≤ 1 := by
    rw [← hE]; exact LinkQ2J8.hwRA_valReader _ (LinkQ2J8.atom_wR_bool hacc.hsatA)
  have hidxA : ∀ k : Fin Pb.nA, (rAT (K := K) b Pb tr k).idx = k := by
    rw [← hE]; exact ReaderR3bJ8.hidxA_valReader hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA hacc.hnpA
  have hBA : AtomChipHQ.LimbsBounded (rAT (K := K) b Pb tr) := by
    rw [← hE]; exact ReaderR3bJ8.hB_valReader hp32 hacc.hsatA
  have hwout : ∀ k, Pb.nA ≤ k → (rAT (K := K) b Pb tr k).wR = 0 := by
    rw [← hE]; exact LinkQ2J8.wR_valReader_out _
  have hTout : ∀ j, Pb.nA ≤ j → (rAT (K := K) b Pb tr j).wR = 0 → (rAT (K := K) b Pb tr j).aR ≠ 0 := by
    rw [← hE]; exact LinkQ2J8.aR_valReader_out _
  -- #3: hservedA
  have hA3 : 3 + 2 * r.A < p := by
    have := hr.2.2.2.2.1; simp only [EncInjJ8.cornerC, corner31] at this
    rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]; omega
  have rAV := RealAJ8.rdAV_view δ b Pb tr (chalsAJ8Z δ χ) M.pubsA
  have hserved := ServedAJ8.hservedA_of_outside
    (withLiftC (RR4 δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg) (LL4 δ b L0 Pb skel hs hL)) hoC
    hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA (chalsAJ8Z_ok δ χ) hacc'.hvalA0 rAV
    ⟨(RealAJ8.avReqsJ8_length δ b Pb tr).trans (by have := hacc'.hbudV.2.2.1; omega),
      (RealAJ8.avProvsJ8_length δ b Pb tr).le.trans hacc'.hbudV.2.2.1⟩ hA3
  -- #4: houtA
  have rAX := RealAJ8.rdAX_view δ b Pb tr (chalsAJ8Z δ χ) M.pubsA (chalsAJ8Z δ χ) M.pubsV
  have hac : AtomServedQ.acoins δ (chalsAJ8Z δ χ) = AtomServedQ.acoins δ (ProbJ8.chalsAJ8 δ χ) := by
    simp only [AtomServedQ.acoins, chalsAJ8Z_of_ne δ χ (show (33 : ℕ) ≠ 37 by decide) (by decide),
      chalsAJ8Z_of_ne δ χ (show (34 : ℕ) ≠ 37 by decide) (by decide),
      chalsAJ8Z_of_ne δ χ (show (35 : ℕ) ≠ 37 by decide) (by decide),
      chalsAJ8Z_of_ne δ χ (show (36 : ℕ) ≠ 37 by decide) (by decide)]
  have houtA : ((AtomServedQ.acoins δ (chalsAJ8Z δ χ)).gamma, (AtomServedQ.acoins δ (chalsAJ8Z δ χ)).pole) ∉
      IOFailureEventW ((AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M'.pubsA
          (qA δ b Pb tr (chalsAJ8Z δ χ) M'.pubsA) ++ M'.wreqs).map (BalanceQ.liftRec (K := K) (L := 𝕂′)))
        (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M'.pubsA
          (qA δ b Pb tr (chalsAJ8Z δ χ) M'.pubsA))) := by
    rw [hac]
    refine LinkQ2J8.houtA_of_outside
      (withLiftC (RR4 δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg) (LL4 δ b L0 Pb skel hs hL)) hoC _ _
      rAX.1 rAX.2 ?_ ?_
    · refine le_trans (le_of_eq (congrArg List.length rAX.1.symm)) ?_
      have := RealAJ8.axReqsJ8_length δ b Pb tr
      have := hacc'.hbudV.2.2.1; have := hacc'.hbudV.2.2.2
      omega
    · refine le_trans (le_of_eq (congrArg List.length rAX.2.symm)) ?_
      rw [RealAJ8.axProvsJ8_length]; exact hacc'.hbudV.2.2.1
  have hcountA := hcountA_ofZ'' δ b Pb c χ M tr hacc'.hlenA
  -- #1.5: hXW
  have hfx := Lift40J8.fpx_out (LL4 δ b L0 Pb skel hs hL) (ListJ8C.outside40C _ _ hoC)
    (by show (RealVJ8.fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr).length ≤ r.W
        rw [RealVJ8.fxReqsJ8, walkXInternal_length]; exact hL.W)
    (by show (RealVJ8.fxProvsJ8 δ b Pb.nodesC Pb.orbitC tr).length ≤ 2 * r.D
        rw [RealVJ8.fxProvsJ8, liftWts_length]
        exact (cXRec_length δ b _ _ _ _ _).trans (by have := hB.x2; omega))
  have hXW := hXW_of_ioG δ b Pb c χ M' tr hacc hp64
    (by show Quad.mk _ (M.pubsC 2) (M.pubsC 3) = Quad.mk _ (M.pubsW 0) (M.pubsW 1)
        rw [hacc'.hfxC.1, hacc'.hfxC.2]) hfx
  -- the census
  have hG : ∀ pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2 ((cellT δ b Pb χ M' tr).map (·.b0))
      (AtomBigJ8.extB p (rAT b Pb tr)) ++ censusG Pb c),
      pr ∈ (RR4 δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg).D.prs tr := by
    intro pr hpr
    show pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2 (TraceJ8.rowsMJ8 Pb.nodesC Pb.orbitC tr) (extT8 b Pb tr) ++
      censusG Pb c)
    rw [rowsMJ8_eq_cellT δ b Pb χ M' tr]
    exact hpr
  have hext := LinkQ2J8.hext_of_rows (q := p) hBA hwout hmax
  have hy : Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 2) (chalsAJ8Z δ χ 3) ≠ 0 := by
    rw [chalsAJ8Z_of_ne δ χ (by omega) (by omega), chalsAJ8Z_of_ne δ χ (by omega) (by omega)]
    exact (outJ8_of_outside _ _ b hoC).atom_hz
  -- S1: `SmallU` at the reader (R3b), from the export consume of the #4 balance
  have hcs := AtomServedQ.consumeServedQ_of_balance δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M'.pubsA _
    hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA M'.wreqs hacc.hbalA houtA hcountA
  have hsU : ∀ k : Fin Pb.nA, SmallU (rAT (K := K) b Pb tr k) := by
    rw [← hE]
    exact ReaderR3bJ8.smallU_valReader hq hacc'.hnA62 hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA hserved hcs
  have hvp := AtomLeavesUJ8.hvp_of_mbU χ hq hpG hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA hacc.hnpA hy
    hserved hRA hsU hidxA hBA (fun k => hwRA k) hTout
  exact
    { rdX := rX
      budX := ⟨(congrArg List.length rX.1).le.trans bX.1, (congrArg List.length rX.2).le.trans bX.2⟩
      rdP := rP
      budP := ⟨(congrArg List.length rP.1).le.trans bP.1, (congrArg List.length rP.2).le.trans bP.2⟩
      rdS := rS
      budS := ⟨(congrArg List.length rS.1).le.trans bS.1, (congrArg List.length rS.2).le.trans bS.2⟩
      hcount := hcnt
      rdV := rV
      budV := ⟨lV.1.trans (by have := hacc'.hbudV.1; have := hB.x2; omega),
        lV.2.trans (by have := hacc'.hbudV.2.1; have := hB.x2; omega)⟩
      rdWC := L2.1
      rdWW := L2.2
      hext := hext
      hprs := fun pr hpr => hG pr (censusPairs_append_mem hpr)
      hvp := hvp
      hXW := hXW
      hHXW := AcceptsJ8ZHG.hHXW_of_acceptsZ δ b Pb c χ M' tr hacc hp64 hx hpp hss (hcnt .x)
      hRA := hRA
      hsA := hsU
      hidxA := hidxA
      hrn := by rw [← hE]; exact LinkQ2J8.hrn_valReader _
      hB := hBA
      hwRA := hwRA
      houtA := houtA
      hservedA := hserved
      hseedsV := AcceptsJ8ZS.hseedsV_of_outsideZ δ b _ Pb χ M' tr hoC
        (AcceptsJ8ZS.rowsAJ8_eq_atomTZ δ b Pb χ M' tr) hΛ
      hHXV := hHXV_ofZG δ b Pb c χ M' tr hacc rfl houtA hcountA
      hprsG := hG }

/-! ## 3. THE FINAL theorem -/

/-- The public layout bound `LayLe` at the empty skeleton, from the five public table sizes. -/
theorem layLe_ofG (Pb : PubJ8 p) (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A)
    (hLV : Pb.nV ≤ r.AW) : LayLe (layPb Pb [] (by simp)) r :=
  ⟨hLC, hLM, hLW, hLA, hLV⟩

open Classical in
/-- **THE residue-free J-8 bound.**  For every staged prover trace map `Q`, at the census corner:
`Pr_χ[(∃ M, AcceptsJ8''' … (Q χ) r g) ∧ ¬ HoldsN c] < 2^-155`, with NO `LinkJ8` premise — only statement binders:
the field pin (`hpG`, `hcK`), the corner / maxlen / leaves / registered-id / layout / census binders (`hr`, `hqM`,
`hk`, `hmax`, `hg`, `hLC … hLV`, `hnM`, `hreg`) and the faithful registry (`hRg`). -/
theorem probJ8NV_final [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q)
    (hpG : p = Nock.Atoms.p) (hcK : Fintype.card K = VclL.Events.cK)
    (hr : RowsLe r EncInjJ8.cornerC) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8' p K δ, AcceptsJ8'''' δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 :=
  RepriceJ8.probJ8X_lt_155_census32
    (AtomFpxJ8.withFpxV δ b
      (withLiftC (RR4 δ b (g := g + r.N) (R0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (P := 2 ^ 66))
          Pb c [] (by simp) (layLe_ofG Pb hLC hLM hLW hLA hLV) rfl hnM hreg)
        (LL4 δ b (L0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ)) Pb [] (by simp)
          (layLe_ofG Pb hLC hLM hLW hLA hLV)))
      Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA) Q hQ _ _
    (fun χ hacc hout => by
      obtain ⟨M, hM⟩ := hacc
      exact hsoundJ8XUG δ b Pb hRg c χ M (Q χ) _ _ hpG hqM hk hM hout hM.hbudV.2.2.2 hM.hbudV.2.2.1
        (wdV_view δ b Pb (Q χ) _ _)
        (linkXUG_of_R5 δ b Pb c χ M (Q χ) _ _ [] (by simp) (layLe_ofG Pb hLC hLM hLW hLA hLV) rfl hnM hreg hpG hr
          hg hmax hM hout))
    hcK hr (le_refl _) (RepriceJ8.g32_of_corner hr hg)

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8NV
