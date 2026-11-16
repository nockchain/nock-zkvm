/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/HbalJ9AL.lean

  **The S8 lists and `hbal` from `AcceptsJ9AL`.** The twin of `J9A/HbalJ9A.lean` with the ALU terms.
  * `extACL`, `provsACL`: the S8 wiring lists at the coins and the message, `HbalJ9A.extAC` / `provsAC` with the ALU
    lists of `RR49AL` inserted in the S8 order: `ext .x = (walkX ++ aluX) ++ jRd`,
    `ext .s = pinCons regs ++ (pinsP ++ axLimb ++ aluReg) ++ jCons`,
    `provs .s = jProv ++ (inc ++ walkV ++ (axTag ++ aluProv) ++ split)`.
  * `extACL_eq`, `provsACL_eq`: they ARE `RR49AL.extAL` / `provsAL` (the readout bridge of `XAL`).
  * The gated ALU sums (`aluOn` present: `AluSumAL`; absent: the empty lists and the zero terminals of `ALChipOK`):
    `aluXL_sum`, `aluSP_sum`, `aluFpL_sum`.  `sP` is boolean by the verifier's `preg` layout (`PregOK`).
  * `balJ9AL_frame`: `BalJ9A.balJ9A_frame` with the ALU export reads on `.x` (`hGx` with `pubALx`).
  * **`hbalAL`**: S8's `hbal : BalJ8 … (pubVJ9 …) provsACL extACL` from the `AcceptsJ9AL` fields alone, at
    `p = Nock.Atoms.p` (the ALU's field, `AluTeleAL`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.HbalJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.BalJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluSumAL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.HbalJ9AL

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
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceVSQ (mcoins)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (BalJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.BalXJ8 (provsX_sumQ provsP_sumQ)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 pad8_sum atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (byBal)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z chalsAJ8Z_agree)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (pubVJ9 rhoX_pubVJ9)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL (AcceptsJ9AL ALChipOK PregOK)
open Nock.NockVMROM.Thm54.VclL.Handle.ShareJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.JGenJ8 (JChipOK extX_sumQG)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Atoms (Fp)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (c4 c5 c6 c7)

noncomputable section

/-! ## 1. The S8 lists -/

section Lists
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The S8 externals at the coins and the message** (`HbalJ9A.extAC` + the ALU's coin-free lists). -/
def extACL (Pb : PubJ9AL p) (χ : Coins frameJ8 K) (M : MsgJ9AL' p K δ) (tr : TrJ9AL (ZMod p)) :
    (bl : Bal) → List (Fin (mOf bl) → K) :=
  byBal (β := fun bl => List (Fin (mOf bl) → K))
    ((ServeH.walkXReqs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (qW δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsW) ++ RR49AL.aluXL δ b Pb tr) ++
      jRd b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ))
    (if Pb.axOn then AxisChipJ9.axPathReqs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
      (qAX δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsX) else [])
    (pinCons (p := p) (K := K) Pb.regs Pb.idx ++
      (RR49AL.pinsP Pb ++ (if Pb.axOn then AxisChipJ9.axLimbReqs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
        (qAX δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsX) else []) ++ RR49AL.aluSL δ b Pb tr) ++
      jCons b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ))

/-- **The S8 providers at the coins and the message** (`HbalJ9A.provsAC` + the ALU's coin-free provides). -/
def provsACL (Pb : PubJ9AL p) (χ : Coins frameJ8 K) (M : MsgJ9AL' p K δ) (tr : TrJ9AL (ZMod p)) :
    (bl : Bal) → List ((Fin (mOf bl) → K) × K) :=
  byBal (β := fun bl => List ((Fin (mOf bl) → K) × K))
    (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC))
    (ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsW))
    (jProv b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ) ++
      (pad8 (atomIncProvs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
          (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)) ++
        pWA Pb.krootsV (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
          (qV δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsV)) ++
        ((if Pb.axOn then AxisChipJ9.axTagProvs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
          (qAX δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsX) else []) ++ RR49AL.aluPL δ b Pb tr) ++
        pSA Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS
          (qSP δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsS)))

/-- **`extACL` is `RR49AL.extAL`** (the readout bridge). -/
theorem extACL_eq (Pb : PubJ9AL p) (χ : Coins frameJ8 K) (M : MsgJ9AL' p K δ) (tr : TrJ9AL (ZMod p)) (bl : Bal) :
    extACL δ b Pb χ M tr bl = RR49AL.extAL δ b Pb tr bl := by
  obtain ⟨hL, hP, hT⟩ := axLists_qAX δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsX
  have hJ := ReadIOJ8.jLists_congr b Pb.nodesJ Pb.orbitJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ (fun _ => (0 : K)) (fun _ => 0)
    (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ) tr.J Pb.lay
    (by simp only [TraceJ8.widthW_eq, TraceJ8.widthJ_eq, TraceJ8.widthA_eq, TraceJ8.widthV_eq, TraceJ8.widthM_eq]; omega)
    (by norm_num) (fun _ _ _ _ => rfl)
  cases bl
  · show (_ ++ _) ++ _ = (_ ++ _) ++ _
    rw [(DescentVSQ.walkLists_congrW b Pb.nodesW Pb.orbitW Pb.orbitW _ _ (fun _ => (0 : K)) (fun _ => 0)
      (qW δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsW) tr.W
      (by simp only [TraceJ8.widthW_eq, TraceJ8.widthJ_eq, TraceJ8.widthA_eq, TraceJ8.widthV_eq, TraceJ8.widthM_eq]; omega)
      (by norm_num) (fun _ _ _ _ => rfl)).1, hJ.1]
  · show (if Pb.axOn then AxisChipJ9.axPathReqs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
      (qAX δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsX) else []) =
        (if Pb.axOn then axPathReqsOf b Pb.toPubJ9A tr.toTrJ9A else [])
    rw [hP]
  · show _ ++ (_ ++ (if Pb.axOn then AxisChipJ9.axLimbReqs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
        (qAX δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsX) else []) ++ _) ++ _ =
      _ ++ (_ ++ (if Pb.axOn then axLimbReqsOf b Pb.toPubJ9A tr.toTrJ9A else []) ++ _) ++ _
    rw [hL, hJ.2.1]

/-- **`provsACL` is `RR49AL.provsAL`**. -/
theorem provsACL_eq (Pb : PubJ9AL p) (χ : Coins frameJ8 K) (M : MsgJ9AL' p K δ) (tr : TrJ9AL (ZMod p)) (bl : Bal) :
    provsACL δ b Pb χ M tr bl = RR49AL.provsAL δ b Pb tr bl := by
  obtain ⟨hL, hP, hT⟩ := axLists_qAX δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsX
  cases bl
  · exact ReadIOJ8.cellProvsW_congr b Pb.nodesC Pb.orbitC Pb.orbitC _ _ (fun _ => (0 : K)) (fun _ => 0)
      (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC) tr.M (by rw [TraceJ8.widthM_eq]; omega) (by norm_num)
      (fun _ _ _ _ => rfl)
  · exact (DescentVSQ.walkLists_congrW b Pb.nodesW Pb.orbitW Pb.orbitW _ _ (fun _ => (0 : K)) (fun _ => 0)
      (qW δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsW) tr.W
      (by simp only [TraceJ8.widthW_eq, TraceJ8.widthJ_eq, TraceJ8.widthA_eq, TraceJ8.widthV_eq, TraceJ8.widthM_eq]; omega)
      (by norm_num) (fun _ _ _ _ => rfl)).2
  · have hS' : pSA Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS
        (qSP δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsS) =
        (if Pb.spOn then splitProvsOf b Pb.toPubJ9A tr.toTrJ9A else []) := by
      unfold pSA; rw [splitProvs_qSP]
    show _ ++ (pad8 _ ++ pWA _ _ ++ (_ ++ _) ++ pSA _ _ _ _ _ _ _ _) = _ ++ (pad8 _ ++ _ ++ (_ ++ _) ++ _)
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

/-! ## 2. The gated ALU sums (at the ALU's field `Fp`) -/

section ALU
variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] [Fintype K] [DecidableEq K] (δ : Fp)
  [Fact (¬ IsSquare (algebraMap Fp K δ))] (b : Basis (Fin 3) Fp K)

local notation "𝕂′" => Quad (algebraMap Fp K δ)

/-- The ALU challenge vector's handle coins are the compute coins. -/
theorem kappaAL (χ : Coins frameJ8 K) :
    AluSumAL.κ δ (AluSZChipJ9.chalsALJ8 δ χ) = TeleCQ.coinsCV b δ (chalVJ8 b χ) :=
  (mcoins_of_agree δ χ (AluSZChipJ9.chalsALJ8 δ χ) (fun j h1 h2 => by
    rw [AluSZChipJ9.chalsALJ8_of_lt δ χ (by omega)]; exact chalsAJ8Z_agree δ χ j h1 h2)).trans
    (coinsCV_J8 δ b χ).symm

/-- **`sP` is boolean** at every ALU row: the column is the verifier's `preg` preprocessing `preL 0` (`hbind`), which
`PregOK` lays out as `1` on the first `|prims|` rows and `0` elsewhere. -/
theorem sP_bool {Pb : PubJ9AL Nock.Atoms.p} {tr : TrJ9AL Fp} {chals pubs : ℕ → K}
    (hbind : (AluSZChipJ9.aluSZChipJ9 δ b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL).BindsPreprocessing
      (qAL δ b Pb tr chals pubs))
    (hpre : PregOK Pb.nodesL Pb.prims Pb.preL) (i : Fin Pb.nL) :
    AluTeleAL.fv b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL (qAL δ b Pb tr chals pubs) AluSZChipJ9.sP i = 0 ∨
      AluTeleAL.fv b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL (qAL δ b Pb tr chals pubs) AluSZChipJ9.sP i = 1 := by
  have h2 : qAL δ b Pb tr chals pubs ⟨2, by rw [AluSZChipJ9.aluSZ_width_eq]; omega⟩ = Pb.preL 0 :=
    hbind ⟨2, by show 2 < 5; omega⟩
  show (Reify.envOfTrace (qAL δ b Pb tr chals pubs) Pb.orbitL.ω (Pb.nodesL i) (slotVal b 94 chals)
      (slotVal b 94 pubs)).trace 2 = 0 ∨ (Reify.envOfTrace (qAL δ b Pb tr chals pubs) Pb.orbitL.ω (Pb.nodesL i)
      (slotVal b 94 chals) (slotVal b 94 pubs)).trace 2 = 1
  rw [envOfTrace_trace _ _ _ _ _ (by rw [AluSZChipJ9.aluSZ_width_eq]; omega), h2, (hpre.2 i).1]
  split_ifs <;> simp

/-- **The ALU export sum, gated** (`0` when absent). -/
theorem aluXL_sum {Pb : PubJ9AL Nock.Atoms.p} {tr : TrJ9AL Fp} (χ : Coins frameJ8 K) {pubsL : ℕ → K}
    (hALk : ALChipOK δ b Pb.aluOn Pb.prims Pb.hnL Pb.nodesL Pb.orbitL Pb.preL (AluSZChipJ9.chalsALJ8 δ χ) pubsL
      (qAL δ b Pb tr (AluSZChipJ9.chalsALJ8 δ χ) pubsL)) :
    ((RR49AL.aluXL δ b Pb tr).map fun r =>
        (compress (TeleCQ.coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum =
      Quad.mk _ (pubsL AluSZChipJ9.pubALx) (pubsL (AluSZChipJ9.pubALx + 1)) := by
  rcases hALk with ⟨hon, hsat, hbind, hinj, hadj, -, -⟩ | ⟨hoff, -, -, -, -, -, h1, h2⟩
  · rw [RR49AL.aluXL, if_pos hon, ← kappaAL δ b χ]
    exact AluSumAL.aluX_sumL δ b Pb tr _ pubsL hsat hbind hinj hadj
  · rw [RR49AL.aluXL, if_neg (by simp [hoff]), h1, h2, Quad.mk_zero']
    simp

/-- **The ALU service sum, gated**: Σ `hdr` consumes − Σ (`preg` + jet) provides = `pubALs` (`0` when absent). -/
theorem aluSP_sum {Pb : PubJ9AL Nock.Atoms.p} {tr : TrJ9AL Fp} (χ : Coins frameJ8 K) {pubsL : ℕ → K}
    (hALk : ALChipOK δ b Pb.aluOn Pb.prims Pb.hnL Pb.nodesL Pb.orbitL Pb.preL (AluSZChipJ9.chalsALJ8 δ χ) pubsL
      (qAL δ b Pb tr (AluSZChipJ9.chalsALJ8 δ χ) pubsL)) :
    ((RR49AL.aluSL δ b Pb tr).map fun r =>
        (compress (TeleCQ.coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum -
      ((RR49AL.aluPL δ b Pb tr).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (TeleCQ.coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) q.1))⁻¹).sum =
      Quad.mk _ (pubsL AluSZChipJ9.pubALs) (pubsL (AluSZChipJ9.pubALs + 1)) := by
  rcases hALk with ⟨hon, hsat, hbind, hinj, hadj, -, hpre⟩ | ⟨hoff, -, -, -, h1, h2, -, -⟩
  · rw [RR49AL.aluSL, RR49AL.aluPL, if_pos hon, if_pos hon, ← kappaAL δ b χ]
    exact AluSumAL.aluS_sumL δ b Pb tr _ pubsL hsat hbind hinj hadj (sP_bool δ b hbind hpre)
  · rw [RR49AL.aluSL, RR49AL.aluPL, if_neg (by simp [hoff]), if_neg (by simp [hoff]), h1, h2, Quad.mk_zero']
    simp

/-- **The ALU validity sum, gated**, at the validity coins `γV = (χ₄, χ₆)`, `ρV = (χ₅, χ₇)` (`0` when absent). -/
theorem aluFpL_sum {Pb : PubJ9AL Nock.Atoms.p} {tr : TrJ9AL Fp} (χ : Coins frameJ8 K) {pubsL : ℕ → K}
    (hALk : ALChipOK δ b Pb.aluOn Pb.prims Pb.hnL Pb.nodesL Pb.orbitL Pb.preL (AluSZChipJ9.chalsALJ8 δ χ) pubsL
      (qAL δ b Pb tr (AluSZChipJ9.chalsALJ8 δ χ) pubsL)) :
    ((RR49AL.aluFpL δ b Pb tr χ).map fun r => (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
      Quad.mk _ (pubsL AluSZChipJ9.pubALv) (pubsL (AluSZChipJ9.pubALv + 1)) := by
  rcases hALk with ⟨hon, hsat, hbind, hinj, hadj, -, -⟩ | ⟨hoff, -, h1, h2, -, -, -, -⟩
  · rw [RR49AL.aluFpL, if_pos hon]
    exact AluSumAL.aluV_sumL δ b Pb tr _ pubsL hsat hbind hinj hadj _ _
      (Chips.ChipRAP.chalsOK_mono δ (by norm_num : 5 ≤ 11) (AluSZChipJ9.chalsALJ8_ok δ χ))
  · rw [RR49AL.aluFpL, if_neg (by simp [hoff]), h1, h2, Quad.mk_zero']
    simp

end ALU

/-! ## 3. The frame and `hbal` -/

section Frame
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))] {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`BalJ9A.balJ9A_frame` with the ALU export reads on `.x`** (`aluX`, sum `TaluX`, `hGx` with `TaluX`). -/
theorem balJ9AL_frame (χ : SVFrame.Coins FrameJ8.frameJ8 K) (c : P8PublicClaim) (m : FrameVS.ClaimMsgVS)
    (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → ZMod p)
    (orbitC : StrictOrbitDomain (ZMod p) 3 hC) (chalsC pubsC : ℕ → K)
    (QC : Fin (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.w → (ZMod p)[X])
    (hsatC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.Satisfies QC)
    (hbindC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    (hchC : ∀ j, 33 ≤ j → j ≤ 36 → chalsC j = chalsMJ8 δ χ j)
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hsatW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hF : GeneratedField.PrimeFieldElems (ZMod p)) (hp64 : 64 ≤ ringChar (ZMod p))
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    (hchW : ∀ j, 33 ≤ j → j ≤ 36 → chalsW j = chalsMJ8 δ χ j)
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).rap.w → (ZMod p)[X])
    (hJk : JChipOK δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (aluX : List (Fin 5 → K)) (TaluX : 𝕂′)
    (hAX : (aluX.map fun r => (compress (TeleCQ.coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum = TaluX)
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    (hextX : ext .x = (ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++ aluX) ++
      jRd b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (hprovP : provs .p = ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW)
    (TextP : 𝕂′)
    (hP_ext : ((ext .p).map fun r =>
      (compress (TeleCQ.coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum = TextP)
    (TprovS TextS : 𝕂′)
    (hS_prov : ((provs .s).map fun q => algebraMap K 𝕂′ q.2 *
      (compress (TeleCQ.coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) q.1))⁻¹).sum = TprovS)
    (hS_ext : ((ext .s).map fun r =>
      (compress (TeleCQ.coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum = TextS)
    (hGx : ρ 3 + (Quad.mk _ (pubsW WalkHQ.pubXQ) (pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (pubsJ 2) (pubsJ 3) + TaluX) =
      Quad.mk _ (pubsC CellHQ.pubHQ) (pubsC (CellHQ.pubHQ + 1)))
    (hGp : ρ 4 + TextP = Quad.mk _ (pubsW WalkHQ.pubPQ) (pubsW (WalkHQ.pubPQ + 1)))
    (hGs : ρS + TextS = TprovS) :
    BalJ8 (b := b) (δ := δ) (chalV := chalVJ8 b χ) (pubVal := pubVJ9 δ b c m ρ ρS χ) provs ext := by
  have hcv := coinsCV_J8 δ b χ
  intro bl
  rw [rhoX_pubVJ9 δ b c m ρ ρS χ bl]
  cases bl with
  | x =>
    have hx1 := extX_sumQG δ b _ kroots hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW
        ((mcoins_of_agree δ χ chalsW hchW).trans hcv.symm) nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ hJk
        ((coinsJX_J8 δ χ).trans hcv.symm)
    have hx2 := provsX_sumQ δ b _ hnC nodesC orbitC chalsC pubsC QC hsatC hbindC hinjC hadjC
        ((mcoins_of_agree δ χ chalsC hchC).trans hcv.symm)
    have key : ∀ (f : (Fin 5 → K) → 𝕂′) (W A J : List (Fin 5 → K)),
        (((W ++ A) ++ J).map f).sum = ((W ++ J).map f).sum + (A.map f).sum := by
      intros; simp only [List.map_append, List.sum_append]; ring
    rw [rhoX_x_J8, hextX, hprovX]
    refine Eq.trans ?_ (hGx.trans hx2.symm)
    exact congrArg (ρ 3 + ·) ((key _ _ _ _).trans (congrArg₂ (· + ·) hx1 hAX))
  | p =>
    have hp2 := provsP_sumQ δ b _ kroots hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW
        ((mcoins_of_agree δ χ chalsW hchW).trans hcv.symm)
    rw [rhoX_p_J8, hP_ext, hprovP]
    convert hGp using 1
    exact hp2
  | s =>
    rw [rhoX_s_J8, hS_ext, hS_prov]
    exact hGs

end Frame

section Bal
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **S8's `hbal` from `AcceptsJ9AL`** (at the ALU's field `p = Nock.Atoms.p`). -/
theorem hbalAL {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {r : RowsJ9AL} {g : ℕ}
    (hacc : AcceptsJ9AL δ b Pb Rg c χ M tr r g) (hp64 : 64 ≤ ringChar (ZMod p)) (hpG : p = Nock.Atoms.p) :
    BalJ8 (b := b) (δ := δ) (chalV := chalVJ8 b χ) (pubVal := pubVJ9 δ b c M.m M.ρ M.ρS χ)
      (provsACL δ b Pb χ M tr) (extACL δ b Pb χ M tr) := by
  subst hpG
  have hcv := coinsCV_J8 δ b χ
  have hcM : (⟨Quad.mk _ (chalsMJ8 δ χ 33) (chalsMJ8 δ χ 35), Quad.mk _ (chalsMJ8 δ χ 34) (chalsMJ8 δ χ 36)⟩ :
      IOCoins _) = TeleCQ.coinsCV b δ (chalVJ8 b χ) :=
    (mcoins_of_agree δ χ (chalsMJ8 δ χ) (fun _ _ _ => rfl)).trans hcv.symm
  have hcA : (⟨Quad.mk _ (chalsAJ8Z δ χ 33) (chalsAJ8Z δ χ 35), Quad.mk _ (chalsAJ8Z δ χ 34) (chalsAJ8Z δ χ 36)⟩ :
      IOCoins _) = TeleCQ.coinsCV b δ (chalVJ8 b χ) :=
    (mcoins_of_agree δ χ (chalsAJ8Z δ χ) (chalsAJ8Z_agree δ χ)).trans hcv.symm
  have hcJ : Nock.Jet.RapJetJ8.coinsJ δ (chalsJJ8 χ) = TeleCQ.coinsCV b δ (chalVJ8 b χ) :=
    (coinsJ_J8 δ χ).trans hcv.symm
  -- the share sums at the compute coins
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
  have hAS := aluSP_sum δ b χ hacc.hALk
  have hAX := aluXL_sum δ b χ hacc.hALk
  -- the `.s` balance: `hGS` with the primitive pins and the ALU service terminal
  set κ := TeleCQ.coinsCV b δ (chalVJ8 b χ) with hκ
  have hGS := hacc.hGS
  have hsP : ((RR49AL.pinsP (p := Nock.Atoms.p) (K := K) Pb).map fun r => (compress κ (liftRec (L := Quad (algebraMap Fp K δ)) r))⁻¹).sum =
      ((AcceptsJ9AL.pinRgP (p := Nock.Atoms.p) (K := K) Pb).map fun r =>
        (compress κ (liftRec (L := Quad (algebraMap Fp K δ)) r))⁻¹).sum +
      ((AcceptsJ9AL.pinOpP (p := Nock.Atoms.p) (K := K) Pb).map fun r =>
        (compress κ (liftRec (L := Quad (algebraMap Fp K δ)) r))⁻¹).sum := by
    rw [RR49AL.pinsP, List.map_append, List.sum_append]
  have hGs := balS_J9A κ M.ρS (pinCons (p := Nock.Atoms.p) (K := K) Pb.regs Pb.idx)
    (RR49AL.pinsP Pb ++ (if Pb.axOn then AxisChipJ9.axLimbReqs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
        (qAX δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsX) else []) ++ RR49AL.aluSL δ b Pb tr)
    (jCons b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ))
    (jProv b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ))
    (pad8 (atomIncProvs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
      (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)))
    (pWA Pb.krootsV (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
      (qV δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsV)))
    ((if Pb.axOn then AxisChipJ9.axTagProvs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
      (qAX δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsX) else []) ++ RR49AL.aluPL δ b Pb tr)
    (pSA Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS
      (qSP δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsS))
    (Quad.mk _ (M.pubsJ 0) (M.pubsJ 1))
    (Quad.mk _ (M.pubsA AtomChipHQ.pubMI) (M.pubsA (AtomChipHQ.pubMI + 1)))
    (Quad.mk _ (M.pubsV WalkHQ.pubPQ) (M.pubsV (WalkHQ.pubPQ + 1)))
    (((RR49AL.pinsP (p := Nock.Atoms.p) (K := K) Pb).map fun r => (compress κ (liftRec (L := Quad (algebraMap Fp K δ)) r))⁻¹).sum +
      Quad.mk _ (M.pubsX AxisChipJ9.pubAXs) (M.pubsX (AxisChipJ9.pubAXs + 1)) +
      Quad.mk _ (M.pubsL AluSZChipJ9.pubALs) (M.pubsL (AluSZChipJ9.pubALs + 1)))
    (Quad.mk _ (M.pubsS SplitChipJ9.pubSPs) (M.pubsS (SplitChipJ9.pubSPs + 1)))
    (by rw [hsP]; linear_combination hGS) h3 hI8 hW
    (by simp only [List.map_append, List.sum_append]; linear_combination hX + hAS) hS
  exact balJ9AL_frame χ c M.m M.ρ M.ρS Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _
    hacc.hsatC hacc.hbindC hacc.hinjC hacc.hadjC (fun _ _ _ => rfl)
    Pb.kroots Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _ hacc.hsatW hacc.hbindW
    (GeneratedField.primeFieldElems_zmod Nock.Atoms.p) hp64 hacc.hinjW hacc.hadjW (fun _ _ _ => rfl)
    Pb.nodesJ Pb.orbitJ M.pubsJ Pb.lay _ hacc.hJk (RR49AL.aluXL δ b Pb tr) _ hAX rfl rfl rfl _ hXP _ _ rfl rfl
    hacc.hGx hacc.hGp hGs

end Bal

end

end Nock.NockVMROM.Thm54.VclL.Handle.HbalJ9AL

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.HbalJ9AL
#print axioms extACL_eq
#print axioms provsACL_eq
#print axioms aluXL_sum
#print axioms aluSP_sum
#print axioms aluFpL_sum
#print axioms balJ9AL_frame
#print axioms hbalAL
end Axioms
