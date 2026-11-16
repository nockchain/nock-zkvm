/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALClosed.lean

  **J-9 AL general completeness, close.**

  * `BRun9AL`: the honest J-9 AL record of a run, `⟨t, hgen, PbL, MAL, trAL, rowsAL, gL, badAL⟩`, at the
    template table the caller passes (the capstone passes `rtP Rt0 prims`).
  * `obligations_of_runAL`: every field of `ComplJ9ALObligations` at `BRun9AL`.  Sources:
    the compute / walk / axis / split / atom-walk / claim fields from the J-9 A record `BA` through `goodAL_BA`;
    the cell / J / atom tables from the overlay record `B8L`; `hGS`; `hGx hsumC' hbalA' hvalA0 hfxC
    hfxA`; the static, census, primitive, length and budget fields; `hALk wt staged fig`.
  * **`complJ9AL_closed`**: `complJ9AL_of_obligations` at `BRun9AL` over `rtP Rt prims`, with `RowsLe31AL`
    discharged from `h31A` and `h31L`.  Binders: `hpG hax9 hop5 hleaf hwalk9 hwalkA` (at `rtP Rt prims`), the
    prim-aware `hRt hregAx`, `hnd hprim h31A h31L hlimb hnoDec`.  `h31L` is the STRICT ALU size `aluLen < 2^31`
    (the ALU table has `nL = aluLen + 1` rows and the figure's `RowsLe31AL` needs `nL ≤ 2^31`).
  * `complJ9AL_closed_of`: the same from `CompiledByP` (no `hRt`, `hregAx`, `hprim`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALObl
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALRun
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALOfAlu
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALTables
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALJ
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALBalS
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALBalX
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALBalV
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALBalV2
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALBalA
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALStatic
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AClosed
import Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALClosed

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ ProgOp5OK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A WalkDepthOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (Rows31A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (rtP j9alDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALObl (HonestJ9AL ComplJ9ALObligations RowsLe31AL
  complJ9AL_of_obligations)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL (AcceptsJ9AL)
open Nock.Jet.Prim (PrimOp primSpec)

-- the opens of ComplJ9ALObl (the field statements are copied from there)
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
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL toHQ)
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (computeChipVCLHX9)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9V (AcceptsJ9V)
open Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ prob_exists_le RowsLe31)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AcceptsJ9A AXChipOK SPChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AObl (HonestJ9A RowsLe31A)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL (AcceptsJ9AL ALChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 (aluSZChipJ9)
open Nock.Jet.Prim (PrimOp)

noncomputable section

section Rec
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (prims : List (ℕ × PrimOp))

/-- **The honest J-9 AL record of a run**. -/
def BRun9AL (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    HonestJ9AL p K δ Rg fuel s f r :=
  { t := t
    hgen := hgen
    Pb := ComplJ9ALRun.PbL δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)
    M := ComplJ9ALRun.MAL δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)
    tr := ComplJ9ALRun.trAL δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)
    rows := ComplJ9ALRun.rowsAL δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)
    g := ComplJ9ALRun.gL δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)
    bad := ComplJ9ALRun.badAL δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) }

/-- Generic summand swaps (first-order, so `exact` never unfolds the honest record). -/
theorem swap_last {M : Type} [AddCommGroup M] {a d X Y : M} (e : Y = X) (h : a + X = d) : a + Y = d := by
  rw [e]; exact h

theorem swap_first {M : Type} [AddCommGroup M] {s d X Y : M} (e : Y = X) (h : X + s = d) : Y + s = d := by
  rw [e]; exact h

theorem swap_mid {M : Type} [AddCommGroup M] {a b c d X Y : M} (e : Y = X) (h : a + (b + c + X) = d) :
    a + (b + c + Y) = d := by
  rw [e]; exact h

/-- Read-backs of the ALU publics at the three terminals. -/
theorem pubsL_v (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ)
      (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsL (AluSZChipJ9.pubALv))
      (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsL (AluSZChipJ9.pubALv + 1)) =
    ComplJ9ALRun.SV δ Rt hgen prims (ComplJ9ALRun.nLRun (K := K) δ Rt hgen prims) χ := by
  show Quad.mk _ (ComplJ9ALRun.pubsLOf δ Rt hgen prims χ AluSZChipJ9.pubALv)
    (ComplJ9ALRun.pubsLOf δ Rt hgen prims χ (AluSZChipJ9.pubALv + 1)) = _
  simp only [ComplJ9ALRun.pubsLOf, AluSZChipJ9.pubALv]
  exact ComplJ8Of.pub2_mk2 δ _ 0 rfl

theorem pubsL_s (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ)
      (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsL (AluSZChipJ9.pubALs))
      (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsL (AluSZChipJ9.pubALs + 1)) =
    ComplJ9ALRun.SS δ Rt hgen prims (ComplJ9ALRun.nLRun (K := K) δ Rt hgen prims) χ := by
  show Quad.mk _ (ComplJ9ALRun.pubsLOf δ Rt hgen prims χ AluSZChipJ9.pubALs)
    (ComplJ9ALRun.pubsLOf δ Rt hgen prims χ (AluSZChipJ9.pubALs + 1)) = _
  simp only [ComplJ9ALRun.pubsLOf, AluSZChipJ9.pubALs]
  norm_num
  exact ComplJ8Of.pub2_mk2 δ _ 2 rfl

theorem pubsL_x (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ)
      (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsL (AluSZChipJ9.pubALx))
      (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsL (AluSZChipJ9.pubALx + 1)) =
    ComplJ9ALRun.SX δ Rt hgen prims (ComplJ9ALRun.nLRun (K := K) δ Rt hgen prims) χ := by
  show Quad.mk _ (ComplJ9ALRun.pubsLOf δ Rt hgen prims χ AluSZChipJ9.pubALx)
    (ComplJ9ALRun.pubsLOf δ Rt hgen prims χ (AluSZChipJ9.pubALx + 1)) = _
  simp only [ComplJ9ALRun.pubsLOf, AluSZChipJ9.pubALx]
  norm_num
  exact ComplJ8Of.pub2_mk2 δ _ 4 rfl

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem hlenL_of (χ : Coins frameJ8 K) :
    (ComplJ9ALRun.tbR δ Rt hgen prims (AluPoles.yOf δ χ)).length ≤ ComplJ9ALRun.nLRun (K := K) δ Rt hgen prims := by
  rw [ComplJ9ALRun.tbR_length]; simp only [ComplJ9ALRun.nLRun]; omega

theorem hnLle_of (h31L : ComplJ9ALRun.aluLen (K := K) δ Rt hgen prims < 2 ^ 31) :
    ComplJ9ALRun.nLRun (K := K) δ Rt hgen prims ≤ 2 ^ 31 := by
  simp only [ComplJ9ALRun.nLRun]; omega
/-- Replace the cell, J and atom layout fields of `P` by those of `Q`. -/
def updFrom (P Q : PubJ8 p) : PubJ8 p :=
  { P with
    hC := Q.hC,
    nC := Q.nC,
    hnC := Q.hnC,
    nodesC := Q.nodesC,
    orbitC := Q.orbitC,
    hJ := Q.hJ,
    nJ := Q.nJ,
    nodesJ := Q.nodesJ,
    orbitJ := Q.orbitJ,
    lay := Q.lay,
    hA := Q.hA,
    nA := Q.nA,
    hnA := Q.hnA,
    nodesA := Q.nodesA,
    orbitA := Q.orbitA,
    Rt := Q.Rt,
    regs := Q.regs,
    ids := Q.ids,
    idx := Q.idx,
    rk := Q.rk }

def updFrom9 (P : PubJ9A p) (Q : PubJ8 p) : PubJ9A p := { P with toPubJ8 := updFrom P.toPubJ8 Q }

theorem cellL {P P' Q : PubJ8 p} {tr' trQ : TrJ8 (ZMod p)} (chals pubs pubs' : ℕ → K)
    (hP : P' = updFrom P Q) (hT : tr'.M = trQ.M) (hp : pubs' = pubs)
    (H : (CellTwinKW.cellChipHQKW δ b Q.hnC Q.nodesC Q.orbitC chals pubs).rap.Satisfies (qM δ b Q trQ chals pubs) ∧
      (CellTwinKW.cellChipHQKW δ b Q.hnC Q.nodesC Q.orbitC chals pubs).BindsPreprocessing (qM δ b Q trQ chals pubs)) :
    (CellTwinKW.cellChipHQKW δ b P'.hnC P'.nodesC P'.orbitC chals pubs').rap.Satisfies (qM δ b P' tr' chals pubs') ∧
      (CellTwinKW.cellChipHQKW δ b P'.hnC P'.nodesC P'.orbitC chals pubs').BindsPreprocessing
        (qM δ b P' tr' chals pubs') := by
  subst hP
  subst pubs'
  have e : qM δ b (updFrom P Q) tr' chals pubs = qM δ b Q trQ chals pubs := by
    funext j
    show tr'.M _ = trQ.M _
    rw [hT] <;> rfl
  rw [e]
  exact H

theorem jL {P P' Q : PubJ8 p} {tr' trQ : TrJ8 (ZMod p)} (chals pubs pubs' : ℕ → K)
    (hP : P' = updFrom P Q) (hT : tr'.J = trQ.J) (hp : pubs' = pubs)
    (H : JGenJ8.JChipOK δ b Q.nodesJ Q.orbitJ chals pubs Q.lay (qJ δ b Q trQ chals pubs)) :
    JGenJ8.JChipOK δ b P'.nodesJ P'.orbitJ chals pubs' P'.lay (qJ δ b P' tr' chals pubs') := by
  subst hP
  subst pubs'
  have e : qJ δ b (updFrom P Q) tr' chals pubs = qJ δ b Q trQ chals pubs := by
    funext j
    show tr'.J _ = trQ.J _
    rw [hT] <;> rfl
  rw [e]
  exact H

theorem walkL {P P' Q : PubJ8 p} {tr tr' : TrJ8 (ZMod p)} (chals pubs pubs' : ℕ → K)
    (hP : P' = updFrom P Q) (hT : tr'.W = tr.W) (hp : pubs' = pubs)
    (H : (WalkJ8.walkChipJ8 δ P.kroots b P.hnW P.nodesW P.orbitW chals pubs).rap.Satisfies (qW δ b P tr chals pubs) ∧
      (WalkJ8.walkChipJ8 δ P.kroots b P.hnW P.nodesW P.orbitW chals pubs).BindsPreprocessing
        (qW δ b P tr chals pubs)) :
    (WalkJ8.walkChipJ8 δ P'.kroots b P'.hnW P'.nodesW P'.orbitW chals pubs').rap.Satisfies
        (qW δ b P' tr' chals pubs') ∧
      (WalkJ8.walkChipJ8 δ P'.kroots b P'.hnW P'.nodesW P'.orbitW chals pubs').BindsPreprocessing
        (qW δ b P' tr' chals pubs') := by
  subst hP
  subst pubs'
  have e : qW δ b (updFrom P Q) tr' chals pubs = qW δ b P tr chals pubs := by
    funext j
    show tr'.W _ = tr.W _
    rw [hT] <;> rfl
  rw [e]
  exact H

theorem awL {P P' Q : PubJ8 p} {tr tr' : TrJ8 (ZMod p)} (chals pubs pubs' : ℕ → K)
    (hP : P' = updFrom P Q) (hT : tr'.V = tr.V) (hp : pubs' = pubs)
    (H : AcceptsJ8V.AWChipOK δ b P.krootsV P.hnV P.nodesV P.orbitV chals pubs (qV δ b P tr chals pubs)) :
    AcceptsJ8V.AWChipOK δ b P'.krootsV P'.hnV P'.nodesV P'.orbitV chals pubs' (qV δ b P' tr' chals pubs') := by
  subst hP
  subst pubs'
  have e : qV δ b (updFrom P Q) tr' chals pubs = qV δ b P tr chals pubs := by
    funext j
    show tr'.V _ = tr.V _
    rw [hT] <;> rfl
  rw [e]
  exact H

theorem xL {P P' : PubJ9A p} {Q : PubJ8 p} {tr tr' : TrJ9A (ZMod p)} (chals pubs pubs' : ℕ → ZMod p)
    (hP : P' = updFrom9 P Q) (hT : tr'.C = tr.C) (hp : pubs' = pubs)
    (H : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 P.hn P.nodes b δ chals pubs P.orbit)
      (qX9 δ b P tr chals pubs)) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 P'.hn P'.nodes b δ chals pubs' P'.orbit)
      (qX9 δ b P' tr' chals pubs') := by
  subst hP
  subst pubs'
  have e : qX9 δ b (updFrom9 P Q) tr' chals pubs = qX9 δ b P tr chals pubs := by
    funext j
    show tr'.C _ = tr.C _
    rw [hT] <;> rfl
  rw [e]
  exact H

theorem PbL_toPubJ8_eq (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ8 =
      updFrom (ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).Pb.toPubJ8
        (ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).Pb := rfl

theorem PbL_toPubJ9A_eq (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ9A =
      updFrom9 (ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).Pb
        (ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).Pb := rfl


theorem mixM_eq (χ : Coins frameJ8 K) (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    (BRun9AL δ b Rt hgen prims hpG h31A).M χ =
    { toMsgJ9A' := { ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ) with
        pubsC := ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ).pubsC
        pubsJ := ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ).pubsJ
        pubsA := ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ).pubsA }
      pubsL := ComplJ9ALRun.pubsLOf δ Rt hgen prims χ } := rfl

theorem mixM_C (M : MsgJ9A' p K δ) (N : MsgJ8' p K δ) (pl : ℕ → K) :
    ({ toMsgJ9A' := { M with pubsC := N.pubsC, pubsJ := N.pubsJ, pubsA := N.pubsA }, pubsL := pl } : MsgJ9AL' p K δ).pubsC = N.pubsC := rfl
theorem mixM_J (M : MsgJ9A' p K δ) (N : MsgJ8' p K δ) (pl : ℕ → K) :
    ({ toMsgJ9A' := { M with pubsC := N.pubsC, pubsJ := N.pubsJ, pubsA := N.pubsA }, pubsL := pl } : MsgJ9AL' p K δ).pubsJ = N.pubsJ := rfl
theorem mixM_W (M : MsgJ9A' p K δ) (N : MsgJ8' p K δ) (pl : ℕ → K) :
    ({ toMsgJ9A' := { M with pubsC := N.pubsC, pubsJ := N.pubsJ, pubsA := N.pubsA }, pubsL := pl } : MsgJ9AL' p K δ).pubsW = M.pubsW := rfl
theorem mixM_V (M : MsgJ9A' p K δ) (N : MsgJ8' p K δ) (pl : ℕ → K) :
    ({ toMsgJ9A' := { M with pubsC := N.pubsC, pubsJ := N.pubsJ, pubsA := N.pubsA }, pubsL := pl } : MsgJ9AL' p K δ).pubsV = M.pubsV := rfl
theorem mixM_m (M : MsgJ9A' p K δ) (N : MsgJ8' p K δ) (pl : ℕ → K) :
    ({ toMsgJ9A' := { M with pubsC := N.pubsC, pubsJ := N.pubsJ, pubsA := N.pubsA }, pubsL := pl } : MsgJ9AL' p K δ).m = M.m := rfl
theorem mixM_rho (M : MsgJ9A' p K δ) (N : MsgJ8' p K δ) (pl : ℕ → K) :
    ({ toMsgJ9A' := { M with pubsC := N.pubsC, pubsJ := N.pubsJ, pubsA := N.pubsA }, pubsL := pl } : MsgJ9AL' p K δ).ρ = M.ρ := rfl
theorem mixM_rhoS (M : MsgJ9A' p K δ) (N : MsgJ8' p K δ) (pl : ℕ → K) :
    ({ toMsgJ9A' := { M with pubsC := N.pubsC, pubsJ := N.pubsJ, pubsA := N.pubsA }, pubsL := pl } : MsgJ9AL' p K δ).ρS = M.ρS := rfl

theorem pubsC_eqL (χ : Coins frameJ8 K) (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsC =
      ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ).pubsC :=
  (congrArg (fun x => x.pubsC) (mixM_eq δ b Rt hgen prims χ hpG h31A)).trans
    (mixM_C δ ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ)
      ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ) (ComplJ9ALRun.pubsLOf δ Rt hgen prims χ))
theorem pubsJ_eqL (χ : Coins frameJ8 K) (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsJ =
      ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ).pubsJ :=
  (congrArg (fun x => x.pubsJ) (mixM_eq δ b Rt hgen prims χ hpG h31A)).trans
    (mixM_J δ ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ)
      ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ) (ComplJ9ALRun.pubsLOf δ Rt hgen prims χ))
theorem pubsW_eqL (χ : Coins frameJ8 K) (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsW =
      ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ).pubsW :=
  (congrArg (fun x => x.pubsW) (mixM_eq δ b Rt hgen prims χ hpG h31A)).trans
    (mixM_W δ ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ)
      ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ) (ComplJ9ALRun.pubsLOf δ Rt hgen prims χ))
theorem pubsV_eqL (χ : Coins frameJ8 K) (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsV =
      ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ).pubsV :=
  (congrArg (fun x => x.pubsV) (mixM_eq δ b Rt hgen prims χ hpG h31A)).trans
    (mixM_V δ ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ)
      ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ) (ComplJ9ALRun.pubsLOf δ Rt hgen prims χ))
theorem pubsX_eqL (χ : Coins frameJ8 K) (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ClaimJ9.pubVJ9 δ b (cJ s f r) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).m ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).ρ
      ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).ρS χ =
    ClaimJ9.pubVJ9 δ b (cJ s f r) ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ).m
      ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ).ρ ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ).ρS χ := by
  have h1 := (congrArg (fun x => x.m) (mixM_eq δ b Rt hgen prims χ hpG h31A)).trans
    (mixM_m δ ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ)
      ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ) (ComplJ9ALRun.pubsLOf δ Rt hgen prims χ))
  have h2 := (congrArg (fun x => x.ρ) (mixM_eq δ b Rt hgen prims χ hpG h31A)).trans
    (mixM_rho δ ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ)
      ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ) (ComplJ9ALRun.pubsLOf δ Rt hgen prims χ))
  have h3 := (congrArg (fun x => x.ρS) (mixM_eq δ b Rt hgen prims χ hpG h31A)).trans
    (mixM_rhoS δ ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ)
      ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ) (ComplJ9ALRun.pubsLOf δ Rt hgen prims χ))
  rw [h1, h2, h3]

theorem pinRg_eq (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    AcceptsJ9AL.pinRgP (p := p) (K := K) (BRun9AL δ b Rt hgen prims hpG h31A).Pb =
      (ComplJ9ALRun.psRun (p := p) Rt hgen prims).map fun q =>
        AcceptsJ9AL.pinRgVec (p := p) (K := K) q.1 (ComplJ9ALRun.vcRun (p := p) Rt hgen prims q.1) := rfl

theorem pinOp_eq (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    AcceptsJ9AL.pinOpP (p := p) (K := K) (BRun9AL δ b Rt hgen prims hpG h31A).Pb =
      (ComplJ9ALRun.psRun (p := p) Rt hgen prims).map fun q =>
        Nock.Jet.RapJetJ8.keyK (K := K) 8 [(q.1 : ZMod p), (RealIOJ9AL.primCode q.2 : ZMod p), 0, 0, 0, 0, 0,
          (AluSZChipJ9.tagOp : ZMod p)] := rfl

theorem pinCons_eq (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    Nock.Jet.PinJ8.pinCons (p := p) (K := K) (BRun9AL δ b Rt hgen prims hpG h31A).Pb.regs
        (BRun9AL δ b Rt hgen prims hpG h31A).Pb.idx =
      Nock.Jet.PinJ8.pinCons (p := p) (K := K) (ComplJ9ALData.j9alDataOf p Rg Rt prims hgen).regs
        (j9aDataOf p Rg Rt hgen).idx := rfl

theorem pinRecsJ8_eq (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) :
    AcceptsJ8P.pinRecsJ8 δ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ8 χ =
      AcceptsJ8P.pinRecsJ8 δ (ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).Pb χ := by
  unfold AcceptsJ8P.pinRecsJ8
  rfl

theorem pinRecsP_eq (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) :
    AcceptsJ9AL.pinRecsP δ (BRun9AL δ b Rt hgen prims hpG h31A).Pb χ =
      (ComplJ9ALRun.psRun (p := p) Rt hgen prims).map fun q => ClaimVS.claimVec δ (AcceptsJ8.encJ8 δ χ (Nock.Jet.Prim.primC q.2))
        ((ComplJ9ALRun.vcRun (p := p) Rt hgen prims q.1 : ℕ) : ZMod p)
        (((ComplJ9ALData.rkPOf prims q.1).1 : ℕ) : ZMod p) (((ComplJ9ALData.rkPOf prims q.1).2 : ℕ) : ZMod p) := rfl


theorem mixM_X (M : MsgJ9A' p K δ) (N : MsgJ8' p K δ) (pl : ℕ → K) :
    ({ toMsgJ9A' := { M with pubsC := N.pubsC, pubsJ := N.pubsJ, pubsA := N.pubsA }, pubsL := pl } : MsgJ9AL' p K δ).pubsX = M.pubsX := rfl
theorem mixM_S (M : MsgJ9A' p K δ) (N : MsgJ8' p K δ) (pl : ℕ → K) :
    ({ toMsgJ9A' := { M with pubsC := N.pubsC, pubsJ := N.pubsJ, pubsA := N.pubsA }, pubsL := pl } : MsgJ9AL' p K δ).pubsS = M.pubsS := rfl
theorem mixM_A (M : MsgJ9A' p K δ) (N : MsgJ8' p K δ) (pl : ℕ → K) :
    ({ toMsgJ9A' := { M with pubsC := N.pubsC, pubsJ := N.pubsJ, pubsA := N.pubsA }, pubsL := pl } : MsgJ9AL' p K δ).pubsA = N.pubsA := rfl
theorem pubsA_eqL (χ : Coins frameJ8 K) (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA = ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ).pubsA :=
  (congrArg (fun x => x.pubsA) (mixM_eq δ b Rt hgen prims χ hpG h31A)).trans
    (mixM_A δ ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ) ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ) (ComplJ9ALRun.pubsLOf δ Rt hgen prims χ))
theorem pubsXX_eqL (χ : Coins frameJ8 K) (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsX = ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ).pubsX :=
  (congrArg (fun x => x.pubsX) (mixM_eq δ b Rt hgen prims χ hpG h31A)).trans
    (mixM_X δ ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ) ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ) (ComplJ9ALRun.pubsLOf δ Rt hgen prims χ))
theorem pubsS_eqL (χ : Coins frameJ8 K) (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsS = ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ).pubsS :=
  (congrArg (fun x => x.pubsS) (mixM_eq δ b Rt hgen prims χ hpG h31A)).trans
    (mixM_S δ ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ) ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ) (ComplJ9ALRun.pubsLOf δ Rt hgen prims χ))
theorem rhoS_eqL (χ : Coins frameJ8 K) (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).ρS = ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ).ρS :=
  (congrArg (fun x => x.ρS) (mixM_eq δ b Rt hgen prims χ hpG h31A)).trans
    (mixM_rhoS δ ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ) ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ) (ComplJ9ALRun.pubsLOf δ Rt hgen prims χ))
theorem m_eqL (χ : Coins frameJ8 K) (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).m = ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ).m :=
  (congrArg (fun x => x.m) (mixM_eq δ b Rt hgen prims χ hpG h31A)).trans
    (mixM_m δ ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ) ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ) (ComplJ9ALRun.pubsLOf δ Rt hgen prims χ))

theorem toJ8_V {F : Type} [Field F] (T : TrJ9A F) : T.toJ8.V = T.V := rfl

theorem trL_eq (χ : Coins frameJ8 K) (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    (BRun9AL δ b Rt hgen prims hpG h31A).tr χ = ComplJ9ALRun.trAL δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) χ := rfl

theorem trV_eqL (χ : Coins frameJ8 K) (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ((BRun9AL δ b Rt hgen prims hpG h31A).tr χ).toJ8.V = ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).tr χ).toJ8.V :=
  (congrArg (fun T : TrJ9AL (ZMod p) => T.toTrJ9A.toJ8.V) (trL_eq δ b Rt hgen prims χ hpG h31A)).trans
    ((toJ8_V _).trans ((ComplJ9ALRun.trAL_V δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) χ).trans (toJ8_V _).symm))



theorem gBA_of (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (χ : Coins frameJ8 K)
    (hχ : (BRun9AL δ b Rt hgen prims hpG h31A).Good χ) : (ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).Good χ :=
  ComplJ9ALRun.goodAL_BA δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hχ

theorem gL_of (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (χ : Coins frameJ8 K)
    (hχ : (BRun9AL δ b Rt hgen prims hpG h31A).Good χ) :
    (ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).Good χ :=
  ComplJ9ALRun.goodAL_B8L δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hχ

theorem hin_of (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (χ : Coins frameJ8 K)
    (hχ : (BRun9AL δ b Rt hgen prims hpG h31A).Good χ) :
    ∀ L ∈ ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A),
      ∀ e ∈ L, χ ∉ e.ev := fun L hL e he =>
  ComplJ9ALRun.goodAL_spec δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hχ e
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatten.mpr ⟨L, hL, he⟩)))

include δ b prims in
theorem f_hsatX (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hop5 : ProgOp5OK p t) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 (BRun9AL δ b Rt hgen prims hpG h31A).Pb.hn (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodes b δ (chalVJ8 b χ)
    (ClaimJ9.pubVJ9 δ b (cJ s f r) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).m ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).ρ ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).ρS χ) (BRun9AL δ b Rt hgen prims hpG h31A).Pb.orbit)
    (qX9 δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ9A ((BRun9AL δ b Rt hgen prims hpG h31A).tr χ).toTrJ9A (chalVJ8 b χ)
      (ClaimJ9.pubVJ9 δ b (cJ s f r) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).m ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).ρ ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).ρS χ)) :=
  fun χ hχ => xL δ b (chalVJ8 b χ)
  (ClaimJ9.pubVJ9 δ b (cJ s f r) ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ).m ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ).ρ ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ).ρS χ)
  (ClaimJ9.pubVJ9 δ b (cJ s f r) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).m ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).ρ ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).ρS χ) (PbL_toPubJ9A_eq δ b Rt hgen prims hpG h31A)
  ((ComplJ9ALRun.trAL_C δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) χ)) (pubsX_eqL δ b Rt hgen prims χ hpG h31A) (ComplJ9AOfComp.hsatXA δ b Rt hgen hpG h31A hax9 hop5 χ (gBA_of δ b Rt hgen prims hpG h31A χ hχ))

include δ b prims in
theorem f_hinjX (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    Function.Injective (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodes :=
  ComplJ9AOfComp.hinjXA δ b Rt hgen hpG h31A

include δ b prims in
theorem f_hadjX (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ∀ (i : Fin (BRun9AL δ b Rt hgen prims hpG h31A).Pb.n) (hi : (i : ℕ) + 1 < (BRun9AL δ b Rt hgen prims hpG h31A).Pb.n), (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodes i * (BRun9AL δ b Rt hgen prims hpG h31A).Pb.orbit.ω :=
  ComplJ9AOfComp.hadjXA δ b Rt hgen hpG h31A

include δ b prims in
theorem f_hsatC (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → (cellChipHQKW δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.hnC (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesC (BRun9AL δ b Rt hgen prims hpG h31A).Pb.orbitC (chalsMJ8 δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsC).rap.Satisfies
    (qM δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ8 ((BRun9AL δ b Rt hgen prims hpG h31A).tr χ).toJ8 (chalsMJ8 δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsC) :=
  fun χ hχ => (cellL δ b (chalsMJ8 δ χ) ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ).pubsC ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsC (PbL_toPubJ8_eq δ b Rt hgen prims hpG h31A)
  ((ComplJ9ALRun.trAL_M δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) χ)) (pubsC_eqL δ b Rt hgen prims χ hpG h31A) (ComplJ9ALTables.cellOK_L δ b Rt prims hgen (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.cellsL_pos (p := p) Rt prims hgen) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen)
      (ComplJ9ALRun.AVL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) hpG (ComplJ9AChains.hp63_of_G hpG) hleaf
      (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      χ (gL_of δ b Rt hgen prims hpG h31A χ hχ))).1

include δ b prims in
theorem f_hbindC (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → (cellChipHQKW δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.hnC (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesC (BRun9AL δ b Rt hgen prims hpG h31A).Pb.orbitC (chalsMJ8 δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsC).BindsPreprocessing
    (qM δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ8 ((BRun9AL δ b Rt hgen prims hpG h31A).tr χ).toJ8 (chalsMJ8 δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsC) :=
  fun χ hχ => (cellL δ b (chalsMJ8 δ χ) ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ).pubsC ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsC (PbL_toPubJ8_eq δ b Rt hgen prims hpG h31A)
  ((ComplJ9ALRun.trAL_M δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) χ)) (pubsC_eqL δ b Rt hgen prims χ hpG h31A) (ComplJ9ALTables.cellOK_L δ b Rt prims hgen (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.cellsL_pos (p := p) Rt prims hgen) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen)
      (ComplJ9ALRun.AVL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) hpG (ComplJ9AChains.hp63_of_G hpG) hleaf
      (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      χ (gL_of δ b Rt hgen prims hpG h31A χ hχ))).2

include δ b prims in
theorem f_hinjC (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    Function.Injective (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesC :=
  (ComplJ9ALJ.nodes_L δ b Rt prims hgen (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.cellsL_pos (p := p) Rt prims hgen) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen)
    (ComplJ9ALRun.AVL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9AChains.hp63_of_G hpG) (ComplJ9ARun.rows31_of_A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A))).1.1

include δ b prims in
theorem f_hadjC (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ∀ (i : Fin (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nC) (hi : (i : ℕ) + 1 < (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nC), (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesC i * (BRun9AL δ b Rt hgen prims hpG h31A).Pb.orbitC.ω :=
  (ComplJ9ALJ.nodes_L δ b Rt prims hgen (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.cellsL_pos (p := p) Rt prims hgen) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen)
    (ComplJ9ALRun.AVL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9AChains.hp63_of_G hpG) (ComplJ9ARun.rows31_of_A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A))).1.2.1

include δ b prims in
theorem f_hnpC (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nC < ringChar (ZMod p) :=
  (ComplJ9ALJ.nodes_L δ b Rt prims hgen (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.cellsL_pos (p := p) Rt prims hgen) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen)
    (ComplJ9ALRun.AVL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9AChains.hp63_of_G hpG) (ComplJ9ARun.rows31_of_A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A))).1.2.2

include δ b prims in
theorem f_hsatW (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t)) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → (walkChipJ8 δ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.kroots b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.hnW (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesW (BRun9AL δ b Rt hgen prims hpG h31A).Pb.orbitW (chalsMJ8 δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsW).rap.Satisfies
    (qW δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ8 ((BRun9AL δ b Rt hgen prims hpG h31A).tr χ).toJ8 (chalsMJ8 δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsW) :=
  fun χ hχ => (walkL δ b (chalsMJ8 δ χ) ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ).pubsW ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsW (PbL_toPubJ8_eq δ b Rt hgen prims hpG h31A)
  ((ComplJ9ALRun.trAL_W δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) χ)) (pubsW_eqL δ b Rt hgen prims χ hpG h31A) (ComplJ9AOfMem.walk_A δ b Rt hgen hpG h31A hwalk9 χ (gBA_of δ b Rt hgen prims hpG h31A χ hχ))).1

include δ b prims in
theorem f_hbindW (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t)) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → (walkChipJ8 δ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.kroots b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.hnW (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesW (BRun9AL δ b Rt hgen prims hpG h31A).Pb.orbitW (chalsMJ8 δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsW).BindsPreprocessing
    (qW δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ8 ((BRun9AL δ b Rt hgen prims hpG h31A).tr χ).toJ8 (chalsMJ8 δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsW) :=
  fun χ hχ => (walkL δ b (chalsMJ8 δ χ) ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ).pubsW ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsW (PbL_toPubJ8_eq δ b Rt hgen prims hpG h31A)
  ((ComplJ9ALRun.trAL_W δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) χ)) (pubsW_eqL δ b Rt hgen prims χ hpG h31A) (ComplJ9AOfMem.walk_A δ b Rt hgen hpG h31A hwalk9 χ (gBA_of δ b Rt hgen prims hpG h31A χ hχ))).2

include δ b prims in
theorem f_hinjW (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    Function.Injective (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesW :=
  (ComplJ9AOfMem.nodes_A δ b Rt hgen hpG h31A).2.1.1

include δ b prims in
theorem f_hadjW (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ∀ (i : Fin (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nW) (hi : (i : ℕ) + 1 < (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nW), (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesW i * (BRun9AL δ b Rt hgen prims hpG h31A).Pb.orbitW.ω :=
  (ComplJ9AOfMem.nodes_A δ b Rt hgen hpG h31A).2.1.2.1

include δ b prims in
theorem f_hkW (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    1 ≤ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.kroots :=
  (ComplJ9AOfMem.nodes_A δ b Rt hgen hpG h31A).2.1.2.2.1

include δ b prims in
theorem f_hknW (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    (BRun9AL δ b Rt hgen prims hpG h31A).Pb.kroots ≤ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nW :=
  (ComplJ9AOfMem.nodes_A δ b Rt hgen hpG h31A).2.1.2.2.2.1

include δ b prims in
theorem f_hkpW (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    (BRun9AL δ b Rt hgen prims hpG h31A).Pb.kroots + (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nW < ringChar (ZMod p) :=
  (ComplJ9AOfMem.nodes_A δ b Rt hgen hpG h31A).2.1.2.2.2.2

include δ b prims in
theorem f_hJk (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hRtJ : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → JGenJ8.JChipOK δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesJ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.orbitJ (chalsJJ8 χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsJ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.lay
    (qJ δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ8 ((BRun9AL δ b Rt hgen prims hpG h31A).tr χ).toJ8 (chalsJJ8 χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsJ) :=
  fun χ hχ => jL δ b (chalsJJ8 χ) ((ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).M χ).pubsJ ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsJ (PbL_toPubJ8_eq δ b Rt hgen prims hpG h31A)
  ((ComplJ9ALRun.trAL_J δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) χ)) (pubsJ_eqL δ b Rt hgen prims χ hpG h31A) (ComplJ9ALJ.jOK_L δ b Rt prims hgen (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.cellsL_pos (p := p) Rt prims hgen) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen)
      (ComplJ9ALRun.AVL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) hRtJ
      (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))
      χ (gL_of δ b Rt hgen prims hpG h31A χ hχ))

include δ b prims in
theorem f_hsatA (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → (AtomChipHQ.atomChipHQ δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.hnA (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesA (BRun9AL δ b Rt hgen prims hpG h31A).Pb.orbitA (chalsAJ8Z δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA).rap.Satisfies
    (qA δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ8 ((BRun9AL δ b Rt hgen prims hpG h31A).tr χ).toJ8 (chalsAJ8Z δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA) :=
  fun χ hχ => (ComplJ9ALTables.atomOK_L δ b Rt prims hgen hpG (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen) (ComplJ9ARun.rows31_of_A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) χ
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))).1

include δ b prims in
theorem f_hbindA (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → (AtomChipHQ.atomChipHQ δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.hnA (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesA (BRun9AL δ b Rt hgen prims hpG h31A).Pb.orbitA (chalsAJ8Z δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA).BindsPreprocessing
    (qA δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ8 ((BRun9AL δ b Rt hgen prims hpG h31A).tr χ).toJ8 (chalsAJ8Z δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA) :=
  fun χ hχ => (ComplJ9ALTables.atomOK_L δ b Rt prims hgen hpG (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen) (ComplJ9ARun.rows31_of_A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) χ
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))).2.1

include δ b prims in
theorem f_hinjA (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    Function.Injective (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesA :=
  (ComplJ9ALJ.nodes_L δ b Rt prims hgen (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.cellsL_pos (p := p) Rt prims hgen) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen)
    (ComplJ9ALRun.AVL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9AChains.hp63_of_G hpG) (ComplJ9ARun.rows31_of_A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A))).2.2.1

include δ b prims in
theorem f_hadjA (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ∀ (i : Fin (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nA) (hi : (i : ℕ) + 1 < (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nA), (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesA i * (BRun9AL δ b Rt hgen prims hpG h31A).Pb.orbitA.ω :=
  (ComplJ9ALJ.nodes_L δ b Rt prims hgen (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.cellsL_pos (p := p) Rt prims hgen) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen)
    (ComplJ9ALRun.AVL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9AChains.hp63_of_G hpG) (ComplJ9ARun.rows31_of_A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A))).2.2.2.1

include δ b prims in
theorem f_hnpA (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nA < p :=
  (ComplJ9ALJ.nodes_L δ b Rt prims hgen (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.cellsL_pos (p := p) Rt prims hgen) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen)
    (ComplJ9ALRun.AVL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9AChains.hp63_of_G hpG) (ComplJ9ARun.rows31_of_A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A))).2.2.2.2

include δ b prims in
theorem f_hsatL (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → (atomChipHQL δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.hnA (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesA (BRun9AL δ b Rt hgen prims hpG h31A).Pb.orbitA (chalsAJ8Z δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA).rap.Satisfies
    (qAL δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ8 ((BRun9AL δ b Rt hgen prims hpG h31A).tr χ).toJ8 (chalsAJ8Z δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA) :=
  fun χ hχ => (ComplJ9ALTables.atomOK_L δ b Rt prims hgen hpG (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen) (ComplJ9ARun.rows31_of_A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) χ
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))).2.2.1

include δ b prims in
theorem f_hbindL (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → (atomChipHQL δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.hnA (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesA (BRun9AL δ b Rt hgen prims hpG h31A).Pb.orbitA (chalsAJ8Z δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA).BindsPreprocessing
    (qAL δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ8 ((BRun9AL δ b Rt hgen prims hpG h31A).tr χ).toJ8 (chalsAJ8Z δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA) :=
  fun χ hχ => (ComplJ9ALTables.atomOK_L δ b Rt prims hgen hpG (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen) (ComplJ9ARun.rows31_of_A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) χ
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
        (hin_of δ b Rt hgen prims hpG h31A χ hχ _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))).2.2.2

include δ b prims in
theorem f_hVk (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → AWChipOK δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.krootsV (BRun9AL δ b Rt hgen prims hpG h31A).Pb.hnV (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesV (BRun9AL δ b Rt hgen prims hpG h31A).Pb.orbitV (chalsAJ8Z δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsV
    (qV δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ8 ((BRun9AL δ b Rt hgen prims hpG h31A).tr χ).toJ8 (chalsAJ8Z δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsV) :=
  fun χ hχ => awL (P := (ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).Pb.toPubJ8) (P' := (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ8) (Q := (ComplJ9ALRun.B8L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).Pb)
    (tr := ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).tr χ).toJ8) (tr' := ((BRun9AL δ b Rt hgen prims hpG h31A).tr χ).toJ8) δ b (chalsAJ8Z δ χ)
    ((ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A).M χ).pubsV ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsV (PbL_toPubJ8_eq δ b Rt hgen prims hpG h31A)
    (trV_eqL δ b Rt hgen prims χ hpG h31A) (pubsV_eqL δ b Rt hgen prims χ hpG h31A) (ComplJ9AOfMem.aw_A δ b Rt hgen hpG h31A hax9 hwalkA χ (gBA_of δ b Rt hgen prims hpG h31A χ hχ))

include δ b prims in
theorem f_hGx (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hop5 : ProgOp5OK p t) (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t)) (hRtJ : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p) (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)) (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).ρ 3 + (Quad.mk _ (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsW WalkHQ.pubXQ) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsW (WalkHQ.pubXQ + 1)) +
      Quad.mk _ (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsJ 2) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsJ 3) +
      Quad.mk _ (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsL AluSZChipJ9.pubALx) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsL (AluSZChipJ9.pubALx + 1))) =
    Quad.mk _ (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsC CellHQ.pubHQ) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsC (CellHQ.pubHQ + 1)) :=
  fun χ hχ =>
  swap_mid (pubsL_x δ b Rt hgen prims hpG h31A χ) <| ComplJ9ALBalX.hGx_L δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hax9 hop5 hwalk9 hRtJ hnd hprim hnoDec χ
    (gBA_of δ b Rt hgen prims hpG h31A χ hχ) (gL_of δ b Rt hgen prims hpG h31A χ hχ) _ ((hlenL_of δ Rt hgen prims) χ)

include δ b prims in
theorem f_hGp (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hop5 : ProgOp5OK p t) (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t)) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).ρ 4 + Quad.mk _ (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsX AxisChipJ9.pubAXp) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsX (AxisChipJ9.pubAXp + 1)) =
    Quad.mk _ (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsW WalkHQ.pubPQ) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsW (WalkHQ.pubPQ + 1)) :=
  fun χ hχ => ComplJ9ABalP.hGpA δ b Rt hgen hpG h31A hax9 hop5 (ComplJ9ARunFacts.hlen_run Rt hgen hpG h31A) hwalk9 χ (gBA_of δ b Rt hgen prims hpG h31A χ hχ)

include δ b prims in
theorem f_hGS (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads) (hRtJ : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p) (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)) (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).ρS + ((pinCons (p := p) (K := K) (BRun9AL δ b Rt hgen prims hpG h31A).Pb.regs (BRun9AL δ b Rt hgen prims hpG h31A).Pb.idx).map fun x =>
      (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      ((AcceptsJ9AL.pinRgP (p := p) (K := K) (BRun9AL δ b Rt hgen prims hpG h31A).Pb).map fun x =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      ((AcceptsJ9AL.pinOpP (p := p) (K := K) (BRun9AL δ b Rt hgen prims hpG h31A).Pb).map fun x =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      Quad.mk _ (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsJ 0) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsJ 1) +
      Quad.mk _ (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsX AxisChipJ9.pubAXs) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsX (AxisChipJ9.pubAXs + 1)) +
      Quad.mk _ (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsL AluSZChipJ9.pubALs) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsL (AluSZChipJ9.pubALs + 1)) =
    Quad.mk _ (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA AtomChipHQ.pubMI) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA (AtomChipHQ.pubMI + 1)) +
      Quad.mk _ (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsV WalkHQ.pubPQ) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsV (WalkHQ.pubPQ + 1)) +
      Quad.mk _ (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsS SplitChipJ9.pubSPs) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsS (SplitChipJ9.pubSPs + 1)) :=
  by
  intro χ hχ
  rw [pinRg_eq δ b Rt hgen prims hpG h31A, pinOp_eq δ b Rt hgen prims hpG h31A, pinCons_eq δ b Rt hgen prims hpG h31A,
    rhoS_eqL δ b Rt hgen prims χ hpG h31A, pubsJ_eqL δ b Rt hgen prims χ hpG h31A, pubsXX_eqL δ b Rt hgen prims χ hpG h31A,
    pubsA_eqL δ b Rt hgen prims χ hpG h31A, pubsV_eqL δ b Rt hgen prims χ hpG h31A, pubsS_eqL δ b Rt hgen prims χ hpG h31A]
  exact swap_last (pubsL_s δ b Rt hgen prims hpG h31A χ) <| ComplJ9ALBalS.hGS_L δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hax9 hwalkA hRtJ hnd hprim hnoDec χ
    (gBA_of δ b Rt hgen prims hpG h31A χ hχ) (gL_of δ b Rt hgen prims hpG h31A χ hχ) _ ((hlenL_of δ Rt hgen prims) χ)

include δ b prims in
theorem f_hsumCP (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)) (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ →
    Quad.mk (algebraMap (ZMod p) K δ) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsL AluSZChipJ9.pubALv) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsL (AluSZChipJ9.pubALv + 1)) +
    ((ClaimJ9.claimRecsJ9 δ χ (cJ s f r) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).m ++ pinRecsJ8 δ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ8 χ ++
        AcceptsJ9AL.pinRecsP δ (BRun9AL δ b Rt hgen prims hpG h31A).Pb χ).map fun x => (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x)⁻¹).sum =
      Quad.mk (algebraMap (ZMod p) K δ) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsC 0) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsC 1) +
        Quad.mk (algebraMap (ZMod p) K δ) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA AtomChipHQ.pubMB) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA (AtomChipHQ.pubMB + 1)) :=
  by
  intro χ hχ
  rw [pinRecsJ8_eq δ b Rt hgen prims hpG h31A, pinRecsP_eq δ b Rt hgen prims hpG h31A,
    m_eqL δ b Rt hgen prims χ hpG h31A, pubsC_eqL δ b Rt hgen prims χ hpG h31A, pubsA_eqL δ b Rt hgen prims χ hpG h31A]
  exact swap_first (pubsL_v δ b Rt hgen prims hpG h31A χ) <| ComplJ9ALBalV2.hsumC_L δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hnd hprim hnoDec _ χ ((hlenL_of δ Rt hgen prims) χ)

include δ b prims in
theorem f_hbalAP (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ →
    Quad.mk (algebraMap (ZMod p) K δ) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA CellHQ.pubHQ) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA AtomChipHQ.pubC) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA (AtomChipHQ.pubC + 1)) +
        Quad.mk (algebraMap (ZMod p) K δ) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsV WalkHQ.pubXQ) (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsV (WalkHQ.pubXQ + 1)) :=
  fun χ hχ => ComplJ9ALBalA.hbalA_L δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hax9 hwalkA χ (gBA_of δ b Rt hgen prims hpG h31A χ hχ)

include δ b prims in
theorem f_hvalA0 (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA 0 = 0 ∧ ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA 1 = 0 :=
  fun χ hχ => ComplJ9ALBalA.hvalA0_L δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) χ (gBA_of δ b Rt hgen prims hpG h31A χ hχ)

include δ b prims in
theorem f_hfxC (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t)) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsC 2 = ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsW 0 ∧ ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsC 3 = ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsW 1 :=
  fun χ hχ => ComplJ9ALBalA.hfxC_L δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hwalk9 χ (gBA_of δ b Rt hgen prims hpG h31A χ hχ)

include δ b prims in
theorem f_hfxA (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA 2 = ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsV 0 ∧ ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsA 3 = ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsV 1 :=
  fun χ hχ => ComplJ9ALBalA.hfxA_L δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hax9 hwalkA χ (gBA_of δ b Rt hgen prims hpG h31A χ hχ)

include δ b prims in
theorem f_hlay (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots) (hRtJ : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    List.ofFn (BRun9AL δ b Rt hgen prims hpG h31A).Pb.lay = layoutJ8 (BRun9AL δ b Rt hgen prims hpG h31A).Pb.Rt (BRun9AL δ b Rt hgen prims hpG h31A).Pb.regs (BRun9AL δ b Rt hgen prims hpG h31A).Pb.ids :=
  (ComplJ9ALStatic.stat_L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.cellsL_pos (p := p) Rt prims hgen) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen)
    (ComplJ9ALRun.AVL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) hax9 hleaf hRtJ).1

include δ b prims in
theorem f_hsmall (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots) (hRtJ : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ∀ q ∈ layoutJ8 (BRun9AL δ b Rt hgen prims hpG h31A).Pb.Rt (BRun9AL δ b Rt hgen prims hpG h31A).Pb.regs (BRun9AL δ b Rt hgen prims hpG h31A).Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p :=
  (ComplJ9ALStatic.stat_L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.cellsL_pos (p := p) Rt prims hgen) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen)
    (ComplJ9ALRun.AVL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) hax9 hleaf hRtJ).2.1

include δ b prims in
theorem f_huniq (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots) (hRtJ : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ((layoutJ8 (BRun9AL δ b Rt hgen prims hpG h31A).Pb.Rt (BRun9AL δ b Rt hgen prims hpG h31A).Pb.regs (BRun9AL δ b Rt hgen prims hpG h31A).Pb.ids).filterMap tvKey).Nodup :=
  (ComplJ9ALStatic.stat_L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.cellsL_pos (p := p) Rt prims hgen) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen)
    (ComplJ9ALRun.AVL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) hax9 hleaf hRtJ).2.2.1

include δ b prims in
theorem f_hTpl (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots) (hRtJ : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ∀ i ∈ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.regs, Rg.R i = some ⟨((BRun9AL δ b Rt hgen prims hpG h31A).Pb.Rt i).toTemplate p, Nock.Jet.Autogen.compile p ((BRun9AL δ b Rt hgen prims hpG h31A).Pb.Rt i)⟩ ∧
    axPosB ((BRun9AL δ b Rt hgen prims hpG h31A).Pb.Rt i) = true ∧ ((BRun9AL δ b Rt hgen prims hpG h31A).Pb.Rt i).WellTyped p :=
  (ComplJ9ALStatic.stat_L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.cellsL_pos (p := p) Rt prims hgen) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen)
    (ComplJ9ALRun.AVL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) hax9 hleaf hRtJ).2.2.2.1

include δ b prims in
theorem f_hnd (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots) (hRtJ : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    (BRun9AL δ b Rt hgen prims hpG h31A).Pb.regs.Nodup :=
  (ComplJ9ALStatic.stat_L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.cellsL_pos (p := p) Rt prims hgen) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen)
    (ComplJ9ALRun.AVL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) hax9 hleaf hRtJ).2.2.2.2.1

include δ b prims in
theorem f_hidx (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots) (hRtJ : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ∀ id ∈ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.regs, (BRun9AL δ b Rt hgen prims hpG h31A).Pb.idx id < p :=
  (ComplJ9ALStatic.stat_L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.cellsL_pos (p := p) Rt prims hgen) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen)
    (ComplJ9ALRun.AVL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) hax9 hleaf hRtJ).2.2.2.2.2.1

include δ b prims in
theorem f_hrk (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots) (hRtJ : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ∀ id ∈ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.regs, (BRun9AL δ b Rt hgen prims hpG h31A).Pb.rk id ≠ (0, 0) :=
  (ComplJ9ALStatic.stat_L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.cellsL_pos (p := p) Rt prims hgen) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen)
    (ComplJ9ALRun.AVL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) hax9 hleaf hRtJ).2.2.2.2.2.2.1

include δ b prims in
theorem f_hlt (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots) (hRtJ : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ∀ id ∈ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.regs, ((BRun9AL δ b Rt hgen prims hpG h31A).Pb.rk id).1 < ringChar (ZMod p) ∧ ((BRun9AL δ b Rt hgen prims hpG h31A).Pb.rk id).2 < ringChar (ZMod p) ∧
    (BRun9AL δ b Rt hgen prims hpG h31A).Pb.idx id < ringChar (ZMod p) :=
  (ComplJ9ALStatic.stat_L δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.cellsL_pos (p := p) Rt prims hgen) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen)
    (ComplJ9ALRun.AVL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) hax9 hleaf hRtJ).2.2.2.2.2.2.2

include δ b prims in
theorem f_hclI (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots) :
    ∀ χ, ∀ k : Fin 3, (isCellN (claimNoun (cJ s f r) k) = true ∨ ClaimJ9.isBigN p (claimNoun (cJ s f r) k) = true) →
    (((BRun9AL δ b Rt hgen prims hpG h31A).M χ).m k).1 < p :=
  fun χ => (ComplJ9AOfStatic.claim_A δ b Rt hgen hpG h31A hleaf).1 χ

include δ b prims in
theorem f_hclR (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots) :
    ∀ k : Fin 3, isCellN (claimNoun (cJ s f r) k) = true → (claimNoun (cJ s f r) k).internal / 2 ^ 62 < p :=
  (ComplJ9AOfStatic.claim_A δ b Rt hgen hpG h31A hleaf).2.1

include δ b prims in
theorem f_hcenP (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots) :
    ∀ x ∈ ClaimJ9.censusGJ9 (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ8 (cJ s f r) ++ AcceptsJ9AL.censusP (BRun9AL δ b Rt hgen prims hpG h31A).Pb,
    x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, lenL v ≤ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nA + 2 :=
  ComplJ9ALStatic.cen_L δ b Rt hgen prims hpG (ComplJ9ALRun.hFL Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALData.cellsL_pos (p := p) Rt prims hgen) (ComplJ9ALData.acsL_pos (p := p) Rt prims hgen)
    (ComplJ9ALRun.AVL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)) hleaf

include δ b prims in
theorem f_hcellF (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots) :
    isCellN (cJ s f r).formula = true :=
  (ComplJ9AOfStatic.claim_A δ b Rt hgen hpG h31A hleaf).2.2.2

include δ b prims in
theorem f_hlenC (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hnd : (prims.map Prod.fst).Nodup) (h31L : ComplJ9ALRun.aluLen (K := K) δ Rt hgen prims < 2 ^ 31) :
    3 + (BRun9AL δ b Rt hgen prims hpG h31A).Pb.regs.length + 2 * (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nC < p :=
  by
  have h := ((ComplJ9ALStatic.lengths_L Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hnd (ComplJ9ALRun.nLRun (K := K) δ Rt hgen prims) (hnLle_of δ Rt hgen prims h31L))).2
  have e1 : (BRun9AL δ b Rt hgen prims hpG h31A).Pb.regs.length = (ComplJ9ALData.j9alDataOf p Rg Rt prims hgen).regs.length := rfl
  have e2 : (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nC = (ComplJ9ALData.j9alDataOf p Rg Rt prims hgen).cells.length := rfl
  rw [e1, e2]
  omega

include δ b prims in
theorem f_hlenA (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nA + (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nV < p :=
  (ComplJ9AOfStatic.budget_A δ b Rt hgen hpG h31A).2.1

include δ b prims in
theorem f_hnAS (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nA + (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nS < 2 ^ 57 :=
  (ComplJ9AOfStatic.budget_A δ b Rt hgen hpG h31A).2.2.1

include δ b prims in
theorem f_hbud (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    BudJ9AL (BRun9AL δ b Rt hgen prims hpG h31A).Pb (BRun9AL δ b Rt hgen prims hpG h31A).rows ((BRun9AL δ b Rt hgen prims hpG h31A).g + (BRun9AL δ b Rt hgen prims hpG h31A).rows.N) :=
  (ComplJ9ALStatic.bud_genericL (ComplJ9ALRun.PbL δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A))).1

include δ b prims in
theorem f_hbudV (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    (BRun9AL δ b Rt hgen prims hpG h31A).Pb.regs.length ≤ (BRun9AL δ b Rt hgen prims hpG h31A).g ∧ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nA ≤ (BRun9AL δ b Rt hgen prims hpG h31A).rows.mb ∧ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nA ≤ (BRun9AL δ b Rt hgen prims hpG h31A).rows.A ∧ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nV ≤ (BRun9AL δ b Rt hgen prims hpG h31A).rows.AW ∧
    (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nX ≤ (BRun9AL δ b Rt hgen prims hpG h31A).rows.AX ∧ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nS ≤ (BRun9AL δ b Rt hgen prims hpG h31A).rows.SP :=
  (ComplJ9ALStatic.bud_genericL (ComplJ9ALRun.PbL δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A))).2

include δ b prims in
theorem f_hAXk (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → AXChipOK δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.axOn (BRun9AL δ b Rt hgen prims hpG h31A).Pb.hnX (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesX (BRun9AL δ b Rt hgen prims hpG h31A).Pb.orbitX (chalsMJ8 δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsX
    (qAX δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ9A ((BRun9AL δ b Rt hgen prims hpG h31A).tr χ).toTrJ9A (chalsMJ8 δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsX) :=
  fun χ hχ => ComplJ9AOf.axOK_A δ b Rt hgen hpG h31A χ (gBA_of δ b Rt hgen prims hpG h31A χ hχ)

include δ b prims in
theorem f_hSPk (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → SPChipOK δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nA (BRun9AL δ b Rt hgen prims hpG h31A).Pb.spOn (BRun9AL δ b Rt hgen prims hpG h31A).Pb.hnS (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesS (BRun9AL δ b Rt hgen prims hpG h31A).Pb.orbitS (chalsMJ8 δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsS
    (qSP δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.toPubJ9A ((BRun9AL δ b Rt hgen prims hpG h31A).tr χ).toTrJ9A (chalsMJ8 δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsS) :=
  fun χ hχ => ComplJ9AOf.spOK_A δ b Rt hgen hpG h31A hax9 χ (gBA_of δ b Rt hgen prims hpG h31A χ hχ)

include δ b prims in
theorem f_hlenX (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nX + (BRun9AL δ b Rt hgen prims hpG h31A).Pb.n < p ∧ 2 * (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nS < p :=
  (ComplJ9AOfStatic.budget_A δ b Rt hgen hpG h31A).2.2.2.2.2

include δ b prims in
theorem f_hALk (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)) (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) (hlimb : AluCallOK.PrimLimbs62 (prims.map Prod.fst) t) (h31L : ComplJ9ALRun.aluLen (K := K) δ Rt hgen prims < 2 ^ 31) :
    ∀ χ, (BRun9AL δ b Rt hgen prims hpG h31A).Good χ → ALChipOK δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb.aluOn (BRun9AL δ b Rt hgen prims hpG h31A).Pb.prims (BRun9AL δ b Rt hgen prims hpG h31A).Pb.hnL (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nodesL (BRun9AL δ b Rt hgen prims hpG h31A).Pb.orbitL (BRun9AL δ b Rt hgen prims hpG h31A).Pb.preL
    (AluSZChipJ9.chalsALJ8 δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsL (RealIOJ9AL.qAL δ b (BRun9AL δ b Rt hgen prims hpG h31A).Pb ((BRun9AL δ b Rt hgen prims hpG h31A).tr χ) (AluSZChipJ9.chalsALJ8 δ χ) ((BRun9AL δ b Rt hgen prims hpG h31A).M χ).pubsL) :=
  fun χ hχ => ComplJ9ALOfAlu.hALk_run δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) (le_of_lt h31L) hnd hprim hnoDec hlimb χ hχ

include δ b prims in
theorem f_hPrim (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)) :
    ∀ q ∈ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.prims, Rg.R q.1 = some (Nock.Jet.Prim.primSpec q.2) :=
  (ComplJ9ALStatic.prims_L Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hax9 hnd hprim).1

include δ b prims in
theorem f_hdisjP (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)) :
    ∀ q ∈ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.prims, q.1 ∉ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.regs :=
  (ComplJ9ALStatic.prims_L Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hax9 hnd hprim).2.1

include δ b prims in
theorem f_hlenL (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)) (h31L : ComplJ9ALRun.aluLen (K := K) δ Rt hgen prims < 2 ^ 31) :
    (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nL + (BRun9AL δ b Rt hgen prims hpG h31A).Pb.n < p ∧ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nL ≤ (BRun9AL δ b Rt hgen prims hpG h31A).rows.AL ∧ ∀ q ∈ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.prims, q.1 < p ∧ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.idxP q.1 < p :=
  ⟨((ComplJ9ALStatic.lengths_L Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hnd (ComplJ9ALRun.nLRun (K := K) δ Rt hgen prims) (hnLle_of δ Rt hgen prims h31L))).1, le_refl _, ((ComplJ9ALStatic.prims_L Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hax9 hnd hprim)).2.2.2.2.2⟩

include δ b prims in
theorem f_hndP (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)) :
    ((BRun9AL δ b Rt hgen prims hpG h31A).Pb.prims.map Prod.fst).Nodup :=
  (ComplJ9ALStatic.prims_L Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hax9 hnd hprim).2.2.1

include δ b prims in
theorem f_hrkP (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)) :
    ∀ q ∈ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.prims, (BRun9AL δ b Rt hgen prims hpG h31A).Pb.rkP q.1 ≠ (0, 0) :=
  (ComplJ9ALStatic.prims_L Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hax9 hnd hprim).2.2.2.1

include δ b prims in
theorem f_hltP (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hax9 : ProgAxOK9A p t) (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)) :
    ∀ q ∈ (BRun9AL δ b Rt hgen prims hpG h31A).Pb.prims, ((BRun9AL δ b Rt hgen prims hpG h31A).Pb.rkP q.1).1 < ringChar (ZMod p) ∧ ((BRun9AL δ b Rt hgen prims hpG h31A).Pb.rkP q.1).2 < ringChar (ZMod p) ∧
    (BRun9AL δ b Rt hgen prims hpG h31A).Pb.idxP q.1 < ringChar (ZMod p) :=
  (ComplJ9ALStatic.prims_L Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hax9 hnd hprim).2.2.2.2.1

include δ b prims in
theorem f_hlenCP (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) (hnd : (prims.map Prod.fst).Nodup) (h31L : ComplJ9ALRun.aluLen (K := K) δ Rt hgen prims < 2 ^ 31) :
    3 + (BRun9AL δ b Rt hgen prims hpG h31A).Pb.regs.length + (BRun9AL δ b Rt hgen prims hpG h31A).Pb.prims.length + (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nL + 2 * (BRun9AL δ b Rt hgen prims hpG h31A).Pb.nC < p :=
  ((ComplJ9ALStatic.lengths_L Rt hgen prims hpG (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hnd (ComplJ9ALRun.nLRun (K := K) δ Rt hgen prims) (hnLle_of δ Rt hgen prims h31L))).2

include δ b prims in
theorem f_wt (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    ∀ e ∈ (BRun9AL δ b Rt hgen prims hpG h31A).bad, (e.1.card : ℚ) / Fintype.card (Coins frameJ8 K) ≤ e.2 :=
  ComplJ9ALOfAlu.wtAL δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)

include δ b prims in
theorem f_staged (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    StJ9AL (BRun9AL δ b Rt hgen prims hpG h31A).tr :=
  ComplJ9ALOfAlu.stagedAL δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)

include δ b prims in
theorem f_fig (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen)) :
    p = Nock.Atoms.p → Fintype.card K = VclL.Events.cK → RowsLe31AL (BRun9AL δ b Rt hgen prims hpG h31A).Pb → (BRun9AL δ b Rt hgen prims hpG h31A).epsC < 1 / 2 ^ 120 :=
  fun _ hK hrows => ComplJ9ALOfAlu.figAL δ b Rt hgen prims hpG h31A (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A) hK hrows.2

/-- **Every obligation at `BRun9AL`.**  Binders: the J-9 A run binders, the prim-aware `hRtJ`, the registry facts
`hnd hprim`, the strict ALU size `h31L : aluLen < 2^31`, and the disclosed `hlimb hnoDec`.  Assembled from one
lemma per field (each field is its own declaration so no single elaboration exhausts the heartbeat budget). -/
theorem obligations_of_runAL (hpG : p = Nock.Atoms.p) (hax9 : ProgAxOK9A p t) (hop5 : ProgOp5OK p t)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots)
    (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads)
    (hRtJ : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2))
    (h31A : Rows31A (j9aDataOf p Rg Rt hgen))
    (h31L : ComplJ9ALRun.aluLen (K := K) δ Rt hgen prims < 2 ^ 31)
    (hlimb : AluCallOK.PrimLimbs62 (prims.map Prod.fst) t)
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) :
    ComplJ9ALObligations δ b (BRun9AL δ b Rt hgen prims hpG h31A) :=
  { hsatX := f_hsatX δ b Rt hgen prims hpG h31A hax9 hop5
    hinjX := f_hinjX δ b Rt hgen prims hpG h31A
    hadjX := f_hadjX δ b Rt hgen prims hpG h31A
    hsatC := f_hsatC δ b Rt hgen prims hpG h31A hleaf
    hbindC := f_hbindC δ b Rt hgen prims hpG h31A hleaf
    hinjC := f_hinjC δ b Rt hgen prims hpG h31A
    hadjC := f_hadjC δ b Rt hgen prims hpG h31A
    hnpC := f_hnpC δ b Rt hgen prims hpG h31A
    hsatW := f_hsatW δ b Rt hgen prims hpG h31A hwalk9
    hbindW := f_hbindW δ b Rt hgen prims hpG h31A hwalk9
    hinjW := f_hinjW δ b Rt hgen prims hpG h31A
    hadjW := f_hadjW δ b Rt hgen prims hpG h31A
    hkW := f_hkW δ b Rt hgen prims hpG h31A
    hknW := f_hknW δ b Rt hgen prims hpG h31A
    hkpW := f_hkpW δ b Rt hgen prims hpG h31A
    hJk := f_hJk δ b Rt hgen prims hpG h31A hRtJ
    hsatA := f_hsatA δ b Rt hgen prims hpG h31A
    hbindA := f_hbindA δ b Rt hgen prims hpG h31A
    hinjA := f_hinjA δ b Rt hgen prims hpG h31A
    hadjA := f_hadjA δ b Rt hgen prims hpG h31A
    hnpA := f_hnpA δ b Rt hgen prims hpG h31A
    hsatL := f_hsatL δ b Rt hgen prims hpG h31A
    hbindL := f_hbindL δ b Rt hgen prims hpG h31A
    hVk := f_hVk δ b Rt hgen prims hpG h31A hax9 hwalkA
    hGx := f_hGx δ b Rt hgen prims hpG h31A hax9 hop5 hwalk9 hRtJ hnd hprim hnoDec
    hGp := f_hGp δ b Rt hgen prims hpG h31A hax9 hop5 hwalk9
    hGS := f_hGS δ b Rt hgen prims hpG h31A hax9 hwalkA hRtJ hnd hprim hnoDec
    hsumC' := f_hsumCP δ b Rt hgen prims hpG h31A hnd hprim hnoDec
    hbalA' := f_hbalAP δ b Rt hgen prims hpG h31A hax9 hwalkA
    hvalA0 := f_hvalA0 δ b Rt hgen prims hpG h31A
    hfxC := f_hfxC δ b Rt hgen prims hpG h31A hwalk9
    hfxA := f_hfxA δ b Rt hgen prims hpG h31A hax9 hwalkA
    hlay := f_hlay δ b Rt hgen prims hpG h31A hax9 hleaf hRtJ
    hsmall := f_hsmall δ b Rt hgen prims hpG h31A hax9 hleaf hRtJ
    huniq := f_huniq δ b Rt hgen prims hpG h31A hax9 hleaf hRtJ
    hTpl := f_hTpl δ b Rt hgen prims hpG h31A hax9 hleaf hRtJ
    hnd := f_hnd δ b Rt hgen prims hpG h31A hax9 hleaf hRtJ
    hidx := f_hidx δ b Rt hgen prims hpG h31A hax9 hleaf hRtJ
    hrk := f_hrk δ b Rt hgen prims hpG h31A hax9 hleaf hRtJ
    hlt := f_hlt δ b Rt hgen prims hpG h31A hax9 hleaf hRtJ
    hclI := f_hclI δ b Rt hgen prims hpG h31A hleaf
    hclR := f_hclR δ b Rt hgen prims hpG h31A hleaf
    hcen' := f_hcenP δ b Rt hgen prims hpG h31A hleaf
    hcellF := f_hcellF δ b Rt hgen prims hpG h31A hleaf
    hlenC := f_hlenC δ b Rt hgen prims hpG h31A hnd h31L
    hlenA := f_hlenA δ b Rt hgen prims hpG h31A
    hnAS := f_hnAS δ b Rt hgen prims hpG h31A
    hbud := f_hbud δ b Rt hgen prims hpG h31A
    hbudV := f_hbudV δ b Rt hgen prims hpG h31A
    hAXk := f_hAXk δ b Rt hgen prims hpG h31A
    hSPk := f_hSPk δ b Rt hgen prims hpG h31A hax9
    hlenX := f_hlenX δ b Rt hgen prims hpG h31A
    hALk := f_hALk δ b Rt hgen prims hpG h31A hnd hprim hnoDec hlimb h31L
    hPrim := f_hPrim δ b Rt hgen prims hpG h31A hax9 hnd hprim
    hdisjP := f_hdisjP δ b Rt hgen prims hpG h31A hax9 hnd hprim
    hlenL := f_hlenL δ b Rt hgen prims hpG h31A hax9 hnd hprim h31L
    hndP := f_hndP δ b Rt hgen prims hpG h31A hax9 hnd hprim
    hrkP := f_hrkP δ b Rt hgen prims hpG h31A hax9 hnd hprim
    hltP := f_hltP δ b Rt hgen prims hpG h31A hax9 hnd hprim
    hlenCP := f_hlenCP δ b Rt hgen prims hpG h31A hnd h31L
    wt := f_wt δ b Rt hgen prims hpG h31A
    staged := f_staged δ b Rt hgen prims hpG h31A
    fig := f_fig δ b Rt hgen prims hpG h31A }

/-- `RowsLe31AL` at `BRun9AL`, from `h31A` and the strict `h31L`. -/
theorem rowsLe31AL_runAL (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen))
    (h31L : ComplJ9ALRun.aluLen (K := K) δ Rt hgen prims < 2 ^ 31) :
    RowsLe31AL (BRun9AL δ b Rt hgen prims hpG h31A).Pb := by
  have h31 := ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A
  have hW : (Nock.NockVMROM.Thm54.VclL.GenWalk.walkRows (j9aDataOf p Rg Rt hgen).cells
      (j9aDataOf p Rg Rt hgen).reads).length ∈ ComplJ9ARun.sizesA (j9aDataOf p Rg Rt hgen) :=
    List.mem_append_left _ (by simp [Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of.sizesJ8])
  refine ⟨⟨⟨h31A _ (ComplJ9AOfStatic.mem_N9 Rt hgen), h31 _ (ComplJ9ALStatic.memL_cells Rt hgen prims),
    h31A _ hW, h31 _ (ComplJ9ALStatic.memL_jrows Rt hgen prims), h31 _ (ComplJ9ALStatic.memL_acs Rt hgen prims),
    h31A _ (ComplJ9AOfStatic.mem_nV Rt hgen)⟩,
    h31A _ (ComplJ9AOfStatic.mem_nX Rt hgen), h31A _ (ComplJ9AOfStatic.mem_nS Rt hgen)⟩, ?_⟩
  show ComplJ9ALRun.aluLen (K := K) δ Rt hgen prims + 1 ≤ 2 ^ 31
  omega

open Classical in
/-- **`complJ9AL_closed`: J-9 AL general completeness at Goldilocks, chips on, ALU and primitives included.**
For a generated run `hgen` of a program over a verified registry `Rg`, where the called non-primitive jets are
registered in compiled form from the template table `rtP Rt prims` (primitive ids sent to the trivial template)
and the primitive ids are distinct and registered with their primitive specs (`hnd`, `hprim`); under the J-9 A
axis, op-5, leaf and walk-depth conditions, every table of at most `2^31` rows and ALU length `aluLen < 2^31` (`h31L`; the ALU table has `aluLen + 1 ≤ 2^31`
rows), primitive operands within 62 limbs and no decrement primitive: at the run's honest record `BRun9AL`,
(1) `AcceptsJ9AL` accepts at every good coin, (2) the fraction of coins that are not good is at most `ε_c`,
(3) the trace family is staged (`StJ9AL`), (4) the claim holds (`HoldsN`), and (5) when `|K| = cK`,
`ε_c < 2^-120` and some coin is accepted. -/
theorem complJ9AL_closed (hpG : p = Nock.Atoms.p) (hax9 : ProgAxOK9A p t) (hop5 : ProgOp5OK p t)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg (rtP Rt prims) hgen).roots)
    (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg (rtP Rt prims) hgen).preads)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hregAx : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst → ∀ i, (Rt id).ax i < p)
    (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2))
    (h31A : Rows31A (j9aDataOf p Rg (rtP Rt prims) hgen))
    (h31L : ComplJ9ALRun.aluLen (K := K) δ (rtP Rt prims) hgen prims < 2 ^ 31)
    (hlimb : AluCallOK.PrimLimbs62 (prims.map Prod.fst) t)
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) :
    let B := BRun9AL δ b (rtP Rt prims) hgen prims hpG h31A
    (∀ χ, B.Good χ → AcceptsJ9AL δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ9AL B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9AL δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) := by
  intro B
  have hRtJ : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨((rtP Rt prims) id).toTemplate p, Nock.Jet.Autogen.compile p ((rtP Rt prims) id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB ((rtP Rt prims) id) = true ∧ ((rtP Rt prims) id).WellTyped p := by
    intro id hid hn
    rw [ComplJ9ALData.rtP_of_not_mem Rt prims hn]
    exact hRt id hid hn
  have O := obligations_of_runAL δ b (rtP Rt prims) hgen prims hpG hax9 hop5 hleaf hwalk9 hwalkA hRtJ hnd hprim
    h31A h31L hlimb hnoDec
  have hrows := rowsLe31AL_runAL δ b (rtP Rt prims) hgen prims hpG h31A h31L
  obtain ⟨h1, h2, h3, h4, h5⟩ := complJ9AL_of_obligations δ b B O
  exact ⟨h1, h2, h3, h4, fun hcK => h5 hpG hcK hrows⟩

end Rec

section Of
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (prims : List (ℕ × PrimOp))

open Classical in
/-- **`complJ9AL_closed_of`: J-9 AL completeness with the registry condition stated as `CompiledByP`.**
The same five conclusions as `complJ9AL_closed` (acceptance at every good coin, bad-coin fraction at most `ε_c`,
staging, the claim holds, and for `|K| = cK` the bound `ε_c < 2^-120` with an accepting coin), where the
per-jet registration hypotheses are replaced by the single condition that the registry is compiled from `Rt`
with the primitives `prims` (`CompiledByP`), together with distinct primitive ids. -/
theorem complJ9AL_closed_of (hpG : p = Nock.Atoms.p) (hax9 : ProgAxOK9A p t) (hop5 : ProgOp5OK p t)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg (rtP Rt prims) hgen).roots)
    (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg (rtP Rt prims) hgen).preads)
    (hC : CheckedRegistryP.CompiledByP p Rg Rt prims) (hnd : (prims.map Prod.fst).Nodup)
    (h31A : Rows31A (j9aDataOf p Rg (rtP Rt prims) hgen))
    (h31L : ComplJ9ALRun.aluLen (K := K) δ (rtP Rt prims) hgen prims < 2 ^ 31)
    (hlimb : AluCallOK.PrimLimbs62 (prims.map Prod.fst) t)
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) :
    let B := BRun9AL δ b (rtP Rt prims) hgen prims hpG h31A
    (∀ χ, B.Good χ → AcceptsJ9AL δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ9AL B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9AL δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) := by
  obtain ⟨hRt, hregAx, hprim⟩ := CheckedRegistryP.hRt_hregAx_ofP hC hgen
  exact complJ9AL_closed δ b Rt hgen prims hpG hax9 hop5 hleaf hwalk9 hwalkA hRt hregAx hnd hprim h31A h31L hlimb
    hnoDec

end Of

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALClosed
