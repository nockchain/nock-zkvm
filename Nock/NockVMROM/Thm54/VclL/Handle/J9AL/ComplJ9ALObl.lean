/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALObl.lean

  **J-9 AL obligations layer, ** (twin of `ComplJ9AObl`, retargeted from `AcceptsJ9A` to `AcceptsJ9AL`).
  * `HonestJ9AL`: the honest data of a run at the J-9 AL records (`PubJ9AL`, `MsgJ9AL'`, `TrJ9AL`, `RowsJ9AL`).
  * `RowsLe31AL`: `RowsLe31A` + the ALU table height `nL ≤ 2^31`.
  * `ComplJ9ALObligations`: one field per `AcceptsJ9AL` field (per good coin where `ComplJ9AObligations` has one; the
    chi-free new fields bare), plus `wt`, `staged : StJ9AL`, `fig`.
  * `honest_accepted_J9AL_of_obligations`, `probJ9AL_notGood_le`, `exists_good9AL`, `complJ9AL_of_obligations`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AObl
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ARun
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALData
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluSatRun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALObl

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

/-- Every table has `≤ 2^31` rows, incl. the axis, split and ALU tables. -/
def RowsLe31AL {p : ℕ} [Fact p.Prime] (Pb : PubJ9AL p) : Prop :=
  RowsLe31A Pb.toPubJ9A ∧ Pb.nL ≤ 2 ^ 31

/-! ## 1. The honest data -/

/-- **The honest J-9 AL data of one run.** -/
structure HonestJ9AL (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] (δ : ZMod p)
    (Rg : Nock.Jet.VerifiedRegistry) (fuel : ℕ) (s f r : Noun) where
  t : NTree SkelX
  hgen : genX Rg.R fuel s f = some (t, r)
  Pb : PubJ9AL p
  M : Coins frameJ8 K → MsgJ9AL' p K δ
  tr : Coins frameJ8 K → TrJ9AL (ZMod p)
  rows : RowsJ9AL
  g : ℕ
  bad : List (Finset (Coins frameJ8 K) × ℚ)

namespace HonestJ9AL
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] {δ : ZMod p}
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- A coin is good when it lies outside every honest bad event. -/
def Good (B : HonestJ9AL p K δ Rg fuel s f r) (χ : Coins frameJ8 K) : Prop := ∀ e ∈ B.bad, χ ∉ e.1

/-- The completeness error: the sum of the weights. -/
def epsC (B : HonestJ9AL p K δ Rg fuel s f r) : ℚ := (B.bad.map Prod.snd).sum

end HonestJ9AL

/-! ## 2. The obligations -/

section Obl
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

structure ComplJ9ALObligations (B : HonestJ9AL p K δ Rg fuel s f r) : Prop where
  -- ### [B1] chip: compute (twin RAP)
  hsatX : ∀ χ, B.Good χ → RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 B.Pb.hn B.Pb.nodes b δ (chalVJ8 b χ)
    (ClaimJ9.pubVJ9 δ b (cJ s f r) (B.M χ).m (B.M χ).ρ (B.M χ).ρS χ) B.Pb.orbit)
    (qX9 δ b B.Pb.toPubJ9A (B.tr χ).toTrJ9A (chalVJ8 b χ)
      (ClaimJ9.pubVJ9 δ b (cJ s f r) (B.M χ).m (B.M χ).ρ (B.M χ).ρS χ))
  hinjX : Function.Injective B.Pb.nodes
  hadjX : ∀ (i : Fin B.Pb.n) (hi : (i : ℕ) + 1 < B.Pb.n), B.Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = B.Pb.nodes i * B.Pb.orbit.ω
  -- ### [B1] chip: cell
  hsatC : ∀ χ, B.Good χ → (cellChipHQKW δ b B.Pb.hnC B.Pb.nodesC B.Pb.orbitC (chalsMJ8 δ χ) (B.M χ).pubsC).rap.Satisfies
    (qM δ b B.Pb.toPubJ8 (B.tr χ).toJ8 (chalsMJ8 δ χ) (B.M χ).pubsC)
  hbindC : ∀ χ, B.Good χ → (cellChipHQKW δ b B.Pb.hnC B.Pb.nodesC B.Pb.orbitC (chalsMJ8 δ χ) (B.M χ).pubsC).BindsPreprocessing
    (qM δ b B.Pb.toPubJ8 (B.tr χ).toJ8 (chalsMJ8 δ χ) (B.M χ).pubsC)
  hinjC : Function.Injective B.Pb.nodesC
  hadjC : ∀ (i : Fin B.Pb.nC) (hi : (i : ℕ) + 1 < B.Pb.nC), B.Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = B.Pb.nodesC i * B.Pb.orbitC.ω
  hnpC : B.Pb.nC < ringChar (ZMod p)
  -- ### [B1] chip: J-8 walk
  hsatW : ∀ χ, B.Good χ → (walkChipJ8 δ B.Pb.kroots b B.Pb.hnW B.Pb.nodesW B.Pb.orbitW (chalsMJ8 δ χ) (B.M χ).pubsW).rap.Satisfies
    (qW δ b B.Pb.toPubJ8 (B.tr χ).toJ8 (chalsMJ8 δ χ) (B.M χ).pubsW)
  hbindW : ∀ χ, B.Good χ → (walkChipJ8 δ B.Pb.kroots b B.Pb.hnW B.Pb.nodesW B.Pb.orbitW (chalsMJ8 δ χ) (B.M χ).pubsW).BindsPreprocessing
    (qW δ b B.Pb.toPubJ8 (B.tr χ).toJ8 (chalsMJ8 δ χ) (B.M χ).pubsW)
  hinjW : Function.Injective B.Pb.nodesW
  hadjW : ∀ (i : Fin B.Pb.nW) (hi : (i : ℕ) + 1 < B.Pb.nW), B.Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = B.Pb.nodesW i * B.Pb.orbitW.ω
  hkW : 1 ≤ B.Pb.kroots
  hknW : B.Pb.kroots ≤ B.Pb.nW
  hkpW : B.Pb.kroots + B.Pb.nW < ringChar (ZMod p)
  -- ### [B1] chip: J chip
  hJk : ∀ χ, B.Good χ → JGenJ8.JChipOK δ b B.Pb.nodesJ B.Pb.orbitJ (chalsJJ8 χ) (B.M χ).pubsJ B.Pb.lay
    (qJ δ b B.Pb.toPubJ8 (B.tr χ).toJ8 (chalsJJ8 χ) (B.M χ).pubsJ)
  -- ### [B1] chip: atom table
  hsatA : ∀ χ, B.Good χ → (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
    (qA δ b B.Pb.toPubJ8 (B.tr χ).toJ8 (chalsAJ8Z δ χ) (B.M χ).pubsA)
  hbindA : ∀ χ, B.Good χ → (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
    (qA δ b B.Pb.toPubJ8 (B.tr χ).toJ8 (chalsAJ8Z δ χ) (B.M χ).pubsA)
  hinjA : Function.Injective B.Pb.nodesA
  hadjA : ∀ (i : Fin B.Pb.nA) (hi : (i : ℕ) + 1 < B.Pb.nA), B.Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = B.Pb.nodesA i * B.Pb.orbitA.ω
  hnpA : B.Pb.nA < p
  hsatL : ∀ χ, B.Good χ → (atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
    (qAL δ b B.Pb.toPubJ8 (B.tr χ).toJ8 (chalsAJ8Z δ χ) (B.M χ).pubsA)
  hbindL : ∀ χ, B.Good χ → (atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
    (qAL δ b B.Pb.toPubJ8 (B.tr χ).toJ8 (chalsAJ8Z δ χ) (B.M χ).pubsA)
  -- ### [B1] chip: atom walk
  hVk : ∀ χ, B.Good χ → AWChipOK δ b B.Pb.krootsV B.Pb.hnV B.Pb.nodesV B.Pb.orbitV (chalsAJ8Z δ χ) (B.M χ).pubsV
    (qV δ b B.Pb.toPubJ8 (B.tr χ).toJ8 (chalsAJ8Z δ χ) (B.M χ).pubsV)
  -- ### [B2] balance
  /-- [AL] CHANGED: + the ALU export terminal. -/
  hGx : ∀ χ, B.Good χ → (B.M χ).ρ 3 + (Quad.mk _ ((B.M χ).pubsW WalkHQ.pubXQ) ((B.M χ).pubsW (WalkHQ.pubXQ + 1)) +
      Quad.mk _ ((B.M χ).pubsJ 2) ((B.M χ).pubsJ 3) +
      Quad.mk _ ((B.M χ).pubsL AluSZChipJ9.pubALx) ((B.M χ).pubsL (AluSZChipJ9.pubALx + 1))) =
    Quad.mk _ ((B.M χ).pubsC CellHQ.pubHQ) ((B.M χ).pubsC (CellHQ.pubHQ + 1))
  hGp : ∀ χ, B.Good χ → (B.M χ).ρ 4 + Quad.mk _ ((B.M χ).pubsX AxisChipJ9.pubAXp) ((B.M χ).pubsX (AxisChipJ9.pubAXp + 1)) =
    Quad.mk _ ((B.M χ).pubsW WalkHQ.pubPQ) ((B.M χ).pubsW (WalkHQ.pubPQ + 1))
  /-- [AL] CHANGED: + the primitive pins `pinRgP`, `pinOpP` and the ALU service terminal (left). -/
  hGS : ∀ χ, B.Good χ → (B.M χ).ρS + ((pinCons (p := p) (K := K) B.Pb.regs B.Pb.idx).map fun x =>
      (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      ((AcceptsJ9AL.pinRgP (p := p) (K := K) B.Pb).map fun x =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      ((AcceptsJ9AL.pinOpP (p := p) (K := K) B.Pb).map fun x =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      Quad.mk _ ((B.M χ).pubsJ 0) ((B.M χ).pubsJ 1) +
      Quad.mk _ ((B.M χ).pubsX AxisChipJ9.pubAXs) ((B.M χ).pubsX (AxisChipJ9.pubAXs + 1)) +
      Quad.mk _ ((B.M χ).pubsL AluSZChipJ9.pubALs) ((B.M χ).pubsL (AluSZChipJ9.pubALs + 1)) =
    Quad.mk _ ((B.M χ).pubsA AtomChipHQ.pubMI) ((B.M χ).pubsA (AtomChipHQ.pubMI + 1)) +
      Quad.mk _ ((B.M χ).pubsV WalkHQ.pubPQ) ((B.M χ).pubsV (WalkHQ.pubPQ + 1)) +
      Quad.mk _ ((B.M χ).pubsS SplitChipJ9.pubSPs) ((B.M χ).pubsS (SplitChipJ9.pubSPs + 1))
  /-- [AL] CHANGED: the cell validity, + the ALU validity terminal (left), + the primitive pin records. -/
  hsumC' : ∀ χ, B.Good χ →
    Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsL AluSZChipJ9.pubALv) ((B.M χ).pubsL (AluSZChipJ9.pubALv + 1)) +
    ((ClaimJ9.claimRecsJ9 δ χ (cJ s f r) (B.M χ).m ++ pinRecsJ8 δ B.Pb.toPubJ8 χ ++
        AcceptsJ9AL.pinRecsP δ B.Pb χ).map fun x => (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x)⁻¹).sum =
      Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsC 0) ((B.M χ).pubsC 1) +
        Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsA AtomChipHQ.pubMB) ((B.M χ).pubsA (AtomChipHQ.pubMB + 1))
  hbalA' : ∀ χ, B.Good χ →
    Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsA CellHQ.pubHQ) ((B.M χ).pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsA AtomChipHQ.pubC) ((B.M χ).pubsA (AtomChipHQ.pubC + 1)) +
        Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsV WalkHQ.pubXQ) ((B.M χ).pubsV (WalkHQ.pubXQ + 1))
  hvalA0 : ∀ χ, B.Good χ → (B.M χ).pubsA 0 = 0 ∧ (B.M χ).pubsA 1 = 0
  hfxC : ∀ χ, B.Good χ → (B.M χ).pubsC 2 = (B.M χ).pubsW 0 ∧ (B.M χ).pubsC 3 = (B.M χ).pubsW 1
  hfxA : ∀ χ, B.Good χ → (B.M χ).pubsA 2 = (B.M χ).pubsV 0 ∧ (B.M χ).pubsA 3 = (B.M χ).pubsV 1
  -- ### [B1] J layout and registry pins
  hlay : List.ofFn B.Pb.lay = layoutJ8 B.Pb.Rt B.Pb.regs B.Pb.ids
  hsmall : ∀ q ∈ layoutJ8 B.Pb.Rt B.Pb.regs B.Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p
  huniq : ((layoutJ8 B.Pb.Rt B.Pb.regs B.Pb.ids).filterMap tvKey).Nodup
  hTpl : ∀ i ∈ B.Pb.regs, Rg.R i = some ⟨(B.Pb.Rt i).toTemplate p, Nock.Jet.Autogen.compile p (B.Pb.Rt i)⟩ ∧
    axPosB (B.Pb.Rt i) = true ∧ (B.Pb.Rt i).WellTyped p
  hnd : B.Pb.regs.Nodup
  hidx : ∀ id ∈ B.Pb.regs, B.Pb.idx id < p
  hrk : ∀ id ∈ B.Pb.regs, B.Pb.rk id ≠ (0, 0)
  hlt : ∀ id ∈ B.Pb.regs, (B.Pb.rk id).1 < ringChar (ZMod p) ∧ (B.Pb.rk id).2 < ringChar (ZMod p) ∧
    B.Pb.idx id < ringChar (ZMod p)
  -- ### [B1] claim checks and census
  hclI : ∀ χ, ∀ k : Fin 3, (isCellN (claimNoun (cJ s f r) k) = true ∨ ClaimJ9.isBigN p (claimNoun (cJ s f r) k) = true) →
    ((B.M χ).m k).1 < p
  hclR : ∀ k : Fin 3, isCellN (claimNoun (cJ s f r) k) = true → (claimNoun (cJ s f r) k).internal / 2 ^ 62 < p
  /-- [AL] CHANGED: + the primitive formula nouns. -/
  hcen' : ∀ x ∈ ClaimJ9.censusGJ9 B.Pb.toPubJ8 (cJ s f r) ++ AcceptsJ9AL.censusP B.Pb,
    x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, lenL v ≤ B.Pb.nA + 2
  hcellF : isCellN (cJ s f r).formula = true
  -- ### [B1] public lengths
  hlenC : 3 + B.Pb.regs.length + 2 * B.Pb.nC < p
  hlenA : B.Pb.nA + B.Pb.nV < p
  -- ### [J9A] axis / split
  hnAS : B.Pb.nA + B.Pb.nS < 2 ^ 57
  /-- [AL] CHANGED: the J-9 AL budget. -/
  hbud : BudJ9AL B.Pb B.rows (B.g + B.rows.N)
  hbudV : B.Pb.regs.length ≤ B.g ∧ B.Pb.nA ≤ B.rows.mb ∧ B.Pb.nA ≤ B.rows.A ∧ B.Pb.nV ≤ B.rows.AW ∧
    B.Pb.nX ≤ B.rows.AX ∧ B.Pb.nS ≤ B.rows.SP
  hAXk : ∀ χ, B.Good χ → AXChipOK δ b B.Pb.axOn B.Pb.hnX B.Pb.nodesX B.Pb.orbitX (chalsMJ8 δ χ) (B.M χ).pubsX
    (qAX δ b B.Pb.toPubJ9A (B.tr χ).toTrJ9A (chalsMJ8 δ χ) (B.M χ).pubsX)
  hSPk : ∀ χ, B.Good χ → SPChipOK δ b B.Pb.nA B.Pb.spOn B.Pb.hnS B.Pb.nodesS B.Pb.orbitS (chalsMJ8 δ χ) (B.M χ).pubsS
    (qSP δ b B.Pb.toPubJ9A (B.tr χ).toTrJ9A (chalsMJ8 δ χ) (B.M χ).pubsS)
  hlenX : B.Pb.nX + B.Pb.n < p ∧ 2 * B.Pb.nS < p
  -- ### [AL] ADDED: the ALU, present or absent
  hALk : ∀ χ, B.Good χ → ALChipOK δ b B.Pb.aluOn B.Pb.prims B.Pb.hnL B.Pb.nodesL B.Pb.orbitL B.Pb.preL
    (AluSZChipJ9.chalsALJ8 δ χ) (B.M χ).pubsL (RealIOJ9AL.qAL δ b B.Pb (B.tr χ) (AluSZChipJ9.chalsALJ8 δ χ) (B.M χ).pubsL)
  hPrim : ∀ q ∈ B.Pb.prims, Rg.R q.1 = some (Nock.Jet.Prim.primSpec q.2)
  hdisjP : ∀ q ∈ B.Pb.prims, q.1 ∉ B.Pb.regs
  hlenL : B.Pb.nL + B.Pb.n < p ∧ B.Pb.nL ≤ B.rows.AL ∧ ∀ q ∈ B.Pb.prims, q.1 < p ∧ B.Pb.idxP q.1 < p
  hndP : (B.Pb.prims.map Prod.fst).Nodup
  hrkP : ∀ q ∈ B.Pb.prims, B.Pb.rkP q.1 ≠ (0, 0)
  hltP : ∀ q ∈ B.Pb.prims, (B.Pb.rkP q.1).1 < ringChar (ZMod p) ∧ (B.Pb.rkP q.1).2 < ringChar (ZMod p) ∧
    B.Pb.idxP q.1 < ringChar (ZMod p)
  hlenCP : 3 + B.Pb.regs.length + B.Pb.prims.length + B.Pb.nL + 2 * B.Pb.nC < p
  -- ### [B3] bad events, staging, figure
  wt : ∀ e ∈ B.bad, (e.1.card : ℚ) / Fintype.card (Coins frameJ8 K) ≤ e.2
  staged : StJ9AL B.tr
  fig : p = Nock.Atoms.p → Fintype.card K = VclL.Events.cK → RowsLe31AL B.Pb → B.epsC < 1 / 2 ^ 120

end Obl

/-! ## 3. The main theorems -/

section Main
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- **Honest acceptance at every good coin, from the obligations** (field-by-field assembly). -/
theorem honest_accepted_J9AL_of_obligations (B : HonestJ9AL p K δ Rg fuel s f r)
    (O : ComplJ9ALObligations δ b B) (χ : Coins frameJ8 K) (hχ : B.Good χ) :
    AcceptsJ9AL δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g :=
  { hsatX := O.hsatX χ hχ
    hinjX := O.hinjX
    hadjX := O.hadjX
    hsatC := O.hsatC χ hχ
    hbindC := O.hbindC χ hχ
    hinjC := O.hinjC
    hadjC := O.hadjC
    hnpC := O.hnpC
    hsatW := O.hsatW χ hχ
    hbindW := O.hbindW χ hχ
    hinjW := O.hinjW
    hadjW := O.hadjW
    hkW := O.hkW
    hknW := O.hknW
    hkpW := O.hkpW
    hJk := O.hJk χ hχ
    hsatA := O.hsatA χ hχ
    hbindA := O.hbindA χ hχ
    hinjA := O.hinjA
    hadjA := O.hadjA
    hnpA := O.hnpA
    hVk := O.hVk χ hχ
    hGx := O.hGx χ hχ
    hGp := O.hGp χ hχ
    hGS := O.hGS χ hχ
    hlay := O.hlay
    hsmall := O.hsmall
    huniq := O.huniq
    hTpl := O.hTpl
    hnd := O.hnd
    hidx := O.hidx
    hrk := O.hrk
    hlt := O.hlt
    hsumC' := O.hsumC' χ hχ
    hbalA' := O.hbalA' χ hχ
    hvalA0 := O.hvalA0 χ hχ
    hfxC := O.hfxC χ hχ
    hfxA := O.hfxA χ hχ
    hclI := O.hclI χ
    hclR := O.hclR
    hcen' := O.hcen'
    hlenC := O.hlenC
    hlenA := O.hlenA
    hcellF := O.hcellF
    hnAS := O.hnAS
    hbud := O.hbud
    hbudV := O.hbudV
    hsatL := O.hsatL χ hχ
    hbindL := O.hbindL χ hχ
    hAXk := O.hAXk χ hχ
    hSPk := O.hSPk χ hχ
    hlenX := O.hlenX
    hALk := O.hALk χ hχ
    hPrim := O.hPrim
    hdisjP := O.hdisjP
    hlenL := O.hlenL
    hndP := O.hndP
    hrkP := O.hrkP
    hltP := O.hltP
    hlenCP := O.hlenCP }

open Classical in
/-- **`Pr_χ[some honest bad event] ≤ ε_c`.** -/
theorem probJ9AL_notGood_le (B : HonestJ9AL p K δ Rg fuel s f r) (O : ComplJ9ALObligations δ b B) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC := by
  have he : (Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ) =
      Finset.univ.filter fun χ : Coins frameJ8 K => ∃ e ∈ B.bad, χ ∈ e.1 := by
    ext χ
    simp [HonestJ9AL.Good]
  rw [he]
  exact prob_exists_le B.bad O.wt

open Classical in
/-- **Non-vacuity**: when `ε_c < 1` some coin is good. -/
theorem exists_good9AL (B : HonestJ9AL p K δ Rg fuel s f r) (O : ComplJ9ALObligations δ b B) (h1 : B.epsC < 1) :
    ∃ χ : Coins frameJ8 K, B.Good χ := by
  by_contra hn0
  have hn : ∀ χ : Coins frameJ8 K, ¬ B.Good χ := not_exists.mp hn0
  have hall : (Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ) = Finset.univ := by
    ext χ; simp [hn χ]
  have hp := probJ9AL_notGood_le δ b B O
  rw [hall, Finset.card_univ] at hp
  have hpos : (0 : ℚ) < Fintype.card (Coins frameJ8 K) := by exact_mod_cast Fintype.card_pos
  rw [div_self hpos.ne'] at hp
  linarith

open Classical in
/-- **J-9 AL general completeness from the obligations.** -/
theorem complJ9AL_of_obligations (B : HonestJ9AL p K δ Rg fuel s f r) (O : ComplJ9ALObligations δ b B) :
    (∀ χ, B.Good χ → AcceptsJ9AL δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ9AL B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (p = Nock.Atoms.p → Fintype.card K = VclL.Events.cK → RowsLe31AL B.Pb →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9AL δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) := by
  refine ⟨fun χ hχ => honest_accepted_J9AL_of_obligations δ b B O χ hχ,
    probJ9AL_notGood_le δ b B O, O.staged, genX_sound Rg.faithful B.hgen, fun hpG hcK hrows => ?_⟩
  have hfig := O.fig hpG hcK hrows
  have h1 : B.epsC < 1 := lt_trans hfig (by norm_num)
  obtain ⟨χ, hχ⟩ := exists_good9AL δ b B O h1
  exact ⟨hfig, χ, honest_accepted_J9AL_of_obligations δ b B O χ hχ⟩

end Main

/-! ## 4. The IFACE block -/

section Iface
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf rowsOfT)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (prims : List (ℕ × PrimOp)) (hpG : p = Nock.Atoms.p)
  (h31A : ComplJ9ARun.Rows31A (j9aDataOf p Rg Rt hgen))
  (h31 : ComplJ9ARun.Rows31A (ComplJ9ALData.j9alDataOf p Rg Rt prims hgen))

local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DL" => ComplJ9ALData.j9alDataOf p Rg Rt prims hgen
local notation "BA" => ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A
set_option quotPrecheck false

include hpG h31 in
theorem hFL : DvdOK (DL) := ComplJ9ARun.dvdOK_of_A (ComplJ9ARun.dvdA_of_rows hpG _ h31)
local notation "FL" => hFL (Rt := Rt) (hgen := hgen) (prims := prims) hpG h31
local notation "psRun" => ComplJ9ALData.primsC prims (List.map Prod.fst (J8Data.calls (DA)))
local notation "vcRun" => ComplJ9ALData.idxPOf (J8Data.cells (DA)) prims
local notation "mRun" => fun id : ℕ =>
  ((ComplJ9ALData.pcallsR (prims.map Prod.fst) (rowsOfT t)).countP fun x => x.1 = id) + 1   -- mP = c+1
local notation "tbR" y:max => AluSatRun.tblRun δ Rt prims hgen psRun vcRun mRun y
local notation "famsJL" => famsOf δ b (DL) FL (cellsL_pos Rt prims hgen) ++
  ComplJ9BOf.famsA9 δ b (DL) (DL) FL (acsL_pos Rt prims hgen)
local notation "AVL" => ComplJ9BBalF.avOf9 δ b (DL) FL (avOf δ b (DL) FL (acsL_pos Rt prims hgen))
local notation "B8L" => honestJ8Of δ b (DL) FL (cellsL_pos Rt prims hgen) (acsL_pos Rt prims hgen) AVL famsJL
-- (`abbrev`s; here `local notation`s, since the section variables are explicit.)
-- ALU terminals, n abstract (padding rows contribute 0):
--   SV n χ := ∑ i : Fin n, AluSatRows.tV δ (chalsALJ8 δ χ) (tbR (yOf δ χ)) i     (likewise SS with tS, SX with tX)

end Iface

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALObl
