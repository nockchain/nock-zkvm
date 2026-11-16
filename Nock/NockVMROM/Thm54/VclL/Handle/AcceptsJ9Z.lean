/-
  Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9Z.lean

  **The accepted-trace layer of `AcceptsJ9V`** (atom walk absent here; the present twin is
  `AcceptsJ9ZG`).  New module, additive.
  * `toMsgJ9Z` / `toMsgJ9ZA`: `toMsgJ8Z` / `toMsgJ8ZA` with `reqsC := claimRecsJ9 ++ pinRecsJ8`.
  * `AcceptsJ9ZA`: `AbsentVJ8.AcceptsJ8ZA` with `hsatX` at `pubVJ9` (every other field verbatim);
    `acceptsJ9ZA_of_V` (proof text `acceptsJ8ZA_of_V`'s).
  * The compute environments at `pubVJ9` (`envX9`) have the SAME trace as the J-8 ones (`envX9_trace`), so every
    trace readout (`stX`, `rowW`, `hdV`, the compute requests) is shared (`stX_envX9`, `hdV_envX9`, `reqsOf9_eq`).
  * Row 0 at `pubVJ9`: `row0_claim9` (the handles are the publics `0..5`), `row0_hd9` (kind / value of `claimKH`),
    `hseedJ9`, `hrealJ9`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9V

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9Z

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
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (xS xF xE)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (envCJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP (toMsgJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 St40 sum40 fpx_out v4 v5 v6 v7)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (extY_below shV_round)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (compReqsX)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8 (toMsgJ8ZA)

noncomputable section

section Accept
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`toMsgJ9Z`**: `toMsgJ8Z` with the J-9 claim records (`claimRecsJ9 ++ pinRecsJ8`). -/
def toMsgJ9Z (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) :
    MsgJ8 p K δ :=
  { toMsgJ8Z δ b Pb c χ M tr with reqsC := claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb χ }

/-- **`toMsgJ9ZA`**: `toMsgJ9Z` with no atom-walk handle read. -/
def toMsgJ9ZA (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) :
    MsgJ8 p K δ :=
  { toMsgJ9Z δ b Pb c χ M tr with wreqs := [] }

/-- **`AcceptsJ9ZA`**: `AbsentVJ8.AcceptsJ8ZA` with the compute chip at `pubVJ9`. -/
structure AcceptsJ9ZA (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) : Prop where
  -- compute
  hsatX : RAP.SatisfiesWithPreprocessing (computeChipVCLHX Pb.hn Pb.nodes b δ (chalVJ8 b χ)
    (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit) (qX δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ))
  hinjX : Function.Injective Pb.nodes
  hadjX : ∀ (i : Fin Pb.n) (hi : (i : ℕ) + 1 < Pb.n), Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = Pb.nodes i * Pb.orbit.ω
  -- the cell table
  hsatC : (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.Satisfies
    (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)
  hbindC : (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).BindsPreprocessing
    (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)
  hinjC : Function.Injective Pb.nodesC
  hadjC : ∀ (i : Fin Pb.nC) (hi : (i : ℕ) + 1 < Pb.nC), Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesC i * Pb.orbitC.ω
  hnpC : Pb.nC < ringChar (ZMod p)
  -- the J-8 walk
  hsatW : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).rap.Satisfies
    (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)
  hbindW : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).BindsPreprocessing
    (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)
  hinjW : Function.Injective Pb.nodesW
  hadjW : ∀ (i : Fin Pb.nW) (hi : (i : ℕ) + 1 < Pb.nW), Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesW i * Pb.orbitW.ω
  hkW : 1 ≤ Pb.kroots
  hknW : Pb.kroots ≤ Pb.nW
  hkpW : Pb.kroots + Pb.nW < ringChar (ZMod p)
  hJk : JGenJ8.JChipOK δ b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ)
  -- the atom table
  hsatA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
    (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  hbindA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
    (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  hinjA : Function.Injective Pb.nodesA
  hadjA : ∀ (i : Fin Pb.nA) (hi : (i : ℕ) + 1 < Pb.nA), Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesA i * Pb.orbitA.ω
  hnpA : Pb.nA < p
  -- the public balance equations
  hGx : M.ρ 3 + (Quad.mk _ (M.pubsW WalkHQ.pubXQ) (M.pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (M.pubsJ 2) (M.pubsJ 3)) =
    Quad.mk _ (M.pubsC CellHQ.pubHQ) (M.pubsC (CellHQ.pubHQ + 1))
  hGp : M.ρ 4 = Quad.mk _ (M.pubsW WalkHQ.pubPQ) (M.pubsW (WalkHQ.pubPQ + 1))
  hGS : M.ρS + ((pinCons (p := p) (K := K) Pb.regs Pb.idx).map fun r =>
      (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum + Quad.mk _ (M.pubsJ 0) (M.pubsJ 1) =
    Quad.mk _ (M.pubsA AtomChipHQ.pubMI) (M.pubsA (AtomChipHQ.pubMI + 1)) +
      Quad.mk _ (M.pubsV WalkHQ.pubPQ) (M.pubsV (WalkHQ.pubPQ + 1))
  hsumC : (M.reqsC.map fun r => (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
    Quad.mk _ (M.pubsC 0) (M.pubsC 1) + (M.xsC.map fun x => x.2 * (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x.1)⁻¹).sum
  hxneC : ∀ x ∈ M.xsC, FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x.1 ≠ 0
  hbalA : Quad.mk _ (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) =
    Quad.mk _ (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) +
      ((M.wreqs.map (liftRec (K := K) (L := 𝕂′))).map fun r =>
        (compress (AtomServedQ.acoins δ (chalsAJ8Z δ χ)) r)⁻¹).sum
  -- the cell validity's external keys
  hxC : ∀ x ∈ M.xsC, ∃ k ∈ M.vp, x.1 = ClaimVS.claimVec δ k.1 (k.2.2.2 : ZMod p) (k.2.1 : ZMod p) (k.2.2.1 : ZMod p)
  hvp0 : ∀ k ∈ M.vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar (ZMod p)
  -- the J chip's public checks and the registry pin
  hlay : List.ofFn Pb.lay = layoutJ8 Pb.Rt Pb.regs Pb.ids
  hsmall : ∀ q ∈ layoutJ8 Pb.Rt Pb.regs Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p
  huniq : ((layoutJ8 Pb.Rt Pb.regs Pb.ids).filterMap tvKey).Nodup
  hTpl : ∀ i ∈ Pb.regs, Rg i = some ⟨(Pb.Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Pb.Rt i)⟩ ∧
    axPosB (Pb.Rt i) = true ∧ (Pb.Rt i).WellTyped p
  hnd : Pb.regs.Nodup
  hidx : ∀ id ∈ Pb.regs, Pb.idx id < p
  hrk : ∀ id ∈ Pb.regs, Pb.rk id ≠ (0, 0)
  hlt : ∀ id ∈ Pb.regs, (Pb.rk id).1 < ringChar (ZMod p) ∧ (Pb.rk id).2 < ringChar (ZMod p) ∧
    Pb.idx id < ringChar (ZMod p)
  hpinC : ∀ id ∈ Pb.regs, ClaimVS.claimVec δ
    (encZY (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))
      (Nock.Jet.Autogen.compile p (Pb.Rt id))) (Pb.idx id : ZMod p)
    ((Pb.rk id).1 : ZMod p) ((Pb.rk id).2 : ZMod p) ∈ M.reqsC
  -- the atom walk ABSENT: its two `s` publics are `0`
  hV0 : M.pubsV WalkHQ.pubPQ = 0 ∧ M.pubsV (WalkHQ.pubPQ + 1) = 0

variable {δ b}

/-- **`AcceptsJ9V` at `krootsV = 0` ⇒ `AcceptsJ9ZA` at `toMsgJ9ZA`.** -/
theorem acceptsJ9ZA_of_V {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsJ9V.AcceptsJ9V δ b Pb Rg c χ M tr r g)
    (h0 : Pb.krootsV = 0) : AcceptsJ9ZA δ b Pb Rg c χ (toMsgJ9ZA δ b Pb c χ M tr) tr :=
  have hz := (AcceptsJ8V.aw_absent_iff δ b h0).1 h.hVk
  { hsatX := h.hsatX
    hinjX := h.hinjX
    hadjX := h.hadjX
    hsatC := h.hsatC
    hbindC := h.hbindC
    hinjC := h.hinjC
    hadjC := h.hadjC
    hnpC := h.hnpC
    hsatW := h.hsatW
    hbindW := h.hbindW
    hinjW := h.hinjW
    hadjW := h.hadjW
    hkW := h.hkW
    hknW := h.hknW
    hkpW := h.hkpW
    hJk := h.hJk
    hsatA := h.hsatA
    hbindA := h.hbindA
    hinjA := h.hinjA
    hadjA := h.hadjA
    hnpA := h.hnpA
    hGx := h.hGx
    hGp := h.hGp
    hGS := h.hGS
    hlay := h.hlay
    hsmall := h.hsmall
    huniq := h.huniq
    hTpl := h.hTpl
    hnd := h.hnd
    hidx := h.hidx
    hrk := h.hrk
    hlt := h.hlt
    hsumC := by
      show _ = _ + ((mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _).map _).sum
      rw [mbXs_sum δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ h.hsatA h.hbindA h.hinjA h.hadjA _ _
        (chalsAJ8Z_ok δ χ)]
      exact h.hsumC'
    hxneC := mbXs_den δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ h.hsatA _ _ (chalsAJ8Z_ok δ χ)
    hbalA := by
      show Quad.mk _ (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) =
        Quad.mk _ (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) +
          (((([] : List (Fin 5 → K))).map (liftRec (K := K) (L := 𝕂′))).map fun r =>
            (compress (AtomServedQ.acoins δ (chalsAJ8Z δ χ)) r)⁻¹).sum
      have hb := h.hbalA'
      rw [hz.2.2.1, hz.2.2.2.1, Quad.mk_zero', add_zero] at hb
      simpa using hb
    hxC := mbXs_claimVec δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _
    hvp0 := fun k hk => by
      obtain ⟨h1, h2, h3⟩ := mbVp_small δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ k hk
      exact ⟨h1, h2, by rw [ZMod.ringChar_zmod_n]; exact h3⟩
    hpinC := fun id hid => List.mem_append_right _ (List.mem_map.mpr ⟨id, hid, rfl⟩)
    hV0 := ⟨hz.2.2.2.2.1, hz.2.2.2.2.2⟩ }

end Accept

end

end Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9Z
