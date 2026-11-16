/-
  Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8G.lean

  * **`AcceptsJ8''''`** = `AcceptsJ8'''` with the J chip's five conjuncts (`hsatJ hbindJ hinjJ hnJ hadjJ`) replaced
    by `hJk : JGenJ8.JChipOK …`: the J chip PRESENT (the five conjuncts), or ABSENT (`nJ = 0` and
    `pubsJ 0 = pubsJ 1 = pubsJ 2 = pubsJ 3 = 0`, so the J terms of `hGx` / `hGS` vanish and every J list is empty).
    Every other conjunct is `AcceptsJ8'''`'s, verbatim.  `ofL` / `toL_of_pos`: the present case IS `AcceptsJ8'''`.
    `absent_layout`: in the absent case `hlay` forces `regs = ids = []`.
  * **`AcceptsJ8ZG`** / **`acceptsJ8ZG_of''''`**: `AcceptsJ8Z` / `acceptsJ8Z_of''` likewise.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
import Nock.NockVMROM.Thm54.VclL.Handle.JGenJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G

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

noncomputable section


open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L

section Accept
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`AcceptsJ8ZG`**: `AcceptsJ8Z.AcceptsJ8Z` with the J chip present or absent (`JGenJ8.JChipOK`). -/
structure AcceptsJ8ZG (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) : Prop where
  -- compute
  hsatX : RAP.SatisfiesWithPreprocessing (computeChipVCLHX Pb.hn Pb.nodes b δ (chalVJ8 b χ)
    (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb.orbit) (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ))
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
  -- the atom walk
  hsatV : (walkChipHQK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV).rap.Satisfies
    (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV)
  hbindV : (walkChipHQK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV).BindsPreprocessing
    (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV)
  hinjV : Function.Injective Pb.nodesV
  hadjV : ∀ (i : Fin Pb.nV) (hi : (i : ℕ) + 1 < Pb.nV), Pb.nodesV ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesV i * Pb.orbitV.ω
  hkV : 1 ≤ Pb.krootsV
  hknV : Pb.krootsV ≤ Pb.nV
  hkpV : Pb.krootsV + Pb.nV < ringChar (ZMod p)
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

/-- **`AcceptsJ8''''`: THE verifier's checks, the J chip present or absent.**  `AcceptsJ8'''` (the atom table at
the variant chip `atomChipHQL`) with the J chip's five conjuncts `hsatJ hbindJ hinjJ hnJ hadjJ` replaced by
`hJk : JChipOK …`: either those five, or `nJ = 0` and `pubsJ 0..3 = 0` (then `hlay` forces the empty layout,
`regs = ids = []`).  No other conjunct changes. -/
structure AcceptsJ8'''' (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (r : RowsJ8) (g : ℕ) : Prop where
  -- compute
  hsatX : RAP.SatisfiesWithPreprocessing (computeChipVCLHX Pb.hn Pb.nodes b δ (chalVJ8 b χ)
    (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb.orbit) (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ))
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
  -- the atom walk
  hsatV : (walkChipHQK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV).rap.Satisfies
    (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV)
  hbindV : (walkChipHQK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV).BindsPreprocessing
    (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV)
  hinjV : Function.Injective Pb.nodesV
  hadjV : ∀ (i : Fin Pb.nV) (hi : (i : ℕ) + 1 < Pb.nV), Pb.nodesV ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesV i * Pb.orbitV.ω
  hkV : 1 ≤ Pb.krootsV
  hknV : Pb.krootsV ≤ Pb.nV
  hkpV : Pb.krootsV + Pb.nV < ringChar (ZMod p)
  -- the public balance equations
  hGx : M.ρ 3 + (Quad.mk _ (M.pubsW WalkHQ.pubXQ) (M.pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (M.pubsJ 2) (M.pubsJ 3)) =
    Quad.mk _ (M.pubsC CellHQ.pubHQ) (M.pubsC (CellHQ.pubHQ + 1))
  hGp : M.ρ 4 = Quad.mk _ (M.pubsW WalkHQ.pubPQ) (M.pubsW (WalkHQ.pubPQ + 1))
  hGS : M.ρS + ((pinCons (p := p) (K := K) Pb.regs Pb.idx).map fun r =>
      (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum + Quad.mk _ (M.pubsJ 0) (M.pubsJ 1) =
    Quad.mk _ (M.pubsA AtomChipHQ.pubMI) (M.pubsA (AtomChipHQ.pubMI + 1)) +
      Quad.mk _ (M.pubsV WalkHQ.pubPQ) (M.pubsV (WalkHQ.pubPQ + 1))
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
  -- the cell validity: verifier-computed requests against the cell terminal and the atom g5 terminal (Q2 S2)
  hsumC' : ((claimRecsJ8 δ χ c M.m ++ pinRecsJ8 δ Pb χ).map fun r => (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
    Quad.mk (algebraMap (ZMod p) K δ) (M.pubsC 0) (M.pubsC 1) + Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubMB) (M.pubsA (AtomChipHQ.pubMB + 1))
  -- the atom export: provides = old-export consumes + the atom walk's handle reads (Q1, `pubsV 4/5`)
  hbalA' : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) =
    Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) +
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV WalkHQ.pubXQ) (M.pubsV (WalkHQ.pubXQ + 1))
  -- the atom table's validity terminal (Q2 S3)
  hvalA0 : M.pubsA 0 = 0 ∧ M.pubsA 1 = 0
  -- the fingerprint-export links (Q1): cell ↔ J-8 walk, atom table ↔ atom walk
  hfxC : M.pubsC 2 = M.pubsW 0 ∧ M.pubsC 3 = M.pubsW 1
  hfxA : M.pubsA 2 = M.pubsV 0 ∧ M.pubsA 3 = M.pubsV 1
  hclA : ∀ k : Fin 3, ∀ v, claimNoun c k = .atom v → v < p
  hclI : ∀ k : Fin 3, isCellN (claimNoun c k) = true → (M.m k).1 < p
  hclR : ∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < p
  -- the census size check on the registered and claim cell nouns
  hcen : ∀ x ∈ censusG Pb c, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, v < p
  -- public lengths
  hlenC : 3 + Pb.regs.length + 2 * Pb.nC < p
  hlenA : Pb.nA + Pb.nV < p
  hcellF : isCellN c.formula = true
  hnA62 : Pb.nA ≤ 2 ^ 62
  hbud : RealIOJ8.BudJ8 Pb r (g + r.N)
  hbudV : Pb.regs.length ≤ g ∧ Pb.nA ≤ r.mb ∧ Pb.nA ≤ r.A ∧ Pb.nV ≤ r.AW
  -- the atom table at the variant chip (`AcceptsJ8'''`)
  hsatL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
    (qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  hbindL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
    (qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)

/-- **`AcceptsJ8''''` ⇒ `AcceptsJ8ZG` at `toMsgJ8Z`** (as `acceptsJ8Z_of''`). -/
theorem acceptsJ8ZG_of'''' {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsJ8'''' δ b Pb Rg c χ M tr r g) :
    AcceptsJ8ZG δ b Pb Rg c χ (toMsgJ8Z δ b Pb c χ M tr) tr where
  hsatX := h.hsatX
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
  hsatV := h.hsatV
  hbindV := h.hbindV
  hinjV := h.hinjV
  hadjV := h.hadjV
  hkV := h.hkV
  hknV := h.hknV
  hkpV := h.hkpV
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
    show _ = _ + (((ServeH.walkXReqs b Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV _).map _).map _).sum
    rw [List.map_map]
    refine h.hbalA'.trans ?_
    congr 1
    exact (WalkTeleJ8.walkHQK_reqs_sumQ δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV _
      h.hsatV h.hbindV h.hinjV h.hadjV).symm
  hxC := mbXs_claimVec δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _
  hvp0 := fun k hk => by
    obtain ⟨h1, h2, h3⟩ := mbVp_small δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ k hk
    exact ⟨h1, h2, by rw [ZMod.ringChar_zmod_n]; exact h3⟩
  hpinC := fun id hid => List.mem_append_right _ (List.mem_map.mpr ⟨id, hid, rfl⟩)

/-- **Present case**: `AcceptsJ8''''` with a non-empty J table is `AcceptsJ8'''`. -/
theorem toL_of_pos {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsJ8'''' δ b Pb Rg c χ M tr r g)
    (hpos : 0 < Pb.nJ) : AcceptsJ8''' δ b Pb Rg c χ M tr r g :=
  have hJ := JGenJ8.present_of_pos h.hJk hpos
  { toPP :=
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
        hsatA := h.hsatA
        hbindA := h.hbindA
        hinjA := h.hinjA
        hadjA := h.hadjA
        hnpA := h.hnpA
        hsatV := h.hsatV
        hbindV := h.hbindV
        hinjV := h.hinjV
        hadjV := h.hadjV
        hkV := h.hkV
        hknV := h.hknV
        hkpV := h.hkpV
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
        hsumC' := h.hsumC'
        hbalA' := h.hbalA'
        hvalA0 := h.hvalA0
        hfxC := h.hfxC
        hfxA := h.hfxA
        hclA := h.hclA
        hclI := h.hclI
        hclR := h.hclR
        hcen := h.hcen
        hlenC := h.hlenC
        hlenA := h.hlenA
        hcellF := h.hcellF
        hnA62 := h.hnA62
        hbud := h.hbud
        hbudV := h.hbudV
        hsatJ := hJ.1
        hbindJ := hJ.2.1
        hinjJ := hJ.2.2.1
        hnJ := hJ.2.2.2.1
        hadjJ := hJ.2.2.2.2 }
    hsatL := h.hsatL
    hbindL := h.hbindL }

/-- **`AcceptsJ8'''` is the present case of `AcceptsJ8''''`.** -/
theorem ofL {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsJ8''' δ b Pb Rg c χ M tr r g) :
    AcceptsJ8'''' δ b Pb Rg c χ M tr r g :=
  { hsatX := h.toPP.hsatX
    hinjX := h.toPP.hinjX
    hadjX := h.toPP.hadjX
    hsatC := h.toPP.hsatC
    hbindC := h.toPP.hbindC
    hinjC := h.toPP.hinjC
    hadjC := h.toPP.hadjC
    hnpC := h.toPP.hnpC
    hsatW := h.toPP.hsatW
    hbindW := h.toPP.hbindW
    hinjW := h.toPP.hinjW
    hadjW := h.toPP.hadjW
    hkW := h.toPP.hkW
    hknW := h.toPP.hknW
    hkpW := h.toPP.hkpW
    hsatA := h.toPP.hsatA
    hbindA := h.toPP.hbindA
    hinjA := h.toPP.hinjA
    hadjA := h.toPP.hadjA
    hnpA := h.toPP.hnpA
    hsatV := h.toPP.hsatV
    hbindV := h.toPP.hbindV
    hinjV := h.toPP.hinjV
    hadjV := h.toPP.hadjV
    hkV := h.toPP.hkV
    hknV := h.toPP.hknV
    hkpV := h.toPP.hkpV
    hGx := h.toPP.hGx
    hGp := h.toPP.hGp
    hGS := h.toPP.hGS
    hlay := h.toPP.hlay
    hsmall := h.toPP.hsmall
    huniq := h.toPP.huniq
    hTpl := h.toPP.hTpl
    hnd := h.toPP.hnd
    hidx := h.toPP.hidx
    hrk := h.toPP.hrk
    hlt := h.toPP.hlt
    hsumC' := h.toPP.hsumC'
    hbalA' := h.toPP.hbalA'
    hvalA0 := h.toPP.hvalA0
    hfxC := h.toPP.hfxC
    hfxA := h.toPP.hfxA
    hclA := h.toPP.hclA
    hclI := h.toPP.hclI
    hclR := h.toPP.hclR
    hcen := h.toPP.hcen
    hlenC := h.toPP.hlenC
    hlenA := h.toPP.hlenA
    hcellF := h.toPP.hcellF
    hnA62 := h.toPP.hnA62
    hbud := h.toPP.hbud
    hbudV := h.toPP.hbudV
    hJk := Or.inl ⟨h.toPP.hsatJ, h.toPP.hbindJ, h.toPP.hinjJ, h.toPP.hnJ, h.toPP.hadjJ⟩
    hsatL := h.hsatL
    hbindL := h.hbindL }

/-- **The absent case has the empty layout**: `nJ = 0` and `hlay` give `regs = []` and `ids = []` (and conversely
the empty registry with no call forces `nJ = 0`, so the J chip is absent exactly when the layout is empty). -/
theorem absent_layout {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsJ8'''' δ b Pb Rg c χ M tr r g)
    (h0 : Pb.nJ = 0) : Pb.regs = [] ∧ Pb.ids = [] := by
  have hl := h.hlay
  have hlen := congrArg List.length hl
  rw [List.length_ofFn, h0, Nock.Jet.ChipJ8.layoutJ8, List.length_append, List.length_map] at hlen
  refine ⟨List.eq_nil_of_length_eq_zero (by omega), ?_⟩
  cases hid : Pb.ids with
  | nil => rfl
  | cons i is =>
    rw [hid] at hlen
    simp [Nock.Jet.ChipJ8.blocks, Nock.Jet.ChipJ8.blockPre] at hlen

theorem nJ_zero_of_empty {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsJ8'''' δ b Pb Rg c χ M tr r g)
    (hreg : Pb.regs = []) (hids : Pb.ids = []) : Pb.nJ = 0 := by
  have hlen := congrArg List.length h.hlay
  rw [hreg, hids, List.length_ofFn] at hlen
  simpa [Nock.Jet.ChipJ8.layoutJ8, Nock.Jet.ChipJ8.blocks] using hlen

end Accept

end

end Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G
