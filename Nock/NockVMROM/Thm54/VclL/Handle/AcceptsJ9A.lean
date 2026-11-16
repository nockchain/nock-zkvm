/-
  Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9A.lean

Against `AcceptsJ9V` (49 fields):
  * CHANGED (4): `hsatX` (the twin RAP `computeChipVCLHX9`, `qX9`), `hGp` (+ the axis path consume), `hGS` (+ the
    axis net service terminal on the left, + the split limb provides on the right), `hnA62 → hnAS`
    (`Pb.nA + Pb.nS < 2^57`); `hbud → BudJ9A`, `hbudV` (+ `nX ≤ AX ∧ nS ≤ SP`).
  * ADDED (3): `hAXk : AXChipOK`, `hSPk : SPChipOK`, `hlenX`.
  * every other field verbatim (at `Pb.toPubJ8`, `M.toMsgJ8'`, `tr.toJ8`, `r.toRowsJ8`): machine-checked by
    `AcceptsJ9A.of_V`, which builds an `AcceptsJ9A` from an `AcceptsJ9V` at the projections, taking only the
    changed / added pieces as arguments (every verbatim field is a bare projection of the `AcceptsJ9V`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9V
import Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A

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


open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9

open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (computeChipVCLHX9)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9V (AcceptsJ9V)


section Accept
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The axis chip, present or absent** (R8: absence is a public flag; the `AWChipOK` precedent).  Present:
`axOn = true` and the chip's five conjuncts.  Absent: `axOn = false` and the four axis publics (`pubAXs, pubAXp` and
`+1`) are `0`.  A1 item: presence requires the public flag. -/
def AXChipOK (axOn : Bool) {hX nX : ℕ} (hnX : 0 < nX) (nodesX : Fin nX → ZMod p)
    (orbitX : StrictOrbitDomain (ZMod p) 3 hX) (chalsX pubsX : ℕ → K)
    (QX : Fin (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).rap.w → (ZMod p)[X]) : Prop :=
  (axOn = true ∧ (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).rap.Satisfies QX ∧
      (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).BindsPreprocessing QX ∧
      Function.Injective nodesX ∧
      (∀ (i : Fin nX) (hi : (i : ℕ) + 1 < nX), nodesX ⟨(i : ℕ) + 1, hi⟩ = nodesX i * orbitX.ω) ∧
      nX < p) ∨
    (axOn = false ∧ pubsX AxisChipJ9.pubAXs = 0 ∧ pubsX (AxisChipJ9.pubAXs + 1) = 0 ∧
      pubsX AxisChipJ9.pubAXp = 0 ∧ pubsX (AxisChipJ9.pubAXp + 1) = 0)

/-- **The split chip, present or absent** (`nA` the verifier's `pubNA`, a template parameter).  Present:
`spOn = true` and the chip's five conjuncts.  Absent: `spOn = false` and the service terminal `pubSPs` (and `+1`) is
`0`.  A1 item: presence requires the public flag. -/
def SPChipOK (nA : ℕ) (spOn : Bool) {hS nS : ℕ} (hnS : 0 < nS) (nodesS : Fin nS → ZMod p)
    (orbitS : StrictOrbitDomain (ZMod p) 3 hS) (chalsS pubsS : ℕ → K)
    (QS : Fin (SplitChipJ9.splitChipJ9 δ nA b hnS nodesS orbitS chalsS pubsS).rap.w → (ZMod p)[X]) : Prop :=
  (spOn = true ∧ (SplitChipJ9.splitChipJ9 δ nA b hnS nodesS orbitS chalsS pubsS).rap.Satisfies QS ∧
      (SplitChipJ9.splitChipJ9 δ nA b hnS nodesS orbitS chalsS pubsS).BindsPreprocessing QS ∧
      Function.Injective nodesS ∧
      (∀ (i : Fin nS) (hi : (i : ℕ) + 1 < nS), nodesS ⟨(i : ℕ) + 1, hi⟩ = nodesS i * orbitS.ω) ∧
      nS < p) ∨
    (spOn = false ∧ pubsS SplitChipJ9.pubSPs = 0 ∧ pubsS (SplitChipJ9.pubSPs + 1) = 0)

/-- **`AcceptsJ9A`** (J-9 A twin of `AcceptsJ9V`, see the module header). -/
structure AcceptsJ9A (Pb : PubJ9A p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ9A' p K δ) (tr : TrJ9A (ZMod p)) (r : RowsJ9A) (g : ℕ) : Prop where
  -- compute: CHANGED, the twin RAP
  hsatX : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 Pb.hn Pb.nodes b δ (chalVJ8 b χ)
    (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit) (qX9 δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ))
  hinjX : Function.Injective Pb.nodes
  hadjX : ∀ (i : Fin Pb.n) (hi : (i : ℕ) + 1 < Pb.n), Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = Pb.nodes i * Pb.orbit.ω
  -- the cell table
  hsatC : (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.Satisfies
    (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC)
  hbindC : (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).BindsPreprocessing
    (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC)
  hinjC : Function.Injective Pb.nodesC
  hadjC : ∀ (i : Fin Pb.nC) (hi : (i : ℕ) + 1 < Pb.nC), Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesC i * Pb.orbitC.ω
  hnpC : Pb.nC < ringChar (ZMod p)
  -- the J-8 walk
  hsatW : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).rap.Satisfies
    (qW δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsW)
  hbindW : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).BindsPreprocessing
    (qW δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsW)
  hinjW : Function.Injective Pb.nodesW
  hadjW : ∀ (i : Fin Pb.nW) (hi : (i : ℕ) + 1 < Pb.nW), Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesW i * Pb.orbitW.ω
  hkW : 1 ≤ Pb.kroots
  hknW : Pb.kroots ≤ Pb.nW
  hkpW : Pb.kroots + Pb.nW < ringChar (ZMod p)

  hJk : JGenJ8.JChipOK δ b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay
    (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ)
  -- the atom table
  hsatA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
    (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)
  hbindA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
    (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)
  hinjA : Function.Injective Pb.nodesA
  hadjA : ∀ (i : Fin Pb.nA) (hi : (i : ℕ) + 1 < Pb.nA), Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesA i * Pb.orbitA.ω
  hnpA : Pb.nA < p
  -- the atom walk: PRESENT or ABSENT
  hVk : AWChipOK δ b Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
    (qV δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsV)
  -- the public balance equations
  hGx : M.ρ 3 + (Quad.mk _ (M.pubsW WalkHQ.pubXQ) (M.pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (M.pubsJ 2) (M.pubsJ 3)) =
    Quad.mk _ (M.pubsC CellHQ.pubHQ) (M.pubsC (CellHQ.pubHQ + 1))
  -- CHANGED: the axis chip consumes path records
  hGp : M.ρ 4 + Quad.mk _ (M.pubsX AxisChipJ9.pubAXp) (M.pubsX (AxisChipJ9.pubAXp + 1)) =
    Quad.mk _ (M.pubsW WalkHQ.pubPQ) (M.pubsW (WalkHQ.pubPQ + 1))
  -- CHANGED: + the axis net service terminal (left), + the split limb provides (right)
  hGS : M.ρS + ((pinCons (p := p) (K := K) Pb.regs Pb.idx).map fun r =>
      (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum + Quad.mk _ (M.pubsJ 0) (M.pubsJ 1) +
      Quad.mk _ (M.pubsX AxisChipJ9.pubAXs) (M.pubsX (AxisChipJ9.pubAXs + 1)) =
    Quad.mk _ (M.pubsA AtomChipHQ.pubMI) (M.pubsA (AtomChipHQ.pubMI + 1)) +
      Quad.mk _ (M.pubsV WalkHQ.pubPQ) (M.pubsV (WalkHQ.pubPQ + 1)) +
      Quad.mk _ (M.pubsS SplitChipJ9.pubSPs) (M.pubsS (SplitChipJ9.pubSPs + 1))
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
  -- the cell validity
  hsumC' : ((claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb.toPubJ8 χ).map fun r => (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
    Quad.mk (algebraMap (ZMod p) K δ) (M.pubsC 0) (M.pubsC 1) + Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubMB) (M.pubsA (AtomChipHQ.pubMB + 1))
  -- the atom export
  hbalA' : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) =
    Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) +
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV WalkHQ.pubXQ) (M.pubsV (WalkHQ.pubXQ + 1))
  hvalA0 : M.pubsA 0 = 0 ∧ M.pubsA 1 = 0
  hfxC : M.pubsC 2 = M.pubsW 0 ∧ M.pubsC 3 = M.pubsW 1
  hfxA : M.pubsA 2 = M.pubsV 0 ∧ M.pubsA 3 = M.pubsV 1
  -- the claim checks
  hclI : ∀ k : Fin 3, (isCellN (claimNoun c k) = true ∨ isBigN p (claimNoun c k) = true) → (M.m k).1 < p
  hclR : ∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < p
  hcen' : ∀ x ∈ censusGJ9 Pb.toPubJ8 c, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, lenL v ≤ Pb.nA + 2
  -- public lengths
  hlenC : 3 + Pb.regs.length + 2 * Pb.nC < p
  hlenA : Pb.nA + Pb.nV < p
  hcellF : isCellN c.formula = true
  -- CHANGED: replaces `hnA62 : Pb.nA ≤ 2 ^ 62`
  hnAS : Pb.nA + Pb.nS < 2 ^ 57
  -- CHANGED: the J-9 A budget
  hbud : BudJ9A Pb r (g + r.N)
  -- CHANGED: + the axis and split row parameters
  hbudV : Pb.regs.length ≤ g ∧ Pb.nA ≤ r.mb ∧ Pb.nA ≤ r.A ∧ Pb.nV ≤ r.AW ∧ Pb.nX ≤ r.AX ∧ Pb.nS ≤ r.SP
  -- the atom table at the variant chip
  hsatL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
    (qAL δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)
  hbindL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
    (qAL δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)
  -- ADDED: the axis chip, present or absent
  hAXk : AXChipOK δ b Pb.axOn Pb.hnX Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
    (qAX δ b Pb tr (chalsMJ8 δ χ) M.pubsX)
  -- ADDED: the split chip, present or absent
  hSPk : SPChipOK δ b Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS
    (qSP δ b Pb tr (chalsMJ8 δ χ) M.pubsS)
  -- ADDED: the LogUp counts for `hcount`
  hlenX : Pb.nX + Pb.n < p ∧ 2 * Pb.nS < p


/-- `AcceptsJ9V` together with the twin chip's satisfaction `hsatX` gives `AcceptsJ9A`. -/
theorem AcceptsJ9A.of_V {Pb : PubJ9A p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9A' p K δ} {tr : TrJ9A (ZMod p)} {r : RowsJ9A} {g : ℕ}
    (h : AcceptsJ9V δ b Pb.toPubJ8 Rg c χ M.toMsgJ8' tr.toJ8 r.toRowsJ8 g)
    (hsatX : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 Pb.hn Pb.nodes b δ (chalVJ8 b χ)
      (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit) (qX9 δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)))
    (hGp : M.ρ 4 + Quad.mk _ (M.pubsX AxisChipJ9.pubAXp) (M.pubsX (AxisChipJ9.pubAXp + 1)) =
      Quad.mk _ (M.pubsW WalkHQ.pubPQ) (M.pubsW (WalkHQ.pubPQ + 1)))
    (hGS : M.ρS + ((pinCons (p := p) (K := K) Pb.regs Pb.idx).map fun r =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum + Quad.mk _ (M.pubsJ 0) (M.pubsJ 1) +
        Quad.mk _ (M.pubsX AxisChipJ9.pubAXs) (M.pubsX (AxisChipJ9.pubAXs + 1)) =
      Quad.mk _ (M.pubsA AtomChipHQ.pubMI) (M.pubsA (AtomChipHQ.pubMI + 1)) +
        Quad.mk _ (M.pubsV WalkHQ.pubPQ) (M.pubsV (WalkHQ.pubPQ + 1)) +
        Quad.mk _ (M.pubsS SplitChipJ9.pubSPs) (M.pubsS (SplitChipJ9.pubSPs + 1)))
    (hnAS : Pb.nA + Pb.nS < 2 ^ 57) (hbud : BudJ9A Pb r (g + r.N))
    (hbudV : Pb.regs.length ≤ g ∧ Pb.nA ≤ r.mb ∧ Pb.nA ≤ r.A ∧ Pb.nV ≤ r.AW ∧ Pb.nX ≤ r.AX ∧ Pb.nS ≤ r.SP)
    (hAXk : AXChipOK δ b Pb.axOn Pb.hnX Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
      (qAX δ b Pb tr (chalsMJ8 δ χ) M.pubsX))
    (hSPk : SPChipOK δ b Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS
      (qSP δ b Pb tr (chalsMJ8 δ χ) M.pubsS))
    (hlenX : Pb.nX + Pb.n < p ∧ 2 * Pb.nS < p) :
    AcceptsJ9A δ b Pb Rg c χ M tr r g where
  hsatX := hsatX
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
  hVk := h.hVk
  hGx := h.hGx
  hGp := hGp
  hGS := hGS
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
  hclI := h.hclI
  hclR := h.hclR
  hcen' := h.hcen'
  hlenC := h.hlenC
  hlenA := h.hlenA
  hcellF := h.hcellF
  hnAS := hnAS
  hbud := hbud
  hbudV := hbudV
  hsatL := h.hsatL
  hbindL := h.hbindL
  hAXk := hAXk
  hSPk := hSPk
  hlenX := hlenX

end Accept

end

end Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A
#print axioms AcceptsJ9A.of_V
#print axioms AcceptsJ9A
end Axioms
