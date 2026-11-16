/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplGeneric.lean

Each group is a structure with the SAME field statements.
  * `toObl` / `ofObl`: the two directions of the regrouping (a field shuffle), so `ComplGenericObligations` and
    `ComplJ8Obligations` are logically equivalent.
  * `complGeneric_j8`: `complJ8_of_obligations` with `AcceptsJ8V` replaced by
    `AcceptsGeneric (J8providers) claimJ8 budgetJ8` (through `acceptsGeneric_j8_iff`), from `ComplGenericObligations`.

  Disclosed reduction: the generic balance via `Ps.flatMap` / `tabs_balance` is NOT built
  here; the balance group is the three J-8 `balG balV balF` fields as stated.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
import Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ8Iff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplGeneric

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
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL toHQ)
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
open Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX (HdlOK isPair PairOK hk hv)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestRowX (SmallX)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ8

noncomputable section

section Obl
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **Compute provider** (12 fields): the hypotheses of `computeChipVCLHX_honest_sat`, the walk publics, the
accumulator terminals and the good-coin conditions. -/
structure ComputeCompl (B : HonestJ8 p K δ Rg fuel s f r) : Prop where
  hH : HdlOK (ringChar (ZMod p)) B.H
  hpair : ∀ u, InTree B.t u → isPair B.H (rowOfSkelX u.label) → PairOK (F := ZMod p) (B.pd (rowOfSkelX u.label))
  hN : B.Pb.n = B.W.length
  hinjX : Function.Injective B.Pb.nodes
  hadjX : ∀ (i : Fin B.Pb.n) (hi : (i : ℕ) + 1 < B.Pb.n),
    B.Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = B.Pb.nodes i * B.Pb.orbit.ω
  htrC : ∀ χ, qX δ b B.Pb (B.tr χ) (chalVJ8 b χ) (pubJ δ b B χ) =
    VclL.HonestTraceX.polyX b δ B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ)
      (VclL.HonestTraceX.lnW (αJ b χ)) (VclL.HonestTraceX.cntW B.W (αJ b χ))
      (VclL.HonestTraceX.accW (F := ZMod p) B.H B.W (αJ b χ) (γJ b χ)) B.Pb.nodes
      (computeChipVCLHX B.Pb.hn B.Pb.nodes b δ (chalVJ8 b χ) (pubJ δ b B χ) B.Pb.orbit).rap.w
  hpIC : ∀ χ, limbVal b (pubJ δ b B χ) pubIC = αJ b χ
  hpS : ∀ χ, limbVal b (pubJ δ b B χ) pubSeed =
    VclL.HonestTraceX.curW (F := ZMod p) B.H B.W (γJ b χ) 1 * αJ b χ
  hpO : ∀ χ, limbVal b (pubJ δ b B χ) pubOut = 0
  hpub : ∀ χ, pubJ δ b B χ 0 = hk B.H s ∧ pubJ δ b B χ 1 = hv B.H s ∧ pubJ δ b B χ 2 = hk B.H f ∧
    pubJ δ b B χ 3 = hv B.H f ∧ pubJ δ b B χ 4 = hk B.H r ∧ pubJ δ b B χ 5 = hv B.H r
  hρ : ∀ χ, ∀ a < 6, ∀ k : Fin 3, pubJ δ b B χ (VclL.HonestTraceX.pubOfA a + k) =
    coord b (VclL.HonestTraceX.accV b δ B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ) a B.Pb.n) k
  goodC : ∀ χ, B.Good χ → B.W.length ≤ orderOf (αJ b χ) ∧
    ∀ j < B.Pb.n, ∀ S ∈ Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := ZMod p),
      HonestSlotX.dVal b δ S (VclL.HonestTraceX.env0 B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ) j) ≠ 0 ∨
        HonestSlotX.aVal b δ S (VclL.HonestTraceX.env0 B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ) j) = 0

/-- **Cell provider** (2 fields). -/
structure CellCompl (B : HonestJ8 p K δ Rg fuel s f r) : Prop where
  cellOK : ∀ χ, B.Good χ →
    (cellChipHQKW δ b B.Pb.hnC B.Pb.nodesC B.Pb.orbitC (chalsMJ8 δ χ) (B.M χ).pubsC).rap.Satisfies
      (qM δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsC) ∧
    (cellChipHQKW δ b B.Pb.hnC B.Pb.nodesC B.Pb.orbitC (chalsMJ8 δ χ) (B.M χ).pubsC).BindsPreprocessing
      (qM δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsC)
  cellNodes : Function.Injective B.Pb.nodesC ∧
    (∀ (i : Fin B.Pb.nC) (hi : (i : ℕ) + 1 < B.Pb.nC),
      B.Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = B.Pb.nodesC i * B.Pb.orbitC.ω) ∧ B.Pb.nC < ringChar (ZMod p)

/-- **J-8 walk provider** (2 fields). -/
structure WalkCompl (B : HonestJ8 p K δ Rg fuel s f r) : Prop where
  walkOK : ∀ χ, B.Good χ →
    (walkChipJ8 δ B.Pb.kroots b B.Pb.hnW B.Pb.nodesW B.Pb.orbitW (chalsMJ8 δ χ) (B.M χ).pubsW).rap.Satisfies
      (qW δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsW) ∧
    (walkChipJ8 δ B.Pb.kroots b B.Pb.hnW B.Pb.nodesW B.Pb.orbitW (chalsMJ8 δ χ) (B.M χ).pubsW).BindsPreprocessing
      (qW δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsW)
  walkNodes : Function.Injective B.Pb.nodesW ∧
    (∀ (i : Fin B.Pb.nW) (hi : (i : ℕ) + 1 < B.Pb.nW),
      B.Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = B.Pb.nodesW i * B.Pb.orbitW.ω) ∧
    1 ≤ B.Pb.kroots ∧ B.Pb.kroots ≤ B.Pb.nW ∧ B.Pb.kroots + B.Pb.nW < ringChar (ZMod p)

/-- **J provider** (2 fields: the chip, present or absent, and the registry statics). -/
structure JetCompl (B : HonestJ8 p K δ Rg fuel s f r) : Prop where
  jOK : ∀ χ, B.Good χ → JGenJ8.JChipOK δ b B.Pb.nodesJ B.Pb.orbitJ (chalsJJ8 χ) (B.M χ).pubsJ B.Pb.lay
    (qJ δ b B.Pb (B.tr χ) (chalsJJ8 χ) (B.M χ).pubsJ)
  stat : List.ofFn B.Pb.lay = layoutJ8 B.Pb.Rt B.Pb.regs B.Pb.ids ∧
    (∀ q ∈ layoutJ8 B.Pb.Rt B.Pb.regs B.Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) ∧
    ((layoutJ8 B.Pb.Rt B.Pb.regs B.Pb.ids).filterMap tvKey).Nodup ∧
    (∀ i ∈ B.Pb.regs, Rg.R i = some ⟨(B.Pb.Rt i).toTemplate p, Nock.Jet.Autogen.compile p (B.Pb.Rt i)⟩ ∧
      axPosB (B.Pb.Rt i) = true ∧ (B.Pb.Rt i).WellTyped p) ∧
    B.Pb.regs.Nodup ∧ (∀ id ∈ B.Pb.regs, B.Pb.idx id < p) ∧ (∀ id ∈ B.Pb.regs, B.Pb.rk id ≠ (0, 0)) ∧
    (∀ id ∈ B.Pb.regs, (B.Pb.rk id).1 < ringChar (ZMod p) ∧ (B.Pb.rk id).2 < ringChar (ZMod p) ∧
      B.Pb.idx id < ringChar (ZMod p))

/-- **Atom provider** (2 fields: both chip views, and the node conditions). -/
structure AtomCompl (B : HonestJ8 p K δ Rg fuel s f r) : Prop where
  atomOK : ∀ χ, B.Good χ →
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (qA δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (qA δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (qAL δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (qAL δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA)
  atomNodes : Function.Injective B.Pb.nodesA ∧
    (∀ (i : Fin B.Pb.nA) (hi : (i : ℕ) + 1 < B.Pb.nA),
      B.Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = B.Pb.nodesA i * B.Pb.orbitA.ω) ∧ B.Pb.nA < p

/-- **Atom-walk provider** (1 field: present or absent). -/
structure AtomWalkCompl (B : HonestJ8 p K δ Rg fuel s f r) : Prop where
  awOK : ∀ χ, B.Good χ → AWChipOK δ b B.Pb.krootsV B.Pb.hnV B.Pb.nodesV B.Pb.orbitV (chalsAJ8Z δ χ) (B.M χ).pubsV
    (qV δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsV)

/-- **The cross-table balances** (3 fields: export/path/service, validity/atom handle/atom validity, fingerprint
links). -/
structure BalCompl (B : HonestJ8 p K δ Rg fuel s f r) : Prop where
  balG : ∀ χ, B.Good χ →
    (B.M χ).ρ 3 + (Quad.mk _ ((B.M χ).pubsW WalkHQ.pubXQ) ((B.M χ).pubsW (WalkHQ.pubXQ + 1)) +
        Quad.mk _ ((B.M χ).pubsJ 2) ((B.M χ).pubsJ 3)) =
      Quad.mk _ ((B.M χ).pubsC CellHQ.pubHQ) ((B.M χ).pubsC (CellHQ.pubHQ + 1)) ∧
    (B.M χ).ρ 4 = Quad.mk _ ((B.M χ).pubsW WalkHQ.pubPQ) ((B.M χ).pubsW (WalkHQ.pubPQ + 1)) ∧
    (B.M χ).ρS + ((pinCons (p := p) (K := K) B.Pb.regs B.Pb.idx).map fun x =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
        Quad.mk _ ((B.M χ).pubsJ 0) ((B.M χ).pubsJ 1) =
      Quad.mk _ ((B.M χ).pubsA AtomChipHQ.pubMI) ((B.M χ).pubsA (AtomChipHQ.pubMI + 1)) +
        Quad.mk _ ((B.M χ).pubsV WalkHQ.pubPQ) ((B.M χ).pubsV (WalkHQ.pubPQ + 1))
  balV : ∀ χ, B.Good χ →
    ((claimRecsJ8 δ χ (cJ s f r) (B.M χ).m ++ pinRecsJ8 δ B.Pb χ).map fun x => (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x)⁻¹).sum =
      Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsC 0) ((B.M χ).pubsC 1) +
        Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsA AtomChipHQ.pubMB) ((B.M χ).pubsA (AtomChipHQ.pubMB + 1)) ∧
    Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsA CellHQ.pubHQ) ((B.M χ).pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsA AtomChipHQ.pubC) ((B.M χ).pubsA (AtomChipHQ.pubC + 1)) +
        Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsV WalkHQ.pubXQ) ((B.M χ).pubsV (WalkHQ.pubXQ + 1)) ∧
    ((B.M χ).pubsA 0 = 0 ∧ (B.M χ).pubsA 1 = 0)
  balF : ∀ χ, B.Good χ →
    ((B.M χ).pubsC 2 = (B.M χ).pubsW 0 ∧ (B.M χ).pubsC 3 = (B.M χ).pubsW 1) ∧
    ((B.M χ).pubsA 2 = (B.M χ).pubsV 0 ∧ (B.M χ).pubsA 3 = (B.M χ).pubsV 1)

/-- **Claim component** (`claim`: `hclA hclI hclR hcen hcellF`). -/
def ClaimCompl (B : HonestJ8 p K δ Rg fuel s f r) : Prop :=
  ∀ χ : Coins frameJ8 K, (∀ k : Fin 3, ∀ v, claimNoun (cJ s f r) k = .atom v → v < p) ∧
    (∀ k : Fin 3, isCellN (claimNoun (cJ s f r) k) = true → ((B.M χ).m k).1 < p) ∧
    (∀ k : Fin 3, isCellN (claimNoun (cJ s f r) k) = true → (claimNoun (cJ s f r) k).internal / 2 ^ 62 < p) ∧
    (∀ x ∈ censusG B.Pb (cJ s f r), x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, v < p) ∧
    isCellN (cJ s f r).formula = true

/-- **Size and budget component** (`budget`: `hlenC hlenA hnA62 hbud hbudV`). -/
def BudgetCompl (B : HonestJ8 p K δ Rg fuel s f r) : Prop :=
  3 + B.Pb.regs.length + 2 * B.Pb.nC < p ∧ B.Pb.nA + B.Pb.nV < p ∧ B.Pb.nA ≤ 2 ^ 62 ∧
    RealIOJ8.BudJ8 B.Pb B.rows (B.g + B.rows.N) ∧
    (B.Pb.regs.length ≤ B.g ∧ B.Pb.nA ≤ B.rows.mb ∧ B.Pb.nA ≤ B.rows.A ∧ B.Pb.nV ≤ B.rows.AW)

/-- **The generic completeness obligations**: `∀ P ∈ Ps, P.compl`, the balances, the claim and budget
components, and the shared `wt`, `staged`, `fig`, at the J-8 provider list.  The same 29 facts as
`ComplJ8Obligations`, listed by provider. -/
structure ComplGenericObligations (B : HonestJ8 p K δ Rg fuel s f r) : Prop where
  compute : ComputeCompl δ b B
  cell : CellCompl δ b B
  walk : WalkCompl δ b B
  jet : JetCompl δ b B
  atom : AtomCompl δ b B
  atomWalk : AtomWalkCompl δ b B
  balances : BalCompl δ b B
  claim : ClaimCompl δ B
  budget : BudgetCompl δ B
  wt : ∀ e ∈ B.bad, (e.1.card : ℚ) / Fintype.card (Coins frameJ8 K) ≤ e.2
  staged : StJ8 B.tr
  fig : p = Nock.Atoms.p → Fintype.card K = VclL.Events.cK → RowsLe31 B.Pb → B.epsC < 1 / 2 ^ 120


theorem ofObl {B : HonestJ8 p K δ Rg fuel s f r} (O : ComplJ8Obligations δ b B) :
    ComplGenericObligations δ b B where
  compute := ⟨O.hH, O.hpair, O.hN, O.hinjX, O.hadjX, O.htrC, O.hpIC, O.hpS, O.hpO, O.hpub, O.hρ, O.goodC⟩
  cell := ⟨O.cellOK, O.cellNodes⟩
  walk := ⟨O.walkOK, O.walkNodes⟩
  jet := ⟨O.jOK, O.stat⟩
  atom := ⟨O.atomOK, O.atomNodes⟩
  atomWalk := ⟨O.awOK⟩
  balances := ⟨O.balG, O.balV, O.balF⟩
  claim := O.claim
  budget := O.budget
  wt := O.wt
  staged := O.staged
  fig := O.fig

/-- The regrouping, other direction. -/
theorem toObl {B : HonestJ8 p K δ Rg fuel s f r} (G : ComplGenericObligations δ b B) :
    ComplJ8Obligations δ b B where
  hH := G.compute.hH
  hpair := G.compute.hpair
  hN := G.compute.hN
  hinjX := G.compute.hinjX
  hadjX := G.compute.hadjX
  htrC := G.compute.htrC
  hpIC := G.compute.hpIC
  hpS := G.compute.hpS
  hpO := G.compute.hpO
  hpub := G.compute.hpub
  hρ := G.compute.hρ
  goodC := G.compute.goodC
  cellOK := G.cell.cellOK
  cellNodes := G.cell.cellNodes
  walkOK := G.walk.walkOK
  walkNodes := G.walk.walkNodes
  jOK := G.jet.jOK
  atomOK := G.atom.atomOK
  atomNodes := G.atom.atomNodes
  awOK := G.atomWalk.awOK
  balG := G.balances.balG
  balV := G.balances.balV
  balF := G.balances.balF
  stat := G.jet.stat
  claim := G.claim
  budget := G.budget
  wt := G.wt
  staged := G.staged
  fig := G.fig

/-- **The regrouping is an equivalence**. -/
theorem complGenericObligations_iff (B : HonestJ8 p K δ Rg fuel s f r) :
    Nonempty (ComplGenericObligations δ b B) ↔ Nonempty (ComplJ8Obligations δ b B) :=
  ⟨fun ⟨G⟩ => ⟨toObl δ b G⟩, fun ⟨O⟩ => ⟨ofObl δ b O⟩⟩

open Classical in
/-- **J-8 general completeness at the generic predicate**: `complJ8_of_obligations` with `AcceptsJ8V`
read as `AcceptsGeneric (J8providers) claimJ8 budgetJ8` (through `acceptsGeneric_j8_iff`), from the by-provider
obligations. -/
theorem complGeneric_j8 (B : HonestJ8 p K δ Rg fuel s f r) (G : ComplGenericObligations δ b B)
    (hp63 : 2 ^ 63 < p) (hax : ProgAxOK p B.t) (hop5 : ProgOp5OK p B.t) (hleaf : ProgLeafOK B.t) :
    (∀ χ, B.Good χ → AcceptsGeneric δ (J8providers δ b) (claimJ8 δ b) budgetJ8 B.Pb Rg.R (cJ s f r) χ (B.M χ)
      (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ8 B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (p = Nock.Atoms.p → Fintype.card K = VclL.Events.cK → RowsLe31 B.Pb →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsGeneric δ (J8providers δ b) (claimJ8 δ b) budgetJ8 B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ)
        B.rows B.g) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := complJ8_of_obligations δ b B (toObl δ b G) hp63 hax hop5 hleaf
  refine ⟨fun χ hχ => (acceptsGeneric_j8_iff _ _ _ _ _ _ _ _).2 (h1 χ hχ), h2, h3, h4, fun hpG hcK hrows => ?_⟩
  obtain ⟨hε, χ, hχ⟩ := h5 hpG hcK hrows
  exact ⟨hε, χ, (acceptsGeneric_j8_iff _ _ _ _ _ _ _ _).2 hχ⟩

end Obl

end

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplGeneric
#print axioms ofObl
#print axioms toObl
#print axioms complGenericObligations_iff
#print axioms complGeneric_j8
end Axioms

end Nock.NockVMROM.Thm54.VclL.Handle.ComplGeneric
