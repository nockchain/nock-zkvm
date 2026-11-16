/-
  Nock/NockVMROM/Thm54/VclL/Handle/LinkJ8R3.lean

  **`LinkJ8X'` at the real data.**

  The data are the `layPb` realizations with every IO list `LinkJ8X'` pins read off the trace:
  `R := realIO (realizeJ8 R0 (layPb Pb skel hs) …) Pb`, `L := real40 (realize40 L0 (layPb Pb skel hs) …) Pb`.
  * **`LinkJ8R3`**: the residue — `LinkJ8X'` without the eleven fields derived here.
  * **`linkX_of_R3`**: on `AcceptsJ8'`, outside `allJ8X`, under the public budget checks `BudJ8` (Goldilocks, the
    census corner), `LinkJ8R3` ⇒ `LinkJ8X'`.  Derived: `rdX` / `rdS` (`RealIOJ8`), `rdP` (`RealIOJ8`), `budX` /
    `budP` / `budS` / `hcount` (`RealIOJ8`, `BudJ8`), `rdWC` / `rdWW` (Q1 `linkJ8_L2` at `realize40`), `hHXW` (Q1H
    `hHXW_of_accepts` at the exclusions of #5 / #1 / #6 at the real lists), `hseedsV` (Q1S `hseedsV_of_outside` at
    `realizeJ8`'s `rowsA`).
  * **`probJ8R3_final`**: `Pr[(∃ M, AcceptsJ8') ∧ ¬ HoldsN c] < 2^-155` at the real data, conditional on the
    residue `LinkJ8R3` only.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1H
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1S

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3

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
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
set_option linter.dupNamespace false

noncomputable section

section Sound
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The residue of `LinkJ8X'` at the real data**: every field except `rdX budX rdP budP rdS budS hcount rdWC rdWW
hHXW hseedsV` (derived by `linkX_of_R3`). -/
structure LinkJ8R3 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (rA : ℕ → AtomChipHQ.ARow) : Prop where
  rdV : R.D.valReqs tr χ = M.reqsC ++ cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) ∧
    R.D.valProvs tr χ = SVFrame.liftWts (cellVRecords δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))) ++ M.xsC
  budV : (R.D.valReqs tr χ).length ≤ 3 + 2 * r.D + g ∧ (R.D.valProvs tr χ).length ≤ r.D + r.mb
  hext : ∀ j m, AtomBigJ8.extB p rA j = some m → ∃ v, m = .atom v ∧ lenL v ≤ r.maxlen
  hprs : ∀ pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2 ((cellT δ b Pb χ M tr).map (·.b0))
    (AtomBigJ8.extB p rA)), pr ∈ R.D.prs tr
  hvp : AtomLeaves (encJ8 δ χ) M.vp (AtomBigJ8.extB p rA)
  hXW : KeysExported (cellT δ b Pb χ M tr)
    (walkDataOf δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (AtomWalkAW.restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)))).X
  hRA : ∀ k : Fin Pb.nA, AtomChipHQ.Reads (AtomServedQ.aEF b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA
    (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA) k) (rA k)
  hsA : ∀ k : Fin Pb.nA, (rA k).Small
  hidxA : ∀ k : Fin Pb.nA, (rA k).idx = k
  hrn : ∀ k, Pb.nA ≤ k → (rA k).inc = 0
  hB : AtomChipHQ.LimbsBounded rA
  hwRA : ∀ j, (rA j).wR ≤ 1
  hok : ∀ j, (rA j).inc = 1 → AtomChipHQ.ChainOK rA j
  houtA : ((AtomServedQ.acoins δ (chalsAJ8 δ χ)).gamma, (AtomServedQ.acoins δ (chalsAJ8 δ χ)).pole) ∉
    IOFailureEventW ((AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA
        (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA) ++ M.wreqs).map (BalanceQ.liftRec (K := K) (L := 𝕂′)))
      (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA
        (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA)))
  hservedA : ValidityServed (atomT δ b Pb χ M tr)
  hHXV : ∀ j < Pb.nV, ∃ c' ∈ atomT δ b Pb χ M tr,
    (natOf ((AtomWalkAW.walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV) j).trace WChip.idx),
      childHOf (AtomWalkAW.walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV) j) false,
      childHOf (AtomWalkAW.walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV) j) true) = exportRec c'.b0
  hprsG : ∀ pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2 ((cellT δ b Pb χ M tr).map (·.b0))
    (AtomBigJ8.extB p rA) ++ censusG Pb c), pr ∈ R.D.prs tr
  hrealA : isCellN c.formula = false → (stX (envX δ b Pb c χ M tr 0)).isChain = false

/-- The real data `R` (`realizeJ8` at `layPb`, the handle-balance lists off the trace). -/
abbrev RR (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (Pb : PubJ8 p) (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (ext : TrJ8 (ZMod p) → ℕ → Option Noun)
    (hext : ∀ Q : Coins frameJ8 K → TrJ8 (ZMod p), StJ8 Q → ∀ χ χ', ext (Q χ) = ext (Q χ'))
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) :
    DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g :=
  realIO δ b (realizeJ8 (g := g) δ b R0 (layPb Pb skel hs) hL ext hext hP hnM) Pb

/-- The real data `L` (`realize40` at `layPb`, the path lists off the trace). -/
abbrev LL (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (Pb : PubJ8 p) (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r) :
    Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r :=
  real40 δ b (realize40 δ b L0 (layPb Pb skel hs) hL) Pb

/-- **`LinkJ8X'` from its residue `LinkJ8R3` at the real data**: eleven fields derived. -/
theorem linkX_of_R3 [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (ext : TrJ8 (ZMod p) → ℕ → Option Noun)
    (hext : ∀ Q : Coins frameJ8 K → TrJ8 (ZMod p), StJ8 Q → ∀ χ χ', ext (Q χ) = ext (Q χ'))
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31)
    (hpG : p = Nock.Atoms.p) (hacc' : AcceptsJ8' δ b Pb Rg c χ M tr)
    (hout : ∀ s ∈ allJ8C (withLiftC (RR δ b (g := g) R0 Pb skel hs hL ext hext hP hnM) (LL δ b L0 Pb skel hs hL)),
      ¬ s.mem tr χ)
    (hB : BudJ8 Pb r g) (hcap : 3 * r.N + r.W + r.rd < p ∧ 2 * r.N < p ∧ r.N + 2 * r.J + g < p)
    (hΛ : fuelChip ≤ r.Λ) {rA : ℕ → AtomChipHQ.ARow}
    (hl : LinkJ8R3 δ b Pb c χ (toMsgJ8 δ b Pb c χ M tr) tr (RR δ b (g := g) R0 Pb skel hs hL ext hext hP hnM) rA) :
    LinkJ8X' δ b Pb c χ (toMsgJ8 δ b Pb c χ M tr) tr (RR δ b (g := g) R0 Pb skel hs hL ext hext hP hnM)
      (LL δ b L0 Pb skel hs hL) rA := by
  have hacc := acceptsJ8_of' δ b hacc'
  have hp17 : 17 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hp64 : 64 ≤ p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  set M' := toMsgJ8 δ b Pb c χ M tr
  have rX := rdX_realIO δ b (realizeJ8 (g := g) δ b R0 (layPb Pb skel hs) hL ext hext hP hnM) Pb c χ M' tr
  have rS := rdS_realIO δ b (realizeJ8 (g := g) δ b R0 (layPb Pb skel hs) hL ext hext hP hnM) Pb c χ M' tr
  have rP := rdP_real40 δ b (realize40 δ b L0 (layPb Pb skel hs) hL) Pb c χ M' tr
  have bX := budX_of δ b Pb c χ M' tr hacc hp17 hB
  have bP := budP_of δ b Pb c χ M' tr hacc hp17 hB
  have bS := budS_of δ b Pb c χ M' tr hacc hp17 hB
  have L2 := LinkJ8Q1.linkJ8_L2 δ b Pb skel hs L0 hL c χ M' tr hacc hp17
  have hx := ListJ8C.hout_x_of_outsideC _ b hout _ _ rX.1 rX.2 bX.1 bX.2
  have hpp := ListJ8C.hout_p_of_outside40C _ _ b hout _ _ rP.1 rP.2 bP.1 bP.2
  have hss := ListJ8C.hout_s_of_outsideC _ b hout _ _ rS.1 rS.2 bS.1 bS.2
  have hcnt := hcount_of δ b Pb c χ M' tr hacc hp17 hB hcap
  exact
    { rdX := rX
      budX := by rw [rX.1, rX.2]; exact bX
      rdP := rP
      budP := by rw [rP.1, rP.2]; exact bP
      rdS := rS
      budS := by rw [rS.1, rS.2]; exact bS
      hcount := hcnt
      rdV := hl.rdV
      budV := hl.budV
      rdWC := L2.1
      rdWW := L2.2
      hext := hl.hext
      hprs := hl.hprs
      hvp := hl.hvp
      hXW := hl.hXW
      hHXW := LinkJ8Q1H.hHXW_of_accepts δ b Pb c χ M' tr hacc hp64 hx hpp hss (hcnt .x)
      hRA := hl.hRA
      hsA := hl.hsA
      hidxA := hl.hidxA
      hrn := hl.hrn
      hB := hl.hB
      hwRA := hl.hwRA
      hok := hl.hok
      houtA := hl.houtA
      hservedA := hl.hservedA
      hseedsV := LinkJ8Q1S.hseedsV_of_outside δ b _ Pb χ M' tr hout
        (LinkJ8Q1S.rowsAJ8_eq_atomT δ b Pb χ M' tr) hΛ
      hHXV := hl.hHXV
      hprsG := hl.hprsG
      hrealA := hl.hrealA }

open Classical in
/-- **The J-8 figure at the real data**: for every staged `Q`, `Pr[(∃ M', AcceptsJ8') ∧ ¬ HoldsN c] < 2^-155`
at the census corner, conditional on the residue `LinkJ8R3` only (the IO readouts, their budgets, the counts,
`rdWC`, `rdWW`, `hHXW`, `hseedsV` are derived), under the public budget checks `BudJ8`. -/
theorem probJ8R3_final [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim)
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (ext : TrJ8 (ZMod p) → ℕ → Option Noun)
    (hext : ∀ Q : Coins frameJ8 K → TrJ8 (ZMod p), StJ8 Q → ∀ χ χ', ext (Q χ) = ext (Q χ'))
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hB : BudJ8 Pb r g)
    (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    (hcK : Fintype.card K = VclL.Events.cK) (hr : RowsLe r EncInjJ8.cornerC) (hg : g ≤ 2 ^ 31)
    (hlink : ∀ χ (M : MsgJ8' p K δ), AcceptsJ8' δ b Pb Rg c χ M (Q χ) →
      ∃ rA, LinkJ8R3 δ b Pb c χ (toMsgJ8 δ b Pb c χ M (Q χ)) (Q χ)
        (RR δ b (g := g) R0 Pb skel hs hL ext hext hP hnM) rA) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8' p K δ, AcceptsJ8' δ b Pb Rg c χ M (Q χ)) ∧ ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 := by
  have hAW : Pb.nV ≤ r.AW := hL.V
  have hbA : Pb.nA ≤ r.A := hL.A
  have hΛ : fuelChip ≤ r.Λ := by rw [hr.2.2.2.1]; exact le_refl _
  have hcap := hcap_corner hr hg hpG
  exact AtomFpxJ8.probJ8X_lt_155_census
    (AtomFpxJ8.withFpxV δ b (withLiftC (RR δ b (g := g) R0 Pb skel hs hL ext hext hP hnM) (LL δ b L0 Pb skel hs hL))
      Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA) Q hQ _ _
    (fun χ hacc hout => by
      obtain ⟨M, hM⟩ := hacc
      obtain ⟨rA, hl⟩ := hlink χ M hM
      exact hsoundJ8X' δ b Pb hRg c χ M (Q χ) _ _ hpG hqM hk hAW hbA hM hout (wdV_view δ b Pb (Q χ) _ _)
        (linkX_of_R3 δ b Pb c χ M (Q χ) R0 L0 skel hs hL ext hext hP hnM hpG hM
          (AtomFpxJ8.outsideC_of_outsideX _ hout) hB hcap hΛ hl))
    hcK hr (le_of_eq hP) hg

end Sound

end

end Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3
