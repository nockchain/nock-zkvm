/-
  Nock/NockVMROM/Thm54/VclL/Handle/LinkJ8R3G.lean

  **`hprsG` — the census readout extended by the registered and claim cell
  nouns.**

  * `realizeG`: `realizeJ8` at `layPb` / `extT8` whose census readout is `EncInjJ8.censusPairs (censusList2 rows ext ++
    censusG Pb c)` (Q2's `censusPairs_reg_length_le`: still `≤ 2^66`, so `P = 2^66` and the figure are unchanged);
    `RRG = realIO (realizeG …) Pb`.
  * `linkX_of_R3G` (as `linkX_of_R3`), **`LinkJ8R3G`** = `LinkJ8R3A` minus `hprsG`; `linkR3_of_R3G` derives `hRA`
    `hrn` `hwRA` `hprs` AND `hprsG`; **`probJ8R3G_final`** (`< 2^-155`, conditional on `LinkJ8R3G` only).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3G

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

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3
open Nock.NockVMROM.Thm54.VclL.Handle.LinkQ2J8 (valReader)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (rowsMJ8 rowsB0 crA)

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8 (censusList2)

noncomputable section

section Sound
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`realizeJ8` with the census readout extended by `censusG Pb c`.** -/
def realizeG (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (Pb : PubJ8 p) (c : P8PublicClaim) (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31) :
    DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g :=
  let R1 := realizeJ8 (g := g) δ b R0 (layPb Pb skel hs) hL (extT8 b Pb) (extT8_staged b Pb) hP hnM
  { R1 with
    D := { R1.D with
      prs := fun tr => EncInjJ8.censusPairs (censusList2 (TraceJ8.rowsMJ8 Pb.nodesC Pb.orbitC tr) (extT8 b Pb tr) ++
        censusG Pb c)
      prs_le := fun tr => hP ▸ LinkQ2J8.censusPairs_reg_length_le _ _ _
        (by rw [TraceJ8.rowsMJ8, TraceJ8.rowsB0_length]; exact hnM) hreg
      prs_const := fun Q hQ χ χ' => by
        simp only [TraceJ8.rowsMJ8_const Pb.nodesC Pb.orbitC Q hQ χ χ', extT8_staged b Pb Q hQ χ χ'] } }

/-- The census-extended real data. -/
abbrev RRG (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (Pb : PubJ8 p) (c : P8PublicClaim) (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31) :
    DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g :=
  realIO δ b (realizeG δ b (g := g) R0 Pb c skel hs hL hP hnM hreg) Pb

/-- **`LinkJ8R3A` minus `hprsG`** (derived at `RRG`). -/
structure LinkJ8R3G (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    : Prop where
  rdV : R.D.valReqs tr χ = M.reqsC ++ cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) ∧
    R.D.valProvs tr χ = SVFrame.liftWts (cellVRecords δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))) ++ M.xsC
  budV : (R.D.valReqs tr χ).length ≤ 3 + 2 * r.D + g ∧ (R.D.valProvs tr χ).length ≤ r.D + r.mb
  hext : ∀ j m, AtomBigJ8.extB p (rAT (K := K) b Pb tr) j = some m → ∃ v, m = .atom v ∧ lenL v ≤ r.maxlen
  hvp : AtomLeaves (encJ8 δ χ) M.vp (AtomBigJ8.extB p (rAT (K := K) b Pb tr))
  hXW : KeysExported (cellT δ b Pb χ M tr)
    (walkDataOf δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (AtomWalkAW.restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)))).X
  hsA : ∀ k : Fin Pb.nA, ((rAT (K := K) b Pb tr) k).Small
  hidxA : ∀ k : Fin Pb.nA, ((rAT (K := K) b Pb tr) k).idx = k
  hB : AtomChipHQ.LimbsBounded (rAT (K := K) b Pb tr)
  hok : ∀ j, ((rAT (K := K) b Pb tr) j).inc = 1 → AtomChipHQ.ChainOK (rAT (K := K) b Pb tr) j
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
  hrealA : isCellN c.formula = false → (stX (envX δ b Pb c χ M tr 0)).isChain = false


/-- `linkX_of_R3` at the census-extended data `RRG`. -/
theorem linkX_of_R3G [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31)
    (hpG : p = Nock.Atoms.p) (hacc' : AcceptsJ8' δ b Pb Rg c χ M tr)
    (hout : ∀ s ∈ allJ8C (withLiftC (RRG δ b (g := g) R0 Pb c skel hs hL hP hnM hreg) (LL δ b L0 Pb skel hs hL)),
      ¬ s.mem tr χ)
    (hB : BudJ8 Pb r g) (hcap : 3 * r.N + r.W + r.rd < p ∧ 2 * r.N < p ∧ r.N + 2 * r.J + g < p)
    (hΛ : fuelChip ≤ r.Λ) {rA : ℕ → AtomChipHQ.ARow}
    (hl : LinkJ8R3 δ b Pb c χ (toMsgJ8 δ b Pb c χ M tr) tr (RRG δ b (g := g) R0 Pb c skel hs hL hP hnM hreg) rA) :
    LinkJ8X' δ b Pb c χ (toMsgJ8 δ b Pb c χ M tr) tr (RRG δ b (g := g) R0 Pb c skel hs hL hP hnM hreg)
      (LL δ b L0 Pb skel hs hL) rA := by
  have hacc := acceptsJ8_of' δ b hacc'
  have hp17 : 17 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hp64 : 64 ≤ p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  set M' := toMsgJ8 δ b Pb c χ M tr
  have rX := rdX_realIO δ b (realizeG δ b (g := g) R0 Pb c skel hs hL hP hnM hreg) Pb c χ M' tr
  have rS := rdS_realIO δ b (realizeG δ b (g := g) R0 Pb c skel hs hL hP hnM hreg) Pb c χ M' tr
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


theorem censusPairs_append_mem {l m : List Noun} {pr : List ℕ × List ℕ} (h : pr ∈ EncInjJ8.censusPairs l) :
    pr ∈ EncInjJ8.censusPairs (l ++ m) := by
  unfold EncInjJ8.censusPairs at h ⊢
  obtain ⟨x, hx, hpr⟩ := List.mem_flatMap.mp h
  exact List.mem_flatMap.mpr ⟨x, CensusVS.allPairs_append_mem _ _ hx, hpr⟩

/-- **`LinkJ8R3` from `LinkJ8R3G`** at `RRG`, `rA := rAT`: `hRA hrn hwRA hprs hprsG` derived. -/
theorem linkR3_of_R3G (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31)
    (hacc' : AcceptsJ8' δ b Pb Rg c χ M tr)
    (hl : LinkJ8R3G δ b Pb c χ (toMsgJ8 δ b Pb c χ M tr) tr (RRG δ b (g := g) R0 Pb c skel hs hL hP hnM hreg)) :
    LinkJ8R3 δ b Pb c χ (toMsgJ8 δ b Pb c χ M tr) tr (RRG δ b (g := g) R0 Pb c skel hs hL hP hnM hreg)
      (rAT b Pb tr) := by
  have hacc := acceptsJ8_of' δ b hacc'
  set M' := toMsgJ8 δ b Pb c χ M tr
  have hE := rAT_eq δ b Pb tr (chalsAJ8 δ χ) M'.pubsA
  have hG : ∀ pr ∈ EncInjJ8.censusPairs (censusList2 ((cellT δ b Pb χ M' tr).map (·.b0)) (AtomBigJ8.extB p (rAT b Pb tr)) ++
      censusG Pb c), pr ∈ (RRG δ b (g := g) R0 Pb c skel hs hL hP hnM hreg).D.prs tr := by
    intro pr hpr
    show pr ∈ EncInjJ8.censusPairs (censusList2 (TraceJ8.rowsMJ8 Pb.nodesC Pb.orbitC tr) (extT8 b Pb tr) ++ censusG Pb c)
    rw [rowsMJ8_eq_cellT δ b Pb χ M' tr]
    exact hpr
  exact
    { rdV := hl.rdV
      budV := hl.budV
      hext := hl.hext
      hprs := fun pr hpr => hG pr (censusPairs_append_mem hpr)
      hvp := hl.hvp
      hXW := hl.hXW
      hRA := by rw [← hE]; exact LinkQ2J8.hRA_valReader _
      hsA := hl.hsA
      hidxA := hl.hidxA
      hrn := by rw [← hE]; exact LinkQ2J8.hrn_valReader _
      hB := hl.hB
      hwRA := by rw [← hE]; exact LinkQ2J8.hwRA_valReader _ (LinkQ2J8.atom_wR_bool hacc.hsatA)
      hok := hl.hok
      houtA := hl.houtA
      hservedA := hl.hservedA
      hHXV := hl.hHXV
      hprsG := hG
      hrealA := hl.hrealA }

open Classical in
/-- **The J-8 figure at the census-extended real data**: `< 2^-155` at the census corner, conditional on
`LinkJ8R3G` only. -/
theorem probJ8R3G_final [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim)
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31)
    (hB : BudJ8 Pb r g)
    (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    (hcK : Fintype.card K = VclL.Events.cK) (hr : RowsLe r EncInjJ8.cornerC) (hg : g ≤ 2 ^ 31)
    (hlink : ∀ χ (M : MsgJ8' p K δ), AcceptsJ8' δ b Pb Rg c χ M (Q χ) →
      LinkJ8R3G δ b Pb c χ (toMsgJ8 δ b Pb c χ M (Q χ)) (Q χ) (RRG δ b (g := g) R0 Pb c skel hs hL hP hnM hreg)) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8' p K δ, AcceptsJ8' δ b Pb Rg c χ M (Q χ)) ∧ ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 := by
  have hAW : Pb.nV ≤ r.AW := hL.V
  have hbA : Pb.nA ≤ r.A := hL.A
  have hΛ : fuelChip ≤ r.Λ := by rw [hr.2.2.2.1]; exact le_refl _
  have hcap := hcap_corner hr hg hpG
  exact AtomFpxJ8.probJ8X_lt_155_census
    (AtomFpxJ8.withFpxV δ b (withLiftC (RRG δ b (g := g) R0 Pb c skel hs hL hP hnM hreg) (LL δ b L0 Pb skel hs hL))
      Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA) Q hQ _ _
    (fun χ hacc hout => by
      obtain ⟨M, hM⟩ := hacc
      exact hsoundJ8X' δ b Pb hRg c χ M (Q χ) _ _ hpG hqM hk hAW hbA hM hout (wdV_view δ b Pb (Q χ) _ _)
        (linkX_of_R3G δ b Pb c χ M (Q χ) R0 L0 skel hs hL hP hnM hreg hpG hM
          (AtomFpxJ8.outsideC_of_outsideX _ hout) hB hcap hΛ
          (linkR3_of_R3G δ b Pb c χ M (Q χ) R0 skel hs hL hP hnM hreg hM (hlink χ M hM))))
    hcK hr (le_of_eq hP) hg

end Sound

end

end Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3G
