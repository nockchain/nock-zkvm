/-
  Nock/NockVMROM/Thm54/VclL/Handle/LinkJ8R3A.lean

  **The atom-table reader read off the trace; `hRA` / `hrn` / `hwRA` /
  `hprs` derived.**

  * `rAT Pb tr`: Q2's canonical reader `valReader` on the atom table's coin-free row environments; `rAT_eq`: it IS
    `valReader` at the chip view at every coin and message (the reader reads trace columns only);
    `rAT_congr`: it reads round-0 columns only (`< 205`).
  * `extT8 Pb tr = extB p (rAT Pb tr)`: the census readout's atom-export map, staged (`extT8_staged`).
  * `rowsMJ8_eq_cellT`: the census readout's cell rows are the decoded cell table's `b0`.
  * **`LinkJ8R3A`** = `LinkJ8R3` minus `hRA hrn hwRA hprs`, at `rA := rAT Pb tr` and `ext := extT8 Pb`;
    `linkR3_of_R3A`; **`probJ8R3A_final`** (`< 2^-155`, conditional on `LinkJ8R3A` only).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A

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

noncomputable section

section Reader
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

/-- **The atom-table reader of a trace** (Q2's `valReader` at the coin-free row environments). -/
def rAT (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) : ℕ → AtomChipHQ.ARow :=
  valReader (fun k : Fin Pb.nA => AtomServedQ.aEF b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A k)

theorem valReader_congr {n : ℕ} {e e' : Fin n → Env (ZMod p)} (h : ∀ k, (e k).trace = (e' k).trace) :
    valReader e = valReader e' := by
  funext k
  unfold valReader
  split_ifs with hk
  · simp only [h]
  · rfl

theorem rAT_eq (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (chals pubs : ℕ → K) :
    valReader (fun k : Fin Pb.nA => AtomServedQ.aEF b Pb.nodesA Pb.orbitA chals pubs
      (qA δ b Pb tr chals pubs) k) = rAT b Pb tr := by
  refine valReader_congr fun k => ?_
  funext j
  simp only [AtomServedQ.aEF, Reify.envOfTrace, TraceJ8.widthA_eq]
  rfl



/-- The reader reads its rows' columns `< 205` only. -/
theorem valReader_congr205 {n : ℕ} {e e' : Fin n → Env (ZMod p)}
    (h : ∀ k, ∀ c < 205, (e k).trace c = (e' k).trace c) : valReader e = valReader e' := by
  funext k
  unfold valReader
  split_ifs with hk
  · simp only [h _ Chips.ChipRAP.Cell.idx (by decide), h _ Chips.ChipRAP.Cell.aL (by decide), h _ Chips.ChipRAP.Cell.wR (by decide), h _ Chips.ChipRAP.Cell.idR (by decide),
      h _ Chips.ChipRAP.Cell.aR (by decide), h _ AtomChipHQ.inc (by decide), h _ AtomChipHQ.cout (by decide),
      h _ AtomChipHQ.idxO (by decide), h _ AtomChipHQ.lO (by decide), h _ AtomChipHQ.kRO (by decide),
      h _ AtomChipHQ.vRO (by decide)]
  · rfl

theorem rAT_congr (Pb : PubJ8 p) {tr tr' : TrJ8 (ZMod p)} (h : Agree0 tr tr') : rAT (K := K) b Pb tr = rAT b Pb tr' :=
  valReader_congr205 fun k => DescentVSQ.envOfTrace_congrW 205 tr.A tr'.A (by norm_num) (by norm_num)
    (fun c h1 h2 hc => h.A ⟨c, h1⟩ (by simp [crA, hc])) _ _ _ _ _ _ _

/-- **The census readout's atom-export map**, read off the trace. -/
def extT8 (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) : ℕ → Option Noun := AtomBigJ8.extB p (rAT (K := K) b Pb tr)

theorem extT8_staged (Pb : PubJ8 p) :
    ∀ Q : Coins frameJ8 K → TrJ8 (ZMod p), StJ8 Q → ∀ χ χ', extT8 (K := K) b Pb (Q χ) = extT8 b Pb (Q χ') :=
  fun Q hQ χ χ' => by
    unfold extT8
    rw [rAT_congr b Pb (agree0_of_staged hQ χ χ')]

/-- **The census readout's cell rows are the decoded cell table's `b0`.** -/
theorem rowsMJ8_eq_cellT (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    rowsMJ8 Pb.nodesC Pb.orbitC tr = (cellT δ b Pb χ M tr).map (·.b0) := by
  unfold rowsMJ8 rowsB0 cellT cellTableOf
  rw [List.map_ofFn]
  congr 1

end Reader

section Sound
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`LinkJ8R3` at the trace's reader `rAT`, minus `hRA hrn hwRA hprs`** (derived by `linkR3_of_R3A`). -/
structure LinkJ8R3A (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
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
  hprsG : ∀ pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2 ((cellT δ b Pb χ M tr).map (·.b0))
    (AtomBigJ8.extB p (rAT (K := K) b Pb tr)) ++ censusG Pb c), pr ∈ R.D.prs tr
  hrealA : isCellN c.formula = false → (stX (envX δ b Pb c χ M tr 0)).isChain = false


/-- **`LinkJ8R3` from `LinkJ8R3A`** at `rA := rAT Pb tr` and the census map `ext := extT8 Pb`. -/
theorem linkR3_of_R3A (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31)
    (hacc' : AcceptsJ8' δ b Pb Rg c χ M tr)
    (hl : LinkJ8R3A δ b Pb c χ (toMsgJ8 δ b Pb c χ M tr) tr
      (RR δ b (g := g) R0 Pb skel hs hL (extT8 b Pb) (extT8_staged b Pb) hP hnM)) :
    LinkJ8R3 δ b Pb c χ (toMsgJ8 δ b Pb c χ M tr) tr
      (RR δ b (g := g) R0 Pb skel hs hL (extT8 b Pb) (extT8_staged b Pb) hP hnM) (rAT b Pb tr) := by
  have hacc := acceptsJ8_of' δ b hacc'
  set M' := toMsgJ8 δ b Pb c χ M tr
  have hE := rAT_eq δ b Pb tr (chalsAJ8 δ χ) M'.pubsA
  exact
    { rdV := hl.rdV
      budV := hl.budV
      hext := hl.hext
      hprs := fun pr hpr => by
        show pr ∈ TraceJ8.prsJ8 Pb.nodesC Pb.orbitC (extT8 b Pb) tr
        unfold TraceJ8.prsJ8
        rw [rowsMJ8_eq_cellT δ b Pb χ M' tr]
        exact hpr
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
      hprsG := hl.hprsG
      hrealA := hl.hrealA }

open Classical in
/-- **The J-8 figure at the real data with the trace's atom reader**: `< 2^-155` at the census corner,
conditional on `LinkJ8R3A` only. -/
theorem probJ8R3A_final [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim)
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hB : BudJ8 Pb r g)
    (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    (hcK : Fintype.card K = VclL.Events.cK) (hr : RowsLe r EncInjJ8.cornerC) (hg : g ≤ 2 ^ 31)
    (hlink : ∀ χ (M : MsgJ8' p K δ), AcceptsJ8' δ b Pb Rg c χ M (Q χ) →
      LinkJ8R3A δ b Pb c χ (toMsgJ8 δ b Pb c χ M (Q χ)) (Q χ)
        (RR δ b (g := g) R0 Pb skel hs hL (extT8 b Pb) (extT8_staged b Pb) hP hnM)) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8' p K δ, AcceptsJ8' δ b Pb Rg c χ M (Q χ)) ∧ ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 :=
  probJ8R3_final δ b Pb hRg c R0 L0 skel hs hL (extT8 b Pb) (extT8_staged b Pb) hP hnM hB Q hQ hpG hqM hk hcK hr hg
    fun χ M hM => ⟨rAT b Pb (Q χ), linkR3_of_R3A δ b Pb c χ M (Q χ) R0 skel hs hL hP hnM hM (hlink χ M hM)⟩

end Sound

end

end Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A
