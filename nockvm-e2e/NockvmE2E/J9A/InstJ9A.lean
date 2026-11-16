/-
the J-9 A twin of `J8/InstJ8.lean`.
`Ι9` (eight tables), `unflat9`, `Datum9A`, `DatumOK9A`, `Msg9`/`Mcode9`/`decM9`, the eight chips, `consT9`, `PubP9A`,
`StmtP9A`, `accGen9A`, caps and `clJ9A : CLay`, `Handle/RealIOJ9A.lean`, `AcceptsJ9A.lean`).
Nothing here states `E2EJ9AIface`.
-/
import NockvmE2E.J8.IfaceG
import Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ChipHX9RAP
import Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9
import Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial

namespace NockvmE2E.J9A.InstJ9A

open NockvmE2E.Rap NockvmE2E.Succ
open NockvmE2E.J8.IfaceG (CLay NIface)
open Nock.TraceGenExe Nock.NockVMROM.Thm54.T0Tower
open NockvmE2E.J8.InstJ8 (P Φ0 KQ' truncP truncP_deg chip_ok hI_expand preOf xpF ext0 len_cell len_walkJ8 len_jet len_atom len_walkHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crC crM crW crJ crA)

noncomputable section Inst
open Nock.Jet.ChipJ8 (jetChipJ8 layoutJ8 PRow tvKey axPosB)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.V1J8 (PubEqJ8)
open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial Nock.NockVMROM Nock.NockVMROM.Thm54.VclL
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
open Nock.Atoms (lenL)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (RowsLe)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (withLiftC)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R4 (RR4 LL4)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R5 (R0d L0d)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8NV (hsoundJ8XUG linkXUG_of_R5)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A (hsoundJ8XUA linkXUA_of_R5)
open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8 (RR4A)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (wdV_view)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8NV (layLe_ofG)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (c4 c5 c6 c7 c11 c12 c15 c16 c2 c3 liftJ8 embJ8 yDep sumJ8 orderJ8 ioSummandJ8 atomDyckJ8 atomCensusJ8 zeroYJ8 bivJ8 specV specH specZY)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (sumJ8C allJ8C DataJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (sum40 Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8 (allJ8X atomFpxJ8 withFpxV)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (specVQ specHQ spec01 spec1314 v2 v3 v4 v5 v6 v7 v11 v12 v13 v14 v0 v1)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (specV specH specZY)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (spec01J8 c0 c1)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (spec01J8 c0 c1)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (specV specH specZY)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (gatesHX9 gatesHX9P gatesHX9P_length permX9 widthHX9 computeChipVCLHX9 computeChipVCLHX9_width)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (pinRecsJ8)
open Nock.Jet.PinJ8 (pinCons)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.FiniteIO (compress)

/-! ## 1. the flat column index (eight tables) -/

/-- the eight chips' columns, in the flat order (compute9, cell, walkJ8, jet, atom, walkHQK, axis, split) -/
abbrev Ι9 : Type := Fin 137 ⊕ Fin 242 ⊕ Fin 166 ⊕ Fin 71 ⊕ Fin 349 ⊕ Fin 166 ⊕ Fin 52 ⊕ Fin 90

abbrev iC (j : Fin 137) : Ι9 := Sum.inl j
abbrev iM (j : Fin 242) : Ι9 := Sum.inr (Sum.inl j)
abbrev iW (j : Fin 166) : Ι9 := Sum.inr (Sum.inr (Sum.inl j))
abbrev iJ (j : Fin 71) : Ι9 := Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))
abbrev iA (j : Fin 349) : Ι9 := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))
abbrev iV (j : Fin 166) : Ι9 := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))))
abbrev iX (j : Fin 52) : Ι9 := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))))
abbrev iS (j : Fin 90) : Ι9 := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr j))))))

def colR9 : Ι9 → ℕ :=
  Sum.elim crC9 (Sum.elim crM (Sum.elim crW (Sum.elim crJ (Sum.elim crA (Sum.elim crW (Sum.elim crAX crSP))))))

theorem colR9_le : ∀ j, colR9 j ≤ 2 := by
  intro j
  rcases j with j | j | j | j | j | j | j | j
  · simp only [colR9, Sum.elim_inl, crC9]; split_ifs <;> omega
  · simp only [colR9, Sum.elim_inr, Sum.elim_inl, crM]; split_ifs <;> omega
  · simp only [colR9, Sum.elim_inr, Sum.elim_inl, crW]; split_ifs <;> omega
  · simp only [colR9, Sum.elim_inr, Sum.elim_inl, crJ]; split_ifs <;> omega
  · simp only [colR9, Sum.elim_inr, Sum.elim_inl, crA]; split_ifs <;> omega
  · simp only [colR9, Sum.elim_inr, Sum.elim_inl, crW]; split_ifs <;> omega
  · simp only [colR9, Sum.elim_inr, Sum.elim_inl, crAX]; split_ifs <;> omega
  · simp only [colR9, Sum.elim_inr, Sum.elim_inl, crSP]; split_ifs <;> omega

/-- the interface trace as nock's eight chip traces -/
def unflat9 (tr : Ι9 → (ZMod P)[X]) : TrJ9A (ZMod P) :=
  ⟨fun j => tr (iC j), fun j => tr (iM j), fun j => tr (iW j), fun j => tr (iJ j), fun j => tr (iA j),
    fun j => tr (iV j), fun j => tr (iX j), fun j => tr (iS j)⟩

/-- `unflat9` carries `TracesStaged` at `colR9` to nock's `StJ9A` -/
theorem stJ9A_unflat (Q : Coins Φ0 KC → Ι9 → (ZMod P)[X]) (hQ : TracesStaged Φ0 colR9 Q) :
    StJ9A (fun χ => unflat9 (Q χ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j χ χ' h; exact hQ (iC j) χ χ' h
  · intro j χ χ' h; exact hQ (iM j) χ χ' h
  · intro j χ χ' h; exact hQ (iW j) χ χ' h
  · intro j χ χ' h; exact hQ (iJ j) χ χ' h
  · intro j χ χ' h; exact hQ (iA j) χ χ' h
  · intro j χ χ' h; exact hQ (iV j) χ χ' h
  · intro j χ χ' h; exact hQ (iX j) χ χ' h
  · intro j χ χ' h; exact hQ (iS j) χ χ' h

set_option maxRecDepth 100000 in
theorem card_Ι9 : Fintype.card Ι9 = 1273 := by
  simp only [Fintype.card_sum, Fintype.card_fin]


/-! ## 2. the datum -/

/-- the fixed checked datum `(Pb, Rg, c, r, g)` of the J-9 A interface -/
structure Datum9A where
  Pb : PubJ9A P
  Rg : Nock.Jet.Registry
  c : P8PublicClaim
  r : RowsJ9A
  g : ℕ
  /-- the number of points of the union domain -/
  hN : ℕ
  /-- the generator of the union domain `H = {ω^i : i < hN}` -/
  ω : ZMod P

def HdomOf9 (d : Datum9A) : Finset (ZMod P) := (Finset.range d.hN).image (fun i => d.ω ^ i)

/-- the row set of each of the eight tables -/
def HtOf9 (d : Datum9A) : Fin 8 → Finset (ZMod P)
  | 0 => rowNodeSet d.Pb.nodes
  | 1 => rowNodeSet d.Pb.nodesC
  | 2 => rowNodeSet d.Pb.nodesW
  | 3 => rowNodeSet d.Pb.nodesJ
  | 4 => rowNodeSet d.Pb.nodesA
  | 5 => rowNodeSet d.Pb.nodesV
  | 6 => rowNodeSet d.Pb.nodesX
  | 7 => rowNodeSet d.Pb.nodesS

/-- the binders of `soundJ9A_pointwise` / `epsilonOf_listJ9A` / `oneRound_listJ9A` (SIG Part 1) and the caps -/
structure DatumOK9A (d : Datum9A) : Prop where
  hRg : d.Rg.Faithful
  hcK : Fintype.card KC = VclL.Events.cK
  hr : RowsLe d.r.toRowsJ8 EncInjJ8.cornerC
  hAX : d.r.AX ≤ 2 ^ 31
  hSP : d.r.SP ≤ 2 ^ 31
  hqM : ∀ x < ringChar (ZMod P), lenL x ≤ d.r.maxlen
  hk : 2 * fuelChip ≤ d.r.leaves
  hmax : d.Pb.nA + 2 ≤ d.r.maxlen
  hg : d.g ≤ 2 ^ 31
  hLC : d.Pb.n ≤ d.r.N
  hLM : d.Pb.nC ≤ d.r.D
  hLW : d.Pb.nW ≤ d.r.W
  hLA : d.Pb.nA ≤ d.r.A
  hLV : d.Pb.nV ≤ d.r.AW
  hnM : d.Pb.nC ≤ 2 ^ 31
  /-- NOTE `+ 6` (SIG Part 3.4) -/
  hreg9 : (censusG d.Pb.toPubJ8 d.c).length + 6 ≤ 2 ^ 31
  hHt : ∀ t, HtOf9 d t ⊆ HdomOf9 d
  hcapH : d.hN ≤ 2 ^ 26


/-! ## 3. the message -/

/-- the message: nock's `MsgJ9A'` plus the 33 compute publics -/
abbrev Msg9 : Type := MsgJ9A' P KC deltaF × (Fin 33 → ZMod P)

/-- finite codes: claim message, `ρ`, `ρS`, the five J-8 public slices, the axis slice (4 slots `pubAXs, +1, pubAXp, +1`),
the split slice (2 slots `pubSPs, +1`), `xp` -/
abbrev Mcode9 : Type :=
  (Fin 3 → Fin P × Fin P × Fin P) × (Fin 5 → KQ') × KQ' × (Fin 6 → KC) × (Fin 8 → KC) × (Fin 4 → KC) ×
    (Fin 12 → KC) × (Fin 8 → KC) × (Fin 4 → KC) × (Fin 2 → KC) × (Fin 33 → ZMod P)

def decM9 (m : Mcode9) : Msg9 :=
  (⟨⟨fun k => ((m.1 k).1.val, (m.1 k).2.1.val, (m.1 k).2.2.val), m.2.1, m.2.2.1, ext0 m.2.2.2.1, ext0 m.2.2.2.2.1,
    ext0 m.2.2.2.2.2.1, ext0 m.2.2.2.2.2.2.1, ext0 m.2.2.2.2.2.2.2.1⟩,
    ext0 m.2.2.2.2.2.2.2.2.1, ext0 m.2.2.2.2.2.2.2.2.2.1⟩, m.2.2.2.2.2.2.2.2.2.2)

attribute [local instance] Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.twinFact
  Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.twinAlg

variable (d : Datum9A)


/-! ## 4. the chips -/

def chipC (χ : Coins Φ0 KC) (M : Msg9) :=
  computeChipVCLHX9 d.Pb.hn d.Pb.nodes powerBasis3 deltaF (chalVJ8 powerBasis3 χ) (xpF M.2) d.Pb.orbit
def chipM (χ : Coins Φ0 KC) (M : Msg9) :=
  cellChipHQKW deltaF powerBasis3 d.Pb.hnC d.Pb.nodesC d.Pb.orbitC (chalsMJ8 deltaF χ) M.1.pubsC
def chipW (χ : Coins Φ0 KC) (M : Msg9) :=
  walkChipJ8 deltaF d.Pb.kroots powerBasis3 d.Pb.hnW d.Pb.nodesW d.Pb.orbitW (chalsMJ8 deltaF χ) M.1.pubsW
def chipJ (χ : Coins Φ0 KC) (M : Msg9) :=
  jetChipJ8 deltaF powerBasis3 d.Pb.nodesJ d.Pb.orbitJ (chalsJJ8 χ) M.1.pubsJ d.Pb.lay
/-- the atom table, read by the variant chip `atomChipHQL` (as at J-8; `atomChipHQ` is its `toHQ` view) -/
def chipA (χ : Coins Φ0 KC) (M : Msg9) :=
  atomChipHQL deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA
def chipV (χ : Coins Φ0 KC) (M : Msg9) :=
  walkChipHQK deltaF d.Pb.krootsV powerBasis3 d.Pb.hnV d.Pb.nodesV d.Pb.orbitV (chalsAJ8Z deltaF χ) M.1.pubsV
def chipX (χ : Coins Φ0 KC) (M : Msg9) :=
  AxisChipJ9.axisChipJ9 deltaF powerBasis3 d.Pb.hnX d.Pb.nodesX d.Pb.orbitX (chalsMJ8 deltaF χ) M.1.pubsX
def chipS (χ : Coins Φ0 KC) (M : Msg9) :=
  SplitChipJ9.splitChipJ9 deltaF d.Pb.nA powerBasis3 d.Pb.hnS d.Pb.nodesS d.Pb.orbitS (chalsMJ8 deltaF χ) M.1.pubsS

/-- the number of constraints of each table (independent of the coins and the message) -/
def sz9 : Fin 8 → ℕ
  | 0 => (computeChipVCLHX9 d.Pb.hn d.Pb.nodes powerBasis3 deltaF (fun _ => 0) (fun _ => 0) d.Pb.orbit).rap.s
  | 1 => (cellChipHQKW deltaF powerBasis3 d.Pb.hnC d.Pb.nodesC d.Pb.orbitC (fun _ => 0) (fun _ => 0)).rap.s
  | 2 => (walkChipJ8 deltaF d.Pb.kroots powerBasis3 d.Pb.hnW d.Pb.nodesW d.Pb.orbitW (fun _ => 0) (fun _ => 0)).rap.s
  | 3 => (jetChipJ8 deltaF powerBasis3 d.Pb.nodesJ d.Pb.orbitJ (fun _ => 0) (fun _ => 0) d.Pb.lay).rap.s
  | 4 => (atomChipHQL deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (fun _ => 0) (fun _ => 0)).rap.s
  | 5 => (walkChipHQK deltaF d.Pb.krootsV powerBasis3 d.Pb.hnV d.Pb.nodesV d.Pb.orbitV (fun _ => 0) (fun _ => 0)).rap.s
  | 6 => (AxisChipJ9.axisChipJ9 deltaF powerBasis3 d.Pb.hnX d.Pb.nodesX d.Pb.orbitX (fun _ => 0) (fun _ => 0)).rap.s
  | 7 => (SplitChipJ9.splitChipJ9 deltaF d.Pb.nA powerBasis3 d.Pb.hnS d.Pb.nodesS d.Pb.orbitS (fun _ => 0) (fun _ => 0)).rap.s

/-- the constraint `l` of table `t`, truncated into the interface variables -/
def consT9 (χ : Coins Φ0 KC) (M : Msg9) : (t : Fin 8) → Fin (sz9 d t) → MvPolynomial (Ι9 × Fin 2) (ZMod P)
  | 0, l => truncP (fun j => iC (Fin.cast (computeChipVCLHX9_width d.Pb.hn d.Pb.nodes powerBasis3 deltaF
      (chalVJ8 powerBasis3 χ) (xpF M.2) d.Pb.orbit) j)) ((chipC d χ M).rap.C l)
  | 1, l => truncP (fun j => iM (Fin.cast (CellTwinKW.cellChipHQKW_width deltaF powerBasis3 d.Pb.hnC d.Pb.nodesC
      d.Pb.orbitC (chalsMJ8 deltaF χ) M.1.pubsC) j)) ((chipM d χ M).rap.C l)
  | 2, l => truncP (fun j => iW (Fin.cast (WalkJ8.walkChipJ8_width deltaF d.Pb.kroots powerBasis3 d.Pb.hnW
      d.Pb.nodesW d.Pb.orbitW (chalsMJ8 deltaF χ) M.1.pubsW) j)) ((chipW d χ M).rap.C l)
  | 3, l => truncP (fun j => iJ (Fin.cast (Nock.Jet.ChipJ8.jetChipJ8_width deltaF powerBasis3
      d.Pb.nodesJ d.Pb.orbitJ (chalsJJ8 χ) M.1.pubsJ d.Pb.lay) j)) ((chipJ d χ M).rap.C l)
  | 4, l => truncP (fun j => iA (Fin.cast (AtomChipHQL.atomChipHQL_width deltaF powerBasis3
      d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA) j)) ((chipA d χ M).rap.C l)
  | 5, l => truncP (fun j => iV (Fin.cast (CellTwinK.walkChipHQK_width deltaF d.Pb.krootsV
      powerBasis3 d.Pb.hnV d.Pb.nodesV d.Pb.orbitV (chalsAJ8Z deltaF χ) M.1.pubsV) j)) ((chipV d χ M).rap.C l)
  | 6, l => truncP (fun j => iX (Fin.cast (AxisChipJ9.width_eq deltaF powerBasis3 d.Pb.hnX d.Pb.nodesX
      d.Pb.orbitX (chalsMJ8 deltaF χ) M.1.pubsX) j)) ((chipX d χ M).rap.C l)
  | 7, l => truncP (fun j => iS (Fin.cast (SplitChipJ9.width_eq deltaF d.Pb.nA powerBasis3 d.Pb.hnS d.Pb.nodesS
      d.Pb.orbitS (chalsMJ8 deltaF χ) M.1.pubsS) j)) ((chipS d χ M).rap.C l)

theorem consT9_deg (χ : Coins Φ0 KC) (M : Msg9) (t : Fin 8) (l : Fin (sz9 d t)) :
    (consT9 d χ M t l).totalDegree ≤ 4 := by
  match t, l with
  | 0, l => exact (truncP_deg _ _).trans ((chipC d χ M).rap.C_deg l)
  | 1, l => exact (truncP_deg _ _).trans ((chipM d χ M).rap.C_deg l)
  | 2, l => exact (truncP_deg _ _).trans ((chipW d χ M).rap.C_deg l)
  | 3, l => exact (truncP_deg _ _).trans ((chipJ d χ M).rap.C_deg l)
  | 4, l => exact (truncP_deg _ _).trans ((chipA d χ M).rap.C_deg l)
  | 5, l => exact (truncP_deg _ _).trans ((chipV d χ M).rap.C_deg l)
  | 6, l => exact (truncP_deg _ _).trans ((chipX d χ M).rap.C_deg l)
  | 7, l => exact (truncP_deg _ _).trans ((chipS d χ M).rap.C_deg l)

/-- the row shift of each table -/
def omegaOf9 : Fin 8 → ZMod P
  | 0 => d.Pb.orbit.ω
  | 1 => d.Pb.orbitC.ω
  | 2 => d.Pb.orbitW.ω
  | 3 => d.Pb.orbitJ.ω
  | 4 => d.Pb.orbitA.ω
  | 5 => d.Pb.orbitV.ω
  | 6 => d.Pb.orbitX.ω
  | 7 => d.Pb.orbitS.ω

def tabΙ9 : Ι9 → Fin 8 :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (Sum.elim (fun _ => 2) (Sum.elim (fun _ => 3)
    (Sum.elim (fun _ => 4) (Sum.elim (fun _ => 5) (Sum.elim (fun _ => 6) (fun _ => 7)))))))

/-- the fixed columns (zero coins: the preprocessing does not read them) -/
def preJ9 : Ι9 → Option (ZMod P)[X]
  | Sum.inl c => preOf (computeChipVCLHX9 d.Pb.hn d.Pb.nodes powerBasis3 deltaF (fun _ => 0) (fun _ => 0) d.Pb.orbit)
      (Fin.cast (computeChipVCLHX9_width d.Pb.hn d.Pb.nodes powerBasis3 deltaF (fun _ => 0) (fun _ => 0) d.Pb.orbit).symm c)
  | Sum.inr (Sum.inl c) => preOf (cellChipHQKW deltaF powerBasis3 d.Pb.hnC d.Pb.nodesC d.Pb.orbitC (fun _ => 0) (fun _ => 0))
      (Fin.cast (CellTwinKW.cellChipHQKW_width deltaF powerBasis3 d.Pb.hnC d.Pb.nodesC d.Pb.orbitC (fun _ => 0) (fun _ => 0)).symm c)
  | Sum.inr (Sum.inr (Sum.inl c)) => preOf (walkChipJ8 deltaF d.Pb.kroots powerBasis3 d.Pb.hnW d.Pb.nodesW d.Pb.orbitW (fun _ => 0) (fun _ => 0))
      (Fin.cast (WalkJ8.walkChipJ8_width deltaF d.Pb.kroots powerBasis3 d.Pb.hnW d.Pb.nodesW d.Pb.orbitW (fun _ => 0) (fun _ => 0)).symm c)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl c))) => preOf (jetChipJ8 deltaF powerBasis3 d.Pb.nodesJ d.Pb.orbitJ (fun _ => 0) (fun _ => 0) d.Pb.lay)
      (Fin.cast (Nock.Jet.ChipJ8.jetChipJ8_width deltaF powerBasis3 d.Pb.nodesJ d.Pb.orbitJ (fun _ => 0) (fun _ => 0) d.Pb.lay).symm c)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c)))) => preOf (atomChipHQL deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (fun _ => 0) (fun _ => 0))
      (Fin.cast (AtomChipHQL.atomChipHQL_width deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (fun _ => 0) (fun _ => 0)).symm c)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c))))) => preOf (walkChipHQK deltaF d.Pb.krootsV powerBasis3 d.Pb.hnV d.Pb.nodesV d.Pb.orbitV (fun _ => 0) (fun _ => 0))
      (Fin.cast (CellTwinK.walkChipHQK_width deltaF d.Pb.krootsV powerBasis3 d.Pb.hnV d.Pb.nodesV d.Pb.orbitV (fun _ => 0) (fun _ => 0)).symm c)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c)))))) => preOf (AxisChipJ9.axisChipJ9 deltaF powerBasis3 d.Pb.hnX d.Pb.nodesX d.Pb.orbitX (fun _ => 0) (fun _ => 0))
      (Fin.cast (AxisChipJ9.width_eq deltaF powerBasis3 d.Pb.hnX d.Pb.nodesX d.Pb.orbitX (fun _ => 0) (fun _ => 0)).symm c)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr c)))))) => preOf (SplitChipJ9.splitChipJ9 deltaF d.Pb.nA powerBasis3 d.Pb.hnS d.Pb.nodesS d.Pb.orbitS (fun _ => 0) (fun _ => 0))
      (Fin.cast (SplitChipJ9.width_eq deltaF d.Pb.nA powerBasis3 d.Pb.hnS d.Pb.nodesS d.Pb.orbitS (fun _ => 0) (fun _ => 0)).symm c)


/-! ## 5. `Pub`, `StmtOK`, the present tables -/

/-- the eight public equations of `AcceptsJ9A` (hGx, hGp, hGS, hsumC', hbalA', hvalA0, hfxC, hfxA) at the interface message -/
def PubEq9A (χ : Coins Φ0 KC) (M : Msg9) : Prop :=
  (M.1.ρ 3 + (Quad.mk _ (M.1.pubsW WalkHQ.pubXQ) (M.1.pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (M.1.pubsJ 2) (M.1.pubsJ 3)) =
    Quad.mk _ (M.1.pubsC CellHQ.pubHQ) (M.1.pubsC (CellHQ.pubHQ + 1))) ∧
  (M.1.ρ 4 + Quad.mk _ (M.1.pubsX AxisChipJ9.pubAXp) (M.1.pubsX (AxisChipJ9.pubAXp + 1)) =
    Quad.mk _ (M.1.pubsW WalkHQ.pubPQ) (M.1.pubsW (WalkHQ.pubPQ + 1))) ∧
  (M.1.ρS + ((pinCons (p := P) (K := KC) d.Pb.regs d.Pb.idx).map fun r =>
      (compress (coinsCV powerBasis3 deltaF (chalVJ8 powerBasis3 χ)) (liftRec (L := KQ') r))⁻¹).sum +
      Quad.mk _ (M.1.pubsJ 0) (M.1.pubsJ 1) +
      Quad.mk _ (M.1.pubsX AxisChipJ9.pubAXs) (M.1.pubsX (AxisChipJ9.pubAXs + 1)) =
    Quad.mk _ (M.1.pubsA AtomChipHQ.pubMI) (M.1.pubsA (AtomChipHQ.pubMI + 1)) +
      Quad.mk _ (M.1.pubsV WalkHQ.pubPQ) (M.1.pubsV (WalkHQ.pubPQ + 1)) +
      Quad.mk _ (M.1.pubsS SplitChipJ9.pubSPs) (M.1.pubsS (SplitChipJ9.pubSPs + 1))) ∧
  (((claimRecsJ9 deltaF χ d.c M.1.m ++ pinRecsJ8 deltaF d.Pb.toPubJ8 χ).map fun r => (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
    Quad.mk (algebraMap (ZMod P) KC deltaF) (M.1.pubsC 0) (M.1.pubsC 1) +
      Quad.mk (algebraMap (ZMod P) KC deltaF) (M.1.pubsA AtomChipHQ.pubMB) (M.1.pubsA (AtomChipHQ.pubMB + 1))) ∧
  (Quad.mk (algebraMap (ZMod P) KC deltaF) (M.1.pubsA CellHQ.pubHQ) (M.1.pubsA (CellHQ.pubHQ + 1)) =
    Quad.mk (algebraMap (ZMod P) KC deltaF) (M.1.pubsA AtomChipHQ.pubC) (M.1.pubsA (AtomChipHQ.pubC + 1)) +
      Quad.mk (algebraMap (ZMod P) KC deltaF) (M.1.pubsV WalkHQ.pubXQ) (M.1.pubsV (WalkHQ.pubXQ + 1))) ∧
  (M.1.pubsA 0 = 0 ∧ M.1.pubsA 1 = 0) ∧
  (M.1.pubsC 2 = M.1.pubsW 0 ∧ M.1.pubsC 3 = M.1.pubsW 1) ∧
  (M.1.pubsA 2 = M.1.pubsV 0 ∧ M.1.pubsA 3 = M.1.pubsV 1)

/-- **`Pub`**: the eight public equations, `hclI` (widened to big atoms), absent ⇒ publics `0` (V, J, **X, S**), the compute
publics `= pubVJ9` -/
def PubP9A (χ : Coins Φ0 KC) (M : Msg9) : Prop :=
  PubEq9A d χ M ∧
  (∀ k : Fin 3, (isCellN (claimNoun d.c k) = true ∨ isBigN P (claimNoun d.c k) = true) → (M.1.m k).1 < P) ∧
  ((d.Pb.krootsV = 0 → M.1.pubsV 0 = 0 ∧ M.1.pubsV 1 = 0 ∧ M.1.pubsV WalkHQ.pubXQ = 0 ∧ M.1.pubsV (WalkHQ.pubXQ + 1) = 0 ∧
      M.1.pubsV WalkHQ.pubPQ = 0 ∧ M.1.pubsV (WalkHQ.pubPQ + 1) = 0) ∧
    (d.Pb.nJ = 0 → M.1.pubsJ 0 = 0 ∧ M.1.pubsJ 1 = 0 ∧ M.1.pubsJ 2 = 0 ∧ M.1.pubsJ 3 = 0) ∧
    (d.Pb.axOn = false → M.1.pubsX AxisChipJ9.pubAXs = 0 ∧ M.1.pubsX (AxisChipJ9.pubAXs + 1) = 0 ∧
      M.1.pubsX AxisChipJ9.pubAXp = 0 ∧ M.1.pubsX (AxisChipJ9.pubAXp + 1) = 0) ∧
    (d.Pb.spOn = false → M.1.pubsS SplitChipJ9.pubSPs = 0 ∧ M.1.pubsS (SplitChipJ9.pubSPs + 1) = 0)) ∧
  (∀ j : Fin 33, M.2 j = pubVJ9 deltaF powerBasis3 d.c M.1.m M.1.ρ M.1.ρS χ j)

/-- the static (statement-level) conjuncts of `AcceptsJ9A` -/
structure StmtP9A : Prop where
  hinjX : Function.Injective d.Pb.nodes
  hadjX : ∀ (i : Fin d.Pb.n) (hi : (i : ℕ) + 1 < d.Pb.n), d.Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = d.Pb.nodes i * d.Pb.orbit.ω
  hinjC : Function.Injective d.Pb.nodesC
  hadjC : ∀ (i : Fin d.Pb.nC) (hi : (i : ℕ) + 1 < d.Pb.nC), d.Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = d.Pb.nodesC i * d.Pb.orbitC.ω
  hnpC : d.Pb.nC < ringChar (ZMod P)
  hinjW : Function.Injective d.Pb.nodesW
  hadjW : ∀ (i : Fin d.Pb.nW) (hi : (i : ℕ) + 1 < d.Pb.nW), d.Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = d.Pb.nodesW i * d.Pb.orbitW.ω
  hkW : 1 ≤ d.Pb.kroots
  hknW : d.Pb.kroots ≤ d.Pb.nW
  hkpW : d.Pb.kroots + d.Pb.nW < ringChar (ZMod P)
  hJst : d.Pb.nJ ≠ 0 → Function.Injective d.Pb.nodesJ ∧
    ∀ (i : Fin d.Pb.nJ) (hi : (i : ℕ) + 1 < d.Pb.nJ), d.Pb.nodesJ ⟨(i : ℕ) + 1, hi⟩ = d.Pb.nodesJ i * d.Pb.orbitJ.ω
  hinjA : Function.Injective d.Pb.nodesA
  hadjA : ∀ (i : Fin d.Pb.nA) (hi : (i : ℕ) + 1 < d.Pb.nA), d.Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = d.Pb.nodesA i * d.Pb.orbitA.ω
  hnpA : d.Pb.nA < P
  hVst : d.Pb.krootsV ≠ 0 → Function.Injective d.Pb.nodesV ∧
    (∀ (i : Fin d.Pb.nV) (hi : (i : ℕ) + 1 < d.Pb.nV), d.Pb.nodesV ⟨(i : ℕ) + 1, hi⟩ = d.Pb.nodesV i * d.Pb.orbitV.ω) ∧
    1 ≤ d.Pb.krootsV ∧ d.Pb.krootsV ≤ d.Pb.nV ∧ d.Pb.krootsV + d.Pb.nV < ringChar (ZMod P)
  /-- the axis geometry, inside AXChipOK's PRESENT disjunct -/
  hXst : d.Pb.axOn = true → Function.Injective d.Pb.nodesX ∧
    (∀ (i : Fin d.Pb.nX) (hi : (i : ℕ) + 1 < d.Pb.nX), d.Pb.nodesX ⟨(i : ℕ) + 1, hi⟩ = d.Pb.nodesX i * d.Pb.orbitX.ω) ∧
    d.Pb.nX < P
  /-- the split geometry, inside SPChipOK's PRESENT disjunct -/
  hSst : d.Pb.spOn = true → Function.Injective d.Pb.nodesS ∧
    (∀ (i : Fin d.Pb.nS) (hi : (i : ℕ) + 1 < d.Pb.nS), d.Pb.nodesS ⟨(i : ℕ) + 1, hi⟩ = d.Pb.nodesS i * d.Pb.orbitS.ω) ∧
    d.Pb.nS < P
  hlay : List.ofFn d.Pb.lay = layoutJ8 d.Pb.Rt d.Pb.regs d.Pb.ids
  hsmall : ∀ q ∈ layoutJ8 d.Pb.Rt d.Pb.regs d.Pb.ids, q.id < P ∧ q.cid < P ∧ q.nid < P ∧ q.n1 < P ∧ q.n2 < P
  huniq : ((layoutJ8 d.Pb.Rt d.Pb.regs d.Pb.ids).filterMap tvKey).Nodup
  hTpl : ∀ i ∈ d.Pb.regs, d.Rg i = some ⟨(d.Pb.Rt i).toTemplate P, Nock.Jet.Autogen.compile P (d.Pb.Rt i)⟩ ∧
    axPosB (d.Pb.Rt i) = true ∧ (d.Pb.Rt i).WellTyped P
  hnd : d.Pb.regs.Nodup
  hidx : ∀ id ∈ d.Pb.regs, d.Pb.idx id < P
  hrk : ∀ id ∈ d.Pb.regs, d.Pb.rk id ≠ (0, 0)
  hlt : ∀ id ∈ d.Pb.regs, (d.Pb.rk id).1 < ringChar (ZMod P) ∧ (d.Pb.rk id).2 < ringChar (ZMod P) ∧
    d.Pb.idx id < ringChar (ZMod P)
  hclR : ∀ k : Fin 3, isCellN (claimNoun d.c k) = true → (claimNoun d.c k).internal / 2 ^ 62 < P
  hcen' : ∀ x ∈ censusGJ9 d.Pb.toPubJ8 d.c, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, lenL v ≤ d.Pb.nA + 2
  hlenC : 3 + d.Pb.regs.length + 2 * d.Pb.nC < P
  hlenA : d.Pb.nA + d.Pb.nV < P
  hcellF : isCellN d.c.formula = true
  /-- replaces `hnA62` -/
  hnAS : d.Pb.nA + d.Pb.nS < 2 ^ 57
  hbud : BudJ9A d.Pb d.r (d.g + d.r.N)
  hbudV : d.Pb.regs.length ≤ d.g ∧ d.Pb.nA ≤ d.r.mb ∧ d.Pb.nA ≤ d.r.A ∧ d.Pb.nV ≤ d.r.AW ∧
    d.Pb.nX ≤ d.r.AX ∧ d.Pb.nS ≤ d.r.SP
  hlenX : d.Pb.nX + d.Pb.n < P ∧ 2 * d.Pb.nS < P

/-- the tables present at the J-9 A side: the jet / atom walk / axis / split may be absent -/
def present9A (t : Fin 8) : Prop :=
  ¬(t = 3 ∧ d.Pb.nJ = 0) ∧ ¬(t = 5 ∧ d.Pb.krootsV = 0) ∧ ¬(t = 6 ∧ d.Pb.axOn = false) ∧ ¬(t = 7 ∧ d.Pb.spOn = false)

/-- the accept predicate of J-9 A, over nock's message and trace -/
def AccJ9A (d : Datum9A) :
    Coins Φ0 KC → MsgJ9A' P KC deltaF → TrJ9A (ZMod P) → Prop :=
  fun χ M tr => AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 d.Pb d.Rg d.c χ M tr d.r d.g

theorem accGen9A (hd : DatumOK9A d) (χ : Coins Φ0 KC) (M : Msg9) (tr : Ι9 → (ZMod P)[X])
    (hv : ∀ t : Fin 8, present9A d t → ∀ l : Fin (sz9 d t), ∀ x ∈ HtOf9 d t, (MvPolynomial.aeval
      (fun q : Ι9 × Fin 2 => (tr q.1).comp (Polynomial.C (omegaOf9 d (tabΙ9 q.1) ^ (q.2 : ℕ)) * Polynomial.X))
      (consT9 d χ M t l)).eval x = 0)
    (hp : PubP9A d χ M) (hs : StmtP9A d)
    (hpre : ∀ j c, present9A d (tabΙ9 j) → preJ9 d j = some c → tr j = c) :
    AccJ9A d χ M.1 (unflat9 tr) := by
  obtain ⟨hPE, hclI, ⟨habsV, habsJ, habsX, habsS⟩, hder⟩ := hp
  obtain ⟨hGx, hGp, hGS, hsumC', hbalA', hvalA0, hfxC, hfxA⟩ := hPE
  have hxp : xpF M.2 = pubVJ9 deltaF powerBasis3 d.c M.1.m M.1.ρ M.1.ρS χ := by
    funext j
    unfold xpF
    split_ifs with h
    · exact hder ⟨j, h⟩
    · have h12 : 12 ≤ j := by omega
      have h27 : ¬ j < 27 := by omega
      have h30 : ¬ j < 30 := by omega
      rw [pubVJ9_hi deltaF powerBasis3 d.c M.1.m M.1.ρ M.1.ρS χ j h12]
      simp [pubVJ8, h27, h30, h]
  have hp0 : present9A d 0 := by unfold present9A; simp
  have hp1 : present9A d 1 := by unfold present9A; simp
  have hp2 : present9A d 2 := by unfold present9A; simp
  have hp4 : present9A d 4 := by unfold present9A; simp
  have cX : ∀ pv, xpF M.2 = pv → RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX9 d.Pb.hn d.Pb.nodes powerBasis3 deltaF (chalVJ8 powerBasis3 χ) pv d.Pb.orbit)
      (fun j => tr (iC (Fin.cast (computeChipVCLHX9_width d.Pb.hn d.Pb.nodes powerBasis3 deltaF
        (chalVJ8 powerBasis3 χ) pv d.Pb.orbit) j))) := by
    intro pv hpv
    subst hpv
    exact chip_ok (chipC d χ M) _ tr (fun q => omegaOf9 d (tabΙ9 q)) (fun j => rfl) (hI_expand) (preJ9 d)
      (fun c q hj => hpre _ q hp0 hj) (fun c => rfl) (fun i x hx => hv 0 hp0 i x hx)
  have cM := chip_ok (chipM d χ M) (fun j => iM (Fin.cast (CellTwinKW.cellChipHQKW_width deltaF powerBasis3
      d.Pb.hnC d.Pb.nodesC d.Pb.orbitC (chalsMJ8 deltaF χ) M.1.pubsC) j)) tr (fun q => omegaOf9 d (tabΙ9 q))
      (fun j => rfl) (hI_expand) (preJ9 d) (fun c q hj => hpre _ q hp1 hj) (fun c => rfl) (fun i x hx => hv 1 hp1 i x hx)
  have cW := chip_ok (chipW d χ M) (fun j => iW (Fin.cast (WalkJ8.walkChipJ8_width deltaF d.Pb.kroots
      powerBasis3 d.Pb.hnW d.Pb.nodesW d.Pb.orbitW (chalsMJ8 deltaF χ) M.1.pubsW) j)) tr (fun q => omegaOf9 d (tabΙ9 q))
      (fun j => rfl) (hI_expand) (preJ9 d) (fun c q hj => hpre _ q hp2 hj) (fun c => rfl) (fun i x hx => hv 2 hp2 i x hx)
  have cA := chip_ok (chipA d χ M) (fun j => iA (Fin.cast
      (AtomChipHQL.atomChipHQL_width deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA) j))
      tr (fun q => omegaOf9 d (tabΙ9 q))
      (fun j => rfl) (hI_expand) (preJ9 d) (fun c q hj => hpre _ q hp4 hj) (fun c => rfl) (fun i x hx => hv 4 hp4 i x hx)
  have hJk : JGenJ8.JChipOK deltaF powerBasis3 d.Pb.nodesJ d.Pb.orbitJ (chalsJJ8 χ) M.1.pubsJ d.Pb.lay
      (AcceptsJ8.qJ deltaF powerBasis3 d.Pb.toPubJ8 (unflat9 tr).toJ8 (chalsJJ8 χ) M.1.pubsJ) := by
    by_cases h0 : d.Pb.nJ = 0
    · obtain ⟨a, b, c, e⟩ := habsJ h0
      exact Or.inr ⟨h0, a, b, c, e⟩
    · have hp3 : present9A d 3 := by unfold present9A; simp [h0]
      have cJ := chip_ok (chipJ d χ M) (fun j => iJ (Fin.cast
        (Nock.Jet.ChipJ8.jetChipJ8_width deltaF powerBasis3 d.Pb.nodesJ d.Pb.orbitJ (chalsJJ8 χ) M.1.pubsJ d.Pb.lay) j))
        tr (fun q => omegaOf9 d (tabΙ9 q)) (fun j => rfl) (hI_expand) (preJ9 d) (fun c q hj => hpre _ q hp3 hj) (fun c => rfl)
        (fun i x hx => hv 3 hp3 i x hx)
      obtain ⟨hinj, hadj⟩ := hs.hJst h0
      exact Or.inl ⟨cJ.1, cJ.2, hinj, Nat.pos_of_ne_zero h0, hadj⟩
  have hVk : AcceptsJ8V.AWChipOK deltaF powerBasis3 d.Pb.krootsV d.Pb.hnV d.Pb.nodesV d.Pb.orbitV (chalsAJ8Z deltaF χ)
      M.1.pubsV (AcceptsJ8.qV deltaF powerBasis3 d.Pb.toPubJ8 (unflat9 tr).toJ8 (chalsAJ8Z deltaF χ) M.1.pubsV) := by
    by_cases h0 : d.Pb.krootsV = 0
    · obtain ⟨a, b, c, e, f, g⟩ := habsV h0
      exact Or.inr ⟨h0, a, b, c, e, f, g⟩
    · have hp5 : present9A d 5 := by unfold present9A; simp [h0]
      have cV := chip_ok (chipV d χ M) (fun j => iV (Fin.cast
        (CellTwinK.walkChipHQK_width deltaF d.Pb.krootsV powerBasis3 d.Pb.hnV d.Pb.nodesV d.Pb.orbitV (chalsAJ8Z deltaF χ)
          M.1.pubsV) j))
        tr (fun q => omegaOf9 d (tabΙ9 q)) (fun j => rfl) (hI_expand) (preJ9 d) (fun c q hj => hpre _ q hp5 hj) (fun c => rfl)
        (fun i x hx => hv 5 hp5 i x hx)
      obtain ⟨hinj, hadj, h1, h2, h3⟩ := hs.hVst h0
      exact Or.inl ⟨cV.1, cV.2, hinj, hadj, h1, h2, h3⟩
  have hAXk : AcceptsJ9A.AXChipOK deltaF powerBasis3 d.Pb.axOn d.Pb.hnX d.Pb.nodesX d.Pb.orbitX (chalsMJ8 deltaF χ)
      M.1.pubsX (qAX deltaF powerBasis3 d.Pb (unflat9 tr) (chalsMJ8 deltaF χ) M.1.pubsX) := by
    by_cases h0 : d.Pb.axOn = false
    · obtain ⟨a, b, c, e⟩ := habsX h0
      exact Or.inr ⟨h0, a, b, c, e⟩
    · have h1 : d.Pb.axOn = true := by simpa using h0
      have hp6 : present9A d 6 := by unfold present9A; simp [h1]
      have cX' := chip_ok (chipX d χ M) (fun j => iX (Fin.cast
        (AxisChipJ9.width_eq deltaF powerBasis3 d.Pb.hnX d.Pb.nodesX d.Pb.orbitX (chalsMJ8 deltaF χ) M.1.pubsX) j))
        tr (fun q => omegaOf9 d (tabΙ9 q)) (fun j => rfl) (hI_expand) (preJ9 d) (fun c q hj => hpre _ q hp6 hj) (fun c => rfl)
        (fun i x hx => hv 6 hp6 i x hx)
      obtain ⟨hinj, hadj, hlt⟩ := hs.hXst h1
      exact Or.inl ⟨h1, cX'.1, cX'.2, hinj, hadj, hlt⟩
  have hSPk : AcceptsJ9A.SPChipOK deltaF powerBasis3 d.Pb.nA d.Pb.spOn d.Pb.hnS d.Pb.nodesS d.Pb.orbitS (chalsMJ8 deltaF χ)
      M.1.pubsS (qSP deltaF powerBasis3 d.Pb (unflat9 tr) (chalsMJ8 deltaF χ) M.1.pubsS) := by
    by_cases h0 : d.Pb.spOn = false
    · obtain ⟨a, b⟩ := habsS h0
      exact Or.inr ⟨h0, a, b⟩
    · have h1 : d.Pb.spOn = true := by simpa using h0
      have hp7 : present9A d 7 := by unfold present9A; simp [h1]
      have cS' := chip_ok (chipS d χ M) (fun j => iS (Fin.cast
        (SplitChipJ9.width_eq deltaF d.Pb.nA powerBasis3 d.Pb.hnS d.Pb.nodesS d.Pb.orbitS (chalsMJ8 deltaF χ) M.1.pubsS) j))
        tr (fun q => omegaOf9 d (tabΙ9 q)) (fun j => rfl) (hI_expand) (preJ9 d) (fun c q hj => hpre _ q hp7 hj) (fun c => rfl)
        (fun i x hx => hv 7 hp7 i x hx)
      obtain ⟨hinj, hadj, hlt⟩ := hs.hSst h1
      exact Or.inl ⟨h1, cS'.1, cS'.2, hinj, hadj, hlt⟩
  have hL : (atomChipHQL deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA).rap.Satisfies
      (AcceptsJ8L.qAL deltaF powerBasis3 d.Pb.toPubJ8 (unflat9 tr).toJ8 (chalsAJ8Z deltaF χ) M.1.pubsA) := cA.1
  have hLb : (atomChipHQL deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA).BindsPreprocessing
      (AcceptsJ8L.qAL deltaF powerBasis3 d.Pb.toPubJ8 (unflat9 tr).toJ8 (chalsAJ8Z deltaF χ) M.1.pubsA) := cA.2
  have hA1 := AtomChipHQL.atomChipHQL_sat deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA _ hL
  have hA2 := AtomChipHQL.atomChipHQL_bind deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA _ hLb
  rw [AcceptsJ8L.qAL_toHQ] at hA1 hA2
  exact
    { hsatX := cX _ hxp
      hinjX := hs.hinjX
      hadjX := hs.hadjX
      hsatC := cM.1
      hbindC := cM.2
      hinjC := hs.hinjC
      hadjC := hs.hadjC
      hnpC := hs.hnpC
      hsatW := cW.1
      hbindW := cW.2
      hinjW := hs.hinjW
      hadjW := hs.hadjW
      hkW := hs.hkW
      hknW := hs.hknW
      hkpW := hs.hkpW
      hJk := hJk
      hsatA := hA1
      hbindA := hA2
      hinjA := hs.hinjA
      hadjA := hs.hadjA
      hnpA := hs.hnpA
      hVk := hVk
      hGx := hGx
      hGp := hGp
      hGS := hGS
      hlay := hs.hlay
      hsmall := hs.hsmall
      huniq := hs.huniq
      hTpl := hs.hTpl
      hnd := hs.hnd
      hidx := hs.hidx
      hrk := hs.hrk
      hlt := hs.hlt
      hsumC' := hsumC'
      hbalA' := hbalA'
      hvalA0 := hvalA0
      hfxC := hfxC
      hfxA := hfxA
      hclI := hclI
      hclR := hs.hclR
      hcen' := hs.hcen'
      hlenC := hs.hlenC
      hlenA := hs.hlenA
      hcellF := hs.hcellF
      hnAS := hs.hnAS
      hbud := hs.hbud
      hbudV := hs.hbudV
      hsatL := cA.1
      hbindL := cA.2
      hAXk := hAXk
      hSPk := hSPk
      hlenX := hs.hlenX }


/-! ## 6. caps -/

def ns9 : ℕ := ∑ t : Fin 8, sz9 d t

set_option maxRecDepth 100000 in
theorem len_compute9 : (gatesHX9 powerBasis3 deltaF).length ≤ 5000 := by decide +kernel

theorem sz9_le (t : Fin 8) : sz9 d t ≤ 5000 := by
  fin_cases t
  · exact (gatesHX9P_length powerBasis3 deltaF).trans_le len_compute9
  · exact len_cell
  · exact len_walkJ8 _
  · exact len_jet
  · exact len_atom
  · exact len_walkHQK _
  · exact ((AxisChipJ9.axisChipJ9_fingerprint deltaF powerBasis3 d.Pb.hnX d.Pb.nodesX d.Pb.orbitX
      (fun _ => 0) (fun _ => 0)).2.1).trans_le (by norm_num)
  · exact ((SplitChipJ9.splitChipJ9_fingerprint deltaF d.Pb.nA powerBasis3 d.Pb.hnS d.Pb.nodesS d.Pb.orbitS
      (fun _ => 0) (fun _ => 0)).2.1).trans_le (by norm_num)

theorem cap_ns9_of : ns9 d ≤ 2 ^ 20 := by
  unfold ns9
  calc ∑ t, sz9 d t ≤ ∑ _t : Fin 8, 5000 := Finset.sum_le_sum fun t _ => sz9_le d t
    _ = 40000 := by simp
    _ ≤ 2 ^ 20 := by norm_num

theorem cap_H9_of (hd : DatumOK9A d) : (HdomOf9 d).card ≤ 2 ^ 26 :=
  (Finset.card_image_le.trans (by simpa using hd.hcapH))

/-! ## 7. `clJ9A`: the J-9 A chip layer -/

open Classical in
set_option maxRecDepth 50000 in
/-- **`clJ9A`**: the J-9 A chip layer (the twin of `IfaceG.clJ8`) -/
noncomputable def clJ9A (hd : DatumOK9A d) :
    CLay (Tr := TrJ9A (ZMod P)) StJ9A (MsgJ9A' P KC deltaF) (AccJ9A d) where
  ι0 := Ι9
  fι := inferInstance
  dι := inferInstance
  colR := colR9
  hround := colR9_le
  unflat := unflat9
  stUnflat := stJ9A_unflat
  pre := preJ9 d
  Msg := Msg9
  Mcode := Mcode9
  fM := inferInstance
  dM := inferInstance
  dec := decM9
  msg0 := Prod.fst
  T := 8
  Ht := HtOf9 d
  H := HdomOf9 d
  hHt := hd.hHt
  ωt := omegaOf9 d
  tabC := tabΙ9
  sz := sz9 d
  consT := consT9 d
  hdeg χ M t l := consT9_deg d χ M t l
  Pub := PubP9A d
  StmtOK := StmtP9A d
  present := present9A d
  accOn χ M tr hv hp hs hpre := accGen9A d hd χ M tr hv hp hs hpre
  cap_ns := cap_ns9_of d
  cap_m := by
    show Fintype.card Ι9 * 2 + 3 * (4 - 1) ≤ 2 ^ 12
    rw [card_Ι9]; norm_num
  cap_H := cap_H9_of d hd

/-! ## 8. vacuity of `StmtP9A` / `PubP9A`, and R1 (the public-column count) -/

/-- **`StmtP9A` and `PubP9A` are implied by nock's `AcceptsJ9A`** (compute publics `xp := pubVJ9`): they are inhabited wherever
the accept predicate is (e.g. at `complJ9A_closed_absent`'s accepting coin, see `WitJ9A`). -/
theorem stmt_pub_of_acc9 (d : Datum9A) (χ : Coins Φ0 KC) (M : MsgJ9A' P KC deltaF) (tr : TrJ9A (ZMod P))
    (h : AccJ9A d χ M tr) :
    StmtP9A d ∧ PubP9A d χ (M, fun j => pubVJ9 deltaF powerBasis3 d.c M.m M.ρ M.ρS χ j) := by
  refine ⟨⟨h.hinjX, h.hadjX, h.hinjC, h.hadjC, h.hnpC, h.hinjW, h.hadjW, h.hkW, h.hknW, h.hkpW, ?_, h.hinjA, h.hadjA, h.hnpA, ?_,
    ?_, ?_, h.hlay, h.hsmall, h.huniq, h.hTpl, h.hnd, h.hidx, h.hrk, h.hlt, h.hclR, h.hcen', h.hlenC, h.hlenA, h.hcellF,
    h.hnAS, h.hbud, h.hbudV, h.hlenX⟩,
    ⟨h.hGx, h.hGp, h.hGS, h.hsumC', h.hbalA', h.hvalA0, h.hfxC, h.hfxA⟩, h.hclI, ⟨?_, ?_, ?_, ?_⟩, fun j => rfl⟩
  · intro h0
    rcases h.hJk with ⟨-, -, hinj, -, hadj⟩ | ⟨hn0, -⟩
    · exact ⟨hinj, hadj⟩
    · exact absurd hn0 h0
  · intro h0
    rcases h.hVk with ⟨-, -, hinj, hadj, h1, h2, h3⟩ | ⟨hk0, -⟩
    · exact ⟨hinj, hadj, h1, h2, h3⟩
    · exact absurd hk0 h0
  · intro h0
    rcases h.hAXk with ⟨-, -, -, hinj, hadj, hlt⟩ | ⟨hf, -⟩
    · exact ⟨hinj, hadj, hlt⟩
    · rw [h0] at hf; exact absurd hf (by simp)
  · intro h0
    rcases h.hSPk with ⟨-, -, -, hinj, hadj, hlt⟩ | ⟨hf, -⟩
    · exact ⟨hinj, hadj, hlt⟩
    · rw [h0] at hf; exact absurd hf (by simp)
  · intro h0
    rcases h.hVk with ⟨-, -, -, -, h1, -, -⟩ | ⟨-, a, b, c, e, f, g⟩
    · omega
    · exact ⟨a, b, c, e, f, g⟩
  · intro h0
    rcases h.hJk with ⟨-, -, -, hpos, -⟩ | ⟨-, a, b, c, e⟩
    · omega
    · exact ⟨a, b, c, e⟩
  · intro h0
    rcases h.hAXk with ⟨hf, -⟩ | ⟨-, a, b, c, e⟩
    · rw [h0] at hf; exact absurd hf (by simp)
    · exact ⟨a, b, c, e⟩
  · intro h0
    rcases h.hSPk with ⟨hf, -⟩ | ⟨-, a, b⟩
    · rw [h0] at hf; exact absurd hf (by simp)
    · exact ⟨a, b⟩

/-- **R1**: public columns of the J-9 A executed instance per table (compute / cell / walkJ8 / jet / atom / walkHQK / axis / split):
J-8's `PE.tabLens = #[33, 18, 24, 12, 36, 24]` (33 base publics `xp`; `3 ×` the K-slot count 6 / 8 / 4 / 12 / 8 for the five
`MsgJ8'` slices) plus axis `3 × 4` (K-slots `pubAXs, +1, pubAXp, +1`, AxisChipJ9.lean:109-110) and split `3 × 2`
(`pubSPs, +1`, SplitChipJ9.lean:72). [S] counted off the `Mcode9` slices read by `AcceptsJ9A`. -/
def pubLens9A : List ℕ := [33, 18, 24, 12, 36, 24, 12, 6]

/-- **R1 result**: 165 public columns (J-8: 147), and TieJ8G's `Cap npub` bound `(card ι0 + npub) * 2 + 9 ≤ 2^12` holds with
room: the allowed `npub` is `≤ 770` (`(1273 + 770) * 2 + 9 = 4095`), so the cap is NOT binding at J-9 A. -/
theorem pubLens9A_sum : pubLens9A.sum = 165 := by decide

theorem r1_cap9A : (Fintype.card Ι9 + pubLens9A.sum) * 2 + 9 ≤ 2 ^ 12 := by
  rw [card_Ι9, pubLens9A_sum]; norm_num

theorem r1_cap9A_max : (Fintype.card Ι9 + 770) * 2 + 9 ≤ 2 ^ 12 := by
  rw [card_Ι9]; norm_num

/-- **`AcceptsJ9A` is monotone in the row budget and `g`** (rows enter only through `hbud` / `hbudV`; every field an upper bound;
twin of `Batch4775.acceptsJ8V_mono_rows`). Lets a witness at nock's own `BRun9A` rows be restated at the census corner. -/
theorem acceptsJ9A_mono_rows {Pb : PubJ9A P} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : SVFrame.Coins frameJ8 KC}
    {M : MsgJ9A' P KC deltaF} {tr : TrJ9A (ZMod P)} {r r' : RowsJ9A} {g g' : ℕ}
    (h : AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 Pb Rg c χ M tr r g)
    (hN : r.N ≤ r'.N) (hD : r.D ≤ r'.D) (hW : r.W ≤ r'.W) (hJ : r.J ≤ r'.J) (hcalls : r.calls ≤ r'.calls)
    (hheads : r.heads ≤ r'.heads) (hblocks : r.blocks ≤ r'.blocks) (hrd : r.rd ≤ r'.rd) (hmb : r.mb ≤ r'.mb)
    (hA : r.A ≤ r'.A) (hAW : r.AW ≤ r'.AW) (hAX : r.AX ≤ r'.AX) (hSP : r.SP ≤ r'.SP) (hg : g ≤ g') :
    AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 Pb Rg c χ M tr r' g' := by
  have hb := h.hbud
  have hv := h.hbudV
  exact { h with
    hbud := ⟨by have := hb.x1; omega, by have := hb.x2; omega, by have := hb.p1; omega, by have := hb.p2; omega,
      by have := hb.s1; omega, by have := hb.s2; omega⟩
    hbudV := ⟨by have := hv.1; omega, by have := hv.2.1; omega, by have := hv.2.2.1; omega,
      by have := hv.2.2.2.1; omega, by have := hv.2.2.2.2.1; omega, by have := hv.2.2.2.2.2; omega⟩ }

end Inst

#print axioms card_Ι9
#print axioms stJ9A_unflat
#print axioms accGen9A
#print axioms clJ9A
#print axioms stmt_pub_of_acc9
#print axioms pubLens9A_sum
#print axioms r1_cap9A
#print axioms acceptsJ9A_mono_rows

end NockvmE2E.J9A.InstJ9A
