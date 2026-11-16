/-
the J-9 AL twin of `J9A/InstJ9A.lean`.
`Ι9L = Ι9 ⊕ Fin 196` (J-9 A's `Ι9` reused verbatim), `unflat9L`, `Datum9AL`, `DatumOK9AL`, `Msg9L`/`Mcode9L`/`decM9L`, the ALU chip,
`sz9L`, `consT9L`, `omegaOf9L`, `tabΙ9L`, `preJ9L`, `Mof9L`. (`accGen9L`, `clJ9AL` follow in this file.)
Not zero-knowledge.
-/
import NockvmE2E.J9A.InstJ9A
import NockvmE2E.J9A.RVUJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL
import Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

open Polynomial

namespace NockvmE2E.J9AL.InstJ9AL

open NockvmE2E.Rap NockvmE2E.Succ
open NockvmE2E.J8.IfaceG (CLay NIface)
open NockvmE2E.J9A.InstJ9A
open Nock.TraceGenExe Nock.NockVMROM.Thm54.T0Tower
open NockvmE2E.J8.InstJ8 (P Φ0 KQ' truncP truncP_deg chip_ok hI_expand preOf xpF ext0 len_cell len_walkJ8 len_jet len_atom len_walkHQK)

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
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL (pinRecsP censusP)

attribute [local instance] Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.twinFact
  Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.twinAlg

/-! ## 1. the flat column index: the nine tables -/

/-- the nine chips' columns: J-9 A's eight (`Ι9`) then the ALU's 196 -/
abbrev Ι9L : Type := Ι9 ⊕ Fin 196

abbrev iL (j : Fin 196) : Ι9L := Sum.inr j

def colR9L : Ι9L → ℕ := Sum.elim colR9 crAL

theorem colR9L_le : ∀ j, colR9L j ≤ 2 := by
  intro j
  rcases j with j | j
  · exact colR9_le j
  · simp only [colR9L, Sum.elim_inr, crAL]; split_ifs <;> omega

def unflat9L (tr : Ι9L → (ZMod P)[X]) : TrJ9AL (ZMod P) :=
  ⟨unflat9 (tr ∘ Sum.inl), fun j => tr (iL j)⟩

theorem stJ9AL_unflat (Q : Coins Φ0 KC → Ι9L → (ZMod P)[X]) (hQ : TracesStaged Φ0 colR9L Q) :
    StJ9AL (fun χ => unflat9L (Q χ)) := by
  refine ⟨?_, ?_⟩
  · exact stJ9A_unflat (fun χ => Q χ ∘ Sum.inl) (fun j χ χ' h => hQ (Sum.inl j) χ χ' h)
  · intro j χ χ' h
    exact hQ (iL j) χ χ' h

set_option maxRecDepth 100000 in
theorem card_Ι9L : Fintype.card Ι9L = 1469 := by
  rw [Fintype.card_sum, card_Ι9]; simp

/-! ## 2. the datum -/

structure Datum9AL where
  Pb : PubJ9AL P
  Rg : Nock.Jet.Registry
  c : P8PublicClaim
  r : RowsJ9AL
  g : ℕ
  hN : ℕ
  ω : ZMod P

def Datum9AL.toA (d : Datum9AL) : Datum9A := ⟨d.Pb.toPubJ9A, d.Rg, d.c, d.r.toRowsJ9A, d.g, d.hN, d.ω⟩

def HdomOf9L (d : Datum9AL) : Finset (ZMod P) := HdomOf9 d.toA

/-- the row set of each of the nine tables (0..7 as `HtOf9`, 8 = the ALU's) -/
def HtOf9L (d : Datum9AL) : Fin 9 → Finset (ZMod P)
  | 0 => HtOf9 d.toA 0
  | 1 => HtOf9 d.toA 1
  | 2 => HtOf9 d.toA 2
  | 3 => HtOf9 d.toA 3
  | 4 => HtOf9 d.toA 4
  | 5 => HtOf9 d.toA 5
  | 6 => HtOf9 d.toA 6
  | 7 => HtOf9 d.toA 7
  | 8 => rowNodeSet d.Pb.nodesL

/-- `DatumOK9A`'s fields at `d.Pb` / `d.r`, with `hreg9` replaced by `hreg9P`, and `hAL`, `hpreLdeg` added -/
structure DatumOK9AL (d : Datum9AL) : Prop where
  hRg : d.Rg.Faithful
  hcK : Fintype.card KC = VclL.Events.cK
  hr : RowsLe d.r.toRowsJ8 EncInjJ8.cornerC
  hAX : d.r.AX ≤ 2 ^ 31
  hSP : d.r.SP ≤ 2 ^ 31
  hAL : d.r.AL ≤ 2 ^ 31
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
  /-- NOTE `+ 6` (SIG Part 3.4); the census now includes the primitive nouns -/
  hreg9P : (censusG d.Pb.toPubJ8 d.c ++ censusP d.Pb).length + 6 ≤ 2 ^ 31
  /-- the ALU's `preg` columns have degree below the union domain's size -/
  hpreLdeg : ∀ k, (d.Pb.preL k).natDegree ≤ d.hN
  hHt : ∀ t : Fin 9, HtOf9L d t ⊆ HdomOf9L d
  hcapH : d.hN ≤ 2 ^ 26

/-! ## 3. the message -/

abbrev Msg9L : Type := MsgJ9AL' P KC deltaF × (Fin 33 → ZMod P)

def Msg9L.toA (M : Msg9L) : Msg9 := (M.1.toMsgJ9A', M.2)

/-- finite codes: `Mcode9` and the ALU's six publics (`pubALv, +1, pubALs, +1, pubALx, +1`) -/
abbrev Mcode9L : Type := Mcode9 × (Fin 6 → KC)

def decM9L (m : Mcode9L) : Msg9L := (⟨(decM9 m.1).1, ext0 m.2⟩, (decM9 m.1).2)

/-! ## 4. the chips -/

def chipL (d : Datum9AL) (χ : Coins Φ0 KC) (M : Msg9L) :=
  AluSZChipJ9.aluSZChipJ9 deltaF powerBasis3 d.Pb.hnL d.Pb.nodesL d.Pb.orbitL
    (AluSZChipJ9.chalsALJ8 deltaF χ) M.1.pubsL d.Pb.preL

/-- the number of constraints of each table (independent of the coins and the message) -/
def sz9L (d : Datum9AL) : Fin 9 → ℕ
  | 0 => sz9 d.toA 0
  | 1 => sz9 d.toA 1
  | 2 => sz9 d.toA 2
  | 3 => sz9 d.toA 3
  | 4 => sz9 d.toA 4
  | 5 => sz9 d.toA 5
  | 6 => sz9 d.toA 6
  | 7 => sz9 d.toA 7
  | 8 => (AluSZChipJ9.aluSZChipJ9 deltaF powerBasis3 d.Pb.hnL d.Pb.nodesL d.Pb.orbitL
      (fun _ => 0) (fun _ => 0) d.Pb.preL).rap.s

theorem truncP_rename {w : ℕ} {ι ι' : Type} (f : ι → ι') (e : Fin w → ι) (q : MvPolynomial (Fin w × ℕ) (ZMod P)) :
    MvPolynomial.rename (Prod.map f id) (truncP e q) = truncP (f ∘ e) q := by
  unfold truncP
  rw [MvPolynomial.rename_bind₁]
  refine congrArg (fun g => MvPolynomial.bind₁ g q) ?_
  funext s
  by_cases h : s.2 < 2 <;> simp [h, MvPolynomial.rename_X]

/-- the constraint `l` of table `t`, truncated into the interface variables -/
def consT9L (d : Datum9AL) (χ : Coins Φ0 KC) (M : Msg9L) :
    (t : Fin 9) → Fin (sz9L d t) → MvPolynomial (Ι9L × Fin 2) (ZMod P)
  | 0, l => MvPolynomial.rename (Prod.map Sum.inl id) (consT9 d.toA χ M.toA 0 l)
  | 1, l => MvPolynomial.rename (Prod.map Sum.inl id) (consT9 d.toA χ M.toA 1 l)
  | 2, l => MvPolynomial.rename (Prod.map Sum.inl id) (consT9 d.toA χ M.toA 2 l)
  | 3, l => MvPolynomial.rename (Prod.map Sum.inl id) (consT9 d.toA χ M.toA 3 l)
  | 4, l => MvPolynomial.rename (Prod.map Sum.inl id) (consT9 d.toA χ M.toA 4 l)
  | 5, l => MvPolynomial.rename (Prod.map Sum.inl id) (consT9 d.toA χ M.toA 5 l)
  | 6, l => MvPolynomial.rename (Prod.map Sum.inl id) (consT9 d.toA χ M.toA 6 l)
  | 7, l => MvPolynomial.rename (Prod.map Sum.inl id) (consT9 d.toA χ M.toA 7 l)
  | 8, l => truncP (fun j => iL (Fin.cast (AluSZChipJ9.aluSZ_width_eq deltaF powerBasis3 d.Pb.hnL d.Pb.nodesL
      d.Pb.orbitL (AluSZChipJ9.chalsALJ8 deltaF χ) M.1.pubsL d.Pb.preL) j)) ((chipL d χ M).rap.C l)

theorem consT9L_deg (d : Datum9AL) (χ : Coins Φ0 KC) (M : Msg9L) (t : Fin 9) (l : Fin (sz9L d t)) :
    (consT9L d χ M t l).totalDegree ≤ 4 := by
  match t, l with
  | 0, l => exact (MvPolynomial.totalDegree_rename_le _ _).trans (consT9_deg d.toA χ M.toA 0 l)
  | 1, l => exact (MvPolynomial.totalDegree_rename_le _ _).trans (consT9_deg d.toA χ M.toA 1 l)
  | 2, l => exact (MvPolynomial.totalDegree_rename_le _ _).trans (consT9_deg d.toA χ M.toA 2 l)
  | 3, l => exact (MvPolynomial.totalDegree_rename_le _ _).trans (consT9_deg d.toA χ M.toA 3 l)
  | 4, l => exact (MvPolynomial.totalDegree_rename_le _ _).trans (consT9_deg d.toA χ M.toA 4 l)
  | 5, l => exact (MvPolynomial.totalDegree_rename_le _ _).trans (consT9_deg d.toA χ M.toA 5 l)
  | 6, l => exact (MvPolynomial.totalDegree_rename_le _ _).trans (consT9_deg d.toA χ M.toA 6 l)
  | 7, l => exact (MvPolynomial.totalDegree_rename_le _ _).trans (consT9_deg d.toA χ M.toA 7 l)
  | 8, l => exact (truncP_deg _ _).trans ((chipL d χ M).rap.C_deg l)

/-- the row shift of each table -/
def omegaOf9L (d : Datum9AL) : Fin 9 → ZMod P
  | 0 => omegaOf9 d.toA 0
  | 1 => omegaOf9 d.toA 1
  | 2 => omegaOf9 d.toA 2
  | 3 => omegaOf9 d.toA 3
  | 4 => omegaOf9 d.toA 4
  | 5 => omegaOf9 d.toA 5
  | 6 => omegaOf9 d.toA 6
  | 7 => omegaOf9 d.toA 7
  | 8 => d.Pb.orbitL.ω

def tabΙ9L : Ι9L → Fin 9 := Sum.elim (fun j => Fin.castSucc (tabΙ9 j)) (fun _ => 8)

/-- the fixed columns (zero coins: the preprocessing does not read them) -/
def preJ9L (d : Datum9AL) : Ι9L → Option (ZMod P)[X] :=
  Sum.elim (preJ9 d.toA) (fun c => NockvmE2E.J8.InstJ8.preOf (AluSZChipJ9.aluSZChipJ9 deltaF powerBasis3 d.Pb.hnL d.Pb.nodesL d.Pb.orbitL
      (fun _ => 0) (fun _ => 0) d.Pb.preL)
    (Fin.cast (AluSZChipJ9.aluSZ_width_eq deltaF powerBasis3 d.Pb.hnL d.Pb.nodesL d.Pb.orbitL
      (fun _ => 0) (fun _ => 0) d.Pb.preL).symm c))

/-! ## 4b. the message read off the verifier's publics -/

/-- **the J-9 AL message read off the verifier's publics**: J-9 A's `Mof9` and the ALU slice (table 8) -/
noncomputable def Mof9L (L : NockvmE2E.Exec.PE.PubLayout) (pub : Array UInt64) : Msg9L :=
  (⟨(NockvmE2E.J9A.RVUJ9A.Mof9 L pub).1, NockvmE2E.Exec.SP.pubK (NockvmE2E.Exec.SP.slOf L pub 8)⟩, (NockvmE2E.J9A.RVUJ9A.Mof9 L pub).2)

/-! ## 5. `Pub`, `StmtOK`, the present tables -/

def PubEq9AL (d : Datum9AL) (χ : Coins Φ0 KC) (M : Msg9L) : Prop :=
  (M.1.ρ 3 + (Quad.mk _ (M.1.pubsW WalkHQ.pubXQ) (M.1.pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (M.1.pubsJ 2) (M.1.pubsJ 3) +
      Quad.mk _ (M.1.pubsL AluSZChipJ9.pubALx) (M.1.pubsL (AluSZChipJ9.pubALx + 1))) =
    Quad.mk _ (M.1.pubsC CellHQ.pubHQ) (M.1.pubsC (CellHQ.pubHQ + 1))) ∧
  (M.1.ρ 4 + Quad.mk _ (M.1.pubsX AxisChipJ9.pubAXp) (M.1.pubsX (AxisChipJ9.pubAXp + 1)) =
    Quad.mk _ (M.1.pubsW WalkHQ.pubPQ) (M.1.pubsW (WalkHQ.pubPQ + 1))) ∧
  (M.1.ρS + ((pinCons (p := P) (K := KC) d.Pb.regs d.Pb.idx).map fun r =>
      (compress (coinsCV powerBasis3 deltaF (chalVJ8 powerBasis3 χ)) (liftRec (L := KQ') r))⁻¹).sum +
      ((AcceptsJ9AL.pinRgP (p := P) (K := KC) d.Pb).map fun r =>
        (compress (coinsCV powerBasis3 deltaF (chalVJ8 powerBasis3 χ)) (liftRec (L := KQ') r))⁻¹).sum +
      ((AcceptsJ9AL.pinOpP (p := P) (K := KC) d.Pb).map fun r =>
        (compress (coinsCV powerBasis3 deltaF (chalVJ8 powerBasis3 χ)) (liftRec (L := KQ') r))⁻¹).sum +
      Quad.mk _ (M.1.pubsJ 0) (M.1.pubsJ 1) +
      Quad.mk _ (M.1.pubsX AxisChipJ9.pubAXs) (M.1.pubsX (AxisChipJ9.pubAXs + 1)) +
      Quad.mk _ (M.1.pubsL AluSZChipJ9.pubALs) (M.1.pubsL (AluSZChipJ9.pubALs + 1)) =
    Quad.mk _ (M.1.pubsA AtomChipHQ.pubMI) (M.1.pubsA (AtomChipHQ.pubMI + 1)) +
      Quad.mk _ (M.1.pubsV WalkHQ.pubPQ) (M.1.pubsV (WalkHQ.pubPQ + 1)) +
      Quad.mk _ (M.1.pubsS SplitChipJ9.pubSPs) (M.1.pubsS (SplitChipJ9.pubSPs + 1))) ∧
  (Quad.mk (algebraMap (ZMod P) KC deltaF) (M.1.pubsL AluSZChipJ9.pubALv) (M.1.pubsL (AluSZChipJ9.pubALv + 1)) +
    ((claimRecsJ9 deltaF χ d.c M.1.m ++ pinRecsJ8 deltaF d.Pb.toPubJ8 χ ++ AcceptsJ9AL.pinRecsP deltaF d.Pb χ).map
      fun r => (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
    Quad.mk (algebraMap (ZMod P) KC deltaF) (M.1.pubsC 0) (M.1.pubsC 1) +
      Quad.mk (algebraMap (ZMod P) KC deltaF) (M.1.pubsA AtomChipHQ.pubMB) (M.1.pubsA (AtomChipHQ.pubMB + 1))) ∧
  (Quad.mk (algebraMap (ZMod P) KC deltaF) (M.1.pubsA CellHQ.pubHQ) (M.1.pubsA (CellHQ.pubHQ + 1)) =
    Quad.mk (algebraMap (ZMod P) KC deltaF) (M.1.pubsA AtomChipHQ.pubC) (M.1.pubsA (AtomChipHQ.pubC + 1)) +
      Quad.mk (algebraMap (ZMod P) KC deltaF) (M.1.pubsV WalkHQ.pubXQ) (M.1.pubsV (WalkHQ.pubXQ + 1))) ∧
  (M.1.pubsA 0 = 0 ∧ M.1.pubsA 1 = 0) ∧
  (M.1.pubsC 2 = M.1.pubsW 0 ∧ M.1.pubsC 3 = M.1.pubsW 1) ∧
  (M.1.pubsA 2 = M.1.pubsV 0 ∧ M.1.pubsA 3 = M.1.pubsV 1)

def PubP9AL (d : Datum9AL) (χ : Coins Φ0 KC) (M : Msg9L) : Prop :=
  PubEq9AL d χ M ∧
  (∀ k : Fin 3, (isCellN (claimNoun d.c k) = true ∨ isBigN P (claimNoun d.c k) = true) → (M.1.m k).1 < P) ∧
  ((d.Pb.krootsV = 0 → M.1.pubsV 0 = 0 ∧ M.1.pubsV 1 = 0 ∧ M.1.pubsV WalkHQ.pubXQ = 0 ∧ M.1.pubsV (WalkHQ.pubXQ + 1) = 0 ∧
      M.1.pubsV WalkHQ.pubPQ = 0 ∧ M.1.pubsV (WalkHQ.pubPQ + 1) = 0) ∧
    (d.Pb.nJ = 0 → M.1.pubsJ 0 = 0 ∧ M.1.pubsJ 1 = 0 ∧ M.1.pubsJ 2 = 0 ∧ M.1.pubsJ 3 = 0) ∧
    (d.Pb.axOn = false → M.1.pubsX AxisChipJ9.pubAXs = 0 ∧ M.1.pubsX (AxisChipJ9.pubAXs + 1) = 0 ∧
      M.1.pubsX AxisChipJ9.pubAXp = 0 ∧ M.1.pubsX (AxisChipJ9.pubAXp + 1) = 0) ∧
    (d.Pb.spOn = false → M.1.pubsS SplitChipJ9.pubSPs = 0 ∧ M.1.pubsS (SplitChipJ9.pubSPs + 1) = 0) ∧
    (d.Pb.aluOn = false → M.1.pubsL AluSZChipJ9.pubALv = 0 ∧ M.1.pubsL (AluSZChipJ9.pubALv + 1) = 0 ∧
      M.1.pubsL AluSZChipJ9.pubALs = 0 ∧ M.1.pubsL (AluSZChipJ9.pubALs + 1) = 0 ∧
      M.1.pubsL AluSZChipJ9.pubALx = 0 ∧ M.1.pubsL (AluSZChipJ9.pubALx + 1) = 0)) ∧
  (∀ j : Fin 33, M.2 j = pubVJ9 deltaF powerBasis3 d.c M.1.m M.1.ρ M.1.ρS χ j)

/-- the static conjuncts of `AcceptsJ9AL` -/
structure StmtP9AL (d : Datum9AL) : Prop where
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
  hcen' : ∀ x ∈ censusGJ9 d.Pb.toPubJ8 d.c ++ AcceptsJ9AL.censusP d.Pb, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, lenL v ≤ d.Pb.nA + 2
  hlenC : 3 + d.Pb.regs.length + 2 * d.Pb.nC < P
  hlenA : d.Pb.nA + d.Pb.nV < P
  hcellF : isCellN d.c.formula = true
  /-- replaces `hnA62` -/
  hnAS : d.Pb.nA + d.Pb.nS < 2 ^ 57
  hbud : BudJ9AL d.Pb d.r (d.g + d.r.N)
  hbudV : d.Pb.regs.length ≤ d.g ∧ d.Pb.nA ≤ d.r.mb ∧ d.Pb.nA ≤ d.r.A ∧ d.Pb.nV ≤ d.r.AW ∧
    d.Pb.nX ≤ d.r.AX ∧ d.Pb.nS ≤ d.r.SP
  hlenX : d.Pb.nX + d.Pb.n < P ∧ 2 * d.Pb.nS < P
  hALst : d.Pb.aluOn = true → Function.Injective d.Pb.nodesL ∧
    (∀ (i : Fin d.Pb.nL) (hi : (i : ℕ) + 1 < d.Pb.nL), d.Pb.nodesL ⟨(i : ℕ) + 1, hi⟩ = d.Pb.nodesL i * d.Pb.orbitL.ω) ∧
    d.Pb.nL < P ∧ AcceptsJ9AL.PregOK d.Pb.nodesL d.Pb.prims d.Pb.preL
  hALabs : d.Pb.aluOn = false → d.Pb.prims = []
  hPrim : ∀ q ∈ d.Pb.prims, d.Rg q.1 = some (Nock.Jet.Prim.primSpec q.2)
  hdisjP : ∀ q ∈ d.Pb.prims, q.1 ∉ d.Pb.regs
  hlenL : d.Pb.nL + d.Pb.n < P ∧ d.Pb.nL ≤ d.r.AL ∧ ∀ q ∈ d.Pb.prims, q.1 < P ∧ d.Pb.idxP q.1 < P
  hndP : (d.Pb.prims.map Prod.fst).Nodup
  hrkP : ∀ q ∈ d.Pb.prims, d.Pb.rkP q.1 ≠ (0, 0)
  hltP : ∀ q ∈ d.Pb.prims, (d.Pb.rkP q.1).1 < ringChar (ZMod P) ∧ (d.Pb.rkP q.1).2 < ringChar (ZMod P) ∧
    d.Pb.idxP q.1 < ringChar (ZMod P)
  hlenCP : 3 + d.Pb.regs.length + d.Pb.prims.length + d.Pb.nL + 2 * d.Pb.nC < P

/-- the tables present: the nine, with the ALU absent iff `aluOn = false` -/
def present9L (d : Datum9AL) (t : Fin 9) : Prop :=
  (∀ h : (t : ℕ) < 8, present9A d.toA ⟨t, h⟩) ∧ ¬(t = 8 ∧ d.Pb.aluOn = false)

def AccJ9AL (d : Datum9AL) : Coins Φ0 KC → MsgJ9AL' P KC deltaF → TrJ9AL (ZMod P) → Prop :=
  fun χ M tr => AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 d.Pb d.Rg d.c χ M tr d.r d.g

theorem omegaOf9L_castSucc (d : Datum9AL) (t : Fin 8) : omegaOf9L d t.castSucc = omegaOf9 d.toA t := by
  fin_cases t <;> rfl

theorem sz9L_castSucc (d : Datum9AL) (t : Fin 8) : sz9L d t.castSucc = sz9 d.toA t := by
  fin_cases t <;> rfl

theorem HtOf9L_castSucc (d : Datum9AL) (t : Fin 8) : HtOf9L d t.castSucc = HtOf9 d.toA t := by
  fin_cases t <;> rfl

theorem present9L_castSucc (d : Datum9AL) (t : Fin 8) : present9L d t.castSucc ↔ present9A d.toA t := by
  constructor
  · intro h
    exact h.1 (by simp) 
  · intro h
    refine ⟨fun hh => ?_, fun hh => ?_⟩
    · exact h
    · have := hh.1
      have h8 : (Fin.castSucc t : Fin 9).val = 8 := by rw [this]; rfl
      have : t.val < 8 := t.isLt
      simp at h8; omega

theorem consT9L_old (d : Datum9AL) (χ : Coins Φ0 KC) (M : Msg9L) (t : Fin 8) (l : Fin (sz9 d.toA t)) :
    consT9L d χ M t.castSucc (Fin.cast (sz9L_castSucc d t).symm l) =
      MvPolynomial.rename (Prod.map Sum.inl id) (consT9 d.toA χ M.toA t l) := by
  fin_cases t <;> rfl

/-- the old eight tables' constraint hypothesis, read at the `Ι9` view of the trace -/
theorem hvOld (d : Datum9AL) (χ : Coins Φ0 KC) (M : Msg9L) (tr : Ι9L → (ZMod P)[X])
    (hv : ∀ t : Fin 9, present9L d t → ∀ l : Fin (sz9L d t), ∀ x ∈ HtOf9L d t, (MvPolynomial.aeval
      (fun q : Ι9L × Fin 2 => (tr q.1).comp (Polynomial.C (omegaOf9L d (tabΙ9L q.1) ^ (q.2 : ℕ)) * Polynomial.X))
      (consT9L d χ M t l)).eval x = 0) :
    ∀ t : Fin 8, present9A d.toA t → ∀ l : Fin (sz9 d.toA t), ∀ x ∈ HtOf9 d.toA t, (MvPolynomial.aeval
      (fun q : Ι9 × Fin 2 => ((tr ∘ Sum.inl) q.1).comp (Polynomial.C (omegaOf9 d.toA (tabΙ9 q.1) ^ (q.2 : ℕ)) * Polynomial.X))
      (consT9 d.toA χ M.toA t l)).eval x = 0 := by
  intro t hp l x hx
  have h := hv t.castSucc ((present9L_castSucc d t).2 hp) (Fin.cast (sz9L_castSucc d t).symm l) x
    (by rw [HtOf9L_castSucc]; exact hx)
  rw [consT9L_old, MvPolynomial.aeval_rename] at h
  have hfun : ((fun q : Ι9L × Fin 2 => (tr q.1).comp (Polynomial.C (omegaOf9L d (tabΙ9L q.1) ^ (q.2 : ℕ)) * Polynomial.X)) ∘
      Prod.map Sum.inl id) =
      (fun q : Ι9 × Fin 2 => ((tr ∘ Sum.inl) q.1).comp (Polynomial.C (omegaOf9 d.toA (tabΙ9 q.1) ^ (q.2 : ℕ)) * Polynomial.X)) := by
    funext q
    simp only [Function.comp, Prod.map_fst, Prod.map_snd, id, tabΙ9L, Sum.elim_inl, omegaOf9L_castSucc]
  rw [hfun] at h
  exact h

theorem accGen9L (d : Datum9AL) (hd : DatumOK9AL d) (χ : Coins Φ0 KC) (M : Msg9L) (tr : Ι9L → (ZMod P)[X])
    (hv : ∀ t : Fin 9, present9L d t → ∀ l : Fin (sz9L d t), ∀ x ∈ HtOf9L d t, (MvPolynomial.aeval
      (fun q : Ι9L × Fin 2 => (tr q.1).comp (Polynomial.C (omegaOf9L d (tabΙ9L q.1) ^ (q.2 : ℕ)) * Polynomial.X))
      (consT9L d χ M t l)).eval x = 0)
    (hp : PubP9AL d χ M) (hs : StmtP9AL d)
    (hpre : ∀ j c, present9L d (tabΙ9L j) → preJ9L d j = some c → tr j = c) :
    AccJ9AL d χ M.1 (unflat9L tr) := by
  obtain ⟨hPE, hclI, ⟨habsV, habsJ, habsX, habsS, habsL⟩, hder⟩ := hp
  obtain ⟨hGx, hGp, hGS, hsumC', hbalA', hvalA0, hfxC, hfxA⟩ := hPE
  have hv' := hvOld d χ M tr hv
  have hpre' : ∀ j c, present9A d.toA (tabΙ9 j) → preJ9 d.toA j = some c → (tr ∘ Sum.inl) j = c :=
    fun j c h hj => hpre (Sum.inl j) c ((present9L_castSucc d (tabΙ9 j)).2 h) hj
  set trI : Ι9 → (ZMod P)[X] := tr ∘ Sum.inl with hTI
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
  have hp0 : present9A d.toA 0 := by unfold present9A; simp
  have hp1 : present9A d.toA 1 := by unfold present9A; simp
  have hp2 : present9A d.toA 2 := by unfold present9A; simp
  have hp4 : present9A d.toA 4 := by unfold present9A; simp
  have cX : ∀ pv, xpF M.2 = pv → RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX9 d.Pb.hn d.Pb.nodes powerBasis3 deltaF (chalVJ8 powerBasis3 χ) pv d.Pb.orbit)
      (fun j => trI (iC (Fin.cast (computeChipVCLHX9_width d.Pb.hn d.Pb.nodes powerBasis3 deltaF
        (chalVJ8 powerBasis3 χ) pv d.Pb.orbit) j))) := by
    intro pv hpv
    subst hpv
    exact chip_ok (chipC d.toA χ M.toA) _ trI (fun q => omegaOf9 d.toA (tabΙ9 q)) (fun j => rfl) (hI_expand) (preJ9 d.toA)
      (fun c q hj => hpre' _ q hp0 hj) (fun c => rfl) (fun i x hx => hv' 0 hp0 i x hx)
  have cM := chip_ok (chipM d.toA χ M.toA) (fun j => iM (Fin.cast (CellTwinKW.cellChipHQKW_width deltaF powerBasis3
      d.Pb.hnC d.Pb.nodesC d.Pb.orbitC (chalsMJ8 deltaF χ) M.1.pubsC) j)) trI (fun q => omegaOf9 d.toA (tabΙ9 q))
      (fun j => rfl) (hI_expand) (preJ9 d.toA) (fun c q hj => hpre' _ q hp1 hj) (fun c => rfl) (fun i x hx => hv' 1 hp1 i x hx)
  have cW := chip_ok (chipW d.toA χ M.toA) (fun j => iW (Fin.cast (WalkJ8.walkChipJ8_width deltaF d.Pb.kroots
      powerBasis3 d.Pb.hnW d.Pb.nodesW d.Pb.orbitW (chalsMJ8 deltaF χ) M.1.pubsW) j)) trI (fun q => omegaOf9 d.toA (tabΙ9 q))
      (fun j => rfl) (hI_expand) (preJ9 d.toA) (fun c q hj => hpre' _ q hp2 hj) (fun c => rfl) (fun i x hx => hv' 2 hp2 i x hx)
  have cA := chip_ok (chipA d.toA χ M.toA) (fun j => iA (Fin.cast
      (AtomChipHQL.atomChipHQL_width deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA) j))
      trI (fun q => omegaOf9 d.toA (tabΙ9 q))
      (fun j => rfl) (hI_expand) (preJ9 d.toA) (fun c q hj => hpre' _ q hp4 hj) (fun c => rfl) (fun i x hx => hv' 4 hp4 i x hx)
  have hJk : JGenJ8.JChipOK deltaF powerBasis3 d.Pb.nodesJ d.Pb.orbitJ (chalsJJ8 χ) M.1.pubsJ d.Pb.lay
      (AcceptsJ8.qJ deltaF powerBasis3 d.Pb.toPubJ8 (unflat9 trI).toJ8 (chalsJJ8 χ) M.1.pubsJ) := by
    by_cases h0 : d.Pb.nJ = 0
    · obtain ⟨a, b, c, e⟩ := habsJ h0
      exact Or.inr ⟨h0, a, b, c, e⟩
    · have hp3 : present9A d.toA 3 := by unfold present9A; simp [Datum9AL.toA, h0]
      have cJ := chip_ok (chipJ d.toA χ M.toA) (fun j => iJ (Fin.cast
        (Nock.Jet.ChipJ8.jetChipJ8_width deltaF powerBasis3 d.Pb.nodesJ d.Pb.orbitJ (chalsJJ8 χ) M.1.pubsJ d.Pb.lay) j))
        trI (fun q => omegaOf9 d.toA (tabΙ9 q)) (fun j => rfl) (hI_expand) (preJ9 d.toA) (fun c q hj => hpre' _ q hp3 hj) (fun c => rfl)
        (fun i x hx => hv' 3 hp3 i x hx)
      obtain ⟨hinj, hadj⟩ := hs.hJst h0
      exact Or.inl ⟨cJ.1, cJ.2, hinj, Nat.pos_of_ne_zero h0, hadj⟩
  have hVk : AcceptsJ8V.AWChipOK deltaF powerBasis3 d.Pb.krootsV d.Pb.hnV d.Pb.nodesV d.Pb.orbitV (chalsAJ8Z deltaF χ)
      M.1.pubsV (AcceptsJ8.qV deltaF powerBasis3 d.Pb.toPubJ8 (unflat9 trI).toJ8 (chalsAJ8Z deltaF χ) M.1.pubsV) := by
    by_cases h0 : d.Pb.krootsV = 0
    · obtain ⟨a, b, c, e, f, g⟩ := habsV h0
      exact Or.inr ⟨h0, a, b, c, e, f, g⟩
    · have hp5 : present9A d.toA 5 := by unfold present9A; simp [Datum9AL.toA, h0]
      have cV := chip_ok (chipV d.toA χ M.toA) (fun j => iV (Fin.cast
        (CellTwinK.walkChipHQK_width deltaF d.Pb.krootsV powerBasis3 d.Pb.hnV d.Pb.nodesV d.Pb.orbitV (chalsAJ8Z deltaF χ)
          M.1.pubsV) j))
        trI (fun q => omegaOf9 d.toA (tabΙ9 q)) (fun j => rfl) (hI_expand) (preJ9 d.toA) (fun c q hj => hpre' _ q hp5 hj) (fun c => rfl)
        (fun i x hx => hv' 5 hp5 i x hx)
      obtain ⟨hinj, hadj, h1, h2, h3⟩ := hs.hVst h0
      exact Or.inl ⟨cV.1, cV.2, hinj, hadj, h1, h2, h3⟩
  have hAXk : AcceptsJ9A.AXChipOK deltaF powerBasis3 d.Pb.axOn d.Pb.hnX d.Pb.nodesX d.Pb.orbitX (chalsMJ8 deltaF χ)
      M.1.pubsX (qAX deltaF powerBasis3 d.Pb.toPubJ9A (unflat9 trI) (chalsMJ8 deltaF χ) M.1.pubsX) := by
    by_cases h0 : d.Pb.axOn = false
    · obtain ⟨a, b, c, e⟩ := habsX h0
      exact Or.inr ⟨h0, a, b, c, e⟩
    · have h1 : d.Pb.axOn = true := by simpa using h0
      have hp6 : present9A d.toA 6 := by unfold present9A; simp [Datum9AL.toA, h1]
      have cX' := chip_ok (chipX d.toA χ M.toA) (fun j => iX (Fin.cast
        (AxisChipJ9.width_eq deltaF powerBasis3 d.Pb.hnX d.Pb.nodesX d.Pb.orbitX (chalsMJ8 deltaF χ) M.1.pubsX) j))
        trI (fun q => omegaOf9 d.toA (tabΙ9 q)) (fun j => rfl) (hI_expand) (preJ9 d.toA) (fun c q hj => hpre' _ q hp6 hj) (fun c => rfl)
        (fun i x hx => hv' 6 hp6 i x hx)
      obtain ⟨hinj, hadj, hlt⟩ := hs.hXst h1
      exact Or.inl ⟨h1, cX'.1, cX'.2, hinj, hadj, hlt⟩
  have hSPk : AcceptsJ9A.SPChipOK deltaF powerBasis3 d.Pb.nA d.Pb.spOn d.Pb.hnS d.Pb.nodesS d.Pb.orbitS (chalsMJ8 deltaF χ)
      M.1.pubsS (qSP deltaF powerBasis3 d.Pb.toPubJ9A (unflat9 trI) (chalsMJ8 deltaF χ) M.1.pubsS) := by
    by_cases h0 : d.Pb.spOn = false
    · obtain ⟨a, b⟩ := habsS h0
      exact Or.inr ⟨h0, a, b⟩
    · have h1 : d.Pb.spOn = true := by simpa using h0
      have hp7 : present9A d.toA 7 := by unfold present9A; simp [Datum9AL.toA, h1]
      have cS' := chip_ok (chipS d.toA χ M.toA) (fun j => iS (Fin.cast
        (SplitChipJ9.width_eq deltaF d.Pb.nA powerBasis3 d.Pb.hnS d.Pb.nodesS d.Pb.orbitS (chalsMJ8 deltaF χ) M.1.pubsS) j))
        trI (fun q => omegaOf9 d.toA (tabΙ9 q)) (fun j => rfl) (hI_expand) (preJ9 d.toA) (fun c q hj => hpre' _ q hp7 hj) (fun c => rfl)
        (fun i x hx => hv' 7 hp7 i x hx)
      obtain ⟨hinj, hadj, hlt⟩ := hs.hSst h1
      exact Or.inl ⟨h1, cS'.1, cS'.2, hinj, hadj, hlt⟩
  have hL : (atomChipHQL deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA).rap.Satisfies
      (AcceptsJ8L.qAL deltaF powerBasis3 d.Pb.toPubJ8 (unflat9 trI).toJ8 (chalsAJ8Z deltaF χ) M.1.pubsA) := cA.1
  have hLb : (atomChipHQL deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA).BindsPreprocessing
      (AcceptsJ8L.qAL deltaF powerBasis3 d.Pb.toPubJ8 (unflat9 trI).toJ8 (chalsAJ8Z deltaF χ) M.1.pubsA) := cA.2
  have hA1 := AtomChipHQL.atomChipHQL_sat deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA _ hL
  have hA2 := AtomChipHQL.atomChipHQL_bind deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA _ hLb
  rw [AcceptsJ8L.qAL_toHQ] at hA1 hA2
  have hALk : AcceptsJ9AL.ALChipOK deltaF powerBasis3 d.Pb.aluOn d.Pb.prims d.Pb.hnL d.Pb.nodesL d.Pb.orbitL d.Pb.preL
      (AluSZChipJ9.chalsALJ8 deltaF χ) M.1.pubsL
      (RealIOJ9AL.qAL deltaF powerBasis3 d.Pb (unflat9L tr) (AluSZChipJ9.chalsALJ8 deltaF χ) M.1.pubsL) := by
    by_cases h0 : d.Pb.aluOn = false
    · obtain ⟨a, b, c, e, f, g⟩ := habsL h0
      exact Or.inr ⟨h0, hs.hALabs h0, a, b, c, e, f, g⟩
    · have h1 : d.Pb.aluOn = true := by simpa using h0
      have hp8 : present9L d 8 := ⟨fun h => absurd h (by decide), fun h => h0 h.2⟩
      have cL := chip_ok (chipL d χ M) (fun j => iL (Fin.cast (AluSZChipJ9.aluSZ_width_eq deltaF powerBasis3 d.Pb.hnL
        d.Pb.nodesL d.Pb.orbitL (AluSZChipJ9.chalsALJ8 deltaF χ) M.1.pubsL d.Pb.preL) j))
        tr (fun q => omegaOf9L d (tabΙ9L q)) (fun j => rfl) (hI_expand) (preJ9L d) (fun c q hj => hpre _ q hp8 hj)
        (fun c => rfl) (fun i x hx => hv 8 hp8 i x hx)
      obtain ⟨hinj, hadj, hlt, hpr⟩ := hs.hALst h1
      exact Or.inl ⟨h1, cL.1, cL.2, hinj, hadj, hlt, hpr⟩
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
      hlenX := hs.hlenX
      hALk := hALk
      hPrim := hs.hPrim
      hdisjP := hs.hdisjP
      hlenL := hs.hlenL
      hndP := hs.hndP
      hrkP := hs.hrkP
      hltP := hs.hltP
      hlenCP := hs.hlenCP }

/-! ## 6. caps -/

def ns9L (d : Datum9AL) : ℕ := ∑ t : Fin 9, sz9L d t

theorem sz9L_alu_le {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod P) (orbit : StrictOrbitDomain (ZMod P) 3 h)
    (chals pubs : ℕ → KC) (pre : Fin 3 → (ZMod P)[X]) :
    (AluSZChipJ9.aluSZChipJ9 deltaF powerBasis3 hn nodes orbit chals pubs pre).rap.s ≤ 5000 := by
  rw [show (AluSZChipJ9.aluSZChipJ9 deltaF powerBasis3 hn nodes orbit chals pubs pre).rap =
    expandChip (AluSZChipJ9.aluTemplateSZ deltaF) powerBasis3 _ _ orbit _ from rfl, expandChip_s]
  simp [AluSZChipJ9.aluTemplateSZ, AluSZChipJ9.baseGates_length, AluSZChipJ9.aluMixed_length]

theorem sz9L_le (d : Datum9AL) (t : Fin 9) : sz9L d t ≤ 5000 := by
  fin_cases t
  · exact sz9_le d.toA 0
  · exact sz9_le d.toA 1
  · exact sz9_le d.toA 2
  · exact sz9_le d.toA 3
  · exact sz9_le d.toA 4
  · exact sz9_le d.toA 5
  · exact sz9_le d.toA 6
  · exact sz9_le d.toA 7
  · exact sz9L_alu_le _ _ _ _ _ _

theorem cap_ns9L (d : Datum9AL) : ns9L d ≤ 2 ^ 20 := by
  unfold ns9L
  calc ∑ t, sz9L d t ≤ ∑ _t : Fin 9, 5000 := Finset.sum_le_sum fun t _ => sz9L_le d t
    _ = 45000 := by simp
    _ ≤ 2 ^ 20 := by norm_num

theorem cap_H9L (d : Datum9AL) (hd : DatumOK9AL d) : (HdomOf9L d).card ≤ 2 ^ 26 :=
  (Finset.card_image_le.trans (by simpa [Datum9AL.toA] using hd.hcapH))

/-! ## 7. `clJ9AL`: the J-9 AL chip layer -/

open Classical in
set_option maxRecDepth 50000 in
/-- **`clJ9AL`**: the J-9 AL chip layer (T := 9) -/
noncomputable def clJ9AL (d : Datum9AL) (hd : DatumOK9AL d) :
    CLay (Tr := TrJ9AL (ZMod P)) StJ9AL (MsgJ9AL' P KC deltaF) (AccJ9AL d) where
  ι0 := Ι9L
  fι := inferInstance
  dι := inferInstance
  colR := colR9L
  hround := colR9L_le
  unflat := unflat9L
  stUnflat := stJ9AL_unflat
  pre := preJ9L d
  Msg := Msg9L
  Mcode := Mcode9L
  fM := inferInstance
  dM := inferInstance
  dec := decM9L
  msg0 := Prod.fst
  T := 9
  Ht := HtOf9L d
  H := HdomOf9L d
  hHt := hd.hHt
  ωt := omegaOf9L d
  tabC := tabΙ9L
  sz := sz9L d
  consT := consT9L d
  hdeg χ M t l := consT9L_deg d χ M t l
  Pub := PubP9AL d
  StmtOK := StmtP9AL d
  present := present9L d
  accOn χ M tr hv hp hs hpre := accGen9L d hd χ M tr hv hp hs hpre
  cap_ns := cap_ns9L d
  cap_m := by
    show Fintype.card Ι9L * 2 + 3 * (4 - 1) ≤ 2 ^ 12
    rw [card_Ι9L]; norm_num
  cap_H := cap_H9L d hd

/-! ## 8. non-vacuity receipt -/

/-- **`StmtP9AL` and `PubP9AL` are implied by nock's `AcceptsJ9AL`** (compute publics `xp := pubVJ9`): accept ⇒ Stmt ∧ Pub. -/
theorem stmt_pub_of_acc9L (d : Datum9AL) (χ : Coins Φ0 KC) (M : MsgJ9AL' P KC deltaF) (tr : TrJ9AL (ZMod P))
    (h : AccJ9AL d χ M tr) :
    StmtP9AL d ∧ PubP9AL d χ (M, fun j => pubVJ9 deltaF powerBasis3 d.c M.m M.ρ M.ρS χ j) := by
  have hAL := h.hALk
  have hS : StmtP9AL d := by
    refine StmtP9AL.mk
      (hinjX := h.hinjX)
      (hadjX := h.hadjX)
      (hinjC := h.hinjC)
      (hadjC := h.hadjC)
      (hnpC := h.hnpC)
      (hinjW := h.hinjW)
      (hadjW := h.hadjW)
      (hkW := h.hkW)
      (hknW := h.hknW)
      (hkpW := h.hkpW)
      (hJst := ?_)
      (hinjA := h.hinjA)
      (hadjA := h.hadjA)
      (hnpA := h.hnpA)
      (hVst := ?_)
      (hXst := ?_)
      (hSst := ?_)
      (hlay := h.hlay)
      (hsmall := h.hsmall)
      (huniq := h.huniq)
      (hTpl := h.hTpl)
      (hnd := h.hnd)
      (hidx := h.hidx)
      (hrk := h.hrk)
      (hlt := h.hlt)
      (hclR := h.hclR)
      (hcen' := h.hcen')
      (hlenC := h.hlenC)
      (hlenA := h.hlenA)
      (hcellF := h.hcellF)
      (hnAS := h.hnAS)
      (hbud := h.hbud)
      (hbudV := h.hbudV)
      (hlenX := h.hlenX)
      (hALst := ?_)
      (hALabs := ?_)
      (hPrim := h.hPrim)
      (hdisjP := h.hdisjP)
      (hlenL := h.hlenL)
      (hndP := h.hndP)
      (hrkP := h.hrkP)
      (hltP := h.hltP)
      (hlenCP := h.hlenCP)
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
      rcases hAL with ⟨-, -, -, hinj, hadj, hlt, hpr⟩ | ⟨hf, -⟩
      · exact ⟨hinj, hadj, hlt, hpr⟩
      · rw [h0] at hf; exact absurd hf (by simp)
    · intro h0
      rcases hAL with ⟨hf, -⟩ | ⟨-, hp, -⟩
      · rw [h0] at hf; exact absurd hf (by simp)
      · exact hp
  have hP : PubP9AL d χ (M, fun j => pubVJ9 deltaF powerBasis3 d.c M.m M.ρ M.ρS χ j) := by
    refine ⟨⟨h.hGx, h.hGp, h.hGS, h.hsumC', h.hbalA', h.hvalA0, h.hfxC, h.hfxA⟩, h.hclI, ⟨?_, ?_, ?_, ?_, ?_⟩, fun j => rfl⟩
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
    · intro h0
      rcases hAL with ⟨hf, -⟩ | ⟨-, -, a, b, c, e, f, g⟩
      · rw [h0] at hf; exact absurd hf (by simp)
      · exact ⟨a, b, c, e, f, g⟩
  exact ⟨hS, hP⟩

end Inst

#print axioms colR9L_le
#print axioms stJ9AL_unflat
#print axioms card_Ι9L
#print axioms truncP_rename
#print axioms consT9L_deg
#print axioms hvOld
#print axioms accGen9L
#print axioms sz9L_le
#print axioms cap_ns9L
#print axioms clJ9AL
#print axioms stmt_pub_of_acc9L

end NockvmE2E.J9AL.InstJ9AL
