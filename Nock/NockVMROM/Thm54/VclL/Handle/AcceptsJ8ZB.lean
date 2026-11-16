/-
  Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8ZB.lean

  **The handle-balance budgets at `AcceptsJ8Z`.**  New module, additive.
  Verbatim twins (hypothesis `AcceptsJ8Z`; the proofs read `hsatX` only) of `RealIOJ8.compLen / budX_of / budP_of /
  budS_of / hcount_of`: `compLenZ`, **`budX_ofZ`**, **`budP_ofZ`**, **`budS_ofZ`**, **`hcount_ofZ`**.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z
import Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZB

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf compReqsX)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crC crM crW crJ crA staged_eq)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8)
open Nock.Jet.ChipJ8 (jetChipJ8)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.FibreJ8 (effP)

open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8

noncomputable section

section Budgets
open Nock.Jet.ChipJ8 (entsX ents0T ents1T ents2T ents3)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

variable {Rg : Nock.Jet.Registry} {r : RowsJ8} {g : ℕ}

theorem compLenZ (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8Z δ b Pb Rg c χ M tr) (hp : 17 < p) (bl : Bal) :
    (compReqsX (K := K) (hn := Pb.hn) (nodes := Pb.nodes) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
        (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) bl).length ≤ ReadIOJ8.capB bl * Pb.n :=
  ReadIOJ8.compReqsX_length_le hacc.hsatX (by rw [ZMod.ringChar_zmod_n]; exact hp) bl

/-- **`budX`** at `realIO`. -/
theorem budX_ofZ (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8Z δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g) :
    (reqsOf δ b Pb c χ M tr .x).length ≤ 3 * r.N + r.W + r.rd ∧
      (liftP (δ := δ) (provsJ8 δ b Pb χ M tr .x)).length ≤ r.D := by
  refine ⟨?_, ?_⟩
  · rw [reqsOf_length]
    have h1 := compLenZ δ b Pb c χ M tr hacc hp .x
    have h2 : (extJ8 δ b Pb c χ M tr .x).length = Pb.nW + jCount entsX Pb.lay := by
      simp only [extJ8, byBal]
      erw [List.length_append, walkXReqs_length, jRd_length]
    simp only [ReadIOJ8.capB] at h1
    have := hB.x1
    omega
  · simp only [liftP, List.length_map]
    show (cellProvsW b Pb.nodesC Pb.orbitC _ _ _).length ≤ r.D
    simp only [cellProvsW, List.length_map, List.length_finRange]
    exact hB.x2

/-- **`budP`** at `real40`. -/
theorem budP_ofZ (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8Z δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g) :
    (reqsOf δ b Pb c χ M tr .p).length ≤ 2 * r.N ∧
      (liftP (δ := δ) (provsJ8 δ b Pb χ M tr .p)).length ≤ 2 * r.W := by
  refine ⟨?_, ?_⟩
  · rw [reqsOf_length]
    have h1 := compLenZ δ b Pb c χ M tr hacc hp .p
    have h2 : (extJ8 δ b Pb c χ M tr .p).length = 0 := rfl
    simp only [ReadIOJ8.capB] at h1
    have := hB.p1
    omega
  · simp only [liftP, List.length_map]
    show (ServeH.walkPProvs b Pb.nodesW Pb.orbitW _ _ _).length ≤ 2 * r.W
    rw [walkPProvs_length]; have := hB.p2; omega

theorem atomIncProvs_length_leZ {F K' : Type} [Field F] [Field K'] [Algebra F K'] [DecidableEq F]
    (b' : Basis (Fin 3) F K') {h n w : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (chals pubs : ℕ → K') (Q : Fin w → F[X]) : (atomIncProvs b' nodes orbit chals pubs Q).length ≤ n := by
  unfold atomIncProvs
  exact (AcceptsJ8P.length_flatMap_ite_le _ _ _).trans (by simp)

/-- **`budS`** at `realIO`. -/
theorem budS_ofZ (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8Z δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g) :
    (reqsOf δ b Pb c χ M tr .s).length ≤ r.N + 2 * r.J + g ∧
      (effP (liftP (δ := δ) (provsJ8 δ b Pb χ M tr .s))).length ≤ r.calls + r.heads + r.blocks + r.J := by
  refine ⟨?_, ?_⟩
  · rw [reqsOf_length]
    have h1 := compLenZ δ b Pb c χ M tr hacc hp .s
    have h2 : (extJ8 δ b Pb c χ M tr .s).length =
        Pb.regs.length + (jCount ents0T Pb.lay + jCount ents1T Pb.lay) := by
      simp only [extJ8, byBal]
      erw [List.length_append, jCons_length]
      erw [List.length_map]
    simp only [ReadIOJ8.capB] at h1
    have := hB.s1
    omega
  · refine (List.length_filter_le _ _).trans ?_
    simp only [liftP, List.length_map]
    show (_ ++ (pad8 _ ++ pad8 _)).length ≤ _
    simp only [List.length_append, pad8, List.length_map, jProv_length, walkPProvs_length]
    have := atomIncProvs_length_leZ b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA)
    have := hB.s2
    omega

/-- **`hcount`** from the budgets and the frame's caps below `p`. -/
theorem hcount_ofZ (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8Z δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g)
    (hcap : 3 * r.N + r.W + r.rd < p ∧ 2 * r.N < p ∧ r.N + 2 * r.J + g < p) :
    ∀ bl, (reqsOf δ b Pb c χ M tr bl).length < p := by
  intro bl
  cases bl
  · exact lt_of_le_of_lt (budX_ofZ δ b Pb c χ M tr hacc hp hB).1 hcap.1
  · exact lt_of_le_of_lt (budP_ofZ δ b Pb c χ M tr hacc hp hB).1 hcap.2.1
  · exact lt_of_le_of_lt (budS_ofZ δ b Pb c χ M tr hacc hp hB).1 hcap.2.2

end Budgets

end

end Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZB
