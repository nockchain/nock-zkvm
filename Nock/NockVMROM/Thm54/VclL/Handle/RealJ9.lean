/-
  Nock/NockVMROM/Thm54/VclL/Handle/RealJ9.lean

  **The trace readouts of the J-9 claim lists** (both layouts).
  * `claimRecsT9`: `RealVJ8.claimRecsT` `++` the big-leaf records, the serials READ off compute row 0;
    `valReqsJ9` (the readout's requests with them), `valJ9_reads` (round 0), `valJ9_length` (same budget as J-8: `≤ 3` claim
    records).
  * `claimX`: the claim's big atoms and the atom-table nouns at the claim serials (`≤ 6` nouns, round 0).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9ZL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.RealJ9

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

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun claimH isCellN)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crA crM crW crC staged_eq below_of_mem shV)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (mbXs claimCells claimRecsJ8 pinRecsJ8 rkC MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z chalsAJ8Z_zAt)

open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.RealVJ8

noncomputable section

section Val
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (xS xF xE)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (envCJ8)

/-- The claim serial of position `k`, read off compute row 0 (round-0 column). -/
def claimRow0 (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (k : Fin 3) : ZMod p :=
  (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C 0).trace (![xS, xF, xE] k).v

theorem claimRow0_const (Pb : PubJ8 p) (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q) (χ χ' : Coins frameJ8 K)
    (k : Fin 3) : claimRow0 Pb (Q χ) k = claimRow0 Pb (Q χ') k := by
  have hk : (![xS, xF, xE] k).v < 69 := by fin_cases k <;> decide
  simp only [claimRow0, envCJ8]
  rw [envOfTrace_trace _ _ _ _ _ (by omega : (![xS, xF, xE] k).v < 123),
    envOfTrace_trace _ _ _ _ _ (by omega : (![xS, xF, xE] k).v < 123),
    staged_eq hQ.1 (r := 0) (fun i hi => absurd hi (by omega)) _ (by simp only [crC, if_pos hk, le_refl])]

/-- **The J-9 claim records off the trace**: the cell records (`claimRecsT`) and the big-leaf records
`claimVec (E (atom n)) serial 0 0`. -/
def claimRecsT9 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (tr : TrJ8 (ZMod p)) :
    List (Fin 5 → 𝕂′) :=
  claimRecsT δ Pb c χ tr ++ (claimBigs p c).map fun k =>
    ClaimVS.claimVec δ (encJ8 δ χ (claimNoun c k)) (claimRow0 Pb tr k) 0 0

/-- **The readout's requests on a J-9 trace.** -/
def valReqsJ9 (Pb : PubJ8 p) (c : P8PublicClaim) (tr : TrJ8 (ZMod p)) (χ : Coins frameJ8 K) : List (Fin 5 → 𝕂′) :=
  (claimRecsT9 δ Pb c χ tr ++ pinRecsJ8 δ Pb χ) ++
    cVInt δ b Pb.nodesC Pb.orbitC (fun _ => (0 : K)) (fun _ => 0) (restrictQ 129 134 shM tr.M)

theorem valJ9_reads (Pb : PubJ8 p) (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q) :
    ReadsOnC frameJ8 (coinsBelow frameJ8 1) fun χ => (valReqsJ9 δ b Pb c (Q χ) χ, valProvsJ8 δ b Pb (Q χ) χ) := by
  intro χ χ' hχ
  have h8 := valJ8_reads δ b Pb c Q hQ χ χ' hχ
  have hE := encJ8_congr δ hχ
  have h1 := congrArg Prod.fst h8
  have h2 := congrArg Prod.snd h8
  simp only at h1 h2
  refine Prod.ext ?_ h2
  simp only [valReqsJ8] at h1
  have hb : (claimBigs p c).map (fun k => ClaimVS.claimVec δ (encJ8 δ χ (claimNoun c k)) (claimRow0 Pb (Q χ) k) 0 0) =
      (claimBigs p c).map (fun k => ClaimVS.claimVec δ (encJ8 δ χ' (claimNoun c k)) (claimRow0 Pb (Q χ') k) 0 0) := by
    refine List.map_congr_left fun k _ => ?_
    rw [hE, claimRow0_const Pb Q hQ χ χ' k]
  show (claimRecsT9 δ Pb c χ (Q χ) ++ _) ++ _ = (claimRecsT9 δ Pb c χ' (Q χ') ++ _) ++ _
  simp only [claimRecsT9, List.append_assoc] at h1 ⊢
  obtain ⟨h1a, h1b⟩ := List.append_inj h1 (by simp [claimRecsT])
  rw [h1a, hb, h1b]

theorem claimRecsT9_length (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (tr : TrJ8 (ZMod p)) :
    (claimRecsT9 δ Pb c χ tr).length ≤ 3 := by
  simp only [claimRecsT9, claimRecsT, List.length_append, List.length_map]
  exact claimCells_bigs_length p c

theorem valJ9_length (Pb : PubJ8 p) (c : P8PublicClaim) (tr : TrJ8 (ZMod p)) (χ : Coins frameJ8 K) :
    (valReqsJ9 δ b Pb c tr χ).length ≤ 3 + Pb.regs.length + 2 * Pb.nC ∧
      (valProvsJ8 δ b Pb tr χ).length ≤ Pb.nC + Pb.nA := by
  refine ⟨?_, (valJ8_length δ b Pb c tr χ).2⟩
  unfold valReqsJ9
  have h1 := claimRecsT9_length δ Pb c χ tr
  have h2 := cVInt_length δ b Pb.nodesC Pb.orbitC (fun _ => (0 : K)) (fun _ => 0) (restrictQ 129 134 shM tr.M)
  simp only [List.length_append, pinRecsJ8, List.length_map]
  omega

/-- **The claim's census extension**: its big atoms, and the atom-table nouns at the claim serials of the big
positions. -/
def claimX (Pb : PubJ8 p) (c : P8PublicClaim) (tr : TrJ8 (ZMod p)) : List Noun :=
  (claimBigs p c).map (claimNoun c) ++ (claimBigs p c).filterMap fun k => extT8 (K := K) b Pb tr (claimRow0 Pb tr k).val

theorem claimX_length (Pb : PubJ8 p) (c : P8PublicClaim) (tr : TrJ8 (ZMod p)) :
    (claimX (K := K) b Pb c tr).length ≤ 6 := by
  have h := claimCells_bigs_length p c
  have h2 := List.length_filterMap_le (fun k => extT8 (K := K) b Pb tr (claimRow0 Pb tr k).val) (claimBigs p c)
  simp only [claimX, List.length_append, List.length_map]
  omega

theorem claimX_const (Pb : PubJ8 p) (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q)
    (χ χ' : Coins frameJ8 K) : claimX (K := K) b Pb c (Q χ) = claimX (K := K) b Pb c (Q χ') := by
  simp only [claimX, extT8_staged b Pb Q hQ χ χ', claimRow0_const Pb Q hQ χ χ']

end Val

section Data
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

def withJ9 (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (Pb : PubJ8 p) (c : P8PublicClaim) (hP : P = 2 ^ 66) (hnM : Pb.nC ≤ 2 ^ 31)
    (hreg9 : (censusG Pb c).length + 6 ≤ 2 ^ 31) :
    DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g :=
  { R with
    D := { R.D with
      valReqs := fun tr χ => valReqsJ9 δ b Pb c tr χ
      valProvs := fun tr χ => valProvsJ8 δ b Pb tr χ
      val_reads := fun Q hQ => valJ9_reads δ b Pb c Q hQ
      prs := fun tr => EncInjJ8.censusPairs (censusList2 (TraceJ8.rowsMJ8 Pb.nodesC Pb.orbitC tr) (extT8 b Pb tr) ++
        (censusG Pb c ++ claimX b Pb c tr))
      prs_le := fun tr => hP ▸ LinkQ2J8.censusPairs_reg_length_le _ _ _
        (by rw [TraceJ8.rowsMJ8, TraceJ8.rowsB0_length]; exact hnM)
        (by have := claimX_length (K := K) b Pb c tr; rw [List.length_append]; omega)
      prs_const := fun Q hQ χ χ' => by
        simp only [TraceJ8.rowsMJ8_const Pb.nodesC Pb.orbitC Q hQ χ χ', extT8_staged b Pb Q hQ χ χ',
          claimX_const b Pb c Q hQ χ χ'] } }

end Data

end

end Nock.NockVMROM.Thm54.VclL.Handle.RealJ9
