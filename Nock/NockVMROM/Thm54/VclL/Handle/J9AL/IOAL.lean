/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/IOAL.lean

  **(`IOAL`): the compute IO events and counts of S8 from the J-9 AL bundle.** The twin of `J9A/IOJ9A.lean` (`reqsJ9_eqA`, `ioA`) and of the length lemmas of `J9A/BudLenJ9A.lean`.
  * `aluXL_length_le` and the budgets `reqsAL_x_le` ... `hcountAL` at the `RR49AL` lists, rows `rowsBL r`, id
    parameter `gL r g`.  Two extra hypotheses on `.s` (`hSL`: the pins; `hpL`: the ALU provides) are explicit.
  * `reqsJ9_eqAL`: S8's request lists at `extACL` are `RR49AL.reqsAL`.
  * `ioAL`: outside `allJ8C R`, S8's `hout` (x, p), `houtS`, `hcount`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.IOJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.BudLenJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.HbalJ9AL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.RR49AL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.IOAL

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (computeChipVCLHX9)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (liftP)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (byBal)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (pubVJ9)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL (AcceptsJ9AL)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.FibreJ8 (effP)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)

noncomputable section

section Budgets
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

variable {Pb : PubJ9AL p} {tr : TrJ9AL (ZMod p)} {r : RowsJ9AL} {g : ℕ}

theorem aluXL_length_le (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) :
    (RR49AL.aluXL (K := K) δ b Pb tr).length ≤ Pb.nL := by
  unfold RR49AL.aluXL
  split_ifs
  · unfold aluExportReqsOf
    rw [List.length_flatMap]
    calc _ ≤ ((List.finRange Pb.nL).map fun _ => 1).sum :=
          List.sum_le_sum fun i _ => by split_ifs <;> simp
      _ = Pb.nL := by simp
  · simp

theorem aluSL_length_le (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) :
    (RR49AL.aluSL (K := K) δ b Pb tr).length ≤ 2 * Pb.nL := by
  unfold RR49AL.aluSL
  split_ifs
  · unfold aluRegReqsOf
    rw [List.length_flatMap]
    calc _ ≤ ((List.finRange Pb.nL).map fun _ => 2).sum :=
          List.sum_le_sum fun i _ => by split_ifs <;> simp
      _ = 2 * Pb.nL := by simp [mul_comm]
  · simp

theorem pinsP_length (Pb : PubJ9AL p) :
    (RR49AL.pinsP (p := p) (K := K) Pb).length = 2 * Pb.prims.length := by
  simp [RR49AL.pinsP, AcceptsJ9AL.pinRgP, AcceptsJ9AL.pinOpP, two_mul]

theorem reqsAL_length (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) (bl : Bal) :
    (RR49AL.reqsAL δ b Pb tr bl).length =
      (CompReqsX9.compReqsOf9 (K := K) Pb.toPubJ9A tr.toTrJ9A bl).length +
        (RR49AL.extAL δ b Pb tr bl).length := by
  unfold RR49AL.reqsAL
  rw [List.length_map, List.length_append]

theorem reqsAL_x_le (hp : 20 < p) (hB : BudJ9AL Pb r (g + r.N)) (chalV pubVal : ℕ → ZMod p)
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 Pb.hn Pb.nodes b δ chalV pubVal Pb.orbit)
      (qX9 δ b Pb.toPubJ9A tr.toTrJ9A chalV pubVal)) :
    (RR49AL.reqsAL δ b Pb tr .x).length ≤
      3 * (RR49AL.rowsBL r).N + (RR49AL.rowsBL r).W + (RR49AL.rowsBL r).rd := by
  rw [reqsAL_length]
  have h1 := BudLenJ9A.compReqsOf9_length_le (K := K) δ b Pb.toPubJ9A tr.toTrJ9A chalV pubVal hsat hp .x
  have h3 := aluXL_length_le (K := K) δ b Pb tr
  have h2 : (RR49AL.extAL δ b Pb tr .x).length =
      Pb.nW + (RR49AL.aluXL (K := K) δ b Pb tr).length + RealIOJ8.jCount Nock.Jet.ChipJ8.entsX Pb.lay := by
    simp only [RR49AL.extAL, byBal]
    erw [List.length_append, List.length_append, RealIOJ8.walkXReqs_length, RealIOJ8.jRd_length]
    rfl
  simp only [BudLenJ9A.capB9] at h1
  have := hB.x1
  simp only [RR49AL.rowsBL, RR49A.rowsB]
  omega

theorem provsAL_x_le (hB : BudJ9AL Pb r (g + r.N)) :
    (liftP (δ := δ) (RR49AL.provsAL δ b Pb tr .x)).length ≤ (RR49AL.rowsBL r).D := by
  simp only [liftP, List.length_map]
  show (CellTwinKW.cellProvsW b Pb.nodesC Pb.orbitC _ _ _).length ≤ r.D
  simp only [CellTwinKW.cellProvsW, List.length_map, List.length_finRange]
  exact hB.x2

theorem reqsAL_p_le (hp : 20 < p) (hB : BudJ9AL Pb r (g + r.N)) (chalV pubVal : ℕ → ZMod p)
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 Pb.hn Pb.nodes b δ chalV pubVal Pb.orbit)
      (qX9 δ b Pb.toPubJ9A tr.toTrJ9A chalV pubVal)) :
    (RR49AL.reqsAL δ b Pb tr .p).length ≤ 2 * (RR49AL.rowsBL r).N := by
  rw [reqsAL_length]
  have h1 := BudLenJ9A.compReqsOf9_length_le (K := K) δ b Pb.toPubJ9A tr.toTrJ9A chalV pubVal hsat hp .p
  have h2 : (RR49AL.extAL δ b Pb tr .p).length ≤ Pb.nX := by
    simp only [RR49AL.extAL, byBal]
    by_cases hx : Pb.axOn = true
    · simp only [hx, ↓reduceIte]
      exact BudLenJ9A.axPathReqsOf_length_le b Pb.toPubJ9A tr.toTrJ9A
    · simp [hx]
  simp only [BudLenJ9A.capB9] at h1
  have := hB.p1
  simp only [RR49AL.rowsBL, RR49A.rowsB]
  omega

theorem provsAL_p_le (hB : BudJ9AL Pb r (g + r.N)) :
    (liftP (δ := δ) (RR49AL.provsAL δ b Pb tr .p)).length ≤ 2 * (RR49AL.rowsBL r).W := by
  simp only [liftP, List.length_map]
  show (ServeH.walkPProvs b Pb.nodesW Pb.orbitW _ _ _).length ≤ 2 * r.W
  rw [RealIOJ8.walkPProvs_length]
  have := hB.p2
  omega

/-- **`budS` requests.**  EXTRA HYPOTHESIS `hSL : |aluSL| + 2·|prims| ≤ 2·nL` (ALU rows are exclusively `preg` / `hdr`):
`BudJ9AL.s1`'s `2·nL` then covers the ALU service consumes and the primitive pins; `gL` leaves `AL` to spare. -/
theorem reqsAL_s_le (hp : 20 < p) (hB : BudJ9AL Pb r (g + r.N)) (hSL : (RR49AL.aluSL δ b Pb tr).length + 2 * Pb.prims.length ≤ 2 * Pb.nL)
    (chalV pubVal : ℕ → ZMod p)
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 Pb.hn Pb.nodes b δ chalV pubVal Pb.orbit)
      (qX9 δ b Pb.toPubJ9A tr.toTrJ9A chalV pubVal)) :
    (RR49AL.reqsAL δ b Pb tr .s).length ≤
      (RR49AL.rowsBL r).N + 2 * (RR49AL.rowsBL r).J + RR49AL.gL r g := by
  rw [reqsAL_length]
  have h1 := BudLenJ9A.compReqsOf9_length_le (K := K) δ b Pb.toPubJ9A tr.toTrJ9A chalV pubVal hsat hp .s
  have h3 := aluSL_length_le (K := K) δ b Pb tr
  have h4 := pinsP_length (p := p) (K := K) Pb
  have h2 : (RR49AL.extAL δ b Pb tr .s).length ≤
      Pb.regs.length + (RR49AL.pinsP (p := p) (K := K) Pb).length + Pb.nX + (RR49AL.aluSL (K := K) δ b Pb tr).length +
        (RealIOJ8.jCount Nock.Jet.ChipJ8.ents0T Pb.lay + RealIOJ8.jCount Nock.Jet.ChipJ8.ents1T Pb.lay) := by
    simp only [RR49AL.extAL, byBal]
    erw [List.length_append, List.length_append, List.length_append, List.length_append, RealIOJ8.jCons_length]
    have e1 : (pinCons (p := p) (K := K) Pb.regs Pb.idx).length = Pb.regs.length := by
      unfold pinCons; exact List.length_map _
    by_cases hx : Pb.axOn = true
    · simp only [hx, ↓reduceIte]
      have e2 := BudLenJ9A.axLimbReqsOf_length b Pb.toPubJ9A tr.toTrJ9A
      simp only [mOf] at *
      omega
    · simp only [hx, Bool.false_eq_true, ↓reduceIte]
      simp only [mOf, List.length_nil] at *
      omega
  simp only [BudLenJ9A.capB9] at h1
  have := hB.s1
  simp only [RR49AL.rowsBL, RR49A.rowsB, RR49AL.gL]
  omega

/-- **`budS` providers.**  EXTRA HYPOTHESIS `hpL : (aluPL δ b Pb tr).length ≤ 2 * Pb.nL`: `BudJ9AL.s2` charges `2·nL`
for the ALU provides, while `aluRegProvsOf` (`≤ 2` per row) and `aluJetProvsOf` (`≤ 1` per row) bound the list only
by `3·nL` (an honest row is `preg` or `hdr`, not both; not derivable from `hB`). -/
theorem provsAL_s_le (hB : BudJ9AL Pb r (g + r.N)) (hpL : (RR49AL.aluPL δ b Pb tr).length ≤ 2 * Pb.nL) :
    (effP (liftP (δ := δ) (RR49AL.provsAL δ b Pb tr .s))).length ≤
      (RR49AL.rowsBL r).calls + (RR49AL.rowsBL r).heads + (RR49AL.rowsBL r).blocks + (RR49AL.rowsBL r).J := by
  refine (List.length_filter_le _ _).trans ?_
  simp only [liftP, List.length_map]
  show (jProv b Pb.nodesJ Pb.orbitJ _ _ Pb.lay tr.J ++
      (pad8 (atomIncProvs b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A) ++
        (if 1 ≤ Pb.krootsV then pad8 (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (fun _ => (0 : K)) (fun _ => 0) tr.V)
          else []) ++
        ((if Pb.axOn then axTagProvsOf b Pb.toPubJ9A tr.toTrJ9A else []) ++ RR49AL.aluPL δ b Pb tr) ++
        (if Pb.spOn then splitProvsOf b Pb.toPubJ9A tr.toTrJ9A else []))).length ≤ _
  have h0 : (if 1 ≤ Pb.krootsV then pad8 (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (fun _ => (0 : K)) (fun _ => 0) tr.V)
      else ([] : List ((Fin 8 → K) × K))).length ≤ 2 * Pb.nV := by
    split_ifs
    · simp [pad8, RealIOJ8.walkPProvs_length]
    · simp
  simp only [List.length_append, pad8, List.length_map, RealIOJ8.jProv_length, RealIOJ8.walkPProvs_length] at h0 ⊢
  have h1 := BudLenJ9A.atomIncProvs_length_le9 b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A
  have h2 : (if Pb.axOn then axTagProvsOf b Pb.toPubJ9A tr.toTrJ9A else ([] : List ((Fin 8 → K) × K))).length ≤ Pb.nX := by
    split_ifs
    · exact BudLenJ9A.axTagProvsOf_length_le b Pb.toPubJ9A tr.toTrJ9A
    · simp
  have h3 : (if Pb.spOn then splitProvsOf b Pb.toPubJ9A tr.toTrJ9A else ([] : List ((Fin 8 → K) × K))).length ≤ 2 * Pb.nS := by
    split_ifs
    · exact BudLenJ9A.splitProvsOf_length_le b Pb.toPubJ9A tr.toTrJ9A
    · simp
  have := hB.s2
  simp only [RR49AL.rowsBL, RR49A.rowsB]
  omega

theorem hcountAL (hp : 20 < p) (hB : BudJ9AL Pb r (g + r.N)) (hSL : (RR49AL.aluSL δ b Pb tr).length + 2 * Pb.prims.length ≤ 2 * Pb.nL)
    (chalV pubVal : ℕ → ZMod p)
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 Pb.hn Pb.nodes b δ chalV pubVal Pb.orbit)
      (qX9 δ b Pb.toPubJ9A tr.toTrJ9A chalV pubVal))
    (hcap : 3 * (RR49AL.rowsBL r).N + (RR49AL.rowsBL r).W + (RR49AL.rowsBL r).rd < p ∧
      2 * (RR49AL.rowsBL r).N < p ∧ (RR49AL.rowsBL r).N + 2 * (RR49AL.rowsBL r).J + RR49AL.gL r g < p) :
    ∀ bl, (RR49AL.reqsAL δ b Pb tr bl).length < p := by
  intro bl
  cases bl
  · exact lt_of_le_of_lt (reqsAL_x_le δ b hp hB chalV pubVal hsat) hcap.1
  · exact lt_of_le_of_lt (reqsAL_p_le δ b hp hB chalV pubVal hsat) hcap.2.1
  · exact lt_of_le_of_lt (reqsAL_s_le δ b hp hB hSL chalV pubVal hsat) hcap.2.2

end Budgets

section IO
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem reqsJ9_eqAL (Pb : PubJ9AL p) (χ : Coins frameJ8 K) (M : MsgJ9AL' p K δ) (tr : TrJ9AL (ZMod p))
    (chalV pv : ℕ → ZMod p) (bl : Bal) :
    TeleX9.reqsJ9 (hn := Pb.hn) (nodes := Pb.nodes) (b := b) (δ := δ) (chalV := chalV) (pubVal := pv)
      (orbit := Pb.orbit) (P := qX9 δ b Pb.toPubJ9A tr.toTrJ9A chalV pv)
      (HbalJ9AL.extACL δ b Pb χ M tr) bl = RR49AL.reqsAL δ b Pb tr bl := by
  unfold TeleX9.reqsJ9 RR49AL.reqsAL
  rw [HbalJ9AL.extACL_eq δ b Pb χ M tr bl]
  exact congrArg (fun l => (l ++ RR49AL.extAL δ b Pb tr bl).map (BalanceQ.liftRec (L := 𝕂′)))
    (CompReqsX9.compReqsX9_eq_of9 Pb.toPubJ9A tr.toTrJ9A chalV pv bl)

theorem reqsAL_p_eq (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) :
    RR49AL.reqsAL δ b Pb tr .p = RR49A.reqsA δ b Pb.axOn Pb.toPubJ9A tr.toTrJ9A .p := rfl

theorem provsAL_p_eq (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) :
    RR49AL.provsAL δ b Pb tr .p = RR49A.provsA b Pb.axOn Pb.spOn Pb.toPubJ9A tr.toTrJ9A .p := rfl

/-- **S8's compute IO events and counts, from the bundle** (J-9 AL).  EXTRA HYPOTHESES `hSL`, `hpL` (see
`reqsAL_s_le`, `provsAL_s_le`). -/
theorem ioAL {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {r : RowsJ9AL} {g P : ℕ}
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9AL (ZMod p)) StJ9AL (RR49AL.rowsBL r) P
      (RR49AL.gL r g))
    (hRx : R.D.cxReqs tr χ = RR49AL.reqsAL δ b Pb tr .x ∧
      R.D.cxProvs tr χ = liftP (RR49AL.provsAL δ b Pb tr .x))
    (hRs : R.D.svReqs tr χ = RR49AL.reqsAL δ b Pb tr .s ∧
      R.D.svProvs tr χ = effP (liftP (RR49AL.provsAL δ b Pb tr .s)))
    (hout : ∀ s ∈ allJ8C R, ¬ s.mem tr χ)
    (hpp : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (RR49AL.reqsAL δ b Pb tr .p) (liftP (RR49AL.provsAL δ b Pb tr .p)))
    (hacc : AcceptsJ9AL δ b Pb Rg c χ M tr r g) (hp : 20 < p)
    (hcap : 3 * (RR49AL.rowsBL r).N + (RR49AL.rowsBL r).W + (RR49AL.rowsBL r).rd < p ∧
      2 * (RR49AL.rowsBL r).N < p ∧ (RR49AL.rowsBL r).N + 2 * (RR49AL.rowsBL r).J + RR49AL.gL r g < p)
    (hSL : (RR49AL.aluSL δ b Pb tr).length + 2 * Pb.prims.length ≤ 2 * Pb.nL)
    (hpL : (RR49AL.aluPL δ b Pb tr).length ≤ 2 * Pb.nL) :
    (∀ bl, bl ≠ .s → ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (TeleX9.reqsJ9 (hn := Pb.hn) (nodes := Pb.nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ9 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
        (P := qX9 δ b Pb.toPubJ9A tr.toTrJ9A (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ))
        (HbalJ9AL.extACL δ b Pb χ M tr) bl)
        (liftP (HbalJ9AL.provsACL δ b Pb χ M tr bl))) ∧
    (((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (TeleX9.reqsJ9 (hn := Pb.hn) (nodes := Pb.nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ9 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
        (P := qX9 δ b Pb.toPubJ9A tr.toTrJ9A (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ))
        (HbalJ9AL.extACL δ b Pb χ M tr) .s)
        (effP (liftP (HbalJ9AL.provsACL δ b Pb χ M tr .s)))) ∧
    (∀ bl, (TeleX9.reqsJ9 (hn := Pb.hn) (nodes := Pb.nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ9 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
        (P := qX9 δ b Pb.toPubJ9A tr.toTrJ9A (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ))
        (HbalJ9AL.extACL δ b Pb χ M tr) bl).length < p) := by
  have hB := hacc.hbud
  have hsat := hacc.hsatX
  have hx' := ListJ8C.hout_x_of_outsideC R b hout _ _ hRx.1 hRx.2
    (reqsAL_x_le δ b hp hB _ _ hsat) (provsAL_x_le δ b hB)
  have hs' := ListJ8C.hout_s_of_outsideC R b hout _ _ hRs.1 hRs.2
    (reqsAL_s_le δ b hp hB hSL _ _ hsat) (provsAL_s_le δ b hB hpL)
  have hc := hcountAL δ b hp hB hSL _ _ hsat hcap
  refine ⟨fun bl hbl => ?_, ?_, fun bl => ?_⟩
  · rw [reqsJ9_eqAL, HbalJ9AL.provsACL_eq]
    cases bl with
    | x => exact hx'
    | p => exact hpp
    | s => exact absurd rfl hbl
  · rw [reqsJ9_eqAL, HbalJ9AL.provsACL_eq]
    exact hs'
  · rw [reqsJ9_eqAL]
    exact hc bl

end IO

end

end Nock.NockVMROM.Thm54.VclL.Handle.IOAL
