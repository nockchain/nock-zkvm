/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/RR49AL.lean

  **The J-9 AL real data and its bound.**

  * **Rows.**  `rowsBL r` = `RR49A.rowsB r` (J-9 A option (b)) with `blocks += 2·AL` (the ALU service provides:
    `BudJ9AL.s2` charges `2·nL`) and `rd += AL` (the ALU export reads: `BudJ9AL.x1` charges `nL`); the id parameter
    `gL r g = g + N + AX + 3·AL` (validity: `pinRecsP` + `aluFpReqsOf`, `≤ 2·nL`; service: `aluRegReqsOf` + the
    prim pins, `≤ 3·nL`).
  * **The bound** `boundJ9AL = boundJ8X (rowsBL r) P (gL r g) + weightC/|𝕂|²` (`weightC = AL·(2A + 32·AL + 2)`, the
    `AluSZEvent` per-call `arithSZ` at `C = AL`).  `numJ9AL_le_P4`: at the census corner (`cornerC9L`, `g = 2^31`) the
    numerator is `≤` the `RepriceJ9AL.numJ8X_optL_census32` quantity (kernel `decide`), so `figJ9AL_155`:
    `boundJ9AL < 2^-155` below the corner.  That statement is consumed as is.
  * **The coin-free lists** `extAL` / `provsAL` / `reqsAL` (round-0 columns, `ReadsOnC frameJ8 ∅`), in the S8 wiring
    order (`HokJ9AG9`): `ext .x = (walkX ++ aluX) ++ jRd`, `ext .s = pinCons regs ++ (pinsP ++ axLimb ++ aluReg) ++
    jCons`, `provs .s = jProv ++ (inc ++ walkV ++ (axTag ++ aluProv) ++ split)`.  The ALU lists are gated on the
    public flag `aluOn`.  `pinsP` is the ONE place naming the verifier's primitive pins: `pinRgP ++ pinOpP` (the
    keyRg pin and the op-record pin of `AcceptsJ9AL.hGS`).
  * **The datum** `XAL X Pb c`: any J-9 A datum `X` at `rowsB r` pulled back along `TrJ9AL.toTrJ9A`, re-indexed to
    `rowsBL r` / `gL r g`, with #2 / #5 / #6 replaced; `allJ9AL = allJ8X (XAL …) ++ [arithSZ]`, `epsilon_allJ9AL`,
    `probJ9AL_lt_155`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.RR49A
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL
import Nock.NockVMROM.Thm54.VclL.Handle.AluSZEvent
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.RepriceJ9AL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.RR49AL

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 Nock.NockVMROM.Thm54.VclL.Handle.WeightsPinJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (prob_le_of_outside)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8 (cornerC)
open Nock.NockVMROM.Thm54.VclL.Events (cK cK_eq cK_pos)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crJ crA crW staged_eq below_of_mem)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (byBal)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (liftP)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.FibreJ8 (effP)

noncomputable section

/-! ## 1. Rows, the bound, the figure -/

/-- **The J-9 AL rows**: J-9 A option (b) (`blocks + AX + 2·SP`), plus the ALU's two service provides per row on
`blocks` and its export read per row on `rd`. -/
def rowsBL (r : RowsJ9AL) : RowsJ8 :=
  { RR49A.rowsB r.toRowsJ9A with blocks := r.blocks + r.AX + 2 * r.SP + 2 * r.AL, rd := r.rd + r.AL }

/-- **The J-9 AL id parameter**: `g + N + AX` (J-9 A) plus `3·AL` (the ALU's validity and service consumes and the
primitive pins, `≤ 3·nL`). -/
def gL (r : RowsJ9AL) (g : ℕ) : ℕ := g + r.N + r.AX + 3 * r.AL

/-- The `arithSZ` weight at `C = AL` calls (`AluSZEvent.weightC`). -/
def wSZ (r : RowsJ9AL) : ℕ := AluSZEvent.weightC r.AL r.A r.AL

/-- **The J-9 AL numerator over `|𝕂|⁴`** (at `|𝕂′| = |𝕂|²`). -/
def numJ9AL (c : ℕ) (r : RowsJ9AL) (P g : ℕ) : ℕ := numJ8X c (rowsBL r) P (gL r g) + wSZ r * c ^ 2

/-- **The J-9 AL bound**: `boundJ8X` at the J-9 AL rows plus the `arithSZ` weight over `|𝕂|²`. -/
def boundJ9AL (c c' : ℕ) (r : RowsJ9AL) (P g : ℕ) : ℚ :=
  boundJ8X c c' (rowsBL r) P (gL r g) + (wSZ r : ℚ) / (c : ℚ) ^ 2

theorem boundJ9AL_eq (c : ℕ) (r : RowsJ9AL) (P g : ℕ) (hc : 0 < c) :
    boundJ9AL c (c ^ 2) r P g = (numJ9AL c r P g : ℚ) / (c : ℚ) ^ 4 := by
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [boundJ9AL, boundJ8X_eq c _ _ _ hc, numJ9AL]
  push_cast
  field_simp

/-- The quantity (`RepriceJ9AL.numJ8X_optL_census32`), named. -/
def xP4 (c : ℕ) : ℕ :=
  numJ8X c { cornerC9.toRowsJ8 with blocks := cornerC9.blocks + 2 ^ 31 + 2 * 2 ^ 31 + 2 ^ 31 } (2 ^ 66)
      (2 ^ 33 + 2 ^ 31 + 2 * 2 ^ 31)
    + ioFailureUnionBound 5 (3 + 2 * 2 ^ 31 + 5 * 2 ^ 31) (2 ^ 31) (c ^ 2)
    + 2 ^ 31 * (2 * 2 ^ 31 + 32 * 2 ^ 31 + 2) * c ^ 2

theorem xP4_lt (c : ℕ) (hc : c = 18446744069414584321 ^ 3) : xP4 c * 2 ^ 155 < c ^ 4 :=
  RepriceJ9AL.numJ8X_optL_census32 c hc

/-- **The J-9 AL numerator at the census corner is under that of `RepriceJ9AL`** (kernel `decide`; the corner is `cornerC9L`,
`P = 2^66`, `g = 2^31`, so `gL = 6·2^31`). -/
theorem numJ9AL_le_P4 (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    numJ9AL c cornerC9L (2 ^ 66) (2 ^ 31) ≤ xP4 c := by
  subst hc
  unfold numJ9AL xP4 rowsBL gL wSZ AluSZEvent.weightC RR49A.rowsB cornerC9L numJ8X numJ8Pin cornerC9 numHQ cornerC
    corner31 fuelChip pairCount ioFailureUnionBound
  decide +kernel

theorem rowsBL_le {r : RowsJ9AL} (h : RowsLe r.toRowsJ8 cornerC) (hAX : r.AX ≤ 2 ^ 31) (hSP : r.SP ≤ 2 ^ 31)
    (hAL : r.AL ≤ 2 ^ 31) : RowsLe (rowsBL r) (rowsBL cornerC9L) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, ?_, h14, h15⟩
  · show r.blocks + r.AX + 2 * r.SP + 2 * r.AL ≤ cornerC.blocks + 2 ^ 31 + 2 * 2 ^ 31 + 2 * 2 ^ 31
    omega
  · show r.rd + r.AL ≤ cornerC.rd + 2 ^ 31
    omega

/-- **Monotone to the corner.** -/
theorem numJ9AL_corner {c : ℕ} {r : RowsJ9AL} {P g : ℕ} (h : RowsLe r.toRowsJ8 cornerC) (hAX : r.AX ≤ 2 ^ 31)
    (hSP : r.SP ≤ 2 ^ 31) (hAL : r.AL ≤ 2 ^ 31) (hP : P ≤ 2 ^ 66) (hg : g ≤ 2 ^ 31) :
    numJ9AL c r P g ≤ numJ9AL c cornerC9L (2 ^ 66) (2 ^ 31) := by
  have hN := h.1
  have hA := h.2.2.2.2.1
  simp only [cornerC, corner31] at hN hA
  have e1 := numJ8X_corner (c := c) (rowsBL_le h hAX hSP hAL) hP
    (show gL r g ≤ gL cornerC9L (2 ^ 31) by
      show g + r.N + r.AX + 3 * r.AL ≤ 2 ^ 31 + cornerC.N + 2 ^ 31 + 3 * 2 ^ 31
      simp only [cornerC, corner31]; omega)
  have e2 : wSZ r ≤ wSZ cornerC9L := by
    show r.AL * (2 * r.A + 32 * r.AL + 2) ≤ 2 ^ 31 * (2 * cornerC.A + 32 * 2 ^ 31 + 2)
    simp only [cornerC, corner31]
    exact Nat.mul_le_mul hAL (by omega)
  unfold numJ9AL
  have := Nat.mul_le_mul_right (c ^ 2) e2
  omega

/-- **The J-9 AL figure: `< 2^-155`** below the census corner (`AX, SP, AL ≤ 2^31`, `P ≤ 2^66`, `g ≤ 2^31`). -/
theorem figJ9AL_155 {r : RowsJ9AL} {P g : ℕ} (h : RowsLe r.toRowsJ8 cornerC) (hAX : r.AX ≤ 2 ^ 31)
    (hSP : r.SP ≤ 2 ^ 31) (hAL : r.AL ≤ 2 ^ 31) (hP : P ≤ 2 ^ 66) (hg : g ≤ 2 ^ 31) :
    boundJ9AL cK (cK ^ 2) r P g < 1 / (2 : ℚ) ^ 155 := by
  rw [boundJ9AL_eq _ _ _ _ cK_pos]
  have h1 := numJ9AL_corner (c := cK) h hAX hSP hAL hP hg
  have h2 := numJ9AL_le_P4 cK cK_eq
  have h3 := xP4_lt cK cK_eq
  have hn : numJ9AL cK r P g * 2 ^ 155 < cK ^ 4 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (h1.trans h2)) h3
  have hc : (0 : ℚ) < (cK : ℚ) ^ 4 := by have := cK_pos; positivity
  rw [div_lt_div_iff₀ hc (by positivity), one_mul]
  exact_mod_cast hn

/-! ## 2. The coin-free J-9 AL lists -/

section Lists
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The verifier's primitive pins** (the ONE place naming them; `AcceptsJ9AL.hGS`'s primitive consumes). -/
def pinsP (Pb : PubJ9AL p) : List (Fin 8 → K) :=
  AcceptsJ9AL.pinRgP (p := p) (K := K) Pb ++ AcceptsJ9AL.pinOpP (p := p) (K := K) Pb

/-- The ALU's export reads, gated on `aluOn`. -/
def aluXL (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) : List (Fin 5 → K) :=
  if Pb.aluOn then aluExportReqsOf δ b Pb tr else []

/-- The ALU's service consumes, gated on `aluOn`. -/
def aluSL (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) : List (Fin 8 → K) :=
  if Pb.aluOn then aluRegReqsOf δ b Pb tr else []

/-- The ALU's service provides (`preg`: keyRg + op record; `hdr`: keyJet), gated on `aluOn`. -/
def aluPL (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) : List ((Fin 8 → K) × K) :=
  if Pb.aluOn then aluRegProvsOf δ b Pb tr ++ aluJetProvsOf δ b Pb tr else []

/-- **The J-9 AL externals** (coin-free). -/
def extAL (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) : (bl : Bal) → List (Fin (mOf bl) → K) :=
  byBal (β := fun bl => List (Fin (mOf bl) → K))
    ((ServeH.walkXReqs b Pb.nodesW Pb.orbitW (fun _ => (0 : K)) (fun _ => 0) tr.W ++ aluXL δ b Pb tr) ++
      jRd b Pb.nodesJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0) Pb.lay tr.J)
    (if Pb.axOn then axPathReqsOf b Pb.toPubJ9A tr.toTrJ9A else [])
    (pinCons (p := p) (K := K) Pb.regs Pb.idx ++
      (pinsP Pb ++ (if Pb.axOn then axLimbReqsOf b Pb.toPubJ9A tr.toTrJ9A else []) ++ aluSL δ b Pb tr) ++
      jCons b Pb.nodesJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0) Pb.lay tr.J)

/-- **The J-9 AL providers** (coin-free). -/
def provsAL (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) : (bl : Bal) → List ((Fin (mOf bl) → K) × K) :=
  byBal (β := fun bl => List ((Fin (mOf bl) → K) × K))
    (RealIOJ8.provsT b Pb.toPubJ8 tr.toJ8 .x)
    (RealIOJ8.provsT b Pb.toPubJ8 tr.toJ8 .p)
    (jProv b Pb.nodesJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0) Pb.lay tr.J ++
      (pad8 (atomIncProvs b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A) ++
        (if 1 ≤ Pb.krootsV then pad8 (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (fun _ => (0 : K)) (fun _ => 0) tr.V)
          else []) ++
        ((if Pb.axOn then axTagProvsOf b Pb.toPubJ9A tr.toTrJ9A else []) ++ aluPL δ b Pb tr) ++
        (if Pb.spOn then splitProvsOf b Pb.toPubJ9A tr.toTrJ9A else [])))

/-- **The J-9 AL requests of balance `bl`** (coin-free): the twin compute's and the externals, lifted. -/
def reqsAL (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) (bl : Bal) : List (Fin (mOf bl) → 𝕂′) :=
  (CompReqsX9.compReqsOf9 (K := K) Pb.toPubJ9A tr.toTrJ9A bl ++ extAL δ b Pb tr bl).map (liftRec (L := 𝕂′))

/-- Along `StJ9AL`, the four ALU round-0 lists agree at any two coins. -/
theorem alu_const (Pb : PubJ9AL p) {Q : Coins frameJ8 K → TrJ9AL (ZMod p)} (hQ : StJ9AL Q)
    (χ χ' : Coins frameJ8 K) :
    aluXL δ b Pb (Q χ) = aluXL δ b Pb (Q χ') ∧ aluSL δ b Pb (Q χ) = aluSL δ b Pb (Q χ') ∧
      aluPL δ b Pb (Q χ) = aluPL δ b Pb (Q χ') := by
  obtain ⟨h1, h2, h3, h4⟩ := lists_readsL δ b Pb hQ
  have e : ∀ i ∈ (∅ : Finset (Fin frameJ8.n)), χ i = χ' i := fun i hi => absurd hi (Finset.notMem_empty i)
  refine ⟨?_, ?_, ?_⟩
  · have e4 : aluExportReqsOf δ b Pb (Q χ) = aluExportReqsOf δ b Pb (Q χ') := h4 χ χ' e
    unfold aluXL; rw [e4]
  · have e1 : aluRegReqsOf δ b Pb (Q χ) = aluRegReqsOf δ b Pb (Q χ') := h1 χ χ' e
    unfold aluSL; rw [e1]
  · have e2 : aluRegProvsOf δ b Pb (Q χ) = aluRegProvsOf δ b Pb (Q χ') := h2 χ χ' e
    have e3 : aluJetProvsOf δ b Pb (Q χ) = aluJetProvsOf δ b Pb (Q χ') := h3 χ χ' e
    unfold aluPL; rw [e2, e3]

/-- **Along `StJ9AL` the J-9 AL lists are constant in the coins.** -/
theorem listsAL_const (Pb : PubJ9AL p) {Q : Coins frameJ8 K → TrJ9AL (ZMod p)} (hQ : StJ9AL Q)
    (χ χ' : Coins frameJ8 K) (bl : Bal) :
    reqsAL δ b Pb (Q χ) bl = reqsAL δ b Pb (Q χ') bl ∧ provsAL δ b Pb (Q χ) bl = provsAL δ b Pb (Q χ') bl := by
  obtain ⟨h, hX, hS⟩ := RR49A.agreeA (Q := fun χ => (Q χ).toTrJ9A) hQ.1 χ χ'
  obtain ⟨aX, aS, aP⟩ := alu_const δ b Pb hQ χ χ'
  have hC := RR49A.compA_const (K := K) Pb.toPubJ9A (Q := fun χ => (Q χ).toTrJ9A) hQ.1 χ χ' bl
  have hW := DescentVSQ.walkLists_congrW b Pb.nodesW Pb.orbitW Pb.orbitW (fun _ => (0 : K)) (fun _ => 0)
    (fun _ => (0 : K)) (fun _ => 0) (Q χ).W (Q χ').W (by norm_num) (by norm_num)
    (fun c h1 h2 hc => h.W ⟨c, h1⟩ (by simp [crW, hc]))
  have hV := DescentVSQ.walkLists_congrW b Pb.nodesV Pb.orbitV Pb.orbitV (fun _ => (0 : K)) (fun _ => 0)
    (fun _ => (0 : K)) (fun _ => 0) (Q χ).V (Q χ').V (by norm_num) (by norm_num)
    (fun c h1 h2 hc => h.V ⟨c, h1⟩ (by simp [crW, hc]))
  have hJ := ReadIOJ8.jLists_congr b Pb.nodesJ Pb.orbitJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0)
    (fun _ => (0 : K)) (fun _ => 0) (Q χ).J (Q χ').J Pb.lay (by norm_num) (by norm_num)
    (fun c h1 h2 hc => h.J ⟨c, h1⟩ (by simp [crJ, hc]))
  have hA := ReadIOJ8.atomIncProvs_congr b Pb.nodesA Pb.orbitA Pb.orbitA (fun _ => (0 : K))
      (fun _ => 0) (fun _ => (0 : K)) (fun _ => 0) (Q χ).A (Q χ').A (by norm_num) (by norm_num)
      (fun c h1 h2 hc => h.A ⟨c, h1⟩ (by simp [crA, hc]))
  have hE : extAL δ b Pb (Q χ) bl = extAL δ b Pb (Q χ') bl := by
    cases bl
    · show (_ ++ aluXL δ b Pb (Q χ)) ++ _ = (_ ++ aluXL δ b Pb (Q χ')) ++ _
      rw [hW.1, hJ.1, aX]
    · show (if Pb.axOn then axPathReqsOf b Pb.toPubJ9A (Q χ).toTrJ9A else []) =
        (if Pb.axOn then axPathReqsOf b Pb.toPubJ9A (Q χ').toTrJ9A else [])
      rw [axPathReqsOf_congr b Pb.toPubJ9A hX]
    · show pinCons (p := p) (K := K) Pb.regs Pb.idx ++
          (pinsP Pb ++ (if Pb.axOn then axLimbReqsOf b Pb.toPubJ9A (Q χ).toTrJ9A else []) ++ aluSL δ b Pb (Q χ)) ++
          jCons b Pb.nodesJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0) Pb.lay (Q χ).J =
        pinCons (p := p) (K := K) Pb.regs Pb.idx ++
          (pinsP Pb ++ (if Pb.axOn then axLimbReqsOf b Pb.toPubJ9A (Q χ').toTrJ9A else []) ++ aluSL δ b Pb (Q χ')) ++
          jCons b Pb.nodesJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0) Pb.lay (Q χ').J
      rw [axLimbReqsOf_congr b Pb.toPubJ9A hX, hJ.2.1, aS]
  refine ⟨?_, ?_⟩
  · unfold reqsAL; rw [hC, hE]
  · cases bl
    · exact RealIOJ8.provsT_congr b h Pb.toPubJ8 .x
    · exact RealIOJ8.provsT_congr b h Pb.toPubJ8 .p
    · show jProv b Pb.nodesJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0) Pb.lay (Q χ).J ++
          (pad8 (atomIncProvs b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) (Q χ).A) ++
            (if 1 ≤ Pb.krootsV then pad8 (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (fun _ => (0 : K)) (fun _ => 0)
              (Q χ).V) else []) ++
            ((if Pb.axOn then axTagProvsOf b Pb.toPubJ9A (Q χ).toTrJ9A else []) ++ aluPL δ b Pb (Q χ)) ++
            (if Pb.spOn then splitProvsOf b Pb.toPubJ9A (Q χ).toTrJ9A else [])) =
        jProv b Pb.nodesJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0) Pb.lay (Q χ').J ++
          (pad8 (atomIncProvs b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) (Q χ').A) ++
            (if 1 ≤ Pb.krootsV then pad8 (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (fun _ => (0 : K)) (fun _ => 0)
              (Q χ').V) else []) ++
            ((if Pb.axOn then axTagProvsOf b Pb.toPubJ9A (Q χ').toTrJ9A else []) ++ aluPL δ b Pb (Q χ')) ++
            (if Pb.spOn then splitProvsOf b Pb.toPubJ9A (Q χ').toTrJ9A else []))
      rw [hJ.2.2, hV.2, hA, axTagProvsOf_congr b Pb.toPubJ9A hX, splitProvsOf_congr b Pb.toPubJ9A hS, aP]

end Lists

/-! ## 3. The validity readout (#2) with the primitive pins and the ALU's validity reads -/

section Val
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (cVInt)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (pinRecsJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL (pinRecsP)
open Nock.NockVMROM.Thm54.VclL.Handle.ComapJ9A (stJ8_toJ8)

/-- **The ALU's validity reads**, gated on `aluOn` (`aluFpReqsOf` at the ALU challenge vector `chalsALJ8`). -/
def aluFpL (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) (χ : Coins frameJ8 K) : List (Fin 5 → 𝕂′) :=
  if Pb.aluOn then aluFpReqsOf δ b Pb tr (AluSZChipJ9.chalsALJ8 δ χ) else []

/-- **#2's requests on a J-9 AL trace**: the J-9 claim records and registry pins, then the primitive pins and the
ALU's validity reads (the consumer list of `AcceptsJ9AL.hsumC'`), then the cell table's internal consumers. -/
def valReqsAL (Pb : PubJ9AL p) (c : P8PublicClaim) (tr : TrJ9AL (ZMod p)) (χ : Coins frameJ8 K) :
    List (Fin 5 → 𝕂′) :=
  ((RealJ9.claimRecsT9 δ Pb.toPubJ8 c χ tr.toJ8 ++ pinRecsJ8 δ Pb.toPubJ8 χ) ++
      (pinRecsP δ Pb χ ++ aluFpL δ b Pb tr χ)) ++
    cVInt δ b Pb.nodesC Pb.orbitC (fun _ => (0 : K)) (fun _ => 0) (restrictQ 129 134 RealVJ8.shM tr.toJ8.M)

/-- **The ALU validity reads depend only on `z` (leaves `37 / 38`) and the ALU columns of rounds `0, 1`.** -/
theorem aluFp_congr (Pb : PubJ9AL p) (tr tr' : TrJ9AL (ZMod p)) (chals chals' : ℕ → K)
    (hL : ∀ j : Fin wAL, crAL j ≤ 1 → tr.L j = tr'.L j) (h37 : chals 37 = chals' 37) (h38 : chals 38 = chals' 38) :
    aluFpReqsOf δ b Pb tr chals = aluFpReqsOf δ b Pb tr' chals' := by
  unfold aluFpReqsOf
  refine List.flatMap_congr fun i _ => ?_
  have hF : ∀ j < 148, (alEF b Pb.nodesL Pb.orbitL chals (fun _ => (0 : K))
      (qAL δ b Pb tr chals (fun _ => (0 : K))) i).trace j =
      (alEF b Pb.nodesL Pb.orbitL chals' (fun _ => (0 : K)) (qAL δ b Pb tr' chals' (fun _ => (0 : K))) i).trace j := by
    intro j hj
    simp only [alEF]
    rw [envOfTrace_trace _ _ _ _ _ (by rw [AluSZChipJ9.aluSZ_width_eq]; omega),
      envOfTrace_trace _ _ _ _ _ (by rw [AluSZChipJ9.aluSZ_width_eq]; omega)]
    simp only [qAL]
    congr 1
    apply hL
    show crAL _ ≤ 1
    simp only [crAL, Fin.coe_cast]
    split_ifs <;> omega
  have hK : ∀ r < 18, (alEK δ b Pb.nodesL Pb.orbitL chals (fun _ => (0 : K))
      (qAL δ b Pb tr chals (fun _ => (0 : K))) i).trace r =
      (alEK δ b Pb.nodesL Pb.orbitL chals' (fun _ => (0 : K)) (qAL δ b Pb tr' chals' (fun _ => (0 : K))) i).trace r := by
    refine gather_trace_congr b _ (BK := 18) (fun r hr k hk => hF _ ?_)
    simp only [ChipTemplate.col0, AluSZChipJ9.aluTemplateSZ_baseCols]; omega
  have hc : ∀ j, (alEK δ b Pb.nodesL Pb.orbitL chals (fun _ => (0 : K))
      (qAL δ b Pb tr chals (fun _ => (0 : K))) i).chal j = chals j :=
    TeleH.gather_chal_T b (AluSZChipJ9.aluTemplateSZ δ) 94
      (AluSZChipJ9.aluTemplateSZ_baseCols δ) _ chals rfl
  have hc' : ∀ j, (alEK δ b Pb.nodesL Pb.orbitL chals' (fun _ => (0 : K))
      (qAL δ b Pb tr' chals' (fun _ => (0 : K))) i).chal j = chals' j :=
    TeleH.gather_chal_T b (AluSZChipJ9.aluTemplateSZ δ) 94 (AluSZChipJ9.aluTemplateSZ_baseCols δ) _ chals' rfl
  rw [hF AluSZChipJ9.aV (by decide)]
  split_ifs
  · rfl
  · refine List.singleton_inj.mpr ?_
    funext c
    fin_cases c
    · simp only [AluSZChipJ9.valKey, AtomChipHQ.zAt]
      simp only [Fin.zero_eta, Fin.isValue, Fin.val_zero, List.getD_cons_zero, ev_chal, hc, hc', h37, h38]
    · rfl
    · simp only [AluSZChipJ9.valKey]
      simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Fin.val_two, List.getD_cons_succ,
        List.getD_cons_zero, ev_var, hK AluSZChipJ9.L (by decide), hK (AluSZChipJ9.L + 1) (by decide)]
    · rfl
    · simp only [AluSZChipJ9.valKey]
      simp only [Fin.reduceFinMk, Fin.isValue, List.getD_cons_succ, List.getD_cons_zero, ev_base,
        CoeffExpr.eval, cv, hF AluSZChipJ9.sv (by decide)]

/-- **#2 reads below round `1`** (the J-9 part by `RealJ9.valJ9_reads`; the primitive pins through `encJ8`; the
ALU reads by `aluFp_congr`: `z` is a round-0 coin and `L` a round-1 column). -/
theorem valAL_reads (Pb : PubJ9AL p) (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q) :
    ReadsOnC frameJ8 (coinsBelow frameJ8 1) fun χ =>
      (valReqsAL δ b Pb c (Q χ) χ, RealVJ8.valProvsJ8 δ b Pb.toPubJ8 (Q χ).toJ8 χ) := by
  intro χ χ' hχ
  have hQ8 := stJ8_toJ8 (Q := fun χ => (Q χ).toTrJ9A) hQ.1
  have h8 := RealJ9.valJ9_reads δ b Pb.toPubJ8 c (fun χ => (Q χ).toJ8) hQ8 χ χ' hχ
  have h1 := congrArg Prod.fst h8
  have h2 := congrArg Prod.snd h8
  simp only at h1 h2
  refine Prod.ext ?_ h2
  simp only [RealJ9.valReqsJ9] at h1
  obtain ⟨h1a, h1b⟩ := List.append_inj h1
    (by simp [RealJ9.claimRecsT9, RealVJ8.claimRecsT, pinRecsJ8])
  have hE := RealVJ8.encJ8_congr δ hχ
  have hm : ∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → i ∈ coinsBelow frameJ8 1 := fun i hi => by
    simp only [coinsBelow, Finset.mem_filter, Finset.mem_univ, true_and, hi]; norm_num
  have hP : pinRecsP δ Pb χ = pinRecsP δ Pb χ' := by unfold pinRecsP; rw [hE]
  have hA : aluFpL δ b Pb (Q χ) χ = aluFpL δ b Pb (Q χ') χ' := by
    unfold aluFpL
    split_ifs
    · refine aluFp_congr δ b Pb _ _ _ _ (fun j hj => staged_eq hQ.2 (r := 1) (below_of_mem hχ) j hj) ?_ ?_
      · rw [AluSZChipJ9.chalsALJ8_of_lt δ χ (by norm_num), AluSZChipJ9.chalsALJ8_of_lt δ χ' (by norm_num)]
        simp only [ChalsAZJ8.chalsAJ8Z, if_pos rfl]; exact hχ c2 (hm _ (by decide))
      · rw [AluSZChipJ9.chalsALJ8_of_lt δ χ (by norm_num), AluSZChipJ9.chalsALJ8_of_lt δ χ' (by norm_num)]
        simp only [ChalsAZJ8.chalsAJ8Z, if_neg (show (38 : ℕ) ≠ 37 by decide), if_pos rfl]
        exact hχ c3 (hm _ (by decide))
    · rfl
  show ((_ ++ _) ++ (_ ++ _)) ++ _ = ((_ ++ _) ++ (_ ++ _)) ++ _
  rw [h1a, h1b, hP, hA]

end Val

/-! ## 4. The J-9 AL datum, the `arithSZ` summand, the list, the probability statement -/

section Data
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ9AL} {P g₀ : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.ComapJ9A (stJ8_toJ8)

/-- **The J-9 AL datum** from any J-9 A datum `X` at `rowsB r`: pulled back along `toTrJ9A`, re-indexed to
`rowsBL r` and `gL r g` (only #2's, #5's and #6's budgets read the moved fields), with #2 at `valReqsAL`, #5 at
`reqsAL .x` / `provsAL .x` and #6 at `reqsAL .s` / `provsAL .s`.  #1, #3, #4, #7–#11 are `X`'s along `toTrJ9A`. -/
def XAL (X : DataJ8X (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A
      (RR49A.rowsB r.toRowsJ9A) P g₀) (Pb : PubJ9AL p) (c : P8PublicClaim) (g : ℕ) :
    DataJ8X (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9AL (ZMod p)) StJ9AL (rowsBL r) P (gL r g) where
  C :=
    { D :=
      { Tr40 := X.C.D.Tr40
        St40 := X.C.D.St40
        l40 := X.C.D.l40
        π40 := fun tr => X.C.D.π40 tr.toTrJ9A
        hπ40 := fun Q' hQ' y₁ y₂ => X.C.D.hπ40 _ hQ'.1 y₁ y₂
        eps40 := X.C.D.eps40
        valReqs := fun tr χ => valReqsAL δ b Pb c tr χ
        valProvs := fun tr χ => RealVJ8.valProvsJ8 δ b Pb.toPubJ8 tr.toJ8 χ
        val_reads := fun Q hQ => valAL_reads δ b Pb c Q hQ
        avReqs := fun tr χ => X.C.D.avReqs tr.toTrJ9A χ
        avProvs := fun tr χ => X.C.D.avProvs tr.toTrJ9A χ
        av_reads := fun Q hQ => X.C.D.av_reads _ hQ.1
        axReqs := fun tr χ => X.C.D.axReqs tr.toTrJ9A χ
        axProvs := fun tr χ => X.C.D.axProvs tr.toTrJ9A χ
        ax_reads := fun Q hQ => X.C.D.ax_reads _ hQ.1
        cxReqs := fun tr _ => reqsAL δ b Pb tr .x
        cxProvs := fun tr _ => liftP (provsAL δ b Pb tr .x)
        cx_reads := fun Q hQ χ χ' _ => by
          obtain ⟨h1, h2⟩ := listsAL_const δ b Pb hQ χ χ' .x
          simp only [h1, h2]
        svReqs := fun tr _ => reqsAL δ b Pb tr .s
        svProvs := fun tr _ => effP (liftP (provsAL δ b Pb tr .s))
        sv_reads := fun Q hQ χ χ' _ => by
          obtain ⟨h1, h2⟩ := listsAL_const δ b Pb hQ χ χ' .s
          simp only [h1, h2]
        rowsA := fun tr => X.C.D.rowsA tr.toTrJ9A
        skelA := fun tr => X.C.D.skelA tr.toTrJ9A
        rowsA_le := fun tr => X.C.D.rowsA_le tr.toTrJ9A
        skelA_le := fun tr => X.C.D.skelA_le tr.toTrJ9A
        rowsA_const := fun Q hQ => X.C.D.rowsA_const _ hQ.1
        wdA := fun tr χ => X.C.D.wdA tr.toTrJ9A χ
        wdA_le := fun tr χ => X.C.D.wdA_le tr.toTrJ9A χ
        wdA_reads := fun Q hQ => X.C.D.wdA_reads _ hQ.1
        prs := fun tr => X.C.D.prs tr.toTrJ9A
        prs_le := fun tr => X.C.D.prs_le tr.toTrJ9A
        prs_const := fun Q hQ => X.C.D.prs_const _ hQ.1 }
      wdC := fun tr χ => X.C.wdC tr.toTrJ9A χ
      wdC_le := fun tr χ => X.C.wdC_le tr.toTrJ9A χ
      wdC_reads := fun Q hQ => X.C.wdC_reads _ hQ.1 }
  vxReqs := fun tr χ => X.vxReqs tr.toTrJ9A χ
  vxProvs := fun tr χ => X.vxProvs tr.toTrJ9A χ
  vx_reads := fun Q hQ => X.vx_reads _ hQ.1

/-! ### The readouts of `XAL` (definitional) -/

theorem rdV_AL (X : DataJ8X (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A
      (RR49A.rowsB r.toRowsJ9A) P g₀) (Pb : PubJ9AL p) (c : P8PublicClaim) (g : ℕ) (tr : TrJ9AL (ZMod p))
    (χ : Coins frameJ8 K) :
    (XAL δ b X Pb c g).C.D.valReqs tr χ = valReqsAL δ b Pb c tr χ ∧
      (XAL δ b X Pb c g).C.D.valProvs tr χ = RealVJ8.valProvsJ8 δ b Pb.toPubJ8 tr.toJ8 χ := ⟨rfl, rfl⟩

theorem rdX_AL (X : DataJ8X (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A
      (RR49A.rowsB r.toRowsJ9A) P g₀) (Pb : PubJ9AL p) (c : P8PublicClaim) (g : ℕ) (tr : TrJ9AL (ZMod p))
    (χ : Coins frameJ8 K) :
    (XAL δ b X Pb c g).C.D.cxReqs tr χ = reqsAL δ b Pb tr .x ∧
      (XAL δ b X Pb c g).C.D.cxProvs tr χ = liftP (provsAL δ b Pb tr .x) := ⟨rfl, rfl⟩

theorem rdS_AL (X : DataJ8X (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A
      (RR49A.rowsB r.toRowsJ9A) P g₀) (Pb : PubJ9AL p) (c : P8PublicClaim) (g : ℕ) (tr : TrJ9AL (ZMod p))
    (χ : Coins frameJ8 K) :
    (XAL δ b X Pb c g).C.D.svReqs tr χ = reqsAL δ b Pb tr .s ∧
      (XAL δ b X Pb c g).C.D.svProvs tr χ = effP (liftP (provsAL δ b Pb tr .s)) := ⟨rfl, rfl⟩

/-! ### The `arithSZ` readouts: the ALU's and the atom table's round-0 rows, at `q = Nock.Atoms.p` (`AluSZEvent`/`AluSZOps`'s `q`) -/

/-- A round-0 atom row read at another modulus (the two `ZMod` fields through `val`). -/
def reB0 {q : ℕ} (q' : ℕ) (c : CellRowB0 q) : CellRowB0 q' :=
  { c with aL := ((c.aL.val : ℕ) : ZMod q'), aR := ((c.aR.val : ℕ) : ZMod q') }

/-- **The ALU's round-0 rows** (base columns `< 94` of the coin-free row environment, through `natOf`, at
`Nock.Atoms.p`), truncated at the ALU row budget. -/
def aluAL (r : RowsJ9AL) (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) : List (AluSZEvent.ARow Nock.Atoms.p) :=
  (List.ofFn fun i : Fin Pb.nL => fun j =>
    if j < 94 then ((natOf ((alE0 (K := K) δ b Pb tr i).trace j) : ℕ) : ZMod Nock.Atoms.p) else 0).take r.AL

/-- **The atom table's round-0 rows** (`rowsAJ8`, at `Nock.Atoms.p`), truncated at the atom row budget. -/
def atomAL (r : RowsJ9AL) (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) : List (CellRowB0 Nock.Atoms.p) :=
  ((TraceJ8.rowsAJ8 Pb.nodesA Pb.orbitA tr.toJ8).map (reB0 Nock.Atoms.p)).take r.A

theorem aluAL_length_le (r : RowsJ9AL) (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) :
    (aluAL (K := K) δ b r Pb tr).length ≤ r.AL := by
  unfold aluAL; simp

theorem atomAL_length_le (r : RowsJ9AL) (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) :
    (atomAL r Pb tr).length ≤ r.A := by
  unfold atomAL; simp

theorem hdrsAL_le (r : RowsJ9AL) (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) :
    (AluSZEvent.hdrs (aluAL (K := K) δ b r Pb tr)).length ≤ r.AL :=
  (AluSZEvent.hdrs_length_le _).trans (aluAL_length_le δ b r Pb tr)

theorem arithAL_const (r : RowsJ9AL) (Pb : PubJ9AL p) {Q : Coins frameJ8 K → TrJ9AL (ZMod p)} (hQ : StJ9AL Q)
    (χ χ' : Coins frameJ8 K) :
    aluAL (K := K) δ b r Pb (Q χ) = aluAL (K := K) δ b r Pb (Q χ') ∧ atomAL r Pb (Q χ) = atomAL r Pb (Q χ') := by
  refine ⟨?_, ?_⟩
  · have hL : ∀ j : Fin wAL, crAL j = 0 → (Q χ).L j = (Q χ').L j :=
      fun j hj => staged_eq hQ.2 (r := 0) (fun i hi => absurd hi (by omega)) j hj.le
    unfold aluAL
    congr 2
    funext i j
    split_ifs with hj
    · rw [alTrace_congr (K := K) δ b Pb hL i j hj]
    · rfl
  · unfold atomAL
    rw [TraceJ8.rowsAJ8_const Pb.nodesA Pb.orbitA (fun χ => (Q χ).toJ8) (stJ8_toJ8 (Q := fun χ => (Q χ).toTrJ9A) hQ.1)
      χ χ']

/-- **The arithmetic SZ summand of J-9 AL** (`AluSZEvent`'s per-call `arithSZ` at `C = AL`, `A`, `AL`; coins `{17, 18}`). -/
def arithAL (r : RowsJ9AL) (Pb : PubJ9AL p) : BadSummand frameJ8 K (TrJ9AL (ZMod p)) StJ9AL :=
  AluSZEvent.arithSZ (q := Nock.Atoms.p) (algebraMap (ZMod p) K δ) StJ9AL (aluAL (K := K) δ b r Pb) (atomAL r Pb)
    r.AL r.A r.AL (hdrsAL_le δ b r Pb) (atomAL_length_le r Pb) (aluAL_length_le δ b r Pb)
    (fun Q hQ χ χ' => arithAL_const δ b r Pb hQ χ χ')

/-- **The J-9 AL summand list**: `XAL`'s (#1–#11) and `arithSZ`. -/
def allJ9AL (X : DataJ8X (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A
      (RR49A.rowsB r.toRowsJ9A) P g₀) (Pb : PubJ9AL p) (c : P8PublicClaim) (g : ℕ) :
    List (BadSummand frameJ8 K (TrJ9AL (ZMod p)) StJ9AL) :=
  allJ8X (XAL δ b X Pb c g) ++ [arithAL δ b r Pb]

/-- **`ε` of the J-9 AL list is `boundJ9AL`.** -/
theorem epsilon_allJ9AL (X : DataJ8X (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A
      (RR49A.rowsB r.toRowsJ9A) P g₀) (Pb : PubJ9AL p) (c : P8PublicClaim) (g : ℕ) :
    epsilonOf (allJ9AL δ b X Pb c g) = boundJ9AL (Fintype.card K) (Fintype.card 𝕂′) r P g := by
  rw [allJ9AL, WeightsJ8.epsilonOf_append, epsilon_allJ8X, eps_single]
  have hw : (arithAL δ b r Pb (K := K)).weight = wSZ r := rfl
  have hn : (arithAL δ b r Pb (K := K)).coins.card = 2 := Finset.card_pair (by decide)
  rw [hw, hn, boundJ9AL]

/-- Outside the J-9 AL list: outside `XAL`'s list and outside `arithSZ`. -/
theorem outside_allJ9AL (X : DataJ8X (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A
      (RR49A.rowsB r.toRowsJ9A) P g₀) (Pb : PubJ9AL p) (c : P8PublicClaim) (g : ℕ) {tr : TrJ9AL (ZMod p)}
    {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ9AL δ b X Pb c g, ¬ s.mem tr χ) :
    (∀ s ∈ allJ8X (XAL δ b X Pb c g), ¬ s.mem tr χ) ∧ ¬ (arithAL δ b r Pb).mem tr χ :=
  ⟨fun s hs => h s (List.mem_append_left _ hs), h _ (List.mem_append_right _ (List.mem_singleton_self _))⟩

open Classical in
/-- **The J-9 AL probability statement**: `Pr[accept ∧ ¬ target] < 2^-155` for any soundness core `hsound` that
concludes the target outside the J-9 AL list, below the census corner. -/
theorem probJ9AL_lt_155 (X : DataJ8X (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A
      (RR49A.rowsB r.toRowsJ9A) P g₀) (Pb : PubJ9AL p) (c : P8PublicClaim) (g : ℕ)
    (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q) (Acc : Coins frameJ8 K → Prop) (Holds : Prop)
    (hsound : ∀ χ, Acc χ → (∀ s ∈ allJ9AL δ b X Pb c g, ¬ s.mem (Q χ) χ) → Holds)
    (hcK : Fintype.card K = cK) (h : RowsLe r.toRowsJ8 cornerC) (hAX : r.AX ≤ 2 ^ 31) (hSP : r.SP ≤ 2 ^ 31)
    (hAL : r.AL ≤ 2 ^ 31) (hP : P ≤ 2 ^ 66) (hg : g ≤ 2 ^ 31) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K => Acc χ ∧ ¬ Holds).card : ℚ) /
        Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 := by
  refine lt_of_le_of_lt (prob_le_of_outside _ Q hQ Acc Holds hsound) ?_
  rw [epsilon_allJ9AL, quad_card, hcK]
  exact figJ9AL_155 h hAX hSP hAL hP hg

end Data

end

end Nock.NockVMROM.Thm54.VclL.Handle.RR49AL

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.RR49AL
#print axioms numJ9AL_le_P4
#print axioms figJ9AL_155
#print axioms listsAL_const
#print axioms aluFp_congr
#print axioms valAL_reads
#print axioms XAL
#print axioms arithAL
#print axioms epsilon_allJ9AL
#print axioms probJ9AL_lt_155
end Axioms
