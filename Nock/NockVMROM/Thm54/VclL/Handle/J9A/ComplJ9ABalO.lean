/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalO.lean

  **J-9 A L7 balance: the six balance fields of `ComplJ9AObligations` at `BRun9A`**
  (`hGx hsumC' hbalA' hvalA0 hfxC hfxA`), verbatim forms, assembled from the pieces
  `ComplJ9ABalG1.hGx_A_of` (+ `BalW.hslotA/hrootA`, `BalCR.hC_runA`, `BalJ.hJA_A`, `BalR.hrangeA_of`),
  `BalGen.hfxC_A_of`, `BalGen.hvalA0_A`, `BalFA.hfxA_A`, `BalV1.hsumC'_A`, `BalV2.hbalA_A_of`. -/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalG1
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalGen
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalJ
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalR
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalCR
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalFA
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalV1
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalV2
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalO

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf readsA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (WalkDepthOK9A ProgAxOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (rowsOfT9)

noncomputable section

section J9A
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen))

local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DD" => j8DataOf p Rg Rt hgen
local notation "BA" => BRun9A δ b Rt hgen hpG h31A

set_option maxHeartbeats 1000000 in
/-- **`hGx` at `BRun9A`** (field verbatim). -/
theorem hGx_A (hax9 : ProgAxOK9A p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (hsub : ComplJ9ABalCR.Sub9 (p := p) Rt hgen)
    (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hrowsA : ∀ l ∈ (rowsOfT9 t).toList,
      (l.chip = .old → HonestCompX.RowOKX p l.rn) ∧
      (l.chip = .old → l.rn.st = .s3 → l.rn.sf1.isCell = true → l.rn.sf1 = .cell l.rn.ftth l.rn.fttt) ∧
      ∀ k < 12, (HonestCompX.hN l.rn k).isCell = true → HonestCompX.hN l.rn k ∈ (DA).cells) :
    ∀ χ, (BA).Good χ → ((BA).M χ).ρ 3 + (Quad.mk _ (((BA).M χ).pubsW WalkHQ.pubXQ)
        (((BA).M χ).pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (((BA).M χ).pubsJ 2) (((BA).M χ).pubsJ 3)) =
      Quad.mk _ (((BA).M χ).pubsC CellHQ.pubHQ) (((BA).M χ).pubsC (CellHQ.pubHQ + 1)) := by
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hmC : (DA).cells.length ∈ sizesJ8 (DA) := by simp [sizesJ8]
  have hlen : (DA).cells.length < p := by
    have h1 := rows31_of_A h31A (DA).cells.length hmC
    have : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
    omega
  have hkN : ∀ x ∈ (DD).jrows, (x.pre.kd = .rp ∨ x.pre.kd = .sl ∨ x.pre.kd = .sr) → x.w.kN = 1 :=
    fun x hx => (Nock.Jet.ChipJ8.gate_facts x (ComplJ8Jet.jrows_gate_run Rt hgen hp0 hRt x hx)).2.2.2
  have hwcellA : ∀ u ∈ walkRows (DA).cells (DA).reads, u.label.node ∈ (DA).cells :=
    ComplJ9ABalGen.walkRows_node_cells_gen _ _ (ComplJ8Data.cells_closed _)
      (ComplJ9ADataRec.cellsA_pos Rt hgen) (ComplJ9ABalW.hslotA hgen) (ComplJ9ABalW.hrootA hgen)
  exact ComplJ9ABalG1.hGx_A_of δ b Rt hgen hpG h31A hwalk9 hwcellA
    (ComplJ9ABalCR.hC_runA δ b Rt hgen hpG h31A hax9 hop5 hsub)
    (fun χ _ => ComplJ9ABalJ.hJA_A δ b Rt hgen hpG h31A hRt χ)
    (ComplJ9ABalR.hrangeA_of p Rg Rt hgen hwalk9 hwcellA hlen hkN hrowsA)

/-- **`hsumC'` at `BRun9A`** (field verbatim). -/
theorem hsumC_A :
    ∀ χ, (BA).Good χ →
    ((ClaimJ9.claimRecsJ9 δ χ (ComplJ8.cJ s f r) ((BA).M χ).m ++
        AcceptsJ8P.pinRecsJ8 δ (BA).Pb.toPubJ8 χ).map fun x => (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6), Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      Quad.mk (algebraMap (ZMod p) K δ) (((BA).M χ).pubsC 0) (((BA).M χ).pubsC 1) +
        Quad.mk (algebraMap (ZMod p) K δ) (((BA).M χ).pubsA AtomChipHQ.pubMB)
          (((BA).M χ).pubsA (AtomChipHQ.pubMB + 1)) :=
  ComplJ9ABalV1.hsumC'_A δ b Rt hgen hpG h31A

/-- **`hbalA'` at `BRun9A`** (field verbatim). -/
theorem hbalA_A (hax9 : ProgAxOK9A p t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads) :
    ∀ χ, (BA).Good χ →
      Quad.mk (algebraMap (ZMod p) K δ) (((BA).M χ).pubsA CellHQ.pubHQ) (((BA).M χ).pubsA (CellHQ.pubHQ + 1)) =
        Quad.mk (algebraMap (ZMod p) K δ) (((BA).M χ).pubsA AtomChipHQ.pubC)
            (((BA).M χ).pubsA (AtomChipHQ.pubC + 1)) +
          Quad.mk (algebraMap (ZMod p) K δ) (((BA).M χ).pubsV WalkHQ.pubXQ)
            (((BA).M χ).pubsV (WalkHQ.pubXQ + 1)) :=
  ComplJ9ABalV2.hbalA_A_of δ b Rt hgen hpG h31A hax9 hwalkA (ComplJ9ABalFA.hallA_A Rt hgen hpG)
    (ComplJ9ABalFA.hwA_A Rt hgen hpG)

/-- **`hvalA0` at `BRun9A`** (field verbatim). -/
theorem hvalA0_A' : ∀ χ, (BA).Good χ → ((BA).M χ).pubsA 0 = 0 ∧ ((BA).M χ).pubsA 1 = 0 :=
  ComplJ9ABalGen.hvalA0_A δ b Rt hgen hpG h31A

/-- **`hfxC` at `BRun9A`** (field verbatim). -/
theorem hfxC_A' (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t)) :
    ∀ χ, (BA).Good χ → ((BA).M χ).pubsC 2 = ((BA).M χ).pubsW 0 ∧ ((BA).M χ).pubsC 3 = ((BA).M χ).pubsW 1 :=
  ComplJ9ABalGen.hfxC_A_of δ b Rt hgen hpG h31A hwalk9 (ComplJ9ABalW.hslotA hgen) (ComplJ9ABalW.hrootA hgen)

/-- **`hfxA` at `BRun9A`** (field verbatim). -/
theorem hfxA_A' (hax9 : ProgAxOK9A p t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads) :
    ∀ χ, (BA).Good χ → ((BA).M χ).pubsA 2 = ((BA).M χ).pubsV 0 ∧ ((BA).M χ).pubsA 3 = ((BA).M χ).pubsV 1 :=
  ComplJ9ABalFA.hfxA_A δ b Rt hgen hpG h31A hax9 hwalkA

end J9A

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalO

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalO
#print axioms hGx_A
#print axioms hsumC_A
#print axioms hbalA_A
#print axioms hvalA0_A'
#print axioms hfxC_A'
#print axioms hfxA_A'
end Axioms
