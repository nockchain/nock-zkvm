/-
**`nock_e2e_J9AL_numbers`**, the numeric corollary of `nock_e2e_J9AL_succinct`.  Twin of `nock_e2e_J9AL_numbers`
(J9A/E2ESuccinctNum.lean) with `famJ9A` replaced by `famJ9AL`: the proof uses only `shapeOkF` unfolding and generic lemmas.  Any bound
`P <= 2^-82 + (bfriErr + mcROM + coll)` at an instance with `shapeOkF famJ9AL XI` (so `l = 170`, `nD = k + 7 <= 32`), `theta = delta = 31/64`,
`Q_FSf, Q_Hf <= 2^64`, `Vf <= 2^32`, `T <= 2^40` gives `P <= 2^-82 + (2^-83 + 2^-120)`.  NOT zero-knowledge.  Cite it together with a witness that its binders are satisfiable (for the release headlines: J9AL/E2ESuccinctNonVacL.lean, Z38 jp_witness).
-/
import NockvmE2E.Exec.HFixNum
import NockvmE2E.Exec.VKBindBridge
import NockvmE2E.Exec.E2EJ8P
import NockvmE2E.Exec.ShapeF
import NockvmE2E.Exec.J9ALChipsFam
open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal
set_option autoImplicit false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.J9AL.E2ESuccinctNumJ9AL
open NockvmE2E.Exec NockvmE2E.Exec.ShapeF NockvmE2E.Exec.V NockvmE2E.Exec.J9AChips NockvmE2E.Exec.J9ALChips NockvmE2E.Merkle.SideMerkle

/-- **`nock_e2e_J9AL_numbers`**: `P ≤ 2⁻⁸² + (bfriErr + mcROM + coll)` ⟹ `P ≤ 2⁻⁸² + (2⁻⁸³ + 2⁻¹²⁰)` at `Q ≤ 2^64`, `V ≤ 2^32`, `T ≤ 2^40` -/
theorem nock_e2e_J9AL_numbers [SampleableType KC] (XI : ExecInst) (hsh : shapeOkF famJ9AL XI = true) (P : ℝ≥0∞) (m : ℕ) (hm : m + 1 ≤ 2 ^ 12)
    (Q_FSf Q_Hf Vf Pf T : ℕ) (hQFS : Q_FSf ≤ 2 ^ 64) (hQH : Q_Hf ≤ 2 ^ 64) (hV : Vf ≤ 2 ^ 32) (hT : T ≤ 2 ^ 40)
    (h : P ≤ (2 ^ 82 : ℝ≥0∞)⁻¹ +
      (bfriErr (ω := smoothDomain XI.nD (hn32_of_shapeF hsh)) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (31 / 64 : ℝ) (31 / 64 : ℝ≥0)
          ((m * ((2 ^ XI.nD : ℝ≥0) / Fintype.card KC) : ℝ≥0)) Q_FSf +
        (MerkleTreeMultiExtractability.multiCheckpointROMErrorNumerator ((XI.k * (Q_FSf + 1)) * Pf) (XI.k * (Q_FSf + 1)) Vf Q_Hf : ℝ≥0∞) *
          (Nat.card E2E.DgJ8 : ℝ≥0∞)⁻¹ +
        ((Q_Hf + Vf + T) ^ 2 : ℝ≥0∞) / (2 * (Nat.card E2E.DgJ8 : ℝ≥0∞)))) :
    P ≤ (2 ^ 82 : ℝ≥0∞)⁻¹ + ((2 ^ 83 : ℝ≥0∞)⁻¹ + (2 ^ 120 : ℝ≥0∞)⁻¹) := by
  have hl : XI.l = 170 := hl_of_shapeF hsh
  have hn32 : XI.nD ≤ 32 := hn32_of_shapeF hsh
  have hnD : XI.nD = XI.k + 7 := by
    have h0 := hsh
    unfold shapeOkF at h0
    simp only [Bool.and_eq_true, beq_iff_eq] at h0
    omega
  have hk61 : XI.k ≤ 61 := by omega
  have hA := NockvmE2E.Exec.V.bfriErr_numbers (F := KC) (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+))
    (fun _ => rfl) 1 (by simp [hnD, pow_add, pow_succ]; omega) hn32 NockvmE2E.Exec.E2EJ8P.hF_X m hm Q_FSf hQFS
  rw [hl] at h
  exact h.trans (add_le_add le_rfl (NockvmE2E.Exec.V.epsfix_numbers _ 0 hA Q_Hf Vf XI.k Q_FSf Pf T hQH hV hT hk61 hQFS
    NockvmE2E.Exec.VKBindBridge.DgJ8_ge))

end NockvmE2E.J9AL.E2ESuccinctNumJ9AL

#print axioms NockvmE2E.J9AL.E2ESuccinctNumJ9AL.nock_e2e_J9AL_numbers
