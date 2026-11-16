/-
  Nock/RedTeam/Batch782Thm54U1Sound.lean

  **U1 pre-greenlight, Q2: U1 (`topPin := top − P·lm₂·lm₁·lm₀`, a replica here, NOT
  the deployed pin) is SOUND for the shift at every width, with no hypothesis on the field.**

  * `shift_le_nMinus1Low` / `shift_le_formRN_pred`: boolean shift bits + `pPin` + U1 + the
    deployed `rangeGate` ⇒ `rowShift ≤ formRN − 1`.
-/
import Nock.RedTeam.Batch781Thm54U1Reproduce
import Nock.NockVMROM.Thm54.P8Core.Batch782Thm54U1Sound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Nock.RedTeam.Batch782

open scoped Classical
open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.CoordinateCompiler

variable {F : Type*} [Field F]

theorem topPinU1_degree : (topPinU1 (F := F)).degree ≤ 4 := by
  simp [topPinU1, CoeffExpr.degree, lm_degree]


open Nock.RedTeam.Batch781 in
/-- The scope's `p = 769` row (shift `63`, `top = 1`) FAILS the U1 pin: the bit-matched top of
`63` against `n − 1 = 9` is `0`. -/
theorem u1_rejects_row769 : (topPinU1 (F := F769)).eval row769 ≠ 0 := by
  rw [topPinU1_eval, row769, rowEnv_top, rowEnv_P,
    rowEnv_lm _ _ _ _ _ _ 2 (by decide), rowEnv_lm _ _ _ _ _ _ 1 (by decide),
    rowEnv_lm _ _ _ _ _ _ 0 (by decide)]
  have h1 : matchedLm F769 63 1 = 0 := by
    simp only [matchedLm, nMinus1Bit, formRN_769]
    rw [if_neg (by decide), show Nat.testBit 63 1 = true by decide]; simp
  rw [h1]; simp

open Nock.RedTeam.Batch781 in
/-- `cert_ambiguous_31`'s axis-`34` row FAILS the U1 pin (`5 ≠ n − 1 = 4`). -/
theorem u1_rejects_row31 : (topPinU1 (F := F31)).eval row31 ≠ 0 := by
  rw [topPinU1_eval, row31, rowEnv_top, rowEnv_P,
    rowEnv_lm _ _ _ _ _ _ 2 (by decide), rowEnv_lm _ _ _ _ _ _ 1 (by decide),
    rowEnv_lm _ _ _ _ _ _ 0 (by decide)]
  have h0 : matchedLm F31 5 0 = 0 := by
    simp [matchedLm, nMinus1Bit, formRN_31]
  rw [h0]; simp

open Nock.RedTeam.Batch781 in
/-- The decoded shift of the scope's row is `63`, out of range at `n = 10`. -/
theorem row769_shift : rowShift row769 = 63 := by
  unfold rowShift
  have h : ∀ k ∈ Finset.range 6, row769.trace (265 + k) = 1 := fun k hk => by
    have hk' := Finset.mem_range.mp hk
    have := rowEnv_m ((2 : F769) ^ 63) (certCBit (2 ^ 63)) 63 (matchedP F769 63) 1
      (fun k => 1 * certEqRun (2 ^ 63) (3 * (k + 1))) k hk'
    simp only [col0] at this
    rw [show 265 + k = 202 + 63 + k by omega, row769, this]
    interval_cases k <;> decide
  rw [Finset.sum_congr rfl (fun k hk => by rw [if_pos (h k hk)])]
  decide


section Decoded

variable {K : Type} [Field K] {N : ℕ}

noncomputable def computeArity (env : Env K) : ℕ :=
  1 + (if env.trace 0 + (env.trace 2 + (env.trace 5 + (env.trace 6 + (env.trace 7 +
          (env.trace 8 + env.trace 9))))) = 1 then 1 else 0)
    + (if env.trace 6 + env.trace 9 = 1 then 1 else 0)

noncomputable def computePrefix (envsC : Fin N → Env K) (i : Fin N) : ℕ :=
  ∑ i' ∈ Finset.univ.filter (fun i' : Fin N => i'.val < i.val), computeArity (envsC i')

noncomputable def locateExp (envsC : Fin N → Env K) (e : ℕ) : Option (Fin N × ℕ) :=
  ((List.finRange N).find? fun i =>
      decide (computePrefix envsC i < e ∧ e ≤ computePrefix envsC i + computeArity (envsC i))).map
    fun i => (i, e - computePrefix envsC i - 1)

noncomputable def rowBits (env : Env K) (k : ℕ) : Bool :=
  decide (1 ≤ k ∧ k ≤ 63 ∧ env.trace (202 + (k - 1)) = 1)

noncomputable def slotCert (envsC : Fin N → Env K) (i : Fin N) (j : ℕ) : ℕ × (ℕ → Bool) :=
  match j with
  | 0 => (1, fun k => decide (k = 1))
  | 1 => if (envsC i).trace 0 = 1 then (rowShift (envsC i), rowBits (envsC i))
         else (1, fun _ => false)
  | _ => if (envsC i).trace 9 = 1 then (rowShift (envsC i), rowBits (envsC i))
         else (1, fun _ => false)

noncomputable def decodedShift (envsC : Fin N → Env K) (e : ℕ) : ℕ :=
  match locateExp envsC e with
  | some (i, j) => (slotCert envsC i j).1
  | none => 0

/-- **The `CertInRange` source U1 delivers for Part 2** (shift form, `FormRAxisEvent.CertInRange`
at `decodedShift`): on compute rows that satisfy the U1 gate set, every decoded shift — row slots
and the C-a constant slots (shift `1`) alike — is `≤ formRN − 1`.  `2 ≤ formRN` is `hp`'s
fragment (`25 ≤ p ⇒ formRN ≥ 5`).  At `64 ≤ formRN` this was width arithmetic
(`CensusNamesFormR.decodedShift_in_range`); below `64` it needs the U1 pin. -/
theorem decodedShift_in_range_of_U1 (envsC : Fin N → Env K) (hn : 2 ≤ formRN K)
    (hb : ∀ i, ∀ k, k < 6 → (bbool (colM (F := K) k)).eval (envsC i) = 0)
    (hp : ∀ i, (pPin (F := K)).eval (envsC i) = 0)
    (ht : ∀ i, (topPinU1 (F := K)).eval (envsC i) = 0)
    (hr : ∀ i, (rangeGate (F := K)).eval (envsC i) = 0) :
    ∀ e, decodedShift envsC e ≤ formRN K - 1 := by
  intro e
  have hrow : ∀ i, rowShift (envsC i) ≤ formRN K - 1 := fun i =>
    shift_le_formRN_pred (envsC i) (hb i) (hp i) (ht i) (hr i)
  unfold decodedShift
  split
  · rename_i i j _
    unfold slotCert
    split
    · simp only; omega
    · split_ifs
      · exact hrow i
      · simp only; omega
    · split_ifs
      · exact hrow i
      · simp only; omega
  · omega

end Decoded

end Nock.RedTeam.Batch782

#print axioms Nock.RedTeam.Batch782.shift_le_nMinus1Low
#print axioms Nock.RedTeam.Batch782.shift_le_formRN_pred
#print axioms Nock.RedTeam.Batch782.decodedShift_in_range_of_U1
#print axioms Nock.RedTeam.Batch782.u1_rejects_row769
#print axioms Nock.RedTeam.Batch782.u1_rejects_row31
#print axioms Nock.RedTeam.Batch782.row769_shift
