/-
  Nock/RedTeam/Batch733Thm54DecodedLambdaSlotMapReadSet.lean

  **The thirty-second move's slot map (C-a) and read set (C-b), lane
  `lambda-consumer-32nd`.**  Receipts; no production edit.

  * **C-a, the slot→certificate map** (`slotCert_*`): slot `0` is the constant certificate
    `(shift 1, {c₁})`; slot `1` is the row's certificate `(rowShift, rowBits)` iff `trace 0 = 1`, else
    the constant `(shift 1, ∅)`; slot `2` is the row's certificate iff `trace 9 = 1`, else `(shift 1, ∅)`
    (in particular under selector `6`).  The constants' Form R polynomials are the deployed records'
    constants (`Batch747.sampledSlotT_structure` / `sampledSlotC_structure`): `Tpoly 1 = Y` (`T = λ`),
    `C'poly n (shift-1 cert {c₁}) = Y^{n−1} + Y^{n−2}` (`sampledSlotC 67 = lamPowVar 0 + lamPowVar 1`)
    and `C'poly n ∅ = Y^{n−1}` (`lamPowVar 0`, the `G`/selector-`6` arms of bases `75`/`83`).
  * **C-b and the round-0 read set** (`event_readSet`): two env tuples that agree on compute source
    columns `0..9` and `202..270` and on memory base columns `0..2` and `181` give the SAME decoded
    event, whatever their other columns, their challenge components, and the memory `𝕂` envs.  So no
    `𝕂` role and no challenge is read (`event_ignores_envsK`).  Both chips' round-0 columns: the
    compute selectors and certificate block (`202..264` bits, `265..270` shift), the memory selectors
    and `reqIdx` (`OptimizedMemoryGateBasis.reqIdxCol = 181`, `reqIdxCol_eq`).
-/
import Nock.NockVMROM.Thm54.DecodedLambdaEvent
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.P8Core.Batch733Thm54DecodedLambdaSlotMapReadSet

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch733

open scoped Classical Polynomial
open Nock Nock.Reified Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.RedTeam.Batch575
open Polynomial

noncomputable section

/-! ## C-a -/

section SlotMap
variable {K : Type} [Field K] {N : ℕ} (envsC : Fin N → Env K) (i : Fin N)

theorem slotCert_zero : slotCert envsC i 0 = (1, fun k => decide (k = 1)) := rfl

theorem slotCert_one_of_s0 (h : (envsC i).trace 0 = 1) :
    slotCert envsC i 1 = (rowShift (envsC i), rowBits (envsC i)) := by
  simp [slotCert, h]

theorem slotCert_one_of_not_s0 (h : (envsC i).trace 0 ≠ 1) :
    slotCert envsC i 1 = (1, fun _ => false) := by
  simp [slotCert, h]

theorem slotCert_two_of_s9 (h : (envsC i).trace 9 = 1) :
    slotCert envsC i 2 = (rowShift (envsC i), rowBits (envsC i)) := by
  simp [slotCert, h]

theorem slotCert_two_of_not_s9 (h : (envsC i).trace 9 ≠ 1) :
    slotCert envsC i 2 = (1, fun _ => false) := by
  simp [slotCert, h]

/-- Selector `6` without selector `9` (one-hot rows): slot `2` is the axis-2 constant. -/
theorem slotCert_two_of_s6 (_h6 : (envsC i).trace 6 = 1) (h9 : (envsC i).trace 9 = 0) :
    slotCert envsC i 2 = (1, fun _ => false) := by
  have : (envsC i).trace 9 ≠ 1 := by rw [h9]; exact zero_ne_one
  exact slotCert_two_of_not_s9 envsC i this

end SlotMap

section Constants
variable {K : Type} [Field K]

/-- `T` of a shift-`1` certificate is `λ` (`sampledSlotT 67 = sampledLam`). -/
theorem Tpoly_one : (Tpoly 1 : Polynomial K) = X := by simp [Tpoly, Y]

/-- `C'` of the slot-0 constant certificate is `Y^{n−1} + Y^{n−2}`
(`sampledSlotC 67 = lamPowVar 0 + lamPowVar 1`), `n ≥ 2`. -/
theorem C'poly_slot0 (n : ℕ) (hn : 2 ≤ n) :
    (C'poly n (fun k => decide (k = 1)) : Polynomial K) = X ^ (n - 1) + X ^ (n - 2) := by
  unfold C'poly Nock.RedTeam.Batch554.Cpoly
  congr 1
  rw [Finset.sum_eq_single 0]
  · simp [Nock.RedTeam.Batch554.bit]
    congr 1
  · intro j _ hj
    simp [Nock.RedTeam.Batch554.bit]
    exact hj
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- `C'` of the empty certificate is `Y^{n−1}` (`lamPowVar 0`). -/
theorem C'poly_empty (n : ℕ) :
    (C'poly n (fun _ => false) : Polynomial K) = X ^ (n - 1) := by
  unfold C'poly
  exact Cpoly_false (n - 1)

end Constants

/-! ## C-b and the read set -/

theorem reqIdxCol_eq : OptimizedMemoryGateBasis.reqIdxCol = 181 := rfl

section ReadSet
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [Fintype F] [DecidableEq F] {N M : ℕ}

/-- The memory read set: base selectors `0..2` and `reqIdx` (`181`). -/
def MemoryAgree (envsF envsF' : Fin M → Env F) : Prop :=
  ∀ r c, (c ≤ 2 ∨ c = 181) → (envsF r).trace c = (envsF' r).trace c

variable {envsC envsC' : Fin N → Env K}

variable {envsF envsF' : Fin M → Env F}

theorem foOfMem_congr (h : MemoryAgree envsF envsF') : foOfMem envsF = foOfMem envsF' := by
  funext i
  unfold foOfMem
  split_ifs with hi
  · rw [memRowStateOf_congr fun c hc => h _ c (Or.inl hc)]
  · rfl

theorem childIdx_congr (h : MemoryAgree envsF envsF') (kroots : ℕ) :
    childIdx envsF kroots = childIdx envsF' kroots := by
  funext i l
  unfold childIdx
  rw [foOfMem_congr h]

theorem rowExp_congr (h : MemoryAgree envsF envsF') : rowExp envsF = rowExp envsF' := by
  funext r
  unfold rowExp
  rw [h r 181 (Or.inr rfl)]

/-- The decoded tree reads only the memory read set, and never the `𝕂` envs. -/
theorem decodedMTreeOfEnvs_congr (h : MemoryAgree envsF envsF') (envsK envsK' : Fin M → Env K)
    (kroots : ℕ) :
    ∀ i, decodedMTreeOfEnvs envsK envsF kroots i = decodedMTreeOfEnvs envsK' envsF' kroots i := by
  refine measure_induction (M := M) _ fun i ih => ?_
  by_cases hi : 1 ≤ i ∧ i ≤ M
  · conv_lhs => rw [decodedMTreeOfEnvs, dif_pos hi]
    conv_rhs => rw [decodedMTreeOfEnvs, dif_pos hi]
    have hst := memRowStateOf_congr (e := envsF ⟨i - 1, by omega⟩) (e' := envsF' ⟨i - 1, by omega⟩)
      fun c hc => h _ c (Or.inl hc)
    have hc := childIdx_congr h kroots
    have he := rowExp_congr h
    rw [hst, hc, he]
    have hch : ∀ l, (if i < childIdx envsF' kroots i l then
        decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF' kroots i l) else .halt) =
        (if i < childIdx envsF' kroots i l then
        decodedMTreeOfEnvs envsK' envsF' kroots (childIdx envsF' kroots i l) else .halt) := by
      intro l
      split_ifs with hlt
      · exact ih _ hlt hi.1 hi.2
      · rfl
    rw [← hc] at hch
    rcases memRowStateOf (envsF' ⟨i - 1, by omega⟩) <;> simp only [hc] at hch ⊢ <;>
      simp only [hch]
  · rw [tree_out envsK envsF kroots i hi, tree_out envsK' envsF' kroots i hi]

/-- **The read set (C-b).**  Agreement on the compute columns `0..9`, `202..270` and the memory base
columns `0..2`, `181` determines the event; the `𝕂` envs and every challenge component are free. -/
theorem event_readSet (hC : ComputeAgree envsC envsC') (hF : MemoryAgree envsF envsF')
    (envsK envsK' : Fin M → Env K) (kroots : ℕ) :
    decodedLambdaEventOfEnvs envsC envsK envsF kroots =
      decodedLambdaEventOfEnvs envsC' envsK' envsF' kroots := by
  have hr : ∀ r, decodedRootBad envsC envsK envsF kroots r =
      decodedRootBad envsC' envsK' envsF' kroots r := by
    intro r
    unfold decodedRootBad decodedRootPoly
    rw [decodedShift_congr hC, decodedBits_congr hC,
      decodedMTreeOfEnvs_congr hF envsK envsK' kroots r]
  unfold decodedLambdaEventOfEnvs
  simp only [hr]

/-- In particular no `𝕂` env is read. -/
theorem event_ignores_envsK (envsC : Fin N → Env K) (envsF : Fin M → Env F)
    (envsK envsK' : Fin M → Env K) (kroots : ℕ) :
    decodedLambdaEventOfEnvs envsC envsK envsF kroots =
      decodedLambdaEventOfEnvs envsC envsK' envsF kroots :=
  event_readSet (fun _ _ _ => rfl) (fun _ _ _ => rfl) envsK envsK' kroots

end ReadSet

end

end Nock.RedTeam.Batch733

#print axioms Nock.RedTeam.Batch733.slotCert_zero
#print axioms Nock.RedTeam.Batch733.slotCert_one_of_s0
#print axioms Nock.RedTeam.Batch733.slotCert_one_of_not_s0
#print axioms Nock.RedTeam.Batch733.slotCert_two_of_s9
#print axioms Nock.RedTeam.Batch733.slotCert_two_of_s6
#print axioms Nock.RedTeam.Batch733.Tpoly_one
#print axioms Nock.RedTeam.Batch733.C'poly_slot0
#print axioms Nock.RedTeam.Batch733.C'poly_empty
#print axioms Nock.RedTeam.Batch733.event_readSet
#print axioms Nock.RedTeam.Batch733.event_ignores_envsK
