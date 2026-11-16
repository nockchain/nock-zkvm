/-
  Nock/NockVMROM/Thm54/P8Core/Batch733Thm54DecodedLambdaSlotMapReadSet.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch733Thm54DecodedLambdaSlotMapReadSet`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch733Thm54DecodedLambdaSlotMapReadSet.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.DecodedLambdaEvent

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

section ReadSet

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [Fintype F] [DecidableEq F] {N M : ℕ}

/-- The compute read set: selectors `0..9` and the certificate block `202..270`. -/
def ComputeAgree (envsC envsC' : Fin N → Env K) : Prop :=
  ∀ i c, (c < 10 ∨ (202 ≤ c ∧ c ≤ 270)) → (envsC i).trace c = (envsC' i).trace c

theorem computeArity_congr {e e' : Env K} (h : ∀ c, c < 10 → e.trace c = e'.trace c) :
    computeArity e = computeArity e' := by
  unfold computeArity
  rw [h 0 (by omega), h 2 (by omega), h 5 (by omega), h 6 (by omega), h 7 (by omega),
    h 8 (by omega), h 9 (by omega)]

theorem rowShift_congr {e e' : Env K} (h : ∀ c, 265 ≤ c → c ≤ 270 → e.trace c = e'.trace c) :
    rowShift e = rowShift e' := by
  unfold rowShift
  refine Finset.sum_congr rfl fun k hk => ?_
  have := Finset.mem_range.mp hk
  rw [h (265 + k) (by omega) (by omega)]

theorem rowBits_congr {e e' : Env K} (h : ∀ c, 202 ≤ c → c ≤ 264 → e.trace c = e'.trace c) :
    rowBits e = rowBits e' := by
  funext k
  unfold rowBits
  by_cases hk : 1 ≤ k ∧ k ≤ 63
  · rw [h (202 + (k - 1)) (by omega) (by omega)]
  · simp only [decide_eq_decide]
    constructor <;> intro hh <;> exact absurd ⟨hh.1, hh.2.1⟩ hk

variable {envsC envsC' : Fin N → Env K}

theorem computePrefix_congr (h : ComputeAgree envsC envsC') :
    computePrefix envsC = computePrefix envsC' := by
  funext i
  unfold computePrefix
  exact Finset.sum_congr rfl fun i' _ => computeArity_congr fun c hc => h i' c (Or.inl hc)

theorem locateExp_congr (h : ComputeAgree envsC envsC') : locateExp envsC = locateExp envsC' := by
  funext e
  unfold locateExp
  rw [computePrefix_congr h]
  have ha : ∀ i, computeArity (envsC i) = computeArity (envsC' i) := fun i =>
    computeArity_congr fun c hc => h i c (Or.inl hc)
  simp only [ha]

theorem slotCert_congr (h : ComputeAgree envsC envsC') : slotCert envsC = slotCert envsC' := by
  funext i j
  have hs : rowShift (envsC i) = rowShift (envsC' i) :=
    rowShift_congr fun c h1 h2 => h i c (Or.inr ⟨by omega, h2⟩)
  have hb : rowBits (envsC i) = rowBits (envsC' i) :=
    rowBits_congr fun c h1 h2 => h i c (Or.inr ⟨h1, by omega⟩)
  have h0 := h i 0 (Or.inl (by omega))
  have h9 := h i 9 (Or.inl (by omega))
  unfold slotCert
  rw [hs, hb, h0, h9]

theorem decodedShift_congr (h : ComputeAgree envsC envsC') :
    decodedShift envsC = decodedShift envsC' := by
  funext e
  unfold decodedShift
  rw [locateExp_congr h, slotCert_congr h]

theorem decodedBits_congr (h : ComputeAgree envsC envsC') :
    decodedBits envsC = decodedBits envsC' := by
  funext e k
  unfold decodedBits
  rw [locateExp_congr h, slotCert_congr h]

end ReadSet

end

end Nock.RedTeam.Batch733


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

section ReadSet

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [Fintype F] [DecidableEq F] {N M : ℕ}
variable {envsC envsC' : Fin N → Env K}
variable {envsF envsF' : Fin M → Env F}

theorem memRowStateOf_congr {e e' : Env F} (h : ∀ c, c ≤ 2 → e.trace c = e'.trace c) :
    memRowStateOf e = memRowStateOf e' := by
  unfold memRowStateOf
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega)]

end ReadSet

end

end Nock.RedTeam.Batch733
