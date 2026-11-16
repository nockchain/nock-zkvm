/-
  Nock/RedTeam/Batch581Thm54FormREvent.lean

  Form R template polynomial
  at the strategy layer, with the certificate the landed row encode uses: `m = formRCertShift a`,
  `c_{j+1} = formRCertBit a j`, `n = Nat.size (ringChar K)` (`FormRAxisEvent.formRPolyOfCert`).

  Now the certificate is a certificate-AXIS map
  `A : ℕ → ℕ` and the polynomial is the landed one; the wrapper type is deleted.

  * `axis_cert_shapes` — axis `1` gives `(m, c) = (0, false)`, axis `2` gives `(1, false)`.
-/
import Nock.NockVMROM.Thm54.FormRAxisEvent
import Nock.RedTeam.Batch546Thm54LambdaModel
import Nock.RedTeam.Batch576Thm54FormRNegatives
import Nock.RedTeam.Batch577Thm54FormRCompleteness

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch581

open Nock
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54.FormRAxisEvent
open Nock.RedTeam.Batch546
open Nock.RedTeam.Batch575
open Nock.RedTeam.Batch576
open Nock.RedTeam.Batch577
open Polynomial

variable {K : Type} [Field K]

/-- Axis `1`: shift `0`, no bits. -/
theorem axis1_shape :
    certShiftOf (fun _ => 1) = (fun _ => 0) ∧ certBitsOf (fun _ => 1) = (fun _ _ => false) := by
  refine ⟨funext fun _ => by simp [certShiftOf, MemoryTable.formRCertShift, Nat.size_one],
    funext fun _ => funext fun _ => ?_⟩
  simp [certBitsOf, MemoryTable.formRCertBit, MemoryTable.formRCertShift, Nat.size_one]

/-- Axis `2` (`/[2]`, left child): shift `1`, bit `c_1 = 0`. -/
theorem axis2_shape :
    certShiftOf (fun _ => 2) = (fun _ => 1) ∧ certBitsOf (fun _ => 2) = (fun _ => leftBit) := by
  have hs : Nat.size 2 = 2 := by decide
  refine ⟨funext fun _ => by simp [certShiftOf, MemoryTable.formRCertShift, hs],
    funext fun _ => funext fun k => ?_⟩
  simp only [certBitsOf, MemoryTable.formRCertBit, MemoryTable.formRCertShift, hs, leftBit]
  split
  · rename_i h
    have : k - 1 = 0 := by omega
    rw [this]; decide
  · rfl

theorem axis_cert_shapes :
    (certShiftOf (fun _ => 1) = (fun _ => 0) ∧ certBitsOf (fun _ => 1) = (fun _ _ => false)) ∧
      (certShiftOf (fun _ => 2) = (fun _ => 1) ∧ certBitsOf (fun _ => 2) = (fun _ => leftBit)) :=
  ⟨axis1_shape, axis2_shape⟩

theorem crossing_template_nonzero (e : ℕ) (a : K) :
    formRPolyOfCert (fun _ => 1) (crossingTree e a) ≠ 0 := by
  intro hz
  have hB := n1_crossing_rejected (K := K) (formRN K) e a 0 (fun _ => false) (Nat.zero_le _)
  refine hB ?_
  have hz' : formRCounts (formRN K) (fun _ => (0 : ℕ)) (fun _ _ => false) (crossingTree e a) = 0 := by
    simpa [formRPolyOfCert, axis1_shape.1, axis1_shape.2] using hz
  simpa using (congrArg (fun p => Polynomial.coeff p e) hz')

theorem t1_template_nonzero (e : ℕ) :
    formRPolyOfCert (fun _ => 1) (t1 e (1 : K)) ≠ 0 := by
  intro hz
  have haxis : axis1 = fun _ => (0 : ℕ) := funext fun _ => rfl
  have hbits : axis1bits = fun _ _ => false := funext fun _ => funext fun _ => rfl
  have hB := n2_t1_rejected (K := K) (formRN K) e
  refine hB ?_
  have : formRCounts (formRN K) axis1 axis1bits (t1 e (1 : K)) = 0 := by
    simpa [formRPolyOfCert, axis1_shape.1, axis1_shape.2, haxis, hbits] using hz
  simp [this]

theorem honest_template_zero (e : ℕ) (a : K) (h2 : 2 ≤ ringChar K) :
    FormRRootIdentity (fun _ => 2) (c1Tree e a) := by
  have hn : 2 ≤ formRN K := by
    have := Nat.size_le_size h2
    simpa [formRN, show Nat.size 2 = 2 by decide] using this
  simpa [FormRRootIdentity, formRPolyOfCert, axis2_shape.1, axis2_shape.2] using
    (c1_honest (K := K) (formRN K) e a hn).2.1

end Nock.RedTeam.Batch581

#print axioms Nock.RedTeam.Batch581.crossing_template_nonzero
#print axioms Nock.RedTeam.Batch581.t1_template_nonzero
#print axioms Nock.RedTeam.Batch581.honest_template_zero
#print axioms Nock.RedTeam.Batch581.axis_cert_shapes
