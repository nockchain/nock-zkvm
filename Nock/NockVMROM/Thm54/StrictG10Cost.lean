/-
  Nock/NockVMROM/Thm54/StrictG10Cost.lean

  Theorem 5.4 deploys the Goldilocks cubic, `e = 3`.  At that
  specialization the paper's per-chip formulas read

  * compute: `62·3 + 13 = 199` columns, `24·3 + 15 = 87` transition gates;
  * memory:  `61·3 + 13 = 196` columns, `24·3 + 16 = 88` transition gates;
  * headline totals: `395` field elements per row and `175` degree-`≤ 4` gates.

  Everything below is read off `RAP_NockCompIO`/`RAP_NockMemIO`'s own `.w`, `.d`, `.k`, `.e` and
  their actual expanded gate lists — the `Nock.NockVM.comp_io_columns` family is the *transcription
  target* these are matched against, not the source of the numbers.

  `constructedStrictFingerprint` is then shown equal to
  `CompleteProductionCost.strictPaperG10Fingerprint`.  Both stay true, and
  `constructed_fingerprint_ne_segmentedProduction` records that they are different objects.
-/

import Nock.NockVMROM.Thm54.MonolithicMemRAP
import Nock.NockVMROM.Thm54.CompleteProductionCost
import Mathlib.FieldTheory.Finite.GaloisField

namespace Nock.NockVMROM.Thm54
namespace MonolithicRAP

open Module
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension

noncomputable section

/-! ## 1. The `e = 3` fingerprints of the constructed pair -/

section G10

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable {h : ℕ} (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
  (orbit : StrictOrbitDomain F 3 h) (Hc Hm : Finset F)

/-- **`199` compute columns at `e = 3`**, and the constructed width matches the
paper transcription `Nock.NockVM.comp_io_columns 3`. -/
theorem RAP_NockCompIO_width_e3 :
    (RAP_NockCompIO b chalVal pubVal orbit Hc).w = 199 ∧
      (RAP_NockCompIO b chalVal pubVal orbit Hc).w = Nock.NockVM.comp_io_columns 3 := by
  have hw := RAP_NockCompIO_width b chalVal pubVal orbit Hc
  refine ⟨by rw [hw], by rw [hw]; rfl⟩

/-- **`196` memory columns at `e = 3`**, matching `Nock.NockVM.mem_io_columns 3`. -/
theorem RAP_NockMemIO_width_e3 :
    (RAP_NockMemIO b chalVal pubVal orbit Hm).w = 196 ∧
      (RAP_NockMemIO b chalVal pubVal orbit Hm).w = Nock.NockVM.mem_io_columns 3 := by
  have hw := RAP_NockMemIO_width b chalVal pubVal orbit Hm
  refine ⟨by rw [hw], by rw [hw]; rfl⟩

/-- **`87` compute transition gates at `e = 3`**, matching
`Nock.NockVM.comp_io_deg4_gates 3`. -/
theorem RAP_NockCompIO_transition_gates_e3 :
    ((compTemplate F).transitionGates b).length = 87 ∧
      ((compTemplate F).transitionGates b).length = Nock.NockVM.comp_io_deg4_gates 3 := by
  have hg := RAP_NockCompIO_transition_gates (K := K) b
  refine ⟨by rw [hg], by rw [hg]; rfl⟩

/-- **`88` memory transition gates at `e = 3`**, matching
`Nock.NockVM.mem_io_deg4_gates 3`. -/
theorem RAP_NockMemIO_transition_gates_e3 :
    ((memTemplate F).transitionGates b).length = 88 ∧
      ((memTemplate F).transitionGates b).length = Nock.NockVM.mem_io_deg4_gates 3 := by
  have hg := RAP_NockMemIO_transition_gates (K := K) b
  refine ⟨by rw [hg], by rw [hg]; rfl⟩

/-- **The `395` headline: total field elements per row across both constructed chips.** -/
theorem constructed_total_columns_e3 :
    (RAP_NockCompIO b chalVal pubVal orbit Hc).w
        + (RAP_NockMemIO b chalVal pubVal orbit Hm).w = 395 ∧
      (RAP_NockCompIO b chalVal pubVal orbit Hc).w
        + (RAP_NockMemIO b chalVal pubVal orbit Hm).w = Nock.NockVM.total_row_elements := by
  have hc := (RAP_NockCompIO_width_e3 b chalVal pubVal orbit Hc).1
  have hm := (RAP_NockMemIO_width_e3 b chalVal pubVal orbit Hm).1
  refine ⟨by rw [hc, hm], by rw [hc, hm]; rfl⟩

/-- **The `175` headline: total degree-`≤ 4` transition gates across both constructed chips.** -/
theorem constructed_total_transition_gates_e3 :
    ((compTemplate F).transitionGates b).length + ((memTemplate F).transitionGates b).length
        = 175 ∧
      ((compTemplate F).transitionGates b).length + ((memTemplate F).transitionGates b).length
        = Nock.NockVM.total_deg4_gates := by
  have hc := (RAP_NockCompIO_transition_gates_e3 (K := K) b).1
  have hm := (RAP_NockMemIO_transition_gates_e3 (K := K) b).1
  refine ⟨by rw [hc, hm], by rw [hc, hm]; rfl⟩

/-- **Max degree `4` and the two round counts, at `e = 3`**. -/
theorem constructed_degree_and_rounds_e3 :
    (RAP_NockCompIO b chalVal pubVal orbit Hc).d = 4 ∧
      (RAP_NockMemIO b chalVal pubVal orbit Hm).d = 4 ∧
      (RAP_NockCompIO b chalVal pubVal orbit Hc).k = 2 ∧
      (RAP_NockMemIO b chalVal pubVal orbit Hm).k = 1 ∧
      (RAP_NockCompIO b chalVal pubVal orbit Hc).e = 3 ∧
      (RAP_NockMemIO b chalVal pubVal orbit Hm).e = 3 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. The strict `(199, 196, 3)` fingerprint -/

/-- The strict-paper fingerprint of the constructed pair: compute width, memory width, extension
degree — all three read off the constructed RAPs. -/
def constructedStrictFingerprint : ℕ × ℕ × ℕ :=
  ((RAP_NockCompIO b chalVal pubVal orbit Hc).w,
    (RAP_NockMemIO b chalVal pubVal orbit Hm).w,
    (RAP_NockCompIO b chalVal pubVal orbit Hc).e)

/-- **The constructed pair's fingerprint is `(199, 196, 3)`.** -/
theorem constructedStrictFingerprint_eq :
    constructedStrictFingerprint b chalVal pubVal orbit Hc Hm = (199, 196, 3) := by
  unfold constructedStrictFingerprint
  rw [(RAP_NockCompIO_width_e3 b chalVal pubVal orbit Hc).1,
    (RAP_NockMemIO_width_e3 b chalVal pubVal orbit Hm).1]
  rfl

/-- **The constructed pair meets the strict-paper G10 fingerprint.**  This is a NEW equality about
the NEW coordinate-expanded monolithic object; it leaves
`CompleteProductionCost.completeProductionCost_ne_strictPaperG10` — a statement about the OLD
segmented `(188, 78, 3)` production object — untouched and true. -/
theorem constructed_fingerprint_eq_strictG10 :
    constructedStrictFingerprint b chalVal pubVal orbit Hc Hm
      = CompleteProductionCost.strictPaperG10Fingerprint := by
  rw [constructedStrictFingerprint_eq]
  unfold CompleteProductionCost.strictPaperG10Fingerprint
  rw [Nock.NockVMROM.paperParamCost_IO_thm54.1, Nock.NockVMROM.paperParamCost_IO_thm54.2.1]

/-- **The constructed object is not the old scoped segmented production object.**  Its fingerprint
is `(199, 196, 3)` while the segmented production census is `(188, 78, 3)`; both facts hold, of two
different objects. -/
theorem constructed_fingerprint_ne_segmentedProduction :
    constructedStrictFingerprint b chalVal pubVal orbit Hc Hm ≠ (188, 78, 3) := by
  rw [constructedStrictFingerprint_eq]
  decide

end G10

/-! ## 3. A concrete non-vacuous `e = 3` instance

`𝔽₁₃` carries an element of exact order `e·2^h = 3·2² = 12` (`Staging.omega13_order`), and
`GaloisField 13 3` is a genuine cubic extension of it, so both constructed RAPs exist as concrete
values at the paper's `e = 3`. -/

section Concrete

/-- The concrete base field of the non-vacuity instance. -/
abbrev G13 : Type := ZMod 13

/-- A genuine cubic extension of `𝔽₁₃`. -/
abbrev G13cubic : Type := GaloisField 13 3

/-- A three-element coordinate basis of the cubic extension over `𝔽₁₃`. -/
def basis13 : Basis (Fin 3) G13 G13cubic :=
  stdCoordBasis G13 G13cubic 3 (GaloisField.finrank 13 (by norm_num))

/-- The concrete constructed compute chip at `e = 3`. -/
def concreteCompRAP : RAP G13 :=
  RAP_NockCompIO basis13 (fun _ => 0) (fun _ => 0) Staging.stagingOrbit Finset.univ

/-- The concrete constructed memory chip at `e = 3`. -/
def concreteMemRAP : RAP G13 :=
  RAP_NockMemIO basis13 (fun _ => 0) (fun _ => 0) Staging.stagingOrbit Finset.univ

/-- **The concrete pair exists and carries the paper's `e = 3` fingerprint.** -/
theorem concrete_fingerprint :
    concreteCompRAP.w = 199 ∧ concreteMemRAP.w = 196 ∧
      concreteCompRAP.e = 3 ∧ concreteMemRAP.e = 3 ∧
      concreteCompRAP.d = 4 ∧ concreteMemRAP.d = 4 ∧
      concreteCompRAP.k = 2 ∧ concreteMemRAP.k = 1 := by
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact (RAP_NockCompIO_width_e3 basis13 (fun _ => 0) (fun _ => 0)
      Staging.stagingOrbit Finset.univ).1
  · exact (RAP_NockMemIO_width_e3 basis13 (fun _ => 0) (fun _ => 0)
      Staging.stagingOrbit Finset.univ).1

/-- **The concrete pair's `Def:RAP` generator really has order `e·2^h`**. -/
theorem concrete_omega_order :
    orderOf concreteCompRAP.ω = concreteCompRAP.e * 2 ^ concreteCompRAP.h ∧
      orderOf concreteMemRAP.ω = concreteMemRAP.e * 2 ^ concreteMemRAP.h :=
  ⟨Staging.stagingOrbit.order_ω, Staging.stagingOrbit.order_ω⟩

/-- The concrete pair's strict fingerprint is the paper's strict G10 fingerprint. -/
theorem concrete_fingerprint_eq_strictG10 :
    (concreteCompRAP.w, concreteMemRAP.w, concreteCompRAP.e)
      = CompleteProductionCost.strictPaperG10Fingerprint :=
  constructed_fingerprint_eq_strictG10 basis13 (fun _ => 0) (fun _ => 0)
    Staging.stagingOrbit Finset.univ Finset.univ

end Concrete

end

end MonolithicRAP
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockCompIO_width_e3
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockMemIO_width_e3
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockCompIO_transition_gates_e3
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockMemIO_transition_gates_e3
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.constructed_total_columns_e3
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.constructed_total_transition_gates_e3
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.constructed_degree_and_rounds_e3
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.constructedStrictFingerprint_eq
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.constructed_fingerprint_eq_strictG10
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.constructed_fingerprint_ne_segmentedProduction
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.concrete_fingerprint
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.concrete_omega_order
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.concrete_fingerprint_eq_strictG10
