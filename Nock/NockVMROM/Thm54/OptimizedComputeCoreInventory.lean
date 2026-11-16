import Nock.NockVMROM.Thm54.PaperCensusArithmetic
import Nock.NockVMROM.Thm54.RAPPadding
import Nock.NockVMROM.Thm54.MonolithicMemRAP

/-!
# Source-derived inventory for the optimized compute core

This module records the part of R6 that is determined by the paper without choosing an
unpublished optimized column layout or inventing folded gate bodies.

There are two deliberately separate inventories:

* the explicit compute-row occurrences transcribed by the existing `94`-column AIR, where every `K³` fingerprint contributes three extension-field
  scalars; and
* the aggregate, already-walk-composed semantic blocks stated by `Thm:comp_38` plus the program-IO increments stated by
  `Thm:IO_result`.

The paper fixes the second inventory at `(13,58)` columns and `(13,21)` transition gates, but
does not enumerate a sharing/packing map from the first inventory to the second.  It displays one
specific four-way nonlinear fold at the paper; it does not list all thirteen base and
twenty-one extension transition expressions.  Consequently this file supplies no `ChipTemplate`
inhabitant and no zero, dummy-power, or self-language gate.

The endpoint/equality inventory is also kept explicit.  `ChipTemplate.allGates` and `RAP.s` count
transition gates together with endpoint/equality gates; the padding source therefore has total
`.s = 24e+15`, not merely the transition bucket `21e+13`.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeCoreInventory

open Nock.NockVMROM.Thm54

/-! ## Appendix-level semantic occurrences

These are occurrence taxonomies, not an optimized column assignment.  The counts agree with the
existing explicit `computeAIR` layout documented in `Nock/AIR.lean`.
-/

/-- The twelve `K³` fingerprints in the current label and its three child labels. -/
abbrev LabelFingerprintRole := Fin 12

/-- The three scalar coordinates `(size, dyck, leaf)` of every NPR fingerprint. -/
abbrev FingerprintCoordinate := Fin 3

/-- Scalar extension-field occurrences contributed by the twelve label fingerprints. -/
abbrev LabelFingerprintScalar := LabelFingerprintRole × FingerprintCoordinate

/-- The six formula-decomposition fingerprints
`f_h, f_t, f_th, f_tt, f_tth, f_ttt`. -/
abbrev FormulaDecompositionRole := Fin 6

/-- Scalar extension-field occurrences contributed by formula decomposition. -/
abbrev FormulaDecompositionScalar := FormulaDecompositionRole × FingerprintCoordinate

/-- The two line-nonce occurrences `ln_prev, ln`. -/
abbrev LineNonceOccurrence := Fin 2

/-- The three compute-table memory-record occurrences. -/
abbrev MemoryRecordRole := Fin 3

/-- Extension-field parts of one record: three root coordinates, three child coordinates, and
one timestamp. -/
abbrev MemoryRecordExtensionPart := Fin 7

/-- Scalar extension-field occurrences in all three memory records. -/
abbrev MemoryRecordExtensionScalar := MemoryRecordRole × MemoryRecordExtensionPart

/-- The base-field axis occurrence in each of the three records. -/
abbrev MemoryRecordAxisOccurrence := MemoryRecordRole

/-- The eleven one-hot opcode selectors `op_0,...,op_9,op_11`. -/
abbrev OpcodeSelectorOccurrence := Fin 11

/-- The three extension-valued inverse witnesses materialized by the existing exact AIR:
`cons_inv`, `inv_gen`, and the polynomial `z⁻¹` witness used by NPR concatenation. -/
abbrev ExplicitAuxiliaryOccurrence := Fin 3

theorem labelFingerprintScalar_card :
    Fintype.card LabelFingerprintScalar = 36 := by
  simp

theorem formulaDecompositionScalar_card :
    Fintype.card FormulaDecompositionScalar = 18 := by
  simp

theorem memoryRecordExtensionScalar_card :
    Fintype.card MemoryRecordExtensionScalar = 21 := by
  simp

/-- The directly reified extension-valued occurrence count is `80`; this is an explicit
semantic inventory, not the optimized `58`-column layout. -/
theorem explicitReifiedExtensionOccurrenceCount :
    Fintype.card LabelFingerprintScalar
      + Fintype.card FormulaDecompositionScalar
      + Fintype.card LineNonceOccurrence
      + Fintype.card MemoryRecordExtensionScalar
      + Fintype.card ExplicitAuxiliaryOccurrence = 80 := by
  norm_num [labelFingerprintScalar_card, formulaDecompositionScalar_card,
    memoryRecordExtensionScalar_card]

/-- The directly reified base-valued occurrence count is `14`: eleven selectors and three
record axes. -/
theorem explicitReifiedBaseOccurrenceCount :
    Fintype.card OpcodeSelectorOccurrence
      + Fintype.card MemoryRecordAxisOccurrence = 14 := by
  norm_num

/-! ## Paper-determined optimized semantic blocks

The anonymous `Fin` indices below intentionally carry no variable names.  The paper gives only the
block totals: the already-walk-composed compute RAP and the generic program-IO increment.  Giving
those anonymous positions invented semantic names would exceed the source.
-/

/-- Base columns in the already-walk-composed `Thm:comp_38` block. -/
abbrev TableWalkBaseColumn := Fin 13

/-- `Thm:IO_result` adds no base column on the program side. -/
abbrev ProgramIOBaseColumn := Fin 0

/-- Typed base-column taxonomy for the optimized compute semantic core. -/
abbrev BaseColumn := TableWalkBaseColumn ⊕ ProgramIOBaseColumn

/-- Extension columns in the already-walk-composed `Thm:comp_38` block. -/
abbrev TableWalkExtensionColumn := Fin 57

/-- The one extension-valued program-IO accumulator column. -/
abbrev ProgramIOExtensionColumn := Fin 1

/-- Typed extension-column taxonomy for the optimized compute semantic core. -/
abbrev ExtensionColumn := TableWalkExtensionColumn ⊕ ProgramIOExtensionColumn

theorem baseColumn_card : Fintype.card BaseColumn = 13 := by
  simp

theorem extensionColumn_card : Fintype.card ExtensionColumn = 58 := by
  simp

/-- Coordinate-expanded optimized compute-core width. -/
def expandedColumnCount (e : ℕ) : ℕ :=
  Fintype.card BaseColumn + Fintype.card ExtensionColumn * e

/-- The typed block inventory is exactly the source-plus-generic-IO arithmetic, with no second
walk contribution. -/
theorem expandedColumnCount_eq_source (e : ℕ) :
    expandedColumnCount e =
      PaperCensusArithmetic.compAfterGenericIOColumns e := by
  rw [PaperCensusArithmetic.compAfterGenericIOColumns_eq]
  simp [expandedColumnCount]
  omega

theorem expandedColumnCount_eq (e : ℕ) :
    expandedColumnCount e = 58 * e + 13 := by
  rw [expandedColumnCount_eq_source,
    PaperCensusArithmetic.compAfterGenericIOColumns_eq]

/-! ## Folded transition-gate taxonomy -/

/-- Base transition gates in the already-walk-composed `Thm:comp_38` block.  The paper does not enumerate their thirteen bodies. -/
abbrev TableWalkBaseTransition := Fin 13

/-- Program IO contributes no base transition gate. -/
abbrev ProgramIOBaseTransition := Fin 0

/-- Typed base transition-gate taxonomy for the optimized compute semantic core. -/
abbrev BaseTransition := TableWalkBaseTransition ⊕ ProgramIOBaseTransition

/-- Extension transition gates in the already-walk-composed `Thm:comp_38` block. -/
abbrev TableWalkExtensionTransition := Fin 20

/-- The one extension-valued program-IO transition gate. -/
abbrev ProgramIOExtensionTransition := Fin 1

/-- Typed extension transition-gate taxonomy for the optimized compute semantic core. -/
abbrev ExtensionTransition :=
  TableWalkExtensionTransition ⊕ ProgramIOExtensionTransition

theorem baseTransition_card : Fintype.card BaseTransition = 13 := by
  simp

theorem extensionTransition_card :
    Fintype.card ExtensionTransition = 21 := by
  simp

/-- Coordinate-expanded transition count before the authorized residual padding. -/
def expandedTransitionCount (e : ℕ) : ℕ :=
  Fintype.card BaseTransition + Fintype.card ExtensionTransition * e

theorem expandedTransitionCount_eq_source (e : ℕ) :
    expandedTransitionCount e =
      PaperCensusArithmetic.compAfterGenericIOTransitions e := by
  rw [PaperCensusArithmetic.compAfterGenericIOTransitions_eq]
  simp [expandedTransitionCount]
  omega

theorem expandedTransitionCount_eq (e : ℕ) :
    expandedTransitionCount e = 21 * e + 13 := by
  rw [expandedTransitionCount_eq_source,
    PaperCensusArithmetic.compAfterGenericIOTransitions_eq]

/-! ## Endpoint/equality buckets

Theorem 5.4 separately lists `2e` degree-one endpoints, `e` degree-three endpoints, and two
base equality checks.  The authorized AO residual adds only columns and
transition constraints, so these are also the required core-scope bucket sizes.
-/

abbrev ExtensionDegreeOneEndpoint := Fin 2
abbrev ExtensionDegreeThreeEndpoint := Fin 1
/-- This inventory models the padding-source template, not the deployed chip; since stage 3e the deployed chip commits twenty-two individual masked equations
(`OptimizedComputeFinal.finalEndpointEqualityChecks`), so the two tracks diverge here. -/
abbrev BaseEqualityCheck := Fin 2

theorem extensionDegreeOneEndpoint_card :
    Fintype.card ExtensionDegreeOneEndpoint = 2 := by
  rfl

theorem extensionDegreeThreeEndpoint_card :
    Fintype.card ExtensionDegreeThreeEndpoint = 1 := by
  rfl

theorem baseEqualityCheck_card :
    Fintype.card BaseEqualityCheck = 2 := by
  rfl

/-- Endpoint and equality constraints contribute `3e+2` constraints outside the transition
bucket. -/
def expandedEndpointEqualityCount (e : ℕ) : ℕ :=
  Fintype.card ExtensionDegreeOneEndpoint * e
    + Fintype.card ExtensionDegreeThreeEndpoint * e
    + Fintype.card BaseEqualityCheck

theorem expandedEndpointEqualityCount_eq (e : ℕ) :
    expandedEndpointEqualityCount e = 3 * e + 2 := by
  simp [expandedEndpointEqualityCount]
  omega

/-- A `ChipTemplate` carrying all requested source buckets has `24e+15` total gates before
authorized residual padding, because `allGates` includes endpoints and equalities. -/
def expandedAllGateCount (e : ℕ) : ℕ :=
  expandedTransitionCount e + expandedEndpointEqualityCount e

theorem expandedAllGateCount_eq (e : ℕ) :
    expandedAllGateCount e = 24 * e + 15 := by
  rw [expandedAllGateCount, expandedTransitionCount_eq,
    expandedEndpointEqualityCount_eq]
  omega

/-- Final transition count after adding the authorized `3e+2` literal-zero constraints. -/
def expandedFinalTransitionCount (e : ℕ) : ℕ :=
  expandedTransitionCount e + RAPPadding.residualTransitionGates e

theorem expandedFinalTransitionCount_eq (e : ℕ) :
    expandedFinalTransitionCount e = 24 * e + 15 := by
  rw [expandedFinalTransitionCount, expandedTransitionCount_eq]
  simp [RAPPadding.residualTransitionGates]
  omega

/-- Final total `RAP.s`: source transitions, unchanged endpoint/equality buckets, and the
authorized literal-zero transition residual. -/
def expandedFinalTotalConstraintCount (e : ℕ) : ℕ :=
  expandedAllGateCount e + RAPPadding.residualTransitionGates e

theorem expandedFinalTotalConstraintCount_eq (e : ℕ) :
    expandedFinalTotalConstraintCount e =
      RAPPadding.computeFinalTotalConstraints e := by
  rw [expandedFinalTotalConstraintCount, expandedAllGateCount_eq]
  simp [RAPPadding.residualTransitionGates,
    RAPPadding.computeFinalTotalConstraints]
  omega

theorem cubic_inventory :
    expandedColumnCount 3 = 187 ∧
      expandedTransitionCount 3 = 76 ∧
      expandedEndpointEqualityCount 3 = 11 ∧
      expandedAllGateCount 3 = 87 ∧
      expandedFinalTransitionCount 3 = 87 ∧
      expandedFinalTotalConstraintCount 3 = 98 := by
  norm_num [expandedColumnCount_eq, expandedTransitionCount_eq,
    expandedEndpointEqualityCount_eq, expandedAllGateCount_eq,
    expandedFinalTransitionCount_eq, expandedFinalTotalConstraintCount_eq,
    RAPPadding.computeFinalTotalConstraints]

/-- The corrected padding source `.s` is exactly the inventory's all-gates count. -/
theorem cubic_allGates_eq_padding_source_total :
    expandedAllGateCount 3 = RAPPadding.computeCoreTotalConstraints 3 := by
  norm_num [expandedAllGateCount_eq, RAPPadding.computeCoreTotalConstraints,
    RAPPadding.computeCoreTransitionGates,
    RAPPadding.computeCoreEndpointEqualityConstraints]

/-! ## Equality with the consumed monolithic total-constraint fingerprints -/

open Module
open Nock.Framework
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension

noncomputable section

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem padded_compute_s_eq_RAP_NockCompIO_s {e h : ℕ}
    (R : RAP F) (hk : 0 < R.k)
    (hw : R.w = RAPPadding.computeCoreWidth e)
    (hs : R.s = RAPPadding.computeCoreTotalConstraints e)
    (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F e h) (H : Finset F) :
    (RAPPadding.padComputeCore R hk e).s =
      (RAP_NockCompIO b chalVal pubVal orbit H).s := by
  rw [(RAPPadding.padComputeCore_fingerprint R hk e hw hs).2,
    RAP_NockCompIO_s]
  rfl

theorem padded_memory_s_eq_RAP_NockMemIO_s {e h : ℕ}
    (R : RAP F) (hk : 0 < R.k)
    (hw : R.w = RAPPadding.memoryCoreWidth e)
    (hs : R.s = RAPPadding.memoryCoreTotalConstraints e)
    (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F e h) (H : Finset F) :
    (RAPPadding.padMemoryCore R hk e).s =
      (RAP_NockMemIO b chalVal pubVal orbit H).s := by
  rw [(RAPPadding.padMemoryCore_fingerprint R hk e hw hs).2,
    RAP_NockMemIO_s]
  rfl

end

#print axioms expandedColumnCount_eq_source
#print axioms expandedTransitionCount_eq_source
#print axioms expandedAllGateCount_eq
#print axioms cubic_inventory
#print axioms cubic_allGates_eq_padding_source_total
#print axioms padded_compute_s_eq_RAP_NockCompIO_s
#print axioms padded_memory_s_eq_RAP_NockMemIO_s

end OptimizedComputeCoreInventory
end Nock.NockVMROM.Thm54
