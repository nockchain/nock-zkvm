import Nock.NockVMROM.Thm54.RAPPadding
import Nock.NockVMROM.Thm54.PlusIOSegmentedRAP

/-!
# Author-selected source inventory for the optimized memory core

The paper fixes the memory language and its one aggregate forest walk but does not publish a sharing map from the
explicit `35`-column `memoryAIR` to the optimized `6 + 55e` source fingerprint.  This file records
the selected production map as a correctness delta.  It is an occurrence inventory, not a second
memory language.

The four current-state selectors and fixed first/last masks are the six base roles.  The extension
roles contain every non-selector `memoryAIR` occurrence, the complete six-column single forest
walk, the sampled finite-field memory-IO witness surface, and four derived forest/axis summaries.
No role is residual padding; the authorized `6e+7` residual is added only after source satisfaction.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedMemoryCoreInventory

/-- Four `Vmem` states. -/
abbrev StateSelectorRole := Fin 4

/-- Fixed first/last-row masks used by canonical polynomial satisfaction. -/
abbrev EndpointMaskRole := Fin 2

/-- Typed six-base-column source codec. -/
abbrev BaseRole := StateSelectorRole ⊕ EndpointMaskRole

/-- Parent, left-child, and right-child NPR plus indicator/count occurrences: columns `4..18` of
the exact `memoryAIR`. -/
abbrev CellAndAxisAccumulatorRole := Fin 15

/-- Left-child state selectors: exact columns `19..22`. -/
abbrev ChildStateSelectorRole := Fin 4

/-- One NMR record: root NPR, child NPR, axis, and unique timestamp, exact columns `23..30`. -/
abbrev NMRRecordRole := Fin 8

/-- Current/next `intermediate`, its inverse witness, and the NPR seed inverse: columns `31..34`. -/
abbrev IntermediateRole := Fin 4

/-- All non-selector exact memory-table occurrences, in source-column order `4..34`. -/
abbrev MemoryTablePayloadRole :=
  CellAndAxisAccumulatorRole ⊕
    (ChildStateSelectorRole ⊕ (NMRRecordRole ⊕ IntermediateRole))

/-- One and only one aggregate forest walk: line, current fingerprint, child sum, fanout/count,
and accumulator roles. -/
abbrev ForestWalkRole := Fin 6

/-- Sampled finite-field memory-IO roles: compressed response, safe denominator and inverse,
multiplicity and inverse, current/next accumulator, terminal, activity, request terminal, and the
remaining explicitly checked malformed controls. -/
abbrev SampledMemoryIORole := Fin 14

/-- Extension-field mirrors of the four base state selectors.  These are not padding: they let the
extension-valued memory equations consume the same state chosen by the six-base codec; the four
scalar equality checks bind the mirrors back to the base selectors. -/
abbrev StateSelectorMirrorRole := Fin 4

/-- Physical role `55`;
not a reuse of hosted walk roles `34`/`35`/`36`. -/
abbrev QueueWitnessRole := Fin 1

/-- +1 queue-inverse). -/
abbrev ExtensionRole :=
  MemoryTablePayloadRole ⊕
    (ForestWalkRole ⊕ (SampledMemoryIORole ⊕ (StateSelectorMirrorRole ⊕ QueueWitnessRole)))

theorem baseRole_card : Fintype.card BaseRole = 6 := by simp

theorem memoryTablePayloadRole_card :
    Fintype.card MemoryTablePayloadRole = 31 := by simp

theorem extensionRole_card : Fintype.card ExtensionRole = 56 := by simp

/-- Explicit physical extension index: table payload `0..30`, forest walk `31..36`, sampled IO
`37..50`, selector mirrors `51..54`, queue inverse `55`. -/
def extensionIndex : ExtensionRole → Fin 56
  | .inl (.inl i) => ⟨i, by omega⟩
  | .inl (.inr (.inl i)) => ⟨15 + i, by omega⟩
  | .inl (.inr (.inr (.inl i))) => ⟨19 + i, by omega⟩
  | .inl (.inr (.inr (.inr i))) => ⟨27 + i, by omega⟩
  | .inr (.inl i) => ⟨31 + i, by omega⟩
  | .inr (.inr (.inl i)) => ⟨37 + i, by omega⟩
  | .inr (.inr (.inr (.inl i))) => ⟨51 + i, by omega⟩
  | .inr (.inr (.inr (.inr i))) => ⟨55 + i, by omega⟩

set_option maxRecDepth 100000 in
theorem extensionIndex_injective : Function.Injective extensionIndex := by
  decide

set_option maxRecDepth 100000 in
theorem extensionIndex_surjective : Function.Surjective extensionIndex := by
  decide

noncomputable def extensionEquiv : ExtensionRole ≃ Fin 56 :=
  Equiv.ofBijective extensionIndex
    ⟨extensionIndex_injective, extensionIndex_surjective⟩

@[simp] theorem extensionEquiv_apply (r : ExtensionRole) :
    extensionEquiv r = extensionIndex r := rfl

/-- Explicit selected occurrence map for the exact memory-table payload. -/
def memoryTableSourceColumn : MemoryTablePayloadRole → Fin 35
  | .inl i => ⟨4 + i, by omega⟩
  | .inr (.inl i) => ⟨19 + i, by omega⟩
  | .inr (.inr (.inl i)) => ⟨23 + i, by omega⟩
  | .inr (.inr (.inr i)) => ⟨31 + i, by omega⟩

theorem memoryTableSourceColumn_injective :
    Function.Injective memoryTableSourceColumn := by
  decide

/-- Dense payload index corresponding to exact memory columns `4..34`. -/
def memoryTablePayloadIndex (r : MemoryTablePayloadRole) : Fin 31 :=
  ⟨(memoryTableSourceColumn r : ℕ) - 4, by
    rcases r with i | i
    · omega
    · rcases i with i | i
      · omega
      · rcases i with i | i <;> omega⟩

theorem memoryTablePayloadIndex_injective :
    Function.Injective memoryTablePayloadIndex := by
  decide

theorem memoryTablePayloadIndex_surjective :
    Function.Surjective memoryTablePayloadIndex := by
  decide

noncomputable def memoryTablePayloadEquiv :
    MemoryTablePayloadRole ≃ Fin 31 :=
  Equiv.ofBijective memoryTablePayloadIndex
    ⟨memoryTablePayloadIndex_injective, memoryTablePayloadIndex_surjective⟩

@[simp] theorem memoryTablePayloadEquiv_apply (r : MemoryTablePayloadRole) :
    memoryTablePayloadEquiv r = memoryTablePayloadIndex r := rfl

theorem memoryTableSourceColumn_val (r : MemoryTablePayloadRole) :
    (memoryTableSourceColumn r : ℕ) = 4 + (memoryTablePayloadIndex r : ℕ) := by
  rcases r with r | r
  · simp [memoryTableSourceColumn, memoryTablePayloadIndex] <;> omega
  · rcases r with r | r
    · simp [memoryTableSourceColumn, memoryTablePayloadIndex] <;> omega
    · rcases r with r | r <;>
        simp [memoryTableSourceColumn, memoryTablePayloadIndex] <;> omega

theorem extensionIndex_payload_val (r : MemoryTablePayloadRole) :
    (extensionIndex (.inl r) : ℕ) = (memoryTablePayloadIndex r : ℕ) := by
  rcases r with r | r
  · simp [extensionIndex, memoryTablePayloadIndex, memoryTableSourceColumn] <;> omega
  · rcases r with r | r
    · simp [extensionIndex, memoryTablePayloadIndex, memoryTableSourceColumn] <;> omega
    · rcases r with r | r <;>
        simp [extensionIndex, memoryTablePayloadIndex, memoryTableSourceColumn] <;> omega

/-- Coordinate-expanded source width selected by the author-authorized delta. -/
def expandedColumnCount (e : ℕ) : ℕ :=
  Fintype.card BaseRole + Fintype.card ExtensionRole * e

theorem expandedColumnCount_eq (e : ℕ) :
    expandedColumnCount e = 56 * e + 6 := by
  simp [expandedColumnCount, baseRole_card, extensionRole_card]
  omega

/-- Source transition families: fourteen base equations and twenty-one extension-valued folds. -/
abbrev BaseTransitionRole := Fin 14
abbrev ExtensionTransitionRole := Fin 21

/-- Exact endpoint/equality buckets of the optimized memory source: `2e`, `2e`, and four scalar checks. -/
abbrev ExtensionDegreeOneEndpoint := Fin 2
abbrev ExtensionDegreeThreeEndpoint := Fin 2
abbrev BaseEqualityCheck := Fin 4

theorem source_gate_census :
    Fintype.card BaseTransitionRole = 14 ∧
      Fintype.card ExtensionTransitionRole = 21 ∧
      Fintype.card ExtensionDegreeOneEndpoint = 2 ∧
      Fintype.card ExtensionDegreeThreeEndpoint = 2 ∧
      Fintype.card BaseEqualityCheck = 4 := by
  decide

def expandedTransitionCount (e : ℕ) : ℕ := 14 + 21 * e
def expandedEndpointEqualityCount (e : ℕ) : ℕ := 2 * e + 2 * e + 4
def expandedTotalConstraintCount (e : ℕ) : ℕ :=
  expandedTransitionCount e + expandedEndpointEqualityCount e

/-! ### The inventory after the `𝔽 → 𝕂` retyping

The three counts above are the **pre-retyping** inventory.  `w` does not move: the mixed gates read columns that already exist. -/

def expandedTransitionCountMixedFolded (e : ℕ) : ℕ := 11 + 26 * e
def expandedEndpointEqualityCountMixedFolded (e : ℕ) : ℕ := 0 * e + 4 * e + 4 * e

/-- 6 base + 49 mixed `𝕂` gates. -/
def expandedTransitionCountMixed (e : ℕ) : ℕ := 6 + 49 * e
def expandedEndpointEqualityCountMixed (_e : ℕ) : ℕ := 0
def expandedTotalConstraintCountMixed (e : ℕ) : ℕ :=
  expandedTransitionCountMixed e + expandedEndpointEqualityCountMixed e

/-- `174 / 153`. -/
theorem cubic_source_census_mixed :
    expandedColumnCount 3 = 174 ∧
      expandedTransitionCountMixed 3 = 153 ∧
      expandedEndpointEqualityCountMixed 3 = 0 ∧
      expandedTotalConstraintCountMixed 3 = 153 := by
  refine ⟨?_, by decide, rfl, by decide⟩
  rw [expandedColumnCount_eq]

theorem cubic_source_census_mixed_folded :
    expandedTransitionCountMixedFolded 3 = 89 ∧
      expandedEndpointEqualityCountMixedFolded 3 = 24 ∧
      expandedTransitionCountMixedFolded 3 + expandedEndpointEqualityCountMixedFolded 3 = 113 := by
  decide

theorem cubic_source_census :
    expandedColumnCount 3 = 174 ∧
      expandedTransitionCount 3 = 77 ∧
      expandedEndpointEqualityCount 3 = 16 ∧
      expandedTotalConstraintCount 3 = 93 := by
  norm_num [expandedColumnCount_eq, expandedTransitionCount,
    expandedEndpointEqualityCount, expandedTotalConstraintCount]

theorem cubic_source_matches_padding :
    expandedColumnCount 3 + 6 = RAPPadding.memoryCoreWidth 3 ∧
      expandedTotalConstraintCount 3 = RAPPadding.memoryCoreTotalConstraints 3 := by
  norm_num [expandedColumnCount_eq, expandedTotalConstraintCount,
    expandedTransitionCount, expandedEndpointEqualityCount,
    RAPPadding.memoryCoreWidth, RAPPadding.memoryCoreTotalConstraints,
    RAPPadding.memoryCoreTransitionGates,
    RAPPadding.memoryCoreEndpointEqualityConstraints]

end OptimizedMemoryCoreInventory
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCoreInventory.memoryTableSourceColumn_injective
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCoreInventory.cubic_source_census
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCoreInventory.cubic_source_matches_padding
