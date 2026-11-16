import Nock.NockVMROM.Thm54.PaperCensusArithmetic
import Nock.NockVMROM.Thm54.StrictPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
The paper separates generic IO table-building columns, transition gates, and endpoint constraints.  Its `Thm:comp_38` / `Thm:mem_38` source counts are already
walk/forest-composed.  The connective
narrative is the paper, and the consumed fingerprints are in Theorem 5.4.

This module therefore checks arithmetic and scope only.  It does not assign Nock semantics to
counted gates or construct a paper-shaped semantic template.
-/

namespace Nock.RedTeam.Batch35

/-! ## 1. Exact generic-IO bucket transcription -/

def compGenericIOColumnIncrement (e : ℕ) : ℕ := e
def compGenericIOTransitionIncrement (e : ℕ) : ℕ := e
def memGenericIOColumnIncrement (e : ℕ) : ℕ := e + 1
def memGenericIOTransitionIncrement (e : ℕ) : ℕ := 1 + e

def compGenericIOEndpointEqualities : ℕ := 1
def memGenericIOEndpointDeg3 (e : ℕ) : ℕ := e
def memGenericIOEndpointEqualities : ℕ := 2

theorem encoded_generic_io_increments (e : ℕ) :
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOColumns e =
        Nock.ComputeTable.comp_columns e + compGenericIOColumnIncrement e ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOTransitions e =
        Nock.ComputeTable.comp_deg4_gates e + compGenericIOTransitionIncrement e ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOColumns e =
        Nock.MemoryTable.mem_columns e + memGenericIOColumnIncrement e ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOTransitions e =
        Nock.MemoryTable.mem_deg4_gates e + memGenericIOTransitionIncrement e := by
  simp [Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOColumns,
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOTransitions,
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOColumns,
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOTransitions,
    compGenericIOColumnIncrement, compGenericIOTransitionIncrement,
    memGenericIOColumnIncrement, memGenericIOTransitionIncrement]

/-- Exact pin for the separately stated endpoint buckets. -/
theorem endpoint_bucket_pin (e : ℕ) :
    compGenericIOEndpointEqualities = 1 ∧
      memGenericIOEndpointDeg3 e = e ∧
      memGenericIOEndpointEqualities = 2 := by
  simp [compGenericIOEndpointEqualities, memGenericIOEndpointDeg3,
    memGenericIOEndpointEqualities]

/-- The compute endpoint equality is not silently included in the encoded transition increment. -/
theorem compute_endpoint_not_added_to_transition_count (e : ℕ) :
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOTransitions e ≠
      Nock.ComputeTable.comp_deg4_gates e +
        (compGenericIOTransitionIncrement e + compGenericIOEndpointEqualities) := by
  simp [Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOTransitions,
    compGenericIOTransitionIncrement, compGenericIOEndpointEqualities]

/-- The memory endpoint gates/equalities are likewise not in the encoded transition increment. -/
theorem memory_endpoints_not_added_to_transition_count (e : ℕ) :
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOTransitions e ≠
      Nock.MemoryTable.mem_deg4_gates e +
        (memGenericIOTransitionIncrement e + memGenericIOEndpointDeg3 e +
          memGenericIOEndpointEqualities) := by
  simp [Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOTransitions,
    memGenericIOTransitionIncrement, memGenericIOEndpointDeg3,
    memGenericIOEndpointEqualities]
  omega

/-! ## 2. Independent normal forms and deltas -/

theorem independent_normal_forms (e : ℕ) :
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOColumns e = 58 * e + 13 ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOTransitions e = 21 * e + 13 ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOColumns e = 55 * e + 6 ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOTransitions e = 21 * e + 14 := by
  simp only [Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOColumns,
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOTransitions,
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOColumns,
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOTransitions,
    Nock.ComputeTable.comp_columns, Nock.ComputeTable.comp_deg4_gates,
    Nock.MemoryTable.mem_columns, Nock.MemoryTable.mem_deg4_gates]
  omega

theorem independent_raw_deltas (e : ℕ) :
    Nock.ComputeTable.comp_columns e + 5 * e = Nock.NockVM.comp_io_columns e ∧
      Nock.ComputeTable.comp_deg4_gates e + (4 * e + 2) =
        Nock.NockVM.comp_io_deg4_gates e ∧
      Nock.MemoryTable.mem_columns e + (7 * e + 8) =
        Nock.NockVM.mem_io_columns e ∧
      Nock.MemoryTable.mem_deg4_gates e + (4 * e + 3) =
        Nock.NockVM.mem_io_deg4_gates e := by
  simp only [Nock.ComputeTable.comp_columns, Nock.ComputeTable.comp_deg4_gates,
    Nock.MemoryTable.mem_columns, Nock.MemoryTable.mem_deg4_gates,
    Nock.NockVM.comp_io_columns, Nock.NockVM.comp_io_deg4_gates,
    Nock.NockVM.mem_io_columns, Nock.NockVM.mem_io_deg4_gates]
  omega

theorem independent_residual_identities (e : ℕ) :
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOColumns e + 4 * e =
        Nock.NockVM.comp_io_columns e ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOTransitions e +
          (3 * e + 2) = Nock.NockVM.comp_io_deg4_gates e ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOColumns e +
          (6 * e + 7) = Nock.NockVM.mem_io_columns e ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOTransitions e +
          (3 * e + 2) = Nock.NockVM.mem_io_deg4_gates e := by
  simp only [Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOColumns,
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOTransitions,
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOColumns,
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOTransitions,
    Nock.ComputeTable.comp_columns, Nock.ComputeTable.comp_deg4_gates,
    Nock.MemoryTable.mem_columns, Nock.MemoryTable.mem_deg4_gates,
    Nock.NockVM.comp_io_columns, Nock.NockVM.comp_io_deg4_gates,
    Nock.NockVM.mem_io_columns, Nock.NockVM.mem_io_deg4_gates]
  omega

/-! ## 3. Positive-degree attacks and concrete non-vacuity -/

theorem all_after_generic_io_ne_capstone {e : ℕ} (he : 0 < e) :
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOColumns e ≠
        Nock.NockVM.comp_io_columns e ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOTransitions e ≠
        Nock.NockVM.comp_io_deg4_gates e ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOColumns e ≠
        Nock.NockVM.mem_io_columns e ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOTransitions e ≠
        Nock.NockVM.mem_io_deg4_gates e := by
  simp only [Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOColumns,
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOTransitions,
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOColumns,
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOTransitions,
    Nock.ComputeTable.comp_columns, Nock.ComputeTable.comp_deg4_gates,
    Nock.MemoryTable.mem_columns, Nock.MemoryTable.mem_deg4_gates,
    Nock.NockVM.comp_io_columns, Nock.NockVM.comp_io_deg4_gates,
    Nock.NockVM.mem_io_columns, Nock.NockVM.mem_io_deg4_gates]
  omega

theorem independent_cubic_values :
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOColumns 3 = 187 ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOTransitions 3 = 76 ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOColumns 3 = 171 ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOTransitions 3 = 77 ∧
      Nock.NockVM.comp_io_columns 3 = 199 ∧
      Nock.NockVM.comp_io_deg4_gates 3 = 87 ∧
      Nock.NockVM.mem_io_columns 3 = 196 ∧
      Nock.NockVM.mem_io_deg4_gates 3 = 88 := by
  norm_num [Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOColumns,
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOTransitions,
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOColumns,
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOTransitions,
    Nock.ComputeTable.comp_columns, Nock.ComputeTable.comp_deg4_gates,
    Nock.MemoryTable.mem_columns, Nock.MemoryTable.mem_deg4_gates,
    Nock.NockVM.comp_io_columns, Nock.NockVM.comp_io_deg4_gates,
    Nock.NockVM.mem_io_columns, Nock.NockVM.mem_io_deg4_gates]

/-- `e = 3` witnesses the only substantive hypothesis used by the non-equality theorem. -/
theorem cubic_positive_witness :
    0 < (3 : ℕ) ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOColumns 3 ≠
        Nock.NockVM.comp_io_columns 3 ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOTransitions 3 ≠
        Nock.NockVM.comp_io_deg4_gates 3 ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOColumns 3 ≠
        Nock.NockVM.mem_io_columns 3 ∧
      Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOTransitions 3 ≠
        Nock.NockVM.mem_io_deg4_gates 3 := by
  norm_num [Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOColumns,
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.compAfterGenericIOTransitions,
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOColumns,
    Nock.NockVMROM.Thm54.PaperCensusArithmetic.memAfterGenericIOTransitions,
    Nock.ComputeTable.comp_columns, Nock.ComputeTable.comp_deg4_gates,
    Nock.MemoryTable.mem_columns, Nock.MemoryTable.mem_deg4_gates,
    Nock.NockVM.comp_io_columns, Nock.NockVM.comp_io_deg4_gates,
    Nock.NockVM.mem_io_columns, Nock.NockVM.mem_io_deg4_gates]

/-! ## 4. Count arithmetic does not identify taxonomy or semantics -/

/-- Provenance tags for the already-composed source theorems: compute uses `Thm:Walk_IOP` and memory uses `Corr:forest`. -/
inductive SourceComposition where
  | walkIOP
  | forest
  deriving DecidableEq

structure SourceCount where
  columns : ℕ
  transitions : ℕ
  composition : SourceComposition

def computeSourceCount (e : ℕ) : SourceCount :=
  ⟨Nock.ComputeTable.comp_columns e, Nock.ComputeTable.comp_deg4_gates e, .walkIOP⟩

def memorySourceCount (e : ℕ) : SourceCount :=
  ⟨Nock.MemoryTable.mem_columns e, Nock.MemoryTable.mem_deg4_gates e, .forest⟩

/-- The arithmetic starts from the paper's source definitions themselves, tagged with the
composition their paper proofs already perform; no second Walk/forest increment is added. -/
theorem source_counts_are_already_composed (e : ℕ) :
    (computeSourceCount e).columns = Nock.ComputeTable.comp_columns e ∧
      (computeSourceCount e).transitions = Nock.ComputeTable.comp_deg4_gates e ∧
      (computeSourceCount e).composition = .walkIOP ∧
      (memorySourceCount e).columns = Nock.MemoryTable.mem_columns e ∧
      (memorySourceCount e).transitions = Nock.MemoryTable.mem_deg4_gates e ∧
      (memorySourceCount e).composition = .forest := by
  simp [computeSourceCount, memorySourceCount]

/-- The source statements say degree `4`, while the consumed capstone says degree *at most* `4`. -/
inductive DegreeTaxonomy where
  | exact (d : ℕ)
  | atMost (d : ℕ)
  deriving DecidableEq

theorem source_and_capstone_degree_taxonomies_differ :
    DegreeTaxonomy.exact 4 ≠ DegreeTaxonomy.atMost 4 := by
  decide

structure CountedGateTaxonomy where
  count : ℕ
  endpointConstraintsIncluded : Bool

theorem count_does_not_identify_gate_taxonomy (n : ℕ) :
    ∃ a b : CountedGateTaxonomy, a.count = n ∧ b.count = n ∧ a ≠ b := by
  refine ⟨⟨n, false⟩, ⟨n, true⟩, rfl, rfl, ?_⟩
  intro h
  have hbool := congrArg CountedGateTaxonomy.endpointConstraintsIncluded h
  simp at hbool

/-- The count identities are unconditional, so hypothesis satisfiability is not applicable;
`cubic_positive_witness` separately inhabits the positive-degree attack premise. -/
inductive ArithmeticVacuityStatus where
  | notApplicableUnconditional
  deriving DecidableEq

def arithmeticVacuityStatus : ArithmeticVacuityStatus :=
  .notApplicableUnconditional

theorem arithmetic_vacuity_not_applicable :
    arithmeticVacuityStatus = .notApplicableUnconditional := rfl

/-! ## 5. Scope guards -/

abbrev reviewed_comp_residual_signature :=
  @Nock.NockVMROM.Thm54.PaperCensusArithmetic.comp_columns_residual

/-- Exact projection pin: the strict package still carries the compute semantic-template field. -/
def strict_package_compSemanticTemplate_field
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ}
    (P : Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage F K hOrb q Λ) :
    Nock.RedTeam.Batch29.B29SemanticTemplate (K := K)
      (Nock.NockVMROM.Thm54.MonolithicRAP.compTemplate F) P.compLanguage :=
  P.compSemanticTemplate

/-- Exact projection pin: the strict package still carries the memory semantic-template field. -/
def strict_package_memSemanticTemplate_field
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ}
    (P : Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage F K hOrb q Λ) :
    Nock.RedTeam.Batch29.B29SemanticTemplate (K := K)
      (Nock.NockVMROM.Thm54.MonolithicRAP.memTemplate F) P.memLanguage :=
  P.memSemanticTemplate

/-- The strict capstone remains conditional on a package. -/
noncomputable def strict_capstone_target
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ}
    (P : Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage F K hOrb q Λ) :
    Nock.NockVMROM.Thm54.StrictPackage.StrictThm54Statement P :=
  Nock.NockVMROM.Thm54.StrictPackage.strictNockVMROM_of_package P

theorem paper_alias_remains_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest := rfl

end Nock.RedTeam.Batch35

#print axioms Nock.RedTeam.Batch35.encoded_generic_io_increments
#print axioms Nock.RedTeam.Batch35.endpoint_bucket_pin
#print axioms Nock.RedTeam.Batch35.compute_endpoint_not_added_to_transition_count
#print axioms Nock.RedTeam.Batch35.memory_endpoints_not_added_to_transition_count
#print axioms Nock.RedTeam.Batch35.independent_normal_forms
#print axioms Nock.RedTeam.Batch35.independent_raw_deltas
#print axioms Nock.RedTeam.Batch35.independent_residual_identities
#print axioms Nock.RedTeam.Batch35.all_after_generic_io_ne_capstone
#print axioms Nock.RedTeam.Batch35.independent_cubic_values
#print axioms Nock.RedTeam.Batch35.cubic_positive_witness
#print axioms Nock.RedTeam.Batch35.source_counts_are_already_composed
#print axioms Nock.RedTeam.Batch35.source_and_capstone_degree_taxonomies_differ
#print axioms Nock.RedTeam.Batch35.count_does_not_identify_gate_taxonomy
#print axioms Nock.RedTeam.Batch35.arithmetic_vacuity_not_applicable
#print axioms Nock.RedTeam.Batch35.reviewed_comp_residual_signature
#print axioms Nock.RedTeam.Batch35.strict_package_compSemanticTemplate_field
#print axioms Nock.RedTeam.Batch35.strict_package_memSemanticTemplate_field
#print axioms Nock.RedTeam.Batch35.strict_capstone_target
#print axioms Nock.RedTeam.Batch35.paper_alias_remains_forest
