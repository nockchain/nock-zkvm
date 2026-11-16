import Nock.NockVMROM.Thm54.BuildableTopologyCorrectness

/-!
# Buildable semantic axis witness

The generic reverse polynomial connective is `AxisBridge.countsP_zero_of_exactMemoryAxisValidity`.
This module derives the full generated memory witness from one buildable execution.  Its
same-execution served-memory CORE recursively traverses the supplied forest, and the connective
below translates that Nock-level witness into ancestry, exact support, semantic axis validity,
and the identically-zero root polynomial.  Neither buildable input accepts an axis or arithmetic
conclusion.
-/

namespace Nock.NockVMROM.Thm54.BuildableAxisWitness

open scoped Classical Polynomial
open Nock
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open BuildableChips BuildableTopologyCorrectness
open OptimizedComputeFinalTrace
open OptimizedMemorySameExecution
open TemplateAxisCounting

noncomputable section

/-- Exact-execution lift of the reverse batching theorem.  The only connective hypothesis not
already supplied by structural refinement and semantic axis validity is exact per-root exponent
support equality; this is the localization statement that a global semantic IO preimage does not
itself provide. -/
theorem rootPolynomial_of_exactMemoryAxisValidity
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h2 : (2 : K) ≠ 0)
    (S : ExactAxisStructuralRefinement cfg exec)
    (V : ExactMemoryAxisValidity cfg exec)
    (hsupport : ∀ i e,
      e ∈ readExps (exactAxisTree cfg exec i) ↔
        e ∈ verifyExps (exactAxisTree cfg exec i)) :
    ∀ i : Fin cfg.kMem, countsP_bin (exactAxisTree cfg exec i) = 0 := by
  intro i
  let t := exactAxisTree cfg exec i
  have hrnd : (readExps t).Nodup := S.readExps_nodup i
  have hvnd : (verifyExps t).Nodup := S.verifyExps_nodup i
  apply countsP_zero_of_exactMemoryAxisValidity h2 t hrnd hvnd (hsupport i)
  · intro e he
    exact nested_of_readVerifyNested t (S.ancestry i) e
      (fun q => readCount_le_one q t hrnd)
      (fun q => verifyCount_le_one q t hvnd)
  · intro e he
    exact V i e he ((hsupport i e).1 he)

/-- Indicator twin of `rootPolynomial_of_exactMemoryAxisValidity`. -/
theorem rootIndicator_of_exactMemoryAxisValidity
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (S : ExactAxisStructuralRefinement cfg exec)
    (hsupport : ∀ i e,
      e ∈ readExps (exactAxisTree cfg exec i) ↔
        e ∈ verifyExps (exactAxisTree cfg exec i)) :
    ∀ i : Fin cfg.kMem, indP_bin (exactAxisTree cfg exec i) = 0 := by
  intro i
  let t := exactAxisTree cfg exec i
  exact indP_zero_of_balanced t (S.readExps_nodup i) (S.verifyExps_nodup i) (hsupport i)

/-- First-row instance of the honest root-zero bridge (`memory_first_*`).
    Later seeds (`0 < i < kMem`) are the `hmore` argument — MultiRoot fills
    them by `simp` on the constructed cells; `kMem = 1` callers pass
    `fun _ hpos hlt => False.elim (by omega)`. -/
theorem rootPubZero_of_first_row
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows) (h0 : (i : ℕ) = 0) :
    (E.exec.memoryPubAt i).pt.counts = 0 ∧
      (E.exec.memoryPubAt i).pt.indicator = 0 := by
  have hi0 : i = ⟨0, E.cfg.memRows_pos⟩ := Fin.ext h0
  subst hi0
  exact ⟨E.chained.memory_first_counts, E.chained.memory_first_indicator⟩

/-- Assemble the evaluated first-row bridge.  Later-seed zeros (`0 < i < kMem`)
    are `LaterSeedZeros` / `hmore` — remaining Relaxis join at form R
    (`Batch558.cancellingTree_is_remaining_join`), not this field. -/
theorem rootPubZero_of_buildable
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows) (h0 : (i : ℕ) = 0) :
    (E.exec.memoryPubAt i).pt.counts = 0 ∧
      (E.exec.memoryPubAt i).pt.indicator = 0 :=
  rootPubZero_of_first_row E i h0

/-- Honest later-seed parent accums. Vacuous at `kMem ≤ 1`. -/
abbrev LaterSeedZeros {F K : Type} [Field F] [Field K] [Algebra F K]
    (E : BuildableNockExecution F K) : Prop :=
  ∀ i : Fin E.cfg.memRows,
    0 < (i : ℕ) → (i : ℕ) < E.cfg.kMem →
      (E.exec.memoryPubAt i).pt.counts = 0 ∧
        (E.exec.memoryPubAt i).pt.indicator = 0

/-- Later-seed zeros are vacuous when `kMem ≤ 1`. -/
theorem hmore_of_kMem_le_one
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (E : BuildableNockExecution F K) (hk : E.cfg.kMem ≤ 1) :
    LaterSeedZeros E :=
  fun _ hpos hlt => False.elim (by omega)

/-- Generic Milestone-4 production-memory assignment.  `hmore` is the
honest later-seed parent-accum fact; it is vacuous at
`kMem ≤ 1`. -/
noncomputable def buildableMemoryProductionAssignment
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) (I : Inputs E)
    (hmore : ∀ i : Fin E.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < E.cfg.kMem →
        (E.exec.memoryPubAt i).pt.counts = 0 ∧
          (E.exec.memoryPubAt i).pt.indicator = 0 := by later_seed_zeros) :
    MemoryProductionAssignment (sampledAssignment E I) E.execA where
  obligations := (memoryChipAssignment E I).obligations
  exec_encode := E.exec_encode
  axisStructural := E.memoryTrace.axisStructural
  axisRootPolynomial :=
    rootPolynomial_of_exactMemoryAxisValidity E.two_ne_zero
      E.memoryTrace.axisStructural E.memoryTrace.axisValidity E.memoryTrace.support
  axisRootIndicator :=
    rootIndicator_of_exactMemoryAxisValidity
      E.memoryTrace.axisStructural E.memoryTrace.support
  rootPubZero := fun i h0 => rootPubZero_of_buildable E i h0

/-- Generic use receipt: every fully supplied buildable execution and chip input inhabits the
production-memory assignment, with no additional axis or arithmetic premise. -/
theorem buildableMemoryProductionAssignment_nonempty
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) (I : Inputs E)
    (hmore : ∀ i : Fin E.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < E.cfg.kMem →
        (E.exec.memoryPubAt i).pt.counts = 0 ∧
          (E.exec.memoryPubAt i).pt.indicator = 0 := by later_seed_zeros) :
    Nonempty (MemoryProductionAssignment (sampledAssignment E I) E.execA) :=
  ⟨buildableMemoryProductionAssignment E I hmore⟩

namespace Concrete

open ConcreteStrictPackage
open BuildableConcrete
open BuildableChips.Concrete
open OptimizedMemorySameExecution.Concrete

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := ConcreteStrictPackage.concrete_char73
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- Its primitive memory obligations come from Milestone 3; ancestry and the exact
root polynomial come from the same concrete execution. -/
noncomputable def memoryProduction
    (hmore : LaterSeedZeros concreteExecution) :
    MemoryProductionAssignment (sampledAssignment concreteExecution inputs73)
      concreteExecution.execA :=
  buildableMemoryProductionAssignment concreteExecution inputs73 hmore

/-- Concrete non-vacuity of the strengthened universal input and its generated production-memory
upgrade.  No axis conclusion is accepted by either input record.
`hmore` is the remaining Relaxis join at form R (`kMem = 2` dummy halt). -/
theorem memoryProduction_nonvacuous
    (hmore : LaterSeedZeros concreteExecution) :
    Nonempty (SemanticTrace.ExactExecutionSemanticData
        concreteExecution.q concreteExecution.Λ concreteExecution.cfg concreteExecution.exec) ∧
      Nonempty (MemoryProductionAssignment
        (sampledAssignment concreteExecution inputs73) concreteExecution.execA) :=
  ⟨⟨concreteExecution.semanticData⟩, ⟨memoryProduction hmore⟩⟩

/-- The concrete generated assignment exports every used root-indexed axis consequence through the
production theorem, on the same exact execution. -/
theorem axis_eq_relaxis_of_used
    (hmore : LaterSeedZeros concreteExecution)
    (root : Fin concreteExecution.cfg.kMem) (e : ℕ)
    (hread : e ∈ readExps (exactAxisTree concreteExecution.cfg concreteExecution.execA root))
    (hverify : e ∈ verifyExps (exactAxisTree concreteExecution.cfg concreteExecution.execA root)) :
    vaxis e (exactAxisTree concreteExecution.cfg concreteExecution.execA root) =
      Relaxis e (exactAxisTree concreteExecution.cfg concreteExecution.execA root) := by
  have h2 : (2 : K73cubic) ≠ 0 := by
    intro hk
    have hbase : (2 : F73) ≠ 0 := by decide
    apply hbase
    apply (algebraMap F73 K73cubic).injective
    simpa only [map_ofNat, map_zero] using hk
  exact MemoryProductionAssignment.axis_eq_relaxis_of_used
    h2 (memoryProduction hmore) root e hread hverify

end Concrete

end
end Nock.NockVMROM.Thm54.BuildableAxisWitness

#print axioms Nock.NockVMROM.Thm54.BuildableAxisWitness.Concrete.memoryProduction
#print axioms Nock.NockVMROM.Thm54.BuildableAxisWitness.Concrete.memoryProduction_nonvacuous
#print axioms Nock.NockVMROM.Thm54.BuildableAxisWitness.Concrete.axis_eq_relaxis_of_used
#print axioms Nock.NockVMROM.Thm54.BuildableAxisWitness.rootPolynomial_of_exactMemoryAxisValidity
#print axioms Nock.NockVMROM.Thm54.BuildableAxisWitness.buildableMemoryProductionAssignment
#print axioms Nock.NockVMROM.Thm54.BuildableAxisWitness.buildableMemoryProductionAssignment_nonempty
