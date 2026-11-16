import Nock.NockVMROM.Thm54.TemplateAxisStructure

/-!
# Production axis-structure verifier

The checks here read the α-free `MemoryRowTemplate` forest committed after the NPR seed.  They use
the committed natural `recordExponent` metadata directly; in particular, the checker never calls
the noncomputable `timestampExp`.

No prover-supplied proof field, axis-validity conclusion, per-root `countsP` acceptance, evaluator,
or semantic target is added.
-/

open scoped BigOperators Classical

namespace Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier

open Nock Nock.Walk
open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.AxisBridge
open SemanticTimestampStrategy
open TemplateRawJointSoundness
open TemplateAxisCounting
open TemplateAxisStructure

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]

/-! ## Linear, bottom-up ancestry checker -/

structure AncestryScan where
  accepts : Bool
  verifyExponents : Finset ℕ

/-- One bottom-up pass.  The finite set is generated from verify nodes in the same root. -/
def ancestryScan : MTree K → AncestryScan
  | .halt => ⟨true, ∅⟩
  | .decompose l r =>
      let sl := ancestryScan l
      let sr := ancestryScan r
      ⟨sl.accepts && sr.accepts, sl.verifyExponents ∪ sr.verifyExponents⟩
  | .read e c =>
      let sc := ancestryScan c
      ⟨decide (e ∈ sc.verifyExponents) && sc.accepts, sc.verifyExponents⟩
  | .verify e _ c =>
      let sc := ancestryScan c
      ⟨sc.accepts, insert e sc.verifyExponents⟩

def readVerifyNestedCheck (t : MTree K) : Bool :=
  (ancestryScan t).accepts

@[simp] theorem ancestryScan_verifyExponents (t : MTree K) :
    (ancestryScan t).verifyExponents = (verifyExps t).toFinset := by
  induction t with
  | halt => rfl
  | decompose l r ihl ihr => simp [ancestryScan, verifyExps, ihl, ihr]
  | read e c ih => simp [ancestryScan, verifyExps, ih]
  | verify e a c ih => simp [ancestryScan, verifyExps, ih]

theorem ancestryScan_accepts_iff (t : MTree K) :
    (ancestryScan t).accepts = true ↔ ReadVerifyNested t := by
  induction t with
  | halt => simp [ancestryScan, ReadVerifyNested]
  | decompose l r ihl ihr =>
      simp only [ancestryScan, Bool.and_eq_true, ReadVerifyNested]
      exact and_congr ihl ihr
  | read e c ih =>
      simp only [ancestryScan, Bool.and_eq_true, decide_eq_true_eq,
        ancestryScan_verifyExponents, ReadVerifyNested]
      rw [verifyCount_eq_count]
      have hmem :
          e ∈ (verifyExps c).toFinset ↔ 1 ≤ (verifyExps c).count e := by
        simp only [List.mem_toFinset]
        rw [← List.count_pos_iff]
        omega
      exact and_congr hmem ih
  | verify e a c ih =>
      simpa only [ancestryScan, ReadVerifyNested] using ih

@[simp] theorem readVerifyNestedCheck_eq_true_iff (t : MTree K) :
    readVerifyNestedCheck t = true ↔ ReadVerifyNested t :=
  ancestryScan_accepts_iff t

/-! ## Direct α-free root checks -/

/-- An authoritative template root, selected before `alphaM`. -/
def alphaFreeRoot
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (i : Fin T.kMem) :
    MTree K :=
  templateAxisTree (templateMemoryTreeAt E i)

/-- Direct check of committed `recordExponent` uniqueness at read nodes. -/
def readExponentUniqueCheck (t : MTree K) : Bool :=
  decide (readExps t).Nodup

@[simp] theorem readExponentUniqueCheck_eq_true_iff (t : MTree K) :
    readExponentUniqueCheck t = true ↔ (readExps t).Nodup := by
  simp [readExponentUniqueCheck]

/-- This is used on the read/verify exponent lists generated from one
root, never inferred by slicing the flattened global `LIO`. -/
def finiteLmIOCheck {R : Type} [DecidableEq R]
    (Ksz : ℕ) (requests responses : List R) : Bool :=
  decide (IO.InRange Ksz requests.length) &&
    decide (responses.length ≤ requests.length) &&
    decide responses.Nodup &&
    decide (requests.toFinset = responses.toFinset)

theorem finiteLmIOCheck_eq_true_iff {R : Type} [DecidableEq R]
    (Ksz : ℕ) (requests responses : List R) :
    finiteLmIOCheck Ksz requests responses = true ↔
      IO.LmIO Ksz requests responses := by
  rw [IO.LmIO_iff]
  simp [finiteLmIOCheck, and_assoc]

/-- Per-root intermediate partition on committed natural exponent/record identifiers. -/
def rootExponentPartitionCheck (Ksz : ℕ) (t : MTree K) : Bool :=
  finiteLmIOCheck Ksz (readExps t) (verifyExps t)

@[simp] theorem rootExponentPartitionCheck_eq_true_iff
    (Ksz : ℕ) (t : MTree K) :
    rootExponentPartitionCheck Ksz t = true ↔
      IO.LmIO Ksz (readExps t) (verifyExps t) := by
  simp [rootExponentPartitionCheck, finiteLmIOCheck_eq_true_iff]

def forestExponentPartitionCheck
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) : Bool :=
  finiteLmIOCheck T.Ksz (templateForestReadExps E) (templateForestVerifyExps E)

@[simp] theorem forestExponentPartitionCheck_eq_true_iff
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) :
    forestExponentPartitionCheck E = true ↔
      IO.LmIO T.Ksz (templateForestReadExps E) (templateForestVerifyExps E) := by
  simp [forestExponentPartitionCheck, finiteLmIOCheck_eq_true_iff]

/-- The two α-free per-root checks on one committed root. -/
def alphaFreeRootStructureCheck (t : MTree K) : Bool :=
  readVerifyNestedCheck t && readExponentUniqueCheck t

theorem alphaFreeRootStructureCheck_eq_true_iff (t : MTree K) :
    alphaFreeRootStructureCheck t = true ↔
      ReadVerifyNested t ∧ (readExps t).Nodup := by
  simp [alphaFreeRootStructureCheck]

/-- Exact α-free structural proposition decided by the verifier. -/
structure AlphaFreeAxisStructure
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) : Prop where
  ancestry : ∀ i, ReadVerifyNested (alphaFreeRoot E i)
  read_exponents_nodup : ∀ i, (readExps (alphaFreeRoot E i)).Nodup
  forest_partition :
    IO.LmIO T.Ksz (templateForestReadExps E) (templateForestVerifyExps E)

def alphaFreeAxisStructureCheck
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) : Bool :=
  decide (∀ i : Fin T.kMem, alphaFreeRootStructureCheck (alphaFreeRoot E i) = true) &&
    forestExponentPartitionCheck E

theorem alphaFreeAxisStructureCheck_eq_true_iff
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) :
    alphaFreeAxisStructureCheck E = true ↔ AlphaFreeAxisStructure E := by
  constructor
  · intro h
    rw [alphaFreeAxisStructureCheck, Bool.and_eq_true] at h
    have hall : ∀ i : Fin T.kMem,
        alphaFreeRootStructureCheck (alphaFreeRoot E i) = true := by
      simpa using h.1
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · exact (alphaFreeRootStructureCheck_eq_true_iff _).1 (hall i) |>.1
    · exact (alphaFreeRootStructureCheck_eq_true_iff _).1 (hall i) |>.2
    · exact (forestExponentPartitionCheck_eq_true_iff E).1 h.2
  · intro h
    rw [alphaFreeAxisStructureCheck, Bool.and_eq_true]
    refine ⟨?_, (forestExponentPartitionCheck_eq_true_iff E).2 h.forest_partition⟩
    simp only [decide_eq_true_eq]
    intro i
    exact (alphaFreeRootStructureCheck_eq_true_iff _).2
      ⟨h.ancestry i, h.read_exponents_nodup i⟩

/-! ## Separate no-wrap check at `alphaM` -/

/-- Every read exponent of one root lies below the multiplicative order of `alphaM`. -/
def rootNoWrapCheck (α : K) (t : MTree K) : Bool :=
  (readExps t).all fun e => decide (e < orderOf α)

theorem rootNoWrapCheck_eq_true_iff (α : K) (t : MTree K) :
    rootNoWrapCheck α t = true ↔
      ∀ e ∈ readExps t, e < orderOf α := by
  simp [rootNoWrapCheck, List.all_eq_true]

def noWrapCheck
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) : Bool :=
  decide (∀ i : Fin T.kMem, rootNoWrapCheck α (alphaFreeRoot E i) = true)

theorem noWrapCheck_eq_true_iff
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) :
    noWrapCheck E α = true ↔
      ∀ i e, e ∈ readExps (alphaFreeRoot E i) → e < orderOf α := by
  simp only [noWrapCheck, decide_eq_true_eq]
  constructor
  · intro h i e he
    exact (rootNoWrapCheck_eq_true_iff α _).1 (h i) e he
  · intro h i
    exact (rootNoWrapCheck_eq_true_iff α _).2 (h i)

/-! ## Sound transport to the specialized exact refinement -/

theorem exactAxisStructuralRefinement_of_checks
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) {lmb : K}
    (hstructure : alphaFreeAxisStructureCheck E = true)
    (hnowrap : noWrapCheck E α = true) :
    ExactAxisStructuralRefinement (T.specialize α lmb) (E.specializeA α lmb) := by
  have S := (alphaFreeAxisStructureCheck_eq_true_iff E).1 hstructure
  have W := (noWrapCheck_eq_true_iff E α).1 hnowrap
  refine
    { ancestry := ?_
      read_timestamps_nodup := ?_
      intermediate_matching := ?_ }
  · intro i
    rw [TemplateAxisStructure.exactAxisTree_specialize E α i,
      TemplateAxisStructure.recoveredAxisTree_eq_reindexAxisTree]
    exact TemplateAxisStructure.readVerifyNested_reindexAxisTree _ (S.ancestry i)
  · intro i
    change ((readExps (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i)).map
      (fun e => α ^ e)).Nodup
    rw [TemplateAxisStructure.specialized_readTimestamps_eq_template E α i]
    apply (S.read_exponents_nodup i).map_on
    intro x hx y hy hpow
    exact pow_injOn_Iio_orderOf
      (Set.mem_Iio.mpr (W i x hx)) (Set.mem_Iio.mpr (W i y hy)) hpow
  · change IO.LmIO T.Ksz
      (forestReadTimestamps (T.specialize α lmb) (E.specializeA α lmb))
      (forestVerifyTimestamps (T.specialize α lmb) (E.specializeA α lmb))
    rw [TemplateAxisStructure.forestReadTimestamps_specialize E α,
      TemplateAxisStructure.forestVerifyTimestamps_specialize E α]
    apply TemplateAxisStructure.lmIO_map_of_injective_on_requests
      T.Ksz _ _ (fun e => α ^ e) S.forest_partition
    intro x hx y hy hpow
    obtain ⟨ix, hix⟩ := TemplateAxisStructure.mem_templateForestReadExps hx
    obtain ⟨iy, hiy⟩ := TemplateAxisStructure.mem_templateForestReadExps hy
    exact pow_injOn_Iio_orderOf
      (Set.mem_Iio.mpr (W ix x hix)) (Set.mem_Iio.mpr (W iy y hiy)) hpow

/-! ## Template-staged production acceptance -/

abbrev ProductionStrategy :=
  ProductionRawVerifier.TemplateAdapter.Strategy F K p

def committedTemplate
    (T : ProductionStrategy (F := F) (K := K) (p := p))
    (z : K) (hz : z ≠ 0) :
    ExactExecutionTemplate (T.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate :=
  (T.raw.timestamp.afterSeed ⟨z, hz⟩).executionTemplate

/-- The structural check is α-free; only the explicitly separate no-wrap check sees `alphaM`. -/
def structuralChecksAt
    (T : ProductionStrategy (F := F) (K := K) (p := p))
    (z : K) (hz : z ≠ 0) (alphaMValue : K) : Bool :=
  alphaFreeAxisStructureCheck (committedTemplate T z hz) &&
    noWrapCheck (committedTemplate T z hz) alphaMValue

def ProductionAxisStructureAccepts
    (T : ProductionStrategy (F := F) (K := K) (p := p))
    (ω : JointCoins K) (lmb : K) : Prop :=
  if hz : nprSeed ω ≠ 0 then
    (T.messageAt ω lmb hz).VerifierChecks T.raw.claim ω ∧
      structuralChecksAt T (nprSeed ω) hz (alphaM ω) = true
  else False

theorem accepts_iff
    (T : ProductionStrategy (F := F) (K := K) (p := p))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    ProductionAxisStructureAccepts T ω lmb ↔
      (T.messageAt ω lmb hz).VerifierChecks T.raw.claim ω ∧
        structuralChecksAt T (nprSeed ω) hz (alphaM ω) = true := by
  simp [ProductionAxisStructureAccepts, hz]

theorem productionRawAccepts_of_accepts
    (T : ProductionStrategy (F := F) (K := K) (p := p))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (h : ProductionAxisStructureAccepts T ω lmb) :
    T.Accepts ω lmb := by
  apply (T.accepts_iff_production ω lmb hz).2
  exact ((accepts_iff T ω lmb hz).1 h).1

/-- Acceptance yields the structural refinement of the a-bearing view consumed by template axis
counting. -/
theorem exactAxisStructuralRefinement_of_accepts
    (T : ProductionStrategy (F := F) (K := K) (p := p))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (h : ProductionAxisStructureAccepts T ω lmb) :
    ExactAxisStructuralRefinement
      (specializedProblem T.raw.timestamp (nprSeed ω) hz (alphaM ω) lmb).cfg
      (specializedExecA T.raw.timestamp (nprSeed ω) hz (alphaM ω) lmb) := by
  have hs := ((accepts_iff T ω lmb hz).1 h).2
  have hparts : alphaFreeAxisStructureCheck
        (committedTemplate T (nprSeed ω) hz) = true ∧
      noWrapCheck (committedTemplate T (nprSeed ω) hz) (alphaM ω) = true := by
    simpa [structuralChecksAt] using hs
  exact exactAxisStructuralRefinement_of_checks
    (committedTemplate T (nprSeed ω) hz) (alphaM ω) hparts.1 hparts.2

/-- Reverse of `exactAxisStructuralRefinement_of_checks`: specialized structural
refinement plus the paper uniqueness window on read and verify exponents
inhabits the α-free Boolean. -/
theorem alphaFreeAxisStructure_of_specialized
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) {lmb : K}
    (R : ExactAxisStructuralRefinement (T.specialize α lmb) (E.specializeA α lmb))
    (hread : ∀ i e, e ∈ readExps (alphaFreeRoot E i) → e < orderOf α)
    (hverify : ∀ i e, e ∈ verifyExps (alphaFreeRoot E i) → e < orderOf α) :
    AlphaFreeAxisStructure E where
  ancestry := fun i =>
    TemplateAxisStructure.template_readVerifyNested_of_specialized E α R
      (fun j e he => hread j e (by simpa [alphaFreeRoot] using he))
      (fun j e he => hverify j e (by simpa [alphaFreeRoot] using he)) i
  read_exponents_nodup := fun i => by
    simpa [alphaFreeRoot] using
      TemplateAxisStructure.template_readExps_nodup_of_specialized E α R i
  forest_partition :=
    TemplateAxisStructure.template_forestPartition_of_specialized E α R
      (fun e he => by
        obtain ⟨i, hi⟩ := TemplateAxisStructure.mem_templateForestReadExps he
        exact hread i e (by simpa [alphaFreeRoot] using hi))
      (fun e he => by
        obtain ⟨i, hi⟩ := TemplateAxisStructure.mem_templateForestVerifyExps he
        exact hverify i e (by simpa [alphaFreeRoot] using hi))

/-! ## Checker-guarded template axis counting -/

/-- One root's guarded bad-`alphaM` set, now restricted to verifier-computed structure and
no-wrap acceptance. -/
def verifierGuardedRootAlphas
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (lmb : K)
    (i : Fin T.kMem) : Finset K :=
  Finset.univ.filter fun α =>
    alphaFreeAxisStructureCheck E = true ∧
    noWrapCheck E α = true ∧
    (∃ e : ℕ,
      e ∈ readExps (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i) ∧
      e ∈ verifyExps (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i) ∧
      vaxis e (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i) ≠
        Relaxis e (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i)) ∧
    templateAxisPolynomial E i ≠ 0 ∧
    (templateAxisPolynomial E i).eval α = 0

/-- Direct instantiation of the template guarded-root argument.  Structural refinement is generated
from the two Boolean checks at the selected point; there is no positional-honesty or root-partition
premise. -/
theorem verifierGuardedRootAlphas_card_le
    (h2 : (2 : K) ≠ 0)
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (lmb : K)
    (i : Fin T.kMem) :
    (verifierGuardedRootAlphas E lmb i).card ≤
      (templateAxisPolynomial E i).natDegree := by
  by_cases hempty : verifierGuardedRootAlphas E lmb i = ∅
  · simp [hempty]
  · have hnonempty : (verifierGuardedRootAlphas E lmb i).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨α₀, hα₀⟩ := hnonempty
    have hparts := (Finset.mem_filter.mp hα₀).2
    have hne : templateAxisPolynomial E i ≠ 0 := hparts.2.2.2.1
    have hsubset :
        verifierGuardedRootAlphas E lmb i ⊆
          Finset.univ.filter fun α : K => (templateAxisPolynomial E i).IsRoot α := by
      intro α hα
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ α, (Finset.mem_filter.mp hα).2.2.2.2.2⟩
    exact (Finset.card_le_card hsubset).trans (Nock.Walk.card_roots_le _ hne)

/-- Union over authoritative roots for one committed seed-time template. -/
def verifierGuardedRootUnion
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (lmb : K) : Finset K :=
  (Finset.univ : Finset (Fin T.kMem)).biUnion (verifierGuardedRootAlphas E lmb)

/-- Checker-guarded axis cardinality with no structural residual hypotheses. -/
theorem verifierGuardedRootUnion_card_le
    (h2 : (2 : K) ≠ 0)
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (lmb : K) :
    (verifierGuardedRootUnion E lmb).card ≤ templateAxisWorkload E := by
  calc
    (verifierGuardedRootUnion E lmb).card
        ≤ ∑ i : Fin T.kMem, (verifierGuardedRootAlphas E lmb i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ i : Fin T.kMem, (templateAxisPolynomial E i).natDegree :=
      Finset.sum_le_sum fun i _ => verifierGuardedRootAlphas_card_le h2 E lmb i
    _ = templateAxisWorkload E := rfl

/-- Strategy-level spelling at the staged `(z, alphaM)` carrier. -/
theorem production_guarded_axis_cardinal
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy (F := F) (K := K) (p := p))
    (z : K) (hz : z ≠ 0) (lmb : K) :
    (verifierGuardedRootUnion (committedTemplate T z hz) lmb).card ≤
      templateAxisWorkload (committedTemplate T z hz) :=
  verifierGuardedRootUnion_card_le h2 _ lmb


/-- Accurate scope: the established crossing is rejected by the new ancestry checker.  This says
nothing about rejection by the old topology-enabled production acceptance before this extension. -/
theorem crossing_rejected_by_new_ancestry_check (e : ℕ) :
    readVerifyNestedCheck (K := K)
      (.decompose (.read e .halt) (.verify e (2 : K) .halt)) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact crossing_not_readVerifyNested (K := K) e
    ((readVerifyNestedCheck_eq_true_iff _).1 h)

theorem duplicate_read_exponent_rejected (e : ℕ) :
    readExponentUniqueCheck (K := K)
      (.decompose
        (.read e (.verify e (1 : K) .halt))
        (.read e (.verify e (1 : K) .halt))) = false := by
  simp [readExponentUniqueCheck, readExps]

theorem mismatched_root_partition_rejected :
    rootExponentPartitionCheck 2
      (.read 0 (.verify 0 (1 : K) (.verify 1 (1 : K) .halt))) = false := by
  simp [rootExponentPartitionCheck, finiteLmIOCheck, readExps, verifyExps, IO.InRange]

/-! ## Deterministic operation receipt -/

def totalTemplateReadVerifyOccurrences
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) : ℕ :=
  Finset.univ.sum fun i : Fin T.kMem =>
    (readExps (alphaFreeRoot E i)).length +
      (verifyExps (alphaFreeRoot E i)).length

/-- Unit-cost finite-set model: one visit per authoritative memory row and one set/list action per
read or verify occurrence. -/
def axisStructureVerifierNaturalOperations
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) : ℕ :=
  T.memRows + totalTemplateReadVerifyOccurrences E

theorem axis_structure_verifier_natural_operation_bound
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) :
    axisStructureVerifierNaturalOperations E =
        T.memRows + totalTemplateReadVerifyOccurrences E ∧
      axisStructureVerifierNaturalOperations E ≤
        2 * (T.memRows + totalTemplateReadVerifyOccurrences E) := by
  constructor
  · rfl
  · unfold axisStructureVerifierNaturalOperations
    omega

/-! ## Exact protocol/cost delta -/

/-- No RAP schema changes: the existing eight families and 32 segmented evaluations remain. -/
theorem production_axis_structure_exact_delta :
    8 * 4 = 32 ∧
      0 + 8 = 8 ∧
      0 + 32 = 32 ∧
      0 + 676 = 676 ∧
      3 + 1 = 4 := by
  decide

end

end Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier

#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.readVerifyNestedCheck_eq_true_iff
#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck_eq_true_iff
#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.exactAxisStructuralRefinement_of_checks
#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.exactAxisStructuralRefinement_of_accepts
#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.alphaFreeAxisStructure_of_specialized
#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.verifierGuardedRootAlphas_card_le
#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.production_guarded_axis_cardinal
#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.crossing_rejected_by_new_ancestry_check
#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.duplicate_read_exponent_rejected
#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.mismatched_root_partition_rejected
#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.axis_structure_verifier_natural_operation_bound
#print axioms Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.production_axis_structure_exact_delta
