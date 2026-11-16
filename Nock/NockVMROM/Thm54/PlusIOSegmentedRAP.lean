import Nock.NockVMROM.Thm54.ExactCanonicalRAP
import Nock.NockVMROM.Thm54.JointCoins

/-!
# Exact segmented table, walk, and IO RAP families

This module promotes the compiled `+IO` substrate without pretending that the resulting
heterogeneous family is one monolithic RAP.  The table and walk RAPs are over `K`; the IO RAPs
are over `RatFunc (RatFunc K)`.  Composition is the conjunction of six ordinary RAP families,
with explicit, pairwise-disjoint local column embeddings.

The construction is indexed by one `ExactCanonicalRAPProblem`, so every table, walk, and IO
object uses the same exact configuration and execution.  IO endpoints are public family data.
An IO assignment is not inferred from `ChainedSemanticExactLanguage`: construction from the
language endpoint explicitly requires `IO.LIO` (or a `SemanticIOWitness` that supplies it).

## `1-1*` scope

The disjoint local bookkeeping widths proved here are `94 + 6 + 2 = 102` and
`36 + 6 + 3 = 45`, strictly below the paper's named `199` and `196` widths.  Moreover,
`ExactConfig.eDeg = 1`; the paper's `e = 3` translator is not present.  Accordingly this module
exports no final Theorem 5.4 alias and no total-width claim across the two different fields.
-/

namespace Nock.NockVMROM.Thm54

open Classical
open Nock Framework Framework.Reify Framework.Thm54
open Nock.Reified
open scoped Polynomial

noncomputable section

/-! ## Generic conjunction of ordinary RAPs with explicit column embeddings -/

/-- A family of ordinary RAPs embedded into a common local column index.

The common index is only bookkeeping for assignments over one field.  In particular, separate
`EmbeddedRAPFamily` values are used below for the base field and the IO accumulator field. -/
structure EmbeddedRAPFamily (L Col Idx : Type*) [Field L] where
  rap : Idx → RAP L
  columnEmbedding : ∀ i, Fin (rap i).w ↪ Col

namespace EmbeddedRAPFamily

variable {L Col Idx : Type*} [Field L]

def pullAssignment (A : Col → L[X]) (e : Fin n ↪ Col) : Fin n → L[X] :=
  fun j => A (e j)

def Satisfies (R : EmbeddedRAPFamily L Col Idx) (A : Col → L[X]) : Prop :=
  ∀ i, (R.rap i).Satisfies (pullAssignment A (R.columnEmbedding i))

theorem satisfies_iff_conjunction (R : EmbeddedRAPFamily L Col Idx)
    (A : Col → L[X]) :
    R.Satisfies A ↔
      ∀ i, (R.rap i).Satisfies (pullAssignment A (R.columnEmbedding i)) :=
  Iff.rfl

end EmbeddedRAPFamily

/-! ## Explicit disjoint local columns -/

abbrev ComputePlusIOColumn :=
  Sum (Fin Trans.computeAIRchained.numTraceCols)
    (Sum (Fin Trans.walkAIR.numTraceCols) (Fin Trans.ioProgAIR.numTraceCols))

abbrev MemoryPlusIOColumn :=
  Sum (Fin 36)
    (Sum (Fin Trans.walkAIR.numTraceCols) (Fin Trans.ioMemAIR.numTraceCols))

def computeTableColumnEmbedding :
    Fin Trans.computeAIRchained.numTraceCols ↪ ComputePlusIOColumn where
  toFun := Sum.inl
  inj' := by
    intro a b h
    exact Sum.inl.inj h

def computeWalkColumnEmbedding :
    Fin Trans.walkAIR.numTraceCols ↪ ComputePlusIOColumn where
  toFun := fun j => Sum.inr (Sum.inl j)
  inj' := by
    intro a b h
    exact Sum.inl.inj (Sum.inr.inj h)

def computeIOColumnEmbedding :
    Fin Trans.ioProgAIR.numTraceCols ↪ ComputePlusIOColumn where
  toFun := fun j => Sum.inr (Sum.inr j)
  inj' := by
    intro a b h
    exact Sum.inr.inj (Sum.inr.inj h)

def memoryTableColumnEmbedding :
    Fin 36 ↪ MemoryPlusIOColumn where
  toFun := Sum.inl
  inj' := by
    intro a b h
    exact Sum.inl.inj h

def memoryWalkColumnEmbedding :
    Fin Trans.walkAIR.numTraceCols ↪ MemoryPlusIOColumn where
  toFun := fun j => Sum.inr (Sum.inl j)
  inj' := by
    intro a b h
    exact Sum.inl.inj (Sum.inr.inj h)

def memoryIOColumnEmbedding :
    Fin Trans.ioMemAIR.numTraceCols ↪ MemoryPlusIOColumn where
  toFun := fun j => Sum.inr (Sum.inr j)
  inj' := by
    intro a b h
    exact Sum.inr.inj (Sum.inr.inj h)

theorem compute_disjoint_width :
    Fintype.card ComputePlusIOColumn = 102 := by
  have htable : Trans.computeAIRchained.numTraceCols = 94 := by
    simpa only [kindSeg_numTraceCols] using comp_all_seg_cols.1
  simp only [ComputePlusIOColumn]
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, htable,
    Trans.walkAIR_numTraceCols, Trans.ioProgAIR_numTraceCols]

theorem memory_disjoint_width :
    Fintype.card MemoryPlusIOColumn = 45 := by
  decide

theorem compute_width_lt_paper_199 :
    Fintype.card ComputePlusIOColumn < 199 := by
  rw [compute_disjoint_width]
  omega

theorem memory_width_lt_paper_196 :
    Fintype.card MemoryPlusIOColumn < 196 := by
  rw [memory_disjoint_width]
  omega

theorem compute_width_ne_paper_199 :
    Fintype.card ComputePlusIOColumn ≠ 199 :=
  ne_of_lt compute_width_lt_paper_199

theorem memory_width_ne_paper_196 :
    Fintype.card MemoryPlusIOColumn ≠ 196 :=
  ne_of_lt memory_width_lt_paper_196

theorem compute_table_walk_columns_disjoint :
    Set.range computeTableColumnEmbedding ∩ Set.range computeWalkColumnEmbedding = ∅ := by
  ext x
  constructor
  · rintro ⟨⟨_, rfl⟩, ⟨_, h⟩⟩
    cases h
  · simp

theorem compute_table_io_columns_disjoint :
    Set.range computeTableColumnEmbedding ∩ Set.range computeIOColumnEmbedding = ∅ := by
  ext x
  constructor
  · rintro ⟨⟨_, rfl⟩, ⟨_, h⟩⟩
    cases h
  · simp

theorem compute_walk_io_columns_disjoint :
    Set.range computeWalkColumnEmbedding ∩ Set.range computeIOColumnEmbedding = ∅ := by
  ext x
  constructor
  · rintro ⟨⟨_, rfl⟩, ⟨_, h⟩⟩
    cases h
  · simp

theorem memory_table_walk_columns_disjoint :
    Set.range memoryTableColumnEmbedding ∩ Set.range memoryWalkColumnEmbedding = ∅ := by
  ext x
  constructor
  · rintro ⟨⟨_, rfl⟩, ⟨_, h⟩⟩
    cases h
  · simp

theorem memory_table_io_columns_disjoint :
    Set.range memoryTableColumnEmbedding ∩ Set.range memoryIOColumnEmbedding = ∅ := by
  ext x
  constructor
  · rintro ⟨⟨_, rfl⟩, ⟨_, h⟩⟩
    cases h
  · simp

theorem memory_walk_io_columns_disjoint :
    Set.range memoryWalkColumnEmbedding ∩ Set.range memoryIOColumnEmbedding = ∅ := by
  ext x
  constructor
  · rintro ⟨⟨_, rfl⟩, ⟨_, h⟩⟩
    cases h
  · simp

/-! ## One exact-problem-indexed heterogeneous family -/

abbrev IOField (K : Type*) [Field K] := RatFunc (RatFunc K)

/-- Exact table/walk/IO family data for one configuration and one execution.

The node encoders are explicit because no canonical finite-coordinate encoders for the full
compute and memory labels are currently exported.  Their injectivity is load-bearing for the
walk soundness interface.  The two walk recurrences have separate `α` challenges, while one
walk-node RLC challenge is shared between them.  None of these three walk challenges is borrowed
from the table challenge vector. -/
structure PlusIOSegmentedFamily (F K : Type) [Field F] [Field K] [Algebra F K] where
  problem : ExactCanonicalRAPProblem F K
  /-- Compute-walk recurrence challenge `αc`, separate from the table timestamp challenge. -/
  computeWalkAlpha : K
  /-- Memory-walk recurrence challenge `αm`, separate from `αc` and the table timestamp. -/
  memoryWalkAlpha : K
  /-- Shared compute/memory walk-node RLC challenge, separate from the table record RLC. -/
  walkGamma : K
  compNodeWidth : ℕ
  compNodeEncode :
    (ComputeTable.State × ComputeTable.DTcomp K) → Fin compNodeWidth → K
  /-- The compute encoder determines the paper's `LT_comp` projection.  H1.W
 replaced full-row injectivity: the deployed label is the ten-coordinate
  projection, which is injective on `computeLabelOf` and on nothing more. -/
  compNodeEncode_labelOf :
    ∀ a b, compNodeEncode a = compNodeEncode b →
      ComputeTable.computeLabelOf a = ComputeTable.computeLabelOf b
  memNodeWidth : ℕ
  memNodeEncode :
    (MemoryTable.MState × MemoryTable.DTmem K) → Fin memNodeWidth → K
  /-- The memory encoder determines the paper's `x^mem` projection.  H1.W
  memory replaced full-row injectivity: the deployed label is the six-coordinate
  projection, which is injective on `memoryLabelOf` and on nothing more. -/
  memNodeEncode_labelOf :
    ∀ a b, memNodeEncode a = memNodeEncode b →
      MemoryTable.memoryLabelOf a = MemoryTable.memoryLabelOf b
  /-- Public terminal value of the program-side IO accumulator. -/
  requests : IOField K
  /-- Public initial value of the memory-side IO accumulator. -/
  responses : IOField K
  /-- Public terminal value of the memory-side IO accumulator. -/
  outMem : IOField K
  progIO_capacity :
    problem.exec.derivedRequestIO.length + 1 ≤ 2 ^ problem.cfg.orbit.h
  memIO_capacity :
    problem.exec.derivedResponseIO.length + 1 ≤ 2 ^ problem.cfg.orbit.h

namespace PlusIOSegmentedFamily

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Replace only the public IO endpoint data; all exact problem, encoder, and capacity data remain
definitionally the same. -/
def withIOEndpoints (R : PlusIOSegmentedFamily F K)
    (requests responses outMem : IOField K) : PlusIOSegmentedFamily F K :=
  { R with requests := requests, responses := responses, outMem := outMem }

/-- Change only the three walk challenges.  The exact table problem, execution, node encoders,
and IO data remain definitionally fixed.  The argument order follows the joint coin layout:
`(αc, γw, αm)`. -/
def withWalkChallenges (R : PlusIOSegmentedFamily F K)
    (computeWalkAlpha walkGamma memoryWalkAlpha : K) : PlusIOSegmentedFamily F K :=
  { R with
      computeWalkAlpha := computeWalkAlpha
      memoryWalkAlpha := memoryWalkAlpha
      walkGamma := walkGamma }

@[simp]
theorem withWalkChallenges_problem (R : PlusIOSegmentedFamily F K)
    (computeWalkAlpha walkGamma memoryWalkAlpha : K) :
    (R.withWalkChallenges computeWalkAlpha walkGamma memoryWalkAlpha).problem = R.problem :=
  rfl

/-- Instantiate the walk layer at joint coins `((αc, γw), (αm, z))`.

Only `(αc, γw, αm)` enters this fixed-execution family.  The NPR coin `z` remains available as
`nprSeed ω` to the separate seed-indexed commitment/label strategy; it does not mutate the table
timestamp, table record-RLC challenge, or the already-fixed exact problem. -/
def atJointCoins (R : PlusIOSegmentedFamily F K)
    (ω : JointCoins K) : PlusIOSegmentedFamily F K :=
  R.withWalkChallenges (alphaC ω) (gamma ω) (alphaM ω)

@[simp]
theorem withIOEndpoints_computeWalkAlpha (R : PlusIOSegmentedFamily F K)
    (requests responses outMem : IOField K) :
    (R.withIOEndpoints requests responses outMem).computeWalkAlpha = R.computeWalkAlpha :=
  rfl

@[simp]
theorem withIOEndpoints_memoryWalkAlpha (R : PlusIOSegmentedFamily F K)
    (requests responses outMem : IOField K) :
    (R.withIOEndpoints requests responses outMem).memoryWalkAlpha = R.memoryWalkAlpha :=
  rfl

@[simp]
theorem withIOEndpoints_walkGamma (R : PlusIOSegmentedFamily F K)
    (requests responses outMem : IOField K) :
    (R.withIOEndpoints requests responses outMem).walkGamma = R.walkGamma :=
  rfl

@[simp]
theorem atJointCoins_problem (R : PlusIOSegmentedFamily F K) (ω : JointCoins K) :
    (R.atJointCoins ω).problem = R.problem :=
  rfl

@[simp]
theorem atJointCoins_computeWalkAlpha (R : PlusIOSegmentedFamily F K) (ω : JointCoins K) :
    (R.atJointCoins ω).computeWalkAlpha = alphaC ω :=
  rfl

@[simp]
theorem atJointCoins_memoryWalkAlpha (R : PlusIOSegmentedFamily F K) (ω : JointCoins K) :
    (R.atJointCoins ω).memoryWalkAlpha = alphaM ω :=
  rfl

@[simp]
theorem atJointCoins_walkGamma (R : PlusIOSegmentedFamily F K) (ω : JointCoins K) :
    (R.atJointCoins ω).walkGamma = gamma ω :=
  rfl

/-- Joint-coin instantiation leaves all table challenge coordinates untouched.  In particular,
the sampled `z` is consumed by the separate seed-indexed commitment strategy, not by mutating
this fixed exact problem. -/
theorem atJointCoins_preserves_table_challenges
    (R : PlusIOSegmentedFamily F K) (ω : JointCoins K) :
    (R.atJointCoins ω).problem.cfg.challenges.α = R.problem.cfg.challenges.α ∧
      (R.atJointCoins ω).problem.cfg.challenges.γ = R.problem.cfg.challenges.γ ∧
      (R.atJointCoins ω).problem.cfg.challenges.z = R.problem.cfg.challenges.z :=
  ⟨rfl, rfl, rfl⟩

def walkChallengeValuation (α : K) : ℕ → K
  | 0 => α
  | _ => 0

def computeNodeVal (R : PlusIOSegmentedFamily F K)
    (t : Nock.Walk.NTree (ComputeTable.State × ComputeTable.DTcomp K)) : K :=
  Nock.Walk.rlc R.walkGamma (R.compNodeEncode t.label)

def memoryNodeVal (R : PlusIOSegmentedFamily F K)
    (t : Nock.Walk.NTree (MemoryTable.MState × MemoryTable.DTmem K)) : K :=
  Nock.Walk.rlc R.walkGamma (R.memNodeEncode t.label)

/-- Both walk node values use the explicit shared walk `γw`, not the table record-RLC `γ`. -/
theorem walk_node_values_share_gamma (R : PlusIOSegmentedFamily F K)
    (ct : Nock.Walk.NTree (ComputeTable.State × ComputeTable.DTcomp K))
    (mt : Nock.Walk.NTree (MemoryTable.MState × MemoryTable.DTmem K)) :
    R.computeNodeVal ct =
        Nock.Walk.rlc R.walkGamma (R.compNodeEncode ct.label) ∧
      R.memoryNodeVal mt =
        Nock.Walk.rlc R.walkGamma (R.memNodeEncode mt.label) :=
  ⟨rfl, rfl⟩

def computeWalkRows (R : PlusIOSegmentedFamily F K) :
    List (Nock.Walk.NTree (ComputeTable.State × ComputeTable.DTcomp K)) :=
  Nock.Walk.bfsForest [R.problem.exec.computeTree]

def memoryWalkRows (R : PlusIOSegmentedFamily F K) :
    List (Nock.Walk.NTree (MemoryTable.MState × MemoryTable.DTmem K)) :=
  Nock.Walk.bfsForest R.problem.exec.memoryForest

def computeWalkSeed (R : PlusIOSegmentedFamily F K) : K :=
  Nock.Walk.curCol R.computeNodeVal R.computeWalkRows 1 * R.computeWalkAlpha

noncomputable def memoryWalkSeed (R : PlusIOSegmentedFamily F K) : K :=
  (Nock.Walk.nodeListP
    (Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows) R.problem.cfg.kMem).eval
      R.memoryWalkAlpha

def computeWalkPublicValuation (R : PlusIOSegmentedFamily F K) : ℕ → K
  | 0 => R.computeWalkAlpha
  | 1 => R.computeWalkSeed
  | _ => 0

noncomputable def memoryWalkPublicValuation (R : PlusIOSegmentedFamily F K) : ℕ → K
  | 0 => R.memoryWalkAlpha ^ R.problem.cfg.kMem
  | 1 => R.memoryWalkSeed
  | _ => 0

noncomputable def computeWalkParams (R : PlusIOSegmentedFamily F K) :
    SegmentedRAPParams K where
  chalVal := walkChallengeValuation R.computeWalkAlpha
  pubVal := R.computeWalkPublicValuation
  eDeg := R.problem.cfg.eDeg
  hExp := R.problem.cfg.orbit.h
  ω := R.problem.cfg.orbit.ω
  βcoset := R.problem.cfg.orbit.βcoset
  domain := R.problem.cfg.computeDomain
  βcoset_ne_zero := R.problem.cfg.orbit.βcoset_ne_zero
  hExp_pos := R.problem.cfg.orbit_h_pos

noncomputable def memoryWalkParams (R : PlusIOSegmentedFamily F K) :
    SegmentedRAPParams K where
  chalVal := walkChallengeValuation R.memoryWalkAlpha
  pubVal := R.memoryWalkPublicValuation
  eDeg := R.problem.cfg.eDeg
  hExp := R.problem.cfg.orbit.h
  ω := R.problem.cfg.orbit.ω
  βcoset := R.problem.cfg.orbit.βcoset
  domain := R.problem.cfg.memoryDomain
  βcoset_ne_zero := R.problem.cfg.orbit.βcoset_ne_zero
  hExp_pos := R.problem.cfg.orbit_h_pos

/-- Changing `αc` cannot change any memory-walk RAP parameter. -/
theorem memoryWalkParams_independent_computeWalkAlpha
    (R : PlusIOSegmentedFamily F K) (αc₁ αc₂ γw αm : K) :
    (R.withWalkChallenges αc₁ γw αm).memoryWalkParams =
      (R.withWalkChallenges αc₂ γw αm).memoryWalkParams :=
  rfl

/-- Changing `αm` cannot change any compute-walk RAP parameter. -/
theorem computeWalkParams_independent_memoryWalkAlpha
    (R : PlusIOSegmentedFamily F K) (αc γw αm₁ αm₂ : K) :
    (R.withWalkChallenges αc γw αm₁).computeWalkParams =
      (R.withWalkChallenges αc γw αm₂).computeWalkParams :=
  rfl

/-- The explicit walk-node challenge can vary while the exact table problem—and therefore its
record-RLC challenge—remains fixed. -/
theorem walkGamma_independent_recordGamma
    (R : PlusIOSegmentedFamily F K) (αc γw αm : K) :
    (R.withWalkChallenges αc γw αm).walkGamma = γw ∧
      (R.withWalkChallenges αc γw αm).problem.cfg.challenges.γ =
        R.problem.cfg.challenges.γ :=
  ⟨rfl, rfl⟩


theorem walk_challenge_discrimination
    (R : PlusIOSegmentedFamily F K)
    (αc₁ αc₂ γw αm₁ αm₂ : K) :
    (R.withWalkChallenges αc₁ γw αm₁).memoryWalkParams =
        (R.withWalkChallenges αc₂ γw αm₁).memoryWalkParams ∧
      (R.withWalkChallenges αc₁ γw αm₁).computeWalkParams =
        (R.withWalkChallenges αc₁ γw αm₂).computeWalkParams ∧
      (R.withWalkChallenges αc₁ γw αm₁).walkGamma = γw ∧
      (R.withWalkChallenges αc₁ γw αm₁).problem.cfg.challenges.γ =
        R.problem.cfg.challenges.γ :=
  ⟨rfl, rfl, rfl, rfl⟩

noncomputable def computeTableRAP (R : PlusIOSegmentedFamily F K)
    (kind : ConstraintKind) : RAP K :=
  (exactCanonicalProgParams (F := F) (K := K) R.problem).rap
    Trans.computeAIRchained kind

noncomputable def memoryTableRAP (R : PlusIOSegmentedFamily F K)
    (kind : ConstraintKind) : RAP K :=
  (exactCanonicalMemParams (F := F) (K := K) R.problem).rap
    (Trans.memoryAIRchained (K := K)) kind

noncomputable def computeWalkRAP (R : PlusIOSegmentedFamily F K)
    (kind : ConstraintKind) : RAP K :=
  R.computeWalkParams.rap Trans.walkAIR kind

noncomputable def memoryWalkRAP (R : PlusIOSegmentedFamily F K)
    (kind : ConstraintKind) : RAP K :=
  R.memoryWalkParams.rap Trans.walkAIR kind

theorem table_walk_common_base_parameters (R : PlusIOSegmentedFamily F K)
    (kind : ConstraintKind) :
    (R.computeTableRAP kind).e = (R.computeWalkRAP kind).e ∧
      (R.computeTableRAP kind).h = (R.computeWalkRAP kind).h ∧
      (R.computeTableRAP kind).ω = (R.computeWalkRAP kind).ω ∧
      (R.computeTableRAP kind).β = (R.computeWalkRAP kind).β ∧
      (R.memoryTableRAP kind).e = (R.memoryWalkRAP kind).e ∧
      (R.memoryTableRAP kind).h = (R.memoryWalkRAP kind).h ∧
      (R.memoryTableRAP kind).ω = (R.memoryWalkRAP kind).ω ∧
      (R.memoryTableRAP kind).β = (R.memoryWalkRAP kind).β := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem airToRAP_width_is_e_independent (air : AIR) (chalVal pubVal : ℕ → K)
    (e₁ e₂ h : ℕ) (ω β : K) (H : Finset K) (hβ : β ≠ 0) (hh : 1 ≤ h) :
    (airToRAP air chalVal pubVal e₁ h ω β H hβ hh).w =
      (airToRAP air chalVal pubVal e₂ h ω β H hβ hh).w ∧
    (airToRAP air chalVal pubVal e₁ h ω β H hβ hh).w = air.numTraceCols := by
  exact ⟨rfl, rfl⟩

theorem airToRAP_is_single_round (air : AIR) (chalVal pubVal : ℕ → K)
    (e h : ℕ) (ω β : K) (H : Finset K) (hβ : β ≠ 0) (hh : 1 ≤ h) :
    (airToRAP air chalVal pubVal e h ω β H hβ hh).k = 1 :=
  rfl

/-! ### IO-side RAPs over the actual accumulator field -/

noncomputable def ioBaseDomain (D : OrbitDomain K) (records : ℕ) :
    ConstraintKind → Finset K
  | .row => D.rowDomain (records + 1)
  | .transition => D.transitionDomain (records + 1) (by omega)
  | .boundary => D.boundaryDomain
  | .terminal => D.terminalDomain (records + 1) (by omega)

noncomputable def liftFinsetToIO (H : Finset K) : Finset (IOField K) :=
  H.image (algebraMap K (IOField K))

noncomputable def progIOParams (R : PlusIOSegmentedFamily F K) :
    SegmentedRAPParams (IOField K) where
  chalVal := fun _ => 0
  pubVal := fun
    | 0 => R.requests
    | _ => 0
  eDeg := R.problem.cfg.eDeg
  hExp := R.problem.cfg.orbit.h
  ω := algebraMap K (IOField K) R.problem.cfg.orbit.ω
  βcoset := algebraMap K (IOField K) R.problem.cfg.orbit.βcoset
  domain := fun kind =>
    liftFinsetToIO (ioBaseDomain R.problem.cfg.orbit
      R.problem.exec.derivedRequestIO.length kind)
  βcoset_ne_zero := by
    intro hzero
    apply R.problem.cfg.orbit.βcoset_ne_zero
    apply (algebraMap K (IOField K)).injective
    simpa using hzero
  hExp_pos := R.problem.cfg.orbit_h_pos

noncomputable def memIOParams (R : PlusIOSegmentedFamily F K) :
    SegmentedRAPParams (IOField K) where
  chalVal := fun _ => 0
  pubVal := fun
    | 0 => R.responses
    | 1 => R.outMem
    | _ => 0
  eDeg := R.problem.cfg.eDeg
  hExp := R.problem.cfg.orbit.h
  ω := algebraMap K (IOField K) R.problem.cfg.orbit.ω
  βcoset := algebraMap K (IOField K) R.problem.cfg.orbit.βcoset
  domain := fun kind =>
    liftFinsetToIO (ioBaseDomain R.problem.cfg.orbit
      R.problem.exec.derivedResponseIO.length kind)
  βcoset_ne_zero := by
    intro hzero
    apply R.problem.cfg.orbit.βcoset_ne_zero
    apply (algebraMap K (IOField K)).injective
    simpa using hzero
  hExp_pos := R.problem.cfg.orbit_h_pos

noncomputable def computeIORAP (R : PlusIOSegmentedFamily F K)
    (kind : ConstraintKind) : RAP (IOField K) :=
  R.progIOParams.rap Trans.ioProgAIR kind

noncomputable def memoryIORAP (R : PlusIOSegmentedFamily F K)
    (kind : ConstraintKind) : RAP (IOField K) :=
  R.memIOParams.rap Trans.ioMemAIR kind

inductive TableWalkPart
  | table
  | walk
deriving DecidableEq

noncomputable def computeTableWalkFamily (R : PlusIOSegmentedFamily F K) :
    EmbeddedRAPFamily K ComputePlusIOColumn (TableWalkPart × ConstraintKind) where
  rap
    | (.table, kind) => R.computeTableRAP kind
    | (.walk, kind) => R.computeWalkRAP kind
  columnEmbedding
    | (.table, _) => computeTableColumnEmbedding
    | (.walk, _) => computeWalkColumnEmbedding

noncomputable def memoryTableWalkFamily (R : PlusIOSegmentedFamily F K) :
    EmbeddedRAPFamily K MemoryPlusIOColumn (TableWalkPart × ConstraintKind) where
  rap
    | (.table, kind) => R.memoryTableRAP kind
    | (.walk, kind) => R.memoryWalkRAP kind
  columnEmbedding
    | (.table, _) => memoryTableColumnEmbedding
    | (.walk, _) => memoryWalkColumnEmbedding

noncomputable def computeIOFamily (R : PlusIOSegmentedFamily F K) :
    EmbeddedRAPFamily (IOField K) ComputePlusIOColumn ConstraintKind where
  rap := R.computeIORAP
  columnEmbedding := fun _ => computeIOColumnEmbedding

noncomputable def memoryIOFamily (R : PlusIOSegmentedFamily F K) :
    EmbeddedRAPFamily (IOField K) MemoryPlusIOColumn ConstraintKind where
  rap := R.memoryIORAP
  columnEmbedding := fun _ => memoryIOColumnEmbedding

/-- Compute-side heterogeneous satisfaction: a base-field table/walk conjunction and a separate
IO-field conjunction, not one RAP. -/
def ComputeSatisfies (R : PlusIOSegmentedFamily F K)
    (baseAssignment : ComputePlusIOColumn → K[X])
    (ioAssignment : ComputePlusIOColumn → (IOField K)[X]) : Prop :=
  R.computeTableWalkFamily.Satisfies baseAssignment ∧
    R.computeIOFamily.Satisfies ioAssignment

/-- Memory-side heterogeneous satisfaction, again kept in its two actual fields. -/
def MemorySatisfies (R : PlusIOSegmentedFamily F K)
    (baseAssignment : MemoryPlusIOColumn → K[X])
    (ioAssignment : MemoryPlusIOColumn → (IOField K)[X]) : Prop :=
  R.memoryTableWalkFamily.Satisfies baseAssignment ∧
    R.memoryIOFamily.Satisfies ioAssignment

theorem actual_component_widths (R : PlusIOSegmentedFamily F K)
    (kind : ConstraintKind) :
    (R.computeTableRAP kind).w = 94 ∧
      (R.computeWalkRAP kind).w = 6 ∧
      (R.computeIORAP kind).w = 2 ∧
      (R.memoryTableRAP kind).w = 36 ∧
      (R.memoryWalkRAP kind).w = 6 ∧
      (R.memoryIORAP kind).w = 3 := by
  have hcomp : Trans.computeAIRchained.numTraceCols = 94 := by
    simpa only [kindSeg_numTraceCols] using comp_all_seg_cols.1
  have hmem : (Trans.memoryAIRchained (K := K)).numTraceCols = 36 := by
    simpa only [kindSeg_numTraceCols] using mem_seg_cols.1
  exact ⟨hcomp, Trans.walkAIR_numTraceCols, Trans.ioProgAIR_numTraceCols,
    hmem, Trans.walkAIR_numTraceCols, Trans.ioMemAIR_numTraceCols⟩

theorem io_common_mapped_parameters (R : PlusIOSegmentedFamily F K)
    (kind : ConstraintKind) :
    (R.computeIORAP kind).e = (R.computeTableRAP kind).e ∧
      (R.computeIORAP kind).h = (R.computeTableRAP kind).h ∧
      (R.computeIORAP kind).ω =
        algebraMap K (IOField K) (R.computeTableRAP kind).ω ∧
      (R.computeIORAP kind).β =
        algebraMap K (IOField K) (R.computeTableRAP kind).β ∧
      (R.memoryIORAP kind).e = (R.memoryTableRAP kind).e ∧
      (R.memoryIORAP kind).h = (R.memoryTableRAP kind).h ∧
      (R.memoryIORAP kind).ω =
        algebraMap K (IOField K) (R.memoryTableRAP kind).ω ∧
      (R.memoryIORAP kind).β =
        algebraMap K (IOField K) (R.memoryTableRAP kind).β := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem progIONodes_injective (R : PlusIOSegmentedFamily F K) :
    Function.Injective
      (fun i : Fin (R.problem.exec.derivedRequestIO.length + 1) =>
        algebraMap K (IOField K) (R.problem.cfg.orbit.orbitPoint i)) :=
  (algebraMap K (IOField K)).injective.comp
    (R.problem.cfg.orbit.orbitPoint_injective R.progIO_capacity)

theorem memIONodes_injective (R : PlusIOSegmentedFamily F K) :
    Function.Injective
      (fun i : Fin (R.problem.exec.derivedResponseIO.length + 1) =>
        algebraMap K (IOField K) (R.problem.cfg.orbit.orbitPoint i)) :=
  (algebraMap K (IOField K)).injective.comp
    (R.problem.cfg.orbit.orbitPoint_injective R.memIO_capacity)

/-- The last two conjuncts pin the shipped translator metadata:
it is exactly `e = 1`, and therefore not the paper's `e = 3` translator. -/
theorem one_to_one_star_scope (R : PlusIOSegmentedFamily F K) :
    Fintype.card ComputePlusIOColumn = 102 ∧
      Fintype.card MemoryPlusIOColumn = 45 ∧
      Fintype.card ComputePlusIOColumn < 199 ∧
      Fintype.card MemoryPlusIOColumn < 196 ∧
      R.problem.cfg.eDeg = 1 ∧
      R.problem.cfg.eDeg ≠ 3 := by
  refine ⟨compute_disjoint_width, memory_disjoint_width,
    compute_width_lt_paper_199, memory_width_lt_paper_196,
    R.problem.cfg.eDeg_eq_one, ?_⟩
  rw [R.problem.cfg.eDeg_eq_one]
  norm_num

end PlusIOSegmentedFamily

/-! ## Canonical interpolation and same-execution assignments -/

noncomputable def encodeEnvTrace {L : Type*} [Field L] {n w : ℕ}
    (rows : Fin n → Env L) (nodes : Fin n → L) :
    Fin w → L[X] :=
  fun j => Lagrange.interpolate Finset.univ nodes (fun i => (rows i).trace j)

theorem encodeEnvTrace_eval_at_node {L : Type*} [Field L] {n w : ℕ}
    (rows : Fin n → Env L) (nodes : Fin n → L) (hnodes : Function.Injective nodes)
    (i : Fin n) (j : Fin w) :
    (encodeEnvTrace rows nodes j).eval (nodes i) = (rows i).trace j :=
  Lagrange.eval_interpolate_at_node
    (fun i => (rows i).trace j) hnodes.injOn (Finset.mem_univ i)

structure WalkAssignment (K : Type*) where
  ln : ℕ → K
  count : ℕ → K
  acc : ℕ → K

/-- One IO assignment over the exact execution's two derived IO lists.

This is explicit witness data, not a consequence of the plain chained language.  The constructors
below require either `IO.LIO` or `SemanticIOWitness`. -/
structure ExactDerivedIOAssignment {F K : Type} [Field F] [Field K] [Algebra F K]
    (R : PlusIOSegmentedFamily F K) (p : ℕ) [CharP K p] where
  multiplicity : Fin R.problem.exec.derivedResponseIO.length → ZMod p
  progAcc : ℕ → IOField K
  memAcc : ℕ → IOField K
  multiplicity_ne_zero : ∀ j, multiplicity j ≠ 0
  progSat :
    IO.ProgIOSat
      (fun i => SetEq.RLC (IO.listExt R.problem.exec.derivedRequestIO i))
      progAcc R.requests R.problem.exec.derivedRequestIO.length
  memSat :
    IO.MemIOSat
      (fun i => SetEq.RLC (IO.listExt R.problem.exec.derivedResponseIO i))
      (IO.castμ (𝔽 := K) multiplicity)
      memAcc R.responses R.outMem R.problem.exec.derivedResponseIO.length
  endpoints_agree : R.requests = R.responses
  memory_closes : R.outMem = 0

namespace ExactDerivedIOAssignment

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {R : PlusIOSegmentedFamily F K} {p : ℕ} [CharP K p]

theorem toIOSat (A : ExactDerivedIOAssignment R p) :
    IOSat p R.problem.exec.derivedRequestIO R.problem.exec.derivedResponseIO := by
  exact ⟨A.multiplicity, A.progAcc, A.memAcc, R.requests, R.responses, R.outMem,
    A.multiplicity_ne_zero, A.progSat, A.memSat, A.endpoints_agree, A.memory_closes⟩

/-- `IO.LIO` produces public endpoint values and one exact derived-IO assignment.  The result
updates only those public endpoint fields of the supplied structural family. -/
theorem exists_with_public_endpoints_of_LIO
    (R : PlusIOSegmentedFamily F K)
    (hKp : R.problem.cfg.Ksz < p)
    (hLIO : IO.LIO R.problem.cfg.Ksz
      R.problem.exec.derivedRequestIO R.problem.exec.derivedResponseIO) :
    ∃ requests responses outMem : IOField K,
      Nonempty (ExactDerivedIOAssignment
        (R.withIOEndpoints requests responses outMem) p) := by
  have hperm := hLIO.2.2
  have hKreq :
      IO.InRange R.problem.cfg.Ksz R.problem.exec.derivedRequestIO.length := by
    rw [hperm.length_eq]
    exact hLIO.1
  have hKresp :
      R.problem.exec.derivedResponseIO.length ≤ R.problem.cfg.Ksz :=
    hLIO.1.2
  have hreqnd : R.problem.exec.derivedRequestIO.Nodup :=
    hperm.nodup_iff.mpr hLIO.2.1
  have hrespnd : R.problem.exec.derivedResponseIO.Nodup :=
    hLIO.2.1
  obtain ⟨m, accP, accM, requests, responses, outMem, hm, hprog, hmem, hagree, hclose⟩ :=
    (IO.io_result_LIO R.problem.cfg.Ksz hKp
      R.problem.exec.derivedRequestIO R.problem.exec.derivedResponseIO
      hKreq hKresp hreqnd hrespnd).2 hLIO
  exact ⟨requests, responses, outMem,
    ⟨{ multiplicity := m
       progAcc := accP
       memAcc := accM
       multiplicity_ne_zero := hm
       progSat := hprog
       memSat := hmem
       endpoints_agree := hagree
       memory_closes := hclose }⟩⟩

/-- Semantic request uniqueness plus semantic exact acceptance supplies the required `LIO`.
There is intentionally no corresponding constructor from plain `ChainedSemanticExactLanguage`. -/
theorem exists_with_public_endpoints_of_semanticIOWitness
    (R : PlusIOSegmentedFamily F K)
    (hKp : R.problem.cfg.Ksz < p)
    (w : SemanticIOWitness R.problem.cfg R.problem.exec)
    (hsemantic : SemanticExactLanguage R.problem.cfg R.problem.exec) :
    ∃ requests responses outMem : IOField K,
      Nonempty (ExactDerivedIOAssignment
        (R.withIOEndpoints requests responses outMem) p) :=
  exists_with_public_endpoints_of_LIO R hKp
    (w.strongExactLanguage_of_semanticExactLanguage hsemantic).2.2

end ExactDerivedIOAssignment

/-- One assignment carrier for the one exact problem.  Its P4 auxiliaries, both walk assignments,
and one IO assignment all refer to `R.problem`, hence to the same `cfg` and `exec`. -/
structure PlusIOSameExecutionAssignment {F K : Type} [Field F] [Field K] [Algebra F K]
    (R : PlusIOSegmentedFamily F K) (p : ℕ) [CharP K p] where
  computeTableAux : ExactCanonicalProgAux R.problem
  memoryTableAux : ExactCanonicalMemAux R.problem
  computeWalk : WalkAssignment K
  memoryWalk : WalkAssignment K
  exactIO : ExactDerivedIOAssignment R p

namespace PlusIOSameExecutionAssignment

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

noncomputable def computeTableTrace (A : PlusIOSameExecutionAssignment R p) :
    Fin Trans.computeAIRchained.numTraceCols → K[X] :=
  exactCanonicalEncodeProg R.problem A.computeTableAux

noncomputable def memoryTableTrace (A : PlusIOSameExecutionAssignment R p) :
    Fin (Trans.memoryAIRchained (K := K)).numTraceCols → K[X] :=
  exactCanonicalEncodeMem R.problem A.memoryTableAux

noncomputable def computeWalkTrace (A : PlusIOSameExecutionAssignment R p) :
    Fin Trans.walkAIR.numTraceCols → K[X] :=
  encodeEnvTrace
    (fun i : Fin R.problem.cfg.compRows =>
      Trans.walkRowEnv
        (Nock.Walk.curCol R.computeNodeVal R.computeWalkRows)
        (Nock.Walk.chldCol R.computeNodeVal R.computeWalkRows)
        (Nock.Walk.foCol R.computeWalkRows)
        A.computeWalk.ln A.computeWalk.count A.computeWalk.acc
        R.computeWalkAlpha R.computeWalkSeed R.computeWalkAlpha
        ((i : ℕ) + 1))
    R.problem.cfg.compNodes

noncomputable def memoryWalkTrace (A : PlusIOSameExecutionAssignment R p) :
    Fin Trans.walkAIR.numTraceCols → K[X] :=
  encodeEnvTrace
    (fun i : Fin R.problem.cfg.memRows =>
      Trans.walkRowEnv
        (Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows)
        (Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
        (Nock.Walk.foCol R.memoryWalkRows)
        A.memoryWalk.ln A.memoryWalk.count A.memoryWalk.acc
        R.memoryWalkAlpha R.memoryWalkSeed
        (R.memoryWalkAlpha ^ R.problem.cfg.kMem)
        ((i : ℕ) + 1))
    R.problem.cfg.memNodes

noncomputable def computeIOTrace (A : PlusIOSameExecutionAssignment R p) :
    Fin Trans.ioProgAIR.numTraceCols → (IOField K)[X] :=
  encodeEnvTrace
    (fun i : Fin (R.problem.exec.derivedRequestIO.length + 1) =>
      Trans.ioProgRowEnv
        (fun q => SetEq.RLC (IO.listExt R.problem.exec.derivedRequestIO q))
        A.exactIO.progAcc R.requests i)
    (fun i => algebraMap K (IOField K) (R.problem.cfg.orbit.orbitPoint i))

noncomputable def memoryIOTrace (A : PlusIOSameExecutionAssignment R p) :
    Fin Trans.ioMemAIR.numTraceCols → (IOField K)[X] :=
  encodeEnvTrace
    (fun i : Fin (R.problem.exec.derivedResponseIO.length + 1) =>
      Trans.ioMemRowEnv
        (fun q => SetEq.RLC (IO.listExt R.problem.exec.derivedResponseIO q))
        (IO.castμ (𝔽 := K) A.exactIO.multiplicity)
        A.exactIO.memAcc R.responses R.outMem i)
    (fun i => algebraMap K (IOField K) (R.problem.cfg.orbit.orbitPoint i))

/-- The actual acceptance proposition is exactly the six ordinary RAP-family conjunction.
No cross-field monolithic RAP is asserted. -/
def Satisfies (A : PlusIOSameExecutionAssignment R p) : Prop :=
  (∀ kind, (R.computeTableRAP kind).Satisfies A.computeTableTrace) ∧
  (∀ kind, (R.memoryTableRAP kind).Satisfies A.memoryTableTrace) ∧
  (∀ kind, (R.computeWalkRAP kind).Satisfies A.computeWalkTrace) ∧
  (∀ kind, (R.memoryWalkRAP kind).Satisfies A.memoryWalkTrace) ∧
  (∀ kind, (R.computeIORAP kind).Satisfies A.computeIOTrace) ∧
  (∀ kind, (R.memoryIORAP kind).Satisfies A.memoryIOTrace)

theorem satisfies_iff_six_families (A : PlusIOSameExecutionAssignment R p) :
    A.Satisfies ↔
      (∀ kind, (R.computeTableRAP kind).Satisfies A.computeTableTrace) ∧
      (∀ kind, (R.memoryTableRAP kind).Satisfies A.memoryTableTrace) ∧
      (∀ kind, (R.computeWalkRAP kind).Satisfies A.computeWalkTrace) ∧
      (∀ kind, (R.memoryWalkRAP kind).Satisfies A.memoryWalkTrace) ∧
      (∀ kind, (R.computeIORAP kind).Satisfies A.computeIOTrace) ∧
      (∀ kind, (R.memoryIORAP kind).Satisfies A.memoryIOTrace) :=
  Iff.rfl

end PlusIOSameExecutionAssignment

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.EmbeddedRAPFamily.satisfies_iff_conjunction
#print axioms Nock.NockVMROM.Thm54.compute_disjoint_width
#print axioms Nock.NockVMROM.Thm54.memory_disjoint_width
#print axioms Nock.NockVMROM.Thm54.compute_table_walk_columns_disjoint
#print axioms Nock.NockVMROM.Thm54.memory_table_walk_columns_disjoint
#print axioms Nock.NockVMROM.Thm54.PlusIOSegmentedFamily.atJointCoins_preserves_table_challenges
#print axioms Nock.NockVMROM.Thm54.PlusIOSegmentedFamily.walk_challenge_discrimination
#print axioms Nock.NockVMROM.Thm54.PlusIOSegmentedFamily.table_walk_common_base_parameters
#print axioms Nock.NockVMROM.Thm54.PlusIOSegmentedFamily.io_common_mapped_parameters
#print axioms Nock.NockVMROM.Thm54.PlusIOSegmentedFamily.progIONodes_injective
#print axioms Nock.NockVMROM.Thm54.PlusIOSegmentedFamily.one_to_one_star_scope
#print axioms Nock.NockVMROM.Thm54.encodeEnvTrace_eval_at_node
#print axioms Nock.NockVMROM.Thm54.ExactDerivedIOAssignment.toIOSat
#print axioms Nock.NockVMROM.Thm54.ExactDerivedIOAssignment.exists_with_public_endpoints_of_LIO
#print axioms Nock.NockVMROM.Thm54.ExactDerivedIOAssignment.exists_with_public_endpoints_of_semanticIOWitness
#print axioms Nock.NockVMROM.Thm54.PlusIOSameExecutionAssignment.satisfies_iff_six_families

#check Nock.NockVMROM.Thm54.EmbeddedRAPFamily
#check Nock.NockVMROM.Thm54.PlusIOSegmentedFamily
#check Nock.NockVMROM.Thm54.PlusIOSegmentedFamily.computeTableWalkFamily
#check Nock.NockVMROM.Thm54.PlusIOSegmentedFamily.computeIOFamily
#check Nock.NockVMROM.Thm54.ExactDerivedIOAssignment
#check Nock.NockVMROM.Thm54.PlusIOSameExecutionAssignment
#check Nock.NockVMROM.Thm54.PlusIOSameExecutionAssignment.Satisfies
