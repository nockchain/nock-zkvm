import Nock.NockVMROM.Thm54.JointVerification
import Nock.NockVMROM.Thm54.SeedFibers
import Nock.NockVMROM.Thm54.AxisSoundness
import Nock.NockVMROM.Thm54.SemanticTrace
import Nock.NockVMROM.Thm54.PointwiseBridge

/-!
The experiment samples exactly `JointCoins K = K⁴`, in the order represented by the strategy:

1. seed-independent public nouns are committed in `P8PublicClaim`;
2. after a nonzero NPR seed `z`, the exact table problem, table auxiliaries, IO trace data, and
   public endpoints are committed in `P8SeedCommitment`;
3. only after `((αc, γ), (αm, z))` is known are the two walk responses supplied.

An `ExactCanonicalRAPProblem` contains a proof that its NPR seed is nonzero.  Consequently a typed
exact problem cannot be supplied at `z = 0`; acceptance is definitionally false there and the
whole zero fiber is nevertheless included in the failure union and counted honestly.

The target used here is non-circular: noun realization and exact axis semantics for the sampled
problem, together with an actual `evalN` result for the seed-independent public claim.  Current
production theorems do not derive its false-acceptance containment.  That exact remaining statement
is exported as `ResidualGenuineTargetContainment`; no target conclusion is stored in the strategy.

This is a proof-carrying conditional experiment, not yet the raw arbitrary-prover verifier model:
`ExactCanonicalRAPProblem` carries table WF hypotheses and `ExactDerivedIOAssignment` carries IO
satisfaction, endpoint agreement, and memory closure.  The finite counting theorems below are valid
for this typed experiment, while raw-response soundness requires a separate interface that derives
those facts from verifier checks.
-/

open scoped BigOperators Classical

namespace Nock.NockVMROM.Thm54

open Nock Nock.Walk

noncomputable section

set_option linter.unusedSectionVars false

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]

/-! ## Challenge-ordered conditional strategy -/

/-- Seed-independent public semantic claim.  These nouns are fixed before `z`. -/
structure P8PublicClaim where
  subject : Noun
  formula : Noun
  result : Noun

/-- Genuine evaluator conclusion for the public nouns. -/
def P8PublicClaim.Holds (claim : P8PublicClaim) : Prop :=
  ∃ fuel : ℕ, Nock.evalN fuel claim.subject claim.formula = some claim.result

/-- The paper's finite-field semantics for the fixed public nouns.  In particular OP4 is total
modular increment at the supplied characteristic. -/
def P8PublicClaim.HoldsMod (q : ℕ) (claim : P8PublicClaim) : Prop :=
  ∃ fuel : ℕ, FieldEmbedding.evalFBy q fuel claim.subject claim.formula = some claim.result

/-- The canonical public compute row at the root of one exact problem. -/
def exactRootComputePub (problem : ExactCanonicalRAPProblem F K) : ComputeTable.Pub K :=
  problem.exec.computePubAt ⟨0, problem.cfg.compRows_pos⟩

/-- Data committed after `z` but before the walk coins.

The three binding equations are commitment equations, not an evaluator or target conclusion.
The table and IO witness data are fixed here; only the two walk assignments remain open. -/
structure P8SeedCommitment (claim : P8PublicClaim) (z : K) where
  family : PlusIOSegmentedFamily F K
  sampled_seed : family.problem.cfg.challenges.z = z
  subject_binding :
    (exactRootComputePub family.problem).s =
      GlobalCarryRecognizer.enc z claim.subject
  formula_binding :
    (exactRootComputePub family.problem).f =
      GlobalCarryRecognizer.enc z claim.formula
  result_binding :
    (exactRootComputePub family.problem).e =
      GlobalCarryRecognizer.enc z claim.result
  computeTableAux : ExactCanonicalProgAux family.problem
  memoryTableAux : ExactCanonicalMemAux family.problem
  exactIO : ExactDerivedIOAssignment family p

/-- Responses opened only after all walk coins are known. -/
structure P8WalkResponse {claim : P8PublicClaim} {z : K}
    (C : P8SeedCommitment (F := F) (K := K) claim z)
    (ω : JointCoins K) where
  computeWalk : WalkAssignment K
  memoryWalk : WalkAssignment K

/-- The challenge order is represented in the type:

* `claim` has no field challenge argument;
* `afterSeed` sees `z`, and is required only on the nonzero branch admitted by the exact problem;
* `afterWalk` sees the complete `ω`, and its response is indexed by the commitment at `nprSeed ω`.
-/
structure P8Strategy where
  claim : P8PublicClaim
  afterSeed :
    ∀ z : K, z ≠ 0 → P8SeedCommitment (F := F) (K := K) claim z
  afterWalk :
    ∀ (ω : JointCoins K) (hz : nprSeed ω ≠ 0),
      P8WalkResponse (afterSeed (nprSeed ω) hz) ω

namespace P8Strategy

/-- Exact sampled family.  The exact problem is selected by `z`; the three walk challenges are
then overwritten by `(αc, γ, αm)` without changing that problem. -/
def familyAt (T : P8Strategy (F := F) (K := K))
    (ω : JointCoins K) (hz : nprSeed ω ≠ 0) : PlusIOSegmentedFamily F K :=
  (T.afterSeed (nprSeed ω) hz).family.atJointCoins ω

/-- Assemble the seed-time table/IO commitments and the post-walk responses. -/
def assignmentAt (T : P8Strategy (F := F) (K := K))
    (ω : JointCoins K) (hz : nprSeed ω ≠ 0) :
    PlusIOSameExecutionAssignment (T.familyAt ω hz) p where
  computeTableAux := (T.afterSeed (nprSeed ω) hz).computeTableAux
  memoryTableAux := (T.afterSeed (nprSeed ω) hz).memoryTableAux
  computeWalk := (T.afterWalk ω hz).computeWalk
  memoryWalk := (T.afterWalk ω hz).memoryWalk
  exactIO :=
    { multiplicity := (T.afterSeed (nprSeed ω) hz).exactIO.multiplicity
      progAcc := (T.afterSeed (nprSeed ω) hz).exactIO.progAcc
      memAcc := (T.afterSeed (nprSeed ω) hz).exactIO.memAcc
      multiplicity_ne_zero :=
        (T.afterSeed (nprSeed ω) hz).exactIO.multiplicity_ne_zero
      progSat := (T.afterSeed (nprSeed ω) hz).exactIO.progSat
      memSat := (T.afterSeed (nprSeed ω) hz).exactIO.memSat
      endpoints_agree := (T.afterSeed (nprSeed ω) hz).exactIO.endpoints_agree
      memory_closes := (T.afterSeed (nprSeed ω) hz).exactIO.memory_closes }

/-- Conditional acceptance at `ω`.  It evaluates all six segmented families of the exact
`z`-indexed problem at the sampled walk coordinates, plus shared IO, on one typed same-execution
assignment.  The assignment type already carries table-WF and semantic IO evidence; this definition
must not be presented as raw arbitrary-prover acceptance.  The zero-seed branch cannot accept. -/
def Accepts (T : P8Strategy (F := F) (K := K)) (ω : JointCoins K) : Prop :=
  if hz : nprSeed ω ≠ 0 then
    (T.assignmentAt ω hz).Satisfies ∧ SharedIOSat (T.familyAt ω hz) p
  else False

theorem not_accepts_zero (T : P8Strategy (F := F) (K := K))
    (ω : JointCoins K) (hz : nprSeed ω = 0) :
    ¬ T.Accepts ω := by
  simp [Accepts, hz]

/-- Exact six-family expansion of acceptance on a valid seed. -/
theorem accepts_iff_six_families
    (T : P8Strategy (F := F) (K := K))
    (ω : JointCoins K) (hz : nprSeed ω ≠ 0) :
    T.Accepts ω ↔
      (∀ kind, ((T.familyAt ω hz).computeTableRAP kind).Satisfies
        (T.assignmentAt ω hz).computeTableTrace) ∧
      (∀ kind, ((T.familyAt ω hz).memoryTableRAP kind).Satisfies
        (T.assignmentAt ω hz).memoryTableTrace) ∧
      (∀ kind, ((T.familyAt ω hz).computeWalkRAP kind).Satisfies
        (T.assignmentAt ω hz).computeWalkTrace) ∧
      (∀ kind, ((T.familyAt ω hz).memoryWalkRAP kind).Satisfies
        (T.assignmentAt ω hz).memoryWalkTrace) ∧
      (∀ kind, ((T.familyAt ω hz).computeIORAP kind).Satisfies
        (T.assignmentAt ω hz).computeIOTrace) ∧
      (∀ kind, ((T.familyAt ω hz).memoryIORAP kind).Satisfies
        (T.assignmentAt ω hz).memoryIOTrace) ∧
      SharedIOSat (T.familyAt ω hz) p := by
  simp only [Accepts, dif_pos hz,
    PlusIOSameExecutionAssignment.Satisfies, and_assoc]

/-- The sampled exact problem uses `z`, while the walk family uses exactly `αc`, shared `γ`,
and `αm`. -/
theorem sampled_challenges
    (T : P8Strategy (F := F) (K := K))
    (ω : JointCoins K) (hz : nprSeed ω ≠ 0) :
    (T.familyAt ω hz).problem.cfg.challenges.z = nprSeed ω ∧
      (T.familyAt ω hz).computeWalkAlpha = alphaC ω ∧
      (T.familyAt ω hz).walkGamma = gamma ω ∧
      (T.familyAt ω hz).memoryWalkAlpha = alphaM ω := by
  exact ⟨(T.afterSeed (nprSeed ω) hz).sampled_seed, rfl, rfl, rfl⟩

/-- Strongest currently assembled non-circular semantic target, on the exact sampled problem.
`SemanticTrace.ExactExecutionSemanticData` stores noun realizations, row-local opcode inputs, and
the explicit comparison census, but no opcode theorem conclusion or evaluator conclusion. -/
def FieldTargetAt (T : P8Strategy (F := F) (K := K)) (q : ℕ)
    (ω : JointCoins K) : Prop :=
  if hz : nprSeed ω ≠ 0 then
    let problem := (T.familyAt ω hz).problem
    (∃ Λ : ℕ,
      Nonempty
        (SemanticTrace.ExactExecutionSemanticData q Λ problem.cfg problem.exec)) ∧
        ExactMemoryAxisSemantics problem.cfg problem.exec
  else False

/-- Concrete genuine target: the field target plus an actual Nock evaluation of the public nouns.
No field of `P8Strategy` assumes this proposition. -/
def GenuineTargetAt (T : P8Strategy (F := F) (K := K)) (q : ℕ)
    (ω : JointCoins K) : Prop :=
  T.FieldTargetAt q ω ∧ T.claim.Holds

/-- Concrete false-acceptance event against the genuine target. -/
def FalseAcceptanceSet (T : P8Strategy (F := F) (K := K)) (q : ℕ) :
    Finset (JointCoins K) :=
  Finset.univ.filter (fun ω => T.Accepts ω ∧ ¬ T.GenuineTargetAt q ω)

@[simp]
theorem mem_FalseAcceptanceSet_iff
    (T : P8Strategy (F := F) (K := K)) (q : ℕ) (ω : JointCoins K) :
    ω ∈ T.FalseAcceptanceSet q ↔ T.Accepts ω ∧ ¬ T.GenuineTargetAt q ω := by
  simp [FalseAcceptanceSet]

end P8Strategy

/-! ## Explicit finite NPR comparison census -/

/-- A census indexed by occurrences, so duplicate noun comparisons retain their multiplicity. -/
structure ComparisonCensus (Λ : ℕ) where
  count : ℕ
  pair : Fin count → Noun × Noun
  leaves_bounded :
    ∀ i, (pair i).1.leaves ≤ Λ ∧ (pair i).2.leaves ≤ Λ

namespace ComparisonCensus

/-- Occurrence-preserving conversion of the active semantic trace census. -/
def ofSemanticData
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec) :
    ComparisonCensus Λ where
  count := (SemanticTrace.comparisonCensus w).length
  pair i :=
    SemanticTrace.ComparisonUse.pair
      ((SemanticTrace.comparisonCensus w).get i)
  leaves_bounded i :=
    SemanticTrace.census_leaves_bounded w
      (List.get_mem (SemanticTrace.comparisonCensus w) i)

/-- The conversion retains the number of comparison occurrences exactly; it does not deduplicate
equal noun pairs. -/
@[simp]
theorem ofSemanticData_count
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec) :
    (ofSemanticData w).count = (SemanticTrace.comparisonCensus w).length :=
  rfl

/-- Every occurrence retains its exact noun pair. -/
@[simp]
theorem ofSemanticData_pair
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec)
    (i : Fin (SemanticTrace.comparisonCensus w).length) :
    (ofSemanticData w).pair i =
      SemanticTrace.ComparisonUse.pair
        ((SemanticTrace.comparisonCensus w).get i) :=
  rfl

/-- The leaf bounds attached to each semantic occurrence are retained by the finite census. -/
theorem ofSemanticData_pair_leaves_bounded
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec)
    (i : Fin (ofSemanticData w).count) :
    ((ofSemanticData w).pair i).1.leaves ≤ Λ ∧
      ((ofSemanticData w).pair i).2.leaves ≤ Λ :=
  (ofSemanticData w).leaves_bounded i

/-- The concrete semantic census has at most ten occurrences per canonical compute row. -/
theorem ofSemanticData_count_le
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec) :
    (ofSemanticData w).count ≤ 10 * cfg.compRows :=
  SemanticTrace.comparisonCensus_count_le w

def badSeeds (C : ComparisonCensus Λ) : Finset K :=
  (Finset.univ : Finset (Fin C.count)).biUnion fun i =>
    Finset.univ.filter fun z : K =>
      ¬ GlobalCarryRecognizer.SepSeed z (C.pair i).1 (C.pair i).2

@[simp]
theorem mem_badSeeds_iff (C : ComparisonCensus Λ) (z : K) :
    z ∈ C.badSeeds (K := K) ↔
      ∃ i : Fin C.count,
        ¬ GlobalCarryRecognizer.SepSeed z (C.pair i).1 (C.pair i).2 := by
  simp only [badSeeds, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_filter]

/-- Each collision occurrence contributes its own `2Λ - 1` root count. -/
theorem badSeeds_card_le (C : ComparisonCensus Λ) :
    (C.badSeeds (K := K)).card ≤ C.count * (2 * Λ - 1) := by
  calc
    (C.badSeeds (K := K)).card ≤
        ∑ i : Fin C.count,
          (Finset.univ.filter fun z : K =>
            ¬ GlobalCarryRecognizer.SepSeed z (C.pair i).1 (C.pair i).2).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin C.count, (2 * Λ - 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact GlobalCarryRecognizer.sepSeed_bad_card_le Λ
        (C.pair i).1 (C.pair i).2
        (C.leaves_bounded i).1 (C.leaves_bounded i).2
    _ = C.count * (2 * Λ - 1) := by simp

end ComparisonCensus

/-! ## Seed-fiber lifts into `JointCoins` -/

def computeSeedFiberEquiv (K : Type*) :
    (K × (K × K)) × K ≃ JointCoins K where
  toFun x := ((x.1.2.1, x.1.2.2), (x.2, x.1.1))
  invFun ω := ((nprSeed ω, computeCoins ω), alphaM ω)
  left_inv := by rintro ⟨⟨z, α, γ⟩, αm⟩; rfl
  right_inv := by rintro ⟨⟨α, γ⟩, ⟨αm, z⟩⟩; rfl

def memorySeedFiberEquiv (K : Type*) :
    (K × (K × K)) × K ≃ JointCoins K where
  toFun x := ((x.2, x.1.2.2), (x.1.2.1, x.1.1))
  invFun ω := ((nprSeed ω, memoryCoins ω), alphaC ω)
  left_inv := by rintro ⟨⟨z, α, γ⟩, αc⟩; rfl
  right_inv := by rintro ⟨⟨αc, γ⟩, ⟨αm, z⟩⟩; rfl

def axisSeedFiberEquiv (K : Type*) :
    (K × K) × (K × K) ≃ JointCoins K where
  toFun x := ((x.2.1, x.2.2), (x.1.2, x.1.1))
  invFun ω := ((nprSeed ω, alphaM ω), (alphaC ω, gamma ω))
  left_inv := by rintro ⟨⟨z, αm⟩, ⟨αc, γ⟩⟩; rfl
  right_inv := by rintro ⟨⟨αc, γ⟩, ⟨αm, z⟩⟩; rfl

def liftComputeSeedFibers (E : Finset (K × (K × K))) :
    Finset (JointCoins K) :=
  (E ×ˢ (Finset.univ : Finset K)).map (computeSeedFiberEquiv K).toEmbedding

def liftMemorySeedFibers (E : Finset (K × (K × K))) :
    Finset (JointCoins K) :=
  (E ×ˢ (Finset.univ : Finset K)).map (memorySeedFiberEquiv K).toEmbedding

def liftAxisSeedFibers (E : Finset (K × K)) :
    Finset (JointCoins K) :=
  (E ×ˢ (Finset.univ : Finset (K × K))).map (axisSeedFiberEquiv K).toEmbedding

@[simp]
theorem mem_fiberEvent_iff {A Ω : Type*} [Fintype Ω]
    [DecidableEq A] [DecidableEq Ω]
    (seeds : Finset A) (bad : A → Finset Ω) (a : A) (ω : Ω) :
    (a, ω) ∈ fiberEvent seeds bad ↔ a ∈ seeds ∧ ω ∈ bad a := by
  simp [fiberEvent]

@[simp]
theorem mem_liftComputeSeedFibers_iff
    (E : Finset (K × (K × K))) (ω : JointCoins K) :
    ω ∈ liftComputeSeedFibers E ↔
      (nprSeed ω, computeCoins ω) ∈ E := by
  rw [liftComputeSeedFibers, Finset.mem_map_equiv]
  simp [computeSeedFiberEquiv]

@[simp]
theorem mem_liftMemorySeedFibers_iff
    (E : Finset (K × (K × K))) (ω : JointCoins K) :
    ω ∈ liftMemorySeedFibers E ↔
      (nprSeed ω, memoryCoins ω) ∈ E := by
  rw [liftMemorySeedFibers, Finset.mem_map_equiv]
  simp [memorySeedFiberEquiv]

@[simp]
theorem mem_liftAxisSeedFibers_iff
    (E : Finset (K × K)) (ω : JointCoins K) :
    ω ∈ liftAxisSeedFibers E ↔
      (nprSeed ω, alphaM ω) ∈ E := by
  rw [liftAxisSeedFibers, Finset.mem_map_equiv]
  simp [axisSeedFiberEquiv]

theorem card_liftComputeSeedFibers (E : Finset (K × (K × K))) :
    (liftComputeSeedFibers E).card = E.card * Fintype.card K := by
  simp [liftComputeSeedFibers]

theorem card_liftMemorySeedFibers (E : Finset (K × (K × K))) :
    (liftMemorySeedFibers E).card = E.card * Fintype.card K := by
  simp [liftMemorySeedFibers]

theorem card_liftAxisSeedFibers (E : Finset (K × K)) :
    (liftAxisSeedFibers E).card = E.card * Fintype.card K ^ 2 := by
  simp only [liftAxisSeedFibers, Finset.card_map, Finset.card_product,
    Finset.card_univ, Fintype.card_prod]
  ring

/-! ## Regenerated-label walk events -/

def computeWalkFailureEvent
    (hchar : NodeEncoding.StateTagChar K)
    (labels : ZLabelFamily K ComputeTable.State (ComputeTable.DTcomp K))
    (fo : ℕ → ℕ) (h : ℕ) : Finset (JointCoins K) :=
  liftComputeSeedFibers
    (walkBadJoint (ComputeTable.comp_stateSep (K := K))
      (NodeEncoding.computeNodeEncode hchar) labels fo h)

def memoryWalkFailureEvent
    (hchar : NodeEncoding.StateTagChar K)
    (labels : ZLabelFamily K MemoryTable.MState (MemoryTable.DTmem K))
    (fo : ℕ → ℕ) (kroots h : ℕ) : Finset (JointCoins K) :=
  liftMemorySeedFibers
    (walkBadForestJoint (MemoryTable.mem_stateSep (K := K))
      (NodeEncoding.memoryNodeEncode hchar) labels fo kroots h)

@[simp]
theorem mem_computeWalkFailureEvent_iff
    (hchar : NodeEncoding.StateTagChar K)
    (labels : ZLabelFamily K ComputeTable.State (ComputeTable.DTcomp K))
    (fo : ℕ → ℕ) (h : ℕ) (ω : JointCoins K) :
    ω ∈ computeWalkFailureEvent hchar labels fo h ↔
      nprSeed ω ≠ 0 ∧
        computeCoins ω ∈
          walkBadFiber (ComputeTable.comp_stateSep (K := K))
            (NodeEncoding.computeNodeEncode hchar) labels fo h (nprSeed ω) := by
  simp [computeWalkFailureEvent, walkBadJoint]

@[simp]
theorem mem_memoryWalkFailureEvent_iff
    (hchar : NodeEncoding.StateTagChar K)
    (labels : ZLabelFamily K MemoryTable.MState (MemoryTable.DTmem K))
    (fo : ℕ → ℕ) (kroots h : ℕ) (ω : JointCoins K) :
    ω ∈ memoryWalkFailureEvent hchar labels fo kroots h ↔
      nprSeed ω ≠ 0 ∧
        memoryCoins ω ∈
          walkBadForestFiber (MemoryTable.mem_stateSep (K := K))
            (NodeEncoding.memoryNodeEncode hchar) labels fo kroots h (nprSeed ω) := by
  simp [memoryWalkFailureEvent, walkBadForestJoint]

def walkWorkload (h nodeWidth : ℕ) : ℕ :=
  h + h * (nodeWidth - 1)

private theorem seed_walk_extension_bound
    (eventCard h nodeWidth : ℕ)
    (hcard :
      eventCard ≤ (Fintype.card K - 1) *
        (Fintype.card K * h +
          Fintype.card K * (h * (nodeWidth - 1)))) :
    eventCard * Fintype.card K ≤
      walkWorkload h nodeWidth * Fintype.card K ^ 3 := by
  let k := Fintype.card K
  have hk : k - 1 ≤ k := Nat.sub_le _ _
  calc
    eventCard * k ≤
        ((k - 1) * (k * h + k * (h * (nodeWidth - 1)))) * k :=
      Nat.mul_le_mul_right k hcard
    _ = ((k - 1) * (k * walkWorkload h nodeWidth)) * k := by
      simp only [walkWorkload]
      ring
    _ ≤ (k * (k * walkWorkload h nodeWidth)) * k := by
      exact Nat.mul_le_mul_right k
        (Nat.mul_le_mul_right (k * walkWorkload h nodeWidth) hk)
    _ = walkWorkload h nodeWidth * k ^ 3 := by ring

theorem computeWalkFailureEvent_card_le
    (hchar : NodeEncoding.StateTagChar K)
    (labels : ZLabelFamily K ComputeTable.State (ComputeTable.DTcomp K))
    (fo : ℕ → ℕ) {h : ℕ}
    (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h)
    (harity : ∀ i, fo i ≤ 3)
    (hfo : ∀ z i, 1 ≤ i → i ≤ h →
      fo i = (ComputeTable.comp_stateSep (K := K)).fanout (labels.row z i).1)
    (hF : ∀ z i, 1 ≤ i → i ≤ h →
      ComputeTable.Fcomp (labels.row z i)
        (fun j : Fin 3 =>
          if (j : ℕ) < fo i then some (labels.child z i (j + 1)) else none)) :
    (computeWalkFailureEvent hchar labels fo h).card ≤
      walkWorkload h NodeEncoding.computeNodeWidth * Fintype.card K ^ 3 := by
  rw [computeWalkFailureEvent, card_liftComputeSeedFibers]
  apply seed_walk_extension_bound
  exact walkBadJoint_card_le_of_label
    (ComputeTable.comp_stateSep (K := K))
    ComputeTable.computeLabelOf
    (fun lbl _ _ h hF => ComputeTable.Fcomp_respects_labelOf lbl h hF)
    (NodeEncoding.computeNodeEncode hchar)
    (fun _ _ h => NodeEncoding.computeNodeEncode_labelOf_eq hchar h)
    labels fo hSf hvalid harity hfo hF

theorem memoryWalkFailureEvent_card_le
    (hchar : NodeEncoding.StateTagChar K)
    (labels : ZLabelFamily K MemoryTable.MState (MemoryTable.DTmem K))
    (fo : ℕ → ℕ) {kroots h : ℕ}
    (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h)
    (hvalid : BFSValidF kroots fo h) (harity : ∀ i, fo i ≤ 2)
    (hfo : ∀ z i, 1 ≤ i → i ≤ h →
      fo i = (MemoryTable.mem_stateSep (K := K)).fanout (labels.row z i).1)
    (hF : ∀ z i, 1 ≤ i → i ≤ h →
      MemoryTable.Fmem (labels.row z i)
        (fun j : Fin 2 =>
          if (j : ℕ) < fo i then some (labels.child z i (j + 1)) else none)) :
    (memoryWalkFailureEvent hchar labels fo kroots h).card ≤
      walkWorkload h NodeEncoding.memoryNodeWidth * Fintype.card K ^ 3 := by
  rw [memoryWalkFailureEvent, card_liftMemorySeedFibers]
  apply seed_walk_extension_bound
  exact walkBadForestJoint_card_le_of_label
    (MemoryTable.mem_stateSep (K := K))
    MemoryTable.memoryLabelOf
    (fun lbl _ _ h hF => MemoryTable.Fmem_respects_labelOf lbl h hF)
    (NodeEncoding.memoryNodeEncode hchar)
    (fun _ _ h => NodeEncoding.memoryNodeEncode_labelOf_eq hchar h)
    labels fo hk hSf hvalid harity hfo hF

/-! ## Seed-indexed axis event

The event below is evaluated at sampled `alphaM`.  This is countable, but its containment role is
not yet connected to acceptance: `PlusIOSegmentedFamily.atJointCoins` changes only
`memoryWalkAlpha`, while the exact axis tree and table constraints continue to use the fixed
`problem.cfg.challenges.α`.  In particular, no diagonal equation
`alphaM ω = problem.cfg.challenges.α` is assumed here.  The missing acceptance-to-sampled-axis
transport is named explicitly below and remains part of `ResidualGenuineTargetContainment`.
-/

/-- Joint-coin instantiation does not change the table timestamp challenge used by the axis
target, even though it changes the memory-walk challenge to `alphaM ω`. -/
theorem P8Strategy.familyAt_preserves_axis_challenge
    (T : P8Strategy (F := F) (K := K))
    (ω : JointCoins K) (hz : nprSeed ω ≠ 0) :
    (T.familyAt ω hz).problem.cfg.challenges.α =
      (T.afterSeed (nprSeed ω) hz).family.problem.cfg.challenges.α :=
  rfl

/-- Precisely the unresolved axis transport, stated without a diagonal challenge premise.

Current production acceptance fixes the root axis boundary at `cfg.challenges.α`; containment in
`seededAxisFailureEvent` needs it at sampled `alphaM`. -/
def SampledAxisBoundaryResidual
    (T : P8Strategy (F := F) (K := K)) : Prop :=
  ∀ (ω : JointCoins K) (hz : nprSeed ω ≠ 0),
    T.Accepts ω →
    let problem := (T.familyAt ω hz).problem
    ∀ i : Fin problem.cfg.kMem,
      (Nock.AxisBatching.MTree.countsP
        (exactAxisTree problem.cfg problem.exec i)).eval (alphaM ω) = 0

def seededAxisPairs (T : P8Strategy (F := F) (K := K)) :
    Finset (K × K) :=
  fiberEvent (validSeeds K) fun z =>
    if hz : z ≠ 0 then
      let problem := (T.afterSeed z hz).family.problem
      axisBadAlphas problem.cfg problem.exec
    else ∅

def seededAxisFailureEvent (T : P8Strategy (F := F) (K := K)) :
    Finset (JointCoins K) :=
  liftAxisSeedFibers (seededAxisPairs T)

@[simp]
theorem mem_seededAxisFailureEvent_iff
    (T : P8Strategy (F := F) (K := K)) (ω : JointCoins K) :
    ω ∈ seededAxisFailureEvent T ↔
      ∃ hz : nprSeed ω ≠ 0,
        let problem := (T.afterSeed (nprSeed ω) hz).family.problem
        alphaM ω ∈ axisBadAlphas problem.cfg problem.exec := by
  rw [seededAxisFailureEvent, mem_liftAxisSeedFibers_iff,
    seededAxisPairs, mem_fiberEvent_iff, mem_validSeeds]
  constructor
  · rintro ⟨hz, hmem⟩
    refine ⟨hz, ?_⟩
    simpa only [dif_pos hz] using hmem
  · rintro ⟨hz, hmem⟩
    refine ⟨hz, ?_⟩
    simpa only [dif_pos hz] using hmem

theorem seededAxisFailureEvent_card_le
    (h2 : (2 : K) ≠ 0)
    (T : P8Strategy (F := F) (K := K)) (axisWorkload : ℕ)
    (refinement :
      ∀ (z : K) (hz : z ≠ 0),
        let problem := (T.afterSeed z hz).family.problem
        ExactAxisRefinement problem.cfg problem.exec)
    (hwork :
      ∀ (z : K) (hz : z ≠ 0),
        let problem := (T.afterSeed z hz).family.problem
        exactAxisWorkload problem.cfg problem.exec ≤ axisWorkload) :
    (seededAxisFailureEvent T).card ≤
      axisWorkload * Fintype.card K ^ 3 := by
  rw [seededAxisFailureEvent, card_liftAxisSeedFibers]
  have hpairs :
      (seededAxisPairs T).card ≤
        (Fintype.card K - 1) * axisWorkload := by
    unfold seededAxisPairs
    simpa only [validSeeds_card] using
      (fiberEvent_card_le (validSeeds K)
        (fun z =>
          if hz : z ≠ 0 then
            let problem := (T.afterSeed z hz).family.problem
            axisBadAlphas problem.cfg problem.exec
          else ∅)
        axisWorkload (by
          intro z hz
          have hz0 : z ≠ 0 := (mem_validSeeds z).1 hz
          simp only [dif_pos hz0]
          exact (axisBadAlphas_card_le h2 (refinement z hz0)).trans
            (hwork z hz0)))
  calc
    (seededAxisPairs T).card * Fintype.card K ^ 2
        ≤ ((Fintype.card K - 1) * axisWorkload) *
            Fintype.card K ^ 2 :=
      Nat.mul_le_mul_right _ hpairs
    _ ≤ (Fintype.card K * axisWorkload) * Fintype.card K ^ 2 := by
      exact Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right axisWorkload (Nat.sub_le _ _))
    _ = axisWorkload * Fintype.card K ^ 3 := by ring

/-! ## Aggregate event and workload -/

def zeroSeedFailureEvent : Finset (JointCoins K) :=
  liftSeed ({0} : Finset K)

@[simp]
theorem mem_zeroSeedFailureEvent_iff (ω : JointCoins K) :
    ω ∈ (zeroSeedFailureEvent : Finset (JointCoins K)) ↔ nprSeed ω = 0 := by
  simp [zeroSeedFailureEvent]

theorem zeroSeedFailureEvent_card :
    (zeroSeedFailureEvent : Finset (JointCoins K)).card =
      Fintype.card K ^ 3 := by
  rw [zeroSeedFailureEvent, card_liftSeed]
  simp

def collisionFailureEvent (C : ComparisonCensus Λ) :
    Finset (JointCoins K) :=
  liftSeed (C.badSeeds (K := K))

@[simp]
theorem mem_collisionFailureEvent_iff
    (C : ComparisonCensus Λ) (ω : JointCoins K) :
    ω ∈ collisionFailureEvent C ↔
      ∃ i : Fin C.count,
        ¬ GlobalCarryRecognizer.SepSeed (nprSeed ω)
          (C.pair i).1 (C.pair i).2 := by
  simp [collisionFailureEvent]

theorem collisionFailureEvent_card_le
    (C : ComparisonCensus Λ) :
    (collisionFailureEvent (K := K) C).card ≤
      (C.count * (2 * Λ - 1)) * Fintype.card K ^ 3 := by
  rw [collisionFailureEvent, card_liftSeed]
  exact Nat.mul_le_mul_right _ C.badSeeds_card_le

/-- Every state-indexed production comparison premise is covered by the collision event built
from the canonical semantic census.  The witness index is the original list occurrence, so
duplicate noun pairs remain distinct census occurrences. -/
theorem collisionFailureEvent_ofSemanticData_covers_comparisonListed
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec)
    (row : Fin cfg.compRows) (role : SemanticTrace.ComparisonRole)
    (left right : Noun)
    (hlisted :
      SemanticTrace.ComparisonListed (w.rows row) role left right)
    (ω : JointCoins K)
    (hbad :
      ¬ GlobalCarryRecognizer.SepSeed (nprSeed ω) left right) :
    ω ∈ collisionFailureEvent (K := K) (ComparisonCensus.ofSemanticData w) := by
  rw [mem_collisionFailureEvent_iff]
  have hcensus :
      ({ role := role, left := left, right := right } :
        SemanticTrace.ComparisonUse) ∈ SemanticTrace.comparisonCensus w :=
    SemanticTrace.comparison_mem_census w row _ hlisted
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hcensus
  refine ⟨i, ?_⟩
  have hpair :
      (ComparisonCensus.ofSemanticData w).pair i = (left, right) := by
    change SemanticTrace.ComparisonUse.pair
      ((SemanticTrace.comparisonCensus w).get i) = (left, right)
    rw [hi]
    rfl
  rw [hpair]
  exact hbad

/-- OP9's axis-atom comparison is covered by the same canonical collision event; it is not an
extra uncounted faithfulness premise. -/
theorem collisionFailureEvent_ofSemanticData_covers_op9_axis
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec)
    (row : Fin cfg.compRows)
    (gate : Σ tail : OpcodeSemantics.TailRealization
        (exec.computeRowAt row).2.1.z (exec.computeRowAt row).2.2.2,
      SemanticTrace.AxisAtomComparisonCertificate
        (exec.computeRowAt row).2.1.z q (exec.computeRowAt row).2.2.2 tail)
    (hgate : gate ∈ (w.rows row).axisGates)
    (ω : JointCoins K)
    (hbad :
      ¬ GlobalCarryRecognizer.SepSeed (nprSeed ω)
        gate.1.head (.atom gate.2.axis)) :
    ω ∈ collisionFailureEvent (K := K) (ComparisonCensus.ofSemanticData w) := by
  apply collisionFailureEvent_ofSemanticData_covers_comparisonListed
    w row .axisAtom gate.1.head (.atom gate.2.axis)
  · exact (w.rows row).axisGate_listed gate hgate
  · exact hbad

/-- Full finite failure union: zero seed, fixed-seed compute walk, fixed-seed memory forest walk,
the occurrence-indexed NPR collision census, and the seed-indexed exact axis event. -/
def FailureUnion
    (T : P8Strategy (F := F) (K := K))
    (hchar : NodeEncoding.StateTagChar K)
    (computeLabels : ZLabelFamily K ComputeTable.State (ComputeTable.DTcomp K))
    (computeFo : ℕ → ℕ) (computeHeight : ℕ)
    (memoryLabels : ZLabelFamily K MemoryTable.MState (MemoryTable.DTmem K))
    (memoryFo : ℕ → ℕ) (memoryRoots memoryHeight : ℕ)
    (census : ComparisonCensus Λ) : Finset (JointCoins K) :=
  ((((zeroSeedFailureEvent ∪
      computeWalkFailureEvent hchar computeLabels computeFo computeHeight) ∪
      memoryWalkFailureEvent hchar memoryLabels memoryFo memoryRoots memoryHeight) ∪
      collisionFailureEvent census) ∪
      seededAxisFailureEvent T)

@[simp]
theorem mem_FailureUnion_iff
    (T : P8Strategy (F := F) (K := K))
    (hchar : NodeEncoding.StateTagChar K)
    (computeLabels : ZLabelFamily K ComputeTable.State (ComputeTable.DTcomp K))
    (computeFo : ℕ → ℕ) (computeHeight : ℕ)
    (memoryLabels : ZLabelFamily K MemoryTable.MState (MemoryTable.DTmem K))
    (memoryFo : ℕ → ℕ) (memoryRoots memoryHeight : ℕ)
    (census : ComparisonCensus Λ) (ω : JointCoins K) :
    ω ∈ FailureUnion T hchar computeLabels computeFo computeHeight
        memoryLabels memoryFo memoryRoots memoryHeight census ↔
      nprSeed ω = 0 ∨
      (nprSeed ω ≠ 0 ∧
        computeCoins ω ∈
          walkBadFiber (ComputeTable.comp_stateSep (K := K))
            (NodeEncoding.computeNodeEncode hchar)
            computeLabels computeFo computeHeight (nprSeed ω)) ∨
      (nprSeed ω ≠ 0 ∧
        memoryCoins ω ∈
          walkBadForestFiber (MemoryTable.mem_stateSep (K := K))
            (NodeEncoding.memoryNodeEncode hchar)
            memoryLabels memoryFo memoryRoots memoryHeight (nprSeed ω)) ∨
      (∃ i : Fin census.count,
        ¬ GlobalCarryRecognizer.SepSeed (nprSeed ω)
          (census.pair i).1 (census.pair i).2) ∨
      (∃ hz : nprSeed ω ≠ 0,
        let problem := (T.afterSeed (nprSeed ω) hz).family.problem
        alphaM ω ∈ axisBadAlphas problem.cfg problem.exec) := by
  simp [FailureUnion]

def jointWorkload
    (computeHeight memoryHeight collisionCount Λ axisWorkload : ℕ) : ℕ :=
  1 +
  walkWorkload computeHeight NodeEncoding.computeNodeWidth +
  walkWorkload memoryHeight NodeEncoding.memoryNodeWidth +
  collisionCount * (2 * Λ - 1) +
  axisWorkload

/-- Exact aggregate finite bound.  It uses only cardinal union bounds; no independence premise
appears. -/
theorem failureUnion_card_le
    (h2 : (2 : K) ≠ 0)
    (T : P8Strategy (F := F) (K := K))
    (hchar : NodeEncoding.StateTagChar K)
    (computeLabels : ZLabelFamily K ComputeTable.State (ComputeTable.DTcomp K))
    (computeFo : ℕ → ℕ) {computeHeight : ℕ}
    (computeSf : Sf computeFo computeHeight + 1 = computeHeight)
    (computeValid : BFSValid computeFo computeHeight)
    (computeArity : ∀ i, computeFo i ≤ 3)
    (computeFanout : ∀ z i, 1 ≤ i → i ≤ computeHeight →
      computeFo i =
        (ComputeTable.comp_stateSep (K := K)).fanout (computeLabels.row z i).1)
    (computeLocal : ∀ z i, 1 ≤ i → i ≤ computeHeight →
      ComputeTable.Fcomp (computeLabels.row z i)
        (fun j : Fin 3 =>
          if (j : ℕ) < computeFo i
          then some (computeLabels.child z i (j + 1)) else none))
    (memoryLabels : ZLabelFamily K MemoryTable.MState (MemoryTable.DTmem K))
    (memoryFo : ℕ → ℕ) {memoryRoots memoryHeight : ℕ}
    (memoryRootsPos : 1 ≤ memoryRoots)
    (memorySf : memoryRoots + Sf memoryFo memoryHeight = memoryHeight)
    (memoryValid : BFSValidF memoryRoots memoryFo memoryHeight)
    (memoryArity : ∀ i, memoryFo i ≤ 2)
    (memoryFanout : ∀ z i, 1 ≤ i → i ≤ memoryHeight →
      memoryFo i =
        (MemoryTable.mem_stateSep (K := K)).fanout (memoryLabels.row z i).1)
    (memoryLocal : ∀ z i, 1 ≤ i → i ≤ memoryHeight →
      MemoryTable.Fmem (memoryLabels.row z i)
        (fun j : Fin 2 =>
          if (j : ℕ) < memoryFo i
          then some (memoryLabels.child z i (j + 1)) else none))
    (census : ComparisonCensus Λ)
    (axisWorkload : ℕ)
    (axisRefinement :
      ∀ (z : K) (hz : z ≠ 0),
        let problem := (T.afterSeed z hz).family.problem
        ExactAxisRefinement problem.cfg problem.exec)
    (axisWorkloadBound :
      ∀ (z : K) (hz : z ≠ 0),
        let problem := (T.afterSeed z hz).family.problem
        exactAxisWorkload problem.cfg problem.exec ≤ axisWorkload) :
    (FailureUnion T hchar computeLabels computeFo computeHeight
      memoryLabels memoryFo memoryRoots memoryHeight census).card ≤
      jointWorkload computeHeight memoryHeight census.count Λ axisWorkload *
        Fintype.card K ^ 3 := by
  let Z : Finset (JointCoins K) := zeroSeedFailureEvent
  let C : Finset (JointCoins K) :=
    computeWalkFailureEvent hchar computeLabels computeFo computeHeight
  let M : Finset (JointCoins K) :=
    memoryWalkFailureEvent hchar memoryLabels memoryFo memoryRoots memoryHeight
  let N : Finset (JointCoins K) := collisionFailureEvent census
  let A : Finset (JointCoins K) := seededAxisFailureEvent T
  have hZ : Z.card ≤ 1 * Fintype.card K ^ 3 := by
    simp [Z, zeroSeedFailureEvent_card]
  have hC : C.card ≤
      walkWorkload computeHeight NodeEncoding.computeNodeWidth *
        Fintype.card K ^ 3 := by
    exact computeWalkFailureEvent_card_le hchar computeLabels computeFo
      computeSf computeValid computeArity computeFanout computeLocal
  have hM : M.card ≤
      walkWorkload memoryHeight NodeEncoding.memoryNodeWidth *
        Fintype.card K ^ 3 := by
    exact memoryWalkFailureEvent_card_le hchar memoryLabels memoryFo
      memoryRootsPos memorySf memoryValid memoryArity memoryFanout memoryLocal
  have hN : N.card ≤
      (census.count * (2 * Λ - 1)) * Fintype.card K ^ 3 :=
    collisionFailureEvent_card_le census
  have hA : A.card ≤ axisWorkload * Fintype.card K ^ 3 :=
    seededAxisFailureEvent_card_le h2 T axisWorkload
      axisRefinement axisWorkloadBound
  calc
    (FailureUnion T hchar computeLabels computeFo computeHeight
      memoryLabels memoryFo memoryRoots memoryHeight census).card
        ≤ Z.card + C.card + M.card + N.card + A.card := by
          dsimp only [FailureUnion, Z, C, M, N, A]
          calc
            ((((zeroSeedFailureEvent ∪
                computeWalkFailureEvent hchar computeLabels computeFo computeHeight) ∪
                memoryWalkFailureEvent hchar memoryLabels memoryFo memoryRoots memoryHeight) ∪
                collisionFailureEvent census) ∪
                seededAxisFailureEvent T).card
                ≤ (((zeroSeedFailureEvent ∪
                    computeWalkFailureEvent hchar computeLabels computeFo computeHeight) ∪
                    memoryWalkFailureEvent hchar memoryLabels memoryFo memoryRoots memoryHeight) ∪
                    collisionFailureEvent census).card +
                    (seededAxisFailureEvent T).card :=
              Finset.card_union_le _ _
            _ ≤ ((zeroSeedFailureEvent ∪
                  computeWalkFailureEvent hchar computeLabels computeFo computeHeight) ∪
                  memoryWalkFailureEvent hchar memoryLabels memoryFo memoryRoots memoryHeight).card +
                  (collisionFailureEvent census).card +
                  (seededAxisFailureEvent T).card := by
              exact Nat.add_le_add_right
                (Finset.card_union_le
                  ((zeroSeedFailureEvent ∪
                    computeWalkFailureEvent hchar computeLabels computeFo computeHeight) ∪
                    memoryWalkFailureEvent hchar memoryLabels memoryFo memoryRoots memoryHeight)
                  (collisionFailureEvent census))
                (seededAxisFailureEvent T).card
            _ ≤ (zeroSeedFailureEvent ∪
                  computeWalkFailureEvent hchar computeLabels computeFo computeHeight).card +
                  (memoryWalkFailureEvent hchar memoryLabels memoryFo memoryRoots memoryHeight).card +
                  (collisionFailureEvent census).card +
                  (seededAxisFailureEvent T).card := by
              exact Nat.add_le_add_right
                (Nat.add_le_add_right
                  (Finset.card_union_le
                    (zeroSeedFailureEvent ∪
                      computeWalkFailureEvent hchar computeLabels computeFo computeHeight)
                    (memoryWalkFailureEvent hchar memoryLabels memoryFo memoryRoots memoryHeight))
                  (collisionFailureEvent census).card)
                (seededAxisFailureEvent T).card
            _ ≤ (zeroSeedFailureEvent : Finset (JointCoins K)).card +
                  (computeWalkFailureEvent hchar computeLabels computeFo computeHeight).card +
                  (memoryWalkFailureEvent hchar memoryLabels memoryFo memoryRoots memoryHeight).card +
                  (collisionFailureEvent census).card +
                  (seededAxisFailureEvent T).card := by
              exact Nat.add_le_add_right
                (Nat.add_le_add_right
                  (Nat.add_le_add_right
                    (Finset.card_union_le
                      (zeroSeedFailureEvent : Finset (JointCoins K))
                      (computeWalkFailureEvent hchar computeLabels computeFo computeHeight))
                    (memoryWalkFailureEvent hchar memoryLabels memoryFo memoryRoots memoryHeight).card)
                  (collisionFailureEvent census).card)
                (seededAxisFailureEvent T).card
    _ ≤
        1 * Fintype.card K ^ 3 +
        walkWorkload computeHeight NodeEncoding.computeNodeWidth *
          Fintype.card K ^ 3 +
        walkWorkload memoryHeight NodeEncoding.memoryNodeWidth *
          Fintype.card K ^ 3 +
        (census.count * (2 * Λ - 1)) * Fintype.card K ^ 3 +
        axisWorkload * Fintype.card K ^ 3 :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hZ hC) hM) hN) hA
    _ = jointWorkload computeHeight memoryHeight census.count Λ axisWorkload *
        Fintype.card K ^ 3 := by
      simp only [jointWorkload]
      ring


/-- The exact remaining production seam.  It asks for containment of the concrete false-acceptance
set in the concrete five-class finite union.  In particular it does not assume the target
conclusion; it assumes only the implication that still has to be assembled from fixed-seed walk
soundness, noun/opcode realization, served-memory wiring, no-overflow, and DFS scheduling. -/
def ResidualGenuineTargetContainment
    (T : P8Strategy (F := F) (K := K)) (q : ℕ)
    (hchar : NodeEncoding.StateTagChar K)
    (computeLabels : ZLabelFamily K ComputeTable.State (ComputeTable.DTcomp K))
    (computeFo : ℕ → ℕ) (computeHeight : ℕ)
    (memoryLabels : ZLabelFamily K MemoryTable.MState (MemoryTable.DTmem K))
    (memoryFo : ℕ → ℕ) (memoryRoots memoryHeight : ℕ)
    (census : ComparisonCensus Λ) : Prop :=
  ∀ ω, T.Accepts ω → ¬ T.GenuineTargetAt q ω →
    ω ∈ FailureUnion T hchar computeLabels computeFo computeHeight
      memoryLabels memoryFo memoryRoots memoryHeight census

theorem falseAcceptance_subset_failureUnion
    (T : P8Strategy (F := F) (K := K)) (q : ℕ)
    (hchar : NodeEncoding.StateTagChar K)
    (computeLabels : ZLabelFamily K ComputeTable.State (ComputeTable.DTcomp K))
    (computeFo : ℕ → ℕ) (computeHeight : ℕ)
    (memoryLabels : ZLabelFamily K MemoryTable.MState (MemoryTable.DTmem K))
    (memoryFo : ℕ → ℕ) (memoryRoots memoryHeight : ℕ)
    (census : ComparisonCensus Λ)
    (hcontain : ResidualGenuineTargetContainment T q hchar
      computeLabels computeFo computeHeight
      memoryLabels memoryFo memoryRoots memoryHeight census) :
    T.FalseAcceptanceSet q ⊆
      FailureUnion T hchar computeLabels computeFo computeHeight
        memoryLabels memoryFo memoryRoots memoryHeight census := by
  intro ω hω
  exact hcontain ω
    ((T.mem_FalseAcceptanceSet_iff q ω).1 hω).1
    ((T.mem_FalseAcceptanceSet_iff q ω).1 hω).2

theorem falseAcceptance_card_le
    (T : P8Strategy (F := F) (K := K)) (q workload : ℕ)
    (failure : Finset (JointCoins K))
    (hcontain : T.FalseAcceptanceSet q ⊆ failure)
    (hfailure : failure.card ≤ workload * Fintype.card K ^ 3) :
    (T.FalseAcceptanceSet q).card ≤ workload * Fintype.card K ^ 3 :=
  (Finset.card_le_card hcontain).trans hfailure

theorem falseAcceptance_jointProbability_le
    (T : P8Strategy (F := F) (K := K)) (q workload : ℕ)
    (failure : Finset (JointCoins K))
    (hcontain : T.FalseAcceptanceSet q ⊆ failure)
    (hfailure : failure.card ≤ workload * Fintype.card K ^ 3) :
    |jointProbability (T.FalseAcceptanceSet q)| ≤
      (workload : ℝ) / (Fintype.card K : ℝ) :=
  jointProbability_le_workload_div_card _ _
    (falseAcceptance_card_le T q workload failure hcontain hfailure)

namespace ExactPrimeFamily

theorem P8PointwiseBridge_of_contained_joint_events
    (Ksz h : ℕ → ℕ) (kroots : ℕ)
    (bad failure :
      ∀ n, Finset (JointCoins (FieldAt Ksz h kroots n)))
    (workload : ℕ → ℕ)
    (hcontain : ∀ n, bad n ⊆ failure n)
    (hcard :
      ∀ n, (failure n).card ≤
        workload n * Fintype.card (FieldAt Ksz h kroots n) ^ 3) :
    P8PointwiseBridge Ksz h kroots
      (fun n => (workload n : ℝ))
      (fun n => jointProbability (bad n)) := by
  apply P8PointwiseBridge_of_joint_card_le
  intro n
  exact (Finset.card_le_card (hcontain n)).trans (hcard n)

end ExactPrimeFamily

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.P8Strategy.accepts_iff_six_families
#print axioms Nock.NockVMROM.Thm54.P8Strategy.sampled_challenges
#print axioms Nock.NockVMROM.Thm54.ComparisonCensus.ofSemanticData_count_le
#print axioms Nock.NockVMROM.Thm54.ComparisonCensus.badSeeds_card_le
#print axioms Nock.NockVMROM.Thm54.collisionFailureEvent_ofSemanticData_covers_comparisonListed
#print axioms Nock.NockVMROM.Thm54.collisionFailureEvent_ofSemanticData_covers_op9_axis
#print axioms Nock.NockVMROM.Thm54.computeWalkFailureEvent_card_le
#print axioms Nock.NockVMROM.Thm54.memoryWalkFailureEvent_card_le
#print axioms Nock.NockVMROM.Thm54.seededAxisFailureEvent_card_le
#print axioms Nock.NockVMROM.Thm54.failureUnion_card_le
#print axioms Nock.NockVMROM.Thm54.falseAcceptance_jointProbability_le
#print axioms Nock.NockVMROM.Thm54.ExactPrimeFamily.P8PointwiseBridge_of_contained_joint_events
