import Nock.NockVMROM.Thm54.SemanticStrategy

/-!
The first section retains a useful *sampled-witness* adapter for one `P8Strategy`, seed, and
semantic-data value.

`BoundP8Census` is the global construction: its pair list is computed only from a
`SemanticStrategy.BoundP8Strategy.skeleton`, before any seed is sampled.  It contains the three
public root bindings followed by the exact state-indexed internal comparison occurrences in
canonical skeleton BFS order, retaining duplicates and OP9's axis-atom occurrence.

Semantic-data existence and `SkeletonComparisonCompatibility` remain separate premises.  No target
predicate, `evalN` conclusion, or acceptance assumption is used here.
-/

open scoped Classical

namespace Nock.NockVMROM.Thm54

open Nock Nock.Walk

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {p : ℕ} [CharP K p]

namespace ComparisonCensus

/-- Generic occurrence-preserving adapter from a list of noun pairs. -/
def ofPairList (pairs : List (Noun × Noun))
    (bounded :
      ∀ pair ∈ pairs, pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ) :
    ComparisonCensus Λ where
  count := pairs.length
  pair i := pairs.get i
  leaves_bounded i := bounded _ (List.get_mem pairs i)

@[simp]
theorem ofPairList_count (pairs : List (Noun × Noun))
    (bounded :
      ∀ pair ∈ pairs, pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ) :
    (ofPairList pairs bounded).count = pairs.length :=
  rfl

@[simp]
theorem ofPairList_pair (pairs : List (Noun × Noun))
    (bounded :
      ∀ pair ∈ pairs, pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ)
    (i : Fin pairs.length) :
    (ofPairList pairs bounded).pair i = pairs.get i :=
  rfl

/-- List membership gives an occurrence index; equal pairs are not deduplicated. -/
theorem exists_pair_of_mem (pairs : List (Noun × Noun))
    (bounded :
      ∀ pair ∈ pairs, pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ)
    {pair : Noun × Noun} (hpair : pair ∈ pairs) :
    ∃ i : Fin (ofPairList pairs bounded).count,
      (ofPairList pairs bounded).pair i = pair := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hpair
  exact ⟨i, hi⟩

end ComparisonCensus

namespace P8Census

/-- The exact configuration selected by `T` after the sampled nonzero seed. -/
abbrev sampledCfg (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0) :
    ExactConfig F K :=
  (T.afterSeed z hz).family.problem.cfg

/-- The exact execution selected by `T` after the sampled nonzero seed. -/
abbrev sampledExec (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0) :
    ExactExecution (sampledCfg T z hz) :=
  (T.afterSeed z hz).family.problem.exec

/-- Semantic data can only be supplied for the exact strategy-selected configuration/execution. -/
abbrev StrategySemanticData
    (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0)
    (q Λ : ℕ) :=
  SemanticTrace.ExactExecutionSemanticData q Λ
    (sampledCfg T z hz) (sampledExec T z hz)

/-- The strategy-selected semantic root row. -/
abbrev rootData
    {T : P8Strategy (F := F) (K := K)} {z : K} {hz : z ≠ 0}
    {q Λ : ℕ} (w : StrategySemanticData T z hz q Λ) :=
  w.rows (SemanticTrace.rootRowIndex (sampledCfg T z hz))

/-- Explicit `Λ` bounds for all six nouns in the three public-root comparison pairs. -/
structure RootPairLeavesBounded
    (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0)
    {q Λ : ℕ} (w : StrategySemanticData T z hz q Λ) : Prop where
  semantic_subject : (rootData w).root.subject.leaves ≤ Λ
  public_subject : T.claim.subject.leaves ≤ Λ
  semantic_formula : (rootData w).root.formula.leaves ≤ Λ
  public_formula : T.claim.formula.leaves ≤ Λ
  semantic_result : (rootData w).root.result.leaves ≤ Λ
  public_result : T.claim.result.leaves ≤ Λ

/-- The exact occurrence list: three public bindings first, then every semantic occurrence. -/
def pairs
    (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0)
    {q Λ : ℕ} (w : StrategySemanticData T z hz q Λ) :
    List (Noun × Noun) :=
  [((rootData w).root.subject, T.claim.subject),
    ((rootData w).root.formula, T.claim.formula),
    ((rootData w).root.result, T.claim.result)] ++
    (SemanticTrace.comparisonCensus w).map SemanticTrace.ComparisonUse.pair

/-- All pair-list leaf bounds: the six root bounds are explicit, and semantic bounds are inherited
from `ExactExecutionSemanticData`. -/
theorem pairs_leaves_bounded
    (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0)
    {q Λ : ℕ} (w : StrategySemanticData T z hz q Λ)
    (hroot : RootPairLeavesBounded T z hz w) :
    ∀ pair ∈ pairs T z hz w,
      pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ := by
  intro pair hpair
  simp only [pairs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with (rfl | rfl | rfl) | hsemantic
  · exact ⟨hroot.semantic_subject, hroot.public_subject⟩
  · exact ⟨hroot.semantic_formula, hroot.public_formula⟩
  · exact ⟨hroot.semantic_result, hroot.public_result⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hsemantic
    exact SemanticTrace.census_leaves_bounded w hc

/-- Sampled-witness, occurrence-preserving census. -/
def canonical
    (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0)
    {q Λ : ℕ} (w : StrategySemanticData T z hz q Λ)
    (hroot : RootPairLeavesBounded T z hz w) :
    ComparisonCensus Λ :=
  ComparisonCensus.ofPairList (pairs T z hz w)
    (pairs_leaves_bounded T z hz w hroot)

/-- The canonical census contains exactly the three bindings plus every semantic occurrence. -/
@[simp]
theorem canonical_count
    (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0)
    {q Λ : ℕ} (w : StrategySemanticData T z hz q Λ)
    (hroot : RootPairLeavesBounded T z hz w) :
    (canonical T z hz w hroot).count =
      3 + (SemanticTrace.comparisonCensus w).length := by
  simp [canonical, pairs]
  omega

/-- The count is at most three public bindings plus ten semantic comparisons per compute row. -/
theorem canonical_count_le
    (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0)
    {q Λ : ℕ} (w : StrategySemanticData T z hz q Λ)
    (hroot : RootPairLeavesBounded T z hz w) :
    (canonical T z hz w hroot).count ≤
      3 + 10 * (sampledCfg T z hz).compRows := by
  rw [canonical_count]
  exact Nat.add_le_add_left (SemanticTrace.comparisonCensus_count_le w) 3

/-- The semantic-root/public-subject pair is literally occurrence zero. -/
theorem subject_pair_at_zero
    (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0)
    {q Λ : ℕ} (w : StrategySemanticData T z hz q Λ)
    (hroot : RootPairLeavesBounded T z hz w) :
    (canonical T z hz w hroot).pair
        ⟨0, by simp [canonical, pairs]⟩ =
      ((rootData w).root.subject, T.claim.subject) :=
  rfl

/-- The semantic-root/public-formula pair is literally occurrence one. -/
theorem formula_pair_at_one
    (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0)
    {q Λ : ℕ} (w : StrategySemanticData T z hz q Λ)
    (hroot : RootPairLeavesBounded T z hz w) :
    (canonical T z hz w hroot).pair
        ⟨1, by simp [canonical, pairs]⟩ =
      ((rootData w).root.formula, T.claim.formula) :=
  rfl

/-- The semantic-root/public-result pair is literally occurrence two. -/
theorem result_pair_at_two
    (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0)
    {q Λ : ℕ} (w : StrategySemanticData T z hz q Λ)
    (hroot : RootPairLeavesBounded T z hz w) :
    (canonical T z hz w hroot).pair
        ⟨2, by simp [canonical, pairs]⟩ =
      ((rootData w).root.result, T.claim.result) :=
  rfl

/-- Every semantic occurrence has a lookup in the strategy-bound census. -/
theorem semantic_pair_lookup
    (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0)
    {q Λ : ℕ} (w : StrategySemanticData T z hz q Λ)
    (hroot : RootPairLeavesBounded T z hz w)
    {c : SemanticTrace.ComparisonUse}
    (hc : c ∈ SemanticTrace.comparisonCensus w) :
    ∃ i : Fin (canonical T z hz w hroot).count,
      (canonical T z hz w hroot).pair i = c.pair := by
  apply ComparisonCensus.exists_pair_of_mem
  rw [pairs, List.mem_append]
  exact Or.inr (List.mem_map.mpr ⟨c, hc, rfl⟩)

/-- Existing state-indexed `ComparisonListed` occurrences remain covered. -/
theorem comparisonListed_pair_lookup
    (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0)
    {q Λ : ℕ} (w : StrategySemanticData T z hz q Λ)
    (hroot : RootPairLeavesBounded T z hz w)
    (row : Fin (sampledCfg T z hz).compRows)
    (role : SemanticTrace.ComparisonRole) (left right : Noun)
    (hlisted : SemanticTrace.ComparisonListed (w.rows row) role left right) :
    ∃ i : Fin (canonical T z hz w hroot).count,
      (canonical T z hz w hroot).pair i = (left, right) := by
  let c : SemanticTrace.ComparisonUse :=
    { role := role, left := left, right := right }
  have hc : c ∈ SemanticTrace.comparisonCensus w :=
    SemanticTrace.comparison_mem_census w row c hlisted
  obtain ⟨i, hi⟩ := semantic_pair_lookup T z hz w hroot hc
  exact ⟨i, by simpa [c, SemanticTrace.ComparisonUse.pair] using hi⟩

/-- OP9's axis-atom occurrence remains covered by the same strategy-bound census. -/
theorem op9_axis_pair_lookup
    (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0)
    {q Λ : ℕ} (w : StrategySemanticData T z hz q Λ)
    (hroot : RootPairLeavesBounded T z hz w)
    (row : Fin (sampledCfg T z hz).compRows)
    (gate : Σ tail : OpcodeSemantics.TailRealization
        ((sampledExec T z hz).computeRowAt row).2.1.z
        ((sampledExec T z hz).computeRowAt row).2.2.2,
      SemanticTrace.AxisAtomComparisonCertificate
        ((sampledExec T z hz).computeRowAt row).2.1.z q
        ((sampledExec T z hz).computeRowAt row).2.2.2 tail)
    (hgate : gate ∈ (w.rows row).axisGates) :
    ∃ i : Fin (canonical T z hz w hroot).count,
      (canonical T z hz w hroot).pair i =
        (gate.1.head, .atom gate.2.axis) := by
  apply comparisonListed_pair_lookup T z hz w hroot row .axisAtom
  exact (w.rows row).axisGate_listed gate hgate

/-! ## Seed-independent census from a bound semantic skeleton -/

/-- Total pre-seed projection of a decomposition noun.  The fallback is unreachable in every
slot used by `skeletonComparisons`; making the projection total keeps the occurrence list simple. -/
def skeletonDec (s : SemanticStrategy.ComputeRowSkeleton)
    (slot : SemanticStrategy.DecSlot) : Noun :=
  if h : SemanticStrategy.decActive s.state slot = true
  then s.decomposition slot h
  else .atom 0

/-- Total pre-seed projection of one subformula noun. -/
def skeletonSubformula (s : SemanticStrategy.ComputeRowSkeleton)
    (i : Fin 3) (slot : SemanticStrategy.TripleSlot) : Noun :=
  if h : (i : ℕ) < ComputeTable.fanoutComp s.state
  then s.subformula i h slot
  else .atom 0

/-- Total pre-seed projection of one memory-record axis. -/
def skeletonMemoryAxis (s : SemanticStrategy.ComputeRowSkeleton)
    (i : Fin 3) : ℕ :=
  if h : (i : ℕ) < Nock.Framework.recordCount s.state
  then (s.memoryRecord i h).axis
  else 0

/-- Public constructor for one fixed skeleton comparison occurrence. -/
def skeletonUse (role : SemanticTrace.ComparisonRole)
    (left right : Noun) : SemanticTrace.ComparisonUse :=
  { role := role, left := left, right := right }

/-- Exact state-indexed comparison extraction from one pre-seed skeleton row at the characteristic.

The order and multiplicity match `SemanticTrace.requiredComparisonRoles`.  In particular OP6 keeps
both occurrences comparing the same recursive formula to its two branch formulas, and OP9 includes
the axis-atom pair sourced from skeleton memory record `mr3`.  OP4 compares against the paper's
modular target at `ringChar K`, including the top-residue wrap. -/
def skeletonComparisons {K : Type*} [Field K]
    (s : SemanticStrategy.ComputeRowSkeleton) :
    List SemanticTrace.ComparisonUse :=
  let d := skeletonDec s
  let sf := skeletonSubformula s
  match s.state with
  | .s0 =>
      [skeletonUse .opcodeHead (d .f_h) (.atom 0),
        skeletonUse .formulaCons s.formula (.cell (d .f_h) (d .f_t)),
        skeletonUse .recursiveFormula (d .f_t) (.atom (skeletonMemoryAxis s 1))]
  | .s1 =>
      [skeletonUse .opcodeHead (d .f_h) (.atom 1),
        skeletonUse .formulaCons s.formula (.cell (d .f_h) (d .f_t)),
        skeletonUse .producedResult s.evaluation (d .f_t)]
  | .s2 =>
      [skeletonUse .opcodeHead (d .f_h) (.atom 2),
        skeletonUse .formulaCons s.formula (.cell (d .f_h) (d .f_t)),
        skeletonUse .tailCons (d .f_t) (.cell (d .f_th) (d .f_tt)),
        skeletonUse .recursiveSubject (sf 0 .subject) s.subject,
        skeletonUse .recursiveFormula (sf 0 .formula) (d .f_th),
        skeletonUse .recursiveSubject (sf 1 .subject) s.subject,
        skeletonUse .recursiveFormula (sf 1 .formula) (d .f_tt),
        skeletonUse .recursiveSubject (sf 2 .subject) (sf 0 .result),
        skeletonUse .recursiveFormula (sf 2 .formula) (sf 1 .result),
        skeletonUse .producedResult s.evaluation (sf 2 .result)]
  | .s3 =>
      [skeletonUse .opcodeHead (d .f_h) (.atom 3),
        skeletonUse .formulaCons s.formula (.cell (d .f_h) (d .f_t)),
        skeletonUse .recursiveSubject (sf 0 .subject) s.subject,
        skeletonUse .recursiveFormula (sf 0 .formula) (d .f_t),
        skeletonUse .producedResult s.evaluation (Noun.wut (sf 0 .result))]
  | .s4 =>
      [skeletonUse .opcodeHead (d .f_h) (.atom 4),
        skeletonUse .formulaCons s.formula (.cell (d .f_h) (d .f_t)),
        skeletonUse .recursiveSubject (sf 0 .subject) s.subject,
        skeletonUse .recursiveFormula (sf 0 .formula) (d .f_t),
        skeletonUse .producedResult s.evaluation
          (OpcodeSemantics.incMod (ringChar K) (sf 0 .result))]
  | .s5 =>
      [skeletonUse .opcodeHead (d .f_h) (.atom 5),
        skeletonUse .formulaCons s.formula (.cell (d .f_h) (d .f_t)),
        skeletonUse .tailCons (d .f_t) (.cell (d .f_th) (d .f_tt)),
        skeletonUse .recursiveSubject (sf 0 .subject) s.subject,
        skeletonUse .recursiveFormula (sf 0 .formula) (d .f_th),
        skeletonUse .recursiveSubject (sf 1 .subject) s.subject,
        skeletonUse .recursiveFormula (sf 1 .formula) (d .f_tt),
        skeletonUse .equalityOperand (sf 0 .result) (sf 1 .result),
        skeletonUse .producedResult s.evaluation
          (Noun.tis (sf 0 .result) (sf 1 .result))]
  | .s6 =>
      [skeletonUse .opcodeHead (d .f_h) (.atom 6),
        skeletonUse .formulaCons s.formula (.cell (d .f_h) (d .f_t)),
        skeletonUse .tailCons (d .f_t) (.cell (d .f_th) (d .f_tt)),
        skeletonUse .branchTailCons (d .f_tt) (.cell (d .f_tth) (d .f_ttt)),
        skeletonUse .recursiveSubject (sf 0 .subject) s.subject,
        skeletonUse .recursiveFormula (sf 0 .formula) (d .f_tth),
        skeletonUse .recursiveFormula (sf 0 .formula) (d .f_ttt),
        skeletonUse .recursiveSubject (sf 1 .subject) s.subject,
        skeletonUse .recursiveFormula (sf 1 .formula) (d .f_th),
        skeletonUse .producedResult s.evaluation (sf 0 .result)]
  | .s7 =>
      [skeletonUse .opcodeHead (d .f_h) (.atom 7),
        skeletonUse .formulaCons s.formula (.cell (d .f_h) (d .f_t)),
        skeletonUse .tailCons (d .f_t) (.cell (d .f_th) (d .f_tt)),
        skeletonUse .recursiveSubject (sf 1 .subject) s.subject,
        skeletonUse .recursiveFormula (sf 1 .formula) (d .f_th),
        skeletonUse .recursiveSubject (sf 0 .subject) (sf 1 .result),
        skeletonUse .recursiveFormula (sf 0 .formula) (d .f_tt),
        skeletonUse .producedResult s.evaluation (sf 0 .result)]
  | .s8 =>
      [skeletonUse .opcodeHead (d .f_h) (.atom 8),
        skeletonUse .formulaCons s.formula (.cell (d .f_h) (d .f_t)),
        skeletonUse .tailCons (d .f_t) (.cell (d .f_th) (d .f_tt)),
        skeletonUse .recursiveSubject (sf 1 .subject) s.subject,
        skeletonUse .recursiveFormula (sf 1 .formula) (d .f_th),
        skeletonUse .recursiveSubject (sf 0 .subject)
          (.cell (sf 1 .result) s.subject),
        skeletonUse .recursiveFormula (sf 0 .formula) (d .f_tt),
        skeletonUse .producedResult s.evaluation (sf 0 .result)]
  | .s9 =>
      [skeletonUse .opcodeHead (d .f_h) (.atom 9),
        skeletonUse .formulaCons s.formula (.cell (d .f_h) (d .f_t)),
        skeletonUse .tailCons (d .f_t) (.cell (d .f_th) (d .f_tt)),
        skeletonUse .axisAtom (d .f_th) (.atom (skeletonMemoryAxis s 2)),
        skeletonUse .recursiveSubject (sf 0 .subject) s.subject,
        skeletonUse .recursiveFormula (sf 0 .formula) (d .f_tt),
        skeletonUse .recursiveSubject (sf 1 .subject) (sf 0 .result),
        skeletonUse .producedResult s.evaluation (sf 1 .result)]
  | .cons =>
      [skeletonUse .formulaCons s.formula (.cell (d .f_h) (d .f_t)),
        skeletonUse .recursiveSubject (sf 0 .subject) s.subject,
        skeletonUse .recursiveFormula (sf 0 .formula) (d .f_h),
        skeletonUse .recursiveSubject (sf 1 .subject) s.subject,
        skeletonUse .recursiveFormula (sf 1 .formula) (d .f_t),
        skeletonUse .producedResult s.evaluation
          (.cell (sf 0 .result) (sf 1 .result))]

/-- The skeleton extractor has exactly the production role sequence, including duplicate roles. -/
theorem skeletonComparisons_roles
    (K : Type*) [Field K] (s : SemanticStrategy.ComputeRowSkeleton) :
    (skeletonComparisons (K := K) s).map SemanticTrace.ComparisonUse.role =
      SemanticTrace.requiredComparisonRoles s.state := by
  cases h : s.state <;>
    simp [skeletonComparisons, h, skeletonUse,
      SemanticTrace.requiredComparisonRoles]

theorem skeletonComparisons_length_le
    (K : Type*) [Field K] (s : SemanticStrategy.ComputeRowSkeleton) :
    (skeletonComparisons (K := K) s).length ≤ 10 := by
  calc
    (skeletonComparisons (K := K) s).length =
        ((skeletonComparisons (K := K) s).map
          SemanticTrace.ComparisonUse.role).length := by simp
    _ = (SemanticTrace.requiredComparisonRoles s.state).length := by
      rw [skeletonComparisons_roles K]
    _ ≤ 10 := SemanticTrace.requiredComparisonRoles_length_le s.state

/-- All fixed row occurrences in canonical skeleton BFS order. -/
def skeletonComparisonCensus {K : Type*} [Field K]
    (S : SemanticStrategy.SemanticSkeleton) :
    List SemanticTrace.ComparisonUse :=
  (SemanticStrategy.computeSkeletonRows S).flatMap (skeletonComparisons (K := K))

/-- The fully seed-independent pair list.  Its first three entries are the skeleton root/public
claim bindings (definitionally self-pairs), followed by all fixed row occurrences. -/
def boundPairs (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)) :
    List (Noun × Noun) :=
  let claim := T.skeleton.publicClaim
  [(T.skeleton.computeTree.label.subject, claim.subject),
    (T.skeleton.computeTree.label.formula, claim.formula),
    (T.skeleton.computeTree.label.evaluation, claim.result)] ++
    (skeletonComparisonCensus (K := K) T.skeleton).map SemanticTrace.ComparisonUse.pair

/-- The only field is the explicit leaf
bound needed by `ComparisonCensus`; its occurrence list depends solely on `T.skeleton`. -/
structure BoundP8Census
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)) (Λ : ℕ) : Prop where
  leaves_bounded :
    ∀ pair ∈ boundPairs T,
      pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ

namespace BoundP8Census

/-- The fixed `ComparisonCensus`; unlike `canonical`, it has no seed or post-seed semantic witness
argument. -/
def census
    {T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)} {Λ : ℕ}
    (C : BoundP8Census T Λ) : ComparisonCensus Λ :=
  ComparisonCensus.ofPairList (boundPairs T) C.leaves_bounded

@[simp]
theorem census_count
    {T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)} {Λ : ℕ}
    (C : BoundP8Census T Λ) :
    C.census.count = (boundPairs T).length :=
  rfl

theorem census_count_exact
    {T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)} {Λ : ℕ}
    (C : BoundP8Census T Λ) :
    C.census.count =
      3 + (skeletonComparisonCensus (K := K) T.skeleton).length := by
  rw [census_count]
  simp [boundPairs]
  omega

private theorem flatMap_length_le
    {α β : Type*} (bound : ℕ) (xs : List α) (f : α → List β)
    (h : ∀ x ∈ xs, (f x).length ≤ bound) :
    (xs.flatMap f).length ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hx := h x (by simp)
      have hxs : ∀ y ∈ xs, (f y).length ≤ bound :=
        fun y hy => h y (by simp [hy])
      have hi := ih hxs
      calc
        (f x).length + (List.flatMap f xs).length
            ≤ bound + xs.length * bound := Nat.add_le_add hx hi
        _ = (xs.length + 1) * bound := by
          simp [Nat.add_mul, Nat.add_comm]

/-- At most ten fixed internal comparison occurrences per canonical skeleton row. -/
theorem skeletonComparisonCensus_length_le
    (S : SemanticStrategy.SemanticSkeleton) :
    (skeletonComparisonCensus (K := K) S).length ≤
      10 * (SemanticStrategy.computeSkeletonRows S).length := by
  unfold skeletonComparisonCensus
  have h := flatMap_length_le 10
    (SemanticStrategy.computeSkeletonRows S) (skeletonComparisons (K := K))
    (fun s _ => skeletonComparisons_length_le K s)
  simpa [Nat.mul_comm] using h

/-- Global fixed-census workload bound. -/
theorem count_le
    {T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)} {Λ : ℕ}
    (C : BoundP8Census T Λ) :
    C.census.count ≤
      3 + 10 * (SemanticStrategy.computeSkeletonRows T.skeleton).length := by
  rw [census_count]
  simp only [boundPairs, List.length_append, List.length_cons, List.length_nil,
    List.length_map]
  have h := skeletonComparisonCensus_length_le (K := K) T.skeleton
  omega

end BoundP8Census

/-- Exact sampled configuration of a bound strategy. -/
abbrev boundSampledCfg
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) : ExactConfig F K :=
  (T.afterSeed z hz).payload.family.problem.cfg

/-- Exact sampled execution of a bound strategy. -/
abbrev boundSampledExec
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) : ExactExecution (boundSampledCfg T z hz) :=
  (T.afterSeed z hz).payload.family.problem.exec

/-- The skeleton and sampled execution have the same canonical compute-row count by `BindsAt`. -/
theorem bound_computeRows_length
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) :
    (SemanticStrategy.computeSkeletonRows T.skeleton).length =
      (boundSampledCfg T z hz).compRows := by
  calc
    (SemanticStrategy.computeSkeletonRows T.skeleton).length =
        (boundSampledExec T z hz).computeRows.length :=
      (T.afterSeed z hz).binds.computeRows.length_eq
    _ = (boundSampledCfg T z hz).compRows :=
      (boundSampledExec T z hz).computeRows_length

/-- The pre-seed skeleton row at the exact sampled execution index. -/
def boundSkeletonRowAt
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0)
    (i : Fin (boundSampledCfg T z hz).compRows) :
    SemanticStrategy.ComputeRowSkeleton :=
  (SemanticStrategy.computeSkeletonRows T.skeleton).get
    (Fin.cast (bound_computeRows_length T z hz).symm i)

/-- Precise residual linkage not supplied by `BindsAt`.

`BindsAt` connects skeleton slots to table fingerprints, while semantic row data and local
certificates expose concrete nouns but do not identify every certificate noun with its skeleton
slot.  This residual states only that each sampled listed role/pair is the corresponding occurrence
in the fixed extractor for the same BFS row.  It contains no census, `SepSeed`, collision-event,
acceptance, target, or evaluator conclusion. -/
structure SkeletonComparisonCompatibility
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) {q Λ : ℕ}
    (w : SemanticTrace.ExactExecutionSemanticData q Λ
      (boundSampledCfg T z hz) (boundSampledExec T z hz)) : Prop where
  listed :
    ∀ (row : Fin (boundSampledCfg T z hz).compRows)
      (role : SemanticTrace.ComparisonRole) (left right : Noun),
      SemanticTrace.ComparisonListed (w.rows row) role left right →
      ∃ fixed ∈ skeletonComparisons (K := K) (boundSkeletonRowAt T z hz row),
        fixed.role = role ∧ fixed.pair = (left, right)

/-- Compatibility puts every sampled `ComparisonListed` pair at a fixed, pre-seed occurrence. -/
theorem bound_pair_lookup_of_comparisonListed
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (C : BoundP8Census T Λ) (z : K) (hz : z ≠ 0) {q : ℕ}
    (w : SemanticTrace.ExactExecutionSemanticData q Λ
      (boundSampledCfg T z hz) (boundSampledExec T z hz))
    (_certs : SemanticTrace.ExactExecutionLocalCertificates w)
    (hcompat : SkeletonComparisonCompatibility T z hz w)
    (row : Fin (boundSampledCfg T z hz).compRows)
    (role : SemanticTrace.ComparisonRole) (left right : Noun)
    (hlisted : SemanticTrace.ComparisonListed (w.rows row) role left right) :
    ∃ i : Fin C.census.count, C.census.pair i = (left, right) := by
  obtain ⟨fixed, hfixed, _, hp⟩ :=
    hcompat.listed row role left right hlisted
  apply ComparisonCensus.exists_pair_of_mem
  rw [boundPairs, List.mem_append]
  apply Or.inr
  apply List.mem_map.mpr
  refine ⟨fixed, ?_, hp⟩
  unfold skeletonComparisonCensus
  rw [List.mem_flatMap]
  exact ⟨boundSkeletonRowAt T z hz row, List.get_mem _ _, hfixed⟩

section Finite

variable [Fintype K] [DecidableEq K]

/-- Every listed pair is separated outside the canonical bad-seed event. -/
theorem sepSeed_of_not_mem_badSeeds
    {Λ : ℕ} (C : ComparisonCensus Λ) (z : K)
    (hz : z ∉ C.badSeeds (K := K)) (i : Fin C.count) :
    GlobalCarryRecognizer.SepSeed z (C.pair i).1 (C.pair i).2 := by
  by_contra hsep
  exact hz ((ComparisonCensus.mem_badSeeds_iff C z).2 ⟨i, hsep⟩)

/-- The single pre-seed census supports one global bad-seed bound for the whole strategy. -/
theorem BoundP8Census.badSeeds_card_le
    {T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)} {Λ : ℕ}
    (C : BoundP8Census T Λ) :
    (C.census.badSeeds (K := K)).card ≤
      (3 + 10 * (SemanticStrategy.computeSkeletonRows T.skeleton).length) *
        (2 * Λ - 1) := by
  exact C.census.badSeeds_card_le.trans
    (Nat.mul_le_mul_right (2 * Λ - 1) C.count_le)

/-- Any failed sampled `ComparisonListed` separation is covered by the one fixed bad-seed set. -/
theorem bound_badSeed_of_comparisonListed
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (C : BoundP8Census T Λ) (z : K) (hz : z ≠ 0) {q : ℕ}
    (w : SemanticTrace.ExactExecutionSemanticData q Λ
      (boundSampledCfg T z hz) (boundSampledExec T z hz))
    (certs : SemanticTrace.ExactExecutionLocalCertificates w)
    (hcompat : SkeletonComparisonCompatibility T z hz w)
    (row : Fin (boundSampledCfg T z hz).compRows)
    (role : SemanticTrace.ComparisonRole) (left right : Noun)
    (hlisted : SemanticTrace.ComparisonListed (w.rows row) role left right)
    (hbad : ¬ GlobalCarryRecognizer.SepSeed z left right) :
    z ∈ C.census.badSeeds (K := K) := by
  obtain ⟨i, hi⟩ :=
    bound_pair_lookup_of_comparisonListed T C z hz w certs hcompat
      row role left right hlisted
  rw [ComparisonCensus.mem_badSeeds_iff]
  exact ⟨i, by simpa [hi] using hbad⟩

/-- Outside the one fixed bad-seed event, compatibility identifies a sampled listed pair with the
corresponding fixed occurrence in the same canonical skeleton row, and that pair is separated. -/
theorem bound_comparisonListed_fixed_outside_badSeeds
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (C : BoundP8Census T Λ) (z : K) (hz : z ≠ 0) {q : ℕ}
    (w : SemanticTrace.ExactExecutionSemanticData q Λ
      (boundSampledCfg T z hz) (boundSampledExec T z hz))
    (certs : SemanticTrace.ExactExecutionLocalCertificates w)
    (hcompat : SkeletonComparisonCompatibility T z hz w)
    (row : Fin (boundSampledCfg T z hz).compRows)
    (role : SemanticTrace.ComparisonRole) (left right : Noun)
    (hlisted : SemanticTrace.ComparisonListed (w.rows row) role left right)
    (hgood : z ∉ C.census.badSeeds (K := K)) :
    ∃ fixed ∈ skeletonComparisons (K := K) (boundSkeletonRowAt T z hz row),
      fixed.role = role ∧ fixed.pair = (left, right) ∧
        GlobalCarryRecognizer.SepSeed z left right := by
  obtain ⟨fixed, hfixed, hrole, hp⟩ :=
    hcompat.listed row role left right hlisted
  obtain ⟨i, hi⟩ :=
    bound_pair_lookup_of_comparisonListed T C z hz w certs hcompat
      row role left right hlisted
  have hsep := sepSeed_of_not_mem_badSeeds C.census z hgood i
  exact ⟨fixed, hfixed, hrole, hp, by simpa [hi] using hsep⟩

/-- OP9's sampled axis-atom comparison is the fixed skeleton `mr3` axis occurrence outside the
same global bad-seed event. -/
theorem bound_op9_axis_fixed_outside_badSeeds
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (C : BoundP8Census T Λ) (z : K) (hz : z ≠ 0) {q : ℕ}
    (w : SemanticTrace.ExactExecutionSemanticData q Λ
      (boundSampledCfg T z hz) (boundSampledExec T z hz))
    (certs : SemanticTrace.ExactExecutionLocalCertificates w)
    (hcompat : SkeletonComparisonCompatibility T z hz w)
    (row : Fin (boundSampledCfg T z hz).compRows)
    (gate : Σ tail : OpcodeSemantics.TailRealization
        ((boundSampledExec T z hz).computeRowAt row).2.1.z
        ((boundSampledExec T z hz).computeRowAt row).2.2.2,
      SemanticTrace.AxisAtomComparisonCertificate
        ((boundSampledExec T z hz).computeRowAt row).2.1.z q
        ((boundSampledExec T z hz).computeRowAt row).2.2.2 tail)
    (hgate : gate ∈ (w.rows row).axisGates)
    (hgood : z ∉ C.census.badSeeds (K := K)) :
    ∃ fixed ∈ skeletonComparisons (K := K) (boundSkeletonRowAt T z hz row),
      fixed.role = .axisAtom ∧
        fixed.pair = (gate.1.head, .atom gate.2.axis) ∧
        GlobalCarryRecognizer.SepSeed z gate.1.head (.atom gate.2.axis) := by
  apply bound_comparisonListed_fixed_outside_badSeeds
    T C z hz w certs hcompat row .axisAtom gate.1.head (.atom gate.2.axis)
  · exact (w.rows row).axisGate_listed gate hgate
  · exact hgood

/-- A bad `ComparisonListed` semantic occurrence lies in the canonical collision event. -/
theorem collisionEvent_covers_comparisonListed
    (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0)
    {q Λ : ℕ} (w : StrategySemanticData T z hz q Λ)
    (hroot : RootPairLeavesBounded T z hz w)
    (row : Fin (sampledCfg T z hz).compRows)
    (role : SemanticTrace.ComparisonRole) (left right : Noun)
    (hlisted : SemanticTrace.ComparisonListed (w.rows row) role left right)
    (ω : JointCoins K)
    (hbad :
      ¬ GlobalCarryRecognizer.SepSeed (nprSeed ω) left right) :
    ω ∈ collisionFailureEvent (K := K) (canonical T z hz w hroot) := by
  rw [mem_collisionFailureEvent_iff]
  obtain ⟨i, hi⟩ :=
    comparisonListed_pair_lookup T z hz w hroot row role left right hlisted
  exact ⟨i, by simpa [hi] using hbad⟩

/-- A bad OP9 axis-atom occurrence lies in the same canonical collision event. -/
theorem collisionEvent_covers_op9_axis
    (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0)
    {q Λ : ℕ} (w : StrategySemanticData T z hz q Λ)
    (hroot : RootPairLeavesBounded T z hz w)
    (row : Fin (sampledCfg T z hz).compRows)
    (gate : Σ tail : OpcodeSemantics.TailRealization
        ((sampledExec T z hz).computeRowAt row).2.1.z
        ((sampledExec T z hz).computeRowAt row).2.2.2,
      SemanticTrace.AxisAtomComparisonCertificate
        ((sampledExec T z hz).computeRowAt row).2.1.z q
        ((sampledExec T z hz).computeRowAt row).2.2.2 tail)
    (hgate : gate ∈ (w.rows row).axisGates)
    (ω : JointCoins K)
    (hbad :
      ¬ GlobalCarryRecognizer.SepSeed (nprSeed ω)
        gate.1.head (.atom gate.2.axis)) :
    ω ∈ collisionFailureEvent (K := K) (canonical T z hz w hroot) := by
  apply collisionEvent_covers_comparisonListed T z hz w hroot row .axisAtom
    gate.1.head (.atom gate.2.axis)
  · exact (w.rows row).axisGate_listed gate hgate
  · exact hbad

/-- The public claim's three nouns satisfy the numeric bound needed to reflect equal NPR
fingerprints back to noun equality. -/
structure PublicClaimBoundedBy (q : ℕ) (claim : P8PublicClaim) : Prop where
  subject : FieldEmbedding.BoundedBy q claim.subject
  formula : FieldEmbedding.BoundedBy q claim.formula
  result : FieldEmbedding.BoundedBy q claim.result

/-- Outside the canonical collision event, the semantic root nouns are exactly the public claim
nouns.  The proof uses only the three seed-time binding equations, root realization equations, the
same sampled seed, `SepSeed`, bounded Nat-cast injectivity, and noun bounds. -/
theorem root_nouns_eq_publicClaim
    (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0)
    {q Λ : ℕ} (w : StrategySemanticData T z hz q Λ)
    (hroot : RootPairLeavesBounded T z hz w)
    (hclaim : PublicClaimBoundedBy q T.claim)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hgood :
      z ∉ (canonical T z hz w hroot).badSeeds (K := K)) :
    (rootData w).root.subject = T.claim.subject ∧
      (rootData w).root.formula = T.claim.formula ∧
      (rootData w).root.result = T.claim.result := by
  let C := T.afterSeed z hz
  let ri := SemanticTrace.rootRowIndex (sampledCfg T z hz)
  have hseed :
      ((sampledExec T z hz).computeRowAt ri).2.1.z = z :=
    (w.same_seed ri).trans C.sampled_seed
  have hsubjectSep :
      GlobalCarryRecognizer.SepSeed z
        (rootData w).root.subject T.claim.subject := by
    have h := sepSeed_of_not_mem_badSeeds
      (canonical T z hz w hroot) z hgood
      ⟨0, by simp [canonical, pairs]⟩
    simpa [subject_pair_at_zero] using h
  have hformulaSep :
      GlobalCarryRecognizer.SepSeed z
        (rootData w).root.formula T.claim.formula := by
    have h := sepSeed_of_not_mem_badSeeds
      (canonical T z hz w hroot) z hgood
      ⟨1, by simp [canonical, pairs]⟩
    simpa [formula_pair_at_one] using h
  have hresultSep :
      GlobalCarryRecognizer.SepSeed z
        (rootData w).root.result T.claim.result := by
    have h := sepSeed_of_not_mem_badSeeds
      (canonical T z hz w hroot) z hgood
      ⟨2, by simp [canonical, pairs]⟩
    simpa [result_pair_at_two] using h
  have hcommitSubject :
      ((sampledExec T z hz).computePubAt ri).s =
        GlobalCarryRecognizer.enc z T.claim.subject := by
    simpa [C, ri, sampledCfg, sampledExec, exactRootComputePub,
      SemanticTrace.rootRowIndex] using C.subject_binding
  have hcommitFormula :
      ((sampledExec T z hz).computePubAt ri).f =
        GlobalCarryRecognizer.enc z T.claim.formula := by
    simpa [C, ri, sampledCfg, sampledExec, exactRootComputePub,
      SemanticTrace.rootRowIndex] using C.formula_binding
  have hcommitResult :
      ((sampledExec T z hz).computePubAt ri).e =
        GlobalCarryRecognizer.enc z T.claim.result := by
    simpa [C, ri, sampledCfg, sampledExec, exactRootComputePub,
      SemanticTrace.rootRowIndex] using C.result_binding
  have hsemanticBounds := (rootData w).root_bounded
  constructor
  · apply GlobalCarryRecognizer.noun_eq_of_enc_eq z
      (rootData w).root.subject T.claim.subject
      hsubjectSep hcast hsemanticBounds.1 hclaim.subject
    calc
      GlobalCarryRecognizer.enc z (rootData w).root.subject =
          GlobalCarryRecognizer.enc
            ((sampledExec T z hz).computeRowAt ri).2.1.z
            (rootData w).root.subject := by rw [hseed]
      _ = ((sampledExec T z hz).computePubAt ri).s := by
        exact (rootData w).root.subject_realizes.symm
      _ = GlobalCarryRecognizer.enc z T.claim.subject := hcommitSubject
  · constructor
    · apply GlobalCarryRecognizer.noun_eq_of_enc_eq z
        (rootData w).root.formula T.claim.formula
        hformulaSep hcast hsemanticBounds.2.1 hclaim.formula
      calc
        GlobalCarryRecognizer.enc z (rootData w).root.formula =
            GlobalCarryRecognizer.enc
              ((sampledExec T z hz).computeRowAt ri).2.1.z
              (rootData w).root.formula := by rw [hseed]
        _ = ((sampledExec T z hz).computePubAt ri).f := by
          exact (rootData w).root.formula_realizes.symm
        _ = GlobalCarryRecognizer.enc z T.claim.formula := hcommitFormula
    · apply GlobalCarryRecognizer.noun_eq_of_enc_eq z
        (rootData w).root.result T.claim.result
        hresultSep hcast hsemanticBounds.2.2 hclaim.result
      calc
        GlobalCarryRecognizer.enc z (rootData w).root.result =
            GlobalCarryRecognizer.enc
              ((sampledExec T z hz).computeRowAt ri).2.1.z
              (rootData w).root.result := by rw [hseed]
        _ = ((sampledExec T z hz).computePubAt ri).e := by
          exact (rootData w).root.result_realizes.symm
        _ = GlobalCarryRecognizer.enc z T.claim.result := hcommitResult

/-- Joint-coin form: if the joint collision event does not occur and its NPR coordinate is the
same sampled seed, the three semantic root nouns equal the public claim nouns. -/
theorem root_nouns_eq_publicClaim_of_not_mem_collisionEvent
    (T : P8Strategy (F := F) (K := K)) (z : K) (hz : z ≠ 0)
    {q Λ : ℕ} (w : StrategySemanticData T z hz q Λ)
    (hroot : RootPairLeavesBounded T z hz w)
    (hclaim : PublicClaimBoundedBy q T.claim)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (ω : JointCoins K) (hsampled : nprSeed ω = z)
    (hgood :
      ω ∉ collisionFailureEvent (K := K) (canonical T z hz w hroot)) :
    (rootData w).root.subject = T.claim.subject ∧
      (rootData w).root.formula = T.claim.formula ∧
      (rootData w).root.result = T.claim.result := by
  apply root_nouns_eq_publicClaim T z hz w hroot hclaim hcast
  intro hbad
  obtain ⟨i, hi⟩ :=
    (ComparisonCensus.mem_badSeeds_iff
      (canonical T z hz w hroot) z).1 hbad
  apply hgood
  rw [mem_collisionFailureEvent_iff]
  exact ⟨i, by simpa [hsampled] using hi⟩

end Finite

end P8Census

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.P8Census.canonical_count
#print axioms Nock.NockVMROM.Thm54.P8Census.canonical_count_le
#print axioms Nock.NockVMROM.Thm54.P8Census.comparisonListed_pair_lookup
#print axioms Nock.NockVMROM.Thm54.P8Census.op9_axis_pair_lookup
#print axioms Nock.NockVMROM.Thm54.P8Census.collisionEvent_covers_comparisonListed
#print axioms Nock.NockVMROM.Thm54.P8Census.collisionEvent_covers_op9_axis
#print axioms Nock.NockVMROM.Thm54.P8Census.root_nouns_eq_publicClaim
#print axioms Nock.NockVMROM.Thm54.P8Census.root_nouns_eq_publicClaim_of_not_mem_collisionEvent
#print axioms Nock.NockVMROM.Thm54.P8Census.skeletonComparisons_roles
#print axioms Nock.NockVMROM.Thm54.P8Census.BoundP8Census.count_le
#print axioms Nock.NockVMROM.Thm54.P8Census.BoundP8Census.badSeeds_card_le
#print axioms Nock.NockVMROM.Thm54.P8Census.bound_pair_lookup_of_comparisonListed
#print axioms Nock.NockVMROM.Thm54.P8Census.bound_badSeed_of_comparisonListed
#print axioms Nock.NockVMROM.Thm54.P8Census.bound_comparisonListed_fixed_outside_badSeeds
#print axioms Nock.NockVMROM.Thm54.P8Census.bound_op9_axis_fixed_outside_badSeeds
