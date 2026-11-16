import Nock.NockVMROM.Thm54.P8Census

/-!
# Semantic rows canonically bound to the pre-seed skeleton

This file constructs semantic row data from the nouns already present in a
`SemanticStrategy.SemanticSkeleton`.  In particular, no noun is selected from a
post-seed fingerprint realization.
-/

namespace Nock.NockVMROM.Thm54.BoundSemanticTrace

open scoped Classical
open Nock Nock.Walk

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {p : ℕ} [CharP K p]

abbrev RowSkeleton := SemanticStrategy.ComputeRowSkeleton

/-- Seed-independent operational facts which are not consequences of noun/fingerprint binding.

The served lookups use the exact skeleton nouns and axes.  Modular OP4 is total and contributes no
operational side condition.  Size-window facts are deliberately absent: they fail at low-order
seeds and are supplied separately outside the counted size-window event. -/
structure SkeletonOperationalCore (s : RowSkeleton) : Prop where
  s0_record :
    ∀ h : s.state = .s0,
      let mr := s.memoryRecord (1 : Fin 3) (by simp [h, Nock.Framework.recordCount])
      mr.root = s.subject ∧ mr.child = s.evaluation
  s0_served :
    s.state = .s0 →
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun s.subject 1)
        (P8Census.skeletonMemoryAxis s 1) s.evaluation
  s9_record :
    ∀ h : s.state = .s9,
      let mr := s.memoryRecord (2 : Fin 3) (by simp [h, Nock.Framework.recordCount])
      mr.root = P8Census.skeletonSubformula s 0 .result ∧
        mr.child = P8Census.skeletonSubformula s 1 .formula
  s9_served :
    s.state = .s9 →
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun
          (P8Census.skeletonSubformula s 0 .result) 1)
        (P8Census.skeletonMemoryAxis s 2)
        (P8Census.skeletonSubformula s 1 .formula)

/-- The three seed-dependent size-window facts consumed by OP3, OP4, and OP6. -/
structure SkeletonSizeWindowPremises (z : K) (s : RowSkeleton) : Prop where
  s3_window :
    s.state = .s3 →
      OpcodeSemantics.SizeWindow z
        (P8Census.skeletonSubformula s 0 .result)
  s4_window :
    s.state = .s4 →
      OpcodeSemantics.SizeWindow z
        (P8Census.skeletonSubformula s 0 .result)
  s6_window :
    s.state = .s6 →
      OpcodeSemantics.SizeWindow z
        (P8Census.skeletonSubformula s 1 .result)

/-- The complete row-local operational package at one seed.

Production code constructs this from a seed-independent `SkeletonOperationalCore` and window facts
proved outside the counted low-order event.  It is retained as the local consumer interface so the
opcode scheduling proof continues to expose every served lookup and record equation explicitly.
The modulus is canonically the characteristic of `K`. -/
structure SkeletonOperationalPremises (q : ℕ) (z : K)
    (s : RowSkeleton) : Prop
    extends SkeletonOperationalCore s, SkeletonSizeWindowPremises z s where
  q_eq_ringChar : q = ringChar K

def SkeletonOperationalPremises.ofCoreAndWindows
    {q : ℕ} {z : K} {s : RowSkeleton}
    (hq : q = ringChar K)
    (core : SkeletonOperationalCore s)
    (windows : SkeletonSizeWindowPremises z s) :
    SkeletonOperationalPremises q z s :=
  { core, windows with q_eq_ringChar := hq }

/-- The exact seed-independent `q` bounds needed to turn the fixed census'
separation event into `PairFaithful`.  This is deliberately separate from
`SkeletonOperationalPremises`: it mentions comparisons but contains no
operational or target conclusion. -/
def FixedComparisonBoundedBy
    (q : ℕ) (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)) : Prop :=
  ∀ s ∈ SemanticStrategy.computeSkeletonRows T.skeleton,
    ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
      FieldEmbedding.BoundedBy q c.left ∧
        FieldEmbedding.BoundedBy q c.right

/-- Unlike `P8Census.boundPairs`, this definition has no `BoundP8Strategy` parameter and therefore
cannot project a family, exact problem, table auxiliary witness, IO assignment, or walk response. -/
def skeletonPairs (K : Type*) [Field K] (S : SemanticStrategy.SemanticSkeleton) :
    List (Noun × Noun) :=
  let claim := S.publicClaim
  [(S.computeTree.label.subject, claim.subject),
    (S.computeTree.label.formula, claim.formula),
    (S.computeTree.label.evaluation, claim.result)] ++
    (P8Census.skeletonComparisonCensus (K := K) S).map SemanticTrace.ComparisonUse.pair

structure SkeletonP8Census
    (K : Type*) [Field K] (S : SemanticStrategy.SemanticSkeleton) (Λ : ℕ) : Prop where
  leaves_bounded :
    ∀ pair ∈ skeletonPairs K S,
      pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ

namespace SkeletonP8Census

def census {K : Type*} [Field K] {S : SemanticStrategy.SemanticSkeleton} {Λ : ℕ}
    (C : SkeletonP8Census K S Λ) : ComparisonCensus Λ :=
  ComparisonCensus.ofPairList (skeletonPairs K S) C.leaves_bounded

@[simp] theorem census_count
    {S : SemanticStrategy.SemanticSkeleton} {Λ : ℕ}
    (C : SkeletonP8Census K S Λ) :
    C.census.count = (skeletonPairs K S).length :=
  rfl

theorem count_le
    {S : SemanticStrategy.SemanticSkeleton} {Λ : ℕ}
    (C : SkeletonP8Census K S Λ) :
    C.census.count ≤
      3 + 10 * (SemanticStrategy.computeSkeletonRows S).length := by
  rw [census_count]
  simp only [skeletonPairs, List.length_append, List.length_cons, List.length_nil,
    List.length_map]
  have h := P8Census.BoundP8Census.skeletonComparisonCensus_length_le (K := K) S
  omega

end SkeletonP8Census

/-- Seed-independent comparison bounds stated only for a skeleton. -/
def SkeletonComparisonBoundedBy
    (K : Type*) [Field K] (q : ℕ) (S : SemanticStrategy.SemanticSkeleton) : Prop :=
  ∀ s ∈ SemanticStrategy.computeSkeletonRows S,
    ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
      FieldEmbedding.BoundedBy q c.left ∧
        FieldEmbedding.BoundedBy q c.right

/-- `BindsAt` alone gives the canonical compute-row cardinality agreement. -/
theorem computeRows_length_of_binds
    {S : SemanticStrategy.SemanticSkeleton}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {z : K}
    (binds : SemanticStrategy.BindsAt z S cfg exec) :
    (SemanticStrategy.computeSkeletonRows S).length = cfg.compRows := by
  calc
    (SemanticStrategy.computeSkeletonRows S).length = exec.computeRows.length :=
      binds.derived_computeRows.length_eq
    _ = cfg.compRows := exec.computeRows_length

/-- Canonical pre-seed skeleton row at an explicit exact execution index. -/
def skeletonRowAt
    (S : SemanticStrategy.SemanticSkeleton)
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) {z : K}
    (binds : SemanticStrategy.BindsAt z S cfg exec)
    (i : Fin cfg.compRows) : SemanticStrategy.ComputeRowSkeleton :=
  (SemanticStrategy.computeSkeletonRows S).get
    (Fin.cast (computeRows_length_of_binds binds).symm i)

/-- The explicit `BindsAt` context supplies the row binding without opening any semantic family. -/
theorem skeletonRowAt_binds
    (S : SemanticStrategy.SemanticSkeleton)
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) {z : K}
    (binds : SemanticStrategy.BindsAt z S cfg exec)
    (i : Fin cfg.compRows) :
    SemanticStrategy.BindComputeRow z (skeletonRowAt S exec binds i)
      (exec.computeRowAt i) := by
  let hs : Fin (SemanticStrategy.computeSkeletonRows S).length :=
    Fin.cast (computeRows_length_of_binds binds).symm i
  let he : Fin exec.computeRows.length :=
    Fin.cast exec.computeRows_length.symm i
  have h := binds.derived_computeRows.get hs.isLt he.isLt
  simpa [hs, he, skeletonRowAt, ExactExecution.computeRowAt] using h

/-- The OP9 axis comparison is definitionally tied to skeleton memory record
`mr3`, with no noun selected after the seed. -/
@[simp]
theorem op9AxisUse_right_is_mr3 (s : RowSkeleton) :
    (P8Census.skeletonUse .axisAtom
      (P8Census.skeletonDec s .f_th)
      (.atom (P8Census.skeletonMemoryAxis s 2))).right =
        .atom (P8Census.skeletonMemoryAxis s 2) :=
  rfl

theorem boundSkeletonRowAt_binds
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0)
    (i : Fin (P8Census.boundSampledCfg T z hz).compRows) :
    SemanticStrategy.BindComputeRow z
      (P8Census.boundSkeletonRowAt T z hz i)
      ((P8Census.boundSampledExec T z hz).computeRowAt i) := by
  let hs : Fin (SemanticStrategy.computeSkeletonRows T.skeleton).length :=
    Fin.cast (P8Census.bound_computeRows_length T z hz).symm i
  let he : Fin (P8Census.boundSampledExec T z hz).computeRows.length :=
    Fin.cast (P8Census.boundSampledExec T z hz).computeRows_length.symm i
  have h := (T.afterSeed z hz).binds.derived_computeRows.get hs.isLt he.isLt
  simpa [hs, he, P8Census.boundSkeletonRowAt,
    ExactExecution.computeRowAt] using h

section Finite

variable [Fintype K] [DecidableEq K]

theorem fixedComparison_faithful
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (C : P8Census.BoundP8Census T Λ)
    (hb : FixedComparisonBoundedBy q T)
    (z : K) (hz : z ≠ 0)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (i : Fin (P8Census.boundSampledCfg T z hz).compRows)
    (c : SemanticTrace.ComparisonUse)
    (hc : c ∈ P8Census.skeletonComparisons (K := K)
      (P8Census.boundSkeletonRowAt T z hz i)) :
    OpcodeSemantics.PairFaithful z q c.left c.right := by
  have hsMem :
      P8Census.boundSkeletonRowAt T z hz i ∈
        SemanticStrategy.computeSkeletonRows T.skeleton :=
    List.get_mem _ _
  have hpairMem : c.pair ∈ P8Census.boundPairs T := by
    rw [P8Census.boundPairs, List.mem_append]
    apply Or.inr
    apply List.mem_map.mpr
    refine ⟨c, ?_, rfl⟩
    rw [P8Census.skeletonComparisonCensus, List.mem_flatMap]
    exact ⟨P8Census.boundSkeletonRowAt T z hz i, hsMem, hc⟩
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hpairMem
  let jc : Fin C.census.count := ⟨j, by
    simpa [P8Census.BoundP8Census.census] using j.isLt⟩
  have hjc : C.census.pair jc = c.pair := by
    simpa [P8Census.BoundP8Census.census, jc] using hj
  have hsep := P8Census.sepSeed_of_not_mem_badSeeds C.census z hgood jc
  have hq := hb _ hsMem c hc
  exact
    { separates := by
        rw [hjc] at hsep
        exact hsep
      left_bounded := hq.1
      right_bounded := hq.2 }

/-- Skeleton/config/execution form of `fixedComparison_faithful`.  Its only post-seed premise is
the bare binding relation. -/
theorem skeletonComparison_faithful
    (S : SemanticStrategy.SemanticSkeleton)
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) {z : K}
    (binds : SemanticStrategy.BindsAt z S cfg exec)
    (C : SkeletonP8Census K S Λ)
    (hb : SkeletonComparisonBoundedBy K q S)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (i : Fin cfg.compRows)
    (c : SemanticTrace.ComparisonUse)
    (hc : c ∈ P8Census.skeletonComparisons (K := K)
      (skeletonRowAt S exec binds i)) :
    OpcodeSemantics.PairFaithful z q c.left c.right := by
  have hsMem :
      skeletonRowAt S exec binds i ∈ SemanticStrategy.computeSkeletonRows S :=
    List.get_mem _ _
  have hpairMem : c.pair ∈ skeletonPairs K S := by
    rw [skeletonPairs, List.mem_append]
    apply Or.inr
    apply List.mem_map.mpr
    refine ⟨c, ?_, rfl⟩
    rw [P8Census.skeletonComparisonCensus, List.mem_flatMap]
    exact ⟨skeletonRowAt S exec binds i, hsMem, hc⟩
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hpairMem
  let jc : Fin C.census.count := ⟨j, by
    simpa [SkeletonP8Census.census] using j.isLt⟩
  have hjc : C.census.pair jc = c.pair := by
    simpa [SkeletonP8Census.census, jc] using hj
  have hsep := P8Census.sepSeed_of_not_mem_badSeeds C.census z hgood jc
  have hq := hb _ hsMem c hc
  exact
    { separates := by
        rw [hjc] at hsep
        exact hsep
      left_bounded := hq.1
      right_bounded := hq.2 }

end Finite

/-- The served-lookup tuples reconstructed from the skeleton and public row.
The body matches on `s.state`; the type does not mention it, so `cases s.state`
inside `buildCoveredRow` stays well-typed. -/
def servedTuplesOf (s : RowSkeleton) (pub : ComputeTable.Pub K) :
    List (ComputeTable.MemRec K × Noun × ℕ × Noun) :=
  if s.state = .s9 then
    [(computeMemRec pub 2,
      P8Census.skeletonSubformula s 0 .result,
      P8Census.skeletonMemoryAxis s 2,
      P8Census.skeletonSubformula s 1 .formula)]
  else if s.state = .s0 then
    [(computeMemRec pub 1, s.subject,
      P8Census.skeletonMemoryAxis s 1, s.evaluation)]
  else
    []

/-- Canonical row construction for all eleven states.  Every noun below is a
projection of `s`. -/
def buildCoveredRow
    {q Λ : ℕ} {z : K} {s : RowSkeleton}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        c.LeavesBounded Λ) :
    { data : SemanticTrace.ComputeRowSemanticData q Λ row //
      data.comparisons = P8Census.skeletonComparisons (K := K) s ∧
        data.needs.served.map (fun l => (l.record, l.root, l.axis, l.child)) =
          servedTuplesOf s row.2.2.1 } := by
  rcases row with ⟨rowState, inp, pub, dec⟩
  rcases hbind with
    ⟨hrowState, hseed, hpubState, hsubject, hformula, hevaluation,
      hdec, hsf, hmr⟩
  change rowState = s.state at hrowState
  subst rowState
  have realize {n : Noun} {fp : ComputeTable.FP K}
      (h : SemanticStrategy.bindFP z n fp) :
      OpcodeSemantics.Realizes inp.z fp n := by
    rw [hseed]
    exact h
  have decRealize (slot : SemanticStrategy.DecSlot)
      (ha : SemanticStrategy.decActive s.state slot = true) :
      OpcodeSemantics.Realizes inp.z (SemanticStrategy.decFP dec slot)
        (s.decomposition slot ha) := by
    have h := hdec slot
    simp only [dif_pos ha] at h
    exact realize h
  have sfRealize (i : Fin 3)
      (hi : (i : ℕ) < ComputeTable.fanoutComp s.state)
      (slot : SemanticStrategy.TripleSlot) :
      OpcodeSemantics.Realizes inp.z
        (SemanticStrategy.tripleFP (computeSubformulaFPs pub i) slot)
        (s.subformula i hi slot) := by
    have h := hsf i
    simp only [dif_pos hi] at h
    exact realize (h slot)
  let root : OpcodeSemantics.RootRealization inp pub dec :=
    { subject := s.subject
      formula := s.formula
      result := s.evaluation
      head := s.decomposition .f_h (by
        cases hs : s.state <;> simp [SemanticStrategy.decActive])
      tail := s.decomposition .f_t (by
        cases hs : s.state <;> simp [SemanticStrategy.decActive])
      subject_realizes := realize hsubject
      formula_realizes := realize hformula
      result_realizes := realize hevaluation
      head_realizes := decRealize .f_h (by
        cases hs : s.state <;> simp [SemanticStrategy.decActive])
      tail_realizes := decRealize .f_t (by
        cases hs : s.state <;> simp [SemanticStrategy.decActive]) }
  have mkTail
      (hs : SemanticStrategy.hasTailDecomposition s.state = true) :
      OpcodeSemantics.TailRealization inp.z dec :=
    { head := s.decomposition .f_th (by
        simpa [SemanticStrategy.decActive] using hs)
      tail := s.decomposition .f_tt (by
        simpa [SemanticStrategy.decActive] using hs)
      head_realizes := decRealize .f_th (by
        simpa [SemanticStrategy.decActive] using hs)
      tail_realizes := decRealize .f_tt (by
        simpa [SemanticStrategy.decActive] using hs) }
  have mkBranch (hs : s.state = .s6) :
      OpcodeSemantics.BranchTailRealization inp.z dec :=
    { head := s.decomposition .f_tth (by
        simp [SemanticStrategy.decActive, hs])
      tail := s.decomposition .f_ttt (by
        simp [SemanticStrategy.decActive, hs])
      head_realizes := decRealize .f_tth (by
        simp [SemanticStrategy.decActive, hs])
      tail_realizes := decRealize .f_ttt (by
        simp [SemanticStrategy.decActive, hs]) }
  have mkCall (i : Fin 3)
      (hi : (i : ℕ) < ComputeTable.fanoutComp s.state) :
      SemanticTrace.RealizedCall inp.z :=
    { subjectFP := (computeSubformulaFPs pub i).1
      formulaFP := (computeSubformulaFPs pub i).2.1
      resultFP := (computeSubformulaFPs pub i).2.2
      realization :=
        { subject := s.subformula i hi .subject
          formula := s.subformula i hi .formula
          result := s.subformula i hi .result
          subject_realizes := sfRealize i hi .subject
          formula_realizes := sfRealize i hi .formula
          result_realizes := sfRealize i hi .result } }
  have rootBounds :
      ∀ n ∈ [root.subject, root.formula, root.result],
        FieldEmbedding.BoundedBy q n := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact hb.1
    · exact hb.2.1
    · exact hb.2.2.1
  have commonRoles :
      (P8Census.skeletonComparisons (K := K) s).map
          SemanticTrace.ComparisonUse.role =
        SemanticTrace.requiredComparisonRoles s.state :=
    P8Census.skeletonComparisons_roles K s
  cases hs : s.state with
  | s0 =>
      have hiMR : (1 : ℕ) < Nock.Framework.recordCount s.state := by
        simp [hs, Nock.Framework.recordCount]
      have hmr1 := hmr (1 : Fin 3)
      simp [hs, Nock.Framework.recordCount] at hmr1
      have hrecord := hop.s0_record hs
      dsimp only at hrecord
      let served : SemanticTrace.ServedNounLookup inp.z :=
        { record := computeMemRec pub 1
          root := s.subject
          axis := P8Census.skeletonMemoryAxis s 1
          child := s.evaluation
          realization := by
            have haxis := hmr1.2.2
            have hroot := hmr1.1
            have hchild := hmr1.2.1
            rw [hrecord.1] at hroot
            rw [hrecord.2] at hchild
            exact
              { root_realizes := realize hroot
                child_realizes := realize hchild
                axis_realizes := by
                  simpa [P8Census.skeletonMemoryAxis, hs,
                    Nock.Framework.recordCount] using haxis }
          served := by
            exact hop.s0_served hs }
      exact
        ⟨({
          root := root
          tails := []
          branchTails := []
          calls := []
          windows := []
          axisGates := []
          tails_count := by simp [SemanticTrace.requiredTailRealizations, hs]
          branchTails_count := by
            simp [SemanticTrace.requiredBranchTailRealizations, hs]
          calls_count := by simp [SemanticTrace.requiredCallRealizations, hs]
          windows_count := by simp [SemanticTrace.requiredSizeWindows, hs]
          axisGates_count := by simp [SemanticTrace.requiredAxisAtomGates, hs]
          realizedNouns := [root.subject, root.formula, root.result]
          subject_mem := by simp
          formula_mem := by simp
          result_mem := by simp
          bounded := rootBounds
          comparisons := P8Census.skeletonComparisons (K := K) s
          comparison_faithful := by
            intro c hc
            rw [hseed]
            exact hfaith c hc
          comparison_leaves := hleaves
          comparison_roles := by simpa [hs] using commonRoles
          axisGate_listed := by simp
          axisGate_tail_mem := by simp
          needs :=
            { served := [served]
              served_count := by simp [SemanticTrace.requiredServedLookups, hs] } }),
          ⟨rfl, by simp [servedTuplesOf, hs, served]⟩⟩
  | s1 =>
      exact
        ⟨({
          root := root
          tails := []
          branchTails := []
          calls := []
          windows := []
          axisGates := []
          tails_count := by simp [SemanticTrace.requiredTailRealizations, hs]
          branchTails_count := by simp [SemanticTrace.requiredBranchTailRealizations, hs]
          calls_count := by simp [SemanticTrace.requiredCallRealizations, hs]
          windows_count := by simp [SemanticTrace.requiredSizeWindows, hs]
          axisGates_count := by simp [SemanticTrace.requiredAxisAtomGates, hs]
          realizedNouns := [root.subject, root.formula, root.result]
          subject_mem := by simp
          formula_mem := by simp
          result_mem := by simp
          bounded := rootBounds
          comparisons := P8Census.skeletonComparisons (K := K) s
          comparison_faithful := by
            intro c hc
            rw [hseed]
            exact hfaith c hc
          comparison_leaves := hleaves
          comparison_roles := by simpa [hs] using commonRoles
          axisGate_listed := by simp
          axisGate_tail_mem := by simp
          needs :=
            { served := []
              served_count := by simp [SemanticTrace.requiredServedLookups, hs] } }),
          ⟨rfl, by simp [servedTuplesOf, hs]⟩⟩
  | s2 =>
      exact
        ⟨({
          root := root
          tails := [mkTail (by simp [SemanticStrategy.hasTailDecomposition, hs])]
          branchTails := []
          calls := [mkCall 0 (by simp [hs, ComputeTable.fanoutComp]),
            mkCall 1 (by simp [hs, ComputeTable.fanoutComp]),
            mkCall 2 (by simp [hs, ComputeTable.fanoutComp])]
          windows := []
          axisGates := []
          tails_count := by simp [SemanticTrace.requiredTailRealizations, hs]
          branchTails_count := by simp [SemanticTrace.requiredBranchTailRealizations, hs]
          calls_count := by simp [SemanticTrace.requiredCallRealizations, hs]
          windows_count := by simp [SemanticTrace.requiredSizeWindows, hs]
          axisGates_count := by simp [SemanticTrace.requiredAxisAtomGates, hs]
          realizedNouns := [root.subject, root.formula, root.result]
          subject_mem := by simp
          formula_mem := by simp
          result_mem := by simp
          bounded := rootBounds
          comparisons := P8Census.skeletonComparisons (K := K) s
          comparison_faithful := by
            intro c hc
            rw [hseed]
            exact hfaith c hc
          comparison_leaves := hleaves
          comparison_roles := by simpa [hs] using commonRoles
          axisGate_listed := by simp
          axisGate_tail_mem := by simp
          needs :=
            { served := []
              served_count := by simp [SemanticTrace.requiredServedLookups, hs] } }),
          ⟨rfl, by simp [servedTuplesOf, hs]⟩⟩
  | s3 =>
      exact
        ⟨({
          root := root
          tails := []
          branchTails := []
          calls := [mkCall 0 (by simp [hs, ComputeTable.fanoutComp])]
          windows := [
            { noun := P8Census.skeletonSubformula s 0 .result
              window := by rw [hseed]; exact hop.s3_window hs }]
          axisGates := []
          tails_count := by simp [SemanticTrace.requiredTailRealizations, hs]
          branchTails_count := by simp [SemanticTrace.requiredBranchTailRealizations, hs]
          calls_count := by simp [SemanticTrace.requiredCallRealizations, hs]
          windows_count := by simp [SemanticTrace.requiredSizeWindows, hs]
          axisGates_count := by simp [SemanticTrace.requiredAxisAtomGates, hs]
          realizedNouns := [root.subject, root.formula, root.result]
          subject_mem := by simp
          formula_mem := by simp
          result_mem := by simp
          bounded := rootBounds
          comparisons := P8Census.skeletonComparisons (K := K) s
          comparison_faithful := by
            intro c hc
            rw [hseed]
            exact hfaith c hc
          comparison_leaves := hleaves
          comparison_roles := by simpa [hs] using commonRoles
          axisGate_listed := by simp
          axisGate_tail_mem := by simp
          needs :=
            { served := []
              served_count := by simp [SemanticTrace.requiredServedLookups, hs] } }),
          ⟨rfl, by simp [servedTuplesOf, hs]⟩⟩
  | s4 =>
      exact
        ⟨({
          root := root
          tails := []
          branchTails := []
          calls := [mkCall 0 (by simp [hs, ComputeTable.fanoutComp])]
          windows := [
            { noun := P8Census.skeletonSubformula s 0 .result
              window := by rw [hseed]; exact hop.s4_window hs }]
          axisGates := []
          tails_count := by simp [SemanticTrace.requiredTailRealizations, hs]
          branchTails_count := by simp [SemanticTrace.requiredBranchTailRealizations, hs]
          calls_count := by simp [SemanticTrace.requiredCallRealizations, hs]
          windows_count := by simp [SemanticTrace.requiredSizeWindows, hs]
          axisGates_count := by simp [SemanticTrace.requiredAxisAtomGates, hs]
          realizedNouns := [root.subject, root.formula, root.result]
          subject_mem := by simp
          formula_mem := by simp
          result_mem := by simp
          bounded := rootBounds
          comparisons := P8Census.skeletonComparisons (K := K) s
          comparison_faithful := by
            intro c hc
            rw [hseed]
            exact hfaith c hc
          comparison_leaves := hleaves
          comparison_roles := by simpa [hs] using commonRoles
          axisGate_listed := by simp
          axisGate_tail_mem := by simp
          needs :=
            { served := []
              served_count := by simp [SemanticTrace.requiredServedLookups, hs] } }),
          ⟨rfl, by simp [servedTuplesOf, hs]⟩⟩
  | s5 =>
      exact
        ⟨({
          root := root
          tails := [mkTail (by simp [SemanticStrategy.hasTailDecomposition, hs])]
          branchTails := []
          calls := [mkCall 0 (by simp [hs, ComputeTable.fanoutComp]),
            mkCall 1 (by simp [hs, ComputeTable.fanoutComp])]
          windows := []
          axisGates := []
          tails_count := by simp [SemanticTrace.requiredTailRealizations, hs]
          branchTails_count := by simp [SemanticTrace.requiredBranchTailRealizations, hs]
          calls_count := by simp [SemanticTrace.requiredCallRealizations, hs]
          windows_count := by simp [SemanticTrace.requiredSizeWindows, hs]
          axisGates_count := by simp [SemanticTrace.requiredAxisAtomGates, hs]
          realizedNouns := [root.subject, root.formula, root.result]
          subject_mem := by simp
          formula_mem := by simp
          result_mem := by simp
          bounded := rootBounds
          comparisons := P8Census.skeletonComparisons (K := K) s
          comparison_faithful := by
            intro c hc
            rw [hseed]
            exact hfaith c hc
          comparison_leaves := hleaves
          comparison_roles := by simpa [hs] using commonRoles
          axisGate_listed := by simp
          axisGate_tail_mem := by simp
          needs :=
            { served := []
              served_count := by simp [SemanticTrace.requiredServedLookups, hs] } }),
          ⟨rfl, by simp [servedTuplesOf, hs]⟩⟩
  | s6 =>
      exact
        ⟨({
          root := root
          tails := [mkTail (by simp [SemanticStrategy.hasTailDecomposition, hs])]
          branchTails := [mkBranch hs]
          calls := [mkCall 0 (by simp [hs, ComputeTable.fanoutComp]),
            mkCall 1 (by simp [hs, ComputeTable.fanoutComp])]
          windows := [
            { noun := P8Census.skeletonSubformula s 1 .result
              window := by rw [hseed]; exact hop.s6_window hs }]
          axisGates := []
          tails_count := by simp [SemanticTrace.requiredTailRealizations, hs]
          branchTails_count := by simp [SemanticTrace.requiredBranchTailRealizations, hs]
          calls_count := by simp [SemanticTrace.requiredCallRealizations, hs]
          windows_count := by simp [SemanticTrace.requiredSizeWindows, hs]
          axisGates_count := by simp [SemanticTrace.requiredAxisAtomGates, hs]
          realizedNouns := [root.subject, root.formula, root.result]
          subject_mem := by simp
          formula_mem := by simp
          result_mem := by simp
          bounded := rootBounds
          comparisons := P8Census.skeletonComparisons (K := K) s
          comparison_faithful := by
            intro c hc
            rw [hseed]
            exact hfaith c hc
          comparison_leaves := hleaves
          comparison_roles := by simpa [hs] using commonRoles
          axisGate_listed := by simp
          axisGate_tail_mem := by simp
          needs :=
            { served := []
              served_count := by simp [SemanticTrace.requiredServedLookups, hs] } }),
          ⟨rfl, by simp [servedTuplesOf, hs]⟩⟩
  | s7 =>
      exact
        ⟨({
          root := root
          tails := [mkTail (by simp [SemanticStrategy.hasTailDecomposition, hs])]
          branchTails := []
          calls := [mkCall 0 (by simp [hs, ComputeTable.fanoutComp]),
            mkCall 1 (by simp [hs, ComputeTable.fanoutComp])]
          windows := []
          axisGates := []
          tails_count := by simp [SemanticTrace.requiredTailRealizations, hs]
          branchTails_count := by simp [SemanticTrace.requiredBranchTailRealizations, hs]
          calls_count := by simp [SemanticTrace.requiredCallRealizations, hs]
          windows_count := by simp [SemanticTrace.requiredSizeWindows, hs]
          axisGates_count := by simp [SemanticTrace.requiredAxisAtomGates, hs]
          realizedNouns := [root.subject, root.formula, root.result]
          subject_mem := by simp
          formula_mem := by simp
          result_mem := by simp
          bounded := rootBounds
          comparisons := P8Census.skeletonComparisons (K := K) s
          comparison_faithful := by
            intro c hc
            rw [hseed]
            exact hfaith c hc
          comparison_leaves := hleaves
          comparison_roles := by simpa [hs] using commonRoles
          axisGate_listed := by simp
          axisGate_tail_mem := by simp
          needs :=
            { served := []
              served_count := by simp [SemanticTrace.requiredServedLookups, hs] } }),
          ⟨rfl, by simp [servedTuplesOf, hs]⟩⟩
  | s8 =>
      exact
        ⟨({
          root := root
          tails := [mkTail (by simp [SemanticStrategy.hasTailDecomposition, hs])]
          branchTails := []
          calls := [mkCall 0 (by simp [hs, ComputeTable.fanoutComp]),
            mkCall 1 (by simp [hs, ComputeTable.fanoutComp])]
          windows := []
          axisGates := []
          tails_count := by simp [SemanticTrace.requiredTailRealizations, hs]
          branchTails_count := by simp [SemanticTrace.requiredBranchTailRealizations, hs]
          calls_count := by simp [SemanticTrace.requiredCallRealizations, hs]
          windows_count := by simp [SemanticTrace.requiredSizeWindows, hs]
          axisGates_count := by simp [SemanticTrace.requiredAxisAtomGates, hs]
          realizedNouns := [root.subject, root.formula, root.result]
          subject_mem := by simp
          formula_mem := by simp
          result_mem := by simp
          bounded := rootBounds
          comparisons := P8Census.skeletonComparisons (K := K) s
          comparison_faithful := by
            intro c hc
            rw [hseed]
            exact hfaith c hc
          comparison_leaves := hleaves
          comparison_roles := by simpa [hs] using commonRoles
          axisGate_listed := by simp
          axisGate_tail_mem := by simp
          needs :=
            { served := []
              served_count := by simp [SemanticTrace.requiredServedLookups, hs] } }),
          ⟨rfl, by simp [servedTuplesOf, hs]⟩⟩
  | s9 =>
      have hthActive :
          SemanticStrategy.decActive s.state .f_th = true := by
        simp [SemanticStrategy.decActive,
          SemanticStrategy.hasTailDecomposition, hs]
      have httActive :
          SemanticStrategy.decActive s.state .f_tt = true := by
        simp [SemanticStrategy.decActive,
          SemanticStrategy.hasTailDecomposition, hs]
      let tail : OpcodeSemantics.TailRealization inp.z dec :=
        { head := s.decomposition .f_th hthActive
          tail := s.decomposition .f_tt httActive
          head_realizes := decRealize .f_th hthActive
          tail_realizes := decRealize .f_tt httActive }
      have htailHead :
          tail.head = P8Census.skeletonDec s .f_th := by
        dsimp only [tail]
        simp [P8Census.skeletonDec, hs, SemanticStrategy.decActive,
          SemanticStrategy.hasTailDecomposition]
      let axisUse : SemanticTrace.ComparisonUse :=
        P8Census.skeletonUse .axisAtom
          (P8Census.skeletonDec s .f_th)
          (.atom (P8Census.skeletonMemoryAxis s 2))
      have haxisMem :
          axisUse ∈ P8Census.skeletonComparisons (K := K) s := by
        simp [axisUse, P8Census.skeletonComparisons, hs,
          P8Census.skeletonUse]
      let axisGate :
          Σ tail : OpcodeSemantics.TailRealization inp.z dec,
            SemanticTrace.AxisAtomComparisonCertificate inp.z q dec tail :=
        ⟨tail,
          { axis := P8Census.skeletonMemoryAxis s 2
            faithful := by
              rw [htailHead]
              have hf := hfaith axisUse haxisMem
              simpa [axisUse, P8Census.skeletonUse] using
                (hseed.symm ▸ hf) }⟩
      have hiMR : (2 : ℕ) < Nock.Framework.recordCount s.state := by
        simp [hs, Nock.Framework.recordCount]
      have hmr3 := hmr (2 : Fin 3)
      simp [hs, Nock.Framework.recordCount] at hmr3
      have hrecord := hop.s9_record hs
      dsimp only at hrecord
      let served : SemanticTrace.ServedNounLookup inp.z :=
        { record := computeMemRec pub 2
          root := P8Census.skeletonSubformula s 0 .result
          axis := P8Census.skeletonMemoryAxis s 2
          child := P8Census.skeletonSubformula s 1 .formula
          realization := by
            have haxis := hmr3.2.2
            have hroot := hmr3.1
            have hchild := hmr3.2.1
            rw [hrecord.1] at hroot
            rw [hrecord.2] at hchild
            exact
              { root_realizes := realize hroot
                child_realizes := realize hchild
                axis_realizes := by
                  simpa [P8Census.skeletonMemoryAxis, hs,
                    Nock.Framework.recordCount] using haxis }
          served := hop.s9_served hs }
      exact
        ⟨({
          root := root
          tails := [tail]
          branchTails := []
          calls := [mkCall 0 (by simp [hs, ComputeTable.fanoutComp]),
            mkCall 1 (by simp [hs, ComputeTable.fanoutComp])]
          windows := []
          axisGates := [axisGate]
          tails_count := by simp [SemanticTrace.requiredTailRealizations, hs]
          branchTails_count := by
            simp [SemanticTrace.requiredBranchTailRealizations, hs]
          calls_count := by simp [SemanticTrace.requiredCallRealizations, hs]
          windows_count := by simp [SemanticTrace.requiredSizeWindows, hs]
          axisGates_count := by simp [SemanticTrace.requiredAxisAtomGates, hs]
          realizedNouns := [root.subject, root.formula, root.result]
          subject_mem := by simp
          formula_mem := by simp
          result_mem := by simp
          bounded := rootBounds
          comparisons := P8Census.skeletonComparisons (K := K) s
          comparison_faithful := by
            intro c hc
            rw [hseed]
            exact hfaith c hc
          comparison_leaves := hleaves
          comparison_roles := by simpa [hs] using commonRoles
          axisGate_listed := by
            intro gate hgate
            simp only [List.mem_singleton] at hgate
            subst gate
            simpa [axisGate, htailHead, axisUse, P8Census.skeletonUse] using
              haxisMem
          axisGate_tail_mem := by
            intro gate hgate
            simp only [List.mem_singleton] at hgate
            subst gate
            simp [axisGate]
          needs :=
            { served := [served]
              served_count := by simp [SemanticTrace.requiredServedLookups, hs] } }),
          ⟨rfl, by simp [servedTuplesOf, hs, served]⟩⟩
  | cons =>
      exact
        ⟨({
          root := root
          tails := []
          branchTails := []
          calls := [mkCall 0 (by simp [hs, ComputeTable.fanoutComp]),
            mkCall 1 (by simp [hs, ComputeTable.fanoutComp])]
          windows := []
          axisGates := []
          tails_count := by simp [SemanticTrace.requiredTailRealizations, hs]
          branchTails_count := by simp [SemanticTrace.requiredBranchTailRealizations, hs]
          calls_count := by simp [SemanticTrace.requiredCallRealizations, hs]
          windows_count := by simp [SemanticTrace.requiredSizeWindows, hs]
          axisGates_count := by simp [SemanticTrace.requiredAxisAtomGates, hs]
          realizedNouns := [root.subject, root.formula, root.result]
          subject_mem := by simp
          formula_mem := by simp
          result_mem := by simp
          bounded := rootBounds
          comparisons := P8Census.skeletonComparisons (K := K) s
          comparison_faithful := by
            intro c hc
            rw [hseed]
            exact hfaith c hc
          comparison_leaves := hleaves
          comparison_roles := by simpa [hs] using commonRoles
          axisGate_listed := by simp
          axisGate_tail_mem := by simp
          needs :=
            { served := []
              served_count := by simp [SemanticTrace.requiredServedLookups, hs] } }),
          ⟨rfl, by simp [servedTuplesOf, hs]⟩⟩

@[simp]
theorem buildCoveredRow_comparisons
    {q Λ : ℕ} {z : K} {s : RowSkeleton}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        c.LeavesBounded Λ) :
    (buildCoveredRow hb hop hbind hfaith hleaves).1.comparisons =
      P8Census.skeletonComparisons (K := K) s := by
  exact (buildCoveredRow hb hop hbind hfaith hleaves).2.1

theorem buildCoveredRow_servedTuples
    {q Λ : ℕ} {z : K} {s : RowSkeleton}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        c.LeavesBounded Λ) :
    ((buildCoveredRow hb hop hbind hfaith hleaves).1.needs.served).map
        (fun l => (l.record, l.root, l.axis, l.child)) =
      servedTuplesOf s row.2.2.1 :=
  (buildCoveredRow hb hop hbind hfaith hleaves).2.2

end

end Nock.NockVMROM.Thm54.BoundSemanticTrace

namespace Nock.NockVMROM.Thm54

open scoped Classical
open Nock Nock.Walk

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {p : ℕ} [CharP K p]
variable [Fintype K] [DecidableEq K]

namespace BoundSemanticTrace

theorem fixedComparison_leaves
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (C : P8Census.BoundP8Census T Λ)
    (z : K) (hz : z ≠ 0)
    (i : Fin (P8Census.boundSampledCfg T z hz).compRows)
    (c : SemanticTrace.ComparisonUse)
    (hc : c ∈ P8Census.skeletonComparisons (K := K)
      (P8Census.boundSkeletonRowAt T z hz i)) :
    c.LeavesBounded Λ := by
  apply C.leaves_bounded c.pair
  rw [P8Census.boundPairs, List.mem_append]
  apply Or.inr
  apply List.mem_map.mpr
  refine ⟨c, ?_, rfl⟩
  rw [P8Census.skeletonComparisonCensus, List.mem_flatMap]
  exact ⟨P8Census.boundSkeletonRowAt T z hz i, List.get_mem _ _, hc⟩

theorem skeletonComparison_leaves
    (S : SemanticStrategy.SemanticSkeleton)
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) {z : K}
    (binds : SemanticStrategy.BindsAt z S cfg exec)
    (C : SkeletonP8Census K S Λ)
    (i : Fin cfg.compRows)
    (c : SemanticTrace.ComparisonUse)
    (hc : c ∈ P8Census.skeletonComparisons (K := K)
      (skeletonRowAt S exec binds i)) :
    c.LeavesBounded Λ := by
  apply C.leaves_bounded c.pair
  rw [skeletonPairs, List.mem_append]
  apply Or.inr
  apply List.mem_map.mpr
  refine ⟨c, ?_, rfl⟩
  rw [P8Census.skeletonComparisonCensus, List.mem_flatMap]
  exact ⟨skeletonRowAt S exec binds i, List.get_mem _ _, hc⟩

end BoundSemanticTrace

namespace SemanticTrace.ComputeRowSemanticData

/-- Canonical semantic row data from an explicit skeleton/config/execution/binding context. -/
def ofSkeleton
    (S : SemanticStrategy.SemanticSkeleton)
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) {z : K}
    (binds : SemanticStrategy.BindsAt z S cfg exec)
    (C : BoundSemanticTrace.SkeletonP8Census K S Λ)
    (hb : S.BoundedBy q)
    (hcmp : BoundSemanticTrace.SkeletonComparisonBoundedBy K q S)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (hop :
      ∀ s ∈ SemanticStrategy.computeSkeletonRows S,
        BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (i : Fin cfg.compRows) :
    SemanticTrace.ComputeRowSemanticData q Λ (exec.computeRowAt i) := by
  let s := BoundSemanticTrace.skeletonRowAt S exec binds i
  have hsMem : s ∈ SemanticStrategy.computeSkeletonRows S :=
    List.get_mem _ _
  exact (BoundSemanticTrace.buildCoveredRow
    ((List.forall_iff_forall_mem.mp hb.computeRows) s hsMem)
    (hop s hsMem)
    (BoundSemanticTrace.skeletonRowAt_binds S exec binds i)
    (fun c hc =>
      BoundSemanticTrace.skeletonComparison_faithful
        S exec binds C hcmp hgood i c hc)
    (fun c hc =>
      BoundSemanticTrace.skeletonComparison_leaves
        S exec binds C i c hc)).1

@[simp] theorem ofSkeleton_comparisons
    (S : SemanticStrategy.SemanticSkeleton)
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) {z : K}
    (binds : SemanticStrategy.BindsAt z S cfg exec)
    (C : BoundSemanticTrace.SkeletonP8Census K S Λ)
    (hb : S.BoundedBy q)
    (hcmp : BoundSemanticTrace.SkeletonComparisonBoundedBy K q S)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (hop :
      ∀ s ∈ SemanticStrategy.computeSkeletonRows S,
        BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (i : Fin cfg.compRows) :
    (ofSkeleton S exec binds C hb hcmp hgood hop i).comparisons =
      P8Census.skeletonComparisons (K := K)
        (BoundSemanticTrace.skeletonRowAt S exec binds i) := by
  unfold ofSkeleton
  exact BoundSemanticTrace.buildCoveredRow_comparisons _ _ _ _ _

/-- **The served-lookup tuples of a canonical row are the skeleton's own.**

The twin of `ofSkeleton_comparisons`, and the projection `semanticCoverage` consumes: it turns an
obligation about `needs.served` — an existentially-built list inside `buildCoveredRow` — into one
about `servedTuplesOf`, which is a three-way `if` on `s.state` and is therefore `[]` at nine of the
eleven states.  The `Service` supply then has to be exhibited only at `.s0` and `.s9`. -/
@[simp] theorem ofSkeleton_servedTuples
    (S : SemanticStrategy.SemanticSkeleton)
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) {z : K}
    (binds : SemanticStrategy.BindsAt z S cfg exec)
    (C : BoundSemanticTrace.SkeletonP8Census K S Λ)
    (hb : S.BoundedBy q)
    (hcmp : BoundSemanticTrace.SkeletonComparisonBoundedBy K q S)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (hop :
      ∀ s ∈ SemanticStrategy.computeSkeletonRows S,
        BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (i : Fin cfg.compRows) :
    ((ofSkeleton S exec binds C hb hcmp hgood hop i).needs.served).map
        (fun l => (l.record, l.root, l.axis, l.child)) =
      BoundSemanticTrace.servedTuplesOf
        (BoundSemanticTrace.skeletonRowAt S exec binds i)
        ((exec.computeRowAt i).2.2.1) := by
  unfold ofSkeleton
  exact BoundSemanticTrace.buildCoveredRow_servedTuples _ _ _ _ _

/-- Canonical exact-row adapter.  The row binding is obtained from
`BindsAt.derived_computeRows`; no public or private fingerprint realization
witness is opened. -/
def ofBoundSkeleton
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (C : P8Census.BoundP8Census T Λ)
    (hb : T.skeleton.BoundedBy q)
    (hcmp : BoundSemanticTrace.FixedComparisonBoundedBy q T)
    (z : K) (hz : z ≠ 0)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (hop :
      ∀ s ∈ SemanticStrategy.computeSkeletonRows T.skeleton,
        BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (i : Fin (P8Census.boundSampledCfg T z hz).compRows) :
    SemanticTrace.ComputeRowSemanticData q Λ
      ((P8Census.boundSampledExec T z hz).computeRowAt i) := by
  let s := P8Census.boundSkeletonRowAt T z hz i
  have hsMem :
      s ∈ SemanticStrategy.computeSkeletonRows T.skeleton :=
    List.get_mem _ _
  exact (BoundSemanticTrace.buildCoveredRow
    ((List.forall_iff_forall_mem.mp hb.computeRows) s hsMem)
    (hop s hsMem)
    (BoundSemanticTrace.boundSkeletonRowAt_binds T z hz i)
    (fun c hc =>
      BoundSemanticTrace.fixedComparison_faithful
        T C hcmp z hz hgood i c hc)
    (fun c hc =>
      BoundSemanticTrace.fixedComparison_leaves T C z hz i c hc)).1

@[simp]
theorem ofBoundSkeleton_comparisons
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (C : P8Census.BoundP8Census T Λ)
    (hb : T.skeleton.BoundedBy q)
    (hcmp : BoundSemanticTrace.FixedComparisonBoundedBy q T)
    (z : K) (hz : z ≠ 0)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (hop :
      ∀ s ∈ SemanticStrategy.computeSkeletonRows T.skeleton,
        BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (i : Fin (P8Census.boundSampledCfg T z hz).compRows) :
    (ofBoundSkeleton T C hb hcmp z hz hgood hop i).comparisons =
      P8Census.skeletonComparisons (K := K)
        (P8Census.boundSkeletonRowAt T z hz i) := by
  unfold ofBoundSkeleton
  exact BoundSemanticTrace.buildCoveredRow_comparisons _ _ _ _ _

end SemanticTrace.ComputeRowSemanticData

namespace SemanticTrace.ExactExecutionSemanticData

/-- Aggregate construction on all canonical BFS rows.  Traversal language and
accepted-row facts remain separate field-level inputs. -/
def ofBoundSkeleton
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (C : P8Census.BoundP8Census T Λ)
    (hb : T.skeleton.BoundedBy q)
    (hcmp : BoundSemanticTrace.FixedComparisonBoundedBy q T)
    (z : K) (hz : z ≠ 0)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (hop :
      ∀ s ∈ SemanticStrategy.computeSkeletonRows T.skeleton,
        BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (language :
      NounRealizedTraversableChainedSemanticExactLanguage q
        (P8Census.boundSampledCfg T z hz)
        (P8Census.boundSampledExec T z hz))
    (rowAccepted :
      ∀ i : Fin (P8Census.boundSampledCfg T z hz).compRows,
        ExactExecution.ComputeRowAccepted
          (P8Census.boundSampledCfg T z hz)
          ((P8Census.boundSampledExec T z hz).computeRowAt i)) :
    SemanticTrace.ExactExecutionSemanticData q Λ
      (P8Census.boundSampledCfg T z hz)
      (P8Census.boundSampledExec T z hz) where
  language := language
  rowAccepted := rowAccepted
  rows i :=
    SemanticTrace.ComputeRowSemanticData.ofBoundSkeleton
      T C hb hcmp z hz hgood hop i

end SemanticTrace.ExactExecutionSemanticData

namespace P8Census

/-- Compatibility is immediate because every covered row stores the fixed
`skeletonComparisons` list itself. -/
theorem skeletonComparisonCompatibility_ofBoundSkeleton
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (C : BoundP8Census T Λ)
    (hb : T.skeleton.BoundedBy q)
    (hcmp : BoundSemanticTrace.FixedComparisonBoundedBy q T)
    (z : K) (hz : z ≠ 0)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (hop :
      ∀ s ∈ SemanticStrategy.computeSkeletonRows T.skeleton,
        BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (language :
      NounRealizedTraversableChainedSemanticExactLanguage q
        (boundSampledCfg T z hz) (boundSampledExec T z hz))
    (rowAccepted :
      ∀ i : Fin (boundSampledCfg T z hz).compRows,
        ExactExecution.ComputeRowAccepted (boundSampledCfg T z hz)
          ((boundSampledExec T z hz).computeRowAt i)) :
    SkeletonComparisonCompatibility T z hz
      (SemanticTrace.ExactExecutionSemanticData.ofBoundSkeleton
        T C hb hcmp z hz hgood hop language rowAccepted) := by
  refine ⟨?_⟩
  intro row role left right hlisted
  refine ⟨{ role := role, left := left, right := right }, ?_, rfl, rfl⟩
  change { role := role, left := left, right := right } ∈
    (SemanticTrace.ComputeRowSemanticData.ofBoundSkeleton
      T C hb hcmp z hz hgood hop row).comparisons at hlisted
  rw [SemanticTrace.ComputeRowSemanticData.ofBoundSkeleton_comparisons] at hlisted
  exact hlisted

end P8Census

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.BoundSemanticTrace.buildCoveredRow_comparisons
#print axioms Nock.NockVMROM.Thm54.BoundSemanticTrace.buildCoveredRow_servedTuples
#print axioms Nock.NockVMROM.Thm54.SemanticTrace.ComputeRowSemanticData.ofSkeleton_servedTuples
#print axioms Nock.NockVMROM.Thm54.BoundSemanticTrace.boundSkeletonRowAt_binds
#print axioms Nock.NockVMROM.Thm54.BoundSemanticTrace.fixedComparison_faithful
#print axioms Nock.NockVMROM.Thm54.BoundSemanticTrace.skeletonRowAt_binds
#print axioms Nock.NockVMROM.Thm54.BoundSemanticTrace.skeletonComparison_faithful
#print axioms Nock.NockVMROM.Thm54.SemanticTrace.ComputeRowSemanticData.ofSkeleton
#print axioms Nock.NockVMROM.Thm54.SemanticTrace.ComputeRowSemanticData.ofBoundSkeleton
#print axioms Nock.NockVMROM.Thm54.SemanticTrace.ExactExecutionSemanticData.ofBoundSkeleton
#print axioms Nock.NockVMROM.Thm54.P8Census.skeletonComparisonCompatibility_ofBoundSkeleton
