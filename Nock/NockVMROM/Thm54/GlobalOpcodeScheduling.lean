import Nock.NockVMROM.Thm54.OpcodeScheduling
import Nock.NockVMROM.Thm54.EdgeComparisonCensus

/-!
# Global opcode scheduling: production boundary

`OpcodeScheduling` closes all eleven local frame/index schedules, superseding the old
`DFSScheduling.ProductionOpcodeFrameIndexResidual`.  The intended production recursion must,
however, not assume `ExactExecutionLocalCertificates`: recursive constructors of that type already
store the child `FieldEmbedding.evalFBy` equations which bottom-up assembly is meant to derive.

This module proves the adapters available without that circular input:

* exact `Fcomp` topology fixes each actual node's child count;
* every actual node has a mechanically obtained canonical BFS row index;
* successful `evalFBy` executions can be raised to common fuel;
* a maximal ROM trace ending in `Verb.ofNoun result` implies a genuine `Nock.evalN` evaluation.

`EdgeComparisonCensus` closes noun-level coherence of adjacent skeleton rows using one fixed,
pre-seed collision census. It is not a production assumption.
-/

namespace Nock.NockVMROM.Thm54.GlobalOpcodeScheduling

open scoped Classical
open Nock Nock.Noun Nock.Verb Nock.Walk
open ComputeTable
open DFSScheduling
open SemanticTrace
open OpcodeScheduling

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Exact topology, not an arbitrary equation, identifies the number of actual children at every
compute node. -/
theorem child_count_of_Fcomp
    {tree node : NTree (State × DTcomp K)}
    (htopology : RVTWithArity (Fcomp (K := K)) tree)
    (hnode : InTree tree node) :
    node.children.length = fanoutComp node.label.1 :=
  (fanout_eq_children_length_of_properArity
    (ComputeTable.comp_stateSep (K := K))
    htopology.rvt htopology.arity node hnode).symm

/-- `Fcomp` exposes the actual active child label and its committed call triple. -/
theorem actual_child_identifies_call_slot
    {tree node : NTree (State × DTcomp K)}
    (htopology : RVTWithArity (Fcomp (K := K)) tree)
    (hnode : InTree tree node)
    (i : Fin 3) (hi : (i : ℕ) < fanoutComp node.label.1) :
    ∃ child,
      node.childOpt i = some child ∧
      (child.label.2.2.1.s, child.label.2.2.1.f, child.label.2.2.1.e) =
        sfTriple node.label.2.2.1 i := by
  have hFcon :=
    (RVT_iff_forall_InTree (Fcomp (K := K)) tree).mp htopology.rvt node hnode
  obtain ⟨childLabel, hlabel, htriple⟩ :=
    Fcomp_identifies_program_result hFcon.1 i hi
  cases hc : node.childOpt i with
  | none =>
      simp [NTree.childLabel, hc] at hlabel
  | some child =>
      refine ⟨child, rfl, ?_⟩
      have : child.label = childLabel := by
        have hs : some child.label = some childLabel := by
          simpa [NTree.childLabel, hc] using hlabel
        exact Option.some.inj hs
      subst childLabel
      exact htriple

/-- Every actual node of an exact execution occurs at a canonical BFS row.  No node-index map is
stored in production data. -/
theorem exists_computeRowIndex_of_inTree
    {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    {node : NTree (State × DTcomp K)}
    (hnode : InTree exec.computeTree node) :
    ∃ i : Fin cfg.compRows, exec.computeRowAt i = node.label := by
  have hnodeBfs : node ∈ bfsForest [exec.computeTree] :=
    (mem_bfsForest [exec.computeTree] node).2
      ⟨exec.computeTree, by simp, hnode⟩
  have hlabel : node.label ∈ exec.computeRows := by
    rw [ExactExecution.computeRows]
    exact List.mem_map.2 ⟨node, hnodeBfs, rfl⟩
  obtain ⟨n, hn, hget⟩ := List.getElem_of_mem hlabel
  let j : Fin exec.computeRows.length := ⟨n, hn⟩
  let i : Fin cfg.compRows := Fin.cast exec.computeRows_length j
  refine ⟨i, ?_⟩
  simpa [i, j, List.get_eq_getElem] using
    (exec.computeRowAt_cast j).trans hget

/-- A trace endpoint in the form used by the recursive scheduler. -/
def TraceEndpoint (root : Verb) (result : Noun) (trace : List Verb) : Prop :=
  Verb.TraceOfROM root trace ∧
    trace.getLast? = some (Verb.ofNoun result)

theorem MaximalDFSTrace.toEndpoint
    {root : Verb} {result : Noun} {trace : List Verb}
    (h : MaximalDFSTrace root result trace) :
    TraceEndpoint root result trace :=
  ⟨⟨h.1, consistentROM_of_dfsSchedule h.2.1⟩, h.2.2.1⟩

private theorem den_of_traceEndpoint
    {result : Noun} :
    ∀ {before : Verb} {trace : List Verb},
      TraceEndpoint before result trace →
      Verb.editOk before = true →
      ∃ fuel, Verb.den fuel before = some result := by
  intro before trace htrace
  rcases htrace with ⟨⟨hhead, hsched⟩, hlast⟩
  induction trace generalizing before with
  | nil => simp at hhead
  | cons first rest ih =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst first
      intro hok
      cases rest with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          subst before
          exact ⟨result.size, Verb.den_ofNoun result result.size le_rfl⟩
      | cons next tail =>
          simp only [ConsistentR] at hsched
          have hstep : Verb.next before = some next :=
            Verb.step_of_stepROM hsched.1
          have hnextOk : Verb.editOk next = true :=
            Verb.editOk_next hstep hok
          have hdenNext :=
            ih (by simpa using hlast) (by rfl) hsched.2 hnextOk
          exact (Verb.den_step hok hstep).2 hdenNext

/-- Proved one-direction evaluator adapter: a complete maximal ROM execution computes the same
result in the Nat reference evaluator. -/
theorem evalN_of_maximalDFSTrace
    {subject formula result : Noun} {trace : List Verb}
    (h : MaximalDFSTrace (Verb.program subject formula) result trace) :
    ∃ fuel, Nock.evalN fuel subject formula = some result := by
  have hden :=
    den_of_traceEndpoint (MaximalDFSTrace.toEndpoint h)
      (Verb.editOk_program subject formula)
  exact (Verb.den_iff_evalN subject formula result).1 hden

/-- Successful field evaluation is stable when one unit of fuel is added. -/
theorem evalFBy_succ {q fuel : ℕ} {subject formula result : Noun}
    (h : FieldEmbedding.evalFBy q fuel subject formula = some result) :
    FieldEmbedding.evalFBy q (fuel + 1) subject formula = some result := by
  induction fuel, subject, formula using FieldEmbedding.evalFBy.induct q
      generalizing result with
  | case11 fuel subject tail ih =>
      simp only [FieldEmbedding.evalFBy, Option.map_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | case12 fuel subject tail ih =>
      simp only [FieldEmbedding.evalFBy, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | _ => simp_all [FieldEmbedding.evalFBy]

/-- Successful field evaluation is stable under any larger fuel budget. -/
theorem evalFBy_mono {q n m : ℕ} {subject formula result : Noun}
    (hnm : n ≤ m)
    (h : FieldEmbedding.evalFBy q n subject formula = some result) :
    FieldEmbedding.evalFBy q m subject formula = some result := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact evalFBy_succ ih

/-- Two independently obtained child evaluations can be padded to one common fuel. -/
theorem evalFBy_commonFuel₂
    {q f₁ f₂ : ℕ}
    {s₁ p₁ r₁ s₂ p₂ r₂ : Noun}
    (h₁ : FieldEmbedding.evalFBy q f₁ s₁ p₁ = some r₁)
    (h₂ : FieldEmbedding.evalFBy q f₂ s₂ p₂ = some r₂) :
    ∃ fuel,
      FieldEmbedding.evalFBy q fuel s₁ p₁ = some r₁ ∧
      FieldEmbedding.evalFBy q fuel s₂ p₂ = some r₂ :=
  ⟨max f₁ f₂,
    evalFBy_mono (Nat.le_max_left _ _) h₁,
    evalFBy_mono (Nat.le_max_right _ _) h₂⟩

/-- Three independently obtained OP2 child evaluations can be padded to one common fuel. -/
theorem evalFBy_commonFuel₃
    {q f₁ f₂ f₃ : ℕ}
    {s₁ p₁ r₁ s₂ p₂ r₂ s₃ p₃ r₃ : Noun}
    (h₁ : FieldEmbedding.evalFBy q f₁ s₁ p₁ = some r₁)
    (h₂ : FieldEmbedding.evalFBy q f₂ s₂ p₂ = some r₂)
    (h₃ : FieldEmbedding.evalFBy q f₃ s₃ p₃ = some r₃) :
    ∃ fuel,
      FieldEmbedding.evalFBy q fuel s₁ p₁ = some r₁ ∧
      FieldEmbedding.evalFBy q fuel s₂ p₂ = some r₂ ∧
      FieldEmbedding.evalFBy q fuel s₃ p₃ = some r₃ := by
  refine ⟨max f₁ (max f₂ f₃), ?_, ?_, ?_⟩
  · exact evalFBy_mono (by omega) h₁
  · exact evalFBy_mono (by omega) h₂
  · exact evalFBy_mono (by omega) h₃

/-- Compatibility alias for the now-derived fixed-census edge property. -/
abbrev ChildSkeletonCoherence :=
  EdgeComparisonCensus.ChildSkeletonCoherence

/-- Edge coherence is derived from the combined pre-seed census, never passed independently. -/
theorem childSkeletonCoherence_of_bareCensus
    [Fintype K] [DecidableEq K]
    (S : SemanticStrategy.SemanticSkeleton)
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) (z : K)
    (binds : SemanticStrategy.BindsAt z S cfg exec)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K S Λ)
    {q : ℕ} (hb : S.BoundedBy q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (htopology : RVTWithArity (Fcomp (K := K)) exec.computeTree)
    (hgood : z ∉ C.census.badSeeds (K := K)) :
    ChildSkeletonCoherence S.computeTree :=
  EdgeComparisonCensus.childSkeletonCoherence_of_skeletonCensus
    S exec z binds C hb hcast htopology hgood

/-- Compatibility wrapper for the proof-carrying strategy interface. -/
theorem childSkeletonCoherence_of_fixedCensus
    [Fintype K] [DecidableEq K]
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (C : EdgeComparisonCensus.CombinedBoundCensus T Λ)
    (z : K) (hz : z ≠ 0) {q : ℕ}
    (hb : T.skeleton.BoundedBy q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (htopology : RVTWithArity (Fcomp (K := K))
      (P8Census.boundSampledExec T z hz).computeTree)
    (hgood : z ∉ C.census.badSeeds (K := K)) :
    ChildSkeletonCoherence T.skeleton.computeTree :=
  EdgeComparisonCensus.childSkeletonCoherence_of_combinedCensus
    T C z hz hb hcast htopology hgood

private abbrev CanonicalRowData
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ) :=
  (BoundSemanticTrace.buildCoveredRow hb hop hbind hfaith hleaves).1

@[simp] private theorem canonical_root_subject
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ) :
    (CanonicalRowData hb hop hbind hfaith hleaves).root.subject = s.subject := by
  rcases s with ⟨state, subject, formula, evaluation,
    decomposition, subformula, memoryRecord⟩
  rcases row with ⟨rowState, inp, pub, dec⟩
  rcases hbind with
    ⟨hrowState, hseed, hpubState, hsubject, hformula, hevaluation,
      hdec, hsf, hmr⟩
  change rowState = state at hrowState
  subst rowState
  cases state <;> rfl

@[simp] private theorem canonical_root_formula
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ) :
    (CanonicalRowData hb hop hbind hfaith hleaves).root.formula = s.formula := by
  rcases s with ⟨state, subject, formula, evaluation,
    decomposition, subformula, memoryRecord⟩
  rcases row with ⟨rowState, inp, pub, dec⟩
  rcases hbind with
    ⟨hrowState, hseed, hpubState, hsubject, hformula, hevaluation,
      hdec, hsf, hmr⟩
  change rowState = state at hrowState
  subst rowState
  cases state <;> rfl

@[simp] private theorem canonical_root_result
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ) :
    (CanonicalRowData hb hop hbind hfaith hleaves).root.result = s.evaluation := by
  rcases s with ⟨state, subject, formula, evaluation,
    decomposition, subformula, memoryRecord⟩
  rcases row with ⟨rowState, inp, pub, dec⟩
  rcases hbind with
    ⟨hrowState, hseed, hpubState, hsubject, hformula, hevaluation,
      hdec, hsf, hmr⟩
  change rowState = state at hrowState
  subst rowState
  cases state <;> rfl

@[simp] private theorem canonical_root_head
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ) :
    (CanonicalRowData hb hop hbind hfaith hleaves).root.head =
      P8Census.skeletonDec s .f_h := by
  rcases s with ⟨state, subject, formula, evaluation,
    decomposition, subformula, memoryRecord⟩
  rcases row with ⟨rowState, inp, pub, dec⟩
  rcases hbind with
    ⟨hrowState, hseed, hpubState, hsubject, hformula, hevaluation,
      hdec, hsf, hmr⟩
  change rowState = state at hrowState
  subst rowState
  cases state <;> rfl

@[simp] private theorem canonical_root_tail
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ) :
    (CanonicalRowData hb hop hbind hfaith hleaves).root.tail =
      P8Census.skeletonDec s .f_t := by
  rcases s with ⟨state, subject, formula, evaluation,
    decomposition, subformula, memoryRecord⟩
  rcases row with ⟨rowState, inp, pub, dec⟩
  rcases hbind with
    ⟨hrowState, hseed, hpubState, hsubject, hformula, hevaluation,
      hdec, hsf, hmr⟩
  change rowState = state at hrowState
  subst rowState
  cases state <;> rfl

@[simp] private theorem canonical_comparisons
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ) :
    (CanonicalRowData hb hop hbind hfaith hleaves).comparisons =
      P8Census.skeletonComparisons (K := K) s :=
  BoundSemanticTrace.buildCoveredRow_comparisons hb hop hbind hfaith hleaves

private def canonicalCall
    {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {st : State} {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hbind : SemanticStrategy.BindComputeRow z s (st, (inp, pub, dec)))
    (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state) :
    OpcodeSemantics.CallRealization inp.z
      (computeSubformulaFPs pub i).1
      (computeSubformulaFPs pub i).2.1
      (computeSubformulaFPs pub i).2.2 := by
  rcases hbind with ⟨_, hseed, _, _, _, _, _, hsf, _⟩
  have h := hsf i
  simp only [dif_pos hi] at h
  exact
    { subject := s.subformula i hi .subject
      formula := s.subformula i hi .formula
      result := s.subformula i hi .result
      subject_realizes := by rw [hseed]; exact h .subject
      formula_realizes := by rw [hseed]; exact h .formula
      result_realizes := by rw [hseed]; exact h .result }

private def canonicalTail
    {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {st : State} {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hbind : SemanticStrategy.BindComputeRow z s (st, (inp, pub, dec)))
    (hactive : SemanticStrategy.hasTailDecomposition s.state = true) :
    OpcodeSemantics.TailRealization inp.z dec := by
  rcases hbind with ⟨_, hseed, _, _, _, _, hdec, _, _⟩
  have hheadActive :
      SemanticStrategy.decActive s.state .f_th = true := by
    simpa [SemanticStrategy.decActive] using hactive
  have htailActive :
      SemanticStrategy.decActive s.state .f_tt = true := by
    simpa [SemanticStrategy.decActive] using hactive
  have hh := hdec .f_th
  have ht := hdec .f_tt
  simp only [dif_pos hheadActive] at hh
  simp only [dif_pos htailActive] at ht
  exact
    { head := s.decomposition .f_th hheadActive
      tail := s.decomposition .f_tt htailActive
      head_realizes := by rw [hseed]; exact hh
      tail_realizes := by rw [hseed]; exact ht }

@[simp] private theorem canonicalCall_subject
    {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {st : State} {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hbind : SemanticStrategy.BindComputeRow z s (st, (inp, pub, dec)))
    (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state) :
    (canonicalCall hbind i hi).subject = s.subformula i hi .subject := by
  rcases hbind with ⟨_, hseed, _, _, _, _, _, hsf, _⟩
  rfl

@[simp] private theorem canonicalCall_formula
    {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {st : State} {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hbind : SemanticStrategy.BindComputeRow z s (st, (inp, pub, dec)))
    (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state) :
    (canonicalCall hbind i hi).formula = s.subformula i hi .formula := by
  rcases hbind with ⟨_, hseed, _, _, _, _, _, hsf, _⟩
  rfl

@[simp] private theorem canonicalCall_result
    {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {st : State} {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hbind : SemanticStrategy.BindComputeRow z s (st, (inp, pub, dec)))
    (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state) :
    (canonicalCall hbind i hi).result = s.subformula i hi .result := by
  rcases hbind with ⟨_, hseed, _, _, _, _, _, hsf, _⟩
  rfl

@[simp] private theorem canonicalTail_head
    {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {st : State} {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hbind : SemanticStrategy.BindComputeRow z s (st, (inp, pub, dec)))
    (hactive : SemanticStrategy.hasTailDecomposition s.state = true) :
    (canonicalTail hbind hactive).head =
      P8Census.skeletonDec s .f_th := by
  rcases hbind with ⟨_, hseed, _, _, _, _, hdec, _, _⟩
  simp [canonicalTail, P8Census.skeletonDec, hactive,
    SemanticStrategy.decActive]

@[simp] private theorem canonicalTail_tail
    {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {st : State} {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hbind : SemanticStrategy.BindComputeRow z s (st, (inp, pub, dec)))
    (hactive : SemanticStrategy.hasTailDecomposition s.state = true) :
    (canonicalTail hbind hactive).tail =
      P8Census.skeletonDec s .f_tt := by
  rcases hbind with ⟨_, hseed, _, _, _, _, hdec, _, _⟩
  simp [canonicalTail, P8Census.skeletonDec, hactive,
    SemanticStrategy.decActive]

private def canonicalBranch
    {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hs : s.state = .s6)
    (hbind : SemanticStrategy.BindComputeRow z s (.s6, (inp, pub, dec))) :
    OpcodeSemantics.BranchTailRealization inp.z dec := by
  rcases hbind with ⟨_, hseed, _, _, _, _, hdec, _, _⟩
  have hh := hdec .f_tth
  have ht := hdec .f_ttt
  simp [hs, SemanticStrategy.decActive] at hh ht
  exact
    { head := s.decomposition .f_tth (by simp [hs, SemanticStrategy.decActive])
      tail := s.decomposition .f_ttt (by simp [hs, SemanticStrategy.decActive])
      head_realizes := by rw [hseed]; exact hh
      tail_realizes := by rw [hseed]; exact ht }

@[simp] private theorem canonicalBranch_head
    {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hs : s.state = .s6)
    (hbind : SemanticStrategy.BindComputeRow z s (.s6, (inp, pub, dec))) :
    (canonicalBranch hs hbind).head = P8Census.skeletonDec s .f_tth := by
  rcases hbind with ⟨_, hseed, _, _, _, _, hdec, _, _⟩
  simp [canonicalBranch, P8Census.skeletonDec, hs, SemanticStrategy.decActive]

@[simp] private theorem canonicalBranch_tail
    {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hs : s.state = .s6)
    (hbind : SemanticStrategy.BindComputeRow z s (.s6, (inp, pub, dec))) :
    (canonicalBranch hs hbind).tail = P8Census.skeletonDec s .f_ttt := by
  rcases hbind with ⟨_, hseed, _, _, _, _, hdec, _, _⟩
  simp [canonicalBranch, P8Census.skeletonDec, hs, SemanticStrategy.decActive]

private def canonicalLocalCertificate_s0
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hs : s.state = .s0)
    (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s (.s0, (inp, pub, dec)))
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hz : z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hv : Vcomp inp pub dec) :
    LocalOpcodeCertificate q Λ
      (CanonicalRowData hb hop hbind hfaith hleaves) := by
  let data := CanonicalRowData hb hop hbind hfaith hleaves
  change LocalOpcodeCertificate q Λ data
  have hdSubject := canonical_root_subject hb hop hbind hfaith hleaves
  have hdFormula := canonical_root_formula hb hop hbind hfaith hleaves
  have hdResult := canonical_root_result hb hop hbind hfaith hleaves
  have hdHead := canonical_root_head hb hop hbind hfaith hleaves
  have hdTail := canonical_root_tail hb hop hbind hfaith hleaves
  have hstate : pub.state = .s0 := hbind.2.2.1.trans hs
  have hinpz : inp.z = z := hbind.2.1
  have hhead : ComparisonListed data .opcodeHead data.root.head (.atom 0) := by
    simp [ComparisonListed, data, hdHead, P8Census.skeletonComparisons,
      P8Census.skeletonUse, hs]
  have hformula : ComparisonListed data .formulaCons data.root.formula
      (.cell data.root.head data.root.tail) := by
    simp [ComparisonListed, data, hdFormula, hdHead, hdTail,
      P8Census.skeletonComparisons,
      P8Census.skeletonUse, hs]
  let axis := P8Census.skeletonMemoryAxis s 1
  have htail : ComparisonListed data .recursiveFormula data.root.tail (.atom axis) := by
    simp [ComparisonListed, data, hdTail, P8Census.skeletonComparisons,
      P8Census.skeletonUse, axis, hs]
  have hiMR : (1 : ℕ) < Nock.Framework.recordCount s.state := by
    simp [hs, Nock.Framework.recordCount]
  have hmr1 := hbind.2.2.2.2.2.2.2.2 (1 : Fin 3)
  simp [hs, Nock.Framework.recordCount] at hmr1
  have hrecord := hop.s0_record hs
  dsimp only at hrecord
  have hmr' : OpcodeSemantics.RealizesMemRec inp.z pub.mr2
      data.root.subject data.root.result axis := by
    rw [hdSubject, hdResult]
    have hroot := hmr1.1
    have hchild := hmr1.2.1
    rw [hrecord.1] at hroot
    rw [hrecord.2] at hchild
    exact
      { root_realizes := by rw [hinpz]; exact hroot
        child_realizes := by rw [hinpz]; exact hchild
        axis_realizes := by
          simpa [axis, P8Census.skeletonMemoryAxis, hs,
            Nock.Framework.recordCount, computeMemRec] using hmr1.2.2 }
  have hserved : GlobalCarryAxis.ServedLookup
      (GlobalCarryRecognizer.ofNoun data.root.subject 1) axis data.root.result := by
    rw [hdSubject, hdResult]
    exact hop.s0_served hs
  exact .s0 data 0 axis hstate (hinpz ▸ hz) hcast
    hhead hformula htail hmr' hserved hv

private def canonicalLocalCertificate_s1
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hs : s.state = .s1)
    (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s (.s1, (inp, pub, dec)))
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hz : z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hv : Vcomp inp pub dec) :
    LocalOpcodeCertificate q Λ
      (CanonicalRowData hb hop hbind hfaith hleaves) := by
  let data := CanonicalRowData hb hop hbind hfaith hleaves
  change LocalOpcodeCertificate q Λ data
  have hdFormula := canonical_root_formula hb hop hbind hfaith hleaves
  have hdResult := canonical_root_result hb hop hbind hfaith hleaves
  have hdHead := canonical_root_head hb hop hbind hfaith hleaves
  have hdTail := canonical_root_tail hb hop hbind hfaith hleaves
  have hstate : pub.state = .s1 := hbind.2.2.1.trans hs
  have hinpz : inp.z = z := hbind.2.1
  have hhead : ComparisonListed data .opcodeHead data.root.head (.atom 1) := by
    simp [ComparisonListed, data, hdHead, P8Census.skeletonComparisons,
      P8Census.skeletonUse, hs]
  have hformula : ComparisonListed data .formulaCons data.root.formula
      (.cell data.root.head data.root.tail) := by
    simp [ComparisonListed, data, hdFormula, hdHead, hdTail,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs]
  have hresult : ComparisonListed data .producedResult
      data.root.result data.root.tail := by
    simp [ComparisonListed, data, hdResult, hdTail,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs]
  exact .s1 data 0 hstate (hinpz ▸ hz) hcast hhead hformula hresult hv

def canonicalLocalCertificate_s2
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hs : s.state = .s2)
    (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s (.s2, (inp, pub, dec)))
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hz : z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hv : Vcomp inp pub dec)
    {f₁ f₂ f₃ : ℕ}
    (heval₁ : FieldEmbedding.evalFBy q f₁
      (s.subformula 0 (by simp [hs, fanoutComp]) .subject)
      (s.subformula 0 (by simp [hs, fanoutComp]) .formula) =
        some (s.subformula 0 (by simp [hs, fanoutComp]) .result))
    (heval₂ : FieldEmbedding.evalFBy q f₂
      (s.subformula 1 (by simp [hs, fanoutComp]) .subject)
      (s.subformula 1 (by simp [hs, fanoutComp]) .formula) =
        some (s.subformula 1 (by simp [hs, fanoutComp]) .result))
    (heval₃ : FieldEmbedding.evalFBy q f₃
      (s.subformula 2 (by simp [hs, fanoutComp]) .subject)
      (s.subformula 2 (by simp [hs, fanoutComp]) .formula) =
        some (s.subformula 2 (by simp [hs, fanoutComp]) .result)) :
    LocalOpcodeCertificate q Λ
      (CanonicalRowData hb hop hbind hfaith hleaves) := by
  let data := CanonicalRowData hb hop hbind hfaith hleaves
  let tail := canonicalTail hbind (by simp [hs, SemanticStrategy.hasTailDecomposition])
  let call1 := canonicalCall hbind 0 (by simp [hs, fanoutComp])
  let call2 := canonicalCall hbind 1 (by simp [hs, fanoutComp])
  let call3 := canonicalCall hbind 2 (by simp [hs, fanoutComp])
  let fuel := max f₁ (max f₂ f₃)
  have hcall1 := evalFBy_mono (q := q) (m := fuel) (by simp [fuel]) heval₁
  have hcall2 := evalFBy_mono (q := q) (m := fuel) (by simp [fuel]) heval₂
  have hcall3 := evalFBy_mono (q := q) (m := fuel) (by simp [fuel]) heval₃
  have hstate : pub.state = .s2 := hbind.2.2.1.trans hs
  have hinpz : inp.z = z := hbind.2.1
  have hhead : ComparisonListed data .opcodeHead data.root.head (.atom 2) := by
    simp [ComparisonListed, data, P8Census.skeletonComparisons,
      P8Census.skeletonUse, hs]
  have hformula : ComparisonListed data .formulaCons data.root.formula
      (.cell data.root.head data.root.tail) := by
    simp [ComparisonListed, data, P8Census.skeletonComparisons,
      P8Census.skeletonUse, hs]
  have htail : ComparisonListed data .tailCons data.root.tail
      (.cell tail.head tail.tail) := by
    simp [ComparisonListed, data, tail,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs,
      SemanticStrategy.hasTailDecomposition, SemanticStrategy.decActive]
  have h1s : ComparisonListed data .recursiveSubject
      call1.subject data.root.subject := by
    simp [ComparisonListed, data, call1, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h1f : ComparisonListed data .recursiveFormula call1.formula tail.head := by
    simp [ComparisonListed, data, call1, tail, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs,
      fanoutComp, SemanticStrategy.hasTailDecomposition, SemanticStrategy.decActive]
  have h2s : ComparisonListed data .recursiveSubject
      call2.subject data.root.subject := by
    simp [ComparisonListed, data, call2, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h2f : ComparisonListed data .recursiveFormula call2.formula tail.tail := by
    simp [ComparisonListed, data, call2, tail, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs,
      fanoutComp, SemanticStrategy.hasTailDecomposition, SemanticStrategy.decActive]
  have h3s : ComparisonListed data .recursiveSubject
      call3.subject call1.result := by
    simp [ComparisonListed, data, call1, call3, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h3f : ComparisonListed data .recursiveFormula
      call3.formula call2.result := by
    simp [ComparisonListed, data, call2, call3, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have hresult : ComparisonListed data .producedResult
      data.root.result call3.result := by
    simp [ComparisonListed, data, call3, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  refine .s2 data fuel tail call1 call2 call3 hstate (hinpz ▸ hz) hcast
    hhead hformula htail h1s h1f h2s h2f h3s h3f hresult ?_ ?_ ?_ hv
  · simpa [call1, hs, fanoutComp] using hcall1
  · simpa [call2, hs, fanoutComp] using hcall2
  · simpa [call3, hs, fanoutComp] using hcall3

def canonicalLocalCertificate_s3
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hs : s.state = .s3)
    (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s (.s3, (inp, pub, dec)))
    (hfaith : ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
      OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves : ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hz : z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hv : Vcomp inp pub dec) {fuel : ℕ}
    (heval : FieldEmbedding.evalFBy q fuel
      (s.subformula 0 (by simp [hs, fanoutComp]) .subject)
      (s.subformula 0 (by simp [hs, fanoutComp]) .formula) =
        some (s.subformula 0 (by simp [hs, fanoutComp]) .result)) :
    LocalOpcodeCertificate q Λ
      (CanonicalRowData hb hop hbind hfaith hleaves) := by
  let data := CanonicalRowData hb hop hbind hfaith hleaves
  let call1 := canonicalCall hbind 0 (by simp [hs, fanoutComp])
  have hstate : pub.state = .s3 := hbind.2.2.1.trans hs
  have hinpz : inp.z = z := hbind.2.1
  have hhead : ComparisonListed data .opcodeHead data.root.head (.atom 3) := by
    simp [ComparisonListed, data, P8Census.skeletonComparisons,
      P8Census.skeletonUse, hs]
  have hformula : ComparisonListed data .formulaCons data.root.formula
      (.cell data.root.head data.root.tail) := by
    simp [ComparisonListed, data, P8Census.skeletonComparisons,
      P8Census.skeletonUse, hs]
  have h1s : ComparisonListed data .recursiveSubject
      call1.subject data.root.subject := by
    simp [ComparisonListed, data, call1, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h1f : ComparisonListed data .recursiveFormula
      call1.formula data.root.tail := by
    simp [ComparisonListed, data, call1, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have hresult : ComparisonListed data .producedResult data.root.result
      (Noun.wut call1.result) := by
    simp [ComparisonListed, data, call1, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have hsize : OpcodeSemantics.SizeWindow inp.z call1.result := by
    have hw : OpcodeSemantics.SizeWindow inp.z
        (P8Census.skeletonSubformula s 0 .result) := by
      simpa [hinpz] using hop.s3_window hs
    simpa [call1, P8Census.skeletonSubformula, hs, fanoutComp] using hw
  refine .s3 data fuel call1 hstate (hinpz ▸ hz) hcast
    hhead hformula h1s h1f hresult hsize ?_ hv
  simpa [call1, hs, fanoutComp] using heval

def canonicalLocalCertificate_s4
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hs : s.state = .s4)
    (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s (.s4, (inp, pub, dec)))
    (hfaith : ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
      OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves : ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hz : z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hv : Vcomp inp pub dec) {fuel : ℕ}
    (heval : FieldEmbedding.evalFBy q fuel
      (s.subformula 0 (by simp [hs, fanoutComp]) .subject)
      (s.subformula 0 (by simp [hs, fanoutComp]) .formula) =
        some (s.subformula 0 (by simp [hs, fanoutComp]) .result)) :
    LocalOpcodeCertificate q Λ
      (CanonicalRowData hb hop hbind hfaith hleaves) := by
  let data := CanonicalRowData hb hop hbind hfaith hleaves
  let call1 := canonicalCall hbind 0 (by simp [hs, fanoutComp])
  have hstate : pub.state = .s4 := hbind.2.2.1.trans hs
  have hinpz : inp.z = z := hbind.2.1
  have hhead : ComparisonListed data .opcodeHead data.root.head (.atom 4) := by
    simp [ComparisonListed, data, P8Census.skeletonComparisons,
      P8Census.skeletonUse, hs]
  have hformula : ComparisonListed data .formulaCons data.root.formula
      (.cell data.root.head data.root.tail) := by
    simp [ComparisonListed, data, P8Census.skeletonComparisons,
      P8Census.skeletonUse, hs]
  have h1s : ComparisonListed data .recursiveSubject
      call1.subject data.root.subject := by
    simp [ComparisonListed, data, call1, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h1f : ComparisonListed data .recursiveFormula
      call1.formula data.root.tail := by
    simp [ComparisonListed, data, call1, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have hresult : ComparisonListed data .producedResult data.root.result
      (OpcodeSemantics.incMod (ringChar K) call1.result) := by
    simp [ComparisonListed, data, call1, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have hsize : OpcodeSemantics.SizeWindow inp.z call1.result := by
    have hw : OpcodeSemantics.SizeWindow inp.z
        (P8Census.skeletonSubformula s 0 .result) := by
      simpa [hinpz] using hop.s4_window hs
    simpa [call1, P8Census.skeletonSubformula, hs, fanoutComp] using hw
  refine .s4 data fuel call1 hstate (hinpz ▸ hz) hop.q_eq_ringChar hcast
    hhead hformula h1s h1f hresult hsize ?_ hv
  simpa [call1, hs, fanoutComp] using heval

def canonicalLocalCertificate_s5
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hs : s.state = .s5)
    (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s (.s5, (inp, pub, dec)))
    (hfaith : ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
      OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves : ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hz : z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hv : Vcomp inp pub dec)
    {f₁ f₂ : ℕ}
    (heval₁ : FieldEmbedding.evalFBy q f₁
      (s.subformula 0 (by simp [hs, fanoutComp]) .subject)
      (s.subformula 0 (by simp [hs, fanoutComp]) .formula) =
        some (s.subformula 0 (by simp [hs, fanoutComp]) .result))
    (heval₂ : FieldEmbedding.evalFBy q f₂
      (s.subformula 1 (by simp [hs, fanoutComp]) .subject)
      (s.subformula 1 (by simp [hs, fanoutComp]) .formula) =
        some (s.subformula 1 (by simp [hs, fanoutComp]) .result)) :
    LocalOpcodeCertificate q Λ
      (CanonicalRowData hb hop hbind hfaith hleaves) := by
  let data := CanonicalRowData hb hop hbind hfaith hleaves
  let tail := canonicalTail hbind (by simp [hs, SemanticStrategy.hasTailDecomposition])
  let call1 := canonicalCall hbind 0 (by simp [hs, fanoutComp])
  let call2 := canonicalCall hbind 1 (by simp [hs, fanoutComp])
  let fuel := max f₁ f₂
  have hcall1 := evalFBy_mono (q := q) (m := fuel) (by simp [fuel]) heval₁
  have hcall2 := evalFBy_mono (q := q) (m := fuel) (by simp [fuel]) heval₂
  have hstate : pub.state = .s5 := hbind.2.2.1.trans hs
  have hinpz : inp.z = z := hbind.2.1
  have hhead : ComparisonListed data .opcodeHead data.root.head (.atom 5) := by
    simp [ComparisonListed, data, P8Census.skeletonComparisons,
      P8Census.skeletonUse, hs]
  have hformula : ComparisonListed data .formulaCons data.root.formula
      (.cell data.root.head data.root.tail) := by
    simp [ComparisonListed, data, P8Census.skeletonComparisons,
      P8Census.skeletonUse, hs]
  have htail : ComparisonListed data .tailCons data.root.tail
      (.cell tail.head tail.tail) := by
    simp [ComparisonListed, data, tail, P8Census.skeletonComparisons,
      P8Census.skeletonUse, hs]
  have h1s : ComparisonListed data .recursiveSubject
      call1.subject data.root.subject := by
    simp [ComparisonListed, data, call1, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h1f : ComparisonListed data .recursiveFormula call1.formula tail.head := by
    simp [ComparisonListed, data, call1, tail, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h2s : ComparisonListed data .recursiveSubject
      call2.subject data.root.subject := by
    simp [ComparisonListed, data, call2, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h2f : ComparisonListed data .recursiveFormula call2.formula tail.tail := by
    simp [ComparisonListed, data, call2, tail, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have hcompare : ComparisonListed data .equalityOperand
      call1.result call2.result := by
    simp [ComparisonListed, data, call1, call2, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have hresult : ComparisonListed data .producedResult data.root.result
      (Noun.tis call1.result call2.result) := by
    simp [ComparisonListed, data, call1, call2, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  refine .s5 data fuel tail call1 call2 hstate (hinpz ▸ hz) hcast
    hhead hformula htail h1s h1f h2s h2f hcompare hresult ?_ ?_ hv
  · simpa [call1, hs, fanoutComp] using hcall1
  · simpa [call2, hs, fanoutComp] using hcall2

def canonicalLocalCertificate_s6
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hs : s.state = .s6) (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s (.s6, (inp, pub, dec)))
    (hfaith : ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
      OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves : ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hz : z ≠ 0) (hq : 1 < q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hv : Vcomp inp pub dec) {f₁ f₂ : ℕ}
    (heval₁ : FieldEmbedding.evalFBy q f₁
      (s.subformula 0 (by simp [hs, fanoutComp]) .subject)
      (s.subformula 0 (by simp [hs, fanoutComp]) .formula) =
        some (s.subformula 0 (by simp [hs, fanoutComp]) .result))
    (heval₂ : FieldEmbedding.evalFBy q f₂
      (s.subformula 1 (by simp [hs, fanoutComp]) .subject)
      (s.subformula 1 (by simp [hs, fanoutComp]) .formula) =
        some (s.subformula 1 (by simp [hs, fanoutComp]) .result)) :
    LocalOpcodeCertificate q Λ
      (CanonicalRowData hb hop hbind hfaith hleaves) := by
  let data := CanonicalRowData hb hop hbind hfaith hleaves
  let tail := canonicalTail hbind (by simp [hs, SemanticStrategy.hasTailDecomposition])
  let branch := canonicalBranch hs hbind
  let call1 := canonicalCall hbind 0 (by simp [hs, fanoutComp])
  let call2 := canonicalCall hbind 1 (by simp [hs, fanoutComp])
  let fuel := max f₁ f₂
  have hc1 := evalFBy_mono (q := q) (m := fuel) (by simp [fuel]) heval₁
  have hc2 := evalFBy_mono (q := q) (m := fuel) (by simp [fuel]) heval₂
  have hstate : pub.state = .s6 := hbind.2.2.1.trans hs
  have hinpz : inp.z = z := hbind.2.1
  have hhead : ComparisonListed data .opcodeHead data.root.head (.atom 6) := by
    simp [ComparisonListed, data, P8Census.skeletonComparisons, P8Census.skeletonUse, hs]
  have hformula : ComparisonListed data .formulaCons data.root.formula
      (.cell data.root.head data.root.tail) := by
    simp [ComparisonListed, data, P8Census.skeletonComparisons, P8Census.skeletonUse, hs]
  have htail : ComparisonListed data .tailCons data.root.tail (.cell tail.head tail.tail) := by
    simp [ComparisonListed, data, tail, P8Census.skeletonComparisons, P8Census.skeletonUse, hs]
  have hbranch : ComparisonListed data .branchTailCons tail.tail
      (.cell branch.head branch.tail) := by
    simp [ComparisonListed, data, tail, branch, P8Census.skeletonComparisons,
      P8Census.skeletonUse, hs]
  have h1s : ComparisonListed data .recursiveSubject call1.subject data.root.subject := by
    simp [ComparisonListed, data, call1, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h1fz : ComparisonListed data .recursiveFormula call1.formula branch.head := by
    simp [ComparisonListed, data, call1, branch, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h1fo : ComparisonListed data .recursiveFormula call1.formula branch.tail := by
    simp [ComparisonListed, data, call1, branch, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h2s : ComparisonListed data .recursiveSubject call2.subject data.root.subject := by
    simp [ComparisonListed, data, call2, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h2f : ComparisonListed data .recursiveFormula call2.formula tail.head := by
    simp [ComparisonListed, data, call2, tail, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have hresult : ComparisonListed data .producedResult data.root.result call1.result := by
    simp [ComparisonListed, data, call1, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have hbcond : FieldEmbedding.BoundedBy q call2.result := by
    simpa [call2, hs, fanoutComp] using
      hb.2.2.2.2.1 (1 : Fin 3) (by simp [hs, fanoutComp]) .result
  have hw : OpcodeSemantics.SizeWindow inp.z call2.result := by
    have hw' : OpcodeSemantics.SizeWindow inp.z
        (P8Census.skeletonSubformula s 1 .result) := by
      simpa [hinpz] using hop.s6_window hs
    simpa [call2, P8Census.skeletonSubformula, hs, fanoutComp] using hw'
  refine .s6 data fuel tail branch call1 call2 hstate (hinpz ▸ hz) hq hcast
    hhead hformula htail hbranch h1s h1fz h1fo h2s h2f hresult hbcond hw ?_ ?_ hv
  · simpa [call1, hs, fanoutComp] using hc1
  · simpa [call2, hs, fanoutComp] using hc2

def canonicalLocalCertificate_s7
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hs : s.state = .s7) (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s (.s7, (inp, pub, dec)))
    (hfaith : ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
      OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves : ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hz : z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hv : Vcomp inp pub dec) {f₁ f₂ : ℕ}
    (heval₁ : FieldEmbedding.evalFBy q f₁
      (s.subformula 0 (by simp [hs, fanoutComp]) .subject)
      (s.subformula 0 (by simp [hs, fanoutComp]) .formula) =
        some (s.subformula 0 (by simp [hs, fanoutComp]) .result))
    (heval₂ : FieldEmbedding.evalFBy q f₂
      (s.subformula 1 (by simp [hs, fanoutComp]) .subject)
      (s.subformula 1 (by simp [hs, fanoutComp]) .formula) =
        some (s.subformula 1 (by simp [hs, fanoutComp]) .result)) :
    LocalOpcodeCertificate q Λ
      (CanonicalRowData hb hop hbind hfaith hleaves) := by
  let data := CanonicalRowData hb hop hbind hfaith hleaves
  let tail := canonicalTail hbind (by simp [hs, SemanticStrategy.hasTailDecomposition])
  let call1 := canonicalCall hbind 0 (by simp [hs, fanoutComp])
  let call2 := canonicalCall hbind 1 (by simp [hs, fanoutComp])
  let fuel := max f₁ f₂
  have hc1 := evalFBy_mono (q := q) (m := fuel) (by simp [fuel]) heval₁
  have hc2 := evalFBy_mono (q := q) (m := fuel) (by simp [fuel]) heval₂
  have hstate : pub.state = .s7 := hbind.2.2.1.trans hs
  have hinpz : inp.z = z := hbind.2.1
  have hhead : ComparisonListed data .opcodeHead data.root.head (.atom 7) := by
    simp [ComparisonListed, data, P8Census.skeletonComparisons, P8Census.skeletonUse, hs]
  have hformula : ComparisonListed data .formulaCons data.root.formula
      (.cell data.root.head data.root.tail) := by
    simp [ComparisonListed, data, P8Census.skeletonComparisons, P8Census.skeletonUse, hs]
  have htail : ComparisonListed data .tailCons data.root.tail (.cell tail.head tail.tail) := by
    simp [ComparisonListed, data, tail, P8Census.skeletonComparisons, P8Census.skeletonUse, hs]
  have h2s : ComparisonListed data .recursiveSubject call2.subject data.root.subject := by
    simp [ComparisonListed, data, call2, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h2f : ComparisonListed data .recursiveFormula call2.formula tail.head := by
    simp [ComparisonListed, data, call2, tail, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h1s : ComparisonListed data .recursiveSubject call1.subject call2.result := by
    simp [ComparisonListed, data, call1, call2, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h1f : ComparisonListed data .recursiveFormula call1.formula tail.tail := by
    simp [ComparisonListed, data, call1, tail, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have hresult : ComparisonListed data .producedResult data.root.result call1.result := by
    simp [ComparisonListed, data, call1, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  refine .s7 data fuel tail call1 call2 hstate (hinpz ▸ hz) hcast
    hhead hformula htail h2s h2f h1s h1f hresult ?_ ?_ hv
  · simpa [call1, hs, fanoutComp] using hc1
  · simpa [call2, hs, fanoutComp] using hc2

def canonicalLocalCertificate_s8
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hs : s.state = .s8) (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s (.s8, (inp, pub, dec)))
    (hfaith : ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
      OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves : ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hz : z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hv : Vcomp inp pub dec) {f₁ f₂ : ℕ}
    (heval₁ : FieldEmbedding.evalFBy q f₁
      (s.subformula 0 (by simp [hs, fanoutComp]) .subject)
      (s.subformula 0 (by simp [hs, fanoutComp]) .formula) =
        some (s.subformula 0 (by simp [hs, fanoutComp]) .result))
    (heval₂ : FieldEmbedding.evalFBy q f₂
      (s.subformula 1 (by simp [hs, fanoutComp]) .subject)
      (s.subformula 1 (by simp [hs, fanoutComp]) .formula) =
        some (s.subformula 1 (by simp [hs, fanoutComp]) .result)) :
    LocalOpcodeCertificate q Λ
      (CanonicalRowData hb hop hbind hfaith hleaves) := by
  let data := CanonicalRowData hb hop hbind hfaith hleaves
  let tail := canonicalTail hbind (by simp [hs, SemanticStrategy.hasTailDecomposition])
  let call1 := canonicalCall hbind 0 (by simp [hs, fanoutComp])
  let call2 := canonicalCall hbind 1 (by simp [hs, fanoutComp])
  let fuel := max f₁ f₂
  have hc1 := evalFBy_mono (q := q) (m := fuel) (by simp [fuel]) heval₁
  have hc2 := evalFBy_mono (q := q) (m := fuel) (by simp [fuel]) heval₂
  have hstate : pub.state = .s8 := hbind.2.2.1.trans hs
  have hinpz : inp.z = z := hbind.2.1
  have hhead : ComparisonListed data .opcodeHead data.root.head (.atom 8) := by
    simp [ComparisonListed, data, P8Census.skeletonComparisons, P8Census.skeletonUse, hs]
  have hformula : ComparisonListed data .formulaCons data.root.formula
      (.cell data.root.head data.root.tail) := by
    simp [ComparisonListed, data, P8Census.skeletonComparisons, P8Census.skeletonUse, hs]
  have htail : ComparisonListed data .tailCons data.root.tail (.cell tail.head tail.tail) := by
    simp [ComparisonListed, data, tail, P8Census.skeletonComparisons, P8Census.skeletonUse, hs]
  have h2s : ComparisonListed data .recursiveSubject call2.subject data.root.subject := by
    simp [ComparisonListed, data, call2, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h2f : ComparisonListed data .recursiveFormula call2.formula tail.head := by
    simp [ComparisonListed, data, call2, tail, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h1s : ComparisonListed data .recursiveSubject call1.subject
      (.cell call2.result data.root.subject) := by
    simp [ComparisonListed, data, call1, call2, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h1f : ComparisonListed data .recursiveFormula call1.formula tail.tail := by
    simp [ComparisonListed, data, call1, tail, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have hresult : ComparisonListed data .producedResult data.root.result call1.result := by
    simp [ComparisonListed, data, call1, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  refine .s8 data fuel tail call1 call2 hstate (hinpz ▸ hz) hcast
    hhead hformula htail h2s h2f h1s h1f hresult ?_ ?_ hv
  · simpa [call1, hs, fanoutComp] using hc1
  · simpa [call2, hs, fanoutComp] using hc2

def canonicalLocalCertificate_cons
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hs : s.state = .cons) (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s (.cons, (inp, pub, dec)))
    (hfaith : ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
      OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves : ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hz : z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hv : Vcomp inp pub dec) {f₁ f₂ : ℕ}
    (heval₁ : FieldEmbedding.evalFBy q f₁
      (s.subformula 0 (by simp [hs, fanoutComp]) .subject)
      (s.subformula 0 (by simp [hs, fanoutComp]) .formula) =
        some (s.subformula 0 (by simp [hs, fanoutComp]) .result))
    (heval₂ : FieldEmbedding.evalFBy q f₂
      (s.subformula 1 (by simp [hs, fanoutComp]) .subject)
      (s.subformula 1 (by simp [hs, fanoutComp]) .formula) =
        some (s.subformula 1 (by simp [hs, fanoutComp]) .result)) :
    LocalOpcodeCertificate q Λ
      (CanonicalRowData hb hop hbind hfaith hleaves) := by
  let data := CanonicalRowData hb hop hbind hfaith hleaves
  let call1 := canonicalCall hbind 0 (by simp [hs, fanoutComp])
  let call2 := canonicalCall hbind 1 (by simp [hs, fanoutComp])
  let fuel := max f₁ f₂
  have hc1 := evalFBy_mono (q := q) (m := fuel) (by simp [fuel]) heval₁
  have hc2 := evalFBy_mono (q := q) (m := fuel) (by simp [fuel]) heval₂
  have hstate : pub.state = .cons := hbind.2.2.1.trans hs
  have hinpz : inp.z = z := hbind.2.1
  have hformula : ComparisonListed data .formulaCons data.root.formula
      (.cell data.root.head data.root.tail) := by
    simp [ComparisonListed, data, P8Census.skeletonComparisons, P8Census.skeletonUse, hs]
  have h1s : ComparisonListed data .recursiveSubject call1.subject data.root.subject := by
    simp [ComparisonListed, data, call1, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h1f : ComparisonListed data .recursiveFormula call1.formula data.root.head := by
    simp [ComparisonListed, data, call1, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h2s : ComparisonListed data .recursiveSubject call2.subject data.root.subject := by
    simp [ComparisonListed, data, call2, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h2f : ComparisonListed data .recursiveFormula call2.formula data.root.tail := by
    simp [ComparisonListed, data, call2, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have hresult : ComparisonListed data .producedResult data.root.result
      (.cell call1.result call2.result) := by
    simp [ComparisonListed, data, call1, call2, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  refine .cons data fuel call1 call2 hstate (hinpz ▸ hz) hcast
    hformula h1s h1f h2s h2f hresult ?_ ?_ hv
  · simpa [call1, hs, fanoutComp] using hc1
  · simpa [call2, hs, fanoutComp] using hc2

def canonicalLocalCertificate_s9
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hs : s.state = .s9) (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s (.s9, (inp, pub, dec)))
    (hfaith : ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
      OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves : ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hz : z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hv : Vcomp inp pub dec) {f₁ f₂ : ℕ}
    (heval₁ : FieldEmbedding.evalFBy q f₁
      (s.subformula 0 (by simp [hs, fanoutComp]) .subject)
      (s.subformula 0 (by simp [hs, fanoutComp]) .formula) =
        some (s.subformula 0 (by simp [hs, fanoutComp]) .result))
    (heval₂ : FieldEmbedding.evalFBy q f₂
      (s.subformula 1 (by simp [hs, fanoutComp]) .subject)
      (s.subformula 1 (by simp [hs, fanoutComp]) .formula) =
        some (s.subformula 1 (by simp [hs, fanoutComp]) .result)) :
    LocalOpcodeCertificate q Λ
      (CanonicalRowData hb hop hbind hfaith hleaves) := by
  let data := CanonicalRowData hb hop hbind hfaith hleaves
  let tail := canonicalTail hbind (by simp [hs, SemanticStrategy.hasTailDecomposition])
  let call1 := canonicalCall hbind 0 (by simp [hs, fanoutComp])
  let call2 := canonicalCall hbind 1 (by simp [hs, fanoutComp])
  let axis := P8Census.skeletonMemoryAxis s 2
  let fuel := max f₁ f₂
  have hc1 := evalFBy_mono (q := q) (m := fuel) (by simp [fuel]) heval₁
  have hc2 := evalFBy_mono (q := q) (m := fuel) (by simp [fuel]) heval₂
  have hstate : pub.state = .s9 := hbind.2.2.1.trans hs
  have hinpz : inp.z = z := hbind.2.1
  have hhead : ComparisonListed data .opcodeHead data.root.head (.atom 9) := by
    simp [ComparisonListed, data, P8Census.skeletonComparisons, P8Census.skeletonUse, hs]
  have hformula : ComparisonListed data .formulaCons data.root.formula
      (.cell data.root.head data.root.tail) := by
    simp [ComparisonListed, data, P8Census.skeletonComparisons, P8Census.skeletonUse, hs]
  have htail : ComparisonListed data .tailCons data.root.tail (.cell tail.head tail.tail) := by
    simp [ComparisonListed, data, tail, P8Census.skeletonComparisons, P8Census.skeletonUse, hs]
  have haxis : ComparisonListed data .axisAtom tail.head (.atom axis) := by
    simp [ComparisonListed, data, tail, axis, P8Census.skeletonComparisons,
      P8Census.skeletonUse, hs]
  have h1s : ComparisonListed data .recursiveSubject call1.subject data.root.subject := by
    simp [ComparisonListed, data, call1, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h1f : ComparisonListed data .recursiveFormula call1.formula tail.tail := by
    simp [ComparisonListed, data, call1, tail, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have h2s : ComparisonListed data .recursiveSubject call2.subject call1.result := by
    simp [ComparisonListed, data, call1, call2, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have hresult : ComparisonListed data .producedResult data.root.result call2.result := by
    simp [ComparisonListed, data, call2, P8Census.skeletonSubformula,
      P8Census.skeletonComparisons, P8Census.skeletonUse, hs, fanoutComp]
  have hmr3 := hbind.2.2.2.2.2.2.2.2 (2 : Fin 3)
  simp [hs, Nock.Framework.recordCount] at hmr3
  have hrecord := hop.s9_record hs
  dsimp only at hrecord
  have hmr' : OpcodeSemantics.RealizesMemRec inp.z pub.mr3
      call1.result call2.formula axis := by
    have hr := hmr3.1
    have hc := hmr3.2.1
    rw [hrecord.1] at hr
    rw [hrecord.2] at hc
    exact
      { root_realizes := by
          change SemanticStrategy.bindFP inp.z call1.result pub.mr3.root
          rw [show call1.result = P8Census.skeletonSubformula s 0 .result by
            simp [call1, P8Census.skeletonSubformula, hs, fanoutComp], hinpz]
          exact hr
        child_realizes := by
          change SemanticStrategy.bindFP inp.z call2.formula pub.mr3.child
          rw [show call2.formula = P8Census.skeletonSubformula s 1 .formula by
            simp [call2, P8Census.skeletonSubformula, hs, fanoutComp], hinpz]
          exact hc
        axis_realizes := by
          simpa [axis, P8Census.skeletonMemoryAxis, hs,
            Nock.Framework.recordCount, computeMemRec] using hmr3.2.2 }
  have hserved : GlobalCarryAxis.ServedLookup
      (GlobalCarryRecognizer.ofNoun call1.result 1) axis call2.formula := by
    simpa [call1, call2, axis, P8Census.skeletonSubformula, hs, fanoutComp] using
      hop.s9_served hs
  refine .s9 data fuel axis tail call1 call2 hstate (hinpz ▸ hz) hcast
    hhead hformula htail haxis h1s h1f h2s hresult hmr' hserved ?_ ?_ hv
  · simpa [call1, hs, fanoutComp] using hc1
  · simpa [call2, hs, fanoutComp] using hc2

inductive S0S5 : State → Type
  | s0 : S0S5 .s0
  | s1 : S0S5 .s1
  | s2 : S0S5 .s2
  | s3 : S0S5 .s3
  | s4 : S0S5 .s4
  | s5 : S0S5 .s5

theorem canonicalLocalCertificate_s0_s5
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {st : State} {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hcovered : S0S5 st)
    (hs : s.state = st)
    (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s (st, (inp, pub, dec)))
    (hfaith : ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
      OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves : ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hz : z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hv : Vcomp inp pub dec)
    (hcalls :
      ∀ (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state),
        ∃ fuel, FieldEmbedding.evalFBy q fuel
          (s.subformula i hi .subject) (s.subformula i hi .formula) =
            some (s.subformula i hi .result)) :
    Nonempty (LocalOpcodeCertificate q Λ
      (CanonicalRowData hb hop hbind hfaith hleaves)) := by
  cases hcovered with
  | s0 =>
    exact ⟨canonicalLocalCertificate_s0 hs hb hop hbind hfaith hleaves
      hz hcast hv⟩
  | s1 =>
    exact ⟨canonicalLocalCertificate_s1 hs hb hop hbind hfaith hleaves
      hz hcast hv⟩
  | s2 =>
    obtain ⟨f₁, h₁⟩ := hcalls 0 (by simp [hs, fanoutComp])
    obtain ⟨f₂, h₂⟩ := hcalls 1 (by simp [hs, fanoutComp])
    obtain ⟨f₃, h₃⟩ := hcalls 2 (by simp [hs, fanoutComp])
    exact ⟨canonicalLocalCertificate_s2 hs hb hop hbind hfaith hleaves
      hz hcast hv h₁ h₂ h₃⟩
  | s3 =>
    obtain ⟨fuel, heval⟩ := hcalls 0 (by simp [hs, fanoutComp])
    exact ⟨canonicalLocalCertificate_s3 hs hb hop hbind hfaith hleaves
      hz hcast hv heval⟩
  | s4 =>
    obtain ⟨fuel, heval⟩ := hcalls 0 (by simp [hs, fanoutComp])
    exact ⟨canonicalLocalCertificate_s4 hs hb hop hbind hfaith hleaves
      hz hcast hv heval⟩
  | s5 =>
    obtain ⟨f₁, h₁⟩ := hcalls 0 (by simp [hs, fanoutComp])
    obtain ⟨f₂, h₂⟩ := hcalls 1 (by simp [hs, fanoutComp])
    exact ⟨canonicalLocalCertificate_s5 hs hb hop hbind hfaith hleaves
      hz hcast hv h₁ h₂⟩

inductive AllState : State → Type
  | s0 : AllState .s0
  | s1 : AllState .s1
  | s2 : AllState .s2
  | s3 : AllState .s3
  | s4 : AllState .s4
  | s5 : AllState .s5
  | s6 : AllState .s6
  | s7 : AllState .s7
  | s8 : AllState .s8
  | s9 : AllState .s9
  | cons : AllState .cons

theorem canonicalLocalCertificate_all
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {st : State} {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hall : AllState st) (hs : s.state = st) (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s (st, (inp, pub, dec)))
    (hfaith : ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
      OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves : ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hz : z ≠ 0) (hq : 1 < q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hv : Vcomp inp pub dec)
    (hcalls : ∀ (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state),
      ∃ fuel, FieldEmbedding.evalFBy q fuel
        (s.subformula i hi .subject) (s.subformula i hi .formula) =
          some (s.subformula i hi .result)) :
    Nonempty (LocalOpcodeCertificate q Λ
      (CanonicalRowData hb hop hbind hfaith hleaves)) := by
  cases hall with
  | s0 => exact ⟨canonicalLocalCertificate_s0 hs hb hop hbind hfaith hleaves hz hcast hv⟩
  | s1 => exact ⟨canonicalLocalCertificate_s1 hs hb hop hbind hfaith hleaves hz hcast hv⟩
  | s2 =>
      obtain ⟨f₁, h₁⟩ := hcalls 0 (by simp [hs, fanoutComp])
      obtain ⟨f₂, h₂⟩ := hcalls 1 (by simp [hs, fanoutComp])
      obtain ⟨f₃, h₃⟩ := hcalls 2 (by simp [hs, fanoutComp])
      exact ⟨canonicalLocalCertificate_s2 hs hb hop hbind hfaith hleaves hz hcast hv h₁ h₂ h₃⟩
  | s3 =>
      obtain ⟨f, h⟩ := hcalls 0 (by simp [hs, fanoutComp])
      exact ⟨canonicalLocalCertificate_s3 hs hb hop hbind hfaith hleaves hz hcast hv h⟩
  | s4 =>
      obtain ⟨f, h⟩ := hcalls 0 (by simp [hs, fanoutComp])
      exact ⟨canonicalLocalCertificate_s4 hs hb hop hbind hfaith hleaves hz hcast hv h⟩
  | s5 =>
      obtain ⟨f₁, h₁⟩ := hcalls 0 (by simp [hs, fanoutComp])
      obtain ⟨f₂, h₂⟩ := hcalls 1 (by simp [hs, fanoutComp])
      exact ⟨canonicalLocalCertificate_s5 hs hb hop hbind hfaith hleaves hz hcast hv h₁ h₂⟩
  | s6 =>
      obtain ⟨f₁, h₁⟩ := hcalls 0 (by simp [hs, fanoutComp])
      obtain ⟨f₂, h₂⟩ := hcalls 1 (by simp [hs, fanoutComp])
      exact ⟨canonicalLocalCertificate_s6 hs hb hop hbind hfaith hleaves hz hq hcast hv h₁ h₂⟩
  | s7 =>
      obtain ⟨f₁, h₁⟩ := hcalls 0 (by simp [hs, fanoutComp])
      obtain ⟨f₂, h₂⟩ := hcalls 1 (by simp [hs, fanoutComp])
      exact ⟨canonicalLocalCertificate_s7 hs hb hop hbind hfaith hleaves hz hcast hv h₁ h₂⟩
  | s8 =>
      obtain ⟨f₁, h₁⟩ := hcalls 0 (by simp [hs, fanoutComp])
      obtain ⟨f₂, h₂⟩ := hcalls 1 (by simp [hs, fanoutComp])
      exact ⟨canonicalLocalCertificate_s8 hs hb hop hbind hfaith hleaves hz hcast hv h₁ h₂⟩
  | s9 =>
      obtain ⟨f₁, h₁⟩ := hcalls 0 (by simp [hs, fanoutComp])
      obtain ⟨f₂, h₂⟩ := hcalls 1 (by simp [hs, fanoutComp])
      exact ⟨canonicalLocalCertificate_s9 hs hb hop hbind hfaith hleaves hz hcast hv h₁ h₂⟩
  | cons =>
      obtain ⟨f₁, h₁⟩ := hcalls 0 (by simp [hs, fanoutComp])
      obtain ⟨f₂, h₂⟩ := hcalls 1 (by simp [hs, fanoutComp])
      exact ⟨canonicalLocalCertificate_cons hs hb hop hbind hfaith hleaves hz hcast hv h₁ h₂⟩

def allStateWitness (st : State) : AllState st :=
  match st with
  | .s0 => .s0
  | .s1 => .s1
  | .s2 => .s2
  | .s3 => .s3
  | .s4 => .s4
  | .s5 => .s5
  | .s6 => .s6
  | .s7 => .s7
  | .s8 => .s8
  | .s9 => .s9
  | .cons => .cons

/-- Canonical certificate dispatcher for every compute state.  Its only recursive inputs are
successful evaluations of the row's actual call slots. -/
theorem canonicalLocalCertificate
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {st : State} {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hs : s.state = st) (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s (st, (inp, pub, dec)))
    (hfaith : ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
      OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves : ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hz : z ≠ 0) (hq : 1 < q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hv : Vcomp inp pub dec)
    (hcalls : ∀ (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state),
      ∃ fuel, FieldEmbedding.evalFBy q fuel
        (s.subformula i hi .subject) (s.subformula i hi .formula) =
          some (s.subformula i hi .result)) :
    Nonempty (LocalOpcodeCertificate q Λ
      (CanonicalRowData hb hop hbind hfaith hleaves)) :=
  canonicalLocalCertificate_all (allStateWitness st) hs hb hop hbind hfaith
    hleaves hz hq hcast hv hcalls

/-- Bottom-up local evaluator step: child evaluator witnesses imply the parent's evaluator
witness, through the canonical certificate and the proved opcode semantics. -/
theorem canonicalRow_evalFBy
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {st : State} {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hs : s.state = st) (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s (st, (inp, pub, dec)))
    (hfaith : ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
      OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves : ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hz : z ≠ 0) (hq : 1 < q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hv : Vcomp inp pub dec)
    (hcalls : ∀ (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state),
      ∃ fuel, FieldEmbedding.evalFBy q fuel
        (s.subformula i hi .subject) (s.subformula i hi .formula) =
          some (s.subformula i hi .result)) :
    ∃ fuel, FieldEmbedding.evalFBy q fuel s.subject s.formula =
      some s.evaluation := by
  obtain ⟨cert⟩ := canonicalLocalCertificate hs hb hop hbind hfaith hleaves
    hz hq hcast hv hcalls
  obtain ⟨fuel, successor, hstep, heval⟩ :=
    LocalOpcodeCertificate.semantics cert
  refine ⟨fuel + 1, ?_⟩
  simpa [canonical_root_subject, canonical_root_formula, canonical_root_result] using heval

/-- Child endpoint selected by a certificate, in structural child-slot order. -/
def expectedChildRoot
    {q Λ : ℕ} {row : State × DTcomp K}
    {data : ComputeRowSemanticData q Λ row}
    (cert : LocalOpcodeCertificate q Λ data) :
    Fin (fanoutComp row.1) → Verb := by
  cases hcert : cert with
  | s0 data fuel axis hstate hz hcast hhead hformula htail hmr hserved hv =>
      exact Fin.elim0
  | s1 data fuel hstate hz hcast hhead hformula hresult hv =>
      exact Fin.elim0
  | s2 data fuel tail call1 call2 call3 hstate hz hcast hhead hformula htail
      h1s h1f h2s h2f h3s h3f hresult hcall1 hcall2 hcall3 hv =>
      exact Fin.cases (Verb.program data.root.subject tail.head)
        (Fin.cases (Verb.program data.root.subject tail.tail)
          (fun _ => Verb.program call1.result call2.result))
  | s3 data fuel call1 hstate hz hcast hhead hformula h1s h1f hresult
      hsize hcall hv =>
      exact (fun _ => Verb.program data.root.subject data.root.tail)
  | s4 data fuel call1 hstate hz hq hcast hhead hformula h1s h1f hresult
      hsize hcall hv =>
      exact (fun _ => Verb.program data.root.subject data.root.tail)
  | s5 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h1s h1f h2s h2f hcompare hresult hcall1 hcall2 hv =>
      exact Fin.cases (Verb.program data.root.subject tail.head)
        (fun _ => Verb.program data.root.subject tail.tail)
  | s6 data fuel tail branch call1 call2 hstate hz hq hcast hhead hformula htail
      hbranch h1s h1fz h1fo h2s h2f hresult hb hw hc1 hc2 hv =>
      exact Fin.cases (Verb.program call1.subject call1.formula)
        (fun _ => Verb.program call2.subject call2.formula)
  | s7 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h2s h2f h1s h1f hresult hc1 hc2 hv =>
      exact Fin.cases (Verb.program call2.result tail.tail)
        (fun _ => Verb.program data.root.subject tail.head)
  | s8 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h2s h2f h1s h1f hresult hc1 hc2 hv =>
      exact Fin.cases (Verb.program (.cell call2.result data.root.subject) tail.tail)
        (fun _ => Verb.program data.root.subject tail.head)
  | s9 data fuel axis tail call1 call2 hstate hz hcast hhead hformula htail
      haxis h1s h1f h2s hresult hmr hserved hc1 hc2 hv =>
      exact Fin.cases (Verb.program data.root.subject tail.tail)
        (fun _ => Verb.program call1.result call2.formula)
  | cons data fuel call1 call2 hstate hz hcast hformula h1s h1f h2s h2f
      hresult hc1 hc2 hv =>
      exact Fin.cases (Verb.program data.root.subject data.root.head)
        (fun _ => Verb.program data.root.subject data.root.tail)

def expectedChildResult
    {q Λ : ℕ} {row : State × DTcomp K}
    {data : ComputeRowSemanticData q Λ row}
    (cert : LocalOpcodeCertificate q Λ data) :
    Fin (fanoutComp row.1) → Noun := by
  cases hcert : cert with
  | s0 data fuel axis hstate hz hcast hhead hformula htail hmr hserved hv =>
      exact Fin.elim0
  | s1 data fuel hstate hz hcast hhead hformula hresult hv =>
      exact Fin.elim0
  | s2 data fuel tail call1 call2 call3 hstate hz hcast hhead hformula htail
      h1s h1f h2s h2f h3s h3f hresult hcall1 hcall2 hcall3 hv =>
      exact Fin.cases call1.result (Fin.cases call2.result (fun _ => call3.result))
  | s3 data fuel call1 hstate hz hcast hhead hformula h1s h1f hresult
      hsize hcall hv => exact fun _ => call1.result
  | s4 data fuel call1 hstate hz hq hcast hhead hformula h1s h1f hresult
      hsize hcall hv => exact fun _ => call1.result
  | s5 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h1s h1f h2s h2f hcompare hresult hcall1 hcall2 hv =>
      exact Fin.cases call1.result (fun _ => call2.result)
  | s6 data fuel tail branch call1 call2 hstate hz hq hcast hhead hformula htail
      hbranch h1s h1fz h1fo h2s h2f hresult hb hw hc1 hc2 hv =>
      exact Fin.cases call1.result (fun _ => call2.result)
  | s7 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h2s h2f h1s h1f hresult hc1 hc2 hv =>
      exact Fin.cases call1.result (fun _ => call2.result)
  | s8 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h2s h2f h1s h1f hresult hc1 hc2 hv =>
      exact Fin.cases call1.result (fun _ => call2.result)
  | s9 data fuel axis tail call1 call2 hstate hz hcast hhead hformula htail
      haxis h1s h1f h2s hresult hmr hserved hc1 hc2 hv =>
      exact Fin.cases call1.result (fun _ => call2.result)
  | cons data fuel call1 call2 hstate hz hcast hformula h1s h1f h2s h2f
      hresult hc1 hc2 hv =>
      exact Fin.cases call1.result (fun _ => call2.result)

/-- State-independent carrier for the at-most-three structural child traces. -/
def CertificateChildren
    {q Λ : ℕ} {row : State × DTcomp K}
    {data : ComputeRowSemanticData q Λ row}
    (cert : LocalOpcodeCertificate q Λ data) (traces : Fin 3 → List Verb) : Prop :=
  match cert with
  | .s0 .. => True
  | .s1 .. => True
  | .s2 data _ tail call1 call2 call3 .. =>
      TraceEndpoint (Verb.program call1.subject call1.formula) call1.result (traces 0) ∧
      TraceEndpoint (Verb.program call2.subject call2.formula) call2.result (traces 1) ∧
      TraceEndpoint (Verb.program call3.subject call3.formula) call3.result (traces 2)
  | .s3 data _ call1 .. =>
      TraceEndpoint (Verb.program call1.subject call1.formula) call1.result (traces 0)
  | .s4 data _ call1 .. =>
      TraceEndpoint (Verb.program call1.subject call1.formula) call1.result (traces 0)
  | .s5 data _ tail call1 call2 .. =>
      TraceEndpoint (Verb.program call1.subject call1.formula) call1.result (traces 0) ∧
      TraceEndpoint (Verb.program call2.subject call2.formula) call2.result (traces 1)
  | .s6 data fuel tail branch call1 call2 .. =>
      TraceEndpoint (Verb.program call1.subject call1.formula) call1.result (traces 0) ∧
      TraceEndpoint (Verb.program call2.subject call2.formula) call2.result (traces 1)
  | .s7 data _ tail call1 call2 .. =>
      TraceEndpoint (Verb.program call1.subject call1.formula) call1.result (traces 0) ∧
      TraceEndpoint (Verb.program call2.subject call2.formula) call2.result (traces 1)
  | .s8 data _ tail call1 call2 .. =>
      TraceEndpoint (Verb.program call1.subject call1.formula) call1.result (traces 0) ∧
      TraceEndpoint (Verb.program call2.subject call2.formula) call2.result (traces 1)
  | .s9 data _ _ tail call1 call2 .. =>
      TraceEndpoint (Verb.program call1.subject call1.formula) call1.result (traces 0) ∧
      TraceEndpoint (Verb.program call2.subject call2.formula) call2.result (traces 1)
  | .cons data _ call1 call2 .. =>
      TraceEndpoint (Verb.program call1.subject call1.formula) call1.result (traces 0) ∧
      TraceEndpoint (Verb.program call2.subject call2.formula) call2.result (traces 1)

private theorem noun_eq_of_listed_realizes
    {q Λ : ℕ} {row : State × DTcomp K}
    {data : ComputeRowSemanticData q Λ row} {role : ComparisonRole}
    {fp₁ fp₂ : FP K} {a b : Noun}
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (h : ComparisonListed data role a b)
    (ha : OpcodeSemantics.Realizes row.2.1.z fp₁ a)
    (hb : OpcodeSemantics.Realizes row.2.1.z fp₂ b)
    (hfp : fp₁ = fp₂) : a = b :=
  OpcodeSemantics.noun_eq_of_realizes_eq ha hb hfp hcast h.faithful

private theorem canonicalCertificateWithChildren
    {q Λ : ℕ} {z : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {st : State} {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hs : s.state = st) (hb : s.BoundedBy q)
    (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hbind : SemanticStrategy.BindComputeRow z s (st, (inp, pub, dec)))
    (hfaith : ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
      OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves : ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hz : z ≠ 0) (hq : 1 < q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hv : Vcomp inp pub dec) (traces : Fin 3 → List Verb)
    (hcalls : ∀ (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state),
      ∃ fuel, FieldEmbedding.evalFBy q fuel
        (s.subformula i hi .subject) (s.subformula i hi .formula) =
          some (s.subformula i hi .result))
    (hends : ∀ (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state),
      TraceEndpoint
        (Verb.program (s.subformula i hi .subject) (s.subformula i hi .formula))
        (s.subformula i hi .result) (traces i)) :
    ∃ cert : LocalOpcodeCertificate q Λ
        (CanonicalRowData hb hop hbind hfaith hleaves),
      CertificateChildren cert traces := by
  cases hall : allStateWitness st with
  | s0 =>
      let cert := canonicalLocalCertificate_s0 hs hb hop hbind hfaith hleaves hz hcast hv
      exact ⟨cert, by simp [cert, CertificateChildren, canonicalLocalCertificate_s0]⟩
  | s1 =>
      let cert := canonicalLocalCertificate_s1 hs hb hop hbind hfaith hleaves hz hcast hv
      exact ⟨cert, by simp [cert, CertificateChildren, canonicalLocalCertificate_s1]⟩
  | s2 =>
      obtain ⟨f₁, h₁⟩ := hcalls 0 (by simp [hs, fanoutComp])
      obtain ⟨f₂, h₂⟩ := hcalls 1 (by simp [hs, fanoutComp])
      obtain ⟨f₃, h₃⟩ := hcalls 2 (by simp [hs, fanoutComp])
      let cert := canonicalLocalCertificate_s2 hs hb hop hbind hfaith hleaves hz hcast hv
        h₁ h₂ h₃
      refine ⟨cert, ?_⟩
      simpa [cert, canonicalLocalCertificate_s2, CertificateChildren, hs, fanoutComp] using
        And.intro (hends 0 (by simp [hs, fanoutComp]))
          (And.intro (hends 1 (by simp [hs, fanoutComp]))
            (hends 2 (by simp [hs, fanoutComp])))
  | s3 =>
      obtain ⟨fuel, heval⟩ := hcalls 0 (by simp [hs, fanoutComp])
      let cert := canonicalLocalCertificate_s3 hs hb hop hbind hfaith hleaves hz hcast hv heval
      refine ⟨cert, ?_⟩
      simpa [cert, canonicalLocalCertificate_s3, CertificateChildren, hs, fanoutComp] using
        hends 0 (by simp [hs, fanoutComp])
  | s4 =>
      obtain ⟨fuel, heval⟩ := hcalls 0 (by simp [hs, fanoutComp])
      let cert := canonicalLocalCertificate_s4 hs hb hop hbind hfaith hleaves hz hcast hv heval
      refine ⟨cert, ?_⟩
      simpa [cert, canonicalLocalCertificate_s4, CertificateChildren, hs, fanoutComp] using
        hends 0 (by simp [hs, fanoutComp])
  | s5 =>
      obtain ⟨f₁, h₁⟩ := hcalls 0 (by simp [hs, fanoutComp])
      obtain ⟨f₂, h₂⟩ := hcalls 1 (by simp [hs, fanoutComp])
      let cert := canonicalLocalCertificate_s5 hs hb hop hbind hfaith hleaves hz hcast hv h₁ h₂
      refine ⟨cert, ?_⟩
      simpa [cert, canonicalLocalCertificate_s5, CertificateChildren, hs, fanoutComp] using
        And.intro (hends 0 (by simp [hs, fanoutComp]))
          (hends 1 (by simp [hs, fanoutComp]))
  | s6 =>
      obtain ⟨f₁, h₁⟩ := hcalls 0 (by simp [hs, fanoutComp])
      obtain ⟨f₂, h₂⟩ := hcalls 1 (by simp [hs, fanoutComp])
      let cert := canonicalLocalCertificate_s6 hs hb hop hbind hfaith hleaves hz hq hcast hv
        h₁ h₂
      refine ⟨cert, ?_⟩
      simpa [cert, canonicalLocalCertificate_s6, CertificateChildren, hs, fanoutComp] using
        And.intro (hends 0 (by simp [hs, fanoutComp]))
          (hends 1 (by simp [hs, fanoutComp]))
  | s7 =>
      obtain ⟨f₁, h₁⟩ := hcalls 0 (by simp [hs, fanoutComp])
      obtain ⟨f₂, h₂⟩ := hcalls 1 (by simp [hs, fanoutComp])
      let cert := canonicalLocalCertificate_s7 hs hb hop hbind hfaith hleaves hz hcast hv h₁ h₂
      refine ⟨cert, ?_⟩
      simpa [cert, canonicalLocalCertificate_s7, CertificateChildren, hs, fanoutComp] using
        And.intro (hends 0 (by simp [hs, fanoutComp]))
          (hends 1 (by simp [hs, fanoutComp]))
  | s8 =>
      obtain ⟨f₁, h₁⟩ := hcalls 0 (by simp [hs, fanoutComp])
      obtain ⟨f₂, h₂⟩ := hcalls 1 (by simp [hs, fanoutComp])
      let cert := canonicalLocalCertificate_s8 hs hb hop hbind hfaith hleaves hz hcast hv h₁ h₂
      refine ⟨cert, ?_⟩
      simpa [cert, canonicalLocalCertificate_s8, CertificateChildren, hs, fanoutComp] using
        And.intro (hends 0 (by simp [hs, fanoutComp]))
          (hends 1 (by simp [hs, fanoutComp]))
  | s9 =>
      obtain ⟨f₁, h₁⟩ := hcalls 0 (by simp [hs, fanoutComp])
      obtain ⟨f₂, h₂⟩ := hcalls 1 (by simp [hs, fanoutComp])
      let cert := canonicalLocalCertificate_s9 hs hb hop hbind hfaith hleaves hz hcast hv h₁ h₂
      refine ⟨cert, ?_⟩
      simpa [cert, canonicalLocalCertificate_s9, CertificateChildren, hs, fanoutComp] using
        And.intro (hends 0 (by simp [hs, fanoutComp]))
          (hends 1 (by simp [hs, fanoutComp]))
  | cons =>
      obtain ⟨f₁, h₁⟩ := hcalls 0 (by simp [hs, fanoutComp])
      obtain ⟨f₂, h₂⟩ := hcalls 1 (by simp [hs, fanoutComp])
      let cert := canonicalLocalCertificate_cons hs hb hop hbind hfaith hleaves hz hcast hv
        h₁ h₂
      refine ⟨cert, ?_⟩
      simpa [cert, canonicalLocalCertificate_cons, CertificateChildren, hs, fanoutComp] using
        And.intro (hends 0 (by simp [hs, fanoutComp]))
          (hends 1 (by simp [hs, fanoutComp]))

/-- The all-state local scheduling dispatcher. -/
theorem assemble_local
    {q Λ : ℕ} {row : State × DTcomp K}
    {data : ComputeRowSemanticData q Λ row}
    (cert : LocalOpcodeCertificate q Λ data)
    (childTrace : Fin 3 → List Verb)
    (hchildren : CertificateChildren cert childTrace) :
    ∃ fuel, FieldEmbedding.evalFBy q fuel data.root.subject data.root.formula =
      some data.root.result := by
  obtain ⟨fuel, _, _, heval⟩ := LocalOpcodeCertificate.semantics cert
  exact ⟨fuel + 1, heval⟩
/-
  cases cert with
  | s0 data fuel axis hstate hz hcast hhead hformula htail hmr hserved hv =>
      let cert := LocalOpcodeCertificate.s0 data fuel axis hstate hz hcast hhead
        hformula htail hmr hserved hv
      obtain ⟨_, hs⟩ := s0_complete_of_certificate cert
      exact ⟨_, ⟨rfl, hs, rfl, Verb.ofNoun_terminal data.root.result⟩⟩
  | s1 data fuel hstate hz hcast hhead hformula hresult hv =>
      let cert := LocalOpcodeCertificate.s1 data fuel hstate hz hcast hhead
        hformula hresult hv
      exact ⟨_, ⟨rfl, s1_complete_of_certificate cert, rfl,
        Verb.ofNoun_terminal data.root.result⟩⟩
  | s2 data fuel tail call1 call2 call3 hstate hz hcast hhead hformula htail
      h1s h1f h2s h2f h3s h3f hresult hcall1 hcall2 hcall3 hv =>
      let cert := LocalOpcodeCertificate.s2 data fuel tail call1 call2 call3 hstate hz
        hcast hhead hformula htail h1s h1f h2s h2f h3s h3f hresult
        hcall1 hcall2 hcall3 hv
      have hc :
          TraceEndpoint (Verb.program call1.subject call1.formula) call1.result (childTrace 0) ∧
          TraceEndpoint (Verb.program call2.subject call2.formula) call2.result (childTrace 1) ∧
          TraceEndpoint (Verb.program call3.subject call3.formula) call3.result (childTrace 2) := by
        simpa [CertificateChildren] using hchildren
      have hv' := hv
      obtain ⟨_, _, _, _, heval⟩ := hv'
      simp only [evalV, hstate] at heval
      obtain ⟨he1s, he1f, he2s, he2f, he3s, he3f, _⟩ := heval
      have e1s := noun_eq_of_listed_realizes hcast h1s call1.subject_realizes
        data.root.subject_realizes he1s
      have e1f := noun_eq_of_listed_realizes hcast h1f call1.formula_realizes
        tail.head_realizes he1f
      have e2s := noun_eq_of_listed_realizes hcast h2s call2.subject_realizes
        data.root.subject_realizes he2s
      have e2f := noun_eq_of_listed_realizes hcast h2f call2.formula_realizes
        tail.tail_realizes he2f
      have e3s := noun_eq_of_listed_realizes hcast h3s call3.subject_realizes
        call1.result_realizes he3s
      have e3f := noun_eq_of_listed_realizes hcast h3f call3.formula_realizes
        call2.result_realizes he3f
      apply s2_complete_of_certificate_and_children cert childTrace
      intro i
      fin_cases i
      · change TraceEndpoint (Verb.program data.root.subject tail.head)
          call1.result (childTrace 0)
        simpa [e1s, e1f] using hc.1
      · change TraceEndpoint (Verb.program data.root.subject tail.tail)
          call2.result (childTrace 1)
        simpa [e2s, e2f] using hc.2.1
      · change TraceEndpoint (Verb.program call1.result call2.result)
          call3.result (childTrace 2)
        simpa [e3s, e3f] using hc.2.2
  | s3 data fuel call1 hstate hz hcast hhead hformula h1s h1f hresult hsize hcall hv =>
      let cert := LocalOpcodeCertificate.s3 data fuel call1 hstate hz hcast hhead
        hformula h1s h1f hresult hsize hcall hv
      have hc : TraceEndpoint (Verb.program call1.subject call1.formula)
          call1.result (childTrace 0) := by
        simpa [CertificateChildren] using hchildren
      have hv' := hv
      obtain ⟨_, _, _, _, heval⟩ := hv'
      simp only [evalV, hstate] at heval
      have es := noun_eq_of_listed_realizes hcast h1s call1.subject_realizes
        data.root.subject_realizes heval.1
      have ef := noun_eq_of_listed_realizes hcast h1f call1.formula_realizes
        data.root.tail_realizes heval.2.1
      obtain ⟨trace, ht, hl⟩ := s3_complete_of_certificate_and_children cert
        (by simpa [es, ef] using hc.1) (by simpa [s3ChildResult] using hc.2)
      exact ⟨trace, maximalDFSTrace_of_traceOfROM ht hl⟩
  | s4 data fuel call1 hstate hz hq hcast hhead hformula h1s h1f hresult hsize hcall hv =>
      let cert := LocalOpcodeCertificate.s4 data fuel call1 hstate hz hq hcast hhead
        hformula h1s h1f hresult hsize hcall hv
      have hc : TraceEndpoint (Verb.program call1.subject call1.formula)
          call1.result (childTrace 0) := by
        simpa [CertificateChildren] using hchildren
      have hv' := hv
      obtain ⟨_, _, _, _, heval⟩ := hv'
      simp only [evalV, hstate] at heval
      have es := noun_eq_of_listed_realizes hcast h1s call1.subject_realizes
        data.root.subject_realizes heval.1
      have ef := noun_eq_of_listed_realizes hcast h1f call1.formula_realizes
        data.root.tail_realizes heval.2.1
      obtain ⟨trace, ht, hl⟩ := s4_complete_of_certificate_and_children cert
        (by simpa [es, ef] using hc.1) (by simpa [s4ChildResult] using hc.2)
      exact ⟨trace, maximalDFSTrace_of_traceOfROM ht hl⟩
  | s5 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h1s h1f h2s h2f hcompare hresult hcall1 hcall2 hv =>
      let cert := LocalOpcodeCertificate.s5 data fuel tail call1 call2 hstate hz hcast
        hhead hformula htail h1s h1f h2s h2f hcompare hresult hcall1 hcall2 hv
      have hc :
          TraceEndpoint (Verb.program call1.subject call1.formula) call1.result (childTrace 0) ∧
          TraceEndpoint (Verb.program call2.subject call2.formula) call2.result (childTrace 1) := by
        simpa [CertificateChildren] using hchildren
      have hv' := hv
      obtain ⟨_, _, _, _, heval⟩ := hv'
      simp only [evalV, hstate] at heval
      have he1s := heval.1
      have he1f := heval.2.1
      have he2s := heval.2.2.1
      have he2f := heval.2.2.2.1
      have e1s := noun_eq_of_listed_realizes hcast h1s call1.subject_realizes
        data.root.subject_realizes he1s
      have e1f := noun_eq_of_listed_realizes hcast h1f call1.formula_realizes
        tail.head_realizes he1f
      have e2s := noun_eq_of_listed_realizes hcast h2s call2.subject_realizes
        data.root.subject_realizes he2s
      have e2f := noun_eq_of_listed_realizes hcast h2f call2.formula_realizes
        tail.tail_realizes he2f
      obtain ⟨trace, ht, hl⟩ := s5_complete_of_certificate_and_children cert
        (by
          change Verb.TraceOfROM (Verb.program data.root.subject tail.head) (childTrace 0)
          simpa [e1s, e1f] using hc.1.1)
        (by simpa [s5LeftResult] using hc.1.2)
        (by
          change Verb.TraceOfROM (Verb.program data.root.subject tail.tail) (childTrace 1)
          simpa [e2s, e2f] using hc.2.1)
        (by simpa [s5RightResult] using hc.2.2)
      exact ⟨trace, maximalDFSTrace_of_traceOfROM ht hl⟩
  | s6 data fuel tail branch call1 call2 hstate hz hq hcast hhead hformula htail
      hbranch h1s h1fz h1fo h2s h2f hresult hb hw hc1 hc2 hv =>
      let cert := LocalOpcodeCertificate.s6 data fuel tail branch call1 call2 hstate hz hq
        hcast hhead hformula htail hbranch h1s h1fz h1fo h2s h2f hresult hb hw hc1 hc2 hv
      have hc :
          TraceEndpoint (Verb.program call1.subject call1.formula) call1.result (childTrace 0) ∧
          TraceEndpoint (Verb.program call2.subject call2.formula) call2.result (childTrace 1) := by
        simpa [CertificateChildren] using hchildren
      let traces : Fin 2 → List Verb := Fin.cases (childTrace 0) (fun _ => childTrace 1)
      apply s6_complete_of_certificate_and_children cert traces
      intro i
      fin_cases i
      · change TraceEndpoint (Verb.program call1.subject call1.formula)
          call1.result (childTrace 0)
        exact hc.1
      · change TraceEndpoint (Verb.program call2.subject call2.formula)
          call2.result (childTrace 1)
        exact hc.2
  | s7 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h2s h2f h1s h1f hresult hc1 hc2 hv =>
      let cert := LocalOpcodeCertificate.s7 data fuel tail call1 call2 hstate hz hcast
        hhead hformula htail h2s h2f h1s h1f hresult hc1 hc2 hv
      have hc :
          TraceEndpoint (Verb.program call1.subject call1.formula) call1.result (childTrace 0) ∧
          TraceEndpoint (Verb.program call2.subject call2.formula) call2.result (childTrace 1) := by
        simpa [CertificateChildren] using hchildren
      have hv' := hv
      obtain ⟨_, _, _, _, heval⟩ := hv'
      simp only [evalV, hstate] at heval
      obtain ⟨he1s, he1f, _, he2s, he2f, _⟩ := heval
      have e1s := noun_eq_of_listed_realizes hcast h1s call1.subject_realizes
        call2.result_realizes he1s
      have e1f := noun_eq_of_listed_realizes hcast h1f call1.formula_realizes
        tail.tail_realizes he1f
      have e2s := noun_eq_of_listed_realizes hcast h2s call2.subject_realizes
        data.root.subject_realizes he2s
      have e2f := noun_eq_of_listed_realizes hcast h2f call2.formula_realizes
        tail.head_realizes he2f
      obtain ⟨trace, ht, hl⟩ := s7_complete_of_certificate_and_children cert
        (by simpa [s7SecondFormula, e2s, e2f] using hc.2.1)
        (by simpa [s7SecondResult] using hc.2.2)
        (by simpa [s7FirstFormula, s7SecondResult, e1s, e1f] using hc.1.1)
        (by simpa [s7FirstResult] using hc.1.2)
      exact ⟨trace, maximalDFSTrace_of_traceOfROM ht hl⟩
  | @s8 inp pub dec data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h2s h2f h1s h1f hresult hc1 hc2 hv =>
      let cert := LocalOpcodeCertificate.s8 data fuel tail call1 call2 hstate hz hcast
        hhead hformula htail h2s h2f h1s h1f hresult hc1 hc2 hv
      have hc :
          TraceEndpoint (Verb.program call1.subject call1.formula) call1.result (childTrace 0) ∧
          TraceEndpoint (Verb.program call2.subject call2.formula) call2.result (childTrace 1) := by
        simpa [CertificateChildren] using hchildren
      have hv' := hv
      obtain ⟨_, _, _, _, heval⟩ := hv'
      simp only [evalV, hstate] at heval
      obtain ⟨he1s, he1f, _, he2s, he2f, _⟩ := heval
      have e1s : call1.subject =.cell call2.result data.root.subject := by
        apply OpcodeSemantics.cell_eq_of_cons_encoding hz hcast
          call1.subject call2.result data.root.subject h1s.faithful
        calc
          FP.cons inp.z (OpcodeSemantics.enc inp.z call2.result)
              (OpcodeSemantics.enc inp.z data.root.subject) =
              FP.cons inp.z pub.sf2_e pub.s := by
                rw [← call2.result_realizes, ← data.root.subject_realizes]
          _ = pub.sf1_s := he1s.symm
          _ = OpcodeSemantics.enc inp.z call1.subject := call1.subject_realizes
      have e1f := noun_eq_of_listed_realizes hcast h1f call1.formula_realizes
        tail.tail_realizes he1f
      have e2s := noun_eq_of_listed_realizes hcast h2s call2.subject_realizes
        data.root.subject_realizes he2s
      have e2f := noun_eq_of_listed_realizes hcast h2f call2.formula_realizes
        tail.head_realizes he2f
      let traces : Fin 2 → List Verb := Fin.cases (childTrace 0) (fun _ => childTrace 1)
      apply s8_complete_of_certificate_and_children cert traces
      intro i
      fin_cases i
      · change TraceEndpoint
          (Verb.program (.cell call2.result data.root.subject) tail.tail)
          call1.result (childTrace 0)
        simpa [e1s, e1f] using hc.1
      · change TraceEndpoint (Verb.program data.root.subject tail.head)
          call2.result (childTrace 1)
        simpa [e2s, e2f] using hc.2
  | s9 data fuel axis tail call1 call2 hstate hz hcast hhead hformula htail
      haxis h1s h1f h2s hresult hmr hserved hc1 hc2 hv =>
      let cert := LocalOpcodeCertificate.s9 data fuel axis tail call1 call2 hstate hz
        hcast hhead hformula htail haxis h1s h1f h2s hresult hmr hserved hc1 hc2 hv
      have hc :
          TraceEndpoint (Verb.program call1.subject call1.formula) call1.result (childTrace 0) ∧
          TraceEndpoint (Verb.program call2.subject call2.formula) call2.result (childTrace 1) := by
        simpa [CertificateChildren] using hchildren
      have hv' := hv
      obtain ⟨_, _, _, _, heval⟩ := hv'
      simp only [evalV, hstate] at heval
      obtain ⟨he1s, he1f, he2s, _, _, _, _⟩ := heval
      have e1s := noun_eq_of_listed_realizes hcast h1s call1.subject_realizes
        data.root.subject_realizes he1s
      have e1f := noun_eq_of_listed_realizes hcast h1f call1.formula_realizes
        tail.tail_realizes he1f
      have e2s := noun_eq_of_listed_realizes hcast h2s call2.subject_realizes
        call1.result_realizes he2s
      let traces : Fin 2 → List Verb := Fin.cases (childTrace 0) (fun _ => childTrace 1)
      apply s9_complete_of_certificate_and_children cert traces
      intro i
      fin_cases i
      · change TraceEndpoint (Verb.program data.root.subject tail.tail)
          call1.result (childTrace 0)
        simpa [e1s, e1f] using hc.1
      · change TraceEndpoint (Verb.program call1.result call2.formula)
          call2.result (childTrace 1)
        simpa [e2s] using hc.2
  | cons data fuel call1 call2 hstate hz hcast hformula h1s h1f h2s h2f
      hresult hc1 hc2 hv =>
      let cert := LocalOpcodeCertificate.cons data fuel call1 call2 hstate hz hcast
        hformula h1s h1f h2s h2f hresult hc1 hc2 hv
      have hc :
          TraceEndpoint (Verb.program call1.subject call1.formula) call1.result
              (childTrace 0) ∧
          TraceEndpoint (Verb.program call2.subject call2.formula) call2.result
              (childTrace 1) := by
        simpa [CertificateChildren] using hchildren
      have hv' := hv
      obtain ⟨_, _, _, _, heval⟩ := hv'
      simp only [evalV, hstate] at heval
      obtain ⟨he1s, he1f, he2s, he2f, _, _⟩ := heval
      have e1s := noun_eq_of_listed_realizes hcast h1s call1.subject_realizes
        data.root.subject_realizes he1s
      have e1f := noun_eq_of_listed_realizes hcast h1f call1.formula_realizes
        data.root.head_realizes he1f
      have e2s := noun_eq_of_listed_realizes hcast h2s call2.subject_realizes
        data.root.subject_realizes he2s
      have e2f := noun_eq_of_listed_realizes hcast h2f call2.formula_realizes
        data.root.tail_realizes he2f
      obtain ⟨trace, ht, hl⟩ := cons_complete_of_certificate_and_children cert
        (by simpa [e1s, e1f] using hc.1.1) (by simpa [consLeftResult] using hc.1.2)
        (by simpa [e2s, e2f] using hc.2.1) (by simpa [consRightResult] using hc.2.2)
      exact ⟨trace, maximalDFSTrace_of_traceOfROM ht hl⟩
-/

/-- Entirely pre-evaluator input for bottom-up recursion.  It mirrors `ComputeTreeBinds`, adding
only bounded canonical-row premises and raw row acceptance. -/
inductive CanonicalTreePremises (q Λ : ℕ) (z : K) :
    NTree SemanticStrategy.ComputeRowSkeleton →
      NTree (State × DTcomp K) → Prop
  | node {s sc row rc}
      (shape : sc.length = fanoutComp s.state)
      (hb : s.BoundedBy q)
      (hop : BoundSemanticTrace.SkeletonOperationalPremises q z s)
      (hbind : SemanticStrategy.BindComputeRow z s row)
      (hfaith : ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
      (hleaves : ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
      (hv : Vcomp row.2.1 row.2.2.1 row.2.2.2)
      (children : List.Forall₂ (CanonicalTreePremises q Λ z) sc rc) :
      CanonicalTreePremises q Λ z (.node s sc) (.node row rc)

def NodeSchedulingConclusion (q : ℕ)
    (s : SemanticStrategy.ComputeRowSkeleton) : Prop :=
  ∃ fuel, FieldEmbedding.evalFBy q fuel s.subject s.formula = some s.evaluation

private theorem canonicalTree_bottomUp_aux
    {q Λ : ℕ} {z : K} (hz : z ≠ 0) (hq : 1 < q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    {whole : NTree SemanticStrategy.ComputeRowSkeleton}
    (hcoherent : ChildSkeletonCoherence whole) :
    ∀ stree, InTree whole stree →
      ∀ etree, CanonicalTreePremises q Λ z stree etree →
        NodeSchedulingConclusion q stree.label := by
  intro stree
  refine NTree.rec
    (motive_1 := fun stree =>
      InTree whole stree →
        ∀ etree, CanonicalTreePremises q Λ z stree etree →
          NodeSchedulingConclusion q stree.label)
    (motive_2 := fun trees =>
      ∀ stree ∈ trees, InTree whole stree →
        ∀ etree, CanonicalTreePremises q Λ z stree etree →
          NodeSchedulingConclusion q stree.label)
    ?_ ?_ ?_ stree
  · intro s sc ih hnode etree hprem
    cases etree with
    | node row rc =>
      cases hprem with
      | @node _ _ _ _ shape hb hop hbind hfaith hleaves hv children =>
        have childSlot (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state) :
            ∃ fuel, FieldEmbedding.evalFBy q fuel
              (s.subformula i hi .subject) (s.subformula i hi .formula) =
                some (s.subformula i hi .result) := by
          have hil : (i : ℕ) < sc.length := by simpa [shape] using hi
          have hir : (i : ℕ) < rc.length := by
            simpa [children.length_eq] using hil
          let schild := sc[i]
          let echild := rc[i]
          have hsMem : schild ∈ sc := List.get_mem sc ⟨i, hil⟩
          have hsIn : InTree whole schild :=
            InTree_trans hnode (InTree.sub hsMem (InTree.here schild))
          have hcp : CanonicalTreePremises q Λ z schild echild :=
            children.get hil hir
          obtain ⟨fuel, heval⟩ := ih schild hsMem hsIn echild hcp
          have hopt : (NTree.node s sc).childOpt i = some schild := by
            change sc[i]? = some sc[i]
            exact List.getElem?_eq_some_iff.mpr ⟨hil, rfl⟩
          have hc := hcoherent (.node s sc) hnode i hi schild hopt
          rw [hc.1, hc.2.1, hc.2.2] at heval
          exact ⟨fuel, heval⟩
        rcases row with ⟨st, inp, pub, dec⟩
        have hs : s.state = st := hbind.1.symm
        exact canonicalRow_evalFBy hs hb hop hbind hfaith hleaves
          hz hq hcast hv childSlot
  · intro stree hmem
    simp at hmem
  · intro head tail ihHead ihTail stree hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact ihHead
    · exact ihTail stree hmem
/-
  intro stree
  refine NTree.rec
    (motive_1 := fun stree =>
      InTree whole stree →
        ∀ etree, CanonicalTreePremises q Λ z stree etree →
          NodeSchedulingConclusion q stree.label)
    (motive_2 := fun trees =>
      ∀ stree ∈ trees, InTree whole stree →
        ∀ etree, CanonicalTreePremises q Λ z stree etree →
          NodeSchedulingConclusion q stree.label)
    ?_ ?_ ?_ stree
  · intro s sc ih
    · intro hnode etree hprem
      cases etree with
      | node row rc =>
        cases hprem with
        | @node _ _ _ _ shape hb hop hbind hfaith hleaves hv children =>
          have childSlot (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state) :
              ∃ trace,
                MaximalDFSTrace
                  (Verb.program (s.subformula i hi.subject)
                    (s.subformula i hi.formula))
                  (s.subformula i hi.result) trace ∧
                ∃ fuel, FieldEmbedding.evalFBy q fuel
                  (s.subformula i hi.subject) (s.subformula i hi.formula) =
                    some (s.subformula i hi.result) := by
            have hil : (i : ℕ) < sc.length := by simpa [shape] using hi
            have hir : (i : ℕ) < rc.length := by
              simpa [children.length_eq] using hil
            let schild := sc[i]
            let echild := rc[i]
            have hsMem : schild ∈ sc := List.get_mem sc ⟨i, hil⟩
            have hsIn : InTree whole schild :=
              InTree_trans hnode (InTree.sub hsMem (InTree.here schild))
            have hcp : CanonicalTreePremises q Λ z schild echild :=
              children.get hil hir
            obtain ⟨trace, htrace, fuel, heval⟩ :=
              ih schild hsMem hsIn echild hcp
            have hopt : (NTree.node s sc).childOpt i = some schild := by
              change sc[i]? = some sc[i]
              exact List.getElem?_eq_some_iff.mpr ⟨hil, rfl⟩
            have hc := hcoherent (.node s sc) hnode i hi schild hopt
            rw [hc.1, hc.2.1, hc.2.2] at htrace heval
            refine ⟨trace, ?_, fuel, ?_⟩
            · exact htrace
            · exact heval
          let traces : Fin 3 → List Verb := fun i =>
            if hi : (i : ℕ) < fanoutComp s.state
            then Classical.choose (childSlot i hi)
            else []
          have hends (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state) :
              TraceEndpoint
                (Verb.program (s.subformula i hi.subject)
                  (s.subformula i hi.formula))
                (s.subformula i hi.result) (traces i) := by
            have hs := Classical.choose_spec (childSlot i hi)
            simpa [traces, hi] using MaximalDFSTrace.toEndpoint hs.1
          have hcalls (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state) :
              ∃ fuel, FieldEmbedding.evalFBy q fuel
                (s.subformula i hi.subject) (s.subformula i hi.formula) =
                  some (s.subformula i hi.result) :=
            (Classical.choose_spec (childSlot i hi)).2
          rcases row with ⟨st, inp, pub, dec⟩
          have hs : s.state = st := hbind.1.symm
          obtain ⟨cert, hcertChildren⟩ :=
            canonicalCertificateWithChildren hs hb hop hbind hfaith hleaves
              hz hq hcast hv traces hcalls hends
          obtain ⟨trace, htrace⟩ := assemble_local cert traces hcertChildren
          obtain ⟨fuel, successor, hstep, heval⟩ :=
            LocalOpcodeCertificate.semantics cert
          refine ⟨trace, ?_, fuel + 1, ?_⟩
          · simpa [canonical_root_subject, canonical_root_formula,
              canonical_root_result] using htrace
          · simpa [canonical_root_subject, canonical_root_formula,
              canonical_root_result] using heval
  · intro stree hmem
    simp at hmem
  · intro head tail ihHead ihTail stree hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact ihHead
    · exact ihTail stree hmem
-/

/-- Structural simultaneous bottom-up theorem.  The induction is the native `NTree.rec`;
there is no well-founded measure or evaluator premise. -/
theorem canonicalTree_bottomUp
    {q Λ : ℕ} {z : K} (hz : z ≠ 0) (hq : 1 < q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    {stree : NTree SemanticStrategy.ComputeRowSkeleton}
    {etree : NTree (State × DTcomp K)}
    (hcoherent : ChildSkeletonCoherence stree)
    (hprem : CanonicalTreePremises q Λ z stree etree) :
    NodeSchedulingConclusion q stree.label :=
  canonicalTree_bottomUp_aux hz hq hcast hcoherent stree (InTree.here stree) etree hprem

theorem canonicalTree_evalFBy
    {q Λ : ℕ} {z : K} (hz : z ≠ 0) (hq : 1 < q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    {stree : NTree SemanticStrategy.ComputeRowSkeleton}
    {etree : NTree (State × DTcomp K)}
    (hcoherent : ChildSkeletonCoherence stree)
    (hprem : CanonicalTreePremises q Λ z stree etree) :
    ∃ fuel, FieldEmbedding.evalFBy q fuel stree.label.subject stree.label.formula =
      some stree.label.evaluation := by
  exact canonicalTree_bottomUp hz hq hcast hcoherent hprem

/-- Final collision-closed capstone in an explicit skeleton/config/execution/binding context. -/
theorem bareCensus_bottomUp
    [Fintype K] [DecidableEq K]
    (S : SemanticStrategy.SemanticSkeleton)
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) (z : K)
    (binds : SemanticStrategy.BindsAt z S cfg exec)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K S Λ)
    {q : ℕ} (hz : z ≠ 0) (hq : 1 < q)
    (hb : S.BoundedBy q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (htopology : RVTWithArity (Fcomp (K := K)) exec.computeTree)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (hprem : CanonicalTreePremises q Λ z S.computeTree exec.computeTree) :
    NodeSchedulingConclusion q S.computeTree.label :=
  canonicalTree_bottomUp hz hq hcast
    (childSkeletonCoherence_of_bareCensus S exec z binds C hb hcast htopology hgood)
    hprem

theorem bareCensus_evalFBy
    [Fintype K] [DecidableEq K]
    (S : SemanticStrategy.SemanticSkeleton)
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) (z : K)
    (binds : SemanticStrategy.BindsAt z S cfg exec)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K S Λ)
    {q : ℕ} (hz : z ≠ 0) (hq : 1 < q)
    (hb : S.BoundedBy q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (htopology : RVTWithArity (Fcomp (K := K)) exec.computeTree)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (hprem : CanonicalTreePremises q Λ z S.computeTree exec.computeTree) :
    ∃ fuel, FieldEmbedding.evalFBy q fuel
      S.computeTree.label.subject S.computeTree.label.formula =
      some S.computeTree.label.evaluation := by
  exact bareCensus_bottomUp S exec z binds C hz hq hb hcast htopology hgood hprem

/-- Final collision-closed production capstone.  Child coherence is derived internally from the
single combined pre-seed census. -/
theorem combinedCensus_bottomUp
    [Fintype K] [DecidableEq K]
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (C : EdgeComparisonCensus.CombinedBoundCensus T Λ)
    (z : K) (hz : z ≠ 0) {q : ℕ} (hq : 1 < q)
    (hb : T.skeleton.BoundedBy q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (htopology : RVTWithArity (Fcomp (K := K))
      (P8Census.boundSampledExec T z hz).computeTree)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (hprem : CanonicalTreePremises q Λ z T.skeleton.computeTree
      (P8Census.boundSampledExec T z hz).computeTree) :
    NodeSchedulingConclusion q T.skeleton.computeTree.label :=
  canonicalTree_bottomUp hz hq hcast
    (childSkeletonCoherence_of_fixedCensus T C z hz hb hcast htopology hgood) hprem

theorem combinedCensus_evalFBy
    [Fintype K] [DecidableEq K]
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (C : EdgeComparisonCensus.CombinedBoundCensus T Λ)
    (z : K) (hz : z ≠ 0) {q : ℕ} (hq : 1 < q)
    (hb : T.skeleton.BoundedBy q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (htopology : RVTWithArity (Fcomp (K := K))
      (P8Census.boundSampledExec T z hz).computeTree)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (hprem : CanonicalTreePremises q Λ z T.skeleton.computeTree
      (P8Census.boundSampledExec T z hz).computeTree) :
    ∃ fuel, FieldEmbedding.evalFBy q fuel T.skeleton.computeTree.label.subject
      T.skeleton.computeTree.label.formula =
        some T.skeleton.computeTree.label.evaluation := by
  exact combinedCensus_bottomUp T C z hz hq hb hcast htopology hgood hprem

/-- Exact simultaneous production target. -/
def BottomUpGlobalSchedulingConclusion
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (data : ExactExecutionSemanticData q Λ cfg exec) : Prop :=
  let root := data.rows (rootRowIndex cfg)
  ∃ fuel, FieldEmbedding.evalFBy q fuel
    root.root.subject root.root.formula = some root.root.result

end

end Nock.NockVMROM.Thm54.GlobalOpcodeScheduling

#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.child_count_of_Fcomp
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.actual_child_identifies_call_slot
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.exists_computeRowIndex_of_inTree
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.evalN_of_maximalDFSTrace
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.evalFBy_mono
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.evalFBy_commonFuel₃
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.childSkeletonCoherence_of_fixedCensus
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.canonicalLocalCertificate_s2
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.canonicalLocalCertificate_s3
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.canonicalLocalCertificate_s4
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.canonicalLocalCertificate_s5
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.canonicalLocalCertificate_s0_s5
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.canonicalLocalCertificate_s6
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.canonicalLocalCertificate_s7
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.canonicalLocalCertificate_s8
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.canonicalLocalCertificate_s9
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.canonicalLocalCertificate_cons
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.canonicalLocalCertificate
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.canonicalRow_evalFBy
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.canonicalTree_bottomUp
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.canonicalTree_evalFBy
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.bareCensus_bottomUp
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.bareCensus_evalFBy
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.combinedCensus_bottomUp
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.combinedCensus_evalFBy
#check Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.canonicalTree_bottomUp
#check Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.canonicalTree_evalFBy
#check Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.combinedCensus_bottomUp
#check Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.combinedCensus_evalFBy
