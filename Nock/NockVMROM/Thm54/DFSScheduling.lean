import Nock.NockVMROM.Thm54.OpcodeSemantics
import Nock.NockVMROM.Thm54.ExactTraversal

/-!
# Maximal-DFS scheduling for global ROM traces

`OpcodeSemantics` proves the first `StepROM` of each realized compute row and a separate
`evalFBy` equation.  A global execution additionally has to schedule every recursive call in the
exact order selected by `Verb.getIndex`: the largest pending DFS-preorder index.

This file separates local scheduling laws from the global target.  `SelectedROMRewrite` is the
data inspected by `nextROM` (maximal index, selected subverb, successful local ROM reduction, and
the frame-preserving splice), and the contextual relations state the precise extra obligation
needed to lift a child schedule through `replaceAt`.  `DFSSchedule` is the edge-by-edge list
closure.  The later `TreeDFSSchedule` explicitly stores such a root schedule and is labeled only
as a target/specification, never as something constructed from row-local facts.
-/

namespace Nock.NockVMROM.Thm54.DFSScheduling

open Nock Nock.Walk
open Nock.Verb

/-! ## Exact selected-rewrite interface -/

/-- One explicit maximal-DFS ROM rewrite.

Unlike `StepROM`, the witness retains the selected DFS index and the local `reduceROM` equation.
Thus this is usable as scheduling data rather than as an opaque transition hypothesis. -/
def SelectedROMRewrite (before after : Verb) : Prop :=
  ∃ i sub replacement,
    IsMaxPending dfsLt before i ∧
    Verb.map i before = some sub ∧
    inDomain sub = true ∧
    reduceROM sub = some replacement ∧
    after = replaceAt i before replacement

/-- The explicit selected-rewrite interface is exactly one `nextROM` step. -/
theorem selectedROMRewrite_iff_stepROM {before after : Verb} :
    SelectedROMRewrite before after ↔ StepROM before after := by
  constructor
  · rintro ⟨i, sub, replacement, hmax, hmap, hdom, hreduce, rfl⟩
    unfold StepROM nextROM
    simp [getIndex_eq_some_iff.mpr hmax, hmap, hdom, hreduce]
  · intro h
    unfold StepROM nextROM at h
    cases hindex : getIndex before with
    | none =>
        simp only [hindex] at h
        contradiction
    | some i =>
        simp only [hindex] at h
        cases hmap : Verb.map i before with
        | none =>
            simp only [hmap] at h
            contradiction
        | some sub =>
            simp only [hmap] at h
            by_cases hdom : inDomain sub = true
            · simp only [if_pos hdom] at h
              cases hreduce : reduceROM sub with
              | none =>
                  simp only [hreduce] at h
                  contradiction
              | some replacement =>
                  simp only [hreduce, Option.some.injEq] at h
                  exact ⟨i, sub, replacement, getIndex_eq_some_iff.mp hindex,
                    hmap, hdom, hreduce, h.symm⟩
            · simp only [if_neg hdom] at h
              contradiction

/-- Construct a ROM step directly from the selected maximal site and its local rewrite. -/
theorem stepROM_replaceAt_of_maximalDFS
    {parent sub replacement : Verb} {i : ℕ}
    (hmax : IsMaxPending dfsLt parent i)
    (hmap : Verb.map i parent = some sub)
    (hdom : inDomain sub = true)
    (hreduce : reduceROM sub = some replacement) :
    StepROM parent (replaceAt i parent replacement) :=
  selectedROMRewrite_iff_stepROM.mp
    ⟨i, sub, replacement, hmax, hmap, hdom, hreduce, rfl⟩

/-- `getIndex`-oriented form of `stepROM_replaceAt_of_maximalDFS`. -/
theorem stepROM_replaceAt_of_getIndex
    {parent sub replacement : Verb} {i : ℕ}
    (hindex : getIndex parent = some i)
    (hmap : Verb.map i parent = some sub)
    (hdom : inDomain sub = true)
    (hreduce : reduceROM sub = some replacement) :
    StepROM parent (replaceAt i parent replacement) :=
  stepROM_replaceAt_of_maximalDFS
    (getIndex_eq_some_iff.mp hindex) hmap hdom hreduce

/-! ## Explicit schedules and trace concatenation -/

/-- A list is scheduled by the actual maximal-DFS ROM rule at every adjacent pair. -/
def DFSSchedule (trace : List Verb) : Prop :=
  ConsistentR SelectedROMRewrite trace

/-- An explicit maximal-DFS schedule is a ROM-consistent list. -/
theorem consistentROM_of_dfsSchedule :
    ∀ {trace : List Verb}, DFSSchedule trace → ConsistentR StepROM trace
  | [], _ => trivial
  | [_], _ => trivial
  | before :: after :: rest, h =>
      ⟨selectedROMRewrite_iff_stepROM.mp h.1,
        consistentROM_of_dfsSchedule h.2⟩

/-- Every ROM-consistent list can be unpacked into its exact selected-rewrite witnesses. -/
theorem dfsSchedule_of_consistentROM :
    ∀ {trace : List Verb}, ConsistentR StepROM trace → DFSSchedule trace
  | [], _ => trivial
  | [_], _ => trivial
  | before :: after :: rest, h =>
      ⟨selectedROMRewrite_iff_stepROM.mpr h.1,
        dfsSchedule_of_consistentROM h.2⟩

theorem dfsSchedule_iff_consistentROM {trace : List Verb} :
    DFSSchedule trace ↔ ConsistentR StepROM trace :=
  ⟨consistentROM_of_dfsSchedule, dfsSchedule_of_consistentROM⟩

/-- Prefixing one selected rewrite to a scheduled tail preserves scheduling. -/
theorem DFSSchedule.cons {before after : Verb} {rest : List Verb}
    (hstep : SelectedROMRewrite before after)
    (hschedule : DFSSchedule (after :: rest)) :
    DFSSchedule (before :: after :: rest) :=
  ⟨hstep, hschedule⟩

/-- A schedule with a specified head is a `TraceOfROM`. -/
theorem traceOfROM_of_dfsSchedule {root : Verb} {trace : List Verb}
    (hhead : trace.head? = some root)
    (hschedule : DFSSchedule trace) :
    TraceOfROM root trace :=
  ⟨hhead, consistentROM_of_dfsSchedule hschedule⟩

/-- Concatenate two nonempty consistent relation paths whose boundary vertices agree.

The second head is dropped, so the common boundary occurs exactly once. -/
theorem consistentR_append_tail {R : Verb → Verb → Prop} :
    ∀ {left right : List Verb} {middle : Verb},
      left.getLast? = some middle →
      right.head? = some middle →
      ConsistentR R left →
      ConsistentR R right →
      ConsistentR R (left ++ right.tail) := by
  intro left
  induction left with
  | nil =>
      intro right middle hlast
      simp at hlast
  | cons first rest ih =>
      intro right middle hlast hhead hleft hright
      cases rest with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          subst middle
          cases right with
          | nil => simp at hhead
          | cons r rs =>
              simp only [List.head?_cons, Option.some.injEq] at hhead
              subst r
              simpa using hright
      | cons second rest' =>
          simp only [ConsistentR] at hleft
          have htail :
              ConsistentR R ((second :: rest') ++ right.tail) :=
            ih hlast hhead hleft.2 hright
          simpa only [List.cons_append, ConsistentR] using And.intro hleft.1 htail

/-- Concatenate two ROM traces at a shared endpoint. -/
theorem traceOfROM_concat {root middle : Verb} {left right : List Verb}
    (hleft : TraceOfROM root left)
    (hlast : left.getLast? = some middle)
    (hright : TraceOfROM middle right) :
    TraceOfROM root (left ++ right.tail) := by
  constructor
  · cases left with
    | nil =>
        have himpossible := hleft.1
        simp at himpossible
    | cons first rest =>
        simpa using hleft.1
  · exact consistentR_append_tail hlast hright.1 hleft.2 hright.2

/-- Concatenate two explicit DFS schedules at a shared endpoint. -/
theorem dfsSchedule_concat {middle : Verb} {left right : List Verb}
    (hlast : left.getLast? = some middle)
    (hhead : right.head? = some middle)
    (hleft : DFSSchedule left)
    (hright : DFSSchedule right) :
    DFSSchedule (left ++ right.tail) :=
  consistentR_append_tail hlast hhead hleft hright

/-! ## Contextual replacement schedules -/

/-- The verb obtained by placing `child` in the fixed `replaceAt` frame. -/
def plugAt (frame : Verb) (hole : ℕ) (child : Verb) : Verb :=
  replaceAt hole frame child

/-- One child transition is admissible in a fixed frame exactly when the global scheduler selects
some maximal site in the plugged parent and its local rewrite produces the plugged child
successor.

The selected global index need not equal `hole`: while evaluating a child program it normally
points to a pending node *inside* the child.  This is why the final splice equation is explicit. -/
def ContextualRewriteAt (frame : Verb) (hole : ℕ)
    (childBefore childAfter : Verb) : Prop :=
  ∃ globalIndex sub replacement,
    IsMaxPending dfsLt (plugAt frame hole childBefore) globalIndex ∧
    Verb.map globalIndex (plugAt frame hole childBefore) = some sub ∧
    inDomain sub = true ∧
    reduceROM sub = some replacement ∧
    plugAt frame hole childAfter =
      replaceAt globalIndex (plugAt frame hole childBefore) replacement

/-- An admissible contextual child rewrite is a genuine parent ROM step. -/
theorem ContextualRewriteAt.stepROM
    {frame childBefore childAfter : Verb} {hole : ℕ}
    (h : ContextualRewriteAt frame hole childBefore childAfter) :
    StepROM (plugAt frame hole childBefore) (plugAt frame hole childAfter) := by
  obtain ⟨globalIndex, sub, replacement, hmax, hmap, hdom, hreduce, hsplice⟩ := h
  rw [hsplice]
  exact stepROM_replaceAt_of_maximalDFS hmax hmap hdom hreduce

/-- Every adjacent child pair has an exact globally maximal realization in the fixed frame. -/
def ContextualScheduleAt (frame : Verb) (hole : ℕ) : List Verb → Prop
  | [] => True
  | [_] => True
  | childBefore :: childAfter :: rest =>
      ContextualRewriteAt frame hole childBefore childAfter ∧
      ContextualScheduleAt frame hole (childAfter :: rest)

/-- Contextual scheduling lifts to ROM consistency after mapping the fixed frame over the child
states. -/
theorem contextualSchedule_consistentROM (frame : Verb) (hole : ℕ) :
    ∀ {childTrace : List Verb},
      ContextualScheduleAt frame hole childTrace →
      ConsistentR StepROM (childTrace.map (plugAt frame hole))
  | [], _ => trivial
  | [_], _ => trivial
  | childBefore :: childAfter :: rest, h =>
      ⟨h.1.stepROM, contextualSchedule_consistentROM frame hole h.2⟩

/-- Honest contextual trace lifting.

The child trace supplies its initial state; `ContextualScheduleAt` supplies the additional
maximal-DFS/frame facts that are not derivable from a bare child trace for an arbitrary context. -/
theorem traceOfROM_map_plugAt
    {childRoot frame : Verb} {hole : ℕ} {childTrace : List Verb}
    (hchild : TraceOfROM childRoot childTrace)
    (hcontext : ContextualScheduleAt frame hole childTrace) :
    TraceOfROM (plugAt frame hole childRoot)
      (childTrace.map (plugAt frame hole)) := by
  constructor
  · rw [List.head?_map, hchild.1]
    rfl
  · exact contextualSchedule_consistentROM frame hole hcontext

/-! ## Universal frame laws -/

/-- A fixed `replaceAt` frame preserves the actual maximal-DFS ROM scheduler.

This is a local context law, not a trace or schedule witness: it is universally quantified over
one arbitrary selected child rewrite. -/
def MaximalDFSFrameLaw (frame : Verb) (hole : ℕ) : Prop :=
  ∀ {childBefore childAfter : Verb},
    SelectedROMRewrite childBefore childAfter →
    ContextualRewriteAt frame hole childBefore childAfter

/-- A universal frame law lifts any explicit child schedule to contextual scheduling. -/
theorem contextualScheduleAt_of_frameLaw
    {frame : Verb} {hole : ℕ} (hlaw : MaximalDFSFrameLaw frame hole) :
    ∀ {childTrace : List Verb},
      DFSSchedule childTrace →
      ContextualScheduleAt frame hole childTrace
  | [], _ => trivial
  | [_], _ => trivial
  | childBefore :: childAfter :: rest, hschedule =>
      ⟨hlaw hschedule.1,
        contextualScheduleAt_of_frameLaw hlaw hschedule.2⟩

/-- Contextual trace lifting from a universal maximal-DFS frame law. -/
theorem traceOfROM_map_plugAt_of_frameLaw
    {childRoot frame : Verb} {hole : ℕ} {childTrace : List Verb}
    (hchild : TraceOfROM childRoot childTrace)
    (hlaw : MaximalDFSFrameLaw frame hole) :
    TraceOfROM (plugAt frame hole childRoot)
      (childTrace.map (plugAt frame hole)) :=
  traceOfROM_map_plugAt hchild
    (contextualScheduleAt_of_frameLaw hlaw
      (dfsSchedule_of_consistentROM hchild.2))

/-! ## Global tree target/specification -/

/-- Source-level program and claimed terminal result attached to each realized compute label. -/
structure RealizedNodeSemantics (Label : Type*) where
  program : Label → Verb
  result : Label → Noun

/-- Global tree scheduling **target/specification** over a realized compute `NTree`.

This predicate already stores the root `DFSSchedule`, endpoint, recursively scheduled children,
and their contextual occurrences.  It is therefore a desired global specification, not a
construction from row-local facts.  No theorem below manufactures it from `Fcomp`,
`childLinkComp`, or `OpcodeSemantics`. -/
def TreeDFSSchedule {Label : Type*} (sem : RealizedNodeSemantics Label) :
    (tree : NTree Label) → List Verb → Prop
  | .node label children, trace =>
      trace.head? = some (sem.program label) ∧
      trace.getLast? = some (Verb.ofNoun (sem.result label)) ∧
      DFSSchedule trace ∧
      ∀ child ∈ children,
        ∃ childTrace frame hole pre post,
          TreeDFSSchedule sem child childTrace ∧
          ContextualScheduleAt frame hole childTrace ∧
          trace = pre ++ childTrace.map (plugAt frame hole) ++ post
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ‹child ∈ children›
  omega

/-- Projection/specification theorem: the root schedule already stored by `TreeDFSSchedule` is a
global ROM trace ending in the stated root result.  This is intentionally not presented as a
construction theorem. -/
theorem treeDFSSchedule_to_traceOfROM
    {Label : Type*} {sem : RealizedNodeSemantics Label}
    {tree : NTree Label} {trace : List Verb}
    (h : TreeDFSSchedule sem tree trace) :
    TraceOfROM (sem.program tree.label) trace ∧
      trace.getLast? = some (Verb.ofNoun (sem.result tree.label)) := by
  cases tree with
  | node label children =>
      rw [TreeDFSSchedule] at h
      exact ⟨traceOfROM_of_dfsSchedule h.1 h.2.2.1, h.2.1⟩

/-! ## Sharply typed residual: opcode-local frame/index laws -/

/-- Opcode-specific frame/index data, separated from the propositions it must satisfy.

Keeping this as explicit input makes the residual below a `Prop` with no existentially hidden
trace, schedule, frame, or index. -/
structure OpcodeFrameIndexLayout {Label : Type*}
    (sem : RealizedNodeSemantics Label) (node : NTree Label) where
  initialSuccessor : Verb
  childFrame : NTree Label → Verb
  childHole : NTree Label → ℕ

/-- Per-node laws still needed from each opcode expansion.

`initial` is only the row-local first rewrite.  For each actual child, the supplied frame and hole
identify its opcode-specific one-hole context, while `childMaximalDFS` says universally that every
selected child rewrite remains the globally selected rewrite in that context.  There is no trace,
`DFSSchedule`, or existential schedule conclusion here.

These laws still need phase-chain equations between successive child contexts and an
opcode-specific finite postlude after all children become terminal.  Those equations differ for
OP2, OP3/4, OP5, OP6, OP7/8, OP9, and structural cons; the existing row API does not expose them. -/
structure OpcodeLocalFrameIndexLaws {Label : Type*}
    (sem : RealizedNodeSemantics Label) (node : NTree Label)
    (layout : OpcodeFrameIndexLayout sem node) : Prop where
  initial :
    SelectedROMRewrite (sem.program node.label) layout.initialSuccessor
  childMaximalDFS :
    ∀ child ∈ node.children,
      MaximalDFSFrameLaw (layout.childFrame child) (layout.childHole child)

/-- Production-level residual seam.

For every accepted compute node, `Fcomp` and its actual `childLinkComp` realization equalities must
determine opcode-local frame/index laws.  The conclusion is local and universal over one rewrite;
it is not an existential trace or scheduling witness. -/
def ProductionOpcodeFrameIndexResidual {K : Type*} [Field K]
    (sem : RealizedNodeSemantics
      (ComputeTable.State × ComputeTable.DTcomp K))
    (layout :
      ∀ node : NTree (ComputeTable.State × ComputeTable.DTcomp K),
        OpcodeFrameIndexLayout sem node) : Prop :=
  ∀ node : NTree (ComputeTable.State × ComputeTable.DTcomp K),
    ComputeTable.Fcomp node.label (fun i => node.childLabel i) →
    ComputeTable.childLinkComp node.label (fun i => node.childLabel i) →
    OpcodeLocalFrameIndexLaws sem node (layout node)

/-- Exact compute topology exposes the production `Fcomp` and `childLinkComp` premises needed by
the local residual at every node.  The conclusion remains only local frame/index laws. -/
theorem opcodeLocalFrameIndexLaws_of_computeTopology
    {K : Type*} [Field K]
    {sem : RealizedNodeSemantics
      (ComputeTable.State × ComputeTable.DTcomp K)}
    {layout :
      ∀ node : NTree (ComputeTable.State × ComputeTable.DTcomp K),
        OpcodeFrameIndexLayout sem node}
    {tree node : NTree (ComputeTable.State × ComputeTable.DTcomp K)}
    (hresidual : ProductionOpcodeFrameIndexResidual sem layout)
    (htopology : RVTWithArity (ComputeTable.Fcomp (K := K)) tree)
    (hnode : InTree tree node) :
    OpcodeLocalFrameIndexLaws sem node (layout node) := by
  have hFcon :=
    (RVT_iff_forall_InTree (ComputeTable.Fcomp (K := K)) tree).mp
      htopology.rvt node hnode
  exact hresidual node hFcon.1 hFcon.1.2.2.2

end Nock.NockVMROM.Thm54.DFSScheduling

#print axioms Nock.NockVMROM.Thm54.DFSScheduling.selectedROMRewrite_iff_stepROM
#print axioms Nock.NockVMROM.Thm54.DFSScheduling.stepROM_replaceAt_of_maximalDFS
#print axioms Nock.NockVMROM.Thm54.DFSScheduling.traceOfROM_concat
#print axioms Nock.NockVMROM.Thm54.DFSScheduling.traceOfROM_map_plugAt
#print axioms Nock.NockVMROM.Thm54.DFSScheduling.traceOfROM_map_plugAt_of_frameLaw
#print axioms Nock.NockVMROM.Thm54.DFSScheduling.treeDFSSchedule_to_traceOfROM
#print axioms Nock.NockVMROM.Thm54.DFSScheduling.opcodeLocalFrameIndexLaws_of_computeTopology
