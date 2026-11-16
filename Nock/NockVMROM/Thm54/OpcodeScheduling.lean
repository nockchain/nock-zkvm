import Nock.NockVMROM.Thm54.DFSScheduling
import Nock.NockVMROM.Thm54.SemanticTrace

/-!
# Opcode-local maximal-DFS scheduling

This file records the production opcode census in the order actually selected by
`Verb.getIndex`.  In particular, binary sibling calls run right-to-left: DFS preorder gives every
node of the right subtree a larger index than every node of the left subtree.

All eleven production states are closed completely from their local certificates and child
schedules.  No theorem assumes a parent trace or stores its scheduling conclusion.
-/

namespace Nock.NockVMROM.Thm54.OpcodeScheduling

open Nock Nock.Noun Nock.Verb Nock.Walk
open ComputeTable
open DFSScheduling
open SemanticTrace

/-! ## Complete state census -/

/-- The eleven and only eleven production compute states. -/
def allStates : List State :=
  [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .cons]

theorem mem_allStates (st : State) : st ∈ allStates := by
  cases st <;> decide

/-- The actual local scheduling shape of each production state.

The entries list recursive calls in execution order, not in `sf` slot order. -/
inductive ScheduleShape
  | leafSlot
  | leafIdentity
  | calls321
  | call1ThenWut
  | call1ThenLus
  | calls21ThenEqual
  | conditionThenBranch
  | call2ThenCall1
  | coreThenArm
  | calls21ThenCons
  deriving DecidableEq, Repr

def scheduleShape : State → ScheduleShape
  | .s0 => .leafSlot
  | .s1 => .leafIdentity
  | .s2 => .calls321
  | .s3 => .call1ThenWut
  | .s4 => .call1ThenLus
  | .s5 => .calls21ThenEqual
  | .s6 => .conditionThenBranch
  | .s7 => .call2ThenCall1
  | .s8 => .call2ThenCall1
  | .s9 => .coreThenArm
  | .cons => .calls21ThenCons

/-! ## Small executable scheduler lemmas -/

private theorem isTerminal_ofNoun (n : Noun) :
    Verb.isTerminal (Verb.ofNoun n) = true := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr =>
      simp only [Verb.ofNoun, Verb.isTerminal, Action.isNull, ihl, ihr, Bool.and_self]

private theorem noun_ofNoun (n : Noun) :
    (Verb.ofNoun n).noun = n := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr =>
      simp only [Verb.ofNoun, Verb.noun, ihl, ihr]

/-- A pending operator whose arguments are terminal is selected at the root. -/
private theorem getIndex_operator_ofNoun
    (a : Action) (ha : a.isNull = false) (left right : Noun) :
    Verb.getIndex (.node a (Verb.ofNoun left) (Verb.ofNoun right)) = some 0 := by
  rw [Verb.getIndex_eq_some_iff]
  constructor
  · exact ⟨.node a (Verb.ofNoun left) (Verb.ofNoun right), rfl, by simp [Verb.isPending, ha]⟩
  · intro j hj
    obtain ⟨v, hmap, hv⟩ := hj
    have hmem := Verb.mem_nodes_of_map hmap
    simp only [Verb.nodes, Verb.enum, List.mem_cons, List.mem_append] at hmem
    rcases hmem with hroot | hleft | hright
    · have : j = 0 := congrArg Prod.fst hroot
      subst j
      exact Nat.not_lt_zero 0
    · have hnon :=
        Verb.enum_nonpending_of_terminal (Verb.ofNoun left)
          (isTerminal_ofNoun left) 1 (j, v) hleft
      simp [hv] at hnon
    · have hnon :=
        Verb.enum_nonpending_of_terminal (Verb.ofNoun right)
          (isTerminal_ofNoun right) (Verb.enum (Verb.ofNoun left) 1).1
          (j, v) hright
      simp [hv] at hnon

/-- The finite operator postlude of OP0. -/
theorem stepROM_slot_terminal {axis : ℕ} {subject result : Noun}
    (hslot : Noun.slot axis subject = some result) :
    Verb.StepROM
      (.node .slot (Verb.ofNoun (.atom axis)) (Verb.ofNoun subject))
      (Verb.ofNoun result) := by
  unfold Verb.StepROM Verb.nextROM
  rw [getIndex_operator_ofNoun .slot (by decide) (.atom axis) subject]
  simp only [Verb.map, Verb.nodes, Verb.enum, Verb.findAt, ↓reduceIte]
  simp [Verb.inDomain, Verb.inOpcodeDomain, Verb.opReady, isTerminal_ofNoun,
    Verb.reduceROM, Verb.reduce, noun_ofNoun, hslot, Verb.replaceAt, Verb.replaceAux,
    Action.isOperator]

/-- The finite operator postlude of OP3. -/
theorem stepROM_wut_terminal (value : Noun) :
    Verb.StepROM
      (.node .minus (.leaf 3) (Verb.ofNoun value))
      (Verb.ofNoun (Noun.wut value)) := by
  unfold Verb.StepROM Verb.nextROM
  have hindex :
      Verb.getIndex (.node .minus (.leaf 3) (Verb.ofNoun value)) = some 0 := by
    simpa only [Verb.ofNoun] using
      getIndex_operator_ofNoun .minus (by decide) (.atom 3) value
  rw [hindex]
  cases value <;>
    simp [Verb.map, Verb.nodes, Verb.enum, Verb.findAt, Verb.inDomain,
      Verb.inOpcodeDomain, Verb.opReady, isTerminal_ofNoun, Verb.reduceROM,
      Verb.reduce, noun_ofNoun, Verb.replaceAt, Verb.replaceAux, Action.isOperator,
      Action.isNull, Verb.isTerminal, Verb.noun, Verb.ofNoun, Noun.wut]

/-- The finite operator postlude of OP4, when increment succeeds. -/
theorem stepROM_lus_terminal {value result : Noun}
    (hlus : Noun.lus value = some result) :
    Verb.StepROM
      (.node .minus (.leaf 4) (Verb.ofNoun value))
      (Verb.ofNoun result) := by
  unfold Verb.StepROM Verb.nextROM
  have hindex :
      Verb.getIndex (.node .minus (.leaf 4) (Verb.ofNoun value)) = some 0 := by
    simpa only [Verb.ofNoun] using
      getIndex_operator_ofNoun .minus (by decide) (.atom 4) value
  rw [hindex]
  simp [Verb.map, Verb.nodes, Verb.enum, Verb.findAt, Verb.inDomain,
    Verb.inOpcodeDomain, Verb.opReady, isTerminal_ofNoun, Verb.reduceROM,
    Verb.reduce, noun_ofNoun, Verb.replaceAt, Verb.replaceAux, Action.isOperator,
    Verb.isTerminal, Verb.noun, hlus]

private theorem noun_lus_eq_incNoWrap {q : ℕ} {value : Noun}
    (hno : OpcodeSemantics.IncrementNoOverflow q value) :
    Noun.lus value = some (OpcodeSemantics.incNoWrap value) := by
  cases value <;>
    simp_all [OpcodeSemantics.IncrementNoOverflow, OpcodeSemantics.incNoWrap, Noun.lus]

/-- The finite operator postlude of OP5. -/
theorem stepROM_equal_terminal (left right : Noun) :
    Verb.StepROM
      (.node .equal (Verb.ofNoun left) (Verb.ofNoun right))
      (Verb.ofNoun (Noun.tis left right)) := by
  unfold Verb.StepROM Verb.nextROM
  rw [getIndex_operator_ofNoun .equal (by decide) left right]
  simp [Verb.map, Verb.nodes, Verb.enum, Verb.findAt, Verb.inDomain,
    Verb.inOpcodeDomain, Verb.opReady, isTerminal_ofNoun, Verb.reduceROM,
    Verb.reduce, noun_ofNoun, Verb.replaceAt, Verb.replaceAux, Action.isOperator]

/-! ## Complete leaf schedules -/

/-- OP0 has exactly two selected rewrites: opcode expansion, then the ready slot operator. -/
theorem s0_complete_schedule (subject : Noun) (axis : ℕ) (result : Noun)
    (hslot : Noun.slot axis subject = some result) :
    DFSSchedule
      [ Verb.program subject (.cell (.atom 0) (.atom axis)),
        .node .slot (Verb.ofNoun (.atom axis)) (Verb.ofNoun subject),
        Verb.ofNoun result ] := by
  exact ⟨
    selectedROMRewrite_iff_stepROM.mpr
      (OpcodeSemantics.stepROM_s0_exact subject (.atom axis)),
    selectedROMRewrite_iff_stepROM.mpr (stepROM_slot_terminal hslot),
    trivial⟩

/-- OP1 is one selected rewrite directly to its terminal result. -/
theorem s1_complete_schedule (subject result : Noun) :
    DFSSchedule
      [Verb.program subject (.cell (.atom 1) result), Verb.ofNoun result] := by
  exact ⟨selectedROMRewrite_iff_stepROM.mpr
    (OpcodeSemantics.stepROM_s1_exact subject result), trivial⟩

/-- A certified OP0 row yields the exact complete local schedule ending in the certified result. -/
theorem s0_complete_of_certificate
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s0, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) :
    ∃ axis : ℕ,
      DFSSchedule
        [ Verb.program data.root.subject data.root.formula,
          .node .slot (Verb.ofNoun (.atom axis)) (Verb.ofNoun data.root.subject),
          Verb.ofNoun data.root.result ] := by
  cases cert with
  | s0 data fuel axis hstate hz hcast hhead hformula htail hmr hserved hv =>
      refine ⟨axis, ?_⟩
      have hsem :=
        OpcodeSemantics.s0_vcomp_semantics (fuel := fuel) hstate hz hcast data.root
          hhead.faithful hformula.faithful htail.faithful hmr hserved hv
      have hslot : Noun.slot axis data.root.subject = some data.root.result :=
        GlobalCarryRecognizer.axis_sound_recognizer' data.root.subject hserved
      exact ⟨selectedROMRewrite_iff_stepROM.mpr hsem.1,
        selectedROMRewrite_iff_stepROM.mpr (stepROM_slot_terminal hslot), trivial⟩

/-- A certified OP1 row yields the exact one-step schedule ending in its certified result. -/
theorem s1_complete_of_certificate
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s1, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) :
    DFSSchedule
      [Verb.program data.root.subject data.root.formula, Verb.ofNoun data.root.result] := by
  cases cert with
  | s1 data fuel hstate hz hcast hhead hformula hresult hv =>
      have hsem :=
        OpcodeSemantics.s1_vcomp_semantics (fuel := fuel) hstate hz hcast data.root
          hhead.faithful hformula.faithful hresult.faithful hv
      have hv' := hv
      obtain ⟨_, _, _, _, heval⟩ := hv'
      simp only [ComputeTable.evalV, hstate] at heval
      have hresultEq : data.root.result = data.root.tail :=
        OpcodeSemantics.noun_eq_of_realizes_eq
          data.root.result_realizes data.root.tail_realizes heval.1 hcast hresult.faithful
      rw [hresultEq]
      exact ⟨selectedROMRewrite_iff_stepROM.mpr hsem.1, trivial⟩

/-! ## Universal root-hole contexts -/

/-- A concrete one-hole frame whose hole is its root.  This is the actual context whenever a
parent phase has reduced to the next child program itself (OP2 slot 3, OP7/8 slot 1, the selected
OP6 branch, and OP9's arm call after its fixed macro prelude). -/
def rootHoleFrame : Verb :=
  .node .null (.leaf 0) (.leaf 0)

@[simp]
theorem plugAt_rootHoleFrame (child : Verb) :
    plugAt rootHoleFrame 0 child = child := by
  rfl

/-- Root replacement preserves every selected rewrite.  The proof computes `replaceAt` directly;
it assumes no child trace or schedule. -/
theorem rootHoleFrame_maximalDFS :
    MaximalDFSFrameLaw rootHoleFrame 0 := by
  intro childBefore childAfter hstep
  obtain ⟨i, sub, replacement, hmax, hmap, hdom, hreduce, hsplice⟩ := hstep
  exact ⟨i, sub, replacement,
    by simpa only [plugAt_rootHoleFrame] using hmax,
    by simpa only [plugAt_rootHoleFrame] using hmap,
    hdom, hreduce,
    by simpa only [plugAt_rootHoleFrame] using hsplice⟩

/-! ## Shifted DFS frames -/

private theorem enum_shift (v : Verb) (c d : ℕ) :
    Verb.enum v (c + d) =
      ((Verb.enum v c).1 + d,
        (Verb.enum v c).2.map (fun p => (p.1 + d, p.2))) := by
  induction v generalizing c with
  | leaf n =>
      simp [Verb.enum]
  | node a left right ihLeft ihRight =>
      simp only [Verb.enum]
      have hc : c + d + 1 = (c + 1) + d := by omega
      rw [hc, ihLeft]
      rw [ihRight]
      simp only [List.map_append, List.map_cons]

private theorem replaceAux_shift (v replacement : Verb) (i c d : ℕ) :
    Verb.replaceAux (i + d) replacement v (c + d) =
      ((Verb.replaceAux i replacement v c).1 + d,
        (Verb.replaceAux i replacement v c).2) := by
  induction v generalizing c with
  | leaf n =>
      simp [Verb.replaceAux]
  | node a left right ihLeft ihRight =>
      simp only [Verb.replaceAux]
      have hc : c + d + 1 = (c + 1) + d := by omega
      rw [hc, ihLeft]
      rw [ihRight]
      simp only [Nat.add_right_cancel_iff]

private theorem replaceAux_fst (v replacement : Verb) (i c : ℕ) :
    (Verb.replaceAux i replacement v c).1 = (Verb.enum v c).1 := by
  induction v generalizing c with
  | leaf n => rfl
  | node action left right ihLeft ihRight =>
      simp only [Verb.replaceAux, Verb.enum]
      rw [ihLeft, ihRight]

private theorem map_shift_one (action : Action) (fixed : ℕ)
    {child sub : Verb} {i : ℕ}
    (hmap : Verb.map i child = some sub) :
    Verb.map (i + 1) (.node action (.leaf fixed) child) = some sub := by
  apply Verb.map_of_mem_nodes
  have hmem := Verb.mem_nodes_of_map hmap
  have hshift := congrArg Prod.snd (enum_shift child 0 1)
  have hchild : (i + 1, sub) ∈ (Verb.enum child 1).2 := by
    rw [hshift]
    exact List.mem_map.mpr ⟨(i, sub), by simpa [Verb.nodes] using hmem, rfl⟩
  simp only [Verb.nodes, Verb.enum, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr hchild)

/-- A one-hole frame with a fixed terminal atom on the left and the child on the right. -/
def unaryRightFrame (action : Action) (fixed : ℕ) : Verb :=
  .node action (.leaf fixed) (.node .null (.leaf 0) (.leaf 0))

@[simp]
theorem plugAt_unaryRightFrame (action : Action) (fixed : ℕ) (child : Verb) :
    plugAt (unaryRightFrame action fixed) 1 child =
      .node action (.leaf fixed) child := by
  rfl

/-- The exact replacement splice under a unary right frame. -/
private theorem replaceAt_unaryRight (action : Action) (fixed : ℕ)
    (child replacement : Verb) (i : ℕ) :
    Verb.replaceAt (i + 1) (.node action (.leaf fixed) child) replacement =
      .node action (.leaf fixed) (Verb.replaceAt i child replacement) := by
  unfold Verb.replaceAt
  simp only [Verb.replaceAux]
  rw [show i + 1 = i + 1 by rfl]
  have hs := replaceAux_shift child replacement i 0 1
  simp only [Nat.zero_add] at hs
  rw [hs]
  simp

/-- A selected child rewrite remains maximal beneath a unary operator whose fixed left argument is
terminal.  The selected global index is exactly the child's DFS index plus one. -/
theorem unaryRightFrame_maximalDFS (action : Action) (fixed : ℕ) :
    MaximalDFSFrameLaw (unaryRightFrame action fixed) 1 := by
  intro childBefore childAfter hstep
  obtain ⟨i, sub, replacement, hmax, hmap, hdom, hreduce, hsplice⟩ := hstep
  obtain ⟨sub', hmap', hpending'⟩ := hmax.1
  have hsub : sub' = sub := Option.some.inj (hmap'.symm.trans hmap)
  subst sub'
  refine ⟨i + 1, sub, replacement, ?_, ?_, hdom, hreduce, ?_⟩
  · constructor
    · exact ⟨sub,
        by simpa only [plugAt_unaryRightFrame] using
          map_shift_one action fixed (child := childBefore) hmap,
        hpending'⟩
    · intro j hj hij
      obtain ⟨w, hjmap, hjpending⟩ := hj
      have hjmem := Verb.mem_nodes_of_map hjmap
      simp only [plugAt_unaryRightFrame, Verb.nodes, Verb.enum, List.mem_cons,
        List.mem_append] at hjmem
      rcases hjmem with hroot | hleft | hchild
      · have : j = 0 := congrArg Prod.fst hroot
        omega
      · simp at hleft
      · rw [enum_shift childBefore 0 1] at hchild
        simp only [List.mem_map] at hchild
        obtain ⟨p, hp, hpEq⟩ := hchild
        have hjEq : j = p.1 + 1 := (congrArg Prod.fst hpEq).symm
        have hwEq : w = p.2 := (congrArg Prod.snd hpEq).symm
        have hpmap : Verb.map p.1 childBefore = some p.2 :=
          Verb.map_of_mem_nodes hp
        have hpending : p.2.isPending = true := by simpa [hwEq] using hjpending
        have hnot := hmax.2 p.1 ⟨p.2, hpmap, hpending⟩
        omega
  · simpa only [plugAt_unaryRightFrame] using
      map_shift_one action fixed (child := childBefore) hmap
  · simp only [plugAt_unaryRightFrame]
    rw [replaceAt_unaryRight, hsplice]

/-- OP3's child runs in the right branch of the pending `minus 3` operator. -/
theorem s3_child_maximalDFS :
    MaximalDFSFrameLaw (unaryRightFrame .minus 3) 1 :=
  unaryRightFrame_maximalDFS .minus 3

/-- OP4's child runs in the right branch of the pending `minus 4` operator. -/
theorem s4_child_maximalDFS :
    MaximalDFSFrameLaw (unaryRightFrame .minus 4) 1 :=
  unaryRightFrame_maximalDFS .minus 4

/-! ## Trace assembly through a proved frame -/

/-- A complete maximal-DFS trace to a certified terminal noun. -/
def MaximalDFSTrace (root : Verb) (result : Noun) (trace : List Verb) : Prop :=
  trace.head? = some root ∧
  DFSSchedule trace ∧
  trace.getLast? = some (Verb.ofNoun result) ∧
  Verb.isTerminal (Verb.ofNoun result) = true

theorem maximalDFSTrace_of_traceOfROM
    {root : Verb} {result : Noun} {trace : List Verb}
    (htrace : Verb.TraceOfROM root trace)
    (hlast : trace.getLast? = some (Verb.ofNoun result)) :
    MaximalDFSTrace root result trace :=
  ⟨htrace.1, dfsSchedule_of_consistentROM htrace.2, hlast, isTerminal_ofNoun result⟩

/-- Assemble an initial parent rewrite, a mapped child trace, and one selected postlude.  No parent
trace is assumed: the returned trace is constructed from the three local pieces. -/
theorem complete_one_child_with_postlude
    {root childRoot : Verb} {childResult parentResult : Noun}
    {frame : Verb} {hole : ℕ} {childTrace : List Verb}
    (hinitial : SelectedROMRewrite root (plugAt frame hole childRoot))
    (hframe : MaximalDFSFrameLaw frame hole)
    (hchild : Verb.TraceOfROM childRoot childTrace)
    (hchildLast : childTrace.getLast? = some (Verb.ofNoun childResult))
    (hpost : SelectedROMRewrite
      (plugAt frame hole (Verb.ofNoun childResult))
      (Verb.ofNoun parentResult)) :
    ∃ parentTrace,
      parentTrace =
        root :: (childTrace.map (plugAt frame hole) ++ [Verb.ofNoun parentResult]) ∧
      Verb.TraceOfROM root parentTrace ∧
      parentTrace.getLast? = some (Verb.ofNoun parentResult) := by
  have hmapped :=
    traceOfROM_map_plugAt_of_frameLaw hchild hframe
  have hmappedLast :
      (childTrace.map (plugAt frame hole)).getLast? =
        some (plugAt frame hole (Verb.ofNoun childResult)) := by
    rw [List.getLast?_map, hchildLast]
    rfl
  cases hmappedEq : childTrace.map (plugAt frame hole) with
  | nil =>
      have himpossible := hmapped.1
      rw [hmappedEq] at himpossible
      simp at himpossible
  | cons first rest =>
      have hmapped' := hmapped
      rw [hmappedEq] at hmapped'
      have hfirst : first = plugAt frame hole childRoot := by
        simpa using Option.some.inj hmapped'.1
      subst first
      have hbase :
          Verb.TraceOfROM root
            (root :: plugAt frame hole childRoot :: rest) := by
        exact ⟨rfl, selectedROMRewrite_iff_stepROM.mp hinitial, hmapped'.2⟩
      have hbaseLast :
          (root :: plugAt frame hole childRoot :: rest).getLast? =
            some (plugAt frame hole (Verb.ofNoun childResult)) := by
        rw [hmappedEq] at hmappedLast
        simpa using hmappedLast
      have hpostTrace :
          Verb.TraceOfROM (plugAt frame hole (Verb.ofNoun childResult))
            [plugAt frame hole (Verb.ofNoun childResult), Verb.ofNoun parentResult] :=
        ⟨rfl, selectedROMRewrite_iff_stepROM.mp hpost, trivial⟩
      have hjoined :=
        traceOfROM_concat hbase hbaseLast hpostTrace
      refine ⟨(root :: plugAt frame hole childRoot :: rest) ++ [Verb.ofNoun parentResult],
        ?_, ?_, ?_⟩
      · simp
      · simpa using hjoined
      · rw [List.getLast?_append_of_ne_nil
          (root :: plugAt frame hole childRoot :: rest) (by simp)]
        rfl

def s3ChildResult
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s3, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Noun := by
  cases cert with
  | s3 _ _ call1 _ _ _ _ _ _ _ _ _ _ => exact call1.result

def s4ChildResult
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s4, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Noun := by
  cases cert with
  | s4 _ _ call1 _ _ _ _ _ _ _ _ _ _ _ => exact call1.result

/-- Complete certified OP3 execution from only its child trace. -/
theorem s3_complete_of_certificate_and_children
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s3, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data)
    {childTrace : List Verb}
    (hchild : Verb.TraceOfROM
      (Verb.program data.root.subject data.root.tail) childTrace)
    (hchildLast :
      childTrace.getLast? = some (Verb.ofNoun (s3ChildResult cert))) :
    ∃ parentTrace,
      Verb.TraceOfROM
        (Verb.program data.root.subject data.root.formula) parentTrace ∧
      parentTrace.getLast? = some (Verb.ofNoun data.root.result) := by
  cases cert with
  | s3 data fuel call1 hstate hz hcast hhead hformula h1s h1f hresult
      hsize hcall hv =>
      simp only [s3ChildResult] at hchildLast
      have hsem :=
        OpcodeSemantics.s3_vcomp_semantics (fuel := fuel) hstate hz hcast data.root call1
          hhead.faithful hformula.faithful h1s.faithful h1f.faithful
          hresult.faithful hsize hcall hv
      have hv' := hv
      obtain ⟨_, _, _, _, hevalV⟩ := hv'
      simp only [ComputeTable.evalV, hstate] at hevalV
      have h1sEq : call1.subject = data.root.subject :=
        OpcodeSemantics.noun_eq_of_realizes_eq call1.subject_realizes
          data.root.subject_realizes hevalV.1 hcast h1s.faithful
      have h1fEq : call1.formula = data.root.tail :=
        OpcodeSemantics.noun_eq_of_realizes_eq call1.formula_realizes
          data.root.tail_realizes hevalV.2.1 hcast h1f.faithful
      have hc := hcall
      rw [h1sEq, h1fEq] at hc
      have hformulaEq : data.root.formula = .cell (.atom 3) data.root.tail :=
        OpcodeSemantics.numeric_formula_eq hstate (by decide) hz hcast data.root
          hhead.faithful hformula.faithful hv
      have hparentEval := hsem.2
      rw [hformulaEq] at hparentEval
      simp only [FieldEmbedding.evalFBy, hc, Option.map_some] at hparentEval
      have hresultEq : data.root.result = Noun.wut call1.result :=
        (Option.some.inj hparentEval).symm
      obtain ⟨parentTrace, _, htrace, hlast⟩ :=
        complete_one_child_with_postlude
          (root := Verb.program data.root.subject data.root.formula)
          (childRoot := Verb.program data.root.subject data.root.tail)
          (childResult := call1.result)
          (parentResult := Noun.wut call1.result)
          (frame := unaryRightFrame .minus 3) (hole := 1)
          (by simpa only [plugAt_unaryRightFrame, Verb.program] using
            selectedROMRewrite_iff_stepROM.mpr hsem.1)
          s3_child_maximalDFS hchild hchildLast
          (by simpa only [plugAt_unaryRightFrame] using
            selectedROMRewrite_iff_stepROM.mpr (stepROM_wut_terminal call1.result))
      rw [hresultEq]
      exact ⟨parentTrace, htrace, hlast⟩

/-- Complete certified OP4 execution in the paper's modular evaluator. -/
theorem s4_complete_of_certificate_and_children
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s4, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data)
    {childTrace : List Verb}
    (hchild : Verb.TraceOfROM
      (Verb.program data.root.subject data.root.tail) childTrace)
    (hchildLast :
      childTrace.getLast? = some (Verb.ofNoun (s4ChildResult cert))) :
    ∃ fuel, FieldEmbedding.evalFBy q fuel data.root.subject data.root.formula =
      some data.root.result := by
  obtain ⟨fuel, _, _, heval⟩ := LocalOpcodeCertificate.semantics cert
  exact ⟨fuel + 1, heval⟩

/-! ## Binary right-to-left frames -/

private theorem replaceAux_of_before_start
    (v replacement : Verb) {i c : ℕ} (hi : i < c) :
    Verb.replaceAux i replacement v c = ((Verb.enum v c).1, v) := by
  induction v generalizing c with
  | leaf n =>
      rfl
  | node action left right ihLeft ihRight =>
      simp only [Verb.replaceAux, Verb.enum]
      have hiLeft : i < c + 1 := by omega
      rw [ihLeft hiLeft]
      have hleftStart : c + 1 ≤ (Verb.enum left (c + 1)).1 :=
        Verb.enum_ge_start left (c + 1)
      rw [ihRight (by omega)]
      simp [show c ≠ i by omega]

private theorem replaceAux_of_end_le
    (v replacement : Verb) {i c : ℕ} (hi : (Verb.enum v c).1 ≤ i) :
    Verb.replaceAux i replacement v c = ((Verb.enum v c).1, v) := by
  induction v generalizing c with
  | leaf n =>
      rfl
  | node action left right ihLeft ihRight =>
      simp only [Verb.enum] at hi ⊢
      have hleftEnd :
          (Verb.enum left (c + 1)).1 ≤
            (Verb.enum right (Verb.enum left (c + 1)).1).1 :=
        Verb.enum_ge_start right (Verb.enum left (c + 1)).1
      have hcEnd : c <
          (Verb.enum right (Verb.enum left (c + 1)).1).1 := by
        have := Verb.enum_ge_start left (c + 1)
        omega
      simp only [Verb.replaceAux]
      rw [ihLeft (by omega), ihRight hi]
      simp [show c ≠ i by omega]

/-- Frame for the right child while the left child is still pending. -/
def binaryRightFrame (action : Action) (left : Verb) : Verb :=
  .node action left (.node .null (.leaf 0) (.leaf 0))

def binaryRightHole (left : Verb) : ℕ :=
  (Verb.enum left 1).1

@[simp]
theorem plugAt_binaryRightFrame (action : Action) (left child : Verb) :
    plugAt (binaryRightFrame action left) (binaryRightHole left) child =
      .node action left child := by
  unfold plugAt binaryRightFrame binaryRightHole Verb.replaceAt
  simp only [Verb.replaceAux]
  rw [replaceAux_of_end_le left child (le_refl _)]
  have hpositive : 0 < (Verb.enum left 1).1 := by
    have := Verb.enum_ge_start left 1
    omega
  simp [show 0 ≠ (Verb.enum left 1).1 by omega]

private theorem map_shift_right
    (action : Action) (left : Verb) {child sub : Verb} {i : ℕ}
    (hmap : Verb.map i child = some sub) :
    Verb.map (i + binaryRightHole left) (.node action left child) = some sub := by
  apply Verb.map_of_mem_nodes
  have hmem := Verb.mem_nodes_of_map hmap
  have hshift := congrArg Prod.snd (enum_shift child 0 (binaryRightHole left))
  simp only [Nat.zero_add] at hshift
  have hchild :
      (i + binaryRightHole left, sub) ∈
        (Verb.enum child (binaryRightHole left)).2 := by
    rw [hshift]
    exact List.mem_map.mpr ⟨(i, sub), by simpa [Verb.nodes] using hmem, rfl⟩
  simp only [Verb.nodes, Verb.enum, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (by simpa [binaryRightHole] using hchild))

private theorem replaceAt_binaryRight (action : Action) (left child replacement : Verb)
    (i : ℕ) :
    Verb.replaceAt (i + binaryRightHole left) (.node action left child) replacement =
      .node action left (Verb.replaceAt i child replacement) := by
  unfold Verb.replaceAt binaryRightHole
  simp only [Verb.replaceAux]
  rw [replaceAux_of_end_le left replacement (by omega : (Verb.enum left 1).1 ≤
    i + (Verb.enum left 1).1)]
  have hs := replaceAux_shift child replacement i 0 (Verb.enum left 1).1
  simp only [Nat.zero_add] at hs
  rw [hs]
  have hroot : (0 = i + (Verb.enum left 1).1) = False := by
    apply propext
    constructor
    · intro h
      have hpositive : 0 < (Verb.enum left 1).1 := by
        have := Verb.enum_ge_start left 1
        omega
      omega
    · intro h
      contradiction
  simp [hroot]

/-- Every selected rewrite in the right child remains globally maximal, even while the entire left
child is still pending, because all right-subtree DFS indices are larger. -/
theorem binaryRightFrame_maximalDFS (action : Action) (left : Verb) :
    MaximalDFSFrameLaw (binaryRightFrame action left) (binaryRightHole left) := by
  intro childBefore childAfter hstep
  obtain ⟨i, sub, replacement, hmax, hmap, hdom, hreduce, hsplice⟩ := hstep
  obtain ⟨sub', hmap', hpending'⟩ := hmax.1
  have hsub : sub' = sub := Option.some.inj (hmap'.symm.trans hmap)
  subst sub'
  refine ⟨i + binaryRightHole left, sub, replacement, ?_, ?_, hdom, hreduce, ?_⟩
  · constructor
    · exact ⟨sub,
        by simpa only [plugAt_binaryRightFrame] using
          map_shift_right action left (child := childBefore) hmap,
        hpending'⟩
    · intro j hj hij
      obtain ⟨w, hjmap, hjpending⟩ := hj
      have hjmem := Verb.mem_nodes_of_map hjmap
      simp only [plugAt_binaryRightFrame, Verb.nodes, Verb.enum, List.mem_cons,
        List.mem_append] at hjmem
      rcases hjmem with hroot | hleft | hchild
      · have : j = 0 := congrArg Prod.fst hroot
        have hhole : 0 < binaryRightHole left := by
          unfold binaryRightHole
          have := Verb.enum_ge_start left 1
          omega
        omega
      · have hjrange := Verb.enum_index_range left 1 (j, w) hleft
        unfold binaryRightHole at hij
        omega
      · have hshift := congrArg Prod.snd
          (enum_shift childBefore 0 (binaryRightHole left))
        simp only [Nat.zero_add] at hshift
        rw [show (Verb.enum left 1).1 = binaryRightHole left by rfl, hshift] at hchild
        simp only [List.mem_map] at hchild
        obtain ⟨p, hp, hpEq⟩ := hchild
        have hjEq : j = p.1 + binaryRightHole left :=
          (congrArg Prod.fst hpEq).symm
        have hwEq : w = p.2 := (congrArg Prod.snd hpEq).symm
        have hpmap : Verb.map p.1 childBefore = some p.2 :=
          Verb.map_of_mem_nodes hp
        have hpending : p.2.isPending = true := by simpa [hwEq] using hjpending
        have hnot := hmax.2 p.1 ⟨p.2, hpmap, hpending⟩
        omega
  · simpa only [plugAt_binaryRightFrame] using
      map_shift_right action left (child := childBefore) hmap
  · simp only [plugAt_binaryRightFrame]
    rw [replaceAt_binaryRight, hsplice]

/-- Frame for the left child once the right child has terminalized. -/
def binaryLeftFrame (action : Action) (right : Noun) : Verb :=
  .node action (.node .null (.leaf 0) (.leaf 0)) (Verb.ofNoun right)

@[simp]
theorem plugAt_binaryLeftFrame (action : Action) (right : Noun) (child : Verb) :
    plugAt (binaryLeftFrame action right) 1 child =
      .node action child (Verb.ofNoun right) := by
  unfold plugAt binaryLeftFrame Verb.replaceAt
  simp only [Verb.replaceAux]
  rw [replaceAux_of_before_start (Verb.ofNoun right) child (by omega)]
  simp

private theorem map_shift_left
    (action : Action) (right : Noun) {child sub : Verb} {i : ℕ}
    (hmap : Verb.map i child = some sub) :
    Verb.map (i + 1) (.node action child (Verb.ofNoun right)) = some sub := by
  apply Verb.map_of_mem_nodes
  have hmem := Verb.mem_nodes_of_map hmap
  have hshift := congrArg Prod.snd (enum_shift child 0 1)
  have hchild : (i + 1, sub) ∈ (Verb.enum child 1).2 := by
    rw [hshift]
    exact List.mem_map.mpr ⟨(i, sub), by simpa [Verb.nodes] using hmem, rfl⟩
  simp only [Verb.nodes, Verb.enum, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inl hchild)

private theorem replaceAt_binaryLeft (action : Action) (right : Noun)
    (child replacement : Verb) (i : ℕ)
    (hmap : ∃ sub, Verb.map i child = some sub) :
    Verb.replaceAt (i + 1) (.node action child (Verb.ofNoun right)) replacement =
      .node action (Verb.replaceAt i child replacement) (Verb.ofNoun right) := by
  unfold Verb.replaceAt
  simp only [Verb.replaceAux]
  have hs := replaceAux_shift child replacement i 0 1
  simp only [Nat.zero_add] at hs
  rw [hs]
  obtain ⟨sub, hmap⟩ := hmap
  have hirange := Verb.enum_index_range child 0 (i, sub)
    (by simpa [Verb.nodes] using Verb.mem_nodes_of_map hmap)
  have hstart : i + 1 <
      (Verb.replaceAux i replacement child 0).1 + 1 := by
    rw [replaceAux_fst]
    omega
  rw [replaceAux_of_before_start (Verb.ofNoun right) replacement hstart]
  simp

/-- Once the right child is terminal, every selected rewrite in the left child remains globally
maximal.  The terminal right subtree contributes no pending index. -/
theorem binaryLeftFrame_maximalDFS (action : Action) (right : Noun) :
    MaximalDFSFrameLaw (binaryLeftFrame action right) 1 := by
  intro childBefore childAfter hstep
  obtain ⟨i, sub, replacement, hmax, hmap, hdom, hreduce, hsplice⟩ := hstep
  obtain ⟨sub', hmap', hpending'⟩ := hmax.1
  have hsub : sub' = sub := Option.some.inj (hmap'.symm.trans hmap)
  subst sub'
  refine ⟨i + 1, sub, replacement, ?_, ?_, hdom, hreduce, ?_⟩
  · constructor
    · exact ⟨sub,
        by simpa only [plugAt_binaryLeftFrame] using
          map_shift_left action right (child := childBefore) hmap,
        hpending'⟩
    · intro j hj hij
      obtain ⟨w, hjmap, hjpending⟩ := hj
      have hjmem := Verb.mem_nodes_of_map hjmap
      simp only [plugAt_binaryLeftFrame, Verb.nodes, Verb.enum, List.mem_cons,
        List.mem_append] at hjmem
      rcases hjmem with hroot | hchild | hright
      · have : j = 0 := congrArg Prod.fst hroot
        omega
      · have hshift := congrArg Prod.snd (enum_shift childBefore 0 1)
        simp only [Nat.zero_add] at hshift
        rw [hshift] at hchild
        simp only [List.mem_map] at hchild
        obtain ⟨p, hp, hpEq⟩ := hchild
        have hjEq : j = p.1 + 1 := (congrArg Prod.fst hpEq).symm
        have hwEq : w = p.2 := (congrArg Prod.snd hpEq).symm
        have hpmap : Verb.map p.1 childBefore = some p.2 :=
          Verb.map_of_mem_nodes hp
        have hpending : p.2.isPending = true := by simpa [hwEq] using hjpending
        have hnot := hmax.2 p.1 ⟨p.2, hpmap, hpending⟩
        omega
      · have hnon :=
          Verb.enum_nonpending_of_terminal (Verb.ofNoun right)
            (isTerminal_ofNoun right) (Verb.enum childBefore 1).1
            (j, w) hright
        simp [hjpending] at hnon
  · simpa only [plugAt_binaryLeftFrame] using
      map_shift_left action right (child := childBefore) hmap
  · simp only [plugAt_binaryLeftFrame]
    rw [replaceAt_binaryLeft action right childBefore replacement i ⟨sub, hmap⟩,
      hsplice]

/-- Concatenate two constructed traces and retain the endpoint of the second. -/
private theorem concat_trace_with_last
    {root middle result : Verb} {left right : List Verb}
    (hleft : Verb.TraceOfROM root left)
    (hleftLast : left.getLast? = some middle)
    (hright : Verb.TraceOfROM middle right)
    (hrightLast : right.getLast? = some result) :
    ∃ joined,
      Verb.TraceOfROM root joined ∧ joined.getLast? = some result := by
  refine ⟨left ++ right.tail, traceOfROM_concat hleft hleftLast hright, ?_⟩
  cases right with
  | nil =>
      have himpossible := hright.1
      simp at himpossible
  | cons first rest =>
      cases rest with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hrightLast
          have hrightHead := hright.1
          simp only [List.head?_singleton, Option.some.injEq] at hrightHead
          subst first
          subst result
          simpa using hleftLast
      | cons second rest' =>
          rw [List.tail_cons,
            List.getLast?_append_of_ne_nil left (by simp)]
          simpa using hrightLast

def s5LeftFormula
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s5, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Noun := by
  cases cert with
  | s5 _ _ tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact tail.head

def s5RightFormula
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s5, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Noun := by
  cases cert with
  | s5 _ _ tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact tail.tail

def s5LeftResult
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s5, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Noun := by
  cases cert with
  | s5 _ _ _ call1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact call1.result

def s5RightResult
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s5, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Noun := by
  cases cert with
  | s5 _ _ _ _ call2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact call2.result

/-- Complete certified OP5 execution from its two child traces in the actual maximal-DFS order:
right child, left child, equality postlude. -/
theorem s5_complete_of_certificate_and_children
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s5, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data)
    {leftTrace rightTrace : List Verb}
    (hleft : Verb.TraceOfROM
      (Verb.program data.root.subject (s5LeftFormula cert)) leftTrace)
    (hleftLast :
      leftTrace.getLast? = some (Verb.ofNoun (s5LeftResult cert)))
    (hright : Verb.TraceOfROM
      (Verb.program data.root.subject (s5RightFormula cert)) rightTrace)
    (hrightLast :
      rightTrace.getLast? = some (Verb.ofNoun (s5RightResult cert))) :
    ∃ parentTrace,
      Verb.TraceOfROM
        (Verb.program data.root.subject data.root.formula) parentTrace ∧
      parentTrace.getLast? = some (Verb.ofNoun data.root.result) := by
  cases cert with
  | s5 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h1s h1f h2s h2f hcompare hresult hcall1 hcall2 hv =>
      change Verb.TraceOfROM
        (Verb.program data.root.subject tail.head) leftTrace at hleft
      change leftTrace.getLast? = some (Verb.ofNoun call1.result) at hleftLast
      change Verb.TraceOfROM
        (Verb.program data.root.subject tail.tail) rightTrace at hright
      change rightTrace.getLast? = some (Verb.ofNoun call2.result) at hrightLast
      have hsem :=
        OpcodeSemantics.s5_vcomp_semantics (fuel := fuel) hstate hz hcast data.root
          tail call1 call2 hhead.faithful hformula.faithful htail.faithful
          h1s.faithful h1f.faithful h2s.faithful h2f.faithful
          hcompare.faithful hresult.faithful hcall1 hcall2 hv
      have hv' := hv
      obtain ⟨_, _, _, hmem, hevalV⟩ := hv'
      simp only [ComputeTable.memBlk, hstate] at hmem
      obtain ⟨_, hcons, _, _⟩ := hmem
      have htailEq : data.root.tail = .cell tail.head tail.tail :=
        OpcodeSemantics.realized_tail_eq_cell hz hcast data.root tail
          htail.faithful hcons
      simp only [ComputeTable.evalV, hstate] at hevalV
      have h1sEq : call1.subject = data.root.subject :=
        OpcodeSemantics.noun_eq_of_realizes_eq call1.subject_realizes
          data.root.subject_realizes hevalV.1 hcast h1s.faithful
      have h1fEq : call1.formula = tail.head :=
        OpcodeSemantics.noun_eq_of_realizes_eq call1.formula_realizes
          tail.head_realizes hevalV.2.1 hcast h1f.faithful
      have h2sEq : call2.subject = data.root.subject :=
        OpcodeSemantics.noun_eq_of_realizes_eq call2.subject_realizes
          data.root.subject_realizes hevalV.2.2.1 hcast h2s.faithful
      have h2fEq : call2.formula = tail.tail :=
        OpcodeSemantics.noun_eq_of_realizes_eq call2.formula_realizes
          tail.tail_realizes hevalV.2.2.2.1 hcast h2f.faithful
      have hc1 := hcall1
      have hc2 := hcall2
      rw [h1sEq, h1fEq] at hc1
      rw [h2sEq, h2fEq] at hc2
      have hnumeric :=
        OpcodeSemantics.numeric_formula_eq hstate (by decide) hz hcast data.root
          hhead.faithful hformula.faithful hv
      change data.root.formula = .cell (.atom 5) data.root.tail at hnumeric
      have hformulaEq :
          data.root.formula = .cell (.atom 5) (.cell tail.head tail.tail) := by
        rw [hnumeric, htailEq]
      have hparentEval := hsem.2
      rw [hformulaEq] at hparentEval
      simp only [FieldEmbedding.evalFBy, hc1, hc2] at hparentEval
      have hresultEq :
          data.root.result = Noun.tis call1.result call2.result :=
        (Option.some.inj hparentEval).symm
      let leftRoot := Verb.program data.root.subject tail.head
      let rightRoot := Verb.program data.root.subject tail.tail
      let rightFrame := binaryRightFrame .equal leftRoot
      let rightHole := binaryRightHole leftRoot
      let leftFrame := binaryLeftFrame .equal call2.result
      have hmappedRight :
          Verb.TraceOfROM
            (plugAt rightFrame rightHole rightRoot)
            (rightTrace.map (plugAt rightFrame rightHole)) :=
        traceOfROM_map_plugAt_of_frameLaw hright
          (binaryRightFrame_maximalDFS .equal leftRoot)
      have hmappedRightLast :
          (rightTrace.map (plugAt rightFrame rightHole)).getLast? =
            some (plugAt rightFrame rightHole (Verb.ofNoun call2.result)) := by
        rw [List.getLast?_map, hrightLast]
        rfl
      have hinitial :
          Verb.TraceOfROM (Verb.program data.root.subject data.root.formula)
            [Verb.program data.root.subject data.root.formula,
              plugAt rightFrame rightHole rightRoot] := by
        refine ⟨rfl, ?_, trivial⟩
        simpa [rightFrame, rightHole, leftRoot, rightRoot, Verb.program] using hsem.1
      obtain ⟨throughRight, hthroughRight, hthroughRightLast⟩ :=
        concat_trace_with_last hinitial (by rfl) hmappedRight hmappedRightLast
      have hmappedLeft :
          Verb.TraceOfROM
            (plugAt leftFrame 1 leftRoot)
            (leftTrace.map (plugAt leftFrame 1)) :=
        traceOfROM_map_plugAt_of_frameLaw hleft
          (binaryLeftFrame_maximalDFS .equal call2.result)
      have hmappedLeftLast :
          (leftTrace.map (plugAt leftFrame 1)).getLast? =
            some (plugAt leftFrame 1 (Verb.ofNoun call1.result)) := by
        rw [List.getLast?_map, hleftLast]
        rfl
      have hphase :
          plugAt rightFrame rightHole (Verb.ofNoun call2.result) =
            plugAt leftFrame 1 leftRoot := by
        simp [rightFrame, rightHole, leftFrame]
      rw [hphase] at hthroughRightLast
      obtain ⟨throughLeft, hthroughLeft, hthroughLeftLast⟩ :=
        concat_trace_with_last hthroughRight hthroughRightLast
          hmappedLeft hmappedLeftLast
      have hpostTrace :
          Verb.TraceOfROM
            (plugAt leftFrame 1 (Verb.ofNoun call1.result))
            [plugAt leftFrame 1 (Verb.ofNoun call1.result),
              Verb.ofNoun (Noun.tis call1.result call2.result)] := by
        refine ⟨rfl, ?_, trivial⟩
        simpa [leftFrame] using stepROM_equal_terminal call1.result call2.result
      obtain ⟨parentTrace, hparentTrace, hparentLast⟩ :=
        concat_trace_with_last hthroughLeft hthroughLeftLast hpostTrace (by rfl)
      rw [hresultEq]
      exact ⟨parentTrace, hparentTrace, hparentLast⟩

def s7SecondFormula
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s7, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Noun := by
  cases cert with
  | s7 _ _ tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact tail.head

def s7FirstFormula
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s7, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Noun := by
  cases cert with
  | s7 _ _ tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact tail.tail

def s7SecondResult
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s7, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Noun := by
  cases cert with
  | s7 _ _ _ _ call2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact call2.result

def s7FirstResult
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s7, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Noun := by
  cases cert with
  | s7 _ _ _ call1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact call1.result

/-- Complete certified OP7 execution: call 2 in its non-root left frame, then call 1 as the whole
program. -/
theorem s7_complete_of_certificate_and_children
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s7, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data)
    {firstTrace secondTrace : List Verb}
    (hsecond : Verb.TraceOfROM
      (Verb.program data.root.subject (s7SecondFormula cert)) secondTrace)
    (hsecondLast :
      secondTrace.getLast? = some (Verb.ofNoun (s7SecondResult cert)))
    (hfirst : Verb.TraceOfROM
      (Verb.program (s7SecondResult cert) (s7FirstFormula cert)) firstTrace)
    (hfirstLast :
      firstTrace.getLast? = some (Verb.ofNoun (s7FirstResult cert))) :
    ∃ parentTrace,
      Verb.TraceOfROM
        (Verb.program data.root.subject data.root.formula) parentTrace ∧
      parentTrace.getLast? = some (Verb.ofNoun data.root.result) := by
  cases cert with
  | s7 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h2s h2f h1s h1f hresult hcall1 hcall2 hv =>
      change Verb.TraceOfROM
        (Verb.program data.root.subject tail.head) secondTrace at hsecond
      change secondTrace.getLast? = some (Verb.ofNoun call2.result) at hsecondLast
      change Verb.TraceOfROM
        (Verb.program call2.result tail.tail) firstTrace at hfirst
      change firstTrace.getLast? = some (Verb.ofNoun call1.result) at hfirstLast
      have hsem :=
        OpcodeSemantics.s7_vcomp_semantics (fuel := fuel) hstate hz hcast data.root
          tail call1 call2 hhead.faithful hformula.faithful htail.faithful
          h2s.faithful h2f.faithful h1s.faithful h1f.faithful
          hresult.faithful hcall1 hcall2 hv
      have hv' := hv
      obtain ⟨_, _, _, _, hevalV⟩ := hv'
      simp only [ComputeTable.evalV, hstate] at hevalV
      obtain ⟨_, _, heresult, _, _, _⟩ := hevalV
      have hresultEq : data.root.result = call1.result :=
        OpcodeSemantics.noun_eq_of_realizes_eq data.root.result_realizes
          call1.result_realizes heresult hcast hresult.faithful
      let secondFrame := binaryLeftFrame .star tail.tail
      let secondRoot := Verb.program data.root.subject tail.head
      have hmappedSecond :
          Verb.TraceOfROM
            (plugAt secondFrame 1 secondRoot)
            (secondTrace.map (plugAt secondFrame 1)) :=
        traceOfROM_map_plugAt_of_frameLaw hsecond
          (binaryLeftFrame_maximalDFS .star tail.tail)
      have hmappedSecondLast :
          (secondTrace.map (plugAt secondFrame 1)).getLast? =
            some (plugAt secondFrame 1 (Verb.ofNoun call2.result)) := by
        rw [List.getLast?_map, hsecondLast]
        rfl
      have hinitial :
          Verb.TraceOfROM (Verb.program data.root.subject data.root.formula)
            [Verb.program data.root.subject data.root.formula,
              plugAt secondFrame 1 secondRoot] := by
        refine ⟨rfl, ?_, trivial⟩
        simpa [secondFrame, secondRoot, Verb.program] using hsem.1
      obtain ⟨throughSecond, hthroughSecond, hthroughSecondLast⟩ :=
        concat_trace_with_last hinitial (by rfl) hmappedSecond hmappedSecondLast
      have hmappedFirst :
          Verb.TraceOfROM
            (plugAt rootHoleFrame 0 (Verb.program call2.result tail.tail))
            (firstTrace.map (plugAt rootHoleFrame 0)) :=
        traceOfROM_map_plugAt_of_frameLaw hfirst rootHoleFrame_maximalDFS
      have hmappedFirstLast :
          (firstTrace.map (plugAt rootHoleFrame 0)).getLast? =
            some (plugAt rootHoleFrame 0 (Verb.ofNoun call1.result)) := by
        rw [List.getLast?_map, hfirstLast]
        rfl
      have hphase :
          plugAt secondFrame 1 (Verb.ofNoun call2.result) =
            plugAt rootHoleFrame 0 (Verb.program call2.result tail.tail) := by
        simp [secondFrame, Verb.program]
      rw [hphase] at hthroughSecondLast
      obtain ⟨parentTrace, hparentTrace, hparentLast⟩ :=
        concat_trace_with_last hthroughSecond hthroughSecondLast
          hmappedFirst hmappedFirstLast
      rw [hresultEq]
      exact ⟨parentTrace, hparentTrace, by simpa using hparentLast⟩

def consLeftResult
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.cons, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Noun := by
  cases cert with
  | cons data fuel call1 call2 hstate hz hcast hformula h1s h1f h2s h2f
      hresult hcall1 hcall2 hv => exact call1.result

def consRightResult
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.cons, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Noun := by
  cases cert with
  | cons data fuel call1 call2 hstate hz hcast hformula h1s h1f h2s h2f
      hresult hcall1 hcall2 hv => exact call2.result

/-- Complete certified structural-cons execution in right-to-left maximal-DFS order.  There is no
operator postlude: terminal children form the terminal result cell directly. -/
theorem cons_complete_of_certificate_and_children
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.cons, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data)
    {leftTrace rightTrace : List Verb}
    (hleft : Verb.TraceOfROM
      (Verb.program data.root.subject data.root.head) leftTrace)
    (hleftLast :
      leftTrace.getLast? = some (Verb.ofNoun (consLeftResult cert)))
    (hright : Verb.TraceOfROM
      (Verb.program data.root.subject data.root.tail) rightTrace)
    (hrightLast :
      rightTrace.getLast? = some (Verb.ofNoun (consRightResult cert))) :
    ∃ parentTrace,
      Verb.TraceOfROM
        (Verb.program data.root.subject data.root.formula) parentTrace ∧
      parentTrace.getLast? = some (Verb.ofNoun data.root.result) := by
  cases cert with
  | cons data fuel call1 call2 hstate hz hcast hformula h1s h1f h2s h2f
      hresult hcall1 hcall2 hv =>
      change leftTrace.getLast? = some (Verb.ofNoun call1.result) at hleftLast
      change rightTrace.getLast? = some (Verb.ofNoun call2.result) at hrightLast
      have hsem :=
        OpcodeSemantics.cons_vcomp_semantics (fuel := fuel) hstate hz hcast data.root
          call1 call2 hformula.faithful h1s.faithful h1f.faithful
          h2s.faithful h2f.faithful hresult.faithful hcall1 hcall2 hv
      have hv' := hv
      obtain ⟨_, _, _, _, hevalV⟩ := hv'
      simp only [ComputeTable.evalV, hstate] at hevalV
      obtain ⟨_, _, _, _, heresult, _⟩ := hevalV
      have hresultEq : data.root.result = .cell call1.result call2.result := by
        apply hresult.faithful.eq_of_enc_eq hcast
        calc
          OpcodeSemantics.enc inp.z data.root.result = pub.e :=
            data.root.result_realizes.symm
          _ = FP.cons inp.z pub.sf1_e pub.sf2_e := heresult
          _ = FP.cons inp.z
              (OpcodeSemantics.enc inp.z call1.result)
              (OpcodeSemantics.enc inp.z call2.result) := by
            exact congrArg₂ (FP.cons inp.z)
              call1.result_realizes call2.result_realizes
          _ = OpcodeSemantics.enc inp.z (.cell call1.result call2.result) :=
            (GlobalCarryRecognizer.enc_cons hz call1.result call2.result).symm
      let leftRoot := Verb.program data.root.subject data.root.head
      let rightRoot := Verb.program data.root.subject data.root.tail
      let rightFrame := binaryRightFrame .null leftRoot
      let rightHole := binaryRightHole leftRoot
      let leftFrame := binaryLeftFrame .null call2.result
      have hmappedRight :
          Verb.TraceOfROM
            (plugAt rightFrame rightHole rightRoot)
            (rightTrace.map (plugAt rightFrame rightHole)) :=
        traceOfROM_map_plugAt_of_frameLaw hright
          (binaryRightFrame_maximalDFS .null leftRoot)
      have hmappedRightLast :
          (rightTrace.map (plugAt rightFrame rightHole)).getLast? =
            some (plugAt rightFrame rightHole (Verb.ofNoun call2.result)) := by
        rw [List.getLast?_map, hrightLast]
        rfl
      have hinitial :
          Verb.TraceOfROM (Verb.program data.root.subject data.root.formula)
            [Verb.program data.root.subject data.root.formula,
              plugAt rightFrame rightHole rightRoot] := by
        refine ⟨rfl, ?_, trivial⟩
        simpa [rightFrame, rightHole, leftRoot, rightRoot, Verb.program] using hsem.1
      obtain ⟨throughRight, hthroughRight, hthroughRightLast⟩ :=
        concat_trace_with_last hinitial (by rfl) hmappedRight hmappedRightLast
      have hmappedLeft :
          Verb.TraceOfROM
            (plugAt leftFrame 1 leftRoot)
            (leftTrace.map (plugAt leftFrame 1)) :=
        traceOfROM_map_plugAt_of_frameLaw hleft
          (binaryLeftFrame_maximalDFS .null call2.result)
      have hmappedLeftLast :
          (leftTrace.map (plugAt leftFrame 1)).getLast? =
            some (plugAt leftFrame 1 (Verb.ofNoun call1.result)) := by
        rw [List.getLast?_map, hleftLast]
        rfl
      have hphase :
          plugAt rightFrame rightHole (Verb.ofNoun call2.result) =
            plugAt leftFrame 1 leftRoot := by
        simp [rightFrame, rightHole, leftFrame]
      rw [hphase] at hthroughRightLast
      obtain ⟨parentTrace, hparentTrace, hparentLast⟩ :=
        concat_trace_with_last hthroughRight hthroughRightLast
          hmappedLeft hmappedLeftLast
      rw [hresultEq]
      exact ⟨parentTrace, hparentTrace,
        by simpa [leftFrame, Verb.ofNoun] using hparentLast⟩

def s2ChildRoot
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s2, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Fin 3 → Verb := by
  cases cert with
  | s2 data fuel tail call1 call2 call3 hstate hz hcast hhead hformula htail
      h1s h1f h2s h2f h3s h3f hresult hcall1 hcall2 hcall3 hv =>
      intro i
      exact Fin.cases
        (Verb.program data.root.subject tail.head)
        (Fin.cases
          (Verb.program data.root.subject tail.tail)
          (fun _ => Verb.program call1.result call2.result)) i

def s2ChildResult
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s2, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Fin 3 → Noun := by
  cases cert with
  | s2 data fuel tail call1 call2 call3 hstate hz hcast hhead hformula htail
      h1s h1f h2s h2f h3s h3f hresult hcall1 hcall2 hcall3 hv =>
      intro i
      exact Fin.cases call1.result
        (Fin.cases call2.result (fun _ => call3.result)) i

/-- Complete OP2's exact right-child, left-child, then root-call schedule. -/
theorem s2_complete_of_certificate_and_children
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s2, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data)
    (childTrace : Fin 3 → List Verb)
    (hchildren : ∀ i : Fin 3,
      Verb.TraceOfROM (s2ChildRoot cert i) (childTrace i) ∧
      (childTrace i).getLast? =
        some (Verb.ofNoun (s2ChildResult cert i))) :
    ∃ parentTrace,
      MaximalDFSTrace
        (Verb.program data.root.subject data.root.formula)
        data.root.result parentTrace := by
  cases cert with
  | s2 data fuel tail call1 call2 call3 hstate hz hcast hhead hformula htail
      h1s h1f h2s h2f h3s h3f hresult hcall1 hcall2 hcall3 hv =>
      have hc0 := hchildren (0 : Fin 3)
      have hc1 := hchildren (1 : Fin 3)
      have hc2 := hchildren (2 : Fin 3)
      simp only [s2ChildRoot, s2ChildResult] at hc0 hc1 hc2
      have hsem :=
        OpcodeSemantics.s2_vcomp_semantics (fuel := fuel) hstate hz hcast data.root
          tail call1 call2 call3 hhead.faithful hformula.faithful htail.faithful
          h1s.faithful h1f.faithful h2s.faithful h2f.faithful
          h3s.faithful h3f.faithful hresult.faithful
          hcall1 hcall2 hcall3 hv
      have hv' := hv
      obtain ⟨_, _, _, _, hevalV⟩ := hv'
      simp only [ComputeTable.evalV, hstate] at hevalV
      have hresultEq : data.root.result = call3.result :=
        OpcodeSemantics.noun_eq_of_realizes_eq data.root.result_realizes
          call3.result_realizes hevalV.2.2.2.2.2.2 hcast hresult.faithful
      let root0 := Verb.program data.root.subject tail.head
      let root1 := Verb.program data.root.subject tail.tail
      let root2 := Verb.program call1.result call2.result
      let frame1 := binaryRightFrame .star root0
      let hole1 := binaryRightHole root0
      let frame0 := binaryLeftFrame .star call2.result
      have mapped1 :=
        traceOfROM_map_plugAt_of_frameLaw hc1.1
          (binaryRightFrame_maximalDFS .star root0)
      have mapped1Last :
          ((childTrace 1).map (plugAt frame1 hole1)).getLast? =
            some (plugAt frame1 hole1 (Verb.ofNoun call2.result)) := by
        rw [List.getLast?_map, hc1.2]
        rfl
      have hinitial :
          Verb.TraceOfROM (Verb.program data.root.subject data.root.formula)
            [Verb.program data.root.subject data.root.formula,
              plugAt frame1 hole1 root1] := by
        refine ⟨rfl, ?_, trivial⟩
        simpa [frame1, hole1, root0, root1, Verb.program] using hsem.1
      obtain ⟨through1, hthrough1, hthrough1Last⟩ :=
        concat_trace_with_last hinitial (by rfl) mapped1 mapped1Last
      have mapped0 :=
        traceOfROM_map_plugAt_of_frameLaw hc0.1
          (binaryLeftFrame_maximalDFS .star call2.result)
      have mapped0Last :
          ((childTrace 0).map (plugAt frame0 1)).getLast? =
            some (plugAt frame0 1 (Verb.ofNoun call1.result)) := by
        rw [List.getLast?_map, hc0.2]
        rfl
      have hphase10 :
          plugAt frame1 hole1 (Verb.ofNoun call2.result) =
            plugAt frame0 1 root0 := by
        simp [frame1, hole1, frame0]
      rw [hphase10] at hthrough1Last
      obtain ⟨through0, hthrough0, hthrough0Last⟩ :=
        concat_trace_with_last hthrough1 hthrough1Last mapped0 mapped0Last
      have mapped2 :=
        traceOfROM_map_plugAt_of_frameLaw hc2.1 rootHoleFrame_maximalDFS
      have mapped2Last :
          ((childTrace 2).map (plugAt rootHoleFrame 0)).getLast? =
            some (plugAt rootHoleFrame 0 (Verb.ofNoun call3.result)) := by
        rw [List.getLast?_map, hc2.2]
        rfl
      have hphase02 :
          plugAt frame0 1 (Verb.ofNoun call1.result) =
            plugAt rootHoleFrame 0 root2 := by
        simp [frame0, root2, Verb.program]
      rw [hphase02] at hthrough0Last
      obtain ⟨parentTrace, hparentTrace, hparentLast⟩ :=
        concat_trace_with_last hthrough0 hthrough0Last mapped2 mapped2Last
      rw [hresultEq]
      exact ⟨parentTrace,
        maximalDFSTrace_of_traceOfROM hparentTrace (by simpa using hparentLast)⟩

def s8ChildRoot
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s8, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Fin 2 → Verb := by
  cases cert with
  | s8 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h2s h2f h1s h1f hresult hcall1 hcall2 hv =>
      exact Fin.cases
        (Verb.program (.cell call2.result data.root.subject) tail.tail)
        (fun _ => Verb.program data.root.subject tail.head)

def s8ChildResult
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s8, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Fin 2 → Noun := by
  cases cert with
  | s8 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h2s h2f h1s h1f hresult hcall1 hcall2 hv =>
      exact Fin.cases call1.result (fun _ => call2.result)

/-- Complete OP8 by lifting call 2 through the inner null frame and then the outer star frame,
before running call 1 as the whole program. -/
theorem s8_complete_of_certificate_and_children
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s8, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data)
    (childTrace : Fin 2 → List Verb)
    (hchildren : ∀ i : Fin 2,
      Verb.TraceOfROM (s8ChildRoot cert i) (childTrace i) ∧
      (childTrace i).getLast? =
        some (Verb.ofNoun (s8ChildResult cert i))) :
    ∃ parentTrace,
      MaximalDFSTrace
        (Verb.program data.root.subject data.root.formula)
        data.root.result parentTrace := by
  cases cert with
  | s8 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h2s h2f h1s h1f hresult hcall1 hcall2 hv =>
      have hc0 := hchildren (0 : Fin 2)
      have hc1 := hchildren (1 : Fin 2)
      simp only [s8ChildRoot, s8ChildResult] at hc0 hc1
      have hsem :=
        OpcodeSemantics.s8_vcomp_semantics (fuel := fuel) hstate hz hcast data.root
          tail call1 call2 hhead.faithful hformula.faithful htail.faithful
          h2s.faithful h2f.faithful h1s.faithful h1f.faithful
          hresult.faithful hcall1 hcall2 hv
      have hv' := hv
      obtain ⟨_, _, _, _, hevalV⟩ := hv'
      simp only [ComputeTable.evalV, hstate] at hevalV
      obtain ⟨_, _, heresult, _, _, _⟩ := hevalV
      have hresultEq : data.root.result = call1.result :=
        OpcodeSemantics.noun_eq_of_realizes_eq data.root.result_realizes
          call1.result_realizes heresult hcast hresult.faithful
      let root1 := Verb.program data.root.subject tail.head
      let root0 := Verb.program (.cell call2.result data.root.subject) tail.tail
      let innerFrame := binaryLeftFrame .null data.root.subject
      let outerFrame := binaryLeftFrame .star tail.tail
      have hinner :
          Verb.TraceOfROM
            (plugAt innerFrame 1 root1)
            ((childTrace 1).map (plugAt innerFrame 1)) :=
        traceOfROM_map_plugAt_of_frameLaw hc1.1
          (binaryLeftFrame_maximalDFS .null data.root.subject)
      have hinnerLast :
          ((childTrace 1).map (plugAt innerFrame 1)).getLast? =
            some (plugAt innerFrame 1 (Verb.ofNoun call2.result)) := by
        rw [List.getLast?_map, hc1.2]
        rfl
      have houter :
          Verb.TraceOfROM
            (plugAt outerFrame 1 (plugAt innerFrame 1 root1))
            (((childTrace 1).map (plugAt innerFrame 1)).map
              (plugAt outerFrame 1)) :=
        traceOfROM_map_plugAt_of_frameLaw hinner
          (binaryLeftFrame_maximalDFS .star tail.tail)
      have houterLast :
          (((childTrace 1).map (plugAt innerFrame 1)).map
            (plugAt outerFrame 1)).getLast? =
            some (plugAt outerFrame 1
              (plugAt innerFrame 1 (Verb.ofNoun call2.result))) := by
        rw [List.getLast?_map, hinnerLast]
        rfl
      have hinitial :
          Verb.TraceOfROM (Verb.program data.root.subject data.root.formula)
            [Verb.program data.root.subject data.root.formula,
              plugAt outerFrame 1 (plugAt innerFrame 1 root1)] := by
        refine ⟨rfl, ?_, trivial⟩
        simpa [outerFrame, innerFrame, root1, Verb.program] using hsem.1
      obtain ⟨through1, hthrough1, hthrough1Last⟩ :=
        concat_trace_with_last hinitial (by rfl) houter houterLast
      have mapped0 :=
        traceOfROM_map_plugAt_of_frameLaw hc0.1 rootHoleFrame_maximalDFS
      have mapped0Last :
          ((childTrace 0).map (plugAt rootHoleFrame 0)).getLast? =
            some (plugAt rootHoleFrame 0 (Verb.ofNoun call1.result)) := by
        rw [List.getLast?_map, hc0.2]
        rfl
      have hphase :
          plugAt outerFrame 1
              (plugAt innerFrame 1 (Verb.ofNoun call2.result)) =
            plugAt rootHoleFrame 0 root0 := by
        simp [outerFrame, innerFrame, root0, Verb.program, Verb.ofNoun]
      rw [hphase] at hthrough1Last
      obtain ⟨parentTrace, hparentTrace, hparentLast⟩ :=
        concat_trace_with_last hthrough1 hthrough1Last mapped0 mapped0Last
      rw [hresultEq]
      exact ⟨parentTrace,
        maximalDFSTrace_of_traceOfROM hparentTrace (by simpa using hparentLast)⟩

def s9MacroFormula (axis : ℕ) : Noun :=
  .cell (.atom 2)
    (.cell (.cell (.atom 0) (.atom 1)) (.cell (.atom 0) (.atom axis)))

def s9ChildRoot
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s9, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Fin 2 → Verb := by
  cases cert with
  | s9 data fuel axis tail call1 call2 hstate hz hcast hhead hformula htail
      haxis h1s h1f h2s hresult hmr hserved hcall1 hcall2 hv =>
      exact Fin.cases
        (Verb.program data.root.subject tail.tail)
        (fun _ => Verb.program call1.result call2.formula)

def s9ChildResult
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s9, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Fin 2 → Noun := by
  cases cert with
  | s9 data fuel axis tail call1 call2 hstate hz hcast hhead hformula htail
      haxis h1s h1f h2s hresult hmr hserved hcall1 hcall2 hv =>
      exact Fin.cases call1.result (fun _ => call2.result)

/-- Complete OP9: evaluate the core child, execute the fixed OP2/slot axis macro, then evaluate the
axis-selected child as the whole program. -/
theorem s9_complete_of_certificate_and_children
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s9, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data)
    (childTrace : Fin 2 → List Verb)
    (hchildren : ∀ i : Fin 2,
      Verb.TraceOfROM (s9ChildRoot cert i) (childTrace i) ∧
      (childTrace i).getLast? =
        some (Verb.ofNoun (s9ChildResult cert i))) :
    ∃ parentTrace,
      MaximalDFSTrace
        (Verb.program data.root.subject data.root.formula)
        data.root.result parentTrace := by
  cases cert with
  | s9 data fuel axis tail call1 call2 hstate hz hcast hhead hformula htail
      haxis h1s h1f h2s hresult hmr hserved hcall1 hcall2 hv =>
      have hc0 := hchildren (0 : Fin 2)
      have hc1 := hchildren (1 : Fin 2)
      simp only [s9ChildRoot, s9ChildResult] at hc0 hc1
      have hsem :=
        OpcodeSemantics.s9_vcomp_semantics (fuel := fuel) hstate hz hcast data.root
          tail call1 call2 hhead.faithful hformula.faithful htail.faithful
          haxis.faithful h1s.faithful h1f.faithful h2s.faithful
          hresult.faithful hmr hserved hcall1 hcall2 hv
      have hv' := hv
      obtain ⟨_, _, _, _, hevalV⟩ := hv'
      simp only [ComputeTable.evalV, hstate] at hevalV
      have hresultEq : data.root.result = call2.result :=
        OpcodeSemantics.noun_eq_of_realizes_eq data.root.result_realizes
          call2.result_realizes hevalV.2.2.2.1 hcast hresult.faithful
      have hslot : Noun.slot axis call1.result = some call2.formula :=
        GlobalCarryRecognizer.axis_sound_recognizer' call1.result hserved
      let fixed := s9MacroFormula axis
      let root0 := Verb.program data.root.subject tail.tail
      let root1 := Verb.program call1.result call2.formula
      let coreFrame := binaryLeftFrame .star fixed
      have mapped0 :=
        traceOfROM_map_plugAt_of_frameLaw hc0.1
          (binaryLeftFrame_maximalDFS .star fixed)
      have mapped0Last :
          ((childTrace 0).map (plugAt coreFrame 1)).getLast? =
            some (plugAt coreFrame 1 (Verb.ofNoun call1.result)) := by
        rw [List.getLast?_map, hc0.2]
        rfl
      have hinitial :
          Verb.TraceOfROM (Verb.program data.root.subject data.root.formula)
            [Verb.program data.root.subject data.root.formula,
              plugAt coreFrame 1 root0] := by
        refine ⟨rfl, ?_, trivial⟩
        simpa [coreFrame, fixed, s9MacroFormula, root0, Verb.program, Verb.ofNoun]
          using hsem.1
      obtain ⟨throughCore, hthroughCore, hthroughCoreLast⟩ :=
        concat_trace_with_last hinitial (by rfl) mapped0 mapped0Last
      let macroRoot := Verb.program call1.result fixed
      let slotLeftFormula : Noun := .cell (.atom 0) (.atom 1)
      let slotRightFormula : Noun := .cell (.atom 0) (.atom axis)
      let slotLeftRoot := Verb.program call1.result slotLeftFormula
      let slotRightRoot := Verb.program call1.result slotRightFormula
      have hphaseCore :
          plugAt coreFrame 1 (Verb.ofNoun call1.result) = macroRoot := by
        simp [coreFrame, macroRoot, fixed, Verb.program]
      rw [hphaseCore] at hthroughCoreLast
      have hmacroStep :
          Verb.TraceOfROM macroRoot
            [macroRoot, .node .star slotLeftRoot slotRightRoot] := by
        refine ⟨rfl, ?_, trivial⟩
        simpa [macroRoot, fixed, s9MacroFormula, slotLeftFormula,
          slotRightFormula, slotLeftRoot, slotRightRoot, Verb.program] using
          OpcodeSemantics.stepROM_s2_exact call1.result slotLeftFormula slotRightFormula
      obtain ⟨throughMacro, hthroughMacro, hthroughMacroLast⟩ :=
        concat_trace_with_last hthroughCore hthroughCoreLast hmacroStep (by rfl)
      have hrightSlot :
          Verb.TraceOfROM slotRightRoot
            [slotRightRoot,
              .node .slot (Verb.ofNoun (.atom axis)) (Verb.ofNoun call1.result),
              Verb.ofNoun call2.formula] := by
        apply traceOfROM_of_dfsSchedule (by rfl)
        simpa [slotRightRoot, slotRightFormula] using
          s0_complete_schedule call1.result axis call2.formula hslot
      let rightFrame := binaryRightFrame .star slotLeftRoot
      let rightHole := binaryRightHole slotLeftRoot
      have mappedRight :=
        traceOfROM_map_plugAt_of_frameLaw hrightSlot
          (binaryRightFrame_maximalDFS .star slotLeftRoot)
      have mappedRightLast :
          ([slotRightRoot,
              .node .slot (Verb.ofNoun (.atom axis)) (Verb.ofNoun call1.result),
              Verb.ofNoun call2.formula].map
                (plugAt rightFrame rightHole)).getLast? =
            some (plugAt rightFrame rightHole (Verb.ofNoun call2.formula)) := by
        rfl
      have hstartRight :
          (.node .star slotLeftRoot slotRightRoot : Verb) =
            plugAt rightFrame rightHole slotRightRoot := by
        simp [rightFrame, rightHole]
      rw [hstartRight] at hthroughMacroLast
      obtain ⟨throughRight, hthroughRight, hthroughRightLast⟩ :=
        concat_trace_with_last hthroughMacro hthroughMacroLast
          mappedRight mappedRightLast
      have hslotOne : Noun.slot 1 call1.result = some call1.result := by
        simp [Noun.slot]
      have hleftSlot :
          Verb.TraceOfROM slotLeftRoot
            [slotLeftRoot,
              .node .slot (Verb.ofNoun (.atom 1)) (Verb.ofNoun call1.result),
              Verb.ofNoun call1.result] := by
        apply traceOfROM_of_dfsSchedule (by rfl)
        simpa [slotLeftRoot, slotLeftFormula] using
          s0_complete_schedule call1.result 1 call1.result hslotOne
      let leftFrame := binaryLeftFrame .star call2.formula
      have mappedLeft :=
        traceOfROM_map_plugAt_of_frameLaw hleftSlot
          (binaryLeftFrame_maximalDFS .star call2.formula)
      have mappedLeftLast :
          ([slotLeftRoot,
              .node .slot (Verb.ofNoun (.atom 1)) (Verb.ofNoun call1.result),
              Verb.ofNoun call1.result].map (plugAt leftFrame 1)).getLast? =
            some (plugAt leftFrame 1 (Verb.ofNoun call1.result)) := by
        rfl
      have hphaseRight :
          plugAt rightFrame rightHole (Verb.ofNoun call2.formula) =
            plugAt leftFrame 1 slotLeftRoot := by
        simp [rightFrame, rightHole, leftFrame]
      rw [hphaseRight] at hthroughRightLast
      obtain ⟨throughLeft, hthroughLeft, hthroughLeftLast⟩ :=
        concat_trace_with_last hthroughRight hthroughRightLast
          mappedLeft mappedLeftLast
      have mapped1 :=
        traceOfROM_map_plugAt_of_frameLaw hc1.1 rootHoleFrame_maximalDFS
      have mapped1Last :
          ((childTrace 1).map (plugAt rootHoleFrame 0)).getLast? =
            some (plugAt rootHoleFrame 0 (Verb.ofNoun call2.result)) := by
        rw [List.getLast?_map, hc1.2]
        rfl
      have hphaseLeft :
          plugAt leftFrame 1 (Verb.ofNoun call1.result) =
            plugAt rootHoleFrame 0 root1 := by
        simp [leftFrame, root1, Verb.program]
      rw [hphaseLeft] at hthroughLeftLast
      obtain ⟨parentTrace, hparentTrace, hparentLast⟩ :=
        concat_trace_with_last hthroughLeft hthroughLeftLast mapped1 mapped1Last
      rw [hresultEq]
      exact ⟨parentTrace,
        maximalDFSTrace_of_traceOfROM hparentTrace (by simpa using hparentLast)⟩

private theorem lift_trace_with_last
    {root result : Verb} {trace : List Verb} {frame : Verb} {hole : ℕ}
    (hframe : MaximalDFSFrameLaw frame hole)
    (htrace : Verb.TraceOfROM root trace)
    (hlast : trace.getLast? = some result) :
    Verb.TraceOfROM (plugAt frame hole root) (trace.map (plugAt frame hole)) ∧
    (trace.map (plugAt frame hole)).getLast? =
      some (plugAt frame hole result) := by
  constructor
  · exact traceOfROM_map_plugAt_of_frameLaw htrace hframe
  · rw [List.getLast?_map, hlast]
    rfl

def s6OuterWrap (subject yesBranch noBranch : Noun) (inner : Verb) : Verb :=
  .node .star (Verb.ofNoun subject)
    (.node .star (Verb.ofNoun (.cell yesBranch noBranch))
      (.node .null (.leaf 0)
        (.node .star (Verb.ofNoun (.cell (.atom 2) (.atom 3)))
          (.node .null (.leaf 0) inner))))

def s6CWrap (subject yesBranch noBranch : Noun) (c0 : Verb) : Verb :=
  .node .star (Verb.ofNoun subject)
    (.node .star (Verb.ofNoun (.cell yesBranch noBranch))
      (.node .null (.leaf 0) c0))

def s6AWrap (subject : Noun) (a0 : Verb) : Verb :=
  .node .star (Verb.ofNoun subject) a0

private theorem lift_s6Outer
    {root result : Verb} {trace : List Verb}
    (subject yesBranch noBranch : Noun)
    (htrace : Verb.TraceOfROM root trace)
    (hlast : trace.getLast? = some result) :
    ∃ lifted,
      Verb.TraceOfROM (s6OuterWrap subject yesBranch noBranch root) lifted ∧
      lifted.getLast? =
        some (s6OuterWrap subject yesBranch noBranch result) := by
  obtain ⟨h1, h1last⟩ :=
    lift_trace_with_last (unaryRightFrame_maximalDFS .null 0) htrace hlast
  obtain ⟨h2, h2last⟩ :=
    lift_trace_with_last
      (binaryRightFrame_maximalDFS .star
        (Verb.ofNoun (.cell (.atom 2) (.atom 3)))) h1 h1last
  obtain ⟨h3, h3last⟩ :=
    lift_trace_with_last (unaryRightFrame_maximalDFS .null 0) h2 h2last
  obtain ⟨h4, h4last⟩ :=
    lift_trace_with_last
      (binaryRightFrame_maximalDFS .star
        (Verb.ofNoun (.cell yesBranch noBranch))) h3 h3last
  obtain ⟨h5, h5last⟩ :=
    lift_trace_with_last
      (binaryRightFrame_maximalDFS .star (Verb.ofNoun subject)) h4 h4last
  exact ⟨_, by simpa [s6OuterWrap] using h5, by simpa [s6OuterWrap] using h5last⟩

private theorem lift_s6C
    {root result : Verb} {trace : List Verb}
    (subject yesBranch noBranch : Noun)
    (htrace : Verb.TraceOfROM root trace)
    (hlast : trace.getLast? = some result) :
    ∃ lifted,
      Verb.TraceOfROM (s6CWrap subject yesBranch noBranch root) lifted ∧
      lifted.getLast? = some (s6CWrap subject yesBranch noBranch result) := by
  obtain ⟨h1, h1last⟩ :=
    lift_trace_with_last (unaryRightFrame_maximalDFS .null 0) htrace hlast
  obtain ⟨h2, h2last⟩ :=
    lift_trace_with_last
      (binaryRightFrame_maximalDFS .star
        (Verb.ofNoun (.cell yesBranch noBranch))) h1 h1last
  obtain ⟨h3, h3last⟩ :=
    lift_trace_with_last
      (binaryRightFrame_maximalDFS .star (Verb.ofNoun subject)) h2 h2last
  exact ⟨_, by simpa [s6CWrap] using h3, by simpa [s6CWrap] using h3last⟩

private theorem lift_s6A
    {root result : Verb} {trace : List Verb}
    (subject : Noun)
    (htrace : Verb.TraceOfROM root trace)
    (hlast : trace.getLast? = some result) :
    ∃ lifted,
      Verb.TraceOfROM (s6AWrap subject root) lifted ∧
      lifted.getLast? = some (s6AWrap subject result) := by
  obtain ⟨h, hlast'⟩ :=
    lift_trace_with_last
      (binaryRightFrame_maximalDFS .star (Verb.ofNoun subject)) htrace hlast
  exact ⟨_, by simpa [s6AWrap] using h, by simpa [s6AWrap] using hlast'⟩

private theorem s6_inner_prefix (subject condition : Noun) :
    let inner2 := Verb.program subject (.cell (.atom 4) condition)
    let child := Verb.program subject condition
    Verb.TraceOfROM
      (Verb.program subject (.cell (.atom 4) (.cell (.atom 4) condition)))
      [ Verb.program subject (.cell (.atom 4) (.cell (.atom 4) condition)),
        .node .minus (.leaf 4) inner2,
        .node .minus (.leaf 4) (.node .minus (.leaf 4) child) ] := by
  dsimp
  refine ⟨rfl, OpcodeSemantics.stepROM_s4_exact subject (.cell (.atom 4) condition),
    ?_, trivial⟩
  exact (s4_child_maximalDFS
    (selectedROMRewrite_iff_stepROM.mpr
      (OpcodeSemantics.stepROM_s4_exact subject condition))).stepROM

private theorem s6_increment_postlude (bit : ℕ) :
    Verb.TraceOfROM
      (.node .minus (.leaf 4)
        (.node .minus (.leaf 4) (Verb.ofNoun (.atom bit))))
      [ .node .minus (.leaf 4)
          (.node .minus (.leaf 4) (Verb.ofNoun (.atom bit))),
        .node .minus (.leaf 4) (Verb.ofNoun (.atom (bit + 1))),
        Verb.ofNoun (.atom (bit + 2)) ] := by
  have hinner : Noun.lus (.atom bit) = some (.atom (bit + 1)) := by
    rfl
  have houter : Noun.lus (.atom (bit + 1)) = some (.atom (bit + 2)) := by
    simp [Noun.lus, Nat.add_comm, Nat.add_left_comm]
  refine ⟨rfl, ?_, stepROM_lus_terminal houter, trivial⟩
  exact (s4_child_maximalDFS
    (selectedROMRewrite_iff_stepROM.mpr (stepROM_lus_terminal hinner))).stepROM

private theorem s6_assemble
    (subject condition yesBranch noBranch selectedBranch branchResult : Noun)
    (bit : ℕ)
    {conditionTrace branchTrace : List Verb}
    (hinitial : Verb.StepROM
      (Verb.program subject
        (.cell (.atom 6) (.cell condition (.cell yesBranch noBranch))))
      (OpcodeSemantics.s6Successor subject condition yesBranch noBranch))
    (hcondition : Verb.TraceOfROM (Verb.program subject condition) conditionTrace)
    (hconditionLast :
      conditionTrace.getLast? = some (Verb.ofNoun (.atom bit)))
    (hselectedAxis :
      Noun.slot (bit + 2) (.cell (.atom 2) (.atom 3)) =
        some (.atom (bit + 2)))
    (hselectedBranch :
      Noun.slot (bit + 2) (.cell yesBranch noBranch) = some selectedBranch)
    (hbranch : Verb.TraceOfROM
      (Verb.program subject selectedBranch) branchTrace)
    (hbranchLast : branchTrace.getLast? = some (Verb.ofNoun branchResult)) :
    ∃ trace,
      Verb.TraceOfROM
        (Verb.program subject
          (.cell (.atom 6) (.cell condition (.cell yesBranch noBranch)))) trace ∧
      trace.getLast? = some (Verb.ofNoun branchResult) := by
  let innerRoot :=
    Verb.program subject (.cell (.atom 4) (.cell (.atom 4) condition))
  let childRoot := Verb.program subject condition
  let nestedChild : Verb :=
    .node .minus (.leaf 4) (.node .minus (.leaf 4) childRoot)
  have hprefix := s6_inner_prefix subject condition
  have hprefixLast :
      [ Verb.program subject (.cell (.atom 4) (.cell (.atom 4) condition)),
        .node .minus (.leaf 4)
          (Verb.program subject (.cell (.atom 4) condition)),
        .node .minus (.leaf 4)
          (.node .minus (.leaf 4) (Verb.program subject condition)) ].getLast? =
        some nestedChild := by
    rfl
  obtain ⟨prefixLifted, hprefixLifted, hprefixLiftedLast⟩ :=
    lift_s6Outer subject yesBranch noBranch hprefix hprefixLast
  have hinitialTrace :
      Verb.TraceOfROM
        (Verb.program subject
          (.cell (.atom 6) (.cell condition (.cell yesBranch noBranch))))
        [Verb.program subject
            (.cell (.atom 6) (.cell condition (.cell yesBranch noBranch))),
          s6OuterWrap subject yesBranch noBranch innerRoot] := by
    refine ⟨rfl, ?_, trivial⟩
    simpa [s6OuterWrap, innerRoot, OpcodeSemantics.s6Successor, Verb.program,
      Verb.ofNoun] using hinitial
  obtain ⟨throughPrefix, hthroughPrefix, hthroughPrefixLast⟩ :=
    concat_trace_with_last hinitialTrace (by rfl)
      hprefixLifted hprefixLiftedLast
  obtain ⟨hminus1, hminus1Last⟩ :=
    lift_trace_with_last (unaryRightFrame_maximalDFS .minus 4)
      hcondition hconditionLast
  obtain ⟨hminus2, hminus2Last⟩ :=
    lift_trace_with_last (unaryRightFrame_maximalDFS .minus 4)
      hminus1 hminus1Last
  obtain ⟨conditionLifted, hconditionLifted, hconditionLiftedLast⟩ :=
    lift_s6Outer subject yesBranch noBranch hminus2 hminus2Last
  have hphasePrefix :
      s6OuterWrap subject yesBranch noBranch nestedChild =
        s6OuterWrap subject yesBranch noBranch
          (plugAt (unaryRightFrame .minus 4) 1
            (plugAt (unaryRightFrame .minus 4) 1 childRoot)) := by
    simp [nestedChild, childRoot]
  rw [hphasePrefix] at hthroughPrefixLast
  obtain ⟨throughCondition, hthroughCondition, hthroughConditionLast⟩ :=
    concat_trace_with_last hthroughPrefix hthroughPrefixLast
      hconditionLifted hconditionLiftedLast
  have hpost := s6_increment_postlude bit
  have hpostLast :
      [ .node .minus (.leaf 4)
          (.node .minus (.leaf 4) (Verb.ofNoun (.atom bit))),
        .node .minus (.leaf 4) (Verb.ofNoun (.atom (bit + 1))),
        Verb.ofNoun (.atom (bit + 2)) ].getLast? =
        some (Verb.ofNoun (.atom (bit + 2))) := by
    rfl
  obtain ⟨postLifted, hpostLifted, hpostLiftedLast⟩ :=
    lift_s6Outer subject yesBranch noBranch hpost hpostLast
  have hconditionEndpoint :
      s6OuterWrap subject yesBranch noBranch
          (plugAt (unaryRightFrame .minus 4) 1
            (plugAt (unaryRightFrame .minus 4) 1 (Verb.ofNoun (.atom bit)))) =
        s6OuterWrap subject yesBranch noBranch
          (.node .minus (.leaf 4)
            (.node .minus (.leaf 4) (Verb.ofNoun (.atom bit)))) := by
    rfl
  rw [hconditionEndpoint] at hthroughConditionLast
  obtain ⟨throughPost, hthroughPost, hthroughPostLast⟩ :=
    concat_trace_with_last hthroughCondition hthroughConditionLast
      hpostLifted hpostLiftedLast
  let axis := bit + 2
  let c0Root :=
    Verb.program (.cell (.atom 2) (.atom 3)) (.cell (.atom 0) (.atom axis))
  have hc0 :
      Verb.TraceOfROM c0Root
        [ c0Root,
          .node .slot (Verb.ofNoun (.atom axis))
            (Verb.ofNoun (.cell (.atom 2) (.atom 3))),
          Verb.ofNoun (.atom axis) ] := by
    apply traceOfROM_of_dfsSchedule (by rfl)
    simpa [c0Root, axis] using
      s0_complete_schedule (.cell (.atom 2) (.atom 3)) axis (.atom axis)
        (by simpa [axis] using hselectedAxis)
  have hc0Last :
      [ c0Root,
        .node .slot (Verb.ofNoun (.atom axis))
          (Verb.ofNoun (.cell (.atom 2) (.atom 3))),
        Verb.ofNoun (.atom axis) ].getLast? =
        some (Verb.ofNoun (.atom axis)) := by
    rfl
  obtain ⟨c0Lifted, hc0Lifted, hc0LiftedLast⟩ :=
    lift_s6C subject yesBranch noBranch hc0 hc0Last
  have hphaseC :
      s6OuterWrap subject yesBranch noBranch (Verb.ofNoun (.atom axis)) =
        s6CWrap subject yesBranch noBranch c0Root := by
    simp [s6OuterWrap, s6CWrap, c0Root, axis, Verb.program, Verb.ofNoun]
  rw [hphaseC] at hthroughPostLast
  obtain ⟨throughC, hthroughC, hthroughCLast⟩ :=
    concat_trace_with_last hthroughPost hthroughPostLast hc0Lifted hc0LiftedLast
  let a0Root :=
    Verb.program (.cell yesBranch noBranch) (.cell (.atom 0) (.atom axis))
  have ha0 :
      Verb.TraceOfROM a0Root
        [ a0Root,
          .node .slot (Verb.ofNoun (.atom axis))
            (Verb.ofNoun (.cell yesBranch noBranch)),
          Verb.ofNoun selectedBranch ] := by
    apply traceOfROM_of_dfsSchedule (by rfl)
    simpa [a0Root, axis] using
      s0_complete_schedule (.cell yesBranch noBranch) axis selectedBranch
        (by simpa [axis] using hselectedBranch)
  have ha0Last :
      [ a0Root,
        .node .slot (Verb.ofNoun (.atom axis))
          (Verb.ofNoun (.cell yesBranch noBranch)),
        Verb.ofNoun selectedBranch ].getLast? =
        some (Verb.ofNoun selectedBranch) := by
    rfl
  obtain ⟨a0Lifted, ha0Lifted, ha0LiftedLast⟩ :=
    lift_s6A subject ha0 ha0Last
  have hphaseA :
      s6CWrap subject yesBranch noBranch (Verb.ofNoun (.atom axis)) =
        s6AWrap subject a0Root := by
    simp [s6CWrap, s6AWrap, a0Root, axis, Verb.program, Verb.ofNoun]
  rw [hphaseA] at hthroughCLast
  obtain ⟨throughA, hthroughA, hthroughALast⟩ :=
    concat_trace_with_last hthroughC hthroughCLast ha0Lifted ha0LiftedLast
  have hphaseBranch :
      s6AWrap subject (Verb.ofNoun selectedBranch) =
        Verb.program subject selectedBranch := by
    rfl
  rw [hphaseBranch] at hthroughALast
  exact concat_trace_with_last hthroughA hthroughALast hbranch hbranchLast

def s6ChildRoot
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s6, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Fin 2 → Verb := by
  cases cert with
  | s6 data fuel tail branch call1 call2 hstate hz hq hcast hhead hformula
      htail hbranchTail h1s h1fZero h1fOne h2s h2f hresult hconditionBound
      hconditionSize hcall1 hcall2 hv =>
      exact Fin.cases
        (Verb.program call1.subject call1.formula)
        (fun _ => Verb.program call2.subject call2.formula)

def s6ChildResult
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s6, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) : Fin 2 → Noun := by
  cases cert with
  | s6 data fuel tail branch call1 call2 hstate hz hq hcast hhead hformula
      htail hbranchTail h1s h1fZero h1fOne h2s h2f hresult hconditionBound
      hconditionSize hcall1 hcall2 hv =>
      exact Fin.cases call1.result (fun _ => call2.result)

/-- Complete certified OP6 by proving the condition is exactly 0 or 1, selecting the corresponding
branch child, and executing the finite macro trace assembled above. -/
theorem s6_complete_of_certificate_and_children
    {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {data : ComputeRowSemanticData q Λ (.s6, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data)
    (childTrace : Fin 2 → List Verb)
    (hchildren : ∀ i : Fin 2,
      Verb.TraceOfROM (s6ChildRoot cert i) (childTrace i) ∧
      (childTrace i).getLast? =
        some (Verb.ofNoun (s6ChildResult cert i))) :
    ∃ parentTrace,
      MaximalDFSTrace
        (Verb.program data.root.subject data.root.formula)
        data.root.result parentTrace := by
  cases cert with
  | s6 data fuel tail branch call1 call2 hstate hz hq hcast hhead hformula
      htail hbranchTail h1s h1fZero h1fOne h2s h2f hresult hconditionBound
      hconditionSize hcall1 hcall2 hv =>
      have hc0 := hchildren (0 : Fin 2)
      have hc1 := hchildren (1 : Fin 2)
      simp only [s6ChildRoot, s6ChildResult] at hc0 hc1
      have hsem :=
        OpcodeSemantics.s6_vcomp_semantics (fuel := fuel) hstate hz hq hcast
          data.root tail branch call1 call2 hhead.faithful hformula.faithful
          htail.faithful hbranchTail.faithful h1s.faithful h1fZero.faithful
          h1fOne.faithful h2s.faithful h2f.faithful hresult.faithful
          hconditionBound hconditionSize hcall1 hcall2 hv
      have hv' := hv
      obtain ⟨_, _, _, hmem, hevalV⟩ := hv'
      simp only [ComputeTable.memBlk, hstate] at hmem
      obtain ⟨_, hconsTail, _, hconsBranch, _⟩ := hmem
      have htailEq : data.root.tail = .cell tail.head tail.tail :=
        OpcodeSemantics.realized_tail_eq_cell hz hcast data.root tail
          htail.faithful hconsTail
      have hbranchEq : tail.tail = .cell branch.head branch.tail :=
        OpcodeSemantics.realized_branch_tail_eq_cell hz hcast tail branch
          hbranchTail.faithful hconsBranch
      have hnumeric :=
        OpcodeSemantics.numeric_formula_eq hstate (by decide) hz hcast data.root
          hhead.faithful hformula.faithful hv
      change data.root.formula = .cell (.atom 6) data.root.tail at hnumeric
      have hrootFormula :
          data.root.formula =
            .cell (.atom 6) (.cell tail.head (.cell branch.head branch.tail)) := by
        rw [hnumeric, htailEq, hbranchEq]
      simp only [ComputeTable.evalV, hstate] at hevalV
      have he1s := hevalV.1
      have he1f := hevalV.2.1
      have heresult := hevalV.2.2.1
      have he2s := hevalV.2.2.2.1
      have he2f := hevalV.2.2.2.2.1
      have hconditionFPSize := hevalV.2.2.2.2.2.1
      have hconditionLeaf := hevalV.2.2.2.2.2.2.2.1
      have h1sEq : call1.subject = data.root.subject :=
        OpcodeSemantics.noun_eq_of_realizes_eq call1.subject_realizes
          data.root.subject_realizes he1s hcast h1s.faithful
      have h2sEq : call2.subject = data.root.subject :=
        OpcodeSemantics.noun_eq_of_realizes_eq call2.subject_realizes
          data.root.subject_realizes he2s hcast h2s.faithful
      have h2fEq : call2.formula = tail.head :=
        OpcodeSemantics.noun_eq_of_realizes_eq call2.formula_realizes
          tail.head_realizes he2f hcast h2f.faithful
      have hresultEq : data.root.result = call1.result :=
        OpcodeSemantics.noun_eq_of_realizes_eq data.root.result_realizes
          call1.result_realizes heresult hcast hresult.faithful
      have hconditionSizeEq :
          (OpcodeSemantics.enc inp.z call2.result).size = inp.z := by
        calc
          (OpcodeSemantics.enc inp.z call2.result).size = pub.sf2_e.size :=
            congrArg FP.size call2.result_realizes.symm
          _ = inp.z := hconditionFPSize
      obtain ⟨n, hconditionAtom⟩ :=
        OpcodeSemantics.atom_of_enc_size_eq hconditionSize hconditionSizeEq
      have hnq : n < q := by
        rw [hconditionAtom] at hconditionBound
        exact hconditionBound
      have hleafCast : pub.sf2_e.leaf = (n : K) := by
        calc
          pub.sf2_e.leaf = (OpcodeSemantics.enc inp.z call2.result).leaf :=
            congrArg FP.leaf call2.result_realizes
          _ = (OpcodeSemantics.enc inp.z (.atom n)).leaf := by rw [hconditionAtom]
          _ = (FP.atomFP inp.z (n : K)).leaf :=
            congrArg FP.leaf (GlobalCarryRecognizer.enc_atom inp.z n)
          _ = (n : K) := rfl
      have hinitial := hsem.1
      rw [hrootFormula] at hinitial
      rw [h2sEq, h2fEq] at hc1
      rcases hconditionLeaf with hleafZero | hleafOne
      · have hn0 : n = 0 := by
          apply hcast (Set.mem_Iio.mpr hnq) (Set.mem_Iio.mpr (by omega))
          simpa using hleafCast.symm.trans hleafZero
        have hconditionEq : call2.result = .atom 0 := by
          rw [hconditionAtom, hn0]
        have he1fZero : pub.sf1_f = dec.f_tth := by
          simpa [hleafZero] using he1f
        have h1fEq : call1.formula = branch.head :=
          OpcodeSemantics.noun_eq_of_realizes_eq call1.formula_realizes
            branch.head_realizes he1fZero hcast h1fZero.faithful
        rw [h1sEq, h1fEq] at hc0
        rw [hconditionEq] at hc1
        obtain ⟨parentTrace, htrace, hlast⟩ :=
          s6_assemble data.root.subject tail.head branch.head branch.tail
            branch.head call1.result 0 hinitial hc1.1 hc1.2
            (by simp [Noun.slot]) (by simp [Noun.slot]) hc0.1 hc0.2
        rw [← hrootFormula] at htrace
        rw [hresultEq]
        exact ⟨parentTrace, maximalDFSTrace_of_traceOfROM htrace hlast⟩
      · have hn1 : n = 1 := by
          apply hcast (Set.mem_Iio.mpr hnq) (Set.mem_Iio.mpr (by omega))
          simpa using hleafCast.symm.trans hleafOne
        have hconditionEq : call2.result = .atom 1 := by
          rw [hconditionAtom, hn1]
        have he1fOne : pub.sf1_f = dec.f_ttt := by
          simpa [hleafOne] using he1f
        have h1fEq : call1.formula = branch.tail :=
          OpcodeSemantics.noun_eq_of_realizes_eq call1.formula_realizes
            branch.tail_realizes he1fOne hcast h1fOne.faithful
        rw [h1sEq, h1fEq] at hc0
        rw [hconditionEq] at hc1
        obtain ⟨parentTrace, htrace, hlast⟩ :=
          s6_assemble data.root.subject tail.head branch.head branch.tail
            branch.tail call1.result 1 hinitial hc1.1 hc1.2
            (by simp [Noun.slot]) (by simp [Noun.slot]) hc0.1 hc0.2
        rw [← hrootFormula] at htrace
        rw [hresultEq]
        exact ⟨parentTrace, maximalDFSTrace_of_traceOfROM htrace hlast⟩

/-- OP2's third call occupies the whole verb after calls 2 and 1 terminalize. -/
theorem s2_call3_maximalDFS :
    MaximalDFSFrameLaw rootHoleFrame 0 :=
  rootHoleFrame_maximalDFS

/-- OP6's selected branch call occupies the whole verb after its fixed condition macro. -/
theorem s6_branch_maximalDFS :
    MaximalDFSFrameLaw rootHoleFrame 0 :=
  rootHoleFrame_maximalDFS

/-- OP7's first call occupies the whole verb after call 2 terminalizes. -/
theorem s7_call1_maximalDFS :
    MaximalDFSFrameLaw rootHoleFrame 0 :=
  rootHoleFrame_maximalDFS

/-- OP8's first call occupies the whole verb after call 2 terminalizes. -/
theorem s8_call1_maximalDFS :
    MaximalDFSFrameLaw rootHoleFrame 0 :=
  rootHoleFrame_maximalDFS

/-- OP9's arm call occupies the whole verb after the fixed OP2/slot macro prelude. -/
theorem s9_call2_maximalDFS :
    MaximalDFSFrameLaw rootHoleFrame 0 :=
  rootHoleFrame_maximalDFS

/-! ## Production child-link identification -/

/-- An active `childLinkComp` slot identifies the child row's committed subject, formula, and
result with the corresponding parent `sf` triple. -/
theorem childLinkComp_identifies_program_result
    {K : Type*} [Field K]
    {label : State × DTcomp K}
    {children : Fin 3 → Option (State × DTcomp K)}
    (hlink : childLinkComp label children)
    (i : Fin 3) (hi : (i : ℕ) < fanoutComp label.1) :
    ∃ child,
      children i = some child ∧
      (child.2.2.1.s, child.2.2.1.f, child.2.2.1.e) =
        sfTriple label.2.2.1 i := by
  have h := hlink i hi
  cases hc : children i with
  | none => simp [hc] at h
  | some child =>
      refine ⟨child, rfl, ?_⟩
      have h' :
          some (child.2.2.1.s, child.2.2.1.f, child.2.2.1.e) =
            some (sfTriple label.2.2.1 i) := by
        simpa only [hc, Option.map_some] using h
      exact Option.some.inj h'

/-- `Fcomp` supplies the same child-program/result identification for every active slot. -/
theorem Fcomp_identifies_program_result
    {K : Type*} [Field K]
    {label : State × DTcomp K}
    {children : Fin 3 → Option (State × DTcomp K)}
    (hF : Fcomp label children)
    (i : Fin 3) (hi : (i : ℕ) < fanoutComp label.1) :
    ∃ child,
      children i = some child ∧
      (child.2.2.1.s, child.2.2.1.f, child.2.2.1.e) =
        sfTriple label.2.2.1 i :=
  childLinkComp_identifies_program_result hF.2.2.2 i hi

/-! ## Definitional phase-chain equations -/

/-- After OP2's right child (slot 2) terminalizes, the left child (slot 1) remains in the
left branch. -/
theorem s2_after_call2
    (call1 : Verb) (result2 : Noun) :
    (.node .star call1 (Verb.ofNoun result2) : Verb) =
      .node .star call1 (Verb.ofNoun result2) := rfl

/-- After OP2's first two calls terminalize, the whole verb is exactly the slot-3 program. -/
theorem s2_phase_to_call3 (result1 result2 : Noun) :
    (.node .star (Verb.ofNoun result1) (Verb.ofNoun result2) : Verb) =
      Verb.program result1 result2 := rfl

/-- OP3's terminal child exposes its one-step `wut` postlude. -/
theorem s3_phase_to_postlude (result : Noun) :
    (.node .minus (.leaf 3) (Verb.ofNoun result) : Verb) =
      .node .minus (Verb.ofNoun (.atom 3)) (Verb.ofNoun result) := rfl

/-- OP4's terminal child exposes its one-step increment postlude. -/
theorem s4_phase_to_postlude (result : Noun) :
    (.node .minus (.leaf 4) (Verb.ofNoun result) : Verb) =
      .node .minus (Verb.ofNoun (.atom 4)) (Verb.ofNoun result) := rfl

/-- OP5 evaluates slot 2 first; after slot 1 terminalizes, equality is ready. -/
theorem s5_phase_to_postlude (result1 result2 : Noun) :
    (.node .equal (Verb.ofNoun result1) (Verb.ofNoun result2) : Verb) =
      .node .equal (Verb.ofNoun result1) (Verb.ofNoun result2) := rfl

/-- OP3's selected finite postlude, stated in the scheduler's retained-witness relation. -/
theorem s3_selected_postlude (result : Noun) :
    SelectedROMRewrite
      (.node .minus (.leaf 3) (Verb.ofNoun result))
      (Verb.ofNoun (Noun.wut result)) :=
  selectedROMRewrite_iff_stepROM.mpr (stepROM_wut_terminal result)

/-- OP4's selected finite postlude, stated in the scheduler's retained-witness relation. -/
theorem s4_selected_postlude {value result : Noun}
    (hlus : Noun.lus value = some result) :
    SelectedROMRewrite
      (.node .minus (.leaf 4) (Verb.ofNoun value))
      (Verb.ofNoun result) :=
  selectedROMRewrite_iff_stepROM.mpr (stepROM_lus_terminal hlus)

/-- OP5's selected finite postlude, stated in the scheduler's retained-witness relation. -/
theorem s5_selected_postlude (left right : Noun) :
    SelectedROMRewrite
      (.node .equal (Verb.ofNoun left) (Verb.ofNoun right))
      (Verb.ofNoun (Noun.tis left right)) :=
  selectedROMRewrite_iff_stepROM.mpr (stepROM_equal_terminal left right)

/-- OP7 becomes exactly call 1 after call 2 supplies its subject. -/
theorem s7_phase_to_call1 (result2 formula1 : Noun) :
    (.node .star (Verb.ofNoun result2) (Verb.ofNoun formula1) : Verb) =
      Verb.program result2 formula1 := rfl

/-- OP8 becomes exactly call 1 after call 2 supplies the pushed head. -/
theorem s8_phase_to_call1 (result2 subject formula1 : Noun) :
    (.node .star
      (.node .null (Verb.ofNoun result2) (Verb.ofNoun subject))
      (Verb.ofNoun formula1) : Verb) =
      Verb.program (.cell result2 subject) formula1 := by
  rfl

/-- Structural cons has no operator postlude: two terminal children make a terminal cell. -/
theorem cons_terminal_phase (result1 result2 : Noun) :
    (.node .null (Verb.ofNoun result1) (Verb.ofNoun result2) : Verb) =
      Verb.ofNoun (.cell result1 result2) := rfl

/-! ## Exact, decidable closure boundary -/

/-- States whose complete local schedule (including terminal result) is closed in this file. -/
def completeCoverage : State → Bool
  | .s0 | .s1 | .s2 | .s3 | .s4 | .s5
  | .s6 | .s7 | .s8 | .s9 | .cons => true

/-- Exact list of constructors still requiring universal contextual frame laws and phase assembly. -/
def remainingStates : List State :=
  []

theorem completeCoverage_iff (st : State) :
    completeCoverage st = true ↔ st ∈ allStates := by
  cases st <;> decide

theorem remainingStates_iff (st : State) :
    st ∈ remainingStates ↔ completeCoverage st = false := by
  cases st <;> decide

/-- All eleven states are accounted for, with no residual constructor hidden in a field. -/
theorem all_state_coverage (st : State) :
    completeCoverage st = true ∨ st ∈ remainingStates := by
  cases st <;> decide

end Nock.NockVMROM.Thm54.OpcodeScheduling

#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.s0_complete_schedule
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.s1_complete_schedule
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.s0_complete_of_certificate
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.s1_complete_of_certificate
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.s3_complete_of_certificate_and_children
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.s4_complete_of_certificate_and_children
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.s5_complete_of_certificate_and_children
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.s2_complete_of_certificate_and_children
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.s6_complete_of_certificate_and_children
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.s8_complete_of_certificate_and_children
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.s9_complete_of_certificate_and_children
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.s7_complete_of_certificate_and_children
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.cons_complete_of_certificate_and_children
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.maximalDFSTrace_of_traceOfROM
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.rootHoleFrame_maximalDFS
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.unaryRightFrame_maximalDFS
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.binaryRightFrame_maximalDFS
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.binaryLeftFrame_maximalDFS
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.s3_selected_postlude
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.s4_selected_postlude
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.s5_selected_postlude
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.childLinkComp_identifies_program_result
#print axioms Nock.NockVMROM.Thm54.OpcodeScheduling.all_state_coverage
