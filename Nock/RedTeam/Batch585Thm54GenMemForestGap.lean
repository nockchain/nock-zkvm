/-
  Nock/RedTeam/Batch585Thm54GenMemForestGap.lean

  **Production `genMemForest` is OP1-arm stars; the live compiler is not.**

  The claim: `genMemForestFromTree` / `genMemForestFromList` serve only
  OP1-arm star-shaped subjects, so `nockCompiles_zmod` is vacuous on any program
  whose OP0 reads a subject built otherwise.  That sentence names the wrong
  worker.

  * `genMemForest` (`Gen.lean`) is a formula/subject classifier.  Default arm
    `[]`.  Production `genTrace` (`BFSAssign.lean`) still uses it.
  * `genMemForestFromTree` (`GenMem.lean`) is request-generic: one
    `genAnnotatedRecordTree` (or a two-record chain) per `extractNodeReqs`
    entry.  No OP1-arm restriction on the request root.
  * `nockCompiles_zmod` builds the honest forest by
    `genMemoryForest = threadGenForest (genMemForestFromTree …)`
    (`GenSemanticDataParts.lean::genMemoryForest`), not `genMemForest`.

  **HEADLINE: `nockCompiles_zmod` is not vacuous** at a program outside the
  OP1-arm classifier.  The completeness debt that remains is production
  `genTrace` / `genMemForest`, not the §1 compiler.

  Witness: `*[[2 3] [0 2]] = 2`.  Smallest OP0 whose
  subject is a cons and whose formula is not the classifier's `[0 1]`-on-atom
  arm.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenServedForest
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticDataParts
import Nock.NockVMROM.Thm54.TraceGen.GenGuardedRom
import Nock.NockVMROM.Thm54.TraceGen.GenCommitmentBridge

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch585

open Nock Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

variable {K : Type} [Field K]

/-! ## 1. The two shapes

`ServedShape` is read off `genRowMemForest` / `extractNodeReqs` /
`genAnnotatedRecordTree` (`GenMem.lean`): a request is served when it is a
genuine slot of its own root.  The program subject is unconstrained.

`Op1ArmStar` is the production classifier `genMemForest` (`Gen.lean`). -/

/-- Request-list shape `genMemForestFromTree` actually accepts: every request
    is a genuine `Noun.slot` of its own root.  No OP1-arm or atom-subject
    restriction -/
def ServedShape (_subject : Noun) (reqs : List MemRecordReq) : Prop :=
  ∀ r ∈ reqs, Noun.slot r.axis r.root = some r.child

/-- Forest `forest` serves `reqs` when it is nonempty whenever there is a
    request and every root is a `RootShape` of those requests
    (`GenServedForest.lean::RootShape`). -/
def Serves (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (reqs : List MemRecordReq) (forest : List (NTree (GenMemoryRow K))) : Prop :=
  (reqs ≠ [] → forest ≠ []) ∧
    ∀ u ∈ forest, RootShape E z α lmb reqs u

/-- The production classifier's accepted formulas (`Gen.lean::genMemForest`).
    Default arm is `[]`. -/
def Op1ArmStar (formula subject : Noun) : Bool :=
  match formula, subject with
  | .cell (.atom 1) (.atom _), _ => true
  | .cell (.cell (.atom 1) (.atom _)) (.cell (.atom 1) (.atom _)), _ => true
  | .cell (.atom 0) (.atom 1), .atom _ => true
  | .cell (.atom 4) (.cell (.atom 1) (.atom _)), _ => true
  | .cell (.atom 3) (.cell (.atom 1) (.atom _)), _ => true
  | .cell (.atom 5) (.cell (.cell (.atom 1) (.atom _))
      (.cell (.atom 1) (.atom _))), _ => true
  | .cell (.atom 7) (.cell (.cell (.atom 1) (.atom _))
      (.cell (.atom 1) (.atom _))), _ => true
  | .cell (.atom 8) (.cell (.cell (.atom 1) (.atom _))
      (.cell (.atom 1) (.atom _))), _ => true
  | .cell (.atom 2) (.cell (.cell (.atom 1) (.atom _))
      (.cell (.atom 1) (.atom _))), _ => true
  | .cell (.atom 6) (.cell (.cell (.atom 1) (.atom _))
      (.cell (.cell (.atom 1) (.atom _)) (.cell (.atom 1) (.atom _)))), _ => true
  | .cell (.atom 9) (.cell (.atom 1) (.cell (.atom 1) (.cell (.atom 1) (.atom _)))),
    _ => true
  | _, _ => false

/-! ## 2. Witness program — outside the classifier, inside `ServedShape`

`*[[2 3] [0 2]] = /[2 [2 3]] = 2`. -/

def witnessSubject : Noun := .cell (.atom 2) (.atom 3)
def witnessFormula : Noun := .cell (.atom 0) (.atom 2)
def witnessResult : Noun := .atom 2

/-- Assigned-exponent request list of the OP0 row: formula-open `@3`, then
    the slot read of the cons subject `@2`.  They do not chain
    (`2 ≠ [2 3]`). -/
def witnessReqOpen : MemRecordReq :=
  { root := witnessFormula, child := .atom 2, axis := 3, recordExp := 1 }

def witnessReqSlot : MemRecordReq :=
  { root := witnessSubject, child := witnessResult, axis := 2, recordExp := 2 }

def witnessReqs : List MemRecordReq :=
  [witnessReqOpen, witnessReqSlot]

theorem witness_evalN :
    Nock.evalN 1 witnessSubject witnessFormula = some witnessResult := by
  simp [Nock.evalN, witnessSubject, witnessFormula, witnessResult, Noun.slot]

theorem witness_slot : Noun.slot 2 witnessSubject = some witnessResult := by
  simp [witnessSubject, witnessResult, Noun.slot]

theorem witness_not_op1ArmStar :
    Op1ArmStar witnessFormula witnessSubject = false :=
  rfl

theorem servedShape_witness : ServedShape witnessSubject witnessReqs := by
  intro r hr
  simp [witnessReqs] at hr
  rcases hr with rfl | rfl
  · simp [witnessReqOpen, witnessFormula, Noun.slot]
  · simpa [witnessReqSlot] using witness_slot

theorem witness_not_chain : witnessReqOpen.child ≠ witnessReqSlot.root := by
  simp [witnessReqOpen, witnessReqSlot, witnessSubject]

/-! ## 3. Classifier does not serve; generic worker does -/

theorem classifier_empty (z α : K) :
    genMemForest z α witnessFormula witnessSubject = [] :=
  rfl

/-- The production classifier emits no forest for this program, so it does
    not serve the nonempty request list. -/
theorem not_serves_classifier (E : Noun → ComputeTable.FP K) (z α lmb : K) :
    ¬ Serves E z α lmb witnessReqs (genMemForest z α witnessFormula witnessSubject) := by
  intro h
  have hne : witnessReqs ≠ [] := by simp [witnessReqs]
  have := h.1 hne
  simp [classifier_empty] at this

theorem generic_row_eq (E : Noun → ComputeTable.FP K) (z α lmb : K) :
    genRowMemForest E z α lmb witnessReqs =
      [genAnnotatedRecordTree E z α lmb witnessReqOpen.root witnessReqOpen.child
        witnessReqOpen.axis witnessReqOpen.recordExp,
       genAnnotatedRecordTree E z α lmb witnessReqSlot.root witnessReqSlot.child
        witnessReqSlot.axis witnessReqSlot.recordExp] := by
  simp only [witnessReqs, genRowMemForest, if_neg witness_not_chain]

theorem serves_generic (E : Noun → ComputeTable.FP K) (z α lmb : K) :
    Serves E z α lmb witnessReqs (genRowMemForest E z α lmb witnessReqs) := by
  rw [generic_row_eq]
  refine ⟨fun _ => List.cons_ne_nil _ _, ?_⟩
  intro u hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact Or.inl ⟨witnessReqOpen, by simp [witnessReqs], rfl⟩
  · exact Or.inl ⟨witnessReqSlot, by simp [witnessReqs], rfl⟩

/-- Honest forest accepted on `ServedShape` — `c1`-style reuse of
    `RootShape` / `genRowMemForest`, not a re-proof of the builder. -/
theorem honest_accepted_on_servedShape (E : Noun → ComputeTable.FP K) (z α lmb : K) :
    ServedShape witnessSubject witnessReqs ∧
      Serves E z α lmb witnessReqs (genRowMemForest E z α lmb witnessReqs) :=
  ⟨servedShape_witness, serves_generic E z α lmb⟩

/-! ## 4. The compute tree the generic worker sees -/

noncomputable def witnessRow : GenComputeRow K :=
  skelNode (genSkelOp0 witnessSubject witnessFormula (.atom 0) (.atom 2)
      witnessResult 2)
    [{ root := witnessFormula, child := .atom 2, axis := 3, ts := 0 },
     { root := witnessSubject, child := witnessResult, axis := 2, ts := 0 }]

noncomputable def witnessTree : NTree (GenComputeRow K) :=
  .node (witnessRow (K := K)) []

theorem witness_gen :
    genComputeSkeleton (K := K) 1 witnessSubject witnessFormula =
      .ok (witnessTree, witnessResult) := by
  simp [genComputeSkeleton, witnessFormula, witnessSubject, witnessResult,
    witnessTree, witnessRow, Noun.slot]

def extractReqOpen : MemRecordReq :=
  { root := witnessFormula, child := .atom 2, axis := 3, recordExp := 0 }

def extractReqSlot : MemRecordReq :=
  { root := witnessSubject, child := witnessResult, axis := 2, recordExp := 0 }

theorem extract_witness :
    extractNodeReqs (witnessRow (K := K)) = [extractReqOpen, extractReqSlot] := by
  simp [extractNodeReqs, extractNodeReqsAux, getRecordExp, witnessRow, skelNode,
    zeroStamp, extractReqOpen, extractReqSlot, witnessFormula, witnessSubject,
    witnessResult]

theorem extract_not_chain : extractReqOpen.child ≠ extractReqSlot.root := by
  simp [extractReqOpen, extractReqSlot, witnessSubject]

theorem fromTree_eq_row (E : Noun → ComputeTable.FP K) (z α lmb : K) :
    genMemForestFromTree E z α lmb (witnessTree (K := K)) =
      genRowMemForest E z α lmb (extractNodeReqs (witnessRow (K := K))) :=
  genMemForestFromTree_leaf (lmb := lmb) E z α _

theorem fromTree_row_eq (E : Noun → ComputeTable.FP K) (z α lmb : K) :
    genRowMemForest E z α lmb [extractReqOpen, extractReqSlot] =
      [genAnnotatedRecordTree E z α lmb extractReqOpen.root extractReqOpen.child
        extractReqOpen.axis extractReqOpen.recordExp,
       genAnnotatedRecordTree E z α lmb extractReqSlot.root extractReqSlot.child
        extractReqSlot.axis extractReqSlot.recordExp] := by
  simp only [genRowMemForest, if_neg extract_not_chain]

theorem fromTree_length (E : Noun → ComputeTable.FP K) (z α lmb : K) :
    (genMemForestFromTree E z α lmb (witnessTree (K := K))).length = 2 := by
  rw [fromTree_eq_row, extract_witness, fromTree_row_eq]
  rfl

/-- `genMemForestFromTree` does produce a forest serving the request list.
    The claimed `¬ Serves` is true of `genMemForest`, not of this worker. -/
theorem serves_fromTree (E : Noun → ComputeTable.FP K) (z α lmb : K) :
    Serves E z α lmb (extractNodeReqs (witnessRow (K := K)))
      (genMemForestFromTree E z α lmb (witnessTree (K := K))) := by
  rw [fromTree_eq_row, extract_witness, fromTree_row_eq]
  refine ⟨fun _ => List.cons_ne_nil _ _, ?_⟩
  intro u hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact Or.inl ⟨extractReqOpen, by simp, rfl⟩
  · exact Or.inl ⟨extractReqSlot, by simp, rfl⟩

theorem generic_trace_ok (z α lmb : K) :
    (genTraceGeneric 31 4 z α lmb 1 witnessSubject witnessFormula).isOk = true := by
  rw [genTraceGeneric_isOk_iff, witness_gen]
  rfl

/-! ## 5. `nockCompiles_zmod` path and program-side premises

`nockCompiles_zmod` (`GenNockCompilesCarrier.lean`) specialises `nockCompiles_p76`
and builds the honest forest from `romTree` → `genMemoryForest` →
`genMemForestFromTree`.  It never calls `genMemForest`. -/

theorem compiler_forest_is_generic (z α lmb : K) (inp : MemoryTable.Inputs K)
    (t : NTree (GenComputeRow K)) :
    genMemoryForest z α lmb inp t =
      threadGenForest inp 0
        (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t))) :=
  rfl

theorem premises_hs : FieldEmbedding.BoundedBy 31 witnessSubject := by
  simp [witnessSubject, FieldEmbedding.BoundedBy]

theorem premises_hf : FieldEmbedding.BoundedBy 31 witnessFormula := by
  simp [witnessFormula, FieldEmbedding.BoundedBy]

theorem premises_evalGRom :
    evalGRom 31 1 witnessSubject witnessFormula = some witnessResult := by
  simp [evalGRom, witnessSubject, witnessFormula, witnessResult, Noun.slot]

/-- `RunBoundedBy` (`GenNockCompilesCarrier.lean::RunBoundedBy`) at this
    program: the guarded ROM run succeeds.  No `OP_4`, so any `q > 3`. -/
theorem premises_hbound :
    ∃ result, evalGRom 31 1 witnessSubject witnessFormula = some result :=
  ⟨witnessResult, premises_evalGRom⟩

theorem premises_hp : 25 ≤ 31 := by omega

/-- **HEADLINE.**  The §1 compiler is not vacuous here.  The program-side
    premises of `nockCompiles_zmod` hold, `genComputeSkeleton` succeeds, and
    the forest the compiler commits is `genMemForestFromTree` of that tree
    (nonempty, `Serves`), not the empty `genMemForest`. -/
theorem nockCompiles_zmod_not_vacuous (z α lmb : K) :
    Nock.evalN 1 witnessSubject witnessFormula = some witnessResult ∧
      FieldEmbedding.BoundedBy 31 witnessSubject ∧
      FieldEmbedding.BoundedBy 31 witnessFormula ∧
      evalGRom 31 1 witnessSubject witnessFormula = some witnessResult ∧
      25 ≤ 31 ∧
      Op1ArmStar witnessFormula witnessSubject = false ∧
      genMemForest z α witnessFormula witnessSubject = [] ∧
      (genMemForestFromTree (encC z) z α lmb (witnessTree (K := K))).length = 2 ∧
      Serves (encC z) z α lmb (extractNodeReqs (witnessRow (K := K)))
        (genMemForestFromTree (encC z) z α lmb (witnessTree (K := K))) ∧
      genMemoryForest z α lmb ⟨z, 0, 0⟩ (witnessTree (K := K)) =
        threadGenForest ⟨z, 0, 0⟩ 0
          (genMemForestFromTree (encC z) z α lmb
            (bfsAssign (airReorder (witnessTree (K := K))))) :=
  ⟨witness_evalN, premises_hs, premises_hf, premises_evalGRom, premises_hp,
    witness_not_op1ArmStar, classifier_empty z α, fromTree_length (encC z) z α lmb,
    serves_fromTree (encC z) z α lmb,
    compiler_forest_is_generic z α lmb ⟨z, 0, 0⟩ (witnessTree (K := K))⟩

end Nock.RedTeam.Batch585

#print axioms Nock.RedTeam.Batch585.witness_evalN
#print axioms Nock.RedTeam.Batch585.witness_not_op1ArmStar
#print axioms Nock.RedTeam.Batch585.servedShape_witness
#print axioms Nock.RedTeam.Batch585.not_serves_classifier
#print axioms Nock.RedTeam.Batch585.serves_generic
#print axioms Nock.RedTeam.Batch585.serves_fromTree
#print axioms Nock.RedTeam.Batch585.witness_gen
#print axioms Nock.RedTeam.Batch585.generic_trace_ok
#print axioms Nock.RedTeam.Batch585.compiler_forest_is_generic
#print axioms Nock.RedTeam.Batch585.nockCompiles_zmod_not_vacuous
