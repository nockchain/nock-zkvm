/-
  Nock/RedTeam/Batch163Thm54GenericScopeWitnesses.lean

  * `decide` witnesses that `NoHead8` holds at explicit OP8 formulas, and
  * elaboration of the generic results against the OP2 / OP3 / OP8 fixture runs.

  This module supplies both as committed artifacts, so the claims are reproducible from the tree
  rather than from a transcript.  It proves nothing new about the construction; it is scope
  evidence.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenericCensus
import Nock.NockVMROM.Thm54.TraceGen.Op2Gen
import Nock.NockVMROM.Thm54.TraceGen.Op3Gen
import Nock.NockVMROM.Thm54.TraceGen.Op8Gen
import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.ForestExponentWindow

set_option autoImplicit false

namespace Nock.RedTeam.Batch163

open Nock Nock.Walk
open Nock.NockVMROM.Thm54.TraceGen

variable {K : Type} [Field K]

/-! ## `NoHead8` is vacuous — witnesses at explicit OP8 formulas

`genComputeSkeleton_inTree_cmpKind` carries `NoHead8 subject` / `NoHead8 formula`, whose name reads
as excluding OP8.  `noHead8_all` proves the predicate holds of every noun; these `decide` checks
confirm it concretely at formulas whose head *is* the OP8 atom, which is the case the name suggests
would fail. -/

/-- A bare OP8 formula satisfies `NoHead8`. -/
theorem op8_formula_noHead8 :
    NoHead8 (Noun.cell (.atom 8) (.cell (.atom 1) (.atom 0))) := by decide

/-- A nested OP8 formula satisfies `NoHead8`. -/
theorem op8_nested_noHead8 :
    NoHead8 (Noun.cell (.atom 8) (.cell (.cell (.atom 8) (.atom 1)) (.atom 0))) := by decide

/-- The released OP8 fixture's own subject and formula satisfy it. -/
theorem op8_fixture_noHead8 :
    NoHead8 op8Subject ∧ NoHead8 op8ParentFormula :=
  ⟨noHead8_all _, noHead8_all _⟩

/-! ## The generic results reach OP2 / OP3 / OP8 programs

`gen_op2` / `gen_op3` / `gen_op8` do not exist as per-arm construction helpers, which was misread as
an opcode coverage hole.  The `genComputeSkeleton_inTree_*` inductions split all twelve opcodes
internally, so the generic results apply to those programs.  Witnessed here by instantiating them at
the released OP2, OP3 and OP8 fixture runs. -/

/-- **The census induction reaches an OP2 program.**  There is an accepted OP2 run every node of
which satisfies `nodeCensus`. -/
theorem generic_reaches_op2 :
    ∃ t r, genComputeSkeleton (K := K) 2 op2Subject op2ParentFormula = .ok (t, r) ∧
      ∀ u, InTree t u → nodeCensus u.label :=
  ⟨_, _, genComputeSkeleton_op2 0,
    genComputeSkeleton_inTree_census (genComputeSkeleton_op2 0)⟩

/-- **The census induction reaches an OP8 program** — the opcode `NoHead8` appeared to exclude. -/
theorem generic_reaches_op8 :
    ∃ t r, genComputeSkeleton (K := K) 2 op8Subject op8ParentFormula = .ok (t, r) ∧
      ∀ u, InTree t u → nodeCensus u.label :=
  ⟨_, _, genComputeSkeleton_op8 0,
    genComputeSkeleton_inTree_census (genComputeSkeleton_op8 0)⟩

/-- **The unconditional `cmpKind` corollary reaches the OP8 program**, with its two vacuous
`NoHead8` hypotheses discharged by `noHead8_all`. -/
theorem cmpKind_reaches_op8 :
    ∃ t r, genComputeSkeleton (K := K) 2 op8Subject op8ParentFormula = .ok (t, r) ∧
      ∀ u, InTree t u → NodeCmpKind (K := K) u.label :=
  ⟨_, _, genComputeSkeleton_op8 0,
    genComputeSkeleton_inTree_cmpKind_unconditional (genComputeSkeleton_op8 0)⟩

/-- **The `DA` census premises reach OP2 and OP8**, at `Data`'s field shape, in both the DFS and the
AIR-reordered orderings (the latter added at `DI`). -/
theorem da_reaches_op2_op8 (z α : K) : True := by
  have _s2 := genComputeSkeleton_slotSemantics (K := K) z α (genComputeSkeleton_op2 0) []
  have _r2 := genComputeSkeleton_recordEquations (K := K) z α (genComputeSkeleton_op2 0) []
  have _s8 := genComputeSkeleton_slotSemantics (K := K) z α (genComputeSkeleton_op8 0) []
  have _a2 := genComputeSkeleton_slotSemantics_air (K := K) z α (genComputeSkeleton_op2 0) []
  have _a8 := genComputeSkeleton_recordEquations_air (K := K) z α (genComputeSkeleton_op8 0) []
  trivial

/-- **OP3 coverage.**  OP3 is the opcode whose `V_comp` route carries the `op3CallSizeOk` side
condition, so its coverage by the census induction is the case most worth witnessing.

Stated as an **elaboration check** rather than an existential: the OP3 fixture is stated over the
concrete cubic field, which is fixed here by unification from `genComputeSkeleton_op3` and is not
nameable in this namespace.  The content is that these four terms typecheck at that fixture, i.e.
that the generic results accept an OP3 program. -/
theorem generic_reaches_op3 : True := by
  have _c3 := genComputeSkeleton_inTree_census (genComputeSkeleton_op3 0)
  have _s3 := genComputeSkeleton_slotSemantics 0 0 (genComputeSkeleton_op3 0) []
  have _r3 := genComputeSkeleton_recordEquations 0 0 (genComputeSkeleton_op3 0) []
  have _a3 := genComputeSkeleton_slotSemantics_air 0 0 (genComputeSkeleton_op3 0) []
  trivial

end Nock.RedTeam.Batch163

#print axioms Nock.RedTeam.Batch163.op8_formula_noHead8
#print axioms Nock.RedTeam.Batch163.op8_nested_noHead8
#print axioms Nock.RedTeam.Batch163.op8_fixture_noHead8
#print axioms Nock.RedTeam.Batch163.generic_reaches_op2
#print axioms Nock.RedTeam.Batch163.generic_reaches_op8
#print axioms Nock.RedTeam.Batch163.cmpKind_reaches_op8
#print axioms Nock.RedTeam.Batch163.da_reaches_op2_op8
#print axioms Nock.RedTeam.Batch163.generic_reaches_op3
