import Nock.NockVMROM.Thm54.NounRealization
import Nock.NockVMROM.Thm54.MemoryMplus2L
import Nock.NockVMROM.Thm54.ExactOneHot
import Nock.NockVMROM.Thm54.SemanticTrace
import Nock.NockVMROM.Thm54.ServedMemoryTrace

/-!
# Minimal buildable execution input

`BuildableNockExecution` is the universal-constructor input boundary.  It contains one already
supplied finite exact execution and only semantic or field conditions known before compilation.
It deliberately contains no RAP, optimized package, compiler residual, topology binding,
coordinate pin, acceptance proof, axis conclusion, semantic target, or soundness theorem.

The active row positivity and orbit-prefix capacities are already fields of `ExactConfig`.
Timestamp bounds are already part of the `SemanticIOPreimage` carried by the exact semantic
language.  Noun bounds are the `q`-indexed witnesses in
`NounRealizedTraversableChainedSemanticExactLanguage`.
-/

namespace Nock.NockVMROM.Thm54

open Nock

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The exact execution is write-free because every compute row uses the ROM state type
`OP_0,...,OP_9,cons`, which excludes opcode 10. -/
def WriteFreeExactExecution {cfg : ExactConfig F K} (exec : ExactExecution cfg) : Prop :=
  ∀ i : Fin cfg.compRows, (exec.computePubAt i).state.toNat < 10

/-- Every `ExactExecution` is write-free by construction; no caller proof is needed. -/
theorem writeFreeExactExecution {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    WriteFreeExactExecution exec := by
  intro i
  cases (exec.computePubAt i).state <;> decide

/-- Minimal pre-compilation input for the universal NockVMROM constructor.

The retained fields are:

* `q`/`Λ`: the finite atom and evaluator/leaf bounds used by the semantic execution;
* `cfg`/`exec`: one positive, capacity-bounded exact forest-first execution;
* `semanticData`: exact row-level Nock semantics, served slot lookups, semantic row validity,
  exact chaining, exact arity-3/2 traversability, bounded noun realization, and bounded semantic
  timestamps;
* `memoryTrace`: recursively generated Nock services on each actual supplied forest root, with an
  exact per-root partition and coverage of every row-level OP0/OP9 served lookup;
* `requestNodup`: the paper's unique-request condition on the execution-derived requests;
* `recordCountBalance`: the exact pre-compilation count condition equivalent to `M + 2L`;
* `q_le_ringChar`/`two_ne_zero`/`Ksz_lt_ringChar`: finite-field injectivity/range and binary-axis
  nondegeneracy conditions;
* `programIOCapacity`/`memoryIOCapacity`: the two execution-derived IO prefixes fit the configured
  orbit.

No field is a compiler, topology, RAP-satisfaction, acceptance, axis, target, or soundness result.
-/
structure BuildableNockExecution
    (F K : Type) [Field F] [Field K] [Algebra F K] where
  /-- Bound on every realized Nat-valued noun atom. -/
  q : ℕ
  /-- The atom range is nontrivial. -/
  q_gt_one : 1 < q
  /-- Finite evaluator/leaf bound for the exact row-level semantic data. -/
  Λ : ℕ
  /-- One exact field/domain configuration. -/
  cfg : ExactConfig F K
  /-- The a-bearing view of the execution. -/
  execA : ExactExecution cfg
  /-- One already supplied finite exact execution; this API does not discover termination.
  Its memory rows are row-level: the Form R row encode of `execA`. -/
  exec : ExactExecution cfg
  /-- The executed trace is the row encode of the a-bearing view. -/
  exec_encode : exec = execA.encodeMem
  /-- Exact semantic CORE on every authoritative compute row.  Its `language` field retains the
  previous chained/noun-realized/traversable input, while `rows` additionally carries the actual
  served Nock slot semantics. -/
  semanticData :
    SemanticTrace.ExactExecutionSemanticData q Λ cfg exec
  /-- Same-execution Nock service/traversal CORE on the supplied memory forest.  This is a
  recursive noun-indexed walk over the actual supplied roots: each `read_root` node binds its
  realized noun and emitted record to a compute-side service, each matching `verify_child` node
  binds its realized noun and committed `address` column, and the route between them is the binary
  expansion of the record's own axis.  It contains no axis
  polynomial, ancestry primitive, noun shape, or proof-system conclusion. -/
  memoryTrace :
    ServedMemoryTrace.ExactServedMemoryTrace q Λ cfg exec semanticData execA
  /-- Unique execution-derived requests. -/
  requestNodup : exec.derivedRequestIO.Nodup
  /-- Exact `verify_child`/`read_root` balance for the `M + 2L` budget. -/
  recordCountBalance : RowLayout.RecordCountBalanced exec
  /-- Bounded Nat atoms embed without wraparound. -/
  q_le_ringChar : q ≤ ringChar K
  /-- The binary Nock-axis recurrence is nondegenerate.  This field has no default either. -/
  two_ne_zero : (2 : K) ≠ 0
  /-- The semantic IO count bound lies below the field characteristic. -/
  Ksz_lt_ringChar : cfg.Ksz < ringChar K
  /-- The request accumulator's active prefix fits the configured orbit. -/
  programIOCapacity : exec.derivedRequestIO.length + 1 ≤ 2 ^ cfg.orbit.h
  /-- The response accumulator's active prefix fits the configured orbit. -/
  memoryIOCapacity : exec.derivedResponseIO.length + 1 ≤ 2 ^ cfg.orbit.h

namespace BuildableNockExecution

variable (E : BuildableNockExecution F K)

/-- Exhaustive post-M4 eta receipt.  In particular, the semantic memory trace and binary-axis
nondegeneracy are explicit fields; neither is derived from the preceding semantic data. -/
theorem eta_with_memoryTrace :
    E =
      { q := E.q
        q_gt_one := E.q_gt_one
        Λ := E.Λ
        cfg := E.cfg
        execA := E.execA
        exec := E.exec
        exec_encode := E.exec_encode
        semanticData := E.semanticData
        memoryTrace := E.memoryTrace
        requestNodup := E.requestNodup
        recordCountBalance := E.recordCountBalance
        q_le_ringChar := E.q_le_ringChar
        two_ne_zero := E.two_ne_zero
        Ksz_lt_ringChar := E.Ksz_lt_ringChar
        programIOCapacity := E.programIOCapacity
        memoryIOCapacity := E.memoryIOCapacity } := by
  cases E
  rfl

/-- Compatibility accessor for the former `language` field.  The language is now definitionally
the language carried by the stronger row-level semantic CORE. -/
abbrev language :
    NounRealizedTraversableChainedSemanticExactLanguage E.q E.cfg E.exec :=
  E.semanticData.language

/-- Public write-free receipt derived from the exact carrier, not stored as an input premise. -/
theorem writeFree : WriteFreeExactExecution E.exec :=
  writeFreeExactExecution E.exec

/-- The compute active domain is positive before compilation. -/
theorem computeRows_pos : 0 < E.cfg.compRows :=
  E.cfg.compRows_pos

/-- The memory active domain is positive before compilation. -/
theorem memoryRows_pos : 0 < E.cfg.memRows :=
  E.cfg.memRows_pos

/-- The exact execution already supplies a bounded semantic timestamp witness. -/
theorem timestampBounds :
    Nonempty (SemanticIOPreimage E.cfg E.exec) :=
  E.language.traversable.chained.semantic.2.2

/-- The semantic layer consumed by the existing exact compiler. -/
theorem chained : ChainedSemanticExactLanguage E.cfg E.exec :=
  E.language.toChained

/-- All five exact one-hot clauses are derived from the retained semantic input. -/
theorem oneHot : OneHotRealization E.cfg E.exec :=
  E.chained.oneHotRealization

/-- Exact compute arity 3 and memory arity 2 are part of the retained traversal input. -/
theorem traversal :
    ComputeExactTopology E.exec ∧ MemoryExactTopology E.exec :=
  ⟨E.language.traversable.compute_topology, E.language.traversable.memory_topology⟩

/-- The configured memory rows have the exact paper budget `M + 2L`. -/
theorem memoryRows_eq_M_add_two_mul_L :
    E.cfg.memRows = RowLayout.memoryM E.exec + 2 * RowLayout.memoryL E.exec :=
  RowLayout.memRows_eq_M_add_two_mul_L_of_count_balance E.recordCountBalance

end BuildableNockExecution

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.writeFreeExactExecution
#print axioms Nock.NockVMROM.Thm54.BuildableNockExecution.eta_with_memoryTrace
#print axioms Nock.NockVMROM.Thm54.BuildableNockExecution.writeFree
#print axioms Nock.NockVMROM.Thm54.BuildableNockExecution.timestampBounds
#print axioms Nock.NockVMROM.Thm54.BuildableNockExecution.oneHot
#print axioms Nock.NockVMROM.Thm54.BuildableNockExecution.traversal
#print axioms Nock.NockVMROM.Thm54.BuildableNockExecution.memoryRows_eq_M_add_two_mul_L
