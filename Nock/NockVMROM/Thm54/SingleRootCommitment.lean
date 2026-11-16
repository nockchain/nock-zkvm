import Nock.NockVMROM.Thm54.BuildableChips
import Nock.NockVMROM.Thm54.BuildablePackage
import Nock.NockVMROM.Thm54.HonestCommitment
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# `SingleRootCommitment` — the generic served-vacuous single-root Theorem-5.4 wrapper

This is the served-vacuous analogue of `ServedForestCommitment` (the served-forest module).  Where
the served module bundles a multi-root served forest into `dataMG → residualMG → packageMG →
statementMG`, this module bundles the **single-root, served-vacuous** case — the shape of the OP1
slice (`TraceGen/Op1StatementK3.lean`) and every COMPUTE-ONLY opcode whose
`requiredServedLookups = 0` (OP2/OP5/OP7/OP8): those executions have a single-root memory
reconstruction and no served lookups, so the honest commitment `Data` collapses to one root.

The shared, opcode-invariant chain here is exactly the residual → package → statement wrapper of
`TraceGen/GenStatement.statement_of_generated_residual`, packaged as a structure so each
compute-only opcode instantiates it in one line:

  `exec, inputs, data, zeroChallenges  ↦  residual, package, statement, statement_nonvacuous`.

The per-opcode work (the compute-row semantic CORE, the certificate, the single-root memory
reconstruction, and the `BuildableNockExecution`/`Data` construction over a cubic carrier) lives in
the per-opcode files (`Op2Statement.lean`, …); this module carries none of it.

Everything is additive and kernel-clean; nothing existing is touched.  `statement_of_generated_residual`
still stands and this module is a strict re-packaging of it
-/

namespace Nock.NockVMROM.Thm54.SingleRootModule

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

/-- The per-opcode inputs to a served-vacuous single-root Theorem-5.4 statement:

* `exec` — the buildable Nock execution (the compute-only CORE together with its single-root
  memory reconstruction, i.e. `requiredServedLookups = 0`);
* `inputs` — the backend `Inputs` record, which pins the released extension degree `finrank F K = 3`
  via `basis : Basis (Fin 3) F K` (`BuildableChips.lean`, the "`Inputs` wall");
* `data` — the honest commitment over the execution's OWN emitted node trees; and

This is the single-root analogue of `ServedForestModule.ServedForestCommit`. -/
structure SingleRootCommit (F K : Type) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] where
  exec : BuildableNockExecution F K
  inputs : Inputs exec
  data : Data exec
  zeroChallenges : inputs.computeChallenges = default
  pairedRecordLayout : RowLayout.PairedRecordLayout exec.exec
  honestVer : ∀ row ∈ exec.exec.memoryRows,
    row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)
  walkOrder : 2 ≤ exec.cfg.compRows →
    exec.cfg.compRows ≤ orderOf inputs.computeWalkAlpha
  memoryWalkOrder : 2 ≤ exec.cfg.memRows →
    exec.cfg.memRows ≤ orderOf inputs.memoryWalkAlpha
  /-- The package field `rowsBound`'s hypothesis on this execution. -/
  rowsBound : 3 * exec.cfg.compRows < ringChar K ∧ exec.cfg.memRows < ringChar K
  generated : GeneratedField.ClaimGenerated K (commitmentResidualOfZero data).verifier.raw.claim
    (commitmentResidualOfZero data).Λ
  primeField : GeneratedField.PrimeFieldElems F

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- The committed Milestone-5 residual over the commitment's own emitted node trees — exactly
`commitmentResidualOfZero` of `C.data`, i.e. never a hand-built residual. -/
noncomputable def residualSR (C : SingleRootCommit F K) :
    BuildablePackage.CommitmentResidual C.exec :=
  commitmentResidualOfZero C.data

theorem residualSR_nonvacuous (C : SingleRootCommit F K) :
    Nonempty (BuildablePackage.CommitmentResidual C.exec) :=
  ⟨residualSR C⟩

/-- The full optimized strict NockVM-ROM package built from the single-root commitment. -/
noncomputable def packageSR (C : SingleRootCommit F K)
    (hmore : BuildableAxisWitness.LaterSeedZeros C.exec := by later_seed_zeros) :
    OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K C.inputs.hOrb :=
  buildFullPackage C.exec C.inputs (residualSR C) C.zeroChallenges
    C.pairedRecordLayout hmore C.walkOrder C.memoryWalkOrder C.rowsBound C.generated C.primeField

/-- **The generic served-vacuous single-root Theorem-5.4 statement.**  This is the unchanged
released capstone `universalOptimizedFullStrictThm54` — the real 14-conjunct
`OptimizedFullStrictThm54Statement` — over the package of any single-root commitment.  Each
compute-only opcode (OP2/OP5/OP7/OP8) obtains its statement by instantiating `SingleRootCommit`. -/
theorem statementSR (C : SingleRootCommit F K)
    (hmore : BuildableAxisWitness.LaterSeedZeros C.exec := by later_seed_zeros)
    (hax : FormRAxisBound (packageSR C hmore).optimized.sampled (packageSR C hmore).optimized.basis)
    (hbasis : FormRBasis (packageSR C hmore).optimized.basis)
    (hwidth : FormRWidth F) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageSR C hmore) :=
  universalOptimizedFullStrictThm54 C.exec C.inputs (residualSR C) C.zeroChallenges
    C.pairedRecordLayout hmore C.walkOrder C.memoryWalkOrder C.rowsBound C.generated C.primeField
    hax hbasis hwidth

theorem statementSR_nonvacuous (C : SingleRootCommit F K)
    (hmore : BuildableAxisWitness.LaterSeedZeros C.exec := by later_seed_zeros)
    (hax : FormRAxisBound (packageSR C hmore).optimized.sampled (packageSR C hmore).optimized.basis)
    (hbasis : FormRBasis (packageSR C hmore).optimized.basis)
    (hwidth : FormRWidth F) :
    Nonempty
      (OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageSR C hmore)) :=
  ⟨statementSR C hmore hax hbasis hwidth⟩

end Nock.NockVMROM.Thm54.SingleRootModule

#print axioms Nock.NockVMROM.Thm54.SingleRootModule.residualSR
#print axioms Nock.NockVMROM.Thm54.SingleRootModule.packageSR
#print axioms Nock.NockVMROM.Thm54.SingleRootModule.statementSR
#print axioms Nock.NockVMROM.Thm54.SingleRootModule.statementSR_nonvacuous
