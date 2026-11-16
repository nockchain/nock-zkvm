/-
  Nock/NockVMROM/Thm54/TraceGen/GenStatement.lean

  Closing the loop from the executable generator toward a Theorem-5.4 statement instance.

  The intended chain is:

    fresh Nock program → `genTrace` → generated `Data` → `commitmentResidualOfZero`
      → `CommitmentResidual` → `buildFullPackage` → `OptimizedFullStrictThm54Statement`.

  This module lands the residual half of that chain over the GENERATED honest commitments —
  `op1Residual` / `consResidual` are `commitmentResidualOfZero` applied to the generator's OWN
  emitted node trees (`dataOfGenerated` / `consDataOfGenerated`), not to any hand-built `Data`.  So
  the committed layer that `buildFullPackage` consumes is produced end-to-end by the executable
  generator on a fresh ROM program.

  The package/statement half is BLOCKED, and the block is fundamental — recorded here as a compiled
  artifact rather than asserted in prose.  The generator's OP1/cons executions
  are built over `F = K = ZMod 97` (`eDeg = 1`, `Op1Config`/`ConsConfig`), so `finrank F K = 1` and
  `Inputs Op1Execution` / `Inputs ConsExecution` are provably UNINHABITED
  (`inputs_op1Execution_isEmpty`, `inputs_consExecution_isEmpty`, from `no_basis_fin3_field_self`).

  Reaching `op1Statement` / `consStatement` therefore requires re-basing the generator (or the
  OP1/cons `BuildableNockExecution` carriers) over a genuine cubic extension `K / ZMod 97` with
  `finrank = 3` — the F97/`K97cubic` shape already used by `DistinctCensusFold2.packageR` — which is
  a semantic-carrier re-basing, not a wiring step.  See the module footer.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op1GenData
import Nock.NockVMROM.Thm54.TraceGen.Op1Gen
import Nock.NockVMROM.Thm54.TraceGen.ConsGenMem
import Nock.NockVMROM.Thm54.TraceGen.ConsGen
import Nock.NockVMROM.Thm54.BuildableChips
import Nock.NockVMROM.Thm54.BuildablePackage
import Nock.NockVMROM.Thm54.ForestExponentWindow
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.TraceGen

open Module
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

/-- The consumed-`q` char instance for the OP1 slice field, mirroring the F73 fixture's local
instance (`BuildablePackage.lean:397`). -/
local instance : CharP Op1Config.F (ringChar Op1Config.F) := ringChar.charP Op1Config.F

/-- The consumed-`q` char instance for the cons slice field. -/
local instance : CharP ConsConfig.F (ringChar ConsConfig.F) := ringChar.charP ConsConfig.F

/-! ## The generated OP1 committed residual

`op1Residual` is the exact Milestone-5 committed residual over the generator's own emitted OP1 node
trees.  The `Data Op1Execution` it wraps is `dataOfGenerated`, whose committed `computeNodes` /
`memoryNodes` are the generator's output on the fresh program `*[0 [1 5]] = 5`. -/

/-- A concrete successful OP1 generator run (`genTrace 97 3 8 4 1 (.atom 0) [1 5] =.ok G`). -/
noncomputable def op1GenTrace : GenTrace Op1Config.F Op1Config.F :=
  (genTrace_op1_computeRows 0).choose

/-- The concrete OP1 run commits exactly the verified honest OP1 node trees. -/
theorem op1GenTraceOK : GenTraceOK op1GenTrace :=
  genTrace_spec 0 op1GenTrace (genTrace_op1_computeRows 0).choose_spec.1

/-- **The generated OP1 committed residual** — `commitmentResidualOfZero` over the generator's own
    emitted node trees, i.e. over `dataOfGenerated`, never over a hand-built `Data`.  This is the
    committed half of the Theorem-5.4 package produced end-to-end by the executable generator. -/
noncomputable def op1Residual
    (hread : Vmem (Op1Config.memoryInputs Op1Config.seedZ)
      (Op1Config.readPub Op1Config.seedZ Op1Config.alphaA))
    (hdec : Vmem (Op1Config.memoryInputs Op1Config.seedZ)
      (Op1Config.decomposePub Op1Config.seedZ Op1Config.alphaA))
    (hver : Vmem (Op1Config.memoryInputs Op1Config.seedZ)
      (Op1Config.verifyPub Op1Config.seedZ Op1Config.alphaA)) :
    BuildablePackage.CommitmentResidual (Op1Config.Op1Execution hread hdec hver) :=
  commitmentResidualOfZero (dataOfGenerated op1GenTrace op1GenTraceOK hread hdec hver)

theorem op1Residual_nonvacuous
    (hread : Vmem (Op1Config.memoryInputs Op1Config.seedZ)
      (Op1Config.readPub Op1Config.seedZ Op1Config.alphaA))
    (hdec : Vmem (Op1Config.memoryInputs Op1Config.seedZ)
      (Op1Config.decomposePub Op1Config.seedZ Op1Config.alphaA))
    (hver : Vmem (Op1Config.memoryInputs Op1Config.seedZ)
      (Op1Config.verifyPub Op1Config.seedZ Op1Config.alphaA)) :
    Nonempty (BuildablePackage.CommitmentResidual (Op1Config.Op1Execution hread hdec hver)) :=
  ⟨op1Residual hread hdec hver⟩

/-! ## The generated cons committed residual -/

/-- A concrete successful cons generator run
    (`genTrace 97 4 8 4 2 (.atom 0) [[1 5] [1 6]] =.ok G`). -/
noncomputable def consGenTrace : GenTrace ConsConfig.F ConsConfig.F :=
  (genTrace_cons_computeRows 0).choose

/-- The concrete cons run commits exactly the verified honest cons node trees. -/
theorem consGenTraceOK : ConsGenTraceOK consGenTrace :=
  consGenTrace_spec 0 consGenTrace (genTrace_cons_computeRows 0).choose_spec.1

/-- **The generated cons committed residual** — `commitmentResidualOfZero` over the generator's own
    emitted cons node trees (`consDataOfGenerated`), for the fresh program
    `*[0 [[1 5] [1 6]]] = [5 6]` -/
noncomputable def consResidual
    (hReadF : Vmem ConsConfig.memInputs ConsConfig.pReadF)
    (hDecF : Vmem ConsConfig.memInputs ConsConfig.pDecF)
    (hReadL : Vmem ConsConfig.memInputs ConsConfig.pReadL)
    (hReadR : Vmem ConsConfig.memInputs ConsConfig.pReadR)
    (hDecL : Vmem ConsConfig.memInputs ConsConfig.pDecL)
    (hVerifyF : Vmem ConsConfig.memInputs ConsConfig.pVerifyF)
    (hVerifyL : Vmem ConsConfig.memInputs ConsConfig.pVerifyL)
    (hDecR : Vmem ConsConfig.memInputs ConsConfig.pDecR)
    (hVerifyR : Vmem ConsConfig.memInputs ConsConfig.pVerifyR) :
    BuildablePackage.CommitmentResidual
      (ConsConfig.ConsExecution hReadF hDecF hReadL hReadR hDecL
        hVerifyF hVerifyL hDecR hVerifyR) :=
  commitmentResidualOfZero (consDataOfGenerated consGenTrace consGenTraceOK
    hReadF hDecF hReadL hReadR hDecL hVerifyF hVerifyL hDecR hVerifyR)

theorem consResidual_nonvacuous
    (hReadF : Vmem ConsConfig.memInputs ConsConfig.pReadF)
    (hDecF : Vmem ConsConfig.memInputs ConsConfig.pDecF)
    (hReadL : Vmem ConsConfig.memInputs ConsConfig.pReadL)
    (hReadR : Vmem ConsConfig.memInputs ConsConfig.pReadR)
    (hDecL : Vmem ConsConfig.memInputs ConsConfig.pDecL)
    (hVerifyF : Vmem ConsConfig.memInputs ConsConfig.pVerifyF)
    (hVerifyL : Vmem ConsConfig.memInputs ConsConfig.pVerifyL)
    (hDecR : Vmem ConsConfig.memInputs ConsConfig.pDecR)
    (hVerifyR : Vmem ConsConfig.memInputs ConsConfig.pVerifyR) :
    Nonempty (BuildablePackage.CommitmentResidual
      (ConsConfig.ConsExecution hReadF hDecF hReadL hReadR hDecL
        hVerifyF hVerifyL hDecR hVerifyR)) :=
  ⟨consResidual hReadF hDecF hReadL hReadR hDecL hVerifyF hVerifyL hDecR hVerifyR⟩

/-! ## The wiring bridge — generated-Data residual → the released capstone

The residual is the *only* generated-Data-dependent input to the released Theorem-5.4 statement.
`statement_of_generated_residual` is the unchanged capstone
`optimizedFullStrictNockVMROM_of_package` applied to a package whose committed half is
`commitmentResidualOfZero D` — and `D` may be `dataOfGenerated` / `consDataOfGenerated`, i.e. the
generator's own honest commitment.  The OP1/cons executions do not have such a
record (§wall below), which is exactly why this bridge does not specialize to an `op1Statement`
inhabitant here -/
theorem statement_of_generated_residual
    {F K : Type} [Field F]
    [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    {E : BuildableNockExecution F K} (D : Data E) (I : Inputs E)
    (hz : I.computeChallenges = default)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hax : FormRAxisBound
      (buildFullPackage E I (commitmentResidualOfZero D) hz hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (buildFullPackage E I (commitmentResidualOfZero D) hz hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hbasis : FormRBasis
      (buildFullPackage E I (commitmentResidualOfZero D) hz hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : FormRWidth F) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
      (buildFullPackage E I (commitmentResidualOfZero D) hz hprl hmore hord hordM hrows hgenF hF) :=
  universalOptimizedFullStrictThm54 E I (commitmentResidualOfZero D) hz hprl hmore hord hordM hrows hgenF hF
    hax hbasis hwidth

/-! ## The `Inputs` wall — a compiled record of why the statement half is blocked

`Inputs E` requires `basis : Basis (Fin 3) F K`, so any `Inputs` for an execution over `F = K`
forces `finrank F F = 3`, contradicting `finrank F F = 1`.  The OP1/cons generator executions are
over `F = K = ZMod 97` (`eDeg = 1`), so their `Inputs` types are provably uninhabited. -/

/-- A field has no `Fin 3`-indexed basis over itself: `finrank F F = 1 ≠ 3`. -/
theorem no_basis_fin3_field_self {F : Type} [Field F] :
    IsEmpty (Basis (Fin 3) F F) := by
  constructor
  intro b
  have h3 : Module.finrank F F = 3 := by
    rw [Module.finrank_eq_card_basis b]; simp
  rw [Module.finrank_self] at h3
  exact absurd h3 (by norm_num)

/-- **The OP1 backend-inputs record is uninhabited.**  `Inputs Op1Execution` carries
    `basis : Basis (Fin 3) (ZMod 97) (ZMod 97)`, which cannot exist — so no `buildFullPackage`,
    and hence no `op1Statement`, can be built from the `eDeg = 1` generated OP1 execution. -/
theorem inputs_op1Execution_isEmpty
    (hread : Vmem (Op1Config.memoryInputs Op1Config.seedZ)
      (Op1Config.readPub Op1Config.seedZ Op1Config.alphaA))
    (hdec : Vmem (Op1Config.memoryInputs Op1Config.seedZ)
      (Op1Config.decomposePub Op1Config.seedZ Op1Config.alphaA))
    (hver : Vmem (Op1Config.memoryInputs Op1Config.seedZ)
      (Op1Config.verifyPub Op1Config.seedZ Op1Config.alphaA)) :
    IsEmpty (Inputs (Op1Config.Op1Execution hread hdec hver)) :=
  ⟨fun I => no_basis_fin3_field_self.false I.basis⟩

/-- **The cons backend-inputs record is uninhabited**, for the same reason. -/
theorem inputs_consExecution_isEmpty
    (hReadF : Vmem ConsConfig.memInputs ConsConfig.pReadF)
    (hDecF : Vmem ConsConfig.memInputs ConsConfig.pDecF)
    (hReadL : Vmem ConsConfig.memInputs ConsConfig.pReadL)
    (hReadR : Vmem ConsConfig.memInputs ConsConfig.pReadR)
    (hDecL : Vmem ConsConfig.memInputs ConsConfig.pDecL)
    (hVerifyF : Vmem ConsConfig.memInputs ConsConfig.pVerifyF)
    (hVerifyL : Vmem ConsConfig.memInputs ConsConfig.pVerifyL)
    (hDecR : Vmem ConsConfig.memInputs ConsConfig.pDecR)
    (hVerifyR : Vmem ConsConfig.memInputs ConsConfig.pVerifyR) :
    IsEmpty (Inputs (ConsConfig.ConsExecution hReadF hDecF hReadL hReadR hDecL
      hVerifyF hVerifyL hDecR hVerifyR)) :=
  ⟨fun I => no_basis_fin3_field_self.false I.basis⟩

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.statement_of_generated_residual
#print axioms Nock.NockVMROM.Thm54.TraceGen.op1Residual
#print axioms Nock.NockVMROM.Thm54.TraceGen.op1Residual_nonvacuous
#print axioms Nock.NockVMROM.Thm54.TraceGen.consResidual
#print axioms Nock.NockVMROM.Thm54.TraceGen.consResidual_nonvacuous
#print axioms Nock.NockVMROM.Thm54.TraceGen.inputs_op1Execution_isEmpty
#print axioms Nock.NockVMROM.Thm54.TraceGen.inputs_consExecution_isEmpty
