/-
  Nock/NockVMROM/Thm54/TraceGen/Op1StatementK3.lean

  The GENERATED, EXECUTABLE Theorem-5.4 statement instance
  over the computable cubic table field `K3`.

  This is exactly the statement the degree-1 OP1 slice provably could NOT form
  (`GenStatement.inputs_op1Execution_isEmpty`): `buildFullPackage` needs `I : Inputs E`, and
  `Inputs E` carries `basis : Basis (Fin 3) F K`, which over `F = K = ZMod 97` (`finrank = 1`) cannot
  exist.  Re-basing the OP1 execution over `K = K3` (`finrank (ZMod 97) K3 = 3`) fills that wall with
  `K3`'s power basis (`inputsK3`), and the unchanged capstone bridge
  `statement_of_generated_residual` then produces the fourteen-field
  `OptimizedFullStrictThm54Statement` of a package whose committed half is `dataK3Generated` — the
  GENERATOR's own OP1 node trees, emitted by `genTrace` over `K3` on the fresh program `*[0 [1 5]]`
  and packaged by `dataOfGeneratedK3` (`Op1GenDataK3.lean`), NOT the hand-built literal
  `Op1ConfigK3.data`.  So the "generated" label is now earned: the committed layer this capstone
  consumes is produced end-to-end by the executable trace generator, and only the field-agnostic
  census/bind/timestamp obligations are transported from the verified literal commitment across the
  proved node-tree equalities (`gen_computeNodesK3_eq` / `gen_memForestK3_eq`).
-/
import Nock.NockVMROM.Thm54.TraceGen.Op1InputsK3
import Nock.NockVMROM.Thm54.TraceGen.Op1GenDataK3
import Nock.NockVMROM.Thm54.TraceGen.GenStatement
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.MemoryTable

set_option maxRecDepth 10000

/-- `K3` is finite-dimensional over the base `ZMod 97` (degree `3`), from its power basis. -/
local instance finiteDimK3 : FiniteDimensional F K :=
  (Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.basis :
      Module.Basis (Fin 3) F K).finiteDimensional_of_finite

/-- The consumed-`q` char instance for the cubic table field (`BuildablePackage.lean:397`). -/
local instance charRingK3stmt : CharP K (ringChar K) := ringChar.charP K

noncomputable section

variable
  (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
  (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
  (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA))
  (hmore : BuildableAxisWitness.LaterSeedZeros (Op1Execution_K3 hread hdec hver))


theorem op1_leafIs : GeneratedField.LeafIs (K := K) 1 (.atom 0) (.cell (.atom 1) (.atom 5)) 2 := by
  gen_simp

theorem op1_evalIsSome : (FieldEmbedding.evalGBy (ringChar K) 1 (.atom 0) (.cell (.atom 1) (.atom 5))).isSome := by
  eval_simp

/-- Program-level `generated` at any window `Λ ≥ 2`. -/
theorem op1_program_generated (Λ : ℕ) (hΛ : 2 ≤ Λ) :
    ∃ (gfuel : ℕ) (G : Nock.Walk.NTree (TraceGen.GenComputeRow K)) (R : Noun) (fuel : ℕ)
      (r : Noun),
      TraceGen.genComputeSkeleton (K := K) gfuel (.atom 0) (.cell (.atom 1) (.atom 5)) = .ok (G, R) ∧
        FieldEmbedding.evalGBy (ringChar K) fuel (.atom 0) (.cell (.atom 1) (.atom 5)) = some r ∧
        TraceGen.programLeafBound (TraceGen.airReorder G) ≤ Λ :=
  GeneratedField.generated_of _ _ _ _ 1 1 (GeneratedField.le_of_leafIs op1_leafIs hΛ)
    op1_evalIsSome

/-- Negative control: zero margin (`Λ = 1` is refuted). -/
theorem op1_leaf_margin_zero :
    ¬ ∃ (G : Nock.Walk.NTree (TraceGen.GenComputeRow K)) (R : Noun),
      TraceGen.genComputeSkeleton (K := K) 1 (.atom 0) (.cell (.atom 1) (.atom 5)) = .ok (G, R) ∧
        TraceGen.programLeafBound (TraceGen.airReorder G) ≤ 1 := by
  rintro ⟨G, R, hx, hle⟩
  have h := op1_leafIs
  unfold GeneratedField.LeafIs at h
  rw [hx] at h
  simp only at h
  omega

omit hmore in
theorem op1_claim :
    (dataK3Generated hread hdec hver).skeleton.publicClaim.subject = (.atom 0) ∧
      (dataK3Generated hread hdec hver).skeleton.publicClaim.formula = (.cell (.atom 1) (.atom 5)) := by
  show (dataK3Generated hread hdec hver).skeleton.computeTree.label.subject = _ ∧
    (dataK3Generated hread hdec hver).skeleton.computeTree.label.formula = _
  simp only [Data.skeleton, skeletonOfNodes, mapNTree_label]
  show ((mapNTree GenComputeRow.node op1GenTraceK3.computeNodes).label).skel.subject = _ ∧
    ((mapNTree GenComputeRow.node op1GenTraceK3.computeNodes).label).skel.formula = _
  rw [op1GenTraceK3OK.computeNodes_eq]
  exact ⟨rfl, rfl⟩

omit hmore in
/-- `generated` at the generated OP1 commitment, window `Λ = 3` (leaf bound 2). -/
theorem op1_generated :
    GeneratedField.ClaimGenerated K (dataK3Generated hread hdec hver).skeleton.publicClaim
      (dataK3Generated hread hdec hver).Λ :=
  GeneratedField.claimGenerated_of_eq (op1_claim hread hdec hver).1 (op1_claim hread hdec hver).2
    (op1_program_generated _ (by show 2 ≤ 3; norm_num))

theorem op1_primeField : GeneratedField.PrimeFieldElems F := by
  haveI : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  exact GeneratedField.primeFieldElems_zmod 97

/-- **The generated OP1/K3 Theorem-5.4 package.**
-/
noncomputable def op1PackageK3 :
    OptimizedFullStrictNockVMROMPackage F K (inputsK3 hread hdec hver).hOrb :=
  buildFullPackage (Op1Execution_K3 hread hdec hver) (inputsK3 hread hdec hver) (commitmentResidualOfZero (dataK3Generated hread hdec hver))
    (inputsK3_challenges hread hdec hver) (pairedRecordLayout seedZ alphaA)
    hmore
    (fun h => by
      have : (Op1Execution_K3 hread hdec hver).cfg.compRows = 1 := rfl
      omega)
    (fun _ => by
      have hα : (inputsK3 hread hdec hver).memoryWalkAlpha = (3 : K) := rfl
      have hrows : (Op1Execution_K3 hread hdec hver).cfg.memRows = 6 := rfl
      rw [hα, Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.three_order, hrows]
      norm_num)
    (by
      have h1 : (Op1Execution_K3 hread hdec hver).cfg.compRows = 1 := rfl
      have h2 : (Op1Execution_K3 hread hdec hver).cfg.memRows = 6 := rfl
      rw [h1, h2, ← Algebra.ringChar_eq F K, ZMod.ringChar_zmod_n]
      norm_num)
    (op1_generated hread hdec hver) op1_primeField

/-- **The generated, executable Theorem-5.4 statement instance over the cubic field `K3`.**  The
fourteen-field released `OptimizedFullStrictThm54Statement` holds of `op1PackageK3`, whose committed
layer is `dataK3Generated` — the GENERATOR's own node trees emitted by `genTrace` over `K3`, not the
hand-built literal `Op1ConfigK3.data` -/
theorem op1StatementK3
    (hax : FormRAxisBound (op1PackageK3 hread hdec hver hmore).optimized.sampled
      (op1PackageK3 hread hdec hver hmore).optimized.basis)
    (hbasis : FormRBasis (op1PackageK3 hread hdec hver hmore).optimized.basis)
    (hwidth : FormRWidth F) :
    OptimizedFullStrictThm54Statement (op1PackageK3 hread hdec hver hmore) :=
  Nock.NockVMROM.Thm54.TraceGen.statement_of_generated_residual (dataK3Generated hread hdec hver) (inputsK3 hread hdec hver)
    (inputsK3_challenges hread hdec hver) (pairedRecordLayout seedZ alphaA)
    hmore
    (fun h => by
      have : (Op1Execution_K3 hread hdec hver).cfg.compRows = 1 := rfl
      omega)
    (fun _ => by
      have hα : (inputsK3 hread hdec hver).memoryWalkAlpha = (3 : K) := rfl
      have hrows : (Op1Execution_K3 hread hdec hver).cfg.memRows = 6 := rfl
      rw [hα, Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.three_order, hrows]
      norm_num)
    (by
      have h1 : (Op1Execution_K3 hread hdec hver).cfg.compRows = 1 := rfl
      have h2 : (Op1Execution_K3 hread hdec hver).cfg.memRows = 6 := rfl
      rw [h1, h2, ← Algebra.ringChar_eq F K, ZMod.ringChar_zmod_n]
      norm_num)
    (op1_generated hread hdec hver) op1_primeField
    hax hbasis hwidth

end

end Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3.op1PackageK3
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3.op1StatementK3
