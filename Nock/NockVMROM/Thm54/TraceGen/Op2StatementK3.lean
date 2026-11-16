/-
  Nock/NockVMROM/Thm54/TraceGen/Op2StatementK3.lean

  Stage 3 (final) of the OP2 Layer-2 CORE: the released 14-conjunct Theorem-5.4
  instance over `K3` for the fan-out-3 eval program

      `*[0 [2 [1 [0 1]] [1 [1 5]]]] = 5`

  Built via the generic served-vacuous single-root wrapper
  `statementSR : SingleRootCommit → OptimizedFullStrictThm54Statement`.
  The committed layer is the literal honest `Op2ConfigK3.data` (compute-only /
  served-vacuous; there is no Layer-1 committed served-memory fixture).
-/
import Nock.NockVMROM.Thm54.TraceGen.Op2InputsK3
import Nock.NockVMROM.Thm54.SingleRootCommitment
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.SingleRootModule
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

set_option maxRecDepth 10000

/-- `K3` is finite-dimensional over the base `ZMod 97` (degree `3`), from its power basis. -/
local instance finiteDimK3 : FiniteDimensional F K :=
  (Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.basis :
      Module.Basis (Fin 3) F K).finiteDimensional_of_finite

/-- The consumed-`q` char instance for the cubic table field. -/
local instance charRingK3stmt : CharP K (ringChar K) := ringChar.charP K

noncomputable section

variable (hfirst :
  ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
    ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0)


theorem op2_leafIs : GeneratedField.LeafIs (K := K) 2 (.atom 0) (.cell (.atom 2) (.cell (.cell (.atom 1) (.cell (.atom 0) (.atom 1))) (.cell (.atom 1) (.cell (.atom 1) (.atom 5))))) 7 := by
  gen_simp

theorem op2_evalIsSome : (FieldEmbedding.evalGBy (ringChar K) 2 (.atom 0) (.cell (.atom 2) (.cell (.cell (.atom 1) (.cell (.atom 0) (.atom 1))) (.cell (.atom 1) (.cell (.atom 1) (.atom 5)))))).isSome := by
  eval_simp

/-- Negative control: the window has zero margin (`Λ = 6` is refuted). -/
theorem op2_leaf_margin_zero :
    ¬ ∃ (G : Nock.Walk.NTree (GenComputeRow K)) (R : Noun),
      genComputeSkeleton (K := K) 2 (.atom 0) (.cell (.atom 2) (.cell (.cell (.atom 1) (.cell (.atom 0) (.atom 1))) (.cell (.atom 1) (.cell (.atom 1) (.atom 5))))) = .ok (G, R) ∧
        programLeafBound (airReorder G) ≤ 6 := by
  rintro ⟨G, R, hx, hle⟩
  have h := op2_leafIs
  unfold GeneratedField.LeafIs at h
  rw [hx] at h
  simp only at h
  omega

theorem op2_claim :
    (commitmentResidualOfZero (data hfirst)).verifier.raw.claim.subject = (.atom 0) ∧
      (commitmentResidualOfZero (data hfirst)).verifier.raw.claim.formula = (.cell (.atom 2) (.cell (.cell (.atom 1) (.cell (.atom 0) (.atom 1))) (.cell (.atom 1) (.cell (.atom 1) (.atom 5))))) := by
  show (data hfirst).skeleton.computeTree.label.subject = (.atom 0) ∧
    (data hfirst).skeleton.computeTree.label.formula = (.cell (.atom 2) (.cell (.cell (.atom 1) (.cell (.atom 0) (.atom 1))) (.cell (.atom 1) (.cell (.atom 1) (.atom 5)))))
  simp [Data.skeleton, skeletonOfNodes, mapNTree_label]
  all_goals (try refine ⟨?_, ?_⟩)
  all_goals first | rfl | decide

theorem op2_generated :
    GeneratedField.ClaimGenerated K (commitmentResidualOfZero (data hfirst)).verifier.raw.claim
      (commitmentResidualOfZero (data hfirst)).Λ :=
  GeneratedField.claimGenerated_of_eq (op2_claim hfirst).1 (op2_claim hfirst).2
    (GeneratedField.generated_of _ _ _ _ 2 2
      (GeneratedField.le_of_leafIs op2_leafIs (le_of_eq rfl)) op2_evalIsSome)

theorem op2_primeField : GeneratedField.PrimeFieldElems F := by
  haveI : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  exact GeneratedField.primeFieldElems_zmod 97

noncomputable def op2Commit : SingleRootCommit F K where
  exec := Op2Execution hfirst
  inputs := inputsK3 hfirst
  data := data hfirst
  zeroChallenges := inputsK3_challenges hfirst
  pairedRecordLayout := pairedRecordLayout
  honestVer := honestVer
  walkOrder := fun _ => by
    have hα : (inputsK3 hfirst).computeWalkAlpha = (2 : K) := rfl
    have hrows : (Op2Execution hfirst).cfg.compRows = 4 := rfl
    rw [hα, Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.two_order, hrows]
    norm_num
  memoryWalkOrder := fun _ => by
    have hα : (inputsK3 hfirst).memoryWalkAlpha = (3 : K) := rfl
    have hrows : (Op2Execution hfirst).cfg.memRows = 23 := rfl
    rw [hα, Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.three_order, hrows]
    norm_num
  rowsBound := by
    have h1 : (Op2Execution hfirst).cfg.compRows = 4 := rfl
    have h2 : (Op2Execution hfirst).cfg.memRows = 23 := rfl
    rw [h1, h2, ← Algebra.ringChar_eq F K, ZMod.ringChar_zmod_n]
    norm_num
  generated := op2_generated hfirst
  primeField := op2_primeField

/-- **The released OP2 Theorem-5.4 instance.**  The 14-conjunct
`OptimizedFullStrictThm54Statement` of the served-vacuous single-root package. -/
theorem op2Statement
    (hax : FormRAxisBound (packageSR (op2Commit hfirst) (BuildableAxisWitness.hmore_of_kMem_le_one (Op2Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide))).optimized.sampled
      (packageSR (op2Commit hfirst) (BuildableAxisWitness.hmore_of_kMem_le_one (Op2Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide))).optimized.basis)
    (hbasis : FormRBasis (packageSR (op2Commit hfirst) (BuildableAxisWitness.hmore_of_kMem_le_one (Op2Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide))).optimized.basis)
    (hwidth : FormRWidth F) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
      (packageSR (op2Commit hfirst)
        (BuildableAxisWitness.hmore_of_kMem_le_one (Op2Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide))) :=
  statementSR (op2Commit hfirst)
    (BuildableAxisWitness.hmore_of_kMem_le_one (Op2Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide)) hax hbasis hwidth

/-- Non-vacuity witness: the statement type is inhabited. -/
theorem op2_nonvacuous
    (hax : FormRAxisBound (packageSR (op2Commit hfirst) (BuildableAxisWitness.hmore_of_kMem_le_one (Op2Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide))).optimized.sampled
      (packageSR (op2Commit hfirst) (BuildableAxisWitness.hmore_of_kMem_le_one (Op2Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide))).optimized.basis)
    (hbasis : FormRBasis (packageSR (op2Commit hfirst) (BuildableAxisWitness.hmore_of_kMem_le_one (Op2Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide))).optimized.basis)
    (hwidth : FormRWidth F) :
    Nonempty
      (OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
        (packageSR (op2Commit hfirst)
          (BuildableAxisWitness.hmore_of_kMem_le_one (Op2Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide)))) :=
  statementSR_nonvacuous (op2Commit hfirst)
    (BuildableAxisWitness.hmore_of_kMem_le_one (Op2Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide)) hax hbasis hwidth

end

end Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.op2Commit
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.op2Statement
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.op2_nonvacuous
