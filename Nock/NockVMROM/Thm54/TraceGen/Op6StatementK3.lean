/-
  Nock/NockVMROM/Thm54/TraceGen/Op6StatementK3.lean

  Stage 5 (final) of the OP6 Layer-2 CORE: the released 14-conjunct Theorem-5.4
  instance over `K3` for the fan-out-2 branch (if) program

      `*[s [6 a b c]] = *[*[s a] b] or *[*[s a] c]`

  Built via the generic served-vacuous single-root wrapper
  `statementSR : SingleRootCommit → OptimizedFullStrictThm54Statement`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op6InputsK3
import Nock.NockVMROM.Thm54.SingleRootCommitment
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.SingleRootModule
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

set_option maxRecDepth 10000

local instance finiteDimK3 : FiniteDimensional F K :=
  (Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.basis :
      Module.Basis (Fin 3) F K).finiteDimensional_of_finite

local instance charRingK3stmt : CharP K (ringChar K) := ringChar.charP K

noncomputable section

variable (hfirst :
  ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
    ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0)


theorem op6_leafIs : GeneratedField.LeafIs (K := K) 2 (.atom 0) (.cell (.atom 6) (.cell (.cell (.atom 1) (.atom 0)) (.cell (.cell (.atom 1) (.atom 5)) (.cell (.atom 1) (.atom 6))))) 7 := by
  gen_simp

theorem op6_evalIsSome : (FieldEmbedding.evalGBy (ringChar K) 2 (.atom 0) (.cell (.atom 6) (.cell (.cell (.atom 1) (.atom 0)) (.cell (.cell (.atom 1) (.atom 5)) (.cell (.atom 1) (.atom 6)))))).isSome := by
  eval_simp

/-- Negative control: the window has zero margin (`Λ = 6` is refuted). -/
theorem op6_leaf_margin_zero :
    ¬ ∃ (G : Nock.Walk.NTree (GenComputeRow K)) (R : Noun),
      genComputeSkeleton (K := K) 2 (.atom 0) (.cell (.atom 6) (.cell (.cell (.atom 1) (.atom 0)) (.cell (.cell (.atom 1) (.atom 5)) (.cell (.atom 1) (.atom 6))))) = .ok (G, R) ∧
        programLeafBound (airReorder G) ≤ 6 := by
  rintro ⟨G, R, hx, hle⟩
  have h := op6_leafIs
  unfold GeneratedField.LeafIs at h
  rw [hx] at h
  simp only at h
  omega

theorem op6_claim :
    (commitmentResidualOfZero (data hfirst)).verifier.raw.claim.subject = (.atom 0) ∧
      (commitmentResidualOfZero (data hfirst)).verifier.raw.claim.formula = (.cell (.atom 6) (.cell (.cell (.atom 1) (.atom 0)) (.cell (.cell (.atom 1) (.atom 5)) (.cell (.atom 1) (.atom 6))))) := by
  show (data hfirst).skeleton.computeTree.label.subject = (.atom 0) ∧
    (data hfirst).skeleton.computeTree.label.formula = (.cell (.atom 6) (.cell (.cell (.atom 1) (.atom 0)) (.cell (.cell (.atom 1) (.atom 5)) (.cell (.atom 1) (.atom 6)))))
  simp [Data.skeleton, skeletonOfNodes, mapNTree_label]
  all_goals (try refine ⟨?_, ?_⟩)
  all_goals first | rfl | decide

theorem op6_generated :
    GeneratedField.ClaimGenerated K (commitmentResidualOfZero (data hfirst)).verifier.raw.claim
      (commitmentResidualOfZero (data hfirst)).Λ :=
  GeneratedField.claimGenerated_of_eq (op6_claim hfirst).1 (op6_claim hfirst).2
    (GeneratedField.generated_of _ _ _ _ 2 2
      (GeneratedField.le_of_leafIs op6_leafIs (le_of_eq rfl)) op6_evalIsSome)

theorem op6_primeField : GeneratedField.PrimeFieldElems F := by
  haveI : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  exact GeneratedField.primeFieldElems_zmod 97

noncomputable def op6Commit : SingleRootCommit F K where
  exec := Op6Execution hfirst
  inputs := inputsK3 hfirst
  data := data hfirst
  zeroChallenges := inputsK3_challenges hfirst
  pairedRecordLayout := pairedRecordLayout
  honestVer := honestVer
  walkOrder := fun _ => by
    have hα : (inputsK3 hfirst).computeWalkAlpha = (2 : K) := rfl
    have hrows : (Op6Execution hfirst).cfg.compRows = 3 := rfl
    rw [hα, Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.two_order, hrows]
    norm_num
  memoryWalkOrder := fun _ => by
    have hα : (inputsK3 hfirst).memoryWalkAlpha = (3 : K) := rfl
    have hrows : (Op6Execution hfirst).cfg.memRows = 23 := rfl
    rw [hα, Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.three_order, hrows]
    norm_num
  rowsBound := by
    have h1 : (Op6Execution hfirst).cfg.compRows = 3 := rfl
    have h2 : (Op6Execution hfirst).cfg.memRows = 23 := rfl
    rw [h1, h2, ← Algebra.ringChar_eq F K, ZMod.ringChar_zmod_n]
    norm_num
  generated := op6_generated hfirst
  primeField := op6_primeField

theorem op6Statement
    (hax : FormRAxisBound (packageSR (op6Commit hfirst) (BuildableAxisWitness.hmore_of_kMem_le_one (Op6Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide))).optimized.sampled
      (packageSR (op6Commit hfirst) (BuildableAxisWitness.hmore_of_kMem_le_one (Op6Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide))).optimized.basis)
    (hbasis : FormRBasis (packageSR (op6Commit hfirst) (BuildableAxisWitness.hmore_of_kMem_le_one (Op6Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide))).optimized.basis)
    (hwidth : FormRWidth F) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageSR (op6Commit hfirst) (BuildableAxisWitness.hmore_of_kMem_le_one (Op6Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide))) :=
  statementSR (op6Commit hfirst) (BuildableAxisWitness.hmore_of_kMem_le_one (Op6Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide)) hax hbasis hwidth

theorem op6_nonvacuous
    (hax : FormRAxisBound (packageSR (op6Commit hfirst) (BuildableAxisWitness.hmore_of_kMem_le_one (Op6Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide))).optimized.sampled
      (packageSR (op6Commit hfirst) (BuildableAxisWitness.hmore_of_kMem_le_one (Op6Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide))).optimized.basis)
    (hbasis : FormRBasis (packageSR (op6Commit hfirst) (BuildableAxisWitness.hmore_of_kMem_le_one (Op6Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide))).optimized.basis)
    (hwidth : FormRWidth F) :
    Nonempty
      (OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageSR (op6Commit hfirst) (BuildableAxisWitness.hmore_of_kMem_le_one (Op6Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide)))) :=
  statementSR_nonvacuous (op6Commit hfirst) (BuildableAxisWitness.hmore_of_kMem_le_one (Op6Execution hfirst) (by
        change (cfg seedZ alphaA).kMem ≤ 1
        decide)) hax hbasis hwidth

end

end Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.op6Commit
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.op6Statement
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.op6_nonvacuous
