/-
  Nock/NockVMROM/Thm54/TraceGen/Op9StatementK3.lean

  Stage 5 (final) of the OP9 Layer-2 CORE: the released 14-conjunct Theorem-5.4
  instance over `K3` for the fan-out-2 invoke program

      `*[s [9 a b]] = /[a *[s b]]`

  OP9 has TWO serviced roots (`kMem = 2`) and a non-trivial `semanticCoverage`
  (arm fetch via axis-2 on the computed core).  It cannot use the served-vacuous
  `SingleRootCommitment` wrapper; instead it directly invokes
  `BuildablePackage.buildFullPackage` and `universalOptimizedFullStrictThm54`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op9InputsK3
import Nock.NockVMROM.Thm54.BuildablePackage
import Nock.NockVMROM.Thm54.HonestCommitment
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.TraceGen.CubicField97

set_option maxRecDepth 10000

local instance finiteDimK3 : FiniteDimensional F K :=
  (Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.basis :
      Module.Basis (Fin 3) F K).finiteDimensional_of_finite

local instance charRingK3stmt : CharP K (ringChar K) := ringChar.charP K

noncomputable section

variable (hfirst :
  ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
    ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0)

theorem op9_leafIs : GeneratedField.LeafIs (K := K) 2 (.atom 0) (.cell (.atom 9) (.cell (.atom 2) (.cell (.atom 1) (.cell (.cell (.atom 1) (.atom 7)) (.cell (.atom 1) (.atom 9)))))) 7 := by
  gen_simp

theorem op9_evalIsSome : (FieldEmbedding.evalGBy (ringChar K) 2 (.atom 0) (.cell (.atom 9) (.cell (.atom 2) (.cell (.atom 1) (.cell (.cell (.atom 1) (.atom 7)) (.cell (.atom 1) (.atom 9))))))).isSome := by
  eval_simp

/-- Program-level `generated` at any window `Λ ≥ 7`. -/
theorem op9_program_generated (Λ : ℕ) (hΛ : 7 ≤ Λ) :
    ∃ (gfuel : ℕ) (G : Nock.Walk.NTree (TraceGen.GenComputeRow K)) (R : Noun) (fuel : ℕ)
      (r : Noun),
      TraceGen.genComputeSkeleton (K := K) gfuel (.atom 0) (.cell (.atom 9) (.cell (.atom 2) (.cell (.atom 1) (.cell (.cell (.atom 1) (.atom 7)) (.cell (.atom 1) (.atom 9)))))) = .ok (G, R) ∧
        FieldEmbedding.evalGBy (ringChar K) fuel (.atom 0) (.cell (.atom 9) (.cell (.atom 2) (.cell (.atom 1) (.cell (.cell (.atom 1) (.atom 7)) (.cell (.atom 1) (.atom 9)))))) = some r ∧
        TraceGen.programLeafBound (TraceGen.airReorder G) ≤ Λ :=
  GeneratedField.generated_of _ _ _ _ 2 2 (GeneratedField.le_of_leafIs op9_leafIs hΛ)
    op9_evalIsSome

/-- Negative control: zero margin (`Λ = 6` is refuted). -/
theorem op9_leaf_margin_zero :
    ¬ ∃ (G : Nock.Walk.NTree (TraceGen.GenComputeRow K)) (R : Noun),
      TraceGen.genComputeSkeleton (K := K) 2 (.atom 0) (.cell (.atom 9) (.cell (.atom 2) (.cell (.atom 1) (.cell (.cell (.atom 1) (.atom 7)) (.cell (.atom 1) (.atom 9)))))) = .ok (G, R) ∧
        TraceGen.programLeafBound (TraceGen.airReorder G) ≤ 6 := by
  rintro ⟨G, R, hx, hle⟩
  have h := op9_leafIs
  unfold GeneratedField.LeafIs at h
  rw [hx] at h
  simp only at h
  omega

theorem op9Residual_claim :
    (commitmentResidualOfZero (data hfirst)).verifier.raw.claim.subject = (.atom 0) ∧
      (commitmentResidualOfZero (data hfirst)).verifier.raw.claim.formula = (.cell (.atom 9) (.cell (.atom 2) (.cell (.atom 1) (.cell (.cell (.atom 1) (.atom 7)) (.cell (.atom 1) (.atom 9)))))) := by
  show (data hfirst).skeleton.computeTree.label.subject = (.atom 0) ∧
    (data hfirst).skeleton.computeTree.label.formula = (.cell (.atom 9) (.cell (.atom 2) (.cell (.atom 1) (.cell (.cell (.atom 1) (.atom 7)) (.cell (.atom 1) (.atom 9))))))
  simp [HonestCommitment.Data.skeleton, HonestCommitment.skeletonOfNodes, mapNTree_label]
  all_goals (try refine ⟨?_, ?_⟩)
  all_goals first | rfl | decide

/-- `generated` at `commitmentResidualOfZero (data hfirst)` (window `7`). -/
theorem op9Residual_generated :
    GeneratedField.ClaimGenerated K (commitmentResidualOfZero (data hfirst)).verifier.raw.claim (commitmentResidualOfZero (data hfirst)).Λ :=
  GeneratedField.claimGenerated_of_eq (op9Residual_claim hfirst).1 (op9Residual_claim hfirst).2
    (op9_program_generated _ (le_of_eq rfl))

theorem op9_primeField : GeneratedField.PrimeFieldElems F := by
  haveI : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  exact GeneratedField.primeFieldElems_zmod 97

variable {hmore : BuildableAxisWitness.LaterSeedZeros (Op9Execution hfirst)}
include hmore

/-- The OP9/K3 committed residual: built from `commitmentResidualOfZero` over the
two-serviced-root honest `Data`. -/
noncomputable def op9Residual : BuildablePackage.CommitmentResidual (Op9Execution hfirst) :=
  commitmentResidualOfZero (data hfirst)

/-- Dummy-wired later-seed parent accums at `kMem = 2`. -/
theorem op9_laterSeedZeros : BuildableAxisWitness.LaterSeedZeros (Op9Execution hfirst) :=
  hmore

/-- The full optimized strict NockVM-ROM package for OP9. -/
noncomputable def op9Package :
    OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K
      (inputsK3 hfirst).hOrb :=
  buildFullPackage (Op9Execution hfirst) (inputsK3 hfirst) (op9Residual hfirst)
    (inputsK3_challenges hfirst)
    pairedRecordLayout
    hmore
    (hord := fun _ => by
      have hα : (inputsK3 hfirst).computeWalkAlpha = (2 : K) := rfl
      have hrows : (Op9Execution hfirst).cfg.compRows = 3 := rfl
      rw [hα, Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.two_order, hrows]
      norm_num)
    (hordM := fun _ => by
      have hα : (inputsK3 hfirst).memoryWalkAlpha = (3 : K) := rfl
      have hrows : (Op9Execution hfirst).cfg.memRows = 30 := rfl
      rw [hα, Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.three_order, hrows]
      norm_num)
    (hrows := by
      have h1 : (Op9Execution hfirst).cfg.compRows = 3 := rfl
      have h2 : (Op9Execution hfirst).cfg.memRows = 30 := rfl
      rw [h1, h2, ← Algebra.ringChar_eq F K, ZMod.ringChar_zmod_n]
      norm_num)
    (hgenF := op9Residual_generated hfirst) (hF := op9_primeField)

/-- **The released OP9 Theorem-5.4 instance.**  The 14-conjunct
`OptimizedFullStrictThm54Statement` for the two-serviced-root invoke execution. -/
theorem op9Statement
    (hax : FormRAxisBound (op9Package (hmore := hmore) hfirst).optimized.sampled
      (op9Package (hmore := hmore) hfirst).optimized.basis)
    (hbasis : FormRBasis (op9Package (hmore := hmore) hfirst).optimized.basis)
    (hwidth : FormRWidth F) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (op9Package (hmore := hmore) hfirst) :=
  universalOptimizedFullStrictThm54 (Op9Execution hfirst) (inputsK3 hfirst)
    (op9Residual hfirst) (inputsK3_challenges hfirst)
    pairedRecordLayout
    hmore
    (hord := fun _ => by
      have hα : (inputsK3 hfirst).computeWalkAlpha = (2 : K) := rfl
      have hrows : (Op9Execution hfirst).cfg.compRows = 3 := rfl
      rw [hα, Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.two_order, hrows]
      norm_num)
    (hordM := fun _ => by
      have hα : (inputsK3 hfirst).memoryWalkAlpha = (3 : K) := rfl
      have hrows : (Op9Execution hfirst).cfg.memRows = 30 := rfl
      rw [hα, Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.three_order, hrows]
      norm_num)
    (hrows := by
      have h1 : (Op9Execution hfirst).cfg.compRows = 3 := rfl
      have h2 : (Op9Execution hfirst).cfg.memRows = 30 := rfl
      rw [h1, h2, ← Algebra.ringChar_eq F K, ZMod.ringChar_zmod_n]
      norm_num)
    (hgenF := op9Residual_generated hfirst) (hF := op9_primeField)
    hax hbasis hwidth

/-- Non-vacuity witness: the statement type is inhabited. -/
theorem op9_nonvacuous
    (hax : FormRAxisBound (op9Package (hmore := hmore) hfirst).optimized.sampled
      (op9Package (hmore := hmore) hfirst).optimized.basis)
    (hbasis : FormRBasis (op9Package (hmore := hmore) hfirst).optimized.basis)
    (hwidth : FormRWidth F) :
    Nonempty
      (OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (op9Package (hmore := hmore) hfirst)) :=
  ⟨op9Statement (hmore := hmore) hfirst hax hbasis hwidth⟩

end

end Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.op9Residual
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.op9Package
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.op9Statement
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.op9_nonvacuous
