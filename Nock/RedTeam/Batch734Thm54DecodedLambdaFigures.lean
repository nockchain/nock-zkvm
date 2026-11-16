/-
  Nock/RedTeam/Batch734Thm54DecodedLambdaFigures.lean

  **The figures after the thirty-second move (lane `lambda-consumer-32nd`).**
  `123 / 122 / 120` are re-proved: the figure theorems (`hostile_soundness_formR_at_two_pow_31/_32`,
  `hostile_soundness_at_paper_configuration`, `hostile_soundness_for_real_programs_at_two_pow_31/_32`)
  take `p8Work` as a numeral and reach none of `workload`, `formRUniformWorkload`,
  `fixedFormRWorkload`, `formRLambdaEvent`, the decoded event (`figures_avoid_the_move`, proof-term
  reach with a positive control).
-/
import Lean
import Nock.NockVMROM.Thm54.RealProgramSoundness
import Nock.NockVMROM.Thm54.HostileWorkloadMajorant
import Nock.NockVMROM.Thm54.GoldilocksParameters
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.RedTeam.Batch333Thm54FinalShape2Binders
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch734

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.GoldilocksParameters

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

theorem formRUniformWorkload_le (T : ProductionStrategy F K) (N M : ℕ)
    (hn : FormRAxisEvent.formRN K ≤ 64)
    (hN : (SemanticStrategy.computeSkeletonRows T.skeleton).length ≤ N)
    (hM : (SemanticStrategy.memorySkeletonRows T.skeleton).length ≤ M) :
    formRUniformWorkload T ≤ M * (3 * N + 130) := by
  unfold formRUniformWorkload
  exact Nat.mul_le_mul hM (by omega)

/-- The thirty-third move's pair summand at a memory-row majorant `M`:
`reqPairWorkload T Λ ≤ M·(2(M ⊔ Λ) − 1)`. -/
theorem reqPairWorkload_le (T : ProductionStrategy F K) (Λ M : ℕ)
    (hM : (SemanticStrategy.memorySkeletonRows T.skeleton).length ≤ M) :
    reqPairWorkload T Λ ≤ M * (2 * (M ⊔ Λ) - 1) := by
  unfold reqPairWorkload
  exact Nat.mul_le_mul hM (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 (max_le_max hM le_rfl)) 1)

/-- `workload_le_p8Majorant` restated at `workload` (verbatim proof). -/
theorem workload_le_p8Majorant'
    (T : ProductionStrategy F K) (Λ topologyBound axisWorkload R M A : ℕ)
    (hrows : (SemanticStrategy.computeSkeletonRows T.skeleton).length ≤ R)
    (htop : topologyBound ≤ 24 * R + 8 * M)
    (hax : axisWorkload + formRUniformWorkload T + reqPairWorkload T Λ ≤ A) :
    workload T Λ topologyBound axisWorkload ≤ p8Majorant R M Λ A := by
  have hsw : SizeWindowCounting.sizeWindowRootBound Λ ≤ Λ * Λ :=
    SizeWindowCounting.sizeWindowRootBound_le_square Λ
  have hcoll :
      (3 + 19 * (SemanticStrategy.computeSkeletonRows T.skeleton).length) * (2 * Λ - 1)
        ≤ (3 + 19 * R) * (2 * Λ) :=
    Nat.mul_le_mul (by omega) (Nat.sub_le _ _)
  simp only [workload, p8Majorant]
  omega

theorem figure_122_after_32nd (T : ProductionStrategy F K) (R M Λ A : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hn : FormRAxisEvent.formRN K ≤ 64)
    (hrows : (SemanticStrategy.computeSkeletonRows T.skeleton).length ≤ R)
    (hmrows : (SemanticStrategy.memorySkeletonRows T.skeleton).length ≤ M)
    (topologyBound axisWorkload : ℕ)
    (htop : topologyBound ≤ 24 * R + 8 * M) (hax : axisWorkload ≤ A) :
    goldilocksHostileFailureBound (workload T Λ topologyBound axisWorkload)
        (FiniteIO.ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 122 := by
  refine hostile_soundness_formR_at_two_pow_31 R M Λ A _ hR hM hΛ hA ?_
  have hf := formRUniformWorkload_le T R M hn hrows hmrows
  have hp := reqPairWorkload_le T Λ M hmrows
  have h := workload_le_p8Majorant' T Λ topologyBound axisWorkload R M
    (A + M * (3 * R + 130) + M * (2 * (M ⊔ Λ) - 1)) hrows htop (by omega)
  have he : p8Majorant R M Λ (A + M * (3 * R + 130) + M * (2 * (M ⊔ Λ) - 1)) =
      p8Majorant R M Λ A + M * (3 * R + 130) + M * (2 * (M ⊔ Λ) - 1) := by
    simp only [p8Majorant]; ring
  omega

theorem figure_120_after_32nd (T : ProductionStrategy F K) (R M Λ A : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hn : FormRAxisEvent.formRN K ≤ 64)
    (hrows : (SemanticStrategy.computeSkeletonRows T.skeleton).length ≤ R)
    (hmrows : (SemanticStrategy.memorySkeletonRows T.skeleton).length ≤ M)
    (topologyBound axisWorkload : ℕ)
    (htop : topologyBound ≤ 24 * R + 8 * M) (hax : axisWorkload ≤ A) :
    goldilocksHostileFailureBound (workload T Λ topologyBound axisWorkload)
        (FiniteIO.ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 120 := by
  refine hostile_soundness_formR_at_two_pow_32 R M Λ A _ hR hM hΛ hA ?_
  have hf := formRUniformWorkload_le T R M hn hrows hmrows
  have hp := reqPairWorkload_le T Λ M hmrows
  have h := workload_le_p8Majorant' T Λ topologyBound axisWorkload R M
    (A + M * (3 * R + 130) + M * (2 * (M ⊔ Λ) - 1)) hrows htop (by omega)
  have he : p8Majorant R M Λ (A + M * (3 * R + 130) + M * (2 * (M ⊔ Λ) - 1)) =
      p8Majorant R M Λ A + M * (3 * R + 130) + M * (2 * (M ⊔ Λ) - 1) := by
    simp only [p8Majorant]; ring
  omega


partial def reach (env : Lean.Environment) (roots : Array Lean.Name) : Std.HashSet Lean.Name := Id.run do
  let mut seen : Std.HashSet Lean.Name := {}
  let mut work := roots.toList
  while true do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      if !(`Nock).isPrefixOf n then continue
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
        for c in cs do
          unless seen.contains c do work := c :: work
  return seen

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let T := `Nock.NockVMROM.Thm54
  let figs := #[T ++ `RealProgramSoundness.hostile_soundness_formR_at_two_pow_31,
    T ++ `RealProgramSoundness.hostile_soundness_formR_at_two_pow_32,
    T ++ `GoldilocksParameters.hostile_soundness_at_paper_configuration,
    T ++ `RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_31,
    T ++ `RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_32]
  let moved := #[T ++ `ProductionP8Containment.workload, T ++ `ProductionP8Containment.formRUniformWorkload,
    T ++ `ProductionP8Containment.fixedFormRWorkload, T ++ `FormRAxisEvent.formRLambdaEvent,
    T ++ `DecodedLambdaEvent.decodedLambdaEventOfEnvs]
  for f in figs do
    let cl := reach env #[f]
    for n in moved do
      if cl.contains n then throwError m!"{f} reaches {n}"
  -- positive control: the composed figure does reach `workload` and the uniform summand
  let pc := reach env #[`Nock.RedTeam.Batch734.figure_122_after_32nd]
  unless pc.contains (T ++ `ProductionP8Containment.workload) ∧
      pc.contains (T ++ `ProductionP8Containment.formRUniformWorkload) do
    throwError "positive control failed"
  logInfo "figures_avoid_the_move: the five figure theorems reach none of the moved names; positive control reaches workload and formRUniformWorkload"

end Nock.RedTeam.Batch734

#print axioms Nock.RedTeam.Batch734.formRUniformWorkload_le
#print axioms Nock.RedTeam.Batch734.figure_122_after_32nd
#print axioms Nock.RedTeam.Batch734.figure_120_after_32nd
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.hostile_soundness_formR_at_two_pow_31
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.hostile_soundness_formR_at_two_pow_32
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.hostile_soundness_at_paper_configuration
