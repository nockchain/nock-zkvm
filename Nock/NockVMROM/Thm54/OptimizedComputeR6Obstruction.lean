import Nock.NockVMROM.Thm54.OptimizedComputeFinal
import Nock.NockVMROM.Thm54.OptimizedComputeSampledTrace

/-!
# R6 same-object compute compiler alias regression and repair

The direct
final compiler repairs both aliases: challenges use disjoint namespaces and extension role 61
carries the walk line.

The current optimized substitution assigns both the compute-table timestamp challenge and the
compute-walk recurrence challenge to physical challenge slot zero.  It likewise assigns both the
compute-table line nonce and the compute-walk line value to extension role 55.  Those identifications
are not valid for the already-accepted concrete same-execution assignment: its table timestamp and
table line are `4`, while its independently sampled compute-walk challenge and first line are `0`.

The old impossibility remains a regression theorem. The production 62-role compiler has a general
same-object recovery environment and recovers the concrete `4/0` assignment exactly. This is a
connective/compiler implementation repair, not a claim about the paper construction.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeR6Obstruction

open Nock
open Nock.Reified
open OptimizedComputeSubstitution
open OptimizedComputeSampledTrace
open OptimizedComputeSampledTrace.Concrete
open ConcreteStrictPackage

noncomputable section

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance char73 : CharP K73cubic 73 := inferInstance
local instance charRing : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- The current compiler uses one physical challenge variable for two semantically independent
challenges. -/
theorem legacy_compute_walk_challenge_physical_collision :
    computeSubst .challenge 0 = walkSubst .challenge 0 := by
  rfl

/-- The current compiler also uses one physical extension value for the table line nonce and the
compute-walk line. -/
theorem legacy_compute_walk_line_physical_collision :
    computeTraceSubst .traceCur 66 = walkSubst .traceCur 0 := by
  rfl

/-- The concrete table timestamp challenge is four. -/
theorem concrete_table_timestamp_eq_four :
    honestLegacyFamily.problem.cfg.challenges.computeInputs.α = (4 : K73cubic) := by
  change (cfg honestSeed honestAlpha).challenges.computeInputs.α = (4 : K73cubic)
  rfl

/-- The same concrete family's compute-walk challenge is independently zero. -/
theorem concrete_compute_walk_challenge_eq_zero :
    honestLegacyFamily.computeWalkAlpha = (0 : K73cubic) := by
  rfl

/-- The concrete table row stores line nonce four. -/
theorem concrete_table_line_eq_four :
    (honestLegacyFamily.problem.exec.computePubAt honestRowIndex).ln =
      (4 : K73cubic) := by
  rw [honest_computePubAt]
  rfl

/-- The accepted same-execution compute-walk certificate stores first line zero. -/
theorem concrete_compute_walk_line_eq_zero :
    honestSampled.exact.computeWalk.ln 1 = (0 : K73cubic) := by
  have hline := honest_obligations.2.1.1.ln1
  calc
    honestSampled.exact.computeWalk.ln 1 =
        honestLegacyFamily.computeWalkAlpha := hline
    _ = 0 := concrete_compute_walk_challenge_eq_zero

/-- Exact recovery premises required by a same-object row decoder using the current substitution.
The fields mention the actual compiler expressions, not an abstract slot-count argument. -/
structure CurrentCompilerSameObjectRecovery (env : Env K73cubic) : Prop where
  tableChallenge :
    (computeSubst .challenge 0).eval env =
      honestLegacyFamily.problem.cfg.challenges.computeInputs.α
  walkChallenge :
    (walkSubst .challenge 0).eval env = honestLegacyFamily.computeWalkAlpha
  tableLine :
    (computeTraceSubst .traceCur 66).eval env =
      (honestLegacyFamily.problem.exec.computePubAt honestRowIndex).ln
  walkLine :
    (walkSubst .traceCur 0).eval env = honestSampled.exact.computeWalk.ln 1

/-- No physical environment can decode the concrete same-execution table and walk challenges
through the current compiler. -/
theorem no_current_compiler_same_object_challenges (env : Env K73cubic) :
    ¬ ((computeSubst .challenge 0).eval env =
        honestLegacyFamily.problem.cfg.challenges.computeInputs.α ∧
      (walkSubst .challenge 0).eval env = honestLegacyFamily.computeWalkAlpha) := by
  rintro ⟨htable, hwalk⟩
  have hsame :
      honestLegacyFamily.problem.cfg.challenges.computeInputs.α =
        honestLegacyFamily.computeWalkAlpha := by
    calc
      honestLegacyFamily.problem.cfg.challenges.computeInputs.α =
          (computeSubst .challenge 0).eval env := htable.symm
      _ = (walkSubst .challenge 0).eval env := by
        rw [legacy_compute_walk_challenge_physical_collision]
      _ = honestLegacyFamily.computeWalkAlpha := hwalk
  rw [concrete_table_timestamp_eq_four,
    concrete_compute_walk_challenge_eq_zero] at hsame
  exact
    (@SetEq.Lcast_ne_zero K73cubic _ 73 char73 4 (by norm_num) (by norm_num))
      hsame

/-- Independently, no physical environment can decode both concrete first-row line values through
the current shared extension role. -/
theorem no_current_compiler_same_object_lines (env : Env K73cubic) :
    ¬ ((computeTraceSubst .traceCur 66).eval env =
        (honestLegacyFamily.problem.exec.computePubAt honestRowIndex).ln ∧
      (walkSubst .traceCur 0).eval env = honestSampled.exact.computeWalk.ln 1) := by
  rintro ⟨htable, hwalk⟩
  have hsame :
      (honestLegacyFamily.problem.exec.computePubAt honestRowIndex).ln =
        honestSampled.exact.computeWalk.ln 1 := by
    calc
      (honestLegacyFamily.problem.exec.computePubAt honestRowIndex).ln =
          (computeTraceSubst .traceCur 66).eval env := htable.symm
      _ = (walkSubst .traceCur 0).eval env := by
        rw [legacy_compute_walk_line_physical_collision]
      _ = honestSampled.exact.computeWalk.ln 1 := hwalk
  rw [concrete_table_line_eq_four, concrete_compute_walk_line_eq_zero] at hsame
  exact
    (@SetEq.Lcast_ne_zero K73cubic _ 73 char73 4 (by norm_num) (by norm_num))
      hsame

/-- Compiled stop condition for the requested concrete canonical trace and arbitrary-trace
same-object language: the current compiler cannot recover all four required values even at the
unique active concrete row. -/
theorem current_compiler_same_object_recovery_is_empty (env : Env K73cubic) :
    ¬ CurrentCompilerSameObjectRecovery env := by
  intro h
  exact no_current_compiler_same_object_challenges env
    ⟨h.tableChallenge, h.walkChallenge⟩

/-! ## Production repair -/

structure FinalCompilerSameObjectRecovery (env : Env K73cubic) : Prop where
  tableChallenge :
    (computeSubst .challenge 0).eval env =
      honestLegacyFamily.problem.cfg.challenges.computeInputs.α
  walkChallenge :
    (finalWalkSubst .challenge 0).eval env = honestLegacyFamily.computeWalkAlpha
  tableLine :
    (computeTraceSubst .traceCur 66).eval env =
      (honestLegacyFamily.problem.exec.computePubAt honestRowIndex).ln
  walkLine :
    (finalWalkSubst .traceCur 0).eval env = honestSampled.exact.computeWalk.ln 1

/-- A physical environment with independent table/walk challenge and line values. -/
def finalRecoveryEnv (tableChallengeValue walkChallengeValue tableLineValue walkLineValue :
    K73cubic) : Env K73cubic where
  trace i :=
    if i = ext0 + 55 then tableLineValue
    else if i = finalWalkLineIndex then walkLineValue
    else 0
  traceNext := fun _ => 0
  chal i :=
    if i = tableChallengeBase then tableChallengeValue
    else if i = walkChallengeBase then walkChallengeValue
    else 0
  pub := fun _ => 0

theorem final_compiler_recovers_independent_values
    (tableChallengeValue walkChallengeValue tableLineValue walkLineValue : K73cubic) :
    (computeSubst .challenge 0).eval
        (finalRecoveryEnv tableChallengeValue walkChallengeValue tableLineValue walkLineValue) =
        tableChallengeValue ∧
      (finalWalkSubst .challenge 0).eval
        (finalRecoveryEnv tableChallengeValue walkChallengeValue tableLineValue walkLineValue) =
        walkChallengeValue ∧
      (computeTraceSubst .traceCur 66).eval
        (finalRecoveryEnv tableChallengeValue walkChallengeValue tableLineValue walkLineValue) =
        tableLineValue ∧
      (finalWalkSubst .traceCur 0).eval
        (finalRecoveryEnv tableChallengeValue walkChallengeValue tableLineValue walkLineValue) =
        walkLineValue := by
  simp [Expr.eval, computeSubst, finalWalkSubst, walkChallenge, finalRecoveryEnv,
    computeTraceSubst, lnCur, finalWalkLine, finalWalkLineIndex, finalWalkLineRole,
    ext0, tableChallengeBase, walkChallengeBase]

def concreteFinalRecoveryEnv : Env K73cubic :=
  finalRecoveryEnv
    honestLegacyFamily.problem.cfg.challenges.computeInputs.α
    honestLegacyFamily.computeWalkAlpha
    (honestLegacyFamily.problem.exec.computePubAt honestRowIndex).ln
    (honestSampled.exact.computeWalk.ln 1)

theorem concrete_final_compiler_same_object_recovery :
    FinalCompilerSameObjectRecovery concreteFinalRecoveryEnv := by
  have h := final_compiler_recovers_independent_values
    honestLegacyFamily.problem.cfg.challenges.computeInputs.α
    honestLegacyFamily.computeWalkAlpha
    (honestLegacyFamily.problem.exec.computePubAt honestRowIndex).ln
    (honestSampled.exact.computeWalk.ln 1)
  exact ⟨by simpa [concreteFinalRecoveryEnv] using h.1,
    by simpa [concreteFinalRecoveryEnv] using h.2.1,
    by simpa [concreteFinalRecoveryEnv] using h.2.2.1,
    by simpa [concreteFinalRecoveryEnv] using h.2.2.2⟩

theorem concrete_final_recovers_four_zero :
    (computeSubst .challenge 0).eval concreteFinalRecoveryEnv = 4 ∧
      (finalWalkSubst .challenge 0).eval concreteFinalRecoveryEnv = 0 ∧
      (computeTraceSubst .traceCur 66).eval concreteFinalRecoveryEnv = 4 ∧
      (finalWalkSubst .traceCur 0).eval concreteFinalRecoveryEnv = 0 := by
  exact ⟨by
      simpa [concrete_table_timestamp_eq_four] using
        concrete_final_compiler_same_object_recovery.tableChallenge,
    by
      calc
        (finalWalkSubst .challenge 0).eval concreteFinalRecoveryEnv =
            honestLegacyFamily.computeWalkAlpha :=
          concrete_final_compiler_same_object_recovery.walkChallenge
        _ = 0 := concrete_compute_walk_challenge_eq_zero,
    by
      simpa [concrete_table_line_eq_four] using
        concrete_final_compiler_same_object_recovery.tableLine,
    by
      calc
        (finalWalkSubst .traceCur 0).eval concreteFinalRecoveryEnv =
            honestSampled.exact.computeWalk.ln 1 :=
          concrete_final_compiler_same_object_recovery.walkLine
        _ = 0 := concrete_compute_walk_line_eq_zero⟩

#print axioms legacy_compute_walk_challenge_physical_collision
#print axioms legacy_compute_walk_line_physical_collision
#print axioms concrete_table_timestamp_eq_four
#print axioms concrete_compute_walk_challenge_eq_zero
#print axioms concrete_table_line_eq_four
#print axioms concrete_compute_walk_line_eq_zero
#print axioms no_current_compiler_same_object_challenges
#print axioms no_current_compiler_same_object_lines
#print axioms current_compiler_same_object_recovery_is_empty
#print axioms final_compiler_recovers_independent_values
#print axioms concrete_final_compiler_same_object_recovery
#print axioms concrete_final_recovers_four_zero

end
end OptimizedComputeR6Obstruction
end Nock.NockVMROM.Thm54
