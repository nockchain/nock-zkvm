/-
FRI's native guards and terminal
check, and the law tying the terminal check to the legacy verifier.

* `trueGuards`: the guard schedule that never stops early. FRI's fold verifiers check nothing per
  round; its only per-round check (final `natDegree < d`, `SingleRound.lean:550`) is carried by the
  native message type, so no guard is needed. The FS theorem holds for *every* guard
  schedule; `trueGuards` is the canonical one.
* `friAccepts`: the native terminal check = the legacy acceptance predicate `queryBad` (final
  degree check ∧ `QueryRound.verifyQueries` returns `some`, `BadEvents.lean:31-39`) evaluated on
  the legacy full transcript decoded from the native path (`Lift.Alternating.pathTranscript`).
  It is classical (`decide` on a `Prop`); the FS theorem only needs a `Bool`-valued function.
* `friAccepts_run_true` / `_false`: the law. On the decoded transcript the legacy FRI verifier
  (`(reduction k s d hdom l).verifier.toVerifier`, ambient `[]ₒ`, `General.lean:91`) returns `some`
  iff `friAccepts` holds (from `Fri.Spec.reduction_run`, `VerifierExecution.lean:167`).
-/
import NockvmE2E.FriPort.Rounds

open OracleComp OracleSpec ProtocolSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Fri.Spec Domain

set_option linter.unusedSectionVars false

namespace NockvmE2E.FriPort

/-- The guard schedule that accepts every message (no early stop). -/
def trueGuards {Input Salt : Type} : (rounds : List Round) → GuardSchedule Input Salt rounds
  | [] => PUnit.unit
  | _ :: rounds => (fun _ _ _ => true, fun _ _ _ => trueGuards rounds)

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]

/-- FRI's legacy input statement: no challenges yet, and the initial oracle word. -/
abbrev FriStmt := Statement (k := k) F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j

variable (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)

/-- The legacy full transcript of a native FRI path. -/
noncomputable abbrev friTranscript
    (path : (protocol (friRounds (ω := ω) s d l)).tree.ExecutionPath) :
    (pSpec k (ω := ω) s l).FullTranscript :=
  (friAlt (ω := ω) s d l).pathTranscript path

/-- **F2. FRI's native terminal check**: the legacy FRI acceptance predicate (final degree check
and all query-path folding checks) on the decoded legacy transcript. -/
noncomputable def friAccepts {Salt : Type} (z : FriStmt (ω := ω) s × Salt)
    (path : (protocol (friRounds (ω := ω) s d l)).tree.ExecutionPath) : Bool :=
  open Classical in
  decide (queryBad s d l (round_bound hdom) (initialOracle s z.1)
    (Transcript.restrict (b := Fin.last _) (by simp only [Fin.val_succ, Fin.val_last]; omega)
      (friTranscript s d l path)))

theorem friAccepts_iff {Salt : Type} (z : FriStmt (ω := ω) s × Salt)
    (path : (protocol (friRounds (ω := ω) s d l)).tree.ExecutionPath) :
    friAccepts s d l hdom z path = true ↔
      queryBad s d l (round_bound hdom) (initialOracle s z.1)
        (Transcript.restrict (b := Fin.last _) (by simp only [Fin.val_succ, Fin.val_last]; omega)
          (friTranscript s d l path)) := by
  classical
  unfold friAccepts
  exact decide_eq_true_iff

/-- **F2 law, accept side.** If `friAccepts`, the legacy FRI verifier run on the decoded
transcript returns `some`. -/
theorem friAccepts_run_true {Salt : Type} (z : FriStmt (ω := ω) s × Salt)
    (path : (protocol (friRounds (ω := ω) s d l)).tree.ExecutionPath)
    (h : friAccepts s d l hdom z path = true) :
    ∃ out, ((reduction k s d hdom l).verifier.toVerifier.run z.1 (friTranscript s d l path)).run =
      pure (some out) := by
  rw [reduction_run]
  simp only [(friAccepts_iff s d l hdom z path).mp h, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- **F2 law, reject side.** If not `friAccepts`, the legacy FRI verifier run on the decoded
transcript returns `none`. -/
theorem friAccepts_run_false {Salt : Type} (z : FriStmt (ω := ω) s × Salt)
    (path : (protocol (friRounds (ω := ω) s d l)).tree.ExecutionPath)
    (h : friAccepts s d l hdom z path = false) :
    ((reduction k s d hdom l).verifier.toVerifier.run z.1 (friTranscript s d l path)).run =
      pure none := by
  have hq : ¬ queryBad s d l (round_bound hdom) (initialOracle s z.1)
      (Transcript.restrict (b := Fin.last _) (by simp only [Fin.val_succ, Fin.val_last]; omega)
        (friTranscript s d l path)) := fun hq => by
    rw [← friAccepts_iff s d l hdom z path, h] at hq; exact Bool.noConfusion hq
  rw [reduction_run]
  simp only [hq, ↓reduceIte]

end NockvmE2E.FriPort
