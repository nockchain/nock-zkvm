/-
Merkle (B) file 5: the paired public stopped verification, run on the compiled key domain
through `untranslateK`, equals the compiled verification up to its terminal opening round.
-/
import NockvmE2E.Merkle.Reduction

open OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle.VerifyTransport

open NockvmE2E.Merkle NockvmE2E.Merkle.Reduction

section

variable {Y : Type} [Finite Y] [DecidableEq Y] {Op : Type} [Finite Op] [DecidableEq Op]
  {Input : Type} {All : List Round}

/-- The compiled verification of a proof, given the paired path already traversed: the same queries
as the paired verification, then (at the end) the opening round's stage. Defined by recursion on
the mask, following the paired path. -/
def finishK (z : Input) :
    (ms : MRounds Y) → GuardSchedule Input PUnit (compiledRoundsK Y Op ms) →
    PublicMessages (compiledRoundsK Y Op ms) →
    (E : Key Input PUnit (compiledRoundsK Y Op ms) → Key Input PUnit All) →
    (∀ k, (E k).Challenge = k.Challenge) →
    (protocol (pairedRoundsK Y ms)).tree.ExecutionPath →
    OracleComp (oracleSpec Input PUnit All)
      (Option (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath)
  | [], g, cm, E, pc, _ => mappedStoppedComplete (compiledRoundsK Y Op []) g z cm E pc
  | ⟨_, .clear⟩ :: ms, (_, next), (m, rest), E, pc, p => do
      let suffix ← finishK z ms (next m PUnit.unit p.2.1) rest
        (fun k => E (Key.later m PUnit.unit k)) (fun k => pc (Key.later m PUnit.unit k)) p.2.2
      return suffix.map fun tail => ⟨m, p.2.1, tail⟩
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, (_, next), (root, rest), E, pc, p => do
      let suffix ← finishK z ms (next root PUnit.unit p.2.1) rest
        (fun k => E (Key.later root PUnit.unit k)) (fun k => pc (Key.later root PUnit.unit k)) p.2.2
      return suffix.map fun tail => ⟨root, p.2.1, tail⟩

/-- **Verification transport.** The paired public stopped verification, with its keys renamed to the
compiled domain by `untranslateK` (QD's `mappedStoppedComplete` with `embed := untranslateK`), is
the compiled verification up to the terminal opening round: the compiled run is the paired run
followed by `finishK`, whose last stage is the opening round's guard and query. This holds for every
choice of words `words` (the paired messages are `pairMsgs`). -/
theorem compiled_eq_paired_then_finish (z : Input) (words : (r : Round) → Nonempty r.Message → Input → List Y → Y → r.Message) :
    (ms : MRounds Y) → (pre : List Y) → (g : GuardSchedule Input PUnit (compiledRoundsK Y Op ms)) →
    (cm : PublicMessages (compiledRoundsK Y Op ms)) →
    (E : Key Input PUnit (compiledRoundsK Y Op ms) → Key Input PUnit All) →
    (pc : ∀ k, (E k).Challenge = k.Challenge) →
    mappedStoppedComplete (compiledRoundsK Y Op ms) g z cm E pc =
      (mappedStoppedComplete (pairedRoundsK Y ms) (pairGuards Y Op ms g) z
          (pairMsgs z words ms pre cm) (fun k => E (untranslateK Y Op ms k))
          (fun k => (pc (untranslateK Y Op ms k)).trans (untranslate_challengeK Y Op ms k)) >>=
        fun p? => match p? with
          | none => pure none
          | some p => finishK z ms g cm E pc p)
  | [], _, _, _, _, _ => by
      have hb : ∀ g' pm' E' pc', mappedStoppedComplete (pairedRoundsK Y ([] : MRounds Y)) g' z pm'
          (allRounds := All) E' pc' = pure (some PUnit.unit) := fun _ _ _ _ => rfl
      rw [hb]
      exact Eq.symm (pure_bind (m := OracleComp (oracleSpec Input PUnit All))
        (α := Option (protocol (pairedRoundsK Y ([] : MRounds Y))).tree.ExecutionPath)
        (some PUnit.unit) (fun p? => match p? with
          | none => pure none
          | some p => finishK z [] _ _ _ _ p))
  | ⟨_, .clear⟩ :: ms, pre, (guard, next), (m, rest), E, pc => by
      by_cases hg : guard z m PUnit.unit = true
      · unfold mappedStoppedComplete
        simp only [pairedRoundsK, pairGuards, pairMsgs, finishK, compiledRoundsK, hg]
        simp only [mappedStoppedComplete, hg, Bool.not_true, Bool.false_eq_true, ite_false,
          bind_assoc, pure_bind]
        congr 1
        funext response
        have ih' := compiled_eq_paired_then_finish z words ms pre
          (next m PUnit.unit (cast (pc (Key.here z m PUnit.unit)) response)) rest
          (fun key => E (Key.later m PUnit.unit key)) (fun key => pc _)
        rw [ih']
        simp only [bind_assoc]
        congr 1
        funext x
        cases x with
        | none => rfl
        | some p => rfl
      · have hg' : guard z m PUnit.unit = false := by simpa using hg
        unfold mappedStoppedComplete
        simp only [pairedRoundsK, pairGuards, pairMsgs, compiledRoundsK, hg']
        simp [mappedStoppedComplete, hg']
  | ⟨r, .merkle _ _ _ _ _⟩ :: ms, pre, (guard, next), (root, rest), E, pc => by
      by_cases hg : guard z root PUnit.unit = true
      · unfold mappedStoppedComplete
        simp only [pairedRoundsK, pairGuards, pairMsgs, finishK, compiledRoundsK, hg]
        simp only [mappedStoppedComplete, hg, Bool.not_true, Bool.false_eq_true, ite_false,
          bind_assoc, pure_bind]
        congr 1
        funext response
        have ih' := compiled_eq_paired_then_finish z words ms (pre ++ [show Y from root])
          (next root PUnit.unit (cast (pc (Key.here z root PUnit.unit)) response)) rest
          (fun key => E (Key.later root PUnit.unit key)) (fun key => pc _)
        rw [ih']
        simp only [bind_assoc]
        congr 1
        funext x
        cases x with
        | none => rfl
        | some p => rfl
      · have hg' : guard z root PUnit.unit = false := by simpa using hg
        unfold mappedStoppedComplete
        simp only [pairedRoundsK, pairGuards, pairMsgs, compiledRoundsK, hg']
        simp [mappedStoppedComplete, hg']

/-- QD's compiled `publicStoppedVerify` is QD's paired `publicStoppedVerifyWith` (keys embedded by
`untranslateK`) followed by `finishK` (the opening round included). -/
theorem publicStoppedVerify_compiled_eq (z : Input)
    (words : (r : Round) → Nonempty r.Message → Input → List Y → Y → r.Message) (ms : MRounds Y)
    (g : GuardSchedule Input PUnit (compiledRoundsK Y Op ms))
    (cm : PublicMessages (compiledRoundsK Y Op ms)) :
    publicStoppedVerify (compiledRoundsK Y Op ms) g z cm =
      (publicStoppedVerifyWith (allRounds := compiledRoundsK Y Op ms) (pairedRoundsK Y ms)
          (pairGuards Y Op ms g) z (pairMsgs z words ms [] cm) (untranslateK Y Op ms)
          (untranslate_challengeK Y Op ms) >>=
        fun p? => match p? with
          | none => pure none
          | some p => finishK z ms g cm id (fun _ => rfl) p) := by
  rw [publicStoppedVerify_eq_with, publicStoppedVerifyWith_eq_mapped,
    publicStoppedVerifyWith_eq_mapped]
  exact compiled_eq_paired_then_finish z words ms [] g cm id (fun _ => rfl)

/-- Coherence of a paired key with a memo `words`: each of its merkle messages carries the word
`words` assigns to its root prefix. -/
def Coherent {Input : Type} (words : (r : Round) → Nonempty r.Message → Input → List Y → Y → r.Message) :
    (ms : MRounds Y) → List Y → Key Input PUnit (pairedRoundsK Y ms) → Prop
  | [], _, _ => True
  | ⟨_, .clear⟩ :: _, _, .inl _ => True
  | ⟨_, .clear⟩ :: ms, pre, .inr (_, _, k) => Coherent words ms pre k
  | ⟨r, .merkle _ _ ne _ we⟩ :: _, pre, .inl (z, m, _) => m.1 = words r (merkle_nonempty ne we) z pre m.2
  | ⟨r, .merkle _ _ ne _ we⟩ :: ms, pre, .inr (m, _, k) =>
      m.1 = words r (merkle_nonempty ne we) k.input pre m.2 ∧ Coherent words ms (pre ++ [m.2]) k

theorem input_untranslateK {Input : Type} :
    (ms : MRounds Y) → (k : Key Input PUnit (pairedRoundsK Y ms)) →
    (untranslateK Y Op ms k).input = k.input
  | [], k => nomatch k
  | ⟨_, .clear⟩ :: _, .inl _ => rfl
  | ⟨_, .clear⟩ :: ms, .inr (_, _, k) => input_untranslateK ms k
  | ⟨_, .merkle _ _ _ _ _⟩ :: _, .inl _ => rfl
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, .inr (_, _, k) => input_untranslateK ms k

/-- Renaming a coherent paired key to the compiled domain and translating back is the identity:
the key B's FS oracle was asked is the key the paired verifier asks. -/
theorem translateK_untranslateK {Input : Type}
    (words : (r : Round) → Nonempty r.Message → Input → List Y → Y → r.Message) :
    (ms : MRounds Y) → (pre : List Y) → (k : Key Input PUnit (pairedRoundsK Y ms)) →
    Coherent words ms pre k →
    translateK Y Op ms words pre (untranslateK Y Op ms k) = some k
  | [], _, k, _ => nomatch k
  | ⟨_, .clear⟩ :: _, _, .inl (_, _, ⟨⟩), _ => rfl
  | ⟨_, .clear⟩ :: ms, pre, .inr (_, ⟨⟩, k), h => by
      simp only [untranslateK, translateK, translateK_untranslateK words ms pre k h]; rfl
  | ⟨r, .merkle _ _ ne _ we⟩ :: _, pre, .inl (z, m, ⟨⟩), h => by
      obtain ⟨w, root⟩ := m
      simp only [Coherent] at h
      simp only [untranslateK, translateK, h]
  | ⟨r, .merkle _ _ ne _ we⟩ :: ms, pre, .inr (m, ⟨⟩, k), h => by
      obtain ⟨w, root⟩ := m
      obtain ⟨h1, h2⟩ := h
      have hi := input_untranslateK (Op := Op) ms k
      have ih := translateK_untranslateK words ms (pre ++ [show Y from root]) k h2
      simp only [untranslateK, translateK, ih, Option.map_some]
      change some (Sum.inr ((words r (merkle_nonempty ne we) (untranslateK Y Op ms k).input pre root, root),
        PUnit.unit, k)) =
        some (Sum.inr ((w, root), PUnit.unit, k))
      rw [hi, ← h1]

end

end NockvmE2E.Merkle.VerifyTransport
