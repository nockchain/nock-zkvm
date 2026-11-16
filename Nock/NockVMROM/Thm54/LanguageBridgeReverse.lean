import Nock.NockVMROM.Thm54.LanguageBridge

/-!
# Image-restricted reverse language bridge (Track D, downgraded)

The bare converse of the forward language bridge is **false** and is compiled as such in
`LanguageBridge` (`not_reverse_language_projection`, `accepts_does_not_pin_io`): plain acceptance
cannot manufacture a threaded semantic preimage. The closure plan downgraded the full reverse to
optional because the paper's Theorem 5.4 does not require a language *equivalence* — it requires
**perfect completeness** (the forward direction, already proved as `language_stmtOfExact_canonical`)
and negligible soundness error (a probabilistic bound, not a deterministic converse).

This module records the honest, image-restricted reverse: any statement that *is* in the forward
image of the exact chained semantic language lies in the NockVMROM language at the canonical tag.
This is exactly as much reverse as is true, and it is enough for the paper's claim; the unrestricted
converse remains refuted next door.
-/

namespace Nock.NockVMROM.Thm54

open Nock.Framework

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **Image-restricted reverse.** If a statement `x` is the forward projection of some exact chained
semantic execution, then `x` is in the NockVMROM language at that configuration's canonical tag.
Follows immediately from the forward bridge; no bare converse is claimed. -/
theorem language_of_in_image (x : Stmt F K)
    (h : ∃ (cfg : ExactConfig F K) (exec : ExactExecution cfg),
      ChainedSemanticExactLanguage cfg exec ∧ stmtOfExact cfg exec = x) :
    ∃ cfg : ExactConfig F K,
      Language (Tag F K cfg.challenges.α cfg.challenges.β cfg.Ksz) x := by
  obtain ⟨cfg, exec, hchain, hx⟩ := h
  exact ⟨cfg, hx ▸ language_stmtOfExact_canonical hchain⟩

/-- **Perfect completeness is the forward direction the paper needs.** Every exact chained execution
projects into the NockVMROM language at the canonical tag. Re-exported here to make explicit that
the paper's completeness requirement is already discharged and does not need the reverse. -/
theorem perfect_completeness_is_forward
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    Language (Tag F K cfg.challenges.α cfg.challenges.β cfg.Ksz) (stmtOfExact cfg exec) :=
  language_stmtOfExact_canonical h

/-- **The unrestricted reverse remains false**, re-exported for contrast: there is no total
projection from the language back to exact chained carriers. -/
theorem unrestricted_reverse_still_false (α β : K) {Ksz : ℕ} (hK : 1 ≤ Ksz)
    (r : (nmrMEF F K).Rec) :
    ¬ ∀ x : Stmt F K, Language (Tag F K α β Ksz) x →
        ∃ (cfg : ExactConfig F K) (exec : ExactExecution cfg),
          ChainedSemanticExactLanguage cfg exec ∧ stmtOfExact cfg exec = x :=
  not_reverse_language_projection α β hK r

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.language_of_in_image
#print axioms Nock.NockVMROM.Thm54.perfect_completeness_is_forward
#print axioms Nock.NockVMROM.Thm54.unrestricted_reverse_still_false
