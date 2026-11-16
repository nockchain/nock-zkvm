/-
  NockPure/PurePaperNames.lean — paper-label aliases for the PURE (VM-independent) fragment.

  A deliberately small counterpart to the VM-heavy `Nock.PaperNames` (which pulls in the whole
  §5 stack): every alias here points at a declaration inside the `NockPure` closure, so a paper
  object of the Nock *language* is findable by its the paper label without importing the zkVM.

  Extension rows (Tier B / OP₁₁) are OURS, not the paper's — the paper stops at OP₁₀ — and are
  flagged as such.  Pure aliases, no new content.
-/
import Batteries.Tactic.Alias
import Nock.PureAgreement

namespace NockPure

/-! ## §2 the Nock language -/

-- the paper proper binary trees / nouns
alias «Def:noun» := Nock.Noun
-- the paper terminal (fully-executed) state
alias «Def:terminal_state» := Nock.Verb.isTerminal
-- the executable big-step reference (`*[subject formula]`), the test oracle
alias «Def:reference_eval» := Nock.evalN
-- the paper the opcode/operator local rewrite
alias «Alg:Opcode_Updates_verb» := Nock.Verb.redex
alias «Alg:reduce» := Nock.Verb.reduce
-- the paper the Nock transition function `*`
alias «Alg:Nock_transition» := Nock.Verb.next
-- the paper the program verb `F = *[subject, formula]` and its run
alias «Def:program_verb» := Nock.Verb.program
alias «Def:run» := Nock.Verb.runProgram

/-! ## Adequacy (agreement of the small-step machine with the big-step reference) -/

-- Tier A soundness (paper-faithful): `runProgram` ⇒ `evalN`
alias «Thm:runProgram_sound» := Nock.Verb.runProgram_sound

/-! ## §OP₁₁ — the hint extension -/

-- the paper-faithful oracle restricted to OP₀..OP₁₀ (crashes on OP₁₁), and its refinement
alias «Ext:evalPaper» := Nock.evalPaper
alias «Ext:evalPaper_le_evalN» := Nock.evalPaper_le_evalN
-- the OP₁₁-extended machine and its soundness against full standard Nock
alias «Ext:runHint» := Nock.Verb.runHintProgram
alias «Ext:runHint_sound» := Nock.Verb.runHintProgram_sound
-- the exact Tier A / Tier B boundary
alias «Ext:paper_hint_separation» := Nock.Verb.paper_hint_separation

end NockPure
