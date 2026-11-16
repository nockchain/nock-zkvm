/-
`RapInput (rapJ J wm) 4` (inputs).
Kept in its own file because `RapInput` lives in `Succ/Statement` (imported only here).
-/
import NockvmE2E.J8.Statement
import NockvmE2E.Succ.Statement

set_option autoImplicit false

namespace NockvmE2E.J8

open NockvmE2E.Rap

variable {B K : Type} [Field B] [Field K] [Algebra B K] [Fintype K] [DecidableEq K]
  {J : RapAirJ B K} {ι β : Type} {colRound : ι → ℕ}

/-- **`RapInput (rapJ J wm) 4`**: soundness (pointwise), `|K| ≥ 2`, one round per summand, blocks `< 4`. -/
theorem rapInput_rapJ (wm : WordMap J colRound β) (pread : Tr ι β → J.Msg) :
    NockvmE2E.Succ.RapInput (rapJ J wm pread) 4 :=
  ⟨soundG_rapJ wm pread, card_rapJ J, oneRound_rapJ wm pread, blk_lt_rapJ wm pread⟩

end NockvmE2E.J8
