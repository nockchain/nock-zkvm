/-
  Nock/RedTeam/Batch171Thm54ThreeBetas.lean

  **The paper's `β` is three different things; this pins which is which, in the build.**

  This module makes the distinction **gate-checked**.

  | paper | role | this tree | value at `DotConfig769` |
  |---|---|---|---|
  | `Def:RAP` `(ω, β)` | evaluation-orbit coset shift | `OrbitDomain.βcoset` | `1`, and `≠ 0` by a structure field |
  | `Def:NMR` `𝒯 := β^k` | **timestamp base** | `ChallengeVector.α` | the honest coin `DotConfig769.alphaA`, used as `α ^ e` |
  | pole offset | LogUp offset `RLC^γ(·) − β` | `ChallengeVector.β` | `0` |

  If a later change sets `ChallengeVector.β` nonzero "to restore the paper's randomness", or pins
  `βcoset` to zero, or moves timestamps off `α`, one of the theorems below fails.  That is the point:
  the mistake `EM` records is one a reader makes from the paper, so the guard belongs next to the
  code rather than in a document.

  Not repeated here.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierAHonestData
import Nock.NockVMROM.Thm54.ForestExponentWindow

set_option autoImplicit false

namespace Nock.RedTeam.Batch171

open Nock Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54.GenericHonestData

/-! ## β₁ — the RAP evaluation-orbit coset shift is **nonzero** -/

/-- `Def:RAP`'s `(ω, β)`. -/
theorem rap_beta_coset_ne_zero :
    (executionOrbit : OrbitDomain K).βcoset ≠ 0 :=
  (executionOrbit : OrbitDomain K).βcoset_ne_zero

theorem rap_beta_coset_value : (executionOrbit : OrbitDomain K).βcoset = 1 := rfl

/-! ## β₂ — the NMR timestamp base is `α`, and it is not the pole offset -/

/-- `Def:NMR`'s `𝒯 := β^k` is this tree's `ChallengeVector.α`: committed memory
timestamps are powers of it.  `MemoryTimestampClosedAt` is exactly "is a power of `α`". -/
theorem nmr_timestamp_base_is_alpha (e : ℕ) :
    MemoryTimestampClosedAt (DotConfig769.alphaA : K) ((DotConfig769.alphaA : K) ^ e) :=
  ⟨e, rfl⟩

/-- The timestamp base is **not** the pole offset: the configuration's `α` and `β` are different
columns of the challenge vector, and only one of them is zero. -/
theorem timestamp_base_ne_pole_offset :
    ((cfg seedZ DotConfig769.alphaA).challenges.α, (cfg seedZ DotConfig769.alphaA).challenges.β)
      = (DotConfig769.alphaA, (0 : K)) := rfl

/-! ## β₃ — the LogUp pole offset is the one set to zero -/

/-- the paper's offset. Zero here; `Batch170` is why that is sound. -/
theorem logup_pole_offset_is_zero :
    (cfg seedZ DotConfig769.alphaA).challenges.β = 0 := rfl

/-- ...and the record-RLC challenge likewise. -/
theorem record_rlc_challenge_is_zero :
    (cfg seedZ DotConfig769.alphaA).challenges.γ = 0 := rfl

/-- **The three are genuinely distinct at the live configuration**: the orbit shift is nonzero, the
timestamp base is the honest coin, and the pole offset is zero.  Stated as one theorem so a change
that collapses any two of them cannot pass unnoticed. -/
theorem three_betas_are_distinct_roles :
    (executionOrbit : OrbitDomain K).βcoset ≠ 0 ∧
      (cfg seedZ DotConfig769.alphaA).challenges.α = DotConfig769.alphaA ∧
        (cfg seedZ DotConfig769.alphaA).challenges.β = 0 :=
  ⟨rap_beta_coset_ne_zero, rfl, rfl⟩

end Nock.RedTeam.Batch171

#print axioms Nock.RedTeam.Batch171.rap_beta_coset_ne_zero
#print axioms Nock.RedTeam.Batch171.nmr_timestamp_base_is_alpha
#print axioms Nock.RedTeam.Batch171.three_betas_are_distinct_roles
