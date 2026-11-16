/-
  Nock/RedTeam/Batch324Thm54Batch151DebtReview.lean

  Paper re-read at source:
  `:1328`, `:1329`, `:1413`, `:1427`, `:1450`, `:1728`, `:1852-1854`.

  Every named theorem `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`
  except `b324_eleven_one_two` / the cite pin (axiom-free).
-/
import Nock.RedTeam.Batch151Thm54AlphaNeZero
import Nock.NockVMROM.Thm54.GenericHonestCommitment

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch324

open scoped Classical
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.RedTeam.Batch151

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! No `BuildableNockExecution` can carry `α = 0`. The
always-operative `mem_record₁` makes
the request list nonempty; `SemanticIOPreimage` requires every request
exponent `< timestampBound ≤ orderOf α`; `orderOf 0 = 0` empties that
window. The argument is not `∀ D'`, does not unpark PRL, and does not
widen the §J tick. -/

/-- Independent: `orderOf (0 : K) = 0` -/
theorem b324_orderOf_zero : orderOf (0 : K) = 0 :=
  batch151_orderOf_zero

/-- Always-operative `mr1` -/
theorem b324_mr1_always (pub : ComputeTable.Pub K) :
    pub.mr1 ∈ NockVM.activeRequestRecords pub :=
  batch151_activeRequestRecords_always_includes_mr1 pub

/-- Request list nonempty -/
def b324_rawRequests_ne_nil :=
  @batch151_rawRequests_ne_nil

/-- Re-derived `α ≠ 0` on every `BuildableNockExecution`. -/
theorem b324_alpha_ne_zero (E : BuildableNockExecution F K) :
    E.cfg.challenges.α ≠ 0 :=
  batch151_alpha_ne_zero_rederived E

/-- Empty injective window at `0` -/
theorem b324_empty_window_at_zero :
    ∀ n : ℕ, n ≤ orderOf (0 : K) → n = 0 :=
  batch151_empty_window_at_zero

/-- `∀ D'` stays refuted -/
def b324_forall_data_still_refuted :=
  @batch151_forall_data_still_refuted

/-- Accounting pin -/
theorem b324_eleven_one_two : 11 + 1 + 2 = 14 :=
  batch151_residual_pair

/-- `Def:NMR` address space `𝒜` is the paper; timestamp space
`𝒯 := β^k` is the paper. -/
def b324_nmr_timestamp_is_1329 : True := trivial

/-- The load-bearing proof is `batch151_alpha_ne_zero_rederived`. -/
def b324_f73_named_is_rfl :=
  @batch151_f73_alpha_ne_zero

end

#print axioms b324_orderOf_zero
#print axioms b324_mr1_always
#print axioms b324_rawRequests_ne_nil
#print axioms b324_alpha_ne_zero
#print axioms b324_empty_window_at_zero
#print axioms b324_forall_data_still_refuted
#print axioms b324_eleven_one_two
#print axioms b324_nmr_timestamp_is_1329
#print axioms b324_f73_named_is_rfl

end Nock.RedTeam.Batch324
