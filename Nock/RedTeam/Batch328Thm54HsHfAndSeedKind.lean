/-
  Nock/RedTeam/Batch328Thm54HsHfAndSeedKind.lean

  **§2 measurement and §3 strengthening receipt.**

  * `hs` / `hf` stay: `Batch325` is the compiled counterexample.
    `RunBoundedBy` is not widened.
  * Replacing `hseedcard` by `Λ < p` (and `11 < p` by `29 ≤ p`) is a
    **strengthening**: the joint budget can sit under `p³` with `Λ ≥ p`.
    Numerals `p = 769`, `rows = 8`, `Λ = 1000`.
-/
import Nock.NockVMROM.Thm54.SizeWindowCounting
import Nock.NockVMROM.Thm54.TraceGen.GenGoodSeedExists
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.TraceGen.GenSeedVcomp
import Nock.RedTeam.Batch325Thm54RunBoundedNotTyping

set_option autoImplicit false

namespace Nock.RedTeam.Batch328

open Nock Nock.Walk
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.GoodSeed
open Nock.RedTeam.Batch325

/-- §2 negative: `RunBoundedBy` does not give subject typing -/
theorem b328_run_not_imp_hs :
    ∃ q fuel s f r,
      evalGRom q fuel s f = some r ∧ ¬ FieldEmbedding.BoundedBy q s :=
  b325_run_not_imp_hs

/-- §2 negative: `RunBoundedBy` does not give formula typing -/
theorem b328_run_not_imp_hf :
    ∃ q fuel s f r,
      evalGRom q fuel s f = some r ∧ ¬ FieldEmbedding.BoundedBy q f :=
  b325_run_not_imp_hf

/-- Joint budget at `Λ = 1000`, `rows = 8` sits under `769³`,
    but `1000 ≮ 769`.  So `hseedcard` does not give `Λ < p`. -/
theorem b328_budget_at_lambda_1000 :
    seedBudgetVcomp 1000 8 < 769 ^ 3 := by
  have hsq : sizeWindowRootBound 1000 ≤ 1000 * 1000 :=
    sizeWindowRootBound_le_square 1000
  unfold seedBudgetVcomp seedBudget
  omega

theorem b328_lambda_not_lt_p : ¬ (1000 < 769) := by
  decide

/-- Compiled obstruction: the `p73` replacement strengthens -/
theorem b328_hseedcard_not_imp_lambda_lt_p :
    seedBudgetVcomp 1000 8 < 769 ^ 3 ∧ ¬ (1000 < 769) :=
  ⟨b328_budget_at_lambda_1000, b328_lambda_not_lt_p⟩

/-- `11 < 13` does not give the cubic floor `29 ≤ p`. -/
theorem b328_eleven_not_imp_twenty_nine : 11 < 13 ∧ ¬ (29 ≤ 13) := by
  decide

/-- `hKszChar` is §1's `rows < p`: every compute row emits a request. -/
theorem b328_compilerKszOf_ge_compRows {K : Type}
    [Field K] [Fintype K] [DecidableEq K]
    (α : K) (t : NTree (GenComputeRow K)) :
    (bfsRows (airReorder t)).length ≤ compilerKszOf (0 : K) α t :=
  compilerKszOf_ge_compRows α t

end Nock.RedTeam.Batch328

#print axioms Nock.RedTeam.Batch328.b328_run_not_imp_hs
#print axioms Nock.RedTeam.Batch328.b328_run_not_imp_hf
#print axioms Nock.RedTeam.Batch328.b328_hseedcard_not_imp_lambda_lt_p
#print axioms Nock.RedTeam.Batch328.b328_eleven_not_imp_twenty_nine
