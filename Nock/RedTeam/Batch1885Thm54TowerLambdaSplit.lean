/-
  Nock/RedTeam/Batch1885Thm54TowerLambdaSplit.lean

  **The Form R lambda-exponent is split from the row count at the
  tower chip.**

  `vclGatesQ7T n e b delta`, `towerKeptGates n e b delta`, `vclRAPQ7T (n :=..) (e :=..)`: `n` is the row
  count (read by `finalBaseTransitionGates n`), `e` the lambda-exponent (read by `toQ`/`wIm`/`coreRe`
  via `lamPow`).

  * Control `goodCFT_iff_goodCF_checks`: `GoodCFT` is EXACTLY the five checks (Iff.rfl); and
    `goodCFT_of_checks`: the five checks alone give `GoodCFT`, for every `V` regardless of `V.N` vs
    `pwScaleExp K`.  UNCONFIRMED: no concrete `V` with `V.N != 63` is exhibited (the general implication is the control).
-/
import Nock.RedTeam.Batch1882Thm54VclStandaloneNoHrow
import Nock.RedTeam.Batch1744Thm54VclLIOFieldQuad
import Nock.RedTeam.Batch1881Thm54TowerRowFactsAt

set_option autoImplicit false

namespace Nock.RedTeam.Batch1885

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD Nock.NockVMROM.Thm54.T0Tower

noncomputable section
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [CharP K (ringChar K)] [DecidableEq F] {hC : ℕ} {S : MemShape}
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

theorem goodCFT_iff_goodCF_checks (V : VerifierData F K hC S) (ρ : Fin 3 → Quad (algebraMap F K δ)) :
    GoodCFT δ V ρ ↔ (V.AdjacentC ∧ Function.Injective V.computeNodes ∧
      (∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1) ∧ V.N ≤ ringChar K ∧ ρ 0 = 0) := Iff.rfl

theorem goodCFT_of_checks (V : VerifierData F K hC S) (ρ : Fin 3 → Quad (algebraMap F K δ))
    (h1 : V.AdjacentC) (h2 : Function.Injective V.computeNodes)
    (h3 : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1) (h4 : V.N ≤ ringChar K) (h5 : ρ 0 = 0) :
    GoodCFT δ V ρ := ⟨h1, h2, h3, h4, h5⟩

end

#print axioms goodCFT_iff_goodCF_checks
#print axioms goodCFT_of_checks
#print axioms compSoundnessVCLT
#print axioms rowFactsAt_compSoundnessVCLT
#print axioms Nock.RedTeam.Batch1882.vcl_standalone_soundness'
#print axioms Nock.RedTeam.Batch1882.vcl_standalone_155'
#print axioms Nock.RedTeam.Batch1882.vcl_standalone_154'
#print axioms Nock.RedTeam.Batch1882.vcl_standalone_164'

end Nock.RedTeam.Batch1885
