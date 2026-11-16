/-
  Nock/RedTeam/Batch1935Thm54TowerHonestFamily.lean

  **`compSoundnessVCLT` with the honest fields.**

  * `honest_fields`: the family's honest fields are these (by `rfl`).
  * NC `honestReq_zero_load_bearing`: with a request vector whose validity terminal is nonzero, the tower CF chip
    at the honest datum accepts NO trace (so `reqT … 0 = 0` is load-bearing in `honest_accepted_T`).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerCompFamilyT
import Nock.RedTeam.Batch1885Thm54TowerLambdaSplit

set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1935
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Compute.TowerD Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower Nock.Framework

section
variable (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [CharP K (ringChar K)] [Fintype F] [DecidableEq F] (hC : ℕ) (S : MemShape)
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

theorem honest_fields :
    (compSoundnessVCLT F K hC S δ).Honest = HonestVCLT F K δ hC S ∧
    (∀ H : HonestVCLT F K δ hC S, (compSoundnessVCLT F K hC S δ).honestV H = H.V) ∧
    (∀ H : HonestVCLT F K δ hC S, (compSoundnessVCLT F K hC S δ).honestBad H = badT H.V H.t) ∧
    (∀ (H : HonestVCLT F K δ hC S) χ, (compSoundnessVCLT F K hC S δ).honestQ H χ = traceT H.V χ H.αs H.hgen) ∧
    (∀ (H : HonestVCLT F K δ hC S) χ, (compSoundnessVCLT F K hC S δ).honestReq H χ = reqT H.t χ) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **NC**: a request vector with a nonzero validity terminal makes the chip at the honest datum reject every
trace (the honest `reqT … 0 = 0` is load-bearing). -/
theorem honestReq_zero_load_bearing (H : HonestVCLT F K δ hC S) (χ : Coins frameVCL K)
    (ρ : Fin 3 → Quad (algebraMap F K δ)) (hρ : ρ 0 ≠ 0) (Q : Fin (tableVCLT hC).width → Polynomial F) :
    ¬ RAP.SatisfiesWithPreprocessing (chipCFT δ H.V (xT H.t) ρ χ)
      (fun j => Q (Fin.cast (chipCFT_width δ H.V (xT H.t) ρ χ) j)) :=
  chipCFT_rejects_bad δ H.V (xT H.t) ρ χ Q (fun hg => hρ hg.2.2.2.2)

end

#print axioms honest_fields
#print axioms honestReq_zero_load_bearing
#print axioms compSoundnessVCLT
#print axioms rowFactsAt_compSoundnessVCLT
#print axioms Nock.RedTeam.Batch1880.vcl_standalone_soundness
#print axioms Nock.RedTeam.Batch1880.vcl_standalone_155
#print axioms Nock.RedTeam.Batch1880.vcl_standalone_154
#print axioms Nock.RedTeam.Batch1880.vcl_standalone_164
#print axioms Nock.RedTeam.Batch1882.vcl_standalone_soundness'
#print axioms Nock.RedTeam.Batch1882.vcl_standalone_155'
#print axioms honest_staged_T
#print axioms honest_accepted_T

end Nock.RedTeam.Batch1935
