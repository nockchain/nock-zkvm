/-
  Nock/RedTeam/Batch1993Thm54WalkW4cFamily.lean

  **The honest fields of the walk memory family.**

  `memSoundnessVCLW δF hT hP kr` now carries `Honest := HonestVCLW δF hT hP hC kr`, `honestReq = req`,
  `honestMsg2 = yTot`, `honestQ = trace`, `honest_staged = trace_stagedW`, `honestBad = bad`,
  `honest_accepted = acceptedW`; every soundness field unchanged.
  `honestBad_epsilon`: the family's honest ε is `(1 + 5·nC + 3·nW)/|𝕂|²` (COMPILED).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.MemSoundnessVCLW

namespace Nock.RedTeam.Batch1993
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

theorem honestBad_epsilon {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [DecidableEq F] [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
    [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K] (hT hP kr : ℕ) {hC : ℕ} {C : TableSpec}
    (H : (memSoundnessVCLW (K := K) δF hT hP kr (hC := hC) (C := C)).Honest) :
    epsilonOf ((memSoundnessVCLW (K := K) δF hT hP kr (hC := hC) (C := C)).honestBad H) =
      (1 + 5 * (H.V.memRows (tCW hT hP) : ℚ) + 3 * (H.V.memRows (tWW hT hP) : ℚ)) / (Fintype.card K : ℚ) ^ 2 :=
  epsilon_badW H

end Nock.RedTeam.Batch1993

#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.memSoundnessVCLW
#print axioms Nock.RedTeam.Batch1993.honestBad_epsilon
