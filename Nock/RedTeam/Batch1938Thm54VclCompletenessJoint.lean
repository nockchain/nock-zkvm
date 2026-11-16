/-
  Nock/RedTeam/Batch1938Thm54VclCompletenessJoint.lean

  **`vcl_completeness'` -- no bundled hypothesis.**  `HonestVCLJ extends HonestVCLT` (TowerJointSizes.lean) adds the memory-shape definitional fields (`hC0`, `hP0`,
  `memNodes = ω^i`, size check `hsizeM`); `hadj`/`hinj` are derived.  `hrank` is derived from `hleaf`,
  `h62` (over every read of the demand) from `haxis`; `hrows` is `hmemRows`.  `hF`/`hq` are field parameters.
  `vcl_completeness_goldilocks` discharges `hF`, `hq` at Goldilocks.
-/
import Nock.RedTeam.Batch1937Thm54VclCompleteness
import Nock.NockVMROM.Thm54.VclL.Compute.TowerJointSizes
import Nock.Field

set_option autoImplicit false

namespace Nock.RedTeam.Batch1938

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.RedTeam.Batch1880 Nock.RedTeam.Batch1882

noncomputable section
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (hT hP hC : ℕ)

open Classical in
/-- **Completeness at the two VCL families, no bundled hypothesis.**  Parameters: `hF`, `hq` (field).
Public size conditions: `hleaf` (every noun of the run has `≤ 2^110` leaves), `hmemRows` (memory row counts
`+ 1 < char F`), `haxis` (every read axis `< 2^63`). -/
theorem vcl_completeness' (HC : HonestVCLJ (K := K) δF hT hP hC)
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hleaf : programLeafBound (airReorder HC.t) ≤ 2 ^ 110)
    (hmemRows : ∀ k, HC.V.memRows k + 1 < ringChar F)
    (haxis : programAxisBound (airReorder HC.t) < 2 ^ 63) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        ∃ s ∈ (CFv (K := K) δF hT hP hC).honestBad HC.toHonestVCLT ++
            (MFv (K := K) δF hT hP hC).honestBad
              (jointMem δF HC.toHonestVCLT (jointMemFacts_of HC hF hq hleaf hmemRows haxis)),
          s.mem ((CFv (K := K) δF hT hP hC).honestQ HC.toHonestVCLT χ,
            (MFv (K := K) δF hT hP hC).honestQ
              (jointMem δF HC.toHonestVCLT (jointMemFacts_of HC hF hq hleaf hmemRows haxis)) χ) χ).card : ℚ) /
        Fintype.card (Coins frameVCL K) ≤
      epsilonOf ((CFv (K := K) δF hT hP hC).honestBad HC.toHonestVCLT ++
        (MFv (K := K) δF hT hP hC).honestBad
          (jointMem δF HC.toHonestVCLT (jointMemFacts_of HC hF hq hleaf hmemRows haxis))) :=
  Batch1937.vcl_completeness δF hT hP hC HC.toHonestVCLT (jointMemFacts_of HC hF hq hleaf hmemRows haxis)

end

section Goldilocks
variable {K : Type} [Field K] [Algebra Nock.Field.Fp K] [FiniteDimensional Nock.Field.Fp K] [Fintype K]
  [DecidableEq K] (δF : Nock.Field.Fp) [Fact (¬ IsSquare (algebraMap Nock.Field.Fp K δF))] (hT hP hC : ℕ)

theorem goldilocks_hq : 2 ^ 63 < ringChar Nock.Field.Fp := by
  have : ringChar Nock.Field.Fp = Nock.Field.p := ZMod.ringChar_zmod_n _
  rw [this, Nock.Field.p_eq]; norm_num

open Classical in
/-- **`vcl_completeness` at Goldilocks**: `hF` (`primeFieldElems_zmod`) and `hq` discharged; remaining
hypotheses are `HC` and the three public size conditions. -/
theorem vcl_completeness_goldilocks (HC : HonestVCLJ (K := K) δF hT hP hC)
    (hleaf : programLeafBound (airReorder HC.t) ≤ 2 ^ 110)
    (hmemRows : ∀ k, HC.V.memRows k + 1 < ringChar Nock.Field.Fp)
    (haxis : programAxisBound (airReorder HC.t) < 2 ^ 63) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        ∃ s ∈ (CFv (K := K) δF hT hP hC).honestBad HC.toHonestVCLT ++
            (MFv (K := K) δF hT hP hC).honestBad
              (jointMem δF HC.toHonestVCLT
                (jointMemFacts_of HC (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq
                  hleaf hmemRows haxis)),
          s.mem ((CFv (K := K) δF hT hP hC).honestQ HC.toHonestVCLT χ,
            (MFv (K := K) δF hT hP hC).honestQ
              (jointMem δF HC.toHonestVCLT
                (jointMemFacts_of HC (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq
                  hleaf hmemRows haxis)) χ) χ).card : ℚ) /
        Fintype.card (Coins frameVCL K) ≤
      epsilonOf ((CFv (K := K) δF hT hP hC).honestBad HC.toHonestVCLT ++
        (MFv (K := K) δF hT hP hC).honestBad
          (jointMem δF HC.toHonestVCLT
            (jointMemFacts_of HC (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq
              hleaf hmemRows haxis))) :=
  vcl_completeness' δF hT hP hC HC (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq
    hleaf hmemRows haxis

end Goldilocks

#print axioms VclL.Compute.gen_reqFacts
#print axioms VclL.Compute.TowerD.demT_rank_lt
#print axioms VclL.Compute.TowerD.demT_depth_le
#print axioms VclL.Compute.TowerD.HonestVCLJ.hinj
#print axioms VclL.Compute.TowerD.jointMemFacts_of
#print axioms vcl_completeness'
#print axioms vcl_completeness_goldilocks

end Nock.RedTeam.Batch1938
