import Nock.NockVMROM.Thm54.VCL38.OptimizedStrictFullPackageDefs

/-!
The statement `OptimizedFullStrictThm54Statement` and the theorem `optimizedFullStrictNockVMROM_of_package` for the VCL-L optimized strict full package. The primary field is the generic standalone statement `StandaloneThm54Statement` at the VCL-L instance: compute
family `compSoundnessVCLT` (chip `computeChipVCLQ7T`, width 410, with `z1`), memory family
`memSoundnessVCL` (the cell table and the path chip), the eleven-coin `frameVCL`, IO
`ioSpecVCLQuad`, seed `seedSpecVCL`, fingerprints in `𝕂′ = Quad δ`, joint summands
`jointSummandsStd`.  For every verifier datum `V` with `V.Checks` and every staged prover
(`msg.Staged`), the fraction of the eleven coins at which the traces are accepted (`AcceptsV`) while
the claim's Nock semantics fails is at most `epsilonOf (allSummands …)`; `bound` states
`epsilonOf … ≤ boundVCL''` (equality is NOT claimed); the three figure fields are the kernel figures
`< 2⁻¹⁵⁵` (N, cell rows, path rows `≤ 2³¹`), `< 2⁻¹⁵⁴` (`≤ 2³²`), `< 2⁻¹⁶⁴` (N `≤ 2²¹`, cell rows
`≤ 2²⁰`, path rows `≤ 2²¹`) at `Fintype.card K = cK` and `leafBoundF … ≤ 2^110`; `completeness` is
`vcl_completeness'` at the package's honest run: the probability over the coin that some honest bad
summand fires is at most its `ε` (statistical, not perfect, completeness).
-/
open Nock Nock.NockVMROM Nock.NockVMROM.Thm54
namespace Nock.VCL38


namespace Nock.NockVMROM.Thm54
namespace OptimizedStrictFullPackage

open Nock Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Events
open OptimizedFullStrictNockVMROMPackage

open Classical in
structure OptimizedFullStrictThm54Statement
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) : Prop where
  /-- **Primary:** `StandaloneThm54Statement` at `CF P`, `MF P`, `jointSummandsStd`. -/
  standalone : StandaloneThm54Statement P.CF P.MF (jointSummandsStd P.CF P.MF)
  /-- `ε ≤ boundVCL''` for every verifier datum and both first messages (no equality claimed). -/
  bound : ∀ (V : VerifierData F K hOrb P.shape) (x : P.CF.Msg0) (y : P.MF.Msg0),
    epsilonOf (allSummands (CF := P.CF) (MF := P.MF) V x y (jointSummandsStd P.CF P.MF)) ≤
      boundVCL'' (Fintype.card K) V.N (cellRows V) (pathRows V)
        (leafBoundF (ringChar P.FP) V.N V.claim) (2 ^ 110)
  /-- **Figure `< 2⁻¹⁵⁵`** at N, cell rows, path rows `≤ 2³¹`. -/
  figure_155 : ∀ (V : VerifierData F K hOrb P.shape),
    V.Checks (consumerBound P.CF P.MF V) (ringChar P.FP) →
    ∀ msg : Messages P.CF P.MF, msg.Staged →
    Fintype.card K = cK → V.N ≤ 2 ^ 31 → cellRows V ≤ 2 ^ 31 → pathRows V ≤ 2 ^ 31 →
    leafBoundF (ringChar P.FP) V.N V.claim ≤ 2 ^ 110 →
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) < 1 / (2 : ℚ) ^ 155
  /-- **Figure `< 2⁻¹⁵⁴`** at N, cell rows, path rows `≤ 2³²`. -/
  figure_154 : ∀ (V : VerifierData F K hOrb P.shape),
    V.Checks (consumerBound P.CF P.MF V) (ringChar P.FP) →
    ∀ msg : Messages P.CF P.MF, msg.Staged →
    Fintype.card K = cK → V.N ≤ 2 ^ 32 → cellRows V ≤ 2 ^ 32 → pathRows V ≤ 2 ^ 32 →
    leafBoundF (ringChar P.FP) V.N V.claim ≤ 2 ^ 110 →
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) < 1 / (2 : ℚ) ^ 154
  /-- **Figure `< 2⁻¹⁶⁴`** at N `≤ 2²¹`, cell rows `≤ 2²⁰`, path rows `≤ 2²¹`. -/
  figure_164 : ∀ (V : VerifierData F K hOrb P.shape),
    V.Checks (consumerBound P.CF P.MF V) (ringChar P.FP) →
    ∀ msg : Messages P.CF P.MF, msg.Staged →
    Fintype.card K = cK → V.N ≤ 2 ^ 21 → cellRows V ≤ 2 ^ 20 → pathRows V ≤ 2 ^ 21 →
    leafBoundF (ringChar P.FP) V.N V.claim ≤ 2 ^ 110 →
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) < 1 / (2 : ℚ) ^ 164
  /-- **Completeness (statistical)** at the package's honest run (`vcl_completeness'`). -/
  completeness :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        ∃ s ∈ P.CF.honestBad P.honest.toHonestVCLT ++ P.MF.honestBad P.honestMem,
          s.mem (P.CF.honestQ P.honest.toHonestVCLT χ, P.MF.honestQ P.honestMem χ) χ).card : ℚ) /
        Fintype.card (Coins frameVCL K) ≤
      epsilonOf (P.CF.honestBad P.honest.toHonestVCLT ++ P.MF.honestBad P.honestMem)

def optimizedFullStrictNockVMROM_of_package
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    OptimizedFullStrictThm54Statement P where
  standalone := standalone_generic (Nock.RedTeam.Batch1882.rowFactsAt_CFv P.δ P.hT P.hP hOrb)
    (Nock.RedTeam.Batch1880.extraPremises_vcl P.δ P.hT P.hP hOrb)
  bound := fun V x y => Nock.RedTeam.Batch1880.vcl_epsilon_le P.δ P.hT P.hP hOrb V x y
  figure_155 := fun V hV msg hst hcK hN hD hP' hΛ =>
    Nock.RedTeam.Batch1882.vcl_standalone_155' P.δ P.hT P.hP hOrb V hV msg hst hcK hN hD hP' hΛ
  figure_154 := fun V hV msg hst hcK hN hD hP' hΛ =>
    Nock.RedTeam.Batch1882.vcl_standalone_154' P.δ P.hT P.hP hOrb V hV msg hst hcK hN hD hP' hΛ
  figure_164 := fun V hV msg hst hcK hN hD hP' hΛ =>
    Nock.RedTeam.Batch1882.vcl_standalone_164' P.δ P.hT P.hP hOrb V hV msg hst hcK hN hD hP' hΛ
  completeness := Nock.RedTeam.Batch1938.vcl_completeness' P.δ P.hT P.hP hOrb P.honest
    P.primeField P.char_gt P.hleaf P.hmemRows P.haxis

end OptimizedStrictFullPackage
end Nock.NockVMROM.Thm54

end Nock.VCL38
