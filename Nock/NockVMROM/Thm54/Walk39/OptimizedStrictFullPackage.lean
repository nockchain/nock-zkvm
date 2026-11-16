import Nock.NockVMROM.Thm54.Walk39.OptimizedStrictFullPackageDefs

/-!
The statement structure `OptimizedFullStrictThm54Statement` for the walk-instance package.  Its
primary field is the generic standalone statement `StandaloneThm54Statement` at the walk instance:
compute family `compSoundnessVCLT` (chip `computeChipVCLQ7T`, width 410, with `z1`), memory family
`memSoundnessVCLW`, the eleven-coin `frameVCL`, IO `ioSpecVCLQuad`, seed `seedSpecVCL`, fingerprints
in `𝕂′ = Quad δ`, and joint summands `jointSummandsStd`.  For every verifier datum `V` with
`V.Checks` and every staged prover (`msg.Staged`), the fraction of the eleven coins at which the
traces are accepted (`AcceptsV`) while the claim's Nock semantics fails is at most
`epsilonOf (allSummands …)`.  The field `bound` states `epsilonOf … ≤ boundVCLW''` (`boundVCL''` with
path rows replaced by walk rows `W`, plus the walk event `15W/|𝕂|`; equality is not claimed).  The
three figure fields are the kernel figures `< 2⁻¹⁵⁵` (N, cell rows, walk rows `≤ 2³¹`), `< 2⁻¹⁵⁴`
(`≤ 2³²`) and `< 2⁻¹⁶⁴` (N `≤ 2²¹`, cell rows `≤ 2²⁰`, walk rows `≤ 2²¹`) at `Fintype.card K = cK`,
and `leafBoundF … ≤ 2^110` (walk rows = `pathRows V`, i.e. table `1` of `shapeVW`).  The field
`completeness` is `vcl_completenessW5'` at the package's honest run: the probability over the coin
that some honest bad summand fires is at most its `ε` (statistical, not perfect, completeness).
-/

open Nock Nock.NockVMROM Nock.NockVMROM.Thm54
namespace Nock.Walk39

namespace Nock.NockVMROM.Thm54
namespace OptimizedStrictFullPackage

open Nock Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Events
open OptimizedFullStrictNockVMROMPackage

attribute [local instance] ringCharFactW algZModW

open Classical in
structure OptimizedFullStrictThm54Statement
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) : Prop where
  /-- **Primary:** `StandaloneThm54Statement` at `CF P`, `MF P`, `jointSummandsStd`. -/
  standalone : StandaloneThm54Statement P.CF P.MF (jointSummandsStd P.CF P.MF)
  /-- `ε ≤ boundVCLW''` for every verifier datum and both first messages (no equality claimed). -/
  bound : ∀ (V : VerifierData F K hOrb P.shape) (x : P.CF.Msg0) (y : P.MF.Msg0),
    epsilonOf (allSummands (CF := P.CF) (MF := P.MF) V x y (jointSummandsStd P.CF P.MF)) ≤
      boundVCLW'' (Fintype.card K) V.N (cellRows V) (pathRows V)
        (leafBoundF (ringChar P.FP) V.N V.claim) (2 ^ 110)
  /-- **Figure `< 2⁻¹⁵⁵`** at N, cell rows, walk rows (`pathRows V`) `≤ 2³¹`. -/
  figure_155 : ∀ (V : VerifierData F K hOrb P.shape),
    V.Checks (consumerBound P.CF P.MF V) (ringChar P.FP) →
    ∀ msg : Messages P.CF P.MF, msg.Staged →
    Fintype.card K = cK → V.N ≤ 2 ^ 31 → cellRows V ≤ 2 ^ 31 → pathRows V ≤ 2 ^ 31 →
    leafBoundF (ringChar P.FP) V.N V.claim ≤ 2 ^ 110 →
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) < 1 / (2 : ℚ) ^ 155
  /-- **Figure `< 2⁻¹⁵⁴`** at N, cell rows, walk rows `≤ 2³²`. -/
  figure_154 : ∀ (V : VerifierData F K hOrb P.shape),
    V.Checks (consumerBound P.CF P.MF V) (ringChar P.FP) →
    ∀ msg : Messages P.CF P.MF, msg.Staged →
    Fintype.card K = cK → V.N ≤ 2 ^ 32 → cellRows V ≤ 2 ^ 32 → pathRows V ≤ 2 ^ 32 →
    leafBoundF (ringChar P.FP) V.N V.claim ≤ 2 ^ 110 →
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) < 1 / (2 : ℚ) ^ 154
  /-- **Figure `< 2⁻¹⁶⁴`** at N `≤ 2²¹`, cell rows `≤ 2²⁰`, walk rows `≤ 2²¹`. -/
  figure_164 : ∀ (V : VerifierData F K hOrb P.shape),
    V.Checks (consumerBound P.CF P.MF V) (ringChar P.FP) →
    ∀ msg : Messages P.CF P.MF, msg.Staged →
    Fintype.card K = cK → V.N ≤ 2 ^ 21 → cellRows V ≤ 2 ^ 20 → pathRows V ≤ 2 ^ 21 →
    leafBoundF (ringChar P.FP) V.N V.claim ≤ 2 ^ 110 →
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) < 1 / (2 : ℚ) ^ 164
  /-- **Completeness (statistical)** at the package's honest run (`vcl_completenessW5'`). -/
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
  standalone := VclL.StandaloneW.vcl_standaloneW P.δ P.hT P.hP hOrb P.kr
  bound := fun V x y => VclL.StandaloneW.vcl_epsilonW_le P.δ P.hT P.hP hOrb P.kr V x y
  figure_155 := fun V hV msg hst hcK hN hD hP' hΛ =>
    VclL.StandaloneW.vcl_standaloneW_155' P.δ P.hT P.hP hOrb P.kr V hV msg hst hcK hN hD hP' hΛ
  figure_154 := fun V hV msg hst hcK hN hD hP' hΛ =>
    VclL.StandaloneW.vcl_standaloneW_154' P.δ P.hT P.hP hOrb P.kr V hV msg hst hcK hN hD hP' hΛ
  figure_164 := fun V hV msg hst hcK hN hD hP' hΛ =>
    VclL.StandaloneW.vcl_standaloneW_164' P.δ P.hT P.hP hOrb P.kr V hV msg hst hcK hN hD hP' hΛ
  completeness := vcl_completenessW5' P.δ P.hT P.hP hOrb P.honest
    P.primeField P.char_gt P.hleaf P.hmemRows P.haxis P.hkp

end OptimizedStrictFullPackage
end Nock.NockVMROM.Thm54

end Nock.Walk39
