import Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs

/-!
`OptimizedFullStrictThm54Statement P` has six fields: `standalone`, `bound`, three figure fields and
`completeness`.  `bound`:
`epsilonOf … ≤ boundVCLHQ''` (in fact `=`, `epsilonVSQH_eq`), at `claimFuel V.claim`.  `completeness`: `vsqCompleteness` at the
package's honest run, `Pr_χ[¬ HonestGoodVSQ] ≤ epsCVSQ`; `HonestGoodVSQ` is exactly the coin premise of honest
acceptance (`honest_accepted_VSQ_run`).

`optimizedFullStrictNockVMROM_of_package` proves `OptimizedFullStrictThm54Statement P` for every package `P`.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedStrictFullPackage

open Nock Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Events
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.PullVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS
open Nock.NockVMROM.Thm54.VclL.Handle.CoresVSQH
open OptimizedFullStrictNockVMROMPackage

attribute [local instance] ringCharFactW algZModW decQ40

open Classical in
structure OptimizedFullStrictThm54Statement
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) : Prop where
  /-- **Primary:** `StandaloneG` at the honest-carrying VSQ cores `CF P`, `MF P` and `jointVSQ`. -/
  standalone : StandaloneG P.CF P.MF P.joint
  /-- `ε ≤ boundVCLHQ''` for every verifier datum and both first messages. -/
  bound : ∀ (V : VerifierData F K hOrb P.shape) (x : P.CF.Msg0) (y : P.MF.Msg0),
    epsilonOf (allSummandsG (CC := P.CF) (MC := P.MF) V x y P.joint) ≤
      boundVCLHQ'' (Fintype.card K) (Fintype.card P.FP) V.N
        (V.memRows (tCQ P.hT P.hP)) (V.memRows (tWQ P.hT P.hP)) (claimFuel V.claim)
  /-- **Figure `< 2⁻¹⁵⁶`** at N, cell rows, walk rows `≤ 2³¹`. -/
  figure_156 : ∀ (V : VerifierData F K hOrb P.shape),
    V.Checks (fun a => P.CF.reqBound V a + P.MF.internalBound V a) (ringChar P.FP) →
    ∀ msg : MessagesG P.CF P.MF, TracesStaged frameVSQ (tableVSQ hOrb) P.shape msg.traces →
    Fintype.card K = cK → V.N ≤ 2 ^ 31 → V.memRows (tCQ P.hT P.hP) ≤ 2 ^ 31 →
    V.memRows (tWQ P.hT P.hP) ≤ 2 ^ 31 → leafBoundF (ringChar F) V.N V.claim ≤ 2 ^ 110 →
    ((Finset.univ.filter fun χ : Coins frameVSQ K =>
        AcceptsG V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVSQ K) < 1 / (2 : ℚ) ^ 156
  /-- **Figure `< 2⁻¹⁵⁵`** at N, cell rows, walk rows `≤ 2³²`. -/
  figure_155 : ∀ (V : VerifierData F K hOrb P.shape),
    V.Checks (fun a => P.CF.reqBound V a + P.MF.internalBound V a) (ringChar P.FP) →
    ∀ msg : MessagesG P.CF P.MF, TracesStaged frameVSQ (tableVSQ hOrb) P.shape msg.traces →
    Fintype.card K = cK → V.N ≤ 2 ^ 32 → V.memRows (tCQ P.hT P.hP) ≤ 2 ^ 32 →
    V.memRows (tWQ P.hT P.hP) ≤ 2 ^ 32 → leafBoundF (ringChar F) V.N V.claim ≤ 2 ^ 110 →
    ((Finset.univ.filter fun χ : Coins frameVSQ K =>
        AcceptsG V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVSQ K) < 1 / (2 : ℚ) ^ 155
  /-- **Figure `< 2⁻¹⁶⁶`** at N `≤ 2²¹`, cell rows `≤ 2²⁰`, walk rows `≤ 2²¹`. -/
  figure_166 : ∀ (V : VerifierData F K hOrb P.shape),
    V.Checks (fun a => P.CF.reqBound V a + P.MF.internalBound V a) (ringChar P.FP) →
    ∀ msg : MessagesG P.CF P.MF, TracesStaged frameVSQ (tableVSQ hOrb) P.shape msg.traces →
    Fintype.card K = cK → V.N ≤ 2 ^ 21 → V.memRows (tCQ P.hT P.hP) ≤ 2 ^ 20 →
    V.memRows (tWQ P.hT P.hP) ≤ 2 ^ 21 → leafBoundF (ringChar F) V.N V.claim ≤ 2 ^ 110 →
    ((Finset.univ.filter fun χ : Coins frameVSQ K =>
        AcceptsG V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVSQ K) < 1 / (2 : ℚ) ^ 166
  /-- **Completeness (statistical)** at the package's honest run (`vsqCompleteness`): the coins at which the
  honest-acceptance premise `HonestGoodVSQ` fails have mass `≤ epsCVSQ`. -/
  completeness :
    ((Finset.univ.filter fun χ : Coins frameVSQ K => ¬ HonestGoodVSQ P.honest P.t P.x χ).card : ℚ) /
        Fintype.card (Coins frameVSQ K) ≤ epsCVSQ P.honest P.t

def optimizedFullStrictNockVMROM_of_package
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    OptimizedFullStrictThm54Statement P where
  standalone := standaloneVSQH P.δ P.hT P.hP P.kr hOrb
  bound := fun V x y => (epsilonVSQH_eq P.δ P.hT P.hP P.kr hOrb V x y).le
  figure_156 := fun V hV msg hst hcK hN hD hW hΛ =>
    fig_of_bound P.δ P.hT P.hP P.kr hOrb V hV msg hst hcK hΛ (figVCLHQ''_156 _ _ _ hN hD hW)
  figure_155 := fun V hV msg hst hcK hN hD hW hΛ =>
    fig_of_bound P.δ P.hT P.hP P.kr hOrb V hV msg hst hcK hΛ (figVCLHQ''_155_at_32 _ _ _ hN hD hW)
  figure_166 := fun V hV msg hst hcK hN hD hW hΛ =>
    fig_of_bound P.δ P.hT P.hP P.kr hOrb V hV msg hst hcK hΛ (figVCLHQ''_166_kernel _ _ _ hN hD hW)
  completeness := by
    classical
    refine le_trans ?_ (standaloneVSQH_completeness_le P.δ P.hT P.hP P.kr hOrb P.hdat)
    convert prob_not_good_le P.δ P.hT P.hP P.kr hOrb P.hdat P.hN using 4

end OptimizedStrictFullPackage
end Nock.NockVMROM.Thm54

