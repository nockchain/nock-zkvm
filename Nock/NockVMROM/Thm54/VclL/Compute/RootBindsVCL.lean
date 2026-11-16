import Nock.NockVMROM.Thm54.VclL.Compute.WalkSatVCL
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.Batch458Thm54StrategyBindsStop

/-!
# V4T : `root_binds` at the VCL layout

.  The argument is the paper's walk-IOP root binding: the walk is seeded at the verifier's `seedOfClaim =
RLC^γ(claim label) · α` and closes at `out_walk = 0`, so outside the `α`-root event the first row's
`cur` is the claim label's RLC (`cur_one_eq_root_of_walkSat`); outside the `γ`-collision event the
label vectors are equal; the label vector carries `(s, f, e)`'s fingerprints
(`bindFP_of_labelVec_eq`).

* **`root_binds_of_walk`** — the generic step, PARAMETRIC in the coin map: any `WalkSat` seeded at
  `root · α` with `out = 0`, whose first `cur` is the RLC of a decoded `Pub`'s label vector, binds that
  `Pub` to the claim outside the two root events.  Nothing here reads a challenge slot: the
  coin-map (`chalV`) dependence lives only in how the `WalkSat` is built.
* **`vcl_root_cur_eq_claim`**, **`vcl_root_binds`** — the instance at `layoutVCLD` through
  `vcl_walkSat` / `vcl_walk_out` (the frame's `root_binds` shape: `bindFP` of the claim's subject,
  formula, result to the first row's decoded `s`, `f`, `e`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace WalkVCL

open Nock Nock.Walk Nock.Reified Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SVCompute
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.RedTeam.Batch458
open scoped Polynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The generic step (any coin map) -/

section generic
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- **`root_binds_of_walk`**: a walk seeded at `root · α` with `out = 0`, whose first `cur` is
`RLC^γ(labelVecOfPub pub)`, binds `pub`'s `(s, f, e)` to the claim at seed `z`, outside
`alphaBadOf (rootDiffP …)` and `gammaBadOf (claim label) (pub label)`. -/
theorem root_binds_of_walk {cur : ℕ → K} {chld : ℕ → ℕ → K} {fo : ℕ → ℕ} {ln count acc : ℕ → K}
    {α γ z : K} {h : ℕ} (claim : P8PublicClaim) (pub : Pub K)
    (hw : WalkSat cur chld fo ln count acc α (Walk.rlc γ (claimLabelVec z claim) * α) α h)
    (hout : acc h = 0)
    (hcur : cur 1 = Walk.rlc γ (labelVecOfPub pub))
    (hα : α ∉ alphaBadOf (rootDiffP cur chld fo (Walk.rlc γ (claimLabelVec z claim)) h))
    (hγ : γ ∉ gammaBadOf (claimLabelVec z claim) (labelVecOfPub pub)) :
    SemanticStrategy.bindFP z claim.subject pub.s ∧ SemanticStrategy.bindFP z claim.formula pub.f ∧
      SemanticStrategy.bindFP z claim.result pub.e := by
  have h1 := cur_one_eq_root_of_walkSat hw hout hα
  rw [hcur] at h1
  have hlab := eq_of_rlc_eq_of_not_mem hγ h1.symm
  exact bindFP_of_labelVec_eq _ _ _ hlab.symm

end generic

/-! ## 2. The instance at `layoutVCLD` -/

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {h : ℕ}
  (D : SVCompute.ChipData F K h) (γc ρc : ℕ)
  (c : OptimizedProductionChallengeTuple K F)
  (Q : Fin (chipOfP D (layoutVCLD (F := F) (K := K) (h := h) γc ρc) c).rap.w → F[X])
  (hadj : D.Adjacent)
  (RF : RowFactsP D (layoutVCLD (F := F) (K := K) (h := h) γc ρc) c Q)
  (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)

/-- The `α`-root event's polynomial at the VCL walk operands (the claim label's RLC as root). -/
noncomputable def rootPolyVCL : Polynomial K :=
  rootDiffP (curW D γc ρc c Q RF hchar) (chldW D γc ρc c Q RF hchar) (foW D γc ρc c Q RF hchar)
    (Walk.rlc (gamma c.1) (claimLabelVec (nprSeed c.1) D.claim)) D.N

include hadj in
/-- **`cur(1) = RLC^γ(claim label)` outside the `α`-root event**. -/
theorem vcl_root_cur_eq_claim (hα : alphaC c.1 ∉ alphaBadOf (rootPolyVCL D γc ρc c Q RF hchar)) :
    Walk.rlc (gamma c.1) (labelVecOfPub (pubAt D γc ρc c Q RF hchar (firstRowD D))) =
      Walk.rlc (gamma c.1) (claimLabelVec (nprSeed c.1) D.claim) := by
  have h := cur_one_eq_root_of_walkSat (vcl_walkSat D γc ρc c Q hadj RF hchar)
    (vcl_walk_out D γc ρc c Q RF hchar) hα
  rw [curW, rowOf_oneD] at h
  exact h

include hadj in
/-- **`root_binds` at the VCL layout**: outside the `α`-root and `γ`-root events, the first row's
decoded `(s, f, e)` are the claim's `(subject, formula, result)` at the NPR seed (`bindFP`), at
the row's one-hot state.  The frame's `CompSoundnessFamily.root_binds` shape. -/
theorem vcl_root_binds (hα : alphaC c.1 ∉ alphaBadOf (rootPolyVCL D γc ρc c Q RF hchar))
    (hγ : gamma c.1 ∉ gammaBadOf (claimLabelVec (nprSeed c.1) D.claim)
      (labelVecOfPub (pubAt D γc ρc c Q RF hchar (firstRowD D)))) :
    ∃ st0 : State, OneHotSelector (SB D γc ρc c Q (firstRowD D)) st0 ∧
      SemanticStrategy.bindFP (nprSeed c.1) D.claim.subject (decodePub (BV D γc ρc c Q (firstRowD D)) st0).s ∧
      SemanticStrategy.bindFP (nprSeed c.1) D.claim.formula (decodePub (BV D γc ρc c Q (firstRowD D)) st0).f ∧
      SemanticStrategy.bindFP (nprSeed c.1) D.claim.result (decodePub (BV D γc ρc c Q (firstRowD D)) st0).e := by
  refine ⟨stAt D γc ρc c Q RF hchar (firstRowD D), stAt_spec D γc ρc c Q RF hchar (firstRowD D), ?_⟩
  have hb := root_binds_of_walk (z := nprSeed c.1) D.claim (pubAt D γc ρc c Q RF hchar (firstRowD D))
    (vcl_walkSat D γc ρc c Q hadj RF hchar) (vcl_walk_out D γc ρc c Q RF hchar)
    (by rw [curW, rowOf_oneD]) hα hγ
  exact hb

end

end WalkVCL
end VclL.Compute
end Nock.NockVMROM.Thm54
