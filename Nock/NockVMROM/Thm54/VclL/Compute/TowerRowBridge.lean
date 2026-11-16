import Nock.NockVMROM.Thm54.VclL.Compute.TowerGenMap
import Nock.NockVMROM.Thm54.VclL.Compute.TowerRowLocal

/-!
# Bridge C1c's `RowMatchT` / `AgreeOffT` to C2a's `RowMatch` / `AgreeOff`

The two pairs are field-for-field copies; the bridge is the anonymous
constructor.  `honest_rowMatch_feeds_rowLocal`: at honest data every row-local kept gate holds at
`towerEnv309`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.ComputeTable Nock.Reified Module
open Nock.NockVMROM.Thm54.OptimizedComputeCodec Nock.NockVMROM.Thm54.OptimizedComputeOverlay
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7 Nock.NockVMROM.Thm54.VclL.Compute.LnRead

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

section Bridge
variable {L : Type} [Field L]

theorem RowMatchT.toRowMatch {env : Env L} {inp : Inputs L} {st : State} {pub : Pub L} {dec : Dec L}
    {ex : Extra L} (h : RowMatchT env inp st pub dec ex) : RowMatch env inp st pub dec ex :=
  ⟨h.table, h.chal, h.pubs, h.air, h.oneHot⟩

end Bridge

section Bridge2
variable {F L : Type} [Field F] [Field L]

theorem AgreeOffT.toAgreeOff {E₁ E₂ : CorrectedFinalTypedEnv F L} (h : AgreeOffT E₁ E₂) :
    AgreeOff E₁ E₂ :=
  ⟨h.baseTrace, h.baseTraceNext, h.extTraceNext, h.certBase, h.certExt, h.expCol, h.ext, h.chal⟩

end Bridge2

section Feed
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **MRG1 corollary.**  At honest data (`honest_rowMatch`'s hypotheses), every row-local kept core
gate holds in `𝕂′` at `towerEnv309`. -/
theorem honest_rowMatch_feeds_rowLocal (b : Basis (Fin 3) F K) (χ : Coins frameVCL K)
    (αs : Quad (algebraMap F K δ))
    (pub : Pub (Quad (algebraMap F K δ))) (dec : Dec (Quad (algebraMap F K δ))) (i n : ℕ)
    (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (tg : Fin 3 → Quad (algebraMap F K δ)) (eF : Env F)
    (hF : ∀ c, SrcRead c → eF.trace c = srcColT b
      (genRowVals pub dec (honestEx (towerInputs (δ := δ) χ αs) pub dec) i n wc wa wln winv r58 r59 vcl tg) c)
    (hch : eF.chal = chalVQ7T δ b χ)
    (hv : Vcomp (towerInputs (δ := δ) χ αs) pub dec) (wf : WF (towerInputs (δ := δ) χ αs) pub)
    (hz : zQuad δ χ ≠ 0)
    (h58 : Quad.im _ r58 = 0) (h61 : Quad.im _ wln = 0) (h62 : Quad.im _ winv = 0)
    (g : CorrectedCoreExtGateId) (hg : g ∈ keptCoreIdsQ7) (hlt : g.val < 72) :
    towerHolds δ (gatherEnv b eF) eF (coreTarget g) := by
  obtain ⟨hM, hA⟩ := honest_rowMatch b χ αs pub dec i n wc wa wln winv r58 r59 vcl tg eF hF hch hv wf hz
    h58 h61 h62
  exact towerHolds_rowLocal δ (gatherEnv b eF) eF _ hM.toRowMatch hA.toAgreeOff g hg hlt

end Feed

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
