/-
  Nock/RedTeam/Batch433Thm54ComputeWalkLabel.lean

  **The `LT_comp` label layer, receipts (Option A; twentieth move).**

  * `childPayloadWidth = 10` = `sf_state` + `sfTriple`; absent
    child slots use `nullStateTag = 10` (`:1748`/`:1752` compute `⊥`).
  * `labelRLC` / `childSumCC` / `selectorCM` are in-gate expressions over a row reader and the
    walk `(α, γ)`; the deployed transition subst `finalWalkSubstInGate` reads them on the successor
    row (`nextReader`), the boundary subst `finalWalkInitialSubst` on the first row through the
    public initial masks (`firstReader`).
  * Walk-γ is compute `𝕂` slot `10` (`DeployedChipFamily.computeKOfTuple c 10 = gamma c.1`);
    JointCoins `gamma` is already a coordinate of the tuple — the challenge space is unchanged.
  * The three child tags are hosted in overlay coordinates `2..4` (`childTagHost`), the coordinates
    the in-gate `cur`/`cc`/`cm` freed.
-/
import Nock.NockVMROM.Thm54.ComputeWalkLabel
import Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
import Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
import Nock.NockVMROM.Thm54.DeployedChipFamily

namespace Nock.RedTeam.Batch433

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open OptimizedComputeSubstitution

theorem label_width_ten : computeLabelWidth = 10 := computeLabelWidth_eq

theorem child_payload_ten : childPayloadWidth = 10 := childPayloadWidth_eq

/-- Option A: child payload matches own `LT_comp` width. -/
theorem child_matches_label_width :
    childPayloadWidth = computeLabelWidth :=
  child_payload_matches_label_width

/-- The deployed encoder width is the paper's label width (`93 → 10`). -/
theorem deployed_width_is_label_width :
    NodeEncoding.computeNodeWidth = 10 :=
  NodeEncoding.computeNode_width

theorem null_tag_ten : ComputeTable.nullStateTag = 10 := null_state_tag_eq

theorem walk_gamma_slot : walkGammaChallengeIndex = 10 := rfl

theorem walk_gamma_expr :
    walkGammaChallenge = .Var .challenge 10 := rfl

theorem walk_alpha_expr :
    walkAlphaChallenge = .Var .challenge 6 := rfl

/-- The deployed chip reads the walk `γ` (JointCoins `gamma`) at slot `10`. -/
theorem deployed_slot10_is_gamma {F K : Type} [Field F] [Field K] [Fintype K] [Fintype F]
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F) :
    DeployedChipFamily.computeKOfTuple c 10 = gamma c.1 := rfl

/-- Fanout never exceeds the three child slots. -/
theorem fanout_le_three (st : ComputeTable.State) : ComputeTable.fanoutComp st ≤ 3 :=
  fanoutComp_le_three st

/-- Positive control: walk-γ index is disjoint from walk-α and sampled IO. -/
theorem walk_gamma_disjoint_namespace :
    walkGammaChallengeIndex ≠ walkChallengeBase ∧
      walkGammaChallengeIndex ≠ sampledChallengeBase ∧
      walkGammaChallengeIndex ≠ sampledChallengeBase + 1 := by
  decide

/-- The deployed transition subst reads `cur`/`cc`/`cm` in-gate on the successor row. -/
theorem inGate_subst_uses_label_rlc :
    finalWalkSubstInGate .traceNext 3 = labelRLC nextReader ∧
      finalWalkSubstInGate .traceNext 4 = childSumCC nextReader ∧
      finalWalkSubstInGate .traceNext 5 = selectorCM nextReader :=
  finalWalkSubstInGate_next

/-- The deployed packing's cross-row singletons are the walk recurrences through the in-gate
subst (`Batch432`'s hosted `finalWalkSubst` is gone). -/
theorem packing_uses_inGate_subst :
    OptimizedComputeGateBasis.crossRowSingletons =
      [Reified.Trans.lnChainExpr.subst computeSubst,
       Reified.Trans.walkLnStep.subst finalWalkSubstInGate,
       Reified.Trans.walkCountStep.subst finalWalkSubstInGate,
       Reified.Trans.walkAccStep.subst finalWalkSubstInGate] :=
  rfl

/-- The boundary subst reads `cur`/`cc`/`cm` in-gate on the first row through the public masks. -/
theorem boundary_subst_uses_first_reader :
    OptimizedComputeFinalTypedLowering.finalWalkInitialSubst .traceCur 3 = labelRLC firstReader ∧
      OptimizedComputeFinalTypedLowering.finalWalkInitialSubst .traceCur 4 =
        childSumCC firstReader ∧
      OptimizedComputeFinalTypedLowering.finalWalkInitialSubst .traceCur 5 =
        selectorCM firstReader :=
  ⟨rfl, rfl, rfl⟩

/-- The first-row selectors are the public initial masks (`OptimizedComputeTemplate.initialMask`). -/
theorem first_reader_is_public_mask (st : ComputeTable.State) :
    firstReader.sel st = OptimizedComputeTemplate.initialMask st := rfl

/-- Child state tags are hosted in overlay coords `2..4`: `pubFP (overlayANat st) 2`,
`pubFP (overlayBNat st) 0/1`. -/
theorem child_state_hosted_in_overlay (st : ComputeTable.State) :
    childTagHost curReader st 0 = pubFP .traceCur (overlayANat st) 2 ∧
      childTagHost curReader st 1 = pubFP .traceCur (overlayBNat st) 0 ∧
      childTagHost curReader st 2 = pubFP .traceCur (overlayBNat st) 1 :=
  ⟨rfl, rfl, rfl⟩

/-- The in-gate `cc` keeps the paper's one-hot fanout selector: the inner
sum of state `st` has exactly `fanoutComp st` terms. -/
theorem cc_inner_sum_is_fanout_gated (r : RowReader) (st : ComputeTable.State) :
    childSumAt r st = childInnerSum r st (ComputeTable.fanoutComp st) := rfl

end Nock.RedTeam.Batch433

#print axioms Nock.RedTeam.Batch433.deployed_width_is_label_width
#print axioms Nock.RedTeam.Batch433.inGate_subst_uses_label_rlc
#print axioms Nock.RedTeam.Batch433.packing_uses_inGate_subst
#print axioms Nock.RedTeam.Batch433.boundary_subst_uses_first_reader
