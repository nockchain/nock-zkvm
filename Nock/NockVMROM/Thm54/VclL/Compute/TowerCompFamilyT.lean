import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestAccept

/-!
# `compSoundnessVCLT` with the honest fields

The family moved here from
`TowerCompChipQ7.lean` (§8 there) so that it can import the honest side; its soundness fields are verbatim.
`Honest := PEmpty` is replaced by `HonestVCLT`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Walk Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7
open Nock.NockVMROM.Thm54.VclL.Compute.NodeRecQ7
open Nock.ComputeTable (State DTcomp)
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.VclL.Compute.CoreQ7 Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Compute.CompChipVCL
open Nock.NockVMROM.Thm54.VclL.Compute.CompTreeVCL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (seedSpecVCL)
open Nock.NockVMROM.Thm54.VclL.Chips (ioSpecVCLQuad ioSpecVCLQuad_round)
open Nock.NockVMROM.Thm54.VclL.Compute.SummandsQ7
open Nock.NockVMROM.Thm54.SVWalk
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.ComputeWalkSeed Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.ComputePaperPacking (OneHotSelector)
open Nock.NockVMROM.Thm54.Unhosted309 (goodSrc physOf physOf_good_round varVal)
open Nock.NockVMROM.Thm54.VclL.Compute.TopoQ7 (lnPatch_pub_sfe)

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

section family
variable (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [CharP K (ringChar K)] [Fintype F] [DecidableEq F] (hC : ℕ) (S : MemShape)
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **`CompSoundnessVCLT`** (the tower compute soundness family): `Kio = Kfp = Quad δ`, `Z := seedSpecVCL`,
`I := ioSpecVCLQuad`. -/
def compSoundnessVCLT :
    CompSoundnessFamily F K (Quad (algebraMap F K δ)) (Quad (algebraMap F K δ)) RV.KeyVCL frameVCL hC S
      (tableVCLT hC) 3 (m := RV.mVCL)
      (RV.recordViewVCL F K (Quad (algebraMap F K δ)) (tableVCLT hC) S hC)
      (seedSpecVCL (algebraMap F K δ)) (ioSpecVCLQuad (algebraMap F K δ)) where
  Msg0 := ℕ → F
  chip := fun V x ρ χ => chipCFT δ V x ρ χ
  chip_width := fun V x ρ χ => chipCFT_width δ V x ρ χ
  reqBound := reqBoundCF
  reqFacts := fun V x ρ χ Q h => reqFactsCFT δ V x ρ χ Q h
  reqFacts_length := fun V x ρ χ Q h a => reqFactsCFT_length δ V x ρ χ Q h a
  reqRecords := fun V x Q χ => reqRecordsCFT δ V x Q χ
  recRound := 1
  recRound_le_io := fun i hi => (ioSpecVCLQuad_round (algebraMap F K δ) i hi).ge
  reqRecords_round := fun V x Q Q' χ χ' hQ _ => by
    funext a
    exact reqRecsT_round δ V _ _ _ _ Q Q' (fun j hj => hQ j hj) a
  reqFacts_records := fun V x ρ χ Q h a => reqFactsCFT_records δ V x ρ χ Q h a
  shape := fun V _ b => shapeVG (towerGather δ V.basis) V b
  shape_size := fun V _ b => shapeVG_size_le (towerGather δ V.basis) V b
  tree := fun V x Q χ => treeVG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ)
    (pubVQ7T δ V.basis V.claim x χ) Q
  treeRound := 2
  tree_round := fun V x Q Q' χ χ' hQ hχ => by
    have hs : ∀ i : Fin frameVCL.n, frameVCL.sampledAfter i < 2 := by decide
    have h1 : χ = χ' := funext fun i => hχ i (hs i)
    have h2 : Q = Q' := funext fun j => hQ j ((tableVCLT_wide hC).le_two j)
    subst h1; subst h2; rfl
  tree_shape := fun V x Q χ => treeVG_shape (towerGather δ V.basis) V _ _ Q
  axB0 := fun V _ b _ k => axB0Q7 V b k
  keyOf := fun V _ b st k => keyOfQ7 V b st k
  recKey := fun V _ b st S' j => recKeyQ7' V b st S' j
  recKey_s0 := fun V _ b S' => recKey_s0' V b S'
  inlineRecords := fun _ => 0
  inline_not_read := fun st j hj => absurd hj (Nat.not_lt_zero _)
  inlinePairs := fun _ _ _ => []
  inlinePairCount := 0
  inlinePairs_length := fun _ _ _ => le_rfl
  summands := fun V _ => summandsQ7T δ V
  node_records := fun V x ρ χ Q h Qm hout u hu j _ hj =>
    node_records_CFT δ V x ρ χ Q h Qm hout u hu j hj
  inline_records := fun V x ρ χ Q h Qm hout u hu j hj => absurd hj (Nat.not_lt_zero _)
  root_binds := fun V x ρ χ Q h Qm hout => root_binds_CFT δ V x ρ χ Q h Qm hout
  Honest := HonestVCLT F K δ hC S
  honestV := fun H => H.V
  honestMsg0 := fun H => xT H.t
  honestReq := fun H χ => reqT H.t χ
  honestQ := fun H χ => traceT H.V χ H.αs H.hgen
  honest_staged := fun H => honest_staged_T H
  honestBad := fun H => badT H.V H.t
  honest_accepted := fun H χ Qm hbad => honest_accepted_T H χ Qm hbad

end family

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
