/-
  Nock/RedTeam/Batch1944Thm54AccHonest.lean

  **The accumulator gates at the honest trace, and the repeated-read
  multiplicity check.**

  * Route: prefix-sum fill (`accGatesT_honest`), the terms at
    the filled env equal those at the accumulator-zeroed env (`termQ_acc_eq`: accumulator columns are round 2,
    the inverses `den′⁻¹` read round `≤ 1` only), publics = `reqT` (`pubCFT_r*`), terminals via
    `terminal_eq_closed` (`sumX_of_rows`, `sumP_of_rows`).
  * MULTIPLICITY (mandatory check), decided by proof:
    - path: the compute side requests one `pReq` PER OCCURRENCE (`sumP_of_rows`, no dedup); the memory path table
      has ONE chain per distinct read whose last row carries `m = preads.count r` (`path_pTotal`).  A duplicated
      read balances (`dup_path_balances`); a dedup'd provide total would NOT (`dedup_provide_unbalanced`).
    - export: `shallowSided` keeps every occurrence (`dup_export_kept`), and the cell table's `mx` counts every
      occurrence in `exportConsumers` (`xs_count_add`), so `honestReqCF 1` = memory `req 1` (`req_eq`) per occurrence.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestAccept
import Nock.NockVMROM.Thm54.VclL.Compute.TowerJointSizes
import Nock.RedTeam.Batch1938Thm54VclCompletenessJoint
import Nock.RedTeam.Batch1744Thm54VclLIOFieldQuad
import Nock.RedTeam.Batch1881Thm54TowerRowFactsAt

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch1944

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD

section Dup
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] {δF : F}
  [Fact (¬ IsSquare (algebraMap F K δF))]
variable (γ ρ z : Quad (algebraMap F K δF)) (cells : List Noun)

/-- **A duplicated path read balances**: at `preads = [r, r]` the memory path table's provide total (one chain,
`m = 2` on its last row) equals the compute side's closed form, which has TWO requests. -/
theorem dup_path_balances (reads : List (Noun × ℕ)) (r : Noun × ℕ) (hp : isPathAx r.2 = true)
    (hs : (Noun.slot r.2 r.1).isSome) :
    ∑ k ∈ Finset.range (pathTable δF z cells [r, r]).length,
        liftQ δF ((pathTable δF z cells [r, r]).getD k (chainRow δF z cells (.atom 0) 0 [] 0)).m *
          (pathFillInv δF γ ρ ((pathTable δF z cells [r, r]).getD k
            (chainRow δF z cells (.atom 0) 0 [] 0))).pProvInv =
      honestReqCF γ ρ z cells [r, r] reads 2 ∧
    honestReqCF γ ρ z cells [r, r] reads 2 = cinv δF γ ρ (pReq δF z cells r) + cinv δF γ ρ (pReq δF z cells r) ∧
    pathReads [r, r] = [r] := by
  have hpr : pathReads [r, r] = [r] := by simp [pathReads, hp]
  refine ⟨?_, ?_, hpr⟩
  · rw [path_pTotal γ ρ z cells [r, r] (by rw [hpr]; simpa using hs)]
    rfl
  · show (([r, r].filter fun r => isPathAx r.2).map fun r =>
      (FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (pReq δF z cells r))⁻¹).sum = _
    simp [hp, cinv]

/-- **NC: a dedup'd provide total would not balance** a duplicated read (whenever the record's reciprocal is
nonzero and `2 ≠ 1`, i.e. always in a field): the multiplicity `m = count` is load-bearing. -/
theorem dedup_provide_unbalanced (reads : List (Noun × ℕ)) (r : Noun × ℕ) (hp : isPathAx r.2 = true)
    (hne : cinv δF γ ρ (pReq δF z cells r) ≠ 0) :
    ((pathReads [r, r]).map fun r => cinv δF γ ρ (pReq δF z cells r)).sum ≠
      honestReqCF γ ρ z cells [r, r] reads 2 := by
  have hpr : pathReads [r, r] = [r] := by simp [pathReads, hp]
  rw [hpr]
  show _ ≠ (([r, r].filter fun r => isPathAx r.2).map fun r =>
      (FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (pReq δF z cells r))⁻¹).sum
  simp only [hp, List.filter_cons_of_pos, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  intro h
  apply hne
  have : cinv δF γ ρ (pReq δF z cells r) = (FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (pReq δF z cells r))⁻¹ := rfl
  rw [this] at h ⊢
  linear_combination -h

end Dup

/-- **Export reads keep every occurrence**: a repeated export read `(c, 2)` gives two export requests on the
compute side (`shallowSided`) and two consumptions of `c` in the cell table's `exportConsumers` (its `mx`). -/
theorem dup_export_kept :
    shallowSided [((Noun.cell (.atom 1) (.atom 2)), 2), ((Noun.cell (.atom 1) (.atom 2)), 2)] =
        [((Noun.cell (.atom 1) (.atom 2)), false), ((Noun.cell (.atom 1) (.atom 2)), false)] ∧
      (exportConsumers [] [((Noun.cell (.atom 1) (.atom 2)), 2), ((Noun.cell (.atom 1) (.atom 2)), 2)]).count
        (Noun.cell (.atom 1) (.atom 2)) = 2 := by
  decide +kernel

end Nock.RedTeam.Batch1944

#print axioms Nock.RedTeam.Batch1944.dup_path_balances
#print axioms Nock.RedTeam.Batch1944.dedup_provide_unbalanced
#print axioms Nock.RedTeam.Batch1944.dup_export_kept
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.HonestVCLT.hacc
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.accGatesT_T_of_terms
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.termQ_acc_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.sumX_of_rows
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.sumP_of_rows
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honest_accepted_T
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.demT_slot
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.demT_depth_le
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.jointMemFacts_of
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.compSoundnessVCLT
#print axioms Nock.RedTeam.Batch1938.vcl_completeness'
#print axioms Nock.RedTeam.Batch1938.vcl_completeness_goldilocks
#print axioms Nock.RedTeam.Batch1937.vcl_completeness
