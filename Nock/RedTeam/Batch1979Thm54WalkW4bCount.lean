/-
  Nock/RedTeam/Batch1979Thm54WalkW4bCount.lean

  **`|walkRows| ≤ pathLen` on the run.**

  * `GenWalkCount.trie_size_le`: a read trie has at most `Σ_{distinct targets} |target|` nodes;
    `walkRows_length_le`: `|walkRows| ≤ Σ_{distinct path reads} depth (+1 dummy iff no read)`.
  * Consequence for the completeness twin: the path table's chosen orbit height `hPr`
    also fits the walk table, so `hF` can stay verbatim (heights from `pathLen`).
  * Control: `reads3`  is tight (`3 = 3`).
-/
import Nock.NockVMROM.Thm54.VclL.Walk.GenWalkCount
import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestRun
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemReq
import Nock.RedTeam.Batch1978Thm54WalkW4bBound

set_option autoImplicit false

namespace Nock.RedTeam.Batch1979

open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk Nock.NockVMROM.Thm54.VclL.Chips
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

theorem walkLen_le_pathLen {fuel : ℕ} {S Fm R : Noun}
    {t : NTree (GenComputeRow (Quad (algebraMap F K δF)))}
    (hgen : genComputeSkeleton (K := Quad (algebraMap F K δF)) fuel S Fm = .ok (t, R)) :
    (walkRows (demT t).cells (demT t).preads).length ≤ pathLen (K := K) δF t := by
  refine (walkRows_length_le _ _).trans (le_of_eq ?_)
  unfold pathLen pathTableP pathTable
  rw [List.length_append, List.length_flatMap, chainRows_length]
  congr 1
  · congr 1
    refine List.map_congr_left fun r hr => ?_
    rw [chainRows_length]
    obtain ⟨-, -, child, hw⟩ := deep_facts hr (demT_slot_of_gen δF hgen r hr)
    have := congrArg List.length (pathSteps_sides r.1 (axisBits r.2) (by rw [hw]; rfl))
    simpa using this.symm
  · by_cases hp : pathReads (demT t).preads = []
    · rw [padSteps_of_eq _ _ hp, if_pos hp]; rfl
    · rw [padSteps_of_ne _ _ hp, if_neg hp]; rfl

theorem reads3_tight :
    (walkRows [Batch1978.rA, Batch1978.rB, Batch1978.rC] Batch1978.reads3).length =
      ((pathReads Batch1978.reads3).map fun r => depthOf r.2).sum := by
  rw [Batch1978.reads3_walk.2, Batch1978.reads3_path]

end

end Nock.RedTeam.Batch1979

#print axioms Nock.NockVMROM.Thm54.VclL.GenWalk.trie_size_le
#print axioms Nock.NockVMROM.Thm54.VclL.GenWalk.costT_split
#print axioms Nock.NockVMROM.Thm54.VclL.GenWalk.costT_targetsOf
#print axioms Nock.NockVMROM.Thm54.VclL.GenWalk.walkRows_length_le
#print axioms Nock.RedTeam.Batch1979.walkLen_le_pathLen
#print axioms Nock.RedTeam.Batch1979.reads3_tight
