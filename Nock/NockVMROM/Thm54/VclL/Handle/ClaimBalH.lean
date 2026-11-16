/-
  Nock/NockVMROM/Thm54/VclL/Handle/ClaimBalH.lean

  Additive.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ClaimH
import Nock.NockVMROM.Thm54.VclL.Handle.HonestRows
import Nock.NockVMROM.Thm54.TraceGen.GenMemTable

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.TraceGen
open Nock.ComputeTable (FP)

noncomputable section

section Claim
variable {q : ℕ} {Kfp : Type} [Field Kfp] [Fintype Kfp] [DecidableEq Kfp] [Algebra (ZMod q) Kfp]
  [Fact q.Prime]

/-- **The claim's validity record is provided (balanced) at the honest table.** -/
theorem claim_validity_balanced (z : Kfp) (cells claim xcs : List Noun)
    (hnd : cells.Nodup) (hcell : ∀ n ∈ cells, n.isCell = true)
    (hclosed : ∀ n ∈ cells, ∀ c ∈ childCells n, c ∈ cells)
    (hbind : ∀ b ∈ claim.flatMap selfCell, b ∈ cells) :
    ValidityBalanced (tableRows (q := q) z cells (vcsOf cells claim) xcs)
      ((claim.flatMap selfCell).map (vkeyOf z cells)) :=
  genMemTable_validity_balanced z cells claim xcs hnd hcell hclosed hbind

/-- One external lookup per claim-cell occurrence (atoms carry none). -/
theorem claim_external_length (z : Kfp) (cells claim : List Noun) :
    ((claim.flatMap selfCell).map (vkeyOf z cells)).length = (claim.flatMap selfCell).length := by
  simp

/-- **The row of a cell provides its validity key `vcs.count` times**: child in-degree plus the claim
occurrences (the claim record is one unit of that count). -/
theorem claim_row_provides (z : Kfp) (cells claim xcs : List Noun)
    (hcell : ∀ n ∈ cells, n.isCell = true) {n : Noun} (hn : n ∈ cells) :
    (vkeyOf z cells n, (cells.flatMap childCells).count n + (claim.flatMap selfCell).count n) ∈
      vProv (tableRows (q := q) z cells (vcsOf cells claim) xcs) := by
  rw [vProv_rows z cells _ xcs hcell]
  refine List.mem_map.mpr ⟨n, hn, ?_⟩
  simp [vcsOf, List.count_append]

/-- **The claim handles denote the claim nouns at the honest table**: the validity existence form
(`hprov` of `claim_handles_denote`) is discharged from the balance. -/
theorem claim_denotes_honest (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0) (cells claim xcs : List Noun)
    (hnd : cells.Nodup) (hcell : ∀ n ∈ cells, n.isCell = true)
    (hclosed : ∀ n ∈ cells, ∀ c ∈ childCells n, c ∈ cells)
    (hbind : ∀ b ∈ claim.flatMap selfCell, b ∈ cells)
    (h : TableAccepts z (tableRows (q := q) z cells (vcsOf cells claim) xcs)
      ((claim.flatMap selfCell).map (vkeyOf z cells)))
    (hT2 : z ∉ tableBadSeeds fuelChip
      ((tableRows (q := q) z cells (vcsOf cells claim) xcs).map (·.b0)) claim)
    (hwin : ∀ x ∈ claim, x.leaves ≤ fuelChip ∧ ∀ k ∈ x.leafList, k < q) :
    ∀ x ∈ claim,
      denH ((tableRows (q := q) z cells (vcsOf cells claim) xcs).map (·.b0))
        (claimHandle x (cells.idxOf x)) = some x := by
  have hbal := claim_validity_balanced (q := q) z cells claim xcs hnd hcell hclosed hbind
  refine claim_handles_denote hq hz h hT2 hwin (fun x => cells.idxOf x) ?_
  intro x hx L R hxLR
  have hmem : vkeyOf z cells x ∈ (claim.flatMap selfCell).map (vkeyOf z cells) := by
    refine List.mem_map.mpr ⟨x, List.mem_flatMap.mpr ⟨x, hx, ?_⟩, rfl⟩
    rw [hxLR]; simp [selfCell]
  obtain ⟨c, hc, hk⟩ := ValidityBalanced.provided hbal _ hmem
  exact ⟨rankOf x / 2 ^ 62, rankOf x % 2 ^ 62, c, hc, hk⟩

end Claim

section Pub
variable {F : Type} [Field F]

/-- The honest claim publics are the handles of the root row's `s f e` (the consume side of the claim
record: the first row's `hpub` gates compare the row's handles with these, nothing else). -/
theorem pubVec_hdl (cells : List Noun) (r0 : RowN) :
    ((pubVec cells r0 0 : F), (pubVec cells r0 1 : F)) = hdl cells r0.s ∧
    ((pubVec cells r0 2 : F), (pubVec cells r0 3 : F)) = hdl cells r0.f ∧
    ((pubVec cells r0 4 : F), (pubVec cells r0 5 : F)) = hdl cells r0.e :=
  ⟨rfl, rfl, rfl⟩

end Pub

end

end Nock.NockVMROM.Thm54.VclL.Handle
