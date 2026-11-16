/-
  Nock/RedTeam/Batch164Thm54TraceConfined.lean

  **The Λ-confinement premise is real, is sharp, and does discharge `census`.**

  `GenTraceConfined.lean` makes `RowLeafWindow` follow from a decidable measurement, and
  `GenGenericCensusWindow.lean` turns that into `Data.census` for every accepted program.  Two ways
  that story could be worth nothing:

  1. the premise could be undischargeable in practice — decidable in principle but not reducible at
     any real tree; or
  2. it could be vacuous — satisfied for every `Λ`, in which case it constrains nothing and the
     projection is doing no work.

  Both are checked here at Tier A's OP6/OP2/OP9 program, which is the smallest committed tree that
  is outside every DFS = BFS shape gate (`dotTree_not_isPathTree`,
  `dotTree_not_childrenAreLeaves`).

  * `dot_traceConfined` — the measurement **holds** at `Λ = 22`, discharged from the row list.
  * `dot_not_traceConfined_21` — and **fails** at `Λ = 21`.  So 22 is the exact window of this
    program, the premise is a genuine constraint on `Λ`, and (2) is refuted.
  * `dot_root_not_rowLeafWindow` — at 21 the *conclusion* fails too, at the root row: the projection
    is not proving something that would hold anyway.
  * `dot_census_generic` — `census` at the dot program, obtained from the generic theorem with the
    measurement as its only input.  Nothing program-specific enters except the number 22.

  Note where the 22 comes from: the root row's **formula**, whose 22 leaves are the whole program
  text.  That is `NockProgram^Λ`'s window doing exactly what it says.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenericCensusWindow
import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.ForestExponentWindow

set_option autoImplicit false

namespace Nock.RedTeam.Batch164

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.CensusExtraClosure
open Nock.NockVMROM.Thm54.HonestCommitment
open ComputeTable

variable {K : Type} [Field K]

/-! ## The measurement is dischargeable -/

/-- **The Tier A program is Λ-confined at 22**, discharged from `dot_air_bfsRows` row by row.

This is the whole cost of the premise at a concrete program: eight rows, three `Nat` comparisons
each, no proof about the construction. -/
theorem dot_traceConfined : TraceConfined 22 (dotTreeAir (K := K)) := by
  intro g hg
  rw [dot_air_bfsRows] at hg
  fin_cases hg <;>
    exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

/-! ## The measurement is not vacuous -/

/-- **And it fails at 21.**  So `TraceConfined` is a real constraint on `Λ`, not a predicate every
tree satisfies; 22 is this program's exact window. -/
theorem dot_not_traceConfined_21 : ¬ TraceConfined 21 (dotTreeAir (K := K)) := by
  intro h
  have hr := h (dotTreeAir (K := K)).label (by rw [dot_air_bfsRows]; simp)
  exact absurd (show (22 : ℕ) ≤ 21 from hr.2.1) (by decide)

/-- **The conclusion fails at 21 too**, at the root row.  The projection therefore carries the
premise into a place where it is needed: without it `RowLeafWindow` is false here, so
`leafWindow_of_traceConfined` is not proving a fact that holds regardless. -/
theorem dot_root_not_rowLeafWindow :
    ¬ RowLeafWindow 21 (dotTreeAir (K := K)).label.skel := by
  intro h
  exact absurd (show (22 : ℕ) ≤ 21 from h.2.1) (by decide)

/-! ## And it discharges `census` -/

/-- **`Data.census` at the Tier A program, from the generic theorem.**

The only program-specific input is the number 22.  Everything else — cell identities, the leaf
window at all nine subformula slots, the edge-pair comparisons — comes from
`genComputeSkeleton_census_air`, which knows nothing about this program beyond the fact that the
generator accepted it. -/
theorem dot_census_generic (z α : K) (mf : List (NTree (MemoryNode K))) :
    EdgeComparisonCensus.CombinedSkeletonCensus K
      (skeletonOfNodes (mapNTree GenComputeRow.node
        (renderRows z α (bfsAssign (airReorder (dotTree (K := K)))))) mf) 22 :=
  genComputeSkeleton_census_air z α (by decide) (genComputeSkeleton_dot 0)
    (by rw [airReorder_dotTree]; exact dot_traceConfined) mf

end Nock.RedTeam.Batch164

#print axioms Nock.RedTeam.Batch164.dot_traceConfined
#print axioms Nock.RedTeam.Batch164.dot_not_traceConfined_21
#print axioms Nock.RedTeam.Batch164.dot_root_not_rowLeafWindow
#print axioms Nock.RedTeam.Batch164.dot_census_generic
