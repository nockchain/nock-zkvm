/-
  Nock/RedTeam/Batch772Thm54RequestIndex.lean

  * `mapComputeJoinInFuel_shape`: the deployed compute join (`mapComputeJoinIn`, hence
    `mapComputeJoin` / `computeJoinOf`) preserves the tree shape and every row's state, for ANY
    subject, formula, served forest and `q`.  So the built skeleton's BFS state sequence is the
    typed rows' state sequence.
  * `requestList_getElem?`: in `requestList S`, slot `j` of BFS row `a` sits at index
    `Σ_{a' < a} recordCount(state a') + j` (0-based), for ANY row list.
-/
import Nock.RedTeam.Batch530Thm54ComputeTreeBindsDeployed
import Nock.NockVMROM.Thm54.PreZCensusCore
import Nock.NockVMROM.Thm54.P8Core.Batch772Thm54RequestIndex

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch772

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.PreSeedCensus

variable {K : Type} [Field K] [DecidableEq K]

theorem mapComputeJoinInFuel_shape (q : ℕ) (forest : List (NTree (MState × DTmem K))) :
    ∀ (n : ℕ) (t : NTree (State × DTcomp K)) (subj formula : Noun), t.size ≤ n →
      mapNTree ComputeRowSkeleton.state (mapComputeJoinInFuel n q forest t subj formula) =
        mapNTree Prod.fst t := by
  intro n
  induction n with
  | zero =>
      intro t _ _ h
      cases t
      simp [NTree.size] at h
  | succ n ih =>
      intro t subj formula hsz
      obtain ⟨row, ch⟩ := t
      have IH : ∀ c ∈ ch, ∀ s f,
          mapNTree ComputeRowSkeleton.state (mapComputeJoinInFuel n q forest c s f) =
            mapNTree Prod.fst c :=
        fun c hc s f => ih c s f (Batch530.child_size_le_of_node hsz hc)
      rcases row with ⟨st, d⟩
      cases st <;> rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, rest⟩⟩⟩⟩ <;>
        simp [mapComputeJoinInFuel, mapNTree, computeSkeletonRow, IH] <;>
        (intro a ha; exact IH a (by simp [ha]) _ _)

/-! ## §B  the request list is indexed by the exponent prefix -/

end Nock.RedTeam.Batch772

#print axioms Nock.RedTeam.Batch772.mapComputeJoinInFuel_shape
#print axioms Nock.RedTeam.Batch772.recs_length
#print axioms Nock.RedTeam.Batch772.recs_getElem?
#print axioms Nock.RedTeam.Batch772.flatMap_getElem?_prefix
#print axioms Nock.RedTeam.Batch772.requestList_getElem?
