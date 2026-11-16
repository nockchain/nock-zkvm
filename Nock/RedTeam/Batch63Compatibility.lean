import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis

/-!
The repaired
production object no longer uses this list; retaining the snapshot lets the original compiled
finding remain reproducible without reinterpreting it against the replacement gates.

The
fourteen-entry `baseTransitionGates` below is a literal copy and never moves.  `compat_fold_tracks_live_source_list` below is the receipt.

And
`Batch63.honest_foldCollisionExcluded_nonvacuous`
(`Batch63Thm54OptimizedMemoryCanonicalSatisfaction.lean:262`) discharges the collision premise
from `canonical_transitionSources`, a fact about the live list only.  The snapshot's purpose is
served by freezing the *gate list* that the repartition replaced; the fold is a function of
whatever the census currently is, and saying so is cheaper than duplicating the canonical
satisfaction theory over a dead list.
-/

namespace Nock.RedTeam.Batch63

open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis

def baseTransitionGates {F : Type} [Field F] : List (CoeffExpr F) :=
  [bbool (F := F) (bcur (F := F) 0), bbool (F := F) (bcur (F := F) 1),
   bbool (F := F) (bcur (F := F) 2), bbool (F := F) (bcur (F := F) 3),
   bsum4 (F := F) .traceCur,
   bbool (F := F) (bcur (F := F) 4), bbool (F := F) (bcur (F := F) 5),
   .mul (bcur (F := F) 4) (bbool (F := F) (bcur (F := F) 0)),
   .mul (bcur (F := F) 4) (bbool (F := F) (bcur (F := F) 1)),
   .mul (bcur (F := F) 4) (bbool (F := F) (bcur (F := F) 2)),
   .mul (bcur (F := F) 4) (bbool (F := F) (bcur (F := F) 3)),
   .mul (bcur (F := F) 5) (bbool (F := F) (bcur (F := F) 0)),
   .mul (bcur (F := F) 5) (bbool (F := F) (bcur (F := F) 1)),
   .mul (bcur (F := F) 5) (bbool (F := F) (bcur (F := F) 2))]

def foldChallenge : Expr := .Var .challenge 6

noncomputable def sourceIndices {K : Type} [Field K] :
    List (Fin (transitionSources (K := K)).length) :=
  (Finset.univ : Finset (Fin (transitionSources (K := K)).length)).toList

noncomputable def foldAt {K : Type} [Field K] (j : Fin 21) : Expr :=
  (sourceIndices (K := K)).foldr
    (fun (i : Fin (transitionSources (K := K)).length) acc =>
      if (i : ℕ) % 21 = j then
        .Add (.Mul (.Pow foldChallenge ((i : ℕ) / 21))
          ((transitionSources (K := K)).get i)) acc
      else acc)
    (.Const 0)

noncomputable def extensionTransitionGates {K : Type} [Field K] : List Expr :=
  List.ofFn (foldAt (K := K))

def FoldCollisionExcluded {K : Type} [Field K] (env : Env K) : Prop :=
  ∀ j : Fin 21,
    ((foldAt (K := K)) j).eval env = 0 →
      ∀ i : Fin (transitionSources (K := K)).length,
        (i : ℕ) % 21 = j → ((transitionSources (K := K)).get i).eval env = 0

theorem source_to_fold_complete {K : Type} [Field K] (env : Env K)
    (h : ∀ e ∈ transitionSources (K := K), e.eval env = 0) :
    ∀ g ∈ extensionTransitionGates (K := K), g.eval env = 0 := by
  intro g hg
  obtain ⟨j, -, rfl⟩ := List.mem_ofFn.mp hg
  simp only [foldAt]
  induction (sourceIndices (K := K)) with
  | nil => simp [Expr.eval]
  | cons i t ih =>
      simp only [List.foldr_cons]
      by_cases hj : (i : ℕ) % 21 = j
      · rw [if_pos hj]
        simp only [Expr.eval]
        rw [h ((transitionSources (K := K)).get i) (List.get_mem _ _), mul_zero, zero_add]
        exact ih
      · rw [if_neg hj]
        exact ih

/-- **The compatibility fold tracks the live source census.**  Recorded so the header's claim is compiled rather than asserted. -/
theorem compat_fold_tracks_live_source_list {K : Type} [Field K] :
    (transitionSources (K := K)).length = 50 ∧
      (extensionTransitionGates (K := K)).length = 21 := by
  refine ⟨transitionSources_length (K := K), ?_⟩
  simp [extensionTransitionGates]

theorem fold_to_source_of_collision_excluded {K : Type} [Field K] (env : Env K)
    (hfold : ∀ g ∈ extensionTransitionGates (K := K), g.eval env = 0)
    (hcollision : FoldCollisionExcluded env) :
    ∀ e ∈ transitionSources (K := K), e.eval env = 0 := by
  intro e he
  obtain ⟨i, hi⟩ := List.get_of_mem he
  let j : Fin 21 := ⟨(i : ℕ) % 21, Nat.mod_lt _ (by omega)⟩
  rw [← hi]
  apply hcollision j
  · apply hfold ((foldAt (K := K)) j)
    exact List.mem_ofFn.mpr ⟨j, by simp⟩
  · simp [j]

end Nock.RedTeam.Batch63
