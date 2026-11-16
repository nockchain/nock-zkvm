/-
  Nock/RedTeam/Batch773Thm54ExpOfRequestList.lean

  Route B's (iii) `HbindCompute T Qc z` reads `T.read_root k` / `T.verify_child k` at
  `k = expOf P Qc a j = S(a) + j + 1`.  With `T = requestTargets S` for the BUILT skeleton `S`
  (any `mapComputeJoinIn` of `typedComputeTree`, in particular `decodedSkeletonOf`), this file
  proves, for every active slot `(a, j)` of the committed compute trace:

    `requestTargets S.read_root (expOf a j) = ((computeSkeletonRows S)[a].memoryRecord j).root`
    `requestTargets S.verify_child (expOf a j) = ((computeSkeletonRows S)[a].memoryRecord j).child`

  i.e. the exponent names the request of BFS row `a`, slot `j`, of the built skeleton.

  Premises, by class (Part 2 census):
  * `hsat`, `hchar` — acceptance (one-hot selector: the typed state's arity is the row's `rowArity`);
  * `Tiles computeFanout 1 rows`, `Queued computeFanout 1 rows` — acceptance, the walk gate
    (`Walk.SfF_tiling_of_qgate`, `bfsValidF_of_qgate`), over the TYPED rows `typedComputeRows P Qc`.
    (`ExecOfTraces.TracesWalkHyps` states them over `foC`/`lblC`, the family-chip labels; the
    bridge `foC = computeFanout ∘ typed` is NOT proved here.)
  No premise on the served forest, `q`, the root subject / formula, or `c ∉ event`.
-/
import Nock.RedTeam.Batch771Thm54BfsRoundTrip
import Nock.RedTeam.Batch772Thm54RequestIndex
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.WrapFixesVcomp
import Nock.NockVMROM.Thm54.P8Core.Batch773Thm54ExpOfRequestList
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch773

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.RedTeam.Batch772
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.WrapFixesVcomp
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.Framework
open Nock.Reified
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open scoped Polynomial

noncomputable section

/-! ## §A  the typed tree is the BFS inverse of the typed rows -/

section Typed

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X])

theorem typedComputeRows_ne_nil_of_tiles
    (ht : Batch771.Tiles computeFanout 1 (typedComputeRows P Qc)) :
    typedComputeRows P Qc ≠ [] := by
  intro h
  rw [h] at ht
  simp [Batch771.Tiles] at ht

theorem typedComputeTree_rows
    (ht : Batch771.Tiles computeFanout 1 (typedComputeRows P Qc))
    (hq : Batch771.Queued computeFanout 1 (typedComputeRows P Qc)) :
    (bfsForest [typedComputeTree P Qc]).map NTree.label = typedComputeRows P Qc := by
  have hbfs := Batch771.bfs_rebuildForest computeFanout le_rfl ht hq
  have hne := typedComputeRows_ne_nil_of_tiles P Qc ht
  have hrf : rebuildForest computeFanout 1 (typedComputeRows P Qc) =
      reconForest 1 (Batch771.foRows computeFanout (typedComputeRows P Qc))
        (Batch771.lblRows ((typedComputeRows P Qc).head hne) (typedComputeRows P Qc))
        (typedComputeRows P Qc).length :=
    Batch771.rebuildForest_eq_reconForest computeFanout _ le_rfl ht hq
  have hlen : (rebuildForest computeFanout 1 (typedComputeRows P Qc)).length = 1 := by
    rw [hrf]; simp [reconForest]
  rw [← hbfs]
  unfold typedComputeTree typedComputeForest
  generalize rebuildForest computeFanout 1 (typedComputeRows P Qc) = rf at hlen ⊢
  match rf, hlen with
  | [t], _ => simp

end Typed

/-! ## §B  an accepted row's typed state has the row's arity -/

section Rows

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X])

theorem arity_eq_recordCount (s : State) : arity s = Nock.Framework.recordCount s := by
  cases s <;> rfl

theorem computeStateOf_decodeSource (E : CorrectedFinalTypedEnv F K) :
    computeStateOf (DeployedComputeRows.decodeSource E) = computeStateOf E.toSourceEnv := by
  have h : ∀ k, k < 11 →
      (DeployedComputeRows.decodeSource E).trace k = E.toSourceEnv.trace k := by
    intro k hk
    simp [DeployedComputeRows.decodeSource, Env.ofSubst, computeSubst, computeTraceSubst, hk,
      Expr.eval]
  simp only [computeStateOf, h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num),
    h 4 (by norm_num), h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num),
    h 8 (by norm_num), h 9 (by norm_num), h 10 (by norm_num)]

variable (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
include hsat

/-- **The row's mask arity is `recordCount` of its typed state** (the one-hot selector of an
accepted row; `cons` / `s0` are told apart by column `10`). -/
theorem rowArity_eq_recordCount_typed
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (i : Fin (rows P)) :
    rowArity (rowEnv P Qc i) = Nock.Framework.recordCount (typedComputeLabel P Qc i).1 := by
  obtain ⟨s, hsel⟩ := source_selector P Qc hsat hchar i
  have hone : OneHotSelector (rowEnv P Qc i).toSourceEnv s := by
    intro st; rw [hsel st]; simp [ComputeTable.opSel]
  have hst : (typedComputeLabel P Qc i).1 = s := by
    show computeStateOf (DeployedComputeRows.decodeSource (rowEnv P Qc i)) = s
    rw [computeStateOf_decodeSource]
    exact computeStateOf_of_oneHot hone
  rw [hst, rowArity_eq_arity P Qc i s hsel, arity_eq_recordCount]

/-- **`S(a)` is the prefix of `recordCount` over the typed rows' states.** -/
theorem prefixExp_eq_typed_prefix
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) :
    ∀ m, m ≤ rows P → prefixExp P Qc m =
      (((typedComputeRows P Qc).take m).map
        (fun r => Nock.Framework.recordCount r.1)).sum := by
  intro m
  induction m with
  | zero => intro _; simp [prefixExp]
  | succ m ih =>
      intro hm
      have hm' : m < rows P := by omega
      rw [prefixExp_succ P Qc m hm', ih (by omega),
        rowArity_eq_recordCount_typed P Qc hsat hchar ⟨m, hm'⟩, List.take_add_one]
      have hlen : m < (typedComputeRows P Qc).length := by
        rw [typedComputeRows_length]; exact hm'
      have hget : (typedComputeRows P Qc)[m]? = some (typedComputeLabel P Qc ⟨m, hm'⟩) := by
        have hfr : (List.finRange P.optimized.family.problem.cfg.compRows)[m]? = some ⟨m, hm'⟩ := by
          rw [List.getElem?_eq_getElem (by simpa using hm')]; simp
        simp [typedComputeRows, List.getElem?_map, hfr]
      simp [hget]

end Rows

/-! ## §C  the built skeleton -/

section Built

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X])

/-- **The built skeleton's BFS state sequence is the typed rows' state sequence**, for any served
forest, `q`, root subject and formula. -/
theorem builtRows_states
    (ht : Batch771.Tiles computeFanout 1 (typedComputeRows P Qc))
    (hq : Batch771.Queued computeFanout 1 (typedComputeRows P Qc))
    (S : SemanticSkeleton) (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (subj formula : Noun)
    (hS : S.computeTree = mapComputeJoinIn q forest (typedComputeTree P Qc) subj formula) :
    (computeSkeletonRows S).map ComputeRowSkeleton.state =
      (typedComputeRows P Qc).map Prod.fst := by
  have hshape := Batch772.mapComputeJoinInFuel_shape q forest (typedComputeTree P Qc).size
    (typedComputeTree P Qc) subj formula le_rfl
  have h1 : computeSkeletonRows S = (bfsForest [S.computeTree]).map NTree.label := rfl
  have h3 := bfs_labels_mapNTree ComputeRowSkeleton.state S.computeTree
  rw [hS] at h3
  unfold mapComputeJoinIn at h3
  rw [hshape, bfs_labels_mapNTree, typedComputeTree_rows P Qc ht hq] at h3
  rw [h1, hS]
  unfold mapComputeJoinIn
  exact h3.symm

variable (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
include hsat

/-- **S5 — `expOf a j` is the `requestList` index of the built skeleton.**  For every active slot
`(a, j)` of the committed compute trace, entry `expOf a j − 1` (0-based; `expOf` is 1-based, as
`requestTargets`) of the built skeleton's request list is the record of BFS row `a`, slot `j`. -/
theorem expOf_requestList
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (ht : Batch771.Tiles computeFanout 1 (typedComputeRows P Qc))
    (hq : Batch771.Queued computeFanout 1 (typedComputeRows P Qc))
    (S : SemanticSkeleton) (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (subj formula : Noun)
    (hS : S.computeTree = mapComputeJoinIn q forest (typedComputeTree P Qc) subj formula)
    (a : Fin (rows P)) (j : Fin 3) (hact : activeMask (rowEnv P Qc a) j = 1) :
    ∃ (ha : (a : ℕ) < (computeSkeletonRows S).length)
      (hj : (j : ℕ) < Nock.Framework.recordCount (computeSkeletonRows S)[(a : ℕ)].state),
      (requestList S)[expOf P Qc a j - 1]? =
        some ((computeSkeletonRows S)[(a : ℕ)].memoryRecord
          ⟨j, lt_of_lt_of_le hj (Nock.Framework.recordCount_le _)⟩ hj) := by
  have hst := builtRows_states P Qc ht hq S q forest subj formula hS
  have hlenR : (computeSkeletonRows S).length = rows P := by
    have := congrArg List.length hst
    simpa [typedComputeRows_length] using this
  have haR : (a : ℕ) < (computeSkeletonRows S).length := by rw [hlenR]; exact a.isLt
  have hrows : (a : ℕ) < (typedComputeRows P Qc).length := by
    rw [typedComputeRows_length]; exact a.isLt
  -- the row's state
  have hstate : (computeSkeletonRows S)[(a : ℕ)].state = (typedComputeLabel P Qc a).1 := by
    have h := List.getElem_of_eq hst (i := (a : ℕ)) (by simpa using haR)
    simpa [typedComputeRows] using h
  have hjR : (j : ℕ) < Nock.Framework.recordCount (computeSkeletonRows S)[(a : ℕ)].state := by
    rw [hstate, ← rowArity_eq_recordCount_typed P Qc hsat hchar a]
    have := active_lt_rowArity (rowEnv P Qc a) j hact
    omega
  -- the prefix
  have hpre : (((computeSkeletonRows S).take (a : ℕ)).map
        (fun r => Nock.Framework.recordCount r.state)).sum = prefixExp P Qc a := by
    rw [prefixExp_eq_typed_prefix P Qc hsat hchar a (by omega)]
    have h := congrArg (fun l => (l.take (a : ℕ)).map Nock.Framework.recordCount |>.sum) hst
    simp only [List.map_take, List.map_map] at h
    simpa [Function.comp_def] using h
  refine ⟨haR, hjR, ?_⟩
  have h := requestList_getElem? S a haR j hjR
  rw [hpre] at h
  have hexp : expOf P Qc a j - 1 = prefixExp P Qc a + (j : ℕ) := by
    unfold expOf; omega
  rw [hexp]
  exact h

/-- **The built skeleton has exactly `totalRequests = S(rows)` requests.** -/
theorem requestList_length_eq_totalRequests
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (ht : Batch771.Tiles computeFanout 1 (typedComputeRows P Qc))
    (hq : Batch771.Queued computeFanout 1 (typedComputeRows P Qc))
    (S : SemanticSkeleton) (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (subj formula : Noun)
    (hS : S.computeTree = mapComputeJoinIn q forest (typedComputeTree P Qc) subj formula) :
    (requestList S).length = totalRequests P Qc := by
  have hst := builtRows_states P Qc ht hq S q forest subj formula hS
  rw [requestList_eq, List.length_flatMap]
  simp only [recs_length]
  have h := congrArg (fun l => (l.map Nock.Framework.recordCount).sum) hst
  simp only [List.map_map] at h
  unfold totalRequests
  rw [prefixExp_eq_typed_prefix P Qc hsat hchar (rows P) le_rfl,
    List.take_of_length_le (by rw [typedComputeRows_length])]
  simpa [Function.comp_def] using h

/-- **`requestTargets` at `expOf`** (the (iii) target of route B, `T := requestTargets S`): the
root / child noun at the exponent of an active slot are the root / child of that row's record. -/
theorem requestTargets_expOf
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (ht : Batch771.Tiles computeFanout 1 (typedComputeRows P Qc))
    (hq : Batch771.Queued computeFanout 1 (typedComputeRows P Qc))
    (S : SemanticSkeleton) (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (subj formula : Noun)
    (hS : S.computeTree = mapComputeJoinIn q forest (typedComputeTree P Qc) subj formula)
    (a : Fin (rows P)) (j : Fin 3) (hact : activeMask (rowEnv P Qc a) j = 1) :
    ∃ (ha : (a : ℕ) < (computeSkeletonRows S).length)
      (hj : (j : ℕ) < Nock.Framework.recordCount (computeSkeletonRows S)[(a : ℕ)].state),
      requestTargets S .read_root (expOf P Qc a j) =
          ((computeSkeletonRows S)[(a : ℕ)].memoryRecord
            ⟨j, lt_of_lt_of_le hj (Nock.Framework.recordCount_le _)⟩ hj).root ∧
        requestTargets S .verify_child (expOf P Qc a j) =
          ((computeSkeletonRows S)[(a : ℕ)].memoryRecord
            ⟨j, lt_of_lt_of_le hj (Nock.Framework.recordCount_le _)⟩ hj).child := by
  obtain ⟨ha, hj, h⟩ := expOf_requestList P Qc hsat hchar ht hq S q forest subj formula hS a j hact
  refine ⟨ha, hj, ?_, ?_⟩
  · have hk : expOf P Qc a j = (expOf P Qc a j - 1) + 1 := by
      have := expOf_pos P Qc a j; omega
    rw [hk]
    simp [requestTargets, h]
  · have hk : expOf P Qc a j = (expOf P Qc a j - 1) + 1 := by
      have := expOf_pos P Qc a j; omega
    rw [hk]
    simp [requestTargets, h]

/-- **The same, for the route-B built skeleton `decodedSkeletonOf`** (the root subject / formula
wrappers are `mapComputeJoin`'s; the theorem does not look at them). -/
theorem requestTargets_expOf_decoded
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (ht : Batch771.Tiles computeFanout 1 (typedComputeRows P Qc))
    (hq : Batch771.Queued computeFanout 1 (typedComputeRows P Qc))
    (a : Fin (rows P)) (j : Fin 3) (hact : activeMask (rowEnv P Qc a) j = 1) :
    ∃ (ha : (a : ℕ) < (computeSkeletonRows (decodedSkeletonOf P Qc Qm)).length)
      (hj : (j : ℕ) < Nock.Framework.recordCount
        (computeSkeletonRows (decodedSkeletonOf P Qc Qm))[(a : ℕ)].state),
      requestTargets (decodedSkeletonOf P Qc Qm) .read_root (expOf P Qc a j) =
          ((computeSkeletonRows (decodedSkeletonOf P Qc Qm))[(a : ℕ)].memoryRecord
            ⟨j, lt_of_lt_of_le hj (Nock.Framework.recordCount_le _)⟩ hj).root ∧
        requestTargets (decodedSkeletonOf P Qc Qm) .verify_child (expOf P Qc a j) =
          ((computeSkeletonRows (decodedSkeletonOf P Qc Qm))[(a : ℕ)].memoryRecord
            ⟨j, lt_of_lt_of_le hj (Nock.Framework.recordCount_le _)⟩ hj).child :=
  requestTargets_expOf P Qc hsat hchar ht hq (decodedSkeletonOf P Qc Qm) (ringChar K)
    (typedMemoryForest P Qm) _ _ rfl a j hact

end Built

end

end Nock.RedTeam.Batch773

#print axioms Nock.RedTeam.Batch773.typedComputeTree_rows
#print axioms Nock.RedTeam.Batch773.rowArity_eq_recordCount_typed
#print axioms Nock.RedTeam.Batch773.prefixExp_eq_typed_prefix
#print axioms Nock.RedTeam.Batch773.builtRows_states
#print axioms Nock.RedTeam.Batch773.expOf_requestList
#print axioms Nock.RedTeam.Batch773.requestList_length_eq_totalRequests
#print axioms Nock.RedTeam.Batch773.requestTargets_expOf
#print axioms Nock.RedTeam.Batch773.requestTargets_expOf_decoded
