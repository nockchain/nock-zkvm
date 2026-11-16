import Nock.RedTeam.Batch1250Thm54HonestGoodGenerated
import Nock.NockVMROM.Thm54.TraceGen.GenMemAtomFill
import Nock.NockVMROM.Thm54.TraceGen.GenRequestTargets
import Nock.NockVMROM.Thm54.TraceGen.GenRecordExponentBridge
import Nock.RedTeam.Batch998Thm54HonestExponentCoherence
import Nock.RedTeam.Batch1251Thm54HonestPairNotDiagonal

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1253Thm54HonestBatch1253.SeedIrrelevance.lean

* `genMemoryForest_bfs_sig`: the BFS `(skel, stamp)` projection of `genMemoryForest z α λ inp t` equals that of the
    reference forest `refForest t` (`E = encC 1`, `z = α = 1`, `λ = 0`): it reads none of `E, z, α, λ, inp`.
  * `honestPairs0 F K q t`: a z-FREE pair list (states, halt atoms, record exponents of `rows0 t`, targets
    `requestTargets` of the compute skeleton).  `AtGen.reqPairs_eq_honestPairs0`: at `genPkg` the pinned component-12
    pair list IS `honestPairs0` (the z-irrelevance lemma).  `AtGen.hpair_of_seed`: `z ∉ pairBadSeeds (M₀ ⊔ Λ)
    honestPairs0 → hpair`.
  * `Seed`: the widened seed `romSeedPair` (census ∧ size window ∧ `SeedGood` ∧ pair-good) under
    `seedBudgetPairB Λ rows M₀ < |K|`; `pairBadSeeds` card `≤ M₀·(2(M₀⊔Λ)−1)`; `pairBudget_lt_pow` (one pair term,
    `< p³` at `25 ≤ p`: `hp` unmoved).

  -- the paper
-/

/-! Scratch (fork PAIR): the skeleton/stamp projection of the generated memory forest reads
neither the encoder `E`, nor `z`, `α`, `λ`. -/

set_option autoImplicit false

namespace Nock.RedTeam.Batch1253

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TraceGen

variable {K : Type} [Field K]

/-- The coin-free projection of a generated memory row: its skeleton and its stamp. -/
def sig (g : GenMemoryRow K) : MemoryRowSkeleton × MemoryTimestampRow := (g.skel, g.stamp)

/-- Forest form. -/
def sigF (l : List (NTree (GenMemoryRow K))) := l.map (mapNTree (sig (K := K)))

theorem nounWalk_sig (E E' : Noun → ComputeTable.FP K) (z z' lmb lmb' : K) :
    ∀ n, mapNTree sig (genAnnotatedNounWalk E z lmb n).1 =
      mapNTree sig (genAnnotatedNounWalk E' z' lmb' n).1
  | .atom _ => by simp [genAnnotatedNounWalk, mapNTree, sig, gMemRow9]
  | .cell h t => by
      simp only [genAnnotatedNounWalk, mapNTree, List.map_cons, List.map_nil]
      rw [nounWalk_sig E E' z z' lmb lmb' h, nounWalk_sig E E' z z' lmb lmb' t]
      simp [sig, gMemRow9]

theorem verify_sig (E E' : Noun → ComputeTable.FP K) (z z' lmb lmb' : K)
    (root child : Noun) (ax : ℕ) (ts ts' : K) (recordExp : ℕ) :
    mapNTree sig (genAnnotatedVerify E z lmb root child ax ts recordExp).1 =
      mapNTree sig (genAnnotatedVerify E' z' lmb' root child ax ts' recordExp).1 := by
  simp only [genAnnotatedVerify, mapNTree, List.map_cons, List.map_nil]
  rw [nounWalk_sig E E' z z' lmb lmb' child]
  simp [sig, gMemRow9]

theorem descent_sig (E E' : Noun → ComputeTable.FP K) (z z' lmb lmb' : K)
    (root child : Noun) (recAxis : ℕ) (ts ts' : K) (recordExp : ℕ)
    (currentNoun : Noun) (remainingAxis : ℕ) :
    sigF (genAnnotatedDescent E z lmb root child recAxis ts recordExp currentNoun remainingAxis).1 =
      sigF (genAnnotatedDescent E' z' lmb' root child recAxis ts' recordExp currentNoun
        remainingAxis).1 := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    rw [genAnnotatedDescent, genAnnotatedDescent]
    split
    · simp only [sigF, List.map_cons, List.map_nil]
      rw [verify_sig E E' z z' lmb lmb' root child recAxis ts ts' recordExp]
    · split
      · have h1 := ih (axisRest n) (axisRest_lt (by omega)) (formulaTail currentNoun)
        simp only [sigF] at h1 ⊢
        simp only [List.map_cons, List.map_nil, mapNTree, List.map_append, h1]
        rw [nounWalk_sig E E' z z' lmb lmb' (formulaHead currentNoun)]
        simp [sig, gMemRow9]
      · have h1 := ih (axisRest n) (axisRest_lt (by omega)) (formulaHead currentNoun)
        simp only [sigF] at h1 ⊢
        simp only [List.map_cons, List.map_nil, mapNTree, List.map_append, h1]
        rw [nounWalk_sig E E' z z' lmb lmb' (formulaTail currentNoun)]
        simp [sig, gMemRow9]

theorem recordTree_sig (E E' : Noun → ComputeTable.FP K) (z z' α α' lmb lmb' : K)
    (root child : Noun) (axis : ℕ) (recordExp : ℕ) :
    mapNTree sig (genAnnotatedRecordTree E z α lmb root child axis recordExp) =
      mapNTree sig (genAnnotatedRecordTree E' z' α' lmb' root child axis recordExp) := by
  have h := descent_sig E E' z z' lmb lmb' root child axis (α ^ recordExp) (α' ^ recordExp)
    recordExp root axis
  simp only [sigF] at h
  simp only [genAnnotatedRecordTree, mapNTree, h]
  simp [sig, gMemRow9]

theorem descentCont_sig (E E' : Noun → ComputeTable.FP K) (z z' lmb lmb' : K)
    (cont cont' : List (NTree (GenMemoryRow K)))
    (contCell contCell' : MemoryTable.Cell K) (contState : MemoryTable.MState)
    (currentNoun : Noun) (remainingAxis : ℕ) (hc : sigF cont = sigF cont') :
    sigF (genAnnotatedDescentCont E z lmb cont contCell contState currentNoun remainingAxis).1 =
      sigF (genAnnotatedDescentCont E' z' lmb' cont' contCell' contState currentNoun
        remainingAxis).1 := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    rw [genAnnotatedDescentCont, genAnnotatedDescentCont]
    split
    · exact hc
    · split
      · have h1 := ih (axisRest n) (axisRest_lt (by omega)) (formulaTail currentNoun)
        simp only [sigF] at h1 ⊢
        simp only [List.map_cons, List.map_nil, mapNTree, List.map_append, h1]
        rw [nounWalk_sig E E' z z' lmb lmb' (formulaHead currentNoun)]
        simp [sig, gMemRow9]
      · have h1 := ih (axisRest n) (axisRest_lt (by omega)) (formulaHead currentNoun)
        simp only [sigF] at h1 ⊢
        simp only [List.map_cons, List.map_nil, mapNTree, List.map_append, h1]
        rw [nounWalk_sig E E' z z' lmb lmb' (formulaTail currentNoun)]
        simp [sig, gMemRow9]

theorem chainedInner_sig (E E' : Noun → ComputeTable.FP K) (z z' α α' lmb lmb' : K)
    (prev : MemRecordReq) :
    ∀ reqs, sigF (genAnnotatedChainedInner E z α lmb prev reqs).1 =
      sigF (genAnnotatedChainedInner E' z' α' lmb' prev reqs).1
  | [] => by
      simp only [genAnnotatedChainedInner, sigF, List.map_cons, List.map_nil]
      rw [verify_sig E E' z z' lmb lmb' prev.root prev.child prev.axis (α ^ prev.recordExp)
        (α' ^ prev.recordExp) prev.recordExp]
  | r :: more => by
      have hin := chainedInner_sig E E' z z' α α' lmb lmb' r more
      have hd := descentCont_sig E E' z z' lmb lmb'
        (genAnnotatedChainedInner E z α lmb r more).1
        (genAnnotatedChainedInner E' z' α' lmb' r more).1
        (genAnnotatedChainedInner E z α lmb r more).2
        (genAnnotatedChainedInner E' z' α' lmb' r more).2
        (chainedInnerRootState more) r.root r.axis hin
      simp only [sigF] at hd
      simp only [genAnnotatedChainedInner, sigF, List.map_cons, List.map_nil, mapNTree, hd]
      simp [sig, gMemRow9]

theorem chainedTree_sig (E E' : Noun → ComputeTable.FP K) (z z' α α' lmb lmb' : K)
    (reqs : List MemRecordReq) :
    (genAnnotatedChainedTree E z α lmb reqs).map (mapNTree sig) =
      (genAnnotatedChainedTree E' z' α' lmb' reqs).map (mapNTree sig) := by
  match reqs with
  | [] => simp [genAnnotatedChainedTree]
  | [r] =>
      simp only [genAnnotatedChainedTree, Option.map_some]
      rw [recordTree_sig E E' z z' α α' lmb lmb']
  | r :: r2 :: rest =>
      have hin := chainedInner_sig E E' z z' α α' lmb lmb' r (r2 :: rest)
      have hd := descentCont_sig E E' z z' lmb lmb'
        (genAnnotatedChainedInner E z α lmb r (r2 :: rest)).1
        (genAnnotatedChainedInner E' z' α' lmb' r (r2 :: rest)).1
        (genAnnotatedChainedInner E z α lmb r (r2 :: rest)).2
        (genAnnotatedChainedInner E' z' α' lmb' r (r2 :: rest)).2
        (chainedInnerRootState (r2 :: rest)) r.root r.axis hin
      simp only [sigF] at hd
      simp only [genAnnotatedChainedTree, Option.map_some, mapNTree, hd]
      simp [sig, gMemRow9]

theorem chainedTree_isSome (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (r : MemRecordReq) (rs : List MemRecordReq) :
    ∃ t, genAnnotatedChainedTree E z α lmb (r :: rs) = some t := by
  cases rs <;> exact ⟨_, rfl⟩

theorem pairForest_sig (E E' : Noun → ComputeTable.FP K) (z z' α α' lmb lmb' : K)
    (r1 r2 : MemRecordReq) :
    sigF (if r1.child = r2.root then
        match genAnnotatedChainedTree E z α lmb [r1, r2] with
        | some t => [t]
        | none => [genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
                   genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]
      else
        [genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
         genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]) =
    sigF (if r1.child = r2.root then
        match genAnnotatedChainedTree E' z' α' lmb' [r1, r2] with
        | some t => [t]
        | none => [genAnnotatedRecordTree E' z' α' lmb' r1.root r1.child r1.axis r1.recordExp,
                   genAnnotatedRecordTree E' z' α' lmb' r2.root r2.child r2.axis r2.recordExp]
      else
        [genAnnotatedRecordTree E' z' α' lmb' r1.root r1.child r1.axis r1.recordExp,
         genAnnotatedRecordTree E' z' α' lmb' r2.root r2.child r2.axis r2.recordExp]) := by
  split
  · obtain ⟨t, ht⟩ := chainedTree_isSome E z α lmb r1 [r2]
    obtain ⟨t', ht'⟩ := chainedTree_isSome E' z' α' lmb' r1 [r2]
    have hc := chainedTree_sig E E' z z' α α' lmb lmb' [r1, r2]
    rw [ht, ht'] at hc
    simp only [Option.map_some, Option.some.injEq] at hc
    rw [ht, ht']
    simp [sigF, hc]
  · simp only [sigF, List.map_cons, List.map_nil]
    rw [recordTree_sig E E' z z' α α' lmb lmb', recordTree_sig E E' z z' α α' lmb lmb']

theorem rowMemForest_sig (E E' : Noun → ComputeTable.FP K) (z z' α α' lmb lmb' : K)
    (reqs : List MemRecordReq) :
    sigF (genRowMemForest E z α lmb reqs) = sigF (genRowMemForest E' z' α' lmb' reqs) := by
  match reqs with
  | [] => simp [genRowMemForest, sigF]
  | [r] =>
      simp only [genRowMemForest, sigF, List.map_cons, List.map_nil]
      rw [recordTree_sig E E' z z' α α' lmb lmb']
  | [r1, r2] =>
      simp only [genRowMemForest]
      exact pairForest_sig E E' z z' α α' lmb lmb' r1 r2
  | [r1, r2, r3] =>
      have e : ∀ (E : Noun → ComputeTable.FP K) (z α lmb : K),
          genRowMemForest E z α lmb [r1, r2, r3] =
            genRowMemForest E z α lmb [r1, r2] ++
              [genAnnotatedRecordTree E z α lmb r3.root r3.child r3.axis r3.recordExp] := by
        intro E z α lmb; simp [genRowMemForest]
      have hp := rowMemForest_sig E E' z z' α α' lmb lmb' [r1, r2]
      rw [e, e]
      simp only [sigF, List.map_append, List.map_cons, List.map_nil] at hp ⊢
      rw [hp, recordTree_sig E E' z z' α α' lmb lmb']
  | r1 :: r2 :: r3 :: r4 :: rest =>
      simp only [genRowMemForest, sigF, List.map_map]
      apply List.map_congr_left
      intro r _
      exact recordTree_sig E E' z z' α α' lmb lmb' r.root r.child r.axis r.recordExp
termination_by reqs.length

mutual
theorem fromTree_sig (E E' : Noun → ComputeTable.FP K) (z z' α α' lmb lmb' : K) :
    ∀ t, sigF (genMemForestFromTree E z α lmb t) = sigF (genMemForestFromTree E' z' α' lmb' t)
  | .node g cs => by
      have h1 := rowMemForest_sig E E' z z' α α' lmb lmb' (extractNodeReqs g)
      have h2 := fromList_sig E E' z z' α α' lmb lmb' cs
      simp only [sigF] at h1 h2 ⊢
      simp only [genMemForestFromTree, List.map_append, h1, h2]

theorem fromList_sig (E E' : Noun → ComputeTable.FP K) (z z' α α' lmb lmb' : K) :
    ∀ ts, sigF (genMemForestFromList E z α lmb ts) = sigF (genMemForestFromList E' z' α' lmb' ts)
  | [] => by simp [genMemForestFromList, sigF]
  | t :: ts => by
      have h1 := fromTree_sig E E' z z' α α' lmb lmb' t
      have h2 := fromList_sig E E' z z' α α' lmb lmb' ts
      simp only [sigF] at h1 h2 ⊢
      simp only [genMemForestFromList, List.map_append, h1, h2]
end

/-- **BFS form**: the BFS list of `(skel, stamp)` of the generated forest reads no coin. -/
theorem bfs_sig (E E' : Noun → ComputeTable.FP K) (z z' α α' lmb lmb' : K)
    (t : NTree (GenComputeRow K)) :
    (bfsForest (genMemForestFromTree E z α lmb t)).map (fun n => sig n.label) =
      (bfsForest (genMemForestFromTree E' z' α' lmb' t)).map (fun n => sig n.label) := by
  have h := fromTree_sig E E' z z' α α' lmb lmb' t
  have e : ∀ (l : List (NTree (GenMemoryRow K))),
      (bfsForest l).map (fun n => sig n.label) = (bfsForest (sigF l)).map NTree.label := by
    intro l
    rw [sigF, bfsForest_mapNTree, List.map_map]
    exact List.map_congr_left fun t _ => (mapNTree_label sig t).symm
  rw [e, e, h]

/-- Threading keeps `(skel, stamp)` row by row. -/
theorem thread_sig (inp : MemoryTable.Inputs K) :
    ∀ (acc : K) (gs : List (GenMemoryRow K)),
      (threadGenRows inp acc gs).map sig = gs.map sig
  | _, [] => rfl
  | acc, g :: gs => by
      rw [threadGenRows_cons, List.map_cons, List.map_cons, thread_sig inp _ gs]
      rfl

/-- **The committed forest**: BFS `(skel, stamp)` of `genMemoryForest z α λ inp t` is the
coin-free reference `genMemForestFromTree (encC 1) 1 1 0 (bfsAssign (airReorder t))`. -/
theorem genMemoryForest_bfs_sig (z α lmb : K) (inp : MemoryTable.Inputs K)
    (t : NTree (GenComputeRow K)) :
    (bfsForest (genMemoryForest z α lmb inp t)).map (fun n => sig n.label) =
      (bfsForest (genMemForestFromTree (encC (1 : K)) 1 1 0 (bfsAssign (airReorder t)))).map
        (fun n => sig n.label) := by
  have e : (bfsForest (genMemoryForest z α lmb inp t)).map (fun n => sig n.label) =
      ((bfsForest (genMemoryForest z α lmb inp t)).map NTree.label).map sig := by
    rw [List.map_map]; rfl
  rw [e]
  unfold genMemoryForest
  rw [threadGenForest_bfs_labels, thread_sig, List.map_map]
  exact bfs_sig _ _ _ _ _ _ _ _ _

end Nock.RedTeam.Batch1253


/-! P2: at ANY package, the route-B pair list of the canonical memory trace is
a function of three row data only — state, the honest atom, the honest `reqIdx`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1253

open Nock Nock.Walk Nock.Reified
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.PreSeedCensus

noncomputable section

/-- The route-B pair list read off a pre-`z` label map and a `reqIdx` map (`reqPairsOfEnvs`'s body). -/
def pairsOf {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] (q kroots M : ℕ)
    (lbl : ℕ → MState × F) (rq : ℕ → F) (T : MState → ℕ → Noun) : List (Noun × Noun) :=
  (List.range' 1 M).map fun i =>
    (decodePre K q (buildTF kroots (fun j => fanoutMem (lbl j).1) lbl M i),
      T (lbl i).1 (RecordCarrier.natLift (rq i)))

theorem reqPairsOfEnvs_eq_pairsOf {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (K : Type) [Field K] [Algebra F K] (q kroots : ℕ) {M : ℕ}
    (envs : Fin M → Env F) (hM : 0 < M) (T : MState → ℕ → Noun) :
    reqPairsOfEnvs K q kroots envs hM T =
      pairsOf K q kroots M (preLblOfEnvs envs hM) (preReqIdxOfEnvs envs hM) T := rfl

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Canonical state column (cols `0..2`). -/
theorem canon_state (i : Fin P.optimized.family.problem.cfg.memRows) :
    StrategyOfTraces.memoryStateOf (P.memoryBaseEnv (canonicalMemoryTrace P) i) =
      (P.optimized.family.problem.exec.memoryPubAt i).st := by
  have h := Nock.RedTeam.Batch959.memRowState_honest P i
  rw [← h]
  rfl

/-- Canonical atom column (`180`). -/
theorem canon_atom (i : Fin P.optimized.family.problem.cfg.memRows) :
    (P.memoryBaseEnv (canonicalMemoryTrace P) i).trace 180 =
      OptimizedMemoryCanonicalTrace.honestAtomOf (F := F)
        (P.optimized.family.problem.exec.memoryPubAt i) := by
  show (P.memoryBaseEnv (OptimizedCanonicalHostileLists.honestMemoryTrace P) i).trace 180 = _
  rw [OptimizedCanonicalHostileLists.canonical_memoryBaseEnv]
  exact OptimizedMemoryCanonicalSatisfaction.canonical_physical_atom _ _
    P.optimized.memoryNodes_injective _ _ _ _ i

/-- Canonical `reqIdx` column (`181`). -/
theorem canon_reqIdx (i : Fin P.optimized.family.problem.cfg.memRows) :
    (P.memoryBaseEnv (canonicalMemoryTrace P) i).trace 181 =
      OptimizedMemorySemanticRealization.honestReqIdx P.optimized.family i := by
  show (P.memoryBaseEnv (OptimizedCanonicalHostileLists.honestMemoryTrace P) i).trace 181 = _
  rw [OptimizedCanonicalHostileLists.canonical_memoryBaseEnv]
  exact OptimizedMemoryCanonicalSatisfaction.canonical_physical_reqIdx _ _
    P.optimized.memoryNodes_injective _ _ _ _ i

/-- **The pair list at any package, from row data.**  If the row data `(state, atom)` and `reqIdx`
of every canonical row agree with `f i` / `g i` (row `0` read out of range), the canonical pair list
is `pairsOf` of the two maps. -/
theorem canon_pairs_eq (kroots : ℕ) (T : MState → ℕ → Noun)
    (f : ℕ → MState × F) (g : ℕ → F)
    (hf : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      ((P.optimized.family.problem.exec.memoryPubAt i).st,
        OptimizedMemoryCanonicalTrace.honestAtomOf (F := F)
          (P.optimized.family.problem.exec.memoryPubAt i)) = f i)
    (hg : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      OptimizedMemorySemanticRealization.honestReqIdx P.optimized.family i = g i) :
    reqPairsOfEnvs K P.q kroots (P.memoryBaseEnv (canonicalMemoryTrace P))
        P.optimized.family.problem.cfg.memRows_pos T =
      pairsOf K P.q kroots P.optimized.family.problem.cfg.memRows
        (fun j => if j - 1 < P.optimized.family.problem.cfg.memRows then f (j - 1) else f 0)
        (fun j => if j - 1 < P.optimized.family.problem.cfg.memRows then g (j - 1) else g 0) T := by
  rw [reqPairsOfEnvs_eq_pairsOf]
  have hL : preLblOfEnvs (P.memoryBaseEnv (canonicalMemoryTrace P))
      P.optimized.family.problem.cfg.memRows_pos =
      (fun j => if j - 1 < P.optimized.family.problem.cfg.memRows then f (j - 1) else f 0) := by
    funext j
    unfold preLblOfEnvs preStateOfEnvs preAtomOfEnvs
    split_ifs with hj
    · rw [canon_state, OptimizedMemoryGateBasis.atomCol, canon_atom]
      exact hf ⟨j - 1, hj⟩
    · rw [canon_state, OptimizedMemoryGateBasis.atomCol, canon_atom]
      exact hf ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩
  have hR : preReqIdxOfEnvs (P.memoryBaseEnv (canonicalMemoryTrace P))
      P.optimized.family.problem.cfg.memRows_pos =
      (fun j => if j - 1 < P.optimized.family.problem.cfg.memRows then g (j - 1) else g 0) := by
    funext j
    unfold preReqIdxOfEnvs
    split_ifs with hj
    · rw [OptimizedMemoryGateBasis.reqIdxCol, canon_reqIdx]; exact hg ⟨j - 1, hj⟩
    · rw [OptimizedMemoryGateBasis.reqIdxCol, canon_reqIdx]
      exact hg ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩
  rw [hL, hR]

end

end Nock.RedTeam.Batch1253

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace Nock.RedTeam.Batch1253.AtGen
open Nock.RedTeam.Batch1253
open Nock.MemoryTable Nock.NockVMROM.Thm54.SemanticTimestampStrategy

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.Framework
open Nock.Framework.Thm54
open Module
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam.Batch906
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.RedTeam.Batch1061 (genPkg gen_honest_accepted)

noncomputable section
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.Reified
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

/-! ## The coin-free reference data -/

/-- The coin-free reference forest of the program (encoder `encC 1`, `z = α = 1`, `λ = 0`). -/
def refForest (t : NTree (GenComputeRow K)) : List (NTree (GenMemoryRow K)) :=
  genMemForestFromTree (encC (1 : K)) 1 1 0 (bfsAssign (airReorder t))

/-- BFS `(skel, stamp)` rows of the reference forest. -/
def rows0 (t : NTree (GenComputeRow K)) : List (MemoryRowSkeleton × MemoryTimestampRow) :=
  (bfsForest (refForest t)).map (fun n => sig n.label)

/-- The honest pre-seed atom a skeleton row names. -/
def atomF (F : Type) [Field F] (s : MemoryRowSkeleton) : F :=
  if h : s.state = .halt then ((s.haltAtom h : ℕ) : F) else 0

/-- Row `i`'s pre-`z` label `(state, atom)` from the reference rows. -/
def lbl0 (F : Type) [Field F] (t : NTree (GenComputeRow K)) (i : ℕ) : MState × F :=
  match (rows0 t)[i]? with
  | some r => (r.1.state, atomF F r.1)
  | none => (.halt, 0)

/-- Row `i`'s pre-`z` `reqIdx` from the reference rows. -/
def rq0 (F : Type) [Field F] (t : NTree (GenComputeRow K)) (i : ℕ) : F :=
  match (rows0 t)[i]? with
  | some r =>
      if r.1.state = .read_root ∨ r.1.state = .verify_child then (r.2.recordExponent : F) else 0
  | none => 0

/-- **The honest pair list, z-free.** -/
def honestPairs0 (F K : Type) [Field F] [Field K] [Algebra F K] (q : ℕ)
    (t : NTree (GenComputeRow K)) : List (Noun × Noun) :=
  pairsOf K q (refForest t).length (rows0 t).length
    (fun j => if j - 1 < (rows0 t).length then lbl0 F t (j - 1) else lbl0 F t 0)
    (fun j => if j - 1 < (rows0 t).length then rq0 F t (j - 1) else rq0 F t 0)
    (requestTargets (genComputeSemanticSkeleton (bfsAssign (airReorder t))))

section Generated
variable {q Λ : ℕ}
    {z α : K} {hz : z ≠ 0} {htwo : (2 : K) ≠ 0} {a b c : K}
    {chal : ChallengeVector K} {hinp : chal.computeInputs = ⟨α, z, a, b, c⟩}
    {hmi : chal.memoryInputs = memInputs z}
    {Ksz : ℕ} {orbit : OrbitDomain K} {horb : 1 ≤ orbit.h}
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    {h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)}
    {hseed : SeedGood z t}
    {hcoins : ComputeCoinsGeneric z α a b c (airReorder t)}
    {hΛ : 1 ≤ Λ} {hconf : TraceConfined Λ (airReorder t)}
    {hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length}
    {hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h}
    {hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h}
    {B : ℕ} {hB : B ≤ orderOf α}
    {hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B}
    {hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz}
    {hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz}
    {hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q}
    {hq : 11 < q} {hchar : q = ringChar K}
    {haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t))}
    {hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds}
    {hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))}
    {hKszChar : Ksz < ringChar K}
    {hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h}
    {hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h}
    {hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K}





set_option quotPrecheck false in
set_option hygiene false in
local notation "GP" => genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef
  hinterCard hhon hprl hmore hord hordM hrows

set_option quotPrecheck false in
set_option hygiene false in
local notation "EG" => genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
  hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
  haxis hbad hout hKszChar hprogCap hmemCap hfirst

set_option quotPrecheck false in
set_option hygiene false in
local notation "IG" => inputsOfCarrier (EG) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n
  hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon
variable
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    {fuelG : ℕ} {rG : Noun} (hG : FieldEmbedding.evalGBy q fuelG subject formula = some rG)
    (hF : GeneratedField.PrimeFieldElems F)

/-- The generated memory forest at the seed. -/
local notation "MF" => genMemoryForest z α chal.lam (memInputs z) t

theorem memRows_eq : (GP).optimized.family.problem.cfg.memRows = (rows0 t).length := by
  show (bfsForest (MF)).length = _
  have h := genMemoryForest_bfs_sig (K := K) z α chal.lam (memInputs z) t
  have := congrArg List.length h
  simpa [rows0, refForest] using this

theorem kMem_eq : (GP).optimized.family.problem.cfg.kMem = (refForest t).length := by
  show (MF).length = _
  have h := fromTree_sig (K := K) (encC z) (encC (1 : K)) z 1 α 1 chal.lam 0 (bfsAssign (airReorder t))
  have hl := congrArg List.length h
  simp only [sigF, List.length_map] at hl
  unfold genMemoryForest threadGenForest
  rw [zipBfs_length]
  exact hl

/-- The executed memory row at `i` is the row encode of BFS row `i` of the committed forest. -/
theorem pubAt_eq (i : Fin (GP).optimized.family.problem.cfg.memRows) :
    (GP).optimized.family.problem.exec.memoryPubAt i =
      (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow chal.lam
        ((bfsForest (MF))[(i : ℕ)]'i.isLt).label.row).2.2 := by
  have hmr : (GP).optimized.family.problem.exec.memoryRows =
      (bfsForest (MF)).map
        (fun nd => SemanticTimestampStrategy.MemoryRowTemplate.encodeRow chal.lam
          (GenMemoryRow.row nd.label)) :=
    genExactExecution_memoryRows _ _ _ _ _ _ _ _ _ _ _ _
  unfold ExactExecution.memoryPubAt ExactExecution.memoryRowAt
  simp only [List.get_eq_getElem, Fin.val_cast]
  have hlt : (i : ℕ) < (GP).optimized.family.problem.exec.memoryRows.length := by
    rw [ExactExecution.memoryRows_length]; exact i.isLt
  have h1 : (GP).optimized.family.problem.exec.memoryRows[(i : ℕ)]? =
      some (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow chal.lam
        ((bfsForest (MF))[(i : ℕ)]'i.isLt).label.row) := by
    rw [hmr, List.getElem?_map, List.getElem?_eq_getElem i.isLt]; rfl
  rw [List.getElem?_eq_getElem hlt] at h1
  rw [Option.some.inj h1]

include h in
/-- Every BFS row of the committed forest binds its skeleton (`MemoryNodesOK`). -/
theorem bind_row (nd : NTree (GenMemoryRow K)) (hn : nd ∈ bfsForest (MF)) :
    BindMemoryRowA z nd.label.skel nd.label.row := by
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ _).mp hn
  have hok := genThreadedMemoryNodesOK (lmb := chal.lam) z α (memInputs z) h u hu
  have := hok _ (Nock.RedTeam.Batch998.inTree_mapNTree_of GenMemoryRow.node hin)
  have hb := this.2.2.1
  rw [mapNTree_label] at hb
  exact hb

/-- BFS row `i`'s `(skel, stamp)` is reference row `i`. -/
theorem row_sig (i : ℕ) (hi : i < (bfsForest (MF)).length) :
    (rows0 t)[i]? = some (sig ((bfsForest (MF))[i]'hi).label) := by
  have h := genMemoryForest_bfs_sig (K := K) z α chal.lam (memInputs z) t
  unfold rows0 refForest
  rw [← h, List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

/-- **Row data, (state, atom).** -/
theorem hf_row (i : Fin (GP).optimized.family.problem.cfg.memRows) :
    (((GP).optimized.family.problem.exec.memoryPubAt i).st,
      OptimizedMemoryCanonicalTrace.honestAtomOf (F := F)
        ((GP).optimized.family.problem.exec.memoryPubAt i)) = lbl0 F t i := by
  have hi : (i : ℕ) < (bfsForest (MF)).length := i.isLt
  rw [pubAt_eq (hG := hG) (hF := hF)]
  unfold lbl0
  rw [row_sig (i : ℕ) hi]
  simp only [sig]
  generalize hnd : (bfsForest (MF))[(i : ℕ)]'hi = nd
  have hmem : nd ∈ bfsForest (MF) := hnd ▸ List.getElem_mem hi
  have hb := bind_row (h := h) nd hmem
  have hst : nd.label.row.2.2.st = nd.label.skel.state := hb.2.2.1
  have hpt : nd.label.row.2.2.pt.noun = GlobalCarryRecognizer.enc z nd.label.skel.parent := hb.2.2.2.1
  refine Prod.ext ?_ ?_
  · simp only [encodeRow_pub_st]; exact hst
  · simp only
    unfold OptimizedMemoryCanonicalTrace.honestAtomOf atomF
    simp only [encodeRow_pub_st, encodeRow_pub_pt]
    by_cases hh : nd.label.skel.state = .halt
    · have hpar := nd.label.skel.haltParent hh
      have hleaf : nd.label.row.2.2.pt.noun.leaf = ((nd.label.skel.haltAtom hh : ℕ) : K) := by
        rw [hpt, hpar, GlobalCarryRecognizer.enc_atom]; rfl
      have hex : nd.label.row.2.2.st = .halt ∧
          ∃ a : F, algebraMap F K a = nd.label.row.2.2.pt.noun.leaf :=
        ⟨hst.trans hh, ⟨((nd.label.skel.haltAtom hh : ℕ) : F), by rw [hleaf, map_natCast]⟩⟩
      rw [dif_pos hex, dif_pos hh]
      apply (algebraMap F K).injective
      rw [hex.2.choose_spec, hleaf, map_natCast]
    · have hne : ¬ (nd.label.row.2.2.st = .halt ∧
          ∃ a : F, algebraMap F K a = nd.label.row.2.2.pt.noun.leaf) :=
        fun hx => hh (hst ▸ hx.1)
      rw [dif_neg hne, dif_neg hh]


/-- Reference row `i` is also the unthreaded forest's BFS row `i`. -/
theorem row_sig_unthreaded (i : ℕ)
    (hi : i < (bfsForest (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))).length) :
    (rows0 t)[i]? = some (sig ((bfsForest (genMemForestFromTree (encC z) z α chal.lam
      (bfsAssign (airReorder t))))[i]'hi).label) := by
  have h := bfs_sig (K := K) (encC z) (encC (1 : K)) z 1 α 1 chal.lam 0 (bfsAssign (airReorder t))
  unfold rows0 refForest
  rw [← h, List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

include h hB hwin in
/-- **Row data, `reqIdx`.** -/
theorem hg_row (i : Fin (GP).optimized.family.problem.cfg.memRows) :
    OptimizedMemorySemanticRealization.honestReqIdx (GP).optimized.family i = rq0 F t i := by
  have hi : (i : ℕ) < (bfsForest (MF)).length := i.isLt
  have hlenU : (bfsForest (genMemForestFromTree (encC z) z α chal.lam
      (bfsAssign (airReorder t)))).length = (bfsForest (MF)).length := by
    have h1 := congrArg List.length (genMemoryForest_bfs_sig (K := K) z α chal.lam (memInputs z) t)
    have h2 := congrArg List.length (bfs_sig (K := K) (encC z) (encC (1 : K)) z 1 α 1 chal.lam 0
      (bfsAssign (airReorder t)))
    simp only [List.length_map] at h1 h2
    omega
  have hiU : (i : ℕ) < (bfsForest (genMemForestFromTree (encC z) z α chal.lam
      (bfsAssign (airReorder t)))).length := by omega
  have hst : ((GP).optimized.family.problem.exec.memoryPubAt i).st =
      (((bfsForest (MF))[(i : ℕ)]'hi).label.skel.state) := by
    rw [pubAt_eq (hG := hG) (hF := hF), encodeRow_pub_st]
    exact (bind_row (h := h) _ (List.getElem_mem hi)).2.2.1
  have hskel : ((bfsForest (MF))[(i : ℕ)]'hi).label.skel =
      ((bfsForest (genMemForestFromTree (encC z) z α chal.lam
        (bfsAssign (airReorder t))))[(i : ℕ)]'hiU).label.skel := by
    have e1 := row_sig (K := K) (z := z) (α := α) (chal := chal) (t := t) (i : ℕ) hi
    have e2 := row_sig_unthreaded (K := K) (z := z) (α := α) (chal := chal) (t := t) (i : ℕ) hiU
    rw [e1] at e2
    have := congrArg Prod.fst (Option.some.inj e2)
    simpa [sig] using this
  unfold rq0
  rw [row_sig_unthreaded (i : ℕ) hiU]
  simp only [sig]
  unfold OptimizedMemorySemanticRealization.honestReqIdx
  by_cases hlive : ((GP).optimized.family.problem.exec.memoryPubAt i).st = .read_root ∨
      ((GP).optimized.family.problem.exec.memoryPubAt i).st = .verify_child
  · have hhi : (i : ℕ) < (genTimestampSkeleton F (airReorder t)
        (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))
        (genComputeSkeleton_memForest_stampsWellFormed z α h)).memoryRows.length := by
      simp only [genTimestampSkeleton, genMemoryStamps, List.length_map]; exact hiU
    have hzc : chal.z = z := by
      have := congrArg ComputeTable.Inputs.z hinp
      simpa [ChallengeVector.computeInputs] using this
    have key := GenRecordExponentBridge.generated_reqIdxNat_eq_recordExponent
      (GP).optimized.sampled z α chal hzc Ksz orbit horb a b c h hmempos hcomp hmem
      (horb_of_window hB hwin) rfl rfl i hhi hlive
    rw [key]
    have hl' := hlive
    rw [hst, hskel] at hl'
    erw [if_pos hl']
    simp [genTimestampSkeleton, genMemoryStamps]
  · have hl' := hlive
    rw [hst, hskel] at hl'
    erw [if_neg hl']
    simp [OptimizedMemorySemanticRealization.reqIdxNat, hlive]


/-- The pinned targets are the z-free targets of the BFS-assigned compute tree. -/
theorem targets_eq :
    requestTargets (GP).strategy.skeleton =
      requestTargets (genComputeSemanticSkeleton (bfsAssign (airReorder t))) := by
  have hsk : (GP).strategy.skeleton =
      genSemanticSkeleton (bfsAssign (airReorder t)) (MF) :=
    genSkeletonOfNodes_eq (lmb := chal.lam) z α a b c (memInputs z) t
  rw [hsk]
  exact requestTargets_congr (computeSkeletonRows_genSemantic _ _)

include h hB hwin in
/-- **z-irrelevance of the honest pairs.**  The route-B pair list of the canonical memory trace at
the generated package is the z-free list `honestPairs0 F K q t`. -/
theorem reqPairs_eq_honestPairs0 :
    reqPairsOfEnvs K (GP).q (GP).optimized.family.problem.cfg.kMem
        ((GP).memoryBaseEnv (canonicalMemoryTrace (GP)))
        (GP).optimized.family.problem.cfg.memRows_pos
        (requestTargets (GP).strategy.skeleton) =
      honestPairs0 F K q t := by
  rw [canon_pairs_eq (GP) _ _ (lbl0 F t) (rq0 F t) (hf_row (h := h) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows (hG := hG) (hF := hF))
    (hg_row (h := h) (hB := hB) (hwin := hwin) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows (hG := hG) (hF := hF)), targets_eq (hG := hG) (hF := hF)]
  unfold honestPairs0
  rw [kMem_eq (hG := hG) (hF := hF), memRows_eq (hG := hG) (hF := hF)]
  rfl

include h hB hwin in
/-- **`hpair` from a z-free seed condition.** -/
theorem hpair_of_seed
    (hzp : z ∉ pairBadSeeds (K := K) ((rows0 t).length ⊔ Λ) (honestPairs0 F K q t)) :
    (GP).honestTuple.1 ∉ PreSeedCensus.reqPairEventOfEnvs K (GP).q
      (GP).optimized.family.problem.cfg.kMem
      ((GP).optimized.family.problem.cfg.memRows ⊔ (GP).optimized.Λ)
      ((GP).memoryBaseEnv (canonicalMemoryTrace (GP))) (GP).optimized.family.problem.cfg.memRows_pos
      (PreSeedCensus.requestTargets (GP).strategy.skeleton) := by
  unfold reqPairEventOfEnvs
  rw [reqPairs_eq_honestPairs0 (h := h) (hB := hB) (hwin := hwin) (hG := hG) (hF := hF), mem_liftSeed_iff, memRows_eq (hG := hG) (hF := hF)]
  have hzc : chal.z = z := by
    have := congrArg ComputeTable.Inputs.z hinp
    simpa [ChallengeVector.computeInputs] using this
  show chal.z ∉ _
  rw [hzc]
  exact hzp


end Generated
end
end Nock.RedTeam.Batch1253.AtGen

/-! ## The widened seed (route (b)): the joint seed also avoids an extra z-free bad set -/

namespace Nock.RedTeam.Batch1253.Seed

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.GoodSeed
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.RedTeam.Batch1253
open Nock.RedTeam.Batch1253.AtGen

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {lmb : K}

/-- **`GenSeedVcomp.exists_vcomp_seed_of_accepted` with one extra bad set `X`**, priced into the
budget. -/
theorem exists_vcomp_seed_avoiding {q Λ : ℕ} (hq : 1 < q) (hle : q ≤ ringChar K)
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder t))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (X : Finset K)
    (hcard : seedBudgetVcomp Λ (bfsForest [bfsAssign (airReorder t)]).length + X.card
        < Fintype.card K) :
    ∃ z : K, z ≠ 0
      ∧ z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
              (genMemoryForest z α lmb (memInputs z) t)).census.badSeeds
      ∧ z ∉ sizeWindowFailureSeeds (K := K)
              (genSemanticSkeleton (bfsAssign (airReorder t))
                (genMemoryForest z α lmb (memInputs z) t))
      ∧ SeedGood z t
      ∧ z ∉ X := by
  let rows := (bfsForest [bfsAssign (airReorder t)]).length
  let Cempty := genSkeletonP8Census (K := K) hΛ h hconf
    ([] : List (NTree (GenMemoryRow K)))
  let Sempty := genSemanticSkeleton (bfsAssign (airReorder t))
    ([] : List (NTree (GenMemoryRow K)))
  let KM : Finset K :=
    (({0} : Finset K) ∪ Cempty.census.badSeeds (K := K)) ∪
      sizeWindowFailureSeeds (K := K) Sempty
  let D : Finset K :=
    Finset.univ.filter (fun z : K => ∃ g ∈ bfsRows (airReorder t), ¬ RowSeedGood z g)
  have hrows : (bfsRows (airReorder t)).length = rows := by
    unfold rows
    rw [bfsRows_length, bfsForest_bfsAssign_length]
  have hKMcard : KM.card ≤ seedBudget Λ rows := by
    have h1 : (({0} : Finset K) ∪ Cempty.census.badSeeds (K := K)).card
        ≤ 1 + (3 + 10 * (computeSkeletonRows Sempty).length) * (2 * Λ - 1) := by
      refine (Finset.card_union_le _ _).trans ?_
      have hcen := (Cempty.census.badSeeds_card_le (K := K)).trans
        (Nat.mul_le_mul_right (2 * Λ - 1) Cempty.count_le)
      simpa using Nat.add_le_add_left hcen 1
    have hlen : (computeSkeletonRows Sempty).length = rows := by
      unfold rows
      rw [computeSkeletonRows_length]
    rw [hlen] at h1
    refine (Finset.card_union_le _ _).trans ?_
    exact Nat.add_le_add h1 (sizeWindowFailureSeeds_card_le Sempty Λ hwin)
  have hDcard : D.card ≤ rows * (3 * (2 * Λ - 1)) := by
    have := seedBad_card_le_of_generated hq hle hs hf hG h hΛ hconf
    rwa [hrows] at this
  have hunion : ((KM ∪ D) ∪ X).card < Fintype.card K := by
    refine lt_of_le_of_lt ?_ hcard
    refine (Finset.card_union_le _ X).trans ?_
    refine Nat.add_le_add_right ?_ _
    refine (Finset.card_union_le KM D).trans ?_
    have : rows * (3 * (2 * Λ - 1)) = 3 * rows * (2 * Λ - 1) := by ring
    rw [this] at hDcard
    exact Nat.add_le_add hKMcard hDcard
  obtain ⟨z, hz⟩ := exists_notMem_of_card_lt hunion
  have hzKMD : z ∉ KM ∪ D := fun h => hz (Finset.mem_union_left X h)
  have hzX : z ∉ X := fun h => hz (Finset.mem_union_right _ h)
  have hzKM : z ∉ KM := fun h => hzKMD (Finset.mem_union_left D h)
  have hzD : z ∉ D := fun h => hzKMD (Finset.mem_union_right KM h)
  have hz01 : z ∉ ({0} : Finset K) ∪ Cempty.census.badSeeds (K := K) :=
    fun h => hzKM (Finset.mem_union_left _ h)
  have hzWin : z ∉ sizeWindowFailureSeeds (K := K) Sempty :=
    fun h => hzKM (Finset.mem_union_right _ h)
  have hz0 : z ≠ 0 :=
    fun h => hz01 (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have hzbad : z ∉ Cempty.census.badSeeds (K := K) :=
    fun h => hz01 (Finset.mem_union_right _ h)
  refine ⟨z, hz0, ?_, ?_, ?_, hzX⟩
  · rw [badSeeds_memoryForest_irrelevant
      (genSkeletonP8Census (K := K) hΛ h hconf (genMemoryForest z α lmb (memInputs z) t))
      Cempty]
    exact hzbad
  · rw [sizeWindowFailureSeeds_memoryForest_irrelevant (bfsAssign (airReorder t))
      (genMemoryForest z α lmb (memInputs z) t) ([] : List (NTree (GenMemoryRow K)))]
    exact hzWin
  · exact seedGood_raw_of_airReorder
      (seedGood_airReorder_of_not_mem z t hzD)

/-- The z-free pair bad set of a program at window `Λ`. -/
noncomputable def pairBad (F : Type) [Field F] [Algebra F K] (q Λ : ℕ)
    (t : NTree (GenComputeRow K)) : Finset K :=
  pairBadSeeds (K := K) ((rows0 t).length ⊔ Λ) (honestPairs0 F K q t)

theorem honestPairs0_length (F : Type) [Field F] [Algebra F K] (q : ℕ)
    (t : NTree (GenComputeRow K)) : (honestPairs0 F K q t).length = (rows0 t).length := by
  simp [honestPairs0, pairsOf]

/-- **Card of the pair bad set**: `M₀·(2(M₀ ⊔ Λ) − 1)`, `M₀` the program's memory row count. -/
theorem pairBad_card_le (F : Type) [Field F] [Algebra F K] (q Λ : ℕ)
    (t : NTree (GenComputeRow K)) :
    (pairBad F q Λ t).card ≤ (rows0 t).length * (2 * ((rows0 t).length ⊔ Λ) - 1) := by
  have := pairBadSeeds_card_le (K := K) ((rows0 t).length ⊔ Λ) (honestPairs0 F K q t)
  rwa [honestPairs0_length] at this

/-- **The widened seed exists** under the one-pair budget `seedBudgetPairB`
. -/
theorem exists_vcomp_pair_seed (F : Type) [Field F] [Algebra F K] {q Λ : ℕ} (hq : 1 < q)
    (hle : q ≤ ringChar K)
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder t))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : Nock.RedTeam.Batch1251.seedBudgetPairB Λ (bfsForest [bfsAssign (airReorder t)]).length
        (rows0 t).length < Fintype.card K) :
    ∃ z : K, z ≠ 0
      ∧ z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
              (genMemoryForest z α lmb (memInputs z) t)).census.badSeeds
      ∧ z ∉ sizeWindowFailureSeeds (K := K)
              (genSemanticSkeleton (bfsAssign (airReorder t))
                (genMemoryForest z α lmb (memInputs z) t))
      ∧ SeedGood z t
      ∧ z ∉ pairBadSeeds (K := K) ((rows0 t).length ⊔ Λ) (honestPairs0 F K q t) := by
  refine exists_vcomp_seed_avoiding hq hle hs hf hG h hΛ hconf α hwin (pairBad F q Λ t) ?_
  refine lt_of_le_of_lt ?_ hcard
  unfold Nock.RedTeam.Batch1251.seedBudgetPairB
  exact Nat.add_le_add_left (pairBad_card_le F q Λ t) _

/-- **`romSeedPair`**: the compiler's seed, jointly avoiding the `KM` union, the Dyck-bad set and
the z-free honest pair bad set.  `Classical.choose`. -/
noncomputable def romSeedPair (F : Type) [Field F] [Algebra F K] {q Λ : ℕ} (hq : 1 < q)
    (hle : q ≤ ringChar K)
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder t))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : Nock.RedTeam.Batch1251.seedBudgetPairB Λ (bfsForest [bfsAssign (airReorder t)]).length
        (rows0 t).length < Fintype.card K) : K :=
  (exists_vcomp_pair_seed (lmb := (0 : K)) F hq hle hs hf hG h hΛ hconf α hwin hcard).choose

section Spec
variable (F : Type) [Field F] [Algebra F K] {q Λ : ℕ} (hq : 1 < q) (hle : q ≤ ringChar K)
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder t))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : Nock.RedTeam.Batch1251.seedBudgetPairB Λ (bfsForest [bfsAssign (airReorder t)]).length
        (rows0 t).length < Fintype.card K)

theorem romSeedPair_ne_zero : romSeedPair F hq hle hs hf hG h hΛ hconf α hwin hcard ≠ 0 :=
  (exists_vcomp_pair_seed (lmb := (0 : K)) F hq hle hs hf hG h hΛ hconf α hwin hcard).choose_spec.1

/-- The census set at every `λ` (the census reads only the compute tree). -/
theorem romSeedPair_notMem_badSeeds (lmb' : K) :
    romSeedPair F hq hle hs hf hG h hΛ hconf α hwin hcard ∉
      (genSkeletonP8Census (K := K) hΛ h hconf
        (genMemoryForest (romSeedPair F hq hle hs hf hG h hΛ hconf α hwin hcard) α lmb'
          (memInputs (romSeedPair F hq hle hs hf hG h hΛ hconf α hwin hcard)) t)).census.badSeeds := by
  rw [badSeeds_memoryForest_irrelevant _
    (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest (romSeedPair F hq hle hs hf hG h hΛ hconf α hwin hcard) α (0 : K)
        (memInputs (romSeedPair F hq hle hs hf hG h hΛ hconf α hwin hcard)) t))]
  exact (exists_vcomp_pair_seed (lmb := (0 : K)) F hq hle hs hf hG h hΛ hconf α hwin
    hcard).choose_spec.2.1

theorem romSeedPair_notMem_sizeWindowFailureSeeds (lmb' : K) :
    romSeedPair F hq hle hs hf hG h hΛ hconf α hwin hcard ∉
      sizeWindowFailureSeeds (K := K)
        (genSemanticSkeleton (bfsAssign (airReorder t))
          (genMemoryForest (romSeedPair F hq hle hs hf hG h hΛ hconf α hwin hcard) α lmb'
            (memInputs (romSeedPair F hq hle hs hf hG h hΛ hconf α hwin hcard)) t)) := by
  rw [sizeWindowFailureSeeds_memoryForest_irrelevant _ _
    (genMemoryForest (romSeedPair F hq hle hs hf hG h hΛ hconf α hwin hcard) α (0 : K)
      (memInputs (romSeedPair F hq hle hs hf hG h hΛ hconf α hwin hcard)) t)]
  exact (exists_vcomp_pair_seed (lmb := (0 : K)) F hq hle hs hf hG h hΛ hconf α hwin
    hcard).choose_spec.2.2.1

theorem romSeedPair_seedGood : SeedGood (romSeedPair F hq hle hs hf hG h hΛ hconf α hwin hcard) t :=
  (exists_vcomp_pair_seed (lmb := (0 : K)) F hq hle hs hf hG h hΛ hconf α hwin
    hcard).choose_spec.2.2.2.1

/-- The pair half: the chosen seed avoids the z-free honest pair bad set. -/
theorem romSeedPair_notMem_pairBad :
    romSeedPair F hq hle hs hf hG h hΛ hconf α hwin hcard ∉
      pairBadSeeds (K := K) ((rows0 t).length ⊔ Λ) (honestPairs0 F K q t) :=
  (exists_vcomp_pair_seed (lmb := (0 : K)) F hq hle hs hf hG h hΛ hconf α hwin
    hcard).choose_spec.2.2.2.2

end Spec

/-! ## The arithmetic: `hp`'s numeral `25` is unmoved -/

/-- The widened budget is below `p³` at every `p ≥ 25` given the §1 bounds (`rows, Λ < p`) and the
`hF` export `3·M₀ ≤ p − 1` (`Batch1251.threeM_le_of_hF`). -/
theorem pairBudget_lt_pow {Λ rows M p : ℕ} (hrows : rows < p) (hΛp : Λ < p)
    (hM : 3 * M ≤ p - 1) (hp : 25 ≤ p) :
    Nock.RedTeam.Batch1251.seedBudgetPairB Λ rows M < p ^ 3 :=
  Nock.RedTeam.Batch1251.seedBudgetPairB_lt_pow hrows hΛp hM hp

end Nock.RedTeam.Batch1253.Seed

#print axioms Nock.RedTeam.Batch1253.AtGen.reqPairs_eq_honestPairs0
#print axioms Nock.RedTeam.Batch1253.AtGen.hpair_of_seed
#print axioms Nock.RedTeam.Batch1253.Seed.exists_vcomp_seed_avoiding
#print axioms Nock.RedTeam.Batch1253.Seed.exists_vcomp_pair_seed
#print axioms Nock.RedTeam.Batch1253.Seed.romSeedPair_notMem_pairBad
#print axioms Nock.RedTeam.Batch1253.Seed.romSeedPair_seedGood
#print axioms Nock.RedTeam.Batch1253.Seed.romSeedPair_notMem_badSeeds
#print axioms Nock.RedTeam.Batch1253.Seed.romSeedPair_notMem_sizeWindowFailureSeeds
#print axioms Nock.RedTeam.Batch1253.Seed.pairBudget_lt_pow
