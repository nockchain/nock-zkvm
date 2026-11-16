/-
  Nock/NockVMROM/Thm54/TraceGen/GenServedForest.lean

  **What the generated memory forest's roots are.**

  `GenServedRootTrace` builds a `RootTrace` from *one* forest root of a known shape.  Nothing yet
  said that a generated forest's roots have those shapes.  This module says it: every root of
  `genMemForestFromTree` is either a one-record tree or a two-record chain, for requests of one
  compute node (`RootShape`), and the requests are the node's own extracted requests.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenServedRootTrace

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## A. The two shapes a generated forest root can have -/

/-- One root of `genRowMemForest`: a single-record tree, or a two-record chain.

The chain disjunct carries `r1.recordExp ≠ r2.recordExp`.  `ET` §2 recorded that membership alone
was enough for `roots` and not for `timestampPowersNodup`; in fact `rootTraceOfChainedPair` needs it
too, as its `hne` argument, and nothing recovers it from the tree — `genAnnotatedChainedTree` has no
guard and returns `some` for any non-empty request list, and an axis-`1` request has
`slot 1 root = some root`, so `r1 = r2` is not excluded structurally.  The row's own exponents being
distinct is what excludes it, which is why the classification below takes that as a hypothesis.

`timestampExp α ·` is a choice on the *field value*
(`AxisSoundness.lean:50`), so at `α = 1` — or any `α` with `α ^ 2 = 1` — the two sides of `hne` are
literally the same term however far apart the exponents are.  The missing half is the
orbit-capacity premise `e < orderOf α`; `roots` carries it as a stated hypothesis
(`GenServedRoots.lean` §C, `timestampExp_pow_ne_of_lt_orderOf`).  Do not read this disjunct as
supplying `hne` on its own. -/
def RootShape (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (reqs : List MemRecordReq) (u : NTree (GenMemoryRow K)) : Prop :=
  (∃ r ∈ reqs, u = genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) ∨
    (∃ r1 ∈ reqs, ∃ r2 ∈ reqs, r1.child = r2.root ∧
      r1.recordExp ≠ r2.recordExp ∧
      genAnnotatedChainedTree E z α lmb [r1, r2] = some u)

theorem RootShape.mono {E : Noun → ComputeTable.FP K} {z α : K}
    {reqs reqs' : List MemRecordReq} {u : NTree (GenMemoryRow K)}
    (hsub : reqs ⊆ reqs') (h : RootShape E z α lmb reqs u) :
    RootShape E z α lmb reqs' u := by
  rcases h with ⟨r, hr, hu⟩ | ⟨r1, h1, r2, h2, hlink, hne, hu⟩
  · exact Or.inl ⟨r, hsub hr, hu⟩
  · exact Or.inr ⟨r1, hsub h1, r2, hsub h2, hlink, hne, hu⟩

/-- The two-request block of `genRowMemForest`, isolated: it is the same in the `[r1, r2]` and
`[r1, r2, r3]` arms. -/
private theorem rootShape_pair (E : Noun → ComputeTable.FP K) (z α : K)
    (r1 r2 : MemRecordReq) (reqs : List MemRecordReq)
    (h1 : r1 ∈ reqs) (h2 : r2 ∈ reqs) (hne : r1.recordExp ≠ r2.recordExp)
    (u : NTree (GenMemoryRow K))
    (hu : u ∈ (if r1.child = r2.root then
        match genAnnotatedChainedTree E z α lmb [r1, r2] with
        | some t => [t]
        | none => [genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
                   genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]
      else
        [genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
         genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp])) :
    RootShape E z α lmb reqs u := by
  by_cases hlink : r1.child = r2.root
  · rw [if_pos hlink] at hu
    cases hc : genAnnotatedChainedTree E z α lmb [r1, r2] with
    | none =>
        rw [hc] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact Or.inl ⟨r1, h1, rfl⟩
        · exact Or.inl ⟨r2, h2, rfl⟩
    | some tr =>
        rw [hc] at hu
        simp only [List.mem_singleton] at hu
        subst hu
        exact Or.inr ⟨r1, h1, r2, h2, hlink, hne, hc⟩
  · rw [if_neg hlink] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact Or.inl ⟨r1, h1, rfl⟩
    · exact Or.inl ⟨r2, h2, rfl⟩

/-- **Every root of one compute row's memory forest has one of the two shapes.** -/
theorem rootShape_genRowMemForest (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ (reqs : List MemRecordReq),
      (reqs.map MemRecordReq.recordExp).Nodup →
      ∀ u : NTree (GenMemoryRow K),
      u ∈ genRowMemForest E z α lmb reqs → RootShape E z α lmb reqs u := by
  intro reqs
  match reqs with
  | [] => intro _ u hu; simp [genRowMemForest] at hu
  | [r] =>
      intro _ u hu
      simp only [genRowMemForest, List.mem_singleton] at hu
      exact Or.inl ⟨r, by simp, hu⟩
  | [r1, r2] =>
      intro hnd u hu
      have hne : r1.recordExp ≠ r2.recordExp := by
        rw [List.map_cons, List.map_cons, List.nodup_cons] at hnd
        intro heq
        exact hnd.1 (by simp [heq])
      exact rootShape_pair E z α r1 r2 _ (by simp) (by simp) hne u hu
  | [r1, r2, r3] =>
      intro hnd u hu
      have hne : r1.recordExp ≠ r2.recordExp := by
        rw [List.map_cons, List.map_cons, List.nodup_cons] at hnd
        intro heq
        exact hnd.1 (by simp [heq])
      simp only [genRowMemForest, List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact rootShape_pair E z α r1 r2 _ (by simp) (by simp) hne u hu
      · exact Or.inl ⟨r3, by simp, rfl⟩
  | r1 :: r2 :: r3 :: r4 :: rest =>
      intro _ u hu
      simp only [genRowMemForest, List.mem_map] at hu
      obtain ⟨r, hr, hu⟩ := hu
      exact Or.inl ⟨r, hr, hu.symm⟩

/-! ## B. Every root of the whole generated forest belongs to one compute node -/

/-- Row-level exponent distinctness at every node of a compute tree — the hypothesis the chain
disjunct needs.  Supplied for a generated program by `genForestRecordExps_nodup`. -/
def NodeExpsNodup (t : NTree (GenComputeRow K)) : Prop :=
  ∀ n, InTree t n → ((extractNodeReqs n.label).map MemRecordReq.recordExp).Nodup

theorem NodeExpsNodup.here {t : NTree (GenComputeRow K)} (h : NodeExpsNodup t) :
    ((extractNodeReqs t.label).map MemRecordReq.recordExp).Nodup :=
  h t (InTree.here _)

theorem NodeExpsNodup.child {t c : NTree (GenComputeRow K)} (h : NodeExpsNodup t)
    (hc : c ∈ t.children) : NodeExpsNodup c :=
  fun n hn => h n (InTree.sub hc hn)

mutual
theorem rootShape_genMemForestFromTree (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ (t : NTree (GenComputeRow K)), NodeExpsNodup t →
      ∀ u : NTree (GenMemoryRow K),
      u ∈ genMemForestFromTree E z α lmb t →
      ∃ n, InTree t n ∧ RootShape E z α lmb (extractNodeReqs n.label) u
  | .node g cs, hnd, u, hu => by
      rw [genMemForestFromTree, List.mem_append] at hu
      rcases hu with hu | hu
      · exact ⟨.node g cs, InTree.here _,
          rootShape_genRowMemForest E z α (extractNodeReqs g) hnd.here u hu⟩
      · obtain ⟨c, hc, n, hn, hs⟩ :=
          rootShape_genMemForestFromList E z α cs
            (fun c hc => hnd.child (by simpa using hc)) u hu
        exact ⟨n, InTree.sub (by simpa using hc) hn, hs⟩

theorem rootShape_genMemForestFromList (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ (cs : List (NTree (GenComputeRow K))), (∀ c ∈ cs, NodeExpsNodup c) →
      ∀ u : NTree (GenMemoryRow K),
      u ∈ genMemForestFromList E z α lmb cs →
      ∃ c ∈ cs, ∃ n, InTree c n ∧ RootShape E z α lmb (extractNodeReqs n.label) u
  | [], _, u, hu => by simp [genMemForestFromList] at hu
  | c :: cs, hnd, u, hu => by
      rw [genMemForestFromList, List.mem_append] at hu
      rcases hu with hu | hu
      · obtain ⟨n, hn, hs⟩ :=
          rootShape_genMemForestFromTree E z α c (hnd c (by simp)) u hu
        exact ⟨c, by simp, n, hn, hs⟩
      · obtain ⟨c', hc', n, hn, hs⟩ :=
          rootShape_genMemForestFromList E z α cs
            (fun d hd => hnd d (by simp [hd])) u hu
        exact ⟨c', by simp [hc'], n, hn, hs⟩
end

end Nock.NockVMROM.Thm54.TraceGen
