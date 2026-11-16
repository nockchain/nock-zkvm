/-
  Nock/NockVMROM/Thm54/TraceGen/GenChainedServedGen.lean

  **§D — the chained root's served records, unconditionally.**

  `FB`'s `genMemForest_recordExps_nodup` and `genMemForest_timestampPowers_nodup`
  (`GenMemForestOrder.lean:270`) take two readout hypotheses, `h1` for a one-record root and `h2`
  for a chained pair, **universally quantified over the requests**.

  **The obstruction is packaging, not mathematics.**  Reading `chainInner_pair_props`' proof, its
  `servedGen` conclusion uses only `servedGen_singleton_node`,
  `responseRecords_eq_singleton_of_read_root`, `responseRecords_of_ne_read`,
  `servedGen_descentCont` — which is `∀ remaining current` with **no slot hypothesis**
  (`GenServedRootTrace.lean:655`) — and `servedGen_no_read`.  `hslot`/`hne` are consumed by the
  `VerifyRoute` and `ServiceWalk` components, not by this one.  So the chained equation is provable
  outright, and this module proves it that way rather than by refactoring the bundle.

  With `genAnnotatedChainedTree_pair_servedGen` here and `genAnnotatedRecordTree_servedGen`
  (`GenServedRootTrace.lean:317`, already unconditional), `rd u := (servedGen [u]).map (·.ts)`
  satisfies both `h1` and `h2` **as stated**, so `FB`'s two theorems need no signature change.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenServedRoots

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## A. A verify subtree serves nothing -/

/-- The verify leaf of a record has no `read_root` row, so it contributes no served record. -/
theorem servedGen_genAnnotatedVerify (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (e : ℕ) :
    servedGen [(genAnnotatedVerify E z lmb root child ax ts e).1] = [] := by
  refine servedGen_no_read _ ?_ ?_
  · rw [forestFibre_cons, forestFibre_nil, genAnnotatedVerify_fibre_read]
  · exact genAnnotatedVerify_bfs_ver_false E z root child ax ts e

/-- A descent over a continuation that serves nothing serves nothing. -/
theorem servedGen_descent_of_nil (E : Noun → ComputeTable.FP K) (z : K)
    (c : NTree (GenMemoryRow K)) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) (hc : servedGen [c] = [])
    (current : Noun) (remaining : ℕ)
    {u : NTree (GenMemoryRow K)}
    (hu : u ∈ (genAnnotatedDescentCont E z lmb [c] contCell contState current remaining).1) :
    servedGen [u] = [] := by
  rw [servedGen_descentCont E z c contCell contState remaining current u hu, hc]

/-! ## B. The inner node of a two-request chain -/

/-- **The inner continuation of a `[r₁, r₂]` chain serves exactly `r₂`'s record.**

The inner node is `read_root` for `r₂` over a `verify_child` for `r₁`, whose own descent ends in
`r₂`'s verify leaf.  One record comes off the top; the rest of the subtree is silent. -/
theorem servedGen_chainedInner_pair (E : Noun → ComputeTable.FP K) (z α : K)
    (r1 r2 : MemRecordReq) :
    servedGen (genAnnotatedChainedInner E z α lmb r1 [r2]).1 =
      [⟨E r2.root, E r2.child, (r2.axis : K), α ^ r2.recordExp⟩] := by
  have hcont : (genAnnotatedChainedInner E z α lmb r2 []).1 =
      [(genAnnotatedVerify E z lmb r2.root r2.child r2.axis (α ^ r2.recordExp) r2.recordExp).1] := by
    rw [genAnnotatedChainedInner_nil]
  obtain ⟨d2, hd2⟩ := List.length_eq_one_iff.mp
    (genAnnotatedDescentCont_length_one (lmb := lmb) E z
      (genAnnotatedChainedInner E z α lmb r2 []).1
      (genAnnotatedChainedInner E z α lmb r2 []).2
      (chainedInnerRootState ([] : List MemRecordReq))
      (by rw [hcont]; rfl) r2.root r2.axis)
  have hserved2 : servedGen [d2] = [] := by
    have hstep := servedGen_descentCont E z
      (genAnnotatedVerify E z lmb r2.root r2.child r2.axis (α ^ r2.recordExp) r2.recordExp).1
      (genAnnotatedChainedInner E z α lmb r2 []).2
      (chainedInnerRootState ([] : List MemRecordReq)) r2.axis r2.root d2 (by
        rw [← hcont, hd2]; exact List.mem_singleton_self d2)
    rw [hstep, servedGen_genAnnotatedVerify]
  rw [genAnnotatedChainedInner, servedGen_singleton_node, servedGen_singleton_node,
    responseRecords_eq_singleton_of_read_root _ (by rw [gMemRow9_st, annotatedReadPub_st])
      (by rw [gMemRow9_ver, annotatedReadPub_ver]),
    responseRecords_of_ne_read _ (by rw [gMemRow9_st, annotatedVerifyPub_st]; decide)
      (by rw [gMemRow9_ver, annotatedVerifyPub_ver]),
    gMemRow9_mem, annotatedReadPub_mem, List.nil_append, hd2, hserved2, List.append_nil]

/-! ## C. `h2`, unconditional -/

/-- **The two-request chain serves exactly its two records, in order.**

No `hslot`, no `hne`, no `services` — the readout is structural.  With
`genAnnotatedRecordTree_servedGen` this is the pair `h1`/`h2` of
`genMemForest_recordExps_nodup` / `_timestampPowers_nodup` for
`rd u := (servedGen [u]).map (·.ts)`, so those two theorems need no signature change. -/
theorem genAnnotatedChainedTree_pair_servedGen (E : Noun → ComputeTable.FP K) (z α : K)
    (r1 r2 : MemRecordReq) {t : NTree (GenMemoryRow K)}
    (ht : genAnnotatedChainedTree E z α lmb [r1, r2] = some t) :
    servedGen [t] =
      [⟨E r1.root, E r1.child, (r1.axis : K), α ^ r1.recordExp⟩,
       ⟨E r2.root, E r2.child, (r2.axis : K), α ^ r2.recordExp⟩] := by
  have hteq := Option.some.inj ((genAnnotatedChainedTree_pair E z α r1 r2).symm.trans ht)
  subst hteq
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp
    (show (genAnnotatedChainedInner E z α lmb r1 [r2]).1.length = 1 from by
      rw [genAnnotatedChainedInner]; rfl)
  have hcserved : servedGen [c] =
      [⟨E r2.root, E r2.child, (r2.axis : K), α ^ r2.recordExp⟩] := by
    rw [← hc]; exact servedGen_chainedInner_pair E z α r1 r2
  obtain ⟨d, hd⟩ := List.length_eq_one_iff.mp
    (genAnnotatedDescentCont_length_one (lmb := lmb) E z
      (genAnnotatedChainedInner E z α lmb r1 [r2]).1
      (genAnnotatedChainedInner E z α lmb r1 [r2]).2
      (chainedInnerRootState [r2]) (by rw [genAnnotatedChainedInner]; rfl) r1.root r1.axis)
  have hdserved : servedGen [d] =
      [⟨E r2.root, E r2.child, (r2.axis : K), α ^ r2.recordExp⟩] := by
    refine Eq.trans ?_ hcserved
    refine servedGen_descentCont (lmb := lmb) E z c (genAnnotatedChainedInner E z α lmb r1 [r2]).2
      (chainedInnerRootState [r2]) r1.axis r1.root d ?_
    rw [← hc, hd]
    exact List.mem_singleton_self d
  rw [servedGen_singleton_node,
    responseRecords_eq_singleton_of_read_root _ (by rw [gMemRow9_st, annotatedReadPub_st])
      (by rw [gMemRow9_ver, annotatedReadPub_ver]),
    gMemRow9_mem, annotatedReadPub_mem, hd, hdserved]
  rfl

/-! ## D. `FB`'s two `nodup` theorems, instantiated

`rd u := (servedGen [u]).map (·.ts)` is a total function of the tree, and §A–§C plus
`genAnnotatedRecordTree_servedGen` supply `h1` and `h2` **as `FB` states them** — universally
quantified over the requests, no slot condition, no services.  So neither `FB` lemma needs its
signature weakened, which is what `FH`'s and `FU`'s §D plans both assumed would be necessary. -/

/-- The readout: a root's served records, keyed by timestamp. -/
def servedTs (u : NTree (GenMemoryRow K)) : List K :=
  (servedGen [u]).map (fun r => r.ts)

/-- `h1` for `servedTs`: a one-record root reads back its own timestamp. -/
theorem servedTs_recordTree (E : Noun → ComputeTable.FP K) (z α : K) (r : MemRecordReq) :
    servedTs (genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp)
      = [α ^ r.recordExp] := by
  rw [servedTs, genAnnotatedRecordTree_servedGen]
  rfl

/-- `h2` for `servedTs`: a chained pair reads back both timestamps, in order. -/
theorem servedTs_chainedPair (E : Noun → ComputeTable.FP K) (z α : K)
    (r1 r2 : MemRecordReq) {u : NTree (GenMemoryRow K)}
    (_hlink : r1.child = r2.root)
    (hu : genAnnotatedChainedTree E z α lmb [r1, r2] = some u) :
    servedTs u = [α ^ r1.recordExp, α ^ r2.recordExp] := by
  rw [servedTs, genAnnotatedChainedTree_pair_servedGen E z α r1 r2 hu]
  rfl

/-- **The generated forest's timestamp readout is `Nodup`.**

`FB`'s `genMemForest_timestampPowers_nodup` with its two readout hypotheses discharged.  This is
what `timestampPowersNodup` reduces to, and the reduction was the only thing §D was blocking. -/
theorem genMemForest_servedTs_nodup (E : Noun → ComputeTable.FP K) (z α : K)
    (t : NTree (GenComputeRow K)) (hmatch : treeRequestsMatch (bfsAssign t))
    (horb : accAt t (bfsRows t).length < orderOf α) :
    ((genMemForestFromTree E z α lmb (bfsAssign t)).flatMap servedTs).Nodup :=
  genMemForest_timestampPowers_nodup E z α servedTs
    (servedTs_recordTree E z α)
    (fun r1 r2 u hlink hu => servedTs_chainedPair E z α r1 r2 hlink hu)
    t hmatch horb

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.servedGen_genAnnotatedVerify
#print axioms Nock.NockVMROM.Thm54.TraceGen.servedGen_descent_of_nil
#print axioms Nock.NockVMROM.Thm54.TraceGen.servedGen_chainedInner_pair
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedChainedTree_pair_servedGen
#print axioms Nock.NockVMROM.Thm54.TraceGen.servedTs_recordTree
#print axioms Nock.NockVMROM.Thm54.TraceGen.servedTs_chainedPair
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemForest_servedTs_nodup
