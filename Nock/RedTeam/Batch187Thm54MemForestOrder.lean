/-
  Nock/RedTeam/Batch187Thm54MemForestOrder.lean

  **`timestampPowersNodup` at the generated forest.**

  `GenMemForestOrder` proves the generated memory forest's `z^i` timestamps are distinct, by carrying `genSemanticRequests_exponent_nodup`'s BFS-order
  distinctness across `Walk.bfsForest_perm_dfsForest` into the DFS pre-order the forest is built
  in.  Three things about that could be empty, and this artifact checks each.

  * **The `[α ^ e]` / `[α ^ e₁, α ^ e₂]` shape `h1`/`h2` assume is a shape the real builders
    have.**  §A exhibits it at the two builders that actually produce the forest's roots:
    `rootTraceOfRecordTree` (`services := [s]`) and `rootTraceOfChainedPair`
    (`services := [s1, s2]`) have `timestampPowers` exactly `[α ^ e]` and `[α ^ e₁, α ^ e₂]`.
    **Neither theorem is an instance of `h1` or `h2`**: both take a `Service` and conclude about
    `RootTrace.timestampPowers`, and neither mentions the readout `rd` that `h1`/`h2` quantify
    over (`rd` is applied to *annotated trees*, not to a `RootTrace`).  So the shipped
    `timestampPowersNodup` does **not** rest on an open hypothesis.  §A remains evidence that the
    assumed shape is the real one.
  * **The `Nodup` could be `Nodup []`.**  §B: the exponent list has length
    `accAt t |bfsRows t|`, which is positive at every compute tree, so it is never empty.
  * **The permutation could be doing no work.**  §C states the forest equation with `dfsTree` on
    the right and no `bfsForest` in it; `Batch186` already showed the two orders differ.

  §D records that `accAt … < orderOf α` fails outright at `α = 0`, which is why no separate
  `α ≠ 0` binder is carried.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMemForestOrder

set_option autoImplicit false

namespace Nock.RedTeam.Batch187

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.TraceGen

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ### A. The list shapes `h1` / `h2` assume are the shapes the two existing builders produce

`genMemForest_timestampPowers_nodup` assumes a readout `rd` with
`rd (record tree for r) = [α ^ r.recordExp]` and `rd (chained tree for r₁,r₂) =
[α ^ r₁.recordExp, α ^ r₂.recordExp]`.  A hypothesis of that shape is worth nothing if no real
object has it.  The two theorems below show `GenServedRootTrace`'s builders produce exactly those
two lists: their `services` lists are literally `[s]` and `[s1, s2]`, and their `hexp` binders fix
each `Service.exponent` to `timestampExp α (α ^ e)`, whose `α`-power is `α ^ e` again.

**What these are not.**  Neither theorem instantiates `h1` or `h2`.  Both take a `Service` (or
two) plus a builder's full argument list and conclude about `RootTrace.timestampPowers`; neither
mentions `rd`, and `h1`/`h2` apply `rd` to an *annotated tree*
(`genAnnotatedRecordTree` / `genAnnotatedChainedTree`), not to a `RootTrace`.  These are `RootTrace`
**shape** facts. -/

theorem b187_recordTree_root_timestampPowers
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    (E : Noun → ComputeTable.FP K) (z : K) (root child : Noun) (ax e : ℕ)
    (s : Service cfg exec)
    (hroot : s.root = root) (hchild : s.child = child) (haxis : s.axis = ax)
    (hexp : s.exponent = timestampExp cfg.challenges.α (cfg.challenges.α ^ e))
    (hrec : s.record = ⟨E root, E child, (ax : K), cfg.challenges.α ^ e⟩)
    (hslot : Noun.slot ax root = some child)
    (hax : exactAxisTree cfg exec i
        = axisMTree cfg.challenges.α
            (mappedRecordTree E z cfg.challenges.α MemoryTable.formRDefault root child ax e))
    (hsrv : rootResponseRecords exec i
        = servedGen [genAnnotatedRecordTree E z cfg.challenges.α MemoryTable.formRDefault root child ax e]) :
    (rootTraceOfRecordTree (i := i) E z root child ax e s hroot hchild haxis hexp hrec hslot
        hax hsrv).timestampPowers
      = [cfg.challenges.α ^ e] :=
  timestampPowers_of_services_singleton _ s e rfl hexp

theorem b187_chainedPair_root_timestampPowers
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    (E : Noun → ComputeTable.FP K) (z : K) (r1 r2 : MemRecordReq)
    (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z cfg.challenges.α MemoryTable.formRDefault [r1, r2] = some t)
    (hlink : r1.child = r2.root)
    (s1 s2 : Service cfg exec)
    (hroot1 : s1.root = r1.root) (hchild1 : s1.child = r1.child)
    (haxis1 : s1.axis = r1.axis)
    (hexp1 : s1.exponent =
      timestampExp cfg.challenges.α (cfg.challenges.α ^ r1.recordExp))
    (hrec1 : s1.record =
      ⟨E r1.root, E r1.child, (r1.axis : K), cfg.challenges.α ^ r1.recordExp⟩)
    (hroot2 : s2.root = r2.root) (hchild2 : s2.child = r2.child)
    (haxis2 : s2.axis = r2.axis)
    (hexp2 : s2.exponent =
      timestampExp cfg.challenges.α (cfg.challenges.α ^ r2.recordExp))
    (hrec2 : s2.record =
      ⟨E r2.root, E r2.child, (r2.axis : K), cfg.challenges.α ^ r2.recordExp⟩)
    (hslot1 : Noun.slot r1.axis r1.root = some r1.child)
    (hslot2 : Noun.slot r2.axis r2.root = some r2.child)
    (hne : timestampExp cfg.challenges.α (cfg.challenges.α ^ r1.recordExp) ≠
      timestampExp cfg.challenges.α (cfg.challenges.α ^ r2.recordExp))
    (hax : exactAxisTree cfg exec i
        = axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row t))
    (hsrv : rootResponseRecords exec i = servedGen [t]) :
    (rootTraceOfChainedPair (i := i) E z r1 r2 t ht hlink s1 s2 hroot1 hchild1 haxis1 hexp1
        hrec1 hroot2 hchild2 haxis2 hexp2 hrec2 hslot1 hslot2 hne hax hsrv).timestampPowers
      = [cfg.challenges.α ^ r1.recordExp, cfg.challenges.α ^ r2.recordExp] :=
  timestampPowers_of_services_pair _ s1 s2 _ _ rfl hexp1 hexp2

/-! ### B. The `Nodup` is not `Nodup []`

A distinctness claim about an empty list says nothing.  The generated forest always carries at
least one record exponent, because every compute row emits at least one memory record
(`recordCount_pos`, via `accAt_length_pos`). -/

theorem b187_exps_ne_nil (t : NTree (GenComputeRow K))
    (hmatch : treeRequestsMatch (bfsAssign t)) :
    genForestRecordExps (bfsAssign t) ≠ [] :=
  genForestRecordExps_ne_nil t hmatch

theorem b187_exps_length (t : NTree (GenComputeRow K))
    (hmatch : treeRequestsMatch (bfsAssign t)) :
    (genForestRecordExps (bfsAssign t)).length = accAt t (bfsRows t).length :=
  genForestRecordExps_length t hmatch

/-! ### C. BFS order is not the forest's order

The permutation in §A of `GenMemForestOrder` is doing real work: `genMemForestFromTree` is a DFS
pre-order `flatMap`, an equation with `dfsTree` on the right and no `bfsForest` anywhere.  If the
two orders agreed, `Walk.dfsForest_append` would hold for `bfsForest` too — `Batch186` shows it
does not. -/

theorem b187_forest_is_dfs (E : Noun → ComputeTable.FP K) (z α : K)
    (t : NTree (GenComputeRow K)) :
    genMemForestFromTree E z α MemoryTable.formRDefault t =
      (dfsTree t).flatMap (fun n => genRowMemForest E z α MemoryTable.formRDefault (extractNodeReqs n.label)) :=
  genMemForestFromTree_eq_flatMap E z α t

/-! ### D. The orbit hypothesis subsumes `α ≠ 0` — the negative direction only

`accAt t (bfsRows t).length < orderOf α` fails at `α = 0` for every program, since
`orderOf (0 : K) = 0`.  So the hypothesis is doing the `α ≠ 0` work as well as the capacity work,
and no separate `hα` binder is carried.

That is all this section proves.  It does **not** show the hypothesis is satisfiable: no positive
witness `(K, α, t)` with `accAt t (bfsRows t).length < orderOf α` is exhibited here, and for
infinite-order `α` the hypothesis is unsatisfiable. -/

theorem b187_orbit_excludes_zero (t : NTree (GenComputeRow K)) :
    ¬ (accAt t (bfsRows t).length < orderOf (0 : K)) := by
  have hz : orderOf (0 : K) = 0 := by
    rw [orderOf_eq_zero_iff]
    intro h
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp h
    rw [zero_pow hn.ne'] at hpow
    exact zero_ne_one hpow
  rw [hz]; omega

#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemForestFromTree_eq_flatMap
#print axioms Nock.NockVMROM.Thm54.TraceGen.genForestRecordExps_nodup
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemForest_recordExps_nodup
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemForest_timestampPowers_nodup
#print axioms Nock.RedTeam.Batch187.b187_recordTree_root_timestampPowers
#print axioms Nock.RedTeam.Batch187.b187_chainedPair_root_timestampPowers

end Nock.RedTeam.Batch187
