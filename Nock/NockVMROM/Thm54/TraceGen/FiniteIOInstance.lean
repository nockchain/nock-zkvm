/-
  Nock/NockVMROM/Thm54/TraceGen/FiniteIOInstance.lean

  Phase 4b (concrete): the finite-field IO chip INSTANTIATED on the generated OP1 and cons traces.

  `TraceGen/FiniteIOChecker.lean` ships the GENERAL machinery: `recordsOfReqs` (encode a
  `ServiceReq` request/response list to a `PreChallengeRecords`) and `finiteIO_gates_zero_of_LIO`
  (any `IO.LIO` record set with a non-pole-hitting coin admits a committed witness zeroing every
  `finiteIOProgAIR`/`finiteIOMemAIR` gate).  This module discharges the two remaining obligations on
  the concrete generated traces over `K = ZMod 97`:

  * `encReq` — the canonical record vectorization `ServiceReq K → (Fin 8 → K)`: the eight `MemRec`
    columns `root.{size,dyck,leaf}, child.{size,dyck,leaf}, axis, ts`, fingerprinted at the seed `z`
    through the computable `encC`.  Value-keyed,
    positionless: no committed-line index enters.

  * `Op1.gen_op1ServiceReqs_eq` / `Cons.gen_consServiceReqs_eq` — **the generator → `ServiceReq`
    linkage**.  The value-keyed service requests `genTrace` ACTUALLY
    emits for the OP1 / cons program — collected in DFS pre-order by `Gen.genServiceReqs` off the
    generator's own committed compute tree `G.computeNodes` — are exactly `[req]` resp.
    `[reqCons, reqL, reqR]`.  These are the compute-side drivers of the served memory forest, the
    analogue of `Op1GenData.gen_memForest_eq`/`ConsGenMem.gen_consMemForest_eq` one layer earlier
    (the requests that DRIVE the forest emission).  Proved via the `renderRows`/`assignExponents`
    passes, exactly as the compute/memory chips collapse through `Encode.encC_eq`.

  * `Op1.gen_op1_finiteIO_zero` — the OP1 IO chip, stated over `genTrace` output: for every trace
    the generator produces on `*[0 [1 5]] = 5`, the record set `recordsGen G` built from ITS OWN
    emitted `ServiceReq`s (via `gen_op1ServiceReqs_eq`, so mechanically tied to `genTrace`) is in
    `IO.LIO`, the sampled coin `(γ,pole) = (0,1)` misses the pole, and every
    `finiteIOProgAIR`/`finiteIOMemAIR` gate vanishes.

  * `Cons.gen_cons_finiteIO_zero` — the cons IO chip, stated over `genTrace` output: for every trace
    the generator produces on `*[0 [[1 5] [1 6]]] = [5 6]`, the record set `recordsGen G` built from
    the generator's three emitted requests (via `gen_consServiceReqs_eq`), carrying the distinct
    timestamps `α, α², α³`, forms an `IO.LIO` record set (distinct fingerprints via the timestamps,
    request/response multisets coincide) whose sampled coin misses the pole; every IO gate vanishes.
    The `IO.LIO` (Nodup + Perm) and pole-avoidance proofs carry over from the hand-built witness
    across the record equality `recordsGen_eq`.

  Together `Op1.gen_op1_finiteIO_zero`/`Cons.gen_cons_finiteIO_zero` are the IO-chip analogue of
  `gen_op1_computeAIR_zero`/`gen_cons_computeAIR_zero`, closing the THREE-chip checker
  (compute+memory of `Checker.lean`, and now IO) on the concrete generated OP1/cons traces — and,
  with the `*ServiceReqs_eq` linkage, the IO chip is now stated over `genTrace`'s OWN emitted records
  at parity with the compute/memory chips (no hand-built `ServiceReq` literal is trusted).
-/
import Nock.NockVMROM.Thm54.TraceGen.FiniteIOChecker
import Nock.NockVMROM.Thm54.TraceGen.Encode
import Nock.NockVMROM.Thm54.TraceGen.Op1Config
import Nock.NockVMROM.Thm54.TraceGen.ConsConfig
import Nock.NockVMROM.Thm54.TraceGen.Op1GenData
import Nock.NockVMROM.Thm54.TraceGen.ConsGenMem
import Nock.NockVMROM.Thm54.ForestExponentWindow

namespace Nock.NockVMROM.Thm54.TraceGen.FiniteIOChecker

open Nock Nock.Reified
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.TraceGen

variable {K : Type} [Field K]

/-! ## `encReq` — the canonical 8-column record vectorization -/

/-- **`encReq`.**  The canonical `ServiceReq K → (Fin 8 → K)` record vector: the eight `MemRec`
    columns `root.{size,dyck,leaf}, child.{size,dyck,leaf}, axis, ts`, fingerprinting `root`/`child`
    at the seed `z` through the computable `encC`.  Positionless/value-keyed. -/
def encReq (z : K) (r : ServiceReq K) : Fin 8 → K :=
  ![(encC z r.root).size, (encC z r.root).dyck, (encC z r.root).leaf,
    (encC z r.child).size, (encC z r.child).dyck, (encC z r.child).leaf,
    (r.axis : K), r.ts]

/-- The eighth column of `encReq` reads back the timestamp. -/
@[simp] theorem encReq_ts (z : K) (r : ServiceReq K) : encReq z r 7 = r.ts := rfl

/-- Two service requests with distinct timestamps encode to distinct record vectors (they differ in
    the eighth column), independent of the field.

    **The hypothesis is not free on a multi-record row.**  That is true *across*
    rows and false *within* one: `renderNode` (`Gen.lean:2884`) stamps every entry of `g.requests`
    with `α ^ stamp.recordExponent 0` in all eleven branches — `List.map` carries no index — so the
    two or three requests of an `OP_0`/`OP_2`/`OP_5`/`OP_6`/`OP_7`/`OP_8`/`OP_9` row share one
    `ServiceReq.ts`.  The two instantiations below are `Op1Config` and `ConsConfig`, whose rows are
    single-record (`activeRequestRecords`, `NockVM.lean:622`), which is why `by decide` discharges
    `h` there: `ConsConfig`'s `α, α², α³` come from three *different* rows.

    This is duplicate data, not a hole in the construction.  The authoritative per-record timestamps
    are the row's own `mr1/mr2/mr3.ts`, which `renderOp9Row` (`Gen.lean:2832-2837`) sets to
    `α ^ recordExponent 0/1/2` respectively; `ExactExecution.rawRequests` reads *those*
    (`Language.lean:33`), and `DotConfig257.rawRequest_timestamps` measures them as thirteen
    consecutive distinct powers across a trace containing the three-record `OP_9` row.  The served
    forest likewise recomputes exponents positionally via `getRecordExp stamp (i + k)`
    (`GenMem.lean:1035`) and never reads `ServiceReq.ts`.

    So: extending `FiniteIOInstance` to a multi-record program cannot use this lemma to separate two
    requests of one row.  Separate them on `root`/`child`/`axis`, or key off `mr1/mr2/mr3.ts`. -/
theorem encReq_ne_of_ts_ne (z : K) {r₁ r₂ : ServiceReq K} (h : r₁.ts ≠ r₂.ts) :
    encReq z r₁ ≠ encReq z r₂ := by
  intro heq
  exact h (by have := congrFun heq 7; simpa using this)

/-! ## OP1 slice: the single-record IO chip -/

namespace Op1

open Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton (formulaNoun resultNoun)

/-- The value-keyed request the generated OP1 compute row emits: opening the formula `[1 5]` at
    axis `3`, timestamp `α = α¹`. -/
def req : ServiceReq (ZMod 97) := ⟨formulaNoun, resultNoun, 3, Op1Config.alphaA⟩

/-- **`gen_op1ServiceReqs_eq` — the generator → `ServiceReq` linkage.**  The value-keyed service
    requests `genTrace` actually emits for the OP1 program `*[0 [1 5]] = 5` (collected in DFS
    pre-order by `genServiceReqs`) are exactly `[req]` — the one root request, stamped at the honest
    timestamp `α = α¹`.  This is the IO-chip analogue of `gen_computeNodes_eq`/`gen_memForest_eq`
    one layer earlier: the requests that DRIVE the served forest emission. -/
theorem gen_op1ServiceReqs_eq (n : ℕ) (G : GenTrace Op1Config.F Op1Config.F)
    (h : genTrace 97 3 Op1Config.seedZ Op1Config.alphaA (n + 1)
          Op1Skeleton.subjectNoun formulaNoun = .ok G) :
    genServiceReqs G.computeNodes = [req] := by
  have hG : G =
      { subject := Op1Skeleton.subjectNoun, formula := formulaNoun, result := resultNoun
        fuel := n + 1
        computeNodes := renderRows Op1Config.seedZ Op1Config.alphaA (bfsAssign
          (.node (skelNode (genSkelOp1 Op1Skeleton.subjectNoun formulaNoun resultNoun (.atom 1))
            [⟨formulaNoun, resultNoun, 3, 0⟩]) []))
        memoryNodes := genOp1MemForest Op1Config.seedZ Op1Config.alphaA 5 } :=
    Except.ok.inj h.symm
  subst hG
  rw [bfsAssign_node_nil_eq_assignExponents]
  have hstate : (genSkelOp1 Op1Skeleton.subjectNoun formulaNoun resultNoun (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  simp only [assignExponents, assignTree, assignList, renderRows, renderNode, skelNode, hstate,
    List.map_nil, genServiceReqs, List.flatten_nil, List.append_nil, stampOfAcc, List.map_cons,
    req, Nat.zero_add, pow_one]

/-- The OP1 pre-challenge record set: the one request, served by itself. -/
def records : PreChallengeRecords (ZMod 97) 8 :=
  recordsOfReqs (encReq Op1Config.seedZ) [req] [req]

/-- **`recordsGen`.**  The OP1 pre-challenge record set built from the GENERATOR's own emitted
    `ServiceReq`s (`genServiceReqs G.computeNodes`), served by themselves — the value-keyed forest
    each committed request drives.  By `gen_op1ServiceReqs_eq` this coincides with `records`. -/
def recordsGen (G : GenTrace Op1Config.F Op1Config.F) : PreChallengeRecords (ZMod 97) 8 :=
  recordsOfReqs (encReq Op1Config.seedZ)
    (genServiceReqs G.computeNodes) (genServiceReqs G.computeNodes)

/-- Sampled coins `(γ, pole) = (0, 1)` — picked off the record support. -/
def coins : IOCoins (ZMod 97) := ⟨0, 1⟩

/-- The OP1 record set lies in `IO.LIO` at `K = 3`: one distinct response, requests permute it. -/
theorem lio : IO.LIO 3 records.requests records.responses := by
  simp only [records, recordsOfReqs_requests, recordsOfReqs_responses, List.map_cons, List.map_nil]
  exact ⟨⟨by decide, by decide⟩, List.nodup_singleton _, List.Perm.refl _⟩

/-- The sampled pole misses every compressed record. -/
theorem pole : ∀ v ∈ records.requests ++ records.responses, compress coins v ≠ 0 := by
  intro v hv
  simp only [records, recordsOfReqs_requests, recordsOfReqs_responses, List.map_cons, List.map_nil,
    List.mem_append, List.mem_singleton] at hv
  rcases hv with rfl | rfl <;> decide

/-- The generated OP1 record set equals the hand-built one: both are the served forest of the single
    emitted request (`gen_op1ServiceReqs_eq`), so the `IO.LIO` and pole-avoidance proofs carry over. -/
theorem recordsGen_eq (n : ℕ) (G : GenTrace Op1Config.F Op1Config.F)
    (h : genTrace 97 3 Op1Config.seedZ Op1Config.alphaA (n + 1)
          Op1Skeleton.subjectNoun formulaNoun = .ok G) :
    recordsGen G = records := by
  rw [recordsGen, gen_op1ServiceReqs_eq n G h, records]

/-- **`gen_op1_finiteIO_zero` — the OP1 IO chip, over `genTrace` output.**  For every trace the
    generator produces on the OP1 program `*[0 [1 5]] = 5`, the finite-IO record set built from ITS
    OWN emitted `ServiceReq`s (`recordsGen G`, mechanically tied to `genTrace` via
    `gen_op1ServiceReqs_eq`) lies in `IO.LIO`, misses the sampled pole, and zeroes every
    `finiteIOProgAIR`/`finiteIOMemAIR` gate at a committed witness.  This is the IO-chip analogue of
    `gen_op1_computeAIR_zero`, now stated over the generator's emitted records at parity with the
    compute/memory chips. -/
theorem gen_op1_finiteIO_zero (n : ℕ) (G : GenTrace Op1Config.F Op1Config.F)
    (h : genTrace 97 3 Op1Config.seedZ Op1Config.alphaA (n + 1)
          Op1Skeleton.subjectNoun formulaNoun = .ok G) :
    ∃ w : PostChallengeIOWitness (recordsGen G) coins,
      ProgGatesZero (recordsGen G) coins w ∧ MemGatesZero (recordsGen G) coins w := by
  rw [recordsGen_eq n G h]
  exact finiteIO_gates_zero_of_LIO records coins lio pole

end Op1

/-! ## cons slice: the three-record IO chip -/

namespace Cons

open Nock.NockVMROM.Thm54.TraceGen.ConsSkeleton
  (formulaNoun rightFormula leftFormula leftResult rightResult)

/-- The `.cons` root's value-keyed request: opening the whole formula `[[1 5] [1 6]]` at axis `3`,
    child the right branch `[1 6]`, timestamp `α = α¹`. -/
def reqCons : ServiceReq (ZMod 97) := ⟨formulaNoun, rightFormula, 3, ConsConfig.alphaA⟩

/-- The left `OP_1` child's request: opening `[1 5]` at axis `3`, timestamp `α²`. -/
def reqL : ServiceReq (ZMod 97) := ⟨leftFormula, leftResult, 3, ConsConfig.alphaA ^ 2⟩

/-- The right `OP_1` child's request: opening `[1 6]` at axis `3`, timestamp `α³`. -/
def reqR : ServiceReq (ZMod 97) := ⟨rightFormula, rightResult, 3, ConsConfig.alphaA ^ 3⟩

/-- The three committed requests in the compute-row emission order. -/
def reqs : List (ServiceReq (ZMod 97)) := [reqCons, reqL, reqR]

/-- **`gen_consServiceReqs_eq` — the branching generator → `ServiceReq` linkage.**  The value-keyed
    service requests `genTrace` actually emits for the cons program `*[0 [[1 5] [1 6]]] = [5 6]`
    (collected in DFS pre-order by `genServiceReqs`) are exactly `[reqCons, reqL, reqR]`: the cons
    root request (stamped at `α`), then the two `OP_1` children (stamped at `α², α³` by the BFS
    exponent pass).  This is the branching analogue of `gen_op1ServiceReqs_eq` and the IO-chip
    analogue of `gen_consMemForest_eq` one layer earlier — the requests that DRIVE the served forest
    emission. -/
theorem gen_consServiceReqs_eq (n : ℕ) (G : GenTrace ConsConfig.F ConsConfig.F)
    (h : genTrace 97 4 ConsConfig.seedZ ConsConfig.alphaA (n + 2)
          ConsSkeleton.subjectNoun formulaNoun = .ok G) :
    genServiceReqs G.computeNodes = reqs := by
  have hG : G =
      { subject := ConsSkeleton.subjectNoun, formula := formulaNoun, result := ConsSkeleton.resultNoun
        fuel := n + 2
        computeNodes := renderRows ConsConfig.seedZ ConsConfig.alphaA (bfsAssign
          (.node (skelNode (genSkelCons ConsSkeleton.subjectNoun leftFormula rightFormula
              leftResult rightResult) [⟨formulaNoun, rightFormula, 3, 0⟩])
            [.node (skelNode (genSkelOp1 ConsSkeleton.subjectNoun leftFormula leftResult (.atom 1))
                [⟨leftFormula, leftResult, 3, 0⟩]) [],
             .node (skelNode (genSkelOp1 ConsSkeleton.subjectNoun rightFormula rightResult (.atom 1))
                [⟨rightFormula, rightResult, 3, 0⟩]) []]))
        memoryNodes := genMemForest ConsConfig.seedZ ConsConfig.alphaA formulaNoun } :=
    Except.ok.inj h.symm
  subst hG
  rw [bfsAssign_eq_assignExponents_two_leaves]
  have hcons : (genSkelCons ConsSkeleton.subjectNoun leftFormula rightFormula leftResult
        rightResult).state = ComputeTable.State.cons := rfl
  have hop1 : (genSkelOp1 ConsSkeleton.subjectNoun leftFormula leftResult (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  have hop1' : (genSkelOp1 ConsSkeleton.subjectNoun rightFormula rightResult (Noun.atom 1)).state
      = ComputeTable.State.s1 := rfl
  simp only [assignExponents, assignTree, assignList, subtreeRecordCount, stampOfAcc, renderRows,
    renderNode, skelNode, hcons, hop1, hop1', Nock.Framework.recordCount, List.map_nil,
    List.map_cons, List.sum_nil, genServiceReqs, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.nil_append, List.cons_append, reqs, reqCons, reqL, reqR,
    Nat.zero_add, Nat.add_zero, pow_one]

/-- The cons pre-challenge record set: the honest served forest serves each request by fingerprint
    VALUE, so the response multiset equals the request multiset (here the same committed order). -/
def records : PreChallengeRecords (ZMod 97) 8 :=
  recordsOfReqs (encReq ConsConfig.seedZ) reqs reqs

/-- **`recordsGen`.**  The cons pre-challenge record set built from the GENERATOR's own emitted
    `ServiceReq`s (`genServiceReqs G.computeNodes`), served by themselves.  By
    `gen_consServiceReqs_eq` this coincides with `records`. -/
def recordsGen (G : GenTrace ConsConfig.F ConsConfig.F) : PreChallengeRecords (ZMod 97) 8 :=
  recordsOfReqs (encReq ConsConfig.seedZ)
    (genServiceReqs G.computeNodes) (genServiceReqs G.computeNodes)

/-- Sampled coins `(γ, pole) = (0, 1)` — picked off the record support. -/
def coins : IOCoins (ZMod 97) := ⟨0, 1⟩

/-- The cons record set lies in `IO.LIO` at `K = 4`: the three fingerprints are pairwise distinct
    (distinct timestamps `α, α², α³`), and the requests permute the responses (identically here). -/
theorem lio : IO.LIO 4 records.requests records.responses := by
  refine ⟨⟨by decide, by decide⟩, ?_, ?_⟩
  · -- responses.Nodup, via the pairwise-distinct timestamps
    have h12 : encReq ConsConfig.seedZ reqCons ≠ encReq ConsConfig.seedZ reqL :=
      encReq_ne_of_ts_ne _ (by decide)
    have h13 : encReq ConsConfig.seedZ reqCons ≠ encReq ConsConfig.seedZ reqR :=
      encReq_ne_of_ts_ne _ (by decide)
    have h23 : encReq ConsConfig.seedZ reqL ≠ encReq ConsConfig.seedZ reqR :=
      encReq_ne_of_ts_ne _ (by decide)
    simp only [records, recordsOfReqs_responses, reqs, List.map_cons, List.map_nil,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true,
      not_or, not_false_iff]
    exact ⟨⟨h12, h13⟩, h23⟩
  · exact List.Perm.refl _

/-- The sampled pole misses every compressed record. -/
theorem pole : ∀ v ∈ records.requests ++ records.responses, compress coins v ≠ 0 := by
  intro v hv
  simp only [records, recordsOfReqs_requests, recordsOfReqs_responses, reqs, List.map_cons,
    List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hv
  rcases hv with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;> decide

/-- The generated cons record set equals the hand-built one: both are the served forest of the three
    emitted requests (`gen_consServiceReqs_eq`), so the `IO.LIO` and pole-avoidance proofs carry
    over. -/
theorem recordsGen_eq (n : ℕ) (G : GenTrace ConsConfig.F ConsConfig.F)
    (h : genTrace 97 4 ConsConfig.seedZ ConsConfig.alphaA (n + 2)
          ConsSkeleton.subjectNoun formulaNoun = .ok G) :
    recordsGen G = records := by
  rw [recordsGen, gen_consServiceReqs_eq n G h, records]

/-- **`gen_cons_finiteIO_zero` — the cons IO chip, over `genTrace` output.**  For every trace the
    generator produces on the cons program `*[0 [[1 5] [1 6]]] = [5 6]`, the finite-IO record set
    built from ITS OWN emitted `ServiceReq`s (`recordsGen G`, mechanically tied to `genTrace` via
    `gen_consServiceReqs_eq`) — the three committed records carrying the distinct timestamps
    `α, α², α³` — lies in `IO.LIO`, misses the sampled pole, and zeroes every
    `finiteIOProgAIR`/`finiteIOMemAIR` gate at a committed witness.  This is the IO-chip analogue of
    `gen_cons_computeAIR_zero`, now stated over the generator's emitted records at parity with the
    compute/memory chips. -/
theorem gen_cons_finiteIO_zero (n : ℕ) (G : GenTrace ConsConfig.F ConsConfig.F)
    (h : genTrace 97 4 ConsConfig.seedZ ConsConfig.alphaA (n + 2)
          ConsSkeleton.subjectNoun formulaNoun = .ok G) :
    ∃ w : PostChallengeIOWitness (recordsGen G) coins,
      ProgGatesZero (recordsGen G) coins w ∧ MemGatesZero (recordsGen G) coins w := by
  rw [recordsGen_eq n G h]
  exact finiteIO_gates_zero_of_LIO records coins lio pole

end Cons

end Nock.NockVMROM.Thm54.TraceGen.FiniteIOChecker

#print axioms Nock.NockVMROM.Thm54.TraceGen.FiniteIOChecker.Op1.gen_op1ServiceReqs_eq
#print axioms Nock.NockVMROM.Thm54.TraceGen.FiniteIOChecker.Op1.gen_op1_finiteIO_zero
#print axioms Nock.NockVMROM.Thm54.TraceGen.FiniteIOChecker.Cons.gen_consServiceReqs_eq
#print axioms Nock.NockVMROM.Thm54.TraceGen.FiniteIOChecker.Cons.gen_cons_finiteIO_zero
