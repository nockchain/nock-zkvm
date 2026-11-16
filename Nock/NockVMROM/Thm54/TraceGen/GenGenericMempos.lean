/-
  Nock/NockVMROM/Thm54/TraceGen/GenGenericMempos.lean

  **Generic `hmempos` — the generated memory forest of any accepted
  `genComputeSkeleton` is nonempty.**

  `mem_record₁` always verifies the opening of
  the formula at the given opcode, so every compute-table state requests
  at least one record (`Nock.Framework.recordCount_pos`).  The generator
  matches that ISA class: every successful arm emits the formula-open
  `⟨formula, tail, 3⟩` first (`genComputeSkeleton_root_requests`).  That
  is the full compute-table ISA (`s0`–`s9` and `cons`), not a fragment.

  `hmempos` is therefore a theorem of `h : genComputeSkeleton =.ok`,
  not a fixture (`mm_mempos`) and not a field of `E`.  No `∀ E`, no C5.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenChainedLanguage
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMemWeb
import Nock.NockVMROM.Thm54.TraceGen.GenCommitmentBridge

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open MemoryTable

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## One compute row's requests produce a nonempty forest -/

/-- Extraction preserves length, so a nonempty request list stays nonempty. -/
theorem extractNodeReqs_ne_nil (g : GenComputeRow K)
    (hne : g.requests ≠ []) : extractNodeReqs g ≠ [] := by
  intro h
  have hlen := extractNodeReqs_length g
  rw [h] at hlen
  exact hne (List.eq_nil_of_length_eq_zero hlen.symm)

/-- `genRowMemForest` of a nonempty request list is nonempty.

Every branch of the auto-chainer (`GenMem.lean`) returns at least one
annotated record tree: singleton, chainable/independent pair, the
three-record `first2 ++ [r3]` case, and the catch-all `map`. -/
theorem genRowMemForest_ne_nil (E : Noun → ComputeTable.FP K) (z α : K)
    (reqs : List MemRecordReq) (hne : reqs ≠ []) :
    genRowMemForest E z α lmb reqs ≠ [] := by
  match reqs with
  | [] => exact (hne rfl).elim
  | [r] => simp [genRowMemForest]
  | [r1, r2] =>
    simp only [genRowMemForest]
    split_ifs
    · cases genAnnotatedChainedTree E z α lmb [r1, r2] <;> simp
    · simp
  | [r1, r2, r3] =>
    simp only [genRowMemForest]
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  | r1 :: r2 :: r3 :: r4 :: rest =>
    simp [genRowMemForest]

/-- A tree whose root row has a request contributes at least one memory
root — the paper's always-on `mem_record₁`. -/
theorem genMemForestFromTree_ne_nil (E : Noun → ComputeTable.FP K) (z α : K)
    (t : NTree (GenComputeRow K)) (hne : t.label.requests ≠ []) :
    genMemForestFromTree E z α lmb t ≠ [] := by
  cases t with
  | node g cs =>
    change genRowMemForest E z α lmb (extractNodeReqs g) ++
        genMemForestFromList E z α lmb cs ≠ []
    intro hempty
    exact genRowMemForest_ne_nil (lmb := lmb) E z α _ (extractNodeReqs_ne_nil g hne)
      ((List.append_eq_nil_iff.mp hempty).1)

theorem ntree_size_pos {α : Type} (t : NTree α) : 0 < t.size := by
  cases t with
  | node _ cs =>
    simp [NTree.size]

theorem totalSize_pos_of_ne_nil {α : Type} {l : List (NTree α)}
    (h : l ≠ []) : 0 < totalSize l := by
  match l with
  | [] => exact (h rfl).elim
  | t :: rest =>
    rw [totalSize_cons]
    have := ntree_size_pos t
    omega

/-! ## `hmempos` at the committed forest

`genMemoryForest` threads `genMemForestFromTree` of the BFS-assigned
AIR-ordered tree.  Threading preserves `totalSize`; `bfsForest.length`
is `totalSize`. -/

/-- **The generated memory forest of any accepted program is nonempty.**

ISA class: every compute-table opcode (`s0`–`s9` and `cons`).  The paper
makes `mem_record₁` always operative; the generator
emits that formula-open request on every successful arm
(`genComputeSkeleton_root_requests`).  Quantified over the generated
forest, not `mmTree`, and not over a hostile `E`. -/
theorem genComputeSkeleton_hmempos (z α : K) (inp : Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    0 < (bfsForest (genMemoryForest z α lmb inp t)).length := by
  obtain ⟨hne, _hax⟩ := genComputeSkeleton_root_requests h
  have hreq : (bfsAssign (airReorder t)).label.requests = t.label.requests := by
    rw [bfsAssign_root_requests, airReorder_label]
  have hforest :
      genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t)) ≠ [] :=
    genMemForestFromTree_ne_nil (lmb := lmb) (encC z) z α (bfsAssign (airReorder t))
      (by rw [hreq]; exact hne)
  rw [bfsForest_length, genMemoryForest, threadGenForest_totalSize]
  exact totalSize_pos_of_ne_nil hforest

/-- Brief name: same fact, seed-independent -/
theorem genMemoryForest_bfsForest_length_pos (z α : K) (inp : Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    0 < (bfsForest (genMemoryForest z α lmb inp t)).length :=
  genComputeSkeleton_hmempos z α inp h

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.extractNodeReqs_ne_nil
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRowMemForest_ne_nil
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemForestFromTree_ne_nil
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_hmempos
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemoryForest_bfsForest_length_pos
