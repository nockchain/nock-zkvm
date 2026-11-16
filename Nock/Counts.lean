/-
  Nock/Counts.lean

  **Proven count theorems for the reified AIR** (deliverable: turn the §5 cost/count
  figures from undischarged `def`s into PROVEN theorems from the reified AIR).

  `Nock/AIR.lean` reifies the compute/memory RAP gates as first-class, serializable `AIR`
  data (`computeAIR`, `(memoryAIR (K := K))`, and the transition AIRs `walkAIR`/`ioProgAIR`/`ioMemAIR`/
  `(memoryAIRchained (K := K))`/`computeAIRchained`).  Because that data is fully concrete and `K`-free,
  its interface sizes (`numTraceCols`/`numChallenges`/`numPublic`), its constraint count
  (`constraints.length`), its maximum constraint degree (`AIR.maxDegree`), and its full degree
  histogram (`constraints.countP (·.degree == d)`) are all COMPUTABLE and hence provable by
  kernel reduction.  NO `native_decide` is used.  Atomic / chained / memory / walk / IO counts
  are `rfl` (some under an elevated `maxRecDepth` because the compute constraint list has 526
  entries) and `#print axioms` reports the empty set.  Packed count theorems
  (`computeAIRPacked_*`) are still `rfl` with no `native_decide`; `#print axioms` reports
  `{propext}` because packing combinators use `Classical.propDecidable`.
  `packed_fewer_constraints_than_atomic` is `omega` after those `rfl`s and reports
  `{propext, Quot.sound}`. All I2-whitelist, not a leak.

  These are the ACTUAL, mechanically-verified counts of the reified construction.

  Cross-reference to the undischarged §5 cost `def`s in `Nock/NockVM.lean`:
    `ComputeTable.comp_columns`/`comp_deg4_gates`, `MemoryTable.mem_columns`/`mem_deg4_gates`,
    `NockVM.comp_io_columns`/`comp_io_deg4_gates`/`mem_io_columns`/`mem_io_deg4_gates`/
    `total_row_elements`/`total_deg4_gates`/`extOrder`/`Λ`/`kbound`/`security_bits`.
  Those remain documented `def`s mirroring the paper (with its internal inconsistencies); the
  theorems here are the independent, proven reified figures they are compared against.
-/
import Nock.AIRPacked

namespace Nock
namespace Reified

set_option maxRecDepth 40000

/-! ## 1. `computeAIR` — the full per-row compute-table AIR

  Interface sizes, constraint count (526), max degree (4), and the complete degree histogram. -/

theorem computeAIR_numTraceCols : computeAIR.numTraceCols = 94 := rfl
theorem computeAIR_numChallenges : computeAIR.numChallenges = 5 := rfl
theorem computeAIR_numPublic : computeAIR.numPublic = 0 := rfl

/-- **526 constraints** — the mechanically-verified constraint count of the reified compute AIR. -/
theorem computeAIR_num_constraints : computeAIR.constraints.length = 526 := rfl

/-- **Max constraint degree 4** — matches the paper's "degree ≤ 4" claim (`Thm:comp_38`). -/
theorem computeAIR_maxDegree : computeAIR.maxDegree = 4 := by rfl

/-- Degree histogram of `computeAIR` (all 526 constraints classified by trace-degree). -/
theorem computeAIR_deg0 : computeAIR.constraints.countP (fun c => c.degree == 0) = 0 := rfl
theorem computeAIR_deg1 : computeAIR.constraints.countP (fun c => c.degree == 1) = 10 := rfl
theorem computeAIR_deg2 : computeAIR.constraints.countP (fun c => c.degree == 2) = 472 := rfl
theorem computeAIR_deg3 : computeAIR.constraints.countP (fun c => c.degree == 3) = 31 := rfl
theorem computeAIR_deg4 : computeAIR.constraints.countP (fun c => c.degree == 4) = 13 := rfl
theorem computeAIR_deg_ge5 : computeAIR.constraints.countP (fun c => 5 ≤ c.degree) = 0 := rfl

/-- The histogram is complete: the four occupied degree buckets sum to the total constraint count. -/
theorem computeAIR_hist_total : 10 + 472 + 31 + 13 = computeAIR.constraints.length := rfl

/-! ## 1b. `computeAIRPacked` — paper selector fold

  Same 94/5/0 interface as production `computeAIR`. Constraint count is **93**
  (= 27 always-on prefix + 66 packed evaluation / extra / memory-record gates)
  rather than 526. Production `computeAIR` is unchanged. This is a
  granularity/cost delta, not a soundness change (`packed_iff_atomic`). -/

theorem computeAIRPacked_numTraceCols : computeAIRPacked.numTraceCols = 94 := rfl
theorem computeAIRPacked_numChallenges : computeAIRPacked.numChallenges = 5 := rfl
theorem computeAIRPacked_numPublic : computeAIRPacked.numPublic = 0 := rfl

/-- **93 constraints** — selector-packed compute AIR (`Σ_k op_k · (slot − target_k) = 0`). -/
theorem computeAIRPacked_num_constraints : computeAIRPacked.constraints.length = 93 := rfl

/-- **Max constraint degree 4** — same bound as production `computeAIR`. -/
theorem computeAIRPacked_maxDegree : computeAIRPacked.maxDegree = 4 := by rfl

/-- Degree histogram of `computeAIRPacked`. -/
theorem computeAIRPacked_deg0 : computeAIRPacked.constraints.countP (fun c => c.degree == 0) = 0 := rfl
theorem computeAIRPacked_deg1 : computeAIRPacked.constraints.countP (fun c => c.degree == 1) = 10 := rfl
theorem computeAIRPacked_deg2 : computeAIRPacked.constraints.countP (fun c => c.degree == 2) = 57 := rfl
theorem computeAIRPacked_deg3 : computeAIRPacked.constraints.countP (fun c => c.degree == 3) = 19 := rfl
theorem computeAIRPacked_deg4 : computeAIRPacked.constraints.countP (fun c => c.degree == 4) = 7 := rfl
theorem computeAIRPacked_deg_ge5 : computeAIRPacked.constraints.countP (fun c => 5 ≤ c.degree) = 0 := rfl

/-- The histogram is complete: the four occupied degree buckets sum to 93. -/
theorem computeAIRPacked_hist_total : 10 + 57 + 19 + 7 = computeAIRPacked.constraints.length := rfl

/-- Packed compute AIR is strictly smaller than the atomic expansion (93 < 526).
    Honest-selector zeros agree (`packed_iff_atomic`). -/
theorem packed_fewer_constraints_than_atomic :
    computeAIRPacked.constraints.length < computeAIR.constraints.length := by
  rw [computeAIRPacked_num_constraints, computeAIR_num_constraints]
  omega

/-! ## 2. `(memoryAIR (K := K))` — the full per-row memory-table AIR

The exponent in the form-R read gates is `Nat.size (ringChar K)`, so the AIR takes a field.
Degrees do not depend on that exponent (`Expr.powDegree`). -/

section MemoryCounts
variable {K : Type*} [Field K]


theorem memoryAIR_numTraceCols : (memoryAIR (K := K)).numTraceCols = 36 := rfl
theorem memoryAIR_numChallenges : (memoryAIR (K := K)).numChallenges = 9 := rfl
theorem memoryAIR_numPublic : (memoryAIR (K := K)).numPublic = 0 := rfl

/-- **75 constraints** — the mechanically-verified constraint count of the reified memory AIR. -/
theorem memoryAIR_num_constraints : (memoryAIR (K := K)).constraints.length = 75 := rfl

/-- **Max constraint degree 4** — matches the paper's "degree ≤ 4" claim (`Thm:mem_38`). -/
theorem memoryAIR_maxDegree : (memoryAIR (K := K)).maxDegree = 4 :=
  mem_slice_maxDegree

/-- Degree histogram of `(memoryAIR (K := K))`. -/
theorem memoryAIR_deg0 : (memoryAIR (K := K)).constraints.countP (fun c => c.degree == 0) = 0 := rfl
theorem memoryAIR_deg1 : (memoryAIR (K := K)).constraints.countP (fun c => c.degree == 1) = 2 := rfl
/-- Form R's read-root counts gate is degree 4 (selector · axis · C' · ts), so the
degree-2 bucket is 66 and the degree-4 bucket is 2. -/
theorem memoryAIR_deg2 : (memoryAIR (K := K)).constraints.countP (fun c => c.degree == 2) = 66 := rfl
theorem memoryAIR_deg3 : (memoryAIR (K := K)).constraints.countP (fun c => c.degree == 3) = 5 := rfl
theorem memoryAIR_deg4 : (memoryAIR (K := K)).constraints.countP (fun c => c.degree == 4) = 2 := rfl
theorem memoryAIR_deg_ge5 : (memoryAIR (K := K)).constraints.countP (fun c => 5 ≤ c.degree) = 0 := rfl

theorem memoryAIR_hist_total : 2 + 66 + 5 + 2 = (memoryAIR (K := K)).constraints.length := rfl

/-! The reified construction refutes the equality at
  the ground-truth level: the memory table has STRICTLY FEWER constraints and STRICTLY FEWER
  degree-4 gates than the compute table, at every measured granularity. -/

theorem mem_fewer_constraints_than_comp :
    (memoryAIR (K := K)).constraints.length < computeAIR.constraints.length := by
  rw [memoryAIR_num_constraints, computeAIR_num_constraints]
  omega

theorem mem_fewer_deg4_than_comp :
    (memoryAIR (K := K)).constraints.countP (fun c => c.degree == 4)
      < computeAIR.constraints.countP (fun c => c.degree == 4) := by
  rw [memoryAIR_deg4, computeAIR_deg4]
  omega

end MemoryCounts

/-! ## 3. The cross-row TRANSITION AIRs (`Nock.Reified.Trans`) -/

namespace Trans

/-- Walk α-telescoping AIR: 3 boundary + 3 transition + 1 terminal. -/
theorem walkAIR_numTraceCols : walkAIR.numTraceCols = 6 := rfl
theorem walkAIR_numChallenges : walkAIR.numChallenges = 1 := rfl
theorem walkAIR_numPublic : walkAIR.numPublic = 2 := rfl
theorem walkAIR_num_constraints : walkAIR.constraints.length = 7 := rfl
theorem walkAIR_maxDegree : walkAIR.maxDegree = 2 := by rfl

/-- Prog-IO accumulator AIR. -/
theorem ioProgAIR_numTraceCols : ioProgAIR.numTraceCols = 2 := rfl
theorem ioProgAIR_numChallenges : ioProgAIR.numChallenges = 0 := rfl
theorem ioProgAIR_numPublic : ioProgAIR.numPublic = 1 := rfl
theorem ioProgAIR_num_constraints : ioProgAIR.constraints.length = 3 := rfl
theorem ioProgAIR_maxDegree : ioProgAIR.maxDegree = 1 := by rfl

/-- Mem-IO accumulator AIR. -/
theorem ioMemAIR_numTraceCols : ioMemAIR.numTraceCols = 3 := rfl
theorem ioMemAIR_numChallenges : ioMemAIR.numChallenges = 0 := rfl
theorem ioMemAIR_numPublic : ioMemAIR.numPublic = 2 := rfl
theorem ioMemAIR_num_constraints : ioMemAIR.constraints.length = 3 := rfl
theorem ioMemAIR_maxDegree : ioMemAIR.maxDegree = 2 := by rfl

section MemoryChainCounts
variable {K : Type*} [Field K]

/-- `(memoryAIRchained (K := K))` = `(memoryAIR (K := K))` (75) + 1 cross-row LogUp chaining transition gate + 3
    `.boundary` gates (the two distinct axis-accumulator seeds plus LogUp `ipre = 0`) + 1
    `.terminal` gate (`icur = 0`).  All five added gates are degree 1, so `maxDegree` is unchanged
    (still 4). -/
theorem memoryAIRchained_num_constraints : (memoryAIRchained (K := K)).constraints.length = 80 := rfl
theorem memoryAIRchained_maxDegree : (memoryAIRchained (K := K)).maxDegree = 4 := by
  have hmem : constraintMax (memoryAIR (K := K)).constraints = 4 := mem_slice_maxDegree
  have hdeg : (memoryAIRchained (K := K)).maxDegree =
      constraintMax (memoryAIRchained (K := K)).constraints := rfl
  rw [hdeg, memoryAIRchained, constraintMax_append, constraintMax_append, constraintMax_append, hmem]
  have hchain : constraintMax [⟨.transition, icurChainExpr⟩] = 1 := by
    simp [constraintMax, icurChainExpr, tc, tn, Expr.degree]
  have hseed : constraintMax (memSeedBoundaryExprs.map (fun e => (⟨.boundary, e⟩ : Constraint))) = 1 := by
    simp [constraintMax, memSeedBoundaryExprs, memSeedCountsExpr, memSeedIndicatorExpr, tc, Expr.degree]
  have hend : constraintMax [⟨.boundary, memIpreInitExpr⟩, ⟨.terminal, memIcurTermExpr⟩] = 1 := by
    simp [constraintMax, memIpreInitExpr, memIcurTermExpr, tc, Expr.degree]
  rw [hchain, hseed, hend]
  decide

/-- Exact reflected constraint-kind census: 75 row, 1 transition, 3 boundary, 1 terminal. -/
theorem memoryAIRchained_kind_counts :
    (memoryAIRchained (K := K)).constraints.countP (fun c => c.kind == .row) = 75 ∧
      (memoryAIRchained (K := K)).constraints.countP (fun c => c.kind == .transition) = 1 ∧
      (memoryAIRchained (K := K)).constraints.countP (fun c => c.kind == .boundary) = 3 ∧
      (memoryAIRchained (K := K)).constraints.countP (fun c => c.kind == .terminal) = 1 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Complete reflected degree census.  The five chained/endpoint gates raise degree-1 from 2 to 7;
    all higher-degree buckets are exactly those of the 75-gate row AIR. -/
theorem memoryAIRchained_degree_counts :
    (memoryAIRchained (K := K)).constraints.countP (fun c => c.degree == 0) = 0 ∧
      (memoryAIRchained (K := K)).constraints.countP (fun c => c.degree == 1) = 7 ∧
      (memoryAIRchained (K := K)).constraints.countP (fun c => c.degree == 2) = 66 ∧
      (memoryAIRchained (K := K)).constraints.countP (fun c => c.degree == 3) = 5 ∧
      (memoryAIRchained (K := K)).constraints.countP (fun c => c.degree == 4) = 2 ∧
      (memoryAIRchained (K := K)).constraints.countP (fun c => 5 ≤ c.degree) = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The occupied degree buckets sum to the mechanically reflected total of 80. -/
theorem memoryAIRchained_hist_total :
    7 + 66 + 5 + 2 = (memoryAIRchained (K := K)).constraints.length := rfl

end MemoryChainCounts

/-- `computeAIRchained` = `computeAIR` (526) + 1 cross-row line-nonce hand-off transition gate. -/
theorem computeAIRchained_num_constraints : computeAIRchained.constraints.length = 527 := rfl
theorem computeAIRchained_maxDegree : computeAIRchained.maxDegree = 4 := by rfl

end Trans

/-! ## 4. -/

#print axioms computeAIR_num_constraints
#print axioms computeAIR_maxDegree
#print axioms computeAIR_deg4
#print axioms computeAIRPacked_num_constraints
#print axioms computeAIRPacked_maxDegree
#print axioms computeAIRPacked_deg4
#print axioms packed_fewer_constraints_than_atomic
#print axioms memoryAIR_num_constraints
#print axioms memoryAIR_maxDegree
#print axioms mem_fewer_deg4_than_comp
#print axioms Trans.walkAIR_num_constraints
#print axioms Trans.memoryAIRchained_num_constraints
#print axioms Trans.memoryAIRchained_maxDegree
#print axioms Trans.memoryAIRchained_kind_counts
#print axioms Trans.memoryAIRchained_degree_counts
#print axioms Trans.computeAIRchained_num_constraints

end Reified
end Nock
