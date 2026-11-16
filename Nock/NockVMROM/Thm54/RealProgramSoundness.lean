/-
  Nock/NockVMROM/Thm54/RealProgramSoundness.lean

  **A Goldilocks soundness figure whose record count is derived, not assumed.**

  `ExtensionChallenges.soundnessK_at_paper_configuration` (`ExtensionChallenges.lean:833`) and
  `GoldilocksParameters.soundness_at_paper_configuration` (`GoldilocksParameters.lean:391`) both
  carry `hio : ioWork ≤ 16 ^ 65 = 2 ^ 260` as a *hypothesis*.  That ceiling is not satisfiable at
  the row counts those theorems name.  The real workload is
  `ioFailureUnionBound 8 n n |K| = |K| · (28n² + 4n)` (`GoldilocksParameters.lean:127`), so at
  `|K| = p³ ≈ 2^192` the ceiling admits at most `n ≈ 2^31.6` memory records — fewer than
  `1.52` records per compute row.  But `V_comp` emits `mem_record₁`
  unconditionally (`:1728`), `mem_record₂` for every `formula_head ∈ {2,5,6,7,8,9}` (`:1730`)
  and for `OP₀` (`:1742`), and `mem_record₃` for `OP₆` (`:1733`) and `OP₉` (`:1737-1738`).
  `NockVM.activeRequestRecords` (`Nock/NockVM.lean:650`) transcribes exactly that: `1` record for
  `s1/s3/s4/cons`, `2` for `s0/s2/s5/s7/s8`, `3` for `s6/s9`.  A program with `R` compute rows
  therefore has `R ≤ n ≤ 3R` records — the lower half is
  `GatedIOChip.compRows_le_requests_length` (`GatedIOChip.lean:912`), the upper half is §1 here —
  and at `R = 2^31` rows the `2^260` ceiling is met only if *every* row is a one-record row.

  This module rebuilds the figure with nothing assumed about the record count.

  * **§1** derives `|requests| ≤ 3 · compRows` and `|responses| ≤ memRows` from opcode arity.
  * **§2** majorizes `ProductionP8Containment.workload` (`ProductionP8Containment.lean:548`) by an
    explicit polynomial in the compute rows `R`, memory rows `M`, leaf window `Λ` and axis workload `A`; and bounds the axis polynomial's degree by the largest
    timestamp exponent in the memory tree, so the residual input is a trace-local quantity.
  * **§3** collapses the two-denominator bound: at the *real* `ioWork` the `ioWork/|K|²` summand
    is exactly `(28n² + 4n)/|K|`, so the whole bound is a single fraction over `|K|`.
  * **§4/§5** give the parametric theorem: with every size parameter at most `2^r` (`r ≥ 2`) and
    `2r + b = 183`, the false-acceptance bound is below `2^-b`.  **`b = 183 − 2r`.**
  * **§5.1** repeats §4/§5 with the axis workload allowed to be *quadratic* (`A ≤ 4·2^{2r}`),
    which is the shape `kMem · L` actually has, at **no change to `b`**.
  * At `r = 32` that is **119 bits**; at `r = 31`,
    **121 bits**; at `r = 20`, **143 bits**.

  Nothing here is assumed about `ioWork`.  `A` enters the numerator linearly and
  once while the coefficient budget is `511` (`sizeWorkQuad_not_lt_cardK_at_512`), so raising the
  allowance from `A ≤ 2^32` to `A ≤ 4·2^64` moves the leading coefficient `291 → 295` and costs
  **no bits**; and `4·2^64` is above the axis workload's honest shape `kMem · L`, whose two
  factors are a memory-row count (`kMem_le_memRows`, §1) and the paper's record count
  `L ≤ 3·compRows`.  So the only remaining input is the leaf window `hΛ`.
-/
import Nock.NockVMROM.Thm54.ExtensionChallenges
import Nock.NockVMROM.Thm54.Language
import Nock.NockVMROM.Thm54.RawTopologyRAP
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.WalkTilingEvents
import Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
import Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54
namespace RealProgramSoundness

open Polynomial
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.SizeWindowCounting

noncomputable section

/-! ## 1. The record count is derived from opcode arity

`V_comp` emits at most three memory records per compute row and
a memory row serves at most one response.  Both bounds below are structural: they hold for every trace,
honest or hostile. -/

/-- A flat-map of blocks each of length at most `c` is at most `c` times as long as the block
list.  The `≥` counterpart is `GatedIOChip.length_le_flatMap` (`GatedIOChip.lean:893`). -/
theorem length_flatMap_le {α β : Type*} (l : List α) (g : α → List β) (c : ℕ)
    (hg : ∀ a ∈ l, (g a).length ≤ c) : (l.flatMap g).length ≤ c * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h1 : (g a).length ≤ c := hg a (by simp)
    have h2 : (t.flatMap g).length ≤ c * t.length :=
      ih (fun b hb => hg b (List.mem_cons_of_mem a hb))
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    calc (g a).length + (t.flatMap g).length ≤ c + c * t.length := Nat.add_le_add h1 h2
      _ = c * (t.length + 1) := by ring

/-- A flat-map of nonempty blocks is at least as long as the block list. -/
theorem one_le_length_flatMap {α β : Type*} (l : List α) (g : α → List β)
    (hg : ∀ a ∈ l, g a ≠ []) : l.length ≤ (l.flatMap g).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h1 : 1 ≤ (g a).length := List.length_pos_of_ne_nil (hg a (by simp))
    have h2 : t.length ≤ (t.flatMap g).length :=
      ih (fun b hb => hg b (List.mem_cons_of_mem a hb))
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    omega

/-- **Every compute row emits at least one memory request** — the paper's unconditional
    `mem_record₁`. -/
theorem activeRequestRecords_ne_nil {K : Type*} (pub : ComputeTable.Pub K) :
    NockVM.activeRequestRecords pub ≠ [] := by
  cases hs : pub.state <;> simp [NockVM.activeRequestRecords, hs]

/-- **At most three memory requests per compute row.**  `OP₆`/`OP₉` are the only three-record
    opcodes; every other state emits one or two.  Compare
    `GatedIOChip.activeRequestRecords_ne_nil` (`GatedIOChip.lean:906`), the matching lower
    bound of `1` from the paper's unconditional `mem_record₁`. -/
theorem activeRequestRecords_length_le_three {K : Type*} (pub : ComputeTable.Pub K) :
    (NockVM.activeRequestRecords pub).length ≤ 3 := by
  cases hs : pub.state <;> simp [NockVM.activeRequestRecords, hs]

/-- **At most one external response per memory row.**  External IO is `ver`-selected; a row emits at most its `mem` record. -/
theorem responseRecords_length_le_one {K : Type*} [Field K] (pub : MemoryTable.Pub K) :
    (MemoryTable.responseRecords pub).length ≤ 1 := by
  simp [MemoryTable.responseRecords]
  split <;> simp

section NockVMLevel

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- **`|reqRecs| ≤ 3 · hc`.**  `NockVM.reqRecs` (`Nock/NockVM.lean:659`) flat-maps compute rows
    and then the row's opcode-active records. -/
theorem reqRecs_length_le (lblc : ℕ → ComputeTable.State × ComputeTable.DTcomp K) (hc : ℕ)
    (lmb : K) :
    (NockVM.reqRecs lblc hc lmb).length ≤ 3 * hc := by
  have h := length_flatMap_le (List.range hc)
    (fun k => (NockVM.activeRequestRecords (lblc (k + 1)).2.2.1).map NockVM.encRec) 3
    (fun k _ => by
      rw [List.length_map]; exact activeRequestRecords_length_le_three _)
  simpa [NockVM.reqRecs] using h

/-- **`|respRecs| ≤ hm`.**  `NockVM.respRecs` (`Nock/NockVM.lean:684`) flat-maps memory rows. -/
theorem respRecs_length_le (lblm : ℕ → MemoryTable.MState × MemoryTable.DTmem K) (hm : ℕ) :
    (NockVM.respRecs lblm hm).length ≤ hm := by
  have h := length_flatMap_le (List.range hm)
    (fun k => (MemoryTable.responseRecords (lblm (k + 1)).2.2).map NockVM.encRec) 1
    (fun k _ => by
      rw [List.length_map]; exact responseRecords_length_le_one _)
  simpa [NockVM.respRecs] using h

end NockVMLevel

section ExecutionLevel

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **`|requests| ≤ 3 · compRows` for every execution.**  The upper counterpart of
    `GatedIOChip.compRows_le_requests_length` (`GatedIOChip.lean:912`). -/
theorem derivedRequestIO_length_le {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.derivedRequestIO.length ≤ 3 * cfg.compRows := by
  rw [ExactExecution.derivedRequestIO_eq_computeRows, List.length_map,
    ← exec.computeRows_length]
  exact length_flatMap_le exec.computeRows
    (fun row : ComputeTable.State × ComputeTable.DTcomp K =>
      NockVM.activeRequestRecords row.2.2.1) 3
    (fun row _ => activeRequestRecords_length_le_three _)

/-- **`|responses| ≤ memRows` for every execution.** -/
theorem derivedResponseIO_length_le {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.derivedResponseIO.length ≤ cfg.memRows := by
  rw [← exec.memoryRows_length]
  exact ExactExecution.derivedResponseIO_length_le exec

/-- `R ≤ n ≤ 3R`.  The lower
    half restates `GatedIO.compRows_le_requests_length` (`GatedIOChip.lean:912`) — reproved here so
    this module does not import that chip — from the paper's unconditional `mem_record₁`. -/
theorem derivedRequestIO_length_between {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    cfg.compRows ≤ exec.derivedRequestIO.length ∧
      exec.derivedRequestIO.length ≤ 3 * cfg.compRows := by
  refine ⟨?_, derivedRequestIO_length_le exec⟩
  rw [ExactExecution.derivedRequestIO_eq_computeRows, List.length_map,
    ← exec.computeRows_length]
  exact one_le_length_flatMap exec.computeRows
    (fun row : ComputeTable.State × ComputeTable.DTcomp K =>
      NockVM.activeRequestRecords row.2.2.1)
    (fun row _ => activeRequestRecords_ne_nil _)

/-- **`kMem ≤ memRows` for every execution.**  `ExactExecution.memory_bfs_length`
(`Execution.lean:36`) identifies `memRows` with `(bfsForest memoryForest).length`, which is
`Walk.totalSize` of the forest (`Walk.lean:870`), and every root contributes at least itself
(`Walk.totalSize_flatMap_children`, `Walk.lean:719`).  So the memory-root count is itself a
row count, and is bounded by everything that bounds `memRows`. -/
theorem kMem_le_memRows {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    cfg.kMem ≤ cfg.memRows := by
  have hlen : exec.memoryForest.length ≤ Nock.Walk.totalSize exec.memoryForest := by
    have h := Nock.Walk.totalSize_flatMap_children exec.memoryForest
    omega
  rw [← exec.memory_root_count, ← exec.memory_bfs_length, Nock.Walk.bfsForest_length]
  exact hlen

end ExecutionLevel

/-! ## 2. A derived majorant for `p8Work`

Unfolding it:

    workload = 1 + (3 + 19·R)·(2Λ − 1) + topologyBound + axisWorkload + sizeWindowRootBound Λ

with `R` the compute-skeleton row count.  `topologyWorkload` (`RawTopologyRAP.lean:289`) is
`24·compRows + 8·memRows`, and `sizeWindowRootBound Λ = ∑_{d=1}^{Λ} d ≤ Λ²`
(`SizeWindowCounting.lean:182`).  So the only input that is not a row count or the paper's leaf
window is the axis workload. -/

/-- The explicit `p8Work` majorant: compute rows `R`, memory rows `M`, leaf window `Λ`, axis workload `A`. -/
def p8Majorant (R M Λ A : ℕ) : ℕ :=
  1 + (3 + 19 * R) * (2 * Λ) + (24 * R + 8 * M) + A + Λ * Λ

/-- `topologyWorkload` in the shape §2 uses. -/
theorem topologyWorkload_eq {F K : Type} [Field F] [Field K] [Algebra F K]
    (Rf : RawPlusIOSegmentedFamily F K) :
    topologyWorkload Rf = 24 * Rf.cfg.compRows + 8 * Rf.cfg.memRows := by
  simp only [topologyWorkload]; ring

section Workload

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable [charRing : CharP K (ringChar K)]

/-- **`workload` is majorized by `p8Majorant`.**  Derived from
`ProductionP8Containment.workload`'s own definition; the three inputs are the compute-row count,
a topology majorant, and an axis majorant.  Since the thirtieth move `workload` carries the Form R
λ-event summand (`formRUniformWorkload T` since the thirty-second) beside the axis summand, and since
the thirty-third the request-indexed pair summand `reqPairWorkload T Λ`; `p8Majorant`'s linear `A`
slot majorises the three together (`hax`). -/
theorem workload_le_p8Majorant
    (T : ProductionP8Containment.ProductionStrategy F K)
    (Λ topologyBound axisWorkload R M A : ℕ)
    (hrows : (SemanticStrategy.computeSkeletonRows T.skeleton).length ≤ R)
    (htop : topologyBound ≤ 24 * R + 8 * M)
    (hax : axisWorkload + ProductionP8Containment.formRUniformWorkload T +
      ProductionP8Containment.reqPairWorkload T Λ ≤ A) :
    ProductionP8Containment.workload T Λ topologyBound axisWorkload ≤ p8Majorant R M Λ A := by
  have hsw : sizeWindowRootBound Λ ≤ Λ * Λ := sizeWindowRootBound_le_square Λ
  have hcoll :
      (3 + 19 * (SemanticStrategy.computeSkeletonRows T.skeleton).length) * (2 * Λ - 1)
        ≤ (3 + 19 * R) * (2 * Λ) :=
    Nat.mul_le_mul (by omega) (Nat.sub_le _ _)
  simp only [ProductionP8Containment.workload, p8Majorant]
  omega

end Workload

/-! ### 2.3 The axis workload is bounded by the largest timestamp exponent

`templateAxisWorkload` (`TemplateAxisCounting.lean:387`) is `∑ᵢ (templateAxisPolynomial E i).natDegree`,
and `templateAxisPolynomial` (`:68`) is `countsP` of the root's memory tree
(`Nock/AxisBatching.lean:134`).  `countsP` only ever adds `X^e` for exponents `e` that literally
occur in the tree, so its degree is at most the largest such `e`.  This converts an unbounded
`Finset.sup` over `K` into a trace-local quantity. -/

/-- The largest timestamp exponent occurring in a memory tree. -/
def maxExp {K : Type*} : AxisBatching.MTree K → ℕ
  | .halt => 0
  | .decompose l r => max (maxExp l) (maxExp r)
  | .read e c => max e (maxExp c)
  | .verify e _ c => max e (maxExp c)

section AxisDegree

set_option maxHeartbeats 800000

variable {K : Type*} [Field K]

/-- `axis_indicator`'s degree is at most the largest exponent in the tree. -/
theorem natDegree_indP_le_maxExp (t : AxisBatching.MTree K) :
    (AxisBatching.MTree.indP t).natDegree ≤ maxExp t := by
  induction t with
  | halt => simp [AxisBatching.MTree.indP, maxExp]
  | decompose l r ihl ihr =>
      simp only [AxisBatching.MTree.indP, maxExp]
      refine (natDegree_C_mul_le _ _).trans ?_
      exact (natDegree_add_le _ _).trans (max_le_max ihl ihr)
  | read e c ih =>
      simp only [AxisBatching.MTree.indP, maxExp]
      refine (natDegree_sub_le _ _).trans ?_
      refine max_le (ih.trans (le_max_right e (maxExp c))) ?_
      exact (natDegree_C_mul_le _ _).trans
        ((natDegree_X_pow (R := K) e).trans_le (le_max_left e (maxExp c)))
  | verify e a c ih =>
      simp only [AxisBatching.MTree.indP, maxExp]
      refine (natDegree_add_le _ _).trans ?_
      refine max_le (ih.trans (le_max_right e (maxExp c))) ?_
      exact (natDegree_C_mul_le _ _).trans
        ((natDegree_X_pow (R := K) e).trans_le (le_max_left e (maxExp c)))

/-- **`axis_counts`'s degree is at most the largest exponent in the tree.**  The `decompose`
    branch's `C 2⁻¹` factor cannot raise the degree. -/
theorem natDegree_countsP_le_maxExp (t : AxisBatching.MTree K) :
    (AxisBatching.MTree.countsP t).natDegree ≤ maxExp t := by
  induction t with
  | halt => simp [AxisBatching.MTree.countsP, maxExp]
  | decompose l r ihl ihr =>
      simp only [AxisBatching.MTree.countsP, maxExp]
      refine (natDegree_add_le _ _).trans ?_
      refine max_le ?_ ((natDegree_indP_le_maxExp r).trans (le_max_right (maxExp l) (maxExp r)))
      refine (natDegree_add_le _ _).trans ?_
      refine max_le ((natDegree_add_le _ _).trans (max_le_max ihl ihr)) ?_
      refine (natDegree_C_mul_le _ _).trans ?_
      exact (natDegree_add_le _ _).trans
        (max_le_max (natDegree_indP_le_maxExp l) (natDegree_indP_le_maxExp r))
  | read e c ih =>
      simp only [AxisBatching.MTree.countsP, maxExp]
      refine (natDegree_sub_le _ _).trans ?_
      refine max_le (ih.trans (le_max_right e (maxExp c))) ?_
      exact (natDegree_C_mul_le _ _).trans
        ((natDegree_X_pow (R := K) e).trans_le (le_max_left e (maxExp c)))
  | verify e a c ih =>
      simp only [AxisBatching.MTree.countsP, maxExp]
      refine (natDegree_add_le _ _).trans ?_
      refine max_le (ih.trans (le_max_right e (maxExp c))) ?_
      exact (natDegree_C_mul_le _ _).trans
        ((natDegree_X_pow (R := K) e).trans_le (le_max_left e (maxExp c)))

end AxisDegree

/-! ## 3. At the real `ioWork` the bound is one fraction over `|K|`

`goldilocksFailureBoundK` (`ExtensionChallenges.lean:790`) is
`(p8Work + 494N + 21 + 33M)/|K| + ioWork/|K|²`.  Substituting the *actual*
`ioWork = |K|·(28n² + 4n)` cancels one power of `|K|`, so the entire figure is
`(p8Work + 494N + 21 + 33M + 28n² + 4n)/|K|`.  This is why no `ioWork` ceiling is needed: the
`|K|` in `ioFailureUnionBound` was never real slack. -/

/-- The total numerator: everything the bound charges, over one `|K|`. -/
def totalWork (p8Work N M n : ℕ) : ℕ :=
  p8Work + 494 * N + 21 + 33 * M + 28 * n * n + 4 * n

/-- **The collapse.**  With the real IO workload the two summands become one. -/
theorem boundK_at_real_io (p8Work N M n : ℕ) :
    ExtensionChallenges.goldilocksFailureBoundK p8Work
        (ioFailureUnionBound 8 n n (Fintype.card Nock.Field.K)) N M
      = (totalWork p8Work N M n : ℚ) / (cardKGold : ℚ) := by
  rw [ExtensionChallenges.goldilocksFailureBoundK_eq, ioFailureUnionBound_eight, card_K_gold]
  have hk : ((cardKGold : ℕ) : ℚ) ≠ 0 := by norm_num
  simp only [totalWork, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  ring

/-- `ioFailureUnionBound` is monotone in the two list lengths, so a record-count majorant
suffices. -/
theorem ioFailureUnionBound_mono (m k₁ k₂ n cardK : ℕ) (h1 : k₁ ≤ n) (h2 : k₂ ≤ n) :
    ioFailureUnionBound m k₁ k₂ cardK ≤ ioFailureUnionBound m n n cardK := by
  simp only [ioFailureUnionBound]
  have hs : k₁ + k₂ ≤ n + n := Nat.add_le_add h1 h2
  exact Nat.add_le_add
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul hs hs)))
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hs))

/-- **The tight criterion.**  `b` bits of soundness hold exactly when the total numerator times
`2^b` fits under `|K|`.  Everything below is an instance of this. -/
theorem boundK_lt_of_totalWork (p8Work N M n b : ℕ)
    (h : totalWork p8Work N M n * 2 ^ b < cardKGold) :
    ExtensionChallenges.goldilocksFailureBoundK p8Work
        (ioFailureUnionBound 8 n n (Fintype.card Nock.Field.K)) N M
      < 1 / (2 : ℚ) ^ b := by
  rw [boundK_at_real_io]
  rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
  have hq : ((totalWork p8Work N M n * 2 ^ b : ℕ) : ℚ) < ((cardKGold : ℕ) : ℚ) := by
    exact_mod_cast h
  push_cast at hq ⊢
  linarith

/-! ### 3.1 The `16^65` ceiling, refuted as a compiled statement

`ExtensionChallenges.soundnessK_at_paper_configuration` (`ExtensionChallenges.lean:833`) and
`GoldilocksParameters.soundness_at_paper_configuration` (`GoldilocksParameters.lean:391`) assume
`hio : ioWork ≤ 16 ^ 65 = 2 ^ 260`.  The three statements below locate that ceiling exactly. -/

/-- The largest record count the `16^65` ceiling admits: `n* = 3 246 690 102 ≈ 2^31.596`. -/
abbrev ioNStar : ℕ := 3246690102

theorem ioWork_le_at_ioNStar :
    ioFailureUnionBound 8 ioNStar ioNStar (Fintype.card Nock.Field.K) ≤ 16 ^ 65 := by
  rw [ioFailureUnionBound_eight, card_K_gold]; norm_num

theorem not_ioWork_le_at_ioNStar_succ :
    ¬ ioFailureUnionBound 8 (ioNStar + 1) (ioNStar + 1) (Fintype.card Nock.Field.K) ≤ 16 ^ 65 := by
  rw [ioFailureUnionBound_eight, card_K_gold]; norm_num

/-- **Two memory records per compute row already breaks the ceiling at `2^31` rows.**
`n* < 2 · 2^31`, so a program whose rows are `OP{0,2,5,7,8}`
cannot satisfy `hio` at the row count `soundnessK_at_paper_configuration` names.  Three records is worse still. -/
theorem not_ioWork_le_at_two_records_per_row :
    ¬ ioFailureUnionBound 8 (2 * 2 ^ 31) (2 * 2 ^ 31) (Fintype.card Nock.Field.K) ≤ 16 ^ 65 := by
  rw [ioFailureUnionBound_eight, card_K_gold]; norm_num

/-! ## 4. The uniform size majorant

With every size parameter at most `S`, the total numerator is `291S² + 578S + 22`.  The three
quadratic contributions are `38S²` from the census/window product, `S²` from
`sizeWindowRootBound`, and `252S²` from `28n²` at `n ≤ 3S`. -/

/-- **`p8Work ≤ 39S² + 39S + 1` at uniform size `S`.**  The two quadratic contributions are
`38S²` from the census/window product `(3 + 19R)(2Λ − 1)` and `S²` from `sizeWindowRootBound Λ`.
At `S = 2^32` this is `≈ 2^69.29`, i.e. **larger** than the `2^62` majorant the `p8Work ≤ 2^60`
ceiling was meant to cover — but see `p8Majorant_le_io_term`: it is still the smaller of the two
quadratic terms, so it is not what limits the figure. -/
theorem p8Majorant_le_of_size (S R M Λ A : ℕ)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ S) :
    p8Majorant R M Λ A ≤ 39 * (S * S) + 39 * S + 1 := by
  have a1 : (3 + 19 * R) * (2 * Λ) ≤ (3 + 19 * S) * (2 * S) :=
    Nat.mul_le_mul (by omega) (by omega)
  have a1' : (3 + 19 * S) * (2 * S) = 38 * (S * S) + 6 * S := by ring
  have a2 : Λ * Λ ≤ S * S := Nat.mul_le_mul hΛ hΛ
  simp only [p8Majorant]
  rw [a1'] at a1
  linarith

/-- **`p8Work` does not bind: it is dominated by the IO term.**  So the
answer to "does the `p8Work` ceiling matter" is no — but *not* because `p8Work` is negligible
(`2^62/|K| = 2^-130`); it is because the two quadratic terms sit in a fixed `39 : 252` ratio, and
`p8Work` costs about `0.2` bits of the final figure. -/
theorem p8Majorant_le_io_term (S R M Λ A : ℕ) (hS : 1 ≤ S)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ S) :
    p8Majorant R M Λ A ≤ 28 * (3 * S) * (3 * S) := by
  have h := p8Majorant_le_of_size S R M Λ A hR hM hΛ hA
  have hSS : S ≤ S * S := Nat.le_mul_of_pos_left S hS
  have h1 : (1 : ℕ) ≤ S * S := le_trans hS hSS
  have he : 28 * (3 * S) * (3 * S) = 252 * (S * S) := by ring
  rw [he]
  linarith

theorem totalWork_le_of_size (S R M Λ A p8Work n : ℕ)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ S)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) (hn3 : n ≤ 3 * S) :
    totalWork p8Work R M n ≤ 291 * (S * S) + 578 * S + 22 := by
  have h1 : p8Majorant R M Λ A ≤ 39 * (S * S) + 39 * S + 1 :=
    p8Majorant_le_of_size S R M Λ A hR hM hΛ hA
  have h2 : 28 * n * n ≤ 252 * (S * S) := by
    calc 28 * n * n ≤ 28 * (3 * S) * (3 * S) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 28 hn3) hn3
      _ = 252 * (S * S) := by ring
  have h3 : 4 * n ≤ 12 * S := by omega
  simp only [totalWork]
  linarith

/-- **The arithmetic core.**  For every `r ≥ 2`, the uniform-size numerator at `S = 2^r` clears
`2^(183 − 2r)`.  Written as `2r + b = 183` so no natural subtraction appears. -/
theorem sizeWork_lt_cardK (r b : ℕ) (hr : 2 ≤ r) (hb : 2 * r + b = 183) :
    (291 * (2 ^ r * 2 ^ r) + 578 * 2 ^ r + 22) * 2 ^ b < cardKGold := by
  have h1 : (2 : ℕ) ^ r * 2 ^ r * 2 ^ b = 2 ^ 183 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have h2 : (2 : ℕ) ^ r * 2 ^ b ≤ 2 ^ 181 := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ^ b ≤ 2 ^ 179 := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc (291 * (2 ^ r * 2 ^ r) + 578 * 2 ^ r + 22) * 2 ^ b
      = 291 * (2 ^ r * 2 ^ r * 2 ^ b) + 578 * (2 ^ r * 2 ^ b) + 22 * 2 ^ b := by ring
    _ ≤ 291 * 2 ^ 183 + 578 * 2 ^ 181 + 22 * 2 ^ 179 := by
        rw [h1]
        exact Nat.add_le_add
          (Nat.add_le_add_left (Nat.mul_le_mul_left 578 h2) _)
          (Nat.mul_le_mul_left 22 h3)
    _ < cardKGold := by norm_num

/-- **And `183 − 2r` is the best this majorant gives.**  One more bit fails for every `r`:
`291 · 2^184 > |K|`, and the numerator's leading term alone already reaches it. -/
theorem sizeWork_not_lt_cardK (r b : ℕ) (hb : 2 * r + b = 183) :
    ¬ ((291 * (2 ^ r * 2 ^ r) + 578 * 2 ^ r + 22) * 2 ^ (b + 1) < cardKGold) := by
  have h1 : (2 : ℕ) ^ r * 2 ^ r * 2 ^ (b + 1) = 2 ^ 184 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hA : 291 * (2 ^ r * 2 ^ r) ≤ 291 * (2 ^ r * 2 ^ r) + 578 * 2 ^ r + 22 := by omega
  have hstep : 291 * (2 ^ r * 2 ^ r) * 2 ^ (b + 1)
      ≤ (291 * (2 ^ r * 2 ^ r) + 578 * 2 ^ r + 22) * 2 ^ (b + 1) :=
    Nat.mul_le_mul_right _ hA
  have heq : 291 * (2 ^ r * 2 ^ r) * 2 ^ (b + 1) = 291 * 2 ^ 184 := by
    rw [mul_assoc, h1]
  rw [heq] at hstep
  have hcard : cardKGold ≤ 291 * 2 ^ 184 := by norm_num
  exact Nat.not_lt.mpr (le_trans hcard hstep)

/-! ## 5. The parametric theorem

**For every program whose compute rows, memory rows, leaf window and axis workload are all at most
`2^r` (`r ≥ 2`), the false-acceptance bound is below `2^-(183 − 2r)`** — with the memory-record
budget `n ≤ 3·2^r` *derived* from opcode arity (§1 gives `n ≤ 3R` for every execution, and
`R ≤ 2^r`), and no ceiling on `ioWork` anywhere.  `b` is written as `2r + b = 183` to keep natural
subtraction out of the statement; the bound is tight for this majorant, i.e. `b + 1` fails. -/

theorem soundness_at_row_budget (r b R M Λ A p8Work n : ℕ)
    (hr : 2 ≤ r) (hb : 2 * r + b = 183)
    (hR : R ≤ 2 ^ r) (hM : M ≤ 2 ^ r) (hΛ : Λ ≤ 2 ^ r) (hA : A ≤ 2 ^ r)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) (hn : n ≤ 3 * 2 ^ r) :
    ExtensionChallenges.goldilocksFailureBoundK p8Work
        (ioFailureUnionBound 8 n n (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ b := by
  refine boundK_lt_of_totalWork _ _ _ _ _ ?_
  refine lt_of_le_of_lt
    (Nat.mul_le_mul_right _ (totalWork_le_of_size (2 ^ r) R M Λ A p8Work n hR hM hΛ hA hp8 hn))
    (sizeWork_lt_cardK r b hr hb)

/-- The same statement with a general request/response pair, using §3's monotonicity: the two
derived IO lists need only be *bounded* by the record budget `n`, which §1 supplies
unconditionally (`|requests| ≤ 3·compRows`, `|responses| ≤ memRows`). -/
theorem soundness_at_row_budget' (r b R M Λ A p8Work k₁ k₂ n : ℕ)
    (hr : 2 ≤ r) (hb : 2 * r + b = 183)
    (hR : R ≤ 2 ^ r) (hM : M ≤ 2 ^ r) (hΛ : Λ ≤ 2 ^ r) (hA : A ≤ 2 ^ r)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) (hn : n ≤ 3 * 2 ^ r)
    (h1 : k₁ ≤ n) (h2 : k₂ ≤ n) :
    ExtensionChallenges.goldilocksFailureBoundK p8Work
        (ioFailureUnionBound 8 k₁ k₂ (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ b := by
  refine lt_of_le_of_lt ?_ (soundness_at_row_budget r b R M Λ A p8Work n hr hb hR hM hΛ hA hp8 hn)
  exact ExtensionChallenges.boundK_mono R M (le_refl _)
    (ioFailureUnionBound_mono 8 k₁ k₂ n _ h1 h2)

/-! ## 5.1 The axis workload is allowed to be *quadratic* at no cost

`A` enters `p8Majorant` **linearly and once**, while the numerator's budget is quadratic: at
`S = 2^r` the leading coefficient may grow to `511` before `(… )·2^(183−2r) < |K|` fails
(`sizeWorkQuad_not_lt_cardK_at_512` pins that ceiling).  §4 spends `291` of it, so raising the
axis allowance from `A ≤ S` to `A ≤ 4S²` moves the coefficient `291 → 295` and **does not move
`b` at all**.  That matters because the axis workload's real shape is a *product*: the paper's
axis polynomial is one per memory root, of degree at most the largest
timestamp exponent, so the honest majorant is `kMem · L` — quadratic in the trace, not linear.

`b = 183 − 2r` is unchanged; the statements below are strictly more general than §4/§5's, since
`A ≤ S ≤ 4·S·S` whenever `1 ≤ S`. -/

/-- **`p8Work ≤ 43S² + 39S + 1` with a quadratic axis allowance.**  Compare
`p8Majorant_le_of_size`'s `39S² + 39S + 1`: the axis summand contributes `4S²` instead of `S`. -/
theorem p8Majorant_le_of_size_quadAxis (S R M Λ A : ℕ)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ 4 * (S * S)) :
    p8Majorant R M Λ A ≤ 43 * (S * S) + 39 * S + 1 := by
  have a1 : (3 + 19 * R) * (2 * Λ) ≤ (3 + 19 * S) * (2 * S) :=
    Nat.mul_le_mul (by omega) (by omega)
  have a1' : (3 + 19 * S) * (2 * S) = 38 * (S * S) + 6 * S := by ring
  have a2 : Λ * Λ ≤ S * S := Nat.mul_le_mul hΛ hΛ
  simp only [p8Majorant]
  rw [a1'] at a1
  linarith

theorem totalWork_le_of_size_quadAxis (S R M Λ A p8Work n : ℕ)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ 4 * (S * S))
    (hp8 : p8Work ≤ p8Majorant R M Λ A) (hn3 : n ≤ 3 * S) :
    totalWork p8Work R M n ≤ 295 * (S * S) + 578 * S + 22 := by
  have h1 : p8Majorant R M Λ A ≤ 43 * (S * S) + 39 * S + 1 :=
    p8Majorant_le_of_size_quadAxis S R M Λ A hR hM hΛ hA
  have h2 : 28 * n * n ≤ 252 * (S * S) := by
    calc 28 * n * n ≤ 28 * (3 * S) * (3 * S) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 28 hn3) hn3
      _ = 252 * (S * S) := by ring
  have h3 : 4 * n ≤ 12 * S := by omega
  simp only [totalWork]
  linarith

/-- **The arithmetic core, quadratic-axis version.**  `295` in place of §4's `291`; the same
`2r + b = 183`. -/
theorem sizeWorkQuad_lt_cardK (r b : ℕ) (hr : 2 ≤ r) (hb : 2 * r + b = 183) :
    (295 * (2 ^ r * 2 ^ r) + 578 * 2 ^ r + 22) * 2 ^ b < cardKGold := by
  have h1 : (2 : ℕ) ^ r * 2 ^ r * 2 ^ b = 2 ^ 183 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have h2 : (2 : ℕ) ^ r * 2 ^ b ≤ 2 ^ 181 := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ^ b ≤ 2 ^ 179 := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc (295 * (2 ^ r * 2 ^ r) + 578 * 2 ^ r + 22) * 2 ^ b
      = 295 * (2 ^ r * 2 ^ r * 2 ^ b) + 578 * (2 ^ r * 2 ^ b) + 22 * 2 ^ b := by ring
    _ ≤ 295 * 2 ^ 183 + 578 * 2 ^ 181 + 22 * 2 ^ 179 := by
        rw [h1]
        exact Nat.add_le_add
          (Nat.add_le_add_left (Nat.mul_le_mul_left 578 h2) _)
          (Nat.mul_le_mul_left 22 h3)
    _ < cardKGold := by norm_num

/-- **`183 − 2r` is still the best after the relaxation.**  One more bit fails for every `r`,
exactly as `sizeWork_not_lt_cardK` records for §4's numerator. -/
theorem sizeWorkQuad_not_lt_cardK (r b : ℕ) (hb : 2 * r + b = 183) :
    ¬ ((295 * (2 ^ r * 2 ^ r) + 578 * 2 ^ r + 22) * 2 ^ (b + 1) < cardKGold) := by
  have h1 : (2 : ℕ) ^ r * 2 ^ r * 2 ^ (b + 1) = 2 ^ 184 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hA : 295 * (2 ^ r * 2 ^ r) ≤ 295 * (2 ^ r * 2 ^ r) + 578 * 2 ^ r + 22 := by omega
  have hstep : 295 * (2 ^ r * 2 ^ r) * 2 ^ (b + 1)
      ≤ (295 * (2 ^ r * 2 ^ r) + 578 * 2 ^ r + 22) * 2 ^ (b + 1) :=
    Nat.mul_le_mul_right _ hA
  have heq : 295 * (2 ^ r * 2 ^ r) * 2 ^ (b + 1) = 295 * 2 ^ 184 := by
    rw [mul_assoc, h1]
  rw [heq] at hstep
  have hcard : cardKGold ≤ 295 * 2 ^ 184 := by norm_num
  exact Nat.not_lt.mpr (le_trans hcard hstep)

/-- **The coefficient ceiling, measured.**  `512 · 2^183 > |K|`, so the leading coefficient of
the uniform-size numerator may not exceed `511`.  §4 spends `291` and §5.1 spends `295`; that is
the slack the quadratic axis allowance is paid out of. -/
theorem sizeWorkQuad_not_lt_cardK_at_512 (r b : ℕ) (hb : 2 * r + b = 183) :
    ¬ (512 * (2 ^ r * 2 ^ r)) * 2 ^ b < cardKGold := by
  have h1 : (2 : ℕ) ^ r * 2 ^ r * 2 ^ b = 2 ^ 183 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have heq : (512 * (2 ^ r * 2 ^ r)) * 2 ^ b = 512 * 2 ^ 183 := by
    rw [mul_assoc, h1]
  rw [heq]
  have hcard : cardKGold ≤ 512 * 2 ^ 183 := by norm_num
  exact Nat.not_lt.mpr hcard

theorem soundness_at_row_budget_quadAxis (r b R M Λ A p8Work n : ℕ)
    (hr : 2 ≤ r) (hb : 2 * r + b = 183)
    (hR : R ≤ 2 ^ r) (hM : M ≤ 2 ^ r) (hΛ : Λ ≤ 2 ^ r) (hA : A ≤ 4 * (2 ^ r * 2 ^ r))
    (hp8 : p8Work ≤ p8Majorant R M Λ A) (hn : n ≤ 3 * 2 ^ r) :
    ExtensionChallenges.goldilocksFailureBoundK p8Work
        (ioFailureUnionBound 8 n n (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ b := by
  refine boundK_lt_of_totalWork _ _ _ _ _ ?_
  refine lt_of_le_of_lt
    (Nat.mul_le_mul_right _
      (totalWork_le_of_size_quadAxis (2 ^ r) R M Λ A p8Work n hR hM hΛ hA hp8 hn))
    (sizeWorkQuad_lt_cardK r b hr hb)

theorem soundness_at_row_budget_quadAxis' (r b R M Λ A p8Work k₁ k₂ n : ℕ)
    (hr : 2 ≤ r) (hb : 2 * r + b = 183)
    (hR : R ≤ 2 ^ r) (hM : M ≤ 2 ^ r) (hΛ : Λ ≤ 2 ^ r) (hA : A ≤ 4 * (2 ^ r * 2 ^ r))
    (hp8 : p8Work ≤ p8Majorant R M Λ A) (hn : n ≤ 3 * 2 ^ r)
    (h1 : k₁ ≤ n) (h2 : k₂ ≤ n) :
    ExtensionChallenges.goldilocksFailureBoundK p8Work
        (ioFailureUnionBound 8 k₁ k₂ (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ b := by
  refine lt_of_le_of_lt ?_
    (soundness_at_row_budget_quadAxis r b R M Λ A p8Work n hr hb hR hM hΛ hA hp8 hn)
  exact ExtensionChallenges.boundK_mono R M (le_refl _)
    (ioFailureUnionBound_mono 8 k₁ k₂ n _ h1 h2)

/-! ## 5.2 An octic axis allowance (thirtieth move)

Since the thirtieth move `workload` carries the Form R λ-event summand `fixedFormRWorkload` in the
same linear slot as the axis workload; at the deployable maximum the pair is `≤ 3·2^64 + 4·2^64`,
so the allowance is raised to `A ≤ 8S²`.  The coefficient moves `295 → 299`, still far below the
`511` ceiling (`sizeWorkQuad_not_lt_cardK_at_512`): `b = 183 − 2r` is unchanged. -/

theorem p8Majorant_le_of_size_octAxis (S R M Λ A : ℕ)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ 8 * (S * S)) :
    p8Majorant R M Λ A ≤ 47 * (S * S) + 39 * S + 1 := by
  have a1 : (3 + 19 * R) * (2 * Λ) ≤ (3 + 19 * S) * (2 * S) :=
    Nat.mul_le_mul (by omega) (by omega)
  have a1' : (3 + 19 * S) * (2 * S) = 38 * (S * S) + 6 * S := by ring
  have a2 : Λ * Λ ≤ S * S := Nat.mul_le_mul hΛ hΛ
  simp only [p8Majorant]
  rw [a1'] at a1
  linarith

theorem totalWork_le_of_size_octAxis (S R M Λ A p8Work n : ℕ)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ 8 * (S * S))
    (hp8 : p8Work ≤ p8Majorant R M Λ A) (hn3 : n ≤ 3 * S) :
    totalWork p8Work R M n ≤ 299 * (S * S) + 578 * S + 22 := by
  have h1 : p8Majorant R M Λ A ≤ 47 * (S * S) + 39 * S + 1 :=
    p8Majorant_le_of_size_octAxis S R M Λ A hR hM hΛ hA
  have h2 : 28 * n * n ≤ 252 * (S * S) := by
    calc 28 * n * n ≤ 28 * (3 * S) * (3 * S) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 28 hn3) hn3
      _ = 252 * (S * S) := by ring
  have h3 : 4 * n ≤ 12 * S := by omega
  simp only [totalWork]
  linarith

theorem sizeWorkOct_lt_cardK (r b : ℕ) (hr : 2 ≤ r) (hb : 2 * r + b = 183) :
    (299 * (2 ^ r * 2 ^ r) + 578 * 2 ^ r + 22) * 2 ^ b < cardKGold := by
  have h1 : (2 : ℕ) ^ r * 2 ^ r * 2 ^ b = 2 ^ 183 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have h2 : (2 : ℕ) ^ r * 2 ^ b ≤ 2 ^ 181 := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ^ b ≤ 2 ^ 179 := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc (299 * (2 ^ r * 2 ^ r) + 578 * 2 ^ r + 22) * 2 ^ b
      = 299 * (2 ^ r * 2 ^ r * 2 ^ b) + 578 * (2 ^ r * 2 ^ b) + 22 * 2 ^ b := by ring
    _ ≤ 299 * 2 ^ 183 + 578 * 2 ^ 181 + 22 * 2 ^ 179 := by
        rw [h1]
        exact Nat.add_le_add
          (Nat.add_le_add_left (Nat.mul_le_mul_left 578 h2) _)
          (Nat.mul_le_mul_left 22 h3)
    _ < cardKGold := by norm_num

theorem soundness_at_row_budget_octAxis' (r b R M Λ A p8Work k₁ k₂ n : ℕ)
    (hr : 2 ≤ r) (hb : 2 * r + b = 183)
    (hR : R ≤ 2 ^ r) (hM : M ≤ 2 ^ r) (hΛ : Λ ≤ 2 ^ r) (hA : A ≤ 8 * (2 ^ r * 2 ^ r))
    (hp8 : p8Work ≤ p8Majorant R M Λ A) (hn : n ≤ 3 * 2 ^ r)
    (h1 : k₁ ≤ n) (h2 : k₂ ≤ n) :
    ExtensionChallenges.goldilocksFailureBoundK p8Work
        (ioFailureUnionBound 8 k₁ k₂ (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ b := by
  refine lt_of_le_of_lt ?_ (?_ : ExtensionChallenges.goldilocksFailureBoundK p8Work
        (ioFailureUnionBound 8 n n (Fintype.card Nock.Field.K)) R M < 1 / (2 : ℚ) ^ b)
  · exact ExtensionChallenges.boundK_mono R M (le_refl _)
      (ioFailureUnionBound_mono 8 k₁ k₂ n _ h1 h2)
  · refine boundK_lt_of_totalWork _ _ _ _ _ ?_
    refine lt_of_le_of_lt
      (Nat.mul_le_mul_right _
        (totalWork_le_of_size_octAxis (2 ^ r) R M Λ A p8Work n hR hM hΛ hA hp8 hn))
      (sizeWorkOct_lt_cardK r b hr hb)

/-! ## 6. The deployable maximum, and the corollaries

`GoldilocksParameters.orbit_height_le` (`GoldilocksParameters.lean:203`) proves every
`OrbitDomain K` over Goldilocks has `h ≤ 32`, because `v₂(p³ − 1) = 32`.  `ExactConfig.compRows_le`
and `memRows_le` (`Config.lean:112,114`) bound both row counts by `2 ^ orbit.h`.  So the `r = 32`
instance needs **no row hypothesis at all**: it is a property of the type. -/

/-- Every Goldilocks `ExactConfig` has at most `2^32` compute rows — derived, not assumed. -/
theorem compRows_le_two_pow_32 (cfg : ExactConfig Nock.Field.Fp Nock.Field.K) :
    cfg.compRows ≤ 2 ^ 32 :=
  le_trans cfg.compRows_le (Nat.pow_le_pow_right (by norm_num) (orbit_height_le cfg.orbit))

/-- Every Goldilocks `ExactConfig` has at most `2^32` memory rows — derived, not assumed. -/
theorem memRows_le_two_pow_32 (cfg : ExactConfig Nock.Field.Fp Nock.Field.K) :
    cfg.memRows ≤ 2 ^ 32 :=
  le_trans cfg.memRows_le (Nat.pow_le_pow_right (by norm_num) (orbit_height_le cfg.orbit))

/-- **119 bits at the deployable maximum, `2^32` rows.** -/
theorem soundness_at_two_pow_32 (R M Λ A p8Work n : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) (hn : n ≤ 3 * R) :
    ExtensionChallenges.goldilocksFailureBoundK p8Work
        (ioFailureUnionBound 8 n n (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 119 :=
  soundness_at_row_budget 32 119 R M Λ A p8Work n (by norm_num) (by norm_num)
    hR hM hΛ hA hp8 (le_trans hn (Nat.mul_le_mul_left 3 hR))

/-- **121 bits at `2^31` rows.** -/
theorem soundness_at_two_pow_31 (R M Λ A p8Work n : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) (hn : n ≤ 3 * R) :
    ExtensionChallenges.goldilocksFailureBoundK p8Work
        (ioFailureUnionBound 8 n n (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 121 :=
  soundness_at_row_budget 31 121 R M Λ A p8Work n (by norm_num) (by norm_num)
    hR hM hΛ hA hp8 (le_trans hn (Nat.mul_le_mul_left 3 hR))

/-- **143 bits at a million (`2^20`) rows.** -/
theorem soundness_at_two_pow_20 (R M Λ A p8Work n : ℕ)
    (hR : R ≤ 2 ^ 20) (hM : M ≤ 2 ^ 20) (hΛ : Λ ≤ 2 ^ 20) (hA : A ≤ 2 ^ 20)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) (hn : n ≤ 3 * R) :
    ExtensionChallenges.goldilocksFailureBoundK p8Work
        (ioFailureUnionBound 8 n n (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 143 :=
  soundness_at_row_budget 20 143 R M Λ A p8Work n (by norm_num) (by norm_num)
    hR hM hΛ hA hp8 (le_trans hn (Nat.mul_le_mul_left 3 hR))

/-- **The headline: an execution-level figure with the record count derived.**  For *any*
`ExactExecution` over Goldilocks, with the leaf window and the axis workload at most `2^32`, the
false-acceptance bound at the execution's own derived request list is below `2^-119`.  The row
counts come from the orbit (`v₂(p³−1) = 32`) and the record count from opcode arity; nothing about `ioWork` is assumed. -/
theorem soundness_for_execution {cfg : ExactConfig Nock.Field.Fp Nock.Field.K}
    (exec : ExactExecution cfg) (Λ A p8Work : ℕ)
    (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant cfg.compRows cfg.memRows Λ A) :
    ExtensionChallenges.goldilocksFailureBoundK p8Work
        (ioFailureUnionBound 8 exec.derivedRequestIO.length exec.derivedResponseIO.length
          (Fintype.card Nock.Field.K))
        cfg.compRows cfg.memRows
      < 1 / (2 : ℚ) ^ 119 := by
  refine soundness_at_row_budget' 32 119 cfg.compRows cfg.memRows Λ A p8Work
    exec.derivedRequestIO.length exec.derivedResponseIO.length (3 * 2 ^ 32)
    (by norm_num) (by norm_num)
    (compRows_le_two_pow_32 cfg) (memRows_le_two_pow_32 cfg) hΛ hA hp8 (le_refl _)
    ?_ ?_
  · exact le_trans (derivedRequestIO_length_le exec)
      (Nat.mul_le_mul_left 3 (compRows_le_two_pow_32 cfg))
  · exact le_trans (derivedResponseIO_length_le exec)
      (le_trans (memRows_le_two_pow_32 cfg) (by norm_num))


/-- The row caps do not use the base field: only `cfg.orbit` and `v₂(p³−1) = 32`.  Generalized
from `compRows_le_two_pow_32` so the generated path, whose base field is a variable, can use it. -/
theorem compRows_le_two_pow_32' {F : Type} [Field F] [Algebra F Nock.Field.K]
    (cfg : ExactConfig F Nock.Field.K) : cfg.compRows ≤ 2 ^ 32 :=
  le_trans cfg.compRows_le (Nat.pow_le_pow_right (by norm_num) (orbit_height_le cfg.orbit))

theorem memRows_le_two_pow_32' {F : Type} [Field F] [Algebra F Nock.Field.K]
    (cfg : ExactConfig F Nock.Field.K) : cfg.memRows ≤ 2 ^ 32 :=
  le_trans cfg.memRows_le (Nat.pow_le_pow_right (by norm_num) (orbit_height_le cfg.orbit))

/-- **The headline, with the axis workload allowed its honest quadratic shape.**  Identical to
`soundness_for_execution` except that the axis majorant may be as large as `4·2^32·2^32 = 2^66`
— which is what `kMem · L` costs at the deployable maximum (`kMem ≤ memRows ≤ 2^32` by
`kMem_le_memRows`, `L ≤ 3·compRows ≤ 3·2^32` by §1).  Still **119 bits**. -/
theorem soundness_for_execution_quadAxis {F : Type} [Field F] [Algebra F Nock.Field.K]
    {cfg : ExactConfig F Nock.Field.K}
    (exec : ExactExecution cfg) (Λ A p8Work : ℕ)
    (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 4 * (2 ^ 32 * 2 ^ 32))
    (hp8 : p8Work ≤ p8Majorant cfg.compRows cfg.memRows Λ A) :
    ExtensionChallenges.goldilocksFailureBoundK p8Work
        (ioFailureUnionBound 8 exec.derivedRequestIO.length exec.derivedResponseIO.length
          (Fintype.card Nock.Field.K))
        cfg.compRows cfg.memRows
      < 1 / (2 : ℚ) ^ 119 := by
  refine soundness_at_row_budget_quadAxis' 32 119 cfg.compRows cfg.memRows Λ A p8Work
    exec.derivedRequestIO.length exec.derivedResponseIO.length (3 * 2 ^ 32)
    (by norm_num) (by norm_num)
    (compRows_le_two_pow_32' cfg) (memRows_le_two_pow_32' cfg) hΛ hA hp8 (le_refl _)
    ?_ ?_
  · exact le_trans (derivedRequestIO_length_le exec)
      (Nat.mul_le_mul_left 3 (compRows_le_two_pow_32' cfg))
  · exact le_trans (derivedResponseIO_length_le exec)
      (le_trans (memRows_le_two_pow_32' cfg) (by norm_num))

/-- **`soundness_for_execution_quadAxis` at the octic allowance `A ≤ 8·2^32·2^32`** (thirtieth
move: the axis and Form R λ-event summands share `p8Majorant`'s `A` slot).  Still **119 bits**. -/
theorem soundness_for_execution_octAxis {F : Type} [Field F] [Algebra F Nock.Field.K]
    {cfg : ExactConfig F Nock.Field.K}
    (exec : ExactExecution cfg) (Λ A p8Work : ℕ)
    (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 8 * (2 ^ 32 * 2 ^ 32))
    (hp8 : p8Work ≤ p8Majorant cfg.compRows cfg.memRows Λ A) :
    ExtensionChallenges.goldilocksFailureBoundK p8Work
        (ioFailureUnionBound 8 exec.derivedRequestIO.length exec.derivedResponseIO.length
          (Fintype.card Nock.Field.K))
        cfg.compRows cfg.memRows
      < 1 / (2 : ℚ) ^ 119 := by
  refine soundness_at_row_budget_octAxis' 32 119 cfg.compRows cfg.memRows Λ A p8Work
    exec.derivedRequestIO.length exec.derivedResponseIO.length (3 * 2 ^ 32)
    (by norm_num) (by norm_num)
    (compRows_le_two_pow_32' cfg) (memRows_le_two_pow_32' cfg) hΛ hA hp8 (le_refl _)
    ?_ ?_
  · exact le_trans (derivedRequestIO_length_le exec)
      (Nat.mul_le_mul_left 3 (compRows_le_two_pow_32' cfg))
  · exact le_trans (derivedResponseIO_length_le exec)
      (le_trans (memRows_le_two_pow_32' cfg) (by norm_num))

/-! ## 7.

Every figure above is stated about `ExtensionChallenges.goldilocksFailureBoundK`, the
`𝕂`-typed bound `(p8Work + 494N + 21 + 33M)/|𝕂| + ioWork/|𝕂|²`.  The first dominates the second term by term
(`21 ≥ 1`, `33·M ≥ 19·M`, identical `ioWork/|𝕂|²`), so one monotonicity lemma transfers
`121`/`119` to the consumed bound with **no** `ioWork` ceiling anywhere.  The paper's own claim at `k = 2^31` is `121`. -/

/-- **Term-by-term domination of the consumed bound by the `𝕂`-bound.**  At the same four
arguments, `goldilocksTrimmedFailureBound p8Work ioWork N M`
(`GoldilocksParameters.lean::goldilocksTrimmedFailureBound`, i.e. the capstone's
`optimizedTrimmedProductionFailureProbabilityBound` instantiated at `|𝕂|`, `|𝔽|`) is at most
`ExtensionChallenges.goldilocksFailureBoundK p8Work ioWork N M`: the first numerator carries
`p8Work` where the second carries `p8Work + 494N + 21 + 33·M`, and the `ioWork/|𝕂|²` summand is
identical -/
theorem trimmed_le_goldilocksFailureBoundK (p8Work ioWork N M : ℕ) :
    goldilocksTrimmedFailureBound p8Work ioWork N M
      ≤ ExtensionChallenges.goldilocksFailureBoundK p8Work ioWork N M := by
  rw [goldilocksTrimmedFailureBound_eq, ExtensionChallenges.goldilocksFailureBoundK_eq]
  have hnum : (p8Work : ℚ)
      ≤ (p8Work + 494 * N + 21 + 33 * M : ℚ) := by
    have h : p8Work ≤ p8Work + 494 * N + 21 + 33 * M := by omega
    exact_mod_cast h
  have s1 : (p8Work : ℚ) / (cardKGold : ℚ)
      ≤ (p8Work + 494 * N + 21 + 33 * M : ℚ) / (cardKGold : ℚ) := by
    gcongr
  linarith

/-- **121 bits for real programs at `2^31` compute rows — at the *consumed* bound.**  Under
exactly `soundness_at_two_pow_31`'s hypotheses — `R, M, Λ, A ≤ 2^31`, `p8Work` bounded by the
tree's own `p8Majorant`, and the record count `n ≤ 3·R` that §1 derives from opcode arity —
the consumed trimmed bound is below `2^-121`.  No `ioWork` ceiling is assumed anywhere; this
is the headline the `2^-123` of `trimmed_soundness_at_paper_configuration` cannot honestly
carry, because its `hio : ioWork ≤ 16^65` fails of every real execution at `N = 2^31` with
two or more records per row (`not_ioWork_le_at_two_records_per_row`).  The paper's own claim
at `k = 2^31` is `121` bits -/
theorem trimmed_soundness_for_real_programs_at_two_pow_31 (R M Λ A p8Work n : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) (hn : n ≤ 3 * R) :
    goldilocksTrimmedFailureBound p8Work
        (ioFailureUnionBound 8 n n (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 121 :=
  lt_of_le_of_lt (trimmed_le_goldilocksFailureBoundK _ _ _ _)
    (soundness_at_two_pow_31 R M Λ A p8Work n hR hM hΛ hA hp8 hn)

/-- **119 bits at the deployable maximum `2^32` rows — at the *consumed* bound.**  The
`soundness_at_two_pow_32` instance, transferred by
`trimmed_le_goldilocksFailureBoundK`; the orbit ceiling `v₂(p³−1) = 32`
(`GoldilocksParameters.orbit_height_le`) is what makes `2^32` deployable rather than nominal. -/
theorem trimmed_soundness_for_real_programs_at_two_pow_32 (R M Λ A p8Work n : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) (hn : n ≤ 3 * R) :
    goldilocksTrimmedFailureBound p8Work
        (ioFailureUnionBound 8 n n (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 119 :=
  lt_of_le_of_lt (trimmed_le_goldilocksFailureBoundK _ _ _ _)
    (soundness_at_two_pow_32 R M Λ A p8Work n hR hM hΛ hA hp8 hn)

/-- **The `∀ ExactExecution` form, at the consumed bound.**  For any `ExactExecution` over
Goldilocks — both row counts derived from the orbit (`compRows_le_two_pow_32`,
`memRows_le_two_pow_32`), the record count derived from opcode arity (§1) — the consumed
trimmed bound at the execution's own derived request/response lists is below `2^-119`.
Nothing about `ioWork` is assumed -/
theorem trimmed_soundness_for_execution {cfg : ExactConfig Nock.Field.Fp Nock.Field.K}
    (exec : ExactExecution cfg) (Λ A p8Work : ℕ)
    (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant cfg.compRows cfg.memRows Λ A) :
    goldilocksTrimmedFailureBound p8Work
        (ioFailureUnionBound 8 exec.derivedRequestIO.length exec.derivedResponseIO.length
          (Fintype.card Nock.Field.K))
        cfg.compRows cfg.memRows
      < 1 / (2 : ℚ) ^ 119 :=
  lt_of_le_of_lt (trimmed_le_goldilocksFailureBoundK _ _ _ _)
    (soundness_for_execution exec Λ A p8Work hΛ hA hp8)

/-! ## 8.

**The collapse.**  `ioFailureUnionBound 8 (3N) M |𝕂| = |𝕂|·(7(3N+M)² + 2(3N+M))`, so the whole bound
is one fraction over `|𝕂|`, with numerator
`p8Work + (1 + 3N(3N−1)/2) + 7(3N+M)² + 2(3N+M)`.  At uniform size `S`, doubled to
clear the division: `2·numerator ≤ 367S² + 104S + 4`.  Hence
**`b = 184 − 2r`**: `122` at `2^31`, `120` at `2^32` — the quadratic α-summand still decides
the figure.  At the symmetric majorant `k₁ = k₂ = 3S` the numerator still gives `121`
(`hostile_soundness_symmetric_majorant_at_two_pow_31`).  The paper's own claim at
`k = 2^31` is `121`; the tree now proves one more. -/

/-- The total numerator of the consumed bound at the record majorants, over one `|𝕂|`. -/
def hostileTotalWork (p8Work N M : ℕ) : ℕ :=
  p8Work + OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
    (9 * ((3 * N + M) * (3 * N + M)) + 2 * (3 * N + M)) +
    (9 * ((M + M) * (M + M)) + 2 * (M + M)) +
    M +
    pricedWalkWork N M

/-- `ioFailureUnionBound 8 k₁ k₂ cardK = cardK · (7(k₁+k₂)² + 2(k₁+k₂))`. -/
theorem ioFailureUnionBound_eight' (k₁ k₂ cardK : ℕ) :
    ioFailureUnionBound 8 k₁ k₂ cardK = cardK * (7 * ((k₁ + k₂) * (k₁ + k₂)) + 2 * (k₁ + k₂)) := by
  simp only [ioFailureUnionBound, show (8 : ℕ) - 1 = 7 from rfl]
  ring

/-- Form R `m = 9`: `ioFailureUnionBound 9 k₁ k₂ cardK = cardK · (8(k₁+k₂)² + 2(k₁+k₂))`. -/
theorem ioFailureUnionBound_nine' (k₁ k₂ cardK : ℕ) :
    ioFailureUnionBound 9 k₁ k₂ cardK = cardK * (8 * ((k₁ + k₂) * (k₁ + k₂)) + 2 * (k₁ + k₂)) := by
  simp only [ioFailureUnionBound, show (9 : ℕ) - 1 = 8 from rfl]
  ring

theorem ioFailureUnionBound_ten' (k₁ k₂ cardK : ℕ) :
    ioFailureUnionBound 10 k₁ k₂ cardK = cardK * (9 * ((k₁ + k₂) * (k₁ + k₂)) + 2 * (k₁ + k₂)) := by
  simp only [ioFailureUnionBound, show (10 : ℕ) - 1 = 9 from rfl]
  ring

theorem hostileBound_at_majorants (p8Work N M : ℕ) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * N) M (Fintype.card Nock.Field.K)) N M
      = (hostileTotalWork p8Work N M : ℚ) / (cardKGold : ℚ) := by
  rw [goldilocksHostileFailureBound_eq, ioFailureUnionBound_ten',
    ioFailureUnionBound_ten' M M, card_K_gold]
  have hk : ((cardKGold : ℕ) : ℚ) ≠ 0 := by norm_num
  simp only [hostileTotalWork, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  ring

theorem hostileBound_lt_of_totalWork (p8Work N M b : ℕ)
    (h : hostileTotalWork p8Work N M * 2 ^ b < cardKGold) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * N) M (Fintype.card Nock.Field.K)) N M
      < 1 / (2 : ℚ) ^ b := by
  rw [hostileBound_at_majorants]
  rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
  have hq : ((hostileTotalWork p8Work N M * 2 ^ b : ℕ) : ℚ) < ((cardKGold : ℕ) : ℚ) := by
    exact_mod_cast h
  push_cast at hq ⊢
  linarith

theorem two_hostileTotalWork_le_of_size (S R M Λ A p8Work : ℕ)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ S)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) :
    2 * hostileTotalWork p8Work R M ≤ 447 * (S * S) + 152 * S + 288 := by
  have h1 : p8Majorant R M Λ A ≤ 39 * (S * S) + 39 * S + 1 :=
    p8Majorant_le_of_size S R M Λ A hR hM hΛ hA
  have h2 := OptimizedHostileTimestamps.two_mul_timestampCollisionBound_le (3 * R)
  have h3 : (3 * R + M) * (3 * R + M) ≤ (4 * S) * (4 * S) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 : (M + M) * (M + M) ≤ (2 * S) * (2 * S) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h5 : 3 * R * (3 * R) ≤ 3 * S * (3 * S) := Nat.mul_le_mul (by omega) (by omega)
  have hwr : ComputeWalkRootEvents.walkRootBound R ≤ S + 9 := by
    rw [ComputeWalkRootEvents.walkRootBound_eq]; omega
  have htc : WalkTilingEvents.computeTilingBound R ≤ 2 * S + 2 := by
    simp only [WalkTilingEvents.computeTilingBound]; omega
  have htm : WalkTilingEvents.memoryTilingBound M ≤ 2 * S + 1 := by
    simp only [WalkTilingEvents.memoryTilingBound]; omega
  have hγc : WalkPrefixGammaEvents.computePrefixGammaBound R ≤ 9 * S := by
    simp only [WalkPrefixGammaEvents.computePrefixGammaBound]; omega
  have hγm : WalkPrefixGammaEvents.memoryPrefixGammaBound M ≤ 5 * S := by
    simp only [WalkPrefixGammaEvents.memoryPrefixGammaBound]; omega
  have hpw : pricedWalkWork R M ≤
      (S + 9) + (2 * S + 2) + (2 * S + 1) + 9 * S + 5 * S + S + (4 * S + 130) := by
    simp only [pricedWalkWork, WalkPrefixGammaEvents.computePrefixGammaBound,
      WalkPrefixGammaEvents.memoryPrefixGammaBound,
      WalkForestPrefixAlphaEvents.memoryForestAlphaBound, pwAccountingWork']
    omega
  simp only [hostileTotalWork]
  have e1 : 2 * (p8Work +
      OptimizedHostileTimestamps.timestampCollisionBound (3 * R) +
      (9 * ((3 * R + M) * (3 * R + M)) + 2 * (3 * R + M)) +
      (9 * ((M + M) * (M + M)) + 2 * (M + M)) + M +
      pricedWalkWork R M)
      = 2 * p8Work +
        2 * OptimizedHostileTimestamps.timestampCollisionBound (3 * R) +
        18 * ((3 * R + M) * (3 * R + M)) + 4 * (3 * R + M) +
        18 * ((M + M) * (M + M)) + 4 * (M + M) + 2 * M +
        2 * pricedWalkWork R M := by ring
  rw [e1]
  have e2 : 447 * (S * S) + 152 * S + 288 =
      2 * (39 * (S * S) + 39 * S + 1) + (3 * S * (3 * S) + 2) +
        18 * ((4 * S) * (4 * S)) + 16 * S +
        18 * ((2 * S) * (2 * S)) + 8 * S + 2 * S +
        2 * (S + 9) + 2 * (2 * S + 2) + 2 * (2 * S + 1) +
        2 * (9 * S) + 2 * (5 * S) + 2 * S +
        2 * (4 * S + 130) := by ring
  rw [e2]
  omega

/-- **The arithmetic core.** -/
theorem hostileSizeWork_lt_cardK (r b : ℕ) (hr : 4 ≤ r) (hb : 2 * r + b = 184) :
    (447 * (2 ^ r * 2 ^ r) + 152 * 2 ^ r + 288) * 2 ^ b < 2 * cardKGold := by
  have h1 : (2 : ℕ) ^ r * 2 ^ r * 2 ^ b = 2 ^ 184 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have h2 : (2 : ℕ) ^ r * 2 ^ b ≤ 2 ^ 180 := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ^ b ≤ 2 ^ 176 := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc (447 * (2 ^ r * 2 ^ r) + 152 * 2 ^ r + 288) * 2 ^ b
      = 447 * (2 ^ r * 2 ^ r * 2 ^ b) + 152 * (2 ^ r * 2 ^ b) + 288 * 2 ^ b := by ring
    _ ≤ 447 * 2 ^ 184 + 152 * 2 ^ 180 + 288 * 2 ^ 176 := by
        rw [h1]
        exact Nat.add_le_add
          (Nat.add_le_add_left (Nat.mul_le_mul_left 152 h2) _)
          (Nat.mul_le_mul_left 288 h3)
    _ < 2 * cardKGold := by norm_num

/-- **And `184 − 2r` is the best this majorant gives**: `367 · 2^185 > 2·|K|`. -/
theorem hostileSizeWork_not_lt_cardK (r b : ℕ) (hb : 2 * r + b = 184) :
    ¬ ((447 * (2 ^ r * 2 ^ r) + 152 * 2 ^ r + 288) * 2 ^ (b + 1) < 2 * cardKGold) := by
  have h1 : (2 : ℕ) ^ r * 2 ^ r * 2 ^ (b + 1) = 2 ^ 185 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hA : 447 * (2 ^ r * 2 ^ r) ≤ 447 * (2 ^ r * 2 ^ r) + 152 * 2 ^ r + 288 := by omega
  have hstep : 447 * (2 ^ r * 2 ^ r) * 2 ^ (b + 1)
      ≤ (447 * (2 ^ r * 2 ^ r) + 152 * 2 ^ r + 288) * 2 ^ (b + 1) :=
    Nat.mul_le_mul_right _ hA
  have heq : 447 * (2 ^ r * 2 ^ r) * 2 ^ (b + 1) = 447 * 2 ^ 185 := by
    rw [mul_assoc, h1]
  rw [heq] at hstep
  have hcard : 2 * cardKGold ≤ 447 * 2 ^ 185 := by norm_num
  exact Nat.not_lt.mpr (le_trans hcard hstep)

/-- **The parametric theorem at the consumed stage-2B bound: `b = 184 − 2r`.** -/
theorem hostile_soundness_at_row_budget (r b R M Λ A p8Work : ℕ)
    (hr : 4 ≤ r) (hb : 2 * r + b = 184)
    (hR : R ≤ 2 ^ r) (hM : M ≤ 2 ^ r) (hΛ : Λ ≤ 2 ^ r) (hA : A ≤ 2 ^ r)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ b := by
  refine hostileBound_lt_of_totalWork _ _ _ _ ?_
  have h := two_hostileTotalWork_le_of_size (2 ^ r) R M Λ A p8Work hR hM hΛ hA hp8
  have h' := hostileSizeWork_lt_cardK r b hr hb
  have : 2 * (hostileTotalWork p8Work R M * 2 ^ b)
      ≤ (447 * (2 ^ r * 2 ^ r) + 152 * 2 ^ r + 288) * 2 ^ b := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ h
  omega

/-- **122 bits for real programs at `2^31` compute rows — at the consumed stage-2B bound.**
`R, M, Λ, A ≤ 2^31`, `p8Work` under the tree's own `p8Majorant`; the record counts are the
capstone's own majorants (`3R`, `M`), derived for every trace from the list definitions.  No
`ioWork` ceiling anywhere.

The consumed-bound figures are re-pointed to `workloadEv`: at chip width
(`formRN K ≤ 64`) `Batch1040.workloadEv_le_numeral` bounds `workloadEv P Λ` by the numeric slot,
and the doubled numerator `463S² + 412S + 30` gives **122 bits at `2^31`, 120 at `2^32`**
(`Batch1040.hostile_soundness_ev_at_two_pow_31` / `_32`); at the paper configuration 122, and 123
only under the `p8Work ≤ 2^60` ceiling (`Batch1040.ev_paper_122`, `ev_paper_not_123`,
`ev_ceiling_paper_123`).  The two theorems below remain true statements about the bound function at
any `p8Work` under `p8Majorant` -/
theorem hostile_soundness_for_real_programs_at_two_pow_31 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_at_row_budget 31 122 R M Λ A p8Work (by norm_num) (by norm_num) hR hM hΛ hA hp8

/-- **120 bits at the deployable maximum `2^32` rows — at the consumed stage-2B bound.** -/
theorem hostile_soundness_for_real_programs_at_two_pow_32 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 120 :=
  hostile_soundness_at_row_budget 32 120 R M Λ A p8Work (by norm_num) (by norm_num) hR hM hΛ hA hp8

/-! ### 8.1 The thirtieth move: the Form R λ-event summand (R3)

Since the thirtieth move the consumed bound prices the Form R λ-event through
`fixedFormRWorkload` **inside `workload`** (`p8Work`), at worst case `M·(3N + 130)`
(`Batch638.fixedFormRWorkload_le_64`), and `pricedWalkWork` no longer carries the slack
`pwAccountingWork' 64 N M = M + 3N + 130`.  So the hostile figures are re-proved with
`p8Work ≤ p8Majorant R M Λ A + M·(3R + 130)`: at uniform size `S`,
`2 · hostileTotalWork ≤ 453S² + 404S + 28` (was `407S² + 152S + 288` before the thirtieth), and
**`b = 184 − 2r` still holds: `122` at `2^31`, `120` at `2^32`**.  The paper-configuration `123`
(`GoldilocksParameters.hostile_soundness_at_paper_configuration`, `p8Work ≤ 2^60`) is untouched.

`IORLCCollisionEvent_card_le`'s factor is `m − 1 = 9`, so
`hostileTotalWork`'s two IO masses are `9·(3N+M)² + 2(3N+M)` and `9·(2M)² + 2(2M)`: the doubled
numerator is `453S² + 404S + 28` (the thirtieth's `413S² + 404S + 28` plus `2·((4S)² + (2S)²) =
40S²`; `Batch666.numerator_ten`), and `122` / `120` hold (`453·2^184 + 404·2^180 + 28·2^176 <
2|𝕂|`).

`workload` carries the request-indexed pair summand
`reqPairWorkload T Λ = M·(2(M ⊔ Λ) − 1) ≤ 2S²`, so `hp8` gains `+ M·(2(M ⊔ Λ) − 1)` and the doubled
numerator is `457S² + 404S + 28`; `122` / `120` still hold (`457·2^184 + 404·2^180 + 28·2^176 <
2|𝕂|`, `Batch747.joint_122` / `joint_120`).  The pre-thirtieth majorant above is likewise `447S² + 152S + 288`. -/

theorem two_hostileTotalWork_le_of_size_formR_prePair (S R M Λ A p8Work : ℕ)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ S)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    2 * hostileTotalWork p8Work R M ≤ 453 * (S * S) + 404 * S + 28 := by
  have h1 : p8Majorant R M Λ A ≤ 39 * (S * S) + 39 * S + 1 :=
    p8Majorant_le_of_size S R M Λ A hR hM hΛ hA
  have hfr : M * (3 * R + 130) ≤ 3 * (S * S) + 130 * S := by
    have : M * (3 * R + 130) ≤ S * (3 * S + 130) := Nat.mul_le_mul hM (by omega)
    nlinarith
  have h2 := OptimizedHostileTimestamps.two_mul_timestampCollisionBound_le (3 * R)
  have h3 : (3 * R + M) * (3 * R + M) ≤ (4 * S) * (4 * S) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 : (M + M) * (M + M) ≤ (2 * S) * (2 * S) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h5 : 3 * R * (3 * R) ≤ 3 * S * (3 * S) := Nat.mul_le_mul (by omega) (by omega)
  have hpw : pricedWalkWork R M ≤ (S + 9) + (2 * S + 2) + (2 * S + 1) + 9 * S + 5 * S + S := by
    simp only [pricedWalkWork, ComputeWalkRootEvents.walkRootBound_eq,
      WalkTilingEvents.computeTilingBound, WalkTilingEvents.memoryTilingBound,
      WalkPrefixGammaEvents.computePrefixGammaBound,
      WalkPrefixGammaEvents.memoryPrefixGammaBound,
      WalkForestPrefixAlphaEvents.memoryForestAlphaBound]
    omega
  simp only [hostileTotalWork]
  nlinarith

/-- **** `p8Work` now also carries the request-indexed pair
summand `M·(2(M ⊔ Λ) − 1) ≤ 2S²`, so the doubled numerator is `457S² + 404S + 28` (was `453`). -/
theorem two_hostileTotalWork_le_of_size_formR (S R M Λ A p8Work : ℕ)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ S)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130) + M * (2 * (M ⊔ Λ) - 1)) :
    2 * hostileTotalWork p8Work R M ≤ 457 * (S * S) + 404 * S + 28 := by
  have hp : M * (2 * (M ⊔ Λ) - 1) ≤ 2 * (S * S) := by
    have hmax : M ⊔ Λ ≤ S := max_le hM hΛ
    calc M * (2 * (M ⊔ Λ) - 1) ≤ S * (2 * S) := Nat.mul_le_mul hM (by omega)
      _ = 2 * (S * S) := by ring
  have hsplit : hostileTotalWork p8Work R M ≤
      hostileTotalWork (p8Work - M * (2 * (M ⊔ Λ) - 1)) R M + M * (2 * (M ⊔ Λ) - 1) := by
    simp only [hostileTotalWork]; omega
  have h := two_hostileTotalWork_le_of_size_formR_prePair S R M Λ A
    (p8Work - M * (2 * (M ⊔ Λ) - 1)) hR hM hΛ hA (by omega)
  omega

theorem hostileSizeWorkFormR_lt_cardK (r b : ℕ) (hr : 4 ≤ r) (hb : 2 * r + b = 184) :
    (457 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ b < 2 * cardKGold := by
  have h1 : (2 : ℕ) ^ r * 2 ^ r * 2 ^ b = 2 ^ 184 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have h2 : (2 : ℕ) ^ r * 2 ^ b ≤ 2 ^ 180 := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ^ b ≤ 2 ^ 176 := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc (457 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ b
      = 457 * (2 ^ r * 2 ^ r * 2 ^ b) + 404 * (2 ^ r * 2 ^ b) + 28 * 2 ^ b := by ring
    _ ≤ 457 * 2 ^ 184 + 404 * 2 ^ 180 + 28 * 2 ^ 176 := by
        rw [h1]
        exact Nat.add_le_add
          (Nat.add_le_add_left (Nat.mul_le_mul_left 404 h2) _)
          (Nat.mul_le_mul_left 28 h3)
    _ < 2 * cardKGold := by norm_num

/-- **The parametric theorem with the λ-event summand: `b = 184 − 2r`.** -/
theorem hostile_soundness_formR_at_row_budget (r b R M Λ A p8Work : ℕ)
    (hr : 4 ≤ r) (hb : 2 * r + b = 184)
    (hR : R ≤ 2 ^ r) (hM : M ≤ 2 ^ r) (hΛ : Λ ≤ 2 ^ r) (hA : A ≤ 2 ^ r)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130) + M * (2 * (M ⊔ Λ) - 1)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ b := by
  refine hostileBound_lt_of_totalWork _ _ _ _ ?_
  have h := two_hostileTotalWork_le_of_size_formR (2 ^ r) R M Λ A p8Work hR hM hΛ hA hp8
  have h' := hostileSizeWorkFormR_lt_cardK r b hr hb
  have : 2 * (hostileTotalWork p8Work R M * 2 ^ b)
      ≤ (457 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ b := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ h
  omega

/-- **R3: 122 bits at `2^31` rows with the λ-event summand at worst case.** -/
theorem hostile_soundness_formR_at_two_pow_31 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130) + M * (2 * (M ⊔ Λ) - 1)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_formR_at_row_budget 31 122 R M Λ A p8Work (by norm_num) (by norm_num)
    hR hM hΛ hA hp8

/-- **R3: 120 bits at `2^32` rows with the λ-event summand at worst case.** -/
theorem hostile_soundness_formR_at_two_pow_32 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130) + M * (2 * (M ⊔ Λ) - 1)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 120 :=
  hostile_soundness_formR_at_row_budget 32 120 R M Λ A p8Work (by norm_num) (by norm_num)
    hR hM hΛ hA hp8

/-- **And `184 − 2r` is the best this numerator gives** (`457 · 2^185 > 2·|K|`). -/
theorem hostileSizeWorkFormR_not_lt_cardK (r b : ℕ) (hb : 2 * r + b = 184) :
    ¬ ((457 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ (b + 1) < 2 * cardKGold) := by
  have h1 : (2 : ℕ) ^ r * 2 ^ r * 2 ^ (b + 1) = 2 ^ 185 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hA : 457 * (2 ^ r * 2 ^ r) ≤ 457 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28 := by omega
  have hstep : 457 * (2 ^ r * 2 ^ r) * 2 ^ (b + 1)
      ≤ (457 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ (b + 1) :=
    Nat.mul_le_mul_right _ hA
  have heq : 457 * (2 ^ r * 2 ^ r) * 2 ^ (b + 1) = 457 * 2 ^ 185 := by
    rw [mul_assoc, h1]
  rw [heq] at hstep
  have hcard : 2 * cardKGold ≤ 457 * 2 ^ 185 := by norm_num
  exact Nat.not_lt.mpr (le_trans hcard hstep)

/-- The pre-thirty-third tightness (`453`), kept for the receipts that cite it.  **And `184 − 2r` is the best this numerator gives** (`453 · 2^185 > 2·|K|`). -/
theorem hostileSizeWorkFormR_not_lt_cardK_prePair (r b : ℕ) (hb : 2 * r + b = 184) :
    ¬ ((453 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ (b + 1) < 2 * cardKGold) := by
  have h1 : (2 : ℕ) ^ r * 2 ^ r * 2 ^ (b + 1) = 2 ^ 185 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hA : 453 * (2 ^ r * 2 ^ r) ≤ 453 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28 := by omega
  have hstep : 453 * (2 ^ r * 2 ^ r) * 2 ^ (b + 1)
      ≤ (453 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ (b + 1) :=
    Nat.mul_le_mul_right _ hA
  have heq : 453 * (2 ^ r * 2 ^ r) * 2 ^ (b + 1) = 453 * 2 ^ 185 := by
    rw [mul_assoc, h1]
  rw [heq] at hstep
  have hcard : 2 * cardKGold ≤ 453 * 2 ^ 185 := by norm_num
  exact Nat.not_lt.mpr (le_trans hcard hstep)

/-- **The `∀ ExactConfig` form, at the consumed stage-2B bound.**  Both row counts come from the
orbit (`compRows_le_two_pow_32`, `memRows_le_two_pow_32`); the bound is trace-free, so no
execution is even named -/
theorem hostile_soundness_for_execution (cfg : ExactConfig Nock.Field.Fp Nock.Field.K)
    (Λ A p8Work : ℕ) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant cfg.compRows cfg.memRows Λ A) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * cfg.compRows) cfg.memRows (Fintype.card Nock.Field.K))
        cfg.compRows cfg.memRows
      < 1 / (2 : ℚ) ^ 120 :=
  hostile_soundness_for_real_programs_at_two_pow_32 cfg.compRows cfg.memRows Λ A p8Work
    (compRows_le_two_pow_32 cfg) (memRows_le_two_pow_32 cfg) hΛ hA hp8

/-- **Where the extra bit comes from.**  At the *symmetric* record majorant `k₁ = k₂ = 3R` that
§3–§6 used, the stage-2B bound at `2^31` rows still gives `121`, not `122`: the α-summand costs
nothing at the bit level, and the gain is entirely the response-count majorant `M`. -/
theorem hostile_soundness_symmetric_majorant_at_two_pow_31 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 8 (3 * R) (3 * R) (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 121 := by
  -- the symmetric numerator, over one `|𝕂|`
  set W : ℕ := p8Work +
    OptimizedHostileTimestamps.timestampCollisionBound (3 * R) +
    (28 * (3 * R) * (3 * R) + 4 * (3 * R)) +
    (36 * M * M + 4 * M) + M + pricedWalkWork R M with hW
  have hcollapse : goldilocksHostileFailureBound p8Work
      (ioFailureUnionBound 8 (3 * R) (3 * R) (Fintype.card Nock.Field.K)) R M
      = (W : ℚ) / (cardKGold : ℚ) := by
    rw [goldilocksHostileFailureBound_eq, ioFailureUnionBound_eight (3 * R),
      ioFailureUnionBound_ten M, card_K_gold]
    have hk : ((cardKGold : ℕ) : ℚ) ≠ 0 := by norm_num
    simp only [hW, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    ring
  -- `2W ≤ 647·S² + 118·S + 24` at uniform size `S` (old 591/102 plus 56S²+8S interWork
  -- plus `2S` from the all-row `|𝕂|·M` hit plus `6S + 20` from `2 · walkRootBound R`)
  have hgen : ∀ S : ℕ, R ≤ S → M ≤ S → Λ ≤ S → A ≤ S →
      2 * W ≤ 663 * (S * S) + 160 * S + 288 := by
    intro S hR hM hΛ hA
    have h1 : p8Majorant R M Λ A ≤ 39 * (S * S) + 39 * S + 1 :=
      p8Majorant_le_of_size S R M Λ A hR hM hΛ hA
    have h2 := OptimizedHostileTimestamps.two_mul_timestampCollisionBound_le (3 * R)
    have h3 : 3 * R * (3 * R) ≤ 3 * S * (3 * S) := Nat.mul_le_mul (by omega) (by omega)
    have h4 : M * M ≤ S * S := Nat.mul_le_mul hM hM
    have hwr : ComputeWalkRootEvents.walkRootBound R ≤ S + 9 := by
      rw [ComputeWalkRootEvents.walkRootBound_eq]; omega
    have htc : WalkTilingEvents.computeTilingBound R ≤ 2 * S + 2 := by
      simp only [WalkTilingEvents.computeTilingBound]; omega
    have htm : WalkTilingEvents.memoryTilingBound M ≤ 2 * S + 1 := by
      simp only [WalkTilingEvents.memoryTilingBound]; omega
    have hγc : WalkPrefixGammaEvents.computePrefixGammaBound R ≤ 9 * S := by
      simp only [WalkPrefixGammaEvents.computePrefixGammaBound]; omega
    have hγm : WalkPrefixGammaEvents.memoryPrefixGammaBound M ≤ 5 * S := by
      simp only [WalkPrefixGammaEvents.memoryPrefixGammaBound]; omega
    have hpw : pricedWalkWork R M ≤
        (S + 9) + (2 * S + 2) + (2 * S + 1) + 9 * S + 5 * S + S + (4 * S + 130) := by
      simp only [pricedWalkWork, WalkPrefixGammaEvents.computePrefixGammaBound,
        WalkPrefixGammaEvents.memoryPrefixGammaBound,
        WalkForestPrefixAlphaEvents.memoryForestAlphaBound, pwAccountingWork']
      omega
    have e1 : 2 * W = 2 * p8Work +
        2 * OptimizedHostileTimestamps.timestampCollisionBound (3 * R) +
        56 * (3 * R * (3 * R)) + 24 * R + 72 * (M * M) + 8 * M + 2 * M +
        2 * pricedWalkWork R M := by
      rw [hW]; ring
    have e2 : 663 * (S * S) + 160 * S + 288 =
        2 * (39 * (S * S) + 39 * S + 1) + (3 * S * (3 * S) + 2) +
          56 * (3 * S * (3 * S)) + 24 * S +
          72 * (S * S) + 8 * S + 2 * S +
          2 * (S + 9) + 2 * (2 * S + 2) + 2 * (2 * S + 1) +
          2 * (9 * S) + 2 * (5 * S) + 2 * S +
          2 * (4 * S + 130) := by ring
    rw [e1, e2]
    have hp8' : 2 * p8Work ≤ 2 * (39 * (S * S) + 39 * S + 1) :=
      Nat.mul_le_mul_left 2 (hp8.trans h1)
    have hts : 2 * OptimizedHostileTimestamps.timestampCollisionBound (3 * R)
        ≤ (3 * S) * (3 * S) + 2 :=
      le_trans h2 (Nat.add_le_add_right h3 2)
    omega
  have hbound : 2 * W ≤ 663 * (2 ^ 31 * 2 ^ 31) + 160 * 2 ^ 31 + 288 :=
    hgen (2 ^ 31) hR hM hΛ hA
  have hnum : W * 2 ^ 121 < cardKGold := by
    have h1 : (663 * (2 ^ 31 * 2 ^ 31) + 160 * 2 ^ 31 + 288) * 2 ^ 121 < 2 * cardKGold := by
      norm_num
    have h2 : 2 * (W * 2 ^ 121) ≤ (663 * (2 ^ 31 * 2 ^ 31) + 160 * 2 ^ 31 + 288) * 2 ^ 121 := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_right _ hbound
    exact Nat.lt_of_mul_lt_mul_left (h2.trans_lt h1)
  rw [hcollapse, div_lt_div_iff₀ (by norm_num) (by positivity)]
  have hq : ((W * 2 ^ 121 : ℕ) : ℚ) < ((cardKGold : ℕ) : ℚ) := by exact_mod_cast hnum
  push_cast at hq ⊢
  linarith

end

end RealProgramSoundness
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.derivedRequestIO_length_le
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.derivedResponseIO_length_le
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.reqRecs_length_le
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.respRecs_length_le
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.workload_le_p8Majorant
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.natDegree_countsP_le_maxExp
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.boundK_at_real_io
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.boundK_lt_of_totalWork
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.p8Majorant_le_io_term
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.not_ioWork_le_at_two_records_per_row
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.not_ioWork_le_at_ioNStar_succ
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.sizeWork_lt_cardK
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.sizeWork_not_lt_cardK
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.soundness_at_row_budget
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.soundness_at_two_pow_32
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.soundness_at_two_pow_31
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.soundness_for_execution
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.kMem_le_memRows
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.sizeWorkQuad_lt_cardK
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.sizeWorkQuad_not_lt_cardK
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.sizeWorkQuad_not_lt_cardK_at_512
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.trimmed_le_goldilocksFailureBoundK
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.trimmed_soundness_for_real_programs_at_two_pow_31
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.trimmed_soundness_for_real_programs_at_two_pow_32
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.trimmed_soundness_for_execution
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.soundness_at_row_budget_quadAxis
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.soundness_for_execution_quadAxis
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_31
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_32
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.hostile_soundness_for_execution
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.hostile_soundness_symmetric_majorant_at_two_pow_31
