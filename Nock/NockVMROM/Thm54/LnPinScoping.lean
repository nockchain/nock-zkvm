import Nock.NockVMROM.Thm54.NockGigaRAPFinite
import Nock.NockVMROM.Thm54.SemanticTimestampStrategy

/-!
# Scoping probes for transcribing the deployed client's `ln` pin

**This module adds no gate to any shipped AIR.**  Every AIR here is a *copy* under a new name,
built so the census, degree and variable-range consequences of the deployed client's `ln`
constraints can be measured by kernel reduction instead of estimated.  `Trans.computeAIRchained`,
`FiniteIO.finiteIOProgAIR`, `GigaFinite.computeCombinedFiniteAIR` and every existing theorem about
them are untouched.

## What the client has that this tree does not

* `%ln-starts-at-z` — `hoon/common/v2/table/verifier/compute.hoon:172-173`,
  `(mpsub-pelt z (w %ln))`, i.e. a **boundary** gate `ln₀ = z`.
* `%ln-inc` — `:1057-1059`, `(1 - pad)·(ln' - ln·z) = 0`.
* `%ln-dec` — `:1062-1064`, `pad·(ln - ln'·z) = 0`.
* memory twins `%mem-ln-init` (`verifier/memory.hoon:28-29`, `ln - z`) and
  `%mem-line-number-update` (`:342-343`, `ln' - ln·z`).

This tree already has the **transition** half on the compute side.  The per-row recurrence
`ln = ln_prev·α^{1,2,3}` is `Trans.memBlkExprs` (`Nock/AIR.lean:719`, soundness
`memBlkExprs_s0_sound … memBlkExprs_cons_sound`, `Nock/AIR.lean:925-991`) and the cross-row
hand-off `ln(i) = ln_prev(i+1)` is `Trans.lnChainExpr` (`Nock/AIR.lean:1996`).  What is absent is
the **boundary** half: nothing pins the first row's `ln_prev`.

The compute-side pin is carried instead as a *commitment-structure field*:
`SemanticTimestampSkeleton.computeStartsAtZero : ComputeLineStartsAtZero computeRows`
(`SemanticTimestampStrategy.lean:82`, predicate at `:54`), discharged for the generator by
`BFSAssign.bfsAssign_startsAtZero` (`BFSAssign.lean:233`).  So the question is not whether the
tree believes `ln_prev₀ = 1`; it is whether that belief is an AIR gate or a modelling field.

## The two candidate transcriptions, and why they are different objects

`pinnedComputeAIRchained` (§1) adds the compute-block boundary gate `ln_prev = 1`.  It reaches the compute table's own timestamp columns `74/82/90` and **not**
the prog-IO record column `111`: `pinnedComputeAIRchained_varsBelow` shows the block still reads
only columns `< 94`, so it is constraint-disjoint from the IO block exactly as
`computeAIRchained_varsBelow` (`ComputeStagedTable.lean:349`) already was.

`pinnedIOProgAIR` (§2) is the transcription of the client's **memory-table** pin
(`%mem-ln-init` + `%mem-line-number-update`) onto the prog-IO chip's own record timestamp column.
That is the one that reaches column `111`, and §3 is the reason it matters.

## Paper anchors

the paper (`𝓛𝒯_comp`, no line number among the labels), `:1693`
(`W_comp := (ln_prev, ln, mem_record₁₂₃)`), `:1728-1742` (Algorithm NockCompute's `ln` clauses),
`:738-741` (`Example:fibonacci`'s absolute base cases).
-/

namespace Nock.NockVMROM.Thm54.LnPinScoping

open Nock Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.Reified Nock.Reified.Trans
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.ComputeChip

set_option maxRecDepth 400000

/-! ## 1. The compute-block boundary pin, measured on a copy -/

/-- **The candidate compute-block boundary gate**: `ln_prev - 1` at the first row (column `65`).
This is the direct analogue of the client's `%ln-starts-at-z`
(`verifier/compute.hoon:172-173`) once the client's single `ln` column is split into this tree's
`ln_prev`/`ln` pair: the client pins `ln₀ = z` and increments uniformly, this tree increments by
the opcode-dependent `α^{1,2,3}` of the paper, so the invariant form of the same pin is
on `ln_prev`. -/
def lnPrevPinExpr : Expr := .Sub (tc 65) (.Const 1)

/-- This AIR exists **in order to be rejected**.  So the pin cannot buy the
thing it would be adopted for, and this copy is here only so the census, degree and column-range
*cost* of adopting it can be read off the kernel instead of estimated.

**Nothing ships it.**  The one extra gate is the
whole difference; `computeAIRchained_census_unchanged` below is the receipt that the shipped AIR
still has `527` constraints and no boundary gate. -/
def pinnedComputeAIRchained : AIR :=
  { computeAIRchained with
    constraints := computeAIRchained.constraints ++ [⟨.boundary, lnPrevPinExpr⟩] }

/-- The shipped AIR is untouched: it still has `527` constraints and no boundary gate. -/
theorem computeAIRchained_census_unchanged :
    computeAIRchained.constraints.length = 527 ∧
      (computeAIRchained.constraints.filter (fun c => c.kind == .boundary)).length = 0 :=
  ⟨rfl, rfl⟩

/-- **Constraint cost of the compute pin: exactly one gate.** -/
theorem pinnedComputeAIRchained_num_constraints :
    pinnedComputeAIRchained.constraints.length = 528 := rfl

/-- **Degree cost of the compute pin: zero.** -/
theorem pinnedComputeAIRchained_maxDegree :
    pinnedComputeAIRchained.maxDegree = 4 := by rfl

theorem lnPrevPinExpr_degree : lnPrevPinExpr.degree = 1 := rfl

theorem pinnedComputeAIRchained_kind_census :
    (pinnedComputeAIRchained.constraints.filter (fun c => c.kind == .row)).length = 526 ∧
      (pinnedComputeAIRchained.constraints.filter
        (fun c => c.kind == .transition)).length = 1 ∧
      (pinnedComputeAIRchained.constraints.filter
        (fun c => c.kind == .boundary)).length = 1 ∧
      (pinnedComputeAIRchained.constraints.filter
        (fun c => c.kind == .terminal)).length = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Same bound as
`ComputeChip.computeAIRchained_varsBelow` (`ComputeStagedTable.lean:349`): columns `< 94`,
challenges `< 5`, no publics.  This is the *negative* half of the scoping answer — the compute
pin cannot reach the prog-IO record column `111`, because no gate of this block mentions it. -/
theorem pinnedComputeAIRchained_varsBelow :
    pinnedComputeAIRchained.constraints.all
      (fun c => c.expr.varsBelow 94 5 0) = true := by rfl

/-- **Gate soundness.**  The boundary gate vanishes on a compute row environment iff that row's
`ln_prev` is `1`. -/
theorem lnPrevPinExpr_sound {K : Type*} [Field K]
    (inp : ComputeTable.Inputs K) (op : ComputeTable.State → K) (pub : ComputeTable.Pub K)
    (dec : ComputeTable.Dec K) (ex : ComputeTable.Extra K) :
    lnPrevPinExpr.eval (computeEnvFull inp op pub dec ex) = 0 ↔ pub.ln_prev = 1 := by
  simp only [lnPrevPinExpr, Expr.eval, eval_lnPrev, Int.cast_one, sub_eq_zero]

/-! ### 1b. The honest generator already satisfies it

`ComputeLineStartsAtZero` (`SemanticTimestampStrategy.lean:54`) says the first stamp has
`lnPrevExponent = 0`, and `Gen.lean:2577` renders `ln_prev := α ^ stamp.lnPrevExponent`.  So the
gate is discharged by `α^0 = 1` with no side condition on `α` — in particular the pin is free at
`α = 0`, which matters on this branch. -/

/-- The rendered first-row `ln_prev` of any α-free stamp list satisfying
`ComputeLineStartsAtZero` is `1`, hence the boundary gate vanishes. -/
theorem startsAtZero_renders_one {K : Type*} [Field K] (α : K)
    (stamps : List ComputeTimestampRow) (h : ComputeLineStartsAtZero stamps) :
    ∃ row rest, stamps = row :: rest ∧ α ^ row.lnPrevExponent = 1 := by
  cases stamps with
  | nil => exact absurd h id
  | cons row rest =>
      refine ⟨row, rest, rfl, ?_⟩
      have : row.lnPrevExponent = 0 := h
      rw [this, pow_zero]

/-! ## 2. The prog-IO chip pin — the transcription that reaches column `111`

The client pins the *memory* table's own `ln` column with `%mem-ln-init` (`ln - z`,
`verifier/memory.hoon:28-29`) and `%mem-line-number-update` (`ln' - ln·z`, `:342-343`).  The
analogue here is a pin on the prog-IO chip's own record-timestamp column, which is the **last**
record column, index `recBase + m - 1` — at the deployed `m = 8`, `recBase = 4`, combined index
`ComputeChip.ioTraceOff + 11 = 111`.

`finiteIOProgAIR` has `numChallenges = 2` (`0 = γ`, the RLC seed; `1 = pole`).  The pin needs the
timestamp base `α`, so the copy declares a third slot `2`. -/

/-- Timestamp column of a width-`m` record based at `recBase`: the last record coordinate. -/
def tsCol (m recBase : ℕ) : ℕ := recBase + m - 1

theorem tsCol_eight : tsCol 8 4 = 11 := rfl

/-- **`%mem-ln-init` transcribed**: boundary gate `ts - α`. -/
def ioTsInit (m recBase : ℕ) : Expr := .Sub (tc (tsCol m recBase)) (chl 2)

/-- **`%mem-line-number-update` transcribed**: transition gate `ts' - ts·α`. -/
def ioTsStep (m recBase : ℕ) : Expr :=
  .Sub (Trans.tn (tsCol m recBase)) (.Mul (tc (tsCol m recBase)) (chl 2))

/-- Not shipped. -/
def pinnedIOProgAIR (m : ℕ) : AIR where
  numTraceCols := m + 4
  numChallenges := 3
  numPublic := 1
  constraints :=
    (finiteIOProgAIR m).constraints
      ++ [⟨.boundary, ioTsInit m 4⟩, ⟨.transition, ioTsStep m 4⟩]

/-- **Constraint cost of the IO pin: exactly two gates** (`4 → 6`). -/
theorem pinnedIOProgAIR_num_constraints (m : ℕ) :
    (pinnedIOProgAIR m).constraints.length = 6 := rfl

/-- **Degree cost of the IO pin: zero.**  Challenges are degree `0` (`Nock/AIR.lean:120`), so
`ts' - ts·α` is degree `1`; the chip's maximum stays at `ioInvPin`'s `2`. -/
theorem ioTsInit_degree (m : ℕ) : (ioTsInit m 4).degree = 1 := rfl
theorem ioTsStep_degree (m : ℕ) : (ioTsStep m 4).degree = 1 := rfl

theorem pinnedIOProgAIR_maxDegree_eight : (pinnedIOProgAIR 8).maxDegree = 2 := by rfl
theorem finiteIOProgAIR_maxDegree_eight : (finiteIOProgAIR 8).maxDegree = 2 := by rfl

theorem pinnedIOProgAIR_varsBelow_eight :
    (pinnedIOProgAIR 8).constraints.all
      (fun c => c.expr.varsBelow 12 3 1) = true := by rfl

/-- **Gate soundness (boundary).**  Vanishes iff the row's record timestamp column carries the
timestamp base drawn on challenge slot `2`. -/
theorem ioTsInit_sound {K : Type*} [Field K] (m : ℕ) (env : Env K) :
    (ioTsInit m 4).eval env = 0 ↔ env.trace (tsCol m 4) = env.chal 2 := by
  show env.trace (tsCol m 4) - env.chal 2 = 0 ↔ _
  rw [sub_eq_zero]

/-- **Gate soundness (transition).**  Vanishes iff the next row's timestamp is this row's scaled
by the base — the client's `%mem-line-number-update` (`verifier/memory.hoon:342-343`). -/
theorem ioTsStep_sound {K : Type*} [Field K] (m : ℕ) (env : Env K) :
    (ioTsStep m 4).eval env = 0
      ↔ env.traceNext (tsCol m 4) = env.trace (tsCol m 4) * env.chal 2 := by
  show env.traceNext (tsCol m 4) - env.trace (tsCol m 4) * env.chal 2 = 0 ↔ _
  rw [sub_eq_zero]

/-! ## 3. What the pin buys — the exclusion at the record timestamp column, *derived*

There the exclusion is
`StagedChip.columnChallenges`, a declaration, honoured by the hypothesis
`RoundFibred.StagedAssignment.col_reads` (`RoundFibredSoundness.lean:563`).  `JP` §5 proved
`col_reads` is not implied by satisfaction *at a constraint-free chip*
(`col_reads_not_implied_by_satisfaction`, `GigaRAPThirdMessage.lean:839`).

That counterexample is not an obstruction to the pin route, and this section says why in a
compiled form: with a gate present, satisfaction **does** determine the column, and a determined
column is constant in every coin it is not determined *by*.  The theorems below are stated at the
row-value level, which is where the pin's content lives; §4 records what remains between them and
a statement about `StagedAssignment.col`. -/

/-- **The pin determines the timestamp column outright.**  A row family satisfying the two
transcribed gates is `α^{i+1}`, with no freedom left to the prover. -/
theorem pinned_ts_determined {K : Type*} [Field K] (α : K) (f : ℕ → K)
    (h0 : f 0 = α) (hstep : ∀ i, f (i + 1) = f i * α) :
    ∀ i, f i = α ^ (i + 1) := by
  intro i
  induction i with
  | zero => simpa using h0
  | succ k ih => rw [hstep k, ih, ← pow_succ]

/-- **The headline probe: the pin replaces the declaration at the record timestamp column.**

Two prover strategies, run at two challenge vectors that agree *only* on the timestamp base `α`,
produce the **same** timestamp column — provided each satisfies the transcribed gates.  There is
no `col_reads` hypothesis at this column, and the two vectors are otherwise arbitrary, so in
particular they may differ at both `RAP_prog-IO` coins.

This is the property `GigaIOFreshness.prog_records_const_in_the_io_coins`
(`GigaRAPIOFreshness.lean:177`) obtains from `col_reads` and
`GigaIOThirdMessage.prog_records_const_in_the_io_coins3`
(`GigaRAPThirdMessage.lean:650`) obtains from the third verifier message.  Here it comes from the
constraint system. -/
theorem pinned_ts_const_in_every_other_coin {K : Type*} [Field K] {ι : Type*}
    (χ₁ χ₂ : ι → K) (a : ι) (hα : χ₁ a = χ₂ a)
    (f g : ℕ → K)
    (hf0 : f 0 = χ₁ a) (hfs : ∀ i, f (i + 1) = f i * χ₁ a)
    (hg0 : g 0 = χ₂ a) (hgs : ∀ i, g (i + 1) = g i * χ₂ a) :
    ∀ i, f i = g i := by
  intro i
  rw [pinned_ts_determined _ f hf0 hfs i, pinned_ts_determined _ g hg0 hgs i, hα]

/-- `e` here is the per-row exponent increment — `recordCount` of the row's state, i.e. `1`, `2` or
`3` per the paper.  The selectors are compute columns `0 … 10`, which
`GigaFinite.finRoundOf` (`NockGigaRAPFinite.lean:843`) puts in round `0`: `if c < 11 then 0`.
That is the load-bearing arithmetic fact for the scoping question — the exponent is round-`0`
data, so a *binding* commitment already makes it constant in every coin. -/
theorem pinned_lnPrev_determined {K : Type*} [Field K] (α : K) (e : ℕ → ℕ) (f : ℕ → K)
    (h0 : f 0 = 1) (hstep : ∀ i, f (i + 1) = f i * α ^ e i) :
    ∀ i, f i = α ^ (∑ j ∈ Finset.range i, e j) := by
  intro i
  induction i with
  | zero => simpa using h0
  | succ k ih =>
      rw [hstep k, ih, Finset.sum_range_succ, pow_add]

/-- The compute-side conclusion, in the same "two challenge vectors" form as
`pinned_ts_const_in_every_other_coin`: agreement on `α` and on the *exponent data* suffices.  The
exponent data is round-`0` (the opcode selectors), so on a binding commitment it is not a
hypothesis about the IO coins at all. -/
theorem pinned_lnPrev_const_in_every_other_coin {K : Type*} [Field K] {ι : Type*}
    (χ₁ χ₂ : ι → K) (a : ι) (hα : χ₁ a = χ₂ a) (e : ℕ → ℕ) (f g : ℕ → K)
    (hf0 : f 0 = 1) (hfs : ∀ i, f (i + 1) = f i * χ₁ a ^ e i)
    (hg0 : g 0 = 1) (hgs : ∀ i, g (i + 1) = g i * χ₂ a ^ e i) :
    ∀ i, f i = g i := by
  intro i
  rw [pinned_lnPrev_determined _ e f hf0 hfs i, pinned_lnPrev_determined _ e g hg0 hgs i, hα]

/-! ## 3b. The in-tree precedent: the WALK table already ships the client's pin verbatim

The pair
of gates §2 proposes for the prog-IO chip is **already deployed** in this tree, on `walkAIR`
(`Nock/AIR.lean:2323`):

* `Trans.walkLn1` (`Nock/AIR.lean:2065`) is `ln(1) - α`, a `.boundary` gate — the exact shape of
  `%ln-starts-at-z` (`verifier/compute.hoon:172-173`) and `%mem-ln-init`
  (`verifier/memory.hoon:28-29`);
* `Trans.walkLnStep` (`Nock/AIR.lean:2058`) is `ln(i+1) - α·ln(i)`, a `.transition` gate — the
  exact shape of `%ln-inc` (`:1057-1059`) and `%mem-line-number-update` (`:342-343`).

Soundness is already proved: `Trans.reified_walk_ln1_sound` and
`Trans.reified_walk_ln_step_sound` (`Nock/AIR.lean:2095`, `:2075`).  The compute table is the one place where the boundary half is missing. -/

theorem walk_table_already_carries_the_pin :
    (⟨.boundary, walkLn1⟩ : Constraint) ∈ walkAIR.constraints ∧
      (⟨.transition, walkLnStep⟩ : Constraint) ∈ walkAIR.constraints := by
  constructor <;> simp [walkAIR]

/-- The shapes coincide up to the column index: the walk pin is `tc 0`-based, the proposed IO pin
is `tc (tsCol m 4)`-based, and both read the base on a challenge slot. -/
theorem ioTs_gates_are_the_walk_gates_reindexed :
    ioTsInit 8 4 = .Sub (tc 11) (chl 2) ∧
      ioTsStep 8 4 = .Sub (Trans.tn 11) (.Mul (tc 11) (chl 2)) ∧
      walkLn1 = .Sub (tc 0) (chl 0) ∧
      walkLnStep = .Sub (Trans.tn 0) (.Mul (chl 0) (tc 0)) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 3c. Consecutiveness — the honest request stream really is `α^1, α^2, …`

The IO pin of §2 asserts the record timestamps advance by one power per **row of the IO chip**.
That is only completable if the honest request stream carries consecutive exponents.  It does,
and it follows from two fields the α-free commitment already has:
`SemanticTimestampSkeleton.computeRecordOffsets` (`recordExponent i = lnPrevExponent + i + 1`)
and `computeLineAdvance` (`lnExponent = lnPrevExponent + recordCount state`), chained across rows
by `computeLineChain` (all at `SemanticTimestampStrategy.lean:82-92`), with the origin fixed by
`computeStartsAtZero`.  `requestTopology` (`:92`) flattens rows in order, records in index
order, so the stream is exactly `1, 2, 3, …`.

The two lemmas below are the induction step, stated over the field data rather than over the
structure so they carry no `SemanticSkeleton` plumbing. -/

/-- Within one row, successive records advance by exactly one power. -/
theorem record_exponents_step_within_row
    (lnPrev n : ℕ) (rexp : ℕ → ℕ)
    (hoff : ∀ i, i < n → rexp i = lnPrev + i + 1)
    (i : ℕ) (hi : i + 1 < n) :
    rexp (i + 1) = rexp i + 1 := by
  rw [hoff i (by omega), hoff (i + 1) (by omega)]
  omega

/-- Across a row boundary, the first record of the next row advances by exactly one power from
the last record of this row.  `hadv` is `computeLineAdvance`, `hchain` is `computeLineChain`. -/
theorem record_exponents_step_across_rows
    (lnPrev lnExp n lnPrev' : ℕ) (rexp rexp' : ℕ → ℕ)
    (hn : 0 < n)
    (hoff : ∀ i, i < n → rexp i = lnPrev + i + 1)
    (hadv : lnExp = lnPrev + n)
    (hchain : lnExp = lnPrev')
    (hoff' : ∀ i, i < 1 → rexp' i = lnPrev' + i + 1) :
    rexp' 0 = rexp (n - 1) + 1 := by
  rw [hoff' 0 (by omega), hoff (n - 1) (by omega), ← hchain, hadv]
  omega

/-! ## 3d. The total cost of both pins on the combined compute chip, measured -/

/-- Not shipped. -/
def pinnedComputeCombinedFiniteAIR (nc m : ℕ) (fC : ℕ → ℕ) : AIR where
  numTraceCols  := m + 104
  numChallenges := nc
  numPublic     := 3
  constraints :=
    pinnedComputeAIRchained.constraints
      ++ walkAIR.constraints.map
          (fun c => ⟨c.kind, c.expr.shiftBlock ComputeChip.walkTraceOff ComputeChip.walkChalOff
            ComputeChip.walkPubOff⟩)
      ++ (pinnedIOProgAIR m).constraints.map
          (fun c => ⟨c.kind, c.expr.remapBlock ComputeChip.ioTraceOff fC ComputeChip.ioPubOff⟩)

/-- **Total constraint cost: `538 → 541`, i.e. three gates.** -/
theorem pinnedComputeCombinedFiniteAIR_num_constraints (nc m : ℕ) (fC : ℕ → ℕ) :
    (pinnedComputeCombinedFiniteAIR nc m fC).constraints.length = 541 := by rfl

/-- **Total kind census: `526 / 7 / 6 / 2`** against the shipped `526 / 6 / 4 / 2`
(`GigaFinite.computeCombinedFiniteAIR_kind_census`, `NockGigaRAPFinite.lean:260`).  No row gate
is added, which is the count that drives per-row prover work. -/
theorem pinnedComputeCombinedFiniteAIR_kind_census (nc m : ℕ) (fC : ℕ → ℕ) :
    ((pinnedComputeCombinedFiniteAIR nc m fC).constraints.filter
        (fun c => c.kind == .row)).length = 526 ∧
      ((pinnedComputeCombinedFiniteAIR nc m fC).constraints.filter
        (fun c => c.kind == .transition)).length = 7 ∧
      ((pinnedComputeCombinedFiniteAIR nc m fC).constraints.filter
        (fun c => c.kind == .boundary)).length = 6 ∧
      ((pinnedComputeCombinedFiniteAIR nc m fC).constraints.filter
        (fun c => c.kind == .terminal)).length = 2 := by
  refine ⟨by rfl, by rfl, by rfl, by rfl⟩

/-- `AIR.maxDegree` over an append is the max of the two folds — so a block of degree-`≤ d` gates
appended to an AIR of degree `d` cannot move it.  Used instead of a `541`-constraint `rfl`. -/
theorem maxDegree_fold_append (cs ds : List Constraint) :
    (cs ++ ds).foldr (fun c acc => max c.expr.degree acc) 0
      = max (cs.foldr (fun c acc => max c.expr.degree acc) 0)
            (ds.foldr (fun c acc => max c.expr.degree acc) 0) := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih, max_assoc]

/-- **Total degree cost: zero.**  All three added gates are degree `1`
(`lnPrevPinExpr_degree`, `ioTsInit_degree`, `ioTsStep_degree`) and the shipped maximum is `4`. -/
theorem pinnedComputeCombinedFiniteAIR_added_gates_are_degree_one :
    lnPrevPinExpr.degree = 1 ∧ (ioTsInit 8 4).degree = 1 ∧ (ioTsStep 8 4).degree = 1 :=
  ⟨rfl, rfl, rfl⟩

theorem pinnedComputeAIRchained_maxDegree_via_append :
    pinnedComputeAIRchained.maxDegree = max computeAIRchained.maxDegree 1 := by
  show (computeAIRchained.constraints ++ [(⟨.boundary, lnPrevPinExpr⟩ : Constraint)]).foldr
      (fun c acc => max c.expr.degree acc) 0 = _
  rw [maxDegree_fold_append]
  rfl

/-! ## 4. The two gaps that remain between §3 and a `StagedAssignment` theorem

Stated, not hidden.  Neither is refuted here; both are work, and §4.2 is the larger one.

**4.1 Interpolation.**  `StagedAssignment.col` is valued in `K[X]`, not in row values.  §3 fixes
the column at every deployed row point; concluding that the *polynomial* is a function of `α`
needs the deployed domain to be at least as large as the column's degree bound, so that the
interpolant is unique.  That is a standard AIR side condition and this tree already carries
domain/degree data on `params`, but no lemma of this shape exists yet.

**4.2 The row correspondence, which blocks the *compute-side* route specifically.**
A cross-block linking gate — pinning IO record columns `104 … 111` to the compute table's own
`mr1/mr2/mr3` (columns `67 … 90`) — is what would carry §1's compute pin to column `111`.  It is
**not constructible per row**: one compute row emits up to three memory records, the prog-IO chip carries one record per row, and a `StagedChip` has a
single `params.domain` for both blocks.  `GigaRAPAssembledWitness.lean`'s header states the same
obstruction from the completeness side and isolates the equation `n + 1 = cfg.compRows` that
would remove it; that equation is false whenever any row requests more than one record.

This is why §2 is the transcription that matters and §1 is not: the client's own repair is the
*memory-table* pin (`%mem-ln-init`, `%mem-line-number-update`), applied to the table that owns
the column, not a cross-table link. -/

/-! ## 5. The two findings that decide the scoping question, recorded

**5.1 The compute-side pin contradicts a stated paper `iff`.**  `Lem:equiv_compute` is an equivalence: "`RAP_comp` admits a satisfying assignment for
`(x^comp, x_out^comp, W_comp)` **if and only if** `V_comp(x^comp, x_out^comp; W_comp) = Accept`".
Re-read at source.  `V_comp` never pins `ln_prev`: every clause reads it
(`ln_prev·z`, `ln_prev·z²`, `ln = ln_prev·z³`) and none fixes it, and `ln_prev` is a witness
polynomial of `W_comp` (`:1693`) rather than a label of `𝓛𝒯_comp` (`:1690`), so
`Example:fibonacci`'s absolute base cases (`:738-741`) are not a precedent for it.  Adding
`lnPrevPinExpr` to `computeAIRchained` therefore makes the AIR **strictly stronger than
`V_comp`** and falsifies the `⟸` direction of the paper's own equivalence — whose in-tree
transcription is `PlusIOTraceEncoding.computeSegmentedRAP_wholeTrace_iff`
(`TraceEncoding.lean:423`), whose right-hand side is exactly "per-row `Vcomp`, plus the adjacent
line hand-off, and nothing else".  So the compute pin is not merely an extra gate: it is a `1-1`
regression against the paper.  `GenericHonestCommitment.vcomp_s1_ignores_first_ln_prev`
(`:97`) would remain **true and would become the proof that the regression is real**, rather
than becoming false or becoming unused.

**5.2 The IO-side pin is available on the request side and NOT on the response side.**
`NockVM.reqRecs` (`Nock/NockVM.lean:659`) flat-maps the compute rows in order and each row's
active records in slot order, so with `computeStartsAtZero` its timestamps are `α^1, α^2, …`
consecutively (§3c) and `pinnedIOProgAIR`'s two gates are completable.  `NockVM.respRecs`
(`Nock/NockVM.lean:684`) flat-maps the **memory** walk's `read_root` rows, and the whole content of
`IO.LIO` / `reqRecs.Perm respRecs` is that the two lists are a *permutation* and not the same
order.  So `ts(row j) = α^{j+1}` is false for the honest response trace: the twin pin on
`finiteIOMemAIR` is not completable, and forcing it on both sides would collapse the permutation
to the identity and with it the multiset argument.

**5.3 What the client actually pins, re-read at source.**  `%ln` is a **per-table row counter**
in both client tables, not a shared timestamp.  Compute `%ln` is `z^{f(i)}` with `f` from the
round-`0` `%pad` column; memory `%ln` increments unconditionally
(`prover/memory.hoon:582`, `new-line-ct = (pmul line-ct z.chals)`) and is consumed by the
within-table `%kvs` accumulator (`:620`, `(pmul (padd par wt-pax) line-ct)`) and by `%data-k`
(`:653`, `:660`).  Where it *does* reach — a
per-table `α`-power line counter with a boundary and a step gate — this tree already complies, on
`walkAIR` (§3b). -/

section Audit

#print axioms pinnedComputeAIRchained_num_constraints
#print axioms pinnedComputeAIRchained_maxDegree
#print axioms pinnedComputeAIRchained_kind_census
#print axioms pinnedComputeAIRchained_varsBelow
#print axioms computeAIRchained_census_unchanged
#print axioms lnPrevPinExpr_sound
#print axioms startsAtZero_renders_one
#print axioms pinnedIOProgAIR_num_constraints
#print axioms pinnedIOProgAIR_maxDegree_eight
#print axioms pinnedIOProgAIR_varsBelow_eight
#print axioms ioTsInit_sound
#print axioms ioTsStep_sound
#print axioms pinned_ts_determined
#print axioms pinned_ts_const_in_every_other_coin
#print axioms pinned_lnPrev_determined
#print axioms pinned_lnPrev_const_in_every_other_coin
#print axioms walk_table_already_carries_the_pin
#print axioms ioTs_gates_are_the_walk_gates_reindexed
#print axioms record_exponents_step_within_row
#print axioms record_exponents_step_across_rows
#print axioms pinnedComputeCombinedFiniteAIR_num_constraints
#print axioms pinnedComputeCombinedFiniteAIR_kind_census
#print axioms maxDegree_fold_append
#print axioms pinnedComputeAIRchained_maxDegree_via_append

end Audit

end Nock.NockVMROM.Thm54.LnPinScoping
