import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.GigaRAPIOSlots
import Nock.NockVMROM.Thm54.IOChipCompleteness
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# A satisfying trace for the *assembled* giga-RAP chips, and non-vacuity of the composition

`GigaRAPIOSlots.io_lio_of_giga_satisfies_at_production_coins` (`GigaRAPIOSlots.lean:963`) is an
implication whose main hypothesis is `(finiteComputeChip canonicalIOSlots qC).Satisfies PC` — a
112-column trace satisfying 538 constraints — together with its 53-column / 93-constraint memory
twin.

This module closes it.  It supplies

* the **converse of the fold** — `finiteComputeChip_satisfies_of_gates` /
  `finiteMemoryChip_satisfies_of_gates`, which build assembled-chip satisfaction out of per-block
  gate vanishing (the missing direction of `finiteComputeChip_fold_loses_nothing`);
* an explicit **satisfying 112-column trace and 53-column trace** at an explicit deployment;
* the whole hypothesis bundle of `io_lio_of_giga_satisfies` and of
  `io_lio_of_giga_satisfies_at_production_coins`, so neither is vacuous.

## What the witness is, and exactly how degenerate it is

**Read this before quoting anything below.**

* The `100` compute-side columns `0 … 99` and the `41` memory-side columns `0 … 40` are
  **constant** polynomials.  The compute-table block holds the constant row
  `col 0 = 1, col 14 = col 15 = col 47 = col 50 = col 67 = col 68 = col 70 = 1, col 73 = 3,
  col 93 = 1`, all other columns `0`; the memory-table block holds `col 0 = col 34 = 1`, all
  others `0`; both walk blocks are identically `0`.  So the trace **encodes no Nock execution**:
  it is a fixed point of the row gates, not a computation.  Nothing here claims otherwise.
* The **IO block is real**: columns `100 … 111` (resp. `41 … 52`) are `IOChipCompleteness`'s
  interpolated `chipTrace`, carrying genuine records, reciprocals, multiplicities and a genuine
  accumulator, at the real record length.
* **No constraint is deployed on the empty set.**  This is the one place where this witness is
  strictly better than the obvious cheat.  `IOChipCompleteness.chipParams`
  (`IOChipCompleteness.lean:161`) sets `domain.row := ∅`, which is harmless there because the IO
  chip has no row gates; carrying that choice over to the assembled chip would erase `526` of the
  `538` compute constraints and `75` of the `93` memory constraints, and the resulting "witness"
  would say almost nothing.  `gigaParams` instead deploys `.row` on the full `n + 1`-row prefix
  `D.rowDomain (n + 1)`, which is non-empty, and the constant columns above are chosen so that
  **every** gate of `computeAIRchained` (`527`), of `walkAIR` (`7`) and of `memoryAIRchained`
  (`80`) vanishes identically there — verified by kernel reduction over `ℤ`
  (`computeAIRchained_vanishes`, `walkAIR_vanishes`, `memoryAIRchained_vanishes`) and transported
  to an arbitrary field by `eval_castEnv`.
* So what the headline non-vacuity theorems buy is: **the 538-constraint conjunction is
  consistent, and consistent jointly with a non-degenerate IO block at real records.**
* What it does **not** buy: it is not a completeness theorem for the compute table.  A
  non-degenerate witness — one whose columns are the trace of an actual execution — would need
  the compute block to be `PlusIOSegmentedRAP.computeTableRAP`'s own satisfying trace
  (`SampledIOSameExecution.lean:103`, `ComputeSampledObligations`) and the walk block to be
  `PlusIOTraceEncoding.lean:1349`'s walk certificate, glued on **one** shared per-kind evaluation
  domain.  That gluing is exactly what fails today: the compute table is deployed on
  `cfg.compRows` rows and the prog-IO chip on `|requests| + 1` rows, and a `StagedChip` has one
  `params.domain` for both.  §11 states that obstruction, and isolates the single equation
  (`n + 1 = cfg.compRows`) that would remove it.

## Paper anchors

The two coins the IO block reads are the paper ("Verifier responds with random elements
`α, β ∈ 𝕂`"), consumed by `RLC^α(IO_prog(i,k,·)) - β` at the paper; the commitment that
precedes them is the paper, and the round is priced at the paper.  The multiplicity
column the response chip pins is the paper.
-/

namespace Nock.NockVMROM.Thm54.GigaWitness

open Nock Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.Reified Nock.Reified.Trans
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.Staged
open Nock.NockVMROM.Thm54.GigaChips
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.GigaFinite
open Nock.NockVMROM.Thm54.GigaIOSlots
open Nock.NockVMROM.Thm54.IOCoinReconciliation
open scoped Polynomial

/-! ## 1. Integer evaluation, and its transport to an arbitrary field

The constant row values below are integers (`0`, `1`, `3`).  Checking `538` gate evaluations by
`decide` is only possible over a type with decidable equality and computable arithmetic, and the
statement has to hold over an *arbitrary* field `K`.  `evalZ` evaluates a reified expression in
`ℤ`; `eval_castEnv` says the field evaluation of the cast environment is the cast of the integer
evaluation, so an integer `0` is a `K`-valued `0` in every characteristic. -/

/-- Integer evaluation of a reified constraint expression. -/
def evalZ : Reified.Expr → Reified.Env ℤ → ℤ
  | .Var .traceCur i,  env => env.trace i
  | .Var .traceNext i, env => env.traceNext i
  | .Var .challenge i, env => env.chal i
  | .Var .publicVal i, env => env.pub i
  | .Const c,          _   => c
  | .Add a b,          env => evalZ a env + evalZ b env
  | .Sub a b,          env => evalZ a env - evalZ b env
  | .Mul a b,          env => evalZ a env * evalZ b env
  | .Neg a,            env => - evalZ a env
  | .Pow e n,          env => (evalZ e env) ^ n

/-- The `K`-valued environment induced by an integer environment. -/
def castEnv (K : Type*) [Field K] (e : Reified.Env ℤ) : Reified.Env K where
  trace := fun i => ((e.trace i : ℤ) : K)
  traceNext := fun i => ((e.traceNext i : ℤ) : K)
  chal := fun i => ((e.chal i : ℤ) : K)
  pub := fun i => ((e.pub i : ℤ) : K)

/-- **Integer evaluation transports to every field.**  `Int.cast` is a ring hom and `Expr.eval`
is built only from the ring operations, so the two evaluations agree under the cast. -/
theorem eval_castEnv {K : Type*} [Field K] (envZ : Reified.Env ℤ) (e : Reified.Expr) :
    e.eval (castEnv K envZ) = ((evalZ e envZ : ℤ) : K) := by
  induction e with
  | Var kind i => cases kind <;> rfl
  | Const c => rfl
  | Add a b ha hb => simp only [Reified.Expr.eval, evalZ, ha, hb, Int.cast_add]
  | Sub a b ha hb => simp only [Reified.Expr.eval, evalZ, ha, hb, Int.cast_sub]
  | Mul a b ha hb => simp only [Reified.Expr.eval, evalZ, ha, hb, Int.cast_mul]
  | Neg a ha => simp only [Reified.Expr.eval, evalZ, ha, Int.cast_neg]
  | Pow a n ha => simp only [Reified.Expr.eval, evalZ, ha, Int.cast_pow]

/-! ## 2. The constant row values, and the three vanishing certificates -/

/-- The compute-table block's constant row.  Found by solving the three gates that the all-zero
row fails (the opcode one-hot sum, `col 73 = 3`, and the `chl 1 · col 93 = 1` inverse pin) and
closing under the gates those activate. -/
def compValZ : ℕ → ℤ := fun j =>
  if j = 0 then 1 else if j = 14 then 1 else if j = 15 then 1
  else if j = 47 then 1 else if j = 50 then 1 else if j = 67 then 1
  else if j = 68 then 1 else if j = 70 then 1 else if j = 73 then 3
  else if j = 93 then 1 else 0

/-- The memory-table block's constant row. -/
def memValZ : ℕ → ℤ := fun j => if j = 0 then 1 else if j = 34 then 1 else 0

/-- `compValZ` is supported on the compute-table block. -/
theorem compValZ_high (j : ℕ) (hj : 94 ≤ j) : compValZ j = 0 := by
  unfold compValZ; split_ifs <;> omega

/-- `memValZ` is supported on the memory-table block. -/
theorem memValZ_high (j : ℕ) (hj : 35 ≤ j) : memValZ j = 0 := by
  unfold memValZ; split_ifs <;> omega

/-- The compute table's own challenge valuation: only its slot `1` is nonzero. -/
def compChalZ : ℕ → ℤ := fun j => if j = 1 then 1 else 0

/-- The memory table's own challenge valuation: only its slot `0` (the proof's slot `1`, by
`GigaChips.memChalMap`) is nonzero. -/
def memChalZ : ℕ → ℤ := fun j => if j = 0 then 1 else 0

/-- The integer environment the compute-table block is read in. -/
def compEnvZ : Reified.Env ℤ := ⟨compValZ, compValZ, compChalZ, fun _ => 0⟩

/-- The integer environment the memory-table block is read in. -/
def memEnvZ : Reified.Env ℤ := ⟨memValZ, memValZ, memChalZ, fun _ => 0⟩

/-- The integer environment both walk blocks are read in: everything zero. -/
def walkEnvZ : Reified.Env ℤ := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

set_option maxRecDepth 400000 in
/-- **All 527 `computeAIRchained` gates vanish at the constant row**, of every kind — the 526
row-local gates *and* the `ln` hand-off transition gate. -/
theorem computeAIRchained_vanishes :
    computeAIRchained.constraints.all (fun c => evalZ c.expr compEnvZ == 0) = true := by decide

set_option maxRecDepth 400000 in
/-- **All 80 `memoryAIRchained` gates vanish at the constant row**: the 75 row-local gates, the
`icur` chaining transition, the two axis seed boundaries, the LogUp seed and the LogUp terminal. -/
theorem memoryAIRchained_vanishes :
    (memoryAIRchained (K := ℚ)).constraints.all (fun c => evalZ c.expr memEnvZ == 0) = true := by decide

set_option maxRecDepth 400000 in
/-- **All 7 `walkAIR` gates vanish at the zero row** (given a zero coin and zero publics). -/
theorem walkAIR_vanishes :
    walkAIR.constraints.all (fun c => evalZ c.expr walkEnvZ == 0) = true := by decide

/-! ## 3. The deployment

`gigaParams` is `IOChipCompleteness.chipParams` with two changes: the challenge valuation is
spread over the *proof's* ten slots (the compute table's `1`, the two IO coins at `8`, `9`) rather
than over the IO chip's own two, and `.row` is deployed on the full `n + 1`-row prefix instead of
on `∅`. -/

variable {K : Type*} [Field K]

/-- **The assembled deployment.**  Slot `1` carries the constant `1` both tables' inverse pins
need; slots `8` and `9` are `canonicalIOSlots`, carrying `γ` and the LogUp pole.  Public slot `2` is the shared IO terminal (`ioPubOff`,
`memIoPubOff`); slots `0`, `1` are the walk's `initial_count` and `seed`, both zero. -/
noncomputable def gigaParams (D : OrbitDomain K) (coins : IOCoins K) (terminal : K) (n : ℕ) :
    SegmentedRAPParams K where
  chalVal := fun j =>
    if j = 1 then 1 else if j = 8 then coins.gamma else if j = 9 then coins.pole else 0
  pubVal := fun j => if j < 2 then 0 else terminal
  eDeg := 1
  hExp := D.h + 1
  ω := D.ω
  βcoset := D.βcoset
  domain := fun k => match k with
    | .boundary => D.boundaryDomain
    | .transition => D.transitionDomain (n + 1) (Nat.succ_pos n)
    | .terminal => D.terminalDomain (n + 1) (Nat.succ_pos n)
    | .row => D.rowDomain (n + 1)
  βcoset_ne_zero := D.βcoset_ne_zero
  hExp_pos := Nat.le_add_left 1 D.h

section Deployment

variable (D : OrbitDomain K) (coins : IOCoins K) (terminal : K) (n : ℕ)

@[simp] theorem gigaParams_ω : (gigaParams D coins terminal n).ω = D.ω := rfl

@[simp] theorem gigaParams_domain_boundary :
    (gigaParams D coins terminal n).domain .boundary = D.boundaryDomain := rfl

@[simp] theorem gigaParams_domain_transition :
    (gigaParams D coins terminal n).domain .transition
      = D.transitionDomain (n + 1) (Nat.succ_pos n) := rfl

@[simp] theorem gigaParams_domain_terminal :
    (gigaParams D coins terminal n).domain .terminal
      = D.terminalDomain (n + 1) (Nat.succ_pos n) := rfl

/-- **The row segment is deployed on a non-empty set** — the whole `n + 1`-row prefix.  This is
the difference between this witness and the vacuous one. -/
theorem gigaParams_domain_row :
    (gigaParams D coins terminal n).domain .row = D.rowDomain (n + 1) := rfl

theorem gigaParams_row_nonempty :
    D.βcoset ∈ (gigaParams D coins terminal n).domain .row := by
  show D.βcoset ∈ D.rowDomain (n + 1)
  have : D.orbitPoint 0 ∈ D.rowDomain (n + 1) := by
    simp only [OrbitDomain.rowDomain, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨0, Nat.succ_pos n⟩, rfl⟩
  simpa [OrbitDomain.orbitPoint] using this

/-- The compute table reads the proof's slots `0 … 4`; the valuation there is `compChalZ`. -/
theorem gigaParams_computeChal (i : ℕ) (hi : i < 5) :
    (gigaParams D coins terminal n).chalVal i = ((compChalZ i : ℤ) : K) := by
  interval_cases i
  all_goals simp [gigaParams, compChalZ]

/-- The memory table reads the proof's slots through `memChalMap`; the valuation there is
`memChalZ`. -/
theorem gigaParams_memChal (i : ℕ) (hi : i < 3) :
    (gigaParams D coins terminal n).chalVal (memChalMap i) = ((memChalZ i : ℤ) : K) := by
  interval_cases i
  all_goals simp [gigaParams, memChalZ, memChalMap]

/-- The compute walk reads the proof's slot `5`, which is zero. -/
theorem gigaParams_walkChal (i : ℕ) (hi : i < 1) :
    (gigaParams D coins terminal n).chalVal (i + ComputeChip.walkChalOff) = 0 := by
  interval_cases i
  all_goals simp [gigaParams, ComputeChip.walkChalOff]

/-- The memory walk reads the proof's slot `0`, which is zero. -/
theorem gigaParams_memWalkChal (i : ℕ) (hi : i < 1) :
    (gigaParams D coins terminal n).chalVal (memWalkChalMap i) = 0 := by
  interval_cases i
  all_goals simp [gigaParams, memWalkChalMap]

/-- Both walk blocks' two publics are zero. -/
theorem gigaParams_walkPub (i : ℕ) (hi : i < 2) :
    (gigaParams D coins terminal n).pubVal i = 0 := by
  show (if i < 2 then (0 : K) else terminal) = 0
  rw [if_pos hi]

/-- **The IO block sees exactly `IOChipCompleteness.chipParams`' challenge valuation.** -/
theorem gigaParams_io_chalVal :
    (fun i => (gigaParams D coins terminal n).chalVal (canonicalIOSlots.map i))
      = (IOChip.chipParams D coins terminal n).chalVal := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl
  | (k + 2) =>
      show (gigaParams D coins terminal n).chalVal (canonicalIOSlots.map (k + 2)) = _
      rw [show canonicalIOSlots.map (k + 2) = 0 from by
        simp [IOSlots.map]]
      simp [gigaParams, IOChip.chipParams]

/-- **The IO block sees exactly `IOChipCompleteness.chipParams`' public valuation** (the shared
terminal), at either block offset — `ComputeChip.ioPubOff = memIoPubOff = 2`. -/
theorem gigaParams_io_pubVal (off : ℕ) (hoff : 2 ≤ off) :
    (fun i => (gigaParams D coins terminal n).pubVal (i + off))
      = (IOChip.chipParams D coins terminal n).pubVal := by
  funext i
  show (if i + off < 2 then (0 : K) else terminal) = terminal
  rw [if_neg (by omega)]

end Deployment

/-! ## 4. The two committed traces -/

/-- **The assembled compute chip's 112 committed columns.**  Columns `0 … 99` are the constant
compute-table row and the zero walk row; columns `100 … 111` are `IOChipCompleteness.chipTrace`,
the interpolated prog-IO chip. -/
noncomputable def gigaComputeTrace (D : OrbitDomain K) (n : ℕ)
    (acc inv mult multInv : ℕ → K) (recs : ℕ → Fin 9 → K) :
    Fin (computeCombinedFiniteAIR 10 9 canonicalIOSlots.map).numTraceCols → K[X] :=
  fun j =>
    if h : (j : ℕ) < 100 then Polynomial.C ((compValZ (j : ℕ) : ℤ) : K)
    else IOChip.chipTrace D n acc inv mult multInv recs
      ⟨(j : ℕ) - 100, by have h2 : (j : ℕ) < 113 := j.isLt; omega⟩

/-- **The assembled memory chip's 53 committed columns.** -/
noncomputable def gigaMemoryTrace (D : OrbitDomain K) (n : ℕ)
    (acc inv mult multInv : ℕ → K) (recs : ℕ → Fin 9 → K) :
    Fin (memoryCombinedFiniteAIR (K := K) 10 9 canonicalIOSlots.map).numTraceCols → K[X] :=
  fun j =>
    if h : (j : ℕ) < 42 then Polynomial.C ((memValZ (j : ℕ) : ℤ) : K)
    else IOChip.chipTrace D n acc inv mult multInv recs
      ⟨(j : ℕ) - 42, by have h2 : (j : ℕ) < 55 := j.isLt; omega⟩

section Blocks

variable (D : OrbitDomain K) (n : ℕ) (acc inv mult multInv : ℕ → K) (recs : ℕ → Fin 9 → K)

theorem finComputeBlock_gigaComputeTrace (i : Fin 94) :
    finComputeBlock (gigaComputeTrace D n acc inv mult multInv recs) i
      = Polynomial.C ((compValZ (i : ℕ) : ℤ) : K) := by
  show (if h : ((i : ℕ)) < 100 then _ else _) = _
  rw [dif_pos (by have := i.isLt; omega)]

theorem finWalkBlock_gigaComputeTrace (i : Fin 6) :
    finWalkBlock (gigaComputeTrace D n acc inv mult multInv recs) i = 0 := by
  show (if h : ((i : ℕ) + 94) < 100 then _ else _) = _
  rw [dif_pos (by have := i.isLt; omega),
    compValZ_high ((i : ℕ) + 94) (by omega)]
  simp

theorem finProgIoBlock_gigaComputeTrace :
    finProgIoBlock (gigaComputeTrace D n acc inv mult multInv recs)
      = IOChip.chipTrace D n acc inv mult multInv recs := by
  funext i
  simp only [finProgIoBlock, gigaComputeTrace]
  rw [dif_neg (by omega)]
  exact congrArg (IOChip.chipTrace D n acc inv mult multInv recs) (Fin.ext (by simp))

theorem finMemBlock_gigaMemoryTrace (i : Fin 36) :
    finMemBlock (gigaMemoryTrace D n acc inv mult multInv recs) i
      = Polynomial.C ((memValZ (i : ℕ) : ℤ) : K) := by
  show (if h : ((i : ℕ)) < 42 then _ else _) = _
  rw [dif_pos (by have := i.isLt; omega)]

theorem finMemWalkBlock_gigaMemoryTrace (i : Fin 6) :
    finMemWalkBlock (gigaMemoryTrace D n acc inv mult multInv recs) i = 0 := by
  show (if h : ((i : ℕ) + 36) < 42 then _ else _) = _
  rw [dif_pos (by have := i.isLt; omega),
    memValZ_high ((i : ℕ) + 36) (by omega)]
  simp

theorem finMemIoBlock_gigaMemoryTrace :
    finMemIoBlock (gigaMemoryTrace D n acc inv mult multInv recs)
      = IOChip.chipTrace D n acc inv mult multInv recs := by
  funext i
  simp only [finMemIoBlock, gigaMemoryTrace]
  rw [dif_neg (by omega)]
  exact congrArg (IOChip.chipTrace D n acc inv mult multInv recs) (Fin.ext (by simp))

end Blocks

/-! ## 5. The converse of the fold

`GigaRAPIOSlots.finiteComputeChip_fold_loses_nothing` (`GigaRAPIOSlots.lean:748`) projects
assembled satisfaction down to the three block RAPs.  These two theorems are the missing converse:
they assemble.  They are stated in the per-constraint gate form because that is what both the
projection lemmas and `segmented_is_kinded` consume, and because it keeps the block parameters
implicit rather than forcing the caller to name three `SegmentedRAPParams`. -/

theorem finiteComputeChip_satisfies_of_gates (S : IOSlots) (q : SegmentedRAPParams K)
    (PC : Fin (computeCombinedFiniteAIR 10 9 S.map).numTraceCols → K[X])
    (hcomp : ∀ c ∈ computeAIRchained.constraints, ∀ x ∈ q.domain c.kind,
      c.expr.eval (envOfTrace (finComputeBlock PC) q.ω x q.chalVal q.pubVal) = 0)
    (hwalk : ∀ c ∈ walkAIR.constraints, ∀ x ∈ q.domain c.kind,
      c.expr.eval (envOfTrace (finWalkBlock PC) q.ω x
        (fun i => q.chalVal (i + ComputeChip.walkChalOff)) q.pubVal) = 0)
    (hio : ∀ c ∈ (finiteIOProgAIR 9).constraints, ∀ x ∈ q.domain c.kind,
      c.expr.eval (envOfTrace (finProgIoBlock PC) q.ω x
        (fun i => q.chalVal (S.map i)) (fun i => q.pubVal (i + ComputeChip.ioPubOff))) = 0) :
    (finiteComputeChip S q).Satisfies PC := by
  rw [finiteComputeChip_satisfies_iff_kinded]
  intro c hc x hx
  simp only [computeCombinedFiniteAIR, List.mem_append, List.mem_map] at hc
  rcases hc with (hc | ⟨c0, hc0, rfl⟩) | ⟨c0, hc0, rfl⟩
  · have hvb : c.expr.varsBelow 94 5 0 = true :=
      (List.all_eq_true.mp ComputeChip.computeAIRchained_varsBelow) c hc
    rw [eval_finCompute_block PC q.ω x q.chalVal q.pubVal c.expr hvb]
    exact hcomp c hc x hx
  · have hvb : c0.expr.varsBelow 6 1 2 = true :=
      (List.all_eq_true.mp ComputeChip.walkAIR_varsBelow) c0 hc0
    show (c0.expr.shiftBlock ComputeChip.walkTraceOff ComputeChip.walkChalOff
      ComputeChip.walkPubOff).eval _ = 0
    rw [eval_finWalk_block PC q.ω x q.chalVal q.pubVal c0.expr hvb]
    exact hwalk c0 hc0 x hx
  · have hvb : c0.expr.varsBelow (9 + 4) 2 1 = true :=
      (List.all_eq_true.mp (finiteIOProgAIR_varsBelow 9)) c0 hc0
    show (c0.expr.remapBlock ComputeChip.ioTraceOff S.map ComputeChip.ioPubOff).eval _ = 0
    rw [eval_finProgIo_block PC q.ω x q.chalVal q.pubVal c0.expr hvb]
    exact hio c0 hc0 x hx

theorem finiteMemoryChip_satisfies_of_gates (S : IOSlots) (q : SegmentedRAPParams K)
    (PM : Fin (memoryCombinedFiniteAIR (K := K) 10 9 S.map).numTraceCols → K[X])
    (hmem : ∀ c ∈ (memoryAIRchained (K := K)).constraints, ∀ x ∈ q.domain c.kind,
      c.expr.eval (envOfTrace (finMemBlock PM) q.ω x
        (fun i => q.chalVal (memChalMap i)) q.pubVal) = 0)
    (hwalk : ∀ c ∈ walkAIR.constraints, ∀ x ∈ q.domain c.kind,
      c.expr.eval (envOfTrace (finMemWalkBlock PM) q.ω x
        (fun i => q.chalVal (memWalkChalMap i)) q.pubVal) = 0)
    (hio : ∀ c ∈ (finiteIOMemAIR 9).constraints, ∀ x ∈ q.domain c.kind,
      c.expr.eval (envOfTrace (finMemIoBlock PM) q.ω x
        (fun i => q.chalVal (S.map i)) (fun i => q.pubVal (i + memIoPubOff))) = 0) :
    (finiteMemoryChip S q).Satisfies PM := by
  rw [finiteMemoryChip_satisfies_iff_kinded]
  intro c hc x hx
  simp only [memoryCombinedFiniteAIR, List.mem_append, List.mem_map] at hc
  rcases hc with (⟨c0, hc0, rfl⟩ | ⟨c0, hc0, rfl⟩) | ⟨c0, hc0, rfl⟩
  · have hvb : c0.expr.varsBelow 36 9 0 = true :=
      (List.all_eq_true.mp memoryAIRchained_varsBelow) c0 hc0
    show (c0.expr.remapBlock memTraceOff memChalMap memPubOff).eval _ = 0
    rw [eval_finMem_block PM q.ω x q.chalVal q.pubVal c0.expr hvb]
    exact hmem c0 hc0 x hx
  · have hvb : c0.expr.varsBelow 6 1 2 = true :=
      (List.all_eq_true.mp ComputeChip.walkAIR_varsBelow) c0 hc0
    show (c0.expr.remapBlock memWalkTraceOff memWalkChalMap memWalkPubOff).eval _ = 0
    rw [eval_finMemWalk_block PM q.ω x q.chalVal q.pubVal c0.expr hvb]
    exact hwalk c0 hc0 x hx
  · have hvb : c0.expr.varsBelow (9 + 4) 2 1 = true :=
      (List.all_eq_true.mp (finiteIOMemAIR_varsBelow 9)) c0 hc0
    show (c0.expr.remapBlock memIoTraceOff S.map memIoPubOff).eval _ = 0
    rw [eval_finMemIo_block PM q.ω x q.chalVal q.pubVal c0.expr hvb]
    exact hio c0 hc0 x hx


/-! ## 6. The witness satisfies both assembled chips

The three block obligations, discharged.  The two table blocks and the two walk blocks are
constant, so their gates vanish at *every* point of *every* domain — which is why `.row` may be
deployed non-empty.  The IO block is the real one, and its obligation is exactly
`IOChipCompleteness.chip_satisfies`' own conclusion, taken as a hypothesis here so that it is
supplied once and consumed by both chips. -/

section Witness

variable (D : OrbitDomain K) (coins : IOCoins K) (terminal : K) (n : ℕ)
  (acc inv mult multInv : ℕ → K) (recs : ℕ → Fin 9 → K)

/-- Every `computeAIRchained` gate vanishes on the constant compute block, at every point. -/
theorem compute_block_gates (c : Reified.Constraint)
    (hc : c ∈ computeAIRchained.constraints) (x : K) :
    c.expr.eval (envOfTrace (finComputeBlock (gigaComputeTrace D n acc inv mult multInv recs))
      (gigaParams D coins terminal n).ω x (gigaParams D coins terminal n).chalVal
      (gigaParams D coins terminal n).pubVal) = 0 := by
  have hvb : c.expr.varsBelow 94 5 0 = true :=
    (List.all_eq_true.mp ComputeChip.computeAIRchained_varsBelow) c hc
  have hz : evalZ c.expr compEnvZ = 0 := by
    have h := (List.all_eq_true.mp computeAIRchained_vanishes) c hc
    simpa using h
  have h1 : ∀ i, i < 94 →
      (envOfTrace (finComputeBlock (gigaComputeTrace D n acc inv mult multInv recs))
        (gigaParams D coins terminal n).ω x (gigaParams D coins terminal n).chalVal
        (gigaParams D coins terminal n).pubVal).trace i = (castEnv K compEnvZ).trace i := by
    intro i hi
    simp only [envOfTrace, dif_pos hi, castEnv, compEnvZ,
      finComputeBlock_gigaComputeTrace, Polynomial.eval_C]
  have h2 : ∀ i, i < 94 →
      (envOfTrace (finComputeBlock (gigaComputeTrace D n acc inv mult multInv recs))
        (gigaParams D coins terminal n).ω x (gigaParams D coins terminal n).chalVal
        (gigaParams D coins terminal n).pubVal).traceNext i
        = (castEnv K compEnvZ).traceNext i := by
    intro i hi
    simp only [envOfTrace, dif_pos hi, castEnv, compEnvZ,
      finComputeBlock_gigaComputeTrace, Polynomial.eval_C]
  have h3 : ∀ i, i < 5 →
      (gigaParams D coins terminal n).chalVal i = (castEnv K compEnvZ).chal i :=
    fun i hi => gigaParams_computeChal D coins terminal n i hi
  rw [Reified.Expr.eval_congr_of_varsBelow c.expr hvb h1 h2 h3 (fun i hi => absurd hi (by omega)),
    eval_castEnv, hz, Int.cast_zero]

/-- Every `walkAIR` gate vanishes on the zero compute-walk block, at every point. -/
theorem compute_walk_gates (c : Reified.Constraint)
    (hc : c ∈ walkAIR.constraints) (x : K) :
    c.expr.eval (envOfTrace (finWalkBlock (gigaComputeTrace D n acc inv mult multInv recs))
      (gigaParams D coins terminal n).ω x
      (fun i => (gigaParams D coins terminal n).chalVal (i + ComputeChip.walkChalOff))
      (gigaParams D coins terminal n).pubVal) = 0 := by
  have hvb : c.expr.varsBelow 6 1 2 = true :=
    (List.all_eq_true.mp ComputeChip.walkAIR_varsBelow) c hc
  have hz : evalZ c.expr walkEnvZ = 0 := by
    have h := (List.all_eq_true.mp walkAIR_vanishes) c hc
    simpa using h
  have h1 : ∀ i, i < 6 →
      (envOfTrace (finWalkBlock (gigaComputeTrace D n acc inv mult multInv recs))
        (gigaParams D coins terminal n).ω x
        (fun i => (gigaParams D coins terminal n).chalVal (i + ComputeChip.walkChalOff))
        (gigaParams D coins terminal n).pubVal).trace i = (castEnv K walkEnvZ).trace i := by
    intro i hi
    simp only [envOfTrace, dif_pos hi, castEnv, walkEnvZ,
      finWalkBlock_gigaComputeTrace, Polynomial.eval_zero, Int.cast_zero]
  have h2 : ∀ i, i < 6 →
      (envOfTrace (finWalkBlock (gigaComputeTrace D n acc inv mult multInv recs))
        (gigaParams D coins terminal n).ω x
        (fun i => (gigaParams D coins terminal n).chalVal (i + ComputeChip.walkChalOff))
        (gigaParams D coins terminal n).pubVal).traceNext i
        = (castEnv K walkEnvZ).traceNext i := by
    intro i hi
    simp only [envOfTrace, dif_pos hi, castEnv, walkEnvZ,
      finWalkBlock_gigaComputeTrace, Polynomial.eval_zero, Int.cast_zero]
  have h3 : ∀ i, i < 1 →
      (gigaParams D coins terminal n).chalVal (i + ComputeChip.walkChalOff)
        = (castEnv K walkEnvZ).chal i := by
    intro i hi
    rw [gigaParams_walkChal D coins terminal n i hi]
    simp [castEnv, walkEnvZ]
  have h4 : ∀ i, i < 2 →
      (gigaParams D coins terminal n).pubVal i = (castEnv K walkEnvZ).pub i := by
    intro i hi
    rw [gigaParams_walkPub D coins terminal n i hi]
    simp [castEnv, walkEnvZ]
  rw [Reified.Expr.eval_congr_of_varsBelow c.expr hvb h1 h2 h3 h4, eval_castEnv, hz, Int.cast_zero]

set_option maxHeartbeats 8000000
/-- Every `memoryAIRchained` gate vanishes on the constant memory block, at every point. -/
theorem memory_block_gates (c : Reified.Constraint)
    (hc : c ∈ (memoryAIRchained (K := K)).constraints) (x : K) :
    c.expr.eval (envOfTrace (finMemBlock (gigaMemoryTrace D n acc inv mult multInv recs))
      (gigaParams D coins terminal n).ω x
      (fun i => (gigaParams D coins terminal n).chalVal (memChalMap i))
      (gigaParams D coins terminal n).pubVal) = 0 := by
  have hvb : c.expr.varsBelow 36 9 0 = true :=
    (List.all_eq_true.mp memoryAIRchained_varsBelow) c hc
  have hz : evalZ c.expr memEnvZ = 0 := by
    have hdec : memEqBlkExprs (K := K) .decompose = @memEqBlkExprs ℚ _ .decompose := rfl
    have hhalt : memEqBlkExprs (K := K) .halt = @memEqBlkExprs ℚ _ .halt := rfl
    have hsel0 (i : ℕ) (hi0 : i ≠ 0) (hi34 : i ≠ 34) : evalZ (tc i) memEnvZ = 0 := by
      simp [evalZ, tc, memEnvZ, memValZ, hi0, hi34]
    have hgated (e : Expr) (he : e ∈ memPerStateGated (K := K)) :
        evalZ e memEnvZ = 0 := by
      unfold memPerStateGated at he
      obtain ⟨k, -, hke⟩ := List.mem_flatMap.mp he
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hke
      cases k with
      | decompose =>
          have heQ : gateByM .decompose e' ∈ memPerStateGated (K := ℚ) := by
            unfold memPerStateGated
            refine List.mem_flatMap.mpr ⟨.decompose, by simp [allMStates], ?_⟩
            refine List.mem_map.mpr ⟨e', ?_, rfl⟩
            simpa [hdec] using he'
          have : (⟨.row, gateByM .decompose e'⟩ : Constraint) ∈
              (memoryAIRchained (K := ℚ)).constraints := by
            simp [memoryAIRchained, Reified.memoryAIR, heQ]
          exact of_decide_eq_true
            ((List.all_eq_true.mp memoryAIRchained_vanishes) _ this)
      | halt =>
          change evalZ (.Mul (tc 1) e') memEnvZ = 0
          simp [evalZ, hsel0 1 (by decide) (by decide)]
      | read_root =>
          change evalZ (.Mul (tc 2) e') memEnvZ = 0
          simp [evalZ, hsel0 2 (by decide) (by decide)]
      | verify_child =>
          change evalZ (.Mul (tc 3) e') memEnvZ = 0
          simp [evalZ, hsel0 3 (by decide) (by decide)]
    simp [memoryAIRchained, Reified.memoryAIR, List.mem_append, List.mem_map] at hc
    have vanishQ (e : Expr) (k : ConstraintKind)
        (hm : (⟨k, e⟩ : Constraint) ∈ (memoryAIRchained (K := ℚ)).constraints) :
        evalZ e memEnvZ = 0 :=
      of_decide_eq_true ((List.all_eq_true.mp memoryAIRchained_vanishes) _ hm)
    rcases hc with hsv | hzinv | hg | hchain | hseed | hipre | hicur
    · obtain ⟨e, he, hc⟩ := hsv
      have heq : c.expr = e := by cases c; cases hc; rfl
      rw [heq]
      exact vanishQ e .row (by
        refine List.mem_append.mpr (Or.inl ?_)
        refine List.mem_append.mpr (Or.inl ?_)
        refine List.mem_append.mpr (Or.inl ?_)
        refine List.mem_append.mpr (Or.inl ?_)
        refine List.mem_append.mpr (Or.inl ?_)
        exact List.mem_map.mpr ⟨e, he, rfl⟩)
    · have heq : c.expr = zZinvExprM := by cases c; cases hzinv; rfl
      rw [heq]
      exact vanishQ zZinvExprM .row (by
        simp [memoryAIRchained, Reified.memoryAIR])
    · obtain ⟨e, he, hc⟩ := hg
      have heq : c.expr = e := by cases c; cases hc; rfl
      rw [heq]
      exact hgated e he
    · have heq : c.expr = icurChainExpr := by cases c; cases hchain; rfl
      rw [heq]
      exact vanishQ icurChainExpr .transition (by
        simp [memoryAIRchained, Reified.memoryAIR])
    · obtain ⟨e, he, hc⟩ := hseed
      have heq : c.expr = e := by cases c; cases hc; rfl
      rw [heq]
      exact vanishQ e .boundary (by
        simp [memoryAIRchained, Reified.memoryAIR, List.mem_append, List.mem_map, he])
    · have heq : c.expr = memIpreInitExpr := by cases c; cases hipre; rfl
      rw [heq]
      exact vanishQ memIpreInitExpr .boundary (by
        simp [memoryAIRchained, Reified.memoryAIR])
    · have heq : c.expr = memIcurTermExpr := by cases c; cases hicur; rfl
      rw [heq]
      exact vanishQ memIcurTermExpr .terminal (by
        simp [memoryAIRchained, Reified.memoryAIR])
  have h1 : ∀ i, i < 36 →
      (envOfTrace (finMemBlock (gigaMemoryTrace D n acc inv mult multInv recs))
        (gigaParams D coins terminal n).ω x
        (fun i => (gigaParams D coins terminal n).chalVal (memChalMap i))
        (gigaParams D coins terminal n).pubVal).trace i = (castEnv K memEnvZ).trace i := by
    intro i hi
    simp only [envOfTrace, dif_pos hi, castEnv, memEnvZ,
      finMemBlock_gigaMemoryTrace, Polynomial.eval_C]
  have h2 : ∀ i, i < 36 →
      (envOfTrace (finMemBlock (gigaMemoryTrace D n acc inv mult multInv recs))
        (gigaParams D coins terminal n).ω x
        (fun i => (gigaParams D coins terminal n).chalVal (memChalMap i))
        (gigaParams D coins terminal n).pubVal).traceNext i = (castEnv K memEnvZ).traceNext i := by
    intro i hi
    simp only [envOfTrace, dif_pos hi, castEnv, memEnvZ,
      finMemBlock_gigaMemoryTrace, Polynomial.eval_C]
  have h3 : ∀ i, i < 9 →
      (envOfTrace (finMemBlock (gigaMemoryTrace D n acc inv mult multInv recs))
        (gigaParams D coins terminal n).ω x
        (fun i => (gigaParams D coins terminal n).chalVal (memChalMap i))
        (gigaParams D coins terminal n).pubVal).chal i
        = (castEnv K memEnvZ).chal i := by
    intro i hi
    simp only [envOfTrace]
    if hlt : i < 3 then
      exact gigaParams_memChal D coins terminal n i hlt
    else
      have : memChalZ i = 0 := by
        unfold memChalZ; split_ifs <;> omega
      have hmap : memChalMap i = 0 := by
        unfold memChalMap
        split
        · omega
        · omega
        · omega
        · rfl
        · rfl
      simp [gigaParams, hmap, castEnv, memEnvZ, this]
  rw [Reified.Expr.eval_congr_of_varsBelow c.expr hvb h1 h2 h3 (fun i hi => absurd hi (by omega)),
    eval_castEnv, hz, Int.cast_zero]

/-- Every `walkAIR` gate vanishes on the zero memory-walk block, at every point. -/
theorem memory_walk_gates (c : Reified.Constraint)
    (hc : c ∈ walkAIR.constraints) (x : K) :
    c.expr.eval (envOfTrace (finMemWalkBlock (gigaMemoryTrace D n acc inv mult multInv recs))
      (gigaParams D coins terminal n).ω x
      (fun i => (gigaParams D coins terminal n).chalVal (memWalkChalMap i))
      (gigaParams D coins terminal n).pubVal) = 0 := by
  have hvb : c.expr.varsBelow 6 1 2 = true :=
    (List.all_eq_true.mp ComputeChip.walkAIR_varsBelow) c hc
  have hz : evalZ c.expr walkEnvZ = 0 := by
    have h := (List.all_eq_true.mp walkAIR_vanishes) c hc
    simpa using h
  have h1 : ∀ i, i < 6 →
      (envOfTrace (finMemWalkBlock (gigaMemoryTrace D n acc inv mult multInv recs))
        (gigaParams D coins terminal n).ω x
        (fun i => (gigaParams D coins terminal n).chalVal (memWalkChalMap i))
        (gigaParams D coins terminal n).pubVal).trace i = (castEnv K walkEnvZ).trace i := by
    intro i hi
    simp only [envOfTrace, dif_pos hi, castEnv, walkEnvZ,
      finMemWalkBlock_gigaMemoryTrace, Polynomial.eval_zero, Int.cast_zero]
  have h2 : ∀ i, i < 6 →
      (envOfTrace (finMemWalkBlock (gigaMemoryTrace D n acc inv mult multInv recs))
        (gigaParams D coins terminal n).ω x
        (fun i => (gigaParams D coins terminal n).chalVal (memWalkChalMap i))
        (gigaParams D coins terminal n).pubVal).traceNext i = (castEnv K walkEnvZ).traceNext i := by
    intro i hi
    simp only [envOfTrace, dif_pos hi, castEnv, walkEnvZ,
      finMemWalkBlock_gigaMemoryTrace, Polynomial.eval_zero, Int.cast_zero]
  have h3 : ∀ i, i < 1 →
      (gigaParams D coins terminal n).chalVal (memWalkChalMap i) = (castEnv K walkEnvZ).chal i := by
    intro i hi
    rw [gigaParams_memWalkChal D coins terminal n i hi]
    simp [castEnv, walkEnvZ]
  have h4 : ∀ i, i < 2 →
      (gigaParams D coins terminal n).pubVal i = (castEnv K walkEnvZ).pub i := by
    intro i hi
    rw [gigaParams_walkPub D coins terminal n i hi]
    simp [castEnv, walkEnvZ]
  rw [Reified.Expr.eval_congr_of_varsBelow c.expr hvb h1 h2 h3 h4, eval_castEnv, hz, Int.cast_zero]

/-- **The assembled compute chip is satisfied**: 112 columns, 538 constraints, all four kinds on
non-empty domains. -/
theorem gigaComputeTrace_satisfies
    (hio : ∀ k : Reified.ConstraintKind,
      ((IOChip.chipParams D coins terminal n).rap (finiteIOProgAIR 9) k).Satisfies
        (IOChip.chipTrace D n acc inv mult multInv recs)) :
    (finiteComputeChip canonicalIOSlots (gigaParams D coins terminal n)).Satisfies
      (gigaComputeTrace D n acc inv mult multInv recs) := by
  refine finiteComputeChip_satisfies_of_gates canonicalIOSlots (gigaParams D coins terminal n)
    (gigaComputeTrace D n acc inv mult multInv recs)
    (fun c hc x _ => compute_block_gates D coins terminal n acc inv mult multInv recs c hc x)
    (fun c hc x _ => compute_walk_gates D coins terminal n acc inv mult multInv recs c hc x)
    ?_
  intro c hc x hx
  have hc' := hc
  have hdom : (gigaParams D coins terminal n).domain c.kind
      = (IOChip.chipParams D coins terminal n).domain c.kind := by
    simp only [finiteIOProgAIR, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl
    all_goals rfl
  have hg := IOChip.gates_vanish_of_satisfies (IOChip.chipParams D coins terminal n)
    (finiteIOProgAIR 9) (IOChip.chipTrace D n acc inv mult multInv recs) hio c hc x (hdom ▸ hx)
  rw [finProgIoBlock_gigaComputeTrace, gigaParams_io_chalVal,
    gigaParams_io_pubVal D coins terminal n ComputeChip.ioPubOff (by decide)]
  exact hg

/-- **The assembled memory chip is satisfied**: 54 columns, 93 constraints. -/
theorem gigaMemoryTrace_satisfies
    (hio : ∀ k : Reified.ConstraintKind,
      ((IOChip.chipParams D coins terminal n).rap (finiteIOMemAIR 9) k).Satisfies
        (IOChip.chipTrace D n acc inv mult multInv recs)) :
    (finiteMemoryChip canonicalIOSlots (gigaParams D coins terminal n)).Satisfies
      (gigaMemoryTrace D n acc inv mult multInv recs) := by
  refine finiteMemoryChip_satisfies_of_gates canonicalIOSlots (gigaParams D coins terminal n)
    (gigaMemoryTrace D n acc inv mult multInv recs)
    (fun c hc x _ => memory_block_gates D coins terminal n acc inv mult multInv recs c hc x)
    (fun c hc x _ => memory_walk_gates D coins terminal n acc inv mult multInv recs c hc x)
    ?_
  intro c hc x hx
  have hc' := hc
  have hdom : (gigaParams D coins terminal n).domain c.kind
      = (IOChip.chipParams D coins terminal n).domain c.kind := by
    simp only [finiteIOMemAIR, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl
  have hg := IOChip.gates_vanish_of_satisfies (IOChip.chipParams D coins terminal n)
    (finiteIOMemAIR 9) (IOChip.chipTrace D n acc inv mult multInv recs) hio c hc x (hdom ▸ hx)
  rw [finMemIoBlock_gigaMemoryTrace, gigaParams_io_chalVal,
    gigaParams_io_pubVal D coins terminal n memIoPubOff (by decide)]
  exact hg

end Witness


/-! ## 7. Transporting `ChipRows` / `ChipAgreement` between deployments

`ChipRows` reads only the boundary/transition/terminal domains and `ω`; `ChipAgreement` reads only
`ω`, two challenge slots and public slot `0`.  Neither mentions `.row`, which is the single field
on which `gigaParams` and `IOChipCompleteness.chipParams` differ. -/

theorem chipRows_transfer (q q' : SegmentedRAPParams K) (hω : q.ω = q'.ω)
    (hb : q.domain .boundary = q'.domain .boundary)
    (ht : q.domain .transition = q'.domain .transition)
    (hm : q.domain .terminal = q'.domain .terminal)
    (nn : ℕ) (x₀ : K) (h : IOChip.ChipRows nn q' x₀) : IOChip.ChipRows nn q x₀ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [IOChip.rowPt, hω, hb]; exact h.boundary_mem
  · intro i hi; rw [IOChip.rowPt, hω, ht]; exact h.transition_mem i hi
  · rw [IOChip.rowPt, hω, hm]; exact h.terminal_mem

theorem chipAgreement_transfer {w : ℕ} (q q' : SegmentedRAPParams K) (hω : q.ω = q'.ω)
    (hc0 : q.chalVal 0 = q'.chalVal 0) (hc1 : q.chalVal 1 = q'.chalVal 1)
    (hp0 : q.pubVal 0 = q'.pubVal 0)
    (recsL : List (Fin 9 → K)) (coins : IOCoins K) (terminal x₀ : K) (P : Fin w → K[X])
    (h : IOChip.ChipAgreement recsL coins terminal q' x₀ P) :
    IOChip.ChipAgreement recsL coins terminal q x₀ P := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc0]; exact h.gamma_eq
  · rw [hc1]; exact h.pole_eq
  · rw [hp0]; exact h.terminal_eq
  · intro i c
    have hr := h.record_eq i c
    simpa only [IOChip.rowEnv, IOChip.rowPt, envOfTrace, hω] using hr

/-! ## 8. The whole hypothesis bundle of `io_lio_of_giga_satisfies`

Every hypothesis of `GigaRAPIOSlots.io_lio_of_giga_satisfies` (`GigaRAPIOSlots.lean:805`) other
than the five range/uniqueness/counted-event side conditions — which are conditions on the records
and the coins, not on the trace — holds simultaneously at this witness.  The scalar-column
plumbing mirrors `IOChipCompleteness.satisfies_of_io_lio` (`IOChipCompleteness.lean:475`); the new
content is that the columns are placed in the **assembled** 112- and 53-column traces. -/

theorem giga_bundle_of_io_lio {Ksz : ℕ} (D : OrbitDomain K)
    (records : PreChallengeRecords K 9) (coins : IOCoins K)
    (hlio : IO.LIO Ksz records.requests records.responses)
    (hden : ∀ v ∈ records.requests ++ records.responses, compress coins v ≠ 0)
    (hcap : records.requests.length + 1 ≤ 2 ^ D.h) :
    ∃ (terminal : K) (qC qM : SegmentedRAPParams K) (x₀p x₀m : K)
      (PC : Fin (computeCombinedFiniteAIR 10 9 canonicalIOSlots.map).numTraceCols → K[X])
      (PM : Fin (memoryCombinedFiniteAIR (K := K) 10 9 canonicalIOSlots.map).numTraceCols → K[X]),
        (finiteComputeChip canonicalIOSlots qC).Satisfies PC
      ∧ (finiteMemoryChip canonicalIOSlots qM).Satisfies PM
      ∧ IOChip.ChipRows records.requests.length
          (remapParams qC canonicalIOSlots.map ComputeChip.ioPubOff) x₀p
      ∧ IOChip.ChipRows records.responses.length
          (remapParams qM canonicalIOSlots.map memIoPubOff) x₀m
      ∧ IOChip.ChipAgreement records.requests coins terminal
          (remapParams qC canonicalIOSlots.map ComputeChip.ioPubOff) x₀p (finProgIoBlock PC)
      ∧ IOChip.ChipAgreement records.responses coins terminal
          (remapParams qM canonicalIOSlots.map memIoPubOff) x₀m (finMemIoBlock PM)
      ∧ qC.domain .row = D.rowDomain (records.requests.length + 1)
      ∧ qM.domain .row = D.rowDomain (records.responses.length + 1) := by
  classical
  obtain ⟨w, hw⟩ := finiteIO_complete_of_LIO (Ksz := Ksz) records coins hlio hden
  have hlen : records.requests.length = records.responses.length := hlio.2.2.length_eq
  -- request-side scalar columns
  have hPinit : IOChip.natOfFin w.requestAcc 0 = 0 := by
    have h0 := IOChip.natOfFin_apply w.requestAcc (0 : Fin (records.requests.length + 1))
    rw [show ((0 : Fin (records.requests.length + 1)) : ℕ) = 0 from rfl] at h0
    rw [h0, hw.requestInit]
  have hPpin : ∀ i, i < records.requests.length →
      compress coins (IOChip.listCol records.requests i) * IOChip.natOfFin w.requestInv i = 1 := by
    intro i hi
    rw [show IOChip.listCol records.requests i = records.requests.get ⟨i, hi⟩ from
      IOChip.listCol_get records.requests ⟨i, hi⟩,
      show IOChip.natOfFin w.requestInv i = w.requestInv ⟨i, hi⟩ from
      IOChip.natOfFin_apply w.requestInv ⟨i, hi⟩]
    exact hw.requestInvPin ⟨i, hi⟩
  have hPstep : ∀ i, i < records.requests.length →
      IOChip.natOfFin w.requestAcc (i + 1)
        = IOChip.natOfFin w.requestAcc i + IOChip.natOfFin w.requestInv i := by
    intro i hi
    have hs := hw.requestStep ⟨i, hi⟩
    rw [show IOChip.natOfFin w.requestAcc (i + 1) = w.requestAcc (Fin.succ ⟨i, hi⟩) from
        IOChip.natOfFin_apply w.requestAcc (Fin.succ ⟨i, hi⟩),
      show IOChip.natOfFin w.requestAcc i = w.requestAcc (Fin.castSucc ⟨i, hi⟩) from
        IOChip.natOfFin_apply w.requestAcc (Fin.castSucc ⟨i, hi⟩),
      show IOChip.natOfFin w.requestInv i = w.requestInv ⟨i, hi⟩ from
        IOChip.natOfFin_apply w.requestInv ⟨i, hi⟩]
    exact hs
  have hPterm : IOChip.natOfFin w.requestAcc records.requests.length = w.terminal := by
    rw [show IOChip.natOfFin w.requestAcc records.requests.length
        = w.requestAcc (Fin.last records.requests.length) from
      IOChip.natOfFin_apply w.requestAcc (Fin.last records.requests.length)]
    exact hw.requestTerm
  have hPstepM : ∀ i, i < records.requests.length →
      IOChip.natOfFin w.requestAcc (i + 1)
        = IOChip.natOfFin w.requestAcc i
          + (fun _ : ℕ => (1 : K)) i * IOChip.natOfFin w.requestInv i := by
    intro i hi; rw [hPstep i hi, one_mul]
  -- response-side scalar columns
  have hMinit : IOChip.natOfFin w.responseAcc 0 = 0 := by
    have h0 := IOChip.natOfFin_apply w.responseAcc (0 : Fin (records.responses.length + 1))
    rw [show ((0 : Fin (records.responses.length + 1)) : ℕ) = 0 from rfl] at h0
    rw [h0, hw.responseInit]
  have hMpin : ∀ i, i < records.responses.length →
      compress coins (IOChip.listCol records.responses i)
        * IOChip.natOfFin w.responseInv i = 1 := by
    intro i hi
    rw [show IOChip.listCol records.responses i = records.responses.get ⟨i, hi⟩ from
      IOChip.listCol_get records.responses ⟨i, hi⟩,
      show IOChip.natOfFin w.responseInv i = w.responseInv ⟨i, hi⟩ from
      IOChip.natOfFin_apply w.responseInv ⟨i, hi⟩]
    exact hw.responseInvPin ⟨i, hi⟩
  have hMbool : ∀ i, i < records.responses.length →
      IOChip.natOfFin w.multiplicity i * (IOChip.natOfFin w.multiplicity i - 1) = 0 := by
    intro i hi
    rw [show IOChip.natOfFin w.multiplicity i = w.multiplicity ⟨i, hi⟩ from
      IOChip.natOfFin_apply w.multiplicity ⟨i, hi⟩]
    exact hw.multBool ⟨i, hi⟩
  have hMminv : ∀ i, i < records.responses.length →
      IOChip.natOfFin w.multiplicity i * IOChip.natOfFin w.multInv i = 1 := by
    intro i hi
    rw [show IOChip.natOfFin w.multiplicity i = w.multiplicity ⟨i, hi⟩ from
      IOChip.natOfFin_apply w.multiplicity ⟨i, hi⟩,
      show IOChip.natOfFin w.multInv i = w.multInv ⟨i, hi⟩ from
      IOChip.natOfFin_apply w.multInv ⟨i, hi⟩]
    exact hw.multInvPin ⟨i, hi⟩
  have hMstepM : ∀ i, i < records.responses.length →
      IOChip.natOfFin w.responseAcc (i + 1)
        = IOChip.natOfFin w.responseAcc i
          + IOChip.natOfFin w.multiplicity i * IOChip.natOfFin w.responseInv i := by
    intro i hi
    have hs := hw.responseStep ⟨i, hi⟩
    rw [show IOChip.natOfFin w.responseAcc (i + 1) = w.responseAcc (Fin.succ ⟨i, hi⟩) from
        IOChip.natOfFin_apply w.responseAcc (Fin.succ ⟨i, hi⟩),
      show IOChip.natOfFin w.responseAcc i = w.responseAcc (Fin.castSucc ⟨i, hi⟩) from
        IOChip.natOfFin_apply w.responseAcc (Fin.castSucc ⟨i, hi⟩),
      show IOChip.natOfFin w.responseInv i = w.responseInv ⟨i, hi⟩ from
        IOChip.natOfFin_apply w.responseInv ⟨i, hi⟩,
      show IOChip.natOfFin w.multiplicity i = w.multiplicity ⟨i, hi⟩ from
        IOChip.natOfFin_apply w.multiplicity ⟨i, hi⟩]
    exact hs
  have hMstepP : ∀ i, i < records.responses.length →
      IOChip.natOfFin w.responseAcc (i + 1)
        = IOChip.natOfFin w.responseAcc i + IOChip.natOfFin w.responseInv i := by
    intro i hi
    rw [hMstepM i hi, show IOChip.natOfFin w.multiplicity i = w.multiplicity ⟨i, hi⟩ from
      IOChip.natOfFin_apply w.multiplicity ⟨i, hi⟩, multiplicity_eq_one hw ⟨i, hi⟩, one_mul]
  have hMterm : IOChip.natOfFin w.responseAcc records.responses.length = w.terminal := by
    rw [show IOChip.natOfFin w.responseAcc records.responses.length
        = w.responseAcc (Fin.last records.responses.length) from
      IOChip.natOfFin_apply w.responseAcc (Fin.last records.responses.length)]
    exact hw.responseTerm
  have hcapM : records.responses.length + 1 ≤ 2 ^ D.h := by rw [← hlen]; exact hcap
  obtain ⟨satP, -, rowsP, agreeP⟩ :=
    IOChip.chip_satisfies D coins w.terminal records.requests (IOChip.natOfFin w.requestAcc)
      (IOChip.natOfFin w.requestInv) (fun _ => 1) (fun _ => 1) hcap hPinit hPpin
      (fun i _ => by ring) (fun i _ => by ring) hPstep hPstepM hPterm
  obtain ⟨-, satM, rowsM, agreeM⟩ :=
    IOChip.chip_satisfies D coins w.terminal records.responses (IOChip.natOfFin w.responseAcc)
      (IOChip.natOfFin w.responseInv) (IOChip.natOfFin w.multiplicity)
      (IOChip.natOfFin w.multInv) hcapM hMinit hMpin hMbool hMminv hMstepP hMstepM hMterm
  refine ⟨w.terminal, gigaParams D coins w.terminal records.requests.length,
    gigaParams D coins w.terminal records.responses.length, D.βcoset, D.βcoset,
    gigaComputeTrace D records.requests.length (IOChip.natOfFin w.requestAcc)
      (IOChip.natOfFin w.requestInv) (fun _ => 1) (fun _ => 1) (IOChip.listCol records.requests),
    gigaMemoryTrace D records.responses.length (IOChip.natOfFin w.responseAcc)
      (IOChip.natOfFin w.responseInv) (IOChip.natOfFin w.multiplicity)
      (IOChip.natOfFin w.multInv) (IOChip.listCol records.responses),
    ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · exact gigaComputeTrace_satisfies D coins w.terminal records.requests.length _ _ _ _ _ satP
  · exact gigaMemoryTrace_satisfies D coins w.terminal records.responses.length _ _ _ _ _ satM
  · exact chipRows_transfer
      (remapParams (gigaParams D coins w.terminal records.requests.length)
        canonicalIOSlots.map ComputeChip.ioPubOff)
      (IOChip.chipParams D coins w.terminal records.requests.length)
      rfl rfl rfl rfl _ _ rowsP
  · exact chipRows_transfer
      (remapParams (gigaParams D coins w.terminal records.responses.length)
        canonicalIOSlots.map memIoPubOff)
      (IOChip.chipParams D coins w.terminal records.responses.length)
      rfl rfl rfl rfl _ _ rowsM
  · refine chipAgreement_transfer
      (remapParams (gigaParams D coins w.terminal records.requests.length)
        canonicalIOSlots.map ComputeChip.ioPubOff)
      (IOChip.chipParams D coins w.terminal records.requests.length) rfl
      (congrFun (gigaParams_io_chalVal D coins w.terminal records.requests.length) 0)
      (congrFun (gigaParams_io_chalVal D coins w.terminal records.requests.length) 1)
      (congrFun (gigaParams_io_pubVal D coins w.terminal records.requests.length
        ComputeChip.ioPubOff (by decide)) 0) _ _ _ _ _ ?_
    rw [finProgIoBlock_gigaComputeTrace]
    exact agreeP
  · refine chipAgreement_transfer
      (remapParams (gigaParams D coins w.terminal records.responses.length)
        canonicalIOSlots.map memIoPubOff)
      (IOChip.chipParams D coins w.terminal records.responses.length) rfl
      (congrFun (gigaParams_io_chalVal D coins w.terminal records.responses.length) 0)
      (congrFun (gigaParams_io_chalVal D coins w.terminal records.responses.length) 1)
      (congrFun (gigaParams_io_pubVal D coins w.terminal records.responses.length
        memIoPubOff (by decide)) 0) _ _ _ _ _ ?_
    rw [finMemIoBlock_gigaMemoryTrace]
    exact agreeM


/-! ## 9. A concrete, unconditional instance over `ZMod 97`

The analogue of `IOChipCompleteness.satisfies_of_io_lio_concrete` (`IOChipCompleteness.lean:692`)
for the **assembled** chips: a closed term, no hypotheses, on a two-row orbit with one genuine
record row and one terminal row. -/

section Concrete

local instance primeGigaWitness97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- The one-record deployment used below. -/
def concreteRecords : PreChallengeRecords (ZMod 97) 9 :=
  ⟨[(0 : Fin 9 → ZMod 97)], [(0 : Fin 9 → ZMod 97)]⟩

/-- The coins used below: `γ = 0`, pole `= 1`. -/
def concreteCoins : IOCoins (ZMod 97) := ⟨0, 1⟩

theorem concrete_compress_ne_zero :
    compress concreteCoins (0 : Fin 9 → ZMod 97) ≠ 0 := by
  show (1 : ZMod 97) + Walk.rlc (0 : ZMod 97) (0 : Fin 9 → ZMod 97) ≠ 0
  rw [show Walk.rlc (0 : ZMod 97) (0 : Fin 9 → ZMod 97) = 0 from by simp [Walk.rlc], add_zero]
  decide

/-- **Unconditional non-vacuity of the assembled chips.**  Both the 112-column / 538-constraint
compute chip and the 53-column / 93-constraint memory chip are satisfied, with all four constraint
kinds deployed on non-empty domains, together with the `ChipRows` and `ChipAgreement` data at a
genuine record. -/
theorem giga_bundle_concrete :
    ∃ (terminal : ZMod 97) (qC qM : SegmentedRAPParams (ZMod 97)) (x₀p x₀m : ZMod 97)
      (PC : Fin (computeCombinedFiniteAIR 10 9 canonicalIOSlots.map).numTraceCols → (ZMod 97)[X])
      (PM : Fin (memoryCombinedFiniteAIR (K := ZMod 97) 10 9 canonicalIOSlots.map).numTraceCols → (ZMod 97)[X]),
        (finiteComputeChip canonicalIOSlots qC).Satisfies PC
      ∧ (finiteMemoryChip canonicalIOSlots qM).Satisfies PM
      ∧ IOChip.ChipRows concreteRecords.requests.length
          (remapParams qC canonicalIOSlots.map ComputeChip.ioPubOff) x₀p
      ∧ IOChip.ChipRows concreteRecords.responses.length
          (remapParams qM canonicalIOSlots.map memIoPubOff) x₀m
      ∧ IOChip.ChipAgreement concreteRecords.requests concreteCoins terminal
          (remapParams qC canonicalIOSlots.map ComputeChip.ioPubOff) x₀p (finProgIoBlock PC)
      ∧ IOChip.ChipAgreement concreteRecords.responses concreteCoins terminal
          (remapParams qM canonicalIOSlots.map memIoPubOff) x₀m (finMemIoBlock PM)
      ∧ qC.domain .row = IOChip.concreteOrbit.rowDomain (concreteRecords.requests.length + 1)
      ∧ qM.domain .row = IOChip.concreteOrbit.rowDomain (concreteRecords.responses.length + 1) := by
  obtain ⟨hlio, hden, hcap⟩ :=
    IOChip.completeness_hypotheses_inhabited IOChip.concreteOrbit (le_refl 1) concreteCoins
      (0 : Fin 9 → ZMod 97) concrete_compress_ne_zero
  exact giga_bundle_of_io_lio (Ksz := 1) IOChip.concreteOrbit concreteRecords concreteCoins
    hlio hden hcap

end Concrete

/-! ## 10. Non-vacuity of the composition at production coins

`GigaRAPIOSlots.io_lio_of_giga_satisfies_at_production_coins` (`GigaRAPIOSlots.lean:963`) is now
known to have a simultaneously-satisfiable hypothesis bundle.  `giga_composition_roundtrip` is the
machine-checked form of that claim: it compiles only if the seven objects produced here are
*literally* the seven that theorem consumes, in its own order, at its own types. -/

section Composition

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F]
  {hOrb : ℕ} (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)

omit [Fintype F] [DecidableEq F] in
/-- **The package's sampled pole misses every compressed record.**  This is
`SampledIOSameExecutionAssignment.poleHitGood` read as a denominator condition; it is what the
honest prover needs in order to commit the reciprocal column at all. -/
theorem sampled_compress_ne_zero
    (v : Fin 9 → K)
    (hv : v ∈ P.optimized.sampled.sampled.records.requests
            ++ P.optimized.sampled.sampled.records.responses) :
    compress P.optimized.sampled.sampled.coins v ≠ 0 := by
  classical
  intro hzero
  refine P.optimized.sampled.poleHitGood ?_
  simp only [IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨v, hv, by simpa [compress] using hzero⟩

/-- **The whole hypothesis bundle of the composition, at the package's own records and coins.**
The coins are `ioCoinsOf c`, identified with the sampled pair by
`IOCoinReconciliation.ioCoinsOf_eq_sampled`; the records are the package's own. -/
theorem giga_bundle_at_production_coins
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (D : OrbitDomain K)
    (hcap : P.optimized.sampled.sampled.records.requests.length + 1 ≤ 2 ^ D.h) :
    ∃ (terminal : K) (qC qM : SegmentedRAPParams K) (x₀p x₀m : K)
      (PC : Fin (computeCombinedFiniteAIR 10 9 canonicalIOSlots.map).numTraceCols → K[X])
      (PM : Fin (memoryCombinedFiniteAIR (K := K) 10 9 canonicalIOSlots.map).numTraceCols → K[X]),
        (finiteComputeChip canonicalIOSlots qC).Satisfies PC
      ∧ (finiteMemoryChip canonicalIOSlots qM).Satisfies PM
      ∧ IOChip.ChipRows P.optimized.sampled.sampled.records.requests.length
          (remapParams qC canonicalIOSlots.map ComputeChip.ioPubOff) x₀p
      ∧ IOChip.ChipRows P.optimized.sampled.sampled.records.responses.length
          (remapParams qM canonicalIOSlots.map memIoPubOff) x₀m
      ∧ IOChip.ChipAgreement P.optimized.sampled.sampled.records.requests
          (ioCoinsOf c) terminal
          (remapParams qC canonicalIOSlots.map ComputeChip.ioPubOff) x₀p (finProgIoBlock PC)
      ∧ IOChip.ChipAgreement P.optimized.sampled.sampled.records.responses
          (ioCoinsOf c) terminal
          (remapParams qM canonicalIOSlots.map memIoPubOff) x₀m (finMemIoBlock PM) := by
  have hcoins : ioCoinsOf c = P.optimized.sampled.sampled.coins :=
    ioCoinsOf_eq_sampled P Qc Qm c hacc
  obtain ⟨terminal, qC, qM, x₀p, x₀m, PC, PM, hC, hM, hrowsP, hrowsM, hagP, hagM, -, -⟩ :=
    giga_bundle_of_io_lio (Ksz := P.optimized.family.problem.cfg.Ksz) D
      P.optimized.sampled.sampled.records P.optimized.sampled.sampled.coins
      P.optimized.sampled.sampled.lio (sampled_compress_ne_zero P) hcap
  exact ⟨terminal, qC, qM, x₀p, x₀m, PC, PM, hC, hM, hrowsP, hrowsM,
    by rw [hcoins]; exact hagP, by rw [hcoins]; exact hagM⟩

/-- **`io_lio_of_giga_satisfies_at_production_coins` is not vacuous.**  Its own conclusion,
re-derived by feeding it the bundle built above.  As a proposition this is
`P.optimized.sampled.sampled.lio` again — the content is entirely type-level, exactly as with
`IOChipCompleteness.lio_roundtrip` (`IOChipCompleteness.lean:614`): it compiles only if the seven
objects `giga_bundle_at_production_coins` produces are accepted verbatim as the assembled-chip
hypotheses of the headline. -/
theorem giga_composition_roundtrip
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (D : OrbitDomain K)
    (hcap : P.optimized.sampled.sampled.records.requests.length + 1 ≤ 2 ^ D.h) :
    IO.LIO P.optimized.family.problem.cfg.Ksz
      P.optimized.sampled.sampled.records.requests
      P.optimized.sampled.sampled.records.responses := by
  obtain ⟨terminal, qC, qM, x₀p, x₀m, PC, PM, hC, hM, hrowsP, hrowsM, hagP, hagM⟩ :=
    giga_bundle_at_production_coins P Qc Qm c hacc D hcap
  exact GigaIOSlots.io_lio_of_giga_satisfies_at_production_coins P Qc Qm c hacc hgood
    terminal qC qM x₀p x₀m PC PM hC hM hrowsP hrowsM hagP hagM

end Composition


/-! ## 11. Why the *honest* compute block cannot simply be substituted here

The witness above is a fixed point of the row gates, not an execution.  The tree does contain an
honest satisfying trace for the compute-table block — `SampledIOSameExecution.lean:103`'s
`ComputeSampledObligations`, a field of the package through `P.optimized.computeObligations`,
whose first conjunct is `∀ kind, (R.computeTableRAP kind).Satisfies A.exact.computeTableTrace`
with `computeTableRAP := (exactCanonicalProgParams R.problem).rap Trans.computeAIRchained kind`
(`PlusIOSegmentedRAP.lean:423`) — and an honest walk certificate
(`PlusIOTraceEncoding.lean:1349`, `computeWalkCertificate_exists`).

What blocks substituting them into `finiteComputeChip` is not the columns but the **domain**: a
`StagedChip` stores one `params : SegmentedRAPParams K` (`StagedTableRAP.lean:162`), so all three
blocks of one chip are evaluated on one and the same per-kind point set.  `blocks_share_one_domain`
is that fact, stated.  The honest compute table is deployed on `cfg.compRows` rows
(`ExactConfig.compRows`, with `cfg.computeDomain` built from it) and the prog-IO chip on
`|requests| + 1` rows (`IOChipCompleteness.chipParams`), and nothing in the tree forces those two
row counts to agree.  Reconciling them is the work an honest assembled witness needs; it is not
done here. -/

/-- **The reconciliation obligation, isolated.**  `PlusIOSegmentedRAP.computeWalkParams`
(`PlusIOSegmentedRAP.lean:363`) already deploys the walk block on `cfg.computeDomain`, the very
domain `ExactCanonicalRAP.exactCanonicalProgParams` (`ExactCanonicalRAP.lean:97`, through
`SegmentedRAPParams.ofComputeConfig`) gives the compute table — so those two blocks agree already.
The IO chip is the odd one out, and this theorem says the *only* thing that has to be reconciled
is the row count: at `n + 1 = cfg.compRows` the assembled deployment's four domains are literally
`cfg.computeDomain`.  Everything else already lines up — `cfg.eDeg = 1`
(`ExactConfig.eDeg_eq_one`), `ω` and `βcoset` are `cfg.orbit`'s, `hExp` is inert for
`RAP.Satisfies`, the compute table's coins sit at proof slots `0 … 4`, the walk's at `5` and the
IO chip's at `8`, `9`, and the three publics do not collide (`walkPubOff = 0`, `ioPubOff = 2`).

Whether `n + 1 = cfg.compRows` can be *had* is a different question, and the honest answer is that
it should not be assumed: the paper gives OP9 three `mem_axis` reads in one compute
row, so the request list is not in bijection with the compute rows.  The real fix is a padded
prog-IO deployment on `cfg.compRows` rows, which is a change to the IO chip's row geometry
(`IOChipCompleteness.chipParams`), not a new package field. -/
theorem gigaParams_domain_eq_computeDomain {F : Type*} [Field F] [Algebra F K]
    (cfg : ExactConfig F K) (coins : IOCoins K) (terminal : K) (n : ℕ)
    (hn : n + 1 = cfg.compRows) :
    (gigaParams cfg.orbit coins terminal n).domain = cfg.computeDomain := by
  have htr : ∀ (m₁ m₂ : ℕ) (p₁ : 0 < m₁) (p₂ : 0 < m₂), m₁ = m₂ →
      cfg.orbit.transitionDomain m₁ p₁ = cfg.orbit.transitionDomain m₂ p₂ := by
    intro m₁ m₂ p₁ p₂ h; subst h; rfl
  have hte : ∀ (m₁ m₂ : ℕ) (p₁ : 0 < m₁) (p₂ : 0 < m₂), m₁ = m₂ →
      cfg.orbit.terminalDomain m₁ p₁ = cfg.orbit.terminalDomain m₂ p₂ := by
    intro m₁ m₂ p₁ p₂ h; subst h; rfl
  funext k
  cases k with
  | boundary => rfl
  | transition => exact htr _ _ _ _ hn
  | terminal => exact hte _ _ _ _ hn
  | row => exact congrArg cfg.orbit.rowDomain hn

theorem blocks_share_one_domain (S : IOSlots) (q : SegmentedRAPParams K)
    (kind : Reified.ConstraintKind) :
    (q.rap computeAIRchained kind).H
        = ((remapParams q S.map ComputeChip.ioPubOff).rap (finiteIOProgAIR 9) kind).H
      ∧ (q.rap computeAIRchained kind).H
        = ((ComputeChip.shiftParams q ComputeChip.walkChalOff
            ComputeChip.walkPubOff).rap walkAIR kind).H :=
  ⟨rfl, rfl⟩


/-! ## 12. The orbit capacity is the package's own

`giga_bundle_at_production_coins` carries an orbit `D` and the capacity `|requests| + 1 ≤ 2^D.h`.
At the package's own orbit that capacity is not an assumption: it is
`OptimizedFullStrictNockVMROMPackage.progCapacity` transported along the accepted tuple's
`same_problem` field.  So the composition's non-vacuity needs no orbit hypothesis at all. -/

section Capacity

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F]
  {hOrb : ℕ} (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- **The package's own orbit is long enough for the request rows plus the terminal row.** -/
theorem package_progCapacity
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    P.optimized.sampled.sampled.records.requests.length + 1
      ≤ 2 ^ P.optimized.family.problem.cfg.orbit.h := by
  have hz := hacc.same_problem.nprSeed_ne
  have hcapa := P.progCapacity (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda
  have hcfg := hacc.same_problem.specialized_cfg_eq_family
  have hheq := hacc.same_problem.specialized_exec_heq_family
  have hexec : (TemplateRawJointSoundness.specializedProblem P.optimized.verifier.raw.timestamp
      (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).exec.derivedRequestIO
      = P.optimized.family.problem.exec.derivedRequestIO := by
    congr 1
  rw [P.optimized.sampled.requests_eq, ← hexec, ← hcfg]
  exact hcapa

/-- **The composition is non-vacuous with no orbit hypothesis.**  `giga_composition_roundtrip` at
the package's own orbit. -/
theorem giga_composition_roundtrip_at_package_orbit
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm) :
    IO.LIO P.optimized.family.problem.cfg.Ksz
      P.optimized.sampled.sampled.records.requests
      P.optimized.sampled.sampled.records.responses :=
  giga_composition_roundtrip P Qc Qm c hacc hgood P.optimized.family.problem.cfg.orbit
    (package_progCapacity P Qc Qm c hacc)

end Capacity

end Nock.NockVMROM.Thm54.GigaWitness

section Audit

open Nock.NockVMROM.Thm54.GigaWitness

#check @eval_castEnv
#check @computeAIRchained_vanishes
#check @memoryAIRchained_vanishes
#check @walkAIR_vanishes
#check @gigaParams
#check @gigaParams_row_nonempty
#check @gigaComputeTrace
#check @gigaMemoryTrace
#check @finiteComputeChip_satisfies_of_gates
#check @finiteMemoryChip_satisfies_of_gates
#check @gigaComputeTrace_satisfies
#check @gigaMemoryTrace_satisfies
#check @giga_bundle_of_io_lio
#check @giga_bundle_concrete
#check @giga_bundle_at_production_coins
#check @giga_composition_roundtrip
#check @package_progCapacity
#check @giga_composition_roundtrip_at_package_orbit
#check @gigaParams_domain_eq_computeDomain
#check @blocks_share_one_domain

#print axioms Nock.NockVMROM.Thm54.GigaWitness.eval_castEnv
#print axioms Nock.NockVMROM.Thm54.GigaWitness.computeAIRchained_vanishes
#print axioms Nock.NockVMROM.Thm54.GigaWitness.memoryAIRchained_vanishes
#print axioms Nock.NockVMROM.Thm54.GigaWitness.walkAIR_vanishes
#print axioms Nock.NockVMROM.Thm54.GigaWitness.gigaParams_row_nonempty
#print axioms Nock.NockVMROM.Thm54.GigaWitness.finiteComputeChip_satisfies_of_gates
#print axioms Nock.NockVMROM.Thm54.GigaWitness.finiteMemoryChip_satisfies_of_gates
#print axioms Nock.NockVMROM.Thm54.GigaWitness.gigaComputeTrace_satisfies
#print axioms Nock.NockVMROM.Thm54.GigaWitness.gigaMemoryTrace_satisfies
#print axioms Nock.NockVMROM.Thm54.GigaWitness.giga_bundle_of_io_lio
#print axioms Nock.NockVMROM.Thm54.GigaWitness.giga_bundle_concrete
#print axioms Nock.NockVMROM.Thm54.GigaWitness.giga_bundle_at_production_coins
#print axioms Nock.NockVMROM.Thm54.GigaWitness.giga_composition_roundtrip
#print axioms Nock.NockVMROM.Thm54.GigaWitness.package_progCapacity
#print axioms Nock.NockVMROM.Thm54.GigaWitness.giga_composition_roundtrip_at_package_orbit
#print axioms Nock.NockVMROM.Thm54.GigaWitness.gigaParams_domain_eq_computeDomain
#print axioms Nock.NockVMROM.Thm54.GigaWitness.blocks_share_one_domain

end Audit
