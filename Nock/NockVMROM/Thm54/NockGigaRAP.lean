import Nock.NockVMROM.Thm54.ComputeStagedTable

/-!
# The giga-RAP: the compute chip and the memory chip on ONE interaction schedule

`ComputeStagedTable` folded the three compute-side AIRs into one `Staged.StagedChip`.  This module
does the same for the memory side and — the point of the exercise — puts **both** chips on a
single `ChallengeChronology`, so the interaction schedule is a property of the *proof* rather than
of a table.

## Why one schedule, and why it is a typing fact

**A symbol trap worth recording**, because the client's own comments read as a contradiction and
are not one.  `prover.hoon:167` labels the first draw "round one challenges: a, b, c,..., α" and
`:211` the second "round two challenges: β, z" — so the client's `α` is an *ext*-block coin and
its `z` a *mega-ext* one, the reverse of this tree's `nockChronology`, where `z` is usable by
round-1 columns and `α` only by round-2 ones.  The two agree once read by **role** rather than by
letter: the client's round-one draw is the coin set its fingerprint (ext) columns need, which is
this tree's `z, a, b, c`; the client's round-two draw is the coin set its accumulator (mega-ext)
columns need, which is this tree's timestamp base `α`, `α_C`, `β` and `γ`.  The *structure* — two messages, fingerprints before the first, accumulators after the
second — is identical, and it is the structure `nockChronology` encodes.
`Staged.StagedChip` therefore takes `rounds` and `chronology` as **parameters**, and
`Staged.GigaRAP` stores them once; two chips of one proof cannot declare two schedules.

**And there is exactly one chronology object.**  `nockChronology` — eight slots, three column
blocks, two verifier messages — is declared in `ComputeStagedTable.lean` (item 0), because
`ComputeChip.computeChip`'s type mentions it; this module adds the memory chip on the *same*
object.  A per-chip chronology would have been the table-level error one level down: the compute
chip's own six coins are the proof's slots `0…5` and it simply never reads `β` (slot `6`) or `γ`
(slot `7`), which is `ComputeChip.colChalOf_lt_six`, not a second coin space.

## The memory fold

| AIR | `numTraceCols` | constraints | `.row` | `.transition` | `.boundary` | `.terminal` |
|---|---|---|---|---|---|---|
| `Trans.memoryAIRchained` | 36 | 80 | 75 | 1 | 3 | 1 |
| `Trans.walkAIR`          |  6 |  7 |  0 | 3 | 3 | 1 |
| `Trans.ioMemAIR`         |  3 |  3 |  0 | 1 | 1 | 1 |

`memoryCombinedAIR` folds them into one **45**-column, **90**-constraint field-free
`Reified.AIR`: the memory table keeps columns `0…35`, the memory walk moves to `36…41` and the
mem-IO block to `42…44`.  The memory walk is `Trans.walkAIR` again — there is no separate
`memoryWalkAIR`; the two walks differ only in their RAP parameters
(`RawVerifier.memoryWalkParams`, `:204`).

## One correction to the method: the challenge remap is not an offset

`ComputeStagedTable` shifts each block's challenge indices by a *constant*, which works because
the compute blocks may sit at contiguous slots.  The memory blocks cannot: the coins the memory
table reads are **not fresh**.  the paper says in as many words that the mem-IO block's
"Verifier randomness `α, β ∈ 𝕂` [is] **obtained from the computation table's** `w_prog-IO`
array", and `:542` that "we begin by seeding the memory table with the terminal output of the
compute table"; `JointCoins.gamma` is likewise documented as the challenge *shared* by the two
experiments.  So the memory table's `z` must land on the **same global slot** as the compute
table's `z`, and the memory walk's `α` on the same slot as the compute table's timestamp base —
which `RawVerifier.VerifierGates` (`:389`, `:391`) pins as literally the same coins
(`memoryWalkAlpha = alphaM ω`, `computeWalkAlpha = alphaC ω`).

A constant offset cannot do that while leaving compute's slots `0…4` in place, so item 0
generalises `Expr.shiftBlock`'s index map to an arbitrary challenge renaming
(`Expr.remapBlock`), with `Expr.shiftBlock` recovered as the special case.  Inheritance is then
*definitional*: memory reads slot `1`, and slot `1` is compute's `z`.

## The load-bearing schedule fact

`γ` and `z` are sampled **strictly before** the memory chip's accumulator round.  That is not a
convention here: it is `StagedChip.columns_commit_before_sampling`, a field, discharged by
`decide` (`memoryColumns_commit_before_sampling`).  `gamma_at_accumulator_round_breaks_chip` shows
the obligation has teeth — moving `γ`'s sampling to the accumulator round makes it false.
-/

namespace Nock.Reified

/-- The index map of a block placement with an **arbitrary challenge renaming**: trace columns by
`offT`, challenges by `fC`, public values by `offP`.  `blockShift` (`ComputeStagedTable.lean:115`)
is the special case `fC = (· + offC)`. -/
def blockRemap (offT : ℕ) (fC : ℕ → ℕ) (offP : ℕ) : VarKind → ℕ → ℕ := fun k i =>
  match k with
  | .traceCur   => i + offT
  | .traceNext  => i + offT
  | .challenge  => fC i
  | .publicVal  => i + offP

/-- Place an expression's variables into a block of a wider column/public space, renaming its
challenge indices by `fC`. -/
def Expr.remapBlock (offT : ℕ) (fC : ℕ → ℕ) (offP : ℕ) : Expr → Expr :=
  Expr.mapVars (blockRemap offT fC offP)

/-- **`remapBlock` generalises `shiftBlock`**: with a constant challenge offset the two index maps
agree constructor by constructor. -/
theorem blockRemap_eq_blockShift (offT offC offP : ℕ) :
    blockRemap offT (· + offC) offP = blockShift offT offC offP := by
  funext k i; cases k <;> rfl

theorem Expr.remapBlock_eq_shiftBlock (offT offC offP : ℕ) :
    Expr.remapBlock offT (· + offC) offP = Expr.shiftBlock offT offC offP :=
  congrArg Expr.mapVars (blockRemap_eq_blockShift offT offC offP)

/-- Block placement is a rename, so it preserves trace degree. -/
theorem Expr.degree_remapBlock (offT : ℕ) (fC : ℕ → ℕ) (offP : ℕ) (e : Expr) :
    (e.remapBlock offT fC offP).degree = e.degree :=
  Expr.degree_mapVars _ e

end Nock.Reified

namespace Nock.NockVMROM.Thm54.GigaChips

open Nock Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.Reified Nock.Reified.Trans
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.Staging Nock.NockVMROM.Thm54.Staged
open Nock.NockVMROM.Thm54.ComputeChip
open scoped Polynomial

variable {K : Type*} [Field K]

noncomputable section

/-! ## 1. The proof's coin space

`nockChronology` and its eight slots are declared in `ComputeStagedTable.lean` (item 0), because
`ComputeChip.computeChip`'s *type* mentions them and there is exactly one chronology in the
development.  This item keeps only the memory-facing reading of it. -/

/-- The two coins the memory side inherits are sampled at the *later* message, together with the
compute table's `α`; `z` at the earlier one. -/
theorem gamma_beta_sampled_after_round_one :
    nockSampledAfter gammaSlot = 1 ∧ nockSampledAfter betaSlot = 1 ∧
      nockSampledAfter alphaSlot = 1 ∧ nockSampledAfter zSlot = 0 := by decide

/-! ## 2. The combined memory AIR -/

/-- Trace offset of the memory table block. -/
def memTraceOff : ℕ := 0
/-- Trace offset of the memory walk block: `Trans.memoryAIRchained.numTraceCols`. -/
def memWalkTraceOff : ℕ := 36
/-- Trace offset of the mem-IO block: `36 + Trans.walkAIR.numTraceCols`. -/
def memIoTraceOff : ℕ := 42

/-- **The memory table's challenge renaming.**  `memoryEnvFull`'s slots are `0 = z`, `1 = β`,
`2 = γ` (`AIR.lean:1424-1425`); they land on the proof's `1`, `6`, `7`.  `z` goes to the slot the
compute table already reads, which is what "the memory table is seeded with the compute table's
output" means at the level of coins. -/
def memChalMap : ℕ → ℕ
  | 0 => 1
  | 1 => 6
  | 2 => 7
  | 8 => 0
  | _ => 0

/-- The memory walk's single coin is the timestamp base — `memoryWalkAlpha = alphaM ω`
(`RawVerifier.lean:391`), the same coin the compute table reads at slot `0`. -/
def memWalkChalMap : ℕ → ℕ := fun _ => 0

/-- `ioMemAIR.numChallenges = 0`, so this map is vacuous. -/
def memIoChalMap : ℕ → ℕ := fun _ => 0

/-- Public offset of the memory table block (it has `numPublic = 0`). -/
def memPubOff : ℕ := 0
/-- Public offset of the memory walk block: `0 = initial_count`, `1 = seed`. -/
def memWalkPubOff : ℕ := 0
/-- Public offset of the mem-IO block: `2 = responses`, `3 = out_mem`. -/
def memIoPubOff : ℕ := 2

/-- **The combined memory chip's AIR** — one table, three column blocks, still field-free. -/
noncomputable def memoryCombinedAIR : Reified.AIR where
  numTraceCols  := 45
  numChallenges := 8
  numPublic     := 4
  constraints :=
    (memoryAIRchained (K := K)).constraints.map
        (fun c => ⟨c.kind, c.expr.remapBlock memTraceOff memChalMap memPubOff⟩)
      ++ walkAIR.constraints.map
          (fun c => ⟨c.kind, c.expr.remapBlock memWalkTraceOff memWalkChalMap memWalkPubOff⟩)
      ++ ioMemAIR.constraints.map
          (fun c => ⟨c.kind, c.expr.remapBlock memIoTraceOff memIoChalMap memIoPubOff⟩)

@[simp] theorem memoryCombinedAIR_numTraceCols : (memoryCombinedAIR (K := K)).numTraceCols = 45 := rfl
@[simp] theorem memoryCombinedAIR_numChallenges : (memoryCombinedAIR (K := K)).numChallenges = 8 := rfl
@[simp] theorem memoryCombinedAIR_numPublic : (memoryCombinedAIR (K := K)).numPublic = 4 := rfl

/-- Print the exported **assembled memory chip**.  The counterpart of
`ComputeStagedTable.exportComputeCombinedAIR`: `Nock/AIR.lean`'s `exportMemoryAIR` /
`exportMemoryAIRchained` print the memory table alone, so the walk and mem-IO blocks — and with
them seven of this chip's fifteen non-`row` gates — were reachable by no exporter. -/
def exportMemoryCombinedAIR : IO Unit := IO.println (Reified.AIR.toJson (memoryCombinedAIR (K := K)))

/-! ### The census -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
/-- **90 constraints**: `80 + 7 + 3`. -/
theorem memoryCombinedAIR_num_constraints : (memoryCombinedAIR (K := K)).constraints.length = 90 := by rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
/-- **The per-kind census.**  `.row` is the memory table's 75; `.transition` is its LogUp
chaining gate plus the walk's three steps plus the mem-IO step; `.boundary` is its two axis seeds
plus `ipre = 0`, the walk's three initial gates and the mem-IO init; `.terminal` is
`icur = 0`, `out_walk` and `out_mem`. -/
theorem memoryCombinedAIR_kind_census :
    ((memoryCombinedAIR (K := K)).constraints.filter (fun c => c.kind == .row)).length = 75 ∧
      ((memoryCombinedAIR (K := K)).constraints.filter (fun c => c.kind == .transition)).length = 5 ∧
      ((memoryCombinedAIR (K := K)).constraints.filter (fun c => c.kind == .boundary)).length = 7 ∧
      ((memoryCombinedAIR (K := K)).constraints.filter (fun c => c.kind == .terminal)).length = 3 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
/-- The same census through `kindSeg`, the form `SegmentedRAPParams.rap` consumes. -/
theorem memoryCombinedAIR_kindSeg_census :
    (kindSeg (memoryCombinedAIR (K := K)) .row).constraints.length = 75 ∧
      (kindSeg (memoryCombinedAIR (K := K)) .transition).constraints.length = 5 ∧
      (kindSeg (memoryCombinedAIR (K := K)) .boundary).constraints.length = 7 ∧
      (kindSeg (memoryCombinedAIR (K := K)) .terminal).constraints.length = 3 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The census adds up: `75 + 5 + 7 + 3 = 90`. -/
theorem memoryCombinedAIR_census_total :
    (kindSeg (memoryCombinedAIR (K := K)) .row).constraints.length
        + (kindSeg (memoryCombinedAIR (K := K)) .transition).constraints.length
        + (kindSeg (memoryCombinedAIR (K := K)) .boundary).constraints.length
        + (kindSeg (memoryCombinedAIR (K := K)) .terminal).constraints.length
      = (memoryCombinedAIR (K := K)).constraints.length := by
  have hl := memoryCombinedAIR_num_constraints (K := K)
  obtain ⟨hr, ht, hb, hterm⟩ := memoryCombinedAIR_kindSeg_census (K := K)
  rw [hr, ht, hb, hterm, hl]

private def degFold (l : List Reified.Constraint) : ℕ :=
  l.foldr (fun c acc => max c.expr.degree acc) 0

private theorem degFold_append (a b : List Reified.Constraint) :
    degFold (a ++ b) = max (degFold a) (degFold b) := by
  induction a with
  | nil => simp [degFold]
  | cons c t ih =>
    simp only [degFold, List.cons_append, List.foldr_cons] at *
    rw [ih, ← max_assoc]

private theorem degFold_map_remap (offT : ℕ) (fC : ℕ → ℕ) (offP : ℕ)
    (l : List Reified.Constraint) :
    degFold (l.map (fun c => ⟨c.kind, c.expr.remapBlock offT fC offP⟩)) = degFold l := by
  induction l with
  | nil => rfl
  | cons c t ih =>
    simp only [List.map_cons, degFold, List.foldr_cons] at *
    rw [ih, Expr.degree_remapBlock]

private theorem maxDegree_eq_degFold (air : Reified.AIR) : air.maxDegree = degFold air.constraints := rfl

/-- Folding does not raise the constraint degree: block placement is a rename
(`Expr.degree_remapBlock`) and the walk / mem-IO gates are degree `≤ 2`, so the maximum stays
`memoryAIRchained`'s `4`. -/
theorem memoryCombinedAIR_maxDegree : (memoryCombinedAIR (K := K)).maxDegree = 4 := by
  have hchain : degFold (memoryAIRchained (K := K)).constraints = 4 := by
    simp only [memoryAIRchained]
    rw [degFold_append, degFold_append, degFold_append]
    have hmem : degFold (memoryAIR (K := K)).constraints = 4 := by
      have h := mem_slice_maxDegree (K := K)
      unfold AIR.maxDegree at h
      simpa [degFold] using h
    have hicur : degFold [⟨.transition, icurChainExpr⟩] = 1 := by
      simp only [degFold, List.foldr_cons, List.foldr_nil, icurChainExpr]
      unfold Expr.degree Reified.tc tn
      rfl
    have hseed : degFold
        (memSeedBoundaryExprs.map (fun e => (⟨.boundary, e⟩ : Reified.Constraint))) = 1 := by
      simp only [memSeedBoundaryExprs, memSeedCountsExpr, memSeedIndicatorExpr,
        degFold, List.map, List.foldr]
      unfold Expr.degree Reified.tc
      rfl
    have hend : degFold [⟨.boundary, memIpreInitExpr⟩, ⟨.terminal, memIcurTermExpr⟩] = 1 := by
      simp only [degFold, List.foldr, memIpreInitExpr, memIcurTermExpr]
      unfold Expr.degree Reified.tc
      rfl
    rw [hmem, hicur, hseed, hend]
    norm_num
  rw [maxDegree_eq_degFold]
  simp only [memoryCombinedAIR]
  rw [degFold_append, degFold_append, degFold_map_remap, degFold_map_remap, degFold_map_remap,
    hchain]
  have hwalk : degFold walkAIR.constraints ≤ 4 := by
    have : walkAIR.maxDegree ≤ 4 := by
      unfold walkAIR AIR.maxDegree
      decide
    simpa [maxDegree_eq_degFold, degFold] using this
  have hio : degFold ioMemAIR.constraints ≤ 4 := by
    have : ioMemAIR.maxDegree ≤ 4 := by
      unfold ioMemAIR AIR.maxDegree
      decide
    simpa [maxDegree_eq_degFold, degFold] using this
  omega

/-! ### The variable-range facts

`walkAIR_varsBelow` (`ComputeStagedTable.lean`) is reused — the memory walk *is* `Trans.walkAIR`. -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
/-- Every `memoryAIRchained` constraint reads only columns `< 36`, challenges `< 9`, no publics. -/
theorem memoryAIRchained_varsBelow :
    (memoryAIRchained (K := K)).constraints.all (fun c => c.expr.varsBelow 36 9 0) = true := by rfl

/-- Every `ioMemAIR` constraint reads only columns `< 3`, no challenges, publics `< 2`. -/
theorem ioMemAIR_varsBelow :
    ioMemAIR.constraints.all (fun c => c.expr.varsBelow 3 0 2) = true := by rfl

/-! ## 3. The memory round schedule: the client's three column blocks

The client's `%memory` table has the same three blocks as `%compute`: `basic-column-names` (`:12`),
`ext-column-names` (`:29`) and `mega-ext-column-names` (`:42`).  The assignment below is made by
one criterion — **which coins the honest column value reads** — and then checked against those
three lists.

* **Round 0** (base, 9 columns) — the columns that read **no** coin: the four state one-hots
  `op` (`0…3`, `AIR.lean:1406`), the four left-child-state one-hots (`19…22`, `:1414-1417`) and
  the record axis `mem.axis` (`29`, `:1420`).  Client: `%pad`, `%op-l`/`%op-r`, `%axis-flag` and
  `%axis` in `basic-column-names` (`memory.hoon:14-19`).
* **Round 1** (ext, 19 columns) — the columns that read the NPR seed `z` and nothing later: the
  parent / left-child / right-child noun fingerprints (`4…6`, `9…11`, `14…16`), the memory
  record's root and child fingerprints (`23…28`), the `z⁻¹` witness (`34`), the walk's node
  fingerprint `cur` (`38`) and the mem-IO row fraction and multiplicity (`42`, `43`).  Client:
  `%parent-size`/`%parent-dyck`/`%parent-leaf`, `%lc-*`, `%rc-*` and `%inv`
  (`memory.hoon:31-40`) — a column-for-column match.
* **Round 2** (mega-ext, 16 columns) — the columns whose honest value reads a coin of the *later*
  message: the record timestamp `mem.ts` (`30`), the six axis accumulators
  `pt/lc/rc.indicator` and `.counts` (`7, 8, 12, 13, 17, 18`), the LogUp `ipre`/`icur`/`g`
  (`31…33`), the walk's `ln`/`count`/`acc`/`cc`/`cm` (`36…38`, `40`, `41`) and the mem-IO
  accumulator (`42`). The form R `C'` column (`35`) is coin-free, like `mem.axis`.  Client: `%ln`, `%nc`, `%kvs`, `%kvs-ioz`, `%kvsf`, `%decode-mset`,
  `%op0-mset`, `%data-k` (`memory.hoon:44-51`).

**One deliberate divergence from the client's naming, and it is forced.**  The client carries
`%axis-flag`, `%count`, `%count-inv`, `%dmult`, `%mult`, `%mult-lc`, `%mult-rc` in
`basic-column-names`, i.e. as base-field scalars.  This tree's `indicator`/`counts` are *not*
those: `MemoryTable.SV` makes them axis **accumulators over timestamps** —
`pt.indicator = lc.indicator ± mem.ts` and `pt.counts = lc.counts + mem.axis · mem.ts`
(`MemoryTable.lean:216-223`) — so their honest value is a function of the timestamp base and they
belong to the mega-ext block.  The classification is read off the constraints, not chosen. -/

/-- The ten coin-free columns of the combined memory chip (form R `C'` at 35). -/
def memBaseCols : List ℕ := [0, 1, 2, 3, 19, 20, 21, 22, 29, 35]

/-- The sixteen later-message columns of the combined memory chip. -/
def memMegaExtCols : List ℕ := [7, 8, 12, 13, 17, 18, 30, 31, 32, 33, 36, 37, 38, 40, 41, 42]

/-- The three-block round assignment of the memory chip. -/
def memRoundOf (c : Fin 45) : Fin 3 :=
  if (c : ℕ) ∈ memBaseCols then 0 else if (c : ℕ) ∈ memMegaExtCols then 2 else 1

/-- **The memory schedule.**  `width_eq` is a field of `RoundSchedule`, so the declared widths
`10 / 19 / 16` are the *actual* column-fibre cardinalities, checked by `decide`. -/
def memorySchedule : RoundSchedule 45 3 where
  roundOf := memRoundOf
  width := ![10, 19, 16]
  width_eq := by decide

theorem memorySchedule_width : memorySchedule.width = ![10, 19, 16] := rfl

/-- `w = Σ_r w_RAP(r)`: `10 + 19 + 16 = 45`. -/
theorem memorySchedule_total : (45 : ℕ) = ∑ r, memorySchedule.width r :=
  memorySchedule.total_width

theorem memBaseCols_nodup : memBaseCols.Nodup := by decide
theorem memMegaExtCols_nodup : memMegaExtCols.Nodup := by decide
theorem memBaseCols_length : memBaseCols.length = 10 := rfl
theorem memMegaExtCols_length : memMegaExtCols.length = 16 := rfl

/-! ### Each block membership as a `decide`d theorem

A wrong assignment breaks a theorem rather than hiding in prose. -/

/-- The four memory-state one-hots and the four left-child-state one-hots are round-0. -/
theorem mem_selector_columns_round_zero :
    memRoundOf 0 = 0 ∧ memRoundOf 1 = 0 ∧ memRoundOf 2 = 0 ∧ memRoundOf 3 = 0 ∧
      memRoundOf 19 = 0 ∧ memRoundOf 20 = 0 ∧ memRoundOf 21 = 0 ∧ memRoundOf 22 = 0 := by
  decide

/-- `mem.axis` (column 29) is round-0: the record axis is data, not a function of any coin.
Client: `%axis` in `basic-column-names` (`memory.hoon:15`). -/
theorem mem_axis_column_round_zero : memRoundOf 29 = 0 := by decide

/-- The nine noun-fingerprint columns of the parent and the two children are round-1 — they read
the NPR seed `z` and nothing later.  Client: `%parent-*`, `%lc-*`, `%rc-*`. -/
theorem mem_fingerprint_columns_round_one :
    memRoundOf 4 = 1 ∧ memRoundOf 5 = 1 ∧ memRoundOf 6 = 1 ∧
      memRoundOf 9 = 1 ∧ memRoundOf 10 = 1 ∧ memRoundOf 11 = 1 ∧
      memRoundOf 14 = 1 ∧ memRoundOf 15 = 1 ∧ memRoundOf 16 = 1 := by decide

/-- The memory record's root and child fingerprints (columns `23…28`) are round-1. -/
theorem mem_record_fingerprint_columns_round_one :
    memRoundOf 23 = 1 ∧ memRoundOf 24 = 1 ∧ memRoundOf 25 = 1 ∧
      memRoundOf 26 = 1 ∧ memRoundOf 27 = 1 ∧ memRoundOf 28 = 1 := by decide

/-- The `z⁻¹` witness (column 34) is a round-1 ext column, exactly as the compute chip's column
93 is (`ComputeChip.zinv_column_round_one`).  Client: `%inv` (`memory.hoon:40`). -/
theorem mem_zinv_column_round_one : memRoundOf 34 = 1 := by decide

/-- Form R `C'` (column 35) is round-0: `Pub.cprime` is constantly `1`, no coin. -/
theorem mem_cprime_column_round_zero : memRoundOf 35 = 0 := by decide

/-- The six axis accumulators are round-2: they accumulate `mem.ts`
(`MemoryTable.lean:216-223`), hence read the timestamp base. -/
theorem mem_axis_accumulator_columns_round_two :
    memRoundOf 7 = 2 ∧ memRoundOf 8 = 2 ∧ memRoundOf 12 = 2 ∧ memRoundOf 13 = 2 ∧
      memRoundOf 17 = 2 ∧ memRoundOf 18 = 2 := by decide

/-- The record timestamp `mem.ts` (column 30) is round-2: `ts ∈ 𝒯 := β^k` in `Def:NMR`, this tree's `α^k`.  Client: `%data-k` (`memory.hoon:51`). -/
theorem mem_ts_column_round_two : memRoundOf 30 = 2 := by decide

/-- The LogUp columns `ipre`, `icur` and the free inverse witness `g` (`31…33`) are round-2:
`recRLCExpr` is the `γ`-RLC of the record and `poleExpr = recRLCExpr − β`
(`AIR.lean:1507`, `:1514`).  Client: `%kvs`, `%kvs-ioz`, `%decode-mset`, `%op0-mset`. -/
theorem mem_logup_columns_round_two :
    memRoundOf 31 = 2 ∧ memRoundOf 32 = 2 ∧ memRoundOf 33 = 2 := by decide

/-- The memory walk's accumulators (`36…38`) and its two `α`-RLC columns (`40`, `41`) are round-2;
its node fingerprint `cur` (`39`) is round-1, since it is seeded by `z` and not by `α`.  Exactly
the compute chip's `walk_columns_rounds` pattern at columns `94…99`. -/
theorem mem_walk_columns_rounds :
    memRoundOf 36 = 2 ∧ memRoundOf 37 = 2 ∧ memRoundOf 38 = 2 ∧
      memRoundOf 39 = 1 ∧ memRoundOf 40 = 2 ∧ memRoundOf 41 = 2 := by decide

/-- `acc_mem` (column 42) is round-2; the mem-IO row fraction (43) and multiplicity (44) are
round-1, since `SetEq.RLC` of a response record reads no verifier coin.  The compute chip's
`io_columns_rounds` at `100`/`101` is the same split. -/
theorem mem_io_columns_rounds :
    memRoundOf 42 = 2 ∧ memRoundOf 43 = 1 ∧ memRoundOf 44 = 1 := by decide

/-! ## 4. The memory chip's column challenges, and the `γ`/`z` obligation -/

/-- The coins a memory column of round `r` may read: none at round `0`, the NPR seed at round `1`,
and the timestamp base, the seed, `β` and `γ` at round `2`. -/
def memColChalOf (r : Fin 3) : Finset (Fin 8) :=
  match r with
  | 0 => ∅
  | 1 => {1}
  | 2 => {0, 1, 6, 7}

/-- **Which sampled coins each memory column's committed value may read.** -/
def memoryColumnChallenges (c : Fin 45) : Finset (Fin 8) := memColChalOf (memRoundOf c)

/-- No coin is readable by a memory selector or axis column. -/
theorem mem_base_columns_challenge_free (c : Fin 45) (hc : (c : ℕ) ∈ memBaseCols) :
    memoryColumnChallenges c = ∅ := by
  simp [memoryColumnChallenges, memRoundOf, hc, memColChalOf]

/-- **Commit before sample**, as a statement about the round: a round-`r` memory column may read
only coins sampled strictly before round `r`. -/
theorem memColChalOf_usable : ∀ r : Fin 3, ∀ j : Fin 8, j ∈ memColChalOf r →
    (nockSampledAfter j : ℕ) < (r : ℕ) := by decide

/-- **Commit before sample** at every one of the 45 memory columns. -/
theorem memoryColumns_commit_before_sampling :
    ∀ c : Fin 45, ∀ j ∈ memoryColumnChallenges c,
      (nockSampledAfter j : ℕ) < (memRoundOf c : ℕ) :=
  fun _ j hj => memColChalOf_usable _ j hj

/-- **The load-bearing fact.**  `γ` and `z` are sampled strictly before the memory chip's
accumulator round — `z` at the earlier message, `γ` at the later one — so the memory
accumulators are committed *against coins the verifier has already sent*, which is the direction
the paper describes.  The accumulator round is `2`. -/
theorem memory_inherits_gamma_and_seed :
    (nockSampledAfter zSlot : ℕ) < 2 ∧ (nockSampledAfter gammaSlot : ℕ) < 2 ∧
      (nockSampledAfter betaSlot : ℕ) < 2 ∧ (nockSampledAfter alphaSlot : ℕ) < 2 := by decide

/-- **The obligation has teeth.**  Move `γ`'s sampling to the accumulator round itself and
commit-before-sample becomes **false** — a round-2 column would be reading a coin sent at round
2.  This is the schedule-level form of `RoundFibredSoundness.cylinder_card_le_needs_dependence`:
what is load-bearing is the *strictness* of `usableByColumnOf`. -/
theorem gamma_at_accumulator_round_breaks_chip :
    ¬ (∀ c : Fin 45, ∀ j ∈ memoryColumnChallenges c,
        ((![1, 0, 0, 0, 0, 1, 1, 2] : Fin 8 → Fin 3) j : ℕ) < (memRoundOf c : ℕ)) := by decide

/-- And `z` cannot be deferred to the later message either: the ext-block fingerprints read it. -/
theorem seed_at_later_message_breaks_chip :
    ¬ (∀ c : Fin 45, ∀ j ∈ memoryColumnChallenges c,
        ((![1, 1, 0, 0, 0, 1, 1, 1] : Fin 8 → Fin 3) j : ℕ) < (memRoundOf c : ℕ)) := by decide

/-! ## 5. The compute chip in the proof's coin space

There is nothing to do here.  `ComputeChip.computeChip` is already a
`StagedChip L 3 nockChronology`: its `columnChallenges` is `ComputeChip.computeColumnChallenges`
into `Fin 8`, its commit-before-sample obligation is
`ComputeChip.computeColumns_commit_before_sampling` against `nockSampledAfter`, and
`ComputeChip.colChalOf_lt_six` records that it reads none of the two slots the memory side needs.
The retired `computeChipG` / `colChalOfG` / `colChalOfG_eq_image` existed only to relate a
six-slot compute chronology to this eight-slot one; with one chronology there is nothing to
relate. -/

/-! ## 6. The two chips, and the giga-RAP -/

variable {L : Type*} [Field L]

/-- **The memory chip**, on the same chronology object as `ComputeChip.computeChip`. -/
noncomputable def memoryChip (q : SegmentedRAPParams L) :
    StagedChip L 3 nockChronology where
  air := (memoryCombinedAIR (K := L))
  params := q
  schedule := memorySchedule
  columnChallenges := memoryColumnChallenges
  columns_commit_before_sampling := memoryColumns_commit_before_sampling

@[simp] theorem memoryChip_air (q : SegmentedRAPParams L) :
    (memoryChip q).air = (memoryCombinedAIR (K := L)) := rfl

@[simp] theorem memoryChip_schedule (q : SegmentedRAPParams L) :
    (memoryChip q).schedule = memorySchedule := rfl

/-- The memory chip's four derived RAPs carry width `45`, `k = 3` and the widths `![10, 19, 16]`. -/
theorem memoryChip_rap (q : SegmentedRAPParams L) (kind : Reified.ConstraintKind) :
    ((memoryChip q).rap kind).w = 45 ∧ ((memoryChip q).rap kind).k = 3 ∧
      ((memoryChip q).rap kind).wRAP = ![10, 19, 16] := ⟨rfl, rfl, rfl⟩

/-- **The giga-RAP of one Nock proof**: two chips, one interaction schedule.

The two chips carry their own `SegmentedRAPParams` — the memory chip's public block is its own
(`initial_count`, `seed`, `responses`, `out_mem`) — but they cannot carry their own *chronology*,
because it is an index of the type.  Sharing the coins themselves is then a condition on the two
parameter records; `chipsShareCoins` states it. -/
noncomputable def nockGigaRAP (qC qM : SegmentedRAPParams L) : GigaRAP L where
  rounds := 3
  rounds_pos := by norm_num
  chronology := nockChronology
  chips := [ComputeChip.computeChip qC, memoryChip qM]

@[simp] theorem nockGigaRAP_rounds (qC qM : SegmentedRAPParams L) :
    (nockGigaRAP qC qM).rounds = 3 := rfl

@[simp] theorem nockGigaRAP_chronology (qC qM : SegmentedRAPParams L) :
    (nockGigaRAP qC qM).chronology = nockChronology := rfl

/-- **Satisfaction of the giga-RAP is satisfaction of both chips.** -/
theorem nockGigaRAP_satisfies_iff (qC qM : SegmentedRAPParams L)
    (P : (T : StagedChip L 3 nockChronology) → Fin T.air.numTraceCols → L[X]) :
    (nockGigaRAP qC qM).Satisfies P
      ↔ (ComputeChip.computeChip qC).Satisfies (P (ComputeChip.computeChip qC))
        ∧ (memoryChip qM).Satisfies (P (memoryChip qM)) := by
  show ChipList.Satisfies [ComputeChip.computeChip qC, memoryChip qM] P ↔ _
  rw [ChipList.satisfies_cons, ChipList.satisfies_cons]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, ChipList.satisfies_nil P⟩⟩

/-- **The coins really are shared.**  The two chips' challenge valuations agree on every slot of
the proof's coin space, which is what `prover.hoon:168`/`:212`/`:213` — one global draw welded
into one list and handed to every table — says.  Stated as a condition rather than baked in,
because `params` is per-chip. -/
def chipsShareCoins (qC qM : SegmentedRAPParams L) : Prop :=
  ∀ j : Fin 8, qM.chalVal j = qC.chalVal j

/-- Under `chipsShareCoins`, the memory table's `z` **is** the compute table's `z` and the memory
walk's `α` **is** the compute table's timestamp base — the two inheritances of the paper
each an equality of field elements rather than a naming convention. -/
theorem memory_reads_compute_coins (qC qM : SegmentedRAPParams L)
    (h : chipsShareCoins qC qM) :
    qM.chalVal (memChalMap 0) = qC.chalVal 1 ∧
      qM.chalVal (memWalkChalMap 0) = qC.chalVal 0 :=
  ⟨h zSlot, h alphaSlot⟩

/-- Sharing one parameter record is the special case. -/
theorem chipsShareCoins_self (q : SegmentedRAPParams L) : chipsShareCoins q q := fun _ => rfl

/-! ## 6b. Folding the memory side loses nothing

The three blocks of a combined memory trace are *projections* of it, so the three separate
per-kind satisfactions come back with **no trace-splitting hypothesis**: the only extra inputs are
the `varsBelow` facts of item 2, proved by kernel reduction on the shipped AIRs.  This is
`ComputeChip.computeChip_fold_loses_nothing` at the memory side, with one extra wrinkle — the
memory table's challenge indices are *remapped*, not shifted, so the recovered challenge valuation
is `cv ∘ memChalMap` rather than `cv (· + off)`. -/

/-- The chip's width, as its own AIR states it. -/
theorem memChipWidth : (memoryCombinedAIR (K := L)).numTraceCols = 45 := rfl

/-- The memory-table block of a combined trace: columns `0…35`. -/
def memBlock (P : Fin (memoryCombinedAIR (K := L)).numTraceCols → L[X]) : Fin 36 → L[X] :=
  fun i => P ⟨i, by have := i.isLt; rw [memChipWidth]; omega⟩

/-- The memory-walk block of a combined trace: columns `36…41`. -/
def memWalkBlock (P : Fin (memoryCombinedAIR (K := L)).numTraceCols → L[X]) : Fin 6 → L[X] :=
  fun i => P ⟨i + 36, by have := i.isLt; rw [memChipWidth]; omega⟩

/-- The mem-IO block of a combined trace: columns `42…44`. -/
def memIoBlock (P : Fin (memoryCombinedAIR (K := L)).numTraceCols → L[X]) : Fin 3 → L[X] :=
  fun i => P ⟨i + 42, by have := i.isLt; rw [memChipWidth]; omega⟩

/-- The parameters a block placed at `(fC, offP)` sees.  Everything else `RAP.Satisfies` reads —
`ω` and the per-kind domain — is shared, which is what "one table" means. -/
def remapParams (q : SegmentedRAPParams L) (fC : ℕ → ℕ) (offP : ℕ) : SegmentedRAPParams L :=
  { q with chalVal := fun i => q.chalVal (fC i), pubVal := fun i => q.pubVal (i + offP) }

@[simp] theorem remapParams_ω (q : SegmentedRAPParams L) (fC : ℕ → ℕ) (offP : ℕ) :
    (remapParams q fC offP).ω = q.ω := rfl

@[simp] theorem remapParams_domain (q : SegmentedRAPParams L) (fC : ℕ → ℕ) (offP : ℕ) :
    (remapParams q fC offP).domain = q.domain := rfl

/-- **Memory-table block.** -/
theorem eval_mem_block (P : Fin (memoryCombinedAIR (K := L)).numTraceCols → L[X]) (ω x : L)
    (cv pv : ℕ → L) (e : Reified.Expr) (he : e.varsBelow 36 9 0 = true) :
    (e.remapBlock memTraceOff memChalMap memPubOff).eval (envOfTrace P ω x cv pv)
      = e.eval (envOfTrace (memBlock P) ω x (fun i => cv (memChalMap i)) pv) := by
  rw [Reified.Expr.remapBlock, Reified.Expr.eval_mapVars]
  refine Reified.Expr.eval_congr_of_varsBelow e he ?_ ?_ (fun i _ => rfl)
    (fun i hi => absurd hi (by omega))
  · intro i hi
    have h45 : i < 45 := by omega
    simp [Reified.Env.remap, Reified.blockRemap, envOfTrace, memBlock, memTraceOff, h45, hi]
  · intro i hi
    have h45 : i < 45 := by omega
    simp [Reified.Env.remap, Reified.blockRemap, envOfTrace, memBlock, memTraceOff, h45, hi]

/-- **Memory-walk block.**  Its single coin is the proof's slot `0`. -/
theorem eval_mem_walk_block (P : Fin (memoryCombinedAIR (K := L)).numTraceCols → L[X]) (ω x : L)
    (cv pv : ℕ → L) (e : Reified.Expr) (he : e.varsBelow 6 1 2 = true) :
    (e.remapBlock memWalkTraceOff memWalkChalMap memWalkPubOff).eval (envOfTrace P ω x cv pv)
      = e.eval (envOfTrace (memWalkBlock P) ω x (fun i => cv (memWalkChalMap i)) pv) := by
  rw [Reified.Expr.remapBlock, Reified.Expr.eval_mapVars]
  refine Reified.Expr.eval_congr_of_varsBelow e he ?_ ?_ (fun i _ => rfl) (fun i _ => rfl)
  · intro i hi
    have h45 : i + 36 < 45 := by omega
    simp [Reified.Env.remap, Reified.blockRemap, envOfTrace, memWalkBlock, memWalkTraceOff,
      memWalkPubOff, h45, hi]
  · intro i hi
    have h45 : i + 36 < 45 := by omega
    simp [Reified.Env.remap, Reified.blockRemap, envOfTrace, memWalkBlock, memWalkTraceOff,
      memWalkPubOff, h45, hi]

/-- **Mem-IO block.**  `ioMemAIR.numChallenges = 0`, so the challenge valuation is a free
parameter here; its two public values are read at combined indices `2` and `3`. -/
theorem eval_mem_io_block (P : Fin (memoryCombinedAIR (K := L)).numTraceCols → L[X]) (ω x : L)
    (cv cv' pv : ℕ → L) (e : Reified.Expr) (he : e.varsBelow 3 0 2 = true) :
    (e.remapBlock memIoTraceOff memIoChalMap memIoPubOff).eval (envOfTrace P ω x cv pv)
      = e.eval (envOfTrace (memIoBlock P) ω x cv' (fun i => pv (i + memIoPubOff))) := by
  rw [Reified.Expr.remapBlock, Reified.Expr.eval_mapVars]
  refine Reified.Expr.eval_congr_of_varsBelow e he ?_ ?_ (fun i hi => absurd hi (by omega))
    (fun i _ => rfl)
  · intro i hi
    interval_cases i <;>
      simp [Reified.Env.remap, Reified.blockRemap, envOfTrace, memIoBlock, memIoTraceOff,
        memIoPubOff]
  · intro i hi
    interval_cases i <;>
      simp [Reified.Env.remap, Reified.blockRemap, envOfTrace, memIoBlock, memIoTraceOff,
        memIoPubOff]

/-! ### The three block memberships -/

theorem memTable_mem_combined {c : Reified.Constraint} (hc : c ∈ (memoryAIRchained (K := L)).constraints) :
    (⟨c.kind, c.expr.remapBlock memTraceOff memChalMap memPubOff⟩ : Reified.Constraint)
      ∈ (memoryCombinedAIR (K := L)).constraints := by
  simp only [memoryCombinedAIR, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl ⟨c, hc, rfl⟩)

theorem memWalk_mem_combined {c : Reified.Constraint} (hc : c ∈ walkAIR.constraints) :
    (⟨c.kind, c.expr.remapBlock memWalkTraceOff memWalkChalMap memWalkPubOff⟩ :
        Reified.Constraint)
      ∈ (memoryCombinedAIR (K := L)).constraints := by
  simp only [memoryCombinedAIR, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨c, hc, rfl⟩)

theorem memIo_mem_combined {c : Reified.Constraint} (hc : c ∈ ioMemAIR.constraints) :
    (⟨c.kind, c.expr.remapBlock memIoTraceOff memIoChalMap memIoPubOff⟩ : Reified.Constraint)
      ∈ (memoryCombinedAIR (K := L)).constraints := by
  simp only [memoryCombinedAIR, List.mem_append, List.mem_map]
  exact Or.inr ⟨c, hc, rfl⟩

/-- **`StagedChip.satisfies_iff_kinded` at the memory chip.** -/
theorem memoryChip_satisfies_iff_kinded (q : SegmentedRAPParams L)
    (P : Fin (memoryCombinedAIR (K := L)).numTraceCols → L[X]) :
    (memoryChip q).Satisfies P
      ↔ ∀ c ∈ (memoryCombinedAIR (K := L)).constraints, ∀ x ∈ q.domain c.kind,
          c.expr.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0 :=
  (memoryChip q).satisfies_iff_kinded P

/-! ### The payoff -/

/-- **Folding loses nothing, memory-table block.** -/
theorem fold_gives_memTable (q qm : SegmentedRAPParams L)
    (hω : qm.ω = q.ω) (hcv : ∀ i, i < 9 → qm.chalVal i = q.chalVal (memChalMap i))
    (hdom : ∀ kind, qm.domain kind = q.domain kind)
    (P : Fin (memoryCombinedAIR (K := L)).numTraceCols → L[X]) (h : (memoryChip q).Satisfies P) :
    ∀ kind, (qm.rap (memoryAIRchained (K := L)) kind).Satisfies (memBlock P) := by
  have hk := (memoryChip_satisfies_iff_kinded q P).mp h
  show ∀ kind, (airToRAP (kindSeg (memoryAIRchained (K := L)) kind) qm.chalVal qm.pubVal qm.eDeg qm.hExp
      qm.ω qm.βcoset (qm.domain kind) qm.βcoset_ne_zero qm.hExp_pos).Satisfies (memBlock P)
  refine (segmented_is_kinded (memoryAIRchained (K := L)) qm.chalVal qm.pubVal qm.eDeg qm.hExp qm.ω
    qm.βcoset qm.βcoset_ne_zero qm.hExp_pos qm.domain (memBlock P)).mpr ?_
  intro c hc x hx
  have hvb : c.expr.varsBelow 36 9 0 = true :=
    (List.all_eq_true.mp memoryAIRchained_varsBelow) c hc
  have hzero : (c.expr.remapBlock memTraceOff memChalMap memPubOff).eval
      (envOfTrace P q.ω x q.chalVal q.pubVal) = 0 :=
    hk ⟨c.kind, c.expr.remapBlock memTraceOff memChalMap memPubOff⟩
      (memTable_mem_combined hc) x (by rw [hdom] at hx; exact hx)
  rw [eval_mem_block P q.ω x q.chalVal q.pubVal c.expr hvb] at hzero
  refine Eq.trans ?_ hzero
  exact Reified.Expr.eval_congr_of_varsBelow c.expr hvb
    (fun _ _ => rfl) (fun _ _ => by rw [hω]; rfl)
    (fun i hi => hcv i hi) (fun i hi => absurd hi (by omega))

/-- **Folding loses nothing, memory-walk block.**  Its coin `0` is the chip's coin `0` — the
timestamp base, which `RawVerifier.lean:391` proves *is* `memoryWalkAlpha`. -/
theorem fold_gives_memWalk (q qw : SegmentedRAPParams L)
    (hω : qw.ω = q.ω) (hcv : ∀ i, i < 1 → qw.chalVal i = q.chalVal (memWalkChalMap i))
    (hpv : ∀ i, i < 2 → qw.pubVal i = q.pubVal (i + memWalkPubOff))
    (hdom : ∀ kind, qw.domain kind = q.domain kind)
    (P : Fin (memoryCombinedAIR (K := L)).numTraceCols → L[X]) (h : (memoryChip q).Satisfies P) :
    ∀ kind, (qw.rap walkAIR kind).Satisfies (memWalkBlock P) := by
  have hk := (memoryChip_satisfies_iff_kinded q P).mp h
  show ∀ kind, (airToRAP (kindSeg walkAIR kind) qw.chalVal qw.pubVal qw.eDeg qw.hExp
      qw.ω qw.βcoset (qw.domain kind) qw.βcoset_ne_zero qw.hExp_pos).Satisfies (memWalkBlock P)
  refine (segmented_is_kinded walkAIR qw.chalVal qw.pubVal qw.eDeg qw.hExp qw.ω
    qw.βcoset qw.βcoset_ne_zero qw.hExp_pos qw.domain (memWalkBlock P)).mpr ?_
  intro c hc x hx
  have hvb : c.expr.varsBelow 6 1 2 = true :=
    (List.all_eq_true.mp ComputeChip.walkAIR_varsBelow) c hc
  have hzero : (c.expr.remapBlock memWalkTraceOff memWalkChalMap memWalkPubOff).eval
      (envOfTrace P q.ω x q.chalVal q.pubVal) = 0 :=
    hk ⟨c.kind, c.expr.remapBlock memWalkTraceOff memWalkChalMap memWalkPubOff⟩
      (memWalk_mem_combined hc) x (by rw [hdom] at hx; exact hx)
  rw [eval_mem_walk_block P q.ω x q.chalVal q.pubVal c.expr hvb] at hzero
  refine Eq.trans ?_ hzero
  exact Reified.Expr.eval_congr_of_varsBelow c.expr hvb
    (fun _ _ => rfl) (fun _ _ => by rw [hω]; rfl)
    (fun i hi => hcv i hi) (fun i hi => hpv i hi)

/-- **Folding loses nothing, mem-IO block.** -/
theorem fold_gives_memIo (q qi : SegmentedRAPParams L)
    (hω : qi.ω = q.ω) (hpv : ∀ i, i < 2 → qi.pubVal i = q.pubVal (i + memIoPubOff))
    (hdom : ∀ kind, qi.domain kind = q.domain kind)
    (P : Fin (memoryCombinedAIR (K := L)).numTraceCols → L[X]) (h : (memoryChip q).Satisfies P) :
    ∀ kind, (qi.rap ioMemAIR kind).Satisfies (memIoBlock P) := by
  have hk := (memoryChip_satisfies_iff_kinded q P).mp h
  show ∀ kind, (airToRAP (kindSeg ioMemAIR kind) qi.chalVal qi.pubVal qi.eDeg qi.hExp
      qi.ω qi.βcoset (qi.domain kind) qi.βcoset_ne_zero qi.hExp_pos).Satisfies (memIoBlock P)
  refine (segmented_is_kinded ioMemAIR qi.chalVal qi.pubVal qi.eDeg qi.hExp qi.ω
    qi.βcoset qi.βcoset_ne_zero qi.hExp_pos qi.domain (memIoBlock P)).mpr ?_
  intro c hc x hx
  have hvb : c.expr.varsBelow 3 0 2 = true :=
    (List.all_eq_true.mp ioMemAIR_varsBelow) c hc
  have hzero : (c.expr.remapBlock memIoTraceOff memIoChalMap memIoPubOff).eval
      (envOfTrace P q.ω x q.chalVal q.pubVal) = 0 :=
    hk ⟨c.kind, c.expr.remapBlock memIoTraceOff memIoChalMap memIoPubOff⟩
      (memIo_mem_combined hc) x (by rw [hdom] at hx; exact hx)
  rw [eval_mem_io_block P q.ω x q.chalVal qi.chalVal q.pubVal c.expr hvb] at hzero
  refine Eq.trans ?_ hzero
  exact Reified.Expr.eval_congr_of_varsBelow c.expr hvb
    (fun _ _ => rfl) (fun _ _ => by rw [hω]; rfl)
    (fun i hi => absurd hi (by omega)) (fun i hi => hpv i hi)

/-- **The headline: folding the three memory-side AIRs into one staged chip loses nothing.**

Satisfying the single 45-column, 90-constraint memory chip yields the three separate per-kind
`RAP.Satisfies` obligations — one per AIR — that `RawVerifier.SixRAPSatisfy` (`:408`) consumes on
the memory side, at the chip's own parameters with the blocks' valuations remapped. -/
theorem memoryChip_fold_loses_nothing (q : SegmentedRAPParams L)
    (P : Fin (memoryCombinedAIR (K := L)).numTraceCols → L[X]) (h : (memoryChip q).Satisfies P) :
    (∀ kind, ((remapParams q memChalMap memPubOff).rap (memoryAIRchained (K := L)) kind).Satisfies
        (memBlock P))
      ∧ (∀ kind, ((remapParams q memWalkChalMap memWalkPubOff).rap walkAIR kind).Satisfies
          (memWalkBlock P))
      ∧ (∀ kind, ((remapParams q memIoChalMap memIoPubOff).rap ioMemAIR kind).Satisfies
          (memIoBlock P)) :=
  ⟨fold_gives_memTable q (remapParams q memChalMap memPubOff) rfl (fun _ _ => rfl)
     (fun _ => rfl) P h,
   fold_gives_memWalk q (remapParams q memWalkChalMap memWalkPubOff) rfl (fun _ _ => rfl)
     (fun _ _ => rfl) (fun _ => rfl) P h,
   fold_gives_memIo q (remapParams q memIoChalMap memIoPubOff) rfl (fun _ _ => rfl)
     (fun _ => rfl) P h⟩

/-! ### The converse: the memory fold is complete, not merely sound -/

/-- Lay three block traces side by side into one combined memory trace. -/
def concatMemBlocks (Pm : Fin 36 → L[X]) (Pw : Fin 6 → L[X]) (Pi : Fin 3 → L[X]) :
    Fin (memoryCombinedAIR (K := L)).numTraceCols → L[X] := fun i =>
  if h : (i : ℕ) < 36 then Pm ⟨i, h⟩
  else if h2 : (i : ℕ) < 42 then Pw ⟨(i : ℕ) - 36, by omega⟩
  else Pi ⟨(i : ℕ) - 42, by have := lt_of_lt_of_eq i.isLt memChipWidth; omega⟩

@[simp] theorem memBlock_concat (Pm : Fin 36 → L[X]) (Pw : Fin 6 → L[X]) (Pi : Fin 3 → L[X]) :
    memBlock (concatMemBlocks Pm Pw Pi) = Pm := by
  funext i; simp [memBlock, concatMemBlocks, i.isLt]

@[simp] theorem memWalkBlock_concat (Pm : Fin 36 → L[X]) (Pw : Fin 6 → L[X])
    (Pi : Fin 3 → L[X]) : memWalkBlock (concatMemBlocks Pm Pw Pi) = Pw := by
  funext i
  have hi := i.isLt
  simp only [memWalkBlock, concatMemBlocks]
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 1

@[simp] theorem memIoBlock_concat (Pm : Fin 36 → L[X]) (Pw : Fin 6 → L[X])
    (Pi : Fin 3 → L[X]) : memIoBlock (concatMemBlocks Pm Pw Pi) = Pi := by
  funext i
  have hi := i.isLt
  simp only [memIoBlock, concatMemBlocks]
  rw [dif_neg (by omega), dif_neg (by omega)]
  congr 1

/-- **The memory fold is complete.**  Three block traces satisfying the three separate per-kind
RAPs concatenate to a trace satisfying the single staged memory chip. -/
theorem memoryChip_satisfies_concat (q : SegmentedRAPParams L)
    (Pm : Fin 36 → L[X]) (Pw : Fin 6 → L[X]) (Pi : Fin 3 → L[X])
    (hm : ∀ kind, ((remapParams q memChalMap memPubOff).rap (memoryAIRchained (K := L)) kind).Satisfies Pm)
    (hw : ∀ kind, ((remapParams q memWalkChalMap memWalkPubOff).rap walkAIR kind).Satisfies Pw)
    (hi : ∀ kind, ((remapParams q memIoChalMap memIoPubOff).rap ioMemAIR kind).Satisfies Pi) :
    (memoryChip q).Satisfies (concatMemBlocks Pm Pw Pi) := by
  have hm' := (segmented_is_kinded (memoryAIRchained (K := L))
    (remapParams q memChalMap memPubOff).chalVal (remapParams q memChalMap memPubOff).pubVal
    q.eDeg q.hExp q.ω q.βcoset q.βcoset_ne_zero q.hExp_pos q.domain Pm).mp hm
  have hw' := (segmented_is_kinded walkAIR
    (remapParams q memWalkChalMap memWalkPubOff).chalVal
    (remapParams q memWalkChalMap memWalkPubOff).pubVal
    q.eDeg q.hExp q.ω q.βcoset q.βcoset_ne_zero q.hExp_pos q.domain Pw).mp hw
  have hi' := (segmented_is_kinded ioMemAIR
    (remapParams q memIoChalMap memIoPubOff).chalVal
    (remapParams q memIoChalMap memIoPubOff).pubVal
    q.eDeg q.hExp q.ω q.βcoset q.βcoset_ne_zero q.hExp_pos q.domain Pi).mp hi
  refine (memoryChip_satisfies_iff_kinded q (concatMemBlocks Pm Pw Pi)).mpr ?_
  intro c hc0 x hx
  simp only [memoryCombinedAIR, List.mem_append, List.mem_map] at hc0
  rcases hc0 with (⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩) | ⟨d, hd, rfl⟩
  · have hvb : d.expr.varsBelow 36 9 0 = true :=
      (List.all_eq_true.mp memoryAIRchained_varsBelow) d hd
    show (d.expr.remapBlock memTraceOff memChalMap memPubOff).eval
      (envOfTrace (concatMemBlocks Pm Pw Pi) q.ω x q.chalVal q.pubVal) = 0
    rw [eval_mem_block (concatMemBlocks Pm Pw Pi) q.ω x q.chalVal q.pubVal d.expr hvb,
      memBlock_concat]
    exact hm' d hd x hx
  · have hvb : d.expr.varsBelow 6 1 2 = true :=
      (List.all_eq_true.mp ComputeChip.walkAIR_varsBelow) d hd
    show (d.expr.remapBlock memWalkTraceOff memWalkChalMap memWalkPubOff).eval
      (envOfTrace (concatMemBlocks Pm Pw Pi) q.ω x q.chalVal q.pubVal) = 0
    rw [eval_mem_walk_block (concatMemBlocks Pm Pw Pi) q.ω x q.chalVal q.pubVal d.expr hvb,
      memWalkBlock_concat]
    exact hw' d hd x hx
  · have hvb : d.expr.varsBelow 3 0 2 = true :=
      (List.all_eq_true.mp ioMemAIR_varsBelow) d hd
    show (d.expr.remapBlock memIoTraceOff memIoChalMap memIoPubOff).eval
      (envOfTrace (concatMemBlocks Pm Pw Pi) q.ω x q.chalVal q.pubVal) = 0
    rw [eval_mem_io_block (concatMemBlocks Pm Pw Pi) q.ω x q.chalVal
      (remapParams q memIoChalMap memIoPubOff).chalVal q.pubVal d.expr hvb, memIoBlock_concat]
    exact hi' d hd x hx

/-- **Two-sided.**  The staged memory chip and the three-AIR conjunction accept the same traces,
up to the concatenation/projection pair. -/
theorem memoryChip_satisfies_iff_blocks (q : SegmentedRAPParams L)
    (Pm : Fin 36 → L[X]) (Pw : Fin 6 → L[X]) (Pi : Fin 3 → L[X]) :
    (memoryChip q).Satisfies (concatMemBlocks Pm Pw Pi)
      ↔ ((∀ kind, ((remapParams q memChalMap memPubOff).rap (memoryAIRchained (K := L)) kind).Satisfies Pm)
          ∧ (∀ kind,
              ((remapParams q memWalkChalMap memWalkPubOff).rap walkAIR kind).Satisfies Pw)
          ∧ (∀ kind,
              ((remapParams q memIoChalMap memIoPubOff).rap ioMemAIR kind).Satisfies Pi)) := by
  refine ⟨fun h => ?_, fun h => memoryChip_satisfies_concat q Pm Pw Pi h.1 h.2.1 h.2.2⟩
  obtain ⟨h1, h2, h3⟩ := memoryChip_fold_loses_nothing q (concatMemBlocks Pm Pw Pi) h
  rw [memBlock_concat] at h1
  rw [memWalkBlock_concat] at h2
  rw [memIoBlock_concat] at h3
  exact ⟨h1, h2, h3⟩

/-! ## 7. `Thm:NockVMROM`'s per-chip round counts versus the three shared blocks

the paper prices `RAP_NockComp-IO` at "**Two** rounds of interaction, providing **three**
random elements in `𝕂`" and `:1478` prices `RAP_NockMem-IO` at "**One** round of interaction,
providing **a** random element in `𝕂`".  Both chips here sit on a **three-block, two-message**
schedule.  Those are not in tension, and the paper settles it rather than leaving it to reading:

* the paper — `RAP_prog-IO` *Additional* Costs: "One round of interaction, providing two
  random elements in `𝕂`" (the `α, β` of `:509`).  Together with `RAP_prog`'s own round that is
  `1 + 1 = 2` rounds and `1 + 2 = 3` elements, exactly `:1458`.
* the paper — `RAP_mem-IO` *Additional* Costs: "`e + 1` columns", and **no** round of
  interaction at all.  So the memory-IO extension draws nothing; `:1478`'s single round and single
  element are `RAP_mem`'s own.

So a chip's round count in `Thm:NockVMROM` counts the verifier messages **that chip causes**, i.e.
the coins freshly drawn for it; the block schedule is the global commitment order, and a chip may
*consume* coins drawn at messages it did not cause.  That is precisely what `:547` says the memory
side does with `α, β`.  `nockChronology` records both: eight slots (all the coins the proof draws)
with `nockSampledAfter` saying which message delivered each, and each chip declaring, per column,
which of them it reads.

`exact_resources`'s `M.rap.k = 1` versus `C.rap.k = 2` is therefore about the *per-chip* RAP
tuples of `Def:RAP`, and is untouched here: `StagedChip.rap` reports `k = rounds` for both chips
(`memoryChip_rap`, `ComputeChip.computeChip_rap_k`), which is the *schedule's* round count, a different
quantity from the number of messages a chip causes. -/

end

end Nock.NockVMROM.Thm54.GigaChips

section Audit

variable {K : Type*} [Field K]

open Nock.NockVMROM.Thm54.GigaChips

#check @Nock.Reified.Expr.remapBlock
#check @Nock.Reified.Expr.remapBlock_eq_shiftBlock
#check @nockChronology
#check @(memoryCombinedAIR (K := K))
#check @memoryCombinedAIR_num_constraints
#check @memoryCombinedAIR_kind_census
#check @memorySchedule
#check @memoryChip
#check @Nock.NockVMROM.Thm54.ComputeChip.computeChip
#check @nockGigaRAP
#check @nockGigaRAP_satisfies_iff
#check @memory_inherits_gamma_and_seed
#check @gamma_at_accumulator_round_breaks_chip
#check @memoryChip_fold_loses_nothing
#check @memoryChip_satisfies_iff_blocks

#print axioms Nock.Reified.Expr.remapBlock_eq_shiftBlock
#print axioms Nock.Reified.Expr.degree_remapBlock
#print axioms Nock.NockVMROM.Thm54.GigaChips.gamma_beta_sampled_after_round_one
#print axioms Nock.NockVMROM.Thm54.GigaChips.memoryCombinedAIR_num_constraints
#print axioms Nock.NockVMROM.Thm54.GigaChips.memoryCombinedAIR_kind_census
#print axioms Nock.NockVMROM.Thm54.GigaChips.memoryCombinedAIR_kindSeg_census
#print axioms Nock.NockVMROM.Thm54.GigaChips.memoryCombinedAIR_census_total
#print axioms Nock.NockVMROM.Thm54.GigaChips.memoryCombinedAIR_maxDegree
#print axioms Nock.NockVMROM.Thm54.GigaChips.memoryAIRchained_varsBelow
#print axioms Nock.NockVMROM.Thm54.GigaChips.ioMemAIR_varsBelow
#print axioms Nock.NockVMROM.Thm54.GigaChips.memorySchedule_total
#print axioms Nock.NockVMROM.Thm54.GigaChips.mem_selector_columns_round_zero
#print axioms Nock.NockVMROM.Thm54.GigaChips.mem_axis_column_round_zero
#print axioms Nock.NockVMROM.Thm54.GigaChips.mem_fingerprint_columns_round_one
#print axioms Nock.NockVMROM.Thm54.GigaChips.mem_record_fingerprint_columns_round_one
#print axioms Nock.NockVMROM.Thm54.GigaChips.mem_zinv_column_round_one
#print axioms Nock.NockVMROM.Thm54.GigaChips.mem_axis_accumulator_columns_round_two
#print axioms Nock.NockVMROM.Thm54.GigaChips.mem_ts_column_round_two
#print axioms Nock.NockVMROM.Thm54.GigaChips.mem_logup_columns_round_two
#print axioms Nock.NockVMROM.Thm54.GigaChips.mem_walk_columns_rounds
#print axioms Nock.NockVMROM.Thm54.GigaChips.mem_io_columns_rounds
#print axioms Nock.NockVMROM.Thm54.GigaChips.mem_base_columns_challenge_free
#print axioms Nock.NockVMROM.Thm54.GigaChips.memColChalOf_usable
#print axioms Nock.NockVMROM.Thm54.GigaChips.memoryColumns_commit_before_sampling
#print axioms Nock.NockVMROM.Thm54.GigaChips.memory_inherits_gamma_and_seed
#print axioms Nock.NockVMROM.Thm54.GigaChips.gamma_at_accumulator_round_breaks_chip
#print axioms Nock.NockVMROM.Thm54.GigaChips.seed_at_later_message_breaks_chip
#print axioms Nock.NockVMROM.Thm54.GigaChips.memoryChip_rap
#print axioms Nock.NockVMROM.Thm54.GigaChips.nockGigaRAP_satisfies_iff
#print axioms Nock.NockVMROM.Thm54.GigaChips.memory_reads_compute_coins
#print axioms Nock.NockVMROM.Thm54.GigaChips.eval_mem_block
#print axioms Nock.NockVMROM.Thm54.GigaChips.eval_mem_walk_block
#print axioms Nock.NockVMROM.Thm54.GigaChips.eval_mem_io_block
#print axioms Nock.NockVMROM.Thm54.GigaChips.memoryChip_satisfies_iff_kinded
#print axioms Nock.NockVMROM.Thm54.GigaChips.fold_gives_memTable
#print axioms Nock.NockVMROM.Thm54.GigaChips.fold_gives_memWalk
#print axioms Nock.NockVMROM.Thm54.GigaChips.fold_gives_memIo
#print axioms Nock.NockVMROM.Thm54.GigaChips.memoryChip_fold_loses_nothing
#print axioms Nock.NockVMROM.Thm54.GigaChips.memoryChip_satisfies_concat
#print axioms Nock.NockVMROM.Thm54.GigaChips.memoryChip_satisfies_iff_blocks

end Audit
