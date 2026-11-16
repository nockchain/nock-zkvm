import Nock.NockVMROM.Thm54.StagedTableRAP
import Nock.NockVMROM.Thm54.ExprReindex
import Nock.Counts

/-!
# The real compute chip as one `StagedChip`

The deployed client has **one** `%compute` table with three column blocks: `basic-column-names` (`:16`, the
`%pad`/`%op0…%op9` selectors), `ext-column-names` (`:31`), and `mega-ext-column-names` (`:90`:
`%ln`, `%sfcons-inv`, `%opc`, `%stack-kv`, `%decode-mset`, `%op0-mset`).  The walk's `ln` and the
IO accumulator are **columns of that one table's mega-ext block**, not separate RAPs.

This tree instead carries three separate `Reified.AIR`s for the compute side:

| AIR | `numTraceCols` | constraints | `.row` | `.transition` | `.boundary` | `.terminal` |
|---|---|---|---|---|---|---|
| `Trans.computeAIRchained` | 94 | 527 | 526 | 1 | 0 | 0 |
| `Trans.walkAIR`           |  6 |   7 |   0 | 3 | 3 | 1 |
| `Trans.ioProgAIR`         |  2 |   3 |   0 | 1 | 1 | 1 |

`computeCombinedAIR` folds them into one 102-column, 537-constraint `Reified.AIR` — still
**field-free** — by offsetting the walk's trace columns to `94…99` and the IO's to `100…101`;
`computeChip` instantiates `Staged.StagedChip` on it with the client's three-block round schedule.

## What the reindexing is, and why the recorded obstruction does not bite

`OptimizedComputeReindexObstruction.no_mr1Timestamp_exprReindex` proves `Expr.mapVars` *cannot*
recover a source variable that the record-free 13/58 codec **erased**: a renaming keeps a trace
variable a single trace projection (`mapVars_mr1Timestamp_is_projection`), so it can never become a
composite such as `ln_prev * α`.  That obstruction is about *changing what a column means*.  Here
nothing is erased and nothing is recomputed: every source column keeps its value and only its
index moves, which is exactly a rename — the operation `Expr.mapVars` is for.  Concretely
`Expr.eval_mapVars` (`ExprReindex.lean:39`) is used in the direction it holds, and the recovered
sub-environments are *equalities*, not reconstructions.

## Challenges and public values are offset too, and why (a deviation, deliberate)

Trace columns are not the only colliding index space.

**Public values.**  `Trans.computeAIRchained.numPublic = 0`, `Trans.walkAIR.numPublic = 2`
(`0 = initial_count`, `1 = seed`) and `Trans.ioProgAIR.numPublic = 1` (`0 = requests`).  Leaving
public indices alone would force one combined public value to be simultaneously the walk's
`initial_count` and the IO's `requests`, so public indices are offset by the prefix-sum rule: walk
by `0`, IO by `2`, giving `numPublic = 3`.

**Challenges.**  It is tempting to *share* challenge slot `0`, since `walkAIR`'s only challenge is
"α" (`walkLn1 : ln(1) − α`, `walkLnStep : ln(i+1) − α·ln(i)`) and so is `computeEnvFull`'s
`chal 0` (`AIR.lean:515`).  **In this tree they are different coins**, and the tree says so in one
theorem: `TemplateRawJointSoundness.sampledCoordinates` (`:288`) pins
`cfg.challenges.α = alphaM ω` — the compute *table*'s timestamp challenge is `JointCoins`'
memory-walk coordinate `αm` — while `computeWalkAlpha = alphaC ω` is the separate compute-walk
coordinate `αc` (`JointCoins.lean:28`, `:31`).  `RawVerifier.VerifierGates` (`:389`) gates only the
latter.  So the challenge index space is offset as well (walk by `5`, IO by `6`), giving
`computeCombinedAIR.numChallenges = 6`.

This is strictly the more general choice: with six slots a valuation may set slot `5` equal to slot
`0` and recover the shared reading, whereas with five slots the *unshared* reading — the one this
tree actually uses — cannot be expressed at all.  `ioProgAIR.numChallenges = 0`, so its offset is
vacuous and is fixed only for uniformity.

## The chronology is the *proof's*, and there is only one of it

`numChallenges = 6` is the number of slots this **AIR** reads — not the number of coins the proof
draws.  The interaction schedule is a property of the proof (`StagedTableRAP.lean:162` carries
`rounds`/`chronology` as *type indices* of `StagedChip` for exactly that reason), and the proof's
coin space is `nockChronology`'s **eight** slots: the compute chip's six at `0…5` plus the `β` and
`γ` that only the memory table reads.  So `nockChronology` is declared here, ahead of the chip
whose type mentions it, and `ComputeChip` gets **no chronology of its own** — a chip that declared
one would be the same error one level down as a table declaring its own round schedule.  The
compute chip simply never reads slots `6, 7`, which is `colChalOf_lt_six` rather than a second
object.

Nothing about the paper is retyped by this.  `Thm:NockVMROM` prices the compute
chip at "two rounds of interaction, providing **three** random elements in `𝕂`"; six was never
that number, and neither is eight — the AIR's challenge-index range is this tree's bookkeeping,
and the paper's count is the messages the chip *causes* (see `NockGigaRAP.lean`'s item 7).
-/

namespace Nock.Reified

/-- **All variable indices of `e` are below the given per-kind bounds.**  A `Bool` fold so the
concrete AIRs can be checked by `rfl` in the kernel. -/
def Expr.varsBelow (nt nc np : ℕ) : Expr → Bool
  | .Var .traceCur i  => Nat.blt i nt
  | .Var .traceNext i => Nat.blt i nt
  | .Var .challenge i => Nat.blt i nc
  | .Var .publicVal i => Nat.blt i np
  | .Const _          => true
  | .Add a b          => a.varsBelow nt nc np && b.varsBelow nt nc np
  | .Sub a b          => a.varsBelow nt nc np && b.varsBelow nt nc np
  | .Mul a b          => a.varsBelow nt nc np && b.varsBelow nt nc np
  | .Neg a            => a.varsBelow nt nc np
  | .Pow a _          => a.varsBelow nt nc np

/-- **Evaluation only reads the variables the expression mentions.**  Two environments agreeing on
every index below the bounds an expression respects give it the same value.  This is what makes a
sub-AIR's environment (which reads `0` above its own width) interchangeable with the combined
environment (which reads the neighbouring block there) on that sub-AIR's own constraints. -/
theorem Expr.eval_congr_of_varsBelow {L : Type*} [Field L] {nt nc np : ℕ} :
    ∀ (e : Expr), e.varsBelow nt nc np = true → ∀ {env₁ env₂ : Env L},
      (∀ i, i < nt → env₁.trace i = env₂.trace i) →
      (∀ i, i < nt → env₁.traceNext i = env₂.traceNext i) →
      (∀ i, i < nc → env₁.chal i = env₂.chal i) →
      (∀ i, i < np → env₁.pub i = env₂.pub i) →
      e.eval env₁ = e.eval env₂
  | .Var .traceCur i, h, _, _, ht, _, _, _ => ht i (by simpa [Expr.varsBelow] using h)
  | .Var .traceNext i, h, _, _, _, htn, _, _ => htn i (by simpa [Expr.varsBelow] using h)
  | .Var .challenge i, h, _, _, _, _, hc, _ => hc i (by simpa [Expr.varsBelow] using h)
  | .Var .publicVal i, h, _, _, _, _, _, hp => hp i (by simpa [Expr.varsBelow] using h)
  | .Const _, _, _, _, _, _, _, _ => rfl
  | .Add a b, h, _, _, ht, htn, hc, hp => by
      have hab := Bool.and_eq_true_iff.mp h
      simp only [Expr.eval, Expr.eval_congr_of_varsBelow a hab.1 ht htn hc hp,
        Expr.eval_congr_of_varsBelow b hab.2 ht htn hc hp]
  | .Sub a b, h, _, _, ht, htn, hc, hp => by
      have hab := Bool.and_eq_true_iff.mp h
      simp only [Expr.eval, Expr.eval_congr_of_varsBelow a hab.1 ht htn hc hp,
        Expr.eval_congr_of_varsBelow b hab.2 ht htn hc hp]
  | .Mul a b, h, _, _, ht, htn, hc, hp => by
      have hab := Bool.and_eq_true_iff.mp h
      simp only [Expr.eval, Expr.eval_congr_of_varsBelow a hab.1 ht htn hc hp,
        Expr.eval_congr_of_varsBelow b hab.2 ht htn hc hp]
  | .Neg a, h, _, _, ht, htn, hc, hp => by
      simp only [Expr.eval, Expr.eval_congr_of_varsBelow a h ht htn hc hp]
  | .Pow a n, h, _, _, ht, htn, hc, hp => by
      simp only [Expr.eval, Expr.eval_congr_of_varsBelow a h ht htn hc hp]

/-- The index map of a block placement: trace columns by `offT`, challenges by `offC`, public
values by `offP`.  All three index spaces of a `Reified.AIR` collide when AIRs are folded, so all
three are offset. -/
def blockShift (offT offC offP : ℕ) : VarKind → ℕ → ℕ := fun k i =>
  match k with
  | .traceCur   => i + offT
  | .traceNext  => i + offT
  | .challenge  => i + offC
  | .publicVal  => i + offP

/-- Place an expression's variables into a block of a wider column/challenge/public space. -/
def Expr.shiftBlock (offT offC offP : ℕ) : Expr → Expr :=
  Expr.mapVars (blockShift offT offC offP)

/-- With no challenge or public offset, block placement *is* the existing `Expr.shiftTrace`
(`ExprReindex.lean:70`) — the two index maps agree constructor by constructor. -/
theorem Expr.shiftBlock_eq_shiftTrace (off : ℕ) :
    Expr.shiftBlock off 0 0 = Expr.shiftTrace off :=
  congrArg Expr.mapVars (by funext k i; cases k <;> rfl)

theorem Expr.shiftBlock_zero (off : ℕ) (e : Expr) : e.shiftBlock off 0 0 = e.shiftTrace off :=
  congrFun (Expr.shiftBlock_eq_shiftTrace off) e

/-- Block placement is a rename, so it preserves trace degree. -/
theorem Expr.degree_shiftBlock (offT offC offP : ℕ) (e : Expr) :
    (e.shiftBlock offT offC offP).degree = e.degree :=
  Expr.degree_mapVars _ e

end Nock.Reified

namespace Nock.NockVMROM.Thm54.GigaChips

open Nock.NockVMROM.Thm54.Staging

/-! ## 0. The proof's coin space and its chronology

**The eight coins of one proof, and the slot each occupies.**

| slot | coin | read by |
|---|---|---|
| `0` | `α` — the timestamp base, `alphaM ω` | compute table `chal 0`; memory walk `chal 0`; the memory record timestamps |
| `1` | `z` — the NPR fingerprint seed | compute table `chal 1`; memory table `chal 0` |
| `2` | `a` | compute table `chal 2` |
| `3` | `b` | compute table `chal 3` |
| `4` | `c` | compute table `chal 4` |
| `5` | `α_C` — the compute walk's own coin, `alphaC ω` | compute walk `chal 0` |
| `6` | `β` — the LogUp pole offset | memory table `chal 1` |
| `7` | `γ` — the memory-record RLC coin | memory table `chal 2` |

**Eight is the complete coin space of the two chips, not a convenient widening.**  Seven of the
eight are the seven fields of `ChallengeVector` (`Config.lean:37`: `a, b, c, α, z, β, γ`) and the
eighth is `computeWalkAlpha`, which is *not* a `ChallengeVector` field —
`TemplateRawJointSoundness.Strategy.sampledCoordinates` (`:288`) proves
`cfg.challenges.α = alphaM ω` while `computeWalkAlpha = alphaC ω`, so the compute walk's coin is a
ninth field element only in the sense of being a distinct `JointCoins` coordinate.  Read the other
way: the eight cover all four `JointCoins` coordinates — `alphaM` at `0`, `nprSeed` at `1`,
`alphaC` at `5`, `gamma` at `7` — plus the three equality-RLC coefficients `a, b, c` and the pole
offset `β`.  The two chips' AIRs read no other challenge: `computeEnvFull.chal` is `(α, z, a, b, c)`
(`AIR.lean:515`), `walkAIR` has the one coin at each chip's own walk slot, `memoryEnvFull.chal` is
`(z, β, γ)` (`AIR.lean:1424`), and both IO AIRs have `numChallenges = 0`.

This chronology is declared here rather than in `NockGigaRAP` because `ComputeChip.computeChip`'s
*type* mentions it, and there is exactly one of it.  `Lem:equiv_compute` fixes the compute table's
own coin count at `rap_inputs := (α, z, a, b, c) ∈ 𝕂^5`; `α` and `z` are shared
with the memory side by the paper. -/
def nockSampledAfter : Fin 8 → Fin 3 := ![1, 0, 0, 0, 0, 1, 1, 1]

/-- **The proof's chronology**: three column blocks, two verifier messages, eight coins.

`z, a, b, c` are sampled after the selector block (round `0`), because the fingerprint columns of
both chips' ext blocks read `z`.  `α, α_C, β, γ` are sampled after the ext block (round `1`) —
for compute that is the paper's response, for memory it is the same message, since
the paper has the memory side *obtain* `α, β` from the compute table's array rather than draw
them. -/
def nockChronology : ChallengeChronology 3 where
  numChallenges := 8
  sampledAfter := nockSampledAfter

@[simp] theorem nockChronology_numChallenges : nockChronology.numChallenges = 8 := rfl

/-- The timestamp-base slot. -/
def alphaSlot : Fin 8 := ⟨0, by norm_num⟩
/-- The `z` slot. -/
def zSlot : Fin 8 := ⟨1, by norm_num⟩
/-- The compute walk's own coin, `α_C`. -/
def alphaCSlot : Fin 8 := ⟨5, by norm_num⟩
/-- The `β` slot. -/
def betaSlot : Fin 8 := ⟨6, by norm_num⟩
/-- The `γ` slot. -/
def gammaSlot : Fin 8 := ⟨7, by norm_num⟩

/-- `α` (slot `0`) and the compute walk's coin (slot `5`) are coins of the final round of
interaction. -/
theorem alpha_sampled_after_round_one :
    nockSampledAfter alphaSlot = 1 ∧ nockSampledAfter alphaCSlot = 1 := ⟨rfl, rfl⟩

/-- `z, a, b, c` are sampled after the selector block, so the ext columns of both chips may read
them.  Stated over the whole coin space: the round-`0` coins are *exactly* the four slots
`1, 2, 3, 4`. -/
theorem seed_coins_sampled_after_round_zero (j : Fin 8)
    (h0 : (j : ℕ) ≠ 0) (h5 : (j : ℕ) ≠ 5) (h6 : (j : ℕ) ≠ 6) (h7 : (j : ℕ) ≠ 7) :
    nockSampledAfter j = 0 := by
  fin_cases j <;> simp_all [nockSampledAfter]

/-- **Four of the eight coins are withheld to the final round** — the compute table's `α`, the
compute walk's `α_C`, and the memory table's `β` and `γ`.  (This is the compute chip's old
two-of-six fibre count, retyped to the proof's coin space: the two new slots are both
final-round.) -/
theorem nockSampledAfter_fibres :
    (Finset.univ.filter fun j : Fin 8 => nockSampledAfter j = 1).card = 4 ∧
      (Finset.univ.filter fun j : Fin 8 => nockSampledAfter j = 0).card = 4 := by
  refine ⟨rfl, rfl⟩

end Nock.NockVMROM.Thm54.GigaChips

namespace Nock.NockVMROM.Thm54.ComputeChip

open Nock Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.Reified Nock.Reified.Trans
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.Staging Nock.NockVMROM.Thm54.Staged
open Nock.NockVMROM.Thm54.GigaChips
open scoped Polynomial

/-! ## 1. The combined compute AIR -/

/-- Trace offset of the walk block: `Trans.computeAIRchained.numTraceCols`. -/
def walkTraceOff : ℕ := 94
/-- Trace offset of the prog-IO block: `94 + Trans.walkAIR.numTraceCols`. -/
def ioTraceOff : ℕ := 100
/-- Challenge offset of the walk block: `Trans.computeAIRchained.numChallenges = 5`. -/
def walkChalOff : ℕ := 5
/-- Challenge offset of the prog-IO block: `5 + Trans.walkAIR.numChallenges = 6`. -/
def ioChalOff : ℕ := 6
/-- Public offset of the walk block: `Trans.computeAIRchained.numPublic = 0`. -/
def walkPubOff : ℕ := 0
/-- Public offset of the prog-IO block: `0 + Trans.walkAIR.numPublic = 2`. -/
def ioPubOff : ℕ := 2

/-- **The combined compute chip's AIR** — one table, three column blocks, still field-free.
`computeAIRchained` keeps columns `0…93` and its constraints verbatim; `walkAIR` moves to
`94…99`; `ioProgAIR` moves to `100…101`.  Each constraint keeps its `kind`. -/
def computeCombinedAIR : Reified.AIR where
  numTraceCols  := 102
  numChallenges := 6
  numPublic     := 3
  constraints :=
    computeAIRchained.constraints
      ++ walkAIR.constraints.map
          (fun c => ⟨c.kind, c.expr.shiftBlock walkTraceOff walkChalOff walkPubOff⟩)
      ++ ioProgAIR.constraints.map
          (fun c => ⟨c.kind, c.expr.shiftBlock ioTraceOff ioChalOff ioPubOff⟩)

@[simp] theorem computeCombinedAIR_numTraceCols : computeCombinedAIR.numTraceCols = 102 := rfl
@[simp] theorem computeCombinedAIR_numChallenges : computeCombinedAIR.numChallenges = 6 := rfl
@[simp] theorem computeCombinedAIR_numPublic : computeCombinedAIR.numPublic = 3 := rfl

/-- Print the exported **assembled compute chip**.

`Nock/AIR.lean`'s eight `export*AIR` printers cover the *parts* — `computeAIR`,
`computeAIRchained`, `walkAIR`, `ioProgAIR` — and nothing printed the *assembly*.  A backend fed
from `exportComputeAIR` receives 526 `.row` gates and none of the four `.boundary`, five
`.transition` and two `.terminal` gates this chip actually carries (`computeCombinedAIR_kind_census`
below).  This is the same one-line shape as `Reified.exportComputeAIR`; it exists here rather than
in `Nock/AIR.lean` because that file is upstream of `computeCombinedAIR`. -/
def exportComputeCombinedAIR : IO Unit := IO.println (Reified.AIR.toJson computeCombinedAIR)

/-! ### The census -/

set_option maxRecDepth 400000 in
/-- **537 constraints**: `527 + 7 + 3`. -/
theorem computeCombinedAIR_num_constraints : computeCombinedAIR.constraints.length = 537 := by
  rfl

set_option maxRecDepth 400000 in
/-- **The per-kind census.**  `.row` is compute's 526; `.transition` is compute's `ln` hand-off
plus the walk's three steps plus the IO step; `.boundary` is the walk's three initial gates plus
the IO init; `.terminal` is `out_walk` plus the IO terminal. -/
theorem computeCombinedAIR_kind_census :
    (computeCombinedAIR.constraints.filter (fun c => c.kind == .row)).length = 526 ∧
      (computeCombinedAIR.constraints.filter (fun c => c.kind == .transition)).length = 5 ∧
      (computeCombinedAIR.constraints.filter (fun c => c.kind == .boundary)).length = 4 ∧
      (computeCombinedAIR.constraints.filter (fun c => c.kind == .terminal)).length = 2 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 400000 in
/-- The same census through `kindSeg`, the form `SegmentedRAPParams.rap` consumes. -/
theorem computeCombinedAIR_kindSeg_census :
    (kindSeg computeCombinedAIR .row).constraints.length = 526 ∧
      (kindSeg computeCombinedAIR .transition).constraints.length = 5 ∧
      (kindSeg computeCombinedAIR .boundary).constraints.length = 4 ∧
      (kindSeg computeCombinedAIR .terminal).constraints.length = 2 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 400000 in
/-- The census adds up: `526 + 5 + 4 + 2 = 537`. -/
theorem computeCombinedAIR_census_total :
    (kindSeg computeCombinedAIR .row).constraints.length
        + (kindSeg computeCombinedAIR .transition).constraints.length
        + (kindSeg computeCombinedAIR .boundary).constraints.length
        + (kindSeg computeCombinedAIR .terminal).constraints.length
      = computeCombinedAIR.constraints.length := by
  rfl

set_option maxRecDepth 400000 in
/-- Folding does not raise the constraint degree: block placement is a rename
(`Expr.degree_shiftBlock`) and the walk/IO gates are degree `≤ 2`, so the maximum stays
`computeAIRchained`'s `4`. -/
theorem computeCombinedAIR_maxDegree : computeCombinedAIR.maxDegree = 4 := by rfl

set_option maxRecDepth 400000 in
/-- Every compute constraint survives folding **verbatim** — the compute block is at offset `0`
and is not reindexed at all, so it is a literal prefix of the combined list. -/
theorem computeCombinedAIR_compute_prefix :
    computeCombinedAIR.constraints.take 527 = computeAIRchained.constraints := by
  rfl

set_option maxRecDepth 400000 in
/-- The line-nonce hand-off gate is still there. -/
theorem lnChain_mem_combined :
    (⟨.transition, lnChainExpr⟩ : Reified.Constraint) ∈ computeCombinedAIR.constraints := by
  simp only [computeCombinedAIR, List.mem_append]
  exact Or.inl (Or.inl lnChain_mem_computeAIRchained)

/-! ### The variable-range facts that make the fold reversible

These are the *only* extra inputs the fold needs, and they are facts about the shipped AIRs proved
by kernel reduction — **not** carried hypotheses. -/

set_option maxRecDepth 400000 in
/-- Every `computeAIRchained` constraint reads only columns `< 94`, challenges `< 5`, no publics. -/
theorem computeAIRchained_varsBelow :
    computeAIRchained.constraints.all (fun c => c.expr.varsBelow 94 5 0) = true := by rfl

/-- Every `walkAIR` constraint reads only columns `< 6`, challenge `0`, publics `< 2`. -/
theorem walkAIR_varsBelow :
    walkAIR.constraints.all (fun c => c.expr.varsBelow 6 1 2) = true := by rfl

/-- Every `ioProgAIR` constraint reads only columns `< 2`, no challenges, public `0`. -/
theorem ioProgAIR_varsBelow :
    ioProgAIR.constraints.all (fun c => c.expr.varsBelow 2 0 1) = true := by rfl

/-! ## 2. The round schedule: the client's three column blocks -/

/-- **The mega-ext (round-2) columns of the combined chip.**  These are exactly the columns whose
honest value is a function of the timestamp base `α`, i.e. of the coin the verifier sends *after*
the ext block is committed:

* `65`, `66` — `pub.ln_prev`, `pub.ln` (`AIR.lean:501`), the line nonce `ln = ln_prev·α^k`; the client's `%ln` mega-ext column;
* `74`, `82`, `90` — `pub.mr1/mr2/mr3.ts` (`AIR.lean:504,507,510`), the record timestamps
  `ln(i−1)·α^{1,2,3}`;
* `94`, `95`, `96` — the walk's `ln`, `count`, `acc` (`walkRowEnv`, `AIR.lean:2042`): `ln(i) = α^i`, the running `count`, and the walk accumulator;
* `98`, `99` — the walk's `cc = Σ_l α^l·chld'(i,l)` and `cm = α^{fanout(i)}`
  (`walkCC`/`walkCM`, `AIR.lean:2032`/`:2035`) — α-dependent **by definition**;
* `100` — the prog-IO accumulator `acc_prog`, which the paper has the prover build only *after*
  the verifier's response at `:509`.

Everything else is ext (round 1) or a selector (round 0); see `combinedRoundOf`. -/
def megaExtCols : List ℕ := [65, 66, 74, 82, 90, 94, 95, 96, 98, 99, 100]

/-- **The three-block round assignment.**

* **Round 0** — columns `0…10`: the eleven one-hot opcode selectors `op_0…op_9`, `op_cons`
  (`computeEnvFull`, `AIR.lean:478`; the slots themselves at `:481-482`).  They are functions of
  `pub.state` alone and read **no** challenge, which is the client's `basic-column-names` block
  (`compute.hoon:16`) and the paper's
  `x_prog`, "the table of opcode selectors for the compute table".
* **Round 2** — `megaExtCols`: the α-keyed line nonces, record timestamps and accumulators; the
  client's `mega-ext-column-names` (`compute.hoon:90`) and the paper's `acc_prog`.
* **Round 1** — the remaining 80 columns: the noun and decode fingerprint triples (`11…64`), the
  record roots/children/axes (`67…73`, `75…81`, `83…89`), the `cons`/`gen`/`z⁻¹` witnesses
  (`91…93`), the walk's node fingerprint `cur` (`97`) and the prog-IO row fraction (`101`).  These
  read the NPR seed `z` and the compression coins `a, b, c` but not `α`; the client's
  `ext-column-names` (`compute.hoon:31`) and the paper's `T_prog ∪ IO_prog`, committed at -/
def combinedRoundOf (c : Fin 102) : Fin 3 :=
  if (c : ℕ) < 11 then 0 else if (c : ℕ) ∈ megaExtCols then 2 else 1

/-- **The schedule.**  `width_eq` is a field of `RoundSchedule`, so the declared widths
`11 / 80 / 11` are the *actual* column-fibre cardinalities, checked by `decide`. -/
def computeSchedule : RoundSchedule 102 3 where
  roundOf := combinedRoundOf
  width := ![11, 80, 11]
  width_eq := by decide

theorem computeSchedule_width : computeSchedule.width = ![11, 80, 11] := rfl

/-- `w = Σ_r w_RAP(r)`: `11 + 80 + 11 = 102`. -/
theorem computeSchedule_total : (102 : ℕ) = ∑ r, computeSchedule.width r :=
  computeSchedule.total_width

/-! ## 3. The compute chip's coins, inside the proof's chronology

`nockChronology` (item 0) is the only chronology in the development; the compute chip does not
own one.  What is compute-specific is *which* of the proof's eight coins each of its columns may
read, and that is `colChalOf`.

`Lem:equiv_compute` fixes the compute table's own coin count at
`rap_inputs := (α, z, a, b, c) ∈ 𝕂^5`, and `computeEnvFull`'s `chal` slots are
`0 = α`, `1 = z`, `2 = a`, `3 = b`, `4 = c` (`AIR.lean:515`) — the proof's slots `0…4` unchanged,
which is why `computeCombinedAIR` needs no challenge reindexing.  Slot `5` is the walk block's own
challenge, this tree's `alphaC ω`, distinct from the table's `α = alphaM ω`; see the header note.
Slots `6` and `7` are `β` and `γ`, which only the memory table reads — `colChalOf_lt_six` says the
compute chip reads neither.

the paper is the two-message structure: `RAP_prog` builds `(x_prog, T_prog, IO_prog)`
(`:507`), the prover sends `Com(IO_prog)` (`:508`), the **verifier responds with random
`α, β ∈ 𝕂`** (`:509`), and only then does the prover build the accumulator columns `acc_prog`
(`:510`) — the "additional final round of interaction" of `:503`.

So `α` is sampled **after round 1**, and the fingerprint/NPR coins `z, a, b, c`, which the ext
block already needs, **after round 0** (`alpha_sampled_after_round_one`,
`seed_coins_sampled_after_round_zero`).  The walk's own coin (slot `5`) drives the same mega-ext
accumulators (`ln(i) = α^i`, `cc`, `cm`), so it too is a final-round coin.

The paper's `β` at `:509` is the LogUp pole offset, which this tree pins to `0`; it occupies slot `6` because the memory table's AIR reads it
as a variable, not because the compute side samples anything extra. -/

/-- The coins a compute column of round `r` may read: none at round `0` (nothing is sampled yet),
`z, a, b, c` at round `1`, all six of the compute chip's coins at round `2`.  The codomain is the
*proof's* coin space `Fin 8`; the sets are unchanged. -/
def colChalOf (r : Fin 3) : Finset (Fin 8) :=
  match r with
  | 0 => ∅
  | 1 => {1, 2, 3, 4}
  | 2 => {0, 1, 2, 3, 4, 5}

/-- **The compute chip reads none of the coins the memory side adds.**  Sitting in the proof's
eight-slot space does not let a compute column read `β` (slot `6`) or `γ` (slot `7`): every coin
any compute column may read is one of its own six.  This is the surviving content of the retired
`colChalOfG_eq_image` — with one coin space there is no image to compare, but there is still
something to check, namely that widening the space did not widen the chip. -/
theorem colChalOf_lt_six : ∀ r : Fin 3, ∀ j ∈ colChalOf r, (j : ℕ) < 6 := by decide

/-- **Which sampled coins each column's committed value may read.** -/
def computeColumnChallenges (c : Fin 102) : Finset (Fin 8) := colChalOf (combinedRoundOf c)

/-- No coin is readable by a selector column: nothing has been sampled when they are committed. -/
theorem selector_columns_challenge_free (c : Fin 102) (hc : (c : ℕ) < 11) :
    computeColumnChallenges c = ∅ := by
  simp [computeColumnChallenges, combinedRoundOf, hc, colChalOf]

/-- **Commit before sample**, as a statement about the round rather than the column: a round-`r`
column may read only coins sampled strictly before round `r`. -/
theorem colChalOf_usable : ∀ r : Fin 3, ∀ j : Fin 8, j ∈ colChalOf r →
    (nockSampledAfter j : ℕ) < (r : ℕ) := by decide

/-- **Commit before sample** at every one of the 102 columns. -/
theorem computeColumns_commit_before_sampling :
    ∀ c : Fin 102, ∀ j ∈ computeColumnChallenges c,
      (nockSampledAfter j : ℕ) < (combinedRoundOf c : ℕ) :=
  fun _ j hj => colChalOf_usable _ j hj

/-! ## 4. The staged table -/

variable {L : Type*} [Field L]

/-- **The compute chip as one `Staged.StagedChip`.**  The four per-kind RAPs (each over its own
zerofier domain, `params.domain`) are derived, not stored. -/
noncomputable def computeChip (q : SegmentedRAPParams L) :
    StagedChip L 3 nockChronology where
  air := computeCombinedAIR
  params := q
  schedule := computeSchedule
  columnChallenges := computeColumnChallenges
  columns_commit_before_sampling := computeColumns_commit_before_sampling

@[simp] theorem computeChip_air (q : SegmentedRAPParams L) :
    (computeChip q).air = computeCombinedAIR := rfl

/-- The chip's round count and chronology are now the *indices of its type*
(`StagedChip L 3 nockChronology`), so `rounds = 3` holds by typing rather than as a projection
equation — the old `computeChip_rounds`.  Its residual content, that the derived RAPs carry the
count, is `computeChip_rap_k` below; what is still a field, and therefore still worth pinning, is
the schedule. -/
@[simp] theorem computeChip_schedule (q : SegmentedRAPParams L) :
    (computeChip q).schedule = computeSchedule := rfl

/-- The chip's four derived RAPs have width 102. -/
theorem computeChip_rap_w (q : SegmentedRAPParams L) (kind : Reified.ConstraintKind) :
    ((computeChip q).rap kind).w = 102 := rfl

/-- The chip's four derived RAPs carry `k = 3`, not `airToRAP`'s `1`. -/
theorem computeChip_rap_k (q : SegmentedRAPParams L) (kind : Reified.ConstraintKind) :
    ((computeChip q).rap kind).k = 3 := rfl

/-- The declared per-round widths are the real ones. -/
theorem computeChip_rap_wRAP (q : SegmentedRAPParams L) (kind : Reified.ConstraintKind) :
    ((computeChip q).rap kind).wRAP = ![11, 80, 11] := rfl

/-- **`StagedChip.satisfies_iff_kinded` at the compute chip** (`StagedTableRAP.lean:213`):
satisfying the chip is exactly per-constraint vanishing on that constraint's own kind domain. -/
theorem computeChip_satisfies_iff_kinded (q : SegmentedRAPParams L)
    (P : Fin computeCombinedAIR.numTraceCols → L[X]) :
    (computeChip q).Satisfies P
      ↔ ∀ c ∈ computeCombinedAIR.constraints, ∀ x ∈ q.domain c.kind,
          c.expr.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0 :=
  (computeChip q).satisfies_iff_kinded P


/-! ## 5. Folding loses nothing

The three blocks of a combined trace are *projections* of it, so the three separate per-kind
satisfactions are recovered with **no trace-splitting hypothesis**: the only extra inputs are the
`varsBelow` facts of §1, which are proved by kernel reduction on the shipped AIRs.

What *is* carried is the shared-parameter reading of "one table": a single `ω`, a single evaluation
domain per kind, and one public valuation whose blocks are the three AIRs' publics.  That is the
content of folding — one commitment, one zerofier family — and the agreement-form theorems below
say exactly which parameter fields must line up. -/

/-- The full width of the chip, as the chip's own AIR states it. -/
theorem chipWidth : computeCombinedAIR.numTraceCols = 102 := rfl

/-- The compute block of a combined trace: columns `0…93`. -/
def computeBlock (P : Fin computeCombinedAIR.numTraceCols → L[X]) : Fin 94 → L[X] :=
  fun i => P ⟨i, by have := i.isLt; rw [chipWidth]; omega⟩

/-- The walk block of a combined trace: columns `94…99`. -/
def walkBlock (P : Fin computeCombinedAIR.numTraceCols → L[X]) : Fin 6 → L[X] :=
  fun i => P ⟨i + 94, by have := i.isLt; rw [chipWidth]; omega⟩

/-- The prog-IO block of a combined trace: columns `100…101`. -/
def ioBlock (P : Fin computeCombinedAIR.numTraceCols → L[X]) : Fin 2 → L[X] :=
  fun i => P ⟨i + 100, by have := i.isLt; rw [chipWidth]; omega⟩

/-- The challenge and public valuations a block at offsets `(offC, offP)` sees.  Everything that
`RAP.Satisfies` reads besides these — `ω`, and the per-kind domain — is shared, which is what
"one table" means. -/
def shiftParams (q : SegmentedRAPParams L) (offC offP : ℕ) : SegmentedRAPParams L :=
  { q with chalVal := fun i => q.chalVal (i + offC), pubVal := fun i => q.pubVal (i + offP) }

@[simp] theorem shiftParams_ω (q : SegmentedRAPParams L) (offC offP : ℕ) :
    (shiftParams q offC offP).ω = q.ω := rfl

@[simp] theorem shiftParams_domain (q : SegmentedRAPParams L) (offC offP : ℕ) :
    (shiftParams q offC offP).domain = q.domain := rfl

/-! ### Environment agreement, one block at a time -/

/-- **Compute block.**  The compute constraints are not reindexed at all, and they read no column
`≥ 94`, so the combined environment and the compute block's own environment give them the same
value.  The only difference between the two environments is at columns `94…101`, where the
combined one reads the walk/IO blocks and the narrow one reads `0`. -/
theorem eval_compute_block (P : Fin computeCombinedAIR.numTraceCols → L[X]) (ω x : L)
    (cv pv : ℕ → L) (e : Reified.Expr) (he : e.varsBelow 94 5 0 = true) :
    e.eval (envOfTrace P ω x cv pv) = e.eval (envOfTrace (computeBlock P) ω x cv pv) := by
  refine Reified.Expr.eval_congr_of_varsBelow e he ?_ ?_ (fun i _ => rfl) (fun i _ => rfl)
  · intro i hi
    have h102 : i < 102 := by omega
    simp [envOfTrace, computeBlock, h102, hi]
  · intro i hi
    have h102 : i < 102 := by omega
    simp [envOfTrace, computeBlock, h102, hi]

/-- **Walk block.**  `Expr.eval_mapVars` (`ExprReindex.lean:39`) turns the reindexed expression
into the original read under a remapped environment, and that remapped environment *is* the walk
block's own environment on every variable the walk gates mention. -/
theorem eval_walk_block (P : Fin computeCombinedAIR.numTraceCols → L[X]) (ω x : L)
    (cv pv : ℕ → L) (e : Reified.Expr) (he : e.varsBelow 6 1 2 = true) :
    (e.shiftBlock walkTraceOff walkChalOff walkPubOff).eval (envOfTrace P ω x cv pv)
      = e.eval (envOfTrace (walkBlock P) ω x (fun i => cv (i + walkChalOff)) pv) := by
  rw [Reified.Expr.shiftBlock, Reified.Expr.eval_mapVars]
  refine Reified.Expr.eval_congr_of_varsBelow e he ?_ ?_ (fun i _ => rfl) (fun i _ => rfl)
  · intro i hi
    have h102 : i + 94 < 102 := by omega
    simp [Reified.Env.remap, Reified.blockShift, envOfTrace, walkBlock, walkTraceOff,
      walkPubOff, h102, hi]
  · intro i hi
    have h102 : i + 94 < 102 := by omega
    simp [Reified.Env.remap, Reified.blockShift, envOfTrace, walkBlock, walkTraceOff,
      walkPubOff, h102, hi]

/-- **Prog-IO block.**  `ioProgAIR.numChallenges = 0` and none of its three gates reads a
challenge, so the challenge valuation is a free parameter here — which is why
`RawVerifier.progIOParams`'s `chalVal := fun _ => 0` costs nothing.  Its single public value is
read at combined index `2`. -/
theorem eval_io_block (P : Fin computeCombinedAIR.numTraceCols → L[X]) (ω x : L)
    (cv cv' pv : ℕ → L) (e : Reified.Expr) (he : e.varsBelow 2 0 1 = true) :
    (e.shiftBlock ioTraceOff ioChalOff ioPubOff).eval (envOfTrace P ω x cv pv)
      = e.eval (envOfTrace (ioBlock P) ω x cv' (fun i => pv (i + ioPubOff))) := by
  rw [Reified.Expr.shiftBlock, Reified.Expr.eval_mapVars]
  refine Reified.Expr.eval_congr_of_varsBelow e he ?_ ?_ (fun i hi => absurd hi (by omega))
    (fun i _ => rfl)
  · intro i hi
    interval_cases i <;>
      simp [Reified.Env.remap, Reified.blockShift, envOfTrace, ioBlock, ioTraceOff, ioPubOff]
  · intro i hi
    interval_cases i <;>
      simp [Reified.Env.remap, Reified.blockShift, envOfTrace, ioBlock, ioTraceOff, ioPubOff]

/-! ### The three block memberships -/

theorem compute_mem_combined {c : Reified.Constraint} (hc : c ∈ computeAIRchained.constraints) :
    c ∈ computeCombinedAIR.constraints := by
  simp only [computeCombinedAIR, List.mem_append]
  exact Or.inl (Or.inl hc)

theorem walk_mem_combined {c : Reified.Constraint} (hc : c ∈ walkAIR.constraints) :
    (⟨c.kind, c.expr.shiftBlock walkTraceOff walkChalOff walkPubOff⟩ : Reified.Constraint)
      ∈ computeCombinedAIR.constraints := by
  simp only [computeCombinedAIR, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨c, hc, rfl⟩)

theorem io_mem_combined {c : Reified.Constraint} (hc : c ∈ ioProgAIR.constraints) :
    (⟨c.kind, c.expr.shiftBlock ioTraceOff ioChalOff ioPubOff⟩ : Reified.Constraint)
      ∈ computeCombinedAIR.constraints := by
  simp only [computeCombinedAIR, List.mem_append, List.mem_map]
  exact Or.inr ⟨c, hc, rfl⟩

/-! ### The payoff -/

/-- **Folding loses nothing, compute block.**  Agreement form: the recovered RAP may use any
parameters sharing the chip's `ω`, per-kind domains, and challenge valuation on its own five
coins (slots `0…4`).
`computeAIRchained` reads no public values (`numPublic = 0`), so no public hypothesis appears. -/
theorem fold_gives_compute (q qc : SegmentedRAPParams L)
    (hω : qc.ω = q.ω) (hcv : ∀ i, i < 5 → qc.chalVal i = q.chalVal i)
    (hdom : ∀ kind, qc.domain kind = q.domain kind)
    (P : Fin computeCombinedAIR.numTraceCols → L[X]) (h : (computeChip q).Satisfies P) :
    ∀ kind, (qc.rap computeAIRchained kind).Satisfies (computeBlock P) := by
  have hk := (computeChip_satisfies_iff_kinded q P).mp h
  show ∀ kind, (airToRAP (kindSeg computeAIRchained kind) qc.chalVal qc.pubVal qc.eDeg qc.hExp
      qc.ω qc.βcoset (qc.domain kind) qc.βcoset_ne_zero qc.hExp_pos).Satisfies (computeBlock P)
  refine (segmented_is_kinded computeAIRchained qc.chalVal qc.pubVal qc.eDeg qc.hExp qc.ω
    qc.βcoset qc.βcoset_ne_zero qc.hExp_pos qc.domain (computeBlock P)).mpr ?_
  intro c hc x hx
  have hvb : c.expr.varsBelow 94 5 0 = true :=
    (List.all_eq_true.mp computeAIRchained_varsBelow) c hc
  have hzero := hk c (compute_mem_combined hc) x (by rw [hdom] at hx; exact hx)
  refine Eq.trans ?_ hzero
  refine Eq.trans ?_ (eval_compute_block P q.ω x q.chalVal q.pubVal c.expr hvb).symm
  exact Reified.Expr.eval_congr_of_varsBelow c.expr hvb
    (fun _ _ => rfl) (fun _ _ => by rw [hω]; rfl)
    (fun i hi => hcv i hi) (fun i hi => absurd hi (by omega))

/-- **Folding loses nothing, walk block.**  Agreement form: the recovered walk RAP may use any
parameters sharing the chip's `ω` and domains, whose challenge `0` is the chip's challenge `5`
(the walk coin, *not* the table's `α` — see the header note), and whose two public values are the
chip's publics `0` and `1`. -/
theorem fold_gives_walk (q qw : SegmentedRAPParams L)
    (hω : qw.ω = q.ω) (hcv : ∀ i, i < 1 → qw.chalVal i = q.chalVal (i + walkChalOff))
    (hpv : ∀ i, i < 2 → qw.pubVal i = q.pubVal (i + walkPubOff))
    (hdom : ∀ kind, qw.domain kind = q.domain kind)
    (P : Fin computeCombinedAIR.numTraceCols → L[X]) (h : (computeChip q).Satisfies P) :
    ∀ kind, (qw.rap walkAIR kind).Satisfies (walkBlock P) := by
  have hk := (computeChip_satisfies_iff_kinded q P).mp h
  show ∀ kind, (airToRAP (kindSeg walkAIR kind) qw.chalVal qw.pubVal qw.eDeg qw.hExp
      qw.ω qw.βcoset (qw.domain kind) qw.βcoset_ne_zero qw.hExp_pos).Satisfies (walkBlock P)
  refine (segmented_is_kinded walkAIR qw.chalVal qw.pubVal qw.eDeg qw.hExp qw.ω
    qw.βcoset qw.βcoset_ne_zero qw.hExp_pos qw.domain (walkBlock P)).mpr ?_
  intro c hc x hx
  have hvb : c.expr.varsBelow 6 1 2 = true :=
    (List.all_eq_true.mp walkAIR_varsBelow) c hc
  have hzero : (c.expr.shiftBlock walkTraceOff walkChalOff walkPubOff).eval
      (envOfTrace P q.ω x q.chalVal q.pubVal) = 0 :=
    hk ⟨c.kind, c.expr.shiftBlock walkTraceOff walkChalOff walkPubOff⟩
      (walk_mem_combined hc) x (by rw [hdom] at hx; exact hx)
  rw [eval_walk_block P q.ω x q.chalVal q.pubVal c.expr hvb] at hzero
  refine Eq.trans ?_ hzero
  exact Reified.Expr.eval_congr_of_varsBelow c.expr hvb
    (fun _ _ => rfl) (fun _ _ => by rw [hω]; rfl)
    (fun i hi => hcv i hi) (fun i hi => hpv i hi)

/-- **Folding loses nothing, prog-IO block.**  Agreement form: the recovered IO RAP may use any
parameters sharing the chip's `ω` and domains whose single public value is the chip's public `2`.
The challenge valuation is unconstrained. -/
theorem fold_gives_io (q qi : SegmentedRAPParams L)
    (hω : qi.ω = q.ω) (hpv : ∀ i, i < 1 → qi.pubVal i = q.pubVal (i + ioPubOff))
    (hdom : ∀ kind, qi.domain kind = q.domain kind)
    (P : Fin computeCombinedAIR.numTraceCols → L[X]) (h : (computeChip q).Satisfies P) :
    ∀ kind, (qi.rap ioProgAIR kind).Satisfies (ioBlock P) := by
  have hk := (computeChip_satisfies_iff_kinded q P).mp h
  show ∀ kind, (airToRAP (kindSeg ioProgAIR kind) qi.chalVal qi.pubVal qi.eDeg qi.hExp
      qi.ω qi.βcoset (qi.domain kind) qi.βcoset_ne_zero qi.hExp_pos).Satisfies (ioBlock P)
  refine (segmented_is_kinded ioProgAIR qi.chalVal qi.pubVal qi.eDeg qi.hExp qi.ω
    qi.βcoset qi.βcoset_ne_zero qi.hExp_pos qi.domain (ioBlock P)).mpr ?_
  intro c hc x hx
  have hvb : c.expr.varsBelow 2 0 1 = true :=
    (List.all_eq_true.mp ioProgAIR_varsBelow) c hc
  have hzero : (c.expr.shiftBlock ioTraceOff ioChalOff ioPubOff).eval
      (envOfTrace P q.ω x q.chalVal q.pubVal) = 0 :=
    hk ⟨c.kind, c.expr.shiftBlock ioTraceOff ioChalOff ioPubOff⟩
      (io_mem_combined hc) x (by rw [hdom] at hx; exact hx)
  rw [eval_io_block P q.ω x q.chalVal qi.chalVal q.pubVal c.expr hvb] at hzero
  refine Eq.trans ?_ hzero
  exact Reified.Expr.eval_congr_of_varsBelow c.expr hvb
    (fun _ _ => rfl) (fun _ _ => by rw [hω]; rfl)
    (fun i hi => absurd hi (by omega)) (fun i hi => hpv i hi)

/-- **The headline: folding the three compute-side AIRs into one staged table loses nothing.**

Satisfying the single 102-column, 537-constraint staged chip yields the three separate per-kind
`RAP.Satisfies` obligations — one per AIR — that `RawVerifier.SixRAPSatisfy` (`:408`) consumes
on the compute side, at the chip's own parameters with the IO block's public valuation offset.

**No trace-splitting hypothesis is needed**: the blocks are projections of the combined trace and
the variable-range facts are theorems about the shipped AIRs (`computeAIRchained_varsBelow`,
`walkAIR_varsBelow`, `ioProgAIR_varsBelow`), each proved by kernel reduction. -/
theorem computeChip_fold_loses_nothing (q : SegmentedRAPParams L)
    (P : Fin computeCombinedAIR.numTraceCols → L[X]) (h : (computeChip q).Satisfies P) :
    (∀ kind, (q.rap computeAIRchained kind).Satisfies (computeBlock P))
      ∧ (∀ kind, ((shiftParams q walkChalOff walkPubOff).rap walkAIR kind).Satisfies (walkBlock P))
      ∧ (∀ kind, ((shiftParams q ioChalOff ioPubOff).rap ioProgAIR kind).Satisfies (ioBlock P)) :=
  ⟨fold_gives_compute q q rfl (fun _ _ => rfl) (fun _ => rfl) P h,
   fold_gives_walk q (shiftParams q walkChalOff walkPubOff) rfl (fun _ _ => rfl)
     (fun _ _ => rfl) (fun _ => rfl) P h,
   fold_gives_io q (shiftParams q ioChalOff ioPubOff) rfl (fun _ _ => rfl) (fun _ => rfl) P h⟩

/-! ### The converse: the fold is complete, not merely sound -/

/-- Lay three block traces side by side into one combined trace. -/
def concatBlocks (Pc : Fin 94 → L[X]) (Pw : Fin 6 → L[X]) (Pi : Fin 2 → L[X]) :
    Fin computeCombinedAIR.numTraceCols → L[X] := fun i =>
  if h : (i : ℕ) < 94 then Pc ⟨i, h⟩
  else if h2 : (i : ℕ) < 100 then Pw ⟨(i : ℕ) - 94, by omega⟩
  else Pi ⟨(i : ℕ) - 100, by have := lt_of_lt_of_eq i.isLt chipWidth; omega⟩

@[simp] theorem computeBlock_concat (Pc : Fin 94 → L[X]) (Pw : Fin 6 → L[X])
    (Pi : Fin 2 → L[X]) : computeBlock (concatBlocks Pc Pw Pi) = Pc := by
  funext i; simp [computeBlock, concatBlocks, i.isLt]

@[simp] theorem walkBlock_concat (Pc : Fin 94 → L[X]) (Pw : Fin 6 → L[X])
    (Pi : Fin 2 → L[X]) : walkBlock (concatBlocks Pc Pw Pi) = Pw := by
  funext i
  have hi := i.isLt
  simp only [walkBlock, concatBlocks]
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 1

@[simp] theorem ioBlock_concat (Pc : Fin 94 → L[X]) (Pw : Fin 6 → L[X])
    (Pi : Fin 2 → L[X]) : ioBlock (concatBlocks Pc Pw Pi) = Pi := by
  funext i
  have hi := i.isLt
  simp only [ioBlock, concatBlocks]
  rw [dif_neg (by omega), dif_neg (by omega)]
  congr 1

/-- **The fold is complete.**  Three block traces satisfying the three separate per-kind RAPs
concatenate to a trace satisfying the single staged chip — so `computeChip` is equivalent to, not
weaker than, the three-AIR conjunction. -/
theorem computeChip_satisfies_concat (q : SegmentedRAPParams L)
    (Pc : Fin 94 → L[X]) (Pw : Fin 6 → L[X]) (Pi : Fin 2 → L[X])
    (hc : ∀ kind, (q.rap computeAIRchained kind).Satisfies Pc)
    (hw : ∀ kind, ((shiftParams q walkChalOff walkPubOff).rap walkAIR kind).Satisfies Pw)
    (hi : ∀ kind, ((shiftParams q ioChalOff ioPubOff).rap ioProgAIR kind).Satisfies Pi) :
    (computeChip q).Satisfies (concatBlocks Pc Pw Pi) := by
  have hc' := (segmented_is_kinded computeAIRchained q.chalVal q.pubVal q.eDeg q.hExp q.ω
    q.βcoset q.βcoset_ne_zero q.hExp_pos q.domain Pc).mp hc
  have hw' := (segmented_is_kinded walkAIR (shiftParams q walkChalOff walkPubOff).chalVal
    (shiftParams q walkChalOff walkPubOff).pubVal q.eDeg q.hExp q.ω
    q.βcoset q.βcoset_ne_zero q.hExp_pos q.domain Pw).mp hw
  have hi' := (segmented_is_kinded ioProgAIR (shiftParams q ioChalOff ioPubOff).chalVal
    (shiftParams q ioChalOff ioPubOff).pubVal q.eDeg q.hExp q.ω q.βcoset q.βcoset_ne_zero q.hExp_pos
    q.domain Pi).mp hi
  refine (computeChip_satisfies_iff_kinded q (concatBlocks Pc Pw Pi)).mpr ?_
  intro c hc0 x hx
  simp only [computeCombinedAIR, List.mem_append, List.mem_map] at hc0
  rcases hc0 with (hcomp | ⟨d, hd, rfl⟩) | ⟨d, hd, rfl⟩
  · have hvb : c.expr.varsBelow 94 5 0 = true :=
      (List.all_eq_true.mp computeAIRchained_varsBelow) c hcomp
    rw [eval_compute_block (concatBlocks Pc Pw Pi) q.ω x q.chalVal q.pubVal c.expr hvb,
      computeBlock_concat]
    exact hc' c hcomp x hx
  · have hvb : d.expr.varsBelow 6 1 2 = true :=
      (List.all_eq_true.mp walkAIR_varsBelow) d hd
    show (d.expr.shiftBlock walkTraceOff walkChalOff walkPubOff).eval
      (envOfTrace (concatBlocks Pc Pw Pi) q.ω x q.chalVal q.pubVal) = 0
    rw [eval_walk_block (concatBlocks Pc Pw Pi) q.ω x q.chalVal q.pubVal d.expr hvb,
      walkBlock_concat]
    exact hw' d hd x hx
  · have hvb : d.expr.varsBelow 2 0 1 = true :=
      (List.all_eq_true.mp ioProgAIR_varsBelow) d hd
    show (d.expr.shiftBlock ioTraceOff ioChalOff ioPubOff).eval
      (envOfTrace (concatBlocks Pc Pw Pi) q.ω x q.chalVal q.pubVal) = 0
    rw [eval_io_block (concatBlocks Pc Pw Pi) q.ω x q.chalVal
      (shiftParams q ioChalOff ioPubOff).chalVal q.pubVal d.expr hvb, ioBlock_concat]
    exact hi' d hd x hx

/-- **Two-sided.**  The staged chip and the three-AIR conjunction accept the same traces, up to the
concatenation/projection pair. -/
theorem computeChip_satisfies_iff_blocks (q : SegmentedRAPParams L)
    (Pc : Fin 94 → L[X]) (Pw : Fin 6 → L[X]) (Pi : Fin 2 → L[X]) :
    (computeChip q).Satisfies (concatBlocks Pc Pw Pi)
      ↔ ((∀ kind, (q.rap computeAIRchained kind).Satisfies Pc)
          ∧ (∀ kind, ((shiftParams q walkChalOff walkPubOff).rap walkAIR kind).Satisfies Pw)
          ∧ (∀ kind, ((shiftParams q ioChalOff ioPubOff).rap ioProgAIR kind).Satisfies Pi)) := by
  refine ⟨fun h => ?_, fun h => computeChip_satisfies_concat q Pc Pw Pi h.1 h.2.1 h.2.2⟩
  obtain ⟨h1, h2, h3⟩ := computeChip_fold_loses_nothing q (concatBlocks Pc Pw Pi) h
  rw [computeBlock_concat] at h1
  rw [walkBlock_concat] at h2
  rw [ioBlock_concat] at h3
  exact ⟨h1, h2, h3⟩

/-! ### Column-round characterisation

Spelled out so a later reader can check the assignment against `computeEnvFull` (`AIR.lean:478`)
without re-deriving it, and so a wrong assignment shows up as a broken theorem. -/

theorem combinedRoundOf_selector (c : Fin 102) (hc : (c : ℕ) < 11) : combinedRoundOf c = 0 := by
  simp [combinedRoundOf, hc]

theorem combinedRoundOf_megaExt (c : Fin 102) (h1 : ¬ (c : ℕ) < 11)
    (h2 : (c : ℕ) ∈ megaExtCols) : combinedRoundOf c = 2 := by
  simp [combinedRoundOf, h1, h2]

theorem combinedRoundOf_ext (c : Fin 102) (h1 : ¬ (c : ℕ) < 11)
    (h2 : (c : ℕ) ∉ megaExtCols) : combinedRoundOf c = 1 := by
  simp [combinedRoundOf, h1, h2]

/-- The eleven mega-ext columns are distinct, so `width 2 = 11` counts them one each. -/
theorem megaExtCols_nodup : megaExtCols.Nodup := by decide

theorem megaExtCols_length : megaExtCols.length = 11 := rfl

/-- `pub.ln_prev` (slot 65) and `pub.ln` (slot 66) are round-2 columns. -/
theorem ln_columns_round_two : combinedRoundOf 65 = 2 ∧ combinedRoundOf 66 = 2 := by decide

/-- The three record timestamps `pub.mr1/mr2/mr3.ts` (slots 74/82/90) are round-2 columns. -/
theorem ts_columns_round_two :
    combinedRoundOf 74 = 2 ∧ combinedRoundOf 82 = 2 ∧ combinedRoundOf 90 = 2 := by decide

/-- The walk accumulators (offset columns 94/95/96) and its two α-RLC columns (98/99) are
round-2; the walk's node fingerprint `cur` (97) is round-1, since it is seeded by the NPR seed
`z` and not by `α`. -/
theorem walk_columns_rounds :
    combinedRoundOf 94 = 2 ∧ combinedRoundOf 95 = 2 ∧ combinedRoundOf 96 = 2 ∧
      combinedRoundOf 97 = 1 ∧ combinedRoundOf 98 = 2 ∧ combinedRoundOf 99 = 2 := by decide

/-- `acc_prog` (offset column 100) is round-2 — the paper has the prover build it only after
the verifier's response at `:509`.  The prog-IO row fraction (101) is part of `IO_prog`, committed
at `:508`, so it is round-1. -/
theorem io_columns_rounds : combinedRoundOf 100 = 2 ∧ combinedRoundOf 101 = 1 := by decide

/-- The `inp.z⁻¹` witness (slot 93) is a round-1 ext column: it reads the NPR seed `z`, which is
sampled after round 0, and not `α`. -/
theorem zinv_column_round_one : combinedRoundOf 93 = 1 := by decide

/-- All eleven opcode selectors are round-0. -/
theorem selector_columns_round_zero :
    ∀ c : Fin 102, (c : ℕ) < 11 → combinedRoundOf c = 0 :=
  fun c hc => combinedRoundOf_selector c hc

/-! ## 6. What is *not* discharged: `SixRAPSatisfy`'s compute side lives at two fields

`computeChip_fold_loses_nothing` recovers the three per-kind `RAP.Satisfies` obligations at **one**
field `L`.  `RawVerifier.RawMessage.SixRAPSatisfy` (`RawVerifier.lean:408`) does not have that
shape: its first two compute-side conjuncts are `RAP K` obligations
(`computeTableRAP`/`computeWalkRAP`, `:262`/`:269`), while the third is a `RAP (IOField K)`
obligation (`computeIORAP`, `:274`) with
`IOField K = RatFunc (RatFunc K)` (`PlusIOSegmentedRAP.lean:196`) and
`progIOParams.ω = algebraMap K (IOField K) cfg.orbit.ω` (`:227`).

So wiring this chip into `SixRAPSatisfy` needs a **base-change** lemma transporting
`RAP.Satisfies` along `algebraMap K (IOField K)` — an obligation that is entirely independent of
folding: it is already there in the six-RAP statement, and folding neither creates nor removes it.
`fold_gives_compute` / `fold_gives_walk` / `fold_gives_io` are stated in agreement form precisely
so that, once such a transport exists, they apply to the actual parameter tuples rather than only
to derived ones. -/

end Nock.NockVMROM.Thm54.ComputeChip

section Audit

open Nock.NockVMROM.Thm54.ComputeChip

#check @Nock.Reified.Expr.varsBelow
#check @Nock.Reified.Expr.eval_congr_of_varsBelow
#check @Nock.Reified.Expr.shiftBlock
#check @Nock.Reified.Expr.shiftBlock_eq_shiftTrace
#check @computeCombinedAIR
#check @computeCombinedAIR_num_constraints
#check @computeCombinedAIR_kind_census
#check @computeCombinedAIR_maxDegree
#check @computeSchedule
#check @Nock.NockVMROM.Thm54.GigaChips.nockChronology
#check @computeChip
#check @computeChip_satisfies_iff_kinded
#check @computeChip_fold_loses_nothing
#check @computeChip_satisfies_concat
#check @computeChip_satisfies_iff_blocks

#print axioms Nock.Reified.Expr.eval_congr_of_varsBelow
#print axioms Nock.Reified.Expr.shiftBlock_eq_shiftTrace
#print axioms Nock.Reified.Expr.degree_shiftBlock
#print axioms computeCombinedAIR_num_constraints
#print axioms computeCombinedAIR_kind_census
#print axioms computeCombinedAIR_kindSeg_census
#print axioms computeCombinedAIR_census_total
#print axioms computeCombinedAIR_maxDegree
#print axioms computeCombinedAIR_compute_prefix
#print axioms lnChain_mem_combined
#print axioms computeAIRchained_varsBelow
#print axioms walkAIR_varsBelow
#print axioms ioProgAIR_varsBelow
#print axioms computeSchedule_total
#print axioms Nock.NockVMROM.Thm54.GigaChips.nockSampledAfter_fibres
#print axioms Nock.NockVMROM.Thm54.GigaChips.alpha_sampled_after_round_one
#print axioms Nock.NockVMROM.Thm54.GigaChips.seed_coins_sampled_after_round_zero
#print axioms colChalOf_lt_six
#print axioms colChalOf_usable
#print axioms computeColumns_commit_before_sampling
#print axioms selector_columns_challenge_free
#print axioms computeChip_rap_k
#print axioms computeChip_rap_wRAP
#print axioms computeChip_satisfies_iff_kinded
#print axioms eval_compute_block
#print axioms eval_walk_block
#print axioms eval_io_block
#print axioms fold_gives_compute
#print axioms fold_gives_walk
#print axioms fold_gives_io
#print axioms computeChip_fold_loses_nothing
#print axioms computeChip_satisfies_concat
#print axioms computeChip_satisfies_iff_blocks
#print axioms megaExtCols_nodup
#print axioms walk_columns_rounds
#print axioms io_columns_rounds

end Audit
