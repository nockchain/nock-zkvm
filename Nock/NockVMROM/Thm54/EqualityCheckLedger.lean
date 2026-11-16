import Nock.NockVMROM.Thm54.OptimizedComputeFinal
import Nock.NockVMROM.Thm54.GatheredMemoryScalarGates
import Nock.NockVMROM.Thm54.PaperResourceCounts
import Nock.NockVMROM.Thm54.RAPPadding

/-!
# The equality-check ledger: what the `𝔽 → 𝕂` challenge migration actually costs

## What the paper counts in its equality-check bucket

Theorem 5.4 states every resource of both chips as an affine function of `e`
with **two exceptions**: "Two equality checks" and "Four equality checks" carry no `e`.  That is not an omission, and the evidence is positive rather than
an argument from the absent symbol:

* `Thm:Walk_IOP`'s cost list prices the walk's terminal check as "One equality check".  The quantity being checked is `out_walk = 0`, and `out_walk` is **`𝕂`-valued** by construction — the paper types it as "the final output `out_walk ∈ 𝕂` of the `acc_walk` columns".  So the paper counts a
  `𝕂`-valued equality as **one**, in the very same list where it counts a `𝕂`-valued *gate* as
  `e`.
* The IO section says why: "the **Verifier** performs the following equality checks", on `out_prog`, `out_mem` and the `requests`/`responses` pair — all `𝕂`-valued
  terminal outputs, checked outside the committed constraint system, so there is nothing to
  coordinate-expand.  the paper makes the practice explicit.

`paper_equality_checks_reconstructed` below records that the paper's own `2` and `4` decompose
with zero slack under this unit.

**Consequence.**

## What the tree counts in its equality-check bucket

`Thm54Resources.computeEqualityChecks` and `memoryEqualityChecks` are summands of
`computeConstraints` / `memoryConstraints`, which the capstone pins to `C.rap.s` and `M.rap.s` —
the *lengths of the committed gate lists*.  So in this tree the bucket counts **committed
base-field AIR gates**, not verifier-side `𝕂` equalities.

**Both repairs below have now landed, and the units have visibly diverged.**  The counters read
`22` and `4·e = 12`, against the paper's `2` and `4`, and `C.rap.s = 118`, `M.rap.s = 112`.  The
occupants were:

Neither is a terminal-output equality.

So the `2 → 2·e`, `2 → 22` and `4 → 4·e` measured below are costs against the *tree's*
accounting, and the paper conjunct they collide with is one the tree never matched by
construction.

## Which repair the migration requires

Retyping and de-compression are **independent** repairs of the same `/|𝔽|` term, not a sequence:
retyping keeps the coin and widens its sample space to `𝕂`; de-compression deletes the coin and
its collision event outright.  They are separable because they cost differently, and that is the
measurement `KO` asked for:

* an **eleven**-term family (`challenge36`) costs `e = 3` gates retyped and `11` de-compressed.
  `2 → 6` against `2 → 22`.  Here the two repairs are five-fold apart and `JW` §3's next sentence
  already says so.

## The finding: the memory transition cost is absorbed by existing inert padding

It is not.
The memory chip reaches its `24·e + 16` transition count by appending
`RAPPadding.residualTransitionGates e = 3·e + 2` gates that
`RAPPadding.padMemoryCore_residual_compose_zero` proves **compose to zero** (source `s = 93`,
padded `s = 104`; `OptimizedMemoryRAP.sourceMemoryRAP_fingerprint`,
`finalMemoryRAP_fingerprint`).  The repair consumes `3·(e-1)` of those inert slots and `5`
remain — *for every `e`* — so `memoryTransitionGates` is unchanged at `24·e + 16`.

The memory total is therefore `32·e + 16 = 112`, not `35·e + 13 = 118`.

The
paragraph above is the `KV`-era history.  The residual is now `0` (`LL`'s chain took `3`, `LV`'s
denominator pin `2` and one more), the tree's committed transition count is the disclosed
`26·e + 11 = 89` (`Thm54Resources.memoryTransitionGates`; the paper's `24·e + 16 = 88` survives as
`memoryTransitionGatesPaper`), and `M.rap.s = 113`.
-/

namespace Nock.NockVMROM.Thm54
namespace EqualityCheckLedger

open Nock.Framework
open Nock.Reified
open Module
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedComputeFinal

noncomputable section

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-! ## 1. What `challenge36` compresses

`finalSelectorPublicCheck kind publicBase` (`OptimizedComputeFinal.lean`) is
`Σ_{i<11} χ^i · (trace_i − public_{publicBase+i})` with `χ` the challenge at
`finalScalarChallengeBase`, i.e. `FinalComputeChallengeTuple.challenge36`
(`OptimizedComputeCollisionBound.lean`).  The eleven compressed scalar equations are exactly the
list below, and the family is used at two offsets, `20` and `31`
(`finalMaskedEndpointEqualityChecks`). -/

/-- The **eleven** base-field scalar equations that one `finalSelectorPublicCheck` family
compresses: selector column `i` against public value `publicBase + i`. -/
def selectorPublicTerms (publicBase : ℕ) : List (CoeffExpr F) :=
  (List.range 11).map fun i =>
    .sub (.var .traceCur i) (.var .publicVal (publicBase + i))

omit [Field F] in
@[simp] theorem selectorPublicTerms_length (publicBase : ℕ) :
    (selectorPublicTerms (F := F) publicBase).length = 11 := by
  simp [selectorPublicTerms]

/-- **The compression is exactly over those eleven terms.**  If every one of them vanishes then
the compressed check vanishes, for every value of the coin — so de-compression is at least as
strong as the compressed gate at every `challenge36`.  The converse fails, which is what makes
the coin load-bearing: `OptimizedComputeGateBasisObstruction`'s
`selector_public_rlc_requires_challenge36_exclusion` exhibits a trace the compressed gate accepts
with the terms nonzero. -/
theorem compressed_of_decompressed (publicBase : ℕ) (env : Env F)
    (h : ∀ t ∈ selectorPublicTerms (F := F) publicBase, t.eval env = 0) :
    (finalSelectorPublicCheck (F := F) .traceCur publicBase).eval env = 0 := by
  rw [finalSelectorPublicCheck, CoeffExpr.eval_sumList]
  refine List.sum_eq_zero ?_
  intro y hy
  simp only [List.mem_map, List.mem_range] at hy
  obtain ⟨i, hi, rfl⟩ := hy
  have hmem : (CoeffExpr.sub (.var .traceCur i) (.var .publicVal (publicBase + i)))
      ∈ selectorPublicTerms (F := F) publicBase := by
    simp only [selectorPublicTerms, List.mem_map, List.mem_range]
    exact ⟨i, hi, rfl⟩
  have := h _ hmem
  simp only [CoeffExpr.eval] at this ⊢
  rw [this, mul_zero]

/-- The de-compressed replacement for the compute chip's two equality checks: each family's
eleven terms, masked as the compressed gate was.  **Twenty-two base-field gates.** -/
def decompressedComputeEqualityChecks : List (CoeffExpr F) :=
  (selectorPublicTerms 20).map (CoeffExpr.mul isFirstVar) ++
    (selectorPublicTerms 31).map (CoeffExpr.mul isLastVar)

omit [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] in
@[simp] theorem decompressedComputeEqualityChecks_length :
    (decompressedComputeEqualityChecks (F := F)).length = 22 := by
  simp [decompressedComputeEqualityChecks]

theorem compressedComputeEqualityChecks_length :
    (finalMaskedEndpointEqualityChecks (F := F)).length = 2 :=
  finalMaskedEndpointEqualityChecks_length

/-- **The ledger's projection is now the deployed object, character for character.**

`decompressedComputeEqualityChecks` was written here as the *prediction* of what de-compressing
`challenge36` would commit.  Stage 3e committed exactly that list, under the name
`OptimizedComputeFinal.finalEndpointEqualityChecks`.  This theorem is what makes the `2 → 22`
row of the ledger below a measurement of the deployed chip rather than of a hypothetical. -/
theorem ledger_prediction_is_the_deployed_list :
    (decompressedComputeEqualityChecks (F := F)) = finalEndpointEqualityChecks := by
  simp only [decompressedComputeEqualityChecks, finalEndpointEqualityChecks, selectorPublicTerms,
    List.map_map, Function.comp_def]
  congr 1 <;> exact List.map_congr_left fun i _ => rfl

/-! ## 2. What a `𝕂`-valued check costs when committed over `𝔽`: exactly `e`

This is the content of "retyping is `+1 → +e`".  It is an equality, not a bound: `e` coordinate
equations are necessary as well as sufficient. -/

omit [FiniteDimensional F K] in
/-- **Sufficient and necessary: a `𝕂`-valued equation is exactly its `e` coordinate equations.** -/
theorem ext_eq_zero_iff_coords {e : ℕ} (b : Basis (Fin e) F K) (x : K) :
    x = 0 ↔ ∀ k : Fin e, b.repr x k = 0 := by
  constructor
  · rintro rfl k; simp
  · intro h
    have hx : b.repr x = 0 := Finsupp.ext fun k => by simpa using h k
    have := congrArg b.repr.symm hx
    simpa using this

omit [FiniteDimensional F K] in
/-- **No fewer than `e` gates will do.**  Drop any single coordinate equation and a nonzero
element of `𝕂` satisfies all the rest, so committing a retyped check with `e-1` base-field gates
is strictly weaker.  Together with `ext_eq_zero_iff_coords` this makes `e` the exact cost. -/
theorem dropping_a_coordinate_admits_nonzero {e : ℕ} (b : Basis (Fin e) F K) (k₀ : Fin e) :
    ∃ x : K, x ≠ 0 ∧ ∀ k : Fin e, k ≠ k₀ → b.repr x k = 0 := by
  refine ⟨b k₀, b.ne_zero k₀, fun k hk => ?_⟩
  simp [Basis.repr_self, hk.symm]

/-- The list-level form already in the tree, restated at the ledger: committing a list of
`𝕂`-valued gates costs `length · e` base-field gates.  This is
`MonolithicRAP.length_expandList`, the same fact
`GatheredMemoryScalarGates.extension_gate_costs_three_base_gates` reads off at `e = 3`. -/
theorem retyped_gate_length {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    (l : List Nock.Reified.Expr) :
    (MonolithicRAP.expandList b col0 l).length = l.length * e :=
  MonolithicRAP.length_expandList b col0 l

end

/-! ## 3. The paper's equality-check bucket, reconstructed

Both of Theorem 5.4's `e`-independent counts decompose with **zero slack** under the unit
"one `𝕂`-valued terminal equality":

* compute `RAP_NockComp-IO` = compute walk
  + `RAP_prog-IO` additional costs = **two**;
* memory `RAP_NockMem-IO` = forest walk + `RAP_mem-IO` additional costs + the `intermediate` accumulator's terminal check
  = **four**.

Every summand is an equality on a `𝕂`-valued accumulator output. -/

/-- The paper's own `2` and `4` recovered from their components, **and the tree's counters
beside them**.

Compute's `2` is the walk's `out_walk = 0` plus `RAP_prog-IO`'s check; memory's `4` is the forest walk's plus `RAP_mem-IO`'s two plus the `intermediate` terminal check.  Both decompose with zero
slack.

**So neither half is an identification any more, and that is the correct state**: `JZ` §4 and
`KR` §4 both said the agreement was a coincidence, and both repairs have now removed it. -/
theorem paper_equality_checks_reconstructed :
    (1 + 1 = 2 ∧ 1 + 2 + 1 = 4) ∧
      Thm54Resources.computeEqualityChecks Thm54Resources.deployedExtensionDegree = 22 ∧
      Thm54Resources.memoryEqualityChecks Thm54Resources.deployedExtensionDegree = 0 := by
  refine ⟨⟨by decide, by decide⟩, by decide, rfl⟩

/-- **The tree's counters no longer agree with the paper's, on either chip** — stated as the
negative it is, so that nobody re-reads the coincidence back into the numbers. -/
theorem tree_counters_diverge_from_the_paper :
    Thm54Resources.computeEqualityChecks Thm54Resources.deployedExtensionDegree ≠ 2 ∧
      Thm54Resources.memoryEqualityChecks Thm54Resources.deployedExtensionDegree ≠ 4 := by
  refine ⟨by decide, by decide⟩

/-! ## 4. The compute ledger -/

/-- `Thm54Resources.computeEqualityChecks` after retyping `challenge36` to `𝕂`: each of the two
families is committed by its `e` coordinates (§2). -/
def computeEqualityChecksRetyped (e : ℕ) : ℕ := 2 * e

/-- `Thm54Resources.computeEqualityChecks` after de-compressing the two eleven-term families. -/
def computeEqualityChecksDecompressed : ℕ := 22

def computeEqualityChecksCompressed : ℕ := 2

/-- The deployed counter **is** the de-compressed one. -/
theorem computeEqualityChecksDecompressed_is_deployed :
    Thm54Resources.computeEqualityChecks Thm54Resources.deployedExtensionDegree
      = computeEqualityChecksDecompressed := by decide

/-- The paper's degree-`1` endpoint bucket `2·e`, which this ledger's history
was measured against. -/
def computeDegreeOneGatesPaper (e : ℕ) : ℕ := 2 * e

/-- Every delta below is measured against this. -/
def computeConstraintsCompressed (e : ℕ) : ℕ :=
  Thm54Resources.computeTransitionGatesPaper e + computeDegreeOneGatesPaper e
    + Thm54Resources.computeDegreeThreeGates e + computeEqualityChecksCompressed

def computeConstraintsDecompressed (e : ℕ) : ℕ :=
  Thm54Resources.computeTransitionGatesPaper e + computeDegreeOneGatesPaper e
    + Thm54Resources.computeDegreeThreeGates e + computeEqualityChecksDecompressed

theorem computeConstraintsDecompressed_closed (e : ℕ) :
    computeConstraintsDecompressed e = 27 * e + 37 := by
  simp only [computeConstraintsDecompressed, Thm54Resources.computeTransitionGatesPaper,
    computeDegreeOneGatesPaper, Thm54Resources.computeDegreeThreeGates,
    computeEqualityChecksDecompressed]
  omega

theorem computeConstraintsCompressed_closed (e : ℕ) :
    computeConstraintsCompressed e = 27 * e + 17 := by
  simp only [computeConstraintsCompressed, Thm54Resources.computeTransitionGatesPaper,
    computeDegreeOneGatesPaper, Thm54Resources.computeDegreeThreeGates,
    computeEqualityChecksCompressed]
  omega

/-- **The compute number the de-compression actually landed: `98 → 118`.** -/
theorem compute_decompression_delta :
    computeConstraintsDecompressed 3 = computeConstraintsCompressed 3 + 20 := by
  rw [computeConstraintsDecompressed_closed, computeConstraintsCompressed_closed]

def computeConstraintsAnchored (e : ℕ) : ℕ :=
  Thm54Resources.computeTransitionGatesPaper e + 4 * e
    + Thm54Resources.computeDegreeThreeGates e + computeEqualityChecksDecompressed

theorem computeConstraintsAnchored_closed (e : ℕ) :
    computeConstraintsAnchored e = 29 * e + 37 := by
  simp only [computeConstraintsAnchored, Thm54Resources.computeTransitionGatesPaper,
    Thm54Resources.computeDegreeThreeGates, computeEqualityChecksDecompressed]
  omega

theorem compute_anchoring_delta :
    computeConstraintsAnchored 3 = computeConstraintsDecompressed 3 + 6 := by
  rw [computeConstraintsAnchored_closed, computeConstraintsDecompressed_closed]

theorem compute_ln_origin_delta :
    Thm54Resources.computeConstraints 3 = 418 := by
  rw [Thm54Resources.computeConstraints_closed]

theorem computeEqualityChecksRetyped_deployed : computeEqualityChecksRetyped 3 = 6 := by decide

/-- **The two repairs are not the same repair on the compute chip.**  `2 → 6` against `2 → 22`. -/
theorem compute_repairs_differ :
    computeEqualityChecksRetyped 3 ≠ computeEqualityChecksDecompressed := by decide

/-- The de-compressed count is the measured length of the actual replacement gate list, not a
hand-entered number. -/
theorem computeEqualityChecksDecompressed_is_the_list_length {F : Type} [Field F] :
    (decompressedComputeEqualityChecks (F := F)).length = computeEqualityChecksDecompressed := by
  simp [computeEqualityChecksDecompressed]

/-- The compute chip's constraint total after the retype, with the other three buckets unchanged:
the `challenge36` gates are the whole equality bucket and touch nothing else. -/
def computeConstraintsRetyped (e : ℕ) : ℕ :=
  Thm54Resources.computeTransitionGatesPaper e + computeDegreeOneGatesPaper e
    + Thm54Resources.computeDegreeThreeGates e + computeEqualityChecksRetyped e

theorem computeConstraintsRetyped_closed (e : ℕ) :
    computeConstraintsRetyped e = 29 * e + 15 := by
  simp only [computeConstraintsRetyped, Thm54Resources.computeTransitionGatesPaper,
    computeDegreeOneGatesPaper, Thm54Resources.computeDegreeThreeGates,
    computeEqualityChecksRetyped]
  omega

/-- **The compute number: `98 → 102`.** -/
theorem computeConstraintsRetyped_deployed : computeConstraintsRetyped 3 = 102 := by
  rw [computeConstraintsRetyped_closed]

theorem compute_migration_delta :
    computeConstraintsRetyped 3 = computeConstraintsCompressed 3 + 4 := by
  rw [computeConstraintsRetyped_closed, computeConstraintsCompressed_closed]

/-- The compute transition bucket is **untouched** by the migration — the paper's `15 + 24·e` still holds exactly. -/
theorem compute_transition_bucket_unmoved (e : ℕ) :
    computeConstraintsRetyped e - (computeDegreeOneGatesPaper e
        + Thm54Resources.computeDegreeThreeGates e + computeEqualityChecksRetyped e)
      = Thm54Resources.computeTransitionGatesPaper e := by
  simp only [computeConstraintsRetyped]
  omega

/-! ## 5. The memory ledger, with padding absorption

The three mask/chain families (`firstMaskBindingGate`, `lastMaskBindingGate`,
`intermediateChainGate`) are members of the memory chip's **transition** list; the four
`selectorEquality` families are the whole of its **equality** list
(`GatheredMemoryScalarGates.the_four_scalar_gates_are_retyped`).  Either repair takes each
three-term family to `e` gates (`uncompressed_costs_the_same_and_has_no_collision_event`), so the
transition bucket gains `3·(e-1)` and the equality bucket goes `4 → 4·e`. -/

/-- The inert padding the memory transition bucket already carries. -/
theorem memory_padding_budget (e : ℕ) : RAPPadding.residualTransitionGates e = 3 * e + 2 := rfl

/-- **The transition repair fits inside the existing inert padding, for every `e`,
with `5` slots to spare.**  The `3·(e-1)` new real gates displace inert ones, so the chip's
transition count does not move. -/
theorem memory_transition_repair_fits (e : ℕ) (he : 1 ≤ e) :
    3 * (e - 1) + 5 = RAPPadding.residualTransitionGates e := by
  simp only [RAPPadding.residualTransitionGates]
  omega

/-- **The transition bucket was unchanged at the paper's `24·e + 16`** by the
equality-check repair: the semantic core's three compressed families become `3·e`, and `5` inert
pad gates remain.  Stated over `Thm54Resources.memoryTransitionGatesPaper`: since A-mem-2 the
deployed `Thm54Resources.memoryTransitionGates` is the tree count `26·e + 11` (see
`memory_anchoring_delta` below). -/
theorem memory_transition_bucket_unmoved (e : ℕ) :
    (RAPPadding.memoryCoreTransitionGates e - 3 + 3 * e) + 5
      = Thm54Resources.memoryTransitionGatesPaper e := by
  simp only [RAPPadding.memoryCoreTransitionGates, Thm54Resources.memoryTransitionGatesPaper]
  omega

/-- `Thm54Resources.memoryEqualityChecks` after the repair: four three-term families, each
committed by its `e` coordinates. -/
def memoryEqualityChecksRepaired (e : ℕ) : ℕ := 4 * e

theorem memoryEqualityChecksRepaired_deployed : memoryEqualityChecksRepaired 3 = 12 := by decide

def memoryConstraintsRepaired (e : ℕ) : ℕ :=
  Thm54Resources.memoryTransitionGatesPaper e + Thm54Resources.memoryDegreeOneGatesPaper e
    + Thm54Resources.memoryDegreeThreeGatesPaper e + memoryEqualityChecksRepaired e

theorem memoryConstraintsRepaired_closed (e : ℕ) :
    memoryConstraintsRepaired e = 32 * e + 16 := by
  simp only [memoryConstraintsRepaired, Thm54Resources.memoryTransitionGatesPaper,
    Thm54Resources.memoryDegreeOneGatesPaper, Thm54Resources.memoryDegreeThreeGatesPaper,
    memoryEqualityChecksRepaired]
  omega

/-- **The memory number: `104 → 112`.** -/
theorem memoryConstraintsRepaired_deployed : memoryConstraintsRepaired 3 = 112 := by
  rw [memoryConstraintsRepaired_closed]

/-- **The predicted repair is the landed one**.  This module predicted
`memoryConstraintsRepaired e = 32·e + 16`, i.e. `112` at the deployed degree, against a then-live
`Thm54Resources.memoryConstraints 3 = 104`; the delta was `+8`.  The memory retyping has since
landed, so the two agree — the prediction is now a receipt.  The `+8` is recorded as the numeral
`104 + 8 = 112` it always was. -/
theorem memory_migration_delta :
    memoryConstraintsRepaired 3 = Thm54Resources.memoryTransitionGatesPaper 3
        + Thm54Resources.memoryDegreeOneGatesPaper 3
        + Thm54Resources.memoryDegreeThreeGatesPaper 3
        + memoryEqualityChecksRepaired 3 ∧ 104 + 8 = 112 := by
  refine ⟨rfl, by decide⟩

/-- The memory analogue of
`compute_anchoring_delta`.  The paper-shaped mixed set
(`45·e + 5`) replaces the folded `26·e + 11`. -/
theorem memory_anchoring_delta :
    memoryConstraintsRepaired 3 = 112 ∧ Thm54Resources.memoryConstraints 3 = 156 ∧
      Thm54Resources.memoryTransitionGates 3 = 50 * 3 + 6 := by
  refine ⟨memoryConstraintsRepaired_deployed, ?_, rfl⟩
  rw [Thm54Resources.memoryConstraints_closed]

theorem jx_projection_overcounts_by_six :
    memoryConstraintsRepaired 3 + 6 = 35 * 3 + 13 := by decide

/-! ## 6. The costed answer

Exactly **two** conjuncts of `OptimizedFullCostRealization.exact_resources` move, and both are
equality-check counts:

| conjunct | today | after | paper |
|---|---|---|---|
| `computeTransitionGates 3` | `87` | `87` | the paper unchanged |
| `computeDegreeThreeGates 3` | `3` | `3` | the paper unchanged |
| `computeEqualityChecks` | `2` | `6 = 2·e` | the paper **moves** |
| `C.rap.s` | `98` | `102` | — |
| `memoryTransitionGates 3` | `88` | `88` | the paper unchanged (padding absorbs); **`89` since A-mem-2**, `memory_anchoring_delta` |
| `memoryDegreeThreeGates 3` | `6` | `6` | the paper unchanged; **`12` since the `LU` repair**, same total `12 = 6 + 6` (`Thm54Resources.memory_endpoint_total_unmoved_by_lu`) |
| `memoryEqualityChecks` | `4` | `12 = 4·e` | the paper **moves** |
| `M.rap.s` | `104` | `112` | — |

**Both rows of this table have LANDED.**  The compute "after" column is
therefore the *counterfactual* retyping, retained because `compute_repairs_differ` is what makes
the choice between them a choice.

No column count, round count, commitment bound or row count moves: a challenge is not a column,
and retyping changes a coin's type rather than the number of coins drawn. -/

/-- The whole migration in one arithmetic statement. -/
theorem migration_ledger :
    computeConstraintsRetyped 3 = 102 ∧ memoryConstraintsRepaired 3 = 112 ∧
      Thm54Resources.computeConstraints 3 = 418 ∧ Thm54Resources.memoryConstraints 3 = 156 ∧
      computeEqualityChecksDecompressed = 22 ∧ memoryEqualityChecksRepaired 3 = 4 * 3 ∧
      Thm54Resources.computeTransitionGates 3 = 374 ∧
      Thm54Resources.computeTransitionGatesPaper 3 = 87 ∧
      Thm54Resources.memoryTransitionGatesPaper 3 = 88 ∧
      Thm54Resources.memoryTransitionGates 3 = 156 := by
  refine ⟨computeConstraintsRetyped_deployed, memoryConstraintsRepaired_deployed, ?_, ?_,
    by decide, by decide, ?_, ?_, ?_, ?_⟩
  · rw [Thm54Resources.computeConstraints_closed]
  · rw [Thm54Resources.memoryConstraints_closed]
  · rfl
  · rfl
  · rfl
  · rfl

#print axioms ledger_prediction_is_the_deployed_list
#print axioms paper_equality_checks_reconstructed
#print axioms tree_counters_diverge_from_the_paper
#print axioms compute_decompression_delta
#print axioms compressed_of_decompressed
#print axioms ext_eq_zero_iff_coords
#print axioms dropping_a_coordinate_admits_nonzero
#print axioms decompressedComputeEqualityChecks_length
#print axioms memory_transition_bucket_unmoved
#print axioms migration_ledger

end EqualityCheckLedger
end Nock.NockVMROM.Thm54
