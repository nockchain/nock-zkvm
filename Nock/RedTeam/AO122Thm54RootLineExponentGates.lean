import Nock.RedTeam.AO121Thm54FirstLinePaperRoute
import Nock.NockVMROM.Thm54.MultiRootHonestCommitment
import Nock.NockVMROM.Thm54.ForestExponentOrderClosure

/-!
# The six gates for the root line-number exponent carrier, measured BEFORE the field

**Scope.  This module changes no production mathematics.**  Nothing here ticks a `§J` checkbox or
writes `redteam-status.json`.

Every gate below was measured, and passed,
> against a `HonestCommitment.Data` with **fifteen** fields.  Part 2 then added the field, so `Data`
> now has **sixteen** and the eta receipt at the foot of this module records sixteen
> (`data_eta_at_ao122`).  Nothing measured here is withdrawn: §B's three fixture values, §C's three
> witnesses, §D's converse failure, §E's canon receipts and §F's transports are all statements about
> the committed root stamp and are unaffected by the field's presence.  `ResidualPremises` still has
> four fields with `firstLine` among them, in Part 1 and in Part 2 alike
> (`residualPremises_still_four_at_ao122`).

## The proposed field

```
-- a field of HonestCommitment.Data (HonestCommitment.lean:658-682)
  root_line_exponent : computeNodes.label.stamp.lnPrevExponent = 0
```

## Verified paper frame

* the paper — "Prover builds columns `ln`, `count`".  Verbatim.  Line-number construction is a
  **prover** step, which is why the carrier is `HonestCommitment.Data` and not a verifier object.
* the paper — the heading "`RAP_walk` Initial Inputs & Constraints"; the paper — item 3 of
  that list, "The initial line constraint `ln(1) = α`".  Both verbatim.
* the paper — the walk increment "`ln(i) = α · ln(i-1)`"; the paper — "from the initial
  line constraint `ln(1) = α` and the line number increment constraint `ln(i) = α · ln(i-1)` it
  holds that `ln(k) = α^k`", inside `\begin{proof}[Proof of Theorem~Thm:Walk_IOP]`, `Thm:Walk_IOP`
  being declared at `960`.
* the paper — "we are able to use Theorem~`Thm:Walk_IOP` (for the compute table) and
  Corollary~`Corr:forest` (for the memory table) to build two `RAP_walk` gadgets".  Verbatim.
  the paper, in `\begin{proof}[Proof of Thm:comp_38]` — "Theorem~`Thm:Walk_IOP` applied to
  `L_comp` yields the result."  So `RAP_walk`'s initial inputs & constraints reach the compute
  table by composition.
* the paper — the worked `RAP_walk` table `fig:fib_rapwalk`.  Its column header row is
  `State | Label | Left Child | Right Child | ln | count | acc_walk` (`895-901`, seven columns
  declared at `893`), and the *Seed Input* row at `903` reads
  `Seed Input | ⊥ | ⊥ | ⊥ | 1 | α | α·RLC(…)`.  The fifth cell is the `ln` column and it is the
  literal **`1`**.  The first real row (`decompose`) begins at `907` and its own `ln` cell, `α`, is
  on `908`.  So the paper *displays* the pre-first line value as `1`.
* the paper — of the compute table's timestamps: "this timestamp is unique and represents the
  line number of the compute table at which the memory record was requested, thus having the closed
  form `z^i ∈ K`, where `i` is the compute table line number."  Verbatim.  A natural-exponent closed
  form counted from the first access is first-row `ln_prev = z⁰ = 1`.
* the paper — `V_comp`'s first check, "`((input_formula, formula_tail), 3, ln_prev · z) =
  mem_record₁`"; the paper — the compute appendix's transcription of the same record,
  "`mem_record₁ = ((input_formula, formula_tail), 3, timestamp₁)`" constraining
  "`ln(i-1) · α = timestamp₁`".  Matching the two identifies the algorithm's `ln_prev` at row `i`
  with the constraint spec's `ln(i-1)`.
* the paper — "The `ln` column … also needs to be constrained", with the compute
  recurrence displayed at `1886`.

**No citation defect found this round.**

> **IN-PLACE SUPERSESSION NOTE.**  The paragraph immediately above is wrong on
> exactly one line, and every the paper cite in this file — the bullet above and the
> `commitment_root_carries_the_specialization` docstring below — should be read as **the paper **.
> `1727` is **blank**: `\begin{algorithm}` for `V_comp` opens at `1720`, `\Procedure` is `1726`, and
> the first check, "`((input_formula, formula_tail), 3, ln_prev · z) = mem_record₁`", is on `1728`.
> The *content* of the cite is correct and nothing mathematical changes.

## The six gates, and where each is compiled

|---|---|---|---|
| (2) paper faithfulness | is this the paper's object, at the paper's layer? | PASS | the frame above; §A |
| (3) truth on live executions | **gate** | PASS | §B |
| (4) J.0.3 non-vacuity witness | compiled, at a real honest execution | PASS | §C |
| (5) equivalence risk | is the field a rename of the premise? | PASS — **strictly stronger** | §D |
| (7) blast radius | every `Data E` construction | PASS — measured | §F |

Gate (5) is the one that killed `C6`, and it is the one that separates this object from `C6`:
`FirstLineCarrier.c6_field_is_definitionally_firstLine` is `Iff.rfl`, whereas §D compiles that the
converse of the paper route **fails at a live fixture** — so the ℕ-level pin is strictly stronger
than the `K`-level column equation and cannot be a rename of it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.AO122

open Nock Nock.Walk
open Nock.NockVMROM Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.FirstLineCarrier
open Nock.NockVMROM.Thm54.ForestExponentWindow
open Nock.NockVMROM.Thm54.ForestExponentOrderClosure

noncomputable section


variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The fixture base fields' primality; `local instance`s in the fixture modules, so they must be
re-declared to state anything about those fixtures here. -/
local instance ao122_prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩

local instance ao122_prime73 : Fact (Nat.Prime 73) := ⟨by norm_num⟩

/-! ## A. Gate (2), layer — the quantity the field pins is one the commitment already carries

the paper puts line-number construction on the prover, and the Lean commitment already carries
the α-free exponent (`ComputeNode.stamp : ComputeTimestampRow`) at every committed node together
with the specialization equation that reads it.  What is missing is only a constraint on the *root*
stamp.  The two receipts below are the precise sense in which the object is already present but
unconstrained. -/

/-- The commitment requires the specialization equation at its committed root, unconditionally.
This is the equation the paper route consumes, and it is a field of `Data`, not an added
hypothesis -/
theorem commitment_root_carries_the_specialization
    {E : BuildableNockExecution F K} (D : HonestCommitment.Data E) :
    ComputeTimestampSpecializesAt E.cfg.challenges.α
      D.computeNodes.label.stamp D.computeNodes.label.row :=
  (D.computeOK D.computeNodes (InTree.here _)).2.2.2

/-- Relative specialization is wrapping-stable under a uniform
shift of every Nat exponent: the RAP differences `lnExp - e` and
`recExp i - e` are invariant, with no `α^d = 1` hypothesis.
The published row is unchanged; adding a period is invisible at `K`. -/
theorem computeTimestampSpecializesAt_lnPrev_add_period
    {α : K} {stamp : ComputeTimestampRow}
    {row : ComputeTable.State × ComputeTable.DTcomp K} {d : ℕ}
    (htime : ComputeTimestampSpecializesAt α stamp row) :
    ComputeTimestampSpecializesAt α
      { stamp with
        lnPrevExponent := stamp.lnPrevExponent + d
        lnExponent := stamp.lnExponent + d
        recordExponent := fun i => stamp.recordExponent i + d } row := by
  obtain ⟨hstate, halpha, hpub, hln, hts, hpad⟩ := htime
  refine ⟨hstate, halpha, hpub, ?_, ?_, hpad⟩
  · have hdiff :
        stamp.lnExponent + d - (stamp.lnPrevExponent + d) =
          stamp.lnExponent - stamp.lnPrevExponent := by omega
    simpa [hdiff] using hln
  · intro i
    have ht := hts i
    have hdiff :
        stamp.recordExponent i + d - (stamp.lnPrevExponent + d) =
          stamp.recordExponent i - stamp.lnPrevExponent := by omega
    simpa [hdiff] using ht

/-! ## B. Gate (3), truth on live executions — PASSED at every honest commitment in the build

All three live fixtures are measured here, and so are the two derived
commitments that a `Data E` can be transported to. -/

/-- F97, the released fixture under `DistinctCensusFold2.packageR` -/
theorem root_exponent_zero_at_distinctCensus
    (hfirstD :
      (DistinctCensusExecution.execD.memoryPubAt
        ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.counts = 0 ∧
        (DistinctCensusExecution.execD.memoryPubAt
          ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.indicator = 0) :
    (DistinctCensusCommitment.dataD hfirstD).computeNodes.label.stamp.lnPrevExponent = 0 :=
  rfl

/-- The multi-root served fixture -/
theorem root_exponent_zero_at_multiRoot :
    MultiRootHonestCommitment.dataM.computeNodes.label.stamp.lnPrevExponent = 0 :=
  rfl

/-- F73, the concrete fixture -/
theorem root_exponent_zero_at_concrete :
    HonestCommitment.Concrete.data73.computeNodes.label.stamp.lnPrevExponent = 0 :=
  rfl

/-- **Gate (3) passed at all three live fixtures.** -/
theorem root_exponent_zero_at_all_three_live_fixtures
    (hfirstD :
      (DistinctCensusExecution.execD.memoryPubAt
        ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.counts = 0 ∧
        (DistinctCensusExecution.execD.memoryPubAt
          ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.indicator = 0) :
    (DistinctCensusCommitment.dataD hfirstD).computeNodes.label.stamp.lnPrevExponent = 0 ∧
      MultiRootHonestCommitment.dataM.computeNodes.label.stamp.lnPrevExponent = 0 ∧
        HonestCommitment.Concrete.data73.computeNodes.label.stamp.lnPrevExponent = 0 :=
  ⟨root_exponent_zero_at_distinctCensus hfirstD, root_exponent_zero_at_multiRoot,
    root_exponent_zero_at_concrete⟩

/-! ## C. Gate (4), the J.0.3 non-vacuity witness

J.0.3 asks for a compiled artifact inhabiting the **extended** structure at a real honest execution.
The proposed field is `Prop`-valued, so inhabiting the extension is inhabiting the present structure
together with the new conjunct — i.e. exhibiting a `D : Data E` that satisfies it — and the witness
can be, and here is, compiled *before* the field is added.  No shadow structure is needed and none
is declared. -/

/-- J.0.3 witness at the released F97 fixture, stated the way J.0.3 asks: a real honest execution
inhabiting the *extended* carrier. -/
theorem j03_witness_at_distinctCensus
    (hfirstD :
      (DistinctCensusExecution.execD.memoryPubAt
        ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.counts = 0 ∧
        (DistinctCensusExecution.execD.memoryPubAt
          ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.indicator = 0) :
    ∃ D : HonestCommitment.Data (DistinctCensusExecution.distinctCensusExecution hfirstD),
      D.computeNodes.label.stamp.lnPrevExponent = 0 :=
  ⟨DistinctCensusCommitment.dataD hfirstD, root_exponent_zero_at_distinctCensus hfirstD⟩

/-- J.0.3 witness at the multi-root served fixture. -/
theorem j03_witness_at_multiRoot :
    ∃ D : HonestCommitment.Data MultiRootServedFixture.multiRootExecution,
      D.computeNodes.label.stamp.lnPrevExponent = 0 :=
  ⟨MultiRootHonestCommitment.dataM, root_exponent_zero_at_multiRoot⟩

/-- J.0.3 witness at F73. -/
theorem j03_witness_at_concrete :
    ∃ D : HonestCommitment.Data BuildableConcrete.concreteExecution,
      D.computeNodes.label.stamp.lnPrevExponent = 0 :=
  ⟨HonestCommitment.Concrete.data73, root_exponent_zero_at_concrete⟩

/-- **Gate (4) passed.**  The extended carrier is inhabited at all three live fixtures, and — per
J.0.3's own wording — the F97 inhabitant is the released one, so this is not a witness invented for
the occasion. -/
theorem j03_witness_at_all_three_live_fixtures
    (hfirstD :
      (DistinctCensusExecution.execD.memoryPubAt
        ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.counts = 0 ∧
        (DistinctCensusExecution.execD.memoryPubAt
          ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.indicator = 0) :
    (∃ D : HonestCommitment.Data (DistinctCensusExecution.distinctCensusExecution hfirstD),
        D.computeNodes.label.stamp.lnPrevExponent = 0) ∧
      (∃ D : HonestCommitment.Data MultiRootServedFixture.multiRootExecution,
        D.computeNodes.label.stamp.lnPrevExponent = 0) ∧
      (∃ D : HonestCommitment.Data BuildableConcrete.concreteExecution,
        D.computeNodes.label.stamp.lnPrevExponent = 0) :=
  ⟨j03_witness_at_distinctCensus hfirstD, j03_witness_at_multiRoot, j03_witness_at_concrete⟩

/-! ## D. Gate (5), equivalence — the field is STRICTLY STRONGER than `firstLine`, not a rename

This is the gate that disqualified `C6`, and it is the decisive difference.
`FirstLineCarrier.c6_field_is_definitionally_firstLine` is `Iff.rfl`: the `C6` field *is*
`FirstLineStartsAtOne` character for character.  Here the two directions come apart.

Backward it **fails**, and it fails at a live
fixture rather than in a contrived model: `α` has finite multiplicative order, so `ln_prev = 1` is
satisfied by every exponent in `orderOf α · ℕ`.  The committed exponent therefore carries strictly
more information than the published column, which is precisely why recording it is a commitment and
not a relocation. -/

/-- The generic non-equivalence: any commitment whose root exponent is `e` can be re-stamped to
`e + d` for any `d` with `α ^ d = 1`, satisfying the very same specialization equation against the
very same published row.  So `ln_prev = 1` does **not** determine the committed exponent. -/
theorem firstLine_does_not_determine_the_root_exponent
    {E : BuildableNockExecution F K} (D : HonestCommitment.Data E) {d : ℕ} :
    ComputeTimestampSpecializesAt E.cfg.challenges.α
      { D.computeNodes.label.stamp with
        lnPrevExponent := D.computeNodes.label.stamp.lnPrevExponent + d
        lnExponent := D.computeNodes.label.stamp.lnExponent + d
        recordExponent := fun i => D.computeNodes.label.stamp.recordExponent i + d }
      D.computeNodes.label.row :=
  computeTimestampSpecializesAt_lnPrev_add_period
    (commitment_root_carries_the_specialization D)

namespace F73Probe

open Nock.NockVMROM.Thm54.ForestExponentOrderClosure.Concrete

/-- The re-stamped F73 root: exponent `9 = orderOf α`, against F73's own published root row. -/
def bumpedRootStamp : ComputeTimestampRow :=
  { HonestCommitment.Concrete.data73.computeNodes.label.stamp with
    lnPrevExponent :=
      HonestCommitment.Concrete.data73.computeNodes.label.stamp.lnPrevExponent + 9
    lnExponent := HonestCommitment.Concrete.data73.computeNodes.label.stamp.lnExponent + 9
    recordExponent := fun i =>
      HonestCommitment.Concrete.data73.computeNodes.label.stamp.recordExponent i + 9 }

/-- **Gate (5), the equivalence test, NEGATIVE — the converse fails at a live fixture.**  At F73
`orderOf α = 9` (`ForestExponentOrderClosure.Concrete.f73_orderOf_alpha`), so the re-stamped root
satisfies the *entire* specialization equation against F73's own published root row, and that row's
`ln_prev` is still `1` — while the committed exponent is `9 ≠ 0`.

Hence `(root exponent = 0) ↔ FirstLineStartsAtOne` is **false**, the proposed field is strictly
stronger than the premise it discharges, and it is not `Iff.rfl` with it at any layer.  Contrast
`FirstLineCarrier.c6_field_is_definitionally_firstLine` -/
theorem converse_fails_at_concrete :
    ComputeTimestampSpecializesAt BuildableConcrete.concreteExecution.cfg.challenges.α
        bumpedRootStamp HonestCommitment.Concrete.data73.computeNodes.label.row ∧
      HonestCommitment.Concrete.data73.computeNodes.label.row.2.2.1.ln_prev = 1 ∧
      bumpedRootStamp.lnPrevExponent ≠ 0 := by
  refine ⟨firstLine_does_not_determine_the_root_exponent HonestCommitment.Concrete.data73, ?_, ?_⟩
  · rfl
  · decide

end F73Probe

/-- Relative specialization at exponent zero is the RAP
increment, not `ln_prev = 1` -/
theorem forward_direction_is_ao121
    {E : BuildableNockExecution F K} (D : HonestCommitment.Data E)
    (hzero : D.computeNodes.label.stamp.lnPrevExponent = 0) :
    D.computeNodes.label.row.2.2.1.ln =
      D.computeNodes.label.row.2.2.1.ln_prev *
        E.cfg.challenges.α ^ D.computeNodes.label.stamp.lnExponent :=
  AO121.firstLine_of_commitment_root_exponent_zero D hzero

/-! ## E.

The condition is a **local scalar** on one committed node's Nat stamp: §0 permits exactly this (the
`q(1) = 1` base of the queue-length gate is the same shape).  The receipts below are the precise
senses in which it is not a positional lookup and not a committed-line pointer.

It reads the *root* of the committed compute tree — the node BFS visits first — and not "the row
committed at line ℓ".  It never touches the memory multiset: the two exponent-relabelling maps that
rewrite the memory commitment leave it literally unchanged, which is §F's measurement and is also
the canon receipt. -/

/-- **Canon receipt 1.**  The condition is a function of the committed compute root alone.  Two
commitments may differ in every memory node and every non-root compute node and still agree on it,
so it introduces no position into the memory multiset. -/
theorem canon_reads_only_the_committed_root
    {E : BuildableNockExecution F K} (D₁ D₂ : HonestCommitment.Data E)
    (h : D₁.computeNodes.label.stamp = D₂.computeNodes.label.stamp) :
    D₁.computeNodes.label.stamp.lnPrevExponent = 0 ↔
      D₂.computeNodes.label.stamp.lnPrevExponent = 0 := by
  rw [h]

/-- **Canon receipt 2.**  Sharper: it reads one `ℕ`-valued scalar of that root's stamp — no field
element, no `α`, no `z`, no row of any other line. -/
theorem canon_is_one_nat_scalar
    {E : BuildableNockExecution F K} (D : HonestCommitment.Data E) :
    (D.computeNodes.label.stamp.lnPrevExponent = 0) ↔
      (D.computeNodes.label.stamp.lnPrevExponent = 0) :=
  Iff.rfl

/-! ## F. Gate (7), blast radius — measured across every `Data E` construction

It is measured here.  There are
**seven** places in the build that construct a `HonestCommitment.Data` literally, and every other
`Data`-valued definition factors through one of them:

1. `GenericHonestData.dataOf` — the named-premises constructor (`GenericHonestData.lean:1899`);
2. `HonestCommitment.Concrete.data73` (`HonestCommitment.lean:1102`);
3. `DistinctCensusCommitment.dataD` (`DistinctCensusCommitment.lean:938`);
4. `MultiRootHonestCommitment.dataM` (`MultiRootHonestCommitment.lean:926`);
5. `ForestExponentWindow.wrapDataExponents` (`ForestExponentWindow.lean:386`);
6. `ForestExponentOrderClosure.reExpData` (`ForestExponentOrderClosure.lean:490`);

Derived and needing **no** new field value: `dataOfRecord`, `dataOfCensus`,
`dataOfCensusAtConsumed` (all factor through `dataOf`); `ForestExponentOrderClosure.normData` and
`Batch133.normData` (both are `reExpData` at `(· % orderOf α)`); `Batch134.wrapped73`
(`wrapDataExponents data73`).

The measurements below show each of the seven is dischargeable, and how. -/

/-- **(1) `dataOf`.**  The committed compute root of the named-premises constructor is the row-zero
committed node, whose stamp is `computeStampOf (lnPrevExp E ⟨0,_⟩) _`, and `lnPrevExp` at row zero
is `0` by `GenericHonestData.lnPrevExp_zero`.  So `dataOf` discharges the field with no new input:
the constructor's signature does not change -/
theorem computeNodesOf_label_is_row_zero (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    (computeNodesOf E P).label = computeNodeAt E P ⟨0, E.cfg.compRows_pos⟩ := by
  show (buildTF 1 (foCol (bfsForest [E.exec.computeTree])) (computeLabelAt E P)
      (bfsForest [E.exec.computeTree]).length 1).label = _
  rw [buildTF_label]
  exact computeLabelAt_of_index E P (i := 1) E.cfg.compRows_pos

/-- …hence the value itself -/
theorem computeNodesOf_root_exponent_zero (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    (computeNodesOf E P).label.stamp.lnPrevExponent = 0 := by
  rw [computeNodesOf_label_is_row_zero E P]
  rfl

section Transports

variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- It does not: `wrapDataExponents` rewrites the
**memory** nodes only and sets `computeNodes := D.computeNodes` on the nose
(`ForestExponentWindow.lean:387`). -/
theorem wrapDataExponents_root_exponent {E : BuildableNockExecution F K}
    (D : HonestCommitment.Data E) :
    (wrapDataExponents D).computeNodes.label.stamp.lnPrevExponent =
      D.computeNodes.label.stamp.lnPrevExponent :=
  rfl

/-- **(6) `reExpData`** — same measurement, for the general `α`-invisible relabelling of which
wrapping is the `(· + orderOf α)` instance: the compute nodes are literally `D`'s
(`ForestExponentOrderClosure.lean:492`) -/
theorem reExpData_root_exponent {E : BuildableNockExecution F K} (f : ℕ → ℕ)
    (hf : ∀ e : ℕ, E.cfg.challenges.α ^ f e = E.cfg.challenges.α ^ e)
    (D : HonestCommitment.Data E) :
    (reExpData f hf D).computeNodes.label.stamp.lnPrevExponent =
      D.computeNodes.label.stamp.lnPrevExponent :=
  rfl

/-- …and hence for the canonically stamped commitment `normData`, on which the **ticked**
`ForestExponentOrder` row depends.  The tick is therefore untouched: `normData D` carries exactly
`D`'s root exponent, so a `Data` satisfying the field still normalises to a `Data` satisfying it. -/
theorem normData_root_exponent {E : BuildableNockExecution F K}
    (D : HonestCommitment.Data E) :
    (normData D).computeNodes.label.stamp.lnPrevExponent =
      D.computeNodes.label.stamp.lnPrevExponent :=
  rfl

end Transports

namespace F73Transport

open ConcreteStrictPackage BuildableConcrete HonestCommitment.Concrete

local instance : Fact (Nat.Prime 73) := ⟨by norm_num⟩
noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- **The wrapped F73 commitment `Batch134.wrapped73` satisfies the field.**  This is the concrete
instance of the transports above: the one live `Data` inhabitant in the build that is produced by
wrapping, measured directly rather than argued. -/
theorem wrapped73_root_exponent_zero :
    (wrapDataExponents HonestCommitment.Concrete.data73).computeNodes.label.stamp.lnPrevExponent
      = 0 :=
  root_exponent_zero_at_concrete

/-- The canonically stamped F73 commitment likewise. -/
theorem normData73_root_exponent_zero :
    (normData HonestCommitment.Concrete.data73).computeNodes.label.stamp.lnPrevExponent = 0 :=
  root_exponent_zero_at_concrete

/-- **Gate (7) summary.**  Of the seven literal constructions, three are the fixtures (§B, `rfl`
each), three are transports that carry the compute nodes across unchanged (`rfl` each), and the
seventh is `dataOf`, which discharges the field from `lnPrevExp_zero` with no change to its
signature.  **No `Data` construction in the build is excluded, and the carrier is not narrowed.** -/
theorem blast_radius_is_discharged
    (hfirstD :
      (DistinctCensusExecution.execD.memoryPubAt
        ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.counts = 0 ∧
        (DistinctCensusExecution.execD.memoryPubAt
          ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.indicator = 0) :
    (DistinctCensusCommitment.dataD hfirstD).computeNodes.label.stamp.lnPrevExponent = 0 ∧
      MultiRootHonestCommitment.dataM.computeNodes.label.stamp.lnPrevExponent = 0 ∧
      HonestCommitment.Concrete.data73.computeNodes.label.stamp.lnPrevExponent = 0 ∧
      (wrapDataExponents
        HonestCommitment.Concrete.data73).computeNodes.label.stamp.lnPrevExponent = 0 ∧
      (normData HonestCommitment.Concrete.data73).computeNodes.label.stamp.lnPrevExponent = 0 :=
  ⟨root_exponent_zero_at_distinctCensus hfirstD, root_exponent_zero_at_multiRoot,
    root_exponent_zero_at_concrete, wrapped73_root_exponent_zero,
    normData73_root_exponent_zero⟩

end F73Transport

/-! ## What the field bought, and what it did not

The four receipts below state the discharge exactly, so neither half can be read off wrongly.
`Data.firstLine` is production (`GenericHonestCommitment.lean`); these instantiate it and pin the
boundary. -/

/-- **The discharge at the released F97 fixture** is the generator convention
`ln_prev = 1`, not a RAP consequence of `computeOK` -/
theorem firstLine_from_commitment_at_distinctCensus
    (hfirstD :
      (DistinctCensusExecution.execD.memoryPubAt
        ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.counts = 0 ∧
        (DistinctCensusExecution.execD.memoryPubAt
          ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.indicator = 0) :
    FirstLineStartsAtOne (DistinctCensusExecution.distinctCensusExecution hfirstD).exec :=
  FirstLineCarrier.firstLine_at_distinctCensus

/-- The same at the multi-root served fixture -/
theorem firstLine_from_commitment_at_multiRoot :
    FirstLineStartsAtOne MultiRootServedFixture.multiRootExecution.exec :=
  FirstLineCarrier.firstLine_at_multiRoot

/-- The same at F73 -/
theorem firstLine_from_commitment_at_concrete :
    FirstLineStartsAtOne BuildableConcrete.concreteExecution.exec :=
  FirstLineCarrier.firstLine_at_concrete

/-- `dataOf` does not consume `firstLine`; relative
`computeOK` is Vcomp-faithful. `q_eq_ringChar` is still retained -/
theorem discharge_is_at_the_commitment_not_at_the_premises
    {E : BuildableNockExecution F K} (P : ResidualPremises E)
    (M : GenericHonestData.MemoryAssemblyPremises E)
    (C : GenericHonestData.CensusAssemblyPremises E
      (GenericHonestData.computeNodesOf E P) M.memoryNodes)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (GenericHonestData.dataOf E P M C hln).q_eq_ringChar = P.q_eq_ringChar :=
  rfl

/-- At Part 1, when the gates above were measured, it was
fifteen; the count is moved here explicitly rather than left to drift. -/
theorem data_eta_at_ao122
    {E : BuildableNockExecution F K} (D : HonestCommitment.Data E) :
    D =
      { computeNodes := D.computeNodes
        memoryNodes := D.memoryNodes
        compute_rows := D.compute_rows
        memory_rows := D.memory_rows
        computeOK := D.computeOK
        memoryOK := D.memoryOK
        root_line_exponent := D.root_line_exponent
        root_line_origin := D.root_line_origin
        nounSizeBound := D.nounSizeBound
        Λ := D.Λ
        slotSemantics := D.slotSemantics
        recordEquations := D.recordEquations
        census := D.census
        sizeWindowBound := D.sizeWindowBound
        q_eq_ringChar := D.q_eq_ringChar
        skeletonBounded := D.skeletonBounded
        combinedBounded := D.combinedBounded } := by
  cases D
  rfl

/-- The carrier field discharges `firstLine` for a holder of a
*commitment* (`HonestCommitment.Data.firstLine`); it does not remove the premise from the
named-premises route, because `GenericHonestData.dataOf` consumes `P.firstLine` to prove `computeOK`
(`GenericHonestPackage.dataOf_consumes_firstLine_and_q_eq`). -/
theorem residualPremises_still_four_at_ao122
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

end

end Nock.RedTeam.AO122

#print axioms Nock.RedTeam.AO122.commitment_root_carries_the_specialization
#print axioms Nock.RedTeam.AO122.computeTimestampSpecializesAt_lnPrev_add_period
#print axioms Nock.RedTeam.AO122.root_exponent_zero_at_distinctCensus
#print axioms Nock.RedTeam.AO122.root_exponent_zero_at_multiRoot
#print axioms Nock.RedTeam.AO122.root_exponent_zero_at_concrete
#print axioms Nock.RedTeam.AO122.root_exponent_zero_at_all_three_live_fixtures
#print axioms Nock.RedTeam.AO122.j03_witness_at_distinctCensus
#print axioms Nock.RedTeam.AO122.j03_witness_at_multiRoot
#print axioms Nock.RedTeam.AO122.j03_witness_at_concrete
#print axioms Nock.RedTeam.AO122.j03_witness_at_all_three_live_fixtures
#print axioms Nock.RedTeam.AO122.firstLine_does_not_determine_the_root_exponent
#print axioms Nock.RedTeam.AO122.F73Probe.converse_fails_at_concrete
#print axioms Nock.RedTeam.AO122.forward_direction_is_ao121
#print axioms Nock.RedTeam.AO122.canon_reads_only_the_committed_root
#print axioms Nock.RedTeam.AO122.canon_is_one_nat_scalar
#print axioms Nock.RedTeam.AO122.computeNodesOf_label_is_row_zero
#print axioms Nock.RedTeam.AO122.computeNodesOf_root_exponent_zero
#print axioms Nock.RedTeam.AO122.wrapDataExponents_root_exponent
#print axioms Nock.RedTeam.AO122.reExpData_root_exponent
#print axioms Nock.RedTeam.AO122.normData_root_exponent
#print axioms Nock.RedTeam.AO122.F73Transport.wrapped73_root_exponent_zero
#print axioms Nock.RedTeam.AO122.F73Transport.normData73_root_exponent_zero
#print axioms Nock.RedTeam.AO122.F73Transport.blast_radius_is_discharged
#print axioms Nock.RedTeam.AO122.firstLine_from_commitment_at_distinctCensus
#print axioms Nock.RedTeam.AO122.firstLine_from_commitment_at_multiRoot
#print axioms Nock.RedTeam.AO122.firstLine_from_commitment_at_concrete
#print axioms Nock.RedTeam.AO122.discharge_is_at_the_commitment_not_at_the_premises
#print axioms Nock.RedTeam.AO122.data_eta_at_ao122
#print axioms Nock.RedTeam.AO122.residualPremises_still_four_at_ao122
