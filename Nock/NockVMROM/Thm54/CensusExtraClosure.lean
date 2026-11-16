import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.DistinctCensusExecution
import Nock.NockVMROM.Thm54.BelowDefs.CensusExtraClosure

/-!
# The five `CensusRecordPremises` extras, measured

Nothing here weakens a census predicate, adds a carrier field, or ticks a §J checkbox.

**§F is the part with a positive result, and its scope is stated up front.**  Two of the
five extras — `sizeWindowBound` and `slotSemantics` — need **no carrier at all** at any execution
that avoids the opcodes gating them, because `SizeWindowCounting.requiredSizeWindowNouns` is empty
off `{.s3, .s4, .s6}` and both clauses of `ServedLookupBridge.SkeletonSlotSemantics` are gated on
`{.s0, .s9}`.  Read the three scope words literally:

* **generic** — `sizeWindowBound_of_no_window_states` and `slotSemantics_of_no_lookup_states` hold
  for every `F`, `K`, `E`, `P`, `M`;
* **state-gated** — each carries its opcode-avoidance hypothesis *in the statement*, and the gate is
  load-bearing, not decorative (`census_holds_and_sizeWindowBound_fails`,
  `s0SlotFailRow_slotSemantics_fails`).  Neither extra is closed **generically**;
* **fixture-level** — at the released F97 `(distinctCensusExecution hfirstD)` the gates are *discharged*
  (`.s5, .s1, .s1`), so with §B.0's `skeletonBounded`/`combinedBounded` **four of the five fields hold
  there with no carrier**.  This is a statement about that fixture, not about executions in general.

Everything in §F is over the **reconstruction** `skeletonOfNodes (computeNodesOf E P)
(memoryNodesOf E M)` — the object `CensusRecordPremises` quantifies over — and never over the
hand-built `skelD` of `DistinctCensusCommitment`.

The fifth field, `census`, **remains open** and is the only one:
`distinctCensus_censusRecordPremises_of_census` takes it as its sole hypothesis and returns the whole
bundle.  It needs the carrier program's `C2`, the paper's `NockProgram^Λ` leaf window
(`Def[Nock Program]`).  Nothing in §F bears
on it.

## §A. `skeletonBounded` — reduced to three paper constraints, and `combinedBounded` with it

The earlier recorded description ("atom-range `BoundedBy q` on the reconstructed compute-row
`decompNoun` slots") is **accurate**, and `GenericHonestData.skeletonBounded_of_decomp_bounds`
already discharges everything else.  What that description does not say is that the paper supplies
the mechanism, and this section supplies it.

`Lem:decomp` is exactly boundedness inheritance along `cons`: for a valid
noun `n ∈ 𝒩^λ(𝔽)`, `n = cons(n_L, n_R)` holds **iff** `n_L ∈ 𝒩^{λ_L}(𝔽)`, `n_R ∈ 𝒩^{λ_R}(𝔽)` and
`λ = λ_L + λ_R`.  In Lean that is `FieldEmbedding.BoundedBy_cell`, already a `simp` lemma.  So the
only thing standing between the already-held bound on `root.formula` and every active `decompNoun`
slot is the *structural* `cons` equation — and Algorithm `NockCompute` states all three of them,
gated at exactly the opcode sets `SemanticStrategy.decActive` uses:

* `f = cons(f_h, f_t)` is **always operative**;
* `cons(f_th, f_tt) = f_t` under `∑_{i ∈ {2,5,6,7,8,9}} op_i = 1`, which is
  `SemanticStrategy.hasTailDecomposition`, i.e. `decActive · .f_th` verbatim;
* `cons(f_tth, f_ttt) = f_tt` under `op_6 = 1`, which is
  `decActive · .f_tth` verbatim.

`ConsDecomposedRow` is the noun-level reflection of those three constraints and nothing else.  With
it, `skeletonBounded` is a theorem (`skeletonBounded_of_consDecomposed`), and therefore so is
`combinedBounded` (`combinedBounded_of_consDecomposed`), which the earlier analysis had already reduced to
`skeletonBounded` plus `11 < ringChar K`.

`ConsDecomposedRow` is a new named object, not a field of `BuildableNockExecution`; the four census
extras are unchanged, `censusRecordPremises_still_five` still holds, and no capstone moves. The
reduction is not circular: `consDecomposed_not_implied_by_bounds` separates the new object from its
conclusion at the free-skeleton layer (a bounded row need not be `cons`-decomposed). Why the
constraint is not *already* derivable inside `ComputeRowSemanticData`: `Vcomp` states
`f = cons(f_h, f_t)` between **fingerprints**, and reflecting a fingerprint equation to a noun
equation needs `OpcodeSemantics.PairFaithful`, whose `right_bounded` field is the very bound being
sought (`consReflection_is_circular_without_a_bound`).

## §B. `sizeWindowBound` — the recorded missing hypothesis is the wrong kind of bound

The earlier route records the missing hypothesis as "exactly `orderOf z ≤ Λ + 1`", with
`sizeWindowBound_of_SizeWindow_and_order_le_succ_Lambda` as the bridge.  That bridge is sound and is
not withdrawn, but the description is **not accurate** as a statement of what is missing:

1. It is *sufficient*, not necessary.  `SizeWindowCounting.SizeWindowNounsBoundedBy S Λ` is
   `∀ n ∈ skeletonSizeWindowNouns S, n.leaves ≤ Λ` — a purely combinatorial statement in which `z`
   does not occur (`sizeWindowBound_is_seed_free`).
2. It is an **upper** bound on the order of the NPR seed where the paper's regime forces a very
   large one.  With `SizeWindow` on a window noun of `Λ` leaves it pins the order exactly:
   `orderOf z = Λ + 1` (`sizeWindow_route_pins_the_order`).  The paper instantiates `Λ = 2^7` at
   `|𝕂| ≈ 2^192` and asks for `Λ, k ∈ negl(|𝕂|)`, i.e. the opposite regime.
3. It is **false at the live released fixture**.  `DistinctCensusExecution.(distinctCensusExecution hfirstD)`
   is the execution under `DistinctCensusFold2.packageR`; there `z = 8`, `orderOf z = 16` and
   `Λ = 7`, so `orderOf z ≤ Λ + 1` fails (`order_le_succ_Lambda_false_at_distinctCensus`).  The
   residual gap is exhibited, not just asserted: an eight-leaf noun satisfies `SizeWindow` at that
   seed and violates `n.leaves ≤ Λ` (`sizeWindow_gap_at_distinctCensus`).

The honest missing object is the paper's own leaf window, `NockProgram^Λ` — programs "of length
`λ ≤ Λ`" (`Def[Nock Program]`), which
`Corr:ion_single_security` then consumes as "a list of nouns of length at most `Λ`"
.  The ledger cite the paper is the **consumer**, not the definition.

## §C. Why no already-held object reaches it

`E.Λ` occurs in exactly one field of the whole carrier: `SemanticTrace.ComputeRowSemanticData`'s
`comparison_leaves`, on the **free** `comparisons` list.  `ServedMemoryTrace.ExactServedMemoryTrace`
takes `Λ` only as an inert type parameter and never mentions it in a field.  So every route to a
`Λ`-leaf bound must go through that list — and for `sizeWindowBound` even a *complete* identification
of that list with the reconstructed `P8Census.skeletonComparisons` would not suffice: at OP3 and OP4
the required size-window noun occurs only under `Noun.wut` / `incMod`, and at OP6 it does not occur
at all (`sizeWindowNoun_absent_from_s6_comparisons`).  The independence is witnessed uniformly, not
at a degenerate pole: `census_holds_and_sizeWindowBound_fails` is an OP6 skeleton on which
`CombinedSkeletonCensus` holds at `Λ = 2` while `SizeWindowNounsBoundedBy` fails at every `Λ < 4`.

## §D. `slotSemantics` and `census` — recorded descriptions confirmed

The earlier description is **accurate**: the missing object is identification of a served lookup with
the reconstructed skeleton's subject / `mr2`-axis / evaluation (and the OP9 analogue).
`SemanticTrace.RowStateNeeds` has exactly two fields, `served` and `served_count`, and neither ties
a served lookup to the row's own memory records (`rowStateNeeds_eta_two_fields`).
`ServedMemoryTrace.ExactServedMemoryTrace.semanticCoverage` does not supply it either: it maps a
`needs.served` entry to a `Service` carrying the *same* `record`/`root`/`child`/`axis` tuple, so it
is an identity on exactly the four components the identification is about.

The base
case is in the paragraph at the paper, the operator `\(n_2,n_1)` is at the paper, and the
child-axis relation is the display the paper with its body at `1292-1294`. The §J.2
range `1288-1291` does contain the base case and is not wrong; the component cite `1289` is.

The earlier description is **accurate as far as it goes**, with one correction: `census` is not
reducible to a proper sub-object, because `EdgeComparisonCensus.CombinedSkeletonCensus` *is* the
the paper leaf window applied to the reconstructed census list.  The `Λ`-window narrowing that
§A's `cons` object does buy is recorded as `censusDecompSlots_of_consDecomposed`: under the same
three paper constraints every active `decompNoun` slot inherits the row formula's leaf bound, by the
`λ = λ_L + λ_R` half of `Lem:decomp`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.CensusExtraClosure

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.HonestCommitment

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## §A. The paper's `cons` constraints, and `skeletonBounded` from them -/

/-- **The three always-listed `cons` constraints of Algorithm `NockCompute`, at the noun layer.**

Field by field: `formula_cons` is `f = cons(f_h, f_t)`, the constraint the paper calls always
operative; `tail_cons` is `cons(f_th, f_tt) = f_t`, gated by
`∑_{i ∈ {2,5,6,7,8,9}} op_i = 1`; `branchTail_cons` is
`cons(f_tth, f_ttt) = f_tt`, gated by `op_6 = 1`.  The two gates are
`SemanticStrategy.decActive · .f_th` and `decActive · .f_tth` verbatim, by
`SemanticStrategy.decActive_cases`.

This is a structural noun equation only.  It states no atom range and no leaf count. -/

structure ConsDecomposedRow {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) : Prop where
  formula_cons :
    data.root.formula = .cell (decompNoun data .f_h) (decompNoun data .f_t)
  tail_cons :
    ∀ _ : decActive row.1 .f_th = true,
      decompNoun data .f_t =
        .cell (decompNoun data .f_th) (decompNoun data .f_tt)
  branchTail_cons :
    ∀ _ : decActive row.1 .f_tth = true,
      decompNoun data .f_tt =
        .cell (decompNoun data .f_tth) (decompNoun data .f_ttt)

namespace ConsDecomposedRow

variable {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
  {data : ComputeRowSemanticData q Λ row}

/-- The row formula is already a bounded realized noun: it is listed in `realizedNouns` and
`ComputeRowSemanticData.bounded` covers that list.  No premise is used. -/

theorem formula_bounded (data : ComputeRowSemanticData q Λ row) :
    FieldEmbedding.BoundedBy q data.root.formula :=
  data.bounded _ data.formula_mem

/-- `f_h` and `f_t` are bounded: `Lem:decomp` applied to the always-operative
`f = cons(f_h, f_t)`. -/

theorem head_tail_bounded (hc : ConsDecomposedRow data) :
    FieldEmbedding.BoundedBy q (decompNoun data .f_h) ∧
      FieldEmbedding.BoundedBy q (decompNoun data .f_t) := by
  have hf := formula_bounded data
  rw [hc.formula_cons] at hf
  exact hf

/-- **The reduction, per slot.**  Every state-active decomposition slot is bounded. -/

theorem decompNoun_bounded (hc : ConsDecomposedRow data)
    (slot : DecSlot) (hact : decActive row.1 slot = true) :
    FieldEmbedding.BoundedBy q (decompNoun data slot) := by
  obtain ⟨hh, ht⟩ := head_tail_bounded hc
  have htail :
      ∀ _ : decActive row.1 .f_th = true,
        FieldEmbedding.BoundedBy q (decompNoun data .f_th) ∧
          FieldEmbedding.BoundedBy q (decompNoun data .f_tt) := by
    intro hth
    have := ht
    rw [hc.tail_cons hth] at this
    exact this
  cases slot with
  | f_h => exact hh
  | f_t => exact ht
  | f_th => exact (htail hact).1
  | f_tt => exact (htail ((f_tt_active_iff_f_th row.1).mp hact)).2
  | f_tth =>
      have hth : decActive row.1 .f_th = true := by
        have h6 := (decActive_cases row.1).2.2.2.2.1.mp hact
        exact (decActive_cases row.1).2.2.1.mpr (by simp [h6])
      have h2 := (htail hth).2
      rw [hc.branchTail_cons hact] at h2
      exact h2.1
  | f_ttt =>
      have htth : decActive row.1 .f_tth = true :=
        (f_ttt_active_iff_f_tth row.1).mp hact
      have hth : decActive row.1 .f_th = true := by
        have h6 := (decActive_cases row.1).2.2.2.2.1.mp htth
        exact (decActive_cases row.1).2.2.1.mpr (by simp [h6])
      have h2 := (htail hth).2
      rw [hc.branchTail_cons htth] at h2
      exact h2.2

/-- **`Lem:decomp`'s leaf half**: the same three constraints
propagate the row formula's leaf bound to every active decomposition slot.  This is the `Λ`-window
narrowing §C refers to; it is *not* an inhabitation of `census`. -/

theorem decompNoun_leaves_le (hc : ConsDecomposedRow data) {Λ' : ℕ}
    (hf : data.root.formula.leaves ≤ Λ')
    (slot : DecSlot) (hact : decActive row.1 slot = true) :
    (decompNoun data slot).leaves ≤ Λ' := by
  rw [hc.formula_cons] at hf
  simp only [Noun.leaves] at hf
  have hh : (decompNoun data .f_h).leaves ≤ Λ' := by omega
  have ht : (decompNoun data .f_t).leaves ≤ Λ' := by omega
  have htail :
      ∀ _ : decActive row.1 .f_th = true,
        (decompNoun data .f_th).leaves ≤ Λ' ∧
          (decompNoun data .f_tt).leaves ≤ Λ' := by
    intro hth
    have h := ht
    rw [hc.tail_cons hth] at h
    simp only [Noun.leaves] at h
    omega
  cases slot with
  | f_h => exact hh
  | f_t => exact ht
  | f_th => exact (htail hact).1
  | f_tt => exact (htail ((f_tt_active_iff_f_th row.1).mp hact)).2
  | f_tth =>
      have hth : decActive row.1 .f_th = true := by
        have h6 := (decActive_cases row.1).2.2.2.2.1.mp hact
        exact (decActive_cases row.1).2.2.1.mpr (by simp [h6])
      have h2 := (htail hth).2
      rw [hc.branchTail_cons hact] at h2
      simp only [Noun.leaves] at h2
      omega
  | f_ttt =>
      have htth : decActive row.1 .f_tth = true :=
        (f_ttt_active_iff_f_tth row.1).mp hact
      have hth : decActive row.1 .f_th = true := by
        have h6 := (decActive_cases row.1).2.2.2.2.1.mp htth
        exact (decActive_cases row.1).2.2.1.mpr (by simp [h6])
      have h2 := (htail hth).2
      rw [hc.branchTail_cons htth] at h2
      simp only [Noun.leaves] at h2
      omega

end ConsDecomposedRow

/-- **`skeletonBounded` from the three paper `cons` constraints.**  Everything else is already
derived: `GenericHonestData.skeletonBounded_of_decomp_bounds` supplies the memory rows, the memory
trees, the root triple and the subformula slots, and the earlier analysis left exactly the decomposition slots.

This is a reduction, not an inhabitation: `ConsDecomposedRow` is a hypothesis, not a carrier field,
and `CensusRecordPremises` still has its five fields. -/

theorem skeletonBounded_of_consDecomposed (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (hc : ∀ i : Fin E.cfg.compRows, ConsDecomposedRow (E.semanticData.rows i)) :
    (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q where
  computeRows := by
    rw [List.forall_iff_forall_mem]
    intro s hs
    rw [computeSkeletonRows_of_assembly E P M] at hs
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs
    rw [List.mem_range'] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    simp only [Nat.one_mul]
    have hidx : k < E.cfg.compRows := by
      rw [← E.exec.compute_bfs_length]
      exact hk
    have hlbl : computeLabelAt E P (1 + k) = computeNodeAt E P ⟨k, hidx⟩ := by
      have h1 : (1 + k) - 1 = k := Nat.add_sub_cancel_left 1 k
      simpa [h1] using computeLabelAt_of_index E P (i := 1 + k) (by simpa [h1] using hidx)
    rw [hlbl, computeNodeAt, computeNodeOf]
    exact computeSkeletonOf_bounded_of_decomp (E.semanticData.rows ⟨k, hidx⟩)
      (publicRowNoun_of_execution E ⟨k, hidx⟩)
      (fun slot hact => (hc ⟨k, hidx⟩).decompNoun_bounded slot hact)
  memoryRows := memorySkeletonRows_bounded E P M
  memoryTrees := memoryTrees_bounded E P M

/-- **`combinedBounded` becomes fully derived.**  The earlier analysis reduced `combinedBounded` to
`skeletonBounded` plus the consumed characteristic bound; with §A that leaves only the paper `cons`
constraints.  Two of the five `CensusRecordPremises` fields therefore rest on one object. -/

theorem combinedBounded_of_consDecomposed (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (hc : ∀ i : Fin E.cfg.compRows, ConsDecomposedRow (E.semanticData.rows i))
    (hgt : 11 < ringChar K) :
    ProductionP8Containment.CombinedBoundedBy K E.q
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) :=
  combinedBounded_of_skeletonBounded_at_consumed_q E P M
    (skeletonBounded_of_consDecomposed E P M hc) hgt

/-- Both fields at once, in the shape `censusAssemblyOf` consumes them. -/

theorem skeletonBounded_and_combinedBounded_of_consDecomposed
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (hc : ∀ i : Fin E.cfg.compRows, ConsDecomposedRow (E.semanticData.rows i))
    (hgt : 11 < ringChar K) :
    (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q ∧
      ProductionP8Containment.CombinedBoundedBy K E.q
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) :=
  ⟨skeletonBounded_of_consDecomposed E P M hc,
    combinedBounded_of_consDecomposed E P M hc hgt⟩

/-! ### §A.1 The reduction is not circular, and the constraint is not already reflected -/

/-- So the
fingerprint constraint cannot be turned into a noun equation on the way to the bound. -/

theorem consReflection_is_circular_without_a_bound {z : K} {q : ℕ} {f h t : Noun}
    (hpf : OpcodeSemantics.PairFaithful z q f (.cell h t)) :
    FieldEmbedding.BoundedBy q h ∧ FieldEmbedding.BoundedBy q t :=
  hpf.right_bounded

/-- A bounded compute-row skeleton whose formula is *not* the `cons` of its two first-level
decomposition slots.  Stated at the `ComputeRowSkeleton` layer, which is the layer
`SemanticSkeleton.BoundedBy` quantifies over — not at an idealized noun layer. -/

def notConsRow : ComputeRowSkeleton where
  state := .s1
  subject := .atom 0
  formula := .atom 0
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 1⟩

/-- **`ConsDecomposedRow` is strictly more than its own conclusion.**  `notConsRow` is
`BoundedBy 1` in every conjunct of `ComputeRowSkeleton.BoundedBy` — including the decomposition
slots that §A produces — yet its formula is not the `cons` of those slots.  So §A is a genuine
reduction and not a restatement of the bound it proves. -/

theorem consDecomposed_not_implied_by_bounds :
    ComputeRowSkeleton.BoundedBy 1 notConsRow ∧
      notConsRow.formula ≠
        .cell (notConsRow.decomposition .f_h rfl) (notConsRow.decomposition .f_t rfl) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [notConsRow]
  · simp [notConsRow]
  · simp [notConsRow]
  · intro slot h; simp [notConsRow]
  · intro i h slot; simp [notConsRow]
  · intro i h; simp [notConsRow, MemRecSkeleton.BoundedBy]
  · simp [notConsRow]

/-! ## §B. `sizeWindowBound`: the recorded missing hypothesis, measured -/

/-- The named extra is a leaf inequality in `S` and `Λ` alone.  No NPR seed occurs in it, so
`orderOf z ≤ Λ + 1` cannot be *necessary* for it. -- the paper -/

theorem sizeWindowBound_is_seed_free (S : SemanticSkeleton) (Λ : ℕ) :
    SizeWindowCounting.SizeWindowNounsBoundedBy S Λ ↔
      ∀ n ∈ SizeWindowCounting.skeletonSizeWindowNouns S, n.leaves ≤ Λ :=
  Iff.rfl

/-- **The recorded route pins the seed order exactly.**  On a window noun that attains the bound,
sampled `SizeWindow` forces `Λ < orderOf z` and the recorded hypothesis forces `orderOf z ≤ Λ + 1`,
so the two together determine `orderOf z = Λ + 1`.  The paper's regime is the opposite one:
`Λ = 2^7` at `|𝕂| ≈ 2^192` with `Λ, k ∈ negl(|𝕂|)`. -/

theorem sizeWindow_route_pins_the_order {z : K} {n : Noun} {Λ : ℕ}
    (hw : OpcodeSemantics.SizeWindow z n) (hleaves : n.leaves = Λ)
    (hord : orderOf z ≤ Λ + 1) :
    orderOf z = Λ + 1 := by
  have := hw.leaves_lt_order
  rw [hleaves] at this
  omega

/-! ### §B.1 Measured at the live released fixture

`DistinctCensusExecution.(distinctCensusExecution hfirstD)` is the honest execution under
`DistinctCensusFold2.packageR`.  There `Λ = 7` and the NPR seed is `8 : K97cubic`, of order `16`. -/

/-- An eight-leaf noun. -/
def eightLeaves : Noun :=
  .cell (.cell (.cell (.atom 0) (.atom 0)) (.cell (.atom 0) (.atom 0)))
    (.cell (.cell (.atom 0) (.atom 0)) (.cell (.atom 0) (.atom 0)))

theorem eightLeaves_leaves : eightLeaves.leaves = 8 := by
  simp [eightLeaves, Noun.leaves]

section LiveFixture

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusExecution

local instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97ao116 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)

/-- The two fixture numerals, read off the live carrier. -/
theorem distinctCensus_Lambda_and_order :
    (distinctCensusExecution hfirstD).Λ = 7 ∧
      orderOf (distinctCensusExecution hfirstD).cfg.challenges.z = 16 :=
  ⟨rfl, omega8_order⟩

/-- **The recorded missing hypothesis is FALSE at the live released fixture.**  `orderOf z = 16`
and `Λ + 1 = 8`.  So the `orderOf` route is not merely unavailable there; it cannot be taken. -/

theorem order_le_succ_Lambda_false_at_distinctCensus :
    ¬ orderOf (distinctCensusExecution hfirstD).cfg.challenges.z ≤ (distinctCensusExecution hfirstD).Λ + 1 := by
  rw [(distinctCensus_Lambda_and_order hfirstD).2, (distinctCensus_Lambda_and_order hfirstD).1]
  omega

/-! ### §B.0 Non-vacuity of §A at the live released fixture

`ConsDecomposedRow` is not a proposal on paper: every compute row of
`DistinctCensusExecution.(distinctCensusExecution hfirstD)` satisfies it definitionally, because the fixture's
nouns are built the paper's way — `op5Formula = cons(op5Head, op5Tail)`,
`op5Tail = cons(leftFormula, rightFormula)`, `leftFormula = cons(op1Head, operandLeft)`.  So §A is
not conditional on an object no honest execution has. -/

theorem consDecomposedRow_cast
    {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K97cubic}
    (h : row₁ = row₂) {d : ComputeRowSemanticData 97 7 row₂}
    (hd : ConsDecomposedRow d) : ConsDecomposedRow (castRowData h d) := by
  cases h
  exact hd


theorem op5RowData_consDecomposed : ConsDecomposedRow op5RowData where
  formula_cons := rfl
  tail_cons := fun _ => rfl
  branchTail_cons := fun h => absurd h (by decide)


theorem op1LRowData_consDecomposed : ConsDecomposedRow op1LRowData where
  formula_cons := rfl
  tail_cons := fun h => absurd h (by decide)
  branchTail_cons := fun h => absurd h (by decide)


theorem op1RRowData_consDecomposed : ConsDecomposedRow op1RRowData where
  formula_cons := rfl
  tail_cons := fun h => absurd h (by decide)
  branchTail_cons := fun h => absurd h (by decide)

/-- **The §A object is inhabited on a real honest execution**, at every compute row. -/

theorem distinctCensus_consDecomposed :
    ∀ i : Fin (distinctCensusExecution hfirstD).cfg.compRows,
      ConsDecomposedRow ((distinctCensusExecution hfirstD).semanticData.rows i)
  | ⟨0, _⟩ => consDecomposedRow_cast computeRowAtD_zero op5RowData_consDecomposed
  | ⟨1, _⟩ => consDecomposedRow_cast computeRowAtD_one op1LRowData_consDecomposed
  | ⟨2, _⟩ => consDecomposedRow_cast computeRowAtD_two op1RRowData_consDecomposed
  | ⟨n + 3, h⟩ => absurd (show n + 3 < 3 from h) (by omega)

/-- **`skeletonBounded` and `combinedBounded` are unconditional at the live released fixture.**
Two of the five census extras are therefore not merely reduced but discharged on the honest
execution under `DistinctCensusFold2.packageR`, for every `ResidualPremises` / `MemoryRecordPremises`
pair.  The other three census extras are untouched by this, and the premise fields are not deleted:
`censusRecordPremises_still_five_here` is unchanged. -/

theorem distinctCensus_skeletonBounded_and_combinedBounded
    (P : ResidualPremises (distinctCensusExecution hfirstD))
    (M : MemoryRecordPremises (distinctCensusExecution hfirstD)) :
    (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
        (memoryNodesOf (distinctCensusExecution hfirstD) M)).BoundedBy (distinctCensusExecution hfirstD).q ∧
      ProductionP8Containment.CombinedBoundedBy K97cubic (distinctCensusExecution hfirstD).q
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)) :=
  skeletonBounded_and_combinedBounded_of_consDecomposed (distinctCensusExecution hfirstD) P M
    (distinctCensus_consDecomposed hfirstD)
    (by rw [DistinctCensusExecution.ringChar_K97]; omega)

/-- **The residual gap at the released fixture, exhibited.**  Even *complete* sampled `SizeWindow`
on every window noun certifies only `leaves ≤ 15` there, while the extra asks for `leaves ≤ 7`.
`eightLeaves` sits in the gap: it satisfies `SizeWindow` at the fixture seed and violates the
extra.  This is a live-fixture separation, not a synthetic pole. -/

theorem sizeWindow_gap_at_distinctCensus :
    OpcodeSemantics.SizeWindow (distinctCensusExecution hfirstD).cfg.challenges.z eightLeaves ∧
      ¬ eightLeaves.leaves ≤ (distinctCensusExecution hfirstD).Λ := by
  have hord : orderOf (distinctCensusExecution hfirstD).cfg.challenges.z = 16 :=
    (distinctCensus_Lambda_and_order hfirstD).2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hord]; omega
  · rw [eightLeaves_leaves, hord]; omega
  · rw [eightLeaves_leaves, (distinctCensus_Lambda_and_order hfirstD).1]; omega

end LiveFixture

/-! ## §C. Independence of `sizeWindowBound` from `census` at OP6

The required size-window noun of an OP6 row is `skeletonSubformula s 1 .result`
(`SizeWindowCounting.requiredSizeWindowNouns`), and no entry of `P8Census.skeletonComparisons` at
`.s6` mentions it.  So even a complete identification of `data.comparisons` with the reconstructed
`skeletonComparisons` — the object `census` is missing — would not supply `sizeWindowBound`. -/

/-- **Everything the carrier records about a reconstructed size-window noun.**  The size-window
nouns of the reconstructed skeleton are `subformulaNoun` values, i.e. `Classical.choose` witnesses
of `FPRealized`, and `FPRealized z q fp` is `∃ n, BoundedBy q n ∧ enc z n = fp`.  So the two facts
below are the *whole* of what is known about them — an atom range and an encoding equation.  Neither
mentions `Λ`, which is why no already-held object bounds their leaves. -/

theorem reconstructed_subformulaNoun_properties {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row.1) (slot : TripleSlot) :
    FieldEmbedding.BoundedBy q (subformulaNoun Λ pubR i hi slot) ∧
      GlobalCarryRecognizer.enc row.2.1.z (subformulaNoun Λ pubR i hi slot) =
        tripleFP (computeSubformulaFPs row.2.2.1 i) slot :=
  ⟨subformulaNoun_bounded Λ pubR i hi slot,
    subformulaNoun_enc Λ pubR i hi slot⟩

/-- A four-leaf noun. -/
def fourLeaves : Noun :=
  .cell (.cell (.atom 0) (.atom 0)) (.cell (.atom 0) (.atom 0))

theorem fourLeaves_leaves : fourLeaves.leaves = 4 := by
  simp [fourLeaves, Noun.leaves]

/-- An OP6 skeleton row: every noun the census inspects is an atom, and only the size-window slot
`sf 1 .result` — which no OP6 comparison mentions — is large. -/

def s6WindowRow : ComputeRowSkeleton where
  state := .s6
  subject := .atom 0
  formula := .atom 0
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun i _ slot =>
    if (i : ℕ) = 1 ∧ slot = TripleSlot.result then fourLeaves else .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 1⟩

def s6WindowSkeleton : SemanticSkeleton where
  computeTree := .node s6WindowRow []
  memoryForest := []

theorem s6WindowSkeleton_computeRows :
    computeSkeletonRows s6WindowSkeleton = [s6WindowRow] := by
  unfold computeSkeletonRows s6WindowSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

theorem s6WindowSkeleton_sizeWindowNouns :
    SizeWindowCounting.skeletonSizeWindowNouns s6WindowSkeleton = [fourLeaves] := by
  rw [SizeWindowCounting.skeletonSizeWindowNouns, s6WindowSkeleton_computeRows]
  simp [SizeWindowCounting.requiredSizeWindowNouns, s6WindowRow,
    P8Census.skeletonSubformula, ComputeTable.fanoutComp]

/-- **`census` holds and `sizeWindowBound` fails on the same reconstructed-shape skeleton.**  Every
P8 pair and every edge pair has at most two leaves, so `CombinedSkeletonCensus` holds at `Λ = 2`;
the OP6 size-window noun has four, so the extra fails at every `Λ < 4`.  Uniform in `Λ`, so this is
not placed at a single degenerate value. -/

theorem census_holds_and_sizeWindowBound_fails :
    EdgeComparisonCensus.CombinedSkeletonCensus K s6WindowSkeleton 2 ∧
      ∀ Λ : ℕ, Λ < 4 →
        ¬ SizeWindowCounting.SizeWindowNounsBoundedBy s6WindowSkeleton Λ := by
  constructor
  · refine ⟨⟨?_⟩, ⟨?_⟩⟩
    · intro pair hp
      unfold BoundSemanticTrace.skeletonPairs at hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · simp only [SemanticSkeleton.publicClaim, s6WindowSkeleton, s6WindowRow,
          NTree.label_node, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> simp [Noun.leaves]
      · rw [List.mem_map] at hp
        obtain ⟨c, hc, rfl⟩ := hp
        unfold P8Census.skeletonComparisonCensus at hc
        rw [List.mem_flatMap] at hc
        obtain ⟨s, hs, hcs⟩ := hc
        rw [s6WindowSkeleton_computeRows, List.mem_singleton] at hs
        subst hs
        simp only [P8Census.skeletonComparisons, s6WindowRow, P8Census.skeletonDec,
          P8Census.skeletonSubformula, P8Census.skeletonUse, decActive,
          hasTailDecomposition, ComputeTable.fanoutComp, List.mem_cons,
          List.not_mem_nil, or_false] at hcs
        rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [SemanticTrace.ComparisonUse.pair, Noun.leaves]
    · intro pair hp
      unfold EdgeComparisonCensus.edgePairs s6WindowSkeleton at hp
      rw [bfsForest_cons_eq _ (by simp)] at hp
      simp [bfsForest_nil, EdgeComparisonCensus.rowEdgePairs, NTree.childOpt] at hp
  · intro Λ hΛ hbound
    have hmem : fourLeaves ∈ SizeWindowCounting.skeletonSizeWindowNouns s6WindowSkeleton := by
      rw [s6WindowSkeleton_sizeWindowNouns]; simp
    have := hbound fourLeaves hmem
    rw [fourLeaves_leaves] at this
    omega

/-! ## §D. `slotSemantics` and `census` — recorded descriptions confirmed -/

/-- `SemanticTrace.RowStateNeeds` has exactly two fields, and neither relates a served lookup to the
row's own memory records or to `RootRealization`.  So the earlier recorded missing object — served-noun
identification with the reconstructed skeleton — is what is actually missing.  Paper slot semantics:
operator at the paper, base case `\(1,n_1) = n_1` at the paper (not `1289`, which is
blank), child-axis relation at the paper. -/

theorem rowStateNeeds_eta_two_fields {z : K} {st : ComputeTable.State}
    (needs : RowStateNeeds z st) :
    needs = { served := needs.served, served_count := needs.served_count } := by
  cases needs
  rfl

/-- `EdgeComparisonCensus.CombinedSkeletonCensus` *is* the the paper leaf window applied to the
reconstructed census list: the whole predicate unfolds to `pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ`
over `skeletonPairs` and `edgePairs`.  There is no proper sub-object to reduce it to. -/

theorem census_is_the_leaf_window (S : SemanticSkeleton) (Λ : ℕ) :
    EdgeComparisonCensus.CombinedSkeletonCensus K S Λ ↔
      ((∀ pair ∈ BoundSemanticTrace.skeletonPairs K S,
          pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ) ∧
        (∀ pair ∈ EdgeComparisonCensus.edgePairs S.computeTree,
          pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ)) :=
  ⟨fun h => ⟨h.p8.leaves_bounded, h.edges.leaves_bounded⟩,
    fun h => ⟨⟨h.1⟩, ⟨h.2⟩⟩⟩

/-- The `Λ`-window narrowing the §A object buys for `census`: under the same three paper `cons`
constraints, every active decomposition slot inherits the row formula's leaf bound, by the
`λ = λ_L + λ_R` half of `Lem:decomp`.  This removes the decomposition nouns and
the three composite `cons` cells from what a `census` premise has to state; it does **not** inhabit
`census`, whose public-claim, subformula and edge-pair obligations are untouched. -/

theorem censusDecompSlots_of_consDecomposed {q Λ Λ' : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    {data : ComputeRowSemanticData q Λ row}
    (hc : ConsDecomposedRow data) (hf : data.root.formula.leaves ≤ Λ')
    (slot : DecSlot) (hact : decActive row.1 slot = true) :
    (decompNoun data slot).leaves ≤ Λ' :=
  hc.decompNoun_leaves_le hf slot hact

/-! ## §F. Two of the five extras need NO CARRIER AT ALL: they are STATE-GATED

`SizeWindowCounting.requiredSizeWindowNouns` emits nothing outside `{.s3, .s4, .s6}` — those are the
three Algorithm `NockCompute` blocks that read a subformula evaluation's *type*: `OP_3`'s
`evaluation = ?(sf_evaluation_1)`, `OP_4`'s `evaluation = +(sf_evaluation_1)`
 and `OP_6`'s `type(sf_evaluation_2) = atom`, with the proof prose
at the paper.  Both clauses of `ServedLookupBridge.SkeletonSlotSemantics` are gated on
`{.s0, .s9}`.  And the reconstructed compute-row skeleton takes
its `state` field from the execution's own row by `rfl` (`reconstructed_row_state`).  That is the
whole mechanism.  Hence, with **no carrier field, no type index, and no new named object**:

* `sizeWindowBound_of_no_window_states` — the `sizeWindowBound` extra, on the reconstruction, at any
  `E` whose compute rows avoid OP3/OP4/OP6;
* `slotSemantics_of_no_lookup_states` — the `slotSemantics` extra, on the reconstruction, at any `E`
  whose compute rows avoid OP0/OP9.

**What is generic.**  Both of those are generic in `F`, `K`, `E`, `P` and `M`.  Their proofs use no
fixture, no seed, no `Λ`-bound and no `Classical.choose` witness.

**What is state-gated — and the gate is not removable.**  Each carries its opcode-avoidance
hypothesis *in the statement*, and the hypothesis is load-bearing rather than bookkeeping: §C's
`census_holds_and_sizeWindowBound_fails` exhibits an OP6 skeleton on which
`SizeWindowNounsBoundedBy` fails at every `Λ < 4`, and `s0SlotFailRow_slotSemantics_fails` below
exhibits an OP0 row on which `SkeletonSlotSemantics` fails.  So **neither extra is closed
generically**; at an execution containing an OP3/OP4/OP6 row `sizeWindowBound` still needs the object
§B and §C describe, and at one containing an OP0/OP9 row `slotSemantics` still needs the earlier
identification.  "Four of five at F97" must not be read as "four of five generically".

**What is fixture-level.**  `(distinctCensusExecution hfirstD)` has compute rows `.s5, .s1, .s1`, so it
satisfies both hypotheses and both extras hold there unconditionally, for every `(P, M)` pair.

**Layer — the thing that is easiest to get wrong here.**  Every statement in §F is over the
**reconstruction** `skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)`, which is the object
`CensusRecordPremises` quantifies over.  None of it is over the hand-built `skelD` of
`DistinctCensusCommitment`; `DistinctCensusHonestArrays.sizeWindowNounsD` is the `skelD` statement
and is a *different* theorem about a *different* skeleton, and it is not used here.

**`census` is the only field left, and it needs `C2`.**
`distinctCensus_censusRecordPremises_of_census` takes `census` as its **sole** hypothesis and returns
a whole `CensusRecordPremises (distinctCensusExecution hfirstD) P M`.  That is the mechanical form of "four of
the five fields at the released F97 fixture with no carrier": four are supplied, the fifth is the
hypothesis, and the definition would not typecheck if a sixth field or a second gap existed.
`census` is the paper's `NockProgram^Λ` leaf window applied to the reconstructed census list
(`census_is_the_leaf_window`; `Def[Nock Program]`, the paper, the window itself at
the paper) — the object the carrier program calls `C2`.  It is **not** supplied here, and
nothing in §F bears on it.

**Quantifier caveat — CORRECTED later, and the correction STRENGTHENS this
section.**  Every fixture statement below is `∀ (P : ResidualPremises …)
(M : MemoryRecordPremises …), …`.  When this was written neither type was known to be inhabited in
this build; **both now are**, at this very fixture — `Batch138.b138_residualPremises` and
`Batch138.b138_memoryRecordPremises` are compiled inhabitants at `(distinctCensusExecution hfirstD)`
(`b138_premise_pair_inhabited_at_both_fixtures` exhibits the pair at F73 and F97 together).  So these
theorems are instantiable at a real `(P, M)` pair (`Batch138.b138_four_census_extras_at_a_witness`),
and the four discharged fields are statements about a concrete reconstructed skeleton rather than a
`∀` over a possibly-empty type.

**The rest of the caveat is unchanged and still binding.**  These results are still **not** an
inhabited `CensusRecordPremises`, because `census` is not supplied here and nothing in §F bears on it;
`censusRecordPremises_still_five_here` is unchanged; the bundle still has five fields and no carrier
field is added anywhere.  Nor does the F97 `MemoryRecordPremises` inhabitant unpark anything: its
`timestampClosed` is a finite read of the concrete record column, independent of the parked generic
route `GenericHonestData.timestampClosed_of_paired_record_layout`
(`Batch138.b138_pairedRecordLayout_is_a_second_route`), so `PairedRecordLayout` and the *generic*
`timestampClosed` premise stay parked (§J.1.P). -/

/-- The reconstructed compute-row skeleton takes its `state` from the execution's own compute row,
definitionally.  This is the whole mechanism of §F. -/

theorem reconstructed_row_state (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (i : Fin E.cfg.compRows) :
    ((computeNodeAt E P i).skel).state = (E.exec.computeRowAt i).1 := rfl

/-- Every compute-row skeleton of the reconstruction is `(computeNodeAt E P i).skel` for some `i`.
The BFS enumeration is the same one `skeletonBounded_of_consDecomposed` walks. -/

theorem reconstructed_rows_are_nodes (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    {s : ComputeRowSkeleton}
    (hs : s ∈ computeSkeletonRows
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M))) :
    ∃ i : Fin E.cfg.compRows, s = (computeNodeAt E P i).skel := by
  rw [computeSkeletonRows_of_assembly E P M] at hs
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hs
  rw [List.mem_range'] at hj
  obtain ⟨k, hk, rfl⟩ := hj
  simp only [Nat.one_mul]
  have hidx : k < E.cfg.compRows := by
    rw [← E.exec.compute_bfs_length]
    exact hk
  refine ⟨⟨k, hidx⟩, ?_⟩
  have h1 : (1 + k) - 1 = k := Nat.add_sub_cancel_left 1 k
  simpa [h1] using
    congrArg ComputeNode.skel
      (computeLabelAt_of_index E P (i := 1 + k) (by simpa [h1] using hidx))

/-- **`sizeWindowBound` on the reconstruction with no carrier, at any execution avoiding
OP3/OP4/OP6.**

Generic in `F`, `K`, `E`, `P`, `M`.  The opcode-avoidance hypothesis is explicit and is **not**
removable: `census_holds_and_sizeWindowBound_fails` refutes the conclusion at an OP6 row.  No field
is added, no type index is changed, and no `Classical.choose` leaf bound is used — in particular this
is not the refuted `orderOf z ≤ Λ + 1` route of §B, which does not appear anywhere in the proof.

Paper mechanism: a size window is required exactly where the verifier reads a subformula
evaluation's type, i.e. at `OP_3`, `OP_4` and `OP_6`
; prose at the paper. -/

theorem sizeWindowBound_of_no_window_states (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (h : ∀ i : Fin E.cfg.compRows,
      (E.exec.computeRowAt i).1 ≠ .s3 ∧ (E.exec.computeRowAt i).1 ≠ .s4 ∧
        (E.exec.computeRowAt i).1 ≠ .s6) :
    SizeWindowCounting.SizeWindowNounsBoundedBy
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ := by
  intro n hn
  rw [SizeWindowCounting.skeletonSizeWindowNouns, List.mem_flatMap] at hn
  obtain ⟨s, hs, hns⟩ := hn
  obtain ⟨i, rfl⟩ := reconstructed_rows_are_nodes E P M hs
  obtain ⟨h3, h4, h6⟩ := h i
  rw [← reconstructed_row_state E P i] at h3 h4 h6
  have hempty : SizeWindowCounting.requiredSizeWindowNouns ((computeNodeAt E P i).skel) = [] := by
    unfold SizeWindowCounting.requiredSizeWindowNouns
    rcases hstate : ((computeNodeAt E P i).skel).state with
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;> rw [hstate] at h3 h4 h6 <;>
      first
        | rfl
        | exact absurd rfl h3
        | exact absurd rfl h4
        | exact absurd rfl h6
  rw [hempty] at hns
  simp at hns

/-- **`slotSemantics` on the reconstruction with no carrier, at any execution avoiding OP0/OP9.**

Generic in `F`, `K`, `E`, `P`, `M`.  Both clauses of `ServedLookupBridge.SkeletonSlotSemantics` are
gated on `.s0` / `.s9` — the two algorithm blocks that perform a memory lookup
 — so off those two states every clause is discharged by its own gate.  The
opcode-avoidance hypothesis is explicit and is **not** removable:
`s0SlotFailRow_slotSemantics_fails` refutes the conclusion at an OP0 row.

This does **not** supply the previously recorded missing object.  At an OP0 or OP9 row the identification of a served
lookup with the reconstructed skeleton's subject / `mr2`-axis / evaluation is still what is
missing (§D). -/

theorem slotSemantics_of_no_lookup_states (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (h : ∀ i : Fin E.cfg.compRows,
      (E.exec.computeRowAt i).1 ≠ .s0 ∧ (E.exec.computeRowAt i).1 ≠ .s9) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      ServedLookupBridge.SkeletonSlotSemantics s := by
  intro s hs
  obtain ⟨i, rfl⟩ := reconstructed_rows_are_nodes E P M hs
  obtain ⟨h0, h9⟩ := h i
  rw [← reconstructed_row_state E P i] at h0 h9
  exact { s0_slot := fun hst => absurd hst h0, s9_slot := fun hst => absurd hst h9 }

/-! ### §F.1 The opcode gate on `slotSemantics` is real

§C already exhibits the OP6 counterexample for `sizeWindowBound`.  This is the OP0 counterpart for
`slotSemantics`, so that neither theorem of §F can be misread as generically true with a decorative
hypothesis. -/

/-- An OP0 compute-row skeleton whose second memory record has axis `2` on an atomic subject.
`recordCount .s0 = 2`, so `skeletonMemoryAxis · 1` reads that record. -/

def s0SlotFailRow : ComputeRowSkeleton where
  state := .s0
  subject := .atom 0
  formula := .atom 0
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 2⟩

/-- **The OP0 gate is load-bearing.**  `/[2 0]` is `none`, so the `s0_slot` clause fails on
`s0SlotFailRow`.  Hence `slotSemantics_of_no_lookup_states` is genuinely state-gated: its conclusion
is false at an OP0 row of this shape, and the hypothesis cannot be dropped. -/

theorem s0SlotFailRow_slotSemantics_fails :
    ¬ ServedLookupBridge.SkeletonSlotSemantics s0SlotFailRow := by
  intro hslot
  have h := hslot.s0_slot rfl
  rw [show P8Census.skeletonMemoryAxis s0SlotFailRow 1 = 2 from rfl] at h
  simp [s0SlotFailRow, Noun.slot] at h

/-! ### §F.1a The gate is SUFFICIENT and NOT NECESSARY, in both directions

The equivalence test, applied to §F.  If the opcode-avoidance hypothesis were equivalent to
the conclusion the two theorems would be renames and would close nothing, so both directions are
compiled rather than argued.

*Gate ⟹ conclusion*: `sizeWindowBound_of_no_window_states` / `slotSemantics_of_no_lookup_states`.
*Conclusion ⇏ gate*: the two witnesses below — an OP6 skeleton whose size-window noun is an atom, and
an OP0 row whose second record has axis `1` on a subject equal to its evaluation.  Both violate the
gate and satisfy the conclusion, so the gate is **strictly stronger** than what it produces and
neither theorem is an equivalence in disguise.

The gate is nevertheless not a new object in the sense §A's `ConsDecomposedRow` is: it is a decidable
property of the state column `E.exec.computeRowAt` already carries, no field is added, and it is
*discharged* — not assumed — at the released fixture by `distinctCensus_no_window_states` and
`distinctCensus_no_lookup_states`. -/

/-- An OP6 row whose size-window noun `sf 1 .result` is an atom. -/

def s6SmallWindowRow : ComputeRowSkeleton :=
  { s6WindowRow with subformula := fun _ _ _ => .atom 0 }

def s6SmallWindowSkeleton : SemanticSkeleton where
  computeTree := .node s6SmallWindowRow []
  memoryForest := []

theorem s6SmallWindowSkeleton_computeRows :
    computeSkeletonRows s6SmallWindowSkeleton = [s6SmallWindowRow] := by
  unfold computeSkeletonRows s6SmallWindowSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

/-- **The OP3/OP4/OP6 gate is sufficient, not necessary.**  This skeleton has an OP6 row — so the
hypothesis of `sizeWindowBound_of_no_window_states` fails on it — and still satisfies
`SizeWindowNounsBoundedBy` at `Λ = 1`.  Hence that theorem is a genuine implication and not the
conclusion renamed. -/

theorem window_state_gate_not_necessary :
    s6SmallWindowRow.state = .s6 ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy s6SmallWindowSkeleton 1 := by
  refine ⟨rfl, ?_⟩
  intro n hn
  rw [SizeWindowCounting.skeletonSizeWindowNouns, s6SmallWindowSkeleton_computeRows] at hn
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hn
  rw [show SizeWindowCounting.requiredSizeWindowNouns s6SmallWindowRow = [Noun.atom 0] from rfl,
    List.mem_singleton] at hn
  rw [hn]
  simp [Noun.leaves]

/-- An OP0 row whose `mr2` axis is `1` on a subject equal to its evaluation. -/

def s0SlotHoldRow : ComputeRowSkeleton :=
  { s0SlotFailRow with memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 1⟩ }

/-- **The OP0/OP9 gate is sufficient, not necessary.**  This row is `.s0` — so the hypothesis of
`slotSemantics_of_no_lookup_states` fails on it — and still satisfies `SkeletonSlotSemantics`,
because `/[1 n] = n`.  Hence that theorem is a genuine implication and not the
conclusion renamed. -/

theorem lookup_state_gate_not_necessary :
    s0SlotHoldRow.state = .s0 ∧ ServedLookupBridge.SkeletonSlotSemantics s0SlotHoldRow := by
  refine ⟨rfl, ⟨?_, ?_⟩⟩
  · intro _
    rw [show P8Census.skeletonMemoryAxis s0SlotHoldRow 1 = 1 from rfl]
    simp [s0SlotHoldRow, s0SlotFailRow, Noun.slot]
  · intro h
    exact absurd h (by decide)

/-! ### §F.2 The live released F97 fixture -/

section LiveFixtureStateGate

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusExecution

local instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)

/-- The released fixture's three compute rows are `OP_5`, `OP_1`, `OP_1`
. -/

theorem distinctCensus_row_states
    (i : Fin (distinctCensusExecution hfirstD).cfg.compRows) :
    ((distinctCensusExecution hfirstD).exec.computeRowAt i).1 = .s5 ∨
      ((distinctCensusExecution hfirstD).exec.computeRowAt i).1 = .s1 := by
  match i with
  | ⟨0, _⟩ => exact Or.inl (congrArg Prod.fst computeRowAtD_zero)
  | ⟨1, _⟩ => exact Or.inr (congrArg Prod.fst computeRowAtD_one)
  | ⟨2, _⟩ => exact Or.inr (congrArg Prod.fst computeRowAtD_two)
  | ⟨n + 3, h⟩ =>
      have hc : (distinctCensusExecution hfirstD).cfg.compRows = 3 := rfl
      rw [hc] at h
      exact absurd h (by omega)

/-- The released fixture has no OP3/OP4/OP6 row, so it satisfies the `sizeWindowBound` gate. -/

theorem distinctCensus_no_window_states
    (i : Fin (distinctCensusExecution hfirstD).cfg.compRows) :
    ((distinctCensusExecution hfirstD).exec.computeRowAt i).1 ≠ .s3 ∧
      ((distinctCensusExecution hfirstD).exec.computeRowAt i).1 ≠ .s4 ∧
        ((distinctCensusExecution hfirstD).exec.computeRowAt i).1 ≠ .s6 := by
  rcases distinctCensus_row_states hfirstD i with h | h <;> rw [h] <;>
    exact ⟨by decide, by decide, by decide⟩

/-- The released fixture has no OP0/OP9 row, so it satisfies the `slotSemantics` gate. -/

theorem distinctCensus_no_lookup_states
    (i : Fin (distinctCensusExecution hfirstD).cfg.compRows) :
    ((distinctCensusExecution hfirstD).exec.computeRowAt i).1 ≠ .s0 ∧
      ((distinctCensusExecution hfirstD).exec.computeRowAt i).1 ≠ .s9 := by
  rcases distinctCensus_row_states hfirstD i with h | h <;> rw [h] <;>
    exact ⟨by decide, by decide⟩

/-- **`sizeWindowBound` is unconditional at the live released fixture, with no carrier**, for every
`(P, M)` pair, and over the **reconstruction** rather than the hand-built `skelD`.

Contrast `order_le_succ_Lambda_false_at_distinctCensus`, which refutes the `orderOf` route at the same
fixture: this route does not mention the seed at all. -/

theorem distinctCensus_sizeWindowBound
    (P : ResidualPremises (distinctCensusExecution hfirstD))
    (M : MemoryRecordPremises (distinctCensusExecution hfirstD)) :
    SizeWindowCounting.SizeWindowNounsBoundedBy
      (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
        (memoryNodesOf (distinctCensusExecution hfirstD) M)) (distinctCensusExecution hfirstD).Λ :=
  sizeWindowBound_of_no_window_states (distinctCensusExecution hfirstD) P M
    (distinctCensus_no_window_states hfirstD)

/-- **`slotSemantics` is unconditional at the live released fixture, with no carrier**, for every
`(P, M)` pair, and over the **reconstruction** rather than the hand-built `skelD`. -/

theorem distinctCensus_slotSemantics
    (P : ResidualPremises (distinctCensusExecution hfirstD))
    (M : MemoryRecordPremises (distinctCensusExecution hfirstD)) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)),
      ServedLookupBridge.SkeletonSlotSemantics s :=
  slotSemantics_of_no_lookup_states (distinctCensusExecution hfirstD) P M
    (distinctCensus_no_lookup_states hfirstD)

/-- **Four of the five `CensusRecordPremises` fields at the released F97 fixture, with no carrier.**

`slotSemantics` and `sizeWindowBound` from §F; `skeletonBounded` and `combinedBounded` from §B.0's
`distinctCensus_skeletonBounded_and_combinedBounded`.  All four are stated over the same
reconstruction `skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
(memoryNodesOf (distinctCensusExecution hfirstD) M)` for the same `P` and `M`, which is the object
`CensusRecordPremises` quantifies over — the objects are threaded, not independently quantified.

This is **fixture-level and state-conditional**, not generic: see the §F preamble.  The fifth field,
`census`, is not here; `distinctCensus_censusRecordPremises_of_census` states exactly that. -/

theorem distinctCensus_four_census_extras
    (P : ResidualPremises (distinctCensusExecution hfirstD))
    (M : MemoryRecordPremises (distinctCensusExecution hfirstD)) :
    (∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)),
        ServedLookupBridge.SkeletonSlotSemantics s) ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)) (distinctCensusExecution hfirstD).Λ ∧
      (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
        (memoryNodesOf (distinctCensusExecution hfirstD) M)).BoundedBy (distinctCensusExecution hfirstD).q ∧
      ProductionP8Containment.CombinedBoundedBy K97cubic (distinctCensusExecution hfirstD).q
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)) :=
  ⟨distinctCensus_slotSemantics hfirstD P M, distinctCensus_sizeWindowBound hfirstD P M,
    (distinctCensus_skeletonBounded_and_combinedBounded hfirstD P M).1,
    (distinctCensus_skeletonBounded_and_combinedBounded hfirstD P M).2⟩

/-- **`census` is the ONLY remaining `CensusRecordPremises` field at the released F97 fixture.**

Mechanical form of the four-of-five claim: this takes `census` as its **sole** hypothesis and returns
the whole five-field bundle.

**It is not an inhabitation and must not be cited as one.**  `census` is a hypothesis, so no
`CensusRecordPremises (distinctCensusExecution hfirstD) P M` term is produced from nothing.
`censusRecordPremises_still_five_here` is unchanged.

The
"not an inhabitation" warning above is unaffected: it rests on `census` being a hypothesis, not on the
inhabitation status of `P` / `M`.

**Why `census` is the one that stays: it needs `C2`.**  `census_is_the_leaf_window` unfolds it to the
paper's `NockProgram^Λ` leaf window (`Def[Nock Program]`, the paper, the window at
the paper) applied to the reconstructed census list, whose entries at the fixture's `.s5` row
are `subformulaNoun` — `Classical.choose` witnesses of `FPRealized` — about which
`reconstructed_subformulaNoun_properties` records only an atom range and an encoding equation,
neither mentioning `Λ`.  That is the missing object the carrier program calls `C2`, and §F does not
supply it. -/

theorem distinctCensus_censusRecordPremises_of_census
    (P : ResidualPremises (distinctCensusExecution hfirstD))
    (M : MemoryRecordPremises (distinctCensusExecution hfirstD))
    (hcensus : EdgeComparisonCensus.CombinedSkeletonCensus K97cubic
      (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
        (memoryNodesOf (distinctCensusExecution hfirstD) M)) (distinctCensusExecution hfirstD).Λ) :
    CensusRecordPremises (distinctCensusExecution hfirstD) P M where
  slotSemantics := distinctCensus_slotSemantics hfirstD P M
  census := hcensus
  sizeWindowBound := distinctCensus_sizeWindowBound hfirstD P M
  skeletonBounded := (distinctCensus_skeletonBounded_and_combinedBounded hfirstD P M).1
  combinedBounded := (distinctCensus_skeletonBounded_and_combinedBounded hfirstD P M).2

end LiveFixtureStateGate

/-! ## §G. `census` by the paper's own λ-propagation route

**What this section is.**  A *reduction* of the fifth and last unsupplied `CensusRecordPremises`
field to the paper's own objects, with **no carrier change**: `BuildableNockExecution` is still
fourteen fields, `HonestCommitment.Data` sixteen, `ResidualPremises` four and `CensusRecordPremises`
five.  Nothing here inhabits `census`.

**G.0 — what `census` actually is, relative to what the commitment already holds.**
`EdgeComparisonCensus.combinedSkeletonPairs K S = skeletonPairs K S ++ edgePairs S.computeTree` is
one occurrence list.  `census` and the **already-held** `Data` field `combinedBounded` are the *same
quantifier over that same list*, differing only in the KIND of bound:

* `combinedBounded` — `FieldEmbedding.BoundedBy E.q` on both components (atom range);
* `census`         — `leaves ≤ E.Λ` on both components (the the paper leaf window).

`combinedBounded_is_the_same_occurrence_list` is `Iff.rfl`, and `census_iff_combined_leaf_window` is
the leaf analogue.  The two are **not** interchangeable and that is compiled, not asserted:
`census_and_combinedBounded_differ_in_kind` exhibits a row satisfying the atom bound everywhere and
failing the leaf window.  This is the "check the bound is the right KIND" test, applied to the two
fields that live on one list.

**G.1 — where the census nouns come from: labels, and `Classical.choose`.**  On the reconstruction
`skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)` the split is exact and it is *not*
uniform:

* `subject`, `formula`, `evaluation` and every `decomposition` slot are the execution's **own
  labels** — `data.root.subject/formula/result` and `decompNoun data slot`, all by `rfl`;
* every `subformula` slot is `GenericHonestCommitment.subformulaNoun`, i.e. a **`Classical.choose`
  witness** of an `FPRealized` existential, characterised only up to `enc` and `BoundedBy q`.

Consequently the label-only rows are exactly `OP_0` and `OP_1`
(`reconstructed_s0_comparisons_are_labels`, and `GenericHonestData`'s existing
`computeSkeletonOf_s1_skeletonComparisons`); every other opcode's comparison list mentions at least
one chosen witness, and **every** edge pair is one label against one chosen witness
(`edgePairs_left_is_a_child_label`).

**G.2 — the correction to the recorded obstruction.**  It is *not* only that `Classical.choose`
drops the leaf bound.  `E` carries `Λ` in exactly one field — `ComputeRowSemanticData.comparison_leaves`,
on the free `comparisons` list (§C) — so the execution's own labels have **no leaf bound either**.
The residual is therefore not confined to the chosen witnesses.

**G.3 — the reduction, and it is the paper's route.**  `Def[Nock Program]` is a bound on the committed nouns, and `Lem:decomp` propagates it along `cons`.  Two named objects suffice, both stated at the
committed-skeleton layer and neither a carrier field:

* `RowLeafWindow Λ s` — the the paper window on the row's own public triple and its three
  subformula triples.  It does **not** mention the decomposition slots: those are *derived*.
* `RowCellIdentities s` — the five structural `cons` equations Algorithm `NockCompute` states:
  `f = cons(f_h, f_t)` (`1846-1848`), `cons(f_th, f_tt) = f_t` (`1858-1861`),
  `cons(f_tth, f_ttt) = f_tt` (`1872-1875`), `OP_8`'s pushed subject
  `child_one_input ← (cons(sf_evaluation₂, input_subject), …)` (`1790`), and the `cons` state's
  `evaluation = cons(sf_evaluation₁, sf_evaluation₂)` (`1747`, transcribed at `1969`).

`census_of_leafWindow` is then unconditional: those two at every committed compute row, plus
`1 ≤ Λ`, give `CombinedSkeletonCensus` outright.  The `1 ≤ Λ` is needed because the census compares
against literal opcode atoms; it is free at every live fixture.

`census_of_leafWindow` takes two hypotheses that no field of `E`, `P`, `M` or `Data` supplies, so
`CensusRecordPremises` is **still one field short at F97** and `censusRecordPremises_still_five`
still holds. The reduction is not circular: `RowLeafWindow` says nothing about the decomposition
slots or about any `cons` cell, and `RowCellIdentities` states no bound at all
(`leafWindow_does_not_imply_census` compiles that the window alone is not enough — an `OP_1` row
inside the window whose `cons` cell is outside it). -/

/-! ### G.0 The same occurrence list, two kinds of bound -/

/-- `combinedBounded` — a field of `HonestCommitment.Data` — is exactly the atom-range bound on the
combined occurrence list.  Definitional; recorded so that the contrast with `census` is pinned
rather than read off two definitions. -- the paper -/
theorem combinedBounded_is_the_same_occurrence_list (q : ℕ) (S : SemanticSkeleton) :
    ProductionP8Containment.CombinedBoundedBy K q S ↔
      ∀ pair ∈ EdgeComparisonCensus.combinedSkeletonPairs K S,
        FieldEmbedding.BoundedBy q pair.1 ∧ FieldEmbedding.BoundedBy q pair.2 :=
  Iff.rfl

/-- …and `census` is the **leaf-window** bound on that same list.  With the previous theorem this is
the precise sense in which the last unsupplied census field and an already-held one differ only in
the kind of bound. -- the paper -/
theorem census_iff_combined_leaf_window (S : SemanticSkeleton) (Λ : ℕ) :
    EdgeComparisonCensus.CombinedSkeletonCensus K S Λ ↔
      ∀ pair ∈ EdgeComparisonCensus.combinedSkeletonPairs K S,
        pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ := by
  constructor
  · rintro ⟨hp8, hedges⟩ pair hp
    rw [EdgeComparisonCensus.combinedSkeletonPairs, List.mem_append] at hp
    exact hp.elim (hp8.leaves_bounded pair) (hedges.leaves_bounded pair)
  · intro h
    refine ⟨⟨fun pair hp => h pair ?_⟩, ⟨fun pair hp => h pair ?_⟩⟩
    · rw [EdgeComparisonCensus.combinedSkeletonPairs, List.mem_append]
      exact Or.inl hp
    · rw [EdgeComparisonCensus.combinedSkeletonPairs, List.mem_append]
      exact Or.inr hp

/-- **The two bounds are different kinds, and neither implies the other on this list.**  The earlier analysis's
`s1CensusFailRow` satisfies the atom-range bound at `q = 2` in every comparison while failing the
leaf window at `Λ = 1`, because its formula is a two-leaf cell.  So `combinedBounded` cannot be
transported to `census`.

**Exact layer of this separation (clarification; the name reads wider than the statement,
and the declaration is deliberately not renamed).**  What is separated below is the
**row-comparison** list `P8Census.skeletonComparisons s1CensusFailRow` of a single
`ComputeRowSkeleton` — a *sub*-list of `EdgeComparisonCensus.combinedSkeletonPairs`.  The statement
is **not** of the form `CombinedBoundedBy K q S ∧ ¬ CombinedSkeletonCensus K S Λ` on a
`SemanticSkeleton`, and it must not be cited as if it were.  It says exactly, and only, that the
atom-range kind of bound and the leaf-window kind of bound are logically independent where the two
premises meet, which is all that `census_iff_combined_leaf_window` and
`combinedBounded_is_the_same_occurrence_list` need: the two fields are one quantifier over one list
differing in the KIND of bound, so `census` is not reducible to the already-held `combinedBounded`.
Nothing in the earlier reduction depends on the wider skeleton-level shape, and none is claimed.
-- -/
theorem census_and_combinedBounded_differ_in_kind :
    (∀ c ∈ P8Census.skeletonComparisons (K := K) GenericHonestData.s1CensusFailRow,
        FieldEmbedding.BoundedBy 2 c.left ∧ FieldEmbedding.BoundedBy 2 c.right) ∧
      ¬ (∀ c ∈ P8Census.skeletonComparisons (K := K) GenericHonestData.s1CensusFailRow,
        c.LeavesBounded 1) := by
  constructor
  · intro c hc
    simp only [P8Census.skeletonComparisons, GenericHonestData.s1CensusFailRow,
      P8Census.skeletonDec, P8Census.skeletonUse, decActive, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      simp [FieldEmbedding.BoundedBy]
  · intro h
    have hmem :
        P8Census.skeletonUse .formulaCons
            (.cell (.atom 0) (.atom 0)) (.cell (.atom 0) (.atom 0)) ∈
          P8Census.skeletonComparisons (K := K) GenericHonestData.s1CensusFailRow := by
      simp [P8Census.skeletonComparisons, GenericHonestData.s1CensusFailRow,
        P8Census.skeletonDec, P8Census.skeletonUse, decActive]
    have hb := h _ hmem
    simp [ComparisonUse.LeavesBounded, P8Census.skeletonUse, Noun.leaves] at hb

/-! ### G.1 Labels versus `Classical.choose`, on the reconstruction -/

/-- The reconstructed row's public triple and its decomposition slots are the execution's **own
labels**, by `rfl`. -- the paper -/
theorem reconstructed_row_nouns_are_labels {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row)) :
    (computeSkeletonOf data pubR).subject = data.root.subject ∧
      (computeSkeletonOf data pubR).formula = data.root.formula ∧
        (computeSkeletonOf data pubR).evaluation = data.root.result ∧
          ∀ slot h, (computeSkeletonOf data pubR).decomposition slot h = decompNoun data slot :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

/-- …and every reconstructed subformula slot is `subformulaNounOf`: the row's
`CallRealization` when that noun is a windowed realizer of the committed
fingerprint, otherwise a `Classical.choose` witness of `FPRealized`.
Encoding and `BoundedBy q` are unchanged.
-- -/
theorem reconstructed_subformula_is_a_chosen_witness {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row.1) (slot : TripleSlot) :
    (computeSkeletonOf data pubR).subformula i hi slot =
      subformulaNounOf data pubR i hi slot ∧
      GlobalCarryRecognizer.enc row.2.1.z (subformulaNounOf data pubR i hi slot) =
        tripleFP (computeSubformulaFPs row.2.2.1 i) slot ∧
      FieldEmbedding.BoundedBy q (subformulaNounOf data pubR i hi slot) :=
  ⟨rfl, subformulaNounOf_enc data pubR i hi slot,
    subformulaNounOf_bounded data pubR i hi slot⟩

/-- **`OP_0` rows are label-only**, the companion of `GenericHonestData`'s existing OP1 statement:
at `.s0` every noun in the reconstructed comparison list is an execution label or a literal, with no
chosen witness anywhere. -- the paper -/
theorem reconstructed_s0_comparisons_are_labels {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (h : row.1 = .s0) :
    P8Census.skeletonComparisons (K := K) (computeSkeletonOf data pubR) =
      [P8Census.skeletonUse .opcodeHead (decompNoun data .f_h) (.atom 0),
        P8Census.skeletonUse .formulaCons data.root.formula
          (.cell (decompNoun data .f_h) (decompNoun data .f_t)),
        P8Census.skeletonUse .recursiveFormula (decompNoun data .f_t)
          (.atom (atomVal data.root.tail))] := by
  simp [P8Census.skeletonComparisons, computeSkeletonOf, P8Census.skeletonDec,
    P8Census.skeletonUse, P8Census.skeletonMemoryAxis, SemanticStrategy.decActive,
    decompNoun, memRecSkelOf, Nock.Framework.recordCount, h]

/-! ### G.3 The two paper objects, and the reduction -/

/-! ### G.3b The same window also gives §B's `sizeWindowBound`

`§B` above argued that the recorded `orderOf z ≤ Λ + 1` route is the wrong object and that "the
honest missing object is the paper's own leaf window, `NockProgram^Λ`".  That is now literally true:
`requiredSizeWindowNouns` (`SizeWindowCounting.lean:25`) selects nothing but
`P8Census.skeletonSubformula s i .result` at `.s3`/`.s4`/`.s6` rows, and `RowLeafWindow` bounds
**every** `skeletonSubformula s i slot`.  So `sizeWindowBound` and `census` are two consequences of
one hypothesis, not two independent premises. -/

/-- Both census-side extras at once, from the single premise. -/
theorem census_and_sizeWindowBound_of_leafWindow (S : SemanticSkeleton) (Λ : ℕ) (hΛ : 1 ≤ Λ)
    (hc : ∀ s ∈ computeSkeletonRows S, RowCellIdentities s)
    (hw : ∀ s ∈ computeSkeletonRows S, RowLeafWindow Λ s) :
    EdgeComparisonCensus.CombinedSkeletonCensus K S Λ ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy S Λ :=
  ⟨census_of_leafWindow S Λ hΛ hc hw, sizeWindowBound_of_leafWindow S Λ hw⟩

/-! ### G.4 The reduction is not circular, in either direction -/

/-- **The window alone is not enough**, so `RowCellIdentities` is load-bearing rather than
bookkeeping: `notConsRow` lies inside the window at `Λ = 1` in every clause, yet the census compares
its formula against the `cons` cell of its two decomposition slots, which has two leaves.  This is
the `λ = λ_L + λ_R` step of `Lem:decomp` failing for want of the structural
equation. -- the paper -/
theorem leafWindow_does_not_imply_census :
    RowLeafWindow 1 notConsRow ∧
      ¬ (∀ c ∈ P8Census.skeletonComparisons (K := K) notConsRow, c.LeavesBounded 1) := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp [notConsRow, Noun.leaves]
    · simp [notConsRow, Noun.leaves]
    · simp [notConsRow, Noun.leaves]
    · intro i slot
      simp [notConsRow, P8Census.skeletonSubformula, Noun.leaves]
      split_ifs <;> exact Nat.le_of_eq rfl
  · intro h
    have hmem :
        P8Census.skeletonUse .formulaCons (.atom 0)
            (.cell (.atom 0) (.atom 0)) ∈
          P8Census.skeletonComparisons (K := K) notConsRow := by
      simp [P8Census.skeletonComparisons, notConsRow, P8Census.skeletonDec,
        P8Census.skeletonUse, decActive]
    have hb := h _ hmem
    simp [ComparisonUse.LeavesBounded, P8Census.skeletonUse, Noun.leaves] at hb

/-- **…and the cell identities alone are not enough either**, so the window is not a restatement of
them: the earlier `s1CensusFailRow` satisfies all five structural equations and still falls outside the
window at `Λ = 1`.  `RowCellIdentities` states no bound of any kind.
-- -/
theorem cellIdentities_state_no_leaf_bound :
    RowCellIdentities GenericHonestData.s1CensusFailRow ∧
      ¬ RowLeafWindow 1 GenericHonestData.s1CensusFailRow := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [GenericHonestData.s1CensusFailRow, P8Census.skeletonDec, decActive]
    · intro h
      simp [GenericHonestData.s1CensusFailRow, decActive, hasTailDecomposition] at h
    · intro h
      simp [GenericHonestData.s1CensusFailRow, decActive, hasTailDecomposition] at h
    · intro h; simp [GenericHonestData.s1CensusFailRow] at h
    · intro h; simp [GenericHonestData.s1CensusFailRow] at h
  · intro h
    have h2 := h.2.1
    rw [GenericHonestData.s1CensusFailRow_formula_leaves] at h2
    omega

/-! ### G.5 The reduction at the layer `CensusRecordPremises` quantifies over -/

/-- The reduction, restated over the **reconstruction** `skeletonOfNodes (computeNodesOf E P)
(memoryNodesOf E M)` — the object the `census` field actually names — rather than over a bare
skeleton.  Generic in `F`, `K`, `E`, `P`, `M`; no fixture, no seed, no carrier field. -/

theorem census_of_leafWindow_on_reconstruction (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E) (hΛ : 1 ≤ E.Λ)
    (hc : ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      RowCellIdentities s)
    (hw : ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      RowLeafWindow E.Λ s) :
    EdgeComparisonCensus.CombinedSkeletonCensus K
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ :=
  census_of_leafWindow _ _ hΛ hc hw

/-- On the reconstruction the total `P8Census.skeletonDec` projection is the execution's own
decomposition label at every active slot. -- the paper -/
theorem skeletonDec_computeSkeletonOf_of_active {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (slot : DecSlot) (hact : decActive row.1 slot = true) :
    P8Census.skeletonDec (computeSkeletonOf data pubR) slot = decompNoun data slot := by
  simp [P8Census.skeletonDec, computeSkeletonOf, hact]

/-- **§A's `ConsDecomposedRow` supplies `RowCellIdentities` on the reconstruction**, off the two
opcodes whose census target is a cell that is not a `cons` of decomposition slots.  So at an
execution with no `OP_8` and no `cons` row the cell-identity hypothesis of the reduction is exactly
the §A object already in the build, and the residual is the leaf window alone.
-- -/
theorem rowCellIdentities_of_consDecomposed {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    {data : ComputeRowSemanticData q Λ row}
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (hc : ConsDecomposedRow data) (h8 : row.1 ≠ .s8) (hcons : row.1 ≠ .cons) :
    RowCellIdentities (computeSkeletonOf data pubR) where
  formula_cons := by
    rw [skeletonDec_computeSkeletonOf_of_active data pubR .f_h (decActive_cases row.1).1,
      skeletonDec_computeSkeletonOf_of_active data pubR .f_t (decActive_cases row.1).2.1]
    exact hc.formula_cons
  tail_cons := by
    intro hth
    have hth' : decActive row.1 .f_th = true := hth
    have htt' : decActive row.1 .f_tt = true := (f_tt_active_iff_f_th row.1).mpr hth'
    rw [skeletonDec_computeSkeletonOf_of_active data pubR .f_t (decActive_cases row.1).2.1,
      skeletonDec_computeSkeletonOf_of_active data pubR .f_th hth',
      skeletonDec_computeSkeletonOf_of_active data pubR .f_tt htt']
    exact hc.tail_cons hth'
  branchTail_cons := by
    intro htth
    have htth' : decActive row.1 .f_tth = true := htth
    have httt' : decActive row.1 .f_ttt = true := (f_ttt_active_iff_f_tth row.1).mpr htth'
    have htt' : decActive row.1 .f_tt = true := by
      have h6 := (decActive_cases row.1).2.2.2.2.1.mp htth'
      exact (decActive_cases row.1).2.2.2.1.mpr (by simp [h6])
    rw [skeletonDec_computeSkeletonOf_of_active data pubR .f_tt htt',
      skeletonDec_computeSkeletonOf_of_active data pubR .f_tth htth',
      skeletonDec_computeSkeletonOf_of_active data pubR .f_ttt httt']
    exact hc.branchTail_cons htth'
  push_cons := by
    intro h
    exact absurd h h8
  cons_result := by
    intro h
    exact absurd h hcons

/-- **At a fanout-zero row the window is the row's own public triple and nothing else** — no
`Classical.choose` witness enters, because the inactive subformula projections are the literal
`.atom 0`.  `ComputeTable.fanoutComp` is `0` exactly at `OP_0` and `OP_1`, which is the same pair of
opcodes at which G.1 finds the comparison list label-only. -- the paper -/
theorem rowLeafWindow_of_fanout_zero {s : ComputeRowSkeleton} {Λ : ℕ} (hΛ : 1 ≤ Λ)
    (hfan : ComputeTable.fanoutComp s.state = 0)
    (h1 : s.subject.leaves ≤ Λ) (h2 : s.formula.leaves ≤ Λ)
    (h3 : s.evaluation.leaves ≤ Λ) :
    RowLeafWindow Λ s := by
  refine ⟨h1, h2, h3, ?_⟩
  intro i slot
  have hne : ¬ ((i : ℕ) < ComputeTable.fanoutComp s.state) := by
    rw [hfan]; omega
  rw [P8Census.skeletonSubformula, dif_neg hne]
  simpa [Noun.leaves] using hΛ

/-- The two fanout-zero opcodes, recorded so the previous theorem's reach is explicit. -/

theorem fanoutComp_zero_iff_s0_or_s1 (st : ComputeTable.State) :
    ComputeTable.fanoutComp st = 0 ↔ (st = .s0 ∨ st = .s1) := by
  cases st <;> simp [ComputeTable.fanoutComp]

/-- The same, transported to every row of the reconstruction, by the script
`skeletonBounded_of_consDecomposed` already uses. -- the paper -/
theorem rowCellIdentities_on_reconstruction (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (hc : ∀ i : Fin E.cfg.compRows, ConsDecomposedRow (E.semanticData.rows i))
    (h8 : ∀ i : Fin E.cfg.compRows, (E.exec.computeRowAt i).1 ≠ .s8)
    (hcons : ∀ i : Fin E.cfg.compRows, (E.exec.computeRowAt i).1 ≠ .cons) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      RowCellIdentities s := by
  intro s hs
  rw [computeSkeletonRows_of_assembly E P M] at hs
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs
  rw [List.mem_range'] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  simp only [Nat.one_mul]
  have hidx : k < E.cfg.compRows := by
    rw [← E.exec.compute_bfs_length]
    exact hk
  have hlbl : computeLabelAt E P (1 + k) = computeNodeAt E P ⟨k, hidx⟩ := by
    have h1 : (1 + k) - 1 = k := Nat.add_sub_cancel_left 1 k
    simpa [h1] using computeLabelAt_of_index E P (i := 1 + k) (by simpa [h1] using hidx)
  rw [hlbl, computeNodeAt, computeNodeOf]
  exact rowCellIdentities_of_consDecomposed (publicRowNoun_of_execution E ⟨k, hidx⟩)
    (hc ⟨k, hidx⟩) (h8 ⟨k, hidx⟩) (hcons ⟨k, hidx⟩)

section LeafWindowAtF97

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusExecution

local instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)

/-- `1 ≤ Λ` is free at the released fixture: `Λ = 7`. -/
theorem distinctCensus_one_le_Lambda : 1 ≤ (distinctCensusExecution hfirstD).Λ := by
  rw [(distinctCensus_Lambda_and_order hfirstD).1]
  omega

/-- At F97 the reduction's **cell-identity hypothesis is FREE**: §B.0 already inhabits
`ConsDecomposedRow` at every one of the fixture's three rows, and the fixture has no `OP_8` and no
`cons` row, so the two extra identities are vacuous there. -/

theorem distinctCensus_rowCellIdentities
    (P : ResidualPremises (distinctCensusExecution hfirstD))
    (M : MemoryRecordPremises (distinctCensusExecution hfirstD)) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)),
      RowCellIdentities s :=
  rowCellIdentities_on_reconstruction (distinctCensusExecution hfirstD) P M
    (distinctCensus_consDecomposed hfirstD)
    (fun i => by rcases distinctCensus_row_states hfirstD i with h | h <;> rw [h] <;> decide)
    (fun i => by rcases distinctCensus_row_states hfirstD i with h | h <;> rw [h] <;> decide)

/-- **The whole five-field bundle at the released F97 fixture from the paper's window alone.**
`slotSemantics`, `sizeWindowBound`, `skeletonBounded` and `combinedBounded` are already free there
(§B.0, §F); `1 ≤ Λ` is free; and the reduction's cell-identity hypothesis is free too, because §B.0
inhabits `ConsDecomposedRow` at all three rows and the fixture has no `OP_8` and no `cons` row.  So
**the entire bundle at F97 rests on exactly one obligation: the the paper leaf window on the
three reconstructed compute rows.**

**This does NOT inhabit the bundle.**  `RowLeafWindow` is supplied by no field of
`(distinctCensusExecution hfirstD)`, of `P`, of `M`, or of `HonestCommitment.Data` — `E.Λ` occurs in one place
only, `ComputeRowSemanticData.comparison_leaves` on the free `comparisons` list (§C) — so
`CensusRecordPremises` is **still one field short at F97**.  What the theorem records is that the
remaining obligation is now exactly the paper's own λ window on the committed rows, and nothing
else. -/

theorem distinctCensus_censusRecordPremises_of_leafWindow
    (P : ResidualPremises (distinctCensusExecution hfirstD))
    (M : MemoryRecordPremises (distinctCensusExecution hfirstD))
    (hw : ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)),
      RowLeafWindow (distinctCensusExecution hfirstD).Λ s) :
    CensusRecordPremises (distinctCensusExecution hfirstD) P M :=
  distinctCensus_censusRecordPremises_of_census hfirstD P M
    (census_of_leafWindow_on_reconstruction (distinctCensusExecution hfirstD) P M
      (distinctCensus_one_le_Lambda hfirstD) (distinctCensus_rowCellIdentities hfirstD P M) hw)

end LeafWindowAtF97

/-! ## §E. Nothing moved -/

/-- The five census extras are still five named fields. -/

theorem censusRecordPremises_still_five_here {E : BuildableNockExecution F K}
    {P : ResidualPremises E} {M : MemoryRecordPremises E}
    (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } := by
  cases C
  rfl


theorem residual_pair_still_eleven_one_two : 11 + 1 + 2 = 14 := rfl

#print axioms ConsDecomposedRow.formula_bounded
#print axioms ConsDecomposedRow.head_tail_bounded
#print axioms ConsDecomposedRow.decompNoun_bounded
#print axioms ConsDecomposedRow.decompNoun_leaves_le
#print axioms skeletonBounded_of_consDecomposed
#print axioms combinedBounded_of_consDecomposed
#print axioms skeletonBounded_and_combinedBounded_of_consDecomposed
#print axioms consReflection_is_circular_without_a_bound
#print axioms consDecomposed_not_implied_by_bounds
#print axioms sizeWindowBound_is_seed_free
#print axioms sizeWindow_route_pins_the_order
#print axioms consDecomposedRow_cast
#print axioms op5RowData_consDecomposed
#print axioms op1LRowData_consDecomposed
#print axioms op1RRowData_consDecomposed
#print axioms distinctCensus_consDecomposed
#print axioms distinctCensus_skeletonBounded_and_combinedBounded
#print axioms distinctCensus_Lambda_and_order
#print axioms order_le_succ_Lambda_false_at_distinctCensus
#print axioms sizeWindow_gap_at_distinctCensus
#print axioms reconstructed_subformulaNoun_properties
#print axioms s6WindowSkeleton_sizeWindowNouns
#print axioms census_holds_and_sizeWindowBound_fails
#print axioms rowStateNeeds_eta_two_fields
#print axioms census_is_the_leaf_window
#print axioms censusDecompSlots_of_consDecomposed
#print axioms reconstructed_row_state
#print axioms reconstructed_rows_are_nodes
#print axioms sizeWindowBound_of_no_window_states
#print axioms slotSemantics_of_no_lookup_states
#print axioms s0SlotFailRow_slotSemantics_fails
#print axioms s6SmallWindowSkeleton_computeRows
#print axioms window_state_gate_not_necessary
#print axioms lookup_state_gate_not_necessary
#print axioms distinctCensus_row_states
#print axioms distinctCensus_no_window_states
#print axioms distinctCensus_no_lookup_states
#print axioms distinctCensus_sizeWindowBound
#print axioms distinctCensus_slotSemantics
#print axioms distinctCensus_four_census_extras
#print axioms distinctCensus_censusRecordPremises_of_census
#print axioms censusRecordPremises_still_five_here
#print axioms residual_pair_still_eleven_one_two
#print axioms combinedBounded_is_the_same_occurrence_list
#print axioms census_iff_combined_leaf_window
#print axioms census_and_combinedBounded_differ_in_kind
#print axioms reconstructed_row_nouns_are_labels
#print axioms reconstructed_subformula_is_a_chosen_witness
#print axioms reconstructed_s0_comparisons_are_labels
#print axioms edgePairs_left_is_a_child_label
#print axioms wut_leaves
#print axioms tis_leaves
#print axioms incMod_leaves
#print axioms skeletonDec_inactive
#print axioms skeletonDec_leaves_le
#print axioms skeletonComparisons_leavesBounded_of_window
#print axioms mem_computeSkeletonRows_of_inTree
#print axioms census_of_leafWindow
#print axioms leafWindow_does_not_imply_census
#print axioms cellIdentities_state_no_leaf_bound
#print axioms census_of_leafWindow_on_reconstruction
#print axioms skeletonDec_computeSkeletonOf_of_active
#print axioms rowCellIdentities_of_consDecomposed
#print axioms rowLeafWindow_of_fanout_zero
#print axioms fanoutComp_zero_iff_s0_or_s1
#print axioms rowCellIdentities_on_reconstruction
#print axioms distinctCensus_one_le_Lambda
#print axioms distinctCensus_rowCellIdentities
#print axioms distinctCensus_censusRecordPremises_of_leafWindow

end

end Nock.NockVMROM.Thm54.CensusExtraClosure
