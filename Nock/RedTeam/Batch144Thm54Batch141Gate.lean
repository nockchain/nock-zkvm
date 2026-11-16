import Nock.RedTeam.Batch141Thm54CensusTerminal
import Nock.NockVMROM.Thm54.DistinctCensusHonestArrays

/-!
# Independent spec-redteam gate on `Batch141`

**Nothing here
inhabits a named premise, adds a carrier field, weakens a census predicate, withdraws a theorem,
changes a disposition, or ticks a `§J` box.**  `BuildableNockExecution` keeps its fourteen fields,
`HonestCommitment.Data` its sixteen, `ResidualPremises` its **three**, `CensusRecordPremises` its
five, and `BuildablePackage.CommitmentResidual` its twenty-one.  No statement below is a verdict on
the paper construction, which is not in question at any point.

`ResidualPremises` has **three** fields —
`inactiveDec`, `axisAtoms`, `q_eq_ringChar` (`GenericHonestCommitment.lean:791`) — not four.
Every "four" in this file's prose was wrong when
written; the *statement* of `b144_residualPremises_still_four` is a three-field eta and is
unaffected.

## §1. Result 1 — the converse refutation, RE-DERIVED from a new witness, and STRENGTHENED

`Batch141.b141_residual_does_not_imply_check` is the only declaration in the tree that refutes
`residual ⟹ check`, and `AO-126`'s hardening of `AD-3`/`AD-7` rests on it alone.  This section does
not check that proof; it builds a **different** witness by a **different** mechanism and asks the
sharpest question the original leaves open.

`Batch141`'s witness separates at a **`dec`** slot: `bigDecRow.formula =.atom 0` while
`skeletonDec bigDecRow.f_h` is a two-leaf cell.  That row therefore **fails**
`CensusExtraClosure.RowCellIdentities` — `formula_cons` demands
`s.formula =.cell (skeletonDec s.f_h) (skeletonDec s.f_t)`, a *cell*
(the paper, the line `f = cons(f_h, f_t)` at the paper).  And `RowCellIdentities`
is **separately available** in the route: `CensusExtraClosure.distinctCensus_rowCellIdentities`
(`:1795`) discharges it outright at F97, and `AO125.ao125_census_of_check_at_reconCommitment` takes
it as a free input.
So a sceptic can object that at a row satisfying the paper's `cons` equations the extra content the
check carries over the residual is recovered for free by `Lem:decomp` — and that the separation is an artifact of a skeleton
the route never has to consider.

**That objection is answered here, and the answer is that the separation survives.**  `b144MemRow`
separates at a **memory-record** slot instead.  Every state has `1 ≤ recordCount`
(`NockInstances.lean:65`), so address `.memRec 0` is active in **every** row, and the paper's own
description of that slot is `mem_record_1 = ((input_formula, formula_tail), 3, timestamp_1)`.  `RowLeafWindow` names the public triple and the three subformula triples
and nothing else (`CensusExtraClosure.lean:1301-1306`), so it is blind to that slot, and — unlike
the `dec` slots — **no `cons` equation recovers it**: `RowCellIdentities`' five fields
(`CensusExtraClosure.lean:1321-1340`) mention no memory record at all.  Neither do the two
structures that do mention memory records, `ServedLookupBridge.SkeletonSlotSemantics` and
`SkeletonRecordEquations` (`ServedLookupBridge.lean:59-80`), which constrain `memoryRecord 1` only
at `OP_0` and `memoryRecord 2` only at `OP_9` and are therefore **vacuous** at `OP_1`.

`b144_residual_does_not_imply_check` accordingly delivers `RowLeafWindow 2` **and**
`RowCellIdentities` **and** `SkeletonSlotSemantics` **and** `SkeletonRecordEquations` at every
compute row, while `CanonicalCommitmentCheck 97 ⟨·, 2⟩` fails at the same committed bound.  So the
check's leaf conjunct is strictly stronger than the residual **alongside those four
skeleton-layer premises**, which is the exact compiled scope of the theorem.

The route also obtains
`Data.computeOK → ComputeNodesOK → BindComputeRow`, and `Vcomp`'s always-on second conjunct
`pub.mr1 = ⟨pub.f, dec.f_t, 3, pub.ln_prev * inp.α⟩` forces the `mr1` root and the row's formula to share an `enc` fingerprint;
`Batch143`'s own result 2 then forces their leaf counts equal, while `b144MemRow` has 3 leaves
against 2.  So `b144MemRow` is **excluded** once the compute-layer premises are in hand.

What this section achieves is therefore a strict **narrowing**, not a closure: the objection is
moved off the `cons` equations and onto the `mr1` binding, and any future witness must survive
that binding.  `b144_residual_does_not_imply_check` is **true** and its compiled scope (the four
named skeleton-layer predicates) is **exact**; `Batch141`'s result 1 is confirmed at that scope,
and `census` PARKED is undisturbed.

Non-degeneracy is compiled rather than asserted, in both directions and for both witnesses.
`b144_check_holds_at_its_own_bound` shows the same commitment **passes**
`CanonicalCommitmentCheck 97` at its own true bound `3`, so the failure at `2` is exactly the leaf
conjunct at the smaller bound and not a canonical-residue failure; and
`b144_batch141_witness_check_at_its_own_bound` compiles the same fact for `Batch141`'s witness at
its own bound `2`, which `Batch141` states in prose and does not compile.
`b144_rowLeafWindow_is_blind_to_dec_and_memRec` compiles the mechanism attribution itself: the
residual is literally invariant under both fields the check reads.

## §2. Result 2 — inhabitation at F97, re-derived from a SECOND production term

`b144_commitmentResidual_inhabited_at_F97` uses `DistinctCensusHonestArrays.residualHonestD`
(`:537`), built by `HonestCommitment.commitmentResidualOf`, **not** the
`commitmentResidualOfZero`-built `residualD` (`DistinctCensusCommitment.lean:977-978`) that
`Batch141` uses.  `b144_F97_inhabitants_are_the_census_fixture` pins skeleton and window for
**both** terms by `rfl`, so `Batch141`'s pin is re-measured rather than quoted.  The
`Nonempty` statement is confirmed and the recorded distinction stands: what is unavailable is the
strictly different **universal** constructor, and `b144_generic_residual_forces_q_equality`
re-derives why.

## §3. Result 3 — A2 is free, re-derived by a DIFFERENT route

`Batch141` derives the binding through `RawSemanticAssembly.bindsAt_iff_scan.mpr`.
`b144_bindsAt_of_commitmentResidual_direct` derives it from `bindsAt_of_scan`
(`RawSemanticAssembly.lean:638-644`) directly, bypassing the biconditional, from the same three
`CommitmentResidual` fields plus `specializedProblem_seed`, with **no** added hypothesis.
`b144_a2_both_directions` uses `.mp` and `.mpr` in one term.  Confirmed.  Worth recording: the
production constructor `commitmentResidualOf` fills `scan`/`shapeMatch`/`rowFrame` by applying the
`.mp`-side extractors to `D.binds` (`HonestCommitment.lean:987-992`), so on the honest path A2 is a
genuine round trip and "free" is the right word.

## §4. Result 4 — the layer separation, re-derived and sharpened

`b144_census_field_is_over_the_reconstruction` re-extracts the consumed object.
`b144_row_map_does_not_determine_the_reconstruction` strengthens `Batch141`'s coordinate-independence
result from "the two reconstructions carry two arbitrary row skeletons" to
**"the two reconstructions are unequal"**, from an explicit `s₁ ≠ s₂`, and
`b144_layer_separation_is_nonvacuous` supplies a concrete inequality so the hypothesis is
satisfiable at real rows.  Confirmed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch144

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.CensusExtraClosure
open Nock.NockVMROM.Thm54.StrictCommitment
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.RawSemanticAssembly
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## §1. The converse refutation, re-derived from a memory-record witness -/

section Separation

/-- A three-leaf noun, all of whose atoms are `0`. -/
def b144BigNoun : Noun := .cell (.cell (.atom 0) (.atom 0)) (.atom 0)

/-- The `OP_1` row shape with the decomposition noun and the memory record
left free.  `RowLeafWindow` reads neither field. -/
def b144ParamRow (d : Noun) (m : MemRecSkeleton) : ComputeRowSkeleton where
  state := .s1
  subject := .atom 0
  formula := .cell (.atom 0) (.atom 0)
  evaluation := .atom 0
  decomposition := fun _ _ => d
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => m

/-- **The witness.**  An `OP_1` row whose public triple and subformula
projections sit inside the window `2`, whose two active `dec` halves are atoms so the paper's
`f = cons(f_h, f_t)` *holds*, and whose first memory record carries a three-leaf root.  Axis `3` is the paper's own value for that
record. -/
def b144MemRow : ComputeRowSkeleton := b144ParamRow (.atom 0) ⟨b144BigNoun, .atom 0, 3⟩

def b144MemSkeleton : SemanticSkeleton where
  computeTree := .node b144MemRow []
  memoryForest := []

theorem b144MemSkeleton_computeRows :
    computeSkeletonRows b144MemSkeleton = [b144MemRow] := by
  unfold computeSkeletonRows b144MemSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

theorem b144MemSkeleton_memoryRows :
    memorySkeletonRows b144MemSkeleton = [] := by
  simp [memorySkeletonRows, b144MemSkeleton, bfsForest_nil]

/-- **The mechanism attribution, compiled.**  `RowLeafWindow` names the public triple and the three
subformula triples and nothing else (`CensusExtraClosure.lean:1301-1306`), so it is literally
invariant under the decomposition noun and the memory record — the two families of address the
canonical check does read. -/
theorem b144_rowLeafWindow_is_blind_to_dec_and_memRec (Λ : ℕ)
    (d₁ d₂ : Noun) (m₁ m₂ : MemRecSkeleton) :
    RowLeafWindow Λ (b144ParamRow d₁ m₁) ↔ RowLeafWindow Λ (b144ParamRow d₂ m₂) :=
  Iff.rfl

/-- The paper's leaf window at the committed bound `2`. -/
theorem b144MemRow_window : RowLeafWindow 2 b144MemRow := by
  refine ⟨by simp [b144MemRow, b144ParamRow, Noun.leaves],
    by simp [b144MemRow, b144ParamRow, Noun.leaves],
    by simp [b144MemRow, b144ParamRow, Noun.leaves], ?_⟩
  intro i slot
  rw [P8Census.skeletonSubformula]
  split
  · simp [b144MemRow, b144ParamRow, Noun.leaves]
  · simp [Noun.leaves]

/-- **The witness satisfies the paper's five `cons` equations.**  This is what `Batch141`'s witness
does not do, and it is what closes the "recovered for free by `Lem:decomp`" objection. -/
theorem b144MemRow_cellIdentities : RowCellIdentities b144MemRow where
  formula_cons := by
    show (Noun.cell (.atom 0) (.atom 0)) =
      Noun.cell (P8Census.skeletonDec b144MemRow .f_h) (P8Census.skeletonDec b144MemRow .f_t)
    rw [P8Census.skeletonDec, dif_pos (by decide : decActive b144MemRow.state .f_h = true),
      P8Census.skeletonDec, dif_pos (by decide : decActive b144MemRow.state .f_t = true)]
    rfl
  tail_cons := fun h => absurd h (by decide)
  branchTail_cons := fun h => absurd h (by decide)
  push_cons := fun h => absurd h (by decide)
  cons_result := fun h => absurd h (by decide)

/-- The two structures that *do* mention memory records constrain `memoryRecord 1` only at `OP_0`
and `memoryRecord 2` only at `OP_9` (`ServedLookupBridge.lean:59-80`), so both are vacuous at
`OP_1` and neither recovers the slot the separation uses. -/
theorem b144MemRow_slotSemantics : SkeletonSlotSemantics b144MemRow where
  s0_slot := fun h => absurd h (by decide)
  s9_slot := fun h => absurd h (by decide)

theorem b144MemRow_recordEquations : SkeletonRecordEquations b144MemRow where
  s0_record := fun h => absurd h (by decide)
  s9_record := fun h => absurd h (by decide)

/-- Every state has at least one memory record (`NockInstances.lean:65`), so this address is active
in every row and carries the three-leaf root. -/
theorem b144MemRow_memRec_root :
    computeSlotNoun b144MemRow (.memRec 0 .root) = b144BigNoun := by
  rw [computeSlotNoun_memRec_of_active
    (by decide : ((0 : Fin 3) : ℕ) < Nock.Framework.recordCount b144MemRow.state) .root]
  rfl

/-- **Result 1, re-derived independently and narrowed.**  The residual holds at every compute
row of this skeleton — *together with* the paper's five `cons` equations and both memory-record
structures — while `CanonicalCommitmentCheck` **fails** at the same committed bound.  So the check's
leaf conjunct is strictly stronger than the residual alongside **these four skeleton-layer
predicates**, which is this statement's exact scope.

The achievement is a strict **narrowing** of the objection — off the `cons` equations, onto
the `mr1` binding — not its closure. -/
theorem b144_residual_does_not_imply_check :
    (∀ s ∈ computeSkeletonRows b144MemSkeleton,
        RowLeafWindow 2 s ∧ RowCellIdentities s ∧ SkeletonSlotSemantics s ∧
          SkeletonRecordEquations s) ∧
      ¬ CanonicalCommitmentCheck 97 ⟨b144MemSkeleton, 2⟩ := by
  constructor
  · intro s hs
    rw [b144MemSkeleton_computeRows, List.mem_singleton] at hs
    subst hs
    exact ⟨b144MemRow_window, b144MemRow_cellIdentities, b144MemRow_slotSemantics,
      b144MemRow_recordEquations⟩
  · intro h
    have hrow : b144MemRow ∈ computeSkeletonRows
        (⟨b144MemSkeleton, 2⟩ : SkeletonCommitment).skeleton := by
      show b144MemRow ∈ computeSkeletonRows b144MemSkeleton
      rw [b144MemSkeleton_computeRows]
      exact List.mem_singleton_self _
    have hactive : (ComputeSlotAddress.memRec 0 .root) ∈
        activeComputeSlotAddresses b144MemRow.state :=
      (mem_activeComputeSlotAddresses_iff _ _).2 (by decide)
    have hle := (h _ (mem_commitmentNouns_compute hrow hactive)).2
    rw [b144MemRow_memRec_root] at hle
    simp [b144BigNoun, Noun.leaves] at hle

/-! ### Non-degeneracy of both witnesses -/

theorem b144MemRow_slotNoun_cases (a : ComputeSlotAddress) :
    computeSlotNoun b144MemRow a = .atom 0 ∨
      computeSlotNoun b144MemRow a = .cell (.atom 0) (.atom 0) ∨
        computeSlotNoun b144MemRow a = b144BigNoun := by
  cases a with
  | subject => exact Or.inl rfl
  | formula => exact Or.inr (Or.inl rfl)
  | evaluation => exact Or.inl rfl
  | dec slot =>
      refine Or.inl ?_
      show P8Census.skeletonDec b144MemRow slot = .atom 0
      unfold P8Census.skeletonDec
      split <;> rfl
  | sub i slot =>
      refine Or.inl ?_
      show P8Census.skeletonSubformula b144MemRow i slot = .atom 0
      unfold P8Census.skeletonSubformula
      split <;> rfl
  | memRec i slot =>
      have key : computeSlotNoun b144MemRow (.memRec i slot) =
          (if h : (i : ℕ) < Nock.Framework.recordCount b144MemRow.state
            then memRecSkeletonNoun (b144MemRow.memoryRecord i h) slot else .atom 0) := rfl
      rw [key]
      split
      · cases slot
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl
      · exact Or.inl rfl

/-- **Non-degeneracy, this witness.**  The same commitment **passes** the canonical check at its own
true bound `3`, so every committed noun is a canonical residue for `97` and the failure at `2` is
exactly the leaf conjunct at the smaller bound. -/
theorem b144_check_holds_at_its_own_bound :
    CanonicalCommitmentCheck 97 ⟨b144MemSkeleton, 3⟩ := by
  intro n hn
  unfold commitmentNouns at hn
  rw [List.mem_append] at hn
  rcases hn with hn | hn
  · rw [List.mem_flatMap] at hn
    obtain ⟨s, hs, hns⟩ := hn
    rw [show (⟨b144MemSkeleton, 3⟩ : SkeletonCommitment).skeleton = b144MemSkeleton from rfl,
      b144MemSkeleton_computeRows, List.mem_singleton] at hs
    subst hs
    unfold commitmentComputeRowNouns at hns
    rw [List.mem_map] at hns
    obtain ⟨a, _, rfl⟩ := hns
    rcases b144MemRow_slotNoun_cases a with h | h | h <;> rw [h] <;>
      exact ⟨by decide, by decide⟩
  · rw [List.mem_flatMap] at hn
    obtain ⟨s, hs, _⟩ := hn
    rw [show (⟨b144MemSkeleton, 3⟩ : SkeletonCommitment).skeleton = b144MemSkeleton from rfl,
      b144MemSkeleton_memoryRows] at hs
    simp at hs

theorem b144_bigDecRow_slotNoun_cases (a : ComputeSlotAddress) :
    computeSlotNoun Batch141.bigDecRow a = .atom 0 ∨
      computeSlotNoun Batch141.bigDecRow a = .cell (.atom 0) (.atom 0) := by
  cases a with
  | subject => exact Or.inl rfl
  | formula => exact Or.inl rfl
  | evaluation => exact Or.inl rfl
  | dec slot =>
      have key : computeSlotNoun Batch141.bigDecRow (.dec slot) =
          P8Census.skeletonDec Batch141.bigDecRow slot := rfl
      rw [key]
      unfold P8Census.skeletonDec
      split
      · exact Or.inr rfl
      · exact Or.inl rfl
  | sub i slot =>
      refine Or.inl ?_
      show P8Census.skeletonSubformula Batch141.bigDecRow i slot = .atom 0
      unfold P8Census.skeletonSubformula
      split <;> rfl
  | memRec i slot =>
      refine Or.inl ?_
      have key : computeSlotNoun Batch141.bigDecRow (.memRec i slot) =
          (if h : (i : ℕ) < Nock.Framework.recordCount Batch141.bigDecRow.state
            then memRecSkeletonNoun (Batch141.bigDecRow.memoryRecord i h) slot
            else .atom 0) := rfl
      rw [key]
      split
      · cases slot <;> rfl
      · rfl

/-- **Non-degeneracy of `Batch141`'s own witness**, which `Batch141` asserts in prose and does not
compile: `bigDecSkeleton` **passes** `CanonicalCommitmentCheck 97` at its own true bound `2`, so the
canonical-residue conjunct is satisfied there and the failure it exhibits at bound `1` is purely the
leaf conjunct.  Recorded correction: the committed nouns are **not** all `.atom 0` — the two active
`dec` slots are two-leaf cells; what holds is that every *atom* occurring is `0`. -/
theorem b144_batch141_witness_check_at_its_own_bound :
    CanonicalCommitmentCheck 97 ⟨Batch141.bigDecSkeleton, 2⟩ := by
  intro n hn
  unfold commitmentNouns at hn
  rw [List.mem_append] at hn
  rcases hn with hn | hn
  · rw [List.mem_flatMap] at hn
    obtain ⟨s, hs, hns⟩ := hn
    rw [show (⟨Batch141.bigDecSkeleton, 2⟩ : SkeletonCommitment).skeleton =
        Batch141.bigDecSkeleton from rfl,
      Batch141.bigDecSkeleton_computeRows, List.mem_singleton] at hs
    subst hs
    unfold commitmentComputeRowNouns at hns
    rw [List.mem_map] at hns
    obtain ⟨a, _, rfl⟩ := hns
    rcases b144_bigDecRow_slotNoun_cases a with h | h <;> rw [h] <;>
      exact ⟨by decide, by decide⟩
  · rw [List.mem_flatMap] at hn
    obtain ⟨s, hs, _⟩ := hn
    rw [show (⟨Batch141.bigDecSkeleton, 2⟩ : SkeletonCommitment).skeleton =
        Batch141.bigDecSkeleton from rfl] at hs
    simp [memorySkeletonRows, Batch141.bigDecSkeleton, bfsForest_nil] at hs

end Separation

/-! ## §2. `CommitmentResidual` is inhabited at F97 — from a second production term -/

section F97Inhabitation

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment
open Nock.NockVMROM.Thm54.DistinctCensusHonestArrays

local instance prime97b144 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97b144 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

-- Form R leftover first-row counts (live is `chainOneBitWeight`).
variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
include hfirstD

/-- **Result 2, re-derived from a different production term.**  `residualHonestD` is built by
`commitmentResidualOf`, not by the `commitmentResidualOfZero` that `Batch141` uses. -/
theorem b144_commitmentResidual_inhabited_at_F97 :
    Nonempty (BuildablePackage.CommitmentResidual (distinctCensusExecution hfirstD)) :=
  ⟨residualHonestD hfirstD⟩

/-- Both F97 inhabitants are the census fixture, re-measured here rather than quoted. -/
theorem b144_F97_inhabitants_are_the_census_fixture :
    (residualHonestD hfirstD).commitment.skeleton = skelD ∧ (residualHonestD hfirstD).Λ = 7 ∧
      (residualD hfirstD).commitment.skeleton = skelD ∧ (residualD hfirstD).Λ = 7 ∧
        (distinctCensusExecution hfirstD).q = 97 ∧ (distinctCensusExecution hfirstD).Λ = 7 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end F97Inhabitation

section GenericConstructor

variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- The strictly different **universal** form, re-derived: it would force the `q` pin at every
buildable execution, while a buildable execution carries only the inequality. -/
theorem b144_generic_residual_forces_q_equality
    (g : ∀ E : BuildableNockExecution F K, BuildablePackage.CommitmentResidual E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K ∧ E.q ≤ ringChar K :=
  fun E => ⟨(g E).q_eq_ringChar, E.q_le_ringChar⟩

end GenericConstructor

/-! ## §3. A2 is free — re-derived without the biconditional -/

section A2

variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- **Result 3, re-derived by a different route.**  `bindsAt_of_scan` directly, bypassing
`bindsAt_iff_scan`, from three `CommitmentResidual` fields plus `specializedProblem_seed`, with no
added hypothesis. -/
theorem b144_bindsAt_of_commitmentResidual_direct
    (E : BuildableNockExecution F K) (R : BuildablePackage.CommitmentResidual E)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    BindsAt z R.commitment.skeleton
      (specializedProblem R.verifier.raw.timestamp z hz α lmb).cfg
      (specializedProblem R.verifier.raw.timestamp z hz α lmb).exec :=
  bindsAt_of_scan (specializedProblem_seed R.verifier.raw.timestamp z hz α lmb)
    (R.shapeMatch z hz α lmb) (R.rowFrame z hz α lmb) (R.scan z hz α lmb)

/-- Both halves of the same biconditional in one term, so "proved biconditional, usable both ways"
rests on a use of each direction here. -/
theorem b144_a2_both_directions {z : K} {C : SkeletonCommitment}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : BindsAt z C.skeleton cfg exec) :
    (ExecTreeShapeMatchesAt C exec ∧ RowFrameChecksAt z C exec ∧
        ActiveFingerprintChecksAt z C exec) ∧
      BindsAt z C.skeleton cfg exec :=
  ⟨⟨(bindsAt_iff_scan.mp h).2.1, (bindsAt_iff_scan.mp h).2.2.1,
      (bindsAt_iff_scan.mp h).2.2.2⟩,
    bindsAt_iff_scan.mpr (bindsAt_iff_scan.mp h)⟩

end A2

/-! ## §4. The layer separation -/

/-- **Result 4, first half.**  The consumed object of the `census` field is over the
reconstruction. -/
theorem b144_census_field_is_over_the_reconstruction
    {E : BuildableNockExecution F K} {P : ResidualPremises E} {M : MemoryRecordPremises E}
    (C : CensusRecordPremises E P M) :
    EdgeComparisonCensus.CombinedSkeletonCensus K
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ :=
  C.census

/-- **Result 4, second half, strengthened.**  `Batch141` shows the two reconstructions carry two
arbitrary row skeletons; this shows the two reconstructions are **unequal**, from an explicit
`s₁ ≠ s₂`, while the `row` component — all `Data.compute_rows` pins — is identical.  So the binding
layer cannot determine the layer `census` is stated over. -/
theorem b144_row_map_does_not_determine_the_reconstruction
    (stamp : ComputeTimestampRow) (row : ComputeTable.State × ComputeTable.DTcomp K)
    {s₁ s₂ : ComputeRowSkeleton} (hne : s₁ ≠ s₂) :
    mapNTree ComputeNode.row (NTree.node (⟨s₁, stamp, row⟩ : ComputeNode K) []) =
        mapNTree ComputeNode.row (NTree.node (⟨s₂, stamp, row⟩ : ComputeNode K) []) ∧
      skeletonOfNodes (NTree.node (⟨s₁, stamp, row⟩ : ComputeNode K) [])
          ([] : List (NTree (MemoryNode K))) ≠
        skeletonOfNodes (NTree.node (⟨s₂, stamp, row⟩ : ComputeNode K) [])
          ([] : List (NTree (MemoryNode K))) := by
  refine ⟨by simp [mapNTree], fun h => hne ?_⟩
  have hlab := congrArg (fun S => S.computeTree.label) h
  simpa [skeletonOfNodes, mapNTree] using hlab

/-- …and the hypothesis is satisfiable at real rows, so the previous statement is not vacuous. -/
theorem b144_layer_separation_is_nonvacuous : AO125.atomRow ≠ AO125.wideRow := by
  intro h
  have hf := congrArg ComputeRowSkeleton.formula h
  simp [AO125.atomRow, AO125.wideRow] at hf

/-! ## §5. Nothing moved -/

/-- `CensusRecordPremises` is still five named fields. -/
theorem b144_censusRecordPremises_still_five {E : BuildableNockExecution F K}
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

/-- `ResidualPremises` is still exactly its named fields — **three** of them, as the eta below
shows: `axisAtoms`, `inactiveDec`, `q_eq_ringChar`. -/
theorem b144_residualPremises_still_four {E : BuildableNockExecution F K}
    (P : ResidualPremises E) :
    P =
      { axisAtoms := P.axisAtoms
        inactiveDec := P.inactiveDec
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

/-! ## §6. Section 2 — the remaining ungated load-bearing results, in `§J.5.2`'s order

### (a) `Batch140.b140_census_does_not_imply_rowLeafWindow`

The claim is that `CombinedSkeletonCensus K s3WindowSkeleton 2` holds while `RowLeafWindow Λ` fails
at every `Λ < 4`, so the two predicates are independent in both directions and `RowLeafWindow` is not
a relabelling of `census`.  The vacuity risk is that the census half is a conjunction over an empty
list, since the witness is a one-row tree with an empty memory forest and the `edges` component is
therefore trivially satisfied.  **It is not vacuous.**
`BoundSemanticTrace.skeletonPairs` (`:100-106`) always contains the three public-claim pairs, so
`b144_b140_census_is_tight_at_two` compiles that the same census **fails** at `Λ = 1`: the census at
`Λ = 2` is tight, and the `p8` component has real content.  And the window failure is exactly the
four-leaf noun and not a defect of the row: `b144_b140_s3WindowRow_window_at_four` compiles that the
same row **satisfies** `RowLeafWindow 4`, its own true bound.  Confirmed.

### (b) `Batch140.b140_distinctCensus_censusRecordPremises_of_triples_and_op5` and `b140_s5_third_subformula_is_atom`

`b144_s5_third_subformula_is_atom` re-derives the second directly from
`ComputeTable.fanoutComp.s5 = 2` (`NockVM.lean:157-159`), and states the arithmetic alongside it so
the reader need not look it up.  For the first, the question a gate must answer is whether the
"reduction to two inputs" is exactly the residual or a weakening.  The honest answer is compiled in
two parts.  `b144_two_inputs_are_exactly_the_residual` shows the **unrestricted** two-input form is
*equivalent* to `RowLeafWindow` at every row, over every skeleton and every `Λ`, so nothing is lost
in that split.  `Batch140`'s `hop5` is weaker than that unrestricted form — it asks for the
subformula bound only at `OP_5` rows — and `b144_op1_rows_need_no_subformula_input` compiles why it
suffices at F97: `ComputeTable.fanoutComp.s1 = 0`, so at an `OP_1` row every subformula projection
is the literal `.atom 0` and needs only `1 ≤ Λ`.  Combined with `Batch140`'s own state
classification (every reconstructed row is `OP_5` or `OP_1`), the reduction is exact **at F97** and
strictly weaker than the residual in general.  Confirmed, with that scope stated.

### (c) `AO125.ao125_identification_reduces_to_node_equality` and `ao125_check_at_reconCommitment_entails_the_residual`

`b144_check_at_reconCommitment_entails_the_residual` re-derives the second **independently of
`Batch140`'s helper**, from `CanonicalCommitmentCheck.computeSlot_leaves` at
`AO125.ao125_reconCommitment E P M`, where the committed bound is `E.Λ` by `rfl`.  The `AO125`
declaration is a re-export of `Batch140.b140_rowLeafWindow_of_canonicalCommitmentCheck`, so this
closes the residue `§J.5.2` item (c) names.  Confirmed.

For the first: `b144_data_skeleton_is_skeletonOfNodes` pins that `Data.skeleton` *is*
`skeletonOfNodes D.computeNodes D.memoryNodes` by `rfl`, which is what makes the statement a
reduction rather than a bundling, and `b144_identification_reduces_to_node_equality` re-derives the
conclusion.  **One precision, recorded because it is the same shape as §1's:** node equality is
*sufficient* for what wire (a) needs and is **strictly stronger** than it.  What the published
commitment `⟨D.skeleton, D.nounSizeBound⟩` requires is **skeleton** equality, and
`skeletonOfNodes` forgets `stamp` and `row` — `b144_skeleton_equality_does_not_give_node_equality`
compiles that two nodes agreeing only on `skel` already give equal reconstructions, with a concrete
distinct pair from `ComputeTimestampRow.lnPrevExponent` so the statement is not vacuous.  So `AO125`
§B's *theorem* is sound and used in the direction that is sound; its *description* "(a) **is** node
equality" should read "reduces to node equality, which is sufficient and strictly stronger".

### (d) `AO125.ao125_nounSizeBound_is_load_bearing`

`Batch141` §4 re-stated this without re-deriving it.  `b144_nounSizeBound_is_load_bearing`
re-derives it from a **different** witness — this pass's own `⟨b144MemSkeleton, 3⟩` — and adds the
non-vacuity half in the same statement: the check holds at the witness's own committed bound `3`,
`RowLeafWindow 1` fails, and `RowLeafWindow 3` holds.  So the failure at `1` is exactly the untied
scalar `C.nounSizeBound ≤ Λ` and the obligation is genuine off the assembly path.  Confirmed.
-/

section Section2

/-- Leaf windows are monotone in the bound. -/
theorem b144_rowLeafWindow_mono {Λ Λ' : ℕ} (h : Λ ≤ Λ') {s : ComputeRowSkeleton}
    (hw : RowLeafWindow Λ s) : RowLeafWindow Λ' s :=
  ⟨hw.1.trans h, hw.2.1.trans h, hw.2.2.1.trans h, fun i slot => (hw.2.2.2 i slot).trans h⟩

/-! ### (a) -/

/-- **(a), non-vacuity of the census half.**  `skeletonPairs` always contains the three public-claim
pairs (`BoundSemanticTrace.lean:100-106`), so the census at `Λ = 2` is **tight**: it fails at
`Λ = 1`, and the `p8` component therefore has real content rather than quantifying over nothing. -/
theorem b144_b140_census_is_tight_at_two :
    ¬ EdgeComparisonCensus.CombinedSkeletonCensus K Batch140.s3WindowSkeleton 1 := by
  intro h
  have hmem : (Batch140.s3WindowSkeleton.computeTree.label.formula,
      Batch140.s3WindowSkeleton.publicClaim.formula) ∈
      BoundSemanticTrace.skeletonPairs K Batch140.s3WindowSkeleton := by
    unfold BoundSemanticTrace.skeletonPairs
    simp
  have hle := (h.p8.leaves_bounded _ hmem).1
  simp [Batch140.s3WindowSkeleton, Batch140.s3WindowRow, Noun.leaves] at hle

/-- **(a), non-vacuity of the window half.**  The same row satisfies `RowLeafWindow` at its own true
bound `4`, so the failure at every `Λ < 4` is exactly the four-leaf subformula projection and not a
defect of the witness. -/
theorem b144_b140_s3WindowRow_window_at_four : RowLeafWindow 4 Batch140.s3WindowRow := by
  refine ⟨by simp [Batch140.s3WindowRow, Noun.leaves],
    by simp [Batch140.s3WindowRow, Noun.leaves],
    by simp [Batch140.s3WindowRow, Noun.leaves], ?_⟩
  intro i slot
  rw [P8Census.skeletonSubformula]
  split
  · simp only [Batch140.s3WindowRow]
    split
    · simp [fourLeaves_leaves]
    · simp [Noun.leaves]
  · simp [Noun.leaves]

/-! ### (b) -/

/-- **(b), re-derived directly** from `ComputeTable.fanoutComp.s5 = 2`, with the arithmetic stated
alongside the conclusion. -/
theorem b144_s5_third_subformula_is_atom {s : ComputeRowSkeleton} (h : s.state = .s5)
    (slot : TripleSlot) :
    P8Census.skeletonSubformula s 2 slot = .atom 0 ∧ ComputeTable.fanoutComp .s5 = 2 := by
  refine ⟨?_, by decide⟩
  rw [P8Census.skeletonSubformula, dif_neg (by rw [h]; decide)]

/-- **(b), the split is exact in the unrestricted form.**  The two-input shape — public triples plus
subformula projections — is *equivalent* to `RowLeafWindow` at every row, over every skeleton and
every bound.  So nothing is lost in the split itself. -/
theorem b144_two_inputs_are_exactly_the_residual {S : SemanticSkeleton} {Λ : ℕ} :
    (∀ s ∈ computeSkeletonRows S, RowLeafWindow Λ s) ↔
      ((∀ s ∈ computeSkeletonRows S,
          s.subject.leaves ≤ Λ ∧ s.formula.leaves ≤ Λ ∧ s.evaluation.leaves ≤ Λ) ∧
        ∀ s ∈ computeSkeletonRows S, ∀ (i : Fin 3) (slot : TripleSlot),
          (P8Census.skeletonSubformula s i slot).leaves ≤ Λ) := by
  constructor
  · intro h
    exact ⟨fun s hs => ⟨(h s hs).1, (h s hs).2.1, (h s hs).2.2.1⟩,
      fun s hs => (h s hs).2.2.2⟩
  · intro h s hs
    exact ⟨(h.1 s hs).1, (h.1 s hs).2.1, (h.1 s hs).2.2, h.2 s hs⟩

/-- **(b), why `Batch140`'s weaker `OP_5`-only input suffices at F97.**  `fanoutComp.s1 = 0`, so at
an `OP_1` row every subformula projection is the literal `.atom 0` and needs only `1 ≤ Λ`. -/
theorem b144_op1_rows_need_no_subformula_input {s : ComputeRowSkeleton} (h : s.state = .s1)
    (i : Fin 3) (slot : TripleSlot) :
    P8Census.skeletonSubformula s i slot = .atom 0 ∧ ComputeTable.fanoutComp .s1 = 0 := by
  refine ⟨?_, by decide⟩
  rw [P8Census.skeletonSubformula, dif_neg (by rw [h]; simp [ComputeTable.fanoutComp])]

/-! ### (c) -/

section ReconCommitment

variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- The published commitment's skeleton **is** the reconstruction of its own nodes, by `rfl`.  This is
what makes `AO125` §B a reduction rather than a bundling. -/
theorem b144_data_skeleton_is_skeletonOfNodes
    {E : BuildableNockExecution F K} (D : Data E) :
    D.skeleton = skeletonOfNodes D.computeNodes D.memoryNodes :=
  rfl

/-- **(c), first half, re-derived.** -/
theorem b144_identification_reduces_to_node_equality
    {E : BuildableNockExecution F K} (D : Data E)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (hc : D.computeNodes = computeNodesOf E P)
    (hm : D.memoryNodes = memoryNodesOf E M) :
    D.skeleton = skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M) := by
  rw [b144_data_skeleton_is_skeletonOfNodes D, hc, hm]

/-- **(c), the precision.**  Node equality is *sufficient* for wire (a) and **strictly stronger**
than it: `skeletonOfNodes` forgets `stamp` and `row`, so two nodes agreeing only on `skel` already
give equal reconstructions.  The concrete pair differs in `ComputeTimestampRow.lnPrevExponent`, so
the statement is not vacuous. -/
theorem b144_skeleton_equality_does_not_give_node_equality
    (skel : ComputeRowSkeleton) (st : ComputeTable.State)
    (row : ComputeTable.State × ComputeTable.DTcomp K) (re : Fin 3 → ℕ) :
    skeletonOfNodes
        (NTree.node (⟨skel, ⟨st, 0, 0, re⟩, row⟩ : ComputeNode K) [])
        ([] : List (NTree (MemoryNode K))) =
      skeletonOfNodes
        (NTree.node (⟨skel, ⟨st, 1, 0, re⟩, row⟩ : ComputeNode K) [])
        ([] : List (NTree (MemoryNode K))) ∧
    (⟨skel, ⟨st, 0, 0, re⟩, row⟩ : ComputeNode K) ≠ ⟨skel, ⟨st, 1, 0, re⟩, row⟩ := by
  refine ⟨by simp [skeletonOfNodes, mapNTree], fun h => ?_⟩
  have := congrArg (fun n => (ComputeNode.stamp n).lnPrevExponent) h
  simp at this

/-- **(c), second half, re-derived independently of `Batch140`'s helper.**  At
`AO125.ao125_reconCommitment` the committed bound is `E.Λ` by `rfl`, so the check hands back exactly
the residual on every reconstructed row. -/
theorem b144_check_at_reconCommitment_entails_the_residual {p : ℕ}
    (E : BuildableNockExecution F K) (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (hΛ : 1 ≤ E.Λ)
    (h : CanonicalCommitmentCheck p (AO125.ao125_reconCommitment E P M)) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      RowLeafWindow E.Λ s := by
  intro s hs
  have hs' : s ∈ computeSkeletonRows (AO125.ao125_reconCommitment E P M).skeleton := hs
  have key : ∀ a : ComputeSlotAddress, computeSlotActive s.state a = true →
      (computeSlotNoun s a).leaves ≤ E.Λ := fun a ha =>
    h.computeSlot_leaves hs' ((mem_activeComputeSlotAddresses_iff _ _).2 ha)
  refine ⟨key .subject rfl, key .formula rfl, key .evaluation rfl, ?_⟩
  intro i slot
  by_cases hi : (i : ℕ) < ComputeTable.fanoutComp s.state
  · rw [P8Census.skeletonSubformula, dif_pos hi]
    have hk := key (.sub i slot) (by simp [computeSlotActive, hi])
    rwa [computeSlotNoun_sub_of_active hi slot] at hk
  · rw [P8Census.skeletonSubformula, dif_neg hi]
    simpa [Noun.leaves] using hΛ

end ReconCommitment

/-! ### (d) -/

/-- **(d), re-derived from a different witness, with its non-vacuity half in the same statement.**
The check holds at the witness's own committed bound `3`; `RowLeafWindow 1` fails; `RowLeafWindow 3`
holds.  So the untied scalar `C.nounSizeBound ≤ Λ` is load-bearing and the failure at `1` is not a
defect of the witness. -/
theorem b144_nounSizeBound_is_load_bearing :
    CanonicalCommitmentCheck 97 ⟨b144MemSkeleton, 3⟩ ∧
      ¬ (⟨b144MemSkeleton, 3⟩ : SkeletonCommitment).nounSizeBound ≤ 2 ∧
        ¬ (∀ s ∈ computeSkeletonRows b144MemSkeleton, RowLeafWindow 1 s) ∧
          ∀ s ∈ computeSkeletonRows b144MemSkeleton, RowLeafWindow 3 s := by
  refine ⟨b144_check_holds_at_its_own_bound, by decide, ?_, ?_⟩
  · intro h
    have hrow : b144MemRow ∈ computeSkeletonRows b144MemSkeleton := by
      rw [b144MemSkeleton_computeRows]; exact List.mem_singleton_self _
    have := (h b144MemRow hrow).2.1
    simp [b144MemRow, b144ParamRow, Noun.leaves] at this
  · intro s hs
    rw [b144MemSkeleton_computeRows, List.mem_singleton] at hs
    subst hs
    exact b144_rowLeafWindow_mono (by omega) b144MemRow_window

end Section2

#print axioms b144_rowLeafWindow_is_blind_to_dec_and_memRec
#print axioms b144MemRow_window
#print axioms b144MemRow_cellIdentities
#print axioms b144MemRow_slotSemantics
#print axioms b144MemRow_recordEquations
#print axioms b144MemRow_memRec_root
#print axioms b144_residual_does_not_imply_check
#print axioms b144MemRow_slotNoun_cases
#print axioms b144_check_holds_at_its_own_bound
#print axioms b144_bigDecRow_slotNoun_cases
#print axioms b144_batch141_witness_check_at_its_own_bound
#print axioms b144_commitmentResidual_inhabited_at_F97
#print axioms b144_F97_inhabitants_are_the_census_fixture
#print axioms b144_generic_residual_forces_q_equality
#print axioms b144_bindsAt_of_commitmentResidual_direct
#print axioms b144_a2_both_directions
#print axioms b144_census_field_is_over_the_reconstruction
#print axioms b144_row_map_does_not_determine_the_reconstruction
#print axioms b144_layer_separation_is_nonvacuous
#print axioms b144_censusRecordPremises_still_five
#print axioms b144_residualPremises_still_four
#print axioms b144_rowLeafWindow_mono
#print axioms b144_b140_census_is_tight_at_two
#print axioms b144_b140_s3WindowRow_window_at_four
#print axioms b144_s5_third_subformula_is_atom
#print axioms b144_two_inputs_are_exactly_the_residual
#print axioms b144_op1_rows_need_no_subformula_input
#print axioms b144_data_skeleton_is_skeletonOfNodes
#print axioms b144_identification_reduces_to_node_equality
#print axioms b144_skeleton_equality_does_not_give_node_equality
#print axioms b144_check_at_reconCommitment_entails_the_residual
#print axioms b144_nounSizeBound_is_load_bearing

end

end Nock.RedTeam.Batch144
