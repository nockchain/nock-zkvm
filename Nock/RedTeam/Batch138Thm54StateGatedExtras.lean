import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.DistinctCensusCommitment
import Nock.RedTeam.Batch101Thm54MemoryAssembly
import Nock.RedTeam.Batch136Thm54CensusExtras

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!

Nothing here weakens a census predicate, adds a carrier
field, unparks `PairedRecordLayout`, or ticks a `§J` checkbox.

Both types over which every earlier fixture statement is quantified are **inhabited** at the released
F97 `distinctCensusExecution hfirstD`, and the witnesses are compiled here:

* `b138_residualPremises : ResidualPremises (distinctCensusExecution hfirstD)`;
* `b138_memoryRecordPremises : MemoryRecordPremises (distinctCensusExecution hfirstD)`.

Both are kernel-clean.  So `distinctCensus_four_census_extras` and
`distinctCensus_censusRecordPremises_of_census` are instantiable at a real `(P, M)` pair
(`b138_four_census_extras_at_a_witness`, `b138_censusRecordPremises_of_census`), and the four
discharged fields are statements about a concrete reconstructed skeleton rather than a `∀` over a
possibly-empty type.

Both are **inhabited**.

### Why each field goes through, at this fixture

`ResidualPremises` has four fields and none of them is hard here.  `inactiveDec` is
`InactiveDecPadding` on the three rows of `execution_rowsD.1`, and every inactive `Dec` slot of
`op5Dec` / `op1DecOf` is literally `0`.  `axisAtoms` is gated on `.s0` / `.s9` and the fixture's
rows are `.s5, .s1, .s1` (`distinctCensus_row_states`), so both conjuncts are discharged by their
own gates — the same mechanism the earlier §F uses.  `firstLine` is `op5PubD.ln_prev = 1`, which is how
the row is written (`computePubAtD_zero`).  `q_eq_ringChar` is `ringChar_K97`.

`MemoryRecordPremises` has two.  `axisNat` is already derived from `E` generically
(`GenericHonestData.axisNat_of_execution`, consumed through
`memoryRecordPremises_of_timestampClosed`), so only `timestampClosed` is at issue, and at this
fixture it is a **finite read of the record column**: the twenty-one memory rows are
`memoryLabelsD`, exactly eight of them are `read_root` / `verify_child` (hence
`memoryMemRecKind … = .active`), and each of those eight carries one of `recF`, `recT`, `recL`,
`recR`, whose `ts` fields are `alphaD`, `alphaD ^ 2`, `alphaD ^ 3`, `alphaD ^ 4`.  The exponents are
`1, 2, 3, 4`.  The thirteen `decompose` / `halt` rows carry `MemRec.zero` and are `.padding`, so the
premise never fires on them.

### The parked `PairedRecordLayout` does NOT gate this

It does not, and the distinction is between two different objects:

* the **generic named premise** `timestampClosed` on an arbitrary `E` is contingent on
  `PairedRecordLayout` (`GenericHonestData.timestampClosed_of_paired_record_layout`), and that row
  is parked and stays parked and untouched here;
* the **fixture instance** at `distinctCensusExecution hfirstD` is a closed finite statement about a
  concrete record column and needs no permutation at all.

`b138_pairedRecordLayout_is_a_second_route` places the two side by side.  This is exactly the F73
pattern: `Batch101.concreteMemoryRecordPremises` discharged the same field at `concreteExecution`
without `PairedRecordLayout`, at the `axisNat` stage, and nothing about that was ever taken to unpark
anything.  Inhabiting a premise **at a fixture** is a non-vacuity witness; it is not closure of the
generic named premise, and §J.1/§J.1.P are unaffected.

## The honest reading of "four of five at F97"

> At the released F97 `distinctCensusExecution hfirstD`, and for **every** `ResidualPremises` /
> `MemoryRecordPremises` pair over that execution — a pair which **exists** — four of the five
> `CensusRecordPremises` fields hold over the reconstruction
> `skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)` with no carrier field added:
> `slotSemantics` and `sizeWindowBound` because the fixture's three compute rows are `.s5, .s1, .s1`
> and so avoid the opcodes that gate them, `skeletonBounded` and `combinedBounded` from §B.0's
> `cons` object.  The fifth, `census`, remains a hypothesis and needs the carrier program's `C2`.
> This is a statement about that fixture at that state profile, **not** about executions in general
> — at an OP3/OP4/OP6 row `sizeWindowBound` fails and at an OP0/OP9 row `slotSemantics` fails — and
> it is **not** an inhabited `CensusRecordPremises`, because `census` is not supplied.

The earlier §F preamble and its two per-theorem docstrings already say all of this correctly, with one
sentence now out of date: the §F "Quantifier caveat" says "Neither type is known to be inhabited in
this build", and `distinctCensus_censusRecordPremises_of_census` repeats "`P` / `M` are universally
quantified over types not known to be inhabited in this build". The rest of both docstrings, including the
"not an inhabitation" warning about `census`, stands verbatim.

**Item 6 — the generic state-gated implications: CONFIRMED, and they are the durable result.**  §G
re-derives both from the two definitions rather than by re-instantiating the earlier theorems.  The
mechanism is isolated in two lemmas that mention no execution and no fixture:
`b138_requiredSizeWindowNouns_empty_off_gate` (the emitter is `[]` off `{.s3, .s4, .s6}`) and
`b138_skeletonSlotSemantics_of_off_gate` (both clauses are gated on `{.s0, .s9}`), and the hinge is
`b138_reconstructed_row_state`, which is `rfl`.  §G.1 then covers the **states the earlier witnesses do
not reach**: the earlier analysis refutes the conclusion at OP6 and OP0 and shows non-necessity there, and this
module does the same at **OP3** (`b138_window_gate_not_removable_at_s3`,
`b138_window_gate_not_necessary_at_s3`) and at **OP9** (`b138_lookup_gate_not_removable_at_s9`,
`b138_lookup_gate_not_necessary_at_s9`).  Between the two batches every state named in either
hypothesis is covered in both directions, so neither gate is decorative and neither theorem is its
own conclusion renamed at any gated state.  These two implications are carrier-free and
fixture-independent and would stand unchanged even if §1 had gone the other way.

(i)
`b138_four_census_extras_at_a_witness` and `b138_sizeWindowBound_of_no_window_states` /
`b138_slotSemantics_of_no_lookup_states` write `skeletonOfNodes (computeNodesOf E P)
(memoryNodesOf E M)` out in full in statements written here and are discharged by, respectively,
The earlier theorem and independent proofs — so the object those theorems are about is the
reconstruction, with `P` and `M` bound outside the conjunction. (ii) The decisive one, measured
outside the build: `DistinctCensusCommitment.skelD` is **not in the import closure** of
`CensusExtraClosure`, so a silent `skelD` use is not merely absent but impossible in that
environment. Textually, all five `skelD` occurrences in `CensusExtraClosure.lean` are inside
docstrings.

Negatively, measured outside the
build: dropping `census` from the structure instance gives `Fields missing: census`, and dropping a
second field gives `Fields missing: sizeWindowBound`. Lean's structure-instance elaborator rejects
any omission, so "exactly one field remains" is enforced by the typechecker and not asserted.

The table header at `1912` is `OP_0 … OP_6`, so on row `1921` the fifth data column is
`OP_4` with `(z, 0, ⊥)` and on row `1927` the seventh is `OP_6` with `(z, 0 ⊥)` — both correct. Two refinements of the earlier three flagged `1716` point-cites: `ComputeTable.lean:681`'s `1716` is
**not** misplaced — that docstring covers `WF`'s `size8` / `size11` fields as well as `rlc5`, and
`1716` is exactly the opcodes-8/11 paragraph; what is missing there and at
`DistinctCensusExecution.lean:26` is `1991`, the home of EC.5.5 itself. And `AIR.lean:410`'s `1716`
supports the `z ≠ 0` content it is attached to; `1698` is the home of the *term* `rap_inputs`, so
`1698` should be **added**, not substituted. Two further sites carry the same `1716` for the same
`z ≠ 0` claim and the earlier analysis did not list them: `AIR.lean:644` and `AIR.lean:1179`. None of this is a
mathematical defect and none is repaired here.

## Ticking: NOTHING IS TICKED, and the reason is not budget

Both happened.

1. `sizeWindowBound` needs design `C2` and `slotSemantics` needs design `C5`;
   neither object exists, so neither row is done on its own terms.
2. **The premises are not closed generically, and that is compiled.**
   `b138_window_gate_not_removable_at_s3` and `b138_lookup_gate_not_removable_at_s9`, with the earlier analysis's
   OP6 and OP0 witnesses, refute both conclusions at gated rows.  A tick would read as "the premise
   is resolved"; it is resolved at state-eligible executions only.
3.

What IS established, and is the correct thing to record instead of a tick: the two **generic**
state-gated implications are confirmed independently and are carrier-free; the **fixture** instance
at F97 is confirmed and is now **non-vacuous** at a compiled `(P, M)` pair; and `census` is
mechanically the only field left there.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch138

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.CensusExtraClosure

noncomputable section

section Fixture

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusExecution

local instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic

-- Form R leftover first-row `counts = 0` / `indicator = 0` (live is `chainOneBitWeight`).
variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)

/-! ## §A. `ResidualPremises` at the released F97 fixture -/

theorem b138_inactiveDec : InactiveDecPaddingExec (distinctCensusExecution hfirstD).exec :=
  trivial

def b138_residualPremises : ResidualPremises (distinctCensusExecution hfirstD) where
  inactiveDec := b138_inactiveDec hfirstD
  axisAtoms := by
    intro i
    refine ⟨?_, ?_⟩ <;> intro h <;>
      rcases distinctCensus_row_states hfirstD i with hs | hs <;> rw [hs] at h <;>
        exact absurd h (by decide)
  q_eq_ringChar := ringChar_K97.symm

theorem b138_residualPremises_nonempty :
    Nonempty (ResidualPremises (distinctCensusExecution hfirstD)) :=
  ⟨b138_residualPremises hfirstD⟩

/-! ## §B. `MemoryRecordPremises` at the released F97 fixture -/

theorem b138_timestampClosed :
    ∀ i : Fin (distinctCensusExecution hfirstD).cfg.memRows,
      memoryMemRecKind ((distinctCensusExecution hfirstD).exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt (distinctCensusExecution hfirstD).cfg.challenges.α
          ((distinctCensusExecution hfirstD).exec.memoryRowAt i).2.2.mem.ts := by
  intro i
  have hmem : (distinctCensusExecution hfirstD).exec.memoryRowAt i ∈ memoryLabelsD := by
    rw [← execution_rowsD.2]
    exact ExactExecution.memoryRowAt_mem _ i
  revert hmem
  generalize (distinctCensusExecution hfirstD).exec.memoryRowAt i = r
  intro hmem
  simp only [memoryLabelsD, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ => ⟨1, by simp [lblOf, pN1, readPub, recF]; rfl⟩
  · exact fun h => absurd h (by decide)
  · exact fun h => absurd h (by decide)
  · exact fun _ => ⟨2, by simp [lblOf, pN4, readPub, recT]; rfl⟩
  · exact fun _ => ⟨1, by simp [lblOf, pN5, verifyPub, recF]; rfl⟩
  · exact fun h => absurd h (by decide)
  · exact fun _ => ⟨3, by simp [lblOf, pN7, readPub, recL]; rfl⟩
  · exact fun _ => ⟨4, by simp [lblOf, pN15, readPub, recR]; rfl⟩
  · exact fun _ => ⟨2, by simp [lblOf, pN8, verifyPub, recT]; rfl⟩
  · exact fun h => absurd h (by decide)
  · exact fun h => absurd h (by decide)
  · exact fun h => absurd h (by decide)
  · exact fun _ => ⟨4, by simp [lblOf, pN18, verifyPub, recR]; rfl⟩
  · exact fun h => absurd h (by decide)
  · exact fun _ => ⟨3, by simp [lblOf, pN11, verifyPub, recL]; rfl⟩
  · exact fun h => absurd h (by decide)
  · exact fun h => absurd h (by decide)
  · exact fun h => absurd h (by decide)
  · exact fun h => absurd h (by decide)
  · exact fun h => absurd h (by decide)
  · exact fun h => absurd h (by decide)

def b138_memoryRecordPremises : MemoryRecordPremises (distinctCensusExecution hfirstD) :=
  GenericHonestData.memoryRecordPremises_of_timestampClosed (distinctCensusExecution hfirstD)
    (b138_timestampClosed hfirstD) (DistinctCensusCommitment.honestVerD hfirstD)

theorem b138_memoryRecordPremises_nonempty :
    Nonempty (MemoryRecordPremises (distinctCensusExecution hfirstD)) :=
  ⟨b138_memoryRecordPremises hfirstD⟩

/-- **`timestampClosed` at the released fixture does NOT go through the parked
`PairedRecordLayout`.**  `RowLayout.PairedRecordLayout` is a *sufficient* generic route
(`GenericHonestData.timestampClosed_of_paired_record_layout`), and it is parked; but at this fixture
the field is read off the concrete record column, so `b138_timestampClosed` is independent of it.
The abstract statement below is a re-instantiation of the generic bridge, recorded side by side with
the fixture proof to make the two routes visibly distinct — nothing here inhabits, unparks, or
weakens `PairedRecordLayout`. -/

theorem b138_pairedRecordLayout_is_a_second_route
    (h : RowLayout.PairedRecordLayout (distinctCensusExecution hfirstD).exec) :
    (∀ i : Fin (distinctCensusExecution hfirstD).cfg.memRows,
        memoryMemRecKind ((distinctCensusExecution hfirstD).exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt (distinctCensusExecution hfirstD).cfg.challenges.α
            ((distinctCensusExecution hfirstD).exec.memoryRowAt i).2.2.mem.ts) ∧
      (∀ i : Fin (distinctCensusExecution hfirstD).cfg.memRows,
        memoryMemRecKind ((distinctCensusExecution hfirstD).exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt (distinctCensusExecution hfirstD).cfg.challenges.α
            ((distinctCensusExecution hfirstD).exec.memoryRowAt i).2.2.mem.ts) :=
  ⟨GenericHonestData.timestampClosed_of_paired_record_layout
      (DistinctCensusCommitment.honestVerD hfirstD) h,
    b138_timestampClosed hfirstD⟩

/-! ## §C. Consequence — the earlier headline is NOT vacuous

Both `∀`-bound premise types of `distinctCensus_four_census_extras` and
`distinctCensus_censusRecordPremises_of_census` are inhabited at the released F97 fixture, so those
two theorems are instantiable at a real `(P, M)` pair.  The four fields are genuinely held there;
the fifth, `census`, is still a hypothesis. -/

/-- **The four extras, at an inhabited `(P, M)` pair.**  This is the earlier headline with the
quantifier discharged: it is a closed statement about concrete reconstructed skeleton
`skeletonOfNodes (computeNodesOf … b138_residualPremises hfirstD) (memoryNodesOf … b138_memoryRecordPremises hfirstD)`,
not a `∀` over a type that might be empty. -/

theorem b138_four_census_extras_at_a_witness :
    (∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) (b138_residualPremises hfirstD))
          (memoryNodesOf (distinctCensusExecution hfirstD) (b138_memoryRecordPremises hfirstD))),
        ServedLookupBridge.SkeletonSlotSemantics s) ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) (b138_residualPremises hfirstD))
          (memoryNodesOf (distinctCensusExecution hfirstD) (b138_memoryRecordPremises hfirstD)))
        (distinctCensusExecution hfirstD).Λ ∧
      (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) (b138_residualPremises hfirstD))
        (memoryNodesOf (distinctCensusExecution hfirstD) (b138_memoryRecordPremises hfirstD))).BoundedBy
        (distinctCensusExecution hfirstD).q ∧
      ProductionP8Containment.CombinedBoundedBy K97cubic (distinctCensusExecution hfirstD).q
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) (b138_residualPremises hfirstD))
          (memoryNodesOf (distinctCensusExecution hfirstD) (b138_memoryRecordPremises hfirstD))) :=
  distinctCensus_four_census_extras hfirstD (b138_residualPremises hfirstD) (b138_memoryRecordPremises hfirstD)



def b138_censusRecordPremises_of_census
    (hcensus : EdgeComparisonCensus.CombinedSkeletonCensus K97cubic
      (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) (b138_residualPremises hfirstD))
        (memoryNodesOf (distinctCensusExecution hfirstD) (b138_memoryRecordPremises hfirstD)))
      (distinctCensusExecution hfirstD).Λ) :
    CensusRecordPremises (distinctCensusExecution hfirstD) (b138_residualPremises hfirstD)
      (b138_memoryRecordPremises hfirstD) :=
  distinctCensus_censusRecordPremises_of_census hfirstD (b138_residualPremises hfirstD) (b138_memoryRecordPremises hfirstD)
    hcensus

/-- The produced bundle's `census` field **is** the hypothesis, definitionally, and the other four
**are** the §F/§B.0 proofs.  With `censusRecordPremises_still_five_here` (five-field eta) this is the
mechanical form of "exactly one field is open": there is no sixth field and no second hypothesis. -/
theorem b138_exactly_one_field_is_the_hypothesis
    (hcensus : EdgeComparisonCensus.CombinedSkeletonCensus K97cubic
      (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) (b138_residualPremises hfirstD))
        (memoryNodesOf (distinctCensusExecution hfirstD) (b138_memoryRecordPremises hfirstD)))
      (distinctCensusExecution hfirstD).Λ) :
    (b138_censusRecordPremises_of_census hfirstD hcensus).census = hcensus ∧
      (b138_censusRecordPremises_of_census hfirstD hcensus).slotSemantics =
        distinctCensus_slotSemantics hfirstD (b138_residualPremises hfirstD) (b138_memoryRecordPremises hfirstD) ∧
      (b138_censusRecordPremises_of_census hfirstD hcensus).sizeWindowBound =
        distinctCensus_sizeWindowBound hfirstD (b138_residualPremises hfirstD) (b138_memoryRecordPremises hfirstD) :=
  ⟨rfl, rfl, rfl⟩

/-! ## §D.

-/


theorem b138_memoryRecordPremises_inhabited_at_f73 :
    Nonempty (MemoryRecordPremises BuildableConcrete.concreteExecution) :=
  ⟨Nock.RedTeam.Batch101.concreteMemoryRecordPremises⟩

/-- **The pair is inhabited at BOTH live fixtures.**  So "no compiled inhabitant" is retracted for
`MemoryRecordPremises` at F73 and for both types at the released F97 fixture. -/
theorem b138_premise_pair_inhabited_at_both_fixtures :
    (Nonempty (ResidualPremises BuildableConcrete.concreteExecution) ∧
        Nonempty (MemoryRecordPremises BuildableConcrete.concreteExecution)) ∧
      (Nonempty (ResidualPremises (distinctCensusExecution hfirstD)) ∧
        Nonempty (MemoryRecordPremises (distinctCensusExecution hfirstD))) :=
  ⟨⟨Batch96.ConcretePremises.f73_residualPremises_nonvacuous,
      b138_memoryRecordPremises_inhabited_at_f73⟩,
    ⟨b138_residualPremises_nonempty hfirstD, b138_memoryRecordPremises_nonempty hfirstD⟩⟩

end Fixture

/-! ## §G. Section 2 item 6 — the two GENERIC state-gated implications, re-derived independently

These are the durable, carrier-free, fixture-independent part of the earlier analysis, and they are re-proved here
from the two definitions rather than by re-instantiating the earlier theorems.  The two mechanism
lemmas are stated separately so the gate can be read off without the reconstruction machinery. -/

section Generic

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **Mechanism 1, isolated.**  `SizeWindowCounting.requiredSizeWindowNouns` emits nothing outside
`{.s3, .s4, .s6}` — the three Algorithm `NockCompute` blocks that read a subformula evaluation's
type.  Proved by cases on the state, with no reconstruction, no
execution and no fixture. -/

theorem b138_requiredSizeWindowNouns_empty_off_gate (s : ComputeRowSkeleton)
    (h3 : s.state ≠ .s3) (h4 : s.state ≠ .s4) (h6 : s.state ≠ .s6) :
    SizeWindowCounting.requiredSizeWindowNouns s = [] := by
  unfold SizeWindowCounting.requiredSizeWindowNouns
  rcases hst : s.state with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
    rw [hst] at h3 h4 h6 <;>
    first
      | rfl
      | exact absurd rfl h3
      | exact absurd rfl h4
      | exact absurd rfl h6

/-- **Mechanism 2, isolated.**  Both clauses of `ServedLookupBridge.SkeletonSlotSemantics` are gated
on `{.s0, .s9}` — the two algorithm blocks that perform a memory lookup —
so off those two states the structure is inhabited by its own gates.  This is the whole content of
`slotSemantics_of_no_lookup_states` before the reconstruction is threaded in. -/

theorem b138_skeletonSlotSemantics_of_off_gate (s : ComputeRowSkeleton)
    (h0 : s.state ≠ .s0) (h9 : s.state ≠ .s9) :
    ServedLookupBridge.SkeletonSlotSemantics s :=
  { s0_slot := fun hst => absurd hst h0, s9_slot := fun hst => absurd hst h9 }

/-- **`reconstructed_row_state` is `rfl`, restated independently.**  The reconstructed compute-row
skeleton's `state` field IS the execution row's state component, definitionally.  This is the hinge
of §F: without it the opcode hypothesis on `E.exec.computeRowAt` would not reach the skeleton the
census predicates quantify over. -/

theorem b138_reconstructed_row_state (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (i : Fin E.cfg.compRows) :
    ((computeNodeAt E P i).skel).state = (E.exec.computeRowAt i).1 := rfl

/-- **`sizeWindowBound_of_no_window_states`, re-derived.**  Same statement as the earlier analysis's, proved from
`b138_requiredSizeWindowNouns_empty_off_gate` and `reconstructed_rows_are_nodes` rather than by
re-instantiation.  Generic in `F`, `K`, `E`, `P`, `M`; over the **reconstruction**
`skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)`, which is written out in the statement
below rather than abbreviated, so this also witnesses the layer claim of item 7. -/

theorem b138_sizeWindowBound_of_no_window_states (E : BuildableNockExecution F K)
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
  rw [← b138_reconstructed_row_state E P i] at h3 h4 h6
  rw [b138_requiredSizeWindowNouns_empty_off_gate _ h3 h4 h6] at hns
  simp at hns

/-- **`slotSemantics_of_no_lookup_states`, re-derived.**  Same statement, proved from
`b138_skeletonSlotSemantics_of_off_gate`.  Generic in `F`, `K`, `E`, `P`, `M`, over the
reconstruction. -/

theorem b138_slotSemantics_of_no_lookup_states (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (h : ∀ i : Fin E.cfg.compRows,
      (E.exec.computeRowAt i).1 ≠ .s0 ∧ (E.exec.computeRowAt i).1 ≠ .s9) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      ServedLookupBridge.SkeletonSlotSemantics s := by
  intro s hs
  obtain ⟨i, rfl⟩ := reconstructed_rows_are_nodes E P M hs
  obtain ⟨h0, h9⟩ := h i
  rw [← b138_reconstructed_row_state E P i] at h0 h9
  exact b138_skeletonSlotSemantics_of_off_gate _ h0 h9

end Generic

/-! ### §G.1 The gates are load-bearing — at the states the earlier analysis did NOT cover

The earlier analysis refutes the conclusion at an **OP6** row (`census_holds_and_sizeWindowBound_fails`) and at an
**OP0** row (`s0SlotFailRow_slotSemantics_fails`), and shows non-necessity at those same two states.
The four witnesses below are at the **other** gated states — **OP3** for the window gate and **OP9**
for the lookup gate — so between the two batches every state named in either hypothesis is covered
in both directions, and neither theorem can be an equivalence in disguise at any of them. -/

/-- A four-leaf noun, independent of the earlier `fourLeaves`. -/
def b138Four : Noun :=
  .cell (.cell (.atom 0) (.atom 0)) (.cell (.atom 0) (.atom 0))

theorem b138Four_leaves : b138Four.leaves = 4 := by simp [b138Four, Noun.leaves]

/-- An **OP3** row whose size-window noun `sf 0 .result` has four leaves.
`ComputeTable.fanoutComp .s3 = 1`, so index `0` is in range and the slot is read. -/

def b138S3FailRow : ComputeRowSkeleton where
  state := .s3
  subject := .atom 0
  formula := .atom 0
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => b138Four
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 1⟩

def b138S3FailSkeleton : SemanticSkeleton where
  computeTree := .node b138S3FailRow []
  memoryForest := []

theorem b138S3FailSkeleton_computeRows :
    computeSkeletonRows b138S3FailSkeleton = [b138S3FailRow] := by
  unfold computeSkeletonRows b138S3FailSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

/-- **The window gate is not removable at OP3** — the state the earlier OP6 witness does not reach.
`SizeWindowNounsBoundedBy` fails at every `Λ < 4`, uniformly, so this is not placed at a degenerate
value of `Λ`. -/

theorem b138_window_gate_not_removable_at_s3 :
    b138S3FailRow.state = .s3 ∧
      ∀ Λ : ℕ, Λ < 4 →
        ¬ SizeWindowCounting.SizeWindowNounsBoundedBy b138S3FailSkeleton Λ := by
  refine ⟨rfl, ?_⟩
  intro Λ hΛ hbound
  have hmem : b138Four ∈ SizeWindowCounting.skeletonSizeWindowNouns b138S3FailSkeleton := by
    rw [SizeWindowCounting.skeletonSizeWindowNouns, b138S3FailSkeleton_computeRows]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [show SizeWindowCounting.requiredSizeWindowNouns b138S3FailRow = [b138Four] from rfl]
    simp
  have := hbound b138Four hmem
  rw [b138Four_leaves] at this
  omega

/-- The same OP3 row with an atomic window noun. -/

def b138S3HoldRow : ComputeRowSkeleton :=
  { b138S3FailRow with subformula := fun _ _ _ => .atom 0 }

def b138S3HoldSkeleton : SemanticSkeleton where
  computeTree := .node b138S3HoldRow []
  memoryForest := []

theorem b138S3HoldSkeleton_computeRows :
    computeSkeletonRows b138S3HoldSkeleton = [b138S3HoldRow] := by
  unfold computeSkeletonRows b138S3HoldSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

/-- **The window gate is not necessary at OP3 either.**  This skeleton violates the hypothesis of
`sizeWindowBound_of_no_window_states` and still satisfies its conclusion at `Λ = 1`, so the
implication is strict at OP3 as well as at OP6. -/

theorem b138_window_gate_not_necessary_at_s3 :
    b138S3HoldRow.state = .s3 ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy b138S3HoldSkeleton 1 := by
  refine ⟨rfl, ?_⟩
  intro n hn
  rw [SizeWindowCounting.skeletonSizeWindowNouns, b138S3HoldSkeleton_computeRows] at hn
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hn
  rw [show SizeWindowCounting.requiredSizeWindowNouns b138S3HoldRow = [Noun.atom 0] from rfl,
    List.mem_singleton] at hn
  rw [hn]
  simp [Noun.leaves]

/-- An **OP9** row whose third memory record has axis `2` on atomic subformula nouns.
`recordCount .s9 = 3`, so `skeletonMemoryAxis · 2` reads that record. -/

def b138S9FailRow : ComputeRowSkeleton where
  state := .s9
  subject := .atom 0
  formula := .atom 0
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 2⟩

/-- **The lookup gate is not removable at OP9** — the clause the earlier OP0 witness does not reach.
`/[2 0]` is `none`, so the `s9_slot` clause fails.  With `s0SlotFailRow_slotSemantics_fails` this
covers both clauses of `SkeletonSlotSemantics`. -/

theorem b138_lookup_gate_not_removable_at_s9 :
    b138S9FailRow.state = .s9 ∧
      ¬ ServedLookupBridge.SkeletonSlotSemantics b138S9FailRow := by
  refine ⟨rfl, ?_⟩
  intro hslot
  have h := hslot.s9_slot rfl
  rw [show P8Census.skeletonMemoryAxis b138S9FailRow 2 = 2 from rfl] at h
  simp [b138S9FailRow, P8Census.skeletonSubformula, Noun.slot, ComputeTable.fanoutComp] at h

/-- An OP9 row whose third record has axis `1`. -/

def b138S9HoldRow : ComputeRowSkeleton :=
  { b138S9FailRow with memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 1⟩ }

/-- **The lookup gate is not necessary at OP9 either.**  This row is `.s9` — so the hypothesis of
`slotSemantics_of_no_lookup_states` fails on it — and still satisfies `SkeletonSlotSemantics`,
because `/[1 n] = n`. -/

theorem b138_lookup_gate_not_necessary_at_s9 :
    b138S9HoldRow.state = .s9 ∧ ServedLookupBridge.SkeletonSlotSemantics b138S9HoldRow := by
  refine ⟨rfl, ⟨?_, ?_⟩⟩
  · intro h
    exact absurd h (by decide)
  · intro _
    rw [show P8Census.skeletonMemoryAxis b138S9HoldRow 2 = 1 from rfl]
    simp [b138S9HoldRow, b138S9FailRow, P8Census.skeletonSubformula, Noun.slot, ComputeTable.fanoutComp]

/-! ## §E. Accounting — nothing moved -/

/-- The five census extras are still five named fields. -/
theorem b138_censusRecordPremises_still_five {F K : Type} [Field F] [Field K] [Algebra F K]
    {E : BuildableNockExecution F K} {P : ResidualPremises E} {M : MemoryRecordPremises E}
    (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } := by
  cases C
  rfl

/-- `ResidualPremises` is three named fields after `firstLine` left the structure; `MemoryRecordPremises` still two. -/
theorem b138_premise_field_counts_unchanged {F K : Type} [Field F] [Field K] [Algebra F K]
    {E : BuildableNockExecution F K} (P : ResidualPremises E) (M : MemoryRecordPremises E) :
    (InactiveDecPaddingExec E.exec ∧
        (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
          E.q = ringChar K) ∧
      -- 28th: `axisNat` reads the a-bearing row `E.execA`.
      (∀ i : Fin E.cfg.memRows,
          memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
            ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
        (∀ i : Fin E.cfg.memRows,
          memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
            MemoryTimestampClosedAt E.cfg.challenges.α
              (E.exec.memoryRowAt i).2.2.mem.ts) :=
  ⟨GenericHonestCommitment.residualPremises_still_four P, M.axisNat, M.timestampClosed⟩

/-- **`BuildableNockExecution` still has its fourteen fields; no carrier field was added.**  The eta
is exhaustive, so a fifteenth field would break it. -/
theorem b138_execution_still_fourteen_fields {F K : Type} [Field F] [Field K] [Algebra F K]
    (E : BuildableNockExecution F K) :
    E =
      { q := E.q
        q_gt_one := E.q_gt_one
        Λ := E.Λ
        cfg := E.cfg
        execA := E.execA
        exec := E.exec
        exec_encode := E.exec_encode
        semanticData := E.semanticData
        memoryTrace := E.memoryTrace
        requestNodup := E.requestNodup
        recordCountBalance := E.recordCountBalance
        q_le_ringChar := E.q_le_ringChar
        two_ne_zero := E.two_ne_zero
        Ksz_lt_ringChar := E.Ksz_lt_ringChar
        programIOCapacity := E.programIOCapacity
        memoryIOCapacity := E.memoryIOCapacity } :=
  E.eta_with_memoryTrace


theorem b138_residual_pair_still_eleven_one_two : 11 + 1 + 2 = 14 :=
  GenericHonestPackage.residual_pair_still_eleven_one_two_after_logup_inventory


theorem b138_consumed_capstone_untouched {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement P :=
  OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth

#print axioms b138_inactiveDec
#print axioms b138_residualPremises
#print axioms b138_residualPremises_nonempty
#print axioms b138_timestampClosed
#print axioms b138_memoryRecordPremises
#print axioms b138_memoryRecordPremises_nonempty
#print axioms b138_pairedRecordLayout_is_a_second_route
#print axioms b138_four_census_extras_at_a_witness
#print axioms b138_censusRecordPremises_of_census
#print axioms b138_exactly_one_field_is_the_hypothesis
#print axioms b138_memoryRecordPremises_inhabited_at_f73
#print axioms b138_premise_pair_inhabited_at_both_fixtures
#print axioms b138_requiredSizeWindowNouns_empty_off_gate
#print axioms b138_skeletonSlotSemantics_of_off_gate
#print axioms b138_reconstructed_row_state
#print axioms b138_sizeWindowBound_of_no_window_states
#print axioms b138_slotSemantics_of_no_lookup_states
#print axioms b138Four_leaves
#print axioms b138S3FailSkeleton_computeRows
#print axioms b138_window_gate_not_removable_at_s3
#print axioms b138S3HoldSkeleton_computeRows
#print axioms b138_window_gate_not_necessary_at_s3
#print axioms b138_lookup_gate_not_removable_at_s9
#print axioms b138_lookup_gate_not_necessary_at_s9
#print axioms b138_censusRecordPremises_still_five
#print axioms b138_premise_field_counts_unchanged
#print axioms b138_execution_still_fourteen_fields
#print axioms b138_residual_pair_still_eleven_one_two
#print axioms b138_consumed_capstone_untouched

end

end Nock.RedTeam.Batch138
