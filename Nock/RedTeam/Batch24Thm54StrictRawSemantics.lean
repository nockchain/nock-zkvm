/-
  Nock/RedTeam/Batch24Thm54StrictRawSemantics.lean

  `Thm54.StrictOperationalEvidence.StrictRowOperationalEvidence` is the consumer-minimal per-row
  package: fingerprint-level memory-record realization (`OpcodeSemantics.RealizesMemRec`), the two
  served lookups, and the strict modular OP4 success `(lusFBy p operand).isSome`.  It deliberately has
  **no** `IncrementNoOverflow` field.

  These receipts are counter-regressions against re-merging the two layers:

  * So an
    `IncrementNoOverflow` field would be a strictly stronger, non-paper premise.
  * The
    atom shape is therefore load-bearing and must not be dropped from either layer.
  * `b24_strict_op4_isSome_forces_atom_shape` — the strict layer recovers exactly that shape datum,
    and nothing more.
  * `b24_strictEvidence_nonvacuous` / `b24_strictEvidence_s0_nonvacuous` — concrete `ℚ`-seed s4 and
    s0 rows inhabiting the strict structure, the second with the `s0` record *and* served fields both
    live, so none of the receipts above are statements about an empty premise.

  Scope: `s0_served`/`s9_served` of the strict structure are *definitions* copied verbatim from
  `BoundSemanticTrace.SkeletonOperationalCore`; deriving them from acceptance is Packet B and is not
  claimed here.
-/

import Nock.NockVMROM.Thm54.StrictOperationalEvidence
import Nock.RedTeam.Batch22Thm54ModularOperational

namespace Nock.RedTeam.Batch24

open Nock Nock.Noun
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictOperationalEvidence (StrictRowOperationalEvidence)

/-- Reminder: `s0_served`/`s9_served` are definitions pending Packet B (derivation from acceptance);
`s0_record`/`s9_record` are fingerprint-level, not noun equalities. -/
abbrev b24StrictRowOperationalEvidence {K : Type} [Field K]
    (p : ℕ) (z : K) (s : StrictOperationalEvidence.RowSkeleton) : Prop :=
  StrictRowOperationalEvidence p z s

/-- **The two layers really disagree at the top residue.**  Hence the strict evidence cannot carry
`IncrementNoOverflow` without importing a premise the paper does not have. -/
theorem b24_strict_op4_total_but_legacy_fails_at_top (p : ℕ) (hp : 0 < p) :
    (FieldEmbedding.lusFBy p (.atom (p - 1))).isSome = true ∧
      FieldEmbedding.lusFBy p (.atom (p - 1)) = some (.atom 0) ∧
      ¬ OpcodeSemantics.IncrementNoOverflow p (.atom (p - 1)) :=
  ⟨StrictOperationalEvidence.strict_op4_total p (p - 1),
    StrictOperationalEvidence.strict_op4_wraps_at_top p hp,
    Batch22.b22_incNoWrap_fails_at_top p⟩

theorem b24_legacy_holds_below_top (q n : ℕ) (h : n + 1 < q) :
    OpcodeSemantics.IncrementNoOverflow q (.atom n) :=
  Batch22.b22_incNoWrap_holds_below_top q n h

/-- **A cell operand is bounded but not no-overflow.**  `incNoWrap` collapses a cell to `.atom 0`
(a perfectly bounded value), while `IncrementNoOverflow` is false and strict modular OP4 crashes.
So the atom shape is load-bearing in both layers and cannot be inferred from boundedness. -/
theorem b24_cell_operand_not_noOverflow (q : ℕ) (a b : Noun) :
    ¬ OpcodeSemantics.IncrementNoOverflow q (.cell a b) ∧
      OpcodeSemantics.incNoWrap (.cell a b) = .atom 0 ∧
      FieldEmbedding.lusFBy q (.cell a b) = none :=
  ⟨fun h => h.elim, rfl, StrictOperationalEvidence.strict_op4_cell q a b⟩

/-- The strict layer recovers exactly the atom-shape datum from modular success. -/
theorem b24_strict_op4_isSome_forces_atom_shape {p : ℕ} {v : Noun}
    (h : (FieldEmbedding.lusFBy p v).isSome = true) : ∃ n, v = .atom n :=
  StrictOperationalEvidence.atom_of_strict_op4 h

/-! ## Non-vacuity witness

A concrete s4 compute-row skeleton over a real field (`ℚ`).  In state `.s4` we have
`fanoutComp.s4 = 1` and `recordCount.s4 = 1`, so exactly slot `0` of the subformula triple and of
the memory records is live; the `s0`/`s9` fields are discharged by the state mismatch and
`s4_modular` by the atom operand. -/

/-- One concrete pre-seed s4 row whose OP4 operand is the atom `n`. -/
def s4Row (n : ℕ) : StrictOperationalEvidence.RowSkeleton where
  state := .s4
  subject := .atom 0
  formula := .cell (.atom 4) (.atom 0)
  evaluation := .atom (n + 1)
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom n
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 0⟩

@[simp] theorem s4Row_state (n : ℕ) : (s4Row n).state = .s4 := rfl

theorem s4Row_operand (n : ℕ) :
    P8Census.skeletonSubformula (s4Row n) 0 .result = .atom n := by
  simp [P8Census.skeletonSubformula, s4Row, ComputeTable.fanoutComp]

/-- **The strict structure is inhabited over a real field.**  So every receipt above concerns a
satisfiable premise, not an empty one.  Here the arithmetic field `s4_modular` is the live one. -/
theorem b24_strictEvidence_nonvacuous (p n : ℕ) (z : ℚ) :
    StrictRowOperationalEvidence p z (s4Row n) where
  s0_record := fun h => absurd h (by simp)
  s9_record := fun h => absurd h (by simp)
  s0_served := fun h => absurd h (by simp)
  s9_served := fun h => absurd h (by simp)
  s4_modular := fun _ => by
    rw [s4Row_operand]
    exact StrictOperationalEvidence.strict_op4_total p n

/-- A structural reconstruction serves its own root axis: the served-lookup *definition* is
satisfiable, so `s0_served`/`s9_served` are not empty premises even though their derivation from
acceptance is Packet B. -/
theorem servedLookup_root (v : Noun) (a : ℕ) :
    GlobalCarryAxis.ServedLookup (GlobalCarryRecognizer.ofNoun v a) a v where
  matched :=
    ⟨GlobalCarryRecognizer.ofNoun v a, .refl,
      GlobalCarryRecognizer.ofNoun_axisOf v a,
      GlobalCarryRecognizer.ofNoun_nounOf v a⟩

/-- One concrete pre-seed s0 row: `recordCount.s0 = 2`, so record slot `1` is live and carries the
root/child/axis data that `s0_record` and `s0_served` actually talk about. -/
def s0Row : StrictOperationalEvidence.RowSkeleton where
  state := .s0
  subject := .atom 7
  formula := .cell (.atom 0) (.atom 1)
  evaluation := .atom 7
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 7, .atom 7, 1⟩

@[simp] theorem s0Row_state : s0Row.state = .s0 := rfl

theorem s0Row_axis : P8Census.skeletonMemoryAxis s0Row 1 = 1 := by
  simp [P8Census.skeletonMemoryAxis, s0Row, Nock.Framework.recordCount]

/-- **The `s0` record and served fields are jointly satisfiable at a real seed.**  Together with
`b24_strictEvidence_nonvacuous` this rules out the vacuity reading of the strict structure: the
fingerprint-level record obligation and the served lookup both hold non-trivially here. -/
theorem b24_strictEvidence_s0_nonvacuous (p : ℕ) (z : ℚ) :
    StrictRowOperationalEvidence p z s0Row where
  s0_record := fun _ =>
    StrictOperationalEvidence.realizesMemRec_of_bindMemRec
      (StrictOperationalEvidence.bindMemRec_encMemRec z _) rfl rfl s0Row_axis.symm
  s9_record := fun h => absurd h (by simp)
  s9_served := fun h => absurd h (by simp)
  s0_served := fun _ => by
    rw [s0Row_axis]
    exact servedLookup_root (.atom 7) 1
  s4_modular := fun h => absurd h (by simp)

end Nock.RedTeam.Batch24

#print axioms Nock.RedTeam.Batch24.b24_strict_op4_total_but_legacy_fails_at_top
#print axioms Nock.RedTeam.Batch24.b24_legacy_holds_below_top
#print axioms Nock.RedTeam.Batch24.b24_cell_operand_not_noOverflow
#print axioms Nock.RedTeam.Batch24.b24_strict_op4_isSome_forces_atom_shape
#print axioms Nock.RedTeam.Batch24.s4Row_operand
#print axioms Nock.RedTeam.Batch24.b24_strictEvidence_nonvacuous
#print axioms Nock.RedTeam.Batch24.servedLookup_root
#print axioms Nock.RedTeam.Batch24.s0Row_axis
#print axioms Nock.RedTeam.Batch24.b24_strictEvidence_s0_nonvacuous
