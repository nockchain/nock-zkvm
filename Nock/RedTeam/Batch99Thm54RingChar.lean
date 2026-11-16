import Nock.NockVMROM.Thm54.GenericHonestCommitment
import Nock.NockVMROM.Thm54.DistinctCensusExecution
import Nock.RedTeam.Batch98Thm54FirstLine
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS. `BuildableNockExecution` exposes only
`q ≤ ringChar K`; `ExactConfig` exposes no `q`. On the real F73 cubic there
are nontrivial strict bounds below the characteristic, while every shipped
concrete `BuildableNockExecution` constructor explicitly chooses equality.
`Data` and `CommitmentResidual` retain equality as a named premise.

The paper layer is more precise than merely “Lean-only”: atoms are over the
base field `F_p`, so on the F73 model the package equation identifies `q` with
`|F| = p = char(K)`, not with NPR's `|K| = p^3`. Thus the equality is a
paper-faithful base-field pin for the intended full atom range, but it is not
derivable from the weaker `BuildableNockExecution` API.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch99

open scoped Classical
open Nock Nock.Framework
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## A. Under-closure: neither `E` nor `ExactConfig` supplies equality -/

/-- The only
comparison involving `q` is `q_le_ringChar`; there is no equality, `Data`, or
residual field. -/
theorem execution_eta_only_has_q_le
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
        memoryIOCapacity := E.memoryIOCapacity } := by
  cases E
  rfl

/-- Exhaustive eta receipt for the nested exact configuration. It contains
domain geometry and challenges but no atom bound `q`, hence no hidden
`q = ringChar K` premise. -/
theorem exactConfig_eta_has_no_q
    (cfg : ExactConfig F K) :
    cfg =
      { challenges := cfg.challenges
        Ksz := cfg.Ksz
        kMem := cfg.kMem
        orbit := cfg.orbit
        orbit_h_pos := cfg.orbit_h_pos
        compRows := cfg.compRows
        memRows := cfg.memRows
        compRows_pos := cfg.compRows_pos
        memRows_pos := cfg.memRows_pos
        compRows_le := cfg.compRows_le
        memRows_le := cfg.memRows_le
        eDeg := cfg.eDeg
        eDeg_eq_one := cfg.eDeg_eq_one
        compNodes := cfg.compNodes
        compNodes_spec := cfg.compNodes_spec
        memNodes := cfg.memNodes
        memNodes_spec := cfg.memNodes_spec } := by
  cases cfg
  rfl

/-- The exact positive information available from arbitrary `E`. -/
theorem execution_projects_strictly_weaker_bound
    (E : BuildableNockExecution F K) :
    1 < E.q ∧ E.q ≤ ringChar K :=
  ⟨E.q_gt_one, E.q_le_ringChar⟩

/-- Axiom-free negative control: positive lower bound plus upper bound does
not entail equality. -/
theorem positive_le_does_not_force_eq :
    ¬ ∀ (q n : ℕ), 1 < q → q ≤ n → q = n := by
  intro h
  exact (by decide : (2 : ℕ) ≠ 73) (h 2 73 (by decide) (by decide))

/-! ## B. Real-field strict inequality and concrete constructor pins -/

namespace Concrete

open Nock.NockVMROM.Thm54.ConcreteStrictPackage

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := concrete_char73

/-- Independent characteristic computation for the real F73 cubic. -/
theorem independent_char_K73 : (73 : ℕ) = ringChar K73cubic := by
  rw [← Algebra.ringChar_eq F73 K73cubic, ZMod.ringChar_zmod_n]

/-- The inequality carried by `E` can be strict on the actual F73 extension
field used throughout the package. This is a field-and-bound witness, not a
new `BuildableNockExecution`. -/
theorem f73_has_nontrivial_strict_atom_bound :
    ∃ q : ℕ, 1 < q ∧ q < ringChar K73cubic :=
  ⟨2, by decide, by rw [← independent_char_K73]; decide⟩

/-- The base field has cardinality exactly the extension characteristic. -/
theorem independent_base_card_eq_char :
    Fintype.card F73 = ringChar K73cubic := by
  rw [← independent_char_K73]
  simp [F73]

/-- The cubic extension has cardinality `73^3`, the quantity used by the
paper's NPR denominator. -/
theorem independent_cubic_card :
    Fintype.card K73cubic = 73 ^ 3 := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 73 3 (by norm_num)

/-- `|K| = 73^3` is not the characteristic. -/
theorem independent_cubic_card_ne_char :
    Fintype.card K73cubic ≠ ringChar K73cubic := by
  rw [independent_cubic_card, ← independent_char_K73]
  norm_num

/-- The actual F73 commitment witnesses the layer distinction without a
conditional `Data` hypothesis: its `q` is `|F73| = char(K73cubic)` and not
`|K73cubic|` -/
theorem concrete_data73_q_is_base_card_not_extension_card :
    let E := BuildableConcrete.concreteExecution
    E.q = Fintype.card F73 ∧ E.q ≠ Fintype.card K73cubic := by
  dsimp [BuildableConcrete.concreteExecution]
  constructor
  · simp [F73]
  · rw [independent_cubic_card]
    norm_num

/-- The F73 execution pins equality because the constructor literally chooses
`q := 73`; the execution structure did not derive it. -/
theorem f73_fixture_pins_equality_at_construction :
    BuildableConcrete.concreteExecution.q = 73 ∧
      BuildableConcrete.concreteExecution.q = ringChar K73cubic := by
  exact ⟨rfl, independent_char_K73⟩

end Concrete

namespace FixturePins

open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.DistinctCensusExecution

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- Independent F97 characteristic computation. -/
theorem independent_char_K97 :
    ringChar OptimizedStrictNonterminalConcrete.K97cubic = 97 := by
  rw [← Algebra.ringChar_eq OptimizedStrictNonterminalConcrete.F97
    OptimizedStrictNonterminalConcrete.K97cubic, ZMod.ringChar_zmod_n]

/-- All three shipped concrete `BuildableNockExecution` inhabitants found in
the production tree pin `q` to the field characteristic at construction:
F73, the two-serviced-root F97 fixture, and the distinct-census F97 fixture.

Form R: `distinctCensusExecution` takes a leftover first-row
`counts = 0 ∧ indicator = 0` (live is `chainOneBitWeight`). -/
theorem all_shipped_concrete_executions_pin_equality
    (hfirstD :
      (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
        (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0) :
    BuildableConcrete.concreteExecution.q =
        ringChar ConcreteStrictPackage.K73cubic ∧
      MultiRootServedFixture.multiRootExecution.q =
        ringChar OptimizedStrictNonterminalConcrete.K97cubic ∧
      (DistinctCensusExecution.distinctCensusExecution hfirstD).q =
        ringChar OptimizedStrictNonterminalConcrete.K97cubic := by
  refine ⟨Concrete.independent_char_K73, ?_, ?_⟩
  · change 97 = ringChar OptimizedStrictNonterminalConcrete.K97cubic
    exact independent_char_K97.symm
  · change 97 = ringChar OptimizedStrictNonterminalConcrete.K97cubic
    exact independent_char_K97.symm

end FixturePins

/-! ## C. Equality is on `Data` / residual, and means base-field size -/

noncomputable local instance batch99FintypeK73 :
    Fintype ConcreteStrictPackage.K73cubic :=
  Fintype.ofFinite ConcreteStrictPackage.K73cubic

/-- `Data` adds equality to the weaker execution inequality. -/
theorem data_retains_named_equality
    {E : BuildableNockExecution F K} (D : Data E) :
    E.q ≤ ringChar K ∧ E.q = ringChar K :=
  ⟨E.q_le_ringChar, D.q_eq_ringChar⟩

/-- The released residual copies the same equality. -/
theorem commitmentResidual_retains_named_equality
    {E : BuildableNockExecution F K}
    (R : BuildablePackage.CommitmentResidual E) :
    E.q = ringChar K :=
  R.q_eq_ringChar

/-- The exact released optimized package also retains the equality field. -/
theorem released_package_retains_named_equality
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    P.q = ringChar K :=
  P.q_eq_ringChar

/-- On the F73 model, the `Data` premise identifies `q` with `|F| = p`, not
with the cubic NPR sampling cardinality `|K| = p^3`. This is the exact layer
distinction in the paper. -/
theorem data_q_equals_base_card_not_extension_card
    {E : BuildableNockExecution
      ConcreteStrictPackage.F73 ConcreteStrictPackage.K73cubic}
    (D : Data E) :
    E.q = Fintype.card ConcreteStrictPackage.F73 ∧
      E.q ≠ Fintype.card ConcreteStrictPackage.K73cubic := by
  constructor
  · exact D.q_eq_ringChar.trans Concrete.independent_base_card_eq_char.symm
  · intro h
    apply Concrete.independent_cubic_card_ne_char
    exact h ▸ D.q_eq_ringChar

/-! ## D. Four premises, non-generic boundary, accounting, and capstone -/

theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

/-- All remaining residual statements remain projectable. -/
theorem residualPremises_projects_all_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows,
        AxisAtomPremises (E.semanticData.rows i)) ∧
      E.q = ringChar K :=
  ⟨P.inactiveDec, P.axisAtoms, P.q_eq_ringChar⟩

theorem universal_data_would_force_equality
    (g : ∀ E : BuildableNockExecution F K, Data E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  fun E => (g E).q_eq_ringChar

/-- A generic residual constructor has the same consequence. -/
theorem universal_residual_would_force_equality
    (g : ∀ E : BuildableNockExecution F K,
      BuildablePackage.CommitmentResidual E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  fun E => (g E).q_eq_ringChar

/-- The existing constructor still starts from inhabited `Data E` and takes
both dependent post-challenge families -/
theorem commitment_constructor_still_requires_D_A_W
    {E : BuildableNockExecution F K}
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (D : Data E)
    (A : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      TemplateRawJointSoundness.AlphaMCommitment
        (p := ringChar K) D.timestampStrategy z hz α lmb)
    (W : ∀ (ω : JointCoins K) (_lmb : K), nprSeed ω ≠ 0 → RawWalkArrays K) :
    Nonempty (BuildablePackage.CommitmentResidual E) :=
  ⟨commitmentResidualOf D A W⟩

inductive ReviewedField99
  | structural
  | optimized_chips
  | shared_io
  | perfect_completeness
  | containment
  | walk_bounds
  | p8_fixed_field_soundness
  | p8_fixed_field_bits
  | acceptance_to_target
  | complete_false_acceptance_bound
  | complete_false_acceptance_bits
  | exact_resources
  | row_budgets
  | shared_forest_axis
deriving DecidableEq

def substantiveFields99 : List ReviewedField99 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields99 : List ReviewedField99 := [.structural]

def residualFields99 : List ReviewedField99 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

theorem independent_exact_eleven_one_two_accounting :
    substantiveFields99.length = 11 ∧
      typeSummaryFields99.length = 1 ∧
      residualFields99 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields99.length = 2 ∧
      (substantiveFields99 ++ typeSummaryFields99 ++ residualFields99).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  ⟨optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth, rfl⟩

#print axioms execution_eta_only_has_q_le
#print axioms exactConfig_eta_has_no_q
#print axioms execution_projects_strictly_weaker_bound
#print axioms positive_le_does_not_force_eq
#print axioms Concrete.independent_char_K73
#print axioms Concrete.f73_has_nontrivial_strict_atom_bound
#print axioms Concrete.independent_base_card_eq_char
#print axioms Concrete.independent_cubic_card
#print axioms Concrete.independent_cubic_card_ne_char
#print axioms Concrete.concrete_data73_q_is_base_card_not_extension_card
#print axioms Concrete.f73_fixture_pins_equality_at_construction
#print axioms FixturePins.independent_char_K97
#print axioms FixturePins.all_shipped_concrete_executions_pin_equality
#print axioms data_retains_named_equality
#print axioms commitmentResidual_retains_named_equality
#print axioms released_package_retains_named_equality
#print axioms data_q_equals_base_card_not_extension_card
#print axioms residualPremises_eta_still_four
#print axioms residualPremises_projects_all_four
#print axioms universal_data_would_force_equality
#print axioms universal_residual_would_force_equality
#print axioms commitment_constructor_still_requires_D_A_W
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestCommitment.execution_only_has_q_le
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch99
