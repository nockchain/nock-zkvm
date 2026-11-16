import Nock.NockVMROM.Thm54.GenericHonestCommitment
import Nock.NockVMROM.Thm54.GenericHonestData
import Nock.NockVMROM.Thm54.GenericHonestArrays
import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.NockVMROM.Thm54.DistinctCensusCommitment
import Nock.NockVMROM.Thm54.TraceGen.Op6DataK3
import Nock.NockVMROM.Thm54.TraceGen.Op9DataK3
import Nock.NockVMROM.Thm54.Walk37.PaperNames
import Nock.RedTeam.Batch91Thm54CompleteFalseAcceptance
import Nock.RedTeam.Batch128Thm54GenericHonestPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Independent spec-redteam of CN (`q_eq_ringChar` modelling)

Different context.  CN is a claim under attack, not evidence.
Construction files were not edited in this pass.  Paper RAP parameters
`158-159` were re-read at source together.  NPR `|K|=p³` sizing was re-read only as a negative control, not as
the cited pin.

Paper frame (re-read at source):
the paper fixes `F ≡ F_p` at the Goldilocks prime
`p = 2^{64}-2^{32}+1`.  the paper takes `K` as the degree-`e=3`
extension of that `F_p`, hence `char(K)=p`.  The paper names `p` and
never `q`.  Lean `q` is the atom bound on `BuildableNockExecution`.
Honest constructors set `E.q = ringChar K` (F73 `q := 73`; DistinctCensus /
Op6 / Op9 `q := 97`).  C8 as a `ResidualPremises` field stays rejected.
`q_gt_one_and_q_le_do_not_imply_eq` stands.  The named extra remains
in `ResidualPremises`.

CN text still says `residualPremises_still_four` / four-field count.
That wording is attacked against Lean below.

Consumed capstone:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`
(`«Thm:NockVMROM»`).  Untouched.  No C8 field added.  F97 `q` not bumped.

Five axes:
1. Vacuity — honest constructors actually have `q = ringChar K`;
   negative `q_gt_one_and_q_le_do_not_imply_eq` still holds.
2. Weakening — field remains; tick is modelling, not a derivation from `E`;
   C8 not added as a `ResidualPremises` field.
4. Axiom leak — `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
5. Wrong layer — `11+1+2` is the capstone partition, not residual field
   count; `q_eq` remains a constructor extra; not `∀ E, Data E`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch160

open scoped Classical
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.Framework

noncomputable section

local instance batch160_prime73 : Fact (Nat.Prime 73) := ⟨by norm_num⟩
local instance batch160_prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩

open ConcreteStrictPackage
open BuildableConcrete
open OptimizedStrictNonterminalConcrete
open DistinctCensusExecution
open DistinctCensusCommitment
open TraceGen.Op6ConfigK3
open TraceGen.Op9ConfigK3

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := ConcreteStrictPackage.concrete_char73
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic

-- Form R leftover first-row `counts = 0` (live is `chainOneBitWeight`).
variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
variable (hfirst6 :
  ((TraceGen.Op6ConfigK3.exec TraceGen.Op6ConfigK3.seedZ TraceGen.Op6ConfigK3.alphaA).memoryPubAt
      ⟨0, by norm_num [TraceGen.Op6ConfigK3.cfg]⟩).pt.counts = 0 ∧
    ((TraceGen.Op6ConfigK3.exec TraceGen.Op6ConfigK3.seedZ TraceGen.Op6ConfigK3.alphaA).memoryPubAt
      ⟨0, by norm_num [TraceGen.Op6ConfigK3.cfg]⟩).pt.indicator = 0)
variable (hfirst9 :
  ((TraceGen.Op9ConfigK3.exec TraceGen.Op9ConfigK3.seedZ TraceGen.Op9ConfigK3.alphaA).memoryPubAt
      ⟨0, by norm_num [TraceGen.Op9ConfigK3.cfg]⟩).pt.counts = 0 ∧
    ((TraceGen.Op9ConfigK3.exec TraceGen.Op9ConfigK3.seedZ TraceGen.Op9ConfigK3.alphaA).memoryPubAt
      ⟨0, by norm_num [TraceGen.Op9ConfigK3.cfg]⟩).pt.indicator = 0)


/-! ## Axis 1. Vacuity: honest constructors pin `q = ringChar K`;
    `1 < q ≤ char` still does not force equality -/

/-- Paper Goldilocks prime, independently `norm_num`'d. -/
theorem paper_goldilocks_p :
    2 ^ 64 - 2 ^ 32 + 1 = 18446744069414584321 := by
  norm_num

/-- F73 constructor choice `q := 73`, equal to `ringChar K73cubic`. -/
theorem f73_q_eq_ringChar :
    concreteExecution.q = 73 ∧
      concreteExecution.q = ringChar K73cubic ∧
      concreteExecution.q ≤ ringChar K73cubic :=
  GenericHonestCommitment.Concrete.f73_q_pin_is_constructor_choice

/-- DistinctCensus F97 constructor `q := 97 = ringChar K97cubic`. -/
theorem distinctCensus_q_eq_ringChar :
    (distinctCensusExecution hfirstD).q = 97 ∧
      (distinctCensusExecution hfirstD).q = ringChar K97cubic :=
  ⟨rfl, DistinctCensusExecution.ringChar_K97.symm⟩

/-- The DistinctCensus `Data` extra is the same pin. -/
theorem distinctCensus_data_q_eq_ringChar :
    (distinctCensusExecution hfirstD).q = ringChar K97cubic :=
  (dataD hfirstD).q_eq_ringChar

/-- Op6 K3 constructor `q := 97 = ringChar K3`. -/
theorem op6_q_eq_ringChar :
    (Op6Execution hfirst6).q = 97 ∧
      (Op6Execution hfirst6).q = ringChar TraceGen.Op6Skeleton.K :=
  ⟨rfl, TraceGen.Op6ConfigK3.ringChar_K3.symm⟩

theorem op6_data_q_eq_ringChar :
    (Op6Execution hfirst6).q = ringChar TraceGen.Op6Skeleton.K :=
  (TraceGen.Op6ConfigK3.data hfirst6).q_eq_ringChar

/-- Op9 K3 constructor `q := 97 = ringChar K3`. -/
theorem op9_q_eq_ringChar :
    (Op9Execution hfirst9).q = 97 ∧
      (Op9Execution hfirst9).q = ringChar TraceGen.Op9Skeleton.K :=
  ⟨rfl, TraceGen.Op9ConfigK3.ringChar_K3.symm⟩

theorem op9_data_q_eq_ringChar :
    (Op9Execution hfirst9).q = ringChar TraceGen.Op9Skeleton.K :=
  (TraceGen.Op9ConfigK3.data hfirst9).q_eq_ringChar

/-- Negative control: `1 < q ≤ n` does not force `q = n`.
CN does not claim a generic implication from the inequality. -/
theorem q_gt_one_and_q_le_do_not_imply_eq :
    ¬ ∀ (q n : ℕ), 1 < q → q ≤ n → q = n :=
  GenericHonestCommitment.q_gt_one_and_q_le_do_not_imply_eq

/-- On the F73 cubic the inequality is inhabited strictly: `2 ≤ char` and
`2 ≠ char`.  Equality is therefore not a consequence of `E.q_le_ringChar`. -/
theorem f73_strict_q_le_inhabited :
    ∃ q : ℕ, 1 < q ∧ q ≤ ringChar K73cubic ∧ q ≠ ringChar K73cubic :=
  GenericHonestCommitment.Concrete.f73_strict_q_le_inhabited

/-- `11 < char` plus `1 < q ≤ char` likewise does not force equality. -/
theorem eleven_lt_and_q_le_do_not_give_q_eq :
    ¬ ∀ (q n : ℕ), 11 < n → 1 < q → q ≤ n → q = n :=
  GenericHonestData.eleven_lt_and_q_le_do_not_give_q_eq

/-! ## Axis 2. Weakening: field remains; tick is modelling, not derived from `E`;
    C8 not added -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Three-field eta: if C8 were a fourth `ResidualPremises` field, or if
`firstLine` were still a field, this would not compile. -/
theorem residualPremises_eta_three
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

/-- Named extra still projects `E.q = ringChar K`. -/
theorem residual_q_eq_ringChar_is_equality
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    E.q = ringChar K :=
  GenericHonestData.residual_q_eq_ringChar_is_equality P

/-- Exhaustive eta: `E` has `q_le_ringChar` and no `q_eq` / C8 field. -/
theorem execution_eta_has_q_le_not_q_eq
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
  GenericHonestCommitment.execution_eta_has_q_le_not_q_eq E

/-- The only characteristic comparison on `E` is the inequality. -/
theorem execution_only_has_q_le
    (E : BuildableNockExecution F K) :
    E.q ≤ ringChar K :=
  GenericHonestCommitment.execution_only_has_q_le E

/-- Already-held on `E` is `1 < q ≤ ringChar`.  No equality field. -/
theorem execution_already_held_is_q_le
    (E : BuildableNockExecution F K) :
    1 < E.q ∧ E.q ≤ ringChar K :=
  GenericHonestData.execution_already_held_is_q_le E

/-- `Data` still asks for the strict equality on top of `E`'s inequality. -/
theorem data_still_requires_q_equality
    {E : BuildableNockExecution F K} (D : Data E) :
    E.q ≤ ringChar K ∧ E.q = ringChar K :=
  GenericHonestCommitment.data_still_requires_q_equality D

/-- `Data` eta still names `q_eq_ringChar` as a constructor extra. -/
theorem data_eta_still_names_q_eq
    {E : BuildableNockExecution F K} (D : Data E) :
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

/-- Residual package copies the same equality. -/
theorem commitmentResidual_still_requires_q_equality
    {E : BuildableNockExecution F K}
    (R : BuildablePackage.CommitmentResidual E) :
    E.q = ringChar K :=
  GenericHonestCommitment.commitmentResidual_still_requires_q_equality R

/-- Outcome 2: residual equality remains a named Lean-package field. -/
theorem residualPremises_still_names_q_eq
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    E.q = ringChar K ∧
      InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) :=
  GenericHonestCommitment.residualPremises_still_names_q_eq P

/-- `CensusRecordPremises` still five fields. -/
theorem censusRecordPremises_eta_five
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } := by
  cases C
  rfl

/-- `MemoryRecordPremises` still two fields. -/
theorem memoryRecordPremises_eta_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } := by
  cases M
  rfl

variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]
variable [Fintype F] [DecidableEq F]

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  Batch128.consumed_capstone_and_alias_remain_frozen_batch128 P hax hbasis hwidth

/-- This is the capstone partition, not the residual-field count. -/
theorem independent_exact_eleven_one_two_accounting :
    Batch91.reviewedSubstantiveFields.length = 11 ∧
      Batch91.reviewedTypeSummaryFields.length = 1 ∧
      Batch91.reviewedResidualFields =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      Batch91.reviewedResidualFields.length = 2 ∧
      (Batch91.reviewedSubstantiveFields ++ Batch91.reviewedTypeSummaryFields ++
        Batch91.reviewedResidualFields).Nodup ∧
      11 + 1 + 2 = 14 :=
  Batch91.exact_eleven_one_two_partition

/-! ## Axis 3. Definitional drift: paper `p` vs Lean `q`; `158-159` vs `1192`;
    CN four-field wording vs three-field Lean -/

/-- Paper names Goldilocks `p`, never Lean `q`.  Honest `q` is 73 or 97,
not `2^{64}-2^{32}+1`.  F97 `q` is not bumped. -/
theorem goldilocks_p_ne_toy_q :
    2 ^ 64 - 2 ^ 32 + 1 ≠ 73 ∧
      2 ^ 64 - 2 ^ 32 + 1 ≠ 97 :=
  ⟨GenericHonestPackage.goldilocks_p_ne_f73_q,
    GenericHonestPackage.goldilocks_p_ne_f97_q⟩

/-- F97 DistinctCensus `q` stays `97`, not Goldilocks. -/
theorem f97_q_not_bumped :
    (distinctCensusExecution hfirstD).q = 97 ∧
      2 ^ 64 - 2 ^ 32 + 1 ≠ 97 :=
  ⟨rfl, GenericHonestPackage.goldilocks_p_ne_f97_q⟩

/-- Package pin is `|F|=p=char(K)`, not NPR `|K|=p³`. -/
theorem f73_package_pin_is_base_card_not_extension_card :
    Fintype.card F73 = ringChar K73cubic ∧
      Fintype.card K73cubic ≠ ringChar K73cubic :=
  GenericHonestPackage.Concrete.f73_package_pin_is_base_card_not_extension_card

/-- Independent F97 cubic: `|K97cubic| = 97³ ≠ 97 = ringChar`.
NPR collision soundness is this cardinality, not
the CN pin. -/
theorem k97_cubic_card_ne_ringChar :
    Fintype.card K97cubic ≠ ringChar K97cubic := by
  have hcard : Fintype.card K97cubic = 97 ^ 3 := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 97 3 (by norm_num)
  rw [hcard, DistinctCensusExecution.ringChar_K97]
  norm_num

theorem residualPremises_still_three_fields
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  GenericHonestCommitment.residualPremises_still_three P

/-- Stale name cited by CN: `residualPremises_still_four` is a three-conjunct
type.  `firstLine` is not among the conjuncts. -/
theorem leftover_still_four_is_three_conjuncts
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  GenericHonestCommitment.residualPremises_still_four P

/-- Stale name `residualPremises_still_four_after_q` is the same three
conjuncts. -/
theorem leftover_still_four_after_q_is_three_conjuncts
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  GenericHonestCommitment.residualPremises_still_four_after_q P

/-- Stale name `residualPremises_still_names_firstLine` does not mention
`firstLine` in its type; three conjuncts including `q_eq_ringChar`. -/
theorem leftover_still_names_firstLine_is_three_conjuncts
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  GenericHonestCommitment.residualPremises_still_names_firstLine P

/-- Classification tuple is three kinds after the `firstLine` drop, not four. -/
theorem residualPremises_kinds_is_three :
    (PremiseKind.leanEncoding, PremiseKind.paperProtocol, PremiseKind.leanEncoding) =
      (.leanEncoding, .paperProtocol, .leanEncoding) :=
  residualPremises_kinds

/-! ## Axis 5. Wrong layer: `11+1+2` is capstone; `q_eq` is a constructor extra;
    not `∀ E, Data E` -/

/-- A generic `ResidualPremises` constructor would force equality for every
buildable execution.  This module supplies no such constructor. -/
theorem generic_residualPremises_would_force_q_equality
    (g : ∀ E : BuildableNockExecution F K, ResidualPremises E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  GenericHonestCommitment.generic_residualPremises_would_force_q_equality g

/-- A generic `Data` constructor would likewise force the package pin.
Not claimed by CN, and not inhabited. -/
theorem generic_data_would_force_q_equality
    (g : ∀ E : BuildableNockExecution F K, Data E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  GenericHonestCommitment.generic_data_would_force_q_equality g

/-- `packageOf` still takes `Data E` and `Inputs E`.  Not `∀ E, Data E`. -/
def packageOf_still_takes_data_and_inputs :=
  @packageOf

/-- Fibre `Accepts` still takes named `ForestExponentOrder` on a supplied `D`.
    Not `∀ D`. -/
theorem packageOf_fibre_still_takes_forest_order
    {E : BuildableNockExecution F K} (D : Data E)
    (hgt : 11 < ringChar K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (horder : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α) :
    ∀ a g : K,
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts (honestCoin E a g)
        E.cfg.challenges.lam :=
  packageOf_fibre_accepts D hgt I hprl hmore hord hordM hrows hgenF hF horder

end

/-! ## Axis 4. -/

#print axioms paper_goldilocks_p
#print axioms f73_q_eq_ringChar
#print axioms distinctCensus_q_eq_ringChar
#print axioms distinctCensus_data_q_eq_ringChar
#print axioms op6_q_eq_ringChar
#print axioms op6_data_q_eq_ringChar
#print axioms op9_q_eq_ringChar
#print axioms op9_data_q_eq_ringChar
#print axioms q_gt_one_and_q_le_do_not_imply_eq
#print axioms f73_strict_q_le_inhabited
#print axioms eleven_lt_and_q_le_do_not_give_q_eq
#print axioms residualPremises_eta_three
#print axioms residual_q_eq_ringChar_is_equality
#print axioms execution_eta_has_q_le_not_q_eq
#print axioms execution_only_has_q_le
#print axioms execution_already_held_is_q_le
#print axioms data_still_requires_q_equality
#print axioms data_eta_still_names_q_eq
#print axioms commitmentResidual_still_requires_q_equality
#print axioms residualPremises_still_names_q_eq
#print axioms censusRecordPremises_eta_five
#print axioms memoryRecordPremises_eta_two
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms independent_exact_eleven_one_two_accounting
#print axioms goldilocks_p_ne_toy_q
#print axioms f97_q_not_bumped
#print axioms f73_package_pin_is_base_card_not_extension_card
#print axioms k97_cubic_card_ne_ringChar
#print axioms residualPremises_still_three_fields
#print axioms leftover_still_four_is_three_conjuncts
#print axioms leftover_still_four_after_q_is_three_conjuncts
#print axioms leftover_still_names_firstLine_is_three_conjuncts
#print axioms residualPremises_kinds_is_three
#print axioms generic_residualPremises_would_force_q_equality
#print axioms generic_data_would_force_q_equality
#print axioms packageOf_still_takes_data_and_inputs
#print axioms packageOf_fibre_still_takes_forest_order
#print axioms optimizedFullStrictNockVMROM_of_package

end Nock.RedTeam.Batch160
