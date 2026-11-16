import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.NockVMROM.Thm54.DistinctCensusExecution
import Nock.RedTeam.Batch126Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:
RAP parameters `F ≡ F_p` Goldilocks `p = 2^{64}-2^{32}+1`, `K` degree 3; nouns in `N^λ(F)`; NPR collision
soundness in `|K|`; OP4 `(1+n) mod p`; opcode one-hot bound 11; NMR CORE
the paper; joint NockVMROM

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  `ResidualPremises.q_eq_ringChar` is the execution pin
`E.q = ringChar K`.  Already-held `1 < q ≤ ringChar` is an inequality on `E`
with no equality field.  Already-held `11 < ringChar` inhabits opcode-tag
`StateTagChar` = `InjOn natCast (Iic 11)`, a different object.  Assembled
`combinedBounded` still takes named `P.q_eq_ringChar` to transport
`11 < ringChar` onto `11 < E.q`.  Nat witness `q=12`, `n=73` inhabits
`11 < n`, `1 < q ≤ n`, and `q ≠ n`.  Paper `|F|=p=char(K)` is the package
pin; NPR `|K|=p³` is a different cardinality.  F73 constructor chose
`q := 73 = char` while `|K|=73³ ≠ char`.  F97 fixture `q` stays `97`, not
Goldilocks.  Overlay `inputsOfPaperChar` still rewrites only `stateTagChar`.
`inactiveDec` and `axisAtoms` stay named.  Accounting remains `11+1+2`.
The extra is
not rounded into a paper-field or capstone failure.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch127

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.NodeEncoding
open Nock.AxisBridge
open Nock.Framework
open Nock.NockVMROM.Thm54.RowLayout

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## A. Extra is `E.q = ringChar K`, not `q ≤ ringChar` and not `11 < ringChar` -/

/-- Independent unfold.  The named extra's field type is equality of the
execution bound with the field characteristic.  Not `q ≤ ringChar`. -/
theorem residual_q_eq_ringChar_expands
    {E : BuildableNockExecution F K} :
    ResidualPremises E → E.q = ringChar K :=
  ResidualPremises.q_eq_ringChar

/-- Same pin on `ResidualPremises` -/
theorem residual_q_eq_ringChar_is_equality
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    E.q = ringChar K :=
  P.q_eq_ringChar

/-- Same pin on committed `Data`.  Overlay does not rewrite `Data`. -/
theorem data_q_eq_ringChar_is_equality
    {E : BuildableNockExecution F K} (D : Data E) :
    E.q = ringChar K :=
  D.q_eq_ringChar

/-- Already-held on `E` is the inequality.  No equality field. -/
theorem execution_already_held_is_q_le
    (E : BuildableNockExecution F K) :
    1 < E.q ∧ E.q ≤ ringChar K :=
  ⟨E.q_gt_one, E.q_le_ringChar⟩

/-- Exhaustive eta: `E` has `q_le_ringChar` and no `q_eq` field. -/
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

/-- Opcode-tag extra is `InjOn natCast (Iic 11)`, not `q = ringChar`. -/
theorem stateTagChar_def_unchanged :
    NodeEncoding.StateTagChar K =
      Set.InjOn (fun n : ℕ => (n : K)) (Set.Iic 11) :=
  rfl

/-- Independently, `11 < ringChar` inhabits opcode-tag injectivity.
This is not the execution pin -/
theorem independent_eleven_lt_inhabits_stateTagChar
    (h : 11 < ringChar K) :
    Set.InjOn (fun n : ℕ => (n : K)) (Set.Iic 11) := by
  haveI := ringChar.charP K
  intro m hm n hn hmn
  apply CharP.natCast_injOn_Iio K (ringChar K)
  · exact lt_of_le_of_lt hm h
  · exact lt_of_le_of_lt hn h
  · exact hmn

theorem already_held_eleven_lt_inhabits_stateTagChar
    (hgt : 11 < ringChar K) :
    NodeEncoding.StateTagChar K :=
  independent_eleven_lt_inhabits_stateTagChar hgt

/-! ## B. Nat witness is non-vacuous and matches the extra's shape -/

/-- Requested witness: `11 < 73`, `1 < 12 ≤ 73`, and `12 ≠ 73`.
This is the extra's implication shape on `ℕ`, not a field claim. -/
theorem nat_witness_q_twelve_n_seventy_three :
    11 < 73 ∧ 1 < 12 ∧ (12 : ℕ) ≤ 73 ∧ (12 : ℕ) ≠ 73 := by
  decide

/-- `11 < char` plus `1 < q ≤ char` does not force `q = char`. -/
theorem eleven_lt_and_q_le_do_not_give_q_eq :
    ¬ ∀ (q n : ℕ), 11 < n → 1 < q → q ≤ n → q = n := by
  intro h
  have : (12 : ℕ) = 73 :=
    h 12 73 nat_witness_q_twelve_n_seventy_three.1
      nat_witness_q_twelve_n_seventy_three.2.1
      nat_witness_q_twelve_n_seventy_three.2.2.1
  exact nat_witness_q_twelve_n_seventy_three.2.2.2 this

/-- Transporting `11 < ringChar` to `11 < E.q` needs equality, not `q ≤ char`. -/
theorem eleven_lt_char_does_not_give_eleven_lt_q :
    ¬ ∀ (q n : ℕ), 11 < n → q ≤ n → 11 < q := by
  intro h
  have : 11 < 2 := h 2 73 (by decide) (by decide)
  exact Nat.not_lt.mpr (by decide : (2 : ℕ) ≤ 11) this

/-- A constructor from `E` plus `11 < ringChar` would still have to
manufacture equality. -/
theorem generic_residual_from_eleven_lt_would_force_q_equality
    (g : ∀ (E : BuildableNockExecution F K), 11 < ringChar K →
      ResidualPremises E) :
    ∀ (E : BuildableNockExecution F K), 11 < ringChar K →
      E.q = ringChar K :=
  fun E hgt => (g E hgt).q_eq_ringChar

/-! ## C. `|K|=p³` is a different quantity; extra is not that equation -/

/-- Paper Goldilocks prime is not the F73 or F97 fixture `q`. -/
theorem goldilocks_p_ne_f73_q : 2 ^ 64 - 2 ^ 32 + 1 ≠ 73 := by
  norm_num

theorem goldilocks_p_ne_f97_q : 2 ^ 64 - 2 ^ 32 + 1 ≠ 97 := by
  norm_num

theorem goldilocks_p_gt_eleven : 11 < 2 ^ 64 - 2 ^ 32 + 1 := by
  norm_num

/-- Overlay still rewrites only opcode-tag `stateTagChar`. -/
theorem overlay_is_with_stateTagChar
    {E : BuildableNockExecution F K} (I : Inputs E)
    (hgt : 11 < ringChar K) :
    inputsOfPaperChar I hgt =
      { I with stateTagChar :=
          NodeEncoding.stateTagChar_of_ringChar_gt_eleven hgt } :=
  rfl

/-- Named remainder, including FiniteIO and compiler folds, is copied. -/
theorem overlay_preserves_named_remainder
    {E : BuildableNockExecution F K} (I : Inputs E)
    (hgt : 11 < ringChar K) :
    (inputsOfPaperChar I hgt).computeWalkAlpha = I.computeWalkAlpha ∧
      (inputsOfPaperChar I hgt).memoryWalkAlpha = I.memoryWalkAlpha ∧
      (inputsOfPaperChar I hgt).walkGamma = I.walkGamma ∧
      (inputsOfPaperChar I hgt).hOrb = I.hOrb ∧
      (inputsOfPaperChar I hgt).basis = I.basis ∧
      (inputsOfPaperChar I hgt).orbit = I.orbit ∧
      (inputsOfPaperChar I hgt).ioCoins = I.ioCoins ∧
      (inputsOfPaperChar I hgt).computeChallenges = I.computeChallenges ∧
      (inputsOfPaperChar I hgt).memoryScalarChallenge =
        I.memoryScalarChallenge ∧
      (inputsOfPaperChar I hgt).memoryExtensionFold = I.memoryExtensionFold :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `q_eq_ringChar` lives on `E` / `ResidualPremises`.  Overlay arguments
cannot supply it -/
theorem q_eq_from_residual_ignores_overlay
    {E : BuildableNockExecution F K} (P : ResidualPremises E)
    (_I : Inputs E) (_hgt : 11 < ringChar K) :
    E.q = ringChar K :=
  P.q_eq_ringChar

/-- Assembled `combinedBounded` still names the extra: the inhabit takes
`ResidualPremises` and projects `P.q_eq_ringChar` -/
theorem combinedBounded_at_consumed_q_still_names_q_eq
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (hs : (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q)
    (hgt : 11 < ringChar K) :
    CombinedBoundedBy K E.q
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) ∧
      E.q = ringChar K :=
  ⟨GenericHonestData.combinedBounded_of_skeletonBounded_at_consumed_q
      E P M hs hgt,
    P.q_eq_ringChar⟩

/-- Four-field eta still names `q_eq_ringChar`.  Overlay does not delete it. -/
theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } :=
  Batch126.residualPremises_eta_still_four P

/-- Named remainder of `ResidualPremises` after the char inventory. -/
theorem residualPremises_still_four_after_q_eq_inventory
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  ⟨P.inactiveDec, P.axisAtoms, P.q_eq_ringChar⟩

/-! ## D. -/

/-- Census extras remain five named fields. -/
theorem censusRecordPremises_eta_still_five
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } :=
  Batch126.censusRecordPremises_eta_still_five C

/-- Uniqueness window is still `e < orderOf α` -/
theorem ForestExponentOrder_expands
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) :
    ForestExponentOrder E α =
      ((∀ i e, e ∈ readExps (alphaFreeRoot E i) → e < orderOf α) ∧
        (∀ i e, e ∈ verifyExps (alphaFreeRoot E i) → e < orderOf α)) :=
  Batch126.ForestExponentOrder_expands E α

/-- Generic fibre `Accepts` still takes `ForestExponentOrder`.  Not `∀ ω`. -/
theorem packageOf_fibre_accepts_still_takes_window
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
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
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts (honestCoin E a g) E.cfg.challenges.lam :=
  GenericHonestPackage.packageOf_fibre_accepts D hgt I hprl hmore hord hordM hrows hgenF hF horder

theorem packageOf_not_forall_omega
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F) (lmb : K) :
    ¬ ∀ ω : JointCoins K, (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts ω lmb :=
  GenericHonestPackage.packageOf_not_forall_omega D hgt I hprl hmore hord hordM hrows hgenF hF (lmb := lmb)

/-! ## E. Wrong layer: NMR unused; extra is not a paper-field failure -/

/-- NMR address space remains Nat-cast of `mem.axis`.  Named `q = char` is not a paper-field or
capstone failure -/
theorem nmr_axis_is_address_not_q_eq
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
      (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) :=
  Batch126.nmr_axis_is_address_not_firstLine M

theorem released_builder_still_takes_hzero
    {E : BuildableNockExecution F K}
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = default)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    Nonempty (OptimizedFullStrictNockVMROMPackage F K I.hOrb) :=
  Batch126.released_builder_still_takes_hzero I hprl hmore hord hordM hrows hhon R hzero hgenF hF

inductive ReviewedField127
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

def substantiveFields127 : List ReviewedField127 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields127 : List ReviewedField127 := [.structural]

def residualFields127 : List ReviewedField127 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Keeping `q_eq_ringChar` named is not a statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields127.length = 11 ∧
      typeSummaryFields127.length = 1 ∧
      residualFields127 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields127.length = 2 ∧
      (substantiveFields127 ++ typeSummaryFields127 ++ residualFields127).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

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
  ⟨optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth, rfl⟩

/-! ## F. F97 fixture `q` stays `97`, not Goldilocks -/

namespace F97Fixture

open DistinctCensusExecution
open OptimizedStrictNonterminalConcrete

local instance prime97d : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97d : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

-- Form R leftover first-row counts (live is `chainOneBitWeight`).
variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
include hfirstD

/-- F97 fixture `q` is still the constructor value `97`, not Goldilocks. -/
theorem f97_q_not_bumped :
    (distinctCensusExecution hfirstD).q = 97 ∧
      2 ^ 64 - 2 ^ 32 + 1 ≠ 97 :=
  ⟨rfl, goldilocks_p_ne_f97_q⟩

end F97Fixture

/-! ## G. F73: `|F|=char`, `|K|≠char`; equality is constructor `q := 73` -/

namespace Concrete

open ConcreteStrictPackage
open BuildableConcrete
open HonestCommitment.Concrete
open GenericHonestArrays.Concrete
open BuildableChips.Concrete
open GenericHonestPackage.Concrete

local instance : Fact (Nat.Prime 73) := concrete_prime73
noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- F73 already-held `11 < ringChar` is about `K`, not `E.q = char`. -/
theorem f73_already_held_eleven_lt :
    11 < ringChar K73cubic :=
  GenericHonestPackage.Concrete.f73_already_held_eleven_lt

/-- F73 execution already carries the inequality -/
theorem f73_already_held_q_le :
    1 < concreteExecution.q ∧ concreteExecution.q ≤ ringChar K73cubic :=
  execution_already_held_is_q_le concreteExecution

/-- Independent base-field cardinality: `|F_p| = p` -/
theorem f73_base_card_eq_seventy_three :
    Fintype.card F73 = 73 := by
  simp [F73]

/-- Independent characteristic: `char(K) = 73` -/
theorem f73_ringChar_eq_seventy_three :
    ringChar K73cubic = 73 := by
  rw [← Algebra.ringChar_eq F73 K73cubic, ZMod.ringChar_zmod_n]

/-- Package pin is `|F|=p=char(K)` -/
theorem f73_base_card_eq_ringChar :
    Fintype.card F73 = ringChar K73cubic := by
  rw [f73_base_card_eq_seventy_three, f73_ringChar_eq_seventy_three]

/-- NPR soundness uses `|K|`.  On the cubic
`K = F_{p^3}` that cardinality is `p^3`, not `p` -/
theorem f73_cubic_card_eq_p_cubed :
    Fintype.card K73cubic = 73 ^ 3 := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 73 3 (by norm_num)

/-- Extra is not `|K|=char` -/
theorem f73_package_pin_is_base_card_not_extension_card :
    Fintype.card F73 = ringChar K73cubic ∧
      Fintype.card K73cubic ≠ ringChar K73cubic := by
  refine ⟨f73_base_card_eq_ringChar, ?_⟩
  rw [f73_cubic_card_eq_p_cubed, f73_ringChar_eq_seventy_three]
  norm_num

/-- F73 equality is the constructor choice `q := 73` -/
theorem f73_q_pin_is_constructor_choice :
    concreteExecution.q = 73 ∧
      concreteExecution.q = ringChar K73cubic ∧
      concreteExecution.q ≤ ringChar K73cubic :=
  ⟨rfl, f73_ringChar_eq_seventy_three.symm, concreteExecution.q_le_ringChar⟩

/-- Strict `q < char` is compatible with already-held `11 < ringChar`.
Witness `q = 12` matches the Nat extra-shape -/
theorem f73_strict_q_compatible_with_eleven_lt :
    11 < ringChar K73cubic ∧
      ∃ q : ℕ, 1 < q ∧ q ≤ ringChar K73cubic ∧ q ≠ ringChar K73cubic :=
  ⟨f73_already_held_eleven_lt,
    ⟨12, by
      refine ⟨by decide, ?hle, ?hne⟩
      · rw [f73_ringChar_eq_seventy_three]; decide
      · rw [f73_ringChar_eq_seventy_three]; decide⟩⟩

/-- Overlay still does not rewrite F73 `q` -/
theorem f73_overlay_preserves_q_and_io :
    concreteExecution.q = 73 ∧
      inputs73PaperChar.ioCoins = inputs73Fold2.ioCoins ∧
      inputs73PaperChar.computeChallenges = inputs73Fold2.computeChallenges :=
  ⟨rfl, rfl, rfl⟩

-- Form R leftover LaterSeedZeros residual.
variable (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution)
include hmore73

/-- Generic fibre `Accepts` on the F73 package still takes
`ForestExponentOrder`. -/
theorem f73_fibre_accepts_still_takes_window
    (horder : ForestExponentOrder
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α) :
    ∀ a g : K73cubic,
      (package73Of hmore73).strategy.Accepts (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam :=
  GenericHonestPackage.Concrete.package73Of_fibre_accepts hmore73 horder

end Concrete

#print axioms residual_q_eq_ringChar_expands
#print axioms residual_q_eq_ringChar_is_equality
#print axioms data_q_eq_ringChar_is_equality
#print axioms execution_already_held_is_q_le
#print axioms execution_eta_has_q_le_not_q_eq
#print axioms stateTagChar_def_unchanged
#print axioms independent_eleven_lt_inhabits_stateTagChar
#print axioms already_held_eleven_lt_inhabits_stateTagChar
#print axioms nat_witness_q_twelve_n_seventy_three
#print axioms eleven_lt_and_q_le_do_not_give_q_eq
#print axioms eleven_lt_char_does_not_give_eleven_lt_q
#print axioms generic_residual_from_eleven_lt_would_force_q_equality
#print axioms goldilocks_p_ne_f73_q
#print axioms goldilocks_p_ne_f97_q
#print axioms goldilocks_p_gt_eleven
#print axioms overlay_is_with_stateTagChar
#print axioms overlay_preserves_named_remainder
#print axioms q_eq_from_residual_ignores_overlay
#print axioms combinedBounded_at_consumed_q_still_names_q_eq
#print axioms residualPremises_eta_still_four
#print axioms residualPremises_still_four_after_q_eq_inventory
#print axioms censusRecordPremises_eta_still_five
#print axioms ForestExponentOrder_expands
#print axioms packageOf_fibre_accepts_still_takes_window
#print axioms packageOf_not_forall_omega
#print axioms nmr_axis_is_address_not_q_eq
#print axioms released_builder_still_takes_hzero
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms F97Fixture.f97_q_not_bumped
#print axioms Concrete.f73_already_held_eleven_lt
#print axioms Concrete.f73_already_held_q_le
#print axioms Concrete.f73_base_card_eq_seventy_three
#print axioms Concrete.f73_ringChar_eq_seventy_three
#print axioms Concrete.f73_base_card_eq_ringChar
#print axioms Concrete.f73_cubic_card_eq_p_cubed
#print axioms Concrete.f73_package_pin_is_base_card_not_extension_card
#print axioms Concrete.f73_q_pin_is_constructor_choice
#print axioms Concrete.f73_strict_q_compatible_with_eleven_lt
#print axioms Concrete.f73_overlay_preserves_q_and_io
#print axioms Concrete.f73_fibre_accepts_still_takes_window

end
end Nock.RedTeam.Batch127
