import Nock.NockVMROM.Thm54.GenericHonestArrays
import Nock.RedTeam.Batch106Thm54GenericHonestArrays
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  `StateTagChar` remains `InjOn natCast (Iic 11)`.
Independently, `11 < ringChar K` implies that injectivity, including when
the antecedent is uninhabited in characteristic zero (`ringChar = 0`).
The converse and the claimed iff both require `0 < ringChar K`;
characteristic zero satisfies `StateTagChar` and refutes `11 < ringChar`.
the paper is the paper object for bound 11: opcode tags occupy
`{0,...,9} ∪ {11}` with `cons` at 11.  `Iic 11` is the interval hull and
includes unused 10; on fields the two injectivity conditions coincide.
Public `*_of_char` fibre `Accepts` take `11 < ringChar K`, not a free
`StateTagChar`.  Encoding-level constructors still take `StateTagChar`.
Goldilocks `p > 11` is a ℕ inequality; F97 `q` stays 97.  Accounting
remains `11+1+2`.  No `∀ ω`.  No `∀ E`.  `hzero` remains.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch107

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.NodeEncoding
open Nock.NockVMROM.Thm54.ProductionRawVerifier
open Nock.Framework

noncomputable section

/-! ## A. Definition unchanged: still `InjOn natCast (Iic 11)` -/

theorem stateTagChar_def_unchanged {K : Type*} [Field K] :
    NodeEncoding.StateTagChar K =
      Set.InjOn (fun n : ℕ => (n : K)) (Set.Iic 11) :=
  rfl

/-! ## B. Independent forward: `11 < ringChar` ⇒ injectivity on `Iic 11`

Characteristic zero has `ringChar = 0`, so `11 < ringChar` is false and the
implication holds vacuously.  The proof does not cite the production
wrapper. -/

theorem independent_forward {K : Type*} [Field K]
    (h : 11 < ringChar K) :
    Set.InjOn (fun n : ℕ => (n : K)) (Set.Iic 11) := by
  haveI := ringChar.charP K
  intro m hm n hn hmn
  apply CharP.natCast_injOn_Iio K (ringChar K)
  · exact lt_of_le_of_lt hm h
  · exact lt_of_le_of_lt hn h
  · exact hmn

theorem independent_forward_is_stateTagChar {K : Type*} [Field K]
    (h : 11 < ringChar K) :
    NodeEncoding.StateTagChar K :=
  independent_forward h

/-- `ringChar = 0` refutes the paper bound, so the forward map is not a
char-0 constructor -/
theorem ringChar_zero_not_gt_eleven {K : Type*} [Field K]
    (h0 : ringChar K = 0) : ¬ 11 < ringChar K := by
  simp [h0]

/-! ## C. Converse needs `0 < ringChar`; char 0 blocks an unguarded iff -/

theorem independent_converse {K : Type*} [Field K]
    (hchar : Set.InjOn (fun n : ℕ => (n : K)) (Set.Iic 11))
    (hpos : 0 < ringChar K) : 11 < ringChar K := by
  haveI := ringChar.charP K
  by_contra hnot
  have hle : ringChar K ≤ 11 := Nat.not_lt.mp hnot
  have hcast : ((ringChar K : ℕ) : K) = ((0 : ℕ) : K) := by
    simp [CharP.cast_eq_zero]
  have heq : ringChar K = 0 :=
    hchar (show ringChar K ∈ Set.Iic 11 from hle)
      (by simp : (0 : ℕ) ∈ Set.Iic 11) hcast
  exact (Nat.ne_of_gt hpos) heq

theorem independent_iff {K : Type*} [Field K] (hpos : 0 < ringChar K) :
    NodeEncoding.StateTagChar K ↔ 11 < ringChar K :=
  ⟨fun hchar => independent_converse hchar hpos,
    independent_forward_is_stateTagChar⟩

theorem charZero_ringChar_eq_zero {K : Type*} [Field K] [CharZero K] :
    ringChar K = 0 :=
  (CharP.eq K (CharP.ofCharZero K) (ringChar.charP K)).symm

theorem independent_charZero_stateTagChar {K : Type*} [Field K] [CharZero K] :
    NodeEncoding.StateTagChar K := by
  intro m _ n _ hmn
  exact Nat.cast_injective hmn

theorem charZero_not_ringChar_gt_eleven {K : Type*} [Field K] [CharZero K] :
    ¬ 11 < ringChar K :=
  ringChar_zero_not_gt_eleven charZero_ringChar_eq_zero

/-- Unguarded `StateTagChar ↔ 11 < ringChar` fails in characteristic zero.
The production iff is honest only with `0 < ringChar` -/
theorem iff_requires_positive_char {K : Type*} [Field K] [CharZero K] :
    NodeEncoding.StateTagChar K ∧ ¬ 11 < ringChar K :=
  ⟨independent_charZero_stateTagChar, charZero_not_ringChar_gt_eleven⟩

/-! ## D. Paper object at the paper: tags `{0,...,9} ∪ {11}`

The paper has ten Nock opcodes plus `cons` at tag 11; opcode 10 is
unsupported.  Bound 11 is the `cons` tag, not a Lean-only twelfth opcode.
`Iic 11` is the interval hull and includes unused 10. -/

/-- Paper opcode-tag set from the paper. -/
def paperOpcodeFinset : Finset ℕ := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11}

theorem paperOpcodeFinset_card : paperOpcodeFinset.card = 11 := by
  decide

theorem iic_eleven_finset_card : (Finset.Icc 0 11).card = 12 := by
  decide

theorem ten_in_interval_not_paper :
    (10 : ℕ) ∈ Finset.Icc 0 11 ∧ 10 ∉ paperOpcodeFinset := by
  decide

theorem computeStateTag_matches_paper :
    computeStateTag .s0 = 0 ∧
      computeStateTag .s1 = 1 ∧
      computeStateTag .s2 = 2 ∧
      computeStateTag .s3 = 3 ∧
      computeStateTag .s4 = 4 ∧
      computeStateTag .s5 = 5 ∧
      computeStateTag .s6 = 6 ∧
      computeStateTag .s7 = 7 ∧
      computeStateTag .s8 = 8 ∧
      computeStateTag .s9 = 9 ∧
      computeStateTag .cons = 11 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem no_compute_state_is_ten (s : ComputeTable.State) :
    computeStateTag s ≠ 10 := by
  cases s <;> decide

theorem computeStateTag_mem_paper (s : ComputeTable.State) :
    computeStateTag s ∈ paperOpcodeFinset := by
  cases s <;> decide

theorem paperOpcodeFinset_subset_Icc :
    paperOpcodeFinset ⊆ Finset.Icc 0 11 := by
  decide

/-- Interval-hull injectivity implies paper-tag injectivity -/
theorem injOn_Iic_implies_injOn_paper {K : Type*} [Field K]
    (h : Set.InjOn (fun n : ℕ => (n : K)) (Set.Iic 11)) :
    Set.InjOn (fun n : ℕ => (n : K)) (paperOpcodeFinset : Set ℕ) := by
  intro m hm n hn hmn
  have hm' : m ≤ 11 := (Finset.mem_Icc.mp (paperOpcodeFinset_subset_Icc hm)).2
  have hn' : n ≤ 11 := (Finset.mem_Icc.mp (paperOpcodeFinset_subset_Icc hn)).2
  exact h hm' hn' hmn

/-- At characteristic 11, paper tag `cons = 11` collides with opcode 0.
This is why the bound is `11 < char`, not `9 < char` -/
theorem stateTagChar_fails_at_char_eleven :
    letI : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
    ¬ NodeEncoding.StateTagChar (ZMod 11) := by
  intro h
  have hcast : ((0 : ℕ) : ZMod 11) = ((11 : ℕ) : ZMod 11) :=
    (ZMod.natCast_self 11).symm
  have heq : (0 : ℕ) = 11 :=
    h (by simp : (0 : ℕ) ∈ Set.Iic 11) (by simp : (11 : ℕ) ∈ Set.Iic 11) hcast
  omega

/-- Field characteristic is never 10, so unused opcode 10 is not a stronger
field hypothesis than the paper tag set -/
theorem ringChar_ne_ten {K : Type*} [Field K] : ringChar K ≠ 10 := by
  intro h
  haveI := ringChar.charP K
  have hprime := CharP.char_is_prime_or_zero K (ringChar K)
  rw [h] at hprime
  cases hprime with
  | inl hp =>
    have : ¬ Nat.Prime 10 := by decide
    exact this hp
  | inr h0 => omega

theorem prime_le_eleven_mem_paper {p : ℕ} (hp : Nat.Prime p) (hle : p ≤ 11)
    (hpos : 0 < p) : p ∈ paperOpcodeFinset := by
  revert hp
  interval_cases p <;> intro hp
  · exact absurd hp Nat.not_prime_one
  · simp [paperOpcodeFinset]
  · simp [paperOpcodeFinset]
  · exact absurd hp (by decide : ¬ Nat.Prime 4)
  · simp [paperOpcodeFinset]
  · exact absurd hp (by decide : ¬ Nat.Prime 6)
  · simp [paperOpcodeFinset]
  · exact absurd hp (by decide : ¬ Nat.Prime 8)
  · exact absurd hp (by decide : ¬ Nat.Prime 9)
  · exact absurd hp (by decide : ¬ Nat.Prime 10)
  · simp [paperOpcodeFinset]

/-- On positive characteristic, paper-tag injectivity is also `11 < char`.
Primes `≤ 11` all lie in `{0,...,9} ∪ {11}` -/
theorem paper_tags_iff_ringChar_gt_eleven {K : Type*} [Field K]
    (hpos : 0 < ringChar K) :
    Set.InjOn (fun n : ℕ => (n : K)) (paperOpcodeFinset : Set ℕ) ↔
      11 < ringChar K := by
  constructor
  · intro hpaper
    haveI := ringChar.charP K
    by_contra hnot
    have hle : ringChar K ≤ 11 := Nat.not_lt.mp hnot
    have hcast : ((ringChar K : ℕ) : K) = ((0 : ℕ) : K) := by
      simp [CharP.cast_eq_zero]
    have hprime : Nat.Prime (ringChar K) :=
      (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right
        (Nat.pos_iff_ne_zero.mp hpos)
    have hmem : ringChar K ∈ paperOpcodeFinset :=
      prime_le_eleven_mem_paper hprime hle hpos
    have heq : ringChar K = 0 :=
      hpaper hmem (by simp [paperOpcodeFinset]) hcast
    exact (Nat.ne_of_gt hpos) heq
  · intro hgt
    exact injOn_Iic_implies_injOn_paper (independent_forward hgt)

/-! ## E–H use the honest-arrays field bundle -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## E. Public fibre `Accepts` take `11 < ringChar`; encoding-level still takes `StateTagChar` -/

/-- Public residual constructor from the paper bound, not a free `hchar`. -/
theorem of_char_residual_takes_char_bound
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K) :
    (commitmentResidualOfArrays_of_char D hgt).q_eq_ringChar = D.q_eq_ringChar :=
  rfl

theorem fibre_of_char_takes_char_bound
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K) :
    ∀ a g : K,
      (commitmentResidualOfArrays_of_char D hgt).verifier.Accepts
        (honestCoin E a g) E.cfg.challenges.lam :=
  fibre_residual_accepts_of_char D hgt

/-- Encoding-level fibre still takes a `StateTagChar` argument. -/
theorem encoding_fibre_still_takes_stateTagChar
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) :
    ∀ a g : K,
      (commitmentResidualOfArrays D hchar).verifier.Accepts (honestCoin E a g) E.cfg.challenges.lam :=
  fibre_residual_accepts D hchar

theorem of_char_is_encoding_conversion
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K) :
    commitmentResidualOfArrays_of_char D hgt =
      commitmentResidualOfArrays D (stateTagChar_of_paper_char hgt) :=
  rfl

theorem fibre_of_char_eq_encoding
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K) :
    fibre_residual_accepts_of_char D hgt =
      fibre_residual_accepts D (stateTagChar_of_paper_char hgt) :=
  rfl

theorem of_char_still_not_forall_omega
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (lmb : K) :
    ¬ ∀ ω : JointCoins K, (rawStrategyOf D hchar).Accepts ω lmb := by
  intro h
  have h0 := h ((0, 0), (0, 0))
  simp [TemplateRawJointSoundness.Strategy.Accepts, nprSeed] at h0

/-! ## F. Goldilocks is a ℕ pin; F97 `q` is not bumped; `1 < q` and char 2 remain -/

theorem independent_goldilocks_p_gt_eleven :
    11 < 2 ^ 64 - 2 ^ 32 + 1 := by
  norm_num

theorem goldilocks_p_ne_f97_q :
    2 ^ 64 - 2 ^ 32 + 1 ≠ 97 := by
  norm_num

theorem goldilocks_p_ne_f73_q :
    2 ^ 64 - 2 ^ 32 + 1 ≠ 73 := by
  norm_num

theorem one_lt_q_does_not_force_char_gt_eleven :
    ¬ ∀ (q n : ℕ), 1 < q → q ≤ n → 11 < n :=
  GenericHonestArrays.q_gt_one_does_not_give_stateTagChar

theorem stateTagChar_fails_at_char_two :
    ¬ NodeEncoding.StateTagChar (ZMod 2) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have hcast : ((0 : ℕ) : ZMod 2) = ((2 : ℕ) : ZMod 2) :=
    (ZMod.natCast_self 2).symm
  have heq : (0 : ℕ) = 2 :=
    h (by simp : (0 : ℕ) ∈ Set.Iic 11) (by simp : (2 : ℕ) ∈ Set.Iic 11) hcast
  omega

/-! ## G. Named premises and `hzero` remain -/

theorem censusRecordPremises_eta_still_five
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

theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

theorem released_builder_still_takes_hzero
    {E : BuildableNockExecution F K}
    (I : BuildableChips.Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = default)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    -- The package carries `rowsBound`.
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    Nonempty
      (OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K I.hOrb) :=
  GenericHonestArrays.released_builder_still_takes_hzero I R hzero hprl hmore hord hordM hrows hgenF hF

theorem any_universal_residual_still_forces_q_pin
    (g : ∀ E : BuildableNockExecution F K, CommitmentResidual E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  GenericHonestArrays.generic_residual_would_force_q_equality (F := F) (K := K) g

/-! ## H. F73: `11 < char` inhabited; `of_char` residual is `rfl` -/

namespace Concrete

open ConcreteStrictPackage
open BuildableConcrete
open HonestCommitment.Concrete
open GenericHonestArrays.Concrete

local instance : Fact (Nat.Prime 73) := concrete_prime73
noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

theorem f73_char_gt_eleven : 11 < ringChar K73cubic :=
  GenericHonestArrays.Concrete.f73_char_gt_eleven

theorem residual73_of_char_rfl :
    residual73Honest_of_char = residual73Honest :=
  rfl

theorem residual73_fibre_of_char :
    ∀ a g : K73cubic,
      residual73Honest_of_char.verifier.Accepts
        (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam :=
  residual73Honest_fibre_residual_accepts_of_char

theorem residual73_still_rejects_zero_seed :
    ¬ (rawStrategyOf data73 stateTagChar73).Accepts ((0, 0), (0, 0))
      concreteExecution.cfg.challenges.lam := by
  simp [TemplateRawJointSoundness.Strategy.Accepts, nprSeed]

end Concrete

/-! ## I. -/

inductive ReviewedField107
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

def substantiveFields107 : List ReviewedField107 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields107 : List ReviewedField107 := [.structural]

def residualFields107 : List ReviewedField107 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

theorem independent_exact_eleven_one_two_accounting :
    substantiveFields107.length = 11 ∧
      typeSummaryFields107.length = 1 ∧
      residualFields107 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields107.length = 2 ∧
      (substantiveFields107 ++ typeSummaryFields107 ++ residualFields107).Nodup ∧
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

#print axioms stateTagChar_def_unchanged
#print axioms independent_forward
#print axioms independent_forward_is_stateTagChar
#print axioms ringChar_zero_not_gt_eleven
#print axioms independent_converse
#print axioms independent_iff
#print axioms charZero_ringChar_eq_zero
#print axioms independent_charZero_stateTagChar
#print axioms charZero_not_ringChar_gt_eleven
#print axioms iff_requires_positive_char
#print axioms paperOpcodeFinset_card
#print axioms iic_eleven_finset_card
#print axioms ten_in_interval_not_paper
#print axioms computeStateTag_matches_paper
#print axioms no_compute_state_is_ten
#print axioms computeStateTag_mem_paper
#print axioms paperOpcodeFinset_subset_Icc
#print axioms injOn_Iic_implies_injOn_paper
#print axioms stateTagChar_fails_at_char_eleven
#print axioms ringChar_ne_ten
#print axioms prime_le_eleven_mem_paper
#print axioms paper_tags_iff_ringChar_gt_eleven
#print axioms of_char_residual_takes_char_bound
#print axioms fibre_of_char_takes_char_bound
#print axioms encoding_fibre_still_takes_stateTagChar
#print axioms of_char_is_encoding_conversion
#print axioms fibre_of_char_eq_encoding
#print axioms of_char_still_not_forall_omega
#print axioms independent_goldilocks_p_gt_eleven
#print axioms goldilocks_p_ne_f97_q
#print axioms goldilocks_p_ne_f73_q
#print axioms one_lt_q_does_not_force_char_gt_eleven
#print axioms stateTagChar_fails_at_char_two
#print axioms censusRecordPremises_eta_still_five
#print axioms residualPremises_eta_still_four
#print axioms released_builder_still_takes_hzero
#print axioms any_universal_residual_still_forces_q_pin
#print axioms Concrete.f73_char_gt_eleven
#print axioms Concrete.residual73_of_char_rfl
#print axioms Concrete.residual73_fibre_of_char
#print axioms Concrete.residual73_still_rejects_zero_seed
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.fibre_residual_accepts_of_char
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.stateTagChar_iff_paper_char
#print axioms Nock.NockVMROM.Thm54.NodeEncoding.stateTagChar_iff_ringChar_gt_eleven
#print axioms Nock.NockVMROM.Thm54.NodeEncoding.goldilocks_p_gt_eleven
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch107
