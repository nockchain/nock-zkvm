import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.RedTeam.Batch111Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  `sizeWindowBound`, sampled `SizeWindow`, and
`ForestExponentOrder` are three different objects.  The named extra is
`n.leaves ≤ Λ` on OP3/OP4/OP6 skeleton products.
Sampled `SizeWindow` is `1 < orderOf z` and `n.leaves < orderOf z`.
`ForestExponentOrder` is `e < orderOf α` on committed template Nats.  `nounSizeBound = E.Λ` is the already-assembled
numeral, not a leaf proof.  The missing hypothesis
`sizeWindowBound_of_SizeWindow_and_order_le_succ_Lambda` requires
`orderOf z ≤ Λ + 1`; that comparison is extra, not `True`, and is not a
weakening of SizeWindow.  A real F73 noun/seed witness has `leaves = Λ + 1`,
satisfies SizeWindow, and fails the extra.  `ForestExponentOrder` uses `α`,
not `z`, and does not supply the comparison.  Census extras stay five.
`Inputs` stays named.  Accounting remains `11+1+2`.  The NPR `Λ` leaf window is not
rounded into a capstone failure of paper SizeWindow.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch112

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
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.AxisBridge
open Nock.Framework

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## A. Three objects stay distinct -/

/-- The named extra expands to the seed-independent leaf bound `n.leaves ≤ Λ`
on OP3/OP4/OP6 skeleton products, not `True` -/
theorem sizeWindowBound_is_leaves_le_Lambda
    {S : SemanticSkeleton} {Λ : ℕ} :
    SizeWindowCounting.SizeWindowNounsBoundedBy S Λ =
      ∀ n ∈ SizeWindowCounting.skeletonSizeWindowNouns S, n.leaves ≤ Λ :=
  rfl

/-- Sampled `SizeWindow` is the multiplicative-order bound at seed `z`.
The definition was not rewritten to `n.leaves ≤ Λ` -/
theorem SizeWindow_is_leaves_lt_orderOf {z : K} {n : Noun} :
    OpcodeSemantics.SizeWindow z n ↔
      1 < orderOf z ∧ n.leaves < orderOf z :=
  ⟨fun hw => ⟨hw.one_lt_order, hw.leaves_lt_order⟩,
    fun h => ⟨h.1, h.2⟩⟩

/-- `ForestExponentOrder` bounds committed template Nats against
`orderOf α`.  The expansion does not mention noun leaves, `Λ`, or `z`. -/
theorem ForestExponentOrder_is_exponent_window
    {T : ExactConfigTemplate F K} (Et : ExactExecutionTemplate T) (α : K) :
    ForestExponentOrder Et α =
      ((∀ i e, e ∈ readExps (alphaFreeRoot Et i) → e < orderOf α) ∧
        (∀ i e, e ∈ verifyExps (alphaFreeRoot Et i) → e < orderOf α)) :=
  rfl

/-- On the honest sample the uniqueness window uses `α`, not the NPR seed
`z` -/
theorem ForestExponentOrder_uses_alpha {E : BuildableNockExecution F K}
    (D : Data E) :
    ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α =
      ((∀ i e, e ∈ readExps
          (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) →
        e < orderOf E.cfg.challenges.α) ∧
        (∀ i e, e ∈ verifyExps
          (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) →
        e < orderOf E.cfg.challenges.α)) :=
  rfl

/-- Already-held numeral: `nounSizeBound` of assembled `Data` is `E.Λ`.
This is not a proof that window-noun leaves are `≤ Λ` -/
theorem nounSizeBound_of_census_is_Lambda
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOfCensus E P M C hln).nounSizeBound = E.Λ ∧
      (dataOfCensus E P M C hln).Λ = E.Λ :=
  ⟨(dataOfCensus_derived_fields E P M C hln).1,
    (dataOfCensus_derived_fields E P M C hln).2.2⟩

/-! ## B. Missing hypothesis is extra, not `True`, not a SizeWindow weakening -/

/-- Independent reconstruction: sampled `SizeWindow` on every skeleton window
noun inhabits `sizeWindowBound` only with `orderOf z ≤ Λ + 1`.
`ForestExponentOrder` is not a hypothesis -/
theorem sizeWindowBound_of_SizeWindow_and_order_le_succ_Lambda
    {S : SemanticSkeleton} {z : K} {Λ : ℕ}
    (hw : ∀ n ∈ SizeWindowCounting.skeletonSizeWindowNouns S,
      OpcodeSemantics.SizeWindow z n)
    (hord : orderOf z ≤ Λ + 1) :
    SizeWindowCounting.SizeWindowNounsBoundedBy S Λ := by
  intro n hn
  exact Nat.lt_succ_iff.mp (lt_of_lt_of_le (hw n hn).leaves_lt_order hord)

/-- SizeWindow itself is a *lower* bound on `orderOf z`.  It does not force
the missing *upper* bound `orderOf z ≤ Λ + 1` -/
theorem SizeWindow_is_lower_bound_on_order {z : K} {n : Noun}
    (hw : OpcodeSemantics.SizeWindow z n) :
    n.leaves + 1 ≤ orderOf z :=
  Nat.succ_le_of_lt hw.leaves_lt_order

/-- A window noun with `leaves = Λ + 1` refutes the named extra. -/
theorem sizeWindowBound_fails_of_leaves_succ
    {S : SemanticSkeleton} {Λ : ℕ} {n : Noun}
    (hn : n ∈ SizeWindowCounting.skeletonSizeWindowNouns S)
    (hleaves : n.leaves = Λ + 1) :
    ¬ SizeWindowCounting.SizeWindowNounsBoundedBy S Λ := by
  intro h
  have : n.leaves ≤ Λ := h n hn
  rw [hleaves] at this
  exact Nat.not_succ_le_self Λ this

/-- SizeWindow can still hold for that noun when `Λ + 1 < orderOf z`.
This uses the unchanged order-window definition -/
theorem SizeWindow_holds_of_leaves_succ_lt_order
    {z : K} {n : Noun} {Λ : ℕ}
    (hleaves : n.leaves = Λ + 1)
    (hord : Λ + 1 < orderOf z) :
    OpcodeSemantics.SizeWindow z n := by
  refine ⟨lt_of_le_of_lt (Nat.le_add_left 1 Λ) hord, ?_⟩
  simpa [hleaves] using hord

/-! ## C. Non-vacuous separation: real noun, real field element, real skeleton -/

/-- Explicit OP3 row whose consumed size-window noun is a two-leaf cell. -/
def windowComputeRow : ComputeRowSkeleton where
  state := .s3
  subject := .atom 0
  formula := .atom 0
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ slot =>
    match slot with
    | .result => .cell (.atom 0) (.atom 0)
    | _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 1⟩

/-- Concrete nonempty semantic skeleton with that OP3 row. -/
def windowSkeleton : SemanticSkeleton where
  computeTree := .node windowComputeRow []
  memoryForest := []

theorem windowSkeleton_computeRows :
    computeSkeletonRows windowSkeleton = [windowComputeRow] := by
  unfold computeSkeletonRows windowSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

/-- The skeleton's unique size-window noun is the two-leaf cell. -/
theorem windowSkeleton_sizeWindowNouns :
    SizeWindowCounting.skeletonSizeWindowNouns windowSkeleton =
      [.cell (.atom 0) (.atom 0)] := by
  rw [SizeWindowCounting.skeletonSizeWindowNouns, windowSkeleton_computeRows]
  rfl

theorem windowCell_leaves :
    (Noun.cell (.atom 0) (.atom 0)).leaves = 2 :=
  rfl

/-- Independent: `4 : F73` has order strictly larger than `2`.  Not a
Goldilocks bump and not a uniqueness-window claim -/
theorem four_two_lt_orderOf :
    2 < orderOf (4 : F73) := by
  have hz : (4 : F73) ≠ 0 := by decide
  have hne1 : (4 : F73) ≠ 1 := by decide
  have hsq : (4 : F73) ^ 2 ≠ 1 := by decide
  have hcard : 0 < Fintype.card F73 - 1 := by
    have h : Fintype.card F73 = 73 := ZMod.card 73
    omega
  have hfin : IsOfFinOrder (4 : F73) :=
    (isOfFinOrder_iff_pow_eq_one).2
      ⟨Fintype.card F73 - 1, hcard,
        FiniteField.pow_card_sub_one_eq_one _ hz⟩
  have hpos : 0 < orderOf (4 : F73) := (orderOf_pos_iff).2 hfin
  by_contra hnot
  have hle : orderOf (4 : F73) ≤ 2 := Nat.not_lt.mp hnot
  have hpow := pow_orderOf_eq_one (4 : F73)
  have h01 : orderOf (4 : F73) = 1 ∨ orderOf (4 : F73) = 2 := by omega
  rcases h01 with h1 | h2
  · rw [h1, pow_one] at hpow
    exact hne1 hpow
  · rw [h2] at hpow
    exact hsq hpow

/-- Real-field SizeWindow inhabitant: two-leaf cell at `z = 4`, `Λ = 1`. -/
theorem SizeWindow_holds_nonvacuous :
    OpcodeSemantics.SizeWindow (4 : F73) (.cell (.atom 0) (.atom 0)) := by
  refine ⟨lt_of_le_of_lt (Nat.le_add_left 1 1) four_two_lt_orderOf, ?_⟩
  simpa [windowCell_leaves] using four_two_lt_orderOf

/-- The same noun fails the named extra at `Λ = 1` -/
theorem sizeWindowBound_fails_nonvacuous :
    ¬ SizeWindowCounting.SizeWindowNounsBoundedBy windowSkeleton 1 :=
  sizeWindowBound_fails_of_leaves_succ
    (S := windowSkeleton) (Λ := 1) (n := .cell (.atom 0) (.atom 0))
    (by simp [windowSkeleton_sizeWindowNouns]) windowCell_leaves

/-- Combined non-vacuity: SizeWindow holds and the extra fails on one real
skeleton/seed/noun.  The distinction is not prose -/
theorem SizeWindow_and_sizeWindowBound_separate_nonvacuous :
    OpcodeSemantics.SizeWindow (4 : F73) (.cell (.atom 0) (.atom 0)) ∧
      ¬ SizeWindowCounting.SizeWindowNounsBoundedBy windowSkeleton 1 :=
  ⟨SizeWindow_holds_nonvacuous, sizeWindowBound_fails_nonvacuous⟩

/-- The missing hypothesis is false on that same witness, so it is extra
rather than a silent consequence of SizeWindow -/
theorem order_le_succ_Lambda_fails_nonvacuous :
    ¬ orderOf (4 : F73) ≤ 1 + 1 := by
  have := four_two_lt_orderOf
  omega

/-- SizeWindow on the skeleton window noun does not inhabit the extra:
the order comparison is missing and is false here -/
theorem SizeWindow_on_skeleton_does_not_inhabit_extra :
    OpcodeSemantics.SizeWindow (4 : F73)
        (.cell (.atom 0) (.atom 0)) ∧
      (.cell (.atom 0) (.atom 0) ∈
        SizeWindowCounting.skeletonSizeWindowNouns windowSkeleton) ∧
      ¬ SizeWindowCounting.SizeWindowNounsBoundedBy windowSkeleton 1 ∧
      ¬ orderOf (4 : F73) ≤ 1 + 1 :=
  ⟨SizeWindow_holds_nonvacuous,
    by simp [windowSkeleton_sizeWindowNouns],
    sizeWindowBound_fails_nonvacuous,
    order_le_succ_Lambda_fails_nonvacuous⟩

/-! ## D. `ForestExponentOrder` does not supply `orderOf z ≤ Λ + 1` -/

/-- α-window and z-window are different generators.  The uniqueness extra
quantifies `orderOf α`; SizeWindow quantifies `orderOf z`. -/
theorem ForestExponentOrder_alpha_ne_SizeWindow_z
    {T : ExactConfigTemplate F K} (Et : ExactExecutionTemplate T)
    (α z : K) (n : Noun) :
    ForestExponentOrder Et α =
      ((∀ i e, e ∈ readExps (alphaFreeRoot Et i) → e < orderOf α) ∧
        (∀ i e, e ∈ verifyExps (alphaFreeRoot Et i) → e < orderOf α)) ∧
      (OpcodeSemantics.SizeWindow z n ↔
        1 < orderOf z ∧ n.leaves < orderOf z) :=
  ⟨ForestExponentOrder_is_exponent_window Et α,
    SizeWindow_is_leaves_lt_orderOf⟩

/-- The sufficient inhabit lemma does not take `ForestExponentOrder`.
Its extra comparison is on `z`, not `α` -/
theorem missing_hyp_is_z_order_not_alpha_window
    {S : SemanticSkeleton} {z : K} {Λ : ℕ}
    (hw : ∀ n ∈ SizeWindowCounting.skeletonSizeWindowNouns S,
      OpcodeSemantics.SizeWindow z n)
    (hord : orderOf z ≤ Λ + 1) :
    SizeWindowCounting.SizeWindowNounsBoundedBy S Λ :=
  sizeWindowBound_of_SizeWindow_and_order_le_succ_Lambda hw hord

/-! ## E. No silent inhabit of another extra; Inputs stay named -/

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

theorem memoryRecordPremises_eta_still_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } := by
  cases M
  rfl

theorem inputs_eta_still_named {E : BuildableNockExecution F K} (I : Inputs E) :
    I =
      { stateTagChar := I.stateTagChar
        computeWalkAlpha := I.computeWalkAlpha
        memoryWalkAlpha := I.memoryWalkAlpha
        walkGamma := I.walkGamma
        hOrb := I.hOrb
        basis := I.basis
        orbit := I.orbit
        activeDomains := I.activeDomains
        ioCoins := I.ioCoins
        ioPoleHitGood := I.ioPoleHitGood
        ioGammaGood := I.ioGammaGood
        ioLogDerivGood := I.ioLogDerivGood
        computeChallenges := I.computeChallenges
        memoryScalarChallenge := I.memoryScalarChallenge
        memoryExtensionFold := I.memoryExtensionFold
        interPoleHitGood := I.interPoleHitGood
        honestVer := I.honestVer
        ioGood10 := I.ioGood10
        interPoleHitGood10 := I.interPoleHitGood10 } := by
  cases I
  rfl

/-- `censusAssemblyOf` still copies `sizeWindowBound` from the named `C`. -/
theorem censusAssemblyOf_still_copies_sizeWindowBound
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).sizeWindowBound = C.sizeWindowBound :=
  rfl

/-- `dataOfCensus` still takes a named five-field `CensusRecordPremises`. -/
theorem dataOfCensus_still_requires_C
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    dataOfCensus E P M C hln =
      dataOfRecord E P M (censusAssemblyOf E P M C) hln :=
  rfl

/-- `packageOf` still takes a named `Inputs` record. -/
theorem packageOf_still_takes_named_Inputs
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
    (hF : GeneratedField.PrimeFieldElems F) :
    packageOf D hgt I hprl hmore hord hordM hrows hgenF hF =
      buildFullPackageWith E I (commitmentResidualOfArrays_of_char D hgt)
        (computeChallenge_pins E I) hprl hmore hord hordM hrows hgenF hF :=
  rfl

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

theorem released_builder_still_takes_hzero
    {E : BuildableNockExecution F K}
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = default)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    Nonempty (OptimizedFullStrictNockVMROMPackage F K I.hOrb) :=
  ⟨buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF⟩

theorem any_universal_data_still_forces_q_pin
    (g : ∀ E : BuildableNockExecution F K, Data E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  GenericHonestPackage.generic_data_would_force_q_equality (F := F) (K := K) g

variable [Fintype F] [DecidableEq F]

/-! ## F. -/

inductive ReviewedField112
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

def substantiveFields112 : List ReviewedField112 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields112 : List ReviewedField112 := [.structural]

def residualFields112 : List ReviewedField112 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Leaving `sizeWindowBound` named is not a statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields112.length = 11 ∧
      typeSummaryFields112.length = 1 ∧
      residualFields112 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields112.length = 2 ∧
      (substantiveFields112 ++ typeSummaryFields112 ++ residualFields112).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

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

theorem containment_is_implication_not_forall_omega
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
    (hax : OptimizedComputeFinalTrace.FormRAxisBound
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    ∀ (ω : JointCoins K) (lmb : K),
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts ω lmb →
        ω ∉ FailureUnion (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
          (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.census lmb →
        GenuineTargetAt (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
          (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).q
          (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.Λ ω lmb :=
  (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).containment

#print axioms sizeWindowBound_is_leaves_le_Lambda
#print axioms SizeWindow_is_leaves_lt_orderOf
#print axioms ForestExponentOrder_is_exponent_window
#print axioms ForestExponentOrder_uses_alpha
#print axioms nounSizeBound_of_census_is_Lambda
#print axioms sizeWindowBound_of_SizeWindow_and_order_le_succ_Lambda
#print axioms SizeWindow_is_lower_bound_on_order
#print axioms sizeWindowBound_fails_of_leaves_succ
#print axioms SizeWindow_holds_of_leaves_succ_lt_order
#print axioms windowSkeleton_computeRows
#print axioms windowSkeleton_sizeWindowNouns
#print axioms windowCell_leaves
#print axioms four_two_lt_orderOf
#print axioms SizeWindow_holds_nonvacuous
#print axioms sizeWindowBound_fails_nonvacuous
#print axioms SizeWindow_and_sizeWindowBound_separate_nonvacuous
#print axioms order_le_succ_Lambda_fails_nonvacuous
#print axioms SizeWindow_on_skeleton_does_not_inhabit_extra
#print axioms ForestExponentOrder_alpha_ne_SizeWindow_z
#print axioms missing_hyp_is_z_order_not_alpha_window
#print axioms censusRecordPremises_eta_still_five
#print axioms residualPremises_eta_still_four
#print axioms memoryRecordPremises_eta_still_two
#print axioms inputs_eta_still_named
#print axioms censusAssemblyOf_still_copies_sizeWindowBound
#print axioms dataOfCensus_still_requires_C
#print axioms packageOf_still_takes_named_Inputs
#print axioms packageOf_not_forall_omega
#print axioms released_builder_still_takes_hzero
#print axioms any_universal_data_still_forces_q_pin
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms containment_is_implication_not_forall_omega
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.sizeWindowBound_is_leaves_le_Lambda
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.SizeWindow_is_leaves_lt_orderOf
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.sizeWindowBound_of_SizeWindow_and_order_le_succ_Lambda
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch112
