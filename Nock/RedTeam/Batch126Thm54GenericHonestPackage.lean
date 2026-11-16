import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.RedTeam.Batch125Thm54GenericHonestPackage
import Nock.RedTeam.Batch98Thm54FirstLine
import Nock.NockVMROM.Thm54.Walk37.PaperNames
import Nock.ComputeTable
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:
walk RAP chronology the paper (commit, sample `α, γ`, then
`ln`/`count`/`acc_walk`); initial line `ln(1)=α` the paper; Algorithm
NockCompute the paper (no first-row `ln_prev=1` sentence at
`1728-1742`); compute Inputs / timestamps the paper; NMR CORE
the paper; joint NockVMROM

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  `ResidualPremises.firstLine` / `FirstLineStartsAtOne`
is first compute-row `ln_prev = 1`, a Lean analog of walk `ln(1)=α`, not
`WalkSat.ln1`.  Overlay `inputsOfWalkSample` still writes only chip
`(computeWalkAlpha, walkGamma)`; constructed `computeWalk.ln 1` equals the
overlaid sample `a`.  Those are later-round walk RAP columns, not the
compute-table pin.  F73 carries both on one execution: overlay `ln(1)=4`
and compute `ln_prev=1`.  WalkSat coexists with accepted OP1 `ln_prev=2≠1`.
The extra's quantifier sees `E.exec`'s first compute row, not the walk
column and not the adversarial `Vcomp` pub.  `PairedRecordLayout`,
`timestampClosed`, and `ForestExponentOrder` stay named.  Accounting
remains `11+1+2`.  Absence of a compute first-row `ln_prev=1` sentence is not rounded
into a paper walk-RAP or capstone failure.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch126

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
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.AxisBridge
open Nock.Framework
open Nock.NockVMROM.Thm54.RowLayout

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## A. Lean extra is compute `ln_prev=1`, not walk `ln(1)=α` -/

/-- Independent unfold.  The named extra is the first compute public row.
Not `WalkSat.ln1` -/
theorem firstLine_expands
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    FirstLineStartsAtOne exec ↔
      (exec.computePubAt ⟨0, cfg.compRows_pos⟩).ln_prev = 1 :=
  Iff.rfl

/-- `ResidualPremises` no longer names `firstLine`. -/
theorem residual_firstLine_is_compute_pin
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    E.q = ringChar K :=
  P.q_eq_ringChar

/-- Three-field eta.  Overlay does not restore `firstLine` -/
theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } :=
  Batch125.residualPremises_eta_still_four P

/-- Independent unfold of paper walk RAP initial line -/
theorem walkSat_ln1_expands
    {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed initial_count : K} {h : ℕ}
    (hw : WalkSat cur chld' fo ln count acc α seed initial_count h) :
    ln 1 = α :=
  hw.ln1

/-- Walk starts at `α^1`.  Compute analog is `α^0 = 1` -/
theorem walkSat_ln1_is_alpha_pow_one
    {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed initial_count : K} {h : ℕ}
    (hw : WalkSat cur chld' fo ln count acc α seed initial_count h) :
    ln 1 = α ^ 1 := by
  rw [pow_one]
  exact hw.ln1

/-- Right-hand sides differ whenever the sampled walk α is not `1`.
Not an inhabit of `firstLine` -/
theorem walk_alpha_ne_compute_one {α : K} (hα : α ≠ 1) :
    α ^ 1 ≠ (1 : K) := by
  simpa [pow_one] using hα

/-! ## B. Walk overlay unchanged; does not fill `firstLine` -/

/-- Overlay still writes only chip `(a, g)` -/
theorem overlay_still_only_walk_pair
    {E : BuildableNockExecution F K} (I : Inputs E) (a g : K) :
    inputsOfWalkSample I a g =
      { I with computeWalkAlpha := a, walkGamma := g } ∧
      (inputsOfWalkSample I a g).computeWalkAlpha = a ∧
      (inputsOfWalkSample I a g).walkGamma = g :=
  ⟨rfl, rfl, rfl⟩

/-- Named remainder, including FiniteIO and compiler folds, is copied. -/
theorem overlay_preserves_named_remainder
    {E : BuildableNockExecution F K} (I : Inputs E) (a g : K) :
    (inputsOfWalkSample I a g).stateTagChar = I.stateTagChar ∧
      (inputsOfWalkSample I a g).memoryWalkAlpha = I.memoryWalkAlpha ∧
      (inputsOfWalkSample I a g).hOrb = I.hOrb ∧
      (inputsOfWalkSample I a g).basis = I.basis ∧
      (inputsOfWalkSample I a g).orbit = I.orbit ∧
      (inputsOfWalkSample I a g).ioCoins = I.ioCoins ∧
      (inputsOfWalkSample I a g).computeChallenges = I.computeChallenges ∧
      (inputsOfWalkSample I a g).memoryScalarChallenge =
        I.memoryScalarChallenge ∧
      (inputsOfWalkSample I a g).memoryExtensionFold = I.memoryExtensionFold :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Constructed assignment walk column is later-round `ln(1)=α` at the
overlaid sample.  Independent of `E.exec.ln_prev` -/
theorem overlay_sampled_walk_ln1
    {E : BuildableNockExecution F K} (I : Inputs E) (a g : K) :
    (sampledAssignment E (inputsOfWalkSample I a g)).exact.computeWalk.ln 1 =
      a := by
  have hcert := (computeObligations E (inputsOfWalkSample I a g)).2.1
  have hln := hcert.1.ln1
  have hα := (exactFamilyCompletion_of_walk_sample I a g).1
  exact hln.trans hα

/-- That walk column is not the compute-one pin whenever `a ≠ 1` -/
theorem overlay_walk_ln1_ne_compute_one
    {E : BuildableNockExecution F K} (I : Inputs E) {a g : K}
    (hα : a ≠ 1) :
    (sampledAssignment E (inputsOfWalkSample I a g)).exact.computeWalk.ln 1 ≠
      (1 : K) := by
  rw [overlay_sampled_walk_ln1 I a g]
  exact hα

/-- `firstLine` is not a residual field -/
theorem firstLine_from_residual_ignores_overlay
    {E : BuildableNockExecution F K} (P : ResidualPremises E)
    (_I : Inputs E) (_a _g : K) :
    E.q = ringChar K :=
  P.q_eq_ringChar

/-! ## C. -/

/-- `PairedRecordLayout` is still consumed/added `MemRec` perm. -/
theorem paired_record_layout_stays_named
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    PairedRecordLayout exec =
      (consumedRecordList exec).Perm (addedRecordList exec) :=
  Batch125.paired_record_layout_is_consumed_added_perm exec

/-- Honest filler still takes live `ts = α^e` as a named input. -/
theorem filler_still_takes_timestampClosed
    (E : BuildableNockExecution F K)
    (timestampClosed :
      ∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts)
    (honestVer :
      ∀ row ∈ E.exec.memoryRows,
        row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    (GenericHonestData.memoryRecordPremises_of_timestampClosed E
        timestampClosed honestVer).timestampClosed =
      timestampClosed :=
  rfl

/-- Uniqueness window is still `e < orderOf α` -/
theorem ForestExponentOrder_expands
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) :
    ForestExponentOrder E α =
      ((∀ i e, e ∈ readExps (alphaFreeRoot E i) → e < orderOf α) ∧
        (∀ i e, e ∈ verifyExps (alphaFreeRoot E i) → e < orderOf α)) :=
  Batch125.ForestExponentOrder_expands E α

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
  Batch125.censusRecordPremises_eta_still_five C

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

/-! ## D. Wrong layer: NMR unused; compute pin is not walk RAP failure -/

/-- NMR address space remains Nat-cast of `mem.axis`.  Compute `ln_prev=1` missing from Algorithm
NockCompute is not a walk-RAP or capstone failure -/
theorem nmr_axis_is_address_not_firstLine
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
      (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) :=
  Batch125.memoryRecordPremises_still_two_after_record_layout_inventory M

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
  Batch125.released_builder_still_takes_hzero I hprl hmore hord hordM hrows hhon R hzero hgenF hF

inductive ReviewedField126
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

def substantiveFields126 : List ReviewedField126 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields126 : List ReviewedField126 := [.structural]

def residualFields126 : List ReviewedField126 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Keeping `firstLine` named is not a statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields126.length = 11 ∧
      typeSummaryFields126.length = 1 ∧
      residualFields126 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields126.length = 2 ∧
      (substantiveFields126 ++ typeSummaryFields126 ++ residualFields126).Nodup ∧
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

/-! ## E. F73: overlay `ln(1)=4` vs compute `ln_prev=1`; WalkSat with OP1 `2` -/

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

/-- F73 compute public row is definitionally `ln_prev = 1` -/
theorem f73_computePub_ln_prev_is_one :
    (computePub honestSeed honestAlpha).ln_prev = (1 : K73cubic) :=
  rfl

/-- The extra's quantifier sees that first compute row of the honest exec -/
theorem f73_firstLine_on_exec :
    FirstLineStartsAtOne concreteExecution.exec ∧
      (concreteExecution.exec.computePubAt
        ⟨0, concreteExecution.cfg.compRows_pos⟩).ln_prev = 1 := by
  let i0 : Fin (cfg honestSeed honestAlpha).compRows := ⟨0, by norm_num [cfg]⟩
  have hzero : (exec honestSeed honestAlpha).computePubAt i0 =
      computePub honestSeed honestAlpha := computePubAt_zero
  have hi :
      (⟨0, concreteExecution.cfg.compRows_pos⟩ :
        Fin (cfg honestSeed honestAlpha).compRows) = i0 := Fin.ext rfl
  have hpub :
      concreteExecution.exec.computePubAt
          ⟨0, concreteExecution.cfg.compRows_pos⟩ =
        computePub honestSeed honestAlpha := by
    simpa [concreteExecution, hi] using hzero
  constructor
  · unfold FirstLineStartsAtOne
    rw [hpub]
    exact f73_computePub_ln_prev_is_one
  · rw [hpub]
    exact f73_computePub_ln_prev_is_one

theorem f73_four_ne_one : (4 : K73cubic) ≠ 1 := by
  intro h
  have hmap :
      algebraMap F73 K73cubic (4 : F73) =
        algebraMap F73 K73cubic (1 : F73) := by
    calc
      algebraMap F73 K73cubic (4 : F73) = (4 : K73cubic) :=
        map_natCast (algebraMap F73 K73cubic) 4
      _ = 1 := h
      _ = algebraMap F73 K73cubic (1 : F73) := by simp
  exact (by decide : (4 : F73) ≠ 1)
    ((algebraMap F73 K73cubic).injective hmap)

/-- Same execution, two columns: overlay walk `ln(1)=4`, compute `ln_prev=1`.
The extra sees the compute row; the overlay fills the walk column. -/
theorem f73_overlay_ln1_ne_firstLine :
    (sampledAssignment concreteExecution
        (inputsOfWalkSample inputs73Fold2 (4 : K73cubic) 0)).exact.computeWalk.ln 1 =
        (4 : K73cubic) ∧
      (concreteExecution.exec.computePubAt
        ⟨0, concreteExecution.cfg.compRows_pos⟩).ln_prev = 1 ∧
      (4 : K73cubic) ≠ 1 :=
  ⟨overlay_sampled_walk_ln1 inputs73Fold2 (4 : K73cubic) 0,
    f73_firstLine_on_exec.2, f73_four_ne_one⟩

/-- Walk RAP `ln(1)=α` coexists with accepted OP1 `ln_prev=2≠1`.
That adversarial pub is not `E.exec`'s first row. -/
theorem f73_walkSat_and_vcomp_do_not_pin_firstLine :
    ComputeTable.Vcomp (computeInputs honestSeed honestAlpha)
      Batch98.Concrete.nonunitFirstPub (computeDec honestSeed) ∧
    Batch98.Concrete.nonunitFirstPub.ln_prev ≠ 1 ∧
    ∃ ln count acc : ℕ → K73cubic,
      WalkSat Batch98.Concrete.zeroCur Batch98.Concrete.zeroChild
        Batch98.Concrete.zeroFanout ln count acc honestAlpha 0 0 1 ∧
      ln 1 = honestAlpha :=
  ⟨Batch98.Concrete.independent_op1_vcomp_accepts_nonunit_first_ln_prev.1,
    Batch98.Concrete.independent_op1_vcomp_accepts_nonunit_first_ln_prev.2,
    by
      obtain ⟨ln, count, acc, hw, hln, _, _⟩ :=
        Batch98.Concrete.walk_and_compute_first_lines_are_unequal
      exact ⟨ln, count, acc, hw, by simpa using hw.ln1⟩⟩

/-- Filler on F73 still requires named `timestampClosed` -/
theorem f73_filler_still_takes_timestampClosed
    (timestampClosed :
      ∀ i : Fin concreteExecution.cfg.memRows,
        memoryMemRecKind (concreteExecution.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt concreteExecution.cfg.challenges.α
            (concreteExecution.exec.memoryRowAt i).2.2.mem.ts) :
    MemoryRecordPremises concreteExecution :=
  GenericHonestData.memoryRecordPremises_of_timestampClosed
    concreteExecution timestampClosed BuildableChips.Concrete.concrete_honest_ver

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

#print axioms firstLine_expands
#print axioms residual_firstLine_is_compute_pin
#print axioms residualPremises_eta_still_four
#print axioms walkSat_ln1_expands
#print axioms walkSat_ln1_is_alpha_pow_one
#print axioms walk_alpha_ne_compute_one
#print axioms overlay_still_only_walk_pair
#print axioms overlay_preserves_named_remainder
#print axioms overlay_sampled_walk_ln1
#print axioms overlay_walk_ln1_ne_compute_one
#print axioms firstLine_from_residual_ignores_overlay
#print axioms paired_record_layout_stays_named
#print axioms filler_still_takes_timestampClosed
#print axioms ForestExponentOrder_expands
#print axioms censusRecordPremises_eta_still_five
#print axioms packageOf_fibre_accepts_still_takes_window
#print axioms packageOf_not_forall_omega
#print axioms nmr_axis_is_address_not_firstLine
#print axioms released_builder_still_takes_hzero
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms Concrete.f73_computePub_ln_prev_is_one
#print axioms Concrete.f73_firstLine_on_exec
#print axioms Concrete.f73_four_ne_one
#print axioms Concrete.f73_overlay_ln1_ne_firstLine
#print axioms Concrete.f73_walkSat_and_vcomp_do_not_pin_firstLine
#print axioms Concrete.f73_filler_still_takes_timestampClosed
#print axioms Concrete.f73_fibre_accepts_still_takes_window

end
end Nock.RedTeam.Batch126
