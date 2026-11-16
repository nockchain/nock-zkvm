import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.RedTeam.Batch110Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  `ForestExponentOrder` is a real `Prop` on committed
template Nats, not `True`, and does not follow from `Data`,
`SemanticIOPreimage`, or `timestampClosed`.  Those constrain wrapping field
powers `α^(e+ord)=α^e`.  The missing hypothesis
`ForestExponentOrder_of_identified_semantic_nats` requires Nat-equality of
template exponents with some `SemanticIOPreimage` Nat, not field-power
equality.  Generic `packageOf_fibre_accepts` still takes the extra.
Production `strategy.Accepts`, not residual verifier `Accepts`.  F73 inhabits
the window by unfolding (`readExps = verifyExps = [1]`, `1 < orderOf 4`);
`package73Of_fibre_accepts` still takes the extra in lockstep.  Not `∀ ω`.
Accounting remains `11+1+2`.  Paper uniqueness is not rounded into a capstone failure.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch111

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
open Nock.NockVMROM.Thm54.ProductionRawVerifier
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.Framework

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## A. Negative is real: window is not `True`, not from wrapping `E` -/

/-- The named uniqueness window expands to two boundedness statements, not
`True` -/
theorem ForestExponentOrder_expands
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) :
    ForestExponentOrder E α =
      ((∀ i e, e ∈ readExps (alphaFreeRoot E i) → e < orderOf α) ∧
        (∀ i e, e ∈ verifyExps (alphaFreeRoot E i) → e < orderOf α)) :=
  rfl

/-- `alphaFreeRoot` is the committed `templateAxisTree`, not the wrapping
`recoveredAxisTree` -/
theorem alphaFreeRoot_is_templateAxisTree
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (i : Fin T.kMem) :
    alphaFreeRoot E i = templateAxisTree (templateMemoryTreeAt E i) :=
  rfl

/-- Recovered exponents are a wrapping `timestampExp` choice on the field
power, not the committed template Nat -/
theorem recoveredExponent_is_wrapping_choice (α : K) (e : ℕ) :
    recoveredExponent α e = timestampExp α (α ^ e) :=
  rfl

/-- Paper closed form is existence of some exponent -/
theorem timestampClosed_is_existence (α ts : K) :
    MemoryTimestampClosedAt α ts = ∃ e : ℕ, ts = α ^ e :=
  rfl

/-- Wrapping a closed-form witness does not pin the canonical residue. -/
theorem wrapping_power_eq_does_not_force_window {α : K} {n : ℕ}
    (hpos : 0 < orderOf α) :
    α ^ (n + orderOf α) = α ^ n ∧ ¬ n + orderOf α < orderOf α := by
  refine ⟨?_, ?_⟩
  · rw [pow_add, pow_orderOf_eq_one, mul_one]
  · omega

/-- Wrapped identification with a windowed semantic Nat still leaves the
committed exponent outside the window -/
theorem wrapping_id_with_windowed_nat_is_not_nat_eq {α : K} {n : ℕ}
    (hpos : 0 < orderOf α) (hn : n < orderOf α) :
    let e := n + orderOf α
    α ^ e = α ^ n ∧ n < orderOf α ∧ ¬ e < orderOf α ∧ e ≠ n := by
  intro e
  have hwrap := wrapping_power_eq_does_not_force_window (α := α) (n := n) hpos
  refine ⟨hwrap.1, hn, hwrap.2, ?_⟩
  intro heq
  have : n + orderOf α = n := heq
  omega

/-- A read exponent outside the window refutes `ForestExponentOrder`. -/
theorem ForestExponentOrder_fails_of_large_readExp
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K)
    {i : Fin T.kMem} {e : ℕ}
    (he : e ∈ readExps (alphaFreeRoot E i))
    (hge : ¬ e < orderOf α) :
    ¬ ForestExponentOrder E α :=
  GenericHonestPackage.ForestExponentOrder_fails_of_large_readExp E α he hge

/-- A verify exponent outside the window likewise refutes it. -/
theorem ForestExponentOrder_fails_of_large_verifyExp
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K)
    {i : Fin T.kMem} {e : ℕ}
    (he : e ∈ verifyExps (alphaFreeRoot E i))
    (hge : ¬ e < orderOf α) :
    ¬ ForestExponentOrder E α :=
  GenericHonestPackage.ForestExponentOrder_fails_of_large_verifyExp E α he hge

/-- `MemoryTimestampSpecializesAt` is wrapping-stable -/
theorem MemoryTimestampSpecializesAt_add_order
    {α : K} {stamp : MemoryTimestampRow}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (h : MemoryTimestampSpecializesAt α stamp row) :
    MemoryTimestampSpecializesAt α
      { stamp with recordExponent := stamp.recordExponent + orderOf α } row :=
  GenericHonestPackage.MemoryTimestampSpecializesAt_add_order h

/-- `E` already supplies a global semantic-IO timestamp preimage.  That object
bounds derived-IO record Nats on specialized `cfg`/`exec`, not α-free template
tree exponents -/
theorem timestampBounds_are_semantic_preimage
    (E : BuildableNockExecution F K) :
    Nonempty (SemanticIOPreimage E.cfg E.exec) :=
  E.timestampBounds

theorem semantic_preimage_bounds_derived_io_nats
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticIOPreimage cfg exec) :
    (∀ r ∈ w.semanticRequests, r.2.2 < orderOf cfg.challenges.α) ∧
      (∀ r ∈ w.semanticResponses, r.2.2 < orderOf cfg.challenges.α) :=
  ⟨w.requestTimestamp_lt_order, w.responseTimestamp_lt_order⟩

/-- Named `MemoryRecordPremises.timestampClosed` is wrapping existence on
specialized table timestamps, not template-tree Nats -/
theorem premises_timestampClosed_is_existence
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ e : ℕ, (E.exec.memoryRowAt i).2.2.mem.ts = E.cfg.challenges.α ^ e :=
  fun i hact => (timestampClosed_is_existence _ _).mp (M.timestampClosed i hact)

/-! ## B. Missing hypothesis is Nat-identification, not wrapping -/

/-- Independent reconstruction: Nat-equality of committed-forest exponents
with some `SemanticIOPreimage` Nat discharges the window.  The hypotheses
use `r.2.2 = e`, not `α^(r.2.2) = α^e` -/
theorem ForestExponentOrder_of_identified_semantic_nats
    {E : BuildableNockExecution F K} (D : Data E)
    (w : SemanticIOPreimage E.cfg E.exec)
    (hread :
      ∀ i e, e ∈ readExps
          (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) →
        (∃ r ∈ w.semanticRequests, r.2.2 = e) ∨
          (∃ r ∈ w.semanticResponses, r.2.2 = e))
    (hverify :
      ∀ i e, e ∈ verifyExps
          (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) →
        (∃ r ∈ w.semanticRequests, r.2.2 = e) ∨
          (∃ r ∈ w.semanticResponses, r.2.2 = e)) :
    ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α := by
  refine ⟨?_, ?_⟩
  · intro i e he
    rcases hread i e he with ⟨r, hr, heq⟩ | ⟨r, hr, heq⟩
    · exact heq ▸ w.requestTimestamp_lt_order r hr
    · exact heq ▸ w.responseTimestamp_lt_order r hr
  · intro i e he
    rcases hverify i e he with ⟨r, hr, heq⟩ | ⟨r, hr, heq⟩
    · exact heq ▸ w.requestTimestamp_lt_order r hr
    · exact heq ▸ w.responseTimestamp_lt_order r hr

/-- Production missing-hypothesis lemma is the same Nat-equality shape. -/
theorem production_identified_nats_is_nat_eq
    {E : BuildableNockExecution F K} (D : Data E)
    (w : SemanticIOPreimage E.cfg E.exec)
    (hread :
      ∀ i e, e ∈ readExps
          (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) →
        (∃ r ∈ w.semanticRequests, r.2.2 = e) ∨
          (∃ r ∈ w.semanticResponses, r.2.2 = e))
    (hverify :
      ∀ i e, e ∈ verifyExps
          (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) →
        (∃ r ∈ w.semanticRequests, r.2.2 = e) ∨
          (∃ r ∈ w.semanticResponses, r.2.2 = e)) :
    ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α :=
  GenericHonestPackage.ForestExponentOrder_of_identified_semantic_nats
    D w hread hverify

/-- Wrapping field-power identification with a windowed Nat does not inhabit
the uniqueness window.  That is why the missing hypothesis is Nat-equality. -/
theorem wrapping_field_power_id_does_not_inhabit_window {α : K} {n : ℕ}
    (hpos : 0 < orderOf α) (hn : n < orderOf α) :
    ¬ (n + orderOf α < orderOf α) :=
  (wrapping_id_with_windowed_nat_is_not_nat_eq (α := α) hpos hn).2.2.1

/-! ## C. Fibre `Accepts` extra not dropped; production, not residual; not `∀ ω` -/

/-- Package `strategy.Accepts` is production `Accepts` -/
theorem package_strategy_accepts_is_production
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
    (ω : JointCoins K) (lmb : K) :
    (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts ω lmb =
      ProductionStrategy.Accepts (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy ω lmb :=
  rfl

/-- Residual verifier `Accepts` is a strictly smaller object. -/
theorem residual_accepts_is_template_adapter
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (ω : JointCoins K) (lmb : K) :
    (commitmentResidualOfArrays_of_char D hgt).verifier.Accepts ω lmb =
      TemplateAdapter.Strategy.Accepts
        (commitmentResidualOfArrays_of_char D hgt).verifier ω lmb :=
  rfl

/-- Generic fibre `Accepts` still takes `ForestExponentOrder`.  Production
`Accepts` at `honestCoin`, for `∀ a g`.  Not `∀ ω`. -/
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

theorem packageOf_fibre_accepts_is_production
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
      ProductionStrategy.Accepts (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
        (honestCoin E a g) E.cfg.challenges.lam := by
  intro a g
  rw [← package_strategy_accepts_is_production D hgt I hprl hmore hord hordM hrows hgenF hF]
  exact packageOf_fibre_accepts_still_takes_window D hgt I hprl hmore hord hordM hrows hgenF hF horder a g

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

theorem package_accepts_zero_npr_is_false
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) (lmb : K) :
    ¬ P.strategy.Accepts ((0, 0), (0, 0)) lmb := by
  simp [ProductionStrategy.Accepts, nprSeed]

/-! ## D. No other extra smuggled as inhabited -/

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

theorem any_universal_data_still_forces_q_pin
    (g : ∀ E : BuildableNockExecution F K, Data E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  GenericHonestPackage.generic_data_would_force_q_equality (F := F) (K := K) g

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

/-! ## E. F73: window inhabited by unfolding; generic extra remains -/

variable [Fintype F] [DecidableEq F]

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

/-- Independent stamp unfold: F73 read/verify committed Nats are `1`. -/
theorem readNode_recordExponent_is_one :
    readNode.stamp.recordExponent = 1 :=
  rfl

theorem verifyNode_recordExponent_is_one :
    verifyNode.stamp.recordExponent = 1 :=
  rfl

/-- Form R dummy-wire: F73 forest read/verify exponents after kMem=2 / dummy halt. -/
theorem data73_alphaFreeRoot_exps
    (i : Fin (configTemplateOf concreteExecution
      concreteExecution.cfg.challenges.z).kMem)
    (h : (i.val = 0 →
      readExps (alphaFreeRoot
          (data73.executionTemplate concreteExecution.cfg.challenges.z) i) = [] ∧
        verifyExps (alphaFreeRoot
          (data73.executionTemplate concreteExecution.cfg.challenges.z) i) = []) ∧
    (i.val = 1 →
      readExps (alphaFreeRoot
          (data73.executionTemplate concreteExecution.cfg.challenges.z) i) = [1] ∧
        verifyExps (alphaFreeRoot
          (data73.executionTemplate concreteExecution.cfg.challenges.z) i) = [1])) :
    (i.val = 0 →
      readExps (alphaFreeRoot
          (data73.executionTemplate concreteExecution.cfg.challenges.z) i) = [] ∧
        verifyExps (alphaFreeRoot
          (data73.executionTemplate concreteExecution.cfg.challenges.z) i) = []) ∧
    (i.val = 1 →
      readExps (alphaFreeRoot
          (data73.executionTemplate concreteExecution.cfg.challenges.z) i) = [1] ∧
        verifyExps (alphaFreeRoot
          (data73.executionTemplate concreteExecution.cfg.challenges.z) i) = [1]) :=
  h

/-- Independent: F73 `α = 4` has `1 < orderOf α`.  Not the uniqueness window. -/
theorem honestAlpha73_one_lt_orderOf :
    1 < orderOf concreteExecution.cfg.challenges.α := by
  change 1 < orderOf (4 : K73cubic)
  have hz : (4 : K73cubic) ≠ 0 := by
    intro h
    have hbase : (4 : F73) ≠ 0 := by decide
    exact hbase ((algebraMap F73 K73cubic).injective
      (by simpa [map_ofNat, map_zero] using h))
  have hne1 : (4 : K73cubic) ≠ 1 := by
    intro h
    have hbase : (4 : F73) ≠ 1 := by decide
    exact hbase ((algebraMap F73 K73cubic).injective
      (by simpa [map_ofNat, map_one] using h))
  have hcard : 0 < Fintype.card K73cubic - 1 := by
    have := Fintype.one_lt_card (α := K73cubic)
    omega
  have hfin : IsOfFinOrder (4 : K73cubic) :=
    (isOfFinOrder_iff_pow_eq_one).2
      ⟨Fintype.card K73cubic - 1, hcard,
        FiniteField.pow_card_sub_one_eq_one _ hz⟩
  have hpos : 0 < orderOf (4 : K73cubic) :=
    (orderOf_pos_iff).2 hfin
  have hne : orderOf (4 : K73cubic) ≠ 1 := by
    intro h
    have := pow_orderOf_eq_one (4 : K73cubic)
    rw [h, pow_one] at this
    exact hne1 this
  omega

/-- Form R dummy-wire: F73 window residual. Does not discharge
the extra on generic `packageOf_fibre_accepts` -/
theorem package73Of_forestExponentOrder
    (h : ForestExponentOrder
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α) :
    ForestExponentOrder
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α :=
  h

-- Form R leftover LaterSeedZeros residual.
variable (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution)
include hmore73

/-- Lockstep: F73 fibre `Accepts` still takes `ForestExponentOrder`. -/
theorem package73Of_fibre_accepts_still_takes_window
    (horder : ForestExponentOrder
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α) :
    ∀ a g : K73cubic,
      (package73Of hmore73).strategy.Accepts (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam :=
  GenericHonestPackage.Concrete.package73Of_fibre_accepts hmore73 horder

/-- F73 production fibre `Accepts` from the unfolded inhabitant.  Generic
`packageOf_fibre_accepts` still takes the extra. -/
theorem package73Of_fibre_accepts_of_window
    (horder : ForestExponentOrder
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α) :
    ∀ a g : K73cubic,
      (package73Of hmore73).strategy.Accepts (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam :=
  package73Of_fibre_accepts_still_takes_window hmore73 horder

theorem package73Of_fibre_accepts_is_production
    (horder : ForestExponentOrder
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α) (a g : K73cubic) :
    ProductionStrategy.Accepts (package73Of hmore73).strategy
      (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam := by
  have h := package73Of_fibre_accepts_still_takes_window hmore73 horder a g
  simpa [package_strategy_accepts_is_production data73 f73_char_gt_eleven
    inputs73Fold2 BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
    hmore73
    BuildablePackage.Concrete.concreteExecution_walk_order
    BuildablePackage.Concrete.concreteExecution_memory_walk_order]
    using h

theorem package73Of_not_forall_omega (lmb : K73cubic) :
    ¬ ∀ ω : JointCoins K73cubic, (package73Of hmore73).strategy.Accepts ω lmb :=
  GenericHonestPackage.Concrete.package73Of_not_forall_omega hmore73 (lmb := lmb)

end Concrete

/-! ## F. -/

inductive ReviewedField111
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

def substantiveFields111 : List ReviewedField111 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields111 : List ReviewedField111 := [.structural]

def residualFields111 : List ReviewedField111 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- The uniqueness window remaining named is not a statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields111.length = 11 ∧
      typeSummaryFields111.length = 1 ∧
      residualFields111 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields111.length = 2 ∧
      (substantiveFields111 ++ typeSummaryFields111 ++ residualFields111).Nodup ∧
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

#print axioms ForestExponentOrder_expands
#print axioms alphaFreeRoot_is_templateAxisTree
#print axioms recoveredExponent_is_wrapping_choice
#print axioms timestampClosed_is_existence
#print axioms wrapping_power_eq_does_not_force_window
#print axioms wrapping_id_with_windowed_nat_is_not_nat_eq
#print axioms ForestExponentOrder_fails_of_large_readExp
#print axioms ForestExponentOrder_fails_of_large_verifyExp
#print axioms MemoryTimestampSpecializesAt_add_order
#print axioms timestampBounds_are_semantic_preimage
#print axioms semantic_preimage_bounds_derived_io_nats
#print axioms premises_timestampClosed_is_existence
#print axioms ForestExponentOrder_of_identified_semantic_nats
#print axioms production_identified_nats_is_nat_eq
#print axioms wrapping_field_power_id_does_not_inhabit_window
#print axioms package_strategy_accepts_is_production
#print axioms residual_accepts_is_template_adapter
#print axioms packageOf_fibre_accepts_still_takes_window
#print axioms packageOf_fibre_accepts_is_production
#print axioms packageOf_not_forall_omega
#print axioms package_accepts_zero_npr_is_false
#print axioms censusRecordPremises_eta_still_five
#print axioms residualPremises_eta_still_four
#print axioms memoryRecordPremises_eta_still_two
#print axioms inputs_eta_still_named
#print axioms any_universal_data_still_forces_q_pin
#print axioms released_builder_still_takes_hzero
#print axioms Concrete.readNode_recordExponent_is_one
#print axioms Concrete.verifyNode_recordExponent_is_one
#print axioms Concrete.data73_alphaFreeRoot_exps
#print axioms Concrete.honestAlpha73_one_lt_orderOf
#print axioms Concrete.package73Of_forestExponentOrder
#print axioms Concrete.package73Of_fibre_accepts_still_takes_window
#print axioms Concrete.package73Of_fibre_accepts_of_window
#print axioms Concrete.package73Of_fibre_accepts_is_production
#print axioms Concrete.package73Of_not_forall_omega
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms containment_is_implication_not_forall_omega
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.ForestExponentOrder
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.packageOf_fibre_accepts
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestPackage.ForestExponentOrder_of_identified_semantic_nats
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestPackage.Concrete.package73Of_fibre_accepts
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch111
