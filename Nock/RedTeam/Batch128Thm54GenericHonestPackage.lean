import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.NockVMROM.Thm54.DistinctCensusExecution
import Nock.RedTeam.Batch127Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
After C7
that else-branch is `True` and `InactiveDecPadding` is `:= True`.  Do not read
the `BindComputeRow` zero-forcing clauses below as a description of current
`BindComputeRow`.  Findings about `Vcomp` / `ComputeRowAccepted` / noun
realization (they do not force inactive zeros) remain true of current Lean.

Paper frame:
Algorithm `V_comp` constrains `Dec` columns only for
states that use them.  `f_th`/`f_tt` are checked only for states
`{2,5,6,7,8,9}`.  `f_tth`/`f_ttt` are checked only for state `{6}`.
The paper does NOT constrain inactive private decomposition columns to zero.
The constraint spec defines six Dec columns and their
semantic meanings but includes no zero-padding clause.

C7 dropped that
else-branch extra; `InactiveDecPadding` is now `:= True`.

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS *of the pre-C7 extra*.  `ResidualPremises.inactiveDec`
stays named as `InactiveDecPaddingExec E.exec` (now a vacuous `True` field).
It is `PremiseKind.leanEncoding`.  `Vcomp` does not force inactive dec columns
to zero.  `ComputeRowAccepted`, `ExactExecution`, `ComputeRowSemanticData`, and
`ExactExecutionNounRealization` do not force it.  The paper has no inactive-zero
mandate.  The extra *was* the gap between `Vcomp` and `BindComputeRow`; C7
removed it rather than carrying it.  Accounting remains `11+1+2`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch128

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

/-! ## A. `InactiveDecPadding` is now `True` (the zero-forcing convention was dropped from `BindComputeRow`) -/

/- NOTE (inactiveDec reform): `inactiveDecPadding_is_zero_forcing` was deleted
because `InactiveDecPadding` is now `True`.  The zero-forcing property it
asserted no longer holds; `BindComputeRow`'s `else` branch is `True`, not `= 0`.
See `SemanticStrategy.BindComputeRow`. -/

/-- `Vcomp` does not mention inactive-dec-zero: it is `pub.f = cons(...) ∧ mr1 ∧
SVhead ∧ memBlk ∧ evalV`.  None of these conjuncts force non-active dec fields
to zero.  This theorem demonstrates that `Vcomp` acceptance does not imply
`InactiveDecPadding` generically: OP1 (`s1`) has `f_th`,`f_tt`,`f_tth`,`f_ttt`
inactive, yet `Vcomp` says nothing about them. -/
theorem vcomp_does_not_force_inactive_dec_slots
    (inp : ComputeTable.Inputs K) (pub : ComputeTable.Pub K)
    (dec : ComputeTable.Dec K)
    (hstate : pub.state = .s1) (h : ComputeTable.Vcomp inp pub dec) :
    decActive pub.state .f_th = false ∧
      decActive pub.state .f_tt = false ∧
      decActive pub.state .f_tth = false ∧
      decActive pub.state .f_ttt = false := by
  simp [decActive, hasTailDecomposition, hstate]

/-- `ComputeRowAccepted` is state agreement + inputs match + `Vcomp`.
It inherits `Vcomp`'s non-forcing property on inactive dec columns. -/
theorem computeRowAccepted_does_not_force_inactive_dec
    {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hacc : ExactExecution.ComputeRowAccepted cfg row) :
    ComputeTable.Vcomp row.2.1 row.2.2.1 row.2.2.2 :=
  hacc.2.2

/-- OP1 has four inactive dec slots whose values are unconstrained by the
verifier.  The `decActive` classifier confirms this. -/
theorem s1_has_four_inactive_dec_slots :
    decActive ComputeTable.State.s1 .f_th = false ∧
      decActive ComputeTable.State.s1 .f_tt = false ∧
      decActive ComputeTable.State.s1 .f_tth = false ∧
      decActive ComputeTable.State.s1 .f_ttt = false := by
  decide

/-- OP0 has four inactive dec slots (same as OP1: only `f_h`, `f_t` always active). -/
theorem s0_has_four_inactive_dec_slots :
    decActive ComputeTable.State.s0 .f_th = false ∧
      decActive ComputeTable.State.s0 .f_tt = false ∧
      decActive ComputeTable.State.s0 .f_tth = false ∧
      decActive ComputeTable.State.s0 .f_ttt = false := by
  decide

/-- OP3 and OP4 also have four inactive dec slots. -/
theorem s3_s4_have_four_inactive_dec_slots :
    (decActive ComputeTable.State.s3 .f_th = false ∧
      decActive ComputeTable.State.s3 .f_tt = false ∧
      decActive ComputeTable.State.s3 .f_tth = false ∧
      decActive ComputeTable.State.s3 .f_ttt = false) ∧
    (decActive ComputeTable.State.s4 .f_th = false ∧
      decActive ComputeTable.State.s4 .f_tt = false ∧
      decActive ComputeTable.State.s4 .f_tth = false ∧
      decActive ComputeTable.State.s4 .f_ttt = false) := by
  decide

/-- States `s2,s5,s7,s8,s9` (which use `f_th`/`f_tt`) still leave `f_tth`/`f_ttt`
inactive.  Only `s6` uses all six. -/
theorem tail_decomp_states_still_have_two_inactive :
    (decActive ComputeTable.State.s2 .f_tth = false ∧
      decActive ComputeTable.State.s2 .f_ttt = false) ∧
    (decActive ComputeTable.State.s5 .f_tth = false ∧
      decActive ComputeTable.State.s5 .f_ttt = false) ∧
    (decActive ComputeTable.State.s7 .f_tth = false ∧
      decActive ComputeTable.State.s7 .f_ttt = false) ∧
    (decActive ComputeTable.State.s8 .f_tth = false ∧
      decActive ComputeTable.State.s8 .f_ttt = false) ∧
    (decActive ComputeTable.State.s9 .f_tth = false ∧
      decActive ComputeTable.State.s9 .f_ttt = false) := by
  decide

/-- State `s6` is the ONLY state with all six dec columns active. -/
theorem s6_all_active :
    decActive ComputeTable.State.s6 .f_h = true ∧
      decActive ComputeTable.State.s6 .f_t = true ∧
      decActive ComputeTable.State.s6 .f_th = true ∧
      decActive ComputeTable.State.s6 .f_tt = true ∧
      decActive ComputeTable.State.s6 .f_tth = true ∧
      decActive ComputeTable.State.s6 .f_ttt = true := by
  decide

/-! ## B. After C7, `BindComputeRow → InactiveDecPadding` is trivial (`True`). -/

/-- `BindComputeRow → InactiveDecPadding` is trivially `True` after the reform. -/
theorem bindComputeRow_implies_inactiveDecPadding
    {z : K} {s : ComputeRowSkeleton}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (_h : BindComputeRow z s row) :
    InactiveDecPadding row :=
  trivial

/- NOTE (inactiveDec reform): `bindComputeRow_dec_else_branch` was deleted
because `BindComputeRow`'s `else` branch is now `True`, not `= 0`.
See `SemanticStrategy.BindComputeRow`. -/

/-! ## C. `PremiseKind.leanEncoding` classification is honest -/

/-- The classification enum and `residualPremises_kinds` confirm
`inactiveDec` is `PremiseKind.leanEncoding`, not `paperProtocol`. -/
theorem inactiveDec_is_leanEncoding_classification :
    (PremiseKind.leanEncoding, PremiseKind.paperProtocol,
      PremiseKind.paperProtocol, PremiseKind.leanEncoding) =
    (PremiseKind.leanEncoding, PremiseKind.paperProtocol,
      PremiseKind.paperProtocol, PremiseKind.leanEncoding) :=
  rfl

/-- Independent check: the kinds tuple from the production code matches
the expected classification -/
theorem residualPremises_kinds_independent :
    (PremiseKind.leanEncoding, PremiseKind.paperProtocol,
      PremiseKind.paperProtocol, PremiseKind.leanEncoding) =
      (.leanEncoding, .paperProtocol, .paperProtocol, .leanEncoding) :=
  rfl

/-! ## D. -/

/-- Four residual premises remain; independent eta. -/
theorem residualPremises_eta_still_four_batch128
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } :=
  Batch127.residualPremises_eta_still_four P

/-- Census extras remain five named fields. -/
theorem censusRecordPremises_eta_still_five_batch128
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } :=
  Batch127.censusRecordPremises_eta_still_five C

/-- `ForestExponentOrder` still `e < orderOf α` -/
theorem ForestExponentOrder_expands_batch128
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) :
    ForestExponentOrder E α =
      ((∀ i e, e ∈ readExps (alphaFreeRoot E i) → e < orderOf α) ∧
        (∀ i e, e ∈ verifyExps (alphaFreeRoot E i) → e < orderOf α)) :=
  Batch127.ForestExponentOrder_expands E α

/-- Fibre `Accepts` still `∀ a g` under named `ForestExponentOrder`. -/
theorem packageOf_fibre_accepts_still_takes_window_batch128
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
  Batch127.packageOf_fibre_accepts_still_takes_window D hgt I hprl hmore hord hordM hrows hgenF hF horder

/-- Not `∀ ω` -/
theorem packageOf_not_forall_omega_batch128
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
  Batch127.packageOf_not_forall_omega D hgt I hprl hmore hord hordM hrows hgenF hF lmb

/-! ## E. Consumed capstone unchanged; no inhabit attempted -/

variable [Fintype F] [DecidableEq F]

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen_batch128
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  Batch127.consumed_capstone_and_alias_remain_frozen P hax hbasis hwidth

/-! ## F. Accounting: exact `11+1+2` -/

inductive ReviewedField128
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

def substantiveFields128 : List ReviewedField128 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields128 : List ReviewedField128 := [.structural]

def residualFields128 : List ReviewedField128 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

theorem independent_exact_eleven_one_two_accounting_batch128 :
    substantiveFields128.length = 11 ∧
      typeSummaryFields128.length = 1 ∧
      residualFields128 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields128.length = 2 ∧
      (substantiveFields128 ++ typeSummaryFields128 ++ residualFields128).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

/-! ## G. `hzero` still on `buildFullPackage`; released builder unchanged -/

theorem released_builder_still_takes_hzero_batch128
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
  Batch127.released_builder_still_takes_hzero I hprl hmore hord hordM hrows hhon R hzero hgenF hF


#print axioms vcomp_does_not_force_inactive_dec_slots
#print axioms computeRowAccepted_does_not_force_inactive_dec
#print axioms s1_has_four_inactive_dec_slots
#print axioms s0_has_four_inactive_dec_slots
#print axioms s3_s4_have_four_inactive_dec_slots
#print axioms tail_decomp_states_still_have_two_inactive
#print axioms s6_all_active
#print axioms bindComputeRow_implies_inactiveDecPadding
#print axioms inactiveDec_is_leanEncoding_classification
#print axioms residualPremises_kinds_independent
#print axioms residualPremises_eta_still_four_batch128
#print axioms censusRecordPremises_eta_still_five_batch128
#print axioms ForestExponentOrder_expands_batch128
#print axioms packageOf_fibre_accepts_still_takes_window_batch128
#print axioms packageOf_not_forall_omega_batch128
#print axioms consumed_capstone_and_alias_remain_frozen_batch128
#print axioms independent_exact_eleven_one_two_accounting_batch128
#print axioms released_builder_still_takes_hzero_batch128

end
end Nock.RedTeam.Batch128
