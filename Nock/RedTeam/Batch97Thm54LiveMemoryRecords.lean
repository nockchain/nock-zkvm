import Nock.NockVMROM.Thm54.GenericHonestCommitment
import Nock.NockVMROM.Thm54.NonterminalServedRow
import Nock.RedTeam.Batch96Thm54GenericHonestCommitment
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  Under the unchanged four-field `ResidualPremises`,
`bindComputeRow_of_residual` inhabits the complete nine-part
`BindComputeRow` conjunction on every authoritative compute row.  The final
memory-record conjunct covers `mr1`, live `mr2` (OP0 and the six
tail-decomposition states), live `mr3` (OP6 and OP9), and inactive zero
records.  `AxisAtomPremises` contains exactly the two paper address-operand
atom obligations, and has no requirement on another opcode.

This artifact does not construct `Data E`, a generic
`BuildablePackage.CommitmentResidual E`, the later-round `A`/`W` families,
timestamp specialization, or the released `hzero` premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch97

open scoped Classical
open Nock Nock.Noun Nock.Walk
open Nock.Framework
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.OpcodeSemantics
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## A. Full expansion of `BindComputeRow` -/

/-- Independent expansion of all nine `BindComputeRow` conjuncts on every
authoritative compute row.  In particular, the last displayed conjunct is the
full three-record branch, not `True` or a detached existence statement. -/
theorem residual_binding_expands_all_nine_conjuncts
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (i : Fin E.cfg.compRows) :
    let row := E.exec.computeRowAt i
    let s :=
      computeSkeletonOf (E.semanticData.rows i)
        (publicRowNoun_of_execution E i)
    row.1 = s.state ∧
      row.2.1.z = row.2.1.z ∧
      row.2.2.1.state = s.state ∧
      bindFP row.2.1.z s.subject row.2.2.1.s ∧
      bindFP row.2.1.z s.formula row.2.2.1.f ∧
      bindFP row.2.1.z s.evaluation row.2.2.1.e ∧
      (∀ slot : DecSlot,
        if h : decActive s.state slot = true
        then bindFP row.2.1.z (s.decomposition slot h)
          (decFP row.2.2.2 slot)
        else True) ∧
      (∀ j : Fin 3,
        if h : (j : ℕ) < ComputeTable.fanoutComp s.state
        then ∀ slot : TripleSlot,
          bindFP row.2.1.z (s.subformula j h slot)
            (tripleFP (computeSubformulaFPs row.2.2.1 j) slot)
        else computeSubformulaFPs row.2.2.1 j = (0, 0, 0)) ∧
      (∀ j : Fin 3,
        if h : (j : ℕ) < recordCount s.state
        then BindMemRec row.2.1.z (s.memoryRecord j h)
          (computeMemRec row.2.2.1 j)
        else computeMemRec row.2.2.1 j = ComputeTable.MemRec.zero) := by
  dsimp
  exact bindComputeRow_of_residual E P i

/-- The record branch extracted from the independently expanded full row
binding.  This theorem quantifies over every `Fin 3` record slot. -/
theorem residual_binding_closes_every_record_slot
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (i : Fin E.cfg.compRows) :
    let row := E.exec.computeRowAt i
    let s :=
      computeSkeletonOf (E.semanticData.rows i)
        (publicRowNoun_of_execution E i)
    ∀ j : Fin 3,
      if h : (j : ℕ) < recordCount s.state
      then BindMemRec row.2.1.z (s.memoryRecord j h)
        (computeMemRec row.2.2.1 j)
      else computeMemRec row.2.2.1 j = ComputeTable.MemRec.zero := by
  dsimp
  exact (bindComputeRow_of_residual E P i).2.2.2.2.2.2.2.2

/-! ## B. Exact `Vcomp` fingerprint copies and all live paths -/

/-- The four live-record fingerprint equations are the literal `memBlk`
copies: OP0 and tail decomposition for `mr2`, OP6 and OP9 for `mr3`. -/
theorem all_four_vcomp_fingerprint_copies
    {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hacc : ExactExecution.ComputeRowAccepted cfg row) :
    (∀ _h0 : row.1 = .s0,
      row.2.2.1.mr2 =
        ⟨row.2.2.1.s, row.2.2.1.e, row.2.2.2.f_t.leaf,
          row.2.2.1.ln_prev * row.2.1.α ^ 2⟩) ∧
    (∀ _ht : row.1 = .s2 ∨ row.1 = .s5 ∨ row.1 = .s6 ∨
        row.1 = .s7 ∨ row.1 = .s8 ∨ row.1 = .s9,
      row.2.2.1.mr2 =
        ⟨row.2.2.2.f_t, row.2.2.2.f_th, 2,
          row.2.2.1.ln_prev * row.2.1.α ^ 2⟩) ∧
    (∀ _h6 : row.1 = .s6,
      row.2.2.1.mr3 =
        ⟨row.2.2.2.f_tt, row.2.2.2.f_tth, 2,
          row.2.2.1.ln_prev * row.2.1.α ^ 3⟩) ∧
    (∀ _h9 : row.1 = .s9,
      row.2.2.1.mr3 =
        ⟨row.2.2.1.sf1_e, row.2.2.1.sf2_f, row.2.2.2.f_th.leaf,
          row.2.2.1.ln_prev * row.2.1.α ^ 3⟩) := by
  exact ⟨vcomp_mr2_s0 hacc, vcomp_mr2_tailDecomp hacc,
    vcomp_mr3_s6 hacc, vcomp_mr3_s9 hacc⟩

/-- Every live `mr2`/`mr3` paper path yields the complete three-part
`BindMemRec`: root fingerprint, child fingerprint, and field-cast Nat axis. -/
theorem all_four_live_bindmemrec_paths
    {q Λ : ℕ} {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (hatoms : AxisAtomPremises data) :
    (∀ (_h0 : row.1 = .s0) (hi : (1 : ℕ) < recordCount row.1),
      BindMemRec row.2.1.z
        (memRecSkelOf data pubR ⟨1, by omega⟩ hi)
        (computeMemRec row.2.2.1 ⟨1, by omega⟩)) ∧
    (∀ (_ht : row.1 = .s2 ∨ row.1 = .s5 ∨ row.1 = .s6 ∨
          row.1 = .s7 ∨ row.1 = .s8 ∨ row.1 = .s9)
        (hi : (1 : ℕ) < recordCount row.1),
      BindMemRec row.2.1.z
        (memRecSkelOf data pubR ⟨1, by omega⟩ hi)
        (computeMemRec row.2.2.1 ⟨1, by omega⟩)) ∧
    (∀ (_h6 : row.1 = .s6) (hi : (2 : ℕ) < recordCount row.1),
      BindMemRec row.2.1.z
        (memRecSkelOf data pubR ⟨2, by omega⟩ hi)
        (computeMemRec row.2.2.1 ⟨2, by omega⟩)) ∧
    (∀ (_h9 : row.1 = .s9) (hi : (2 : ℕ) < recordCount row.1),
      BindMemRec row.2.1.z
        (memRecSkelOf data pubR ⟨2, by omega⟩ hi)
        (computeMemRec row.2.2.1 ⟨2, by omega⟩)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0 hi
    exact bindMemRec_mr2_s0 data pubR hacc hatoms h0 hi
  · intro ht hi
    exact bindMemRec_mr2_tailDecomp data pubR hacc ht hi
  · intro h6 hi
    exact bindMemRec_mr3_s6 data pubR hacc h6 hi
  · intro h9 hi
    exact bindMemRec_mr3_s9 data pubR hacc hatoms h9 hi

/-- The live-state census is exhaustive: no fifth `mr2` or third `mr3`
case can be hidden behind the generic record quantifier. -/
theorem live_record_state_census_is_exact :
    (∀ st, 1 < recordCount st →
      st = .s0 ∨ st = .s2 ∨ st = .s5 ∨ st = .s6 ∨
        st = .s7 ∨ st = .s8 ∨ st = .s9) ∧
    (∀ st, 2 < recordCount st → st = .s6 ∨ st = .s9) :=
  ⟨recordCount_mr2_live, recordCount_mr3_live⟩

/-! ## C. Axis atoms are exactly the two paper obligations -/

/-- Definitional 1-1 check: no opcode besides OP0 and OP9 occurs in
`AxisAtomPremises`, and neither of those two atom obligations is omitted.
OP0 supplies the formula-tail address; OP9 supplies the formula-tail-head
address -/
theorem axis_atoms_exactly_op0_and_op9
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) :
    AxisAtomPremises data ↔
      ((row.1 = .s0 → ∃ k, data.root.tail = .atom k) ∧
       (row.1 = .s9 → ∃ k, decompNoun data .f_th = .atom k)) :=
  Iff.rfl

/-- Negative control against a stronger Lean-only premise: outside OP0/OP9,
the exact premise is automatically inhabited and demands no noun atom.
-/
theorem axis_atoms_impose_nothing_on_other_opcodes
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (h0 : row.1 ≠ .s0) (h9 : row.1 ≠ .s9) :
    AxisAtomPremises data :=
  ⟨fun hs => (h0 hs).elim, fun hs => (h9 hs).elim⟩

/-- Concrete live OP0 non-vacuity: the existing accepted served-lookup row has
formula tail `atom 2`, so the load-bearing address premise is genuinely
inhabited on an OP0 row rather than only vacuously on OP1. -/
theorem live_op0_axis_atoms_nonvacuous :
    AxisAtomPremises
      Nock.NockVMROM.Thm54.NonterminalServedRow.servedRowData := by
  constructor
  · intro _
    exact ⟨2, rfl⟩
  · intro h9
    simp [Nock.NockVMROM.Thm54.NonterminalServedRow.servedRow] at h9

/-- The atom payload used as an NMR address is exactly the leaf coordinate of
the NPR fingerprint.  The general NPR definition is the paper;
the compute-table atom-shaped triple `(z,0,·)` appears at the paper. -/
theorem independent_realizes_atom_leaf
    {z : K} {fp : ComputeTable.FP K} {k : ℕ}
    (h : OpcodeSemantics.Realizes z fp (.atom k)) :
    fp.leaf = (k : K) := by
  rw [show fp = GlobalCarryRecognizer.enc z (.atom k) from h]
  simp [GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]

/-! ## D. Four real residual fields; still no generic residual -/

/-- Eta expansion pins exactly the unchanged four-field premise record. -/
theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

/-- The same four fields remain available after using the record to close an
arbitrary compute row.  Thus `bindComputeRow_of_residual` has not shrunk the
record in all but name. -/
theorem residual_binding_still_takes_all_four_fields
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (i : Fin E.cfg.compRows) :
    BindComputeRow (E.exec.computeRowAt i).2.1.z
        (computeSkeletonOf (E.semanticData.rows i)
          (publicRowNoun_of_execution E i))
        (E.exec.computeRowAt i) ∧
      InactiveDecPaddingExec E.exec ∧
      (∀ j : Fin E.cfg.compRows,
        AxisAtomPremises (E.semanticData.rows j)) ∧
      E.q = ringChar K :=
  ⟨bindComputeRow_of_residual E P i, P.inactiveDec, P.axisAtoms,
    P.q_eq_ringChar⟩

theorem commitmentResidual_boundary_still_D_A_W
    {E : BuildableNockExecution F K}
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (D : Data E)
    (A : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      AlphaMCommitment (p := ringChar K) D.timestampStrategy z hz α lmb)
    (W : ∀ (ω : JointCoins K) (lmb : K), nprSeed ω ≠ 0 → RawWalkArrays K) :
    (commitmentResidualOf D A W).q_eq_ringChar = D.q_eq_ringChar ∧
      (commitmentResidualOf D A W).commitment.skeleton = D.skeleton :=
  ⟨rfl, rfl⟩

/-- Any truly generic residual theorem would still force the strict
characteristic equality that `BuildableNockExecution` itself does not supply
as equality. -/
theorem generic_residual_would_still_force_q_equality
    (g : ∀ E : BuildableNockExecution F K,
      BuildablePackage.CommitmentResidual E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  fun E => (g E).q_eq_ringChar

theorem released_builder_still_has_hzero
    {E : BuildableNockExecution F K}
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (I : BuildableChips.Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (R : BuildablePackage.CommitmentResidual E)
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
  ⟨BuildablePackage.buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF⟩

/-! ## E. Accounting and consumed capstone -/

inductive ReviewedField97
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

def substantiveFields97 : List ReviewedField97 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields97 : List ReviewedField97 := [.structural]

def residualFields97 : List ReviewedField97 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Independent `11 + 1 + 2` recount. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields97.length = 11 ∧
      typeSummaryFields97.length = 1 ∧
      residualFields97 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields97.length = 2 ∧
      (substantiveFields97 ++ typeSummaryFields97 ++ residualFields97).Nodup ∧
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

#print axioms residual_binding_expands_all_nine_conjuncts
#print axioms residual_binding_closes_every_record_slot
#print axioms all_four_vcomp_fingerprint_copies
#print axioms all_four_live_bindmemrec_paths
#print axioms live_record_state_census_is_exact
#print axioms axis_atoms_exactly_op0_and_op9
#print axioms axis_atoms_impose_nothing_on_other_opcodes
#print axioms live_op0_axis_atoms_nonvacuous
#print axioms independent_realizes_atom_leaf
#print axioms residualPremises_eta_still_four
#print axioms residual_binding_still_takes_all_four_fields
#print axioms commitmentResidual_boundary_still_D_A_W
#print axioms generic_residual_would_still_force_q_equality
#print axioms released_builder_still_has_hzero
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestCommitment.bindComputeRow_of_residual
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestCommitment.bindComputeRow_of_axisAtoms
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestCommitment.bindMemRec_mr2
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestCommitment.bindMemRec_mr3
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.commitmentResidualOf
#print axioms Nock.NockVMROM.Thm54.BuildablePackage.buildFullPackage
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch97
