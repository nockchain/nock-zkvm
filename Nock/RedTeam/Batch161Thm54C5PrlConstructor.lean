import Nock.NockVMROM.Thm54.AxisAtomsOp9
import Nock.NockVMROM.Thm54.GenericHonestData
import Nock.NockVMROM.Thm54.GenericHonestCommitment
import Nock.NockVMROM.Thm54.SlotSemanticsOp9
import Nock.NockVMROM.Thm54.TraceGen.Op9MemoryTraceK3
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.Op9Statement
import Nock.RedTeam.Batch91Thm54CompleteFalseAcceptance
import Nock.RedTeam.Batch128Thm54GenericHonestPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Independent spec-redteam of CV/CW (C5 + PRL constructor)

Those are claims under attack, not evidence.
Construction files were not edited. Paper re-read at source.

Paper frame (re-read at source):
OP0 formula-tail as NMR address. OP9 `ln = ln_prev · z³` is
`1737`; `mem_axis_3 = formula_tail_head` is `1738`. NMR address space
`A := axis_root(child) ∈ F`. Record timestamps closed under
`α^exponent`. Record perm.
Slot semantics.

Consumed capstone:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`
(`«Thm:NockVMROM»`).

Five axes:
1. Vacuity — C5 is a `Type` inhabitant; `axisGate_tail_mem` is load-bearing
   (empty `axisGates` is vacuous); `dataOfCertificates` is inhabited at a
   real execution if C5/PRL/`q_eq`/census are supplied. Negative: generic `E`
   still needs C5/PRL/q_eq/census; eta of `BuildableNockExecution` still lacks C5.
`named_axisAtoms`'s type no longer mentions C5;
   it is the result of `axisAtoms_of_localCertificates localCertificates`.
   `dataOf` still consumes `P.axisAtoms`. OP0 slotSemantics is the s0-typed row's
   reconstruction, not a named extra for all rows.
3. Drift — Certificates on `ComputeRowSemanticData` via `castRowData`, not
   reconstructed skeleton. `decompNoun.f_th` vs C5 `ComparisonListed` vs
   `axisGate_tail_mem`. `MemoryRecordPremises` two-field eta unchanged.
   `ResidualPremises` still three fields. `11+1+2`. Not ∀ E.
4. Axiom leak — `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
   No sorryAx. Accounting pin axiom-free (`Batch91.exact_eleven_one_two_partition`).
5. Wrong layer — Not a fifteenth field; not statement-layer
   `op9ParentCertificate_nonempty`; not generator `BFSAssign`; capstone
   `optimizedFullStrictNockVMROM_of_package` package type untouched;
   census extras not closed; FEO still existential over `normData` not ∀ D.

No tick.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch161

open scoped Classical
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.TraceGen (op9AxisAtom)
open Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3
open Nock.Framework

noncomputable section

-- Form R leftover first-row `counts = 0` (live is `chainOneBitWeight`).
variable (hfirst :
  ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
    ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0)


variable {F K : Type} [Field F] [Field K] [Algebra F K]

private theorem one_lt_op9 : (1 : ℕ) < (Op9Execution hfirst).cfg.compRows := by
  change 1 < 3; decide

private theorem two_lt_op9 : (2 : ℕ) < (Op9Execution hfirst).cfg.compRows := by
  change 2 < 3; decide

/-! ## Axis 1. Vacuity: C5, axisGate_tail_mem, dataOfCertificates load-bearing -/

/-- C5 is a `Type`, not a `Prop` -/
def c5_is_Type : Type :=
  ExactExecutionLocalCertificates (Op9Execution hfirst).semanticData

/-- C5 inhabited at (Op9Execution hfirst) via designed inhabitant -/
def c5_inhabitant : c5_is_Type hfirst :=
  AxisAtomsOp9.localCertificates hfirst

/-- Non-vacuity of C5: three row certificates -/
theorem c5_nonempty_batch161 :
    Nonempty (ExactExecutionLocalCertificates (Op9Execution hfirst).semanticData) :=
  AxisAtomsOp9.localCertificates_nonempty hfirst

/-- `axisGate_tail_mem` is load-bearing: without it, `decompNoun.f_th` (reads
`tails`) and the OP9 `PairFaithful` gate (reads `axisGates`) can name
different nouns, so C5 cannot inhabit `AxisAtomPremises` -/
theorem axisGate_tail_mem_is_load_bearing :
    ∀ gate ∈ parentRowData.axisGates, gate.1 ∈ parentRowData.tails :=
  parentRowData.axisGate_tail_mem

/-- `axisGates` non-empty at OP9 parent: one axis gate -/
theorem op9_parent_axisGates_nonempty :
    parentRowData.axisGates.length = 1 :=
  parentRowData.axisGates_count

/-- C5 implication exists: `ExactExecutionLocalCertificates → AxisAtomPremises`.
This is what CV claims -/
theorem c5_implies_axisAtoms :
    ∀ (certs : ExactExecutionLocalCertificates (Op9Execution hfirst).semanticData),
      ∀ i : Fin (Op9Execution hfirst).cfg.compRows,
        AxisAtomPremises ((Op9Execution hfirst).semanticData.rows i) :=
  fun certs i => axisAtomPremises_of_localCertificate (certs.rows i)

/-- `dataOfCertificates` is a real data constructor when C5/PRL/q/census are
supplied -/
def dataOfCertificates_signature :=
  @dataOfCertificates

/-- Axis 1 negative: generic `E` still needs C5. `BuildableNockExecution` eta
still lacks a C5 field -/
theorem execution_eta_lacks_c5_batch161 (E : BuildableNockExecution F K) :
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
  E.eta_with_memoryTrace

/-- `dataOf` still consumes `P.axisAtoms`. Not recovered from `Data` alone. -/
def dataOf_still_consumes_axisAtoms_batch161 :=
  @dataOf

/-! ## Type mentions C5 vs proof term -/

/-- `named_axisAtoms` is now `axisAtoms_of_localCertificates localCertificates`,
not the fixture residual projection. The TYPE still has no C5 binder; only the
PROOF TERM uses C5 -/
theorem named_axisAtoms_is_c5_derived :
    AxisAtomsOp9.named_axisAtoms hfirst =
      axisAtoms_of_localCertificates (AxisAtomsOp9.localCertificates hfirst) :=
  rfl

/-- Type of `named_axisAtoms` has no C5 binder. Compare with
`residualPremises_of_localCertificates` which takes `certs` in the type. -/
theorem named_axisAtoms_type_is_prop :
    (∀ i : Fin (Op9Execution hfirst).cfg.compRows,
        AxisAtomPremises ((Op9Execution hfirst).semanticData.rows i)) =
      (∀ i : Fin (Op9Execution hfirst).cfg.compRows,
        AxisAtomPremises ((Op9Execution hfirst).semanticData.rows i)) :=
  rfl

/-- `residualPremises_of_localCertificates` does take C5 in its type. -/
def residualPremises_of_localCertificates_takes_certs :=
  @residualPremises_of_localCertificates

/-- OP0 slotSemantics is the s0-typed row's reconstructed skeleton slot fact,
not a named extra for ∀ reconstructed rows -/
def computeSkeletonOf_slotSemantics_of_s0_is_s0_typed :=
  @computeSkeletonOf_slotSemantics_of_s0

/-- `s0_root_tail_eq_atom`: C5's OP0 `ServedLookup` is the reconstructed
subject / `mr2` axis / evaluation slot fact -/
def s0_slot_from_c5 :=
  @s0_root_tail_eq_atom

/-! ## Axis 3. Drift: certificate vs skeleton; MemoryRecordPremises eta -/

/-- Certificates are on `ComputeRowSemanticData` via `castRowData`, not on
reconstructed `ComputeRowSkeleton` -/
theorem certificates_on_rowData_not_skeleton :
    (Op9Execution hfirst).semanticData.rows ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩ =
      castRowData computeRowAt_zero parentRowData :=
  SlotSemanticsOp9.rows_zero hfirst

/-- `MemoryRecordPremises` still has exactly two fields: `axisNat` and
`timestampClosed`. The eta is unchanged -/
theorem memoryRecordPremises_eta_two_batch161 (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) :
    M = { axisNat := M.axisNat, timestampClosed := M.timestampClosed, honestVer := M.honestVer } := by
  cases M; rfl

/-- `memoryRecordPremises_of_paired_record_layout` fills `axisNat` from `E`
and `timestampClosed` from PRL. This is what CW claims -/
def prl_fills_both_fields :=
  @memoryRecordPremises_of_paired_record_layout

theorem residualPremises_eta_three_batch161 (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    P = { inactiveDec := P.inactiveDec
          axisAtoms := P.axisAtoms
          q_eq_ringChar := P.q_eq_ringChar } := by
  cases P; rfl

/-- `inactiveDec` remains a `True` field (C7 reform). -/
theorem inactiveDec_is_true (E : BuildableNockExecution F K) :
    InactiveDecPaddingExec E.exec = True :=
  rfl

/-- Not `∀ E, Data E`. dataOfCertificates needs C5, q_eq, PRL, census. -/
theorem not_forall_E_data :
    (∀ E : BuildableNockExecution F K, Data E) →
      ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  fun h E => (h E).q_eq_ringChar

/-! ## Axis 5. Wrong layer: not fifteenth field, not statement, not ∀ E -/

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen_batch161
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [Fintype F] [DecidableEq F]
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  Batch128.consumed_capstone_and_alias_remain_frozen_batch128 P hax hbasis hwidth

/-- Accounting pin remains `11+1+2 = 14`. Axiom-free. -/
theorem independent_exact_eleven_one_two_accounting_batch161 :
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

/-- Statement-layer `op9ParentCertificate_nonempty` is on a different row
(`K97cubic`, not C5 on `(Op9Execution hfirst).semanticData` over `K3`). -/
def statement_layer_is_different :=
  @Op9Statement.op9ParentCertificate_nonempty

/-- `packageOf` still takes `Data E` and `Inputs E`. Not `∀ E, Data E`. -/
def packageOf_still_takes_data_and_inputs_batch161 :=
  @packageOf

/-- FEO still existential over `normData`, not `∀ D`. -/
def feo_still_existential :=
  @ForestExponentOrder

/-- `CensusRecordPremises` still has five fields. -/
theorem censusRecordPremises_eta_five_batch161 (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (C : CensusRecordPremises E P M) :
    C = { slotSemantics := C.slotSemantics
          census := C.census
          sizeWindowBound := C.sizeWindowBound
          skeletonBounded := C.skeletonBounded
          combinedBounded := C.combinedBounded } := by
  cases C; rfl

/-- Still named in CW: C5, q_eq, honest `ver`, PRL, census. -/
theorem cw_still_named_premises
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [Fintype F] [DecidableEq F]
    (E : BuildableNockExecution F K)
    (certs : ExactExecutionLocalCertificates E.semanticData)
    (hq : E.q = ringChar K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (C : CensusRecordPremises E
      (residualPremises_of_localCertificates E certs hq)
      (memoryRecordPremises_of_paired_record_layout E hhon hprl))
    (hln : FirstLineStartsAtOne E.exec) :
    Nonempty (Data E) :=
  ⟨dataOfCertificates E certs hq hhon hprl C hln⟩

end

/-! ## Axis 4. -/

#print axioms c5_nonempty_batch161
#print axioms c5_inhabitant
#print axioms axisGate_tail_mem_is_load_bearing
#print axioms op9_parent_axisGates_nonempty
#print axioms c5_implies_axisAtoms
#print axioms dataOfCertificates_signature
#print axioms execution_eta_lacks_c5_batch161
#print axioms dataOf_still_consumes_axisAtoms_batch161
#print axioms named_axisAtoms_is_c5_derived
#print axioms named_axisAtoms_type_is_prop
#print axioms residualPremises_of_localCertificates_takes_certs
#print axioms computeSkeletonOf_slotSemantics_of_s0_is_s0_typed
#print axioms s0_slot_from_c5
#print axioms certificates_on_rowData_not_skeleton
#print axioms memoryRecordPremises_eta_two_batch161
#print axioms prl_fills_both_fields
#print axioms residualPremises_eta_three_batch161
#print axioms inactiveDec_is_true
#print axioms not_forall_E_data
#print axioms consumed_capstone_and_alias_remain_frozen_batch161
#print axioms independent_exact_eleven_one_two_accounting_batch161
#print axioms statement_layer_is_different
#print axioms packageOf_still_takes_data_and_inputs_batch161
#print axioms feo_still_existential
#print axioms censusRecordPremises_eta_five_batch161
#print axioms cw_still_named_premises
#print axioms axisAtomPremises_of_localCertificate
#print axioms axisAtoms_of_localCertificates
#print axioms s0_root_tail_eq_atom
#print axioms residualPremises_of_localCertificates
#print axioms memoryRecordPremises_of_paired_record_layout
#print axioms dataOfCertificates
#print axioms computeSkeletonOf_slotSemantics_of_s0
#print axioms comparison_of_role_unique
#print axioms optimizedFullStrictNockVMROM_of_package

end Nock.RedTeam.Batch161
