import Nock.NockVMROM.Thm54.GeneratedRowHandshake
import Nock.NockVMROM.Thm54.GenericHonestData
import Nock.NockVMROM.Thm54.GenericHonestCommitment
import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.RedTeam.Batch91Thm54CompleteFalseAcceptance
import Nock.RedTeam.Batch128Thm54GenericHonestPackage
import Nock.RedTeam.Batch161Thm54C5PrlConstructor
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper re-read at source. Construction files were
not edited in this batch.

Independence disclosure: the same conversation produced CY. This batch is a
compiled scope-attack with negative controls, not an RTS-1.1 distinct-context
flip. `redteam-status.json` top-level `status` is not set to `passed`.

Consumed capstone:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`
(`«Thm:NockVMROM»`).

Five axes:
1. Elaboration, not reachability — `coveredRow` is `buildCoveredRow.1`; the
   root/decomp/call identification theorems and the C5 wrappers **elaborate at
   their stated signatures**; `dataOfCertificates_of_generated` yields `Data`
   **given** C5 / `q_eq` / PRL / census as arguments.
   This axis was
   headed "Vacuity" and read as showing the premises are reachable. It does not.
   15 of the 27 declarations in this file are `def X_exists := @Y` aliases or
   `True := trivial` (lines 90-108, 152, 157, 162, 194, 226, 269, 272, 277), so
   what is discharged is *"these names elaborate"*, not *"these premises are
   inhabited"*. **Nothing here exhibits an inhabitant of
   `SkeletonOperationalPremises`, `BindComputeRow`, or `Vcomp + hcalls`**, and
   the two `theorem`s on this axis take their premises as hypotheses. Read the
   axis as a signature/elaboration check only.
2. Weakening — `computeSkeletonOf_covered_root` is a 4-conjunct `And`, not
   `computeSkeletonOf = s`. Subformula identification carries a leaf-window
   hyp. C5 wrappers still bind `Vcomp` and child `evalFBy`. The generated
   consumer is definitionally `dataOfCertificates`.
3. Drift — reconstruction `memoryRecord` is `memRecSkelOf`, not
   `s.memoryRecord`. Certificates live on `ComputeRowSemanticData`. CY's
   `1415-1431` range includes `1429` (mutated-subject forest) and `1431`
   (intermediate accumulator); PRL is `1413,1415,1427`. `11+1+2`. Not `∀ E`.
4. Axiom leak — `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
   No `sorryAx`. Accounting pin axiom-free.
5. Wrong layer — C5 not a field of `E`; capstone type untouched; `packageOf`
   still takes `Data`/`Inputs`; FEO still existential; generator files not
   this module; no §J tick.

Disposition is compiled below. CY not rewritten. No tick.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch162

open scoped Classical
open Nock
open ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.BoundSemanticTrace
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.GeneratedRowHandshake
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## Axis 1. The handshake theorems elaborate at their stated signatures

Not "the premises are reachable": the `_exists` declarations below are `@`-aliases, which check
that a name elaborates at its signature and nothing more, and the two `theorem`s take their
premises as hypotheses. -/

/-- Covered row data is the generator's `buildCoveredRow.1` -/
theorem coveredRow_is_buildCoveredRow
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ) :
    coveredRow hb hop hbind hfaith hleaves =
      (buildCoveredRow hb hop hbind hfaith hleaves).1 :=
  rfl

def covered_root_subject_exists :=
  @covered_root_subject

def computeSkeletonOf_covered_root_exists :=
  @computeSkeletonOf_covered_root

def computeSkeletonOf_covered_decomp_exists :=
  @computeSkeletonOf_covered_decomp

def covered_callSlotNoun_exists :=
  @covered_callSlotNoun

def subformulaNounOf_covered_exists :=
  @subformulaNounOf_covered

def localCertificate_of_coveredRow_exists :=
  @localCertificate_of_coveredRow

def localCertificates_of_ofSkeleton_exists :=
  @localCertificates_of_ofSkeleton

/-- Generated consumer inhabits `Data` at the same named premises
`dataOfCertificates` already takes -/
theorem generated_consumer_inhabits_data
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
  ⟨dataOfCertificates_of_generated E certs hq hhon hprl C hln⟩

/-! ## Axis 2. Weakening: not skeleton `ext`; window and evalFBy remain -/

/-- `ComputeRowSkeleton` has seven fields. CY's root theorem names four. -/
theorem computeRowSkeleton_eta_seven (s : ComputeRowSkeleton) :
    s = { state := s.state
          subject := s.subject
          formula := s.formula
          evaluation := s.evaluation
          decomposition := s.decomposition
          subformula := s.subformula
          memoryRecord := s.memoryRecord } := by
  cases s; rfl

/-- Reconstruction subformula is `subformulaNounOf`, not a literal copy of
`s.subformula`. The handshake identification of that slot is the separate
windowed theorem -/
theorem computeSkeletonOf_subformula_is_subformulaNounOf
    {q Λ : ℕ} {row : State × DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row)) :
    (computeSkeletonOf data pubR).subformula =
      fun i hi slot => subformulaNounOf data pubR i hi slot :=
  rfl

/-- Subformula identification carries a leaf-window hypothesis.
CY's parenthetical "leaf window" is the actual binder, not the full
`Def[Nock Program]` terminal-state package at `1090-1094` -/
def subformula_id_takes_leaf_window :=
  @computeSkeletonOf_covered_subformula

/-- Covered-row C5 still binds `Vcomp` and child `evalFBy`. Not a field of
`E`, and not discharged by `buildCoveredRow` alone -/
def covered_c5_takes_vcomp_and_evalFBy :=
  @localCertificate_of_coveredRow

/-- Whole-execution C5 still requires `ofSkeleton` row agreement and child
`evalFBy` -/
def ofSkeleton_c5_takes_hrows_and_hcalls :=
  @localCertificates_of_ofSkeleton

/-- Generated `Data` constructor is an alias, not a new bridge. -/
theorem dataOfCertificates_of_generated_is_alias
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
    dataOfCertificates_of_generated E certs hq hhon hprl C hln =
      dataOfCertificates E certs hq hhon hprl C hln :=
  dataOfCertificates_of_generated_eq E certs hq hhon hprl C hln

/-! ## Axis 3. Drift: memory reconstruction; cite range; not ∀ E -/

/-- Reconstruction memory records are the paper-canonical `memRecSkelOf`,
not the generated `s.memoryRecord`. CY does not identify this slot. -/
theorem computeSkeletonOf_memoryRecord_is_memRecSkelOf
    {q Λ : ℕ} {row : State × DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row)) :
    (computeSkeletonOf data pubR).memoryRecord =
      fun i hi => memRecSkelOf data pubR i hi :=
  rfl

/-- `memRecSkelOf` at `mr1` is always formula/tail/axis 3, independent of
whatever the generated skeleton stored -/
def memRecSkelOf_mr1_is_paper_canonical :=
  @memRecSkelOf_mr1

/-- Residual premises still three fields. Handshake added none. -/
theorem residualPremises_eta_three_batch162 (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    P = { inactiveDec := P.inactiveDec
          axisAtoms := P.axisAtoms
          q_eq_ringChar := P.q_eq_ringChar } := by
  cases P; rfl

/-- Census extras still five fields. Handshake added none. -/
theorem censusRecordPremises_eta_five_batch162 (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (C : CensusRecordPremises E P M) :
    C = { slotSemantics := C.slotSemantics
          census := C.census
          sizeWindowBound := C.sizeWindowBound
          skeletonBounded := C.skeletonBounded
          combinedBounded := C.combinedBounded } := by
  cases C; rfl

/-- Not `∀ E, Data E`. -/
theorem not_forall_E_data_batch162 :
    (∀ E : BuildableNockExecution F K, Data E) →
      ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  Batch161.not_forall_E_data

/-- CY item-line `1415-1431` is a range. `1429` is mutated-subject forest
seeding; `1431` is the intermediate accumulator. PRL / IO matching for the
consumer is `1413,1415,1427`. Recorded as S2 cite drift; no Lean object
changed -/
def prl_paper_locations_are_1413_1415_1427 : True := trivial

/-! ## Axis 5. Wrong layer: not a field, not capstone, not ∀ E -/

theorem execution_eta_lacks_c5_batch162 (E : BuildableNockExecution F K) :
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
  Batch161.execution_eta_lacks_c5_batch161 E

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen_batch162
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

theorem independent_exact_eleven_one_two_accounting_batch162 :
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

def packageOf_still_takes_data_and_inputs_batch162 :=
  @packageOf

def feo_still_existential_batch162 :=
  @ForestExponentOrder

/-- Handshake C5 is `Nonempty (LocalOpcodeCertificate …)`, not a new
`BuildableNockExecution` field -/
def covered_c5_is_nonempty_certificate :=
  @localCertificate_of_coveredRow

end

/-! ## Axis 4. -/

#print axioms coveredRow_is_buildCoveredRow
#print axioms covered_root_subject_exists
#print axioms computeSkeletonOf_covered_root_exists
#print axioms computeSkeletonOf_covered_decomp_exists
#print axioms covered_callSlotNoun_exists
#print axioms subformulaNounOf_covered_exists
#print axioms localCertificate_of_coveredRow_exists
#print axioms localCertificates_of_ofSkeleton_exists
#print axioms generated_consumer_inhabits_data
#print axioms computeRowSkeleton_eta_seven
#print axioms computeSkeletonOf_subformula_is_subformulaNounOf
#print axioms subformula_id_takes_leaf_window
#print axioms covered_c5_takes_vcomp_and_evalFBy
#print axioms ofSkeleton_c5_takes_hrows_and_hcalls
#print axioms dataOfCertificates_of_generated_is_alias
#print axioms computeSkeletonOf_memoryRecord_is_memRecSkelOf
#print axioms memRecSkelOf_mr1_is_paper_canonical
#print axioms residualPremises_eta_three_batch162
#print axioms censusRecordPremises_eta_five_batch162
#print axioms not_forall_E_data_batch162
#print axioms prl_paper_locations_are_1413_1415_1427
#print axioms execution_eta_lacks_c5_batch162
#print axioms consumed_capstone_and_alias_remain_frozen_batch162
#print axioms independent_exact_eleven_one_two_accounting_batch162
#print axioms packageOf_still_takes_data_and_inputs_batch162
#print axioms feo_still_existential_batch162
#print axioms covered_c5_is_nonempty_certificate
#print axioms dataOfCertificates_of_generated
#print axioms computeSkeletonOf_covered_root
#print axioms computeSkeletonOf_covered_subformula
#print axioms localCertificates_of_ofSkeleton
#print axioms optimizedFullStrictNockVMROM_of_package

end Nock.RedTeam.Batch162
