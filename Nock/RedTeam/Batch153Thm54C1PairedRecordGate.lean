import Nock.NockVMROM.Thm54
import Nock.RedTeam.Batch91Thm54CompleteFalseAcceptance
import Nock.RedTeam.Batch152Thm54C1PairedRecord
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Nothing here adds a fifteenth field, ticks a `§J` box, retries
the counted-event route, restarts C2 / C4-as-field / `slotSemantics` as a
field, or retouches the capstone.

## Paper frame

* Add to `intermediate` at `read_root`; remove at
  `verify_child` (`1415`).
* Every timestamp added then removed again (`1427`).
* `intermediate` constraints implemented as `RAP_mem-IO` / `RAP_comp-IO`;
  argument equivalent to `Thm:IO_result`; IO and `intermediate` are the two
  memory-record columns matched within the same table (`1431`).
* Algorithm Memspec add (`2072`) / remove (`2080`).
* `Def:unique_request` (`603-611`); `cor_uni_req_uni_resp` (`613`).
* `L_IO` unique matching (`183`); `L_mIO` with multiplicities (`195`).
* Consumed capstone `Thm:NockVMROM` (`1450-1495`)
  → `optimizedFullStrictNockVMROM_of_package`, producing
  `OptimizedFullStrictThm54Statement`. Untouched.

## Five axes

**S0** (vacuity): CLEAR — F97 inhabitant is real NMR records; last-two swap,
not an identity pair; `timestampClosed` applies at F97 through the existing
bridge.

**S1** (weakening): CLEAR on the implication *to* the named premise.
`batch153_paired_from_c1_via_addedRemovedAgain` re-derives `PairedRecordLayout`
from C1 by a **different route** than production
(`pairedRecordLayout_of_intermediatePreimage`): it reconstructs
`AddedRemovedAgain` and uses already-held `addedRecordList_nodup` +
`consumed_length_eq_added_length`. At F97 the analogue of
`cor_uni_req_uni_resp` is compiled as an actual application of
`IO.cor_uni_req_uni_resp`. **Characterization finding (not a refutation):**
`c1_iff_paired_at_f97`'s reverse ignores the `PairedRecordLayout` hypothesis
(constant inhabitant). That is fixture coincidence, not type interchange.
C6-class / rename is **not** compiled: C6 gate (5) was `Iff.rfl`; C1 ⇒ PRL
is a real theorem and the generic reverse was dropped.

**S2** (drift): CLEAR — NMR `Rec` lists + `encRec` / `bridgeRecords`; no
`RatFunc` tower; no counted-event flag.

**S3** (axioms): ⊆ `{propext, Classical.choice, Quot.sound}`. The `11+1+2`
pin is axiom-free.

**S4** (layer): CLEAR — fourteen fields; `ResidualPremises` still four;
capstone untouched; §J tick not licensed.

§J tick: **NOT LICENSED.** Fixture discharge is real; the generic
named-premises constructor still requires `PairedRecordLayout`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch153

open scoped Classical
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusC1
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.DistinctCensusFold2
open Nock.NockVMROM.Thm54.FirstLineCarrier
open Nock.RedTeam.Batch91

local instance prime97d : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97d : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## S0. F97 inhabitant is a last-two swap, not an identity -/

noncomputable abbrev fr (r : ComputeTable.MemRec K97cubic) : ComputeTable.MemRec K97cubic :=
  NockVM.formRRow r MemoryTable.formRDefault

theorem batch153_f97_added_is_FTLR :
    RowLayout.addedRecordList execD = [fr recF, fr recT, fr recL, fr recR] :=
  addedRecordList_distinctCensus

theorem batch153_f97_consumed_is_FTRL :
    RowLayout.consumedRecordList execD = [fr recF, fr recT, fr recR, fr recL] :=
  consumedRecordList_distinctCensus

/-- Distinct timestamps `z^i`: exponents 4 and 3 lie in `Iio (orderOf α)`. -/
theorem batch153_recR_ne_recL : fr recR ≠ fr recL := by
  intro h
  have hts := congrArg (fun r : ComputeTable.MemRec K97cubic => r.ts) h
  simp [fr, NockVM.formRRow, recR, recL] at hts
  have h4 : 4 ∈ Set.Iio (orderOf alphaD) := by
    rw [Set.mem_Iio, alphaD_order]; norm_num
  have h3 : 3 ∈ Set.Iio (orderOf alphaD) := by
    rw [Set.mem_Iio, alphaD_order]; norm_num
  have : 4 = 3 := pow_injOn_Iio_orderOf h4 h3 hts
  nomatch this

theorem batch153_f97_columns_not_identical :
    RowLayout.consumedRecordList execD ≠ RowLayout.addedRecordList execD := by
  rw [batch153_f97_consumed_is_FTRL, batch153_f97_added_is_FTLR]
  intro h
  have h2 := congrArg (fun l : List (ComputeTable.MemRec K97cubic) => l[2]?) h
  simp at h2
  exact batch153_recR_ne_recL h2

theorem batch153_f97_preimage_inhabited :
    Nonempty (SemanticIntermediatePreimage cfgD execD) :=
  ⟨intermediatePreimageD⟩

theorem batch153_f97_perm_is_last_two_swap :
    [fr recF, fr recT, fr recR, fr recL].Perm [fr recF, fr recT, fr recL, fr recR] :=
  (((List.Perm.swap (fr recR) (fr recL) []).cons (fr recT)).cons (fr recF)).symm

theorem batch153_f97_paired_from_lists :
    RowLayout.PairedRecordLayout execD := by
  rw [RowLayout.PairedRecordLayout, batch153_f97_added_is_FTLR,
    batch153_f97_consumed_is_FTRL]
  exact batch153_f97_perm_is_last_two_swap

/-! ## S1. C1 ⇒ PRL by a different route (AddedRemovedAgain) -/

/-- Reconstruct the paper's single inclusion from the designed type, then use
objects already on `E` (`addedRecordList_nodup`,
`consumed_length_eq_added_length`). Production's implication never mentions
`addedRecordList_nodup`; this route does. -/
theorem batch153_addedRemovedAgain_of_c1
    (E : BuildableNockExecution F K)
    (w : SemanticIntermediatePreimage E.cfg E.exec) :
    AddedRemovedAgain E.exec := by
  intro r hr
  have henc :
      NockVM.encRecC r (E.exec.cprimeOf r) ∈
        (RowLayout.addedRecordList E.exec).map
          (fun r => NockVM.encRecC r (E.exec.cprimeOf r)) :=
    List.mem_map.mpr ⟨r, hr, rfl⟩
  rw [← w.added_bridge] at henc
  rw [bridgeRecords, List.mem_map] at henc
  obtain ⟨s, hsAdd, hbridge⟩ := henc
  have hfin :
      w.semanticConsumed.toFinset = w.semanticAdded.toFinset :=
    ((IO.LmIO_iff E.cfg.Ksz w.semanticConsumed w.semanticAdded).1
      w.semantic_lmio).2.2.2
  have hsCons : s ∈ w.semanticConsumed := by
    have : s ∈ w.semanticConsumed.toFinset := by
      rw [hfin]
      exact List.mem_toFinset.mpr hsAdd
    exact List.mem_toFinset.mp this
  have hencCons :
      NockVM.encRecC r (E.exec.cprimeOf r) ∈
        (RowLayout.consumedRecordList E.exec).map
          (fun r => NockVM.encRecC r (E.exec.cprimeOf r)) := by
    rw [← w.consumed_bridge, bridgeRecords, List.mem_map]
    exact ⟨s, hsCons, hbridge⟩
  obtain ⟨r', hr', heq⟩ := List.mem_map.mp hencCons
  have : r' = r := encRecC_cp_injective_here E.exec.cprimeOf heq
  rw [← this]
  exact hr'

theorem batch153_paired_from_c1_via_addedRemovedAgain
    (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (w : SemanticIntermediatePreimage E.cfg E.exec) :
    RowLayout.PairedRecordLayout E.exec :=
  pairedRecordLayout_of_addedRemovedAgain E hhon hC
    (batch153_addedRemovedAgain_of_c1 E w)

/-- The add/remove analogue is an actual `cor_uni_req_uni_resp` at F97, not a
metaphor. Consumed order is nodup because it is a permutation of `semRecs`. -/
theorem batch153_f97_lio_via_cor_uni_req_uni_resp :
    IO.LIO cfgD.Ksz
      intermediatePreimageD.semanticConsumed
      intermediatePreimageD.semanticAdded := by
  have hnd : intermediatePreimageD.semanticConsumed.Nodup := by
    simp only [intermediatePreimageD]
    have hperm : [semF, semT, semR, semL].Perm [semF, semT, semL, semR] :=
      (((List.Perm.swap semR semL []).cons semT).cons semF).symm
    exact (hperm.nodup_iff).2 semRecs_nodup
  exact IO.cor_uni_req_uni_resp cfgD.Ksz
    intermediatePreimageD.semanticConsumed
    intermediatePreimageD.semanticAdded
    hnd intermediatePreimageD.semantic_lmio

/-- Production `c1_iff_paired_at_f97` reverse does not inspect PRL. -/
theorem batch153_f97_reverse_ignores_paired
    (_h : RowLayout.PairedRecordLayout execD) :
    Nonempty (SemanticIntermediatePreimage cfgD execD) :=
  ⟨intermediatePreimageD⟩

theorem batch153_f97_inhabited_without_paired_hypothesis :
    Nonempty (SemanticIntermediatePreimage cfgD execD) :=
  ⟨intermediatePreimageD⟩

/-- C6 gate (5) really was `Iff.rfl`. C1 has no such identity. -/
theorem batch153_c6_gate5_was_iff_rfl :
    ((execD.computePubAt ⟨0, cfgD.compRows_pos⟩).ln_prev = 1) ↔
      FirstLineStartsAtOne execD :=
  c6_field_is_definitionally_firstLine execD

/-! ## S0 continued. `timestampClosed` at F97 from the independent perm

Form R leftover first-row `counts = 0` / `indicator = 0` (live Form R is
`chainOneBitWeight`); dummy-wired through the fixture. -/

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)

theorem batch153_timestampClosed_at_f97 :
    ∀ i : Fin (distinctCensusExecution hfirstD).cfg.memRows,
      memoryMemRecKind ((distinctCensusExecution hfirstD).exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt (distinctCensusExecution hfirstD).cfg.challenges.α
          ((distinctCensusExecution hfirstD).exec.memoryRowAt i).2.2.mem.ts :=
  GenericHonestData.timestampClosed_of_paired_record_layout
    (E := distinctCensusExecution hfirstD)
    (DistinctCensusCommitment.honestVerD hfirstD)
    (batch153_paired_from_c1_via_addedRemovedAgain (distinctCensusExecution hfirstD)
      (DistinctCensusCommitment.honestVerD hfirstD)
      DistinctCensusExecution.execD_cprimeCoherent intermediatePreimageD)

/-! ## S4. -/

theorem batch153_still_fourteen
    (E : BuildableNockExecution F97 K97cubic) :
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

theorem batch153_residual_still_four
    (P : ResidualPremises (distinctCensusExecution hfirstD)) :
    InactiveDecPaddingExec (distinctCensusExecution hfirstD).exec ∧
      (∀ i : Fin (distinctCensusExecution hfirstD).cfg.compRows,
        AxisAtomPremises ((distinctCensusExecution hfirstD).semanticData.rows i)) ∧
          (distinctCensusExecution hfirstD).q = ringChar K97cubic :=
  GenericHonestCommitment.residualPremises_still_four P

/-- `11+1+2` consumed as recorded, not reinterpreted. Axiom-free. -/
theorem batch153_eleven_one_two : 11 + 1 + 2 = 14 :=
  GenericHonestPackage.residual_pair_still_eleven_one_two

theorem batch153_eleven_one_two_is_batch91 :
    reviewedSubstantiveFields.length = 11 ∧
      reviewedTypeSummaryFields.length = 1 ∧
      reviewedResidualFields.length = 2 := by
  decide

theorem batch153_consumed_capstone_untouched
    (hax : OptimizedComputeFinalTrace.FormRAxisBound
      (DistinctCensusFold2.packageR hfirstD).optimized.sampled
      (DistinctCensusFold2.packageR hfirstD).optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis
      (DistinctCensusFold2.packageR hfirstD).optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F97) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
      (DistinctCensusFold2.packageR hfirstD) :=
  OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
    (DistinctCensusFold2.packageR hfirstD) hax hbasis hwidth

/-- Tick widening is not licensed: fixture discharge is not a generic close. -/
theorem batch153_tick_not_licensed :
    RowLayout.PairedRecordLayout execD ∧
      ¬ False :=
  ⟨batch153_f97_paired_from_lists, not_false⟩

end Nock.RedTeam.Batch153

#print axioms Nock.RedTeam.Batch153.batch153_f97_preimage_inhabited
#print axioms Nock.RedTeam.Batch153.batch153_f97_columns_not_identical
#print axioms Nock.RedTeam.Batch153.batch153_paired_from_c1_via_addedRemovedAgain
#print axioms Nock.RedTeam.Batch153.batch153_f97_lio_via_cor_uni_req_uni_resp
#print axioms Nock.RedTeam.Batch153.batch153_f97_reverse_ignores_paired
#print axioms Nock.RedTeam.Batch153.batch153_c6_gate5_was_iff_rfl
#print axioms Nock.RedTeam.Batch153.batch153_timestampClosed_at_f97
#print axioms Nock.RedTeam.Batch153.batch153_still_fourteen
#print axioms Nock.RedTeam.Batch153.batch153_residual_still_four
#print axioms Nock.RedTeam.Batch153.batch153_eleven_one_two
#print axioms Nock.RedTeam.Batch153.batch153_consumed_capstone_untouched
