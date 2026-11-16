import Nock.NockVMROM.Thm54.PairedRecordIOResult
import Nock.NockVMROM.Thm54.DistinctCensusExecution

/-!
# `C1` measured at F97 — type inhabited, field NOT added

This module **defines that type, inhabits it at the
F97 fixture where the two intermediate columns are a nontrivial permutation, and then
refuses the field**. Gate (5): on every `BuildableNockExecution` the type *implies*
`RowLayout.PairedRecordLayout` from objects already on `E` (the add/remove analogue of
`IO.cor_uni_req_uni_resp`). That is C6-class: adding the field would rename the named
premise. J.0.3 therefore does not apply — no carrier was extended — and the §J box
stays unticked. `timestampClosed` remains contingent. `ResidualPremises` stays four. Capstone untouched. Counted-event route not retried.

The analogue of `cor_uni_req_uni_resp` for an add/remove pair inside one table is
identified here: `IO.LmIO` on the semantic lists, plus already-held
`addedRecordList_nodup` and `consumed_length_eq_added_length`, upgrades to `List.Perm`
of the encoded columns, hence to `PairedRecordLayout` via `encRec` injectivity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54

open scoped Classical
open Nock Nock.NockVM
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete

noncomputable section


variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## §A. The designed `C1` type

Not added as a field.  Paper: add at `read_root`, remove at `verify_child` (`1415` / `2080`), matched as the two record columns
of one table (`1431`), unique request (`Def:unique_request` `603-607`,
`cor_uni_req_uni_resp` `613`). -/


/-- Record-level semantic preimage of the `intermediate` add/remove columns.  Exact analogue
of `SemanticIOPreimage` for the two record lists that Algorithm Memspec writes into and
erases from the `intermediate` accumulator. -/
structure SemanticIntermediatePreimage
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) where
  /-- Semantic preimage of the `read_root` add column. -/
  semanticAdded : List ((nmrMEF F K).Rec)
  /-- Semantic preimage of the `verify_child` remove column. -/
  semanticConsumed : List ((nmrMEF F K).Rec)
  /-- Multiplicity-sensitive matching at the NMR-record layer. -/
  semantic_lmio : IO.LmIO cfg.Ksz semanticConsumed semanticAdded
  /-- The add-column preimage encodes to the actual `read_root` records. -/
  added_bridge :
    bridgeRecords F K cfg.challenges.α cfg.challenges.lam semanticAdded
      = (RowLayout.addedRecordList exec).map (fun r => NockVM.encRecC r (exec.cprimeOf r))
  /-- The remove-column preimage encodes to the actual `verify_child` records. -/
  consumed_bridge :
    bridgeRecords F K cfg.challenges.α cfg.challenges.lam semanticConsumed
      = (RowLayout.consumedRecordList exec).map (fun r => NockVM.encRecC r (exec.cprimeOf r))

namespace SemanticIntermediatePreimage

/-- Encoding preserves list length, so the semantic lists have the same lengths as the
table columns. -/
theorem length_eq_columns
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticIntermediatePreimage cfg exec) :
    w.semanticAdded.length = (RowLayout.addedRecordList exec).length ∧
      w.semanticConsumed.length = (RowLayout.consumedRecordList exec).length := by
  constructor
  · simpa [bridgeRecords] using congrArg List.length w.added_bridge
  · simpa [bridgeRecords] using congrArg List.length w.consumed_bridge

end SemanticIntermediatePreimage

/-! ## §B. Local `encRec` un-encoding (no `Fintype` tax)

Copied from `PairedRecordIOResult.encRec_injective` so the C6 implication does not
inherit that module's `[Fintype K]` section telescope. -/


/-- Row-level `C'` (28th): `r ↦ encRecC r (cp r)` is injective for any per-record `C'`. -/
theorem encRecC_cp_injective_here (cp : ComputeTable.MemRec K → K) :
    Function.Injective (fun r => NockVM.encRecC r (cp r)) := by
  intro r s h
  have hs : ∀ i : Fin 9, NockVM.encRecC r (cp r) i = NockVM.encRecC s (cp s) i :=
    fun i => congrFun h i
  refine ComputeTable.MemRec.ext (ComputeTable.FP.ext ?_ ?_ ?_)
    (ComputeTable.FP.ext ?_ ?_ ?_) ?_ ?_
  · simpa [NockVM.encRecC] using hs 0
  · simpa [NockVM.encRecC] using hs 1
  · simpa [NockVM.encRecC] using hs 2
  · simpa [NockVM.encRecC] using hs 3
  · simpa [NockVM.encRecC] using hs 4
  · simpa [NockVM.encRecC] using hs 5
  · simpa [NockVM.encRecC] using hs 6
  · simpa [NockVM.encRecC] using hs 7


theorem perm_of_perm_map_encRecC_cp_here (cp : ComputeTable.MemRec K → K)
    {l l' : List (ComputeTable.MemRec K)}
    (h : (l.map (fun r => NockVM.encRecC r (cp r))).Perm
      (l'.map (fun r => NockVM.encRecC r (cp r)))) : l.Perm l' := by
  have hms :
      ((l : Multiset (ComputeTable.MemRec K)).map (fun r => NockVM.encRecC r (cp r)))
        = ((l' : Multiset (ComputeTable.MemRec K)).map (fun r => NockVM.encRecC r (cp r))) := by
    rw [Multiset.map_coe, Multiset.map_coe]
    exact Multiset.coe_eq_coe.mpr h
  exact Multiset.coe_eq_coe.mp (Multiset.map_injective (encRecC_cp_injective_here cp) hms)

/-! ## §C. `C1` ⇒ `PairedRecordLayout` on every `E`

External IO upgrades `LmIO` to `LIO` from `E.requestNodup`.  The intermediate columns
upgrade `LmIO` to `Perm` from already-held `addedRecordList_nodup` and
`consumed_length_eq_added_length`. -/

private theorem nodup_of_length_eq_toFinset_card {α : Type*} [DecidableEq α]
    {l : List α} (h : l.toFinset.card = l.length) : l.Nodup := by
  have hlen : l.dedup.length = l.length := by
    have hcard := List.toFinset_card_of_nodup (List.nodup_dedup l)
    have hfin : l.dedup.toFinset = l.toFinset := by
      ext x
      simp [List.mem_toFinset, List.mem_dedup]
    rw [hfin] at hcard
    exact hcard.trans h
  have heq : l.dedup = l :=
    List.Sublist.eq_of_length (List.dedup_sublist l) hlen
  rw [← heq]
  exact List.nodup_dedup l


/-- **The add/remove analogue of `cor_uni_req_uni_resp`.**  A semantic `LmIO` preimage of
the two `intermediate` columns, together with objects already on `E`, is
`PairedRecordLayout`.  This is why `C1` is not added as a field. -/
theorem pairedRecordLayout_of_intermediatePreimage
    (E : BuildableNockExecution F K)
    (w : SemanticIntermediatePreimage E.cfg E.exec) :
    RowLayout.PairedRecordLayout E.exec := by
  have hlen_sem : w.semanticConsumed.length = w.semanticAdded.length := by
    have h₁ := w.length_eq_columns.1
    have h₂ := w.length_eq_columns.2
    rw [h₂, consumed_length_eq_added_length E, h₁]
  have hlmio := (IO.LmIO_iff E.cfg.Ksz w.semanticConsumed w.semanticAdded).1 w.semantic_lmio
  obtain ⟨_, _, hnd_add, hfin⟩ := hlmio
  have hnd_cons : w.semanticConsumed.Nodup := by
    have hcard : w.semanticConsumed.toFinset.card = w.semanticConsumed.length := by
      rw [hfin, List.toFinset_card_of_nodup hnd_add, hlen_sem]
    exact nodup_of_length_eq_toFinset_card hcard
  have hperm_sem : w.semanticConsumed.Perm w.semanticAdded :=
    List.perm_of_nodup_nodup_toFinset_eq hnd_cons hnd_add hfin
  have hperm_enc :
      ((RowLayout.consumedRecordList E.exec).map (fun r => NockVM.encRecC r
          (E.exec.cprimeOf r))).Perm
        ((RowLayout.addedRecordList E.exec).map (fun r => NockVM.encRecC r (E.exec.cprimeOf r)))
            := by
    rw [← w.consumed_bridge, ← w.added_bridge]
    exact bridgeRecords_perm F K E.cfg.challenges.α E.cfg.challenges.lam hperm_sem
  exact perm_of_perm_map_encRecC_cp_here E.exec.cprimeOf hperm_enc

/-- Fourteen fields: `C1` was not added. -/
theorem buildableNockExecution_still_fourteen
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
  E.eta_with_memoryTrace

end

/-! ## §D. F97 witness — the two columns are a nontrivial permutation

`distinctCensusExecution` adds `recF, recT, recL, recR` in BFS `read_root` order and
removes `recF, recT, recR, recL` in BFS `verify_child` order.
Unlike F73, the lists are not definitionally equal. -/

namespace DistinctCensusC1

open DistinctCensusExecution

local instance prime97d : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97d : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-- 28th: the executed rows store the Form R row encodes `formRRow r λ` (was `[recF, …]`). -/
theorem addedRecordList_distinctCensus :
    RowLayout.addedRecordList execD =
      [formRRow recF MemoryTable.formRDefault, formRRow recT MemoryTable.formRDefault,
          formRRow recL MemoryTable.formRDefault,
        formRRow recR MemoryTable.formRDefault] := by
  rw [RowLayout.addedRecordList, execution_rowsD.2]
  simp [memoryLabelsD, MemoryTable.responseRecords, lblOf, pN1, pN2, pN3, pN4, pN5, pN6,
    pN7, pN15, pN8, pN16, pN9, pN17, pN18, pN10, pN11, pN19, pN12, pN20, pN21, pN13, pN14,
    readPub, decPub, haltPub, verifyPub]

theorem consumedRecordList_distinctCensus :
    RowLayout.consumedRecordList execD =
      [formRRow recF MemoryTable.formRDefault, formRRow recT MemoryTable.formRDefault,
          formRRow recR MemoryTable.formRDefault,
        formRRow recL MemoryTable.formRDefault] := by
  rw [RowLayout.consumedRecordList, execution_rowsD.2]
  simp [memoryLabelsD, RowLayout.consumedRecords, lblOf, pN1, pN2, pN3, pN4, pN5, pN6,
    pN7, pN15, pN8, pN16, pN9, pN17, pN18, pN10, pN11, pN19, pN12, pN20, pN21, pN13, pN14,
    readPub, decPub, haltPub, verifyPub]


/-- **J.0.3-style witness of the premise at F97.**  The add/remove lists are a swap of
the last two of four committed records, not an identity. -/
theorem pairedRecordLayout_distinctCensus :
    RowLayout.PairedRecordLayout execD := by
  rw [RowLayout.PairedRecordLayout, addedRecordList_distinctCensus,
    consumedRecordList_distinctCensus]
  exact (((List.Perm.swap (formRRow recR MemoryTable.formRDefault) (formRRow recL
      MemoryTable.formRDefault)
    []).cons _).cons _).symm

/-- The `C'` stored beside an executed read record is its Form R `formRCprime` (via
`execD_cprimeCoherent`). -/
theorem cprimeOf_execD_of_row (p : MemoryTable.Pub K97cubic) (hp : lblOf p ∈ memoryLabelsD)
    (r : ComputeTable.MemRec K97cubic) (hm : p.mem = formRRow r MemoryTable.formRDefault)
    (hc : p.cprime = formRCprime r MemoryTable.formRDefault) :
    execD.cprimeOf (formRRow r MemoryTable.formRDefault) =
      formRCprime r MemoryTable.formRDefault := by
  have h := ExactExecution.cprime_eq_cprimeOf execD_cprimeCoherent (lblOf p)
    (by rw [execution_rowsD.2]; exact hp)
  simp only [lblOf] at h
  rw [← hm, ← h, hc]

theorem cprimeOf_execD_recs :
    execD.cprimeOf (formRRow recF MemoryTable.formRDefault) =
      formRCprime recF MemoryTable.formRDefault ∧
      execD.cprimeOf (formRRow recT MemoryTable.formRDefault) =
        formRCprime recT MemoryTable.formRDefault ∧
      execD.cprimeOf (formRRow recL MemoryTable.formRDefault) =
        formRCprime recL MemoryTable.formRDefault ∧
      execD.cprimeOf (formRRow recR MemoryTable.formRDefault) =
        formRCprime recR MemoryTable.formRDefault := by
  refine ⟨cprimeOf_execD_of_row pN1 (by simp [memoryLabelsD]) _ (by simp [pN1, readPub])
      (by simp [pN1, readPub, MemoryTable.Pub.cprime]),
    cprimeOf_execD_of_row pN4 (by simp [memoryLabelsD]) _ (by simp [pN4, readPub])
      (by simp [pN4, readPub, MemoryTable.Pub.cprime]),
    cprimeOf_execD_of_row pN7 (by simp [memoryLabelsD]) _ (by simp [pN7, readPub])
      (by simp [pN7, readPub, MemoryTable.Pub.cprime]),
    cprimeOf_execD_of_row pN15 (by simp [memoryLabelsD]) _ (by simp [pN15, readPub])
      (by simp [pN15, readPub, MemoryTable.Pub.cprime])⟩

/-- Propositional helper over abstract atoms (avoids `tauto` unfolding record equalities). -/
theorem or4_swap_aux (a b c d : Prop) : (a ∨ b ∨ d ∨ c) ↔ (a ∨ b ∨ c ∨ d) := by tauto


/-- **Substantive F97 inhabitant of the designed `C1` type.**  Semantic consumed order is
`[semF, semT, semR, semL]`, which is not the add-column order. -/
noncomputable def intermediatePreimageD : SemanticIntermediatePreimage cfgD execD where
  semanticAdded := [semF, semT, semL, semR]
  semanticConsumed := [semF, semT, semR, semL]
  semantic_lmio := by
    refine ⟨by norm_num [IO.InRange, cfgD], [semF, semT, semL, semR],
      by simp, semRecs_nodup, ?_, List.Perm.refl _⟩
    intro x
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact or4_swap_aux _ _ _ _
  added_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_cons, List.map_cons, List.map_singleton,
      semF_bridge, semT_bridge, semL_bridge, semR_bridge, addedRecordList_distinctCensus]
    obtain ⟨hF, hT, hL, hR⟩ := cprimeOf_execD_recs
    simp only [List.map, hF, hT, hL, hR, encRecC_formRRow]
  consumed_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_cons, List.map_cons, List.map_singleton,
      semF_bridge, semT_bridge, semR_bridge, semL_bridge, consumedRecordList_distinctCensus]
    obtain ⟨hF, hT, hL, hR⟩ := cprimeOf_execD_recs
    simp only [List.map, hF, hT, hL, hR, encRecC_formRRow]

theorem intermediatePreimageD_columns_not_identical :
    (intermediatePreimageD).semanticConsumed ≠ (intermediatePreimageD).semanticAdded := by
  intro h
  have h2 :=
    congrArg (fun l : List ((nmrMEF F97 K97cubic).Rec) => l[2]?) h
  simp [intermediatePreimageD] at h2
  have : semR ≠ semL := by
    intro he
    have := congrArg (fun r : (nmrMEF F97 K97cubic).Rec => r.2.2) he
    norm_num [semR, semL] at this
  exact this h2

/-- Honest `ver` on the F97 distinct-census fixture (structure default). -/
theorem honestVer_distinctCensus
    (hfirstD :
      (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
        (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0) :
    ∀ row ∈ (distinctCensusExecution hfirstD).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  change ∀ row ∈ execD.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)
  simp [execution_rowsD.2, memoryLabelsD, lblOf,
    pN1, pN2, pN3, pN4, pN5, pN6, pN7, pN15, pN8, pN16, pN9, pN17, pN18, pN10, pN11,
    pN19, pN12, pN20, pN21, pN13, pN14, readPub, decPub, haltPub, verifyPub]

theorem timestampClosed_of_distinctCensus_paired_records
    (hfirstD :
      (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
        (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0) :
    ∀ i : Fin (distinctCensusExecution hfirstD).cfg.memRows,
      memoryMemRecKind ((distinctCensusExecution hfirstD).exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt (distinctCensusExecution hfirstD).cfg.challenges.α
          ((distinctCensusExecution hfirstD).exec.memoryRowAt i).2.2.mem.ts :=
  timestampClosed_of_paired_record_layout (E := distinctCensusExecution hfirstD)
    (honestVer_distinctCensus (hfirstD := hfirstD)) pairedRecordLayout_distinctCensus

/-- At F97 the designed type and the named premise are interchangeable. -/
theorem c1_iff_paired_at_f97
    (hfirstD :
      (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
        (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0) :
    Nonempty (SemanticIntermediatePreimage cfgD execD) ↔
      RowLayout.PairedRecordLayout execD :=
  ⟨fun ⟨w⟩ => pairedRecordLayout_of_intermediatePreimage (distinctCensusExecution hfirstD) w,
    fun _ => ⟨intermediatePreimageD⟩⟩

/-- Four residual premises became three when `firstLine` left the structure. -/
theorem residualPremises_still_four_after_c1
    (hfirstD :
      (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
        (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
    (P : ResidualPremises (distinctCensusExecution hfirstD)) :
    InactiveDecPaddingExec (distinctCensusExecution hfirstD).exec ∧
      (∀ i : Fin (distinctCensusExecution hfirstD).cfg.compRows,
        AxisAtomPremises ((distinctCensusExecution hfirstD).semanticData.rows i)) ∧
          (distinctCensusExecution hfirstD).q = ringChar K97cubic :=
  GenericHonestData.residualPremises_still_four P

end DistinctCensusC1

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.pairedRecordLayout_of_intermediatePreimage
#print axioms Nock.NockVMROM.Thm54.buildableNockExecution_still_fourteen
#print axioms Nock.NockVMROM.Thm54.DistinctCensusC1.pairedRecordLayout_distinctCensus
#print axioms Nock.NockVMROM.Thm54.DistinctCensusC1.intermediatePreimageD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusC1.intermediatePreimageD_columns_not_identical
#print axioms Nock.NockVMROM.Thm54.DistinctCensusC1.timestampClosed_of_distinctCensus_paired_records
#print axioms Nock.NockVMROM.Thm54.DistinctCensusC1.c1_iff_paired_at_f97
#print axioms Nock.NockVMROM.Thm54.DistinctCensusC1.residualPremises_still_four_after_c1
