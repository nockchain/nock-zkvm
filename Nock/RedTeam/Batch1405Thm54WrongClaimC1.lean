import Nock.RedTeam.Batch1404Thm54WrongClaimExecution
import Nock.NockVMROM.Thm54.SemanticIntermediatePreimage



set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54

open scoped Classical
open Nock Nock.NockVM
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.WCExecution
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete

namespace WCC1

open WCExecution

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

theorem length_swap_last_two {α : Type} (a b c d : α) :
    ([a, b, d, c] : List α).length ≤ ([a, b, c, d] : List α).length := le_refl _

theorem mem_swap_last_two {α : Type} (a b c d : α) :
    ∀ x : α, x ∈ [a, b, c, d] ↔ x ∈ [a, b, d, c] := by
  intro x
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto


/-- **Substantive F97 inhabitant of the designed `C1` type.**  Semantic consumed order is
`[semF, semT, semR, semL]`, which is not the add-column order. -/
noncomputable def intermediatePreimageD : SemanticIntermediatePreimage cfgD execD where
  semanticAdded := [semF, semT, semL, semR]
  semanticConsumed := [semF, semT, semR, semL]
  semantic_lmio := by
    refine ⟨by norm_num [IO.InRange, cfgD], [semF, semT, semL, semR],
      length_swap_last_two _ _ _ _, semRecs_nodup, mem_swap_last_two _ _ _ _, List.Perm.refl _⟩
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

end WCC1

end Nock.NockVMROM.Thm54
