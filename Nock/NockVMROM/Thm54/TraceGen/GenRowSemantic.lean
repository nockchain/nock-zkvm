/-
  Nock/NockVMROM/Thm54/TraceGen/GenRowSemantic.lean

  Generator-side `ComputeRowSemanticData` and the cumulative noun-realized
  language, as identifications of existing constructors
  (`BoundSemanticTrace.buildCoveredRow` /
  `ComputeRowSemanticData.ofSkeleton`, `BindsAt.nounRealization`,
  `NounRealizedTraversableChainedSemanticExactLanguage.mk`).

  New work is `BindComputeRow` on `render*Row` against the matching
  `genSkel*`, so `rowSemanticDataOf` applies on BFS-rendered rows.
  `Gen.lean` is not edited.

  Slot/record → `SkeletonOperationalCore` is
  `skeletonOperationalCore_of_parts` (item 3).  Size windows and
  `q = ringChar` remain honest hyps via `ofCoreAndWindows`.
  Traversable/chained remains a carried hyp: Vcomp/WF are items 1–2;
  I/O chain is item 5.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenCensus
import Nock.NockVMROM.Thm54.BoundSemanticTrace
import Nock.NockVMROM.Thm54.NounRealization

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.BoundSemanticTrace
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy

variable {K : Type} [Field K]

/-! ## Fingerprint binding of `encC` -- Encode.encC_eq -/

theorem bindFP_encC (z : K) (n : Noun) : bindFP z n (encC z n) := by
  rw [bindFP, encC_eq]

theorem bindMemRec_encC (z : K) (root child : Noun) (axis : ℕ) (ts : K) :
    BindMemRec z ⟨root, child, axis⟩
      ⟨encC z root, encC z child, (axis : K), ts⟩ :=
  ⟨bindFP_encC z root, bindFP_encC z child, rfl⟩

theorem bindFP_triple (z : K) (s f e : Noun) (slot : TripleSlot) :
    bindFP z
      (match slot with
        | .subject => s
        | .formula => f
        | .result => e)
      (tripleFP (encC z s, encC z f, encC z e) slot) := by
  cases slot <;> simp [bindFP, tripleFP, encC_eq]

/-! ## Operational core from item-3 slot/record -/

theorem operationalCore_of_slot_record (s : ComputeRowSkeleton)
    (hrec : SkeletonRecordEquations s) (hslot : SkeletonSlotSemantics s) :
    SkeletonOperationalCore s :=
  skeletonOperationalCore_of_parts hrec hslot

theorem operationalPremises_of_core_windows {q : ℕ} {z : K}
    {s : ComputeRowSkeleton} (hq : q = ringChar K)
    (core : SkeletonOperationalCore s)
    (windows : SkeletonSizeWindowPremises z s) :
    SkeletonOperationalPremises q z s :=
  SkeletonOperationalPremises.ofCoreAndWindows hq core windows

theorem bfsAssign_operationalCore
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hrec : ∀ g ∈ bfsRows t, SkeletonRecordEquations g.skel)
    (hslot : ∀ g ∈ bfsRows t, SkeletonSlotSemantics g.skel) :
    ∀ s ∈ computeSkeletonRows (genSemanticSkeleton (bfsAssign t) mf),
      SkeletonOperationalCore s := by
  intro s hs
  exact operationalCore_of_slot_record s
    (bfsAssign_computeSkeletonRows_recordEquations t mf hrec s hs)
    (bfsAssign_computeSkeletonRows_slotSemantics t mf hslot s hs)

/-! ## `BindComputeRow` on rendered `genSkel*` -/

theorem genSkelOp1_bindCompute
    (z α : K) (subject formula result head : Noun)
    (stamp : SemanticTimestampStrategy.ComputeTimestampRow)
    (hhead : formulaHead formula = head) :
    BindComputeRow z (genSkelOp1 subject formula result head)
      (renderOp1Row z α stamp (genSkelOp1 subject formula result head)) := by
  refine ⟨rfl, rfl, rfl, bindFP_encC z _, bindFP_encC z _, bindFP_encC z _,
    ?dec, ?sf, ?mr⟩
  · intro slot
    cases slot with
    | f_h =>
      simp [genSkelOp1, renderOp1Row, decActive, decFP, bindFP, encC_eq, hhead]
    | f_t =>
      simp [genSkelOp1, renderOp1Row, decActive, decFP, bindFP, encC_eq]
    | f_th | f_tt | f_tth | f_ttt =>
      simp [genSkelOp1, renderOp1Row, decActive, hasTailDecomposition]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp
        (genSkelOp1 subject formula result head).state) := by
      simp [genSkelOp1, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, renderOp1Row,
        genSkelOp1]
  · intro i
    fin_cases i
    · simp [genSkelOp1, renderOp1Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount]
    · simp [genSkelOp1, renderOp1Row, computeMemRec, Nock.Framework.recordCount]
    · simp [genSkelOp1, renderOp1Row, computeMemRec, Nock.Framework.recordCount]

theorem genSkelCons_bindCompute
    (z α : K) (subject leftF rightF leftR rightR : Noun)
    (stamp : SemanticTimestampStrategy.ComputeTimestampRow) :
    BindComputeRow z (genSkelCons subject leftF rightF leftR rightR)
      (renderConsRow z α stamp
        (genSkelCons subject leftF rightF leftR rightR)) := by
  refine ⟨rfl, rfl, rfl, bindFP_encC z _, bindFP_encC z _, bindFP_encC z _,
    ?dec, ?sf, ?mr⟩
  · intro slot
    cases slot with
    | f_h | f_t =>
      simp [genSkelCons, renderConsRow, decActive, decFP, bindFP, encC_eq,
        formulaHead, formulaTail]
    | f_th | f_tt | f_tth | f_ttt =>
      simp [genSkelCons, renderConsRow, decActive, hasTailDecomposition]
  · intro i
    fin_cases i
    · intro slot
      cases slot <;>
        simp [genSkelCons, renderConsRow, computeSubformulaFPs,
          ComputeTable.sfTriple, ComputeTable.fanoutComp, bindFP, encC_eq,
          tripleFP, formulaHead, formulaTail]
    · intro slot
      cases slot <;>
        simp [genSkelCons, renderConsRow, computeSubformulaFPs,
          ComputeTable.sfTriple, ComputeTable.fanoutComp, bindFP, encC_eq,
          tripleFP, formulaHead, formulaTail]
    · simp [genSkelCons, renderConsRow, computeSubformulaFPs,
        ComputeTable.sfTriple, ComputeTable.fanoutComp]
  · intro i
    fin_cases i
    · simp [genSkelCons, renderConsRow, computeMemRec, BindMemRec, bindFP,
        encC_eq, Nock.Framework.recordCount, formulaTail]
    · simp [genSkelCons, renderConsRow, computeMemRec, Nock.Framework.recordCount]
    · simp [genSkelCons, renderConsRow, computeMemRec, Nock.Framework.recordCount]

theorem genSkelOp0_bindCompute
    (z α : K) (subject formula head tail result : Noun) (axis : ℕ)
    (stamp : SemanticTimestampStrategy.ComputeTimestampRow)
    (hhead : formulaHead formula = head) (htail : formulaTail formula = tail) :
    BindComputeRow z (genSkelOp0 subject formula head tail result axis)
      (renderOp0Row z α stamp
        (genSkelOp0 subject formula head tail result axis)) := by
  refine ⟨rfl, rfl, rfl, bindFP_encC z _, bindFP_encC z _, bindFP_encC z _,
    ?dec, ?sf, ?mr⟩
  · intro slot
    cases slot with
    | f_h =>
      simp [genSkelOp0, renderOp0Row, decActive, decFP, bindFP, encC_eq, hhead]
    | f_t =>
      simp [genSkelOp0, renderOp0Row, decActive, decFP, bindFP, encC_eq, htail]
    | f_th | f_tt | f_tth | f_ttt =>
      simp [genSkelOp0, renderOp0Row, decActive, hasTailDecomposition]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp
        (genSkelOp0 subject formula head tail result axis).state) := by
      simp [genSkelOp0, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, renderOp0Row, genSkelOp0]
  · intro i
    fin_cases i
    · simp [genSkelOp0, renderOp0Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount, htail]
    · simp [genSkelOp0, renderOp0Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount, P8Census.skeletonMemoryAxis]
    · simp [genSkelOp0, renderOp0Row, computeMemRec, Nock.Framework.recordCount]

/-! ### Unary OP3 / OP4 -/

theorem genSkelOp3_bindCompute
    (z α : K) (subject formula head tail callSubject callFormula callResult
      result : Noun)
    (stamp : SemanticTimestampStrategy.ComputeTimestampRow)
    (hhead : formulaHead formula = head) (htail : formulaTail formula = tail) :
    BindComputeRow z
      (genSkelOp3 subject formula head tail callSubject callFormula callResult
        result)
      (renderOp3Row z α stamp
        (genSkelOp3 subject formula head tail callSubject callFormula callResult
          result)) := by
  refine ⟨rfl, rfl, rfl, bindFP_encC z _, bindFP_encC z _, bindFP_encC z _,
    ?dec, ?sf, ?mr⟩
  · intro slot
    cases slot with
    | f_h =>
      simp [genSkelOp3, renderOp3Row, decActive, decFP, bindFP, encC_eq, hhead]
    | f_t =>
      simp [genSkelOp3, renderOp3Row, decActive, decFP, bindFP, encC_eq, htail]
    | f_th | f_tt | f_tth | f_ttt =>
      simp [genSkelOp3, renderOp3Row, decActive, hasTailDecomposition]
  · intro i
    fin_cases i
    · intro slot
      cases slot <;>
        simp [genSkelOp3, renderOp3Row, computeSubformulaFPs,
          ComputeTable.sfTriple, ComputeTable.fanoutComp, P8Census.skeletonSubformula,
          bindFP, encC_eq, tripleFP]
    · simp [genSkelOp3, renderOp3Row, computeSubformulaFPs,
        ComputeTable.sfTriple, ComputeTable.fanoutComp]
    · simp [genSkelOp3, renderOp3Row, computeSubformulaFPs,
        ComputeTable.sfTriple, ComputeTable.fanoutComp]
  · intro i
    fin_cases i
    · simp [genSkelOp3, renderOp3Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount, htail]
    · simp [genSkelOp3, renderOp3Row, computeMemRec, Nock.Framework.recordCount]
    · simp [genSkelOp3, renderOp3Row, computeMemRec, Nock.Framework.recordCount]

theorem genSkelOp4_bindCompute
    (z α : K) (subject formula head tail callSubject callFormula callResult
      result : Noun)
    (stamp : SemanticTimestampStrategy.ComputeTimestampRow)
    (hhead : formulaHead formula = head) (htail : formulaTail formula = tail) :
    BindComputeRow z
      (genSkelOp4 subject formula head tail callSubject callFormula callResult
        result)
      (renderOp4Row z α stamp
        (genSkelOp4 subject formula head tail callSubject callFormula callResult
          result)) := by
  refine ⟨rfl, rfl, rfl, bindFP_encC z _, bindFP_encC z _, bindFP_encC z _,
    ?dec, ?sf, ?mr⟩
  · intro slot
    cases slot with
    | f_h =>
      simp [genSkelOp4, renderOp4Row, decActive, decFP, bindFP, encC_eq, hhead]
    | f_t =>
      simp [genSkelOp4, renderOp4Row, decActive, decFP, bindFP, encC_eq, htail]
    | f_th | f_tt | f_tth | f_ttt =>
      simp [genSkelOp4, renderOp4Row, decActive, hasTailDecomposition]
  · intro i
    fin_cases i
    · intro slot
      cases slot <;>
        simp [genSkelOp4, renderOp4Row, computeSubformulaFPs,
          ComputeTable.sfTriple, ComputeTable.fanoutComp, P8Census.skeletonSubformula,
          bindFP, encC_eq, tripleFP]
    · simp [genSkelOp4, renderOp4Row, computeSubformulaFPs,
        ComputeTable.sfTriple, ComputeTable.fanoutComp]
    · simp [genSkelOp4, renderOp4Row, computeSubformulaFPs,
        ComputeTable.sfTriple, ComputeTable.fanoutComp]
  · intro i
    fin_cases i
    · simp [genSkelOp4, renderOp4Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount, htail]
    · simp [genSkelOp4, renderOp4Row, computeMemRec, Nock.Framework.recordCount]
    · simp [genSkelOp4, renderOp4Row, computeMemRec, Nock.Framework.recordCount]

/-! ### Two-record stars OP2 / OP5 / OP7 / OP8 -/

theorem genSkelOp2_bindCompute
    (z α : K) (subject formula head fTail fTh fTt sf1 sf2 result : Noun)
    (stamp : SemanticTimestampStrategy.ComputeTimestampRow)
    (hhead : formulaHead formula = head) (htail : formulaTail formula = fTail)
    (hth : formulaHead (formulaTail formula) = fTh)
    (htt : formulaTail (formulaTail formula) = fTt) :
    BindComputeRow z
      (genSkelOp2 subject formula head fTail fTh fTt sf1 sf2 result)
      (renderOp2Row z α stamp
        (genSkelOp2 subject formula head fTail fTh fTt sf1 sf2 result)) := by
  refine ⟨rfl, rfl, rfl, bindFP_encC z _, bindFP_encC z _, bindFP_encC z _,
    ?dec, ?sf, ?mr⟩
  · intro slot
    cases slot with
    | f_h =>
      simp [genSkelOp2, renderOp2Row, decActive, decFP, bindFP, encC_eq, hhead]
    | f_t =>
      simp [genSkelOp2, renderOp2Row, decActive, decFP, bindFP, encC_eq, htail]
    | f_th =>
      simp [genSkelOp2, renderOp2Row, decActive, hasTailDecomposition, decFP,
        bindFP, encC_eq, hth]
    | f_tt =>
      simp [genSkelOp2, renderOp2Row, decActive, hasTailDecomposition, decFP,
        bindFP, encC_eq, htt]
    | f_tth | f_ttt =>
      simp [genSkelOp2, renderOp2Row, decActive, hasTailDecomposition]
  · intro i
    fin_cases i
    · intro slot
      cases slot <;>
        simp [genSkelOp2, renderOp2Row, computeSubformulaFPs,
          ComputeTable.sfTriple, ComputeTable.fanoutComp, P8Census.skeletonSubformula,
          bindFP, encC_eq, tripleFP]
    · intro slot
      cases slot <;>
        simp [genSkelOp2, renderOp2Row, computeSubformulaFPs,
          ComputeTable.sfTriple, ComputeTable.fanoutComp, P8Census.skeletonSubformula,
          bindFP, encC_eq, tripleFP]
    · intro slot
      cases slot <;>
        simp [genSkelOp2, renderOp2Row, computeSubformulaFPs,
          ComputeTable.sfTriple, ComputeTable.fanoutComp, P8Census.skeletonSubformula,
          bindFP, encC_eq, tripleFP]
  · intro i
    fin_cases i
    · simp [genSkelOp2, renderOp2Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount, htail]
    · simp [genSkelOp2, renderOp2Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount, ← htail, hth]
    · simp [genSkelOp2, renderOp2Row, computeMemRec, Nock.Framework.recordCount]

theorem genSkelOp5_bindCompute
    (z α : K) (subject formula head fTail fTh fTt sf1 sf2 result : Noun)
    (stamp : SemanticTimestampStrategy.ComputeTimestampRow)
    (hhead : formulaHead formula = head) (htail : formulaTail formula = fTail)
    (hth : formulaHead (formulaTail formula) = fTh)
    (htt : formulaTail (formulaTail formula) = fTt) :
    BindComputeRow z
      (genSkelOp5 subject formula head fTail fTh fTt sf1 sf2 result)
      (renderOp5Row z α stamp
        (genSkelOp5 subject formula head fTail fTh fTt sf1 sf2 result)) := by
  refine ⟨rfl, rfl, rfl, bindFP_encC z _, bindFP_encC z _, bindFP_encC z _,
    ?dec, ?sf, ?mr⟩
  · intro slot
    cases slot with
    | f_h =>
      simp [genSkelOp5, renderOp5Row, decActive, decFP, bindFP, encC_eq, hhead]
    | f_t =>
      simp [genSkelOp5, renderOp5Row, decActive, decFP, bindFP, encC_eq, htail]
    | f_th =>
      simp [genSkelOp5, renderOp5Row, decActive, hasTailDecomposition, decFP,
        bindFP, encC_eq, hth]
    | f_tt =>
      simp [genSkelOp5, renderOp5Row, decActive, hasTailDecomposition, decFP,
        bindFP, encC_eq, htt]
    | f_tth | f_ttt =>
      simp [genSkelOp5, renderOp5Row, decActive, hasTailDecomposition]
  · intro i
    fin_cases i
    · intro slot
      cases slot <;>
        simp [genSkelOp5, renderOp5Row, computeSubformulaFPs,
          ComputeTable.sfTriple, ComputeTable.fanoutComp, P8Census.skeletonSubformula,
          bindFP, encC_eq, tripleFP]
    · intro slot
      cases slot <;>
        simp [genSkelOp5, renderOp5Row, computeSubformulaFPs,
          ComputeTable.sfTriple, ComputeTable.fanoutComp, P8Census.skeletonSubformula,
          bindFP, encC_eq, tripleFP]
    · simp [genSkelOp5, renderOp5Row, computeSubformulaFPs,
        ComputeTable.sfTriple, ComputeTable.fanoutComp]
  · intro i
    fin_cases i
    · simp [genSkelOp5, renderOp5Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount, htail]
    · simp [genSkelOp5, renderOp5Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount, ← htail, hth]
    · simp [genSkelOp5, renderOp5Row, computeMemRec, Nock.Framework.recordCount]

theorem genSkelOp7_bindCompute
    (z α : K) (subject formula head fTail fTh fTt sb result : Noun)
    (stamp : SemanticTimestampStrategy.ComputeTimestampRow)
    (hhead : formulaHead formula = head) (htail : formulaTail formula = fTail)
    (hth : formulaHead (formulaTail formula) = fTh)
    (htt : formulaTail (formulaTail formula) = fTt) :
    BindComputeRow z
      (genSkelOp7 subject formula head fTail fTh fTt sb result)
      (renderOp7Row z α stamp
        (genSkelOp7 subject formula head fTail fTh fTt sb result)) := by
  refine ⟨rfl, rfl, rfl, bindFP_encC z _, bindFP_encC z _, bindFP_encC z _,
    ?dec, ?sf, ?mr⟩
  · intro slot
    cases slot with
    | f_h =>
      simp [genSkelOp7, renderOp7Row, decActive, decFP, bindFP, encC_eq, hhead]
    | f_t =>
      simp [genSkelOp7, renderOp7Row, decActive, decFP, bindFP, encC_eq, htail]
    | f_th =>
      simp [genSkelOp7, renderOp7Row, decActive, hasTailDecomposition, decFP,
        bindFP, encC_eq, hth]
    | f_tt =>
      simp [genSkelOp7, renderOp7Row, decActive, hasTailDecomposition, decFP,
        bindFP, encC_eq, htt]
    | f_tth | f_ttt =>
      simp [genSkelOp7, renderOp7Row, decActive, hasTailDecomposition]
  · intro i
    fin_cases i
    · intro slot
      cases slot <;>
        simp [genSkelOp7, renderOp7Row, computeSubformulaFPs,
          ComputeTable.sfTriple, ComputeTable.fanoutComp, P8Census.skeletonSubformula,
          bindFP, encC_eq, tripleFP]
    · intro slot
      cases slot <;>
        simp [genSkelOp7, renderOp7Row, computeSubformulaFPs,
          ComputeTable.sfTriple, ComputeTable.fanoutComp, P8Census.skeletonSubformula,
          bindFP, encC_eq, tripleFP]
    · simp [genSkelOp7, renderOp7Row, computeSubformulaFPs,
        ComputeTable.sfTriple, ComputeTable.fanoutComp]
  · intro i
    fin_cases i
    · simp [genSkelOp7, renderOp7Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount, htail]
    · simp [genSkelOp7, renderOp7Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount, ← htail, hth]
    · simp [genSkelOp7, renderOp7Row, computeMemRec, Nock.Framework.recordCount]

theorem genSkelOp8_bindCompute
    (z α : K) (subject formula head fTail fTh fTt sb result : Noun)
    (stamp : SemanticTimestampStrategy.ComputeTimestampRow)
    (hhead : formulaHead formula = head) (htail : formulaTail formula = fTail)
    (hth : formulaHead (formulaTail formula) = fTh)
    (htt : formulaTail (formulaTail formula) = fTt) :
    BindComputeRow z
      (genSkelOp8 subject formula head fTail fTh fTt sb result)
      (renderOp8Row z α stamp
        (genSkelOp8 subject formula head fTail fTh fTt sb result)) := by
  refine ⟨rfl, rfl, rfl, bindFP_encC z _, bindFP_encC z _, bindFP_encC z _,
    ?dec, ?sf, ?mr⟩
  · intro slot
    cases slot with
    | f_h =>
      simp [genSkelOp8, renderOp8Row, decActive, decFP, bindFP, encC_eq, hhead]
    | f_t =>
      simp [genSkelOp8, renderOp8Row, decActive, decFP, bindFP, encC_eq, htail]
    | f_th =>
      simp [genSkelOp8, renderOp8Row, decActive, hasTailDecomposition, decFP,
        bindFP, encC_eq, hth]
    | f_tt =>
      simp [genSkelOp8, renderOp8Row, decActive, hasTailDecomposition, decFP,
        bindFP, encC_eq, htt]
    | f_tth | f_ttt =>
      simp [genSkelOp8, renderOp8Row, decActive, hasTailDecomposition]
  · intro i
    fin_cases i
    · intro slot
      cases slot <;>
        simp [genSkelOp8, renderOp8Row, computeSubformulaFPs,
          ComputeTable.sfTriple, ComputeTable.fanoutComp, P8Census.skeletonSubformula,
          bindFP, encC_eq, tripleFP]
    · intro slot
      cases slot <;>
        simp [genSkelOp8, renderOp8Row, computeSubformulaFPs,
          ComputeTable.sfTriple, ComputeTable.fanoutComp, P8Census.skeletonSubformula,
          bindFP, encC_eq, tripleFP]
    · simp [genSkelOp8, renderOp8Row, computeSubformulaFPs,
        ComputeTable.sfTriple, ComputeTable.fanoutComp]
  · intro i
    fin_cases i
    · simp [genSkelOp8, renderOp8Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount, htail]
    · simp [genSkelOp8, renderOp8Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount, ← htail, hth]
    · simp [genSkelOp8, renderOp8Row, computeMemRec, Nock.Framework.recordCount]

/-! ### Three-record OP9 / OP6 -/

theorem genSkelOp9_bindCompute
    (z α : K) (subject formula head fTail fTh fTt core arm result : Noun)
    (axis : ℕ) (stamp : SemanticTimestampStrategy.ComputeTimestampRow)
    (hhead : formulaHead formula = head) (htail : formulaTail formula = fTail)
    (hth : formulaHead (formulaTail formula) = fTh)
    (htt : formulaTail (formulaTail formula) = fTt) :
    BindComputeRow z
      (genSkelOp9 subject formula head fTail fTh fTt core arm result axis)
      (renderOp9Row z α stamp
        (genSkelOp9 subject formula head fTail fTh fTt core arm result axis)) := by
  refine ⟨rfl, rfl, rfl, bindFP_encC z _, bindFP_encC z _, bindFP_encC z _,
    ?dec, ?sf, ?mr⟩
  · intro slot
    cases slot with
    | f_h =>
      simp [genSkelOp9, renderOp9Row, decActive, decFP, bindFP, encC_eq, hhead]
    | f_t =>
      simp [genSkelOp9, renderOp9Row, decActive, decFP, bindFP, encC_eq, htail]
    | f_th =>
      simp [genSkelOp9, renderOp9Row, decActive, hasTailDecomposition, decFP,
        bindFP, encC_eq, hth]
    | f_tt =>
      simp [genSkelOp9, renderOp9Row, decActive, hasTailDecomposition, decFP,
        bindFP, encC_eq, htt]
    | f_tth | f_ttt =>
      simp [genSkelOp9, renderOp9Row, decActive, hasTailDecomposition]
  · intro i
    fin_cases i
    · intro slot
      cases slot <;>
        simp [genSkelOp9, renderOp9Row, computeSubformulaFPs,
          ComputeTable.sfTriple, ComputeTable.fanoutComp, P8Census.skeletonSubformula,
          bindFP, encC_eq, tripleFP]
    · intro slot
      cases slot <;>
        simp [genSkelOp9, renderOp9Row, computeSubformulaFPs,
          ComputeTable.sfTriple, ComputeTable.fanoutComp, P8Census.skeletonSubformula,
          bindFP, encC_eq, tripleFP]
    · simp [genSkelOp9, renderOp9Row, computeSubformulaFPs,
        ComputeTable.sfTriple, ComputeTable.fanoutComp]
  · intro i
    fin_cases i
    · simp [genSkelOp9, renderOp9Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount, htail]
    · simp [genSkelOp9, renderOp9Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount, ← htail, hth]
    · simp [genSkelOp9, renderOp9Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount, P8Census.skeletonMemoryAxis,
        P8Census.skeletonSubformula, ComputeTable.fanoutComp]

theorem genSkelOp6_bindCompute
    (z α : K) (subject formula head fTail fTh fTt fTth fTtt cond taken
      result : Noun)
    (stamp : SemanticTimestampStrategy.ComputeTimestampRow)
    (hhead : formulaHead formula = head) (htail : formulaTail formula = fTail)
    (hth : formulaHead (formulaTail formula) = fTh)
    (htt : formulaTail (formulaTail formula) = fTt)
    (htth : formulaHead (formulaTail (formulaTail formula)) = fTth)
    (httt : formulaTail (formulaTail (formulaTail formula)) = fTtt) :
    BindComputeRow z
      (genSkelOp6 subject formula head fTail fTh fTt fTth fTtt cond taken result)
      (renderOp6Row z α stamp
        (genSkelOp6 subject formula head fTail fTh fTt fTth fTtt cond taken
          result)) := by
  refine ⟨rfl, rfl, rfl, bindFP_encC z _, bindFP_encC z _, bindFP_encC z _,
    ?dec, ?sf, ?mr⟩
  · intro slot
    cases slot with
    | f_h =>
      simp [genSkelOp6, renderOp6Row, decActive, decFP, bindFP, encC_eq, hhead]
    | f_t =>
      simp [genSkelOp6, renderOp6Row, decActive, decFP, bindFP, encC_eq, htail]
    | f_th =>
      simp [genSkelOp6, renderOp6Row, decActive, hasTailDecomposition, decFP,
        bindFP, encC_eq, hth]
    | f_tt =>
      simp [genSkelOp6, renderOp6Row, decActive, hasTailDecomposition, decFP,
        bindFP, encC_eq, htt]
    | f_tth =>
      simp [genSkelOp6, renderOp6Row, decActive, decFP, bindFP, encC_eq, htth]
    | f_ttt =>
      simp [genSkelOp6, renderOp6Row, decActive, decFP, bindFP, encC_eq, httt]
  · intro i
    fin_cases i
    · intro slot
      cases slot <;>
        simp [genSkelOp6, renderOp6Row, computeSubformulaFPs,
          ComputeTable.sfTriple, ComputeTable.fanoutComp, P8Census.skeletonSubformula,
          bindFP, encC_eq, tripleFP]
    · intro slot
      cases slot <;>
        simp [genSkelOp6, renderOp6Row, computeSubformulaFPs,
          ComputeTable.sfTriple, ComputeTable.fanoutComp, P8Census.skeletonSubformula,
          bindFP, encC_eq, tripleFP]
    · simp [genSkelOp6, renderOp6Row, computeSubformulaFPs,
        ComputeTable.sfTriple, ComputeTable.fanoutComp]
  · intro i
    fin_cases i
    · simp [genSkelOp6, renderOp6Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount, htail]
    · simp [genSkelOp6, renderOp6Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount, ← htail, hth]
    · simp [genSkelOp6, renderOp6Row, computeMemRec, BindMemRec, bindFP, encC_eq,
        Nock.Framework.recordCount, ← htt, htth]

/-! ## Canonical row data -- `buildCoveredRow` / `ofSkeleton` -/

/-- Generator-side name of the existing covered-row constructor. -/
noncomputable def rowSemanticDataOf {q Λ : ℕ} {z : K}
    {s : ComputeRowSkeleton}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hb : s.BoundedBy q) (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        c.LeavesBounded Λ) :
    ComputeRowSemanticData q Λ row :=
  (buildCoveredRow hb hop hbind hfaith hleaves).1

theorem rowSemanticDataOf_eq {q Λ : ℕ} {z : K}
    {s : ComputeRowSkeleton}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hb : s.BoundedBy q) (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        c.LeavesBounded Λ) :
    rowSemanticDataOf hb hop hbind hfaith hleaves =
      (buildCoveredRow hb hop hbind hfaith hleaves).1 :=
  rfl

/-! ## Noun realization and the cumulative language -/

theorem nounRealization_of_binds {F : Type} [Field F] [Algebra F K]
    {q : ℕ} {z : K} (hz : z ≠ 0) {S : SemanticSkeleton}
    (hb : S.BoundedBy q) {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : BindsAt z S cfg exec) :
    ExactExecutionNounRealization q cfg exec :=
  BindsAt.nounRealization hz hb h

theorem language_of_traversable_noun {F : Type} [Field F] [Algebra F K]
    {q : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (ht : TraversableChainedSemanticExactLanguage cfg exec)
    (hn : ExactExecutionNounRealization q cfg exec) :
    NounRealizedTraversableChainedSemanticExactLanguage q cfg exec where
  traversable := ht
  nounRealization := hn

/-! ## Non-vacuity -- bind on the OP1 / cons / OP0 generators -/

theorem genSkelOp1_bind_nonvacuous (z α : K) :
    BindComputeRow z
      (genSkelOp1 (.atom 0) (.cell (.atom 1) (.atom 5)) (.atom 5) (.atom 1))
      (renderOp1Row z α (stampOfAcc .s1 0)
        (genSkelOp1 (.atom 0) (.cell (.atom 1) (.atom 5)) (.atom 5) (.atom 1))) :=
  genSkelOp1_bindCompute z α _ _ _ _ _ rfl

theorem genSkelCons_bind_nonvacuous (z α : K) :
    BindComputeRow z
      (genSkelCons (.atom 0) (.atom 1) (.atom 2) (.atom 3) (.atom 4))
      (renderConsRow z α (stampOfAcc .cons 0)
        (genSkelCons (.atom 0) (.atom 1) (.atom 2) (.atom 3) (.atom 4))) :=
  genSkelCons_bindCompute z α _ _ _ _ _ _

theorem genSkelOp0_bind_nonvacuous (z α : K) :
    BindComputeRow z
      (genSkelOp0 (.cell (.atom 3) (.atom 4)) (.cell (.atom 0) (.atom 2))
        (.atom 0) (.atom 2) (.atom 3) 2)
      (renderOp0Row z α (stampOfAcc .s0 0)
        (genSkelOp0 (.cell (.atom 3) (.atom 4)) (.cell (.atom 0) (.atom 2))
          (.atom 0) (.atom 2) (.atom 3) 2)) :=
  genSkelOp0_bindCompute z α _ _ _ _ _ _ _ rfl rfl

theorem operationalCore_op1_nonvacuous :
    SkeletonOperationalCore
      (genSkelOp1 (.atom 0) (.cell (.atom 1) (.atom 5)) (.atom 5) (.atom 1)) :=
  operationalCore_of_slot_record _
    (genSkelOp1_recordEquations _ _ _ _)
    (genSkelOp1_slotSemantics _ _ _ _)

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp1_bindCompute
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelCons_bindCompute
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp0_bindCompute
#print axioms Nock.NockVMROM.Thm54.TraceGen.rowSemanticDataOf
#print axioms Nock.NockVMROM.Thm54.TraceGen.nounRealization_of_binds
#print axioms Nock.NockVMROM.Thm54.TraceGen.language_of_traversable_noun
#print axioms Nock.NockVMROM.Thm54.TraceGen.bfsAssign_operationalCore
