/-
  Thm54/P8Core/SVFrameG/Bridge.lean -- Wave 5, F2: the bridge.  `standalone_iff` says the 38th
  statement `StandaloneThm54Statement CF MF joint` is equivalent to `StandaloneG` of the families'
  cores (nothing weakened); `standalone_generic_G`; `ioSummand = ioSummandG` by `rfl`.
-/
import Nock.NockVMROM.Thm54.P8Core.SVFrameG.StandaloneG
import Nock.NockVMROM.Thm54.P8Core.SVFrameG.IO

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.SVFrame

open Nock Nock.Framework Nock.Walk Nock.ComputeTable Nock.MemoryTable Nock.FieldEmbedding
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.SVGenuineF (HoldsF)
open scoped Polynomial

attribute [local instance] Classical.propDecidable

variable {F K Kio Kfp Key : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [Fintype F] [Field Kfp] [DecidableEq Key]
  [Fintype Kfp] [DecidableEq Kfp]
  [Field Kio] [Fintype Kio] [DecidableEq Kio] [Algebra F Kio]
  {Φ : CoinFrame} {hC : ℕ} {S : MemShape} {C : TableSpec} {nAcc : ℕ} {m : Fin nAcc → ℕ}
  {R : RecordView F K Kio Kfp Key C S hC m} {Z : SeedSpec Φ K Kfp} {I : IOCoinSpec Φ K Kio}

def CompSoundnessFamily.toCore (CF : CompSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I) :
    CompCore F K Kio Φ hC S C nAcc :=
  ⟨CF.Msg0, CF.chip, CF.chip_width, CF.reqBound, CF.summands, CF.Honest, CF.honestV, CF.honestQ,
    CF.honestReq, CF.honest_staged, CF.honestBad⟩

def MemSoundnessFamily.toCore (MF : MemSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I) :
    MemCore F K Kio Φ hC S C nAcc :=
  ⟨MF.Msg0, MF.Msg2, MF.chip, MF.chip_width, MF.internalBound, MF.summands, MF.Honest, MF.honestV,
    MF.honestQ, MF.honestReq, MF.honest_staged, MF.honestBad⟩

def CompSoundnessFamily.toIO (CF : CompSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I) :
    CompIO (m := m) F K Kio Φ hC S C nAcc I :=
  { CF.toCore with
    reqRecords := CF.reqRecords, recRound := CF.recRound, recRound_le_io := CF.recRound_le_io,
    reqRecords_round := CF.reqRecords_round }

def MemSoundnessFamily.toIO (MF : MemSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I) :
    MemIO (m := m) F K Kio Φ hC S C nAcc I :=
  { MF.toCore with
    respBound := MF.respBound, internal := MF.internal, respRecords := MF.respRecords,
    respRound := MF.respRound, respRound_le_io := MF.respRound_le_io,
    respRecords_round := MF.respRecords_round, internal_round := MF.internal_round }

omit [Fintype Kfp] [DecidableEq Kfp] in
/-- **The bridge**: the 38th statement is `StandaloneG` of the cores (not `rfl`: `AcceptsV` and
`AcceptsG` are distinct structures; message eta plus `Finset.filter_congr`). -/
theorem standalone_iff (CF : CompSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I)
    (MF : MemSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I)
    (joint : VerifierData F K hC S → CF.Msg0 → MF.Msg0 →
      List (BadSummand Φ K (Traces F C S) (TracesStaged Φ C S))) :
    StandaloneThm54Statement CF MF joint ↔ StandaloneG CF.toCore MF.toCore joint := by
  have key : ∀ (V : VerifierData F K hC S) (a b c d e f),
      (Finset.univ.filter fun χ : Coins Φ K =>
        AcceptsV V (⟨a, b, c, d, e, f⟩ : Messages CF MF) χ ∧ ¬ HoldsF (ringChar K) V.claim) =
      (Finset.univ.filter fun χ : Coins Φ K =>
        AcceptsG V (⟨a, b, c, d, e, f⟩ : MessagesG CF.toCore MF.toCore) χ ∧
          ¬ HoldsF (ringChar K) V.claim) :=
    fun V a b c d e f => Finset.filter_congr (fun χ _ =>
      and_congr_left' ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩)
  constructor
  · rintro ⟨hs, hc⟩
    refine ⟨fun V hV ⟨a, b, c, d, e, f⟩ hst => ?_, hc⟩
    have := hs V hV ⟨a, b, c, d, e, f⟩ hst
    erw [key] at this; exact this
  · rintro ⟨hs, hc⟩
    refine ⟨fun V hV ⟨a, b, c, d, e, f⟩ hst => ?_, hc⟩
    have := hs V hV ⟨a, b, c, d, e, f⟩ hst
    erw [← key] at this; exact this

omit [Fintype Kfp] [DecidableEq Kfp] in
/-- `ioEventAt` is `ioEventAtG` at the IO views, by `rfl`. -/
theorem ioEventAt_eq_G (CF : CompSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I)
    (MF : MemSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I) :
    ioEventAt CF MF = ioEventAtG CF.toIO MF.toIO := rfl

/-- `ioSummand` is `ioSummandG` at the IO views, by `rfl`. -/
theorem ioSummand_eq_G (CF : CompSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I)
    (MF : MemSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I) :
    ioSummand CF MF = ioSummandG CF.toIO MF.toIO := rfl

/-- `standalone_generic`, restated through `StandaloneG`. -/
theorem standalone_generic_G [CharP Kfp (ringChar Kfp)]
    (CF : CompSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I)
    (MF : MemSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I)
    (hrow : rowFactsAt CF) (hP : ExtraPremises CF MF) :
    StandaloneG CF.toCore MF.toCore (jointSummandsStd CF MF) :=
  (standalone_iff CF MF _).mp (standalone_generic hrow hP)

end Nock.NockVMROM.Thm54.SVFrame
