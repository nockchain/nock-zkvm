/-
  Nock/NockVMROM/Thm54/P8Core/EvOnly/RootGoodFTracesEv.lean

  **The package-free context at the traces.**
  The twin of `Batch1173.ctx_of_traces_ev`
  (`EvOnly/Batch1173Thm54C2CombinedServedRecordsEv.lean`) with `hΛG : programLeafBound (airReorder G) ≤ Λ`
  and the honest tree `G` DELETED and the abstract window premise added: the conclusion is
  `RootGoodF.CtxF` at a window `W ≤ P.optimized.Λ` under `1 ≤ W` and
  `nprSeed c.1 ∉ lowOrderRootSeeds W` (the noun-free size-window event).

  No leaf bound of any
  honest tree is named.  Imports P8Core only; never the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.RootGoodF
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch1173Thm54C2CombinedServedRecordsEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace Nock.NockVMROM.Thm54.RootGoodF

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.StrategyOfTracesEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.ComputedWindow
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam.Batch1024
open Nock.RedTeam.Batch1171
open Nock.GlobalCarryRecognizer
open Nock.FieldEmbedding

/-! ## §A  Monotonicity of the context in the window -/

section Mono

variable {K : Type} [Field K] [DecidableEq K] [Fintype K] [CharP K (ringChar K)]
variable {sv : MState → ℕ → Noun} {ax : ℕ → ℕ}

theorem lowOrderFree_mono {z : K} {W W' : ℕ} (hW : W ≤ W') (h : LowOrderFree z W') :
    LowOrderFree z W :=
  fun d hd1 hdW => h d hd1 (hdW.trans hW)

theorem recOK_mono {z : K} {q W W' : ℕ} (hW : W ≤ W') {row : (State × DTcomp K) × ℕ}
    {v : ComputeRowSkeleton} (h : RecOK z q W' row v) : RecOK z q W row v :=
  fun j hj he hl hb => h j hj he (hl.trans hW) hb

theorem censusOK_mono {z : K} {W W' : ℕ} (hW : W ≤ W') {v : ComputeRowSkeleton}
    (h : CensusOK z W' v) : CensusOK z W v :=
  fun c hc hl hr => h c hc (hl.trans hW) (hr.trans hW)

end Mono

/-! ## §B  The context at the traces -/

section Traces

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

open Nock.RedTeam.Batch1111 (rowFacts_core_ev censusOK_of_ev)
open Nock.RedTeam.Batch1142 (hα0_of_goodEv)

/-- **The package-free context at the traces** (`Batch1173.ctx_of_traces_ev` without `G` and `hΛG`):
`CtxF` at every window `W ≤ P.optimized.Λ` with `1 ≤ W`, outside the low-order seeds of `W`. -/
theorem ctxF_of_traces_ev
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P
      (honestQc P c Qc) (honestQm P c Qm))
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    {W : ℕ} (hWΛ : W ≤ P.optimized.Λ) (hW1 : 1 ≤ W)
    (hlow : nprSeed c.1 ∉ SizeWindowCounting.lowOrderRootSeeds (K := K) W)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x) :
    CtxF (sv := svF P c Qm) (ax := axF P c Qc) (nprSeed c.1) (ringChar K) W
      (treeS P c Qc) P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula := by
  have h11 := OptimizedHostileConfiguration.eleven_lt_ringChar_of_package P
  have hz := FamilyIOChain.nprSeed_ne_of_good_at_ev P c Qc Qm hgood
  have hα0 := hα0_of_goodEv P c Qc Qm hgoodEv
  have haxc := Nock.RedTeam.Batch1140.certAxesOK0_of_traces_ev P c Qc Qm hacc hgood hax hbasis hwidth hα0 h
  have hrec := Nock.RedTeam.Batch1172.servedRecordsPos_of_traces_ev P c Qc Qm hacc hgood hax hbasis hwidth hgoodEv h hF
  refine ⟨hz, by omega, by omega, ?_, hW1, lowOrderFree_of_not_mem hlow, ?_, ?_, ?_⟩
  · exact CharP.natCast_injOn_Iio K (ringChar K)
  · intro u hu
    obtain ⟨hst, hz', hV, har, hl⟩ := rowFacts_core_ev P c Qc Qm hacc hgood hax hbasis hwidth h u hu
    exact ⟨hst, hz', hV, har, hl, (haxc u hu).1, (haxc u hu).2⟩
  · intro u s f hpr
    exact recOK_mono hWΛ (hrec u s f hpr)
  · intro u s f _ hreach
    exact censusOK_mono hWΛ (censusOK_of_ev P c Qc Qm hgoodEv hreach)

end Traces

end Nock.NockVMROM.Thm54.RootGoodF
