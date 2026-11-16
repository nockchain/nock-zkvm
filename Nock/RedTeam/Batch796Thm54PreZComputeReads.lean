/-
  Nock/RedTeam/Batch796Thm54PreZComputeReads.lean

  * **(A) Joint agreement.**  `PreZAgree2 P (Qc, Qm) (Qc', Qm')`: the compute pair agrees under
    `PreZAgreeOn (compCC P)` and the memory pair under `PreZAgreeOn (memCC P)` (the landed memory
    model, `PreSeedCensus`).
  * **(B) `Batch742.reqTgt` is pre-`z` on both chips**, for every target builder `Tb Qc Qm` that
    is itself jointly pre-`z` (`reqTgt_preZReads_both`), and so is the route-B pair event
    (`reqPairEvent_preZReads_both`).
  * **(C) The served-decomposition targets are pre-`z` on both chips.**  Every such target, and `reqTgt` at it, is jointly pre-`z`
    (`servedDecompTgt_preZReads_both`, `reqTgt_servedDecomp_preZReads_both`).
  * **(D) Positive controls.**  A compute read of a round-1 column (`𝕂` role `0`) is not pre-`z`
    (`PreZComputeCensus.not_preZReads_role0`, restated as `compute_role0_not_preZ`), and a target
    builder that reads it is not jointly pre-`z` (`role0_builder_not_preZ`): the instrument
    separates.
-/
import Nock.NockVMROM.Thm54.PreZComputeCensus
import Nock.RedTeam.Batch742Thm54RouteBCensus
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch796

open scoped Polynomial
open Polynomial
open Nock
open Nock.MemoryTable
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DeployedStaging
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.NockVMROM.Thm54.PreZComputeCore
open Nock.NockVMROM.Thm54.PreZComputeCore.Served
open Nock.NockVMROM.Thm54.PreZComputeCensus
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.RedTeam.Batch742

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## (A) Joint agreement -/

/-- Both chips' traces agree on every round-0 column. -/
def PreZAgree2 (Qc Qc' : Fin P.computeChip.rap.w → F[X]) (Qm Qm' : Fin P.memoryChip.rap.w → F[X]) :
    Prop :=
  PreZAgreeOn (compCC P) Qc Qc' ∧ PreZAgreeOn (memCC P) Qm Qm'

/-- A function of both traces is jointly pre-`z`. -/
def PreZReads2 {β : Sort*}
    (f : (Fin P.computeChip.rap.w → F[X]) → (Fin P.memoryChip.rap.w → F[X]) → β) : Prop :=
  ∀ Qc Qc' Qm Qm', PreZAgree2 P Qc Qc' Qm Qm' → f Qc Qm = f Qc' Qm'

/-! ## (B) `reqTgt` and the route-B pair event, on both chips -/

/-- **Route B's target map is pre-`z` on both chips** at every jointly pre-`z` target builder. -/
theorem reqTgt_preZReads_both
    (Tb : (Fin P.computeChip.rap.w → F[X]) → (Fin P.memoryChip.rap.w → F[X]) →
      MState → ℕ → Noun) (hTb : PreZReads2 P Tb) :
    PreZReads2 P (fun Qc Qm => reqTgt P Qm (Tb Qc Qm)) := by
  intro Qc Qc' Qm Qm' h
  show reqTgt P Qm (Tb Qc Qm) = reqTgt P Qm' (Tb Qc' Qm')
  rw [hTb Qc Qc' Qm Qm' h, reqTgt_congr P h.2]

/-- The route-B pair event at a jointly pre-`z` builder is pre-`z` on both chips. -/
theorem reqPairEvent_preZReads_both (q Λ : ℕ)
    (Tb : (Fin P.computeChip.rap.w → F[X]) → (Fin P.memoryChip.rap.w → F[X]) →
      MState → ℕ → Noun) (hTb : PreZReads2 P Tb) :
    PreZReads2 P (fun Qc Qm => reqPairEvent (K := K) P q Λ Qm (Tb Qc Qm)) := by
  intro Qc Qc' Qm Qm' h
  show reqPairEvent P q Λ Qm (Tb Qc Qm) = reqPairEvent P q Λ Qm' (Tb Qc' Qm')
  rw [hTb Qc Qc' Qm Qm' h]
  exact reqPairEvent_preZReads P q Λ _ Qm Qm' h.2

/-! ## (C) The served-decomposition targets -/

/-- The memory base environments of two `memCC`-agreeing traces agree on the pre-`z` decoder's
columns `0, 1, 2, 180, 181`. -/
theorem memoryBaseEnv_preZMemCols {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hag : PreZAgreeOn (memCC P) Qm Qm') :
    ∀ i, ∀ c ∈ preZMemCols, (P.memoryBaseEnv Qm i).trace c = (P.memoryBaseEnv Qm' i).trace c := by
  intro i c hc
  have hr : memoryColRound c = 0 := by
    simp only [preZMemCols, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide
  exact preEnv_trace_congr P hag i c hr

/-- **The `reqIdx`-indexed served-noun lookup** at the package's committed memory rows. -/
def servedNoun (q kroots : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) : MState → ℕ → Noun :=
  servedNounOfEnvs K q kroots (P.memoryBaseEnv Qm) P.optimized.family.problem.cfg.memRows_pos

theorem servedNoun_preZReads (q kroots : ℕ) :
    PreZReadsFnOn (memCC P) (servedNoun P q kroots) := fun _ _ hag =>
  servedNounOfEnvs_congr K q kroots (memoryBaseEnv_preZMemCols P hag) _

/-- The round-0 compute data route B may read, per row: structure, decoded state, slot
exponents. -/
abbrev ComputeView (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :=
  (Fin P.optimized.family.problem.cfg.compRows → PreZComputeRow F) ×
    (Fin P.optimized.family.problem.cfg.compRows → ComputeTable.State) ×
    (Fin P.optimized.family.problem.cfg.compRows → Fin 3 → ℕ)

/-- The round-0 compute view of a committed trace. -/
def computeView (Qc : Fin P.computeChip.rap.w → F[X]) : ComputeView P :=
  (preZComputeStructure P Qc,
    fun i => computeStateOf (decodeSource (rowEnv P Qc i)),
    fun i j => expOf P Qc i j)

theorem computeView_preZReads : PreZReadsFnOn (compCC P) (computeView P) := by
  intro Qc Qc' hag
  have h1 := preZComputeStructure_preZReads P Qc Qc' hag
  have h2 : (fun i => computeStateOf (decodeSource (rowEnv P Qc i))) =
      fun i => computeStateOf (decodeSource (rowEnv P Qc' i)) :=
    funext fun i => computeState_preZReads P i Qc Qc' hag
  have h3 : (fun i j => expOf P Qc i j) = fun i j => expOf P Qc' i j :=
    funext fun i => funext fun j => expOf_preZReads P i j Qc Qc' hag
  simp only [computeView, h1, h2, h3]

/-- **A served-decomposition target**: an arbitrary assembly rule `G` applied to the round-0
compute view and the served lookup. -/
def servedDecompTgt (G : ComputeView P → (MState → ℕ → Noun) → MState → ℕ → Noun)
    (q kroots : ℕ) (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    MState → ℕ → Noun :=
  G (computeView P Qc) (servedNoun P q kroots Qm)

/-- **Every served-decomposition target is pre-`z` on both chips.** -/
theorem servedDecompTgt_preZReads_both (G : ComputeView P → (MState → ℕ → Noun) → MState → ℕ → Noun)
    (q kroots : ℕ) : PreZReads2 P (servedDecompTgt P G q kroots) := by
  intro Qc Qc' Qm Qm' h
  show G (computeView P Qc) (servedNoun P q kroots Qm) =
    G (computeView P Qc') (servedNoun P q kroots Qm')
  rw [computeView_preZReads P Qc Qc' h.1, servedNoun_preZReads P q kroots Qm Qm' h.2]

/-- **`reqTgt` at a served-decomposition target is pre-`z` on both chips.** -/
theorem reqTgt_servedDecomp_preZReads_both
    (G : ComputeView P → (MState → ℕ → Noun) → MState → ℕ → Noun) (q kroots : ℕ) :
    PreZReads2 P (fun Qc Qm => reqTgt P Qm (servedDecompTgt P G q kroots Qc Qm)) :=
  reqTgt_preZReads_both P _ (servedDecompTgt_preZReads_both P G q kroots)

/-- The route-B pair event at a served-decomposition target is pre-`z` on both chips. -/
theorem reqPairEvent_servedDecomp_preZReads_both
    (G : ComputeView P → (MState → ℕ → Noun) → MState → ℕ → Noun) (q kroots Λ : ℕ) :
    PreZReads2 P (fun Qc Qm =>
      reqPairEvent (K := K) P q Λ Qm (servedDecompTgt P G q kroots Qc Qm)) :=
  reqPairEvent_preZReads_both P q Λ _ (servedDecompTgt_preZReads_both P G q kroots)

/-! ## (D) Positive controls -/

/-- A round-1 compute read is not pre-`z`. -/
theorem compute_role0_not_preZ :
    ¬ PreZReadsFnOn (compCC P)
      (fun Qc : Fin P.computeChip.rap.w → F[X] =>
        (P.computeBaseEnv Qc ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).trace 13) :=
  not_preZReads_role0 P

/-- A target builder reading a round-1 compute column is not jointly pre-`z`. -/
theorem role0_builder_not_preZ :
    ¬ PreZReads2 P (fun Qc (_ : Fin P.memoryChip.rap.w → F[X]) =>
        (P.computeBaseEnv Qc ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).trace 13) := by
  intro h
  apply not_preZReads_role0 P
  intro Qc Qc' hag
  exact h Qc Qc' (fun _ => 0) (fun _ => 0) ⟨hag, fun _ _ => rfl⟩

end

end Nock.RedTeam.Batch796

#print axioms Nock.NockVMROM.Thm54.PreZComputeCore.compColRound_eq_zero_iff
#print axioms Nock.NockVMROM.Thm54.PreZComputeCore.preZComputeRows_preZReadsC
#print axioms Nock.NockVMROM.Thm54.PreZComputeCore.not_preZReadsC_role0
#print axioms Nock.NockVMROM.Thm54.PreZComputeCore.sourceEnv_trace_congr
#print axioms Nock.NockVMROM.Thm54.PreZComputeCore.Served.servedNounOfEnvs_congr
#print axioms Nock.NockVMROM.Thm54.PreZComputeCensus.computeView_preZ_iff
#print axioms Nock.NockVMROM.Thm54.PreZComputeCensus.preZAgreeOn_compCC_iff
#print axioms Nock.NockVMROM.Thm54.PreZComputeCensus.preZComputeStructure_preZReads
#print axioms Nock.NockVMROM.Thm54.PreZComputeCensus.computeState_preZReads
#print axioms Nock.NockVMROM.Thm54.PreZComputeCensus.activeMask_preZReads
#print axioms Nock.NockVMROM.Thm54.PreZComputeCensus.expOf_preZReads
#print axioms Nock.NockVMROM.Thm54.PreZComputeCensus.not_preZReads_role0
#print axioms Nock.RedTeam.Batch796.reqTgt_preZReads_both
#print axioms Nock.RedTeam.Batch796.reqTgt_servedDecomp_preZReads_both
#print axioms Nock.RedTeam.Batch796.reqPairEvent_servedDecomp_preZReads_both
#print axioms Nock.RedTeam.Batch796.role0_builder_not_preZ
