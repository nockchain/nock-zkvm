/-
  Nock/RedTeam/Batch842Thm54WalkGateBridge.lean

  Delivered:
  * `decodeSource_trace_lt11` / `computeStateOf_decode_congr`: the decoded state reads base
    columns `0..10` only;
  * `rowEnvAt_familyQc_baseTrace`: the family row env at `familyQc P c Qc` has the constant-chip
    row env's base trace, at every `c` (no hypothesis);
  * **`lblCAt_state_eq_typed`**: `(lblCAt P Qc c i).1 = (typedComputeLabel P Qc i).1`, every `c`;
  * **`foC_eq_foRows_typed`**: `foC P Qc c = foRows computeFanout (typedComputeRows P Qc)` on
    `1..N`, every `c`;
  * **`tiles_of_sfCompute`, `queued_of_validCompute`** (and `tiles_queued_of_tracesWalkHyps`):
    the two `TracesWalkHyps` compute fields at ANY `c` give `Batch771.Tiles` / `Queued` of the
    typed rows — exactly the two walk-gate premises of `expOf_requestList`;
  * **Reach : this one
    deployed wrapper reaches `Vmem` / `interV`** through `tracesWalkHyps_compute → deployed_tiling →
    count_eq_ln_last → Batch459.isLast_source_last → Batch457.masks_at_row_at → computeRealization`
    (the honest canonical satisfaction proof).  The bridge theorems above are clean; a clean
    deployed discharge needs `deployed_tiling` / `deployed_bfsValid` restated over the family mask
    twin `FamilyIOChain.masks_at_row_at` (named, not built).

  Only the state component is bridged: the full labels differ off the state (the family decoder
  reads the tuple's coins), and the fanout reads the state only.  Not touched: `expOf_requestList`'s
  own `hsat` is the CONSTANT-chip satisfaction; at the family acceptance object (F) its row-arity
  and prefix uses need the family twins (`FamilyIOChain.rowArity_eq_arity_at`,
  `expCol_eq_prefixExp_at`) — that is a separate cell, not this bridge.
-/
import Nock.RedTeam.Batch773Thm54ExpOfRequestList
import Nock.RedTeam.Batch489Thm54FoOfEqFoW
import Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch842

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open scoped Polynomial

noncomputable section

section Decode

variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq K]

/-- The decoded source columns `0..10` are the base selector columns. -/
theorem decodeSource_trace_lt11 (env : CorrectedFinalTypedEnv F K) (k : ℕ) (hk : k < 11) :
    (decodeSource env).trace k = algebraMap F K (env.baseTrace ⟨k, by omega⟩) := by
  rw [← source_trace_base env k (by omega)]
  simp [decodeSource, Env.ofSubst, computeSubst, computeTraceSubst, hk, Expr.eval]

/-- The decoded state reads the base trace only. -/
theorem computeStateOf_decode_congr {env env' : CorrectedFinalTypedEnv F K}
    (h : env.baseTrace = env'.baseTrace) :
    computeStateOf (decodeSource env) = computeStateOf (decodeSource env') := by
  have hk : ∀ k, (hk : k < 11) → (decodeSource env).trace k = (decodeSource env').trace k := by
    intro k hk
    rw [decodeSource_trace_lt11 env k hk, decodeSource_trace_lt11 env' k hk, h]
  unfold computeStateOf
  rw [hk 1 (by norm_num), hk 2 (by norm_num), hk 3 (by norm_num), hk 4 (by norm_num),
    hk 5 (by norm_num), hk 6 (by norm_num), hk 7 (by norm_num), hk 8 (by norm_num),
    hk 9 (by norm_num), hk 10 (by norm_num)]

end Decode

section Bridge

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X])

/-- The family row env at the reindexed constant-chip trace has the constant-chip row env's base
trace (only the challenge / public maps differ), at every tuple. -/
theorem rowEnvAt_familyQc_baseTrace (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    (rowEnvAt P c (familyQc P c Qc) i).baseTrace = (rowEnv P Qc i).baseTrace := by
  funext k
  have hw := computeChipAt_width P c
  simp only [rowEnvAt, rowEnv, gatherCorrectedFinalTypedEnv, envOfTrace, familyQc]
  by_cases h : (k : ℕ) < P.computeChip.rap.w
  · have h' : (k : ℕ) < (P.computeChipAt c).rap.w := by rw [hw]; exact h
    rw [dif_pos h, dif_pos h']
    rfl
  · have h' : ¬ (k : ℕ) < (P.computeChipAt c).rap.w := by rw [hw]; exact h
    rw [dif_neg h, dif_neg h']

/-- **The state half of `lblC = typed`**: the family decoded state at any tuple `c` is the typed
(constant-chip) decoded state. -/
theorem lblCAt_state_eq_typed (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    (lblCAt P Qc c i).1 = (typedComputeLabel P Qc i).1 := by
  simp only [lblCAt, typedComputeLabel]
  exact computeStateOf_decode_congr (rowEnvAt_familyQc_baseTrace P Qc c i)

/-- **`foC = computeFanout ∘ typed`** on the rows `1..N`, at every tuple. -/
theorem foC_eq_foRows_typed (c : OptimizedProductionChallengeTuple K F) (i : ℕ) (h1 : 1 ≤ i)
    (hi : i ≤ P.optimized.family.problem.cfg.compRows) :
    foC P Qc c i = Batch771.foRows computeFanout (typedComputeRows P Qc) i := by
  have hlt : i - 1 < P.optimized.family.problem.cfg.compRows := by omega
  have hget : (typedComputeRows P Qc)[i - 1]? =
      some (typedComputeLabel P Qc ⟨i - 1, hlt⟩) := by
    simp [typedComputeRows, hlt]
  unfold foC lblC Batch771.foRows
  rw [dif_pos hlt, hget, lblCAt_state_eq_typed P Qc c ⟨i - 1, hlt⟩]
  simp [computeFanout]

theorem Sf_foC_eq_foRows (c : OptimizedProductionChallengeTuple K F) (m : ℕ)
    (hm : m ≤ P.optimized.family.problem.cfg.compRows) :
    Sf (foC P Qc c) m = Sf (Batch771.foRows computeFanout (typedComputeRows P Qc)) m := by
  refine Finset.sum_congr rfl fun i hi => ?_
  have hii := Finset.mem_Icc.mp hi
  exact foC_eq_foRows_typed P Qc c i hii.1 (le_trans hii.2 hm)

/-- **Walk-gate bridge, tiling.**  The `TracesWalkHyps` compute tiling at any `c` is `Tiles` of the
typed rows. -/
theorem tiles_of_sfCompute (c : OptimizedProductionChallengeTuple K F)
    (hsf : Sf (foC P Qc c) P.optimized.family.problem.cfg.compRows + 1 =
      P.optimized.family.problem.cfg.compRows) :
    Batch771.Tiles computeFanout 1 (typedComputeRows P Qc) := by
  have hlen := typedComputeRows_length P Qc
  have hS : Sf (foC P Qc c) P.optimized.family.problem.cfg.compRows =
      ((typedComputeRows P Qc).map computeFanout).sum := by
    rw [Sf_foC_eq_foRows P Qc c _ le_rfl,
      Batch771.Sf_foRows computeFanout (typedComputeRows P Qc) _ (by rw [hlen]),
      List.take_of_length_le (by rw [hlen])]
  unfold Batch771.Tiles
  rw [hlen]
  omega

/-- **Walk-gate bridge, queue validity.**  The `TracesWalkHyps` compute `BFSValid` at any `c` is
`Queued` of the typed rows. -/
theorem queued_of_validCompute (c : OptimizedProductionChallengeTuple K F)
    (hv : BFSValid (foC P Qc c) P.optimized.family.problem.cfg.compRows) :
    Batch771.Queued computeFanout 1 (typedComputeRows P Qc) := by
  have hlen := typedComputeRows_length P Qc
  intro i hi
  rw [hlen] at hi
  have h := hv (i + 1) (by omega) (by omega)
  rw [Nat.add_sub_cancel, Sf_foC_eq_foRows P Qc c i (by omega),
    Batch771.Sf_foRows computeFanout (typedComputeRows P Qc) i (by rw [hlen]; omega)] at h
  omega

/-- Both walk-gate premises of `expOf_requestList` from `TracesWalkHyps` at any tuple. -/
theorem tiles_queued_of_tracesWalkHyps (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) (h : TracesWalkHyps P Qc Qm c) :
    Batch771.Tiles computeFanout 1 (typedComputeRows P Qc) ∧
      Batch771.Queued computeFanout 1 (typedComputeRows P Qc) :=
  ⟨tiles_of_sfCompute P Qc c h.sfCompute, queued_of_validCompute P Qc c h.validCompute⟩

/-- **Deployed form.**  Premises
`hax`, `hbasis`, `hwidth` are `of_package`'s. -/
theorem tiles_queued_of_deployed (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm) :
    Batch771.Tiles computeFanout 1 (typedComputeRows P Qc) ∧
      Batch771.Queued computeFanout 1 (typedComputeRows P Qc) := by
  have hcomp := P.optimizedFailureEvent_good_components Qc Qm c hgood
  have htileC : c.1 ∉ P.computeTilingEventOf Qc := hcomp.2.2.2.2.2.1
  have hC : c.1 ∉ WalkTilingEvents.computeTilingEvent
      (Batch459.foW P c (familyQc P c Qc) hsat) (rows P) := by
    rwa [← Batch489.computeTilingEventOf_eq_foW P c Qc hsat]
  obtain ⟨hsf, hv⟩ :=
    WalkQueueDeployed.tracesWalkHyps_compute P c Qc hsat hax hbasis hwidth hC
  exact ⟨tiles_of_sfCompute P Qc c hsf, queued_of_validCompute P Qc c hv⟩

end Bridge

end

end Nock.RedTeam.Batch842

#print axioms Nock.RedTeam.Batch842.lblCAt_state_eq_typed
#print axioms Nock.RedTeam.Batch842.foC_eq_foRows_typed
#print axioms Nock.RedTeam.Batch842.tiles_queued_of_tracesWalkHyps
#print axioms Nock.RedTeam.Batch842.tiles_queued_of_deployed
