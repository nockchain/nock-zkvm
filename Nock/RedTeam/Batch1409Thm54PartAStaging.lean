import Nock.NockVMROM.Thm54.P8Core.RepartitionedStaging
import Nock.NockVMROM.Thm54.DeployedStaging
import Nock.NockVMROM.Thm54.ComputeWalkLabel
import Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
import Nock.RedTeam.Batch1408Thm54PartAR1
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1409Thm54PartAStaging.lean

  **The compiled facts and the
  ported locality receipts for `P8Core/RepartitionedStaging.lean`.

  * §1 class invariance at the repartitioned schedule (`compute_no_class_change`,
    `compute_sources_count = 94`, `memory_no_class_change`(`_repoint`), `slot3_readers`,
    `slot0_readers`), with the control `compute_noRetarget_changes = ["ep2_1"]`: without
    un-hosting, the walk-count init gate changes class.
  * §2 the read-set congruences, the `rfl` ties to the production package, the round checks, and
    the composed `ReadsOn` receipts at the 12-coin schedule for summands 9 and 10 (the latter at
    `αW`, index 11); summands 2 (memory half) and 4 are env-local with their round checks.
  * §3 the compute read sets for summands 2, 5, 8 (`s2_compute_local_new`, `labels_local_new`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace Nock.RedTeam.Batch1409

open Nock.NockVMROM.Thm54.RepartitionedStaging

/-! ## 1. Class invariance of the compute and memory gates (carried over from `Schedule.lean`) -/
section Sched
open Nock Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.DeployedStaging
  Nock.NockVMROM.Thm54.Staging Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal

/-- Coarse class: 0 base, 1 identity over precommitted (coin, no later column), 2 coin-free over a
later column, 3 commit-after-coin. -/
def coarse (colRound chalRound : ℕ → ℕ) (cols chals : List ℕ) : ℕ :=
  if gateReadsLaterColumn colRound chalRound cols chals then (if chals = [] then 2 else 3)
  else (if chals = [] then 0 else 1)

def hostCols : List ℕ := [6, 7, 9, 10, 18, 19, 27, 28].flatMap fun r => [13 + 3*r, 14 + 3*r, 15 + 3*r]
def W0 : List ℕ := [303, 304, 305]
def W1 : List ℕ := [306, 307, 308]
def swapHosts (w : List ℕ) (cols : List ℕ) : List ℕ := cols.filter (fun c => c ∉ hostCols) ++ w
def retarget (tag : ℕ) (cols : List ℕ) : List ℕ :=
  match tag with
  | 1 => swapHosts W0 cols | 2 => swapHosts W1 cols | 3 => cols ++ W0 ++ W1 | _ => cols

/-- All compute typed sources with their retarget tag. -/
def computeSources : List (String × ℕ × CorrectedFinalTypedExpr) :=
  ((List.finRange 82).map fun i => (s!"core{i.val}", (if i.val = 76 ∨ i.val = 77 then 1 else 0), correctedCoreSource i))
  ++ ((List.finRange 3).map fun j => (s!"aux{j.val}", (if j.val = 0 then 1 else if j.val = 1 then 3 else 0), correctedAuxSource j))
  ++ (correctedEndpoint2.zipIdx.map fun (t, k) => (s!"ep2_{k}", (if k = 1 then 1 else if k = 2 then 2 else 0), t))
  ++ (correctedEndpoint4.map fun t => ("ep4", 3, t))
  ++ (formRLamPins.map fun t => ("lamPin", 0, t))

def oldC (t : CorrectedFinalTypedExpr) : ℕ := coarse computeColRound computeSlotRound (typedColsC t) (typedSlots t)
def newC (tag : ℕ) (t : CorrectedFinalTypedExpr) : ℕ :=
  coarse newComputeColRound newComputeSlotRound (retarget tag (typedColsC t)) (typedSlots t)
/-- Without the retarget (un-hosting refused): which gates would change class. -/
def newCnoRetarget (t : CorrectedFinalTypedExpr) : ℕ :=
  coarse newComputeColRound newComputeSlotRound (typedColsC t) (typedSlots t)

def computeChanged : List String :=
  computeSources.filterMap fun (n, tag, t) => if oldC t ≠ newC tag t then some n else none
def computeChangedNoRetarget : List String :=
  computeSources.filterMap fun (n, _, t) => if oldC t ≠ newCnoRetarget t then some n else none

/-- **Zero illegal compute reads**: every one of the 94 typed sources keeps its coarse class. -/
theorem compute_no_class_change : computeChanged = [] := by decide +kernel
theorem compute_sources_count : computeSources.length = 94 := by decide
/-- Negative control: without un-hosting, ep2_1 (walkCount init) becomes an identity over B1 at αC. -/
theorem compute_noRetarget_changes : computeChangedNoRetarget = ["ep2_1"] := by decide +kernel

/-! Memory: the 50 mixed sources (`memoryMixedReads` = the deployed gates, `memory_mixed_reads`). -/
def oldM (p : List ℕ × List ℕ) : ℕ := coarse memoryColRound memorySlotRound p.1 p.2
def newM (p : List ℕ × List ℕ) : ℕ := coarse newMemoryColRound newMemorySlotRound p.1 p.2
/-- Variant (α) as signed: the six walk gates (indices 27..32) read slot 9 instead of 3. -/
def retargetSlot (i : ℕ) (p : List ℕ × List ℕ) : List ℕ × List ℕ :=
  if 27 ≤ i ∧ i ≤ 32 then (p.1, p.2.map fun q => if q = 3 then 9 else q) else p
theorem memory_no_class_change :
    (memoryMixedReads.zipIdx.filter fun (p, i) => oldM p ≠ newM (retargetSlot i p)) = [] := by decide +kernel
theorem memory_no_class_change_repoint :
    (memoryMixedReads.filter fun p => oldM p ≠ newM p) = [] := by decide +kernel
/-- Only the six walk gates read memory slot 3. -/
theorem slot3_readers :
    (memoryMixedReads.zipIdx.filterMap fun (p, i) => if 3 ∈ p.2 then some i else none) = [27, 28, 29, 30, 31, 32] := by
  decide +kernel
/-- Only compute sources core50, core58, core65, core78, core79, core80 read slot 0 (the timestamp αM). -/
def slot0Readers : List String := computeSources.filterMap fun (n, _, t) => if 0 ∈ typedSlots t then some n else none
theorem slot0_readers : slot0Readers = ["core50", "core58", "core65", "core78", "core79", "core80"] := by decide +kernel

/-! Negative control for summand 2 at deployedChronology: the memory response record reads role 26 (ts),
which is round 2, while IOγ is sampled after round 1. Under the new map every read is ≤ 1. -/
def sched2RecordRoles : List ℕ := [19, 20, 21, 22, 23, 24, 25, 26, 57, 39]
theorem summand2_record_not_local_deployed :
    ¬ (∀ r ∈ sched2RecordRoles, memoryRoleRound r ≤ (deployedChronology.sampledAfter ⟨4, by decide⟩ : ℕ)) := by decide
theorem summand2_record_local_new :
    ∀ r ∈ sched2RecordRoles, newMemoryRoleRound r ≤ (repartitionedChronology.sampledAfter ⟨4, by decide⟩ : ℕ) := by decide

end Sched

/-! ## 2. The bridge receipts -/
section Recs
open Nock Nock.Reified Nock.Framework Nock.NockVMROM.Thm54
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage Nock.NockVMROM.Thm54.DeployedStaging
  Nock.NockVMROM.Thm54.RoundFibred Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
  Nock.NockVMROM.Thm54.WalkTilingEvents Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
  Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Polynomial Nock.Walk
noncomputable section

/-! ## 1. Read-set congruences of the production record / label functions (pointwise). -/

section Cong
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Memory record: roles 19..26, 57; base 181. -/
def recordRoles : List ℕ := [19, 20, 21, 22, 23, 24, 25, 26, 57]
theorem rowRecord_congr' {eK eK' : Env K} {eF eF' : Env F}
    (hK : ∀ r ∈ recordRoles, eK.trace r = eK'.trace r) (hF : eF.trace 181 = eF'.trace 181) :
    OptimizedMemoryHostileAccumulator.rowRecord eK eF = OptimizedMemoryHostileAccumulator.rowRecord eK' eF' := by
  funext c
  unfold OptimizedMemoryHostileAccumulator.rowRecord
  split_ifs with h1 h2
  · have : (c : ℕ) < 8 := h1
    exact hK _ (by unfold recordRoles; interval_cases (c : ℕ) <;> simp)
  · exact hK 57 (by simp [recordRoles])
  · rw [hF]

/-- Memory response terms read the record and `ver` (role 39); `rowResponses` drops the denominator
(role 37, block B2). -/
theorem rowResponses_congr' [DecidableEq K] {eK eK' : Env K} {eF eF' : Env F}
    (hK : ∀ r ∈ recordRoles ++ [39], eK.trace r = eK'.trace r) (hF : eF.trace 181 = eF'.trace 181) :
    OptimizedMemoryHostileAccumulator.rowResponses eK eF = OptimizedMemoryHostileAccumulator.rowResponses eK' eF' := by
  have hr := rowRecord_congr' (fun r hr => hK r (List.mem_append_left _ hr)) hF
  have h39 : eK.trace 39 = eK'.trace 39 := hK 39 (by simp)
  simp only [OptimizedMemoryHostileAccumulator.rowResponses, OptimizedMemoryHostileAccumulator.rowResponseTerms,
    h39, hr]
  split_ifs <;> rfl

/-- Label / child vectors of the memory walk (summands 9, 10): roles 0..14, 45, 46; base 0, 1, 2. -/
def labelRoles : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 45, 46]
def stateBase : List ℕ := [0, 1, 2]

theorem memRowStateOf_congr' [DecidableEq F] {eF eF' : Env F} (hF : ∀ b ∈ stateBase, eF.trace b = eF'.trace b) :
    memRowStateOf eF = memRowStateOf eF' := by
  unfold memRowStateOf
  rw [hF 0 (by simp [stateBase]), hF 1 (by simp [stateBase]), hF 2 (by simp [stateBase])]

theorem memRowLabelVec_congr' [DecidableEq F] {eK eK' : Env K} {eF eF' : Env F}
    (hK : ∀ r ∈ labelRoles, eK.trace r = eK'.trace r) (hF : ∀ b ∈ stateBase, eF.trace b = eF'.trace b) :
    memRowLabelVec eK eF = memRowLabelVec eK' eF' := by
  funext k
  fin_cases k <;> simp only [memRowLabelVec, memRowStateOf_congr' hF] <;>
    exact hK _ (by simp [labelRoles])

theorem memRowChildVec_congr' {eK eK' : Env K} (hK : ∀ r ∈ labelRoles, eK.trace r = eK'.trace r) (j : Fin 2) :
    memRowChildVec eK j = memRowChildVec eK' j := by
  funext k
  fin_cases k <;> fin_cases j <;> simp only [memRowChildVec] <;> exact hK _ (by simp [labelRoles])

variable {M : ℕ} [DecidableEq F]

theorem VCvfo_congr {eK eK' : Fin M → Env K} {eF eF' : Fin M → Env F}
    (hK : ∀ i, ∀ r ∈ labelRoles, (eK i).trace r = (eK' i).trace r)
    (hF : ∀ i, ∀ b ∈ stateBase, (eF i).trace b = (eF' i).trace b) :
    committedMemoryV eK eF = committedMemoryV eK' eF' ∧ committedMemoryCv eK = committedMemoryCv eK' ∧
      foOfMem eF = foOfMem eF' := by
  refine ⟨?_, ?_, ?_⟩
  · funext i; unfold committedMemoryV; split_ifs with h
    · exact memRowLabelVec_congr' (hK _) (hF _)
    · rfl
  · funext i l; unfold committedMemoryCv; split_ifs
    · exact memRowChildVec_congr' (hK _) _
    · rfl
    · rfl
  · funext i; unfold foOfMem; split_ifs with h
    · rw [memRowStateOf_congr' (hF _)]
    · rfl

/-- **Summand 9 is env-local on `labelRoles` / `stateBase`.** -/
theorem summand9_envLocal [Fintype K] [DecidableEq K] (kroots : ℕ) :
    EnvLocal labelRoles stateBase (fun eK eF => memoryPrefixGammaEventOfEnvs (K := K) (F := F) (M := M) eK eF kroots) := by
  intro eK eK' eF eF' hK hF
  obtain ⟨h1, h2, h3⟩ := VCvfo_congr hK hF
  dsimp only; unfold memoryPrefixGammaEventOfEnvs; rw [h1, h2, h3]

/-- **Summand 10 is env-local on the same read set.** -/
theorem summand10_envLocal [Fintype K] [DecidableEq K] (kroots : ℕ) :
    EnvLocal labelRoles stateBase (fun eK eF => memoryForestAlphaEventOfEnvs (K := K) (F := F) (M := M) eK eF kroots) := by
  intro eK eK' eF eF' hK hF
  obtain ⟨h1, h2, h3⟩ := VCvfo_congr hK hF
  dsimp only; unfold memoryForestAlphaEventOfEnvs; rw [h1, h2, h3]

/-- Summand 4's inter records, as a function of the env families (`rfl` to the package's below). -/
def interRecordsOfEnvs [DecidableEq K] (eK : Fin M → Env K) (eF : Fin M → Env F) : FiniteIO.PreChallengeRecords K 10 :=
  ⟨(List.ofFn fun i => if (eF i).trace 2 = 1 then [OptimizedMemoryHostileAccumulator.rowRecord (eK i) (eF i)] else []).flatten,
   (List.ofFn fun i => if (eF i).trace 3 = 1 then [OptimizedMemoryHostileAccumulator.rowRecord (eK i) (eF i)] else []).flatten⟩

def summand4OfEnvs [Fintype K] [DecidableEq K] (eK : Fin M → Env K) (eF : Fin M → Env F) : Finset (K × K) :=
  interFailurePairs (interRecordsOfEnvs eK eF) eK eF

theorem summand4_envLocal [Fintype K] [DecidableEq K] :
    EnvLocal (K := K) (F := F) (M := M) recordRoles [2, 3, 181] summand4OfEnvs := by
  intro eK eK' eF eF' hK hF
  have hr : ∀ i, OptimizedMemoryHostileAccumulator.rowRecord (eK i) (eF i) =
      OptimizedMemoryHostileAccumulator.rowRecord (eK' i) (eF' i) :=
    fun i => rowRecord_congr' (hK i) (hF i 181 (by simp))
  have h2 : ∀ i, (eF i).trace 2 = (eF' i).trace 2 := fun i => hF i 2 (by simp)
  have h3 : ∀ i, (eF i).trace 3 = (eF' i).trace 3 := fun i => hF i 3 (by simp)
  unfold summand4OfEnvs interFailurePairs allRowPoleHitEvent interRecordsOfEnvs
  simp only [hr, h2, h3]

/-- Summand 2's memory half: the response list as a function of the env families. -/
def responsesOfEnvs [DecidableEq K] (eK : Fin M → Env K) (eF : Fin M → Env F) : List (Fin 10 → K) :=
  (List.ofFn fun i => OptimizedMemoryHostileAccumulator.rowResponses (eK i) (eF i)).flatten

theorem summand2mem_envLocal [DecidableEq K] :
    EnvLocal (K := K) (F := F) (M := M) (recordRoles ++ [39]) [181] responsesOfEnvs := by
  intro eK eK' eF eF' hK hF
  unfold responsesOfEnvs
  congr 1; congr 1; funext i
  exact rowResponses_congr' (hK i) (hF i 181 (by simp))

end Cong

/-! ## 2. Ties to the production package (`rfl`). -/

section Ties
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb) (Qm : Fin P.memoryChip.rap.w → F[X])

theorem tie9 : P.memoryPrefixGammaEventOf Qm =
    memoryPrefixGammaEventOfEnvs (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) P.optimized.family.problem.cfg.kMem := rfl
theorem tie10 : P.memoryForestAlphaEventOf Qm =
    memoryForestAlphaEventOfEnvs (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) P.optimized.family.problem.cfg.kMem := rfl
theorem tie4 : interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) =
    summand4OfEnvs (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) := rfl
theorem tie2mem : P.hostileResponses Qm = responsesOfEnvs (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) := rfl
end Ties

/-! ## 3. Rounds: the read sets against the coin's message. Coins in the 12-vector:
  [αC, γ, αM, z, IOγ, IOpole, a, b, c, interPole, λ, αW]. -/

def newSampled : Fin 12 → ℕ := ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1]
def oldSampled : Fin 11 → ℕ := ![1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1]
/-- The 12-vector used by the receipts is the production chronology's. -/
theorem newSampled_eq (j : Fin 12) : newSampled j = (repartitionedChronology.sampledAfter j : ℕ) := by
  fin_cases j <;> rfl
theorem oldSampled_eq (j : Fin 11) : oldSampled j = (deployedChronology.sampledAfter j : ℕ) := by
  fin_cases j <;> rfl
/-- Memory base columns are block 0 on both schedules (memoryColRound c = 0 for c < 6 and c ≥ 180). -/
theorem base_round0 : ∀ b ∈ [0, 1, 2, 3, 181], memoryColRound b = 0 := by decide

-- summand 2 memory half: coin IOγ (4)
theorem s2_new : ∀ r ∈ recordRoles ++ [39], newMemoryRoleRound r ≤ newSampled 4 := by decide
theorem s2_old_NOT : ¬ ∀ r ∈ recordRoles ++ [39], memoryRoleRound r ≤ oldSampled 4 := by decide
theorem s2_old_witness : memoryRoleRound 26 = 2 ∧ oldSampled 4 = 1 := by decide
-- summand 4: coins IOγ (4), interPole (9)
theorem s4_new : ∀ r ∈ recordRoles, newMemoryRoleRound r ≤ newSampled 4 ∧ newMemoryRoleRound r ≤ newSampled 9 := by decide
theorem s4_old_NOT : ¬ ∀ r ∈ recordRoles, memoryRoleRound r ≤ oldSampled 9 := by decide
-- summand 9: coin γ (1)
theorem s9_new : ∀ r ∈ labelRoles, newMemoryRoleRound r ≤ newSampled 1 := by decide
theorem s9_old_NOT : ¬ ∀ r ∈ labelRoles, memoryRoleRound r ≤ oldSampled 1 := by decide
-- summand 10: coin αW (11) under (α); the C2 control: the walk left at αM (2) after the repartition
theorem s10_new_aW : ∀ r ∈ labelRoles, newMemoryRoleRound r ≤ newSampled 11 := by decide
theorem s10_repartition_at_aM_NOT : ¬ ∀ r ∈ labelRoles, newMemoryRoleRound r ≤ newSampled 2 := by decide
theorem s10_old_NOT : ¬ ∀ r ∈ labelRoles, memoryRoleRound r ≤ oldSampled 2 := by decide

/-! ## 4. Negative control as a cylinder: a bad set reading its own coin's column (the deployed summand-2
shape: ts = role 26 committed in block 2, IOγ sampled after block 1). -/
section NC
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- One memory row, one coin (IOγ); the adaptive prover sets role 26 := the coin, which
`K_reads` allows because `memoryRoleRound 26 = 2 > 1 = sampledAfter`. -/
def ncAdaptive : AdaptiveEnvs 1 1 K K where
  roleRound := memoryRoleRound
  baseRound := fun _ => 0
  sampledAfter := fun _ => oldSampled 4
  envK := fun χ _ => ⟨fun r => if r = 26 then χ 0 else 0, fun _ => 0, fun _ => 0, fun _ => 0⟩
  envF := fun _ _ => ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩
  K_reads := by
    intro r χ χ' h i
    by_cases hr : r = 26
    · subst hr; simp only [if_true]; exact h 0 (by decide)
    · simp [hr]
  F_reads := by intro b χ χ' _ i; rfl

/-- The record's ts slot as the bad set ("the coin equals the committed ts"). -/
def ncBad (eK : Fin 1 → Env K) (_ : Fin 1 → Env K) (_ : Fin 1 → K) : Finset K := {(eK 0).trace 26}

theorem nc_envLocal (χ : Fin 1 → K) : EnvLocal (M := 1) [26] [] (fun eK eF => ncBad eK eF χ) := by
  intro eK eK' eF eF' hK _; simp [ncBad, hK 0 26 (by simp)]

theorem nc_not_readsOn (h01 : (0 : K) ≠ 1) :
    ¬ ReadsOn (C := K) (priorCoords (ncAdaptive (K := K)).sampledAfter 0)
      (fun χ => ncBad ((ncAdaptive (K := K)).envK χ) ((ncAdaptive (K := K)).envF χ) χ) := by
  intro h
  have := h (fun _ => 0) (fun _ => 1) (by
    intro j hj; simp only [priorCoords, Finset.mem_filter] at hj; exact absurd hj.2 (lt_irrefl _))
  simp [ncBad, ncAdaptive] at this

theorem nc_cylinder_full :
    cylinder (0 : Fin 1) (fun χ => ncBad ((ncAdaptive (K := K)).envK χ) ((ncAdaptive (K := K)).envF χ) χ)
      = Finset.univ := by
  ext χ; simp [cylinder, ncBad, ncAdaptive]

end NC


/-! ## 5. Composed `ReadsOn` receipts at the 12-coin repartitioned schedule (any adaptive prover). -/
section Composed
variable {M : ℕ} {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F] [Fintype K] [DecidableEq K]

/-- Summand 9's bad set for coin `γ` (index 1): the forest prefix bad γs of the committed vectors. -/
def bad9 (kroots : ℕ) (eK : Fin M → Env K) (eF : Fin M → Env F) (_ : Fin 12 → K) : Finset K :=
  forestPrefixBadGammas (committedMemoryV eK eF) (committedMemoryCv eK) (foOfMem eF) kroots M

/-- Summand 10's bad set for coin `αW` (index 11) under (α): the forest prefix bad αs at the sampled `γ`
(index 1), gated on the tiling as in `memoryForestAlphaEventConsumed`. -/
def bad10W (kroots : ℕ) (eK : Fin M → Env K) (eF : Fin M → Env F) (χ : Fin 12 → K) : Finset K :=
  if kroots + Sf (foOfMem eF) M = M then
    walkForestPrefixAlphaEvent (curOfMem (committedMemoryV eK eF) (χ 1)) (chldOfMem (committedMemoryCv eK) (χ 1))
      (foOfMem eF) kroots M
  else ∅

theorem summand9_readsOn (A : AdaptiveEnvs 12 M K F) (hR : A.roleRound = newMemoryRoleRound)
    (hB : ∀ b ∈ stateBase, A.baseRound b = 0) (hS : A.sampledAfter = newSampled) (kroots : ℕ) :
    ReadsOn (C := K) (∅ ∪ priorCoords A.sampledAfter 1)
      (fun χ => bad9 kroots (A.envK χ) (A.envF χ) χ) := by
  refine readsOn_of_envLocal A 1 labelRoles stateBase ∅ (bad9 kroots) ?_ ?_ ?_ ?_
  · intro χ eK eK' eF eF' hK hF
    obtain ⟨h1, h2, h3⟩ := VCvfo_congr hK hF
    simp only [bad9, h1, h2, h3]
  · intro eK eF χ χ' _; rfl
  · intro r hr; rw [hR, hS]; exact s9_new r hr
  · intro b hb; rw [hB b hb]; exact Nat.zero_le _

theorem summand10W_readsOn (A : AdaptiveEnvs 12 M K F) (hR : A.roleRound = newMemoryRoleRound)
    (hB : ∀ b ∈ stateBase, A.baseRound b = 0) (hS : A.sampledAfter = newSampled) (kroots : ℕ) :
    ReadsOn (C := K) ({1} ∪ priorCoords A.sampledAfter 11)
      (fun χ => bad10W kroots (A.envK χ) (A.envF χ) χ) := by
  refine readsOn_of_envLocal A 11 labelRoles stateBase {1} (bad10W kroots) ?_ ?_ ?_ ?_
  · intro χ eK eK' eF eF' hK hF
    obtain ⟨h1, h2, h3⟩ := VCvfo_congr hK hF
    simp only [bad10W, h1, h2, h3]
  · intro eK eF χ χ' h
    have : χ 1 = χ' 1 := h 1 (by simp)
    simp only [bad10W, this]
  · intro r hr; rw [hR, hS]; exact s10_new_aW r hr
  · intro b hb; rw [hB b hb]; exact Nat.zero_le _

/-- The cylinder premise `i ∉ dep` holds for both. -/
theorem summand9_self : (1 : Fin 12) ∉ (∅ ∪ priorCoords newSampled 1) := by decide
theorem summand10W_self : (11 : Fin 12) ∉ ({1} ∪ priorCoords newSampled 11) := by decide
/-- The C2 control in vector form: with the walk left at αM (index 2), `priorCoords` of αM is the
B0-only set, and summand 10's read roles 3, 4, 8, 9, 13, 14 sit in B1 (round 1 > 0). -/
theorem summand10_at_aM_prior : priorCoords newSampled 2 = ∅ := by decide

end Composed

end
end Recs

/-! ## 3. Compute-side read sets for summands 2, 5, 8 -/
section CompH
open Nock Nock.Reified Nock.ComputeTable Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.DeployedStaging
  Nock.NockVMROM.Thm54.ComputeWalkLabel Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal

def exprCols : Nock.Reified.Expr → List ℕ
  | .Var .traceCur i => [i] | .Var .traceNext i => [i] | .Var _ _ => [] | .Const _ => []
  | .Add a b => exprCols a ++ exprCols b | .Sub a b => exprCols a ++ exprCols b | .Mul a b => exprCols a ++ exprCols b
  | .Neg a => exprCols a | .Pow a _ => exprCols a
def states : List State := [.s0,.s1,.s2,.s3,.s4,.s5,.s6,.s7,.s8,.s9,.cons]
/-- Source index `i` (13 ≤ i < 76) is compute 𝕂-role `i − 13`. -/
def computeLabelRoles : List ℕ := (states.flatMap fun st =>
    ((List.finRange 10).flatMap fun k => exprCols (labelCoordAt curReader st k)) ++
    ((List.finRange 3).flatMap fun j => (List.finRange 10).flatMap fun k => exprCols (childCoordAt curReader st j k)))
  |>.filter (fun i => 13 ≤ i ∧ i < 76) |>.map (· - 13)
def newRoleC (r : ℕ) : ℕ := if r ∈ [32, 33, 34, 35] then 2 else if r < 58 then 1 else 2
/-- Summands 5, 8 (coins αC, γ: M2, sampled after B1): every label / child role is B≤1 after un-hosting. -/
theorem labels_local_new : ∀ r ∈ computeLabelRoles, newRoleC r ≤ 1 := by decide +kernel
/-- At the deployed layout the hosted roles are block 2: NOT local (the eight hosts). -/
theorem labels_old_round2 :
    (∀ r ∈ computeLabelRoles, computeRoleRound r = 2 → r ∈ [6, 7, 9, 10, 18, 19, 27, 28]) ∧
    (∀ r ∈ [6, 7, 9, 10, 18, 19, 27, 28], r ∈ computeLabelRoles ∧ computeRoleRound r = 2) := by decide +kernel
/-- Summand 2, compute half: the request-record reads of the three denominator pins core78–80
(their RLC is the record, `HostileRecordLists.rowRecord`'s slots; reading only) minus the
denominators K33–35 themselves. -/
def computeRecordCols : List ℕ := ([78, 79, 80].flatMap fun i =>
    if h : i < 82 then typedColsC (correctedCoreSource ⟨i, h⟩) else []).filter
  (fun c => ¬ (c ≥ 13 + 3*33 ∧ c < 13 + 3*36))
def newColC (c : ℕ) : ℕ :=
  if c < 13 then 0 else if c < 202 then newRoleC ((c - 13) / 3)
  else if c < 296 then 0 else if c < 302 then 1 else if c = 302 then 0 else 2
/-- The scratch copy of the compute round maps is the production `newComputeColRound`. -/
theorem newColC_eq : newColC = newComputeColRound := by
  funext c; simp [newColC, newComputeColRound, newRoleC, newComputeRoleRound]

theorem s2_compute_local_new : ∀ c ∈ computeRecordCols, newColC c ≤ 1 := by decide +kernel
theorem s2_compute_old_NOT : ¬ ∀ c ∈ computeRecordCols, computeColRound c ≤ 1 := by decide +kernel
/-- Which record columns were round 2 at the deployed layout: K6, K7 (hosts), K54 (`ln_prev`), H1. -/
def oldLate : List ℕ := (computeRecordCols.filter fun c => computeColRound c = 2).dedup
theorem oldLate_eq : oldLate = [31, 32, 33, 34, 35, 36, 299, 300, 301, 175, 176, 177] := by decide +kernel
end CompH

/-! ## 4. -/
section FableB0
open Nock.RedTeam.Batch1408
open Polynomial

open Nock Nock.Reified Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0A
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.StrategyOfTracesEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.NockVMROM.Thm54.DeployedStaging
open Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
section Fable
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

theorem builtSkeleton_computeTree_congr
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)
    {Qc Qc' : Fin P.computeChip.rap.w → F[X]} {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (h : AgreeB0 P.optimized Qc Qc' Qm Qm') :
    (OptimizedFailureEventEv.builtSkeletonEv P Qc Qm).computeTree =
      (OptimizedFailureEventEv.builtSkeletonEv P Qc' Qm').computeTree :=
  skeletonEv_computeTree_congr P.stateTagChar h

/-- Summand 13 (root-result pair, coin `z`): B0 only. -/
theorem summand13_B0
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)
    {Qc Qc' : Fin P.computeChip.rap.w → F[X]} {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (h : AgreeB0 P.optimized Qc Qc' Qm Qm') :
    OptimizedFailureEventEv.rootResultEv P Qc Qm = OptimizedFailureEventEv.rootResultEv P Qc' Qm' := by
  have hT := builtSkeleton_computeTree_congr P h
  have hclaim : (OptimizedFailureEventEv.builtSkeletonEv P Qc Qm).publicClaim =
      (OptimizedFailureEventEv.builtSkeletonEv P Qc' Qm').publicClaim := by
    unfold SemanticSkeleton.publicClaim; rw [hT]
  unfold OptimizedFailureEventEv.rootResultEv; rw [hclaim]

/-- Summand 12 (request pair, coin `z`): B0 only (memory base `0,1,2,180,181`; the skeleton's
compute tree). -/
theorem summand12_B0
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)
    {Qc Qc' : Fin P.computeChip.rap.w → F[X]} {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (h : AgreeB0 P.optimized Qc Qc' Qm Qm')
    (hF : ∀ i, ∀ b ∈ PreZComputeCore.Served.preZMemCols,
      (P.memoryBaseEnv Qm i).trace b = (P.memoryBaseEnv Qm' i).trace b) :
    OptimizedFailureEventEv.reqPairEv P Qc Qm = OptimizedFailureEventEv.reqPairEv P Qc' Qm' := by
  have hT := builtSkeleton_computeTree_congr P h
  have hRT : OptimizedFailureEventEv.builtRequestTargets P Qc Qm =
      OptimizedFailureEventEv.builtRequestTargets P Qc' Qm' := by
    have hrows : SemanticStrategy.computeSkeletonRows (OptimizedFailureEventEv.builtSkeletonEv P Qc Qm) =
        SemanticStrategy.computeSkeletonRows (OptimizedFailureEventEv.builtSkeletonEv P Qc' Qm') := by
      unfold SemanticStrategy.computeSkeletonRows; rw [hT]
    unfold OptimizedFailureEventEv.builtRequestTargets
    funext st k
    unfold PreSeedCensus.requestTargets PreSeedCensus.requestList
    rw [hrows]
  have hst : ∀ i, StrategyOfTraces.memoryStateOf (P.memoryBaseEnv Qm i) =
      StrategyOfTraces.memoryStateOf (P.memoryBaseEnv Qm' i) := by
    intro i; unfold StrategyOfTraces.memoryStateOf
    rw [hF i 0 (by decide), hF i 1 (by decide), hF i 2 (by decide)]
  have hlbl : PreSeedCensus.preLblOfEnvs (P.memoryBaseEnv Qm) P.optimized.family.problem.cfg.memRows_pos =
      PreSeedCensus.preLblOfEnvs (P.memoryBaseEnv Qm') P.optimized.family.problem.cfg.memRows_pos := by
    funext j; unfold PreSeedCensus.preLblOfEnvs PreSeedCensus.preStateOfEnvs PreSeedCensus.preAtomOfEnvs
    split_ifs
    · rw [hst, hF _ _ (by simp [PreZComputeCore.Served.preZMemCols])]
    · rw [hst, hF _ _ (by simp [PreZComputeCore.Served.preZMemCols])]
  have hidx : PreSeedCensus.preReqIdxOfEnvs (P.memoryBaseEnv Qm) P.optimized.family.problem.cfg.memRows_pos =
      PreSeedCensus.preReqIdxOfEnvs (P.memoryBaseEnv Qm') P.optimized.family.problem.cfg.memRows_pos := by
    funext j; unfold PreSeedCensus.preReqIdxOfEnvs
    split_ifs
    · rw [hF _ _ (by simp [PreZComputeCore.Served.preZMemCols])]
    · rw [hF _ _ (by simp [PreZComputeCore.Served.preZMemCols])]
  unfold OptimizedFailureEventEv.reqPairEv PreSeedCensus.reqPairEventOfEnvs PreSeedCensus.reqPairsOfEnvs
    PreSeedCensus.preZNounOfEnvs PreSeedCensus.reqTgtOfEnvs PreSeedCensus.preFoOfEnvs
  rw [hlbl, hidx, hRT]

end Fable
end FableB0

end Nock.RedTeam.Batch1409

#print axioms Nock.NockVMROM.Thm54.RepartitionedStaging.M1_eq
#print axioms Nock.NockVMROM.Thm54.RepartitionedStaging.M2_eq
#print axioms Nock.NockVMROM.Thm54.RepartitionedStaging.moved_vs_deployed
#print axioms Nock.NockVMROM.Thm54.RepartitionedStaging.newComputeBlocks
#print axioms Nock.NockVMROM.Thm54.RepartitionedStaging.newMemoryBlocks
#print axioms Nock.NockVMROM.Thm54.RepartitionedStaging.readsOn_of_envLocal
#print axioms Nock.NockVMROM.Thm54.RepartitionedStaging.not_mem_union_prior
#print axioms Nock.RedTeam.Batch1409.compute_sources_count
#print axioms Nock.RedTeam.Batch1409.compute_no_class_change
#print axioms Nock.RedTeam.Batch1409.memory_no_class_change
#print axioms Nock.RedTeam.Batch1409.memory_no_class_change_repoint
#print axioms Nock.RedTeam.Batch1409.compute_noRetarget_changes
#print axioms Nock.RedTeam.Batch1409.summand9_envLocal
#print axioms Nock.RedTeam.Batch1409.summand10_envLocal
#print axioms Nock.RedTeam.Batch1409.summand4_envLocal
#print axioms Nock.RedTeam.Batch1409.summand2mem_envLocal
#print axioms Nock.RedTeam.Batch1409.tie9
#print axioms Nock.RedTeam.Batch1409.tie10
#print axioms Nock.RedTeam.Batch1409.tie4
#print axioms Nock.RedTeam.Batch1409.tie2mem
#print axioms Nock.RedTeam.Batch1409.summand9_readsOn
#print axioms Nock.RedTeam.Batch1409.summand10W_readsOn
#print axioms Nock.RedTeam.Batch1409.s2_new
#print axioms Nock.RedTeam.Batch1409.s2_old_NOT
#print axioms Nock.RedTeam.Batch1409.s4_old_NOT
#print axioms Nock.RedTeam.Batch1409.s9_old_NOT
#print axioms Nock.RedTeam.Batch1409.s10_old_NOT
#print axioms Nock.RedTeam.Batch1409.s10_repartition_at_aM_NOT
#print axioms Nock.RedTeam.Batch1409.nc_not_readsOn
#print axioms Nock.RedTeam.Batch1409.nc_cylinder_full
#print axioms Nock.RedTeam.Batch1409.labels_local_new
#print axioms Nock.RedTeam.Batch1409.labels_old_round2
#print axioms Nock.RedTeam.Batch1409.s2_compute_local_new
#print axioms Nock.RedTeam.Batch1409.s2_compute_old_NOT
#print axioms Nock.RedTeam.Batch1409.summand12_B0
#print axioms Nock.RedTeam.Batch1409.summand13_B0
