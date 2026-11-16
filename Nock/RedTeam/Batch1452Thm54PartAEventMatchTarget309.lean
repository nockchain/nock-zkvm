import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.DeployedStaging
import Nock.NockVMROM.Thm54.P8Core.PartATarget309
import Nock.RedTeam.Batch1440Thm54PartARelocation
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1452Thm54PartAEventMatchTarget309.lean

  * §A `event_match` (production, `PartAEventMatch`): outside `consumedFailureEvent309 P Qc Qm`
    (fifteen summands, at `c`) and under `AcceptanceAt309`, `forget12 c` is outside the landed
    `optimizedFailureEventEv` at the transported pair.
  * §B `acceptance_outside_failure_implies_target12`, `staged_false_acceptance_bound12'`
    (production, `PartATarget309`): no `hAT`; the premises are the statement's own Form R three.
  * §C `Target309 ⇒` the statement's `OptimizedProductionGenuineTargetAt`:
    `target309_landed_transported` (every field, at the landed tuple and the transported pair,
    unconditionally) and `target309_implies_landed` (at `αW = α`, `views_eq`: the target at the
    re-hosted compute trace and the COMMITTED memory trace).

  Scope: `repartitionedChronology` and the parallel package; nothing here states or implies
  `:966` soundness at `deployedChronology`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1452

open scoped Polynomial
open Nock Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.PartA12
open Nock.NockVMROM.Thm54.PartAStaged
open Nock.NockVMROM.Thm54.PartAReHost
open Nock.NockVMROM.Thm54.PartAReWalk
open Nock.NockVMROM.Thm54.PartATarget309

section Pkg

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- §A receipt. -/
theorem receipt_event_match (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple12 K F) (hacc : AcceptanceAt309 P Qc Qm c)
    (hgood : c ∉ consumedFailureEvent309 P Qc Qm) :
    forget12 c ∉ optimizedFailureEventEv P
      (FamilyEnvCore.honestQc P.optimized (forget12 c)
        (FamilyEnvCore.familyQc P.optimized (forget12 c) (reHost P (forget12 c) Qc)))
      (FamilyEnvCore.honestQm P.optimized (forget12 c)
        (FamilyEnvCore.familyQm P.optimized (forget12 c) (reWalk P Qm c))) :=
  PartAEventMatch.event_match hacc hgood

/-- §A at the statement's consumed event (`consumedFailureEvent_eq_ev`, `rfl`). -/
theorem receipt_event_match_consumed (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple12 K F) (hacc : AcceptanceAt309 P Qc Qm c)
    (hgood : c ∉ consumedFailureEvent309 P Qc Qm) :
    forget12 c ∉ P.consumedFailureEvent (reHost P (forget12 c) Qc) (reWalk P Qm c) := by
  rw [P.consumedFailureEvent_eq_ev]
  exact PartAEventMatch.event_match_raw hacc hgood

/-- §B receipt. -/
theorem receipt_acceptance_outside_failure_implies_target12
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis) (hwidth : FormRWidth F)
    (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple12 K F) (hacc : AcceptanceAt309 P Qc Qm c)
    (hgood : c ∉ consumedFailureEvent309 P Qc Qm) : Target309 P Qc Qm c :=
  acceptance_outside_failure_implies_target12 P hax hbasis hwidth Qc Qm c hacc hgood

/-- §C (i): `Target309` carries the statement's target in full, at the landed tuple and the
transported pair. -/
theorem target309_landed_transported {Qc : Fin 309 → F[X]} {Qm : Fin P.memoryChip.rap.w → F[X]}
    {c : OptimizedProductionChallengeTuple12 K F} (h : Target309 P Qc Qm c) :
    P.OptimizedProductionGenuineTargetAt (reHost P (forget12 c) Qc) (reWalk P Qm c) (forget12 c) :=
  { sampled_io := h.landed_sampled_io
    hostile_io_event_good := h.landed_hostile_io_event_good
    timestamp_collision_good := h.landed_timestamp_collision_good
    compute_source := h.landed_compute_source
    compute := h.landed_compute
    memory := h.landed_memory
    aggregate_forest_axis := h.landed_aggregate_forest_axis
    p8 := h.landed_p8 }

/-- §C (ii) **`target309_implies_landed`**: at `αW = α` (`views_eq`) `Target309` gives the
statement's target at the re-hosted compute trace and the COMMITTED memory trace `Qm`: the memory
buckets from `memory12` at the view, the IO exclusion through the responses' round-≤1 reads. -/
theorem target309_implies_landed {Qc : Fin 309 → F[X]} {Qm : Fin P.memoryChip.rap.w → F[X]}
    {c : OptimizedProductionChallengeTuple12 K F} (h : Target309 P Qc Qm c)
    (hα : walkAlphaOf c = alphaM c.1) :
    P.OptimizedProductionGenuineTargetAt (reHost P (forget12 c) Qc) Qm (forget12 c) := by
  have hresp := hostileResponsesAt_B01 P (PartAEventMatch.agreeM_reWalk P Qm c) (forget12 c)
  have hio : (forget12 c).2.1 ∉ FiniteIO.IOFailureEvent (P.hostileRecordsAt (forget12 c)
      (P.familyQm (forget12 c) Qm) (P.familyQc (forget12 c) (reHost P (forget12 c) Qc))) := by
    have h0 := h.landed_hostile_io_event_good
    simp only [OptimizedFullStrictNockVMROMPackage.hostileRecordsAt,
      OptimizedFullStrictNockVMROMPackage.familyQm, FamilyEnvCore.hostileRecordsAt] at h0 ⊢
    rw [hresp] at h0
    exact h0
  have hmem := h.memory12
  rw [views_eq c hα] at hmem
  exact
    { sampled_io := h.landed_sampled_io
      hostile_io_event_good := hio
      timestamp_collision_good := h.landed_timestamp_collision_good
      compute_source := h.landed_compute_source
      compute := h.landed_compute
      memory := hmem
      aggregate_forest_axis := h.landed_aggregate_forest_axis
      p8 := h.landed_p8 }

open Classical in
/-- §B the unconditional staged bound. -/
theorem receipt_staged_false_acceptance_bound12'
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis) (hwidth : FormRWidth F)
    (Qc : OptimizedProductionChallengeTuple12 K F → Fin 309 → F[X])
    (Qm : OptimizedProductionChallengeTuple12 K F → Fin P.memoryChip.rap.w → F[X])
    (hst : StagedTraces12 P Qc Qm) :
    ((Finset.univ.filter fun c =>
        AcceptanceAt309 P (Qc c) (Qm c) c ∧ ¬ Target309 P (Qc c) (Qm c) c).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple12 K F) ≤
      optimizedHostileProductionFailureProbabilityBound15 (Fintype.card K) (Fintype.card F)
        (workloadEv P P.optimized.Λ)
        (FiniteIO.ioFailureUnionBound 10 (3 * P.optimized.family.problem.cfg.compRows)
          P.optimized.family.problem.cfg.memRows (Fintype.card K))
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows :=
  staged_false_acceptance_bound12' P hax hbasis hwidth Qc Qm hst

end Pkg

/-! ## §D. -/

def partAModules : List Lean.Name :=
  Nock.RedTeam.Batch1440.partAModules ++
  [`Nock.NockVMROM.Thm54.P8Core.PartAReWalk,
   `Nock.NockVMROM.Thm54.P8Core.PartAReWalkChip,
   `Nock.NockVMROM.Thm54.P8Core.PartAReHost,
   `Nock.NockVMROM.Thm54.P8Core.PartAEventMatch,
   `Nock.NockVMROM.Thm54.P8Core.PartATarget309]

open Lean in
run_cmd do
  let env ← getEnv
  let stmt := `Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
  let ctrl := Nock.RedTeam.Batch1440.importClosure env `Nock.NockVMROM.Thm54.DeployedStaging
  unless ctrl.contains stmt do
    throwError "Batch1452 control: DeployedStaging closure does not contain the statement"
  let mut above : Array Name := #[]
  for m in partAModules do
    unless env.header.moduleNames.contains m do
      throwError s!"Batch1452: module {m} not in the environment"
    if (Nock.RedTeam.Batch1440.importClosure env m).contains stmt then above := above.push m
  unless above.isEmpty do
    throwError s!"Batch1452: modules above the statement: {above}"
  logInfo m!"Batch1452 IMPORT-GRAPH: {partAModules.length} Part A modules, 0 import \
    {stmt}; control DeployedStaging imports it: true"

end Nock.RedTeam.Batch1452

#print axioms Nock.NockVMROM.Thm54.PartAEventMatch.event_match
#print axioms Nock.NockVMROM.Thm54.PartATarget309.acceptance_outside_failure_implies_target12
#print axioms Nock.NockVMROM.Thm54.PartATarget309.staged_false_acceptance_bound12'
#print axioms Nock.RedTeam.Batch1452.target309_landed_transported
#print axioms Nock.RedTeam.Batch1452.target309_implies_landed
#print axioms Nock.RedTeam.Batch1452.receipt_event_match_consumed
