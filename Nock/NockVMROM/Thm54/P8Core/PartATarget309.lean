/-
  Nock/NockVMROM/Thm54/P8Core/PartATarget309.lean

  Below the statement (the receipt `Target309 ⇒` the statement's
  `OptimizedProductionGenuineTargetAt` is in `Nock/RedTeam/Batch1452…`, above it).

  * `Target309 P Qc Qm c`: every field of the landed target, at the landed tuple `forget12 c` and
    the transported pair `(reHost P (forget12 c) Qc, reWalk P Qm c)` — the 303-wide image of the
    309 trace and the memory trace re-walked at the timestamp coin — field for field the
    statement's fields with the same bodies; plus the parallel package's own facts: the 309 source
    obligations of the committed compute trace, the twelve-coin memory buckets of the committed
    memory trace at the memory view (walk coin `αW`), the IO and request-timestamp exclusions at
    the committed traces, and summand 15's walk-line exclusion at `α`.
  * `acceptance_outside_failure_implies_target12`: `AcceptanceAt309 ∧ c ∉ consumedFailureEvent309
    → Target309`, through `satisfies303_of_309` (step 3), `memory_satisfies_at_alpha` (step 4),
    `event_match` (step 5) and `PlacementA.holds_of_acceptance_evOnly` (the landed `p8` chain at
    the landed tuple), with the package's `generated` / `primeField` and the three Form R premises
    `hax hbasis hwidth` that the statement's own `acceptance_outside_failure_implies_target` (and
    `of_package`) already carry.
  * `staged_false_acceptance_bound12'`: L4's staged bound at `Target309`, with no `hAT`.

  Scope: `repartitionedChronology` and the parallel package.  Nothing here states or implies
  `:966` soundness at `deployedChronology`
-/
import Nock.NockVMROM.Thm54.P8Core.PartAEventMatch
import Nock.NockVMROM.Thm54.P8Core.PlacementAEvOnly
import Nock.NockVMROM.Thm54.P8Core.PlacementABridge
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.PartATarget309

open scoped Classical Polynomial
open Polynomial
open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.PartA12
open Nock.NockVMROM.Thm54.PartAStaged
open Nock.NockVMROM.Thm54.PartAReHost
open Nock.NockVMROM.Thm54.PartAReWalk
open Nock.NockVMROM.Thm54.PartAEventMatch

noncomputable section

/-- At `αW = α` the memory view is the landed tuple (L4b's `Batch1443.views_eq`, restated in
production). -/
theorem views_eq {K F : Type} [Fintype K] [Fintype F]
    (c : OptimizedProductionChallengeTuple12 K F) (h : walkAlphaOf c = alphaM c.1) :
    walkView11 c = forget12 c := by
  rcases c with ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩, ⟨⟨a5, a6⟩, ⟨r, ⟨i, l, w⟩⟩⟩⟩
  simp only [walkAlphaOf, alphaM] at h
  subst h
  rfl

section Target

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The `landed_*` fields are the
statement's `OptimizedProductionGenuineTargetAt` fields verbatim, at the landed tuple `t :=
forget12 c` and the transported pair; the remaining fields are the parallel package's own. -/
structure Target309 (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple12 K F) : Prop where
  landed_sampled_io :
    IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs
  landed_hostile_io_event_good :
    (forget12 c).2.1 ∉ FiniteIO.IOFailureEvent (P.hostileRecordsAt (forget12 c)
      (P.familyQm (forget12 c) (reWalk P Qm c)) (P.familyQc (forget12 c) (reHost P (forget12 c) Qc)))
  landed_timestamp_collision_good :
    alphaM (forget12 c).1 ∉ OptimizedHostileTimestamps.TimestampCollisionEvent
      (P.hostileRequestsAt (forget12 c) (P.familyQc (forget12 c) (reHost P (forget12 c) Qc))).length
  landed_compute_source :
    ∀ i,
      CorrectedComputeSourceObligations P.optimized.family.problem.cfg.compRows
        (FamilyEnvCore.rowEnvAt P.optimized (forget12 c)
          (P.familyQc (forget12 c) (reHost P (forget12 c) Qc)) i)
        (envOfTrace (P.familyQc (forget12 c) (reHost P (forget12 c) Qc)) P.optimized.orbit.ω
          (P.optimized.computeNodes i)
          (DeployedChipFamily.computeChalValOfTuple P.optimized.basis (forget12 c))
          (P.familyComputePublic (forget12 c)))
  landed_compute :
    ∀ (i : Fin P.optimized.family.problem.cfg.compRows),
      (i : ℕ) + 1 < P.optimized.family.problem.cfg.compRows →
      CorrectedDecodedTransitionSources (FamilyEnvCore.rowEnvAt P.optimized (forget12 c)
        (P.familyQc (forget12 c) (reHost P (forget12 c) Qc)) i)
  landed_memory :
    ∀ i,
      (∀ g ∈ baseTransitionGates P.optimized.basis,
        g.eval (P.memEnvF (forget12 c) (P.familyQm (forget12 c) (reWalk P Qm c)) i) = 0) ∧
      (∀ g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis,
        g.eval (P.memEnvK (forget12 c) (P.familyQm (forget12 c) (reWalk P Qm c)) i)
          (P.memEnvF (forget12 c) (P.familyQm (forget12 c) (reWalk P Qm c)) i) = 0)
  landed_aggregate_forest_axis : P.optimized.OptimizedSharedMemoryConnective
  landed_p8 :
    ∃ fuel, Nock.evalN fuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = some P.optimized.verifier.raw.claim.result
  /-- The 309 chip's source obligations of the committed compute trace. -/
  compute309 :
    ∀ i, Unhosted309.SourceObligations309 (nC P) (G309 P (forget12 c) Qc i) (envAt P (forget12 c) Qc i)
  /-- The twelve-coin memory buckets of the committed memory trace at the memory view (`αW`). -/
  memory12 :
    ∀ i,
      (∀ g ∈ baseTransitionGates P.optimized.basis,
        g.eval (P.memEnvF (walkView11 c) (P.familyQm (walkView11 c) Qm) i) = 0) ∧
      (∀ g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis,
        g.eval (P.memEnvK (walkView11 c) (P.familyQm (walkView11 c) Qm) i)
          (P.memEnvF (walkView11 c) (P.familyQm (walkView11 c) Qm) i) = 0)
  /-- The IO exclusion at the committed traces' records. -/
  hostile_io_event_good :
    (forget12 c).2.1 ∉ FiniteIO.IOFailureEvent (P.hostileRecordsAt (forget12 c)
      (P.familyQm (forget12 c) Qm) (P.familyQc (forget12 c) (truncQc P Qc)))
  /-- The request-timestamp exclusion at the committed compute trace's requests. -/
  timestamp_collision_good :
    alphaM c.1 ∉ OptimizedHostileTimestamps.TimestampCollisionEvent
      (P.hostileRequestsAt (forget12 c) (P.familyQc (forget12 c) (truncQc P Qc))).length
  /-- Summand 15: the memory-row walk-line exclusion at `α`. -/
  walk_timestamp_good :
    alphaM c.1 ∉ OptimizedHostileTimestamps.TimestampCollisionEvent (M P)

/-- The landed acceptance of the transported pair at the landed tuple (steps 3 and 4). -/
theorem transported_acceptance {Qc : Fin 309 → F[X]} {Qm : Fin P.memoryChip.rap.w → F[X]}
    {c : OptimizedProductionChallengeTuple12 K F} (hacc : AcceptanceAt309 P Qc Qm c)
    (hgood : c ∉ consumedFailureEvent309 P Qc Qm) :
    DeployedAcceptanceAt P (forget12 c) (P.familyQc (forget12 c) (reHost P (forget12 c) Qc))
      (P.familyQm (forget12 c) (reWalk P Qm c)) :=
  ⟨satisfies303_of_309 P (forget12 c) Qc hacc.compute_satisfies,
    memory_satisfies_at_alpha P Qc Qm c hacc hgood⟩

/-- **Acceptance at the parallel package outside the twelve-coin event gives
`Target309`.**  `p8` is `PlacementA.holds_of_acceptance_evOnly` at the landed tuple and the
transported pair (`transported_acceptance`, `event_match`). -/
theorem acceptance_outside_failure_implies_target12
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple12 K F)
    (hacc : AcceptanceAt309 P Qc Qm c)
    (hgood : c ∉ consumedFailureEvent309 P Qc Qm) :
    Target309 P Qc Qm c := by
  set t := forget12 c with ht
  set Qc' := reHost P t Qc with hQc'
  set Qm' := reWalk P Qm c with hQm'
  have hacc' : DeployedAcceptanceAt P t (P.familyQc t Qc') (P.familyQm t Qm') :=
    transported_acceptance P hacc hgood
  have hgood' : t ∉ OptimizedFailureEventEv.optimizedFailureEventEv P Qc' Qm' :=
    event_match_raw hacc hgood
  have hc := PlacementA.good_components_of_Ev P Qc' Qm' t hgood'
  have hio : t.2.1 ∉ FiniteIO.IOFailureEvent
      (P.hostileRecordsAt t (P.familyQm t Qm') (P.familyQc t Qc')) :=
    FamilyEnvCore.familyIOGood_of_not_mem P.optimized Qc' Qm' t hc.2.1
  have hts : alphaM t.1 ∉ OptimizedHostileTimestamps.TimestampCollisionEvent
      (P.hostileRequestsAt t (P.familyQc t Qc')).length := by
    have h := hc.2.2.1
    have hlen := FamilyEnvCore.hostileRequestsAt_length_eq P.optimized t Qc'
    rw [show (P.hostileRequestsAt t (P.familyQc t Qc')).length = (P.hostileRequests Qc').length
      from hlen]
    exact h
  have hw0 : P.computeChip.rap.w = 303 := P.optimized.exact_chip_resources.1
  have hgoodEv : t ∉ OptimizedFailureEventEv.optimizedFailureEventEv P
      (FamilyComputeRows.honestQc P t (P.familyQc t Qc'))
      (FamilyMemoryRows.honestQm P t (P.familyQm t Qm')) := by
    rw [show FamilyComputeRows.honestQc P t (P.familyQc t Qc') = Qc' from
          FamilyEnvCore.honestQc_familyQc P.optimized t Qc',
        show FamilyMemoryRows.honestQm P t (P.familyQm t Qm') = Qm' from
          FamilyEnvCore.honestQm_familyQm P.optimized t Qm']
    exact hgood'
  -- the parallel package's own facts
  have hn := Pkg12.notMem_consumedFailureEvent12 P (truncQc P Qc) Qm c hgood
  obtain ⟨_, h2, h3, _, _, _, _, _, _, _, _, _, _, _, h15⟩ := hn
  have hio0 : t.2.1 ∉ FiniteIO.IOFailureEvent
      (P.hostileRecordsAt t (P.familyQm t Qm) (P.familyQc t (truncQc P Qc))) :=
    FamilyEnvCore.familyIOGood_of_not_mem P.optimized (truncQc P Qc) Qm t h2
  have hts0 : alphaM c.1 ∉ OptimizedHostileTimestamps.TimestampCollisionEvent
      (P.hostileRequestsAt t (P.familyQc t (truncQc P Qc))).length := by
    have h := (mt (mem_liftTimestampFailure_iff _ _).2) h3
    have hlen := FamilyEnvCore.hostileRequestsAt_length_eq P.optimized t (truncQc P Qc)
    rw [show (P.hostileRequestsAt t (P.familyQc t (truncQc P Qc))).length =
        (P.hostileRequests (truncQc P Qc)).length from hlen]
    exact h
  have hsat309 := (rowHyps_of_sat P t Qc hacc.compute_satisfies).2
  have hview := memSat_at_view P Qc Qm c hacc
  obtain ⟨gfuel, G, R, fuel, r, hgen, hG, hΛG⟩ := P.generated
  exact
    { landed_sampled_io := P.shared_io
      landed_hostile_io_event_good := hio
      landed_timestamp_collision_good := hts
      landed_compute_source := fun i =>
        FamilyEnvCore.row_obligations_at P.optimized t (P.familyQc t Qc') hacc'.compute_satisfies i
      landed_compute := fun i hi =>
        corrected_conditional_transition_soundness
          (FamilyEnvCore.row_obligations_at P.optimized t (P.familyQc t Qc')
            hacc'.compute_satisfies i)
          (FamilyEnvCore.notLast_at P.optimized t hw0 (P.familyQc t Qc')
            hacc'.compute_satisfies i hi)
      landed_memory := fun i =>
        FamilyEnvCore.memory_row_parts_at P.optimized t (P.familyQm t Qm') hacc'.memory_satisfies i
      landed_aggregate_forest_axis := P.optimized.shared_memory_connective
      landed_p8 := ⟨fuel, (PlacementA.holds_of_acceptance_evOnly P t (P.familyQc t Qc')
        (P.familyQm t Qm') hacc' hgoodEv hax hbasis hwidth hgen hG hΛG P.primeField).2⟩
      compute309 := hsat309
      memory12 := fun i =>
        FamilyEnvCore.memory_row_parts_at P.optimized (walkView11 c) (P.familyQm (walkView11 c) Qm)
          hview i
      hostile_io_event_good := hio0
      timestamp_collision_good := hts0
      walk_timestamp_good := h15 }

open Classical in
/-- **The unconditional staged false-acceptance bound at the parallel package** (H2.2 at
`Target309`; no `hAT`).  For every staged prover strategy, the fraction of the twelve coins at
which its own traces are accepted by the parallel chips while `Target309` fails is at most the
fifteen-summand bound function `optimizedHostileProductionFailureProbabilityBound15` (the consumed
fixed-trace function plus `(1 + M(M−1)/2)/|𝕂|`).  The premises are the three Form R premises the
statement's `acceptance_outside_failure_implies_target` already carries.  At
`repartitionedChronology`; nothing here is about `deployedChronology`. -/
theorem staged_false_acceptance_bound12'
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
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
  staged_false_acceptance_bound12 P (Target309 P)
    (fun Qc Qm c hacc hgood =>
      acceptance_outside_failure_implies_target12 P hax hbasis hwidth Qc Qm c hacc hgood)
    Qc Qm hst

open Classical in
/-- The fixed-trace corollary at `Target309` (a fixed pair is the constant strategy). -/
theorem complete_false_acceptance_bound_of_staged12'
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (qc : Fin 309 → F[X]) (qm : Fin P.memoryChip.rap.w → F[X]) :
    ((Finset.univ.filter fun c => AcceptanceAt309 P qc qm c ∧ ¬ Target309 P qc qm c).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple12 K F) ≤
      optimizedHostileProductionFailureProbabilityBound15 (Fintype.card K) (Fintype.card F)
        (workloadEv P P.optimized.Λ)
        (FiniteIO.ioFailureUnionBound 10 (3 * P.optimized.family.problem.cfg.compRows)
          P.optimized.family.problem.cfg.memRows (Fintype.card K))
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows :=
  complete_false_acceptance_bound_of_staged12 P (Target309 P)
    (fun Qc Qm c hacc hgood =>
      acceptance_outside_failure_implies_target12 P hax hbasis hwidth Qc Qm c hacc hgood)
    qc qm

end Target

end

end Nock.NockVMROM.Thm54.PartATarget309
