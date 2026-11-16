import Nock.NockVMROM.Thm54.JointVerification
import Nock.NockVMROM.Thm54.FiniteFieldIOSoundness
import Nock.NockVMROM.Thm54.MemoryMplus2L
import Nock.NockVMROM.Thm54.Language
import Nock.NockVMROM.Thm54.RecordCarrier

/-!
# Sampled finite-field IO on one exact execution

This is the paper-facing `K`-valued replacement for the symbolic
`RatFunc (RatFunc K)` accumulator.  It does not encode a symbolic accumulator into `K`.
Instead, it threads one `FiniteIO.FiniteIOStrategy` through the exact configuration and execution
already fixed by a `PlusIOSegmentedFamily`, and pins its request/response records to the two lists
derived from that execution.

All three sampled failure events remain explicit:

* `IOPoleHitEvent` (completeness / denominator event);
* `IORLCCollisionEvent` (RLC soundness event);
* `IOLogDerivEvent` (sampled-pole soundness event).

The latter two are fields of `FiniteIOStrategy`; the first is retained here as an explicit field
because it is the hypothesis used by `finiteIO_oracle_agreement`.
-/

namespace Nock.NockVMROM.Thm54

open Nock

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]

/-- These are what the honest traces' chips compress since the
records carry the exponent slot (compute `S(i) + j + 1`, memory `reqIdx`). -/
def honestRecords10 (R : PlusIOSegmentedFamily F K) : FiniteIO.PreChallengeRecords K 10 :=
  RecordCarrier.extRecords R.problem.exec.derivedRequestIO
    ⟨R.problem.exec.derivedRequestIO, R.problem.exec.derivedResponseIO⟩

/-- The honest ten-slot in-table `intermediate` records. -/
def honestInterRecords10 (R : PlusIOSegmentedFamily F K) : FiniteIO.PreChallengeRecords K 10 :=
  RecordCarrier.extRecords R.problem.exec.derivedRequestIO
    ⟨(RowLayout.consumedRecordList R.problem.exec).map (fun r => NockVM.encRecC r
        (R.problem.exec.cprimeOf r)),
      R.problem.exec.derivedResponseIO⟩

/-- One sampled-IO assignment over exactly the same `cfg`/`exec` and table/walk witnesses as the
existing segmented assignment. -/
structure SampledIOSameExecutionAssignment
    (R : PlusIOSegmentedFamily F K) (p : ℕ) [CharP K p] where
  /-- Existing table and walk assignment on `R.problem`; its symbolic IO component is retained only
  as the comparison oracle used by S5. -/
  exact : PlusIOSameExecutionAssignment R p
  /-- Prover-committed sampled finite-field IO data. -/
  sampled : FiniteIO.FiniteIOStrategy K 9 R.problem.cfg.Ksz p
  /-- The sampled request list is exactly the compute rows' derived request list. -/
  requests_eq :
    sampled.records.requests = R.problem.exec.derivedRequestIO
  /-- The sampled response list is exactly the memory rows' derived response list. -/
  responses_eq :
    sampled.records.responses = R.problem.exec.derivedResponseIO
  /-- The completeness-side bad-pole event is retained explicitly. -/
  poleHitGood :
    sampled.coins.pole ∉
      FiniteIO.IOPoleHitEvent sampled.records sampled.coins.gamma
  /-- Sampled internal `intermediate` LogUp pole.
  Production `sampledAssignment` sets this to `I.memoryExtensionFold` (slot `6`);
  the honest `ipre`/`icur` overlay is `interResidentAcc` at
  `⟨sampled.coins.gamma, interPole⟩`.  `TraceGen/Gen.lean` is unedited. -/
  interPole : K
  /-- Twin of `poleHitGood` on the in-table `mem_record` lists,
  not the external IO columns (`:509`).  A zero record gives `compress = interPole`,
  so this is not perfect via structure. -/
  interPoleHitGood :
    interPole ∉
      FiniteIO.IOPoleHitEvent
        { requests := (RowLayout.consumedRecordList R.problem.exec).map (fun r => NockVM.encRecC r
            (R.problem.exec.cprimeOf r))
          responses := R.problem.exec.derivedResponseIO }
        sampled.coins.gamma
  /-- Honest `ver = (st = read_root)` on every memory row.
  Needed so in-table add columns agree with derived IO responses; not a package field. -/
  honestVer : ∀ row ∈ R.problem.exec.memoryRows,
    row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)
  /-- The sampled coins are also outside the IO failure event of the honest
  ten-slot records (`honestRecords10`), which the chips compress since the exponent carrier. -/
  ioGood10 :
    (sampled.coins.gamma, sampled.coins.pole) ∉ FiniteIO.IOFailureEvent (honestRecords10 R)
  /-- Twin of `interPoleHitGood` on the ten-slot in-table records. -/
  interPoleHitGood10 :
    interPole ∉ FiniteIO.IOPoleHitEvent (honestInterRecords10 R) sampled.coins.gamma

namespace SampledIOSameExecutionAssignment

variable {R : PlusIOSegmentedFamily F K}

/-- Sampled intermediate coins: IO `γ` reused, pole = `interPole`. -/
def interCoins (A : SampledIOSameExecutionAssignment R p) : FiniteIO.IOCoins K :=
  ⟨A.sampled.coins.gamma, A.interPole⟩

/-- In-table `mem_record` pair at the sampled execution.
Twin of `BuildableChips.executionRecords` for the *internal* columns. -/
def interRecords (A : SampledIOSameExecutionAssignment R p) :
    FiniteIO.PreChallengeRecords K 9 where
  requests := (RowLayout.consumedRecordList R.problem.exec).map (fun r => NockVM.encRecC r
      (R.problem.exec.cprimeOf r))
  responses := R.problem.exec.derivedResponseIO

/-- The sampled strategy proves the exact execution's record-level IO language. -/
theorem lio (A : SampledIOSameExecutionAssignment R p) :
    IO.LIO R.problem.cfg.Ksz
      R.problem.exec.derivedRequestIO R.problem.exec.derivedResponseIO := by
  rw [← A.requests_eq, ← A.responses_eq]
  exact A.sampled.lio

/-- Sampled acceptance supplies the existing exact symbolic S5 object through the common
`IO.LIO` characterization; no `IOField K → K` encoding occurs. -/
theorem sharedIOSat (A : SampledIOSameExecutionAssignment R p) :
    SharedIOSat R p :=
  (sharedIOSat_iff_LIO R A.sampled.charBound).2 A.lio

/-- The two constructions agree at existential-witness level on this exact record pair. -/
theorem oracle_agreement (A : SampledIOSameExecutionAssignment R p) :
    (∃ w : FiniteIO.PostChallengeIOWitness A.sampled.records A.sampled.coins,
        FiniteIO.FiniteIOAccepts A.sampled.records A.sampled.coins w)
      ↔
    (∃ (mu : Fin A.sampled.records.responses.length → ZMod p)
        (accP accM : ℕ → RatFunc (RatFunc K))
        (requests responses outMem : RatFunc (RatFunc K)),
      (∀ j, mu j ≠ 0) ∧
      IO.ProgIOSat
        (fun i => SetEq.RLC (IO.listExt A.sampled.records.requests i))
        accP requests A.sampled.records.requests.length ∧
      IO.MemIOSat
        (fun i => SetEq.RLC (IO.listExt A.sampled.records.responses i))
        (IO.castμ mu) accM responses outMem A.sampled.records.responses.length ∧
      requests = responses ∧ outMem = 0) :=
  FiniteIO.finiteIO_oracle_agreement A.sampled.records A.sampled.coins
    A.sampled.charBound A.sampled.requestRange A.sampled.responseRange
    A.sampled.uniqueRequest A.sampled.uniqueResponse
    A.sampled.gammaGood A.sampled.poleGood A.poleHitGood

/-- The exact symbolic assignment carried for comparison belongs to the same S5 shared-IO
language proved by the sampled strategy. -/
theorem exact_toIOSat_on_sampled_records
    (A : SampledIOSameExecutionAssignment R p) :
    IOSat p A.sampled.records.requests A.sampled.records.responses := by
  rw [A.requests_eq, A.responses_eq]
  exact A.exact.exactIO.toIOSat

/-- What the in-gate walk needs
of the honest family beyond the walk certificate: (i) the family's node valuation is `RLC^γ` of
the paper's `LT_comp` label vector, and (ii) on every authoritative BFS row the tree's state is the row's state, the
real child count is `fanout(state)` and each active child's `(s, f, e)` is the parent's declared
`sf_j` (`:1684-1690`, the local topology relation `RawComputeTopologyBinding`).  Both are theorems
of every honest execution (`ComputeExactTopology`, `ComputeRowsAccepted`); they are carried here
so the honest gate proofs need no further hypothesis. -/
def WalkLabelObligations (A : SampledIOSameExecutionAssignment R p) : Prop :=
  (∀ t, R.computeNodeVal t = Walk.rlc R.walkGamma (ComputeTable.labelVecOfPub t.label.2.2.1)) ∧
    (∀ t ∈ R.computeWalkRows,
      t.label.1 = t.label.2.2.1.state ∧
        ComputeTable.fanoutComp t.label.1 = t.children.length ∧
        ComputeTable.childLinkComp t.label (fun j => t.childLabel j))

def ComputeSampledObligations
    (A : SampledIOSameExecutionAssignment R p) : Prop :=
  (∀ kind, (R.computeTableRAP kind).Satisfies A.exact.computeTableTrace) ∧
    A.exact.ComputeWalkCertificate ∧
    FiniteIO.FiniteIOAccepts
      A.sampled.records A.sampled.coins A.sampled.witness ∧
    A.WalkLabelObligations

/-- The memory twin of
`WalkLabelObligations`; what the in-gate walk gates need of the honest trace. -/
def MemoryWalkLabelObligations (A : SampledIOSameExecutionAssignment R p) : Prop :=
  (∀ t, R.memoryNodeVal t = Walk.rlc R.walkGamma (MemoryTable.memoryLabelVec t.label.2.2)) ∧
    (∀ t ∈ R.memoryWalkRows,
      t.label.1 = t.label.2.2.st ∧
        MemoryTable.fanoutMem t.label.1 = t.children.length ∧
        MemoryTable.childLinkMem t.label (fun j => t.childLabel j))

/-- Memory-side concrete obligations for the sampled replacement. -/
def MemorySampledObligations
    (A : SampledIOSameExecutionAssignment R p) : Prop :=
  (∀ kind, (R.memoryTableRAP kind).Satisfies A.exact.memoryTableTrace) ∧
    A.exact.MemoryWalkCertificate ∧
    FiniteIO.FiniteIOAccepts
      A.sampled.records A.sampled.coins A.sampled.witness ∧
    A.MemoryWalkLabelObligations

/-- Existing six-family satisfaction projects to the same compute table/walk objects; sampled IO
acceptance is the strategy's own gate theorem. -/
theorem computeSampledObligations_of_six
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.exact.SixConcreteObligations)
    (hlabel : A.WalkLabelObligations) :
    A.ComputeSampledObligations :=
  ⟨h.1, h.2.2.1, A.sampled.accepts, hlabel⟩

/-- Existing six-family satisfaction projects to the same memory table and the same one forest
walk; sampled response IO is the strategy's own accepted finite-field witness. -/
theorem memorySampledObligations_of_six
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.exact.SixConcreteObligations)
    (hlabel : A.MemoryWalkLabelObligations) :
    A.MemorySampledObligations :=
  ⟨h.2.1, h.2.2.2.1, A.sampled.accepts, hlabel⟩

/-- All three bad-event exclusions exported without conflating `gamma`, `pole`, walk randomness,
or the RAP coset shift. -/
theorem three_events_good (A : SampledIOSameExecutionAssignment R p) :
    A.sampled.coins.pole ∉
        FiniteIO.IOPoleHitEvent A.sampled.records A.sampled.coins.gamma ∧
      A.sampled.coins.gamma ∉
        FiniteIO.IORLCCollisionEvent A.sampled.records ∧
      A.sampled.coins.pole ∉
        FiniteIO.IOLogDerivEvent A.sampled.records A.sampled.coins.gamma :=
  ⟨A.poleHitGood, A.sampled.gammaGood, A.sampled.poleGood⟩

/-- The in-table add column is the sampled IO response list under honest `ver`. -/
theorem interRecords_responses_eq (A : SampledIOSameExecutionAssignment R p) :
    A.interRecords.responses = A.sampled.records.responses := by
  simpa [SampledIOSameExecutionAssignment.interRecords] using A.responses_eq.symm

/-- Twin of `FiniteIOStrategy.gammaGood` on the in-table lists: a collision among
`consumed ++ added` is a collision among the IO responses, hence among the IO lists.
`hprl` identifies the remove column with the add column.
`hC` is row-level coherence: on this execution a stored record determines its `C'`
(`ExactExecution.CprimeCoherent`), which the remove column reads through `cprimeOf`. -/
theorem inter_gammaGood_of_io (A : SampledIOSameExecutionAssignment R p)
    (hprl : RowLayout.PairedRecordLayout R.problem.exec)
    (hC : R.problem.exec.CprimeCoherent) :
    A.sampled.coins.gamma ∉ FiniteIO.IORLCCollisionEvent A.interRecords := by
  intro h
  apply A.sampled.gammaGood
  have henc : R.problem.exec.derivedResponseIO =
      (RowLayout.addedRecordList R.problem.exec).map (fun r => NockVM.encRecC r
          (R.problem.exec.cprimeOf r)) := by
    rw [← RowLayout.rawResponses_eq_addedRecordList _ A.honestVer]
    exact ExactExecution.derivedResponseIO_eq_map_encRecC _ hC
  refine FiniteIO.IORLCCollisionEvent_of_mem_subset ?_ h
  intro v hv
  have hv' : v ∈ A.interRecords.responses := by
    simp only [SampledIOSameExecutionAssignment.interRecords, List.mem_append] at hv
    rcases hv with hv | hv
    · simp only [SampledIOSameExecutionAssignment.interRecords] at hv ⊢
      rw [henc]
      exact (hprl.map (fun r => NockVM.encRecC r (R.problem.exec.cprimeOf r))).mem_iff.mp hv
    · exact hv
  rw [interRecords_responses_eq A] at hv'
  exact List.mem_append_right _ hv'

/-- Twin of `FiniteIOStrategy.coins_not_failure` on the in-table `(γ, interPole)` pair.
Honest-side: `gammaGood` + `interPoleHitGood` + `PairedRecordLayout` + `A.honestVer`
(log-derivative event empty) + `hC` (row-level `C'` coherence).
Not a capstone hypothesis. -/
theorem inter_coins_not_failure (A : SampledIOSameExecutionAssignment R p)
    (hprl : RowLayout.PairedRecordLayout R.problem.exec)
    (hC : R.problem.exec.CprimeCoherent) :
    (A.sampled.coins.gamma, A.interPole) ∉ FiniteIO.IOFailureEvent A.interRecords :=
  FiniteIO.notMem_IOFailureEvent_of
    (inter_gammaGood_of_io A hprl hC)
    A.interPoleHitGood
    (by
      have henc : R.problem.exec.derivedResponseIO =
          (RowLayout.addedRecordList R.problem.exec).map (fun r => NockVM.encRecC r
              (R.problem.exec.cprimeOf r)) := by
        rw [← RowLayout.rawResponses_eq_addedRecordList _ A.honestVer]
        exact ExactExecution.derivedResponseIO_eq_map_encRecC _ hC
      have hperm : A.interRecords.requests.Perm A.interRecords.responses := by
        simpa [SampledIOSameExecutionAssignment.interRecords, henc] using
          hprl.map (fun r => NockVM.encRecC r (R.problem.exec.cprimeOf r))
      rw [FiniteIO.IOLogDerivEvent_eq_empty_of_perm _ _ hperm]
      exact Finset.notMem_empty _)


/-- The honest ten-slot records are in `IO.LIO` (the nine-slot `lio`, extended). -/
theorem lio10 (A : SampledIOSameExecutionAssignment R p) :
    IO.LIO R.problem.cfg.Ksz (honestRecords10 R).requests (honestRecords10 R).responses :=
  RecordCarrier.lio_extRecords _ A.lio

theorem pole10_ne (A : SampledIOSameExecutionAssignment R p) :
    ∀ v ∈ (honestRecords10 R).requests ++ (honestRecords10 R).responses,
      FiniteIO.compress A.sampled.coins v ≠ 0 := by
  intro v hv h0
  apply A.ioGood10
  simp only [FiniteIO.IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  refine Or.inr (Or.inl ?_)
  simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨v, hv, by simpa [FiniteIO.compress, add_comm] using h0⟩

theorem witness10_exists (A : SampledIOSameExecutionAssignment R p) :
    ∃ w : FiniteIO.PostChallengeIOWitness (honestRecords10 R) A.sampled.coins,
      FiniteIO.FiniteIOAccepts (honestRecords10 R) A.sampled.coins w :=
  FiniteIO.finiteIO_complete_of_LIO (Ksz := R.problem.cfg.Ksz) _ _ A.lio10 A.pole10_ne

def witness10 (A : SampledIOSameExecutionAssignment R p) :
    FiniteIO.PostChallengeIOWitness (honestRecords10 R) A.sampled.coins :=
  Classical.choose A.witness10_exists

theorem witness10_accepts (A : SampledIOSameExecutionAssignment R p) :
    FiniteIO.FiniteIOAccepts (honestRecords10 R) A.sampled.coins A.witness10 :=
  Classical.choose_spec A.witness10_exists

/-- The honest ten-slot compression of a nine-slot record. -/
def compress10 (A : SampledIOSameExecutionAssignment R p) (v : Fin 9 → K) : K :=
  FiniteIO.compress A.sampled.coins (RecordCarrier.extRec R.problem.exec.derivedRequestIO v)

/-- Every honest request record has a nonzero ten-slot compression (`ioGood10`'s pole-hit
component). -/
theorem compress10_ne_zero (A : SampledIOSameExecutionAssignment R p) {v : Fin 9 → K}
    (hv : v ∈ R.problem.exec.derivedRequestIO) : A.compress10 v ≠ 0 :=
  A.pole10_ne _ (List.mem_append_left _ (List.mem_map.mpr ⟨v, hv, rfl⟩))

/-- The honest ten-slot compression at the in-table coins `(γ, interPole)`. -/
def interCompress10 (A : SampledIOSameExecutionAssignment R p) (v : Fin 9 → K) : K :=
  FiniteIO.compress A.interCoins (RecordCarrier.extRec R.problem.exec.derivedRequestIO v)

theorem inter_coins_not_failure10 (A : SampledIOSameExecutionAssignment R p)
    (hprl : RowLayout.PairedRecordLayout R.problem.exec)
    (hC : R.problem.exec.CprimeCoherent) :
    (A.sampled.coins.gamma, A.interPole) ∉ FiniteIO.IOFailureEvent (honestInterRecords10 R) := by
  have henc : R.problem.exec.derivedResponseIO =
      (RowLayout.addedRecordList R.problem.exec).map (fun r => NockVM.encRecC r
          (R.problem.exec.cprimeOf r)) := by
    rw [← RowLayout.rawResponses_eq_addedRecordList _ A.honestVer]
    exact ExactExecution.derivedResponseIO_eq_map_encRecC _ hC
  have hperm9 : ((RowLayout.consumedRecordList R.problem.exec).map (fun r => NockVM.encRecC r
        (R.problem.exec.cprimeOf r))).Perm R.problem.exec.derivedResponseIO := by
    rw [henc]; exact hprl.map _
  refine FiniteIO.notMem_IOFailureEvent_of ?_ A.interPoleHitGood10 ?_
  · intro h
    apply A.ioGood10
    simp only [FiniteIO.IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    refine Or.inl (FiniteIO.IORLCCollisionEvent_of_mem_subset ?_ h)
    intro v hv
    simp only [honestInterRecords10, honestRecords10, RecordCarrier.extRecords_requests,
      RecordCarrier.extRecords_responses, List.mem_append] at hv ⊢
    rcases hv with hv | hv
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      exact Or.inr (List.mem_map.mpr ⟨w, hperm9.mem_iff.mp hw, rfl⟩)
    · exact Or.inr hv
  · rw [FiniteIO.IOLogDerivEvent_eq_empty_of_perm]
    · exact Finset.notMem_empty _
    · exact hperm9.map _

#print axioms lio
#print axioms sharedIOSat
#print axioms oracle_agreement
#print axioms exact_toIOSat_on_sampled_records
#print axioms computeSampledObligations_of_six
#print axioms memorySampledObligations_of_six
#print axioms three_events_good

end SampledIOSameExecutionAssignment
end
end Nock.NockVMROM.Thm54
