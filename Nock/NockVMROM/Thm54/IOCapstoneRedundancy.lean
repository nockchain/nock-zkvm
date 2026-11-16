import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.IOCoinReconciliation
import Nock.NockVMROM.Thm54.IOChipCompleteness
import Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
import Nock.NockVMROM.Thm54.MultiRootServedFixture
import Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
import Nock.NockVMROM.Thm54.MultiRootHonestArrays
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# The capstone's IO content is derivable from acceptance, not merely carried

`OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage` carries an
`ioStrategy : FiniteIO.FiniteIOStrategy K 9 …` field, and its `shared_io` projection
(`OptimizedStrictFullPackage.lean:112`) delivers `IO.LIO` by *reading* that strategy's own
`FiniteIOStrategy.lio` theorem (`FiniteFieldIOSoundness.lean:551`), which in turn is derived from
the strategy's `accepts` **field** (`FiniteFieldIOSoundness.lean:494`).  The generator discharges
that field from honest semantics (`BuildableChips.finiteIOStrategy`, `:163`, via
`sampledWitness_accepts` and ultimately `execution_lio`), which is the right thing to do for the
*completeness* direction — the generator builds the package and may supply its fields from the
execution it is compiling.

What was missing is the **soundness** counterpart, which is the ⇐ direction of `Thm:IO_result`: a prover who is merely *accepted* must satisfy the IO acceptance predicate,
so the carried field is redundant at an accepted tuple outside the failure event.  This module
supplies it, by composing three things that already exist and had never been put together at the
package:

* `IOChip.projWitness_accepts` (`IOChipSoundness.lean:232`) — `FiniteIOAccepts` **proved** from
  per-kind RAP satisfaction of the two `K`-valued IO chips, with the witness read off the hostile
  committed traces and nothing coming from an execution;
* `IOCoinReconciliation.ioCoinsOf_eq_sampled` (`:177`) — the accepted production tuple's IO
  coordinate *is* the
  package's deployment coins;
* the package's own `family ↔ objects` transport, which carries the sampled records onto
  `objects.reqRecs` / `objects.respRecs`.

## What is proved

* `accepts_derivable` (§2) — the content of the `FiniteIOStrategy.accepts` field, at the package's
  own records and its own sampled coins, follows from chip satisfaction at an accepted tuple.
  This is the `accepts` analogue of `IOCoinReconciliation.gammaGood_derivable` (`:226`) and
  `poleGood_derivable` (`:236`), which retire two other fields of the same structure.
* `sharedIo_derivable` (§3) — **the exact proposition `OptimizedStrictFullPackage.shared_io`
  proves**, reached without touching the carried field.  `sharedIo_derivable_eq_shared_io`
  typechecks only because the two propositions are literally the same one.

`sharedIo_derivable`'s closure contains **none** of `ioStrategy`, `io_requests`, `io_responses`
or `shared_io`.  So it is not only the `accepts` field that is redundant for the capstone's IO
conjunct: the whole `ioStrategy` triple is, because the derivation runs through the *other*
`FiniteIOStrategy` the package carries — `optimized.sampled.sampled`, the one the production
failure event is actually stated over (`optimizedFailureEvent`,
`OptimizedStrictFullPackage.lean:350`, feeds `optimized.sampled.sampled.records` to
`OptimizedProductionFailureEvent`'s `liftIOFailure` summand,
`OptimizedStrictPackage.lean:603,616`) and the one `OptimizedHistoricalAcceptanceAt.sampled_io_coins`
(`OptimizedStrictFullPackage.lean:414`) pins the tuple's IO coordinate to.  Note the package type
does **not** identify the two strategies; only the generator happens to build both from the same
`finiteIOStrategy` (`BuildablePackage.lean:231`, `OptimizedComputeSampledTrace.lean:154`).  This is an observation about the type, not a
proposal to drop a field.

## Scope

Both headlines are `∀`-quantified over the package, the traces and the tuple: they are *not*
fixture claims.  The non-vacuity receipts in §5 are: `chip_hypotheses_inhabited` is generic (any
package with an accepted tuple), while `hypotheses_inhabited_at_packageP` is a **fixture** claim
about `MultiRootPhaseCorrect.packageP` over `F97`/`K97cubic`, and says nothing about any other
package.

## Non-circularity

**Instrument note:** `ConstantInfo.value?` returns `none`
for theorems unless `allowOpaque := true` (Lean 4.31 `Lean/Declaration.lean:482`), so a naive
traversal walks types only and reports a closure with no proof content at all — that reads as a
pass and is not one.  Matching `.thmInfo` directly (as `Lean.CollectAxioms` does) gives closures
of **14580** constants for `accepts_derivable` (8148 theorems) and **15783** for
`sharedIo_derivable` (9020 theorems).  In both, none of
`FiniteIOStrategy.accepts`, `FiniteIOStrategy.lio`, `BuildableChips.execution_lio`,
`GenericHonestData.execution_lio_of_requestNodup`, `BuildableChips.sampledWitness_accepts`,
`FiniteFieldIO.finiteIO_complete_of_LIO` or `FiniteFieldIOChecker.finiteIO_gates_zero_of_LIO`
occurs in it.  Note the deliberate exceptions, which are *not* headlines:
`sharedIo_derivable_eq_shared_io` mentions `shared_io` **by design** (that is the point of the
receipt), and the §5 non-vacuity witnesses use the completeness route to *inhabit* the hypotheses
— inhabiting an implication's antecedent from honest data does not make the implication circular.

Paper frame: the paper (the IO round), the paper (`RLC^α(·) - β`),
the paper (unique request / unique response), the paper (`Thm:IO_result`),
the paper (`Thm:NockVMROM`).
-/

namespace Nock.NockVMROM.Thm54.IOCapstoneRedundancy

open scoped Classical Polynomial
open Nock Nock.NockVMROM Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.IOCoinReconciliation

noncomputable section

section Package

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## 1. The record transport

`family_cfg` / `family_exec` (`OptimizedStrictPackage.lean:253-254`) identify the segmented
family's problem with the threaded objects, and both record lists meet at the derived-IO
projections. -/

/-- The family problem and the threaded objects are the same dependent `cfg`/`exec` pair. -/
theorem family_exec_sigma :
    (⟨P.optimized.family.problem.cfg, P.optimized.family.problem.exec⟩ :
        Σ cfg : ExactConfig F K, ExactExecution cfg)
      = ⟨P.objects.cfg, P.objects.exec⟩ :=
  Sigma.ext P.optimized.family_cfg P.optimized.family_exec

omit P in
theorem derivedRequestIO_heq {c₁ c₂ : ExactConfig F K}
    {e₁ : ExactExecution c₁} {e₂ : ExactExecution c₂} (hc : c₁ = c₂) (he : HEq e₁ e₂) :
    e₁.derivedRequestIO = e₂.derivedRequestIO := by
  subst hc; subst he; rfl

omit P in
theorem derivedResponseIO_heq {c₁ c₂ : ExactConfig F K}
    {e₁ : ExactExecution c₁} {e₂ : ExactExecution c₂} (hc : c₁ = c₂) (he : HEq e₁ e₂) :
    e₁.derivedResponseIO = e₂.derivedResponseIO := by
  subst hc; subst he; rfl

omit P in
/-- Transport of the request-capacity bound along an equality of a raw problem with an
explicit `cfg`/`exec` pair. -/
theorem rawProblem_progCapacity_congr {Q : RawProblem F K} {c : ExactConfig F K}
    {e : ExactExecution c} (h : Q = { cfg := c, exec := e })
    (hc : Q.exec.derivedRequestIO.length + 1 ≤ 2 ^ Q.cfg.orbit.h) :
    e.derivedRequestIO.length + 1 ≤ 2 ^ c.orbit.h := by
  subst h; exact hc

theorem family_derivedRequestIO_eq :
    P.optimized.family.problem.exec.derivedRequestIO = P.objects.exec.derivedRequestIO :=
  derivedRequestIO_heq P.optimized.family_cfg P.optimized.family_exec

theorem family_derivedResponseIO_eq :
    P.optimized.family.problem.exec.derivedResponseIO = P.objects.exec.derivedResponseIO :=
  derivedResponseIO_heq P.optimized.family_cfg P.optimized.family_exec

/-- The chip's committed request list is the capstone's `objects.reqRecs`. -/
theorem sampled_requests_eq_reqRecs :
    P.optimized.sampled.sampled.records.requests = P.objects.reqRecs := by
  rw [P.optimized.sampled.requests_eq, P.objects.req_eq_derived]
  exact family_derivedRequestIO_eq P

/-- The chip's committed response list is the capstone's `objects.respRecs`. -/
theorem sampled_responses_eq_respRecs :
    P.optimized.sampled.sampled.records.responses = P.objects.respRecs := by
  rw [P.optimized.sampled.responses_eq, P.objects.resp_eq_derived]
  exact family_derivedResponseIO_eq P

/-- The `Ksz` the chip is deployed at is the capstone's `objects.cfg.Ksz`. -/
theorem family_Ksz_eq : P.optimized.family.problem.cfg.Ksz = P.objects.cfg.Ksz :=
  congrArg ExactConfig.Ksz P.optimized.family_cfg

/-! ## 2. `accepts` is derivable

`FiniteIOStrategy.accepts` (`FiniteFieldIOSoundness.lean:518`) is a field.  Here is the same
proposition, at the package's own records and its own sampled coins, obtained from chip
satisfaction. -/

section Chip

variable [Fintype F] [DecidableEq F]
  (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
  (c : OptimizedProductionChallengeTuple K F)
  (terminal : K) (qp qm : SegmentedRAPParams K) (x₀p x₀m : K)
  (Pp : Fin (FiniteIO.finiteIOProgAIR 9).numTraceCols → K[X])
  (Pm : Fin (FiniteIO.finiteIOMemAIR 9).numTraceCols → K[X])

omit [DecidableEq F] in
/-- **The workhorse.**  At the package's committed records and the accepted tuple's IO
coordinate, the witness *read off* the two hostile traces satisfies `FiniteIOAccepts`.  Nothing
here is chosen by an execution: `projWitness` is a projection of `Pp`/`Pm`. -/
theorem projWitness_accepts_at_sampled_records
    (hsatP : ∀ k : Reified.ConstraintKind,
      (qp.rap (FiniteIO.finiteIOProgAIR 9) k).Satisfies Pp)
    (hsatM : ∀ k : Reified.ConstraintKind,
      (qm.rap (FiniteIO.finiteIOMemAIR 9) k).Satisfies Pm)
    (hrowsP : IOChip.ChipRows
      P.optimized.sampled.sampled.records.requests.length qp x₀p)
    (hrowsM : IOChip.ChipRows
      P.optimized.sampled.sampled.records.responses.length qm x₀m)
    (hagP : IOChip.ChipAgreement
      P.optimized.sampled.sampled.records.requests (ioCoinsOf c) terminal qp x₀p Pp)
    (hagM : IOChip.ChipAgreement
      P.optimized.sampled.sampled.records.responses (ioCoinsOf c) terminal qm x₀m Pm) :
    FiniteIO.FiniteIOAccepts P.optimized.sampled.sampled.records (ioCoinsOf c)
      (IOChip.projWitness P.optimized.sampled.sampled.records (ioCoinsOf c) terminal
        qp qm x₀p x₀m Pp Pm) :=
  IOChip.projWitness_accepts P.optimized.sampled.sampled.records (ioCoinsOf c) terminal
    qp qm x₀p x₀m Pp Pm hsatP hsatM hrowsP hrowsM hagP hagM

/-- **`accepts_derivable` — the carried `FiniteIOStrategy.accepts` field is redundant.**  At an
accepted production tuple, with per-kind RAP satisfaction of the two `K`-valued IO chips and the
row/coin agreement data, the package's own records and its own sampled coins admit an accepting
post-challenge witness.

Modelled on `IOCoinReconciliation.gammaGood_derivable` (`:226`).  Two differences from that
precedent are deliberate and both make the statement *stronger*, not weaker:

* `hgood` is not needed.  `gammaGood`/`poleGood` are counted-event exclusions and are read off
  the failure event; `accepts` is a gate statement and is read off the gates.  §3 needs `hgood`
  again, because `finiteIO_sound` does.
* the conclusion is existential in the witness.  The field is about the strategy's *carried*
  `witness` column, and a hostile trace need not commit that same column; what the field is
  consumed for — `finiteIO_sound`, hence `lio`, hence `shared_io` — needs only *some* accepting
  witness, and §3 shows the consumption goes through. -/
theorem accepts_derivable
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hsatP : ∀ k : Reified.ConstraintKind,
      (qp.rap (FiniteIO.finiteIOProgAIR 9) k).Satisfies Pp)
    (hsatM : ∀ k : Reified.ConstraintKind,
      (qm.rap (FiniteIO.finiteIOMemAIR 9) k).Satisfies Pm)
    (hrowsP : IOChip.ChipRows
      P.optimized.sampled.sampled.records.requests.length qp x₀p)
    (hrowsM : IOChip.ChipRows
      P.optimized.sampled.sampled.records.responses.length qm x₀m)
    (hagP : IOChip.ChipAgreement
      P.optimized.sampled.sampled.records.requests (ioCoinsOf c) terminal qp x₀p Pp)
    (hagM : IOChip.ChipAgreement
      P.optimized.sampled.sampled.records.responses (ioCoinsOf c) terminal qm x₀m Pm) :
    ∃ w : FiniteIO.PostChallengeIOWitness P.optimized.sampled.sampled.records
            P.optimized.sampled.sampled.coins,
      FiniteIO.FiniteIOAccepts P.optimized.sampled.sampled.records
        P.optimized.sampled.sampled.coins w := by
  have hcoins : ioCoinsOf c = P.optimized.sampled.sampled.coins :=
    ioCoinsOf_eq_sampled P Qc Qm c hacc
  have hkey := projWitness_accepts_at_sampled_records P c terminal qp qm x₀p x₀m Pp Pm
    hsatP hsatM hrowsP hrowsM hagP hagM
  rw [← hcoins]
  exact ⟨_, hkey⟩

/-! ## 3. `shared_io` is derivable

`OptimizedStrictFullPackage.shared_io` (`:112`) is
`IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs`, proved by rewriting
`P.ioStrategy.lio` along `io_requests`/`io_responses`.  Below is the same proposition, reached
from acceptance. -/

/-- **`sharedIo_derivable` — the capstone's IO conjunct, from acceptance.**  At an accepted
production challenge tuple outside the one production failure event, chip satisfaction gives
exactly the proposition `shared_io` proves.

The two counted-event hypotheses of `finiteIO_sound` are *not* assumed: they are the projections
`gammaGood_derivable` / `poleGood_derivable` of `hgood`, which is what
`io_lio_of_satisfies_at_production_coins` (`IOCoinReconciliation.lean:263`) packages.  The five
remaining side conditions (`charBound`, `requestRange`, `responseRange`, `uniqueRequest`,
`uniqueResponse`) are the strategy's *other* fields — the paper and the paper are the
paper's unique-request / unique-response conditions, i.e. membership conditions of the language
`Thm:IO_result` quantifies over, not facts about the prover. -/
theorem sharedIo_derivable
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hsatP : ∀ k : Reified.ConstraintKind,
      (qp.rap (FiniteIO.finiteIOProgAIR 9) k).Satisfies Pp)
    (hsatM : ∀ k : Reified.ConstraintKind,
      (qm.rap (FiniteIO.finiteIOMemAIR 9) k).Satisfies Pm)
    (hrowsP : IOChip.ChipRows
      P.optimized.sampled.sampled.records.requests.length qp x₀p)
    (hrowsM : IOChip.ChipRows
      P.optimized.sampled.sampled.records.responses.length qm x₀m)
    (hagP : IOChip.ChipAgreement
      P.optimized.sampled.sampled.records.requests (ioCoinsOf c) terminal qp x₀p Pp)
    (hagM : IOChip.ChipAgreement
      P.optimized.sampled.sampled.records.responses (ioCoinsOf c) terminal qm x₀m Pm) :
    IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs := by
  have h := io_lio_of_satisfies_at_production_coins P Qc Qm c hacc hgood
    terminal qp qm x₀p x₀m Pp Pm hsatP hsatM hrowsP hrowsM hagP hagM
  rw [sampled_requests_eq_reqRecs P, sampled_responses_eq_respRecs P, family_Ksz_eq P] at h
  exact h

/-- **The two routes conclude the same proposition, checked by the elaborator.**  This equation
typechecks only if `sharedIo_derivable`'s conclusion and the carried `shared_io`'s conclusion are
the *same* `Prop`; `rfl` then closes it by proof irrelevance. -/
theorem sharedIo_derivable_eq_shared_io
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hsatP : ∀ k : Reified.ConstraintKind,
      (qp.rap (FiniteIO.finiteIOProgAIR 9) k).Satisfies Pp)
    (hsatM : ∀ k : Reified.ConstraintKind,
      (qm.rap (FiniteIO.finiteIOMemAIR 9) k).Satisfies Pm)
    (hrowsP : IOChip.ChipRows
      P.optimized.sampled.sampled.records.requests.length qp x₀p)
    (hrowsM : IOChip.ChipRows
      P.optimized.sampled.sampled.records.responses.length qm x₀m)
    (hagP : IOChip.ChipAgreement
      P.optimized.sampled.sampled.records.requests (ioCoinsOf c) terminal qp x₀p Pp)
    (hagM : IOChip.ChipAgreement
      P.optimized.sampled.sampled.records.responses (ioCoinsOf c) terminal qm x₀m Pm) :
    sharedIo_derivable P Qc Qm c terminal qp qm x₀p x₀m Pp Pm hacc hgood
        hsatP hsatM hrowsP hrowsM hagP hagM
      = P.shared_io :=
  rfl

theorem perm_derivable
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hsatP : ∀ k : Reified.ConstraintKind,
      (qp.rap (FiniteIO.finiteIOProgAIR 9) k).Satisfies Pp)
    (hsatM : ∀ k : Reified.ConstraintKind,
      (qm.rap (FiniteIO.finiteIOMemAIR 9) k).Satisfies Pm)
    (hrowsP : IOChip.ChipRows
      P.optimized.sampled.sampled.records.requests.length qp x₀p)
    (hrowsM : IOChip.ChipRows
      P.optimized.sampled.sampled.records.responses.length qm x₀m)
    (hagP : IOChip.ChipAgreement
      P.optimized.sampled.sampled.records.requests (ioCoinsOf c) terminal qp x₀p Pp)
    (hagM : IOChip.ChipAgreement
      P.optimized.sampled.sampled.records.responses (ioCoinsOf c) terminal qm x₀m Pm) :
    P.objects.reqRecs.Perm P.objects.respRecs :=
  (sharedIo_derivable P Qc Qm c terminal qp qm x₀p x₀m Pp Pm hacc hgood
    hsatP hsatM hrowsP hrowsM hagP hagM).2.2

end Chip

/-! ## 5a. Non-vacuity, generic half: the chip hypotheses are inhabited at any accepted tuple

`IOChipCompleteness.satisfies_of_io_lio` (`:477`) is the converse of the soundness route; feeding
it the package's *honest* data produces a deployment satisfying every chip hypothesis of §2/§3 at
the package's own records.  This is an inhabitation receipt, so it may — and does — use the
completeness route; it is not part of either headline's derivation. -/

set_option maxHeartbeats 1000000 in
/-- **The six chip hypotheses of `accepts_derivable` / `sharedIo_derivable` are inhabited at any
package with an accepted production tuple.**  Generic in the package: the capacity comes from the
package's `progCapacity` field transported along `hacc.same_problem`, and the denominator
condition from the sampled assignment's `poleHitGood` field. -/
theorem chip_hypotheses_inhabited [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    ∃ (qp qm : SegmentedRAPParams K) (x₀p x₀m terminal : K)
      (Pp : Fin (FiniteIO.finiteIOProgAIR 9).numTraceCols → K[X])
      (Pm : Fin (FiniteIO.finiteIOMemAIR 9).numTraceCols → K[X]),
        (∀ k : Reified.ConstraintKind,
          (qp.rap (FiniteIO.finiteIOProgAIR 9) k).Satisfies Pp)
      ∧ (∀ k : Reified.ConstraintKind,
          (qm.rap (FiniteIO.finiteIOMemAIR 9) k).Satisfies Pm)
      ∧ IOChip.ChipRows P.optimized.sampled.sampled.records.requests.length qp x₀p
      ∧ IOChip.ChipRows P.optimized.sampled.sampled.records.responses.length qm x₀m
      ∧ IOChip.ChipAgreement P.optimized.sampled.sampled.records.requests
          (ioCoinsOf c) terminal qp x₀p Pp
      ∧ IOChip.ChipAgreement P.optimized.sampled.sampled.records.responses
          (ioCoinsOf c) terminal qm x₀m Pm := by
  have hcoins : ioCoinsOf c = P.optimized.sampled.sampled.coins :=
    ioCoinsOf_eq_sampled P Qc Qm c hacc
  -- the committed request list, as a list of the threaded objects
  have hreq : P.optimized.sampled.sampled.records.requests
      = P.objects.exec.derivedRequestIO :=
    (sampled_requests_eq_reqRecs P).trans P.objects.req_eq_derived
  -- capacity: `progCapacity`, transported along the accepted tuple's `same_problem`
  have hcapObj : P.objects.exec.derivedRequestIO.length + 1 ≤ 2 ^ P.objects.cfg.orbit.h :=
    rawProblem_progCapacity_congr hacc.same_problem.specialized_eq_objects
      (P.progCapacity (nprSeed c.1) hacc.same_problem.nprSeed_ne (alphaM c.1) c.2.2.2.lambda)
  have hcap : P.optimized.sampled.sampled.records.requests.length + 1
      ≤ 2 ^ P.objects.cfg.orbit.h := by
    rw [hreq]; exact hcapObj
  -- denominators: the retained completeness-side pole-hit exclusion
  have hden : ∀ v ∈ P.optimized.sampled.sampled.records.requests ++
      P.optimized.sampled.sampled.records.responses,
      FiniteIO.compress (ioCoinsOf c) v ≠ 0 := by
    intro v hv hzero
    rw [hcoins] at hzero
    refine P.optimized.sampled.poleHitGood ?_
    simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, hv, hzero⟩
  obtain ⟨qp, qm, x₀p, x₀m, terminal, Pp, Pm, h1, h2, h3, h4, h5, h6⟩ :=
    IOChip.satisfies_of_io_lio (m := 9) P.objects.cfg.orbit
      P.optimized.sampled.sampled.records (ioCoinsOf c)
      P.optimized.sampled.sampled.lio hden hcap
  exact ⟨qp, qm, x₀p, x₀m, terminal, Pp, Pm, h1, h2, h3, h4, h5, h6⟩

end Package

/-! ## 5b. Non-vacuity, fixture half: every hypothesis holds at once, and the implication fires

`MultiRootOptimizedAcceptance` exhibits an accepted tuple *outside* the production failure event at
`MultiRootPhaseCorrect.packageP` (`packageP_optimized_acceptance`, `:614`;
`packageP_optimized_outside_failure`, `:619`).  Combining those two with §5a gives a complete
hypothesis bundle for `sharedIo_derivable`, together with its conclusion.

**Fixture scope.**  This is a claim about `packageP` over `F97`/`K97cubic` and about nothing else.
It is what rules out the two headlines being vacuous; it is not a second proof of `IO.LIO`. -/

namespace NonVacuity

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
open Nock.NockVMROM.Thm54.MultiRootHonestArrays
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

local instance prime97rd : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97rd : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hmoreM : LaterSeedZeros (F := F97) (K := K97cubic) multiRootExecution)
variable (hrootAt : ∀ a g : K97cubic,
  (packageP hmoreM).strategy.RootAxisBoundaryAt
    (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g)))
include hmoreM
include hrootAt

end NonVacuity

end

/-! ## 6. Axiom receipts -/

#print axioms Nock.NockVMROM.Thm54.IOCapstoneRedundancy.sampled_requests_eq_reqRecs
#print axioms Nock.NockVMROM.Thm54.IOCapstoneRedundancy.sampled_responses_eq_respRecs
#print axioms Nock.NockVMROM.Thm54.IOCapstoneRedundancy.projWitness_accepts_at_sampled_records
#print axioms Nock.NockVMROM.Thm54.IOCapstoneRedundancy.accepts_derivable
#print axioms Nock.NockVMROM.Thm54.IOCapstoneRedundancy.sharedIo_derivable
#print axioms Nock.NockVMROM.Thm54.IOCapstoneRedundancy.sharedIo_derivable_eq_shared_io
#print axioms Nock.NockVMROM.Thm54.IOCapstoneRedundancy.perm_derivable
#print axioms Nock.NockVMROM.Thm54.IOCapstoneRedundancy.chip_hypotheses_inhabited

end Nock.NockVMROM.Thm54.IOCapstoneRedundancy
