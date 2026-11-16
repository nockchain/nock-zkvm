import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.IOChipSoundness
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.PairedRecordCountedEvent
import Nock.NockVMROM.Thm54.ComputeStagedTable
import Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
import Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Which coins the `K`-valued IO chip consumes

`IOChipSoundness.io_lio_of_satisfies` (`:408`) closes the hostile direction of the sampled-IO
LogUp argument at an *abstract* `coins : FiniteIO.IOCoins K`, outside two counted events.  This
module answers the question that theorem leaves open: **which verifier randomness is `coins`?**

## The paper settles it: the pole is sampled

`RAP_prog-IO` is built in four steps.  Step 2 sends `Com(IO_prog)`; step 3 is
"Verifier responds with random elements `α, β ∈ 𝕂`"; step 4 builds `acc_prog`.
The role of that `β` is fixed by the aggregation constraint, which multiplies factors
`RLC^α(IO_prog(i,k,·)) - β` — i.e. it is exactly the
log-derivative denominator `RLC^Y(·) + X` of `𝓛_LDSE` at `Y ↦ α`,
`X ↦ -β`, and `Lem:ldse_mse` is stated in the rational function field
`𝔽(X, Y)`, formal in both variables.  So `β` **is** the LogUp pole, and the paper draws it as
verifier randomness:

* the paper — the memory IO trace "is parametrized by the **random** extension field
  elements `α, β`";
* the paper — "the terminal output `out_prog` and **randomness** `α, β` of the computation
  table";
* the paper — the cost of `RAP_prog-IO` is "One round of interaction, providing two random
  elements in `𝕂`".

The memory side does not resample: the paper obtains `α, β` "from the computation table's
`w_prog-IO` array", and the paper gives `RAP_mem-IO` `e + 1` columns and **no** round of its
own.  One round, two coins, shared by both IO chips — which is exactly the shape of
`FiniteIO.IOCoins` (`FiniteFieldIO.lean:55`) and of the `PreChallengeRecords → IOCoins →
PostChallengeIOWitness` chronology it sits in.

**Verdict: sampled, not substituted.**  `hpole` is to be discharged by a counted-event argument
over a fresh sample, not by a substitution receipt against an already-drawn coin.

## The tree already samples them, and already pins them

`OptimizedProductionChallengeTuple K F` (`OptimizedStrictPackage.lean:554`) is

    JointCoins K × ((K × K) × (FinalComputeChallengeTuple K × MemoryChallengeTuple K F))

whose **second** coordinate is a free `K × K` reserved for the IO round.  `liftIOFailure`
(`OptimizedStrictPackage.lean:583`) embeds `Finset (K × K)` there, `OptimizedProductionFailureEvent`
(`OptimizedStrictPackage.lean:604`) folds in `liftIOFailure (FiniteIO.IOFailureEvent records)`, and
`optimizedProductionFailureProbabilityBound` (`OptimizedStrictPackage.lean:632`) charges it as
`ioWork / cardK ^ 2` — a two-coin sample, matching the paper.

And the identification is already a *conjunct of acceptance*:
`OptimizedHistoricalAcceptanceAt.sampled_io_coins`
(`OptimizedStrictFullPackage.lean:414`, field of the structure at `:407`) states

    c.2.1 = (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole).

So the honest identification is **neither** of the two candidates one might reach for: not
`interCoins` (§3), and not a new slot of the eight-coin `nockChronology` (§4) — it is the
production tuple's own IO coordinate.  What was missing is the receipt composing that field with
the failure-event projection so that `io_lio_of_satisfies`' two hypotheses are *derived* rather
than assumed.  §2 supplies it.

## What this does and does not buy

`FiniteIO.FiniteIOStrategy` carries `gammaGood`/`poleGood` as **fields**
(`FiniteFieldIOSoundness.lean:530`, `:532`).  §2 shows those two fields are redundant for a
package whose production tuple is accepted and outside the one production failure event: the
exclusions follow from the sampled coordinate.  That is the whole content of "the coins are
verifier randomness of the assembled RAP" — the exclusions are priced against `|K|²`, not
postulated.

It does **not** claim the giga-RAP reads these coins.  `Trans.ioProgAIR`/`ioMemAIR`, which
`ComputeChip.computeCombinedAIR` folds, have `numChallenges = 0`
(`Nock/Counts.lean:155`, `:162`); the `K`-valued chips
`finiteIOProgAIR`/`finiteIOMemAIR` have `numChallenges = 2` each
(`FiniteFieldIOAIR.lean:172`, `:178`) and are not folded into it.
-/

namespace Nock.NockVMROM.Thm54.IOCoinReconciliation

open scoped Classical Polynomial
open Nock Nock.NockVMROM Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

noncomputable section

/-! ## 1. The IO coordinate of the production challenge tuple -/

variable {F K : Type} [Fintype F] [Fintype K]

/-- **The IO coordinate, read as `IOCoins`.**  the paper sends two elements in one message
and the paper prices exactly that; the production tuple's second coordinate is the `K × K`
they land in, with `gamma` the RLC coefficient and `pole` the offset. -/
def ioCoinsOf (c : OptimizedProductionChallengeTuple K F) : FiniteIO.IOCoins K :=
  ⟨c.2.1.1, c.2.1.2⟩

/-- Overwrite only the IO coordinate. -/
def withIOCoins (c : OptimizedProductionChallengeTuple K F) (x : FiniteIO.IOCoins K) :
    OptimizedProductionChallengeTuple K F :=
  (c.1, ((x.gamma, x.pole), c.2.2))

@[simp] theorem ioCoinsOf_withIOCoins (c : OptimizedProductionChallengeTuple K F)
    (x : FiniteIO.IOCoins K) : ioCoinsOf (withIOCoins c x) = x := rfl

@[simp] theorem withIOCoins_p8 (c : OptimizedProductionChallengeTuple K F)
    (x : FiniteIO.IOCoins K) : (withIOCoins c x).1 = c.1 := rfl

@[simp] theorem withIOCoins_rest (c : OptimizedProductionChallengeTuple K F)
    (x : FiniteIO.IOCoins K) : (withIOCoins c x).2.2 = c.2.2 := rfl

@[simp] theorem ioCoinsOf_pair (c : OptimizedProductionChallengeTuple K F) :
    ((ioCoinsOf c).gamma, (ioCoinsOf c).pole) = c.2.1 := rfl

/-- **The IO pole is a free coordinate, i.e. genuinely sampled.**  This is the Lean form of "sampled, not derived": nothing in the other three
coordinates constrains it. -/
theorem ioCoins_free (c : OptimizedProductionChallengeTuple K F) (x : FiniteIO.IOCoins K) :
    ∃ c' : OptimizedProductionChallengeTuple K F,
      c'.1 = c.1 ∧ c'.2.2 = c.2.2 ∧ ioCoinsOf c' = x :=
  ⟨withIOCoins c x, rfl, rfl, rfl⟩

/-- Membership of the lifted IO failure event is a condition on the IO coordinate alone. -/
theorem mem_liftIOFailure_iff [DecidableEq F] [DecidableEq K]
    (bad : Finset (K × K)) (c : OptimizedProductionChallengeTuple K F) :
    c ∈ liftIOFailure (K := K) (F := F) bad
      ↔ ((ioCoinsOf c).gamma, (ioCoinsOf c).pole) ∈ bad := by
  simp [liftIOFailure, ioCoinsOf]

/-- The three components of `IOFailureEvent`, split at a coin pair.  (Same statement as the
fixture-local `TraceGen.Op8InputsK3.not_mem_ioFailure_components`, reproved here so this module
does not depend on a fixture.) -/
theorem notMem_ioFailure_components [Field K] [DecidableEq K] {n : ℕ}
    {records : FiniteIO.PreChallengeRecords K n} {γ pol : K}
    (h : (γ, pol) ∉ FiniteIO.IOFailureEvent records) :
    pol ∉ FiniteIO.IOPoleHitEvent records γ
      ∧ γ ∉ FiniteIO.IORLCCollisionEvent records
      ∧ pol ∉ FiniteIO.IOLogDerivEvent records γ := by
  simp only [FiniteIO.IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    not_or] at h
  exact ⟨h.2.1, h.1, h.2.2⟩

end

/-! ## 2. The receipt: the chip's coins are the tuple's IO coordinate

`OptimizedHistoricalAcceptanceAt.sampled_io_coins` (`OptimizedStrictFullPackage.lean:414`) pins
the tuple's IO coordinate to the package's sampled coins, and
`optimizedFailureEvent_good_components` (`OptimizedStrictFullPackage.lean:605`) projects the one
production failure event onto that coordinate.  Composing them *derives* the two exclusions that
`FiniteIO.FiniteIOStrategy` carries as fields, and hence the two counted-event hypotheses of
`IOChipSoundness.io_lio_of_satisfies`.
-/

section Production

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- **The identification.**  Under production acceptance, the `IOCoins` the `K`-valued chip is
deployed at *is* the IO coordinate of the accepted production challenge tuple.  This is the
`IOCoins` analogue of `TemplateRawJointSoundness.Strategy.sampledCoordinates` (`:288`) for the
`JointCoins` coordinates. -/
theorem ioCoinsOf_eq_sampled
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    ioCoinsOf c = P.optimized.sampled.sampled.coins := by
  have h := hacc.sampled_io_coins
  unfold ioCoinsOf
  rw [h]

/-- **The sampled coin pair is outside the whole three-part IO event.**  Read off the production
failure event at the accepted tuple — not postulated on the strategy. -/
theorem sampled_coins_notMem_ioFailure
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (_hgood : c ∉ P.optimizedFailureEvent Qc Qm) :
    (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole)
      ∉ FiniteIO.IOFailureEvent P.optimized.sampled.sampled.records := by
  have hio := P.sampled_io_event_good_of_historical Qc Qm c hacc
  rw [hacc.sampled_io_coins] at hio
  exact hio

/-- **The two counted-event hypotheses of `io_lio_of_satisfies`, derived.**  Plus the pole-hit
component, which the same projection delivers for free.

This is what "`coins` is verifier-sampled randomness of the assembled RAP" means operationally:
`hγ` and `hpole` are consequences of the accepted tuple lying outside one counted event in a coin
space that contains a free `K × K` for the IO round, so they are priced at `|K|²`
(`optimizedProductionFailureProbabilityBound`'s `ioWork / cardK ^ 2`) rather than assumed. -/
theorem sampled_coins_good
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm) :
    P.optimized.sampled.sampled.coins.gamma
        ∉ FiniteIO.IORLCCollisionEvent P.optimized.sampled.sampled.records
      ∧ P.optimized.sampled.sampled.coins.pole
        ∉ FiniteIO.IOLogDerivEvent P.optimized.sampled.sampled.records
            P.optimized.sampled.sampled.coins.gamma
      ∧ P.optimized.sampled.sampled.coins.pole
        ∉ FiniteIO.IOPoleHitEvent P.optimized.sampled.sampled.records
            P.optimized.sampled.sampled.coins.gamma := by
  have h := notMem_ioFailure_components
    (sampled_coins_notMem_ioFailure P Qc Qm c hacc hgood)
  exact ⟨h.2.1, h.2.2, h.1⟩

/-- The strategy's own `gammaGood` field is redundant at an accepted, good tuple. -/
theorem gammaGood_derivable
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm) :
    P.optimized.sampled.sampled.coins.gamma
      ∉ FiniteIO.IORLCCollisionEvent P.optimized.sampled.sampled.records :=
  (sampled_coins_good P Qc Qm c hacc hgood).1

/-- The strategy's own `poleGood` field is redundant at an accepted, good tuple. -/
theorem poleGood_derivable
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm) :
    P.optimized.sampled.sampled.coins.pole
      ∉ FiniteIO.IOLogDerivEvent P.optimized.sampled.sampled.records
          P.optimized.sampled.sampled.coins.gamma :=
  (sampled_coins_good P Qc Qm c hacc hgood).2.1

/-! ## 3. End to end: hostile committed traces plus an accepted, good tuple give `IO.LIO`

`IOChipSoundness.io_lio_of_satisfies` (`:408`) with its two counted-event hypotheses replaced by
"the accepted production tuple lies outside the one production failure event".  Everything else is
unchanged: the traces `Pp`, `Pm` are arbitrary, the witness is still read off them by
`projWitness`, and the range/uniqueness side conditions come from the package's own sampled
strategy (`FiniteIOStrategy` fields, `FiniteFieldIOSoundness.lean:520-528`).
-/

/-- **Headline.**  At an accepted production challenge tuple outside the production failure event,
any pair of committed traces satisfying the kind-segmented ordinary RAPs of the two `K`-valued IO
chips, agreeing with the package's sampled records and *its own IO coordinate*, implies the
record-level IO language `IO.LIO` — and hence `requests.Perm responses`.

The coins are not a parameter here: they are `ioCoinsOf c`, and `ioCoinsOf_eq_sampled` identifies
them with the chip's deployment coins. -/
theorem io_lio_of_satisfies_at_production_coins
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (terminal : K) (qp qm : SegmentedRAPParams K) (x₀p x₀m : K)
    (Pp : Fin (FiniteIO.finiteIOProgAIR 9).numTraceCols → K[X])
    (Pm : Fin (FiniteIO.finiteIOMemAIR 9).numTraceCols → K[X])
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
    IO.LIO P.optimized.family.problem.cfg.Ksz
      P.optimized.sampled.sampled.records.requests
      P.optimized.sampled.sampled.records.responses := by
  have hcoins : ioCoinsOf c = P.optimized.sampled.sampled.coins :=
    ioCoinsOf_eq_sampled P Qc Qm c hacc
  have hg := sampled_coins_good P Qc Qm c hacc hgood
  refine IOChip.io_lio_of_satisfies (p := ringChar K)
    (Ksz := P.optimized.family.problem.cfg.Ksz)
    P.optimized.sampled.sampled.records (ioCoinsOf c) terminal qp qm x₀p x₀m Pp Pm
    hsatP hsatM hrowsP hrowsM hagP hagM
    P.optimized.sampled.sampled.charBound
    P.optimized.sampled.sampled.requestRange
    P.optimized.sampled.sampled.responseRange
    P.optimized.sampled.sampled.uniqueRequest
    P.optimized.sampled.sampled.uniqueResponse
    ?_ ?_
  · rw [hcoins]; exact hg.1
  · rw [hcoins]; exact hg.2.1

theorem perm_of_satisfies_at_production_coins
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (terminal : K) (qp qm : SegmentedRAPParams K) (x₀p x₀m : K)
    (Pp : Fin (FiniteIO.finiteIOProgAIR 9).numTraceCols → K[X])
    (Pm : Fin (FiniteIO.finiteIOMemAIR 9).numTraceCols → K[X])
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
    P.optimized.sampled.sampled.records.requests.Perm
      P.optimized.sampled.sampled.records.responses :=
  (io_lio_of_satisfies_at_production_coins P Qc Qm c hacc hgood terminal qp qm x₀p x₀m
    Pp Pm hsatP hsatM hrowsP hrowsM hagP hagM).2.2

end Production

/-! ## 4. Why `interCoins` is **not** the identification, and what `β = 0` costs

`PairedRecordCountedEvent.interCoins` (`:210`) is `⟨γ, -β⟩`, read off the memory table's own
`(z, β, γ)` tuple.  Its disclosure receipt
`interCoins_is_the_table_pole_not_the_io_sample` (`PairedRecordCountedEvent.lean:243`) says it is
a different object from the `RAP_prog-IO` sample of the paper and that no theorem identifies
them.  **That receipt is correct and this module upholds it**, for two independent reasons.

*Paper.*  `interCoins`' pole is the pole of the memory table's **internal** `intermediate`
accumulator, whose record pair is
`(IO, intermediate)` *inside one table*.  the paper says that chip's
constraints are "implemented in the exact same way as in `RAP_mem-IO`, `RAP_comp-IO`" — the same
*technique*, a **separate instance**.  The external chip's records are the compute/memory record
lists matched *across* the two tables.  Two instances of `Thm:IO_result`, two
pole coins.

*Lean.*  The IO coordinate of the production tuple is free (`ioCoins_free`, §1), so no constraint
on the other three coordinates can pin it to `interCoins E`; `exists_tuple_io_ne_interCoins`
exhibits that.

`interCoins_logDeriv_is_a_fixed_point_test` states exactly that.  A configuration
pinning `β = 0` therefore cannot serve as the external IO chip's pole — which is why the
production route samples a separate `K × K` instead.
-/

section InterCoins

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- `β = 0` forces the `intermediate` chip's pole to the constant `0`. -/
theorem interCoins_pole_eq_zero (E : BuildableNockExecution F K)
    (hβ : E.cfg.challenges.β = 0) :
    (PairedRecordCountedEvent.interCoins E).pole = 0 := by
  show -E.cfg.challenges.β = 0
  rw [hβ, neg_zero]

/-- **What `β = 0` costs.**  Compare `sampled_coins_good` (§2), where the same exclusion is
bought from a free `K × K` coordinate and priced at `|K|²`. -/
theorem interCoins_logDeriv_is_a_fixed_point_test (E : BuildableNockExecution F K)
    (hβ : E.cfg.challenges.β = 0)
    {n : ℕ} (records : FiniteIO.PreChallengeRecords K n) :
    ((PairedRecordCountedEvent.interCoins E).pole
        ∉ FiniteIO.IOLogDerivEvent records
            (PairedRecordCountedEvent.interCoins E).gamma)
      ↔ (FiniteIO.ioQP records E.cfg.challenges.γ ≠ 0 →
          (FiniteIO.ioQP records E.cfg.challenges.γ).eval 0 ≠ 0) := by
  have hpole : (PairedRecordCountedEvent.interCoins E).pole = 0 :=
    interCoins_pole_eq_zero E hβ
  have hgamma : (PairedRecordCountedEvent.interCoins E).gamma = E.cfg.challenges.γ := rfl
  rw [hpole, hgamma]
  simp only [FiniteIO.IOLogDerivEvent, Finset.mem_filter, Finset.mem_univ, true_and, not_and]

/-- Both `interCoins` components are constants when the configuration pins `β` and `γ`.  This is
the shape of `TraceGen.GenTierAConfig769.cfg` (`:88`, `challenges := { …, β := 0, γ := 0 }`) — a
**fixture** claim about that configuration, never a claim about an arbitrary honest execution. -/
theorem interCoins_eq_zero_of_pinned (E : BuildableNockExecution F K)
    (hβ : E.cfg.challenges.β = 0) (hγ : E.cfg.challenges.γ = 0) :
    PairedRecordCountedEvent.interCoins E = ⟨0, 0⟩ := by
  have h1 : (PairedRecordCountedEvent.interCoins E).gamma = 0 := hγ
  have h2 : (PairedRecordCountedEvent.interCoins E).pole = 0 :=
    interCoins_pole_eq_zero E hβ
  cases hc : PairedRecordCountedEvent.interCoins E with
  | mk g pol =>
      rw [hc] at h1 h2
      simp_all

/-- So `interCoins E = ioCoinsOf c` is not derivable, which is the disclosure
receipt `PairedRecordCountedEvent.interCoins_is_the_table_pole_not_the_io_sample` (`:243`) turned
into an obstruction rather than an absence. -/
theorem exists_tuple_io_ne_interCoins [Fintype F] (E : BuildableNockExecution F K)
    (c : OptimizedProductionChallengeTuple K F) :
    ∃ c' : OptimizedProductionChallengeTuple K F,
      c'.1 = c.1 ∧ c'.2.2 = c.2.2
        ∧ ioCoinsOf c' ≠ PairedRecordCountedEvent.interCoins E := by
  refine ⟨withIOCoins c
    ⟨(PairedRecordCountedEvent.interCoins E).gamma + 1,
      (PairedRecordCountedEvent.interCoins E).pole⟩, rfl, rfl, ?_⟩
  intro h
  have := congrArg FiniteIO.IOCoins.gamma h
  simp only [ioCoinsOf_withIOCoins] at this
  exact one_ne_zero (by linear_combination this)

end InterCoins

/-! ## 5. The bookkeeping that is genuinely absent: the staged chronology has no IO slot

`GigaChips.nockChronology` (`ComputeStagedTable.lean:203`) declares **eight** coins over three
column blocks, and its own module table names all eight: `α, z, a, b, c, α_C, β, γ`.  Slots `6`
and `7` are the memory table's `β` and `γ` — i.e. the two components of `interCoins` — so **none
of the eight is the `RAP_prog-IO` pair of the paper **.  That is a bookkeeping gap in the
staged-chronology object only: the *production* challenge space does carry the pair (§1-§3), and
the round-stratified soundness bound does price it.

`nockChronologyWithIO` is the smallest sound fix: two further coins, in the **final** round.  The
round is forced from both sides by the paper — the coins come after `Com(IO_prog)`, so
they are not usable by the columns of the block that commits `IO_prog`, and they come before
`acc_prog`, so they are usable by the columns of the next block.  In this tree's three-block
schedule that is round `1`, alongside `α, α_C, β, γ`; the accumulators live in block `2`.

This is a proposal, not a landed rewiring: `Gen.lean` and `ComputeStagedTable.lean` are untouched
and `ComputeChip.computeCombinedAIR` still folds the symbolic `ioProgAIR`/`ioMemAIR`
(`numChallenges = 0`, `Nock/Counts.lean:155`, `:162`).
-/

namespace Chronology

open Nock.NockVMROM.Thm54.Staging
open Nock.NockVMROM.Thm54.GigaChips

/-- The eight-coin schedule of `nockChronology`, extended by the two `RAP_prog-IO` coins in the
final round. -/
def nockSampledAfterWithIO : Fin 10 → Fin 3 := ![1, 0, 0, 0, 0, 1, 1, 1, 1, 1]

/-- **The ten-coin chronology.**  Same three blocks, same two verifier messages; the IO round's
two elements join the final message. -/
def nockChronologyWithIO : ChallengeChronology 3 where
  numChallenges := 10
  sampledAfter := nockSampledAfterWithIO

/-- The IO record-RLC coin — the paper's `RLC^α`, this tree's `IOCoins.gamma`. -/
def ioGammaSlot : Fin 10 := ⟨8, by norm_num⟩
/-- The IO pole coin — the paper's `- β`, this tree's `IOCoins.pole`. -/
def ioPoleSlot : Fin 10 := ⟨9, by norm_num⟩

/-- The eight old slots, in place. -/
def embed8 (j : Fin 8) : Fin 10 := Fin.castLE (by norm_num) j

@[simp] theorem withIO_numChallenges : nockChronologyWithIO.numChallenges = 10 := rfl

/-- The extension restricts to `nockSampledAfter` on the eight existing coins: no existing coin
changes round. -/
theorem withIO_restricts (j : Fin 8) :
    nockSampledAfterWithIO (embed8 j) = nockSampledAfter j := by
  revert j; decide

/-- **The two IO coins are new slots.**  Neither is any of the eight coins `nockChronology`
declares — in particular neither is slot `6` (`β`) nor slot `7` (`γ`), the two components of
`PairedRecordCountedEvent.interCoins`. -/
theorem ioSlots_are_new (j : Fin 8) :
    embed8 j ≠ ioGammaSlot ∧ embed8 j ≠ ioPoleSlot := by
  revert j; decide

/-- Stated at the two slots the wrong identification would have used. -/
theorem ioSlots_ne_memory_slots :
    embed8 gammaSlot ≠ ioGammaSlot ∧ embed8 betaSlot ≠ ioPoleSlot := by
  decide

/-- Both IO coins ride the final verifier message. -/
theorem ioSlots_final_round :
    nockSampledAfterWithIO ioGammaSlot = 1 ∧ nockSampledAfterWithIO ioPoleSlot = 1 :=
  ⟨rfl, rfl⟩

/-- Six coins in the final message instead of four; the four round-`0` coins are unchanged. -/
theorem withIO_fibres :
    (Finset.univ.filter fun j : Fin 10 => nockSampledAfterWithIO j = 1).card = 6 ∧
      (Finset.univ.filter fun j : Fin 10 => nockSampledAfterWithIO j = 0).card = 4 :=
  ⟨rfl, rfl⟩

/-- **The chronology condition the round assignment encodes.**  The IO coins are *not* usable by
the columns of the block that commits `IO_prog`, and they *are* usable by the columns of the next block, which is where `acc_prog` lives. -/
theorem ioSlots_commit_then_sample :
    ¬ nockChronologyWithIO.usableByColumnOf 1 ioPoleSlot
      ∧ nockChronologyWithIO.usableByColumnOf 2 ioPoleSlot
      ∧ ¬ nockChronologyWithIO.usableByColumnOf 1 ioGammaSlot
      ∧ nockChronologyWithIO.usableByColumnOf 2 ioGammaSlot := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end Chronology


/-! ## 6. Non-vacuity of the identification, at one compiled fixture

`OptimizedHistoricalAcceptanceAt` is inhabited: `DistinctCensusPhaseCorrect`'s
`packageQ_optimized_acceptance` (`:708`) proves it at the canonical traces and tuple for every
`a g : K97cubic`.  So §2's `hacc` — and with it the `sampled_io_coins` field the identification
rests on — is not an empty hypothesis.

This is a **fixture** claim about `packageQ` over `F97`/`K97cubic`, never a claim about an
arbitrary package.  `packageQ` is moreover the *false-acceptance* fixture (accepted, not a genuine
target), so it inhabits `hacc` only; it does not inhabit `hgood`, and §3's headline is not
instantiated here.
-/

namespace NonVacuity

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
open Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

local instance prime97io : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
include hfirstD

/-- The identification, at `packageQ`: the accepted tuple's IO coordinate is the package's
sampled IO coins.  Fixture scope (`F97`, `K97cubic`). -/
theorem ioCoinsOf_eq_sampled_at_packageQ
    (hrootAt : ∀ a g : K97cubic,
      (packageQ hfirstD).strategy.RootAxisBoundaryAt
        (nprSeed (coinQ a g)) seedH_ne
        (alphaM (coinQ a g)))
    (hax : FormRAxisBound (packageQ hfirstD).optimized.sampled (packageQ hfirstD).optimized.basis)
    (hbasis : FormRBasis (packageQ hfirstD).optimized.basis)
    (hwidth : FormRWidth F97)
    (a g : K97cubic) :
    ioCoinsOf (tupleQ hfirstD a g) = (packageQ hfirstD).optimized.sampled.sampled.coins :=
  ioCoinsOf_eq_sampled (packageQ hfirstD) (computeTraceQ hfirstD) (memoryTraceQ hfirstD)
    (tupleQ hfirstD a g) (packageQ_optimized_acceptance hfirstD hrootAt a g hax hbasis hwidth)

end NonVacuity


/-! ## 7. Axiom receipts -/

#print axioms Nock.NockVMROM.Thm54.IOCoinReconciliation.ioCoins_free
#print axioms Nock.NockVMROM.Thm54.IOCoinReconciliation.ioCoinsOf_eq_sampled
#print axioms Nock.NockVMROM.Thm54.IOCoinReconciliation.sampled_coins_notMem_ioFailure
#print axioms Nock.NockVMROM.Thm54.IOCoinReconciliation.sampled_coins_good
#print axioms Nock.NockVMROM.Thm54.IOCoinReconciliation.io_lio_of_satisfies_at_production_coins
#print axioms Nock.NockVMROM.Thm54.IOCoinReconciliation.perm_of_satisfies_at_production_coins
#print axioms Nock.NockVMROM.Thm54.IOCoinReconciliation.interCoins_logDeriv_is_a_fixed_point_test
#print axioms Nock.NockVMROM.Thm54.IOCoinReconciliation.exists_tuple_io_ne_interCoins
#print axioms Nock.NockVMROM.Thm54.IOCoinReconciliation.Chronology.ioSlots_are_new
#print axioms Nock.NockVMROM.Thm54.IOCoinReconciliation.Chronology.ioSlots_commit_then_sample
#print axioms Nock.NockVMROM.Thm54.IOCoinReconciliation.NonVacuity.ioCoinsOf_eq_sampled_at_packageQ


end Nock.NockVMROM.Thm54.IOCoinReconciliation
