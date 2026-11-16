import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.GigaRAPThirdMessage
import Nock.NockVMROM.Thm54.GigaRAPAssembledWitness
import Nock.NockVMROM.Thm54.GenuineEvalN
import Nock.NockVMROM.Thm54.SaturatedDeclaration
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# The production path, moved onto the chips whose schedule *forces* the IO-coin exclusion

`GigaRAPThirdMessage.lean` builds `computeChip3` / `memoryChip3` (`:353`, `:362`) over the
paper's **three**-message chronology `nockChronologyIO3` (`:131`) and proves
`committed_early_excludes_the_io_coins_compute` (`:435`) and its memory twin (`:442`): for *any*
`StagedChip K 4 nockChronologyIO3` whose `IO_prog` columns are committed by round `2`
(the paper's `Com(IO_prog)`), neither `RAP_prog-IO` coin is declared at
those columns.  That is a consequence of `StagedChip.columns_commit_before_sampling`
(`StagedTableRAP.lean:174`), i.e. of the structure obligation every chip carries, and not of a
chosen `columnChallenges`.

**But that enforcement did not reach the composition.**
`GigaIOSlots.io_lio_of_giga_satisfies_at_production_coins` (`GigaRAPIOSlots.lean:963`) — the only
theorem in the tree that consumes `OptimizedHistoricalAcceptanceAt` together with assembled-chip
satisfaction — still runs at `finiteComputeChip canonicalIOSlots qC` / `finiteMemoryChip
canonicalIOSlots qM`, the **two**-message chips, at which (as those chips' own docstrings now say)
the exclusion at columns `111` / `52` is a declaration rather than a consequence.  So the enforced
chips and the composed chips were different objects.

This module closes that: it ports the production-coin layer to `computeChip3` / `memoryChip3`,
states the whole chain as one theorem, and records what is left assumed.

## What is here

1. **§1 — the production-coin composition at the enforced chips.**

2. **§2 — the chain as one theorem.**  `accepted_giga3_certifies_io_perm_and_evalN` takes a
   package `P`, an accepted tuple `c` outside the failure event, satisfaction of the two
   three-message chips, and the `ChipRows`/`ChipAgreement` data, and concludes *six* things at
   once: `IO.LIO`, `requests.Perm responses`, the genuine `Nock.evalN` evaluation of the committed
   claim, the two counted-event exclusions (derived, via
   `IOCoinReconciliation.sampled_coins_good`, `:208`), and the two **forced** coin exclusions at
   the `IO_prog` record columns of the very chips whose satisfaction was hypothesised.  The last
   two conjuncts are what makes this the *enforced* chain rather than the declared one: they are
   `committed_early_excludes_the_io_coins_compute`/`_memory` instantiated at `computeChip3Sat` /
   `memoryChip3Sat`, whose schedule condition is discharged by `decide` (§4).  At the saturated
   chips those conjuncts are strictly stronger than at the shipped ones, because the declaration
   they quantify over is the larger, schedule-legal set; `giga3_io_columns_undeclared` carries
   both readings.

3. **§3 — non-vacuity.**  `canonicalPlacement3.map = canonicalIOSlots.map` by `rfl`
   (`GigaRAPThirdMessage.lean:227`) and `canonical3_satisfies_iff` (`:587`) is `Iff.rfl`, so
   `GigaWitness.giga_bundle_at_production_coins` (`GigaRAPAssembledWitness.lean:936`) transports
   verbatim.  `giga3_composition_roundtrip_at_package_orbit` re-derives the headline's `IO.LIO`
   conclusion from a bundle that is *built*, with no orbit hypothesis, so the hypothesis list of
   §1 is simultaneously satisfiable.

3.5. **§2.5 — what the saturated chips cost and bought.**  On the `Satisfies` hypotheses the
   re-pointing is a definitional no-op (`giga3_satisfaction_is_the_same_proposition`, `Iff.rfl`):
   `Satisfies` reads `air` and `params`, `saturate` touches only `columnChallenges`, and this
   module quantifies over no `RoundFibred.StagedAssignment` at all, so there was no prover class
   here for saturation to shrink.  On conjuncts (5)/(6) it is a strengthening over an object
   nobody chose: `giga3_production_chips_are_unique`.

4. **§4 — what is left assumed.**  Two items, and one of them turns out to be discharged: the
   schedule condition `ProgIORecordsCommittedByRoundTwo` / `MemIORecordsCommittedByRoundTwo`
   (`GigaRAPThirdMessage.lean:393`, `:399`) is a *theorem* about `computeChip3` / `memoryChip3`
   (`schedule_conditions_are_discharged`), so it is a hypothesis only of the generic statements
   about hostile chips; and `RoundFibred.StagedAssignment.col_reads`
   (`RoundFibredSoundness.lean:563`) is carried, named, and shown non-promotable with no
   hypotheses left (`col_reads_receipt_is_inhabited`).

5. **§5 — the receipt that the migration was necessary.**
   `two_message_exclusion_is_a_choice_three_message_is_not` compiles the sentence
   `GigaRAPThirdMessage.lean:27-32` only asserted in prose: `hostileComputeChip` /
   `hostileMemoryChip` are second, equally legal `StagedChip`s over the two-message chronology
   with the *identical* AIR, params and schedule as `finiteComputeChip` / `finiteMemoryChip`,
   whose satisfaction is the same proposition by `Iff.rfl`, and which **do** declare both
   `RAP_prog-IO` coins at columns `111` / `52`; while over `nockChronologyIO3` no chip meeting
   the paper's schedule condition can.  Without this the claim "the two-message exclusion is
   a choice" is itself unbacked.

The obvious way for this migration to fail would be for the production coin identification to
read the ten-slot chronology.  It does not, and the reason is that `ioCoinsOf`
(`IOCoinReconciliation.lean:102`) and `OptimizedHistoricalAcceptanceAt.sampled_io_coins`
(`OptimizedStrictFullPackage.lean:414`) live in a **different coin space** from the chips'.  The
chips' coins are the `Fin chronology.numChallenges → K` argument of a `StagedAssignment`; the
production coins are the `K × K` second coordinate of
`OptimizedProductionChallengeTuple K F` (`OptimizedStrictPackage.lean:554`), and `ioCoinsOf` is
literally `⟨c.2.1.1, c.2.1.2⟩`.  Neither mentions `nockChronologyWithIO`, `nockChronologyIO3`,
`numChallenges`, or any slot index.  The bridge between the two spaces is
`IOChip.ChipAgreement.gamma_eq`/`pole_eq` (`IOChipSoundness.lean:165`), which under
`remapParams q S.map` unfolds to `q.chalVal (S.slot 0) = coins.gamma` and
`q.chalVal (S.slot 1) = coins.pole` (`GigaIOSlots.chipAgreement_names_the_slots`,
`GigaRAPIOSlots.lean:904`) — a hypothesis of both the two- and the three-message compositions,
and one that names `S.slot i` generically.  So `ioCoinsOf` and `sampled_io_coins` apply verbatim
at `nockChronologyIO3`, and both chronologies happen to have `numChallenges = 10` anyway
(`GigaRAPThirdMessage.io3_numChallenges`, `:135`).

## What did **not** move

The two-message theorems of `GigaRAPIOSlots.lean` are untouched and still compile.  Nothing here
deletes or weakens them; the point is only that the composition a reader should consume is this
one.

`SaturatedDeclaration.lean` used to `import` this module; it used nothing from it but four
docstring mentions, so the edge was dropped and this module imports it instead.  That is what lets
§1-§2 name the saturated chips at all.  The prose references to
`GigaIOThirdMessageProduction.two_message_exclusion_is_a_choice_three_message_is_not` in
`SaturatedDeclaration.lean` are now forward references, and are prose only.

## Where this module is imported from

The line
`import Nock.NockVMROM.Thm54.GigaRAPThirdMessageProduction` belongs after `Thm54.lean:243`
(`import Nock.NockVMROM.Thm54.GenuineEvalN`) whenever that file is next edited.  (Note that
`GigaRAPThirdMessage.lean:92-95`'s claim that *it* is pulled in only through
`GigaRAPIOFreshness.lean` is stale: `Thm54.lean:239` imports it directly, added by the same
commit `9947870`.)

## Scope

Every statement below is about **this tree's** compute/memory chips staged over
`nockChronologyIO3`, and about a package `P : OptimizedFullStrictNockVMROMPackage F K hOrb` with
`[Algebra F K] [FiniteDimensional F K]`.  Nothing here is a claim about arbitrary honest
executions, about the deployed Hoon client, or about the two-message chips of
`GigaRAPIOSlots.lean`.
-/

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction

open Nock Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.Reified Nock.Reified.Trans
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.Staging Nock.NockVMROM.Thm54.Staged
open Nock.NockVMROM.Thm54.GigaChips
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.GigaFinite
open Nock.NockVMROM.Thm54.GigaIOSlots
open Nock.NockVMROM.Thm54.GigaIOThirdMessage
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.IOCoinReconciliation
open Nock.NockVMROM.Thm54.IOCoinReconciliation.Chronology
open Nock.NockVMROM.Thm54.CommitmentModel
open Nock.NockVMROM.Thm54.SaturatedDeclaration
open scoped Polynomial

/-! ## 1. The production-coin composition, at the three-message chips -/

section Composition

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F]
  {hOrb : ℕ} (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- **The composition at the enforced chips.**  Word for word
`GigaIOSlots.io_lio_of_giga_satisfies_at_production_coins` (`GigaRAPIOSlots.lean:963`) with
`finiteComputeChip canonicalIOSlots` / `finiteMemoryChip canonicalIOSlots` replaced by
`computeChip3 S` / `memoryChip3 S` and the canonical placement replaced by an arbitrary
`S : IOPlacement3`.

The two counted-event hypotheses of `IOChipSoundness.io_lio_of_satisfies`
(`IOChipSoundness.lean:408`) are **not** assumed: `IOCoinReconciliation.sampled_coins_good`
(`:208`) reads them off `hgood`.  The coins are not a parameter either: they are `ioCoinsOf c`,
identified with `P.optimized.sampled.sampled.coins` by `ioCoinsOf_eq_sampled`
(`IOCoinReconciliation.lean:177`).

What is new relative to `GigaRAPIOSlots.lean:963` is *not* the conclusion but the object: at
these chips the record columns `102 … 111` / `43 … 52` cannot declare either IO coin
(`computeChip3_io_data_undeclared`, `GigaRAPThirdMessage.lean:480`), whereas at the two-message
chips column `111` / `52` could and the exclusion was a choice. -/
theorem io_lio_of_giga3_satisfies_at_production_coins
    (S : IOPlacement3)
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (terminal : K) (qC qM : SegmentedRAPParams K) (x₀p x₀m : K)
    (PC : Fin (computeCombinedFiniteAIR 10 9 S.map).numTraceCols → K[X])
    (PM : Fin (memoryCombinedFiniteAIR (K := K) 10 9 S.map).numTraceCols → K[X])
    (hC : (computeChip3Sat S qC).Satisfies PC)
    (hM : (memoryChip3Sat S qM).Satisfies PM)
    (hrowsP : IOChip.ChipRows P.optimized.sampled.sampled.records.requests.length
      (remapParams qC S.map ComputeChip.ioPubOff) x₀p)
    (hrowsM : IOChip.ChipRows P.optimized.sampled.sampled.records.responses.length
      (remapParams qM S.map memIoPubOff) x₀m)
    (hagP : IOChip.ChipAgreement P.optimized.sampled.sampled.records.requests
      (ioCoinsOf c) terminal
      (remapParams qC S.map ComputeChip.ioPubOff) x₀p (finProgIoBlock PC))
    (hagM : IOChip.ChipAgreement P.optimized.sampled.sampled.records.responses
      (ioCoinsOf c) terminal
      (remapParams qM S.map memIoPubOff) x₀m (finMemIoBlock PM)) :
    IO.LIO P.optimized.family.problem.cfg.Ksz
      P.optimized.sampled.sampled.records.requests
      P.optimized.sampled.sampled.records.responses :=
  io_lio_of_satisfies_at_production_coins P Qc Qm c hacc hgood terminal
    (remapParams qC S.map ComputeChip.ioPubOff)
    (remapParams qM S.map memIoPubOff) x₀p x₀m
    (finProgIoBlock PC) (finMemIoBlock PM)
    (computeChip3_fold_loses_nothing S qC PC hC).2.2
    (memoryChip3_fold_loses_nothing S qM PM hM).2.2
    hrowsP hrowsM hagP hagM

/-- **The `Perm` conjunct alone**, at the enforced chips: the memory requests the compute table
issued are a permutation of the responses the memory table served.  The analogue of
`GigaIOSlots.perm_of_giga_satisfies_at_production_coins` (`GigaRAPIOSlots.lean:998`). -/
theorem perm_of_giga3_satisfies_at_production_coins
    (S : IOPlacement3)
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (terminal : K) (qC qM : SegmentedRAPParams K) (x₀p x₀m : K)
    (PC : Fin (computeCombinedFiniteAIR 10 9 S.map).numTraceCols → K[X])
    (PM : Fin (memoryCombinedFiniteAIR (K := K) 10 9 S.map).numTraceCols → K[X])
    (hC : (computeChip3Sat S qC).Satisfies PC)
    (hM : (memoryChip3Sat S qM).Satisfies PM)
    (hrowsP : IOChip.ChipRows P.optimized.sampled.sampled.records.requests.length
      (remapParams qC S.map ComputeChip.ioPubOff) x₀p)
    (hrowsM : IOChip.ChipRows P.optimized.sampled.sampled.records.responses.length
      (remapParams qM S.map memIoPubOff) x₀m)
    (hagP : IOChip.ChipAgreement P.optimized.sampled.sampled.records.requests
      (ioCoinsOf c) terminal
      (remapParams qC S.map ComputeChip.ioPubOff) x₀p (finProgIoBlock PC))
    (hagM : IOChip.ChipAgreement P.optimized.sampled.sampled.records.responses
      (ioCoinsOf c) terminal
      (remapParams qM S.map memIoPubOff) x₀m (finMemIoBlock PM)) :
    P.optimized.sampled.sampled.records.requests.Perm
      P.optimized.sampled.sampled.records.responses :=
  (io_lio_of_giga3_satisfies_at_production_coins P S Qc Qm c hacc hgood terminal qC qM x₀p x₀m
    PC PM hC hM hrowsP hrowsM hagP hagM).2.2

/-- **The coins the composition runs at are the package's sampled ones**, at the three-message
chips.  Chronology-independent: `ioCoinsOf` reads the production tuple, not a challenge vector. -/
theorem composition3_coins_are_sampled
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    ioCoinsOf c = P.optimized.sampled.sampled.coins :=
  ioCoinsOf_eq_sampled P Qc Qm c hacc

end Composition

/-! ## 2. The chain, as one theorem -/

section EndToEnd

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F]
  {hOrb : ℕ} (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- **The end-to-end chain at the enforced chips.**

From
* a package `P`,
* an accepted production challenge tuple `c` outside the one production failure event,
* satisfaction of the two **three-message** chips, named as the saturated
  `SaturatedDeclaration.computeChip3Sat S qC` / `memoryChip3Sat S qM` — the same propositions as at
  `computeChip3 S qC` / `memoryChip3 S qM` by `Iff.rfl`, see §2.5,
* the `ChipRows` row-domain data and the `ChipAgreement` column/coin identifications, and
* the three evaluator side conditions of `GenuineEvalN`,

acceptance buys all of the following at once.

1. `IO.LIO` on the package's own sampled records — the record-level IO language.
2. `requests.Perm responses` — the sentence the LogUp argument is *for*.
4. The two counted-event exclusions, **derived** rather than assumed:
   `IOCoinReconciliation.sampled_coins_good` (`:208`) reads `γ ∉ IORLCCollisionEvent` and
   `pole ∉ IOLogDerivEvent` off the accepted tuple lying outside the failure event, so they are
   priced at `|K|²` rather than postulated on the strategy.
5. and 6. The coin **independence** of the `IO_prog` record columns — `102 … 111` on the compute
   side, `43 … 52` on the memory side — now *forced* by
   `committed_early_excludes_the_io_coins_compute`/`_memory`
   (`GigaRAPThirdMessage.lean:435`, `:442`), i.e. by the contrapositive of the structure
   obligation `StagedChip.columns_commit_before_sampling` at a chronology in which the two
   `RAP_prog-IO` coins ride the paper's third message.  On the
   two-message chips of `GigaRAPIOSlots.lean` conjuncts 5 and 6 hold only of the *chosen*
   `finComputeColumnChallenges`, and a second, equally legal chip over the identical AIR declares
   the pair at column `111`.  Here no such chip exists.

**Deliberately not bundled away**: `hrowsP`/`hrowsM`/`hagP`/`hagM` stay hypotheses because they
are what ties a hostile trace to the records the argument is about, and `hs`/`hf`/`hno` stay
hypotheses because they are the evaluator's own side conditions (`GenuineEvalN.lean:64`, and
`NoOverflowRun` does *not* name the result, so it cannot smuggle in conclusion 3).

They use none of this theorem's
fifteen hypotheses: they are schedule facts about `computeChip3Sat S qC` / `memoryChip3Sat S qM`
that hold for **every** `S`, `qC`, `qM`, discharged by
`SaturatedDeclaration.computeChip3Sat_io_data_undeclared` / `memoryChip3Sat_io_data_undeclared`
alone.  They are not vacuous — they are `JP`'s content, and
carrying them here is what states the exclusion at the production package's own type — but nothing
about acceptance produces them.  `giga3_io_columns_undeclared` below is the same pair with the
package, the tuple, the chips and the evaluator conditions all removed, which is the honest form;
this theorem keeps them only so the six things a reader wants at the package type sit in one
place. -/
theorem accepted_giga3_certifies_io_perm_and_evalN
    (S : IOPlacement3)
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (terminal : K) (qC qM : SegmentedRAPParams K) (x₀p x₀m : K)
    (PC : Fin (computeCombinedFiniteAIR 10 9 S.map).numTraceCols → K[X])
    (PM : Fin (memoryCombinedFiniteAIR (K := K) 10 9 S.map).numTraceCols → K[X])
    (hC : (computeChip3Sat S qC).Satisfies PC)
    (hM : (memoryChip3Sat S qM).Satisfies PM)
    (hrowsP : IOChip.ChipRows P.optimized.sampled.sampled.records.requests.length
      (remapParams qC S.map ComputeChip.ioPubOff) x₀p)
    (hrowsM : IOChip.ChipRows P.optimized.sampled.sampled.records.responses.length
      (remapParams qM S.map memIoPubOff) x₀m)
    (hagP : IOChip.ChipAgreement P.optimized.sampled.sampled.records.requests
      (ioCoinsOf c) terminal
      (remapParams qC S.map ComputeChip.ioPubOff) x₀p (finProgIoBlock PC))
    (hagM : IOChip.ChipAgreement P.optimized.sampled.sampled.records.responses
      (ioCoinsOf c) terminal
      (remapParams qM S.map memIoPubOff) x₀m (finMemIoBlock PM))
    (hs : FieldEmbedding.BoundedBy P.q P.optimized.verifier.raw.claim.subject)
    (hf : FieldEmbedding.BoundedBy P.q P.optimized.verifier.raw.claim.formula)
    (hno : GenuineEvalN.NoOverflowRun P.q P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula) :
    -- (1) the record-level IO language
    IO.LIO P.optimized.family.problem.cfg.Ksz
        P.optimized.sampled.sampled.records.requests
        P.optimized.sampled.sampled.records.responses
    -- (2) the permutation the LogUp argument buys
    ∧ P.optimized.sampled.sampled.records.requests.Perm
        P.optimized.sampled.sampled.records.responses
    -- (3) the committed claim is a genuine Nock evaluation
    ∧ (∃ fuel : ℕ, Nock.evalN fuel P.optimized.verifier.raw.claim.subject
        P.optimized.verifier.raw.claim.formula = some P.optimized.verifier.raw.claim.result)
    -- (4) the two counted-event exclusions, derived from acceptance
    ∧ (P.optimized.sampled.sampled.coins.gamma
          ∉ IORLCCollisionEvent P.optimized.sampled.sampled.records
        ∧ P.optimized.sampled.sampled.coins.pole
          ∉ IOLogDerivEvent P.optimized.sampled.sampled.records
              P.optimized.sampled.sampled.coins.gamma)
    -- (5) the compute IO_prog record columns declare neither RAP_prog-IO coin — forced
    ∧ (∀ col : Fin 113, 102 ≤ (col : ℕ) → (col : ℕ) ≤ 111 → ∀ i : Fin 2,
        S.slot i ∉ (computeChip3Sat S qC).columnChallenges col)
    -- (6) the memory twin
    ∧ (∀ col : Fin 55, 44 ≤ (col : ℕ) → (col : ℕ) ≤ 53 → ∀ i : Fin 2,
        S.slot i ∉ (memoryChip3Sat S qM).columnChallenges col) := by
  have hlio := io_lio_of_giga3_satisfies_at_production_coins P S Qc Qm c hacc hgood terminal
    qC qM x₀p x₀m PC PM hC hM hrowsP hrowsM hagP hagM
  have hp8good := (P.optimizedFailureEvent_good_components Qc Qm c hgood).1
  have hgoodcoins := sampled_coins_good P Qc Qm c hacc hgood
  exact ⟨hlio, hlio.2.2,
    GenuineEvalN.package_accepted_evalN P c.1 P.objects.cfg.challenges.lam
      (by rw [← hacc.same_problem.lam_eq]; exact hacc.p8) hp8good hs hf hno,
    ⟨hgoodcoins.1, hgoodcoins.2.1⟩,
    fun col h1 h2 i => computeChip3Sat_io_data_undeclared S qC col h1 h2 i,
    fun col h1 h2 i => memoryChip3Sat_io_data_undeclared S qM col h1 h2 i⟩

/-- **Conjuncts (5) and (6) of `accepted_giga3_certifies_io_perm_and_evalN`, standing alone.**

Measured statement of what those two conjuncts actually depend on: no package, no accepted tuple,
no failure-event exclusion, no satisfying trace, no evaluator side condition — and no `Fintype`,
`Algebra` or `CharP` instance either.  A bare `Field L` and a choice of placement and parameters
suffice, because the exclusion is the contrapositive of the **structure field**
`StagedChip.columns_commit_before_sampling` (`StagedTableRAP.lean:174`) at a chronology in which
the two `RAP_prog-IO` coins ride the paper's third verifier message.  That is precisely why it holds of hostile chips: every chip of the chronology must
discharge the field.

The first two conjuncts are at the
*saturated* chips `SaturatedDeclaration.computeChip3Sat` / `memoryChip3Sat`, whose declaration is
the schedule-legal set itself and is therefore not chosen; the last two are the shipped chips'
original statement, kept so that nothing this theorem used to say is lost.  The first pair
**implies** the second (`SaturatedDeclaration.columnChallenges_subset_scheduleLegal`: a chip can
only withhold, never add), so the move is a strengthening; both are supplied explicitly rather
than derived so that neither reading depends on the reader spotting the inclusion. -/
theorem giga3_io_columns_undeclared {L : Type*} [Field L] (S : IOPlacement3)
    (qC qM : SegmentedRAPParams L) :
    (∀ col : Fin 113, 102 ≤ (col : ℕ) → (col : ℕ) ≤ 111 → ∀ i : Fin 2,
        S.slot i ∉ (computeChip3Sat S qC).columnChallenges col)
    ∧ (∀ col : Fin 55, 44 ≤ (col : ℕ) → (col : ℕ) ≤ 53 → ∀ i : Fin 2,
        S.slot i ∉ (memoryChip3Sat S qM).columnChallenges col)
    ∧ (∀ col : Fin 113, 102 ≤ (col : ℕ) → (col : ℕ) ≤ 111 → ∀ i : Fin 2,
        S.slot i ∉ (computeChip3 S qC).columnChallenges col)
    ∧ (∀ col : Fin 55, 44 ≤ (col : ℕ) → (col : ℕ) ≤ 53 → ∀ i : Fin 2,
        S.slot i ∉ (memoryChip3 S qM).columnChallenges col) :=
  ⟨fun col h1 h2 i => computeChip3Sat_io_data_undeclared S qC col h1 h2 i,
   fun col h1 h2 i => memoryChip3Sat_io_data_undeclared S qM col h1 h2 i,
   fun col h1 h2 i => computeChip3_io_data_undeclared S qC col h1 h2 i,
   fun col h1 h2 i => memoryChip3_io_data_undeclared S qM col h1 h2 i⟩

end EndToEnd

/-! ## 2.5 The chip the chain runs at is uniquely determined

§1 and §2 name `SaturatedDeclaration.computeChip3Sat` / `memoryChip3Sat` rather than the shipped
`computeChip3` / `memoryChip3`.  This section is the receipt for what that move did and did not
cost, because the two halves of it are not alike.

* **On the `Satisfies` hypotheses it is a definitional no-op, and buys nothing by itself.**
  `StagedChip.Satisfies` reads `air` and `params`; `CommitmentModel.saturate` changes only
  `columnChallenges`; so the hypothesis is the *same proposition*, by `Iff.rfl`
  (`giga3_satisfaction_is_the_same_proposition`).  The chain never quantified over a
  `RoundFibred.StagedAssignment` at all — `grep` finds none in this module — so there was no
  prover class here for saturation to shrink.  What the re-pointing buys on this side is only that
  the object whose satisfaction is hypothesised and the object the conclusion talks about are the
  *same* chip.

* **On conjuncts (5) and (6) it is a strengthening.**  `columnChallenges` at the saturated chip is
  the schedule-legal set, which contains the shipped declaration
  (`SaturatedDeclaration.columnChallenges_subset_scheduleLegal`), so "the IO slot is not in it" is
  the stronger sentence — and it is a sentence about an object no one chose:
  `giga3_production_chips_are_unique` says any saturated chip over the same AIR, params and
  schedule *is* this one, where at the shipped chips
  `SaturatedDeclaration.computeChip3_not_saturated` exhibits a second legal declaration.

Nothing here changes an AIR, a constraint, a census or a bound. -/

section Saturation

variable {L : Type*} [Field L]

/-- **The re-pointing is a no-op on the satisfaction axis.**  The hypotheses `hC` / `hM` of §1 and
§2 are the same propositions they were at the shipped chips, by `Iff.rfl` — `Satisfies` does not
read `columnChallenges`.  This is the receipt that the migration of the production chain onto the
saturated chips cannot have moved a bound or a constraint. -/
theorem giga3_satisfaction_is_the_same_proposition (S : IOPlacement3)
    (qC qM : SegmentedRAPParams L)
    (PC : Fin (computeCombinedFiniteAIR 10 9 S.map).numTraceCols → L[X])
    (PM : Fin (memoryCombinedFiniteAIR (K := L) 10 9 S.map).numTraceCols → L[X]) :
    ((computeChip3Sat S qC).Satisfies PC ↔ (computeChip3 S qC).Satisfies PC)
      ∧ ((memoryChip3Sat S qM).Satisfies PM ↔ (memoryChip3 S qM).Satisfies PM) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- The AIR, the params and the schedule are the shipped chips' own, by `rfl`: only the
declaration moved. -/
theorem giga3_saturation_keeps_the_air_and_schedule (S : IOPlacement3)
    (qC qM : SegmentedRAPParams L) :
    (computeChip3Sat S qC).air = (computeChip3 S qC).air
      ∧ (computeChip3Sat S qC).params = (computeChip3 S qC).params
      ∧ (computeChip3Sat S qC).schedule = (computeChip3 S qC).schedule
      ∧ (memoryChip3Sat S qM).air = (memoryChip3 S qM).air
      ∧ (memoryChip3Sat S qM).params = (memoryChip3 S qM).params
      ∧ (memoryChip3Sat S qM).schedule = (memoryChip3 S qM).schedule :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **What the re-pointing buys: the declaration in §1-§2 is not chosen.**

*(a)* Both production chips are saturated, i.e. their `columnChallenges` *is* the schedule-legal
set (`CommitmentModel.Saturated`), so the field carries no information beyond `schedule` and
`chronology`.

*(b)* Consequently there is **no rival**: any `StagedChip L 4 nockChronologyIO3` that is saturated
and has the same AIR, params and schedule is equal to the chip the chain runs at
(`SaturatedDeclaration.eq_of_saturated`).

*(c)* And the shipped chips do **not** have that property: `computeChip3` / `memoryChip3` are not
saturated, so over their AIR, params and schedule a second legal declaration exists — indeed the
saturated one.  That is the freedom §1-§2 no longer quantify over. -/
theorem giga3_production_chips_are_unique (S : IOPlacement3) (qC qM : SegmentedRAPParams L) :
    (Saturated (computeChip3Sat S qC) ∧ Saturated (memoryChip3Sat S qM))
      ∧ (∀ T : StagedChip L 4 nockChronologyIO3, Saturated T →
          T.air = (computeChip3Sat S qC).air → T.params = (computeChip3Sat S qC).params →
          HEq T.schedule (computeChip3Sat S qC).schedule → T = computeChip3Sat S qC)
      ∧ (∀ T : StagedChip L 4 nockChronologyIO3, Saturated T →
          T.air = (memoryChip3Sat S qM).air → T.params = (memoryChip3Sat S qM).params →
          HEq T.schedule (memoryChip3Sat S qM).schedule → T = memoryChip3Sat S qM)
      ∧ ¬ Saturated (computeChip3 S qC) ∧ ¬ Saturated (memoryChip3 S qM) :=
  ⟨⟨computeChip3Sat_saturated S qC, memoryChip3Sat_saturated S qM⟩,
   fun T hsat hair hpar hsch => computeChip3Sat_unique S qC T hsat hair hpar hsch,
   fun T hsat hair hpar hsch => memoryChip3Sat_unique S qM T hsat hair hpar hsch,
   computeChip3_not_saturated S qC, memoryChip3_not_saturated S qM⟩

end Saturation

/-! ## 3. Non-vacuity: the hypothesis bundle is simultaneously satisfiable

`canonicalPlacement3.map = canonicalIOSlots.map` is `rfl`
(`GigaRAPThirdMessage.canonicalPlacement3_map`, `:227`) and `canonical3_satisfies_iff` (`:587`) is
`Iff.rfl`, so the assembled honest witness of `GigaRAPAssembledWitness.lean` satisfies the
three-message chips *as the same proposition*.  Nothing has to be rebuilt. -/

section NonVacuity

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F]
  {hOrb : ℕ} (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- **The whole assembled-chip hypothesis bundle of §1, at the three-message chips.**  The
transport of `GigaWitness.giga_bundle_at_production_coins` (`GigaRAPAssembledWitness.lean:936`)
along `canonicalPlacement3_map`. -/
theorem giga3_bundle_at_production_coins
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (D : OrbitDomain K)
    (hcap : P.optimized.sampled.sampled.records.requests.length + 1 ≤ 2 ^ D.h) :
    ∃ (terminal : K) (qC qM : SegmentedRAPParams K) (x₀p x₀m : K)
      (PC : Fin (computeCombinedFiniteAIR 10 9 canonicalPlacement3.map).numTraceCols → K[X])
      (PM : Fin (memoryCombinedFiniteAIR (K := K) 10 9 canonicalPlacement3.map).numTraceCols → K[X]),
        (computeChip3Sat canonicalPlacement3 qC).Satisfies PC
      ∧ (memoryChip3Sat canonicalPlacement3 qM).Satisfies PM
      ∧ IOChip.ChipRows P.optimized.sampled.sampled.records.requests.length
          (remapParams qC canonicalPlacement3.map ComputeChip.ioPubOff) x₀p
      ∧ IOChip.ChipRows P.optimized.sampled.sampled.records.responses.length
          (remapParams qM canonicalPlacement3.map memIoPubOff) x₀m
      ∧ IOChip.ChipAgreement P.optimized.sampled.sampled.records.requests
          (ioCoinsOf c) terminal
          (remapParams qC canonicalPlacement3.map ComputeChip.ioPubOff) x₀p (finProgIoBlock PC)
      ∧ IOChip.ChipAgreement P.optimized.sampled.sampled.records.responses
          (ioCoinsOf c) terminal
          (remapParams qM canonicalPlacement3.map memIoPubOff) x₀m (finMemIoBlock PM) :=
  GigaWitness.giga_bundle_at_production_coins P Qc Qm c hacc D hcap

/-- **The composition of §1 is not vacuous, and needs no orbit hypothesis.**  Its own conclusion,
re-derived by feeding it a bundle that is *built* rather than assumed — the analogue of
`GigaWitness.giga_composition_roundtrip_at_package_orbit`
(`GigaRAPAssembledWitness.lean:1087`) at the enforced chips.  It compiles only if the seven
objects the bundle produces are accepted verbatim as `io_lio_of_giga3_satisfies_at_production_coins`'s
assembled-chip hypotheses. -/
theorem giga3_composition_roundtrip_at_package_orbit
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm) :
    IO.LIO P.optimized.family.problem.cfg.Ksz
      P.optimized.sampled.sampled.records.requests
      P.optimized.sampled.sampled.records.responses := by
  obtain ⟨terminal, qC, qM, x₀p, x₀m, PC, PM, hC, hM, hrowsP, hrowsM, hagP, hagM⟩ :=
    giga3_bundle_at_production_coins P Qc Qm c hacc P.optimized.family.problem.cfg.orbit
      (GigaWitness.package_progCapacity P Qc Qm c hacc)
  exact io_lio_of_giga3_satisfies_at_production_coins P canonicalPlacement3 Qc Qm c hacc hgood
    terminal qC qM x₀p x₀m PC PM hC hM hrowsP hrowsM hagP hagM

/-- **The end-to-end theorem's assembled-chip conjuncts are not vacuous either**: conjuncts (1),
(2), (5) and (6) of `accepted_giga3_certifies_io_perm_and_evalN` at a built bundle.  Conjuncts
(3) and (4) are omitted here only because (3) carries the three evaluator side conditions, which
are hypotheses of the chain by design and not of the chips. -/
theorem end_to_end_conjuncts_nonvacuous
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm) :
    ∃ (qC : SegmentedRAPParams K) (qM : SegmentedRAPParams K),
      IO.LIO P.optimized.family.problem.cfg.Ksz
          P.optimized.sampled.sampled.records.requests
          P.optimized.sampled.sampled.records.responses
      ∧ P.optimized.sampled.sampled.records.requests.Perm
          P.optimized.sampled.sampled.records.responses
      ∧ (∀ col : Fin 113, 102 ≤ (col : ℕ) → (col : ℕ) ≤ 111 → ∀ i : Fin 2,
          canonicalPlacement3.slot i
            ∉ (computeChip3Sat canonicalPlacement3 qC).columnChallenges col)
      ∧ (∀ col : Fin 55, 44 ≤ (col : ℕ) → (col : ℕ) ≤ 53 → ∀ i : Fin 2,
          canonicalPlacement3.slot i
            ∉ (memoryChip3Sat canonicalPlacement3 qM).columnChallenges col) := by
  obtain ⟨terminal, qC, qM, x₀p, x₀m, PC, PM, hC, hM, hrowsP, hrowsM, hagP, hagM⟩ :=
    giga3_bundle_at_production_coins P Qc Qm c hacc P.optimized.family.problem.cfg.orbit
      (GigaWitness.package_progCapacity P Qc Qm c hacc)
  have hlio := io_lio_of_giga3_satisfies_at_production_coins P canonicalPlacement3 Qc Qm c hacc
    hgood terminal qC qM x₀p x₀m PC PM hC hM hrowsP hrowsM hagP hagM
  exact ⟨qC, qM, hlio, hlio.2.2,
    fun col h1 h2 i => computeChip3Sat_io_data_undeclared canonicalPlacement3 qC col h1 h2 i,
    fun col h1 h2 i => memoryChip3Sat_io_data_undeclared canonicalPlacement3 qM col h1 h2 i⟩

end NonVacuity

/-! ## 4. What remains assumed

After the migration the honest list is short.  Below, each item is either **discharged** (a
theorem about the production chips, so it is not on the list at all) or **carried** (a named
hypothesis, with the receipt saying why it cannot be promoted).

* **`ProgIORecordsCommittedByRoundTwo` / `MemIORecordsCommittedByRoundTwo`
  (`GigaRAPThirdMessage.lean:393`, `:399`) — DISCHARGED at the production chips.**
  These are the Lean image of the paper, `Prover sends Com(IO_prog) to the Verifier`, read
  as a schedule condition: the whole of `IO_prog` — the two multiplicity columns and all eight
  record coordinates, the timestamp `111` included — is committed before the coins are sent.
  They are hypotheses of the *generic* theorems `committed_early_excludes_the_io_coins_compute`
  (`:435`) and `_memory` (`:442`), which quantify over an arbitrary hostile
  `T : StagedChip K 4 nockChronologyIO3`; at `computeChip3` / `memoryChip3` they are proved by
  `decide` (`computeChip3_records_committed_early`, `:471`; `memoryChip3_records_committed_early`,
  `:475`), so they appear **nowhere** in the hypothesis list of §2's chain.
  `schedule_conditions_are_discharged` below is the compiled statement of that.
  What is *not* a Lean proposition, and stays a modelling reading, is the identification of
  `finComputeRoundOf4` / `finMemRoundOf4` (`:235`, `:248`) with the paper's commitment schedule.

* **`RoundFibred.StagedAssignment.col_reads` (`RoundFibredSoundness.lean:563`) — CARRIED.**
  A field of `StagedAssignment`: "two challenge vectors agreeing on `T.columnChallenges c` give
  the same column `c`", i.e. a column committed in round `r` is not a function of a coin sampled
  at message `≥ r`.  It is the Lean image of the **binding** property of the commitment scheme
  the paper writes `Com(·)` for — `We denote by Com(·) a binding commitment scheme, as per
  standard RAP interactive constructions` — whose compilation the paper explicitly delegates
  (`We do not go into detail on the compilation of RAPs into SNARKs here`).  So a
  commitment-binding assumption is legitimate; the requirement is that it be *named*, and it is.
  `col_reads_not_implied_by_satisfaction` (`GigaRAPThirdMessage.lean:839`) is the receipt that it
  cannot be promoted to a theorem about satisfying traces; `col_reads_receipt_is_inhabited` below
  removes that receipt's own hypothesis by exhibiting a constraint-free chip of
  `nockChronologyIO3`, so the receipt is unconditional rather than a statement about a possibly
  empty class.

* **The `ChipRows` / `ChipAgreement` data (`IOChipSoundness.lean:179`, `:165`) — CARRIED, and
  visible in the statement.**  `ChipRows` says the boundary, record and terminal rows lie in the
  evaluation domains their kinds are deployed on; `ChipAgreement` says these trace columns hold
  these records, that public slot `0` is the shared terminal, and that challenge slots
  `S.slot 0` / `S.slot 1` carry `γ` and the pole.  They are what tie a hostile trace to the
  records the argument is about, so they cannot be discharged from acceptance.  They are
  *satisfiable*: §3 builds them.

* **`FieldEmbedding.BoundedBy` and `GenuineEvalN.NoOverflowRun` (`GenuineEvalN.lean:64`) —
  CARRIED, for conjunct (3) only.**  The first is the paper's own typing of a Nock program; the second says the run performs no
  modular wrap, and it does not name the result.

Not on this list, because they are derived: the two counted-event exclusions (§2 conjunct 4, from
`sampled_coins_good`), the IO-coin freshness at the record columns (§2 conjuncts 5 and 6, from
the schedule), the placement's freshness (`IOPlacement3.fresh`, `GigaRAPThirdMessage.lean:190`),
and the identification of the chip's coins with the package's sampled pair
(`composition3_coins_are_sampled`).
-/

section Remaining

variable {L : Type*} [Field L]

/-- **the paper's schedule condition is a theorem at the production chips, not a
hypothesis.**  Both halves by `decide` inside `computeRoundOf4_le_two` /`memRoundOf4_le_two`
(`GigaRAPThirdMessage.lean:448`, `:459`).  Stated at the saturated chips the chain now runs at
*and* at the shipped ones: the condition is about `schedule`, which saturation does not touch
(`giga3_saturation_keeps_the_air_and_schedule`), so it is the same fact twice. -/
theorem schedule_conditions_are_discharged (S : IOPlacement3) (qC qM : SegmentedRAPParams L) :
    (ProgIORecordsCommittedByRoundTwo (computeChip3Sat S qC)
        ∧ MemIORecordsCommittedByRoundTwo (memoryChip3Sat S qM))
      ∧ (ProgIORecordsCommittedByRoundTwo (computeChip3 S qC)
        ∧ MemIORecordsCommittedByRoundTwo (memoryChip3 S qM)) :=
  ⟨⟨computeChip3Sat_records_committed_early S qC, memoryChip3Sat_records_committed_early S qM⟩,
   computeChip3_records_committed_early S qC, memoryChip3_records_committed_early S qM⟩

end Remaining

section ColReadsWitness

variable {K : Type*} [Field K]

/-- A one-column AIR with no constraints. -/
def emptyAIR1 : Reified.AIR where
  numTraceCols := 1
  numChallenges := 10
  numPublic := 0
  constraints := []

/-- Degenerate RAP parameters: every domain empty, `ω = βcoset = 1`.  Used only to inhabit the
class `col_reads_not_implied_by_satisfaction` quantifies over. -/
noncomputable def trivialParams (K : Type*) [Field K] : SegmentedRAPParams K where
  chalVal := fun _ => 0
  pubVal := fun _ => 0
  eDeg := 1
  hExp := 1
  ω := 1
  βcoset := 1
  domain := fun _ => ∅
  βcoset_ne_zero := one_ne_zero
  hExp_pos := le_rfl

/-- The one column is committed in round `0`. -/
def trivialSchedule : RoundSchedule 1 4 where
  roundOf := fun _ => 0
  width := ![1, 0, 0, 0]
  width_eq := by decide

/-- **A constraint-free chip of the three-message chronology.**  Its existence is what makes
`col_reads_not_implied_by_satisfaction` (`GigaRAPThirdMessage.lean:839`) a statement about a
non-empty class. -/
noncomputable def trivialChip3 (K : Type*) [Field K] : StagedChip K 4 nockChronologyIO3 where
  air := emptyAIR1
  params := trivialParams K
  schedule := trivialSchedule
  columnChallenges := fun _ => ∅
  columns_commit_before_sampling := fun _c _j hj => absurd hj (Finset.notMem_empty _)

/-- **The `col_reads` receipt, with no hypotheses left.**  There *is* a chip of
`nockChronologyIO3` and a family of traces that satisfies it at every challenge vector while
violating the `StagedAssignment.col_reads` condition (`RoundFibredSoundness.lean:563`).  So
`col_reads` is not derivable from satisfaction, and carrying it as a field of `StagedAssignment`
— the binding property of the paper's `Com(·)`, whose compilation the paper delegates
— is a genuine, named modelling assumption rather than an oversight. -/
theorem col_reads_receipt_is_inhabited :
    ∃ t : (Fin 10 → K) → (Fin (trivialChip3 K).air.numTraceCols → K[X]),
      (∀ χ, (trivialChip3 K).Satisfies (t χ))
        ∧ ¬ (∀ col (χ₁ χ₂ : Fin 10 → K),
              (∀ j ∈ (trivialChip3 K).columnChallenges col, χ₁ j = χ₂ j) → t χ₁ col = t χ₂ col) :=
  col_reads_not_implied_by_satisfaction (trivialChip3 K) rfl ⟨0, Nat.one_pos⟩ 0
    (Finset.notMem_empty _)

end ColReadsWitness

/-! ## 5. The receipt that the migration was necessary

`GigaRAPThirdMessage.lean:27-32` asserts, in prose, that at the **two**-message chronology
"a second, equally legal `StagedChip` over the identical AIR, params and schedule can declare
both IO coins at column `111`, agree with `finiteComputeChip` on satisfaction by `Iff.rfl`".  That
sentence was never compiled.  It is compiled here, because it is the whole reason the production
path had to move: without it "the exclusion at `111`/`52` is a choice" is an unbacked claim about
an object nobody exhibited, and with it the migration is forced rather than tidy.

Nothing in this section touches the two-message chips; it *adds* a second chip alongside them. -/

section HostileTwoMessageChip

variable {L : Type*} [Field L]

/-- Both `100`, `101` **and** the record timestamp `111` are round-`2` columns of
`finComputeSchedule`. -/
theorem hostileProgCols_round_two (c : Fin 113)
    (hc : (c : ℕ) ∈ finProgIoCoinCols ∨ (c : ℕ) = 111) : finComputeRoundOf c = 2 := by
  rcases hc with hc | hc
  · exact finProgIoCoinCols_round_two c hc
  · obtain rfl : c = (111 : Fin 113) := Fin.ext hc
    decide

theorem hostileMemCols_round_two (c : Fin 55)
    (hc : (c : ℕ) ∈ finMemIoCoinCols ∨ (c : ℕ) = 53) : finMemRoundOf c = 2 := by
  rcases hc with hc | hc
  · exact finMemIoCoinCols_round_two c hc
  · obtain rfl : c = (53 : Fin 55) := Fin.ext hc
    decide

/-- **The hostile declaration.**  `GigaIOSlots.finComputeColumnChallenges`
(`GigaRAPIOSlots.lean:426`) with column `111` — the `IO_prog` record timestamp — moved into the
IO-coin branch. -/
def hostileComputeColumnChallenges (S : IOSlots) (c : Fin 113) : Finset (Fin 10) :=
  if (c : ℕ) ∈ finProgIoCoinCols ∨ (c : ℕ) = 111 then
    insert (S.slot 0) (insert (S.slot 1) (finComputeRoundChalOf (finComputeRoundOf c)))
  else finComputeRoundChalOf (finComputeRoundOf c)

/-- The memory twin, at column `52`. -/
def hostileMemColumnChallenges (S : IOSlots) (c : Fin 55) : Finset (Fin 10) :=
  if (c : ℕ) ∈ finMemIoCoinCols ∨ (c : ℕ) = 53 then
    insert (S.slot 0) (insert (S.slot 1) (finMemRoundChalOf (finMemRoundOf c)))
  else finMemRoundChalOf (finMemRoundOf c)

/-- **The hostile declaration is legal**: it satisfies `columns_commit_before_sampling`
(`StagedTableRAP.lean:174`) at the two-message chronology, because column `111` is committed
after the *same* verifier message as the coins, not before it. -/
theorem hostileComputeColumns_commit_before_sampling (S : IOSlots) :
    ∀ c : Fin 113, ∀ j ∈ hostileComputeColumnChallenges S c,
      (nockSampledAfterWithIO j : ℕ) < (finComputeRoundOf c : ℕ) := by
  intro c j hj
  by_cases hc : (c : ℕ) ∈ finProgIoCoinCols ∨ (c : ℕ) = 111
  · rw [hostileProgCols_round_two c hc]
    simp only [hostileComputeColumnChallenges, if_pos hc, Finset.mem_insert] at hj
    rcases hj with rfl | rfl | hj
    · rw [S.final_round 0]; decide
    · rw [S.final_round 1]; decide
    · simpa using nockSampledAfterWithIO_lt_two j
  · simp only [hostileComputeColumnChallenges, if_neg hc] at hj
    exact finComputeRoundChalOf_usable _ j hj

theorem hostileMemColumns_commit_before_sampling (S : IOSlots) :
    ∀ c : Fin 55, ∀ j ∈ hostileMemColumnChallenges S c,
      (nockSampledAfterWithIO j : ℕ) < (finMemRoundOf c : ℕ) := by
  intro c j hj
  by_cases hc : (c : ℕ) ∈ finMemIoCoinCols ∨ (c : ℕ) = 53
  · rw [hostileMemCols_round_two c hc]
    simp only [hostileMemColumnChallenges, if_pos hc, Finset.mem_insert] at hj
    rcases hj with rfl | rfl | hj
    · rw [S.final_round 0]; decide
    · rw [S.final_round 1]; decide
    · simpa using nockSampledAfterWithIO_lt_two j
  · simp only [hostileMemColumnChallenges, if_neg hc] at hj
    exact finMemRoundChalOf_usable _ j hj

/-- **The hostile chip.**  Same AIR, same params, same schedule, same chronology as
`GigaIOSlots.finiteComputeChip` (`GigaRAPIOSlots.lean:668`); only the declaration differs. -/
noncomputable def hostileComputeChip (S : IOSlots) (q : SegmentedRAPParams L) :
    StagedChip L 3 nockChronologyWithIO where
  air := computeCombinedFiniteAIR 10 9 S.map
  params := q
  schedule := finComputeSchedule
  columnChallenges := hostileComputeColumnChallenges S
  columns_commit_before_sampling := hostileComputeColumns_commit_before_sampling S

/-- The memory twin. -/
noncomputable def hostileMemoryChip (S : IOSlots) (q : SegmentedRAPParams L) :
    StagedChip L 3 nockChronologyWithIO where
  air := memoryCombinedFiniteAIR (K := L) 10 9 S.map
  params := q
  schedule := finMemorySchedule
  columnChallenges := hostileMemColumnChallenges S
  columns_commit_before_sampling := hostileMemColumns_commit_before_sampling S

/-- **The separation, compiled.**

*(a)* At the **two**-message chronology the exclusion at the record timestamp is free data: the
hostile chip has the same AIR, params and schedule as `finiteComputeChip S q`, satisfaction of
the two is the *same proposition* (`Iff.rfl`), and yet it declares both `RAP_prog-IO` coins at
column `111`, which `finiteComputeChip` does not.  So no property of the constraint system, the
column layout or the commitment schedule rules it out — only the choice of declaration does, and
that is exactly what `GigaIOSlots.io_records_read_no_io_coin` (`GigaRAPIOSlots.lean:535`) is a
statement about.

*(b)* At the **three**-message chronology there is no such chip, for any placement: every
`T : StagedChip L 4 nockChronologyIO3` satisfying the paper's schedule condition excludes
both coins at every `IO_prog` column, `111` included
(`GigaIOThirdMessage.committed_early_excludes_the_io_coins_compute`,
`GigaRAPThirdMessage.lean:435`).

Together: the migration of the production path in §1-§2 is not a tidy-up.  It is the difference
between a declaration and a theorem. -/
theorem two_message_exclusion_is_a_choice_three_message_is_not
    (S : IOSlots) (hfresh : ∀ i, ∀ j : Fin 8, S.slot i ≠ embed8 j)
    (S3 : IOPlacement3) (q : SegmentedRAPParams L) :
    ((hostileComputeChip S q).air = (finiteComputeChip S q).air
        ∧ (hostileComputeChip S q).params = (finiteComputeChip S q).params
        ∧ (hostileComputeChip S q).schedule = (finiteComputeChip S q).schedule
        ∧ (∀ Pt : Fin (computeCombinedFiniteAIR 10 9 S.map).numTraceCols → L[X],
            (hostileComputeChip S q).Satisfies Pt ↔ (finiteComputeChip S q).Satisfies Pt)
        ∧ (∀ i, S.slot i ∈ (hostileComputeChip S q).columnChallenges (111 : Fin 113))
        ∧ (∀ i, S.slot i ∉ (finiteComputeChip S q).columnChallenges (111 : Fin 113)))
      ∧ ((hostileMemoryChip S q).air = (finiteMemoryChip S q).air
        ∧ (hostileMemoryChip S q).schedule = (finiteMemoryChip S q).schedule
        ∧ (∀ Pt : Fin (memoryCombinedFiniteAIR (K := L) 10 9 S.map).numTraceCols → L[X],
            (hostileMemoryChip S q).Satisfies Pt ↔ (finiteMemoryChip S q).Satisfies Pt)
        ∧ (∀ i, S.slot i ∈ (hostileMemoryChip S q).columnChallenges (53 : Fin 55))
        ∧ (∀ i, S.slot i ∉ (finiteMemoryChip S q).columnChallenges (53 : Fin 55)))
      ∧ (∀ T : StagedChip L 4 nockChronologyIO3, ProgIORecordsCommittedByRoundTwo T →
          ∀ col : Fin T.air.numTraceCols, 102 ≤ (col : ℕ) → (col : ℕ) ≤ 111 →
            ∀ i, S3.slot i ∉ T.columnChallenges col) := by
  have hdecl : ∀ i : Fin 2, S.slot i ∈ hostileComputeColumnChallenges S 111 := by
    intro i
    have hif : ((111 : Fin 113) : ℕ) ∈ finProgIoCoinCols ∨ ((111 : Fin 113) : ℕ) = 111 :=
      Or.inr rfl
    rw [hostileComputeColumnChallenges, if_pos hif]
    fin_cases i
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hdeclM : ∀ i : Fin 2, S.slot i ∈ hostileMemColumnChallenges S 53 := by
    intro i
    have hif : ((53 : Fin 55) : ℕ) ∈ finMemIoCoinCols ∨ ((53 : Fin 55) : ℕ) = 53 := Or.inr rfl
    rw [hostileMemColumnChallenges, if_pos hif]
    fin_cases i
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  refine ⟨⟨rfl, rfl, rfl, fun _ => Iff.rfl, hdecl,
      fun i => (io_records_read_no_io_coin S hfresh).1 111 (by decide) (by decide) i⟩,
    ⟨rfl, rfl, fun _ => Iff.rfl, hdeclM,
      fun i => (io_records_read_no_io_coin S hfresh).2 53 (by decide) (by decide) i⟩,
    fun T hT col h1 h2 i =>
      committed_early_excludes_the_io_coins_compute S3 T hT col h1 h2 i⟩

end HostileTwoMessageChip

end Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction

section Audit

open Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction

#check @io_lio_of_giga3_satisfies_at_production_coins
#check @perm_of_giga3_satisfies_at_production_coins
#check @composition3_coins_are_sampled
#check @accepted_giga3_certifies_io_perm_and_evalN
#check @giga3_satisfaction_is_the_same_proposition
#check @giga3_production_chips_are_unique
#check @giga3_bundle_at_production_coins
#check @giga3_composition_roundtrip_at_package_orbit
#check @end_to_end_conjuncts_nonvacuous
#check @schedule_conditions_are_discharged
#check @trivialChip3
#check @col_reads_receipt_is_inhabited
#check @hostileComputeChip
#check @two_message_exclusion_is_a_choice_three_message_is_not

#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction.io_lio_of_giga3_satisfies_at_production_coins
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction.perm_of_giga3_satisfies_at_production_coins
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction.composition3_coins_are_sampled
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction.accepted_giga3_certifies_io_perm_and_evalN
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction.giga3_satisfaction_is_the_same_proposition
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction.giga3_saturation_keeps_the_air_and_schedule
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction.giga3_production_chips_are_unique
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction.giga3_bundle_at_production_coins
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction.giga3_composition_roundtrip_at_package_orbit
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction.end_to_end_conjuncts_nonvacuous
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction.giga3_io_columns_undeclared
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction.schedule_conditions_are_discharged
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction.col_reads_receipt_is_inhabited
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction.hostileComputeColumns_commit_before_sampling
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction.hostileMemColumns_commit_before_sampling
#print axioms Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction.two_message_exclusion_is_a_choice_three_message_is_not

end Audit
