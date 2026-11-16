import Nock.NockVMROM.Thm54.PairedRecordCountedEvent
import Nock.NockVMROM.Thm54.BuildableTopology
import Nock.NockVMROM.Thm54.DistinctCensusExecution
import Nock.NockVMROM.Thm54.DistinctCensusCommitment
import Nock.RedTeam.Batch132Thm54PairedRecordCarrierOptions
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# The counted-event route for the `intermediate` pole

Different context from the
prover.  Nothing here inhabits any named premise, and **no carrier field is added**.

**Status of the cite only.  **The claim is unaffected** — `2120` says exactly what was attributed to `2119` — so the
equivalence, the sidestep and the non-vacuity finding all stand unchanged.

## Paper frame, body before appendix

* the paper — `read_root` adds a record to `intermediate`; `verify_child` removes one.
* the paper — "every timestamp needs to be removed from the `IO` multiset, added to
  `intermediate`, and then removed again".
* the paper — "an intermediate aggregator `intermediate ∈ K`"; the paper — its
  constraint at scalar `β, γ`, with the formal `X` of the paper instantiated to
  `−β` (the repo's flag `[M3]`).
* the paper — `Lem:ldse_mse`, whose only size condition is `char > n`.

**Scoped PASS on the equivalence and on the sidestep, with a FINDING against §G's non-vacuity
scope.**

2. **The sidestep is real.**  The `Nodup`-free exit is verified at the statement
   level: `redteam_exit_needs_no_nodup` is already an equivalence for an arbitrary
   `PreChallengeRecords` pair with no repeat-freeness anywhere.  **Refinement:** the claim is exact
   for the exit and for the *remove* column, and loose for the add column's cone — the length bound
   `interRecords_lengths_lt_ringChar` consumes comes from `added_length_inRange`
   (`PairedRecordIOResult.lean:108-112`), hence from `execution_lio_of_requestNodup`, hence from
   `E.requestNodup` and `addedRecordList_nodup`.  Nothing is weakened, both being unconditional on
   `E`; the wording should be scoped (`redteam_add_column_nodup_is_already_on_E`).  A mechanical cone
   scan was attempted and is **not available in this toolchain** — imported theorems come back with
   `ConstantInfo.value? = none`, so a walk sees definitions only; §C records that limitation.
3. Hence
   `concrete_counted_event_route_is_exercised` is a genuine J.0.3 exercise of
   `pairedRecordLayout_of_counted_events`.  The docstring claim in
   `MultiRoot.multiRoot_gamma_in_collision_event` — "this build contains no execution at which the
   three exclusions of §C hold simultaneously" — is therefore **too strong** and must be scoped to
   `multiRootExecution`.
4. **…and the witness confirms rather than overturns the non-closure.**  By §D's equivalence any such
   witness must satisfy the premise already, and at F73 the premise is available with **no counted
   event at all** (`concrete_pairedRecordLayout_without_counted_events`, from
   `pairedRecordLayout_of_addedRemovedAgain`).  So the witness exercises the route without extracting
   anything from it: `concrete_witness_extracts_nothing` compiles both readings side by side.
5. **The second unverified fixture is settled, and it is negative.**  At the F97
   `distinctCensusExecution` the table samples `γ = 0`, where the record RLC is `mem.root.size`
   alone; `recL` and `recR` are distinct records whose roots `leftFormula` and `rightFormula` have
   the **same leaf count** (three), so `enc_size` makes their compressed values equal and counted
   event (2) is **HIT** (`distinctCensus_gamma_in_collision_event`).

**Scoped PASS on the three Section-2 items reached; the rest is unverified and named as such.**

6. **The `[M3]` pole identification is right (§D).**  `FiniteIO.compress coins v = pole + RLC^gamma(v)`
   and `MemoryTable.pole inp r = RLC^γ(r) − β` are both `rfl`, `interCoins` is exactly `(γ, −β)` of the
   table tuple (`redteam_interCoins_is_the_table_tuple`, `rfl`), and the two poles are the **same
   field element** (`redteam_two_poles_coincide`, re-derived independently of
   `compress_interCoins`).  The identification is checked to be **non-degenerate and
   coordinate-order-sensitive** at `γ = 2`, `β = 5` over `ZMod 97`
   (`M3Concrete.redteam_m3_identification_is_order_sensitive`): the pole is nonzero and transposing
   two record coordinates changes it, so a mis-ordering of `Def:MEF`'s eight coordinates against
   the paper's monomials would have been visible.  No mis-identification.
7. **Counted event (1) holds at every live fixture (§E).**  `InterPoleGeneric` is produced at all
   three live `BuildableNockExecution`s — F73 (`ConcreteF73.concrete_interPoleGeneric`, from
   `honest_chained.memory_wf`), F97 multi-root (`F97Fixtures.multiRoot_interPoleGeneric`, from
   `memory_wf_allS`) and F97 census (`F97Fixtures.distinctCensus_interPoleGeneric`, from
   `memory_wf_allD`) — so `MemoryTable.WF` really does discharge event (1) wherever the
   carrier is inhabited, and `interPoleGeneric_of_wf` is not a vacuous convenience.
8. **The semantic-layer break is stated at the right layer (§F).**
   `redteam_semantic_layer_break` exhibits both objects together with their layers named: the
   external object is `IO.LIO` on `List (Fin 9 → K)` whose response list **is**
   `(addedRecordList E.exec).map encRec`, while the `intermediate` object is `IO.LmIO` on `List K`
   whose read list **is** `α`-powers of `AxisBridge.readExps` of the axis trees.
   `redteam_external_exclusions_are_named_inputs` confirms the external exclusions are `Inputs`
   fields.  And the difference is **information loss, not presentation**:
   `TimestampLoss.redteam_timestamp_matching_loses_the_record_permutation` exhibits two distinct
   records sharing a timestamp, so the timestamp-level matching cannot in general recover the record
   permutation.

Nothing here is a claim about the paper.  the paper samples `β, γ` at random; the fixtures pin
them to `0` for arithmetic convenience, which is what makes the record RLC degenerate at two of the
three fixtures.  The residual is a formalization-layer scope question, not a defect of the paper.

**Still unverified after Section 2.**  The generic `interPoleGeneric_of_wf` derivation is *used* rather than re-derived.

**Disclosure — no probability measure appears here.**  No distribution, no soundness error bound.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Nock.RedTeam.Batch135

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.PairedRecordIOResult
open Nock.NockVMROM.Thm54.PairedRecordCountedEvent
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

/-! ## §0. The certificate's numerator is the denominator's derivative -/

section Generic

variable {K : Type*} [Field K]

/-- **`numerP a = derivative (denomP a)`.**  The cleared-denominator numerator of a log-derivative
sum is the formal derivative of its denominator, because `derivative (X + C c) = 1`.  Field-generic,
no characteristic hypothesis, no finiteness. -/
theorem redteam_numerP_eq_derivative_denomP {n : ℕ} (a : Fin n → K) :
    FiniteIO.numerP a = Polynomial.derivative (FiniteIO.denomP a) := by
  rw [FiniteIO.denomP, Polynomial.derivative_prod_finset, FiniteIO.numerP]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp

end Generic

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## §A. The equivalence, independently re-derived and factored through the certificate

It is
re-derived here in two halves, so that the two hypotheses are seen to do different jobs:

* off counted event (2), and with **nothing else**, `ioQP = 0` is *equivalent* to the record
  permutation (`redteam_ioQP_zero_iff_perm`) — an abstract statement about a
  `FiniteIO.PreChallengeRecords` pair, with no execution anywhere in it;
* the genericity hypothesis (counted event (1)) is used only to turn "the sampled pole is not a root
  of a nonzero certificate" into "the certificate vanishes identically"
  (`redteam_logDerivGood_iff_ioQP_zero`), through `E`'s unconditional endpoint identity.

So the equivalence is not an artifact of the accumulator: it already holds at the certificate
level. -/

/-- **Reverse direction, independently and unconditionally.**  A record permutation forces the
certificate to vanish identically. -/
theorem redteam_ioQP_eq_zero_of_perm {records : FiniteIO.PreChallengeRecords K 9} (γ : K)
    (h : records.requests.Perm records.responses) :
    FiniteIO.ioQP records γ = 0 := by
  have hdenom : FiniteIO.denomP (FiniteIO.reqVals records γ)
      = FiniteIO.denomP (FiniteIO.respVals records γ) := by
    show FiniteIO.denomP
        (fun i : Fin records.requests.length => Walk.rlc γ (records.requests.get i))
      = FiniteIO.denomP
          (fun j : Fin records.responses.length => Walk.rlc γ (records.responses.get j))
    rw [denomP_eq_ms_prod, denomP_eq_ms_prod,
      Multiset.coe_eq_coe.mpr (h.map (Walk.rlc γ))]
  have hnum : FiniteIO.numerP (FiniteIO.reqVals records γ)
      = FiniteIO.numerP (FiniteIO.respVals records γ) := by
    rw [redteam_numerP_eq_derivative_denomP, redteam_numerP_eq_derivative_denomP, hdenom]
  simp only [FiniteIO.ioQP, hnum, hdenom, sub_self]

/-- **The certificate-level equivalence.**  For an arbitrary `PreChallengeRecords` pair whose two
column lengths sit below the characteristic, and off counted event (2), the certificate vanishes
identically **iff** the two columns are a permutation of each other.  No execution, no accumulator,
no genericity condition. -/
theorem redteam_ioQP_zero_iff_perm {records : FiniteIO.PreChallengeRecords K 9} (γ : K)
    (hk₁ : records.requests.length < ringChar K)
    (hk₂ : records.responses.length < ringChar K)
    (hγ : γ ∉ FiniteIO.IORLCCollisionEvent records) :
    FiniteIO.ioQP records γ = 0 ↔ records.requests.Perm records.responses := by
  classical
  refine ⟨fun hQ0 => ?_, redteam_ioQP_eq_zero_of_perm γ⟩
  have hQ : FiniteIO.numerP (FiniteIO.reqVals records γ)
        * FiniteIO.denomP (FiniteIO.respVals records γ)
      = FiniteIO.numerP (FiniteIO.respVals records γ)
        * FiniteIO.denomP (FiniteIO.reqVals records γ) := by
    have hh := hQ0
    unfold FiniteIO.ioQP at hh
    rwa [sub_eq_zero] at hh
  have hmse :
      (∏ i, (Polynomial.X + Polynomial.C (FiniteIO.reqVals records γ i)))
        = ∏ j, (Polynomial.X + Polynomial.C (FiniteIO.respVals records γ j)) :=
    (SetEq.mse_ldse_general (p := ringChar K) hk₁ hk₂ _ _).mpr
      (frac_sum_eq_of_ioQP_zero _ _ hQ)
  have hms :
      ((records.requests.map (Walk.rlc γ) : List K) : Multiset K)
        = ((records.responses.map (Walk.rlc γ) : List K) : Multiset K) := by
    refine (IO.prodXaddC_ms_inj _ _).mp ?_
    rw [← denomP_eq_ms_prod, ← denomP_eq_ms_prod]
    exact hmse
  refine perm_of_perm_map_of_injOn (Walk.rlc γ) ?_ (Multiset.coe_eq_coe.mp hms)
  intro u hu v hv heq
  exact FiniteIO.rlc_inj_of_not_collision hγ hu hv heq

/-- **Counted event (1) does exactly one job.**  Given the paper's the paper genericity, the
exclusion of counted event (3) *is* the vanishing of the certificate — because `E`'s endpoint
log-derivative identity already puts the sampled pole among the certificate's roots. -/
theorem redteam_logDerivGood_iff_ioQP_zero (E : BuildableNockExecution F K)
    (hgen : InterPoleGeneric E)
    (hC : E.exec.CprimeCoherent) :
    ((interCoins E).pole ∉
        FiniteIO.IOLogDerivEvent (interRecords E) (interCoins E).gamma)
      ↔ FiniteIO.ioQP (interRecords E) (interCoins E).gamma = 0 := by
  classical
  constructor
  · intro hz
    by_contra hne
    exact hz (by
      simp only [FiniteIO.IOLogDerivEvent, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hne, interQP_eval_eq_zero E hgen hC⟩)
  · intro hQ hmem
    simp only [FiniteIO.IOLogDerivEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem.1 hQ

/-- Both directions, assembled from the two halves above.
The verdict stands: off counted events (1) and (2), excluding counted event (3) is **equivalent** to
`PairedRecordLayout`, so it is a relocation of the named premise and not a weakening of it. -/
theorem redteam_interLogDerivGood_iff_pairedRecordLayout (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (hgen : InterPoleGeneric E)
    (hγ : (interCoins E).gamma ∉ FiniteIO.IORLCCollisionEvent (interRecords E)) :
    ((interCoins E).pole ∉
        FiniteIO.IOLogDerivEvent (interRecords E) (interCoins E).gamma)
      ↔ RowLayout.PairedRecordLayout E.exec := by
  obtain ⟨hk₁, hk₂⟩ := interRecords_lengths_lt_ringChar E hhon hC
  rw [redteam_logDerivGood_iff_ioQP_zero E hgen hC,
    redteam_ioQP_zero_iff_perm (interCoins E).gamma hk₁ hk₂ hγ]
  exact ⟨fun h => perm_of_perm_map_encRecC_cp E.exec.cprimeOf h,
    fun h => h.map (fun r => NockVM.encRecC r (E.exec.cprimeOf r))⟩

theorem redteam_agrees_with_ao114_iff (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (hgen : InterPoleGeneric E)
    (hγ : (interCoins E).gamma ∉ FiniteIO.IORLCCollisionEvent (interRecords E)) :
    (((interCoins E).pole ∉
          FiniteIO.IOLogDerivEvent (interRecords E) (interCoins E).gamma)
        ↔ RowLayout.PairedRecordLayout E.exec)
      ∧ (((interCoins E).pole ∉
          FiniteIO.IOLogDerivEvent (interRecords E) (interCoins E).gamma)
        ↔ RowLayout.PairedRecordLayout E.exec) :=
  ⟨redteam_interLogDerivGood_iff_pairedRecordLayout E hhon hC hgen hγ,
    interLogDerivGood_iff_pairedRecordLayout E hhon hC hgen hγ⟩

/-- **The shape of every possible witness, before any fixture is inspected.**  So a J.0.3 witness for the counted-event route can only ever be an
execution on which the premise was available anyway — which is precisely what §B finds at F73. -/
theorem redteam_any_witness_already_satisfies_the_premise (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (hgen : InterPoleGeneric E)
    (hγ : (interCoins E).gamma ∉ FiniteIO.IORLCCollisionEvent (interRecords E))
    (hz : (interCoins E).pole ∉
      FiniteIO.IOLogDerivEvent (interRecords E) (interCoins E).gamma) :
    RowLayout.PairedRecordLayout E.exec :=
  (redteam_interLogDerivGood_iff_pairedRecordLayout E hhon hC hgen hγ).mp hz

theorem redteam_logDerivEvent_empty_of_perm
    {records : FiniteIO.PreChallengeRecords K 9} (γ : K)
    (h : records.requests.Perm records.responses) :
    FiniteIO.IOLogDerivEvent records γ = ∅ := by
  classical
  rw [FiniteIO.IOLogDerivEvent, Finset.filter_eq_empty_iff]
  intro z _
  rintro ⟨hne, -⟩
  exact hne (redteam_ioQP_eq_zero_of_perm γ h)

/-! ## §B. THE FINDING — the F73 `concreteExecution` satisfies all three exclusions

That is false.  The F73 execution's two `intermediate` record columns are
literally the same one-element list, which makes counted event (2) unsatisfiable for want of an
unequal pair and counted event (3) empty. -/

namespace ConcreteF73

open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.BuildableConcrete

local instance : Fact (Nat.Prime 73) := concrete_prime73
noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- The F73 add column: the single `read_root` row's record. -/
theorem concrete_added :
    RowLayout.addedRecordList (exec honestSeed honestAlpha)
      = [rowRecord honestSeed honestAlpha] := by
  show (exec honestSeed honestAlpha).memoryRows.flatMap
      (fun row =>
        match row.2.2.st with
        | .read_root => [row.2.2.mem]
        | .decompose | .halt | .verify_child => []) = _
  rw [(execution_rows honestSeed honestAlpha).2]
  rfl

/-- Honest `ver` on the F73 concrete fixture. -/
theorem concrete_honestVer :
    ∀ row ∈ concreteExecution.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) :=
  BuildableChips.Concrete.concrete_honest_ver

/-- The F73 remove column: the single `verify_child` row's record — **the same record**. -/
theorem concrete_consumed :
    RowLayout.consumedRecordList (exec honestSeed honestAlpha)
      = [rowRecord honestSeed honestAlpha] := by
  show (exec honestSeed honestAlpha).memoryRows.flatMap
      (fun row => RowLayout.consumedRecords row.2.2) = _
  rw [(execution_rows honestSeed honestAlpha).2]
  rfl

/-- The two columns coincide as lists, not merely as multisets. -/
theorem concrete_consumed_eq_added :
    RowLayout.consumedRecordList (exec honestSeed honestAlpha)
      = RowLayout.addedRecordList (exec honestSeed honestAlpha) := by
  rw [concrete_consumed, concrete_added]

/-- **The premise holds at F73 with no counted event anywhere.**  Through the paper's own single
inclusion at the paper and `pairedRecordLayout_of_addedRemovedAgain`, which consumes only
objects already on `E`.  This is the honest reading of the witness below. -/
theorem concrete_pairedRecordLayout_without_counted_events :
    RowLayout.PairedRecordLayout concreteExecution.exec := by
  show RowLayout.PairedRecordLayout (exec honestSeed honestAlpha)
  rw [RowLayout.PairedRecordLayout, concrete_consumed_eq_added]

/-- The fixture's memory table samples `β = γ = 0`, so `interCoins` is the zero coin pair. -/
theorem concrete_interCoins :
    (interCoins concreteExecution).gamma = (0 : K73cubic)
      ∧ (interCoins concreteExecution).pole = (0 : K73cubic) :=
  ⟨rfl, neg_zero⟩

/-- Both encoded `FiniteIO` columns are the same singleton. -/
theorem concrete_interRecords :
    (interRecords concreteExecution).requests
        = [NockVM.encRecC (rowRecord honestSeed honestAlpha)
            ((exec honestSeed honestAlpha).cprimeOf (rowRecord honestSeed honestAlpha))]
      ∧ (interRecords concreteExecution).responses
        = [NockVM.encRecC (rowRecord honestSeed honestAlpha)
            ((exec honestSeed honestAlpha).cprimeOf (rowRecord honestSeed honestAlpha))] := by
  refine ⟨?_, ?_⟩
  · show (RowLayout.consumedRecordList (exec honestSeed honestAlpha)).map
        (fun r => NockVM.encRecC r ((exec honestSeed honestAlpha).cprimeOf r)) = _
    rw [concrete_consumed]; rfl
  · show (RowLayout.addedRecordList (exec honestSeed honestAlpha)).map
        (fun r => NockVM.encRecC r ((exec honestSeed honestAlpha).cprimeOf r)) = _
    rw [concrete_added]; rfl

/-- Every value occurring in either column is the one encoded record. -/
theorem concrete_mem_eq {v : Fin 9 → K73cubic}
    (hv : v ∈ (interRecords concreteExecution).requests
      ++ (interRecords concreteExecution).responses) :
    v = NockVM.encRecC (rowRecord honestSeed honestAlpha)
      ((exec honestSeed honestAlpha).cprimeOf (rowRecord honestSeed honestAlpha)) := by
  obtain ⟨hreq, hresp⟩ := concrete_interRecords
  rw [hreq, hresp] at hv
  simpa using hv

theorem concrete_interPoleGeneric : InterPoleGeneric concreteExecution :=
  interPoleGeneric_of_wf concreteExecution honest_chained.memory_wf
    (execution_cprimeCoherent honestSeed honestAlpha)

/-- **Counted event (2) is excluded at F73** — and structurally, not numerically: the collision
predicate demands two *unequal* occurring records, and only one record occurs.  No arithmetic in
`K73cubic` is performed. -/
theorem concrete_gammaGood :
    (interCoins concreteExecution).gamma
      ∉ FiniteIO.IORLCCollisionEvent (interRecords concreteExecution) := by
  classical
  intro hmem
  simp only [FiniteIO.IORLCCollisionEvent, Finset.mem_filter, Finset.mem_univ,
    true_and] at hmem
  obtain ⟨u, hu, v, hv, hne, -⟩ := hmem
  exact hne ((concrete_mem_eq hu).trans (concrete_mem_eq hv).symm)

/-- **Counted event (3) is excluded at F73**, because it is the empty set there: the two columns
match, so the certificate vanishes identically. -/
theorem concrete_poleGood :
    (interCoins concreteExecution).pole
      ∉ FiniteIO.IOLogDerivEvent (interRecords concreteExecution)
          (interCoins concreteExecution).gamma := by
  rw [redteam_logDerivEvent_empty_of_perm (interCoins concreteExecution).gamma
    (concrete_pairedRecordLayout_without_counted_events.map
      (fun r => NockVM.encRecC r (concreteExecution.exec.cprimeOf r)))]
  simp

/-- **THE FINDING, compiled.** -/
theorem concrete_all_three_exclusions_hold :
    InterPoleGeneric concreteExecution
      ∧ (interCoins concreteExecution).gamma
          ∉ FiniteIO.IORLCCollisionEvent (interRecords concreteExecution)
      ∧ (interCoins concreteExecution).pole
          ∉ FiniteIO.IOLogDerivEvent (interRecords concreteExecution)
              (interCoins concreteExecution).gamma :=
  ⟨concrete_interPoleGeneric, concrete_gammaGood, concrete_poleGood⟩

theorem concrete_counted_event_route_is_exercised :
    RowLayout.PairedRecordLayout concreteExecution.exec :=
  pairedRecordLayout_of_counted_events concreteExecution concrete_honestVer
    (execution_cprimeCoherent honestSeed honestAlpha)
    concrete_interPoleGeneric concrete_gammaGood concrete_poleGood

/-- The bridge to `MemoryRecordPremises.timestampClosed` is exercised too, at the same fixture. -/
theorem concrete_timestampClosed_route_is_exercised :
    ∀ i : Fin concreteExecution.cfg.memRows,
      memoryMemRecKind (concreteExecution.exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt concreteExecution.cfg.challenges.α
          (concreteExecution.exec.memoryRowAt i).2.2.mem.ts :=
  timestampClosed_of_counted_events concreteExecution concrete_honestVer
    (execution_cprimeCoherent honestSeed honestAlpha)
    concrete_interPoleGeneric concrete_gammaGood concrete_poleGood

/-- **…and the witness extracts nothing.** -/
theorem concrete_witness_extracts_nothing :
    RowLayout.PairedRecordLayout concreteExecution.exec
      ∧ RowLayout.PairedRecordLayout concreteExecution.exec :=
  ⟨concrete_pairedRecordLayout_without_counted_events,
    concrete_counted_event_route_is_exercised⟩

end ConcreteF73

/-! ## F97 `distinctCensusExecution`

For the census fixture the answer is **yes**,
and for the same structural reason as at `multiRootExecution`: the table samples `γ = 0`, where
`RLC^γ` collapses onto `mem.root.size`, and `GlobalCarryRecognizer.enc_size` makes that coordinate
`z ^ (#leaves)`.  `leftFormula = [1 [7 9]]` and `rightFormula = [1 [8 10]]` have the same three
leaves, so `recL` and `recR` — distinct records — share their compressed value. -/

namespace DistinctCensusF97

open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.EqualityOperandCensus
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete

local instance prime97b135 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97b135 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

-- Form R leftover first-row `counts = 0` (live is `chainOneBitWeight`).
variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)

/-- The census fixture's memory compression challenge and pole offset are both `0`. -/
theorem distinctCensus_interCoins :
    (interCoins (distinctCensusExecution hfirstD)).gamma = (0 : K97cubic)
      ∧ (interCoins (distinctCensusExecution hfirstD)).pole = (0 : K97cubic) :=
  ⟨rfl, neg_zero⟩

/-- The fixture's encoded add column, read off `derived_responsesD`. -/
theorem distinctCensus_responses :
    (interRecords (distinctCensusExecution hfirstD)).responses
      = [NockVM.encRecFormR recF MemoryTable.formRDefault,
          NockVM.encRecFormR recT MemoryTable.formRDefault, NockVM.encRecFormR recL
              MemoryTable.formRDefault,
          NockVM.encRecFormR recR MemoryTable.formRDefault] := by
  change (RowLayout.addedRecordList execD).map (fun r => NockVM.encRecC r (execD.cprimeOf r)) = _
  have hhon : ∀ row ∈ execD.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
    simpa [distinctCensusExecution] using DistinctCensusCommitment.honestVerD hfirstD
  rw [← GenericHonestData.rawResponses_eq_addedRecordList execD hhon,
    ← ExactExecution.derivedResponseIO_eq_map_encRecC _
        DistinctCensusExecution.execD_cprimeCoherent]
  exact derived_responsesD

/-- The two equality-operand formulas have the same leaf count. -/
theorem leftFormula_leaves_eq_rightFormula_leaves :
    leftFormula.leaves = rightFormula.leaves := by
  decide

/-- At `γ = 0` the record RLC is `mem.root.size = z ^ (#leaves)`, and `recL`, `recR` share it. -/
theorem distinctCensus_records_collide_at_gamma_zero :
    Walk.rlc (interCoins (distinctCensusExecution hfirstD)).gamma (NockVM.encRecFormR recL
        MemoryTable.formRDefault)
      = Walk.rlc (interCoins (distinctCensusExecution hfirstD)).gamma (NockVM.encRecFormR recR
          MemoryTable.formRDefault) := by
  have hγ : (interCoins (distinctCensusExecution hfirstD)).gamma = (0 : K97cubic) := rfl
  rw [← NockVM.encRecC_formRRow, ← NockVM.encRecC_formRRow, rlc_encRecC, rlc_encRecC, hγ]
  simp only [MemoryTable.recRLC, NockVM.formRRow, recL, recR, encD,
    GlobalCarryRecognizer.enc_size]
  rw [leftFormula_leaves_eq_rightFormula_leaves]
  ring

/-- `recL` and `recR` are distinct: their timestamps are `α ^ 3` and `α ^ 4` at a generator of
order `24`. -/
theorem recL_ne_recR : NockVM.encRecFormR recL MemoryTable.formRDefault
    ≠ NockVM.encRecFormR recR MemoryTable.formRDefault :=
  encRecC_ne_of_ts_ne (by
    rw [ts_recL, ts_recR]
    simpa [alphaD] using
      fixtureAlpha_pow_ne (m := 3) (n := 4) (by norm_num) (by norm_num) (by norm_num))

/-- **Counted event (2) is HIT at the live F97 census execution too.** -/
theorem distinctCensus_gamma_in_collision_event :
    (interCoins (distinctCensusExecution hfirstD)).gamma
      ∈ FiniteIO.IORLCCollisionEvent (interRecords (distinctCensusExecution hfirstD)) := by
  classical
  have hmem : ∀ v ∈ (interRecords (distinctCensusExecution hfirstD)).responses,
      v ∈ (interRecords (distinctCensusExecution hfirstD)).requests
        ++ (interRecords (distinctCensusExecution hfirstD)).responses :=
    fun v hv => List.mem_append_right _ hv
  have h1 : NockVM.encRecFormR recL MemoryTable.formRDefault ∈ (interRecords
      (distinctCensusExecution hfirstD)).responses := by
    rw [distinctCensus_responses hfirstD]; simp
  have h2 : NockVM.encRecFormR recR MemoryTable.formRDefault ∈ (interRecords
      (distinctCensusExecution hfirstD)).responses := by
    rw [distinctCensus_responses hfirstD]; simp
  simp only [FiniteIO.IORLCCollisionEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨_, hmem _ h1, _, hmem _ h2, recL_ne_recR,
    distinctCensus_records_collide_at_gamma_zero hfirstD⟩

end DistinctCensusF97

/-! ## §C. The sidestep, and the `Nodup`-free exit

**Both halves check out, and both are settled at the statement level rather than by a proof-term
scan.**  A mechanical transitive-constant scan was attempted and is *not available in this
toolchain*: `Environment.find?` (and `Kernel.Environment.find?`) return imported theorems with
`ConstantInfo.value?  = none` here, so a cone walk sees definitions only and cannot decide which
lemmas a proof cites.  That limitation is recorded rather than papered over.  What replaces it:

* **Field size.**  Since the theorem compiles, it cannot be consuming a
  bound that is neither hypothesis nor consequence.  **Verified.**
* **The exit.**  `redteam_exit_needs_no_nodup` restates the load-bearing step for an **arbitrary**
  `FiniteIO.PreChallengeRecords` pair, with no `Nodup` on either column and no `E` — and it is
  already an equivalence at that generality, so the exit genuinely does not need repeat-freeness.
  **Verified.**
* **Refinement, disclosed.**  The claim is exact for the exit and for the *remove* column, and loose
  for the add column's cone.  `PairedRecordIOResult.added_length_inRange`
  (`Nock/NockVMROM/Thm54/PairedRecordIOResult.lean:108-112`) obtains the length bound that
  `interRecords_lengths_lt_ringChar` needs from `GenericHonestData.execution_lio_of_requestNodup`,
  which consumes `E.requestNodup` and the add column's `addedRecordList_nodup`.  Nothing is weakened
  — both are unconditional on `E`, which is exactly why the route works — but "neither column has to
  be repeat-free" should be read as "no repeat-freeness *hypothesis* is taken, and the remove column
  has none available".  `redteam_add_column_nodup_is_already_on_E` compiles the disclosure. -/

/-- **Disclosure receipt for the `Nodup`-free claim.**  The add column is unconditionally repeat-free
on `E`, and the very object that supplies its `Nodup` also supplies the length bound the counted-event
route consumes.  So the route takes no repeat-freeness *hypothesis* — the accurate form of the claim
— while the add column's `Nodup` is nonetheless available in the cone of its length bound. -/
theorem redteam_add_column_nodup_is_already_on_E (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent) :
    (RowLayout.addedRecordList E.exec).Nodup
      ∧ IO.LIO E.cfg.Ksz E.exec.derivedRequestIO E.exec.derivedResponseIO
      ∧ IO.InRange E.cfg.Ksz (RowLayout.addedRecordList E.exec).length
      ∧ IO.InRange E.cfg.Ksz (RowLayout.consumedRecordList E.exec).length :=
  ⟨GenericHonestData.addedRecordList_nodup E hhon hC,
    GenericHonestData.execution_lio_of_requestNodup E,
    PairedRecordIOResult.added_length_inRange E hhon hC,
    PairedRecordIOResult.consumed_length_inRange E hhon hC⟩

/-- **The statement-shape half of the sidestep, restated so it is on the record.** -/
theorem redteam_sidestep_is_characteristic_only (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent) :
    ((interRecords E).requests.length < ringChar K
        ∧ (interRecords E).responses.length < ringChar K
        ∧ E.cfg.Ksz < ringChar K)
      ∧ ((4 : ℕ) < ringChar (ZMod 5) ∧ Fintype.card (ZMod 5) < 4 * 4) :=
  ⟨closure_uses_only_the_characteristic_bound E hhon hC,
    Batch132.characteristic_bound_is_not_the_field_size_bound⟩

/-- **The `Nodup`-free half, at the statement level.**  Neither the certificate-level equivalence nor
the counted-event theorem takes a repeat-freeness hypothesis on either record column: the
certificate-level form above is stated for an arbitrary `PreChallengeRecords` pair, with `Nodup`
nowhere in sight, and it is already an equivalence there. -/
theorem redteam_exit_needs_no_nodup {records : FiniteIO.PreChallengeRecords K 9} (γ : K)
    (hk₁ : records.requests.length < ringChar K)
    (hk₂ : records.responses.length < ringChar K)
    (hγ : γ ∉ FiniteIO.IORLCCollisionEvent records) :
    FiniteIO.ioQP records γ = 0 ↔ records.requests.Perm records.responses :=
  redteam_ioQP_zero_iff_perm γ hk₁ hk₂ hγ

/-! ## §D. The `[M3]` pole identification — `compress_interCoins` re-checked

That is the load-bearing identification of the whole
route: if the two poles were different objects, §B's endpoint identity would be about the wrong
denominators.  Three things are checked here.

* The two unfoldings are what the paper says: `FiniteIO.compress coins v = coins.pole + RLC^gamma(v)` and
  `MemoryTable.pole inp r = RLC^γ(r) − β`.
* The identification is **coordinate-order-sensitive and non-degenerate**, so it is not an accident of
  a symmetric or vanishing configuration: at `γ = 2`, `β = 5` over `ZMod 97` a record and its
  `root.dyck`/`root.leaf`-swapped partner get *different* poles, and the pole is nonzero.  A
  mis-ordering of `Def:MEF`'s eight coordinates against the paper's monomials would therefore
  have been visible.
* `interCoins` reads the table tuple, not the later `RAP_prog-IO` sample. -/

section PoleIdentification

/-- `FiniteIO`'s compression is the additive-pole form of the paper. -/
theorem redteam_compress_unfold (coins : FiniteIO.IOCoins K) (v : Fin 9 → K) :
    FiniteIO.compress coins v = coins.pole + Walk.rlc coins.gamma v := rfl

/-- `MemoryTable.pole` is the paper's `RLC^γ(mem_record) − β`; the `[M3]` instantiation is `X ↦ −β`. -/
theorem redteam_memory_pole_unfold (inp : MemoryTable.Inputs K) (r : ComputeTable.MemRec K) :
    MemoryTable.pole inp r = MemoryTable.recRLC inp.γ r - inp.β := rfl

/-- `interCoins` is exactly `(γ, −β)` of the memory table's own tuple — the `[M3]` reading. -/
theorem redteam_interCoins_is_the_table_tuple (E : BuildableNockExecution F K) :
    interCoins E
      = { gamma := E.cfg.challenges.memoryInputs.γ
          pole := -E.cfg.challenges.memoryInputs.β } := rfl

theorem redteam_two_poles_coincide (E : BuildableNockExecution F K)
    (r : ComputeTable.MemRec K) :
    FiniteIO.compress (interCoins E) (NockVM.encRec r)
      = MemoryTable.pole E.cfg.challenges.memoryInputs r := by
  rw [redteam_compress_unfold, redteam_memory_pole_unfold, rlc_encRec]
  show -E.cfg.challenges.β + MemoryTable.recRLC E.cfg.challenges.γ r
    = MemoryTable.recRLC E.cfg.challenges.memoryInputs.γ r - E.cfg.challenges.memoryInputs.β
  show -E.cfg.challenges.β + MemoryTable.recRLC E.cfg.challenges.γ r
    = MemoryTable.recRLC E.cfg.challenges.γ r - E.cfg.challenges.β
  ring

namespace M3Concrete

abbrev F97b135 := ZMod 97

local instance prime97m3 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
local instance charF97m3 : CharP F97b135 (ringChar F97b135) := ringChar.charP F97b135

/-- A record with eight pairwise-distinct coordinates, so every monomial of the paper is
separately visible. -/
def r8 : ComputeTable.MemRec F97b135 := ⟨⟨1, 2, 3⟩, ⟨4, 5, 6⟩, 7, 8⟩

/-- The same record with `root.dyck` and `root.leaf` transposed. -/
def r8swap : ComputeTable.MemRec F97b135 := ⟨⟨1, 3, 2⟩, ⟨4, 5, 6⟩, 7, 8⟩

def inp8 : MemoryTable.Inputs F97b135 := ⟨0, 5, 2⟩

/-- **The `[M3]` identification is non-degenerate and coordinate-order-sensitive.**  At `γ = 2`,
`β = 5` the two `FiniteIO` compressions agree with the two memory-table poles, the pole is nonzero,
and transposing two record coordinates changes it — so the eight-coordinate `Def:MEF` flattening is
matched against the paper's monomials in the right order. -/
theorem redteam_m3_identification_is_order_sensitive :
    FiniteIO.compress ⟨2, -5⟩ (NockVM.encRec r8) = MemoryTable.pole inp8 r8
      ∧ FiniteIO.compress ⟨2, -5⟩ (NockVM.encRec r8swap) = MemoryTable.pole inp8 r8swap
      ∧ MemoryTable.pole inp8 r8 ≠ MemoryTable.pole inp8 r8swap
      ∧ MemoryTable.pole inp8 r8 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [redteam_compress_unfold, rlc_encRec, redteam_memory_pole_unfold]
    show (-5 : F97b135) + MemoryTable.recRLC 2 r8 = MemoryTable.recRLC 2 r8 - 5
    ring
  · rw [redteam_compress_unfold, rlc_encRec, redteam_memory_pole_unfold]
    show (-5 : F97b135) + MemoryTable.recRLC 2 r8swap = MemoryTable.recRLC 2 r8swap - 5
    ring
  · simp only [MemoryTable.pole, MemoryTable.recRLC, inp8, r8, r8swap]
    norm_num
    decide
  · simp only [MemoryTable.pole, MemoryTable.recRLC, inp8, r8]
    norm_num
    decide

end M3Concrete

end PoleIdentification

/-! ## §E. Counted event (1) is discharged at EVERY live fixture

That is checked here by
producing `InterPoleGeneric` at all three live `BuildableNockExecution`s of this build — so the
hypothesis is not merely satisfiable in principle but held everywhere the carrier is inhabited. -/

section EventOneAtFixtures

namespace F97Fixtures

open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete

local instance prime97f : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97f : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

-- Form R leftover first-row `counts = 0` (live is `chainOneBitWeight`).
variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)

/-- Counted event (1) at the F97 two-serviced-root execution. -/
theorem multiRoot_interPoleGeneric : InterPoleGeneric multiRootExecution :=
  interPoleGeneric_of_wf multiRootExecution memory_wf_allS execS_cprimeCoherent

/-- Counted event (1) at the F97 distinct-pair census execution. -/
theorem distinctCensus_interPoleGeneric :
    InterPoleGeneric (distinctCensusExecution hfirstD) :=
  interPoleGeneric_of_wf (distinctCensusExecution hfirstD) memory_wf_allD execD_cprimeCoherent

end F97Fixtures

end EventOneAtFixtures

/-! ## §F.

Three checks.

* The external object really is at the **record** level and its two lists really are the encoded
  record columns.
* The `intermediate` object really is at the **axis-tree exponent** level: `forestReadTimestamps` /
  `forestVerifyTimestamps` are `α ^ e` powers of `readExps`/`verifyExps` of the axis trees, so they
  are `List K`, not `List (Fin 9 → K)`.
* The layer difference is **information loss, not presentation**: two distinct records can share a
  timestamp, so a timestamp-level matching cannot in general recover the record
  permutation.  That is why the paper routes the record matching through `Thm:IO_result`. -/

section SemanticLayer

/-- **The break, compiled with both layers named.**  Left: the external columns' record-level
`IO.LIO`, unconditional on `E`, with its two lists exhibited as the encoded record columns.  Right:
the `intermediate` object, exhibited as `α`-powers of axis-tree exponents. -/
theorem redteam_semantic_layer_break (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent) :
    IO.LIO E.cfg.Ksz E.exec.derivedRequestIO E.exec.derivedResponseIO
      ∧ E.exec.derivedResponseIO =
          (RowLayout.addedRecordList E.exec).map (fun r => NockVM.encRecC r (E.exec.cprimeOf r))
      ∧ IO.LmIO E.cfg.Ksz (forestReadTimestamps E.cfg E.execA)
          (forestVerifyTimestamps E.cfg E.execA)
      ∧ forestReadTimestamps E.cfg E.execA
          = (List.finRange E.cfg.kMem).flatMap (fun i =>
              (AxisBridge.readExps (exactAxisTree E.cfg E.execA i)).map
                (fun e => E.cfg.challenges.α ^ e)) :=
  ⟨GenericHonestData.execution_lio_of_requestNodup E,
    by
      rw [ExactExecution.derivedResponseIO_eq_map_encRecC _ hC,
        GenericHonestData.rawResponses_eq_addedRecordList _ hhon],
    GenericHonestData.execution_structural_intermediate_matching E, rfl⟩

/-- The external columns' three counted-event exclusions are **named `Inputs` fields**, so importing
the counted-event shape for `intermediate` imports an assumption of the same tier.  Re-derived by
projection, which is the whole content of the claim. -/
theorem redteam_external_exclusions_are_named_inputs
    {E : BuildableNockExecution F K} (I : BuildableChips.Inputs E) :
    I.ioCoins.pole ∉
        FiniteIO.IOPoleHitEvent (BuildableChips.executionRecords E) I.ioCoins.gamma
      ∧ I.ioCoins.gamma ∉
          FiniteIO.IORLCCollisionEvent (BuildableChips.executionRecords E)
      ∧ I.ioCoins.pole ∉
          FiniteIO.IOLogDerivEvent (BuildableChips.executionRecords E) I.ioCoins.gamma :=
  ⟨I.ioPoleHitGood, I.ioGammaGood, I.ioLogDerivGood⟩

namespace TimestampLoss

open Nock.NockVMROM.Thm54.PairedRecordIOResult.Concrete

local instance prime97tl : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- **The layer difference is information loss.**  Two distinct records with the same timestamp: the
timestamp-level column pair matches while the record-level column pair does not. -/
theorem redteam_timestamp_matching_loses_the_record_permutation :
    ([rootA].map (fun r : ComputeTable.MemRec (ZMod 97) => r.ts))
        = [rootB].map (fun r => r.ts)
      ∧ ¬ ([rootA] : List (ComputeTable.MemRec (ZMod 97))).Perm [rootB] := by
  refine ⟨by simp [rootA, rootB], ?_⟩
  intro h
  have hmem : rootA ∈ ([rootB] : List (ComputeTable.MemRec (ZMod 97))) :=
    h.mem_iff.mp List.mem_cons_self
  have : rootA = rootB := by simpa using hmem
  exact timestampKeyedColumns_is_about_mem_root.2.1 this

end TimestampLoss

end SemanticLayer

/-! ## §G. Accounting — nothing inhabited, nothing added, nothing ticked -/

theorem execution_eta_still_fourteen_fields_batch135 (E : BuildableNockExecution F K) :
    E =
      { q := E.q
        q_gt_one := E.q_gt_one
        Λ := E.Λ
        cfg := E.cfg
        execA := E.execA
        exec := E.exec
        exec_encode := E.exec_encode
        semanticData := E.semanticData
        memoryTrace := E.memoryTrace
        requestNodup := E.requestNodup
        recordCountBalance := E.recordCountBalance
        q_le_ringChar := E.q_le_ringChar
        two_ne_zero := E.two_ne_zero
        Ksz_lt_ringChar := E.Ksz_lt_ringChar
        programIOCapacity := E.programIOCapacity
        memoryIOCapacity := E.memoryIOCapacity } :=
  E.eta_with_memoryTrace

/-- `BuildableChips.Inputs` is unchanged: fifteen fields, the three IO goodness flags still named. -/
theorem inputs_eta_unchanged_batch135 {E : BuildableNockExecution F K}
    (I : BuildableChips.Inputs E) :
    I =
      { stateTagChar := I.stateTagChar
        computeWalkAlpha := I.computeWalkAlpha
        memoryWalkAlpha := I.memoryWalkAlpha
        walkGamma := I.walkGamma
        hOrb := I.hOrb
        basis := I.basis
        orbit := I.orbit
        activeDomains := I.activeDomains
        ioCoins := I.ioCoins
        ioPoleHitGood := I.ioPoleHitGood
        ioGammaGood := I.ioGammaGood
        ioLogDerivGood := I.ioLogDerivGood
        computeChallenges := I.computeChallenges
        memoryScalarChallenge := I.memoryScalarChallenge
        memoryExtensionFold := I.memoryExtensionFold
        interPoleHitGood := I.interPoleHitGood
        honestVer := I.honestVer
        ioGood10 := I.ioGood10
        interPoleHitGood10 := I.interPoleHitGood10 } := by
  cases I
  rfl

/-- `MemoryRecordPremises` still has its two fields; `timestampClosed` is still named. -/
theorem memoryRecordPremises_still_two_batch135
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
      (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) :=
  GenericHonestData.memoryRecordPremises_still_two_after_logup_inventory M

/-- The `11+1+2` fourteen-field partition of the released capstone statement is unchanged, per
`Batch91.exact_eleven_one_two_partition` and not reinterpreted. -/
theorem exact_eleven_one_two_batch135 : 11 + 1 + 2 = 14 :=
  GenericHonestPackage.residual_pair_still_eleven_one_two_after_logup_inventory

/-- The consumed capstone and its paper alias are untouched. -/
theorem consumed_capstone_untouched_batch135 [Fintype F] [DecidableEq F]
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement P :=
  OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth


#print axioms redteam_numerP_eq_derivative_denomP
#print axioms redteam_ioQP_eq_zero_of_perm
#print axioms redteam_ioQP_zero_iff_perm
#print axioms redteam_logDerivGood_iff_ioQP_zero
#print axioms redteam_interLogDerivGood_iff_pairedRecordLayout
#print axioms redteam_agrees_with_ao114_iff
#print axioms redteam_any_witness_already_satisfies_the_premise
#print axioms redteam_logDerivEvent_empty_of_perm
#print axioms ConcreteF73.concrete_added
#print axioms ConcreteF73.concrete_consumed
#print axioms ConcreteF73.concrete_consumed_eq_added
#print axioms ConcreteF73.concrete_pairedRecordLayout_without_counted_events
#print axioms ConcreteF73.concrete_interCoins
#print axioms ConcreteF73.concrete_interRecords
#print axioms ConcreteF73.concrete_mem_eq
#print axioms ConcreteF73.concrete_interPoleGeneric
#print axioms ConcreteF73.concrete_gammaGood
#print axioms ConcreteF73.concrete_poleGood
#print axioms ConcreteF73.concrete_all_three_exclusions_hold
#print axioms ConcreteF73.concrete_counted_event_route_is_exercised
#print axioms ConcreteF73.concrete_timestampClosed_route_is_exercised
#print axioms ConcreteF73.concrete_witness_extracts_nothing
#print axioms DistinctCensusF97.distinctCensus_interCoins
#print axioms DistinctCensusF97.distinctCensus_responses
#print axioms DistinctCensusF97.leftFormula_leaves_eq_rightFormula_leaves
#print axioms DistinctCensusF97.distinctCensus_records_collide_at_gamma_zero
#print axioms DistinctCensusF97.recL_ne_recR
#print axioms DistinctCensusF97.distinctCensus_gamma_in_collision_event
#print axioms redteam_add_column_nodup_is_already_on_E
#print axioms redteam_sidestep_is_characteristic_only
#print axioms redteam_exit_needs_no_nodup
#print axioms redteam_compress_unfold
#print axioms redteam_memory_pole_unfold
#print axioms redteam_interCoins_is_the_table_tuple
#print axioms redteam_two_poles_coincide
#print axioms M3Concrete.redteam_m3_identification_is_order_sensitive
#print axioms F97Fixtures.multiRoot_interPoleGeneric
#print axioms F97Fixtures.distinctCensus_interPoleGeneric
#print axioms redteam_semantic_layer_break
#print axioms redteam_external_exclusions_are_named_inputs
#print axioms TimestampLoss.redteam_timestamp_matching_loses_the_record_permutation
#print axioms execution_eta_still_fourteen_fields_batch135
#print axioms inputs_eta_unchanged_batch135
#print axioms memoryRecordPremises_still_two_batch135
#print axioms exact_eleven_one_two_batch135
#print axioms consumed_capstone_untouched_batch135

end

end Nock.RedTeam.Batch135
