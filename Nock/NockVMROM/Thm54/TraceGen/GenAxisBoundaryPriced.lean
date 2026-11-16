/-
  Nock/NockVMROM/Thm54/TraceGen/GenAxisBoundaryPriced.lean

  **The axis-counts boundary, priced: spend an existing budget instead of carrying a stronger
  premise.**

  `GenServedFromRecord.CommittedRecordWitness` carries `terminal`, the *perfect* boundary
  `countsP = 0` as a polynomial identity.  The AIR checks the **evaluated** boundary: the appendix's
  `pt.counts : 𝕂` is a single field element, and the body says outright that
  `axis_indicator`/`axis_counts` "are represented by their evaluation at a random extension field
  element, which makes them individual elements in `𝕂`".  The `halt`-state zero
  check and the terminal accounting sentence are therefore
  checks on that evaluation.

  This module closes the gap in the cheapest available way, and the headline is a *negative* result
  about the residual:

  ## The event is already summand 4 — nothing needs adding to `FailureUnion`

  `ProductionP8Containment.specializedAxisValidity_of_accepts` (`:477`) **already** performs the
  lift: from `T.Accepts ω` — whose `RootAxisBoundaryAt` conjunct (`:468`) *is* the evaluated
  boundary `∀ i, (templateAxisPolynomial …).eval (alphaM ω) = 0` — together with
  `ω ∉ guardedAxisFailureEvent T`, it concludes `ExactMemoryAxisValidity`, i.e. `vaxis e = Relaxis e`
  at every record used on both sides of every authoritative memory root.  `guardedAxisFailureEvent`
  is summand 4 of `FailureUnion` (`:545`) and its cardinality is `fixedAxisWorkload T`
  (`guardedAxisFailureEvent_card_le`, `:459`), which is already a summand of `workload` (`:549`).

  What was missing was not a budget but a *shape*: `axis_batching_sound` was
  being called with `countsP = 0`, when everything downstream of it needs only its conclusion at
  one exponent.  §C below makes that substitution, and it costs strictly less than the perfect
  boundary: `committed_axis_eq_address_of_valid` does not even need `(2 : K) ≠ 0`.

  ## Map

  * §B  the *guarded*, staged lift — the shape summand 4 actually uses: the polynomial is fixed
        before the challenge, the bad witness is read on the specialized tree, and the conclusion is
        pointwise axis validity rather than the polynomial identity.  `§B` also proves that the
        guarded set and `ProductionAxisStructureVerifier.verifierGuardedRootAlphas` **agree**
        wherever the verifier's own two structural checks pass.
  * §C  pointwise validity replaces the perfect boundary in the address identification.
  * §D  `PricedRecordWitness`: `CommittedRecordWitness` with `terminal` deleted, the free exponent
        oracle replaced by `AxisSoundness.timestampExpAt`, and the boundary supplied once, globally,
        by `ExactMemoryAxisValidity`.
  * §E  `ServedSlotCovers` from priced witnesses, and then from production acceptance outside
        summand 4 — no boundary premise anywhere in the statement.

  ## Honest accounting

  Nothing here discharges the other three residuals of `IK` §4.  §D/§E still carry, and name:

  * the **IO record matching** (`recRoot`, `recChild`, `expRoot`, `route`) — that the record the
    compute table emitted is the one this walk's `read_root`/`verify_child` pair serves;
  * `Service.timestamp` — the compute-side line-number closed form, still a
    premise `hts`;
  * the unbounded `S.card` and `addr < q` conjuncts of `ServedSlotCovers`.

  Newly named here, and *not* present in `GenServedFromRecord`: `rootIndex`/`nest`, that the served
  region's `read_root` sits inside one of the execution's authoritative memory roots
  (`exec.memoryTreeAt i`).  That premise is *why* the global boundary applies to this record, and
  it replaces a `countsP = 0` on the region's own standalone walk — which the AIR never checks,
  since `RootAxisBoundaryAt` is per authoritative root.  `IK` §4's closing caveat (a `read_root`
  nested inside a larger walk needs the count-localization extended above it) is **closed**, by
  `ReadRootNest.spec`: the nesting may be at any depth.

  Scope: §A–§D are `∀ K` field-generic with no fixed axis, prime, program or fixture.  §E's
  production headline is over an arbitrary `ProductionStrategy F K` at `p = ringChar K`, `∀ ω`.

  -- check), 1427 (terminal accounting), 1450 (`N, L ∈ negl(𝕂)`), 2099 (`pt.counts : 𝕂`),
  -- 2333 (the paper's only Schwartz–Zippel invocation, for the NPR)
-/
import Nock.NockVMROM.Thm54.TraceGen.GenServedFromRecord
import Nock.NockVMROM.Thm54.ProductionP8Containment

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced

open scoped Classical Polynomial

open Nock Nock.Walk
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.TraceGen.GenNounRecovery
open Nock.NockVMROM.Thm54.TraceGen.GenServedFromRecord

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## §A.  The univariate lift: the evaluated boundary buys the polynomial identity

the paper says the two polynomial columns are represented by their evaluation at a random
extension-field element.  So what the AIR gives is `(countsP t).eval a = 0`, and what
`AxisBridge.axis_lookups_valid_perfect_of_memtrace` wants is `countsP t = 0`.  The trade is
ordinary root counting: they differ only on the roots of a nonzero `countsP`, of which there are at
most `deg(countsP)`.

This is the same move `Walk.card_roots_le` makes for the walk polynomials, and the same move the
paper makes exactly once, at the paper, for the NPR fingerprint. -/

section Univariate

variable [Fintype K] [DecidableEq K]

/-- The counted event of the unguarded lift: challenges at which the *evaluated* boundary holds
although the committed `axis_counts` column is not the zero polynomial. -/
def boundaryBadSeeds (t : MTree K) : Finset K :=
  Finset.univ.filter fun a => countsP t ≠ 0 ∧ (countsP t).eval a = 0

/-- **The lift.**  Off `boundaryBadSeeds`, the evaluated boundary *is* the polynomial identity. -/
theorem countsP_eq_zero_of_eval (t : MTree K) (a : K)
    (heval : (countsP t).eval a = 0) (ha : a ∉ boundaryBadSeeds t) :
    countsP t = 0 := by
  by_contra hne
  exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hne, heval⟩)

/-- **The price.**  The event has at most `deg(axis_counts)` members. -/
theorem boundaryBadSeeds_card_le (t : MTree K) :
    (boundaryBadSeeds t).card ≤ (countsP t).natDegree := by
  by_cases h : countsP t = 0
  · have hempty : boundaryBadSeeds t = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro a ha
      exact (Finset.mem_filter.mp ha).2.1 h
    simp [hempty]
  · refine le_trans (Finset.card_le_card ?_) (Nock.Walk.card_roots_le (countsP t) h)
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, (Finset.mem_filter.mp ha).2.2⟩

/-- The price against an external degree budget `B` — the shape
`TraceGen.natDegree_indP_countsP_le` and `TemplateAxisCounting.templateAxisWorkload` supply. -/
theorem boundaryBadSeeds_card_le_of_natDegree_le (t : MTree K) (B : ℕ)
    (hdeg : (countsP t).natDegree ≤ B) :
    (boundaryBadSeeds t).card ≤ B :=
  le_trans (boundaryBadSeeds_card_le t) hdeg

end Univariate

/-! ## §B.  The guarded, staged lift — the shape summand 4 uses

Two things separate §A from what the accounting can actually spend.

1. **The polynomial must be fixed before the challenge is sampled.**  A committed trace whose
   `axis_counts` column were allowed to depend on the challenge would make `boundaryBadSeeds` a
   moving target, and root counting would say nothing.  `TemplateAxisCounting` solves this by
   committing the α-free `templateAxisPolynomial` at the NPR seed and letting only the *tree* on
   which badness is read depend on `α`; `GenNounRecovery.recoveryOf_memTree_seed_independent` is
   the same discipline on the noun side.  `stagedGuardedSeeds` below is that split, generically:
   one fixed `P : K[X]`, one family `tOf : K → MTree K`.

2. **The conclusion needed downstream is not the polynomial identity.**  It is `vaxis e = Relaxis e`
   at the used exponents — `AxisSoundness.ExactMemoryAxisValidity`.  Guarding the event by the
   *existence of a bad record* rather than by `countsP ≠ 0` gives exactly that, with the same
   `deg` price, and is what makes the event coincide with summand 4. -/

section Staged

variable [Fintype K] [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
/-- A used exponent occurs in the `read_root` exponent list. -/
theorem mem_readExps_of_readCount_eq_one (e : ℕ) (t : MTree K)
    (h : readCount e t = 1) : e ∈ readExps t := by
  have hc := readCount_eq_count e t
  rw [h] at hc
  exact List.count_pos_iff.mp (by omega)

omit [Fintype K] [DecidableEq K] in
/-- A used exponent occurs in the `verify_child` exponent list. -/
theorem mem_verifyExps_of_verifyCount_eq_one (e : ℕ) (t : MTree K)
    (h : verifyCount e t = 1) : e ∈ verifyExps t := by
  have hc := verifyCount_eq_count e t
  rw [h] at hc
  exact List.count_pos_iff.mp (by omega)

/-- The staged guarded event: challenges at which some used record's committed axis is wrong while
the *pre-committed* polynomial `P` still evaluates to zero. -/
def stagedGuardedSeeds (P : K[X]) (tOf : K → MTree K) : Finset K :=
  Finset.univ.filter fun a => TemplateAxisBadWitness (tOf a) ∧ P ≠ 0 ∧ P.eval a = 0

/-- **The guarded lift.**  Off the guarded event the evaluated boundary already forces every used
record's committed axis to be the true topological one.  No `char ≠ 2`, no degree bound, and no
polynomial identity: the guard alone does it. -/
theorem axisValid_of_eval_of_notMem
    (P : K[X]) (tOf : K → MTree K) (a : K)
    (heval : P.eval a = 0) (hP : P ≠ 0) (ha : a ∉ stagedGuardedSeeds P tOf)
    (e : ℕ) (hn : Nested e (tOf a))
    (hr : readCount e (tOf a) = 1) (hv : verifyCount e (tOf a) = 1) :
    vaxis e (tOf a) = Relaxis e (tOf a) := by
  by_contra hbad
  exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ⟨e, hn, hr, hv, hbad⟩, hP, heval⟩)

/-- **The price of the guarded event**, given the zero-transfer from the committed polynomial to
the specialized tree (`TemplateAxisCounting.recovered_countsP_eq_zero_of_template_eq_zero` is
exactly this transfer for the production family). -/
theorem stagedGuardedSeeds_card_le (h2 : (2 : K) ≠ 0)
    (P : K[X]) (tOf : K → MTree K)
    (htransfer : P = 0 → ∀ a : K, countsP_bin (tOf a) = 0) :
    (stagedGuardedSeeds P tOf).card ≤ P.natDegree := by
  by_cases hempty : stagedGuardedSeeds P tOf = ∅
  · simp [hempty]
  · obtain ⟨a₀, ha₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hne : P ≠ 0 := (Finset.mem_filter.mp ha₀).2.2.1
    refine le_trans (Finset.card_le_card ?_) (Nock.Walk.card_roots_le P hne)
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, (Finset.mem_filter.mp ha).2.2.2⟩

/-- The guarded event is contained in the unguarded one. -/
theorem stagedGuardedSeeds_diagonal_subset (h2 : (2 : K) ≠ 0) (t : MTree K) :
    stagedGuardedSeeds (countsP t) (fun _ => t) ⊆ boundaryBadSeeds t := by
  intro a ha
  have h := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, h.2.2.1, h.2.2.2⟩

/-- The perfect boundary is the degenerate case of §B: it makes the guarded event empty. -/
theorem axisValid_of_countsP_eq_zero (h2 : (2 : K) ≠ 0) (t : MTree K)
    (hterm : countsP_bin t = 0) (e : ℕ) (hn : Nested e t)
    (hr : readCount e t = 1) (hv : verifyCount e t = 1) :
    vaxis e t = Relaxis e t :=
  axis_batching_sound h2 t hterm e hn hr hv

/-! ### The event **is** summand 4

`ProductionP8Containment.FailureUnion`'s fourth summand is `guardedAxisFailureEvent`, whose
`(alphaM, z)` fibre at a nonzero seed is
`ProductionAxisStructureVerifier.verifierGuardedRootUnion (committedTemplate T.verifier z hz)`, a
union of the per-root sets `verifierGuardedRootAlphas`.  Those sets are
`stagedGuardedSeeds` in disguise: same fixed polynomial, same specialized tree, and — the two
lemmas below — the same membership, at every `alphaM` where the verifier's own two structural
checks pass.  At an `alphaM` where a check fails, acceptance fails, so nothing is owed there.

Consequence: the counted event of §B is **already priced**.  Nothing is added to `FailureUnion`,
and `templateStagedSeeds_biUnion_card_le` spends exactly `templateAxisWorkload` — the summand
`ProductionP8Containment.fixedAxisWorkload` majorizes and `workload` already contains. -/

section Summand4

open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier

/-- (Same identity as inside
`TemplateAxisCounting.recovered_badWitness_of_specialized_bad`, exposed.) -/
theorem exactAxisTree_specialize
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) {lmb : K}
    (i : Fin T.kMem) :
    exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i
      = recoveredAxisTree α (templateMemoryTreeAt E i) := by
  simp only [exactAxisTree, ExactConfigTemplate.specialize_alpha]
  rw [specializeA_memoryTreeAt E α (lmb := lmb) i, ofNTree_specialize_toMTree]

/-- §B's event at one production memory root: the polynomial is the α-free
`templateAxisPolynomial`, fixed at the NPR seed; only the tree on which badness is read sees `α`. -/
def templateStagedSeeds {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (i : Fin T.kMem) : Finset K :=
  stagedGuardedSeeds (templateAxisPolynomial E i)
    (fun α => recoveredAxisTree α (templateMemoryTreeAt E i))

/-- Its price is the fixed polynomial's degree. -/
theorem templateStagedSeeds_card_le (h2 : (2 : K) ≠ 0)
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (i : Fin T.kMem) :
    (templateStagedSeeds E i).card ≤ (templateAxisPolynomial E i).natDegree := by
  refine stagedGuardedSeeds_card_le h2 _ _ ?_
  intro hzero a
  exact recovered_countsP_bin_eq_zero_of_template_eq_zero a _ hzero

/-- **The budget already allocated.**  The whole-forest event costs
`TemplateAxisCounting.templateAxisWorkload`, i.e. `∑ i, deg(templateAxisPolynomial E i)` — the
identical quantity `ProductionP8Containment.fixedAxisWorkload` majorizes and `workload` sums. -/
theorem templateStagedSeeds_biUnion_card_le (h2 : (2 : K) ≠ 0)
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) :
    ((Finset.univ : Finset (Fin T.kMem)).biUnion (templateStagedSeeds E)).card
      ≤ templateAxisWorkload E :=
  le_trans Finset.card_biUnion_le
    (Finset.sum_le_sum fun i _ => templateStagedSeeds_card_le h2 E i)

/-- **Summand 4 ⊆ §B's event.**  Every `alphaM` the production accounting already pays for is one
of ours. -/
theorem mem_templateStagedSeeds_of_mem_verifierGuarded
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (i : Fin T.kMem) (α : K)
    {lmb : K} (hα : α ∈ verifierGuardedRootAlphas E lmb i) :
    α ∈ templateStagedSeeds E i := by
  have h := Finset.mem_filter.mp hα
  obtain ⟨hchk, hwrap, hbad, hne, hroot⟩ := h.2
  have R := exactAxisStructuralRefinement_of_checks E α (lmb := lmb) hchk hwrap
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ α, recovered_badWitness_of_specialized_bad E α R i hbad, hne, hroot⟩

/-- **§B's event ⊆ summand 4, wherever the verifier's checks pass.**  Together with the previous
lemma the two sets coincide on the acceptance region, so §B needs no new failure class. -/
theorem mem_verifierGuarded_of_mem_templateStagedSeeds
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (i : Fin T.kMem) (α : K)
    (hchk : alphaFreeAxisStructureCheck E = true) (hwrap : noWrapCheck E α = true)
    {lmb : K} (hα : α ∈ templateStagedSeeds E i) :
    α ∈ verifierGuardedRootAlphas E lmb i := by
  have h := Finset.mem_filter.mp hα
  obtain ⟨e, -, hr0, hv0, hbad0⟩ := h.2.1
  have hr : readCount e (recoveredAxisTree α (templateMemoryTreeAt E i)) = 1 := hr0
  have hv : verifyCount e (recoveredAxisTree α (templateMemoryTreeAt E i)) = 1 := hv0
  have hbad : vaxis e (recoveredAxisTree α (templateMemoryTreeAt E i))
      ≠ Relaxis e (recoveredAxisTree α (templateMemoryTreeAt E i)) := hbad0
  rw [← exactAxisTree_specialize E α (lmb := lmb) i] at hr hv hbad
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ α, hchk, hwrap,
      ⟨e, mem_readExps_of_readCount_eq_one _ _ hr,
        mem_verifyExps_of_verifyCount_eq_one _ _ hv, hbad⟩, h.2.2.1, h.2.2.2⟩

end Summand4

end Staged

/-! ## §C.  Pointwise validity replaces the perfect boundary

`GenServedFromRecord.committed_axis_eq_address` calls `AxisBatching.axis_batching_sound` with
`hterm : countsP = 0` and then uses only its conclusion, at the single exponent the route names.
So the premise can be weakened to that conclusion.  Two things fall out:

* the `(2 : K) ≠ 0` hypothesis disappears — `char ≠ 2` was needed only inside
  `axis_batching_sound`, to divide by the `(2⁻¹)^{vdep}` scalar;
* the surviving premise is literally an instance of `AxisSoundness.ExactMemoryAxisValidity`, which
  is what production acceptance minus summand 4 supplies (§E). -/

section Validity

/-- The route's own multiplicity data, at the `read_root` that opens the region. -/
theorem AxisRoute.counts_at_read {e : ℕ} {recAxis : K} {b : ℕ} {c : MTree K}
    (h : AxisRoute e recAxis 1 b c) :
    readCount e (MTree.read e c : MTree K) = 1 ∧
      verifyCount e (MTree.read e c : MTree K) = 1 ∧
      Nested e (MTree.read e c : MTree K) := by
  obtain ⟨hr, hv, hn, -, -⟩ := h.spec
  exact ⟨by simp [readCount, hr], by simp [verifyCount, hv], by simpa [Nested] using hn⟩

/-! ### Localizing the global boundary to a nested `read_root`

`IK` §4's last paragraph warned that `GenServedFromRecord`'s route needs the served region's
`read_root` to be the **root** of the walk the count boundary is taken on, and that a `read_root`
nested inside a larger walk needs the count-localization extended above it.  With the boundary
replaced by pointwise validity that extension is short, because `vaxis` and `Relaxis` are *already*
localizing: at a `decompose` they descend into the branch that owns the timestamp, and at a
`read_root` for a different exponent they pass straight through.  `ReadRootNest` is that descent,
and `ReadRootNest.spec` transports validity from the authoritative root down to the region.

the paper is the licence for the sibling `readCount = verifyCount = 0` conditions: a record's
timestamp is added at exactly one `read_root` row and removed at exactly one `verify_child` row. -/

/-- Zero read- and verify-multiplicity below a node makes it well-nested for that timestamp.
(`GenServedFromRecord.nested_of_counts_zero` is `private`; this is the same statement.) -/
theorem nested_of_zero_counts (e : ℕ) :
    ∀ t : MTree K, readCount e t = 0 → verifyCount e t = 0 → Nested e t := by
  intro t
  induction t with
  | halt => simp [Nested]
  | decompose l r ihl ihr =>
      simp only [readCount, verifyCount]
      intro hr hv
      exact ⟨by omega, by omega, ihl (by omega) (by omega), ihr (by omega) (by omega)⟩
  | read e' c ih =>
      simp only [readCount, verifyCount, Nested]
      intro hr hv
      by_cases he : e' = e
      · rw [if_pos he] at hr
        exact ih (by omega) hv
      · rw [if_neg he] at hr
        exact ih (by omega) hv
  | verify e' x c ih =>
      simp only [readCount, verifyCount, Nested]
      intro hr hv
      by_cases he : e' = e
      · rw [if_pos he] at hv
        omega
      · rw [if_neg he] at hv
        exact ⟨fun h => absurd h he, ih hr (by omega)⟩

/-- `ReadRootNest e t sub` — the `read_root` that opens timestamp `e`'s region sits inside `t`, and
`sub` is that `read_root` node.  The sibling conditions are timestamp locality, the same data `AxisRoute` carries below the `read_root`. -/
inductive ReadRootNest (e : ℕ) : MTree K → MTree K → Prop
  | here {c : MTree K} : ReadRootNest e (MTree.read e c) (MTree.read e c)
  | left {l r sub : MTree K} (h : ReadRootNest e l sub)
      (hr : readCount e r = 0) (hv : verifyCount e r = 0) :
      ReadRootNest e (MTree.decompose l r) sub
  | right {l r sub : MTree K} (hr : readCount e l = 0) (hv : verifyCount e l = 0)
      (h : ReadRootNest e r sub) :
      ReadRootNest e (MTree.decompose l r) sub
  | read_other {e' : ℕ} {c sub : MTree K} (hne : e' ≠ e) (h : ReadRootNest e c sub) :
      ReadRootNest e (MTree.read e' c) sub
  | verify_other {e' : ℕ} {x : K} {c sub : MTree K} (hne : e' ≠ e) (h : ReadRootNest e c sub) :
      ReadRootNest e (MTree.verify e' x c) sub

/-- **The localization.**  If the region's own `read_root` node uses the timestamp exactly once on
each side, then so does the whole tree, the committed axis and the true topological axis are the
*same* at both scales, and well-nesting propagates upward.  So the global boundary check at the
authoritative root says exactly what the region needs. -/
theorem ReadRootNest.spec {e : ℕ} {t sub : MTree K} (h : ReadRootNest e t sub) :
    readCount e sub = 1 → verifyCount e sub = 1 →
    readCount e t = 1 ∧ verifyCount e t = 1 ∧
      vaxis e t = vaxis e sub ∧ Relaxis e t = Relaxis e sub ∧
      (Nested e sub → Nested e t) := by
  induction h with
  | here => exact fun hsr hsv => ⟨hsr, hsv, rfl, rfl, id⟩
  | @left l r sub hnest hr hv ih =>
      intro hsr hsv
      obtain ⟨hrl, hvl, hax, hrel, hn⟩ := ih hsr hsv
      refine ⟨by simp [readCount, hrl, hr], by simp [verifyCount, hvl, hv], ?_, ?_, ?_⟩
      · simp only [vaxis, if_pos hvl]; exact hax
      · simp only [Relaxis, if_pos hrl]; exact hrel
      · intro hns
        exact ⟨fun _ => hvl, by omega, hn hns, nested_of_zero_counts e r hr hv⟩
  | @right l r sub hr hv hnest ih =>
      intro hsr hsv
      obtain ⟨hrr, hvr, hax, hrel, hn⟩ := ih hsr hsv
      have hvne : ¬ verifyCount e l = 1 := by omega
      have hrne : ¬ readCount e l = 1 := by omega
      refine ⟨by simp [readCount, hrr, hr], by simp [verifyCount, hvr, hv], ?_, ?_, ?_⟩
      · simp only [vaxis, if_neg hvne]; exact hax
      · simp only [Relaxis, if_neg hrne]; exact hrel
      · intro hns
        exact ⟨by omega, fun _ => hvr, nested_of_zero_counts e l hr hv, hn hns⟩
  | read_other hne hnest ih =>
      intro hsr hsv
      obtain ⟨hrc, hvc, hax, hrel, hn⟩ := ih hsr hsv
      exact ⟨by simp [readCount, hne, hrc], by simp [verifyCount, hvc],
        by simpa [vaxis] using hax, by simpa [Relaxis, hne] using hrel,
        fun hns => by simpa [Nested] using hn hns⟩
  | verify_other hne hnest ih =>
      intro hsr hsv
      obtain ⟨hrc, hvc, hax, hrel, hn⟩ := ih hsr hsv
      exact ⟨by simp [readCount, hrc], by simp [verifyCount, hne, hvc],
        by simpa [vaxis, hne] using hax, by simpa [Relaxis] using hrel,
        fun hns => ⟨fun h => absurd h hne, hn hns⟩⟩

/-- **§C, on the idealized tree.**  `GenServedFromRecord.committed_axis_eq_address` with the
perfect boundary replaced by its own conclusion at the routed exponent.  No `char ≠ 2`. -/
theorem committed_axis_eq_address_of_valid {e : ℕ} {recAxis : K} {b : ℕ} {c : MTree K}
    (hvalid : vaxis e (MTree.read e c : MTree K) = Relaxis e (MTree.read e c : MTree K))
    (h : AxisRoute e recAxis 1 b c) :
    recAxis = ((b : ℕ) : K) := by
  obtain ⟨-, -, -, hax, -⟩ := h.spec
  rw [relaxis_eq_natCast h] at hvalid
  rw [← hvalid]
  simpa [vaxis] using hax.symm

/-- **§C, on the committed walk.**  `GenServedFromRecord.committed_axis_eq_address_of_walk` with
the same substitution. -/
theorem committed_axis_eq_address_of_walk_valid
    {E : NTree (MemoryTable.MState × MemoryTable.DTmem K) → ℕ} {e : ℕ} {recAxis : K} {b : ℕ}
    {d : MemoryTable.DTmem K} {c s : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hE : E (.node (.read_root, d) [c]) = e)
    (hvalid :
      vaxis e (MemWalk.toMTree (ofNTree E (.node (.read_root, d) [c])))
        = Relaxis e (MemWalk.toMTree (ofNTree E (.node (.read_root, d) [c]))))
    (hroute : WalkAxisRoute E e recAxis 1 b c s) :
    recAxis = ((b : ℕ) : K) := by
  have hshape :
      MemWalk.toMTree (ofNTree E (.node (.read_root, d) [c]))
        = (MTree.read e (MemWalk.toMTree (ofNTree E c)) : MTree K) := by
    rw [ofNTree_read, hE]
    rfl
  rw [hshape] at hvalid
  exact committed_axis_eq_address_of_valid hvalid hroute.toAxisRoute

end Validity

/-! ## §D.  `PricedRecordWitness` — the witness with the boundary taken out

Three changes from `GenServedFromRecord.CommittedRecordWitness`:

* `terminal` is **gone**.  The boundary is supplied once, for the whole forest, as
  `ExactMemoryAxisValidity cfg exec` — matching the paper, which checks `axis_counts` at the
  `halt` states of the traversal and concludes about every record at once.
* the free exponent oracle `E` is replaced by `AxisSoundness.timestampExpAt cfg.challenges.α`, the
  exponent map the exact route already uses (`exactAxisTree`).  So the witness no longer quantifies
  over an oracle that could be chosen to suit it.
* a new field `rootIndex`/`nest` says *which* authoritative memory root serves the record, and
  where inside it the region's `read_root` sits.  `CommittedRecordWitness` did not say — its
  `terminal` was a boundary on the region's own standalone walk, which is not an object the AIR
  checks.  `ReadRootNest.spec` localizes the checked root boundary down to any depth, so `IK` §4's
  closing caveat is discharged rather than assumed away. -/

section Priced

variable {cfg : ExactConfig F K} {exec : ExactExecution cfg}

/-- The easy case of `PricedRecordWitness.nest`: the served region's `read_root` **is** the
authoritative memory root.  `GenServedFromRecord`'s `CommittedRecordWitness` was implicitly in this
case (`IK` §4's last paragraph), and it is now one constructor rather than a silent assumption. -/
theorem readRootNest_of_rootShape {i : Fin cfg.kMem} {d : MemoryTable.DTmem K}
    {region : NTree (MemoryTable.MState × MemoryTable.DTmem K)} {e : ℕ}
    (hshape : exec.memoryTreeAt i = .node (.read_root, d) [region])
    (hE : timestampExpAt cfg.challenges.α (.node (.read_root, d) [region]) = e) :
    ReadRootNest e (exactAxisTree cfg exec i)
      (MTree.read e
        (MemWalk.toMTree (ofNTree (timestampExpAt cfg.challenges.α) region))) := by
  have hsh : exactAxisTree cfg exec i
      = (MTree.read e
          (MemWalk.toMTree (ofNTree (timestampExpAt cfg.challenges.α) region)) : MTree K) := by
    show (ofNTree (timestampExpAt cfg.challenges.α) (exec.memoryTreeAt i)).toMTree = _
    rw [hshape, ofNTree_read, hE]
    rfl
  rw [hsh]
  exact ReadRootNest.here

/-- **The memory-side commitment of one emitted record, with no boundary premise.**  Every field is
committed trace data, a `MemoryTable.Vmem` row, or a walk-topology descent. -/
structure PricedRecordWitness (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (q : ℕ) (r : ComputeTable.MemRec K) where
  /-- Which authoritative memory root serves the record. -/
  rootIndex : Fin cfg.kMem
  /-- The `read_root` row that opens the served region. -/
  rootData : MemoryTable.DTmem K
  /-- The subtree below it. -/
  region : NTree (MemoryTable.MState × MemoryTable.DTmem K)
  /-- The matching `verify_child` node. -/
  verifyNode : NTree (MemoryTable.MState × MemoryTable.DTmem K)
  /-- Its ordinary Nock axis in the region. -/
  addr : ℕ
  /-- The record's timestamp exponent on the memory side. -/
  memExponent : ℕ
  /-- The region's `read_root` sits inside that authoritative root — **anywhere** in it, with the
  ordinary timestamp locality on the branches it does not take.  `readRootNest_of_rootShape`
  supplies this when the `read_root` *is* the root. -/
  nest :
    ReadRootNest memExponent (exactAxisTree cfg exec rootIndex)
      (MTree.read memExponent
        (MemWalk.toMTree (ofNTree (timestampExpAt cfg.challenges.α) region)))
  fingerprints :
    MemoryFingerprintStructure cfg.challenges.z (.node (.read_root, rootData) [region])
  leaves : MemoryLeafAtomsRealized q (.node (.read_root, rootData) [region])
  vRoot : MemoryTable.Vmem rootData.1 rootData.2
  stRoot : rootData.2.st = MemoryTable.MState.read_root
  vNode : MemoryTable.Vmem verifyNode.label.2.1 verifyNode.label.2.2
  stNode : verifyNode.label.2.2.st = MemoryTable.MState.verify_child
  expRoot :
    timestampExpAt cfg.challenges.α (.node (.read_root, rootData) [region]) = memExponent
  route :
    WalkAxisRoute (timestampExpAt cfg.challenges.α) memExponent r.axis 1 addr region verifyNode
  recRoot : r.root = rootData.2.mem.root
  recChild : r.child = verifyNode.label.2.2.mem.child

namespace PricedRecordWitness

variable {q : ℕ} {r : ComputeTable.MemRec K}

/-- The served root noun the witness determines: seed-free, a function of the committed walk. -/
def servedRoot (W : PricedRecordWitness cfg exec q r) : Noun :=
  recoveredRootNoun q (.node (.read_root, W.rootData) [W.region])

/-- The served child noun the witness determines: seed-free, a function of the committed walk. -/
def servedChild (W : PricedRecordWitness cfg exec q r) : Noun :=
  GlobalCarryAxis.nounOf (recoveredLabelling q W.verifyNode W.addr)

/-- The routed exponent is used on both sides of the witness's memory root, so the *global* axis
validity of the forest applies to it. -/
theorem mem_exps (W : PricedRecordWitness cfg exec q r) :
    W.memExponent ∈ readExps (exactAxisTree cfg exec W.rootIndex) ∧
      W.memExponent ∈ verifyExps (exactAxisTree cfg exec W.rootIndex) := by
  obtain ⟨hr, hv, -⟩ := AxisRoute.counts_at_read W.route.toAxisRoute
  obtain ⟨hrt, hvt, -, -, -⟩ := W.nest.spec hr hv
  exact ⟨mem_readExps_of_readCount_eq_one _ _ hrt,
    mem_verifyExps_of_verifyCount_eq_one _ _ hvt⟩

/-- **The axis identification, priced.**  The committed `mem.axis` column of the record is the cast
of the node's ordinary Nock axis — from the *global* boundary at the authoritative root, localized
down to the region by `ReadRootNest.spec`, not from a per-record polynomial identity. -/
theorem committed_axis (W : PricedRecordWitness cfg exec q r)
    (hvalid : ExactMemoryAxisValidity cfg exec) :
    r.axis = ((W.addr : ℕ) : K) := by
  obtain ⟨hr, hv, -⟩ := AxisRoute.counts_at_read W.route.toAxisRoute
  obtain ⟨-, -, hax, hrel, -⟩ := W.nest.spec hr hv
  obtain ⟨hre, hve⟩ := W.mem_exps
  have h := hvalid W.rootIndex W.memExponent hre hve
  rw [hax, hrel] at h
  exact committed_axis_eq_address_of_valid h W.route.toAxisRoute

/-- **The witness realizes the record and serves it** — `GenServedFromRecord`'s §F with the perfect
boundary replaced by the global evaluated one.  `(2 : K) ≠ 0` is not needed. -/
theorem realizes_and_served (hz : cfg.challenges.z ≠ 0)
    (W : PricedRecordWitness cfg exec q r)
    (hvalid : ExactMemoryAxisValidity cfg exec) :
    OpcodeSemantics.RealizesMemRec cfg.challenges.z r W.servedRoot W.servedChild W.addr ∧
      Noun.slot W.addr W.servedRoot = some W.servedChild :=
  realizesMemRec_and_served_of_committed hz W.fingerprints W.leaves
    (NodeAddr.read W.route.toNodeAddr) W.vRoot W.stRoot W.vNode W.stNode
    W.recRoot W.recChild (W.committed_axis hvalid)

end PricedRecordWitness

end Priced

/-! ## §E.  `ServedSlotCovers`, and then the same thing from production acceptance

§E.1 is `GenServedFromRecord.servedSlotCovers_of_witnesses` with `terminal` deleted from every
witness and one `ExactMemoryAxisValidity` added.  §E.2 discharges that hypothesis from production
acceptance outside summand 4 of `FailureUnion` — so the *statement* of §E.2 mentions no boundary,
no polynomial, and no bad event at all. -/

section Supply

variable [Fintype K] [DecidableEq K]
variable {cfg : ExactConfig F K} {exec : ExactExecution cfg}

/-- **A `Service` from a priced witness.**  `hreq` (the record is one of the execution's raw
requests) and `hts` are the two
non-geometric premises; both are `GenServedFromRecord`'s and neither is new. -/
theorem exists_service_of_priced_witness {q : ℕ} {r : ComputeTable.MemRec K}
    (hz : cfg.challenges.z ≠ 0)
    (W : PricedRecordWitness cfg exec q r)
    (hvalid : ExactMemoryAxisValidity cfg exec)
    (hreq : r ∈ exec.rawRequests)
    {e : ℕ} (hts : r.ts = cfg.challenges.α ^ e) :
    ∃ svc : ServedMemoryTrace.Service cfg exec,
      svc.record = r ∧ svc.root = W.servedRoot ∧ svc.child = W.servedChild ∧
        svc.axis = W.addr := by
  obtain ⟨hreal, hserved⟩ := W.realizes_and_served hz hvalid
  exact ⟨{ exponent := e, record := r, root := W.servedRoot, child := W.servedChild,
           axis := W.addr, request_mem := hreq, timestamp := hts,
           realization := hreal, served := hserved },
         rfl, rfl, rfl, rfl⟩

/-- **§E.1 — `ServedSlotCovers` from priced witnesses.**  The perfect boundary is gone: what
replaces it is one `ExactMemoryAxisValidity cfg exec`, the paper's single global `axis_counts` zero
check read as a statement about every record at once. -/
theorem servedSlotCovers_of_priced_witnesses {q : ℕ} {S : Finset Noun}
    (hz : cfg.challenges.z ≠ 0)
    (hvalid : ExactMemoryAxisValidity cfg exec)
    (hs0 : ∀ row ∈ exec.computeRows, row.2.2.1.state = ComputeTable.State.s0 →
      ∃ (W : PricedRecordWitness cfg exec q (computeMemRec row.2.2.1 1)) (e : ℕ),
        (computeMemRec row.2.2.1 1).ts = cfg.challenges.α ^ e ∧
          W.servedRoot ∈ S ∧ W.servedChild ∈ S ∧ W.addr < q)
    (hs9 : ∀ row ∈ exec.computeRows, row.2.2.1.state = ComputeTable.State.s9 →
      ∃ (W : PricedRecordWitness cfg exec q (computeMemRec row.2.2.1 2)) (e : ℕ),
        (computeMemRec row.2.2.1 2).ts = cfg.challenges.α ^ e ∧
          W.servedRoot ∈ S ∧ W.servedChild ∈ S ∧ W.addr < q) :
    GenGlobalCollision.ServedSlotCovers exec q S := by
  refine ⟨?_, ?_⟩
  · intro row hrow hst
    obtain ⟨W, e, hts, hrS, hcS, haq⟩ := hs0 row hrow hst
    have hreq : computeMemRec row.2.2.1 1 ∈ exec.rawRequests :=
      GenGlobalCollision.mem_rawRequests_of_bound hrow _
        (mr2_mem_activeRequestRecords _ hst)
    obtain ⟨svc, hrec, hr, hc, ha⟩ := exists_service_of_priced_witness hz W hvalid hreq hts
    exact ⟨svc, hrec, by rw [hr]; exact hrS, by rw [hc]; exact hcS, by rw [ha]; exact haq⟩
  · intro row hrow hst
    obtain ⟨W, e, hts, hrS, hcS, haq⟩ := hs9 row hrow hst
    have hreq : computeMemRec row.2.2.1 2 ∈ exec.rawRequests :=
      GenGlobalCollision.mem_rawRequests_of_bound hrow _
        (mr3_mem_activeRequestRecords _ hst)
    obtain ⟨svc, hrec, hr, hc, ha⟩ := exists_service_of_priced_witness hz W hvalid hreq hts
    exact ⟨svc, hrec, by rw [hr]; exact hrS, by rw [hc]; exact hcS, by rw [ha]; exact haq⟩

end Supply

section Production

variable [Fintype K] [DecidableEq K] [charRing : CharP K (ringChar K)]

open Nock.NockVMROM.Thm54.ProductionP8Containment

/-- Summand 4 of `FailureUnion` is `guardedAxisFailureEvent`, so a coin outside the union is
outside the axis event.  This is the whole of the pricing: the budget already exists. -/
theorem notMem_guardedAxisFailureEvent_of_notMem_failureUnion
    {Λ : ℕ} (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (ω : JointCoins K) {lmb : K}
    (h : ω ∉ ProductionP8Containment.FailureUnion T C lmb) :
    ω ∉ guardedAxisFailureEvent T lmb := by
  intro hg
  exact h (Finset.mem_union_left _ (Finset.mem_union_right _ hg))

/-- **The evaluated boundary is a conjunct of acceptance.**  `RootAxisBoundaryAt` is the AIR's own
form of the paper: the per-root `axis_counts` column, as an element of `𝕂`, is zero. -/
theorem rootAxisBoundary_of_accepts
    (T : ProductionStrategy F K) (ω : JointCoins K) {lmb : K} (hz : nprSeed ω ≠ 0)
    (hacc : T.Accepts ω lmb) :
    T.RootAxisBoundaryAt (nprSeed ω) hz (alphaM ω) :=
  ((T.accepts_iff ω lmb hz).1 hacc).2

/-- **§E.2 — `ServedSlotCovers` at a production-accepted coin outside summand 4.**  No boundary
premise, no polynomial identity, no new failure event: the axis half of the served-slot supply is
paid for by `guardedAxisFailureEvent`, whose cardinality is already `fixedAxisWorkload T` inside
`workload`. -/
theorem servedSlotCovers_of_accepts
    (T : ProductionStrategy F K) (ω : JointCoins K) {lmb : K} (hz : nprSeed ω ≠ 0)
    (hacc : T.Accepts ω lmb)
    (hvalid : ExactMemoryAxisValidity
      (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb)
      (T.specializedExec (nprSeed ω) hz (alphaM ω) lmb))
    {q : ℕ} {S : Finset Noun}
    (hzc : (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb).challenges.z ≠ 0)
    (hs0 : ∀ row ∈ (T.specializedExec (nprSeed ω) hz (alphaM ω) lmb).computeRows,
      row.2.2.1.state = ComputeTable.State.s0 →
      ∃ (W : PricedRecordWitness (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb)
              (T.specializedExec (nprSeed ω) hz (alphaM ω) lmb) q (computeMemRec row.2.2.1 1)) (e : ℕ),
        (computeMemRec row.2.2.1 1).ts
            = (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb).challenges.α ^ e ∧
          W.servedRoot ∈ S ∧ W.servedChild ∈ S ∧ W.addr < q)
    (hs9 : ∀ row ∈ (T.specializedExec (nprSeed ω) hz (alphaM ω) lmb).computeRows,
      row.2.2.1.state = ComputeTable.State.s9 →
      ∃ (W : PricedRecordWitness (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb)
              (T.specializedExec (nprSeed ω) hz (alphaM ω) lmb) q (computeMemRec row.2.2.1 2)) (e : ℕ),
        (computeMemRec row.2.2.1 2).ts
            = (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb).challenges.α ^ e ∧
          W.servedRoot ∈ S ∧ W.servedChild ∈ S ∧ W.addr < q) :
    GenGlobalCollision.ServedSlotCovers
      (T.specializedExec (nprSeed ω) hz (alphaM ω) lmb) q S :=
  servedSlotCovers_of_priced_witnesses hzc hvalid hs0 hs9

end Production

/-! ## §F.  Axiom receipts -/

section Receipts

#print axioms Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced.countsP_eq_zero_of_eval
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced.boundaryBadSeeds_card_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced.axisValid_of_eval_of_notMem
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced.stagedGuardedSeeds_card_le
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced.templateStagedSeeds_biUnion_card_le
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced.mem_templateStagedSeeds_of_mem_verifierGuarded
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced.mem_verifierGuarded_of_mem_templateStagedSeeds
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced.committed_axis_eq_address_of_valid
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced.committed_axis_eq_address_of_walk_valid
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced.nested_of_zero_counts
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced.ReadRootNest.spec
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced.readRootNest_of_rootShape
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced.PricedRecordWitness.mem_exps
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced.PricedRecordWitness.committed_axis
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced.PricedRecordWitness.realizes_and_served
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced.servedSlotCovers_of_priced_witnesses
#print axioms
  Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced.notMem_guardedAxisFailureEvent_of_notMem_failureUnion
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced.servedSlotCovers_of_accepts

end Receipts

end

end Nock.NockVMROM.Thm54.TraceGen.GenAxisBoundaryPriced
