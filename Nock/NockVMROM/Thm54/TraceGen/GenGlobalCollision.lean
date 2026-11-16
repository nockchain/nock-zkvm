/-
  Nock/NockVMROM/Thm54/TraceGen/GenGlobalCollision.lean

  **A sixth counted event: global NPR injectivity, and the noun step it buys.**

  Every collision event in `ProductionP8Containment.FailureUnion` (`:539-546`) is a *census*
  event: a finite list of designated pre-seed noun **pairs**, each contributing `2Λ-1` bad seeds
  (`GlobalCarryRecognizer.sepSeed_bad_card_le`, itself `NPR.collision_card_le_tight`).  That shape
  can only separate pairs somebody wrote down in advance, and the identification this module needs
  is not of that shape: one side of it is a noun the *prover* chose (a
  `ServedMemoryTrace.Service`'s `root`/`child`), so no pre-seed census can list it.

  The paper's own instrument for that situation is `corr:ion_single_security`, leaned as `NPR.collision_table_card_le`: for a **table** of `k` nouns of
  at most `Λ` leaves, at most `k(k-1)(2Λ-1)` seeds admit any collision at all.  Off that event `fn`
  is injective on the table, which upgrades a fingerprint equality to a noun equality without
  either noun having been named in advance.  §A is that event; §B is the noun step; §C is the
  composition and the honest residuals.

  ## What §B closes

  `Def:NMR`'s value domain is `(root_fn, child_fn) ∈ 𝕂³ × 𝕂³` — "two NPR evaluations over `α`" — so the paper's memory record carries no nouns, and
  `GenOperationalCore.recordPair_not_in_skeletonComparisons` compiles the consequence that the
  record root/child pairs are not entries of `P8Census.skeletonComparisons`.  The service side is
  a further step out: its nouns are not skeleton projections at all.

  Given a `Service` whose emitted record **is** the row's own active memory record, §B identifies
  its `(root, child, axis)` with the skeleton record's, hence — with the record equations
  `GenOperationalCore.recordEquations_of_good_seed` already derives generically from acceptance —
  with `(s.subject, s.evaluation, skeletonMemoryAxis s 1)` at OP0 and the OP9 twin at `:1881`.
  Substituting into `Service.served` gives `ServedLookupBridge.SkeletonSlotSemantics`, which
  `skeletonSlotSemantics_iff_served` shows is *equivalent* to the two served fields of
  `BoundSemanticTrace.SkeletonOperationalCore`.  Nothing is weakened.

  ## Why the premise here is not the circular one

  `ServedLookupBridge.slotSemantics_of_served` needs a
  `ServedMemoryTrace.ExactServedMemoryTrace q Λ cfg exec D`, whose `semanticCoverage` quantifies
  over `(D.rows row).needs.served` — and `D.rows` is what `canonicalRowsOfBare` builds *from*
  `hop`.  `GenOperationalCore`'s header records that as circular in that position, and it is.

  `ServedSlotCovers` below is the same supply keyed on `exec.computeRows`' own OP0 `mr2` / OP9 `mr3`
  records instead of on `D`: it mentions no `ExactExecutionSemanticData`, no
  `ComputeRowSemanticData`, no `hop`, and no `canonicalRowsOfBare`.  It is a statement about the
  memory-side partition of the compute table's own request list.  That is the break.

  ## Scope, stated once

  **This is a `∀ E`-route module, not a generated-route one, and the generated route does not need
  it.**  The reason is visible in `Gen.lean:577`: `genSkelOp0` is only reachable through
  `match Nock.Noun.slot ax subject with | some result =>`, so the OP0 slot fact is the generator's
  own matched hypothesis and `genSkelOp0`'s `memoryRecord 1 = ⟨subject, result, axis⟩` makes the
  record equations `rfl`.  `hop` is therefore *not* an open premise for `nockCompiles`.

  What is open is `hop` at an **arbitrary** committed skeleton — `ProductionP8Containment`'s
  `hop : ∀ s ∈ computeSkeletonRows T.skeleton, SkeletonOperationalCore s`, and
  `GenOperationalCore.slotFailRow` shows a legal skeleton where it is false.  §C is that position.

  ## Residuals, plainly

  1. **`ServedSlotCovers` is a premise, not a discharge.**  It is honest service of the two served
     record slots.  §B is the *identification*: it says injectivity is all that separates that
     premise from `hop`'s served half.
  2. **The leaf bound on the prover's nouns is carried, not derived.**  `Service` has no leaf
     bound.  `ServiceWalk.read` carries `hroot : s.root = n` at a node of the walk over
     `RootTrace.subject`, and `VerifyRoute.here` carries `hchild : n = child`, so both service
     nouns are sub-nouns of that root subject — a bound on the committed memory root's leaves
     would discharge it.  That lemma is not proved here.
  3. **`C5`'s own `needs.served` does *not* supply the identification, and this is why.**
     `SemanticTrace.RowStateNeeds` (`:174`) has exactly two fields, `served` and `served_count`;
     nothing ties a `ServedNounLookup`'s `record` to the row's `computeMemRec pub 1`.  The only
     supplier of that tie is `BoundSemanticTrace.buildCoveredRow`'s second component
     (`:320`, `servedTuplesOf s pub` at `:298`) — and `buildCoveredRow` consumed `hop`.  So the
     record identification exists exactly where it is circular.  §B routes around it by taking the
     row's record as the *index* of the supply instead of recovering it from a lookup.

  ## Not claimed

  No `sorry`.  No new axiom.  No carrier field.  `Gen.lean` unedited.  `FailureUnion` itself is
  **not** edited here: §C defines the sixth event and states the composed count in this file.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenOperationalCore
import Nock.NockVMROM.Thm54.TraceGen.GenServiceSupply
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## §A.  The global collision event

`corr:ion_single_security` counts the seeds at which *some* pair of a table
of nouns collides.  `globalBadSeeds` is that event in the recognizer's own predicate `SepSeed`,
which is what `GlobalCarryRecognizer.noun_eq_of_enc_eq` consumes. -/

section Event

variable [Fintype K] [DecidableEq K]

/-- **The sixth counted event.**  Seeds at which two distinct members of the noun table `S` fail
to be separated.  Unlike the five census events this is indexed by a *set of nouns*, not by a list
of designated pairs, so it separates pairs nobody wrote down in advance. -/
def globalBadSeeds (S : Finset Noun) : Finset K :=
  Finset.univ.filter fun z : K =>
    ∃ ij ∈ S.offDiag, ¬ GlobalCarryRecognizer.SepSeed z ij.1 ij.2

/-- The event is *literally* `corr:ion_single_security`'s, at `f = id`: `¬ SepSeed` unfolds to
"the field-nouns differ and the fingerprints agree", which is the corollary's filter. -/
theorem globalBadSeeds_eq_collisionTable (S : Finset Noun) :
    globalBadSeeds (K := K) S =
      Finset.univ.filter (fun r : K => ∃ ij ∈ S.offDiag,
        NPR.fn (id ij.1) r = NPR.fn (id ij.2) r ∧
        (NPR.leafF (K := K) (id ij.1), NPR.dyckBits (K := K) (id ij.1))
          ≠ (NPR.leafF (K := K) (id ij.2), NPR.dyckBits (K := K) (id ij.2))) := by
  ext z
  simp only [globalBadSeeds, Finset.mem_filter, Finset.mem_univ, true_and, id]
  constructor
  · rintro ⟨ij, hij, hbad⟩
    refine ⟨ij, hij, ?_, ?_⟩
    · by_contra hne
      exact hbad fun _ => hne
    · by_contra hne
      exact hbad fun h => absurd hne h
  · rintro ⟨ij, hij, hcol, hdis⟩
    exact ⟨ij, hij, fun hsep => (hsep hdis) hcol⟩

/-- **The count, from the paper's corollary.**  `k(k-1)(2Λ-1)` at `k = S.card`.  The supplier is
`NPR.collision_table_card_le` = `«corr:ion_single_security»`; nothing is re-proved here.

Faithfulness note: the paper prints `k(k-1)/2` because it unions over *unordered* pairs,
while `Finset.offDiag` is ordered, so this bound is exactly `2×` the paper's.  That is a
conservative direction and is the shape the leaned corollary already has; halving it would need
a `Finset.Sym2`-indexed restatement of `collision_table_card_le`, which is not attempted here. -/
theorem globalBadSeeds_card_le (Λ : ℕ) (S : Finset Noun)
    (hS : ∀ n ∈ S, n.leaves ≤ Λ) :
    (globalBadSeeds (K := K) S).card ≤ S.card * (S.card - 1) * (2 * Λ - 1) := by
  rw [globalBadSeeds_eq_collisionTable]
  exact NPR.collision_table_card_le (K := K) Λ S id hS

/-- The event's probability form, for a union-bound consumer. -/
theorem globalBadSeeds_prob_le (Λ : ℕ) (S : Finset Noun)
    (hS : ∀ n ∈ S, n.leaves ≤ Λ) :
    ((globalBadSeeds (K := K) S).card : ℚ) / (Fintype.card K) ≤
      (S.card * (S.card - 1) * (2 * Λ - 1) : ℕ) / (Fintype.card K) := by
  have hcard := globalBadSeeds_card_le (K := K) Λ S hS
  have hpos : (0 : ℚ) ≤ (Fintype.card K : ℚ) := by positivity
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hpos
    |>.trans_eq rfl

/-- **Global NPR injectivity off the event.**  This is the whole point: no census entry, no
designated pair, no pre-seed list — just membership of both nouns in the table. -/
theorem eq_of_enc_eq_of_good {q : ℕ} {S : Finset Noun} {z : K}
    (hgood : z ∉ globalBadSeeds (K := K) S)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hb : ∀ n ∈ S, FieldEmbedding.BoundedBy q n)
    {a b : Noun} (ha : a ∈ S) (hbm : b ∈ S)
    (h : GlobalCarryRecognizer.enc z a = GlobalCarryRecognizer.enc z b) :
    a = b := by
  by_cases hab : a = b
  · exact hab
  · have hoff : (a, b) ∈ S.offDiag := Finset.mem_offDiag.mpr ⟨ha, hbm, hab⟩
    have hsep : GlobalCarryRecognizer.SepSeed z a b := by
      by_contra hns
      exact hgood (Finset.mem_filter.mpr ⟨Finset.mem_univ z, ⟨(a, b), hoff, hns⟩⟩)
    exact GlobalCarryRecognizer.noun_eq_of_enc_eq z a b hsep hcast (hb a ha) (hb b hbm) h

/-- Nat coordinates agree too, inside the cast window. -/
theorem nat_eq_of_cast_eq {q : ℕ} {a b : ℕ}
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (ha : a < q) (hb : b < q) (h : (a : K) = (b : K)) : a = b :=
  hcast (Set.mem_Iio.mpr ha) (Set.mem_Iio.mpr hb) h

end Event


/-! ## §B.  The noun step

`Def:NMR`'s memory record is `(root_fn, child_fn) ∈ 𝕂³ × 𝕂³`: field data,
no nouns.  `ServedMemoryTrace.Service` carries both halves of the bridge — `realization`
(`RealizesMemRec`, i.e. the three fingerprint equations) and `served` (`Noun.slot axis root = some
child`) — but at the *prover's* nouns.  `BindMemRec` carries the same three fingerprints at the
*skeleton's* nouns.  §A closes the gap between them. -/

section NounStep

variable [Fintype K] [DecidableEq K]

/-- **Service nouns are the skeleton record's nouns.**  The three fingerprint coordinates agree by
`RealizesMemRec` + `BindMemRec` on the same record; §A upgrades the two noun coordinates and
`hcast` the `ℕ` axis.

This is the step no census can take: `svc.root` is chosen by the prover after the seed, so it is
not a projection of any pre-seed skeleton and cannot be an entry of
`P8Census.skeletonComparisons` (`GenOperationalCore.recordPair_not_in_skeletonComparisons` records
the weaker fact for the skeleton record pairs themselves). -/
theorem service_eq_of_bindMemRec
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {q : ℕ} {S : Finset Noun}
    (hgood : cfg.challenges.z ∉ globalBadSeeds (K := K) S)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbS : ∀ n ∈ S, FieldEmbedding.BoundedBy q n)
    (svc : ServedMemoryTrace.Service cfg exec)
    {m : MemRecSkeleton}
    (hbind : BindMemRec cfg.challenges.z m svc.record)
    (hsr : svc.root ∈ S) (hsc : svc.child ∈ S)
    (hmr : m.root ∈ S) (hmc : m.child ∈ S)
    (hsa : svc.axis < q) (hma : m.axis < q) :
    svc.root = m.root ∧ svc.child = m.child ∧ svc.axis = m.axis := by
  refine ⟨?_, ?_, ?_⟩
  · exact eq_of_enc_eq_of_good hgood hcast hbS hsr hmr
      (svc.realization.root_realizes.symm.trans hbind.1)
  · exact eq_of_enc_eq_of_good hgood hcast hbS hsc hmc
      (svc.realization.child_realizes.symm.trans hbind.2.1)
  · exact nat_eq_of_cast_eq hcast hsa hma
      (svc.realization.axis_realizes.symm.trans hbind.2.2)

/-- The `ℕ`/noun data of one skeleton row's memory records lies in the counted table.  Both are
committed pre-seed projections, so this is a measurement of the skeleton, not a seed condition. -/
def SkeletonRecordNounsIn (q : ℕ) (S : Finset Noun) (s : ComputeRowSkeleton) : Prop :=
  ∀ (i : Fin 3) (h : (i : ℕ) < Nock.Framework.recordCount s.state),
    (s.memoryRecord i h).root ∈ S ∧ (s.memoryRecord i h).child ∈ S ∧
      (s.memoryRecord i h).axis < q

/-- **The `D`-free service supply.**

`ServedLookupBridge.slotSemantics_of_served` needs an `ExactServedMemoryTrace q Λ cfg exec D`,
whose `semanticCoverage` quantifies over `(D.rows row).needs.served` — and `D.rows` is what
`canonicalRowsOfBare` builds from `hop`.  That is circular in this position and
`GenOperationalCore`'s header says so.

This premise instead quantifies over `exec.rawRequests`, the compute table's own emission list
(`Language.lean:33`).  It mentions no `ExactExecutionSemanticData`, no `ComputeRowSemanticData`,
no `hop`, and no `canonicalRowsOfBare`.  The table-membership and axis-window conjuncts are the
data §A needs about the prover's nouns; the leaf bound backing `S` is `hS` at the counting site. -/
def ServiceCovers {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (q : ℕ) (S : Finset Noun) : Prop :=
  ∀ r ∈ exec.rawRequests,
    ∃ svc : ServedMemoryTrace.Service cfg exec,
      svc.record = r ∧ svc.root ∈ S ∧ svc.child ∈ S ∧ svc.axis < q

/-- **The tight premise.**  `ServiceCovers` asks for a service at *every* emitted record, which is
strictly more than the served half of `hop` gives back: the always-on formula-open `@3` records are emitted at every state and are not among the two slots
`BoundSemanticTrace.servedTuplesOf` reads.  `ServedSlotCovers` asks only at OP0's `mr2` and OP9's
`mr3` — exactly the two slots the served half is about — so nothing is silently strengthened. -/
def ServedSlotCovers {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (q : ℕ) (S : Finset Noun) : Prop :=
  (∀ row ∈ exec.computeRows, row.2.2.1.state = ComputeTable.State.s0 →
      ∃ svc : ServedMemoryTrace.Service cfg exec,
        svc.record = computeMemRec row.2.2.1 1 ∧
          svc.root ∈ S ∧ svc.child ∈ S ∧ svc.axis < q) ∧
  (∀ row ∈ exec.computeRows, row.2.2.1.state = ComputeTable.State.s9 →
      ∃ svc : ServedMemoryTrace.Service cfg exec,
        svc.record = computeMemRec row.2.2.1 2 ∧
          svc.root ∈ S ∧ svc.child ∈ S ∧ svc.axis < q)

/-- Any active request record of a *bound* compute row is one of the execution's raw requests. -/
theorem mem_rawRequests_of_bound
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hrow : row ∈ exec.computeRows)
    (r : ComputeTable.MemRec K)
    (hr : r ∈ Nock.NockVM.activeRequestRecords row.2.2.1) :
    r ∈ exec.rawRequests := by
  have : (fun row : ComputeTable.State × ComputeTable.DTcomp K =>
      Nock.NockVM.activeRequestRecords row.2.2.1) row = _ := rfl
  exact List.mem_flatMap.mpr ⟨row, hrow, hr⟩

/-- The strong supply implies the tight one. -/
theorem ServiceCovers.toServedSlot
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {q : ℕ} {S : Finset Noun}
    (h : ServiceCovers exec q S) : ServedSlotCovers exec q S := by
  refine ⟨?_, ?_⟩
  · intro row hrow hst
    exact h _ (mem_rawRequests_of_bound hrow _ (mr2_mem_activeRequestRecords _ hst))
  · intro row hrow hst
    exact h _ (mem_rawRequests_of_bound hrow _ (mr3_mem_activeRequestRecords _ hst))

/-- **OP0's Nock slot fact, from the service supply.**  the paper is the `OP_0`
semantics `*[a 0 b] = /[b a]`; the paper is the compute gate that pins the emitted record to
`(input_subject, evaluation)`, and the record equations `hrec` are its noun form (already derived
generically by `GenOperationalCore.recordEquations_of_good_seed`). -/
theorem s0_slot_of_serviceCovers
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {q : ℕ} {S : Finset Noun} {z : K}
    {s : ComputeRowSkeleton} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hz : z = cfg.challenges.z)
    (hgood : cfg.challenges.z ∉ globalBadSeeds (K := K) S)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbS : ∀ n ∈ S, FieldEmbedding.BoundedBy q n)
    (hcov : ServedSlotCovers exec q S)
    (hin : SkeletonRecordNounsIn q S s)
    (hrec : ServedLookupBridge.SkeletonRecordEquations s)
    (hbind : BindComputeRow z s row)
    (hrow : row ∈ exec.computeRows)
    (hst : s.state = .s0) :
    Noun.slot (P8Census.skeletonMemoryAxis s 1) s.subject = some s.evaluation := by
  have h1 : ((1 : Fin 3) : ℕ) < Nock.Framework.recordCount s.state := by
    simp [hst, Nock.Framework.recordCount]
  have hstRow : row.2.2.1.state = ComputeTable.State.s0 := by
    rw [hbind.2.2.1, hst]
  obtain ⟨svc, hsrec, hsr, hsc, hsa⟩ := hcov.1 row hrow hstRow
  have hbm : BindMemRec cfg.challenges.z (s.memoryRecord 1 h1) svc.record := by
    rw [hsrec, ← hz]
    exact RawSemanticAssembly.bindComputeRow_memRec hbind 1 h1
  obtain ⟨hmr, hmc, hma⟩ := hin 1 h1
  obtain ⟨hr, hc, ha⟩ :=
    service_eq_of_bindMemRec hgood hcast hbS svc hbm hsr hsc hmr hmc hsa hma
  obtain ⟨hroot, hchild⟩ := hrec.s0_record hst
  have haxis : P8Census.skeletonMemoryAxis s 1 = (s.memoryRecord 1 h1).axis :=
    StrictOperationalEvidence.skeletonMemoryAxis_eq s 1 h1
  rw [haxis, ← hroot, ← hchild, ← hr, ← hc, ← ha]
  exact svc.served

/-- **OP9's Nock slot fact, from the same supply.**  the paper is the OP9 record gate
(`mem_root_3 = sf1_e`, `mem_child_3 = sf2_f`); the paper is the axis clause. -/
theorem s9_slot_of_serviceCovers
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {q : ℕ} {S : Finset Noun} {z : K}
    {s : ComputeRowSkeleton} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hz : z = cfg.challenges.z)
    (hgood : cfg.challenges.z ∉ globalBadSeeds (K := K) S)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbS : ∀ n ∈ S, FieldEmbedding.BoundedBy q n)
    (hcov : ServedSlotCovers exec q S)
    (hin : SkeletonRecordNounsIn q S s)
    (hrec : ServedLookupBridge.SkeletonRecordEquations s)
    (hbind : BindComputeRow z s row)
    (hrow : row ∈ exec.computeRows)
    (hst : s.state = .s9) :
    Noun.slot (P8Census.skeletonMemoryAxis s 2)
        (P8Census.skeletonSubformula s 0 .result) =
      some (P8Census.skeletonSubformula s 1 .formula) := by
  have h2 : ((2 : Fin 3) : ℕ) < Nock.Framework.recordCount s.state := by
    simp [hst, Nock.Framework.recordCount]
  have hstRow : row.2.2.1.state = ComputeTable.State.s9 := by
    rw [hbind.2.2.1, hst]
  obtain ⟨svc, hsrec, hsr, hsc, hsa⟩ := hcov.2 row hrow hstRow
  have hbm : BindMemRec cfg.challenges.z (s.memoryRecord 2 h2) svc.record := by
    rw [hsrec, ← hz]
    exact RawSemanticAssembly.bindComputeRow_memRec hbind 2 h2
  obtain ⟨hmr, hmc, hma⟩ := hin 2 h2
  obtain ⟨hr, hc, ha⟩ :=
    service_eq_of_bindMemRec hgood hcast hbS svc hbm hsr hsc hmr hmc hsa hma
  obtain ⟨hroot, hchild⟩ := hrec.s9_record hst
  have haxis : P8Census.skeletonMemoryAxis s 2 = (s.memoryRecord 2 h2).axis :=
    StrictOperationalEvidence.skeletonMemoryAxis_eq s 2 h2
  rw [haxis, ← hroot, ← hchild, ← hr, ← hc, ← ha]
  exact svc.served

/-- **The served half of `hop`, at one bound row.**  `SkeletonSlotSemantics` is *equivalent* to the
two served fields (`ServedLookupBridge.skeletonSlotSemantics_iff_served`), so this is the served
obligation itself and not a weakening. -/
theorem skeletonSlotSemantics_of_serviceCovers
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {q : ℕ} {S : Finset Noun} {z : K}
    {s : ComputeRowSkeleton} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hz : z = cfg.challenges.z)
    (hgood : cfg.challenges.z ∉ globalBadSeeds (K := K) S)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbS : ∀ n ∈ S, FieldEmbedding.BoundedBy q n)
    (hcov : ServedSlotCovers exec q S)
    (hin : SkeletonRecordNounsIn q S s)
    (hrec : ServedLookupBridge.SkeletonRecordEquations s)
    (hbind : BindComputeRow z s row)
    (hrow : row ∈ exec.computeRows) :
    ServedLookupBridge.SkeletonSlotSemantics s where
  s0_slot hst :=
    s0_slot_of_serviceCovers hz hgood hcast hbS hcov hin hrec hbind hrow hst
  s9_slot hst :=
    s9_slot_of_serviceCovers hz hgood hcast hbS hcov hin hrec hbind hrow hst

/-- **`SkeletonOperationalCore` at one bound row** — both halves, the record half from `hrec` and
the served half from §B.  This is `hop`'s per-row content. -/
theorem skeletonOperationalCore_of_serviceCovers
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {q : ℕ} {S : Finset Noun} {z : K}
    {s : ComputeRowSkeleton} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hz : z = cfg.challenges.z)
    (hgood : cfg.challenges.z ∉ globalBadSeeds (K := K) S)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbS : ∀ n ∈ S, FieldEmbedding.BoundedBy q n)
    (hcov : ServedSlotCovers exec q S)
    (hin : SkeletonRecordNounsIn q S s)
    (hrec : ServedLookupBridge.SkeletonRecordEquations s)
    (hbind : BindComputeRow z s row)
    (hrow : row ∈ exec.computeRows) :
    BoundSemanticTrace.SkeletonOperationalCore s :=
  ServedLookupBridge.skeletonOperationalCore_of_parts hrec
    (skeletonSlotSemantics_of_serviceCovers hz hgood hcast hbS hcov hin hrec hbind hrow)

end NounStep

/-! ## §C.  Whole-skeleton form: `hop`, with no operational premise left

`GenOperationalCore.operationalCore_of_accepted_and_slots` reduced `hop` to `hslot`
(`SkeletonSlotSemantics` at every committed row) plus a counted seed condition.  §B discharges
`hslot`, so the composite below has **no** operational premise: only acceptance, the two committed
bindings, the fifth (record) census event, and the sixth (global) event. -/

section Whole

variable [Fintype K] [DecidableEq K]

private theorem exists_paired {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      ∀ a ∈ l₁, ∃ b ∈ l₂, R a b := by
  intro l₁ l₂ h
  induction h with
  | nil => intro a ha; simp at ha
  | @cons x y xs ys hxy _ ih =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact ⟨y, by simp, hxy⟩
      · obtain ⟨b, hb, hR⟩ := ih a ha'
        exact ⟨b, by simp [hb], hR⟩

/-- **The served half at every committed row of an arbitrary skeleton.** -/
theorem slotSemantics_of_serviceCovers
    {q : ℕ} {z : K} {S : SemanticSkeleton} {N : Finset Noun}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hz : z = cfg.challenges.z)
    (hgood : cfg.challenges.z ∉ globalBadSeeds (K := K) N)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbN : ∀ n ∈ N, FieldEmbedding.BoundedBy q n)
    (hcov : ServedSlotCovers exec q N)
    (hin : ∀ s ∈ computeSkeletonRows S, SkeletonRecordNounsIn q N s)
    (hrec : ∀ s ∈ computeSkeletonRows S, ServedLookupBridge.SkeletonRecordEquations s)
    (binds : BindsAt z S cfg exec) :
    ∀ s ∈ computeSkeletonRows S, ServedLookupBridge.SkeletonSlotSemantics s := by
  intro s hs
  obtain ⟨row, hrow, hbind⟩ := exists_paired binds.derived_computeRows s hs
  exact skeletonSlotSemantics_of_serviceCovers hz hgood hcast hbN hcov
    (hin s hs) (hrec s hs) hbind hrow

/-- **`hop` from acceptance and two counted events, with no operational premise.**

Compare `GenOperationalCore.operationalCore_of_accepted_and_slots`, which still carried `hslot`.
Here the record half comes from the fifth event (`SkeletonRecordCensus`) and the served half from
the sixth (`globalBadSeeds`); the only non-counted premises are acceptance, the binding, the two
committed-table measurements, and `ServiceCovers`. -/
theorem operationalCore_of_accepted_and_serviceCovers
    {q Λ : ℕ} {z : K} {S : SemanticSkeleton} {N : Finset Noun}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hz : z = cfg.challenges.z)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbound : S.BoundedBy q)
    (C : GenOperationalCore.SkeletonRecordCensus S Λ)
    (hgoodC : z ∉ (C.census).badSeeds (K := K))
    (hgoodN : cfg.challenges.z ∉ globalBadSeeds (K := K) N)
    (hbN : ∀ n ∈ N, FieldEmbedding.BoundedBy q n)
    (hcov : ServedSlotCovers exec q N)
    (hin : ∀ s ∈ computeSkeletonRows S, SkeletonRecordNounsIn q N s)
    (binds : BindsAt z S cfg exec)
    (hrows : exec.ComputeRowsAccepted) :
    ∀ s ∈ computeSkeletonRows S, BoundSemanticTrace.SkeletonOperationalCore s := by
  have hrec := GenOperationalCore.recordEquations_of_good_seed
    hcast hbound C hgoodC binds hrows
  exact GenOperationalCore.operationalCore_of_accepted_and_slots
    hcast hbound C hgoodC binds hrows
    (slotSemantics_of_serviceCovers hz hgoodN hcast hbN hcov hin hrec binds)

/-! ### The sixth event's contribution to the union bound

`ProductionP8Containment.FailureUnion` (`:539-546`) is a union of five events and
`ProductionP8Containment.workload` is the matching numerator.  The one-line change is to union in
`globalBadSeeds N` (lifted to `JointCoins K` through the seed coordinate, exactly as
`collisionFailureEvent` lifts the census event) and to add `N.card * (N.card - 1) * (2 * Λ - 1)` to
`workload`.  The count that justifies it is `globalBadSeeds_card_le`; the statement below is the
arithmetic of the composed numerator, stated here because `ProductionP8Containment.lean` is not
edited by this module. -/

/-- **The composed numerator.**  Five-class workload `W` plus the sixth event's `k(k-1)(2Λ-1)`. -/
def composedWorkload (W : ℕ) (N : Finset Noun) (Λ : ℕ) : ℕ :=
  W + N.card * (N.card - 1) * (2 * Λ - 1)

/-- The sixth event is bounded by the term `composedWorkload` adds — nothing else changes. -/
theorem globalBadSeeds_card_le_composed (W Λ : ℕ) (N : Finset Noun)
    (hN : ∀ n ∈ N, n.leaves ≤ Λ) :
    W + (globalBadSeeds (K := K) N).card ≤ composedWorkload W N Λ :=
  Nat.add_le_add_left (globalBadSeeds_card_le Λ N hN) W

/-- **`Batch258`'s numerator, recomputed.**  `W = 16914` (`Batch258.b258_workload_le`),
`Λ = 22`, and a noun table of `78` entries — `2` nouns for each of at most `22` emitted records
(`L = 22`) plus `2` for each of the `17` compute rows' served record slots — gives
`16914 + 78 * 77 * 43 = 275172`.  Fourteen bits do **not** survive at `p = 769`:
`275172 * 2^14 > 769^3`.  Ten do. -/
theorem composed_numerator_at_batch258 :
    composedWorkload 16914 (N := (∅ : Finset Noun)) 22 = 16914 ∧
      16914 + 78 * 77 * 43 = 275172 ∧
      ¬ (275172 * 2 ^ 14 ≤ 769 ^ 3) ∧
      275172 * 2 ^ 10 ≤ 769 ^ 3 ∧
      ¬ (275172 * 2 ^ 11 ≤ 769 ^ 3) := by
  refine ⟨by simp [composedWorkload], by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The tighter table.  `ServedSlotCovers` needs only ONE service per OP0/OP9 row, so `2` service
nouns and `2` skeleton record nouns per such row bound the table by `4 * 17 = 68` rather than `78`.

The **proved** bound is
`TraceGen.card_traceNounTable_le : card ≤ 6 * (computeSkeletonRows S).length + 2 * rows.length`
(`TraceGen/GenServiceBookkeeping.lean`).  The `68`/`212822`/eleven-bit arithmetic below is a
statement about a *stated* `k`, which remains valid as such.
`16914 + 68 * 67 * 43 = 212822`, and **eleven** bits survive, not fourteen.

`k` is not *measured* at `bpPackage` — no `ServedSlotCovers` inhabitant exists there — so these are
arithmetic facts about a stated `k`, not a soundness number for that package. -/
theorem composed_numerator_at_batch258_tight :
    16914 + 68 * 67 * 43 = 212822 ∧
      212822 * 2 ^ 11 ≤ 769 ^ 3 ∧
      ¬ (212822 * 2 ^ 12 ≤ 769 ^ 3) ∧
      ¬ (212822 * 2 ^ 14 ≤ 769 ^ 3) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The *bipartite* refinement, for the record.  Only (service noun, skeleton noun) pairs need
separating, so `n_svc * n_skel * (2Λ-1) = 44 * 34 * 43 = 64328` suffices in place of
`k(k-1)(2Λ-1)`; that is `81242` and twelve bits.  This is **not** what
`NPR.collision_table_card_le` proves, so it is recorded as arithmetic only. -/
theorem bipartite_numerator_at_batch258 :
    16914 + 44 * 34 * 43 = 81242 ∧
      81242 * 2 ^ 12 ≤ 769 ^ 3 ∧
      ¬ (81242 * 2 ^ 13 ≤ 769 ^ 3) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

end Whole

end

end Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision

#print axioms Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision.globalBadSeeds_eq_collisionTable
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision.globalBadSeeds_card_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision.eq_of_enc_eq_of_good

#print axioms Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision.service_eq_of_bindMemRec
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision.s0_slot_of_serviceCovers
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision.s9_slot_of_serviceCovers
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision.skeletonSlotSemantics_of_serviceCovers
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision.skeletonOperationalCore_of_serviceCovers
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision.slotSemantics_of_serviceCovers
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision.operationalCore_of_accepted_and_serviceCovers
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision.composed_numerator_at_batch258
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision.bipartite_numerator_at_batch258
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision.ServiceCovers.toServedSlot
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision.composed_numerator_at_batch258_tight
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision.globalBadSeeds_prob_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision.globalBadSeeds_card_le_composed
