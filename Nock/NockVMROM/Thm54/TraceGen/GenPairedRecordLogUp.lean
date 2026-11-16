/-
  Nock/NockVMROM/Thm54/TraceGen/GenPairedRecordLogUp.lean

  **`PairedRecordLayout` from the memory RAP's own `intermediate` block, with the bad challenge
  set exhibited BEFORE the challenge is quantified.**

  The four-step derivation it names — telescope the accumulator, lift
  the evaluated log-derivative identity to `RatFunc K` off a counted event, read the permutation
  off `Lem:ldse_mse`, then consume it with `timestampClosed_of_paired_record_layout` — is
  **already in the tree**, at `PairedRecordCountedEvent.pairedRecordLayout_of_counted_events`
.  Nothing here reproves it.

  What that module also records, in its own §D and in two header disclosures, is *why* it is a
  relocation and not a closure:

  * `interLogDerivGood_iff_pairedRecordLayout` — off counted events (1) and (2), and on `E`'s own
    accumulator, exclusion of counted event (3) is **equivalent** to the conclusion.  As a
    hypothesis *on `E`* it therefore renames the premise.
  * "`E` has no chronology": `E.cfg.challenges` (carrying `β`, `γ`) and `E.exec` (carrying the two
    record columns) are fields of one structure with no ordering between them, so "the bad set is
    small" does not, on `E` alone, yield "the sampled `(β, γ)` lies outside it".

  Both observations are about **quantifier order**, not about the algebra.  This module supplies
  the missing order.  The bad set is built from a *record commitment* and `γ` only — data that
  contains no `β` and no execution — and `β` and the execution are then quantified **after** it:

  (`counted_soundness_of_record_commitment`, and `counted_soundness_of_exact_execution` at the
  `ExactExecution` carrier).  Read contrapositively this is the LogUp soundness statement: an
  **unpaired** record commitment admits a closed `intermediate` chain for at most
  `#consumed + #added` values of the pole challenge.  In the paired case the bad set is *empty*
  (`badPoleSet_eq_empty_of_perm`), so the hypothesis costs nothing where the conclusion holds —
  which is the §D equivalence, now harmless, because the equivalence is between two properties of
  the *commitment* and the quantifier over `β` ranges outside it.

  ## What the AIR input is

  The single AIR hypothesis is `RAPInterChain inp 0 0 pubs`: the memory RAP's `intermediate` block
  `MemoryTable.interR` — the inverse-witness column form of the paper (`read_root`, add) and
  the paper (`verify_child`, remove) — chained across the walk-ordered rows by the hand-off
  `icur(i) = ipre(i+1)`, with the initial and terminal `intermediate = 0` boundaries of
  the paper.  Everything else is derived:

  * the pole non-vanishing is **not assumed** — the
    inverse-witness gate `pole · g = 1` forces it (`pole_ne_zero_of_interR`);
  * the telescope is `MemoryTable.interChain_balance`, already in the tree;
  * the lift and the read-off are the existing `FiniteIO` / `SetEq` machinery.

  * `consumed.length < ringChar K`, `added.length < ringChar K` — row-count/no-wraparound windows.
    They are exactly the paper's own `char p > n` in `Lem:ldse_mse`, and they
    enter through `SetEq.natCast_inj_of_lt`, i.e. they are the condition that record
    *multiplicities* cast injectively into `K`.  §1-legitimate.
  * `γ ∉ FiniteIO.IORLCCollisionEvent …` — the record-RLC injectivity event, `card ≤ n²·7`
    (`IORLCCollisionEvent_card_le` at `m = 8`).  A challenge-side condition on pre-challenge data;
    §1-legitimate, and it is the same event the external IO columns assume as a named `Inputs`
    field (`external_counted_events_are_named_inputs`).
  * `β ∉ badPoleSet cp …`, `card ≤ #consumed + #added` — the counted pole event.  This is the ONE
    probabilistic step, and its whole content is the cardinality bound.
  * `[Fintype K] [DecidableEq K]` — required to speak of the events as `Finset K` at all.  Not a
    restriction on the algebra; the AIR side (`RAPInterChain`, the telescope) is `[Field K]`-only.

  **Disclosure — the commitment is quantified, not adaptive.**  Each headline fixes ONE record
  commitment and bounds the bad `β` for that commitment.  It does not union-bound over every
  commitment a prover might choose after seeing `β`, and no such union is claimed or available.
  This is the commit-then-challenge order the protocol itself has — the paper implements the
  `intermediate` column "in the exact same way as in `RAP_mem-IO`, `RAP_comp-IO`", i.e. as a
  post-challenge witness column over pre-challenge committed records — but it is an ordering
  assumption about the *protocol*, supplied here by the quantifier structure and not by any object
  in the tree.  `PairedRecordCountedEvent`'s "`E` has no chronology" disclosure is the statement
  that `BuildableNockExecution` cannot express it; these theorems express it outside `E`.

  **Disclosure — TWO events, not one.**  Lifting the evaluated identity to `RatFunc K` needs the
  log-derivative event (`badPoleSet`, in `β`); recovering *records* from *compressed values* needs
  the RLC-collision event (in `γ`, `card ≤ n²·7` at record width `m = 8`).  Neither substitutes
  for the other.

  **Not claimed.**  No zero-error inhabitation of `PairedRecordLayout`; §D's equivalence rules that
  out and is not disputed here.  No `Nodup` on either column, no field-size bound, no carrier field,
  no section-J tick.  The `Finset` cardinalities are subset counts, not a probability measure —
  the same disclosure `PairedRecordCountedEvent` §F carries.
-/
import Nock.NockVMROM.Thm54.PairedRecordCountedEvent

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLogUp

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.PairedRecordCountedEvent

noncomputable section

/-! ## §A. The RAP `intermediate` block, chained — the only AIR input

This section is `[Field K]`-only: no `Fintype`, no characteristic, no event. -/

section AIR

variable {K : Type} [Field K]

/- Every statement is taken at
a `C'`-coherence function `cp` (`ExactExecution.cprimeOf` on a `CprimeCoherent` execution): the
row's `C'` is `cp` of its stored record, and the pole of a record column reads `cp`. -/
variable (cp : ComputeTable.MemRec K → K)

/-- **The inverse-witness gate forces the pole to be non-vanishing.**  On a `read_root` or
`verify_child` row the RAP `intermediate` block carries `pole · g = 1`, so the paper's
genericity condition (`MemoryTable.WF.pole_ne`) is a *consequence* of the AIR and not a hypothesis
of this module. -/
theorem pole_ne_zero_of_interR (inp : MemoryTable.Inputs K) {p : MemoryTable.Pub K} {g : K}
    (h : MemoryTable.interR inp p g)
    (hst : p.st = MemoryTable.MState.read_root ∨ p.st = MemoryTable.MState.verify_child) :
    MemoryTable.pole inp p.mem p.cprime ≠ 0 := by
  have h1 : MemoryTable.pole inp p.mem p.cprime * g = 1 := by
    rcases hst with hs | hs
    · simp only [MemoryTable.interR, hs] at h; exact h.1
    · simp only [MemoryTable.interR, hs] at h; exact h.1
  intro h0
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

/-- The RAP `intermediate` block implies the algorithm's honest `pole⁻¹` step, unconditionally:
the genericity `MemoryTable.inter_iff` needs is supplied by the witness column itself. -/
theorem interV_of_interR (inp : MemoryTable.Inputs K) {p : MemoryTable.Pub K} {g : K}
    (h : MemoryTable.interR inp p g) : MemoryTable.interV inp p :=
  (MemoryTable.inter_iff inp p ⟨fun hst => pole_ne_zero_of_interR inp h hst⟩).mp ⟨g, h⟩

/-- **`RAPInterChain` — the memory RAP's `intermediate` column, chained.**  Each row satisfies the
RAP block `MemoryTable.interR` for *some* inverse-witness value `g` (the auxiliary LogUp column);
the head's `ipre` is the running seed; `icur(i) = ipre(i+1)` is the cross-row hand-off that makes
the accumulator "global to the traversal"; and `term` is its value after the last
row.  Used at `seed = term = 0`, the two boundaries the memory RAP checks.

This is `MemoryTable.InterChain` with the *verifier* step replaced by the *RAP* step, so the pole
non-vanishing comes for free. -/
def RAPInterChain (inp : MemoryTable.Inputs K) : K → K → List (MemoryTable.Pub K) → Prop
  | seed, term, [] => seed = term
  | seed, term, p :: rest =>
      p.ipre = seed ∧ (∃ g, MemoryTable.interR inp p g)
        ∧ RAPInterChain inp p.icur term rest

/-- The RAP chain is a verifier chain, so `MemoryTable.interChain_telescope` and
`interChain_balance` apply to it. -/
theorem interChain_of_rapInterChain (inp : MemoryTable.Inputs K) :
    ∀ (pubs : List (MemoryTable.Pub K)) (seed term : K),
      RAPInterChain inp seed term pubs → MemoryTable.InterChain inp seed term pubs := by
  intro pubs
  induction pubs with
  | nil => intro seed term h; exact h
  | cons p rest ih =>
      intro seed term h
      obtain ⟨hseed, ⟨g, hg⟩, hrest⟩ := h
      exact ⟨hseed, interV_of_interR inp hg, ih p.icur term hrest⟩

/-- Every live row of a RAP chain has a non-vanishing pole. -/
theorem pole_ne_zero_of_rapInterChain (inp : MemoryTable.Inputs K) :
    ∀ (pubs : List (MemoryTable.Pub K)) (seed term : K),
      RAPInterChain inp seed term pubs →
        ∀ p ∈ pubs, (p.st = MemoryTable.MState.read_root
            ∨ p.st = MemoryTable.MState.verify_child) →
          MemoryTable.pole inp p.mem p.cprime ≠ 0 := by
  intro pubs
  induction pubs with
  | nil => intro seed term _ p hp; simp at hp
  | cons q rest ih =>
      intro seed term h p hp hst
      obtain ⟨-, ⟨g, hg⟩, hrest⟩ := h
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact pole_ne_zero_of_interR inp hg hst
      · exact ih q.icur term hrest p hp' hst

/-! ### The two record columns of a row list -/

/-- The add column: records a `read_root` row adds to `intermediate`, in walk
order.  By state — not by `ver` (external IO is `responseRecords`).
`RowLayout.addedRecordList` is this, composed with the BFS row projection. -/
def addedOf (pubs : List (MemoryTable.Pub K)) : List (ComputeTable.MemRec K) :=
  pubs.flatMap fun p =>
    match p.st with
    | .read_root => [p.mem]
    | .decompose | .halt | .verify_child => []

/-- The remove column: records a `verify_child` row removes from `intermediate`, in walk order. -/
def consumedOf (pubs : List (MemoryTable.Pub K)) : List (ComputeTable.MemRec K) :=
  pubs.flatMap RowLayout.consumedRecords

theorem mem_addedOf {pubs : List (MemoryTable.Pub K)} {r : ComputeTable.MemRec K}
    (hr : r ∈ addedOf pubs) :
    ∃ p ∈ pubs, p.st = MemoryTable.MState.read_root ∧ p.mem = r := by
  obtain ⟨p, hp, hmem⟩ := List.mem_flatMap.mp hr
  refine ⟨p, hp, ?_⟩
  cases hst : p.st with
  | decompose => simp [hst] at hmem
  | halt => simp [hst] at hmem
  | read_root =>
      refine ⟨rfl, ?_⟩
      simp only [hst, List.mem_singleton] at hmem
      exact hmem.symm
  | verify_child => simp [hst] at hmem

theorem mem_consumedOf {pubs : List (MemoryTable.Pub K)} {r : ComputeTable.MemRec K}
    (hr : r ∈ consumedOf pubs) :
    ∃ p ∈ pubs, p.st = MemoryTable.MState.verify_child ∧ p.mem = r := by
  obtain ⟨p, hp, hmem⟩ := List.mem_flatMap.mp hr
  refine ⟨p, hp, ?_⟩
  cases hst : p.st with
  | decompose => simp [RowLayout.consumedRecords, hst] at hmem
  | halt => simp [RowLayout.consumedRecords, hst] at hmem
  | read_root => simp [RowLayout.consumedRecords, hst] at hmem
  | verify_child =>
      refine ⟨rfl, ?_⟩
      simp only [RowLayout.consumedRecords, hst, List.mem_singleton] at hmem
      exact hmem.symm

/-- The add column's LogUp mass is the `read_root` rows' LogUp mass. -/
theorem sum_inv_addedOf (inp : MemoryTable.Inputs K) (pubs : List (MemoryTable.Pub K))
    (hC : ∀ p ∈ pubs, p.cprime = cp p.mem) :
    ((addedOf pubs).map (fun r => (MemoryTable.pole inp r (cp r))⁻¹)).sum
      = ((pubs.filter (fun p => decide (p.st = MemoryTable.MState.read_root))).map
          (fun p => (MemoryTable.pole inp p.mem p.cprime)⁻¹)).sum := by
  induction pubs with
  | nil => simp [addedOf]
  | cons p rest ih =>
      have hCrest : ∀ q ∈ rest, q.cprime = cp q.mem :=
        fun q hq => hC q (List.mem_cons.mpr (Or.inr hq))
      have hCp : p.cprime = cp p.mem := hC p (List.mem_cons.mpr (Or.inl rfl))
      have hadd :
          addedOf (p :: rest) =
            (match p.st with
              | .read_root => [p.mem]
              | .decompose | .halt | .verify_child => []) ++ addedOf rest := by
        simp [addedOf]
      rw [hadd, List.map_append, List.sum_append, ih hCrest, List.filter_cons]
      cases hst : p.st <;> simp [hst, hCp]

/-- The remove column's LogUp mass is the `verify_child` rows' LogUp mass. -/
theorem sum_inv_consumedOf (inp : MemoryTable.Inputs K) (pubs : List (MemoryTable.Pub K))
    (hC : ∀ p ∈ pubs, p.cprime = cp p.mem) :
    ((consumedOf pubs).map (fun r => (MemoryTable.pole inp r (cp r))⁻¹)).sum
      = ((pubs.filter (fun p => decide (p.st = MemoryTable.MState.verify_child))).map
          (fun p => (MemoryTable.pole inp p.mem p.cprime)⁻¹)).sum := by
  induction pubs with
  | nil => simp [consumedOf]
  | cons p rest ih =>
      have hCrest : ∀ q ∈ rest, q.cprime = cp q.mem :=
        fun q hq => hC q (List.mem_cons.mpr (Or.inr hq))
      have hCp : p.cprime = cp p.mem := hC p (List.mem_cons.mpr (Or.inl rfl))
      have hcons : consumedOf (p :: rest) = RowLayout.consumedRecords p ++ consumedOf rest := by
        simp [consumedOf]
      rw [hcons, List.map_append, List.sum_append, ih hCrest, List.filter_cons]
      cases hst : p.st <;> simp [RowLayout.consumedRecords, hst, hCp]

/-- **THE TELESCOPE, at the record columns.**  A verifier `intermediate` chain with both zero
boundaries forces the two record columns to carry equal LogUp mass.  This is
`MemoryTable.interChain_balance` (already in the tree) transported from the `read_root`/
`verify_child` row filters onto the add/remove record columns. -/
theorem interChain_balance_columns (inp : MemoryTable.Inputs K) (pubs : List (MemoryTable.Pub K))
    (hC : ∀ p ∈ pubs, p.cprime = cp p.mem)
    (h : MemoryTable.InterChain inp 0 0 pubs) :
    ((consumedOf pubs).map (fun r => (MemoryTable.pole inp r (cp r))⁻¹)).sum
      = ((addedOf pubs).map (fun r => (MemoryTable.pole inp r (cp r))⁻¹)).sum := by
  have hb := MemoryTable.interChain_balance inp pubs h
  rw [sum_inv_consumedOf cp inp pubs hC, sum_inv_addedOf cp inp pubs hC]
  exact hb.symm

/-- The same telescope off the RAP form of the block. -/
theorem rapInterChain_balance (inp : MemoryTable.Inputs K) (pubs : List (MemoryTable.Pub K))
    (hC : ∀ p ∈ pubs, p.cprime = cp p.mem)
    (h : RAPInterChain inp 0 0 pubs) :
    ((consumedOf pubs).map (fun r => (MemoryTable.pole inp r (cp r))⁻¹)).sum
      = ((addedOf pubs).map (fun r => (MemoryTable.pole inp r (cp r))⁻¹)).sum :=
  interChain_balance_columns cp inp pubs hC (interChain_of_rapInterChain inp pubs 0 0 h)

/-- The poles of both record columns are non-vanishing on a RAP chain. -/
theorem pole_ne_zero_of_mem_columns (inp : MemoryTable.Inputs K)
    (pubs : List (MemoryTable.Pub K))
    (hC : ∀ p ∈ pubs, p.cprime = cp p.mem)
    (h : RAPInterChain inp 0 0 pubs) :
    ∀ r ∈ consumedOf pubs ++ addedOf pubs, MemoryTable.pole inp r (cp r) ≠ 0 := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨p, hp, hst, hmem⟩ := mem_consumedOf hr
    have := pole_ne_zero_of_rapInterChain inp pubs 0 0 h p hp (Or.inr hst)
    rw [hC p hp, hmem] at this
    exact this
  · obtain ⟨p, hp, hst, hmem⟩ := mem_addedOf hr
    have := pole_ne_zero_of_rapInterChain inp pubs 0 0 h p hp (Or.inl hst)
    rw [hC p hp, hmem] at this
    exact this

end AIR

/-! ## §B. The record commitment, the memory table's coins, and the counted pole set -/

section Counted

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
variable (cp : ComputeTable.MemRec K → K)

/-- **The pre-challenge record commitment.**  The remove column on the "requests" side, the add
column on the "responses" side, each flattened by `Def:MEF`.  Same construction as
`PairedRecordCountedEvent.interRecords`, but taking the two columns as *arguments* rather than
reading them off an `E` that also carries the challenges — which is the whole point: this object
mentions no `β`. -/
def recordCommitment (consumed added : List (ComputeTable.MemRec K)) :
    FiniteIO.PreChallengeRecords K 9 where
  requests := consumed.map (fun r => NockVM.encRecC r (cp r))
  responses := added.map (fun r => NockVM.encRecC r (cp r))

omit cp in
/-- The memory table's own `(γ, β)` in `FiniteIO`'s additive pole convention: `pole := -β`, the
documented flag `[M3]` instantiation `X ↦ −β` of the paper. -/
def poleCoins (inp : MemoryTable.Inputs K) : FiniteIO.IOCoins K where
  gamma := inp.γ
  pole := -inp.β

omit cp in
/-- The two poles are the same pole. -/
theorem compress_poleCoins (inp : MemoryTable.Inputs K) (r : ComputeTable.MemRec K) (c : K) :
    FiniteIO.compress (poleCoins inp) (NockVM.encRecC r c) = MemoryTable.pole inp r c := by
  show -inp.β + Walk.rlc inp.γ (NockVM.encRecC r c) = MemoryTable.recRLC inp.γ r c - inp.β
  rw [rlc_encRecC]
  ring

/-- **The counted pole set.**  The set of `β` at which the committed columns' log-derivative
difference polynomial vanishes without being identically zero — `FiniteIO.IOLogDerivEvent` in the
memory table's `−β` convention.  It is a function of the *commitment* and `γ` alone: no execution
and no `β` occur in its construction, which is exactly what makes quantifying `β` outside it a
condition on the challenge rather than on the prover's data. -/
def badPoleSet (consumed added : List (ComputeTable.MemRec K)) (γ : K) : Finset K :=
  (FiniteIO.IOLogDerivEvent (recordCommitment cp consumed added) γ).image (fun z => -z)

theorem mem_badPoleSet_iff (consumed added : List (ComputeTable.MemRec K)) (γ β : K) :
    β ∈ badPoleSet cp consumed added γ
      ↔ -β ∈ FiniteIO.IOLogDerivEvent (recordCommitment cp consumed added) γ := by
  classical
  simp only [badPoleSet, Finset.mem_image]
  refine ⟨?_, fun h => ⟨-β, h, neg_neg β⟩⟩
  rintro ⟨z, hz, rfl⟩
  simpa using hz

/-- **THE COUNT.**  At most one bad pole per committed record: univariate Schwartz–Zippel on the
`ioQP` certificate (`FiniteIO.IOLogDerivEvent_card_le`).  This is the whole probabilistic content
of the argument. -/
theorem badPoleSet_card_le (consumed added : List (ComputeTable.MemRec K)) (γ : K) :
    (badPoleSet cp consumed added γ).card ≤ consumed.length + added.length := by
  classical
  refine le_trans Finset.card_image_le ?_
  have h := FiniteIO.IOLogDerivEvent_card_le (recordCommitment cp consumed added) γ
  simpa [recordCommitment] using h

/-- **The bad set is EMPTY when the columns already match.**  So the hypothesis `β ∉ badPoleSet`
costs nothing exactly where the conclusion holds — which is `PairedRecordCountedEvent` §D's
equivalence, now stated of the *commitment* instead of of a bundled `E`.  It is why the
`∀ β ∉ bad` quantifier below has content: the restriction bites only on an unpaired commitment,
and there it bites on at most `#consumed + #added` challenges. -/
theorem badPoleSet_eq_empty_of_perm {consumed added : List (ComputeTable.MemRec K)}
    (hlc : consumed.length < ringChar K) (hla : added.length < ringChar K)
    (h : consumed.Perm added) (γ : K) : badPoleSet cp consumed added γ = ∅ := by
  classical
  have hQ : FiniteIO.ioQP (recordCommitment cp consumed added) γ = 0 := by
    refine ioQP_eq_zero_of_perm γ ?_ ?_ ?_
    · simpa [recordCommitment] using hlc
    · simpa [recordCommitment] using hla
    · exact h.map (fun r => NockVM.encRecC r (cp r))
  have hev : FiniteIO.IOLogDerivEvent (recordCommitment cp consumed added) γ = ∅ := by
    rw [FiniteIO.IOLogDerivEvent, Finset.filter_eq_empty_iff]
    intro z _
    rintro ⟨hne, -⟩
    exact hne hQ
  rw [badPoleSet, hev, Finset.image_empty]

/-! ## §C. The engine: a `PreChallengeRecords`-level permutation read-off

`FiniteIO.finiteIO_sound` glues this to `FiniteIOAccepts` and exits through `lem:set_inclusion`,
so it needs both columns `Nodup`.  `PairedRecordCountedEvent.pairedRecordLayout_of_counted_events`
glues it to `E`. -/

/-- **The read-off.**  Two record columns whose compressed reciprocals sum to the same value at a
pole outside the log-derivative event, with a compression challenge outside the RLC-collision
event and both lengths below the characteristic, are a permutation of each other. -/
theorem perm_of_compress_sum_eq
    (C : FiniteIO.PreChallengeRecords K 9) (coins : FiniteIO.IOCoins K)
    (hk₁ : C.requests.length < ringChar K) (hk₂ : C.responses.length < ringChar K)
    (hne : ∀ v ∈ C.requests ++ C.responses, FiniteIO.compress coins v ≠ 0)
    (hbal : (C.requests.map (fun v => (FiniteIO.compress coins v)⁻¹)).sum
              = (C.responses.map (fun v => (FiniteIO.compress coins v)⁻¹)).sum)
    (hγ : coins.gamma ∉ FiniteIO.IORLCCollisionEvent C)
    (hz : coins.pole ∉ FiniteIO.IOLogDerivEvent C coins.gamma) :
    C.requests.Perm C.responses := by
  classical
  have hdA : ∀ i, coins.pole + FiniteIO.reqVals C coins.gamma i ≠ 0 := fun i =>
    hne _ (List.mem_append_left _ (List.get_mem _ _))
  have hdB : ∀ j, coins.pole + FiniteIO.respVals C coins.gamma j ≠ 0 := fun j =>
    hne _ (List.mem_append_right _ (List.get_mem _ _))
  have hend : (∑ i, (coins.pole + FiniteIO.reqVals C coins.gamma i)⁻¹)
      = ∑ j, (coins.pole + FiniteIO.respVals C coins.gamma j)⁻¹ := by
    have e1 : (∑ i, (coins.pole + FiniteIO.reqVals C coins.gamma i)⁻¹)
        = (C.requests.map (fun v => (FiniteIO.compress coins v)⁻¹)).sum :=
      FiniteIO.sum_fin_get C.requests (fun v => (FiniteIO.compress coins v)⁻¹)
    have e2 : (∑ j, (coins.pole + FiniteIO.respVals C coins.gamma j)⁻¹)
        = (C.responses.map (fun v => (FiniteIO.compress coins v)⁻¹)).sum :=
      FiniteIO.sum_fin_get C.responses (fun v => (FiniteIO.compress coins v)⁻¹)
    rw [e1, e2, hbal]
  -- the difference polynomial vanishes at the sampled pole
  have hQeval : (FiniteIO.ioQP C coins.gamma).eval coins.pole = 0 := by
    have hSA := FiniteIO.sum_inv_eval (FiniteIO.reqVals C coins.gamma) coins.pole hdA
    have hSB := FiniteIO.sum_inv_eval (FiniteIO.respVals C coins.gamma) coins.pole hdB
    simp only [FiniteIO.ioQP, Polynomial.eval_sub, Polynomial.eval_mul]
    have h1 : (FiniteIO.numerP (FiniteIO.reqVals C coins.gamma)).eval coins.pole
          * (FiniteIO.denomP (FiniteIO.respVals C coins.gamma)).eval coins.pole
        = ((∑ i, (coins.pole + FiniteIO.reqVals C coins.gamma i)⁻¹)
              * (FiniteIO.denomP (FiniteIO.reqVals C coins.gamma)).eval coins.pole)
            * (FiniteIO.denomP (FiniteIO.respVals C coins.gamma)).eval coins.pole := by rw [hSA]
    have h2 : (FiniteIO.numerP (FiniteIO.respVals C coins.gamma)).eval coins.pole
          * (FiniteIO.denomP (FiniteIO.reqVals C coins.gamma)).eval coins.pole
        = ((∑ j, (coins.pole + FiniteIO.respVals C coins.gamma j)⁻¹)
              * (FiniteIO.denomP (FiniteIO.respVals C coins.gamma)).eval coins.pole)
            * (FiniteIO.denomP (FiniteIO.reqVals C coins.gamma)).eval coins.pole := by rw [hSB]
    rw [h1, h2, hend]
    ring
  -- …hence identically, off the counted event
  have hQ0 : FiniteIO.ioQP C coins.gamma = 0 := by
    by_contra hne0
    exact hz (by
      simp only [FiniteIO.IOLogDerivEvent, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hne0, hQeval⟩)
  have hQ : FiniteIO.numerP (FiniteIO.reqVals C coins.gamma)
        * FiniteIO.denomP (FiniteIO.respVals C coins.gamma)
      = FiniteIO.numerP (FiniteIO.respVals C coins.gamma)
        * FiniteIO.denomP (FiniteIO.reqVals C coins.gamma) := by
    have hh := hQ0
    unfold FiniteIO.ioQP at hh
    rwa [sub_eq_zero] at hh
  -- `Lem:ldse_mse` and unique factorisation
  have hmse :
      (∏ i, (Polynomial.X + Polynomial.C (FiniteIO.reqVals C coins.gamma i)))
        = ∏ j, (Polynomial.X + Polynomial.C (FiniteIO.respVals C coins.gamma j)) :=
    (SetEq.mse_ldse_general (p := ringChar K) hk₁ hk₂ _ _).mpr
      (frac_sum_eq_of_ioQP_zero _ _ hQ)
  have hms :
      ((C.requests.map (Walk.rlc coins.gamma) : List K) : Multiset K)
        = ((C.responses.map (Walk.rlc coins.gamma) : List K) : Multiset K) := by
    refine (IO.prodXaddC_ms_inj _ _).mp ?_
    rw [← denomP_eq_ms_prod, ← denomP_eq_ms_prod]
    exact hmse
  refine perm_of_perm_map_of_injOn (Walk.rlc coins.gamma) ?_ (Multiset.coe_eq_coe.mp hms)
  intro u hu v hv heq
  exact FiniteIO.rlc_inj_of_not_collision hγ hu hv heq

/-- The same read-off, on `MemRec` columns at the memory table's own `(γ, β)`. -/
theorem perm_of_logup_balance (inp : MemoryTable.Inputs K)
    (consumed added : List (ComputeTable.MemRec K))
    (hlc : consumed.length < ringChar K) (hla : added.length < ringChar K)
    (hγ : inp.γ ∉ FiniteIO.IORLCCollisionEvent (recordCommitment cp consumed added))
    (hβ : inp.β ∉ badPoleSet cp consumed added inp.γ)
    (hpole : ∀ r ∈ consumed ++ added, MemoryTable.pole inp r (cp r) ≠ 0)
    (hbal : (consumed.map (fun r => (MemoryTable.pole inp r (cp r))⁻¹)).sum
              = (added.map (fun r => (MemoryTable.pole inp r (cp r))⁻¹)).sum) :
    consumed.Perm added := by
  classical
  have hne : ∀ v ∈ (recordCommitment cp consumed added).requests
        ++ (recordCommitment cp consumed added).responses,
      FiniteIO.compress (poleCoins inp) v ≠ 0 := by
    intro v hv
    have hex : ∃ r ∈ consumed ++ added, NockVM.encRecC r (cp r) = v := by
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨r, hr, hrv⟩ := List.mem_map.mp hv
        exact ⟨r, List.mem_append_left _ hr, hrv⟩
      · obtain ⟨r, hr, hrv⟩ := List.mem_map.mp hv
        exact ⟨r, List.mem_append_right _ hr, hrv⟩
    obtain ⟨r, hr, rfl⟩ := hex
    rw [compress_poleCoins]
    exact hpole r hr
  have hbal' :
      ((recordCommitment cp consumed added).requests.map
          (fun v => (FiniteIO.compress (poleCoins inp) v)⁻¹)).sum
        = ((recordCommitment cp consumed added).responses.map
            (fun v => (FiniteIO.compress (poleCoins inp) v)⁻¹)).sum := by
    have e1 : ((recordCommitment cp consumed added).requests.map
          (fun v => (FiniteIO.compress (poleCoins inp) v)⁻¹)).sum
        = (consumed.map (fun r => (MemoryTable.pole inp r (cp r))⁻¹)).sum := by
      show ((consumed.map (fun r => NockVM.encRecC r (cp r))).map
          (fun v => (FiniteIO.compress (poleCoins inp) v)⁻¹)).sum = _
      rw [List.map_map]
      exact congrArg List.sum (List.map_congr_left (fun r _ => by
        simp only [Function.comp_apply, compress_poleCoins]))
    have e2 : ((recordCommitment cp consumed added).responses.map
          (fun v => (FiniteIO.compress (poleCoins inp) v)⁻¹)).sum
        = (added.map (fun r => (MemoryTable.pole inp r (cp r))⁻¹)).sum := by
      show ((added.map (fun r => NockVM.encRecC r (cp r))).map
          (fun v => (FiniteIO.compress (poleCoins inp) v)⁻¹)).sum = _
      rw [List.map_map]
      exact congrArg List.sum (List.map_congr_left (fun r _ => by
        simp only [Function.comp_apply, compress_poleCoins]))
    rw [e1, e2, hbal]
  have hperm := perm_of_compress_sum_eq (recordCommitment cp consumed added) (poleCoins inp)
    (by simpa [recordCommitment] using hlc) (by simpa [recordCommitment] using hla)
    hne hbal' hγ ((mem_badPoleSet_iff cp consumed added inp.γ inp.β).not.mp hβ)
  have hinj : Function.Injective (fun r => NockVM.encRecC r (cp r)) := by
    intro r s h
    have hs : ∀ i : Fin 9, NockVM.encRecC r (cp r) i = NockVM.encRecC s (cp s) i :=
      fun i => congrFun h i
    refine ComputeTable.MemRec.ext (ComputeTable.FP.ext ?_ ?_ ?_)
      (ComputeTable.FP.ext ?_ ?_ ?_) ?_ ?_
    · simpa [NockVM.encRecC] using hs 0
    · simpa [NockVM.encRecC] using hs 1
    · simpa [NockVM.encRecC] using hs 2
    · simpa [NockVM.encRecC] using hs 3
    · simpa [NockVM.encRecC] using hs 4
    · simpa [NockVM.encRecC] using hs 5
    · simpa [NockVM.encRecC] using hs 6
    · simpa [NockVM.encRecC] using hs 7
  have hms :
      ((consumed : Multiset (ComputeTable.MemRec K)).map (fun r => NockVM.encRecC r (cp r)))
        = ((added : Multiset (ComputeTable.MemRec K)).map
            (fun r => NockVM.encRecC r (cp r))) := by
    rw [Multiset.map_coe, Multiset.map_coe]
    exact Multiset.coe_eq_coe.mpr hperm
  exact Multiset.coe_eq_coe.mp (Multiset.map_injective hinj hms)

/-! ## §D. The row-level statement, and the chronologically ordered headline -/

/-- **`PairedRecordLayout` at the row-list level, from the AIR block alone.**  The only AIR input
is the chained RAP `intermediate` column with both zero boundaries; the pole genericity is derived
from its inverse-witness gate, and the telescope from `MemoryTable.interChain_balance`. -/
theorem perm_of_rapInterChain (inp : MemoryTable.Inputs K) (pubs : List (MemoryTable.Pub K))
    (hlc : (consumedOf pubs).length < ringChar K)
    (hla : (addedOf pubs).length < ringChar K)
    (hγ : inp.γ ∉ FiniteIO.IORLCCollisionEvent
            (recordCommitment cp (consumedOf pubs) (addedOf pubs)))
    (hβ : inp.β ∉ badPoleSet cp (consumedOf pubs) (addedOf pubs) inp.γ)
    (hC : ∀ p ∈ pubs, p.cprime = cp p.mem)
    (h : RAPInterChain inp 0 0 pubs) :
    (consumedOf pubs).Perm (addedOf pubs) :=
  perm_of_logup_balance cp inp _ _ hlc hla hγ hβ
    (pole_ne_zero_of_mem_columns cp inp pubs hC h) (rapInterChain_balance cp inp pubs hC h)

/-- **The same, off the ALGORITHM's form of the block** (`MemoryTable.InterChain`, the shape
`GenericHonestData.execution_interChain` derives unconditionally on `E`), with the pole genericity
of the paper taken as the separate hypothesis it is there — this is
`PairedRecordCountedEvent.InterPoleGeneric`, discharged from `MemoryTable.WF` by
`interPoleGeneric_of_wf`. -/
theorem perm_of_interChain (inp : MemoryTable.Inputs K) (pubs : List (MemoryTable.Pub K))
    (hlc : (consumedOf pubs).length < ringChar K)
    (hla : (addedOf pubs).length < ringChar K)
    (hγ : inp.γ ∉ FiniteIO.IORLCCollisionEvent
            (recordCommitment cp (consumedOf pubs) (addedOf pubs)))
    (hβ : inp.β ∉ badPoleSet cp (consumedOf pubs) (addedOf pubs) inp.γ)
    (hpole : ∀ r ∈ consumedOf pubs ++ addedOf pubs, MemoryTable.pole inp r (cp r) ≠ 0)
    (hC : ∀ p ∈ pubs, p.cprime = cp p.mem)
    (h : MemoryTable.InterChain inp 0 0 pubs) :
    (consumedOf pubs).Perm (addedOf pubs) :=
  perm_of_logup_balance cp inp _ _ hlc hla hγ hβ hpole (interChain_balance_columns cp inp pubs hC h)

/-- **THE HEADLINE — counted soundness with the bad set exhibited before the challenge.**

Fix a record commitment (two `MemRec` columns) and a compression challenge `γ` outside the
RLC-collision event.  Then there is a `Finset K` of at most `#consumed + #added` pole challenges
outside which **no** row list carrying those two columns admits a closed RAP `intermediate`
chain unless the columns are a permutation of each other.

The quantifier order is the content.  `bad` is constructed from `consumed`, `added` and `γ` — it
mentions no `β` and no execution — and `β`, the seed `z` and the row list are all quantified after
it.  `PairedRecordCountedEvent` §D's finding (excluding counted event (3) is *equivalent* to the
conclusion) and its "`E` has no chronology" disclosure are both statements about a bundled `E`
whose challenges and record columns cannot be ordered; neither applies here, and
`badPoleSet_eq_empty_of_perm` shows the restriction is vacuous on a paired commitment and
therefore bites only where cheating is attempted.

This is **not** a zero-error inhabitation of `PairedRecordLayout`: LogUp at a sampled pole cannot
be zero-error, and the cardinality bound is the strongest true statement of this shape. -/
theorem counted_soundness_of_record_commitment
    (consumed added : List (ComputeTable.MemRec K)) (γ : K)
    (hlc : consumed.length < ringChar K) (hla : added.length < ringChar K)
    (hγ : γ ∉ FiniteIO.IORLCCollisionEvent (recordCommitment cp consumed added)) :
    ∃ bad : Finset K,
      bad.card ≤ consumed.length + added.length
        ∧ ∀ β ∉ bad, ∀ (z : K) (pubs : List (MemoryTable.Pub K)),
            consumedOf pubs = consumed → addedOf pubs = added →
            RAPInterChain (⟨z, β, γ⟩ : MemoryTable.Inputs K) 0 0 pubs →
            (∀ p ∈ pubs, p.cprime = cp p.mem) →
            consumed.Perm added := by
  refine ⟨badPoleSet cp consumed added γ, badPoleSet_card_le cp consumed added γ, ?_⟩
  intro β hβ z pubs hc ha hchain hC
  have hres := perm_of_rapInterChain cp (⟨z, β, γ⟩ : MemoryTable.Inputs K) pubs
    (by rw [hc]; exact hlc) (by rw [ha]; exact hla)
    (by rw [hc, ha]; exact hγ) (by rw [hc, ha]; exact hβ) hC hchain
  rwa [hc, ha] at hres

/-! ## §E. The `ExactExecution` carrier, and `timestampClosed` -/

variable {F : Type} [Field F] [Algebra F K]

theorem consumedOf_memoryPubRows {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    consumedOf (memoryPubRows exec) = RowLayout.consumedRecordList exec := by
  show (exec.memoryRows.map (fun row => row.2.2)).flatMap RowLayout.consumedRecords
      = exec.memoryRows.flatMap (fun row => RowLayout.consumedRecords row.2.2)
  rw [List.flatMap_map]

theorem addedOf_memoryPubRows {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    addedOf (memoryPubRows exec) = RowLayout.addedRecordList exec := by
  show (exec.memoryRows.map (fun row => row.2.2)).flatMap
        (fun p =>
          match p.st with
          | .read_root => [p.mem]
          | .decompose | .halt | .verify_child => [])
      = exec.memoryRows.flatMap fun row =>
          match row.2.2.st with
          | .read_root => [row.2.2.mem]
          | .decompose | .halt | .verify_child => []
  rw [List.flatMap_map]

/-- **`RowLayout.PairedRecordLayout` on the real carrier**, from the memory RAP's `intermediate`
block at the configuration's own challenge tuple. -/
theorem pairedRecordLayout_of_rapInterChain {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (inp : MemoryTable.Inputs K)
    (hlc : (RowLayout.consumedRecordList exec).length < ringChar K)
    (hla : (RowLayout.addedRecordList exec).length < ringChar K)
    (hγ : inp.γ ∉ FiniteIO.IORLCCollisionEvent
            (recordCommitment cp (RowLayout.consumedRecordList exec)
              (RowLayout.addedRecordList exec)))
    (hβ : inp.β ∉ badPoleSet cp (RowLayout.consumedRecordList exec)
            (RowLayout.addedRecordList exec) inp.γ)
    (hC : ∀ row ∈ exec.memoryRows, row.2.2.cprime = cp row.2.2.mem)
    (h : RAPInterChain inp 0 0 (memoryPubRows exec)) :
    RowLayout.PairedRecordLayout exec := by
  have hCpubs : ∀ p ∈ memoryPubRows exec, p.cprime = cp p.mem := by
    intro p hp
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hp
    exact hC row hrow
  have hres := perm_of_rapInterChain cp inp (memoryPubRows exec)
    (by rw [consumedOf_memoryPubRows]; exact hlc)
    (by rw [addedOf_memoryPubRows]; exact hla)
    (by rw [consumedOf_memoryPubRows, addedOf_memoryPubRows]; exact hγ)
    (by rw [consumedOf_memoryPubRows, addedOf_memoryPubRows]; exact hβ) hCpubs h
  rw [consumedOf_memoryPubRows, addedOf_memoryPubRows] at hres
  exact hres

/-- **The headline at the `ExactExecution` carrier.**  The bad set precedes `β`, the configuration
and the execution alike. -/
theorem counted_soundness_of_exact_execution
    (consumed added : List (ComputeTable.MemRec K)) (γ : K)
    (hlc : consumed.length < ringChar K) (hla : added.length < ringChar K)
    (hγ : γ ∉ FiniteIO.IORLCCollisionEvent (recordCommitment cp consumed added)) :
    ∃ bad : Finset K,
      bad.card ≤ consumed.length + added.length
        ∧ ∀ β ∉ bad, ∀ (z : K) (cfg : ExactConfig F K) (exec : ExactExecution cfg),
            RowLayout.consumedRecordList exec = consumed →
            RowLayout.addedRecordList exec = added →
            RAPInterChain (⟨z, β, γ⟩ : MemoryTable.Inputs K) 0 0 (memoryPubRows exec) →
            (∀ row ∈ exec.memoryRows, row.2.2.cprime = cp row.2.2.mem) →
            RowLayout.PairedRecordLayout exec := by
  refine ⟨badPoleSet cp consumed added γ, badPoleSet_card_le cp consumed added γ, ?_⟩
  intro β hβ z cfg exec hc ha hchain hC
  refine pairedRecordLayout_of_rapInterChain cp exec (⟨z, β, γ⟩ : MemoryTable.Inputs K)
    (by rw [hc]; exact hlc) (by rw [ha]; exact hla)
    (by rw [hc, ha]; exact hγ) (by rw [hc, ha]; exact hβ) hC hchain

/-- …and therefore `MemoryRecordPremises.timestampClosed`, through the bridge that was already
written (`GenericHonestData.timestampClosed_of_paired_record_layout`).  Step 4 of the route needed
nothing new, exactly as briefed. -/
theorem timestampClosed_of_rapInterChain (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (inp : MemoryTable.Inputs K)
    (hlc : (RowLayout.consumedRecordList E.exec).length < ringChar K)
    (hla : (RowLayout.addedRecordList E.exec).length < ringChar K)
    (hγ : inp.γ ∉ FiniteIO.IORLCCollisionEvent
            (recordCommitment cp (RowLayout.consumedRecordList E.exec)
              (RowLayout.addedRecordList E.exec)))
    (hβ : inp.β ∉ badPoleSet cp (RowLayout.consumedRecordList E.exec)
            (RowLayout.addedRecordList E.exec) inp.γ)
    (hC : ∀ row ∈ E.exec.memoryRows, row.2.2.cprime = cp row.2.2.mem)
    (h : RAPInterChain inp 0 0 (memoryPubRows E.exec)) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt E.cfg.challenges.α (E.exec.memoryRowAt i).2.2.mem.ts :=
  timestampClosed_of_paired_record_layout hhon
    (pairedRecordLayout_of_rapInterChain cp E.exec inp hlc hla hγ hβ hC h)

/-- **THE HEADLINE at `BuildableNockExecution`, with no chain hypothesis at all.**

`GenericHonestData.execution_interChain` derives the whole ordered `intermediate` accumulator
with both zero boundaries **unconditionally on `E`**, so at this carrier the AIR input is already
paid for.  What is left, once the bad set is exhibited before the challenge, is exactly:

* the two row-count windows below the characteristic;
* `γ` outside the RLC-collision event — the same event the external IO columns take as a named
  `Inputs` field;
* the paper's own the paper genericity (`InterPoleGeneric`, taken at the record's own `C'`
  `cp r` since row-level memory retired `C' = 1`);
* and `β` outside a set of at most `#consumed + #added` values **determined by the pre-challenge
  record commitment and `γ` alone**.

That last item is the residual, and this is its exact size. -/
theorem counted_soundness_of_buildable_execution
    (consumed added : List (ComputeTable.MemRec K)) (γ : K)
    (hlc : consumed.length < ringChar K) (hla : added.length < ringChar K)
    (hγ : γ ∉ FiniteIO.IORLCCollisionEvent (recordCommitment cp consumed added)) :
    ∃ bad : Finset K,
      bad.card ≤ consumed.length + added.length
        ∧ ∀ β ∉ bad, ∀ E : BuildableNockExecution F K,
            E.cfg.challenges.memoryInputs.β = β →
            E.cfg.challenges.memoryInputs.γ = γ →
            RowLayout.consumedRecordList E.exec = consumed →
            RowLayout.addedRecordList E.exec = added →
            -- Row-level memory: `PairedRecordCountedEvent.InterPoleGeneric` at the record's own
            -- `C'` (`cp`) instead of the retired `C' = 1`.
            (∀ r ∈ RowLayout.consumedRecordList E.exec ++ RowLayout.addedRecordList E.exec,
              MemoryTable.pole E.cfg.challenges.memoryInputs r (cp r) ≠ 0) →
            (∀ row ∈ E.exec.memoryRows, row.2.2.cprime = cp row.2.2.mem) →
            RowLayout.PairedRecordLayout E.exec := by
  refine ⟨badPoleSet cp consumed added γ, badPoleSet_card_le cp consumed added γ, ?_⟩
  intro β hβ E hEβ hEγ hc ha hgen hC
  have hchain := execution_interChain E
  have hCpubs : ∀ p ∈ memoryPubRows E.exec, p.cprime = cp p.mem := by
    intro p hp
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hp
    exact hC row hrow
  have hres := perm_of_interChain cp E.cfg.challenges.memoryInputs (memoryPubRows E.exec)
    (by rw [consumedOf_memoryPubRows, hc]; exact hlc)
    (by rw [addedOf_memoryPubRows, ha]; exact hla)
    (by rw [consumedOf_memoryPubRows, addedOf_memoryPubRows, hc, ha, hEγ]; exact hγ)
    (by rw [consumedOf_memoryPubRows, addedOf_memoryPubRows, hc, ha, hEγ, hEβ]; exact hβ)
    (by rw [consumedOf_memoryPubRows, addedOf_memoryPubRows]; exact hgen)
    hCpubs hchain
  rw [consumedOf_memoryPubRows, addedOf_memoryPubRows] at hres
  exact hres

end Counted

end

end Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLogUp


#print axioms Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLogUp.pole_ne_zero_of_interR
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLogUp.interV_of_interR
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLogUp.interChain_balance_columns
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLogUp.rapInterChain_balance
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLogUp.pole_ne_zero_of_mem_columns
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLogUp.badPoleSet_card_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLogUp.badPoleSet_eq_empty_of_perm
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLogUp.perm_of_compress_sum_eq
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLogUp.perm_of_logup_balance
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLogUp.perm_of_rapInterChain
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLogUp.perm_of_interChain
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLogUp.counted_soundness_of_record_commitment
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLogUp.pairedRecordLayout_of_rapInterChain
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLogUp.counted_soundness_of_exact_execution
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLogUp.timestampClosed_of_rapInterChain
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLogUp.counted_soundness_of_buildable_execution
