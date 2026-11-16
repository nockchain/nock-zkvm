import Nock.NockVMROM.Thm54.PairedRecordIOResult
import Nock.RedTeam.Batch131Thm54PairedRecordLayout

/-!
# Which `PairedRecordLayout` carrier option is faithful

Different context from the
prover.  Nothing here inhabits any named premise and **no carrier field is added**.

**Status of the cites only.

* **the paper is BLANK.**  "An intermediate aggregator `intermediate ∈ K`" is at **`2120`**.
  The gate cite `2123` was always right.
* **the paper is BLANK.**  `acc_prog ∈ K^{h₁} ⊆ F^{h₁ × e}` is at **`510`**.
* **the paper is BLANK.**  The Log-Derivative Multiset Argument Aggregation Constraint heading
  is at **`523`** and its `\textit{Specification:}` display — the layer the sibling cites `549` and
  `577` land on — is at **`526`**.  Cite `526` to match the siblings.

**Every verdict here is unaffected**, because each corrected line says exactly what was attributed
to the blank one: the paper does type `intermediate ∈ K`, the accumulator is
`acc_prog ∈ K^{h₁} ⊆ F^{h₁ × e}`, and the aggregation gates are written with the scalar pole.

## Paper frame, body before appendix

* the paper — `read_root` removes a record from the `IO` column and **adds** it to the global
  accumulator `intermediate`; the paper — `verify_child` **removes** an element from
  `intermediate`.
* the paper — "the `IO` and `intermediate` multisets are also checked to be zero, so every
  timestamp needs to be removed from the `IO` multiset, added to `intermediate`, and then removed
  again."
* the paper — the hinge: `intermediate` "is considered a witness element and its constraints
  are implemented in the exact same way as in `RAP_mem-IO`, `RAP_comp-IO`", and "the argument is
  equivalent to Theorem `Thm:IO_result`, noting simply that in this case the `IO` and `intermediate`
  columns function as the two memory record columns that are matched within the same table".
* **What `RAP_prog-IO` / `RAP_mem-IO` actually are in the paper.**  the paper — "Verifier
  responds with random elements `α, β ∈ K`"; the paper — the accumulator is
  `acc_prog ∈ K^{h₁} ⊆ F^{h₁ × e}`; the paper — every
  aggregation gate is written with the **scalar** pole `RLC^α(·) − β`.  So the paper's own
  `RAP_mem-IO` / `RAP_comp-IO` live at a **sampled scalar challenge over `K`**, and the formal
  `X`, `Y` appear only one layer up, in the *languages* `L_MSE`, `L_LDSE`, `L_uSE`, `L_umLDSE` and the *lemmas*
  `Lem:ldse_mse`, `lem:set_inclusion` that
  `Thm:IO_result` reduces to.
* **And the `intermediate` aggregator is typed the same way.**  the paper — "an intermediate
  aggregator `intermediate ∈ K`"; the paper — its constraint is
  `(RLC^γ(mem_record(i)) − β)·(intermediate(i) − intermediate(i−1)) = op₃(i) − op₂(i)`, at scalar
  `β, γ`.  The formal `X` of `Algorithm:Memspec` is instantiated
  to `−β` in the arithmetization, which is exactly the repo's documented flag `[M3]`
  (`Nock/MemoryTable.lean:106-108`).
* `tab:v_mem` — row `mem.root`, column `verify_child`, entry `⊥`.

## Verdict summary

* Carrier option **(a)** — restating `interV` over `RatFunc (RatFunc K)` — is **not** the shape this
  repo gives the other IO columns and is **not** the paper's shape either: the paper types
  `intermediate ∈ K` and the paper put `RAP_prog-IO`/`RAP_mem-IO` at sampled scalars.
  What the repo carries for the external IO columns is the **record-level** `L_mIO`/`L_IO`
  (`SemanticIOPreimage.semantic_lmio`, derived to `execution_lio_of_requestNodup`), and the
  `intermediate` analogue of *that* object is `PairedRecordLayout` itself
  (`intermediate_matching_at_the_record_level_is_the_premise`).
* Carrier option **(b)** — a `BuildableNockExecution` field of shape `InterChainChallengeFamily` —
  is **worse than not-progress: it is uninhabitable exactly where the premise has content.**
  `interV_not_universal` compiles that a `read_root`/`verify_child` row's accumulator step cannot
  hold at every challenge tuple (the step is a fixed `K`-difference, the pole's inverse is not), so
  `interChainChallengeFamily_false_of_live_row` refutes the field on any execution with an axis
  lookup, and `interChainChallengeFamily_forces_empty_columns` shows it can only hold when both
  record columns are empty — where `PairedRecordLayout` is already free
  (`interChainChallengeFamily_only_where_the_premise_is_free`).  A J.0.3 non-vacuity witness for (b)
  is therefore **not constructible at any fixture**, and the field must not be added.

Nothing here is a claim about the paper's construction: the paper's `intermediate` accumulator is at
one sampled scalar by design, and `Thm:IO_result`'s upgrade to a multiset statement is a *soundness*
argument with counted failure events — which this repo already has for the external IO columns
(`FiniteIO.finiteIO_sound`, `IORLCCollisionEvent`, `IOLogDerivEvent`).  The residual is a
formalization-layer obligation, not a defect of the paper.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Nock.RedTeam.Batch132

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.PairedRecordIOResult
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

/-- The fixture base field. -/
abbrev F97 := ZMod 97

local instance prime97b132 : Fact (Nat.Prime 97) := ⟨by norm_num⟩

noncomputable section

/-! ## §0. Field-generic lemmas (no `F`, no `Algebra`, no finiteness) -/

section Generic

variable {K : Type*} [Field K]

/-- **A live accumulator row cannot satisfy its step at every challenge tuple.**  Two challenge
tuples suffice, and neither needs a field-size hypothesis: at `β = RLC^γ(mem)` the pole is `0` (so
Lean's inverse is `0`), and at `β = RLC^γ(mem) − 1` the pole is `1`.  A fixed `icur − ipre` cannot
be both. -/
theorem interV_not_universal {p : MemoryTable.Pub K}
    (hst : p.st = MemoryTable.MState.read_root ∨ p.st = MemoryTable.MState.verify_child) :
    ¬ (∀ inp : MemoryTable.Inputs K, MemoryTable.interV inp p) := by
  intro h
  have hp0 : MemoryTable.pole
      (⟨0, MemoryTable.recRLC (1 : K) p.mem p.cprime, 1⟩ : MemoryTable.Inputs K) p.mem p.cprime = 0 := by
    simp [MemoryTable.pole]
  have hp1 : MemoryTable.pole
      (⟨0, MemoryTable.recRLC (1 : K) p.mem p.cprime - 1, 1⟩ : MemoryTable.Inputs K) p.mem p.cprime = 1 := by
    simp [MemoryTable.pole]
  have e0 := (MemoryTable.interV_iff_delta
    (⟨0, MemoryTable.recRLC (1 : K) p.mem p.cprime, 1⟩ : MemoryTable.Inputs K) p).mp
      (h ⟨0, MemoryTable.recRLC (1 : K) p.mem p.cprime, 1⟩)
  have e1 := (MemoryTable.interV_iff_delta
    (⟨0, MemoryTable.recRLC (1 : K) p.mem p.cprime - 1, 1⟩ : MemoryTable.Inputs K) p).mp
      (h ⟨0, MemoryTable.recRLC (1 : K) p.mem p.cprime - 1, 1⟩)
  rcases hst with hst | hst
  · rw [MemoryTable.interDelta, hst, hp0, inv_zero] at e0
    rw [MemoryTable.interDelta, hst, hp1, inv_one] at e1
    exact one_ne_zero (α := K) (e1.symm.trans e0)
  · rw [MemoryTable.interDelta, hst, hp0, inv_zero, neg_zero] at e0
    rw [MemoryTable.interDelta, hst, hp1, inv_one] at e1
    have hone : (1 : K) = 0 := by
      have h' : -(1 : K) = 0 := e1.symm.trans e0
      linear_combination -h'
    exact one_ne_zero hone

/-- Every row of a chained `intermediate` accumulator satisfies its own per-row step. -/
theorem interChain_mem_interV (inp : MemoryTable.Inputs K) :
    ∀ (rows : List (MemoryTable.Pub K)) (seed term : K),
      MemoryTable.InterChain inp seed term rows →
        ∀ p ∈ rows, MemoryTable.interV inp p := by
  intro rows
  induction rows with
  | nil => intro _ _ _ p hp; exact absurd hp (List.not_mem_nil)
  | cons a rest ih =>
      intro seed term h p hp
      obtain ⟨_, hV, hrest⟩ := h
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact hV
      · exact ih a.icur term hrest p hp'

/-- Independent injectivity proof for the eight-coordinate flattening (`Def:MEF`). -/
theorem redteam_encRec_injective : Function.Injective (NockVM.encRec (K := K)) := by
  intro r s h
  have h0 : r.root.size = s.root.size := congrFun h 0
  have h1 : r.root.dyck = s.root.dyck := congrFun h 1
  have h2 : r.root.leaf = s.root.leaf := congrFun h 2
  have h3 : r.child.size = s.child.size := congrFun h 3
  have h4 : r.child.dyck = s.child.dyck := congrFun h 4
  have h5 : r.child.leaf = s.child.leaf := congrFun h 5
  have h6 : r.axis = s.axis := congrFun h 6
  have h7 : r.ts = s.ts := congrFun h 7
  exact ComputeTable.MemRec.ext (ComputeTable.FP.ext h0 h1 h2)
    (ComputeTable.FP.ext h3 h4 h5) h6 h7

/-- Each of the eight coordinates reads back exactly one record field — the reason injectivity
holds, recorded so it is not taken on faith. -/
theorem encRec_reads_back_every_field (r : ComputeTable.MemRec K) :
    NockVM.encRec r 0 = r.root.size ∧ NockVM.encRec r 1 = r.root.dyck
      ∧ NockVM.encRec r 2 = r.root.leaf ∧ NockVM.encRec r 3 = r.child.size
      ∧ NockVM.encRec r 4 = r.child.dyck ∧ NockVM.encRec r 5 = r.child.leaf
      ∧ NockVM.encRec r 6 = r.axis ∧ NockVM.encRec r 7 = r.ts :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Independent un-encoding, by multiplicity counting rather than `Multiset.map_injective`. -/
theorem redteam_perm_of_perm_map_encRec {l l' : List (ComputeTable.MemRec K)}
    (h : (l.map NockVM.encRec).Perm (l'.map NockVM.encRec)) : l.Perm l' := by
  classical
  refine List.perm_iff_count.mpr (fun r => ?_)
  have hc := h.count_eq (NockVM.encRec r)
  rwa [List.count_map_of_injective l NockVM.encRec redteam_encRec_injective,
    List.count_map_of_injective l' NockVM.encRec redteam_encRec_injective] at hc

/-- The `.active` record kind is *exactly* the two axis-lookup states, so the `iff`'s case split is
exhaustive and the read half really is the whole of the other side. -/
theorem memoryMemRecKind_active_iff (s : MemoryTable.MState) :
    memoryMemRecKind s = FPSlotKind.active
      ↔ (s = MemoryTable.MState.read_root ∨ s = MemoryTable.MState.verify_child) := by
  cases s <;> simp [memoryMemRecKind]

end Generic

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## §A. Carrier option (b) is uninhabitable — the decisive negative

`InterChainChallengeFamily E := ∀ inp : MemoryTable.Inputs K, InterChain inp 0 0 (memoryPubRows …)`.
`ipre`/`icur` are **fixed `K` columns of the committed rows**, while the per-row step
`icur − ipre = ±(RLC^γ(mem) − β)⁻¹` moves with the challenge.
Quantifying the *same* committed columns over *all* challenges therefore over-determines them.
The two field-generic ingredients are `interV_not_universal` and `interChain_mem_interV` (§0). -/

/-- **FINDING against carrier option (b).**  On any execution carrying a single `read_root` or
`verify_child` memory row, the proposed `InterChainChallengeFamily` field is **false**.  It is not a
strengthening of the accumulator that `E` already derives — it is an over-determination of the
committed `intermediate` column. -/
theorem interChainChallengeFamily_false_of_live_row
    (E : BuildableNockExecution F K)
    (hlive : ∃ p ∈ GenericHonestData.memoryPubRows E.exec,
      p.st = MemoryTable.MState.read_root ∨ p.st = MemoryTable.MState.verify_child) :
    ¬ InterChainChallengeFamily E := by
  intro h
  obtain ⟨p, hp, hst⟩ := hlive
  refine interV_not_universal hst (fun inp => ?_)
  exact interChain_mem_interV inp (GenericHonestData.memoryPubRows E.exec) 0 0 (h inp) p hp

/-- A nonempty add column exhibits a `read_root` row among the accumulator's `Pub` rows. -/
theorem read_root_row_of_added_ne_nil {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (hne : RowLayout.addedRecordList exec ≠ []) :
    ∃ p ∈ GenericHonestData.memoryPubRows exec, p.st = MemoryTable.MState.read_root := by
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨row, hrow, hresp⟩ := List.mem_flatMap.mp hr
  refine ⟨row.2.2, List.mem_map.mpr ⟨row, hrow, rfl⟩, ?_⟩
  cases hs : row.2.2.st with
  | decompose => simp [MemoryTable.responseRecords, hs] at hresp
  | halt => simp [MemoryTable.responseRecords, hs] at hresp
  | read_root => rfl
  | verify_child => simp [MemoryTable.responseRecords, hs] at hresp

/-- A nonempty remove column exhibits a `verify_child` row among the accumulator's `Pub` rows. -/
theorem verify_child_row_of_consumed_ne_nil {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (hne : RowLayout.consumedRecordList exec ≠ []) :
    ∃ p ∈ GenericHonestData.memoryPubRows exec, p.st = MemoryTable.MState.verify_child := by
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨row, hrow, hcons⟩ := List.mem_flatMap.mp hr
  refine ⟨row.2.2, List.mem_map.mpr ⟨row, hrow, rfl⟩, ?_⟩
  cases hs : row.2.2.st with
  | decompose => simp [RowLayout.consumedRecords, hs] at hcons
  | halt => simp [RowLayout.consumedRecords, hs] at hcons
  | read_root => simp [RowLayout.consumedRecords, hs] at hcons
  | verify_child => rfl

/-- **Carrier option (b) forces both record columns empty.**  So the field cannot hold on any
execution that performs an axis lookup at all. -/
theorem interChainChallengeFamily_forces_empty_columns (E : BuildableNockExecution F K)
    (h : InterChainChallengeFamily E) :
    RowLayout.addedRecordList E.exec = [] ∧ RowLayout.consumedRecordList E.exec = [] := by
  have hadd : RowLayout.addedRecordList E.exec = [] := by
    by_contra hne
    obtain ⟨p, hp, hst⟩ := read_root_row_of_added_ne_nil E.exec hne
    exact interChainChallengeFamily_false_of_live_row E ⟨p, hp, Or.inl hst⟩ h
  refine ⟨hadd, ?_⟩
  by_contra hne
  obtain ⟨p, hp, hst⟩ := verify_child_row_of_consumed_ne_nil E.exec hne
  exact interChainChallengeFamily_false_of_live_row E ⟨p, hp, Or.inr hst⟩ h

/-- Carrier option (b) does imply `PairedRecordLayout` — but only by
forcing both columns empty, i.e. only on executions where the premise is already free.  Adding it
as a `BuildableNockExecution` field would therefore make every axis-lookup execution fall outside
the carrier, and no J.0.3 non-vacuity witness can exist for it. -/
theorem interChainChallengeFamily_only_where_the_premise_is_free
    (E : BuildableNockExecution F K) (h : InterChainChallengeFamily E) :
    RowLayout.PairedRecordLayout E.exec := by
  obtain ⟨hadd, hcons⟩ := interChainChallengeFamily_forces_empty_columns E h
  rw [RowLayout.PairedRecordLayout, hadd, hcons]

/-- Named so the ledger cannot read it as partial progress. -/
theorem mass_balanced_at_every_offset_of_family_has_a_false_hypothesis
    (E : BuildableNockExecution F K)
    (hlive : ∃ p ∈ GenericHonestData.memoryPubRows E.exec,
      p.st = MemoryTable.MState.read_root ∨ p.st = MemoryTable.MState.verify_child) :
    ¬ InterChainChallengeFamily E :=
  interChainChallengeFamily_false_of_live_row E hlive

/-! ### The repaired option-(b) shape, and the bound it would actually need

That shape is
consistent (it is implied by the premise).  What it is missing is the many-points-to-formal step,
and the bound available on `E` is a **characteristic** bound, not a **field-size** bound. -/

/-- The repaired shape: equal record-level LogUp mass at every challenge tuple. -/
def MassBalancedAtEveryOffset (E : BuildableNockExecution F K) : Prop :=
  ∀ inp : MemoryTable.Inputs K,
    ((RowLayout.addedRecordList E.exec).map
        (fun r => (MemoryTable.pole inp r)⁻¹)).sum
      = ((RowLayout.consumedRecordList E.exec).map
          (fun r => (MemoryTable.pole inp r)⁻¹)).sum

/-- **The repaired shape is consistent** — unlike `InterChainChallengeFamily`, it is implied by the
premise, so it is inhabited wherever the premise is.  It is therefore the honest name for what a
challenge-indexed carrier would supply; the open direction is the converse. -/
theorem massBalancedAtEveryOffset_of_pairedRecordLayout (E : BuildableNockExecution F K)
    (h : RowLayout.PairedRecordLayout E.exec) : MassBalancedAtEveryOffset E := by
  intro inp
  exact ((h.map (fun r => (MemoryTable.pole inp r)⁻¹)).sum_eq).symm

/-- **`E.Ksz_lt_ringChar` is not the bound the missing step needs.**  Going from "the difference of
the two log-derivative sums vanishes at every non-pole point of `K`" to "it vanishes formally"
is an interpolation whose hypothesis is a **field-size** bound (`4·Ksz ≤ |K|`, from a numerator of
degree `≤ 2·Ksz − 1` against `|K| − 2·Ksz` available points), whereas `E` carries only
`Ksz < ringChar K`.  The two are genuinely different: here is a field and a `Ksz` satisfying the
characteristic bound and violating the size bound.  So the closeout's parenthetical "degree bound
available from `E.Ksz_lt_ringChar`" is **not established**. -/
theorem characteristic_bound_is_not_the_field_size_bound :
    (4 : ℕ) < ringChar (ZMod 5) ∧ Fintype.card (ZMod 5) < 4 * 4 := by
  refine ⟨?_, ?_⟩
  · rw [ZMod.ringChar_zmod_n]; norm_num
  · rw [ZMod.card]; norm_num

/-! ### The same negative at the F97 fixture field, so it is not an artifact of a generic `K` -/

namespace Concrete

def liveRow : MemoryTable.Pub F97 :=
  { st := .read_root
    pt := ⟨⟨1, 0, 0⟩, 0, 0⟩
    lc := ⟨⟨1, 0, 0⟩, 0, 0⟩
    rc := MemoryTable.Cell.zero
    lcSt := .read_root
    rcSt := .halt
    mem := PairedRecordIOResult.Concrete.rootA
    ipre := 0
    icur := 3 }

/-- **Compiled at the fixture:** this honest-shaped `read_root` row's accumulator step fails at some
challenge tuple, so no committed row can satisfy the option-(b) family. -/
theorem liveRow_interV_not_universal :
    ¬ (∀ inp : MemoryTable.Inputs F97, MemoryTable.interV inp liveRow) :=
  interV_not_universal (Or.inl rfl)

end Concrete

/-! ## §B. Carrier option (a) — the layer the repo and the paper actually use

the paper licenses treating `intermediate` "in the exact same way as in `RAP_mem-IO`,
`RAP_comp-IO`".  So the question is what *this repo* does with those two columns.  Answer: the
matching is carried and derived at the **record level**, and the formal `RatFunc (RatFunc K)` tower
appears only in the *characterisation theorem* `IO.io_result_LIO` (an `iff`, never a hypothesis on a
production execution) and in the oracle-agreement regression against the finite-field path. -/

/-- **What `E` carries for the external IO columns: the record-level language.**  `IO.LIO` on the
execution-derived request/response record lists, unconditionally on `E`.  This is the object
the paper tells us to reuse for `intermediate` — not a rational-function accumulator. -/
theorem external_io_matching_is_record_level_on_E (E : BuildableNockExecution F K) :
    IO.LIO E.cfg.Ksz E.exec.derivedRequestIO E.exec.derivedResponseIO :=
  GenericHonestData.execution_lio_of_requestNodup E

/-- **…and the `intermediate` analogue of that very object is the named premise.**  A carrier field of option-(a) shape, being at least this
strong, is therefore a rename. -/
theorem symbolicInterLDSE_iff_pairedRecordLayout (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent) :
    SymbolicInterLDSE E ↔ RowLayout.PairedRecordLayout E.exec :=
  (symbolicInterLDSE_iff_symbolicInterMSE E hhon hC).trans
    (pairedRecordLayout_iff_symbolicInterMSE E)

/-- The record-level `L_IO` membership of the encoded `(intermediate, IO)` column pair **is** the
premise, with its two side conditions already on `E`.  Independently re-derived here from the two
already-held facts rather than cited. -/
theorem intermediate_matching_at_the_record_level_is_the_premise
    (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent) :
    IO.LIO E.cfg.Ksz ((RowLayout.consumedRecordList E.exec).map NockVM.encRec)
        ((RowLayout.addedRecordList E.exec).map NockVM.encRec)
      ↔ RowLayout.PairedRecordLayout E.exec := by
  constructor
  · intro h
    exact perm_of_perm_map_encRec h.2.2
  · intro h
    refine ⟨?_, ?_, h.map NockVM.encRec⟩
    · rw [List.length_map]
      exact added_length_inRange E hhon hC
    · have hnd := Batch131.encoded_addedRecordList_nodup E hhon hC
      have hinjC :
          Function.Injective (fun r => NockVM.encRecC (K := K) r (E.exec.cprimeOf r)) := by
        intro r s hrs
        have h0 : r.root.size = s.root.size := congrFun hrs 0
        have h1 : r.root.dyck = s.root.dyck := congrFun hrs 1
        have h2 : r.root.leaf = s.root.leaf := congrFun hrs 2
        have h3 : r.child.size = s.child.size := congrFun hrs 3
        have h4 : r.child.dyck = s.child.dyck := congrFun hrs 4
        have h5 : r.child.leaf = s.child.leaf := congrFun hrs 5
        have h6 : r.axis = s.axis := congrFun hrs 6
        have h7 : r.ts = s.ts := congrFun hrs 7
        exact ComputeTable.MemRec.ext (ComputeTable.FP.ext h0 h1 h2)
          (ComputeTable.FP.ext h3 h4 h5) h6 h7
      have hsrc := (List.nodup_map_iff hinjC).mp hnd
      exact (List.nodup_map_iff redteam_encRec_injective).mpr hsrc

/-! ## §C. The two iffs, independently re-derived

Here it is re-obtained from
multiplicity counting (`List.perm_iff_count`), a genuinely different argument, so the `iff` is not
believed on one route only.  The un-encoding ingredients are in §0. -/

/-- Same statement, un-encoding by
counting.  Both directions check out, and they are not swapped: `IO.SEcond`'s first argument is the
remove column and `PairedRecordLayout` is `consumedRecordList.Perm addedRecordList`. -/
theorem redteam_pairedRecordLayout_iff_symbolicInterMSE (E : BuildableNockExecution F K) :
    SymbolicInterMSE E ↔ RowLayout.PairedRecordLayout E.exec := by
  rw [SymbolicInterMSE, IO.SEcond_iff]
  constructor
  · intro h
    exact redteam_perm_of_perm_map_encRec (Multiset.coe_eq_coe.mp h)
  · intro h
    exact Multiset.coe_eq_coe.mpr (h.map NockVM.encRec)

/-- The LDSE form closes the premise; re-derived through the independent `iff`. -/
theorem redteam_pairedRecordLayout_of_symbolicInterLDSE (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (h : SymbolicInterLDSE E) : RowLayout.PairedRecordLayout E.exec :=
  (redteam_pairedRecordLayout_iff_symbolicInterMSE E).mp
    ((symbolicInterLDSE_iff_symbolicInterMSE E hhon hC).mp h)

/-- **`SymbolicInterMSE` is not a `True`-like predicate.**  Its underlying `IO.SEcond` genuinely
fails on a concrete unmatched pair at the fixture field, so the `iff` above is not an equivalence
of two trivially-true propositions. -/
theorem symbolicInterMSE_predicate_discriminates :
    ¬ IO.SEcond (𝔽 := F97) (M := 9)
        [NockVM.encRec PairedRecordIOResult.Concrete.rootA]
        [NockVM.encRec PairedRecordIOResult.Concrete.rootB] := by
  intro h
  rw [IO.SEcond_iff] at h
  have hs : NockVM.encRec (K := F97) PairedRecordIOResult.Concrete.rootA
      = NockVM.encRec PairedRecordIOResult.Concrete.rootB := by
    simpa using h
  exact (PairedRecordIOResult.Concrete.timestampKeyedColumns_is_about_mem_root).2.1
    (redteam_encRec_injective hs)

/-! ## §D. Route 2 — the circularity claim, independently re-derived

It
does, and the read half really is free on `E`; both are re-derived here from the `Service` layer
rather than cited. -/

/-- Independent re-derivation: every record added to `intermediate` has a closed timestamp,
unconditionally on `E`, via `RootTrace.recordPartition` and `Service.timestamp`. -/
theorem redteam_added_timestamp_closed (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    ∀ s ∈ RowLayout.addedRecordList E.exec,
      MemoryTimestampClosedAt E.cfg.challenges.α s.ts := by
  intro s hs
  obtain ⟨sA, hsA, hts⟩ := GenericHonestData.exec_added_ts_of_execA hs
  obtain ⟨sv, hsv⟩ := GenericHonestPackage.service_record_of_added hhon hsA
  exact ⟨sv.exponent, by rw [hts, hsv]; exact sv.timestamp⟩

/-- **The circularity, re-derived.**  `VerifyReindexingRecovery` — the whole content of Route 2's
verify half — implies the named premise's conclusion `timestampClosed` with no record matching
anywhere in the derivation.  So Route 2 cannot be a route *to* `PairedRecordLayout` *in order to
reach* `timestampClosed`. -/
theorem redteam_timestampClosed_of_verifyReindexingRecovery (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (h : VerifyReindexingRecovery E) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt E.cfg.challenges.α
          (E.exec.memoryRowAt i).2.2.mem.ts := by
  intro i hact
  cases hst : (E.exec.memoryRowAt i).1 with
  | decompose => simp [memoryMemRecKind, hst] at hact
  | halt => simp [memoryMemRecKind, hst] at hact
  | read_root =>
      exact redteam_added_timestamp_closed E hhon
        (E.exec.memoryRowAt i).2.2.mem
        (GenericHonestPackage.read_root_mem_in_addedRecordList E i hst)
  | verify_child =>
      exact (GenericHonestData.timestampExp_recovers_ts_iff_closed _ _).mp
        (h _ (GenericHonestPackage.verify_child_mem_in_consumedRecordList E i hst))

/-- And the recovery step is *equivalent* to closure on the remove column, so the circularity is
not an artifact of a lossy implication. -/
theorem redteam_verifyReindexingRecovery_iff_consumed_closed (E : BuildableNockExecution F K) :
    VerifyReindexingRecovery E ↔
      ∀ r ∈ RowLayout.consumedRecordList E.exec,
        TimestampClosedAt E.cfg.challenges.α r.ts :=
  ⟨fun h r hr => (GenericHonestData.timestampExp_recovers_ts_iff_closed _ _).mp (h r hr),
    fun h r hr => (GenericHonestData.timestampExp_recovers_ts_iff_closed _ _).mpr (h r hr)⟩

/-! ## §E. `timestampClosed_iff_verify_child_half` is a genuine sharpening

The exhaustiveness ingredient is `memoryMemRecKind_active_iff` (§0). -/

/-- **The remaining half is not vacuously true.**  `MemoryTimestampClosedAt` is a real constraint:
at `α = −1` over `F97` the closed timestamps are `{1, −1}`, and `2` is not one of them.  So
`timestampClosed_iff_verify_child_half` sharpens a premise that still has content. -/
theorem memoryTimestampClosedAt_is_not_trivial :
    ¬ MemoryTimestampClosedAt (96 : F97) 2 := by
  rintro ⟨e, he⟩
  have h96 : (96 : F97) = -1 := by decide
  rw [h96] at he
  rcases neg_one_pow_eq_or (R := F97) e with h | h
  · rw [h] at he; revert he; decide
  · rw [h] at he; revert he; decide

/-! ## §F/§G/§H.

For a
*positive* separation claim that makes the witness stronger, not weaker — but it is worth removing
the dependence, which is what this section does: the two timestamp-equal records separate at
**every** `(β, γ)`, degenerate or not. -/

namespace Concrete

/-- **Strengthening of `poles_separate_at_every_offset`: separation at every challenge PAIR.** -/
theorem poles_separate_at_every_challenge_pair :
    ∀ β γ : F97,
      MemoryTable.pole (⟨0, β, γ⟩ : MemoryTable.Inputs F97)
          PairedRecordIOResult.Concrete.rootA
        ≠ MemoryTable.pole (⟨0, β, γ⟩ : MemoryTable.Inputs F97)
            PairedRecordIOResult.Concrete.rootB := by
  intro β γ h
  simp only [MemoryTable.pole, MemoryTable.recRLC,
    PairedRecordIOResult.Concrete.rootA, PairedRecordIOResult.Concrete.rootB] at h
  have h1 : (1 : F97) = 0 := by linear_combination h
  revert h1
  decide

theorem gamma_one_collapses_the_rlc (r : ComputeTable.MemRec F97) :
    MemoryTable.recRLC (1 : F97) r
      = r.root.size + r.root.dyck + r.root.leaf + r.child.size + r.child.dyck + r.child.leaf
          + r.axis + r.ts := by
  simp only [MemoryTable.recRLC, one_pow, one_mul, mul_zero, add_zero]

end Concrete

/-! ## §I. Accounting — nothing inhabited, nothing added -/

theorem execution_eta_still_fourteen_fields_batch132 (E : BuildableNockExecution F K) :
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

/-- `MemoryRecordPremises` still has its two fields; `timestampClosed` is still named. -/
theorem memoryRecordPremises_still_two_batch132
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
      (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) :=
  GenericHonestData.memoryRecordPremises_still_two_after_logup_inventory M

/-- The `11+1+2` partition of the released capstone statement is unchanged. -/
theorem exact_eleven_one_two_batch132 : 11 + 1 + 2 = 14 :=
  GenericHonestPackage.residual_pair_still_eleven_one_two_after_logup_inventory


#print axioms interV_not_universal
#print axioms interChain_mem_interV
#print axioms interChainChallengeFamily_false_of_live_row
#print axioms read_root_row_of_added_ne_nil
#print axioms verify_child_row_of_consumed_ne_nil
#print axioms interChainChallengeFamily_forces_empty_columns
#print axioms interChainChallengeFamily_only_where_the_premise_is_free
#print axioms mass_balanced_at_every_offset_of_family_has_a_false_hypothesis
#print axioms massBalancedAtEveryOffset_of_pairedRecordLayout
#print axioms characteristic_bound_is_not_the_field_size_bound
#print axioms Concrete.liveRow_interV_not_universal
#print axioms external_io_matching_is_record_level_on_E
#print axioms symbolicInterLDSE_iff_pairedRecordLayout
#print axioms intermediate_matching_at_the_record_level_is_the_premise
#print axioms redteam_encRec_injective
#print axioms encRec_reads_back_every_field
#print axioms redteam_perm_of_perm_map_encRec
#print axioms redteam_pairedRecordLayout_iff_symbolicInterMSE
#print axioms redteam_pairedRecordLayout_of_symbolicInterLDSE
#print axioms symbolicInterMSE_predicate_discriminates
#print axioms redteam_added_timestamp_closed
#print axioms redteam_timestampClosed_of_verifyReindexingRecovery
#print axioms redteam_verifyReindexingRecovery_iff_consumed_closed
#print axioms memoryMemRecKind_active_iff
#print axioms memoryTimestampClosedAt_is_not_trivial
#print axioms Concrete.poles_separate_at_every_challenge_pair
#print axioms Concrete.gamma_one_collapses_the_rlc
#print axioms execution_eta_still_fourteen_fields_batch132
#print axioms memoryRecordPremises_still_two_batch132
#print axioms exact_eleven_one_two_batch132

end

end Nock.RedTeam.Batch132
