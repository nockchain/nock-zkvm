/-
  Nock/NockVMROM/Thm54/TraceGen/GenServedCoverage.lean

  **`semanticCoverage` reduced from eleven states to two.**

  `ExactServedMemoryTrace.semanticCoverage` (`ServedMemoryTrace.lean:616`) asks, for every compute
  row and every served lookup that row carries, for a `Service` in the forest partition with the
  same record, root, child and axis.  Stated that way it quantifies over an existentially built
  list inside `buildCoveredRow` and there is nothing to case on.

  `ofSkeleton_servedTuples` (`BoundSemanticTrace.lean`) turns that list into `servedTuplesOf`, which
  is a three-way `if` on the row's state: a singleton at `.s9`, a singleton at `.s0`, and `[]` at
  the other nine.  So the whole obligation collapses to **two explicit tuples**, each written out of
  the skeleton's own projections:

  * `.s0` — `(computeMemRec pub 1, s.subject, skeletonMemoryAxis s 1, s.evaluation)`;
  * `.s9` — `(computeMemRec pub 2, skeletonSubformula s 0.result, skeletonMemoryAxis s 2,
    skeletonSubformula s 1.formula)`.

  That is what this module proves.  It supplies no `Service`: the two-state obligation is the
  interface the supply is written against, and it is deliberately stated over an arbitrary
  `roots` family so that the supply and the reduction can be built independently.

  **Scope.**  Everything here is at `ofSkeleton`, hence at any skeleton, config and execution — not
  at a generated trace and not at a configuration.  The corollary at the bottom instantiates it at
  `genSemanticData`'s rows, where the skeleton is the generator's.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticData
import Nock.NockVMROM.Thm54.ServedMemoryTrace

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.BoundSemanticTrace
open Nock.NockVMROM.Thm54.SemanticStrategy

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## The two-state supply obligation -/

/-- **The `Service` supply obligation, as `semanticCoverage` actually needs it.**

A tuple-level statement rather than a `ServedNounLookup`-level one: the lookup's two proof fields
(`realization`, `served`) are not what the forest partition has to match, so carrying them into the
obligation would only make it harder to discharge. -/
def ServedSupply {q Λ : ℕ} (S : SemanticSkeleton)
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) {z : K}
    (binds : BindsAt z S cfg exec) {execA : ExactExecution cfg}
    (roots : ∀ i : Fin cfg.kMem, RootTrace cfg execA i) : Prop :=
  ∀ (row : Fin cfg.compRows) (rec : ComputeTable.MemRec K) (rt : Noun) (ax : ℕ) (ch : Noun),
    (rec, rt, ax, ch) ∈
      servedTuplesOf (skeletonRowAt S exec binds row) ((exec.computeRowAt row).2.2.1) →
    ∃ (i : Fin cfg.kMem) (s : Service cfg execA),
      s ∈ (roots i).services ∧ s.record = rec ∧ s.root = rt ∧ s.child = ch ∧ s.axis = ax

/-- **`semanticCoverage` from the tuple-level supply.**

The whole content is `ofSkeleton_servedTuples`: membership in `needs.served` maps forward to
membership in `servedTuplesOf`, and the five conjuncts are the four components plus the root index. -/
theorem semanticCoverage_of_servedSupply [Fintype K] [DecidableEq K]
    {q Λ : ℕ} (S : SemanticSkeleton)
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) {z : K}
    (binds : BindsAt z S cfg exec) {execA : ExactExecution cfg}
    (C : SkeletonP8Census K S Λ)
    (hb : S.BoundedBy q)
    (hcmp : SkeletonComparisonBoundedBy K q S)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (hop : ∀ s ∈ computeSkeletonRows S, SkeletonOperationalPremises q z s)
    (roots : ∀ i : Fin cfg.kMem, RootTrace cfg execA i)
    (hsup : ServedSupply (q := q) (Λ := Λ) S exec binds roots) :
    ∀ row : Fin cfg.compRows,
      ∀ lookup ∈ (SemanticTrace.ComputeRowSemanticData.ofSkeleton
          S exec binds C hb hcmp hgood hop row).needs.served,
        ∃ (i : Fin cfg.kMem) (s : Service cfg execA),
          s ∈ (roots i).services ∧ s.record = lookup.record ∧ s.root = lookup.root ∧
            s.child = lookup.child ∧ s.axis = lookup.axis := by
  intro row lookup hlookup
  have hmem :
      (lookup.record, lookup.root, lookup.axis, lookup.child) ∈
        servedTuplesOf (skeletonRowAt S exec binds row) ((exec.computeRowAt row).2.2.1) := by
    rw [← SemanticTrace.ComputeRowSemanticData.ofSkeleton_servedTuples
      S exec binds C hb hcmp hgood hop row]
    exact List.mem_map.mpr ⟨lookup, hlookup, rfl⟩
  exact hsup row _ _ _ _ hmem

/-! ## The reduction to `.s0` and `.s9`

`servedTuplesOf` is `[]` at the other nine states, so nothing has to be supplied there. -/

/-- **`ServedSupply` from the two states that actually carry a lookup.**

Nine of the eleven states discharge by `List.not_mem_nil`; the two that remain each contribute one
tuple, spelled out of the skeleton's projections. -/
theorem servedSupply_of_states {q Λ : ℕ} (S : SemanticSkeleton)
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) {z : K}
    (binds : BindsAt z S cfg exec) {execA : ExactExecution cfg}
    (roots : ∀ i : Fin cfg.kMem, RootTrace cfg execA i)
    (h0 : ∀ row : Fin cfg.compRows,
      (skeletonRowAt S exec binds row).state = .s0 →
      ∃ (i : Fin cfg.kMem) (s : Service cfg execA),
        s ∈ (roots i).services ∧
          s.record = computeMemRec ((exec.computeRowAt row).2.2.1) 1 ∧
          s.root = (skeletonRowAt S exec binds row).subject ∧
          s.child = (skeletonRowAt S exec binds row).evaluation ∧
          s.axis = P8Census.skeletonMemoryAxis (skeletonRowAt S exec binds row) 1)
    (h9 : ∀ row : Fin cfg.compRows,
      (skeletonRowAt S exec binds row).state = .s9 →
      ∃ (i : Fin cfg.kMem) (s : Service cfg execA),
        s ∈ (roots i).services ∧
          s.record = computeMemRec ((exec.computeRowAt row).2.2.1) 2 ∧
          s.root = P8Census.skeletonSubformula (skeletonRowAt S exec binds row) 0 .result ∧
          s.child = P8Census.skeletonSubformula (skeletonRowAt S exec binds row) 1 .formula ∧
          s.axis = P8Census.skeletonMemoryAxis (skeletonRowAt S exec binds row) 2) :
    ServedSupply (q := q) (Λ := Λ) S exec binds roots := by
  intro row rec rt ax ch hmem
  unfold servedTuplesOf at hmem
  by_cases hs9 : (skeletonRowAt S exec binds row).state = .s9
  · rw [if_pos hs9] at hmem
    simp only [List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨hrec, hrt, hax, hch⟩ := hmem
    obtain ⟨i, s, hsm, hsrec, hsrt, hsch, hsax⟩ := h9 row hs9
    exact ⟨i, s, hsm, hsrec.trans hrec.symm, hsrt.trans hrt.symm,
      hsch.trans hch.symm, hsax.trans hax.symm⟩
  · rw [if_neg hs9] at hmem
    by_cases hs0 : (skeletonRowAt S exec binds row).state = .s0
    · rw [if_pos hs0] at hmem
      simp only [List.mem_singleton, Prod.mk.injEq] at hmem
      obtain ⟨hrec, hrt, hax, hch⟩ := hmem
      obtain ⟨i, s, hsm, hsrec, hsrt, hsch, hsax⟩ := h0 row hs0
      exact ⟨i, s, hsm, hsrec.trans hrec.symm, hsrt.trans hrt.symm,
        hsch.trans hch.symm, hsax.trans hax.symm⟩
    · rw [if_neg hs0] at hmem
      simp at hmem

/-- **The nine vacuous states, as a usable statement.**

Not needed by `servedSupply_of_states`, which case-splits internally, but it is the fact a caller
reaches for when discharging `h0`/`h9` at a configuration whose rows are known: outside `.s0` and
`.s9` there is no lookup at all. -/
theorem served_nil_of_state [Fintype K] [DecidableEq K]
    {q Λ : ℕ} (S : SemanticSkeleton)
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) {z : K}
    (binds : BindsAt z S cfg exec)
    (C : SkeletonP8Census K S Λ)
    (hb : S.BoundedBy q)
    (hcmp : SkeletonComparisonBoundedBy K q S)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (hop : ∀ s ∈ computeSkeletonRows S, SkeletonOperationalPremises q z s)
    (row : Fin cfg.compRows)
    (h0 : (skeletonRowAt S exec binds row).state ≠ .s0)
    (h9 : (skeletonRowAt S exec binds row).state ≠ .s9) :
    (SemanticTrace.ComputeRowSemanticData.ofSkeleton
      S exec binds C hb hcmp hgood hop row).needs.served = [] := by
  have hmap := SemanticTrace.ComputeRowSemanticData.ofSkeleton_servedTuples
    S exec binds C hb hcmp hgood hop row
  have hnil : servedTuplesOf (skeletonRowAt S exec binds row)
      ((exec.computeRowAt row).2.2.1) = [] := by
    unfold servedTuplesOf
    rw [if_neg h9, if_neg h0]
  have hlen := congrArg List.length (hmap.trans hnil)
  rw [List.length_map, List.length_nil] at hlen
  exact List.eq_nil_of_length_eq_zero hlen

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.semanticCoverage_of_servedSupply
#print axioms Nock.NockVMROM.Thm54.TraceGen.servedSupply_of_states
#print axioms Nock.NockVMROM.Thm54.TraceGen.served_nil_of_state
