import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.ServedLookupBridge
import Nock.RedTeam.Batch136Thm54CensusExtras

/-!

Different
context from the architect. **Nothing here inhabits a named premise, adds a carrier field, weakens
a census predicate, or ticks a `§J` box.**  `BuildableNockExecution` keeps its fourteen fields and
`CensusRecordPremises` its five.

Two things are settled, both by compiled artifacts rather than by reading hypotheses.

## §A. `C2`'s non-carrier route IS blocked — but not by the recorded mechanism

That reading is **read off hypotheses and is not the
operative obstruction**, for two compiled reasons.

1. `GlobalCarryRecognizer.sepSeed_bad_card_le` is a **cardinality** statement about the bad-seed
   filter. So even if `C2` supplied the leaf bound, that route to
   `FPRealizationWitness.unique` would still not be available at a fixed seed. This does not weaken
   the case for `C2`; it corrects the reason.
2. The operative obstruction is plain non-injectivity of `GlobalCarryRecognizer.enc z` on
   `BoundedBy q` nouns, and it survives at a **non-degenerate** seed. So the two facts
   `CensusExtraClosure.reconstructed_subformulaNoun_properties` records about a `chooseNoun` witness
   do not determine its leaf count, at any `Λ`, even away from `orderOf z = 1`.

The residual missing object is therefore a size window on the **chosen** noun,
which is strictly weaker than the `n.leaves ≤ Λ` conjunct `C2` proposes — but it is seed-dependent,
where the paper's `NockProgram^Λ` is seed-free, so `C2`'s
shape remains the faithful one. Recorded so the alternative is not rediscovered.

## §B. `sizeWindowBound` and `slotSemantics` need no carrier at any state-eligible execution

This is the constructive half, and it moves the ranking.

`SizeWindowCounting.requiredSizeWindowNouns` is `[]` off `{.s3, .s4, .s6}`, and both clauses of
`ServedLookupBridge.SkeletonSlotSemantics` are gated on `{.s0, .s9}`.  The reconstructed skeleton
row `(computeNodeAt E P i).skel` takes its `state` field from `(E.exec.computeRowAt i).1` by
`rfl`.  Hence, with **no carrier field and no type index**:

What
they do settle is that `C2`'s claimed leverage of **two** premises is not realised at any live
fixture: at all three live fixtures `sizeWindowBound` is free, and `C2` buys `census` alone.

## §C. Overlap B holds at OP0 and is gated at OP9

That second input is the OP0 clause of `AxisAtomPremises` *with its witness pinned to the
certificate's own `axis`* — so at OP0 one object really does serve both premises, which is
Overlap B as claimed.

At OP9 it does not go through the same way, and the reason is `§A`'s. The premise's OP9 clause is
stated on `P8Census.skeletonSubformula s 0 .result` and `… s 1 .formula`, which on the
reconstruction are `subformulaNoun` — `Classical.choose` witnesses — whereas
`LocalOpcodeCertificate.s9.hserved` is stated on the certificate's own `call1.result` and
`call2.formula`. So
Overlap B is **half measured, half conditional**, and its conditional half rests on the same
uniqueness object as `C2`.

Nothing here is a verdict on the paper construction, which is not in question at any point.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch137

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.HonestCommitment

noncomputable section

/-! ## §A. The `C2` non-carrier route, compiled -/

/-- A three-leaf noun with every leaf `0`. -/
def threeLeaf : Noun := .cell (.cell (.atom 0) (.atom 0)) (.atom 0)

theorem threeLeaf_leaves : threeLeaf.leaves = 3 := by
  simp [threeLeaf, Noun.leaves]

theorem threeLeaf_bounded : FieldEmbedding.BoundedBy 1 threeLeaf := by
  simp [threeLeaf]

/-- **The collision.**  At `z = -1` the three-leaf all-zero noun and the one-leaf atom have the
same global-carry encoding, in every field.  `enc` is computed through the production
`enc_cons` homomorphism, not by unfolding `NPR.listPoly`. -/

theorem redteam_enc_neg_one_collision {K : Type*} [Field K] :
    GlobalCarryRecognizer.enc (-1 : K) threeLeaf =
      GlobalCarryRecognizer.enc (-1 : K) (.atom 0) := by
  have hz : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have h0 : GlobalCarryRecognizer.enc (-1 : K) (.atom 0) =
      ⟨(-1 : K), 0, 0⟩ := by
    refine ComputeTable.FP.ext ?_ ?_ ?_
    · simp [GlobalCarryRecognizer.enc, Noun.leaves]
    · simp [GlobalCarryRecognizer.enc, NPR.dyckBits, Noun.dyckWord, Noun.shape,
        Nock.BTree.encode, NPR.listPoly, NPR.cpoly]
    · simp [GlobalCarryRecognizer.enc, NPR.leafF, Noun.leafList, NPR.listPoly, NPR.cpoly]
  have hinner : GlobalCarryRecognizer.enc (-1 : K) (.cell (.atom 0) (.atom 0)) =
      ⟨(1 : K), -1, 0⟩ := by
    rw [GlobalCarryRecognizer.enc_cons hz, h0]
    refine ComputeTable.FP.ext ?_ ?_ ?_
    · simp [ComputeTable.FP.cons]
    · simp [ComputeTable.FP.cons]
    · simp [ComputeTable.FP.cons]
  have h3 : GlobalCarryRecognizer.enc (-1 : K) threeLeaf =
      ⟨(-1 : K), 0, 0⟩ := by
    rw [threeLeaf, GlobalCarryRecognizer.enc_cons hz, hinner, h0]
    refine ComputeTable.FP.ext ?_ ?_ ?_
    · simp [ComputeTable.FP.cons]
    · simp [ComputeTable.FP.cons]
    · simp [ComputeTable.FP.cons]
  rw [h3, h0]

/-- `orderOf (-1)` is `2` away from characteristic two, so the collision above is **not** placed
at a degenerate seed: it survives `Λ < orderOf z`. -/
theorem redteam_one_lt_orderOf_neg_one {K : Type*} [Field K] (h2 : (1 : K) ≠ -1) :
    1 < orderOf (-1 : K) := by
  have hpow : (-1 : K) ^ 2 = 1 := by ring
  have hd : orderOf (-1 : K) ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
  have hle : orderOf (-1 : K) ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  have hne0 : orderOf (-1 : K) ≠ 0 := by
    intro h
    rw [h] at hd
    exact absurd (Nat.eq_zero_of_zero_dvd hd) (by norm_num)
  have hne1 : orderOf (-1 : K) ≠ 1 := by
    rw [Ne, orderOf_eq_one_iff]
    intro h
    exact h2 h.symm
  omega

/-- **`C2`'s non-carrier route is blocked, at a non-degenerate seed.**

The two facts `CensusExtraClosure.reconstructed_subformulaNoun_properties` records about a
reconstructed `subformulaNoun` — an atom range and an encoding equation — do not determine its leaf
count, even when a `Λ`-leaf noun realizes the same fingerprint and `Λ < orderOf z`.  So no theorem
of the shape "`BoundedBy q n` and `enc z n = enc z real` and `real.leaves ≤ Λ` imply
`n.leaves ≤ Λ`" exists, and `chooseNoun` cannot be shown to return the real noun from what is
recorded about it.  This is a statement about the recorded facts, not about the paper's
`NockProgram^Λ`, which is exactly the object `C2` restores. -/

theorem redteam_c2_noncarrier_route_blocked {K : Type*} [Field K] (h2 : (1 : K) ≠ -1) :
    ∃ (z : K) (q Λ : ℕ) (real chosen : Noun),
      z ≠ 0 ∧ Λ < orderOf z ∧
        FieldEmbedding.BoundedBy q real ∧ real.leaves ≤ Λ ∧
          FieldEmbedding.BoundedBy q chosen ∧
            GlobalCarryRecognizer.enc z chosen = GlobalCarryRecognizer.enc z real ∧
              ¬ chosen.leaves ≤ Λ := by
  refine ⟨-1, 1, 1, .atom 0, threeLeaf, neg_ne_zero.mpr one_ne_zero,
    redteam_one_lt_orderOf_neg_one h2, by simp, by simp [Noun.leaves],
    threeLeaf_bounded, redteam_enc_neg_one_collision, ?_⟩
  rw [threeLeaf_leaves]
  omega

/-- **What the encoding does determine.**  `enc`'s `size` coordinate is `z ^ n.leaves`, so equal
encodings pin the two leaf counts modulo `orderOf z`, hence equal as soon as both sit below it.

The residual object needed to close `C2` without the paper's `Λ` is therefore a size window on the
*chosen* noun, not a `Λ`-leaf bound.  It is strictly weaker, but seed-dependent, so it is recorded
as an alternative and not as a recommendation. -/

theorem redteam_leaves_eq_of_enc_eq_of_windows {K : Type*} [Field K] {z : K} {m n : Noun}
    (h : GlobalCarryRecognizer.enc z m = GlobalCarryRecognizer.enc z n)
    (hm : m.leaves < orderOf z) (hn : n.leaves < orderOf z) :
    m.leaves = n.leaves := by
  have hsize : z ^ m.leaves = z ^ n.leaves := congrArg ComputeTable.FP.size h
  have hpos : 0 < orderOf z := Nat.lt_of_le_of_lt (Nat.zero_le _) hm
  have hone : z ^ orderOf z = 1 := pow_orderOf_eq_one z
  have hz : z ≠ 0 := by
    intro h0
    rw [h0] at hone hpos
    rw [zero_pow hpos.ne'] at hone
    exact zero_ne_one hone
  have key : ∀ a b : ℕ, a ≤ b → b < orderOf z → z ^ a = z ^ b → a = b := by
    intro a b hab hb heq
    have hzp : z ^ a ≠ 0 := pow_ne_zero _ hz
    have hmul : z ^ a * z ^ (b - a) = z ^ a * 1 := by
      rw [mul_one, ← pow_add, Nat.add_sub_cancel' hab]
      exact heq.symm
    have hsub : z ^ (b - a) = 1 := mul_left_cancel₀ hzp hmul
    have hdvd : orderOf z ∣ (b - a) := orderOf_dvd_of_pow_eq_one hsub
    rcases Nat.eq_zero_or_pos (b - a) with h0 | hp
    · omega
    · have := Nat.le_of_dvd hp hdvd
      omega
  rcases le_total m.leaves n.leaves with hle | hle
  · exact key _ _ hle hn hsize
  · exact (key _ _ hle hm hsize.symm).symm

/-- **The recorded blocker is misidentified, and here is why it matters.**  Both nouns of the
collision are bounded by three leaves — the hypotheses `sepSeed_bad_card_le` takes — and the seed is
still not separating.  A leaf bound is a *counting* input to the bad-seed cardinality, never a
producer of `SepSeed` at a fixed seed, so supplying `C2`'s bound would not by itself unlock
`FPRealizationWitness.unique`.  `C2` remains the right object; it works by supplying the leaf count
directly, not by unblocking uniqueness. -/

theorem redteam_leaf_bounds_do_not_give_sepSeed {K : Type*} [Field K] :
    threeLeaf.leaves ≤ 3 ∧ (Noun.atom 0).leaves ≤ 3 ∧
      ¬ GlobalCarryRecognizer.SepSeed (-1 : K) threeLeaf (.atom 0) := by
  refine ⟨by rw [threeLeaf_leaves], by simp [Noun.leaves], ?_⟩
  intro hsep
  refine hsep ?_ (GlobalCarryRecognizer.enc_eq_imp_fn_eq _ _ _ redteam_enc_neg_one_collision)
  intro hpair
  have hlen := congrArg (fun p => p.1.length) hpair
  simp only [NPR.leafF_length, threeLeaf_leaves, Noun.leaves] at hlen
  omega

/-! ## §B. `sizeWindowBound` and `slotSemantics` on the reconstruction, with no carrier -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The reconstructed compute-row skeleton takes its state from the execution's own row, by `rfl`.
This is the whole mechanism of §B. -/

theorem redteam_reconstructed_row_state (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (i : Fin E.cfg.compRows) :
    ((computeNodeAt E P i).skel).state = (E.exec.computeRowAt i).1 := rfl

/-- Every reconstructed compute-row skeleton is `(computeNodeAt E P i).skel` for some `i`. -/

theorem redteam_reconstructed_rows_are_nodes (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    {s : ComputeRowSkeleton}
    (hs : s ∈ computeSkeletonRows
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M))) :
    ∃ i : Fin E.cfg.compRows, s = (computeNodeAt E P i).skel := by
  rw [computeSkeletonRows_of_assembly E P M] at hs
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hs
  rw [List.mem_range'] at hj
  obtain ⟨k, hk, rfl⟩ := hj
  simp only [Nat.one_mul]
  have hidx : k < E.cfg.compRows := by
    rw [← E.exec.compute_bfs_length]
    exact hk
  refine ⟨⟨k, hidx⟩, ?_⟩
  have h1 : (1 + k) - 1 = k := Nat.add_sub_cancel_left 1 k
  simpa [h1] using
    congrArg ComputeNode.skel
      (computeLabelAt_of_index E P (i := 1 + k) (by simpa [h1] using hidx))

/-- **`sizeWindowBound` with no carrier, at any execution avoiding OP3/OP4/OP6.**

`SizeWindowCounting.requiredSizeWindowNouns` emits nothing outside those three states, and the
reconstructed row's state is the execution's own.  No field is added, no type index is changed, and
no `Classical.choose` leaf bound is used.

Cite note: the pair the paper carried by several existing modules for this fact is
defective — `1707` is **blank** and `1712` is the `OP_5` paragraph. The `OP_3` paragraph is
the paper and the `OP_6` one is the paper. -/

theorem redteam_sizeWindowBound_of_no_window_states (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (h : ∀ i : Fin E.cfg.compRows,
      (E.exec.computeRowAt i).1 ≠ .s3 ∧ (E.exec.computeRowAt i).1 ≠ .s4 ∧
        (E.exec.computeRowAt i).1 ≠ .s6) :
    SizeWindowCounting.SizeWindowNounsBoundedBy
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ := by
  intro n hn
  rw [SizeWindowCounting.skeletonSizeWindowNouns, List.mem_flatMap] at hn
  obtain ⟨s, hs, hns⟩ := hn
  obtain ⟨i, rfl⟩ := redteam_reconstructed_rows_are_nodes E P M hs
  obtain ⟨h3, h4, h6⟩ := h i
  rw [← redteam_reconstructed_row_state E P i] at h3 h4 h6
  have hempty : SizeWindowCounting.requiredSizeWindowNouns ((computeNodeAt E P i).skel) = [] := by
    unfold SizeWindowCounting.requiredSizeWindowNouns
    rcases hstate : ((computeNodeAt E P i).skel).state with
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;> rw [hstate] at h3 h4 h6 <;>
      first
        | rfl
        | exact absurd rfl h3
        | exact absurd rfl h4
        | exact absurd rfl h6
  rw [hempty] at hns
  simp at hns

/-- **`slotSemantics` with no carrier, at any execution avoiding OP0/OP9.**

Both clauses of `ServedLookupBridge.SkeletonSlotSemantics` are gated on `.s0` / `.s9`
, and the reconstructed row's state is the execution's own. -/

theorem redteam_slotSemantics_of_no_lookup_states (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (h : ∀ i : Fin E.cfg.compRows,
      (E.exec.computeRowAt i).1 ≠ .s0 ∧ (E.exec.computeRowAt i).1 ≠ .s9) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      ServedLookupBridge.SkeletonSlotSemantics s := by
  intro s hs
  obtain ⟨i, rfl⟩ := redteam_reconstructed_rows_are_nodes E P M hs
  obtain ⟨h0, h9⟩ := h i
  rw [← redteam_reconstructed_row_state E P i] at h0 h9
  exact { s0_slot := fun hst => absurd hst h0, s9_slot := fun hst => absurd hst h9 }

/-! ### §B.1 The live released F97 fixture -/

section LiveFixture

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusExecution

local instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic

-- Form R leftover first-row `counts = 0` / `indicator = 0` (live is `chainOneBitWeight`).
variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
/-- The released fixture's three compute rows are `OP_5`, `OP_1`, `OP_1`. -/
theorem redteam_distinctCensus_row_states
    (i : Fin (distinctCensusExecution hfirstD).cfg.compRows) :
    ((distinctCensusExecution hfirstD).exec.computeRowAt i).1 = .s5 ∨
      ((distinctCensusExecution hfirstD).exec.computeRowAt i).1 = .s1 := by
  match i with
  | ⟨0, _⟩ => exact Or.inl (congrArg Prod.fst computeRowAtD_zero)
  | ⟨1, _⟩ => exact Or.inr (congrArg Prod.fst computeRowAtD_one)
  | ⟨2, _⟩ => exact Or.inr (congrArg Prod.fst computeRowAtD_two)
  | ⟨n + 3, h⟩ =>
      have hc : (distinctCensusExecution hfirstD).cfg.compRows = 3 := rfl
      rw [hc] at h
      exact absurd h (by omega)

/-- The released fixture has no OP3/OP4/OP6 row. -/
theorem redteam_distinctCensus_no_window_states
    (i : Fin (distinctCensusExecution hfirstD).cfg.compRows) :
    ((distinctCensusExecution hfirstD).exec.computeRowAt i).1 ≠ .s3 ∧
      ((distinctCensusExecution hfirstD).exec.computeRowAt i).1 ≠ .s4 ∧
        ((distinctCensusExecution hfirstD).exec.computeRowAt i).1 ≠ .s6 := by
  rcases redteam_distinctCensus_row_states hfirstD i with h | h <;> rw [h] <;>
    exact ⟨by decide, by decide, by decide⟩

/-- The released fixture has no OP0/OP9 row. -/
theorem redteam_distinctCensus_no_lookup_states
    (i : Fin (distinctCensusExecution hfirstD).cfg.compRows) :
    ((distinctCensusExecution hfirstD).exec.computeRowAt i).1 ≠ .s0 ∧
      ((distinctCensusExecution hfirstD).exec.computeRowAt i).1 ≠ .s9 := by
  rcases redteam_distinctCensus_row_states hfirstD i with h | h <;> rw [h] <;>
    exact ⟨by decide, by decide⟩

/-- **`sizeWindowBound` is unconditional at the live released fixture, with no carrier.**
For every `(P, M)` pair.  Contrast `CensusExtraClosure.order_le_succ_Lambda_false_at_distinctCensus`,
which refutes the `orderOf` route at the same fixture: this route does not use the seed at all. -/

theorem redteam_distinctCensus_sizeWindowBound
    (P : ResidualPremises (distinctCensusExecution hfirstD))
    (M : MemoryRecordPremises (distinctCensusExecution hfirstD)) :
    SizeWindowCounting.SizeWindowNounsBoundedBy
      (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
        (memoryNodesOf (distinctCensusExecution hfirstD) M)) (distinctCensusExecution hfirstD).Λ :=
  redteam_sizeWindowBound_of_no_window_states (distinctCensusExecution hfirstD) P M
    (redteam_distinctCensus_no_window_states hfirstD)

/-- **`slotSemantics` is unconditional at the live released fixture, with no carrier.** -/

theorem redteam_distinctCensus_slotSemantics
    (P : ResidualPremises (distinctCensusExecution hfirstD))
    (M : MemoryRecordPremises (distinctCensusExecution hfirstD)) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)),
      ServedLookupBridge.SkeletonSlotSemantics s :=
  redteam_slotSemantics_of_no_lookup_states (distinctCensusExecution hfirstD) P M
    (redteam_distinctCensus_no_lookup_states hfirstD)

/-- **Four of the five `CensusRecordPremises` fields at the released F97 fixture, no carrier.**

The fifth field, `census`, is
**not** here: its `skeletonPairs` entries at the `.s5` row are `subformulaNoun` values, so it is the
one field that genuinely needs §A's missing leaf bound. Nothing is inhabited by this theorem —
`CensusRecordPremises` is not constructed and still has five fields. -/

theorem redteam_distinctCensus_four_of_five
    (P : ResidualPremises (distinctCensusExecution hfirstD))
    (M : MemoryRecordPremises (distinctCensusExecution hfirstD)) :
    (∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)),
        ServedLookupBridge.SkeletonSlotSemantics s) ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)) (distinctCensusExecution hfirstD).Λ ∧
      (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
        (memoryNodesOf (distinctCensusExecution hfirstD) M)).BoundedBy (distinctCensusExecution hfirstD).q ∧
      ProductionP8Containment.CombinedBoundedBy K97cubic (distinctCensusExecution hfirstD).q
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)) :=
  ⟨redteam_distinctCensus_slotSemantics hfirstD P M,
    redteam_distinctCensus_sizeWindowBound hfirstD P M,
    (CensusExtraClosure.distinctCensus_skeletonBounded_and_combinedBounded hfirstD P M).1,
    (CensusExtraClosure.distinctCensus_skeletonBounded_and_combinedBounded hfirstD P M).2⟩

end LiveFixture

/-! ## §C. Overlap B -/

/-- The earlier `Iff` is verified to be two-directional, restated independently. -/

theorem redteam_servedLookup_iff_slot (a : ℕ) (root child : Noun) :
    GlobalCarryAxis.ServedLookup (GlobalCarryRecognizer.ofNoun root 1) a child ↔
      Noun.slot a root = some child :=
  RecognizerCompleteness.servedLookup_iff_slot a root child

/-- **Overlap B, OP0 half: compiled.**  A `LocalOpcodeCertificate.s0`'s own `hserved` field, plus
the OP0 atom identification of the row tail with the certificate's own `axis`, gives the
reconstructed skeleton row's `s0_slot` clause verbatim.  So at OP0 the certificate really does
serve `slotSemantics` as well as `axisAtoms`.

The atom input is not smuggled: it *is* the OP0 clause of `AxisAtomPremises` with its existential
witness pinned to the certificate's `axis`, which is what makes this an overlap rather than a
second premise. -/

theorem redteam_overlapB_s0 {q Λ : ℕ}
    {inp : ComputeTable.Inputs K} {pub : ComputeTable.Pub K} {dec : ComputeTable.Dec K}
    (data : ComputeRowSemanticData q Λ (ComputeTable.State.s0, (inp, pub, dec)))
    (pubR : ComputePublicRowNounRealization q
      (computePublicLabel (ComputeTable.State.s0, (inp, pub, dec))))
    (axis : ℕ) (hax : data.root.tail = .atom axis)
    (hserved : GlobalCarryAxis.ServedLookup
      (GlobalCarryRecognizer.ofNoun data.root.subject 1) axis data.root.result) :
    Noun.slot (P8Census.skeletonMemoryAxis (computeSkeletonOf data pubR) 1)
        (computeSkeletonOf data pubR).subject =
      some (computeSkeletonOf data pubR).evaluation := by
  have haxis : P8Census.skeletonMemoryAxis (computeSkeletonOf data pubR) 1 = axis := by
    unfold P8Census.skeletonMemoryAxis
    rw [dif_pos (show ((1 : Fin 3) : ℕ) <
      Nock.Framework.recordCount (computeSkeletonOf data pubR).state from Nat.one_lt_two)]
    show (memRecSkelOf data pubR 1 Nat.one_lt_two).axis = axis
    simp only [memRecSkelOf]
    norm_num [hax, atomVal]
  rw [haxis]
  exact (redteam_servedLookup_iff_slot _ _ _).mp hserved

/-- **Overlap B, OP9 half: conditional.**  The same derivation needs, in addition, the
identification of the certificate's own `CallRealization` nouns with the reconstruction's
`Classical.choose` witnesses. -/

theorem redteam_overlapB_s9_of_identification {q Λ : ℕ}
    {inp : ComputeTable.Inputs K} {pub : ComputeTable.Pub K} {dec : ComputeTable.Dec K}
    (data : ComputeRowSemanticData q Λ (ComputeTable.State.s9, (inp, pub, dec)))
    (pubR : ComputePublicRowNounRealization q
      (computePublicLabel (ComputeTable.State.s9, (inp, pub, dec))))
    (axis : ℕ) (callResult callFormula : Noun)
    (hax : decompNoun data .f_th = .atom axis)
    (hid1 : callResult =
      P8Census.skeletonSubformula (computeSkeletonOf data pubR) 0 .result)
    (hid2 : callFormula =
      P8Census.skeletonSubformula (computeSkeletonOf data pubR) 1 .formula)
    (hserved : GlobalCarryAxis.ServedLookup
      (GlobalCarryRecognizer.ofNoun callResult 1) axis callFormula) :
    Noun.slot (P8Census.skeletonMemoryAxis (computeSkeletonOf data pubR) 2)
        (P8Census.skeletonSubformula (computeSkeletonOf data pubR) 0 .result) =
      some (P8Census.skeletonSubformula (computeSkeletonOf data pubR) 1 .formula) := by
  have haxis : P8Census.skeletonMemoryAxis (computeSkeletonOf data pubR) 2 = axis := by
    unfold P8Census.skeletonMemoryAxis
    rw [dif_pos (show ((2 : Fin 3) : ℕ) <
      Nock.Framework.recordCount (computeSkeletonOf data pubR).state from Nat.lt_succ_self 2)]
    show (memRecSkelOf data pubR 2 (Nat.lt_succ_self 2)).axis = axis
    simp only [memRecSkelOf]
    norm_num [hax, atomVal]
  rw [haxis, ← hid1, ← hid2]
  exact (redteam_servedLookup_iff_slot _ _ _).mp hserved

/-! ## §D. Nothing moved -/

/-- The census bundle still has its five named fields. -/
theorem redteam_censusRecordPremises_still_five {E : BuildableNockExecution F K}
    {P : ResidualPremises E} {M : MemoryRecordPremises E}
    (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } := by
  cases C
  rfl

/-- The residual bundle still has its four named fields. -/
theorem redteam_residualPremises_still_four {E : BuildableNockExecution F K}
    (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  GenericHonestCommitment.residualPremises_still_four P


theorem redteam_eleven_one_two : 11 + 1 + 2 = 14 := rfl

#print axioms threeLeaf_leaves
#print axioms threeLeaf_bounded
#print axioms redteam_enc_neg_one_collision
#print axioms redteam_one_lt_orderOf_neg_one
#print axioms redteam_c2_noncarrier_route_blocked
#print axioms redteam_leaves_eq_of_enc_eq_of_windows
#print axioms redteam_leaf_bounds_do_not_give_sepSeed
#print axioms redteam_reconstructed_row_state
#print axioms redteam_reconstructed_rows_are_nodes
#print axioms redteam_sizeWindowBound_of_no_window_states
#print axioms redteam_slotSemantics_of_no_lookup_states
#print axioms redteam_distinctCensus_row_states
#print axioms redteam_distinctCensus_sizeWindowBound
#print axioms redteam_distinctCensus_slotSemantics
#print axioms redteam_distinctCensus_four_of_five
#print axioms redteam_servedLookup_iff_slot
#print axioms redteam_overlapB_s0
#print axioms redteam_overlapB_s9_of_identification
#print axioms redteam_censusRecordPremises_still_five
#print axioms redteam_residualPremises_still_four
#print axioms redteam_eleven_one_two

end

end Nock.RedTeam.Batch137
