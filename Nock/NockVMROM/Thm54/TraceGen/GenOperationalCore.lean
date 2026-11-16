/-
  Nock/NockVMROM/Thm54/TraceGen/GenOperationalCore.lean

  **`SkeletonOperationalCore` — how much of it is derivable, and where the rest is stuck.**

  `ProductionP8Containment.accepted_outside_failureUnion` (`:598`) and
  `production_jointProbability_falseAcceptance_le` (`:978`) both carry

      hop : ∀ s ∈ SemanticStrategy.computeSkeletonRows T.skeleton,
              BoundSemanticTrace.SkeletonOperationalCore s

  `ServedLookupBridge.skeletonOperationalCore_iff` splits `hop` into exactly two halves:

  * `SkeletonRecordEquations` — the noun-level record shape at OP0/OP9;
  * `SkeletonSlotSemantics`   — the two Nock `/` facts, equivalent to the served lookups.

  ## What this file lands

  **The record half, generically, from acceptance.**  `skeletonRecordEquations_of_accepted`
  derives `SkeletonRecordEquations` at *every* committed row of an *arbitrary* skeleton from

  * `binds : SemanticStrategy.BindsAt z S cfg exec` — already a field of
    `ProductionP8Containment.BareSemanticSupport`, not part of `hop`;
  * `exec.ComputeRowsAccepted` — already derived from acceptance inside
    `accepted_outside_failureUnion` (`hrows`, `:665`);
  * `hcast` and `S.BoundedBy q` — already hypotheses there;
  * a **counted** seed condition `z ∉ (SkeletonRecordCensus.census …).badSeeds`, of exactly the
    species of the existing collision event, with the same `count * (2Λ - 1)` bound
    (`recordCensus_badSeeds_card_le`).

  The compute gate that makes this work is `ComputeTable.memBlk`: at `op_0 = 1` it pins
  `mem_root_2 = input_subject`, `mem_child_2 = evaluation`, and at `op_9 = 1`
  `mem_root_3 = sf1_e`, `mem_child_3 = sf2_f` — but at the `𝕂^3` fingerprint
  level, so the fingerprint→noun step needs `GlobalCarryRecognizer.SepSeed` at those four pairs.

  **The four record pairs are NOT census entries.**  `P8Census.skeletonComparisons` at `.s0`
  lists only `(f_h, 0)`, `(formula, cons(f_h,f_t))`, `(f_t, atom mem_axis_2)`, and at `.s9` only
  the head/cons/axis-atom/recursive/result occurrences (`P8Census.lean:275-364`).  `recordPair_not_in_skeletonComparisons` compiles that for a legal row.  Hence
  `combined_pairFaithful` supplies nothing here and a *separate* census is needed; that census is
  `SkeletonRecordCensus` below.  The *axis* halves of the same two records ARE census entries —
  `.s0` lists `recursiveFormula (f_t, atom mem_axis_2)` and `.s9` lists
  `axisAtom (f_th, atom mem_axis_3)` — so census-goodness does supply faithfulness there; only the root/child pairs are missing.  No axis equation is proved or needed
  in this file.

  **The served half is not landed, and the obstruction is reproduced.**
  `record_does_not_imply_slot` exhibits a legal `ComputeRowSkeleton` at `.s0` that satisfies
  `SkeletonRecordEquations` and refutes `SkeletonSlotSemantics`, hence refutes
  `SkeletonOperationalCore`.  So the record half is strictly weaker and no amount of record-level
  gating reaches the served half.  The only existing supplier is
  `ServedLookupBridge.slotSemantics_of_served`, which needs a
  `ServedMemoryTrace.ExactServedMemoryTrace q Λ cfg exec D` — and `D` is
  `SemanticTrace.ExactExecutionSemanticData`, whose `rows` field is literally what
  `canonicalRowsOfBare` produces from `hop`.  That route is circular in this position.

  ## What is still assumed after this file

  `operationalCore_of_accepted_and_slots` is the strictly better shape:  `hop` replaced by
  `hslot : ∀ s ∈ computeSkeletonRows S, SkeletonSlotSemantics s` (two Nock `/` facts per OP0/OP9
  row) plus a counted seed condition.  The record half is gone from the premises.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticDataParts
import Nock.NockVMROM.Thm54.TraceGen.GenCommitmentBridge

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.GenOperationalCore

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

variable {lmb : K}

/-! ## 1. Total pre-seed projections of the two record nouns

`P8Census.skeletonMemoryAxis` already projects the axis totally; the root and child nouns had no
total projection, and a pair list needs one. -/

/-- Total pre-seed projection of one memory-record root noun. -/
def skeletonRecordRoot (s : ComputeRowSkeleton) (i : Fin 3) : Noun :=
  if h : (i : ℕ) < Nock.Framework.recordCount s.state
  then (s.memoryRecord i h).root
  else .atom 0

/-- Total pre-seed projection of one memory-record child noun. -/
def skeletonRecordChild (s : ComputeRowSkeleton) (i : Fin 3) : Noun :=
  if h : (i : ℕ) < Nock.Framework.recordCount s.state
  then (s.memoryRecord i h).child
  else .atom 0

theorem skeletonRecordRoot_eq (s : ComputeRowSkeleton) (i : Fin 3)
    (h : (i : ℕ) < Nock.Framework.recordCount s.state) :
    skeletonRecordRoot s i = (s.memoryRecord i h).root := by
  simp [skeletonRecordRoot, h]

theorem skeletonRecordChild_eq (s : ComputeRowSkeleton) (i : Fin 3)
    (h : (i : ℕ) < Nock.Framework.recordCount s.state) :
    skeletonRecordChild s i = (s.memoryRecord i h).child := by
  simp [skeletonRecordChild, h]

/-! ## 2. The four record pairs and the record census

These are the pairs the paper and the paper equate at the fingerprint level and which
`P8Census.skeletonComparisons` does not list. -/

/-- The record noun pairs of one committed row: two at OP0, two at OP9, none elsewhere. -/
def recordPairs (s : ComputeRowSkeleton) : List (Noun × Noun) :=
  match s.state with
  | .s0 =>
      [(skeletonRecordRoot s 1, s.subject),
        (skeletonRecordChild s 1, s.evaluation)]
  | .s9 =>
      [(skeletonRecordRoot s 2, P8Census.skeletonSubformula s 0 .result),
        (skeletonRecordChild s 2, P8Census.skeletonSubformula s 1 .formula)]
  | _ => []

theorem mem_recordPairs_s0_root (s : ComputeRowSkeleton) (h : s.state = .s0) :
    (skeletonRecordRoot s 1, s.subject) ∈ recordPairs s := by
  simp [recordPairs, h]

theorem mem_recordPairs_s0_child (s : ComputeRowSkeleton) (h : s.state = .s0) :
    (skeletonRecordChild s 1, s.evaluation) ∈ recordPairs s := by
  simp [recordPairs, h]

theorem mem_recordPairs_s9_root (s : ComputeRowSkeleton) (h : s.state = .s9) :
    (skeletonRecordRoot s 2, P8Census.skeletonSubformula s 0 .result) ∈ recordPairs s := by
  simp [recordPairs, h]

theorem mem_recordPairs_s9_child (s : ComputeRowSkeleton) (h : s.state = .s9) :
    (skeletonRecordChild s 2, P8Census.skeletonSubformula s 1 .formula) ∈ recordPairs s := by
  simp [recordPairs, h]

theorem recordPairs_length_le (s : ComputeRowSkeleton) :
    (recordPairs s).length ≤ 2 := by
  cases hs : s.state <;> simp [recordPairs, hs]

/-- All record pairs of one skeleton, in canonical BFS row order. -/
def recordPairList (S : SemanticSkeleton) : List (Noun × Noun) :=
  (computeSkeletonRows S).flatMap recordPairs

theorem mem_recordPairList {S : SemanticSkeleton} {s : ComputeRowSkeleton}
    (hs : s ∈ computeSkeletonRows S) {pair : Noun × Noun}
    (hpair : pair ∈ recordPairs s) :
    pair ∈ recordPairList S := by
  rw [recordPairList, List.mem_flatMap]
  exact ⟨s, hs, hpair⟩

theorem recordPairList_length_le (S : SemanticSkeleton) :
    (recordPairList S).length ≤ 2 * (computeSkeletonRows S).length := by
  simp only [recordPairList]
  generalize computeSkeletonRows S = l
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have ha := recordPairs_length_le a
      omega

/-- Leaf bounds for the record-pair occurrence list of one bare pre-seed skeleton.  Exactly the
shape of `BoundSemanticTrace.SkeletonP8Census`, on the pairs the paper needs and
`P8Census.skeletonComparisons` omits. -/
structure SkeletonRecordCensus (S : SemanticSkeleton) (Λ : ℕ) : Prop where
  leaves_bounded :
    ∀ pair ∈ recordPairList S, pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ

namespace SkeletonRecordCensus

def census {S : SemanticSkeleton} {Λ : ℕ} (C : SkeletonRecordCensus S Λ) :
    ComparisonCensus Λ :=
  ComparisonCensus.ofPairList (recordPairList S) C.leaves_bounded

end SkeletonRecordCensus

section Counting

variable [Fintype K] [DecidableEq K]

/-- The record census contributes its own `2Λ - 1` roots per occurrence, i.e. at most
`2 * compRows * (2Λ - 1)` bad seeds.  Same species and same bound shape as
`ComparisonCensus.badSeeds_card_le` on the existing combined census. -/
theorem recordCensus_badSeeds_card_le {S : SemanticSkeleton} {Λ : ℕ}
    (C : SkeletonRecordCensus S Λ) :
    ((C.census).badSeeds (K := K)).card ≤ (recordPairList S).length * (2 * Λ - 1) := by
  simpa [SkeletonRecordCensus.census] using
    ComparisonCensus.badSeeds_card_le (K := K) (C.census)

/-- Separation at every record pair, from the counted seed condition. -/
theorem sepSeed_of_good_seed {S : SemanticSkeleton} {Λ : ℕ}
    (C : SkeletonRecordCensus S Λ) {z : K}
    (hgood : z ∉ (C.census).badSeeds (K := K))
    {pair : Noun × Noun} (hpair : pair ∈ recordPairList S) :
    GlobalCarryRecognizer.SepSeed z pair.1 pair.2 := by
  obtain ⟨i, hi⟩ :=
    ComparisonCensus.exists_pair_of_mem (recordPairList S) C.leaves_bounded hpair
  have hsep := P8Census.sepSeed_of_not_mem_badSeeds (C.census) z hgood i
  rw [show (C.census).pair i = pair from hi] at hsep
  exact hsep

end Counting

/-! ## 3. The four faithfulness data, and their supply from the record census -/

/-- Exactly the collision/boundedness data the fingerprint→noun step of the paper
needs.  Pair-local, like `OpcodeSemantics.PairFaithful` itself. -/
structure RecordFaithful (z : K) (q : ℕ) (s : ComputeRowSkeleton) : Prop where
  s0_root :
    s.state = .s0 →
      OpcodeSemantics.PairFaithful z q (skeletonRecordRoot s 1) s.subject
  s0_child :
    s.state = .s0 →
      OpcodeSemantics.PairFaithful z q (skeletonRecordChild s 1) s.evaluation
  s9_root :
    s.state = .s9 →
      OpcodeSemantics.PairFaithful z q (skeletonRecordRoot s 2)
        (P8Census.skeletonSubformula s 0 .result)
  s9_child :
    s.state = .s9 →
      OpcodeSemantics.PairFaithful z q (skeletonRecordChild s 2)
        (P8Census.skeletonSubformula s 1 .formula)

section Faithful

variable [Fintype K] [DecidableEq K]

/-- `RecordFaithful` at every committed row, from `S.BoundedBy q` (which already bounds the record
nouns — `ComputeRowSkeleton.BoundedBy`'s last conjunct) plus the counted record-census seed
condition.  Nothing operational is assumed. -/
theorem recordFaithful_of_good_seed {S : SemanticSkeleton} {Λ q : ℕ}
    (C : SkeletonRecordCensus S Λ) (hb : S.BoundedBy q) {z : K}
    (hgood : z ∉ (C.census).badSeeds (K := K))
    {s : ComputeRowSkeleton} (hs : s ∈ computeSkeletonRows S) :
    RecordFaithful z q s := by
  have hrow : ComputeRowSkeleton.BoundedBy q s :=
    List.forall_iff_forall_mem.mp hb.computeRows s hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hi : ((1 : Fin 3) : ℕ) < Nock.Framework.recordCount s.state := by
      simp [h, Nock.Framework.recordCount]
    refine ⟨sepSeed_of_good_seed C hgood (mem_recordPairList hs
      (mem_recordPairs_s0_root s h)), ?_, hrow.1⟩
    rw [skeletonRecordRoot_eq s 1 hi]
    exact (hrow.2.2.2.2.2 1 hi).1
  · intro h
    have hi : ((1 : Fin 3) : ℕ) < Nock.Framework.recordCount s.state := by
      simp [h, Nock.Framework.recordCount]
    refine ⟨sepSeed_of_good_seed C hgood (mem_recordPairList hs
      (mem_recordPairs_s0_child s h)), ?_, hrow.2.2.1⟩
    rw [skeletonRecordChild_eq s 1 hi]
    exact (hrow.2.2.2.2.2 1 hi).2
  · intro h
    have hi : ((2 : Fin 3) : ℕ) < Nock.Framework.recordCount s.state := by
      simp [h, Nock.Framework.recordCount]
    have hf : ((0 : Fin 3) : ℕ) < ComputeTable.fanoutComp s.state := by
      simp [h, ComputeTable.fanoutComp]
    refine ⟨sepSeed_of_good_seed C hgood (mem_recordPairList hs
      (mem_recordPairs_s9_root s h)), ?_, ?_⟩
    · rw [skeletonRecordRoot_eq s 2 hi]
      exact (hrow.2.2.2.2.2 2 hi).1
    · rw [show P8Census.skeletonSubformula s 0 .result = s.subformula 0 hf .result from
        dif_pos hf]
      exact hrow.2.2.2.2.1 0 hf .result
  · intro h
    have hi : ((2 : Fin 3) : ℕ) < Nock.Framework.recordCount s.state := by
      simp [h, Nock.Framework.recordCount]
    have hf : ((1 : Fin 3) : ℕ) < ComputeTable.fanoutComp s.state := by
      simp [h, ComputeTable.fanoutComp]
    refine ⟨sepSeed_of_good_seed C hgood (mem_recordPairList hs
      (mem_recordPairs_s9_child s h)), ?_, ?_⟩
    · rw [skeletonRecordChild_eq s 2 hi]
      exact (hrow.2.2.2.2.2 2 hi).2
    · rw [show P8Census.skeletonSubformula s 1 .formula = s.subformula 1 hf .formula from
        dif_pos hf]
      exact hrow.2.2.2.2.1 1 hf .formula

end Faithful

/-! ## 4. The record half of one accepted row

`memBlk` at `op_0 = 1` and at `op_9 = 1` pins the two record
fingerprints; `BindComputeRow` binds both sides to committed nouns; `RecordFaithful` reflects the
resulting fingerprint equality into a noun equality. -/

/-- **OP0 record shape from acceptance**. -/
theorem record_s0_of_accepted_row {q : ℕ} {z : K} {s : ComputeRowSkeleton}
    {cfg : ExactConfig F K} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbind : BindComputeRow z s row)
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (hfaith : RecordFaithful z q s)
    (h : s.state = ComputeTable.State.s0) :
    skeletonRecordRoot s 1 = s.subject ∧ skeletonRecordChild s 1 = s.evaluation := by
  have hi : ((1 : Fin 3) : ℕ) < Nock.Framework.recordCount s.state := by
    simp [h, Nock.Framework.recordCount]
  have hst : row.2.2.1.state = ComputeTable.State.s0 := by
    rw [hbind.2.2.1, h]
  have hmem : ComputeTable.memBlk row.2.1 row.2.2.1 row.2.2.2 := hacc.2.2.2.2.2.1
  simp only [ComputeTable.memBlk, hst] at hmem
  have hmr2 : row.2.2.1.mr2 =
      ⟨row.2.2.1.s, row.2.2.1.e, row.2.2.2.f_t.leaf,
        row.2.2.1.ln_prev * row.2.1.α ^ 2⟩ := hmem.1
  have hbm : BindMemRec z (s.memoryRecord 1 hi) (computeMemRec row.2.2.1 1) :=
    RawSemanticAssembly.bindComputeRow_memRec hbind 1 hi
  have hcm : computeMemRec row.2.2.1 (1 : Fin 3) = row.2.2.1.mr2 := rfl
  have hroot : row.2.2.1.s =
      GlobalCarryRecognizer.enc z (s.memoryRecord 1 hi).root := by
    have h1 := hbm.1
    rw [hcm, hmr2] at h1
    exact h1
  have hchild : row.2.2.1.e =
      GlobalCarryRecognizer.enc z (s.memoryRecord 1 hi).child := by
    have h1 := hbm.2.1
    rw [hcm, hmr2] at h1
    exact h1
  have hsubj : row.2.2.1.s = GlobalCarryRecognizer.enc z s.subject := hbind.2.2.2.1
  have heval : row.2.2.1.e = GlobalCarryRecognizer.enc z s.evaluation :=
    hbind.2.2.2.2.2.1
  refine ⟨?_, ?_⟩
  · refine (hfaith.s0_root h).eq_of_enc_eq hcast ?_
    rw [skeletonRecordRoot_eq s 1 hi]
    exact hroot.symm.trans hsubj
  · refine (hfaith.s0_child h).eq_of_enc_eq hcast ?_
    rw [skeletonRecordChild_eq s 1 hi]
    exact hchild.symm.trans heval

/-- **OP9 record shape from acceptance**. -/
theorem record_s9_of_accepted_row {q : ℕ} {z : K} {s : ComputeRowSkeleton}
    {cfg : ExactConfig F K} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbind : BindComputeRow z s row)
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (hfaith : RecordFaithful z q s)
    (h : s.state = ComputeTable.State.s9) :
    skeletonRecordRoot s 2 = P8Census.skeletonSubformula s 0 .result ∧
      skeletonRecordChild s 2 = P8Census.skeletonSubformula s 1 .formula := by
  have hi : ((2 : Fin 3) : ℕ) < Nock.Framework.recordCount s.state := by
    simp [h, Nock.Framework.recordCount]
  have hf0 : ((0 : Fin 3) : ℕ) < ComputeTable.fanoutComp s.state := by
    simp [h, ComputeTable.fanoutComp]
  have hf1 : ((1 : Fin 3) : ℕ) < ComputeTable.fanoutComp s.state := by
    simp [h, ComputeTable.fanoutComp]
  have hst : row.2.2.1.state = ComputeTable.State.s9 := by
    rw [hbind.2.2.1, h]
  have hmem : ComputeTable.memBlk row.2.1 row.2.2.1 row.2.2.2 := hacc.2.2.2.2.2.1
  simp only [ComputeTable.memBlk, hst] at hmem
  have hmr3 : row.2.2.1.mr3 =
      ⟨row.2.2.1.sf1_e, row.2.2.1.sf2_f, row.2.2.2.f_th.leaf,
        row.2.2.1.ln_prev * row.2.1.α ^ 3⟩ := hmem.2.2.1
  have hbm : BindMemRec z (s.memoryRecord 2 hi) (computeMemRec row.2.2.1 2) :=
    RawSemanticAssembly.bindComputeRow_memRec hbind 2 hi
  have hcm : computeMemRec row.2.2.1 (2 : Fin 3) = row.2.2.1.mr3 := rfl
  have hroot : row.2.2.1.sf1_e =
      GlobalCarryRecognizer.enc z (s.memoryRecord 2 hi).root := by
    have h1 := hbm.1
    rw [hcm, hmr3] at h1
    exact h1
  have hchild : row.2.2.1.sf2_f =
      GlobalCarryRecognizer.enc z (s.memoryRecord 2 hi).child := by
    have h1 := hbm.2.1
    rw [hcm, hmr3] at h1
    exact h1
  have hsf0 := hbind.2.2.2.2.2.2.2.1 (0 : Fin 3)
  rw [dif_pos hf0] at hsf0
  have hsf1 := hbind.2.2.2.2.2.2.2.1 (1 : Fin 3)
  rw [dif_pos hf1] at hsf1
  have hres : row.2.2.1.sf1_e =
      GlobalCarryRecognizer.enc z (s.subformula 0 hf0 .result) := hsf0 .result
  have hform : row.2.2.1.sf2_f =
      GlobalCarryRecognizer.enc z (s.subformula 1 hf1 .formula) := hsf1 .formula
  refine ⟨?_, ?_⟩
  · refine (hfaith.s9_root h).eq_of_enc_eq hcast ?_
    rw [skeletonRecordRoot_eq s 2 hi,
      show P8Census.skeletonSubformula s 0 .result = s.subformula 0 hf0 .result from
        dif_pos hf0]
    exact hroot.symm.trans hres
  · refine (hfaith.s9_child h).eq_of_enc_eq hcast ?_
    rw [skeletonRecordChild_eq s 2 hi,
      show P8Census.skeletonSubformula s 1 .formula = s.subformula 1 hf1 .formula from
        dif_pos hf1]
    exact hchild.symm.trans hform

/-- **The record half of `SkeletonOperationalCore` at one accepted row.** -/
theorem skeletonRecordEquations_of_accepted_row {q : ℕ} {z : K} {s : ComputeRowSkeleton}
    {cfg : ExactConfig F K} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbind : BindComputeRow z s row)
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (hfaith : RecordFaithful z q s) :
    ServedLookupBridge.SkeletonRecordEquations s where
  s0_record := by
    intro h
    have hi : ((1 : Fin 3) : ℕ) < Nock.Framework.recordCount s.state := by
      simp [h, Nock.Framework.recordCount]
    obtain ⟨hr, hc⟩ := record_s0_of_accepted_row hcast hbind hacc hfaith h
    rw [skeletonRecordRoot_eq s 1 hi] at hr
    rw [skeletonRecordChild_eq s 1 hi] at hc
    exact ⟨hr, hc⟩
  s9_record := by
    intro h
    have hi : ((2 : Fin 3) : ℕ) < Nock.Framework.recordCount s.state := by
      simp [h, Nock.Framework.recordCount]
    obtain ⟨hr, hc⟩ := record_s9_of_accepted_row hcast hbind hacc hfaith h
    rw [skeletonRecordRoot_eq s 2 hi] at hr
    rw [skeletonRecordChild_eq s 2 hi] at hc
    exact ⟨hr, hc⟩

/-! ## 5. The record half at every committed row of an arbitrary skeleton -/

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

/-- **`SkeletonRecordEquations` at every committed row of an arbitrary skeleton, from
acceptance.**  No operational premise: `binds` is `BareSemanticSupport.binds`, `hrows` is derived
from acceptance, and `hfaith` is supplied by `recordFaithful_of_good_seed` from a counted seed
condition. -/
theorem skeletonRecordEquations_of_accepted {q : ℕ} {z : K} {S : SemanticSkeleton}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (binds : BindsAt z S cfg exec)
    (hrows : exec.ComputeRowsAccepted)
    (hfaith : ∀ s ∈ computeSkeletonRows S, RecordFaithful z q s) :
    ∀ s ∈ computeSkeletonRows S, ServedLookupBridge.SkeletonRecordEquations s := by
  intro s hs
  obtain ⟨row, hrow, hbind⟩ := exists_paired binds.derived_computeRows s hs
  exact skeletonRecordEquations_of_accepted_row hcast hbind
    ((ExactExecution.computeRowsAccepted_iff exec).1 hrows row hrow) (hfaith s hs)

section Capstone

variable [Fintype K] [DecidableEq K]

/-- **The record half, fully discharged from acceptance and a counted seed event.** -/
theorem recordEquations_of_good_seed {q Λ : ℕ} {z : K} {S : SemanticSkeleton}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbound : S.BoundedBy q)
    (C : SkeletonRecordCensus S Λ)
    (hgood : z ∉ (C.census).badSeeds (K := K))
    (binds : BindsAt z S cfg exec)
    (hrows : exec.ComputeRowsAccepted) :
    ∀ s ∈ computeSkeletonRows S, ServedLookupBridge.SkeletonRecordEquations s :=
  skeletonRecordEquations_of_accepted hcast binds hrows
    (fun _ hs => recordFaithful_of_good_seed C hbound hgood hs)

/-- **`hop` with its record half derived rather than assumed.**

This is the strictly better shape than
`ProductionP8Containment.accepted_outside_failureUnion`'s `hop`: the only operational premise left
is `hslot`, the two Nock `/` facts of `ServedLookupBridge.SkeletonSlotSemantics`, which `skeletonSlotSemantics_iff_served` shows is *equivalent* to the two
served-lookup fields — so nothing is hidden and nothing is weakened.  The record fields are gone from the premises. -/
theorem operationalCore_of_accepted_and_slots {q Λ : ℕ} {z : K} {S : SemanticSkeleton}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbound : S.BoundedBy q)
    (C : SkeletonRecordCensus S Λ)
    (hgood : z ∉ (C.census).badSeeds (K := K))
    (binds : BindsAt z S cfg exec)
    (hrows : exec.ComputeRowsAccepted)
    (hslot : ∀ s ∈ computeSkeletonRows S,
      ServedLookupBridge.SkeletonSlotSemantics s) :
    ∀ s ∈ computeSkeletonRows S, BoundSemanticTrace.SkeletonOperationalCore s :=
  fun s hs =>
    ServedLookupBridge.skeletonOperationalCore_of_parts
      (recordEquations_of_good_seed hcast hbound C hgood binds hrows s hs)
      (hslot s hs)

end Capstone

/-! ## 6. The generated path: `hop` is already fully closed there

The statements below only instantiate it at the memory forest a live configuration commits, and
project out the two halves, so that the generated route and the general route below speak the same
language. -/

section Generated

/-- **`SkeletonOperationalCore` at the committed skeleton of any accepted program.**  A naming of
`TraceGen.genOperationalCore` at `TraceGen.genMemoryForest`, the forest
`TraceGen.genBindsAt_threaded` binds. -/
theorem genCommittedOperationalCore (z α : K) (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (TraceGen.GenComputeRow K)} {result : Noun}
    (h : TraceGen.genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ s ∈ computeSkeletonRows
        (TraceGen.genSemanticSkeleton (TraceGen.bfsAssign (TraceGen.airReorder t))
          (TraceGen.genMemoryForest z α lmb inp t)),
      BoundSemanticTrace.SkeletonOperationalCore s :=
  TraceGen.genOperationalCore h (TraceGen.genMemoryForest z α lmb inp t)

/-- The served half on the generated path — the half the general route above cannot supply. -/
theorem genCommittedSlotSemantics (z α : K) (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (TraceGen.GenComputeRow K)} {result : Noun}
    (h : TraceGen.genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ s ∈ computeSkeletonRows
        (TraceGen.genSemanticSkeleton (TraceGen.bfsAssign (TraceGen.airReorder t))
          (TraceGen.genMemoryForest z α lmb inp t)),
      ServedLookupBridge.SkeletonSlotSemantics s :=
  fun s hs =>
    ServedLookupBridge.skeletonSlotSemantics_of_core
      (genCommittedOperationalCore z α inp h s hs)

/-- The record half on the generated path. -/
theorem genCommittedRecordEquations (z α : K) (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (TraceGen.GenComputeRow K)} {result : Noun}
    (h : TraceGen.genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ s ∈ computeSkeletonRows
        (TraceGen.genSemanticSkeleton (TraceGen.bfsAssign (TraceGen.airReorder t))
          (TraceGen.genMemoryForest z α lmb inp t)),
      ServedLookupBridge.SkeletonRecordEquations s :=
  fun s hs =>
    ServedLookupBridge.skeletonRecordEquations_of_core
      (genCommittedOperationalCore z α inp h s hs)

end Generated

/-! ## 7. The reproduced negatives

Two facts, compiled, about why the served half is not reachable from the record half and why the
record pairs need their own census. -/

/-- A legal OP0 row whose record equations hold and whose `/` fact fails: the committed axis is `2`
and the committed subject is an atom, so `/(2, subject)` is `none`. -/
def slotFailRow : ComputeRowSkeleton where
  state := .s0
  subject := .atom 1
  formula := .atom 2
  evaluation := .atom 3
  decomposition := fun _ _ => .atom 4
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 1, .atom 3, 2⟩

theorem slotFailRow_recordEquations :
    ServedLookupBridge.SkeletonRecordEquations slotFailRow where
  s0_record := by intro _; exact ⟨rfl, rfl⟩
  s9_record := by intro h; exact absurd h (by decide)

theorem slotFailRow_not_slotSemantics :
    ¬ ServedLookupBridge.SkeletonSlotSemantics slotFailRow := by
  intro hslot
  have hi : ((1 : Fin 3) : ℕ) < Nock.Framework.recordCount slotFailRow.state := by
    decide
  have hax : P8Census.skeletonMemoryAxis slotFailRow 1 = 2 :=
    (StrictOperationalEvidence.skeletonMemoryAxis_eq slotFailRow 1 hi).trans rfl
  have hsub : slotFailRow.subject = Noun.atom 1 := rfl
  have hev : slotFailRow.evaluation = Noun.atom 3 := rfl
  have h := hslot.s0_slot rfl
  rw [hax, hsub, hev] at h
  simp [Nock.Noun.slot] at h

/-- **The record half is strictly weaker than `SkeletonOperationalCore`.**  So the served half of
`hop` carries content that no record-level gate — the paper included — can supply. -/
theorem record_does_not_imply_slot :
    ∃ s : ComputeRowSkeleton,
      ServedLookupBridge.SkeletonRecordEquations s ∧
        ¬ ServedLookupBridge.SkeletonSlotSemantics s :=
  ⟨slotFailRow, slotFailRow_recordEquations, slotFailRow_not_slotSemantics⟩

theorem slotFailRow_not_operationalCore :
    ¬ BoundSemanticTrace.SkeletonOperationalCore slotFailRow := fun core =>
  slotFailRow_not_slotSemantics
    (ServedLookupBridge.skeletonSlotSemantics_of_core core)

/-- **The OP0 record pair is not a census entry.**  `P8Census.skeletonComparisons` at `.s0` lists
the opcode head, the formula cons, and the formula-tail/axis-atom occurrence — nothing comparing a
record root with the subject.  Hence `ProductionP8Containment.combined_pairFaithful` cannot supply
`RecordFaithful`, and `SkeletonRecordCensus` is a genuinely new counted event rather than a
projection of the existing one. -/
theorem recordPair_not_in_skeletonComparisons :
    (skeletonRecordRoot slotFailRow 1, slotFailRow.subject) ∉
      (P8Census.skeletonComparisons (K := K) slotFailRow).map
        SemanticTrace.ComparisonUse.pair := by
  simp [P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
    P8Census.skeletonMemoryAxis, skeletonRecordRoot, slotFailRow,
    SemanticTrace.ComparisonUse.pair, Nock.Framework.recordCount,
    SemanticStrategy.decActive]

end

end Nock.NockVMROM.Thm54.GenOperationalCore

#print axioms Nock.NockVMROM.Thm54.GenOperationalCore.skeletonRecordEquations_of_accepted_row
#print axioms Nock.NockVMROM.Thm54.GenOperationalCore.skeletonRecordEquations_of_accepted
#print axioms Nock.NockVMROM.Thm54.GenOperationalCore.recordFaithful_of_good_seed
#print axioms Nock.NockVMROM.Thm54.GenOperationalCore.recordEquations_of_good_seed
#print axioms Nock.NockVMROM.Thm54.GenOperationalCore.operationalCore_of_accepted_and_slots
#print axioms Nock.NockVMROM.Thm54.GenOperationalCore.recordCensus_badSeeds_card_le
#print axioms Nock.NockVMROM.Thm54.GenOperationalCore.recordPairList_length_le
#print axioms Nock.NockVMROM.Thm54.GenOperationalCore.genCommittedOperationalCore
#print axioms Nock.NockVMROM.Thm54.GenOperationalCore.genCommittedSlotSemantics
#print axioms Nock.NockVMROM.Thm54.GenOperationalCore.genCommittedRecordEquations
#print axioms Nock.NockVMROM.Thm54.GenOperationalCore.record_does_not_imply_slot
#print axioms Nock.NockVMROM.Thm54.GenOperationalCore.slotFailRow_not_operationalCore
#print axioms Nock.NockVMROM.Thm54.GenOperationalCore.recordPair_not_in_skeletonComparisons
