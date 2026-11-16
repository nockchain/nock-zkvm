import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.ServedLookupBridge
import Nock.RedTeam.Batch137Thm54CarrierProgram

/-!

**Nothing here inhabits a named premise, adds a carrier field,
weakens a census predicate, withdraws a theorem, or ticks a `§J` box.**
`BuildableNockExecution` keeps its fourteen fields, `HonestCommitment.Data` its sixteen,
`ResidualPremises` its **three** and `CensusRecordPremises` its five. No statement below is a
verdict on the paper construction, which is not in question at any point.

**Accounting correction.**  `ResidualPremises` has **three** fields —
`inactiveDec`, `axisAtoms`, `q_eq_ringChar` (`GenericHonestCommitment.lean:791`) — not four. `firstLine` left the structure at a later stage. Every "four" in this file's prose was wrong when
written; the *statements* were always three-field etas and are unaffected.

## §A.

That is enough to refute the
schema, but it leaves three scope questions a gate must answer: is the witness an artefact of the
smallest possible atom range (`BoundedBy 1` forces every leaf to `0`), of `Λ = 1`, or of
`orderOf z = 2`? The answer to all three is no, and the general mechanism is compiled here.

`leftComb k` is the left comb with `k + 1` leaves, all of them the atom `0`.
`b143_enc_leftComb` computes its fingerprint in closed form at any nonzero seed — the `size`
coordinate is `z ^ (k+1)`, the `leaf` coordinate is `0` because every leaf is `0`, and the `dyck`
coordinate is `z ^ k * ∑ i ∈ range k, z ^ i`, a geometric sum.  Hence
`b143_enc_leftComb_collision`: whenever `2 ≤ orderOf z`, the comb with `orderOf z + 1` leaves has
**exactly the same fingerprint as the one-leaf atom `0`**, because `z ^ orderOf z = 1` kills the
size coordinate's excess and the geometric sum `∑ i ∈ range (orderOf z), z ^ i` vanishes at any
`z ≠ 1` with `z ^ orderOf z = 1`.

The strengthening that matters downstream is `b143_f97_enc_collision_across_the_window`: at the
released F97 fixture's own seed, own `q = 97` and own `Λ = 7`, the seventeen-leaf comb and the
one-leaf atom `0` have the **same full `enc` fingerprint**, one inside the window and one outside.

## §B.

Same statement, independent proof.

That it is **seed-dependent** where the paper's window is **seed-free** is compiled rather than
argued.  `b143_window_hypothesis_is_seed_dependent` fixes one noun and one `Λ` and exhibits two
seeds in `ZMod 11` — one of order `5`, one of order `2` — at which the hypothesis of result 2
respectively holds and fails, while `leaves ≤ Λ` (the paper's `NockProgram^Λ` membership) is the same proposition at both seeds because no
seed occurs in it.  `b143_f97_collision_is_outside_the_result2_window` closes the loop: at F97 the
colliding comb has seventeen leaves against `orderOf z = 16`, so result 2 is unavailable exactly
where §A's collision lives.  The two results are consistent and jointly delimit the residual.

## §C. Result 3 — Overlap B: CONFIRMED, and the OP0 half is stronger than recorded

The asymmetry is **structural and pinned by `rfl`**, which is the cleanest form of the finding. `computeSkeletonOf` sets `subject := data.root.subject` and `evaluation := data.root.result`
(`b143_skeleton_subject_is_root`, `b143_skeleton_evaluation_is_root`, both `rfl`), while its
`subformula` field is `subformulaNoun` — a `Classical.choose` witness
(`b143_skeleton_subformula_is_a_chosen_witness`). A `LocalOpcodeCertificate.s0`'s `hserved` is
stated on `data.root.subject` / `data.root.result` (`SemanticTrace.lean:282-283`) and therefore
lands on the reconstruction's own nouns; a `LocalOpcodeCertificate.s9`'s `hserved` is stated on
`call1.result` / `call2.formula` (`SemanticTrace.lean:482-483`), which are `CallRealization` nouns
and **not** the reconstruction's.

Two sharpenings.

1. That attribution is sound, but the certificate's own `htail` field is a `ComparisonListed`, hence
   a `PairFaithful` (`SemanticTrace.lean:256-262`), which carries `SepSeed` and both boundedness
   facts and therefore *does* reflect the fingerprint equality to a noun equality
   (`OpcodeSemantics.PairFaithful.eq_of_enc_eq`). This is exactly how the production theorem
   `OpcodeSemantics.s0_vcomp_semantics` obtains `row.tail = .atom axis` from its own inputs. `b143_overlapB_s0_axis_from_certificate_fields` compiles that derivation from the certificate's
   `htail`, `hmr`, `hv`, `hz`, `hcast` alone, and `b143_overlapB_s0_from_certificate_fields` then
   gets the whole `s0_slot` clause with **no `AxisAtomPremises` input at all**. So at OP0 the
   certificate serves `slotSemantics` outright; Overlap B at OP0 is *stronger* than the record, not
   weaker.
2. **The OP9 identification is exactly an instance of the schema §A refutes.**
   `b143_overlapB_s9_identification_is_an_enc_collision_question` compiles that the certificate's
   `call1.result` and the reconstruction's `skeletonSubformula … 0 .result` are two `BoundedBy q`
   nouns with the *same* `enc` fingerprint, and likewise for `call2.formula` against
   `skeletonSubformula … 1 .formula`.

The theorem therefore does not by itself witness that an identification is *needed*; what does is
the pair of facts above plus §A. The docstring's reading is correct about the certificate route;
the compiled statement alone does not establish it.

## §D.

`b143_distinctCensus_no_lookup_states` re-derives the OP0/OP9 absence at the released F97 fixture
from the fixture's own three row equations.  Its consequence for `C5` is compiled rather than
asserted: `b143_distinctCensus_axisAtoms` inhabits the whole `AxisAtomPremises` family at that
fixture — every clause is vacuous by the state gate — with **no carrier field and no certificate**.
That is the `axisAtoms` half of the earlier "at F97 both target premises are already vacuous or free
without `C5`", gated here for the first time; the `slotSemantics` half is
`CensusExtraClosure.distinctCensus_slotSemantics`.

-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch143

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

/-! ## §A. The `C2` non-carrier route, at every window and every atom range -/

/-- The left comb with `k + 1` leaves, every leaf the atom `0`. -/
def leftComb : ℕ → Noun
  | 0 => .atom 0
  | k + 1 => .cell (leftComb k) (.atom 0)

theorem b143_leftComb_leaves (k : ℕ) : (leftComb k).leaves = k + 1 := by
  induction k with
  | zero => simp [leftComb, Noun.leaves]
  | succ k ih => simp [leftComb, Noun.leaves, ih]


theorem b143_leftComb_bounded {q : ℕ} (hq : 0 < q) (k : ℕ) :
    FieldEmbedding.BoundedBy q (leftComb k) := by
  induction k with
  | zero => simpa [leftComb] using hq
  | succ k ih => exact ⟨ih, hq⟩

/-- **The comb's fingerprint in closed form.**  Computed through the production `enc_cons`
homomorphism, not by unfolding `NPR.listPoly`.  The `dyck` coordinate is a geometric sum, which is
the whole mechanism of §A. -/

theorem b143_enc_leftComb {K : Type*} [Field K] {z : K} (hz : z ≠ 0) (k : ℕ) :
    GlobalCarryRecognizer.enc z (leftComb k) =
      ⟨z ^ (k + 1), z ^ k * ∑ i ∈ Finset.range k, z ^ i, 0⟩ := by
  have hatom : GlobalCarryRecognizer.enc z (Noun.atom 0) = ⟨z, 0, 0⟩ := by
    refine ComputeTable.FP.ext ?_ ?_ ?_
    · simp [GlobalCarryRecognizer.enc, Noun.leaves]
    · simp [GlobalCarryRecognizer.enc, NPR.dyckBits, Noun.dyckWord, Noun.shape,
        Nock.BTree.encode, NPR.listPoly, NPR.cpoly]
    · simp [GlobalCarryRecognizer.enc, NPR.leafF, Noun.leafList, NPR.listPoly, NPR.cpoly]
  induction k with
  | zero => simpa [leftComb] using hatom
  | succ k ih =>
      rw [show leftComb (k + 1) = .cell (leftComb k) (.atom 0) from rfl,
        GlobalCarryRecognizer.enc_cons hz, ih, hatom]
      refine ComputeTable.FP.ext ?_ ?_ ?_
      · simp [ComputeTable.FP.cons, pow_succ]
      · simp only [ComputeTable.FP.cons, Finset.sum_range_succ]
        field_simp
        ring
      · simp [ComputeTable.FP.cons]

/-- **The collision, at every seed of order at least two.**  `z ^ orderOf z = 1` makes the comb with
`orderOf z + 1` leaves share the atom's `size` coordinate, and the geometric sum
`∑ i ∈ range (orderOf z), z ^ i` vanishes, so the `dyck` coordinates agree too. -/

theorem b143_enc_leftComb_collision {K : Type*} [Field K] {z : K} (hord : 2 ≤ orderOf z) :
    GlobalCarryRecognizer.enc z (leftComb (orderOf z)) =
      GlobalCarryRecognizer.enc z (.atom 0) := by
  have hpow : z ^ orderOf z = 1 := pow_orderOf_eq_one z
  have hz : z ≠ 0 := (orderOf_pos_iff.mp (by omega)).isUnit.ne_zero
  have hne1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  have hsum : ∑ i ∈ Finset.range (orderOf z), z ^ i = 0 := by
    have hmul : (∑ i ∈ Finset.range (orderOf z), z ^ i) * (z - 1) = 0 := by
      rw [geom_sum_mul, hpow, sub_self]
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne1
  have hatom : GlobalCarryRecognizer.enc z (Noun.atom 0) = ⟨z, 0, 0⟩ := by
    simpa [leftComb] using b143_enc_leftComb (z := z) hz 0
  rw [b143_enc_leftComb hz, hatom]
  refine ComputeTable.FP.ext ?_ ?_ ?_
  · simp [pow_succ, hpow]
  · simp [hsum]
  · rfl



theorem b143_route_blocked {K : Type*} [Field K] {z : K} {q Λ : ℕ}
    (hq : 0 < q) (hΛ : 1 ≤ Λ) (hord : Λ < orderOf z) :
    ∃ real chosen : Noun,
      z ≠ 0 ∧ Λ < orderOf z ∧
        FieldEmbedding.BoundedBy q real ∧ real.leaves ≤ Λ ∧
          FieldEmbedding.BoundedBy q chosen ∧
            GlobalCarryRecognizer.enc z chosen = GlobalCarryRecognizer.enc z real ∧
              ¬ chosen.leaves ≤ Λ := by
  have h2 : 2 ≤ orderOf z := by omega
  have hz : z ≠ 0 := (orderOf_pos_iff.mp (by omega)).isUnit.ne_zero
  refine ⟨.atom 0, leftComb (orderOf z), hz, hord, by simpa using hq, ?_,
    b143_leftComb_bounded hq _, b143_enc_leftComb_collision h2, ?_⟩
  · simpa [Noun.leaves] using hΛ
  · rw [b143_leftComb_leaves]
    omega

/-- **The mechanism attribution, gated.**  A leaf bound is not a producer of `SepSeed` at a fixed
seed: the two colliding nouns are bounded by every positive atom range and leaf-bounded by
`orderOf z + 1`, and the seed is still not separating. -/

theorem b143_leaf_bounds_do_not_give_sepSeed {K : Type*} [Field K] {z : K} {q : ℕ}
    (hq : 0 < q) (hord : 2 ≤ orderOf z) :
    FieldEmbedding.BoundedBy q (leftComb (orderOf z)) ∧
        FieldEmbedding.BoundedBy q (Noun.atom 0) ∧
      (leftComb (orderOf z)).leaves ≤ orderOf z + 1 ∧
        (Noun.atom 0).leaves ≤ orderOf z + 1 ∧
          ¬ GlobalCarryRecognizer.SepSeed z (leftComb (orderOf z)) (.atom 0) := by
  refine ⟨b143_leftComb_bounded hq _, by simpa using hq, by rw [b143_leftComb_leaves], ?_, ?_⟩
  · simp [Noun.leaves]
  · intro hsep
    refine hsep ?_ (GlobalCarryRecognizer.enc_eq_imp_fn_eq _ _ _
      (b143_enc_leftComb_collision hord))
    intro hpair
    have hlen := congrArg (fun p => p.1.length) hpair
    simp only [NPR.leafF_length, b143_leftComb_leaves, Noun.leaves] at hlen
    omega

/-! ### §A.1 The same obstruction at the released F97 fixture's own seed, `q` and `Λ` -/

section LiveFixture

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusExecution

local instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

-- Form R leftover first-row counts (live is `chainOneBitWeight`).
variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
include hfirstD

/-- **A full three-coordinate fingerprint collision across the released F97 window.**  At the
fixture's own seed the seventeen-leaf comb and the one-leaf atom `0` have the same `enc` value, both
are bounded by the fixture's own `q`, and exactly one of them is inside the fixture's own window
`Λ = 7`. -/

theorem b143_f97_enc_collision_across_the_window :
    GlobalCarryRecognizer.enc (distinctCensusExecution hfirstD).cfg.challenges.z (leftComb 16) =
        GlobalCarryRecognizer.enc (distinctCensusExecution hfirstD).cfg.challenges.z (.atom 0) ∧
      FieldEmbedding.BoundedBy (distinctCensusExecution hfirstD).q (leftComb 16) ∧
        FieldEmbedding.BoundedBy (distinctCensusExecution hfirstD).q (Noun.atom 0) ∧
          (Noun.atom 0).leaves ≤ (distinctCensusExecution hfirstD).Λ ∧
            ¬ (leftComb 16).leaves ≤ (distinctCensusExecution hfirstD).Λ := by
  have hord : orderOf (distinctCensusExecution hfirstD).cfg.challenges.z = 16 :=
    (CensusExtraClosure.distinctCensus_Lambda_and_order hfirstD).2
  have hq : 0 < (distinctCensusExecution hfirstD).q := by
    rw [show (distinctCensusExecution hfirstD).q = 97 from rfl]
    omega
  refine ⟨?_, b143_leftComb_bounded hq 16, by simpa using hq, ?_, ?_⟩
  · have hcoll := b143_enc_leftComb_collision
      (z := (distinctCensusExecution hfirstD).cfg.challenges.z) (by rw [hord]; omega)
    rwa [hord] at hcoll
  · rw [show (distinctCensusExecution hfirstD).Λ = 7 from rfl]
    simp [Noun.leaves]
  · rw [b143_leftComb_leaves, show (distinctCensusExecution hfirstD).Λ = 7 from rfl]
    omega

/-- The colliding comb sits **outside** result 2's window at the fixture, which is why the two
results do not conflict: `orderOf z = 16` and the comb has seventeen leaves. -/

theorem b143_f97_collision_is_outside_the_result2_window :
    ¬ (leftComb 16).leaves < orderOf (distinctCensusExecution hfirstD).cfg.challenges.z := by
  rw [b143_leftComb_leaves, (CensusExtraClosure.distinctCensus_Lambda_and_order hfirstD).2]
  omega

end LiveFixture

/-! ## §B. Result 2, re-derived from monoid injectivity, and its seed-dependence -/



theorem b143_leaves_eq_of_enc_eq_of_windows {K : Type*} [Field K] {z : K} {m n : Noun}
    (h : GlobalCarryRecognizer.enc z m = GlobalCarryRecognizer.enc z n)
    (hm : m.leaves < orderOf z) (hn : n.leaves < orderOf z) :
    m.leaves = n.leaves :=
  pow_injOn_Iio_orderOf (x := z) hm hn (congrArg ComputeTable.FP.size h)

/-- **Result 2's hypothesis is seed-dependent; the paper's window is not.**  One noun, one `Λ`, two
seeds of `ZMod 11`: at the order-`5` seed the hypothesis holds, at the order-`2` seed it fails, and
the paper's `leaves ≤ Λ` is the same proposition at both because no seed occurs in
it.  That is why `C2`'s shape, not result 2's, is the faithful one. -/

theorem b143_window_hypothesis_is_seed_dependent :
    (leftComb 2).leaves ≤ 3 ∧
      (leftComb 2).leaves < orderOf (3 : ZMod 11) ∧
        ¬ (leftComb 2).leaves < orderOf (-1 : ZMod 11) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h5 : orderOf (3 : ZMod 11) = 5 := orderOf_eq_prime (by decide) (by decide)
  have h2 : orderOf (-1 : ZMod 11) = 2 := orderOf_eq_prime (by decide) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [b143_leftComb_leaves]
  · rw [b143_leftComb_leaves, h5]; omega
  · rw [b143_leftComb_leaves, h2]; omega

/-! ## §C. Overlap B: the asymmetry pinned by `rfl`, and both halves gated -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The reconstruction's `subject` is the root realization's own noun, by `rfl`. -/

theorem b143_skeleton_subject_is_root {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row)) :
    (computeSkeletonOf data pubR).subject = data.root.subject := rfl

/-- The reconstruction's `evaluation` is the root realization's own noun, by `rfl`. -/

theorem b143_skeleton_evaluation_is_root {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row)) :
    (computeSkeletonOf data pubR).evaluation = data.root.result := rfl

/-- The reconstruction's subformula projections are `subformulaNounOf`. -/

theorem b143_skeleton_subformula_is_a_chosen_witness {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row.1) (slot : TripleSlot) :
    P8Census.skeletonSubformula (computeSkeletonOf data pubR) i slot =
      subformulaNounOf data pubR i hi slot := by
  unfold P8Census.skeletonSubformula
  rw [dif_pos (show (i : ℕ) < ComputeTable.fanoutComp (computeSkeletonOf data pubR).state from hi)]
  rfl

/-- **The OP0 axis input is a certificate field, not a second premise.**  A
`LocalOpcodeCertificate.s0` stores `htail` as a `ComparisonListed`, hence a `PairFaithful`, which
carries `SepSeed` and both boundedness facts and therefore reflects the fingerprint equality that
`Vcomp`'s memory block supplies.  This is the production derivation of
`OpcodeSemantics.s0_vcomp_semantics`, isolated. -/

theorem b143_overlapB_s0_axis_from_certificate_fields {q Λ axis : ℕ}
    {inp : ComputeTable.Inputs K} {pub : ComputeTable.Pub K} {dec : ComputeTable.Dec K}
    (data : ComputeRowSemanticData q Λ (ComputeTable.State.s0, (inp, pub, dec)))
    (hstate : pub.state = .s0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (htail : ComparisonListed data .recursiveFormula data.root.tail (.atom axis))
    (hmr : OpcodeSemantics.RealizesMemRec inp.z pub.mr2
      data.root.subject data.root.result axis)
    (hv : ComputeTable.Vcomp inp pub dec) :
    data.root.tail = .atom axis := by
  obtain ⟨_, _, _, hmem, _⟩ := hv
  simp only [ComputeTable.memBlk, hstate] at hmem
  obtain ⟨hmr2, _, _, hsize, hdyck⟩ := hmem
  have haxisField : dec.f_t.leaf = (axis : K) := by
    calc
      dec.f_t.leaf = pub.mr2.axis := (congrArg ComputeTable.MemRec.axis hmr2).symm
      _ = (axis : K) := hmr.axis_realizes
  have htailEnc : GlobalCarryRecognizer.enc inp.z data.root.tail =
      GlobalCarryRecognizer.enc inp.z (.atom axis) := by
    calc
      GlobalCarryRecognizer.enc inp.z data.root.tail = dec.f_t :=
        data.root.tail_realizes.symm
      _ = ComputeTable.FP.atomFP inp.z (axis : K) :=
        ComputeTable.FP.ext hsize hdyck haxisField
      _ = GlobalCarryRecognizer.enc inp.z (.atom axis) :=
        (GlobalCarryRecognizer.enc_atom inp.z axis).symm
  exact htail.faithful.eq_of_enc_eq hcast htailEnc

/-- **Overlap B, OP0 half: compiled from the certificate's own fields alone.**  No
`AxisAtomPremises` input appears. -/

theorem b143_overlapB_s0_from_certificate_fields {q Λ axis : ℕ}
    {inp : ComputeTable.Inputs K} {pub : ComputeTable.Pub K} {dec : ComputeTable.Dec K}
    (data : ComputeRowSemanticData q Λ (ComputeTable.State.s0, (inp, pub, dec)))
    (pubR : ComputePublicRowNounRealization q
      (computePublicLabel (ComputeTable.State.s0, (inp, pub, dec))))
    (hstate : pub.state = .s0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (htail : ComparisonListed data .recursiveFormula data.root.tail (.atom axis))
    (hmr : OpcodeSemantics.RealizesMemRec inp.z pub.mr2
      data.root.subject data.root.result axis)
    (hserved : GlobalCarryAxis.ServedLookup
      (GlobalCarryRecognizer.ofNoun data.root.subject 1) axis data.root.result)
    (hv : ComputeTable.Vcomp inp pub dec) :
    Noun.slot (P8Census.skeletonMemoryAxis (computeSkeletonOf data pubR) 1)
        (computeSkeletonOf data pubR).subject =
      some (computeSkeletonOf data pubR).evaluation := by
  have hax : data.root.tail = .atom axis :=
    b143_overlapB_s0_axis_from_certificate_fields data hstate hcast htail hmr hv
  have haxis : P8Census.skeletonMemoryAxis (computeSkeletonOf data pubR) 1 = axis := by
    unfold P8Census.skeletonMemoryAxis
    rw [dif_pos (show ((1 : Fin 3) : ℕ) <
      Nock.Framework.recordCount (computeSkeletonOf data pubR).state from Nat.one_lt_two)]
    show (memRecSkelOf data pubR 1 Nat.one_lt_two).axis = axis
    unfold memRecSkelOf
    norm_num [hax, atomVal]
  rw [haxis]
  exact (RecognizerCompleteness.servedLookup_iff_slot _ _ _).mp hserved

/-- **The OP9 identification, reduced to the schema §A refutes.**  The certificate's `call1.result`
and the reconstruction's `skeletonSubformula … 0 .result` are two `BoundedBy q` nouns with the *same*
`enc` fingerprint, and likewise for `call2.formula`. -/

theorem b143_overlapB_s9_identification_is_an_enc_collision_question {q Λ : ℕ}
    {inp : ComputeTable.Inputs K} {pub : ComputeTable.Pub K} {dec : ComputeTable.Dec K}
    (data : ComputeRowSemanticData q Λ (ComputeTable.State.s9, (inp, pub, dec)))
    (pubR : ComputePublicRowNounRealization q
      (computePublicLabel (ComputeTable.State.s9, (inp, pub, dec))))
    (call1 : OpcodeSemantics.CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
    (call2 : OpcodeSemantics.CallRealization inp.z pub.sf2_s pub.sf2_f pub.sf2_e) :
    (GlobalCarryRecognizer.enc inp.z call1.result =
        GlobalCarryRecognizer.enc inp.z
          (P8Census.skeletonSubformula (computeSkeletonOf data pubR) 0 .result) ∧
      FieldEmbedding.BoundedBy q
        (P8Census.skeletonSubformula (computeSkeletonOf data pubR) 0 .result)) ∧
    (GlobalCarryRecognizer.enc inp.z call2.formula =
        GlobalCarryRecognizer.enc inp.z
          (P8Census.skeletonSubformula (computeSkeletonOf data pubR) 1 .formula) ∧
      FieldEmbedding.BoundedBy q
        (P8Census.skeletonSubformula (computeSkeletonOf data pubR) 1 .formula)) := by
  have h0 : ((0 : Fin 3) : ℕ) < ComputeTable.fanoutComp ComputeTable.State.s9 := by
    simp [ComputeTable.fanoutComp]
  have h1 : ((1 : Fin 3) : ℕ) < ComputeTable.fanoutComp ComputeTable.State.s9 := by
    simp [ComputeTable.fanoutComp]
  rw [b143_skeleton_subformula_is_a_chosen_witness data pubR 0 h0 .result,
    b143_skeleton_subformula_is_a_chosen_witness data pubR 1 h1 .formula]
  refine ⟨⟨?_, subformulaNounOf_bounded data pubR 0 h0 .result⟩,
    ⟨?_, subformulaNounOf_bounded data pubR 1 h1 .formula⟩⟩
  · rw [subformulaNounOf_enc data pubR 0 h0 .result]
    simpa [computeSubformulaFPs, ComputeTable.sfTriple, tripleFP,
      OpcodeSemantics.Realizes] using call1.result_realizes.symm
  · rw [subformulaNounOf_enc data pubR 1 h1 .formula]
    simpa [computeSubformulaFPs, ComputeTable.sfTriple, tripleFP,
      OpcodeSemantics.Realizes] using call2.formula_realizes.symm

/-! ## §D. Result 4, re-derived, and the `axisAtoms` consequence at F97 -/

section F97

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusExecution

local instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

-- Form R leftover first-row counts (live is `chainOneBitWeight`).
variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
include hfirstD

/-- **Result 4, gated.**  The released F97 fixture has no OP0 and no OP9 compute row, re-derived
from the fixture's own three row equations. -/
theorem b143_distinctCensus_no_lookup_states
    (i : Fin (distinctCensusExecution hfirstD).cfg.compRows) :
    ((distinctCensusExecution hfirstD).exec.computeRowAt i).1 ≠ .s0 ∧
      ((distinctCensusExecution hfirstD).exec.computeRowAt i).1 ≠ .s9 := by
  match i with
  | ⟨0, h⟩ =>
      have hrow : ((distinctCensusExecution hfirstD).exec.computeRowAt ⟨0, h⟩).1 =
          ComputeTable.State.s5 := congrArg Prod.fst computeRowAtD_zero
      rw [hrow]
      exact ⟨by decide, by decide⟩
  | ⟨1, h⟩ =>
      have hrow : ((distinctCensusExecution hfirstD).exec.computeRowAt ⟨1, h⟩).1 =
          ComputeTable.State.s1 := congrArg Prod.fst computeRowAtD_one
      rw [hrow]
      exact ⟨by decide, by decide⟩
  | ⟨2, h⟩ =>
      have hrow : ((distinctCensusExecution hfirstD).exec.computeRowAt ⟨2, h⟩).1 =
          ComputeTable.State.s1 := congrArg Prod.fst computeRowAtD_two
      rw [hrow]
      exact ⟨by decide, by decide⟩
  | ⟨n + 3, h⟩ =>
      have hc : (distinctCensusExecution hfirstD).cfg.compRows = 3 := rfl
      rw [hc] at h
      exact absurd h (by omega)

/-- **`axisAtoms` at the released F97 fixture, with no carrier and no certificate.**  Both clauses of
`AxisAtomPremises` are gated on OP0 / OP9, which result 4 excludes at every row.  This is the
`axisAtoms` half of the earlier ground for deprioritizing `C5`, compiled.  It inhabits **no** named
premise bundle: `ResidualPremises` still has its three fields and this is one conjunct of one of
them. -/

theorem b143_distinctCensus_axisAtoms :
    ∀ i : Fin (distinctCensusExecution hfirstD).cfg.compRows,
      AxisAtomPremises ((distinctCensusExecution hfirstD).semanticData.rows i) := by
  intro i
  obtain ⟨h0, h9⟩ := b143_distinctCensus_no_lookup_states hfirstD i
  exact ⟨fun h => absurd h h0, fun h => absurd h h9⟩

end F97

/-! ## §E. Nothing moved -/

/-- The census bundle still has its five named fields. -/
theorem b143_censusRecordPremises_still_five {E : BuildableNockExecution F K}
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

/-- The residual bundle still has its named fields — **three** of them (`inactiveDec`,
`axisAtoms`, `q_eq_ringChar`; `GenericHonestCommitment.lean:791`), as the conjunction below
shows. -/
theorem b143_residualPremises_still_four {E : BuildableNockExecution F K}
    (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  GenericHonestCommitment.residualPremises_still_four P


theorem b143_eleven_one_two : 11 + 1 + 2 = 14 := rfl

#print axioms b143_leftComb_leaves
#print axioms b143_leftComb_bounded
#print axioms b143_enc_leftComb
#print axioms b143_enc_leftComb_collision
#print axioms b143_route_blocked
#print axioms b143_leaf_bounds_do_not_give_sepSeed
#print axioms b143_f97_enc_collision_across_the_window
#print axioms b143_f97_collision_is_outside_the_result2_window
#print axioms b143_leaves_eq_of_enc_eq_of_windows
#print axioms b143_window_hypothesis_is_seed_dependent
#print axioms b143_skeleton_subject_is_root
#print axioms b143_skeleton_evaluation_is_root
#print axioms b143_skeleton_subformula_is_a_chosen_witness
#print axioms b143_overlapB_s0_axis_from_certificate_fields
#print axioms b143_overlapB_s0_from_certificate_fields
#print axioms b143_overlapB_s9_identification_is_an_enc_collision_question
#print axioms b143_distinctCensus_no_lookup_states
#print axioms b143_distinctCensus_axisAtoms
#print axioms b143_censusRecordPremises_still_five
#print axioms b143_residualPremises_still_four
#print axioms b143_eleven_one_two

end

end Nock.RedTeam.Batch143
