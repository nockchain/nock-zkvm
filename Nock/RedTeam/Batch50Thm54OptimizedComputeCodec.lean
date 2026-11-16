import Nock.NockVMROM.Thm54.OptimizedComputeCodecConcrete
import Nock.NockVMROM.Thm54.StrictPackage

/-!

Paper frame:

* compute and memory CORE: the paper;
* connective assembly: the paper;
* consumed compute capstone: the paper;
* appendix compute row and constraints: the paper;
* `Thm:comp_38` proof: the paper.

This artifact tests only the normalized `13`-base/`58`-extension codec.  It does not claim a
`ChipTemplate`, a 13/21 gate basis, a walk/program-IO overlay, an all-trace RAP biconditional,
padding composition, Batch-29 replacement, or an alias cutover.
-/

namespace Nock.RedTeam.Batch50

open Nock
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeCodec
open Nock.NockVMROM.Thm54.OptimizedComputeCodecConcrete
open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.StrictPackage

noncomputable section

/-! ## 1. Independent physical-slot census -/

theorem exact_base_slot_census :
    Fintype.card (OptimizedComputeCodec.BaseColumn) = 13 ∧
      Fintype.card (Fin 11) = 11 ∧
      Fintype.card (Fin 2) = 2 := by
  norm_num [OptimizedComputeCodec.BaseColumn]

theorem exact_extension_slot_census :
    Fintype.card (OptimizedComputeCodec.ExtensionColumn) = 58 ∧
      Fintype.card (Fin 12 × Fin 3) = 36 ∧
      Fintype.card (Fin 6 × Fin 3) = 18 ∧
      Fintype.card (Fin 4) = 4 := by
  norm_num [OptimizedComputeCodec.ExtensionColumn]

theorem base_partition_is_exhaustive
    (i : OptimizedComputeCodec.BaseColumn) :
    (∃ j : Fin 11, i = Sum.inl j) ∨ (∃ j : Fin 2, i = Sum.inr j) := by
  cases i with
  | inl j => exact Or.inl ⟨j, rfl⟩
  | inr j => exact Or.inr ⟨j, rfl⟩

theorem extension_partition_is_exhaustive
    (i : OptimizedComputeCodec.ExtensionColumn) :
    (∃ r : Fin 12, ∃ c : Fin 3, i = Sum.inl (r, c)) ∨
      (∃ r : Fin 6, ∃ c : Fin 3, i = Sum.inr (Sum.inl (r, c))) ∨
      (∃ j : Fin 4, i = Sum.inr (Sum.inr j)) := by
  rcases i with rc | rc
  · exact Or.inl ⟨rc.1, rc.2, rfl⟩
  · rcases rc with rc | j
    · exact Or.inr (Or.inl ⟨rc.1, rc.2, rfl⟩)
    · exact Or.inr (Or.inr ⟨j, rfl⟩)

theorem reject_base_off_by_one :
    ¬ Nonempty (OptimizedComputeCodec.BaseColumn ≃ Fin 12) ∧
      ¬ Nonempty (OptimizedComputeCodec.BaseColumn ≃ Fin 14) := by
  constructor
  · rintro ⟨e⟩
    have h := Fintype.card_congr e
    norm_num [OptimizedComputeCodec.BaseColumn] at h
  · rintro ⟨e⟩
    have h := Fintype.card_congr e
    norm_num [OptimizedComputeCodec.BaseColumn] at h

theorem reject_extension_off_by_one :
    ¬ Nonempty (OptimizedComputeCodec.ExtensionColumn ≃ Fin 57) ∧
      ¬ Nonempty (OptimizedComputeCodec.ExtensionColumn ≃ Fin 59) := by
  constructor
  · rintro ⟨e⟩
    have h := Fintype.card_congr e
    norm_num [OptimizedComputeCodec.ExtensionColumn] at h
  · rintro ⟨e⟩
    have h := Fintype.card_congr e
    norm_num [OptimizedComputeCodec.ExtensionColumn] at h

/-! ## 2. Every codec projection and memory-record reconstruction -/

variable {F K : Type*} [Field F] [Field K]

omit [Field K] in
theorem every_public_fingerprint_projects
    (pub : Pub K) (dec : Dec K) (ex : Extra K) (r : Fin 12) :
    decodePubFingerprint (encodeExtension pub dec ex) r = pubFingerprint pub r := by
  fin_cases r <;> ext <;> rfl

omit [Field K] in
theorem every_decomposition_fingerprint_projects
    (pub : Pub K) (dec : Dec K) (ex : Extra K) (r : Fin 6) :
    decodeDecFingerprint (encodeExtension pub dec ex) r = decFingerprint dec r := by
  fin_cases r <;> ext <;> rfl

omit [Field K] in
theorem every_scalar_extension_projects
    (pub : Pub K) (dec : Dec K) (ex : Extra K) :
    (encodeExtension pub dec ex) (.inr (.inr 0)) = pub.ln_prev ∧
      (encodeExtension pub dec ex) (.inr (.inr 1)) = pub.ln ∧
      (encodeExtension pub dec ex) (.inr (.inr 2)) = ex.consInv ∧
      (encodeExtension pub dec ex) (.inr (.inr 3)) = ex.invGen := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem every_base_projection (st : State) :
    decodeState (encodeBase (F := F) st) = st ∧
      (∀ i : Fin 11,
        encodeBase (F := F) st (.inl i) =
          if i = stateIndex st then 1 else 0) ∧
      encodeBase (F := F) st (.inr 0) = (fanoutComp st : F) ∧
      encodeBase (F := F) st (.inr 1) =
        (Nock.Framework.recordCount st : F) := by
  refine ⟨decodeState_encodeBase st, ?_, rfl, rfl⟩
  intro i
  rfl

theorem decoded_record_slots_are_exact
    (inp : Inputs K) (base : OptimizedComputeCodec.BaseColumn → F)
    (x : OptimizedComputeCodec.ExtensionColumn → K) :
    let dec := decodeDec x
    let core := decodePubCore base x
    let pub := decodePub inp base x
    pub.mr1.root = core.f ∧
      pub.mr1.child = dec.f_t ∧
      pub.mr1.axis = 3 ∧
      pub.mr1.ts = core.ln_prev * inp.α ∧
      pub.mr2.root = (expectedMr2 inp core dec).root ∧
      pub.mr2.child = (expectedMr2 inp core dec).child ∧
      pub.mr2.axis = (expectedMr2 inp core dec).axis ∧
      pub.mr2.ts = (expectedMr2 inp core dec).ts ∧
      pub.mr3.root = (expectedMr3 inp core dec).root ∧
      pub.mr3.child = (expectedMr3 inp core dec).child ∧
      pub.mr3.axis = (expectedMr3 inp core dec).axis ∧
      pub.mr3.ts = (expectedMr3 inp core dec).ts := by
  simp [decodePub, expectedMr1]

theorem accepted_row_reconstructs_same_records
    {inp : Inputs K} {pub : Pub K} {dec : Dec K} {ex : Extra K}
    (h : Vcomp inp pub dec) :
    let decoded :=
      decodePub (F := F) inp (encodeBase pub.state) (encodeExtension pub dec ex)
    decoded.mr1 = pub.mr1 ∧ decoded.mr2 = pub.mr2 ∧ decoded.mr3 = pub.mr3 := by
  have hp := decodePub_encode_of_vcomp (F := F) (ex := ex) h
  simp [hp]

theorem codec_distinguishes_semantic_rows
    {inp : Inputs K}
    {pub₁ pub₂ : Pub K} {dec₁ dec₂ : Dec K} {ex₁ ex₂ : Extra K}
    (h₁ : Vcomp inp pub₁ dec₁) (h₂ : Vcomp inp pub₂ dec₂)
    (hne :
      { pub₁ with sf1_st := none, sf2_st := none, sf3_st := none, certC? := none } ≠
          { pub₂ with sf1_st := none, sf2_st := none, sf3_st := none, certC? := none } ∨
        dec₁ ≠ dec₂ ∨ ex₁ ≠ ex₂) :
    encode (F := F) pub₁ dec₁ ex₁ ≠ encode (F := F) pub₂ dec₂ ex₂ := by
  intro heq
  have hd := congrArg (decode inp) heq
  rw [decode_encode_of_vcomp h₁, decode_encode_of_vcomp h₂] at hd
  have hp :
      { pub₁ with sf1_st := none, sf2_st := none, sf3_st := none, certC? := none } =
        { pub₂ with sf1_st := none, sf2_st := none, sf3_st := none, certC? := none } :=
    congrArg Prod.fst hd
  have hde : dec₁ = dec₂ := congrArg (fun t => t.2.1) hd
  have hex : ex₁ = ex₂ := congrArg (fun t => t.2.2) hd
  exact hne.elim (fun h => h hp) (fun h => h.elim (fun h => h hde) (fun h => h hex))

/-! ## 3. Two same-input accepted rows and roundtrip non-vacuity -/

noncomputable def s6Head : FP K73cubic := FP.atomFP honestSeed 6
noncomputable def s6TailHead : FP K73cubic := FP.atomFP honestSeed 2
noncomputable def s6TailTailHead : FP K73cubic := FP.atomFP honestSeed 3
noncomputable def s6TailTailTail : FP K73cubic := FP.atomFP honestSeed 4
noncomputable def s6TailTail : FP K73cubic :=
  FP.cons honestSeed s6TailTailHead s6TailTailTail
noncomputable def s6Tail : FP K73cubic :=
  FP.cons honestSeed s6TailHead s6TailTail
noncomputable def s6Formula : FP K73cubic :=
  FP.cons honestSeed s6Head s6Tail
noncomputable def s6Subject : FP K73cubic := FP.atomFP honestSeed 8
noncomputable def s6Evaluation : FP K73cubic := FP.atomFP honestSeed 5
noncomputable def s6Branch : FP K73cubic := FP.atomFP honestSeed 0

noncomputable def s6Dec : Dec K73cubic where
  f_h := s6Head
  f_t := s6Tail
  f_th := s6TailHead
  f_tt := s6TailTail
  f_tth := s6TailTailHead
  f_ttt := s6TailTailTail

noncomputable def s6Pub : Pub K73cubic where
  state := .s6
  s := s6Subject
  f := s6Formula
  e := s6Evaluation
  sf1_s := s6Subject
  sf1_f := s6TailTailHead
  sf1_e := s6Evaluation
  sf2_s := s6Subject
  sf2_f := s6TailHead
  sf2_e := s6Branch
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 2
  ln := 2 * honestAlpha ^ 3
  mr1 := ⟨s6Formula, s6Tail, 3, 8⟩
  mr2 := ⟨s6Tail, s6TailHead, 2, 32⟩
  mr3 := ⟨s6TailTail, s6TailTailHead, 2, 128⟩

noncomputable def s6Extra : Extra K73cubic := ⟨1, 2⟩

theorem s6_vcomp :
    Vcomp (computeInputs honestSeed honestAlpha) s6Pub s6Dec := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · ext <;> norm_num [s6Pub, s6Dec, computeInputs, honestAlpha]
  · simp [SVhead, headAtom, s6Pub, s6Dec, s6Head, computeInputs,
      State.toNat, honestSeed]
  · norm_num [memBlk, s6Pub, s6Dec, s6Tail, s6TailTail, computeInputs,
      honestAlpha]
  · simp [evalV, sfz3, s6Pub, s6Dec, s6Branch, s6Subject, s6Evaluation,
      computeInputs, FP.atomFP]

theorem two_opcodes_are_jointly_nonvacuous :
    Vcomp (computeInputs honestSeed honestAlpha)
        (computePub honestSeed honestAlpha) (computeDec honestSeed) ∧
      Vcomp (computeInputs honestSeed honestAlpha) s6Pub s6Dec :=
  ⟨compute_accepts, s6_vcomp⟩

theorem s6_roundtrip_same_row :
    decode (computeInputs honestSeed honestAlpha)
        (encode (F := F73) s6Pub s6Dec s6Extra) =
      ({ s6Pub with sf1_st := none, sf2_st := none, sf3_st := none, certC? := none },
        s6Dec, s6Extra) :=
  decode_encode_of_vcomp s6_vcomp

theorem two_rows_differ_in_state_and_all_records :
    s6Pub.state ≠ (computePub honestSeed honestAlpha).state ∧
      s6Pub.ln_prev ≠ (computePub honestSeed honestAlpha).ln_prev ∧
      s6Pub.mr1 ≠ (computePub honestSeed honestAlpha).mr1 ∧
      s6Pub.mr2 ≠ (computePub honestSeed honestAlpha).mr2 ∧
      s6Pub.mr3 ≠ (computePub honestSeed honestAlpha).mr3 := by
  have hinj : Set.InjOn (fun k : ℕ => (k : K73cubic)) (Set.Iio 73) :=
    StrictRawReconstruction.charCast_injOn 73
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · intro h
    have : (2 : ℕ) = 1 := hinj (by norm_num) (by norm_num)
      (by simpa [s6Pub, computePub] using h)
    omega
  · intro h
    have ht := congrArg (fun r : MemRec K73cubic => r.ts) h
    have : (8 : ℕ) = 4 := hinj (by norm_num) (by norm_num) (by
      simpa [s6Pub, computePub, requestRecord, honestAlpha] using ht)
    omega
  · intro h
    have ha := congrArg (fun r : MemRec K73cubic => r.axis) h
    have : (2 : ℕ) = 0 := hinj (by norm_num) (by norm_num) (by
      simpa [s6Pub, computePub, MemRec.zero] using ha)
    omega
  · intro h
    have ha := congrArg (fun r : MemRec K73cubic => r.axis) h
    have : (2 : ℕ) = 0 := hinj (by norm_num) (by norm_num) (by
      simpa [s6Pub, computePub, MemRec.zero] using ha)
    omega

theorem two_valid_rows_have_distinct_codewords :
    encode (F := F73) s6Pub s6Dec s6Extra ≠ honestRow := by
  apply codec_distinguishes_semantic_rows s6_vcomp compute_accepts
  exact Or.inl (fun hpub =>
    two_rows_differ_in_state_and_all_records.1 (congrArg Pub.state hpub))

/-! ## 4. Malformed encodings and the exact codec validity boundary -/

noncomputable def twoHotBase : OptimizedComputeCodec.BaseColumn → F73
  | .inl i => if i = stateIndex .s0 ∨ i = stateIndex .s1 then 1 else 0
  | .inr i => encodeBase (F := F73) .s0 (.inr i)

theorem non_one_hot_base_rejected : ¬ BaseWellFormed twoHotBase := by
  intro h
  have hs := baseWellFormed_selectors twoHotBase h (stateIndex .s1)
  norm_num [twoHotBase, decodeState, stateIndex, encodeBase] at hs

noncomputable def conflictingFanoutBase : OptimizedComputeCodec.BaseColumn → F73
  | .inl i => encodeBase (F := F73) .s1 (.inl i)
  | .inr i => if i = 0 then 1 else encodeBase (F := F73) .s1 (.inr i)

theorem conflicting_fanout_rejected : ¬ BaseWellFormed conflictingFanoutBase := by
  intro h
  have hf := baseWellFormed_fanout conflictingFanoutBase h
  norm_num [conflictingFanoutBase, decodeState, encodeBase, stateIndex, fanoutComp] at hf

noncomputable def conflictingRecordCountBase : OptimizedComputeCodec.BaseColumn → F73
  | .inl i => encodeBase (F := F73) .s1 (.inl i)
  | .inr i => if i = 1 then 0 else encodeBase (F := F73) .s1 (.inr i)

theorem conflicting_record_count_rejected :
    ¬ BaseWellFormed conflictingRecordCountBase := by
  intro h
  have hr := baseWellFormed_recordCount conflictingRecordCountBase h
  norm_num [conflictingRecordCountBase, decodeState, encodeBase, stateIndex,
    Nock.Framework.recordCount] at hr

theorem all_zero_base_rejected :
    ¬ BaseWellFormed (fun _ : OptimizedComputeCodec.BaseColumn => (0 : F73)) :=
  zero_base_rejected

noncomputable def zeroExtensionRow : Row F73 K73cubic where
  base := encodeBase .s1
  extension := fun _ => 0

theorem arbitrary_extension_passes_base_boundary
    (x : OptimizedComputeCodec.ExtensionColumn → K73cubic) :
    BaseWellFormed
      ({ base := encodeBase (F := F73) .s1, extension := x } : Row F73 K73cubic).base :=
  encodeBase_wellFormed .s1

theorem zero_extension_decodes_but_vcomp_rejects :
    BaseWellFormed zeroExtensionRow.base ∧
      ¬ Vcomp (computeInputs honestSeed honestAlpha)
        (decodePub (F := F73) (computeInputs honestSeed honestAlpha)
          zeroExtensionRow.base zeroExtensionRow.extension)
        (decodeDec zeroExtensionRow.extension) := by
  refine ⟨encodeBase_wellFormed .s1, ?_⟩
  intro h
  have hs := h.2.2.1
  norm_num [SVhead, headAtom, zeroExtensionRow, decodePub, decodePubCore,
    decodePubFingerprint, decodeDec, decodeDecFingerprint, fpOfCoordinates,
    decodeState, encodeBase, stateIndex, computeInputs, honestSeed] at hs

noncomputable def wrongRecordPub : Pub K73cubic :=
  { computePub honestSeed honestAlpha with mr1 := MemRec.zero }

theorem wrong_memory_record_rejected_by_vcomp :
    ¬ Vcomp (computeInputs honestSeed honestAlpha) wrongRecordPub
      (computeDec honestSeed) := by
  intro h
  have hr := h.2.1
  have hz : (MemRec.zero : MemRec K73cubic) =
      requestRecord honestSeed honestAlpha := by
    simpa [wrongRecordPub, computePub, computeDec, computeInputs, requestRecord] using hr
  exact honest_request_ne_zero hz.symm

theorem decoder_never_materializes_an_independent_wrong_record
    (inp : Inputs K) (row : Row F K) :
    let dec := (decode inp row).2.1
    let core := decodePubCore row.base row.extension
    let pub := (decode inp row).1
    pub.mr1 = expectedMr1 inp core dec ∧
      pub.mr2 = expectedMr2 inp core dec ∧
      pub.mr3 = expectedMr3 inp core dec := by
  simp [decode, decodePub]

/-! ## 5. Cubic carrier and same-package witness -/

theorem concrete_carrier_is_degree_three :
    Module.finrank F73 K73cubic = 3 := by
  simpa using GaloisField.finrank 73 (by norm_num)

theorem concrete_witness_is_exact_package_row :
    honestRow =
        encode (F := F73) (computePub honestSeed honestAlpha)
          (computeDec honestSeed) honestExtra ∧
      decode (computeInputs honestSeed honestAlpha) honestRow =
        (computePub honestSeed honestAlpha, computeDec honestSeed, honestExtra) :=
  ⟨rfl, honestRow_decode⟩

/-! ## 6. Scope guards: the future optimized core is not claimed here -/

def strict_package_still_consumes_B29
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
    Nock.RedTeam.Batch29.B29SemanticTemplate
      (K := K) (MonolithicRAP.compTemplate F) P.compLanguage :=
  P.compSemanticTemplate

noncomputable def strict_capstone_is_still_conditional
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
    StrictThm54Statement P :=
  strictNockVMROM_of_package P

theorem paper_alias_is_still_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  rfl

end
end Nock.RedTeam.Batch50

#print axioms Nock.RedTeam.Batch50.exact_base_slot_census
#print axioms Nock.RedTeam.Batch50.exact_extension_slot_census
#print axioms Nock.RedTeam.Batch50.reject_base_off_by_one
#print axioms Nock.RedTeam.Batch50.reject_extension_off_by_one
#print axioms Nock.RedTeam.Batch50.every_public_fingerprint_projects
#print axioms Nock.RedTeam.Batch50.every_decomposition_fingerprint_projects
#print axioms Nock.RedTeam.Batch50.decoded_record_slots_are_exact
#print axioms Nock.RedTeam.Batch50.codec_distinguishes_semantic_rows
#print axioms Nock.RedTeam.Batch50.s6_vcomp
#print axioms Nock.RedTeam.Batch50.s6_roundtrip_same_row
#print axioms Nock.RedTeam.Batch50.two_valid_rows_have_distinct_codewords
#print axioms Nock.RedTeam.Batch50.non_one_hot_base_rejected
#print axioms Nock.RedTeam.Batch50.conflicting_fanout_rejected
#print axioms Nock.RedTeam.Batch50.conflicting_record_count_rejected
#print axioms Nock.RedTeam.Batch50.all_zero_base_rejected
#print axioms Nock.RedTeam.Batch50.zero_extension_decodes_but_vcomp_rejects
#print axioms Nock.RedTeam.Batch50.wrong_memory_record_rejected_by_vcomp
#print axioms Nock.RedTeam.Batch50.decoder_never_materializes_an_independent_wrong_record
#print axioms Nock.RedTeam.Batch50.concrete_carrier_is_degree_three
#print axioms Nock.RedTeam.Batch50.concrete_witness_is_exact_package_row
#print axioms Nock.RedTeam.Batch50.strict_package_still_consumes_B29
#print axioms Nock.RedTeam.Batch50.strict_capstone_is_still_conditional
#print axioms Nock.RedTeam.Batch50.paper_alias_is_still_forest
