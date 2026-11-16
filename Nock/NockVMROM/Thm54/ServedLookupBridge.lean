/-
  Nock/NockVMROM/Thm54/ServedLookupBridge.lean

  ## What is closed and what is not

  `RecognizerCompleteness.servedLookup_iff_slot` proves

      `ServedLookup (ofNoun root 1) a child  ↔  Noun.slot a root = some child`

  in *both* directions.  Hence the served fields of `BoundSemanticTrace.SkeletonOperationalCore` are
  neither weaker nor stronger than

  * OP0: `\(axis(mr2), subject) = evaluation`;
  * OP9: `\(axis(mr3), sf1.result) = sf2.formula`

.
  `SkeletonSlotSemantics` names exactly those two facts and
  `skeletonSlotSemantics_iff_served` proves the naming is exact (`Iff`, not an implication), so this
  is a *translation* of the obligation into Nock language, not a weakening.

  **The remaining honest premise.**  The slot facts themselves are NOT derivable from field-level
  acceptance of a compute row: `ExactExecution.ComputeRowAccepted` gives the state tag, the shared
  inputs, and `ComputeTable.Vcomp`, and `Vcomp` only ever sees the memory record *fingerprints*
  `(root_fn, child_fn, axis)`; no compute constraint relates those three to a slot.  The memory side
  supplies the relation only through the honest per-root reconstruction
  `AxisSoundness.ExactMemoryHonestReconstruction` (`AxisBridge.HonestRecon`).

  `HonestRecon = NounShape ∧ ReadVerifyNested`; `NounShape` is free
  (`AxisBridge.nounShape_canonNoun`) and `ReadVerifyNested` is now decided by a verifier check
  (`ProductionAxisStructureVerifier.readVerifyNestedCheck_eq_true_iff` `:84`) and follows from
  acceptance as `TemplateAxisCounting.ExactAxisStructuralRefinement.ancestry` (produced by
  `exactAxisStructuralRefinement_of_accepts` `:300`).  So the *reconstruction* is available; what is
  actually missing is the verify-side **record partition** — `MTree.verify` retains only `(ℕ, K)`, so
  recovering a `MemRec` from its exponent is equivalent to `TimestampClosedAt`
  (`timestampExp_recovers_ts_iff_closed`, `GenericHonestData.lean:4417`).  `AxisBridge`'s own
  section "The NOUN is irrelevant to axis SOUNDNESS" says as much.

  So one honest premise remains, and it is now named in Nock language rather
  than in recognizer language: **`SkeletonSlotSemantics`** (equivalently the served fields,
  equivalently honest reconstruction of the row subject).  Everything else in
  `StrictRowOperationalEvidence` is discharged here from the record equations and modular OP4.
-/

import Nock.NockVMROM.Thm54.RecognizerCompleteness
import Nock.NockVMROM.Thm54.RawSemanticAssembly
import Nock.NockVMROM.Thm54.ServedMemoryTrace

namespace Nock.NockVMROM.Thm54.ServedLookupBridge

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM.Thm54.RecognizerCompleteness
open Nock.NockVMROM.Thm54.StrictOperationalEvidence

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

abbrev RowSkeleton := SemanticStrategy.ComputeRowSkeleton

/-! ## The two Nock slot facts of a pre-seed compute row -/

/-- **The served-memory obligation, in Nock language.**  `s0_slot` is the `OP_0` slot semantics of
the row; `s9_slot` is the `OP_9` core/arm lookup at the committed `mr3` axis.
Both are stated on the pre-seed skeleton nouns only: no field, no seed, no fingerprint. -/
structure SkeletonSlotSemantics (s : RowSkeleton) : Prop where
  s0_slot :
    s.state = .s0 →
      Noun.slot (P8Census.skeletonMemoryAxis s 1) s.subject = some s.evaluation
  s9_slot :
    s.state = .s9 →
      Noun.slot (P8Census.skeletonMemoryAxis s 2)
        (P8Census.skeletonSubformula s 0 .result) =
          some (P8Census.skeletonSubformula s 1 .formula)

/-- The two record noun equations of `BoundSemanticTrace.SkeletonOperationalCore`, isolated from the
served fields so that the served obligation can be replaced independently. -/
structure SkeletonRecordEquations (s : RowSkeleton) : Prop where
  s0_record :
    ∀ h : s.state = .s0,
      let mr := s.memoryRecord (1 : Fin 3) (by simp [h, Nock.Framework.recordCount])
      mr.root = s.subject ∧ mr.child = s.evaluation
  s9_record :
    ∀ h : s.state = .s9,
      let mr := s.memoryRecord (2 : Fin 3) (by simp [h, Nock.Framework.recordCount])
      mr.root = P8Census.skeletonSubformula s 0 .result ∧
        mr.child = P8Census.skeletonSubformula s 1 .formula

/-! ## The served fields are exactly the slot facts -/

/-- **B2, step 2 (forward).**  The `OP_0` served lookup of a row, derived from the row's slot fact by
recognizer completeness. -/
theorem strict_s0_served_of_slot {s : RowSkeleton}
    (hslot : SkeletonSlotSemantics s) (h : s.state = .s0) :
    GlobalCarryAxis.ServedLookup
      (GlobalCarryRecognizer.ofNoun s.subject 1)
      (P8Census.skeletonMemoryAxis s 1) s.evaluation :=
  servedLookup_of_slot (hslot.s0_slot h)

/-- **B2, step 2 (forward), OP9.** -/
theorem strict_s9_served_of_slot {s : RowSkeleton}
    (hslot : SkeletonSlotSemantics s) (h : s.state = .s9) :
    GlobalCarryAxis.ServedLookup
      (GlobalCarryRecognizer.ofNoun
        (P8Census.skeletonSubformula s 0 .result) 1)
      (P8Census.skeletonMemoryAxis s 2)
      (P8Census.skeletonSubformula s 1 .formula) :=
  servedLookup_of_slot (hslot.s9_slot h)

/-- The converse: served lookups give back the slot facts (`axis_sound_recognizer'`). -/
theorem skeletonSlotSemantics_of_served {s : RowSkeleton}
    (h0 : s.state = .s0 →
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun s.subject 1)
        (P8Census.skeletonMemoryAxis s 1) s.evaluation)
    (h9 : s.state = .s9 →
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun
          (P8Census.skeletonSubformula s 0 .result) 1)
        (P8Census.skeletonMemoryAxis s 2)
        (P8Census.skeletonSubformula s 1 .formula)) :
    SkeletonSlotSemantics s where
  s0_slot h := (servedLookup_iff_slot _ _ _).1 (h0 h)
  s9_slot h := (servedLookup_iff_slot _ _ _).1 (h9 h)

/-- **The naming is exact.**  The two served fields of `SkeletonOperationalCore` are *equivalent* to
`SkeletonSlotSemantics`; replacing them is a change of language, not of strength. -/
theorem skeletonSlotSemantics_iff_served (s : RowSkeleton) :
    SkeletonSlotSemantics s ↔
      ((s.state = .s0 →
          GlobalCarryAxis.ServedLookup
            (GlobalCarryRecognizer.ofNoun s.subject 1)
            (P8Census.skeletonMemoryAxis s 1) s.evaluation) ∧
        (s.state = .s9 →
          GlobalCarryAxis.ServedLookup
            (GlobalCarryRecognizer.ofNoun
              (P8Census.skeletonSubformula s 0 .result) 1)
            (P8Census.skeletonMemoryAxis s 2)
            (P8Census.skeletonSubformula s 1 .formula))) :=
  ⟨fun h => ⟨strict_s0_served_of_slot h, strict_s9_served_of_slot h⟩,
    fun h => skeletonSlotSemantics_of_served h.1 h.2⟩

/-! ## Decomposing and rebuilding the operational core -/

/-- An operational core supplies its record equations. -/
theorem skeletonRecordEquations_of_core {s : RowSkeleton}
    (core : BoundSemanticTrace.SkeletonOperationalCore s) :
    SkeletonRecordEquations s where
  s0_record := core.s0_record
  s9_record := core.s9_record

/-- An operational core supplies the slot facts. -/
theorem skeletonSlotSemantics_of_core {s : RowSkeleton}
    (core : BoundSemanticTrace.SkeletonOperationalCore s) :
    SkeletonSlotSemantics s :=
  skeletonSlotSemantics_of_served core.s0_served core.s9_served

/-- Conversely, the record equations and slot facts rebuild the whole operational core. -/
theorem skeletonOperationalCore_of_parts {s : RowSkeleton}
    (hrec : SkeletonRecordEquations s) (hslot : SkeletonSlotSemantics s) :
    BoundSemanticTrace.SkeletonOperationalCore s where
  s0_record := hrec.s0_record
  s0_served := strict_s0_served_of_slot hslot
  s9_record := hrec.s9_record
  s9_served := strict_s9_served_of_slot hslot

/-- **Exact decomposition of the operational core.**  It is precisely the record equations and the
two Nock slot facts. -/
theorem skeletonOperationalCore_iff (s : RowSkeleton) :
    BoundSemanticTrace.SkeletonOperationalCore s ↔
      (SkeletonRecordEquations s ∧ SkeletonSlotSemantics s) :=
  ⟨fun core => ⟨skeletonRecordEquations_of_core core, skeletonSlotSemantics_of_core core⟩,
    fun h => skeletonOperationalCore_of_parts h.1 h.2⟩

/-! ## ExactServedMemoryTrace coverage → skeleton `/` facts

The orphan join between closeout `slotSemantics` and the OP9 served-memory
coverage: `Service.served` is `Noun.slot axis root = some child` on the
exact memory-trace services, not `needs.served` length, not NMR `axisNat`,
and not the paper `/(1,n)=n` base case. Identifying those triples with a
skeleton row's OP0/OP9 slots inhabits `SkeletonSlotSemantics`. -/

/-- The `(root, axis, child)` triples of every service in an exact served-memory
trace. -/
def servedTuplesOf {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {D : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec} {execA : ExactExecution cfg}
    (T : ServedMemoryTrace.ExactServedMemoryTrace q Λ cfg exec D execA) :
    List (Noun × ℕ × Noun) :=
  (List.finRange cfg.kMem).flatMap fun i =>
    (T.roots i).services.map fun s => (s.root, s.axis, s.child)

/-- Every served tuple is a genuine `Noun.slot` (`Service.served`). -/
theorem servedTuplesOf_slot {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {D : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec} {execA : ExactExecution cfg}
    (T : ServedMemoryTrace.ExactServedMemoryTrace q Λ cfg exec D execA)
    {root : Noun} {axis : ℕ} {child : Noun}
    (h : (root, axis, child) ∈ servedTuplesOf T) :
    Noun.slot axis root = some child := by
  unfold servedTuplesOf at h
  rw [List.mem_flatMap] at h
  obtain ⟨i, _, hsvc⟩ := h
  obtain ⟨s, _, htuple⟩ := List.mem_map.mp hsvc
  have hroot : s.root = root := congrArg Prod.fst htuple
  have haxis : s.axis = axis := congrArg (fun p => p.2.1) htuple
  have hchild : s.child = child := congrArg (fun p => p.2.2) htuple
  rw [← hroot, ← haxis, ← hchild]
  exact s.served

/-- **Identifying served nouns with skeleton slots.**  If an OP0/OP9 row's
slot triple is among `servedTuplesOf T`, `SkeletonSlotSemantics` follows from
`Service.served`. This is not `needs.served` length, not `axisNat`, and not
the paper `/(1,n)=n` base case -/
theorem slotSemantics_of_served {q Λ : ℕ} {cfg : ExactConfig F K}
    {exec : ExactExecution cfg}
    {D : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec} {execA : ExactExecution cfg}
    (T : ServedMemoryTrace.ExactServedMemoryTrace q Λ cfg exec D execA)
    (s : RowSkeleton)
    (hs0 : s.state = .s0 →
      (s.subject, P8Census.skeletonMemoryAxis s 1, s.evaluation) ∈ servedTuplesOf T)
    (hs9 : s.state = .s9 →
      (P8Census.skeletonSubformula s 0 .result,
       P8Census.skeletonMemoryAxis s 2,
       P8Census.skeletonSubformula s 1 .formula) ∈ servedTuplesOf T) :
    SkeletonSlotSemantics s where
  s0_slot h := servedTuplesOf_slot T (hs0 h)
  s9_slot h := servedTuplesOf_slot T (hs9 h)

/-! ## Strict row evidence with no assumed served lookup -/

/-- **B2, step 3 (canonical-fingerprint form).**  `StrictRowOperationalEvidence` assembled from the
record equations, the two Nock slot facts, and strict modular OP4. -/
theorem strictRowOperationalEvidence_of_slots {p : ℕ} {z : K} {s : RowSkeleton}
    (hrec : SkeletonRecordEquations s) (hslot : SkeletonSlotSemantics s)
    (hs4 : s.state = .s4 →
      (FieldEmbedding.lusFBy p (P8Census.skeletonSubformula s 0 .result)).isSome) :
    StrictRowOperationalEvidence p z s where
  s0_record := by
    intro h
    obtain ⟨hroot, hchild⟩ := hrec.s0_record h
    have haxis :
        P8Census.skeletonMemoryAxis s 1 =
          (s.memoryRecord (1 : Fin 3)
            (by simp [h, Nock.Framework.recordCount])).axis :=
      skeletonMemoryAxis_eq s 1 _
    exact realizesMemRec_of_bindMemRec (bindMemRec_encMemRec z _) hroot hchild haxis.symm
  s9_record := by
    intro h
    obtain ⟨hroot, hchild⟩ := hrec.s9_record h
    have haxis :
        P8Census.skeletonMemoryAxis s 2 =
          (s.memoryRecord (2 : Fin 3)
            (by simp [h, Nock.Framework.recordCount])).axis :=
      skeletonMemoryAxis_eq s 2 _
    exact realizesMemRec_of_bindMemRec (bindMemRec_encMemRec z _) hroot hchild haxis.symm
  s0_served := strict_s0_served_of_slot hslot
  s9_served := strict_s9_served_of_slot hslot
  s4_modular := hs4

/-- **The strict row evidence is exactly (records ∧ slots ∧ modular OP4).**  Nothing is lost by
building it that way, so `strictRowOperationalEvidence_of_slots` is not a weakening. -/
theorem slotSemantics_of_strictRowOperationalEvidence {p : ℕ} {z : K} {s : RowSkeleton}
    (ev : StrictRowOperationalEvidence p z s) : SkeletonSlotSemantics s :=
  skeletonSlotSemantics_of_served ev.s0_served ev.s9_served

/-! ## Production-record form: the two records of an actually scanned row

`RawSemanticAssembly.ScannedRowRecordRealization` states the record obligations at the *production*
table record rather than the canonical `encMemRec` fingerprint.  The strict production package below
is that, plus the served lookups, plus strict modular OP4 — i.e. the whole consumer-minimal contract
of a scanned row, with the served fields derived. -/

/-- Consumer-minimal strict evidence for a **scanned production row**. -/
structure StrictScannedRowEvidence (p : ℕ) (z : K) (s : RowSkeleton)
    (row : ComputeTable.State × ComputeTable.DTcomp K) : Prop where
  records : RawSemanticAssembly.ScannedRowRecordRealization z s row
  s0_served :
    s.state = .s0 →
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun s.subject 1)
        (P8Census.skeletonMemoryAxis s 1) s.evaluation
  s9_served :
    s.state = .s9 →
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun
          (P8Census.skeletonSubformula s 0 .result) 1)
        (P8Census.skeletonMemoryAxis s 2)
        (P8Census.skeletonSubformula s 1 .formula)
  s4_modular :
    s.state = .s4 →
      (FieldEmbedding.lusFBy p (P8Census.skeletonSubformula s 0 .result)).isSome

/-- **B2, step 3 (production-record form).**  A Packet-A2 row binding (which A2 derives from the
active-fingerprint scan plus the frame), the record equations, the Nock slot facts, and strict
modular OP4 give the whole scanned-row contract.  The served fields are *derived*. -/
theorem strictScannedRowEvidence_of_bindComputeRow {p : ℕ} {z : K} {s : RowSkeleton}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hrec : SkeletonRecordEquations s) (hslot : SkeletonSlotSemantics s)
    (hs4 : s.state = .s4 →
      (FieldEmbedding.lusFBy p (P8Census.skeletonSubformula s 0 .result)).isSome)
    (hbind : SemanticStrategy.BindComputeRow z s row) :
    StrictScannedRowEvidence p z s row where
  records :=
    { s0_record := fun h =>
        strict_s0_record_of_bound
          (skeletonOperationalCore_of_parts hrec hslot)
          h (RawSemanticAssembly.bindComputeRow_memRec hbind 1
            (by simp [h, Nock.Framework.recordCount]))
      s9_record := fun h =>
        strict_s9_record_of_bound
          (skeletonOperationalCore_of_parts hrec hslot)
          h (RawSemanticAssembly.bindComputeRow_memRec hbind 2
            (by simp [h, Nock.Framework.recordCount])) }
  s0_served := strict_s0_served_of_slot hslot
  s9_served := strict_s9_served_of_slot hslot
  s4_modular := hs4

/-- The canonical-fingerprint strict evidence is a projection of the scanned-row evidence, at any
seed: the scanned form is the stronger one. -/
theorem strictRowOperationalEvidence_of_scanned {p : ℕ} {z : K} {s : RowSkeleton}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hrec : SkeletonRecordEquations s)
    (ev : StrictScannedRowEvidence p z s row) :
    StrictRowOperationalEvidence p z s :=
  strictRowOperationalEvidence_of_slots hrec
    (skeletonSlotSemantics_of_served ev.s0_served ev.s9_served) ev.s4_modular

/-! ## The containment capstone with the served fields traded for slot facts

`RawSemanticAssembly.verifierGeneratedTopologyRawContainment` takes the whole operational core
`hop` as an explicit premise.  Below, that premise is replaced by its exact decomposition: record
equations and **Nock slot facts** (no recognizer language).
Since `skeletonOperationalCore_iff` is an `Iff`, this is the same theorem restated at the honest
premise. -/

section Containment

open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrictCommitment
open Nock.NockVMROM.Thm54.RawSemanticAssembly

variable [Fintype K] [DecidableEq K] [charRing : CharP K (ringChar K)]
variable {Λ : ℕ}

/-- **Verifier-generated-topology raw containment with the served lookups eliminated.**  Identical to
`RawSemanticAssembly.verifierGeneratedTopologyRawContainment` except that the operational premise is
now the row-local pair (record equations, Nock slot facts); no
`GlobalCarryAxis.ServedLookup` appears anywhere in the hypotheses. -/
theorem verifierGeneratedTopologyRawContainment_of_slotSemantics
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (C : SkeletonCommitment) (q : ℕ)
    (hclaim : C.skeleton.publicClaim = V.raw.claim)
    (hshape : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      ExecTreeShapeMatchesAt C (specializedProblem V.raw.timestamp z hz α lmb).exec)
    (hframe : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      RowFrameChecksAt z C (specializedProblem V.raw.timestamp z hz α lmb).exec)
    (hscan : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      ActiveFingerprintChecksAt z C (specializedProblem V.raw.timestamp z hz α lmb).exec)
    (census : EdgeComparisonCensus.CombinedSkeletonCensus K C.skeleton Λ)
    (hchar : NodeEncoding.StateTagChar K)
    (hq : 1 < q)
    (hqChar : q = ringChar K)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbound : C.skeleton.BoundedBy q)
    (hcombined : ProductionP8Containment.CombinedBoundedBy K q C.skeleton)
    (hrec : ∀ s ∈ computeSkeletonRows C.skeleton, SkeletonRecordEquations s)
    (hslot : ∀ s ∈ computeSkeletonRows C.skeleton, SkeletonSlotSemantics s)
    (hKp : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem V.raw.timestamp z hz α lmb).cfg.Ksz < ringChar K)
    (hProgCap : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem V.raw.timestamp z hz α lmb).exec.derivedRequestIO.length + 1 ≤
        2 ^ (specializedProblem V.raw.timestamp z hz α lmb).cfg.orbit.h)
    (hMemCap : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem V.raw.timestamp z hz α lmb).exec.derivedResponseIO.length + 1 ≤
        2 ^ (specializedProblem V.raw.timestamp z hz α lmb).cfg.orbit.h)
    (ω : JointCoins K) (lmb : K)
    (hacc : (productionStrategy_of_scan V C hclaim hshape hframe hscan).Accepts ω lmb)
    (hout : ω ∉ ProductionP8Containment.FailureUnion
      (productionStrategy_of_scan V C hclaim hshape hframe hscan) census lmb)
    (hlam : ∀ (hz : nprSeed ω ≠ 0) i,
      (((productionStrategy_of_scan V C hclaim hshape hframe hscan).verifier.familyAt ω lmb hz).exec.memoryPubAt i).lambda = ((productionStrategy_of_scan V C hclaim hshape hframe hscan).verifier.familyAt ω lmb hz).cfg.challenges.lam) :
    ProductionP8Containment.GenuineTargetAt
      (productionStrategy_of_scan V C hclaim hshape hframe hscan) q Λ ω lmb :=
  verifierGeneratedTopologyRawContainment V C q hclaim hshape hframe hscan census hchar hq
    hqChar hcast hbound hcombined
    (fun s hs => skeletonOperationalCore_of_parts (hrec s hs) (hslot s hs))
    hKp hProgCap hMemCap ω lmb hacc hout hlam

end Containment

end

end Nock.NockVMROM.Thm54.ServedLookupBridge

#print axioms Nock.NockVMROM.Thm54.ServedLookupBridge.strict_s0_served_of_slot
#print axioms Nock.NockVMROM.Thm54.ServedLookupBridge.strict_s9_served_of_slot
#print axioms Nock.NockVMROM.Thm54.ServedLookupBridge.skeletonSlotSemantics_of_served
#print axioms Nock.NockVMROM.Thm54.ServedLookupBridge.skeletonSlotSemantics_iff_served
#print axioms Nock.NockVMROM.Thm54.ServedLookupBridge.skeletonRecordEquations_of_core
#print axioms Nock.NockVMROM.Thm54.ServedLookupBridge.skeletonSlotSemantics_of_core
#print axioms Nock.NockVMROM.Thm54.ServedLookupBridge.skeletonOperationalCore_of_parts
#print axioms Nock.NockVMROM.Thm54.ServedLookupBridge.skeletonOperationalCore_iff
#print axioms Nock.NockVMROM.Thm54.ServedLookupBridge.servedTuplesOf_slot
#print axioms Nock.NockVMROM.Thm54.ServedLookupBridge.slotSemantics_of_served
#print axioms Nock.NockVMROM.Thm54.ServedLookupBridge.strictRowOperationalEvidence_of_slots
#print axioms Nock.NockVMROM.Thm54.ServedLookupBridge.slotSemantics_of_strictRowOperationalEvidence
#print axioms Nock.NockVMROM.Thm54.ServedLookupBridge.strictScannedRowEvidence_of_bindComputeRow
#print axioms Nock.NockVMROM.Thm54.ServedLookupBridge.strictRowOperationalEvidence_of_scanned
#print axioms
  Nock.NockVMROM.Thm54.ServedLookupBridge.verifierGeneratedTopologyRawContainment_of_slotSemantics
