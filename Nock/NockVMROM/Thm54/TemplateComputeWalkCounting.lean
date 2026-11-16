import Nock.NockVMROM.Thm54.TemplateRawJointSoundness

/-!
# Canonical compute-tree vector correspondence

The committed compute vectors below are obtained directly from the authoritative compute tree and
its BFS children.  Their `VecBFT` relation is therefore unconditional canonical-tree bookkeeping,
not walk-soundness evidence.  In the topology-enabled architecture this module contributes no
production failure event or soundness workload.  `Fcomp`/`RVT` remain separate topology/row
obligations.
-/

open scoped BigOperators Classical

namespace Nock.NockVMROM.Thm54.TemplateRawJointSoundness

open Nock Nock.Walk

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {p : ℕ} [CharP K p]

/-! ## Committed full-label vectors -/

/-- The full encoded compute label at one one-based BFS position, with the same zero convention
as `Walk.curCol` outside the committed prefix. -/
def committedComputeVector (R : RawPlusIOSegmentedFamily F K) (i : ℕ) :
    Fin R.compNodeWidth → K :=
  ((R.computeWalkRows[i - 1]?).map fun t => R.compNodeEncode t.label).getD 0

/-- The full encoded child label at one one-based parent/child position, with the same zero
convention as `Walk.chldCol`. -/
def committedComputeChildVector (R : RawPlusIOSegmentedFamily F K) (i l : ℕ) :
    Fin R.compNodeWidth → K :=
  (((R.computeWalkRows[i - 1]?).bind fun t => t.children[l - 1]?).map
    fun t => R.compNodeEncode t.label).getD 0

private theorem committed_curValsV_eq
    (R : RawPlusIOSegmentedFamily F K) :
    curValsV (committedComputeVector R) R.computeWalkRows.length =
      R.computeWalkRows.map (fun t => R.compNodeEncode t.label) := by
  apply List.ext_getElem (by simp)
  intro j hj hj'
  simp only [curValsV, List.getElem_map, List.getElem_range]
  have hjW : j < R.computeWalkRows.length := by
    simpa [curValsV] using hj
  simp [committedComputeVector, List.getElem?_eq_getElem hjW]

private theorem committed_blkValsV_eq
    (R : RawPlusIOSegmentedFamily F K) (j : ℕ)
    (hj : j < R.computeWalkRows.length) :
    blkValsV (committedComputeChildVector R) (foCol R.computeWalkRows) (j + 1) =
      (R.computeWalkRows.get ⟨j, hj⟩).children.map
        (fun t => R.compNodeEncode t.label) := by
  apply List.ext_getElem (by simp [blkValsV, foCol, hj])
  intro l hl hl'
  simp only [blkValsV, List.getElem_map, List.getElem_range]
  have hchild :
      l < (R.computeWalkRows.get ⟨j, hj⟩).children.length := by
    simpa [blkValsV, foCol, hj] using hl
  simp only [committedComputeChildVector, Nat.add_sub_cancel,
    List.getElem?_eq_getElem hj, Option.bind_some]
  change (Option.map (fun t => R.compNodeEncode t.label)
      (R.computeWalkRows.get ⟨j, hj⟩).children[l]?).getD 0 =
    R.compNodeEncode ((R.computeWalkRows.get ⟨j, hj⟩).children.get ⟨l, hchild⟩).label
  rw [List.getElem?_eq_getElem hchild]
  rfl

private theorem committed_flatBlksV_eq
    (R : RawPlusIOSegmentedFamily F K) :
    flatBlksV (committedComputeChildVector R) (foCol R.computeWalkRows)
        R.computeWalkRows.length =
      (R.computeWalkRows.flatMap NTree.children).map
        (fun t => R.compNodeEncode t.label) := by
  let f := fun t : NTree (ComputeTable.State × ComputeTable.DTcomp K) =>
    R.compNodeEncode t.label
  have hoptions :
      (List.range R.computeWalkRows.length).map
          (fun j => R.computeWalkRows[j]?) =
        R.computeWalkRows.map some := by
    apply List.ext_getElem?
    intro j
    by_cases hj : j < R.computeWalkRows.length
    · simp [hj]
    · have hle : R.computeWalkRows.length ≤ j := by omega
      simp [List.getElem?_eq_none hle]
      exact hle
  unfold flatBlksV
  calc
    (List.range R.computeWalkRows.length).flatMap
        (fun i => blkValsV (committedComputeChildVector R)
          (foCol R.computeWalkRows) (i + 1)) =
        (List.range R.computeWalkRows.length).flatMap
          (fun j => (R.computeWalkRows[j]?).map
            (fun t => t.children.map f) |>.getD []) := by
      apply List.flatMap_congr
      intro j hj
      have hj' : j < R.computeWalkRows.length := List.mem_range.mp hj
      rw [List.getElem?_eq_getElem hj']
      simpa [f] using committed_blkValsV_eq R j hj'
    _ = ((List.range R.computeWalkRows.length).map
          (fun j => R.computeWalkRows[j]?)).flatMap
          (fun ot => ot.map (fun t => t.children.map f) |>.getD []) := by
      rw [List.flatMap_map]
    _ = (R.computeWalkRows.map some).flatMap
          (fun ot => ot.map (fun t => t.children.map f) |>.getD []) := by
      rw [hoptions]
    _ = R.computeWalkRows.flatMap (fun t => t.children.map f) := by
      simp [List.flatMap_map]
    _ = (R.computeWalkRows.flatMap NTree.children).map f := by
      rw [List.map_flatMap]

/-- Canonical-tree correspondence: the node-vector list is definitionally the encoded BFS tree,
and the child-vector blocks are definitionally its encoded BFS children.  No acceptance,
challenge, `Fcomp`, `RVT`, or state-separation premise is involved. -/
theorem committedComputeVectors_vecBFT
    (R : RawPlusIOSegmentedFamily F K) :
    VecBFT (committedComputeVector R) (committedComputeChildVector R)
      (foCol R.computeWalkRows) R.cfg.compRows := by
  have hlen : R.computeWalkRows.length = R.cfg.compRows := by
    simpa [RawPlusIOSegmentedFamily.computeWalkRows] using R.exec.compute_bfs_length
  rw [← hlen]
  unfold VecBFT
  rw [committed_curValsV_eq, committed_flatBlksV_eq]
  let f := fun t : NTree (ComputeTable.State × ComputeTable.DTcomp K) =>
    R.compNodeEncode t.label
  have htail :
      R.computeWalkRows =
        R.exec.computeTree :: R.computeWalkRows.flatMap NTree.children := by
    exact walk_tail_eq R.exec.computeTree
  have hroot :
      committedComputeVector R 1 = f R.exec.computeTree := by
    change ((R.computeWalkRows[0]?).map
      (fun t => R.compNodeEncode t.label)).getD 0 =
        R.compNodeEncode R.exec.computeTree.label
    rw [htail]
    rfl
  rw [hroot]
  simpa [f] using congrArg (List.map f) htail

@[simp] theorem rlc_committedComputeVector
    (R : RawPlusIOSegmentedFamily F K) (i : ℕ) :
    rlc R.walkGamma (committedComputeVector R i) =
      curCol R.computeNodeVal R.computeWalkRows i := by
  generalize hopt : R.computeWalkRows[i - 1]? = opt
  cases opt with
  | none =>
      simp [committedComputeVector, curCol, hopt, rlc]
  | some t =>
      simp [committedComputeVector, RawPlusIOSegmentedFamily.computeNodeVal, curCol, hopt]

@[simp] theorem rlc_committedComputeChildVector
    (R : RawPlusIOSegmentedFamily F K) (i l : ℕ) :
    rlc R.walkGamma (committedComputeChildVector R i l) =
      chldCol R.computeNodeVal R.computeWalkRows i l := by
  generalize hopt :
    (R.computeWalkRows[i - 1]?.bind fun t => t.children[l - 1]?) = opt
  cases opt with
  | none =>
      simp [committedComputeChildVector, chldCol, hopt, rlc]
  | some t =>
      simp [committedComputeChildVector, RawPlusIOSegmentedFamily.computeNodeVal, chldCol, hopt]

/-- The exact regenerated-label failure: the committed full node vectors do not equal the root
vector followed by the committed child vectors in BFS order.  This is deliberately `VecBFT`, not
`ReconGoal`; no row relation (`Fcomp`) or `RVT` assertion is hidden in the event. -/
def ComputeRegeneratedLabelFailure (R : RawPlusIOSegmentedFamily F K) : Prop :=
  ¬ VecBFT (committedComputeVector R) (committedComputeChildVector R)
    (foCol R.computeWalkRows) R.cfg.compRows

/-- The alleged regenerated-label failure is impossible for vectors projected from the
authoritative tree itself. -/
@[simp] theorem not_computeRegeneratedLabelFailure
    (R : RawPlusIOSegmentedFamily F K) :
    ¬ ComputeRegeneratedLabelFailure R := by
  intro hfail
  exact hfail (committedComputeVectors_vecBFT R)

/-- Canonical-width version of the committed node vector. -/
def canonicalCommittedComputeVector
    (hchar : NodeEncoding.StateTagChar K)
    (R : RawPlusIOSegmentedFamily F K) (i : ℕ) :
    Fin NodeEncoding.computeNodeWidth → K :=
  ((R.computeWalkRows[i - 1]?).map fun t =>
    NodeEncoding.computeNodeEncode hchar t.label).getD 0

/-- Canonical-width version of the committed child vector. -/
def canonicalCommittedComputeChildVector
    (hchar : NodeEncoding.StateTagChar K)
    (R : RawPlusIOSegmentedFamily F K) (i l : ℕ) :
    Fin NodeEncoding.computeNodeWidth → K :=
  (((R.computeWalkRows[i - 1]?).bind fun t => t.children[l - 1]?).map fun t =>
    NodeEncoding.computeNodeEncode hchar t.label).getD 0

private theorem computeVectors_heq_of_encoder_heq
    {width₁ width₂ : ℕ}
    (rows : List (NTree (ComputeTable.State × ComputeTable.DTcomp K)))
    (enc₁ : (ComputeTable.State × ComputeTable.DTcomp K) → Fin width₁ → K)
    (enc₂ : (ComputeTable.State × ComputeTable.DTcomp K) → Fin width₂ → K)
    (hwidth : width₁ = width₂)
    (henc : HEq enc₁ enc₂) :
    HEq (fun i => ((rows[i - 1]?).map fun t => enc₁ t.label).getD 0)
        (fun i => ((rows[i - 1]?).map fun t => enc₂ t.label).getD 0) ∧
      HEq (fun i l => (((rows[i - 1]?).bind fun t =>
          t.children[l - 1]?).map fun t => enc₁ t.label).getD 0)
        (fun i l => (((rows[i - 1]?).bind fun t =>
          t.children[l - 1]?).map fun t => enc₂ t.label).getD 0) := by
  cases hwidth
  have henc' : enc₁ = enc₂ := eq_of_heq henc
  cases henc'
  exact ⟨HEq.rfl, HEq.rfl⟩

/-- Raw acceptance transports the raw encoder payload to the canonical state-tag encoder,
including both total vector functions. -/
theorem committedComputeVectors_canonical_of_rawAccepts
    (T : Strategy F K p) (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (hchar : NodeEncoding.StateTagChar K)
    (hraw : RawAccepts T.claim (T.familyAt ω lmb hz) ω (T.messageAt ω lmb hz)) :
    (T.familyAt ω lmb hz).compNodeWidth = NodeEncoding.computeNodeWidth ∧
      HEq (committedComputeVector (T.familyAt ω lmb hz))
        (canonicalCommittedComputeVector hchar (T.familyAt ω lmb hz)) ∧
      HEq (committedComputeChildVector (T.familyAt ω lmb hz))
        (canonicalCommittedComputeChildVector hchar (T.familyAt ω lmb hz)) := by
  have henc :=
    (T.messageAt ω lmb hz).canonicalNodeEncoders_of_accepts hchar hraw
  rcases henc with ⟨hwidth, hencode, _, _⟩
  have hvectors := computeVectors_heq_of_encoder_heq
    (T.familyAt ω lmb hz).computeWalkRows
    (T.familyAt ω lmb hz).compNodeEncode
    (NodeEncoding.computeNodeEncode hchar) hwidth hencode
  refine ⟨hwidth, ?_, ?_⟩
  · change HEq
      (fun i => (((T.familyAt ω lmb hz).computeWalkRows[i - 1]?).map fun t =>
        (T.familyAt ω lmb hz).compNodeEncode t.label).getD 0)
      (fun i => (((T.familyAt ω lmb hz).computeWalkRows[i - 1]?).map fun t =>
        NodeEncoding.computeNodeEncode hchar t.label).getD 0)
    exact hvectors.1
  · change HEq
      (fun i l => ((((T.familyAt ω lmb hz).computeWalkRows[i - 1]?).bind fun t =>
        t.children[l - 1]?).map fun t =>
          (T.familyAt ω lmb hz).compNodeEncode t.label).getD 0)
      (fun i l => ((((T.familyAt ω lmb hz).computeWalkRows[i - 1]?).bind fun t =>
        t.children[l - 1]?).map fun t =>
          NodeEncoding.computeNodeEncode hchar t.label).getD 0)
    exact hvectors.2

/-- Inserting later coins changes the walk challenges but not the committed vectors. -/
@[simp] theorem rlc_committedComputeVector_atCoins
    (C : AlphaMCommitment (F := F) (K := K) (p := p) T z hz alphaMValue lmb)
    (alphaCValue gammaValue : K) (i : ℕ) :
    rlc gammaValue (committedComputeVector C.familyData.base i) =
      curCol (C.familyData.atCoins alphaCValue gammaValue).computeNodeVal
        (C.familyData.atCoins alphaCValue gammaValue).computeWalkRows i := by
  change rlc (C.familyData.atCoins alphaCValue gammaValue).walkGamma
      (committedComputeVector (C.familyData.atCoins alphaCValue gammaValue) i) =
    curCol (C.familyData.atCoins alphaCValue gammaValue).computeNodeVal
      (C.familyData.atCoins alphaCValue gammaValue).computeWalkRows i
  exact rlc_committedComputeVector _ _

/-- Child-vector analogue of `rlc_committedComputeVector_atCoins`. -/
@[simp] theorem rlc_committedComputeChildVector_atCoins
    (C : AlphaMCommitment (F := F) (K := K) (p := p) T z hz alphaMValue lmb)
    (alphaCValue gammaValue : K) (i l : ℕ) :
    rlc gammaValue (committedComputeChildVector C.familyData.base i l) =
      chldCol (C.familyData.atCoins alphaCValue gammaValue).computeNodeVal
        (C.familyData.atCoins alphaCValue gammaValue).computeWalkRows i l := by
  change rlc (C.familyData.atCoins alphaCValue gammaValue).walkGamma
      (committedComputeChildVector (C.familyData.atCoins alphaCValue gammaValue) i l) =
    chldCol (C.familyData.atCoins alphaCValue gammaValue).computeNodeVal
      (C.familyData.atCoins alphaCValue gammaValue).computeWalkRows i l
  exact rlc_committedComputeChildVector _ _ _

/-! ## Quarantined generic bad fibers -/

section Finite

variable [Fintype K] [DecidableEq K]

/-- Its vectors are fixed by `C.familyData.base` before the pair is inspected; `(alphaC, gamma)` only
evaluate the displayed walk equations and never define the vector polynomial.  The filter is
proved empty below. -/
def specializedComputeBadFiber
    (C : AlphaMCommitment (F := F) (K := K) (p := p) T z hz alphaMValue lmb) :
    Finset (K × K) :=
  let R := C.familyData.base
  Finset.univ.filter fun pair =>
    (∃ ln count acc : ℕ → K,
      WalkSat
        (fun i => rlc pair.2 (committedComputeVector R i))
        (fun i l => rlc pair.2 (committedComputeChildVector R i l))
        (foCol R.computeWalkRows) ln count acc pair.1
        (rlc pair.2 (committedComputeVector R 1) * pair.1) pair.1
        R.cfg.compRows ∧
      acc R.cfg.compRows = 0) ∧
    ComputeRegeneratedLabelFailure R

/-- Put a fixed `(z, alphaM)` compute fiber into the canonical joint order
`((alphaC, gamma), (alphaM, z))`. -/
def fixedZAlphaMComputeEvent (z alphaMValue : K) (bad : Finset (K × K)) :
    Finset (JointCoins K) :=
  bad ×ˢ (({alphaMValue} : Finset K) ×ˢ ({z} : Finset K))

@[simp] theorem mem_fixedZAlphaMComputeEvent_iff
    (z alphaMValue : K) (bad : Finset (K × K)) (ω : JointCoins K) :
    ω ∈ fixedZAlphaMComputeEvent z alphaMValue bad ↔
      nprSeed ω = z ∧ alphaM ω = alphaMValue ∧ computeCoins ω ∈ bad := by
  rcases ω with ⟨⟨alphaCValue, gammaValue⟩, ⟨alphaM', z'⟩⟩
  simp [fixedZAlphaMComputeEvent, nprSeed, Thm54.alphaM, computeCoins, alphaC, gamma,
    eq_comm]
  aesop

theorem card_fixedZAlphaMComputeEvent
    (z alphaMValue : K) (bad : Finset (K × K)) :
    (fixedZAlphaMComputeEvent z alphaMValue bad).card = bad.card := by
  simp [fixedZAlphaMComputeEvent]

/-- It is not a production failure term and is proved equal to `∅` below. -/
def specializedComputeWalkFailureEvent (T : Strategy F K p) (lmb : K) :
    Finset (JointCoins K) :=
  (Finset.univ : Finset (K × K)).biUnion fun za =>
    if hz : za.1 ≠ 0 then
      fixedZAlphaMComputeEvent za.1 za.2
        (specializedComputeBadFiber (T.afterAlphaM za.1 hz za.2 lmb))
    else ∅

@[simp] theorem mem_specializedComputeWalkFailureEvent_iff
    (T : Strategy F K p) (lmb : K) (ω : JointCoins K) :
    ω ∈ specializedComputeWalkFailureEvent T lmb ↔
      ∃ hz : nprSeed ω ≠ 0,
        computeCoins ω ∈
          specializedComputeBadFiber
            (T.afterAlphaM (nprSeed ω) hz (alphaM ω) lmb) := by
  constructor
  · intro h
    rw [specializedComputeWalkFailureEvent] at h
    obtain ⟨za, _, hza⟩ := Finset.mem_biUnion.mp h
    split at hza
    · rename_i hz
      have hm := (mem_fixedZAlphaMComputeEvent_iff za.1 za.2 _ ω).1 hza
      rcases za with ⟨z, alphaMValue⟩
      rcases hm with ⟨hseed, halpha, hbad⟩
      dsimp at hz hseed halpha hbad ⊢
      subst z
      subst alphaMValue
      exact ⟨hz, by simpa only [proof_irrel_heq] using hbad⟩
    · simp at hza
  · rintro ⟨hz, hbad⟩
    rw [specializedComputeWalkFailureEvent]
    apply Finset.mem_biUnion.mpr
    refine ⟨(nprSeed ω, alphaM ω), Finset.mem_univ _, ?_⟩
    rw [dif_pos hz]
    exact (mem_fixedZAlphaMComputeEvent_iff _ _ _ _).2 ⟨rfl, rfl, hbad⟩

@[simp] theorem specializedComputeBadFiber_eq_empty
    (C : AlphaMCommitment (F := F) (K := K) (p := p) T z hz alphaMValue lmb) :
    specializedComputeBadFiber C = ∅ := by
  ext pair
  simp [specializedComputeBadFiber]

/-- The global event is empty because every fixed committed tree already satisfies its vector-BFT
correspondence.  It must not be inserted into the production soundness union. -/
@[simp] theorem specializedComputeWalkFailureEvent_eq_empty
    (T : Strategy F K p) (lmb : K) :
    specializedComputeWalkFailureEvent T lmb = ∅ := by
  ext ω
  simp [specializedComputeWalkFailureEvent, fixedZAlphaMComputeEvent]

/-! ## Quarantined generic counting adapters

They are not production evidence:
the concrete event above is empty before any counting theorem is applied.
-/

theorem specializedComputeBadFiber_card_le
    (C : AlphaMCommitment (F := F) (K := K) (p := p) T z hz alphaMValue lmb) :
    (specializedComputeBadFiber C).card ≤
      Fintype.card K * walkWorkload C.familyData.base.cfg.compRows
        C.familyData.base.compNodeWidth := by
  rw [specializedComputeBadFiber_eq_empty]
  simp

/-- Quarantined generic fiber-sum adapter.  The concrete production workload is zero below. -/
theorem specializedComputeWalkFailureEvent_card_le
    (T : Strategy F K p) (lmb : K) (workload : ℕ)
    (_hwork : ∀ z (hz : z ≠ 0) alphaMValue,
      walkWorkload
        (T.afterAlphaM z hz alphaMValue lmb).familyData.base.cfg.compRows
        (T.afterAlphaM z hz alphaMValue lmb).familyData.base.compNodeWidth ≤ workload) :
    (specializedComputeWalkFailureEvent T lmb).card ≤
      workload * Fintype.card K ^ 3 := by
  rw [specializedComputeWalkFailureEvent_eq_empty]
  simp

/-- Quarantined generic residual adapter. -/
theorem specializedComputeWalkCountingResidual
    (T : Strategy F K p) (lmb : K) (workload : ℕ)
    (hwork : ∀ z (hz : z ≠ 0) alphaMValue,
      walkWorkload
        (T.afterAlphaM z hz alphaMValue lmb).familyData.base.cfg.compRows
        (T.afterAlphaM z hz alphaMValue lmb).familyData.base.compNodeWidth ≤ workload) :
    SpecializedComputeWalkCountingResidual
      (specializedComputeWalkFailureEvent T lmb) workload :=
  specializedComputeWalkFailureEvent_card_le T lmb workload hwork

/-- Exact production cardinality: zero. -/
theorem specializedComputeWalkFailureEvent_card_eq_zero
    (T : Strategy F K p) (lmb : K) :
    (specializedComputeWalkFailureEvent T lmb).card = 0 := by
  rw [specializedComputeWalkFailureEvent_eq_empty]
  rfl

/-- Exact production workload is zero. -/
theorem specializedComputeWalkCountingResidual_zero
    (T : Strategy F K p) (lmb : K) :
    SpecializedComputeWalkCountingResidual
      (specializedComputeWalkFailureEvent T lmb)
      0 := by
  rw [specializedComputeWalkFailureEvent_eq_empty]
  simp [SpecializedComputeWalkCountingResidual]

/-! ## Raw acceptance and deterministic correspondence -/

/-- Quarantined compatibility lemma: the antecedent is impossible by
`not_computeRegeneratedLabelFailure`.  This is not a production failure-containment theorem. -/
theorem computeRegeneratedLabelFailure_mem_event_of_rawAccepts
    (T : Strategy F K p) (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (_hraw : RawAccepts T.claim (T.familyAt ω lmb hz) ω (T.messageAt ω lmb hz))
    (hfail :
      ComputeRegeneratedLabelFailure
        (T.alphaMCommitment ω lmb hz).familyData.base) :
    ω ∈ specializedComputeWalkFailureEvent T lmb := by
  exact (not_computeRegeneratedLabelFailure _ hfail).elim

/-- Final topology-enabled theorem.  Raw acceptance supplies the walk certificate, while `VecBFT`
is independent canonical-tree correspondence and needs no outside-event hypothesis.  This theorem
intentionally stops before `Fcomp`/`RVT`; topology RAP and row semantics handle those separately. -/
theorem computeWalkCertificate_and_vecBFT_of_rawAccepts
    (T : Strategy F K p) (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (hraw : RawAccepts T.claim (T.familyAt ω lmb hz) ω (T.messageAt ω lmb hz)) :
    (T.messageAt ω lmb hz).ComputeWalkCertificate ∧
      VecBFT
        (committedComputeVector
          (T.alphaMCommitment ω lmb hz).familyData.base)
        (committedComputeChildVector
          (T.alphaMCommitment ω lmb hz).familyData.base)
        (foCol (T.alphaMCommitment ω lmb hz).familyData.base.computeWalkRows)
        (T.alphaMCommitment ω lmb hz).familyData.base.cfg.compRows := by
  exact ⟨((T.messageAt ω lmb hz).computeWalkRAP_wholeTrace_iff).1 hraw.2.2.2.1,
    committedComputeVectors_vecBFT _⟩

end Finite

end

end Nock.NockVMROM.Thm54.TemplateRawJointSoundness

#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.committedComputeVectors_vecBFT
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.committedComputeVectors_canonical_of_rawAccepts
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.specializedComputeWalkFailureEvent_eq_empty
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.specializedComputeWalkCountingResidual_zero
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.computeWalkCertificate_and_vecBFT_of_rawAccepts
