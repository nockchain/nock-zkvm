import Nock.NockVMROM.Thm54.TemplateAxisCounting
import Nock.NockVMROM.Thm54.ProductionRawVerifier
import Nock.NockVMROM.Thm54.EdgeComparisonCensus

/-!
# Structural axis data from a fixed timestamp template

This file isolates the part of `ExactAxisStructuralRefinement` which really is fixed before
`alphaM`.  Natural timestamp exponents and a per-root intermediate partition are transported
through specialization; honest reconstruction is stable under the (possibly non-injective)
exponent recovery chosen by the exact carrier.

The final section records the genuine remaining boundary.  Fingerprint comparison censuses can
turn equal fingerprints into noun equalities, but noun equality is position-free.  The existing
crossing witness therefore prevents `ReadVerifyNested` from being derived from
`Fmem`/`childLinkMem`, canonical record binding, and such a census alone.
-/

open scoped Classical

namespace Nock.NockVMROM.Thm54.TemplateAxisStructure

open Nock Nock.Walk
open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.AxisBridge
open SemanticTimestampStrategy
open TemplateAxisCounting

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]

/-! ## Exponent reindexing preserves honest reconstruction -/

/-- Reindex only the natural timestamp labels of an axis tree. -/
def reindexAxisTree (f : ℕ → ℕ) : MTree K → MTree K
  | .halt => .halt
  | .decompose l r => .decompose (reindexAxisTree f l) (reindexAxisTree f r)
  | .read e c => .read (f e) (reindexAxisTree f c)
  | .verify e a c => .verify (f e) a (reindexAxisTree f c)

@[simp] theorem readExps_reindexAxisTree (f : ℕ → ℕ) (t : MTree K) :
    readExps (reindexAxisTree f t) = (readExps t).map f := by
  induction t with
  | halt => rfl
  | decompose l r ihl ihr =>
      simp [reindexAxisTree, readExps, ihl, ihr]
  | read e c ih => simp [reindexAxisTree, readExps, ih]
  | verify e a c ih => simp [reindexAxisTree, readExps, ih]

@[simp] theorem verifyExps_reindexAxisTree (f : ℕ → ℕ) (t : MTree K) :
    verifyExps (reindexAxisTree f t) = (verifyExps t).map f := by
  induction t with
  | halt => rfl
  | decompose l r ihl ihr =>
      simp [reindexAxisTree, verifyExps, ihl, ihr]
  | read e c ih => simp [reindexAxisTree, verifyExps, ih]
  | verify e a c ih => simp [reindexAxisTree, verifyExps, ih]

theorem nounShape_reindexAxisTree
    {subj : Noun} {t : MTree K} (h : NounShape subj t) (f : ℕ → ℕ) :
    NounShape subj (reindexAxisTree f t) := by
  induction h with
  | halt => exact .halt
  | decompose hl hr ihl ihr => exact .decompose ihl ihr
  | read h ih => exact .read ih
  | verify h ih => exact .verify ih

theorem readVerifyNested_reindexAxisTree
    (f : ℕ → ℕ) {t : MTree K} (h : ReadVerifyNested t) :
    ReadVerifyNested (reindexAxisTree f t) := by
  induction t with
  | halt => trivial
  | decompose l r ihl ihr =>
      exact ⟨ihl h.1, ihr h.2⟩
  | read e c ih =>
      refine ⟨?_, ih h.2⟩
      rw [verifyCount_eq_count, verifyExps_reindexAxisTree]
      have hmem : e ∈ verifyExps c := by
        rw [← List.count_pos_iff]
        rw [← verifyCount_eq_count]
        exact h.1
      have hmapped : f e ∈ (verifyExps c).map f :=
        List.mem_map.mpr ⟨e, hmem, rfl⟩
      have hpos : 0 < ((verifyExps c).map f).count (f e) :=
        List.count_pos_iff.mpr hmapped
      exact hpos
  | verify e a c ih =>
      exact ih h

/-- Reverse of `readVerifyNested_reindexAxisTree` when `f` is injective on the
tree's read and verify exponents -/
theorem readVerifyNested_of_reindexAxisTree
    (f : ℕ → ℕ) {t : MTree K}
    (hinj : ∀ x y,
      (x ∈ readExps t ∨ x ∈ verifyExps t) →
        (y ∈ readExps t ∨ y ∈ verifyExps t) → f x = f y → x = y)
    (h : ReadVerifyNested (reindexAxisTree f t)) :
    ReadVerifyNested t := by
  induction t with
  | halt => trivial
  | decompose l r ihl ihr =>
      refine ⟨ihl (fun x y hx hy => hinj x y ?xl ?yl) h.1,
        ihr (fun x y hx hy => hinj x y ?xr ?yr) h.2⟩
      · exact hx.elim (fun hx => Or.inl (List.mem_append.mpr (Or.inl hx)))
          (fun hx => Or.inr (List.mem_append.mpr (Or.inl hx)))
      · exact hy.elim (fun hy => Or.inl (List.mem_append.mpr (Or.inl hy)))
          (fun hy => Or.inr (List.mem_append.mpr (Or.inl hy)))
      · exact hx.elim (fun hx => Or.inl (List.mem_append.mpr (Or.inr hx)))
          (fun hx => Or.inr (List.mem_append.mpr (Or.inr hx)))
      · exact hy.elim (fun hy => Or.inl (List.mem_append.mpr (Or.inr hy)))
          (fun hy => Or.inr (List.mem_append.mpr (Or.inr hy)))
  | read e c ih =>
      refine ⟨?_, ih (fun x y hx hy => hinj x y ?xc ?yc) h.2⟩
      · have hmem : f e ∈ (verifyExps c).map f := by
          have hpos : 0 < verifyCount (f e) (reindexAxisTree f c) :=
            Nat.succ_le_iff.mp h.1
          rw [verifyCount_eq_count, verifyExps_reindexAxisTree] at hpos
          exact List.count_pos_iff.mp hpos
        obtain ⟨e', he', hf⟩ := List.mem_map.mp hmem
        have heq : e' = e :=
          hinj e' e (Or.inr he') (Or.inl (by simp [readExps])) hf
        subst e'
        rw [verifyCount_eq_count]
        exact Nat.succ_le_iff.mpr (List.count_pos_iff.mpr he')
      · exact hx.elim (fun hx => Or.inl (List.mem_cons_of_mem e hx)) Or.inr
      · exact hy.elim (fun hy => Or.inl (List.mem_cons_of_mem e hy)) Or.inr
  | verify e a c ih =>
      exact ih (fun x y hx hy => hinj x y
        (hx.elim Or.inl (fun hx => Or.inr (List.mem_cons_of_mem e hx)))
        (hy.elim Or.inl (fun hy => Or.inr (List.mem_cons_of_mem e hy)))) h

theorem honestRecon_reindexAxisTree
    {subj : Noun} {t : MTree K} (h : HonestRecon subj t) (f : ℕ → ℕ) :
    HonestRecon subj (reindexAxisTree f t) :=
  ⟨nounShape_reindexAxisTree h.1 f, readVerifyNested_reindexAxisTree f h.2⟩

/-- The recovered specialized tree is just the fixed template tree with its exponents reindexed. -/
theorem recoveredAxisTree_eq_reindexAxisTree (α : K)
    (t : NTree (MemoryRowTemplate (K := K))) :
    recoveredAxisTree α t =
      reindexAxisTree (recoveredExponent α) (templateAxisTree t) := by
  let P := fun t : NTree (MemoryRowTemplate (K := K)) =>
    recoveredAxisTree α t =
      reindexAxisTree (recoveredExponent α) (templateAxisTree t)
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro row children ih
    simp only [P]
    cases hs : row.timestamp.state with
    | decompose =>
        rcases children with _ | ⟨l, rest⟩
        · simp [templateAxisTree, recoveredAxisTree, reindexAxisTree, hs]
        · rcases rest with _ | ⟨r, tail⟩
          · simp [templateAxisTree, recoveredAxisTree, reindexAxisTree, hs]
          · rcases tail with _ | ⟨x, xs⟩
            · have hl := ih l (by simp)
              have hr := ih r (by simp)
              simp only [P] at hl hr
              simp [templateAxisTree, recoveredAxisTree, reindexAxisTree, hs, hl, hr]
            · simp [templateAxisTree, recoveredAxisTree, reindexAxisTree, hs]
    | halt =>
        simp [templateAxisTree, recoveredAxisTree, reindexAxisTree, hs]
    | read_root =>
        rcases children with _ | ⟨c, rest⟩
        · simp [templateAxisTree, recoveredAxisTree, reindexAxisTree, hs]
        · rcases rest with _ | ⟨x, xs⟩
          · have hc := ih c (by simp)
            simp only [P] at hc
            simp [templateAxisTree, recoveredAxisTree, reindexAxisTree,
              recoveredExponent, hs, hc]
          · simp [templateAxisTree, recoveredAxisTree, reindexAxisTree, hs]
    | verify_child =>
        rcases children with _ | ⟨c, rest⟩
        · simp [templateAxisTree, recoveredAxisTree, reindexAxisTree, hs]
        · rcases rest with _ | ⟨x, xs⟩
          · have hc := ih c (by simp)
            simp only [P] at hc
            simp [templateAxisTree, recoveredAxisTree, reindexAxisTree,
              recoveredExponent, hs, hc]
          · simp [templateAxisTree, recoveredAxisTree, reindexAxisTree, hs]
  · intro c hc
    simp at hc
  · intro head tail ihHead ihTail c hc
    simp only [List.mem_cons] at hc
    exact hc.elim (fun h => h ▸ ihHead) (ihTail c)

theorem honestRecon_recoveredAxisTree
    (α : K) (t : NTree (MemoryRowTemplate (K := K))) {subj : Noun}
    (h : HonestRecon subj (templateAxisTree t)) :
    HonestRecon subj (recoveredAxisTree α t) := by
  rw [recoveredAxisTree_eq_reindexAxisTree]
  exact honestRecon_reindexAxisTree h _

theorem exactAxisTree_specialize
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (α : K) {lmb : K} (i : Fin T.kMem) :
    exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i =
      recoveredAxisTree α (templateMemoryTreeAt E i) := by
  simp only [exactAxisTree, ExactConfigTemplate.specialize_alpha]
  rw [specializeA_memoryTreeAt E α i, ofNTree_specialize_toMTree]

theorem recoveredExponent_pow (α : K) (e : ℕ) :
    α ^ recoveredExponent α e = α ^ e := by
  symm
  exact timestampExp_spec
    (show TimestampClosedAt α (α ^ e) from ⟨e, rfl⟩)

/-- Recovered exponents are injective on the paper uniqueness window
`e < orderOf α`. -/
theorem recoveredExponent_injOn_Iio_orderOf (α : K) :
    Set.InjOn (recoveredExponent α) (Set.Iio (orderOf α)) := by
  intro e₁ h₁ e₂ h₂ hrec
  have hpow : α ^ e₁ = α ^ e₂ := by
    rw [← recoveredExponent_pow α e₁, hrec, recoveredExponent_pow α e₂]
  exact pow_injOn_Iio_orderOf (Set.mem_Iio.mp h₁) (Set.mem_Iio.mp h₂) hpow

theorem specialized_readTimestamps_eq_template
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (α : K) {lmb : K} (i : Fin T.kMem) :
    (readExps (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i)).map
        (fun e => α ^ e) =
      (readExps (templateAxisTree (templateMemoryTreeAt E i))).map
        (fun e => α ^ e) := by
  rw [exactAxisTree_specialize E α i, recoveredAxisTree_eq_reindexAxisTree]
  simp [List.map_map, Function.comp_def, recoveredExponent_pow]

theorem specialized_verifyTimestamps_eq_template
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (α : K) {lmb : K} (i : Fin T.kMem) :
    (verifyExps (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i)).map
        (fun e => α ^ e) =
      (verifyExps (templateAxisTree (templateMemoryTreeAt E i))).map
        (fun e => α ^ e) := by
  rw [exactAxisTree_specialize E α i, recoveredAxisTree_eq_reindexAxisTree]
  simp [List.map_map, Function.comp_def, recoveredExponent_pow]

/-- Specialization transports the α-free aggregate request multiset to the one global
`intermediate` request multiset of the exact forest. -/
theorem forestReadTimestamps_specialize
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) {lmb : K} :
    forestReadTimestamps (T.specialize α lmb) (E.specializeA α lmb) =
      (templateForestReadExps E).map (fun e => α ^ e) := by
  rw [templateForestReadExps, List.map_flatMap]
  refine List.flatMap_congr ?_
  intro i _
  exact specialized_readTimestamps_eq_template E α i

/-- Specialization transports the α-free aggregate response multiset to the one global
`intermediate` response multiset of the exact forest. -/
theorem forestVerifyTimestamps_specialize
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) {lmb : K} :
    forestVerifyTimestamps (T.specialize α lmb) (E.specializeA α lmb) =
      (templateForestVerifyExps E).map (fun e => α ^ e) := by
  rw [templateForestVerifyExps, List.map_flatMap]
  refine List.flatMap_congr ?_
  intro i _
  exact specialized_verifyTimestamps_eq_template E α i

theorem mem_templateForestReadExps
    {T : ExactConfigTemplate F K} {E : ExactExecutionTemplate T} {e : ℕ}
    (he : e ∈ templateForestReadExps E) :
    ∃ i : Fin T.kMem, e ∈ readExps (templateAxisTree (templateMemoryTreeAt E i)) := by
  rw [templateForestReadExps, List.mem_flatMap] at he
  obtain ⟨i, -, hi⟩ := he
  exact ⟨i, hi⟩

theorem mem_templateForestVerifyExps
    {T : ExactConfigTemplate F K} {E : ExactExecutionTemplate T} {e : ℕ}
    (he : e ∈ templateForestVerifyExps E) :
    ∃ i : Fin T.kMem, e ∈ verifyExps (templateAxisTree (templateMemoryTreeAt E i)) := by
  rw [templateForestVerifyExps, List.mem_flatMap] at he
  obtain ⟨i, -, hi⟩ := he
  exact ⟨i, hi⟩

/-! ## Natural root partition and exact structural refinement -/

/-- Mapping an `LmIO` relation is sound when the map is injective on its request support. -/
theorem lmIO_map_of_injective_on_requests
    {R S : Type*} [DecidableEq R] [DecidableEq S]
    (Ksz : ℕ) (requests responses : List R) (f : R → S)
    (h : IO.LmIO Ksz requests responses)
    (hinj : ∀ x ∈ requests, ∀ y ∈ requests, f x = f y → x = y) :
    IO.LmIO Ksz (requests.map f) (responses.map f) := by
  obtain ⟨hrange, uniq, hlen, huniq, hmem, hperm⟩ := h
  refine ⟨by simpa using hrange, uniq.map f, by simpa using hlen, ?_, ?_, hperm.map f⟩
  · apply huniq.map_on
    intro x hx y hy hxy
    exact hinj x ((hmem x).2 hx) y ((hmem y).2 hy) hxy
  · intro y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact List.mem_map.mpr ⟨x, (hmem x).1 hx, rfl⟩
    · intro hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact List.mem_map.mpr ⟨x, (hmem x).2 hx, rfl⟩

/-- Reverse of `lmIO_map_of_injective_on_requests` when `f` is injective on
the union of requests and responses -/
theorem lmIO_of_map_injective_on_union
    {R S : Type*} [DecidableEq R] [DecidableEq S]
    (Ksz : ℕ) (requests responses : List R) (f : R → S)
    (h : IO.LmIO Ksz (requests.map f) (responses.map f))
    (hinj : ∀ x ∈ requests ++ responses, ∀ y ∈ requests ++ responses,
      f x = f y → x = y) :
    IO.LmIO Ksz requests responses := by
  rw [IO.LmIO_iff] at h ⊢
  refine ⟨by simpa using h.1, by simpa using h.2.1, List.Nodup.of_map f h.2.2.1, ?_⟩
  ext x
  constructor
  · intro hx
    have hfx : f x ∈ (requests.map f).toFinset :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, List.mem_toFinset.mp hx, rfl⟩)
    have hfy : f x ∈ (responses.map f).toFinset := by
      rw [← h.2.2.2]; exact hfx
    obtain ⟨y, hy, hfxy⟩ := List.mem_map.mp (List.mem_toFinset.mp hfy)
    have heq : x = y :=
      hinj x (List.mem_append.mpr (Or.inl (List.mem_toFinset.mp hx)))
        y (List.mem_append.mpr (Or.inr hy)) hfxy.symm
    subst y
    exact List.mem_toFinset.mpr hy
  · intro hx
    have hfx : f x ∈ (responses.map f).toFinset :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, List.mem_toFinset.mp hx, rfl⟩)
    have hfy : f x ∈ (requests.map f).toFinset := by
      rw [h.2.2.2]; exact hfx
    obtain ⟨y, hy, hfxy⟩ := List.mem_map.mp (List.mem_toFinset.mp hfy)
    have heq : x = y :=
      hinj x (List.mem_append.mpr (Or.inr (List.mem_toFinset.mp hx)))
        y (List.mem_append.mpr (Or.inl hy)) hfxy.symm
    subst y
    exact List.mem_toFinset.mpr hy

/-- Exactly the α-free data needed by the structural axis connector.

`forestPartition` is the paper's *one* `intermediate` condition, carried on the aggregate multiset of
the whole committed forest rather than on each seeded root; the paper seeds
record-free atom subjects into that same forest.  `honesty` includes the positional
read-before-verify fact which a noun-comparison census cannot recover. -/
structure AlphaFreeStructuralData
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) where
  subjects : Fin T.kMem → Noun
  honesty :
    ∀ i, HonestRecon (subjects i)
      (templateAxisTree (templateMemoryTreeAt E i))
  timestampBound : ℕ
  readExponentBound :
    ∀ i e, e ∈ readExps (templateAxisTree (templateMemoryTreeAt E i)) →
      e < timestampBound
  readExponentsNodup :
    ∀ i, (readExps (templateAxisTree (templateMemoryTreeAt E i))).Nodup
  forestPartition :
    IO.LmIO T.Ksz (templateForestReadExps E) (templateForestVerifyExps E)

namespace AlphaFreeStructuralData

def exactMemoryHonestReconstruction
    {T : ExactConfigTemplate F K} {E : ExactExecutionTemplate T}
    (D : AlphaFreeStructuralData E) (α lmb : K) :
    ExactMemoryHonestReconstruction (T.specialize α lmb) (E.specializeA α lmb) D.subjects := by
  intro i
  rw [exactAxisTree_specialize E α i]
  exact honestRecon_recoveredAxisTree α _ (D.honesty i)

theorem readTimestamps_nodup
    {T : ExactConfigTemplate F K} {E : ExactExecutionTemplate T}
    (D : AlphaFreeStructuralData E) (α : K) {lmb : K}
    (horder : D.timestampBound ≤ orderOf α) :
    ∀ i, ((readExps (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i)).map
      (fun e => α ^ e)).Nodup := by
  intro i
  rw [specialized_readTimestamps_eq_template E α i]
  apply (D.readExponentsNodup i).map_on
  intro x hx y hy hpow
  exact (pow_injOn_Iio_orderOf (x := α))
    (lt_of_lt_of_le (D.readExponentBound i x hx) horder)
    (lt_of_lt_of_le (D.readExponentBound i y hy) horder) hpow

theorem intermediateMatching
    {T : ExactConfigTemplate F K} {E : ExactExecutionTemplate T}
    (D : AlphaFreeStructuralData E) (α : K) {lmb : K}
    (horder : D.timestampBound ≤ orderOf α) :
    IO.LmIO T.Ksz
      (forestReadTimestamps (T.specialize α lmb) (E.specializeA α lmb))
      (forestVerifyTimestamps (T.specialize α lmb) (E.specializeA α lmb)) := by
  rw [forestReadTimestamps_specialize E α, forestVerifyTimestamps_specialize E α]
  apply lmIO_map_of_injective_on_requests T.Ksz _ _ (fun e => α ^ e)
    D.forestPartition
  intro x hx y hy hpow
  obtain ⟨ix, hix⟩ := mem_templateForestReadExps hx
  obtain ⟨iy, hiy⟩ := mem_templateForestReadExps hy
  exact (pow_injOn_Iio_orderOf (x := α))
    (lt_of_lt_of_le (D.readExponentBound ix x hix) horder)
    (lt_of_lt_of_le (D.readExponentBound iy y hiy) horder) hpow

/-- Exact structural refinement for every no-wrap specialization.  It has no acceptance,
`root_accepts`, axis-validity, evaluator, or target premise. -/
def exactAxisStructuralRefinement
    {T : ExactConfigTemplate F K} {E : ExactExecutionTemplate T}
    (D : AlphaFreeStructuralData E) (α lmb : K)
    (horder : D.timestampBound ≤ orderOf α) :
    ExactAxisStructuralRefinement (T.specialize α lmb) (E.specializeA α lmb) :=
  ExactAxisStructuralRefinement.ofHonestReconstruction
    (D.exactMemoryHonestReconstruction α lmb)
    (D.readTimestamps_nodup α horder)
    (D.intermediateMatching α horder)

end AlphaFreeStructuralData

/-- Strategy-level spelling on the a-bearing view `specializedExecA`. -/
theorem strategy_exactAxisStructuralRefinement
    {p : ℕ} [CharP K p]
    (T : TemplateRawJointSoundness.Strategy F K p)
    (z : K) (hz : z ≠ 0) (α lmb : K)
    (D : AlphaFreeStructuralData
      (T.timestamp.afterSeed ⟨z, hz⟩).executionTemplate)
    (horder : D.timestampBound ≤ orderOf α) :
    ExactAxisStructuralRefinement
      (TemplateRawJointSoundness.specializedProblem T.timestamp z hz α lmb).cfg
      (TemplateRawJointSoundness.specializedExecA T.timestamp z hz α lmb) := by
  simpa [TemplateRawJointSoundness.specializedProblem,
    TemplateRawJointSoundness.specializedExecA] using
    D.exactAxisStructuralRefinement α lmb horder

/-! ## Reverse transport from specialized structural refinement

The specialized `ExactAxisStructuralRefinement` is already on an honest execution.
Read-exponent uniqueness on the α-free template follows from timestamp uniqueness
without a no-wrap hypothesis.  Ancestry and
the one global `intermediate` matching reverse only inside the paper uniqueness window `e < orderOf α`,
whose paper content is the closed-form timestamps `z^i`, the
IO/`intermediate` accounting with `z^i` uniqueness, and the
negligibility window. -/

theorem template_readExps_nodup_of_specialized
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) {lmb : K}
    (R : ExactAxisStructuralRefinement (T.specialize α lmb) (E.specializeA α lmb))
    (i : Fin T.kMem) :
    (readExps (templateAxisTree (templateMemoryTreeAt E i))).Nodup := by
  have hts : ((readExps (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i)).map
      (fun e => α ^ e)).Nodup := by
    simpa [ExactConfigTemplate.specialize_alpha] using R.read_timestamps_nodup i
  rw [specialized_readTimestamps_eq_template E α i] at hts
  exact List.Nodup.of_map _ hts

theorem template_readVerifyNested_of_specialized
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) {lmb : K}
    (R : ExactAxisStructuralRefinement (T.specialize α lmb) (E.specializeA α lmb))
    (hread : ∀ i e,
      e ∈ readExps (templateAxisTree (templateMemoryTreeAt E i)) → e < orderOf α)
    (hverify : ∀ i e,
      e ∈ verifyExps (templateAxisTree (templateMemoryTreeAt E i)) → e < orderOf α)
    (i : Fin T.kMem) :
    ReadVerifyNested (templateAxisTree (templateMemoryTreeAt E i)) := by
  have hanc : ReadVerifyNested
      (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i) := R.ancestry i
  rw [exactAxisTree_specialize E α i, recoveredAxisTree_eq_reindexAxisTree] at hanc
  refine readVerifyNested_of_reindexAxisTree (recoveredExponent α) ?_ hanc
  intro x y hx hy hrec
  have hxlt : x < orderOf α :=
    hx.elim (hread i x) (hverify i x)
  have hylt : y < orderOf α :=
    hy.elim (hread i y) (hverify i y)
  exact recoveredExponent_injOn_Iio_orderOf α (Set.mem_Iio.mpr hxlt)
    (Set.mem_Iio.mpr hylt) hrec

theorem template_forestPartition_of_specialized
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) {lmb : K}
    (R : ExactAxisStructuralRefinement (T.specialize α lmb) (E.specializeA α lmb))
    (hread : ∀ e, e ∈ templateForestReadExps E → e < orderOf α)
    (hverify : ∀ e, e ∈ templateForestVerifyExps E → e < orderOf α) :
    IO.LmIO T.Ksz (templateForestReadExps E) (templateForestVerifyExps E) := by
  have hmatch : IO.LmIO (T.specialize α lmb).Ksz
      (forestReadTimestamps (T.specialize α lmb) (E.specializeA α lmb))
      (forestVerifyTimestamps (T.specialize α lmb) (E.specializeA α lmb)) :=
    R.intermediate_matching
  rw [forestReadTimestamps_specialize E α,
    forestVerifyTimestamps_specialize E α] at hmatch
  change IO.LmIO T.Ksz _ _ at hmatch
  refine lmIO_of_map_injective_on_union T.Ksz _ _ (fun e => α ^ e) hmatch ?_
  intro x hx y hy hpow
  have hxlt : x < orderOf α := by
    rw [List.mem_append] at hx
    exact hx.elim (hread x) (hverify x)
  have hylt : y < orderOf α := by
    rw [List.mem_append] at hy
    exact hy.elim (hread y) (hverify y)
  exact pow_injOn_Iio_orderOf hxlt hylt hpow

/-! ## Additional fixed memory comparison census -/

private def childParentOrSelf
    (node : NTree SemanticStrategy.MemoryRowSkeleton) (i : Fin 2) : Noun :=
  (node.childOpt i).map (fun child => child.label.parent) |>.getD node.label.parent

private def activeRecordRootOrParent
    (row : SemanticStrategy.MemoryRowSkeleton) : Noun :=
  if h : memoryMemRecKind row.state = .active then (row.memoryRecord h).root else row.parent

private def activeRecordChildOrParent
    (row : SemanticStrategy.MemoryRowSkeleton) : Noun :=
  if h : memoryMemRecKind row.state = .active then (row.memoryRecord h).child else row.parent

/-- Five occurrence-preserving comparisons per semantic memory node: both ordered edges, both
live-record noun coordinates, and the two child occurrences. -/
def memoryHonestyNodePairs
    (node : NTree SemanticStrategy.MemoryRowSkeleton) : List (Noun × Noun) :=
  [ (node.label.parent, childParentOrSelf node 0),
    (node.label.parent, childParentOrSelf node 1),
    (activeRecordRootOrParent node.label, node.label.parent),
    (activeRecordChildOrParent node.label, node.label.parent),
    (childParentOrSelf node 0, childParentOrSelf node 1) ]

def memoryHonestyPairs (S : SemanticStrategy.SemanticSkeleton) :
    List (Noun × Noun) :=
  (bfsForest S.memoryForest).flatMap memoryHonestyNodePairs

@[simp] theorem memoryHonestyNodePairs_length
    (node : NTree SemanticStrategy.MemoryRowSkeleton) :
    (memoryHonestyNodePairs node).length = 5 :=
  rfl

theorem memoryHonestyPairs_length (S : SemanticStrategy.SemanticSkeleton) :
    (memoryHonestyPairs S).length =
      5 * (SemanticStrategy.memorySkeletonRows S).length := by
  have h :
      ∀ xs : List (NTree SemanticStrategy.MemoryRowSkeleton),
        (xs.flatMap memoryHonestyNodePairs).length = 5 * xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
        simp [memoryHonestyNodePairs, ih, Nat.mul_add]
  simpa [memoryHonestyPairs, SemanticStrategy.memorySkeletonRows] using
    h (bfsForest S.memoryForest)

def extendedCombinedPairs
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)) :
    List (Noun × Noun) :=
  EdgeComparisonCensus.combinedPairs T ++ memoryHonestyPairs T.skeleton

structure ExtendedCombinedBoundCensus
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)) (Λ : ℕ) : Prop where
  core : EdgeComparisonCensus.CombinedBoundCensus T Λ
  memory_leaves_bounded :
    ∀ pair ∈ memoryHonestyPairs T.skeleton,
      pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ

namespace ExtendedCombinedBoundCensus

def census
    {T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)} {Λ : ℕ}
    (C : ExtendedCombinedBoundCensus T Λ) : ComparisonCensus Λ :=
  ComparisonCensus.ofPairList (extendedCombinedPairs T) (by
    intro pair hp
    rw [extendedCombinedPairs, List.mem_append] at hp
    exact hp.elim
      (fun h => by
        have hcoreBound :
            ∀ pair ∈ EdgeComparisonCensus.combinedPairs T,
              pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ := by
          intro corePair hcore
          rw [EdgeComparisonCensus.combinedPairs, List.mem_append] at hcore
          exact hcore.elim
            (C.core.p8.leaves_bounded corePair)
            (C.core.edges.leaves_bounded corePair)
        obtain ⟨i, hi⟩ :=
          ComparisonCensus.exists_pair_of_mem
            (EdgeComparisonCensus.combinedPairs T)
            hcoreBound h
        have hb := C.core.census.leaves_bounded i
        change
          ((EdgeComparisonCensus.combinedPairs T).get i).1.leaves ≤ Λ ∧
            ((EdgeComparisonCensus.combinedPairs T).get i).2.leaves ≤ Λ at hb
        change (EdgeComparisonCensus.combinedPairs T).get i = pair at hi
        rw [hi] at hb
        exact hb)
      (C.memory_leaves_bounded pair))

@[simp] theorem census_count
    {T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)} {Λ : ℕ}
    (C : ExtendedCombinedBoundCensus T Λ) :
    C.census.count =
      C.core.census.count + (memoryHonestyPairs T.skeleton).length := by
  simp [census, extendedCombinedPairs,
    EdgeComparisonCensus.combinedPairs,
    EdgeComparisonCensus.CombinedBoundCensus.census]
  omega

/-- Combined fixed NPR workload, now including five memory comparisons per memory row. -/
theorem count_le
    {T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)} {Λ : ℕ}
    (C : ExtendedCombinedBoundCensus T Λ) :
    C.census.count ≤
      3 + 19 * (SemanticStrategy.computeSkeletonRows T.skeleton).length +
        5 * (SemanticStrategy.memorySkeletonRows T.skeleton).length := by
  have hcore := C.core.count_le
  rw [census_count, memoryHonestyPairs_length]
  omega

theorem memory_pair_lookup
    {T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)} {Λ : ℕ}
    (C : ExtendedCombinedBoundCensus T Λ)
    {pair : Noun × Noun} (hp : pair ∈ memoryHonestyPairs T.skeleton) :
    ∃ i : Fin C.census.count, C.census.pair i = pair :=
  ComparisonCensus.exists_pair_of_mem _ _ (by
    rw [extendedCombinedPairs, List.mem_append]
    exact Or.inr hp)

theorem memory_pair_noun_eq
    {T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)} {Λ q : ℕ}
    (C : ExtendedCombinedBoundCensus T Λ)
    (z : K) (hgood : z ∉ C.census.badSeeds (K := K))
    {pair : Noun × Noun} (hp : pair ∈ memoryHonestyPairs T.skeleton)
    (henc : GlobalCarryRecognizer.enc z pair.1 =
      GlobalCarryRecognizer.enc z pair.2)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hleft : FieldEmbedding.BoundedBy q pair.1)
    (hright : FieldEmbedding.BoundedBy q pair.2) :
    pair.1 = pair.2 := by
  obtain ⟨i, hi⟩ := C.memory_pair_lookup hp
  have hsep := P8Census.sepSeed_of_not_mem_badSeeds C.census z hgood i
  apply GlobalCarryRecognizer.noun_eq_of_enc_eq z _ _ (by simpa [hi] using hsep)
    hcast hleft hright
  exact henc

theorem badSeeds_card_le
    {T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)} {Λ : ℕ}
    (C : ExtendedCombinedBoundCensus T Λ) :
    (C.census.badSeeds (K := K)).card ≤
      (3 + 19 * (SemanticStrategy.computeSkeletonRows T.skeleton).length +
        5 * (SemanticStrategy.memorySkeletonRows T.skeleton).length) *
          (2 * Λ - 1) :=
  C.census.badSeeds_card_le.trans
    (Nat.mul_le_mul_right (2 * Λ - 1) C.count_le)

end ExtendedCombinedBoundCensus

/-! ## The genuine positional boundary -/

/-- Noun shape, hence all noun equalities obtainable from an NPR census, does not imply honest
reconstruction.  The missing conjunct is exactly `ReadVerifyNested`. -/
theorem nounShape_not_enough_for_honestRecon :
    ∃ (subj : Noun) (t : MTree K),
      NounShape subj t ∧ ¬ HonestRecon subj t := by
  let t : MTree K :=
    .decompose (.read 0 (.decompose .halt .halt)) (.verify 0 (2 : K) .halt)
  refine ⟨canonNoun t, t, nounShape_canonNoun t, ?_⟩
  intro h
  exact (readVerifyNested_wall (K := K) 0).2.2.2.2.2.2.2.2.2 h.2

end

end Nock.NockVMROM.Thm54.TemplateAxisStructure

#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.honestRecon_recoveredAxisTree
#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.AlphaFreeStructuralData.exactMemoryHonestReconstruction
#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.AlphaFreeStructuralData.exactAxisStructuralRefinement
#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.strategy_exactAxisStructuralRefinement
#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.ExtendedCombinedBoundCensus.count_le
#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.ExtendedCombinedBoundCensus.badSeeds_card_le
#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.nounShape_not_enough_for_honestRecon
#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.readVerifyNested_of_reindexAxisTree
#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.recoveredExponent_injOn_Iio_orderOf
#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.lmIO_of_map_injective_on_union
#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.template_readExps_nodup_of_specialized
#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.template_readVerifyNested_of_specialized
#print axioms Nock.NockVMROM.Thm54.TemplateAxisStructure.template_forestPartition_of_specialized
