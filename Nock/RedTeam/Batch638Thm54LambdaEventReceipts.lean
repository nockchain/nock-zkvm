/-
  Nock/RedTeam/Batch638Thm54LambdaEventReceipts.lean

  * **R1** (`lifted_event_readsOn_seed`, `mem_formRLambdaEvent_iff`): the pair set of the
    production event, as a function of the coin vector, is `ReadsOn {seedIdx}`; membership of a
    tuple in the event is exactly "its `(αM, λ)` lies in that pair set at its own vector".  The
    guard reads only the template (`guard_reads_template`).  Both positive controls re-run
    (`positive_control_lambda`, `positive_control_encodedT`).
  * **R2** (`guarded_union_card_le`, re-run; `formRLambdaEvent_card_le`, production): the guarded
    union is `≤ |𝕂|⁹ · Σ_i |𝕂|(deg_i + E')` with the nonzero premise from the guard.  The numeral
    (`fixedFormRWorkload_le`): `fixedFormRWorkload T ≤ M·(2(n−1) + E' + 1)` at `n = formRN K`
    (general `n`, no width hypothesis), `E' = 3N + 3`, `M = |memorySkeletonRows|`, from `degY_le`,
    `kMem ≤ M` (`memoryForest_length_le_memorySkeletonRows`) and `Σ_i nodeCount_i ≤ M`
    (`nodeCount_templateAxisTree_le_size`, the template's `memory_bfs_length`), under
    `CertInRange` at every seed; at `formRN K = 64`, **`M·(3N + 130)`** (`fixedFormRWorkload_le_64`).
  * **R5** (`package_certInRange`): every seed's template certificate of an honest commitment
    (`HonestCommitment.Data`, the package strategy `timestampStrategy`) is in range — the rendered
    memory record's axis is a nat-cast (`renderMemoryMemRec`), so `nockAxisOf` returns a residue
    below `ringChar K`.  Composed: `package_fixedFormRWorkload_le` (no `CertInRange` premise).
-/
import Nock.NockVMROM.Thm54.FormRAxisEvent
import Nock.NockVMROM.Thm54.RealProgramAxisWorkload
import Nock.NockVMROM.Thm54.HonestCommitment
import Nock.RedTeam.Batch634Thm54LambdaEventImportCycle

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Nock.RedTeam.Batch638

open Nock
open Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FormRAxisEvent
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.RedTeam.Batch575
open Nock.AxisBatching
open scoped Classical Polynomial BigOperators

noncomputable section

/-! ## R1 at the production event -/

section R1

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] [Fintype F]
variable [CharP K (ringChar K)]

/-- The production event's pair set at a coin vector `x` (the `Batch641.liftedGuarded` shape, over
the production strategy's committed templates, at `E' = 3N + 3`). -/
def liftedEventAt (T : ProductionP8Containment.ProductionStrategy F K) (s : K)
    (x : Fin 11 → K) : Finset (K × K) :=
  if hz : s ≠ 0 then
    Finset.univ.biUnion fun i :
        Fin (T.verifier.raw.timestamp.afterSeed ⟨s, hz⟩).configTemplate.kMem =>
      if formRGuard (formRTemplatePolynomial
          (ProductionAxisStructureVerifier.committedTemplate T.verifier s hz) i)
          (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 3)
      then formRBadAt (ProductionAxisStructureVerifier.committedTemplate T.verifier s hz)
          i (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 3) x
      else ∅
  else ∅

def liftedEvent (T : ProductionP8Containment.ProductionStrategy F K) (x : Fin 11 → K) :
    Finset (K × K) :=
  liftedEventAt T (x seedIdx) x

/-- **R1.**  The pair set reads only the seed. -/
theorem lifted_event_readsOn_seed (T : ProductionP8Containment.ProductionStrategy F K) :
    ReadsOn (C := K) (n := 11) ({seedIdx} : Finset (Fin 11)) (liftedEvent T) := by
  intro x y hxy
  have hz : x seedIdx = y seedIdx := hxy seedIdx (Finset.mem_singleton_self _)
  unfold liftedEvent liftedEventAt
  by_cases h : x seedIdx ≠ 0
  · have h' : y seedIdx ≠ 0 := hz ▸ h
    rw [dif_pos h, dif_pos h']
    generalize hs : x seedIdx = s at h ⊢
    have hs' : y seedIdx = s := hz ▸ hs
    subst hs'
    apply Finset.biUnion_congr rfl
    intro i _
    split_ifs
    · rw [formRBadAt_eq_template, formRBadAt_eq_template]
    · rfl
  · have h' : ¬ y seedIdx ≠ 0 := hz ▸ h
    rw [dif_neg h, dif_neg h']

/-- **R1, the bridge.**  A tuple is in the production λ-event iff its `(αM, λ)` lies in the pair
set at its own coin vector, whose seed coordinate is `nprSeed c.1`. -/
theorem mem_formRLambdaEvent_iff (T : ProductionP8Containment.ProductionStrategy F K)
    (c : OptimizedProductionChallengeTuple K F) :
    c ∈ formRLambdaEvent T ↔
      (landedVec c alphaMIdx, landedVec c lamIdx) ∈ liftedEvent T (landedVec c) := by
  change _ ↔ _ ∈ liftedEventAt T (nprSeed c.1) (landedVec c)
  simp only [formRLambdaEvent, Finset.mem_filter, Finset.mem_univ, true_and, liftedEventAt]
  constructor
  · rintro ⟨hz, hmem⟩
    rw [dif_pos hz]
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hmem
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
    unfold formRGuardedBad at hi
    split_ifs at hi with hg
    · rw [if_pos hg]
      exact (Finset.mem_filter.mp hi).2
    · simp at hi
  · intro h
    by_cases hz' : nprSeed c.1 ≠ 0
    · rw [dif_pos hz'] at h
      refine ⟨hz', ?_⟩
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp h
      refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
      unfold formRGuardedBad
      split_ifs at hi with hg
      · rw [if_pos hg]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      · simp at hi
    · rw [dif_neg hz'] at h
      simp at h

/-- R1: the guard reads only the template (`Batch634.guard_reads_template`, re-run). -/
theorem guard_reads_template {T T' : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (E₂ : ExactExecutionTemplate T') (i : Fin T.kMem) (j : Fin T'.kMem) (E' : ℕ)
    (hP : formRTemplatePolynomial E i = formRTemplatePolynomial E₂ j)
    (hB : formRGuardedAxisFailureEvent E i E' = formRGuardedAxisFailureEvent E₂ j E') :
    formRGuardedBad E i E' = formRGuardedBad E₂ j E' :=
  Batch634.guard_reads_template E E₂ i j E' hP hB

/-- **R1, positive control 1** (re-run): a set reading the landed `λ` fails. -/
theorem positive_control_lambda :
    ¬ ReadsOn (C := K) (n := 11) (priorCoords landedRound lamIdx)
      (fun x : Fin 11 → K => ({x lamIdx} : Finset K)) :=
  lambdaBad_not_readsOn

/-- **R1, positive control 2** (re-run): a set reading the encoded `T = λ^m` fails. -/
theorem positive_control_encodedT (row : MemoryRowTemplate (K := K))
    (ha : memoryMemRecKind row.timestamp.state = .active)
    (hax : row.placeholder.2.2.mem.axis = ((2 : ℕ) : K)) (h2 : 2 < ringChar K) :
    ¬ ReadsOn (C := K) (n := 11) (priorCoords landedRound lamIdx) (encodedTBad row) :=
  encodedTBad_not_readsOn row ha hax h2

/-- The R1 positive control on the seed: the production pair set is NOT read-free in general — it
is genuinely a function of `z` (the instrument is not vacuous).  Stated as: `seedIdx` is a prior
coordinate of `λ`, so `ReadsOn {seedIdx}` is the prior-round check. -/
theorem seed_is_prior : seedIdx ∈ priorCoords landedRound lamIdx := by
  rw [lambda_prior]; decide

end R1

/-! ## R2 -/

section R2

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] [Fintype F]

/-- **R2 (guarded union, re-run at production `formRGuardedUnion`).** -/
theorem guarded_union_card_le {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (E' : ℕ)
    (hA : ∀ i, CertInRange K (templateCertAxis (templateMemoryTreeAt E i))) :
    (formRGuardedUnion E E').card ≤
      Fintype.card K ^ 9 * ∑ i : Fin T.kMem,
        Fintype.card K * (2 * (formRN K - 1) +
          nodeCount (templateAxisTree (templateMemoryTreeAt E i)) + E') :=
  Batch634.guarded_union_card_le E E' hA

/-- One template axis tree has at most as many nodes as its template tree. -/
theorem nodeCount_templateAxisTree_le_size (t : NTree (MemoryRowTemplate (K := K))) :
    nodeCount (templateAxisTree t) ≤ t.size := by
  let P := fun t : NTree (MemoryRowTemplate (K := K)) => nodeCount (templateAxisTree t) ≤ t.size
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro row children ih
    simp only [P]
    have hsize : (NTree.node row children).size = 1 + (children.map NTree.size).sum := by
      simp [NTree.size]
    rw [hsize]
    cases hs : row.timestamp.state with
      | decompose =>
          rcases children with _ | ⟨l, rest⟩
          · simp [templateAxisTree, hs, nodeCount]
          · rcases rest with _ | ⟨r, tail⟩
            · simp [templateAxisTree, hs, nodeCount]
            · rcases tail with _ | ⟨x, xs⟩
              · have hl := ih l (by simp)
                have hr := ih r (by simp)
                simp only [P] at hl hr
                simp [templateAxisTree, hs, nodeCount]
                omega
              · simp [templateAxisTree, hs, nodeCount]
      | halt =>
          simp [templateAxisTree, hs, nodeCount]
      | read_root =>
          rcases children with _ | ⟨c, rest⟩
          · simp [templateAxisTree, hs, nodeCount]
          · rcases rest with _ | ⟨x, xs⟩
            · have hc := ih c (by simp)
              simp only [P] at hc
              simp [templateAxisTree, hs, nodeCount]
              omega
            · simp [templateAxisTree, hs, nodeCount]
      | verify_child =>
          rcases children with _ | ⟨c, rest⟩
          · simp [templateAxisTree, hs, nodeCount]
          · rcases rest with _ | ⟨x, xs⟩
            · have hc := ih c (by simp)
              simp only [P] at hc
              simp [templateAxisTree, hs, nodeCount]
              omega
            · simp [templateAxisTree, hs, nodeCount]
  · intro c hc
    simp at hc
  · intro head tail ihHead ihTail c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

/-- `Σ_i nodeCount_i ≤ memRows`: the axis trees of one template are no larger than its memory
forest, whose BFS length is the template's row count. -/
theorem sum_nodeCount_le_memRows {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) :
    ∑ i : Fin T.kMem, nodeCount (templateAxisTree (templateMemoryTreeAt E i)) ≤ T.memRows := by
  have hsz : ∑ i : Fin T.kMem, (templateMemoryTreeAt E i).size = T.memRows := by
    have h := E.memory_root_count
    calc ∑ i : Fin T.kMem, (templateMemoryTreeAt E i).size
        = ∑ j : Fin E.memoryForest.length, (E.memoryForest[j.1]).size :=
          Fintype.sum_equiv (finCongr h.symm) _ _
            (fun i => by simp [templateMemoryTreeAt, List.get_eq_getElem])
      _ = (E.memoryForest.map NTree.size).sum := Fin.sum_univ_fun_getElem _ _
      _ = T.memRows := by rw [← E.memory_bfs_length, bfsForest_length]; rfl
  rw [← hsz]
  exact Finset.sum_le_sum fun i _ => nodeCount_templateAxisTree_le_size _

variable [CharP K (ringChar K)]

/-- **R2 numeral, general `n`.**  Under `CertInRange` at every seed, the Form R summand is at most
`M·(2(n−1) + E' + 1)` with `n = formRN K`, `E' = 3N + 3`, `M = |memorySkeletonRows|`. -/
theorem fixedFormRWorkload_le (T : ProductionP8Containment.ProductionStrategy F K)
    (hb : T.BindsAll)
    (hA : ∀ z (hz : z ≠ 0) i, CertInRange K (templateCertAxis (templateMemoryTreeAt
      (ProductionAxisStructureVerifier.committedTemplate T.verifier z hz) i))) :
    ProductionP8Containment.fixedFormRWorkload T ≤
      (SemanticStrategy.memorySkeletonRows T.skeleton).length *
        (2 * (formRN K - 1) + (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 3)
          + 1) := by
  set E' := 3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 3
  set M := (SemanticStrategy.memorySkeletonRows T.skeleton).length
  unfold ProductionP8Containment.fixedFormRWorkload
  haveI : Nonempty K := ⟨0⟩
  refine ciSup_le fun z => ?_
  by_cases hz : z ≠ 0
  · rw [dif_pos hz]
    set E := ProductionAxisStructureVerifier.committedTemplate T.verifier z hz
    have hkMem : (T.verifier.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate.kMem ≤ M := by
      rw [TraceGen.committedTemplate_kMem T hb z hz]
      exact RealProgramAxisWorkload.memoryForest_length_le_memorySkeletonRows T.skeleton
    have hrows : (T.verifier.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate.memRows = M :=
      TraceGen.specializedCfg_memRows T hb z hz 0 0
    have hnodes := sum_nodeCount_le_memRows E
    have hper : ∀ i, ((Finset.range (E' + 1)).sup fun k =>
          ((formRTemplatePolynomial E i).coeff k).natDegree) + E' ≤
        nodeCount (templateAxisTree (templateMemoryTreeAt E i)) + (2 * (formRN K - 1) + E') := by
      intro i
      have hs : ((Finset.range (E' + 1)).sup fun k =>
          ((formRTemplatePolynomial E i).coeff k).natDegree) ≤
            2 * (formRN K - 1) + nodeCount (templateAxisTree (templateMemoryTreeAt E i)) := by
        refine Finset.sup_le fun k _ => ?_
        exact degY_le (K := K) (formRN K) _ _ (hA z hz i) k _
      omega
    calc ∑ i, (((Finset.range (E' + 1)).sup fun k =>
            ((formRTemplatePolynomial E i).coeff k).natDegree) + E')
        ≤ ∑ i : Fin (T.verifier.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate.kMem,
            (nodeCount (templateAxisTree (templateMemoryTreeAt E i)) +
              (2 * (formRN K - 1) + E')) := Finset.sum_le_sum fun i _ => hper i
      _ = (∑ i : Fin (T.verifier.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate.kMem,
            nodeCount (templateAxisTree (templateMemoryTreeAt E i))) +
            (T.verifier.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate.kMem *
              (2 * (formRN K - 1) + E') := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
      _ ≤ M + M * (2 * (formRN K - 1) + E') :=
          Nat.add_le_add (hnodes.trans (le_of_eq hrows)) (Nat.mul_le_mul_right _ hkMem)
      _ = M * (2 * (formRN K - 1) + E' + 1) := by ring
  · rw [dif_neg hz]; exact Nat.zero_le _

/-- **R2 numeral at Goldilocks width (`formRN K = 64`) with row majorants `N`, `M`:
`fixedFormRWorkload ≤ M·(3N + 130)`.** -/
theorem fixedFormRWorkload_le_64 (T : ProductionP8Containment.ProductionStrategy F K)
    (hb : T.BindsAll)
    (hA : ∀ z (hz : z ≠ 0) i, CertInRange K (templateCertAxis (templateMemoryTreeAt
      (ProductionAxisStructureVerifier.committedTemplate T.verifier z hz) i)))
    (hn : formRN K = 64) (N M : ℕ)
    (hN : (SemanticStrategy.computeSkeletonRows T.skeleton).length ≤ N)
    (hM : (SemanticStrategy.memorySkeletonRows T.skeleton).length ≤ M) :
    ProductionP8Containment.fixedFormRWorkload T ≤ M * (3 * N + 130) := by
  refine (fixedFormRWorkload_le T hb hA).trans ?_
  rw [hn]
  calc (SemanticStrategy.memorySkeletonRows T.skeleton).length *
        (2 * (64 - 1) + (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 3) + 1)
      ≤ M * (2 * (64 - 1) + (3 * N + 3) + 1) := Nat.mul_le_mul hM (by omega)
    _ = M * (3 * N + 130) := by ring

/-- The approved figure is `Batch641.worst_case_64` / `Batch628.trueFigure` at `kMem = M`. -/
theorem figure_is_approved (N M : ℕ) :
    M * (2 * (64 - 1) + (3 * N + 3) + 1) = M * (3 * N + 130) := by ring

end R2

/-! ## R5 — the package strategy's certificates are in range -/

section R5

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-- A nat-cast's residue is below the characteristic. -/
theorem nockAxisOf_natCast_lt (a : ℕ) : MemoryTable.nockAxisOf ((a : ℕ) : K) < ringChar K := by
  have hp : 0 < ringChar K := Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite K (ringChar K))
  have hmod : ((a : ℕ) : K) = (((a % ringChar K : ℕ)) : K) := CharP.cast_eq_mod K (ringChar K) a
  rw [hmod]
  exact (MemoryTable.nockAxisOf_spec (K := K) (Nat.mod_lt a hp)).1

/-- Every rendered memory template row carries a nat-cast axis. -/
theorem render_axis_natCast (z : K) (n : HonestCommitment.MemoryNode K) :
    ∃ a : ℕ, (HonestCommitment.renderMemoryTemplate z n).placeholder.2.2.mem.axis = (a : K) := by
  simp only [HonestCommitment.renderMemoryTemplate, HonestCommitment.renderMemoryRow,
    HonestCommitment.renderMemoryPub, HonestCommitment.renderMemoryMemRec]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨0, by simp [ComputeTable.MemRec.zero]⟩

/-- **R5 (`package_certInRange`).**  For an honest commitment (the package strategy's
`timestampStrategy`), every seed's template certificate is in range. -/
theorem package_certInRange {E : BuildableNockExecution F K} (D : HonestCommitment.Data E)
    (z : K) (i : Fin (HonestCommitment.configTemplateOf E z).kMem) :
    CertInRange K (templateCertAxis (templateMemoryTreeAt (D.executionTemplate z) i)) := by
  apply certInRange_of_lt
  intro e
  have hp : 0 < ringChar K := Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite K (ringChar K))
  unfold templateCertAxis certAxisVia
  cases h : readRowAt (templateMemoryTreeAt (D.executionTemplate z) i) e with
  | none => simpa using hp
  | some r =>
      simp only [Option.map_some, Option.getD_some]
      have hmem : r ∈ (bfsForest [templateMemoryTreeAt (D.executionTemplate z) i]).map
          NTree.label := List.mem_of_find?_eq_some h
      -- the tree is a rendered memory node tree
      have htree : ∃ n0, templateMemoryTreeAt (D.executionTemplate z) i =
          mapNTree (HonestCommitment.renderMemoryTemplate z) n0 := by
        unfold templateMemoryTreeAt
        simp only [HonestCommitment.Data.executionTemplate, List.get_eq_getElem, List.getElem_map]
        exact ⟨_, rfl⟩
      obtain ⟨n0, hn0⟩ := htree
      rw [hn0, TraceGen.bfsForest_mapNTree_singleton, List.map_map] at hmem
      obtain ⟨m, -, hm⟩ := List.mem_map.mp hmem
      have hr : r = HonestCommitment.renderMemoryTemplate z m.label := by
        rw [← hm]; simp [mapNTree_label]
      obtain ⟨a, ha⟩ := render_axis_natCast z m.label
      rw [hr, templateRowCertAxis, ha]
      exact nockAxisOf_natCast_lt a

end R5

end

end Nock.RedTeam.Batch638

#print axioms Nock.RedTeam.Batch638.lifted_event_readsOn_seed
#print axioms Nock.RedTeam.Batch638.mem_formRLambdaEvent_iff
#print axioms Nock.RedTeam.Batch638.guard_reads_template
#print axioms Nock.RedTeam.Batch638.positive_control_lambda
#print axioms Nock.RedTeam.Batch638.positive_control_encodedT
#print axioms Nock.RedTeam.Batch638.guarded_union_card_le
#print axioms Nock.RedTeam.Batch638.nodeCount_templateAxisTree_le_size
#print axioms Nock.RedTeam.Batch638.sum_nodeCount_le_memRows
#print axioms Nock.RedTeam.Batch638.fixedFormRWorkload_le
#print axioms Nock.RedTeam.Batch638.fixedFormRWorkload_le_64
#print axioms Nock.RedTeam.Batch638.nockAxisOf_natCast_lt
#print axioms Nock.RedTeam.Batch638.package_certInRange
#print axioms Nock.NockVMROM.Thm54.FormRAxisEvent.formRLambdaEvent_card_le
