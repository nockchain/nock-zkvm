import Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
import Nock.RedTeam.Batch64Thm54RepairedOptimizedMemory

/-!
# certified optimized-memory red team

The governing
paper frame is the aggregate forest, carried NMR axis
, memory language, complete Memspec
, and the memory half of Theorem 5.4.

The accepted criterion is syntactic production hygiene, exact disjoint semantic ownership,
unconditional forward completeness, collision-conditioned reverse recovery, direct concrete
malformed discrimination, and same-assignment axis assembly.  The rejected all-fourteen
matroid-style isolation criterion is deliberately not reinstated.
-/

namespace Nock.RedTeam.Batch65

open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Module
open Polynomial
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.Concrete
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace
open Nock.NockVMROM.Thm54.OptimizedMemoryCodec
open Nock.NockVMROM.Thm54.OptimizedMemoryCoreInventory
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedMemorySameExecution
open Nock.NockVMROM.Thm54.OptimizedMemorySameExecution.Concrete
open Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeSampledTrace.Concrete

noncomputable section

/-! ## Exact codec, source ownership, and resource surface -/

theorem exact_codec_and_resource_receipt :
    Fintype.card BaseRole = 6 ∧
      Fintype.card ExtensionRole = 56 ∧
      memoryRowSources (K := K73cubic).length = 33 ∧
      transitionSources (K := K73cubic).length = 50 ∧
      extensionFoldSources (K := K73cubic).length = 40 ∧
      (baseTransitionGates (F := F73) (K := K73cubic) basis73).length = 6 ∧
      (foldedBaseTransitionGates (F := F73) (K := K73cubic) basis73).length = 11 ∧
      extensionTransitionGates (K := K73cubic).length = 21 ∧
      (mixedTransitionGates (F := F73) (K := K73cubic) basis73).length = 50 ∧
      (foldedMixedTransitionGates (F := F73)).length = 6 ∧
      degreeOneEndpoints.length = 0 ∧
      degreeThreeEndpoints.length = 0 ∧
      foldedDegreeThreeEndpoints.length = 4 ∧
      (equalityChecks basis73).length = 0 ∧
      (foldedEqualityChecks basis73).length = 12 ∧
      expandedColumnCount 3 = 174 ∧
      expandedTransitionCount 3 = 77 ∧
      expandedTotalConstraintCount 3 = 93 ∧
      expandedTransitionCountMixed 3 = 153 ∧
      expandedTotalConstraintCountMixed 3 = 153 ∧
      expandedTransitionCountMixedFolded 3 = 89 ∧
      180 + 23 = 203 ∧ 6 + 49 * 3 = 153 := by
  decide

theorem codec_roundtrip_all_four_states
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (r : SemanticRow F K) :
    decode (encode r) = r :=
  decode_encode r

theorem accepted_codec_has_no_fallback
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (r : EncodedRow F K) (h : AcceptedControls r) :
    encode (decode r) = r :=
  encode_decode_of_accepted r h

theorem malformed_codec_controls_reject
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (r : EncodedRow F K)
    (hzero : ∀ i : Fin 4, r.base (stateSlot i) = 0)
    (hfirst : r.base 4 * (r.base 4 - 1) ≠ 0)
    (hlast : r.base 5 * (r.base 5 - 1) ≠ 0) :
    ¬ AcceptedControls r ∧ ¬ AcceptedControls r ∧ ¬ AcceptedControls r :=
  ⟨all_zero_state_rejected r hzero,
    malformed_first_mask_rejected r hfirst,
    malformed_last_mask_rejected r hlast⟩

theorem all_four_codec_states_are_distinct_and_covered :
    stateIndex .decompose = 0 ∧
      stateIndex .halt = 1 ∧
      stateIndex .read_root = 2 ∧
      stateIndex .verify_child = 3 ∧
      (∀ s : MemoryTable.MState,
        decodeState (encode
          ({ state := s, isFirst := 0, isLast := 0,
             table := fun _ => 0, walk := fun _ => 0, sampledIO := fun _ => 0,
             selectorMirror := fun _ => 0, walkInv := 0 } : SemanticRow F73 K73cubic)) = s) := by
  exact ⟨rfl, rfl, rfl, rfl, fun s => decodeState_encode _⟩

theorem final_resource_and_inert_padding_receipt :
    let Q := namedFinalMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
      honestLegacyFamily.problem.cfg.kMem
    Q.rap.w = 205 ∧ Q.rap.s = 156 ∧ Q.rap.d = 4 ∧ Q.rap.k = 1 ∧
      (∀ P : Fin Q.rap.w → F73[X],
        RAP.SatisfiesWithPreprocessing Q P ↔
          RAP.SatisfiesWithPreprocessing
            (namedSourceMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
              honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem)
            (RAPPadding.projectTrace
              (namedSourceMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
                honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem).rap
              (RAPPadding.firstRoundExtra
                (namedSourceMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
                  honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem).rap
                (namedSourceMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
                  honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem).rounds_pos
                (RAPPadding.memoryResidualColumns 3)) P)) := by
  dsimp only
  exact ⟨(finalMemoryRAP_fingerprint honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem).1,
    (finalMemoryRAP_fingerprint honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem).2.1,
    (finalMemoryRAP_fingerprint honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem).2.2.1,
    (finalMemoryRAP_fingerprint honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem).2.2.2,
    fun P => final_satisfies_iff_source honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
      honestLegacyFamily.problem.cfg.kMem P⟩


def actualAuthorityWitness (i : Fin (transitionSources (K := K73cubic)).length) : Bool :=
  match sourceAuthority i with
  | .selectorBase =>
      decide ((i : ℕ) < 5) &&
        decide ((transitionSources (K := K73cubic)).get i ∈ selectorBaseSources (K := K73cubic))
  | .promotedChain => decide ((transitionSources (K := K73cubic)).get i = memoryChainSource)
  | .promotedAccumulator =>
      decide ((transitionSources (K := K73cubic)).get i = sampledSources.get ⟨3, by decide⟩)
  | .derivedFirstMask =>
      decide ((transitionSources (K := K73cubic)).get i = sampledSources.get ⟨5, by decide⟩)
  | .derivedLastMask =>
      decide ((transitionSources (K := K73cubic)).get i = sampledSources.get ⟨6, by decide⟩)
  | .promotedTerminal =>
      decide ((transitionSources (K := K73cubic)).get i = sampledSources.get ⟨9, by decide⟩)
  | .extensionFold =>
      decide ((transitionSources (K := K73cubic)).get i ∈ extensionFoldSources (K := K73cubic))

/-- 4.35 migration helpers: `List.get` at a literal-width `Fin` index into a list whose length is
only defeq to that width is not matched by `simp`/`rw` once the term is checked at reducible
transparency; restate with the exact `Fin` index. Proof-only additions. -/
theorem sampledSources_get_aux (k : Fin 10) :
    sampledSources.get k = sampledSources[(k : ℕ)]'(by
      have := k.isLt
      simpa [sampledSources] using this) := rfl

theorem sampledFoldSources_get_aux (j : Fin 6) :
    sampledFoldSources.get j = sampledFoldSources[(j : ℕ)]'(by
      have := j.isLt
      simpa [sampledFoldSources] using this) := rfl

set_option maxRecDepth 200000 in
private theorem selector_row_mem
    {K : Type} [Field K]
    (i : Fin (transitionSources (K := K)).length) (h5 : (i : ℕ) < 5) :
    (transitionSources (K := K)).get i ∈ selectorBaseSources (K := K) := by
  have hrow : (memoryRowSources (K := K)).length = 33 := memoryRowSources_length
  simp only [List.get_eq_getElem]
  simp only [transitionSources, selectorBaseSources, List.append_assoc]
  have hia : (i : ℕ) < (memoryRowSources (K := K)).length := by omega
  rw [List.getElem_append_left hia]
  have htake : (i : ℕ) < ((memoryRowSources (K := K)).take 5).length := by
    simp [List.length_take, hrow, h5]
  rw [← List.getElem_take (j := 5) (h := htake)]
  exact List.mem_of_getElem rfl

private theorem midrow_mem_fold
    {K : Type} [Field K]
    (i : Fin (transitionSources (K := K)).length)
    (hlo : 5 ≤ (i : ℕ)) (hhi : (i : ℕ) < 33) :
    (transitionSources (K := K)).get i ∈ extensionFoldSources (K := K) := by
  have hrow : (memoryRowSources (K := K)).length = 33 := memoryRowSources_length
  have hfold : (extensionFoldSources (K := K)).length = 40 := extensionFoldSources_length
  have hdrop : ((memoryRowSources (K := K)).drop 5).length = 28 := by
    simp [List.length_drop, hrow]
  have hj : (i : ℕ) - 5 < (extensionFoldSources (K := K)).length := by omega
  apply List.mem_of_getElem (i := (i : ℕ) - 5) (h := hj)
  simp only [List.get_eq_getElem]
  simp only [transitionSources, extensionFoldSources, List.append_assoc]
  conv_rhs => rw [List.getElem_append_left (by simpa [hrow] using hhi)]
  conv_lhs => rw [List.getElem_append_left (by simpa [hdrop] using (by omega : (i : ℕ) - 5 < 28))]
  simp [List.getElem_drop, Nat.add_sub_cancel' hlo]

private theorem walk_span_mem_fold
    {K : Type} [Field K]
    (i : Fin (transitionSources (K := K)).length)
    (hlo : 34 ≤ (i : ℕ)) (hhi : (i : ℕ) < 40) :
    (transitionSources (K := K)).get i ∈ extensionFoldSources (K := K) := by
  rw [List.mem_iff_getElem?]
  refine ⟨(i : ℕ) - 6, ?_⟩
  rw [List.get_eq_getElem]
  have htrans :
      (transitionSources (K := K))[(i : ℕ)]? =
        some ((transitionSources (K := K))[(i : ℕ)]) :=
    (List.getElem_eq_iff i.isLt).1 rfl
  rw [← htrans]
  simp only [extensionFoldSources, transitionSources, List.append_assoc, List.getElem?_append,
    List.length_drop, List.length_singleton, memoryRowSources_length,
    walkBoundarySources_length, walkTransitionSources_length]
  split_ifs <;> first | rfl | omega

private theorem transition_sampled_eq
    {K : Type} [Field K]
    (i : Fin (transitionSources (K := K)).length) (k : Fin 10)
    (h : (i : ℕ) = 40 + k) :
    (transitionSources (K := K)).get i = sampledSources.get k := by
  rw [List.get_eq_getElem, sampledSources_get_aux, List.getElem_eq_iff]
  have hright : sampledSources[(k : ℕ)]? = some (sampledSources[(k : ℕ)]) :=
    (List.getElem_eq_iff k.isLt).1 rfl
  rw [← hright]
  simp only [transitionSources, List.append_assoc, List.getElem?_append, List.length_singleton,
    memoryRowSources_length, walkBoundarySources_length, walkTransitionSources_length, h]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

private theorem sampled_in_fold
    {K : Type} [Field K] (j : Fin 6) :
    sampledFoldSources.get j ∈ extensionFoldSources (K := K) := by
  rw [List.mem_iff_getElem?]
  refine ⟨34 + (j : ℕ), ?_⟩
  rw [sampledFoldSources_get_aux]
  have hget :
      sampledFoldSources[(j : ℕ)]? = some (sampledFoldSources[(j : ℕ)]) :=
    (List.getElem_eq_iff j.isLt).1 rfl
  rw [← hget]
  simp only [extensionFoldSources, List.append_assoc, List.getElem?_append, List.length_drop,
    memoryRowSources_length, walkBoundarySources_length, walkTransitionSources_length]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

private theorem chain_source_eq
    {K : Type} [Field K]
    (i : Fin (transitionSources (K := K)).length) (hc : (i : ℕ) = 33) :
    (transitionSources (K := K)).get i = memoryChainSource := by
  rw [List.get_eq_getElem, List.getElem_eq_iff]
  simp only [transitionSources, List.append_assoc, List.getElem?_append, List.length_singleton,
    memoryRowSources_length, hc]
  split_ifs <;> first | rfl | omega

private theorem extension_authority_mem
    {K : Type} [Field K]
    (i : Fin (transitionSources (K := K)).length)
    (h5 : ¬ (i : ℕ) < 5) (h33 : ¬ (i : ℕ) = 33) (h43 : ¬ (i : ℕ) = 43)
    (h45 : ¬ (i : ℕ) = 45) (h46 : ¬ (i : ℕ) = 46) (h49 : ¬ (i : ℕ) = 49) :
    (transitionSources (K := K)).get i ∈ extensionFoldSources (K := K) := by
  have hlt : (i : ℕ) < 50 := by simpa [transitionSources_length] using i.isLt
  by_cases hmid : (i : ℕ) < 33
  · exact midrow_mem_fold i (by omega) hmid
  by_cases hwalk : (i : ℕ) < 40
  · exact walk_span_mem_fold i (by omega) hwalk
  have hk : (i : ℕ) = 40 ∨ (i : ℕ) = 41 ∨ (i : ℕ) = 42 ∨ (i : ℕ) = 44 ∨
      (i : ℕ) = 47 ∨ (i : ℕ) = 48 := by omega
  rcases hk with hk | hk | hk | hk | hk | hk
  · rw [transition_sampled_eq i ⟨0, by decide⟩ (by omega)]
    simp only [sampledSources_get_aux]
    exact sampled_in_fold ⟨0, by decide⟩
  · rw [transition_sampled_eq i ⟨1, by decide⟩ (by omega)]
    simp only [sampledSources_get_aux]
    exact sampled_in_fold ⟨1, by decide⟩
  · rw [transition_sampled_eq i ⟨2, by decide⟩ (by omega)]
    simp only [sampledSources_get_aux]
    exact sampled_in_fold ⟨2, by decide⟩
  · rw [transition_sampled_eq i ⟨4, by decide⟩ (by omega)]
    simp only [sampledSources_get_aux]
    exact sampled_in_fold ⟨3, by decide⟩
  · rw [transition_sampled_eq i ⟨7, by decide⟩ (by omega)]
    simp only [sampledSources_get_aux]
    exact sampled_in_fold ⟨4, by decide⟩
  · rw [transition_sampled_eq i ⟨8, by decide⟩ (by omega)]
    simp only [sampledSources_get_aux]
    exact sampled_in_fold ⟨5, by decide⟩

theorem every_source_occurrence_has_actual_authority
    (i : Fin (transitionSources (K := K73cubic)).length) :
    actualAuthorityWitness i = true := by
  simp only [actualAuthorityWitness, sourceAuthority]
  split_ifs with h5 h33 h43 h45 h46 h49
  · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨h5, selector_row_mem i h5⟩
  · rw [decide_eq_true_eq]
    exact chain_source_eq i h33
  · rw [decide_eq_true_eq]
    exact transition_sampled_eq i ⟨3, by decide⟩ (by omega)
  · rw [decide_eq_true_eq]
    exact transition_sampled_eq i ⟨5, by decide⟩ (by omega)
  · rw [decide_eq_true_eq]
    exact transition_sampled_eq i ⟨6, by decide⟩ (by omega)
  · rw [decide_eq_true_eq]
    exact transition_sampled_eq i ⟨9, by decide⟩ (by omega)
  · rw [decide_eq_true_eq]
    exact extension_authority_mem i h5 h33 h43 h45 h46 h49

theorem production_bucket_hygiene :
    (baseTransitionGates basis73).Nodup ∧
      extensionTransitionGates (K := K73cubic).Nodup ∧
      (equalityChecks basis73).Nodup ∧
      (∀ g ∈ baseTransitionGates basis73, g ≠ .const 0) ∧
      (∀ g ∈ extensionTransitionGates (K := K73cubic), g ≠ (.Const 0 : Expr)) ∧
      (∀ g ∈ equalityChecks basis73, g ≠ .const 0) :=
  ⟨baseTransitionGates_nodup basis73, extensionTransitionGates_nodup,
    equalityChecks_nodup basis73, baseTransitionGates_no_literal_zero basis73,
    extensionTransitionGates_no_literal_zero, equalityChecks_no_literal_zero basis73⟩

/-! ## Actual-gate semantic recovery -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K]

theorem gathered_trace_eq_lift_of_binding
    (b : Basis (Fin 3) F K) (envF : Env F) (role base : ℕ)
    (h : ∀ k : Fin 3,
      (maskBindingCoord (F := F) (K := K) b role base k).eval envF = 0) :
    (gatherEnv b ((memorySourceTemplate (F := F) (K := K) b).col0 3) envF).trace role =
      algebraMap F K (envF.trace base) := by
  apply (eq_iff_coords_eq b _ _).2
  intro k
  have hcur :=
    (isCoordEnv_gather b
      ((memorySourceTemplate (F := F) (K := K) b).col0 3) envF).trace role k
  have hlift :
      coord b (algebraMap F K (envF.trace base)) k =
        coord b (1 : K) k * envF.trace base := by
    rw [show algebraMap F K (envF.trace base) = envF.trace base • (1 : K) by
      simp [Algebra.smul_def]]
    simp [coord, mul_comm]
  have hz := h k
  simp only [maskBindingCoord, CoeffExpr.eval, extCoord, bcur] at hz
  change envF.trace (6 + 3 * role + (k : ℕ)) =
      coord b ((gatherEnv b
        ((memorySourceTemplate (F := F) (K := K) b).col0 3) envF).trace role) k at hcur
  rw [← hcur, hlift]
  exact sub_eq_zero.mp hz

theorem selectorBaseSources_exact :
    selectorBaseSources (K := K) =
      [.Mul (extVar .traceCur 51)
          (.Sub (.Const 1) (extVar .traceCur 51)),
       .Mul (extVar .traceCur 52)
          (.Sub (.Const 1) (extVar .traceCur 52)),
       .Mul (extVar .traceCur 53)
          (.Sub (.Const 1) (extVar .traceCur 53)),
       .Mul (extVar .traceCur 54)
          (.Sub (.Const 1) (extVar .traceCur 54)),
       .Sub (.Add (extVar .traceCur 51)
          (.Add (extVar .traceCur 52)
            (.Add (extVar .traceCur 53) (extVar .traceCur 54)))) (.Const 1)] := by
  rfl

/-- The chip's
`equalityChecks` are now the twelve *coordinates* of the four `𝕂`-valued selector-mirror gates,
so `heq` supplies the coordinate facts directly; no compression coin and no collision exclusion
stands between the committed gates and the binding. -/
theorem selector_mirrors_bound_by_actual_equalities
    (b : Basis (Fin 3) F K) (envF : Env F)
    (heq : ∀ g ∈ foldedEqualityChecks b, g.eval envF = 0) :
    ∀ s : Fin 4,
      (gatherEnv b ((memorySourceTemplate b).col0 3) envF).trace (51 + s) =
        algebraMap F K (envF.trace s) := by
  intro s
  apply gathered_trace_eq_lift_of_binding b envF (51 + s) s
  intro k
  exact heq _ ((mem_foldedEqualityChecks b _).mpr ⟨s, k, rfl⟩)

/-- `RepairedMemoryCollisionGood` dropped here too. -/
theorem selector_sources_recovered_from_actual_gates
    (b : Basis (Fin 3) F K) (envF : Env F)
    (hbase : ∀ g ∈ foldedBaseTransitionGates b, g.eval envF = 0)
    (heq : ∀ g ∈ foldedEqualityChecks b, g.eval envF = 0) :
    ∀ e ∈ selectorBaseSources (K := K),
      e.eval (gatherEnv b ((memorySourceTemplate b).col0 3) envF) = 0 := by
  let envK := gatherEnv b ((memorySourceTemplate b).col0 3) envF
  have hm := selector_mirrors_bound_by_actual_equalities b envF heq
  have hb0 := hbase (bbool (bcur 0)) (by simp [foldedBaseTransitionGates])
  have hb1 := hbase (bbool (bcur 1)) (by simp [foldedBaseTransitionGates])
  have hb2 := hbase (bbool (bcur 2)) (by simp [foldedBaseTransitionGates])
  have hb3 := hbase (bbool (bcur 3)) (by simp [foldedBaseTransitionGates])
  have hbs := hbase (bsum4 .traceCur) (by simp [foldedBaseTransitionGates])
  simp only [bbool, bcur, bsum4, CoeffExpr.eval] at hb0 hb1 hb2 hb3 hbs
  have hb0K := congrArg (algebraMap F K) hb0
  have hb1K := congrArg (algebraMap F K) hb1
  have hb2K := congrArg (algebraMap F K) hb2
  have hb3K := congrArg (algebraMap F K) hb3
  have hbsK := congrArg (algebraMap F K) hbs
  simp only [map_mul, map_sub, map_add, map_one, map_zero] at hb0K hb1K hb2K hb3K hbsK
  intro e he
  rw [selectorBaseSources_exact] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · simp only [Expr.eval, extVar]
    rw [show envK.trace 51 = algebraMap F K (envF.trace 0) by simpa [envK] using hm 0]
    calc
      _ = -((algebraMap F K (envF.trace 0)) *
          ((algebraMap F K (envF.trace 0)) - 1)) := by ring
      _ = 0 := by rw [hb0K]; simp
  · simp only [Expr.eval, extVar]
    rw [show envK.trace 52 = algebraMap F K (envF.trace 1) by simpa [envK] using hm 1]
    calc
      _ = -((algebraMap F K (envF.trace 1)) *
          ((algebraMap F K (envF.trace 1)) - 1)) := by ring
      _ = 0 := by rw [hb1K]; simp
  · simp only [Expr.eval, extVar]
    rw [show envK.trace 53 = algebraMap F K (envF.trace 2) by simpa [envK] using hm 2]
    calc
      _ = -((algebraMap F K (envF.trace 2)) *
          ((algebraMap F K (envF.trace 2)) - 1)) := by ring
      _ = 0 := by rw [hb2K]; simp
  · simp only [Expr.eval, extVar]
    rw [show envK.trace 54 = algebraMap F K (envF.trace 3) by simpa [envK] using hm 3]
    calc
      _ = -((algebraMap F K (envF.trace 3)) *
          ((algebraMap F K (envF.trace 3)) - 1)) := by ring
      _ = 0 := by rw [hb3K]; simp
  · simp only [Expr.eval, extVar]
    rw [show envK.trace 51 = algebraMap F K (envF.trace 0) by simpa [envK] using hm 0,
      show envK.trace 52 = algebraMap F K (envF.trace 1) by simpa [envK] using hm 1,
      show envK.trace 53 = algebraMap F K (envF.trace 2) by simpa [envK] using hm 2,
      show envK.trace 54 = algebraMap F K (envF.trace 3) by simpa [envK] using hm 3]
    simpa using hbsK

/-- **`RepairedMemoryCollisionGood` replaced by the committed mixed gates**. -/
theorem promoted_sources_recovered_from_actual_gates
    (b : Basis (Fin 3) F K) (envF : Env F)
    (hbase : ∀ g ∈ foldedBaseTransitionGates b, g.eval envF = 0)
    (hmix : ∀ g ∈ foldedMixedTransitionGates (F := F),
      g.eval (gatherEnv b ((memorySourceTemplate b).col0 3) envF) envF = 0)
    (hfirstBool : envF.trace 4 * (envF.trace 4 - 1) = 0)
    (hlastBool : envF.trace 5 * (envF.trace 5 - 1) = 0) :
    memoryChainSource.eval
        (gatherEnv b ((memorySourceTemplate b).col0 3) envF) = 0 ∧
      (sampledSources.get ⟨3, by decide⟩).eval
        (gatherEnv b ((memorySourceTemplate b).col0 3) envF) = 0 ∧
      (sampledSources.get ⟨5, by decide⟩).eval
        (gatherEnv b ((memorySourceTemplate b).col0 3) envF) = 0 ∧
      (sampledSources.get ⟨6, by decide⟩).eval
        (gatherEnv b ((memorySourceTemplate b).col0 3) envF) = 0 ∧
      (sampledSources.get ⟨9, by decide⟩).eval
        (gatherEnv b ((memorySourceTemplate b).col0 3) envF) = 0 := by
  let envK := gatherEnv b ((memorySourceTemplate b).col0 3) envF
  have hiso := isCoordEnv_gather b ((memorySourceTemplate b).col0 3) envF
  have hfirstCoords : ∀ k : Fin 3, (maskBindingCoord b 47 4 k).eval envF = 0 :=
    (MixedCoordinateCompiler.mixedCompile_zero_iff b ((memorySourceTemplate b).col0 3)
      hiso (firstMaskMixed (F := F))).1
      (hmix _ (by simp [foldedMixedTransitionGates]))
  have hlastCoords : ∀ k : Fin 3, (maskBindingCoord b 48 5 k).eval envF = 0 :=
    (MixedCoordinateCompiler.mixedCompile_zero_iff b ((memorySourceTemplate b).col0 3)
      hiso (lastMaskMixed (F := F))).1
      (hmix _ (by simp [foldedMixedTransitionGates]))
  have hchainCoords : ∀ k : Fin 3, (chainCoord (F := F) k).eval envF = 0 :=
    (MixedCoordinateCompiler.mixedCompile_zero_iff b ((memorySourceTemplate b).col0 3)
      hiso (chainMixed (F := F))).1
      (hmix _ (by simp [foldedMixedTransitionGates]))
  have hfirst :
      envK.trace 47 = algebraMap F K (envF.trace 4) := by
    simpa [envK] using gathered_trace_eq_lift_of_binding b envF 47 4 hfirstCoords
  have hlast :
      envK.trace 48 = algebraMap F K (envF.trace 5) := by
    simpa [envK] using gathered_trace_eq_lift_of_binding b envF 48 5 hlastCoords
  have hacc :
      (sampledSources.get ⟨3, by decide⟩).eval envK = 0 := by
    apply (coordinateCompile_zero_iff b ((memorySourceTemplate b).col0 3)
      (isCoordEnv_gather b ((memorySourceTemplate b).col0 3) envF)
      (sampledSources.get ⟨3, by decide⟩)).2
    intro k
    have hk := hbase ((foldedBaseTransitionGates b).get
      ⟨8 + (k : ℕ), by rw [foldedBaseTransitionGates_length b]; omega⟩) (List.get_mem _ _)
    rw [show (foldedBaseTransitionGates b).get
        ⟨8 + (k : ℕ), by rw [foldedBaseTransitionGates_length b]; omega⟩ =
      sampledAccumulatorCoord k by fin_cases k <;> rfl] at hk
    simpa [sampledSources, sampledAccumulatorCoord, extCoord, coordinateCompile,
      memorySourceTemplate, ChipTemplate.col0, ChipTemplate.baseCols, extVar] using hk
  have hterminal :
      (sampledSources.get ⟨9, by decide⟩).eval envK = 0 := by
    apply (coordinateCompile_zero_iff b ((memorySourceTemplate b).col0 3)
      (isCoordEnv_gather b ((memorySourceTemplate b).col0 3) envF)
      (sampledSources.get ⟨9, by decide⟩)).2
    intro k
    have hk := hbase ((foldedBaseTransitionGates b).get
      ⟨5 + (k : ℕ), by rw [foldedBaseTransitionGates_length b]; omega⟩) (List.get_mem _ _)
    rw [show (foldedBaseTransitionGates b).get
        ⟨5 + (k : ℕ), by rw [foldedBaseTransitionGates_length b]; omega⟩ =
      sampledTerminalCoord k by fin_cases k <;> rfl] at hk
    simpa [sampledSources, sampledTerminalCoord, extCoord, coordinateCompile,
      memorySourceTemplate, ChipTemplate.col0, ChipTemplate.baseCols, extVar] using hk
  have hfirstMask :
      (sampledSources.get ⟨5, by decide⟩).eval envK = 0 := by
    rw [show sampledSources.get ⟨5, by decide⟩ =
      .Mul (extVar .traceCur 47) (.Sub (extVar .traceCur 47) (.Const 1)) by rfl]
    simp only [Expr.eval, extVar]
    rw [hfirst]
    have hmap := congrArg (algebraMap F K) hfirstBool
    simpa using hmap
  have hlastMask :
      (sampledSources.get ⟨6, by decide⟩).eval envK = 0 := by
    rw [show sampledSources.get ⟨6, by decide⟩ =
      .Mul (extVar .traceCur 48) (.Sub (extVar .traceCur 48) (.Const 1)) by rfl]
    simp only [Expr.eval, extVar]
    rw [hlast]
    have hmap := congrArg (algebraMap F K) hlastBool
    simpa using hmap
  have hchain :
      memoryChainSource.eval envK = 0 := by
    rw [show memoryChainSource =
      .Mul (.Sub (.Const 1) (extVar .traceCur 48))
        (.Sub (extVar .traceCur 28) (extVar .traceNext 27)) by rfl]
    simp only [Expr.eval, extVar]
    rw [hlast]
    norm_num only [Int.cast_one]
    apply (eq_iff_coords_eq b _ 0).2
    intro k
    rw [coord_zero]
    have hcur :=
      (isCoordEnv_gather b ((memorySourceTemplate b).col0 3) envF).trace 28 k
    have hnext :=
      (isCoordEnv_gather b ((memorySourceTemplate b).col0 3) envF).traceNext 27 k
    change envF.trace (90 + (k : ℕ)) = coord b (envK.trace 28) k at hcur
    change envF.traceNext (87 + (k : ℕ)) = coord b (envK.traceNext 27) k at hnext
    have hsmul :
        (1 - algebraMap F K (envF.trace 5)) *
            (envK.trace 28 - envK.traceNext 27) =
          (1 - envF.trace 5) • (envK.trace 28 - envK.traceNext 27) := by
      rw [Algebra.smul_def, map_sub, map_one]
    rw [hsmul, coord_smul, smul_eq_mul, coord_sub, ← hcur, ← hnext]
    simpa [chainCoord, CoeffExpr.eval, extCoord, bcur] using hchainCoords k
  exact ⟨hchain, hacc, hfirstMask, hlastMask, hterminal⟩

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-- Unlike the production classifier census,
this theorem consumes the actual base, equality, and extension-fold gates, the fixed-mask Boolean
facts supplied by preprocessing, and exactly `RepairedMemoryCollisionGood`.

The `92` in the name is retained deliberately: it is the inhabitant of
`OptimizedStrictPackage.OptimizedMemoryRealization.conditional_all_92_sources`, a structure field
referenced from the SHA-pinned `OptimizedStrictFullPackage.lean`.

Scope, because it is easy to over-read: this removes the four coins from what the **source
recovery** needs.  It does **not** by itself remove them from the deployed failure union —
`MemoryChallengeTuple` still carries `selectorEquality`, `firstMask`, `lastMask` and `chain`, and
`optimizedMergedProductionFailureProbabilityBound` still carries `(20 + 14·M)/|𝔽|`.  Shrinking
the tuple and the union is the next step.

-/
theorem actual_production_recovers_all_92_sources
    (b : Basis (Fin 3) F K) (envF : Env F)
    (hbase : ∀ g ∈ foldedBaseTransitionGates b, g.eval envF = 0)
    (heq : ∀ g ∈ foldedEqualityChecks b, g.eval envF = 0)
    (hfold : ∀ g ∈ extensionTransitionGates (K := K),
      g.eval (gatherEnv b ((memorySourceTemplate b).col0 3) envF) = 0)
    (hmix : ∀ g ∈ foldedMixedTransitionGates (F := F),
      g.eval (gatherEnv b ((memorySourceTemplate b).col0 3) envF) envF = 0)
    (hfirstBool : envF.trace 4 * (envF.trace 4 - 1) = 0)
    (hlastBool : envF.trace 5 * (envF.trace 5 - 1) = 0)
    (hfoldGood : FoldCollisionExcluded
      (gatherEnv b ((memorySourceTemplate b).col0 3) envF)) :
    ∀ e ∈ transitionSources (K := K),
      e.eval (gatherEnv b ((memorySourceTemplate b).col0 3) envF) = 0 := by
  let envK := gatherEnv b ((memorySourceTemplate b).col0 3) envF
  have hsel := selector_sources_recovered_from_actual_gates b envF hbase heq
  have hprom := promoted_sources_recovered_from_actual_gates b envF hbase hmix
    hfirstBool hlastBool
  have hext : ∀ e ∈ extensionFoldSources (K := K), e.eval envK = 0 :=
    fold_to_source_of_collision_excluded envK (by simpa [envK] using hfold) hfoldGood
  intro e he
  obtain ⟨i, rfl⟩ := List.get_of_mem he
  have hlt : (i : ℕ) < 50 := by simpa [transitionSources_length] using i.isLt
  by_cases h5 : (i : ℕ) < 5
  · exact hsel _ (selector_row_mem i h5)
  by_cases hmid : (i : ℕ) < 33
  · exact hext _ (midrow_mem_fold i (by omega) hmid)
  by_cases hc : (i : ℕ) = 33
  · rw [chain_source_eq i hc]
    exact hprom.1
  by_cases hwalk : (i : ℕ) < 40
  · exact hext _ (walk_span_mem_fold i (by omega) hwalk)
  by_cases h40 : (i : ℕ) = 40
  · rw [transition_sampled_eq i ⟨0, by decide⟩ (by omega)]
    simp only [sampledSources_get_aux]
    exact hext _ (sampled_in_fold ⟨0, by decide⟩)
  by_cases h41 : (i : ℕ) = 41
  · rw [transition_sampled_eq i ⟨1, by decide⟩ (by omega)]
    simp only [sampledSources_get_aux]
    exact hext _ (sampled_in_fold ⟨1, by decide⟩)
  by_cases h42 : (i : ℕ) = 42
  · rw [transition_sampled_eq i ⟨2, by decide⟩ (by omega)]
    simp only [sampledSources_get_aux]
    exact hext _ (sampled_in_fold ⟨2, by decide⟩)
  by_cases h43 : (i : ℕ) = 43
  · rw [transition_sampled_eq i ⟨3, by decide⟩ (by omega)]
    exact hprom.2.1
  by_cases h44 : (i : ℕ) = 44
  · rw [transition_sampled_eq i ⟨4, by decide⟩ (by omega)]
    simp only [sampledSources_get_aux]
    exact hext _ (sampled_in_fold ⟨3, by decide⟩)
  by_cases h45 : (i : ℕ) = 45
  · rw [transition_sampled_eq i ⟨5, by decide⟩ (by omega)]
    exact hprom.2.2.1
  by_cases h46 : (i : ℕ) = 46
  · rw [transition_sampled_eq i ⟨6, by decide⟩ (by omega)]
    exact hprom.2.2.2.1
  by_cases h47 : (i : ℕ) = 47
  · rw [transition_sampled_eq i ⟨7, by decide⟩ (by omega)]
    simp only [sampledSources_get_aux]
    exact hext _ (sampled_in_fold ⟨4, by decide⟩)
  by_cases h48 : (i : ℕ) = 48
  · rw [transition_sampled_eq i ⟨8, by decide⟩ (by omega)]
    simp only [sampledSources_get_aux]
    exact hext _ (sampled_in_fold ⟨5, by decide⟩)
  · have h49 : (i : ℕ) = 49 := by omega
    rw [transition_sampled_eq i ⟨9, by decide⟩ (by omega)]
    exact hprom.2.2.2.2

/-- The fold half of forward completeness is unconditional and applies to the actual disjoint
`40`-source workload; canonical source satisfaction
separately compiles the base/equality buckets from the same encoded assignment. -/
theorem all_92_sources_imply_actual_extension_folds
    (b : Basis (Fin 3) F K) (envF : Env F)
    (hall : ∀ e ∈ transitionSources (K := K),
      e.eval (gatherEnv b ((memorySourceTemplate b).col0 3) envF) = 0) :
    ∀ g ∈ extensionTransitionGates (K := K),
      g.eval (gatherEnv b ((memorySourceTemplate b).col0 3) envF) = 0 := by
  apply source_to_fold_complete
  intro e he
  exact hall e (extensionFoldSources_subset_transitionSources e he)

/-! ## Collision accounting and necessity controls -/

/-- The merged fold workload is `19`; the
fourteen base-field scalar roots are untouched. -/
theorem exact_collision_workloads :
    (extensionFoldFamilies.map fun es => es.length - 1).sum = 19 ∧
      (∀ (families : Fin 7 → Fin 3 → F73),
        (scalarCompressionBadChallenges
          (List.ofFn fun i : Fin 7 => List.ofFn (families i))).card ≤ 14) :=
  ⟨extensionFoldFamilies_workload, seven_scalar_families_card_le_14⟩

theorem exact_collision_challenge_allocation :
    foldChallenge = (.Var .challenge 6 : Expr) ∧
      selectorEqualityChallenge = (.var .challenge 0 : CoeffExpr F73) ∧
      firstMaskBindingChallenge = (.var .challenge 1 : CoeffExpr F73) ∧
      lastMaskBindingChallenge = (.var .challenge 2 : CoeffExpr F73) ∧
      chainBindingChallenge = (.var .challenge 3 : CoeffExpr F73) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem both_named_collision_premises_are_necessary :
    ((∀ g ∈ extensionTransitionGates (K := ℚ),
        g.eval memoryFoldCancellationEnv = 0) ∧
      (∃ e ∈ extensionFoldSources (K := ℚ),
        e.eval memoryFoldCancellationEnv ≠ 0) ∧
      ¬ FoldCollisionExcluded memoryFoldCancellationEnv) ∧
    ((valueRlcPolynomial scalarCancellationValues).eval 1 = 0 ∧
      (∃ x ∈ scalarCancellationValues, x ≠ 0) ∧
      ¬ ValueCollisionExcluded 1 scalarCancellationValues) :=
  ⟨memory_fold_cancellation_witness, scalar_compression_cancellation_witness⟩

theorem named_direct_multiplicity_avoids_the_cancellation_witness :
    (∀ g ∈ extensionTransitionGates (K := ℚ),
        g.eval memoryFoldCancellationEnv = 0) ∧
      (∃ e ∈ extensionFoldSources (K := ℚ),
        e.eval memoryFoldCancellationEnv ≠ 0) ∧
      DirectMalformedProductionReceipt .multiplicity :=
  ⟨memory_fold_cancellation_witness.1,
    memory_fold_cancellation_witness.2.1,
    honest_direct_malformed_production_census .multiplicity⟩

/-! ## Direct malformed map and same-assignment axis assembly -/

theorem exact_malformed_map :
    malformedMemoryGateId .axis = .extensionFold 17 ∧
      malformedMemoryGateId .timestamp = .extensionFold 0 ∧
      malformedMemoryGateId .forestCount = .extensionFold 8 ∧
      malformedMemoryGateId .forestSeed = .extensionFold 9 ∧
      malformedMemoryGateId .denominator = .extensionFold 13 ∧
      malformedMemoryGateId .multiplicity = .extensionFold 14 ∧
      malformedMemoryGateId .intermediateCurrent = .base 13 ∧
      malformedMemoryGateId .intermediateNext = .base 13 ∧
      malformedMemoryGateId .accumulator = .base 10 ∧
      malformedMemoryGateId .terminal = .base 7 ∧
      (∀ s : Fin 4, malformedMemoryGateId (.selectorMirror s) = .equality s) ∧
      malformedMemoryGateId .firstMask = .preprocessing 0 ∧
      malformedMemoryGateId .lastMask = .preprocessing 1 := by
  simp [malformedMemoryGateId]

theorem every_malformed_class_directly_rejects
    (c : MalformedMemoryClass) :
    DirectMalformedProductionReceipt c :=
  honest_direct_malformed_production_census c

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

theorem same_assignment_realization_nonvacuous
    (hmore : ∀ i : Fin honestLegacyFamily.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < honestLegacyFamily.problem.cfg.kMem →
        (honestLegacyFamily.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (honestLegacyFamily.problem.exec.memoryPubAt i).pt.indicator = 0) :
    RAP.SatisfiesWithPreprocessing
        (namedSourceMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
          honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem)
        (canonicalSourceTrace honestSampled honestMemoryNodes basis73 honestLegacyFamily.problem.cfg.kMem) ∧
      RAP.SatisfiesWithPreprocessing
        (namedFinalMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
          honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem)
        (canonicalFinalMemoryTrace honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit) ∧
      -- Provisional: axis accounting on the a-bearing view `honestExecA`.
      ∀ (root : Fin honestLegacyFamily.problem.cfg.kMem) (e : ℕ),
        e ∈ AxisBridge.readExps
            (exactAxisTree honestLegacyFamily.problem.cfg honestExecA root) →
        e ∈ AxisBridge.verifyExps
            (exactAxisTree honestLegacyFamily.problem.cfg honestExecA root) →
        Nock.AxisBatching.MTree.vaxis e
            (exactAxisTree honestLegacyFamily.problem.cfg honestExecA root) =
          Nock.AxisBatching.MTree.Relaxis e
            (exactAxisTree honestLegacyFamily.problem.cfg honestExecA root) :=
  honest_memory_realization hmore

omit [FiniteDimensional F K] in
theorem every_production_assignment_threads_one_aggregate_forest
    {p : ℕ} [CharP K p] [Fintype K] [DecidableEq K]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p) {execA : ExactExecution R.problem.cfg}
    (P : MemoryProductionAssignment A execA) :
    Nock.Walk.WalkSat
        (Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows)
        (Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
        (Nock.Walk.foCol R.memoryWalkRows)
        A.exact.memoryWalk.ln A.exact.memoryWalk.count A.exact.memoryWalk.acc
        R.memoryWalkAlpha R.memoryWalkSeed
        (R.memoryWalkAlpha ^ R.problem.cfg.kMem)
        R.problem.cfg.memRows ∧
      R.memoryWalkRows = Nock.Walk.bfsForest R.problem.exec.memoryForest ∧
      R.memoryWalkSeed =
        (Nock.Walk.nodeListP
          (Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows)
          R.problem.cfg.kMem).eval R.memoryWalkAlpha ∧
      A.exact.memoryWalk.acc R.problem.cfg.memRows = 0 :=
  ⟨P.oneForestWalk.1, P.memoryWalkRows_eq_one_bfsForest,
    P.aggregateRootSeed, P.oneForestWalk.2⟩

theorem one_forest_and_retained_multiroot_scope :
    honestLegacyFamily.memoryWalkRows =
        Nock.Walk.bfsForest honestLegacyFamily.problem.exec.memoryForest ∧
      honestLegacyFamily.memoryWalkSeed =
        (Nock.Walk.nodeListP
          (Nock.Walk.curCol honestLegacyFamily.memoryNodeVal
            honestLegacyFamily.memoryWalkRows)
          honestLegacyFamily.problem.cfg.kMem).eval
            honestLegacyFamily.memoryWalkAlpha ∧
      Nock.RedTeam.Thm54P3Nonvacuity.cfg.kMem = 2 ∧
      Nock.RedTeam.Thm54P3Nonvacuity.exec.memoryForest.length = 2 ∧
      honestLegacyFamily.problem.cfg.kMem = 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem strict_package_and_alias_unchanged :
    (∀ {F K : Type} [Field F] [Field K] [Algebra F K]
      [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
      {hOrb q Λ : ℕ}
      (P : Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage F K hOrb q Λ),
      Nock.RedTeam.Batch29.B29SemanticTemplate (K := K)
        (memTemplate F) P.memLanguage) ∧
      @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest := by
  exact ⟨fun P => P.memSemanticTemplate, rfl⟩

#print axioms exact_codec_and_resource_receipt
#print axioms all_four_codec_states_are_distinct_and_covered
#print axioms final_resource_and_inert_padding_receipt
#print axioms every_source_occurrence_has_actual_authority
#print axioms production_bucket_hygiene
#print axioms actual_production_recovers_all_92_sources
#print axioms all_92_sources_imply_actual_extension_folds
#print axioms exact_collision_workloads
#print axioms exact_collision_challenge_allocation
#print axioms both_named_collision_premises_are_necessary
#print axioms named_direct_multiplicity_avoids_the_cancellation_witness
#print axioms exact_malformed_map
#print axioms every_malformed_class_directly_rejects
#print axioms same_assignment_realization_nonvacuous
#print axioms every_production_assignment_threads_one_aggregate_forest
#print axioms one_forest_and_retained_multiroot_scope
#print axioms strict_package_and_alias_unchanged

end
end Nock.RedTeam.Batch65
