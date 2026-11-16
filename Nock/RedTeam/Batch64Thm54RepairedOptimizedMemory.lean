import Nock.NockVMROM.Thm54.OptimizedMemoryConcrete
import Nock.RedTeam.Batch63Thm54OptimizedMemoryCanonicalSatisfaction
import Nock.RedTeam.Batch64Compatibility
import Nock.RedTeam.Thm54P3Nonvacuity

/-!
The governing paper frame is the aggregate forest, carried NMR
axis, memory traversal, complete Memspec, and the memory half of Theorem 5.4.

The author-selected `6/55` codec and `14/21` folding remain a recorded correctness delta rather
than a literal transcription of Appendix B.  The artifact deliberately distinguishes syntactic
base-bucket discrimination from collision-conditioned semantic redundancy in the complete
production system.
-/

namespace Nock.RedTeam.Batch64

open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Module
open Polynomial
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.AxisBridge
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
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedMemorySameExecution
open Nock.NockVMROM.Thm54.OptimizedMemorySameExecution.Concrete
open Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeSampledTrace.Concrete

noncomputable section

/-! ## Exact inventory, codec, and resource receipts -/

theorem exact_6_55_inventory :
    Fintype.card BaseRole = 6 ∧
      Fintype.card MemoryTablePayloadRole = 31 ∧
      Fintype.card ForestWalkRole = 6 ∧
      Fintype.card SampledMemoryIORole = 14 ∧
      Fintype.card StateSelectorMirrorRole = 4 ∧
      Fintype.card ExtensionRole = 56 ∧
      ((Finset.univ : Finset MemoryTablePayloadRole).image
        (fun r => (memoryTableSourceColumn r : ℕ))) = Finset.Icc 4 34 ∧
      ((Finset.univ : Finset ExtensionRole).image
        (fun r => (extensionIndex r : ℕ))) = Finset.range 56 := by
  decide

theorem codec_all_four_states_roundtrip
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (r : SemanticRow F K) :
    decode (encode r) = r :=
  decode_encode r

theorem accepted_physical_row_has_no_fallback
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (r : EncodedRow F K) (h : AcceptedControls r) :
    encode (decode r) = r :=
  encode_decode_of_accepted r h

theorem malformed_selector_controls_reject
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (r : EncodedRow F K)
    (hzero : ∀ i : Fin 4, r.base (stateSlot i) = 0)
    (hfirst : r.base 4 * (r.base 4 - 1) ≠ 0)
    (hlast : r.base 5 * (r.base 5 - 1) ≠ 0) :
    ¬ AcceptedControls r ∧ ¬ AcceptedControls r ∧ ¬ AcceptedControls r :=
  ⟨all_zero_state_rejected r hzero,
    malformed_first_mask_rejected r hfirst,
    malformed_last_mask_rejected r hlast⟩

/-- **Which numerals this theorem pins against the production basis, and which it does not.**
`memoryRowSources.length = 33` and `transitionSources.length = 50` are the production objects of
`OptimizedMemoryGateBasis`.  The remaining numerals — `93`,
`171`, `196`, `104` and the `88` — are pure arithmetic here; the production tie for them is
`exact_source_and_final_fingerprints` below, which reads `w`/`s` straight off
`namedSourceMemoryRAP` / `namedFinalMemoryRAP`, and `Batch65:50`.

The `93`/`104`/`88` arithmetic lines are **kept verbatim**: they are pure numerals and
remain true, and they now record the pre-retyping accounting.

Every `3 * 2 + 3 * 2` endpoint summand below is a pure numeral and
stays; the last line records the same total as `3 * 0 + 3 * 4`. -/
theorem exact_resource_partition :
    memoryRowSources (K := K73cubic).length = 33 ∧
      transitionSources (K := K73cubic).length = 50 ∧
      extensionTransitionGates (K := K73cubic).length = 21 ∧
      (Batch64.baseTransitionGates (F := F73)).length = 14 ∧
      (OptimizedMemoryGateBasis.baseTransitionGates (F := F73) basis73).length = 6 ∧
      (foldedBaseTransitionGates (F := F73) (K := K73cubic) basis73).length = 11 ∧
      degreeOneEndpoints.length = 0 ∧
      degreeThreeEndpoints.length = 0 ∧
      foldedDegreeThreeEndpoints.length = 4 ∧
      (OptimizedMemoryGateBasis.equalityChecks basis73).length = 0 ∧
      (foldedEqualityChecks basis73).length = 12 ∧
      (OptimizedMemoryGateBasis.mixedTransitionGates (F := F73) basis73).length = 50 ∧
      14 + 3 * 21 = 77 ∧
      77 + 3 * 2 + 3 * 2 + 4 = 93 ∧
      180 + 23 = 203 ∧
      77 + 11 = 88 ∧
      93 + 11 = 104 ∧
      11 + 3 * 24 = 83 ∧
      83 + 3 * 2 + 3 * 2 + 12 = 107 ∧
      83 + 5 = 88 ∧
      107 + 5 = 112 ∧
      11 + 3 * 25 = 86 ∧
      86 + 3 * 2 + 3 * 2 + 12 = 110 ∧
      86 + 2 = 88 ∧ 110 + 2 = 112 ∧
      11 + 3 * 26 = 89 ∧
      89 + 3 * 2 + 3 * 2 + 12 = 113 ∧
      89 + 0 = 88 + 1 ∧ 113 + 0 = 113 ∧
      89 + 3 * 0 + 3 * 4 + 12 = 113 ∧
      6 + 49 * 3 = 153 := by
  decide

theorem exact_source_and_final_fingerprints :
    let S := namedSourceMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
      honestLegacyFamily.problem.cfg.kMem
    let Q := namedFinalMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
      honestLegacyFamily.problem.cfg.kMem
    S.rap.w = 182 ∧ S.rap.s = 156 ∧ S.rap.d = 4 ∧ S.rap.k = 1 ∧
      Q.rap.w = 205 ∧ Q.rap.s = 156 ∧ Q.rap.d = 4 ∧ Q.rap.k = 1 ∧
      RAPPadding.memoryResidualColumns 3 = 23 ∧
      RAPPadding.memoryResidualTransitionGates 3 = 0 := by
  refine ⟨
    (sourceMemoryRAP_fingerprint basis73 honestMemoryChalVal honestMemoryPubVal
      strictOrbit (rowNodeSet honestMemoryNodes)).1,
    (sourceMemoryRAP_fingerprint basis73 honestMemoryChalVal honestMemoryPubVal
      strictOrbit (rowNodeSet honestMemoryNodes)).2.1,
    (sourceMemoryRAP_fingerprint basis73 honestMemoryChalVal honestMemoryPubVal
      strictOrbit (rowNodeSet honestMemoryNodes)).2.2.1,
    (sourceMemoryRAP_fingerprint basis73 honestMemoryChalVal honestMemoryPubVal
      strictOrbit (rowNodeSet honestMemoryNodes)).2.2.2,
    (finalMemoryRAP_fingerprint honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem).1,
    (finalMemoryRAP_fingerprint honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem).2.1,
    (finalMemoryRAP_fingerprint honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem).2.2.1,
    (finalMemoryRAP_fingerprint honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit honestLegacyFamily.problem.cfg.kMem).2.2.2,
    rfl, rfl⟩

theorem final_padding_equivalence :
    let S := namedSourceMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
      honestLegacyFamily.problem.cfg.kMem
    let Q := namedFinalMemoryRAP honestLegacyFamily.problem.cfg.memRows_pos
      honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
      honestLegacyFamily.problem.cfg.kMem
    ∀ P : Fin Q.rap.w → F73[X],
      RAP.SatisfiesWithPreprocessing Q P ↔
        RAP.SatisfiesWithPreprocessing S
          (RAPPadding.projectTrace S.rap
            (RAPPadding.firstRoundExtra S.rap S.rounds_pos
              (RAPPadding.memoryResidualColumns 3)) P) := by
  dsimp only
  intro P
  exact final_satisfies_iff_source honestLegacyFamily.problem.cfg.memRows_pos
    honestMemoryNodes basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
    honestLegacyFamily.problem.cfg.kMem P

/-! ## Repaired base syntax and complete-system scope -/

theorem exact_repaired_ids_7_13 {F : Type} [Field F] :
    (baseTransitionGates (F := F)).drop 7 =
      [sampledTerminalCoord (F := F) 0,
       sampledTerminalCoord (F := F) 1,
       sampledTerminalCoord (F := F) 2,
       sampledAccumulatorCoord (F := F) 0,
       sampledAccumulatorCoord (F := F) 1,
       sampledAccumulatorCoord (F := F) 2,
       intermediateChainCoord (F := F)] := by
  rfl

theorem repaired_base_bucket_is_syntactically_independent
    {F : Type} [Field F] :
    (repairedSemanticBaseGates (F := F)).Nodup ∧
      (∀ g ∈ repairedSemanticBaseGates (F := F), g ≠ .const 0) ∧
      (∀ j : Fin 7,
        let env := repairedBaseMutation (F := F) j
        let target := (repairedSemanticBaseGates (F := F)).get j
        target.eval env = 1 ∧
          ∀ g ∈ baseTransitionGates (F := F), g ≠ target → g.eval env = 0) :=
  ⟨repairedSemanticBaseGates_nodup,
    repairedSemanticBaseGates_no_literal_zero,
    repaired_base_gate_discrimination⟩

/-- A nonzero named source either reaches an actual production fold gate or witnesses failure of
the exact reverse collision premise.  This is the proper gate linkage for malformed source
controls; source nonzeroness alone is not unconditional folded rejection. -/
theorem nonzero_source_reaches_fold_or_collision
    {K : Type} [Field K] (env : Env K)
    (e : Expr) (he : e ∈ transitionSources (K := K)) (hne : e.eval env ≠ 0) :
    (∃ g ∈ extensionTransitionGates (K := K), g.eval env ≠ 0) ∨
      ¬ FoldCollisionExcluded env := by
  by_cases hc : FoldCollisionExcluded env
  · left
    by_contra hnone
    push Not at hnone
    exact hne (fold_to_source_of_collision_excluded env hnone hc e he)
  · exact Or.inr hc

/-- Under the exact collision-exclusion premise, each sampled-terminal coordinate is implied by
the complete extension-fold block.  Thus IDs `7..9` are syntactically distinct base bodies but
collision-conditioned semantic redundancies in the full production constraint system. -/
theorem sampledTerminalCoord_redundant_under_fold_collision
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (envF : Env F) (k : Fin 3)
    (hfold : ∀ g ∈ extensionTransitionGates (K := K),
      g.eval (gatherEnv b ((memorySourceTemplate b).col0 3) envF) = 0)
    (hcollision : FoldCollisionExcluded
      (gatherEnv b ((memorySourceTemplate b).col0 3) envF)) :
    (sampledTerminalCoord (F := F) k).eval envF = 0 := by
  let envK := gatherEnv b ((memorySourceTemplate b).col0 3) envF
  have hs : (Expr.Sub (extVar .traceCur 40) (extVar .publicVal 2)).eval envK = 0 :=
    fold_to_source_of_collision_excluded envK hfold hcollision
      (.Sub (extVar .traceCur 40) (extVar .publicVal 2))
      (by simp [transitionSources, sampledSources])
  have hc := coordinateCompile_eval b ((memorySourceTemplate b).col0 3)
    (isCoordEnv_gather b ((memorySourceTemplate b).col0 3) envF)
    (.Sub (extVar .traceCur 40) (extVar .publicVal 2)) k
  rw [hs, coord_zero] at hc
  simpa [envK, sampledTerminalCoord, extCoord, coordinateCompile,
    memorySourceTemplate, ChipTemplate.col0, ChipTemplate.baseCols, extVar] using hc.symm

/-- The same exact implication holds for accumulator-residual IDs `10..12`. -/
theorem sampledAccumulatorCoord_redundant_under_fold_collision
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (envF : Env F) (k : Fin 3)
    (hfold : ∀ g ∈ extensionTransitionGates (K := K),
      g.eval (gatherEnv b ((memorySourceTemplate b).col0 3) envF) = 0)
    (hcollision : FoldCollisionExcluded
      (gatherEnv b ((memorySourceTemplate b).col0 3) envF)) :
    (sampledAccumulatorCoord (F := F) k).eval envF = 0 := by
  let src : Expr :=
    .Sub (extVar .traceCur 44)
      (.Add (extVar .traceCur 43) (extVar .traceCur 42))
  let envK := gatherEnv b ((memorySourceTemplate b).col0 3) envF
  have hs : src.eval envK = 0 :=
    fold_to_source_of_collision_excluded envK hfold hcollision src
      (by simp [src, transitionSources, sampledSources])
  have hc := coordinateCompile_eval b ((memorySourceTemplate b).col0 3)
    (isCoordEnv_gather b ((memorySourceTemplate b).col0 3) envF) src k
  rw [hs, coord_zero] at hc
  simpa [src, envK, sampledAccumulatorCoord, extCoord, coordinateCompile,
    memorySourceTemplate, ChipTemplate.col0, ChipTemplate.baseCols, extVar] using hc.symm

theorem first_six_repairs_are_collision_conditioned_redundancies
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (envF : Env F)
    (hfold : ∀ g ∈ extensionTransitionGates (K := K),
      g.eval (gatherEnv b ((memorySourceTemplate b).col0 3) envF) = 0)
    (hcollision : FoldCollisionExcluded
      (gatherEnv b ((memorySourceTemplate b).col0 3) envF)) :
    ∀ j : Fin 6, ((repairedSemanticBaseGates (F := F)).get
      ⟨j, by have := j.isLt; simp [repairedSemanticBaseGates]; omega⟩).eval envF = 0 := by
  intro j
  fin_cases j
  · exact sampledTerminalCoord_redundant_under_fold_collision b envF 0 hfold hcollision
  · exact sampledTerminalCoord_redundant_under_fold_collision b envF 1 hfold hcollision
  · exact sampledTerminalCoord_redundant_under_fold_collision b envF 2 hfold hcollision
  · exact sampledAccumulatorCoord_redundant_under_fold_collision b envF 0 hfold hcollision
  · exact sampledAccumulatorCoord_redundant_under_fold_collision b envF 1 hfold hcollision
  · exact sampledAccumulatorCoord_redundant_under_fold_collision b envF 2 hfold hcollision

/-! ## Fold semantics and concrete non-vacuity -/

theorem fold_forward_is_unconditional
    {K : Type} [Field K] (env : Env K)
    (h : ∀ e ∈ transitionSources (K := K), e.eval env = 0) :
    ∀ g ∈ extensionTransitionGates (K := K), g.eval env = 0 :=
  source_to_fold_complete env h

theorem fold_reverse_has_exact_premise
    {K : Type} [Field K] (env : Env K)
    (hfold : ∀ g ∈ extensionTransitionGates (K := K), g.eval env = 0)
    (hcollision : FoldCollisionExcluded env) :
    ∀ e ∈ transitionSources (K := K), e.eval env = 0 :=
  fold_to_source_of_collision_excluded env hfold hcollision

theorem named_malformed_sources_are_actual_fold_constituents :
    verifyAxisSource (K := K73cubic) ∈ transitionSources (K := K73cubic) ∧
      readTimestampSource (K := K73cubic) ∈ transitionSources (K := K73cubic) ∧
      forestCountSource ∈ transitionSources (K := K73cubic) ∧
      forestSeedSource ∈ transitionSources (K := K73cubic) ∧
      denominatorSource ∈ transitionSources (K := K73cubic) ∧
      multiplicitySource ∈ transitionSources (K := K73cubic) := by
  simp [transitionSources, verifyAxisSource_mem, readTimestampSource_mem,
    forestCountSource_mem, forestSeedSource_mem, denominatorSource_mem,
    multiplicitySource_mem]

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

theorem honest_fold_premise_all_rows
    (i : Fin honestLegacyFamily.problem.cfg.memRows) :
    OptimizedMemoryGateBasis.FoldCollisionExcluded
      (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
        honestMemoryChalVal honestMemoryPubVal strictOrbit i) :=
  Nock.RedTeam.Batch63.honest_foldCollisionExcluded_nonvacuous i

theorem concrete_active_row_premises :
    ((ConcreteStrictPackage.exec honestSeed honestAlpha).memoryPubAt
        ⟨1, by norm_num [ConcreteStrictPackage.cfg]⟩).st = .read_root ∧
      ((ConcreteStrictPackage.exec honestSeed honestAlpha).memoryPubAt
        ⟨4, by norm_num [ConcreteStrictPackage.cfg]⟩).st = .verify_child ∧
      ((ConcreteStrictPackage.exec honestSeed honestAlpha).memoryPubAt
        ⟨4, by norm_num [ConcreteStrictPackage.cfg]⟩).mem.ts ≠ 0 ∧
      responseActive (K := K73cubic)
        ((ConcreteStrictPackage.exec honestSeed honestAlpha).memoryPubAt
          ⟨1, by norm_num [ConcreteStrictPackage.cfg]⟩).ver = 1 := by
  rw [ConcreteStrictPackage.memoryPubAt_one,
    ConcreteStrictPackage.memoryPubAt_four]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp only [ConcreteStrictPackage.verifyPub, ConcreteStrictPackage.requestRecord,
      ConcreteStrictPackage.honestAlpha]
    have hfour : (4 : K73cubic) ≠ 0 := by
      have hbase : (4 : F73) ≠ 0 := by decide
      intro h
      apply hbase
      apply (algebraMap F73 K73cubic).injective
      simpa only [map_ofNat, map_zero] using h
    exact hfour
  · simp [ConcreteStrictPackage.readPub, responseActive]

/-! ## Same-object axis, forest, malformed controls, and canonical satisfaction -/

theorem exact_axis_theorem_shape
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    {A : SampledIOSameExecutionAssignment R p} {execA : ExactExecution R.problem.cfg}
    -- Axis accounting on the a-bearing view `execA`.
    (h2 : (2 : K) ≠ 0) (P : MemoryProductionAssignment A execA)
    (i : Fin R.problem.cfg.kMem) (e : ℕ)
    (hr : e ∈ readExps (exactAxisTree R.problem.cfg execA i))
    (hv : e ∈ verifyExps (exactAxisTree R.problem.cfg execA i)) :
    vaxis e (exactAxisTree R.problem.cfg execA i) =
      Relaxis e (exactAxisTree R.problem.cfg execA i) :=
  P.axis_eq_relaxis_of_used h2 i e hr hv

theorem concrete_axis_boundary_nonvacuous :
    (∀ i : Fin honestLegacyFamily.problem.cfg.kMem,
      countsP_bin (exactAxisTree honestLegacyFamily.problem.cfg
        honestExecA i) = 0) ∧
      Nonempty (MemoryProductionAssignment honestSampled honestExecA) :=
  ⟨honest_axisRootPolynomial, honest_same_object_nonvacuous⟩

theorem one_aggregate_forest_and_seed :
    honestLegacyFamily.memoryWalkRows =
        Nock.Walk.bfsForest honestLegacyFamily.problem.exec.memoryForest ∧
      honestLegacyFamily.memoryWalkSeed =
        (Nock.Walk.nodeListP
          (Nock.Walk.curCol honestLegacyFamily.memoryNodeVal
            honestLegacyFamily.memoryWalkRows)
          honestLegacyFamily.problem.cfg.kMem).eval
            honestLegacyFamily.memoryWalkAlpha ∧
      honestSampled.exact.memoryWalk.acc
        honestLegacyFamily.problem.cfg.memRows = 0 := by
  exact ⟨rfl, rfl, honestProduction.oneForestWalk.2⟩

theorem two_root_scope_controls :
    Nock.RedTeam.Thm54P3Nonvacuity.cfg.kMem = 2 ∧
      Nock.RedTeam.Thm54P3Nonvacuity.exec.memoryForest.length = 2 ∧
      (1 : ZMod 17) * 4 + 2 * 4 ^ 2 ≠
        (2 : ZMod 17) * 4 + 1 * 4 ^ 2 ∧
      (1 : ZMod 17) * 4 + 2 * 4 ^ 2 ≠
        (1 : ZMod 17) * 4 + 1 * 4 ^ 2 ∧
      (4 : ZMod 17) ^ 2 = 16 ∧ (4 : ZMod 17) ^ 2 ≠ 15 := by
  decide

theorem concrete_source_final_and_fold_nonvacuous
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
      (∀ i : Fin honestLegacyFamily.problem.cfg.memRows,
        OptimizedMemoryGateBasis.FoldCollisionExcluded
          (canonicalGatheredEnv honestSampled honestMemoryNodes basis73
            honestMemoryChalVal honestMemoryPubVal strictOrbit i)) :=
  ⟨honest_source_memory_satisfies hmore, honest_final_memory_satisfies hmore,
    honest_fold_premise_all_rows⟩

theorem malformed_sources_have_exact_fold_boundary
    (env : Env K73cubic) (e : Expr) (he : e ∈ transitionSources (K := K73cubic))
    (hne : e.eval env ≠ 0) :
    (∃ g ∈ extensionTransitionGates (K := K73cubic), g.eval env ≠ 0) ∨
      ¬ FoldCollisionExcluded env :=
  nonzero_source_reaches_fold_or_collision env e he hne

theorem repaired_ids_have_named_production_rejection :
    ∀ j : Fin 7,
      let target := (repairedSemanticBaseGates (F := F73)).get j
      let pivot :=
        if (j : ℕ) < 3 then 126 + (j : ℕ)
        else if (j : ℕ) < 6 then 138 + ((j : ℕ) - 3)
        else 90
      target.eval
        (mutateCurrentTrace
          (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
            honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex)
          pivot 1) = 1 :=
  honest_repaired_ids_7_13_named_rejection

theorem fixed_masks_reject_at_exact_final_slots :
    (∀ (Q : Fin honestFinalMemoryRAP.rap.w → F73[X]),
      Q (honestFinalMemoryRAP.preprocessingIndex ⟨0, by change 0 < 4; norm_num⟩) ≠
          honestFinalMemoryRAP.preprocessing ⟨0, by change 0 < 4; norm_num⟩ →
        ¬ RAP.SatisfiesWithPreprocessing honestFinalMemoryRAP Q) ∧
      (∀ (Q : Fin honestFinalMemoryRAP.rap.w → F73[X]),
      Q (honestFinalMemoryRAP.preprocessingIndex ⟨1, by change 1 < 4; norm_num⟩) ≠
          honestFinalMemoryRAP.preprocessing ⟨1, by change 1 < 4; norm_num⟩ →
        ¬ RAP.SatisfiesWithPreprocessing honestFinalMemoryRAP Q) :=
  ⟨honest_wrong_first_mask_preprocessing_rejected,
    honest_wrong_last_mask_preprocessing_rejected⟩

theorem concrete_row_budget_is_M_plus_2L :
    (ConcreteStrictPackage.cfg honestSeed honestAlpha).memRows =
      RowLayout.memoryM (ConcreteStrictPackage.exec honestSeed honestAlpha) +
        2 * RowLayout.memoryL (ConcreteStrictPackage.exec honestSeed honestAlpha) :=
  RowLayout.memRows_eq_M_add_two_mul_L_of_count_balance
    ConcreteStrictPackage.recordCountBalance

/-! ## Wrong-layer boundary -/

theorem strict_package_still_carries_B29
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ}
    (P : Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage F K hOrb q Λ) :
    Nock.RedTeam.Batch29.B29SemanticTemplate (K := K)
        (memTemplate F) P.memLanguage :=
  P.memSemanticTemplate

theorem paper_alias_unchanged :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  rfl

#print axioms exact_6_55_inventory
#print axioms codec_all_four_states_roundtrip
#print axioms accepted_physical_row_has_no_fallback
#print axioms malformed_selector_controls_reject
#print axioms exact_resource_partition
#print axioms exact_source_and_final_fingerprints
#print axioms final_padding_equivalence
#print axioms exact_repaired_ids_7_13
#print axioms repaired_base_bucket_is_syntactically_independent
#print axioms nonzero_source_reaches_fold_or_collision
#print axioms sampledTerminalCoord_redundant_under_fold_collision
#print axioms sampledAccumulatorCoord_redundant_under_fold_collision
#print axioms first_six_repairs_are_collision_conditioned_redundancies
#print axioms named_malformed_sources_are_actual_fold_constituents
#print axioms honest_fold_premise_all_rows
#print axioms concrete_active_row_premises
#print axioms exact_axis_theorem_shape
#print axioms concrete_axis_boundary_nonvacuous
#print axioms one_aggregate_forest_and_seed
#print axioms two_root_scope_controls
#print axioms concrete_source_final_and_fold_nonvacuous
#print axioms repaired_ids_have_named_production_rejection
#print axioms fixed_masks_reject_at_exact_final_slots
#print axioms concrete_row_budget_is_M_plus_2L
#print axioms strict_package_still_carries_B29
#print axioms paper_alias_unchanged

end
end Nock.RedTeam.Batch64
