import Nock.NockVMROM.Thm54.MultiRootHonestCommitment
import Nock.RedTeam.Batch77Thm54UniversalPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Theorem 5.4 converged commitment boundary

Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

This artifact gates:

The controls distinguish fingerprint binding from noun injectivity.  Rendering satisfies
`BindsAt` by construction, while an unrendered row with a genuinely different fingerprint is
rejected.  At the fixture's nonzero seed `-1`, distinct two-leaf nouns can collide, exactly the
probabilistic NPR phenomenon of the paper; therefore `BindsAt` is not, and must not be
reported as, a noun-equality predicate without a `SepSeed` hypothesis.

The all-zero later-round message is also adjudicated exactly: the constructed multi-root strategy
accepts no joint coin because the raw verifier requires every response multiplicity to be nonzero.
Consequently six acceptance/security-facing fields of the fourteen-field released statement are
uninformative at this witness.  The optimized chips, exact language/completeness, genuine
positionless shared IO, walk bounds, exact resources, row budgets, and aggregate forest/axis
connective remain substantive; `structural` is their dependent type-level summary.
-/

namespace Nock.RedTeam.Batch78

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Noun Nock.Walk Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.RawSemanticAssembly
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrictCommitment
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedMemorySameExecution
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic :=
  MultiRootHonestCommitment.instFintypeK97cubic
noncomputable local instance : DecidableEq K97cubic :=
  MultiRootHonestCommitment.instDecidableEqK97cubic
local instance char97 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)

/-! ## A. The renderer: exact strength and negative controls -/

/-- A noun different from the fixture subject but with the same NPR fingerprint at `z = -1`.
For two-leaf nouns the leaf polynomial is `a + b z`; `(7,9)` and `(8,10)` collide at `-1`.
This is the collision event bounded at the paper, not noun injectivity. -/
def collidingSubject : Noun := .cell (.atom 8) (.atom 10)

theorem collidingSubject_ne : collidingSubject ≠ subjectS := by
  decide

theorem collidingSubject_enc_eq :
    GlobalCarryRecognizer.enc servedSeed collidingSubject =
      GlobalCarryRecognizer.enc servedSeed subjectS := by
  rw [collidingSubject, subjectS,
    GlobalCarryRecognizer.enc_cons servedSeed_ne,
    GlobalCarryRecognizer.enc_cons servedSeed_ne,
    GlobalCarryRecognizer.enc_atom, GlobalCarryRecognizer.enc_atom,
    GlobalCarryRecognizer.enc_atom, GlobalCarryRecognizer.enc_atom]
  ext <;> norm_num [ComputeTable.FP.cons, ComputeTable.FP.atomFP, servedSeed]

/-- Change only the committed subject noun of the OP4 parent skeleton. -/
def collidingParentSkeleton : ComputeRowSkeleton :=
  { parentSkeletonRow with subject := collidingSubject }

/-- At the colliding honest seed, the original production row binds the wrong committed noun.
Thus `BindComputeRow` constrains fingerprints, not noun equality. -/
theorem colliding_noun_binds_original_row :
    BindComputeRow servedSeed collidingParentSkeleton parentRowS := by
  have h := bind_parentRow
  rcases h with ⟨hstate, hz, hpub, hs, hf, he, hdec, hsub, hmem⟩
  refine ⟨hstate, hz, hpub, ?_, hf, he, hdec, hsub, hmem⟩
  rw [bindFP, collidingParentSkeleton]
  change parentRowS.2.2.1.s = GlobalCarryRecognizer.enc servedSeed collidingSubject
  rw [collidingSubject_enc_eq]
  exact hs

/-- The identity lemma really is exact: on a binding row rendering performs no normalization.
The collision control above shows why this still does not imply noun equality. -/
theorem colliding_render_identity :
    renderComputeRow servedSeed collidingParentSkeleton parentRowS = parentRowS :=
  renderComputeRow_eq_self colliding_noun_binds_original_row

/-- A second wrong noun used for the rejecting control.  At seed `1` its leaf coordinate is `64`,
while the fixture subject's is `16`. -/
def separatedSubject : Noun := .cell (.atom 0) (.atom 64)

def separatedParentSkeleton : ComputeRowSkeleton :=
  { parentSkeletonRow with subject := separatedSubject }

/-- Away from the collision, the two committed nouns have different fingerprints. -/
theorem separatedSubject_enc_ne_at_one :
    GlobalCarryRecognizer.enc (1 : K97cubic) separatedSubject ≠
      GlobalCarryRecognizer.enc (1 : K97cubic) subjectS := by
  intro h
  have hone : (1 : K97cubic) ≠ 0 := one_ne_zero
  have hc₁ := GlobalCarryRecognizer.enc_cons hone (.atom 0) (.atom 64)
  have hc₂ := GlobalCarryRecognizer.enc_cons hone (.atom 7) (.atom 9)
  rw [separatedSubject, subjectS, hc₁, hc₂,
    GlobalCarryRecognizer.enc_atom, GlobalCarryRecognizer.enc_atom,
    GlobalCarryRecognizer.enc_atom, GlobalCarryRecognizer.enc_atom] at h
  have hl := congrArg ComputeTable.FP.leaf h
  norm_num [ComputeTable.FP.cons, ComputeTable.FP.atomFP] at hl
  exact ts_16_ne_64 hl.symm

/-- Rendering a wrong committed noun still binds, because rendering is the honest prover's
constructor of the sampled row.  This is commit-first completeness, not an independent check. -/
theorem rendered_wrong_noun_binds :
    BindComputeRow (1 : K97cubic) separatedParentSkeleton
      (renderComputeRow (1 : K97cubic) separatedParentSkeleton parentRowS) :=
  bindComputeRow_render _ _ _

/-- The binding predicate does bite on data not produced from that skeleton: a row rendered from
the correct subject at the same seed is rejected by the wrong-subject skeleton. -/
theorem unrendered_wrong_noun_rejected :
    ¬ BindComputeRow (1 : K97cubic) separatedParentSkeleton
      (renderComputeRow (1 : K97cubic) parentSkeletonRow parentRowS) := by
  intro h
  have hs := h.2.2.2.1
  rw [bindFP] at hs
  have hs' :
      GlobalCarryRecognizer.enc (1 : K97cubic) subjectS =
        GlobalCarryRecognizer.enc (1 : K97cubic) separatedSubject := by
    simpa [renderComputeRow, renderPub, separatedParentSkeleton, parentSkeletonRow] using hs
  exact separatedSubject_enc_ne_at_one hs'.symm

/-! ## Genuine multi-root execution and positionless permutation -/

theorem fourteen_rows_all_vmem :
    execS.memoryRows.length = 15 ∧ execS.MemoryRowsAccepted :=
  ⟨by rw [execution_rowsS.2]; rfl, memory_rows_acceptedS⟩

theorem interleaved_global_chain_closes :
    execS.memoryRows =
        [dummyHaltLabelS, aReadOuterLabel, bReadLabel, aDecomposeOuterLabel, bDecomposeLabel,
          aHeadHaltLabel, aReadInnerLabel, bVerifyLabel, bTailHaltLabel,
          aVerifyOuterLabel, bResultHaltLabel, aDecomposeInnerLabel, aInnerHeadHaltLabel,
          aVerifyInnerLabel, aTailHaltLabel] ∧
      (∀ i : Fin cfgS.memRows, ∀ _ : (i : ℕ) + 1 < cfgS.memRows,
        (execS.memoryPubAt i).icur =
          (execS.memoryPubAt ⟨(i : ℕ) + 1, by omega⟩).ipre) ∧
      (dummyHaltPubS.ipre, dummyHaltPubS.icur, aReadOuterPub.icur, bReadPub.icur,
        aDecomposeOuterPub.icur, bDecomposePub.icur, aHeadHaltPub.icur, aReadInnerPub.icur,
        bVerifyPub.icur, bTailHaltPub.icur, aVerifyOuterPub.icur, bResultHaltPub.icur,
        aDecomposeInnerPub.icur, aInnerHeadHaltPub.icur, aVerifyInnerPub.icur,
        aTailHaltPub.icur) =
        ((0 : K97cubic), 0, -1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0) ∧
      dummyHaltPubS.ipre = 0 ∧ aTailHaltPub.icur = 0 :=
  ⟨execution_rowsS.2, memory_chainS, accumulator_valuesS, rfl, rfl⟩

theorem responses_are_genuine_nonidentity_permutation :
    execS.derivedResponseIO.Perm execS.derivedRequestIO ∧
      execS.derivedResponseIO ≠ execS.derivedRequestIO := by
  constructor
  · rw [derived_responsesS, derived_requestsS]
    exact List.Perm.cons _ (List.Perm.swap _ _ [])
  · rw [derived_responsesS, derived_requestsS]
    intro h
    have hsecond := congrArg (fun l => l[1]?) h
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at hsecond
    have hts : servedRecord.ts ≠ servedFormulaRecord.ts := by
      rw [ts_servedRecord, ts_servedFormulaRecord]
      exact ts_16_ne_64.symm
    exact (encRec_ne_of_ts_ne (r := servedRecord) (s := servedFormulaRecord) hts)
      (Option.some.inj hsecond)

theorem rootB_is_real_left_descent :
    ServedMemoryTrace.axisPath 2 = [false] ∧
      Noun.slot 2 subjectS = some resultS ∧
      serviceB.axis = 2 :=
  ⟨axisPath_two, slot_subjectS, rfl⟩

theorem ao48_deferred_scope_reached
    (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution) :
    Nonempty (MemoryProductionAssignment sampledAssignmentM execSA) ∧
      cfgS.kMem = 3 ∧
      (rootTracesS ⟨1, by norm_num [cfgS]⟩).services ≠ [] ∧
      (rootTracesS ⟨2, by norm_num [cfgS]⟩).services ≠ [] ∧
      SemanticTrace.requiredServedLookups
        (execS.computeRowAt ⟨1, by norm_num [cfgS]⟩).1 = 1 :=
  ⟨(deferred_full_sampled_memoryProduction_closed hmoreM).1, rfl,
    both_roots_serviced.1, both_roots_serviced.2,
    (residualM_distinct_from_f73).2.2.2⟩

/-! ## C. Exhaustive three-layer field provenance -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]
variable {E : BuildableNockExecution F K}

/-- Exhaustive eta receipt for `Data`: exactly sixteen supplied fields. -/
theorem data_eta (D : HonestCommitment.Data E) :
    D =
      { computeNodes := D.computeNodes
        memoryNodes := D.memoryNodes
        compute_rows := D.compute_rows
        memory_rows := D.memory_rows
        computeOK := D.computeOK
        memoryOK := D.memoryOK
        root_line_exponent := D.root_line_exponent
        root_line_origin := D.root_line_origin
        nounSizeBound := D.nounSizeBound
        Λ := D.Λ
        slotSemantics := D.slotSemantics
        recordEquations := D.recordEquations
        census := D.census
        sizeWindowBound := D.sizeWindowBound
        q_eq_ringChar := D.q_eq_ringChar
        skeletonBounded := D.skeletonBounded
        combinedBounded := D.combinedBounded } := by
  cases D
  rfl

/-- The displayed right-hand side gives the authoritative 13-derived / 8-copied split. -/
theorem commitmentResidualOf_eta
    (D : HonestCommitment.Data E)
    (A : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      AlphaMCommitment (p := ringChar K) D.timestampStrategy z hz α lmb)
    (W : ∀ (ω : JointCoins K) (_lmb : K), nprSeed ω ≠ 0 → RawWalkArrays K) :
    commitmentResidualOf D A W =
      { verifier := verifierOf D A W
        commitment := ⟨D.skeleton, D.nounSizeBound⟩
        claim_eq := rfl
        scan := fun z _ α lmb =>
          activeFingerprintChecksAt_of_bindsAt (D.binds z α lmb)
        shapeMatch := fun z _ α lmb =>
          execTreeShapeMatchesAt_of_bindsAt (D.binds z α lmb)
        rowFrame := fun z _ α lmb =>
          rowFrameChecksAt_of_bindsAt (D.binds z α lmb)
        slotSemantics := D.slotSemantics
        recordEquations := D.recordEquations
        Λ := D.Λ
        census := D.census
        sizeWindowBound := D.sizeWindowBound
        honestSeed := E.cfg.challenges.z
        honestSeed_ne := D.honestSeed_ne
        honestAlpha := E.cfg.challenges.α
        honest_specialization := D.honest_specialization
        computeLineOrigin := D.line_origin
        q_eq_ringChar := D.q_eq_ringChar
        skeletonBounded := D.skeletonBounded
        combinedBounded := D.combinedBounded
        KszBound := fun _ _ _ _ => E.Ksz_lt_ringChar
        progCapacity := fun z _ α lmb => by
          show ((D.executionTemplate z).specialize α lmb).derivedRequestIO.length + 1 ≤
            2 ^ E.cfg.orbit.h
          rw [derivedRequestIO_length_eq (D.binds z α lmb) D.honest_binds]
          exact E.programIOCapacity
        memCapacity := fun z _ α lmb => by
          show ((D.executionTemplate z).specialize α lmb).derivedResponseIO.length + 1 ≤
            2 ^ E.cfg.orbit.h
          rw [derivedResponseIO_length_eq (D.binds z α lmb) D.honest_binds]
          exact E.memoryIOCapacity } :=
  rfl

theorem exact_three_layer_counts :
    21 = 13 + 8 ∧ 15 = 2 + 2 + 2 + 1 + 1 + 6 + 1 ∧
      35 = 10 + 4 + 21 ∧ 29 = 11 + 6 + 9 + 3 :=
  ⟨by norm_num, by norm_num,
    Nock.RedTeam.Batch77.exact_field_count_adjudication.1,
    Nock.RedTeam.Batch77.exact_field_count_adjudication.2.1⟩

/-! ## Statement informativeness at `packageM` -/

/-- The all-zero later-round message cannot pass the raw verifier's mandatory nonzero
multiplicity gate.  Hence the constructed multi-root production strategy accepts no joint coin. -/
theorem packageM_accepts_none (ω : JointCoins K97cubic) (lmb : K97cubic) :
    ¬ (packageM hmoreM).strategy.Accepts ω lmb := by
  intro hacc
  by_cases hz : nprSeed ω = 0
  · simpa [ProductionStrategy.Accepts, hz] using hacc
  · have hp :
        ProductionAxisStructureAccepts (packageM hmoreM).strategy.verifier ω lmb ∧
          (packageM hmoreM).strategy.RootAxisBoundaryAt (nprSeed ω) hz (alphaM ω) := by
      simpa [ProductionStrategy.Accepts, hz] using hacc
    have hprod : ProductionAxisStructureAccepts (packageM hmoreM).strategy.verifier ω lmb := hp.1
    have hchecks :=
      ((ProductionAxisStructureVerifier.accepts_iff (packageM hmoreM).strategy.verifier ω lmb hz).1 hprod).1
    have hgates := hchecks.1
    unfold RawMessage.VerifierGates at hgates
    rcases hgates with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hmult, _, _, _, _⟩
    have hlen :
        ((packageM hmoreM).strategy.verifier.raw.familyAt ω lmb hz).exec.derivedResponseIO.length = 3 := by
      change ((dataM.executionTemplate (nprSeed ω)).specialize
        (alphaM ω) lmb).derivedResponseIO.length = 3
      rw [derivedResponseIO_length_eq (dataM.binds (nprSeed ω) (alphaM ω) lmb)
        dataM.honest_binds]
      change execS.derivedResponseIO.length = 3
      rw [derived_responsesS]
      rfl
    let j : Fin
        ((packageM hmoreM).strategy.verifier.raw.familyAt ω lmb hz).exec.derivedResponseIO.length :=
      ⟨0, by rw [hlen]; decide⟩
    have hne := hmult j
    exact hne rfl

theorem packageM_falseAcceptance_empty :
    FalseAcceptanceSet (packageM hmoreM).strategy 97 3 cfgS.challenges.lam = ∅ := by
  ext ω
  constructor
  · intro hω
    rw [mem_falseAcceptanceSet_iff] at hω
    exact (packageM_accepts_none hmoreM ω cfgS.challenges.lam hω.1).elim
  · intro hω
    simp at hω


/-- Exact classification of the released statement at this witness.  Seven first-order fields
remain substantive, `structural` is a dependent type-level summary, and all six acceptance/security
fields quantify over empty acceptance sets here. -/
theorem statementM_scope
    (hax : FormRAxisBound (packageM hmoreM).optimized.sampled (packageM hmoreM).optimized.basis)
    (hbasis : FormRBasis (packageM hmoreM).optimized.basis)
    (hwidth : FormRWidth F97) :
    OptimizedComputeRealizationAt (packageM hmoreM).optimized.sampled
        (packageM hmoreM).optimized.computeObligations (packageM hmoreM).optimized.computeNodes
        (packageM hmoreM).optimized.basis (packageM hmoreM).optimized.computeChallenge
        (packageM hmoreM).optimized.computePublic (packageM hmoreM).optimized.orbit ∧
      OptimizedMemoryRealizationAt (packageM hmoreM).optimized.sampled
        (packageM hmoreM).optimized.memoryProduction (packageM hmoreM).optimized.memoryNodes
        (packageM hmoreM).optimized.basis (packageM hmoreM).optimized.memoryChallenge
        (packageM hmoreM).optimized.memoryPublic (packageM hmoreM).optimized.orbit ∧
      IO.LIO (packageM hmoreM).objects.cfg.Ksz (packageM hmoreM).objects.reqRecs (packageM hmoreM).objects.respRecs ∧
      Language
        (Tag F97 K97cubic (packageM hmoreM).objects.cfg.challenges.α
          (packageM hmoreM).objects.cfg.challenges.β (packageM hmoreM).objects.cfg.Ksz)
        (stmtOfExact (packageM hmoreM).objects.cfg (packageM hmoreM).objects.exec) ∧
      (packageM hmoreM).computeChip.rap.w = 303 ∧ (packageM hmoreM).computeChip.rap.s = 418 ∧
      (packageM hmoreM).memoryChip.rap.w = 205 ∧ (packageM hmoreM).memoryChip.rap.s = 156 ∧
      (packageM hmoreM).computeChip.rap.H.card = 2 ∧
      (packageM hmoreM).memoryChip.rap.H.card =
        RowLayout.memoryM (packageM hmoreM).objects.exec + 2 * RowLayout.memoryL (packageM hmoreM).objects.exec ∧
      (packageM hmoreM).optimized.OptimizedSharedMemoryConnective ∧
      FalseAcceptanceSet (packageM hmoreM).strategy 97 3 cfgS.challenges.lam = ∅ :=
  ⟨(statementM hmoreM hax hbasis hwidth).optimized_chips.1,
    (statementM hmoreM hax hbasis hwidth).optimized_chips.2,
    (statementM hmoreM hax hbasis hwidth).shared_io,
    (statementM hmoreM hax hbasis hwidth).perfect_completeness,
    (regressionM hmoreM hax hbasis hwidth).2.2.1, (regressionM hmoreM hax hbasis hwidth).2.2.2.1,
    (regressionM hmoreM hax hbasis hwidth).2.2.2.2.1, (regressionM hmoreM hax hbasis hwidth).2.2.2.2.2.1,
    (regressionM hmoreM hax hbasis hwidth).2.2.2.2.2.2.1,
    (statementM hmoreM hax hbasis hwidth).row_budgets.2,
    (statementM hmoreM hax hbasis hwidth).shared_forest_axis, packageM_falseAcceptance_empty hmoreM⟩

/-- `statementM_of_arrays` really has no hidden restriction on either later-round family. -/
theorem statementM_of_every_arrays
    (A : ∀ (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic),
      AlphaMCommitment (p := ringChar K97cubic) dataM.timestampStrategy z hz α lmb)
    (W : ∀ (ω : JointCoins K97cubic) (_lmb : K97cubic), nprSeed ω ≠ 0 → RawWalkArrays K97cubic)
    (hax : FormRAxisBound
      (buildFullPackage multiRootExecution inputsM
            (commitmentResidualOf dataM A W) inputsM_challenges
            pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
            (residualOf_generated A W) f97_primeField).optimized.sampled
      (buildFullPackage multiRootExecution inputsM
            (commitmentResidualOf dataM A W) inputsM_challenges
            pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
            (residualOf_generated A W) f97_primeField).optimized.basis)
    (hbasis : FormRBasis
      (buildFullPackage multiRootExecution inputsM
            (commitmentResidualOf dataM A W) inputsM_challenges
            pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
            (residualOf_generated A W) f97_primeField).optimized.basis)
    (hwidth : FormRWidth F97) :
    OptimizedFullStrictThm54Statement
      (buildFullPackage multiRootExecution inputsM
        (commitmentResidualOf dataM A W) inputsM_challenges
        pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
            (residualOf_generated A W) f97_primeField) :=
  statementM_of_arrays hmoreM A W hax hbasis hwidth

/-- Lean's production protocol excludes the zero NPR seed at the acceptance boundary and counts it
as a failure class.  The cited paper lines sample uniformly from `K`; they do not literally state
this `Kˣ` restriction. -/
theorem zero_seed_is_outside_strategy_domain
    (T : ProductionStrategy F K) (ω : JointCoins K) (lmb : K) (hzero : nprSeed ω = 0) :
    ¬ T.Accepts ω lmb := by
  simp [ProductionStrategy.Accepts, hzero]

/-! ## E. -/

noncomputable local instance : Fintype ConcreteStrictPackage.K73cubic :=
  BuildablePackage.Concrete.instFintypeK73cubic
noncomputable local instance : DecidableEq ConcreteStrictPackage.K73cubic :=
  BuildablePackage.Concrete.instDecidableEqK73cubic
local instance : CharP ConcreteStrictPackage.K73cubic 73 :=
  ConcreteStrictPackage.concrete_char73
local instance : CharP ConcreteStrictPackage.K73cubic
    (ringChar ConcreteStrictPackage.K73cubic) :=
  ringChar.charP ConcreteStrictPackage.K73cubic

variable (hmore : BuildableAxisWitness.LaterSeedZeros
    Nock.NockVMROM.Thm54.BuildableConcrete.concreteExecution)

/-- The constructor-produced F73 package reuses exactly the hand-built accepting production
strategy carried by `BuildablePackage.Concrete.residual73`. -/
theorem constructed_package73_strategy_eq :
    (BuildablePackage.Concrete.package73 hmore).strategy =
      ConcreteStrictPackage.concreteStrictPackage.strategy :=
  rfl

theorem constructed_package73_accepts :
    (BuildablePackage.Concrete.package73 hmore).strategy.Accepts
      ConcreteStrictPackage.honestCoins MemoryTable.formRDefault := by
  rw [constructed_package73_strategy_eq]
  exact ConcreteStrictPackage.production_accepts_honestCoins

theorem constructed_package73_containment_is_informative :
    (BuildablePackage.Concrete.package73 hmore).strategy.Accepts
        ConcreteStrictPackage.honestCoins MemoryTable.formRDefault ∧
      ConcreteStrictPackage.honestCoins ∉
        FailureUnion (BuildablePackage.Concrete.package73 hmore).strategy
          BuildablePackage.Concrete.residual73.census MemoryTable.formRDefault ∧
      GenuineTargetAt (BuildablePackage.Concrete.package73 hmore).strategy 73 2
        ConcreteStrictPackage.honestCoins MemoryTable.formRDefault := by
  change ConcreteStrictPackage.concreteStrictPackage.strategy.Accepts
      ConcreteStrictPackage.honestCoins MemoryTable.formRDefault ∧
    ConcreteStrictPackage.honestCoins ∉
      FailureUnion ConcreteStrictPackage.concreteStrictPackage.strategy
        ConcreteStrictPackage.census MemoryTable.formRDefault ∧
    GenuineTargetAt ConcreteStrictPackage.concreteStrictPackage.strategy 73 2
      ConcreteStrictPackage.honestCoins MemoryTable.formRDefault
  exact ⟨ConcreteStrictPackage.production_accepts_honestCoins,
    ConcreteStrictPackage.honestCoins_not_failureUnion,
    ConcreteStrictPackage.honest_genuineTarget⟩

/-! ## E. -/

theorem released_aliases_unchanged :
    @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package ∧
      @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch77.released_aliases_unchanged

#print axioms Nock.NockVMROM.Thm54.HonestCommitment.bindComputeRow_render
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.renderComputeRow_eq_self
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.bindMemoryRow_render
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.renderMemoryRow_eq_self
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Data.binds
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Data.honest_specialization
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.derivedRequestIO_length_eq
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.derivedResponseIO_length_eq
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.commitmentResidualOf

#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.memory_rows_acceptedS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.memory_chainS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.derived_requestsS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.derived_responsesS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.axisPath_two
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.multiRootExecution
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.memoryProductionM

#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.dataM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.residualM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.packageM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.statementM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.statementM_of_arrays
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.residualM_distinct_from_f73

#print axioms colliding_noun_binds_original_row
#print axioms unrendered_wrong_noun_rejected
#print axioms fourteen_rows_all_vmem
#print axioms interleaved_global_chain_closes
#print axioms responses_are_genuine_nonidentity_permutation
#print axioms rootB_is_real_left_descent
#print axioms commitmentResidualOf_eta
#print axioms packageM_accepts_none
#print axioms packageM_falseAcceptance_empty
#print axioms statementM_scope
#print axioms statementM_of_every_arrays
#print axioms zero_seed_is_outside_strategy_domain
#print axioms constructed_package73_strategy_eq
#print axioms constructed_package73_accepts
#print axioms constructed_package73_containment_is_informative
#print axioms released_aliases_unchanged

#print axioms «Thm:IO_result»
#print axioms «Thm:Walk_IOP»
#print axioms «Corr:forest»
#print axioms «Thm:deterministic_Trace»
#print axioms «Lem:NPR_decomp»
#print axioms «Thm:Noun_Validation»
#print axioms «Thm:comp_38»
#print axioms «Thm:mem_38»
#print axioms «Thm:NockVMROM»
#print axioms «Lem:equiv_compute»
#print axioms «Lem:equiv_mem»
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVM.V_NockVMROM_forest

end
end Nock.RedTeam.Batch78
