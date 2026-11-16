import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.RedTeam.Batch113Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  Lean `CensusRecordPremises.census` is not the paper
NPR collision lemma (`Lem:ion_univariate_sec` / `Corr:ion_single_security`).
The paper object is a collision-probability bound for nouns that already
have length at most `Λ`.  The named extra is `CombinedSkeletonCensus`:
leaf bounds on reconstructed `skeletonPairs` (public-claim self-pairs plus
`P8Census.skeletonComparisons`) and parent-child `edgePairs`.
`nounSizeBound = E.Λ` is the already-assembled numeral.  Assembled record
equations are root/child identities.
`data.comparison_leaves` bounds a free role-matching list, not the
skeleton projection.  The missing hypothesis is `LeavesBounded Λ` on
reconstructed `skeletonComparisons`, leaf bounds on the public-claim root
nouns, and edge-pair leaf bounds.  An independent OP1 formula `[1 0]` at
`Λ = 1` has record equations, a free one-leaf role-matching list, and
fails the extra; that formula is in `skeletonPairs` and in
`skeletonComparisons`.  SizeWindow and slot predicates are not weakened.
Census extras stay five.  `Inputs` stays named.  Accounting remains
`11+1+2`.  The extra is not rounded into a paper-NPR or capstone failure.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch114

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.AxisBridge
open Nock.Framework

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## A. Lean extra ≠ paper NPR collision definition -/

/-- Paper NPR CORE: collision probability for two nouns that already have
length at most `Λ`.  This is the lemma, not the census extra. -/
theorem paper_npr_is_collision_probability (Λ : ℕ) (n₁ n₂ : Noun)
    (h₁ : n₁.leaves ≤ Λ) (h₂ : n₂.leaves ≤ Λ)
    (hne : (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁) ≠
      (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂)) :
    ((Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card : ℚ)
        / (Fintype.card K)
      ≤ ((2 * (2 * Λ - 1) : ℕ) : ℚ) / (Fintype.card K) :=
  NPR.collision_prob_le Λ n₁ n₂ h₁ h₂ hne

/-- It does not mention `fn`, collision probability,
or a table of `k` nouns -/
theorem combined_census_is_p8_and_edge_leaf_bounds
    {S : SemanticSkeleton} {Λ : ℕ}
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K S Λ) :
    (∀ pair ∈ BoundSemanticTrace.skeletonPairs K S,
      pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ) ∧
      (∀ pair ∈ EdgeComparisonCensus.edgePairs S.computeTree,
        pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ) :=
  ⟨C.p8.leaves_bounded, C.edges.leaves_bounded⟩

/-- Public-claim entries of `skeletonPairs` are self-pairs of the compute
root nouns -/
theorem skeletonPairs_public_claim_self_pairs (S : SemanticSkeleton) :
    [(S.computeTree.label.subject, S.publicClaim.subject),
      (S.computeTree.label.formula, S.publicClaim.formula),
      (S.computeTree.label.evaluation, S.publicClaim.result)] =
      [(S.computeTree.label.subject, S.computeTree.label.subject),
        (S.computeTree.label.formula, S.computeTree.label.formula),
        (S.computeTree.label.evaluation, S.computeTree.label.evaluation)] := by
  simp [SemanticSkeleton.publicClaim]

/-- Consumed extra: `CensusRecordPremises.census` is that combined leaf
bound on the reconstructed assembled skeleton -/
theorem census_extra_is_combined_on_reconstructed
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    EdgeComparisonCensus.CombinedSkeletonCensus K
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ :=
  C.census

/-- The named extra expands to reconstructed pair leaf bounds, not `True`
and not `data.comparison_leaves` -/
theorem census_is_skeleton_pair_leaf_bounds
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (∀ pair ∈ BoundSemanticTrace.skeletonPairs K
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      pair.1.leaves ≤ E.Λ ∧ pair.2.leaves ≤ E.Λ) ∧
      (∀ pair ∈ EdgeComparisonCensus.edgePairs
          (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).computeTree,
        pair.1.leaves ≤ E.Λ ∧ pair.2.leaves ≤ E.Λ) :=
  ⟨C.census.p8.leaves_bounded, C.census.edges.leaves_bounded⟩

/-! ## B. Missing identification is extra, not `True` -/

/-- Already-held numeral: `nounSizeBound` of the census assembly is `E.Λ`.
This is not a proof that reconstructed pair leaves are `≤ Λ`. -/
theorem nounSizeBound_is_assembled_numeral
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).nounSizeBound = E.Λ :=
  censusAssemblyOf_nounSizeBound E P M C

/-- `data.comparison_leaves` bounds the free role-matching list, not
`skeletonComparisons` -/
theorem comparison_leaves_quantify_data_comparisons
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) :
    (∀ c ∈ data.comparisons, c.LeavesBounded Λ) ∧
      data.comparisons.map ComparisonUse.role = requiredComparisonRoles row.1 :=
  ⟨data.comparison_leaves, data.comparison_roles⟩

/-- Record equations are root/child identities, not leaf bounds. -/
theorem recordEquations_are_root_child_identities
    (s : ComputeRowSkeleton)
    (h : ServedLookupBridge.SkeletonRecordEquations s) :
    (∀ hs0 : s.state = .s0,
      let mr := s.memoryRecord (1 : Fin 3)
        (by simp [hs0, Nock.Framework.recordCount])
      mr.root = s.subject ∧ mr.child = s.evaluation) ∧
      (∀ hs9 : s.state = .s9,
        let mr := s.memoryRecord (2 : Fin 3)
          (by simp [hs9, Nock.Framework.recordCount])
        mr.root = P8Census.skeletonSubformula s 0 .result ∧
          mr.child = P8Census.skeletonSubformula s 1 .formula) :=
  ⟨h.s0_record, h.s9_record⟩

/-- `censusAssemblyOf` still copies `census` from the named extra. -/
theorem censusAssemblyOf_still_copies_census
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).census = C.census :=
  rfl

/-- **Missing hypothesis.**  Leaf bounds on reconstructed
`skeletonComparisons`, the public-claim root nouns, and parent-child
edge pairs inhabit `CombinedSkeletonCensus`.  Free
`data.comparison_leaves`, the numeral `nounSizeBound = E.Λ`, assembled
record equations, and the paper collision lemma do not supply those
skeleton-projected bounds -/
theorem census_of_identified_skeleton_pairs
    {S : SemanticSkeleton} {Λ : ℕ}
    (hrows : ∀ s ∈ computeSkeletonRows S,
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hroot :
      S.computeTree.label.subject.leaves ≤ Λ ∧
        S.computeTree.label.formula.leaves ≤ Λ ∧
          S.computeTree.label.evaluation.leaves ≤ Λ)
    (hedges : ∀ pair ∈ EdgeComparisonCensus.edgePairs S.computeTree,
      pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ) :
    EdgeComparisonCensus.CombinedSkeletonCensus K S Λ :=
  GenericHonestData.census_of_identified_skeleton_pairs (K := K)
    hrows hroot hedges

/-! ## C. Non-vacuous OP1 witness: records and free leaves hold, extra fails -/

/-- Independent OP1 row whose formula is the two-leaf constant cell `[1 0]`.
This is a legal OP1 formula shape: head atom `1`, tail atom `0`.
Record equations hold because the row is not OP0/OP9. -/
def failRow : ComputeRowSkeleton where
  state := .s1
  subject := .atom 0
  formula := .cell (.atom 1) (.atom 0)
  evaluation := .atom 0
  decomposition := fun slot _ =>
    match slot with
    | .f_h => .atom 1
    | _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 1⟩

theorem failRow_formula_leaves :
    failRow.formula.leaves = 2 := by
  simp [failRow, Noun.leaves]

theorem failRow_recordEquations :
    ServedLookupBridge.SkeletonRecordEquations failRow where
  s0_record := by
    intro h
    cases h
  s9_record := by
    intro h
    cases h

/-- Opcode-head decomposition of this OP1 row is atom `1`. -/
theorem failRow_dec_head :
    P8Census.skeletonDec failRow .f_h = .atom 1 := by
  simp [P8Census.skeletonDec, failRow, SemanticStrategy.decActive]

/-- A free role-matching OP1 comparison list of one-leaf atoms.  This is
the `data.comparisons` shape: roles match, leaves `≤ 1`, nouns are not
the reconstructed formula cell -/
def freeComparisons : List ComparisonUse :=
  [P8Census.skeletonUse .opcodeHead (.atom 0) (.atom 1),
    P8Census.skeletonUse .formulaCons (.atom 0) (.atom 0),
    P8Census.skeletonUse .producedResult (.atom 0) (.atom 0)]

theorem freeComparisons_roles :
    freeComparisons.map ComparisonUse.role = requiredComparisonRoles .s1 := by
  simp [freeComparisons, P8Census.skeletonUse, requiredComparisonRoles]

theorem freeComparisons_leaves_le_one :
    ∀ c ∈ freeComparisons, c.LeavesBounded 1 := by
  intro c hc
  simp [freeComparisons, P8Census.skeletonUse] at hc
  obtain rfl | rfl | rfl := hc
  · simp [ComparisonUse.LeavesBounded, Noun.leaves]
  · simp [ComparisonUse.LeavesBounded, Noun.leaves]
  · simp [ComparisonUse.LeavesBounded, Noun.leaves]

/-- The free list is not the reconstructed `skeletonComparisons` list.
The formulaCons left noun is `.atom 0` on the free list and the two-leaf
`[1 0]` cell on the skeleton -/
theorem freeComparisons_ne_skeletonComparisons :
    freeComparisons ≠
      P8Census.skeletonComparisons (K := K) failRow := by
  intro h
  have hf :
      (freeComparisons[1]?.map ComparisonUse.left) =
        ((P8Census.skeletonComparisons (K := K) failRow)[1]?.map
          ComparisonUse.left) :=
    congrArg (fun cs => cs[1]?.map ComparisonUse.left) h
  simp [freeComparisons, P8Census.skeletonUse, P8Census.skeletonComparisons,
    failRow, P8Census.skeletonDec, SemanticStrategy.decActive] at hf

/-- Reconstructed formulaCons left noun is the two-leaf formula, so it is
in the extra's comparison-list quantifier -/
theorem failRow_formulaCons_left_is_formula :
    ((P8Census.skeletonComparisons (K := K) failRow)[1]?.map
      ComparisonUse.left) = some failRow.formula := by
  simp [P8Census.skeletonComparisons, failRow, P8Census.skeletonUse,
    P8Census.skeletonDec, SemanticStrategy.decActive]

def failSkeleton : SemanticSkeleton where
  computeTree := .node failRow []
  memoryForest := []

theorem failSkeleton_computeRows :
    computeSkeletonRows failSkeleton = [failRow] := by
  unfold computeSkeletonRows failSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

/-- The two-leaf formula self-pair is in `skeletonPairs` via the public
claim. -/
theorem failSkeleton_formula_pair_mem :
    (failRow.formula, failRow.formula) ∈
      BoundSemanticTrace.skeletonPairs K failSkeleton := by
  unfold BoundSemanticTrace.skeletonPairs
  refine List.mem_append.mpr (.inl ?_)
  simp [SemanticSkeleton.publicClaim, failSkeleton, failRow]

/-- A leaf compute tree emits no parent-child edge pairs. -/
theorem failSkeleton_edgePairs_empty :
    EdgeComparisonCensus.edgePairs failSkeleton.computeTree = [] := by
  unfold EdgeComparisonCensus.edgePairs failSkeleton EdgeComparisonCensus.rowEdgePairs
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil, EdgeComparisonCensus.edgeTriple, NTree.childOpt]

/-- The named extra fails at `Λ = 1`: the reconstructed formula has two
leaves -/
theorem census_fails_of_two_leaf_formula :
    ¬ EdgeComparisonCensus.CombinedSkeletonCensus K failSkeleton 1 := by
  intro h
  have hpair : (failRow.formula, failRow.formula) ∈
      BoundSemanticTrace.skeletonPairs (K := K) failSkeleton :=
    failSkeleton_formula_pair_mem (K := K)
  have hb :
      failRow.formula.leaves ≤ 1 ∧ failRow.formula.leaves ≤ 1 :=
    h.p8.leaves_bounded (pair := (failRow.formula, failRow.formula)) hpair
  have hle : failRow.formula.leaves ≤ 1 := hb.1
  rw [failRow_formula_leaves] at hle
  exact Nat.not_succ_le_self 1 hle

/-- Combined: assembled-style record equations hold, a free role-matching
comparison list is `LeavesBounded 1`, the lists are unequal, and the named
extra fails.  The skeleton-pair identification is therefore extra. -/
theorem census_does_not_follow_from_records_or_free_comparison_leaves :
    ServedLookupBridge.SkeletonRecordEquations failRow ∧
      (freeComparisons.map ComparisonUse.role = requiredComparisonRoles .s1) ∧
      (∀ c ∈ freeComparisons, c.LeavesBounded 1) ∧
      freeComparisons ≠
        P8Census.skeletonComparisons (K := K) failRow ∧
      ¬ EdgeComparisonCensus.CombinedSkeletonCensus K failSkeleton 1 :=
  ⟨failRow_recordEquations,
    freeComparisons_roles,
    freeComparisons_leaves_le_one,
    freeComparisons_ne_skeletonComparisons,
    census_fails_of_two_leaf_formula⟩

/-- The prover's named witness has the same predicate-separation, on an
OP1 two-leaf cell at `Λ = 1`.  That row is also in the extra's
`SemanticSkeleton` quantifier -/
theorem prover_witness_agrees :
    ServedLookupBridge.SkeletonRecordEquations s1CensusFailRow ∧
      (s1FreeComparisons.map ComparisonUse.role = requiredComparisonRoles .s1) ∧
      (∀ c ∈ s1FreeComparisons, c.LeavesBounded 1) ∧
      s1FreeComparisons ≠
        P8Census.skeletonComparisons (K := K) s1CensusFailRow ∧
      ¬ EdgeComparisonCensus.CombinedSkeletonCensus K s1CensusFailSkeleton 1 :=
  GenericHonestData.census_does_not_follow_from_records_or_free_comparison_leaves

/-! ## D. SizeWindow and slot predicates are not weakened; no silent inhabit -/

/-- SizeWindow extra is still `n.leaves ≤ Λ` on OP3/OP4/OP6 products, not
a rewrite of sampled `SizeWindow` -/
theorem sizeWindowBound_still_leaves_le_Lambda
    {S : SemanticSkeleton} {Λ : ℕ} :
    SizeWindowCounting.SizeWindowNounsBoundedBy S Λ =
      ∀ n ∈ SizeWindowCounting.skeletonSizeWindowNouns S, n.leaves ≤ Λ :=
  Batch112.sizeWindowBound_is_leaves_le_Lambda

/-- Sampled SizeWindow is still `leaves < orderOf z`.  Not rewritten to
`≤ Λ` -/
theorem SizeWindow_still_leaves_lt_orderOf {z : K} {n : Noun} :
    OpcodeSemantics.SizeWindow z n ↔
      1 < orderOf z ∧ n.leaves < orderOf z :=
  Batch112.SizeWindow_is_leaves_lt_orderOf

/-- OP1 required size-window list is empty -/
theorem op1_required_size_window_nouns_empty :
    SizeWindowCounting.requiredSizeWindowNouns failRow = [] := by
  simp [SizeWindowCounting.requiredSizeWindowNouns, failRow]

/-- On this OP1 skeleton the size-window list is empty, so
`SizeWindowNounsBoundedBy` holds vacuously.  That is not a general inhabit
of `sizeWindowBound` -/
theorem failSkeleton_sizeWindowBound_vacuous :
    SizeWindowCounting.SizeWindowNounsBoundedBy failSkeleton 1 := by
  intro n hn
  have hrows := failSkeleton_computeRows
  simp [SizeWindowCounting.skeletonSizeWindowNouns] at hn
  rw [hrows] at hn
  simp [SizeWindowCounting.requiredSizeWindowNouns, failRow] at hn

/-- Slot predicates remain an `Iff` with the served fields.  Not weakened. -/
theorem slot_predicates_still_iff_served (s : ComputeRowSkeleton) :
    ServedLookupBridge.SkeletonSlotSemantics s ↔
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
  Batch113.slot_predicates_still_iff_served s

/-- OP1 makes both slot implications vacuous, so `SkeletonSlotSemantics`
holds on this row. -/
theorem failRow_slotSemantics_vacuous :
    ServedLookupBridge.SkeletonSlotSemantics failRow where
  s0_slot := by
    intro h
    cases h
  s9_slot := by
    intro h
    cases h

theorem ao91_slotSemantics_still_fails_on_op0_atom :
    ¬ ServedLookupBridge.SkeletonSlotSemantics Batch113.failRow :=
  Batch113.slotSemantics_fails_on_failRow

theorem censusRecordPremises_eta_still_five
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } := by
  cases C
  rfl

theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

theorem memoryRecordPremises_eta_still_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } := by
  cases M
  rfl

theorem inputs_eta_still_named {E : BuildableNockExecution F K} (I : Inputs E) :
    I =
      { stateTagChar := I.stateTagChar
        computeWalkAlpha := I.computeWalkAlpha
        memoryWalkAlpha := I.memoryWalkAlpha
        walkGamma := I.walkGamma
        hOrb := I.hOrb
        basis := I.basis
        orbit := I.orbit
        activeDomains := I.activeDomains
        ioCoins := I.ioCoins
        ioPoleHitGood := I.ioPoleHitGood
        ioGammaGood := I.ioGammaGood
        ioLogDerivGood := I.ioLogDerivGood
        computeChallenges := I.computeChallenges
        memoryScalarChallenge := I.memoryScalarChallenge
        memoryExtensionFold := I.memoryExtensionFold
        interPoleHitGood := I.interPoleHitGood
        honestVer := I.honestVer
        ioGood10 := I.ioGood10
        interPoleHitGood10 := I.interPoleHitGood10 } := by
  cases I
  rfl

theorem dataOfCensus_still_requires_C
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    dataOfCensus E P M C hln =
      dataOfRecord E P M (censusAssemblyOf E P M C) hln :=
  rfl

theorem packageOf_still_takes_named_Inputs
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    packageOf D hgt I hprl hmore hord hordM hrows hgenF hF =
      buildFullPackageWith E I (commitmentResidualOfArrays_of_char D hgt)
        (computeChallenge_pins E I) hprl hmore hord hordM hrows hgenF hF :=
  rfl

theorem packageOf_not_forall_omega
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F) (lmb : K) :
    ¬ ∀ ω : JointCoins K, (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts ω lmb :=
  GenericHonestPackage.packageOf_not_forall_omega D hgt I hprl hmore hord hordM hrows hgenF hF (lmb := lmb)

theorem released_builder_still_takes_hzero
    {E : BuildableNockExecution F K}
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = default)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    Nonempty (OptimizedFullStrictNockVMROMPackage F K I.hOrb) :=
  ⟨buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF⟩

theorem any_universal_data_still_forces_q_pin
    (g : ∀ E : BuildableNockExecution F K, Data E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  GenericHonestPackage.generic_data_would_force_q_equality (F := F) (K := K) g

/-- NMR address space remains the Nat-cast memory-table axis. -/
theorem nmr_axis_is_not_census_leaf_bound
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  M.axisNat

variable [Fintype F] [DecidableEq F]

/-! ## E. -/

inductive ReviewedField114
  | structural
  | optimized_chips
  | shared_io
  | perfect_completeness
  | containment
  | walk_bounds
  | p8_fixed_field_soundness
  | p8_fixed_field_bits
  | acceptance_to_target
  | complete_false_acceptance_bound
  | complete_false_acceptance_bits
  | exact_resources
  | row_budgets
  | shared_forest_axis
deriving DecidableEq

def substantiveFields114 : List ReviewedField114 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields114 : List ReviewedField114 := [.structural]

def residualFields114 : List ReviewedField114 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Leaving `census` named is not a statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields114.length = 11 ∧
      typeSummaryFields114.length = 1 ∧
      residualFields114 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields114.length = 2 ∧
      (substantiveFields114 ++ typeSummaryFields114 ++ residualFields114).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  ⟨optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth, rfl⟩

theorem containment_is_implication_not_forall_omega
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    ∀ (ω : JointCoins K) (lmb : K),
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts ω lmb →
        ω ∉ FailureUnion (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
          (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.census lmb →
        GenuineTargetAt (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
          (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).q
          (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.Λ ω lmb :=
  (statementOf D hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth).containment

#print axioms paper_npr_is_collision_probability
#print axioms combined_census_is_p8_and_edge_leaf_bounds
#print axioms skeletonPairs_public_claim_self_pairs
#print axioms census_extra_is_combined_on_reconstructed
#print axioms census_is_skeleton_pair_leaf_bounds
#print axioms nounSizeBound_is_assembled_numeral
#print axioms comparison_leaves_quantify_data_comparisons
#print axioms recordEquations_are_root_child_identities
#print axioms censusAssemblyOf_still_copies_census
#print axioms census_of_identified_skeleton_pairs
#print axioms failRow_formula_leaves
#print axioms failRow_recordEquations
#print axioms failRow_dec_head
#print axioms freeComparisons_roles
#print axioms freeComparisons_leaves_le_one
#print axioms freeComparisons_ne_skeletonComparisons
#print axioms failRow_formulaCons_left_is_formula
#print axioms failSkeleton_computeRows
#print axioms failSkeleton_formula_pair_mem
#print axioms failSkeleton_edgePairs_empty
#print axioms census_fails_of_two_leaf_formula
#print axioms census_does_not_follow_from_records_or_free_comparison_leaves
#print axioms prover_witness_agrees
#print axioms sizeWindowBound_still_leaves_le_Lambda
#print axioms SizeWindow_still_leaves_lt_orderOf
#print axioms op1_required_size_window_nouns_empty
#print axioms failSkeleton_sizeWindowBound_vacuous
#print axioms slot_predicates_still_iff_served
#print axioms failRow_slotSemantics_vacuous
#print axioms ao91_slotSemantics_still_fails_on_op0_atom
#print axioms censusRecordPremises_eta_still_five
#print axioms residualPremises_eta_still_four
#print axioms memoryRecordPremises_eta_still_two
#print axioms inputs_eta_still_named
#print axioms dataOfCensus_still_requires_C
#print axioms packageOf_still_takes_named_Inputs
#print axioms packageOf_not_forall_omega
#print axioms released_builder_still_takes_hzero
#print axioms any_universal_data_still_forces_q_pin
#print axioms nmr_axis_is_not_census_leaf_bound
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms containment_is_implication_not_forall_omega
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.census_is_skeleton_pair_leaf_bounds
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestData.census_does_not_follow_from_records_or_free_comparison_leaves
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch114
