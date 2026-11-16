import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.RedTeam.Batch103Thm54CensusExtras
import Nock.RedTeam.Batch115Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  Lean `CensusRecordPremises.combinedBounded` is
`CombinedBoundedBy K E.q` on the assembled skeleton: every pair in
`combinedSkeletonPairs` has both sides `FieldEmbedding.BoundedBy q`.  Those pairs include synthesized rights that row
`skeletonBounded` does not list.
`MemRecSkeleton.BoundedBy` is root/child nouns, not the axis Nat.

On the assembled object, named `skeletonBounded` plus already-held
`11 < ringChar` and `q_eq_ringChar` inhabit the extra:
`combinedBounded_of_skeletonBounded_at_consumed_q` /
`dataOfCensusAtConsumed` / `packageOf`.  The inhabit is not a copy of
`C.combinedBounded` on that constructor: the honest constructor does not
take the field as an input.

Remaining honest
census extras are `slotSemantics`, `census`, `sizeWindowBound`,
`skeletonBounded`.  `Inputs` stays named.  Accounting remains `11+1+2`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch116

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

/-! ## A. Extra is pair-wise atom-range; synthesized rights are not row nouns -/

/-- Paper atom range: every leaf of a noun is a field element of
Goldilocks `F_p`.  Lean names the numeric side-condition `BoundedBy q`. -/
theorem boundedBy_is_atom_lt_q (q : ℕ) :
    (∀ n : ℕ, FieldEmbedding.BoundedBy q (.atom n) ↔ n < q) ∧
      (∀ l r : Noun,
        FieldEmbedding.BoundedBy q (.cell l r) ↔
          FieldEmbedding.BoundedBy q l ∧ FieldEmbedding.BoundedBy q r) :=
  ⟨fun _ => FieldEmbedding.BoundedBy_atom,
    fun _ _ => FieldEmbedding.BoundedBy_cell⟩

/-- The named extra expands to pair-wise `BoundedBy q` on census/edge pairs. -/
theorem combinedBounded_is_pair_atom_range
    {q : ℕ} {S : SemanticSkeleton}
    (h : CombinedBoundedBy K q S) :
    ∀ pair ∈ EdgeComparisonCensus.combinedSkeletonPairs K S,
      FieldEmbedding.BoundedBy q pair.1 ∧
        FieldEmbedding.BoundedBy q pair.2 :=
  h

/-- Combined pairs are public-claim self-pairs, `skeletonComparisons`, and
parent-child `edgePairs` -/
theorem combinedSkeletonPairs_are_public_comparisons_and_edges
    (S : SemanticSkeleton) :
    EdgeComparisonCensus.combinedSkeletonPairs K S =
      BoundSemanticTrace.skeletonPairs K S ++
        EdgeComparisonCensus.edgePairs S.computeTree :=
  rfl

/-- Memory-record `BoundedBy` is root/child nouns.  The axis Nat is not a
conjunct -/
theorem memRecBounded_is_root_and_child_not_axis
    {q : ℕ} (s : MemRecSkeleton) :
    s.BoundedBy q ↔
      FieldEmbedding.BoundedBy q s.root ∧ FieldEmbedding.BoundedBy q s.child :=
  Iff.rfl

/-- Axis `12` is compatible with record `BoundedBy 12` -/
theorem memRec_axis_twelve_bounded_by_twelve :
    MemRecSkeleton.BoundedBy 12 ⟨.atom 0, .atom 0, 12⟩ := by
  simp [MemRecSkeleton.BoundedBy]

/-- OP0 comparisons include the synthesized opcode atom `0` and the `mr2`
axis atom -/
theorem s0_comparisons_include_opcode_and_axis
    (s : ComputeRowSkeleton) (h : s.state = .s0) :
    P8Census.skeletonUse .opcodeHead (P8Census.skeletonDec s .f_h) (.atom 0) ∈
      P8Census.skeletonComparisons (K := K) s ∧
    P8Census.skeletonUse .recursiveFormula (P8Census.skeletonDec s .f_t)
        (.atom (P8Census.skeletonMemoryAxis s 1)) ∈
      P8Census.skeletonComparisons (K := K) s := by
  simp [P8Census.skeletonComparisons, P8Census.skeletonUse, h]

/-- OP9 comparisons include the synthesized `mr3` axis atom. -/
theorem s9_comparisons_include_axis_atom
    (s : ComputeRowSkeleton) (h : s.state = .s9) :
    P8Census.skeletonUse .axisAtom (P8Census.skeletonDec s .f_th)
        (.atom (P8Census.skeletonMemoryAxis s 2)) ∈
      P8Census.skeletonComparisons (K := K) s := by
  simp [P8Census.skeletonComparisons, P8Census.skeletonUse, h]

/-- OP4 comparisons include the modular `incMod` target at `ringChar`. -/
theorem s4_comparisons_include_incMod
    (s : ComputeRowSkeleton) (h : s.state = .s4) :
    P8Census.skeletonUse .producedResult s.evaluation
        (OpcodeSemantics.incMod (ringChar K)
          (P8Census.skeletonSubformula s 0 .result)) ∈
      P8Census.skeletonComparisons (K := K) s := by
  simp [P8Census.skeletonComparisons, P8Census.skeletonUse, h]

/-- Opcode atoms `0..9` are in range at the consumed bound `11 < q`. -/
theorem opcode_atom_bounded_of_eleven_lt {q n : ℕ} (hq : 11 < q)
    (hn : n ≤ 9) : FieldEmbedding.BoundedBy q (.atom n) := by
  simp only [FieldEmbedding.BoundedBy_atom]
  omega

/-! ## B. Assembled-path inhabit is real; it does not copy `C.combinedBounded` -/

/-- Assembled OP0 formula tail is `decompNoun.f_t` -/
theorem decompNoun_f_t_is_root_tail
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) :
    decompNoun data .f_t = data.root.tail :=
  rfl

/-- Assembled OP0 `mr2` axis is `atomVal` of that tail. -/
theorem assembled_s0_axis_is_atomVal_tail {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (h : row.1 = .s0) :
    P8Census.skeletonMemoryAxis (computeSkeletonOf data pubR) 1 =
      atomVal data.root.tail :=
  computeSkeletonOf_s0_memoryAxis data pubR h

/-- Assembled OP9 `mr3` axis is `atomVal` of `decompNoun.f_th`. -/
theorem assembled_s9_axis_is_atomVal_f_th {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (h : row.1 = .s9) :
    P8Census.skeletonMemoryAxis (computeSkeletonOf data pubR) 2 =
      atomVal (decompNoun data .f_th) :=
  computeSkeletonOf_s9_memoryAxis data pubR h

/-- **Inhabit on the assembled skeleton.**  Named `skeletonBounded` plus
already-held `11 < ringChar` and `P.q_eq_ringChar` close `CombinedBoundedBy`
on `skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)`. -/
theorem assembled_combinedBounded_from_named_skeletonBounded
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (hs : (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q)
    (hgt : 11 < ringChar K) :
    CombinedBoundedBy K E.q
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) :=
  GenericHonestData.combinedBounded_of_skeletonBounded_at_consumed_q E P M hs hgt

/-- The honest constructor fills `combinedBounded`; it does not take that
field as an input -/
theorem censusRecordPremises_of_skeletonBounded_fills_combined
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (slotSemantics :
      ∀ s ∈ computeSkeletonRows
          (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
        ServedLookupBridge.SkeletonSlotSemantics s)
    (census :
      EdgeComparisonCensus.CombinedSkeletonCensus K
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ)
    (sizeWindowBound :
      SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ)
    (skeletonBounded :
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q)
    (hgt : 11 < ringChar K) :
    (censusRecordPremises_of_skeletonBounded E P M slotSemantics census
        sizeWindowBound skeletonBounded hgt).combinedBounded =
      GenericHonestData.combinedBounded_of_skeletonBounded_at_consumed_q E P M
        skeletonBounded hgt :=
  rfl

/-- `dataOfCensusAtConsumed` is assembled `Data` whose `combinedBounded` is
that inhabit, not a copy of a caller-supplied extra. -/
theorem dataOfCensusAtConsumed_combinedBounded_is_inhabit
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (slotSemantics :
      ∀ s ∈ computeSkeletonRows
          (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
        ServedLookupBridge.SkeletonSlotSemantics s)
    (census :
      EdgeComparisonCensus.CombinedSkeletonCensus K
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ)
    (sizeWindowBound :
      SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ)
    (skeletonBounded :
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q)
    (hgt : 11 < ringChar K)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOfCensusAtConsumed E P M slotSemantics census sizeWindowBound
        skeletonBounded hgt hln).combinedBounded =
      GenericHonestData.combinedBounded_of_skeletonBounded_at_consumed_q E P M
        skeletonBounded hgt :=
  rfl

/-- Remaining honest extras are still named inputs of that constructor. -/
theorem dataOfCensusAtConsumed_still_names_remaining_extras
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (slotSemantics :
      ∀ s ∈ computeSkeletonRows
          (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
        ServedLookupBridge.SkeletonSlotSemantics s)
    (census :
      EdgeComparisonCensus.CombinedSkeletonCensus K
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ)
    (sizeWindowBound :
      SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ)
    (skeletonBounded :
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q)
    (hgt : 11 < ringChar K)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    let D := dataOfCensusAtConsumed E P M slotSemantics census
      sizeWindowBound skeletonBounded hgt hln
    D.slotSemantics = slotSemantics ∧
      D.census = census ∧
      D.sizeWindowBound = sizeWindowBound ∧
      D.skeletonBounded = skeletonBounded :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `packageOf` consumes that assembled `Data` at already-held `11 < ringChar`
together with named `Inputs` -/
theorem packageOf_consumes_dataOfCensusAtConsumed
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (slotSemantics :
      ∀ s ∈ computeSkeletonRows
          (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
        ServedLookupBridge.SkeletonSlotSemantics s)
    (census :
      EdgeComparisonCensus.CombinedSkeletonCensus K
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ)
    (sizeWindowBound :
      SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ)
    (skeletonBounded :
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q)
    (hgt : 11 < ringChar K)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K
      (dataOfCensusAtConsumed E P M slotSemantics census sizeWindowBound skeletonBounded hgt
        hln).skeleton.publicClaim
      (dataOfCensusAtConsumed E P M slotSemantics census sizeWindowBound skeletonBounded hgt hln).Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    packageOf (dataOfCensusAtConsumed E P M slotSemantics census
        sizeWindowBound skeletonBounded hgt hln) hgt I hprl hmore hord hordM hrows hgenF hF =
      buildFullPackageWith E I
        (commitmentResidualOfArrays_of_char
          (dataOfCensusAtConsumed E P M slotSemantics census
            sizeWindowBound skeletonBounded hgt hln) hgt)
        (computeChallenge_pins E I) hprl hmore hord hordM hrows hgenF hF :=
  rfl

/-- The five-field copy path is unchanged: `censusAssemblyOf` still copies
`combinedBounded` from `C` -/
theorem censusAssemblyOf_still_copies_combinedBounded
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).combinedBounded = C.combinedBounded :=
  rfl

/-- `q_eq_ringChar` remains a named `ResidualPremises` field; the inhabit
uses it as already-held -/
theorem q_eq_ringChar_still_named
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    E.q = ringChar K :=
  P.q_eq_ringChar

theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } :=
  Batch115.residualPremises_eta_still_four P

/-- `11 < ringChar` remains the consumed `packageOf` hypothesis, not a
deleted extra -/
theorem packageOf_still_takes_eleven_lt_ringChar
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

/-! ## C. Not a restatement: independent OP0 `q = 12` witness -/

/-- Independent OP0 row: reconstructed nouns are `.atom 0` or `[0 0]`,
`mr2` axis is `12` -/
def axisFailRow : ComputeRowSkeleton where
  state := .s0
  subject := .atom 0
  formula := .cell (.atom 0) (.atom 0)
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun i _ =>
    if (i : ℕ) = 1 then ⟨.atom 0, .atom 0, 12⟩ else ⟨.atom 0, .atom 0, 1⟩

def axisFailSkeleton : SemanticSkeleton where
  computeTree := .node axisFailRow []
  memoryForest := []

theorem axisFailSkeleton_computeRows :
    computeSkeletonRows axisFailSkeleton = [axisFailRow] := by
  unfold computeSkeletonRows axisFailSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

theorem axisFailRow_bounded_by_twelve :
    axisFailRow.BoundedBy 12 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [axisFailRow]
  · simp [axisFailRow]
  · simp [axisFailRow]
  · intro slot hact
    simp [axisFailRow]
  · intro i h slot
    simp [axisFailRow]
  · intro i h
    simp [axisFailRow, MemRecSkeleton.BoundedBy]
    split_ifs <;> simp

theorem axisFailSkeleton_bounded_by_twelve :
    axisFailSkeleton.BoundedBy 12 where
  computeRows := by
    rw [List.forall_iff_forall_mem]
    intro s hs
    rw [axisFailSkeleton_computeRows] at hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact axisFailRow_bounded_by_twelve
  memoryRows := by
    rw [List.forall_iff_forall_mem]
    intro s hs
    unfold memorySkeletonRows axisFailSkeleton at hs
    simp [bfsForest_nil] at hs
  memoryTrees := by
    intro tree ht
    simp [axisFailSkeleton] at ht

theorem axisFailRow_memoryAxis :
    P8Census.skeletonMemoryAxis axisFailRow 1 = 12 := by
  simp [P8Census.skeletonMemoryAxis, axisFailRow, Nock.Framework.recordCount]

theorem eleven_lt_twelve : 11 < 12 := by decide

theorem twelve_is_not_f97_or_goldilocks :
    12 ≠ 97 ∧ 12 ≠ (2 ^ 64 - 2 ^ 32 + 1) := by
  decide

/-- The extra's OP0 recursive-formula pair is `(.atom 0,.atom 12)`. -/
theorem axisFailRow_axis_pair_mem :
    (Noun.atom 0, Noun.atom 12) ∈
      BoundSemanticTrace.skeletonPairs K axisFailSkeleton := by
  unfold BoundSemanticTrace.skeletonPairs
  refine List.mem_append.mpr (.inr ?_)
  refine List.mem_map.mpr
    ⟨P8Census.skeletonUse .recursiveFormula (.atom 0) (.atom 12), ?_, rfl⟩
  simp [P8Census.skeletonComparisonCensus, axisFailSkeleton_computeRows,
    P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
    P8Census.skeletonMemoryAxis, axisFailRow, SemanticStrategy.decActive,
    Nock.Framework.recordCount]

/-- Predicates are distinct at consumed-compatible `q = 12`: row
`BoundedBy 12` holds and `CombinedBoundedBy` fails on axis atom `12`.
This is not an assembled `Data` counterexample, not `q = 1`, and not a
Goldilocks/F97 bump -/
theorem combinedBounded_not_restatement_at_q_twelve :
    11 < 12 ∧
      12 ≠ 97 ∧
      12 ≠ (2 ^ 64 - 2 ^ 32 + 1) ∧
      axisFailSkeleton.BoundedBy 12 ∧
      ¬ CombinedBoundedBy K 12 axisFailSkeleton := by
  refine ⟨eleven_lt_twelve, twelve_is_not_f97_or_goldilocks.1,
    twelve_is_not_f97_or_goldilocks.2, axisFailSkeleton_bounded_by_twelve, ?_⟩
  intro h
  have hpair : (Noun.atom 0, Noun.atom 12) ∈
      EdgeComparisonCensus.combinedSkeletonPairs K axisFailSkeleton := by
    unfold EdgeComparisonCensus.combinedSkeletonPairs
    exact List.mem_append.mpr (.inl (axisFailRow_axis_pair_mem (K := K)))
  have hb := h _ hpair
  simp [FieldEmbedding.BoundedBy] at hb

/-- The two extras are not definitionally the same predicate. -/
theorem extras_not_definitionally_the_same :
    ¬ ∀ (S : SemanticSkeleton) (q : ℕ),
      S.BoundedBy q ↔ CombinedBoundedBy K q S := by
  intro h
  have hiff := h axisFailSkeleton 12
  exact (combinedBounded_not_restatement_at_q_twelve (K := K)).2.2.2.2
    (hiff.mp (combinedBounded_not_restatement_at_q_twelve (K := K)).2.2.2.1)

/-- The prover's named witness has the same predicate-separation. -/
theorem prover_witness_agrees :
    11 < 12 ∧
      GenericHonestData.s0AxisFailSkeleton.BoundedBy 12 ∧
      ¬ CombinedBoundedBy K 12 GenericHonestData.s0AxisFailSkeleton :=
  GenericHonestData.combinedBounded_not_restatement_at_consumed_q

theorem batch115_q_one_separator_is_not_this_item :
    Batch115.zeroSkeleton.BoundedBy 1 ∧
      ¬ CombinedBoundedBy K 1 Batch115.zeroSkeleton ∧
      ¬ 11 < 1 :=
  ⟨(Batch115.combinedBounded_not_restatement_of_skeletonBounded (K := K)).1,
    (Batch115.combinedBounded_not_restatement_of_skeletonBounded (K := K)).2,
    by decide⟩

/-! ## 115 still compile -/

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

theorem batch115_five_field_eta_still_compiles
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } :=
  Batch115.censusRecordPremises_eta_still_five C

theorem batch103_five_projection_still_compiles
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    let D := dataOfCensus E P M C hln
    (∀ s ∈ computeSkeletonRows D.skeleton,
        ServedLookupBridge.SkeletonSlotSemantics s) ∧
      EdgeComparisonCensus.CombinedSkeletonCensus K D.skeleton D.Λ ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy D.skeleton D.Λ ∧
      D.skeleton.BoundedBy E.q ∧
      CombinedBoundedBy K E.q D.skeleton :=
  Batch103.dataOfCensus_still_requires_and_projects_five_extras E P M C hln

theorem memoryRecordPremises_eta_still_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } :=
  Batch115.memoryRecordPremises_eta_still_two M

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
        interPoleHitGood10 := I.interPoleHitGood10 } :=
  Batch115.inputs_eta_still_named I

/-! ## E. No silent inhabit of another extra; no weakening -/

theorem sizeWindowBound_still_leaves_le_Lambda
    {S : SemanticSkeleton} {Λ : ℕ} :
    SizeWindowCounting.SizeWindowNounsBoundedBy S Λ =
      ∀ n ∈ SizeWindowCounting.skeletonSizeWindowNouns S, n.leaves ≤ Λ :=
  Batch115.sizeWindowBound_still_leaves_le_Lambda

theorem SizeWindow_still_leaves_lt_orderOf {z : K} {n : Noun} :
    OpcodeSemantics.SizeWindow z n ↔
      1 < orderOf z ∧ n.leaves < orderOf z :=
  Batch115.SizeWindow_still_leaves_lt_orderOf

theorem skeletonBounded_still_named_on_C
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q :=
  C.skeletonBounded

theorem dataOfCensus_still_requires_C
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    dataOfCensus E P M C hln =
      dataOfRecord E P M (censusAssemblyOf E P M C) hln :=
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
theorem nmr_axis_is_not_combined_pair_range
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  M.axisNat

/-- Slot predicates remain an `Iff`.  Not weakened -/
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
  Batch115.slot_predicates_still_iff_served s

variable [Fintype F] [DecidableEq F]

/-- Consumed capstone still consumes assembled `Data` from the honest
constructor -/
theorem statementOf_consumes_dataOfCensusAtConsumed
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (slotSemantics :
      ∀ s ∈ computeSkeletonRows
          (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
        ServedLookupBridge.SkeletonSlotSemantics s)
    (census :
      EdgeComparisonCensus.CombinedSkeletonCensus K
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ)
    (sizeWindowBound :
      SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ)
    (skeletonBounded :
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q)
    (hgt : 11 < ringChar K)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K
      (dataOfCensusAtConsumed E P M slotSemantics census sizeWindowBound skeletonBounded hgt
        hln).skeleton.publicClaim
      (dataOfCensusAtConsumed E P M slotSemantics census sizeWindowBound skeletonBounded hgt hln).Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound
      (packageOf (dataOfCensusAtConsumed E P M slotSemantics census
        sizeWindowBound skeletonBounded hgt hln) hgt I hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (packageOf (dataOfCensusAtConsumed E P M slotSemantics census
        sizeWindowBound skeletonBounded hgt hln) hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis
      (packageOf (dataOfCensusAtConsumed E P M slotSemantics census
        sizeWindowBound skeletonBounded hgt hln) hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement
      (packageOf (dataOfCensusAtConsumed E P M slotSemantics census
        sizeWindowBound skeletonBounded hgt hln) hgt I hprl hmore hord hordM hrows hgenF hF) :=
  statementOf (dataOfCensusAtConsumed E P M slotSemantics census
    sizeWindowBound skeletonBounded hgt hln) hgt I hprl hmore hord hordM hrows hgenF hF hax hbasis hwidth

/-! ## F. -/

inductive ReviewedField116
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

def substantiveFields116 : List ReviewedField116 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields116 : List ReviewedField116 := [.structural]

def residualFields116 : List ReviewedField116 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Filling `combinedBounded` on the honest constructor is not a
statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields116.length = 11 ∧
      typeSummaryFields116.length = 1 ∧
      residualFields116 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields116.length = 2 ∧
      (substantiveFields116 ++ typeSummaryFields116 ++ residualFields116).Nodup ∧
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

#print axioms boundedBy_is_atom_lt_q
#print axioms combinedBounded_is_pair_atom_range
#print axioms combinedSkeletonPairs_are_public_comparisons_and_edges
#print axioms memRecBounded_is_root_and_child_not_axis
#print axioms memRec_axis_twelve_bounded_by_twelve
#print axioms s0_comparisons_include_opcode_and_axis
#print axioms s9_comparisons_include_axis_atom
#print axioms s4_comparisons_include_incMod
#print axioms opcode_atom_bounded_of_eleven_lt
#print axioms decompNoun_f_t_is_root_tail
#print axioms assembled_s0_axis_is_atomVal_tail
#print axioms assembled_s9_axis_is_atomVal_f_th
#print axioms assembled_combinedBounded_from_named_skeletonBounded
#print axioms censusRecordPremises_of_skeletonBounded_fills_combined
#print axioms dataOfCensusAtConsumed_combinedBounded_is_inhabit
#print axioms dataOfCensusAtConsumed_still_names_remaining_extras
#print axioms packageOf_consumes_dataOfCensusAtConsumed
#print axioms censusAssemblyOf_still_copies_combinedBounded
#print axioms q_eq_ringChar_still_named
#print axioms residualPremises_eta_still_four
#print axioms packageOf_still_takes_eleven_lt_ringChar
#print axioms axisFailSkeleton_computeRows
#print axioms axisFailRow_bounded_by_twelve
#print axioms axisFailSkeleton_bounded_by_twelve
#print axioms axisFailRow_memoryAxis
#print axioms eleven_lt_twelve
#print axioms twelve_is_not_f97_or_goldilocks
#print axioms axisFailRow_axis_pair_mem
#print axioms combinedBounded_not_restatement_at_q_twelve
#print axioms extras_not_definitionally_the_same
#print axioms prover_witness_agrees
#print axioms batch115_q_one_separator_is_not_this_item
#print axioms censusRecordPremises_eta_still_five
#print axioms batch115_five_field_eta_still_compiles
#print axioms batch103_five_projection_still_compiles
#print axioms memoryRecordPremises_eta_still_two
#print axioms inputs_eta_still_named
#print axioms sizeWindowBound_still_leaves_le_Lambda
#print axioms SizeWindow_still_leaves_lt_orderOf
#print axioms skeletonBounded_still_named_on_C
#print axioms dataOfCensus_still_requires_C
#print axioms packageOf_not_forall_omega
#print axioms released_builder_still_takes_hzero
#print axioms any_universal_data_still_forces_q_pin
#print axioms nmr_axis_is_not_combined_pair_range
#print axioms slot_predicates_still_iff_served
#print axioms statementOf_consumes_dataOfCensusAtConsumed
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms containment_is_implication_not_forall_omega
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestData.combinedBounded_of_skeletonBounded_at_consumed_q
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestData.dataOfCensusAtConsumed
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch116
