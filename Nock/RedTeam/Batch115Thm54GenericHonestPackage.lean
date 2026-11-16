import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.RedTeam.Batch114Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  Lean `CensusRecordPremises.skeletonBounded` is
`SemanticSkeleton.BoundedBy E.q`: every atom of every reconstructed
compute-row noun, including active `decompNoun`, has value `< q`.  That is not `leaves ≤ Λ`.  Memory-row/tree
bounds, the compute root triple, and subformula nouns are already held.
Active `decompNoun` remains `Realizes`-only (`fp = enc z n`).  `Data`
does not force those atoms into `realizedNouns`.  An independent OP1
row with formula `[0 0]` and decomposition `.atom 2` has
`CombinedSkeletonCensus` at `Λ = 2` and vacuous size-window, while
`BoundedBy 2` fails: `.atom 2` has one leaf and is not `BoundedBy 2`.
The extra's quantifier sees that slot: `decActive.s1.f_h = true`.
`census` / `sizeWindowBound` are not restated.  `combinedBounded` stays
named and is pair-wise atom-range on census pairs, not row
`BoundedBy`; a `q = 1` all-atom-`0` OP1 row inhabits `BoundedBy 1` and
fails `CombinedBoundedBy` on opcode atom `1`.  Census extras stay five.
`Inputs` stays named.  Accounting remains `11+1+2`.  The extra is not rounded
into a paper field-bound or capstone failure.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch115

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

/-! ## A. Lean extra is atom-range, not leaf-count -/

/-- Paper atom range: every leaf of a noun is a field element of
Goldilocks `F_p`.  Lean names the numeric side-condition `BoundedBy q`. -/
theorem boundedBy_is_atom_lt_q (q : ℕ) :
    (∀ n : ℕ, FieldEmbedding.BoundedBy q (.atom n) ↔ n < q) ∧
      (∀ l r : Noun,
        FieldEmbedding.BoundedBy q (.cell l r) ↔
          FieldEmbedding.BoundedBy q l ∧ FieldEmbedding.BoundedBy q r) :=
  ⟨fun _ => FieldEmbedding.BoundedBy_atom,
    fun _ _ => FieldEmbedding.BoundedBy_cell⟩

/-- Compute-row `BoundedBy q` includes every active decomposition slot. -/
theorem computeRowBounded_includes_decomposition
    {q : ℕ} {s : ComputeRowSkeleton} (h : s.BoundedBy q) :
    (∀ slot hact, FieldEmbedding.BoundedBy q (s.decomposition slot hact)) :=
  h.2.2.2.1

/-- Consumed extra: reconstructed skeleton `BoundedBy E.q`, including
compute-row decomposition nouns -/
theorem skeletonBounded_extra_is_q_atom_range
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    (computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M))).Forall
      (ComputeRowSkeleton.BoundedBy E.q) ∧
      (memorySkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M))).Forall
      (MemoryRowSkeleton.BoundedBy E.q) ∧
      (∀ tree ∈ (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).memoryForest,
        ∀ node, InTree tree node → node.label.BoundedBy E.q) :=
  ⟨C.skeletonBounded.computeRows, C.skeletonBounded.memoryRows,
    C.skeletonBounded.memoryTrees⟩

/-- Assembled decomposition slots are `decompNoun`, not a leaf count. -/
theorem computeSkeletonOf_decomp_is_decompNoun
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (slot : DecSlot)
    (hact : SemanticStrategy.decActive row.1 slot = true) :
    (computeSkeletonOf data pubR).decomposition slot
        (by simpa [computeSkeletonOf] using hact) =
      decompNoun data slot :=
  rfl

/-- One leaf does not imply atom value `< q` -/
theorem atom_two_one_leaf_not_bounded_by_two :
    (Noun.atom 2).leaves = 1 ∧ ¬ FieldEmbedding.BoundedBy 2 (Noun.atom 2) := by
  constructor
  · rfl
  · simp

/-! ## B. Missing `decompNoun` bounds are not `True`; `Data` does not carry them -/

/-- `Realizes` is fingerprint equality, not `BoundedBy q`. -/
theorem realizes_is_enc_eq {z : K} {fp : ComputeTable.FP K} {n : Noun} :
    OpcodeSemantics.Realizes z fp n ↔
      fp = GlobalCarryRecognizer.enc z n :=
  Iff.rfl

/-- Active `decompNoun` is `Realizes`-only -/
theorem decompNoun_active_is_realizes
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) (slot : DecSlot)
    (hact : SemanticStrategy.decActive row.1 slot = true) :
    OpcodeSemantics.Realizes row.2.1.z (SemanticStrategy.decFP row.2.2.2 slot)
      (decompNoun data slot) :=
  decompNoun_realizes_active data slot hact

/-- `realizedNouns` is forced only for the root triple, not `decompNoun`. -/
theorem realizedNouns_cover_root_triple
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) :
    data.root.subject ∈ data.realizedNouns ∧
      data.root.formula ∈ data.realizedNouns ∧
        data.root.result ∈ data.realizedNouns :=
  ⟨data.subject_mem, data.formula_mem, data.result_mem⟩

/-- Already-held root triple of `computeSkeletonOf` is `BoundedBy q`.
This is not a decomposition bound -/
theorem computeSkeletonOf_root_bounded_is_triple
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row)) :
    FieldEmbedding.BoundedBy q (computeSkeletonOf data pubR).subject ∧
      FieldEmbedding.BoundedBy q (computeSkeletonOf data pubR).formula ∧
        FieldEmbedding.BoundedBy q (computeSkeletonOf data pubR).evaluation :=
  computeSkeletonOf_root_bounded data pubR

/-- Opcode-head decomposition is `data.root.head`, not a `realizedNouns`
member theorem -/
theorem decompNoun_f_h_is_root_head
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) :
    decompNoun data .f_h = data.root.head :=
  rfl

/-- OP1 head and tail slots are active on every state, including `.s1`. -/
theorem op1_head_and_tail_active :
    SemanticStrategy.decActive .s1 .f_h = true ∧
      SemanticStrategy.decActive .s1 .f_t = true :=
  ⟨(SemanticStrategy.decActive_cases .s1).1,
    (SemanticStrategy.decActive_cases .s1).2.1⟩

/-- `censusAssemblyOf` still copies `skeletonBounded` from the named extra. -/
theorem censusAssemblyOf_still_copies_skeletonBounded
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).skeletonBounded = C.skeletonBounded :=
  rfl

/-- **Missing hypothesis.**  Atom-range on reconstructed `decompNoun`
slots, plus already-held root/subformula/memory bounds, inhabit the extra.
`census` leaf bounds and `sizeWindowBound` do not supply those atom values. -/
theorem skeletonBounded_of_decomp_bounds_independent
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (hdecomp :
      ∀ s ∈ computeSkeletonRows
          (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
        ∀ (slot : DecSlot)
          (hact : SemanticStrategy.decActive s.state slot = true),
          FieldEmbedding.BoundedBy E.q (s.decomposition slot hact)) :
    (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q :=
  GenericHonestData.skeletonBounded_of_decomp_bounds E P M hdecomp

/-! ## C. Non-vacuous OP1 witness: census/size-window hold, extra fails -/

/-- Independent OP1 row whose formula is the two-leaf cell `[0 0]` and
whose active decomposition slots are `.atom 2`. -/
def failRow : ComputeRowSkeleton where
  state := .s1
  subject := .atom 0
  formula := .cell (.atom 0) (.atom 0)
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 2
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 1⟩

theorem failRow_formula_is_zero_zero :
    failRow.formula = .cell (.atom 0) (.atom 0) :=
  rfl

theorem failRow_formula_leaves :
    failRow.formula.leaves = 2 := by
  simp [failRow, Noun.leaves]

theorem failRow_formula_bounded_by_two :
    FieldEmbedding.BoundedBy 2 failRow.formula := by
  simp [failRow]

theorem failRow_decomp_head_is_atom_two :
    failRow.decomposition .f_h (by simp [SemanticStrategy.decActive]) =
      .atom 2 := by
  simp [failRow]

theorem failRow_recordEquations :
    ServedLookupBridge.SkeletonRecordEquations failRow where
  s0_record := by
    intro h
    cases h
  s9_record := by
    intro h
    cases h

theorem failRow_root_subformula_memory_bounded :
    FieldEmbedding.BoundedBy 2 failRow.subject ∧
      FieldEmbedding.BoundedBy 2 failRow.formula ∧
        FieldEmbedding.BoundedBy 2 failRow.evaluation ∧
          (∀ i h slot, FieldEmbedding.BoundedBy 2 (failRow.subformula i h slot)) ∧
            (∀ i h, (failRow.memoryRecord i h).BoundedBy 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [failRow]
  · simp [failRow]
  · simp [failRow]
  · intro i h slot
    simp [failRow]
  · intro i h
    simp [failRow, MemRecSkeleton.BoundedBy]

def failSkeleton : SemanticSkeleton where
  computeTree := .node failRow []
  memoryForest := []

theorem failSkeleton_computeRows :
    computeSkeletonRows failSkeleton = [failRow] := by
  unfold computeSkeletonRows failSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

/-- The extra's compute-row quantifier contains this OP1 row. -/
theorem failRow_mem_computeRows :
    failRow ∈ computeSkeletonRows failSkeleton := by
  simp [failSkeleton_computeRows]

/-- Opcode-head decomposition of this OP1 row is the active slot `.atom 2`. -/
theorem failRow_skeletonDec_head :
    P8Census.skeletonDec failRow .f_h = .atom 2 := by
  simp [P8Census.skeletonDec, failRow, SemanticStrategy.decActive]

/-- The named extra fails at `q = 2`: active decomposition is `.atom 2`. -/
theorem skeletonBounded_fails_of_decomp_atom_two :
    ¬ failSkeleton.BoundedBy 2 := by
  intro h
  have hb := (List.forall_iff_forall_mem.mp h.computeRows) _ failRow_mem_computeRows
  have hf_h : SemanticStrategy.decActive .s1 .f_h = true :=
    op1_head_and_tail_active.1
  have hdec : FieldEmbedding.BoundedBy 2 (failRow.decomposition .f_h hf_h) :=
    hb.2.2.2.1 .f_h hf_h
  simp [failRow] at hdec

/-- Census at `Λ = 2` holds: every reconstructed pair, including the
unbounded decomposition atom, has at most two leaves. -/
theorem failSkeleton_census :
    EdgeComparisonCensus.CombinedSkeletonCensus K failSkeleton 2 :=
  census_of_identified_skeleton_pairs
    (fun s hs c hc => by
      rw [failSkeleton_computeRows] at hs
      simp only [List.mem_singleton] at hs
      subst hs
      simp [P8Census.skeletonComparisons, P8Census.skeletonUse,
        P8Census.skeletonDec, failRow, SemanticStrategy.decActive] at hc
      obtain rfl | rfl | rfl := hc
      · simp [ComparisonUse.LeavesBounded, Noun.leaves]
      · simp [ComparisonUse.LeavesBounded, Noun.leaves]
      · simp [ComparisonUse.LeavesBounded, Noun.leaves])
    ⟨by simp [failSkeleton, failRow, Noun.leaves],
      by simp [failSkeleton, failRow, Noun.leaves],
      by simp [failSkeleton, failRow, Noun.leaves]⟩
    (fun pair hp => by
      unfold EdgeComparisonCensus.edgePairs failSkeleton at hp
      rw [bfsForest_cons_eq _ (by simp)] at hp
      simp [bfsForest_nil, EdgeComparisonCensus.rowEdgePairs,
        NTree.childOpt] at hp)

/-- Size-window extra is empty on this OP1 skeleton.  Not a general inhabit. -/
theorem failSkeleton_sizeWindowBound_vacuous :
    SizeWindowCounting.SizeWindowNounsBoundedBy failSkeleton 2 := by
  intro n hn
  have hrows := failSkeleton_computeRows
  simp [SizeWindowCounting.skeletonSizeWindowNouns] at hn
  rw [hrows] at hn
  simp [SizeWindowCounting.requiredSizeWindowNouns, failRow] at hn

/-- Combined: census and size-window hold, root/subformula/memory-record
bounds hold, and the named extra fails -/
theorem skeletonBounded_does_not_follow_from_census_or_sizeWindow :
    ServedLookupBridge.SkeletonRecordEquations failRow ∧
      FieldEmbedding.BoundedBy 2 failRow.subject ∧
      FieldEmbedding.BoundedBy 2 failRow.formula ∧
      FieldEmbedding.BoundedBy 2 failRow.evaluation ∧
      (∀ i h slot, FieldEmbedding.BoundedBy 2 (failRow.subformula i h slot)) ∧
      (∀ i h, (failRow.memoryRecord i h).BoundedBy 2) ∧
      EdgeComparisonCensus.CombinedSkeletonCensus K failSkeleton 2 ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy failSkeleton 2 ∧
      ¬ failSkeleton.BoundedBy 2 :=
  let hroot := failRow_root_subformula_memory_bounded
  ⟨failRow_recordEquations, hroot.1, hroot.2.1, hroot.2.2.1,
    hroot.2.2.2.1, hroot.2.2.2.2, failSkeleton_census,
    failSkeleton_sizeWindowBound_vacuous,
    skeletonBounded_fails_of_decomp_atom_two⟩

/-- The prover's named witness has the same predicate-separation. -/
theorem prover_witness_agrees :
    ServedLookupBridge.SkeletonRecordEquations s1DecompFailRow ∧
      FieldEmbedding.BoundedBy 2 s1DecompFailRow.subject ∧
      FieldEmbedding.BoundedBy 2 s1DecompFailRow.formula ∧
      FieldEmbedding.BoundedBy 2 s1DecompFailRow.evaluation ∧
      (∀ i h slot, FieldEmbedding.BoundedBy 2
        (s1DecompFailRow.subformula i h slot)) ∧
      (∀ i h, (s1DecompFailRow.memoryRecord i h).BoundedBy 2) ∧
      EdgeComparisonCensus.CombinedSkeletonCensus K s1DecompFailSkeleton 2 ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy s1DecompFailSkeleton 2 ∧
      ¬ s1DecompFailSkeleton.BoundedBy 2 :=
  GenericHonestData.skeletonBounded_does_not_follow_from_census_or_sizeWindow

/-! ## D. Not a restatement; `combinedBounded` not swallowed -/

/-- SizeWindow extra is still `n.leaves ≤ Λ` on OP3/OP4/OP6 products. -/
theorem sizeWindowBound_still_leaves_le_Lambda
    {S : SemanticSkeleton} {Λ : ℕ} :
    SizeWindowCounting.SizeWindowNounsBoundedBy S Λ =
      ∀ n ∈ SizeWindowCounting.skeletonSizeWindowNouns S, n.leaves ≤ Λ :=
  Batch114.sizeWindowBound_still_leaves_le_Lambda

/-- Sampled SizeWindow is still `leaves < orderOf z` -/
theorem SizeWindow_still_leaves_lt_orderOf {z : K} {n : Noun} :
    OpcodeSemantics.SizeWindow z n ↔
      1 < orderOf z ∧ n.leaves < orderOf z :=
  Batch114.SizeWindow_still_leaves_lt_orderOf

/-- Census extra is still reconstructed pair leaf bounds. -/
theorem census_still_pair_leaf_bounds
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    (∀ pair ∈ BoundSemanticTrace.skeletonPairs K
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      pair.1.leaves ≤ E.Λ ∧ pair.2.leaves ≤ E.Λ) ∧
      (∀ pair ∈ EdgeComparisonCensus.edgePairs
          (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).computeTree,
        pair.1.leaves ≤ E.Λ ∧ pair.2.leaves ≤ E.Λ) :=
  Batch114.census_is_skeleton_pair_leaf_bounds E P M C

/-- `combinedBounded` is pair-wise atom-range on census pairs, not row
`BoundedBy` -/
theorem combinedBounded_is_pair_atom_range
    {q : ℕ} {S : SemanticSkeleton}
    (h : CombinedBoundedBy K q S) :
    ∀ pair ∈ EdgeComparisonCensus.combinedSkeletonPairs K S,
      FieldEmbedding.BoundedBy q pair.1 ∧
        FieldEmbedding.BoundedBy q pair.2 :=
  h

/-- `censusAssemblyOf` still copies `combinedBounded` from the named extra. -/
theorem censusAssemblyOf_still_copies_combinedBounded
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).combinedBounded = C.combinedBounded :=
  rfl

theorem failRow_opcodeHead_pair_mem :
    (Noun.atom 2, Noun.atom 1) ∈
      BoundSemanticTrace.skeletonPairs K failSkeleton := by
  unfold BoundSemanticTrace.skeletonPairs
  refine List.mem_append.mpr (.inr ?_)
  refine List.mem_map.mpr ⟨P8Census.skeletonUse .opcodeHead (.atom 2) (.atom 1), ?_, rfl⟩
  simp [P8Census.skeletonComparisonCensus, failSkeleton_computeRows,
    P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
    failRow, SemanticStrategy.decActive]

/-- That does not
make `combinedBounded` the same extra: see `zeroRow` below. -/
theorem combinedBounded_also_fails_on_failSkeleton :
    ¬ CombinedBoundedBy K 2 failSkeleton := by
  intro h
  have hpair : (Noun.atom 2, Noun.atom 1) ∈
      EdgeComparisonCensus.combinedSkeletonPairs K failSkeleton := by
    unfold EdgeComparisonCensus.combinedSkeletonPairs
    exact List.mem_append.mpr (.inl (failRow_opcodeHead_pair_mem (K := K)))
  have hb := h _ hpair
  simp [FieldEmbedding.BoundedBy] at hb

/-- OP1 row whose every reconstructed noun is `.atom 0` or `[0 0]`.
`BoundedBy 1` holds; opcode atom `1` is not `BoundedBy 1`. -/
def zeroRow : ComputeRowSkeleton where
  state := .s1
  subject := .atom 0
  formula := .cell (.atom 0) (.atom 0)
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 1⟩

def zeroSkeleton : SemanticSkeleton where
  computeTree := .node zeroRow []
  memoryForest := []

theorem zeroSkeleton_computeRows :
    computeSkeletonRows zeroSkeleton = [zeroRow] := by
  unfold computeSkeletonRows zeroSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

theorem zeroRow_bounded_by_one :
    zeroRow.BoundedBy 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [zeroRow]
  · simp [zeroRow]
  · simp [zeroRow]
  · intro slot hact
    simp [zeroRow]
  · intro i h slot
    simp [zeroRow]
  · intro i h
    simp [zeroRow, MemRecSkeleton.BoundedBy]

/-- Row `BoundedBy 1` holds on this OP1 skeleton.  Memory forest is empty. -/
theorem zeroSkeleton_bounded_by_one :
    zeroSkeleton.BoundedBy 1 where
  computeRows := by
    rw [List.forall_iff_forall_mem]
    intro s hs
    rw [zeroSkeleton_computeRows] at hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact zeroRow_bounded_by_one
  memoryRows := by
    rw [List.forall_iff_forall_mem]
    intro s hs
    unfold memorySkeletonRows zeroSkeleton at hs
    simp [bfsForest_nil] at hs
  memoryTrees := by
    intro tree ht
    simp [zeroSkeleton] at ht

/-- Opcode-head right noun is the literal `.atom 1`, which is not a
compute-row noun of `BoundedBy` -/
theorem zeroRow_opcodeHead_right_is_atom_one :
    ((P8Census.skeletonComparisons (K := K) zeroRow).head?).map
        ComparisonUse.right = some (.atom 1) := by
  simp [P8Census.skeletonComparisons, P8Census.skeletonUse,
    P8Census.skeletonDec, zeroRow, SemanticStrategy.decActive]

theorem zeroRow_opcodeHead_pair_mem :
    (Noun.atom 0, Noun.atom 1) ∈
      BoundSemanticTrace.skeletonPairs K zeroSkeleton := by
  unfold BoundSemanticTrace.skeletonPairs
  refine List.mem_append.mpr (.inr ?_)
  refine List.mem_map.mpr ⟨P8Census.skeletonUse .opcodeHead (.atom 0) (.atom 1), ?_, rfl⟩
  simp [P8Census.skeletonComparisonCensus, zeroSkeleton_computeRows,
    P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
    zeroRow, SemanticStrategy.decActive]

/-- Predicates are distinct: `skeletonBounded` holds at `q = 1` while
`CombinedBoundedBy` fails on opcode atom `1`.  This is not an inhabit of
`combinedBounded` at consumed `q` (`11 < ringChar`). -/
theorem combinedBounded_not_restatement_of_skeletonBounded :
    zeroSkeleton.BoundedBy 1 ∧
      ¬ CombinedBoundedBy K 1 zeroSkeleton := by
  refine ⟨zeroSkeleton_bounded_by_one, ?_⟩
  intro h
  have hpair : (Noun.atom 0, Noun.atom 1) ∈
      EdgeComparisonCensus.combinedSkeletonPairs K zeroSkeleton := by
    unfold EdgeComparisonCensus.combinedSkeletonPairs
    exact List.mem_append.mpr (.inl (zeroRow_opcodeHead_pair_mem (K := K)))
  have hb := h _ hpair
  simp [FieldEmbedding.BoundedBy] at hb

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
theorem nmr_axis_is_not_skeleton_atom_range
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
  Batch114.slot_predicates_still_iff_served s

variable [Fintype F] [DecidableEq F]

/-! ## E. -/

inductive ReviewedField115
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

def substantiveFields115 : List ReviewedField115 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields115 : List ReviewedField115 := [.structural]

def residualFields115 : List ReviewedField115 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Leaving `skeletonBounded` named is not a statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields115.length = 11 ∧
      typeSummaryFields115.length = 1 ∧
      residualFields115 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields115.length = 2 ∧
      (substantiveFields115 ++ typeSummaryFields115 ++ residualFields115).Nodup ∧
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
#print axioms computeRowBounded_includes_decomposition
#print axioms skeletonBounded_extra_is_q_atom_range
#print axioms computeSkeletonOf_decomp_is_decompNoun
#print axioms atom_two_one_leaf_not_bounded_by_two
#print axioms realizes_is_enc_eq
#print axioms decompNoun_active_is_realizes
#print axioms realizedNouns_cover_root_triple
#print axioms computeSkeletonOf_root_bounded_is_triple
#print axioms decompNoun_f_h_is_root_head
#print axioms op1_head_and_tail_active
#print axioms censusAssemblyOf_still_copies_skeletonBounded
#print axioms skeletonBounded_of_decomp_bounds_independent
#print axioms failRow_formula_is_zero_zero
#print axioms failRow_formula_leaves
#print axioms failRow_formula_bounded_by_two
#print axioms failRow_decomp_head_is_atom_two
#print axioms failRow_recordEquations
#print axioms failRow_root_subformula_memory_bounded
#print axioms failSkeleton_computeRows
#print axioms failRow_mem_computeRows
#print axioms failRow_skeletonDec_head
#print axioms skeletonBounded_fails_of_decomp_atom_two
#print axioms failSkeleton_census
#print axioms failSkeleton_sizeWindowBound_vacuous
#print axioms skeletonBounded_does_not_follow_from_census_or_sizeWindow
#print axioms prover_witness_agrees
#print axioms sizeWindowBound_still_leaves_le_Lambda
#print axioms SizeWindow_still_leaves_lt_orderOf
#print axioms census_still_pair_leaf_bounds
#print axioms combinedBounded_is_pair_atom_range
#print axioms censusAssemblyOf_still_copies_combinedBounded
#print axioms failRow_opcodeHead_pair_mem
#print axioms combinedBounded_also_fails_on_failSkeleton
#print axioms zeroRow_bounded_by_one
#print axioms zeroSkeleton_bounded_by_one
#print axioms zeroRow_opcodeHead_right_is_atom_one
#print axioms zeroRow_opcodeHead_pair_mem
#print axioms combinedBounded_not_restatement_of_skeletonBounded
#print axioms censusRecordPremises_eta_still_five
#print axioms residualPremises_eta_still_four
#print axioms memoryRecordPremises_eta_still_two
#print axioms inputs_eta_still_named
#print axioms dataOfCensus_still_requires_C
#print axioms packageOf_still_takes_named_Inputs
#print axioms packageOf_not_forall_omega
#print axioms released_builder_still_takes_hzero
#print axioms any_universal_data_still_forces_q_pin
#print axioms nmr_axis_is_not_skeleton_atom_range
#print axioms slot_predicates_still_iff_served
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms containment_is_implication_not_forall_omega
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.skeletonBounded_is_q_atom_range
#print axioms
  Nock.NockVMROM.Thm54.GenericHonestData.skeletonBounded_does_not_follow_from_census_or_sizeWindow
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch115
