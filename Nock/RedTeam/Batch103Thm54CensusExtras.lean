import Nock.NockVMROM.Thm54.GenericHonestData
import Nock.RedTeam.Batch96Thm54GenericHonestCommitment
import Nock.RedTeam.Batch101Thm54MemoryAssembly
import Nock.RedTeam.Batch102Thm54CensusAssembly
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

NMR axis carry is not re-litigated (`Def:NMR` 1328, per-node carry 1301).

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  All five `CensusRecordPremises` fields stay named.
Memory-row and memory-tree `q`-boundedness are theorems of `E` plus NMR extras,
and they are **not** `skeletonBounded`.  `sizeWindowBound` is `n.leaves ≤ Λ`;
`OpcodeSemantics.SizeWindow` is `n.leaves < orderOf z`.  `dataOfCensus` still
takes `C`.  No `∀ E, Data E`.  Accounting remains `11+1+2`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch103

open scoped Classical
open Nock Nock.Framework Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## A. Derived memory bounds are not `skeletonBounded` -/

/-- Assembled memory-row skeletons are `q`-bounded from public-row existence
and halt atoms.  This is a theorem of `E` plus NMR extras. -/
theorem memory_row_bounds_of_assembly
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) :
    (memorySkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M))).Forall
      (MemoryRowSkeleton.BoundedBy E.q) :=
  memorySkeletonRows_bounded E P M

/-- Assembled memory-tree node labels are likewise `q`-bounded. -/
theorem memory_tree_bounds_of_assembly
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) :
    ∀ tree ∈ (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).memoryForest,
      ∀ node, InTree tree node → node.label.BoundedBy E.q :=
  memoryTrees_bounded E P M

/-- `SemanticSkeleton.BoundedBy` is three conjuncts.  Memory rows and trees
are two of them; compute-row boundedness is the third -/
theorem skeletonBounded_expands_three_conjuncts
    {q : ℕ} {S : SemanticSkeleton} (h : S.BoundedBy q) :
    (computeSkeletonRows S).Forall (ComputeRowSkeleton.BoundedBy q) ∧
      (memorySkeletonRows S).Forall (MemoryRowSkeleton.BoundedBy q) ∧
      (∀ tree ∈ S.memoryForest, ∀ node, InTree tree node →
        node.label.BoundedBy q) :=
  ⟨h.computeRows, h.memoryRows, h.memoryTrees⟩

/-- Compute-row boundedness additionally requires every decomposition noun. -/
theorem computeRowBounded_requires_decompositions
    {q : ℕ} {s : ComputeRowSkeleton} (h : s.BoundedBy q) :
    ∀ slot hact, FieldEmbedding.BoundedBy q (s.decomposition slot hact) :=
  h.2.2.2.1

/-- The reconstructed compute skeleton stores `decompNoun` in every
decomposition slot -/
theorem computeSkeletonOf_decomposition_is_decompNoun
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (slot : DecSlot) (hact : decActive row.1 slot = true) :
    (computeSkeletonOf data pubR).decomposition slot
        (by simpa [computeSkeletonOf] using hact) =
      decompNoun data slot :=
  rfl

/-- Active decomposition nouns are encoding equations, not `BoundedBy q`. -/
theorem decompNoun_active_is_realizes
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) (slot : DecSlot)
    (hact : decActive row.1 slot = true) :
    OpcodeSemantics.Realizes row.2.1.z (SemanticStrategy.decFP row.2.2.2 slot)
      (decompNoun data slot) :=
  decompNoun_realizes_active data slot hact

/-- `Realizes` is the NPR encoding equation `fp = enc z n`.  It does not
mention `BoundedBy` -/
theorem realizes_is_encoding_equation {z : K} {fp : ComputeTable.FP K}
    {n : Noun} :
    OpcodeSemantics.Realizes z fp n ↔ fp = GlobalCarryRecognizer.enc z n :=
  Iff.rfl

/-- `realizedNouns.bounded` covers the root triple only. -/
theorem realizedNouns_cover_root_triple_only
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) :
    data.root.subject ∈ data.realizedNouns ∧
      data.root.formula ∈ data.realizedNouns ∧
      data.root.result ∈ data.realizedNouns ∧
      (∀ n ∈ data.realizedNouns, FieldEmbedding.BoundedBy q n) :=
  ⟨data.subject_mem, data.formula_mem, data.result_mem, data.bounded⟩

/-- Memory-row and memory-tree bounds of the assembled skeleton are two
conjuncts of `BoundedBy`, not the `skeletonBounded` field consumed by `Data`. -/
theorem memory_bounds_are_not_skeletonBounded
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) :
    (memorySkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M))).Forall
      (MemoryRowSkeleton.BoundedBy E.q) ∧
      (∀ tree ∈
          (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).memoryForest,
        ∀ node, InTree tree node → node.label.BoundedBy E.q) ∧
      ((skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q →
        (computeSkeletonRows
            (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M))).Forall
          (ComputeRowSkeleton.BoundedBy E.q)) :=
  ⟨memorySkeletonRows_bounded E P M, memoryTrees_bounded E P M,
    fun h => h.computeRows⟩

/-! ## B. Under-closed attacks: none of the five is a theorem of `E` -/

/-- Exhaustive eta: remaining extras are exactly five named fields. -/
theorem censusRecordPremises_eta_exactly_five
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

/-- `censusAssemblyOf` copies the five extras from `C` -/
theorem censusAssemblyOf_copies_five_extras
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).slotSemantics = C.slotSemantics ∧
      (censusAssemblyOf E P M C).census = C.census ∧
      (censusAssemblyOf E P M C).sizeWindowBound = C.sizeWindowBound ∧
      (censusAssemblyOf E P M C).skeletonBounded = C.skeletonBounded ∧
      (censusAssemblyOf E P M C).combinedBounded = C.combinedBounded :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `needs.served` at OP0 is a `ServedLookup` of *some* nouns, not the
reconstructed skeleton's subject / `mr2` axis / evaluation. -/
theorem served_lookup_of_s0_is_some_nouns
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) (h : row.1 = .s0) :
    ∃ lookup ∈ data.needs.served,
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun lookup.root 1) lookup.axis lookup.child :=
  served_lookup_of_s0_needs data h

/-- `needs.served` at OP9 is likewise a lookup of *some* nouns. -/
theorem served_lookup_of_s9_is_some_nouns
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) (h : row.1 = .s9) :
    ∃ lookup ∈ data.needs.served,
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun lookup.root 1) lookup.axis lookup.child :=
  served_lookup_of_s9_needs data h

/-- Slot semantics of OP0 is the Nock `/` fact after identifying those nouns
with the reconstructed skeleton -/
theorem slotSemantics_s0_needs_skeleton_identification {z : K}
    (s : ComputeRowSkeleton) (lookup : ServedNounLookup z)
    (hstate : s.state = .s0) (hroot : lookup.root = s.subject)
    (haxis : lookup.axis = P8Census.skeletonMemoryAxis s 1)
    (hchild : lookup.child = s.evaluation) :
    ServedLookupBridge.SkeletonSlotSemantics s :=
  skeletonSlotSemantics_of_s0_identification s lookup hstate hroot haxis hchild

/-- Slot semantics of OP9 needs the same identification against `sf1.result`,
`mr3` axis, and `sf2.formula` -/
theorem slotSemantics_s9_needs_skeleton_identification {z : K}
    (s : ComputeRowSkeleton) (lookup : ServedNounLookup z)
    (hstate : s.state = .s9)
    (hroot : lookup.root = P8Census.skeletonSubformula s 0 .result)
    (haxis : lookup.axis = P8Census.skeletonMemoryAxis s 2)
    (hchild : lookup.child = P8Census.skeletonSubformula s 1 .formula) :
    ServedLookupBridge.SkeletonSlotSemantics s :=
  skeletonSlotSemantics_of_s9_identification s lookup hstate hroot haxis hchild

/-- `needs.served` length is the paper OP0/OP9 count.  Length is not
identification -/
theorem needs_served_is_length_only
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) :
    data.needs.served.length = requiredServedLookups row.1 ∧
      requiredServedLookups .s0 = 1 ∧
      requiredServedLookups .s9 = 1 ∧
      requiredServedLookups .s1 = 0 :=
  ⟨data.needs.served_count, rfl, rfl, rfl⟩

/-- SepSeed uniqueness is not demanded. -/
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

/-- `comparison_leaves` quantifies `data.comparisons`, a free role-matching
list -/
theorem comparison_leaves_quantify_data_comparisons
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) :
    (∀ c ∈ data.comparisons, c.LeavesBounded Λ) ∧
      data.comparisons.map ComparisonUse.role = requiredComparisonRoles row.1 :=
  ⟨data.comparison_leaves, data.comparison_roles⟩

/-- Skeleton-projected OP1 comparisons are `decompNoun`/`root` nouns, not the
free `data.comparisons` list -/
theorem s1_skeletonComparisons_are_not_data_comparisons
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (h : row.1 = .s1) :
    P8Census.skeletonComparisons (K := K) (computeSkeletonOf data pubR) =
      [P8Census.skeletonUse .opcodeHead data.root.head (.atom 1),
        P8Census.skeletonUse .formulaCons data.root.formula
          (.cell data.root.head data.root.tail),
        P8Census.skeletonUse .producedResult data.root.result data.root.tail] :=
  computeSkeletonOf_s1_skeletonComparisons data pubR h

/-- PairFaithful on `data.comparisons` includes SepSeed uniqueness, which the
census extra does not demand -/
theorem comparison_faithful_demands_sepSeed
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    {data : ComputeRowSemanticData q Λ row} {c : ComparisonUse}
    (hc : c ∈ data.comparisons) :
    GlobalCarryRecognizer.SepSeed row.2.1.z c.left c.right ∧
      FieldEmbedding.BoundedBy q c.left ∧
      FieldEmbedding.BoundedBy q c.right :=
  let pf := data.comparison_faithful c hc
  ⟨pf.separates, pf.left_bounded, pf.right_bounded⟩

/-! ## C. `sizeWindowBound` vs `SizeWindow` are distinct predicates -/

/-- The named extra is the seed-independent leaf bound `n.leaves ≤ Λ`. -/
theorem sizeWindowBound_is_leaves_le_Lambda
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    ∀ n ∈ SizeWindowCounting.skeletonSizeWindowNouns
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      n.leaves ≤ E.Λ :=
  C.sizeWindowBound

/-- `OpcodeSemantics.SizeWindow` is the sampled-seed order bound
`1 < orderOf z` and `n.leaves < orderOf z` -/
theorem sizeWindow_is_order_bound {z : K} {n : Noun}
    (hw : OpcodeSemantics.SizeWindow z n) :
    1 < orderOf z ∧ n.leaves < orderOf z :=
  ⟨hw.one_lt_order, hw.leaves_lt_order⟩

/-- At the unit seed the order bound is empty, independently of `Λ`. -/
theorem sizeWindow_at_one_fails (n : Noun) :
    ¬ OpcodeSemantics.SizeWindow (1 : K) n := by
  intro hw
  have hlt : 1 < orderOf (1 : K) := hw.one_lt_order
  simp [orderOf_one] at hlt

/-- Row-local `data.windows` carry `SizeWindow` at the row seed, not the
named leaf-window extra.  Those windows exist only for OP3/OP4/OP6. -/
theorem data_windows_are_order_windows
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) :
    (∀ w ∈ data.windows, OpcodeSemantics.SizeWindow row.2.1.z w.noun) ∧
      data.windows.length = requiredSizeWindows row.1 ∧
      requiredSizeWindows .s3 = 1 ∧
      requiredSizeWindows .s4 = 1 ∧
      requiredSizeWindows .s6 = 1 ∧
      requiredSizeWindows .s1 = 0 :=
  ⟨fun w _ => w.window, data.windows_count, rfl, rfl, rfl, rfl⟩

/-- Size-window nouns of the extra are OP3/OP4/OP6 subformula products of
the reconstructed skeleton, not `data.windows` -/
theorem sizeWindowNouns_are_skeleton_subformula_products
    (s : ComputeRowSkeleton) :
    (s.state = .s3 ∨ s.state = .s4 →
      SizeWindowCounting.requiredSizeWindowNouns s =
        [P8Census.skeletonSubformula s 0 .result]) ∧
      (s.state = .s6 →
        SizeWindowCounting.requiredSizeWindowNouns s =
          [P8Census.skeletonSubformula s 1 .result]) ∧
      (s.state = .s1 → SizeWindowCounting.requiredSizeWindowNouns s = []) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; rcases h with h | h <;> simp [SizeWindowCounting.requiredSizeWindowNouns, h]
  · intro h; simp [SizeWindowCounting.requiredSizeWindowNouns, h]
  · intro h; simp [SizeWindowCounting.requiredSizeWindowNouns, h]

/-! ## D. Combined boundedness is not `E.q_gt_one` or atom shape -/

/-- OP9 skeleton comparisons include the opcode atom `.atom 9`. -/
theorem s9_skeletonComparisons_contain_atom_nine
    (s : ComputeRowSkeleton) (h : s.state = .s9) :
    P8Census.skeletonUse .opcodeHead (P8Census.skeletonDec s .f_h) (.atom 9) ∈
      P8Census.skeletonComparisons (K := K) s := by
  simp [P8Census.skeletonComparisons, P8Census.skeletonUse, h]

/-- Combined boundedness of a skeleton that contains an OP9 row requires
`BoundedBy q (.atom 9)` -/
theorem combinedBounded_of_s9_requires_atom_nine
    {S : SemanticSkeleton} {q : ℕ}
    (hb : ProductionP8Containment.CombinedBoundedBy K q S)
    {s : ComputeRowSkeleton}
    (hs : s ∈ computeSkeletonRows S) (h9 : s.state = .s9) :
    FieldEmbedding.BoundedBy q (.atom 9) := by
  have hc :
      P8Census.skeletonUse .opcodeHead (P8Census.skeletonDec s .f_h) (.atom 9) ∈
        P8Census.skeletonComparisons (K := K) s :=
    s9_skeletonComparisons_contain_atom_nine s h9
  have hflat :
      P8Census.skeletonUse .opcodeHead (P8Census.skeletonDec s .f_h) (.atom 9) ∈
        P8Census.skeletonComparisonCensus (K := K) S :=
    List.mem_flatMap.mpr ⟨s, hs, hc⟩
  have hpair :
      (P8Census.skeletonDec s .f_h, .atom 9) ∈
        BoundSemanticTrace.skeletonPairs K S := by
    refine List.mem_append.mpr (.inr ?_)
    exact List.mem_map.mpr ⟨_, hflat, rfl⟩
  have hcomb :
      (P8Census.skeletonDec s .f_h, .atom 9) ∈
        EdgeComparisonCensus.combinedSkeletonPairs K S :=
    List.mem_append.mpr (.inl hpair)
  exact (hb _ hcomb).2

/-- `.atom 9` is not `q`-bounded at `q = 2`.  `E.q_gt_one` is only `1 < q`. -/
theorem atom_nine_not_bounded_by_two :
    ¬ FieldEmbedding.BoundedBy 2 (.atom 9) := by
  simp

/-- `E.q_gt_one` permits `q = 2`. -/
theorem q_gt_one_is_one_lt_q (E : BuildableNockExecution F K) :
    1 < E.q :=
  E.q_gt_one

theorem two_satisfies_q_gt_one : 1 < 2 := by
  decide

/-- `AxisAtomPremises` is atom *shape*, not `atomVal < q`. -/
theorem axisAtomPremises_are_shape
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    {data : ComputeRowSemanticData q Λ row} (h : AxisAtomPremises data) :
    (row.1 = .s0 → ∃ k, data.root.tail = .atom k) ∧
      (row.1 = .s9 → ∃ k, decompNoun data .f_th = .atom k) :=
  h

/-- Combined boundedness extra is `q`-boundedness of every combined skeleton
pair -/
theorem combinedBounded_expands_to_pair_atom_bounds
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    ∀ pair ∈ EdgeComparisonCensus.combinedSkeletonPairs K
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      FieldEmbedding.BoundedBy E.q pair.1 ∧
        FieldEmbedding.BoundedBy E.q pair.2 :=
  C.combinedBounded

/-! ## E. `Data` still needs named `C`; still five -/

/-- Residual plus memory plus derived memory bounds still do not produce
`Data`: `dataOfCensus` retains the five-field argument. -/
theorem dataOfCensus_still_requires_and_projects_five_extras
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    let D := dataOfCensus E P M C hln
    (∀ s ∈ computeSkeletonRows D.skeleton,
        ServedLookupBridge.SkeletonSlotSemantics s) ∧
      EdgeComparisonCensus.CombinedSkeletonCensus K D.skeleton D.Λ ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy D.skeleton D.Λ ∧
      D.skeleton.BoundedBy E.q ∧
      ProductionP8Containment.CombinedBoundedBy K E.q D.skeleton := by
  dsimp [dataOfCensus, dataOfRecord, dataOf, censusAssemblyOf, Data.skeleton]
  exact ⟨C.slotSemantics, C.census, C.sizeWindowBound, C.skeletonBounded,
    C.combinedBounded⟩

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

/-- Hypothetical universal `Data` still manufactures the named characteristic
equality.  No such constructor is supplied. -/
theorem any_universal_data_constructor_still_forces_q_pin
    (g : ∀ E : BuildableNockExecution F K, Data E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  fun E => (g E).q_eq_ringChar

/-! ## F. Concrete non-vacuity of derived memory bounds; F73 is OP1 -/

open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.BuildableConcrete
open Nock.RedTeam.Batch96.ConcretePremises
open Nock.RedTeam.Batch101

/-- Memory-row and memory-tree `q`-boundedness inhabit on the real F73
execution without manufacturing `CensusRecordPremises`. -/
theorem concrete_memory_bounds_nonvacuous_without_census :
    (memorySkeletonRows
        (skeletonOfNodes
          (computeNodesOf concreteExecution f73_residualPremises)
          (memoryNodesOf concreteExecution concreteMemoryRecordPremises))).Forall
      (MemoryRowSkeleton.BoundedBy concreteExecution.q) ∧
      (∀ tree ∈
          (skeletonOfNodes
            (computeNodesOf concreteExecution f73_residualPremises)
            (memoryNodesOf concreteExecution
              concreteMemoryRecordPremises)).memoryForest,
        ∀ node, InTree tree node →
          node.label.BoundedBy concreteExecution.q) :=
  ⟨memorySkeletonRows_bounded concreteExecution f73_residualPremises
      concreteMemoryRecordPremises,
    memoryTrees_bounded concreteExecution f73_residualPremises
      concreteMemoryRecordPremises⟩

/-- The F73 compute row is OP1.  Live OP0/OP9 slot identification and the
OP9 `.atom 9` combined-boundedness stop are not claimed on this fixture.
This is not rounded up to a generic inhabitant of the five extras. -/
theorem f73_compute_row_is_op1 :
    (concreteExecution.exec.computeRowAt
      ⟨0, concreteExecution.cfg.compRows_pos⟩).1 = .s1 :=
  Batch102.f73_compute_row_is_op1

/-- F73 pins `q = 73`, which *does* bound `.atom 9`.  The combined-boundedness
stop is the generic `1 < q` vs `q = 2` control, not this fixture. -/
theorem f73_q_is_seventy_three_and_bounds_atom_nine :
    concreteExecution.q = 73 ∧
      FieldEmbedding.BoundedBy concreteExecution.q (.atom 9) :=
  ⟨rfl, by decide⟩

/-! ## G. -/

inductive ReviewedField103
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

def substantiveFields103 : List ReviewedField103 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields103 : List ReviewedField103 := [.structural]

def residualFields103 : List ReviewedField103 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

theorem independent_exact_eleven_one_two_accounting :
    substantiveFields103.length = 11 ∧
      typeSummaryFields103.length = 1 ∧
      residualFields103 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields103.length = 2 ∧
      (substantiveFields103 ++ typeSummaryFields103 ++ residualFields103).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  ⟨optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth, rfl⟩

#print axioms memory_row_bounds_of_assembly
#print axioms memory_tree_bounds_of_assembly
#print axioms skeletonBounded_expands_three_conjuncts
#print axioms computeRowBounded_requires_decompositions
#print axioms computeSkeletonOf_decomposition_is_decompNoun
#print axioms decompNoun_active_is_realizes
#print axioms realizes_is_encoding_equation
#print axioms realizedNouns_cover_root_triple_only
#print axioms memory_bounds_are_not_skeletonBounded
#print axioms censusRecordPremises_eta_exactly_five
#print axioms censusAssemblyOf_copies_five_extras
#print axioms served_lookup_of_s0_is_some_nouns
#print axioms served_lookup_of_s9_is_some_nouns
#print axioms slotSemantics_s0_needs_skeleton_identification
#print axioms slotSemantics_s9_needs_skeleton_identification
#print axioms needs_served_is_length_only
#print axioms census_is_skeleton_pair_leaf_bounds
#print axioms comparison_leaves_quantify_data_comparisons
#print axioms s1_skeletonComparisons_are_not_data_comparisons
#print axioms comparison_faithful_demands_sepSeed
#print axioms sizeWindowBound_is_leaves_le_Lambda
#print axioms sizeWindow_is_order_bound
#print axioms sizeWindow_at_one_fails
#print axioms data_windows_are_order_windows
#print axioms sizeWindowNouns_are_skeleton_subformula_products
#print axioms s9_skeletonComparisons_contain_atom_nine
#print axioms combinedBounded_of_s9_requires_atom_nine
#print axioms atom_nine_not_bounded_by_two
#print axioms q_gt_one_is_one_lt_q
#print axioms two_satisfies_q_gt_one
#print axioms axisAtomPremises_are_shape
#print axioms combinedBounded_expands_to_pair_atom_bounds
#print axioms dataOfCensus_still_requires_and_projects_five_extras
#print axioms residualPremises_eta_still_four
#print axioms memoryRecordPremises_eta_still_two
#print axioms any_universal_data_constructor_still_forces_q_pin
#print axioms concrete_memory_bounds_nonvacuous_without_census
#print axioms f73_compute_row_is_op1
#print axioms f73_q_is_seventy_three_and_bounds_atom_nine
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memorySkeletonRows_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryTrees_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.censusRecordPremises_still_five
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.dataOfCensus
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch103
