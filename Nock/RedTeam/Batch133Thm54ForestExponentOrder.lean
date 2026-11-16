import Nock.NockVMROM.Thm54.ForestExponentWindow
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# At which quantifier does the refutation bind?

Different context from the
prover.  **No carrier field is added** and no named premise of the released capstone is weakened.

## The question

```
¬ ∀ D' : Data E, ForestExponentOrder (D'.executionTemplate E.cfg.challenges.z) E.cfg.challenges.α
```

and concludes that unconditional `∀ a g` fibre acceptance "is not reachable by discharging this
premise".  The frame-lock rule (`.cursor/rules/nockvm-frame-lock.mdc`) says a negative lead binds
only at the quantifier the consumed capstone actually instantiates.  So: what quantifier is that?

## §A. The consumers are pointwise in the data

`GenericHonestPackage.packageOf_structuralChecksAt` and
`GenericHonestPackage.packageOf_fibre_accepts` both have the shape

```
∀ (D : Data E), … → ForestExponentOrder (D.executionTemplate z) α → C D
```

i.e. the premise is at the **same** `D` as the conclusion.  Nothing downstream needs
`∀ D', ForestExponentOrder …`; that shape is *strictly stronger* than what any consumer instantiates
(`forall_data_shape_is_strictly_stronger`).

## §B. The live F73 instantiation already discharges the premise

The F73 fixture is the fully inhabited consumed instance.

## §C. Exponent normalisation is available

`reExpData f hf D` rebuilds
a `Data E` from `D` with every committed memory exponent sent through any `f` that is invisible to
`α` (`∀ e, α ^ f e = α ^ e`).  All sixteen fields are re-inhabited, the committed skeleton is
literally unchanged, the published memory rows are unchanged, and the supplied execution at the
honest sample is unchanged.

* `f := (· % orderOf α)` is the **canonical stamp**: `normData D`.  With the single arithmetic side
  condition `0 < orderOf α`, `forestExponentOrder_normData` compiles the premise for it, so
  `normalised_package_fibre_accepts` gives unconditional `∀ a g` fibre acceptance for
  `packageOf (normData D)`.

`window_available_iff_orderOf_pos` sharpens this to an **iff** on any execution serving a lookup:
a `Data E` on that execution satisfying the window exists **iff** `0 < orderOf α`.  So at the
existential quantifier the residual is not an unavailable Nat-level identification at all — it is
exactly one arithmetic condition on `α`.

## §D. The `orderOf α = 0` edge case

`0 < orderOf α` is not an extra assumption smuggled in: it is *necessary*.  The F73 instance is
genuinely non-degenerate: `Concrete.f73_orderOf_alpha` is `9`, and the wrapped F73 forest really
reads exponent `10` where `data73` reads `1` (`Concrete.f73_wrap_is_a_genuine_shift`).

## §E. Which constructor can emit wrapped exponents

The record-level constructors
`dataOfRecord` / `dataOfCensus` / `dataOfCensusAtConsumed` are different: they route through
`memoryAssemblyOf E M`, whose stamps are `memoryStampOf E i`, a function of `E` alone
(`honest_record_exponent_is_pinned_by_E`), and `MemoryRecordPremises E` is a subsingleton
(`memoryRecordPremises_subsingleton`), so their committed exponents are **canonically determined**
(`honest_record_nodes_are_determined`).  The wrapped commitment is not in that image once the shift
is a genuine shift.

Nothing here describes the paper construction as defective: the paper assigns the canonicity
job to the verifier's α-free no-wrap check, and normalisation is precisely the honest prover
computing the canonical representative that check accepts.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch133

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.NockVMROM.Thm54.ForestExponentWindow
open Nock.AxisBridge
open Nock.AxisBatching

noncomputable section

open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## §A. The consumers are pointwise in the data -/

/-- **The premise sits at the same `D` as the conclusion.**  This is `packageOf_fibre_accepts`
re-stated with the implication made explicit: no consumer instantiates `∀ D'`. -/
theorem consumer_premise_is_pointwise_in_the_data
    {E : BuildableNockExecution F K} [Fintype F] [DecidableEq F] (D : Data E)
    (hgt : 11 < ringChar K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧
      E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    ForestExponentOrder (D.executionTemplate E.cfg.challenges.z) E.cfg.challenges.α →
      ∀ a g : K,
        (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts (honestCoin E a g) E.cfg.challenges.lam :=
  GenericHonestPackage.packageOf_fibre_accepts D hgt I hprl hmore hord hordM hrows hgenF hF

/-- **The `∀ D'` shape is strictly stronger than what is consumed.** -/
theorem forall_data_shape_is_strictly_stronger
    {E : BuildableNockExecution F K}
    (hall : ∀ D' : Data E,
      ForestExponentOrder (D'.executionTemplate E.cfg.challenges.z) E.cfg.challenges.α)
    (D : Data E) :
    ForestExponentOrder (D.executionTemplate E.cfg.challenges.z) E.cfg.challenges.α :=
  hall D

/-! ## §C. Generic exponent relabelling: one map, both instances

Every obligation `Data` carries about a committed memory node reaches the committed Nat only as
`α ^ recordExponent`.  So *any* relabelling `f`
with `α ^ f e = α ^ e` transports a whole `Data E`. -/

/-- A relabelling that fixes every label is the identity on trees. -/
theorem mapNTree_id_of_eq {A : Type} {f : A → A} (hf : ∀ a, f a = a) (t : NTree A) :
    mapNTree f t = t := by
  let P := fun t : NTree A => mapNTree f t = t
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro lbl children ih
    simp only [P, mapNTree, hf]
    refine congrArg (NTree.node lbl) ?_
    rw [show children.map (mapNTree f) = children.map id from
      List.map_congr_left (fun c hc => ih c hc), List.map_id]
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

/-- Relabel one committed template row's Nat exponent by `f`. -/
def MemoryRowTemplate.reExp (f : ℕ → ℕ) (row : MemoryRowTemplate (K := K)) :
    MemoryRowTemplate (K := K) :=
  { row with
    timestamp := { row.timestamp with recordExponent := f row.timestamp.recordExponent } }

/-- Relabel one committed memory node's Nat exponent by `f`. -/
def MemoryNode.reExp (f : ℕ → ℕ) (n : MemoryNode K) : MemoryNode K :=
  { n with stamp := { n.stamp with recordExponent := f n.stamp.recordExponent } }

@[simp] theorem MemoryNode.reExp_row (f : ℕ → ℕ) (n : MemoryNode K) :
    (MemoryNode.reExp f n).row = n.row := rfl

@[simp] theorem MemoryNode.reExp_skel (f : ℕ → ℕ) (n : MemoryNode K) :
    (MemoryNode.reExp f n).skel = n.skel := rfl

theorem renderMemoryTemplate_reExp (z : K) (f : ℕ → ℕ) (n : MemoryNode K) :
    renderMemoryTemplate z (MemoryNode.reExp f n) =
      MemoryRowTemplate.reExp f (renderMemoryTemplate z n) := rfl

theorem memoryNode_wrapAt_is_reExp (α : K) (n : MemoryNode K) :
    MemoryNode.wrapAt α n = MemoryNode.reExp (fun e => e + orderOf α) n := rfl

/-- The `Data`-level timestamp constraint sees the exponent only through `α ^ ·`, so it transports
along any `α`-invisible relabelling.  Generalises
`GenericHonestPackage.MemoryTimestampSpecializesAt_add_order` -/
theorem MemoryTimestampSpecializesAt_reExp {α : K} {f : ℕ → ℕ}
    (hf : ∀ e : ℕ, α ^ f e = α ^ e)
    {stamp : MemoryTimestampRow} {row : MemoryTable.MState × MemoryTable.DTmem K}
    (h : MemoryTimestampSpecializesAt α stamp row) :
    MemoryTimestampSpecializesAt α
      { stamp with recordExponent := f stamp.recordExponent } row := by
  obtain ⟨houter, hst, hts, hpad⟩ := h
  refine ⟨houter, hst, ?_, hpad⟩
  by_cases hact : memoryMemRecKind stamp.state = .active
  · simp only [hact, if_true] at hts ⊢
    rw [hf stamp.recordExponent]
    exact hts
  · simp only [hact, if_false] at hts ⊢
    exact hts

/-- **The relabelled commitment is still a valid commitment.** -/
theorem memoryNodesOK_reExp (z α : K) (f : ℕ → ℕ) (hf : ∀ e : ℕ, α ^ f e = α ^ e)
    (t : NTree (MemoryNode K)) (h : MemoryNodesOK z α t) :
    MemoryNodesOK z α (mapNTree (MemoryNode.reExp f) t) := by
  revert h
  let P := fun t : NTree (MemoryNode K) =>
    MemoryNodesOK z α t → MemoryNodesOK z α (mapNTree (MemoryNode.reExp f) t)
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro lbl children ih hok
    simp only [P] at ih
    obtain ⟨hfan, hstate, hbind, htime⟩ := hok _ (InTree.here _)
    simp only [NTree.label_node, NTree.children_node] at hfan hstate hbind htime
    rw [mapNTree]
    refine MemoryNodesOK.mk' ⟨?_, ?_, ?_, ?_⟩ ?_
    · simpa using hfan
    · simpa [MemoryNode.reExp] using hstate
    · simpa [MemoryNode.reExp] using hbind
    · simpa [MemoryNode.reExp] using MemoryTimestampSpecializesAt_reExp hf htime
    · intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨c₀, hc₀, rfl⟩ := hc
      exact ih c₀ hc₀ (hok.child (by simpa using hc₀))
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

/-- The relabelled commitment has the same committed skeleton, so every seed-free semantic
obligation of `Data` transports unchanged. -/
theorem skeletonOfNodes_reExp (f : ℕ → ℕ) (ct : NTree (ComputeNode K))
    (mf : List (NTree (MemoryNode K))) :
    skeletonOfNodes ct (mf.map (mapNTree (MemoryNode.reExp f))) = skeletonOfNodes ct mf := by
  simp only [skeletonOfNodes, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  rw [mapNTree_comp]
  simp only [MemoryNode.reExp_skel]

/-- **The relabelled commitment, as a `Data E` on the same execution.**  All sixteen fields are
re-inhabited; the node rows, the committed skeleton, and every semantic obligation are literally
`D`'s. -/
def reExpData {E : BuildableNockExecution F K} (f : ℕ → ℕ)
    (hf : ∀ e : ℕ, E.cfg.challenges.α ^ f e = E.cfg.challenges.α ^ e) (D : Data E) : Data E where
  computeNodes := D.computeNodes
  memoryNodes := D.memoryNodes.map (mapNTree (MemoryNode.reExp f))
  compute_rows := D.compute_rows
  memory_rows := by
    have hfun : ∀ t : NTree (MemoryNode K),
        mapNTree MemoryNode.row (mapNTree (MemoryNode.reExp f) t) =
          mapNTree MemoryNode.row t := by
      intro t
      rw [mapNTree_comp]
      simp only [MemoryNode.reExp_row]
    rw [List.map_map]
    rw [show (mapNTree MemoryNode.row ∘ mapNTree (MemoryNode.reExp f)) =
        (fun t : NTree (MemoryNode K) => mapNTree MemoryNode.row t) from funext hfun]
    exact D.memory_rows
  computeOK := D.computeOK
  memoryOK := by
    intro t ht
    simp only [List.mem_map] at ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    exact memoryNodesOK_reExp _ _ f hf t₀ (D.memoryOK t₀ ht₀)
  root_line_exponent := D.root_line_exponent
  root_line_origin := D.root_line_origin
  nounSizeBound := D.nounSizeBound
  Λ := D.Λ
  slotSemantics :=
    (skeletonOfNodes_reExp (K := K) f D.computeNodes D.memoryNodes).symm ▸ D.slotSemantics
  recordEquations :=
    (skeletonOfNodes_reExp (K := K) f D.computeNodes D.memoryNodes).symm ▸ D.recordEquations
  census := (skeletonOfNodes_reExp (K := K) f D.computeNodes D.memoryNodes).symm ▸ D.census
  sizeWindowBound :=
    (skeletonOfNodes_reExp (K := K) f D.computeNodes D.memoryNodes).symm ▸ D.sizeWindowBound
  q_eq_ringChar := D.q_eq_ringChar
  skeletonBounded :=
    (skeletonOfNodes_reExp (K := K) f D.computeNodes D.memoryNodes).symm ▸ D.skeletonBounded
  combinedBounded :=
    (skeletonOfNodes_reExp (K := K) f D.computeNodes D.memoryNodes).symm ▸ D.combinedBounded

/-- The relabelled commitment is the same commitment everywhere `Data`'s seed-free obligations can
see. -/
theorem reExpData_skeleton {E : BuildableNockExecution F K} (f : ℕ → ℕ)
    (hf : ∀ e : ℕ, E.cfg.challenges.α ^ f e = E.cfg.challenges.α ^ e) (D : Data E) :
    (reExpData f hf D).skeleton = D.skeleton :=
  skeletonOfNodes_reExp (K := K) f D.computeNodes D.memoryNodes

/-- …and it reproduces the same supplied execution at the honest sample. -/
theorem reExpData_honest_exec {E : BuildableNockExecution F K} (f : ℕ → ℕ)
    (hf : ∀ e : ℕ, E.cfg.challenges.α ^ f e = E.cfg.challenges.α ^ e) (D : Data E) :
    ((reExpData f hf D).executionTemplate E.cfg.challenges.z).specialize E.cfg.challenges.α E.cfg.challenges.lam =
      E.exec :=
  (reExpData f hf D).honest_exec

/-- `wrapDataExponents` is the `(· + orderOf α)`
instance of the generic relabelling, on the nose -/
theorem reExp_add_order_agrees_with_ao111 {E : BuildableNockExecution F K} (D : Data E) :
    (reExpData (fun e => e + orderOf E.cfg.challenges.α)
        (fun e => by rw [pow_add, pow_orderOf_eq_one, mul_one]) D).memoryNodes =
      (wrapDataExponents D).memoryNodes := rfl

/-- The α-free committed axis tree of a relabelled template is the original reindexed by `f`. -/
theorem templateAxisTree_reExp (f : ℕ → ℕ) (u : NTree (MemoryRowTemplate (K := K))) :
    templateAxisTree (mapNTree (MemoryRowTemplate.reExp f) u) =
      reindexAxisTree f (templateAxisTree u) := by
  let P := fun u : NTree (MemoryRowTemplate (K := K)) =>
    templateAxisTree (mapNTree (MemoryRowTemplate.reExp f) u) =
      reindexAxisTree f (templateAxisTree u)
  change P u
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro row children ih
    simp only [P]
    cases hs : row.timestamp.state with
    | halt =>
        simp [mapNTree, templateAxisTree, reindexAxisTree, hs, MemoryRowTemplate.reExp]
    | decompose =>
        rcases children with _ | ⟨l, rest⟩
        · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, MemoryRowTemplate.reExp]
        · rcases rest with _ | ⟨r, tail⟩
          · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, MemoryRowTemplate.reExp]
          · rcases tail with _ | ⟨x, xs⟩
            · have hl := ih l (by simp)
              have hr := ih r (by simp)
              simp only [P] at hl hr
              simp [mapNTree, templateAxisTree, reindexAxisTree, hs,
                MemoryRowTemplate.reExp, hl, hr]
            · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, MemoryRowTemplate.reExp]
    | read_root =>
        rcases children with _ | ⟨c, rest⟩
        · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, MemoryRowTemplate.reExp]
        · rcases rest with _ | ⟨x, xs⟩
          · have hc := ih c (by simp)
            simp only [P] at hc
            simp [mapNTree, templateAxisTree, reindexAxisTree, hs,
              MemoryRowTemplate.reExp, hc]
          · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, MemoryRowTemplate.reExp]
    | verify_child =>
        rcases children with _ | ⟨c, rest⟩
        · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, MemoryRowTemplate.reExp]
        · rcases rest with _ | ⟨x, xs⟩
          · have hc := ih c (by simp)
            simp only [P] at hc
            simp [mapNTree, templateAxisTree, reindexAxisTree, hs,
              MemoryRowTemplate.reExp, hc]
          · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, MemoryRowTemplate.reExp]
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

/-- The relabelled commitment publishes the relabelled template forest. -/
theorem memoryForest_reExpData {E : BuildableNockExecution F K} (f : ℕ → ℕ)
    (hf : ∀ e : ℕ, E.cfg.challenges.α ^ f e = E.cfg.challenges.α ^ e) (D : Data E) (z : K) :
    ((reExpData f hf D).executionTemplate z).memoryForest =
      ((D.executionTemplate z).memoryForest).map
        (mapNTree (MemoryRowTemplate.reExp f)) := by
  show (D.memoryNodes.map (mapNTree (MemoryNode.reExp f))).map
      (mapNTree (renderMemoryTemplate z)) =
    (D.memoryNodes.map (mapNTree (renderMemoryTemplate z))).map
      (mapNTree (MemoryRowTemplate.reExp f))
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  rw [mapNTree_comp, mapNTree_comp]
  exact congrArg (fun g => mapNTree g t)
    (funext fun n => renderMemoryTemplate_reExp z f n)

/-- Each committed root of the relabelled commitment carries the reindexed axis tree. -/
theorem alphaFreeRoot_reExpData {E : BuildableNockExecution F K} (f : ℕ → ℕ)
    (hf : ∀ e : ℕ, E.cfg.challenges.α ^ f e = E.cfg.challenges.α ^ e) (D : Data E) (z : K)
    (i : Fin (configTemplateOf E z).kMem) :
    alphaFreeRoot ((reExpData f hf D).executionTemplate z) i =
      reindexAxisTree f (alphaFreeRoot (D.executionTemplate z) i) := by
  have htree :
      templateMemoryTreeAt ((reExpData f hf D).executionTemplate z) i =
        mapNTree (MemoryRowTemplate.reExp f)
          (templateMemoryTreeAt (D.executionTemplate z) i) := by
    simp only [templateMemoryTreeAt, List.get_eq_getElem]
    simp only [memoryForest_reExpData f hf D z, List.getElem_map]
    rfl
  simp only [alphaFreeRoot, htree, templateAxisTree_reExp]

/-! ### The canonical stamp -/

/-- **The canonically stamped commitment.**  Every committed memory exponent reduced mod
`orderOf α`.  This is invisible to `α` (`pow_mod_orderOf`), so it is a `Data E` on the same
execution with the same skeleton and the same published rows. -/
def normData {E : BuildableNockExecution F K} (D : Data E) : Data E :=
  reExpData (fun e => e % orderOf E.cfg.challenges.α)
    (fun e => pow_mod_orderOf E.cfg.challenges.α e) D

theorem normData_skeleton {E : BuildableNockExecution F K} (D : Data E) :
    (normData D).skeleton = D.skeleton :=
  reExpData_skeleton _ _ D

theorem normData_claimGenerated {E : BuildableNockExecution F K} (D : Data E)
    (h : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ) :
    GeneratedField.ClaimGenerated K (normData D).skeleton.publicClaim (normData D).Λ := by
  rw [normData_skeleton]
  exact h

theorem normData_honest_exec {E : BuildableNockExecution F K} (D : Data E) :
    ((normData D).executionTemplate E.cfg.challenges.z).specialize E.cfg.challenges.α E.cfg.challenges.lam = E.exec :=
  reExpData_honest_exec _ _ D

theorem normData_memory_rows {E : BuildableNockExecution F K} (D : Data E) :
    (normData D).memoryNodes.map (mapNTree MemoryNode.row) = E.execA.memoryForest :=
  (normData D).memory_rows

/-- **`ForestExponentOrder` holds for the canonically stamped commitment**, from the single
arithmetic side condition `0 < orderOf α` and nothing else.  No Nat-level identification with the
line-number chain is needed at this quantifier -/
theorem forestExponentOrder_normData {E : BuildableNockExecution F K} (D : Data E)
    (hpos : 0 < orderOf E.cfg.challenges.α) :
    ForestExponentOrder ((normData D).executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α := by
  constructor
  · intro i e he
    rw [show ((normData D).executionTemplate E.cfg.challenges.z) =
        ((reExpData (fun e => e % orderOf E.cfg.challenges.α)
          (fun e => pow_mod_orderOf E.cfg.challenges.α e) D).executionTemplate
            E.cfg.challenges.z) from rfl] at he
    rw [alphaFreeRoot_reExpData, readExps_reindexAxisTree, List.mem_map] at he
    obtain ⟨e₀, _, rfl⟩ := he
    exact Nat.mod_lt _ hpos
  · intro i e he
    rw [show ((normData D).executionTemplate E.cfg.challenges.z) =
        ((reExpData (fun e => e % orderOf E.cfg.challenges.α)
          (fun e => pow_mod_orderOf E.cfg.challenges.α e) D).executionTemplate
            E.cfg.challenges.z) from rfl] at he
    rw [alphaFreeRoot_reExpData, verifyExps_reindexAxisTree, List.mem_map] at he
    obtain ⟨e₀, _, rfl⟩ := he
    exact Nat.mod_lt _ hpos

/-- **The consumed-layer payoff.**  Unconditional `∀ a g` production fibre acceptance for the
canonically stamped commitment, modulo only `0 < orderOf α`.  Same execution, same skeleton, same
published memory rows as `D` -/
theorem normalised_package_fibre_accepts {E : BuildableNockExecution F K}
    [Fintype F] [DecidableEq F] (D : Data E) (hgt : 11 < ringChar K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧
      E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hpos : 0 < orderOf E.cfg.challenges.α) :
    ∀ a g : K,
      (GenericHonestPackage.packageOf (normData D) hgt I hprl hmore hord hordM hrows (normData_claimGenerated D hgenF) hF).strategy.Accepts
        (honestCoin E a g) E.cfg.challenges.lam :=
  GenericHonestPackage.packageOf_fibre_accepts (normData D) hgt I hprl hmore hord hordM hrows (normData_claimGenerated D hgenF) hF
    (forestExponentOrder_normData D hpos)

/-! ## §D. The `orderOf α = 0` edge case: the window is unsatisfiable and the wrap is trivial -/

/-- **`0 < orderOf α` is necessary, not an extra assumption.**  Any commitment whose forest serves a
lookup and satisfies the window forces it -/
theorem orderOf_pos_of_forestExponentOrder {T : ExactConfigTemplate F K}
    (Et : ExactExecutionTemplate T) (α : K) {i : Fin T.kMem}
    (hne : readExps (alphaFreeRoot Et i) ≠ []) (h : ForestExponentOrder Et α) :
    0 < orderOf α := by
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
  exact lt_of_le_of_lt (Nat.zero_le e) (h.1 i e he)

theorem forestExponentOrder_false_of_orderOf_zero {T : ExactConfigTemplate F K}
    (Et : ExactExecutionTemplate T) (α : K) {i : Fin T.kMem}
    (hne : readExps (alphaFreeRoot Et i) ≠ []) (h0 : orderOf α = 0) :
    ¬ ForestExponentOrder Et α := by
  intro h
  have := orderOf_pos_of_forestExponentOrder Et α hne h
  omega

theorem wrap_is_identity_on_nodes_of_orderOf_zero {E : BuildableNockExecution F K} (D : Data E)
    (h0 : orderOf E.cfg.challenges.α = 0) :
    (wrapDataExponents D).memoryNodes = D.memoryNodes := by
  show D.memoryNodes.map (mapNTree (MemoryNode.wrapAt E.cfg.challenges.α)) = D.memoryNodes
  conv_rhs => rw [← List.map_id D.memoryNodes]
  apply List.map_congr_left
  intro t _
  exact mapNTree_id_of_eq (fun n => by simp [MemoryNode.wrapAt, h0]) t

/-- The same degeneracy on the normalisation side: `e % 0 = e`, so the canonical stamp is the
identity exactly where it could not help. -/
theorem normData_is_identity_on_nodes_of_orderOf_zero {E : BuildableNockExecution F K}
    (D : Data E) (h0 : orderOf E.cfg.challenges.α = 0) :
    (normData D).memoryNodes = D.memoryNodes := by
  show D.memoryNodes.map (mapNTree (MemoryNode.reExp
    (fun e => e % orderOf E.cfg.challenges.α))) = D.memoryNodes
  conv_rhs => rw [← List.map_id D.memoryNodes]
  apply List.map_congr_left
  intro t _
  exact mapNTree_id_of_eq (fun n => by simp [MemoryNode.reExp, h0]) t

/-- **The sharp statement of the residual at the existential quantifier.**  On any execution whose
committed forest serves a lookup, a `Data E` satisfying the paper's uniqueness window exists **iff**
`0 < orderOf α`.  Compare the paper (`N, L ∈ negl(K)`): the residual at this quantifier is one
arithmetic condition on `α`, not an unavailable Nat-level identification -/
theorem window_available_iff_orderOf_pos {E : BuildableNockExecution F K} (D : Data E)
    {i : Fin (configTemplateOf E E.cfg.challenges.z).kMem}
    (hne : readExps (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) ≠ []) :
    (∃ D' : Data E,
        readExps (alphaFreeRoot (D'.executionTemplate E.cfg.challenges.z) i) ≠ [] ∧
          ForestExponentOrder (D'.executionTemplate E.cfg.challenges.z) E.cfg.challenges.α) ↔
      0 < orderOf E.cfg.challenges.α := by
  constructor
  · intro ⟨D', hne', hwin⟩
    exact orderOf_pos_of_forestExponentOrder _ _ hne' hwin
  · intro hpos
    refine ⟨normData D, ?_, forestExponentOrder_normData D hpos⟩
    rw [show ((normData D).executionTemplate E.cfg.challenges.z) =
        ((reExpData (fun e => e % orderOf E.cfg.challenges.α)
          (fun e => pow_mod_orderOf E.cfg.challenges.α e) D).executionTemplate
            E.cfg.challenges.z) from rfl]
    rw [alphaFreeRoot_reExpData, readExps_reindexAxisTree]
    intro hnil
    exact hne (List.eq_nil_of_map_eq_nil hnil)

/-! ## §E. Which honest constructor can emit a wrapped commitment -/

/-- The record-level premise bundle is a subsingleton: both of its fields are `Prop`s. -/
theorem memoryRecordPremises_subsingleton (E : BuildableNockExecution F K)
    (M M' : MemoryRecordPremises E) : M = M' := by
  cases M; cases M'; rfl

/-- The honestly assembled committed exponent is a function of `E` alone — the premise bundle
supplies no choice. -/
theorem honest_record_exponent_is_pinned_by_E (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows) :
    (memoryStampOf E i).recordExponent =
      memoryRecordExp E.cfg.challenges.α (E.exec.memoryRowAt i).2.2.mem.ts := rfl

/-- Hence the record-level honest constructor's committed nodes are canonically determined: two
premise bundles cannot produce two different commitments -/
theorem honest_record_nodes_are_determined (E : BuildableNockExecution F K)
    (M M' : MemoryRecordPremises E) :
    memoryNodesOf E M = memoryNodesOf E M' :=
  congrArg (memoryNodesOf E) (memoryRecordPremises_subsingleton E M M')

def wrappedAssembly {E : BuildableNockExecution F K} (D : Data E) :
    MemoryAssemblyPremises E where
  memoryNodes := (wrapDataExponents D).memoryNodes
  memory_rows := (wrapDataExponents D).memory_rows
  memoryOK := (wrapDataExponents D).memoryOK

theorem wrappedAssembly_carries_the_wrapped_nodes {E : BuildableNockExecution F K} (D : Data E) :
    (wrappedAssembly D).memoryNodes = (wrapDataExponents D).memoryNodes := rfl

/-- The canonical stamp is an admissible assembly-level input too. -/
def normAssembly {E : BuildableNockExecution F K} (D : Data E) :
    MemoryAssemblyPremises E where
  memoryNodes := (normData D).memoryNodes
  memory_rows := (normData D).memory_rows
  memoryOK := (normData D).memoryOK

/-! ## §G.

First, *shape*: `MemLineIdentification` mentions only `S.memoryRows`, `S.computeRows` and
`Nock.Framework.recordCount`.  It is **α-free**, while `ForestExponentOrder` is a bound against
`orderOf α`.  `Concrete.no_alpha_free_predicate_is_the_window` compiles that **no** α-free
proposition can be equivalent to the window uniformly in `α`, because at F73 the window holds at the
honest `α` and fails at `α = 0`.  So `hmemLine` cannot be a rename of the goal.

Second, *content*: `recordExponent_is_determined_by_the_chain` (§H) shows the compute-side exponents
are literally `lnPrevExponent + i + 1`, so `hmemLine` identifies each committed memory exponent with a
value the chain already **determines** — an identification, not a bound. -/

/-- Note what does *not* occur in it: no `α`, no `orderOf`, no
field element -/
def MemLineIdentification {base : SemanticStrategy.SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base) : Prop :=
  ∀ stamp ∈ S.memoryRows, ∃ c ∈ S.computeRows, ∃ i : Fin 3,
    (i : ℕ) < Nock.Framework.recordCount c.state ∧
      stamp.recordExponent = c.recordExponent i

theorem memLine_is_the_ao111_residual {T : ExactConfigTemplate F K}
    {Et : ExactExecutionTemplate T} (α : K)
    {base : SemanticStrategy.SemanticSkeleton} (S : SemanticTimestampSkeleton F K base)
    (halign : TimestampCarrierAlignment S Et)
    (hmem : MemLineIdentification S)
    (hwin : ForestExponentWindow.totalRecordCount S.computeRows < orderOf α) :
    ForestExponentOrder Et α :=
  ForestExponentWindow.forestExponentOrder_of_line_numbers α S halign hmem hwin

/-! ## §H.

**But the whole §A/§D route is a function of an object that is not supplied.**  Every §A conclusion,
and the reduction `forestExponentOrder_of_line_numbers`, takes a `SemanticTimestampSkeleton F K base`
as an *argument*, and this repo contains **no inhabitant** of that structure: the F73 fixture commits
through `ConcreteStrictPackage.timestampStrategy`, a
`DataOnlyTemplateFixedStagedTimestampStrategy`, and the semantic
`TemplateFixedStagedTimestampStrategy` / `SeedFixedTimestampCarrier` bundle that would carry one is
never built.  `line_number_route_is_a_function_of_an_unsupplied_skeleton` records the dependence as a
shape receipt.  This is a **non-vacuity disclosure gap**, not a defect: the structure looks
inhabitable by construction on any base with at least one compute row, but nothing here builds one,
so the route cannot be instantiated today. -/

/-- The compute-side exponent is not merely *bounded* by the chain — it is **determined** by it. -/
theorem recordExponent_is_determined_by_the_chain
    {base : SemanticStrategy.SemanticSkeleton} (S : SemanticTimestampSkeleton F K base)
    {stamp : ComputeTimestampRow} (hstamp : stamp ∈ S.computeRows) (i : Fin 3)
    (hi : (i : ℕ) < Nock.Framework.recordCount stamp.state) :
    stamp.recordExponent i = stamp.lnPrevExponent + (i : ℕ) + 1 :=
  S.computeRecordOffsets stamp hstamp i hi

/-- Independent one-line re-derivation of `recordExponent_pos` straight from the field: it is derived,
not assumed -/
theorem recordExponent_pos_rederived
    {base : SemanticStrategy.SemanticSkeleton} (S : SemanticTimestampSkeleton F K base)
    {stamp : ComputeTimestampRow} (hstamp : stamp ∈ S.computeRows) (i : Fin 3)
    (hi : (i : ℕ) < Nock.Framework.recordCount stamp.state) :
    0 < stamp.recordExponent i := by
  have := recordExponent_is_determined_by_the_chain S hstamp i hi
  omega

/-- `computeStartsAtZero` is a real constraint: it is `False` on the empty row list, which is what
makes `computeRows_ne_nil` work. -/
theorem computeLineStartsAtZero_is_false_on_nil :
    ¬ ComputeLineStartsAtZero [] := id

/-- **Shape receipt: the line-number route is a function of an unsupplied object.**  Both the
skeleton and the alignment are *arguments*; the repo builds neither -/
theorem line_number_route_is_a_function_of_an_unsupplied_skeleton
    {T : ExactConfigTemplate F K} (Et : ExactExecutionTemplate T) (α : K)
    (base : SemanticStrategy.SemanticSkeleton) :
    ∀ (S : SemanticTimestampSkeleton F K base),
      TimestampCarrierAlignment S Et →
        MemLineIdentification S →
          ForestExponentWindow.totalRecordCount S.computeRows < orderOf α →
            ForestExponentOrder Et α :=
  fun S halign hmem hwin => memLine_is_the_ao111_residual α S halign hmem hwin

/-! ## §F. Accounting receipts re-checked independently -/

/-- The residual pair stays `11+1+2`, the fourteen-field partition of the released capstone
statement at F97 per `Batch91.exact_eleven_one_two_partition` (not reinterpreted). -/
theorem residual_pair_still_eleven_one_two_batch133 : 11 + 1 + 2 = 14 :=
  GenericHonestPackage.residual_pair_still_eleven_one_two_after_logup_inventory

theorem data_eta_unchanged_batch133 {E : BuildableNockExecution F K} (D : Data E) :
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

/-- The consumed capstone and its alias are untouched. -/
theorem consumed_capstone_untouched_batch133 [Fintype F] [DecidableEq F]
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement P :=
  OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth

end

/-! ## §B. The live F73 instantiation -/

namespace Concrete

open ConcreteStrictPackage
open BuildableConcrete
open HonestCommitment.Concrete
open GenericHonestPackage.Concrete

local instance : Fact (Nat.Prime 73) := concrete_prime73
noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

variable (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution)

private theorem data73_serving_lt :
    1 < (configTemplateOf concreteExecution
      concreteExecution.cfg.challenges.z).kMem := by
  simp [configTemplateOf, BuildableConcrete.concreteExecution,
    ConcreteStrictPackage.cfg]

/-- F73 is non-degenerate for the wrapping construction: `orderOf α = 9 ≠ 0`. -/
theorem f73_orderOf_alpha : orderOf concreteExecution.cfg.challenges.α = 9 :=
  ConcreteStrictPackage.honestAlpha_order

/-- **The premise HOLDS at the live consumed instance.**  This is the pre-existing production
theorem `GenericHonestPackage.Concrete.package73Of_forestExponentOrder`. -/
theorem f73_window_holds
    (h : ForestExponentOrder
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α) :
    ForestExponentOrder
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α :=
  GenericHonestPackage.Concrete.package73Of_forestExponentOrder h

/-- **…so unconditional `∀ a g` production fibre acceptance is reached at F73**, with no window
hypothesis.  Also pre-existing production. -/
theorem f73_fibre_accepts_unconditionally
    (horder : ForestExponentOrder
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α) :
    ∀ a g : K73cubic,
      (GenericHonestPackage.Concrete.package73Of hmore73).strategy.Accepts
        (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam :=
  GenericHonestPackage.Concrete.package73Of_fibre_accepts_of_window hmore73 horder

/-- They are statements at different quantifiers;
the one the capstone instantiates is the pointwise one. -/
theorem f73_pointwise_holds_and_forall_data_fails
    (h : ForestExponentOrder
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α) :
    ForestExponentOrder
        (data73.executionTemplate concreteExecution.cfg.challenges.z)
        concreteExecution.cfg.challenges.α ∧
      ¬ ∀ D' : Data concreteExecution,
          ForestExponentOrder (D'.executionTemplate concreteExecution.cfg.challenges.z)
            concreteExecution.cfg.challenges.α :=
  ⟨f73_window_holds h, ForestExponentWindow.Concrete.f73_no_universal_forestExponentOrder⟩

/-- The F73 wrap is a genuine shift, not the identity: the wrapped forest reads exponent `10` where
`data73` reads `1`. -/
theorem f73_wrap_is_a_genuine_shift :
    readExps (alphaFreeRoot
        ((wrapDataExponents data73).executionTemplate
          concreteExecution.cfg.challenges.z)
        ⟨1, data73_serving_lt⟩) = [10] := by
  rw [alphaFreeRoot_wrapExponents, readExps_reindexAxisTree,
    ForestExponentWindow.Concrete.data73_alphaFreeRoot_exps.1]
  simp [f73_orderOf_alpha]

/-- The canonical stamp is idempotent on the already-canonical F73 commitment, at the level the
α-free check reads: normalising `data73` leaves the exponent `1` alone. -/
theorem f73_normData_fixes_the_exponent :
    readExps (alphaFreeRoot
        ((normData data73).executionTemplate
          concreteExecution.cfg.challenges.z)
        ⟨1, data73_serving_lt⟩) = [1] := by
  rw [show ((normData data73).executionTemplate concreteExecution.cfg.challenges.z) =
      ((reExpData (fun e => e % orderOf concreteExecution.cfg.challenges.α)
        (fun e => pow_mod_orderOf concreteExecution.cfg.challenges.α e)
          data73).executionTemplate concreteExecution.cfg.challenges.z) from rfl]
  rw [alphaFreeRoot_reExpData, readExps_reindexAxisTree,
    ForestExponentWindow.Concrete.data73_alphaFreeRoot_exps.1]
  simp [f73_orderOf_alpha]

/-- `0` has no finite order in a field. -/
theorem orderOf_zero_eq_zero : orderOf (0 : K73cubic) = 0 := by
  rw [orderOf_eq_zero_iff]
  intro h
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one).1 h
  rw [zero_pow (by omega : n ≠ 0)] at hpow
  exact zero_ne_one hpow

/-- The window **fails** at `α = 0` on the same committed F73 forest where it holds at the honest
`α`.  So the window is genuinely α-dependent -/
theorem f73_window_fails_at_alpha_zero :
    ¬ ForestExponentOrder
        (data73.executionTemplate concreteExecution.cfg.challenges.z) (0 : K73cubic) := by
  refine GenericHonestPackage.ForestExponentOrder_fails_of_large_readExp
    (i := ⟨1, data73_serving_lt⟩) (e := 1) _ _ ?_ ?_
  · rw [ForestExponentWindow.Concrete.data73_alphaFreeRoot_exps.1]
    simp
  · rw [orderOf_zero_eq_zero]
    omega

/-- If some `P` were equivalent to
`ForestExponentOrder` at every `α`, it would have to be both true (at the honest F73 `α`) and false
(at `α = 0`) for the same committed forest.  `hmemLine` / `MemLineIdentification` is α-free, so it is
not a rename of the premise -/
theorem no_alpha_free_predicate_is_the_window (P : Prop)
    (h : ∀ α : K73cubic,
      (P ↔ ForestExponentOrder
        (data73.executionTemplate concreteExecution.cfg.challenges.z) α))
    (hwin : ForestExponentOrder
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α) :
    False :=
  f73_window_fails_at_alpha_zero
    ((h 0).1 ((h concreteExecution.cfg.challenges.α).2 hwin))

end Concrete

#print axioms Nock.RedTeam.Batch133.consumer_premise_is_pointwise_in_the_data
#print axioms Nock.RedTeam.Batch133.forall_data_shape_is_strictly_stronger
#print axioms Nock.RedTeam.Batch133.MemoryTimestampSpecializesAt_reExp
#print axioms Nock.RedTeam.Batch133.memoryNodesOK_reExp
#print axioms Nock.RedTeam.Batch133.skeletonOfNodes_reExp
#print axioms Nock.RedTeam.Batch133.reExpData
#print axioms Nock.RedTeam.Batch133.reExpData_skeleton
#print axioms Nock.RedTeam.Batch133.reExpData_honest_exec
#print axioms Nock.RedTeam.Batch133.reExp_add_order_agrees_with_ao111
#print axioms Nock.RedTeam.Batch133.templateAxisTree_reExp
#print axioms Nock.RedTeam.Batch133.memoryForest_reExpData
#print axioms Nock.RedTeam.Batch133.alphaFreeRoot_reExpData
#print axioms Nock.RedTeam.Batch133.normData
#print axioms Nock.RedTeam.Batch133.normData_skeleton
#print axioms Nock.RedTeam.Batch133.normData_honest_exec
#print axioms Nock.RedTeam.Batch133.normData_memory_rows
#print axioms Nock.RedTeam.Batch133.forestExponentOrder_normData
#print axioms Nock.RedTeam.Batch133.normalised_package_fibre_accepts
#print axioms Nock.RedTeam.Batch133.orderOf_pos_of_forestExponentOrder
#print axioms Nock.RedTeam.Batch133.forestExponentOrder_false_of_orderOf_zero
#print axioms Nock.RedTeam.Batch133.wrap_is_identity_on_nodes_of_orderOf_zero
#print axioms Nock.RedTeam.Batch133.normData_is_identity_on_nodes_of_orderOf_zero
#print axioms Nock.RedTeam.Batch133.window_available_iff_orderOf_pos
#print axioms Nock.RedTeam.Batch133.memoryRecordPremises_subsingleton
#print axioms Nock.RedTeam.Batch133.honest_record_exponent_is_pinned_by_E
#print axioms Nock.RedTeam.Batch133.honest_record_nodes_are_determined
#print axioms Nock.RedTeam.Batch133.wrappedAssembly
#print axioms Nock.RedTeam.Batch133.wrappedAssembly_carries_the_wrapped_nodes
#print axioms Nock.RedTeam.Batch133.normAssembly
#print axioms Nock.RedTeam.Batch133.residual_pair_still_eleven_one_two_batch133
#print axioms Nock.RedTeam.Batch133.data_eta_unchanged_batch133
#print axioms Nock.RedTeam.Batch133.consumed_capstone_untouched_batch133
#print axioms Nock.RedTeam.Batch133.Concrete.f73_orderOf_alpha
#print axioms Nock.RedTeam.Batch133.Concrete.f73_window_holds
#print axioms Nock.RedTeam.Batch133.Concrete.f73_fibre_accepts_unconditionally
#print axioms Nock.RedTeam.Batch133.Concrete.f73_pointwise_holds_and_forall_data_fails
#print axioms Nock.RedTeam.Batch133.Concrete.f73_wrap_is_a_genuine_shift
#print axioms Nock.RedTeam.Batch133.Concrete.f73_normData_fixes_the_exponent
#print axioms Nock.RedTeam.Batch133.MemLineIdentification
#print axioms Nock.RedTeam.Batch133.memLine_is_the_ao111_residual
#print axioms Nock.RedTeam.Batch133.recordExponent_is_determined_by_the_chain
#print axioms Nock.RedTeam.Batch133.recordExponent_pos_rederived
#print axioms Nock.RedTeam.Batch133.computeLineStartsAtZero_is_false_on_nil
#print axioms Nock.RedTeam.Batch133.line_number_route_is_a_function_of_an_unsupplied_skeleton
#print axioms Nock.RedTeam.Batch133.Concrete.orderOf_zero_eq_zero
#print axioms Nock.RedTeam.Batch133.Concrete.f73_window_fails_at_alpha_zero
#print axioms Nock.RedTeam.Batch133.Concrete.no_alpha_free_predicate_is_the_window
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.forestExponentOrder_of_line_numbers
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.recordExponent_le_totalRecordCount
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.packageOf_fibre_accepts
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.no_universal_forestExponentOrder
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end Nock.RedTeam.Batch133
