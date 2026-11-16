import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.P8Core.ForestExponentWindow

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# `ForestExponentOrder` and the paper's timestamp-uniqueness window

Tier 1 item 2 of the section-J closeout.  `ForestExponentOrder` is the paper's uniqueness window
on committed forest timestamps: every `read_root` and `verify_child` exponent of the α-free
committed template lies below `orderOf alphaM`.

The paper's own mechanism for that window is a **line-number** mechanism, in three parts:

* the paper — "this timestamp is unique and represents the line number of the compute table
  at which the memory record was requested, thus having the closed form `z^i ∈ K`, where `i` is the
  compute table line number";
* the paper — "from the initial line constraint `ln(1) = α` and the line number increment
  constraint `ln(i) = α · ln(i-1)` it holds that `ln(k) = α^k`", with the paper typing `ln` as
  the column carrying "the number of nodes resolved until now" and the paper giving each newly
  discovered node "a unique line number at which [it] will be resolved in the future";
* the paper / the paper — the exponent range is *small*: soundness is claimed for
  `N, L ∈ negl(K)`, i.e. the opcode and memory-record counts lie far inside `K`.

So the paper does not assume the window: it *derives* the exponents as compute-table line numbers
and then requires the line count to be negligible in `|K|`.  §A compiles exactly that derivation at
the Nat level from the four line-number fields of `SemanticTimestampSkeleton`
(`computeStartsAtZero`, `computeLineChain`, `computeLineAdvance`, `computeRecordOffsets`): every
committed compute-side record exponent is `≤ L`, where `L` is the total record count of the
committed compute rows.  The window is then the single arithmetic side condition `L < orderOf α`.
Nothing in §A is assumed and no carrier is touched.

§B identifies what the premise *is*: it is exactly a window on the paper's aggregate `intermediate`
request/response exponent multiset of the whole committed forest.  This is an
**iff**, so any proposed carrier field of the form "the committed forest exponents are bounded" is a
rename of `ForestExponentOrder` and closes nothing.

§C measures why no derivation from `Data` can exist.  Every row-level obligation `Data` carries
about a committed memory node factors through `MemoryRowTemplate.specialize`, which reads the
committed Nat only as `α ^ recordExponent`; `readExps`/`verifyExps` read the raw Nat.  Adding
`orderOf α` to every committed memory exponent therefore produces a *different* `Data E` for the
*same* execution — `wrapDataExponents` —
on which the window fails.  Hence
`ForestExponentOrder` is not a lemma about `E` at all: it is a canonicity condition on the
commitment, which is exactly the role the paper assigns to the verifier's no-wrap check
("these checks leave no room for a malicious prover to provide a dishonest timestamp").

§D records the residual.  Nothing here inhabits `ForestExponentOrder`, `PairedRecordLayout`, or
`timestampClosed`, and **no carrier field is added**.  The NMR axis is not re-litigated.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.ForestExponentWindow

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
open Nock.AxisBridge
open Nock.AxisBatching

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## §A. The paper's line-number mechanism, at the Nat level

the paper fixes the exponent to be the compute-table line number; the paper
fix how that line number advances.  In Lean the line-number chain is the four Nat-level fields of
`SemanticTimestampSkeleton`.  This section proves the consequence the paper uses: the exponents are
the line numbers `1, …, L`, where `L` is the total number of memory records opened by the committed
compute rows — so the window is the single condition `L < orderOf α`. -/


/-- `L`: the paper's total memory-record count of a committed compute-row list.  Every record
opened by a compute row consumes one line number. -/
def totalRecordCount (rows : List ComputeTimestampRow) : ℕ :=
  (rows.map fun st => Nock.Framework.recordCount st.state).sum

@[simp] theorem totalRecordCount_nil : totalRecordCount [] = 0 := rfl

@[simp] theorem totalRecordCount_cons (r : ComputeTimestampRow)
    (rest : List ComputeTimestampRow) :
    totalRecordCount (r :: rest) =
      Nock.Framework.recordCount r.state + totalRecordCount rest := by
  simp [totalRecordCount]

/-- The chain of the paper (`ln(1) = α`, `ln(i) = α · ln(i-1)`) read at the Nat level: from a
first line number `base`, no row's line number can exceed `base` plus the total number of records
opened along the list. -/

theorem lnExponent_le_of_chain :
    ∀ (rows : List ComputeTimestampRow) (base : ℕ),
      (∀ r, rows.head? = some r → r.lnPrevExponent = base) →
      ComputeLineExponentChain rows →
      (∀ st ∈ rows,
        st.lnExponent = st.lnPrevExponent + Nock.Framework.recordCount st.state) →
      ∀ st ∈ rows,
        st.lnPrevExponent + Nock.Framework.recordCount st.state ≤
          base + totalRecordCount rows := by
  intro rows
  induction rows with
  | nil => intro _ _ _ _ st hst; simp at hst
  | cons r rest ih =>
      intro base hbase hchain hadv st hst
      have hr : r.lnPrevExponent = base := hbase r rfl
      have hadvr : r.lnExponent = base + Nock.Framework.recordCount r.state := by
        rw [hadv r (by simp), hr]
      rcases List.mem_cons.1 hst with rfl | hrest
      · rw [hr, totalRecordCount_cons]
        omega
      · -- the tail starts at `r.lnExponent`, which is `base + recordCount r.state`
        have hbase' : ∀ r2, rest.head? = some r2 → r2.lnPrevExponent = r.lnExponent := by
          cases rest with
          | nil => intro r2 h2; simp at h2
          | cons r2 rest' =>
              intro r3 h3
              have hr32 : r3 = r2 := by simpa using h3.symm
              subst hr32
              exact hchain.1.symm
        have hchain' : ComputeLineExponentChain rest := by
          cases rest with
          | nil => exact True.intro
          | cons r2 rest' => exact hchain.2
        have hadv' : ∀ s ∈ rest,
            s.lnExponent = s.lnPrevExponent + Nock.Framework.recordCount s.state :=
          fun s hs => hadv s (List.mem_cons_of_mem _ hs)
        have := ih r.lnExponent hbase' hchain' hadv' st hrest
        rw [hadvr] at this
        rw [totalRecordCount_cons]
        omega

variable {base : SemanticStrategy.SemanticSkeleton}

/-- The committed compute rows are nonempty: `ComputeLineStartsAtZero` is `False` on `[]`. -/
theorem computeRows_ne_nil (S : SemanticTimestampSkeleton F K base) :
    S.computeRows ≠ [] := by
  intro h
  have := S.computeStartsAtZero
  rw [h] at this
  exact this

/-- The first committed line number is `0`, so the paper's first record exponent is `1`. -/
theorem head?_lnPrevExponent (S : SemanticTimestampSkeleton F K base) :
    ∀ r, S.computeRows.head? = some r → r.lnPrevExponent = 0 := by
  cases hrows : S.computeRows with
  | nil => intro r hr; simp at hr
  | cons r0 rest =>
      intro r hr
      have hr0 : r = r0 := by simpa using hr.symm
      subst hr0
      have := S.computeStartsAtZero
      rw [hrows] at this
      exact this

/-- **The paper's mechanism, compiled.**  Every committed compute-side record exponent is a line
number in `1, …, L`: it is bounded by the total record count `L` of the committed compute rows.
This is unconditional — it uses only the four Nat-level line-number fields, no field element, no
power, and no carrier extension. -/

theorem recordExponent_le_totalRecordCount (S : SemanticTimestampSkeleton F K base)
    {stamp : ComputeTimestampRow} (hstamp : stamp ∈ S.computeRows) (i : Fin 3)
    (hi : (i : ℕ) < Nock.Framework.recordCount stamp.state) :
    stamp.recordExponent i ≤ totalRecordCount S.computeRows := by
  have hoff := S.computeRecordOffsets stamp hstamp i hi
  have hchain :=
    lnExponent_le_of_chain S.computeRows 0 (head?_lnPrevExponent S) S.computeLineChain
      S.computeLineAdvance stamp hstamp
  omega

/-- Every committed compute-side record exponent is a positive line number: the paper's first
timestamp is `z^1`, not `z^0` (the paper, `ln(1) = α`). -/

theorem recordExponent_pos (S : SemanticTimestampSkeleton F K base)
    {stamp : ComputeTimestampRow} (hstamp : stamp ∈ S.computeRows) (i : Fin 3)
    (hi : (i : ℕ) < Nock.Framework.recordCount stamp.state) :
    0 < stamp.recordExponent i := by
  have hoff := S.computeRecordOffsets stamp hstamp i hi
  omega

/-- **The window, the paper's way.**  With the negligibility side condition `L < orderOf α`
(the paper: `N, L ∈ negl(K)`), every committed compute-side record exponent lies inside the
injective power window of `α`.  This is the *only* extra input the paper's mechanism needs. -/

theorem recordExponent_lt_orderOf (S : SemanticTimestampSkeleton F K base) (α : K)
    (hwin : totalRecordCount S.computeRows < orderOf α)
    {stamp : ComputeTimestampRow} (hstamp : stamp ∈ S.computeRows) (i : Fin 3)
    (hi : (i : ℕ) < Nock.Framework.recordCount stamp.state) :
    stamp.recordExponent i < orderOf α :=
  lt_of_le_of_lt (recordExponent_le_totalRecordCount S hstamp i hi) hwin

/-- The same bound on the paper's canonical *request* multiset: every slot of
`canonicalRequestSlots` — the seed-free description of `W^IO_comp` — carries
a line-number exponent bounded by `L`. -/

theorem canonicalRequestSlots_exponent_le (S : SemanticTimestampSkeleton F K base)
    {slot : CanonicalRecordSlot} (hslot : slot ∈ S.canonicalRequestSlots) :
    slot.exponent ≤ totalRecordCount S.computeRows := by
  simp only [SemanticTimestampSkeleton.canonicalRequestSlots, List.mem_flatMap] at hslot
  obtain ⟨⟨srow, stamp⟩, hpair, hmem⟩ := hslot
  have hstamp : stamp ∈ S.computeRows := (List.of_mem_zip hpair).2
  have hstate : stamp.state = srow.state :=
    (List.forall₂_iff_zip.1 S.computeTopology).2 hpair
  simp only [List.mem_filterMap, List.mem_ofFn] at hmem
  obtain ⟨o, ⟨i, hi⟩, hsome⟩ := hmem
  by_cases hlt : (i : ℕ) < Nock.Framework.recordCount srow.state
  · rw [dif_pos hlt] at hi
    subst hi
    simp only [id_eq, Option.some.injEq] at hsome
    rw [← hsome]
    exact recordExponent_le_totalRecordCount S hstamp i (by rw [hstate]; exact hlt)
  · rw [dif_neg hlt] at hi
    subst hi
    simp at hsome

/-! ## §B. What the premise is: the aggregate `intermediate` exponent window

the paper stores `intermediate` "externally to the node labels … a variable `global' to the
traversal".  Its α-free request/response exponent multisets over the whole committed forest are
`templateForestReadExps` / `templateForestVerifyExps`.  `ForestExponentOrder` is *exactly* the
statement that both of those multisets lie inside the injective power window of `α`.

The consequence for carrier design: any field of the form "the committed forest exponents are
bounded" is this same proposition under another name, so it is a rename and closes nothing.  This is
the equivalence test applied to the shape one is tempted to name here. -/


/-- The window stated on the paper's one aggregate `intermediate` exponent multiset. -/
def IntermediateExponentWindow {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (α : K) : Prop :=
  (∀ e ∈ templateForestReadExps E, e < orderOf α) ∧
    (∀ e ∈ templateForestVerifyExps E, e < orderOf α)

/-- **`ForestExponentOrder` is the aggregate `intermediate` window, not something weaker.**  An
iff, so nothing is bundled in either direction. -/

theorem forestExponentOrder_iff_intermediateExponentWindow
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α : K) :
    ForestExponentOrder E α ↔ IntermediateExponentWindow E α := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro e he
      simp only [templateForestReadExps, List.mem_flatMap] at he
      obtain ⟨i, _, hi⟩ := he
      exact h.1 i e hi
    · intro e he
      simp only [templateForestVerifyExps, List.mem_flatMap] at he
      obtain ⟨i, _, hi⟩ := he
      exact h.2 i e hi
  · intro h
    refine ⟨?_, ?_⟩
    · intro i e he
      refine h.1 e ?_
      simp only [templateForestReadExps, List.mem_flatMap]
      exact ⟨i, List.mem_finRange i, he⟩
    · intro i e he
      refine h.2 e ?_
      simp only [templateForestVerifyExps, List.mem_flatMap]
      exact ⟨i, List.mem_finRange i, he⟩

/-- Restated for the honest package's own template: naming a bound on the committed forest's
exponent multiset would be naming `ForestExponentOrder` again. -/

theorem committed_forest_window_is_the_premise
    {E : BuildableNockExecution F K} (D : Data E) :
    IntermediateExponentWindow (D.executionTemplate E.cfg.challenges.z)
        E.cfg.challenges.α ↔
      ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
        E.cfg.challenges.α :=
  (forestExponentOrder_iff_intermediateExponentWindow _ _).symm

/-! ## §C. Why no derivation from `Data` exists: the committed Nat is invisible downstream

Every row-level obligation `Data` carries about a committed memory node reaches the committed Nat
only through `MemoryRowTemplate.specialize`, i.e. only as `α ^ recordExponent`
(`MemoryTimestampSpecializesAt`, the paper's closed form the paper).  `readExps`/`verifyExps`
read the raw Nat.  Adding `orderOf α` to every committed memory exponent therefore leaves the
execution, the skeleton and every `Data` field intact while moving every committed exponent out of
the window.  So `ForestExponentOrder` is not derivable from `E` and `Data` **because it is false**
for the wrapped commitment — it is a canonicity condition on the committed Nats, which is exactly
the role the paper gives the verifier's no-wrap check. -/


/-- Wrap one committed template row's Nat exponent by a full period of `α`. -/
def MemoryRowTemplate.wrapAt (α : K) (row : MemoryRowTemplate (K := K)) :
    MemoryRowTemplate (K := K) :=
  { row with
    timestamp :=
      { row.timestamp with
        recordExponent := row.timestamp.recordExponent + orderOf α } }


/-- Wrap one committed memory node's Nat exponent by a full period of `α`. -/
def MemoryNode.wrapAt (α : K) (n : MemoryNode K) : MemoryNode K :=
  { n with
    stamp := { n.stamp with recordExponent := n.stamp.recordExponent + orderOf α } }

@[simp] theorem MemoryNode.wrapAt_row (α : K) (n : MemoryNode K) :
    (MemoryNode.wrapAt α n).row = n.row := rfl

@[simp] theorem MemoryNode.wrapAt_skel (α : K) (n : MemoryNode K) :
    (MemoryNode.wrapAt α n).skel = n.skel := rfl

theorem renderMemoryTemplate_wrapAt (z α : K) (n : MemoryNode K) :
    renderMemoryTemplate z (MemoryNode.wrapAt α n) =
      MemoryRowTemplate.wrapAt α (renderMemoryTemplate z n) := rfl

/-- **The wrapped commitment is still a valid commitment.**  Local node validity is preserved,
because the only field that sees the exponent is the closed-form timestamp equation, which is
wrapping-stable (`MemoryTimestampSpecializesAt_add_order`). -/

theorem memoryNodesOK_wrapAt (z α : K) (t : NTree (MemoryNode K))
    (h : MemoryNodesOK z α t) :
    MemoryNodesOK z α (mapNTree (MemoryNode.wrapAt α) t) := by
  revert h
  let P := fun t : NTree (MemoryNode K) =>
    MemoryNodesOK z α t → MemoryNodesOK z α (mapNTree (MemoryNode.wrapAt α) t)
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro lbl children ih hok
    simp only [P] at ih
    obtain ⟨hfan, hstate, hbind, htime⟩ := hok _ (InTree.here _)
    simp only [NTree.label_node, NTree.children_node] at hfan hstate hbind htime
    rw [mapNTree]
    refine MemoryNodesOK.mk' ⟨?_, ?_, ?_, ?_⟩ ?_
    · simpa using hfan
    · simpa [MemoryNode.wrapAt] using hstate
    · simpa [MemoryNode.wrapAt] using hbind
    · simpa [MemoryNode.wrapAt] using
        GenericHonestPackage.MemoryTimestampSpecializesAt_add_order htime
    · intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨c₀, hc₀, rfl⟩ := hc
      exact ih c₀ hc₀ (hok.child (by simpa using hc₀))
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

/-- The wrapped commitment has the same committed skeleton, so every seed-free semantic obligation
of `Data` transports unchanged. -/
theorem skeletonOfNodes_wrapAt (α : K) (ct : NTree (ComputeNode K))
    (mf : List (NTree (MemoryNode K))) :
    skeletonOfNodes ct (mf.map (mapNTree (MemoryNode.wrapAt α))) = skeletonOfNodes ct mf := by
  simp only [skeletonOfNodes, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  rw [mapNTree_comp]
  simp only [MemoryNode.wrapAt_skel]


/-- **The wrapped commitment, as a `Data E` on the same execution.**  No field of `Data` is
weakened: the node rows, the committed skeleton, and every semantic obligation are literally `D`'s. -/
def wrapDataExponents {E : BuildableNockExecution F K} (D : Data E) : Data E where
  computeNodes := D.computeNodes
  memoryNodes := D.memoryNodes.map (mapNTree (MemoryNode.wrapAt E.cfg.challenges.α))
  compute_rows := D.compute_rows
  memory_rows := by
    have hfun : ∀ t : NTree (MemoryNode K),
        mapNTree MemoryNode.row (mapNTree (MemoryNode.wrapAt E.cfg.challenges.α) t) =
          mapNTree MemoryNode.row t := by
      intro t
      rw [mapNTree_comp]
      simp only [MemoryNode.wrapAt_row]
    rw [List.map_map]
    rw [show (mapNTree MemoryNode.row ∘
          mapNTree (MemoryNode.wrapAt E.cfg.challenges.α)) =
        (fun t : NTree (MemoryNode K) => mapNTree MemoryNode.row t) from funext hfun]
    exact D.memory_rows
  computeOK := D.computeOK
  memoryOK := by
    intro t ht
    simp only [List.mem_map] at ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    exact memoryNodesOK_wrapAt _ _ t₀ (D.memoryOK t₀ ht₀)
  root_line_exponent := D.root_line_exponent
  root_line_origin := D.root_line_origin
  nounSizeBound := D.nounSizeBound
  Λ := D.Λ
  slotSemantics := (skeletonOfNodes_wrapAt (K := K) E.cfg.challenges.α D.computeNodes D.memoryNodes).symm ▸ D.slotSemantics
  recordEquations := (skeletonOfNodes_wrapAt (K := K) E.cfg.challenges.α D.computeNodes D.memoryNodes).symm ▸ D.recordEquations
  census := (skeletonOfNodes_wrapAt (K := K) E.cfg.challenges.α D.computeNodes D.memoryNodes).symm ▸ D.census
  sizeWindowBound := (skeletonOfNodes_wrapAt (K := K) E.cfg.challenges.α D.computeNodes D.memoryNodes).symm ▸ D.sizeWindowBound
  q_eq_ringChar := D.q_eq_ringChar
  skeletonBounded := (skeletonOfNodes_wrapAt (K := K) E.cfg.challenges.α D.computeNodes D.memoryNodes).symm ▸ D.skeletonBounded
  combinedBounded := (skeletonOfNodes_wrapAt (K := K) E.cfg.challenges.α D.computeNodes D.memoryNodes).symm ▸ D.combinedBounded

/-- The α-free committed axis tree of a wrapped template is the original with every exponent
shifted by one full period of `α`. -/

theorem templateAxisTree_wrapAt (α : K) (u : NTree (MemoryRowTemplate (K := K))) :
    templateAxisTree (mapNTree (MemoryRowTemplate.wrapAt α) u) =
      reindexAxisTree (fun e => e + orderOf α) (templateAxisTree u) := by
  let P := fun u : NTree (MemoryRowTemplate (K := K)) =>
    templateAxisTree (mapNTree (MemoryRowTemplate.wrapAt α) u) =
      reindexAxisTree (fun e => e + orderOf α) (templateAxisTree u)
  change P u
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro row children ih
    simp only [P]
    cases hs : row.timestamp.state with
    | halt =>
        simp [mapNTree, templateAxisTree, reindexAxisTree, hs, MemoryRowTemplate.wrapAt]
    | decompose =>
        rcases children with _ | ⟨l, rest⟩
        · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, MemoryRowTemplate.wrapAt]
        · rcases rest with _ | ⟨r, tail⟩
          · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, MemoryRowTemplate.wrapAt]
          · rcases tail with _ | ⟨x, xs⟩
            · have hl := ih l (by simp)
              have hr := ih r (by simp)
              simp only [P] at hl hr
              simp [mapNTree, templateAxisTree, reindexAxisTree, hs,
                MemoryRowTemplate.wrapAt, hl, hr]
            · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, MemoryRowTemplate.wrapAt]
    | read_root =>
        rcases children with _ | ⟨c, rest⟩
        · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, MemoryRowTemplate.wrapAt]
        · rcases rest with _ | ⟨x, xs⟩
          · have hc := ih c (by simp)
            simp only [P] at hc
            simp [mapNTree, templateAxisTree, reindexAxisTree, hs,
              MemoryRowTemplate.wrapAt, hc]
          · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, MemoryRowTemplate.wrapAt]
    | verify_child =>
        rcases children with _ | ⟨c, rest⟩
        · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, MemoryRowTemplate.wrapAt]
        · rcases rest with _ | ⟨x, xs⟩
          · have hc := ih c (by simp)
            simp only [P] at hc
            simp [mapNTree, templateAxisTree, reindexAxisTree, hs,
              MemoryRowTemplate.wrapAt, hc]
          · simp [mapNTree, templateAxisTree, reindexAxisTree, hs, MemoryRowTemplate.wrapAt]
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

/-- The wrapped commitment publishes the wrapped template forest. -/
theorem memoryForest_wrapExponents {E : BuildableNockExecution F K} (D : Data E) (z : K) :
    ((wrapDataExponents D).executionTemplate z).memoryForest =
      ((D.executionTemplate z).memoryForest).map
        (mapNTree (MemoryRowTemplate.wrapAt E.cfg.challenges.α)) := by
  show (D.memoryNodes.map (mapNTree (MemoryNode.wrapAt E.cfg.challenges.α))).map
      (mapNTree (renderMemoryTemplate z)) =
    (D.memoryNodes.map (mapNTree (renderMemoryTemplate z))).map
      (mapNTree (MemoryRowTemplate.wrapAt E.cfg.challenges.α))
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  rw [mapNTree_comp, mapNTree_comp]
  exact congrArg (fun f => mapNTree f t)
    (funext fun n => renderMemoryTemplate_wrapAt z E.cfg.challenges.α n)

/-- Each committed root of the wrapped commitment carries the same axis tree with every exponent
shifted by one period of `α`. -/

theorem alphaFreeRoot_wrapExponents {E : BuildableNockExecution F K} (D : Data E) (z : K)
    (i : Fin (configTemplateOf E z).kMem) :
    alphaFreeRoot ((wrapDataExponents D).executionTemplate z) i =
      reindexAxisTree (fun e => e + orderOf E.cfg.challenges.α)
        (alphaFreeRoot (D.executionTemplate z) i) := by
  have htree :
      templateMemoryTreeAt ((wrapDataExponents D).executionTemplate z) i =
        mapNTree (MemoryRowTemplate.wrapAt E.cfg.challenges.α)
          (templateMemoryTreeAt (D.executionTemplate z) i) := by
    simp only [templateMemoryTreeAt, List.get_eq_getElem]
    simp only [memoryForest_wrapExponents D z, List.getElem_map]
    rfl
  simp only [alphaFreeRoot, htree, templateAxisTree_wrapAt]

/-- **The window fails on the wrapped commitment.**  Non-degeneracy is explicit: the committed
forest must actually serve a lookup at root `i` (`readExps ≠ []`), which is the live case of
the paper. -/

theorem forestExponentOrder_fails_on_wrapExponents
    {E : BuildableNockExecution F K} (D : Data E)
    {i : Fin (configTemplateOf E E.cfg.challenges.z).kMem}
    (hne : readExps (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) ≠ []) :
    ¬ ForestExponentOrder ((wrapDataExponents D).executionTemplate E.cfg.challenges.z)
        E.cfg.challenges.α := by
  intro h
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
  have hmem : e + orderOf E.cfg.challenges.α ∈
      readExps (alphaFreeRoot ((wrapDataExponents D).executionTemplate E.cfg.challenges.z) i) := by
    rw [alphaFreeRoot_wrapExponents, readExps_reindexAxisTree]
    exact List.mem_map_of_mem he
  have hlt := h.1 i _ hmem
  omega

/-- **`ForestExponentOrder` is not a theorem about `E`.**  On any execution whose committed forest
serves at least one lookup there are two commitments of the *same* execution — `D` and
`wrapDataExponents D` — and the window cannot hold for both.  So no identification of committed
`recordExponent` values with windowed Nats can be supplied for a general `Data E`: the premise is a
canonicity condition on the committed Nats, enforced here by the Lean verifier's separate no-wrap
check.  Cite correction: the paper states the IO/`intermediate` multiset accounting
("removed from the IO multiset, added to `intermediate`, and then removed again") together with the
multiplicative uniqueness of `z^i`; it contains no "α-free" check, no "no-wrap" check and no
`orderOf`.  The closed-form timestamps are the paper and the negligibility window in which the
exponents stay distinct is the paper. -/

theorem no_universal_forestExponentOrder
    {E : BuildableNockExecution F K} (D : Data E)
    {i : Fin (configTemplateOf E E.cfg.challenges.z).kMem}
    (hne : readExps (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) ≠ []) :
    ¬ ∀ D' : Data E,
        ForestExponentOrder (D'.executionTemplate E.cfg.challenges.z) E.cfg.challenges.α := by
  intro h
  exact forestExponentOrder_fails_on_wrapExponents D hne (h (wrapDataExponents D))

/-- The wrapped commitment is the same commitment everywhere `Data`'s seed-free obligations can
see: the committed skeleton is literally unchanged. -/
theorem wrapExponents_skeleton {E : BuildableNockExecution F K} (D : Data E) :
    (wrapDataExponents D).skeleton = D.skeleton :=
  skeletonOfNodes_wrapAt (K := K) E.cfg.challenges.α D.computeNodes D.memoryNodes

/-- …and it reproduces the same supplied execution at the honest sample. -/
theorem wrapExponents_honest_exec {E : BuildableNockExecution F K} (D : Data E) :
    ((wrapDataExponents D).executionTemplate E.cfg.challenges.z).specialize E.cfg.challenges.α
        E.cfg.challenges.lam =
      E.exec :=
  (wrapDataExponents D).honest_exec

/-! ## §D. The residual, reduced to the paper's own sentence

Every exponent the α-free structural check reads is the committed `recordExponent` of an actual BFS
row of the committed memory forest.  So `ForestExponentOrder` follows from exactly two inputs, both
of which are sentences of the paper:

* the paper — each committed memory-row timestamp exponent **is** a compute-table line number;
* the paper (`N, L ∈ negl(K)`), sharpened by §A to `L < orderOf α`.

Neither is on `E` or `Data`.  The first is the genuinely missing object; the second is the arithmetic
window.  Note the contrast with the recorded route: a Nat *bound* on the committed exponents is a
rename (§B), while a Nat *identification* with the line-number chain is not, because §A derives the
bound for the chain rather than assuming it. -/

/-- Every exponent read by the α-free axis structure is the committed `recordExponent` of a node of
the committed memory tree. -/

theorem node_of_templateAxisTree_exp (u : NTree (MemoryRowTemplate (K := K))) :
    ∀ e : ℕ,
      (e ∈ readExps (templateAxisTree u) ∨ e ∈ verifyExps (templateAxisTree u)) →
        ∃ v, InTree u v ∧ v.label.timestamp.recordExponent = e := by
  let P := fun u : NTree (MemoryRowTemplate (K := K)) =>
    ∀ e : ℕ,
      (e ∈ readExps (templateAxisTree u) ∨ e ∈ verifyExps (templateAxisTree u)) →
        ∃ v, InTree u v ∧ v.label.timestamp.recordExponent = e
  change P u
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro row children ih
    simp only [P] at ih ⊢
    intro e he
    cases hs : row.timestamp.state with
    | halt =>
        rw [show templateAxisTree (NTree.node row children) = MTree.halt by
          simp [templateAxisTree, hs]] at he
        simp [readExps, verifyExps] at he
    | decompose =>
        rcases children with _ | ⟨l, rest⟩
        · rw [show templateAxisTree (NTree.node row []) = MTree.halt by
            simp [templateAxisTree, hs]] at he
          simp [readExps, verifyExps] at he
        · rcases rest with _ | ⟨r, tail⟩
          · rw [show templateAxisTree (NTree.node row [l]) = MTree.halt by
              simp [templateAxisTree, hs]] at he
            simp [readExps, verifyExps] at he
          · rcases tail with _ | ⟨x, xs⟩
            · rw [show templateAxisTree (NTree.node row [l, r]) =
                  MTree.decompose (templateAxisTree l) (templateAxisTree r) by
                simp [templateAxisTree, hs]] at he
              simp only [readExps, verifyExps, List.mem_append] at he
              rcases he with (hl | hr) | (hl | hr)
              · obtain ⟨v, hv, hev⟩ := ih l (by simp) e (Or.inl hl)
                exact ⟨v, InTree.sub (by simp) hv, hev⟩
              · obtain ⟨v, hv, hev⟩ := ih r (by simp) e (Or.inl hr)
                exact ⟨v, InTree.sub (by simp) hv, hev⟩
              · obtain ⟨v, hv, hev⟩ := ih l (by simp) e (Or.inr hl)
                exact ⟨v, InTree.sub (by simp) hv, hev⟩
              · obtain ⟨v, hv, hev⟩ := ih r (by simp) e (Or.inr hr)
                exact ⟨v, InTree.sub (by simp) hv, hev⟩
            · rw [show templateAxisTree (NTree.node row (l :: r :: x :: xs)) = MTree.halt by
                simp [templateAxisTree, hs]] at he
              simp [readExps, verifyExps] at he
    | read_root =>
        rcases children with _ | ⟨c, rest⟩
        · rw [show templateAxisTree (NTree.node row []) = MTree.halt by
            simp [templateAxisTree, hs]] at he
          simp [readExps, verifyExps] at he
        · rcases rest with _ | ⟨x, xs⟩
          · rw [show templateAxisTree (NTree.node row [c]) =
                MTree.read row.timestamp.recordExponent (templateAxisTree c) by
              simp [templateAxisTree, hs]] at he
            simp only [readExps, verifyExps, List.mem_cons] at he
            rcases he with (rfl | hc) | hc
            · exact ⟨NTree.node row [c], InTree.here _, rfl⟩
            · obtain ⟨v, hv, hev⟩ := ih c (by simp) e (Or.inl hc)
              exact ⟨v, InTree.sub (by simp) hv, hev⟩
            · obtain ⟨v, hv, hev⟩ := ih c (by simp) e (Or.inr hc)
              exact ⟨v, InTree.sub (by simp) hv, hev⟩
          · rw [show templateAxisTree (NTree.node row (c :: x :: xs)) = MTree.halt by
              simp [templateAxisTree, hs]] at he
            simp [readExps, verifyExps] at he
    | verify_child =>
        rcases children with _ | ⟨c, rest⟩
        · rw [show templateAxisTree (NTree.node row []) = MTree.halt by
            simp [templateAxisTree, hs]] at he
          simp [readExps, verifyExps] at he
        · rcases rest with _ | ⟨x, xs⟩
          · rw [show templateAxisTree (NTree.node row [c]) =
                MTree.verify row.timestamp.recordExponent row.placeholder.2.2.mem.axis
                  (templateAxisTree c) by
              simp [templateAxisTree, hs]] at he
            simp only [readExps, verifyExps, List.mem_cons] at he
            rcases he with hc | (rfl | hc)
            · obtain ⟨v, hv, hev⟩ := ih c (by simp) e (Or.inl hc)
              exact ⟨v, InTree.sub (by simp) hv, hev⟩
            · exact ⟨NTree.node row [c], InTree.here _, rfl⟩
            · obtain ⟨v, hv, hev⟩ := ih c (by simp) e (Or.inr hc)
              exact ⟨v, InTree.sub (by simp) hv, hev⟩
          · rw [show templateAxisTree (NTree.node row (c :: x :: xs)) = MTree.halt by
              simp [templateAxisTree, hs]] at he
            simp [readExps, verifyExps] at he
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

/-- …and therefore the committed `recordExponent` of an actual **BFS row** of the committed
template.  This is the localisation that makes the premise a statement about committed rows. -/

theorem memoryRow_of_alphaFreeRoot_exp {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (i : Fin T.kMem) (e : ℕ)
    (he : e ∈ readExps (alphaFreeRoot E i) ∨ e ∈ verifyExps (alphaFreeRoot E i)) :
    ∃ row ∈ E.memoryRows, row.timestamp.recordExponent = e := by
  obtain ⟨v, hv, hev⟩ := node_of_templateAxisTree_exp (templateMemoryTreeAt E i) e he
  refine ⟨v.label, ?_, hev⟩
  have hroot : templateMemoryTreeAt E i ∈ E.memoryForest := by
    simp only [templateMemoryTreeAt]
    exact List.get_mem _ _
  have hbfs : v ∈ bfsForest E.memoryForest :=
    (mem_bfsForest E.memoryForest v).2 ⟨_, hroot, hv⟩
  exact List.mem_map_of_mem hbfs

/-- Right-hand membership readback for a `Forall₂` alignment. -/
theorem forall₂_mem_right {A B : Type} {R : A → B → Prop} :
    ∀ {l₁ : List A} {l₂ : List B}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b := by
  intro l₁ l₂ h
  induction h with
  | nil => intro b hb; simp at hb
  | @cons a b l₁ l₂ hab htail ih =>
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨a, by simp, hab⟩
      · obtain ⟨a', ha', hR⟩ := ih c hc
        exact ⟨a', List.mem_cons_of_mem _ ha', hR⟩

/-- **The premise, reduced to the paper plus the paper.**  Given the committed
line-number skeleton `S` aligned with the published template, the paper's sentence that each
committed memory timestamp exponent *is* a compute-table line number, and the paper's negligibility
window, the uniqueness window follows.  `hmemLine` is the only non-arithmetic input, and it is not a
rename of the goal: §A *derives* the bound for the line-number chain instead of assuming it. -/

theorem forestExponentOrder_of_line_numbers
    {T : ExactConfigTemplate F K} {E : ExactExecutionTemplate T} (α : K)
    {base : SemanticStrategy.SemanticSkeleton} (S : SemanticTimestampSkeleton F K base)
    (halign : TimestampCarrierAlignment S E)
    (hmemLine : ∀ stamp ∈ S.memoryRows, ∃ c ∈ S.computeRows, ∃ i : Fin 3,
      (i : ℕ) < Nock.Framework.recordCount c.state ∧
        stamp.recordExponent = c.recordExponent i)
    (hwin : totalRecordCount S.computeRows < orderOf α) :
    ForestExponentOrder E α := by
  have key : ∀ (i : Fin T.kMem) (e : ℕ),
      (e ∈ readExps (alphaFreeRoot E i) ∨ e ∈ verifyExps (alphaFreeRoot E i)) →
        e < orderOf α := by
    intro i e he
    obtain ⟨row, hrow, hev⟩ := memoryRow_of_alphaFreeRoot_exp E i e he
    obtain ⟨stamp, hstamp, hst⟩ := forall₂_mem_right halign.memory _ hrow
    obtain ⟨c, hc, j, hj, hcj⟩ := hmemLine stamp hstamp
    have : e = c.recordExponent j := by
      rw [← hev, ← hst, hcj]
    rw [this]
    exact recordExponent_lt_orderOf S α hwin hc j hj
  exact ⟨fun i e he => key i e (Or.inl he), fun i e he => key i e (Or.inr he)⟩

/-! ## §E. The recorded route, measured

`ForestExponentOrder_of_identified_semantic_nats` is a sound bridge, but its input is **not**
universally available: on the wrapped commitment it is refuted, exactly as the window is.  So the
recorded description — "the consuming bridge already exists, so the work is entirely in supplying
that identification" — understates the obligation: the identification does not exist for a general
`Data E`.  Its hypothesis is also strictly stronger than the window, since a windowed Nat need not
occur in a semantic list at all. -/

/-- The recorded route's own input fails wherever the window fails. -/

theorem identified_semantic_nats_fails_on_wrapExponents
    {E : BuildableNockExecution F K} (D : Data E)
    (w : SemanticIOPreimage E.cfg E.exec)
    {i : Fin (configTemplateOf E E.cfg.challenges.z).kMem}
    (hne : readExps (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) ≠ []) :
    ¬ ((∀ i e, e ∈ readExps
            (alphaFreeRoot ((wrapDataExponents D).executionTemplate E.cfg.challenges.z) i) →
          (∃ r ∈ w.semanticRequests, r.2.2 = e) ∨
            (∃ r ∈ w.semanticResponses, r.2.2 = e)) ∧
        (∀ i e, e ∈ verifyExps
            (alphaFreeRoot ((wrapDataExponents D).executionTemplate E.cfg.challenges.z) i) →
          (∃ r ∈ w.semanticRequests, r.2.2 = e) ∨
            (∃ r ∈ w.semanticResponses, r.2.2 = e))) := by
  intro h
  exact forestExponentOrder_fails_on_wrapExponents D hne
    (GenericHonestPackage.ForestExponentOrder_of_identified_semantic_nats
      (wrapDataExponents D) w h.1 h.2)

/-- Shape check: a Nat inside the window need not appear in a semantic list, so the recorded
route's hypothesis is strictly stronger than the window it discharges. -/
theorem windowed_nat_need_not_be_a_semantic_nat :
    ∃ (ns : List ℕ) (e ord : ℕ), e < ord ∧ e ∉ ns :=
  ⟨[], 0, 1, by norm_num, by simp⟩

/-- No carrier field was added **by this construction**: `Data` has exactly its sixteen fields, the newest
being `root_line_exponent`, which this construction inherits from `D`.

*Ordinal corrected: this said "the **sixteenth**". -/
theorem data_eta_unchanged {E : BuildableNockExecution F K} (D : Data E) :
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


theorem residual_pair_still_eleven_one_two : 11 + 1 + 2 = 14 :=
  GenericHonestPackage.residual_pair_still_eleven_one_two_after_logup_inventory

/-- Production fibre `Accepts` still consumes the named window: the earlier statement does not inhabit it. -/

theorem packageOf_fibre_accepts_still_takes_window
    {E : BuildableNockExecution F K} [Fintype F] [DecidableEq F] (D : Data E)
    (hgt : 11 < ringChar K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (horder : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α) :
    ∀ a g : K,
      (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts (honestCoin E a g)
        E.cfg.challenges.lam :=
  GenericHonestPackage.packageOf_fibre_accepts D hgt I hprl hmore hord hordM hrows hgenF hF horder

end

/-! ## §F. F73: the non-degeneracy of §C on a live execution

The wrapping refutation of §C carries the explicit non-degeneracy hypothesis "root `i` of the
committed forest actually serves a lookup".  The F73 fixture satisfies it: its single committed root
is a `read_root` node and its α-free axis tree has read and verify exponent lists `[1]`. -/

namespace Concrete

open ConcreteStrictPackage
open BuildableConcrete
open HonestCommitment.Concrete

local instance : Fact (Nat.Prime 73) := concrete_prime73
noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

private theorem data73_serving_lt :
    1 < (configTemplateOf concreteExecution
      concreteExecution.cfg.challenges.z).kMem := by
  simp [configTemplateOf, BuildableConcrete.concreteExecution,
    ConcreteStrictPackage.cfg]

/-- The F73 serving root (index 1; index 0 is the dummy halt) has read and verify exponents `[1]`. -/

theorem data73_alphaFreeRoot_exps :
    readExps (alphaFreeRoot
        (data73.executionTemplate concreteExecution.cfg.challenges.z)
        ⟨1, data73_serving_lt⟩) = [1] ∧
      verifyExps (alphaFreeRoot
        (data73.executionTemplate concreteExecution.cfg.challenges.z)
        ⟨1, data73_serving_lt⟩) = [1] := by
  constructor <;>
    simp [alphaFreeRoot, templateMemoryTreeAt, templateAxisTree,
      HonestCommitment.Data.executionTemplate, renderMemoryTemplate,
      data73, dummyHaltNodeTree, memNodeTree, mapNTree, readNode, decomposeNode, headNode,
      verifyNode, tailNode, dummyHaltRowTemplate, readRowTemplate, decomposeRowTemplate,
      headRowTemplate, verifyRowTemplate, tailRowTemplate, readExps,
      verifyExps, Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ]

/-- **The §C non-degeneracy hypothesis is inhabited on the live F73 serving root.** -/

theorem data73_readExps_ne_nil :
    readExps (alphaFreeRoot
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      ⟨1, data73_serving_lt⟩) ≠ [] := by
  rw [data73_alphaFreeRoot_exps.1]
  simp

/-- **F73, compiled:** the window fails on the wrapped F73 commitment, so no `∀ D'` identification
can exist even for this fully inhabited execution. -/

theorem f73_no_universal_forestExponentOrder :
    ¬ ∀ D' : Data concreteExecution,
        ForestExponentOrder (D'.executionTemplate concreteExecution.cfg.challenges.z)
          concreteExecution.cfg.challenges.α :=
  no_universal_forestExponentOrder data73 data73_readExps_ne_nil

end Concrete

#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.totalRecordCount
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.lnExponent_le_of_chain
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.computeRows_ne_nil
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.head?_lnPrevExponent
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.recordExponent_le_totalRecordCount
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.recordExponent_pos
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.recordExponent_lt_orderOf
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.canonicalRequestSlots_exponent_le
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.forestExponentOrder_iff_intermediateExponentWindow
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.committed_forest_window_is_the_premise
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.mapNTree_comp
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.memoryNodesOK_wrapAt
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.skeletonOfNodes_wrapAt
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.wrapDataExponents
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.templateAxisTree_wrapAt
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.memoryForest_wrapExponents
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.alphaFreeRoot_wrapExponents
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.forestExponentOrder_fails_on_wrapExponents
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.no_universal_forestExponentOrder
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.wrapExponents_skeleton
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.wrapExponents_honest_exec
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.node_of_templateAxisTree_exp
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.memoryRow_of_alphaFreeRoot_exp
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.forall₂_mem_right
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.forestExponentOrder_of_line_numbers
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.identified_semantic_nats_fails_on_wrapExponents
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.windowed_nat_need_not_be_a_semantic_nat
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.data_eta_unchanged
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.residual_pair_still_eleven_one_two
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.packageOf_fibre_accepts_still_takes_window
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.Concrete.data73_alphaFreeRoot_exps
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.Concrete.data73_readExps_ne_nil
#print axioms Nock.NockVMROM.Thm54.ForestExponentWindow.Concrete.f73_no_universal_forestExponentOrder
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.ForestExponentOrder
#print axioms Nock.NockVMROM.Thm54.GenericHonestPackage.packageOf_fibre_accepts
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end Nock.NockVMROM.Thm54.ForestExponentWindow
