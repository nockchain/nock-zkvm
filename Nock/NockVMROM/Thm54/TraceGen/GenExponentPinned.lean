/-
  Nock/NockVMROM/Thm54/TraceGen/GenExponentPinned.lean

  **Pinning the committed memory-side timestamp exponent at the ℕ level, for an arbitrary
  `ProductionStrategy`.**

  `SemanticTimestampSkeleton` (`SemanticTimestampStrategy.lean:67`) is the α-free commitment.  Its *memory*-side exponent, `MemoryTimestampRow.recordExponent`
  (`:43`), carries no chain and no base: the only field that mentions it is `responseTopology`
  (`:103`), which merely *reads* it into `semanticResponses`.

  ## §A — the ℕ-level IO match, named

  the paper (re-read at source): at `read_root` "we will remove a memory record from the
  `IO` column … Crucially, we add its timestamp (contained in the IO column as part of the memory
  record semantics) to the `axis_counts` and `axis_indicator` columns.  Note that this timestamp is
  unique and represents the line number of the compute table at which the memory record was
  requested".  the paper: "its inclusion in the IO requests verified in the compute table.
  Alongside the fact that it is requested every time we are in a `read_root` or `verify_child`
  state, these checks leave no room for a malicious prover to provide a dishonest timestamp".
  the paper puts that matching into `NockVMROM` itself as the third conjunct
  `(W^IO_comp, W^IO_mem) ∈ 𝓛_mIO^{NMR}`, and `𝓛_mIO` is defined at the paper:
  `responses = σ(unique_requests)` with every request equal to some `unique_request`, i.e. **every
  response is a request**.  `Def:unique_request` is the nodup side condition and
  `Thm:IO_result` the compilation.

  The lift matters and is stated exactly: `𝓛_mIO` at `:1446` is over `MEM = NMR^{α,β}`, i.e. at
  **field** level, where the timestamp appears only as `α ^ e` (`derivedRequestIO` /
  `derivedResponseIO`, `Language.lean:46,51`, are `List (Fin 9 → K)`), so a shift of `e` by
  `orderOf α` is invisible there.  What states the ℕ-level fact is the paper's own sentence:
  the exponent *is* the compute-table line number at which the record was requested.
  `MemoryLineNumbers` is weaker than that sentence — it says only that the exponent is *some*
  committed request's line number, not which one.

  `MemoryLineNumbers` is the **exponent projection** of that matching, stated on committed data
  only: every *active* committed memory row (`read_root` **or** `verify_child`,
  `NounRealization.lean:144`) carries an exponent that already occurs in the committed request list
  `semanticRequests`.

  It is deliberately **weaker** than the paper: the paper matches whole `mem_record`s, this
  matches only their timestamps.  As a hypothesis, weaker is better.

  It is also deliberately restricted to *active* rows, and that restriction is a repair, not a
  weakening of the paper: `GenExponentLineNumbers` §G proves that the unrestricted form —
  `ForestExponentWindow.forestExponentOrder_of_line_numbers`'s `hmemLine` — is refuted by any
  commitment publishing one `decompose`/`halt` noun-walk row, which every non-trivial served forest
  does.  The active rows are exactly the rows the α-free axis structure reads (§D).

  ## §B — the ℕ-level match is **not** derivable from the existing fields

  `remapMemory` rebuilds the commitment with every committed memory exponent sent through an
  arbitrary `f : ℕ → ℕ`.  Every field survives: the compute rows, the four line-number fields,
  `semanticRequests` and `requestTopology` are *literally* the original's, `memoryTopology` only
  ever mentions states, and `responseTopology` holds by construction.  So no existing field of
  `SemanticTimestampSkeleton` can see the memory exponents at all, and
  `no_universal_memoryLineNumbers` is the compiled negative.  This is the skeleton-level analogue of
  `ForestExponentWindow.wrapDataExponents` (`:388`), and unlike it, it needs no `Data`, no
  execution, and no `orderOf`.

  ## §D–§F — the payoff

  `ForestExponentWindow.memoryRow_of_alphaFreeRoot_exp` returns a committed memory row but drops the
  fact that the row is `read_root`/`verify_child`.  §D re-proves the induction keeping that
  conjunct (in this file, because `ForestExponentWindow.lean` is read-only here), which is what makes
  an *active-only* premise sufficient.  §E identifies `totalRecordCount S.computeRows` with a
  quantity of the base skeleton alone (`skeletonRecordCount`), so no seed-uniformity premise on `L`
  is needed.  §F then discharges `GenWorkloadBounds.CommittedExponentWindow` at
  `B = skeletonRecordCount T.skeleton` for an **arbitrary** `T : ProductionStrategy F K` carrying a
  `LineNumberCommitment`, and hence gives `fixedAxisWorkload_le` and `workload_le_explicit` with
  every summand trace data.

  ## What is *not* claimed

  **That stands**, and nothing here refutes
  it: §F is conditional on `LineNumberCommitment`, which is exactly the "line-number identification
  at every seed" that `HU` §5 names as the missing input.  `CommittedExponentWindow` is not removed
  from `workload_le_explicit`; it is *discharged* from a commitment condition that mentions no bound.

  `maxTemplateRecordExponent ≤ L` is **not** provable from `LineNumberCommitment` and should not be
  the target: that scalar is a `foldr max` over *all* committed memory rows including the
  `decompose`/`halt` padding, whose exponents no paper sentence constrains (specialization forces
  their table record to zero, `MemoryRowTemplate.specialize`).  `CommittedExponentWindow` reads only
  the active rows and is the right object.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenWorkloadBounds

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.ExponentPinned

open Nock Nock.Walk
open Nock.AxisBridge
open Nock.AxisBatching
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.ForestExponentWindow
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

/-! ## §A. The ℕ-level IO match on committed data -/

section Match

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
variable {base : SemanticStrategy.SemanticSkeleton}

/-- **The exponent projection of the paper's `𝓛_mIO`, on committed data only.**

Every *active* committed memory row — `read_root` or `verify_child`
(`NounRealization.lean:144`), the two states that request a timestamp — carries
an exponent that already occurs in the committed request list.

Committed-to-committed by construction: the two sides are `S.memoryRows` and
`S.semanticRequests`.  No bound, no `L`, no `totalRecordCount`, no `orderOf`, no workload. -/
def MemoryLineNumbers (S : SemanticTimestampSkeleton F K base) : Prop :=
  ∀ stamp ∈ S.memoryRows,
    memoryMemRecKind stamp.state = .active →
      ∃ slot ∈ S.semanticRequests, slot.exponent = stamp.recordExponent

/-- `requestTopology` is definitionally `canonicalRequestSlots`. -/
theorem semanticRequests_eq_canonicalRequestSlots
    (S : SemanticTimestampSkeleton F K base) :
    S.semanticRequests = S.canonicalRequestSlots :=
  S.requestTopology

/-- **The bound on the memory side, from the match plus the compute-side line-number chain.**
`ForestExponentWindow` §A derives `≤ L` for the request slots with no premise; the match transports
it to the active memory rows. -/
theorem memory_recordExponent_le_of_lineNumbers
    {S : SemanticTimestampSkeleton F K base} (h : MemoryLineNumbers S)
    {stamp : MemoryTimestampRow} (hst : stamp ∈ S.memoryRows)
    (ha : memoryMemRecKind stamp.state = .active) :
    stamp.recordExponent ≤ totalRecordCount S.computeRows := by
  obtain ⟨slot, hslot, heq⟩ := h stamp hst ha
  rw [← heq]
  refine canonicalRequestSlots_exponent_le S ?_
  rwa [← semanticRequests_eq_canonicalRequestSlots S]

/-- Every committed request exponent is a *positive* line number (the paper, `ln(1) = α`).
The `≤` half is `ForestExponentWindow.canonicalRequestSlots_exponent_le`; this is the `0 <` half,
used by §C to separate the match from a bound. -/
theorem canonicalRequestSlots_exponent_pos
    (S : SemanticTimestampSkeleton F K base)
    {slot : CanonicalRecordSlot} (hslot : slot ∈ S.canonicalRequestSlots) :
    0 < slot.exponent := by
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
    exact recordExponent_pos S hstamp i (by rw [hstate]; exact hlt)
  · rw [dif_neg hlt] at hi
    subst hi
    simp at hsome

/-- The premise is consistent: a commitment with no served memory row satisfies it. -/
theorem memoryLineNumbers_of_memoryRows_nil
    (S : SemanticTimestampSkeleton F K base) (h : S.memoryRows = []) :
    MemoryLineNumbers S := by
  intro stamp hst
  rw [h] at hst
  simp at hst

end Match

/-! ## §B. The match is not derivable: the memory exponents are invisible to every existing field -/

section Remap

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
variable {base : SemanticStrategy.SemanticSkeleton}

/-- Send one committed memory row's Nat exponent through `f`. -/
def remapRow (f : ℕ → ℕ) (row : MemoryTimestampRow) : MemoryTimestampRow :=
  { row with recordExponent := f row.recordExponent }

@[simp] theorem remapRow_state (f : ℕ → ℕ) (row : MemoryTimestampRow) :
    (remapRow f row).state = row.state := rfl

@[simp] theorem remapRow_recordExponent (f : ℕ → ℕ) (row : MemoryTimestampRow) :
    (remapRow f row).recordExponent = f row.recordExponent := rfl

private theorem forall₂_remap
    {l : List SemanticStrategy.MemoryRowSkeleton} {r : List MemoryTimestampRow} (f : ℕ → ℕ)
    (h : List.Forall₂ (fun row stamp => stamp.state = row.state) l r) :
    List.Forall₂ (fun row stamp => stamp.state = row.state) l
      (r.map (remapRow f)) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hd tl ih => exact List.Forall₂.cons hd ih

/-- **The commitment with every memory exponent relabelled.**  Nothing else changes: the compute
rows, the four line-number fields, `semanticRequests` and `requestTopology` are literally the
original's, so no existing field of `SemanticTimestampSkeleton` can observe the relabelling. -/
def remapMemory
    (S : SemanticTimestampSkeleton F K base) (f : ℕ → ℕ) :
    SemanticTimestampSkeleton F K base where
  computeRows := S.computeRows
  memoryRows := S.memoryRows.map (remapRow f)
  semanticRequests := S.semanticRequests
  semanticResponses :=
    (let paired :=
      (SemanticStrategy.memorySkeletonRows base).zip
        (S.memoryRows.map (remapRow f))
     paired.filterMap fun pair =>
      if h : pair.1.state = .read_root then
        some
          ({ record := pair.1.memoryRecord (by simp [memoryMemRecKind, h])
             exponent := pair.2.recordExponent } : CanonicalRecordSlot)
      else none)
  computeTopology := S.computeTopology
  memoryTopology := forall₂_remap f S.memoryTopology
  computeStartsAtZero := S.computeStartsAtZero
  computeLineChain := S.computeLineChain
  computeLineAdvance := S.computeLineAdvance
  computeRecordOffsets := S.computeRecordOffsets
  requestTopology := S.requestTopology
  responseTopology := rfl

@[simp] theorem remapMemory_computeRows
    (S : SemanticTimestampSkeleton F K base) (f : ℕ → ℕ) :
    (remapMemory S f).computeRows = S.computeRows := rfl

@[simp] theorem remapMemory_semanticRequests
    (S : SemanticTimestampSkeleton F K base) (f : ℕ → ℕ) :
    (remapMemory S f).semanticRequests = S.semanticRequests := rfl

@[simp] theorem remapMemory_memoryRows
    (S : SemanticTimestampSkeleton F K base) (f : ℕ → ℕ) :
    (remapMemory S f).memoryRows = S.memoryRows.map (remapRow f) := rfl

/-- **The match fails on a relabelling that pushes every memory exponent past `L`.**
Non-degeneracy is explicit and minimal: the commitment must serve at least one lookup, i.e. publish
one `read_root`/`verify_child` row. -/
theorem memoryLineNumbers_fails_on_remap_high
    (S : SemanticTimestampSkeleton F K base)
    {stamp : MemoryTimestampRow} (hst : stamp ∈ S.memoryRows)
    (ha : memoryMemRecKind stamp.state = .active) :
    ¬ MemoryLineNumbers
        (remapMemory S fun e => e + (totalRecordCount S.computeRows + 1)) := by
  intro h
  have hst' :
      remapRow (fun e => e + (totalRecordCount S.computeRows + 1)) stamp ∈
        (remapMemory S fun e => e + (totalRecordCount S.computeRows + 1)).memoryRows :=
    List.mem_map_of_mem hst
  obtain ⟨slot, hslot, heq⟩ := h _ hst' ha
  have hslot' :
      slot ∈
        (remapMemory S fun e =>
          e + (totalRecordCount S.computeRows + 1)).canonicalRequestSlots := by
    rwa [← semanticRequests_eq_canonicalRequestSlots]
  have hle : slot.exponent ≤ totalRecordCount S.computeRows :=
    canonicalRequestSlots_exponent_le _ hslot'
  simp only [remapRow_recordExponent] at heq
  omega

/-- **No universal ℕ-level match.**  Two commitments over the *same* base skeleton with the *same*
compute rows and the *same* `semanticRequests` differ only in their memory exponents, and the match
cannot hold for both.  So the match is not a lemma about `SemanticTimestampSkeleton`: it is a
canonicity condition on the committed memory Nats, exactly as
`ForestExponentWindow.no_universal_forestExponentOrder` is one step downstream. -/
theorem no_universal_memoryLineNumbers
    (S : SemanticTimestampSkeleton F K base)
    {stamp : MemoryTimestampRow} (hst : stamp ∈ S.memoryRows)
    (ha : memoryMemRecKind stamp.state = .active) :
    ¬ ∀ S' : SemanticTimestampSkeleton F K base, MemoryLineNumbers S' :=
  fun h => memoryLineNumbers_fails_on_remap_high S hst ha (h _)

/-! ### §C. The match is not a bound in disguise

The match is not such a bound,
and the separation is one-directional and compiled: relabelling every memory exponent to `0`
satisfies every bound and refutes the match, because committed request exponents are positive. -/

/-- Relabelling every committed memory exponent to `0` satisfies any Nat bound whatsoever… -/
theorem remapMemory_zero_bounded
    (S : SemanticTimestampSkeleton F K base) (B : ℕ) :
    ∀ stamp ∈ (remapMemory S fun _ => 0).memoryRows, stamp.recordExponent ≤ B := by
  intro stamp hst
  rw [remapMemory_memoryRows, List.mem_map] at hst
  obtain ⟨row, _, rfl⟩ := hst
  simp

/-- …and refutes the match. -/
theorem memoryLineNumbers_fails_on_remapMemory_zero
    (S : SemanticTimestampSkeleton F K base)
    {stamp : MemoryTimestampRow} (hst : stamp ∈ S.memoryRows)
    (ha : memoryMemRecKind stamp.state = .active) :
    ¬ MemoryLineNumbers (remapMemory S fun _ => 0) := by
  intro h
  have hst' : remapRow (fun _ => 0) stamp ∈
      (remapMemory S fun _ => 0).memoryRows :=
    List.mem_map_of_mem hst
  obtain ⟨slot, hslot, heq⟩ := h _ hst' ha
  have hpos : 0 < slot.exponent := by
    refine canonicalRequestSlots_exponent_pos (remapMemory S fun _ => 0) ?_
    rwa [← semanticRequests_eq_canonicalRequestSlots]
  simp only [remapRow_recordExponent] at heq
  omega

/-- **A Nat bound on the committed memory exponents does not imply the
match.**  So `MemoryLineNumbers` is not `CommittedExponentWindow` under another name. -/
theorem bound_does_not_imply_memoryLineNumbers
    (S : SemanticTimestampSkeleton F K base)
    {stamp : MemoryTimestampRow} (hst : stamp ∈ S.memoryRows)
    (ha : memoryMemRecKind stamp.state = .active) :
    ∃ S' : SemanticTimestampSkeleton F K base,
      (∀ st ∈ S'.memoryRows, st.recordExponent ≤ totalRecordCount S'.computeRows) ∧
        ¬ MemoryLineNumbers S' :=
  ⟨remapMemory S fun _ => 0,
    remapMemory_zero_bounded S _,
    memoryLineNumbers_fails_on_remapMemory_zero S hst ha⟩

end Remap

/-! ## §D. Every exponent the α-free axis structure reads sits on an **active** committed row

`ForestExponentWindow.node_of_templateAxisTree_exp` / `memoryRow_of_alphaFreeRoot_exp` produce a
committed row with the right exponent but discard its state.  The state is what makes an
active-only premise enough, so the induction is redone here with that conjunct kept.
`templateAxisTree` (`TemplateAxisCounting.lean:35`) emits an exponent only at `read_root` and
`verify_child`, which is `memoryMemRecKind … =.active` (`NounRealization.lean:144`). -/

section ActiveNodes

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **Active-node strengthening of `ForestExponentWindow.node_of_templateAxisTree_exp`.** -/
theorem activeNode_of_templateAxisTree_exp (u : NTree (MemoryRowTemplate (K := K))) :
    ∀ e : ℕ,
      (e ∈ readExps (templateAxisTree u) ∨ e ∈ verifyExps (templateAxisTree u)) →
        ∃ v, InTree u v ∧
          memoryMemRecKind v.label.timestamp.state = .active ∧
          v.label.timestamp.recordExponent = e := by
  let P := fun u : NTree (MemoryRowTemplate (K := K)) =>
    ∀ e : ℕ,
      (e ∈ readExps (templateAxisTree u) ∨ e ∈ verifyExps (templateAxisTree u)) →
        ∃ v, InTree u v ∧
          memoryMemRecKind v.label.timestamp.state = .active ∧
          v.label.timestamp.recordExponent = e
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
              · obtain ⟨v, hv, hact, hev⟩ := ih l (by simp) e (Or.inl hl)
                exact ⟨v, InTree.sub (by simp) hv, hact, hev⟩
              · obtain ⟨v, hv, hact, hev⟩ := ih r (by simp) e (Or.inl hr)
                exact ⟨v, InTree.sub (by simp) hv, hact, hev⟩
              · obtain ⟨v, hv, hact, hev⟩ := ih l (by simp) e (Or.inr hl)
                exact ⟨v, InTree.sub (by simp) hv, hact, hev⟩
              · obtain ⟨v, hv, hact, hev⟩ := ih r (by simp) e (Or.inr hr)
                exact ⟨v, InTree.sub (by simp) hv, hact, hev⟩
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
            · refine ⟨NTree.node row [c], InTree.here _, ?_, rfl⟩
              simp only [NTree.label_node]
              rw [hs]
              rfl
            · obtain ⟨v, hv, hact, hev⟩ := ih c (by simp) e (Or.inl hc)
              exact ⟨v, InTree.sub (by simp) hv, hact, hev⟩
            · obtain ⟨v, hv, hact, hev⟩ := ih c (by simp) e (Or.inr hc)
              exact ⟨v, InTree.sub (by simp) hv, hact, hev⟩
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
            · obtain ⟨v, hv, hact, hev⟩ := ih c (by simp) e (Or.inl hc)
              exact ⟨v, InTree.sub (by simp) hv, hact, hev⟩
            · refine ⟨NTree.node row [c], InTree.here _, ?_, rfl⟩
              simp only [NTree.label_node]
              rw [hs]
              rfl
            · obtain ⟨v, hv, hact, hev⟩ := ih c (by simp) e (Or.inr hc)
              exact ⟨v, InTree.sub (by simp) hv, hact, hev⟩
          · rw [show templateAxisTree (NTree.node row (c :: x :: xs)) = MTree.halt by
              simp [templateAxisTree, hs]] at he
            simp [readExps, verifyExps] at he
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

/-- **Active-row localisation.**  Every exponent read by the α-free axis structure of a committed
root is the `recordExponent` of an *active* BFS row of the committed template. -/
theorem activeMemoryRow_of_alphaFreeRoot_exp
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (i : Fin T.kMem) (e : ℕ)
    (he : e ∈ readExps (alphaFreeRoot E i) ∨ e ∈ verifyExps (alphaFreeRoot E i)) :
    ∃ row ∈ E.memoryRows,
      memoryMemRecKind row.timestamp.state = .active ∧
        row.timestamp.recordExponent = e := by
  obtain ⟨v, hv, hact, hev⟩ :=
    activeNode_of_templateAxisTree_exp (templateMemoryTreeAt E i) e he
  refine ⟨v.label, ?_, hact, hev⟩
  have hroot : templateMemoryTreeAt E i ∈ E.memoryForest := by
    simp only [templateMemoryTreeAt]
    exact List.get_mem _ _
  have hbfs : v ∈ bfsForest E.memoryForest :=
    (mem_bfsForest E.memoryForest v).2 ⟨_, hroot, hv⟩
  exact List.mem_map_of_mem hbfs

end ActiveNodes

/-! ## §E. `totalRecordCount` of the committed compute rows is a quantity of the base skeleton

`computeTopology` pins every committed compute row's *state*, and `totalRecordCount` reads nothing
else.  So the paper's `L` is fixed by the pre-`z` skeleton and no seed-uniformity premise is
needed. -/

section RecordCount

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The paper's `L`, read off the pre-`z` skeleton. -/
def skeletonRecordCount (base : SemanticStrategy.SemanticSkeleton) : ℕ :=
  ((SemanticStrategy.computeSkeletonRows base).map fun r =>
    Nock.Framework.recordCount r.state).sum

private theorem totalRecordCount_of_forall₂ :
    ∀ {l : List SemanticStrategy.ComputeRowSkeleton} {r : List ComputeTimestampRow},
      List.Forall₂ (fun row stamp => stamp.state = row.state) l r →
        totalRecordCount r =
          (l.map fun x => Nock.Framework.recordCount x.state).sum := by
  intro l r h
  induction h with
  | nil => simp [totalRecordCount]
  | cons hd tl ih =>
      rw [totalRecordCount_cons, hd, ih]
      simp

/-- **`L` is skeleton data.**  Unconditional. -/
theorem totalRecordCount_computeRows {base : SemanticStrategy.SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base) :
    totalRecordCount S.computeRows = skeletonRecordCount base :=
  totalRecordCount_of_forall₂ S.computeTopology

end RecordCount

/-! ## §F. The payoff: `CommittedExponentWindow` at `B = L` for an arbitrary `ProductionStrategy` -/

section Production

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- **The commitment condition, bundled.**  For each nonzero seed, the committed timestamp template
is described by a line-number skeleton over the *one* pre-`z` semantic skeleton, and that skeleton
satisfies the ℕ-level IO match.

No field mentions a bound, `L`, `totalRecordCount`, `maxTemplateRecordExponent`, `orderOf` or a
workload; the two relations are commitment-to-commitment. -/
structure LineNumberCommitment (T : ProductionStrategy F K) where
  stamps : ∀ z : K, z ≠ 0 → SemanticTimestampSkeleton F K T.skeleton
  aligned :
    ∀ (z : K) (hz : z ≠ 0),
      TimestampCarrierAlignment (stamps z hz) (committedTemplate T.verifier z hz)
  lineNumbers : ∀ (z : K) (hz : z ≠ 0), MemoryLineNumbers (stamps z hz)

/-- **`GenWorkloadBounds.CommittedExponentWindow`, discharged at `B = L` for an arbitrary
`ProductionStrategy` carrying a `LineNumberCommitment`.**

This is `HU` §5's missing input supplied at the general layer: the bound is *derived* from the
line-number identification, never assumed. -/
theorem committedExponentWindow_of_lineNumbers
    (T : ProductionStrategy F K) (C : LineNumberCommitment T) :
    CommittedExponentWindow T (skeletonRecordCount T.skeleton) := by
  intro z hz i e he
  obtain ⟨row, hrow, hact, hev⟩ :=
    activeMemoryRow_of_alphaFreeRoot_exp (committedTemplate T.verifier z hz) i e he
  obtain ⟨stamp, hstamp, hst⟩ :=
    ForestExponentWindow.forall₂_mem_right (C.aligned z hz).memory _ hrow
  have hactStamp : memoryMemRecKind stamp.state = .active := by rw [hst]; exact hact
  have hle := memory_recordExponent_le_of_lineNumbers (C.lineNumbers z hz) hstamp hactStamp
  rw [totalRecordCount_computeRows] at hle
  have hexp : stamp.recordExponent = e := by rw [hst]; exact hev
  rw [← hexp]
  exact hle

/-- **The axis majorant, bounded by trace data, for an arbitrary `ProductionStrategy` satisfying the
commitment condition.**  `GenExponentLineNumbers.generated_fixedAxisWorkload_le` is the same shape
carried by `hmem : D.memoryNodes = genMemoryNodes …`; this one is carried by
`LineNumberCommitment`, which names no generator. -/
theorem fixedAxisWorkload_le_skeletonRecordCount
    (T : ProductionStrategy F K) (hb : T.BindsAll) (C : LineNumberCommitment T) :
    fixedAxisWorkload T ≤
      T.skeleton.memoryForest.length * skeletonRecordCount T.skeleton :=
  fixedAxisWorkload_le T hb _ (committedExponentWindow_of_lineNumbers T C)

/-- **`workload_le_explicit` with `CommittedExponentWindow` discharged.**  Every summand is trace
data: skeleton row counts, the committed memory-root count, `Λ`, and the skeleton's own record
count `L`. -/
theorem workload_le_explicit_of_lineNumbers
    (T : ProductionStrategy F K) (hb : T.BindsAll) (Λ : ℕ) (C : LineNumberCommitment T) :
    workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) ≤
      1 + (3 + 19 * (SemanticStrategy.computeSkeletonRows T.skeleton).length) * (2 * Λ - 1) +
        (24 * (SemanticStrategy.computeSkeletonRows T.skeleton).length +
          8 * (SemanticStrategy.memorySkeletonRows T.skeleton).length) +
        T.skeleton.memoryForest.length * skeletonRecordCount T.skeleton +
        formRUniformWorkload T +
        reqPairWorkload T Λ +
        SizeWindowCounting.sizeWindowRootBound Λ :=
  workload_le_explicit T hb Λ _ (committedExponentWindow_of_lineNumbers T C)

end Production

end

end Nock.NockVMROM.Thm54.ExponentPinned

/-! ## Scope and axiom receipts -/

#check @Nock.NockVMROM.Thm54.ExponentPinned.MemoryLineNumbers
#check @Nock.NockVMROM.Thm54.ExponentPinned.no_universal_memoryLineNumbers
#check @Nock.NockVMROM.Thm54.ExponentPinned.bound_does_not_imply_memoryLineNumbers
#check @Nock.NockVMROM.Thm54.ExponentPinned.activeMemoryRow_of_alphaFreeRoot_exp
#check @Nock.NockVMROM.Thm54.ExponentPinned.totalRecordCount_computeRows
#check @Nock.NockVMROM.Thm54.ExponentPinned.committedExponentWindow_of_lineNumbers
#check @Nock.NockVMROM.Thm54.ExponentPinned.workload_le_explicit_of_lineNumbers

-- [propext, Classical.choice, Quot.sound]
#print axioms Nock.NockVMROM.Thm54.ExponentPinned.semanticRequests_eq_canonicalRequestSlots
#print axioms Nock.NockVMROM.Thm54.ExponentPinned.memory_recordExponent_le_of_lineNumbers
#print axioms Nock.NockVMROM.Thm54.ExponentPinned.canonicalRequestSlots_exponent_pos
#print axioms Nock.NockVMROM.Thm54.ExponentPinned.memoryLineNumbers_of_memoryRows_nil
#print axioms Nock.NockVMROM.Thm54.ExponentPinned.remapMemory
#print axioms Nock.NockVMROM.Thm54.ExponentPinned.memoryLineNumbers_fails_on_remap_high
#print axioms Nock.NockVMROM.Thm54.ExponentPinned.no_universal_memoryLineNumbers
#print axioms Nock.NockVMROM.Thm54.ExponentPinned.remapMemory_zero_bounded
#print axioms Nock.NockVMROM.Thm54.ExponentPinned.memoryLineNumbers_fails_on_remapMemory_zero
#print axioms Nock.NockVMROM.Thm54.ExponentPinned.bound_does_not_imply_memoryLineNumbers
#print axioms Nock.NockVMROM.Thm54.ExponentPinned.activeNode_of_templateAxisTree_exp
#print axioms Nock.NockVMROM.Thm54.ExponentPinned.activeMemoryRow_of_alphaFreeRoot_exp
#print axioms Nock.NockVMROM.Thm54.ExponentPinned.totalRecordCount_computeRows
#print axioms Nock.NockVMROM.Thm54.ExponentPinned.committedExponentWindow_of_lineNumbers
#print axioms Nock.NockVMROM.Thm54.ExponentPinned.fixedAxisWorkload_le_skeletonRecordCount
#print axioms Nock.NockVMROM.Thm54.ExponentPinned.workload_le_explicit_of_lineNumbers
